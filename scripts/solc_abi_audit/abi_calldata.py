"""ABI encoding with word roles, and the malformed calldata derived from it.

`encode(types, values)` returns the words of the standard ABI encoding, each labelled with its role
(`value`, `offset`, `length`, `data`) and the path of the value it belongs to.  `mutations` derives
calldata variants that target one word each: dirty value words, offsets and lengths that point
outside the calldata or overflow, truncations and trailing data.  An argument can itself be an ABI
encoding (`Enc`), for `abi.decode` probes: its inner words are then labelled and mutated too.
"""

import functools
import re
import subprocess
from dataclasses import dataclass

W = 2 ** 256


@dataclass
class Word:
    value: int
    role: str          # value | offset | length | data
    path: str
    ty: str = ""


@dataclass
class Enc:
    """A `bytes` argument whose content is the ABI encoding of `types` with `values`."""
    types: list
    values: list


def split_tuple(s):
    """Top-level components of `a,b,(c,d)[]`."""
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch == "," and depth == 0:
            out.append(cur)
            cur = ""
            continue
        depth += {"(": 1, ")": -1}.get(ch, 0)
        cur += ch
    if cur:
        out.append(cur)
    return out


def parse(ty):
    """('array', elem, n|None) | ('tuple', [types]) | ('bytes',) | ('string',) | ('value', name)."""
    m = re.fullmatch(r"(.*)\[(\d*)\]", ty)
    if m:
        return ("array", m.group(1), int(m.group(2)) if m.group(2) else None)
    if ty.startswith("("):
        return ("tuple", split_tuple(ty[1:-1]))
    if ty in ("bytes", "string"):
        return (ty,)
    return ("value", ty)


def is_dynamic(ty):
    p = parse(ty)
    if p[0] in ("bytes", "string"):
        return True
    if p[0] == "array":
        return p[2] is None or is_dynamic(p[1])
    if p[0] == "tuple":
        return any(is_dynamic(t) for t in p[1])
    return False


def value_word(ty, v):
    if ty == "bool":
        return int(bool(v))
    if ty == "address":
        return v
    if ty == "function":  # bytes24, left-aligned
        return v << 64
    m = re.fullmatch(r"bytes(\d+)", ty)
    if m:
        return int.from_bytes(v.ljust(32, b"\0")[:32], "big")
    if ty.startswith("int"):
        return v % W
    return v


def encode_one(ty, v, path):
    """(head words, tail words) of one component; the head of a dynamic one is a placeholder."""
    p = parse(ty)
    if p[0] in ("bytes", "string"):
        data = v.encode() if isinstance(v, str) else v
        words = [Word(len(data), "length", path, ty)]
        for i in range(0, len(data), 32):
            words.append(Word(int.from_bytes(data[i:i + 32].ljust(32, b"\0"), "big"), "data", f"{path}[{i // 32}]", ty))
        return words
    if p[0] == "array":
        elems = encode_tuple([p[1]] * len(v), v, path, index=True)
        return ([Word(len(v), "length", path, ty)] if p[2] is None else []) + elems
    if p[0] == "tuple":
        return encode_tuple(p[1], v, path)
    return [Word(value_word(ty, v), "value", path, ty)]


def encode_tuple(types, values, path="", index=False):
    """Words of a tuple (or of array elements, `index`): heads, then tails, offsets relative to the
    start of the tuple."""
    heads, tails = [], []
    names = [f"{path}[{i}]" if index else f"{path}.{i}" for i in range(len(types))]
    head_size = sum(1 if is_dynamic(t) else len(encode_one(t, v, n)) for t, v, n in zip(types, values, names))
    for t, v, n in zip(types, values, names):
        if isinstance(v, Enc):
            inner = encode_tuple(v.types, v.values, n + ":")
            data = b"".join(w.value.to_bytes(32, "big") for w in inner)
            words = [Word(len(data), "length", n, "bytes")] + inner
            heads.append(Word(32 * (head_size + len(tails)), "offset", n, t))
            tails.extend(words)
        elif is_dynamic(t):
            heads.append(Word(32 * (head_size + len(tails)), "offset", n, t))
            tails.extend(encode_one(t, v, n))
        else:
            heads.extend(encode_one(t, v, n))
    return heads + tails


def to_bytes(words):
    return b"".join((w.value % W).to_bytes(32, "big") for w in words)


@functools.lru_cache(maxsize=None)
def selector(sig):
    return bytes.fromhex(subprocess.run(["cast", "sig", sig], capture_output=True, text=True,
                                        check=True).stdout.strip()[2:])


def dirty(word):
    """A non-canonical word for the type of a value word, or None when every word is valid."""
    ty, v = word.ty, word.value
    if ty == "bool":
        return 2
    if ty == "address":
        return v | (1 << 160)
    if ty == "function":
        return v | 1
    m = re.fullmatch(r"bytes(\d+)", ty)
    if m and int(m.group(1)) < 32:
        return v | 1
    m = re.fullmatch(r"(u?)int(\d+)", ty)
    if m and int(m.group(2)) < 256:
        bits = int(m.group(2))
        if m.group(1):
            return v | (1 << bits)
        return (v % (1 << bits)) | (1 << bits) if v % W >= W // 2 else v | (1 << (bits - 1))
    if ty == "enum":
        return 3
    return None


def mutations(sig, types, values):
    """[(label, calldata bytes)] for one call."""
    words = encode_tuple(types, values)
    sel = selector(sig)
    valid = sel + to_bytes(words)
    cases = [("valid", valid), ("selector-only", sel), ("trunc-1", valid[:-1]), ("trunc-32", valid[:-32]),
             ("extra-word", valid + bytes(32))]

    def with_word(i, value):
        ws = list(words)
        ws[i] = Word(value % W, ws[i].role, ws[i].path, ws[i].ty)
        return sel + to_bytes(ws)

    size = len(words) * 32
    for i, w in enumerate(words):
        if w.role == "value":
            d = dirty(w)
            if d is not None:
                cases.append((f"dirty {w.path}", with_word(i, d)))
        elif w.role == "offset":
            for tag, val in [("2^64", 2 ** 64), ("2^256-32", W - 32), ("past-end", size), ("unaligned", w.value + 1),
                             ("zero", 0)]:
                cases.append((f"offset {tag} {w.path}", with_word(i, val)))
        elif w.role == "length":
            for tag, val in [("2^64", 2 ** 64), ("2^256-1", W - 1), ("+1", w.value + 1), ("2^32", 2 ** 32)]:
                cases.append((f"length {tag} {w.path}", with_word(i, val)))
    return cases
