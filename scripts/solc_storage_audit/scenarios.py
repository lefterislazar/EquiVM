"""Scenarios for the dynamic comparison: call sequences, optionally from a prepared storage state.

Each scenario lists the operations it exercises; states are chosen to hit the edges where the
storage algorithms branch: short/long bytes (31/32 bytes), partially filled packed slots, growing
and shrinking assignments, out-of-range indices, empty pops, storage left dirty beyond a value's
length, invalid bytes headers, and arrays straddling the end of storage.
"""

import functools
import json
import subprocess
from dataclasses import dataclass, field
from pathlib import Path

HERE = Path(__file__).resolve().parent
TARGET = "0x00000000000000000000000000000000000c0de1"
FULL = 2**256 - 1
ADDR = "0x00000000000000000000000000000000DeaDBeef"


@functools.lru_cache(maxsize=None)
def cast(*args):
    return subprocess.run(["cast", *args], capture_output=True, text=True, check=True).stdout.strip()


def calldata(sig, *args):
    if "function" in sig:  # cast cannot encode function types; their ABI encoding is bytes24
        encoded = cast("calldata", sig.replace("function", "bytes24"), "--", *args)
        return cast("sig", sig) + encoded[10:]
    return cast("calldata", sig, "--", *args)


def keccak_word(n):
    return int(cast("keccak", "0x" + format(n, "064x")), 16)


def mapping_slot(key_type, key, slot):
    return int(cast("index", key_type, key, str(slot)), 16)


@functools.lru_cache(maxsize=None)
def layout(probe):
    record = json.loads((HERE / "out" / "raw" / "0.8.34" / f"{probe}.json").read_text())
    unit = next(iter(record["units"].values()))
    return {e["label"]: int(e["slot"]) for e in unit["contracts"][probe]["storageLayout"]["storage"]}


def blob(n, seed=1):
    """`n` nonzero bytes as a hex literal."""
    return "0x" + "".join(format((seed + i) % 255 + 1, "02x") for i in range(n))


@dataclass
class Scenario:
    probe: str
    name: str
    steps: list
    storage: dict = field(default_factory=dict)
    note: str = ""

    @property
    def key(self):
        return f"{self.probe}.{self.name}"

    def calldata(self):
        return [calldata(sig, *args) for sig, *args in self.steps]

    def ops(self):
        return sorted({sig.split("(")[0] for sig, *_ in self.steps})


SCENARIOS = []


def scenario(probe, name, steps, storage=None, note=""):
    SCENARIOS.append(Scenario(probe, name, steps, storage or {}, note))


# --- value types -------------------------------------------------------------------------------

VALUES = {
    "u8": ("uint8", "200"), "i8": ("int8", "-5"), "bo": ("bool", "true"), "ad": ("address", ADDR),
    "b7": ("bytes7", "0x01020304050607"), "en": ("uint8", "2"), "ct": ("address", ADDR),
    "u40": ("uint40", "1099511627775"), "i24": ("int24", "-70000"),
    "fx": ("function", "0x" + "ab" * 24), "u256": ("uint256", str(FULL - 1)),
    "i256": ("int256", "-2"), "b32": ("bytes32", "0x" + "cd" * 32),
}
for name, (ty, value) in VALUES.items():
    write = (f"w_{name}({ty})", value)
    read, delete = (f"r_{name}()",), (f"d_{name}()",)
    scenario("ValueTypes", f"{name}.clean", [write, read, delete, read])
    scenario("ValueTypes", f"{name}.dirty", [read, write, read, delete, read],
             storage={s: FULL for s in range(6)},
             note="all slots 0xff..: neighbours must be preserved, reads clean up the stored bits")
scenario("ValueTypes", "en.invalid", [("r_en()",)], storage={0: 0x05 << 240},
         note="enum value 5 stored at offset 30")
scenario("ValueTypes", "bo.nonboolean", [("r_bo()",)], storage={0: 0x02 << 16})
scenario("ValueTypes", "fi", [("w_fi()",), ("d_fi()",), ("w_fi()",)])
scenario("ValueTypes", "rmw", [("w_u8(uint8)", "250"), ("rmw_u8(uint8)", "5"), ("rmw_u8(uint8)", "1"),
                               ("w_i24(int24)", "-8388600"), ("rmw_i24(int24)", "8"), ("rmw_i24(int24)", "1")])

# --- structs -----------------------------------------------------------------------------------

S_T = "(uint8,uint128,uint256,int16)"
N_T = f"({S_T},uint8,bytes,uint16[])"
scenario("Structs", "S", [(f"w_S_mem(uint8,uint128,uint256,int16)", "1", "2", "3", "-4"), ("r_S()",),
                          ("rf_S()",), ("wf_S(uint128)", "99"), ("r_S()",), ("d_S()",), ("r_S()",),
                          (f"w_S_cd({S_T})", "(5,6,7,-8)"), ("r_S()",),
                          (f"set_s2({S_T})", "(9,10,11,-12)"), ("w_S_sto()",), ("r_S()",)])
scenario("Structs", "S.dirty", [("r_S()",), (f"w_S_cd({S_T})", "(5,6,7,-8)"), ("r_S()",), ("d_S()",)],
         storage={s: FULL for s in range(3)})
long_n, short_n = f"((1,2,3,-4),5,{blob(40)},[1,2,3])", f"((6,7,8,-9),10,{blob(3, 9)},[4])"
scenario("Structs", "N", [(f"w_N_mem({N_T})", long_n), ("r_N()",), (f"w_N_mem({N_T})", short_n), ("r_N()",),
                          (f"w_N_cd({N_T})", long_n), (f"wf_N({S_T})", "(1,1,1,1)"), ("r_N()",),
                          (f"set_n2({N_T})", short_n), ("w_N_sto()",), ("r_N()",), ("d_N()",), ("r_N()",)])
scenario("Structs", "M", [("wf_M(uint256,uint256)", "1", "2"), ("d_M()",), ("wf_M(uint256,uint256)", "3", "4")],
         note="delete skips the mapping member")

# --- fixed-size arrays -------------------------------------------------------------------------

FIXED = {
    "p": ("uint8[5]", "[1,2,3,4,5]", "[9,8,7,6,5]"),
    "f": ("uint256[3]", "[1,2,3]", f"[{FULL},0,7]"),
    "ms": ("(uint8,uint128,uint256)[2]", "[(1,2,3),(4,5,6)]", "[(7,8,9),(0,0,1)]"),
    "nn": ("uint8[3][2]", "[[1,2,3],[4,5,6]]", "[[7,8,9],[1,1,1]]"),
    "bb": ("bytes[2]", f"[{blob(40)},{blob(2)}]", f"[{blob(1)},{blob(70)}]"),
}
for name, (ty, a, b) in FIXED.items():
    steps = [(f"w_{name}_mem({ty})", a), (f"r_{name}()",), (f"w_{name}_cd({ty})", b), (f"r_{name}()",),
             (f"set_{name}2({ty})", a), (f"w_{name}_sto()",), (f"r_{name}()",), (f"d_{name}()",), (f"r_{name}()",)]
    scenario("FixedArrays", name, steps)
scenario("FixedArrays", "p.index", [("wi_p(uint256,uint8)", "4", "7"), ("ri_p(uint256)", "4"), ("di_p(uint256)", "4"),
                                    ("ri_p(uint256)", "5"), ("wi_p(uint256,uint8)", "5", "1")])
scenario("FixedArrays", "f.index", [("wi_f(uint256,uint256)", "2", "7"), ("ri_f(uint256)", "2"), ("ri_f(uint256)", "3")])
scenario("FixedArrays", "ms.index", [("wi_ms(uint256,(uint8,uint128,uint256))", "1", "(1,2,3)"), ("r_ms()",)])
scenario("FixedArrays", "nn.index", [("wi_nn(uint256,uint256,uint8)", "1", "2", "9"), ("r_nn()",),
                                     ("wi_nn(uint256,uint256,uint8)", "2", "0", "9")])


def _fixed_dirty():
    lay = layout("FixedArrays")
    return {lay["p"]: FULL, lay["nn"]: FULL, lay["nn"] + 1: FULL}


SCENARIOS_LAZY = [lambda: scenario("FixedArrays", "p.dirty", [("r_p()",), ("w_p_mem(uint8[5])", "[1,2,3,4,5]"), ("r_p()",),
                                                               ("d_p()",), ("w_nn_mem(uint8[3][2])", "[[1,2,3],[4,5,6]]")],
                                   storage=_fixed_dirty(), note="bits beyond the elements in each slot are dirty"),
                  lambda: scenario("FixedArrays", "p.dirty.write", [("w_p_cd(uint8[5])", "[1,2,3,4,5]"), ("r_p()",)],
                                   storage=_fixed_dirty(), note="uint8[5] written over a slot whose bytes 5..31 are dirty")]

# --- dynamic arrays ----------------------------------------------------------------------------

DYN = {
    "p": ("uint8[]", ["[1,2,3]", "[" + ",".join(str(i % 250 + 1) for i in range(40)) + "]", "[9,8]", "[]"]),
    "f": ("uint256[]", ["[1,2,3]", "[4,5,6,7,8]", "[9]", "[]"]),
    "ms": ("(uint8,uint128,uint256)[]", ["[(1,2,3),(4,5,6)]", "[(7,8,9),(1,1,1),(2,2,2)]", "[(3,3,3)]", "[]"]),
    "nn": ("uint16[][]", ["[[1,2],[3]]", "[[4],[5,6,7],[]]", "[[8]]", "[]"]),
    "bb": ("bytes[]", [f"[{blob(40)},{blob(2)}]", f"[{blob(1)},{blob(70)},{blob(31)}]", f"[{blob(33)}]", "[]"]),
    "fa": ("uint8[3][]", ["[[1,2,3],[4,5,6]]", "[[7,8,9],[1,1,1],[2,2,2]]", "[[3,3,3]]", "[]"]),
}
for name, (ty, values) in DYN.items():
    steps = []
    for v in values:
        steps += [(f"w_{name}_mem({ty})", v), (f"r_{name}()",) if name != "fa" else (f"d_{name}()",)]
    scenario("DynArrays", f"{name}.mem", steps)
    scenario("DynArrays", f"{name}.cd", [(f"w_{name}_cd({ty})", v) for v in values[:3]] +
             [(f"w_{name}_cd({ty})", values[0])])
    sto = []
    for v in values:
        sto += [(f"set_{name}2({ty})", v), (f"w_{name}_sto()",)]
    scenario("DynArrays", f"{name}.sto", [(f"w_{name}_mem({ty})", values[1])] + sto)
    scenario("DynArrays", f"{name}.delete", [(f"w_{name}_mem({ty})", values[1]), (f"d_{name}()",)])
    pushes = {"p": ("pushv_p(uint8)", "7"), "f": ("pushv_f(uint256)", "7"),
              "ms": ("pushv_ms(uint8,uint128,uint256)", "1", "2", "3"), "nn": ("pushv_nn(uint16[])", "[1,2,3]"),
              "bb": ("pushv_bb(bytes)", blob(40)), "fa": ("pushv_fa(uint8[3])", "[1,2,3]")}
    pp = [(f"pop_{name}()",), (f"pop_{name}()",)] + [pushes[name]] * 3
    if name not in ("bb", "fa"):
        pp += [(f"push0_{name}()",), (f"push0_{name}()",)]
    pp += [(f"pop_{name}()",)] * 6
    scenario("DynArrays", f"{name}.pushpop", [(f"w_{name}_mem({ty})", values[0])] + pp)
scenario("DynArrays", "p.pushpop.boundary",
         [("w_p_mem(uint8[])", "[" + ",".join(["1"] * 31) + "]"), ("push0_p()",), ("pushv_p(uint8)", "2"),
          ("pushv_p(uint8)", "3"), ("pop_p()",), ("pop_p()",), ("pop_p()",), ("len_p()",)])
scenario("DynArrays", "p.index", [("w_p_mem(uint8[])", "[1,2,3]"), ("wi_p(uint256,uint8)", "2", "9"), ("ri_p(uint256)", "2"),
                                  ("di_p(uint256)", "1"), ("ri_p(uint256)", "3"), ("wi_p(uint256,uint8)", "3", "1"), ("r_p()",)])
scenario("DynArrays", "f.index", [("w_f_mem(uint256[])", "[1,2,3]"), ("wi_f(uint256,uint256)", "2", "9"), ("ri_f(uint256)", "3")])
scenario("DynArrays", "ms.index", [("w_ms_mem((uint8,uint128,uint256)[])", "[(1,2,3)]"),
                                   ("wi_ms(uint256,(uint8,uint128,uint256))", "0", "(9,9,9)"),
                                   ("wi_ms(uint256,(uint8,uint128,uint256))", "1", "(9,9,9)"), ("r_ms()",)])
scenario("DynArrays", "nn.index", [("w_nn_mem(uint16[][])", "[[1,2],[3]]"), ("wi_nn(uint256,uint256,uint16)", "1", "0", "9"),
                                   ("wi_nn(uint256,uint256,uint16)", "1", "1", "9"), ("r_nn()",)])


def _dyn_dirty():
    lay = layout("DynArrays")
    p, f, ms = lay["p"], lay["f"], lay["ms"]
    dp, df, dms = keccak_word(p), keccak_word(f), keccak_word(ms)
    return {p: 3, dp: FULL, dp + 1: FULL,
            f: 2, df: 1, df + 1: 2, df + 2: FULL, df + 3: FULL,
            ms: 1, dms: FULL, dms + 1: FULL, dms + 2: FULL, dms + 3: FULL}


SCENARIOS_LAZY += [
    lambda: scenario("DynArrays", "p.dirty",
                     [("r_p()",), ("push0_p()",), ("r_p()",), ("pushv_p(uint8)", "7"), ("pop_p()",), ("pop_p()",),
                      ("r_p()",), ("w_p_mem(uint8[])", "[1,2,3,4,5]"), ("r_p()",), ("w_p_mem(uint8[])", "[1]"), ("r_p()",)],
                     storage=_dyn_dirty(), note="length 3, data slots 0xff..: dirty bytes beyond the length"),
    lambda: scenario("DynArrays", "p.dirty.grow", [("w_p_mem(uint8[])", "[1,2,3,4,5]"), ("r_p()",)], storage=_dyn_dirty(),
                     note="length 3 grown to 5 over dirty bytes; no later shrink cleans the slot"),
    lambda: scenario("DynArrays", "f.dirty", [("push0_f()",), ("r_f()",), ("w_f_mem(uint256[])", "[1,2,3]"), ("pop_f()",),
                                              ("d_f()",), ("r_f()",)], storage=_dyn_dirty(),
                     note="length 2, two dirty slots past the end"),
    lambda: scenario("DynArrays", "ms.dirty", [("r_ms()",), ("push0_ms()",), ("r_ms()",), ("pop_ms()",), ("pop_ms()",)],
                     storage=_dyn_dirty(), note="length 1, struct slots and the following element dirty"),
]

# --- bytes and strings -------------------------------------------------------------------------

LENGTHS = [0, 1, 31, 32, 33, 64, 65, 3, 100, 0]
scenario("Bytes", "b.mem.transitions",
         [step for n in LENGTHS for step in [("w_b_mem(bytes)", blob(n, n)), ("r_b()",), ("len_b()",)]])
scenario("Bytes", "b.cd.transitions",
         [step for n in LENGTHS for step in [("w_b_cd(bytes)", blob(n, n)), ("r_b()",)]])
scenario("Bytes", "b.sto.transitions",
         [step for n in LENGTHS for step in [("set_b2(bytes)", blob(n, n)), ("w_b_sto()",), ("r_b()",)]])
scenario("Bytes", "s.transitions",
         [step for n in LENGTHS for step in [("w_s_mem(string)", "x" * n), ("r_s()",), ("w_s_cd(string)", "y" * (n + 1)),
                                            ("set_s2(string)", "z" * (n // 2)), ("w_s_sto()",), ("len_s()",)]] +
         [("d_s()",), ("r_s()",)])
scenario("Bytes", "b.literals", [("w_b_litlong()",), ("r_b()",), ("w_b_lit()",), ("r_b()",), ("w_b_litlong()",),
                                 ("set_s2(string)", "hello"), ("w_s_sto()",), ("w_b_froms()",), ("r_b()",)])
scenario("Bytes", "b.delete", [("w_b_mem(bytes)", blob(70)), ("d_b()",), ("r_b()",), ("w_b_mem(bytes)", blob(5)), ("d_b()",)])
scenario("Bytes", "b.pushpop.boundary",
         [("w_b_mem(bytes)", blob(30)), ("push0_b()",), ("pushv_b(bytes1)", "0x41"), ("pushv_b(bytes1)", "0x42"),
          ("r_b()",), ("pop_b()",), ("pop_b()",), ("r_b()",), ("pop_b()",), ("len_b()",)] +
         [("pop_b()",)] * 31 + [("len_b()",)])
scenario("Bytes", "s.pushpop", [("w_s_mem(string)", "a" * 31), ("pushv_s(bytes1)", "0x41"), ("r_s()",),
                                ("pop_s()",), ("pop_s()",), ("r_s()",)])
scenario("Bytes", "b.index",
         [("w_b_mem(bytes)", blob(40)), ("wi_b(uint256,bytes1)", "33", "0x00"), ("ri_b(uint256)", "33"),
          ("di_b(uint256)", "0"), ("ri_b(uint256)", "40"), ("wi_b(uint256,bytes1)", "40", "0x01"),
          ("w_b_mem(bytes)", blob(5)), ("wi_b(uint256,bytes1)", "4", "0x00"), ("ri_b(uint256)", "4"),
          ("di_b(uint256)", "1"), ("r_b()",)])


def _bytes_slot():
    return layout("Bytes")["b"]


def _bytes_dirty_long():
    b = _bytes_slot()
    d = keccak_word(b)
    return {b: 33 * 2 + 1, d: FULL, d + 1: FULL, d + 2: FULL}


def _bytes_dirty_short():
    return {_bytes_slot(): (FULL >> 8 << 8) | (5 * 2)}


SCENARIOS_LAZY += [
    lambda: scenario("Bytes", "b.invalid.long-flag-short-length", [("len_b()",), ("r_b()",), ("ri_b(uint256)", "0"),
                                                                   ("push0_b()",), ("pop_b()",), ("w_b_mem(bytes)", blob(3)),
                                                                   ("r_b()",)],
                     storage={_bytes_slot(): 3}, note="header 0x03: long flag with length 1"),
    lambda: scenario("Bytes", "b.invalid.short-flag-long-length", [("len_b()",), ("r_b()",), ("d_b()",), ("r_b()",)],
                     storage={_bytes_slot(): 0x40}, note="header 0x40: short flag with length 32"),
    lambda: scenario("Bytes", "b.dirty.long",
                     [("r_b()",), ("push0_b()",), ("r_b()",), ("pop_b()",), ("pop_b()",), ("r_b()",),
                      ("w_b_mem(bytes)", blob(40)), ("r_b()",), ("w_b_mem(bytes)", blob(2)), ("r_b()",)],
                     storage=_bytes_dirty_long(), note="length 33, data slots 0xff..: dirty beyond the length"),
    lambda: scenario("Bytes", "b.dirty.short",
                     [("r_b()",), ("push0_b()",), ("r_b()",), ("pushv_b(bytes1)", "0x41"), ("pop_b()",), ("r_b()",),
                      ("w_b_mem(bytes)", blob(40)), ("r_b()",)],
                     storage=_bytes_dirty_short(), note="short length 5 with dirty bytes after it"),
]

# --- mappings ----------------------------------------------------------------------------------

scenario("Mappings", "values", [("w_mu(uint256,uint256)", "1", "2"), ("r_mu(uint256)", "1"), ("d_mu(uint256)", "1"),
                                ("w_ma(address,uint8)", ADDR, "7"), ("r_ma(address)", ADDR),
                                ("w_mi8(int8,uint256)", "-1", "5"), ("r_mi8(int8)", "-1"),
                                ("w_mb4(bytes4,uint256)", "0x01020304", "6"), ("w_mbo(bool,uint256)", "true", "8"),
                                ("w_mm(uint256,uint256,uint256)", "1", "2", "3")])
scenario("Mappings", "dynamic-keys", [("w_mb_cd(bytes,uint256)", blob(40), "1"), ("w_mb_mem(bytes,uint256)", blob(3), "2"),
                                      ("r_mb(bytes)", blob(40)), ("r_mb(bytes)", "0x"), ("w_mst(string,uint256)", "key", "3"),
                                      ("w_mb_cd(bytes,uint256)", "0x", "4")])
scenario("Mappings", "aggregates", [("w_mS(uint256,(uint8,uint128,uint256))", "1", "(1,2,3)"), ("d_mS(uint256)", "1"),
                                    ("w_mby(uint256,bytes)", "1", blob(70)), ("w_mby(uint256,bytes)", "2", blob(4)),
                                    ("d_mby(uint256)", "1"), ("pushv_mda(uint256,uint256)", "1", "5"),
                                    ("pushv_mda(uint256,uint256)", "1", "6"), ("d_mda(uint256)", "1")])

# --- arrays at the end of storage --------------------------------------------------------------

END = 2**256
scenario("SlotPointers", "box.wrap", [("d_box_at(uint256)", str(END - 2))],
         storage={(END - 2 + i) % END: FULL for i in range(5)},
         note="uint256[4] at 2**256-2: occupies slots 2**256-2, 2**256-1, 0, 1")
scenario("SlotPointers", "box.wrap.write", [("w_box_at(uint256,uint256[4])", str(END - 2), "[1,2,3,4]")],
         storage={(END - 2 + i) % END: FULL for i in range(5)})
scenario("SlotPointers", "box.nowrap", [("d_box_at(uint256)", "100")], storage={100 + i: FULL for i in range(5)})
scenario("SlotPointers", "pbox.wrap", [("d_pbox_at(uint256)", str(END - 1))],
         storage={(END - 1 + i) % END: FULL for i in range(3)},
         note="uint8[40] at 2**256-1: occupies slots 2**256-1 and 0")

# --- transient storage and custom layouts ------------------------------------------------------

scenario("Transient", "all", [("w_t(uint256)", "5"), ("r_t()",), ("d_t()",), ("r_t()",), ("w_t8(uint8)", "200"),
                              ("r_t8()",), ("w_ti8(int8)", "-3"), ("r_ti8()",), ("r_t8()",), ("w_tb(bool)", "true"),
                              ("w_ta(address)", ADDR), ("d_ta()",), ("r_ti8()",), ("d_t8()",), ("r_t8()",), ("r_ti8()",)],
         storage={0: FULL}, note="persistent slot 0 is dirty and must stay untouched")
scenario("TransientCollision", "delete-persistent",
         [("w_both(uint256)", "7"), ("r_both()",), ("d_p()",), ("r_both()",)])
scenario("TransientCollision", "delete-transient",
         [("w_both(uint256)", "7"), ("r_both()",), ("d_t()",), ("r_both()",)])
SCENARIOS_LAZY.append(lambda: scenario(
    "LayoutAt", "all", [("w_a(uint8)", "1"), ("w_b(uint16)", "2"), ("w_c(bytes)", blob(40)), ("pushv_d(uint256)", "5"),
                        ("w_m(uint256,uint256)", "1", "2"), ("d_f()",)],
    storage={layout("LayoutAt")["f"] + i: FULL for i in range(3)}, note="layout at 0x1234; f prefilled"))


def _materialize():
    for make in SCENARIOS_LAZY:
        make()


_materialize()


# --- struct elements and length bounds (legacy vs via-IR) -------------------------------------

def _dirty_ms_dyn(length):
    lay = layout("DynArrays")
    d = keccak_word(lay["ms"])
    return {lay["ms"]: length, **{d + i: FULL for i in range(6)}}


def _dirty_ms_fixed():
    s = layout("FixedArrays")["ms"]
    return {s + i: FULL for i in range(4)}


def _dirty_n():
    s = layout("Structs")["n"]
    return {s + i: FULL for i in range(4)}  # n.s (3 slots), n.x; y and z are left empty


def _length(probe, var, n):
    return {layout(probe)[var]: n}


_more = [
    lambda: scenario("DynArrays", "ms.pop.dirty", [("pop_ms()",)], storage=_dirty_ms_dyn(2),
                     note="S[] of length 2 over 0xff.. slots: popping clears the last struct"),
    lambda: scenario("DynArrays", "ms.shrink.dirty", [("w_ms_mem((uint8,uint128,uint256)[])", "[(1,2,3)]")],
                     storage=_dirty_ms_dyn(2), note="assigning one element clears the second"),
    lambda: scenario("DynArrays", "ms.delete.dirty", [("d_ms()",)], storage=_dirty_ms_dyn(2)),
    lambda: scenario("FixedArrays", "ms.delete.dirty", [("d_ms()",)], storage=_dirty_ms_fixed()),
    lambda: scenario("Structs", "N.delete.dirty", [("d_N()",)], storage=_dirty_n(),
                     note="a struct with a nested struct, over 0xff.. slots"),
    lambda: scenario("DynArrays", "p.push.2^64", [("pushv_p(uint8)", "7")], storage=_length("DynArrays", "p", 2 ** 64)),
    lambda: scenario("DynArrays", "p.push0.2^64", [("push0_p()",)], storage=_length("DynArrays", "p", 2 ** 64)),
    lambda: scenario("DynArrays", "f.push.2^64-1", [("pushv_f(uint256)", "7")],
                     storage=_length("DynArrays", "f", 2 ** 64 - 1)),
    lambda: scenario("DynArrays", "ms.push0.2^64", [("push0_ms()",)], storage=_length("DynArrays", "ms", 2 ** 64)),
    lambda: scenario("Bytes", "b.push.2^64", [("pushv_b(bytes1)", "0x41")],
                     storage=_length("Bytes", "b", 2 * 2 ** 64 + 1), note="long header of length 2^64"),
    lambda: scenario("Bytes", "b.push0.2^64", [("push0_b()",)], storage=_length("Bytes", "b", 2 * 2 ** 64 + 1)),
]
for make in _more:
    make()


# --- single-step bytes push/pop on dirty storage (nothing overwrites the result) ---------------

def _bytes_long_dirty(n):
    b = layout("Bytes")["b"]
    d = keccak_word(b)
    return {b: 2 * n + 1, **{d + i: FULL for i in range(n // 32 + 2)}}


def _bytes_short_dirty(n):
    return {layout("Bytes")["b"]: (FULL >> 8 << 8) | (2 * n)}


for _tag, _storage in [("short5", lambda: _bytes_short_dirty(5)), ("short30", lambda: _bytes_short_dirty(30)),
                       ("short31", lambda: _bytes_short_dirty(31)), ("long32", lambda: _bytes_long_dirty(32)),
                       ("long33", lambda: _bytes_long_dirty(33)), ("long64", lambda: _bytes_long_dirty(64))]:
    for _op, _steps in [("push0", [("push0_b()",)]), ("pushv", [("pushv_b(bytes1)", "0x41")]), ("pop", [("pop_b()",)])]:
        scenario("Bytes", f"b.{_op}.dirty.{_tag}", _steps, storage=_storage(),
                 note="one step on dirty storage: the final storage shows every byte written")
