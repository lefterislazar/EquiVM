"""The calls of the ABI probes: signature, argument types and representative values.  Every call
is expanded by `abi_calldata.mutations` into its malformed variants."""

from abi_calldata import Enc

S = "(uint8,bytes,uint16[])"
T = "(uint256,uint8[2])"
SV = (9, b"xyz", [1, 2])
SV2 = (1, b"a" * 40, [3])
TV = (5, [6, 7])
LONG = bytes(range(1, 41))
B32 = bytes(range(32))
FN = (0xC0FFEE << 32) | 0x12345678  # address ++ selector, as a bytes24

# (probe, function, [argument types], [values]); the signature uses the ABI type names
CALLS = [
    ("AbiValue", "u8", ["uint8"], [7]),
    ("AbiValue", "i8", ["int8"], [-3]),
    ("AbiValue", "i40", ["int40"], [-5]),
    ("AbiValue", "u256", ["uint256"], [2 ** 255 + 1]),
    ("AbiValue", "bo", ["bool"], [True]),
    ("AbiValue", "ad", ["address"], [0xDEADBEEF]),
    ("AbiValue", "b3", ["bytes3"], [b"\x01\x02\x03"]),
    ("AbiValue", "b32", ["bytes32"], [B32]),
    ("AbiValue", "en", ["enum"], [2]),
    ("AbiValue", "fx", ["function"], [FN]),
    ("AbiValue", "two", ["uint8", "bool"], [7, True]),
    ("AbiValue", "unused", ["uint8", "bool"], [7, True]),
    ("AbiValue", "dirtyU8", ["uint256"], [0x1FF]),
    ("AbiValue", "dirtyBo", ["uint256"], [2]),
    ("AbiValue", "dirtyI8", ["uint256"], [0x80]),
    ("AbiValue", "dirtyI8", ["uint256"], [0x17F]),
    ("AbiValue", "dirtyAd", ["uint256"], [(1 << 160) | 5]),
]

for probe in ("AbiMem", "AbiCd"):
    CALLS += [
        (probe, "au8", ["uint8[]"], [[1, 2, 3]]),
        (probe, "au8len", ["uint8[]"], [[1, 2, 3]]),
        (probe, "au8at", ["uint8[]", "uint256"], [[1, 2, 3], 1]),
        (probe, "au8at", ["uint8[]", "uint256"], [[1, 2, 3], 3]),
        (probe, "fu8", ["uint8[3]"], [[4, 5, 6]]),
        (probe, "bys", ["bytes"], [b"hello"]),
        (probe, "bys", ["bytes"], [LONG]),
        (probe, "st", ["string"], ["hi"]),
        (probe, "nn", ["uint8[][]"], [[[1, 2], [3]]]),
        (probe, "nnat", ["uint8[][]", "uint256", "uint256"], [[[1, 2], [3]], 1, 0]),
        (probe, "fn", ["uint256[2][]"], [[[1, 2], [3, 4]]]),
        (probe, "nf", ["uint8[][2]"], [[[1], [2, 3]]]),
        (probe, "bb", ["bytes[]"], [[b"ab", LONG]]),
        (probe, "s", [S], [SV]),
        (probe, "sa", [S], [SV]),
        (probe, "sar", [f"{S}[]"], [[SV, SV2]]),
        (probe, "t", [T], [TV]),
        (probe, "tar", [f"{T}[]"], [[TV, (1, [2, 3])]]),
        (probe, "mix", ["uint8", "bytes", "bool"], [7, b"xy", True]),
    ]

CALLS += [
    ("AbiCd", "au8slice", ["uint8[]", "uint256", "uint256"], [[1, 2, 3, 4], 1, 3]),
    ("AbiCd", "fu8at", ["uint8[3]", "uint256"], [[4, 5, 6], 2]),
    ("AbiCd", "bylen", ["bytes"], [LONG]),
    ("AbiCd", "byslice", ["bytes", "uint256", "uint256"], [b"hello", 1, 4]),
    ("AbiCd", "nnlen", ["uint8[][]", "uint256"], [[[1, 2], [3]], 0]),
    ("AbiCd", "nncopy", ["uint8[][]"], [[[1, 2], [3]]]),
    ("AbiCd", "nnenc", ["uint8[][]"], [[[1, 2], [3]]]),
    ("AbiCd", "bbat", ["bytes[]", "uint256"], [[b"ab", LONG], 1]),
    ("AbiCd", "sb", [S], [SV]),
    ("AbiCd", "tail", ["bytes", "uint256[2]"], [b"abc", [1, 2]]),

    ("AbiDecode", "dU8", ["bytes"], [Enc(["uint8"], [7])]),
    ("AbiDecode", "dU8", ["bytes"], [b"\x01"]),
    ("AbiDecode", "dBo", ["bytes"], [Enc(["bool"], [True])]),
    ("AbiDecode", "dArr", ["bytes"], [Enc(["uint8[]"], [[1, 2, 3]])]),
    ("AbiDecode", "dNN", ["bytes"], [Enc(["uint8[][]"], [[[1, 2], [3]]])]),
    ("AbiDecode", "dBy", ["bytes"], [Enc(["bytes"], [b"hi"])]),
    ("AbiDecode", "dS", ["bytes"], [Enc([S], [SV])]),
    ("AbiDecode", "dMix", ["bytes"], [Enc(["uint8", "bytes"], [7, b"hi"])]),
    ("AbiDecode", "dCd", ["bytes"], [Enc(["uint8[]"], [[1, 2]])]),
    ("AbiDecode", "dCdNN", ["bytes"], [Enc(["uint8[][]"], [[[1], [2, 3]]])]),

    ("AbiEncode", "target", ["uint8", "bytes"], [1, b"ab"]),
    ("AbiEncode", "eE", ["uint8", "bytes", "uint16[]"], [7, b"hi", [1, 2]]),
    ("AbiEncode", "eP", ["uint8", "bytes", "uint16[]"], [7, b"hi", [1, 2]]),
    ("AbiEncode", "ePbool", ["bool", "int8", "bytes3", "address"], [True, -3, b"\x01\x02\x03", 0xDEAD]),
    ("AbiEncode", "ePstr", ["string", "bytes32"], ["hi", B32]),
    ("AbiEncode", "eSel", ["uint8", "bytes"], [7, b"hi"]),
    ("AbiEncode", "eSig", ["uint8", "bytes"], [7, b"hi"]),
    ("AbiEncode", "eCall", ["uint8", "bytes"], [7, b"hi"]),
    ("AbiEncode", "eS", [S], [SV2]),
    ("AbiEncode", "eNested", ["uint8[][]", "bytes[]"], [[[1], [2, 3]], [b"a", b"b" * 33]]),
    ("AbiEncode", "eDirty", ["uint256"], [0x1FF]),
    ("AbiEncode", "ePDirty", ["uint256"], [0x80]),
    ("AbiEncode", "ePDirty", ["uint256"], [0x1FF]),
    ("AbiEncode", "rErr", ["uint8", "bytes"], [7, b"hi"]),
    ("AbiEncode", "rStr", ["string"], ["boom"]),
    ("AbiEncode", "rReq", ["bool", "string"], [False, "no"]),
    ("AbiEncode", "rReq", ["bool", "string"], [True, "no"]),
    ("AbiEncode", "rAssert", ["bool"], [False]),

    ("AbiRequireError", "reqPos", ["bool", "uint8", "bytes"], [False, 7, b"hi"]),
    ("AbiRequireError", "reqNamed", ["bool", "uint8", "bytes"], [False, 7, b"hi"]),
    ("AbiRequireError", "reqNamed", ["bool", "uint8", "bytes"], [True, 7, b"hi"]),
]


def abi_name(ty):
    return {"enum": "uint8"}.get(ty, ty)


def signature(fn, types):
    return f"{fn}({','.join(abi_name(t) for t in types)})"
