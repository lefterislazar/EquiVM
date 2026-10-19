import Solidity.Test.Harness
import Solidity.Test.Specs.ViaIRStorage
import Solidity.Test.Fixtures.ViaIRStorageSolc

/-! # Differential cases: the via-IR storage algorithms on storage holding bytes no value covers.

The fixture is compiled with `--via-ir`.  Each case seeds the contract's storage: slots of `0xff…`
behind a struct or a packed array, dirty elements past a dynamic array's length, and dirty bytes
after a short `bytes` value.  On such storage `delete` zeroes whole slots, packed arrays are
written whole slots at a time, and `bytes` push/pop change only the header and the affected byte. -/

namespace Solidity.Test.ViaIRStorage

open Solidity.Test

def runtime : ByteArray := bytesOfHex Fixtures.viaIRStorageRuntimeHex

def full : Ethereum.UInt256 := word (2 ^ 256 - 1)

/-- Layout of the fixture: `s` in slots 0–2, `p` in slot 3, `dp` in slot 4, `b` in slot 5. -/
def dirtyStruct : List (Ethereum.UInt256 × Ethereum.UInt256) := [(word 0, full), (word 1, full), (word 2, full)]
def dirtyP : List (Ethereum.UInt256 × Ethereum.UInt256) := [(word 3, full)]

/-- `dp` of length 3 (`[7, 7, 7]`) whose data slot is `0xff` from element 3 on. -/
def dirtyDp : List (Solm.EvaledStorageRef × Nat) :=
  ({ base := "dp", steps := [] }, 3) ::
    (List.range 32).map fun i => ({ base := "dp", steps := [.aindex (.int i)] }, if i < 3 then 7 else 255)

/-- `b` of length `n < 32` followed by `0xff` bytes in the header slot. -/
def dirtyShortBytes (n : Nat) : List (Ethereum.UInt256 × Ethereum.UInt256) :=
  [(word 5, word ((2 ^ 256 - 1) / 256 * 256 + 2 * n))]

def u8s (xs : List Nat) : Solm.Value := .array (xs.map fun x => .int x)
def b1 (n : Nat) : Solm.Value := .fixedBytes ⟨0, by decide⟩ [UInt8.ofNat n]

def mk (sig : String) (args : List Solm.Value) (tag : String) (storage : List (Ethereum.UInt256 × Ethereum.UInt256) := [])
    (refs : List (Solm.EvaledStorageRef × Nat) := []) (expect : Expect := .success) : Case :=
  { name := s!"{sig} {tag}", code := runtime, call := some (sig, args), storage := storage, refs := refs,
    expect := expect }

def cases : List Case :=
  [ mk "deleteS()" [] "clean",
    mk "deleteS()" [] "dirty slots" dirtyStruct,
    mk "setS(uint8,uint128,uint256,int16)" [.int 1, .int 2, .int 3, .int (-4)] "dirty slots" dirtyStruct,
    mk "setP(uint8[5])" [u8s [1, 2, 3, 4, 5]] "clean",
    mk "setP(uint8[5])" [u8s [1, 2, 3, 4, 5]] "dirty slot" dirtyP,
    mk "deleteP()" [] "dirty slot" dirtyP,
    mk "setDp(uint8[])" [u8s [1, 2, 3, 4, 5]] "grow, dirty tail" (refs := dirtyDp),
    mk "setDp(uint8[])" [u8s [1]] "shrink, dirty tail" (refs := dirtyDp),
    mk "setDp(uint8[])" [u8s ((List.range 40).map (· + 1))] "two slots",
    mk "deleteDp()" [] "dirty tail" (refs := dirtyDp),
    mk "pushDp()" [] "dirty tail" (refs := dirtyDp),
    mk "popDp()" [] "dirty tail" (refs := dirtyDp),
    mk "popDp()" [] "empty" (expect := .revert),
    mk "getDp()" [] "dirty tail" (refs := dirtyDp),
    mk "pushB()" [] "short, dirty" (dirtyShortBytes 5),
    mk "pushBv(bytes1)" [b1 0x41] "short, dirty" (dirtyShortBytes 5),
    mk "popB()" [] "short, dirty" (dirtyShortBytes 5),
    mk "getB()" [] "short, dirty" (dirtyShortBytes 5),
    mk "pushB()" [] "31 bytes to long" (dirtyShortBytes 31),
    mk "pushBv(bytes1)" [b1 0x41] "31 bytes to long" (dirtyShortBytes 31),
    mk "popB()" [] "empty" (expect := .revert) ]

def scenario : Scenario :=
  { name := "ViaIRStorage", program := _root_.ViaIRStorage.SoliditySpec.program, target := "ViaIRStorage",
    cases := cases }

end Solidity.Test.ViaIRStorage
