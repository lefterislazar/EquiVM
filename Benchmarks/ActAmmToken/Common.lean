import Benchmarks.ActAmmToken.Trusted
import Reasoning.ABI
import Reasoning.Stepping
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Dispatch
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmmToken

/-- The selector left on the EVM stack after the dispatcher prefix. -/
abbrev tokenSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Selectors in bytecode order: four below the pivot and five at or above it. -/
def tokenSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩ -- approve
  | 1 => ⟨#[0x18, 0x16, 0x0d, 0xdd]⟩ -- totalSupply
  | 2 => ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩ -- transferFrom
  | 3 => ⟨#[0x40, 0xc1, 0x0f, 0x19]⟩ -- mint
  | 4 => ⟨#[0x42, 0x96, 0x6c, 0x68]⟩ -- burn
  | 5 => ⟨#[0x70, 0xa0, 0x82, 0x31]⟩ -- balanceOf
  | 6 => ⟨#[0x79, 0xcc, 0x67, 0x90]⟩ -- burnFrom
  | 7 => ⟨#[0xb7, 0x76, 0x0c, 0x8f]⟩ -- transfer
  | _ => ⟨#[0xdd, 0x62, 0xed, 0x3e]⟩ -- allowance

-- LIBRARY CANDIDATE: Reasoning.Solc, the caller's address as a mapping key.
theorem tokenSource_keyValueToWord (a : AccountAddress) :
    keyValueToWord (.address a) = UInt256.ofNat a.val := by
  apply u256_inj
  unfold keyValueToWord UInt256.ofNat
  change a.val = (Fin.ofNat UInt256.size a.val).val
  rw [Fin.val_ofNat]
  exact (Nat.mod_eq_of_lt
    (lt_of_lt_of_le a.isLt
      (show AccountAddress.size ≤ UInt256.size from by decide))).symm

end Benchmarks.ActAmmToken
