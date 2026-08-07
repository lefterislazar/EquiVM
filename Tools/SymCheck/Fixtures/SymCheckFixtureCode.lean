import Ethereum.Semantics

open Ethereum

/-- Small dynamic-branch bytecode used to compile-check generated symbolic edge theorems. -/
def symCheckBranchFixtureBytecode : ByteArray :=
  ⟨#[0x57, 0x00, 0x5b, 0x8b, 0x9f, 0x00, 0x5b, 0x56]⟩
