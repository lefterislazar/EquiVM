import Benchmarks.ActAmm.Swap1Base
import Benchmarks.ActAmm.BurnTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammSwap1X_toDecoder
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨314⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5654⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨335⟩, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨340⟩, push1 ⟨4⟩, dup1,
    calldatasize, sub, dup2, add, swap1,
    push2 ⟨335⟩, swap2, swap1,
    push2 ⟨5654⟩, jump (by jump_dest)]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4)
    hsize] at rd'
  exact ⟨_, _, rd'⟩

theorem ammSwap1X_shortarg
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨314⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g
      (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨_, _, rd⟩ := ammSwap1X_toDecoder hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt,
    iszero, push2 ⟨5676⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨5675⟩, push2 ⟨5396⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov)]

theorem ammSwap1X_hugearg
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨314⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g
      (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨_, _, rd⟩ := ammSwap1X_toDecoder hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt,
    iszero, push2 ⟨5676⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨5675⟩, push2 ⟨5396⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov)]

theorem ammSwap1X_dec5521_value
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨314⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5521⟩
      [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨5689⟩,
        ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size,
        ⟨335⟩, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨_, _, rd⟩ := ammSwap1X_toDecoder
    (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt,
    iszero, push2 ⟨5676⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, push2 ⟨5689⟩, dup6, dup3, dup7, add,
    push2 ⟨5521⟩, jump (by jump_dest)]⟩

theorem ammSwap1X_dec5689
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨314⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5689⟩
      [ammSwap1AmountWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨335⟩, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := ammSwap1X_dec5521_value
    hsz68 hsize hszhi hreach
  exact RD.ammDecodeUint256Ok rd (by jump_dest) (by evm_ov)

theorem ammSwap1X_dec5470_to
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨314⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨5470⟩
      [⟨4⟩ + ⟨32⟩, UInt256.ofNat I.calldata.size, ⟨5706⟩,
        ⟨32⟩, ⟨0⟩, ammSwap1AmountWord I, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨335⟩, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := ammSwap1X_dec5689
    hsz68 hsize hszhi hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, pop, pop, push1 ⟨32⟩, push2 ⟨5706⟩,
    dup6, dup3, dup7, add, push2 ⟨5470⟩, jump (by jump_dest)]⟩

theorem ammSwap1X_decoded
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonTo : (ammSwap1ToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨314⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2563⟩
      [ammSwap1ToWord I, ammSwap1AmountWord I, ⟨340⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := ammSwap1X_dec5470_to
    hsz68 hsize hszhi hreach
  obtain ⟨_, _, rd5706⟩ := RD.ammDecodeAddrOk rd hcanonTo
    (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd5706 with [
    jumpdest, swap2, pop, pop, swap3, pop, swap3, swap1, pop,
    jump (by jump_dest),
    jumpdest, push2 ⟨2563⟩, jump (by jump_dest)]⟩

theorem ammSwap1X_noncanon
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (ammSwap1ToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨314⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g
      (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := ammSwap1X_dec5470_to
    hsz68 hsize hbig hreach
  have hunclean : UInt256.eq (ammSwap1ToWord I)
      (UInt256.land (ammSwap1ToWord I) solcAddrMask) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne
      (fun he => hnc (solcAddrCanonical_of_clean he))
  exact RD.ammDecodeAddrRevert rd hunclean (by evm_ov)

end Benchmarks.ActAmm
