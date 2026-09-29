import Benchmarks.ActAmm4.SwapDecodeTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapX_badLength
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hslt : UInt256.slt
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      ⟨96⟩ = ⟨1⟩)
    (hreach : ∃ k C, RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I)
      ⟨323⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g
      (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := amm4SwapX_toDecoder hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩,
    dup5, dup7, sub, slt, iszero,
    push2 ⟨5027⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨5026⟩, push2 ⟨4583⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide)
      (by native_decide) (by native_decide) (by evm_ov)]

theorem amm4SwapX_shortarg
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I)
      ⟨323⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g
      (initState cA gh bl σ σ₀ g A I) := by
  exact amm4SwapX_badLength hsz4 hsize
    (by simpa using (solcCalldataStaticLenCheckShort
      (words := 3) hsz4 (by omega : I.calldata.size < 4 + 32 * 3)
      hsize (by norm_num))) hreach

theorem amm4SwapX_hugearg
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I)
      ⟨323⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g
      (initState cA gh bl σ σ₀ g A I) := by
  exact amm4SwapX_badLength hsz4 hsize
    (by simpa using (solcCalldataStaticLenCheckHuge
      (words := 3) hbig hsize (by norm_num))) hreach

theorem amm4SwapX_noncanon
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (amm4SwapToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g
      (initState cA gh bl σ σ₀ g A I)
      ⟨323⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g
      (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := amm4SwapX_dec4657_to
    hsz100 hsize hbig hreach
  have hunclean : UInt256.eq (amm4SwapToWord I)
      (UInt256.land (amm4SwapToWord I) solcAddrMask) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne
      (fun he => hnc (solcAddrCanonical_of_clean he))
  exact RD.amm4DecodeAddrRevert rd hunclean (by evm_ov)

end Benchmarks.ActAmm4
