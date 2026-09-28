import Benchmarks.ActAmm.BurnBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem ammBurnX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨534⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5654⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨555⟩, ⟨560⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨560⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨555⟩, swap2, swap1, push2 ⟨5654⟩, jump (by jump_dest) ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

theorem ammBurnX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨534⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      ⟨64⟩ = ⟨1⟩ := solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨_, _, rd⟩ := ammBurnX_toDecoder hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨5676⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨5675⟩, push2 ⟨5396⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem ammBurnX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨534⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      ⟨64⟩ = ⟨1⟩ := solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨_, _, rd⟩ := ammBurnX_toDecoder hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨5676⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨5675⟩, push2 ⟨5396⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem ammBurnX_dec5521_value {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨534⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5521⟩
      [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨5689⟩, ⟨0⟩, ⟨0⟩,
        ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨555⟩, ⟨560⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨_, _, rd⟩ := ammBurnX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨5676⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, push2 ⟨5689⟩, dup6, dup3, dup7, add, push2 ⟨5521⟩,
    jump (by jump_dest) ]⟩

theorem ammBurnX_dec5689 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨534⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5689⟩
      [ammBurnLiquidityWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨555⟩, ⟨560⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := ammBurnX_dec5521_value (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  exact RD.ammDecodeUint256Ok rd (by jump_dest) (by evm_ov)

theorem ammBurnX_dec5470_to {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨534⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5470⟩
      [⟨4⟩ + ⟨32⟩, UInt256.ofNat I.calldata.size, ⟨5706⟩, ⟨32⟩,
        ⟨0⟩, ammBurnLiquidityWord I, ⟨4⟩, UInt256.ofNat I.calldata.size,
        ⟨555⟩, ⟨560⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := ammBurnX_dec5689 (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, pop, pop, push1 ⟨32⟩, push2 ⟨5706⟩,
    dup6, dup3, dup7, add, push2 ⟨5470⟩, jump (by jump_dest) ]⟩

theorem ammBurnX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonTo : (ammBurnToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨534⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4582⟩
      [ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := ammBurnX_dec5470_to (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  obtain ⟨_, _, rd5706⟩ := RD.ammDecodeAddrOk rd hcanonTo
    (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd5706 with [
    jumpdest, swap2, pop, pop, swap3, pop, swap3, swap1, pop,
    jump (by jump_dest),
    jumpdest, push2 ⟨4582⟩, jump (by jump_dest) ]⟩

theorem ammBurnX_noncanon {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (ammBurnToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨534⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := ammBurnX_dec5470_to hsz68 hsize hbig hreach
  have hunclean : UInt256.eq (ammBurnToWord I)
      (UInt256.land (ammBurnToWord I) solcAddrMask) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he => hnc (solcAddrCanonical_of_clean he))
  exact RD.ammDecodeAddrRevert rd hunclean (by evm_ov)

theorem ammBurnX_zeroSupply {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammBurnToWord I).toNat < EVM.addressModulus)
    (hzero : solcSlotWord σ I ⟨0⟩ = ⟨0⟩)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨534⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd4582⟩ := ammBurnX_decoded
    hsz68 hsize hbig hcanon hreach
  have rd4584 := evm_run rd4582 with [jumpdest, push0, push0]
  obtain ⟨_, _, rd4585₀⟩ := rd4584.sload (by native_decide) (by evm_ov)
  have rd4585 := rd4585₀
  simp only [solcSlotWord] at hzero
  rw [hzero] at rd4585
  exact evm_run rd4585 with [
    sub, push2 ⟨4594⟩, jumpiNT (by decide),
    raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem ammBurnX_nonzeroSupply {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (ammBurnToWord I).toNat < EVM.addressModulus)
    (hnonzero : solcSlotWord σ I ⟨0⟩ ≠ ⟨0⟩)
    (hreach : ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨534⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4594⟩
      [ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd4582⟩ := ammBurnX_decoded
    hsz68 hsize hbig hcanon hreach
  have rd4584 := evm_run rd4582 with [jumpdest, push0, push0]
  obtain ⟨_, _, rd4585⟩ := rd4584.sload (by native_decide) (by evm_ov)
  have rd4586 := evm_run rd4585 with [sub]
  have hsub : UInt256.sub (solcSlotWord σ I ⟨0⟩) ⟨0⟩ =
      solcSlotWord σ I ⟨0⟩ := by
    apply u256_inj
    rw [usub_toNat (by simp)]
    simp
  have hsub' := hsub
  simp only [solcSlotWord] at hsub'
  rw [hsub'] at rd4586
  have hnonzero' := hnonzero
  simp only [solcSlotWord] at hnonzero'
  exact ⟨_, _, evm_run rd4586 with [
    push2 ⟨4594⟩,
    jumpiT (by simpa [UInt256.isZero] using hnonzero') (by jump_dest) ]⟩

theorem ammBurnX_amount0NumeratorOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : Nat}
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4594⟩
      [ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hfit : (ammBurnLiquidityWord I).toNat *
      (solcSlotWord σ I ⟨5⟩).toNat < UInt256.size) :
    ∃ k' C', RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4611⟩
      [UInt256.mul (ammBurnLiquidityWord I) (solcSlotWord σ I ⟨5⟩),
        solcSlotWord σ I ⟨0⟩, ⟨0⟩, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd4596 := evm_run rd with [jumpdest, push0, push0]
  obtain ⟨_, _, rd4597⟩ := rd4596.sload (by native_decide) (by evm_ov)
  have rd4599 := evm_run rd4597 with [push1 ⟨5⟩]
  obtain ⟨_, _, rd4600⟩ := rd4599.sload (by native_decide) (by evm_ov)
  have rd6747 := evm_run rd4600 with [
    dup5, push2 ⟨4611⟩, swap2, swap1, push2 ⟨6747⟩,
    jump (by jump_dest)]
  exact RD.ammCheckedMulOk rd6747 hfit (by jump_dest) (by evm_ov)

theorem ammBurnX_amount0NumeratorOverflow {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {k C : Nat}
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4594⟩
      [ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hover : UInt256.size ≤ (ammBurnLiquidityWord I).toNat *
      (solcSlotWord σ I ⟨5⟩).toNat) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd4596 := evm_run rd with [jumpdest, push0, push0]
  obtain ⟨_, _, rd4597⟩ := rd4596.sload (by native_decide) (by evm_ov)
  have rd4599 := evm_run rd4597 with [push1 ⟨5⟩]
  obtain ⟨_, _, rd4600⟩ := rd4599.sload (by native_decide) (by evm_ov)
  have rd6747 := evm_run rd4600 with [
    dup5, push2 ⟨4611⟩, swap2, swap1, push2 ⟨6747⟩,
    jump (by jump_dest)]
  exact RD.ammCheckedMulOverflowWide
    (a := ammBurnLiquidityWord I) (b := solcSlotWord σ I ⟨5⟩)
    (ret := ⟨4611⟩)
    (R := [solcSlotWord σ I ⟨0⟩, ⟨0⟩, ammBurnToWord I,
      ammBurnLiquidityWord I, ⟨560⟩, sel])
    rd6747 hover (by decide) (by evm_ov)

theorem ammBurnX_amount0Ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : Nat}
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4611⟩
      [UInt256.mul (ammBurnLiquidityWord I) (solcSlotWord σ I ⟨5⟩),
        solcSlotWord σ I ⟨0⟩, ⟨0⟩, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnonzero : solcSlotWord σ I ⟨0⟩ ≠ ⟨0⟩) :
    ∃ k' C', RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4624⟩
      [UInt256.div
        (UInt256.mul (ammBurnLiquidityWord I) (solcSlotWord σ I ⟨5⟩))
        (solcSlotWord σ I ⟨0⟩),
        ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd6857 := evm_run rd with [
    jumpdest, push2 ⟨4621⟩, swap2, swap1,
    push2 ⟨6857⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd4621⟩ := RD.ammCheckedDivOk rd6857 hnonzero
    (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd4621 with [jumpdest, swap1, pop]⟩

theorem ammBurnX_amount1NumeratorOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel q0 : UInt256} {k C : Nat}
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4624⟩
      [q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hfit : (ammBurnLiquidityWord I).toNat *
      (solcSlotWord σ I ⟨6⟩).toNat < UInt256.size) :
    ∃ k' C', RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4640⟩
      [UInt256.mul (ammBurnLiquidityWord I) (solcSlotWord σ I ⟨6⟩),
        solcSlotWord σ I ⟨0⟩, ⟨0⟩, q0,
        ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd4626 := evm_run rd with [push0, push0]
  obtain ⟨_, _, rd4627⟩ := rd4626.sload (by native_decide) (by evm_ov)
  have rd4629 := evm_run rd4627 with [push1 ⟨6⟩]
  obtain ⟨_, _, rd4630⟩ := rd4629.sload (by native_decide) (by evm_ov)
  have rd6747 := evm_run rd4630 with [
    dup6, push2 ⟨4640⟩, swap2, swap1, push2 ⟨6747⟩,
    jump (by jump_dest)]
  exact RD.ammCheckedMulOk rd6747 hfit (by jump_dest) (by evm_ov)

theorem ammBurnX_amount1NumeratorOverflow {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel q0 : UInt256} {k C : Nat}
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4624⟩
      [q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hover : UInt256.size ≤ (ammBurnLiquidityWord I).toNat *
      (solcSlotWord σ I ⟨6⟩).toNat) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd4626 := evm_run rd with [push0, push0]
  obtain ⟨_, _, rd4627⟩ := rd4626.sload (by native_decide) (by evm_ov)
  have rd4629 := evm_run rd4627 with [push1 ⟨6⟩]
  obtain ⟨_, _, rd4630⟩ := rd4629.sload (by native_decide) (by evm_ov)
  have rd6747 := evm_run rd4630 with [
    dup6, push2 ⟨4640⟩, swap2, swap1, push2 ⟨6747⟩,
    jump (by jump_dest)]
  exact RD.ammCheckedMulOverflowWide
    (a := ammBurnLiquidityWord I) (b := solcSlotWord σ I ⟨6⟩)
    (ret := ⟨4640⟩)
    (R := [solcSlotWord σ I ⟨0⟩, ⟨0⟩, q0,
      ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel])
    rd6747 hover (by decide) (by evm_ov)

theorem ammBurnX_amount1Ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel q0 : UInt256} {k C : Nat}
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4640⟩
      [UInt256.mul (ammBurnLiquidityWord I) (solcSlotWord σ I ⟨6⟩),
        solcSlotWord σ I ⟨0⟩, ⟨0⟩, q0,
        ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnonzero : solcSlotWord σ I ⟨0⟩ ≠ ⟨0⟩) :
    ∃ k' C', RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4653⟩
      [UInt256.div
        (UInt256.mul (ammBurnLiquidityWord I) (solcSlotWord σ I ⟨6⟩))
        (solcSlotWord σ I ⟨0⟩),
        q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd6857 := evm_run rd with [
    jumpdest, push2 ⟨4650⟩, swap2, swap1,
    push2 ⟨6857⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd4650⟩ := RD.ammCheckedDivOk rd6857 hnonzero
    (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd4650 with [jumpdest, swap1, pop]⟩

theorem ammBurnX_supplyUnderflow {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {k C : Nat}
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4653⟩
      [q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hunder : (solcSlotWord σ I ⟨0⟩).toNat <
      (ammBurnLiquidityWord I).toNat) :
    RDrev ammBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd4657 := evm_run rd with [dup4, push0, push0, dup3, dup3]
  obtain ⟨_, _, rd4658⟩ := rd4657.sload (by native_decide) (by evm_ov)
  have rd6645 := evm_run rd4658 with [
    push2 ⟨4668⟩, swap2, swap1, push2 ⟨6645⟩,
    jump (by jump_dest)]
  exact RD.ammCheckedSubUnderflowWide rd6645 hunder
    (by decide) (by evm_ov)

theorem ammBurnX_supplyStored {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {k C : Nat}
    (rd : RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4653⟩
      [q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hle : (ammBurnLiquidityWord I).toNat ≤
      (solcSlotWord σ I ⟨0⟩).toNat)
    (hperm : I.perm = true) :
    ∃ k' C', RD ammBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4676⟩
      [q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩
        (UInt256.sub (solcSlotWord σ I ⟨0⟩) (ammBurnLiquidityWord I)))
      k' C' := by
  have rd4657 := evm_run rd with [dup4, push0, push0, dup3, dup3]
  obtain ⟨_, _, rd4658⟩ := rd4657.sload (by native_decide) (by evm_ov)
  have rd6645 := evm_run rd4658 with [
    push2 ⟨4668⟩, swap2, swap1, push2 ⟨6645⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd4668⟩ := RD.ammCheckedSubOk rd6645 hle
    (by jump_dest) (by evm_ov)
  have rd4673 := evm_run rd4668 with [
    jumpdest, swap3, pop, pop, dup2, swap1]
  obtain ⟨_, _, rd4674⟩ := rd4673.sstore hperm
    (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd4674 with [pop]⟩

theorem ammBurnX_senderLoad {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4676⟩
      [q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4742⟩
      [solcSlotWord σ I (ammTransferSenderSlot I),
        ammBurnLiquidityWord I, ⟨0⟩, ammTransferSenderSlot I,
        ammBurnLiquidityWord I, q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have rd4725₀ := evm_run rd with [
    dup4, push1 ⟨1⟩, push0, caller,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  have rd4725 := rd4725₀
  rw [hsourceClean, hsourceClean] at rd4725
  obtain ⟨_, _, rd4738⟩ := RD.ammMappingHashSuffix rd4725
    amm_mapping_hash_wf (by rfl) (by rfl)
    (by simpa [ammTransferSenderSlot_eq_solc I] using
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (solcSourceWord I)
        solcFreePtrMem_size))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4741 := evm_run rd4738 with [push0, dup3, dup3]
  obtain ⟨_, _, rd4742⟩ := rd4741.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rd4742⟩

theorem ammBurnX_senderUnderflow {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4742⟩
      [solcSlotWord σ I (ammTransferSenderSlot I),
        ammBurnLiquidityWord I, ⟨0⟩, ammTransferSenderSlot I,
        ammBurnLiquidityWord I, q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hunder : (solcSlotWord σ I (ammTransferSenderSlot I)).toNat <
      (ammBurnLiquidityWord I).toNat) :
    RDrev ammBytecode g (initState cAstart gh bl σstart σ₀ g A I) := by
  have rd6645 := evm_run rd with [
    push2 ⟨4751⟩, swap2, swap1, push2 ⟨6645⟩,
    jump (by jump_dest)]
  exact RD.ammCheckedSubUnderflowWide rd6645 hunder
    (by decide) (by evm_ov)

theorem ammBurnX_senderStored {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {k C : Nat}
    (rd : RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4742⟩
      [solcSlotWord σ I (ammTransferSenderSlot I),
        ammBurnLiquidityWord I, ⟨0⟩, ammTransferSenderSlot I,
        ammBurnLiquidityWord I, q1, q0, ammBurnToWord I,
        ammBurnLiquidityWord I, ⟨560⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hle : (ammBurnLiquidityWord I).toNat ≤
      (solcSlotWord σ I (ammTransferSenderSlot I)).toNat)
    (hperm : I.perm = true) :
    ∃ k' C', RD ammBytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨4759⟩
      [q1, q0, ammBurnToWord I, ammBurnLiquidityWord I, ⟨560⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (ammTransferSenderSlot I)
        (UInt256.sub (solcSlotWord σ I (ammTransferSenderSlot I))
          (ammBurnLiquidityWord I))) k' C' := by
  have rd6645 := evm_run rd with [
    push2 ⟨4751⟩, swap2, swap1, push2 ⟨6645⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd4751⟩ := RD.ammCheckedSubOk rd6645 hle
    (by jump_dest) (by evm_ov)
  have rd4756 := evm_run rd4751 with [
    jumpdest, swap3, pop, pop, dup2, swap1]
  obtain ⟨_, _, rd4757⟩ := rd4756.sstore hperm
    (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd4757 with [pop]⟩

end Benchmarks.ActAmm
