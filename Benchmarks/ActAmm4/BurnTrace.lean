import Benchmarks.ActAmm4.BurnBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4BurnX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨495⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5084⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨516⟩, ⟨521⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨521⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨516⟩, swap2, swap1, push2 ⟨5084⟩, jump (by jump_dest) ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

theorem amm4BurnX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨495⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      ⟨64⟩ = ⟨1⟩ := solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  obtain ⟨_, _, rd⟩ := amm4BurnX_toDecoder hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨5106⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨5105⟩, push2 ⟨4583⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem amm4BurnX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨495⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      ⟨64⟩ = ⟨1⟩ := solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨_, _, rd⟩ := amm4BurnX_toDecoder hsz4 hsize hreach
  exact evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨5106⟩, jumpiNT (by rw [hslt]; decide),
    push2 ⟨5105⟩, push2 ⟨4583⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem amm4BurnX_dec4708_value {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨495⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4708⟩
      [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨5119⟩, ⟨0⟩, ⟨0⟩,
        ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨516⟩, ⟨521⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨_, _, rd⟩ := amm4BurnX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨5106⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, push2 ⟨5119⟩, dup6, dup3, dup7, add, push2 ⟨4708⟩,
    jump (by jump_dest) ]⟩

theorem amm4BurnX_dec5119 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨495⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5119⟩
      [amm4BurnLiquidityWord I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨516⟩, ⟨521⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4BurnX_dec4708_value (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  exact RD.amm4DecodeUint256Ok rd (by jump_dest) (by evm_ov)

theorem amm4BurnX_dec4657_to {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨495⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4657⟩
      [⟨4⟩ + ⟨32⟩, UInt256.ofNat I.calldata.size, ⟨5136⟩, ⟨32⟩,
        ⟨0⟩, amm4BurnLiquidityWord I, ⟨4⟩, UInt256.ofNat I.calldata.size,
        ⟨516⟩, ⟨521⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4BurnX_dec5119 (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, pop, pop, push1 ⟨32⟩, push2 ⟨5136⟩,
    dup6, dup3, dup7, add, push2 ⟨4657⟩, jump (by jump_dest) ]⟩

theorem amm4BurnX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonTo : (amm4BurnToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨495⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3769⟩
      [amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4BurnX_dec4657_to (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz68 hsize hszhi hreach
  obtain ⟨_, _, rd5136⟩ := RD.amm4DecodeAddrOk rd hcanonTo
    (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd5136 with [
    jumpdest, swap2, pop, pop, swap3, pop, swap3, swap1, pop,
    jump (by jump_dest),
    jumpdest, push2 ⟨3769⟩, jump (by jump_dest) ]⟩

theorem amm4BurnX_noncanon {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (amm4BurnToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨495⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd⟩ := amm4BurnX_dec4657_to hsz68 hsize hbig hreach
  have hunclean : UInt256.eq (amm4BurnToWord I)
      (UInt256.land (amm4BurnToWord I) solcAddrMask) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he => hnc (solcAddrCanonical_of_clean he))
  exact RD.amm4DecodeAddrRevert rd hunclean (by evm_ov)

theorem amm4BurnX_zeroSupply {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (amm4BurnToWord I).toNat < EVM.addressModulus)
    (hzero : solcSlotWord σ I ⟨0⟩ = ⟨0⟩)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨495⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3769⟩ := amm4BurnX_decoded
    hsz68 hsize hbig hcanon hreach
  have rd3771 := evm_run rd3769 with [jumpdest, push0, push0]
  obtain ⟨_, _, rd3772₀⟩ := rd3771.sload (by native_decide) (by evm_ov)
  have rd3772 := rd3772₀
  simp only [solcSlotWord] at hzero
  rw [hzero] at rd3772
  exact evm_run rd3772 with [
    sub, push2 ⟨3781⟩, jumpiNT (by decide),
    raw revertStub (by native_decide) (by native_decide)
      (by native_decide) (by evm_ov) ]

theorem amm4BurnX_nonzeroSupply {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (amm4BurnToWord I).toNat < EVM.addressModulus)
    (hnonzero : solcSlotWord σ I ⟨0⟩ ≠ ⟨0⟩)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨495⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3781⟩
      [amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3769⟩ := amm4BurnX_decoded
    hsz68 hsize hbig hcanon hreach
  have rd3771 := evm_run rd3769 with [jumpdest, push0, push0]
  obtain ⟨_, _, rd3772⟩ := rd3771.sload (by native_decide) (by evm_ov)
  have rd3773 := evm_run rd3772 with [sub]
  have hsub : UInt256.sub (solcSlotWord σ I ⟨0⟩) ⟨0⟩ =
      solcSlotWord σ I ⟨0⟩ := by
    apply u256_inj
    rw [usub_toNat (by simp)]
    simp
  have hsub' := hsub
  simp only [solcSlotWord] at hsub'
  rw [hsub'] at rd3773
  have hnonzero' := hnonzero
  simp only [solcSlotWord] at hnonzero'
  exact ⟨_, _, evm_run rd3773 with [
    push2 ⟨3781⟩,
    jumpiT (by simpa [UInt256.isZero] using hnonzero') (by jump_dest) ]⟩

theorem amm4BurnX_amount0NumeratorOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : Nat}
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3781⟩
      [amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hfit : (amm4BurnLiquidityWord I).toNat *
      (solcSlotWord σ I ⟨5⟩).toNat < UInt256.size) :
    ∃ k' C', RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3798⟩
      [UInt256.mul (amm4BurnLiquidityWord I) (solcSlotWord σ I ⟨5⟩),
        solcSlotWord σ I ⟨0⟩, ⟨0⟩, amm4BurnToWord I,
        amm4BurnLiquidityWord I, ⟨521⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd3783 := evm_run rd with [jumpdest, push0, push0]
  obtain ⟨_, _, rd3784⟩ := rd3783.sload (by native_decide) (by evm_ov)
  have rd3786 := evm_run rd3784 with [push1 ⟨5⟩]
  obtain ⟨_, _, rd3787⟩ := rd3786.sload (by native_decide) (by evm_ov)
  have rd5458 := evm_run rd3787 with [
    dup5, push2 ⟨3798⟩, swap2, swap1, push2 ⟨5458⟩,
    jump (by jump_dest)]
  exact RD.amm4CheckedMulOk rd5458 hfit (by jump_dest) (by evm_ov)

theorem amm4BurnX_amount0NumeratorOverflow {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256} {k C : Nat}
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3781⟩
      [amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hover : UInt256.size ≤ (amm4BurnLiquidityWord I).toNat *
      (solcSlotWord σ I ⟨5⟩).toNat) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd3783 := evm_run rd with [jumpdest, push0, push0]
  obtain ⟨_, _, rd3784⟩ := rd3783.sload (by native_decide) (by evm_ov)
  have rd3786 := evm_run rd3784 with [push1 ⟨5⟩]
  obtain ⟨_, _, rd3787⟩ := rd3786.sload (by native_decide) (by evm_ov)
  have rd5458 := evm_run rd3787 with [
    dup5, push2 ⟨3798⟩, swap2, swap1, push2 ⟨5458⟩,
    jump (by jump_dest)]
  exact RD.amm4CheckedMulOverflowWide
    (a := amm4BurnLiquidityWord I) (b := solcSlotWord σ I ⟨5⟩)
    (ret := ⟨3798⟩)
    (R := [solcSlotWord σ I ⟨0⟩, ⟨0⟩, amm4BurnToWord I,
      amm4BurnLiquidityWord I, ⟨521⟩, sel])
    rd5458 hover (by decide) (by evm_ov)

theorem amm4BurnX_amount0Ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : Nat}
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3798⟩
      [UInt256.mul (amm4BurnLiquidityWord I) (solcSlotWord σ I ⟨5⟩),
        solcSlotWord σ I ⟨0⟩, ⟨0⟩, amm4BurnToWord I,
        amm4BurnLiquidityWord I, ⟨521⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnonzero : solcSlotWord σ I ⟨0⟩ ≠ ⟨0⟩) :
    ∃ k' C', RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3811⟩
      [UInt256.div
        (UInt256.mul (amm4BurnLiquidityWord I) (solcSlotWord σ I ⟨5⟩))
        (solcSlotWord σ I ⟨0⟩),
        amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd5568 := evm_run rd with [
    jumpdest, push2 ⟨3808⟩, swap2, swap1,
    push2 ⟨5568⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd3808⟩ := RD.amm4CheckedDivOk rd5568 hnonzero
    (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd3808 with [jumpdest, swap1, pop]⟩

theorem amm4BurnX_amount1NumeratorOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel q0 : UInt256} {k C : Nat}
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3811⟩
      [q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hfit : (amm4BurnLiquidityWord I).toNat *
      (solcSlotWord σ I ⟨6⟩).toNat < UInt256.size) :
    ∃ k' C', RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3827⟩
      [UInt256.mul (amm4BurnLiquidityWord I) (solcSlotWord σ I ⟨6⟩),
        solcSlotWord σ I ⟨0⟩, ⟨0⟩, q0,
        amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd3813 := evm_run rd with [push0, push0]
  obtain ⟨_, _, rd3814⟩ := rd3813.sload (by native_decide) (by evm_ov)
  have rd3816 := evm_run rd3814 with [push1 ⟨6⟩]
  obtain ⟨_, _, rd3817⟩ := rd3816.sload (by native_decide) (by evm_ov)
  have rd5458 := evm_run rd3817 with [
    dup6, push2 ⟨3827⟩, swap2, swap1, push2 ⟨5458⟩,
    jump (by jump_dest)]
  exact RD.amm4CheckedMulOk rd5458 hfit (by jump_dest) (by evm_ov)

theorem amm4BurnX_amount1NumeratorOverflow {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel q0 : UInt256} {k C : Nat}
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3811⟩
      [q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hover : UInt256.size ≤ (amm4BurnLiquidityWord I).toNat *
      (solcSlotWord σ I ⟨6⟩).toNat) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd3813 := evm_run rd with [push0, push0]
  obtain ⟨_, _, rd3814⟩ := rd3813.sload (by native_decide) (by evm_ov)
  have rd3816 := evm_run rd3814 with [push1 ⟨6⟩]
  obtain ⟨_, _, rd3817⟩ := rd3816.sload (by native_decide) (by evm_ov)
  have rd5458 := evm_run rd3817 with [
    dup6, push2 ⟨3827⟩, swap2, swap1, push2 ⟨5458⟩,
    jump (by jump_dest)]
  exact RD.amm4CheckedMulOverflowWide
    (a := amm4BurnLiquidityWord I) (b := solcSlotWord σ I ⟨6⟩)
    (ret := ⟨3827⟩)
    (R := [solcSlotWord σ I ⟨0⟩, ⟨0⟩, q0,
      amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel])
    rd5458 hover (by decide) (by evm_ov)

theorem amm4BurnX_amount1Ok {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel q0 : UInt256} {k C : Nat}
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3827⟩
      [UInt256.mul (amm4BurnLiquidityWord I) (solcSlotWord σ I ⟨6⟩),
        solcSlotWord σ I ⟨0⟩, ⟨0⟩, q0,
        amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnonzero : solcSlotWord σ I ⟨0⟩ ≠ ⟨0⟩) :
    ∃ k' C', RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3840⟩
      [UInt256.div
        (UInt256.mul (amm4BurnLiquidityWord I) (solcSlotWord σ I ⟨6⟩))
        (solcSlotWord σ I ⟨0⟩),
        q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd5568 := evm_run rd with [
    jumpdest, push2 ⟨3837⟩, swap2, swap1,
    push2 ⟨5568⟩, jump (by jump_dest)]
  obtain ⟨_, _, rd3837⟩ := RD.amm4CheckedDivOk rd5568 hnonzero
    (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd3837 with [jumpdest, swap1, pop]⟩

theorem amm4BurnX_supplyUnderflow {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {k C : Nat}
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3840⟩
      [q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hunder : (solcSlotWord σ I ⟨0⟩).toNat <
      (amm4BurnLiquidityWord I).toNat) :
    RDrev amm4Bytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd3844 := evm_run rd with [dup4, push0, push0, dup3, dup3]
  obtain ⟨_, _, rd3845⟩ := rd3844.sload (by native_decide) (by evm_ov)
  have rd5253 := evm_run rd3845 with [
    push2 ⟨3855⟩, swap2, swap1, push2 ⟨5253⟩,
    jump (by jump_dest)]
  exact RD.amm4CheckedSubUnderflowWide rd5253 hunder
    (by decide) (by evm_ov)

theorem amm4BurnX_supplyStored {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {k C : Nat}
    (rd : RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3840⟩
      [q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hle : (amm4BurnLiquidityWord I).toNat ≤
      (solcSlotWord σ I ⟨0⟩).toNat)
    (hperm : I.perm = true) :
    ∃ k' C', RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3863⟩
      [q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩
        (UInt256.sub (solcSlotWord σ I ⟨0⟩) (amm4BurnLiquidityWord I)))
      k' C' := by
  have rd3844 := evm_run rd with [dup4, push0, push0, dup3, dup3]
  obtain ⟨_, _, rd3845⟩ := rd3844.sload (by native_decide) (by evm_ov)
  have rd5253 := evm_run rd3845 with [
    push2 ⟨3855⟩, swap2, swap1, push2 ⟨5253⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd3855⟩ := RD.amm4CheckedSubOk rd5253 hle
    (by jump_dest) (by evm_ov)
  have rd3860 := evm_run rd3855 with [
    jumpdest, swap3, pop, pop, dup2, swap1]
  obtain ⟨_, _, rd3861⟩ := rd3860.sstore hperm
    (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd3861 with [pop]⟩

theorem amm4BurnX_senderLoad {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3863⟩
      [q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3929⟩
      [solcSlotWord σ I (amm4TransferSenderSlot I),
        amm4BurnLiquidityWord I, ⟨0⟩, amm4TransferSenderSlot I,
        amm4BurnLiquidityWord I, q1, q0, amm4BurnToWord I,
        amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hsourceClean : UInt256.land solcAddrMask (solcSourceWord I) =
      solcSourceWord I := solcAddrMask_clean_left (solcSourceWord_canonical I)
  have rd3912₀ := evm_run rd with [
    dup4, push1 ⟨1⟩, push0, caller,
    push20 solcAddrMask, and, push20 solcAddrMask, and]
  have rd3912 := rd3912₀
  rw [hsourceClean, hsourceClean] at rd3912
  obtain ⟨_, _, rd3925⟩ := RD.amm4MappingHashSuffix rd3912
    amm4_mapping_hash_wf (by rfl) (by rfl)
    (by simpa [amm4TransferSenderSlot_eq_solc I] using
      (twoWordHashMem_solcMappingSlot ⟨1⟩ (solcSourceWord I)
        solcFreePtrMem_size))
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd3928 := evm_run rd3925 with [push0, dup3, dup3]
  obtain ⟨_, _, rd3929⟩ := rd3928.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, rd3929⟩

theorem amm4BurnX_senderUnderflow {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3929⟩
      [solcSlotWord σ I (amm4TransferSenderSlot I),
        amm4BurnLiquidityWord I, ⟨0⟩, amm4TransferSenderSlot I,
        amm4BurnLiquidityWord I, q1, q0, amm4BurnToWord I,
        amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hunder : (solcSlotWord σ I (amm4TransferSenderSlot I)).toNat <
      (amm4BurnLiquidityWord I).toNat) :
    RDrev amm4Bytecode g (initState cAstart gh bl σstart σ₀ g A I) := by
  have rd5253 := evm_run rd with [
    push2 ⟨3938⟩, swap2, swap1, push2 ⟨5253⟩,
    jump (by jump_dest)]
  exact RD.amm4CheckedSubUnderflowWide rd5253 hunder
    (by decide) (by evm_ov)

theorem amm4BurnX_senderStored {cAstart cA gh bl σstart σ σ₀ A I}
    {g : Sat256} {sel q0 q1 : UInt256} {k C : Nat}
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3929⟩
      [solcSlotWord σ I (amm4TransferSenderSlot I),
        amm4BurnLiquidityWord I, ⟨0⟩, amm4TransferSenderSlot I,
        amm4BurnLiquidityWord I, q1, q0, amm4BurnToWord I,
        amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hle : (amm4BurnLiquidityWord I).toNat ≤
      (solcSlotWord σ I (amm4TransferSenderSlot I)).toNat)
    (hperm : I.perm = true) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3946⟩
      [q1, q0, amm4BurnToWord I, amm4BurnLiquidityWord I, ⟨521⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (amm4TransferSenderSlot I)
        (UInt256.sub (solcSlotWord σ I (amm4TransferSenderSlot I))
          (amm4BurnLiquidityWord I))) k' C' := by
  have rd5253 := evm_run rd with [
    push2 ⟨3938⟩, swap2, swap1, push2 ⟨5253⟩,
    jump (by jump_dest)]
  obtain ⟨_, _, rd3938⟩ := RD.amm4CheckedSubOk rd5253 hle
    (by jump_dest) (by evm_ov)
  have rd3943 := evm_run rd3938 with [
    jumpdest, swap3, pop, pop, dup2, swap1]
  obtain ⟨_, _, rd3944⟩ := rd3943.sstore hperm
    (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd3944 with [pop]⟩

end Benchmarks.ActAmm4
