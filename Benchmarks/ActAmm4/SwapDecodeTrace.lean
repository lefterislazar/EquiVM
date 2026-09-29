import Benchmarks.ActAmm4.SwapBase
import Benchmarks.ActAmm4.Routines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨323⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5004⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨344⟩, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := hreach
  have rd' := evm_run rd with [
    jumpdest, push2 ⟨349⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
    push2 ⟨344⟩, swap2, swap1, push2 ⟨5004⟩, jump (by jump_dest)]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz4) hsize] at rd'
  exact ⟨_, _, rd'⟩

theorem amm4SwapX_dec4708_amount0 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨323⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4708⟩
      [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨5040⟩,
        ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨344⟩, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ := by
    simpa using (solcCalldataStaticLenCheckOk (words := 3)
      (sz := I.calldata.size) (by omega) hszhi hsize)
  obtain ⟨_, _, rd⟩ := amm4SwapX_toDecoder (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) (by omega) hsize hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, push0, push0, push1 ⟨96⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨5027⟩, jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, push2 ⟨5040⟩, dup7, dup3, dup8, add, push2 ⟨4708⟩,
    jump (by jump_dest)]⟩

theorem amm4SwapX_dec5040 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨323⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5040⟩
      [amm4SwapAmount0Word I, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨344⟩, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4SwapX_dec4708_amount0 (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hreach
  exact RD.amm4DecodeUint256Ok rd (by jump_dest) (by evm_ov)

theorem amm4SwapX_dec4708_amount1 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨323⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4708⟩
      [⟨4⟩ + ⟨32⟩, UInt256.ofNat I.calldata.size, ⟨5057⟩, ⟨32⟩,
        ⟨0⟩, ⟨0⟩, amm4SwapAmount0Word I, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨344⟩, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4SwapX_dec5040 (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap4, pop, pop, push1 ⟨32⟩, push2 ⟨5057⟩,
    dup7, dup3, dup8, add, push2 ⟨4708⟩, jump (by jump_dest)]⟩

theorem amm4SwapX_dec5057 {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨323⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5057⟩
      [amm4SwapAmount1Word I, ⟨32⟩, ⟨0⟩, ⟨0⟩,
        amm4SwapAmount0Word I, ⟨4⟩, UInt256.ofNat I.calldata.size,
        ⟨344⟩, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4SwapX_dec4708_amount1 (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hreach
  exact RD.amm4DecodeUint256Ok rd (by jump_dest) (by evm_ov)

theorem amm4SwapX_dec4657_to {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨323⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4657⟩
      [⟨4⟩ + ⟨64⟩, UInt256.ofNat I.calldata.size, ⟨5074⟩, ⟨64⟩,
        ⟨0⟩, amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨344⟩, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4SwapX_dec5057 (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hreach
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, pop, pop, push1 ⟨64⟩, push2 ⟨5074⟩,
    dup7, dup3, dup8, add, push2 ⟨4657⟩, jump (by jump_dest)]⟩

theorem amm4SwapX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonTo : (amm4SwapToWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨323⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD amm4Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2111⟩
      [amm4SwapToWord I, amm4SwapAmount1Word I,
        amm4SwapAmount0Word I, ⟨349⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd⟩ := amm4SwapX_dec4657_to (cA := cA)
    (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel)
    hsz100 hsize hszhi hreach
  obtain ⟨_, _, rd5074⟩ := RD.amm4DecodeAddrOk rd hcanonTo
    (by jump_dest) (by evm_ov)
  exact ⟨_, _, evm_run rd5074 with [
    jumpdest, swap2, pop, pop, swap3, pop, swap3, pop, swap3,
    jump (by jump_dest), jumpdest, push2 ⟨2111⟩, jump (by jump_dest)]⟩

end Benchmarks.ActAmm4
