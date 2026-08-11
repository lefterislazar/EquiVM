import Examples.Precompiles.Modexp.MultiLimbClzStage1

/-! # Incrementally checked prefixes of the deployed leading-zero helper -/
open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Modexp.MultiLimbClz
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem stage128_n_le (x : UInt256) : (stage128 x).n ≤ 128 := by
  unfold stage128
  split <;> simp_all

theorem stage64_n_le {x : UInt256} {n : Nat} (hn : n ≤ 128) :
    (stage64 x n).n ≤ 192 := by
  unfold stage64
  split <;> simp_all <;> omega

theorem stage32_n_le {x : UInt256} {n : Nat} (hn : n ≤ 192) :
    (stage32 x n).n ≤ 224 := by
  unfold stage32
  split <;> simp_all <;> omega

theorem stage16_n_le {x : UInt256} {n : Nat} (hn : n ≤ 224) :
    (stage16 x n).n ≤ 240 := by
  unfold stage16
  split <;> simp_all <;> omega

theorem stage8_n_le {x : UInt256} {n : Nat} (hn : n ≤ 240) :
    (stage8 x n).n ≤ 248 := by
  unfold stage8
  split <;> simp_all <;> omega

theorem stage4_n_le {x : UInt256} {n : Nat} (hn : n ≤ 248) :
    (stage4 x n).n ≤ 252 := by
  unfold stage4
  split <;> simp_all <;> omega

theorem stage2_n_le {x : UInt256} {n : Nat} (hn : n ≤ 252) :
    (stage2 x n).n ≤ 254 := by
  unfold stage2
  split <;> simp_all <;> omega

theorem stage1_n_le {x : UInt256} {n : Nat} (hn : n ≤ 254) :
    (stage1 x n).n ≤ 255 := by
  unfold stage1
  split <;> simp_all <;> omega

theorem through64_n_le (x : UInt256) : (through64 x).n ≤ 192 := by
  let first := stage128 x
  have hfirst : first.n ≤ 128 := stage128_n_le x
  have hsecond := stage64_n_le (x := first.x) hfirst
  simpa only [through64, first] using hsecond

def through32 (x : UInt256) : StageResult :=
  let first := through64 x
  let next := stage32 first.x first.n
  { next with steps := first.steps + next.steps, gas := first.gas + next.gas }

theorem through32_n_le (x : UInt256) : (through32 x).n ≤ 224 := by
  have h := stage32_n_le (x := (through64 x).x) (through64_n_le x)
  simpa only [through32] using h

theorem through32Exact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256} {x ret : UInt256}
    (hdepth : tail.length ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨8042⟩ (x :: ret :: tail) mem aw rdata acc k C) :
    let result := through32 x
    RDx runtimeBytecode ee g s0 ⟨8174⟩
      (result.x :: UInt256.ofNat (2 ^ 255) :: ret :: UInt256.ofNat result.n :: tail)
      mem aw rdata acc (k + result.steps) (C + result.gas) := by
  let first := through64 x
  let next := stage32 first.x first.n
  have rd8137 := through64Exact (by omega) h
  have hnWord : first.n + 32 < UInt256.size := by
    have hfirst : first.n ≤ 192 := by
      simpa only [first] using through64_n_le x
    simp only [UInt256.size]
    omega
  have rd8174 := stage32Exact hnWord hdepth rd8137
  simpa only [through32, first, next, Nat.add_assoc] using rd8174

def through16 (x : UInt256) : StageResult :=
  let first := through32 x
  let next := stage16 first.x first.n
  { next with steps := first.steps + next.steps, gas := first.gas + next.gas }

theorem through16_n_le (x : UInt256) : (through16 x).n ≤ 240 := by
  have h := stage16_n_le (x := (through32 x).x) (through32_n_le x)
  simpa only [through16] using h

theorem through16Exact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256} {x ret : UInt256}
    (hdepth : tail.length ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨8042⟩ (x :: ret :: tail) mem aw rdata acc k C) :
    let result := through16 x
    RDx runtimeBytecode ee g s0 ⟨8213⟩
      (result.x :: UInt256.ofNat (2 ^ 255) :: ret :: UInt256.ofNat result.n :: tail)
      mem aw rdata acc (k + result.steps) (C + result.gas) := by
  let first := through32 x
  let next := stage16 first.x first.n
  have rd8174 := through32Exact hdepth h
  have hnWord : first.n + 16 < UInt256.size := by
    have hfirst : first.n ≤ 224 := by
      simpa only [first] using through32_n_le x
    simp only [UInt256.size]
    omega
  have rd8213 := stage16Exact hnWord hdepth rd8174
  simpa only [through16, first, next, Nat.add_assoc] using rd8213

def through8 (x : UInt256) : StageResult :=
  let first := through16 x
  let next := stage8 first.x first.n
  { next with steps := first.steps + next.steps, gas := first.gas + next.gas }

theorem through8_n_le (x : UInt256) : (through8 x).n ≤ 248 := by
  have h := stage8_n_le (x := (through16 x).x) (through16_n_le x)
  simpa only [through8] using h

theorem through8Exact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256} {x ret : UInt256}
    (hdepth : tail.length ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨8042⟩ (x :: ret :: tail) mem aw rdata acc k C) :
    let result := through8 x
    RDx runtimeBytecode ee g s0 ⟨8253⟩
      (result.x :: UInt256.ofNat (2 ^ 255) :: ret :: UInt256.ofNat result.n :: tail)
      mem aw rdata acc (k + result.steps) (C + result.gas) := by
  let first := through16 x
  let next := stage8 first.x first.n
  have rd8213 := through16Exact hdepth h
  have hnWord : first.n + 8 < UInt256.size := by
    have hfirst : first.n ≤ 240 := by
      simpa only [first] using through16_n_le x
    simp only [UInt256.size]
    omega
  have rd8253 := stage8Exact hnWord hdepth rd8213
  simpa only [through8, first, next, Nat.add_assoc] using rd8253

def through4 (x : UInt256) : StageResult :=
  let first := through8 x
  let next := stage4 first.x first.n
  { next with steps := first.steps + next.steps, gas := first.gas + next.gas }

theorem through4_n_le (x : UInt256) : (through4 x).n ≤ 252 := by
  have h := stage4_n_le (x := (through8 x).x) (through8_n_le x)
  simpa only [through4] using h

theorem through4Exact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256} {x ret : UInt256}
    (hdepth : tail.length ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨8042⟩ (x :: ret :: tail) mem aw rdata acc k C) :
    let result := through4 x
    RDx runtimeBytecode ee g s0 ⟨8293⟩
      (result.x :: UInt256.ofNat (2 ^ 255) :: ret :: UInt256.ofNat result.n :: tail)
      mem aw rdata acc (k + result.steps) (C + result.gas) := by
  let first := through8 x
  let next := stage4 first.x first.n
  have rd8253 := through8Exact hdepth h
  have hnWord : first.n + 4 < UInt256.size := by
    have hfirst : first.n ≤ 248 := by
      simpa only [first] using through8_n_le x
    simp only [UInt256.size]
    omega
  have rd8293 := stage4Exact hnWord hdepth rd8253
  simpa only [through4, first, next, Nat.add_assoc] using rd8293

def through2 (x : UInt256) : StageResult :=
  let first := through4 x
  let next := stage2 first.x first.n
  { next with steps := first.steps + next.steps, gas := first.gas + next.gas }

theorem through2_n_le (x : UInt256) : (through2 x).n ≤ 254 := by
  have h := stage2_n_le (x := (through4 x).x) (through4_n_le x)
  simpa only [through2] using h

theorem through2Exact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256} {x ret : UInt256}
    (hdepth : tail.length ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨8042⟩ (x :: ret :: tail) mem aw rdata acc k C) :
    let result := through2 x
    RDx runtimeBytecode ee g s0 ⟨8333⟩
      (result.x :: UInt256.ofNat (2 ^ 255) :: ret :: UInt256.ofNat result.n :: tail)
      mem aw rdata acc (k + result.steps) (C + result.gas) := by
  let first := through4 x
  let next := stage2 first.x first.n
  have rd8293 := through4Exact hdepth h
  have hnWord : first.n + 2 < UInt256.size := by
    have hfirst : first.n ≤ 252 := by
      simpa only [first] using through4_n_le x
    simp only [UInt256.size]
    omega
  have rd8333 := stage2Exact hnWord hdepth rd8293
  simpa only [through2, first, next, Nat.add_assoc] using rd8333

def through1 (x : UInt256) : StageResult :=
  let first := through2 x
  let next := stage1 first.x first.n
  { next with steps := first.steps + next.steps, gas := first.gas + next.gas }

theorem through1_n_le (x : UInt256) : (through1 x).n ≤ 255 := by
  have h := stage1_n_le (x := (through2 x).x) (through2_n_le x)
  simpa only [through1] using h

theorem through1Exact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256} {x ret : UInt256}
    (hret : (D_J runtimeBytecode 0).contains ret = true)
    (hdepth : tail.length ≤ 1016)
    (h : RDx runtimeBytecode ee g s0 ⟨8042⟩ (x :: ret :: tail) mem aw rdata acc k C) :
    let result := through1 x
    RDx runtimeBytecode ee g s0 ret (UInt256.ofNat result.n :: tail)
      mem aw rdata acc (k + result.steps) (C + result.gas) := by
  let first := through2 x
  let next := stage1 first.x first.n
  have rd8333 := through2Exact hdepth h
  have hnWord : first.n + 1 < UInt256.size := by
    have hfirst : first.n ≤ 254 := by
      simpa only [first] using through2_n_le x
    simp only [UInt256.size]
    omega
  have rdret := stage1Exact hnWord hret (by omega) rd8333
  simpa only [through1, first, next, Nat.add_assoc] using rdret

end Modexp.MultiLimbClz
