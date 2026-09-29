import Benchmarks.ActAmm4.SwapTransfer0Decode
import Benchmarks.ActAmm4.SwapTransfer1Call
import Benchmarks.ActAmm4.SwapTransfer1Decode
import Benchmarks.ActAmm4.SwapBalance0Call
import Benchmarks.ActAmm4.SwapBalance0Decode
import Benchmarks.ActAmm4.SwapBalance1Call
import Benchmarks.ActAmm4.SwapBalance1Decode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.ActAmm4

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

theorem amm4SwapX_transfer1FrameAfterFirst
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel : UInt256} {o0 : ByteArray}
    {cA1 : Batteries.RBSet AccountAddress compare}
    {σE1 : AccountMap} {k C : Nat}
    (hlo : 32 ≤ o0.size) (hbound : o0.size < 2 ^ 138)
    (hcanonTo : (amm4SwapToWord I).toNat < EVM.addressModulus)
    (hcanonBool : UInt256.ofNat
        (fromByteArrayBigEndian (o0.extract 0 32)) = ⟨0⟩ ∨
      UInt256.ofNat
        (fromByteArrayBigEndian (o0.extract 0 32)) = ⟨1⟩)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2607⟩
      [⟨1⟩, ⟨196⟩, ⟨3077966991⟩,
        amm4MintToken0Word σstart I, amm4SwapToWord I,
        amm4SwapAmount1Word I, amm4SwapAmount0Word I, ⟨349⟩, sel]
      (amm4SwapTransfer0PostCallMem I o0) (UInt256.ofNat 7)
      o0 (cA1, σE1) k C) :
    ∃ gasWord k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2763⟩
      [gasWord, amm4MintToken1Word σE1 I, ⟨0⟩,
        amm4MintToken0FreePtr o0, ⟨68⟩,
        amm4MintToken0FreePtr o0, ⟨32⟩,
        amm4MintToken0FreePtr o0 + ⟨68⟩, ⟨3077966991⟩,
        amm4MintToken1Word σE1 I, amm4SwapToWord I,
        amm4SwapAmount1Word I, amm4SwapAmount0Word I,
        ⟨349⟩, sel]
      (amm4SwapTransfer1CalldataMem I
        (amm4SwapAmount0Word I) (amm4SwapAmount1Word I) o0)
      (amm4SwapTransfer1CalldataWords o0)
      o0 (cA1, σE1) k' C' := by
  obtain ⟨_, _, rd2626⟩ := amm4SwapX_transfer0CallSucceeded rd
  have hhi : o0.size < UInt256.size :=
    lt_trans hbound (by norm_num [UInt256.size])
  obtain ⟨_, _, rd6025⟩ := amm4SwapX_transfer0ToDecoder hhi rd2626
  obtain ⟨_, _, rd5983⟩ :=
    amm4SwapX_transfer0DecodeWord hlo hbound rd6025
  obtain ⟨_, _, rd2659⟩ :=
    amm4SwapX_transfer0DecodeOk hcanonBool rd5983
  obtain ⟨_, _, rd2715⟩ := amm4SwapX_transfer1Address rd2659
  obtain ⟨_, _, rd2737⟩ :=
    amm4SwapX_transfer1SelectorMem hlo hbound rd2715
  obtain ⟨_, _, rd2750⟩ :=
    amm4SwapX_transfer1TransferArgs hlo hbound hcanonTo rd2737
  exact amm4SwapX_transfer1CallFrame hlo hbound rd2750

theorem amm4SwapX_balance0FrameAfterSecond
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 : UInt256} {o0 o1 : ByteArray}
    {cA2 : Batteries.RBSet AccountAddress compare}
    {σE1 σE2 : AccountMap} {k C : Nat}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hcanonBool : UInt256.ofNat
        (fromByteArrayBigEndian (o1.extract 0 32)) = ⟨0⟩ ∨
      UInt256.ofNat
        (fromByteArrayBigEndian (o1.extract 0 32)) = ⟨1⟩)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2764⟩
      [⟨1⟩, amm4MintToken0FreePtr o0 + ⟨68⟩, ⟨3077966991⟩,
        amm4MintToken1Word σE1 I, amm4SwapToWord I, q1, q0,
        ⟨349⟩, sel]
      (amm4SwapTransfer1PostCallMem I q0 q1 o0 o1)
      (amm4SwapTransfer1CalldataWords o0)
      o1 (cA2, σE2) k C) :
    ∃ gasWord k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2918⟩
      [gasWord, amm4MintToken0Word σE2 I,
        amm4SwapBalance0FreePtr o0 o1,
        ⟨36⟩, amm4SwapBalance0FreePtr o0 o1, ⟨32⟩,
        amm4SwapBalance0FreePtr o0 o1 + ⟨36⟩,
        ⟨1889567281⟩, amm4MintToken0Word σE2 I,
        ⟨0⟩, amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      (amm4SwapBalance0CalldataMem I q0 q1 o0 o1)
      (amm4SwapBalance0CalldataWords o0 o1)
      o1 (cA2, σE2) k' C' := by
  obtain ⟨_, _, rd2783⟩ := amm4SwapX_transfer1CallSucceeded rd
  have hhi : o1.size < UInt256.size :=
    lt_trans hbound1 (by norm_num [UInt256.size])
  obtain ⟨_, _, rd6025⟩ := amm4SwapX_transfer1ToDecoder
    hlo0 hbound0 hhi rd2783
  obtain ⟨_, _, rd5983⟩ := amm4SwapX_transfer1DecodeWord
    hlo0 hbound0 hlo1 hbound1 rd6025
  obtain ⟨_, _, rd2816⟩ :=
    amm4SwapX_transfer1DecodeOk hcanonBool rd5983
  obtain ⟨_, _, rd2873⟩ := amm4SwapX_balance0Address rd2816
  obtain ⟨_, _, rd2894⟩ :=
    amm4SwapX_balance0SelectorMem hlo0 hbound0 hbound1 rd2873
  obtain ⟨_, _, rd2906⟩ := amm4SwapX_balance0ArgMem rd2894
  exact amm4SwapX_balance0CallFrame hlo0 hbound0 hlo1 hbound1 rd2906

theorem amm4SwapX_balance1FrameAfterThird
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 : UInt256} {o0 o1 o2 : ByteArray}
    {cA3 : Batteries.RBSet AccountAddress compare}
    {σE2 σE3 : AccountMap} {k C : Nat}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hbound2 : o2.size < 2 ^ 138)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨2919⟩
      [⟨1⟩, amm4SwapBalance0FreePtr o0 o1 + ⟨36⟩,
        ⟨1889567281⟩, amm4MintToken0Word σE2 I,
        ⟨0⟩, amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      (amm4SwapBalance0PostCallMem I q0 q1 o0 o1 o2)
      (amm4SwapBalance0CalldataWords o0 o1)
      o2 (cA3, σE3) k C) :
    ∃ gasWord k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3074⟩
      [gasWord, amm4MintToken1Word σE3 I,
        amm4SwapBalance1FreePtr o0 o1 o2,
        ⟨36⟩, amm4SwapBalance1FreePtr o0 o1 o2, ⟨32⟩,
        amm4SwapBalance1FreePtr o0 o1 o2 + ⟨36⟩,
        ⟨1889567281⟩, amm4MintToken1Word σE3 I,
        ⟨0⟩, UInt256.ofNat (fromByteArrayBigEndian (o2.extract 0 32)),
        amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      (amm4SwapBalance1CalldataMem I q0 q1 o0 o1 o2)
      (amm4SwapBalance1CalldataWords o0 o1 o2)
      o2 (cA3, σE3) k' C' := by
  obtain ⟨_, _, rd2938⟩ := amm4SwapX_balance0CallSucceeded rd
  have hhi : o2.size < UInt256.size :=
    lt_trans hbound2 (by norm_num [UInt256.size])
  obtain ⟨_, _, rd5415⟩ := amm4SwapX_balance0ToDecoder
    hlo0 hbound0 hlo1 hbound1 hhi rd2938
  obtain ⟨_, _, rd2969⟩ := amm4SwapX_balance0DecodeOk
    hlo0 hbound0 hlo1 hbound1 hlo2 hbound2 rd5415
  obtain ⟨_, _, rd2972⟩ := amm4SwapX_balance0Continue rd2969
  obtain ⟨_, _, rd3029⟩ := amm4SwapX_balance1Address rd2972
  obtain ⟨_, _, rd3050⟩ := amm4SwapX_balance1SelectorMem
    hlo0 hbound0 hlo1 hbound1 hbound2 rd3029
  obtain ⟨_, _, rd3062⟩ := amm4SwapX_balance1ArgMem rd3050
  exact amm4SwapX_balance1CallFrame
    hlo0 hbound0 hlo1 hbound1 hlo2 hbound2 rd3062

theorem amm4SwapX_arithmeticAfterFourth
    {cAstart gh bl σstart σ₀ A I} {g : Sat256}
    {sel q0 q1 : UInt256} {o0 o1 o2 o3 : ByteArray}
    {cA4 : Batteries.RBSet AccountAddress compare}
    {σE3 σE4 : AccountMap} {k C : Nat}
    (hlo0 : 32 ≤ o0.size) (hbound0 : o0.size < 2 ^ 138)
    (hlo1 : 32 ≤ o1.size) (hbound1 : o1.size < 2 ^ 138)
    (hlo2 : 32 ≤ o2.size) (hbound2 : o2.size < 2 ^ 138)
    (hlo3 : 32 ≤ o3.size) (hbound3 : o3.size < 2 ^ 138)
    (rd : RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3075⟩
      [⟨1⟩, amm4SwapBalance1FreePtr o0 o1 o2 + ⟨36⟩,
        ⟨1889567281⟩, amm4MintToken1Word σE3 I,
        ⟨0⟩, UInt256.ofNat (fromByteArrayBigEndian (o2.extract 0 32)),
        amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      (amm4SwapBalance1PostCallMem I q0 q1 o0 o1 o2 o3)
      (amm4SwapBalance1CalldataWords o0 o1 o2)
      o3 (cA4, σE4) k C) :
    ∃ k' C', RD amm4Bytecode I g
      (initState cAstart gh bl σstart σ₀ g A I) ⟨3128⟩
      [UInt256.ofNat (fromByteArrayBigEndian (o3.extract 0 32)),
        UInt256.ofNat (fromByteArrayBigEndian (o2.extract 0 32)),
        amm4SwapToWord I, q1, q0, ⟨349⟩, sel]
      (amm4SwapBalance1DecodeMem I q0 q1 o0 o1 o2 o3)
      (amm4SwapBalance1CalldataWords o0 o1 o2)
      o3 (cA4, σE4) k' C' := by
  obtain ⟨_, _, rd3094⟩ := amm4SwapX_balance1CallSucceeded rd
  have hhi : o3.size < UInt256.size :=
    lt_trans hbound3 (by norm_num [UInt256.size])
  obtain ⟨_, _, rd5415⟩ := amm4SwapX_balance1ToDecoder
    hlo0 hbound0 hlo1 hbound1 hlo2 hbound2 hhi rd3094
  obtain ⟨_, _, rd3125⟩ := amm4SwapX_balance1DecodeOk
    hlo0 hbound0 hlo1 hbound1 hlo2 hbound2 hlo3 hbound3 rd5415
  exact amm4SwapX_balance1Continue rd3125

end Benchmarks.ActAmm4
