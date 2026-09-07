import Examples.NestedCaller.Sample
import Examples.NestedCaller.CallTraces
import Reasoning.ABI

namespace NestedCaller
open Solm Ethereum Ethereum.EVM Reasoning.Reach Reasoning.Theory Reasoning.Refinement
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- The fixed probe ABI makes the existing gas-derived returndata theorem available
without inspecting any call attempt outcomes. -/
theorem probeReturn_bound {e e' target z out perm i}
    (hcall : typedCallViaEVM nestedCallerConfig e target "probe" 0 [wordValue i] (z, e', out) perm) :
    out.size < 2 ^ 138 := by
  apply typedCallViaEVM_returnData_size_lt_2pow138 hcall
  intro cd hencode
  change some (probeSelector ++ (EVM.wordOfInt (Int.ofNat i.toNat)).toByteArray) = some cd at hencode
  rw [wordOfInt_ofNat_toNat] at hencode
  rw [← Option.some.inj hencode, ByteArray.size_append, toByteArray_size]
  change 4 + 32 ≤ maxReturnDataSizeByGas
  norm_num [maxReturnDataSizeByGas, maxReturnDataWordsByGas]

/-- The actual external-call path of `sample`: GAS, paired CALL, ABI rejection or
return to the internal continuation. Callee code and account changes are arbitrary. -/
theorem probeRefines {ee g s0 targetWord i saved n} {target : AccountAddress}
    (hn : n ≤ 16) (hlen : saved.length + 24 ≤ 1024)
    (hperm : ee.perm = true)
    (hmask : UInt256.land ⟨1461501637330902918203684832716283019655932542975⟩ targetWord = targetWord)
    (htarget : EVM.address target = AccountAddress.ofUInt256 targetWord) :
    StmtsRefine nestedCallerBytecode ee g s0 nestedCallerConfig ⟨215⟩
      (ProbeEntry (MemoryAt n) s0 ee target targetWord i saved) (sampleFunction.body.drop 2)
      (internalCallExit (SampleReturn (MemoryAt (n + 1)) s0 ee saved)) := by
  intro cur k C f e hpc rd hp
  rcases hp with ⟨gas, hs, hc, ht, hi, hg, hm, hw⟩
  rcases hm with ⟨fp, hfplo, hfphi, hsize, hread, hawlo, hawhi⟩
  rw [hpc, hs] at rd
  obtain ⟨k1, C1, rgas⟩ := reachCallGas hn hfplo hfphi hsize hread hawlo hawhi hmask hlen rd
  let pre : Cursor := { pc := ⟨284⟩, stack := [targetWord, ⟨0⟩, UInt256.ofNat fp, ⟨36⟩, UInt256.ofNat fp, ⟨32⟩] ++ callRest fp targetWord gas i saved, mem := argumentMem cur.mem fp i, aw := inputWords cur.aw fp, rdata := cur.rdata, world := cur.world }
  have hb := allocationBound_small (n := n) (by omega)
  have hfps : fp < 2 ^ 144 := by omega
  have hfpu : fp < UInt256.size := by norm_num [UInt256.size] at *; omega
  have haw := inputWords_bounds hn hawhi hfphi
  have hawsmall := lt_of_le_of_lt haw.2.2 (allocationBound_small (by omega))
  have hawcall := callActiveWords_eq (inputWords cur.aw fp) (UInt256.ofNat fp) ⟨36⟩ (UInt256.ofNat fp) ⟨32⟩
    (Or.inr (by rw [ulit_toNat' fp hfpu]; exact haw.2.1))
    (Or.inr (by rw [ulit_toNat' fp hfpu]; change fp + 32 ≤ _; omega))
  refine BlockRefinesFrom.gas (cur := pre) (P := fun c _ e => CallStateRel s0 ee c.world e)
    (by change decode nestedCallerBytecode ⟨284⟩ = _; decide)
    (by simp [pre, callRest]; omega) ?_ rgas hw
  intro callGas
  refine BlockRefinesFrom.externalCall (value := 0) (tgt := target)
    (argVals := [wordValue i]) (fun _ => rfl) (fun h => h)
    (fun _ => by simp only [evalExpr?, ht, EvalResult.ofOption])
    (fun _ => by simp only [evalExpr?]; rfl)
    (fun _ => by simp only [evalExprs?, evalExpr?, hi, EvalResult.ofOption, bind, EvalResult.bind, pure])
    (fun _ => by decide) (fun _ => htarget)
    (fun _ => by
      change some (probeSelector ++ (EVM.wordOfInt (Int.ofNat i.toNat)).toByteArray) = _
      rw [wordOfInt_ofNat_toNat]
      change _ = some ((argumentMem cur.mem fp i).readWithPadding (UInt256.ofNat fp).toNat 36)
      rw [ulit_toNat' fp hfpu, argumentMem_encode])
    (by change decode nestedCallerBytecode ⟨285⟩ = _; decide) hperm
    (by simp [callRest]; omega) trivial ?_ ?_
  · intro out e' world' k' C'
    dsimp only [callCursor]
    intro hcall hout
    have ho := probeReturn_bound hcall
    have hofacts := copiedMem_facts (mem := cur.mem) (i := i) hfps ho
    have hocopySize : fp + 36 ≤ (copiedMem cur.mem fp i out).size := by
      rw [hofacts.1]; exact argumentMem_size cur.mem fp i
    have hocopy64 : (copiedMem cur.mem fp i out).readWithPadding 64 32 = (UInt256.ofNat fp).toByteArray := by
      rw [hofacts.2.1 64 (by omega), argumentMem_read64 i hfplo hsize]; exact hread
    rw [show nestedCallerConfig.externalABI.decode? "probe" out = ABI.decodeReturnValues? [abiUInt256] out from rfl,
      decodeReturnValues_uint256_eq]
    have hos : out.size < 2 ^ 255 := by norm_num at *; omega
    by_cases hword : 32 ≤ out.size
    · rw [if_pos ⟨hword, hos⟩]
      intro rd' hr'
      dsimp only [gasCursor, pre] at rd'
      rw [hawcall, ulit_toNat' fp hfpu] at rd'
      change RD nestedCallerBytecode ee g s0 ⟨286⟩ (⟨1⟩ :: callRest fp targetWord gas i saved)
        (copiedMem cur.mem fp i out) (inputWords cur.aw fp) out world' k' C' at rd'
      obtain ⟨k2, C2, rdec⟩ := successToDecoder (by simp; omega) (by omega) hocopy64
        (by omega) hawsmall rd'
      have hm' := decodedMem_facts hn hfplo hfphi hawlo hawhi ho hword (mem := cur.mem) (i := i)
      let w := UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))
      have hl : memLoad (UInt256.ofNat fp) (inputWords cur.aw fp) (decodedMem cur.mem fp i out) = w := by
        unfold memLoad
        rw [if_neg (not_or.mpr ⟨?_, ?_⟩), ulit_toNat' fp hfpu, hm'.2.1]
        · rw [ulit_toNat' fp hfpu]; omega
        · change ¬ (UInt256.ofNat fp).toNat ≥ (inputWords cur.aw fp * ⟨32⟩).toNat
          rw [ulit_toNat' fp hfpu, umul_toNat _ _ (by
            change (inputWords cur.aw fp).toNat * 32 < UInt256.size
            norm_num [UInt256.size] at *; omega)]
          change ¬ fp ≥ (inputWords cur.aw fp).toNat * 32
          omega
      obtain ⟨k3, C3, rr⟩ := decodedReturn hlen hfpu hword ho hl (by omega) rdec
      have hwval : wordValue w = .int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32))) := by
        simp only [wordValue, w, ulit_toNat' _ (fromByteArrayBigEndian_extract0_32_lt hword)]
      refine BlockProgress.ofRD
        (cur := { pc := ⟨135⟩, stack := w :: saved, mem := decodedMem cur.mem fp i out, aw := inputWords cur.aw fp, rdata := out, world := world' })
        (ExecBlock.consReturn (ExecStmt.return (values := [.int (Int.ofNat (fromByteArrayBigEndian (out.extract 0 32)))]) ?_)) rr ⟨w, ?_, rfl, rfl, hm'.1, hr'⟩
      · simp only [evalExprs?, evalExpr?, store_get_self, collapseReturns, EvalResult.ofOption,
          bind, EvalResult.bind, pure]
      · rw [hwval]
    · rw [if_neg (by rintro ⟨h, _⟩; exact hword h)]
      intro rd'
      dsimp only [gasCursor, pre] at rd'
      rw [hawcall, ulit_toNat' fp hfpu] at rd'
      change RD nestedCallerBytecode ee g s0 ⟨286⟩ (⟨1⟩ :: callRest fp targetWord gas i saved)
        (copiedMem cur.mem fp i out) (inputWords cur.aw fp) out world' k' C' at rd'
      obtain ⟨k2, C2, rdec⟩ := successToDecoder (by simp; omega) (by omega) hocopy64
        (by omega) hawsmall rd'
      exact shortReturn (by simp; omega) hfpu (by omega) rdec
  · intro out world' k' C'
    dsimp only [callCursor]
    intro rd'
    dsimp only [gasCursor, pre] at rd'
    rw [hawcall, ulit_toNat' fp hfpu] at rd'
    exact callFailure (by simp [callRest]; omega) rd'

end NestedCaller
