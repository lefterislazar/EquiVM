import Benchmarks.Dss.End.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.End

def endSlotWord (σ : AccountMap) (I : ExecutionEnv) (slot : UInt256) : UInt256 :=
  solcSlotWord σ I slot

def endAddressSlotWord (σ : AccountMap) (I : ExecutionEnv) (slot : UInt256) : UInt256 :=
  UInt256.land (endSlotWord σ I slot) solcAddrMask

theorem endSlotWord_eq_of_accountMapEquiv (hAccounts : accountMapEquiv σ_evm σ_solm)
    (I : ExecutionEnv) (slot : UInt256) :
    endSlotWord σ_evm I slot = endSlotWord σ_solm I slot :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩

theorem endAddressSlotWord_eq_of_accountMapEquiv
    (hAccounts : accountMapEquiv σ_evm σ_solm) (I : ExecutionEnv) (slot : UInt256) :
    endAddressSlotWord σ_evm I slot = endAddressSlotWord σ_solm I slot := by
  simpa [endAddressSlotWord] using
    congrArg (fun w => UInt256.land w solcAddrMask)
      (endSlotWord_eq_of_accountMapEquiv hAccounts I slot)

@[simp] theorem endConfig_storage_vat :
    config.storage.layout { base := "vat", steps := [] } =
      fun _ => some (addrLoc ⟨1⟩) :=
  rfl

@[simp] theorem endConfig_storage_cat :
    config.storage.layout { base := "cat", steps := [] } =
      fun _ => some (addrLoc ⟨2⟩) :=
  rfl

@[simp] theorem endConfig_storage_dog :
    config.storage.layout { base := "dog", steps := [] } =
      fun _ => some (addrLoc ⟨3⟩) :=
  rfl

@[simp] theorem endConfig_storage_vow :
    config.storage.layout { base := "vow", steps := [] } =
      fun _ => some (addrLoc ⟨4⟩) :=
  rfl

@[simp] theorem endConfig_storage_pot :
    config.storage.layout { base := "pot", steps := [] } =
      fun _ => some (addrLoc ⟨5⟩) :=
  rfl

@[simp] theorem endConfig_storage_spot :
    config.storage.layout { base := "spot", steps := [] } =
      fun _ => some (addrLoc ⟨6⟩) :=
  rfl

@[simp] theorem endConfig_storage_cure :
    config.storage.layout { base := "cure", steps := [] } =
      fun _ => some (addrLoc ⟨7⟩) :=
  rfl

@[simp] theorem endConfig_storage_live :
    config.storage.layout { base := "live", steps := [] } =
      fun _ => some (wordLoc ⟨8⟩) :=
  rfl

@[simp] theorem endConfig_storage_when :
    config.storage.layout { base := "when", steps := [] } =
      fun _ => some (wordLoc ⟨9⟩) :=
  rfl

@[simp] theorem endConfig_storage_wait :
    config.storage.layout { base := "wait", steps := [] } =
      fun _ => some (wordLoc ⟨10⟩) :=
  rfl

theorem endVatBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "vat" = none) :
    ExecTransitionBody config contract evm locals vatTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
            solcAddrMask).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config { contract := contract, locals := locals } evm
          vatRef = .ok { base := "vat", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? contract.storage ({ base := "vat", steps := [] } : EvaledStorageRef)
          = some (.elem .address) := by decide
      rw [evalExpr_storage_scalar (t := .address) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := endConfig_storage_vat), endRuntimeStorageLocLoad_address_offset0])

theorem endCatBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "cat" = none) :
    ExecTransitionBody config contract evm locals catTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
            solcAddrMask).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config { contract := contract, locals := locals } evm
          catRef = .ok { base := "cat", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, catRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? contract.storage ({ base := "cat", steps := [] } : EvaledStorageRef)
          = some (.elem .address) := by decide
      rw [evalExpr_storage_scalar (t := .address) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := endConfig_storage_cat), endRuntimeStorageLocLoad_address_offset0])

theorem endDogBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "dog" = none) :
    ExecTransitionBody config contract evm locals dogTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
            solcAddrMask).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config { contract := contract, locals := locals } evm
          dogRef = .ok { base := "dog", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, dogRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? contract.storage ({ base := "dog", steps := [] } : EvaledStorageRef)
          = some (.elem .address) := by decide
      rw [evalExpr_storage_scalar (t := .address) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := endConfig_storage_dog), endRuntimeStorageLocLoad_address_offset0])

theorem endVowBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "vow" = none) :
    ExecTransitionBody config contract evm locals vowTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
            solcAddrMask).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config { contract := contract, locals := locals } evm
          vowRef = .ok { base := "vow", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, vowRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? contract.storage ({ base := "vow", steps := [] } : EvaledStorageRef)
          = some (.elem .address) := by decide
      rw [evalExpr_storage_scalar (t := .address) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := endConfig_storage_vow), endRuntimeStorageLocLoad_address_offset0])

theorem endPotBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "pot" = none) :
    ExecTransitionBody config contract evm locals potTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
            solcAddrMask).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config { contract := contract, locals := locals } evm
          potRef = .ok { base := "pot", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, potRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? contract.storage ({ base := "pot", steps := [] } : EvaledStorageRef)
          = some (.elem .address) := by decide
      rw [evalExpr_storage_scalar (t := .address) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := endConfig_storage_pot), endRuntimeStorageLocLoad_address_offset0])

theorem endSpotBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "spot" = none) :
    ExecTransitionBody config contract evm locals spotTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩)
            solcAddrMask).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config { contract := contract, locals := locals } evm
          spotRef = .ok { base := "spot", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, spotRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? contract.storage ({ base := "spot", steps := [] } : EvaledStorageRef)
          = some (.elem .address) := by decide
      rw [evalExpr_storage_scalar (t := .address) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := endConfig_storage_spot), endRuntimeStorageLocLoad_address_offset0])

theorem endCureBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "cure" = none) :
    ExecTransitionBody config contract evm locals cureTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩)
            solcAddrMask).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config { contract := contract, locals := locals } evm
          cureRef = .ok { base := "cure", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, cureRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? contract.storage ({ base := "cure", steps := [] } : EvaledStorageRef)
          = some (.elem .address) := by decide
      rw [evalExpr_storage_scalar (t := .address) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := endConfig_storage_cure), endRuntimeStorageLocLoad_address_offset0])

theorem endLiveBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "live" = none) :
    ExecTransitionBody config contract evm locals liveTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config { contract := contract, locals := locals } evm
          liveRef = .ok { base := "live", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? contract.storage ({ base := "live", steps := [] } : EvaledStorageRef)
          = some (.elem (.int uint256Int)) := by decide
      rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := endConfig_storage_live), endRuntimeStorageLocLoad_uint256])

theorem endWhenBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "when" = none) :
    ExecTransitionBody config contract evm locals whenTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨9⟩).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config { contract := contract, locals := locals } evm
          whenRef = .ok { base := "when", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, whenRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? contract.storage ({ base := "when", steps := [] } : EvaledStorageRef)
          = some (.elem (.int uint256Int)) := by decide
      rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := endConfig_storage_when), endRuntimeStorageLocLoad_uint256])

theorem endWaitBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "wait" = none) :
    ExecTransitionBody config contract evm locals waitTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨10⟩).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef config { contract := contract, locals := locals } evm
          waitRef = .ok { base := "wait", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, waitRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? contract.storage ({ base := "wait", steps := [] } : EvaledStorageRef)
          = some (.elem (.int uint256Int)) := by decide
      rw [evalExpr_storage_scalar (t := .int uint256Int) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := endConfig_storage_wait), endRuntimeStorageLocLoad_uint256])

theorem endX_vat {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨564⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (endAddressSlotWord σ I ⟨1⟩)) := by
  simpa [endAddressSlotWord, endSlotWord] using
    (RD.solcAddressGetterExternal (code := endBytecode) (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (sel := sel) (entry := ⟨564⟩) (routine := ⟨1634⟩) (slot := ⟨1⟩)
      (returnPc := ⟨572⟩)
      hreach
      (by dsimp [solcGetterEntryWf]; repeat' first | apply And.intro | native_decide)
      (by dsimp [solcAddressSlotGetterWf]; repeat' first | apply And.intro | native_decide)
      (by jump_dest) (by jump_dest)
      (by dsimp [solcReturnAddressFromMemWf]; repeat' first | apply And.intro | native_decide))

theorem endX_cat {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1208⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (endAddressSlotWord σ I ⟨2⟩)) := by
  simpa [endAddressSlotWord, endSlotWord] using
    (RD.solcAddressGetterExternal (code := endBytecode) (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (sel := sel) (entry := ⟨1208⟩) (routine := ⟨9558⟩) (slot := ⟨2⟩)
      (returnPc := ⟨572⟩)
      hreach
      (by dsimp [solcGetterEntryWf]; repeat' first | apply And.intro | native_decide)
      (by dsimp [solcAddressSlotGetterWf]; repeat' first | apply And.intro | native_decide)
      (by jump_dest) (by jump_dest)
      (by dsimp [solcReturnAddressFromMemWf]; repeat' first | apply And.intro | native_decide))

theorem endX_dog {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1017⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (endAddressSlotWord σ I ⟨3⟩)) := by
  simpa [endAddressSlotWord, endSlotWord] using
    (RD.solcAddressGetterExternal (code := endBytecode) (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (sel := sel) (entry := ⟨1017⟩) (routine := ⟨7675⟩) (slot := ⟨3⟩)
      (returnPc := ⟨572⟩)
      hreach
      (by dsimp [solcGetterEntryWf]; repeat' first | apply And.intro | native_decide)
      (by dsimp [solcAddressSlotGetterWf]; repeat' first | apply And.intro | native_decide)
      (by jump_dest) (by jump_dest)
      (by dsimp [solcReturnAddressFromMemWf]; repeat' first | apply And.intro | native_decide))

theorem endX_vow {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨715⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (endAddressSlotWord σ I ⟨4⟩)) := by
  simpa [endAddressSlotWord, endSlotWord] using
    (RD.solcAddressGetterExternal (code := endBytecode) (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (sel := sel) (entry := ⟨715⟩) (routine := ⟨5236⟩) (slot := ⟨4⟩)
      (returnPc := ⟨572⟩)
      hreach
      (by dsimp [solcGetterEntryWf]; repeat' first | apply And.intro | native_decide)
      (by dsimp [solcAddressSlotGetterWf]; repeat' first | apply And.intro | native_decide)
      (by jump_dest) (by jump_dest)
      (by dsimp [solcReturnAddressFromMemWf]; repeat' first | apply And.intro | native_decide))

theorem endX_pot {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨664⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (endAddressSlotWord σ I ⟨5⟩)) := by
  simpa [endAddressSlotWord, endSlotWord] using
    (RD.solcAddressGetterExternal (code := endBytecode) (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (sel := sel) (entry := ⟨664⟩) (routine := ⟨3209⟩) (slot := ⟨5⟩)
      (returnPc := ⟨572⟩)
      hreach
      (by dsimp [solcGetterEntryWf]; repeat' first | apply And.intro | native_decide)
      (by dsimp [solcAddressSlotGetterWf]; repeat' first | apply And.intro | native_decide)
      (by jump_dest) (by jump_dest)
      (by dsimp [solcReturnAddressFromMemWf]; repeat' first | apply And.intro | native_decide))

theorem endX_spot {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨835⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (endAddressSlotWord σ I ⟨6⟩)) := by
  simpa [endAddressSlotWord, endSlotWord] using
    (RD.solcAddressGetterExternal (code := endBytecode) (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (sel := sel) (entry := ⟨835⟩) (routine := ⟨6675⟩) (slot := ⟨6⟩)
      (returnPc := ⟨572⟩)
      hreach
      (by dsimp [solcGetterEntryWf]; repeat' first | apply And.intro | native_decide)
      (by dsimp [solcAddressSlotGetterWf]; repeat' first | apply And.intro | native_decide)
      (by jump_dest) (by jump_dest)
      (by dsimp [solcReturnAddressFromMemWf]; repeat' first | apply And.intro | native_decide))

theorem endX_cure {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨843⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (endAddressSlotWord σ I ⟨7⟩)) := by
  simpa [endAddressSlotWord, endSlotWord] using
    (RD.solcAddressGetterExternal (code := endBytecode) (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (sel := sel) (entry := ⟨843⟩) (routine := ⟨6690⟩) (slot := ⟨7⟩)
      (returnPc := ⟨572⟩)
      hreach
      (by dsimp [solcGetterEntryWf]; repeat' first | apply And.intro | native_decide)
      (by dsimp [solcAddressSlotGetterWf]; repeat' first | apply And.intro | native_decide)
      (by jump_dest) (by jump_dest)
      (by dsimp [solcReturnAddressFromMemWf]; repeat' first | apply And.intro | native_decide))

theorem endX_live {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨933⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (endSlotWord σ I ⟨8⟩)) := by
  simpa [endSlotWord] using
    (RD.solcWordGetterExternal (code := endBytecode) (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (sel := sel) (entry := ⟨933⟩) (routine := ⟨7494⟩) (slot := ⟨8⟩)
      (returnPc := ⟨509⟩)
      hreach
      (by dsimp [solcGetterEntryWf]; repeat' first | apply And.intro | native_decide)
      (by dsimp [solcWordSlotGetterWf]; repeat' first | apply And.intro | native_decide)
      (by jump_dest) (by jump_dest)
      (by dsimp [solcReturnWordFromMemWf]; repeat' first | apply And.intro | native_decide))

theorem endX_when {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1200⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (endSlotWord σ I ⟨9⟩)) := by
  simpa [endSlotWord] using
    (RD.solcWordGetterExternal (code := endBytecode) (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (sel := sel) (entry := ⟨1200⟩) (routine := ⟨9552⟩) (slot := ⟨9⟩)
      (returnPc := ⟨509⟩)
      hreach
      (by dsimp [solcGetterEntryWf]; repeat' first | apply And.intro | native_decide)
      (by dsimp [solcWordSlotGetterWf]; repeat' first | apply And.intro | native_decide)
      (by jump_dest) (by jump_dest)
      (by dsimp [solcReturnWordFromMemWf]; repeat' first | apply And.intro | native_decide))

theorem endX_wait {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨752⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (endSlotWord σ I ⟨10⟩)) := by
  simpa [endSlotWord] using
    (RD.solcWordGetterExternal (code := endBytecode) (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (sel := sel) (entry := ⟨752⟩) (routine := ⟨5269⟩) (slot := ⟨10⟩)
      (returnPc := ⟨509⟩)
      hreach
      (by dsimp [solcGetterEntryWf]; repeat' first | apply And.intro | native_decide)
      (by dsimp [solcWordSlotGetterWf]; repeat' first | apply And.intro | native_decide)
      (by jump_dest) (by jump_dest)
      (by dsimp [solcReturnWordFromMemWf]; repeat' first | apply And.intro | native_decide))

theorem endVatBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 1))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨564⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz := endSelectorMatches_size 1 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some vatTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 1 (by omega) hsel
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (vatTransition.params.map Param.name) (transitionSignature vatTransition).paramTypes
      I.calldata = some ∅ := by
    simpa using endDecode_noArgs (I := I) hsz
  have hword : endAddressSlotWord σ_evm I ⟨1⟩ = endAddressSlotWord σ_solm I ⟨1⟩ := by
    have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simpa [endAddressSlotWord, endSlotWord] using
      congrArg (fun w => UInt256.land w solcAddrMask) hslot
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ vatTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat (endAddressSlotWord σ_solm I ⟨1⟩).toNat))])) := by
    simpa [endAddressSlotWord, endSlotWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      endVatBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact (endX_vat (g := Sat256.ofUInt256 g) hreach).reEquivExecutionTransport hcode hd hdec
    hbody
    (by
      change some [Value.address (AccountAddress.ofNat (endAddressSlotWord σ_solm I ⟨1⟩).toNat)] =
        some [Value.address (AccountAddress.ofNat (endAddressSlotWord σ_evm I ⟨1⟩).toNat)]
      rw [hword])
    hAccounts
    (returnEquiv_of_encode (endAddressReturnEncoding (endSlotWord σ_evm I ⟨1⟩)))

theorem endCatBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 2))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1208⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz := endSelectorMatches_size 2 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some catTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 2 (by omega) hsel
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (catTransition.params.map Param.name) (transitionSignature catTransition).paramTypes
      I.calldata = some ∅ := by
    simpa using endDecode_noArgs (I := I) hsz
  have hword := endAddressSlotWord_eq_of_accountMapEquiv hAccounts I ⟨2⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ catTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [Value.address (AccountAddress.ofNat (endAddressSlotWord σ_solm I ⟨2⟩).toNat)])) := by
    simpa [endAddressSlotWord, endSlotWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      endCatBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact (endX_cat (g := Sat256.ofUInt256 g) hreach).reEquivExecutionTransport hcode hd hdec
    hbody
    (by
      change some [Value.address (AccountAddress.ofNat (endAddressSlotWord σ_solm I ⟨2⟩).toNat)] =
        some [Value.address (AccountAddress.ofNat (endAddressSlotWord σ_evm I ⟨2⟩).toNat)]
      rw [hword])
    hAccounts
    (returnEquiv_of_encode (endAddressReturnEncoding (endSlotWord σ_evm I ⟨2⟩)))

theorem endDogBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 3))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1017⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz := endSelectorMatches_size 3 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some dogTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 3 (by omega) hsel
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (dogTransition.params.map Param.name) (transitionSignature dogTransition).paramTypes
      I.calldata = some ∅ := by
    simpa using endDecode_noArgs (I := I) hsz
  have hword := endAddressSlotWord_eq_of_accountMapEquiv hAccounts I ⟨3⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ dogTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [Value.address (AccountAddress.ofNat (endAddressSlotWord σ_solm I ⟨3⟩).toNat)])) := by
    simpa [endAddressSlotWord, endSlotWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      endDogBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact (endX_dog (g := Sat256.ofUInt256 g) hreach).reEquivExecutionTransport hcode hd hdec
    hbody
    (by
      change some [Value.address (AccountAddress.ofNat (endAddressSlotWord σ_solm I ⟨3⟩).toNat)] =
        some [Value.address (AccountAddress.ofNat (endAddressSlotWord σ_evm I ⟨3⟩).toNat)]
      rw [hword])
    hAccounts
    (returnEquiv_of_encode (endAddressReturnEncoding (endSlotWord σ_evm I ⟨3⟩)))

theorem endVowBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 4))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨715⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz := endSelectorMatches_size 4 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some vowTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 4 (by omega) hsel
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (vowTransition.params.map Param.name) (transitionSignature vowTransition).paramTypes
      I.calldata = some ∅ := by
    simpa using endDecode_noArgs (I := I) hsz
  have hword := endAddressSlotWord_eq_of_accountMapEquiv hAccounts I ⟨4⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ vowTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [Value.address (AccountAddress.ofNat (endAddressSlotWord σ_solm I ⟨4⟩).toNat)])) := by
    simpa [endAddressSlotWord, endSlotWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      endVowBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact (endX_vow (g := Sat256.ofUInt256 g) hreach).reEquivExecutionTransport hcode hd hdec
    hbody
    (by
      change some [Value.address (AccountAddress.ofNat (endAddressSlotWord σ_solm I ⟨4⟩).toNat)] =
        some [Value.address (AccountAddress.ofNat (endAddressSlotWord σ_evm I ⟨4⟩).toNat)]
      rw [hword])
    hAccounts
    (returnEquiv_of_encode (endAddressReturnEncoding (endSlotWord σ_evm I ⟨4⟩)))

theorem endPotBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 5))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨664⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz := endSelectorMatches_size 5 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some potTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 5 (by omega) hsel
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (potTransition.params.map Param.name) (transitionSignature potTransition).paramTypes
      I.calldata = some ∅ := by
    simpa using endDecode_noArgs (I := I) hsz
  have hword := endAddressSlotWord_eq_of_accountMapEquiv hAccounts I ⟨5⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ potTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [Value.address (AccountAddress.ofNat (endAddressSlotWord σ_solm I ⟨5⟩).toNat)])) := by
    simpa [endAddressSlotWord, endSlotWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      endPotBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact (endX_pot (g := Sat256.ofUInt256 g) hreach).reEquivExecutionTransport hcode hd hdec
    hbody
    (by
      change some [Value.address (AccountAddress.ofNat (endAddressSlotWord σ_solm I ⟨5⟩).toNat)] =
        some [Value.address (AccountAddress.ofNat (endAddressSlotWord σ_evm I ⟨5⟩).toNat)]
      rw [hword])
    hAccounts
    (returnEquiv_of_encode (endAddressReturnEncoding (endSlotWord σ_evm I ⟨5⟩)))

theorem endSpotBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 6))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨835⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz := endSelectorMatches_size 6 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some spotTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 6 (by omega) hsel
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (spotTransition.params.map Param.name) (transitionSignature spotTransition).paramTypes
      I.calldata = some ∅ := by
    simpa using endDecode_noArgs (I := I) hsz
  have hword := endAddressSlotWord_eq_of_accountMapEquiv hAccounts I ⟨6⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ spotTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [Value.address (AccountAddress.ofNat (endAddressSlotWord σ_solm I ⟨6⟩).toNat)])) := by
    simpa [endAddressSlotWord, endSlotWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      endSpotBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact (endX_spot (g := Sat256.ofUInt256 g) hreach).reEquivExecutionTransport hcode hd hdec
    hbody
    (by
      change some [Value.address (AccountAddress.ofNat (endAddressSlotWord σ_solm I ⟨6⟩).toNat)] =
        some [Value.address (AccountAddress.ofNat (endAddressSlotWord σ_evm I ⟨6⟩).toNat)]
      rw [hword])
    hAccounts
    (returnEquiv_of_encode (endAddressReturnEncoding (endSlotWord σ_evm I ⟨6⟩)))

theorem endCureBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 7))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨843⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz := endSelectorMatches_size 7 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some cureTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 7 (by omega) hsel
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (cureTransition.params.map Param.name) (transitionSignature cureTransition).paramTypes
      I.calldata = some ∅ := by
    simpa using endDecode_noArgs (I := I) hsz
  have hword := endAddressSlotWord_eq_of_accountMapEquiv hAccounts I ⟨7⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ cureTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [Value.address (AccountAddress.ofNat (endAddressSlotWord σ_solm I ⟨7⟩).toNat)])) := by
    simpa [endAddressSlotWord, endSlotWord, solcSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      endCureBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact (endX_cure (g := Sat256.ofUInt256 g) hreach).reEquivExecutionTransport hcode hd hdec
    hbody
    (by
      change some [Value.address (AccountAddress.ofNat (endAddressSlotWord σ_solm I ⟨7⟩).toNat)] =
        some [Value.address (AccountAddress.ofNat (endAddressSlotWord σ_evm I ⟨7⟩).toNat)]
      rw [hword])
    hAccounts
    (returnEquiv_of_encode (endAddressReturnEncoding (endSlotWord σ_evm I ⟨7⟩)))

theorem endLiveBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 8))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨933⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz := endSelectorMatches_size 8 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some liveTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 8 (by omega) hsel
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (liveTransition.params.map Param.name) (transitionSignature liveTransition).paramTypes
      I.calldata = some ∅ := by
    simpa using endDecode_noArgs (I := I) hsz
  have hword : endSlotWord σ_evm I ⟨8⟩ = endSlotWord σ_solm I ⟨8⟩ :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ liveTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (endSlotWord σ_solm I ⟨8⟩).toNat))])) := by
    simpa [endSlotWord, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      endLiveBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact (endX_live (g := Sat256.ofUInt256 g) hreach).reEquivExecutionTransport hcode hd hdec
    hbody (by rw [hword]) hAccounts
    (returnEquiv_of_encode (endUint256ReturnEncoding (endSlotWord σ_evm I ⟨8⟩)))

theorem endWhenBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 9))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1200⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz := endSelectorMatches_size 9 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some whenTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 9 (by omega) hsel
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (whenTransition.params.map Param.name) (transitionSignature whenTransition).paramTypes
      I.calldata = some ∅ := by
    simpa using endDecode_noArgs (I := I) hsz
  have hword : endSlotWord σ_evm I ⟨9⟩ = endSlotWord σ_solm I ⟨9⟩ :=
    endSlotWord_eq_of_accountMapEquiv hAccounts I ⟨9⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ whenTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (endSlotWord σ_solm I ⟨9⟩).toNat))])) := by
    simpa [endSlotWord, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      endWhenBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact (endX_when (g := Sat256.ofUInt256 g) hreach).reEquivExecutionTransport hcode hd hdec
    hbody (by rw [hword]) hAccounts
    (returnEquiv_of_encode (endUint256ReturnEncoding (endSlotWord σ_evm I ⟨9⟩)))

theorem endWaitBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsel : endSelectorMatches I (endSelBytes 10))
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨752⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz := endSelectorMatches_size 10 (by omega) hsel
  have hd : dispatchMsg contract I.calldata = some waitTransition := by
    simpa [endTransitionAt, transitions] using endDispatch_at 10 (by omega) hsel
  have hdec : decodeCalldataWithMode config.abiDecodeMode
      (waitTransition.params.map Param.name) (transitionSignature waitTransition).paramTypes
      I.calldata = some ∅ := by
    simpa using endDecode_noArgs (I := I) hsz
  have hword : endSlotWord σ_evm I ⟨10⟩ = endSlotWord σ_solm I ⟨10⟩ :=
    endSlotWord_eq_of_accountMapEquiv hAccounts I ⟨10⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ waitTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (endSlotWord σ_solm I ⟨10⟩).toNat))])) := by
    simpa [endSlotWord, solcSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      endWaitBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        (by simp only [initState]; exact hwv) (by simp)
  exact (endX_wait (g := Sat256.ofUInt256 g) hreach).reEquivExecutionTransport hcode hd hdec
    hbody (by rw [hword]) hAccounts
    (returnEquiv_of_encode (endUint256ReturnEncoding (endSlotWord σ_evm I ⟨10⟩)))

end Benchmarks.Dss.End
