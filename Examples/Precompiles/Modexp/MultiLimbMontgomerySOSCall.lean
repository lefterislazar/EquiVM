import Examples.Precompiles.Modexp.MultiLimbMontgomerySOSFull
import Examples.Precompiles.Modexp.WideWordMemory

/-! # SOS scratch initialization and arithmetic composition -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbMontgomerySOSCall

open Modexp.MultiLimbMontgomerySOSLoop
open Modexp.MultiLimbMontgomerySOSFinalize
open Modexp.MultiLimbMontgomerySOSFull

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def sosZeroMemory (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0 mem ptr.toNat 32

def sosZeroAw (aw ptr : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)

def sosZeroGas (aw ptr : UInt256) : Nat :=
  47 + (Cₘ (sosZeroAw aw ptr) - Cₘ aw)

structure SOSZeroState where
  ptr : UInt256
  memory : ByteArray
  activeWords : UInt256

def sosZeroAdvance (state : SOSZeroState) : SOSZeroState where
  ptr := state.ptr + ⟨32⟩
  memory := sosZeroMemory state.memory state.ptr
  activeWords := sosZeroAw state.activeWords state.ptr

structure SOSZeroSelection where
  final : SOSZeroState
  iterations : Nat
  steps : Nat
  gas : Nat

def selectSOSZeroLoop : Nat → UInt256 → SOSZeroState → Option SOSZeroSelection
  | 0, _, _ => none
  | fuel + 1, stop, state =>
      if state.ptr.lt stop = ⟨0⟩ then
        some { final := state, iterations := 0, steps := 1, gas := 10 }
      else
        match selectSOSZeroLoop fuel stop (sosZeroAdvance state) with
        | none => none
        | some rest => some {
            final := rest.final
            iterations := rest.iterations + 1
            steps := 17 + rest.steps
            gas := 10 + sosZeroGas state.activeWords state.ptr + rest.gas }

/-- One deployed scratch-zero body, returning to the loop guard at PC 7266. -/
theorem sosZeroBody
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {stop aP aEnd sP n0inv kWords nBefore resultPtr nP returnPc resultBase : UInt256}
    (state : SOSZeroState)
    (hdepth : tail.length + 13 ≤ 1022)
    (h : RDx runtimeBytecode ee g s0 ⟨7884⟩
      (state.ptr :: stop :: aP :: aEnd :: sP :: n0inv :: kWords :: nBefore ::
        resultPtr :: nP :: kWords :: returnPc :: resultBase :: tail)
      state.memory state.activeWords rdata acc k C) :
    let next := sosZeroAdvance state
    RDx runtimeBytecode ee g s0 ⟨7266⟩
      (⟨7884⟩ :: next.ptr.lt stop :: next.ptr :: stop :: aP :: aEnd :: sP :: n0inv ::
        kWords :: nBefore :: resultPtr :: nP :: kWords :: returnPc :: resultBase :: tail)
      next.memory next.activeWords rdata acc (k + 16)
      (C + sosZeroGas state.activeWords state.ptr) := by
  have rd := GeneratedTraces.trace_7884_body (by
    simp only [List.length_cons]
    omega) h
  simpa [sosZeroAdvance, sosZeroMemory, sosZeroAw, sosZeroGas,
    u256_add_comm,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd

def sosSetupMemory (mem : ByteArray) (sEnd : UInt256) : ByteArray :=
  sEnd.toByteArray.write 0 mem 64 32

def sosSetupAw (aw : UInt256) : UInt256 :=
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat 64 32)
  UInt256.ofNat (MachineState.M aw1.toNat 64 32)

def sosSetupGas (aw : UInt256) : Nat :=
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat 64 32)
  122 + (Cₘ aw1 - Cₘ aw) + (Cₘ (sosSetupAw aw) - Cₘ aw1)

/-- The deployed `_montSqr` setup computes every pointer and reaches the scratch-zero guard. -/
theorem sosSetupBody
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {resultBase nBefore n0inv kWord returnPc aBase sP : UInt256}
    (hdepth : tail.length + 7 ≤ 1016)
    (hload : wideLoadWord mem aw ⟨64⟩ = sP)
    (h : RDx runtimeBytecode ee g s0 ⟨7217⟩
      (resultBase :: nBefore :: n0inv :: kWord :: ⟨32⟩ :: returnPc :: aBase :: tail)
      mem aw rdata acc k C) :
    let kWords := UInt256.shiftLeft kWord ⟨5⟩
    let aP := aBase + ⟨32⟩
    let aEnd := ⟨32⟩ + (aBase + kWords)
    let resultPtr := resultBase + ⟨32⟩
    let nP := nBefore + ⟨32⟩
    let sEnd := sP + UInt256.shiftLeft kWord ⟨6⟩ + ⟨32⟩
    let zeroState : SOSZeroState := {
      ptr := sP
      memory := sosSetupMemory mem sEnd
      activeWords := sosSetupAw aw }
    RDx runtimeBytecode ee g s0 ⟨7266⟩
      (⟨7884⟩ :: zeroState.ptr.lt sEnd :: zeroState.ptr :: sEnd :: aP :: aEnd :: sP ::
        n0inv :: kWords :: nBefore :: resultPtr :: nP :: kWords :: returnPc :: resultBase :: tail)
      zeroState.memory zeroState.activeWords rdata acc (k + 42) (C + sosSetupGas aw) := by
  have rd := GeneratedTraces.trace_7217_body hdepth h
  simp only [wideLoadWord] at hload
  rw [hload] at rd
  rw [show (⟨64⟩ : UInt256).toNat = 64 by decide] at rd
  simpa [wideLoadWord, sosSetupMemory, sosSetupAw, sosSetupGas,
    u256_add_comm, u256_add_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd

/-- A successful selector executes every scratch-zero iteration and exits at PC 7267 exactly. -/
theorem selectedSOSZeroLoopExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fuel : Nat} {tail : List UInt256}
    {stop aP aEnd sP n0inv kWords nBefore resultPtr nP returnPc resultBase : UInt256}
    (state : SOSZeroState) (selected : SOSZeroSelection)
    (hdepth : tail.length + 15 ≤ 1022)
    (hselect : selectSOSZeroLoop fuel stop state = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨7266⟩
      (⟨7884⟩ :: state.ptr.lt stop :: state.ptr :: stop :: aP :: aEnd :: sP :: n0inv ::
        kWords :: nBefore :: resultPtr :: nP :: kWords :: returnPc :: resultBase :: tail)
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨7267⟩
      (selected.final.ptr :: stop :: aP :: aEnd :: sP :: n0inv :: kWords :: nBefore ::
        resultPtr :: nP :: kWords :: returnPc :: resultBase :: tail)
      selected.final.memory selected.final.activeWords rdata acc
      (k + selected.steps) (C + selected.gas) := by
  induction fuel generalizing state selected k C with
  | zero => simp [selectSOSZeroLoop] at hselect
  | succ fuel ih =>
      simp only [selectSOSZeroLoop] at hselect
      by_cases hexit : state.ptr.lt stop = ⟨0⟩
      · rw [if_pos hexit] at hselect
        injection hselect with heq
        subst selected
        have rd7274 := h.jumpiNT (by native_decide) hexit (by
          simp only [List.length_cons]
          omega)
        exact rd7274.withPC (by native_decide)
      · rw [if_neg hexit] at hselect
        cases hrest : selectSOSZeroLoop fuel stop (sosZeroAdvance state) with
        | none => rw [hrest] at hselect; contradiction
        | some rest =>
            rw [hrest] at hselect
            injection hselect with heq
            subst selected
            have rd7891 := h.jumpiT (by native_decide) hexit (by native_decide) (by
              simp only [List.length_cons]
              omega)
            have rd7273 := sosZeroBody state (by omega) rd7891
            have rdRest := ih (state := sosZeroAdvance state) (selected := rest)
              (k := k + 17) (C := C + 10 + sosZeroGas state.activeWords state.ptr)
              hrest (by simpa [sosZeroAdvance] using rd7273)
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdRest

structure SOSInitializedSelection where
  zero : SOSZeroSelection
  arithmetic : SOSFullSelection
  steps : Nat
  gas : Nat

def selectSOSInitialized
    (zeroFuel rowFuel productFuel doubleFuel diagonalFuel reductionFuel columnFuel
      carryFuel compareFuel subFuel : Nat)
    (zeroState : SOSZeroState)
    (sEnd aP aEnd sP n0inv kWords nBefore resultPtr nP resultBase : UInt256) :
    Option SOSInitializedSelection :=
  match selectSOSZeroLoop zeroFuel sEnd zeroState with
  | none => none
  | some zero =>
      match selectSOSFull rowFuel productFuel doubleFuel diagonalFuel reductionFuel columnFuel
          carryFuel compareFuel subFuel
          { sRow := sP + ⟨32⟩
            aOff := aP
            memory := zero.final.memory
            activeWords := zero.final.activeWords }
          sEnd aP aEnd sP n0inv kWords nBefore resultPtr nP resultBase with
      | none => none
      | some arithmetic => some {
          zero := zero
          arithmetic := arithmetic
          steps := zero.steps + 10 + arithmetic.steps
          gas := zero.gas + 27 + arithmetic.gas }

/-- Scratch initialization and the complete SOS arithmetic body execute as one exact segment. -/
theorem selectedSOSInitializedExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C zeroFuel rowFuel productFuel doubleFuel diagonalFuel reductionFuel columnFuel
      carryFuel compareFuel subFuel : Nat}
    {tail : List UInt256}
    {sEnd aP aEnd sP n0inv kWords nBefore resultPtr nP resultBase returnPc : UInt256}
    (zeroState : SOSZeroState)
    (selected : SOSInitializedSelection)
    (hdepth : tail.length + 16 ≤ 1012)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (hselect : selectSOSInitialized zeroFuel rowFuel productFuel doubleFuel diagonalFuel
      reductionFuel columnFuel carryFuel compareFuel subFuel zeroState
      sEnd aP aEnd sP n0inv kWords nBefore resultPtr nP resultBase = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨7266⟩
      (⟨7884⟩ :: zeroState.ptr.lt sEnd :: zeroState.ptr :: sEnd :: aP :: aEnd :: sP ::
        n0inv :: kWords :: nBefore :: resultPtr :: nP :: kWords :: returnPc :: resultBase :: tail)
      zeroState.memory zeroState.activeWords rdata acc k C) :
    SOSCopyReturnPost ee g s0 returnPc resultBase tail
      selected.arithmetic.suffix.copy.memory selected.arithmetic.suffix.copy.activeWords
      rdata acc (k + selected.steps) (C + selected.gas) := by
  unfold selectSOSInitialized at hselect
  cases hz : selectSOSZeroLoop zeroFuel sEnd zeroState with
  | none => rw [hz] at hselect; contradiction
  | some zero =>
      rw [hz] at hselect
      cases ha : selectSOSFull rowFuel productFuel doubleFuel diagonalFuel reductionFuel
          columnFuel carryFuel compareFuel subFuel
          { sRow := sP + ⟨32⟩
            aOff := aP
            memory := zero.final.memory
            activeWords := zero.final.activeWords }
          sEnd aP aEnd sP n0inv kWords nBefore resultPtr nP resultBase with
      | none => simp [ha] at hselect
      | some arithmetic =>
          have hselected : selected = {
              zero := zero
              arithmetic := arithmetic
              steps := zero.steps + 10 + arithmetic.steps
              gas := zero.gas + 27 + arithmetic.gas } := by
            simpa [ha] using hselect.symm
          subst selected
          have rd7274 := selectedSOSZeroLoopExact zeroState zero (by omega) hz h
          have rd7287 := GeneratedTraces.trace_7267_body (by
            simp only [List.length_cons]
            omega) rd7274
          have rdReturn := selectedSOSFullExact
            { sRow := sP + ⟨32⟩
              aOff := aP
              memory := zero.final.memory
              activeWords := zero.final.activeWords } arithmetic
            (tail := tail) (by omega) hreturn ha (by
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd7287)
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdReturn

structure SOSSetupSelection where
  initialized : SOSInitializedSelection
  steps : Nat
  gas : Nat

def selectSOSSetup
    (zeroFuel rowFuel productFuel doubleFuel diagonalFuel reductionFuel columnFuel
      carryFuel compareFuel subFuel : Nat)
    (mem : ByteArray) (aw resultBase nBefore n0inv kWord aBase sP : UInt256) :
    Option SOSSetupSelection :=
  let kWords := UInt256.shiftLeft kWord ⟨5⟩
  let aP := aBase + ⟨32⟩
  let aEnd := ⟨32⟩ + (aBase + kWords)
  let resultPtr := resultBase + ⟨32⟩
  let nP := nBefore + ⟨32⟩
  let sEnd := sP + UInt256.shiftLeft kWord ⟨6⟩ + ⟨32⟩
  let zeroState : SOSZeroState := {
    ptr := sP
    memory := sosSetupMemory mem sEnd
    activeWords := sosSetupAw aw }
  match selectSOSInitialized zeroFuel rowFuel productFuel doubleFuel diagonalFuel reductionFuel
      columnFuel carryFuel compareFuel subFuel zeroState sEnd aP aEnd sP n0inv kWords
      nBefore resultPtr nP resultBase with
  | none => none
  | some initialized => some {
      initialized := initialized
      steps := 42 + initialized.steps
      gas := sosSetupGas aw + initialized.gas }

/-- From the post-allocation return at PC 7217, setup and all SOS arithmetic execute exactly. -/
theorem selectedSOSSetupExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C zeroFuel rowFuel productFuel doubleFuel diagonalFuel reductionFuel columnFuel
      carryFuel compareFuel subFuel : Nat}
    {tail : List UInt256}
    {resultBase nBefore n0inv kWord returnPc aBase sP : UInt256}
    (selected : SOSSetupSelection)
    (hdepth : tail.length + 16 ≤ 1012)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (hload : wideLoadWord mem aw ⟨64⟩ = sP)
    (hselect : selectSOSSetup zeroFuel rowFuel productFuel doubleFuel diagonalFuel
      reductionFuel columnFuel carryFuel compareFuel subFuel mem aw resultBase nBefore
      n0inv kWord aBase sP = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨7217⟩
      (resultBase :: nBefore :: n0inv :: kWord :: ⟨32⟩ :: returnPc :: aBase :: tail)
      mem aw rdata acc k C) :
    SOSCopyReturnPost ee g s0 returnPc resultBase tail
      selected.initialized.arithmetic.suffix.copy.memory
      selected.initialized.arithmetic.suffix.copy.activeWords
      rdata acc (k + selected.steps) (C + selected.gas) := by
  unfold selectSOSSetup at hselect
  dsimp only at hselect
  let kWords := UInt256.shiftLeft kWord ⟨5⟩
  let aP := aBase + ⟨32⟩
  let aEnd := ⟨32⟩ + (aBase + kWords)
  let resultPtr := resultBase + ⟨32⟩
  let nP := nBefore + ⟨32⟩
  let sEnd := sP + UInt256.shiftLeft kWord ⟨6⟩ + ⟨32⟩
  let zeroState : SOSZeroState := {
    ptr := sP
    memory := sosSetupMemory mem sEnd
    activeWords := sosSetupAw aw }
  cases hi : selectSOSInitialized zeroFuel rowFuel productFuel doubleFuel diagonalFuel
      reductionFuel columnFuel carryFuel compareFuel subFuel zeroState sEnd aP aEnd sP
      n0inv kWords nBefore resultPtr nP resultBase with
  | none => simpa [kWords, aP, aEnd, resultPtr, nP, sEnd, zeroState, hi] using hselect
  | some initialized =>
      have hselected : selected = {
          initialized := initialized
          steps := 42 + initialized.steps
          gas := sosSetupGas aw + initialized.gas } := by
        simpa [kWords, aP, aEnd, resultPtr, nP, sEnd, zeroState, hi] using hselect.symm
      subst selected
      have rd7273 := sosSetupBody (by omega) hload h
      have rdReturn := selectedSOSInitializedExact zeroState initialized
        (tail := tail) (by omega) hreturn hi (by
          simpa [kWords, aP, aEnd, resultPtr, nP, sEnd, zeroState] using rd7273)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdReturn

private theorem sosEntryDecodes :
    [decode runtimeBytecode ⟨7201⟩, decode runtimeBytecode ⟨7202⟩,
      decode runtimeBytecode ⟨7203⟩, decode runtimeBytecode ⟨7204⟩,
      decode runtimeBytecode ⟨7205⟩, decode runtimeBytecode ⟨7206⟩,
      decode runtimeBytecode ⟨7208⟩, decode runtimeBytecode ⟨7209⟩,
      decode runtimeBytecode ⟨7212⟩, decode runtimeBytecode ⟨7213⟩,
      decode runtimeBytecode ⟨7216⟩] =
    [some (.JUMPDEST, .none), some (.SWAP4, .none), some (.SWAP3, .none),
      some (.SWAP1, .none), some (.SWAP2, .none),
      some (.Push .PUSH1, some (⟨32⟩, 1)), some (.SWAP3, .none),
      some (.Push .PUSH2, some (⟨7217⟩, 2)), some (.DUP4, .none),
      some (.Push .PUSH2, some (⟨1487⟩, 2)), some (.JUMP, .none)] := by
  native_decide

private theorem jumpDest_1487_sos :
    (D_J runtimeBytecode 0).contains ⟨1487⟩ = true := by native_decide

structure SOSFunctionSelection where
  setup : SOSSetupSelection
  steps : Nat
  gas : Nat

def selectSOSFunction
    (zeroFuel rowFuel productFuel doubleFuel diagonalFuel reductionFuel columnFuel
      carryFuel compareFuel subFuel : Nat)
    (mem : ByteArray) (aw : UInt256) (words fp : Nat)
    (nBefore n0inv returnPc aBase : UInt256) : Option SOSFunctionSelection :=
  let allocatedMemory :=
    storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize words)) fp words
  let allocatedAw := newWordArrayWords aw fp words
  let sP := UInt256.ofNat (fp + wordArrayAllocationSize words)
  match selectSOSSetup zeroFuel rowFuel productFuel doubleFuel diagonalFuel reductionFuel
      columnFuel carryFuel compareFuel subFuel allocatedMemory allocatedAw (UInt256.ofNat fp)
      nBefore n0inv (UInt256.ofNat words) aBase sP with
  | none => none
  | some setup => some {
      setup := setup
      steps := 89 + setup.steps
      gas := 36 + newWordArrayGas aw fp words + setup.gas }

/-- The complete deployed `_montSqr` call, from PC 7201 through its dynamic return, is exact. -/
theorem selectedSOSFunctionExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C zeroFuel rowFuel productFuel doubleFuel diagonalFuel reductionFuel columnFuel
      carryFuel compareFuel subFuel words fp : Nat}
    {tail : List UInt256}
    {nBefore n0inv returnPc aBase : UInt256}
    (selected : SOSFunctionSelection)
    (hwords : words ≤ 32) (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize words < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hallocated64 : ¬ (⟨64⟩ : UInt256) ≥
      newWordArrayWords aw fp words * ⟨32⟩)
    (hdepth : tail.length + 16 ≤ 1012)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (hselect : selectSOSFunction zeroFuel rowFuel productFuel doubleFuel diagonalFuel
      reductionFuel columnFuel carryFuel compareFuel subFuel mem aw words fp nBefore n0inv
      returnPc aBase = some selected)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨7201⟩
      (aBase :: nBefore :: n0inv :: UInt256.ofNat words :: returnPc :: tail)
      mem aw rdata acc k C) :
    SOSCopyReturnPost I g (initState cA gh bl σ σ₀ g A I) returnPc
      (UInt256.ofNat fp) tail selected.setup.initialized.arithmetic.suffix.copy.memory
      selected.setup.initialized.arithmetic.suffix.copy.activeWords
      rdata acc (k + selected.steps) (C + selected.gas) := by
  let allocatedMemory :=
    storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize words)) fp words
  let allocatedAw := newWordArrayWords aw fp words
  let sP := UInt256.ofNat (fp + wordArrayAllocationSize words)
  unfold selectSOSFunction at hselect
  dsimp only at hselect
  cases hs : selectSOSSetup zeroFuel rowFuel productFuel doubleFuel diagonalFuel reductionFuel
      columnFuel carryFuel compareFuel subFuel allocatedMemory allocatedAw (UInt256.ofNat fp)
      nBefore n0inv (UInt256.ofNat words) aBase sP with
  | none => simpa [allocatedMemory, allocatedAw, sP, hs] using hselect
  | some setup =>
      have hselected : selected = {
          setup := setup
          steps := 89 + setup.steps
          gas := 36 + newWordArrayGas aw fp words + setup.gas } := by
        simpa [allocatedMemory, allocatedAw, sP, hs] using hselect.symm
      subst selected
      have hd := sosEntryDecodes
      simp only [List.cons.injEq, and_true] at hd
      rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      have rd1487 := evm_run h with [known jumpdest h0, known swap4 h1, known swap3 h2,
        known swap1 h3, known swap2 h4, known push1 h5 ⟨32⟩, known swap3 h6,
        known push2 h7 ⟨7217⟩, known dup4 h8, known push2 h9 ⟨1487⟩,
        known jump h10 jumpDest_1487_sos]
      have rd1487Explicit :
          RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1487⟩
            (UInt256.ofNat words :: ⟨7217⟩ :: nBefore :: n0inv ::
              UInt256.ofNat words :: ⟨32⟩ :: returnPc :: aBase :: tail)
            mem aw rdata acc (k + 11) (C + 36) := by
        simpa using rd1487
      have rd7224 := newWordArrayExact (n := words) (fp := fp) (ret := 7217)
        (tail := nBefore :: n0inv :: UInt256.ofNat words :: ⟨32⟩ :: returnPc :: aBase :: tail)
        hwords hfp hbound hmemSize hmemLe hgap haw3 haw64 hread hcalldata
        (by
          simp only [List.length_cons]
          omega) (by native_decide) rd1487Explicit
      have hsetSize :
          (setFreePtr mem (fp + wordArrayAllocationSize words)).size = mem.size :=
        setFreePtr_size hmemSize
      have hallocatedRead :
          allocatedMemory.readWithPadding 64 32 = UInt256.toByteArray sP := by
        dsimp [allocatedMemory, sP]
        rw [storeBytesLength_read64]
        · exact setFreePtr_read64 hmemSize
        · rw [hsetSize]
          exact hmemSize
        · exact hfp
        · rw [hsetSize]
          exact hgap
      have hallocatedSize : 64 < allocatedMemory.size := by
        dsimp [allocatedMemory]
        rw [storeBytesLength_size]
        · omega
        · rw [hsetSize]
          exact hmemLe
        · rw [hsetSize]
          exact hgap
      have hload : wideLoadWord allocatedMemory allocatedAw ⟨64⟩ = sP := by
        apply wideLoadWord_eq_of_read (mem := allocatedMemory) (aw := allocatedAw)
          (off := ⟨64⟩) (value := sP) (by simpa using hallocatedSize) hallocated64
        simpa [show (⟨64⟩ : UInt256).toNat = 64 by decide] using hallocatedRead
      have rdReturn := selectedSOSSetupExact setup (tail := tail) (by omega) hreturn
        hload hs (by
          simpa [allocatedMemory, allocatedAw, sP] using rd7224)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdReturn

end Modexp.MultiLimbMontgomerySOSCall
