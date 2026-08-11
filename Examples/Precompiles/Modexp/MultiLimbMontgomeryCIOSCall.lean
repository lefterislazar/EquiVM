import Examples.Precompiles.Modexp.MultiLimbMontgomeryOuterLoop
import Examples.Precompiles.Modexp.MultiLimbMontgomeryFinalize
import Examples.Precompiles.Modexp.Allocation
import Examples.Precompiles.Modexp.WideWordMemory

/-! # Exact deployed CIOS Montgomery-call setup -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp.MultiLimbMontgomeryCIOSCall

open Modexp.MultiLimbMontgomeryTrace
open Modexp.MultiLimbArithmeticTrace
open Modexp.MultiLimbMontgomeryFinalize
open Modexp.MultiLimbMontgomeryCompareTrace
open Modexp.MultiLimbDivisionTrace

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def ciosZeroMemory (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0 mem ptr.toNat 32

def ciosZeroAw (aw ptr : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat ptr.toNat 32)

def ciosZeroGas (aw ptr : UInt256) : Nat :=
  47 + (Cₘ (ciosZeroAw aw ptr) - Cₘ aw)

structure CIOSZeroState where
  ptr : UInt256
  memory : ByteArray
  activeWords : UInt256

def ciosZeroAdvance (state : CIOSZeroState) : CIOSZeroState where
  ptr := state.ptr + ⟨32⟩
  memory := ciosZeroMemory state.memory state.ptr
  activeWords := ciosZeroAw state.activeWords state.ptr

structure CIOSZeroSelection where
  final : CIOSZeroState
  iterations : Nat
  steps : Nat
  gas : Nat

def selectCIOSZeroLoop : Nat → UInt256 → CIOSZeroState → Option CIOSZeroSelection
  | 0, _, _ => none
  | fuel + 1, stop, state =>
      if state.ptr.lt stop = ⟨0⟩ then
        some { final := state, iterations := 0, steps := 1, gas := 10 }
      else
        match selectCIOSZeroLoop fuel stop (ciosZeroAdvance state) with
        | none => none
        | some rest => some {
            final := rest.final
            iterations := rest.iterations + 1
            steps := 17 + rest.steps
            gas := 10 + ciosZeroGas state.activeWords state.ptr + rest.gas }

def ciosSetupMemory (mem : ByteArray) (stop : UInt256) : ByteArray :=
  stop.toByteArray.write 0 mem 64 32

def ciosSetupAw (aw : UInt256) : UInt256 :=
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat 64 32)
  UInt256.ofNat (MachineState.M aw1.toNat 64 32)

def ciosSetupGas (aw : UInt256) : Nat :=
  let aw1 := UInt256.ofNat (MachineState.M aw.toNat 64 32)
  101 + (Cₘ aw1 - Cₘ aw) + (Cₘ (ciosSetupAw aw) - Cₘ aw1)

/-- Derive all CIOS pointers and reach the deployed scratch-zero guard. -/
theorem ciosSetupBody
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {resultBase n0inv aBase kWord nBefore returnPc bBase tP : UInt256}
    (hdepth : tail.length + 8 ≤ 1016)
    (hload : wideLoadWord mem aw ⟨64⟩ = tP)
    (h : RDx runtimeBytecode ee g s0 ⟨4068⟩
      (resultBase :: ⟨32⟩ :: n0inv :: aBase :: kWord :: nBefore ::
        returnPc :: bBase :: tail) mem aw rdata acc k C) :
    let kWords := UInt256.shiftLeft kWord ⟨5⟩
    let tEnd := tP + kWords
    let stop := tEnd + ⟨64⟩
    let zeroState : CIOSZeroState := {
      ptr := tP
      memory := ciosSetupMemory mem stop
      activeWords := ciosSetupAw aw }
    RDx runtimeBytecode ee g s0 ⟨4111⟩
      (⟨4552⟩ :: zeroState.ptr.lt stop :: zeroState.ptr :: stop :: n0inv :: aBase ::
        (bBase + ⟨32⟩) :: nBefore :: tP :: kWords :: tEnd ::
        (nBefore + ⟨32⟩) :: (resultBase + ⟨32⟩) :: kWords :: returnPc ::
        resultBase :: tail)
      zeroState.memory zeroState.activeWords rdata acc (k + 35) (C + ciosSetupGas aw) := by
  have rd := GeneratedTraces.trace_4068_body hdepth h
  simp only [wideLoadWord] at hload
  rw [hload] at rd
  rw [show (⟨64⟩ : UInt256).toNat = 64 by decide] at rd
  simpa [ciosSetupMemory, ciosSetupAw, ciosSetupGas,
    u256_add_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd

/-- One scratch-zero body, returning to the guard at PC 4111. -/
theorem ciosZeroBody
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {stop n0inv aBase bP nBefore tP kWords tEnd nP resultPtr returnPc resultBase : UInt256}
    (state : CIOSZeroState)
    (hdepth : tail.length + 14 ≤ 1022)
    (h : RDx runtimeBytecode ee g s0 ⟨4552⟩
      (state.ptr :: stop :: n0inv :: aBase :: bP :: nBefore :: tP :: kWords ::
        tEnd :: nP :: resultPtr :: kWords :: returnPc :: resultBase :: tail)
      state.memory state.activeWords rdata acc k C) :
    let next := ciosZeroAdvance state
    RDx runtimeBytecode ee g s0 ⟨4111⟩
      (⟨4552⟩ :: next.ptr.lt stop :: next.ptr :: stop :: n0inv :: aBase :: bP ::
        nBefore :: tP :: kWords :: tEnd :: nP :: resultPtr :: kWords :: returnPc ::
        resultBase :: tail)
      next.memory next.activeWords rdata acc (k + 16)
      (C + ciosZeroGas state.activeWords state.ptr) := by
  have rd := GeneratedTraces.trace_4552_body (by
    simp only [List.length_cons]
    omega) h
  simpa [ciosZeroAdvance, ciosZeroMemory, ciosZeroAw, ciosZeroGas,
    u256_add_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd

/-- A successful zero-loop selection reaches the post-loop setup at PC 4112 exactly. -/
theorem selectedCIOSZeroLoopExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fuel : Nat} {tail : List UInt256}
    {stop n0inv aBase bP nBefore tP kWords tEnd nP resultPtr returnPc resultBase : UInt256}
    (state : CIOSZeroState) (selected : CIOSZeroSelection)
    (hdepth : tail.length + 16 ≤ 1022)
    (hselect : selectCIOSZeroLoop fuel stop state = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨4111⟩
      (⟨4552⟩ :: state.ptr.lt stop :: state.ptr :: stop :: n0inv :: aBase :: bP ::
        nBefore :: tP :: kWords :: tEnd :: nP :: resultPtr :: kWords :: returnPc ::
        resultBase :: tail)
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4112⟩
      (selected.final.ptr :: stop :: n0inv :: aBase :: bP :: nBefore :: tP ::
        kWords :: tEnd :: nP :: resultPtr :: kWords :: returnPc :: resultBase :: tail)
      selected.final.memory selected.final.activeWords rdata acc
      (k + selected.steps) (C + selected.gas) := by
  induction fuel generalizing state selected k C with
  | zero => simp [selectCIOSZeroLoop] at hselect
  | succ fuel ih =>
      simp only [selectCIOSZeroLoop] at hselect
      by_cases hexit : state.ptr.lt stop = ⟨0⟩
      · rw [if_pos hexit] at hselect
        injection hselect with heq
        subst selected
        have rd4112 := h.jumpiNT (by native_decide) hexit (by
          simp only [List.length_cons]
          omega)
        exact rd4112.withPC (by native_decide)
      · rw [if_neg hexit] at hselect
        cases hrest : selectCIOSZeroLoop fuel stop (ciosZeroAdvance state) with
        | none => rw [hrest] at hselect; contradiction
        | some rest =>
            rw [hrest] at hselect
            injection hselect with heq
            subst selected
            have rd4552 := h.jumpiT (by native_decide) hexit (by native_decide) (by
              simp only [List.length_cons]
              omega)
            have rd4111 := ciosZeroBody state (by omega) rd4552
            have rdRest := ih (state := ciosZeroAdvance state) (selected := rest)
              (k := k + 17) (C := C + 10 + ciosZeroGas state.activeWords state.ptr)
              hrest (by simpa [ciosZeroAdvance] using rd4111)
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdRest

/-- Finish the post-zero pointer setup and enter the first CIOS outer iteration. -/
theorem ciosZeroExitToOuter
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {ptr stop n0inv aBase bP nBefore tP kWords tEnd nP resultPtr returnPc resultBase : UInt256}
    (hdepth : tail.length + 16 ≤ 1014)
    (houter : (aBase + ⟨32⟩).lt (aBase + kWords + ⟨32⟩) ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨4112⟩
      (ptr :: stop :: n0inv :: aBase :: bP :: nBefore :: tP :: kWords :: tEnd ::
        nP :: resultPtr :: kWords :: returnPc :: resultBase :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4312⟩
      ((aBase + ⟨32⟩) :: bP :: n0inv :: (tEnd + UInt256.lnot ⟨31⟩) ::
        (tEnd + ⟨32⟩) :: (aBase + kWords + ⟨32⟩) :: (tP + ⟨32⟩) ::
        nBefore :: tP :: kWords :: tEnd :: nP :: resultPtr :: kWords ::
        returnPc :: resultBase :: tail)
      mem aw rdata acc (k + 29) (C + 90) := by
  have rd4146 := GeneratedTraces.trace_4112_body (by
    simp only [List.length_cons]
    omega) h
  have rd4312 := rd4146.jumpiT (by native_decide) houter (by native_decide) (by
    simp only [List.length_cons]
    omega)
  simpa [u256_add_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd4312

structure CIOSSetupSelection where
  zero : CIOSZeroSelection
  outer : CIOSOuterState
  tP : UInt256
  tEnd : UInt256
  kWords : UInt256
  bP : UInt256
  nP : UInt256
  resultPtr : UInt256
  steps : Nat
  gas : Nat

def selectCIOSSetup (zeroFuel : Nat)
    (mem : ByteArray) (aw resultBase n0inv kWord nBefore returnPc aBase bBase : UInt256) :
    Option CIOSSetupSelection :=
  let kWords := UInt256.shiftLeft kWord ⟨5⟩
  let tP := wideLoadWord mem aw ⟨64⟩
  let tEnd := tP + kWords
  let stop := tEnd + ⟨64⟩
  let zeroState : CIOSZeroState := {
    ptr := tP
    memory := ciosSetupMemory mem stop
    activeWords := ciosSetupAw aw }
  if (aBase + ⟨32⟩).lt (aBase + kWords + ⟨32⟩) = ⟨0⟩ then none
  else
    match selectCIOSZeroLoop zeroFuel stop zeroState with
    | none => none
    | some zero => some {
        zero := zero
        outer := {
          aOff := aBase + ⟨32⟩
          memory := zero.final.memory
          activeWords := zero.final.activeWords }
        tP := tP
        tEnd := tEnd
        kWords := kWords
        bP := bBase + ⟨32⟩
        nP := nBefore + ⟨32⟩
        resultPtr := resultBase + ⟨32⟩
        steps := 35 + zero.steps + 29
        gas := ciosSetupGas aw + zero.gas + 90 }

/-- The complete deployed setup from PC 4068 to the first CIOS outer iteration. -/
theorem selectedCIOSSetupExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C zeroFuel : Nat} {tail : List UInt256}
    {resultBase n0inv kWord nBefore returnPc aBase bBase : UInt256}
    (selected : CIOSSetupSelection)
    (hdepth : tail.length + 16 ≤ 1014)
    (hselect : selectCIOSSetup zeroFuel mem aw resultBase n0inv kWord nBefore returnPc
      aBase bBase = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨4068⟩
      (resultBase :: ⟨32⟩ :: n0inv :: aBase :: kWord :: nBefore ::
        returnPc :: bBase :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4312⟩
      (selected.outer.aOff :: selected.bP :: n0inv ::
        (selected.tEnd + UInt256.lnot ⟨31⟩) :: (selected.tEnd + ⟨32⟩) ::
        (aBase + selected.kWords + ⟨32⟩) :: (selected.tP + ⟨32⟩) ::
        nBefore :: selected.tP :: selected.kWords :: selected.tEnd :: selected.nP ::
        selected.resultPtr :: selected.kWords :: returnPc :: resultBase :: tail)
      selected.outer.memory selected.outer.activeWords rdata acc
      (k + selected.steps) (C + selected.gas) := by
  unfold selectCIOSSetup at hselect
  dsimp only at hselect
  let kWords := UInt256.shiftLeft kWord ⟨5⟩
  let tP := wideLoadWord mem aw ⟨64⟩
  let tEnd := tP + kWords
  let stop := tEnd + ⟨64⟩
  let zeroState : CIOSZeroState := {
    ptr := tP
    memory := ciosSetupMemory mem stop
    activeWords := ciosSetupAw aw }
  by_cases houter : (aBase + ⟨32⟩).lt (aBase + kWords + ⟨32⟩) = ⟨0⟩
  · rw [if_pos houter] at hselect
    contradiction
  · rw [if_neg houter] at hselect
    cases hz : selectCIOSZeroLoop zeroFuel stop zeroState with
    | none => rw [hz] at hselect; contradiction
    | some zero =>
        rw [hz] at hselect
        injection hselect with heq
        subst selected
        have rd4111 := ciosSetupBody (by omega) (by rfl) h
        have rd4112 := selectedCIOSZeroLoopExact (tail := tail) zeroState zero (by omega) hz (by
          simpa [kWords, tP, tEnd, stop, zeroState] using rd4111)
        have rd4312 := ciosZeroExitToOuter (by omega) houter (by
          simpa [kWords, tP, tEnd, stop, zeroState] using rd4112)
        simpa [kWords, tP, tEnd, stop, zeroState,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd4312

private theorem ciosEntryDecodes :
    [decode runtimeBytecode ⟨4052⟩, decode runtimeBytecode ⟨4053⟩,
      decode runtimeBytecode ⟨4054⟩, decode runtimeBytecode ⟨4055⟩,
      decode runtimeBytecode ⟨4056⟩, decode runtimeBytecode ⟨4057⟩,
      decode runtimeBytecode ⟨4058⟩, decode runtimeBytecode ⟨4060⟩,
      decode runtimeBytecode ⟨4063⟩, decode runtimeBytecode ⟨4064⟩,
      decode runtimeBytecode ⟨4067⟩] =
    [some (.JUMPDEST, .none), some (.SWAP1, .none), some (.SWAP5, .none),
      some (.SWAP4, .none), some (.SWAP2, .none), some (.SWAP3, .none),
      some (.Push .PUSH1, some (⟨32⟩, 1)),
      some (.Push .PUSH2, some (⟨4068⟩, 2)), some (.DUP5, .none),
      some (.Push .PUSH2, some (⟨1487⟩, 2)), some (.JUMP, .none)] := by
  native_decide

private theorem jumpDest_1487_cios :
    (D_J runtimeBytecode 0).contains ⟨1487⟩ = true := by native_decide

structure CIOSFunctionPrefixSelection where
  setup : CIOSSetupSelection
  steps : Nat
  gas : Nat

def selectCIOSFunctionPrefix (zeroFuel : Nat)
    (mem : ByteArray) (aw : UInt256) (words fp : Nat)
    (aBase bBase nBefore n0inv returnPc : UInt256) : Option CIOSFunctionPrefixSelection :=
  let allocatedMemory :=
    storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize words)) fp words
  let allocatedAw := newWordArrayWords aw fp words
  match selectCIOSSetup zeroFuel allocatedMemory allocatedAw (UInt256.ofNat fp) n0inv
      (UInt256.ofNat words) nBefore returnPc aBase bBase with
  | none => none
  | some setup => some {
      setup := setup
      steps := 89 + setup.steps
      gas := 36 + newWordArrayGas aw fp words + setup.gas }

/-- `_montMul` from its deployed entry through allocation, zeroing, and CIOS-loop entry. -/
theorem selectedCIOSFunctionPrefixExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C zeroFuel words fp : Nat} {tail : List UInt256}
    {aBase bBase nBefore n0inv returnPc : UInt256}
    (selected : CIOSFunctionPrefixSelection)
    (hwords : words ≤ 32) (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize words < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hallocated64 : ¬ (⟨64⟩ : UInt256) ≥ newWordArrayWords aw fp words * ⟨32⟩)
    (hdepth : tail.length + 16 ≤ 1014)
    (hselect : selectCIOSFunctionPrefix zeroFuel mem aw words fp aBase bBase nBefore
      n0inv returnPc = some selected)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4052⟩
      (aBase :: bBase :: nBefore :: n0inv :: UInt256.ofNat words :: returnPc :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4312⟩
      (selected.setup.outer.aOff :: selected.setup.bP :: n0inv ::
        (selected.setup.tEnd + UInt256.lnot ⟨31⟩) ::
        (selected.setup.tEnd + ⟨32⟩) ::
        (aBase + selected.setup.kWords + ⟨32⟩) :: (selected.setup.tP + ⟨32⟩) ::
        nBefore :: selected.setup.tP :: selected.setup.kWords :: selected.setup.tEnd ::
        selected.setup.nP :: selected.setup.resultPtr :: selected.setup.kWords ::
        returnPc :: UInt256.ofNat fp :: tail)
      selected.setup.outer.memory selected.setup.outer.activeWords rdata acc
      (k + selected.steps) (C + selected.gas) := by
  let allocatedMemory :=
    storeBytesLength (setFreePtr mem (fp + wordArrayAllocationSize words)) fp words
  let allocatedAw := newWordArrayWords aw fp words
  unfold selectCIOSFunctionPrefix at hselect
  dsimp only at hselect
  cases hs : selectCIOSSetup zeroFuel allocatedMemory allocatedAw (UInt256.ofNat fp)
      n0inv (UInt256.ofNat words) nBefore returnPc aBase bBase with
  | none => simpa [allocatedMemory, allocatedAw, hs] using hselect
  | some setup =>
      have hselected : selected = {
          setup := setup
          steps := 89 + setup.steps
          gas := 36 + newWordArrayGas aw fp words + setup.gas } := by
        simpa [allocatedMemory, allocatedAw, hs] using hselect.symm
      subst selected
      have hd := ciosEntryDecodes
      simp only [List.cons.injEq, and_true] at hd
      rcases hd with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      have rd1487 := evm_run h with [known jumpdest h0, known swap1 h1, known swap5 h2,
        known swap4 h3, known swap2 h4, known swap3 h5, known push1 h6 ⟨32⟩,
        known push2 h7 ⟨4068⟩, known dup5 h8, known push2 h9 ⟨1487⟩,
        known jump h10 jumpDest_1487_cios]
      have rd1487Explicit :
          RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1487⟩
            (UInt256.ofNat words :: ⟨4068⟩ :: ⟨32⟩ :: n0inv :: aBase ::
              UInt256.ofNat words :: nBefore :: returnPc :: bBase :: tail)
            mem aw rdata acc (k + 11) (C + 36) := by
        simpa using rd1487
      have rd4068 := newWordArrayExact (n := words) (fp := fp) (ret := 4068)
        (tail := ⟨32⟩ :: n0inv :: aBase :: UInt256.ofNat words :: nBefore ::
          returnPc :: bBase :: tail)
        hwords hfp hbound hmemSize hmemLe hgap haw3 haw64 hread hcalldata
        (by simp only [List.length_cons]; omega) (by native_decide) rd1487Explicit
      have hsetSize :
          (setFreePtr mem (fp + wordArrayAllocationSize words)).size = mem.size :=
        setFreePtr_size hmemSize
      have hallocatedRead :
          allocatedMemory.readWithPadding 64 32 =
            UInt256.toByteArray (UInt256.ofNat (fp + wordArrayAllocationSize words)) := by
        dsimp [allocatedMemory]
        rw [storeBytesLength_read64]
        · exact setFreePtr_read64 hmemSize
        · rw [hsetSize]; exact hmemSize
        · exact hfp
        · rw [hsetSize]; exact hgap
      have hallocatedSize : 64 < allocatedMemory.size := by
        dsimp [allocatedMemory]
        rw [storeBytesLength_size]
        · omega
        · rw [hsetSize]; exact hmemLe
        · rw [hsetSize]; exact hgap
      have hload : wideLoadWord allocatedMemory allocatedAw ⟨64⟩ =
          UInt256.ofNat (fp + wordArrayAllocationSize words) := by
        apply wideLoadWord_eq_of_read (mem := allocatedMemory) (aw := allocatedAw)
          (off := ⟨64⟩) (value := UInt256.ofNat (fp + wordArrayAllocationSize words))
          (by simpa using hallocatedSize) hallocated64
        simpa [show (⟨64⟩ : UInt256).toNat = 64 by decide] using hallocatedRead
      have rd4312 := selectedCIOSSetupExact setup (tail := tail) (by omega) hs (by
        simpa [allocatedMemory, allocatedAw] using rd4068)
      simpa [allocatedMemory, allocatedAw, hload,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd4312

theorem ciosOuterIterationGasAfter_add
    (C columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState) :
    ciosOuterIterationGasAfter C columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore shiftedOut state =
      C + ciosOuterIterationGas columns bP tP tEnd tk1Off nP n0inv
        tOff nBefore shiftedOut state := by
  simp only [ciosOuterIterationGas, ciosOuterIterationGasAfter,
    ciosOuterGasAfter, ciosBoundaryGasAfter, ciosShiftGasAfter]
  omega

theorem ciosOuterOneLimbGasAfter_add
    (C : Nat) (bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut : UInt256)
    (state : CIOSOuterState) :
    ciosOuterOneLimbGasAfter C bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut state =
      C + ciosOuterOneLimbGasAfter 0 bP tP tEnd tk1Off nP n0inv tOff nBefore
        shiftedOut state := by
  simp only [ciosOuterOneLimbGasAfter, ciosOuterGasAfter,
    ciosBoundaryGasAfter, ciosShiftGasAfter]
  omega

structure CIOSOuterSelection where
  final : CIOSOuterState
  iterations : Nat
  steps : Nat
  gas : Nat

def selectCIOSOuter : Nat → Nat →
    UInt256 → UInt256 → UInt256 → UInt256 → UInt256 → UInt256 → UInt256 → UInt256 →
      UInt256 → UInt256 → CIOSOuterState → Option CIOSOuterSelection
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | fuel + 1, columns, bP, tP, tEnd, tk1Off, nP, n0inv, tOff, nBefore,
      shiftedOut, aEnd, state =>
      if columns = 1 then
        if (state.aOff + ⟨32⟩).lt aEnd = ⟨0⟩ then
          some {
            final := ciosOuterAdvanceOne bP tP tEnd tk1Off nP n0inv tOff nBefore
              shiftedOut state
            iterations := 1
            steps := 182
            gas := ciosOuterOneLimbGasAfter 0 bP tP tEnd tk1Off nP n0inv
              tOff nBefore shiftedOut state }
        else none
      else if 1 < columns then
        let next := ciosOuterAdvance columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore shiftedOut state
        let iterationGas := ciosOuterIterationGas columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore shiftedOut state
        if (state.aOff + ⟨32⟩).lt aEnd = ⟨0⟩ then
          some {
            final := next
            iterations := 1
            steps := 126 + 56 * columns + 61 * (columns - 1)
            gas := iterationGas }
        else
          match selectCIOSOuter fuel columns bP tP tEnd tk1Off nP n0inv tOff
              nBefore shiftedOut aEnd next with
          | none => none
          | some rest => some {
              final := rest.final
              iterations := rest.iterations + 1
              steps := 126 + 56 * columns + 61 * (columns - 1) + rest.steps
              gas := iterationGas + rest.gas }
      else none

structure CIOSArithmeticFacts (columns : Nat)
    (bP tP tEnd tk1Off nP n0inv tOff nBefore : UInt256)
    (state : CIOSOuterState) : Prop where
  outer : tP.lt tEnd ≠ ⟨0⟩
  multiplyContinue : ∀ j, j < columns - 1 →
    (multiplyPassAdvance (ciosOuterAi state.memory state.activeWords state.aOff)
      (multiplyPassIterate (ciosOuterAi state.memory state.activeWords state.aOff) j
        (ciosMultiplyInitial bP tP state))).resultPtr.lt tEnd ≠ ⟨0⟩
  multiplyExit :
    (multiplyPassAdvance (ciosOuterAi state.memory state.activeWords state.aOff)
      (multiplyPassIterate (ciosOuterAi state.memory state.activeWords state.aOff)
        (columns - 1) (ciosMultiplyInitial bP tP state))).resultPtr.lt tEnd = ⟨0⟩
  reductionStart : tOff.lt tEnd ≠ ⟨0⟩
  reductionContinue : ∀ j, j < columns - 2 →
    (schoolbookAdvance
      (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state)
      (schoolbookIterate
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state) j
        (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore state))).resultPtr.lt tEnd ≠ ⟨0⟩
  reductionExit :
    (schoolbookAdvance
      (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state)
      (schoolbookIterate
        (ciosReductionFactor columns bP tP tEnd tk1Off n0inv state)
        (columns - 2)
        (ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
          tOff nBefore state))).resultPtr.lt tEnd = ⟨0⟩

theorem ciosArithmeticFacts_of_layout
    (columns : Nat) (bP tP tEnd tk1Off nP n0inv tOff nBefore : UInt256)
    (state : CIOSOuterState)
    (hcolumns : 1 < columns)
    (hmultiplyBound : tP.toNat + 32 * columns < UInt256.size)
    (hmultiplyStop : tEnd.toNat = tP.toNat + 32 * columns)
    (hreductionBound : tOff.toNat + 32 * (columns - 1) < UInt256.size)
    (hreductionStop : tEnd.toNat = tOff.toNat + 32 * (columns - 1)) :
    CIOSArithmeticFacts columns bP tP tEnd tk1Off nP n0inv tOff nBefore state := by
  let ai := ciosOuterAi state.memory state.activeWords state.aOff
  let multiplyInitial := ciosMultiplyInitial bP tP state
  let factor := ciosReductionFactor columns bP tP tEnd tk1Off n0inv state
  let reductionInitial := ciosReductionInitial columns bP tP tEnd tk1Off nP n0inv
    tOff nBefore state
  have hmultiply := multiplyPassGuardFacts ai tEnd columns multiplyInitial
    (by omega) (by simpa [multiplyInitial, ciosMultiplyInitial] using hmultiplyBound)
    (by simpa [multiplyInitial, ciosMultiplyInitial] using hmultiplyStop)
  have hreduction := schoolbookGuardFacts factor tEnd (columns - 1) reductionInitial
    (by omega)
    (by simpa [reductionInitial, ciosReductionInitial] using hreductionBound)
    (by simpa [reductionInitial, ciosReductionInitial] using hreductionStop)
  have houterNat : tP.toNat < tEnd.toNat := by rw [hmultiplyStop]; omega
  have hredNat : tOff.toNat < tEnd.toNat := by rw [hreductionStop]; omega
  refine {
    outer := ?_
    multiplyContinue := ?_
    multiplyExit := ?_
    reductionStart := ?_
    reductionContinue := ?_
    reductionExit := ?_ }
  · rw [ult_one houterNat]
    decide
  · simpa only [ai, multiplyInitial] using hmultiply.1
  · simpa only [ai, multiplyInitial] using hmultiply.2
  · rw [ult_one hredNat]
    decide
  · simpa only [factor, reductionInitial, Nat.sub_sub] using hreduction.1
  · simpa only [factor, reductionInitial, Nat.sub_sub] using hreduction.2

/-- A successful selector executes every CIOS outer iteration and exits at PC 4147. -/
theorem selectedCIOSOuterExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fuel columns : Nat} {tail : List UInt256}
    {bP tP tEnd tk1Off nP n0inv tOff nBefore shiftedOut aEnd tail0 tail1 : UInt256}
    (state : CIOSOuterState) (selected : CIOSOuterSelection)
    (hdepth : tail.length + 17 ≤ 1014)
    (hmultiplyBound : tP.toNat + 32 * columns < UInt256.size)
    (hmultiplyStop : tEnd.toNat = tP.toNat + 32 * columns)
    (hreductionBound : tOff.toNat + 32 * (columns - 1) < UInt256.size)
    (hreductionStop : tEnd.toNat = tOff.toNat + 32 * (columns - 1))
    (hselect : selectCIOSOuter fuel columns bP tP tEnd tk1Off nP n0inv tOff nBefore
      shiftedOut aEnd state = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨4312⟩
      (state.aOff :: bP :: n0inv :: shiftedOut :: tk1Off :: aEnd :: tOff ::
        nBefore :: tP :: tail1 :: tEnd :: nP :: tail0 :: tail1 :: tail)
      state.memory state.activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4147⟩
      (selected.final.aOff :: bP :: n0inv :: shiftedOut :: tk1Off :: aEnd :: tOff ::
        nBefore :: tP :: tail1 :: tEnd :: nP :: tail0 :: tail1 :: tail)
      selected.final.memory selected.final.activeWords rdata acc
      (k + selected.steps) (C + selected.gas) := by
  induction fuel generalizing state selected k C with
  | zero => simp [selectCIOSOuter] at hselect
  | succ fuel ih =>
      simp only [selectCIOSOuter] at hselect
      by_cases hone : columns = 1
      · rw [if_pos hone] at hselect
        subst columns
        by_cases hexit : (state.aOff + ⟨32⟩).lt aEnd = ⟨0⟩
        · rw [if_pos hexit] at hselect
          injection hselect with heq
          subst selected
          have hmultiply := multiplyPassGuardFacts
            (ciosOuterAi state.memory state.activeWords state.aOff) tEnd 1
            (ciosMultiplyInitial bP tP state) (by omega)
            (by simpa [ciosMultiplyInitial] using hmultiplyBound)
            (by simpa [ciosMultiplyInitial] using hmultiplyStop)
          have houterNat : tP.toNat < tEnd.toNat := by rw [hmultiplyStop]; omega
          have houter : tP.lt tEnd ≠ ⟨0⟩ := by rw [ult_one houterNat]; decide
          have hredEmptyNat : tOff.toNat = tEnd.toNat := by
            simpa using hreductionStop.symm
          have hredEmpty : tOff.lt tEnd = ⟨0⟩ := by
            rw [ult_zero]
            omega
          have rd := ciosOuterOneLimbThroughExit state hdepth houter
            (by simpa only [ciosMultiplyInitial] using hmultiply.2) hredEmpty hexit h
          rw [ciosOuterOneLimbGasAfter_add] at rd
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd
        · rw [if_neg hexit] at hselect
          contradiction
      · rw [if_neg hone] at hselect
        by_cases hcolumns : 1 < columns
        · rw [if_pos hcolumns] at hselect
          let next := ciosOuterAdvance columns bP tP tEnd tk1Off nP n0inv
            tOff nBefore shiftedOut state
          let iterationGas := ciosOuterIterationGas columns bP tP tEnd tk1Off nP n0inv
            tOff nBefore shiftedOut state
          have facts := ciosArithmeticFacts_of_layout columns bP tP tEnd tk1Off nP n0inv
            tOff nBefore state hcolumns hmultiplyBound hmultiplyStop hreductionBound
            hreductionStop
          by_cases hexit : (state.aOff + ⟨32⟩).lt aEnd = ⟨0⟩
          · rw [if_pos hexit] at hselect
            injection hselect with heq
            subst selected
            have rd := ciosOuterFinalIteration state hdepth hcolumns facts.outer
              facts.multiplyContinue facts.multiplyExit facts.reductionStart
              facts.reductionContinue facts.reductionExit hexit h
            rw [ciosOuterIterationGasAfter_add] at rd
            simpa only [next, iterationGas, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using rd
          · rw [if_neg hexit] at hselect
            cases hrest : selectCIOSOuter fuel columns bP tP tEnd tk1Off nP n0inv tOff
                nBefore shiftedOut aEnd next with
            | none => rw [hrest] at hselect; contradiction
            | some rest =>
                rw [hrest] at hselect
                injection hselect with heq
                subst selected
                have rdNext := ciosOuterIteration state hdepth hcolumns facts.outer
                  facts.multiplyContinue facts.multiplyExit facts.reductionStart
                  facts.reductionContinue facts.reductionExit hexit h
                have rdRest := ih (state := next) (selected := rest)
                  (k := k + (126 + 56 * columns + 61 * (columns - 1)))
                  (C := ciosOuterIterationGasAfter C columns bP tP tEnd tk1Off nP
                    n0inv tOff nBefore shiftedOut state)
                  hrest (by simpa [next, Nat.add_assoc] using rdNext)
                rw [ciosOuterIterationGasAfter_add] at rdRest
                simpa only [iterationGas, Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using rdRest
        · rw [if_neg hcolumns] at hselect
          contradiction

structure CIOSCompareSelection where
  tOff : UInt256
  nOff : UInt256
  activeWords : UInt256
  doSub : UInt256
  iterations : Nat
  steps : Nat
  gas : Nat

def selectCIOSCompare (fuel : Nat) (mem : ByteArray)
    (tP activeWords tOff nOff prevTOff : UInt256) : Option CIOSCompareSelection :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if (compareNWord mem activeWords tOff nOff).toNat <
          (compareTWord mem activeWords tOff).toNat then
        some {
          tOff := tP
          nOff := comparePrev nOff
          activeWords := compareAw activeWords tOff nOff
          doSub := ⟨1⟩
          iterations := 1
          steps := 45
          gas := compareLoadGasAfter 0 activeWords tOff nOff + 97 }
      else if (compareTWord mem activeWords tOff).toNat <
          (compareNWord mem activeWords tOff nOff).toNat then
        some {
          tOff := tP
          nOff := comparePrev nOff
          activeWords := compareAw activeWords tOff nOff
          doSub := ⟨0⟩
          iterations := 1
          steps := 47
          gas := compareLoadGasAfter 0 activeWords tOff nOff + 101 }
      else if prevTOff.gt tP ≠ ⟨0⟩ then
        match selectCIOSCompare fuel mem tP (compareAw activeWords tOff nOff)
            prevTOff (comparePrev nOff) (comparePrev prevTOff) with
        | none => none
        | some rest => some {
            tOff := rest.tOff
            nOff := rest.nOff
            activeWords := rest.activeWords
            doSub := rest.doSub
            iterations := rest.iterations + 1
            steps := 39 + rest.steps
            gas := compareLoadGasAfter 0 activeWords tOff nOff + 77 + rest.gas }
      else
        some {
          tOff := prevTOff
          nOff := comparePrev nOff
          activeWords := compareAw activeWords tOff nOff
          doSub := ⟨1⟩
          iterations := 1
          steps := 39
          gas := compareLoadGasAfter 0 activeWords tOff nOff + 77 }

theorem compareLoadGasAfter_add (C : Nat) (aw tOff nOff : UInt256) :
    compareLoadGasAfter C aw tOff nOff = C + compareLoadGasAfter 0 aw tOff nOff := by
  simp [compareLoadGasAfter]
  omega

/-- Every successful comparison selection reaches the CIOS copy block exactly. -/
theorem selectedCIOSCompareExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fuel : Nat} {tail : List UInt256}
    {tP junk resultPtr nP bytes : UInt256}
    {activeWords tOff nOff prevTOff : UInt256}
    (selected : CIOSCompareSelection)
    (hdepth : tail.length + 8 ≤ 1021)
    (hprev : prevTOff = comparePrev tOff)
    (hselect : selectCIOSCompare fuel mem tP activeWords tOff nOff prevTOff =
      some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨4255⟩
      (tOff :: nOff :: tP :: junk :: ⟨1⟩ :: resultPtr :: nP :: bytes :: tail)
      mem activeWords rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4165⟩
      (selected.tOff :: selected.nOff :: tP :: bytes :: selected.doSub ::
        resultPtr :: nP :: bytes :: tail)
      mem selected.activeWords rdata acc (k + selected.steps) (C + selected.gas) := by
  induction fuel generalizing activeWords tOff nOff prevTOff selected k C junk with
  | zero => simp [selectCIOSCompare] at hselect
  | succ fuel ih =>
      simp only [selectCIOSCompare] at hselect
      by_cases hgreater :
          (compareNWord mem activeWords tOff nOff).toNat <
            (compareTWord mem activeWords tOff).toNat
      · rw [if_pos hgreater] at hselect
        injection hselect with heq
        subst selected
        have rd := compareGreaterToCopy hdepth hgreater h
        rw [compareLoadGasAfter_add] at rd
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd
      · rw [if_neg hgreater] at hselect
        by_cases hless :
            (compareTWord mem activeWords tOff).toNat <
              (compareNWord mem activeWords tOff nOff).toNat
        · rw [if_pos hless] at hselect
          injection hselect with heq
          subst selected
          have rd := compareLessToCopy hdepth hless h
          rw [compareLoadGasAfter_add] at rd
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd
        · rw [if_neg hless] at hselect
          have hequal : compareTWord mem activeWords tOff =
              compareNWord mem activeWords tOff nOff := by
            apply u256_inj
            omega
          by_cases hguard : prevTOff.gt tP ≠ ⟨0⟩
          · rw [if_pos hguard] at hselect
            let nextAw := compareAw activeWords tOff nOff
            let nextTOff := prevTOff
            let nextNOff := comparePrev nOff
            let nextPrevTOff := comparePrev prevTOff
            cases hrest : selectCIOSCompare fuel mem tP nextAw nextTOff nextNOff
                nextPrevTOff with
            | none => rw [hrest] at hselect; contradiction
            | some rest =>
                rw [hrest] at hselect
                injection hselect with heq
                subst selected
                have hcontinuePrev : tP.toNat < prevTOff.toNat := by
                  by_contra hnot
                  apply hguard
                  exact ugt_zero (by omega)
                have hcontinue : tP.toNat < (comparePrev tOff).toNat := by
                  rw [← hprev]
                  exact hcontinuePrev
                have rdNext := compareEqualContinue hdepth hequal hcontinue h
                have rdRest := ih (junk := bytes) (activeWords := nextAw)
                  (tOff := nextTOff) (nOff := nextNOff)
                  (prevTOff := nextPrevTOff) (selected := rest) (by
                    simpa [nextPrevTOff, nextTOff]) hrest (by
                    simpa [nextAw, nextTOff, nextNOff, hprev] using rdNext)
                rw [compareLoadGasAfter_add] at rdRest
                simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdRest
          · rw [if_neg hguard] at hselect
            injection hselect with heq
            subst selected
            have hexitPrev : prevTOff.toNat ≤ tP.toNat := by
              by_contra hnot
              apply hguard
              rw [ugt_one (show tP.toNat < prevTOff.toNat by omega)]
              native_decide
            have hexit : (comparePrev tOff).toNat ≤ tP.toNat := by
              rw [← hprev]
              exact hexitPrev
            have rd := compareEqualExit hdepth hequal hexit h
            rw [compareLoadGasAfter_add] at rd
            simpa only [hprev, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd

/-- A zero CIOS top word initializes the descending comparison and reaches PC 4255. -/
theorem ciosTopZeroToCompare
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {tail : List UInt256}
    {drop0 drop1 drop2 drop3 drop4 drop5 drop6 nBefore tP bytes tEnd
      nP resultPtr returnPc resultBase : UInt256}
    (hdepth : tail.length + 16 ≤ 1021)
    (htop : finalTopWord mem aw tEnd = ⟨0⟩)
    (hguard : tEnd.gt tP ≠ ⟨0⟩)
    (h : RDx runtimeBytecode ee g s0 ⟨4147⟩
      (drop0 :: drop1 :: drop2 :: drop3 :: drop4 :: drop5 :: drop6 ::
        nBefore :: tP :: bytes :: tEnd :: nP :: resultPtr :: bytes ::
        returnPc :: resultBase :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4255⟩
      (tEnd :: (⟨32⟩ + (bytes + nBefore)) :: tP :: bytes :: ⟨1⟩ ::
        nP :: resultPtr :: bytes :: returnPc :: resultBase :: tail)
      mem (finalTopAw aw tEnd) rdata acc (k + 33) (finalTopGasAfter C aw tEnd + 63) := by
  have rd4234 := finalTopZeroToCompare (tail := nP :: resultPtr :: bytes ::
    returnPc :: resultBase :: tail) (by simp only [List.length_cons]; omega) htop h
  have rd4254 := GeneratedTraces.trace_4234_body
    (tail := nP :: resultPtr :: bytes :: returnPc :: resultBase :: tail)
    (by simp only [List.length_cons]; omega) rd4234
  have hcond : (tEnd.gt tP).isZero = ⟨0⟩ := isZero_eq_zero_of_ne hguard
  have rd4255 := rd4254.jumpiNT (by native_decide) hcond
    (by simp only [List.length_cons]; omega)
  have normalized := rd4255.withIndices (k' := k + 33)
    (C' := finalTopGasAfter C aw tEnd + 63) (by omega) (by omega)
  simpa [u256_add_comm, u256_add_assoc] using normalized

structure CIOSSubtractionSelection where
  final : SubtractionState
  iterations : Nat
  steps : Nat
  gas : Nat

def selectCIOSSubtraction : Nat → UInt256 → SubtractionState →
    Option CIOSSubtractionSelection
  | 0, _, _ => none
  | fuel + 1, stop, state =>
      let next := subtractionAdvance state
      let columnGas := subtractionGas state.activeWords state.leftPtr state.rightPtr + 10
      if next.leftPtr.lt stop ≠ ⟨0⟩ then
        match selectCIOSSubtraction fuel stop next with
        | none => none
        | some rest => some {
            final := rest.final
            iterations := rest.iterations + 1
            steps := 35 + rest.steps
            gas := columnGas + rest.gas }
      else
        some { final := next, iterations := 1, steps := 35, gas := columnGas }

/-- Execute every selected final-subtraction column and stop at cleanup PC 4197. -/
theorem selectedCIOSSubtractionExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fuel : Nat} {tail : List UInt256} {stop : UInt256}
    (state : SubtractionState) (selected : CIOSSubtractionSelection)
    (hdepth : tail.length + 4 ≤ 1017)
    (hselect : selectCIOSSubtraction fuel stop state = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨4202⟩
      (subtractionLoopStack state stop tail) state.memory state.activeWords
      rdata acc k C) :
    RDx runtimeBytecode ee g s0 ⟨4197⟩
      (subtractionLoopStack selected.final stop tail)
      selected.final.memory selected.final.activeWords rdata acc
      (k + selected.steps) (C + selected.gas) := by
  induction fuel generalizing state selected k C with
  | zero => simp [selectCIOSSubtraction] at hselect
  | succ fuel ih =>
      simp only [selectCIOSSubtraction] at hselect
      let next := subtractionAdvance state
      let columnGas := subtractionGas state.activeWords state.leftPtr state.rightPtr + 10
      by_cases hcontinue : next.leftPtr.lt stop ≠ ⟨0⟩
      · rw [if_pos hcontinue] at hselect
        cases hrest : selectCIOSSubtraction fuel stop next with
        | none => rw [hrest] at hselect; contradiction
        | some rest =>
            rw [hrest] at hselect
            injection hselect with heq
            subst selected
            have rd4196 := finalSubtractionBody hdepth h
            have rd4202 := rd4196.jumpiT (by native_decide) hcontinue
              (by native_decide) (by simp only [List.length_cons]; omega)
            have rdRest := ih (state := next) (selected := rest)
              (k := k + 35) (C := C + columnGas) hrest (by
                simpa [next, columnGas, subtractionLoopStack,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rd4202)
            simpa [columnGas, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdRest
      · rw [if_neg hcontinue] at hselect
        injection hselect with heq
        subst selected
        have rd4196 := finalSubtractionBody hdepth h
        have hexit : next.leftPtr.lt stop = ⟨0⟩ := by
          by_contra hne
          exact hcontinue hne
        have rd4197 := rd4196.jumpiNT (by native_decide) hexit
          (by simp only [List.length_cons]; omega)
        have normalized := rd4197.withIndices (k' := k + 35)
          (C' := C + columnGas) (by omega) (by simp [columnGas]; omega)
        simpa [next, subtractionLoopStack] using normalized

structure CIOSCopySelection where
  memory : ByteArray
  activeWords : UInt256
  steps : Nat
  gas : Nat

def selectCIOSCopy (fuel : Nat) (mem : ByteArray)
    (aw source bytes doSub resultPtr nP resultBase : UInt256) :
    Option CIOSCopySelection :=
  let copied := finalCopyMemory mem source resultPtr bytes
  let copiedAw := finalCopyAw aw source resultPtr bytes
  let copyGas := finalCopyGas aw source resultPtr bytes
  let stop := ⟨32⟩ + (bytes + resultBase)
  if doSub = ⟨0⟩ then
    some { memory := copied, activeWords := copiedAw, steps := 11, gas := copyGas + 24 }
  else if resultPtr.lt stop = ⟨0⟩ then none
  else
    let initial := finalSubtractionInitialState copied copiedAw resultPtr nP
    match selectCIOSSubtraction fuel stop initial with
    | none => none
    | some sub => some {
        memory := sub.final.memory
        activeWords := sub.final.activeWords
        steps := 28 + sub.steps
        gas := copyGas + 76 + sub.gas }

/-- Copy the CIOS candidate, conditionally subtract every modulus limb, and return. -/
theorem selectedCIOSCopyExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C fuel : Nat} {tail : List UInt256}
    {tOff nOff source bytes doSub rightPtr resultPtr resultBase returnPc : UInt256}
    (selected : CIOSCopySelection)
    (hdepth : tail.length + 10 ≤ 1021)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (hselect : selectCIOSCopy fuel mem aw source bytes doSub resultPtr rightPtr
      resultBase = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨4165⟩
      (tOff :: nOff :: source :: bytes :: doSub :: rightPtr :: resultPtr ::
        bytes :: returnPc :: resultBase :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 returnPc (resultBase :: tail)
      selected.memory selected.activeWords rdata acc
      (k + selected.steps) (C + selected.gas) := by
  let copied := finalCopyMemory mem source resultPtr bytes
  let copiedAw := finalCopyAw aw source resultPtr bytes
  let copyGas := finalCopyGas aw source resultPtr bytes
  let stop := ⟨32⟩ + (bytes + resultBase)
  unfold selectCIOSCopy at hselect
  dsimp only at hselect
  by_cases hdoSub : doSub = ⟨0⟩
  · rw [if_pos hdoSub] at hselect
    injection hselect with heq
    subst selected
    subst doSub
    have rd := finalCopyNoSubReturn (by omega) hreturn h
    simpa [copied, copiedAw, copyGas] using rd
  · rw [if_neg hdoSub] at hselect
    by_cases hempty : resultPtr.lt stop = ⟨0⟩
    · rw [if_pos hempty] at hselect
      contradiction
    · rw [if_neg hempty] at hselect
      let initial := finalSubtractionInitialState copied copiedAw resultPtr rightPtr
      cases hsub : selectCIOSSubtraction fuel stop initial with
      | none => rw [hsub] at hselect; contradiction
      | some sub =>
          rw [hsub] at hselect
          injection hselect with heq
          subst selected
          have rd4202 := finalCopyToSubtraction (resultBase := bytes)
            (bytesAgain := resultBase) hdepth hdoSub (by
              simpa [stop, u256_add_comm] using hempty) h
          have hstop : (⟨32⟩ : UInt256) + (resultBase + bytes) = stop := by
            simp [stop, u256_add_comm resultBase bytes]
          rw [hstop] at rd4202
          have rd4197 := selectedCIOSSubtractionExact initial sub
            (tail := returnPc :: resultBase :: tail) (by
              simp only [List.length_cons]
              omega) hsub (by
              simpa [initial, copied, copiedAw, stop, subtractionLoopStack]
                using rd4202)
          have rd4201 := GeneratedTraces.trace_4197_body
            (tail := resultBase :: tail) (by simp only [List.length_cons]; omega) (by
              simpa [subtractionLoopStack, stop] using rd4197)
          have rdReturn := rd4201.jump (by native_decide) hreturn
            (by simp only [List.length_cons]; omega)
          have normalized := rdReturn.withIndices
            (k' := k + (28 + sub.steps))
            (C' := C + (copyGas + 76 + sub.gas)) (by omega) (by omega)
          simpa [copied, copiedAw, copyGas, initial,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using normalized

theorem finalTopGasAfter_add (C : Nat) (aw tEnd : UInt256) :
    finalTopGasAfter C aw tEnd = C + finalTopGasAfter 0 aw tEnd := by
  simp [finalTopGasAfter]
  omega

structure CIOSFinalizeSelection where
  memory : ByteArray
  activeWords : UInt256
  steps : Nat
  gas : Nat

def selectCIOSFinalize (compareFuel subFuel : Nat)
    (mem : ByteArray) (aw nBefore tP bytes tEnd nP resultPtr resultBase : UInt256) :
    Option CIOSFinalizeSelection :=
  let topAw := finalTopAw aw tEnd
  if finalTopWord mem aw tEnd = ⟨0⟩ then
    if tEnd.gt tP = ⟨0⟩ then none
    else
      match selectCIOSCompare compareFuel mem tP topAw tEnd (⟨32⟩ + (bytes + nBefore))
          (comparePrev tEnd) with
      | none => none
      | some comparison =>
          match selectCIOSCopy subFuel mem comparison.activeWords tP bytes
              comparison.doSub resultPtr nP resultBase with
          | none => none
          | some copy => some {
              memory := copy.memory
              activeWords := copy.activeWords
              steps := 33 + comparison.steps + copy.steps
              gas := finalTopGasAfter 0 aw tEnd + 63 + comparison.gas + copy.gas }
  else
    match selectCIOSCopy subFuel mem topAw tP bytes ⟨1⟩ resultPtr nP resultBase with
    | none => none
    | some copy => some {
        memory := copy.memory
        activeWords := copy.activeWords
        steps := 16 + copy.steps
        gas := finalTopGasAfter 0 aw tEnd + 10 + copy.gas }

/-- Complete CIOS finalization from the outer-loop exit through the dynamic caller return. -/
theorem selectedCIOSFinalizeExact
    {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C compareFuel subFuel : Nat} {tail : List UInt256}
    {drop0 drop1 drop2 drop3 drop4 drop5 drop6 nBefore tP bytes tEnd nP
      resultPtr returnPc resultBase : UInt256}
    (selected : CIOSFinalizeSelection)
    (hdepth : tail.length + 16 ≤ 1021)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (hselect : selectCIOSFinalize compareFuel subFuel mem aw nBefore tP bytes tEnd nP
      resultPtr resultBase = some selected)
    (h : RDx runtimeBytecode ee g s0 ⟨4147⟩
      (drop0 :: drop1 :: drop2 :: drop3 :: drop4 :: drop5 :: drop6 ::
        nBefore :: tP :: bytes :: tEnd :: nP :: resultPtr :: bytes ::
        returnPc :: resultBase :: tail) mem aw rdata acc k C) :
    RDx runtimeBytecode ee g s0 returnPc (resultBase :: tail)
      selected.memory selected.activeWords rdata acc
      (k + selected.steps) (C + selected.gas) := by
  let topAw := finalTopAw aw tEnd
  unfold selectCIOSFinalize at hselect
  dsimp only at hselect
  by_cases htop : finalTopWord mem aw tEnd = ⟨0⟩
  · rw [if_pos htop] at hselect
    by_cases hguardZero : tEnd.gt tP = ⟨0⟩
    · rw [if_pos hguardZero] at hselect
      contradiction
    · rw [if_neg hguardZero] at hselect
      cases hcomparison : selectCIOSCompare compareFuel mem tP topAw tEnd
          (⟨32⟩ + (bytes + nBefore)) (comparePrev tEnd) with
      | none => rw [hcomparison] at hselect; contradiction
      | some comparison =>
          rw [hcomparison] at hselect
          simp only at hselect
          cases hcopy : selectCIOSCopy subFuel mem comparison.activeWords tP bytes
              comparison.doSub resultPtr nP resultBase with
          | none => rw [hcopy] at hselect; contradiction
          | some copy =>
              rw [hcopy] at hselect
              injection hselect with heq
              subst selected
              have rd4255 := ciosTopZeroToCompare hdepth htop hguardZero h
              have rd4165 := selectedCIOSCompareExact comparison
                (tail := returnPc :: resultBase :: tail) (by
                  simp only [List.length_cons]
                  omega) rfl hcomparison (by
                  simpa [topAw] using rd4255)
              have rdReturn := selectedCIOSCopyExact copy (tail := tail) (by omega) hreturn
                hcopy (by simpa using rd4165)
              rw [finalTopGasAfter_add] at rdReturn
              simpa [topAw, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
                using rdReturn
  · rw [if_neg htop] at hselect
    cases hcopy : selectCIOSCopy subFuel mem topAw tP bytes ⟨1⟩ resultPtr nP
        resultBase with
    | none => rw [hcopy] at hselect; contradiction
    | some copy =>
        rw [hcopy] at hselect
        injection hselect with heq
        subst selected
        have rd4165 := finalTopNonzeroToCopy (tail := nP :: resultPtr :: bytes ::
          returnPc :: resultBase :: tail) (by simp only [List.length_cons]; omega) htop h
        have rdReturn := selectedCIOSCopyExact copy (tail := tail) (by omega) hreturn hcopy (by
          simpa [topAw] using rd4165)
        rw [finalTopGasAfter_add] at rdReturn
        simpa [topAw, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdReturn

structure CIOSFunctionSelection where
  head : CIOSFunctionPrefixSelection
  outer : CIOSOuterSelection
  finalize : CIOSFinalizeSelection
  steps : Nat
  gas : Nat

def selectCIOSFunction (zeroFuel outerFuel compareFuel subFuel : Nat)
    (mem : ByteArray) (aw : UInt256) (words fp : Nat)
    (aBase bBase nBefore n0inv returnPc : UInt256) : Option CIOSFunctionSelection :=
  match selectCIOSFunctionPrefix zeroFuel mem aw words fp aBase bBase nBefore n0inv
      returnPc with
  | none => none
  | some head =>
      let setup := head.setup
      let shiftedOut := setup.tEnd + UInt256.lnot ⟨31⟩
      let tk1Off := setup.tEnd + ⟨32⟩
      let tOff := setup.tP + ⟨32⟩
      let aEnd := aBase + setup.kWords + ⟨32⟩
      match selectCIOSOuter outerFuel words setup.bP setup.tP setup.tEnd tk1Off
          setup.nP n0inv tOff nBefore shiftedOut aEnd setup.outer with
      | none => none
      | some outer =>
          match selectCIOSFinalize compareFuel subFuel outer.final.memory
              outer.final.activeWords nBefore setup.tP setup.kWords setup.tEnd setup.nP
              setup.resultPtr (UInt256.ofNat fp) with
          | none => none
          | some finalize => some {
              head := head
              outer := outer
              finalize := finalize
              steps := head.steps + outer.steps + finalize.steps
              gas := head.gas + outer.gas + finalize.gas }

/-- The complete deployed `_montMul` call, including every CIOS computation and return. -/
theorem selectedCIOSFunctionExact
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C zeroFuel outerFuel compareFuel subFuel words fp : Nat}
    {tail : List UInt256} {aBase bBase nBefore n0inv returnPc : UInt256}
    (selected : CIOSFunctionSelection)
    (hwords : words ≤ 32) (hfp : 96 ≤ fp)
    (hbound : fp + wordArrayAllocationSize words < 2 ^ 64)
    (hmemSize : 96 ≤ mem.size) (hmemLe : mem.size ≤ fp)
    (hgap : fp - mem.size < USize.size)
    (haw3 : 3 ≤ aw.toNat) (haw64 : ¬ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat fp))
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hallocated64 : ¬ (⟨64⟩ : UInt256) ≥ newWordArrayWords aw fp words * ⟨32⟩)
    (hmultiplyBound : selected.head.setup.tP.toNat + 32 * words < UInt256.size)
    (hmultiplyStop : selected.head.setup.tEnd.toNat =
      selected.head.setup.tP.toNat + 32 * words)
    (hreductionBound : (selected.head.setup.tP + ⟨32⟩).toNat +
      32 * (words - 1) < UInt256.size)
    (hreductionStop : selected.head.setup.tEnd.toNat =
      (selected.head.setup.tP + ⟨32⟩).toNat + 32 * (words - 1))
    (hdepth : tail.length + 19 ≤ 1014)
    (hreturn : (D_J runtimeBytecode 0).contains returnPc = true)
    (hselect : selectCIOSFunction zeroFuel outerFuel compareFuel subFuel mem aw words fp
      aBase bBase nBefore n0inv returnPc = some selected)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4052⟩
      (aBase :: bBase :: nBefore :: n0inv :: UInt256.ofNat words :: returnPc :: tail)
      mem aw rdata acc k C) :
    RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) returnPc
      (UInt256.ofNat fp :: tail) selected.finalize.memory selected.finalize.activeWords
      rdata acc (k + selected.steps) (C + selected.gas) := by
  unfold selectCIOSFunction at hselect
  cases hp : selectCIOSFunctionPrefix zeroFuel mem aw words fp aBase bBase nBefore
      n0inv returnPc with
  | none => rw [hp] at hselect; contradiction
  | some head =>
      rw [hp] at hselect
      let setup := head.setup
      let shiftedOut := setup.tEnd + UInt256.lnot ⟨31⟩
      let tk1Off := setup.tEnd + ⟨32⟩
      let tOff := setup.tP + ⟨32⟩
      let aEnd := aBase + setup.kWords + ⟨32⟩
      cases ho : selectCIOSOuter outerFuel words setup.bP setup.tP setup.tEnd tk1Off
          setup.nP n0inv tOff nBefore shiftedOut aEnd setup.outer with
      | none => simp [setup, shiftedOut, tk1Off, tOff, aEnd, ho] at hselect
      | some outer =>
          simp only [setup, shiftedOut, tk1Off, tOff, aEnd, ho] at hselect
          cases hf : selectCIOSFinalize compareFuel subFuel outer.final.memory
              outer.final.activeWords nBefore setup.tP setup.kWords setup.tEnd setup.nP
              setup.resultPtr (UInt256.ofNat fp) with
          | none => rw [hf] at hselect; contradiction
          | some finalize =>
              rw [hf] at hselect
              injection hselect with heq
              subst selected
              have rd4312 := selectedCIOSFunctionPrefixExact head
                hwords hfp hbound hmemSize hmemLe hgap haw3 haw64 hread hcalldata
                hallocated64 (by omega) hp h
              have rd4147 := selectedCIOSOuterExact setup.outer outer
                (tail := returnPc :: UInt256.ofNat fp :: tail) (by
                  simp only [List.length_cons]
                  omega) hmultiplyBound hmultiplyStop hreductionBound hreductionStop ho (by
                  simpa [setup, shiftedOut, tk1Off, tOff, aEnd] using rd4312)
              have rdReturn := selectedCIOSFinalizeExact finalize (tail := tail)
                (by omega) hreturn hf (by
                  simpa [setup, shiftedOut, tk1Off, tOff, aEnd] using rd4147)
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rdReturn

end Modexp.MultiLimbMontgomeryCIOSCall
