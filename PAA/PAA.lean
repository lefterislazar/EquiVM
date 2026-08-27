import Mathlib.Logic.Relation
import Mathlib.Data.Nat.Init

universe uA uLA uB uLB uNode

/- Definition of a deterministic
   labeled transition system -/
structure Lts_det (A : Type uA) (L : Type uLA) where
  /- function assigns label to every state -/
  label : A → L
  /- the deterministc lts step -/
  step : A → Option A
  -- /- Set of final states -/ 
  isFinal : L → Prop

  /-- Final labels characterize states on which the stepper stops.  Concrete
      adapters may expose exceptional outcomes as explicit final states. -/
  hfinal : ∀ (f : A), isFinal (label f) ↔ step f = .none

def steps_det (t : Lts_det A lA) (σ σ' : A) : Prop :=
  Relation.ReflTransGen (λ σ σ' ↦ t.step σ = .some σ') σ σ'

inductive steps_det_N (t : Lts_det A lA) : A → A → ℕ → Prop where
  | final :
    t.isFinal (t.label σ) →
    steps_det_N t σ σ 0
  | trans :
    steps_det_N t σ_ σ' n →
    t.step σ = .some σ_ → 
    steps_det_N t σ σ' (n+1)

lemma steps_det_of_steps_det_N (t : Lts_det A lA) :
    steps_det_N t σ σ' N →
    steps_det t σ σ' := by
  intro h
  induction h
  case final => exact Relation.ReflTransGen.refl
  case trans σ_ σ' n σ hstep_det hstep ih =>
    exact Relation.ReflTransGen.head hstep ih

lemma steps_det_N_of_steps_det (t : Lts_det A lA) :
    steps_det t σ σ' →
    t.isFinal (t.label σ') →
    ∃ (n : Nat), steps_det_N t σ σ' n := by
  intro h hfinal
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, steps_det_N.final hfinal⟩
  | head hstep _ ih =>
      obtain ⟨n, ih⟩ := ih
      exact ⟨n + 1, steps_det_N.trans ih hstep⟩

def terminate_at (t : Lts_det A lA) (σ σ': A) : Prop :=
  steps_det t σ σ' ∧ t.isFinal (t.label σ')

lemma steps_det_N_of_terminate_at (t : Lts_det A lA) :
    terminate_at t σ σ' →
    ∃ (n : Nat), steps_det_N t σ σ' n := by
  rintro ⟨hsteps, hfinal⟩
  exact steps_det_N_of_steps_det t hsteps hfinal

def terminate (t : Lts_det A lA) (σ: A) : Prop :=
  ∃ σ', terminate_at t σ σ'


/- Definition of a nondeterministic
   labeled transition system -/
structure Lts_ndet (A : Type uA) (L : Type uLA) where
  /- function assigns label to every state -/
  label : A → L
  /- the lts step relation -/
  step : A → A → Prop
  /- Set of final states -/ 
  isFinal : L → Prop

  /-- Final states have no outgoing transition. -/
  hfinal : ∀ (f x : A), isFinal (label f) → ¬ step f x

def steps_ndet (t : Lts_ndet A lA) (σ σ' : A) : Prop :=
  Relation.ReflTransGen t.step σ σ'
   
def terminate_at_ndet (t : Lts_ndet A lA) (σ σ': A) : Prop :=
  steps_ndet t σ σ' ∧ t.isFinal (t.label σ')

/- A path is anchored at `start`; `steps` contains the label reached by each
  transition. Thus `[]` is the empty path, `[y]` is one step to `y`, and the
  endpoint is the last reached label (or `start` for the empty path). -/
structure Path L where
  start : L
  steps : List L

def Path.final (p : Path L) : L :=
  p.steps.getLastD p.start

namespace Lts

/-- Propositional path following for an arbitrary labelled transition relation. -/
def follow (label : A → L) (step : A → A → Prop)
    (init : A) : List L → A → Prop
  | [], final => final = init
  | nextLabel :: rest, final =>
      ∃ next, step init next ∧ label next = nextLabel ∧
        follow label step next rest final

/-- Mathematical path following for a deterministic transition system. -/
def follow_det_rel (t : Lts_det A L) (init : A) (labels : List L)
    (final : A) : Prop :=
  follow t.label (fun source target => t.step source = .some target)
    init labels final

def path_det_rel (t : Lts_det A L) (init : A) (p : Path L)
    (final : A) : Prop :=
  t.label init = p.start ∧ follow_det_rel t init p.steps final

/-- Executable deterministic path follower.  Decidable label equality is
    deliberately required here rather than by the mathematical LTS. -/
def follow_det [DecidableEq lA]
    (t : Lts_det A lA) (init : A) : List lA → Option A
  | [] => .some init
  | nextLabel :: rest => do
      let next ← t.step init
      if t.label next = nextLabel then
        follow_det t next rest
      else
        .none

/-- The executable follower implements the propositional path semantics. -/
theorem follow_det_eq_some_iff [DecidableEq lA]
    (t : Lts_det A lA) (init final : A) (labels : List lA) :
    follow_det t init labels = .some final ↔
      follow_det_rel t init labels final := by
  induction labels generalizing init with
  | nil => simp [follow_det, follow_det_rel, follow, eq_comm]
  | cons nextLabel rest ih =>
      simp only [follow_det, follow_det_rel, follow]
      cases hstep : t.step init with
      | none => simp
      | some next =>
          by_cases hlabel : t.label next = nextLabel
          · simp [hlabel, ih]
            rfl
          · simp [hlabel]

def path_det [DecidableEq lA] (t : Lts_det A lA) (init : A)
    (p : Path lA) : Option { σ // t.label σ = p.final } :=
  if t.label init = p.start then
    do
      let σ ← follow_det t init p.steps
      if h : t.label σ = p.final then .some ⟨σ, h⟩ else .none
  else .none

/-- Executable deterministic path checking is equivalent to the mathematical
    path relation whenever the endpoint label proof is supplied. -/
theorem path_det_eq_some_iff [DecidableEq lA]
    (t : Lts_det A lA) (init final : A) (p : Path lA)
    (hfinal : t.label final = p.final) :
    path_det t init p = .some ⟨final, hfinal⟩ ↔
      path_det_rel t init p final := by
  constructor
  · intro hexec
    unfold path_det at hexec
    by_cases hstart : t.label init = p.start
    · rw [if_pos hstart] at hexec
      cases hrun : follow_det t init p.steps with
      | none => simp [hrun] at hexec
      | some result =>
          by_cases hend : t.label result = p.final
          · simp [hrun, hend] at hexec
            have hresult : result = final := by simpa using hexec
            subst result
            exact ⟨hstart, (follow_det_eq_some_iff t init final p.steps).mp hrun⟩
          · simp [hrun, hend] at hexec
    · simp [hstart] at hexec
  · rintro ⟨hstart, hfollow⟩
    have hrun : follow_det t init p.steps = .some final :=
      (follow_det_eq_some_iff t init final p.steps).mpr hfollow
    simp [path_det, hstart, hrun, hfinal]

def follow_ndet (t : Lts_ndet A lA) (init : A)
    (labels : List lA) (final : A) : Prop :=
  follow t.label t.step init labels final

def path_ndet (t : Lts_ndet A lA) (init : A) (p : Path lA)
    (final : A) : Prop :=
  t.label init = p.start ∧ follow_ndet t init p.steps final
  
end Lts

/- Forward-simulation triple {φ₁} P; Q {φ₂}.
  If P can be followed from a pair of states satisfying φ₁, then there
  exists a matching execution of Q whose resulting state pair satisfies φ₂. -/
def forward_triple
  (LtsA : Lts_det A lA)
  (LtsB : Lts_ndet B lB)
  (phi1 : A → B → Prop)
  (P : Path lA)
  (Q : Path lB)
  (phi2 : A → B → Prop) :=
  ∀ σA σA' σB,
    LtsA.label σA = P.start → 
    LtsB.label σB = Q.start → 
    phi1 σA σB →
    Lts.path_det_rel LtsA σA P σA' →
    ∃ σB',
      Lts.path_ndet LtsB σB Q σB' ∧
      phi2 σA' σB'


/-- A mathematical path-pair automaton.  Nodes have their own identity, so
    distinct nodes may carry different invariants at the same location pair.
    Concrete certificate formats such as tree maps can be translated into
    this graph without becoming part of its refinement theory. -/
structure PAA (A : Type uA) (lA : Type uLA)
    (B : Type uB) (lB : Type uLB) where
    Node : Type uNode
    location : Node → lA × lB
    invariant : Node → A → B → Prop
    edge : Node → Node → Path lA → Path lB → Prop
    goal : A → B → Prop

def PAA.atNode
  (LtsA : Lts_det A lA)
  (LtsB : Lts_ndet B lB)
  (paa : PAA A lA B lB)
  (node : paa.Node) (σA : A) (σB : B) : Prop :=
  LtsA.label σA = (paa.location node).1 ∧
  LtsB.label σB = (paa.location node).2 ∧
  paa.invariant node σA σB

namespace PAA

/-- The directed node relation obtained by retaining exactly the PAA edges
    whose A path performs no transition. -/
def aEmptyEdge
    (paa : PAA A lA B lB) (source target : paa.Node) : Prop :=
  ∃ P Q, paa.edge source target P Q ∧ P.steps = []

/-- Well-foundedness of the A-empty-edge graph. `WellFounded` uses the
    predecessor-first orientation, hence the reversed arguments below. -/
def AEmptyWellFounded (paa : PAA A lA B lB) : Prop :=
  WellFounded (fun target source => paa.aEmptyEdge source target)

/-- A decreasing natural rank is an executable certificate for mathematical
    well-foundedness. -/
theorem aEmptyWellFounded_of_rank (paa : PAA A lA B lB)
    (rank : paa.Node → Nat)
    (hrank : ∀ {source target}, paa.aEmptyEdge source target →
      rank target < rank source) :
    paa.AEmptyWellFounded := by
  exact Subrelation.wf hrank (InvImage.wf rank Nat.lt_wfRel.2)

end PAA

/-- Mathematical validity conditions sufficient for PAA refinement.  Concrete
    certificate formats may impose additional decidable well-formedness
    conditions without strengthening this theorem-facing interface. -/
structure validPAA
  (LtsA : Lts_det A lA)
  (LtsB : Lts_ndet B lB)
  (paa : PAA A lA B lB) where
    edge_path_ok :
      ∀ {source target P Q}, paa.edge source target P Q →
        P.start = (paa.location source).1 ∧
        Q.start = (paa.location source).2 ∧
        P.final = (paa.location target).1 ∧
        Q.final = (paa.location target).2

    final_preserved : ∀ node,
      LtsA.isFinal (paa.location node).1 →
      LtsB.isFinal (paa.location node).2

    terminal_goal : ∀ node σA σB,
      paa.atNode LtsA LtsB node σA σB →
      LtsA.isFinal (LtsA.label σA) →
      paa.goal σA σB

    hyp1 :
      ∀ {source target P Q}, paa.edge source target P Q →
      forward_triple LtsA LtsB
        (paa.invariant source) P Q (paa.invariant target)

    /- The outgoing A-path conditions cover every related non-final state.
      The target-node witness makes the selected edge immediately usable by
      `hyp1`, whose forward triple constructs the matching B execution. -/
    hyp2A_coverage :
      ∀ source σA σB,
        paa.atNode LtsA LtsB source σA σB →
        ¬ LtsA.isFinal (LtsA.label σA) →
        ∃ (target : paa.Node) (P : Path lA) (Q : Path lB) (σA' : A),
          paa.edge source target P Q ∧
          Lts.path_det_rel LtsA σA P σA'

    aEmpty_wf : paa.AEmptyWellFounded

lemma steps_det_N_of_follow_det_rel
    (t : Lts_det A lA) :
    ∀ labels σ σ' σf n,
      Lts.follow_det_rel t σ labels σ' →
      steps_det_N t σ σf n →
      ∃ m, n = labels.length + m ∧ steps_det_N t σ' σf m := by
  intro labels
  induction labels with
  | nil =>
      intro σ σ' σf n hfollow hterm
      simp [Lts.follow_det_rel, Lts.follow] at hfollow
      subst σ'
      exact ⟨n, by simp, hterm⟩
  | cons nextLabel rest ih =>
      intro σ σ' σf n hfollow hterm
      obtain ⟨next, hstep, _, hfollow⟩ := hfollow
      cases hterm with
      | final hfinal =>
          have hnone := (t.hfinal σ).mp hfinal
          simp [hnone] at hstep
      | trans hrest hfirst =>
          have hnext : _ = next := Option.some.inj (hfirst.symm.trans hstep)
          subst_vars
          obtain ⟨m, hm, hsuffix⟩ := ih _ _ _ _ hfollow hrest
          exact ⟨m, by simp [hm, Nat.add_assoc, Nat.add_comm],
            hsuffix⟩

lemma steps_ndet_of_follow_ndet (t : Lts_ndet B lB) :
    ∀ labels σ σ',
      Lts.follow_ndet t σ labels σ' →
      steps_ndet t σ σ' := by
  intro labels
  induction labels with
  | nil =>
      intro σ σ' h
      simp [Lts.follow_ndet, Lts.follow] at h
      subst σ'
      exact Relation.ReflTransGen.refl
  | cons nextLabel rest ih =>
      intro σ σ' h
      obtain ⟨next, hstep, _, hrest⟩ := h
      exact Relation.ReflTransGen.head hstep (ih _ _ hrest)

lemma steps_ndet_of_path_ndet (t : Lts_ndet B lB) :
    Lts.path_ndet t σ P σ' → steps_ndet t σ σ' := by
  rintro ⟨_, hpath⟩
  exact steps_ndet_of_follow_ndet t _ _ _ hpath

lemma label_eq_getLastD_of_follow (label : A → L) (step : A → A → Prop) :
    ∀ labels σ σ', Lts.follow label step σ labels σ' →
      label σ' = labels.getLastD (label σ) := by
  intro labels
  induction labels with
  | nil =>
      intro σ σ' h
      simp [Lts.follow] at h
      subst σ'
      simp
  | cons nextLabel rest ih =>
      intro σ σ' h
      obtain ⟨next, _, hlabel, hrest⟩ := h
      have hfinal := ih next σ' hrest
      cases rest with
      | nil => simpa [Lts.follow, hlabel] using hfinal
      | cons head tail => simpa [hlabel] using hfinal

lemma label_eq_final_of_path_det_rel (t : Lts_det A lA)
    (hpath : Lts.path_det_rel t σ P σ') :
    t.label σ' = P.final := by
  obtain ⟨hstart, hfollow⟩ := hpath
  rw [Path.final,
    label_eq_getLastD_of_follow t.label
      (fun source target => t.step source = .some target) _ _ _ hfollow,
    hstart]

lemma label_eq_final_of_path_ndet (t : Lts_ndet B lB)
    (hpath : Lts.path_ndet t σ P σ') :
    t.label σ' = P.final := by
  obtain ⟨hstart, hfollow⟩ := hpath
  rw [Path.final,
    label_eq_getLastD_of_follow t.label t.step _ _ _ hfollow, hstart]

theorem paa_refinement
  (LtsA : Lts_det A lA)
  (LtsB : Lts_ndet B lB)
  (paa : PAA A lA B lB)
  (hpaa : validPAA LtsA LtsB paa)
  : ∀ (source : paa.Node) σA σA' σB,
  terminate_at LtsA σA σA' →
  paa.atNode LtsA LtsB source σA σB →
  ∃ σB',
    steps_ndet LtsB σB σB' ∧
    LtsB.isFinal (LtsB.label σB') ∧
    paa.goal σA' σB'
  := by
  have refinement_N :
      ∀ (n : Nat) (source : paa.Node) σA σAf σB,
        steps_det_N LtsA σA σAf n →
        paa.atNode LtsA LtsB source σA σB →
        ∃ σB', steps_ndet LtsB σB σB' ∧
          LtsB.isFinal (LtsB.label σB') ∧ paa.goal σAf σB' := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ihN =>
      intro source
      refine WellFounded.induction hpaa.aEmpty_wf
        (C := fun source => ∀ σA σAf σB,
          steps_det_N LtsA σA σAf n →
          paa.atNode LtsA LtsB source σA σB →
          ∃ σB', steps_ndet LtsB σB σB' ∧
            LtsB.isFinal (LtsB.label σB') ∧ paa.goal σAf σB')
        source ?_
      intro source ihEmpty σA σAf σB hterm hatSource
      obtain ⟨hlabelA, hlabelB, hinvariant⟩ := hatSource
      cases n with
      | zero =>
            cases hterm with
            | final hfinalA =>
                have hfinalLocA : LtsA.isFinal (paa.location source).1 := by
                  rw [← hlabelA]
                  exact hfinalA
                have hfinalLocB : LtsB.isFinal (paa.location source).2 :=
                  hpaa.final_preserved source hfinalLocA
                have hfinalB : LtsB.isFinal (LtsB.label σB) :=
                  by rw [hlabelB]; exact hfinalLocB
                exact ⟨σB, Relation.ReflTransGen.refl, hfinalB,
                  hpaa.terminal_goal source σA σB
                    ⟨hlabelA, hlabelB, hinvariant⟩ hfinalA⟩
      | succ n' =>
            have hnotFinalA : ¬ LtsA.isFinal (LtsA.label σA) := by
              intro hfinalA
              have hnone := (LtsA.hfinal σA).mp hfinalA
              cases hterm with
              | trans _ hfirst => simp [hnone] at hfirst
            have hatSource : paa.atNode LtsA LtsB source σA σB :=
              ⟨hlabelA, hlabelB, hinvariant⟩
            obtain ⟨target, P, Q, σAm, hedge, hpathA⟩ :=
              hpaa.hyp2A_coverage source σA σB hatSource hnotFinalA
            obtain ⟨hPstart, hQstart, hPfinal, hQfinal⟩ :=
              hpaa.edge_path_ok hedge
            have hforward := hpaa.hyp1 hedge
            obtain ⟨σBm, hpathB, hinvariant'⟩ :=
              hforward σA σAm σB
                (hlabelA.trans hPstart.symm)
                (hlabelB.trans hQstart.symm) hinvariant hpathA
            have hσAm : LtsA.label σAm = P.final :=
              label_eq_final_of_path_det_rel LtsA hpathA
            obtain ⟨m, hnm, htermSuffix⟩ :=
              steps_det_N_of_follow_det_rel LtsA P.steps σA σAm σAf (n' + 1)
                hpathA.2 hterm
            have hlabelBm : LtsB.label σBm = Q.final :=
              label_eq_final_of_path_ndet LtsB hpathB
            have hatTarget : paa.atNode LtsA LtsB target σAm σBm :=
              ⟨hσAm.trans hPfinal, hlabelBm.trans hQfinal, hinvariant'⟩
            have hstepsB : steps_ndet LtsB σB σBm :=
              steps_ndet_of_path_ndet LtsB hpathB
            match hempty : P.steps with
            | [] =>
              have hm : m = n' + 1 := by simpa [hempty] using hnm.symm
              obtain ⟨σBf, hstepsB', hfinalBf, hgoal⟩ :=
                ihEmpty target ⟨P, Q, hedge, hempty⟩ σAm σAf σBm
                  (by simpa [hm] using htermSuffix) hatTarget
              exact ⟨σBf, hstepsB.trans hstepsB', hfinalBf, hgoal⟩
            | P0 :: P' =>
              have hm : m < n' + 1 := by
                have hlen : 0 < P.steps.length := by simp [hempty]
                rw [hnm]
                exact Nat.lt_add_of_pos_left hlen
              obtain ⟨σBf, hstepsB', hfinalBf, hgoal⟩ :=
                ihN m hm target σAm σAf σBm
                  htermSuffix hatTarget
              exact ⟨σBf, hstepsB.trans hstepsB', hfinalBf, hgoal⟩
  intro source σA σAf σB htermA hatSource
  obtain ⟨n, htermN⟩ := steps_det_N_of_terminate_at LtsA htermA
  exact refinement_N n source σA σAf σB htermN hatSource
