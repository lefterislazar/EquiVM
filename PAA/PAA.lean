import Ethereum.Semantics
import Ethereum.Theory.ProgressLemmas

/- Definition of a deternimistic
   labeled transition system -/
structure Lts_det (A L) [Ord L] [DecidableEq L] where
  /- function assigns label to every state -/
  label : A → L
  /- the deterministc lts step -/
  step : A → Option A
  -- /- Set of final states -/ 
  isFinal : L → Prop

  hfinal : ∀ (f : A), isFinal (label f) ↔ step f = .none
    -- TODO: what about exceptions?

  -- TODO: do I need this?
  hfinal_exists : ∃ σ, isFinal (label σ)


def steps_det [Ord lA] [DecidableEq lA] (t : Lts_det A lA) (σ σ' : A) : Prop :=
  Relation.ReflTransGen (λ σ σ' ↦ t.step σ = .some σ') σ σ'

inductive steps_det_N [Ord lA] [DecidableEq lA] (t : Lts_det A lA) : A → A → ℕ → Prop where
  | final :
    t.isFinal (t.label σ) →
    steps_det_N t σ σ 0
  | trans :
    steps_det_N t σ_ σ' n →
    t.step σ = .some σ_ → 
    steps_det_N t σ σ' (n+1)

lemma steps_det_of_steps_det_N [Ord lA] [DecidableEq lA] (t : Lts_det A lA) :
    steps_det_N t σ σ' N →
    steps_det t σ σ' := by
  intro h
  induction h
  case final σ _ => simp [steps_det]; grind
  case trans σ_ σ' n σ hstep_det hstep ih =>
    exact Relation.ReflTransGen.head hstep ih

lemma steps_det_N_of_steps_det [Ord lA] [DecidableEq lA] (t : Lts_det A lA) :
    steps_det t σ σ' →
    t.isFinal (t.label σ') →
    ∃ n, steps_det_N t σ σ' n := by
  intro h hfinal
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, steps_det_N.final hfinal⟩
  | head hstep _ ih =>
      obtain ⟨n, ih⟩ := ih
      exact ⟨n + 1, steps_det_N.trans ih hstep⟩

def terminate_at [Ord lA] [DecidableEq lA] (t : Lts_det A lA) (σ σ': A) : Prop :=
  steps_det t σ σ' ∧ t.isFinal (t.label σ')

lemma steps_det_N_of_terminate_at [Ord lA] [DecidableEq lA] (t : Lts_det A lA) :
    terminate_at t σ σ' →
    ∃ n, steps_det_N t σ σ' n := by
  rintro ⟨hsteps, hfinal⟩
  exact steps_det_N_of_steps_det t hsteps hfinal

def terminate [Ord lA] [DecidableEq lA] (t : Lts_det A lA) (σ: A) : Prop :=
  ∃ σ', terminate_at t σ σ'


/- Definition of a non-deternimistic
   labeled transition system -/
structure Lts_ndet (A L) [Ord L] where
  /- function assigns label to every state -/
  label : A → L
  /- the lts step relation -/
  step : A → A → Prop
  /- Set of final states -/ 
  isFinal : L → Prop

  hfinal : ∀ (f x : A), isFinal (label f) → ¬ step f x
    -- TODO: what about exceptions?

  -- TODO: do I need this?
  hfinal_exists : ∃ σ, isFinal (label σ)


def steps_ndet [Ord lA] (t : Lts_ndet A lA) (σ σ' : A) : Prop :=
  Relation.ReflTransGen t.step σ σ'
   
def terminate_at_ndet [Ord lA] (t : Lts_ndet A lA) (σ σ': A) : Prop :=
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

def follow_det [Ord lA] [DecidableEq lA]
    (t : Lts_det A lA) (init : A) : List lA → Option A
  | [] => .some init
  | nextLabel :: rest => do
      let next ← t.step init
      if t.label next = nextLabel then
        follow_det t next rest
      else
        .none

def path_det [Ord lA] [DecidableEq lA] (t : Lts_det A lA) (init : A) (p : Path lA) : Option { σ // t.label σ = p.final } :=
  if t.label init = p.start then
    do
      let σ ← follow_det t init p.steps
      if h : t.label σ = p.final then .some ⟨σ, h⟩ else .none
  else .none

def follow_ndet [Ord lA]
    (t : Lts_ndet A lA) (init : A) : List lA → A → Prop
  | [], final => final = init
  | nextLabel :: rest, final =>
      ∃ next, t.step init next ∧ t.label next = nextLabel ∧
        follow_ndet t next rest final

def path_ndet [Ord lA] (t : Lts_ndet A lA) (init : A) (p : Path lA) (final : A) : Prop :=
  t.label init = p.start ∧ follow_ndet t init p.steps final
  
end Lts

/- Forward-simulation triple {φ₁} P; Q {φ₂}.
  If P can be followed from a pair of states satisfying φ₁, then there
  exists a matching execution of Q whose resulting state pair satisfies φ₂. -/
def forward_triple {A lA B lB} [Ord lA] [DecidableEq lA] [Ord lB] --[DecidableEq lB]
  (LtsA : Lts_det A lA)
  (LtsB : Lts_ndet B lB)
  (phi1 : A → B → Prop)
  (P : Path lA)
  (Q : Path lB)
  (phi2 : A → B → Prop) :=
  ∀ σA σA' σB hσA,
    LtsA.label σA = P.start → 
    LtsB.label σB = Q.start → 
    phi1 σA σB →
    Lts.path_det LtsA σA P = Option.some ⟨σA',hσA⟩ →
    ∃ σB',
      Lts.path_ndet LtsB σB Q σB' ∧
      phi2 σA' σB'


/-- A mathematical path-pair automaton.  Nodes have their own identity, so
    distinct nodes may carry different invariants at the same location pair.
    Concrete certificate formats such as tree maps can be translated into
    this finite graph without becoming part of its refinement theory. -/
structure PAA
  {A lA B lB: Type u_1} [Ord lA] [DecidableEq lA] [Ord lB] --[DecidableEq lB]
  (LtsA : Lts_det A lA)
  (LtsB : Lts_ndet B lB)
  where
    Node : Type u_1
    [nodeFintype : Fintype Node]
    location : Node → lA × lB
    invariant : Node → A → B → Prop
    edge : Node → Node → Path lA → Path lB → Prop
    goal : A → B → Prop

def PAA.atNode
    [Ord lA] [DecidableEq lA] [Ord lB]
  (LtsA : Lts_det A lA)
  (LtsB : Lts_ndet B lB)
  (paa : PAA LtsA LtsB)
  (node : paa.Node) (σA : A) (σB : B) : Prop :=
  LtsA.label σA = (paa.location node).1 ∧
  LtsB.label σB = (paa.location node).2 ∧
  paa.invariant node σA σB

def pathToList (P : Path A) : List A :=
  P.start :: P.steps

def pathPrefix (P : Path A) (Q : Path A) : Prop :=
  P.start = Q.start ∧ P.steps <+: Q.steps

structure validPAA
    [Ord lA] [DecidableEq lA]
    [Ord lB] --[DecidableEq lB]
  (LtsA : Lts_det A lA)
  (LtsB : Lts_ndet B lB)
  (paa : PAA LtsA LtsB) where
    edge_path_ok :
      ∀ {source target P Q}, paa.edge source target P Q →
        P.start = (paa.location source).1 ∧
        Q.start = (paa.location source).2 ∧
        P.final = (paa.location target).1 ∧
        Q.final = (paa.location target).2

    edge_nonempty :
      ∀ {source target P Q}, paa.edge source target P Q →
        P.steps ≠ [] ∨ Q.steps ≠ []

    hfinal : ∀ node,
      LtsA.isFinal (paa.location node).1 ↔
      LtsB.isFinal (paa.location node).2

    hfinal_goal : ∀ node,
      LtsA.isFinal (paa.location node).1 →
      LtsB.isFinal (paa.location node).2 →
      paa.invariant node = paa.goal

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
        ∃ (target : paa.Node) (P : Path lA) (Q : Path lB) (σA' : A)
            (hσA' : LtsA.label σA' = P.final),
          paa.edge source target P Q ∧
          Lts.path_det LtsA σA P = .some ⟨σA', hσA'⟩

    hyp3A_rank : ∃ rank : paa.Node → Nat,
      ∀ {source target P Q}, paa.edge source target P Q →
        P.steps = [] →
        rank target < rank source

lemma steps_det_N_of_follow_det [Ord lA] [DecidableEq lA]
    (t : Lts_det A lA) :
    ∀ labels σ σ' σf n,
      Lts.follow_det t σ labels = .some σ' →
      steps_det_N t σ σf n →
      ∃ m, n = labels.length + m ∧ steps_det_N t σ' σf m := by
  intro labels
  induction labels with
  | nil =>
      intro σ σ' σf n hfollow hterm
      simp [Lts.follow_det] at hfollow
      subst σ'
      exact ⟨n, by simp, hterm⟩
  | cons nextLabel rest ih =>
      intro σ σ' σf n hfollow hterm
      simp only [Lts.follow_det] at hfollow
      cases hstep : t.step σ with
      | none => simp [hstep] at hfollow
      | some next =>
        cases hlabel : t.label next == nextLabel
        · apply of_decide_eq_false at hlabel
          simp [hstep, hlabel] at hfollow
        · apply of_decide_eq_true at hlabel
          simp [hstep, hlabel] at hfollow
          cases hterm with
          | final hfinal =>
              have := (t.hfinal σ).mp hfinal
              simp [this] at hstep
          | trans hrest hfirst =>
              have hnext : _ = next := Option.some.inj (hfirst.symm.trans hstep)
              subst_vars
              obtain ⟨m, hm, hsuffix⟩ := ih _ _ _ _ hfollow hrest
              exact ⟨m, by simp only [List.length_cons]; omega, hsuffix⟩

lemma steps_ndet_of_follow_ndet [Ord lB] (t : Lts_ndet B lB) :
    ∀ labels σ σ',
      Lts.follow_ndet t σ labels σ' →
      steps_ndet t σ σ' := by
  intro labels
  induction labels with
  | nil =>
      intro σ σ' h
      simp [Lts.follow_ndet] at h
      subst σ'
      exact Relation.ReflTransGen.refl
  | cons nextLabel rest ih =>
      intro σ σ' h
      obtain ⟨next, hstep, _, hrest⟩ := h
      exact Relation.ReflTransGen.head hstep (ih _ _ hrest)

lemma steps_ndet_of_path_ndet [Ord lB] (t : Lts_ndet B lB) :
    Lts.path_ndet t σ P σ' → steps_ndet t σ σ' := by
  rintro ⟨_, hpath⟩
  exact steps_ndet_of_follow_ndet t _ _ _ hpath

lemma follow_det_of_path_det [Ord lA] [DecidableEq lA]
    (t : Lts_det A lA)
    (hσ' : t.label σ' = P.final)
    (hpath : Lts.path_det t σ P = .some ⟨σ', hσ'⟩) :
    Lts.follow_det t σ P.steps = .some σ' := by
  unfold Lts.path_det at hpath
  split at hpath
  · rename_i hstart
    cases hfollow : Lts.follow_det t σ P.steps with
    | none => simp [hfollow] at hpath
    | some result =>
        cases hfinal : t.label result == P.final
        · apply of_decide_eq_false at hfinal
          simp [hfollow, hfinal] at hpath
        · apply of_decide_eq_true at hfinal
          simp [hfollow, hfinal] at hpath
          have hresult : result = σ' := by simpa using hpath
          exact congrArg some hresult
  · simp at hpath

lemma label_eq_final_of_follow_ndet [Ord lB] (t : Lts_ndet B lB) :
    ∀ labels σ σ',
      Lts.follow_ndet t σ labels σ' →
      t.label σ' = labels.getLastD (t.label σ) := by
  intro labels
  induction labels with
  | nil =>
      intro σ σ' h
      simp [Lts.follow_ndet] at h
      subst σ'
      simp
  | cons nextLabel rest ih =>
      intro σ σ' h
      obtain ⟨next, _, hlabel, hrest⟩ := h
      have hfinal := ih next σ' hrest
      cases rest with
      | nil => simpa [Lts.follow_ndet, hlabel] using hfinal
      | cons head tail => simpa [hlabel] using hfinal

lemma label_eq_final_of_path_ndet [Ord lB] (t : Lts_ndet B lB)
    (hpath : Lts.path_ndet t σ P σ') :
    t.label σ' = P.final := by
  obtain ⟨hstart, hfollow⟩ := hpath
  rw [Path.final, label_eq_final_of_follow_ndet t _ _ _ hfollow, hstart]

theorem paa_refinement
  [Ord lA] [DecidableEq lA] [Ord lB]
  (LtsA : Lts_det A lA)
  (LtsB : Lts_ndet B lB)
  (paa : PAA LtsA LtsB)
  (hpaa : validPAA LtsA LtsB paa)
  : ∀ (source : paa.Node) σA σA' σB,
  terminate_at LtsA σA σA' →
  paa.atNode LtsA LtsB source σA σB →
  ∃ σB',
    steps_ndet LtsB σB σB' ∧
    LtsB.isFinal (LtsB.label σB') ∧
    paa.goal σA' σB'
  := by
  obtain ⟨rank, hrank⟩ := hpaa.hyp3A_rank
  have refinement_N :
      ∀ n r (source : paa.Node) σA σAf σB,
        rank source = r →
        steps_det_N LtsA σA σAf n →
        paa.atNode LtsA LtsB source σA σB →
        ∃ σB', steps_ndet LtsB σB σB' ∧
          LtsB.isFinal (LtsB.label σB') ∧ paa.goal σAf σB' := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ihN =>
      intro r
      induction r using Nat.strong_induction_on with
      | h r ihR =>
        intro source σA σAf σB hrEq hterm hatSource
        obtain ⟨hlabelA, hlabelB, hinvariant⟩ := hatSource
        cases n with
        | zero =>
            cases hterm with
            | final hfinalA =>
                have hfinalLocA : LtsA.isFinal (paa.location source).1 := by
                  rw [← hlabelA]
                  exact hfinalA
                have hfinalLocB : LtsB.isFinal (paa.location source).2 :=
                  (hpaa.hfinal source).mp hfinalLocA
                have hfinalB : LtsB.isFinal (LtsB.label σB) :=
                  by rw [hlabelB]; exact hfinalLocB
                have hinvariantGoal : paa.invariant source = paa.goal :=
                  hpaa.hfinal_goal source hfinalLocA hfinalLocB
                exact ⟨σB, Relation.ReflTransGen.refl, hfinalB,
                  by simpa [hinvariantGoal] using hinvariant⟩
        | succ n' =>
            have hnotFinalA : ¬ LtsA.isFinal (LtsA.label σA) := by
              intro hfinalA
              have hnone := (LtsA.hfinal σA).mp hfinalA
              cases hterm with
              | trans _ hfirst => simp [hnone] at hfirst
            have hatSource : paa.atNode LtsA LtsB source σA σB :=
              ⟨hlabelA, hlabelB, hinvariant⟩
            obtain ⟨target, P, Q, σAm, hσAm, hedge, hpathA⟩ :=
              hpaa.hyp2A_coverage source σA σB hatSource hnotFinalA
            obtain ⟨hPstart, hQstart, hPfinal, hQfinal⟩ :=
              hpaa.edge_path_ok hedge
            have hforward := hpaa.hyp1 hedge
            obtain ⟨σBm, hpathB, hinvariant'⟩ :=
              hforward σA σAm σB hσAm
                (hlabelA.trans hPstart.symm)
                (hlabelB.trans hQstart.symm) hinvariant hpathA
            have hfollowA := follow_det_of_path_det LtsA hσAm hpathA
            obtain ⟨m, hnm, htermSuffix⟩ :=
              steps_det_N_of_follow_det LtsA P.steps σA σAm σAf (n' + 1)
                hfollowA hterm
            have hlabelBm : LtsB.label σBm = Q.final :=
              label_eq_final_of_path_ndet LtsB hpathB
            have hatTarget : paa.atNode LtsA LtsB target σAm σBm :=
              ⟨hσAm.trans hPfinal, hlabelBm.trans hQfinal, hinvariant'⟩
            have hstepsB : steps_ndet LtsB σB σBm :=
              steps_ndet_of_path_ndet LtsB hpathB
            match hempty : P.steps with
            | [] =>
              have hm : m = n' + 1 := by simp [hempty] at hnm; omega
              have hmeasure : rank target < r := by
                rw [← hrEq]
                exact hrank hedge hempty
              obtain ⟨σBf, hstepsB', hfinalBf, hgoal⟩ :=
                ihR _ hmeasure target σAm σAf σBm rfl
                  (by simpa [hm] using htermSuffix) hatTarget
              exact ⟨σBf, hstepsB.trans hstepsB', hfinalBf, hgoal⟩
            | P0 :: P' =>
              have hm : m < n' + 1 := by
                cases hsteps : P.steps with
                | nil => rw [hempty] at hsteps; contradiction
                | cons head tail => simp [hsteps] at hnm; omega
              obtain ⟨σBf, hstepsB', hfinalBf, hgoal⟩ :=
                ihN m hm (rank target) target σAm σAf σBm rfl
                  htermSuffix hatTarget
              exact ⟨σBf, hstepsB.trans hstepsB', hfinalBf, hgoal⟩
  intro source σA σAf σB htermA hatSource
  obtain ⟨n, htermN⟩ := steps_det_N_of_terminate_at LtsA htermA
  exact refinement_N n (rank source) source σA σAf σB rfl htermN hatSource
