import PAA.PAA

abbrev Cond A := A → Prop

def follow_det_cond [DecidableEq lA]
  (t : Lts_det A lA)
  (init : A)
  (P : List lA)
  (C : A → Prop) :=
  (∃ σ', Lts.follow_det t init P = some σ') ↔ C init

/-- Precondition obtained by taking one transition with the requested label
    and then establishing `C` at the reached state. -/
def CondAfterStep (t : Lts_det A lA) (nextLabel : lA)
    (C : Cond A) : Cond A := fun init =>
  ∃ next, t.step init = .some next ∧ t.label next = nextLabel ∧ C next

/-- Build a path-following condition one transition at a time. -/
theorem follow_det_cond.step [DecidableEq lA]
  (t : Lts_det A lA)
  (init : A)
  (P0 : lA)
  (P : List lA)
  (C : A → Prop)
  (hfollow : ∀ next, t.step init = .some next →
    t.label next = P0 → follow_det_cond t next P C) :
  follow_det_cond t init (P0 :: P) (CondAfterStep t P0 C) := by
  unfold follow_det_cond CondAfterStep
  constructor
  · rintro ⟨final, hpath⟩
    simp only [Lts.follow_det] at hpath
    cases hstep : t.step init with
    | none => simp [hstep] at hpath
    | some next =>
        by_cases hlabel : t.label next = P0
        · simp [hstep, hlabel] at hpath
          have hsuffix : C next :=
            (hfollow next hstep hlabel).mp ⟨final, hpath⟩
          exact ⟨next, rfl, hlabel, hsuffix⟩
        · simp [hstep, hlabel] at hpath
  · rintro ⟨next, hstep, hlabel, hsuffix⟩
    obtain ⟨final, hpath⟩ := (hfollow next hstep hlabel).mpr hsuffix
    exact ⟨final, by simp [Lts.follow_det, hstep, hlabel, hpath]⟩

def path_det_cond [DecidableEq lA]
  (t : Lts_det A lA)
  (init : A)
  (P : Path lA)
  (C : A → Prop) :=
  (∃ σ', Lts.path_det t init P = some σ') ↔ C init
