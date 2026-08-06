import PAA.PAA

abbrev Cond A := A → Prop

def CondAnd (P Q : Cond A) := fun s ↦ P s ∧ Q s

def follow_det_cond [Ord lA] [DecidableEq lA]
  (t : Lts_det A lA)
  (init : A)
  (P : List lA)
  (C : A → Prop) :=
  (∃ σ', Lts.follow_det t init P = some σ') ↔ C init

def follow_det_cond.step [Ord lA] [DecidableEq lA]
  (t : Lts_det A lA)
  (init : A)
  (P0 : lA)
  (P : List lA)
  (C0 C : A → Prop)
  :
  ((∃ σᵢ, t.step init = .some σᵢ ∧ t.label σᵢ = P0) ↔ C0 init) →
  follow_det_cond t σᵢ P C →
  follow_det_cond t init (P0 :: P) (CondAnd C0 C) := by
  intro hstep hfollow
  apply Iff.intro
  · intro ⟨σ', hfollow'⟩
    simp [Lts.follow_det, bind, Option.bind] at hfollow'
    cases hstep_option : (t.step init)
    · simp [hstep_option] at hfollow'
    · simp [hstep_option] at hfollow'
      rename_i σᵢ
      simp [CondAnd]
      apply And.intro
      · _
      · simp [follow_det_cond] at hfollow
  · _

def path_det_cond [Ord lA] [DecidableEq lA]
  (t : Lts_det A lA)
  (init : A)
  (P : Path lA)
  (C : A → Prop) :=
  (∃ σ', Lts.path_det t init P = some σ') ↔ C init

