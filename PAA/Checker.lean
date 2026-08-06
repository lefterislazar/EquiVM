import PAA.PAA

/-! Executable certificate checkers for mathematical PAAs. -/

namespace PAA.Checker

/-- Check that a candidate rank strictly decreases along every selected edge
    between the supplied finite nodes.  An adjacency matrix can select the
    A-empty edges, or a safe over-approximation of them. -/
def checkDAGRank {N : Type*} (nodes : List N)
    (adjacent : N → N → Bool) (rank : N → Nat) : Bool :=
  nodes.all fun source =>
    nodes.all fun target =>
      decide (adjacent source target = true → rank target < rank source)

theorem checkDAGRank_sound {N : Type*}
    (nodes : List N) (adjacent : N → N → Bool) (rank : N → Nat)
    {source target : N}
    (hcheck : checkDAGRank nodes adjacent rank = true)
    (hsource : source ∈ nodes) (htarget : target ∈ nodes)
    (hedge : adjacent source target = true) :
    rank target < rank source := by
  have hsourceCheck := (List.all_eq_true.mp hcheck) source hsource
  have htargetCheck := (List.all_eq_true.mp hsourceCheck) target htarget
  exact (of_decide_eq_true htargetCheck) hedge

/-- Check a topological rank for a Boolean presentation of a PAA's A-empty
    edge graph. -/
def checkAEmptyDAG
    [Ord lA] [DecidableEq lA] [Ord lB]
    {LtsA : Lts_det A lA} {LtsB : Lts_ndet B lB}
    (paa : PAA LtsA LtsB)
    (nodes : List paa.Node)
    (aEmptyAdjacent : paa.Node → paa.Node → Bool)
    (rank : paa.Node → Nat) : Bool :=
  checkDAGRank nodes aEmptyAdjacent rank

/-- Soundness bridge from the executable rank checker to the unchanged
    `validPAA.hyp3A_rank` obligation.

    `hadjacent` only requires the Boolean graph to contain every actual A-empty
    PAA edge; it may conservatively contain additional edges. -/
theorem hyp3A_rank_of_checker
    [Ord lA] [DecidableEq lA] [Ord lB]
    {LtsA : Lts_det A lA} {LtsB : Lts_ndet B lB}
    (paa : PAA LtsA LtsB)
    (nodes : List paa.Node)
    (aEmptyAdjacent : paa.Node → paa.Node → Bool)
    (rank : paa.Node → Nat)
    (hnodes : ∀ node, node ∈ nodes)
    (hadjacent : ∀ {source target},
      paa.aEmptyEdge source target → aEmptyAdjacent source target = true)
    (hcheck : checkAEmptyDAG paa nodes aEmptyAdjacent rank = true) :
    ∃ checkedRank : paa.Node → Nat,
      ∀ {source target P Q}, paa.edge source target P Q →
        P.steps = [] → checkedRank target < checkedRank source := by
  refine ⟨rank, ?_⟩
  intro source target P Q hedge hempty
  apply checkDAGRank_sound nodes aEmptyAdjacent rank hcheck
  · exact hnodes source
  · exact hnodes target
  · exact hadjacent ⟨P, Q, hedge, hempty⟩

end PAA.Checker
