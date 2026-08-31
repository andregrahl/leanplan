/-
The blind heuristic is goal-aware, consistent, and therefore admissible.

`blind` is zero on goal states and the cheapest action cost elsewhere.  Since
every operator of a well-formed task costs at least one, that cheapest cost is
one, and consistency is the observation that a single action never buys more than
its own cost.

This is the heuristic the `leanplan-blind` configuration of the experiment runs,
so it is worth having on the same footing as the domain-dependent ones.
-/
import Proofs.Combinators
import Planner.ExampleHeuristics.Blind

namespace Planner

/-- Folding `min` from `1` never rises above `1`. -/
private theorem minActionCost_le_one (t : Task) : minActionCost t ≤ 1 := by
  simp only [minActionCost, ← Array.foldl_toList]
  have : ∀ (l : List Op) (a : Nat), l.foldl (fun acc op => min acc op.cost) a ≤ a := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons op rest ih =>
        intro a
        exact Nat.le_trans (ih (min a op.cost)) (Nat.min_le_left _ _)
  exact this _ 1

theorem blind_goalAware (t : Task) : t.GoalAware (blind t).eval := by
  intro s _ hgoal
  have h : t.isGoal s = true := hgoal
  simp [blind, h]

theorem blind_consistent (t : Task) (hwf : Task.WF t) : t.Consistent (blind t).eval := by
  refine t.consistent_of_ops _ ?_
  intro op hop s _ _
  have hcost : 1 ≤ op.cost := (hwf.ops op hop).cost
  have hmin : minActionCost t ≤ 1 := minActionCost_le_one t
  simp only [blind]
  split
  · exact Nat.zero_le _
  · split <;> omega

/-- Never overestimates the cost of reaching the goal. -/
theorem blind_admissible (t : Task) (hwf : Task.WF t) : t.Admissible (blind t).eval :=
  t.admissible _ (blind_goalAware t) (blind_consistent t hwf)

end Planner
