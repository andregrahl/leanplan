/-
Goal awareness, consistency and admissibility.

The three properties are stated relative to a state invariant `P`.  The planner
only ever evaluates a heuristic on states reachable from the initial one, and
those are exactly the well-formed states, so requiring a heuristic to behave on
arbitrary bit patterns would be both harder and pointless.  `Invariant` records
that `P` survives every transition, which is what the induction needs.
-/
import Proofs.Task

namespace Planner

variable {S A : Type}

/-- `P` is preserved by every transition of `m`. -/
def Invariant (m : PlanningModel S A) (P : S → Prop) : Prop :=
  ∀ s a s', P s → m.transition s a s' → P s'

/-- A goal-aware heuristic is zero on every valid goal state. -/
def GoalAware (m : PlanningModel S A) (P : S → Prop) (h : S → Nat) : Prop :=
  ∀ s, P s → m.isGoal s → h s = 0

/-- A consistent heuristic satisfies the triangle inequality on every transition. -/
def Consistent (m : PlanningModel S A) (P : S → Prop) (h : S → Nat) : Prop :=
  ∀ s a s', P s → m.transition s a s' → h s ≤ m.actionCost a + h s'

/-- An admissible heuristic never overestimates the cost of reaching the goal. -/
def Admissible (m : PlanningModel S A) (P : S → Prop) (h : S → Nat) : Prop :=
  ∀ s plan final, P s → Executes m s plan final → m.isGoal final → h s ≤ planCost m plan

/--
The bridge every domain heuristic uses: proving goal awareness and consistency —
two local, per-action checks — yields admissibility, a global statement about
every plan.  The induction follows the execution of the plan.
-/
theorem admissible_of_goalAware_consistent (m : PlanningModel S A) (P : S → Prop)
    (hP : Invariant m P) (h : S → Nat)
    (goalAware : GoalAware m P h) (consistent : Consistent m P h) :
    Admissible m P h := by
  intro s plan final hs hexec hgoal
  induction hexec with
  | nil s => simpa [planCost] using goalAware s hs hgoal
  | @cons s mid final a rest hstep _ ih =>
      have hmid : P mid := hP s a mid hs hstep
      have hfirst : h s ≤ m.actionCost a + h mid := consistent s a mid hs hstep
      have hrest : h mid ≤ planCost m rest := ih hmid hgoal
      simpa [planCost] using Nat.le_trans hfirst (Nat.add_le_add_left hrest _)

/-- Well-formedness is a transition invariant of a grounded task. -/
theorem Task.invariant_wf (t : Task) : Invariant t.model (State.WF t.numFacts) := by
  rintro s i s' hs ⟨_, _, rfl⟩
  exact Op.wf_apply _ hs

/-- The heuristic properties a grounded task's heuristic is required to have. -/
abbrev Task.GoalAware (t : Task) (h : State → Nat) : Prop :=
  Planner.GoalAware t.model (State.WF t.numFacts) h

abbrev Task.Consistent (t : Task) (h : State → Nat) : Prop :=
  Planner.Consistent t.model (State.WF t.numFacts) h

abbrev Task.Admissible (t : Task) (h : State → Nat) : Prop :=
  Planner.Admissible t.model (State.WF t.numFacts) h

theorem Task.admissible (t : Task) (h : State → Nat)
    (ga : t.GoalAware h) (con : t.Consistent h) : t.Admissible h :=
  admissible_of_goalAware_consistent _ _ t.invariant_wf h ga con

/-! ### Properties relative to an extra invariant

Well-formedness is not always enough.  Several of the strong heuristics read a
position off the state — which floor the lift is on, where the man is standing —
and are only correct when exactly one such fact holds.  That is true of every
state the search can reach, but not of every well-formed state, so those
heuristics are proved correct relative to an extra invariant `Q`, which the
planner checks of the initial state when it loads the task.

`astar_optimal` takes the invariant as a parameter, so a heuristic proved this way
plugs into the optimality theorem unchanged.
-/

/-- Well-formed, and satisfying the extra invariant `Q`. -/
abbrev Task.Reach (t : Task) (Q : State → Prop) (s : State) : Prop :=
  State.WF t.numFacts s ∧ Q s

abbrev Task.GoalAwareOn (t : Task) (Q : State → Prop) (h : State → Nat) : Prop :=
  Planner.GoalAware t.model (t.Reach Q) h

abbrev Task.ConsistentOn (t : Task) (Q : State → Prop) (h : State → Nat) : Prop :=
  Planner.Consistent t.model (t.Reach Q) h

abbrev Task.AdmissibleOn (t : Task) (Q : State → Prop) (h : State → Nat) : Prop :=
  Planner.Admissible t.model (t.Reach Q) h

/-- `Q` is preserved by every transition out of a well-formed state satisfying it. -/
theorem Task.invariant_reach (t : Task) (Q : State → Prop)
    (hQ : ∀ s i s', State.WF t.numFacts s → Q s → t.step s i s' → Q s') :
    Invariant t.model (t.Reach Q) := by
  rintro s i s' ⟨hs, hq⟩ hstep
  exact ⟨t.invariant_wf s i s' hs hstep, hQ s i s' hs hq hstep⟩

theorem Task.admissibleOn (t : Task) (Q : State → Prop) (h : State → Nat)
    (hQ : ∀ s i s', State.WF t.numFacts s → Q s → t.step s i s' → Q s')
    (ga : t.GoalAwareOn Q h) (con : t.ConsistentOn Q h) : t.AdmissibleOn Q h :=
  admissible_of_goalAware_consistent _ _ (t.invariant_reach Q hQ) h ga con

end Planner
