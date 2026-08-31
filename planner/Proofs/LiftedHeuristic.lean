/-
A heuristic proved at the lifted level, run at the ground level.

The planner searches packed bit sets, so admissibility has to be about the
function A* calls.  But nothing forces the *argument* to be about bit sets.  A
heuristic can be defined over atom-level states — predicates and objects, no fact
numbers anywhere — proved admissible there, and then shown to be what the
compiled version computes.

`admissibleOn_of_lifted` is that step, and it is the same for every domain.  What
a domain then owes is two things, both about itself and neither about grounding:

  * its lifted heuristic is goal-aware and consistent over the domain's schemas;
  * its compiled heuristic computes the lifted one on any state the search sees.

The second is an equality of two computations, not a semantic bridge.
-/
import Proofs.StepView

namespace Planner

open Planner.Pddl

/-- A heuristic on atom-level states. -/
abbrev LiftedH := AtomState → Nat

/-- Zero once the problem's goal atoms all hold. -/
def LiftedGoalAware (p : Problem) (h : LiftedH) : Prop :=
  ∀ σ : AtomState, (∀ a ∈ p.goal.toArray, σ a = true) → h σ = 0

/--
The triangle inequality over the operators the grounder produced, on the states an
invariant admits.  Domains that read a position off the state need the invariant;
those that do not can take `Inv := fun _ => True`.
-/
def LiftedConsistentOn (d : Domain) (p : Problem) (relevance : Bool)
    (Inv : AtomState → Prop) (h : LiftedH) : Prop :=
  ∀ o ∈ groundedOps d p relevance, ∀ σ : AtomState,
    Inv σ → o.applicableA σ → h σ ≤ o.cost + h (o.applyA σ)

/--
The compiled heuristic computes the lifted one wherever the search can look.
The invariant is available: a compiled table that reads a position off the state
is only faithful where the state has one.
-/
def ComputesOn (t : Task) (Inv : AtomState → Prop) (hv : State → Nat)
    (h : LiftedH) : Prop :=
  ∀ s σ, Abstracts t s σ → Inv σ → hv s = h σ

/-- The same with nothing assumed of the state. -/
abbrev Computes (t : Task) (hv : State → Nat) (h : LiftedH) : Prop :=
  ComputesOn t (fun _ => True) hv h

/-- `Reachable` survives every transition, so it is an invariant. -/
theorem reachable_invariant (t : Task) :
    ∀ s i s', State.WF t.numFacts s → Reachable t s → t.step s i s' → Reachable t s' :=
  fun _ i _ _ hr hstep => Reachable.step hr i hstep

/--
**A compiled heuristic that computes a goal-aware lifted one is goal-aware.**
-/
theorem goalAwareOn_of_lifted (d : Domain) (p : Problem) (relevance : Bool)
    (hwf : Task.WF (ground d p relevance))
    (hcost : ∀ o ∈ groundedOps d p relevance, 0 < o.cost)
    (hv : State → Nat) (h : LiftedH) (Inv : AtomState → Prop)
    (hcomp : ComputesOn (ground d p relevance) Inv hv h)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p relevance, ∀ σ, Inv σ → o.applicableA σ →
      Inv (o.applyA σ))
    (hga : LiftedGoalAware p h) :
    (ground d p relevance).GoalAwareOn (Reachable (ground d p relevance)) hv := by
  rintro s ⟨-, hreach⟩ hgoal
  obtain ⟨σ, habs, hinv⟩ :=
    reachable_abstracts_inv d p relevance hwf hcost Inv hinit hpres hreach
  rw [hcomp s σ habs hinv]
  refine hga σ ?_
  exact (assemble_isGoal (groundedOps d p relevance) p.goal.toArray p.init.toArray
    (allObjects d p).toArray d.name habs).mp hgoal

/--
**A compiled heuristic that computes a consistent lifted one is consistent.**

This is the property A\* really wants.  Consistency implies admissibility, and it
is what makes a closed list safe: a consistent heuristic never has to reopen a
node.  It is also what a heuristic can fail while staying admissible, which is why
it is stated on its own rather than only as a step towards `admissibleOn_of_lifted`.
-/
theorem consistentOn_of_lifted (d : Domain) (p : Problem) (relevance : Bool)
    (hwf : Task.WF (ground d p relevance))
    (hcost : ∀ o ∈ groundedOps d p relevance, 0 < o.cost)
    (hv : State → Nat) (h : LiftedH) (Inv : AtomState → Prop)
    (hcomp : ComputesOn (ground d p relevance) Inv hv h)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p relevance, ∀ σ, Inv σ → o.applicableA σ →
      Inv (o.applyA σ))
    (hcon : LiftedConsistentOn d p relevance Inv h) :
    (ground d p relevance).ConsistentOn (Reachable (ground d p relevance)) hv := by
  rintro s i s' ⟨-, hreach⟩ hstep
  obtain ⟨hi, happ, rfl⟩ := hstep
  obtain ⟨σ, habs, hinv⟩ :=
    reachable_abstracts_inv d p relevance hwf hcost Inv hinit hpres hreach
  -- the operator at `i`, before its facts were numbered
  have hops : (ground d p relevance).ops
      = (groundedOps d p relevance).map
        (numberOp (factIndex (allAtoms (groundedOps d p relevance)
          p.goal.toArray)).1) := rfl
  have hmem0 : (ground d p relevance).ops[i] ∈ (ground d p relevance).ops :=
    Array.getElem_mem hi
  set op := (ground d p relevance).ops[i] with hopdef
  have hmem : op ∈ (groundedOps d p relevance).map
      (numberOp (factIndex (allAtoms (groundedOps d p relevance)
        p.goal.toArray)).1) := by rw [← hops]; exact hmem0
  rw [Array.mem_map] at hmem
  obtain ⟨o, ho, hnum⟩ := hmem
  have habs' : Abstracts (ground d p relevance) (op.apply s) (o.applyA σ) := by
    rw [← hnum]
    exact assemble_apply (groundedOps d p relevance) p.goal.toArray p.init.toArray
      (allObjects d p).toArray d.name ho (hcost o ho) (hreach.wf hwf) habs
  have happA : o.applicableA σ :=
    (assemble_applicable (groundedOps d p relevance) p.goal.toArray p.init.toArray
      (allObjects d p).toArray d.name ho habs).mp (by rw [hnum]; exact happ)
  have hcost' : (ground d p relevance).model.actionCost i = o.cost := by
    show (ground d p relevance).actionCost i = o.cost
    unfold Task.actionCost
    rw [Array.getElem?_eq_getElem hi, ← hopdef, ← hnum]
    rfl
  rw [hcomp s σ habs hinv, hcomp _ _ habs' (hpres o ho σ hinv happA), hcost']
  exact hcon o ho σ hinv happA

/--
**A compiled heuristic that computes an admissible lifted one is admissible.**
Proved once; every domain uses it unchanged.
-/
theorem admissibleOn_of_lifted (d : Domain) (p : Problem) (relevance : Bool)
    (hwf : Task.WF (ground d p relevance))
    (hcost : ∀ o ∈ groundedOps d p relevance, 0 < o.cost)
    (hv : State → Nat) (h : LiftedH) (Inv : AtomState → Prop)
    (hcomp : ComputesOn (ground d p relevance) Inv hv h)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p relevance, ∀ σ, Inv σ → o.applicableA σ →
      Inv (o.applyA σ))
    (hga : LiftedGoalAware p h)
    (hcon : LiftedConsistentOn d p relevance Inv h) :
    (ground d p relevance).AdmissibleOn (Reachable (ground d p relevance)) hv :=
  (ground d p relevance).admissibleOn _ hv (reachable_invariant _)
    (goalAwareOn_of_lifted d p relevance hwf hcost hv h Inv hcomp hinit hpres hga)
    (consistentOn_of_lifted d p relevance hwf hcost hv h Inv hcomp hinit hpres hcon)


end Planner
