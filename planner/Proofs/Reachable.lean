/-
Every state the search can be in reads back as a set of ground atoms.

`Proofs/GroundingCorrect.lean` proves the two halves — the initial state is
abstracted, and applying an operator keeps it abstracted.  This file packages
them into the statement a heuristic proof actually wants: for any reachable
state there *is* an atom-level state it stands for.

With this and `Proofs/FactTables.lean`, nothing about grounding or the fact
numbering has to appear in a heuristic's proof again.  What is left there is the
heuristic's own reading of the task, which is where the domain belongs.
-/
import Proofs.FactTables

namespace Planner

open Planner.Pddl

/-- Reachable from the task's initial state by its own transitions. -/
inductive Reachable (t : Task) : State → Prop
  | init : Reachable t t.init
  | step {s s' : State} (h : Reachable t s) (i : Nat) (hstep : t.step s i s') :
      Reachable t s'

/-- A numbered task's fact count is the length of its name table. -/
@[simp] theorem ground_numFacts (d : Domain) (p : Problem) (relevance : Bool) :
    (ground d p relevance).numFacts = (ground d p relevance).factNames.size := rfl

theorem ground_init_wf (d : Domain) (p : Problem) (relevance : Bool)
    (hwf : Task.WF (ground d p relevance)) :
    State.WF (ground d p relevance).numFacts (ground d p relevance).init := hwf.init

/-- Reachable states are well formed. -/
theorem Reachable.wf {t : Task} (hwf : Task.WF t) {s : State} (h : Reachable t s) :
    State.WF t.numFacts s := by
  induction h with
  | init => exact hwf.init
  | step _ i hstep ih => exact t.invariant_wf _ i _ ih hstep

/--
**Every reachable state is an abstraction.**  The atom-level state it stands for
is built along the way: `:init` for the initial state, and the operator's own
atom-level update at each step.
-/
theorem reachable_abstracts (d : Domain) (p : Problem) (relevance : Bool)
    (hwf : Task.WF (ground d p relevance))
    (hcost : ∀ o ∈ groundedOps d p relevance, 0 < o.cost)
    {s : State} (h : Reachable (ground d p relevance) s) :
    ∃ σ, Abstracts (ground d p relevance) s σ := by
  induction h with
  | init =>
      exact ⟨_, assemble_init (groundedOps d p relevance) p.goal.toArray p.init.toArray
        (allObjects d p).toArray d.name⟩
  | @step s s' hreach i hstep ih =>
      obtain ⟨σ, habs⟩ := ih
      obtain ⟨hi, happ, rfl⟩ := hstep
      -- the operator at index `i` is one of the grounded operators, numbered
      have hops : (ground d p relevance).ops
          = (groundedOps d p relevance).map
            (numberOp (factIndex (allAtoms (groundedOps d p relevance)
              p.goal.toArray)).1) := rfl
      have hmem0 : (ground d p relevance).ops[i] ∈ (ground d p relevance).ops :=
        Array.getElem_mem hi
      set op := (ground d p relevance).ops[i] with hopdef
      have hmem : op ∈ (groundedOps d p relevance).map
          (numberOp (factIndex (allAtoms (groundedOps d p relevance)
            p.goal.toArray)).1) := by
        rw [← hops]; exact hmem0
      rw [Array.mem_map] at hmem
      obtain ⟨o, ho, hnum⟩ := hmem
      refine ⟨o.applyA σ, ?_⟩
      rw [← hnum]
      exact assemble_apply (groundedOps d p relevance) p.goal.toArray p.init.toArray
        (allObjects d p).toArray d.name ho (hcost o ho) (hreach.wf hwf) habs

/--
The same, carrying a lifted invariant: anything true of `:init` and preserved by
every operator's atom-level update holds of the state a reachable state stands
for.  Domains that read a position off the state — which floor the lift is on,
where a rover stands — need this.
-/
theorem reachable_abstracts_inv (d : Domain) (p : Problem) (relevance : Bool)
    (hwf : Task.WF (ground d p relevance))
    (hcost : ∀ o ∈ groundedOps d p relevance, 0 < o.cost)
    (Inv : AtomState → Prop)
    (hinit : Inv (fun a => p.init.toArray.contains a))
    (hpres : ∀ o ∈ groundedOps d p relevance, ∀ σ, Inv σ → o.applicableA σ →
      Inv (o.applyA σ))
    {s : State} (h : Reachable (ground d p relevance) s) :
    ∃ σ, Abstracts (ground d p relevance) s σ ∧ Inv σ := by
  induction h with
  | init =>
      exact ⟨_, assemble_init (groundedOps d p relevance) p.goal.toArray p.init.toArray
        (allObjects d p).toArray d.name, hinit⟩
  | @step s s' hreach i hstep ih =>
      obtain ⟨σ, habs, hinv⟩ := ih
      obtain ⟨hi, happ, rfl⟩ := hstep
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
      have happA : o.applicableA σ :=
        (assemble_applicable (groundedOps d p relevance) p.goal.toArray p.init.toArray
          (allObjects d p).toArray d.name ho habs).mp (by rw [hnum]; exact happ)
      refine ⟨o.applyA σ, ?_, hpres o ho σ hinv happA⟩
      rw [← hnum]
      exact assemble_apply (groundedOps d p relevance) p.goal.toArray p.init.toArray
        (allObjects d p).toArray d.name ho (hcost o ho) (hreach.wf hwf) habs

end Planner
