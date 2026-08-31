/-
The simple heuristics, lifted.

All ten *simple* heuristics are the same function: the largest, over families of
goal atoms, of the count still unmet.  Lifted, that is a function of the problem's
goal and the atom-level state, with no fact numbers in it.

Everything here is domain-independent.  A domain supplies only its list of
predicate families and the fact that no schema of it adds two atoms of one family.
-/
import Proofs.LiftedHeuristic
import Proofs.SchemaSupport

namespace Planner.Lifted

open Planner Planner.Pddl

/-- How many of a family's goal atoms are still unmet. -/
def missingL (fam : List GroundAtom) (σ : AtomState) : Nat :=
  (fam.filter fun a => !σ a).length

/-- The largest such count. -/
def maxMissingL (families : List (List GroundAtom)) (σ : AtomState) : Nat :=
  (families.map fun fam => missingL fam σ).foldl max 0

@[simp] theorem maxMissingL_nil (σ : AtomState) : maxMissingL [] σ = 0 := rfl

private theorem foldl_max_init (l : List Nat) :
    ∀ b : Nat, l.foldl max b = max b (l.foldl max 0) := by
  induction l with
  | nil => intro b; simp
  | cons a rest ih =>
      intro b
      rw [List.foldl_cons, ih (max b a), List.foldl_cons, ih (max 0 a)]
      simp [Nat.max_assoc]

theorem maxMissingL_cons (fam : List GroundAtom) (rest : List (List GroundAtom))
    (σ : AtomState) :
    maxMissingL (fam :: rest) σ = max (missingL fam σ) (maxMissingL rest σ) := by
  simp only [maxMissingL, List.map_cons, List.foldl_cons, Nat.zero_max]
  exact foldl_max_init _ _

/-! ### Goal awareness -/

theorem missingL_eq_zero {fam : List GroundAtom} {σ : AtomState}
    (h : ∀ a ∈ fam, σ a = true) : missingL fam σ = 0 := by
  unfold missingL
  simp only [List.length_eq_zero_iff]
  refine List.filter_eq_nil_iff.mpr ?_
  intro a ha
  simp [h a ha]

theorem maxMissingL_eq_zero {families : List (List GroundAtom)} {σ : AtomState}
    (h : ∀ fam ∈ families, ∀ a ∈ fam, σ a = true) : maxMissingL families σ = 0 := by
  induction families with
  | nil => rfl
  | cons fam rest ih =>
      rw [maxMissingL_cons, missingL_eq_zero (h fam (by simp)),
        ih fun f hf => h f (by simp [hf])]
      rfl

theorem liftedGoalAware_maxMissing (p : Problem) (families : List (List GroundAtom))
    (hsub : ∀ fam ∈ families, ∀ a ∈ fam, a ∈ p.goal) :
    LiftedGoalAware p (maxMissingL families) := by
  intro σ hgoal
  refine maxMissingL_eq_zero fun fam hfam a ha => ?_
  exact hgoal a (by simpa using hsub fam hfam a ha)

/-! ### Consistency

A family is *safe* for an operator when the operator adds at most one of its
atoms and deletes none.  That is all consistency needs, and it is a statement
about the domain's schemas.
-/

/-- The operator adds at most one atom of the family and deletes none. -/
def FamilySafeL (fam : List GroundAtom) (o : AtomOp) : Prop :=
  (∃ x : GroundAtom, ∀ a ∈ fam, a ≠ x → a ∉ o.add) ∧ ∀ a ∈ fam, a ∉ o.del

theorem missingL_le_succ {fam : List GroundAtom} {o : AtomOp} {σ : AtomState}
    (hnd : fam.Nodup) (hsafe : FamilySafeL fam o) :
    missingL fam σ ≤ missingL fam (o.applyA σ) + 1 := by
  obtain ⟨⟨x, hone⟩, hdel⟩ := hsafe
  unfold missingL
  refine length_le_succ_of_subset' _ _ x (hnd.filter _) ?_
  intro y hy
  rw [List.mem_filter] at hy
  obtain ⟨hmem, hval⟩ := hy
  by_cases hyx : y = x
  · exact Or.inr hyx
  · refine Or.inl ?_
    rw [List.mem_filter]
    refine ⟨hmem, ?_⟩
    rw [applyA_frame σ (hone y hmem hyx) (hdel y hmem)]
    exact hval

theorem maxMissingL_le_succ {families : List (List GroundAtom)} {o : AtomOp}
    {σ : AtomState} (hnd : ∀ fam ∈ families, fam.Nodup)
    (hsafe : ∀ fam ∈ families, FamilySafeL fam o) :
    maxMissingL families σ ≤ maxMissingL families (o.applyA σ) + 1 := by
  induction families with
  | nil => simp
  | cons fam rest ih =>
      have hone := missingL_le_succ (hnd fam (by simp)) (hsafe fam (by simp))
        (σ := σ)
      have hrest := ih (fun f hf => hnd f (by simp [hf]))
        (fun f hf => hsafe f (by simp [hf]))
      rw [maxMissingL_cons, maxMissingL_cons]
      omega

/-- Consistency, from one fact about the domain's schemas. -/
theorem liftedConsistent_maxMissing (d : Domain) (p : Problem) (relevance : Bool)
    (families : List (List GroundAtom))
    (hnd : ∀ fam ∈ families, fam.Nodup)
    (hcost : ∀ o ∈ groundedOps d p relevance, 1 ≤ o.cost)
    (hsafe : ∀ o ∈ groundedOps d p relevance, ∀ fam ∈ families, FamilySafeL fam o) :
    LiftedConsistentOn d p relevance (fun _ => True) (maxMissingL families) := by
  intro o ho σ _ _
  have hle := maxMissingL_le_succ (σ := σ) hnd (hsafe o ho)
  have := hcost o ho
  omega

/-! ### The compiled version computes it

`missing` counts facts; `missingL` counts atoms.  Under the abstraction they are
the same count, because testing a fact is asking the atom-level state.
-/

/-- The atoms of a task's goal families. -/
def familiesOf (t : Task) (preds : List (List Pddl.Name)) : List (List GroundAtom) :=
  (t.families preds).map fun fam => fam.toList.map fun f => t.factNames.getD f default

theorem missing_eq_missingL {t : Task} {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size)
    (fs : List Fact) (hrange : ∀ f ∈ fs, f < t.factNames.size) :
    missing fs s = missingL (fs.map fun f => t.factNames.getD f default) σ := by
  unfold missing missingL
  rw [List.filter_map, List.length_map, List.countP_eq_length_filter]
  refine congrArg _ ?_
  refine List.filter_congr ?_
  intro f hf
  simp only [Function.comp_apply]
  rw [habs.numbered f (by rw [hn]; exact hrange f hf)]

theorem computes_maxMissing (t : Task) (nm : String) (preds : List (List Pddl.Name))
    (hn : t.numFacts = t.factNames.size)
    (hrange : ∀ f ∈ t.goal, f < t.factNames.size) :
    Computes t (maxMissingOf nm (t.families preds)).eval (maxMissingL (familiesOf t preds)) := by
  intro s σ habs _
  rw [maxMissingOf_eval]
  unfold missingMax familiesOf maxMissingL
  rw [List.map_map]
  refine congrArg (fun l : List Nat => List.foldl max 0 l) ?_
  refine List.map_congr_left ?_
  intro fam hfam
  refine missing_eq_missingL habs hn _ ?_
  intro f hf
  have : f ∈ t.goal := by
    simp only [Task.families, List.mem_map] at hfam
    obtain ⟨ps, -, rfl⟩ := hfam
    exact (mem_goalFactsWith (by simpa using hf)).1
  exact hrange f this

/-! ### Admissible, end to end

Nothing below is domain-specific.  A domain supplies its predicate families and
the one fact that no schema of it adds two atoms of one family or deletes any.
-/

theorem simple_admissibleOn (d : Domain) (p : Problem) (relevance : Bool)
    (hwf : Task.WF (ground d p relevance))
    (hcost : ∀ o ∈ groundedOps d p relevance, 0 < o.cost)
    (nm : String) (preds : List (List Pddl.Name))
    (hnd : ∀ fam ∈ familiesOf (ground d p relevance) preds, fam.Nodup)
    (hsub : ∀ fam ∈ familiesOf (ground d p relevance) preds, ∀ a ∈ fam, a ∈ p.goal)
    (hsafe : ∀ o ∈ groundedOps d p relevance,
      ∀ fam ∈ familiesOf (ground d p relevance) preds, FamilySafeL fam o) :
    (ground d p relevance).AdmissibleOn (Reachable (ground d p relevance))
      (maxMissingOf nm ((ground d p relevance).families preds)).eval := by
  have hn : (ground d p relevance).numFacts = (ground d p relevance).factNames.size := rfl
  have hrange : ∀ f ∈ (ground d p relevance).goal, f < (ground d p relevance).factNames.size :=
    fun f hf => by rw [← hn]; exact hwf.goal f hf
  refine admissibleOn_of_lifted d p relevance hwf hcost _
    (maxMissingL (familiesOf (ground d p relevance) preds))
    (fun _ => True) (computes_maxMissing _ nm preds hn hrange) trivial
    (fun _ _ _ _ _ => trivial)
    (liftedGoalAware_maxMissing p _ hsub)
    (liftedConsistent_maxMissing d p relevance _ hnd (fun o ho => hcost o ho) hsafe)

end Planner.Lifted
