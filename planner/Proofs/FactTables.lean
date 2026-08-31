/-
The fact tables every domain's `compile` is built from.

Each domain's `Data` looks different, but every one of them reads the task
through the same five accessors of `Planner/ExampleHeuristics/Base.lean`:
`factsWith`, `staticWith`, `goalFactsWith`, `goalAtomsWith` and `objectsOfTypes`.
Proving those faithful is therefore one job for all ten domains, not ten jobs.

What "faithful" means here is stated against `Abstracts`, the reading of a packed
state as a set of ground atoms that `Proofs/GroundingCorrect.lean` establishes:
a fact of `factsWith t pred` is in range, its name is the atom it is paired with,
that atom uses `pred`, and testing the bit is asking the atom-level state.
-/
import Proofs.GroundingCorrect
import Proofs.ExampleHeuristics.Base

namespace Planner

open Planner.Pddl

/-! ### `factsWith` lists numbered atoms of one predicate -/

theorem mem_factsWith {t : Task} {pred : Name} {f : Fact} {a : GroundAtom}
    (h : (f, a) ∈ t.factsWith pred) :
    f < t.factNames.size ∧ t.factNames.getD f default = a ∧ a.pred = pred := by
  simp only [Task.factsWith, Array.mem_map, Array.mem_filter] at h
  obtain ⟨⟨b, i⟩, ⟨hmem, hpred⟩, heq⟩ := h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨hf, ha⟩ := heq
  subst hf
  subst ha
  obtain ⟨-, hlt, hget⟩ := Array.mem_zipIdx hmem
  simp only [Nat.zero_add, Nat.sub_zero] at hlt hget
  refine ⟨hlt, ?_, by simpa using hpred⟩
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
  simpa using hget.symm

/--
And it lists *every* numbered atom of that predicate.  With
`Proofs/GroundingComplete.lean`, which says which atoms are numbered, this is
what tells a `compile` that its table has an entry for each object.
-/
theorem mem_factsWith_of_named {t : Task} {pred : Name} {f : Fact} {a : GroundAtom}
    (hf : f < t.factNames.size) (hname : t.factNames.getD f default = a)
    (hpred : a.pred = pred) : (f, a) ∈ t.factsWith pred := by
  have hget : t.factNames[f] = a := by
    rw [← hname, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hf]
    simp
  simp only [Task.factsWith, Array.mem_map, Array.mem_filter]
  refine ⟨(a, f), ⟨?_, by simpa using hpred⟩, rfl⟩
  rw [Array.mem_zipIdx_iff_getElem?]
  simpa using (by rw [Array.getElem?_eq_getElem hf, hget] :
    t.factNames[f]? = some a)

/--
**Every table a domain filters out of `factsWith` inherits its guarantees.**

A compiled table is almost always `(t.factsWith pred).filterMap g` for some `g`
that keeps the entries naming the objects in hand.  Whatever `g` is, an entry of
the result comes from a numbered fact whose atom uses `pred` — which is the
first step of every such table's reader.
-/
theorem mem_factsWith_filterMap {t : Task} {pred : Name} {β : Type}
    {g : Fact × GroundAtom → Option β} {y : β}
    (h : y ∈ (t.factsWith pred).filterMap g) :
    ∃ x ∈ t.factsWith pred, g x = some y ∧ x.1 < t.factNames.size ∧
      t.factNames.getD x.1 default = x.2 ∧ x.2.pred = pred := by
  obtain ⟨x, hx, hval⟩ := Array.mem_filterMap.mp h
  obtain ⟨h1, h2, h3⟩ := mem_factsWith hx
  exact ⟨x, hx, hval, h1, h2, h3⟩

/--
**`factsWith` names each fact once.**

Its facts are the positions of the numbered atoms, filtered, so they inherit the
distinctness of the positions.  Every pool count that has to move by at most one
needs this of its table.
-/
theorem factsWith_nodup (t : Task) (pred : Name) :
    ((t.factsWith pred).map (·.1)).toList.Nodup := by
  have hmap : ((t.factsWith pred).map (·.1)).toList
      = ((t.factNames.toList.zipIdx.filter fun x => x.1.pred == pred)).map (·.2) := by
    simp [Task.factsWith, Array.toList_map]
  rw [hmap]
  exact List.Nodup.sublist (List.Sublist.map _ List.filter_sublist)
    (by rw [List.zipIdx_map_snd]; exact List.nodup_range')

/-! ### Reading one of those facts is asking the atom-level state -/

theorem test_factsWith {t : Task} {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hn : t.numFacts = t.factNames.size) {pred : Name} {f : Fact} {a : GroundAtom}
    (h : (f, a) ∈ t.factsWith pred) : s.test f = σ a := by
  obtain ⟨hlt, hname, -⟩ := mem_factsWith h
  rw [← hname]
  refine (habs.numbered f ?_).symm
  rw [hn]; exact hlt

/-! ### Reading a position off the state

Every domain has one of these: where the lift is, where a rover stands, which
vehicle carries a package, where a tray is.  All of them are
`(tbl.find? fun x => s.test x.1).map (·.2)` over a table of facts paired with a
payload, so both directions are proved once here.
-/

theorem find?_holds {α : Type} {t : Task} {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size)
    {tbl : Array (Fact × α)} (hok : ∀ y ∈ tbl, y.1 < t.factNames.size)
    {x : Fact × α} (h : tbl.find? (fun y => s.test y.1) = some x) :
    x ∈ tbl ∧ σ (t.factNames.getD x.1 default) = true := by
  have hmem : x ∈ tbl := Array.mem_of_find?_eq_some h
  refine ⟨hmem, ?_⟩
  have hp : s.test x.1 = true := by simpa using Array.find?_some h
  rw [habs.numbered x.1 (by rw [hn]; exact hok x hmem)]
  exact hp

theorem find?_none_holds {α : Type} {t : Task} {s : State} {σ : AtomState}
    (habs : Abstracts t s σ) (hn : t.numFacts = t.factNames.size)
    {tbl : Array (Fact × α)} (hok : ∀ y ∈ tbl, y.1 < t.factNames.size)
    (h : tbl.find? (fun y => s.test y.1) = none) :
    ∀ y ∈ tbl, σ (t.factNames.getD y.1 default) = false := by
  intro y hy
  have hp : s.test y.1 = false := by
    have := Array.find?_eq_none.mp h y hy
    simpa using this
  rw [habs.numbered y.1 (by rw [hn]; exact hok y hy)]
  exact hp

/-- The tables `factsWith` builds satisfy the range condition the two need. -/
theorem factsWith_ok {t : Task} {pred : Name} :
    ∀ y ∈ t.factsWith pred, y.1 < t.factNames.size := by
  intro y hy
  exact (mem_factsWith (by simpa using hy)).1

/-! ### Looking a fact up by its arguments

Every domain builds its tables the same way: take the facts of one predicate and
find the one whose arguments are the objects in hand.  What the search then holds
is a `Fact`; what a proof needs is the atom it names, and this says it is exactly
the atom asked for.
-/

theorem factsWith_find_args {t : Task} {pred : Name} {args : List Name}
    {x : Fact × GroundAtom}
    (h : (t.factsWith pred).find? (fun y => y.2.args == args) = some x) :
    t.factNames.getD x.1 default = { pred := pred, args := args } := by
  have hmem : x ∈ t.factsWith pred := Array.mem_of_find?_eq_some h
  obtain ⟨-, hname, hpred⟩ := mem_factsWith hmem
  have hargs : x.2.args = args := by simpa using Array.find?_some h
  rw [hname, ← hpred, ← hargs]

/-- The same, for the `Option Fact` the tables actually store. -/
theorem factsWith_find_args_map {t : Task} {pred : Name} {args : List Name} {f : Fact}
    (h : ((t.factsWith pred).find? (fun y => y.2.args == args)).map (·.1) = some f) :
    t.factNames.getD f default = { pred := pred, args := args } := by
  rcases hf : (t.factsWith pred).find? (fun y => y.2.args == args) with _ | x
  · rw [hf] at h; simp at h
  · rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact factsWith_find_args hf

/-! ### The goal accessors -/

theorem mem_goalFactsWith {t : Task} {preds : List Name} {f : Fact}
    (h : f ∈ t.goalFactsWith preds) :
    f ∈ t.goal ∧ preds.contains (t.factNames.getD f default).pred = true := by
  simp only [Task.goalFactsWith, Array.mem_filter] at h
  exact ⟨h.1, by simpa using h.2⟩

theorem mem_goalAtomsWith {t : Task} {pred : Name} {a : GroundAtom}
    (h : a ∈ t.goalAtomsWith pred) : a ∈ t.goalAtoms ∧ a.pred = pred := by
  simp only [Task.goalAtomsWith, Array.mem_filter] at h
  exact ⟨h.1, by simpa using h.2⟩

/-! ### The static accessor: what it lists holds in every abstracted state -/

theorem staticWith_holds {t : Task} {s : State} {σ : AtomState} (habs : Abstracts t s σ)
    (hdisj : ∀ a ∈ t.staticAtoms, ∀ f, f < t.numFacts → t.factNames.getD f default ≠ a)
    {pred : Name} {a : GroundAtom} (h : a ∈ t.staticWith pred) : σ a = true := by
  simp only [Task.staticWith, Array.mem_filter] at h
  rw [habs.unnumbered a (hdisj a h.1)]
  simpa using h.1

/-! ### Objects -/

theorem mem_objectsOfTypes {t : Task} {tys : List Name} {o : Name}
    (h : o ∈ t.objectsOfTypes tys) :
    ∃ decl ∈ t.objects, decl.name = o ∧ tys.contains decl.type = true := by
  simp only [Task.objectsOfTypes, Array.mem_map, Array.mem_filter] at h
  obtain ⟨decl, ⟨hmem, hty⟩, hname⟩ := h
  exact ⟨decl, hmem, hname, by simpa using hty⟩

end Planner
