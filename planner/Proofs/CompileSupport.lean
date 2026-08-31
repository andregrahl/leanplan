/-
What every domain's `compile` bridge needs.

`Proofs/FactTables.lean` says what the task accessors return and
`Proofs/GroundingComplete.lean` says which atoms are numbered.  Between the two
sits the same small pile of bookkeeping for every domain: reading an object's
type, indexing an object list, pairing two `filterMap`s, and finding the atom a
goal fact names.  It is collected here so a domain's bridge file is only about
that domain.
-/
import Proofs.GroundingComplete
import Proofs.FactTables
import Proofs.StepView

namespace Planner

open Planner.Pddl

/-! ### Duplicate-free compiler traversals -/

/-- `zipIdx` is duplicate-free because its second components are distinct. -/
theorem List.nodup_zipIdx (l : List α) (k : Nat := 0) : (l.zipIdx k).Nodup := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    simp only [List.zipIdx, List.nodup_cons]
    exact ⟨fun hm => by
      have hk := List.le_snd_of_mem_zipIdx hm
      simp only at hk
      omega, ih (k + 1)⟩

/-- `filterMap` preserves duplicate-freedom when its output identifies its
input among the entries actually traversed. -/
theorem List.Nodup.filterMap_on {l : List α} {f : α → Option β}
    (hl : l.Nodup)
    (hinj : ∀ a ∈ l, ∀ a' ∈ l, ∀ b, f a = some b → f a' = some b → a = a') :
    (l.filterMap f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hl
    cases hfa : f a with
    | none =>
      simp only [List.filterMap_cons, hfa]
      exact ih hl (fun x hx y hy b hxb hyb =>
        hinj x (by simp [hx]) y (by simp [hy]) b hxb hyb)
    | some b =>
      simp only [List.filterMap_cons, hfa, List.nodup_cons]
      constructor
      · intro hb
        obtain ⟨a', ha', hfa'⟩ := List.mem_filterMap.mp hb
        have haa := hinj a (by simp) a' (by simp [ha']) b hfa (by simpa using hfa')
        exact ha (haa ▸ ha')
      · exact ih hl (fun x hx y hy c hxc hyc =>
          hinj x (by simp [hx]) y (by simp [hy]) c hxc hyc)

/-- A common compiler pattern: enumerate an array and discard entries.  If an
output carries a key copied from a duplicate-free parallel array, the resulting
array has no duplicate output records. -/
theorem Array.filterMap_zipIdx_nodup_of_key [Inhabited κ]
    (xs : Array α) (keys : Array κ) (hsize : xs.size = keys.size)
    (hkeys : keys.toList.Nodup) (f : α × Nat → Option β) (key : β → κ)
    (hkey : ∀ x ∈ xs.toList.zipIdx, ∀ b,
      f x = some b → key b = keys.getD x.2 default) :
    ((xs.zipIdx).filterMap f).toList.Nodup := by
  rw [Array.toList_filterMap, Array.toList_zipIdx]
  apply List.Nodup.filterMap_on (List.nodup_zipIdx xs.toList)
  intro a ha a' ha' b hba hba'
  obtain ⟨halt, haval⟩ := List.mem_zipIdx' ha
  obtain ⟨ha'lt, ha'val⟩ := List.mem_zipIdx' ha'
  have hk := (hkey a ha b hba).symm.trans (hkey a' ha' b hba')
  have hk' : keys[a.2]'(by simpa [← hsize] using halt) =
      keys[a'.2]'(by simpa [← hsize] using ha'lt) := by
    simpa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem,
      show a.2 < keys.size by simpa [← hsize] using halt,
      show a'.2 < keys.size by simpa [← hsize] using ha'lt] using hk
  have hi : a.2 = a'.2 := (List.Nodup.getElem_inj_iff hkeys).mp (by
    simpa only [Array.getElem_toList] using hk')
  apply Prod.ext
  · rw [haval, ha'val]
    simpa [hi]
  · exact hi

/-- Numbering preserves a duplicate-free problem goal. -/
theorem ground_goal_nodup (d : Domain) (p : Problem) (rel : Bool)
    (hnd : p.goal.Nodup) : ((ground d p rel).goal).toList.Nodup := by
  show ((p.goal.toArray.map (fun a =>
    (factIndex (allAtoms (groundedOps d p rel) p.goal.toArray)).1.getD a 0)).toList).Nodup
  rw [Array.toList_map]
  refine List.Nodup.map_on (fun a ha b hb h => ?_) (by simpa using hnd)
  have hma : a ∈ allAtoms (groundedOps d p rel) p.goal.toArray := by
    unfold allAtoms
    exact Array.mem_append.mpr (Or.inr (by simpa using ha))
  have hmb : b ∈ allAtoms (groundedOps d p rel) p.goal.toArray := by
    unfold allAtoms
    exact Array.mem_append.mpr (Or.inr (by simpa using hb))
  exact factIndex_injective' _ (factIndex_contains _ hma) (factIndex_contains _ hmb) h

/-! ### The task the grounder builds, with the relevance analysis off -/

/-- The task the grounder builds.  `rel` is whether the relevance analysis ran. -/
abbrev taskOf (d : Domain) (p : Problem) (rel : Bool) : Task := ground d p rel

theorem taskOf_objects (d : Domain) (p : Problem) (rel : Bool) :
    (taskOf d p rel).objects = (allObjects d p).toArray := rfl

theorem taskOf_goalAtoms (d : Domain) (p : Problem) (rel : Bool) :
    (taskOf d p rel).goalAtoms = p.goal.toArray := rfl

theorem taskOf_numFacts (d : Domain) (p : Problem) (rel : Bool) :
    (taskOf d p rel).numFacts = (taskOf d p rel).factNames.size := rfl


/-! ### Types -/

theorem isSubtype_refl (d : Domain) (x : Name) : d.isSubtype x x = true := by
  unfold Domain.isSubtype
  rcases h : d.types.length with _ | n
  · simp [Domain.isSubtypeFuel]
  · simp [Domain.isSubtypeFuel]

theorem wellTyped_of_type {d : Domain} {objects : List TypedName} {ty : Name} {o : TypedName}
    (ho : o ∈ objects) (hty : o.type = ty) : WellTyped d objects ty o.name :=
  ⟨o, ho, rfl, by rw [hty]; exact isSubtype_refl d ty⟩


/-- When the relevance analysis does not verify its set, it prunes nothing, and the
two tasks are the same. -/
theorem taskOf_eq_of_unverified (d : Domain) (p : Problem)
    (h : relevantOK (rawOps d p) p.goal.toArray
      (relevantSet (rawOps d p) p.goal.toArray) = false) :
    taskOf d p true = taskOf d p false := by
  have hops : groundedOps d p true = groundedOps d p false := by
    rw [groundedOps_true, groundedOps_false]
    unfold relevanceAnalysis
    simp only [h, Bool.false_eq_true, if_false]
  show ground d p true = ground d p false
  unfold ground
  rw [hops]

/-! ### `staticAtoms` is exactly the part of `:init` no operator mentions -/

theorem staticAtoms_sub (d : Domain) (p : Problem) (rel : Bool) {a : GroundAtom}
    (h : a ∈ (taskOf d p rel).staticAtoms) : a ∈ p.init := by
  rw [show (taskOf d p rel).staticAtoms
      = p.init.toArray.filter (!(factIndex (allAtoms (groundedOps d p rel)
          p.goal.toArray)).1.contains ·) from rfl] at h
  simpa using (Array.mem_filter.mp h).1

theorem mem_staticAtoms (d : Domain) (p : Problem) (rel : Bool) {a : GroundAtom} (hinit : a ∈ p.init)
    (hnot : a ∉ allAtoms (groundedOps d p rel) p.goal.toArray) :
    a ∈ (taskOf d p rel).staticAtoms := by
  rw [show (taskOf d p rel).staticAtoms
      = p.init.toArray.filter (!(factIndex (allAtoms (groundedOps d p rel)
          p.goal.toArray)).1.contains ·) from rfl]
  refine Array.mem_filter.mpr ⟨by simpa using hinit, ?_⟩
  simp only [Bool.not_eq_true']
  rw [Bool.eq_false_iff]
  intro hc
  exact hnot (factIndex_mem _ hc)

/-- The same, read through `staticWith`. -/
theorem mem_staticWith (d : Domain) (p : Problem) (rel : Bool) {a : GroundAtom}
    (hinit : a ∈ p.init)
    (hnot : a ∉ allAtoms (groundedOps d p rel) p.goal.toArray) {pred : Name}
    (hpred : a.pred = pred) : a ∈ (taskOf d p rel).staticWith pred :=
  Array.mem_filter.mpr ⟨mem_staticAtoms d p rel hinit hnot, by simpa using hpred⟩

theorem staticWith_sub (d : Domain) (p : Problem) (rel : Bool) {pred : Name} {a : GroundAtom}
    (h : a ∈ (taskOf d p rel).staticWith pred) : a ∈ p.init ∧ a.pred = pred :=
  ⟨staticAtoms_sub d p rel (Array.mem_filter.mp h).1, by simpa using (Array.mem_filter.mp h).2⟩

/-! ### Objects of one type, and their positions -/

/-- The objects of one type, as the compiled tables index them. -/
abbrev objsOf (t : Task) (ty : Name) : Array Name := t.objectsOfTypes [ty]

theorem objsOf_wellTyped {d : Domain} {p : Problem} {rel : Bool} {ty l : Name}
    (h : l ∈ objsOf (taskOf d p rel) ty) : WellTyped d (allObjects d p) ty l := by
  obtain ⟨o, ho, hname, hty⟩ := mem_objectsOfTypes h
  rw [taskOf_objects] at ho
  refine ⟨o, by simpa using ho, hname, ?_⟩
  have : o.type = ty := by simpa using hty
  rw [this]; exact isSubtype_refl d ty

/-- An object of the declared type is in the list, when the type has no subtype
among the objects. -/
theorem mem_objsOf {d : Domain} {p : Problem} {rel : Bool} {ty l : Name} {o : TypedName}
    (ho : o ∈ allObjects d p) (hname : o.name = l) (hty : o.type = ty) :
    l ∈ objsOf (taskOf d p rel) ty := by
  simp only [objsOf, Task.objectsOfTypes, taskOf_objects, Array.mem_map, Array.mem_filter]
  exact ⟨o, ⟨by simpa using ho, by simp [hty]⟩, hname⟩

theorem objsOf_nodup {d : Domain} {p : Problem} {rel : Bool} {ty : Name}
    (hnd : ((allObjects d p).map (·.name)).Nodup) : (objsOf (taskOf d p rel) ty).toList.Nodup := by
  have heq : (objsOf (taskOf d p rel) ty).toList
      = ((allObjects d p).filter (fun o => [ty].contains o.type)).map (·.name) := by
    simp [objsOf, Task.objectsOfTypes, taskOf_objects]
  rw [heq]
  exact hnd.sublist (List.Sublist.map _ (List.filter_sublist))

/-- Where an object sits in the list. -/
theorem findIdx_sound {xs : Array Name} {l : Name} {i : Nat}
    (h : xs.findIdx? (· == l) = some i) : i < xs.size ∧ xs.getD i "" = l := by
  rw [Array.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨hlt, hp, -⟩ := h
  refine ⟨hlt, ?_⟩
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
  simpa using hp

theorem findIdx_total {xs : Array Name} {l : Name} (h : l ∈ xs) :
    ∃ i, xs.findIdx? (· == l) = some i := by
  rcases hf : xs.findIdx? (· == l) with _ | i
  · rw [Array.findIdx?_eq_none_iff] at hf
    have := hf l h
    simp at this
  · exact ⟨i, rfl⟩

/-! ### Two list facts the pairing needs -/

theorem filterMap_zipIdx {α β : Type} (g : α → Option β) :
    ∀ (l : List α) (n : Nat), (l.zipIdx n).filterMap (fun x => g x.1) = l.filterMap g := by
  intro l
  induction l with
  | nil => intro n; rfl
  | cons x xs ih =>
      intro n
      rcases hg : g x with _ | b
      · rw [List.zipIdx_cons, List.filterMap_cons_none (by simpa using hg),
          List.filterMap_cons_none hg, ih]
      · rw [List.zipIdx_cons, List.filterMap_cons_some (b := b) (by simpa using hg),
          List.filterMap_cons_some hg, ih]

/-- The same, when the implication only holds on the list's own elements. -/
theorem filterMap_sublist_mem {α β : Type} {g f : α → Option β} :
    ∀ (l : List α), (∀ a ∈ l, ∀ b, g a = some b → f a = some b) →
      (l.filterMap g).Sublist (l.filterMap f) := by
  intro l
  induction l with
  | nil => intro _; exact List.Sublist.refl _
  | cons x xs ih =>
      intro h
      rcases hg : g x with _ | b
      · rw [List.filterMap_cons_none hg]
        rcases hfx : f x with _ | c
        · rw [List.filterMap_cons_none hfx]
          exact ih (fun a ha => h a (by simp [ha]))
        · rw [List.filterMap_cons_some hfx]
          exact (ih (fun a ha => h a (by simp [ha]))).cons _
      · rw [List.filterMap_cons_some hg,
          List.filterMap_cons_some (h x (by simp) b hg)]
        exact (ih (fun a ha => h a (by simp [ha]))).cons₂ _

theorem filterMap_sublist {α β : Type} {g f : α → Option β}
    (h : ∀ a b, g a = some b → f a = some b) :
    ∀ (l : List α), (l.filterMap g).Sublist (l.filterMap f) := by
  intro l
  induction l with
  | nil => exact List.Sublist.refl _
  | cons x xs ih =>
      rcases hg : g x with _ | b
      · rw [List.filterMap_cons_none hg]
        rcases hf : f x with _ | c
        · rw [List.filterMap_cons_none hf]; exact ih
        · rw [List.filterMap_cons_some hf]; exact ih.cons _
      · rw [List.filterMap_cons_some hg, List.filterMap_cons_some (h x b hg)]
        exact ih.cons₂ _

theorem mem_of_lookup {α : Type} [BEq α] [LawfulBEq α] {β : Type} :
    ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → (a, b) ∈ l := by
  intro l
  induction l with
  | nil => intro a b h; simp [List.lookup] at h
  | cons x xs ih =>
      intro a b h
      rw [List.lookup_cons] at h
      rcases hb : (a == x.1) with _ | _ <;> rw [hb] at h
      · exact List.mem_cons.mpr (Or.inr (ih h))
      · simp only [Option.some.injEq] at h
        subst h
        have : a = x.1 := by simpa using hb
        rw [this]
        exact List.mem_cons.mpr (Or.inl rfl)

/-- A lookup finds the pair it holds, when the keys are distinct. -/
theorem lookup_of_mem {α : Type} [BEq α] [LawfulBEq α] {β : Type} :
    ∀ {l : List (α × β)}, (l.map (·.1)).Nodup → ∀ {a : α} {b : β}, (a, b) ∈ l →
      l.lookup a = some b := by
  intro l
  induction l with
  | nil => intro _ a b h; simp at h
  | cons x xs ih =>
      intro hnd a b h
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp h with rfl | h1
      · rw [List.lookup_cons]
        simp
      · have hne : ¬ (a = x.1) := by
          intro hc
          exact hnd.1 (by rw [← hc]; exact List.mem_map.mpr ⟨(a, b), h1, rfl⟩)
        rw [List.lookup_cons]
        have : (a == x.1) = false := by simpa using hne
        rw [this]
        exact ih hnd.2 h1


/-! ### The number a goal atom received

`goalFact` is read out of `t.goal` at the goal atom's own position, so what it
names is that goal atom.
-/

theorem goal_name_eq (d : Domain) (p : Problem) (rel : Bool) {i : Nat}
    (hi : i < (taskOf d p rel).goalAtoms.size) :
    (taskOf d p rel).factNames.getD ((taskOf d p rel).goal.getD i 0) default
        = (taskOf d p rel).goalAtoms[i]'hi ∧
      (taskOf d p rel).goal.getD i 0 < (taskOf d p rel).factNames.size := by
  have hmem : (taskOf d p rel).goalAtoms[i]'hi
      ∈ allAtoms (groundedOps d p rel) p.goal.toArray := by
    unfold allAtoms
    exact Array.mem_append.mpr (Or.inr (Array.getElem_mem hi))
  have hix : (taskOf d p rel).goal.getD i 0
      = (factIndex (allAtoms (groundedOps d p rel) p.goal.toArray)).1.getD
          ((taskOf d p rel).goalAtoms[i]'hi) 0 := by
    show (p.goal.toArray.map (fun a =>
      (factIndex (allAtoms (groundedOps d p rel) p.goal.toArray)).1.getD a 0)).getD i 0 = _
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hi)]
    simp only [Option.getD_some, Array.getElem_map]
    rfl
  rw [hix]
  exact ⟨name_ix (groundedOps d p rel) p.goal.toArray p.init.toArray
      (allObjects d p).toArray d.name hmem,
    ix_lt (groundedOps d p rel) p.goal.toArray p.init.toArray
      (allObjects d p).toArray d.name hmem⟩


/-- The atom named by the goal fact at one goal position is a goal atom. -/
theorem goalAtom_of_index (d : Domain) (p : Problem) (rel : Bool) {i : Nat}
    (hi : i < (taskOf d p rel).goalAtoms.size) :
    (taskOf d p rel).factNames.getD ((taskOf d p rel).goal.getD i 0) default ∈ p.goal := by
  obtain ⟨hname, -⟩ := goal_name_eq d p rel hi
  rw [hname]
  have : (taskOf d p rel).goalAtoms[i]'hi ∈ (taskOf d p rel).goalAtoms :=
    Array.getElem_mem hi
  simpa [taskOf_goalAtoms] using this

/-- Every numbered goal fact reads back to an atom of the problem goal. -/
theorem atomOf_mem_goal (d : Domain) (p : Problem) (rel : Bool) {f : Fact}
    (hf : f ∈ (taskOf d p rel).goal) :
    (taskOf d p rel).factNames.getD f default ∈ p.goal := by
  change f ∈ (p.goal.toArray.map fun a =>
    (factIndex (allAtoms (groundedOps d p rel) p.goal.toArray)).1.getD a 0) at hf
  rw [Array.mem_map] at hf
  obtain ⟨a, ha, hfa⟩ := hf
  have hmem : a ∈ allAtoms (groundedOps d p rel) p.goal.toArray := by
    unfold allAtoms
    exact Array.mem_append.mpr (Or.inr (by simpa using ha))
  rw [← hfa]
  change (factIndex (allAtoms (groundedOps d p rel) p.goal.toArray)).2.getD
    ((factIndex (allAtoms (groundedOps d p rel) p.goal.toArray)).1.getD a 0) default ∈ p.goal
  rw [factIndex_name _ hmem]
  simpa using ha

/-- Distinct in-range fact numbers read back to distinct atoms. -/
theorem factNames_inj (d : Domain) (p : Problem) (rel : Bool) {f g : Fact}
    (hf : f < (taskOf d p rel).factNames.size)
    (hg : g < (taskOf d p rel).factNames.size)
    (h : (taskOf d p rel).factNames.getD f default
      = (taskOf d p rel).factNames.getD g default) : f = g := by
  have hfn : (taskOf d p rel).factNames
      = (factIndex (allAtoms (groundedOps d p rel) p.goal.toArray)).2 := rfl
  rw [hfn] at hf hg h
  obtain ⟨-, hf'⟩ := factIndex_rev _ f hf
  obtain ⟨-, hg'⟩ := factIndex_rev _ g hg
  rw [← hf', h, hg']


/-! ### Goal tables have no duplicate entries

Every domain builds its goal table the same way: walk the goal atoms with their
indices, keep the ones the domain recognises, and store `t.goal.getD i 0` in the
entry.  Two entries therefore carry distinct facts unless they came from the same
goal atom, and the problem's goal names each atom once.  So no domain has to
assume its table is duplicate-free -- it follows from `p.goal.Nodup`, which the
records already ask for.
-/

/--
**A goal table built by `zipIdx.filterMap` has no duplicate entries.**

`key` is the entry's reading of the goal atom it came from -- `atomOf t` of the
stored fact, which is the goal atom itself.  Distinct indices give distinct
atoms, because `p.goal` has no duplicate.
-/
theorem goalTable_nodup {β : Type} (d : Domain) (p : Problem) (rel : Bool)
    (hnd : p.goal.Nodup) (f : GroundAtom × Nat → Option β) (key : β → GroundAtom)
    (hkey : ∀ x ∈ (taskOf d p rel).goalAtoms.toList.zipIdx, ∀ b, f x = some b →
      key b = (taskOf d p rel).goalAtoms.getD x.2 default) :
    (((taskOf d p rel).goalAtoms.zipIdx).filterMap f).toList.Nodup := by
  refine Array.filterMap_zipIdx_nodup_of_key _ (taskOf d p rel).goalAtoms rfl ?_ f key hkey
  rw [taskOf_goalAtoms]
  simpa using hnd

/--
**The same, for a table that stores the goal's *fact* rather than its atom.**

Numbering is injective on the goal, so distinct indices give distinct facts, and
`ground_goal_nodup` is what says so.
-/
theorem goalTable_nodup_fact {β : Type} (d : Domain) (p : Problem) (rel : Bool)
    (hnd : p.goal.Nodup) (f : GroundAtom × Nat → Option β) (key : β → Fact)
    (hkey : ∀ x ∈ (taskOf d p rel).goalAtoms.toList.zipIdx, ∀ b, f x = some b →
      key b = (taskOf d p rel).goal.getD x.2 default) :
    (((taskOf d p rel).goalAtoms.zipIdx).filterMap f).toList.Nodup :=
  Array.filterMap_zipIdx_nodup_of_key (taskOf d p rel).goalAtoms (taskOf d p rel).goal
    (by show (taskOf d p rel).goalAtoms.size
          = ((taskOf d p rel).goalAtoms.map (fun a =>
              (factIndex (allAtoms (groundedOps d p rel) p.goal.toArray)).1.getD a 0)).size
        simp)
    (ground_goal_nodup d p rel hnd) f key hkey

/--
The goal atom an entry names, read back through the fact numbering.

This is the `hkey` side condition in the form the domains meet it: the entry
stores `t.goal.getD i 0`, and reading that fact's name gives the `i`-th goal
atom.
-/
theorem atomOf_goal_getD (d : Domain) (p : Problem) (rel : Bool) {i : Nat}
    (hi : i < (taskOf d p rel).goalAtoms.size) :
    (taskOf d p rel).factNames.getD ((taskOf d p rel).goal.getD i 0) default
      = (taskOf d p rel).goalAtoms.getD i default := by
  rw [(goal_name_eq d p rel hi).1]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  rfl

/-! ### Reading an instance's atoms off the operator

A domain proof names the atoms of one schema instance.  What the transition needs
is the *operator's* precondition and delete list, which grounding may have
trimmed.  These two say when the trimming kept what the proof names.
-/

/-- A dynamic precondition of the instance is one of the operator's. -/
theorem pre_mem_op {d : Domain} {p : Problem} {o : AtomOp} (hf : OpFacts d p o)
    {a : GroundAtom} (hmem : a ∈ hf.inst.pre)
    (hdyn : (staticPredicates d).contains a.pred = false) : a ∈ o.pre := by
  have hmem' : a ∈ hf.inst.schema.pre.map (instAtom hf.inst.schema.params hf.inst.args) :=
    hmem
  obtain ⟨y, hy, hval⟩ := List.mem_map.mp hmem'
  rw [← hval]
  exact hf.preComplete y hy (by
    rw [show y.pred = a.pred from by rw [← hval]; rfl]; exact hdyn)

/-- And so it holds wherever the operator applies. -/
theorem pre_holds {d : Domain} {p : Problem} {o : AtomOp} (hf : OpFacts d p o)
    {a : GroundAtom} (hmem : a ∈ hf.inst.pre)
    (hdyn : (staticPredicates d).contains a.pred = false)
    {σ : AtomState} (happ : o.applicableA σ) : σ a = true :=
  happ a (pre_mem_op hf hmem hdyn)

/-- A delete the instance names is a delete of the operator, when the operator
also reads it and does not add it back. -/
theorem del_kept {d : Domain} {p : Problem} {o : AtomOp} (hf : OpFacts d p o)
    {a : GroundAtom} (hmem : a ∈ hf.inst.del) (hadd : a ∉ hf.inst.add)
    (hpre : a ∈ hf.inst.pre)
    (hdyn : (staticPredicates d).contains a.pred = false) : a ∈ o.del := by
  have hmem' : a ∈ hf.inst.schema.del.map (instAtom hf.inst.schema.params hf.inst.args) :=
    hmem
  obtain ⟨y, hy, hval⟩ := List.mem_map.mp hmem'
  have hpre' : a ∈ o.pre := pre_mem_op hf hpre hdyn
  have := hf.delComplete y hy (by rw [hval]; exact hadd) (by rw [hval]; exact hpre')
  rwa [hval] at this


/-- Every atom an operator mentions received a fact number. -/
theorem numbered_of_op (d : Domain) (p : Problem) (rel : Bool) {o : AtomOp}
    (ho : o ∈ groundedOps d p rel) {a : GroundAtom}
    (ha : a ∈ o.pre ∨ a ∈ o.add ∨ a ∈ o.del) :
    ∃ f, f < (ground d p rel).factNames.size ∧
      (ground d p rel).factNames.getD f default = a := by
  have hmem : a ∈ allAtoms (groundedOps d p rel) p.goal.toArray :=
    mem_allAtoms_of_op ho ha
  exact ⟨_, ix_lt (groundedOps d p rel) p.goal.toArray p.init.toArray
      (allObjects d p).toArray d.name hmem,
    name_ix (groundedOps d p rel) p.goal.toArray p.init.toArray
      (allObjects d p).toArray d.name hmem⟩


/-! ### One operator's effect on one atom

A schema's add and delete lists are short and explicit, so what an operator does
to an atom is decided by two list memberships.  These four are the shapes that
recur in every domain's step proof, stated once so that a domain supplies only
the two list equations and two `simp` calls.
-/

/-- An atom outside both lists is untouched. -/
theorem frame_of_lists {d : Domain} {p : Problem} {o : AtomOp} (hf : OpFacts d p o)
    {add del : List GroundAtom} (hadd : hf.inst.add = add) (hdel : hf.inst.del = del)
    {a : GroundAtom} (ha : a ∉ add) (hd : a ∉ del) (σ : AtomState) :
    o.applyA σ a = σ a :=
  applyA_frame σ (fun hmem => ha (hadd ▸ hf.subAdd a hmem))
    (fun hmem => hd (hdel ▸ hf.subDel a hmem))

/-- An atom the operator cannot add is true afterwards only if it was true before. -/
theorem falls_of_lists {d : Domain} {p : Problem} {o : AtomOp} (hf : OpFacts d p o)
    {add : List GroundAtom} (hadd : hf.inst.add = add)
    {a : GroundAtom} (ha : a ∉ add) {σ : AtomState}
    (h : o.applyA σ a = true) : σ a = true := by
  have hna : a ∉ o.add := fun hmem => ha (hadd ▸ hf.subAdd a hmem)
  by_cases hdl : a ∈ o.del
  · rw [applyA_del σ hdl hna] at h; exact absurd h (by simp)
  · rwa [applyA_frame σ hna hdl] at h

/-- An atom the operator cannot delete is false before whenever it is false
afterwards. -/
theorem persists_false_of_lists {d : Domain} {p : Problem} {o : AtomOp}
    (hf : OpFacts d p o) {del : List GroundAtom} (hdel : hf.inst.del = del)
    {a : GroundAtom} (hd : a ∉ del) {σ : AtomState}
    (h : o.applyA σ a = false) : σ a = false := by
  have hnd : a ∉ o.del := fun hmem => hd (hdel ▸ hf.subDel a hmem)
  by_cases ha : a ∈ o.add
  · rw [applyA_add σ ha] at h
    contradiction
  · rwa [applyA_frame σ ha hnd] at h

/-- A delete the operator also reads, and does not add back, really falls. -/
theorem falsified_of_lists {d : Domain} {p : Problem} {o : AtomOp} (hf : OpFacts d p o)
    {add del : List GroundAtom} (hadd : hf.inst.add = add) (hdel : hf.inst.del = del)
    {a : GroundAtom} (ha : a ∉ add) (hmem : a ∈ del) (hpre : a ∈ hf.inst.pre)
    (hdyn : (staticPredicates d).contains a.pred = false) (σ : AtomState) :
    o.applyA σ a = false :=
  applyA_del σ (del_kept hf (hdel ▸ hmem) (fun hc => ha (hadd ▸ hc)) hpre hdyn)
    (fun hmem => ha (hadd ▸ hf.subAdd a hmem))

/-- And on the unpruned task, an add the operator does not already read really holds. -/
theorem asserted_of_lists {d : Domain} {p : Problem} {o : AtomOp} (hfa : OpFactsAdd d p o)
    {y : Atom} (hy : y ∈ hfa.inst.schema.add)
    (hpre : instAtom hfa.inst.schema.params hfa.inst.args y ∉ o.pre) (σ : AtomState) :
    o.applyA σ (instAtom hfa.inst.schema.params hfa.inst.args y) = true :=
  applyA_add σ (hfa.addComplete y hy hpre)

/-! ### Objects of one type -/

/-- A well-typed argument is one of the objects the tables index, when the type
has no proper subtype among the objects. -/
theorem mem_objsOf_of_wellTyped {d : Domain} {p : Problem} {rel : Bool} {ty l : Name}
    (hty : ∀ o ∈ allObjects d p, d.isSubtype o.type ty = true → o.type = ty)
    (hw : WellTyped d (allObjects d p) ty l) :
    l ∈ (ground d p rel).objectsOfTypes [ty] := by
  obtain ⟨ob, hob, hname, hsub⟩ := hw
  exact mem_objsOf hob hname (hty ob hob hsub)

/-- Arguments of two types that do not nest are different objects. -/
theorem ne_of_types {d : Domain} {p : Problem} {ty₁ ty₂ a b : Name}
    (hnd : ((allObjects d p).map (·.name)).Nodup)
    (hdisj : ∀ o ∈ allObjects d p, d.isSubtype o.type ty₁ = true →
      d.isSubtype o.type ty₂ = false)
    (h1 : WellTyped d (allObjects d p) ty₁ a)
    (h2 : WellTyped d (allObjects d p) ty₂ b) : a ≠ b := by
  intro hab
  obtain ⟨o1, ho1, hn1, hs1⟩ := h1
  obtain ⟨o2, ho2, hn2, hs2⟩ := h2
  have hsame : o1 = o2 :=
    List.inj_on_of_nodup_map hnd ho1 ho2 (by rw [hn1, hn2, hab])
  subst hsame
  rw [hdisj o1 ho1 hs1] at hs2
  exact Bool.noConfusion hs2

/-- And an object of one type is not one of another's, when the names are
distinct and the types do not nest. -/
theorem not_mem_objsOf_of_wellTyped {d : Domain} {p : Problem} {rel : Bool}
    {ty₁ ty₂ q : Name}
    (hnd : ((allObjects d p).map (·.name)).Nodup)
    (hdisj : ∀ o ∈ allObjects d p, o.type = ty₂ → d.isSubtype o.type ty₁ = false)
    (hw : WellTyped d (allObjects d p) ty₁ q) :
    q ∉ (ground d p rel).objectsOfTypes [ty₂] := by
  intro hmem
  obtain ⟨ob, hob, hname, hty⟩ := mem_objectsOfTypes hmem
  obtain ⟨ob2, hob2, hname2, hsub2⟩ := hw
  have hob' : ob ∈ allObjects d p := by
    have h2 : ob ∈ (allObjects d p).toArray := hob
    simpa using h2
  have hsame : ob = ob2 :=
    List.inj_on_of_nodup_map hnd hob' hob2 (by rw [hname, hname2])
  subst hsame
  have hty2 : ob.type = ty₂ := by simpa using hty
  rw [hdisj ob hob' hty2] at hsub2
  exact Bool.noConfusion hsub2


/-! ### Reading `:init` by predicate

Every domain's initial-state check asks the same two questions of `:init`: which
one-argument atoms of a predicate it holds, and which two-argument ones.  Both
are one pass, and the membership equations are what turn the check into the
invariant.
-/

/-- The argument pairs of one two-argument predicate in `:init`. -/
def initPairs (p : Problem) (pred : Name) : List (Name × Name) :=
  p.init.filterMap fun a =>
    match a.pred == pred, a.args with
    | true, [x, y] => some (x, y)
    | _, _ => none

/-- And the arguments of one one-argument predicate. -/
def initOnes (p : Problem) (pred : Name) : List Name :=
  p.init.filterMap fun a =>
    match a.pred == pred, a.args with
    | true, [x] => some x
    | _, _ => none

theorem mem_initPairs {p : Problem} {pred x y : Name} :
    (x, y) ∈ initPairs p pred ↔ ({ pred := pred, args := [x, y] } : GroundAtom) ∈ p.init := by
  constructor
  · intro h
    obtain ⟨a, ha, hval⟩ := List.mem_filterMap.mp h
    by_cases hp : (a.pred == pred) = true
    · rcases hargs : a.args with _ | ⟨u, rest⟩
      · rw [hargs] at hval; simp only [hp] at hval; simp at hval
      · cases rest with
        | nil => rw [hargs] at hval; simp only [hp] at hval; simp at hval
        | cons v t =>
            cases t with
            | cons _ _ => rw [hargs] at hval; simp only [hp] at hval; simp at hval
            | nil =>
                rw [hargs] at hval
                simp only [hp, Option.some.injEq, Prod.mk.injEq] at hval
                obtain ⟨rfl, rfl⟩ := hval
                have hpred : a.pred = pred := by simpa using hp
                have heq : ({ pred := pred, args := [u, v] } : GroundAtom) = a := by
                  rw [← hpred, ← hargs]
                rw [heq]; exact ha
    · simp only [Bool.not_eq_true] at hp
      rw [hp] at hval; simp at hval
  · intro h
    refine List.mem_filterMap.mpr ⟨_, h, ?_⟩
    simp

/-- And the argument triples of one three-argument predicate. -/
def initTriples (p : Problem) (pred : Name) : List (Name × Name × Name) :=
  p.init.filterMap fun a =>
    match a.pred == pred, a.args with
    | true, [x, y, z] => some (x, y, z)
    | _, _ => none

theorem mem_initTriples {p : Problem} {pred x y z : Name} :
    (x, y, z) ∈ initTriples p pred ↔
      ({ pred := pred, args := [x, y, z] } : GroundAtom) ∈ p.init := by
  constructor
  · intro h
    obtain ⟨a, ha, hval⟩ := List.mem_filterMap.mp h
    by_cases hp : (a.pred == pred) = true
    · rcases hargs : a.args with _ | ⟨u, rest⟩
      · rw [hargs] at hval; simp only [hp] at hval; simp at hval
      · cases rest with
        | nil => rw [hargs] at hval; simp only [hp] at hval; simp at hval
        | cons v rest =>
            cases rest with
            | nil => rw [hargs] at hval; simp only [hp] at hval; simp at hval
            | cons w rest =>
                cases rest with
                | cons _ _ => rw [hargs] at hval; simp only [hp] at hval; simp at hval
                | nil =>
                    rw [hargs] at hval
                    simp only [hp, Option.some.injEq, Prod.mk.injEq] at hval
                    obtain ⟨rfl, rfl, rfl⟩ := hval
                    have hpred : a.pred = pred := by simpa using hp
                    have heq : ({ pred := pred, args := [u, v, w] } : GroundAtom) = a := by
                      rw [← hpred, ← hargs]
                    rw [heq]; exact ha
    · simp only [Bool.not_eq_true] at hp
      rw [hp] at hval; simp at hval
  · intro h
    refine List.mem_filterMap.mpr ⟨_, h, ?_⟩
    simp

theorem mem_initOnes {p : Problem} {pred x : Name} :
    x ∈ initOnes p pred ↔ ({ pred := pred, args := [x] } : GroundAtom) ∈ p.init := by
  constructor
  · intro h
    obtain ⟨a, ha, hval⟩ := List.mem_filterMap.mp h
    by_cases hp : (a.pred == pred) = true
    · rcases hargs : a.args with _ | ⟨u, rest⟩
      · rw [hargs] at hval; simp only [hp] at hval; simp at hval
      · cases rest with
        | cons _ _ => rw [hargs] at hval; simp only [hp] at hval; simp at hval
        | nil =>
            rw [hargs] at hval
            simp only [hp, Option.some.injEq] at hval
            subst hval
            have hpred : a.pred = pred := by simpa using hp
            have heq : ({ pred := pred, args := [u] } : GroundAtom) = a := by
              rw [← hpred, ← hargs]
            rw [heq]; exact ha
    · simp only [Bool.not_eq_true] at hp
      rw [hp] at hval; simp at hval
  · intro h
    refine List.mem_filterMap.mpr ⟨_, h, ?_⟩
    simp


/-! ### What the relevance analysis leaves of an operator

The pruned operators are the raw ones with their add and delete lists filtered by
the relevant set.  Two things follow, and a domain that reads a position off an
add needs both: the operator the analysis kept touches the set, so everything it
reads is relevant, and an add survives exactly when its atom is.
-/

theorem pruned_op {d : Domain} {p : Problem} {op' : AtomOp}
    (hop' : op' ∈ groundedOps d p true) {r : Std.HashSet GroundAtom}
    (hclosed : Closed (rawOps d p) r)
    (hrdef : relevanceAnalysis (rawOps d p) p.goal.toArray
      = (rawOps d p).filterMap fun op =>
        if ((op.add.filter r.contains).isEmpty && (op.del.filter r.contains).isEmpty)
        then none else some (AtomOp.trim op r)) :
    ∃ op ∈ rawOps d p, op' = op.trim r ∧ (∀ f ∈ op.pre, r.contains f = true) ∧
      op.touches r = true := by
  rw [groundedOps_true, hrdef, Array.mem_filterMap] at hop'
  obtain ⟨op, hop, hval⟩ := hop'
  split at hval
  · exact absurd hval (by simp)
  · rename_i hguard
    have htouch : op.touches r = true := by
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hguard
      unfold AtomOp.touches
      rcases hA : (op.add.filter r.contains).isEmpty with _ | _
      · have : ∃ x ∈ op.add, r.contains x = true := by
          by_contra hc
          have : op.add.filter r.contains = #[] := by
            rw [Array.filter_eq_empty_iff]
            intro x hx
            simp only [Bool.not_eq_true]
            by_contra hcc
            exact hc ⟨x, hx, by simpa using hcc⟩
          rw [this] at hA
          simp at hA
        obtain ⟨x, hx, hrx⟩ := this
        have : op.add.any r.contains = true := by
          rw [← Array.any_toList]
          exact List.any_eq_true.mpr ⟨x, by simpa using hx, hrx⟩
        rw [this]; rfl
      · have hD : (op.del.filter r.contains).isEmpty = false := by
          by_contra hc
          simp only [Bool.not_eq_false] at hc
          exact hguard ⟨hA, hc⟩
        have : ∃ x ∈ op.del, r.contains x = true := by
          by_contra hc
          have : op.del.filter r.contains = #[] := by
            rw [Array.filter_eq_empty_iff]
            intro x hx
            simp only [Bool.not_eq_true]
            by_contra hcc
            exact hc ⟨x, hx, by simpa using hcc⟩
          rw [this] at hD
          simp at hD
        obtain ⟨x, hx, hrx⟩ := this
        have hany : op.del.any r.contains = true := by
          rw [← Array.any_toList]
          exact List.any_eq_true.mpr ⟨x, by simpa using hx, hrx⟩
        rw [hany]; simp
    exact ⟨op, hop, by simpa using hval.symm, hclosed op hop htouch, htouch⟩

/-- An add survives the analysis exactly when its atom is relevant. -/
theorem add_of_trim {op op' : AtomOp} {r : Std.HashSet GroundAtom}
    (h : op' = op.trim r) {a : GroundAtom} (ha : a ∈ op.add)
    (hr : r.contains a = true) : a ∈ op'.add := by
  rw [h]
  show a ∈ op.add.filter r.contains
  exact Array.mem_filter.mpr ⟨ha, hr⟩


/--
The pruned operator, with its instance and the adds the analysis kept.

`opFacts_pruned` throws the instance away and returns only `Nonempty`, which is
enough for a domain that reads nothing off an add.  A domain that does read one
needs the instance and the add together, so this returns both.
-/
theorem opFacts_pruned_add (d : Domain) (p : Problem) {o : AtomOp}
    (ho : o ∈ groundedOps d p true) {r : Std.HashSet GroundAtom}
    (hclosed : Closed (rawOps d p) r)
    (hrdef : relevanceAnalysis (rawOps d p) p.goal.toArray
      = (rawOps d p).filterMap fun op =>
        if ((op.add.filter r.contains).isEmpty && (op.del.filter r.contains).isEmpty)
        then none else some (AtomOp.trim op r)) :
    ∃ hf : OpFacts d p o,
      (∀ f ∈ o.pre, r.contains f = true) ∧
      ∀ y ∈ hf.inst.schema.add,
        instAtom hf.inst.schema.params hf.inst.args y ∉ o.pre →
        r.contains (instAtom hf.inst.schema.params hf.inst.args y) = true →
        instAtom hf.inst.schema.params hf.inst.args y ∈ o.add := by
  obtain ⟨op, hop, hval, hpre, -⟩ := pruned_op ho hclosed hrdef
  subst hval
  obtain ⟨hfa⟩ := opFacts_raw_add d p hop
  refine ⟨⟨hfa.inst, ?_, ?_, ?_, ?_, hfa.staticHeld, ?_, hfa.cost⟩, hpre, ?_⟩
  · intro a ha; exact hfa.subPre a ha
  · intro a ha; exact hfa.subAdd a (Array.mem_filter.mp ha).1
  · intro a ha; exact hfa.subDel a (Array.mem_filter.mp ha).1
  · intro y hy hdyn; exact hfa.preComplete y hy hdyn
  · intro y hy hn hp2
    exact Array.mem_filter.mpr ⟨hfa.delComplete y hy hn hp2, hpre _ hp2⟩
  · intro y hy hnp hr
    exact Array.mem_filter.mpr ⟨hfa.addComplete y hy hnp, hr⟩


end Planner
