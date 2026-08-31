/-
Grounding is complete: every well-typed instance is produced.

`Proofs/GroundingSound.lean` proves one direction — every operator the grounder
emits is a well-typed instance of a schema.  This file proves the converse, which
is what the compiled heuristics need: if a schema has an assignment of well-typed
objects whose *static* preconditions hold in `:init`, then the grounder really
does emit the operator for it, and so every atom that instance mentions receives a
fact number.

That last step is the point.  A compiled heuristic reads a table of facts and asks
"is there an entry for this object?".  The answer is yes exactly when the atom was
numbered, and the atom was numbered exactly when some operator mentions it.  Only
the completeness direction can say so.

Static preconditions are the one exception, by design: `groundSchema` drops a
static atom that holds and discards the operator when it does not, so a static
atom is never numbered.  Every statement below is therefore about the *dynamic*
preconditions, the adds and the deletes.
-/
import Proofs.GroundingSound

namespace Planner

open Planner.Pddl

/-! ### The operator a full assignment builds

`mkOp` is the record `groundSchema.go` pushes once every parameter is bound.  It
is spelled out here so that completeness can name the operator it claims to find,
rather than only assert that one exists.
-/

/-- The operator `groundSchema.go` pushes at a full assignment. -/
def mkOp (a : Action) (dyn : List Atom) (assign : Array Name) : AtomOp :=
  let pre := dedup (((dyn.map (compileAtom a.params)).map (instantiateSlots assign)).toArray)
  let add := dedup (((a.add.map (compileAtom a.params)).map (instantiateSlots assign)).toArray)
  let del := dedup (((a.del.map (compileAtom a.params)).map (instantiateSlots assign)).toArray)
  { name := opName a.name assign
    pre
    add := add.filter (fun x => !pre.contains x)
    del := del.filter (fun x => !add.contains x)
    cost := a.cost }

/-! ### The walk only ever grows its accumulator -/

private theorem foldl_keep {α : Type} {q : AtomOp} (f : Array AtomOp → α → Array AtomOp)
    (hmono : ∀ acc o, q ∈ acc → q ∈ f acc o) :
    ∀ (l : List α) (acc : Array AtomOp), q ∈ acc → q ∈ l.foldl f acc := by
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons x xs ih => intro acc h; exact ih _ (hmono acc x h)

private theorem foldl_hit {α : Type} {q : AtomOp} {o : α} (f : Array AtomOp → α → Array AtomOp)
    (hmono : ∀ acc x, q ∈ acc → q ∈ f acc x) (hhit : ∀ acc, q ∈ f acc o) :
    ∀ (l : List α), o ∈ l → ∀ acc, q ∈ l.foldl f acc := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons x xs ih =>
      intro hx acc
      rcases List.mem_cons.mp hx with rfl | h
      · exact foldl_keep f hmono xs _ (hhit acc)
      · exact ih h _

/-- Nothing already found is lost as the walk continues. -/
theorem go_mono (types : Std.HashMap Name (Array Name)) (init : Std.HashSet GroundAtom)
    (a : Action) (index : Std.HashMap Name (Array GroundAtom))
    (dyn add del : List SlotAtom) (checkAt : Nat → List SlotAtom) :
    ∀ (rest : List TypedName) (assign : Array Name) (acc : Array AtomOp) (q : AtomOp),
      q ∈ acc → q ∈ groundSchema.go types init a index dyn add del checkAt rest assign acc := by
  intro rest
  induction rest with
  | nil =>
      intro assign acc q hq
      rw [groundSchema.go]
      exact Array.mem_push.mpr (Or.inl hq)
  | cons p rest ih =>
      intro assign acc q hq
      rw [groundSchema.go, ← Array.foldl_toList]
      refine foldl_keep (q := q) _ ?_ _ acc hq
      intro acc' o hq'
      by_cases hchk : (checkAt (assign.push o).size).all
          (staticCompatible init index (assign.push o))
      · simp only [hchk, if_true]; exact ih _ _ q hq'
      · simp only [hchk, Bool.false_eq_true, if_false]; exact hq'

/-! ### A prefix of an assignment instantiates a low-level atom the same way -/

theorem instantiateSlots_prefix {params : List TypedName} {atom : Atom}
    {assign full : Array Name} (hpre : assign.toList <+: full.toList)
    (h : (compileAtom params atom).level ≤ assign.size) :
    instantiateSlots assign (compileAtom params atom)
      = instantiateSlots full (compileAtom params atom) := by
  unfold instantiateSlots
  simp only [GroundAtom.mk.injEq, true_and]
  refine List.map_congr_left ?_
  intro sl hsl
  cases sl with
  | obj n => rfl
  | param i =>
      have hi : i + 1 ≤ (compileAtom params atom).level :=
        compileAtom_param_lt (by simpa using hsl)
      have hlt : i < assign.toList.length := by simpa using (by omega : i < assign.size)
      show assign.getD i "" = full.getD i ""
      rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
      have hlt2 : i < full.size := by
        have := hpre.length_le
        simp only [Array.length_toList] at this
        simp only [Array.length_toList] at hlt
        omega
      rw [Array.getElem?_eq_getElem (by simp only [Array.length_toList] at hlt; omega),
        Array.getElem?_eq_getElem hlt2]
      simpa using hpre.getElem hlt

/-- Every initial fact occurs in its predicate bucket. -/
theorem staticFactIndex_mem (init : Std.HashSet GroundAtom) {fact : GroundAtom}
    (hfact : fact ∈ init.toList) :
    fact ∈ (staticFactIndex init).getD fact.pred #[] := by
  unfold staticFactIndex
  have go : ∀ (facts : List GroundAtom) (index : Std.HashMap Name (Array GroundAtom)),
      (fact ∈ facts ∨ fact ∈ index.getD fact.pred #[]) →
      fact ∈ (facts.foldl (fun index atom =>
        index.insert atom.pred ((index.getD atom.pred #[]).push atom)) index).getD
          fact.pred #[] := by
    intro facts
    induction facts with
    | nil =>
        intro index h
        simpa using h
    | cons atom rest ih =>
        intro index h
        apply ih
        rcases h with h | h
        · rcases List.mem_cons.mp h with rfl | hrest
          · exact Or.inr (by
              rw [Std.HashMap.getD_insert]
              simp)
          · exact Or.inl hrest
        · refine Or.inr ?_
          rw [Std.HashMap.getD_insert]
          split
          · rename_i heq
            have hp : atom.pred = fact.pred := by simpa using heq
            rw [hp]
            exact Array.mem_push.mpr (Or.inl h)
          · exact h
  exact go init.toList {} (Or.inl hfact)

/-- A bound parameter reads the same value from every extending assignment. -/
private theorem slot_matchesPrefix_full {assign full : Array Name}
    (hpre : assign.toList <+: full.toList) (slot : Slot) :
    slot.matchesPrefix assign
      (match slot with | .param i => full.getD i "" | .obj name => name) = true := by
  cases slot with
  | obj name => simp [Slot.matchesPrefix]
  | param i =>
      by_cases hi : i < assign.size
      · have hifull : i < full.size := by
          have := hpre.length_le
          simp only [Array.length_toList] at this
          omega
        rw [Slot.matchesPrefix, Array.getElem?_eq_getElem hi]
        simp only [beq_iff_eq]
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hifull]
        simpa using (hpre.getElem (by simpa using hi)).symm
      · have hnone : assign[i]? = none := Array.getElem?_eq_none (by omega)
        simp [Slot.matchesPrefix, hnone]

/-- Instantiating a full assignment supplies a witness for every prefix. -/
private theorem slotsMatchPrefix_full {assign full : Array Name}
    (hpre : assign.toList <+: full.toList) : ∀ slots : List Slot,
    slotsMatchPrefix assign slots (slots.map fun
      | .param i => full.getD i ""
      | .obj name => name) = true := by
  intro slots
  induction slots with
  | nil => rfl
  | cons slot rest ih =>
      simp only [List.map_cons, slotsMatchPrefix, Bool.and_eq_true]
      exact ⟨slot_matchesPrefix_full hpre slot, ih⟩

theorem matchesPrefix_instantiate {assign full : Array Name}
    (hpre : assign.toList <+: full.toList) (slotAtom : SlotAtom) :
    slotAtom.matchesPrefix assign (instantiateSlots full slotAtom) = true := by
  unfold SlotAtom.matchesPrefix instantiateSlots
  simp only [beq_self_eq_true, Bool.true_and]
  exact slotsMatchPrefix_full hpre slotAtom.slots.toList

/-! ### Every well-typed assignment is walked

`go_complete` is the converse of `go_produced`: given objects for the parameters
still unbound and the guarantee that every static precondition of the *finished*
assignment holds in `:init`, the walk reaches the leaf and pushes `mkOp`.

The static checks along the way are the only thing to arrange.  A static atom is
tested as soon as its last parameter is bound, and at that moment the partial
assignment already agrees with the finished one on every slot the atom reads —
that is `instantiateSlots_prefix`.
-/

theorem go_complete (types : Std.HashMap Name (Array Name)) (init : Std.HashSet GroundAtom)
    (a : Action) (checkAt : Nat → List SlotAtom) (dyn stat : List Atom)
    (hcheck : ∀ k, checkAt k = stat.map (compileAtom a.params))
    (full : Array Name) (hfull : full.size = a.params.length)
    (hstat : ∀ y ∈ stat,
      init.contains (instantiateSlots full (compileAtom a.params y)) = true) :
    ∀ (rest : List TypedName) (assign : Array Name) (acc : Array AtomOp)
      (pfx : List TypedName), a.params = pfx ++ rest → assign.size = pfx.length →
      assign.toList <+: full.toList →
      List.Forall₂ (fun (p : TypedName) (o : Name) => o ∈ types.getD p.type #[]) rest
        (full.toList.drop assign.size) →
      mkOp a dyn full ∈ groundSchema.go types init a (staticFactIndex init)
        (dyn.map (compileAtom a.params))
        (a.add.map (compileAtom a.params)) (a.del.map (compileAtom a.params))
        checkAt rest assign acc := by
  intro rest
  induction rest with
  | nil =>
      intro assign acc pfx hparams hsz hp _
      have hlen : assign.size = full.size := by
        rw [hsz, hfull, hparams]; simp
      have heq : assign = full := by
        apply Array.ext'
        exact hp.eq_of_length (by simpa using hlen)
      subst heq
      rw [groundSchema.go]
      exact Array.mem_push.mpr (Or.inr rfl)
  | cons p rest ih =>
      intro assign acc pfx hparams hsz hp hall
      -- The finished assignment supplies the object for `p`.
      have hsplit : full.toList = assign.toList ++ full.toList.drop assign.size := by
        have h : assign.toList = full.toList.take assign.size := by
          simpa using List.prefix_iff_eq_take.mp hp
        rw [h, List.take_append_drop]
      cases hdrop : full.toList.drop assign.size with
      | nil => rw [hdrop] at hall; exact absurd hall (by simp)
      | cons o tail =>
          rw [hdrop] at hall
          obtain ⟨hmem, hrest⟩ := List.forall₂_cons.mp hall
          have hpush : (assign.push o).toList <+: full.toList := by
            rw [hsplit, hdrop]
            simp
          have hpsz : (assign.push o).size = assign.size + 1 := by simp
          -- Every static precondition has the finished assignment as a witness.
          have hchk : (checkAt (assign.push o).size).all
              (staticCompatible init (staticFactIndex init) (assign.push o)) = true := by
            rw [List.all_eq_true]
            intro sl hsl
            rw [hcheck] at hsl
            have hmap := hsl
            rw [List.mem_map] at hmap
            obtain ⟨y, hy, rfl⟩ := hmap
            unfold staticCompatible
            split
            · rename_i hle
              rw [instantiateSlots_prefix hpush hle]
              exact hstat y hy
            · let fact := instantiateSlots full (compileAtom a.params y)
              refine Array.any_eq_true'.mpr ⟨fact, ?_, matchesPrefix_instantiate hpush _⟩
              change fact ∈ (staticFactIndex init).getD fact.pred #[]
              apply staticFactIndex_mem
              simpa using hstat y hy
          rw [groundSchema.go, ← Array.foldl_toList]
          refine foldl_hit (o := o) _ ?_ ?_ _ (by simpa using hmem) acc
          · intro acc' x hq
            by_cases hc : (checkAt (assign.push x).size).all
                (staticCompatible init (staticFactIndex init) (assign.push x))
            · simp only [hc, if_true]; exact go_mono _ _ _ _ _ _ _ _ _ _ _ _ hq
            · simp only [hc, Bool.false_eq_true, if_false]; exact hq
          · intro acc'
            simp only [hchk, if_true]
            refine ih (assign.push o) acc' (pfx ++ [p]) (by simp [hparams]) (by simp [hsz])
              hpush ?_
            rw [hpsz]
            have : full.toList.drop (assign.size + 1) = tail := by
              rw [← List.tail_drop, hdrop]; rfl
            rw [this]
            exact hrest

/-! ### The candidate lists hold every well-typed object

`typeObjects_wellTyped` says the lists hold nothing else; this is the converse.
The type has to be one the domain declares — validation checks that of every
parameter type, so it costs a schema nothing.
-/

theorem typeObjects_mem (d : Domain) (objects : List TypedName) {ty o : Name}
    (hty : ty ∈ d.typeNames) (h : WellTyped d objects ty o) :
    o ∈ (typeObjects d objects).getD ty #[] := by
  set members := ((objects.filter fun y => d.isSubtype y.type ty).map (·.name)).toArray
    with hmembers
  have key : ∀ (l : List Name) (m : Std.HashMap Name (Array Name)),
      (ty ∈ l ∨ m.getD ty #[] = members) →
      (l.foldl (fun r u =>
        r.insert u ((objects.filter fun y => d.isSubtype y.type u).map (·.name)).toArray)
        m).getD ty #[] = members := by
    intro l
    induction l with
    | nil =>
        intro m hm
        rcases hm with h1 | h1
        · simp at h1
        · exact h1
    | cons u rest ih =>
        intro m hm
        refine ih _ ?_
        by_cases hr : ty ∈ rest
        · exact Or.inl hr
        · refine Or.inr ?_
          by_cases hu : u = ty
          · subst hu
            rw [Std.HashMap.getD_insert]
            simp [hmembers]
          · rw [Std.HashMap.getD_insert]
            have : ¬ (u == ty) = true := by simp [hu]
            simp only [this, if_false]
            rcases hm with h1 | h1
            · rcases List.mem_cons.mp h1 with rfl | h2
              · exact absurd rfl hu
              · exact absurd h2 hr
            · exact h1
  have hval : (typeObjects d objects).getD ty #[] = members := by
    unfold typeObjects
    simpa using key d.typeNames ∅ (Or.inl hty)
  rw [hval, hmembers]
  obtain ⟨decl, hdecl, hname, hsub⟩ := h
  simp only [List.mem_toArray, List.mem_map, List.mem_filter]
  exact ⟨decl, ⟨hdecl, hsub⟩, hname⟩

/-! ### The domain's schemas are grounded one after another -/

private theorem foldl_append_keep {q : AtomOp} (g : Action → Array AtomOp) :
    ∀ (l : List Action) (acc : Array AtomOp), q ∈ acc →
      q ∈ l.foldl (fun r b => r ++ g b) acc := by
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons b bs ih => intro acc h; exact ih _ (by simp [h])

private theorem foldl_append_hit {q : AtomOp} {a : Action}
    (g : Action → Array AtomOp) (hq : q ∈ g a) :
    ∀ (l : List Action), a ∈ l → ∀ acc, q ∈ l.foldl (fun r b => r ++ g b) acc := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons b bs ih =>
      intro hb acc
      rcases List.mem_cons.mp hb with rfl | h
      · exact foldl_append_keep g bs _ (by simp [hq])
      · exact ih h _

/-! ### One schema, and then the whole domain -/

/-- Every well-typed assignment whose static preconditions hold is grounded. -/
theorem groundSchema_complete (d : Domain) (types : Std.HashMap Name (Array Name))
    (statics : List Name) (init : Std.HashSet GroundAtom) (a : Action)
    (full : Array Name) (hfull : full.size = a.params.length)
    (hcand : List.Forall₂ (fun (pm : TypedName) (o : Name) => o ∈ types.getD pm.type #[])
      a.params full.toList)
    (hstat : ∀ y ∈ a.pre, statics.contains y.pred = true →
      init.contains (instAtom a.params full.toList y) = true) :
    mkOp a (a.pre.filter fun x => !statics.contains x.pred) full
      ∈ groundSchema d types statics init a := by
  have hcheck : ∀ k : Nat,
      (fun (_ : Nat) => (a.pre.filter fun x => statics.contains x.pred).map
        (compileAtom a.params)) k =
      (a.pre.filter fun x => statics.contains x.pred).map
        (compileAtom a.params) := by
    intro k
    rfl
  have hstat' : ∀ y ∈ a.pre.filter fun x => statics.contains x.pred,
      init.contains (instantiateSlots full (compileAtom a.params y)) = true := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := List.mem_filter.mp hy
    rw [instantiate_compile]
    exact hstat y hy1 hy2
  unfold groundSchema
  simp only
  rw [if_pos]
  · refine go_complete types init a _ _
      (a.pre.filter fun x => statics.contains x.pred) hcheck full hfull hstat'
      a.params #[] #[] [] (by simp) (by simp) (by simp) ?_
    simpa using hcand
  · rw [List.all_eq_true]
    intro sl hsl
    have hmap := hsl
    rw [List.mem_map] at hmap
    obtain ⟨y, hy, rfl⟩ := hmap
    unfold staticCompatible
    split
    · rename_i hle
      rw [instantiateSlots_prefix (full := full) (by simp) hle]
      exact hstat' y hy
    · let fact := instantiateSlots full (compileAtom a.params y)
      refine Array.any_eq_true'.mpr ⟨fact, ?_, matchesPrefix_instantiate (by simp) _⟩
      change fact ∈ (staticFactIndex init).getD fact.pred #[]
      apply staticFactIndex_mem
      simpa using hstat' y hy

/-- And so the grounder, before pruning, emits the operator for every instance. -/
theorem groundedOps_complete (d : Domain) (p : Problem) {a : Action} (ha : a ∈ d.actions)
    (full : Array Name) (hfull : full.size = a.params.length)
    (hty : ∀ pm ∈ a.params, pm.type ∈ d.typeNames)
    (hwt : List.Forall₂ (fun (pm : TypedName) (o : Name) =>
      WellTyped d (allObjects d p) pm.type o) a.params full.toList)
    (hstat : ∀ y ∈ a.pre, (staticPredicates d).contains y.pred = true →
      instAtom a.params full.toList y ∈ p.init) :
    mkOp a (a.pre.filter fun x => !(staticPredicates d).contains x.pred) full
      ∈ groundedOps d p false := by
  set types := typeObjects d (allObjects d p) with htypes
  have key : ∀ (ps : List TypedName) (os : List Name),
      List.Forall₂ (fun (pm : TypedName) (o : Name) =>
        WellTyped d (allObjects d p) pm.type o) ps os →
      (∀ pm ∈ ps, pm.type ∈ d.typeNames) →
      List.Forall₂ (fun (pm : TypedName) (o : Name) => o ∈ types.getD pm.type #[]) ps os := by
    intro ps os h
    induction h with
    | nil => intro _; exact List.Forall₂.nil
    | @cons pm o ps' os' hh hs ih =>
        intro hty'
        exact List.Forall₂.cons (typeObjects_mem d _ (hty' pm (by simp)) hh)
          (ih (fun q hq => hty' q (by simp [hq])))
  have hcand := key a.params full.toList hwt hty
  have hstat' : ∀ y ∈ a.pre, (staticPredicates d).contains y.pred = true →
      (Std.HashSet.ofList p.init).contains (instAtom a.params full.toList y) = true := by
    intro y hy hp'
    simpa using hstat y hy hp'
  have hmem := groundSchema_complete d types (staticPredicates d) (Std.HashSet.ofList p.init)
    a full hfull hcand hstat'
  rw [groundedOps_false]
  unfold rawOps
  exact foldl_append_hit _ hmem d.actions ha #[]

/-! ### Every atom an instance mentions is numbered

This is what the compiled heuristics need.  A dynamic precondition lands in the
operator's precondition list.  An add lands in the add list unless it is already a
precondition, and a delete lands in the delete list unless it is also added — so
in every case the atom is somewhere in `op.pre ++ op.add ++ op.del`, which is what
`allAtoms` collects and `factIndex` numbers.

Static preconditions are deliberately absent: the grounder checks them against
`:init` and drops them, so they are never numbered and a heuristic must read them
from `staticAtoms` instead.
-/

/-- A dynamic precondition of the instance is a precondition of the operator. -/
theorem mem_mkOp_pre (a : Action) (dyn : List Atom) (full : Array Name) {y : Atom}
    (hy : y ∈ dyn) : instAtom a.params full.toList y ∈ (mkOp a dyn full).pre := by
  show instAtom a.params full.toList y
    ∈ dedup (((dyn.map (compileAtom a.params)).map (instantiateSlots full)).toArray)
  refine dedup_mem ?_
  rw [List.mem_toArray, List.mem_map]
  exact ⟨compileAtom a.params y, List.mem_map.mpr ⟨y, hy, rfl⟩,
    instantiate_compile a.params full y⟩

theorem mem_mkOp (a : Action) (dyn : List Atom) (full : Array Name) {y : Atom}
    (hy : y ∈ dyn ∨ y ∈ a.add ∨ y ∈ a.del) :
    instAtom a.params full.toList y ∈ (mkOp a dyn full).pre ∨
    instAtom a.params full.toList y ∈ (mkOp a dyn full).add ∨
    instAtom a.params full.toList y ∈ (mkOp a dyn full).del := by
  set P := dedup (((dyn.map (compileAtom a.params)).map (instantiateSlots full)).toArray)
    with hP
  set A := dedup (((a.add.map (compileAtom a.params)).map (instantiateSlots full)).toArray)
    with hA
  set D := dedup (((a.del.map (compileAtom a.params)).map (instantiateSlots full)).toArray)
    with hD
  have hpre : (mkOp a dyn full).pre = P := rfl
  have hadd : (mkOp a dyn full).add = A.filter (fun x => !P.contains x) := rfl
  have hdel : (mkOp a dyn full).del = D.filter (fun x => !A.contains x) := rfl
  rw [hpre, hadd, hdel]
  have inst : ∀ (l : List Atom) (z : Atom), z ∈ l →
      instAtom a.params full.toList z
        ∈ dedup (((l.map (compileAtom a.params)).map (instantiateSlots full)).toArray) := by
    intro l z hz
    refine dedup_mem ?_
    rw [List.mem_toArray, List.mem_map]
    exact ⟨compileAtom a.params z, List.mem_map.mpr ⟨z, hz, rfl⟩,
      instantiate_compile a.params full z⟩
  -- An atom the operator adds is either already a precondition or kept as an add.
  have addOrPre : ∀ z : GroundAtom, z ∈ A →
      z ∈ P ∨ z ∈ A.filter (fun x => !P.contains x) := by
    intro z hz
    by_cases hp : z ∈ P
    · exact Or.inl hp
    · exact Or.inr (Array.mem_filter.mpr ⟨hz, by simpa using hp⟩)
  rcases hy with hy | hy | hy
  · exact Or.inl (hP ▸ inst dyn y hy)
  · rcases addOrPre _ (hA ▸ inst a.add y hy) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · by_cases hadd2 : instAtom a.params full.toList y ∈ A
    · rcases addOrPre _ hadd2 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Array.mem_filter.mpr ⟨hD ▸ inst a.del y hy,
        by simpa using hadd2⟩))

private theorem inst_of_mem_dedup {params : List TypedName} {full : Array Name}
    {l : List Atom} {x : GroundAtom}
    (hx : x ∈ dedup (((l.map (compileAtom params)).map (instantiateSlots full)).toArray)) :
    ∃ z ∈ l, x = instAtom params full.toList z := by
  have hx' := mem_dedup hx
  rw [List.mem_toArray, List.mem_map] at hx'
  obtain ⟨sl, hsl, hval⟩ := hx'
  rw [List.mem_map] at hsl
  obtain ⟨z, hz, rfl⟩ := hsl
  exact ⟨z, hz, by rw [← hval, instantiate_compile]⟩

/-- An add the operator does not already read is kept as an add. -/
theorem mem_mkOp_add (a : Action) (dyn : List Atom) (full : Array Name) {y : Atom}
    (hy : y ∈ a.add)
    (hp : ∀ z ∈ dyn, instAtom a.params full.toList z ≠ instAtom a.params full.toList y) :
    instAtom a.params full.toList y ∈ (mkOp a dyn full).add := by
  show instAtom a.params full.toList y ∈ Array.filter _ _
  refine Array.mem_filter.mpr ⟨?_, ?_⟩
  · refine dedup_mem ?_
    rw [List.mem_toArray, List.mem_map]
    exact ⟨compileAtom a.params y, List.mem_map.mpr ⟨y, hy, rfl⟩,
      instantiate_compile a.params full y⟩
  · simp only [Bool.not_eq_true']
    rw [Bool.eq_false_iff]
    intro hc
    have hmem : instAtom a.params full.toList y ∈ (mkOp a dyn full).pre :=
      Array.contains_iff_mem.mp hc
    obtain ⟨z, hz, hzv⟩ := inst_of_mem_dedup (l := dyn) hmem
    exact hp z hz hzv.symm

/-- A delete the operator does not re-add is kept as a delete. -/
theorem mem_mkOp_del (a : Action) (dyn : List Atom) (full : Array Name) {y : Atom}
    (hy : y ∈ a.del)
    (hp : ∀ z ∈ a.add, instAtom a.params full.toList z ≠ instAtom a.params full.toList y) :
    instAtom a.params full.toList y ∈ (mkOp a dyn full).del := by
  show instAtom a.params full.toList y ∈ Array.filter _ _
  refine Array.mem_filter.mpr ⟨?_, ?_⟩
  · refine dedup_mem ?_
    rw [List.mem_toArray, List.mem_map]
    exact ⟨compileAtom a.params y, List.mem_map.mpr ⟨y, hy, rfl⟩,
      instantiate_compile a.params full y⟩
  · simp only [Bool.not_eq_true']
    rw [Bool.eq_false_iff]
    intro hc
    obtain ⟨z, hz, hzv⟩ := inst_of_mem_dedup (l := a.add) (Array.contains_iff_mem.mp hc)
    exact hp z hz hzv.symm

theorem mem_allAtoms_of_mem_op {ops : Array AtomOp} {goalAtoms : Array GroundAtom}
    {op : AtomOp} (hop : op ∈ ops) {x : GroundAtom}
    (hx : x ∈ op.pre ∨ x ∈ op.add ∨ x ∈ op.del) : x ∈ allAtoms ops goalAtoms := by
  unfold allAtoms
  rw [Array.mem_append]
  refine Or.inl ?_
  rw [← Array.foldl_toList]
  have keep : ∀ (l : List AtomOp) (acc : Array GroundAtom), x ∈ acc →
      x ∈ l.foldl (fun acc op => acc ++ op.pre ++ op.add ++ op.del) acc := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons b bs ih => intro acc h; exact ih _ (by simp [h])
  have hit : ∀ (l : List AtomOp), op ∈ l → ∀ acc,
      x ∈ l.foldl (fun acc op => acc ++ op.pre ++ op.add ++ op.del) acc := by
    intro l
    induction l with
    | nil => intro h; simp at h
    | cons b bs ih =>
        intro hb acc
        rcases List.mem_cons.mp hb with rfl | h
        · refine keep bs _ ?_
          rcases hx with h | h | h <;> simp [h]
        · exact ih h _
  exact hit ops.toList (by simpa using hop) #[]

/--
**Every atom of a well-typed instance receives a fact number.**  Stated for
`ground d p false`; with relevance analysis on, an operator can still be pruned,
and `Proofs/Relevance.lean` is where that is handled.
-/
theorem ground_names_instance (d : Domain) (p : Problem)
    (i : Instance d (allObjects d p))
    (hty : ∀ pm ∈ i.schema.params, pm.type ∈ d.typeNames)
    (hstat : ∀ y ∈ i.schema.pre, (staticPredicates d).contains y.pred = true →
      instAtom i.schema.params i.args y ∈ p.init)
    {y : Atom}
    (hy : (y ∈ i.schema.pre ∧ (staticPredicates d).contains y.pred = false) ∨
      y ∈ i.schema.add ∨ y ∈ i.schema.del) :
    ∃ f, f < (ground d p false).numFacts ∧
      (ground d p false).factNames.getD f default = instAtom i.schema.params i.args y := by
  have hlen : i.args.length = i.schema.params.length := i.typed.length_eq.symm
  set full := i.args.toArray with hfullDef
  have htoList : full.toList = i.args := by simp [hfullDef]
  have hfull : full.size = i.schema.params.length := by simp [hfullDef, hlen]
  have hwt : List.Forall₂ (fun (pm : TypedName) (o : Name) =>
      WellTyped d (allObjects d p) pm.type o) i.schema.params full.toList := by
    rw [htoList]; exact i.typed
  have hstat' : ∀ z ∈ i.schema.pre, (staticPredicates d).contains z.pred = true →
      instAtom i.schema.params full.toList z ∈ p.init := by
    rw [htoList]; exact hstat
  have hop := groundedOps_complete d p i.mem full hfull hty hwt hstat'
  have hy' : y ∈ (i.schema.pre.filter fun x => !(staticPredicates d).contains x.pred) ∨
      y ∈ i.schema.add ∨ y ∈ i.schema.del := by
    rcases hy with ⟨h1, h2⟩ | h | h
    · exact Or.inl (List.mem_filter.mpr ⟨h1, by simpa using h2⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hmk := mem_mkOp i.schema _ full hy'
  rw [htoList] at hmk
  have hall : instAtom i.schema.params i.args y
      ∈ allAtoms (groundedOps d p false) p.goal.toArray :=
    mem_allAtoms_of_mem_op hop hmk
  refine ⟨_, ix_lt (groundedOps d p false) p.goal.toArray p.init.toArray
      (allObjects d p).toArray d.name hall, ?_⟩
  exact name_ix (groundedOps d p false) p.goal.toArray p.init.toArray
    (allObjects d p).toArray d.name hall

/-- Every goal atom is numbered, with or without pruning: `allAtoms` ends with them. -/
theorem ground_names_goal (d : Domain) (p : Problem) (relevance : Bool)
    {x : GroundAtom} (hx : x ∈ p.goal) :
    ∃ f, f < (ground d p relevance).numFacts ∧
      (ground d p relevance).factNames.getD f default = x := by
  have hall : x ∈ allAtoms (groundedOps d p relevance) p.goal.toArray := by
    unfold allAtoms
    exact Array.mem_append.mpr (Or.inr (by simpa using hx))
  exact ⟨_, ix_lt (groundedOps d p relevance) p.goal.toArray p.init.toArray
      (allObjects d p).toArray d.name hall,
    name_ix (groundedOps d p relevance) p.goal.toArray p.init.toArray
      (allObjects d p).toArray d.name hall⟩

/-! ### With the relevance analysis on

Pruning can drop a whole operator, so completeness has to be conditional: the
operator survives when it writes some relevant fact, and then its preconditions
are still numbered and so is any effect of it on a relevant atom.  `r` and `hrdef`
follow the idiom of `Proofs/Relevance.lean` — the fixpoint's set is supplied by
the caller and `hrdef` is a decidable check at the task.
-/

theorem ground_names_instance_pruned (d : Domain) (p : Problem)
    (i : Instance d (allObjects d p))
    (hty : ∀ pm ∈ i.schema.params, pm.type ∈ d.typeNames)
    (hstat : ∀ y ∈ i.schema.pre, (staticPredicates d).contains y.pred = true →
      instAtom i.schema.params i.args y ∈ p.init)
    (r : Std.HashSet GroundAtom)
    (hrdef : relevanceAnalysis (rawOps d p) p.goal.toArray
      = (rawOps d p).filterMap fun op =>
          if ((op.add.filter r.contains).isEmpty && (op.del.filter r.contains).isEmpty)
          then none else some (AtomOp.trim op r))
    (htouch : (mkOp i.schema
      (i.schema.pre.filter fun x => !(staticPredicates d).contains x.pred)
      i.args.toArray).touches r = true)
    {y : Atom}
    (hy : (y ∈ i.schema.pre ∧ (staticPredicates d).contains y.pred = false) ∨
      ((y ∈ i.schema.add ∨ y ∈ i.schema.del) ∧
        r.contains (instAtom i.schema.params i.args y) = true)) :
    ∃ f, f < (ground d p true).numFacts ∧
      (ground d p true).factNames.getD f default = instAtom i.schema.params i.args y := by
  have hlen : i.args.length = i.schema.params.length := i.typed.length_eq.symm
  set full := i.args.toArray with hfullDef
  have htoList : full.toList = i.args := by simp [hfullDef]
  have hfull : full.size = i.schema.params.length := by simp [hfullDef, hlen]
  have hwt : List.Forall₂ (fun (pm : TypedName) (o : Name) =>
      WellTyped d (allObjects d p) pm.type o) i.schema.params full.toList := by
    rw [htoList]; exact i.typed
  have hstat' : ∀ z ∈ i.schema.pre, (staticPredicates d).contains z.pred = true →
      instAtom i.schema.params full.toList z ∈ p.init := by
    rw [htoList]; exact hstat
  set dyn := i.schema.pre.filter fun x => !(staticPredicates d).contains x.pred with hdyn
  have hraw : mkOp i.schema dyn full ∈ rawOps d p := by
    rw [← groundedOps_false]
    exact groundedOps_complete d p i.mem full hfull hty hwt hstat'
  have hsurv : (mkOp i.schema dyn full).trim r ∈ groundedOps d p true := by
    rw [groundedOps_true]
    exact mem_relevance_of_touches hraw r hrdef htouch
  -- Which of the trimmed lists the atom lands in.
  set op' := (mkOp i.schema dyn full).trim r with hop'
  have hp' : op'.pre = (mkOp i.schema dyn full).pre := rfl
  have ha' : op'.add = (mkOp i.schema dyn full).add.filter r.contains := rfl
  have hd' : op'.del = (mkOp i.schema dyn full).del.filter r.contains := rfl
  have hin : instAtom i.schema.params i.args y ∈ op'.pre ∨
      instAtom i.schema.params i.args y ∈ op'.add ∨
      instAtom i.schema.params i.args y ∈ op'.del := by
    rcases hy with ⟨h1, h2⟩ | ⟨h, hr⟩
    · refine Or.inl ?_
      rw [hp', ← htoList]
      exact mem_mkOp_pre i.schema dyn full (List.mem_filter.mpr ⟨h1, by simpa using h2⟩)
    · have hmk := mem_mkOp i.schema dyn full (Or.inr h)
      rw [htoList] at hmk
      rcases hmk with hm | hm | hm
      · exact Or.inl (by rw [hp']; exact hm)
      · exact Or.inr (Or.inl (by rw [ha']; exact Array.mem_filter.mpr ⟨hm, hr⟩))
      · exact Or.inr (Or.inr (by rw [hd']; exact Array.mem_filter.mpr ⟨hm, hr⟩))
  have hall : instAtom i.schema.params i.args y
      ∈ allAtoms (groundedOps d p true) p.goal.toArray :=
    mem_allAtoms_of_mem_op hsurv hin
  exact ⟨_, ix_lt (groundedOps d p true) p.goal.toArray p.init.toArray
      (allObjects d p).toArray d.name hall,
    name_ix (groundedOps d p true) p.goal.toArray p.init.toArray
      (allObjects d p).toArray d.name hall⟩

/-! ### The other side: an atom the task never numbered

A compiled table with no entry for an atom is only sound if the atom is false
wherever the search goes.  `Abstracts` reads an unnumbered atom out of
`staticAtoms`, and `staticAtoms` is a sub-list of `:init` — so an atom that is
neither numbered nor initially true is false in *every* abstracted state.  This is
what the `…None` fields of the domains' match structures assert, proved once.
-/

theorem unnamed_false (d : Domain) (p : Problem) (relevance : Bool)
    {s : State} {σ : AtomState} (habs : Abstracts (ground d p relevance) s σ)
    {a : GroundAtom}
    (hname : ∀ f, f < (ground d p relevance).numFacts →
      (ground d p relevance).factNames.getD f default ≠ a)
    (hinit : a ∉ p.init) : σ a = false := by
  have h := habs.unnumbered a hname
  rw [h, Bool.eq_false_iff]
  intro hc
  have hmem : a ∈ (ground d p relevance).staticAtoms := Array.contains_iff_mem.mp hc
  rw [show (ground d p relevance).staticAtoms
      = p.init.toArray.filter (!(factIndex (allAtoms (groundedOps d p relevance)
          p.goal.toArray)).1.contains ·) from rfl] at hmem
  exact hinit (by simpa using (Array.mem_filter.mp hmem).1)

/-! ### Static atoms are never numbered

The grounder checks a static precondition against `:init` and drops it, so no
operator carries one; and no schema adds or deletes one, by the definition of
static.  So a numbered static atom can only have come from the goal.  This is what
lets a heuristic read a static predicate off `staticAtoms` and be sure it is
reading everything `:init` said.
-/

private theorem go_pre_pred (types : Std.HashMap Name (Array Name))
    (init : Std.HashSet GroundAtom) (a : Action)
    (index : Std.HashMap Name (Array GroundAtom)) (dyn add del : List SlotAtom)
    (checkAt : Nat → List SlotAtom) :
    ∀ (rest : List TypedName) (assign : Array Name) (acc : Array AtomOp),
      (∀ op ∈ acc, ∀ x ∈ op.pre, ∃ y ∈ dyn, x.pred = y.pred) →
      ∀ op ∈ groundSchema.go types init a index dyn add del checkAt rest assign acc,
        ∀ x ∈ op.pre, ∃ y ∈ dyn, x.pred = y.pred := by
  intro rest
  induction rest with
  | nil =>
      intro assign acc hacc op hop
      rw [groundSchema.go] at hop
      rcases Array.mem_push.mp hop with hmem | rfl
      · exact hacc op hmem
      · intro x hx
        have hx' : x ∈ ((dyn.map (instantiateSlots assign)).toArray) := mem_dedup hx
        rw [List.mem_toArray, List.mem_map] at hx'
        obtain ⟨sl, hsl, hval⟩ := hx'
        exact ⟨sl, hsl, by rw [← hval]; rfl⟩
  | cons pm rest ih =>
      intro assign acc hacc op hop
      rw [groundSchema.go, ← Array.foldl_toList] at hop
      have fold : ∀ (l : List Name) (acc' : Array AtomOp),
          (∀ q ∈ acc', ∀ x ∈ q.pre, ∃ y ∈ dyn, x.pred = y.pred) →
          ∀ q ∈ l.foldl (fun acc o =>
              let assign := assign.push o
              if (checkAt assign.size).all
                  (staticCompatible init index assign)
              then groundSchema.go types init a index dyn add del checkAt rest assign acc
              else acc) acc', ∀ x ∈ q.pre, ∃ y ∈ dyn, x.pred = y.pred := by
        intro l
        induction l with
        | nil => intro acc' h q hq; exact h q hq
        | cons o os ihl =>
            intro acc' h q hq
            refine ihl _ ?_ q hq
            by_cases hchk : (checkAt (assign.push o).size).all
                (staticCompatible init index (assign.push o))
            · simp only [hchk, if_true]; exact ih _ _ h
            · simp only [hchk, Bool.false_eq_true, if_false]; exact h
      exact fold _ acc hacc op hop

/-- An operator's precondition holds only atoms of predicates some schema changes. -/
theorem groundSchema_pre_dynamic (d : Domain) (types : Std.HashMap Name (Array Name))
    (statics : List Name) (init : Std.HashSet GroundAtom) (a : Action) {op : AtomOp}
    (hop : op ∈ groundSchema d types statics init a) {x : GroundAtom} (hx : x ∈ op.pre) :
    statics.contains x.pred = false := by
  unfold groundSchema at hop
  simp only at hop
  split at hop
  · obtain ⟨sl, hsl, hpred⟩ := go_pre_pred types init a (staticFactIndex init)
      _ _ _ _ a.params #[] #[]
      (by simp) op hop x hx
    rw [List.mem_map] at hsl
    obtain ⟨z, hz, rfl⟩ := hsl
    have : x.pred = z.pred := hpred
    rw [this]
    simpa using (List.mem_filter.mp hz).2
  · simp at hop

/-- Every atom of every grounded operator has a predicate some schema changes. -/
theorem rawOps_atom_dynamic (d : Domain) (p : Problem) {op : AtomOp}
    (hop : op ∈ rawOps d p) {x : GroundAtom}
    (hx : x ∈ op.pre ∨ x ∈ op.add ∨ x ∈ op.del) :
    (staticPredicates d).contains x.pred = false := by
  rcases hx with hx | hx | hx
  · -- the precondition case is about what `groundSchema` kept
    have fold : ∀ (l : List Action) (acc : Array AtomOp),
        (∀ q ∈ acc, ∀ z ∈ q.pre, (staticPredicates d).contains z.pred = false) →
        ∀ q ∈ l.foldl (fun g b => g ++ groundSchema d (typeObjects d (allObjects d p))
          (staticPredicates d) (Std.HashSet.ofList p.init) b) acc,
          ∀ z ∈ q.pre, (staticPredicates d).contains z.pred = false := by
      intro l
      induction l with
      | nil => intro acc h q hq; exact h q hq
      | cons b bs ihl =>
          intro acc h q hq
          refine ihl _ ?_ q hq
          intro r hr z hz
          rcases Array.mem_append.mp hr with h1 | h1
          · exact h r h1 z hz
          · exact groundSchema_pre_dynamic d _ _ _ b h1 hz
    unfold rawOps at hop
    exact fold d.actions #[] (by simp) op hop x hx
  · obtain ⟨f⟩ := opFacts_raw d p hop
    obtain ⟨y, hy, hval⟩ := List.mem_map.mp (f.subAdd x hx)
    rw [← hval, instAtom_pred]
    exact not_static_of_mem_add f.inst.mem hy
  · obtain ⟨f⟩ := opFacts_raw d p hop
    obtain ⟨y, hy, hval⟩ := List.mem_map.mp (f.subDel x hx)
    rw [← hval, instAtom_pred]
    exact not_static_of_mem_del f.inst.mem hy

/-- The same for a pruned task: pruning only removes and trims. -/
theorem groundedOps_atom_dynamic (d : Domain) (p : Problem) (rel : Bool) {op : AtomOp}
    (hop : op ∈ groundedOps d p rel) {x : GroundAtom}
    (hx : x ∈ op.pre ∨ x ∈ op.add ∨ x ∈ op.del) :
    (staticPredicates d).contains x.pred = false := by
  cases rel with
  | false => exact rawOps_atom_dynamic d p (by rwa [← groundedOps_false]) hx
  | true =>
      rw [groundedOps_true] at hop
      obtain ⟨op₀, hop₀, hpre, -, hadd, hdel⟩ := relevance_sub hop
      refine rawOps_atom_dynamic d p hop₀ ?_
      rcases hx with h | h | h
      · exact Or.inl (hpre ▸ h)
      · exact Or.inr (Or.inl (hadd x h))
      · exact Or.inr (Or.inr (hdel x h))

/-- **A numbered static atom is a goal atom.** -/
theorem mem_goal_of_static (d : Domain) (p : Problem) (rel : Bool) {x : GroundAtom}
    (hx : x ∈ allAtoms (groundedOps d p rel) p.goal.toArray)
    (hst : (staticPredicates d).contains x.pred = true) : x ∈ p.goal := by
  unfold allAtoms at hx
  rcases Array.mem_append.mp hx with h | h
  · exfalso
    rw [← Array.foldl_toList] at h
    have key : ∀ (l : List AtomOp) (acc : Array GroundAtom),
        (∀ op ∈ l, op ∈ groundedOps d p rel) →
        x ∈ l.foldl (fun acc op => acc ++ op.pre ++ op.add ++ op.del) acc →
        x ∈ acc ∨ ∃ op ∈ l, x ∈ op.pre ∨ x ∈ op.add ∨ x ∈ op.del := by
      intro l
      induction l with
      | nil => intro acc _ h; exact Or.inl h
      | cons b bs ih =>
          intro acc hall h
          rcases ih _ (fun o ho => hall o (by simp [ho])) h with h1 | ⟨o, ho, h1⟩
          · rcases Array.mem_append.mp h1 with h2 | h2
            · rcases Array.mem_append.mp h2 with h3 | h3
              · rcases Array.mem_append.mp h3 with h4 | h4
                · exact Or.inl h4
                · exact Or.inr ⟨b, by simp, Or.inl h4⟩
              · exact Or.inr ⟨b, by simp, Or.inr (Or.inl h3)⟩
            · exact Or.inr ⟨b, by simp, Or.inr (Or.inr h2)⟩
          · exact Or.inr ⟨o, by simp [ho], h1⟩
    have hsub : ∀ op ∈ (groundedOps d p rel).toList, op ∈ groundedOps d p rel :=
      fun o ho => Array.mem_def.mpr ho
    rcases key _ #[] hsub h with h1 | ⟨o, ho, h1⟩
    · simp at h1
    · rw [groundedOps_atom_dynamic d p rel (hsub o ho) h1] at hst
      exact Bool.noConfusion hst
  · simpa using h

end Planner
