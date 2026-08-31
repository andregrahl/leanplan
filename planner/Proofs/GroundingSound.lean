/-
Grounding is sound: every operator it produces is a schema instance.

`Proofs/GroundingCorrect.lean` proves the *numbering* half of grounding — that the
packed states and numbered operators agree with the atom-level model.  This file
starts the other half: that the operators themselves are exactly the well-typed
instances of the domain's schemas, which is the fact every heuristic's
`SchemaStep` assumption needs.

Only the soundness direction is proved here — every operator produced is an
instance.  The converse, that no instance a goal-reaching plan needs is dropped,
is a statement about the relevance fixpoint and is not attempted.

## What still stands between this and a domain's `SchemaStep`

`ground_ops_instance` at the bottom is the first of three links.  The other two
are per-domain and are not written yet:

1. **Pin the domain.**  `groundedOps_instance` says the schema is *some* member of
   `d.actions`.  To case on which, a task has to be known to come from a
   particular domain — `hd : d.actions = [board, depart, up, down]` for miconic,
   say.  That is one decidable check on the parsed domain, run once at load time,
   and it is a far smaller thing to assume than a fact about every operator.
   With it, `i.mem` becomes a four-way case split and `i.typed` peels the
   arguments off one parameter at a time.
2. **Relate the atoms to the compiled tables.**  A shape's fields speak of the
   heuristic's `Data` — `currentFloor d s = some f`, `onBoard s c` — not of raw
   atoms.  Closing that needs compile-faithfulness lemmas per domain, which are
   today the `hcompiled` and `hnd` hypotheses of each `improved_admissible_of_schema`.
   `Proofs/GroundingCorrect.lean`'s `Abstracts` is the bridge from a packed state
   to the atoms; what is missing is the bridge from the atoms to the tables.
-/
import Proofs.GroundingCorrect
import Proofs.Relevance

namespace Planner

open Planner.Pddl

/-! ### Deduplication and the two effect filters only remove -/

theorem mem_dedup {a : GroundAtom} : ∀ {xs : Array GroundAtom}, a ∈ dedup xs → a ∈ xs := by
  intro xs
  unfold dedup
  rw [← Array.foldl_toList]
  have key : ∀ (l : List GroundAtom) (acc : Array GroundAtom),
      a ∈ l.foldl (fun acc b => if acc.contains b then acc else acc.push b) acc →
      a ∈ acc ∨ a ∈ l := by
    intro l
    induction l with
    | nil => intro acc h; exact Or.inl h
    | cons b rest ih =>
        intro acc h
        rcases ih _ h with h1 | h1
        · by_cases hb : acc.contains b
          · simp only [hb, if_true] at h1
            exact Or.inl h1
          · simp only [hb, Bool.false_eq_true, if_false] at h1
            rcases Array.mem_push.mp h1 with h2 | h2
            · exact Or.inl h2
            · exact Or.inr (by simp [h2])
        · exact Or.inr (by simp [h1])
  intro h
  rcases key xs.toList #[] h with h1 | h1
  · simp at h1
  · simpa using h1

/-- Deduplication keeps everything it was given. -/
theorem dedup_mem {a : GroundAtom} : ∀ {xs : Array GroundAtom}, a ∈ xs → a ∈ dedup xs := by
  intro xs
  unfold dedup
  rw [← Array.foldl_toList]
  have key : ∀ (l : List GroundAtom) (acc : Array GroundAtom),
      (a ∈ acc ∨ a ∈ l) →
      a ∈ l.foldl (fun acc b => if acc.contains b then acc else acc.push b) acc := by
    intro l
    induction l with
    | nil =>
        intro acc h
        rcases h with h | h
        · exact h
        · simp at h
    | cons b rest ih =>
        intro acc h
        refine ih _ ?_
        by_cases hb : acc.contains b
        · simp only [hb, if_true]
          rcases h with h | h
          · exact Or.inl h
          · rcases List.mem_cons.mp h with rfl | h'
            · exact Or.inl (by simpa using hb)
            · exact Or.inr h'
        · simp only [hb, Bool.false_eq_true, if_false]
          rcases h with h | h
          · exact Or.inl (Array.mem_push.mpr (Or.inl h))
          · rcases List.mem_cons.mp h with rfl | h'
            · exact Or.inl (Array.mem_push.mpr (Or.inr rfl))
            · exact Or.inr h'
  intro h
  exact key xs.toList #[] (Or.inr (by simpa using h))

/-! ### The relevance analysis only filters -/

theorem relevance_sub {ops : Array AtomOp} {goal : Array GroundAtom} {op' : AtomOp}
    (h : op' ∈ relevanceAnalysis ops goal) :
    ∃ op ∈ ops, op'.pre = op.pre ∧ op'.cost = op.cost ∧
      (∀ a ∈ op'.add, a ∈ op.add) ∧ (∀ a ∈ op'.del, a ∈ op.del) := by
  unfold relevanceAnalysis at h
  simp only at h
  split at h
  · rw [Array.mem_filterMap] at h
    obtain ⟨op, hop, hval⟩ := h
    split at hval
    · exact absurd hval (by simp)
    · rw [Option.some.injEq] at hval
      subst hval
      exact ⟨op, hop, rfl, rfl, fun a ha => (Array.mem_filter.mp ha).1,
        fun a ha => (Array.mem_filter.mp ha).1⟩
  · exact ⟨op', h, rfl, rfl, fun a ha => ha, fun a ha => ha⟩

/-! ### The candidate lists are the objects of the right type -/

theorem typeObjects_wellTyped (d : Domain) (objects : List TypedName) {ty o : Name}
    (h : o ∈ (typeObjects d objects).getD ty #[]) : WellTyped d objects ty o := by
  have key : ∀ (l : List Name) (m : Std.HashMap Name (Array Name)),
      (∀ t x, x ∈ m.getD t #[] → WellTyped d objects t x) →
      ∀ t x, x ∈ (l.foldl (fun r u =>
          r.insert u ((objects.filter fun y => d.isSubtype y.type u).map (·.name)).toArray)
        m).getD t #[] → WellTyped d objects t x := by
    intro l
    induction l with
    | nil => intro m hm t x hx; exact hm t x hx
    | cons u rest ih =>
        intro m hm t x hx
        refine ih _ ?_ t x hx
        intro t' x' hx'
        rw [Std.HashMap.getD_insert] at hx'
        split at hx'
        · rename_i hu
          have hu' : u = t' := by simpa using hu
          subst hu'
          simp only [List.mem_toArray, List.mem_map, List.mem_filter] at hx'
          obtain ⟨decl, ⟨hmem, hsub⟩, hname⟩ := hx'
          exact ⟨decl, hmem, hname, hsub⟩
        · exact hm t' x' hx'
  unfold typeObjects at h
  simp at h
  exact key d.typeNames ∅ (by intro t x hx; simp at hx) ty o h

/-! ### Slots, levels, and partial assignments

A compiled atom's `level` is one past the largest parameter it mentions, which is
how the grounder knows when a static precondition becomes checkable.  Two facts
follow: the level never exceeds the parameter count, and once the assignment is
that long the atom's instantiation stops changing.
-/

private theorem foldl_level_ge {i : Nat} : ∀ (l : List Slot) (b : Nat),
    Slot.param i ∈ l → i + 1 ≤ l.foldl (fun acc s =>
      match s with | .param j => max acc (j + 1) | .obj _ => acc) b := by
  intro l
  induction l with
  | nil => intro b h; simp at h
  | cons x rest ih =>
      intro b h
      rcases List.mem_cons.mp h with rfl | h'
      · have hmono : ∀ (l' : List Slot) (c : Nat), c ≤ l'.foldl (fun acc s =>
            match s with | .param j => max acc (j + 1) | .obj _ => acc) c := by
          intro l'
          induction l' with
          | nil => intro c; exact Nat.le_refl _
          | cons y ys ihy =>
              intro c
              refine Nat.le_trans ?_ (ihy _)
              cases y <;> simp <;> omega
        refine Nat.le_trans ?_ (hmono rest _)
        simp
      · exact ih _ h'

theorem compileAtom_param_lt {params : List TypedName} {atom : Atom} {i : Nat}
    (h : Slot.param i ∈ (compileAtom params atom).slots) :
    i + 1 ≤ (compileAtom params atom).level := by
  have hlevel : (compileAtom params atom).level
      = (compileAtom params atom).slots.foldl (fun acc s =>
          match s with | .param j => max acc (j + 1) | .obj _ => acc) 0 := rfl
  rw [hlevel, ← Array.foldl_toList]
  exact foldl_level_ge _ 0 (by simpa using h)

private theorem foldl_level_le {n : Nat} : ∀ (l : List Slot) (b : Nat),
    (∀ i, Slot.param i ∈ l → i + 1 ≤ n) → b ≤ n →
    l.foldl (fun acc s =>
      match s with | .param j => max acc (j + 1) | .obj _ => acc) b ≤ n := by
  intro l
  induction l with
  | nil => intro b _ hb; exact hb
  | cons x rest ih =>
      intro b hall hb
      refine ih _ (fun i hi => hall i (by simp [hi])) ?_
      cases x with
      | obj _ => exact hb
      | param j =>
          have := hall j (by simp)
          simp only
          omega

theorem compileAtom_level_le (params : List TypedName) (atom : Atom) :
    (compileAtom params atom).level ≤ params.length := by
  have hlevel : (compileAtom params atom).level
      = (compileAtom params atom).slots.foldl (fun acc s =>
          match s with | .param j => max acc (j + 1) | .obj _ => acc) 0 := rfl
  rw [hlevel, ← Array.foldl_toList]
  refine foldl_level_le _ 0 ?_ (Nat.zero_le _)
  intro i hi
  have hmem : Slot.param i ∈ (compileAtom params atom).slots := by simpa using hi
  have : ∃ t ∈ atom.args, (match t with
      | .var v => match params.findIdx? (·.name == v) with
        | some j => Slot.param j
        | none => Slot.obj v
      | .const c => Slot.obj c) = Slot.param i := by
    simpa [compileAtom] using hmem
  obtain ⟨t, -, ht⟩ := this
  cases t with
  | const c => simp at ht
  | var v =>
      simp only at ht
      cases hf : params.findIdx? (·.name == v) with
      | none => rw [hf] at ht; simp at ht
      | some j =>
          rw [hf] at ht
          simp only [Slot.param.injEq] at ht
          subst ht
          rw [List.findIdx?_eq_some_iff_getElem] at hf
          obtain ⟨hlt, -⟩ := hf
          omega

theorem getD_map_range {α : Type} (n k : Nat) (hk : k < n) (f : Nat → α) (dflt : α) :
    ((Array.range n).map f).getD k dflt = f k := by
  have hlt : k < ((Array.range n).map f).size := by simp; exact hk
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
  simp [Array.getElem_map, Array.getElem_range]

theorem instantiateSlots_push {params : List TypedName} {atom : Atom}
    {assign : Array Name} {o : Name}
    (h : (compileAtom params atom).level ≤ assign.size) :
    instantiateSlots (assign.push o) (compileAtom params atom)
      = instantiateSlots assign (compileAtom params atom) := by
  unfold instantiateSlots
  simp only [GroundAtom.mk.injEq, true_and]
  refine List.map_congr_left ?_
  intro sl hsl
  cases sl with
  | obj n => rfl
  | param i =>
      have hi : i + 1 ≤ (compileAtom params atom).level :=
        compileAtom_param_lt (by simpa using hsl)
      have hlt : i < assign.size := by omega
      have hlt' : i < (assign.push o).size := by simp; omega
      show (assign.push o).getD i "" = assign.getD i ""
      rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem hlt, Array.getElem?_eq_getElem hlt',
        Array.getElem_push_lt hlt]

/-! ### What an operator `groundSchema` produces looks like -/

/-- `op` is the schema `a` instantiated with one well-typed object per parameter. -/
def Produced (d : Domain) (objects : List TypedName) (a : Action) (dyn stat : List Atom)
    (init : Std.HashSet GroundAtom) (op : AtomOp) : Prop :=
  ∃ args : List Name,
    List.Forall₂ (fun (p : TypedName) (o : Name) => WellTyped d objects p.type o)
      a.params args ∧
    (∀ x ∈ op.pre, ∃ y ∈ a.pre, x = instAtom a.params args y) ∧
    (∀ x ∈ op.add, ∃ y ∈ a.add, x = instAtom a.params args y) ∧
    (∀ x ∈ op.del, ∃ y ∈ a.del, x = instAtom a.params args y) ∧
    (∀ y ∈ a.pre, y ∈ dyn → instAtom a.params args y ∈ op.pre) ∧
    (∀ y ∈ a.del, instAtom a.params args y ∉ a.add.map (instAtom a.params args) →
      instAtom a.params args y ∈ op.del) ∧
    (∀ y ∈ a.add, instAtom a.params args y ∉ op.pre →
      instAtom a.params args y ∈ op.add) ∧
    (∀ y ∈ stat, init.contains (instAtom a.params args y) = true) ∧
    op.cost = a.cost

/-- Every atom of a slot list, instantiated, is a schema atom instantiated. -/
private theorem mem_instantiated {params : List TypedName} {assign : Array Name}
    {src : List Atom} {sel : List Atom} (hsub : ∀ y ∈ sel, y ∈ src)
    {x : GroundAtom}
    (hx : x ∈ ((sel.map (compileAtom params)).map (instantiateSlots assign)).toArray) :
    ∃ y ∈ src, x = instAtom params assign.toList y := by
  rw [List.mem_toArray, List.mem_map] at hx
  obtain ⟨sl, hsl, hval⟩ := hx
  rw [List.mem_map] at hsl
  obtain ⟨y, hy, rfl⟩ := hsl
  exact ⟨y, hsub y hy, by rw [← hval, instantiate_compile]⟩

private theorem forall2_append {α β : Type} {P : α → β → Prop}
    {l1 l2 : List α} {r1 r2 : List β}
    (h1 : List.Forall₂ P l1 r1) (h2 : List.Forall₂ P l2 r2) :
    List.Forall₂ P (l1 ++ l2) (r1 ++ r2) := by
  induction h1 with
  | nil => simpa using h2
  | cons hx _ ih => exact List.Forall₂.cons hx ih

/-- Every operator the parameter walk pushes is the schema under a well-typed
assignment. -/
theorem go_produced (d : Domain) (objects : List TypedName)
    (types : Std.HashMap Name (Array Name))
    (htypes : ∀ ty o, o ∈ types.getD ty #[] → WellTyped d objects ty o)
    (init : Std.HashSet GroundAtom) (a : Action)
    (index : Std.HashMap Name (Array GroundAtom)) (checkAt : Nat → List SlotAtom)
    (dyn : List Atom) (hdyn : ∀ y ∈ dyn, y ∈ a.pre) (stat : List Atom)
    (hcheck : ∀ k, checkAt k = stat.map (compileAtom a.params)) :
    ∀ (rest : List TypedName) (assign : Array Name) (acc : Array AtomOp)
      (pfx : List TypedName), a.params = pfx ++ rest →
      List.Forall₂ (fun (p : TypedName) (o : Name) => WellTyped d objects p.type o)
        pfx assign.toList →
      (∀ y ∈ stat, (compileAtom a.params y).level ≤ assign.size →
        init.contains (instantiateSlots assign (compileAtom a.params y)) = true) →
      (∀ op ∈ acc, Produced d objects a dyn stat init op) →
      ∀ op ∈ groundSchema.go types init a index (dyn.map (compileAtom a.params))
        (a.add.map (compileAtom a.params)) (a.del.map (compileAtom a.params))
        checkAt rest assign acc, Produced d objects a dyn stat init op := by
  intro rest
  induction rest with
  | nil =>
      intro assign acc pfx hparams hall hdone hacc op hop
      rw [groundSchema.go] at hop
      rcases Array.mem_push.mp hop with hmem | rfl
      · exact hacc op hmem
      · refine ⟨assign.toList, by rw [hparams]; simpa using hall, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          rfl⟩
        · intro x hx
          exact mem_instantiated hdyn (mem_dedup hx)
        · intro x hx
          exact mem_instantiated (fun y hy => hy)
            (mem_dedup (Array.mem_filter.mp hx).1)
        · intro x hx
          exact mem_instantiated (fun y hy => hy)
            (mem_dedup (Array.mem_filter.mp hx).1)
        · intro y _ hy
          refine dedup_mem ?_
          rw [List.mem_toArray, List.mem_map]
          refine ⟨compileAtom a.params y, ?_, ?_⟩
          · rw [List.mem_map]; exact ⟨y, hy, rfl⟩
          · exact instantiate_compile a.params assign y
        · intro y hy hnadd
          refine Array.mem_filter.mpr ⟨?_, ?_⟩
          · refine dedup_mem ?_
            rw [List.mem_toArray, List.mem_map]
            refine ⟨compileAtom a.params y, ?_, ?_⟩
            · rw [List.mem_map]; exact ⟨y, hy, rfl⟩
            · exact instantiate_compile a.params assign y
          · simp only [Bool.not_eq_true']
            by_contra hcon
            have hmem : instAtom a.params assign.toList y ∈
                dedup (((a.add.map (compileAtom a.params)).map
                  (instantiateSlots assign)).toArray) := by
              simpa using (by simpa using hcon :
                (dedup (((a.add.map (compileAtom a.params)).map
                  (instantiateSlots assign)).toArray)).contains
                  (instAtom a.params assign.toList y) = true)
            obtain ⟨z, hz, hzv⟩ := mem_instantiated (src := a.add) (fun w hw => hw)
              (mem_dedup hmem)
            exact hnadd (List.mem_map.mpr ⟨z, hz, hzv.symm⟩)
        · intro y hy hnpre
          refine Array.mem_filter.mpr ⟨?_, ?_⟩
          · refine dedup_mem ?_
            rw [List.mem_toArray, List.mem_map]
            refine ⟨compileAtom a.params y, ?_, ?_⟩
            · rw [List.mem_map]; exact ⟨y, hy, rfl⟩
            · exact instantiate_compile a.params assign y
          · simp only [Bool.not_eq_true']
            by_contra hcon
            exact hnpre (by simpa using (by simpa using hcon :
              (dedup (((dyn.map (compileAtom a.params)).map
                (instantiateSlots assign)).toArray)).contains
                (instAtom a.params assign.toList y) = true))
        · intro y hy
          have hsize : assign.size = a.params.length := by
            rw [hparams]
            simpa using hall.length_eq.symm
          have hlev : (compileAtom a.params y).level ≤ assign.size := by
            rw [hsize]; exact compileAtom_level_le a.params y
          have hres := hdone y hy hlev
          rwa [instantiate_compile] at hres
  | cons p rest ih =>
      intro assign acc pfx hparams hall hdone hacc op hop
      rw [groundSchema.go] at hop
      rw [← Array.foldl_toList] at hop
      have fold : ∀ (l : List Name) (acc' : Array AtomOp),
          (∀ o ∈ l, o ∈ types.getD p.type #[]) →
          (∀ q ∈ acc', Produced d objects a dyn stat init q) →
          ∀ q ∈ l.foldl (fun acc o =>
              let assign := assign.push o
              if (checkAt assign.size).all
                  (staticCompatible init index assign)
              then groundSchema.go types init a index (dyn.map (compileAtom a.params))
                (a.add.map (compileAtom a.params)) (a.del.map (compileAtom a.params))
                checkAt rest assign acc
              else acc) acc', Produced d objects a dyn stat init q := by
        intro l
        induction l with
        | nil => intro acc' _ hacc' q hq; exact hacc' q hq
        | cons o os ihl =>
            intro acc' hmem hacc' q hq
            refine ihl _ (fun x hx => hmem x (by simp [hx])) ?_ q hq
            by_cases hchk : (checkAt (assign.push o).size).all
                (staticCompatible init index (assign.push o))
            · simp only [hchk, if_true]
              refine ih (assign.push o) acc' (pfx ++ [p]) (by simp [hparams]) ?_ ?_ hacc'
              · have hwt : WellTyped d objects p.type o :=
                  htypes p.type o (hmem o (by simp))
                simpa using forall2_append hall (List.Forall₂.cons hwt List.Forall₂.nil)
              · intro y hy hlev
                by_cases hle : (compileAtom a.params y).level ≤ assign.size
                · rw [instantiateSlots_push hle]
                  exact hdone y hy hle
                · have hle' : (compileAtom a.params y).level ≤ (assign.push o).size := hlev
                  have hin : compileAtom a.params y ∈ checkAt (assign.push o).size := by
                    rw [hcheck]
                    exact List.mem_map.mpr ⟨y, hy, rfl⟩
                  rw [List.all_eq_true] at hchk
                  have hc := hchk _ hin
                  unfold staticCompatible at hc
                  rw [if_pos hle'] at hc
                  exact hc
            · simp only [hchk, Bool.false_eq_true, if_false]
              exact hacc'
      exact fold _ acc (fun o ho => by simpa using ho) hacc op hop

/-- Every operator one schema grounds to is that schema under a well-typed assignment. -/
theorem groundSchema_produced (d : Domain) (objects : List TypedName)
    (types : Std.HashMap Name (Array Name))
    (htypes : ∀ ty o, o ∈ types.getD ty #[] → WellTyped d objects ty o)
    (statics : List Name) (init : Std.HashSet GroundAtom) (a : Action) {op : AtomOp}
    (hop : op ∈ groundSchema d types statics init a) :
    Produced d objects a (a.pre.filter fun x => !statics.contains x.pred)
      (a.pre.filter fun x => statics.contains x.pred) init op := by
  unfold groundSchema at hop
  simp only at hop
  split at hop
  · rename_i hzero
    refine go_produced d objects types htypes init a (staticFactIndex init) _ _
      (fun y hy => (List.mem_filter.mp hy).1)
      (a.pre.filter fun x => statics.contains x.pred) ?_
      a.params #[] #[] [] (by simp) (by simp) ?_ (by simp) op hop
    · intro k
      rfl
    · intro y hy hlev
      rw [List.all_eq_true] at hzero
      have hc := hzero (compileAtom a.params y)
        (List.mem_map.mpr ⟨y, hy, rfl⟩)
      unfold staticCompatible at hc
      rw [if_pos hlev] at hc
      exact hc
  · simp at hop

/-- A `Produced` operator names an instance of the domain. -/
theorem instance_of_produced {d : Domain} {objects : List TypedName} {a : Action}
    {statics : List Name} {init : Std.HashSet GroundAtom} (ha : a ∈ d.actions)
    {op : AtomOp}
    (h : Produced d objects a (a.pre.filter fun x => !statics.contains x.pred)
      (a.pre.filter fun x => statics.contains x.pred) init op) :
    ∃ i : Instance d objects,
      (∀ x ∈ op.pre, x ∈ i.pre) ∧ (∀ x ∈ op.add, x ∈ i.add) ∧
      (∀ x ∈ op.del, x ∈ i.del) ∧
      (∀ y ∈ i.schema.pre, statics.contains y.pred = false →
        instAtom i.schema.params i.args y ∈ op.pre) ∧
      (∀ y ∈ i.schema.del, instAtom i.schema.params i.args y ∉ i.add →
        instAtom i.schema.params i.args y ∈ op.del) ∧
      (∀ y ∈ i.schema.add, instAtom i.schema.params i.args y ∉ op.pre →
        instAtom i.schema.params i.args y ∈ op.add) ∧
      (∀ y ∈ i.schema.pre, statics.contains y.pred = true →
        init.contains (instAtom i.schema.params i.args y) = true) ∧
      op.cost = i.cost := by
  obtain ⟨args, htyped, hpre, hadd, hdel, hcomplete, hdelc, haddc, hstat, hcost⟩ := h
  refine ⟨{ schema := a, mem := ha, args := args, typed := htyped }, ?_, ?_, ?_,
    fun y hy hst => hcomplete y hy (List.mem_filter.mpr ⟨hy, by simpa using hst⟩),
    hdelc, haddc,
    fun y hy hst => hstat y (List.mem_filter.mpr ⟨hy, by simpa using hst⟩), hcost⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hpre x hx
    exact List.mem_map.mpr ⟨y, hy, rfl⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hadd x hx
    exact List.mem_map.mpr ⟨y, hy, rfl⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hdel x hx
    exact List.mem_map.mpr ⟨y, hy, rfl⟩

/--
**Grounding is sound.**  Every operator the grounder produces is a well-typed
instance of one of the domain's schemas: its precondition, add and delete lists
are among that instance's, and it costs what the schema costs.
-/
theorem groundedOps_instance (d : Domain) (p : Problem) (relevance : Bool)
    {op : AtomOp} (hop : op ∈ groundedOps d p relevance) :
    ∃ i : Instance d (allObjects d p),
      (∀ x ∈ op.pre, x ∈ i.pre) ∧ (∀ x ∈ op.add, x ∈ i.add) ∧
      (∀ x ∈ op.del, x ∈ i.del) ∧
      (∀ y ∈ i.schema.pre, (staticPredicates d).contains y.pred = false →
        instAtom i.schema.params i.args y ∈ op.pre) ∧
      (∀ y ∈ i.schema.pre, (staticPredicates d).contains y.pred = true →
        (Std.HashSet.ofList p.init).contains (instAtom i.schema.params i.args y) = true) ∧
      op.cost = i.cost := by
  set objects := allObjects d p with hobjects
  set types := typeObjects d objects with htypesDef
  have htypes : ∀ ty o, o ∈ types.getD ty #[] → WellTyped d objects ty o := by
    intro ty o ho
    exact typeObjects_wellTyped d objects ho
  -- Every operator of the fold over the schemas is produced by one of them.
  have fold : ∀ (l : List Action) (acc : Array AtomOp),
      (∀ q ∈ acc, ∃ a ∈ d.actions,
        Produced d objects a (a.pre.filter fun x =>
          !(staticPredicates d).contains x.pred)
          (a.pre.filter fun x => (staticPredicates d).contains x.pred)
          (Std.HashSet.ofList p.init) q) →
      (∀ a ∈ l, a ∈ d.actions) →
      ∀ q ∈ l.foldl (fun g a => g ++ groundSchema d types
        (staticPredicates d) (Std.HashSet.ofList p.init) a) acc,
        ∃ a ∈ d.actions, Produced d objects a (a.pre.filter fun x =>
          !(staticPredicates d).contains x.pred)
          (a.pre.filter fun x => (staticPredicates d).contains x.pred)
          (Std.HashSet.ofList p.init) q := by
    intro l
    induction l with
    | nil => intro acc hacc _ q hq; exact hacc q hq
    | cons a rest ih =>
        intro acc hacc hl q hq
        refine ih _ ?_ (fun b hb => hl b (by simp [hb])) q hq
        intro x hx
        rcases Array.mem_append.mp hx with h1 | h1
        · exact hacc x h1
        · exact ⟨a, hl a (by simp), groundSchema_produced d objects types htypes _ _ a h1⟩
  unfold groundedOps at hop
  simp only [Id.run] at hop
  by_cases hrel : relevance
  · simp only [hrel, if_true] at hop
    obtain ⟨op₀, hop₀, hpre, hcost, hadd, hdel⟩ := relevance_sub hop
    obtain ⟨a, ha, hprod⟩ := fold d.actions #[] (by simp) (fun b hb => hb) op₀ (by
      simpa using hop₀)
    obtain ⟨i, h1, h2, h3, h4, -, -, h6, h7⟩ := instance_of_produced ha hprod
    exact ⟨i, by rw [hpre]; exact h1, fun x hx => h2 x (hadd x hx),
      fun x hx => h3 x (hdel x hx), by rw [hpre]; exact h4, h6,
      by rw [hcost]; exact h7⟩
  · simp only [hrel, Bool.false_eq_true, if_false] at hop
    obtain ⟨a, ha, hprod⟩ := fold d.actions #[] (by simp) (fun b hb => hb) op (by
      simpa using hop)
    obtain ⟨i, h1, h2, h3, h4, -, -, h6, h7⟩ := instance_of_produced ha hprod
    exact ⟨i, h1, h2, h3, h4, h6, h7⟩

/--
The same, for the operators the planner actually searches: every operator of a
grounded task is one of the domain's schemas, numbered.

This is the first link of the step each domain's `SchemaStep` still needs — from
here, casing on which schema the instance names is what produces the shape.
-/
theorem ground_ops_instance (d : Domain) (p : Problem) (relevance : Bool) {op : Op}
    (hop : op ∈ (ground d p relevance).ops) :
    ∃ o ∈ groundedOps d p relevance, ∃ i : Instance d (allObjects d p),
      op = numberOp
        (factIndex (allAtoms (groundedOps d p relevance) p.goal.toArray)).1 o ∧
      (∀ x ∈ o.pre, x ∈ i.pre) ∧ (∀ x ∈ o.add, x ∈ i.add) ∧
      (∀ x ∈ o.del, x ∈ i.del) ∧
      (∀ y ∈ i.schema.pre, (staticPredicates d).contains y.pred = false →
        instAtom i.schema.params i.args y ∈ o.pre) ∧
      (∀ y ∈ i.schema.pre, (staticPredicates d).contains y.pred = true →
        (Std.HashSet.ofList p.init).contains (instAtom i.schema.params i.args y) = true) ∧
      o.cost = i.cost := by
  unfold ground at hop
  rw [assemble_ops] at hop
  rw [Array.mem_map] at hop
  obtain ⟨o, ho, rfl⟩ := hop
  obtain ⟨i, h1, h2, h3, h4, h5, h6⟩ := groundedOps_instance d p relevance ho
  exact ⟨o, ho, i, rfl, h1, h2, h3, h4, h5, h6⟩

/-! ### Everything one operator gives a heuristic

`OpFacts` bundles what a heuristic proof needs about a single grounded operator:
the schema instance it is, that its effects are among the schema's, and the two
converses — every non-static precondition of the schema is present, and every
delete the operator does not re-add is present.  The last is what an invariant
like "the lift is on one floor" rests on.
-/

/-- The operators the fold produces, before the relevance analysis. -/
def rawOps (d : Domain) (p : Problem) : Array AtomOp :=
  d.actions.foldl (fun g a => g ++ groundSchema d (typeObjects d (allObjects d p))
    (staticPredicates d) (Std.HashSet.ofList p.init) a) #[]

theorem groundedOps_false (d : Domain) (p : Problem) :
    groundedOps d p false = rawOps d p := by
  unfold groundedOps rawOps
  simp

theorem groundedOps_true (d : Domain) (p : Problem) :
    groundedOps d p true = relevanceAnalysis (rawOps d p) p.goal.toArray := by
  unfold groundedOps rawOps
  simp

structure OpFacts (d : Domain) (p : Problem) (op : AtomOp) where
  inst : Instance d (allObjects d p)
  subPre : ∀ a ∈ op.pre, a ∈ inst.pre
  subAdd : ∀ a ∈ op.add, a ∈ inst.add
  subDel : ∀ a ∈ op.del, a ∈ inst.del
  preComplete : ∀ y ∈ inst.schema.pre, (staticPredicates d).contains y.pred = false →
    instAtom inst.schema.params inst.args y ∈ op.pre
  /-- And a static one it checked against `:init` really was there. -/
  staticHeld : ∀ y ∈ inst.schema.pre, (staticPredicates d).contains y.pred = true →
    (Std.HashSet.ofList p.init).contains (instAtom inst.schema.params inst.args y) = true
  /-- A delete the operator does not re-add, and which it also reads, is kept —
  through grounding and through the relevance analysis alike. -/
  delComplete : ∀ y ∈ inst.schema.del,
    instAtom inst.schema.params inst.args y ∉ inst.add →
    instAtom inst.schema.params inst.args y ∈ op.pre →
    instAtom inst.schema.params inst.args y ∈ op.del
  cost : op.cost = inst.cost

/--
What a raw operator keeps of its schema's adds.

`OpFacts` cannot carry this.  The relevance analysis may drop an add, and the
pruned operators still satisfy `OpFacts`.  A domain that reads "the object is
now here" off an add needs to know the add survived, and on the unpruned task it
always does: the grounder drops an add only when the operator already reads it.
-/
structure OpFactsAdd (d : Domain) (p : Problem) (op : AtomOp) extends OpFacts d p op where
  addComplete : ∀ y ∈ inst.schema.add,
    instAtom inst.schema.params inst.args y ∉ op.pre →
    instAtom inst.schema.params inst.args y ∈ op.add

/-- Every operator of the fold carries them. -/
theorem opFacts_raw_add (d : Domain) (p : Problem) {op : AtomOp} (hop : op ∈ rawOps d p) :
    Nonempty (OpFactsAdd d p op) := by
  have fold : ∀ (l : List Action) (acc : Array AtomOp),
      (∀ q ∈ acc, ∃ a ∈ d.actions,
        Produced d (allObjects d p) a (a.pre.filter fun x =>
          !(staticPredicates d).contains x.pred)
          (a.pre.filter fun x => (staticPredicates d).contains x.pred)
          (Std.HashSet.ofList p.init) q) →
      (∀ a ∈ l, a ∈ d.actions) →
      ∀ q ∈ l.foldl (fun g a => g ++ groundSchema d (typeObjects d (allObjects d p))
        (staticPredicates d) (Std.HashSet.ofList p.init) a) acc,
        ∃ a ∈ d.actions, Produced d (allObjects d p) a (a.pre.filter fun x =>
          !(staticPredicates d).contains x.pred)
          (a.pre.filter fun x => (staticPredicates d).contains x.pred)
          (Std.HashSet.ofList p.init) q := by
    intro l
    induction l with
    | nil => intro acc hacc _ q hq; exact hacc q hq
    | cons a rest ih =>
        intro acc hacc hl q hq
        refine ih _ ?_ (fun b hb => hl b (by simp [hb])) q hq
        intro x hx
        rcases Array.mem_append.mp hx with h1 | h1
        · exact hacc x h1
        · exact ⟨a, hl a (by simp), groundSchema_produced d (allObjects d p) _
            (fun ty o ho => typeObjects_wellTyped d (allObjects d p) ho) _ _ a h1⟩
  obtain ⟨a, ha, hprod⟩ := fold d.actions #[] (by simp) (fun b hb => hb) op
    (by simpa [rawOps] using hop)
  obtain ⟨i, h1, h2, h3, h4, h5, h5a, h6, h7⟩ := instance_of_produced ha hprod
  exact ⟨⟨⟨i, h1, h2, h3, h4, h6, fun y hy hn _ => h5 y hy hn, h7⟩, h5a⟩⟩

theorem opFacts_raw (d : Domain) (p : Problem) {op : AtomOp} (hop : op ∈ rawOps d p) :
    Nonempty (OpFacts d p op) :=
  (opFacts_raw_add d p hop).map (·.toOpFacts)

/--
And so does every operator that survives the relevance analysis.  No hypothesis is
needed: `relevance_cases` says the analysis either prunes with a closed set or
prunes nothing.
-/
theorem opFacts_pruned (d : Domain) (p : Problem) {op : AtomOp}
    (hop : op ∈ groundedOps d p true) : Nonempty (OpFacts d p op) := by
  rw [groundedOps_true] at hop
  rcases relevance_cases (rawOps d p) p.goal.toArray with ⟨r, hclosed, -, hrdef⟩ | hall
  · obtain ⟨op₀, hop₀, rfl, -, hdel⟩ := relevance_retains hclosed hrdef hop
    obtain ⟨f⟩ := opFacts_raw d p hop₀
    refine ⟨⟨f.inst, f.subPre, ?_, ?_, f.preComplete, f.staticHeld, ?_, f.cost⟩⟩
    · intro a ha
      exact f.subAdd a (Array.mem_filter.mp ha).1
    · intro a ha
      exact f.subDel a (Array.mem_filter.mp ha).1
    · intro y hy hn hpre
      exact hdel _ (f.delComplete y hy hn hpre) hpre
  · rw [hall] at hop
    exact opFacts_raw d p hop

/-- Every operator of a grounded task carries them, pruning on or off. -/
theorem opFacts_ground (d : Domain) (p : Problem) (relevance : Bool) {op : AtomOp}
    (hop : op ∈ groundedOps d p relevance) : Nonempty (OpFacts d p op) := by
  cases relevance with
  | false => exact opFacts_raw d p (by rwa [← groundedOps_false])
  | true => exact opFacts_pruned d p hop

/-! ### Static atoms never move

A predicate is static when no schema adds or deletes it.  So no operator does
either, and an atom with a static predicate has the same truth value in every
state a run passes through.  Domains read `destin`, `above`, `supports` and
`road` this way.
-/

theorem not_static_of_mem_add {d : Domain} {a : Action} (ha : a ∈ d.actions)
    {y : Atom} (hy : y ∈ a.add) : (staticPredicates d).contains y.pred = false := by
  have hchanged : y.pred ∈ d.actions.flatMap fun b => (b.add ++ b.del).map (·.pred) :=
    List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨y, by simp [hy], rfl⟩⟩
  simp only [staticPredicates, List.contains_eq_mem, decide_eq_false_iff_not,
    List.mem_filter, not_and]
  intro _ hb
  rw [decide_eq_true hchanged] at hb
  exact Bool.noConfusion hb

theorem not_static_of_mem_del {d : Domain} {a : Action} (ha : a ∈ d.actions)
    {y : Atom} (hy : y ∈ a.del) : (staticPredicates d).contains y.pred = false := by
  have hchanged : y.pred ∈ d.actions.flatMap fun b => (b.add ++ b.del).map (·.pred) :=
    List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨y, by simp [hy], rfl⟩⟩
  simp only [staticPredicates, List.contains_eq_mem, decide_eq_false_iff_not,
    List.mem_filter, not_and]
  intro _ hb
  rw [decide_eq_true hchanged] at hb
  exact Bool.noConfusion hb

theorem instAtom_pred (params : List TypedName) (args : List Name) (y : Atom) :
    (instAtom params args y).pred = y.pred := rfl

/-- An operator leaves every static atom alone. -/
theorem static_frame {d : Domain} {p : Problem} {o : AtomOp} (hf : OpFacts d p o)
    {a : GroundAtom} (hst : (staticPredicates d).contains a.pred = true)
    (σ : AtomState) : o.applyA σ a = σ a := by
  have hna : a ∉ o.add := by
    intro hmem
    obtain ⟨y, hy, hval⟩ := List.mem_map.mp (hf.subAdd a hmem)
    rw [← hval, instAtom_pred, not_static_of_mem_add hf.inst.mem hy] at hst
    exact Bool.noConfusion hst
  have hnd : a ∉ o.del := by
    intro hmem
    obtain ⟨y, hy, hval⟩ := List.mem_map.mp (hf.subDel a hmem)
    rw [← hval, instAtom_pred, not_static_of_mem_del hf.inst.mem hy] at hst
    exact Bool.noConfusion hst
  have h1 : o.add.contains a = false := by simpa using hna
  have h2 : o.del.contains a = false := by simpa using hnd
  show (if o.add.contains a = true then true
        else if o.del.contains a = true then false else σ a) = σ a
  rw [if_neg (by simp [h1]; exact hna), if_neg (by simp [h2]; exact hnd)]

end Planner
