/-
One transition, in the domain's own terms.

This is the interface a heuristic proof should start from.  Given an operator of a
grounded task and a state the search can be in, it hands back:

  * the schema instance the operator is, from `Proofs/GroundingSound.lean`;
  * the atom-level states before and after, from `Proofs/Reachable.lean`;
  * what the operator did to them — added atoms hold, deleted atoms fail, and
    everything else is untouched.

None of that mentions a domain.  A heuristic then reads the instance's schema to
learn which action it was, and `Proofs/FactTables.lean` to turn atoms back into
the facts its own tables are keyed by.  That is the only part that should ever be
domain-dependent.
-/
import Proofs.Reachable
import Proofs.GroundingSound

namespace Planner

open Planner.Pddl

/-! ### What one operator does to an atom-level state -/

theorem applyA_add {o : AtomOp} (σ : AtomState) {a : GroundAtom} (ha : a ∈ o.add) :
    o.applyA σ a = true := by
  have h : o.add.contains a = true := by simpa using ha
  show (if o.add.contains a = true then true
        else if o.del.contains a = true then false else σ a) = true
  rw [if_pos h]

theorem applyA_del {o : AtomOp} (σ : AtomState) {a : GroundAtom} (ha : a ∈ o.del)
    (hna : a ∉ o.add) : o.applyA σ a = false := by
  have h1 : o.add.contains a = false := by simpa using hna
  have h2 : o.del.contains a = true := by simpa using ha
  show (if o.add.contains a = true then true
        else if o.del.contains a = true then false else σ a) = false
  rw [if_neg (by simp [h1]; exact hna), if_pos h2]

theorem applyA_frame {o : AtomOp} (σ : AtomState) {a : GroundAtom}
    (h1 : a ∉ o.add) (h2 : a ∉ o.del) : o.applyA σ a = σ a := by
  have ha : o.add.contains a = false := by simpa using h1
  have hd : o.del.contains a = false := by simpa using h2
  show (if o.add.contains a = true then true
        else if o.del.contains a = true then false else σ a) = σ a
  rw [if_neg (by simp [ha]; exact h1), if_neg (by simp [hd]; exact h2)]

/-! ### The view of one transition -/

/--
Everything a heuristic needs about one step, with no domain in sight.

`inst` is the schema instance the operator is; `before` and `after` are the
atom-level readings of the two states; `subAdd`, `subDel` and `subPre` say the
operator's atoms are among the schema's; and the last three say what changed.
-/
structure StepView (d : Domain) (p : Problem) (relevance : Bool)
    (op : Op) (s s' : State) where
  /-- The operator, before its facts were numbered. -/
  atomOp : AtomOp
  mem : atomOp ∈ groundedOps d p relevance
  /-- The schema instance it is. -/
  inst : Instance d (allObjects d p)
  subPre : ∀ a ∈ atomOp.pre, a ∈ inst.pre
  subAdd : ∀ a ∈ atomOp.add, a ∈ inst.add
  subDel : ∀ a ∈ atomOp.del, a ∈ inst.del
  /-- Grounding drops a precondition only when it is static, so the others survive. -/
  preComplete : ∀ y ∈ inst.schema.pre,
    (staticPredicates d).contains y.pred = false →
      instAtom inst.schema.params inst.args y ∈ atomOp.pre
  /-- A static precondition was checked against `:init` and really was there. -/
  staticHeld : ∀ y ∈ inst.schema.pre, (staticPredicates d).contains y.pred = true →
    (Std.HashSet.ofList p.init).contains (instAtom inst.schema.params inst.args y) = true
  cost : atomOp.cost = inst.cost
  /-- The atom-level states the two packed states stand for. -/
  before : AtomState
  after : AtomState
  absBefore : Abstracts (ground d p relevance) s before
  absAfter : Abstracts (ground d p relevance) s' after
  /-- What the step did. -/
  added : ∀ a ∈ atomOp.add, after a = true
  deleted : ∀ a ∈ atomOp.del, a ∉ atomOp.add → after a = false
  framed : ∀ a, a ∉ atomOp.add → a ∉ atomOp.del → after a = before a

/--
**The view exists for every transition of a grounded task.**  This is the theorem
a heuristic proof should quote instead of assuming anything about grounding.
-/
theorem stepView (d : Domain) (p : Problem) (relevance : Bool)
    (hwf : Task.WF (ground d p relevance))
    (hcost : ∀ o ∈ groundedOps d p relevance, 0 < o.cost)
    {s s' : State} (hreach : Reachable (ground d p relevance) s)
    {op : Op} (hop : op ∈ (ground d p relevance).ops) (hs' : s' = op.apply s) :
    Nonempty (StepView d p relevance op s s') := by
  obtain ⟨σ, habs⟩ := reachable_abstracts d p relevance hwf hcost hreach
  have hops : (ground d p relevance).ops
      = (groundedOps d p relevance).map
        (numberOp (factIndex (allAtoms (groundedOps d p relevance)
          p.goal.toArray)).1) := rfl
  have hmem : op ∈ (groundedOps d p relevance).map
      (numberOp (factIndex (allAtoms (groundedOps d p relevance)
        p.goal.toArray)).1) := by rw [← hops]; exact hop
  rw [Array.mem_map] at hmem
  obtain ⟨o, ho, hnum⟩ := hmem
  obtain ⟨inst, hpre, hadd, hdel, hcompl, hstat, hc⟩ :=
    groundedOps_instance d p relevance ho
  have habs' : Abstracts (ground d p relevance) s' (o.applyA σ) := by
    subst hs'
    rw [← hnum]
    exact assemble_apply (groundedOps d p relevance) p.goal.toArray p.init.toArray
      (allObjects d p).toArray d.name ho (hcost o ho) (hreach.wf hwf) habs
  exact ⟨⟨o, ho, inst, hpre, hadd, hdel, hcompl, hstat, hc, σ, o.applyA σ, habs, habs',
    fun a ha => applyA_add σ ha, fun a ha hna => applyA_del σ ha hna,
    fun a h1 h2 => applyA_frame σ h1 h2⟩⟩

/-! ### Reading an instance

An instance's atoms are its schema's atoms under its arguments, and its arguments
are one well-typed object per parameter.  Both are definitional; naming them is
what lets a domain's case analysis be written without unfolding anything.
-/

namespace Pddl.Instance

variable {d : Domain} {objects : List TypedName}

theorem pre_eq (i : Instance d objects) :
    i.pre = i.schema.pre.map (instAtom i.schema.params i.args) := rfl

theorem add_eq (i : Instance d objects) :
    i.add = i.schema.add.map (instAtom i.schema.params i.args) := rfl

theorem del_eq (i : Instance d objects) :
    i.del = i.schema.del.map (instAtom i.schema.params i.args) := rfl

theorem args_length (i : Instance d objects) :
    i.args.length = i.schema.params.length := i.typed.length_eq.symm

/-- A one-parameter schema takes one well-typed object. -/
theorem args_one (i : Instance d objects) {q : TypedName}
    (hp : i.schema.params = [q]) :
    ∃ o, i.args = [o] ∧ WellTyped d objects q.type o := by
  have hlen : i.args.length = 1 := by rw [args_length, hp]; rfl
  obtain ⟨o, ho⟩ := List.length_eq_one_iff.mp hlen
  refine ⟨o, ho, ?_⟩
  have h := i.typed
  rw [hp, ho] at h
  cases h with
  | cons h1 _ => exact h1

/-- A two-parameter schema takes two. -/
theorem args_two (i : Instance d objects) {q₁ q₂ : TypedName}
    (hp : i.schema.params = [q₁, q₂]) :
    ∃ o₁ o₂, i.args = [o₁, o₂] ∧ WellTyped d objects q₁.type o₁ ∧
      WellTyped d objects q₂.type o₂ := by
  have hlen : i.args.length = 2 := by rw [args_length, hp]; rfl
  obtain ⟨o₁, o₂, ho⟩ := List.length_eq_two.mp hlen
  refine ⟨o₁, o₂, ho, ?_, ?_⟩ <;>
    · have h := i.typed
      rw [hp, ho] at h
      cases h with
      | cons h1 t1 =>
          cases t1 with
          | cons h2 _ => first | exact h1 | exact h2

/-- A three-parameter schema takes three. -/
theorem args_three (i : Instance d objects) {q₁ q₂ q₃ : TypedName}
    (hp : i.schema.params = [q₁, q₂, q₃]) :
    ∃ o₁ o₂ o₃, i.args = [o₁, o₂, o₃] ∧ WellTyped d objects q₁.type o₁ ∧
      WellTyped d objects q₂.type o₂ ∧ WellTyped d objects q₃.type o₃ := by
  have hlen : i.args.length = 3 := by rw [args_length, hp]; rfl
  obtain ⟨o₁, o₂, o₃, ho⟩ := List.length_eq_three.mp hlen
  refine ⟨o₁, o₂, o₃, ho, ?_, ?_, ?_⟩ <;>
    · have h := i.typed
      rw [hp, ho] at h
      cases h with
      | cons h1 t1 =>
          cases t1 with
          | cons h2 t2 =>
              cases t2 with
              | cons h3 _ => first | exact h1 | exact h2 | exact h3

/-- A four-parameter schema takes four. -/
theorem args_four (i : Instance d objects) {q₁ q₂ q₃ q₄ : TypedName}
    (hp : i.schema.params = [q₁, q₂, q₃, q₄]) :
    ∃ o₁ o₂ o₃ o₄, i.args = [o₁, o₂, o₃, o₄] ∧ WellTyped d objects q₁.type o₁ ∧
      WellTyped d objects q₂.type o₂ ∧ WellTyped d objects q₃.type o₃ ∧
      WellTyped d objects q₄.type o₄ := by
  have hlen : i.args.length = 4 := by rw [args_length, hp]; rfl
  rcases hc : i.args with _ | ⟨o₁, rest⟩
  · rw [hc] at hlen; simp at hlen
  · have hrest : rest.length = 3 := by rw [hc] at hlen; simpa using hlen
    obtain ⟨o₂, o₃, o₄, hr⟩ := List.length_eq_three.mp hrest
    have ho : i.args = [o₁, o₂, o₃, o₄] := by rw [hc, hr]
    refine ⟨o₁, o₂, o₃, o₄, by rw [hr], ?_, ?_, ?_, ?_⟩ <;>
      · have h := i.typed
        rw [hp, ho] at h
        cases h with
        | cons h1 t1 =>
            cases t1 with
            | cons h2 t2 =>
                cases t2 with
                | cons h3 t3 =>
                    cases t3 with
                    | cons h4 _ =>
                        first | exact h1 | exact h2 | exact h3 | exact h4

/-- A five-parameter schema takes five. -/
theorem args_five (i : Instance d objects) {q₁ q₂ q₃ q₄ q₅ : TypedName}
    (hp : i.schema.params = [q₁, q₂, q₃, q₄, q₅]) :
    ∃ o₁ o₂ o₃ o₄ o₅, i.args = [o₁, o₂, o₃, o₄, o₅] ∧ WellTyped d objects q₁.type o₁ ∧
      WellTyped d objects q₂.type o₂ ∧ WellTyped d objects q₃.type o₃ ∧
      WellTyped d objects q₄.type o₄ ∧ WellTyped d objects q₅.type o₅ := by
  have hlen : i.args.length = 5 := by rw [args_length, hp]; rfl
  rcases hc : i.args with _ | ⟨o₁, rest⟩
  · rw [hc] at hlen; simp at hlen
  · rcases hc2 : rest with _ | ⟨o₂, rest2⟩
    · rw [hc, hc2] at hlen; simp at hlen
    · have hrest : rest2.length = 3 := by rw [hc, hc2] at hlen; simpa using hlen
      obtain ⟨o₃, o₄, o₅, hr⟩ := List.length_eq_three.mp hrest
      have ho : i.args = [o₁, o₂, o₃, o₄, o₅] := by rw [hc, hc2, hr]
      refine ⟨o₁, o₂, o₃, o₄, o₅, by rw [hr], ?_, ?_, ?_, ?_, ?_⟩ <;>
        · have h := i.typed
          rw [hp, ho] at h
          cases h with
          | cons h1 t1 =>
              cases t1 with
              | cons h2 t2 =>
                  cases t2 with
                  | cons h3 t3 =>
                      cases t3 with
                      | cons h4 t4 =>
                          cases t4 with
                          | cons h5 _ =>
                              first | exact h1 | exact h2 | exact h3 | exact h4 | exact h5

/-- A six-parameter schema takes six well-typed objects. -/
theorem args_six (i : Instance d objects) {q₁ q₂ q₃ q₄ q₅ q₆ : TypedName}
    (hp : i.schema.params = [q₁, q₂, q₃, q₄, q₅, q₆]) :
    ∃ o₁ o₂ o₃ o₄ o₅ o₆, i.args = [o₁, o₂, o₃, o₄, o₅, o₆] ∧
      WellTyped d objects q₁.type o₁ ∧ WellTyped d objects q₂.type o₂ ∧
      WellTyped d objects q₃.type o₃ ∧ WellTyped d objects q₄.type o₄ ∧
      WellTyped d objects q₅.type o₅ ∧ WellTyped d objects q₆.type o₆ := by
  have hlen : i.args.length = 6 := by rw [args_length, hp]; rfl
  rcases hc : i.args with _ | ⟨o₁, rest⟩
  · rw [hc] at hlen; simp at hlen
  · rcases hc2 : rest with _ | ⟨o₂, rest2⟩
    · rw [hc, hc2] at hlen; simp at hlen
    · rcases hc3 : rest2 with _ | ⟨o₃, rest3⟩
      · rw [hc, hc2, hc3] at hlen; simp at hlen
      · have hrest : rest3.length = 3 := by rw [hc, hc2, hc3] at hlen; simpa using hlen
        obtain ⟨o₄, o₅, o₆, hr⟩ := List.length_eq_three.mp hrest
        have ho : i.args = [o₁, o₂, o₃, o₄, o₅, o₆] := by rw [hc, hc2, hc3, hr]
        refine ⟨o₁, o₂, o₃, o₄, o₅, o₆, by rw [hr], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          · have h := i.typed
            rw [hp, ho] at h
            cases h with
            | cons h1 t1 =>
                cases t1 with
                | cons h2 t2 =>
                    cases t2 with
                    | cons h3 t3 =>
                        cases t3 with
                        | cons h4 t4 =>
                            cases t4 with
                            | cons h5 t5 =>
                                cases t5 with
                                | cons h6 _ =>
                                    first
                                      | exact h1 | exact h2 | exact h3
                                      | exact h4 | exact h5 | exact h6

end Pddl.Instance

end Planner
