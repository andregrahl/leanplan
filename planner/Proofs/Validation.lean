/-
What validation established, read back as propositions.

`validateDomain` and `validateProblem` decide whether a parsed pair is in the
supported fragment, and every proof downstream is stated about a pair that
passed.  Several facts the domain records ask for are therefore not open
assumptions at all -- validation already checked them, and this file is where
that gets said.

The pattern is the one `Proofs/CompileSupport.lean` uses for the goal tables: an
assumption a record carries beside something that implies it is redundant, not
unproved.
-/
import Proofs.Grounding

namespace Planner

open Planner.Pddl

/-! ### A passing duplicate check is `List.Nodup` -/

theorem noDuplicates_go_nodup :
    ∀ (ctx : Name) (l : List Name), noDuplicates.go ctx l = .ok () → l.Nodup := by
  intro ctx l
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons n rest ih =>
      intro h
      unfold noDuplicates.go at h
      split at h
      · exact absurd h (by simp [fail])
      · rename_i hcon
        refine List.nodup_cons.mpr ⟨?_, ih h⟩
        intro hmem
        exact hcon (by simpa using hmem)

theorem noDuplicates_nodup {ctx : Name} {l : List Name}
    (h : noDuplicates ctx l = .ok ()) : l.Nodup :=
  noDuplicates_go_nodup ctx l h

/-! ### What `validateProblem` established -/

/-- **The problem's object names are distinct.** -/
theorem validateProblem_objects_nodup {d : Domain} {p q : Problem}
    (h : validateProblem d p = .ok q) : (p.objects.map (·.name)).Nodup := by
  rcases hnd : noDuplicates "object" (p.objects.map (·.name)) with e | u
  · exfalso
    unfold validateProblem at h
    simp only [hnd] at h
    split at h <;>
      simp only [bind, Except.bind, Pure.pure, Except.pure, fail] at h <;>
      cases h
  · exact noDuplicates_nodup (by rw [hnd])

/-! ### What `validateDomain` established -/

/--
A loop whose body only ever yields the state it was given leaves the state
alone.  Validation's `for` loops are all of this shape: each body either checks
something and continues, or fails outright.
-/
theorem forIn_ok_const {α β : Type} {f : α → β → Except String (ForInStep β)} :
    ∀ (l : List α) (init r : β),
      (∀ a s, f a init = .ok s → s = .yield init) →
      forIn l init f = .ok r → r = init := by
  intro l
  induction l with
  | nil =>
      intro init r _ h
      rw [List.forIn_nil] at h
      simp only [Pure.pure, Except.pure] at h
      injection h with h'
      exact h'.symm
  | cons a rest ih =>
      intro init r hf h
      rw [List.forIn_cons] at h
      rcases hfa : f a init with e | s
      · rw [hfa] at h; exact absurd h (by simp [bind, Except.bind])
      · have hs : s = .yield init := hf a s hfa
        subst hs
        rw [hfa] at h
        simp only [bind, Except.bind] at h
        exact ih init r hf h

/--
And every body call of a loop that succeeded succeeded itself, so a check the
body makes holds of every element.
-/
theorem forIn_ok_each {α β : Type} {f : α → β → Except String (ForInStep β)} :
    ∀ (l : List α) (init r : β),
      (∀ a s, f a init = .ok s → s = .yield init) →
      forIn l init f = .ok r → ∀ a ∈ l, ∃ s, f a init = .ok s := by
  intro l
  induction l with
  | nil => intro _ _ _ _ a ha; simp at ha
  | cons a rest ih =>
      intro init r hf h b hb
      rw [List.forIn_cons] at h
      rcases hfa : f a init with e | s
      · rw [hfa] at h; exact absurd h (by simp [bind, Except.bind])
      · have hs : s = .yield init := hf a s hfa
        subst hs
        rw [hfa] at h
        simp only [bind, Except.bind] at h
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact ⟨_, hfa⟩
        · exact ih init r hf h b hb'

/-- **The domain's constant names are distinct.** -/
theorem validateDomain_constants_nodup {d e : Domain}
    (h : validateDomain d = .ok e) : (d.constants.map (·.name)).Nodup := by
  rcases hnd : noDuplicates "constant" (d.constants.map (·.name)) with err | u
  · exfalso
    unfold validateDomain at h
    simp only [hnd, bind, Except.bind, Pure.pure, Except.pure, fail] at h
    repeat' (first | cases h | split at h)
    -- what is left is the loop reporting an early return, which it never does:
    -- its body either yields the state unchanged or fails outright.
    rename_i _ v hloop _ hfst
    have hv : v = ⟨none, PUnit.unit⟩ :=
      forIn_ok_const _ _ _
        (by intro a s hs
            split at hs
            · injection hs with h'
              exact h'.symm
            · cases hs)
        hloop
    rw [hv] at hfst
    exact absurd hfst (by simp)
  · exact noDuplicates_nodup (by rw [hnd])

/-! ### The record field this discharges -/

/--
A parsed pair that passed both validators.

Nine of the ten domain records ask for `namesNodup`, that the objects a task
mentions have distinct names.  Validation already decided it: the problem's
objects are checked for duplicates, the domain's constants are, and an object
that shadows a constant is rejected.  The third of those lives inside a `for`
loop over the objects, so it is the one that needs `forIn_ok_each`.
-/
structure Validated (d : Domain) (p : Problem) : Prop where
  domainOK : validateDomain d = .ok d
  problemOK : validateProblem d p = .ok p

/-- **No object shadows a domain constant.** -/
theorem Validated.no_shadow {d : Domain} {p : Problem} (h : Validated d p) :
    ∀ o ∈ p.objects, d.constants.all (fun c => c.name != o.name) := by
  intro o ho
  by_contra hc
  simp only [List.all_eq_true, bne_iff_ne, ne_eq, not_forall, Classical.not_imp,
    Decidable.not_not] at hc
  obtain ⟨c, hcm, hname⟩ := hc
  have hany : d.constants.any (·.name == o.name) = true :=
    List.any_eq_true.mpr ⟨c, hcm, by simp [hname]⟩
  have hp := h.problemOK
  unfold validateProblem at hp
  simp only [bind, Except.bind, Pure.pure, Except.pure, fail, hany] at hp
  split at hp
  case isFalse => cases hp
  case isTrue =>
  split at hp
  case h_1 => cases hp
  case h_2 =>
  split at hp
  case h_1 => cases hp
  case h_2 _ v hloop =>
    -- the loop over the objects succeeded, so its body succeeded at `o` too --
    -- but at `o` the body sees the shadowing and fails.
    obtain ⟨s, hs⟩ := forIn_ok_each _ _ _
      (by intro a s hs
          split at hs
          · cases hs
          · split at hs
            · cases hs
            · injection hs with h'
              exact h'.symm)
      hloop o ho
    split at hs
    · cases hs
    · rw [if_pos hany] at hs
      cases hs

/-- **The names a task's objects carry are distinct** — what the records assume. -/
theorem Validated.namesNodup {d : Domain} {p : Problem} (h : Validated d p) :
    ((allObjects d p).map (·.name)).Nodup := by
  show ((p.objects ++ d.constants).map (·.name)).Nodup
  rw [List.map_append]
  refine List.Nodup.append (validateProblem_objects_nodup h.problemOK)
    (validateDomain_constants_nodup h.domainOK) ?_
  intro x hx hy
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
  obtain ⟨c, hc, hceq⟩ := List.mem_map.mp hy
  have := h.no_shadow o ho
  rw [List.all_eq_true] at this
  have hne := this c hc
  simp only [bne_iff_ne, ne_eq] at hne
  exact hne hceq

end Planner
