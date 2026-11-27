/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.APMath

@[expose] public section

/-!
# The subroutine AP: SEP and the loop of ELL-cap in the shape the machine computes them

`valsInv` is the invariant of the loops of SEP that ask the values `v⁺`, `v⁻` (the flag and the array after `t`
turns), `minInv` the one of the loop of the least scale; `sepTailF` is SEP after its searches and `ellIt` one pass of
the loop of ELL-cap on its state. The lemmas give their steps and their ends, and the tests the code makes.
-/

open Matrix

namespace AdversarialBco.Poly.AP

variable {d : ℕ}

/-- The invariant of a loop of values after `t` turns: the flag `fl` is `f₀` while every value asked so far succeeded,
else `0`; the array `f` holds the values that succeeded. -/
def valsInv (ev : (Fin d → ℝ) → ℝ → Option ℝ) (x : Fin d → Fin d → ℝ) (η : Fin d → ℝ) (f0 : ℝ) (t : ℕ) (fl : ℝ)
    (f : Fin d → ℝ) : Prop :=
  (fl = if ∀ j : Fin d, j.val < t → (ev (x j) (η j)).isSome then f0 else 0) ∧
    ∀ j : Fin d, j.val < t → ∀ v, ev (x j) (η j) = some v → f j = v

/-- The invariant of the loop of the least scale after `t` turns: `m` is at most the first `t` scales and is one of
the scales. -/
def minInv (δ : Fin d → ℝ) (t : ℕ) (m : ℝ) : Prop := (∀ j : Fin d, j.val < t → m ≤ δ j) ∧ ∃ j, δ j = m

/-- SEP after its searches, from their state `st`. -/
noncomputable def sepTailF (ev : (Fin d → ℝ) → ℝ → Option ℝ) (τ : ℝ) (st : SepSt d) :
    Option ((Fin d → ℝ) × (Fin d → ℝ)) := do
  let y := st.1
  let δ := st.2.2
  let _v0 ← ev y (τ * oMin δ / 400)
  let vp ← oValsAll ev (fun i => y + δ i • oUnit i) (fun i => τ * δ i / 400)
  let vm ← oValsAll ev (fun i => y - δ i • oUnit i) (fun i => τ * δ i / 400)
  pure (y, fun i => (vp i - vm i) / (2 * δ i))

/-- One pass of the loop of ELL-cap on its state: a running state takes a step, a returned point or a failure
stays. -/
noncomputable def ellIt (Q : Set (Fin d → ℝ)) (a0 : Fin d → ℝ) (r R : ℝ) (P : Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (k : EllConsts) : Option (EllSt d ⊕ (Fin d → ℝ)) → Option (EllSt d ⊕ (Fin d → ℝ))
  | some (.inl st) => ellStep Q a0 r R P w k st
  | o => o

theorem valsInv_zero (ev : (Fin d → ℝ) → ℝ → Option ℝ) (x : Fin d → Fin d → ℝ) (η : Fin d → ℝ) (f0 : ℝ)
    (f : Fin d → ℝ) : valsInv ev x η f0 0 f0 f := by
  unfold valsInv
  have h_empty : ∀ j : Fin d, ¬ (j.val < 0) := by
    intro j
    exact Nat.not_lt_zero _
  constructor
  · simp
  · intro j hlt
    exact absurd hlt (h_empty j)

theorem valsInv_none {ev : (Fin d → ℝ) → ℝ → Option ℝ} {x : Fin d → Fin d → ℝ} {η : Fin d → ℝ} {f0 : ℝ} {t : ℕ}
    {fl : ℝ} {f : Fin d → ℝ} (h : valsInv ev x η f0 t fl f) (i : Fin d) (hi : i.val = t)
    (hv : ev (x i) (η i) = none) : valsInv ev x η f0 (t + 1) 0 f := by
  rcases h with ⟨hfl, hvals⟩
  have hfalse : ¬ (∀ j : Fin d, j.val < t + 1 → (ev (x j) (η j)).isSome) := by
    intro hall
    have hi' : i.val < t + 1 := by omega
    have hisome := hall i hi'
    rw [hv] at hisome
    simp at hisome
  refine ⟨?_, ?_⟩
  · split
    · rename_i h; exact absurd h hfalse
    · rfl
  · intro j hjval v hsome
    have hle : j.val ≤ t := by omega
    by_cases hlt : j.val < t
    · exact hvals j hlt v hsome
    · have heq : j.val = t := by omega
      have hji : j = i := Fin.ext (heq.trans hi.symm)
      subst hji
      rw [hv] at hsome
      simp at hsome

theorem valsInv_some {ev : (Fin d → ℝ) → ℝ → Option ℝ} {x : Fin d → Fin d → ℝ} {η : Fin d → ℝ} {f0 : ℝ} {t : ℕ}
    {fl : ℝ} {f : Fin d → ℝ} (h : valsInv ev x η f0 t fl f) (i : Fin d) (hi : i.val = t) {v : ℝ}
    (hv : ev (x i) (η i) = some v) : valsInv ev x η f0 (t + 1) fl (Function.update f i v) := by
  rcases h with ⟨hfl, hf⟩
  unfold valsInv
  have hisSome : (ev (x i) (η i)).isSome := by
    rw [hv]
    rfl
  constructor
  · rw [hfl]
    split <;> rename_i h_cond_t
    · have h_cond_t1 : ∀ j : Fin d, j.val < t + 1 → (ev (x j) (η j)).isSome = true := by
        intro j hj
        have h_cases : j.val < t ∨ j.val = t := by omega
        rcases h_cases with (hlt | heq)
        · exact h_cond_t j hlt
        · have hji : j = i := Fin.ext (heq.trans hi.symm)
          subst hji
          exact hisSome
      split <;> rename_i h_cond_t1'
      · rfl
      · exfalso; exact h_cond_t1' h_cond_t1
    · split <;> rename_i h_cond_t1
      · have h_cond_t' : ∀ j : Fin d, j.val < t → (ev (x j) (η j)).isSome = true := by
          intro j hj
          apply h_cond_t1 j
          omega
        exfalso; exact h_cond_t h_cond_t'
      · rfl
  · intro j hj
    have h_cases : j.val < t ∨ j.val = t := by omega
    rcases h_cases with (hlt | heq)
    · have hji_ne : j ≠ i := by
        intro h_eq
        subst h_eq
        rw [hi] at hlt
        exact lt_irrefl t hlt
      have hf_j := hf j hlt
      intro v' hv'
      have h_eq : f j = v' := hf_j v' hv'
      simpa [Function.update_of_ne hji_ne, h_eq] using hv'
    · have hji : j = i := Fin.ext (heq.trans hi.symm)
      subst hji
      intro v' hv'
      have h_v_eq : v' = v := by
        have h_eq : some v = some v' := hv.symm.trans hv'
        exact (Option.some.inj h_eq).symm
      simpa [Function.update_self, h_v_eq] using hv'

theorem valsInv_final {ev : (Fin d → ℝ) → ℝ → Option ℝ} {x : Fin d → Fin d → ℝ} {η : Fin d → ℝ} {f0 fl : ℝ}
    {f : Fin d → ℝ} (h : valsInv ev x η f0 d fl f) :
    (oValsAll ev x η = none → fl = 0) ∧ ∀ vp, oValsAll ev x η = some vp → fl = f0 ∧ f = vp := by
  rcases h with ⟨hfl, hf⟩
  have h_all_lt : ∀ j : Fin d, j.val < d := fun j => j.2
  have hfl' : fl = if ∀ j : Fin d, (ev (x j) (η j)).isSome then f0 else 0 := by
    simpa [h_all_lt] using hfl
  constructor
  · intro hnone
    have h_not_all : ¬ ∀ j : Fin d, (ev (x j) (η j)).isSome := by
      intro hall
      unfold oValsAll at hnone
      simp [hall] at hnone
    simp [hfl', h_not_all]
  · intro vp hsome
    have hall : ∀ j : Fin d, (ev (x j) (η j)).isSome := by
      unfold oValsAll at hsome
      simp at hsome
      rcases hsome with ⟨h, _⟩
      exact h
    have hfl_eq : fl = f0 := by
      simp [hfl', hall]
    have hf_eq : f = vp := by
      ext i
      have h_vp_i : vp i = (ev (x i) (η i)).get (hall i) := by
        unfold oValsAll at hsome
        simp [hall] at hsome
        have h_eq_fun : (fun i => (ev (x i) (η i)).get (hall i)) = vp := by
          simpa using hsome
        rw [← h_eq_fun]
      have h_ev : ev (x i) (η i) = some (vp i) := by
        rw [h_vp_i]
        exact (Option.some_get (hall i)).symm
      exact hf i (h_all_lt i) (vp i) h_ev
    exact And.intro hfl_eq hf_eq

theorem minInv_step {δ : Fin d → ℝ} {t : ℕ} {m : ℝ} (h : minInv δ t m) (i : Fin d) (hi : i.val = t) :
    minInv δ (t + 1) (min m (δ i)) := by
  rcases h with ⟨hle, j0, hj0⟩
  refine ⟨?_, ?_⟩
  · intro j hj
    have h_le_t : j.val ≤ t := by omega
    rcases lt_or_eq_of_le h_le_t with (h_lt | h_eq)
    · have hmj : m ≤ δ j := hle j h_lt
      calc
        min m (δ i) ≤ m := min_le_left _ _
        _ ≤ δ j := hmj
    · have hji : j = i := by
        apply Fin.ext
        rw [h_eq, hi]
      rw [hji]
      calc
        min m (δ i) ≤ δ i := min_le_right _ _
        _ = δ i := rfl
  · rcases le_total m (δ i) with (hm | hm)
    · have h_min : min m (δ i) = m := min_eq_left hm
      rw [h_min]
      exact ⟨j0, hj0⟩
    · have h_min : min m (δ i) = δ i := min_eq_right hm
      rw [h_min]
      exact ⟨i, rfl⟩

theorem minInv_final (h0 : 0 < d) {δ : Fin d → ℝ} {m : ℝ} (h : minInv δ d m) : oMin δ = m := by
  rcases h with ⟨hle, j0, hj0⟩
  unfold oMin
  rw [dite_eq_left h0]
  apply le_antisymm
  · have := Finset.inf'_le (Finset.mem_univ j0) (f := δ)
    calc
      Finset.univ.inf' _ δ ≤ δ j0 := this
      _ = m := hj0
  · apply Finset.le_inf'
    intro j hj
    apply hle j
    exact j.isLt

theorem sep_eq_bind (ev : (Fin d → ℝ) → ℝ → Option ℝ) (y0 : Fin d → ℝ) (τ ℓ1 L : ℝ) (J : ℕ) :
    sep ev y0 τ ℓ1 L J = (sepCoords ev y0 τ ℓ1 L J d).bind (sepTailF ev τ) := by
  rfl

theorem sepCoords_succ_lt (ev : (Fin d → ℝ) → ℝ → Option ℝ) (y0 : Fin d → ℝ) (τ ℓ1 L : ℝ) (J : ℕ) {k : ℕ}
    (hk : k < d) :
    sepCoords ev y0 τ ℓ1 L J (k + 1) = (sepCoords ev y0 τ ℓ1 L J k).bind (sepCoord ev τ L J ⟨k, hk⟩) := by
  simp [sepCoords, hk]

theorem sepCoord_eq (ev : (Fin d → ℝ) → ℝ → Option ℝ) (τ L : ℝ) (J : ℕ) (i : Fin d) (st : SepSt d) :
    sepCoord ev τ L J i st = (line (fun s η => ev (st.1 + s • oUnit i) η) st.2.1 τ J).bind
      (fun r => some (st.1 + r.1 • oUnit i, τ * r.2 / (16 * L), Function.update st.2.2 i r.2)) := by
  rfl

theorem add_zero_sub_smul (y u : Fin d → ℝ) (a : ℝ) : y + (0 - a) • u = y - a • u := by
  ext j; simp; ring

theorem not_dot_self_pos_iff (g : Fin d → ℝ) : ¬ (0 < g ⬝ᵥ g) ↔ g = 0 := by
  have h_nonneg : 0 ≤ g ⬝ᵥ g := by
    simpa using dotProduct_star_self_nonneg (R := ℝ) g
  constructor
  · intro h
    have hle : g ⬝ᵥ g ≤ 0 := by linarith
    have heq : g ⬝ᵥ g = 0 := le_antisymm hle h_nonneg
    exact (dotProduct_self_eq_zero.mp heq)
  · intro h
    rw [h]
    simp

theorem ellLoop_eq_iterate (Q : Set (Fin d → ℝ)) (a0 : Fin d → ℝ) (r R : ℝ) (P : Matrix (Fin d) (Fin d) ℝ)
    (w : Fin d → ℝ) (k : EllConsts) (j : ℕ) :
    ellLoop Q a0 r R P w k j =
      (ellIt Q a0 r R P w k)^[j] (some (.inl ⟨(R ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ), 0, none⟩)) := by
  induction j with
  | zero =>
    simp [ellLoop]
  | succ j ih =>
    simp [ellLoop, Function.iterate_succ_apply', ih]
    cases h : (ellIt Q a0 r R P w k)^[j] (some (.inl ⟨(R ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ), 0, none⟩))
    · rfl
    · case some val =>
      cases val with
      | inl st => rfl
      | inr mu => rfl

theorem ellF_eq_code (P : Matrix (Fin d) (Fin d) ℝ) (w a : Fin d → ℝ) :
    ellF P w a = 1 / 2 * ((a + (-1 : ℝ) • w) ⬝ᵥ (P *ᵥ (a + (-1 : ℝ) • w))) := by
  simp [ellF, sub_eq_add_neg]

end AdversarialBco.Poly.AP
