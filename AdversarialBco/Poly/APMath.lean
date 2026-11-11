/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2Oracle

@[expose] public section

/-!
# The subroutine AP: the procedures of `Df2Oracle.lean` in the shape the machine computes them

`lineSt` is one pass of the loop of LINE on the machine state (a running window, a result or a failure) and
`lineEnd` the last check; `line_eq_lineEnd` writes LINE through them. The other lemmas rewrite the definitions into
the order of operations of the code of `MachAPCode.lean`: `ccUpdate_eq`, `ellConsts_eq`, `ellOne_eq`; and the facts
on `oValsAll`, `oMin`, the coordinate step and the step counts that the machine rules read.
-/

open Matrix

namespace AdversarialBco.Poly.AP

variable {d : ℕ}

/-- One pass of the loop of LINE on its state: a running window `inl W` stops at `(p₀ + 2λ, λ)` when its measured
second difference is at most `τ λ/2`, else it is halved; a result `inr` and a failure `none` stay. -/
noncomputable def lineSt (ev1 : ℝ → ℝ → Option ℝ) (τ : ℝ) :
    Option (LineWin ⊕ (ℝ × ℝ)) → Option (LineWin ⊕ (ℝ × ℝ))
  | some (.inl W) =>
    if W.sd ≤ τ * W.lam / 2 then some (.inr (W.p0 + 2 * W.lam, W.lam)) else (lineHalve ev1 τ W).map .inl
  | o => o

/-- The last check of LINE: a running window stops or fails. -/
noncomputable def lineEnd (τ : ℝ) : Option (LineWin ⊕ (ℝ × ℝ)) → Option (ℝ × ℝ)
  | some (.inl W) => if W.sd ≤ τ * W.lam / 2 then some (W.p0 + 2 * W.lam, W.lam) else none
  | some (.inr r) => some r
  | none => none

theorem lineSt_iterate_none (ev1 : ℝ → ℝ → Option ℝ) (τ : ℝ) (j : ℕ) : (lineSt ev1 τ)^[j] none = none := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply]; exact ih

theorem lineSt_iterate_inr (ev1 : ℝ → ℝ → Option ℝ) (τ : ℝ) (r : ℝ × ℝ) (j : ℕ) :
    (lineSt ev1 τ)^[j] (some (.inr r)) = some (.inr r) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply]; exact ih

theorem lineLoop_eq_lineEnd (ev1 : ℝ → ℝ → Option ℝ) (τ : ℝ) (j : ℕ) (W : LineWin) :
    lineLoop ev1 τ j W = lineEnd τ ((lineSt ev1 τ)^[j] (some (.inl W))) := by
  induction j generalizing W with
  | zero => rw [lineLoop]; rfl
  | succ j ih =>
    rw [lineLoop, Function.iterate_succ_apply]
    by_cases h : W.sd ≤ τ * W.lam / 2
    · simp only [lineSt, h, ite_true, lineSt_iterate_inr, lineEnd]
    · cases hH : lineHalve ev1 τ W with
      | none => simp [lineSt, h, hH, lineSt_iterate_none, lineEnd]
      | some W' => simp [lineSt, h, hH, ih]

theorem line_eq_lineEnd (ev1 : ℝ → ℝ → Option ℝ) (ℓ τ : ℝ) (J : ℕ) :
    line ev1 ℓ τ J = lineEnd τ ((lineSt ev1 τ)^[J] ((lineFirst ev1 ℓ τ).map .inl)) := by
  unfold line
  cases hF : lineFirst ev1 ℓ τ with
  | none => simp [lineSt_iterate_none, lineEnd]
  | some W => simp [lineLoop_eq_lineEnd]

theorem oValsAll_eq_some_iff (ev : (Fin d → ℝ) → ℝ → Option ℝ) (x : Fin d → Fin d → ℝ) (η v : Fin d → ℝ) :
    oValsAll ev x η = some v ↔ ∀ i, ev (x i) (η i) = some (v i) := by
  unfold oValsAll
  constructor
  · -- forward direction: (dite ...) = some v → ∀ i, ev (x i) (η i) = some (v i)
    intro h_eq
    by_cases h : ∀ i, (ev (x i) (η i)).isSome
    · rw [dite_eq_left h] at h_eq
      have h_some_inj := Option.some_inj.mp h_eq
      intro i
      have h_val : (ev (x i) (η i)).get (h i) = v i := by
        simpa using congrFun h_some_inj i
      have hi := h i
      have h_coe := Option.coe_get hi
      rw [h_val] at h_coe
      rw [← h_coe]
    · rw [dite_eq_right h] at h_eq
      injection h_eq
  · -- backward direction: (∀ i, ev (x i) (η i) = some (v i)) → (dite ...) = some v
    intro h_all
    by_cases h : ∀ i, (ev (x i) (η i)).isSome
    · rw [dite_eq_left h]
      apply congrArg some
      ext i
      have h_eq_i := h_all i
      simp [h_eq_i]
    · rw [dite_eq_right h]
      have h_contra : ∀ i, (ev (x i) (η i)).isSome := by
        intro i
        rw [h_all i]
        rfl
      exact absurd h_contra h

theorem oValsAll_eq_none_iff (ev : (Fin d → ℝ) → ℝ → Option ℝ) (x : Fin d → Fin d → ℝ) (η : Fin d → ℝ) :
    oValsAll ev x η = none ↔ ∃ i, ev (x i) (η i) = none := by
  unfold oValsAll
  by_cases h : ∀ i, (ev (x i) (η i)).isSome
  · simp [h]
    intro i h_eq
    have hi_some := h i
    rw [h_eq] at hi_some
    simp at hi_some
  · simp [h]
    push Not at h
    rcases h with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rcases Option.eq_none_or_eq_some (ev (x i) (η i)) with (h' | ⟨v, h'⟩)
    · exact h'
    · exfalso; apply hi; rw [h']; simp

theorem oMin_eq_of (h0 : 0 < d) {δ : Fin d → ℝ} {m : ℝ} (hle : ∀ i, m ≤ δ i) (hex : ∃ i, δ i = m) :
    oMin δ = m := by
  unfold oMin
  rw [dite_eq_left h0]
  apply le_antisymm
  · obtain ⟨i, hi⟩ := hex
    calc
      Finset.univ.inf' _ δ ≤ δ i := Finset.inf'_le δ (Finset.mem_univ i)
      _ = m := hi
  · apply Finset.le_inf'
    intro i _
    exact hle i

theorem update_add_eq_oUnit (y : Fin d → ℝ) (i : Fin d) (s : ℝ) :
    Function.update y i (y i + s) = y + s • oUnit i := by
  ext j
  simp [oUnit, Function.update_apply, Pi.single_apply]
  split_ifs with h
  · subst h
    simp
  · simp

theorem ccUpdate_eq (A : Matrix (Fin d) (Fin d) ℝ) (a c : Fin d → ℝ) :
    ccUpdate A a c =
      (((d : ℝ) * d / ((d : ℝ) * d - 1)) • A +
          (0 - (d : ℝ) * d / ((d : ℝ) * d - 1) * (2 / ((d : ℝ) + 1))) •
            vecMulVec ((1 / Real.sqrt (c ⬝ᵥ (A *ᵥ c))) • (A *ᵥ c)) ((1 / Real.sqrt (c ⬝ᵥ (A *ᵥ c))) • (A *ᵥ c)),
        a + (0 - 1 / ((d : ℝ) + 1)) • ((1 / Real.sqrt (c ⬝ᵥ (A *ᵥ c))) • (A *ᵥ c))) := by
  dsimp [ccUpdate]
  simp only [← one_div]
  apply Prod.ext
  · -- first component
    set α := ((d : ℝ) ^ 2) / ((d : ℝ) ^ 2 - 1) with hα
    set k := 2 / ((d : ℝ) + 1) with hk
    set M := vecMulVec ((1 / Real.sqrt (c ⬝ᵥ (A *ᵥ c))) • (A *ᵥ c)) ((1 / Real.sqrt (c ⬝ᵥ (A *ᵥ c))) • (A *ᵥ c)) with hM
    calc
      α • (A - k • M) = α • A - α • (k • M) := by rw [smul_sub]
      _ = α • A - (α * k) • M := by rw [smul_smul]
      _ = α • A + (-(α * k)) • M := by rw [sub_eq_add_neg, neg_smul]
      _ = α • A + (0 - α * k) • M := by rw [zero_sub]
      _ = ((d : ℝ) * d / ((d : ℝ) * d - 1)) • A + (0 - (d : ℝ) * d / ((d : ℝ) * d - 1) * (2 / ((d : ℝ) + 1))) • M := by
        simp [hα, hk, hM, sq]
  · -- second component
    set b' := (1 / Real.sqrt (c ⬝ᵥ (A *ᵥ c))) • (A *ᵥ c) with hb'
    calc
      a - (1 / ((d : ℝ) + 1)) • b' = a + (-((1 / ((d : ℝ) + 1)) • b')) := by rw [sub_eq_add_neg]
      _ = a + ((-(1 / ((d : ℝ) + 1))) • b') := by rw [neg_smul]
      _ = a + ((0 - 1 / ((d : ℝ) + 1)) • b') := by rw [zero_sub]

theorem ellConsts_ext (a b : EllConsts) (hτ : a.τ = b.τ) (hℓ1 : a.ℓ1 = b.ℓ1) (hN : a.N = b.N) (hJ : a.J = b.J)
    (hB : a.B = b.B) : a = b := by
  cases a; cases b; simp at *; simp [*]

theorem ellConsts_eq (r R : ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) (e : ℝ) :
    ellConsts r R P w e =
      let LF := P.trace * (R + oNorm w)
      let θ := min 1 (e / (3 * LF * R))
      let εQ := θ * r / 2
      let τ := εQ / (36 * (R * R) * Real.sqrt d)
      let ℓ1 := r * εQ / (24 * R)
      let N := ⌈2 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (2 * R / (θ * r))⌉₊ + 1
      let J := ⌈Real.log (8 / (r * τ)) / Real.log 2⌉₊
      let ηmin := τ * ℓ1 / 1600 * Real.exp (Real.log 2 * (0 - 3 * (d : ℝ) * ((J : ℝ) + 1)))
      let B := ⌈Real.log (3 * R / (r * ηmin)) / Real.log 2⌉₊
      ⟨τ, ℓ1, N, J, B⟩ := by
  apply ellConsts_ext
  · unfold ellConsts; dsimp
    apply congrArg (fun x => (min 1 (e / (3 * (P.trace * (R + oNorm w)) * R)) * r / 2) / x)
    ring
  · unfold ellConsts; dsimp
  · unfold ellConsts; dsimp
  · unfold ellConsts; dsimp; simp [Real.logb]
    apply congrArg (fun x => ⌈Real.log (8 / (r * x)) / Real.log 2⌉₊)
    apply congrArg (fun x => min 1 (e / (3 * (P.trace * (R + oNorm w)) * R)) * r / 2 / x)
    ring
  · unfold ellConsts; dsimp
    have h2pos : 0 < (2 : ℝ) := by norm_num
    rw [Real.logb]
    apply congrArg (fun x => ⌈Real.log (3 * R / (r * x)) / Real.log 2⌉₊)
    set A := min 1 (e / (3 * (P.trace * (R + oNorm w)) * R)) * r / 2 with hA
    set s := Real.sqrt (d : ℝ) with hs
    set Jl := ⌈Real.log (8 / (r * (A / (36 * R ^ 2 * s)))) / Real.log 2⌉₊ with hJl
    set Jr := ⌈Real.log (8 / (r * (A / (36 * (R * R) * s)))) / Real.log 2⌉₊ with hJr
    have hτ_eq : A / (36 * R ^ 2 * s) = A / (36 * (R * R) * s) := by
      apply congrArg (fun x => A / x)
      ring
    have hJ_eq : (Jl : ℝ) = (Jr : ℝ) := by
      rw [hJl, hJr, hτ_eq]
    have h_exp_eq : (2 : ℝ) ^ (-(3 * (d : ℝ) * ((Jl : ℝ) + 1))) = Real.exp (Real.log 2 * (0 - 3 * (d : ℝ) * ((Jr : ℝ) + 1))) := by
      rw [hJ_eq]
      rw [Real.rpow_def_of_pos h2pos]
      congr
      ring
    calc
      (A / (36 * R ^ 2 * s) * (r * A / (24 * R)) / 1600) * (2 : ℝ) ^ (-(3 * (d : ℝ) * ((Jl : ℝ) + 1)))
          = (A / (36 * (R * R) * s) * (r * A / (24 * R)) / 1600) * (2 : ℝ) ^ (-(3 * (d : ℝ) * ((Jl : ℝ) + 1))) := by rw [hτ_eq]
      _ = (A / (36 * (R * R) * s) * (r * A / (24 * R)) / 1600) * Real.exp (Real.log 2 * (0 - 3 * (d : ℝ) * ((Jr : ℝ) + 1))) := by rw [h_exp_eq]

theorem ceil_logb_le_of_abs_le {x y : ℝ} (h : |x| ≤ y) : ⌈Real.logb 2 x⌉₊ ≤ ⌈Real.logb 2 y⌉₊ := by
  by_cases hx : x = 0
  · subst hx
    simp [Real.logb_zero]
  · have hx_abs_pos : 0 < |x| := abs_pos.2 hx
    have h_logb : Real.logb 2 x ≤ Real.logb 2 y := by
      calc
        Real.logb 2 x = Real.logb 2 |x| := by rw [Real.logb_abs]
        _ ≤ Real.logb 2 y := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hx_abs_pos h
    exact Nat.ceil_mono h_logb

theorem abs_clamp_sub_le {a0 R w : ℝ} (hR : 0 ≤ R) (ha : |a0| ≤ R) : |max (-R) (min R w) - a0| ≤ 2 * R := by
  have ha_bounds : -R ≤ a0 ∧ a0 ≤ R := abs_le.1 ha
  have hmax_low : -R ≤ max (-R) (min R w) := le_max_left _ _
  have hmax_high : max (-R) (min R w) ≤ R := by
    apply max_le
    · linarith
    · exact min_le_left _ _
  apply abs_le.2
  constructor
  · linarith
  · linarith

open Classical in
theorem ellOne_eq (Q : Set ℝ) (a0 r R p w e : ℝ) :
    ellOne Q a0 r R p w e =
      if R < r then none
      else if R < max a0 (0 - a0) then none
      else if a0 ∉ Q then none
      else if max (0 - R) (min R w) ∈ Q then some (max (0 - R) (min R w))
      else some (oBisectLo (· ∈ Q) a0 (max (0 - R) (min R w))
        ⌈Real.log (max (max (0 - R) (min R w) - a0) (0 - (max (0 - R) (min R w) - a0)) /
            (e / (p * (R + max w (0 - w))))) / Real.log 2⌉₊).1 := by
  unfold ellOne
  have h_abs_a0 : |a0| = max a0 (0 - a0) := by
    rw [abs_eq_max_neg, zero_sub]
  have h_abs_w : |w| = max w (0 - w) := by
    rw [abs_eq_max_neg, zero_sub]
  rw [h_abs_a0, h_abs_w]
  -- Now the LHS has max a0 (0 - a0), max (-R) (min R w), max w (0 - w)
  -- The RHS has max a0 (0 - a0), max (0 - R) (min R w), max w (0 - w)
  -- Rewrite 0 - R to -R on RHS
  simp only [zero_sub]
  -- Now both sides have -R, -a0, -w
  -- The only difference is the ∨ vs nested if
  -- Use ite_or to rewrite the LHS
  rw [ite_or]
  -- Now both sides should be syntactically equal
  unfold Real.logb
  rfl

end AdversarialBco.Poly.AP
