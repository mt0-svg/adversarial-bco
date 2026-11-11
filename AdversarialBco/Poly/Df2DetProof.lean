/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2

@[expose] public section

/-!
# DF2, first layer: the deterministic statements

Proofs of the deterministic `Prop`s of `Df2.lean`, statements unchanged, one theorem `<name>_holds` each:
`lemmaDFI_holds`, `lemmaMON_holds`, `propINC2_holds`, `lemmaD2_holds`,
`lemmaONS2Core_holds`, `lemmaZCore_holds`, `df2RowZ_holds`, `df2Trivial_holds`, `df2Carriers_holds`.

* Proposition D.8 goes through `Df2Det.inc2_core`, stated for any sequence of functions `Φ t` with Lemma D.7 and the
  lower bound `Φ_t ≥ -dev'` of the event of Lemma DQ as hypotheses. The last point of the segment in the paper is
  replaced by connectedness (`Df2Det.segment_clopen`): on `[0, 1]` the set where every `|x_θ - μ_s|²_{P_s}` is `< r` is
  open, contains `0`, and its closure in `[0, 1]` lies in it, since `≤ r` everywhere gives `≤ 8 (c₁ρ + 2 dev') < r`.
* Lemma D.13 is the one-round identity `Df2Det.ons2_step` (no sign on `η`, `P₁` or the defects) summed by
  `Df2Det.telescope_ons`.
* The row of Lemma D.18 uses `e^{-x} d n x ≤ 1/16` (`Df2Det.rowz_core`, from `x ≤ 2 e^{x/2}` and `e^{x/2} ≥ e^7 d n`), with
  `κ₀^{1/2}, (32/9)^{1/2} ≤ 2` and `√d ≤ d`: the left side is at most `9/16`.

Hypotheses of the statements that the proofs do not read: `IsClosed Keps`, the bounds by `pri` on `K_ε` and `pri ≤ ρ`
in `PropINC2`;
`0 < h` and `0 ≤ e` in `LemmaD2`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix RealInnerProductSpace

namespace AdversarialBco.Poly.Df2Det

/-! ## Quadratic forms -/

theorem df2Sq_nonneg {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosDef) (v : Fin d → ℝ) : 0 ≤ df2Sq P v := by
  simpa [df2Sq] using hP.posSemidef.dotProduct_mulVec_nonneg v

theorem df2Sq_comb {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (a b : Fin d → ℝ) (θ : ℝ) :
    θ * df2Sq P a + (1 - θ) * df2Sq P b - df2Sq P (θ • a + (1 - θ) • b) = θ * (1 - θ) * df2Sq P (a - b) := by
  unfold df2Sq
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub, dotProduct_add, add_dotProduct,
    smul_dotProduct, dotProduct_smul, sub_dotProduct, dotProduct_sub, smul_eq_mul]
  ring

theorem df2Sq_comb_le {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosDef)
    (a b : Fin d → ℝ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    df2Sq P (θ • a + (1 - θ) • b) ≤ θ * df2Sq P a + (1 - θ) * df2Sq P b := by
  have h := df2Sq_comb P a b θ
  have h2 := df2Sq_nonneg hP (a - b)
  have h3 : 0 ≤ θ * (1 - θ) := mul_nonneg h0 (by linarith)
  nlinarith

theorem df2Quad_comb_le {d : ℕ} (k : ℝ) (b : Fin d → ℝ) {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : P.PosDef) (y y' : Fin d → ℝ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    df2Quad k b P (θ • y + (1 - θ) • y') ≤ θ * df2Quad k b P y + (1 - θ) * df2Quad k b P y' := by
  unfold df2Quad
  have h := df2Sq_comb_le hP y y' h0 h1
  have hl : b ⬝ᵥ (θ • y + (1 - θ) • y') = θ * (b ⬝ᵥ y) + (1 - θ) * (b ⬝ᵥ y') := by
    simp [dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [hl]
  linarith

theorem mid_eq {d : ℕ} (x y : Fin d → ℝ) : (1 / 2 : ℝ) • (x + y) = (1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • y := by
  rw [smul_add]; norm_num

theorem df2Sq_continuous {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (a b c : Fin d → ℝ) :
    Continuous fun θ : ℝ => df2Sq P (θ • a + (1 - θ) • b - c) := by
  have h : Continuous fun θ : ℝ => θ • a + (1 - θ) • b - c := by fun_prop
  exact h.dotProduct (continuous_const.matrix_mulVec h)

theorem segment_clopen {ι : Type*} (F : Finset ι) (q : ι → ℝ → ℝ) (B r : ℝ)
    (hq : ∀ i ∈ F, Continuous (q i)) (hBr : B < r) (h0 : ∀ i ∈ F, q i 0 ≤ B)
    (hstep : ∀ θ ∈ Set.Icc (0 : ℝ) 1, (∀ i ∈ F, q i θ ≤ r) → ∀ i ∈ F, q i θ ≤ B) :
    ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ i ∈ F, q i θ ≤ B := by
  intro θ hθ
  have hUo : IsOpen {θ : ℝ | ∀ i ∈ F, q i θ < r} := by
    have : {θ : ℝ | ∀ i ∈ F, q i θ < r} = ⋂ i ∈ F, {θ | q i θ < r} := by ext; simp
    rw [this]
    exact isOpen_biInter_finset fun i hi => isOpen_lt (hq i hi) continuous_const
  have hsub : Set.Icc (0 : ℝ) 1 ⊆ {θ : ℝ | ∀ i ∈ F, q i θ < r} := by
    refine isPreconnected_Icc.subset_of_closure_inter_subset hUo
      ⟨0, ⟨le_rfl, zero_le_one⟩, fun i hi => (h0 i hi).trans_lt hBr⟩ ?_
    rintro θ ⟨hcl, hθ⟩
    have hle : ∀ i ∈ F, q i θ ≤ r := by
      intro i hi
      have hcl' : closure {θ : ℝ | ∀ i ∈ F, q i θ < r} ⊆ {θ | q i θ ≤ r} :=
        closure_minimal (fun x hx => (hx i hi).le) (isClosed_le (hq i hi) continuous_const)
      exact hcl' hcl
    exact fun i hi => (hstep θ hθ hle i hi).trans_lt hBr
  exact hstep θ hθ (fun i hi => (hsub hθ i hi).le)

theorem df2Sq_add_smul {d : ℕ} (P H : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) (v : Fin d → ℝ) :
    df2Sq (P + η • H) v = df2Sq P v + η * df2Sq H v := by
  simp [df2Sq, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]

theorem ons2_step {d : ℕ} (P H S' : Matrix (Fin d) (Fin d) ℝ) (μ g y : Fin d → ℝ) (η : ℝ)
    (hsym : (P + η • H)ᵀ = P + η • H) (hS : S' * (P + η • H) = 1) :
    η * (g ⬝ᵥ (μ - y) - (1 / 2) * df2Sq H (y - μ)) =
      (1 / 2) * df2Sq P (μ - y) - (1 / 2) * df2Sq (P + η • H) (μ - η • (S' *ᵥ g) - y) +
        η ^ 2 / 2 * df2Sq S' g := by
  have hadd := df2Sq_add_smul P H η (μ - y)
  set P' := P + η • H with hP'
  have hPS : P' * S' = 1 := mul_eq_one_comm.mp hS
  have hz : P' *ᵥ (S' *ᵥ g) = g := by rw [Matrix.mulVec_mulVec, hPS, Matrix.one_mulVec]
  have hv : μ - η • (S' *ᵥ g) - y = (μ - y) - η • (S' *ᵥ g) := by abel
  have h1 : (S' *ᵥ g) ⬝ᵥ (P' *ᵥ (μ - y)) = g ⬝ᵥ (μ - y) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, hz]
  have hexp : df2Sq P' ((μ - y) - η • (S' *ᵥ g)) =
      df2Sq P' (μ - y) - 2 * η * (g ⬝ᵥ (μ - y)) + η ^ 2 * df2Sq S' g := by
    unfold df2Sq
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hz]
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul, h1]
    rw [dotProduct_comm μ g, dotProduct_comm y g, dotProduct_comm (S' *ᵥ g) g]
    ring
  have hneg : df2Sq H (y - μ) = df2Sq H (μ - y) := by
    unfold df2Sq
    rw [← neg_sub μ y, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  rw [hv, hexp, hadd, hneg]
  ring

theorem telescope_ons (t : ℕ) (ht : 1 ≤ t) (f D W G ep : ℕ → ℝ)
    (hf : ∀ s, 1 ≤ s → s ≤ t → f s = (1 / 2) * D s - (1 / 2) * W s + G s)
    (hstep : ∀ s, 1 ≤ s → s < t → D (s + 1) ≤ W s + 2 * ep s) (hlast : 0 ≤ W t) :
    ∑ s ∈ Finset.Icc 1 t, f s ≤ (1 / 2) * D 1 + ∑ s ∈ Finset.Ico 1 t, ep s + ∑ s ∈ Finset.Icc 1 t, G s := by
  have claim : ∀ m, 1 ≤ m → m ≤ t → ∑ s ∈ Finset.Icc 1 m, f s ≤
      (1 / 2) * D 1 + ∑ s ∈ Finset.Ico 1 m, ep s + ∑ s ∈ Finset.Icc 1 m, G s - (1 / 2) * W m := by
    intro m hm1
    induction m, hm1 using Nat.le_induction with
    | base =>
      intro h1t
      have := hf 1 le_rfl h1t
      simp only [Finset.Icc_self, Finset.sum_singleton, Finset.Ico_self, Finset.sum_empty]
      linarith
    | succ m hm ih =>
      intro hmt
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Ico_succ_top hm, Finset.sum_Icc_succ_top (by omega)]
      have h0 := ih (by omega)
      have h1 := hf (m + 1) (by omega) hmt
      have h2 := hstep m hm (by omega)
      linarith
  have := claim t ht le_rfl
  linarith

theorem rowz_core (u x : ℝ) (hu : 1 ≤ u) (hx : 14 + 3 * Real.log u ≤ x) :
    Real.exp (-x) * u * x ≤ 1 / 16 := by
  have hlog : 0 ≤ Real.log u := Real.log_nonneg hu
  have hu0 : 0 < u := by linarith
  have hEpos : 0 < Real.exp (x / 2) := Real.exp_pos _
  have hxE : x ≤ 2 * Real.exp (x / 2) := by have := Real.add_one_le_exp (x / 2); linarith
  have he : 2 ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  have he7 : 32 ≤ Real.exp 7 := by
    have h7 : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h7]
    have := pow_le_pow_left₀ (by norm_num) he 7
    linarith
  have hEu : 32 * u ≤ Real.exp (x / 2) := by
    have h2 : Real.exp (7 + Real.log u) ≤ Real.exp (x / 2) := Real.exp_le_exp.2 (by linarith)
    rw [Real.exp_add, Real.exp_log hu0] at h2
    nlinarith
  have hexp : Real.exp (-x) * (Real.exp (x / 2) * Real.exp (x / 2)) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    have : -x + (x / 2 + x / 2) = 0 := by ring
    rw [this, Real.exp_zero]
  have h1 : 16 * (u * x) ≤ 32 * u * Real.exp (x / 2) := by nlinarith [mul_le_mul_of_nonneg_left hxE hu0.le]
  have h2 : 32 * u * Real.exp (x / 2) ≤ Real.exp (x / 2) * Real.exp (x / 2) :=
    mul_le_mul_of_nonneg_right hEu hEpos.le
  have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos (-x)).le
  linarith

end AdversarialBco.Poly.Df2Det

namespace AdversarialBco.Poly

open Df2Det

/-- Lemma DF-I. -/
theorem lemmaDFI_holds : LemmaDFI := by
  intro d k b P y y'
  have hid : df2Quad k b P y + df2Quad k b P y' - 2 * df2Quad k b P ((1 / 2 : ℝ) • (y + y')) =
      df2Sq P (y - y') / 4 := by
    unfold df2Quad df2Sq
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub, dotProduct_add, add_dotProduct,
      smul_dotProduct, dotProduct_smul, sub_dotProduct, dotProduct_sub, smul_eq_mul]
    ring
  exact ⟨hid, fun c c' e h1 h2 h3 => by linarith⟩

/-- Lemma D.7. -/
theorem lemmaMON_holds : LemmaMON := by
  intro d Φ0 Ω Ωh S BR τ dev' hS hΩ hdev u t hut htτ y hy
  have hy' : y ∈ S u ∩ BR := ⟨hS u t hut hy.1, hy.2⟩
  have h1 := abs_le.mp (hdev u (le_trans hut htτ) y hy')
  have h2 := abs_le.mp (hdev t htτ y hy)
  have h3 := hΩ u t y hut
  linarith [h1.2, h2.1]

end AdversarialBco.Poly

namespace AdversarialBco.Poly.Df2Det

/-! ## Proposition D.8 -/

theorem df2S_anti {d : ℕ} {μ : ℕ → Fin d → ℝ} {P : ℕ → Matrix (Fin d) (Fin d) ℝ} {r : ℝ} {u t : ℕ}
    (hut : u ≤ t) : df2S μ P r t ⊆ df2S μ P r u :=
  fun _ hy s hs1 hsu => hy s hs1 (le_trans hsu hut)

theorem df2S_comb {d : ℕ} {μ : ℕ → Fin d → ℝ} {P : ℕ → Matrix (Fin d) (Fin d) ℝ} {r : ℝ} {t : ℕ}
    (hPD : ∀ s, 1 ≤ s → s ≤ t → (P s).PosDef) {x y : Fin d → ℝ} (hx : x ∈ df2S μ P r t)
    (hy : y ∈ df2S μ P r t) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : θ • x + (1 - θ) • y ∈ df2S μ P r t := by
  intro s hs1 hst
  have heq : θ • x + (1 - θ) • y - μ s = θ • (x - μ s) + (1 - θ) • (y - μ s) := by module
  rw [heq]
  have hx' := hx s hs1 hst
  have hy' := hy s hs1 hst
  have h1' : 0 ≤ 1 - θ := by linarith
  calc _ ≤ θ * df2Sq (P s) (x - μ s) + (1 - θ) * df2Sq (P s) (y - μ s) :=
        df2Sq_comb_le (hPD s hs1 hst) _ _ h0 h1
    _ ≤ θ * r + (1 - θ) * r := by gcongr
    _ = r := by ring

theorem df2R_comb {d : ℕ} {Keps : Set (Fin d → ℝ)} {Φ : ℕ → (Fin d → ℝ) → ℝ} {c : ℝ} {u : ℕ}
    {Pu : Matrix (Fin d) (Fin d) ℝ} (hKc : Convex ℝ Keps) (hP : Pu.PosDef)
    (hq : ∃ k b, Φ (u - 1) = df2Quad k b Pu) {x y : Fin d → ℝ} (hx : x ∈ df2R Keps Φ c u)
    (hy : y ∈ df2R Keps Φ c u) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : θ • x + (1 - θ) • y ∈ df2R Keps Φ c u := by
  obtain ⟨k, b, hkb⟩ := hq
  refine ⟨hKc hx.1 hy.1 h0 (by linarith) (by ring), ?_⟩
  have hx2 : Φ (u - 1) x ≤ c := hx.2
  have hy2 : Φ (u - 1) y ≤ c := hy.2
  show Φ (u - 1) (θ • x + (1 - θ) • y) ≤ c
  rw [hkb] at hx2 hy2 ⊢
  have h1' : 0 ≤ 1 - θ := by linarith
  calc _ ≤ θ * df2Quad k b Pu x + (1 - θ) * df2Quad k b Pu y := df2Quad_comb_le k b hP x y h0 h1
    _ ≤ θ * c + (1 - θ) * c := by gcongr
    _ = c := by ring

theorem dfi_dist {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ} {Φ : (Fin d → ℝ) → ℝ} (hΦ : ∃ k b, Φ = df2Quad k b P)
    {x y : Fin d → ℝ} {c c' e : ℝ} (hx : Φ x ≤ c) (hy : Φ y ≤ c') (hm : -e ≤ Φ ((1 / 2 : ℝ) • (x + y))) :
    df2Sq P (x - y) ≤ 4 * (c + c' + 2 * e) := by
  obtain ⟨k, b, rfl⟩ := hΦ
  exact (lemmaDFI_holds _ k b P x y).2 c c' e hx hy hm

/-- The core of Proposition D.8, for a general sequence of functions `Φ t` with Lemma D.7 and the lower bound of the
event of Lemma DQ as hypotheses. -/
theorem inc2_core {d : ℕ} (Keps BR : Set (Fin d → ℝ)) (μ : ℕ → Fin d → ℝ) (P : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (Φ : ℕ → (Fin d → ℝ) → ℝ) (τ : ℕ) (c dev' r : ℝ)
    (hKc : Convex ℝ Keps) (hKB : Keps ⊆ BR)
    (hPD : ∀ s, 1 ≤ s → s ≤ τ → (P s).PosDef)
    (hquad : ∀ t, t + 1 ≤ τ → ∃ k b, Φ t = df2Quad k b (P (t + 1)))
    (hnew : ∀ t, 1 ≤ t → t ≤ τ → Φ t (μ t) = Φ (t - 1) (μ t))
    (hμ1 : μ 1 ∈ Keps) (hΦμ1 : Φ 0 (μ 1) = 0)
    (hproj : ∀ u, 2 ≤ u → u ≤ τ → (df2R Keps Φ c u).Nonempty → μ u ∈ df2R Keps Φ c u)
    (hmon : ∀ u t, u ≤ t → t ≤ τ → ∀ y ∈ df2S μ P r t ∩ BR, Φ u y ≤ Φ t y + 2 * dev')
    (hlow : ∀ t ≤ τ, ∀ y ∈ df2S μ P r t ∩ BR, -dev' ≤ Φ t y)
    (hc : 0 ≤ c) (hdev : 0 ≤ dev') (hrow : 8 * (c + 2 * dev') < r) :
    ∀ u, 1 ≤ u → u ≤ τ → μ u ∈ df2R Keps Φ c u ∧
      ∀ y ∈ df2R Keps Φ c u, ∀ s, 1 ≤ s → s ≤ u → df2Sq (P s) (y - μ s) ≤ 8 * (c + 2 * dev') := by
  have hq : ∀ s, 1 ≤ s → s ≤ τ → ∃ k b, Φ (s - 1) = df2Quad k b (P s) := by
    intro s h1 h2
    have := hquad (s - 1) (by omega)
    rwa [Nat.sub_add_cancel h1] at this
  have hRc : ∀ u, 1 ≤ u → u ≤ τ → ∀ x ∈ df2R Keps Φ c u, ∀ y ∈ df2R Keps Φ c u, ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      θ • x + (1 - θ) • y ∈ df2R Keps Φ c u :=
    fun u h1 h2 x hx y hy θ h0 h1' => df2R_comb hKc (hPD u h1 h2) (hq u h1 h2) hx hy h0 h1'
  have hSc : ∀ t ≤ τ, ∀ x ∈ df2S μ P r t, ∀ y ∈ df2S μ P r t, (1 / 2 : ℝ) • (x + y) ∈ df2S μ P r t := by
    intro t ht x hx y hy
    rw [mid_eq]
    exact df2S_comb (fun s h1 h2 => hPD s h1 (le_trans h2 ht)) hx hy (by norm_num) (by norm_num)
  have hKm : ∀ x ∈ Keps, ∀ y ∈ Keps, (1 / 2 : ℝ) • (x + y) ∈ Keps := by
    intro x hx y hy
    rw [mid_eq]
    exact hKc hx hy (by norm_num) (by norm_num) (by norm_num)
  have hS0 : ∀ y, y ∈ df2S μ P r 0 := fun y s h1 h2 => absurd (le_trans h1 h2) (by norm_num)
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  intro hu1 huτ
  rcases Nat.lt_or_ge u 2 with hu2 | hu2
  · obtain rfl : u = 1 := by omega
    have ha : μ 1 ∈ df2R Keps Φ c 1 := ⟨hμ1, show Φ 0 (μ 1) ≤ c by rw [hΦμ1]; exact hc⟩
    refine ⟨ha, ?_⟩
    intro y hy s hs1 hs1'
    obtain rfl : s = 1 := by omega
    have hy2 : Φ 0 y ≤ c := hy.2
    have hm := hlow 0 (by omega) _ ⟨hS0 _, hKB (hKm y hy.1 (μ 1) hμ1)⟩
    have := dfi_dist (hq 1 le_rfl huτ) hy2 (le_of_eq hΦμ1) hm
    linarith
  · have ihs : ∀ s, 1 ≤ s → s < u → μ s ∈ df2R Keps Φ c s ∧
        ∀ y ∈ df2R Keps Φ c s, ∀ j, 1 ≤ j → j ≤ s → df2Sq (P j) (y - μ j) ≤ 8 * (c + 2 * dev') :=
      fun s h1 h2 => ih s h2 h1 (by omega)
    have hμS : ∀ s, 1 ≤ s → s < u → μ s ∈ df2S μ P r s := fun s h1 h2 j hj1 hjs =>
      ((ihs s h1 h2).2 (μ s) (ihs s h1 h2).1 j hj1 hjs).trans hrow.le
    have hprev := ihs (u - 1) (by omega) (by omega)
    have hx0R : μ (u - 1) ∈ df2R Keps Φ c u := by
      refine ⟨hprev.1.1, ?_⟩
      have h1 := hnew (u - 1) (by omega) (by omega)
      have h2 : Φ (u - 1 - 1) (μ (u - 1)) ≤ c := hprev.1.2
      show Φ (u - 1) (μ (u - 1)) ≤ c
      rw [h1]; exact h2
    have hau : μ u ∈ df2R Keps Φ c u := hproj u hu2 huτ ⟨_, hx0R⟩
    -- (b_u) for `s ≤ u - 1`, by the segment from `μ (u - 1)`
    have hbprev : ∀ y ∈ df2R Keps Φ c u, ∀ s, 1 ≤ s → s ≤ u - 1 →
        df2Sq (P s) (y - μ s) ≤ 8 * (c + 2 * dev') := by
      intro y hy
      have key := segment_clopen (Finset.Icc 1 (u - 1))
        (fun s θ => df2Sq (P s) (θ • y + (1 - θ) • μ (u - 1) - μ s)) (8 * (c + 2 * dev')) r
        (fun s _ => df2Sq_continuous _ _ _ _) hrow ?_ ?_
      · intro s hs1 hs2
        have := key 1 ⟨zero_le_one, le_rfl⟩ s (Finset.mem_Icc.2 ⟨hs1, hs2⟩)
        simpa using this
      · intro s hs
        obtain ⟨hs1, hs2⟩ := Finset.mem_Icc.1 hs
        have := hprev.2 (μ (u - 1)) hprev.1 s hs1 hs2
        simpa using this
      · intro θ hθ hall s hs
        obtain ⟨hs1, hs2⟩ := Finset.mem_Icc.1 hs
        set x := θ • y + (1 - θ) • μ (u - 1) with hxdef
        have hxR : x ∈ df2R Keps Φ c u := hRc u hu1 huτ y hy _ hx0R θ hθ.1 hθ.2
        have hxS : x ∈ df2S μ P r (u - 1) := fun j hj1 hj2 => hall j (Finset.mem_Icc.2 ⟨hj1, hj2⟩)
        have hx2 : Φ (u - 1) x ≤ c := hxR.2
        have hmonx := hmon (s - 1) (u - 1) (by omega) (by omega) x ⟨hxS, hKB hxR.1⟩
        have has : Φ (s - 1) (μ s) ≤ c := (ihs s hs1 (by omega)).1.2
        have hmS : (1 / 2 : ℝ) • (x + μ s) ∈ df2S μ P r (s - 1) :=
          hSc (s - 1) (by omega) x (df2S_anti (by omega) hxS) (μ s) (df2S_anti (by omega) (hμS s hs1 (by omega)))
        have hmK : (1 / 2 : ℝ) • (x + μ s) ∈ Keps := hKm x hxR.1 (μ s) (ihs s hs1 (by omega)).1.1
        have hm := hlow (s - 1) (by omega) _ ⟨hmS, hKB hmK⟩
        have hsx : Φ (s - 1) x ≤ c + 2 * dev' := by linarith
        have := dfi_dist (hq s hs1 (by omega)) hsx has hm
        show df2Sq (P s) (x - μ s) ≤ 8 * (c + 2 * dev')
        linarith
    refine ⟨hau, ?_⟩
    intro y hy s hs1 hsu
    rcases Nat.lt_or_ge s u with hsu' | hsu'
    · exact hbprev y hy s hs1 (by omega)
    · obtain rfl : s = u := le_antisymm hsu hsu'
      have hmR : (1 / 2 : ℝ) • (y + μ s) ∈ df2R Keps Φ c s := by
        rw [mid_eq]; exact hRc s hu1 huτ y hy _ hau _ (by norm_num) (by norm_num)
      have hmS : (1 / 2 : ℝ) • (y + μ s) ∈ df2S μ P r (s - 1) :=
        fun j hj1 hj2 => (hbprev _ hmR j hj1 hj2).trans hrow.le
      have hm := hlow (s - 1) (by omega) _ ⟨hmS, hKB hmR.1⟩
      have := dfi_dist (hq s hs1 huτ) hy.2 hau.2 hm
      linarith

end AdversarialBco.Poly.Df2Det

namespace AdversarialBco.Poly

open Df2Det

/-- Proposition D.8. -/
theorem propINC2_holds : PropINC2 := by
  intro d Keps BR μ P Φ0 Ω Ωh τ c1 ρ dev' pri r hKc _hKcl hKB hPD hquad hnew hΦ0 _hKpri hμ1 hΦμ1 hproj hΩ0 hΩmon
    hdev hdev0 hρ hc1 _hpri hrow
  have hmon := lemmaMON_holds d Φ0 Ω Ωh (df2S μ P r) BR τ dev' (fun u t hut => df2S_anti hut) hΩmon hdev
  refine inc2_core Keps BR μ P (fun t y => Φ0 y + Ωh t y) τ (c1 * ρ) dev' r hKc hKB hPD hquad hnew hμ1 hΦμ1
    hproj hmon ?_ (by nlinarith) hdev0 hrow
  intro t ht y hy
  have h1 := (abs_le.mp (hdev t ht y hy)).1
  have h2 := hΩ0 t y
  have h3 := hΦ0 y
  show -dev' ≤ Φ0 y + Ωh t y
  linarith

end AdversarialBco.Poly

namespace AdversarialBco.Poly

/-- Lemma D.10 (Lemma D.10 of the paper). -/
theorem lemmaD2_holds : LemmaD2 := by
  intro α Q sReg T Th W Ξ κ a cup r η ν dev ρ'' π0 h e m hκa hacup hr hη hh he hi hii hiii hiv hv hup hlub
  have hak : 0 < a - κ := sub_pos.mpr hκa
  have hca : 0 < cup - a := sub_pos.mpr hacup
  have hrpos : 0 < r := by
    by_contra hneg
    push Not at hneg
    have : r * (a - κ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hak.le
    linarith
  refine ⟨?_, ?_⟩
  · intro hm y hy
    have h1 := hi y hy
    have h4 := (abs_le.mp (hiv y hy))
    have h5 := (hv y hy).1
    have h6 := hup y hy
    have : η * sReg y ≤ η * T y + η * ν := by nlinarith
    have : η * T y ≤ η * Th y + η * dev := by nlinarith [h4.1]
    linarith
  · intro hc
    apply hlub
    intro y hy
    have hcy := hc y hy
    have h2 := hii y hy
    have h3 := hiii y hy
    have h4 := (abs_le.mp (hiv y hy))
    have h5 := (hv y hy).2
    have hT : η * T y ≤ -h - η * dev := by
      by_cases hw : (cup - a) / 2 * η * W y ≤ r * (ρ'' + h + η * dev)
      · have : η * T y ≤ η * sReg y + (cup - a) / 2 * η * W y + η * ν := by nlinarith
        nlinarith
      · push Not at hw
        have hw' : r * (ρ'' + h + η * dev) < r * ((a - κ) / 2 * η * W y) := by
          have : (cup - a) / 2 * η * W y = r * ((a - κ) / 2 * η * W y) := by rw [← hr]; ring
          linarith
        have := lt_of_mul_lt_mul_left hw' hrpos.le
        linarith
    have : η * Th y ≤ η * T y + η * dev := by nlinarith [h4.2]
    linarith

/-- The two carriers. -/
theorem df2Carriers_holds : Df2Carriers := by
  intro d P Q v K
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [real_inner_comm, inner_toEuclideanCLM]
    rfl
  · rfl
  · exact map_mul Matrix.toEuclideanCLM P Q
  · have h1 : Pᵀ = star P := by
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [h1, map_star, ContinuousLinearMap.star_eq_adjoint]
  · rw [EuclideanSpace.norm_sq_eq]
    simp [dotProduct, sq]
  · constructor
    · intro hK
      have := hK.linear_preimage (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap
      convert this using 1
      ext x; simp
    · intro hK
      exact hK.linear_preimage (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm.toLinearMap
  · constructor
    · intro hK
      have := hK.preimage (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ))
      convert this using 1
      ext x; simp
    · intro hK
      exact hK.preimage (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))

end AdversarialBco.Poly

namespace AdversarialBco.Poly

/-- Outside the regime. -/
theorem df2Trivial_holds : Df2Trivial := by
  intro d n Ceps L hd hn hCeps hL hlt
  have hd_nonneg : 0 ≤ d := by linarith
  have hn_nonneg : 0 ≤ n := by linarith
  have hL_nonneg : 0 ≤ L := by linarith
  have hCeps_nonneg : 0 ≤ Ceps := by linarith
  set M := 2 * Ceps * d ^ ((3 : ℝ) / 2) * L ^ 5 with hM_def
  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  have hd_pow : (d ^ ((3 : ℝ) / 2)) ^ 2 = d ^ 3 := by
    calc
      (d ^ ((3 : ℝ) / 2)) ^ 2 = (d ^ ((3 : ℝ) / 2)) ^ (2 : ℝ) := by norm_num
      _ = d ^ (((3 : ℝ) / 2) * (2 : ℝ)) := by rw [Real.rpow_mul hd_nonneg ((3 : ℝ) / 2) (2 : ℝ)]
      _ = d ^ (3 : ℝ) := by norm_num
      _ = d ^ 3 := by norm_num
  have hL_pow : (L ^ 5) ^ 2 = L ^ 10 := by
    calc
      (L ^ 5) ^ 2 = (L ^ 5) ^ (2 : ℝ) := by norm_num
      _ = (L ^ (5 : ℝ)) ^ (2 : ℝ) := by norm_num
      _ = L ^ ((5 : ℝ) * (2 : ℝ)) := by rw [Real.rpow_mul hL_nonneg (5 : ℝ) (2 : ℝ)]
      _ = L ^ (10 : ℝ) := by norm_num
      _ = L ^ 10 := by norm_num
  have hMsq : M ^ 2 = 4 * Ceps ^ 2 * d ^ 3 * L ^ 10 := by
    dsimp [M]
    calc
      (2 * Ceps * d ^ ((3 : ℝ) / 2) * L ^ 5) ^ 2
          = (2 * Ceps) ^ 2 * (d ^ ((3 : ℝ) / 2)) ^ 2 * (L ^ 5) ^ 2 := by ring
      _ = 4 * Ceps ^ 2 * (d ^ ((3 : ℝ) / 2)) ^ 2 * (L ^ 5) ^ 2 := by ring
      _ = 4 * Ceps ^ 2 * d ^ 3 * (L ^ 5) ^ 2 := by rw [hd_pow]
      _ = 4 * Ceps ^ 2 * d ^ 3 * L ^ 10 := by rw [hL_pow]
  have hlt' : n < M ^ 2 := by
    rw [hMsq]
    exact hlt
  have hsqrt : Real.sqrt n < M := by
    calc
      Real.sqrt n < Real.sqrt (M ^ 2) := Real.sqrt_lt_sqrt hn_nonneg hlt'
      _ = M := Real.sqrt_sq hMpos.le
  calc
    n = Real.sqrt n * Real.sqrt n := by
      rw [Real.mul_self_sqrt hn_nonneg]
    _ ≤ M * Real.sqrt n := by
      nlinarith [Real.sqrt_nonneg n, hsqrt]
    _ = 2 * Ceps * d ^ ((3 : ℝ) / 2) * L ^ 5 * Real.sqrt n := rfl

end AdversarialBco.Poly

namespace AdversarialBco.Poly

open Df2Det

/-- Lemma D.13, the deterministic core. -/
theorem lemmaONS2Core_holds : LemmaONS2Core := by
  intro d P S H μ g ep η t y ht hP hPD hproj
  have key := telescope_ons t ht (fun s => η * (g s ⬝ᵥ (μ s - y) - (1 / 2) * df2Sq (H s) (y - μ s)))
    (fun s => df2Sq (P s) (μ s - y)) (fun s => df2Sq (P (s + 1)) (μ s - η • (S (s + 1) *ᵥ g s) - y))
    (fun s => η ^ 2 / 2 * df2Sq (S (s + 1)) (g s)) ep ?_ (fun s h1 h2 => hproj s h1 h2)
    (df2Sq_nonneg (hPD t ht le_rfl).1 _)
  · rw [Finset.mul_sum, Finset.mul_sum]
    exact key
  · intro s h1 h2
    obtain ⟨hpd, hSP⟩ := hPD s h1 h2
    have hPs := hP s h1 h2
    rw [hPs] at hpd hSP
    have hsym : (P s + η • H s)ᵀ = P s + η • H s := by
      have := hpd.1
      rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
    show _ = (1 / 2) * df2Sq (P s) (μ s - y) - (1 / 2) * df2Sq (P (s + 1)) (μ s - η • (S (s + 1) *ᵥ g s) - y) +
      η ^ 2 / 2 * df2Sq (S (s + 1)) (g s)
    rw [hPs]
    exact ons2_step (P s) (H s) (S (s + 1)) (μ s) (g s) y η hsym hSP

/-- Lemma D.18, the step that closes it. -/
theorem lemmaZCore_holds : LemmaZCore := by
  intro d Sg b G η R δ hδpos hSg hb hGη hη
  have hη2 : 0 ≤ η / 2 := by linarith
  calc
    ‖Sg (b - (η / 2) • G)‖ ≤ ‖b - (η / 2) • G‖ / δ := hSg (b - (η / 2) • G)
    _ ≤ (‖b‖ + ‖(η / 2) • G‖) / δ := by
      gcongr
      exact norm_sub_le _ _
    _ = (‖b‖ + (η / 2) * ‖G‖) / δ := by
      rw [norm_smul, Real.norm_of_nonneg hη2]
    _ ≤ (R / (4 * δ ^ 2) + (η / 2) * ‖G‖) / δ := by
      gcongr
    _ ≤ (R / (4 * δ ^ 2) + (3 / 4 * R / δ ^ 2)) / δ := by
      gcongr
    _ = (R / δ ^ 2) / δ := by ring
    _ = R / δ ^ 3 := by ring

/-- The row of Lemma D.18 at `df2C0 = 36`. -/
theorem df2RowZ_holds : Df2RowZ := by
  intro d n x κ0 hd hn hx hκ0 hκ0le4
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos_dn : 1 ≤ (d : ℝ) * (n : ℝ) := by
    nlinarith
  have hpos_dnx : 0 < (d : ℝ) * (n : ℝ) := by
    nlinarith
  have hu : (1 : ℝ) ≤ (d : ℝ) * (n : ℝ) := hpos_dn
  have hxpos : 0 < x := by
    have hlog_nonneg : 0 ≤ Real.log ((d : ℝ) * (n : ℝ)) :=
      Real.log_nonneg hpos_dn
    nlinarith
  have hx_nonneg : 0 ≤ x := by linarith
  have hlog : 14 + 3 * Real.log ((d : ℝ) * (n : ℝ)) ≤ x := by
    simpa [Nat.cast_mul] using hx
  have hW : Real.exp (-x) * ((d : ℝ) * (n : ℝ)) * x ≤ 1/16 :=
    rowz_core ((d : ℝ) * (n : ℝ)) x hu hlog
  have hsqrtκ0 : Real.sqrt κ0 ≤ 2 := by
    calc
      Real.sqrt κ0 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt hκ0le4
      _ = 2 := by norm_num
  have hsqrt329 : Real.sqrt (32/9 : ℝ) ≤ 2 := by
    have h : (32/9 : ℝ) ≤ 4 := by norm_num
    calc
      Real.sqrt (32/9 : ℝ) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt h
      _ = 2 := by norm_num
  set E := Real.exp (-x) with hE
  set N := (n : ℝ) with hN
  set D := (d : ℝ) with hD
  have hEpos : 0 < E := Real.exp_pos (-x)
  have hNpos : 0 < N := by
    have h : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hD_nonneg : 0 ≤ D := by
    have h : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
    exact h
  have hENx_pos : 0 < E * N * x := by
    positivity
  have hENx_nonneg : 0 ≤ E * N * x := by linarith
  -- (E * N * x)^{3/2} = (E * N * x) * sqrt(E * N * x)
  have h_pow3half : (E * N * x) ^ ((3 : ℝ) / 2) = (E * N * x) * Real.sqrt (E * N * x) := by
    calc
      (E * N * x) ^ ((3 : ℝ) / 2) = (E * N * x) ^ ((1 : ℝ) + (1/2 : ℝ)) := by norm_num
      _ = (E * N * x) ^ (1 : ℝ) * (E * N * x) ^ ((1/2 : ℝ)) := by
        rw [Real.rpow_add hENx_pos (1 : ℝ) ((1/2 : ℝ))]
      _ = (E * N * x) * (E * N * x) ^ ((1/2 : ℝ)) := by simp
      _ = (E * N * x) * Real.sqrt (E * N * x) := by rw [Real.sqrt_eq_rpow]
  -- sqrt(D) ≤ D since D ≥ 1
  have hsqrtD_le_D : Real.sqrt D ≤ D := by
    have hDge1 : 1 ≤ D := hd'
    calc
      Real.sqrt D ≤ Real.sqrt (D ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = D := by
        rw [Real.sqrt_sq hD_nonneg]
  -- sqrt(E*N*x) * sqrt(D) = sqrt(E*N*x*D) ≤ sqrt(1/16) = 1/4
  have h_sqrt_prod : Real.sqrt (E * N * x) * Real.sqrt D ≤ 1/4 := by
    have h_mul : Real.sqrt (E * N * x) * Real.sqrt D = Real.sqrt ((E * N * x) * D) := by
      rw [← Real.sqrt_mul hENx_nonneg]
    rw [h_mul]
    have h_bound : (E * N * x) * D ≤ 1/16 := by
      calc
        (E * N * x) * D = E * N * x * D := rfl
        _ = E * (D * N) * x := by ring
        _ = Real.exp (-x) * ((d : ℝ) * (n : ℝ)) * x := by
          simp [hE, hN, hD, mul_comm, mul_assoc]
        _ ≤ 1/16 := hW
    calc
      Real.sqrt ((E * N * x) * D) ≤ Real.sqrt (1/16) := Real.sqrt_le_sqrt h_bound
      _ = 1/4 := by norm_num
  -- (E * N * x)^{3/2} = E^{3/2} * N^{3/2} * x^{3/2}
  have h_mul_pow : (E * N * x) ^ ((3 : ℝ) / 2) = E ^ ((3 : ℝ) / 2) * N ^ ((3 : ℝ) / 2) * x ^ ((3 : ℝ) / 2) := by
    calc
      (E * N * x) ^ ((3 : ℝ) / 2) = ((E * N) * x) ^ ((3 : ℝ) / 2) := by ring
      _ = (E * N) ^ ((3 : ℝ) / 2) * x ^ ((3 : ℝ) / 2) := by rw [Real.mul_rpow (by positivity) (by positivity)]
      _ = (E ^ ((3 : ℝ) / 2) * N ^ ((3 : ℝ) / 2)) * x ^ ((3 : ℝ) / 2) := by rw [Real.mul_rpow (by positivity) (by positivity)]
      _ = E ^ ((3 : ℝ) / 2) * N ^ ((3 : ℝ) / 2) * x ^ ((3 : ℝ) / 2) := by ring
  -- E * N * x ≤ 1/16
  have hENx_bound : E * N * x ≤ 1/16 := by
    calc
      E * N * x ≤ E * (D * N) * x := by
        nlinarith
      _ = Real.exp (-x) * ((d : ℝ) * (n : ℝ)) * x := by
        simp [hE, hN, hD, mul_comm, mul_assoc]
      _ ≤ 1/16 := hW
  -- Now the main inequality
  have h_main : 1 / 4 * Real.sqrt κ0 * df2C0 * Real.sqrt (32 / 9) * Real.exp (-x) ^ ((3 : ℝ) / 2) * (n : ℝ) ^ ((3 : ℝ) / 2) *
      Real.sqrt d * x ^ ((3 : ℝ) / 2) ≤ 3 / 4 := by
    -- Rewrite using E, N, D
    have h_expr : 1 / 4 * Real.sqrt κ0 * df2C0 * Real.sqrt (32 / 9) * Real.exp (-x) ^ ((3 : ℝ) / 2) * (n : ℝ) ^ ((3 : ℝ) / 2) *
        Real.sqrt d * x ^ ((3 : ℝ) / 2) =
        1 / 4 * Real.sqrt κ0 * df2C0 * Real.sqrt (32 / 9) * (E ^ ((3 : ℝ) / 2) * N ^ ((3 : ℝ) / 2) * x ^ ((3 : ℝ) / 2)) * Real.sqrt D := by
      simp [hE, hN, hD, mul_comm, mul_left_comm, mul_assoc]
    rw [h_expr]
    -- Replace E^{3/2} * N^{3/2} * x^{3/2} with (E*N*x)^{3/2} = (E*N*x) * sqrt(E*N*x)
    rw [← h_mul_pow, h_pow3half]
    -- Now the expression is: 1/4 * √κ0 * df2C0 * √(32/9) * ((E*N*x) * √(E*N*x)) * √D
    have h_df2C0 : df2C0 = 36 := rfl
    rw [h_df2C0]
    have h_nonneg_sqrtκ0 : 0 ≤ Real.sqrt κ0 := Real.sqrt_nonneg _
    have h_nonneg_sqrt329 : 0 ≤ Real.sqrt (32/9 : ℝ) := Real.sqrt_nonneg _
    have h_nonneg_sqrtENx : 0 ≤ Real.sqrt (E * N * x) := Real.sqrt_nonneg _
    have h_nonneg_sqrtD : 0 ≤ Real.sqrt D := Real.sqrt_nonneg _
    have h_nonneg_ENx : 0 ≤ E * N * x := hENx_nonneg
    -- Bound each factor and combine
    have h_prod1 : Real.sqrt κ0 * Real.sqrt (32/9) ≤ 2 * 2 :=
      mul_le_mul hsqrtκ0 hsqrt329 h_nonneg_sqrt329 (by norm_num)
    have h_prod2 : (E * N * x) ≤ 1/16 := hENx_bound
    have h_prod3 : Real.sqrt (E * N * x) * Real.sqrt D ≤ 1/4 := h_sqrt_prod
    have h_inner : Real.sqrt κ0 * Real.sqrt (32/9) * (E * N * x) * (Real.sqrt (E * N * x) * Real.sqrt D) ≤
        2 * 2 * (1/16) * (1/4) := by
      have h12 : Real.sqrt κ0 * Real.sqrt (32/9) * (E * N * x) ≤ 2 * 2 * (1/16) :=
        mul_le_mul h_prod1 h_prod2 h_nonneg_ENx (by norm_num)
      have hpos_inner : 0 ≤ Real.sqrt κ0 * Real.sqrt (32/9) * (E * N * x) := by
        positivity
      have hpos_16 : 0 ≤ (2 : ℝ) * 2 * (1/16 : ℝ) := by norm_num
      have hpos_prod3 : 0 ≤ Real.sqrt (E * N * x) * Real.sqrt D := by
        positivity
      exact mul_le_mul h12 h_prod3 hpos_prod3 hpos_16
    calc
      1 / 4 * Real.sqrt κ0 * 36 * Real.sqrt (32 / 9) * ((E * N * x) * Real.sqrt (E * N * x)) * Real.sqrt D
          = ((1/4 : ℝ) * (36 : ℝ)) * (Real.sqrt κ0 * Real.sqrt (32/9) * (E * N * x) * (Real.sqrt (E * N * x) * Real.sqrt D)) := by ring
      _ ≤ ((1/4 : ℝ) * (36 : ℝ)) * ((2 : ℝ) * (2 : ℝ) * (1/16 : ℝ) * (1/4 : ℝ)) := by
        have hpos_9 : 0 ≤ (1/4 : ℝ) * (36 : ℝ) := by norm_num
        exact mul_le_mul_of_nonneg_left h_inner hpos_9
      _ = (9/16 : ℝ) := by norm_num
      _ ≤ 3/4 := by norm_num
  exact h_main

end AdversarialBco.Poly
