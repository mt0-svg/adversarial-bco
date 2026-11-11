/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2DetW1

@[expose] public section

/-!
# DET, Lemma D.14 at `τ` and the epoch

Lemma DF2-W: Lemma D.14 with `K_eps` the
body, `K_τ = R⁻_τ` (the test region of round `τ`), `K_{τ+1} = R⁻_τ ∩ R⁻_{τ+1}`, `Ereg = eReg_τ(x)` for each
`x ∈ K_ε`, `σ_u = s_u(μ_u)`, `β = Ω_{τ+1}/η` and `Fire` the firing of the test at `τ`; (W1) from `Df2DetW1.lean`,
(W2) from the sandwich and the online Newton inequality, (W3) from Lemma DQ and the continuity of `Φ`, (W4s) and (W4c)
from Lemma D.10 on `R⁻_τ` with `h = θ ρ`, `e = α ρ`, (W5) from the range of the surrogate on `K_ε`. The rows R22, R24o
give the two conditions of Lemma D.14 and R19o the level `ρ/η`. Then `epoch_ok`: the epoch either fires at `τ` with
`eReg_τ ≤ 0` on `K_ε`, or runs to the horizon with `eReg_{m-1} ≤ ρ/η`.
-/

open Matrix
open scoped Matrix

namespace AdversarialBco.Poly

open Layer2

theorem convexOn_toLp {d : ℕ} {f : E d → ℝ} (hf : ConvexOn ℝ Set.univ f) {K : Set (Fin d → ℝ)}
    (hK : Convex ℝ K) : ConvexOn ℝ K (fun x => f (WithLp.toLp 2 x)) := by
  refine ⟨hK, fun x _ y _ a b ha hb hab => ?_⟩
  have := hf.2 (Set.mem_univ (WithLp.toLp 2 x)) (Set.mem_univ (WithLp.toLp 2 y)) ha hb hab
  simpa [WithLp.toLp_add, WithLp.toLp_smul] using this

theorem continuous_toLp' {d : ℕ} {f : E d → ℝ} (hf : Continuous f) : Continuous (fun x => f (WithLp.toLp 2 x)) :=
  hf.comp (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))

namespace Df2Ctx

variable {d : ℕ} (c : Df2Ctx d) (π : Df2Path d)

/-- `ρ'' = pri + stab + 1 + η dev_κ`. -/
noncomputable def rhoPP : ℝ := df2Pri c.p + df2Stab c.p d c.n + 1 + c.p.eta * df2DevK c.p d c.n

noncomputable def wA1 : ℝ := 1 + d * c.p.Le / (c.p.lam * c.p.eta)
noncomputable def wA2 : ℝ := (c.p.eta + c.rhoPP) / c.p.eta
noncomputable def wA5 : ℝ := 1 + 10 / (c.p.lam * c.p.eps)
noncomputable def wKs : ℝ :=
  ((c.p.theta - c.p.alpha) * c.p.rho - 2 * df2Pri c.p - c.p.eta * df2Dev c.p d c.n - c.p.eta) / c.p.eta
noncomputable def wKc : ℝ :=
  (7 * (c.p.theta * c.p.rho) + 6 * c.rhoPP + 7 * (c.p.eta * df2Dev c.p d c.n) + c.p.eta) / c.p.eta
noncomputable def wB : ℝ := ((c.p.c1 - c.p.gam) * c.p.rho - df2Pri c.p - df2DevP c.p d c.n) / c.p.eta

/-- `β = Ω_{τ+1}/η`. -/
noncomputable def wBeta (τ : ℕ) (y : Fin d → ℝ) : ℝ := c.OmT π (τ + 1) y / c.p.eta

/-- The losses of Lemma D.14, indexed from 1. -/
noncomputable def sW (u : ℕ) (x : Fin d → ℝ) : ℝ := c.surr π (u - 1) (WithLp.toLp 2 x)

noncomputable def sigW (u : ℕ) : ℝ := c.surr π (u - 1) (WithLp.toLp 2 (c.st π (u - 1)).mu)

theorem wrapS_eq (t : ℕ) (x : Fin d → ℝ) :
    wrapS (c.sW π) t x = ∑ u ∈ Finset.range t, c.surr π u (WithLp.toLp 2 x) := by
  unfold wrapS
  rw [sum_Icc_one (fun i => c.sW π i x)]
  simp only [sW, Nat.add_sub_cancel]

theorem wrapS_succ (t : ℕ) (x : Fin d → ℝ) : wrapS (c.sW π) (t + 1) x = c.SumS π t x := by
  rw [wrapS_eq]; rfl

theorem wrapReg_eq (t : ℕ) (y : Fin d → ℝ) : wrapReg (c.sW π) (c.sigW π) (t + 1) y = c.sReg π (t + 1) y := by
  unfold wrapReg
  rw [wrapS_eq, sum_Icc_one (c.sigW π)]
  unfold sReg
  rw [Finset.sum_sub_distrib]
  simp only [sigW, Nat.add_sub_cancel]

theorem sReg_eq (t : ℕ) (y : Fin d → ℝ) :
    c.sReg π (t + 1) y = ∑ u ∈ Finset.range (t + 1), c.surr π u (WithLp.toLp 2 (c.st π u).mu) - c.SumS π t y := by
  unfold sReg SumS; rw [Finset.sum_sub_distrib]

end Df2Ctx

namespace DetHyp

variable {d : ℕ} {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

/-- `Ξ(y) = Ξ(z) - 2 ℓ(y)`, `ℓ = |· - z|²_{P'}/2`. -/
theorem xi_sub (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) (y : Fin d → ℝ) :
    c.Xi π s y = c.Xi π s (c.zz π s) - 2 * ellF (c.Pn π s) (c.zz π s) y := by
  obtain ⟨hpd, hSP, -, -⟩ := H.r1_le_tau hs
  exact xi_identity (c.Pn π s) (c.Sn π s) hpd.isHermitian (mul_eq_one_comm.1 hSP) (c.bn π s) (c.Gn π s) y
    (c.kn π s) (c.ln π s) c.p.eta

/-- An accurate test point has `Ξ` within `α ρ` of its maximum over `R⁻_s`. -/
theorem xi_acc (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) {pt : Fin d → ℝ}
    (hpt : ∀ x ∈ c.Rm π s, ellF (c.Pn π s) (c.zz π s) pt ≤ ellF (c.Pn π s) (c.zz π s) x + c.eT) :
    ∀ y ∈ c.Rm π s, c.Xi π s y ≤ c.Xi π s pt + c.p.alpha * c.p.rho := by
  intro y hy
  rw [H.xi_sub hs y, H.xi_sub hs pt]
  have := hpt y hy
  have : c.eT ≤ c.p.alpha * c.p.rho / 2 := min_le_right _ _
  linarith

theorem nu_le (H : DetHyp c δ π m) : c.n * c.p.δe / c.p.lam ^ 2 ≤ 1 := H.rows.cnu

theorem mem_SS (H : DetHyp c δ π m) {y : Fin d → ℝ} (hy : y ∈ c.Rm π (c.tau π m)) :
    y ∈ c.SS π (c.tau π m) ∧ oNorm y ≤ c.p.R :=
  H.reg_sub le_rfl (H.Rm_sub_reg le_rfl hy)

/-- The online Newton bound at `τ`: `η T_{τ+1}(y) ≤ ρ'' - Ω_{τ+1}(y)` on `R⁻_τ`. -/
theorem eta_T (H : DetHyp c δ π m) {y : Fin d → ℝ} (hy : y ∈ c.Rm π (c.tau π m)) :
    c.p.eta * c.TT π (c.tau π m + 1) y ≤ c.rhoPP - c.OmT π (c.tau π m + 1) y := by
  obtain ⟨hSS, hR⟩ := H.mem_SS hy
  have h3 := H.q_part1 le_rfl hSS hR
  have h4 := H.ons le_rfl (fun u hu => H.projOK hu) hy
  unfold Df2Ctx.rhoPP
  linarith

/-- (W2). -/
theorem w2 (H : DetHyp c δ π m) {y : Fin d → ℝ} (hy : y ∈ c.Rm π (c.tau π m)) :
    wrapReg (c.sW π) (c.sigW π) (c.tau π m + 1) y ≤ c.wA2 - c.wBeta π (c.tau π m) y := by
  obtain ⟨hSS, -⟩ := H.mem_SS hy
  have hη := H.rows.pos_eta
  rw [Df2Ctx.wrapReg_eq]
  have h1 := H.sand_i le_rfl hSS
  have h2 := H.eta_T hy
  have h3 := H.nu_le
  unfold Df2Ctx.wA2 Df2Ctx.wBeta
  rw [← sub_div, le_div_iff₀ hη]
  nlinarith

theorem OmT_le_succ (H : DetHyp c δ π m) {t : ℕ} (ht : t ≤ c.tau π m) (y : Fin d → ℝ) :
    c.OmT π t y ≤ c.OmT π (t + 1) y := by
  rw [Df2Ctx.OmT_succ]
  have := sq_nonneg_of_psd (H.sHess_psd ht) (y - (c.st π t).mu)
  have := H.kap_pos
  have : 0 ≤ c.p.eta * c.p.kap / 2 * df2Sq (c.sHess π t) (y - (c.st π t).mu) := by positivity
  linarith

/-- (W3), first half. -/
theorem w3a (H : DetHyp c δ π m) {y : Fin d → ℝ} (hy : y ∈ c.Rm π (c.tau π m))
    (hcl : y ∈ closure (c.Keps \ c.Rm π (c.tau π m))) : c.wB ≤ c.wBeta π (c.tau π m) y := by
  have hη := H.rows.pos_eta
  obtain ⟨hSS, hR⟩ := H.mem_SS hy
  by_cases h0 : c.tau π m = 0
  · rw [h0, Rm_zero, Set.sdiff_self, closure_empty] at hcl
    exact absurd hcl (Set.notMem_empty y)
  obtain ⟨t, ht⟩ : ∃ t, c.tau π m = t + 1 := ⟨c.tau π m - 1, by omega⟩
  have htτ : t < c.tau π m := by omega
  have e : c.Rm π (c.tau π m) = c.RmN π t := by rw [← H.Rm_succ htτ, ht]
  rw [e] at hcl
  have hcont : Continuous (c.PhiN π t) :=
    (phi_convex _ (H.r1_le_tau htτ.le).1.posSemidef (c.bn π t) (c.kn π t) 0 Set.univ convex_univ
      isClosed_univ).2.1
  have hlev := closure_level c.Keps (c.PhiN π t) _ hcont y hcl
  rw [H.PhiN_eq htτ.le] at hlev
  have hSD : y ∈ c.SD π (t + 1) :=
    SD_anti (t + 1) (c.tau π m + 1) (by omega) ((H.SD_succ _ y).2 hSS)
  have hdq := (abs_le.1 (H.dq_at (t := t + 1) (by omega) hSD hR)).2
  obtain ⟨-, hP0⟩ := H.phi0_le hR
  have hmono : c.OmT π (t + 1) y ≤ c.OmT π (c.tau π m + 1) y := by
    rw [← ht]; exact H.OmT_le_succ le_rfl y
  unfold Df2Ctx.wB Df2Ctx.wBeta
  apply div_le_div_of_nonneg_right _ hη.le
  linarith

/-- (W3), second half. -/
theorem w3b (H : DetHyp c δ π m) {y : Fin d → ℝ} (hy : y ∈ c.Rm π (c.tau π m))
    (hb : c.wBeta π (c.tau π m) y < c.wB) : y ∈ c.Rm π (c.tau π m) ∩ c.RmN π (c.tau π m) := by
  have hη := H.rows.pos_eta
  obtain ⟨hSS, hR⟩ := H.mem_SS hy
  refine ⟨hy, (H.Rm_sub_reg le_rfl hy).1, ?_⟩
  unfold Df2Ctx.wB Df2Ctx.wBeta at hb
  rw [div_lt_div_iff_of_pos_right hη] at hb
  rw [H.PhiN_eq le_rfl]
  have hdq := (abs_le.1 (H.dq_at (t := c.tau π m + 1) le_rfl ((H.SD_succ _ y).2 hSS) hR)).2
  obtain ⟨-, hP0⟩ := H.phi0_le hR
  linarith

/-- Lemma D.10 on `R⁻_τ` at the accurate test point `pt` of round `τ`. -/
theorem d2_inst (H : DetHyp c δ π m) {pt : Fin d → ℝ} (hpt : pt ∈ c.Rm π (c.tau π m))
    (hacc : ∀ x ∈ c.Rm π (c.tau π m), ellF (c.Pn π (c.tau π m)) (c.zz π (c.tau π m)) pt ≤
      ellF (c.Pn π (c.tau π m)) (c.zz π (c.tau π m)) x + c.eT) :
    (c.Xi π (c.tau π m) pt ≤ -(c.p.theta * c.p.rho) → ∀ y ∈ c.Rm π (c.tau π m),
      c.p.eta * c.sReg π (c.tau π m + 1) y ≤ -(c.p.theta * c.p.rho - c.p.alpha * c.p.rho) + 2 * df2Pri c.p +
        c.p.eta * df2Dev c.p d c.n + c.p.eta * (c.n * c.p.δe / c.p.lam ^ 2)) ∧
    ((∀ y ∈ c.Rm π (c.tau π m), c.p.eta * c.sReg π (c.tau π m + 1) y ≤
      -((1 + 6) * (c.p.theta * c.p.rho) + 6 * c.rhoPP + (1 + 6) * c.p.eta * df2Dev c.p d c.n +
        c.p.eta * (c.n * c.p.δe / c.p.lam ^ 2))) → c.Xi π (c.tau π m) pt ≤ -(c.p.theta * c.p.rho)) := by
  have hη := H.rows.pos_eta
  have hρ := H.rows.pos_rho
  have hθ := H.theta
  have hα := H.alpha
  have hW := H.OmT_eq (c.tau π m + 1)
  exact H.d2 (Fin d → ℝ) (c.Rm π (c.tau π m)) (c.sReg π (c.tau π m + 1)) (c.TT π (c.tau π m + 1))
    (c.ThT π (c.tau π m + 1)) (c.Wt π (c.tau π m + 1)) (c.Xi π (c.tau π m)) (1 / 4) (1 / 2) 2 6 c.p.eta
    (c.n * c.p.δe / c.p.lam ^ 2) (df2Dev c.p d c.n) c.rhoPP (2 * df2Pri c.p) (c.p.theta * c.p.rho)
    (c.p.alpha * c.p.rho) (c.Xi π (c.tau π m) pt) (by norm_num) (by norm_num) (by norm_num) hη
    (by rw [hθ]; linarith) (by rw [hα]; positivity)
    (fun y hy => H.sand_i le_rfl (H.mem_SS hy).1)
    (fun y hy => by have := H.sand_ii le_rfl (H.mem_SS hy).1; linarith)
    (fun y hy => by have := H.eta_T hy; have := hW y; linarith)
    (fun y hy => H.sand_iv le_rfl (H.mem_SS hy).1 (H.mem_SS hy).2)
    (fun y hy => by
      have h1 := H.xi_eq le_rfl y
      obtain ⟨h00, h01⟩ := H.phi0_le (H.mem_SS hy).2
      constructor <;> linarith)
    (H.xi_acc le_rfl hacc) (fun b hb => hb pt hpt)

/-- The previous minimiser: a minimiser of `S_{τ-1}` over `K_ε` in `R⁻_τ` (condition 1 at `τ - 1`). -/
theorem prev_min (H : DetHyp c δ π m) :
    ∃ x0 ∈ c.Rm π (c.tau π m), ∀ y ∈ c.Keps, wrapS (c.sW π) (c.tau π m) x0 ≤ wrapS (c.sW π) (c.tau π m) y := by
  by_cases h0 : c.tau π m = 0
  · refine ⟨0, ?_, fun y _ => ?_⟩
    · rw [h0, Rm_zero]
      apply H.keps.2.2.1
      show oNorm ((0 : Fin d → ℝ) - 0) ≤ 1 - c.p.eps
      rw [sub_zero]
      have : oNorm (0 : Fin d → ℝ) = 0 := by simp [oNorm]
      rw [this]; linarith [H.heps]
    · rw [h0]; simp [wrapS]
  · obtain ⟨t, ht⟩ : ∃ t, c.tau π m = t + 1 := ⟨c.tau π m - 1, by omega⟩
    have htτ : t < c.tau π m := by omega
    obtain ⟨x0, hx0, hmin, hphi⟩ := (H.cond_lt_tau t htτ).1
    refine ⟨x0, ?_, fun y hy => ?_⟩
    · have e : c.Rm π (c.tau π m) = c.RmN π t := by rw [← H.Rm_succ htτ, ht]
      rw [e]; exact ⟨hx0, hphi⟩
    · rw [ht, Df2Ctx.wrapS_succ, Df2Ctx.wrapS_succ]; exact hmin y hy

/-- A minimiser of `S_τ` over `K_ε`. -/
theorem cur_min (H : DetHyp c δ π m) :
    ∃ x1 ∈ c.Keps, ∀ y ∈ c.Keps, c.SumS π (c.tau π m) x1 ≤ c.SumS π (c.tau π m) y := by
  have hcont : Continuous (c.SumS π (c.tau π m)) := by
    unfold Df2Ctx.SumS
    exact continuous_finsetSum _ fun u hu =>
      continuous_toLp' (H.si_at (by have := Finset.mem_range.1 hu; omega)).c2.continuous
  have h0 : (0 : Fin d → ℝ) ∈ c.Keps := by
    apply H.keps.2.2.1
    show oNorm ((0 : Fin d → ℝ) - 0) ≤ 1 - c.p.eps
    rw [sub_zero]
    have : oNorm (0 : Fin d → ℝ) = 0 := by simp [oNorm]
    rw [this]; linarith [H.heps]
  exact exists_min_on c.Keps c.p.R _ H.keps.2.1 H.keps.2.2.2 ⟨0, h0⟩ hcont

/-! ### The rows of Lemma D.14 -/

theorem row_s (H : DetHyp c δ π m) : c.wA1 + c.wA5 ≤ c.wKs := by
  have hη := H.rows.pos_eta; have hl := H.rows.pos_lam; have he := H.rows.pos_eps
  have r := H.rows.r22
  unfold Df2Ctx.wA1 Df2Ctx.wA5 Df2Ctx.wKs
  rw [le_div_iff₀ hη]
  have e : (1 + d * c.p.Le / (c.p.lam * c.p.eta) + (1 + 10 / (c.p.lam * c.p.eps))) * c.p.eta =
      2 * c.p.eta + d * c.p.Le / c.p.lam + 10 * c.p.eta / (c.p.eps * c.p.lam) := by
    field_simp; ring
  rw [e]; linarith

theorem row_c (H : DetHyp c δ π m) : c.wA2 + c.wKc ≤ c.wB := by
  have hη := H.rows.pos_eta
  have r := H.rows.r24o
  unfold Df2Ctx.wA2 Df2Ctx.wKc Df2Ctx.wB Df2Ctx.rhoPP
  rw [← add_div, div_le_div_iff_of_pos_right hη]
  linarith

theorem row_main (H : DetHyp c δ π m) : c.wA1 + c.wA2 ≤ c.p.rho / c.p.eta := by
  have hη := H.rows.pos_eta; have hl := H.rows.pos_lam
  have r := H.rows.r19o
  unfold Df2Ctx.wA1 Df2Ctx.wA2 Df2Ctx.rhoPP
  rw [le_div_iff₀ hη]
  have e : (1 + d * c.p.Le / (c.p.lam * c.p.eta) + (c.p.eta + (df2Pri c.p + df2Stab c.p d c.n + 1 +
      c.p.eta * df2DevK c.p d c.n)) / c.p.eta) * c.p.eta = c.p.eta + d * c.p.Le / c.p.lam + c.p.eta +
      (df2Pri c.p + df2Stab c.p d c.n + 1 + c.p.eta * df2DevK c.p d c.n) := by
    field_simp; ring
  rw [e]; linarith

/-! ### Lemma DF2-W -/

/-- Lemma D.14 at `τ`, for every `x ∈ K_ε`. -/
theorem w_main (H : DetHyp c δ π m) :
    (c.fire π (c.tau π m) → ∀ x ∈ c.Keps, c.eReg π (c.tau π m) x ≤ 0) ∧
    (¬ c.fire π (c.tau π m) →
      (∃ x1 ∈ c.Keps, (∀ y ∈ c.Keps, c.SumS π (c.tau π m) x1 ≤ c.SumS π (c.tau π m) y) ∧
        c.PhiN π (c.tau π m) x1 ≤ (c.p.c1 - c.p.gam) * c.p.rho) ∧
      ∀ x ∈ c.Keps, c.eReg π (c.tau π m) x ≤ c.p.rho / c.p.eta) := by
  set τ := c.tau π m with hτdef
  have hη := H.rows.pos_eta
  obtain ⟨x0, hx0, hmin0⟩ := H.prev_min
  obtain ⟨x1, hx1, hmin1⟩ := H.cur_min
  obtain ⟨pt, htc, hpt, hacc⟩ := H.accT_le (le_refl τ)
  obtain ⟨d2s, d2c⟩ := H.d2_inst hpt hacc
  have hm := H.mode_run (le_refl τ)
  have hRmK : c.Rm π τ ⊆ c.Keps := fun y hy => (H.Rm_sub_reg le_rfl hy).1
  let xs : ℕ → Fin d → ℝ := fun k => if k = τ + 1 then x1 else x0
  have hxs1 : xs (τ + 1) = x1 := by simp [xs]
  have hxs0 : xs (τ + 1 - 1) = x0 := by
    show (if τ + 1 - 1 = τ + 1 then x1 else x0) = x0
    simp
  have hν := H.nu_le
  have hconv : ConvexOn ℝ c.Keps (wrapS (c.sW π) (τ + 1)) :=
    convexOn_sum c.Keps H.keps.1 _ (c.sW π) fun u hu =>
      convexOn_toLp (H.si_at (by have := (Finset.mem_Icc.1 hu).2; omega)).convex H.keps.1
  have hW (x : Fin d → ℝ) (hx : x ∈ c.Keps) := H.W (Fin d → ℝ) c.Keps (c.Rm π τ) (c.Rm π τ ∩ c.RmN π τ) (τ + 1)
    (c.sW π) (c.sigW π) xs (c.wBeta π τ) (c.eReg π τ x) c.wA1 c.wA2 c.wA5 c.wKs c.wKc c.wB (c.fire π τ)
    (by omega) H.keps.1 (H.Rm_props le_rfl).2.1 hRmK Set.inter_subset_left hconv
    (by rw [hxs1]; exact hx1)
    (by rw [hxs1]; intro y hy; rw [Df2Ctx.wrapS_succ, Df2Ctx.wrapS_succ]; exact hmin1 y hy)
    (by rw [hxs0]; exact hmin0)
    (fun y _ => div_nonneg (H.OmT_nonneg le_rfl y _ le_rfl) hη.le)
    (by rw [hxs0]; exact hx0)
    (by
      rw [hxs1, Df2Ctx.wrapReg_eq]
      have h1 := H.w1 x
      have h2 : c.sReg π (τ + 1) x ≤ c.sReg π (τ + 1) x1 := by
        rw [Df2Ctx.sReg_eq, Df2Ctx.sReg_eq]; linarith [hmin1 x hx]
      unfold Df2Ctx.wA1; linarith)
    (fun y hy => H.w2 hy)
    (fun y hy hcl => H.w3a hy hcl)
    (fun y hy hb => H.w3b hy hb)
    (fun hf y hy => by
      obtain ⟨-, -, -, pt', htc', hXi⟩ := (c.fire_iff π τ hm).1 hf
      rw [htc] at htc'
      cases htc'
      have h := d2s hXi y hy
      rw [Df2Ctx.wrapReg_eq]
      unfold Df2Ctx.wKs
      rw [show -(((c.p.theta - c.p.alpha) * c.p.rho - 2 * df2Pri c.p - c.p.eta * df2Dev c.p d c.n - c.p.eta) /
        c.p.eta) = (-((c.p.theta - c.p.alpha) * c.p.rho - 2 * df2Pri c.p - c.p.eta * df2Dev c.p d c.n -
          c.p.eta)) / c.p.eta by ring, le_div_iff₀ hη]
      nlinarith)
    (fun hall => by
      have h := d2c fun y hy => by
        have := hall y hy
        rw [Df2Ctx.wrapReg_eq] at this
        unfold Df2Ctx.wKc at this
        rw [show -((7 * (c.p.theta * c.p.rho) + 6 * c.rhoPP + 7 * (c.p.eta * df2Dev c.p d c.n) + c.p.eta) /
          c.p.eta) = (-(7 * (c.p.theta * c.p.rho) + 6 * c.rhoPP + 7 * (c.p.eta * df2Dev c.p d c.n) +
            c.p.eta)) / c.p.eta by ring, le_div_iff₀ hη] at this
        nlinarith
      exact (c.fire_iff π τ hm).2 ⟨H.not_gdA le_rfl, H.not_gdT le_rfl, H.not_gdZ le_rfl, pt, htc, h⟩)
    (by
      rw [hxs0, hxs1]
      unfold Df2Ctx.sW
      rw [Nat.add_sub_cancel]
      have h0 := (H.si_at (le_refl τ)).bound x0 (hRmK hx0)
      have h1 := (H.si_at (le_refl τ)).bound x1 hx1
      unfold Df2Ctx.wA5
      linarith [h0.2, h1.1])
    H.row_s H.row_c
  refine ⟨fun hf x hx => (hW x hx).1 hf, fun hf => ⟨?_, fun x hx => ?_⟩⟩
  · obtain ⟨⟨-, -, hN⟩, -⟩ := (hW x1 hx1).2.2 hf
    rw [hxs1] at hN
    exact ⟨x1, hx1, hmin1, hN⟩
  · have := ((hW x hx).2.2 hf).2
    linarith [H.row_main]

/-- The epoch theorem on the path: (F) or (N). -/
theorem epoch_ok (H : DetHyp c δ π m) : c.EpochOK π m := by
  obtain ⟨hF, hN⟩ := H.w_main
  by_cases hf : c.fire π (c.tau π m)
  · exact Or.inl ⟨c.tau π m, H.tau_lt, fun s hs => (H.cond_lt_tau s hs).2.2.2, hf, hF hf⟩
  · obtain ⟨hc1, hreg⟩ := hN hf
    obtain ⟨ha, hq⟩ := H.aq (le_refl (c.tau π m))
    have hcond : c.Cond π (c.tau π m) :=
      ⟨hc1, ⟨by linarith, by linarith⟩, H.c3_tau, H.cont_tau hf⟩
    rcases H.tau_cases with ⟨hall, heq⟩ | hn
    · refine Or.inr ⟨fun s hs => (hall s hs).2.2.2, fun x hx => ?_⟩
      rw [← heq]
      exact hreg x hx
    · exact absurd hcond hn

end DetHyp

end AdversarialBco.Poly
