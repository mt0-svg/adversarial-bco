/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2DetSand

@[expose] public section

/-!
# DET, the regions of the calls, the statistic, and the online Newton step lemma with the defects

For a round `s ≤ τ`: the test region `R⁻ = Rm s` is `K_ε` at `s = 0` and the lower region of round `s - 1` after;
it lies in the region `Reg s` (so in the past ellipsoids and in `B_R`); `Rm`, `RmN` and `Rp` are closed and convex.
The statistic of the test is `Ξ = η T̂ - 2 Φ₀`. The online Newton step lemma with the defects ((U1)): if line μ was
accurate in the rounds `u < s`, then `η ĥqReg^κ ≤ pri + stab + 1` on `R⁻` of round `s`; each
Pythagorean defect is at most `1/(2n)` (`approx_min_pyth`, `defect_arith`).
-/

open Matrix MeasureTheory
open scoped Matrix

namespace AdversarialBco.Poly

open Layer2

theorem sum_Icc_one (f : ℕ → ℝ) (t : ℕ) : ∑ i ∈ Finset.Icc 1 t, f i = ∑ u ∈ Finset.range t, f (u + 1) := by
  induction t with
  | zero => simp
  | succ t ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem sum_Ico_one (f : ℕ → ℝ) (t : ℕ) :
    ∑ i ∈ Finset.Ico 1 (t + 1), f i = ∑ u ∈ Finset.range t, f (u + 1) := by
  induction t with
  | zero => simp
  | succ t ih => rw [Finset.sum_Ico_succ_top (by omega), ih, Finset.sum_range_succ]

theorem dot_sub_le {d : ℕ} {a b : Fin d → ℝ} {R : ℝ} (ha : oNorm a ≤ R) (hb : oNorm b ≤ R) :
    (a - b) ⬝ᵥ (a - b) ≤ 4 * R ^ 2 := by
  have h0 : ∀ v : Fin d → ℝ, 0 ≤ v ⬝ᵥ v := fun v => Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hsq : ∀ v : Fin d → ℝ, oNorm v ≤ R → v ⬝ᵥ v ≤ R ^ 2 := fun v hv => by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hv 2; rwa [Real.sq_sqrt (h0 v)] at this
  have e : (a - b) ⬝ᵥ (a - b) + (a + b) ⬝ᵥ (a + b) = 2 * (a ⬝ᵥ a + b ⬝ᵥ b) := by
    simp only [sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add, dotProduct_comm b a]; ring
  linarith [h0 (a + b), hsq a ha, hsq b hb]

namespace Df2Ctx

variable {d : ℕ} (c : Df2Ctx d) (π : Df2Path d)

/-- The test call of round `s` returns a point of its region within `eT` of the least value. -/
def AccT (s : ℕ) : Prop :=
  ∃ pt, c.tcall π s = some pt ∧ pt ∈ c.Rm π s ∧
    ∀ x ∈ c.Rm π s, ellF (c.Pn π s) (c.zz π s) pt ≤ ellF (c.Pn π s) (c.zz π s) x + c.eT

/-- Line μ of round `s`, from the test point `pt`, returns a point of `R⁺` within `eM` of the least value. -/
def AccM (s : ℕ) (pt : Fin d → ℝ) : Prop :=
  ∃ mu', c.mcall π s ((1 - c.p.sb) • pt) (c.p.sb * (1 - c.p.eps)) = some mu' ∧ mu' ∈ c.Rp π s ∧
    ∀ x ∈ c.Rp π s, ellF (c.Pn π s) (c.wmu π s) mu' ≤ ellF (c.Pn π s) (c.wmu π s) x + c.eM π s

/-- The point of line μ of round `u` is within `eM` of the least value over `R⁺`. -/
def ProjOK (u : ℕ) : Prop :=
  ∀ x ∈ c.Rp π u, ellF (c.Pn π u) (c.wmu π u) (c.st π (u + 1)).mu ≤ ellF (c.Pn π u) (c.wmu π u) x + c.eM π u

end Df2Ctx

namespace DetHyp

variable {d : ℕ} {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {m : ℕ}

/-! ### The regions of the calls -/

theorem Rm_zero (c : Df2Ctx d) (π : Df2Path d) : c.Rm π 0 = c.Keps := rfl

theorem Rm_succ (H : DetHyp c δ π m) {s : ℕ} (hs : s < c.tau π m) : c.Rm π (s + 1) = c.RmN π s := by
  have hI := H.stInv_le_tau (s + 1) hs
  have hf : (c.st π (s + 1)).first = false := by
    cases h : (c.st π (s + 1)).first
    · rfl
    · exact absurd (hI.first.1 h) (by omega)
  have hph := (H.succ_of_lt hs).1
  unfold Df2Ctx.Rm Df2Ctx.RmN
  simp only [hf, Bool.false_eq_true, ↓reduceIte]
  ext y
  exact and_congr_right fun _ => by rw [← hph y]; rfl

/-- The lower region of round `s` lies in the region of round `s + 1`... as a set of `Φ'`: `R⁻ ⊆ R⁺`. -/
theorem RmN_sub_Rp (H : DetHyp c δ π m) (s : ℕ) : c.RmN π s ⊆ c.Rp π s := by
  have := H.rows.pos_rho; have hg : c.p.gam = 1 / 100 := H.gam
  rintro y ⟨hy, h⟩; refine ⟨hy, h.trans ?_⟩; rw [hg]; nlinarith

theorem Rm_sub_reg (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) : c.Rm π s ⊆ c.Reg π s := by
  have hρ := H.rows.pos_rho; have hc1 := H.c1; have hg := H.gam
  rcases s with _ | s
  · intro y hy
    rw [Rm_zero] at hy
    refine ⟨hy, ?_⟩
    have h1 : c.Phi π 0 y ≤ df2Pri c.p := by
      rw [H.phi_zero]
      have hR := H.norm_le_of_keps hy
      have h0 := dot_self_nonneg y
      have hyy : y ⬝ᵥ y ≤ c.p.R ^ 2 := by
        have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hR 2; rwa [Real.sq_sqrt h0] at this
      have hs := H.rows.pos_sig2
      unfold df2Pri
      rw [show c.p.R ^ 2 / (2 * c.p.sig2) = 1 / 2 * c.p.sig2⁻¹ * c.p.R ^ 2 by field_simp]
      exact mul_le_mul_of_nonneg_left hyy (by positivity)
    have := H.pri_le_rho
    rw [hc1]; linarith
  · rw [H.Rm_succ (by omega)]
    rintro y ⟨hy, h⟩
    refine ⟨hy, ?_⟩
    rw [(H.succ_of_lt (by omega)).1 y, hg, hc1] at *
    rw [hg, hc1] at h
    linarith

theorem phi_set (P : Matrix (Fin d) (Fin d) ℝ) (hP : P.PosSemidef) (b : Fin d → ℝ) (k a : ℝ)
    (Q : Set (Fin d → ℝ)) (hQ : Convex ℝ Q) (hQc : IsClosed Q) :
    Convex ℝ {y | y ∈ Q ∧ df2Phi P b k y ≤ a} ∧ IsClosed {y | y ∈ Q ∧ df2Phi P b k y ≤ a} :=
  ⟨(phi_convex P hP b k a Q hQ hQc).2.2.1, (phi_convex P hP b k a Q hQ hQc).2.2.2⟩

theorem RmN_props (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    Convex ℝ (c.RmN π s) ∧ IsClosed (c.RmN π s) ∧ c.RmN π s ⊆ oBall 0 c.p.R :=
  ⟨(phi_set _ (H.r1_le_tau hs).1.posSemidef _ _ _ _ H.keps.1 H.keps.2.1).1,
    (phi_set _ (H.r1_le_tau hs).1.posSemidef _ _ _ _ H.keps.1 H.keps.2.1).2,
    fun _ hy => H.keps.2.2.2 hy.1⟩

theorem Rp_props (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    Convex ℝ (c.Rp π s) ∧ IsClosed (c.Rp π s) ∧ c.Rp π s ⊆ oBall 0 c.p.R :=
  ⟨(phi_set _ (H.r1_le_tau hs).1.posSemidef _ _ _ _ H.keps.1 H.keps.2.1).1,
    (phi_set _ (H.r1_le_tau hs).1.posSemidef _ _ _ _ H.keps.1 H.keps.2.1).2,
    fun _ hy => H.keps.2.2.2 hy.1⟩

theorem Rm_props (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    Convex ℝ (c.Rm π s) ∧ IsClosed (c.Rm π s) ∧ c.Rm π s ⊆ oBall 0 c.p.R := by
  rcases s with _ | s
  · rw [Rm_zero]; exact ⟨H.keps.1, H.keps.2.1, H.keps.2.2.2⟩
  · rw [H.Rm_succ (by omega)]; exact H.RmN_props (by omega)

/-! ### The statistic of the test -/

/-- `Ξ_s = η T̂ - 2 Φ₀` at `κ = 1/4`. -/
theorem xi_eq (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) (y : Fin d → ℝ) :
    c.Xi π s y = c.p.eta * c.ThT π (s + 1) y - 2 * c.Phi π 0 y := by
  have hI := H.stInv_le_tau s hs
  unfold Df2Ctx.Xi
  rw [H.PhiN_eq hs]
  have hl : c.ln π s - c.Gn π s ⬝ᵥ y = c.hLin π (s + 1) y := by
    unfold Df2Ctx.ln Df2Ctx.Gn Df2Ctx.hLin
    rw [hI.l, hI.G, ← Finset.sum_range_succ (fun u => c.ghat π u ⬝ᵥ (c.st π u).mu),
      add_dotProduct, sum_dotProduct, ← Finset.sum_range_succ (fun u => c.ghat π u ⬝ᵥ y),
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun u _ => by rw [dotProduct_sub]
  rw [hl]
  unfold Df2Ctx.ThT Df2Ctx.OmH
  rw [H.kap]; ring

/-! ### The online Newton step lemma with the defects -/

/-- The Newton point of line μ: `w_μ = μ - η Σ' ĝ` (the rank-one round lemma (iv)). -/
theorem wmu_eq (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    c.wmu π s = (c.st π s).mu - c.p.eta • (c.Sn π s *ᵥ c.ghat π s) := by
  have hI := H.stInv_le_tau s hs
  obtain ⟨ha, hq⟩ := H.aq hs
  have hR1 : R1Hyp (c.st π s).P (c.st π s).S (c.st π s).A := ⟨hI.pd, hI.AA, hI.SP⟩
  have hl1 : c.p.lam ≠ 1 := by have := H.rows.lam_le; intro h; linarith
  have h := (H.r1iv d _ _ _ (π.xi s) (c.cc π s) (c.Y π s) c.p.lam hR1 (by show 0 < c.aa π s; linarith)
    (by show 0 < c.qq π s; linarith) hl1).1
  have e : c.Sn π s *ᵥ c.ghat π s = (c.Y π s / ((1 - c.p.lam) * c.qq π s)) • c.w π s := h
  rw [e, smul_smul]
  unfold Df2Ctx.wmu
  congr 2; ring

/-- `|ĝ|²_{Σ'} = κ₀ Y² |ξ|²/q` (the rank-one round lemma (iv)). -/
theorem ghat_sq (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    df2Sq (c.Sn π s) (c.ghat π s) = c.p.k0 * c.Y π s ^ 2 * (π.xi s ⬝ᵥ π.xi s) / c.qq π s := by
  have hI := H.stInv_le_tau s hs
  obtain ⟨ha, hq⟩ := H.aq hs
  have hR1 : R1Hyp (c.st π s).P (c.st π s).S (c.st π s).A := ⟨hI.pd, hI.AA, hI.SP⟩
  have hl1 : c.p.lam ≠ 1 := by have := H.rows.lam_le; intro h; linarith
  have h := (H.r1iv d _ _ _ (π.xi s) (c.cc π s) (c.Y π s) c.p.lam hR1 (by show 0 < c.aa π s; linarith)
    (by show 0 < c.qq π s; linarith) hl1).2
  rw [H.k0]; exact h

/-- The stability term: `(η²/2) ∑_{u ≤ s} |ĝ_u|²_{Σ_{u+1}} ≤ stab` on G and Y. -/
theorem stab_le (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) :
    c.p.eta ^ 2 / 2 * ∑ u ∈ Finset.range (s + 1), df2Sq (c.Sn π u) (c.ghat π u) ≤ df2Stab c.p d c.n := by
  have hk0 := H.k0_pos; have hk1 := H.rows.k0_le
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hx : Real.log (1 / c.p.δe) = c.p.Le / 36 := by rw [H.Le_eq]; ring
  have hL := H.Le_pos
  set X := 32 / 9 * (d : ℝ) * Real.log (1 / c.p.δe) with hX
  have hX0 : 0 ≤ X := by rw [hX, hx]; positivity
  have hterm : ∀ u ∈ Finset.range (s + 1), df2Sq (c.Sn π u) (c.ghat π u) ≤ 4 * c.p.k0 * X * c.Y π u ^ 2 := by
    intro u hu
    have hut : u ≤ c.tau π m := by have := Finset.mem_range.1 hu; omega
    rw [H.ghat_sq hut]
    obtain ⟨-, hq⟩ := H.aq hut
    have hξ := H.xibd hut
    have hξ0 := dot_self_nonneg (π.xi u)
    rw [div_le_iff₀ (by linarith)]
    have : c.p.k0 * c.Y π u ^ 2 * (π.xi u ⬝ᵥ π.xi u) ≤ c.p.k0 * c.Y π u ^ 2 * X :=
      mul_le_mul_of_nonneg_left hξ (by positivity)
    have h5 : c.p.k0 * c.Y π u ^ 2 * X ≤ 4 * c.p.k0 * X * c.Y π u ^ 2 * c.qq π u := by
      have : 0 ≤ c.p.k0 * c.Y π u ^ 2 * X := by positivity
      nlinarith
    linarith
  have hY : ∑ u ∈ Finset.range (s + 1), c.Y π u ^ 2 ≤ 22 * c.n := by
    refine le_trans ?_ H.evY
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun _ _ _ => sq_nonneg _
  have h1 := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at h1
  have h2 : 4 * c.p.k0 * X * ∑ u ∈ Finset.range (s + 1), c.Y π u ^ 2 ≤ 4 * c.p.k0 * X * (22 * c.n) :=
    mul_le_mul_of_nonneg_left hY (by positivity)
  have h3 : c.p.eta ^ 2 / 2 * (4 * c.p.k0 * X * (22 * c.n)) ≤ df2Stab c.p d c.n := by
    unfold df2Stab df2Cg
    rw [hX, hx]
    have hn : (0 : ℝ) ≤ c.n := Nat.cast_nonneg _
    have : c.p.eta ^ 2 / 2 * (4 * c.p.k0 * (32 / 9 * d * (c.p.Le / 36)) * (22 * c.n)) =
        (c.p.k0 * (2 * 32 * 22 / (9 * 36))) * (c.p.eta ^ 2 * d * c.n * c.p.Le) := by ring
    rw [this]
    have : c.p.k0 * (2 * 32 * 22 / (9 * 36)) ≤ 2 * 4 := by nlinarith
    have hp : 0 ≤ c.p.eta ^ 2 * d * c.n * c.p.Le := by positivity
    nlinarith
  have hη : 0 ≤ c.p.eta ^ 2 / 2 := by positivity
  calc _ ≤ c.p.eta ^ 2 / 2 * (4 * c.p.k0 * X * ∑ u ∈ Finset.range (s + 1), c.Y π u ^ 2) :=
        mul_le_mul_of_nonneg_left h1 hη
    _ ≤ c.p.eta ^ 2 / 2 * (4 * c.p.k0 * X * (22 * c.n)) := mul_le_mul_of_nonneg_left h2 hη
    _ ≤ _ := h3

/-- A point of `R⁻` of round `s ≥ 1` is in `R⁺` of every round `u < s` (the monotonicity lemma and the margin R20). -/
theorem rm_sub_rp (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) {y : Fin d → ℝ} (hy : y ∈ c.Rm π s)
    {u : ℕ} (hu : u < s) : y ∈ c.Rp π u := by
  obtain ⟨hSS, hR⟩ := H.reg_sub hs (H.Rm_sub_reg hs hy)
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  rw [H.Rm_succ (by omega)] at hy
  obtain ⟨hyK, hyΦ⟩ := hy
  refine ⟨hyK, ?_⟩
  have hSD : y ∈ c.SD π (s' + 1) := (H.SD_succ s' y).2 fun v hv => hSS v (by omega)
  have hmon := H.mon_at (u := u + 1) (t := s' + 1) (by omega) (by omega) hSD hR
  rw [← H.PhiN_eq (by omega), ← H.PhiN_eq (by omega)] at hmon
  have h20 := H.rows.r20
  have hg := H.gam; have hc1 := H.c1; have hρ := H.rows.pos_rho
  linarith

/-- The online Newton step lemma with the defects at round `s ≤ τ`, when line μ was accurate before. -/
theorem ons (H : DetHyp c δ π m) {s : ℕ} (hs : s ≤ c.tau π m) (hP : ∀ u < s, c.ProjOK π u) {y : Fin d → ℝ}
    (hy : y ∈ c.Rm π s) : c.p.eta * c.hqReg π (s + 1) y ≤ df2Pri c.p + df2Stab c.p d c.n + 1 := by
  set τ := c.tau π m with hτ
  have hn1 : (1 : ℝ) ≤ c.n := by exact_mod_cast H.hn
  have hyK : y ∈ c.Keps := (H.Rm_sub_reg hs hy).1
  have hyR := H.norm_le_of_keps hyK
  set PO : ℕ → Matrix (Fin d) (Fin d) ℝ := fun i => if i ≤ 1 then (c.st π 0).P else c.Pn π (i - 2) with hPO
  set SO : ℕ → Matrix (Fin d) (Fin d) ℝ := fun i => if i ≤ 1 then (c.st π 0).S else c.Sn π (i - 2) with hSO
  have hPO1 : ∀ i, PO (i + 1 + 1) = c.Pn π i := fun i => by simp [hPO]
  have hSO1 : ∀ i, SO (i + 1 + 1) = c.Sn π i := fun i => by simp [hSO]
  have hPOi : ∀ i, i ≤ s → PO (i + 1) = (c.st π i).P := by
    intro i hi
    rcases i with _ | i
    · simp [hPO]
    · rw [hPO1]
      have hsl : i < τ := by omega
      have hI := H.stInv_le_tau i hsl.le
      obtain ⟨-, -, -, hcont⟩ := H.cond_lt_tau i hsl
      obtain ⟨pt, mu', -, -, -, -, hst⟩ := c.st_succ_of_cont π i hI.run hcont
      rw [hst]; rfl
  have h := H.ons2 d PO SO (fun i => c.p.kap • c.shh π (i - 1)) (fun i => (c.st π (i - 1)).mu)
    (fun i => c.ghat π (i - 1)) (fun _ => 1 / (2 * c.n)) c.p.eta (s + 1) y (by omega) ?step ?pd ?pyth
  case step =>
    intro i h1 h2
    obtain ⟨u, rfl⟩ : ∃ u, i = u + 1 := ⟨i - 1, by omega⟩
    rw [hPO1, hPOi u (by omega), Df2Ctx.Pn_eq, smul_smul]
    simp only [Nat.add_sub_cancel]
  case pd =>
    intro i h1 h2
    obtain ⟨u, rfl⟩ : ∃ u, i = u + 1 := ⟨i - 1, by omega⟩
    rw [hPO1, hSO1]
    exact ⟨(H.r1_le_tau (by omega)).1, (H.r1_le_tau (by omega)).2.1⟩
  case pyth =>
    intro i h1 h2
    obtain ⟨u, rfl⟩ : ∃ u, i = u + 1 := ⟨i - 1, by omega⟩
    have hu : u < τ := by omega
    simp only [Nat.add_sub_cancel]
    rw [hPO1, hSO1, ← H.wmu_eq hu.le]
    have hyp : y ∈ c.Rp π u := H.rm_sub_rp hs hy (by omega)
    have hmu := (H.succ_of_lt hu).2
    have hPpsd := (H.r1_le_tau hu.le).1.posSemidef
    have htr := hPpsd.trace_nonneg
    have hRp := H.Rp_props hu.le
    have hmR : oNorm (c.st π (u + 1)).mu ≤ c.p.R := H.norm_le_of_keps hmu.1
    set D := Real.sqrt (4 * c.p.R ^ 2 * (c.Pn π u).trace) with hD
    have hD0 : 0 ≤ D := Real.sqrt_nonneg _
    have hD2 : D ^ 2 = 4 * c.p.R ^ 2 * (c.Pn π u).trace := Real.sq_sqrt (by positivity)
    have heM : 0 ≤ c.eM π u := by unfold Df2Ctx.eM; positivity
    have hDb : df2Sq (c.Pn π u) ((c.st π (u + 1)).mu - y) ≤ D ^ 2 := by
      rw [hD2]
      calc _ ≤ (c.Pn π u).trace * (((c.st π (u + 1)).mu - y) ⬝ᵥ ((c.st π (u + 1)).mu - y)) :=
            sq_le_trace _ hPpsd _
        _ ≤ (c.Pn π u).trace * (4 * c.p.R ^ 2) := mul_le_mul_of_nonneg_left (dot_sub_le hmR hyR) htr
        _ = _ := by ring
    have hpy := approx_min_pyth (c.Rp π u) (c.Pn π u) hPpsd (c.wmu π u) (c.st π (u + 1)).mu y (c.eM π u) D
      hRp.1 hmu hyp heM hD0 (hP u (by omega)) hDb
    have hdef := defect_arith c.n H.hn c.p.R (c.Pn π u).trace D htr hD0 hD2.le
    have e : c.eM π u = 1 / (16 * (c.n : ℝ) ^ 2 * max 1 (4 * c.p.R ^ 2 * (c.Pn π u).trace)) := rfl
    rw [← e] at hdef
    linarith
  -- the three terms
  have hL : c.p.eta * ∑ i ∈ Finset.Icc 1 (s + 1),
      (c.ghat π (i - 1) ⬝ᵥ ((c.st π (i - 1)).mu - y) - 1 / 2 * df2Sq (c.p.kap • c.shh π (i - 1)) (y - (c.st π (i - 1)).mu)) =
      c.p.eta * c.hqReg π (s + 1) y := by
    rw [sum_Icc_one]
    unfold Df2Ctx.hqReg
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [Nat.add_sub_cancel, sq_smul]; ring
  have h1 : 1 / 2 * df2Sq (PO 1) ((c.st π (1 - 1)).mu - y) ≤ df2Pri c.p := by
    have : PO 1 = c.p.sig2⁻¹ • 1 := by simp [hPO]; rfl
    rw [this, sq_smul, sq_one, Nat.sub_self, show (c.st π 0).mu = 0 from rfl, zero_sub]
    simp only [neg_dotProduct, dotProduct_neg, neg_neg]
    have h0 := dot_self_nonneg y
    have hyy : y ⬝ᵥ y ≤ c.p.R ^ 2 := by
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hyR 2; rwa [Real.sq_sqrt h0] at this
    have hs2 := H.rows.pos_sig2
    unfold df2Pri
    rw [show c.p.R ^ 2 / (2 * c.p.sig2) = 1 / 2 * (c.p.sig2⁻¹ * c.p.R ^ 2) by field_simp]
    have : c.p.sig2⁻¹ * (y ⬝ᵥ y) ≤ c.p.sig2⁻¹ * c.p.R ^ 2 := mul_le_mul_of_nonneg_left hyy (by positivity)
    linarith
  have h2 : ∑ i ∈ Finset.Ico 1 (s + 1), (fun _ => 1 / (2 * (c.n : ℝ))) i ≤ 1 / 2 := by
    rw [sum_Ico_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : (s : ℝ) ≤ c.n := by
      have := (H.le_tau_lt hs).trans_le H.hmn; exact_mod_cast this.le
    rw [show (s : ℝ) * (1 / (2 * c.n)) = s / c.n / 2 by ring]
    have : (s : ℝ) / c.n ≤ 1 := by rw [div_le_one (by linarith)]; exact this
    linarith
  have h3 : c.p.eta ^ 2 / 2 * ∑ i ∈ Finset.Icc 1 (s + 1), df2Sq (SO (i + 1)) (c.ghat π (i - 1)) ≤
      df2Stab c.p d c.n := by
    rw [sum_Icc_one]
    simp only [hSO1, Nat.add_sub_cancel]
    exact H.stab_le hs
  rw [hL] at h
  linarith

end DetHyp

end AdversarialBco.Poly
