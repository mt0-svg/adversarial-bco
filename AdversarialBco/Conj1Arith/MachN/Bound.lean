/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Arith.MachN.Code
public import AdversarialBco.Conj1.CostL

@[expose] public section

/-!
# The step bound of the code of PG-N with CLAMP-NS

`kPGNS_boundL`: the step count `kPGNS d r₀ R₀ δ₁` of the code of PG-N with CLAMP-NS, at `δ₁ = (df2oPar d n δ).δ1`,
is at most `C (d log (2dn/δ) (2 + log (R₀/r₀)))^k` for explicit `C` and `k = 364`, for `d, n ≥ 1`, `0 < r₀ ≤ R₀` and
`0 < δ < 1`. Every parameter of a stage is at most `y = ⌈10^52 X^28⌉₊` with `X = d log (2dn/δ) (2 + log (R₀/r₀))`
(`pgb_XL`, Conj1/CostL.lean, and the parameter bounds of MachPGBound.lean); the counts `k`, `⌈log₂ (3k + 3)⌉₊` and
`J` of CLAMP-NS at stage `i` are at most `J = nsCount k ≤ pgNs d ρ_i` (`cnsJ_le_pgNs`). The step count of a stage is
then at most `C₀ y^12` (`kStageNS_le`), and the whole count at most `C₁ y^13` (`kPGpoly_leNS`).
-/

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL
  AdversarialBco.Poly.PG

namespace AdversarialBco.Conj1Arith

theorem kStageNS_le {y d jb N nT J mT k c Jn : ℕ} (hy : 1 ≤ y) (hd : d ≤ y) (hjb : jb ≤ y) (hN : N ≤ y)
    (hnT : nT ≤ y) (hJ : J ≤ y) (hmT : mT ≤ y) (hk : k ≤ y) (hc : c ≤ y) (hJn : Jn ≤ y) :
    kStageNS d jb N nT J mT k c Jn ≤ kStageNS 1 1 1 1 1 1 1 1 1 * y ^ 12 := by
  show PB y _ _ 12
  apply PB.mono hy
  case h =>
    unfold kStageNS kRepNS kDescNS kTestNS kVerdNS kSample kVerdNorm kVerdC12 kVerdC3P kPivT kStepNS kVinv kVmat kUpdNS kClampNS kNsCount kNsSym kNsClip kNsRoot kNsLoop kNsStep kNsOut kMtransp kMlin kMfill kMdiag kMmul kMtrace kCompC kGauge kGG kGJ kMemQ
    pb_tac hy
  case hc => simp only [kStageNS, kRepNS, kDescNS, kTestNS, kVerdNS, kSample, kVerdNorm, kVerdC12, kVerdC3P, kPivT, kStepNS, kVinv, kVmat, kUpdNS, kClampNS, kNsCount, kNsSym, kNsClip, kNsRoot, kNsLoop, kNsStep, kNsOut, kMtransp, kMlin, kMfill, kMdiag, kMmul, kMtrace, kCompC, kGauge, kGG, kGJ, kMemQ, le_refl]
  case hk => norm_num

theorem kPGNS_eq (d : ℕ) (r0 R0 δ₁ : ℝ) :
    kPGNS d r0 R0 δ₁ = kPGpoly d ⌈Real.logb 2 (R0 / r0)⌉₊ (pgJr (δ₁ / pgStages r0 R0)) (pgMT (δ₁ / pgStages r0 R0))
      (pgStages r0 R0) (kPGStageNS d r0 R0 δ₁) := rfl

theorem kPGpoly_leNS {y d m0 J mT m S : ℕ} (hy : 1 ≤ y) (hd : d ≤ y) (hm0 : m0 ≤ y) (hJ : J ≤ y) (hmT : mT ≤ y)
    (hm : m ≤ y) (hS : PB y S (kStageNS 1 1 1 1 1 1 1 1 1 + 8) 12) :
    kPGpoly d m0 J mT m S ≤ kPGpoly 1 1 1 1 1 (kStageNS 1 1 1 1 1 1 1 1 1 + 8) * y ^ 13 := by
  show PB y _ _ 13
  apply PB.mono hy
  case h =>
    unfold kPGpoly kCaps
    pb_tac2 hy hS
  case hc => simp only [kPGpoly, kCaps, le_refl]
  case hk => norm_num

theorem kPGStageNS_le {y d : ℕ} {r0 R0 δ₁ : ℝ} (hy : 1 ≤ y) (hd : d ≤ y) (hJ : pgJr (δ₁ / pgStages r0 R0) ≤ y)
    (hmT : pgMT (δ₁ / pgStages r0 R0) ≤ y)
    (hst : ∀ i < pgStages r0 R0, pgJb d (pgRhoStage d i) ≤ y ∧ pgNs d (pgRhoStage d i) ≤ y ∧
      pgNT d (pgRhoStage d i) ≤ y ∧ nsK d (pgRhoStage d i) ≤ y ∧
      Nat.clog 2 (3 * nsK d (pgRhoStage d i) + 3) ≤ y ∧ nsCount (nsK d (pgRhoStage d i)) ≤ y) :
    PB y (kPGStageNS d r0 R0 δ₁) (kStageNS 1 1 1 1 1 1 1 1 1 + 8) 12 := by
  unfold PB kPGStageNS
  refine Finset.sup_le fun i hi => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hst i (Finset.mem_range.1 hi)
  have := kStageNS_le hy hd h1 h2 h3 hJ hmT h4 h5 h6
  have h8 : 8 ≤ 8 * y ^ 12 := Nat.le_mul_of_pos_right _ (pow_pos hy 12)
  calc _ ≤ kStageNS 1 1 1 1 1 1 1 1 1 * y ^ 12 + 8 * y ^ 12 := Nat.add_le_add this h8
    _ = _ := by ring

/-- The step count of PG-N with CLAMP-NS is polynomial in `d log (2dn/δ) (2 + log (R₀/r₀))`. -/
theorem kPGNS_boundL : ∃ C : ℝ, ∃ k : ℕ, ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → ∀ r0 R0 δ : ℝ, 0 < r0 → r0 ≤ R0 → 0 < δ →
    δ < 1 → (kPGNS d r0 R0 (df2oPar d n δ).δ1 : ℝ) ≤
      C * ((d : ℝ) * Real.log (2 * d * n / δ) * (2 + Real.log (R0 / r0))) ^ k := by
  refine ⟨kPGpoly 1 1 1 1 1 (kStageNS 1 1 1 1 1 1 1 1 1 + 8) * (2 * 10 ^ 52) ^ 13, 28 * 13,
    fun d n hd hn r0 R0 δ hr0 hr hδ0 hδ1 => ?_⟩
  obtain ⟨hX1, hdX, hΛX, hLX, hL, hΛ⟩ := pgb_XL hd hn hδ0 hδ1 hr0 hr
  set L := Real.log (2 * d * n / δ) with hLdef
  set Λ := 2 + Real.log (R0 / r0) with hΛdef
  set X := (d : ℝ) * L * Λ with hXdef
  set δ₁ := (df2oPar d n δ).δ1 with hδ₁
  obtain ⟨hd0, hd1, hdlog⟩ := pgb_delta1 hd hn hδ0 hδ1
  rw [← df2oPar_δ1, ← hδ₁] at hd0 hd1 hdlog
  set m := pgStages r0 R0 with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  have hmX : (m : ℝ) ≤ 3 * X := (pgb_stages_le hr0 hr).trans hΛX
  obtain ⟨-, hJ⟩ := pgb_Jr_le hd0 hd1 hm1
  have hMT := pgb_MT_le hd0 hd1 hm1
  have hJX : (pgJr (δ₁ / m) : ℝ) ≤ 45 * X := by nlinarith
  have hMTX : (pgMT (δ₁ / m) : ℝ) ≤ 529 * X := by nlinarith
  set Y := (10 : ℝ) ^ 52 * X ^ 28 with hY
  have hY1 : 1 ≤ Y := by
    have : (1 : ℝ) ≤ X ^ 28 := one_le_pow₀ hX1
    nlinarith
  have toY : ∀ (v : ℕ) (c : ℝ) (j : ℕ), 0 ≤ c → c ≤ 10 ^ 52 → j ≤ 28 → (v : ℝ) ≤ c * X ^ j → v ≤ ⌈Y⌉₊ :=
    fun v c j hc0 hc hj h => Nat.cast_le.1 ((h.trans (pgb_pow_le hX1 hc0 hc hj)).trans (Nat.le_ceil Y))
  have hy : 1 ≤ ⌈Y⌉₊ := Nat.one_le_iff_ne_zero.2 (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; linarith)
  have hdy : d ≤ ⌈Y⌉₊ := toY d 1 1 (by norm_num) (by norm_num) (by norm_num) (by simpa using hdX)
  have hmy : m ≤ ⌈Y⌉₊ := toY m 3 1 (by norm_num) (by norm_num) (by norm_num) (by simpa using hmX)
  have hm0y : ⌈Real.logb 2 (R0 / r0)⌉₊ ≤ ⌈Y⌉₊ := (le_max_right _ _).trans hmy
  have hJy : pgJr (δ₁ / m) ≤ ⌈Y⌉₊ := toY _ 45 1 (by norm_num) (by norm_num) (by norm_num) (by simpa using hJX)
  have hMTy : pgMT (δ₁ / m) ≤ ⌈Y⌉₊ := toY _ 529 1 (by norm_num) (by norm_num) (by norm_num) (by simpa using hMTX)
  have hst : ∀ i < m, pgJb d (pgRhoStage d i) ≤ ⌈Y⌉₊ ∧ pgNs d (pgRhoStage d i) ≤ ⌈Y⌉₊ ∧
      pgNT d (pgRhoStage d i) ≤ ⌈Y⌉₊ ∧ nsK d (pgRhoStage d i) ≤ ⌈Y⌉₊ ∧
      Nat.clog 2 (3 * nsK d (pgRhoStage d i) + 3) ≤ ⌈Y⌉₊ ∧ nsCount (nsK d (pgRhoStage d i)) ≤ ⌈Y⌉₊ := by
    intro i _
    obtain ⟨hρ1, hρ2⟩ := pgb_rho_le hd i
    have hdX' : ∀ j : ℕ, (d : ℝ) ^ j ≤ X ^ j := fun j => pow_le_pow_left₀ (by positivity) hdX j
    have hNs : pgNs d (pgRhoStage d i) ≤ ⌈Y⌉₊ :=
      toY _ (1.8e11 * 26244 ^ 9) 28 (by norm_num) (by norm_num) (by norm_num)
        ((pgb_Ns_le pgNSize hd hρ1 hρ2).trans (mul_le_mul_of_nonneg_left (hdX' 28) (by norm_num)))
    have hJ' : nsCount (nsK d (pgRhoStage d i)) ≤ pgNs d (pgRhoStage d i) := cnsJ_le_pgNs hd hρ1
    have hc : nsCount (nsK d (pgRhoStage d i)) ≤ ⌈Y⌉₊ := hJ'.trans hNs
    refine ⟨toY _ (2 ^ 20) 2 (by norm_num) (by norm_num) (by norm_num) ?_, hNs,
      toY _ (3.7e6 * 26244 ^ 3) 11 (by norm_num) (by norm_num) (by norm_num) ?_, le_trans ?_ hc, le_trans ?_ hc, hc⟩
    · exact (pgb_Jb_le pgBisectSteps hd hρ1 hρ2).trans (mul_le_mul_of_nonneg_left (hdX' 2) (by norm_num))
    · exact (pgb_NT_le pgNTSize hd hρ1 hρ2).trans (mul_le_mul_of_nonneg_left (hdX' 11) (by norm_num))
    · unfold nsCount; omega
    · unfold nsCount; omega
  have hk := kPGpoly_leNS hy hdy hm0y hJy hMTy hmy (kPGStageNS_le hy hdy hJy hMTy hst)
  rw [kPGNS_eq]
  have hceil : (⌈Y⌉₊ : ℝ) ≤ 2 * Y := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ Y)
    linarith
  calc (kPGpoly d ⌈Real.logb 2 (R0 / r0)⌉₊ (pgJr (δ₁ / m)) (pgMT (δ₁ / m)) m (kPGStageNS d r0 R0 δ₁) : ℝ)
      ≤ (kPGpoly 1 1 1 1 1 (kStageNS 1 1 1 1 1 1 1 1 1 + 8) : ℝ) * (⌈Y⌉₊ : ℝ) ^ 13 := by exact_mod_cast hk
    _ ≤ (kPGpoly 1 1 1 1 1 (kStageNS 1 1 1 1 1 1 1 1 1 + 8) : ℝ) * (2 * Y) ^ 13 := by gcongr
    _ = _ := by rw [hY, ← mul_assoc, mul_pow, ← pow_mul, mul_assoc]

end AdversarialBco.Conj1Arith
