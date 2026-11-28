/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EngInd
public import AdversarialBco.Unified.EngAsm

@[expose] public section

/-!
# Step 1 of SHADOW for BL-O's record: the shift and the regret of a round

Bit/BLEngine.lean's `shR_run`, `round_bound` for BL-O's record `recO` (Unified/AsmRec.lean), with piece C's play
(`PlayCO`, Unified/EngDefs.lean) as a hypothesis. What BL-O adds to v2.1:

* the noise: the shift of a round is `m = (r - 1) ε_t + μ` with `r = pt'/pt°` and `μ = 2 (e'(X') - e(X°))/pt°`
  (`shR_runO`), and `tvB(m, r) ≤ 2 (|r - 1| + |μ|) + 2 |r - 1| |ε_t|` for `r ≥ 1/2` (`tau_shift` of
  Unified/BLOParam.lean);
* the gauge band: BL-O's scale is `pt' = max(1, π̃(X')/(1 - ε'))` with `π(X') ≤ π̃ ≤ (1 + 2^{-p-2}) π(X')`
  (`gaugeBandO`), so `|pt' - pt_{ε'}(X')| ≤ 2^{-p-1} π̄ = gb` (`pt_band`), and moving the scale from `pt_{ε'}(X')` to
  `pt'` moves the play's loss by at most `R gb/ε` and the observation's mean by `gb (1/2 + (R/2 + 2)/ε)` (`band_pt`);
  with v2.1's bound (`ext_lip_shift`, Lemma MPAR) this gives `|r - 1| + |μ| ≤ S + band` (`shift_band`), and the
  regret of the round is at most `regO/n` (`play_gap`).

`roundBndO : PlayCO → RoundBndO`.
-/

open MeasureTheory

namespace AdversarialBco.Unified.Eng

open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World AdversarialBco.Unified.BLO AdversarialBco.Unified.Asm
open AdversarialBco.Unified.BudK (BudOK RunCaseK poK parK budO)
open AdversarialBco.Bit.BLP (Par St Mode init refX refPt cV cM opN)
open AdversarialBco.Bit.BLP.EngL (ptE extE)
open AdversarialBco.BitRAM (toE)
open AdversarialBco.Poly.Conj1 (fL)
open Matrix

variable {d : ℕ}

/-! ## The gauge band on a body -/

/-- **Moving the scale of a point** from `pt_{ε'}(X)` to any `p ≥ max(1, gauge(X)/(1 - ε'))`: the loss at the
scaled point moves by at most `R |Δ|/ε`, the mean `p F(X/p)/2 + 2(p - 1)/ε'` by at most `|Δ| (1/2 + (R/2 + 2)/ε)`,
`Δ = p - pt_{ε'}(X)`. -/
theorem band_pt (K : Set (E d)) (hK : Convex ℝ K) (hKc : IsClosed K)
    (h1 : Metric.closedBall (0 : E d) 1 ⊆ K) (R : ℝ) (hR : K ⊆ Metric.closedBall 0 R) (F : E d → ℝ)
    (hF01 : ∀ x ∈ K, F x ∈ Set.Icc (0 : ℝ) 1) (ε ε' : ℝ) (hε0 : 0 < ε) (hε : ε ≤ ε') (hε' : ε' ≤ 1 / 2)
    (hlip : ∀ a b : E d, (1 - ε)⁻¹ • a ∈ K → (1 - ε)⁻¹ • b ∈ K → F b - F a ≤ ‖b - a‖ / ε)
    (X : E d) (p : ℝ) (hp1 : 1 ≤ p) (hpg : gauge K X / (1 - ε') ≤ p) :
    |F (p⁻¹ • X) - F ((ptE K ε' X)⁻¹ • X)| ≤ R * |p - ptE K ε' X| / ε ∧
    |(p * F (p⁻¹ • X) / 2 + 2 * (p - 1) / ε') - extE K ε' F X| ≤
      |p - ptE K ε' X| * (1 / 2 + (R / 2 + 2) / ε) := by
  have hε1 : ε < 1 := by linarith
  have hε'0 : 0 < ε' := by linarith
  have hKn : K ∈ nhds (0 : E d) :=
    Filter.mem_of_superset (Metric.closedBall_mem_nhds (0 : E d) one_pos) h1
  have hR0 : 0 ≤ R := by
    have h := hR (h1 (Metric.mem_closedBall_self zero_le_one))
    simpa using h
  have hmemK : ∀ y : E d, gauge K y ≤ 1 → y ∈ K := by
    intro y hy
    have hc : y ∈ closure K := (gauge_le_one_iff_mem_closure hK hKn).1 hy
    rwa [hKc.closure_eq] at hc
  have hgq : ∀ q : ℝ, 1 ≤ q → gauge K X / (1 - ε') ≤ q → gauge K (q⁻¹ • X) ≤ 1 - ε' := by
    intro q hq hqg
    rw [div_le_iff₀ (by linarith)] at hqg
    rw [gauge_smul_of_nonneg (inv_nonneg.2 (by linarith)), smul_eq_mul, inv_mul_le_iff₀ (by linarith)]
    linarith
  have hmem : ∀ y : E d, gauge K y ≤ 1 - ε' → (1 - ε)⁻¹ • y ∈ K := by
    intro y hy
    refine hmemK _ ?_
    rw [gauge_smul_of_nonneg (inv_nonneg.2 (by linarith)), smul_eq_mul, inv_mul_le_iff₀ (by linarith)]
    linarith
  have hext : extE K ε' F X = ptE K ε' X * F ((ptE K ε' X)⁻¹ • X) / 2 + 2 * (ptE K ε' X - 1) / ε' := rfl
  rw [hext]
  generalize hq1 : ptE K ε' X = p1 at *
  have hp11 : 1 ≤ p1 := hq1 ▸ le_max_left _ _
  have hp1g : gauge K X / (1 - ε') ≤ p1 := hq1 ▸ le_max_right _ _
  have hg0 := hgq p hp1 hpg
  have hg1 := hgq p1 hp11 hp1g
  have hyK : p⁻¹ • X ∈ K := hmemK _ (hg0.trans (by linarith))
  have hy1K : p1⁻¹ • X ∈ K := hmemK _ (hg1.trans (by linarith))
  have hFd : |F (p⁻¹ • X) - F (p1⁻¹ • X)| ≤ ‖p⁻¹ • X - p1⁻¹ • X‖ / ε := by
    rw [abs_le]
    constructor
    · have h := hlip _ _ (hmem _ hg0) (hmem _ hg1)
      rw [norm_sub_rev] at h
      linarith
    · exact hlip _ _ (hmem _ hg1) (hmem _ hg0)
  have hXn : ∀ q : ℝ, 1 ≤ q → q⁻¹ • X ∈ K → ‖X‖ ≤ q * R := by
    intro q hq hqK
    have h := hR hqK
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos (by linarith : (0 : ℝ) < q), inv_mul_le_iff₀ (by linarith)] at h
    exact h
  have hX1 := hXn p1 hp11 hy1K
  have hX0 := hXn p hp1 hyK
  have hp0 : p ≠ 0 := by positivity
  have hp10 : p1 ≠ 0 := by positivity
  have hnd : ‖p⁻¹ • X - p1⁻¹ • X‖ = |p - p1| * ‖X‖ / (p * p1) := by
    rw [← sub_smul, norm_smul, Real.norm_eq_abs, inv_sub_inv hp0 hp10, abs_div,
      abs_of_pos (by positivity : 0 < p * p1), abs_sub_comm]
    ring
  have hnorm : 0 ≤ ‖X‖ := norm_nonneg _
  have hD : 0 ≤ |p - p1| := abs_nonneg _
  refine ⟨?_, ?_⟩
  · have hA : |p - p1| * ‖X‖ / (p * p1) ≤ R * |p - p1| := by
      rw [div_le_iff₀ (by positivity)]
      have : ‖X‖ ≤ p * p1 * R := by nlinarith
      nlinarith
    calc _ ≤ ‖p⁻¹ • X - p1⁻¹ • X‖ / ε := hFd
      _ = |p - p1| * ‖X‖ / (p * p1) / ε := by rw [hnd]
      _ ≤ R * |p - p1| / ε := div_le_div_of_nonneg_right hA hε0.le
  · have hF0 := hF01 _ hyK
    have hB : p1 * |F (p⁻¹ • X) - F (p1⁻¹ • X)| ≤ R * |p - p1| / ε := by
      have h := mul_le_mul_of_nonneg_left hFd (by linarith : (0 : ℝ) ≤ p1)
      rw [hnd] at h
      have e : p1 * (|p - p1| * ‖X‖ / (p * p1) / ε) = |p - p1| * (‖X‖ / p) / ε := by
        field_simp
      rw [e] at h
      have hXp : ‖X‖ / p ≤ R := by rw [div_le_iff₀ (by linarith)]; linarith
      refine h.trans ?_
      rw [mul_comm R]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hXp hD) hε0.le
    have e : (p * F (p⁻¹ • X) / 2 + 2 * (p - 1) / ε') - (p1 * F (p1⁻¹ • X) / 2 + 2 * (p1 - 1) / ε') =
        (p - p1) * F (p⁻¹ • X) / 2 + p1 * (F (p⁻¹ • X) - F (p1⁻¹ • X)) / 2 + 2 * (p - p1) / ε' := by ring
    rw [e]
    have t1 : |(p - p1) * F (p⁻¹ • X) / 2| ≤ |p - p1| / 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg hF0.1, abs_two]
      exact div_le_div_of_nonneg_right (mul_le_of_le_one_right hD hF0.2) (by norm_num)
    have t2 : |p1 * (F (p⁻¹ • X) - F (p1⁻¹ • X)) / 2| ≤ R * |p - p1| / ε / 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ p1), abs_two]
      exact div_le_div_of_nonneg_right hB (by norm_num)
    have t3 : |2 * (p - p1) / ε'| ≤ 2 * |p - p1| / ε := by
      rw [abs_div, abs_mul, abs_two, abs_of_pos hε'0]
      exact div_le_div_of_nonneg_left (by positivity) hε0 hε
    have hs := abs_add_le ((p - p1) * F (p⁻¹ • X) / 2 + p1 * (F (p⁻¹ • X) - F (p1⁻¹ • X)) / 2)
      (2 * (p - p1) / ε')
    have hs2 := abs_add_le ((p - p1) * F (p⁻¹ • X) / 2) (p1 * (F (p⁻¹ • X) - F (p1⁻¹ • X)) / 2)
    have e2 : |p - p1| * (1 / 2 + (R / 2 + 2) / ε) = |p - p1| / 2 + R * |p - p1| / ε / 2 + 2 * |p - p1| / ε := by
      field_simp
      ring
    rw [e2]
    linarith

/-- The shift with the scale moved: `|p/pt° - 1| + |2(e - e₀)/pt°| ≤ S₀ + |p - p₁| (1 + 2c)` from v2.1's bound `S₀` at
the scale `p₁` and `|e - e₁| ≤ |p - p₁| c`. -/
theorem shift_band (p p1 pto e e1 e0 c S0 : ℝ) (hpto : 1 ≤ pto)
    (h0 : |p1 / pto - 1| + |2 * (e1 - e0) / pto| ≤ S0) (he : |e - e1| ≤ |p - p1| * c) :
    |p / pto - 1| + |2 * (e - e0) / pto| ≤ S0 + |p - p1| * (1 + 2 * c) := by
  have hp0 : 0 < pto := by linarith
  have a1 : |p / pto - 1| ≤ |p1 / pto - 1| + |p - p1| := by
    have e' : p / pto - 1 = (p1 / pto - 1) + (p - p1) / pto := by field_simp; ring
    rw [e']
    refine (abs_add_le _ _).trans ?_
    have : |(p - p1) / pto| ≤ |p - p1| := by
      rw [abs_div, abs_of_pos hp0]; exact div_le_self (abs_nonneg _) hpto
    linarith
  have a2 : |2 * (e - e0) / pto| ≤ |2 * (e1 - e0) / pto| + 2 * (|p - p1| * c) := by
    have e' : 2 * (e - e0) / pto = 2 * (e1 - e0) / pto + 2 * (e - e1) / pto := by ring
    rw [e']
    refine (abs_add_le _ _).trans ?_
    have : |2 * (e - e1) / pto| ≤ 2 * (|p - p1| * c) := by
      rw [abs_div, abs_mul, abs_two, abs_of_pos hp0]
      calc 2 * |e - e1| / pto ≤ 2 * |e - e1| := div_le_self (by positivity) hpto
        _ ≤ 2 * (|p - p1| * c) := by linarith
    linarith
  have e3 : |p - p1| * (1 + 2 * c) = |p - p1| + 2 * (|p - p1| * c) := by ring
  rw [e3]
  linarith

/-- The band of the scale: `π ≤ π̃ ≤ (1 + η) π`, `π ≤ π̄` and `ε' ≤ 1/2` give
`|max(1, π̃/(1 - ε')) - max(1, π/(1 - ε'))| ≤ 2 η π̄`. -/
theorem pt_band (g gt ε' η pib : ℝ) (hg0 : 0 ≤ g) (h1 : g ≤ gt) (h2 : gt ≤ (1 + η) * g) (hη : 0 ≤ η)
    (hε' : ε' ≤ 1 / 2) (hgp : g ≤ pib) :
    |max 1 (gt / (1 - ε')) - max 1 (g / (1 - ε'))| ≤ 2 * η * pib := by
  have hd : 0 < 1 - ε' := by linarith
  rw [max_comm 1, max_comm 1]
  calc _ ≤ |gt / (1 - ε') - g / (1 - ε')| := abs_max_sub_max_le_abs _ _ _
    _ = (gt - g) / (1 - ε') := by rw [← sub_div, abs_div, abs_of_nonneg (by linarith), abs_of_pos hd]
    _ ≤ 2 * (gt - g) := by rw [div_le_iff₀ hd]; nlinarith
    _ ≤ 2 * η * pib := by nlinarith

/-- The shift with the noise: from `|r - 1| + |μ| ≤ S ≤ 1/4`, `r > 0` and `tvB((r - 1) ε + μ, r) ≤ 2 S + 2 S |ε|`. -/
theorem tv_noise (r nz μ S : ℝ) (h : |r - 1| + |μ| ≤ S) (hS : S ≤ 1 / 4) :
    0 < r ∧ Bit.Cpl.tvB ((r - 1) * nz + μ) r ≤ 2 * S + 2 * S * |nz| := by
  have hr1 : |r - 1| ≤ S := by linarith [abs_nonneg μ]
  have hr : 1 / 2 ≤ r := by linarith [(abs_le.1 (hr1.trans hS)).1]
  refine ⟨by linarith, ?_⟩
  unfold Bit.Cpl.tvB
  refine (tau_shift r nz μ hr).trans ?_
  have hn : 0 ≤ |nz| := abs_nonneg _
  nlinarith

/-! ## BL-O's play and body -/

/-- On a good position the body `kTh` of P° is the body `S(K)` of BL-O's configuration. -/
theorem kTh_eq_bodyS {n : ℕ} {δ : ℝ} {K : Set (E d)} {c : CfgO d}
    (hq : PgGood d K (df2oPar d n δ).R (some c.S)) : kTh n δ K c.S = bodyS K c := by
  rw [kTh_good hq, df2Kp_eq_posBody hq]
  rfl

/-- BL-O's play in mode `run` is the play of its point `X'` at the scale `pt'`. -/
theorem playPtO_run (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (st : St d) (ξ : Fin d → ℚ) :
    toE (playPtO orc c (.run st) ξ) =
      pgMu c.S + pgOp c.S (((ptO orc c (XO c st ξ) : ℚ) : ℝ)⁻¹ • toE (XO c st ξ)) := by
  have h := toE_pos c ((ptO orc c (XO c st ξ))⁻¹) (XO c st ξ)
  show toE (c.μS + c.AS *ᵥ ((ptO orc c (XO c st ξ))⁻¹ • XO c st ξ)) = _
  rw [h, affO, WithLp.toLp_smul, Rat.cast_inv]
  rfl

/-! ## The totals of a round -/

/-- The shift's total: v2.1's `S₀ ≤ S` and the band `|Δ| (1 + 2c) ≤ gb (2 + (R π̄ + 4)/ε)`. -/
theorem shift_total (A Δ gb R pib ε S0 Sx : ℝ) (hA : A ≤ S0 + Δ * (1 + 2 * (1 / 2 + (R / 2 + 2) / ε)))
    (hS0 : S0 ≤ Sx) (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ gb) (hR : 0 ≤ R) (hpib : 1 ≤ pib) (hε : 0 < ε) :
    A ≤ Sx + gb * (2 + (R * pib + 4) / ε) := by
  have h1 : 1 + 2 * (1 / 2 + (R / 2 + 2) / ε) = 2 + (R + 4) / ε := by field_simp; ring
  have h2 : (R + 4) / ε ≤ (R * pib + 4) / ε := div_le_div_of_nonneg_right (by nlinarith) hε.le
  have h3 : 0 ≤ 2 + (R + 4) / ε := by positivity
  rw [h1] at hA
  have h4 : Δ * (2 + (R + 4) / ε) ≤ gb * (2 + (R * pib + 4) / ε) := by
    calc Δ * (2 + (R + 4) / ε) ≤ gb * (2 + (R + 4) / ε) := mul_le_mul_of_nonneg_right hΔ h3
      _ ≤ gb * (2 + (R * pib + 4) / ε) := mul_le_mul_of_nonneg_left (by linarith) (hΔ0.trans hΔ)
  linarith

/-- The regret's total: the play gap at the scale `pt_{ε'}(X')` and the move of the scale to `pt'`. -/
theorem regret_total (a b c Xb R pib w we gb Δ ε N : ℝ)
    (hbc : |b - c| ≤ ((1 + 2 * R) * Xb + 4 * R * pib * w) / ε) (hab : |a - b| ≤ R * Δ / ε) (hw : w ≤ we)
    (hΔ : Δ ≤ gb) (hR : 0 ≤ R) (hpib : 0 ≤ pib) (hε : 0 < ε) (hN : 0 < N) :
    a ≤ c + N / ε * ((1 + 2 * R) * Xb + 4 * R * pib * we + R * gb) / N := by
  have hε' := hε.ne'
  have hN' := hN.ne'
  have e : N / ε * ((1 + 2 * R) * Xb + 4 * R * pib * we + R * gb) / N =
      ((1 + 2 * R) * Xb + 4 * R * pib * we) / ε + R * gb / ε := by
    field_simp
  rw [e]
  have h1 : ((1 + 2 * R) * Xb + 4 * R * pib * w) / ε ≤ ((1 + 2 * R) * Xb + 4 * R * pib * we) / ε :=
    div_le_div_of_nonneg_right
      (by have := mul_le_mul_of_nonneg_left hw (by positivity : (0 : ℝ) ≤ 4 * R * pib); linarith) hε.le
  have h2 : R * Δ / ε ≤ R * gb / ε := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hΔ hR) hε.le
  have := le_abs_self (a - b)
  have := le_abs_self (b - c)
  linarith

/-! ## The round on the record -/

section Rec

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {K : Set (E d)} {coin : Ω → ℕ → Bool}
  {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ} {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ}
  {orc : (Fin d → ℚ) → ℕ → Bool}

set_option hygiene false in
local notation "BB" => recO n δ r0 R0 a orc h hI.convex
set_option hygiene false in
local notation "WE" => extO n δ r0 R0 a h
set_option hygiene false in
local notation "WW" => envWorld orc coin loss noise ω.1
set_option hygiene false in
local notation "CC" => cfgW d n δ r0 R0 a (envWorld orc coin loss noise ω.1)
set_option hygiene false in
local notation "DB" => dBL d n δ
set_option hygiene false in
local notation "XS" => (so.mu + (1 - (df2oPar d n (dBL d n δ)).lam) • (so.A *ᵥ (extO n δ r0 R0 a h).xi t ω))
set_option hygiene false in
local notation "KT" => kTh n (dBL d n δ) K ((recO n δ r0 R0 a orc h hI.convex).pos ω)
set_option hygiene false in
local notation "EP" => (df2oPar d n (dBL d n δ)).eps
set_option hygiene false in
local notation "PTO" => ptE KT EP (WithLp.toLp 2 XS)
set_option hygiene false in
local notation "XQ" =>
  XO (cfgW d n δ r0 R0 a (envWorld orc coin loss noise ω.1)) st (drawO d n δ r0 R0 (coin ω.1) t).1
set_option hygiene false in
local notation "PT1" => ((ptO orc (cfgW d n δ r0 R0 a (envWorld orc coin loss noise ω.1)) XQ : ℚ) : ℝ)
set_option hygiene false in
local notation "FF" => fun y => (recO n δ r0 R0 a orc h hI.convex).loss ω t
  (pgMu ((recO n δ r0 R0 a orc h hI.convex).pos ω) + pgOp ((recO n δ r0 R0 a orc h hI.convex).pos ω) y)
set_option hygiene false in
local notation "EQ" => (((cfgW d n δ r0 R0 a (envWorld orc coin loss noise ω.1)).par.eps : ℚ) : ℝ)

/-- **BL-O's shift of a round** at which both learners are in mode `run`: `r = pt'/pt°` and
`m = (r - 1) ε_t + 2 (e'(X') - e(X°))/pt°`, `e'(X') = pt' f(x')/2 + 2 (pt' - 1)/ε'` with the gauge play `pt'`. -/
theorem shR_runO (hI : InpU n δ r0 R0 a K orc) (hc : RunCaseO d n δ)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) {ω : Ω × (ℕ → ℝ)}
    (hq : (BB).Case DB ω) {t : ℕ} (ht : t < n) {so : Df2St d} {st : St d}
    (hmo : (BB).mode DB t ω = .run so) (hW : modeO d n δ r0 R0 a WW t = .run st) :
    (BB).shR DB t ω = ((PT1 / PTO - 1) * (WE).nz t ω +
      2 * ((PT1 * (FF) (PT1⁻¹ • toE XQ) / 2 + 2 * (PT1 - 1) / EQ) - extE KT EP (FF) (WithLp.toLp 2 XS)) / PTO,
      PT1 / PTO) := by
  obtain ⟨heps0, heps1⟩ := eps01 hI hc
  obtain ⟨hrp, hint⟩ := RunW.refPlay_run _ hI.convex hq heps0 heps1 hmo
  rw [hrp] at hint
  have hpl : toE (playO d n δ r0 R0 a WW t) = pgMu ((BB).pos ω) + pgOp ((BB).pos ω) (PT1⁻¹ • toE XQ) := by
    have e : playO d n δ r0 R0 a WW t = playPtO orc CC (.run st) (drawO d n δ r0 R0 (coin ω.1) t).1 := by
      unfold playO
      rw [hW]
      rfl
    rw [e]
    exact playPtO_run orc CC st _
  refine Prod.ext ?_ ?_
  · have e1 : ((BB).shR DB t ω).1 = (PT1 / PTO - 1) * (WE).nz t ω +
        (PT1 * (BB).F.L t ((BB).F.lam t ω) (toE (playO d n δ r0 R0 a WW t)) -
          PTO * (if t < n then fL K (BB).F.L t ((BB).F.lam t ω) else 0)
            (pgMu ((BB).pos ω) + pgOp ((BB).pos ω) (WithLp.toLp 2 (PTO⁻¹ • XS))) +
          4 * (PT1 - 1) / EQ - 4 * (PTO - 1) / EP) / PTO := by
      show (shO n δ r0 R0 a orc h hI.convex t ω ((BB).mode DB t ω)).1 = _
      rw [hmo]
      unfold shO
      rw [if_pos ht, hW]
      all_goals rfl
    rw [e1, if_pos ht, WithLp.toLp_smul, fL_interior hint, hpl]
    show _ = _ + 2 * ((PT1 * (BB).F.L t ((BB).F.lam t ω)
        (pgMu ((BB).pos ω) + pgOp ((BB).pos ω) (PT1⁻¹ • toE XQ)) / 2 + 2 * (PT1 - 1) / EQ) -
      (PTO * (BB).F.L t ((BB).F.lam t ω) (pgMu ((BB).pos ω) + pgOp ((BB).pos ω) (PTO⁻¹ • WithLp.toLp 2 XS)) / 2 +
        2 * (PTO - 1) / EP)) / PTO
    ring
  · show (shO n δ r0 R0 a orc h hI.convex t ω ((BB).mode DB t ω)).2 = _
    rw [hmo]
    unfold shO
    rw [if_pos ht, hW]
    all_goals rfl

/-- **The shift and the regret of a round** in `IND(t)` on `Case ∩ Ω_ref ∩ E_bits ∩ NoClip`, from piece C's play. -/
theorem round_bndO (hP : PlayCO) (hI : InpU n δ r0 R0 a K orc) (hc : RunCaseO d n δ)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) {ω : Ω × (ℕ → ℝ)}
    (hq : (BB).Case DB ω) (hG : (BB).Good DB ω) (hbits : ω ∈ (BB).bits) {t : ℕ} (ht : t < n)
    (hInv : EngInvO n δ r0 R0 a orc h hI.convex ω t) :
    (0 < ((BB).shR DB t ω).2 ∧
      Bit.Cpl.tvB ((BB).shR DB t ω).1 ((BB).shR DB t ω).2 ≤
        BudK.kapO d n (kDel δ) + BudK.kapO d n (kDel δ) * |(WE).nz t ω|) ∧
    (BB).loss ω t ((BB).play t ω) ≤ (BB).loss ω t ((BB).refPlay DB t ω) + BudK.regO d n (kDel δ) / n := by
  obtain ⟨a0, s, st, hts, hfa, hcont, hW, htr⟩ := hInv
  have hd := hI.hd
  have hn := hI.hn
  have hreg : Regime d n DB :=
    ⟨hd, hn, deltaO_pos d n _ hd hn, deltaO_lt_one d n _ hd hn, hc.trans (by norm_num)⟩
  obtain ⟨hmo, hdet, htau⟩ :=
    RunW.round_ctx _ hreg hI.compact.isClosed hI.convex hq hG (by omega : a0 + s < n) hfa hcont
  have hbud : BudOK d n (kDel δ) := budO d n δ hd hn hc
  obtain ⟨heps0, heps1⟩ := eps01 hI hc
  obtain ⟨he0, hee, he', hwe⟩ := eps_factsK hd hn hc hbud
  -- piece C's play
  have hxe : ((BB).path DB a0 ω).xi s = (WE).xi t ω := by rw [← hts]; rfl
  have hxi : ∀ i, |((drawO d n δ r0 R0 (coin ω.1) t).1 i : ℝ) - ((BB).path DB a0 ω).xi s i| ≤
      4 / 2 ^ ((CC).par.B / 2) := by
    intro i
    rw [hxe]
    exact (hbits.1 t ht).1 i
  have hXP := hP d K CC (kDel δ) (fun s => apAdv ((BB).adv (a0 + s) ω ((BB).mode DB (a0 + s) ω)))
    ((BB).path DB a0 ω) s st (drawO d n δ r0 R0 (coin ω.1) t).1 hd hn rfl hc hbud hq
    (by show s < n; omega) hdet htau htr hxi
  have hg0' := (hdet.evG s (by rw [htau])).2.1
  generalize hso : ((BB).ctx DB a0 ω).st ((BB).path DB a0 ω) s = so at hmo
  rw [hts] at hmo
  have hXeq : (ctxO K CC (kDel δ) (fun s => apAdv ((BB).adv (a0 + s) ω ((BB).mode DB (a0 + s) ω)))).X
      ((BB).path DB a0 ω) s = XS := by
    show (((BB).ctx DB a0 ω).st ((BB).path DB a0 ω) s).mu + (1 - (df2oPar d n DB).lam) •
      ((((BB).ctx DB a0 ω).st ((BB).path DB a0 ω) s).A *ᵥ ((BB).path DB a0 ω).xi s) = _
    rw [hso, hxe]
  have hX : ‖toE XQ - WithLp.toLp 2 XS‖ ≤ BudK.Xb d n (kDel δ) := by
    have e : toE XQ = WithLp.toLp 2 (cV XQ) := rfl
    rw [e, ← WithLp.toLp_sub, ← LeanAp.oNorm_eq, ← hXeq]
    exact hXP
  have hg0 : gauge KT (WithLp.toLp 2 XS) ≤ Real.sqrt (df2oPar d n DB).Le := by
    rw [← hXeq]
    exact hg0'
  -- the record's shift and plays
  obtain ⟨hrp, -⟩ := RunW.refPlay_run _ hI.convex hq heps0 heps1 hmo
  have hsh := shR_runO hI hc h hq ht hmo hW
  have hpl : (BB).play t ω = pgMu ((BB).pos ω) + pgOp ((BB).pos ω) (PT1⁻¹ • toE XQ) := by
    show toE (playO d n δ r0 R0 a WW t) = _
    have e : playO d n δ r0 R0 a WW t = playPtO orc CC (.run st) (drawO d n δ r0 R0 (coin ω.1) t).1 := by
      unfold playO
      rw [hW]
      rfl
    rw [e]
    exact playPtO_run orc CC st _
  have hL1 : (BB).loss ω t ((BB).play t ω) = (FF) (PT1⁻¹ • toE XQ) := (congrArg ((BB).loss ω t) hpl).trans rfl
  have hL0 : (BB).loss ω t ((BB).refPlay DB t ω) = (FF) (PTO⁻¹ • WithLp.toLp 2 XS) :=
    (congrArg ((BB).loss ω t) hrp).trans rfl
  rw [hsh, hL1, hL0]
  -- the body and the loss on it
  have H := rowHyp_of d n DB hd hn (deltaO_pos d n _ hd hn) (deltaO_lt_one d n _ hd hn) (hc.trans (by norm_num))
  have hR1 : 1 ≤ (df2oPar d n DB).R := row_one_le_R _ d n H
  have hmw : 1 / (df2oPar d n DB).R ≤ df2Mw d := by rw [H.R]; exact inv_R_le_df2Mw d hd
  have hLe0 : 0 ≤ (df2oPar d n DB).Le := by have := H.L504; linarith
  have hbody : Df2Body d (df2oPar d n DB).R KT := body_kTh hI.compact.isClosed hI.convex hR1 hmw _
  obtain ⟨hconv, hclosed, h1, hRb, -⟩ := id hbody
  have hq' : PgGood d K (df2oPar d n DB).R (some ((BB).pos ω)) := hq
  have hf : AdmLoss K ((BB).loss ω t) := (BB).F.adm t ht _
  set F : E d → ℝ := FF with hF
  have hFa : AdmLoss KT F := by
    have hbg := body_good hI.compact.isClosed hI.convex hq'
    rw [kTh_good hq']
    refine ⟨⟨hbg.1, fun x hx y hy a' b' ha hb hab => ?_⟩, fun x hx => hf.2 _ hx.1⟩
    have := hf.1.2 hx.1 hy.1 ha hb hab
    simp only [smul_eq_mul] at this ⊢
    simp only [hF]
    rw [affine_comb _ x y a' b' hab]
    exact this
  have hlip : ∀ x y : E d, (1 - EP)⁻¹ • x ∈ KT → (1 - EP)⁻¹ • y ∈ KT → F y - F x ≤ ‖y - x‖ / EP :=
    fun x y hx hy => PropG.convex_lip_eps KT hconv h1 F hFa.1 hFa.2 _ heps0 heps1 x y hx hy
  have hconvF2 : ConvexOn ℝ KT (fun y => F y / 2) := by
    refine (hFa.1.smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)).congr fun y _ => ?_
    simp only [smul_eq_mul]; ring
  have hF2 : AdmLoss KT (fun y => F y / 2) :=
    ⟨hconvF2, fun x hx => ⟨by linarith [(hFa.2 x hx).1], by linarith [(hFa.2 x hx).2]⟩⟩
  have hSI := (SIF.df2SIFacts_holds d n DB KT (fun y => F y / 2) hd hn (deltaO_pos d n _ hd hn)
    (deltaO_lt_one d n _ hd hn) (hc.trans (by norm_num)) hbody hF2).1.2.2.1
  have hext : ∀ x y : E d, |extE KT EP F x - extE KT EP F y| ≤ 8 / EP * ‖x - y‖ := by
    intro x y
    have e : ∀ z, df2Ext (df2oPar d n DB) KT (fun y => F y / 2) z = extE KT EP F z := by
      intro z; unfold df2Ext df2Pip extE ptE; ring
    have := hSI x y
    rwa [e, e] at this
  -- the gauge band
  have hRint : ((CC).par.R : ℝ) ≤ (CC).par.Rint := by
    have := Nat.le_ceil (parK d n (kDel δ)).R
    show (((parK d n (kDel δ)).R : ℚ) : ℝ) ≤ ((⌈(parK d n (kDel δ)).R⌉₊ : ℕ) : ℝ)
    exact_mod_cast this
  have hGB := gaugeBandO d K orc CC (poK d n (kDel δ)).R XQ hd (frameW hI _) (goodPos_of_pg hq) hR1
    hbud.enc.R_le hRint
  have hKb : KT = bodyS K CC := kTh_eq_bodyS (c := CC) hq
  rw [← hKb] at hGB
  have hPT1 : PT1 = max 1 ((gaugeP orc CC XQ : ℝ) / (1 - EQ)) := by
    show ((max 1 (gaugeP orc CC XQ / (1 - (CC).par.eps)) : ℚ) : ℝ) = _
    push_cast
    rfl
  -- the vocabulary of Theorem BUD
  have eEP : BudK.eps d n (kDel δ) = EP := rfl
  have eR : BudK.R d n (kDel δ) = (df2oPar d n DB).R := rfl
  have epib : BudK.pib d n (kDel δ) = Real.sqrt (df2oPar d n DB).Le + 1 / 8 := rfl
  have egb : BudK.gb d n (kDel δ) = BudK.tp d n (kDel δ) / 2 * BudK.pib d n (kDel δ) := rfl
  have ewe : BudK.we d n (kDel δ) = BudK.tp d n (kDel δ) / 16 * EP := rfl
  have empar : BudK.mpar d n (kDel δ) =
      BudK.tp d n (kDel δ) / 4 * BudK.pib d n (kDel δ) * ((df2oPar d n DB).R + 10) / EP := rfl
  have eS : BudK.S d n (kDel δ) = (2 + 16 / EP) * BudK.Xb d n (kDel δ) + BudK.mpar d n (kDel δ) := rfl
  have eband : BudK.band d n (kDel δ) = BudK.gb d n (kDel δ) *
      (2 + ((df2oPar d n DB).R * BudK.pib d n (kDel δ) + 4) / EP) := rfl
  have ekap : BudK.kapO d n (kDel δ) = 2 * (BudK.S d n (kDel δ) + BudK.band d n (kDel δ)) := rfl
  have ereg : BudK.regO d n (kDel δ) = n / EP * ((1 + 2 * (df2oPar d n DB).R) * BudK.Xb d n (kDel δ) +
      4 * (df2oPar d n DB).R * BudK.pib d n (kDel δ) * BudK.we d n (kDel δ) +
      (df2oPar d n DB).R * BudK.gb d n (kDel δ)) := rfl
  have etp : 2 * (2 : ℝ)⁻¹ ^ ((CC).par.p + 2) = BudK.tp d n (kDel δ) / 2 := by
    have e2 : BudK.tp d n (kDel δ) = 1 / 2 ^ (CC).par.p := rfl
    rw [e2]
    generalize (CC).par.p = P
    rw [pow_add, inv_pow]
    field_simp
  have hee' : EP ≤ EQ := hee
  have he'' : EQ ≤ 1 / 2 := he'
  have hwe' : EQ - EP ≤ BudK.we d n (kDel δ) := hwe
  have hpibd := epib
  have hLe17 : (17467 : ℝ) ≤ (df2oPar d n DB).Le := hbud.Le_ge
  have hpib1 : 1 ≤ BudK.pib d n (kDel δ) := by
    rw [epib]
    have : (1 : ℝ) ≤ Real.sqrt (df2oPar d n DB).Le := by
      rw [Real.one_le_sqrt]; linarith
    linarith
  have hR0 : 0 ≤ (df2oPar d n DB).R := by linarith
  have htp0 : 0 ≤ BudK.tp d n (kDel δ) := by unfold BudK.tp; positivity
  have hXb := hbud.Xb_le
  -- `π(X') ≤ π̄`
  have hgX : gauge KT (toE XQ) ≤ BudK.pib d n (kDel δ) := by
    have hl := Bit.BLP.EngL.gauge_lip1 KT hconv h1 (toE XQ) (WithLp.toLp 2 XS)
    rw [epib]
    have := (abs_le.1 hl).2
    linarith
  -- the scale `pt'` against `pt_{ε'}(X')`
  have hη : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ ((CC).par.p + 2) := by positivity
  have hΔ : |PT1 - ptE KT EQ (toE XQ)| ≤ BudK.gb d n (kDel δ) := by
    rw [hPT1, egb, ← etp]
    have := pt_band (gauge KT (toE XQ)) (gaugeP orc CC XQ : ℝ) EQ _ _ (gauge_nonneg _) hGB.1 hGB.2 hη he'' hgX
    rw [mul_assoc] at this ⊢
    exact this
  have hPT1g : gauge KT (toE XQ) / (1 - EQ) ≤ PT1 := by
    rw [hPT1]
    refine le_trans ?_ (le_max_right _ _)
    exact div_le_div_of_nonneg_right hGB.1 (by linarith)
  have hPT11 : 1 ≤ PT1 := by rw [hPT1]; exact le_max_left _ _
  obtain ⟨hb1, hb2⟩ := band_pt KT hconv hclosed h1 _ hRb F hFa.2 EP EQ heps0 hee' he'' hlip (toE XQ) PT1 hPT11
    hPT1g
  -- v2.1's bound at the scale `pt_{ε'}(X')`
  have h0 := Bit.BLP.EngL.ext_lip_shift KT hconv hclosed h1 _ hRb F hFa.2 EP EQ heps0 hee' he'' hlip hext
    (df2oPar d n DB).Le (BudK.Xb d n (kDel δ)) hLe0 hXb (toE XQ) (WithLp.toLp 2 XS) hg0 hX
  have hmp := Bit.BLP.EngL.mpar_le (BudK.pib d n (kDel δ)) (df2oPar d n DB).R EP (EQ - EP) (BudK.tp d n (kDel δ))
    (by linarith) hR0 heps0 (by linarith) (by linarith) (by rw [← ewe]; exact hwe')
  rw [← hpibd] at h0
  have hpto : 1 ≤ PTO := le_max_left _ _
  have hsb := shift_band PT1 (ptE KT EQ (toE XQ)) PTO
    (PT1 * F (PT1⁻¹ • toE XQ) / 2 + 2 * (PT1 - 1) / EQ) (extE KT EQ F (toE XQ)) (extE KT EP F (WithLp.toLp 2 XS))
    (1 / 2 + ((df2oPar d n DB).R / 2 + 2) / EP) _ hpto h0 hb2
  have hS0 : (2 + 16 / EP) * BudK.Xb d n (kDel δ) +
      (4 * BudK.pib d n (kDel δ) * (EQ - EP) +
        2 * BudK.pib d n (kDel δ) * ((df2oPar d n DB).R + 9) * (EQ - EP) / EP ^ 2) ≤ BudK.S d n (kDel δ) := by
    rw [eS, empar]
    linarith
  have htot := shift_total _ _ _ _ _ _ _ _ hsb hS0 (abs_nonneg _) hΔ hR0 hpib1 heps0
  rw [← eband] at htot
  have hSl := hbud.S_le
  obtain ⟨hr, htv⟩ := tv_noise (PT1 / PTO) ((WE).nz t ω)
    (2 * ((PT1 * F (PT1⁻¹ • toE XQ) / 2 + 2 * (PT1 - 1) / EQ) - extE KT EP F (WithLp.toLp 2 XS)) / PTO)
    (BudK.S d n (kDel δ) + BudK.band d n (kDel δ)) htot hSl
  refine ⟨⟨hr, ?_⟩, ?_⟩
  · rw [ekap]
    exact htv
  · have hgap := Bit.BLP.EngL.play_gap KT hconv hclosed h1 _ hRb F EP EQ heps0 hee' he'' hlip
      (df2oPar d n DB).Le (BudK.Xb d n (kDel δ)) hLe0 hXb (toE XQ) (WithLp.toLp 2 XS) hg0 hX
    rw [← hpibd] at hgap
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [ereg]
    exact regret_total _ _ _ _ _ _ _ _ _ _ _ _ hgap hb1 hwe' hΔ hR0 (by linarith) heps0 hn0

theorem roundBndO (hP : PlayCO) : RoundBndO := by
  intro d n δ r0 R0 a K orc hI hc Ω _ μ coin loss noise h ω hq hG hbits t ht hInv
  exact round_bndO hP hI hc h hq hG hbits ht hInv

end Rec

end AdversarialBco.Unified.Eng
