/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.BLOParam
public import AdversarialBco.Unified.SepMath
public import AdversarialBco.Bit.PieceA.Enc

@[expose] public section

/-!
# BL-O: the CM test in a position, the cross check, the gauge play

The facts of BL-O that need only the pure function (Unified/BLOSpec.lean) and the geometry of a good position:

* `testCertO : TestCertO` (UNI-CM in a position, route Sec. 3.1): the band `6·2^{-k} Rg R0/r0²`, from the bound
  `|A⁻¹| ≤ Rg/r0` of a good position (`preimage_bound`, `ball_transfer`) and UNI-CM (c) (`uni_cm_deep`);
* `crossOKO : CrossOKO` (route Sec. 3.2): the cross check passes in a good position at a radius `Rg ≤ R'`;
* `gaugeBandO : GaugeBandO` (UNI-GAUGE (b) for the play): the gauge play within `2^{-p-2}` of the gauge;
* `playIntO : PlayIntO` (UNI-CM, UNI-GAUGE (a)): every play is interior, on every world, good position or not
  (mode `run` only after the cross check, whose `2d` accepted points span the cross-polytope of the bisection's
  upper end).
-/

namespace AdversarialBco.Unified.BLO

open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.LeanAp AdversarialBco.Uni AdversarialBco.Bit.RQ
open AdversarialBco.Bit.BLP (Par St Mode lnQ lnErr sqrtDn up)
open AdversarialBco.BitRAM (toE)
open AdversarialBco.BitRAMO (WeakMemOracle)
open Metric Matrix

variable {d : ℕ}

/-! ## The geometry of a good position -/

section Geom

variable {K : Set (E d)} {μ : E d} {A : E d →L[ℝ] E d}

theorem convex_posBodyO (hK : Convex ℝ K) (μ : E d) (A : E d →L[ℝ] E d) : Convex ℝ (posBody K μ A) := by
  intro x hx y hy a b ha hb hab
  show μ + A (a • x + b • y) ∈ K
  have h : a • (μ + A x) + b • (μ + A y) = μ + A (a • x + b • y) := by
    rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul, map_add, map_smul, map_smul]
  rw [← h]
  exact hK hx hy ha hb hab

/-- In a position whose body holds `0` and lies in `B̄(0, Rg)`, of a `K` holding `B̄(a, r0)`, the operator is onto and
`|A⁻¹ w| ≤ (Rg/r0)|w|`. -/
theorem preimage_bound {a : E d} {r0 Rg : ℝ} (hr0 : 0 < r0) (hball : closedBall a r0 ⊆ K)
    (h0 : (0 : E d) ∈ posBody K μ A) (hR : posBody K μ A ⊆ closedBall 0 Rg) (w : E d) :
    ∃ v, A v = w ∧ ‖v‖ ≤ Rg / r0 * ‖w‖ := by
  have hRg : 0 ≤ Rg := by
    have := hR h0
    rwa [mem_closedBall, dist_self] at this
  have hinj : Function.Injective A := by
    refine (injective_iff_map_eq_zero A).2 fun v hv => ?_
    by_contra hv0
    have hn : 0 < ‖v‖ := norm_pos_iff.2 hv0
    have hmem : ((Rg + 1) / ‖v‖) • v ∈ posBody K μ A := by
      show μ + A _ ∈ K
      have e : μ + A (((Rg + 1) / ‖v‖) • v) = μ + A 0 := by rw [map_smul, hv, smul_zero, map_zero]
      rw [e]
      exact h0
    have h1 := hR hmem
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
      div_mul_cancel₀ _ hn.ne'] at h1
    linarith
  have hsurj : Function.Surjective A :=
    (LinearMap.injective_iff_surjective (f := (A : E d →ₗ[ℝ] E d))).1 hinj
  by_cases hw : w = 0
  · exact ⟨0, by rw [map_zero, hw], by rw [norm_zero, hw, norm_zero, mul_zero]⟩
  obtain ⟨v, hv⟩ := hsurj w
  refine ⟨v, hv, ?_⟩
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have ht0 : 0 < r0 / ‖w‖ := div_pos hr0 hwn
  have htw : ‖(r0 / ‖w‖) • w‖ = r0 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, div_mul_cancel₀ _ hwn.ne']
  obtain ⟨qp, hqp⟩ := hsurj (a + (r0 / ‖w‖) • w - μ)
  obtain ⟨qm, hqm⟩ := hsurj (a - (r0 / ‖w‖) • w - μ)
  have hp : qp ∈ posBody K μ A := by
    show μ + A qp ∈ K
    have e : μ + A qp = a + (r0 / ‖w‖) • w := by rw [hqp]; abel
    rw [e]
    apply hball
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, htw]
  have hm : qm ∈ posBody K μ A := by
    show μ + A qm ∈ K
    have e : μ + A qm = a - (r0 / ‖w‖) • w := by rw [hqm]; abel
    rw [e]
    apply hball
    rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, htw]
  have hdiff : qp - qm = (2 * (r0 / ‖w‖)) • v := by
    apply hinj
    rw [map_sub, hqp, hqm, map_smul, hv]
    module
  have hb : ‖qp - qm‖ ≤ 2 * Rg := by
    have h1 := hR hp
    have h2 := hR hm
    rw [mem_closedBall, dist_zero_right] at h1 h2
    calc ‖qp - qm‖ ≤ ‖qp‖ + ‖qm‖ := norm_sub_le _ _
      _ ≤ 2 * Rg := by linarith
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at hb
  have h3 : r0 / ‖w‖ * ‖v‖ ≤ Rg := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hwn] at h3
  rw [div_mul_eq_mul_div, le_div_iff₀ hr0]
  linarith

/-- A ball of radius `ρ` in the body maps to a ball of radius `ρ r0/Rg` in `K`. -/
theorem ball_transfer {a : E d} {r0 Rg ρ : ℝ} (hr0 : 0 < r0) (hRg : 0 < Rg) (hball : closedBall a r0 ⊆ K)
    (h0 : (0 : E d) ∈ posBody K μ A) (hR : posBody K μ A ⊆ closedBall 0 Rg) {z : E d}
    (hz : closedBall z ρ ⊆ posBody K μ A) : closedBall (μ + A z) (ρ * r0 / Rg) ⊆ K := by
  intro x hx
  obtain ⟨v, hv, hvn⟩ := preimage_bound hr0 hball h0 hR (x - (μ + A z))
  have hvz : z + v ∈ posBody K μ A := by
    apply hz
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    rw [mem_closedBall, dist_eq_norm] at hx
    calc ‖v‖ ≤ Rg / r0 * ‖x - (μ + A z)‖ := hvn
      _ ≤ Rg / r0 * (ρ * r0 / Rg) := mul_le_mul_of_nonneg_left hx (by positivity)
      _ = ρ := by field_simp
  have e : μ + A (z + v) = x := by rw [map_add, hv]; abel
  rw [← e]
  exact hvz

/-- The gauge margin: a convex body holding `B̄(0, 1)`, a point of gauge `< 1 - ρ` has the ball `B̄(z, ρ)` inside. -/
theorem ball_of_sInf {Kb : Set (E d)} (hKb : Convex ℝ Kb) (h1 : closedBall (0 : E d) 1 ⊆ Kb) {z : E d} {ρ : ℝ}
    (hlt : sInf {t : ℝ | 0 < t ∧ t⁻¹ • z ∈ Kb} < 1 - ρ) : closedBall z ρ ⊆ Kb := by
  have hne : {t : ℝ | 0 < t ∧ t⁻¹ • z ∈ Kb}.Nonempty := by
    refine ⟨‖z‖ + 1, by positivity, h1 ?_⟩
    rw [mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < ‖z‖ + 1), inv_mul_le_iff₀ (by positivity)]
    linarith
  obtain ⟨t, ⟨ht0, htz⟩, htlt⟩ := exists_lt_of_csInf_lt hne hlt
  intro w hw
  have h1t : 0 < 1 - t := by
    rw [mem_closedBall] at hw
    linarith [dist_nonneg (x := w) (y := z)]
  have hu : (1 - t)⁻¹ • (w - z) ∈ Kb := by
    apply h1
    rw [mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos h1t,
      inv_mul_le_iff₀ h1t]
    rw [mem_closedBall, dist_eq_norm] at hw
    linarith
  have hcomb : t • (t⁻¹ • z) + (1 - t) • ((1 - t)⁻¹ • (w - z)) = w := by
    rw [smul_smul, smul_smul, mul_inv_cancel₀ ht0.ne', mul_inv_cancel₀ h1t.ne', one_smul, one_smul]
    abel
  rw [← hcomb]
  exact hKb htz hu ht0.le h1t.le (by ring)

end Geom

/-! ## The CM test in a position -/

theorem toE_cmPt (a : Fin d → ℚ) (r0 : ℚ) (k : ℕ) (y : Fin d → ℚ) :
    toE (cmPt a r0 k y) = toE a + (1 + 2 * (2 : ℝ)⁻¹ ^ k / r0) • (toE y - toE a) := by
  simp only [toE]
  rw [← WithLp.toLp_sub, ← WithLp.toLp_smul, ← WithLp.toLp_add]
  congr 1
  funext i
  simp only [cmPt, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  push_cast
  ring

/-- The real affine map of a position: `y ↦ μ_S + A_S y`. -/
noncomputable def affO (c : CfgO d) (y : Fin d → ℝ) : E d := pgMu c.S + pgOp c.S (WithLp.toLp 2 y)

/-- The point asked by the test `T k s` at `y` is `μ_S + A_S (s y)`. -/
theorem toE_pos (c : CfgO d) (s : ℚ) (y : Fin d → ℚ) :
    toE (c.μS + c.AS *ᵥ (s • y)) = affO c ((s : ℝ) • qR y) := by
  rw [affO, pgOp_apply]
  simp only [CfgO.S, castP, pgMu_pgPack, pgMat_pgPack, toE]
  rw [← WithLp.toLp_add]
  congr 1
  funext i
  simp only [Pi.add_apply, mulVec, dotProduct, Bit.BLP.cM, Matrix.map_apply, Pi.smul_apply, smul_eq_mul, qR,
    WithLp.ofLp_toLp]
  push_cast
  rfl

theorem affO_combo (c : CfgO d) (y1 y2 : Fin d → ℝ) (a b : ℝ) (hab : a + b = 1) :
    affO c (a • y1 + b • y2) = a • affO c y1 + b • affO c y2 := by
  simp only [affO, WithLp.toLp_add, WithLp.toLp_smul, map_add, map_smul]
  rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul]

theorem convex_affO {S : Set (E d)} (hS : Convex ℝ S) (c : CfgO d) : Convex ℝ {y | affO c y ∈ S} := by
  intro x hx y hy a b ha hb hab
  show affO c (a • x + b • y) ∈ S
  rw [affO_combo c x y a b hab]
  exact hS hx hy ha hb hab

theorem oGauge_QKs (K : Set (E d)) (c : CfgO d) (s : ℚ) (x : Fin d → ℝ) :
    oGauge (QKs K c s) 0 x = sInf {t : ℝ | 0 < t ∧ t⁻¹ • WithLp.toLp 2 ((s : ℝ) • x) ∈ bodyS K c} := by
  have e : ∀ t : ℝ, WithLp.toLp 2 ((s : ℝ) • (t⁻¹ • x)) = t⁻¹ • WithLp.toLp 2 ((s : ℝ) • x) := fun t => by
    rw [smul_comm, WithLp.toLp_smul]
  unfold oGauge
  congr 1
  ext t
  simp only [Set.mem_setOf_eq, zero_add, sub_zero, QKs, e]

theorem testCertO : TestCertO := by
  intro d K orc c Rg k s hF hG hRg hs y
  obtain ⟨hK, -, hr0, hrR, hball, hKR, horc⟩ := hF
  obtain ⟨hB1, hBR⟩ := hG
  have hr0' : (0 : ℝ) < c.r0 := by exact_mod_cast hr0
  have hrR' : (c.r0 : ℝ) ≤ c.R0 := by exact_mod_cast hrR
  have hR0 : (0 : ℝ) < c.R0 := lt_of_lt_of_le hr0' hrR'
  have hRg0 : (0 : ℝ) < Rg := by linarith
  have h0 : (0 : E d) ∈ bodyS K c := hB1 (mem_closedBall_self zero_le_one)
  have hq := toE_cmPt c.a c.r0 k (c.μS + c.AS *ᵥ (s • y))
  have hY := toE_pos c s y
  obtain ⟨hacc, -⟩ := uni_cm_weakMem K hK (toE c.a) (toE (c.μS + c.AS *ᵥ (s • y))) c.r0 hr0' hball orc horc
    (cmPt c.a c.r0 k (c.μS + c.AS *ᵥ (s • y))) k hq
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hin := interior_subset (hacc h)
    rw [hY] at hin
    exact hin
  · rw [oGauge_QKs]
    by_contra hle
    push_neg at hle
    have hε : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
    have hη : 0 < 6 * (2 : ℝ)⁻¹ ^ k * Rg * c.R0 / c.r0 ^ 2 := by positivity
    have hsub : closedBall (WithLp.toLp 2 ((s : ℝ) • qR y)) (6 * (2 : ℝ)⁻¹ ^ k * Rg * c.R0 / c.r0 ^ 2 / 2) ⊆
        bodyS K c :=
      ball_of_sInf (Kb := bodyS K c) (convex_posBodyO hK _ _) hB1 (by linarith)
    have hKsub := ball_transfer hr0' hRg0 hball h0 hBR hsub
    have hY' : pgMu c.S + pgOp c.S (WithLp.toLp 2 ((s : ℝ) • qR y)) = toE (c.μS + c.AS *ᵥ (s • y)) := by
      rw [hY]; rfl
    rw [hY'] at hKsub
    have hYK : toE (c.μS + c.AS *ᵥ (s • y)) ∈ K := hKsub (mem_closedBall_self (by positivity))
    have hdist : dist (toE (c.μS + c.AS *ᵥ (s • y))) (toE c.a) ≤ c.R0 := by
      have := hKR hYK
      rwa [mem_closedBall] at this
    have hρ : (2 : ℝ)⁻¹ ^ k + 2 * (2 : ℝ)⁻¹ ^ k * c.R0 / c.r0 ≤
        6 * (2 : ℝ)⁻¹ ^ k * Rg * c.R0 / c.r0 ^ 2 / 2 * c.r0 / Rg := by
      have e1 : 6 * (2 : ℝ)⁻¹ ^ k * Rg * c.R0 / c.r0 ^ 2 / 2 * c.r0 / Rg = 3 * (2 : ℝ)⁻¹ ^ k * c.R0 / c.r0 := by
        field_simp
        ring
      rw [e1]
      have h2 : (2 : ℝ)⁻¹ ^ k ≤ (2 : ℝ)⁻¹ ^ k * c.R0 / c.r0 := by
        rw [le_div_iff₀ hr0']
        nlinarith
      have e2 : 3 * (2 : ℝ)⁻¹ ^ k * c.R0 / c.r0 = (2 : ℝ)⁻¹ ^ k * c.R0 / c.r0 + 2 * (2 : ℝ)⁻¹ ^ k * c.R0 / c.r0 := by
        ring
      linarith
    have hdeep := uni_cm_deep K (toE c.a) (toE (c.μS + c.AS *ᵥ (s • y))) c.r0 c.R0 ((2 : ℝ)⁻¹ ^ k) _ hr0'
      hε.le hKsub hdist hρ
    rw [← hq] at hdeep
    exact (horc (cmPt c.a c.r0 k (c.μS + c.AS *ᵥ (s • y))) k).2 h hdeep

/-! ## The precision of the cross check and of the play -/

theorem kK_spec (c : CfgO d) : (6 * c.par.R * c.R0 / c.r0 ^ 2 : ℝ) ≤ 2 ^ c.kK := by
  have h1 : ((6 * c.par.R * c.R0 / c.r0 ^ 2 : ℚ) : ℝ) ≤ ((⌈6 * c.par.R * c.R0 / c.r0 ^ 2⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_ceil _
  have h2 : ⌈6 * c.par.R * c.R0 / c.r0 ^ 2⌉₊ ≤ 2 ^ c.kK := Nat.le_pow_clog (by norm_num) _
  push_cast at h1
  calc _ ≤ _ := h1
    _ ≤ _ := by exact_mod_cast h2

/-- The band of the test at a precision `k ≥ kK` and a radius `Rg ≤ R'`: at most `2^{-(k - kK)}`. -/
theorem band_le (c : CfgO d) (k : ℕ) (hk : c.kK ≤ k) (Rg : ℝ) (hRgR : Rg ≤ c.par.R)
    (hr0 : (0 : ℝ) < c.r0) (hR0 : (0 : ℝ) ≤ c.R0) :
    6 * (2 : ℝ)⁻¹ ^ k * Rg * c.R0 / c.r0 ^ 2 ≤ (2 : ℝ)⁻¹ ^ (k - c.kK) := by
  have hK := kK_spec c
  have e : (2 : ℝ)⁻¹ ^ k = (2 : ℝ)⁻¹ ^ (k - c.kK) * (2 : ℝ)⁻¹ ^ c.kK := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  have h1 : 6 * Rg * c.R0 / c.r0 ^ 2 ≤ 6 * c.par.R * c.R0 / c.r0 ^ 2 := by gcongr
  have h2 : (2 : ℝ)⁻¹ ^ c.kK * 2 ^ c.kK = 1 := by rw [← mul_pow]; norm_num
  calc 6 * (2 : ℝ)⁻¹ ^ k * Rg * c.R0 / c.r0 ^ 2 =
        (2 : ℝ)⁻¹ ^ (k - c.kK) * ((2 : ℝ)⁻¹ ^ c.kK * (6 * Rg * c.R0 / c.r0 ^ 2)) := by rw [e]; ring
    _ ≤ (2 : ℝ)⁻¹ ^ (k - c.kK) * ((2 : ℝ)⁻¹ ^ c.kK * 2 ^ c.kK) := by
        gcongr
        exact h1.trans hK
    _ = _ := by rw [h2, mul_one]

theorem kC_sub (c : CfgO d) : c.kC - c.kK = c.par.p + 4 := by
  unfold CfgO.kC
  omega

/-! ## The cross check -/

theorem qR_single (i : Fin d) (σ : ℚ) : qR (Pi.single i σ) = Pi.single i (σ : ℝ) := by
  funext j
  by_cases h : j = i
  · subst h; simp [qR]
  · simp [qR, Pi.single_apply, h]

theorem norm_single_le (i : Fin d) (σ : ℝ) : ‖(WithLp.toLp 2 (Pi.single i σ) : E d)‖ = |σ| := by
  have := EuclideanSpace.norm_single (𝕜 := ℝ) i σ
  rw [Real.norm_eq_abs] at this
  exact this

/-- UNI-CM (c) for the test: a point whose query ball fits in `K` is accepted. -/
theorem T_true_of_ball {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d} (hr0 : (0 : ℝ) < c.r0)
    (hKR : K ⊆ closedBall (toE c.a) (c.R0 : ℝ)) (horc : WeakMemOracle K orc) (k : ℕ) (s : ℚ) (y : Fin d → ℚ)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hsub : closedBall (affO c ((s : ℝ) • qR y)) ρ ⊆ K)
    (hρ : (2 : ℝ)⁻¹ ^ k + 2 * (2 : ℝ)⁻¹ ^ k * c.R0 / c.r0 ≤ ρ) : c.T orc k s y = true := by
  rw [← toE_pos] at hsub
  have hYK := hsub (mem_closedBall_self hρ0)
  have hdist : dist (toE (c.μS + c.AS *ᵥ (s • y))) (toE c.a) ≤ c.R0 := by
    have := hKR hYK
    rwa [mem_closedBall] at this
  have hdeep := uni_cm_deep K (toE c.a) (toE (c.μS + c.AS *ᵥ (s • y))) c.r0 c.R0 ((2 : ℝ)⁻¹ ^ k) ρ hr0
    (by positivity) hsub hdist hρ
  rw [← toE_cmPt] at hdeep
  cases hT : c.T orc k s y
  · exact absurd hdeep ((horc _ k).2 hT)
  · rfl

theorem crossOKO : CrossOKO := by
  intro d K orc c Rg hF hG hRg hRgR i
  obtain ⟨-, -, hr0, hrR, hball, hKR, horc⟩ := hF
  obtain ⟨hB1, hBR⟩ := hG
  have hr0' : (0 : ℝ) < c.r0 := by exact_mod_cast hr0
  have hrR' : (c.r0 : ℝ) ≤ c.R0 := by exact_mod_cast hrR
  have hR0 : (0 : ℝ) < c.R0 := lt_of_lt_of_le hr0' hrR'
  have hRg0 : (0 : ℝ) < Rg := by linarith
  have h0 : (0 : E d) ∈ bodyS K c := hB1 (mem_closedBall_self zero_le_one)
  have hb := band_le c c.kC (by unfold CfgO.kC; omega) Rg hRgR hr0' hR0.le
  have hb1 : 6 * (2 : ℝ)⁻¹ ^ c.kC * Rg * c.R0 / c.r0 ^ 2 ≤ 1 :=
    hb.trans (pow_le_one₀ (by norm_num) (by norm_num))
  have hε : (0 : ℝ) < (2 : ℝ)⁻¹ ^ c.kC := by positivity
  have hρ : (2 : ℝ)⁻¹ ^ c.kC + 2 * (2 : ℝ)⁻¹ ^ c.kC * c.R0 / c.r0 ≤ 1 / 2 * c.r0 / Rg := by
    have h2 : (2 : ℝ)⁻¹ ^ c.kC ≤ (2 : ℝ)⁻¹ ^ c.kC * c.R0 / c.r0 := by
      rw [le_div_iff₀ hr0']
      nlinarith
    have e1 : 3 * (2 : ℝ)⁻¹ ^ c.kC * c.R0 / c.r0 =
        6 * (2 : ℝ)⁻¹ ^ c.kC * Rg * c.R0 / c.r0 ^ 2 * (1 / 2 * c.r0 / Rg) := by
      field_simp
      ring
    have h3 : 6 * (2 : ℝ)⁻¹ ^ c.kC * Rg * c.R0 / c.r0 ^ 2 * (1 / 2 * c.r0 / Rg) ≤ 1 * (1 / 2 * c.r0 / Rg) :=
      mul_le_mul_of_nonneg_right hb1 (by positivity)
    have e2 : 3 * (2 : ℝ)⁻¹ ^ c.kC * c.R0 / c.r0 =
        (2 : ℝ)⁻¹ ^ c.kC * c.R0 / c.r0 + 2 * (2 : ℝ)⁻¹ ^ c.kC * c.R0 / c.r0 := by ring
    linarith
  have key : ∀ σ : ℚ, |σ| = 1 / 2 → c.T orc c.kC 1 (Pi.single i σ) = true := by
    intro σ hσ
    have hz : ‖(WithLp.toLp 2 (((1 : ℚ) : ℝ) • qR (Pi.single i σ)) : E d)‖ = 1 / 2 := by
      rw [Rat.cast_one, one_smul, qR_single, norm_single_le, ← Rat.cast_abs, hσ]
      norm_num
    have hsub : closedBall (WithLp.toLp 2 (((1 : ℚ) : ℝ) • qR (Pi.single i σ)) : E d) (1 / 2) ⊆ bodyS K c := by
      intro x hx
      apply hB1
      rw [mem_closedBall, dist_eq_norm] at hx
      rw [mem_closedBall, dist_zero_right]
      calc ‖x‖ = ‖(x - WithLp.toLp 2 (((1 : ℚ) : ℝ) • qR (Pi.single i σ))) +
            WithLp.toLp 2 (((1 : ℚ) : ℝ) • qR (Pi.single i σ))‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
        _ ≤ 1 := by rw [hz]; linarith
    exact T_true_of_ball hr0' hKR horc c.kC 1 (Pi.single i σ) (1 / 2 * c.r0 / Rg) (by positivity)
      (ball_transfer hr0' hRg0 hball h0 hBR hsub) hρ
  exact ⟨key _ (by norm_num), key _ (by norm_num)⟩


/-! ## The gauge play -/

theorem norm_le_l1 (x : E d) : ‖x‖ ≤ ∑ i, |x i| := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (Finset.sum_nonneg fun i _ => abs_nonneg _)]
  have := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => |x i|) fun i _ => abs_nonneg _
  simpa [Real.norm_eq_abs, sq_abs] using this

theorem l1_le_card (x : E d) : ∑ i, |x i| ≤ d * ‖x‖ := by
  calc ∑ i, |x i| ≤ ∑ _i : Fin d, ‖x‖ := Finset.sum_le_sum fun i _ => by
        rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le x i
    _ = d * ‖x‖ := by simp

theorem toE_apply (X : Fin d → ℚ) (i : Fin d) : toE X i = (X i : ℝ) := rfl

theorem l1_cast (X : Fin d → ℚ) : ((l1 X : ℚ) : ℝ) = ∑ i, |toE X i| := by
  simp [l1, toE_apply]

theorem absorbent_of_ball {Kb : Set (E d)} (h1 : closedBall (0 : E d) 1 ⊆ Kb) : Absorbent ℝ Kb :=
  (absorbent_ball_zero one_pos).mono (ball_subset_closedBall.trans h1)

theorem oGauge_QKs_one (K : Set (E d)) (c : CfgO d) (X : Fin d → ℚ) :
    oGauge (QKs K c 1) (qR 0) (qR X) = gauge (bodyS K c) (toE X) := by
  have e0 : qR (0 : Fin d → ℚ) = 0 := by funext i; simp [qR]
  rw [e0, oGauge_QKs, gauge_def']
  congr 1
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_Ioi, Rat.cast_one, one_smul]
  rfl

theorem gaugeBandO : GaugeBandO := by
  intro d K orc c Rg X hd hF hG hRg hRgR hRint
  have hcert := testCertO d K orc c Rg c.kC 1 hF hG hRg one_pos
  obtain ⟨hK, -, hr0, hrR, hball, hKR, horc⟩ := hF
  obtain ⟨hB1, hBR⟩ := hG
  have hr0' : (0 : ℝ) < c.r0 := by exact_mod_cast hr0
  have hrR' : (c.r0 : ℝ) ≤ c.R0 := by exact_mod_cast hrR
  have hR0 : (0 : ℝ) < c.R0 := lt_of_lt_of_le hr0' hrR'
  have hRg0 : (0 : ℝ) < Rg := by linarith
  have habs := absorbent_of_ball hB1
  by_cases hX : X = 0
  · subst hX
    have e : toE (0 : Fin d → ℚ) = 0 := by ext i; simp [toE_apply]
    simp only [gaugeP, if_true, e, gauge_zero, Rat.cast_zero, mul_zero, le_refl, and_self]
  have hgP : gaugeP orc c X = gaugeQ (c.T orc c.kC 1) 0 X (2 * l1 X) c.jG := by rw [gaugeP, if_neg hX]
  set γ := gauge (bodyS K c) (toE X) with hγ
  have hγ0 : 0 ≤ γ := gauge_nonneg _
  have hNγ : ‖toE X‖ / Rg ≤ γ := le_gauge_of_subset_closedBall habs hRg0.le hBR
  have hγN : γ ≤ ‖toE X‖ := by
    have := gauge_mono (absorbent_of_ball (le_refl (closedBall (0 : E d) 1))) hB1 (toE X)
    rw [gauge_closedBall zero_le_one, div_one] at this
    exact this
  have hl1 : ‖toE X‖ ≤ ((l1 X : ℚ) : ℝ) := by rw [l1_cast]; exact norm_le_l1 _
  have hl1d : ((l1 X : ℚ) : ℝ) ≤ d * ‖toE X‖ := by rw [l1_cast]; exact l1_le_card _
  have hXn : 0 < ‖toE X‖ := by
    rw [norm_pos_iff]
    intro h
    apply hX
    funext i
    have := congrArg (fun v : E d => v i) h
    simpa [toE_apply] using this
  set η := 6 * (2 : ℝ)⁻¹ ^ c.kC * Rg * c.R0 / c.r0 ^ 2 with hηdef
  have hηu : η ≤ (2 : ℝ)⁻¹ ^ (c.par.p + 4) := by
    rw [← kC_sub c]
    exact band_le c c.kC (by unfold CfgO.kC; omega) Rg hRgR hr0' hR0.le
  have hη0 : 0 ≤ η := by positivity
  have hu16 : (2 : ℝ)⁻¹ ^ (c.par.p + 4) ≤ 1 / 16 := by
    calc (2 : ℝ)⁻¹ ^ (c.par.p + 4) = (2 : ℝ)⁻¹ ^ c.par.p * (1 / 16) := by rw [pow_add]; norm_num
      _ ≤ 1 * (1 / 16) := by gcongr; exact pow_le_one₀ (by norm_num) (by norm_num)
      _ = 1 / 16 := one_mul _
  have hu0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (c.par.p + 4) := by positivity
  have hη1 : η < 1 := by linarith
  have hH : (0 : ℚ) < 2 * l1 X := by
    have : (0 : ℝ) < ((2 * l1 X : ℚ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hcert' : TestCert (c.T orc c.kC 1) (QKs K c 1) (qR 0) η := by
    have e0 : qR (0 : Fin d → ℚ) = 0 := by funext i; simp [qR]
    rw [e0]
    exact hcert
  have hγH : oGauge (QKs K c 1) (qR 0) (qR X) ≤ ((2 * l1 X : ℚ) : ℝ) := by
    rw [oGauge_QKs_one]
    push_cast
    linarith
  obtain ⟨hlo, hhi⟩ := gaugeAcc d (c.T orc c.kC 1) (QKs K c 1) 0 X (2 * l1 X) c.jG η hη0 hη1 hcert' hH hγH
  rw [oGauge_QKs_one] at hlo hhi
  rw [hgP]
  refine ⟨hlo, hhi.trans ?_⟩
  -- the two error terms
  set u := (2 : ℝ)⁻¹ ^ (c.par.p + 4) with hudef
  have h1η : 0 < 1 - η := by linarith
  have hA : γ / (1 - η) ≤ γ * (1 + 2 * u) := by
    rw [div_le_iff₀ h1η]
    have h3 : 0 ≤ 2 * u - η - 2 * u * η := by nlinarith
    nlinarith [mul_nonneg hγ0 h3]
  have hjG : (2 : ℝ) ^ (c.par.p + 4) * (2 * d * Rg) ≤ 2 ^ c.jG := by
    have hc : ((2 * d * c.par.Rint : ℕ) : ℝ) ≤ ((2 ^ Nat.clog 2 (2 * d * c.par.Rint) : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_pow_clog (by norm_num) _
    push_cast at hc
    have hR : 2 * (d : ℝ) * Rg ≤ 2 * d * c.par.Rint := by
      have : Rg ≤ c.par.Rint := hRgR.trans hRint
      gcongr
    have e : (2 : ℝ) ^ c.jG = 2 ^ (c.par.p + 4) * 2 ^ Nat.clog 2 (2 * d * c.par.Rint) := by
      rw [← pow_add]; rfl
    rw [e]
    exact mul_le_mul_of_nonneg_left (hR.trans hc) (by positivity)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hB : ((2 * l1 X : ℚ) : ℝ) / 2 ^ c.jG ≤ γ * u := by
    have hnum : ((2 * l1 X : ℚ) : ℝ) ≤ 2 * d * ‖toE X‖ := by push_cast; linarith
    calc ((2 * l1 X : ℚ) : ℝ) / 2 ^ c.jG ≤ 2 * d * ‖toE X‖ / 2 ^ c.jG :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ 2 * d * ‖toE X‖ / ((2 : ℝ) ^ (c.par.p + 4) * (2 * d * Rg)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hjG
      _ = ‖toE X‖ / Rg * u := by
          rw [hudef, inv_pow]
          field_simp
      _ ≤ γ * u := mul_le_mul_of_nonneg_right hNγ hu0.le
  have hp2 : (2 : ℝ)⁻¹ ^ (c.par.p + 2) = 4 * u := by rw [hudef]; ring
  rw [hp2]
  nlinarith

/-! ## The plays are interior -/

section Interior

variable {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d}

theorem accept_int (hK : Convex ℝ K) (hr0 : (0 : ℝ) < c.r0) (hball : closedBall (toE c.a) (c.r0 : ℝ) ⊆ K)
    (horc : WeakMemOracle K orc) {k : ℕ} {s : ℚ} {y : Fin d → ℚ} (h : c.T orc k s y = true) :
    affO c ((s : ℝ) • qR y) ∈ interior K := by
  rw [← toE_pos]
  exact (uni_cm_weakMem K hK (toE c.a) _ c.r0 hr0 hball orc horc _ k (toE_cmPt _ _ _ _)).1 h

/-- The cross-polytope `|y|₁ ≤ 1/2` lies in a convex set holding `0` and the `2d` points `±e_i/2`. -/
theorem cross_mem {S : Set (Fin d → ℝ)} (hS : Convex ℝ S) (h0 : (0 : Fin d → ℝ) ∈ S)
    (hp : ∀ i, Pi.single i (1 / 2 : ℝ) ∈ S) (hm : ∀ i, Pi.single i (-1 / 2 : ℝ) ∈ S)
    (y : Fin d → ℝ) (hy : ∑ i, |y i| ≤ 1 / 2) : y ∈ S := by
  let w : Option (Fin d) → ℝ := fun o => o.elim (1 - 2 * ∑ i, |y i|) (fun i => 2 * |y i|)
  let z : Option (Fin d) → Fin d → ℝ := fun o =>
    o.elim 0 (fun i => if 0 ≤ y i then Pi.single i (1 / 2) else Pi.single i (-1 / 2))
  have hsum : ∑ o, w o = 1 := by
    rw [Fintype.sum_option]
    simp only [w, Option.elim, ← Finset.mul_sum]
    ring
  have hw : ∀ o ∈ Finset.univ, 0 ≤ w o := by
    intro o _
    cases o with
    | none => simp only [w, Option.elim]; linarith
    | some i => simp only [w, Option.elim]; positivity
  have hz : ∀ o ∈ Finset.univ, z o ∈ S := by
    intro o _
    cases o with
    | none => exact h0
    | some i =>
      simp only [z, Option.elim]
      split_ifs
      · exact hp i
      · exact hm i
  have hmem := hS.sum_mem hw hsum hz
  have key : ∀ i, (2 * |y i|) • (if 0 ≤ y i then Pi.single i (1 / 2 : ℝ) else Pi.single i (-1 / 2)) =
      Pi.single i (y i) := by
    intro i
    funext j
    by_cases hj : j = i
    · subst hj
      split_ifs with h
      · simp [abs_of_nonneg h]; ring
      · rw [not_le] at h
        simp [abs_of_neg h]; ring
    · split_ifs <;> simp [Pi.single_apply, hj]
  have e : ∑ o, w o • z o = y := by
    rw [Fintype.sum_option]
    simp only [w, z, Option.elim, smul_zero, zero_add]
    simp only [key]
    exact Finset.univ_sum_single y
  rwa [e] at hmem

/-- In mode `run` (cross check passed, `0 ≤ ε' ≤ 1/2`), the gauge play `μ_S + A_S (X'/pt')` is interior. -/
theorem play_int (hK : Convex ℝ K) (hd : 1 ≤ d) (hr0 : (0 : ℝ) < c.r0)
    (hball : closedBall (toE c.a) (c.r0 : ℝ) ⊆ K) (horc : WeakMemOracle K orc) (hcross : crossOK orc c)
    (heps0 : 0 ≤ c.par.eps) (heps : c.par.eps ≤ 1 / 2) (X : Fin d → ℚ) :
    toE (c.μS + c.AS *ᵥ ((ptO orc c X)⁻¹ • X)) ∈ interior K := by
  set S := {y : Fin d → ℝ | affO c y ∈ interior K} with hSdef
  have hS : Convex ℝ S := convex_affO hK.interior c
  have hp : ∀ i, Pi.single i (1 / 2 : ℝ) ∈ S := fun i => by
    have := accept_int hK hr0 hball horc (hcross i).1
    have e : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
    rw [Rat.cast_one, one_smul, qR_single, e] at this
    exact this
  have hm : ∀ i, Pi.single i (-1 / 2 : ℝ) ∈ S := fun i => by
    have := accept_int hK hr0 hball horc (hcross i).2
    have e : ((-1 / 2 : ℚ) : ℝ) = -1 / 2 := by norm_num
    rw [Rat.cast_one, one_smul, qR_single, e] at this
    exact this
  have h0 : (0 : Fin d → ℝ) ∈ S := by
    have := hS (hp ⟨0, hd⟩) (hm ⟨0, hd⟩) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    convert this using 1
    funext j
    by_cases hj : j = ⟨0, hd⟩
    · subst hj; simp; norm_num
    · simp [Pi.single_apply, hj]
  have hcp := cross_mem hS h0 hp hm
  rw [toE_pos]
  show ((((ptO orc c X)⁻¹ : ℚ) : ℝ) • qR X) ∈ S
  by_cases hX : X = 0
  · subst hX
    have e : qR (0 : Fin d → ℚ) = 0 := by funext i; simp [qR]
    rw [e, smul_zero]
    exact h0
  -- the bisection's value
  set H : ℚ := 2 * l1 X with hHdef
  have hl1 : 0 < l1 X := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hX
    have hi' : 0 < |X i| := abs_pos.2 hi
    calc 0 < |X i| := hi'
      _ ≤ l1 X := Finset.single_le_sum (f := fun i => |X i|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hH : 0 < H := by rw [hHdef]; linarith
  set u := (gaugeIt (c.T orc c.kC 1) 0 X H c.jG c.jG).2 with hudef
  have hu1 : 1 ≤ u := by
    have := (gaugeIt_inv (c.T orc c.kC 1) 0 X H c.jG c.jG le_rfl).1
    rw [Nat.sub_self, pow_zero] at this
    omega
  set πt := gaugeP orc c X with hπt
  have hπ : πt = H * u / 2 ^ c.jG := by rw [hπt, gaugeP, if_neg hX]; rfl
  have hπpos : 0 < πt := by
    rw [hπ]
    have : (0 : ℚ) < u := by exact_mod_cast hu1
    positivity
  have hπR : ((πt : ℚ) : ℝ) = (H : ℝ) * u / 2 ^ c.jG := by rw [hπ]; push_cast; ring
  -- the ray point `X'/π̃` is in `S`
  have hray : ((πt : ℚ) : ℝ)⁻¹ • qR X ∈ S := by
    rcases lt_or_ge u (2 ^ c.jG) with hlt | hge
    · have hT := gaugeCertEnd d (c.T orc c.kC 1) 0 X H c.jG hlt
      have := accept_int hK hr0 hball horc hT
      rw [Rat.cast_one, one_smul, qR_gaugePt] at this
      have e0 : qR (0 : Fin d → ℚ) = 0 := by funext i; simp [qR]
      rw [e0, zero_add, sub_zero] at this
      show affO c _ ∈ interior K
      rw [hπR, inv_div]
      exact this
    · apply hcp
      have hL : (0 : ℝ) ≤ ∑ i, |(X i : ℝ)| := Finset.sum_nonneg fun i _ => abs_nonneg _
      have hLH : (H : ℝ) = 2 * ∑ i, |(X i : ℝ)| := by rw [hHdef]; push_cast [l1]; rfl
      have hge' : (2 : ℝ) ^ c.jG ≤ u := by exact_mod_cast hge
      have hπge : (H : ℝ) ≤ (πt : ℝ) := by
        rw [hπR, le_div_iff₀ (by positivity)]
        have : (0 : ℝ) ≤ H := by exact_mod_cast hH.le
        nlinarith
      have hπR0 : (0 : ℝ) < (πt : ℝ) := by exact_mod_cast hπpos
      have e : ∑ i, |(((πt : ℚ) : ℝ)⁻¹ • qR X) i| = ((πt : ℚ) : ℝ)⁻¹ * ∑ i, |(X i : ℝ)| := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul, qR, abs_mul, abs_inv, abs_of_pos hπR0]
      rw [e, inv_mul_le_iff₀ hπR0]
      linarith
  -- the play `X'/pt'` on the segment from `0` to `X'/π̃`
  have h1e : (0 : ℚ) < 1 - c.par.eps := by linarith
  have hpt1 : 1 ≤ ptO orc c X := le_max_left _ _
  have hptπ : πt ≤ ptO orc c X := by
    refine le_trans ?_ (le_max_right _ _)
    rw [le_div_iff₀ h1e]
    nlinarith
  have hptR : (0 : ℝ) < ((ptO orc c X : ℚ) : ℝ) := by exact_mod_cast (lt_of_lt_of_le one_pos hpt1)
  have hπR0 : (0 : ℝ) < (πt : ℝ) := by exact_mod_cast hπpos
  have hθ1 : ((πt : ℚ) : ℝ) / ((ptO orc c X : ℚ) : ℝ) ≤ 1 := by
    rw [div_le_one hptR]
    exact_mod_cast hptπ
  have hθ0 : 0 ≤ ((πt : ℚ) : ℝ) / ((ptO orc c X : ℚ) : ℝ) := by positivity
  have hθ1' : (0 : ℝ) ≤ 1 - ((πt : ℚ) : ℝ) / ((ptO orc c X : ℚ) : ℝ) := by linarith
  have hcomb := hS hray h0 hθ0 hθ1' (by ring)
  convert hcomb using 1
  rw [smul_zero, add_zero, smul_smul, Rat.cast_inv]
  congr 1
  field_simp

end Interior

/-! ## The mode and `ε'` -/

theorem stepO_run {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d} {n : ℕ} {mo : Mode d} {ξ : Fin d → ℚ} {ζ : ℚ}
    {obs : ℤ} {st' : St d} (h : stepO orc c n mo ξ ζ obs = .run st') : ∃ st, mo = .run st := by
  cases mo with
  | off => simp [stepO] at h
  | guard => simp [stepO] at h
  | run st => exact ⟨st, rfl⟩

theorem modeO_run (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (w : BitRAMO.WorldO d) :
    ∀ (t : ℕ) (st : St d), modeO d n δ r0 R0 a w t = .run st →
      ∃ st0, mode0O w.orc (cfgW d n δ r0 R0 a w) = .run st0 := by
  intro t
  induction t with
  | zero => intro st h; exact ⟨st, h⟩
  | succ t ih =>
    intro st h
    simp only [modeO, trajO] at h
    obtain ⟨st1, h1⟩ := stepO_run h
    exact ih st1 h1

theorem mode0O_run {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d} {st : St d} (h : mode0O orc c = .run st) :
    crossOK orc c ∧ c.par.eps ≤ 1 / 2 := by
  unfold mode0O at h
  by_cases h1 : 1 / 2 < c.par.eps
  · rw [if_pos h1] at h
    cases h
  · rw [if_neg h1] at h
    by_cases h2 : crossOK orc c
    · exact ⟨h2, not_lt.1 h1⟩
    · rw [if_neg h2] at h
      cases h

theorem parO_eps (d n : ℕ) (δ : ℚ) : (parO d n δ).eps =
    up (parO d n δ).pF (14500 * d * (sqrtDn (parO d n δ).q d + 1 / 2 ^ (parO d n δ).q) *
      (36 * (lnQ (parO d n δ).q (NeO d n (kDel δ)) + lnErr (parO d n δ).q (NeO d n (kDel δ)))) ^ 5 /
        sqrtDn (parO d n δ).q n) := rfl

theorem parO_q (d n : ℕ) (δ : ℚ) :
    (parO d n δ).q = (parO d n δ).p + 2 * (NeO d n (kDel δ)).size.size + 24 := rfl

theorem up_nonneg {k : ℕ} {x : ℚ} (hx : 0 ≤ x) : 0 ≤ up k x := by
  unfold up
  apply div_nonneg _ (by positivity)
  exact_mod_cast Int.ceil_nonneg (mul_nonneg hx (by positivity))

/-- `ε' ≥ 0` (for `n = 0` the division by `sqrtDn q 0 = 0` gives `0`). -/
theorem eps_parO_nonneg (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) : 0 ≤ (parO d n δ).eps := by
  rw [parO_eps]
  apply up_nonneg
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [sqrtDn]
  have hne : 1 ≤ NeO d n (kDel δ) := by
    unfold NeO
    have : 0 < 15 * 2 ^ (17 + kDel δ) * d ^ 3 * n ^ 4 := by positivity
    omega
  have hq : 1 ≤ (parO d n δ).q := by rw [parO_q]; omega
  have hL := Bit.PieceA.lnQ_err (parO d n δ).q (NeO d n (kDel δ)) hq hne
  have hlog : 0 ≤ Real.log (NeO d n (kDel δ)) := Real.log_nonneg (by exact_mod_cast hne)
  have hLe : (0 : ℝ) ≤ ((lnQ (parO d n δ).q (NeO d n (kDel δ)) + lnErr (parO d n δ).q (NeO d n (kDel δ)) : ℚ) :
      ℝ) := by
    push_cast
    linarith [(abs_le.1 hL).1]
  have hLe' : (0 : ℚ) ≤ lnQ (parO d n δ).q (NeO d n (kDel δ)) + lnErr (parO d n δ).q (NeO d n (kDel δ)) := by
    exact_mod_cast hLe
  have hrn : 0 ≤ sqrtDn (parO d n δ).q n := by unfold sqrtDn; positivity
  have hrd : 0 ≤ sqrtDn (parO d n δ).q d := by unfold sqrtDn; positivity
  apply div_nonneg _ hrn
  exact mul_nonneg (by positivity) (pow_nonneg (by linarith) 5)

theorem playIntO : PlayIntO := by
  intro d n δ r0 R0 a K w hd hr0 hK hball horc t
  have hr0' : (0 : ℝ) < r0 := by exact_mod_cast hr0
  have ha : toE a ∈ interior K := by
    rw [mem_interior]
    exact ⟨ball (toE a) r0, ball_subset_closedBall.trans hball, isOpen_ball, mem_ball_self hr0'⟩
  unfold playO
  rcases hm : modeO d n δ r0 R0 a w t with _ | _ | st
  · exact ha
  · exact ha
  · obtain ⟨st0, h0⟩ := modeO_run d n δ r0 R0 a w t st hm
    obtain ⟨hcross, heps⟩ := mode0O_run h0
    have hball' : closedBall (toE (cfgW d n δ r0 R0 a w).a) ((cfgW d n δ r0 R0 a w).r0 : ℝ) ⊆ K := hball
    have heps0 : 0 ≤ (cfgW d n δ r0 R0 a w).par.eps := eps_parO_nonneg d n δ hd
    have hpl := play_int hK hd hr0' hball' horc hcross heps0 heps
      (XO (cfgW d n δ r0 R0 a w) st (drawO d n δ r0 R0 w.cs t).1)
    exact hpl

end AdversarialBco.Unified.BLO
