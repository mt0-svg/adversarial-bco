/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.BLOGeom
public import AdversarialBco.Unified.BLOPos
public import AdversarialBco.Unified.SepGrid

@[expose] public section

/-!
# BL-O: the SEP field of the stages meets `triPosT_bad_sep`'s hypothesis

`posSepO : PosSepO`. At a good rational stage position `P` (stage body `Kb = S_P(K ∩ cube_j)` with
`B̄(0, 1) ⊆ Kb ⊆ B̄(0, ρ_a)`) and a rational base point `z` with `|z| ≤ r_z`, the stage field `stSepR` is SEP's
vector (`sepAcc`, Unified/SepGrid.lean) for the gauge `h = γ_{Kb}`:

* the stage test (CM at the precision `stK` and the cube check) certifies `Kb` about `0` with the band
  `η = 6·2^{-stK} ρ_a R0/r0² ≤ 2^{-(eη + eH + 2)}` (`stTest_cert`, the argument of `testCertO` on `K ∩ cube_j`);
* the evaluator `stEv` is the bisection gauge of that test (`gaugeAcc`) within `2^{-eη}` of `h` at every grid point
  near the rounded base point, where `h ≤ |·| ≤ 1 + r_z ≤ 2^{eH}`;
* `h` is convex and `1`-Lipschitz (`B̄(0, 1) ⊆ Kb`); SEP's point is within `(64/63) 2^{-e1'} + d 2^{-E-1}` of `z`,
  `e1' = e1 + 1`, so within `(64/63) 2^{-e1}`.
-/

namespace AdversarialBco.Unified.BLO

open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.LeanAp AdversarialBco.Uni AdversarialBco.Bit.RQ
open AdversarialBco.BitRAM (toE)
open AdversarialBco.BitRAMO (WeakMemOracle)
open Metric Matrix

variable {d : ℕ}

/-! ## Rational points -/

theorem exists_castP {P : PgSp d} (hP : UniPos.IsRatPg P) : ∃ Q : PosQ d, castP Q = P := by
  simp only [UniPos.IsRatPg, UniPos.IsQ, Set.mem_range] at hP
  choose f hf using hP
  refine ⟨(fun i => f (Sum.inl i), fun i i' => f (Sum.inr (i, i'))), ?_⟩
  ext k
  rcases k with i | ⟨i, i'⟩
  · rw [castP_apply_inl]; exact hf (Sum.inl i)
  · rw [castP_apply_inr]; exact hf (Sum.inr (i, i'))

theorem exists_toE {z : E d} (hz : UniPos.IsRatE z) : ∃ q : Fin d → ℚ, toE q = z := by
  simp only [UniPos.IsRatE, UniPos.IsQ, Set.mem_range] at hz
  choose f hf using hz
  refine ⟨f, ?_⟩
  ext i
  exact hf i

theorem castP_center (Q : PosQ d) (y : Fin d → ℚ) :
    pgMu (castP Q) + pgOp (castP Q) (WithLp.toLp 2 (qR y)) = toE (Q.1 + Q.2 *ᵥ y) := by
  rw [pgOp_apply]
  simp only [castP, pgMu_pgPack, pgMat_pgPack, toE]
  rw [← WithLp.toLp_add]
  congr 1
  funext i
  simp only [Pi.add_apply, mulVec, dotProduct, Bit.BLP.cM, Matrix.map_apply, qR, WithLp.ofLp_toLp]
  push_cast
  rfl

/-! ## The gauge of a body holding the unit ball -/

section Gauge

variable {Kb : Set (E d)}

theorem gauge_le_norm (h1 : closedBall (0 : E d) 1 ⊆ Kb) (x : E d) : gauge Kb x ≤ ‖x‖ := by
  have := gauge_mono (absorbent_of_ball (le_refl (closedBall (0 : E d) 1))) h1 x
  rwa [gauge_closedBall zero_le_one, div_one] at this

theorem gauge_lip (hc : Convex ℝ Kb) (h1 : closedBall (0 : E d) 1 ⊆ Kb) (x y : E d) :
    |gauge Kb x - gauge Kb y| ≤ ‖x - y‖ := by
  have habs := absorbent_of_ball h1
  have hxy := gauge_add_le hc habs (x - y) y
  have hyx := gauge_add_le hc habs (y - x) x
  rw [sub_add_cancel] at hxy hyx
  have n1 := gauge_le_norm h1 (x - y)
  have n2 := gauge_le_norm h1 (y - x)
  rw [norm_sub_rev] at n2
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem gauge_convexOn (hc : Convex ℝ Kb) (h1 : closedBall (0 : E d) 1 ⊆ Kb) :
    ConvexOn ℝ Set.univ fun y : Fin d → ℝ => gauge Kb (WithLp.toLp 2 y) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
  have habs := absorbent_of_ball h1
  simp only [smul_eq_mul, WithLp.toLp_add, WithLp.toLp_smul]
  calc gauge Kb (a • WithLp.toLp 2 x + b • WithLp.toLp 2 y) ≤
        gauge Kb (a • WithLp.toLp 2 x) + gauge Kb (b • WithLp.toLp 2 y) := gauge_add_le hc habs _ _
    _ = a * gauge Kb (WithLp.toLp 2 x) + b * gauge Kb (WithLp.toLp 2 y) := by
        rw [gauge_smul_of_nonneg ha, gauge_smul_of_nonneg hb, smul_eq_mul, smul_eq_mul]

theorem oGauge_body (Kb : Set (E d)) (x : Fin d → ℝ) :
    oGauge {y | WithLp.toLp 2 y ∈ Kb} 0 x = sInf {t : ℝ | 0 < t ∧ t⁻¹ • WithLp.toLp 2 x ∈ Kb} := by
  unfold oGauge
  congr 1
  ext t
  simp only [Set.mem_ofPred_eq, zero_add, sub_zero, WithLp.toLp_smul]

theorem oGauge_body_eq (Kb : Set (E d)) (x : Fin d → ℝ) :
    oGauge {y | WithLp.toLp 2 y ∈ Kb} 0 x = gauge Kb (WithLp.toLp 2 x) := by
  rw [oGauge_body, gauge_def']
  rfl

end Gauge

/-! ## The stage test certifies the stage body -/

/-- The stage test at the precision `stK` certifies the stage body `S_P(K ∩ cube_j)` about `0` with the band
`6·2^{-stK} Rg R0/r0²`, `Rg` an outer radius of the body. -/
theorem stTest_cert {K : Set (E d)} (hK : Convex ℝ K) {orc : (Fin d → ℚ) → ℕ → Bool} (horc : WeakMemOracle K orc)
    {a : Fin d → ℚ} {r0 R0 : ℚ} (hr0 : (0 : ℝ) < r0) (hrR : (r0 : ℝ) ≤ R0) (hball : closedBall (toE a) (r0 : ℝ) ⊆ K)
    (hKR : K ⊆ closedBall (toE a) (R0 : ℝ)) (j : ℕ) (Q : PosQ d) (Rg : ℝ) (hRg : 1 ≤ Rg)
    (hKbc : Convex ℝ (posBody (K ∩ Bit.triCube (toE a) (2 ^ (j + 1) * r0)) (pgMu (castP Q)) (pgOp (castP Q))))
    (hB1 : closedBall (0 : E d) 1 ⊆
      posBody (K ∩ Bit.triCube (toE a) (2 ^ (j + 1) * r0)) (pgMu (castP Q)) (pgOp (castP Q)))
    (hBR : posBody (K ∩ Bit.triCube (toE a) (2 ^ (j + 1) * r0)) (pgMu (castP Q)) (pgOp (castP Q)) ⊆
      closedBall 0 Rg) :
    TestCert (stTest orc a r0 R0 j Q)
      {y | WithLp.toLp 2 y ∈ posBody (K ∩ Bit.triCube (toE a) (2 ^ (j + 1) * r0)) (pgMu (castP Q)) (pgOp (castP Q))}
      0 (6 * (2 : ℝ)⁻¹ ^ stK d r0 R0 * Rg * R0 / r0 ^ 2) := by
  set Kc := K ∩ Bit.triCube (toE a) (2 ^ (j + 1) * r0) with hKc
  set Kb := posBody Kc (pgMu (castP Q)) (pgOp (castP Q)) with hKb
  have hR0 : (0 : ℝ) < R0 := lt_of_lt_of_le hr0 hrR
  have hRg0 : (0 : ℝ) < Rg := by linarith
  have h0 : (0 : E d) ∈ Kb := hB1 (mem_closedBall_self zero_le_one)
  have hballc : closedBall (toE a) (r0 : ℝ) ⊆ Kc := by
    intro x hx
    refine ⟨hball hx, fun i => ?_⟩
    rw [mem_closedBall, dist_eq_norm] at hx
    have h1 : |x i - toE a i| ≤ ‖x - toE a‖ := by
      have := PiLp.norm_apply_le (x - toE a) i
      rwa [Real.norm_eq_abs] at this
    have h2 : (r0 : ℝ) ≤ 2 ^ (j + 1) * r0 := le_mul_of_one_le_left hr0.le (one_le_pow₀ (by norm_num))
    linarith
  intro y
  have hcen := castP_center Q y
  have hq := toE_cmPt a r0 (stK d r0 R0) (Q.1 + Q.2 *ᵥ y)
  obtain ⟨hacc, -⟩ := uni_cm_weakMem K hK (toE a) (toE (Q.1 + Q.2 *ᵥ y)) r0 hr0 hball orc horc _ _ hq
  have hT : stTest orc a r0 R0 j Q y = (cmQ orc a r0 (stK d r0 R0) (Q.1 + Q.2 *ᵥ y) &&
      decide (∀ i, |(Q.1 + Q.2 *ᵥ y) i - a i| ≤ 2 ^ (j + 1) * r0)) := rfl
  have hbox : ∀ x : Fin d → ℚ, toE x ∈ Bit.triCube (toE a) (2 ^ (j + 1) * r0) ↔
      ∀ i, |x i - a i| ≤ 2 ^ (j + 1) * r0 := by
    intro x
    show (∀ i, |toE x i - toE a i| ≤ 2 ^ (j + 1) * (r0 : ℝ)) ↔ _
    simp only [toE_apply]
    constructor
    · intro h i; exact_mod_cast h i
    · intro h i; exact_mod_cast h i
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hT, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hcm, hb⟩ := h
    show pgMu (castP Q) + pgOp (castP Q) (WithLp.toLp 2 (qR y)) ∈ Kc
    rw [hcen]
    exact ⟨interior_subset (hacc hcm), (hbox _).2 hb⟩
  · rw [oGauge_body]
    by_contra hle
    push_neg at hle
    have hε : (0 : ℝ) < (2 : ℝ)⁻¹ ^ stK d r0 R0 := by positivity
    have hη : 0 < 6 * (2 : ℝ)⁻¹ ^ stK d r0 R0 * Rg * R0 / r0 ^ 2 := by positivity
    have hsub : closedBall (WithLp.toLp 2 (qR y)) (6 * (2 : ℝ)⁻¹ ^ stK d r0 R0 * Rg * R0 / r0 ^ 2 / 2) ⊆ Kb :=
      ball_of_sInf (Kb := Kb) hKbc hB1 (by linarith)
    have hKsub := ball_transfer hr0 hRg0 hballc h0 hBR hsub
    rw [hcen] at hKsub
    have hYc : toE (Q.1 + Q.2 *ᵥ y) ∈ Kc := hKsub (mem_closedBall_self (by positivity))
    have hbx : decide (∀ i, |(Q.1 + Q.2 *ᵥ y) i - a i| ≤ 2 ^ (j + 1) * r0) = true :=
      decide_eq_true ((hbox _).1 hYc.2)
    have hKsub' : closedBall (toE (Q.1 + Q.2 *ᵥ y)) (6 * (2 : ℝ)⁻¹ ^ stK d r0 R0 * Rg * R0 / r0 ^ 2 / 2 * r0 / Rg)
        ⊆ K := hKsub.trans Set.inter_subset_left
    have hdist : dist (toE (Q.1 + Q.2 *ᵥ y)) (toE a) ≤ R0 := by
      have := hKR hYc.1
      rwa [mem_closedBall] at this
    have hρ : (2 : ℝ)⁻¹ ^ stK d r0 R0 + 2 * (2 : ℝ)⁻¹ ^ stK d r0 R0 * R0 / r0 ≤
        6 * (2 : ℝ)⁻¹ ^ stK d r0 R0 * Rg * R0 / r0 ^ 2 / 2 * r0 / Rg := by
      have e1 : 6 * (2 : ℝ)⁻¹ ^ stK d r0 R0 * Rg * R0 / r0 ^ 2 / 2 * r0 / Rg =
          3 * (2 : ℝ)⁻¹ ^ stK d r0 R0 * R0 / r0 := by
        field_simp
        ring
      rw [e1]
      have h2 : (2 : ℝ)⁻¹ ^ stK d r0 R0 ≤ (2 : ℝ)⁻¹ ^ stK d r0 R0 * R0 / r0 := by
        rw [le_div_iff₀ hr0]
        nlinarith
      have e2 : 3 * (2 : ℝ)⁻¹ ^ stK d r0 R0 * R0 / r0 =
          (2 : ℝ)⁻¹ ^ stK d r0 R0 * R0 / r0 + 2 * (2 : ℝ)⁻¹ ^ stK d r0 R0 * R0 / r0 := by ring
      linarith
    have hdeep := uni_cm_deep K (toE a) (toE (Q.1 + Q.2 *ᵥ y)) r0 R0 ((2 : ℝ)⁻¹ ^ stK d r0 R0) _ hr0 hε.le
      hKsub' hdist hρ
    rw [← hq] at hdeep
    have hcm : cmQ orc a r0 (stK d r0 R0) (Q.1 + Q.2 *ᵥ y) = true := by
      cases hc : cmQ orc a r0 (stK d r0 R0) (Q.1 + Q.2 *ᵥ y)
      · exact absurd hdeep ((horc _ _).2 hc)
      · rfl
    rw [hT, hcm, hbx] at h
    simp at h

/-! ## The constants of the stages -/

theorem triE1_eq (d : ℕ) : triE1Q d = UniPos.triE1 d := by
  unfold triE1Q UniPos.triE1
  rw [← natCeil_ratCast]
  push_cast
  rw [triElo_cast]

theorem triETau_eq (d : ℕ) : triETauQ d = UniPos.triETau d := by
  unfold triETauQ UniPos.triETau
  rw [← natCeil_ratCast]
  push_cast
  rw [triKg_eq, triD2_cast, triElo_cast]

theorem triE1_pos (d : ℕ) (hd : 1 ≤ d) : 1 ≤ triE1Q d := by
  rw [triE1_eq]
  obtain ⟨-, he0, he1, -⟩ := UniPos.tri_par_basic d hd
  unfold UniPos.triE1
  apply Nat.clog_pos (by norm_num)
  have h64 : (64 : ℝ) ≤ 64 / Bit.triElo d := by
    rw [le_div_iff₀ he0]
    nlinarith
  have hc := Nat.le_ceil (64 / Bit.triElo d)
  have : (1 : ℝ) < (⌈64 / Bit.triElo d⌉₊ : ℝ) := by linarith
  exact_mod_cast this

theorem triRz_le (d : ℕ) (hd : 1 ≤ d) : UniPos.triRz d ≤ (triRzQ d : ℝ) := by
  obtain ⟨hRa1, -, hkR, -, -, -, hB1, -⟩ := Bit.tri_par_box d hd
  have hR0 : 0 ≤ Bit.triR d := by
    have : (0 : ℝ) < pgKappa := by unfold pgKappa; norm_num
    nlinarith
  unfold UniPos.triRz triRzQ
  push_cast
  rw [triR_cast, triB_cast, triKg_eq]
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : Real.sqrt d ≤ d := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hs2 : Real.sqrt (d * (d + 1) / 2) ≤ d := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hs3 : Real.sqrt (8 * d * Bit.triKg d) ≤ 8 * d * Bit.triKg d := by
    rcases Nat.eq_zero_or_pos (Bit.triKg d) with h | h
    · rw [h]; simp
    · have : (1 : ℝ) ≤ Bit.triKg d := by exact_mod_cast h
      have hx : (1 : ℝ) ≤ 8 * d * Bit.triKg d := by nlinarith
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [hx]
  have h1 : Real.sqrt d * Bit.triR d ≤ d * Bit.triR d := mul_le_mul_of_nonneg_right hs1 hR0
  have h2 : Bit.triB d * Real.sqrt (d * (d + 1) / 2) * Real.sqrt (8 * d * Bit.triKg d) ≤
      Bit.triB d * (d * (8 * d * Bit.triKg d)) := by
    have := mul_le_mul hs2 hs3 (Real.sqrt_nonneg _) (by linarith)
    calc _ = Bit.triB d * (Real.sqrt (d * (d + 1) / 2) * Real.sqrt (8 * d * Bit.triKg d)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this (by linarith)
  nlinarith

theorem triRa_le (d : ℕ) : Bit.triRa d ≤ (triRaQ d : ℝ) := by
  unfold Bit.triRa triRaQ
  rw [triSQ_eq]
  push_cast
  linarith

/-- The band of the stage test at the precision `stK`: at most `2^{-(eη + eH + 2)}`. -/
theorem stBand_le (d : ℕ) (r0 R0 : ℚ) (hr0 : (0 : ℝ) < r0) (hR0 : (0 : ℝ) ≤ R0) :
    6 * (2 : ℝ)⁻¹ ^ stK d r0 R0 * Bit.triRa d * R0 / r0 ^ 2 ≤ (2 : ℝ)⁻¹ ^ (stEEta d + stEH d + 2) := by
  set c := Nat.clog 2 ⌈6 * triRaQ d * R0 / r0 ^ 2⌉₊
  have h1 : ((6 * triRaQ d * R0 / r0 ^ 2 : ℚ) : ℝ) ≤ ((⌈6 * triRaQ d * R0 / r0 ^ 2⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_ceil _
  have h2 : ⌈6 * triRaQ d * R0 / r0 ^ 2⌉₊ ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) _
  push_cast at h1
  have h3 : 6 * Bit.triRa d * R0 / r0 ^ 2 ≤ 2 ^ c := by
    calc 6 * Bit.triRa d * R0 / r0 ^ 2 ≤ 6 * (triRaQ d : ℝ) * R0 / r0 ^ 2 := by gcongr; exact triRa_le d
      _ ≤ _ := h1
      _ ≤ _ := by exact_mod_cast h2
  have e : (2 : ℝ)⁻¹ ^ stK d r0 R0 = (2 : ℝ)⁻¹ ^ (stEEta d + stEH d + 2) * (2 : ℝ)⁻¹ ^ c := by
    rw [← pow_add]; rfl
  have h4 : (2 : ℝ)⁻¹ ^ c * 2 ^ c = 1 := by rw [← mul_pow]; norm_num
  calc 6 * (2 : ℝ)⁻¹ ^ stK d r0 R0 * Bit.triRa d * R0 / r0 ^ 2 =
        (2 : ℝ)⁻¹ ^ (stEEta d + stEH d + 2) * ((2 : ℝ)⁻¹ ^ c * (6 * Bit.triRa d * R0 / r0 ^ 2)) := by
        rw [e]; ring
    _ ≤ (2 : ℝ)⁻¹ ^ (stEEta d + stEH d + 2) * ((2 : ℝ)⁻¹ ^ c * 2 ^ c) := by gcongr
    _ = _ := by rw [h4, mul_one]

/-! ## The grid -/

theorem rndPt_err (E : ℕ) (z : Fin d → ℚ) (i : Fin d) :
    |gridR E (rndPt E z) i - (z i : ℝ)| ≤ (2 : ℝ)⁻¹ ^ (E + 1) := by
  have h2 : (0 : ℝ) < 2 ^ E := by positivity
  have hf1 := Int.floor_le (z i * 2 ^ E + 1 / 2)
  have hf2 := Int.lt_floor_add_one (z i * 2 ^ E + 1 / 2)
  have c1 : ((⌊z i * 2 ^ E + 1 / 2⌋ : ℤ) : ℝ) ≤ (z i : ℝ) * 2 ^ E + 1 / 2 := by
    have := Rat.cast_le (K := ℝ) |>.2 hf1
    push_cast at this
    exact this
  have c2 : (z i : ℝ) * 2 ^ E + 1 / 2 < ((⌊z i * 2 ^ E + 1 / 2⌋ : ℤ) : ℝ) + 1 := by
    have := Rat.cast_lt (K := ℝ) |>.2 hf2
    push_cast at this
    exact this
  have key : gridR E (rndPt E z) i - (z i : ℝ) =
      (((⌊z i * 2 ^ E + 1 / 2⌋ : ℤ) : ℝ) - (z i : ℝ) * 2 ^ E) / 2 ^ E := by
    simp only [gridR, rndPt]
    field_simp
  rw [key, abs_div, abs_of_pos h2, div_le_iff₀ h2]
  have e : (2 : ℝ)⁻¹ ^ (E + 1) * 2 ^ E = 1 / 2 := by
    rw [pow_succ, mul_comm, ← mul_assoc, ← mul_pow]; norm_num
  rw [e, abs_le]
  constructor <;> linarith

theorem norm_toLp_le_card (v : Fin d → ℝ) (c : ℝ) (hv : ∀ i, |v i| ≤ c) : ‖(WithLp.toLp 2 v : E d)‖ ≤ d * c := by
  calc ‖(WithLp.toLp 2 v : E d)‖ ≤ ∑ i, |(WithLp.toLp 2 v : E d) i| := norm_le_l1 _
    _ ≤ ∑ _i : Fin d, c := Finset.sum_le_sum fun i _ => hv i
    _ = d * c := by simp

theorem oNorm_tri (u v w : Fin d → ℝ) : oNorm (u - w) ≤ oNorm (u - v) + oNorm (v - w) := by
  rw [oNorm_eq, oNorm_eq, oNorm_eq]
  have e : (WithLp.toLp 2 (u - w) : E d) = WithLp.toLp 2 (u - v) + WithLp.toLp 2 (v - w) := by
    rw [← WithLp.toLp_add]; congr 1; abel
  rw [e]
  exact norm_add_le _ _

theorem r0_le_R0 {K : Set (E d)} (hd : 1 ≤ d) {c : E d} {r R : ℝ} (hr : 0 ≤ r) (h1 : closedBall c r ⊆ K)
    (h2 : K ⊆ closedBall c R) : r ≤ R := by
  set e : E d := WithLp.toLp 2 (Pi.single ⟨0, hd⟩ r)
  have he : ‖e‖ = r := by
    rw [norm_single_le, abs_of_nonneg hr]
  have hm : c + e ∈ K := h1 (by rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, he])
  have := h2 hm
  rwa [mem_closedBall, dist_eq_norm, add_sub_cancel_left, he] at this

/-! ## SEP in a stage -/

theorem posSepO : PosSepO := by
  intro d K orc a r0 R0 hd hK _ hr0 hball hKR horc j P hPq _ hPg z hzq hz
  obtain ⟨Q, rfl⟩ := exists_castP hPq
  obtain ⟨zq, rfl⟩ := exists_toE hzq
  obtain ⟨hKbc, -, hB1, hBR⟩ := hPg
  have hr0' : (0 : ℝ) < r0 := by exact_mod_cast hr0
  have hrR : (r0 : ℝ) ≤ R0 := r0_le_R0 hd hr0'.le hball hKR
  have hR0 : (0 : ℝ) < R0 := lt_of_lt_of_le hr0' hrR
  obtain ⟨hRa1, -⟩ := Bit.tri_par_box d hd
  have hcert := stTest_cert hK horc hr0' hrR hball hKR j Q (Bit.triRa d) hRa1 hKbc hB1 hBR
  have hη := stBand_le d r0 R0 hr0' hR0.le
  have hη0 : 0 ≤ 6 * (2 : ℝ)⁻¹ ^ stK d r0 R0 * Bit.triRa d * R0 / r0 ^ 2 := by
    have : (0 : ℝ) ≤ Bit.triRa d := by linarith
    positivity
  have hp4 : (2 : ℝ)⁻¹ ^ (stEEta d + stEH d + 2) ≤ 1 / 4 := by
    rw [pow_add]
    have : (2 : ℝ)⁻¹ ^ (stEEta d + stEH d) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc (2 : ℝ)⁻¹ ^ (stEEta d + stEH d) * (2 : ℝ)⁻¹ ^ 2 ≤ 1 * (2 : ℝ)⁻¹ ^ 2 := by gcongr
      _ = 1 / 4 := by norm_num
  have hη1 : 6 * (2 : ℝ)⁻¹ ^ stK d r0 R0 * Bit.triRa d * R0 / r0 ^ 2 < 1 := by linarith
  have he1 := triE1_pos d hd
  -- the evaluator
  have hrnd : ∀ i, |gridR (stE d) (rndPt (stE d) zq) i - (zq i : ℝ)| ≤ (2 : ℝ)⁻¹ ^ (stE d + 1) :=
    rndPt_err (stE d) zq
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdE : (d : ℝ) * (2 : ℝ)⁻¹ ^ (stE d + 1) ≤ (2 : ℝ)⁻¹ ^ (stE1 d + 1) := by
    have hE : stE1 d + 1 + d ≤ stE d + 1 := by
      unfold stE
      have : d ≤ d * (2 * (triETauQ d + 3) + 6 + triETauQ d) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have hdl : (d : ℝ) < 2 ^ d := by exact_mod_cast Nat.lt_two_pow_self
    calc (d : ℝ) * (2 : ℝ)⁻¹ ^ (stE d + 1) ≤ d * (2 : ℝ)⁻¹ ^ (stE1 d + 1 + d) := by
          exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hE) (by positivity)
      _ = (2 : ℝ)⁻¹ ^ (stE1 d + 1) * (d * (2 : ℝ)⁻¹ ^ d) := by rw [pow_add]; ring
      _ ≤ (2 : ℝ)⁻¹ ^ (stE1 d + 1) * 1 := by
          gcongr
          rw [inv_pow, mul_inv_le_iff₀ (by positivity)]
          linarith
      _ = _ := mul_one _
  have hy0 : oNorm (gridR (stE d) (rndPt (stE d) zq) - qR zq) ≤ (2 : ℝ)⁻¹ ^ (stE1 d + 1) := by
    rw [oNorm_eq]
    exact (norm_toLp_le_card _ _ fun i => hrnd i).trans hdE
  have hsmall : 2 * (2 : ℝ)⁻¹ ^ stE1 d + (2 : ℝ)⁻¹ ^ (stE1 d + 1) ≤ 1 := by
    have : (2 : ℝ)⁻¹ ^ stE1 d ≤ 1 / 4 := by
      unfold stE1
      calc (2 : ℝ)⁻¹ ^ (triE1Q d + 1) ≤ (2 : ℝ)⁻¹ ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num)
            (by omega)
        _ = 1 / 4 := by norm_num
    rw [pow_succ]
    linarith
  have hzR : ‖toE zq‖ ≤ (triRzQ d : ℝ) := hz.trans (triRz_le d hd)
  have hH : (triRzQ d : ℝ) + 1 ≤ 2 ^ stEH d := by
    have h1 : ((triRzQ d + 1 : ℚ) : ℝ) ≤ ((⌈triRzQ d + 1⌉₊ : ℕ) : ℝ) := by exact_mod_cast Nat.le_ceil _
    have h2 : ⌈triRzQ d + 1⌉₊ ≤ 2 ^ stEH d := Nat.le_pow_clog (by norm_num) _
    push_cast at h1
    calc _ ≤ _ := h1
      _ ≤ _ := by exact_mod_cast h2
  have hacc : ∀ X, oNorm (gridR (stE d) X - gridR (stE d) (rndPt (stE d) zq)) ≤ 2 * (2 : ℝ)⁻¹ ^ stE1 d →
      |(stEv orc a r0 R0 j Q X : ℝ) / 2 ^ stEu d -
          (fun y : Fin d → ℝ => gauge (posBody (K ∩ Bit.triCube (toE a) (2 ^ (j + 1) * r0)) (pgMu (castP Q))
            (pgOp (castP Q))) (WithLp.toLp 2 y)) (gridR (stE d) X)| ≤
        (2 : ℝ)⁻¹ ^ triETauQ d * (2 : ℝ)⁻¹ ^ stE1 d / 1600 * (2 : ℝ)⁻¹ ^ (3 * d * (0 + triETauQ d + 4)) := by
    intro X hX
    simp only
    set Kb := posBody (K ∩ Bit.triCube (toE a) (2 ^ (j + 1) * r0)) (pgMu (castP Q)) (pgOp (castP Q))
    have hxq : qR (ptDN (2 ^ stE d) X) = gridR (stE d) X := by
      funext i
      simp only [qR, ptDN, gridR]
      push_cast
      rfl
    have hev : ((stEv orc a r0 R0 j Q X : ℤ) : ℝ) / 2 ^ stEu d =
        (gaugeQ (stTest orc a r0 R0 j Q) 0 (ptDN (2 ^ stE d) X) ((2 : ℚ) ^ stEH d) (stJ d) : ℝ) := by
      unfold stEv gaugeQ
      push_cast
      rw [show stJ d = stEu d + stEH d by unfold stJ stEu; ring, pow_add]
      field_simp
    have e0 : qR (0 : Fin d → ℚ) = 0 := by funext i; simp [qR]
    have hγ : oGauge {y | WithLp.toLp 2 y ∈ Kb} (qR 0) (qR (ptDN (2 ^ stE d) X)) =
        gauge Kb (WithLp.toLp 2 (gridR (stE d) X)) := by
      rw [e0, oGauge_body_eq, hxq]
    have hnx : ‖(WithLp.toLp 2 (gridR (stE d) X) : E d)‖ ≤ (triRzQ d : ℝ) + 1 := by
      have t1 := oNorm_tri (gridR (stE d) X) (gridR (stE d) (rndPt (stE d) zq)) (qR zq)
      have t2 : oNorm (qR zq) = ‖toE zq‖ := oNorm_eq _
      have t3 := oNorm_tri (gridR (stE d) X) (qR zq) 0
      simp only [sub_zero] at t3
      rw [oNorm_eq] at t3
      rw [t2] at t3
      linarith
    have hγH : gauge Kb (WithLp.toLp 2 (gridR (stE d) X)) ≤ 2 ^ stEH d :=
      (gauge_le_norm hB1 _).trans (hnx.trans hH)
    have hcert' : TestCert (stTest orc a r0 R0 j Q) {y | WithLp.toLp 2 y ∈ Kb} (qR 0)
        (6 * (2 : ℝ)⁻¹ ^ stK d r0 R0 * Bit.triRa d * R0 / r0 ^ 2) := by
      rw [e0]; exact hcert
    have hHq : (0 : ℚ) < 2 ^ stEH d := by positivity
    obtain ⟨hlo, hhi⟩ := gaugeAcc d (stTest orc a r0 R0 j Q) {y | WithLp.toLp 2 y ∈ Kb} 0 (ptDN (2 ^ stE d) X)
      ((2 : ℚ) ^ stEH d) (stJ d) _ hη0 hη1 hcert' hHq (by rw [hγ]; push_cast; exact hγH)
    rw [hγ] at hlo hhi
    push_cast at hhi
    rw [hev, abs_le]
    set γ := gauge Kb (WithLp.toLp 2 (gridR (stE d) X))
    set η := 6 * (2 : ℝ)⁻¹ ^ stK d r0 R0 * Bit.triRa d * R0 / r0 ^ 2
    set gq := ((gaugeQ (stTest orc a r0 R0 j Q) 0 (ptDN (2 ^ stE d) X) ((2 : ℚ) ^ stEH d) (stJ d) : ℚ) : ℝ)
    have hγ0 : 0 ≤ γ := gauge_nonneg _
    have h1η : 0 < 1 - η := by linarith
    have hA : γ / (1 - η) ≤ γ + 2 * γ * η := by
      rw [div_le_iff₀ h1η]
      nlinarith [mul_nonneg hγ0 hη0]
    have hB : 2 * γ * η ≤ (2 : ℝ)⁻¹ ^ (stEEta d + 1) := by
      calc 2 * γ * η ≤ 2 * 2 ^ stEH d * (2 : ℝ)⁻¹ ^ (stEEta d + stEH d + 2) := by gcongr
        _ = (2 : ℝ)⁻¹ ^ (stEEta d + 1) := by
          rw [show stEEta d + stEH d + 2 = (stEEta d + 1) + stEH d + 1 by ring, pow_add, pow_add, inv_pow (2 : ℝ)
            (stEH d)]
          field_simp
    have hC : (2 : ℝ) ^ stEH d / 2 ^ stJ d = (2 : ℝ)⁻¹ ^ (stEEta d + 1) := by
      rw [show stJ d = (stEEta d + 1) + stEH d by unfold stJ; ring, pow_add, inv_pow]
      field_simp
    have hT : (2 : ℝ)⁻¹ ^ stEEta d ≤
        (2 : ℝ)⁻¹ ^ triETauQ d * (2 : ℝ)⁻¹ ^ stE1 d / 1600 * (2 : ℝ)⁻¹ ^ (3 * d * (0 + triETauQ d + 4)) := by
      rw [zero_add]
      have e : (2 : ℝ)⁻¹ ^ stEEta d = (2 : ℝ)⁻¹ ^ triETauQ d * (2 : ℝ)⁻¹ ^ stE1 d / 2048 *
          (2 : ℝ)⁻¹ ^ (3 * d * (triETauQ d + 4)) := by
        unfold stEEta
        ring
      rw [e]
      gcongr
      norm_num
    have hsum : (2 : ℝ)⁻¹ ^ (stEEta d + 1) + (2 : ℝ)⁻¹ ^ (stEEta d + 1) = (2 : ℝ)⁻¹ ^ stEEta d := by
      rw [pow_succ]; ring
    constructor <;> linarith
  have hlip : ∀ x y : Fin d → ℝ,
      |(fun y : Fin d → ℝ => gauge (posBody (K ∩ Bit.triCube (toE a) (2 ^ (j + 1) * r0)) (pgMu (castP Q))
          (pgOp (castP Q))) (WithLp.toLp 2 y)) x -
        (fun y : Fin d → ℝ => gauge (posBody (K ∩ Bit.triCube (toE a) (2 ^ (j + 1) * r0)) (pgMu (castP Q))
          (pgOp (castP Q))) (WithLp.toLp 2 y)) y| ≤ 2 ^ 0 * oNorm (x - y) := by
    intro x y
    simp only [pow_zero, one_mul]
    rw [oNorm_eq, WithLp.toLp_sub]
    exact gauge_lip hKbc hB1 _ _
  have hEg : stE1 d + d * (2 * (0 + triETauQ d + 3) + 6 + triETauQ d + 0) ≤ stE d := by
    unfold stE; simp
  obtain ⟨Y, G, hsep, hYn, hsub⟩ := sepAcc d _ (stEv orc a r0 R0 j Q) (rndPt (stE d) zq) (stE d) (stE1 d)
    (triETauQ d) 0 (stEu d) hd (gauge_convexOn hKbc hB1) hlip hEg hacc
  have hst : stSep orc a r0 R0 j Q zq = fun i => (G i : ℚ) / 2 ^ (stEu d + 1) := by
    unfold stSep
    rw [hsep]
  refine ⟨gridR (stE d) Y, ?_, fun v => ?_⟩
  · have t := oNorm_tri (gridR (stE d) Y) (gridR (stE d) (rndPt (stE d) zq)) (qR zq)
    show oNorm (gridR (stE d) Y - qR zq) ≤ _
    rw [← triE1_eq]
    have e : (64 / 63 : ℝ) * (1 / 2 ^ triE1Q d) = 64 / 63 * (2 : ℝ)⁻¹ ^ (stE1 d) * 2 := by
      unfold stE1
      rw [pow_succ, one_div, inv_pow]
      field_simp
    rw [e]
    have h4 : (2 : ℝ)⁻¹ ^ (stE1 d + 1) = (2 : ℝ)⁻¹ ^ stE1 d / 2 := by rw [pow_succ]; ring
    have h5 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ stE1 d := by positivity
    linarith
  · have := hsub v
    rw [stSepR_cast, hst, ← triETau_eq, one_div, ← inv_pow]
    have eg : (WithLp.ofLp (toE fun i => (G i : ℚ) / 2 ^ (stEu d + 1)) : Fin d → ℝ) =
        fun i => (G i : ℝ) / 2 ^ (stEu d + 1) := by
      funext i
      simp [toE]
    rw [eg]
    exact this

end AdversarialBco.Unified.BLO
