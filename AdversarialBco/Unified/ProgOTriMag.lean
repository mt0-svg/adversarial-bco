/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOTriStageP
public import AdversarialBco.Unified.ProgOSetupCoins
public import AdversarialBco.Bit.Transfer.XTriMag

@[expose] public section

/-!
# TRI-OGD-O on the oracle machine: the exponents and the magnitudes

* `triExpO : TriExpO (2 ^ 1010) 201`: the grids, the box, a draw, the number `N' = 2^{n_e'}` of draws of a stage and the
  units of one BM-INT draw are at most `2^1010 (W + 1)^201`, from v2.1's bounds of the constants of TRI-M
  (Bit/Transfer/XTriMag.lean) and `triJsTQ ≤ triJsQ + 1` (`triJsTQ_le`), `ℓ ≤ 3 W + 22` (`ellO_le`).
* `tzComp_bound`, `tzStageO_bound`: a stage multiplies the entries by `K = 2^{G_c'} + d N' B_h` and the denominator by
  `2^{G_c'}`; `triMagO_of : TriExpO Ce ke → TriMagO (Ce + 2) (ke + 1)`.
-/

namespace AdversarialBco.Unified.ProgO.TriO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM
open AdversarialBco.Unified.ProgO
open AdversarialBco.BitRAM (len)

variable {d : ℕ}

/-! ## The exponents -/

theorem triD2Q_nonneg {d : ℕ} (hd : 1 ≤ d) : 0 ≤ triD2Q d := by
  have h1 : (0 : ℚ) ≤ (d : ℚ) - 1 := by
    have : (1 : ℚ) ≤ d := by exact_mod_cast hd
    linarith
  unfold triD2Q
  have a1 : 0 ≤ 4 * (d : ℚ) * triRQ d ^ 2 := by positivity
  have a2 : 0 ≤ (d : ℚ) * (triBQ d - triAQ d) ^ 2 := by positivity
  have a3 : 0 ≤ 2 * (d : ℚ) * ((d : ℚ) - 1) * triBQ d ^ 2 :=
    mul_nonneg (mul_nonneg (by positivity) h1) (sq_nonneg _)
  linarith

/-- The new step exponent is at most one more than v2.1's. -/
theorem triJsTQ_le {d : ℕ} (hd : 1 ≤ d) (ℓ : ℕ) : triJsTQ d ℓ ≤ triJsQ d ℓ + 1 := by
  unfold triJsTQ
  apply Nat.clog_le_of_le_pow
  have hx : ⌈(triGuQ d + triBuQ d) ^ 2 * 2 ^ triNeQ d ℓ / triD2Q d⌉₊ ≤ 4 ^ triJsQ d ℓ :=
    Nat.le_pow_clog (show 1 < 4 by norm_num) _
  have hD := triD2Q_nonneg hd
  have hg : 0 ≤ triGuQ d := by unfold triGuQ; positivity
  have hb : 0 ≤ triBuQ d := by unfold triBuQ; positivity
  have hsq : (triGuTQ d + triBuQ d) ^ 2 ≤ 2 * (triGuQ d + triBuQ d) ^ 2 := by unfold triGuTQ; nlinarith
  have hx' : (triGuQ d + triBuQ d) ^ 2 * 2 ^ triNeQ d ℓ / triD2Q d ≤ ((4 ^ triJsQ d ℓ : ℕ) : ℚ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hx)
  have hp : (0 : ℚ) ≤ 2 ^ triNeQ d ℓ := by positivity
  have hnum : (triGuTQ d + triBuQ d) ^ 2 * 2 ^ triNeTQ d ℓ ≤ 4 * ((triGuQ d + triBuQ d) ^ 2 * 2 ^ triNeQ d ℓ) := by
    unfold triNeTQ; rw [pow_succ (2 : ℚ) (triNeQ d ℓ)]; nlinarith
  apply Nat.ceil_le.2
  calc (triGuTQ d + triBuQ d) ^ 2 * 2 ^ triNeTQ d ℓ / triD2Q d
      ≤ 4 * ((triGuQ d + triBuQ d) ^ 2 * 2 ^ triNeQ d ℓ) / triD2Q d := div_le_div_of_nonneg_right hnum hD
    _ = 4 * ((triGuQ d + triBuQ d) ^ 2 * 2 ^ triNeQ d ℓ / triD2Q d) := by ring
    _ ≤ 4 * ((4 ^ triJsQ d ℓ : ℕ) : ℚ) := mul_le_mul_of_nonneg_left hx' (by norm_num)
    _ = ((4 ^ (triJsQ d ℓ + 1) : ℕ) : ℚ) := by push_cast; ring

/-- `ℓ = ellPosO d n k_δ r₀ R₀ ≤ 3 W + 22`. -/
theorem ellO_le {n : ℕ} {δ r0 R0 : ℚ} (a : Fin d → ℚ) (hI : InU d n δ r0 R0) :
    ellO d n δ r0 R0 ≤ 3 * WT d n δ r0 R0 a + 22 := by
  have hM := triMstQ_le hI.hr0 hI.hR0
  have hk := kDel_le_size hI.hδ0
  have hS : len R0.num + len (r0.den : ℤ) + len (δ.den : ℤ) ≤ sizeN δ r0 R0 a := by unfold sizeN; omega
  rw [len_natCast δ.den] at hS
  have hlp := ellPosO_le d n (kDel δ) r0 R0
  have hW : WT d n δ r0 R0 a = d + n.size + sizeN δ r0 R0 a + 1 := rfl
  show ellPosO d n (kDel δ) r0 R0 ≤ 3 * WT d n δ r0 R0 a + 22
  omega

/-- **The exponents of TRI-OGD-O** at `2^1010 (W + 1)^201`. -/
theorem triExpO : TriExpO (2 ^ 1010) 201 := by
  intro d n δ r0 R0 a hI
  have hd := hI.hd
  have hℓ := ellO_le a hI
  have hdW : d ≤ WT d n δ r0 R0 a := by simp only [WT, wU]; omega
  have hLa := triLa_le_lin hd
  have hBv := triBvQ_le_lin hd
  have hJa := triJaQ_le_lin hd
  have hNe := triNeQ_le_lin hd (ellO d n δ r0 R0)
  have hJs := triJsQ_le_lin hd (ellO d n δ r0 R0)
  have hJsT := triJsTQ_le hd (ellO d n δ r0 R0)
  have hP := tzP_le hd
  have hPN := pow_triNeQ_le hd (ellO d n δ r0 R0)
  have hg1 : 1 ≤ triBgQ d := by unfold triBgQ triKgQ; omega
  have hgp : triBgQ d ≤ tzP d := by unfold tzP gsm_prec; omega
  have hbm := bmUnits_le_sq hg1
  have hG : tGcT d (ellO d n δ r0 R0) = triBvQ d + triJsTQ d (ellO d n δ r0 R0) + triJaQ d +
      (triNeQ d (ellO d n δ r0 R0) + 1) := rfl
  rw [hG]
  generalize ellO d n δ r0 R0 = ℓ at *
  generalize WT d n δ r0 R0 a = W at *
  have hdV : d < W + 1 := by omega
  have hℓV : ℓ ≤ 3 * (W + 1) + 19 := by omega
  generalize W + 1 = V at hdV hℓV ⊢
  have hV : 1 ≤ V := by omega
  have p21 : d ^ 21 ≤ V ^ 21 := Nat.pow_le_pow_left hdV.le 21
  have p200 : d ^ 200 ≤ V ^ 200 := Nat.pow_le_pow_left hdV.le 200
  have q21 : V ^ 21 ≤ V ^ 201 := Nat.pow_le_pow_right hV (by norm_num)
  have q1 : V ≤ V ^ 201 := by
    calc V = V ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right hV (by norm_num)
  have q42 : V ^ 42 ≤ V ^ 201 := Nat.pow_le_pow_right hV (by norm_num)
  have e201 : V ^ 201 = V ^ 200 * V := pow_succ _ _
  have c1 : 2 ^ 160 + 4000 ≤ 2 ^ 1010 :=
    calc 2 ^ 160 + 4000 ≤ 2 ^ 160 + 2 ^ 160 := Nat.add_le_add_left (by norm_num) _
      _ = 2 ^ 161 := by ring
      _ ≤ 2 ^ 1010 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have c2 : 2 ^ 1000 * 52 ≤ 2 ^ 1010 :=
    calc 2 ^ 1000 * 52 ≤ 2 ^ 1000 * 2 ^ 10 := Nat.mul_le_mul_left _ (by norm_num)
      _ = 2 ^ 1010 := by rw [← pow_add]
  have c3 : 1176 * (2 ^ 158) ^ 2 ≤ 2 ^ 1010 :=
    calc 1176 * (2 ^ 158) ^ 2 ≤ 2 ^ 11 * 2 ^ 316 := Nat.mul_le_mul (by norm_num) (by rw [← pow_mul])
      _ = 2 ^ 327 := by rw [← pow_add]
      _ ≤ 2 ^ 1010 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  generalize (2 : ℕ) ^ 1010 = C at c1 c2 c3 ⊢
  refine ⟨?_, ?_, ?_⟩
  · -- the grids
    have h1 : 4 * tzP d ≤ 2 ^ 160 * V ^ 21 := by
      calc 4 * tzP d ≤ 4 * (2 ^ 158 * d ^ 21) := by omega
        _ ≤ 4 * (2 ^ 158 * V ^ 21) := by gcongr
        _ = 2 ^ 160 * V ^ 21 := by ring
    have h2 : 2 ^ 160 * V ^ 21 + 4000 * V ≤ C * V ^ 201 :=
      calc 2 ^ 160 * V ^ 21 + 4000 * V ≤ 2 ^ 160 * V ^ 201 + 4000 * V ^ 201 :=
            add_le_add (Nat.mul_le_mul_left _ q21) (Nat.mul_le_mul_left _ q1)
        _ = (2 ^ 160 + 4000) * V ^ 201 := by ring
        _ ≤ C * V ^ 201 := Nat.mul_le_mul_right _ c1
    generalize (2 : ℕ) ^ 160 * V ^ 21 = A at h1 h2
    generalize C * V ^ 201 = R at h2 ⊢
    omega
  · -- the draws of a stage
    calc 2 ^ (triNeQ d ℓ + 1) = 2 * 2 ^ triNeQ d ℓ := by ring
      _ ≤ 2 * (2 ^ 1000 * d ^ 200 * (ℓ + 1)) := Nat.mul_le_mul_left _ hPN
      _ ≤ 2 * (2 ^ 1000 * V ^ 200 * (26 * V)) := by gcongr; omega
      _ = 2 ^ 1000 * 52 * (V ^ 200 * V) := by ring
      _ ≤ C * V ^ 201 := by rw [← e201]; exact Nat.mul_le_mul_right _ c2
  · -- the units of a draw
    calc bmUnits (triBgQ d) ≤ 1176 * triBgQ d ^ 2 := hbm
      _ ≤ 1176 * (2 ^ 158 * V ^ 21) ^ 2 := by
          gcongr; exact hgp.trans (hP.trans (Nat.mul_le_mul_left _ p21))
      _ = 1176 * (2 ^ 158) ^ 2 * V ^ 42 := by ring
      _ ≤ C * V ^ 201 := Nat.mul_le_mul c3 q42

/-- **The exponents of the constants of TRI-OGD-O** (the prologue's straight line and the core step): every exponent of a
power among the constants is at most `C (W + 1)^k`. -/
def TriExpS (C k : ℕ) : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ), InU d n δ r0 R0 →
    triLa (triSQ d) + triLh (triSQ d) + triJaQ d + triBvQ d + 2 * tzP d + tGcT d (ellO d n δ r0 R0) + stE d +
      triETauQ d + stJ d + stEu d + triSQ d ≤ C * (WT d n δ r0 R0 a + 1) ^ k

/-! ## The magnitudes of the stages -/

theorem tzComp_bound (P : StZ d) (S : PosZ d) (Gc : ℕ) {H M : ℤ} (hH : 0 ≤ H) (_hM : 0 ≤ M)
    (hmu : ∀ i, |P.mu i| ≤ H) (hT : ∀ i l, |P.T i l| ≤ H) (hS1 : ∀ i, |S.1 i| ≤ M)
    (hS2 : ∀ i l, |S.2 i l| ≤ M) :
    (∀ i, |(tzComp P S Gc).mu i| ≤ H * (2 ^ Gc + d * M)) ∧
      ∀ i l, |(tzComp P S Gc).T i l| ≤ H * (2 ^ Gc + d * M) := by
  have hsum : ∀ f g : Fin d → ℤ, (∀ l, |f l| ≤ H) → (∀ l, |g l| ≤ M) → |∑ l, f l * g l| ≤ d * (H * M) := by
    intro f g hf hg
    calc |∑ l, f l * g l| ≤ ∑ l, |f l * g l| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin d, H * M := Finset.sum_le_sum fun l _ => by
          rw [abs_mul]; exact mul_le_mul (hf l) (hg l) (abs_nonneg _) hH
      _ = d * (H * M) := by simp
  have h2 : (0 : ℤ) < 2 ^ Gc := by positivity
  constructor
  · intro i
    simp only [tzComp, Matrix.mulVec, dotProduct]
    calc |P.mu i * 2 ^ Gc + ∑ l, P.T i l * S.1 l| ≤ |P.mu i * 2 ^ Gc| + |∑ l, P.T i l * S.1 l| := abs_add_le _ _
      _ ≤ H * 2 ^ Gc + d * (H * M) := by
          gcongr
          · rw [abs_mul, abs_of_pos h2]; exact mul_le_mul_of_nonneg_right (hmu i) h2.le
          · exact hsum _ _ (hT i) hS1
      _ = H * (2 ^ Gc + d * M) := by ring
  · intro i l
    simp only [tzComp, Matrix.mul_apply]
    calc |∑ k, P.T i k * S.2 k l| ≤ d * (H * M) := hsum _ (fun k => S.2 k l) (hT i) (fun k => hS2 k l)
      _ ≤ H * (2 ^ Gc + d * M) := by nlinarith [mul_nonneg hH h2.le]

/-- The stages from `P0`: the denominator `P0.D 2^{j G_c'}`, the entries at most `H K^j`. -/
theorem tzStageO_bound (orc : (Fin d → ℚ) → ℕ → Bool) (a : Fin d → ℚ) (r0 R0 : ℚ) (ℓ : ℕ) (P0 : StZ d)
    (ω : ℕ → ℕ → Bool) {H : ℤ} (hH : 0 ≤ H) (hmu : ∀ i, |P0.mu i| ≤ H) (hT : ∀ i l, |P0.T i l| ≤ H) :
    ∀ j, (tzStageO orc a r0 R0 ℓ P0 ω j).D = P0.D * 2 ^ (j * tGcT d ℓ) ∧
      (∀ i, |(tzStageO orc a r0 R0 ℓ P0 ω j).mu i| ≤
        H * (2 ^ tGcT d ℓ + d * (((2 ^ triNeTQ d ℓ : ℕ) : ℤ) * (tzDCO d ℓ).Bh)) ^ j) ∧
      ∀ i l, |(tzStageO orc a r0 R0 ℓ P0 ω j).T i l| ≤
        H * (2 ^ tGcT d ℓ + d * (((2 ^ triNeTQ d ℓ : ℕ) : ℤ) * (tzDCO d ℓ).Bh)) ^ j
  | 0 => by
    refine ⟨by simp [tzStageO], fun i => ?_, fun i l => ?_⟩
    · simp only [tzStageO, pow_zero, mul_one]; exact hmu i
    · simp only [tzStageO, pow_zero, mul_one]; exact hT i l
  | j + 1 => by
    obtain ⟨hD, h1, h2⟩ := tzStageO_bound orc a r0 R0 ℓ P0 ω hH hmu hT j
    obtain ⟨hR0, hRB, hAl, hAB, hPG, hPGB⟩ := tzDCO_ok d ℓ
    have hS := tzSumO_bound (tzDCO d ℓ) (gvO orc a r0 R0 ℓ j (tzStageO orc a r0 R0 ℓ P0 ω j)) (tBb d)
      (tzY d (triBgQ d) (ω j)) hR0 hRB hAl hAB hPG hPGB (2 ^ triNeTQ d ℓ)
    have hK0 : (0 : ℤ) ≤ 2 ^ tGcT d ℓ + d * (((2 ^ triNeTQ d ℓ : ℕ) : ℤ) * (tzDCO d ℓ).Bh) := by
      have : (0 : ℤ) ≤ (tzDCO d ℓ).Bh := hR0.trans hRB
      positivity
    obtain ⟨c1, c2⟩ := tzComp_bound (tzStageO orc a r0 R0 ℓ P0 ω j)
      (stSumO orc a r0 R0 ℓ j (tzStageO orc a r0 R0 ℓ P0 ω j) (ω j)) (tGcT d ℓ)
      (H := H * (2 ^ tGcT d ℓ + d * (((2 ^ triNeTQ d ℓ : ℕ) : ℤ) * (tzDCO d ℓ).Bh)) ^ j)
      (M := ((2 ^ triNeTQ d ℓ : ℕ) : ℤ) * (tzDCO d ℓ).Bh) (by positivity)
      (mul_nonneg (by positivity) (hR0.trans hRB)) h1 h2 hS.1 hS.2
    refine ⟨?_, fun i => (c1 i).trans_eq (by ring), fun i l => (c2 i l).trans_eq (by ring)⟩
    rw [tzStageO_succ]
    simp only [tzComp, hD]
    ring

/-- **The magnitudes of the stages** from the exponents. -/
theorem triMagO_of {Ce ke : ℕ} (hexp : TriExpO Ce ke) : TriMagO (Ce + 2) (ke + 1) := by
  intro d n orc δ r0 R0 a Da Na rn rd ω j hI hP hj
  obtain ⟨eX1, -, -⟩ := hexp d n δ r0 R0 a hI
  obtain ⟨hDa0, hDa, hNa, -, hrn0, hrn, hrd0, hrd, -⟩ := hP
  have hm : triMstQ r0 R0 ≤ WT d n δ r0 R0 a := mst_le_wU a hI
  have hLa := triLa_ge d
  obtain ⟨hR0, hRB, -, -, -, -⟩ := tzDCO_ok d (ellO d n δ r0 R0)
  set ℓ := ellO d n δ r0 R0 with hℓdef
  set W := WT d n δ r0 R0 a with hWdef
  -- the first position
  have hW2 : (2 : ℤ) ^ W * 2 ^ W = 2 ^ (2 * W) := by rw [← pow_add]; ring_nf
  have hH0 : ∀ x y : ℤ, |x| < 2 ^ W → |y| < 2 ^ W → |x * y| ≤ 2 ^ (2 * W) := fun x y hx hy => by
    rw [abs_mul, ← hW2]; exact mul_le_mul hx.le hy.le (abs_nonneg _) (by positivity)
  have bmu : ∀ i, |(tzP0 Da Na rn rd).mu i| ≤ 2 ^ (2 * W) := fun i => hH0 _ _ (hNa i)
    (by rw [abs_of_pos hrd0]; exact hrd)
  have bT : ∀ i l, |(tzP0 Da Na rn rd).T i l| ≤ 2 ^ (2 * W) := fun i l => by
    simp only [tzP0, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one]
      exact hH0 _ _ (by rw [abs_of_pos hDa0]; exact hDa) (by rw [abs_of_pos hrn0]; exact hrn)
    · simp
  obtain ⟨hD, h1, h2⟩ := tzStageO_bound orc a r0 R0 ℓ (tzP0 Da Na rn rd) ω (by positivity) bmu bT j
  -- the factor of a stage
  have hK : (2 : ℤ) ^ tGcT d ℓ + d * (((2 ^ triNeTQ d ℓ : ℕ) : ℤ) * (tzDCO d ℓ).Bh) ≤
      2 ^ (triLa (triSQ d) + tGcT d ℓ + d + 1) := by
    have hB := tzDCO_Bh_le d ℓ
    have hdd : (d : ℤ) ≤ 2 ^ d := by exact_mod_cast Nat.lt_two_pow_self.le
    have e1 : (2 : ℤ) ^ triNeTQ d ℓ * 2 ^ (triLa (triSQ d) + tGT d ℓ) = 2 ^ (triLa (triSQ d) + tGcT d ℓ) := by
      rw [← pow_add]; congr 1; unfold tGcT; ring
    have e2 : (2 : ℤ) ^ (triLa (triSQ d) + tGcT d ℓ + d + 1) =
        2 * (2 ^ d * 2 ^ (triLa (triSQ d) + tGcT d ℓ)) := by
      rw [pow_succ, pow_add, mul_comm ((2 : ℤ) ^ (triLa (triSQ d) + tGcT d ℓ))]; ring
    have e3 : (2 : ℤ) ^ tGcT d ℓ ≤ 2 ^ (triLa (triSQ d) + tGcT d ℓ) := pow_le_pow_right₀ (by norm_num) (by omega)
    have e4 : (d : ℤ) * (((2 ^ triNeTQ d ℓ : ℕ) : ℤ) * (tzDCO d ℓ).Bh) ≤
        2 ^ d * 2 ^ (triLa (triSQ d) + tGcT d ℓ) := by
      push_cast
      rw [← e1]
      have : (2 : ℤ) ^ triNeTQ d ℓ * (tzDCO d ℓ).Bh ≤ 2 ^ triNeTQ d ℓ * 2 ^ (triLa (triSQ d) + tGT d ℓ) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
      exact mul_le_mul hdd this (mul_nonneg (by positivity) (hR0.trans hRB)) (by positivity)
    have e5 : (1 : ℤ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
    have e6 : (0 : ℤ) ≤ 2 ^ (triLa (triSQ d) + tGcT d ℓ) := by positivity
    rw [e2]; nlinarith
  have hκ : triLa (triSQ d) + tGcT d ℓ + d + 1 ≤ Ce * (W + 1) ^ ke := by omega
  have hB : 2 * W + j * (triLa (triSQ d) + tGcT d ℓ + d + 1) ≤ (Ce + 2) * (W + 1) ^ (ke + 1) := by
    have hjW : j ≤ W := hj.trans hm
    have a1 : j * (triLa (triSQ d) + tGcT d ℓ + d + 1) ≤ (W + 1) * (Ce * (W + 1) ^ ke) :=
      Nat.mul_le_mul (by omega) hκ
    have a2 : W + 1 ≤ (W + 1) ^ (ke + 1) := by
      calc W + 1 = (W + 1) ^ 1 := (pow_one _).symm
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
    have a3 : (W + 1) * (Ce * (W + 1) ^ ke) = Ce * (W + 1) ^ (ke + 1) := by ring
    have a4 : (Ce + 2) * (W + 1) ^ (ke + 1) = Ce * (W + 1) ^ (ke + 1) + 2 * (W + 1) ^ (ke + 1) := by ring
    omega
  have hKj : ((2 : ℤ) ^ tGcT d ℓ + d * (((2 ^ triNeTQ d ℓ : ℕ) : ℤ) * (tzDCO d ℓ).Bh)) ^ j ≤
      2 ^ (j * (triLa (triSQ d) + tGcT d ℓ + d + 1)) := by
    rw [show j * (triLa (triSQ d) + tGcT d ℓ + d + 1) = (triLa (triSQ d) + tGcT d ℓ + d + 1) * j from
      Nat.mul_comm _ _, pow_mul]
    exact pow_le_pow_left₀ (by have : (0 : ℤ) ≤ (tzDCO d ℓ).Bh := hR0.trans hRB; positivity) hK j
  have hfin : ∀ x : ℤ, |x| ≤ 2 ^ (2 * W) *
      ((2 : ℤ) ^ tGcT d ℓ + d * (((2 ^ triNeTQ d ℓ : ℕ) : ℤ) * (tzDCO d ℓ).Bh)) ^ j →
      |x| ≤ 2 ^ ((Ce + 2) * (W + 1) ^ (ke + 1)) := fun x hx => by
    calc |x| ≤ 2 ^ (2 * W) * 2 ^ (j * (triLa (triSQ d) + tGcT d ℓ + d + 1)) :=
          hx.trans (mul_le_mul_of_nonneg_left hKj (by positivity))
      _ = 2 ^ (2 * W + j * (triLa (triSQ d) + tGcT d ℓ + d + 1)) := by rw [← pow_add]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hB
  refine ⟨?_, ?_, fun l => hfin _ (h1 l), fun i l => hfin _ (h2 i l)⟩
  · rw [hD]; simp only [tzP0]; positivity
  · rw [hD]
    simp only [tzP0]
    have hDr : Da * rd ≤ 2 ^ (2 * W) := by
      have := hH0 Da rd (by rw [abs_of_pos hDa0]; exact hDa) (by rw [abs_of_pos hrd0]; exact hrd)
      rwa [abs_of_pos (mul_pos hDa0 hrd0)] at this
    calc Da * rd * 2 ^ (j * tGcT d ℓ) ≤ 2 ^ (2 * W) * 2 ^ (j * (triLa (triSQ d) + tGcT d ℓ + d + 1)) :=
          mul_le_mul hDr (pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ (by omega))) (by positivity)
            (by positivity)
      _ = 2 ^ (2 * W + j * (triLa (triSQ d) + tGcT d ℓ + d + 1)) := by rw [← pow_add]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hB

/-! ## The exponents of the constants -/

theorem clog_ceil_le {x : ℚ} {m : ℕ} (h : x ≤ 2 ^ m) : Nat.clog 2 ⌈x⌉₊ ≤ m :=
  Nat.clog_le_of_le_pow (Nat.ceil_le.2 (by exact_mod_cast h))

theorem pow_le_two_pow (d k : ℕ) : d ^ k ≤ 2 ^ (k * d) := by
  calc d ^ k ≤ (2 ^ d) ^ k := Nat.pow_le_pow_left Nat.lt_two_pow_self.le k
    _ = 2 ^ (k * d) := by rw [← pow_mul, mul_comm]

theorem eloI_le_pow {d : ℕ} (hd : 1 ≤ d) : eloI d ≤ 2 ^ (112 + 14 * d) := by
  rw [pow_add]; exact (eloI_le hd).trans (Nat.mul_le_mul_left _ (pow_le_two_pow d 14))

theorem triE1Q_le {d : ℕ} (hd : 1 ≤ d) : triE1Q d ≤ 112 + 14 * d := by
  unfold triE1Q
  apply clog_ceil_le
  rw [triEloQ_eq hd, div_div_eq_mul_div]
  have hpos : (0 : ℚ) ≤ eloI d := by positivity
  have hN : (eloI d : ℚ) ≤ 2 ^ (112 + 14 * d) := by exact_mod_cast eloI_le_pow hd
  linarith

theorem triETauQ_le {d : ℕ} (hd : 1 ≤ d) : triETauQ d ≤ 367 + 51 * d := by
  unfold triETauQ
  apply clog_ceil_le
  rw [triEloQ_eq hd, triD2Q_eq hd, div_div_eq_mul_div]
  have h4 : (1 : ℚ) ≤ 4 ^ triJaQ d := one_le_pow₀ (by norm_num)
  have hD2 : (d2N d : ℚ) / 4 ^ triJaQ d ≤ d2N d := div_le_self (by positivity) h4
  have b2 : 1 + 8 * d * triKgQ d ≤ 2 ^ (158 + 22 * d) := by
    have hK : 8 * d * triKgQ d ≤ 8 * d * (2 ^ 154 * d ^ 21) := Nat.mul_le_mul_left _ (triKgQ_le hd)
    have e1 : 8 * d * (2 ^ 154 * d ^ 21) = 2 ^ 157 * d ^ 22 := by ring
    have e2 : 1 ≤ 2 ^ 157 * d ^ 22 := Nat.one_le_iff_ne_zero.2 (by positivity)
    have e3 : 2 ^ 158 * d ^ 22 ≤ 2 ^ 158 * 2 ^ (22 * d) := Nat.mul_le_mul_left _ (pow_le_two_pow d 22)
    have e4 : 2 ^ 158 * d ^ 22 = 2 ^ 157 * d ^ 22 + 2 ^ 157 * d ^ 22 := by ring
    rw [pow_add]
    generalize 2 ^ 157 * d ^ 22 = A at e1 e2 e4
    generalize 2 ^ 158 * d ^ 22 = A' at e3 e4
    omega
  have b3 : d2N d + 1 ≤ 2 ^ (91 + 14 * d) := by
    have e3 : 2 ^ 91 * d ^ 14 ≤ 2 ^ 91 * 2 ^ (14 * d) := Nat.mul_le_mul_left _ (pow_le_two_pow d 14)
    have e4 : 2 ^ 91 * d ^ 14 = 2 ^ 90 * d ^ 14 + 2 ^ 90 * d ^ 14 := by ring
    have e2 : 1 ≤ 2 ^ 90 * d ^ 14 := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hD := d2N_le hd
    rw [pow_add]
    generalize 2 ^ 90 * d ^ 14 = A at hD e2 e4
    generalize 2 ^ 91 * d ^ 14 = A' at e3 e4
    omega
  have hN : 64 * d * (1 + 8 * d * triKgQ d) * (d2N d + 1) * eloI d ≤ 2 ^ (367 + 51 * d) := by
    calc 64 * d * (1 + 8 * d * triKgQ d) * (d2N d + 1) * eloI d ≤
          2 ^ 6 * 2 ^ d * 2 ^ (158 + 22 * d) * 2 ^ (91 + 14 * d) * 2 ^ (112 + 14 * d) := by
          gcongr
          · norm_num
          · exact Nat.lt_two_pow_self.le
          · exact eloI_le_pow hd
      _ = 2 ^ (367 + 51 * d) := by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]; congr 1; ring
  calc (64 : ℚ) * d * (1 + 8 * d * triKgQ d) * (d2N d / 4 ^ triJaQ d + 1) * eloI d / 20000 ≤
        64 * d * (1 + 8 * d * triKgQ d) * (d2N d + 1) * eloI d / 20000 := by gcongr
    _ ≤ ((64 * d * (1 + 8 * d * triKgQ d) * (d2N d + 1) * eloI d : ℕ) : ℚ) := by
        push_cast
        have : (0 : ℚ) ≤ 64 * d * (1 + 8 * d * triKgQ d) * (d2N d + 1) * eloI d := by positivity
        linarith
    _ ≤ 2 ^ (367 + 51 * d) := by exact_mod_cast hN

theorem stEH_le {d : ℕ} (hd : 1 ≤ d) : stEH d ≤ 190 + 27 * d := by
  unfold stEH
  apply clog_ceil_le
  have hLa := triLa_ge d
  have hR : triRQ d ≤ 2 ^ triLa (triSQ d) := by
    unfold triRQ; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hB : triBQ d ≤ 2 ^ triLa (triSQ d) := by
    unfold triBQ
    calc (161 : ℚ) * 2 ^ (triLa (triSQ d) - 10) ≤ 2 ^ 10 * 2 ^ (triLa (triSQ d) - 10) := by gcongr; norm_num
      _ = 2 ^ triLa (triSQ d) := by rw [← pow_add]; congr 1; omega
  have hLp : (2 : ℚ) ^ triLa (triSQ d) ≤ 2 ^ 32 * (d : ℚ) ^ 4 := by exact_mod_cast pow_triLa_le hd
  have hK : (triKgQ d : ℚ) ≤ 2 ^ 154 * (d : ℚ) ^ 21 := by exact_mod_cast triKgQ_le hd
  have hd1 : (1 : ℚ) ≤ d := by exact_mod_cast hd
  have hN : (d : ℚ) * (2 ^ 32 * d ^ 4) + 8 * d ^ 2 * (2 ^ 154 * d ^ 21) * (2 ^ 32 * d ^ 4) + 1 ≤
      2 ^ 190 * (d : ℚ) ^ 27 := by
    have p5 : (d : ℚ) ^ 5 ≤ d ^ 27 := pow_le_pow_right₀ hd1 (by norm_num)
    have p0 : (1 : ℚ) ≤ d ^ 27 := one_le_pow₀ hd1
    nlinarith
  have h27 : (d : ℚ) ^ 27 ≤ 2 ^ (27 * d) := by exact_mod_cast pow_le_two_pow d 27
  have hRB : 0 ≤ triRQ d := by unfold triRQ; positivity
  have hBB : 0 ≤ triBQ d := by unfold triBQ; positivity
  unfold triRzQ
  calc (d : ℚ) * triRQ d + 8 * d ^ 2 * triKgQ d * triBQ d + 1 ≤
        (d : ℚ) * (2 ^ 32 * d ^ 4) + 8 * d ^ 2 * (2 ^ 154 * d ^ 21) * (2 ^ 32 * d ^ 4) + 1 := by
        gcongr
        · exact hR.trans hLp
        · exact hB.trans hLp
    _ ≤ 2 ^ 190 * (d : ℚ) ^ 27 := hN
    _ ≤ 2 ^ 190 * 2 ^ (27 * d) := by gcongr
    _ = 2 ^ (190 + 27 * d) := by rw [← pow_add]

/-- **The exponents of the constants of TRI-OGD-O** at `2^170 (W + 1)^21`. -/
theorem triExpS : TriExpS (2 ^ 170) 21 := by
  intro d n δ r0 R0 a hI
  have hd := hI.hd
  have hℓ := ellO_le a hI
  have hdW : d ≤ WT d n δ r0 R0 a := by simp only [WT, wU]; omega
  have hLa := triLa_le_lin hd
  have hLh := triLh_le_lin hd
  have hBv := triBvQ_le_lin hd
  have hJa := triJaQ_le_lin hd
  have hNe := triNeQ_le_lin hd (ellO d n δ r0 R0)
  have hJs := triJsQ_le_lin hd (ellO d n δ r0 R0)
  have hJsT := triJsTQ_le hd (ellO d n δ r0 R0)
  have hP := tzP_le hd
  have hE1 := triE1Q_le hd
  have hEt := triETauQ_le hd
  have hEH := stEH_le hd
  have hSQ := (triSQ_bounds d).2
  have m1 : d * triETauQ d ≤ 367 * d + 51 * (d * d) := by nlinarith
  have hG : tGcT d (ellO d n δ r0 R0) = triBvQ d + triJsTQ d (ellO d n δ r0 R0) + triJaQ d +
      (triNeQ d (ellO d n δ r0 R0) + 1) := rfl
  have hE : stE d = triE1Q d + 1 + d * (2 * (triETauQ d + 3) + 6 + triETauQ d) := rfl
  have hEta : stEEta d = triETauQ d + (triE1Q d + 1) + 11 + 3 * d * (triETauQ d + 4) := rfl
  have hJ : stJ d = stEEta d + stEH d + 1 := rfl
  have hU : stEu d = stEEta d + 1 := rfl
  have q1 : d * (2 * (triETauQ d + 3) + 6 + triETauQ d) = 3 * (d * triETauQ d) + 12 * d := by ring
  have q2 : 3 * d * (triETauQ d + 4) = 3 * (d * triETauQ d) + 12 * d := by ring
  have T : triLa (triSQ d) + triLh (triSQ d) + triJaQ d + triBvQ d + 2 * tzP d + tGcT d (ellO d n δ r0 R0) +
      stE d + triETauQ d + stJ d + stEu d + triSQ d ≤
      6000 + 6000 * d + 459 * (d * d) + 2 * tzP d + 2 * ellO d n δ r0 R0 := by
    rw [hG, hJ, hU, hEta, hE, q1, q2]
    omega
  refine T.trans ?_
  generalize ellO d n δ r0 R0 = ℓ at hℓ ⊢
  generalize WT d n δ r0 R0 a = W at hℓ hdW ⊢
  have hdV : d < W + 1 := by omega
  have hℓV : ℓ ≤ 3 * (W + 1) + 19 := by omega
  generalize W + 1 = V at hdV hℓV ⊢
  have hV : 1 ≤ V := by omega
  have z1 : V ≤ V ^ 21 := by
    calc V = V ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right hV (by norm_num)
  have z2 : d * d ≤ V ^ 21 := by
    calc d * d ≤ V * V := Nat.mul_le_mul hdV.le hdV.le
      _ = V ^ 2 := (sq V).symm
      _ ≤ _ := Nat.pow_le_pow_right hV (by norm_num)
  have z3 : 2 * tzP d ≤ 2 ^ 159 * V ^ 21 := by
    calc 2 * tzP d ≤ 2 * (2 ^ 158 * d ^ 21) := by omega
      _ ≤ 2 * (2 ^ 158 * V ^ 21) := by gcongr
      _ = 2 ^ 159 * V ^ 21 := by ring
  have z4 : 12503 * V ^ 21 + 2 ^ 159 * V ^ 21 ≤ 2 ^ 170 * V ^ 21 := by
    rw [← add_mul]
    exact Nat.mul_le_mul_right _ (by norm_num)
  generalize V ^ 21 = Z at z1 z2 z3 z4
  generalize 2 ^ 159 * Z = A at z3 z4
  generalize 2 ^ 170 * Z = R at z4 ⊢
  omega

end AdversarialBco.Unified.ProgO.TriO
