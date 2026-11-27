/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EllSpec
public import AdversarialBco.Bit.ApQ.Ell

@[expose] public section

/-!
# UNI-ELL: the SEP cut keeps the deep points of the K-part

The keep-ball computation of ELL-cap (Df2OracleProof `step2_cut`) at a centre `x̄` that a
test rejects with the band `η` (`γ(x̄) > 1 - η`, `γ` the gauge of the K-part `QK` about its centre `c`), from a
`τ`-subgradient `g` of `γ` at a point `y` within `2ℓ₁` of `x̄`.

* `keep_cut`: if `η`, `2ℓ₁/r_K` and `τ√d M` are at most `ε/(16M)`, `2ℓ₁ ≤ ε/2`, `ε ≤ 1 ≤ M/4` and `|y - c| ≤ M`,
  then `g ≠ 0` and `⟨g, z - x̄⟩ < 0` for every `z` with `B̄(z, ε) ⊆ QK` and `|z - y| + ε ≤ M`. The lower bound on `|g|`
  comes from `γ(c) = 0`: `⟨g, y - c⟩ ≥ γ(y) - τ√d M > 61/64`.
-/

namespace AdversarialBco.Uni.EllO

open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.LeanAp Matrix

variable {d : ℕ}

theorem keep_cut {QK : Set (Fin d → ℝ)} {c : Fin d → ℝ} {rK RK : ℝ}
    (hQ : Convex ℝ QK) (hcl : IsClosed QK) (hr : 0 < rK) (hball : oBall c rK ⊆ QK) (hQR : QK ⊆ oBall 0 RK)
    {xb y g : Fin d → ℝ} {η τ ℓ1 ε M : ℝ}
    (hγx : 1 - η < oGauge QK c xb) (hy : oNorm (y - xb) ≤ 2 * ℓ1)
    (hsub : ∀ z, oGauge QK c y + g ⬝ᵥ (z - y) - τ * ∑ i, |z i - y i| ≤ oGauge QK c z)
    (hτ : 0 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hM : 4 ≤ M)
    (hη : η ≤ ε / (16 * M)) (hℓr : 2 * ℓ1 / rK ≤ ε / (16 * M)) (hτM : τ * Real.sqrt d * M ≤ ε / (16 * M))
    (hℓε : 2 * ℓ1 ≤ ε / 2) (hyc : oNorm (y - c) ≤ M) :
    g ≠ 0 ∧ ∀ z, oBall z ε ⊆ QK → oNorm (z - y) + ε ≤ M → g ⬝ᵥ (z - xb) < 0 := by
  obtain ⟨-, hLip, hbd, hmem⟩ := Poly.lemmaGAUGE d QK c rK RK hQ hcl hr hball hQR
  set γ := oGauge QK c with hγ
  have hM0 : 0 < M := by linarith
  have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  set a := ε / (16 * M) with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 / 64 := by
    rw [ha, div_le_iff₀ (by positivity)]; nlinarith
  have hγc : γ c = 0 := by
    have := hbd c
    simp only [sub_self, oNorm_zero, zero_div] at this
    linarith [this.1, this.2]
  -- the gauge at `y`
  have hγy : 1 - η - 2 * ℓ1 / rK < γ y := by
    have h1 := hLip xb y
    rw [abs_le, oNorm_sub_comm] at h1
    have h2 : 1 / rK * oNorm (y - xb) ≤ 2 * ℓ1 / rK := by
      rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right hy hr.le
    linarith [h1.1]
  have hl1 : ∀ z, ∑ i, |z i - y i| ≤ Real.sqrt d * oNorm (z - y) := fun z => by
    have := l1_le_sqrt_mul (z - y)
    simpa only [Pi.sub_apply] using this
  -- the lower bound on `|g|` through `γ(c) = 0`
  have hgc : 1 - 3 * a < g ⬝ᵥ (y - c) := by
    have h1 := hsub c
    rw [hγc] at h1
    have h2 : τ * ∑ i, |c i - y i| ≤ τ * Real.sqrt d * M := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hτ
      calc ∑ i, |c i - y i| ≤ Real.sqrt d * oNorm (c - y) := hl1 c
        _ ≤ Real.sqrt d * M := by rw [oNorm_sub_comm]; exact mul_le_mul_of_nonneg_left hyc hsd
    have h3 : g ⬝ᵥ (c - y) = -(g ⬝ᵥ (y - c)) := by rw [← dotProduct_neg, neg_sub]
    linarith
  have hgM : g ⬝ᵥ (y - c) ≤ oNorm g * M :=
    (dot_le g (y - c)).trans (mul_le_mul_of_nonneg_left hyc (oNorm_nonneg g))
  have hgn : 61 / 64 < oNorm g * M := by linarith
  have hgpos : 0 < oNorm g := by
    by_contra h0
    have : oNorm g = 0 := le_antisymm (not_lt.mp h0) (oNorm_nonneg g)
    rw [this, zero_mul] at hgn
    linarith
  refine ⟨fun h0 => by rw [h0, oNorm_zero] at hgpos; exact lt_irrefl 0 hgpos, ?_⟩
  intro z hzball hzM
  set z' := z + (ε / oNorm g) • g with hz'
  have hz'z : oNorm (z' - z) = ε := by
    rw [hz', add_sub_cancel_left, oNorm_smul, abs_of_pos (by positivity)]
    field_simp
  have hz'Q : z' ∈ QK := hzball (by simp only [oBall, Set.mem_ofPred_eq]; rw [hz'z])
  have hγz' : γ z' ≤ 1 := (hmem z').mpr hz'Q
  have h1 := hsub z'
  have hgg : g ⬝ᵥ g = oNorm g ^ 2 := (oNorm_sq g).symm
  have h2 : g ⬝ᵥ (z' - y) = g ⬝ᵥ (z - y) + ε * oNorm g := by
    rw [hz', show z + (ε / oNorm g) • g - y = (z - y) + (ε / oNorm g) • g by abel, dotProduct_add,
      dotProduct_smul, hgg, smul_eq_mul]
    field_simp
  have h3 : τ * ∑ i, |z' i - y i| ≤ τ * Real.sqrt d * M := by
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hτ
    calc ∑ i, |z' i - y i| ≤ Real.sqrt d * oNorm (z' - y) := hl1 z'
      _ ≤ Real.sqrt d * M := by
          apply mul_le_mul_of_nonneg_left _ hsd
          calc oNorm (z' - y) ≤ oNorm (z' - z) + oNorm (z - y) := oNorm_sub_sub_le z' z y
            _ ≤ M := by rw [hz'z]; linarith
  have h4 : g ⬝ᵥ (z - y) < 3 * a - ε * oNorm g := by linarith
  have h5 : g ⬝ᵥ (y - xb) ≤ oNorm g * (2 * ℓ1) :=
    (dot_le g (y - xb)).trans (mul_le_mul_of_nonneg_left hy (oNorm_nonneg g))
  have h6 : g ⬝ᵥ (z - xb) = g ⬝ᵥ (z - y) + g ⬝ᵥ (y - xb) := by
    rw [← dotProduct_add]; congr 1; abel
  have h7 : oNorm g * (2 * ℓ1) ≤ oNorm g * (ε / 2) := mul_le_mul_of_nonneg_left hℓε (oNorm_nonneg g)
  -- `3a ≤ ε |g| / 2`
  have h8 : 3 * a < ε * oNorm g / 2 := by
    have e1 : 3 * a * M = 3 * ε / 16 := by rw [ha]; field_simp
    have e2 : ε * (61 / 64) / 2 < ε * (oNorm g * M) / 2 := by
      apply div_lt_div_of_pos_right _ two_pos; exact mul_lt_mul_of_pos_left hgn hε
    have e3 : 3 * a * M < ε * oNorm g / 2 * M := by nlinarith
    exact lt_of_mul_lt_mul_right e3 hM0.le
  linarith


/-! ## Casts and powers of two -/

open AdversarialBco.Bit.ApQ (vR vZ)

theorem qR_ptDN_pow (s : ℕ) (a : Fin d → ℤ) : qR (ptDN (2 ^ s) a) = vR s a := by
  funext i; simp [qR, ptDN, vR]

theorem qR_ptDN_grid (E : ℕ) (X : Fin d → ℤ) : qR (ptDN (2 ^ E) X) = gridR E X := by
  funext i; simp [qR, ptDN, gridR]

theorem gridR_shift {E s : ℕ} (h : s ≤ E) (a : Fin d → ℤ) : gridR E ((2 : ℤ) ^ (E - s) • a) = vR s a := by
  funext i
  obtain ⟨t, rfl⟩ : ∃ t, E = s + t := ⟨E - s, by omega⟩
  simp only [gridR, vR, Pi.smul_apply, smul_eq_mul, Nat.add_sub_cancel_left]
  push_cast
  rw [pow_add]
  field_simp

theorem ip_le {m n : ℕ} (h : m ≤ n) : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ m :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

theorem ip_le_one (n : ℕ) : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

theorem pow_mul_ip (a b : ℕ) : (2 : ℝ) ^ a * (2 : ℝ)⁻¹ ^ (a + b) = (2 : ℝ)⁻¹ ^ b := by
  rw [pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow, one_mul]

theorem ip_div16 (j m : ℕ) : (2 : ℝ)⁻¹ ^ j / (16 * 2 ^ m) = (2 : ℝ)⁻¹ ^ (j + 4 + m) := by
  rw [pow_add, pow_add, inv_pow, inv_pow, inv_pow]
  field_simp
  norm_num

theorem sqrt_le_clog (hd : 1 ≤ d) : Real.sqrt d ≤ 2 ^ Nat.clog 2 d := by
  have h1 : Real.sqrt d ≤ d := Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast hd))
  have h2 : (d : ℝ) ≤ 2 ^ Nat.clog 2 d := by exact_mod_cast Nat.le_pow_clog (by norm_num) d
  linarith

/-- `M = 2^{eM} ≥ 4 R̄`. -/
theorem eM_ge (I : EllOI d) : 4 * (I.base.Rb : ℝ) ≤ 2 ^ I.eM := by
  have h := Nat.le_pow_clog (by norm_num : 1 < 2) I.base.Rb
  have h' : (I.base.Rb : ℝ) ≤ 2 ^ Nat.clog 2 I.base.Rb := by exact_mod_cast h
  rw [EllOI.eM, pow_add]
  norm_num
  linarith

/-! ## Step 2 of ELL-O on a reject -/

/-- **The SEP cut of ELL-O.** At a centre `a/2^s` in the ball of radius `R` that the test `T` rejects, for a test that
certifies `QK` about `c` with a band `η ≤ 2^{-eK}`: SEP returns `(Y, G)`, `G ≠ 0`, and the cut `G` at `a/2^s` keeps
every point `z` of norm at most `R` with `B̄(z, ρ) ⊆ QK`, `ρ = 2^{-j}`. -/
theorem sep_branch (hSA : SepAcc) (hGA : GaugeAcc) (I : EllOI d) (T : (Fin d → ℚ) → Bool) (QK : Set (Fin d → ℝ))
    (RK η : ℝ) (s : ℕ) (a : Fin d → ℤ) (hd : 1 ≤ d) (hR : 1 ≤ I.R) (hQ : Convex ℝ QK) (hcl : IsClosed QK)
    (hQR : QK ⊆ oBall 0 RK) (hball : oBall (qR I.c) ((2 : ℝ)⁻¹ ^ I.erK) ⊆ QK) (hc : oNorm (qR I.c) ≤ I.R)
    (hT : TestCert T QK (qR I.c) η) (hη0 : 0 ≤ η) (hη : η ≤ (2 : ℝ)⁻¹ ^ I.eK)
    (hbox : oNorm (vR s a) ≤ I.R) (hrej : T (ptDN (2 ^ s) a) = false) :
    ∃ Y G, sepE (I.evO T (I.sepEx s)) ((2 : ℤ) ^ (I.sepEx s - s) • a) (I.sepEx s) I.e1 I.eτ I.eL I.eu =
        some (Y, G) ∧ G ≠ 0 ∧
      ∀ z, oBall z ((2 : ℝ)⁻¹ ^ I.base.j) ⊆ QK → oNorm z ≤ I.R → vZ G ⬝ᵥ (z - vR s a) < 0 := by
  set E := I.sepEx s with hEdef
  have hsE : s ≤ E := by rw [hEdef, EllOI.sepEx]; omega
  set Y0 := (2 : ℤ) ^ (E - s) • a with hY0
  have hxb : gridR E Y0 = vR s a := gridR_shift hsE a
  set rK : ℝ := (2 : ℝ)⁻¹ ^ I.erK with hrKdef
  have hrK : 0 < rK := by positivity
  set c := qR I.c with hcdef
  set γ := oGauge QK c with hγ
  obtain ⟨hconv, hLip, hbd, -⟩ := Poly.lemmaGAUGE d QK c rK RK hQ hcl hrK hball hQR
  have hcQ : c ∈ QK := hball (show oNorm (c - c) ≤ rK by rw [sub_self, oNorm_zero]; exact hrK.le)
  have hRK : 0 ≤ RK := le_trans (oNorm_nonneg (c - 0)) (hQR hcQ)
  have hrinv : 1 / rK = 2 ^ I.eL := by rw [hrKdef, EllOI.eL, inv_pow, one_div, inv_inv]
  have hLip' : ∀ x y, |γ x - γ y| ≤ 2 ^ I.eL * oNorm (x - y) := fun x y => by
    have := hLip x y; rwa [hrinv] at this
  -- the radii
  obtain ⟨hRb1, hRRb⟩ := Bit.ApQ.Rb_spec I.base hR
  have hRb1' : (1 : ℝ) ≤ I.base.Rb := by exact_mod_cast hRb1
  have hRRb' : (I.R : ℝ) ≤ I.base.Rb := by exact_mod_cast hRRb
  have hM := eM_ge I
  have hℓ1 : (2 : ℝ)⁻¹ ^ I.e1 ≤ 1 / 32 := by
    calc (2 : ℝ)⁻¹ ^ I.e1 ≤ (2 : ℝ)⁻¹ ^ 5 := ip_le (by rw [EllOI.e1]; omega)
      _ = 1 / 32 := by norm_num
  have hη1 : η ≤ 1 / 4 := by
    calc η ≤ (2 : ℝ)⁻¹ ^ I.eK := hη
      _ ≤ (2 : ℝ)⁻¹ ^ 2 := ip_le (by rw [EllOI.eK]; omega)
      _ = 1 / 4 := by norm_num
  -- the accuracy of the gauge's values at SEP's points
  have hacc : ∀ X, oNorm (gridR E X - gridR E Y0) ≤ 2 * (2 : ℝ)⁻¹ ^ I.e1 →
      |(I.evO T E X : ℝ) / 2 ^ I.eu - γ (gridR E X)| ≤
        (2 : ℝ)⁻¹ ^ I.eτ * (2 : ℝ)⁻¹ ^ I.e1 / 1600 * (2 : ℝ)⁻¹ ^ (3 * d * (I.eL + I.eτ + 4)) := by
    intro X hX
    set x := ptDN (2 ^ E) X with hx
    have hqx : qR x = gridR E X := qR_ptDN_grid E X
    have hxc : oNorm (gridR E X - c) ≤ 2 ^ I.eM := by
      have h1 : oNorm (gridR E X - c) ≤ oNorm (gridR E X - gridR E Y0) + oNorm (gridR E Y0 - c) :=
        oNorm_sub_sub_le _ _ _
      have h2 : oNorm (gridR E Y0 - c) ≤ oNorm (gridR E Y0) + oNorm c := oNorm_sub_le _ _
      rw [hxb] at h1 h2 hX
      linarith
    have hγH : γ (qR x) ≤ ((2 : ℚ) ^ I.eH : ℚ) := by
      rw [hqx]
      have h1 := (hbd (gridR E X)).2
      have h2 : oNorm (gridR E X - c) / rK ≤ 2 ^ I.eM / rK := div_le_div_of_nonneg_right hxc hrK.le
      have h3 : (2 : ℝ) ^ I.eM / rK = 2 ^ I.eH := by
        rw [div_eq_mul_one_div, hrinv, EllOI.eH, EllOI.eL, pow_add]
      push_cast
      linarith
    obtain ⟨hg1, hg2⟩ := hGA d T QK I.c x ((2 : ℚ) ^ I.eH) I.jg η hη0 (by linarith) hT (by positivity) hγH
    have hev : (I.evO T E X : ℝ) / 2 ^ I.eu = (gaugeQ T I.c x ((2 : ℚ) ^ I.eH) I.jg : ℝ) := by
      simp only [EllOI.evO, gaugeQ]
      push_cast
      rw [show I.jg = I.eH + I.eu by rw [EllOI.jg, EllOI.eu]; ring, pow_add]
      field_simp
      rfl
    rw [hev, ← hqx]
    set gq : ℝ := (gaugeQ T I.c x ((2 : ℚ) ^ I.eH) I.jg : ℝ) with hgq
    set g0 := γ (qR x) with hg0
    have hg0n : 0 ≤ g0 := le_trans (div_nonneg (oNorm_nonneg _) (by linarith)) (hbd (qR x)).1
    have hH : g0 ≤ 2 ^ I.eH := by have := hγH; push_cast at this; exact this
    -- `gq - γ ≤ 2 H η + H/2^{jg} ≤ 2^{-eη}`
    have hdiv : g0 / (1 - η) ≤ g0 + 2 * η * 2 ^ I.eH := by
      rw [div_le_iff₀ (by linarith)]
      have hH0 : (0 : ℝ) ≤ 2 ^ I.eH := by positivity
      have hk : 0 ≤ 2 * 2 ^ I.eH - g0 - 2 * η * 2 ^ I.eH := by nlinarith
      nlinarith [mul_nonneg hη0 hk]
    have hHη : 2 * η * 2 ^ I.eH ≤ (2 : ℝ)⁻¹ ^ (I.eη + 1) := by
      have : (2 : ℝ) ^ I.eH * (2 : ℝ)⁻¹ ^ I.eK = (2 : ℝ)⁻¹ ^ (I.eη + 2) := by
        rw [show I.eK = I.eH + (I.eη + 2) by rw [EllOI.eK]; ring]; exact pow_mul_ip _ _
      have h2 : (2 : ℝ)⁻¹ ^ (I.eη + 2) = (2 : ℝ)⁻¹ ^ (I.eη + 1) / 2 := by rw [pow_succ]; ring
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) I.eH]
    have hHj : ((2 : ℚ) ^ I.eH : ℚ) / (2 : ℝ) ^ I.jg = (2 : ℝ)⁻¹ ^ (I.eη + 1) := by
      push_cast
      rw [div_eq_mul_inv, ← inv_pow, show I.jg = I.eH + (I.eη + 1) by rw [EllOI.jg]; ring]
      exact pow_mul_ip _ _
    have htarget : (2 : ℝ)⁻¹ ^ I.eη ≤
        (2 : ℝ)⁻¹ ^ I.eτ * (2 : ℝ)⁻¹ ^ I.e1 / 1600 * (2 : ℝ)⁻¹ ^ (3 * d * (I.eL + I.eτ + 4)) := by
      rw [EllOI.eη, pow_add, pow_add, pow_add]
      have h11 : (2 : ℝ)⁻¹ ^ 11 ≤ 1 / 1600 := by norm_num
      have hp : 0 ≤ (2 : ℝ)⁻¹ ^ I.eτ * (2 : ℝ)⁻¹ ^ I.e1 := by positivity
      have hq : 0 ≤ (2 : ℝ)⁻¹ ^ (3 * d * (I.eL + I.eτ + 4)) := by positivity
      calc (2 : ℝ)⁻¹ ^ I.eτ * (2 : ℝ)⁻¹ ^ I.e1 * (2 : ℝ)⁻¹ ^ 11 * (2 : ℝ)⁻¹ ^ (3 * d * (I.eL + I.eτ + 4))
          ≤ (2 : ℝ)⁻¹ ^ I.eτ * (2 : ℝ)⁻¹ ^ I.e1 * (1 / 1600) * (2 : ℝ)⁻¹ ^ (3 * d * (I.eL + I.eτ + 4)) := by gcongr
        _ = _ := by ring
    have hsum : (2 : ℝ)⁻¹ ^ (I.eη + 1) + (2 : ℝ)⁻¹ ^ (I.eη + 1) = (2 : ℝ)⁻¹ ^ I.eη := by rw [pow_succ]; ring
    rw [abs_of_nonneg (by linarith)]
    rw [hHj] at hg2
    linarith
  obtain ⟨Y, G, hsep, hY, hsub⟩ := hSA d γ (I.evO T E) Y0 E I.e1 I.eτ I.eL I.eu hd hconv hLip'
    (by rw [hEdef, EllOI.sepEx]; omega) hacc
  refine ⟨Y, G, hsep, ?_⟩
  set g : Fin d → ℝ := fun i => (G i : ℝ) / 2 ^ (I.eu + 1) with hgdef
  set y := gridR E Y with hydef
  rw [hxb] at hY
  have hgG : vZ G = (2 : ℝ) ^ (I.eu + 1) • g := by
    funext i; simp only [vZ, hgdef, Pi.smul_apply, smul_eq_mul]; field_simp
  -- the numeric conditions of `keep_cut`
  set ε : ℝ := (2 : ℝ)⁻¹ ^ I.base.j with hεdef
  set M : ℝ := 2 ^ I.eM with hMdef
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := ip_le_one _
  have hM4 : 4 ≤ M := by linarith
  have hε16 : ε / (16 * M) = (2 : ℝ)⁻¹ ^ (I.base.j + 4 + I.eM) := ip_div16 _ _
  have hηc : η ≤ ε / (16 * M) := by
    rw [hε16]; exact hη.trans (ip_le (by rw [EllOI.eK, EllOI.eη, EllOI.e1]; omega))
  have hℓr : 2 * (2 : ℝ)⁻¹ ^ I.e1 / rK ≤ ε / (16 * M) := by
    rw [hε16, div_eq_mul_one_div, hrinv, EllOI.eL]
    have : (2 : ℝ) ^ (I.erK + 1) * (2 : ℝ)⁻¹ ^ (I.erK + 1 + (I.base.j + 4 + I.eM)) =
        (2 : ℝ)⁻¹ ^ (I.base.j + 4 + I.eM) := pow_mul_ip _ _
    rw [show I.e1 = I.erK + 1 + (I.base.j + 4 + I.eM) by rw [EllOI.e1]; ring]
    rw [← this, pow_succ]
    ring_nf
    exact le_refl _
  have hτM : (2 : ℝ)⁻¹ ^ I.eτ * Real.sqrt d * M ≤ ε / (16 * M) := by
    rw [hε16]
    have hsq := sqrt_le_clog hd
    have e1 : (2 : ℝ)⁻¹ ^ I.eτ * (2 ^ Nat.clog 2 d * 2 ^ I.eM) = (2 : ℝ)⁻¹ ^ (I.base.j + 4 + I.eM) := by
      rw [← pow_add, show I.eτ = Nat.clog 2 d + I.eM + (I.base.j + 4 + I.eM) by rw [EllOI.eτ]; ring, mul_comm]
      exact pow_mul_ip _ _
    calc (2 : ℝ)⁻¹ ^ I.eτ * Real.sqrt d * M = (2 : ℝ)⁻¹ ^ I.eτ * (Real.sqrt d * 2 ^ I.eM) := by rw [hMdef]; ring
      _ ≤ (2 : ℝ)⁻¹ ^ I.eτ * (2 ^ Nat.clog 2 d * 2 ^ I.eM) := by gcongr
      _ = _ := e1
  have hℓε : 2 * (2 : ℝ)⁻¹ ^ I.e1 ≤ ε / 2 := by
    have h1 : (2 : ℝ)⁻¹ ^ I.e1 ≤ (2 : ℝ)⁻¹ ^ (I.base.j + 2) := ip_le (by rw [EllOI.e1]; omega)
    have h2 : (2 : ℝ)⁻¹ ^ (I.base.j + 2) = ε / 4 := by rw [hεdef, pow_add]; norm_num; ring
    linarith
  have hyn : oNorm y ≤ I.base.Rb + 1 := by
    have h1 : oNorm y ≤ oNorm (y - vR s a) + oNorm (vR s a) := by
      have := oNorm_add_le (y - vR s a) (vR s a); rwa [sub_add_cancel] at this
    have h2 : 64 / 63 * (2 : ℝ)⁻¹ ^ I.e1 ≤ 1 := by linarith
    linarith
  have hyc : oNorm (y - c) ≤ M := by
    have := oNorm_sub_le y c
    linarith
  have hy2 : oNorm (y - vR s a) ≤ 2 * (2 : ℝ)⁻¹ ^ I.e1 := by
    have : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ I.e1 := by positivity
    linarith
  have hγx : 1 - η < γ (vR s a) := by
    have := (hT (ptDN (2 ^ s) a)).2 hrej
    rwa [qR_ptDN_pow] at this
  obtain ⟨hg0, hcut⟩ := keep_cut hQ hcl hrK hball hQR hγx hy2 hsub (by positivity) hε0 hε1 hM4 hηc hℓr hτM hℓε hyc
  refine ⟨fun h0 => hg0 ?_, fun z hz hzR => ?_⟩
  · funext i; simp [hgdef, h0]
  · have hzy : oNorm (z - y) + ε ≤ M := by
      have := oNorm_sub_le z y
      linarith
    have h := hcut z hz hzy
    rw [hgG, smul_dotProduct, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (by positivity) h

end AdversarialBco.Uni.EllO
