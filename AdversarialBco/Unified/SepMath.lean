/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.SepSpec
public import AdversarialBco.Poly.Df2OracleProof

@[expose] public section

/-!
# UNI-CM, UNI-GAUGE and (SEP0): the mathematics

The `Prop`s of SepSpec.lean on the real side, except `SepAcc` (SepGrid.lean):

* `cmCert : CmCert` (UNI-CM): from `uni_cm_weakMem` (LeafFrozen.lean), the gauge of `K` about `a` read on
  `Fin d → ℝ`.
* `gaugeIt_inv`: the bisection in counters keeps `l + 2^{j-k} = u` after `k` steps, an upper end equal to `2^j` or
  accepted, a lower end equal to `0` or rejected; `gaugeCertEnd : GaugeCertEnd` (UNI-GAUGE (a));
  `oGauge_ray`: the gauge is positively homogeneous along the rays from its centre; `gaugeAcc : GaugeAcc`
  (UNI-GAUGE (b)).
* `sepZero : SepZero` ((SEP0) of UNI-SEP).
-/

namespace AdversarialBco.Uni

open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.LeanAp Matrix

variable {d : ℕ}

/-! ## (SEP0) -/

theorem sepZero : SepZero := by
  intro d h L τ ρ y0 y g hlip hL hτ hy hsub
  have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hg : oNorm g ≤ L + τ * Real.sqrt d := by
    by_cases hg0 : g = 0
    · rw [hg0, oNorm_zero]; positivity
    · have hn : 0 < oNorm g := lt_of_le_of_ne (oNorm_nonneg g) (fun e => hg0 (oNorm_eq_zero.1 e.symm))
      set v := (oNorm g)⁻¹ • g with hvdef
      have h1 := hsub (y + v)
      have h2 := hlip (y + v) y
      have hgv : g ⬝ᵥ v = oNorm g := by
        rw [hvdef, dotProduct_smul, smul_eq_mul, ← oNorm_sq]; field_simp
      have hv : oNorm v = 1 := by
        rw [hvdef, oNorm_smul, abs_inv, abs_of_pos hn]; field_simp
      have hyv : y + v - y = v := add_sub_cancel_left y v
      have hl1 : ∑ i, |(y + v) i - y i| ≤ Real.sqrt d := by
        have := l1_le_sqrt_mul v
        simpa [hv] using this
      rw [hyv, hgv] at h1
      rw [hyv, hv, mul_one] at h2
      have h3 : τ * ∑ i, |(y + v) i - y i| ≤ τ * Real.sqrt d := mul_le_mul_of_nonneg_left hl1 hτ
      have h4 := (abs_le.1 h2).2
      linarith
  refine ⟨hg, fun z => ?_⟩
  have hz := hsub z
  set r := oNorm (y - y0) with hr
  have hr0 : 0 ≤ r := oNorm_nonneg _
  have h1 : h y0 - L * r ≤ h y := by
    have := (abs_le.1 (hlip y y0)).1; linarith
  have h2 : g ⬝ᵥ (z - y) = g ⬝ᵥ (z - y0) - g ⬝ᵥ (y - y0) := by
    rw [← dotProduct_sub]; congr 1; abel
  have h3 : g ⬝ᵥ (y - y0) ≤ oNorm g * r := dot_le _ _
  have h4 : ∑ i, |z i - y i| ≤ Real.sqrt d * (oNorm (z - y0) + r) := by
    have e : (fun i => |z i - y i|) = fun i => |(z - y) i| := rfl
    have := l1_le_sqrt_mul (z - y)
    have h5 : oNorm (z - y) ≤ oNorm (z - y0) + r := by
      have := oNorm_sub_sub_le z y0 y
      rw [oNorm_sub_comm y0 y] at this; exact this
    calc ∑ i, |z i - y i| = ∑ i, |(z - y) i| := rfl
      _ ≤ Real.sqrt d * oNorm (z - y) := this
      _ ≤ Real.sqrt d * (oNorm (z - y0) + r) := mul_le_mul_of_nonneg_left h5 hsd
  have h6 : τ * ∑ i, |z i - y i| ≤ τ * (Real.sqrt d * (oNorm (z - y0) + r)) := mul_le_mul_of_nonneg_left h4 hτ
  have h7 : (L + oNorm g + τ * Real.sqrt d) * r ≤ (2 * L + 2 * τ * Real.sqrt d) * ρ :=
    mul_le_mul (by linarith) hy hr0 (by positivity)
  nlinarith

/-! ## UNI-CM -/

theorem cmCert : CmCert := by
  intro d K a r0 k orc hK hr0 hball horc y
  have hr0' : (0 : ℝ) < r0 := by exact_mod_cast hr0
  have hq : BitRAM.toE (cmPt a r0 k y) =
      BitRAM.toE a + (1 + 2 * (2 : ℝ)⁻¹ ^ k / r0) • (BitRAM.toE y - BitRAM.toE a) := by
    simp only [BitRAM.toE]
    rw [← WithLp.toLp_sub, ← WithLp.toLp_smul, ← WithLp.toLp_add]
    congr 1
    funext i
    simp only [cmPt, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    push_cast
    ring
  obtain ⟨hacc, hrej⟩ := uni_cm_weakMem K hK (BitRAM.toE a) (BitRAM.toE y) r0 hr0' hball orc horc
    (cmPt a r0 k y) k hq
  refine ⟨fun h => (interior_subset (hacc h) : WithLp.toLp 2 (qR y) ∈ K), fun h => ?_⟩
  have h2 := hrej h
  have hset : {t : ℝ | 0 < t ∧ qR a + t⁻¹ • (qR y - qR a) ∈ {x : Fin d → ℝ | WithLp.toLp 2 x ∈ K}} =
      {t : ℝ | 0 < t ∧ BitRAM.toE a + t⁻¹ • (BitRAM.toE y - BitRAM.toE a) ∈ K} := by
    ext t
    simp only [Set.mem_ofPred_eq, WithLp.toLp_add, WithLp.toLp_smul, WithLp.toLp_sub]
    rfl
  unfold oGauge
  rw [hset]
  exact h2

/-! ## UNI-GAUGE -/

/-- The invariant of the bisection in counters after `k ≤ j` steps. -/
theorem gaugeIt_inv (T : (Fin d → ℚ) → Bool) (a0 x : Fin d → ℚ) (H : ℚ) (j : ℕ) :
    ∀ k ≤ j, (gaugeIt T a0 x H j k).1 + 2 ^ (j - k) = (gaugeIt T a0 x H j k).2 ∧
      ((gaugeIt T a0 x H j k).2 = 2 ^ j ∨ T (gaugePt a0 x H j (gaugeIt T a0 x H j k).2) = true) ∧
      ((gaugeIt T a0 x H j k).1 = 0 ∨ T (gaugePt a0 x H j (gaugeIt T a0 x H j k).1) = false) := by
  intro k
  induction k with
  | zero => intro _; simp [gaugeIt]
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    have e : j - k = (j - (k + 1)) + 1 := by omega
    rw [e, pow_succ] at h1
    set I := gaugeIt T a0 x H j k with hI
    have hm : (I.1 + I.2) / 2 = I.1 + 2 ^ (j - (k + 1)) := by
      generalize 2 ^ (j - (k + 1)) = P at h1 ⊢; omega
    simp only [gaugeIt, ← hI]
    split_ifs with hT
    · exact ⟨by simp only; rw [hm], Or.inr (by simpa using hT), h3⟩
    · refine ⟨by simp only; rw [hm]; generalize 2 ^ (j - (k + 1)) = P at h1 ⊢; omega, h2, Or.inr ?_⟩
      simpa using hT

theorem gaugeCertEnd : GaugeCertEnd := by
  intro d T a0 x H j h
  rcases (gaugeIt_inv T a0 x H j j le_rfl).2.1 with e | e
  · exact absurd e (ne_of_lt h)
  · exact e

/-- The gauge is positively homogeneous along the rays from its centre. -/
theorem oGauge_ray (Q : Set (Fin d → ℝ)) (a0 x : Fin d → ℝ) {c : ℝ} (hc : 0 < c) :
    oGauge Q a0 (a0 + c • (x - a0)) = c * oGauge Q a0 x := by
  unfold oGauge
  rw [← smul_eq_mul, ← Real.sInf_smul_of_nonneg hc.le]
  congr 1
  ext t
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne']
  simp only [Set.mem_ofPred_eq, add_sub_cancel_left, smul_smul, smul_eq_mul]
  constructor
  · rintro ⟨ht, hm⟩
    refine ⟨by positivity, ?_⟩
    have e : (c⁻¹ * t)⁻¹ = t⁻¹ * c := by rw [mul_inv, inv_inv, mul_comm]
    rwa [e]
  · rintro ⟨ht, hm⟩
    have ht' : 0 < t := by
      have := mul_pos hc ht; rwa [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at this
    refine ⟨ht', ?_⟩
    have e : (c⁻¹ * t)⁻¹ = t⁻¹ * c := by rw [mul_inv, inv_inv, mul_comm]
    rwa [e] at hm

theorem oGauge_nonneg (Q : Set (Fin d → ℝ)) (a0 x : Fin d → ℝ) : 0 ≤ oGauge Q a0 x :=
  Real.sInf_nonneg fun _ ht => ht.1.le

/-- A point of `Q` has gauge at most `1`. -/
theorem oGauge_le_one_of_mem {Q : Set (Fin d → ℝ)} {a0 x : Fin d → ℝ} (hx : x ∈ Q) : oGauge Q a0 x ≤ 1 :=
  csInf_le ⟨0, fun _ ht => ht.1.le⟩ ⟨one_pos, by simpa using hx⟩

/-- The ray point of the counter `m ≥ 1`, as a real vector. -/
theorem qR_gaugePt (a0 x : Fin d → ℚ) (H : ℚ) (j m : ℕ) :
    qR (gaugePt a0 x H j m) = qR a0 + ((2 : ℝ) ^ j / ((H : ℝ) * m)) • (qR x - qR a0) := by
  funext i
  simp only [qR, gaugePt, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  push_cast
  ring

theorem gaugeAcc : GaugeAcc := by
  intro d T Q a0 x H j η hη0 hη1 hT hH hγH
  set γ := oGauge Q (qR a0) (qR x) with hγ
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have hη' : 0 < 1 - η := by linarith
  have hγ0 : 0 ≤ γ := oGauge_nonneg _ _ _
  obtain ⟨hlu, hu, hl⟩ := gaugeIt_inv T a0 x H j j le_rfl
  set l := (gaugeIt T a0 x H j j).1 with hldef
  set u := (gaugeIt T a0 x H j j).2 with hudef
  rw [Nat.sub_self, pow_zero] at hlu
  -- the gauge at the ray point of a counter `m ≥ 1`
  have hray : ∀ m : ℕ, 1 ≤ m →
      oGauge Q (qR a0) (qR (gaugePt a0 x H j m)) = (2 : ℝ) ^ j / ((H : ℝ) * m) * γ := fun m hm => by
    rw [qR_gaugePt]
    exact oGauge_ray Q (qR a0) (qR x) (by have : (1 : ℝ) ≤ m := (by exact_mod_cast hm); positivity)
  have hval : ((gaugeQ T a0 x H j : ℚ) : ℝ) = (H : ℝ) * u / 2 ^ j := by
    simp only [gaugeQ, ← hudef]; push_cast; ring
  rw [hval]
  have hu1 : 1 ≤ u := by omega
  have hu1R : (1 : ℝ) ≤ u := by exact_mod_cast hu1
  refine ⟨?_, ?_⟩
  · rcases hu with e | e
    · rw [e]; push_cast; rw [mul_div_assoc, div_self h2j.ne', mul_one]; exact hγH
    · have hmem := (hT _).1 e
      have h1 := oGauge_le_one_of_mem (a0 := qR a0) hmem
      rw [hray u hu1] at h1
      have hc : (0 : ℝ) < (H : ℝ) * u := by positivity
      rw [div_mul_eq_mul_div, div_le_one hc] at h1
      rw [le_div_iff₀ h2j]
      linarith [mul_comm γ ((2 : ℝ) ^ j)]
  · have hul : (u : ℝ) = l + 1 := by exact_mod_cast hlu.symm
    have htl : (H : ℝ) * l / 2 ^ j ≤ γ / (1 - η) := by
      by_cases hl0 : l = 0
      · rw [hl0]; simp only [Nat.cast_zero, mul_zero, zero_div]; positivity
      · have hl1 : 1 ≤ l := Nat.one_le_iff_ne_zero.2 hl0
        rcases hl with e | e
        · exact absurd e hl0
        · have hrej := (hT _).2 e
          rw [hray l hl1] at hrej
          have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl1
          have htl0 : 0 < (H : ℝ) * l / 2 ^ j := by positivity
          have h3 := mul_lt_mul_of_pos_left hrej htl0
          have h4 : (H : ℝ) * l / 2 ^ j * (2 ^ j / ((H : ℝ) * l) * γ) = γ := by field_simp
          rw [h4] at h3
          rw [le_div_iff₀ hη']
          linarith
    rw [hul, mul_add, mul_one, add_div]
    linarith

end AdversarialBco.Uni
