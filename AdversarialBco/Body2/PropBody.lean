/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Body.Inner
public import AdversarialBco.Body2.Arith
public import AdversarialBco.Body2.Glue
public import AdversarialBco.Body2.Glue2
public import AdversarialBco.Body2.Penalty
public import AdversarialBco.StatementBody

@[expose] public section

/-!
# Proposition 2.2 with `C_0 = 1.2 * 10^9`, from Theorem 3.1

`bodyExplicit_of_dil : DilTheorem → BodyExplicit`, the proof of the paper: the extension
`f̃_c + Γ r` with `Γ = 10^8 z^10`, `z = n d D`, Theorem 3.1 on the extended family, the image `ρ` of the diluted law
under the projection onto `J`, the mass outside `J` by Gaussian concentration and the penalty of Lemma 4.1;
then `bodyHExplicit_of_body : BodyExplicit → BodyHExplicit` on the inner body.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace NNReal

namespace AdversarialBco.Body2
open AdversarialBco.BodySpec

theorem KS_pos' : 0 < KS := by
  obtain ⟨h1, -, h3, -⟩ := kappa_bounds
  unfold KS
  have : 0 < kappa := by linarith
  have : 0 < 13 / 4 + 2 * kappa2 := by linarith
  positivity

set_option maxHeartbeats 800000 in
/-- The scalar chain of the proof of Proposition 2.2: from the conclusions of Theorem 3.1 on the extended
family, the mass outside `J`, the bound on `s_h` and the tail of `r`, the bound
`Δ(p_h)^2 ≤ 1.2·10^9 d^2 ln(n d D) ln(2n) ∫ V^J dρ`. -/
theorem body_chain (n d D Δs h gmax Fs Fb EF m0 Δp mb rb s T Vs Vb EV I E2 R2 W : ℝ)
    (hn : 2 ≤ n) (hd : 1 ≤ d) (hD : 1 ≤ D)
    (hΔ1 : 1 / n < Δs) (hΔg : Δs ≤ gmax) (hg1 : gmax ≤ 1) (hh1 : Δs / 2 ≤ h) (hh2 : h ≤ gmax)
    (hΔs : Δs = Fs - m0) (hFb : Fs ≤ Fb)
    (hΔpeq : Δp = (1 - Δs / (4 * h)) * Fs + Δs / (4 * h) / 2 * Fb + Δs / (4 * h) / 2 * EF - m0)
    (hΔp : Δp ≤ 65 / 64 * Δs)
    (hmass : Fs + 10 ^ 8 * (n * d * D) ^ 10 * mb ≤ EF) (hmb : 0 ≤ mb) (hrb0 : 0 ≤ rb) (hrb : rb ≤ mb)
    (hs0 : 0 < s) (hs : Real.sqrt (2 / Real.pi) * s ≤ mb + D + rb)
    (hT : T = Real.sqrt (2 * lnp (26 * d * (n + 10 ^ 8 * (n * d * D) ^ 10) * s / h)))
    (hVs : 0 ≤ Vs)
    (hP3 : h * Δs / (2 * KS * (1 + T) ^ 2 * d ^ 2 * Real.log (2 * gmax / Δs)) ≤ Vs + Vb + EV)
    (hI : I = (1 - Δs / (4 * h)) * Vs + Δs / (4 * h) / 2 * Vb + Δs / (4 * h) / 2 * EV)
    (htail : ∀ t0 : ℝ, 0 ≤ t0 →
      E2 ≤ 2 * (mb + t0) * mb + 2 * (Real.pi / 2 * s) ^ 2 * Real.exp (-t0 ^ 2 / (2 * (Real.pi / 2 * s) ^ 2)))
    (hR2 : R2 ≤ Δs / (4 * h) / 2 * (rb ^ 2 + E2))
    (hW : I ≤ 2 * W + 2 * n ^ 2 * R2)
    (hKD : Δp ^ 2 ≤ KD * (1 + T) ^ 2 * d ^ 2 * Real.log (2 * gmax / Δs) * I) :
    Δp ^ 2 ≤ 1200000000 * d ^ 2 * Real.log (n * d * D) * Real.log (2 * n) * W := by
  set q := Δs / (4 * h) with hq
  set z := n * d * D with hz
  set Γ := 10 ^ 8 * z ^ 10 with hΓ
  have hn0 : 0 < n := by linarith
  have hΔ0 : 0 < Δs := lt_trans (by positivity) hΔ1
  have hh0 : 0 < h := by linarith
  have hh1' : 1 / (2 * n) < h := by
    have : 1 / (2 * n) = (1 / n) / 2 := by field_simp
    rw [this]; linarith
  have hq0 : 0 < q := by positivity
  have hq1 : q ≤ 1 / 2 := by
    rw [hq, div_le_iff₀ (by positivity)]; linarith
  have hnd : 2 ≤ n * d := by
    calc (2 : ℝ) = 2 * 1 := by ring
      _ ≤ n * d := mul_le_mul hn hd (by norm_num) (by linarith only [hn])
  have hz2D : 2 * D ≤ z := mul_le_mul_of_nonneg_right hnd (by linarith only [hD])
  have hz2 : 2 ≤ z := by linarith
  have hnz : n ≤ z := by
    have : n ≤ n * d := le_mul_of_one_le_right hn0.le hd
    have : n * d ≤ n * d * D := le_mul_of_one_le_right (by linarith) hD
    linarith
  have hndz : n * d ≤ z := le_mul_of_one_le_right (by linarith) hD
  have hΓ1 : 1 ≤ Γ := by
    have : 1 ≤ z ^ 10 := one_le_pow₀ (by linarith)
    rw [hΓ]; exact one_le_mul_of_one_le_of_one_le (by norm_num) this
  -- the mass outside `J`
  have hEF : EF - Fs ≤ h / 8 := by
    have hp : (1 - (Fs - m0) / (4 * h)) * Fs + (Fs - m0) / (4 * h) / 2 * Fb + (Fs - m0) / (4 * h) / 2 * EF - m0 ≤
        65 / 64 * (Fs - m0) := by
      rw [← hΔs]; exact hΔpeq ▸ hΔp
    exact mass_arith Fs Fb EF m0 h hh0 (by linarith) hFb hp
  have hΓm : Γ * mb ≤ h / 8 := by linarith
  have hΓm1 : Γ * mb ≤ 1 / 8 := by linarith
  have hmb8 : mb ≤ 1 / 8 := by
    have : mb ≤ Γ * mb := le_mul_of_one_le_left hmb hΓ1
    linarith
  have hsb : s ≤ Real.sqrt (Real.pi / 2) * (17 / 16) * z := sh_arith s mb rb D z hs hmb8 hrb hD hz2D
  obtain ⟨hTz, hTC⟩ := T_arith n d D s h hn hd hD hs0.le hsb hh1'
  rw [← hT] at hTz hTC
  have hT0 : 0 ≤ T := by rw [hT]; exact Real.sqrt_nonneg _
  -- the lower bound on the variance
  obtain ⟨hl0, hl1, hl2⟩ := log_gmax n Δs gmax hn hΔ1 hΔg hg1
  set ι := Δs ^ 2 / (16 * 10 ^ 5 * (1 + T) ^ 2 * d ^ 2 * Real.log (2 / Δs)) with hι
  have hVsum : 4 * ι ≤ Vs + Vb + EV :=
    p3_iota h Δs KS T d (Real.log (2 * gmax / Δs)) (Real.log (2 / Δs)) (Vs + Vb + EV) hΔ0 hh1 KS_pos'
      (by linarith [KS_bounds.1]) hd hT0 hl0 hl1 hP3
  have hIq : 2 * q * ι ≤ I := by
    rw [hI]
    have h1 : q / 2 * Vs ≤ (1 - q) * Vs := mul_le_mul_of_nonneg_right (by linarith) hVs
    have h2 : q / 2 * (4 * ι) ≤ q / 2 * (Vs + Vb + EV) := mul_le_mul_of_nonneg_left hVsum (by linarith only [hq0])
    linarith only [h1, h2]
  have hl2Δ : 0 < Real.log (2 / Δs) := lt_of_lt_of_le hl0 hl1
  have hι0 : 0 < ι := by rw [hι]; positivity
  have hιz : iota0 z ≤ ι := by
    have := iota_arith Δs n d z T (Tz z) hn hd hΔ1 (hΔg.trans hg1) hT0 hTz hndz
    unfold iota0; exact this
  obtain ⟨hι0z, hθ1⟩ := theta_arg z hz2
  -- the tail of `r` and the choice of `t_0`
  set σ := Real.pi / 2 * s with hσ
  have hσ0 : 0 < σ := by rw [hσ]; positivity
  set t0 := σ * Real.sqrt (2 * lnp (8 * n ^ 2 * σ ^ 2 / ι)) with ht0
  have ht00 : 0 ≤ t0 := by rw [ht0]; positivity
  have hE2 := htail t0 ht00
  have hX : n ^ 2 * (2 * σ ^ 2 * Real.exp (-t0 ^ 2 / (2 * σ ^ 2))) ≤ ι / 4 := by
    have := t0_arith n σ ι hσ0 hι0
    calc n ^ 2 * (2 * σ ^ 2 * Real.exp (-t0 ^ 2 / (2 * σ ^ 2)))
        = 2 * n ^ 2 * σ ^ 2 * Real.exp (-(σ * Real.sqrt (2 * lnp (8 * n ^ 2 * σ ^ 2 / ι))) ^ 2 / (2 * σ ^ 2)) := by
          rw [ht0]; ring
      _ ≤ ι / 4 := this
  have hσs0 : σ ≤ s0 z := by
    rw [hσ]; unfold s0
    have := mul_le_mul_of_nonneg_left hsb (by positivity : (0 : ℝ) ≤ Real.pi / 2)
    calc Real.pi / 2 * s ≤ Real.pi / 2 * (Real.sqrt (Real.pi / 2) * (17 / 16) * z) := this
      _ = Real.pi / 2 * (Real.sqrt (Real.pi / 2) * (17 / 16)) * z := by ring
  have ht0b : t0 ≤ s0 z * Real.sqrt (2 * Theta z) := by
    have := t0_mono n z σ (s0 z) ι (iota0 z) hn0.le hnz hσ0.le hσs0 hι0z hιz hθ1
    unfold Theta; exact this
  have hneed := need_mono n z t0 ι hn0.le hnz hz2 ht00 ht0b hι0z hιz
  have hpen : n ^ 2 * (3 + 2 * t0) / (4 * ι) ≤ Γ := hneed.trans (penalty_need z hz2)
  have hout := outside_arith n mb E2 (2 * σ ^ 2 * Real.exp (-t0 ^ 2 / (2 * σ ^ 2))) Γ t0 ι hmb (by linarith)
    ht00 hι0 hE2 hX hΓm1 hpen
  -- the projection
  have hR2' : n ^ 2 * R2 ≤ q / 2 * (3 * ι / 4) := by
    have hrb2 : rb ^ 2 ≤ mb ^ 2 := pow_le_pow_left₀ hrb0 hrb 2
    have h1 : R2 ≤ q / 2 * (mb ^ 2 + E2) := hR2.trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
    have h2 : n ^ 2 * R2 ≤ n ^ 2 * (q / 2 * (mb ^ 2 + E2)) := mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : q / 2 * (n ^ 2 * (mb ^ 2 + E2)) ≤ q / 2 * (3 * ι / 4) :=
      mul_le_mul_of_nonneg_left hout (by linarith only [hq0])
    linarith only [h2, h3]
  have hW' : I / 2 - n ^ 2 * R2 ≤ W := by linarith
  have hC : 4 * KD * ((2 + 4 * Real.log C1) / Real.log 2 + 48) ≤ 1200000000 := by
    unfold C1; exact C0_bound
  have hlz : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
  exact final_arith Δp KD T d (Real.log (2 * gmax / Δs)) (Real.log (2 * n)) I W R2 q ι n
    ((2 + 4 * Real.log C1) / Real.log 2 + 48) (Real.log z) (by unfold KD; norm_num) hd hl0.le hl2 hq0 hι0 hlz
    hKD hIq hR2' hW' hTC hC


/-- The integral under the diluted law of a continuous function integrable under `N(b, S^2)`. -/
theorem dil_int {d : ℕ} (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (bstar b : EuclideanSpace ℝ (Fin d))
    (S : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : Continuous f) (hfi : Integrable f (gaussLaw b S)) :
    IsProbabilityMeasure (dilutedLaw q bstar b S) ∧ Integrable f (dilutedLaw q bstar b S) ∧
      ∫ x, f x ∂(dilutedLaw q bstar b S) = (1 - q) * f bstar + q / 2 * f b + q / 2 * ∫ x, f x ∂(gaussLaw b S) := by
  have hm : AEMeasurable (fun z : EuclideanSpace ℝ (Fin d) => b + S z) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    fun_prop
  have hfi' : Integrable (fun z => f (b + S z)) (stdGaussian (EuclideanSpace ℝ (Fin d))) :=
    (integrable_map_measure hf.aestronglyMeasurable hm).1 hfi
  obtain ⟨h1, h2, h3⟩ := diluted_integral q hq0 hq1 bstar b S f hf hfi'
  refine ⟨h1, h2, ?_⟩
  rw [h3, gaussLaw, integral_map hm hf.aestronglyMeasurable]

/-- The image under a continuous retraction `pr` onto a closed set `J` of a probability law `p`: a probability law
carried by `J`, under which every function that agrees on `J` with a continuous function and is bounded on `J` is
integrable, with `∫ Φ d(p.map pr) = ∫ Φ ∘ pr dp`. -/
theorem map_pr {d : ℕ} (J : Set (EuclideanSpace ℝ (Fin d))) (hJ : IsClosed J)
    (pr : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hprc : Continuous pr) (hprJ : ∀ x, pr x ∈ J)
    (p : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure p] :
    IsProbabilityMeasure (p.map pr) ∧ (p.map pr) Jᶜ = 0 ∧
      ∀ Φ : EuclideanSpace ℝ (Fin d) → ℝ, (∃ g, Continuous g ∧ ∀ y ∈ J, Φ y = g y) → (∃ B, ∀ y ∈ J, |Φ y| ≤ B) →
        Integrable Φ (p.map pr) ∧ Integrable (fun x => Φ (pr x)) p ∧ ∫ y, Φ y ∂(p.map pr) = ∫ x, Φ (pr x) ∂p := by
  have h0 := AdversarialBco.Body.tr_map_proj p J hJ pr hprc hprJ (fun _ => 0) (fun _ => 0) continuous_const
    (fun _ _ => rfl) 0 (fun _ _ => by simp)
  refine ⟨h0.1, h0.2.1, fun Φ ⟨g, hg, hgJ⟩ ⟨B, hB⟩ => ?_⟩
  have h1 := AdversarialBco.Body.tr_map_proj p J hJ pr hprc hprJ Φ g hg hgJ B hB
  exact ⟨h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2⟩


set_option maxHeartbeats 3200000 in
/-- Proposition 2.2 for one law with positive weights, from Theorem 3.1: a probability law `ρ` carried by `J`,
under which every function that agrees on `J` with a continuous function and is bounded on `J` is integrable, with
regret at most `1/n + (β ∫ V^J dρ)^{1/2}`, `β = 1.2·10^9 d^2 ln(n d diam J) ln(2n)`. -/
theorem body_pos (hdil : DilTheorem) {d : ℕ} (hd : 1 ≤ d) (n : ℕ) (hn : 2 ≤ n)
    (J : Set (EuclideanSpace ℝ (Fin d))) (hJc : IsCompact J) (hJv : Convex ℝ J)
    (c0 : EuclideanSpace ℝ (Fin d)) (hc0 : Metric.closedBall c0 (1 / 2) ⊆ J)
    (k : ℕ) (w : Fin k → ℝ) (f : Fin k → EuclideanSpace ℝ (Fin d) → ℝ) (hw : ∀ i, 0 < w i)
    (hw1 : ∑ i, w i = 1)
    (hf : ∀ i, ConvexOn ℝ J (f i) ∧ (∀ x ∈ J, ∀ y ∈ J, |f i x - f i y| ≤ n * dist x y) ∧
      ∀ x ∈ J, f i x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ ρ : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure ρ ∧ ρ Jᶜ = 0 ∧
      (∀ Φ : EuclideanSpace ℝ (Fin d) → ℝ, (∃ g, Continuous g ∧ ∀ y ∈ J, Φ y = g y) →
        (∃ B, ∀ y ∈ J, |Φ y| ≤ B) → Integrable Φ ρ) ∧
      ∫ x, ∑ i, w i * f i x ∂ρ - ∑ i, w i * sInf (f i '' J) ≤
        1 / n + √(1200000000 * (d : ℝ) ^ 2 * Real.log (n * d * Metric.diam J) * Real.log (2 * n) *
          ∫ x, ∑ i, w i * ((∑ j, w j * f j x) - f i x) ^ 2 ∂ρ) := by
  classical
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn0 : (0 : ℝ) < n := by linarith
  have hc0J : c0 ∈ J := hc0 (Metric.mem_closedBall_self (by norm_num))
  have hJn : J.Nonempty := ⟨c0, hc0J⟩
  have hJb : Bornology.IsBounded J := hJc.isBounded
  have hD1 : 1 ≤ Metric.diam J := one_le_diam hd J hJb c0 hc0
  set D := Metric.diam J with hDdef
  set Γ : ℝ := 10 ^ 8 * ((n : ℝ) * d * D) ^ 10 with hΓdef
  have hΓ0 : 0 < Γ := by positivity
  have hF01 : ∀ i, ∀ x ∈ J, f i x ∈ Set.Icc (0 : ℝ) 1 := fun i => (hf i).2.2
  have hFl : ∀ i, ∀ x ∈ J, ∀ y ∈ J, |f i x - f i y| ≤ n * dist x y := fun i => (hf i).2.1
  have hext := fun i => AdversarialBco.Body.tr_ext J hJv hJn (f i) n (hf i).1 (hFl i) (hF01 i) Γ hΓ0.le
  have hGc : ∀ i, Continuous (AdversarialBco.lipExt J (f i) n) := fun i => (hext i).1
  have hGJ : ∀ i, ∀ y ∈ J, AdversarialBco.lipExt J (f i) n y = f i y := fun i => (hext i).2.1
  obtain ⟨pr, hprc, hprJ, hprd, hprid⟩ := AdversarialBco.Body.exists_proj J hJc hJv hJn
  have htr := map_pr J hJc.isClosed pr hprc hprJ
  -- the integrands of (H) on `J` and their continuous extensions
  have hu01 : ∀ y ∈ J, |∑ i, w i * f i y| ≤ 1 ∧ |∑ i, w i * ((∑ j, w j * f j y) - f i y) ^ 2| ≤ 1 :=
    fun y hy => AdversarialBco.Body.tr_unit_bounds k w (fun i => (hw i).le) hw1 (fun i => f i y)
      (fun i => hF01 i y hy)
  have hgbar : Continuous (fun y => ∑ i, w i * AdversarialBco.lipExt J (f i) n y) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (hGc i)
  have hgm : ∃ g, Continuous g ∧ ∀ y ∈ J, (fun y => ∑ i, w i * f i y) y = g y :=
    ⟨_, hgbar, fun y hy => Finset.sum_congr rfl fun i _ => by rw [hGJ i y hy]⟩
  have hgv : ∃ g, Continuous g ∧
      ∀ y ∈ J, (fun y => ∑ i, w i * ((∑ j, w j * f j y) - f i y) ^ 2) y = g y := by
    refine ⟨fun y => ∑ i, w i * ((∑ j, w j * AdversarialBco.lipExt J (f j) n y) -
      AdversarialBco.lipExt J (f i) n y) ^ 2,
      continuous_finsetSum _ fun i _ => continuous_const.mul ((hgbar.sub (hGc i)).pow 2), fun y hy => ?_⟩
    have h1 := fun i => hGJ i y hy
    simp only [h1]
  -- the minimisers
  have hFcont : ∀ i, ContinuousOn (f i) J := fun i =>
    (hGc i).continuousOn.congr fun y hy => (hGJ i y hy).symm
  choose xmin hxJ hxmin hxinf using fun i => AdversarialBco.Body.tr_min J hJc hJn (f i) (hFcont i)
  have hfbcont : ContinuousOn (fun y => ∑ i, w i * f i y) J :=
    hgbar.continuousOn.congr fun y hy => Finset.sum_congr rfl fun i _ => by rw [hGJ i y hy]
  obtain ⟨bstar, hbJ, hbmin, -⟩ := AdversarialBco.Body.tr_min J hJc hJn _ hfbcont
  have hgain1 : ∀ i, f i bstar - f i (xmin i) ≤ 1 := fun i => by
    have h1 := hF01 i bstar hbJ
    have h2 := hF01 i (xmin i) (hxJ i)
    simp only [Set.mem_Icc] at h1 h2
    linarith only [h1.1, h1.2, h2.1, h2.2]
  set Δs := ∑ i, w i * f i bstar - ∑ i, w i * f i (xmin i) with hΔs
  have hinf : ∑ i, w i * sInf (f i '' J) = ∑ i, w i * f i (xmin i) := by simp only [hxinf]
  -- small regret: the point mass at `bstar`
  by_cases hsmall : Δs ≤ 1 / n
  · obtain ⟨hP, hJ0, hgood⟩ := htr (Measure.dirac bstar)
    refine ⟨_, hP, hJ0, fun Φ hg hB => (hgood Φ hg hB).1, ?_⟩
    have hint := (hgood (fun y => ∑ i, w i * f i y) hgm ⟨1, fun y hy => (hu01 y hy).1⟩).2.2
    rw [hint, integral_dirac, hprid bstar hbJ, hinf]
    have := Real.sqrt_nonneg (1200000000 * (d : ℝ) ^ 2 * Real.log (n * d * D) * Real.log (2 * n) *
      ∫ x, ∑ i, w i * ((∑ j, w j * f j x) - f i x) ^ 2 ∂(Measure.map pr (Measure.dirac bstar)))
    linarith
  push Not at hsmall
  have hΔ0 : 0 < Δs := lt_trans (by positivity) hsmall
  have hkne : Nonempty (Fin k) := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp at hw1
    · exact ⟨⟨0, hk⟩⟩
  -- the extended family
  set Fe : Fin k → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun i x => AdversarialBco.lipExt J (f i) n x + Γ * Metric.infDist x J with hFe
  have hrJ0 : ∀ x, 0 ≤ Metric.infDist x J := fun x => Metric.infDist_nonneg
  have hlo : ∀ i x, f i (pr x) ≤ AdversarialBco.lipExt J (f i) n x := fun i x =>
    lipExt_ge J (f i) n hn0.le (hFl i) x (pr x) (hprJ x)
      (fun y hy => proj_nonexp J hJv x (pr x) (hprJ x) (hprd x) y hy)
  have hbdd : ∀ i, BddBelow (f i '' J) := fun i => ⟨0, by rintro _ ⟨y, hy, rfl⟩; exact (hF01 i y hy).1⟩
  have hhi : ∀ i x, AdversarialBco.lipExt J (f i) n x ≤ f i (pr x) + n * Metric.infDist x J := by
    intro i x
    have h1 := AdversarialBco.lipExt_le J hJn (f i) (hbdd i) n hn0.le x (pr x)
    rwa [hGJ i (pr x) (hprJ x), hprd x] at h1
  have hFeJ : ∀ i, ∀ y ∈ J, Fe i y = f i y := fun i y hy => by
    simp only [hFe, hGJ i y hy, Metric.infDist_zero_of_mem hy, mul_zero, add_zero]
  have hmeanlo : ∀ x, (∑ i, w i * f i (pr x)) + Γ * Metric.infDist x J ≤ mean w Fe x := by
    intro x
    have h1 := AdversarialBco.Body.tr_wsum_le w (fun i => (hw i).le) hw1 (fun i => f i (pr x)) (fun i => Fe i x)
      (-(Γ * Metric.infDist x J)) (fun i => by simp only [hFe]; linarith only [hlo i x])
    simp only [mean]; linarith only [h1]
  have hFs : mean w Fe bstar = ∑ i, w i * f i bstar := by
    simp only [mean]; exact Finset.sum_congr rfl fun i _ => by rw [hFeJ i _ hbJ]
  have hm0 : ∑ i, w i * Fe i (xmin i) = ∑ i, w i * f i (xmin i) :=
    Finset.sum_congr rfl fun i _ => by rw [hFeJ i _ (hxJ i)]
  have hcoer : ∀ x, Γ * ‖x‖ - Γ * (‖c0‖ + D) ≤ mean w Fe x := by
    intro x
    have h1 := AdversarialBco.Body.tr_infDist_ge J c0 hc0J D
      (fun y hy => Metric.dist_le_diam_of_mem hJb hy hc0J) x
    have h2 : 0 ≤ ∑ i, w i * f i (pr x) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hw i).le (hF01 i _ (hprJ x)).1
    have h3 := mul_le_mul_of_nonneg_left h1 hΓ0.le
    have h4 := hmeanlo x
    linarith only [h2, h3, h4]
  have hbst : ∀ y, mean w Fe bstar ≤ mean w Fe y := by
    intro y
    have h2 := hbmin (pr y) (hprJ y)
    have h4 : 0 ≤ Γ * Metric.infDist y J := mul_nonneg hΓ0.le (hrJ0 y)
    linarith only [hmeanlo y, hFs, h2, h4]
  have hxm : ∀ i y, Fe i (xmin i) ≤ Fe i y := by
    intro i y
    rw [hFeJ i _ (hxJ i)]
    have h1 := hxmin i (pr y) (hprJ y)
    have h2 := hlo i y
    have h3 := mul_nonneg hΓ0.le (hrJ0 y)
    simp only [hFe]; linarith only [h1, h2, h3]
  have hΔeq : mean w Fe bstar - ∑ i, w i * Fe i (xmin i) = Δs := by rw [hFs, hm0]
  have hgainEq : ∀ i, Fe i bstar - Fe i (xmin i) = f i bstar - f i (xmin i) := fun i => by
    rw [hFeJ i _ hbJ, hFeJ i _ (hxJ i)]
  have hFeL : ∀ i, LipschitzWith (Real.toNNReal (n + Γ)) (Fe i) := fun i => (hext i).2.2.2
  -- Theorem 3.1 on the extended family
  obtain ⟨h, hh1, hh2, -, ⟨b, S, hES⟩, hall⟩ := hdil d hd k w Fe (Real.toNNReal (n + Γ)) xmin Γ
    (Γ * (‖c0‖ + D)) bstar hw hw1 (fun i => (hext i).2.2.1) hFeL hxm hΓ0 hcoer hbst (by rw [hΔeq]; exact hΔ0)
  obtain ⟨hΔp, hP3, hKD⟩ := hall b S hES
  have hnΓ : (0 : ℝ) ≤ n + Γ := by positivity
  simp only [hΔeq, hgainEq, Real.coe_toNNReal _ hnΓ] at hh1 hh2 hΔp hP3 hKD
  simp only [hm0] at hΔp hKD
  set gmax := ⨆ i, (f i bstar - f i (xmin i)) with hgmax
  have hgle : ∀ i, f i bstar - f i (xmin i) ≤ gmax := fun i =>
    le_ciSup (f := fun i => f i bstar - f i (xmin i)) (Finite.bddAbove_range _) i
  have hg1 : gmax ≤ 1 := ciSup_le fun i => hgain1 i
  have hΔg : Δs ≤ gmax := by
    have h1 : Δs = ∑ i, w i * (f i bstar - f i (xmin i)) := by
      rw [hΔs, ← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    have h2 : ∑ i, w i * (f i bstar - f i (xmin i)) ≤ ∑ i, w i * gmax :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hgle i) (hw i).le
    rw [← Finset.sum_mul, hw1, one_mul] at h2
    linarith only [h1, h2]
  -- the laws
  have hSpos : 0 < ‖S‖ := spd_norm_pos hd S hES.1
  have hh0 : 0 < h := by linarith only [hh1, hΔ0]
  set q := Δs / (4 * h) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := by rw [hq, div_le_one (by positivity)]; linarith only [hh1, hΔ0]
  have hνP : IsProbabilityMeasure (gaussLaw b S) := inferInstanceAs (IsProbabilityMeasure (AdversarialBco.Gauss.cloud b S))
  have hFec : ∀ i, Continuous (Fe i) := fun i => (hFeL i).continuous
  have hmc : Continuous (mean w Fe) := continuous_finsetSum _ fun i _ => continuous_const.mul (hFec i)
  have hvc : Continuous (var w Fe) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (((hFec i).sub hmc).pow 2)
  have hrc : Continuous (fun x => Metric.infDist x J) := Metric.continuous_infDist_pt J
  obtain ⟨hmi0, hvi0⟩ := AdversarialBco.Body.tr_integrable_cloud_var b S w Fe _ hFeL
  obtain ⟨hri0, hr2i0⟩ := AdversarialBco.Body.tr_integrable_cloud b S (fun x => Metric.infDist x J) 1
    (Metric.lipschitz_infDist_pt J)
  have hmi : Integrable (mean w Fe) (gaussLaw b S) := hmi0
  have hvi : Integrable (var w Fe) (gaussLaw b S) := hvi0
  have hri : Integrable (fun x => Metric.infDist x J) (gaussLaw b S) := hri0
  have hr2i : Integrable (fun x => Metric.infDist x J ^ 2) (gaussLaw b S) := hr2i0
  obtain ⟨hpP, hpm, hpmeq⟩ := dil_int q hq0 hq1 bstar b S (mean w Fe) hmc hmi
  obtain ⟨-, hpv, hpveq⟩ := dil_int q hq0 hq1 bstar b S (var w Fe) hvc hvi
  obtain ⟨-, hpr2, hpr2eq⟩ := dil_int q hq0 hq1 bstar b S (fun x => Metric.infDist x J ^ 2) (hrc.pow 2) hr2i
  beta_reduce at hpr2eq
  set p := dilutedLaw q bstar b S with hp
  obtain ⟨hρP, hρJ, hgood⟩ := htr p
  refine ⟨p.map pr, hρP, hρJ, fun Φ hg hB => (hgood Φ hg hB).1, ?_⟩
  -- the scalars
  set mb := ∫ x, Metric.infDist x J ∂(gaussLaw b S) with hmb
  set rb := Metric.infDist b J with hrb
  set E2 := ∫ x, Metric.infDist x J ^ 2 ∂(gaussLaw b S) with hE2
  set EF := ∫ x, mean w Fe x ∂(gaussLaw b S) with hEF
  set EV := ∫ x, var w Fe x ∂(gaussLaw b S) with hEV
  set VJ : EuclideanSpace ℝ (Fin d) → ℝ := fun y => ∑ i, w i * ((∑ j, w j * f j y) - f i y) ^ 2 with hVJ
  obtain ⟨-, hVJp, hVJeq⟩ := hgood VJ hgv ⟨1, fun y hy => (hu01 y hy).2⟩
  set W := ∫ y, VJ y ∂(p.map pr) with hW
  set T := Real.sqrt (2 * lnp (26 * d * (n + Γ) * ‖S‖ / h)) with hT
  set Δp := ∫ x, mean w Fe x ∂p - ∑ i, w i * f i (xmin i) with hΔpdef
  have hΔpeq : Δp = (1 - q) * (∑ i, w i * f i bstar) + q / 2 * mean w Fe b + q / 2 * EF -
      ∑ i, w i * f i (xmin i) := by rw [hΔpdef, hpmeq, hFs]
  have hFb : ∑ i, w i * f i bstar ≤ mean w Fe b := hFs ▸ hbst b
  have hmass : (∑ i, w i * f i bstar) + Γ * mb ≤ EF := by
    have h1 : ∀ x, (∑ i, w i * f i bstar) + Γ * Metric.infDist x J ≤ mean w Fe x := fun x => by
      linarith only [hmeanlo x, hbmin (pr x) (hprJ x)]
    have hi1 : Integrable (fun x => (∑ i, w i * f i bstar) + Γ * Metric.infDist x J) (gaussLaw b S) :=
      (integrable_const _).add (hri.const_mul Γ)
    have h2 := integral_mono hi1 hmi h1
    rw [integral_add (integrable_const _) (hri.const_mul Γ), integral_const, integral_const_mul,
      probReal_univ, one_smul] at h2
    exact h2
  have hmb0 : 0 ≤ mb := integral_nonneg fun x => hrJ0 x
  have hrbm : rb ≤ mb := AdversarialBco.Body.tr_jensen_infDist J hJv b S
  have hs : Real.sqrt (2 / Real.pi) * ‖S‖ ≤ mb + D + rb :=
    AdversarialBco.Body.tr_opNorm_bound J pr hprJ hprd D (fun x hx y hy => Metric.dist_le_diam_of_mem hJb hx hy) b S
  have hEVeq : ∫ z, var w Fe (b + S z) ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = EV :=
    (AdversarialBco.Body.tr_integral_cloud b S (var w Fe) hvc).symm
  rw [hEVeq] at hP3
  have hVs : 0 ≤ var w Fe bstar := Finset.sum_nonneg fun i _ => mul_nonneg (hw i).le (sq_nonneg _)
  have htail : ∀ t0 : ℝ, 0 ≤ t0 → E2 ≤ 2 * (mb + t0) * mb +
      2 * (Real.pi / 2 * ‖S‖) ^ 2 * Real.exp (-t0 ^ 2 / (2 * (Real.pi / 2 * ‖S‖) ^ 2)) := fun t0 ht0 =>
    tail_sq (gaussLaw b S) (fun x => Metric.infDist x J) hrJ0 hrc.measurable hri hr2i (Real.pi / 2 * ‖S‖)
      (by positivity) (fun t ht => conc_r J b S hSpos t ht) t0 ht0
  have hR2 : ∫ x, Metric.infDist x J ^ 2 ∂p ≤ q / 2 * (rb ^ 2 + E2) := by
    rw [hpr2eq, Metric.infDist_zero_of_mem hbJ]; linarith only []
  have hpt : ∀ x, var w Fe x ≤ 2 * VJ (pr x) + 0 + 2 * (n : ℝ) ^ 2 * Metric.infDist x J ^ 2 := by
    intro x
    have h1 := proj_var k w (fun i => (hw i).le) hw1 (fun i => Fe i x) (fun i => f i (pr x))
      (Γ * Metric.infDist x J) (n * Metric.infDist x J)
      (fun i => ⟨by simp only [hFe]; linarith only [hlo i x], by simp only [hFe]; linarith only [hhi i x]⟩)
    simp only [var, mean, hVJ]
    linarith only [h1]
  have hWb : ∫ x, var w Fe x ∂p ≤ 2 * W + 2 * (n : ℝ) ^ 2 * ∫ x, Metric.infDist x J ^ 2 ∂p := by
    have h1 := AdversarialBco.Body.tr_integral_bound p (var w Fe) (fun x => VJ (pr x))
      (fun x => Metric.infDist x J ^ 2) 0 (2 * (n : ℝ) ^ 2) hpv hVJp hpr2 hpt
    rw [hVJeq]; linarith only [h1]
  have hchain := body_chain n d D Δs h gmax (∑ i, w i * f i bstar) (mean w Fe b) EF (∑ i, w i * f i (xmin i)) Δp
    mb rb ‖S‖ T (var w Fe bstar) (var w Fe b) EV (∫ x, var w Fe x ∂p) E2 (∫ x, Metric.infDist x J ^ 2 ∂p) W
    hn' hd' hD1 hsmall hΔg hg1 hh1 hh2 hΔs hFb hΔpeq hΔp hmass hmb0 (hrJ0 b) hrbm hSpos hs hT hVs hP3 hpveq htail
    hR2 hWb hKD
  have hreg : ∫ y, ∑ i, w i * f i y ∂(p.map pr) - ∑ i, w i * sInf (f i '' J) ≤ Δp := by
    obtain ⟨-, hi, he⟩ := hgood (fun y => ∑ i, w i * f i y) hgm ⟨1, fun y hy => (hu01 y hy).1⟩
    rw [he, hinf, hΔpdef]
    have h1 := integral_mono hi hpm (fun x => by
      have := mul_nonneg hΓ0.le (hrJ0 x)
      linarith only [hmeanlo x, this])
    linarith only [h1]
  have hsq : Δp ≤ √(1200000000 * (d : ℝ) ^ 2 * Real.log (n * d * D) * Real.log (2 * n) * W) := by
    calc Δp ≤ |Δp| := le_abs_self _
      _ = √(Δp ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ _ := Real.sqrt_le_sqrt hchain
  have : (0 : ℝ) ≤ 1 / n := by positivity
  linarith only [hreg, hsq, this]


/-- **Proposition 2.2** with `C_0 = 1.2·10^9`, from Theorem 3.1. -/
theorem bodyExplicit_of_dil (hdil : DilTheorem) : BodyExplicit := by
  intro d hd n hn J hJc hJv ⟨c0, hc0⟩ k w F hw hw1 hF
  obtain ⟨k', e, -, hwpos, hsum⟩ := reindex_pos k w hw
  have hw1' : ∑ j, w (e j) = 1 := by
    have h1 := hsum (fun _ => 1)
    simp only [mul_one] at h1
    rw [← h1, hw1]
  obtain ⟨ρ, hρ, hρJ, hgood, hreg⟩ := body_pos hdil hd n hn J hJc hJv c0 hc0 k' (fun j => w (e j))
    (fun j => F (e j)) hwpos hw1' (fun j => hF (e j))
  have hJn : J.Nonempty := ⟨c0, hc0 (Metric.mem_closedBall_self (by norm_num))⟩
  refine ⟨ρ, hρ, hρJ, fun i => ?_, ?_⟩
  · have hext := AdversarialBco.Body.tr_ext J hJv hJn (F i) n (hF i).1 (hF i).2.1 (hF i).2.2 0 le_rfl
    refine hgood (F i) ⟨_, hext.1, fun y hy => (hext.2.1 y hy).symm⟩ ⟨1, fun y hy => ?_⟩
    obtain ⟨h0, h1⟩ := (hF i).2.2 y hy
    rw [abs_le]; constructor <;> linarith
  · simp only [hsum]
    exact hreg

/-- Proposition 2.2 on the inner body of a convex body containing a
unit ball, for every `D ≥ diam K`. -/
theorem bodyHExplicit_of_body (hB : BodyExplicit) : BodyHExplicit := by
  intro d hd n hn K hKc hKv c hc D hD
  obtain ⟨hJc, hJv, -, hJD, -⟩ := AdversarialBco.Body.tr_inner hd n hn K hKc hKv c hc D hD
  have hball := inner_ball n hn K c hc
  have hH := hB d hd n hn _ hJc hJv ⟨c, hball⟩
  refine hypH_mono _ _ _ _ _ _ _ hH ?_
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : 1 ≤ Metric.diam {y | Metric.closedBall y (1 / (n : ℝ)) ⊆ K} :=
    one_le_diam hd _ hJc.isBounded c hball
  have h2 : Metric.diam {y | Metric.closedBall y (1 / (n : ℝ)) ⊆ K} ≤ D :=
    Metric.diam_le_of_forall_dist_le (Metric.diam_nonneg.trans hD) hJD
  have h3 : Real.log (n * d * Metric.diam {y | Metric.closedBall y (1 / (n : ℝ)) ⊆ K}) ≤
      Real.log (n * d * D) :=
    Real.log_le_log (mul_pos (mul_pos (by linarith) (by linarith)) (by linarith))
      (mul_le_mul_of_nonneg_left h2 (by positivity))
  have h4 : 0 ≤ Real.log (2 * n) := Real.log_nonneg (by linarith)
  have h5 : (0 : ℝ) ≤ 1200000000 * (d : ℝ) ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 h5) h4

end AdversarialBco.Body2
