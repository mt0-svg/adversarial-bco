/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.AsmThr
public import AdversarialBco.Unified.BLOLocal
public import AdversarialBco.Unified.WorldShadow
public import AdversarialBco.Unified.LeafProb
public import AdversarialBco.Bit.PieceB

@[expose] public section

/-!
# The bit clause (O4) for BL-O's record (`BitsRecO`)

`bitsRecO : BitsRecO` at `δbits = 2^{-p}/4 + 1/(7 N_e)`, `p` and `N_e` of `parO`:

* `E_bits` (`EbitsO`): for `t < n` the draws of BL-O read the coins below `D(t + 1) ≤ blkStart n 0` only
  (`DrawLocalO`), which are the digits of the world's stream (`ExtOK.beta`), so they are BL's draws on the stream
  (`drawO_eq_beta`); off the bad Box-Muller events of the blocks of the rounds `t < n` they are within `e_ξ`, `e_ζ`
  (`ebitsO_compl_subset`, with the error of a block of Bit/PieceB.lean); each block event has probability at
  most `2^{-B/2}` under the stream's law (`gauss_bad_le`), and `n (⌈d/2⌉ + 1) 2^{-B/2} ≤ 2^{-p}/4` (`coins_arith`);
* `NoClip` (`NoClipO`): `E exp(ε_t²) ≤ 2` (W2), so `P(|ε_t| ≥ c) ≤ 2 e^{-c²} ≤ 2/(14 n N_e)` at
  `c = 3 + 4 (ln(14 n N_e))^{1/2}` (`uni_subg_tail`), and the `n` rounds sum to `1/(7 N_e)`;
* `2^{-p}/4 + 1/(7 N_e) ≤ 1/(2 N_e) ≤ δ/8`, since `N_e < 2^p` and `N_e ≥ 2^{17 + k_δ} > 2^{17}/δ` (`DeltaO`).
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Unified.Asm

open AdversarialBco AdversarialBco.Poly AdversarialBco.Unified.World AdversarialBco.Unified.BLO
open AdversarialBco.RealRAM (gaussStream)
open AdversarialBco.Bit.Cpl (cIdx ξc zc)
open AdversarialBco.Bit.Sched (beta blkStart nBlk bmInv blkPair)
open AdversarialBco.Bit.BLP (draw gOut blkUW)
open AdversarialBco.Bit.PieceB (badBM errB errB_le gOut_err gauss_bad_le blkPair_draw blkPair_dither coins_arith
  pairOf_ne)

variable {d : ℕ}

/-- `B ≥ 8` and `B` even at `parO`. -/
theorem parO_B (d n : ℕ) (δ : ℚ) : 8 ≤ (parO d n δ).B ∧ Even (parO d n δ).B := by
  refine ⟨?_, ?_⟩
  · show 8 ≤ 2 * (10 * (NeO d n (kDel δ)).size + 16 * d.size + 160 + (n * (d + 2)).size + 2)
    omega
  · exact ⟨_, (two_mul _)⟩

/-- The block length of `parO` in terms of its precision `p`. -/
theorem parO_B_eq (d n : ℕ) (δ : ℚ) : (parO d n δ).B = 2 * ((parO d n δ).p + (n * (d + 2)).size + 2) := rfl

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {K : Set (E d)} {coin : Ω → ℕ → Bool}
  {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ}

/-- For `t < n`, BL-O's draw on the environment's coins is BL's draw on the digits of the world's stream. -/
theorem drawO_eq_beta {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ}
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (p : Ω × (ℕ → ℝ)) {t : ℕ}
    (ht : t < n) :
    drawO d n δ r0 R0 (coin p.1) t =
      draw (beta d (K0O d n δ r0 R0) (parO d n δ).B ((extO n δ r0 R0 a h).gs p)) (K0O d n δ r0 R0)
        (parO d n δ).B d t := by
  have hE := extO_ok n δ r0 R0 a h
  set K0 := K0O d n δ r0 R0 with hK0
  set B := (parO d n δ).B with hB
  have hle : ∀ j, j < DO d n δ r0 R0 a (t + 1) → j < blkStart d K0 B n 0 := by
    intro j hj
    have h1 : (t + 1) * nBlk d ≤ n * nBlk d := Nat.mul_le_mul_right _ ht
    have h2 : DO d n δ r0 R0 a (t + 1) ≤ blkStart d K0 B n 0 := by
      show K0 + 2 * B * ((t + 1) * nBlk d + 0) ≤ K0 + 2 * B * (n * nBlk d + 0)
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
    omega
  have hN : DO' d n δ r0 R0 a t ≤ DO d n δ r0 R0 a (t + 1) := by
    show K0 + 2 * B * (t * nBlk d + (nBlk d - 1)) ≤ K0 + 2 * B * ((t + 1) * nBlk d + 0)
    refine Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _
    rw [Nat.succ_mul]
    omega
  obtain ⟨h1, h2⟩ := drawLocalO d n δ r0 R0 a (coin p.1) (beta d K0 B ((extO n δ r0 R0 a h).gs p)) t
  exact Prod.ext (h1 fun j _ hj => (hE.beta p j (hle j (lt_of_lt_of_le hj hN))).symm)
    (h2 fun j _ hj => (hE.beta p j (hle j hj)).symm)

/-- Off the bad events of the blocks of the rounds `t < n`, BL-O's draws are sound. -/
theorem ebitsO_compl_subset {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ}
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) :
    (EbitsO n δ r0 R0 a h)ᶜ ⊆ ⋃ t ∈ Finset.range n, ⋃ q ∈ Finset.range (nBlk d),
      {p | bmInv (blkPair d ((extO n δ r0 R0 a h).gs p) (t * nBlk d + q)) ∈ badBM (parO d n δ).B} := by
  intro p hp
  by_contra hno
  apply hp
  simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_ofPred_eq, not_exists] at hno
  obtain ⟨hB8, hBev⟩ := parO_B d n δ
  have herr := errB_le hB8 hBev
  intro t ht
  rw [drawO_eq_beta h p ht]
  set x := (extO n δ r0 R0 a h).gs p with hx
  have hxi : ∀ i : Fin d, (extO n δ r0 R0 a h).xi t p i = x (cIdx d t i) := fun i => rfl
  have hzz : (extO n δ r0 R0 a h).zz t p 0 = x (cIdx d t (d + 1)) := rfl
  refine ⟨fun i => ?_, ?_⟩
  · have hq : (i : ℕ) / 2 < (d + 1) / 2 := by have := i.2; omega
    have hgood := hno t ht ((i : ℕ) / 2) (by unfold nBlk; omega)
    obtain ⟨e1, e2⟩ := gOut_err (K0 := K0O d n δ r0 R0) t ((i : ℕ) / 2) hB8 x hgood
    rw [blkPair_draw d x t _ hq] at e1 e2
    rw [hxi]
    simp only [draw]
    unfold eXiO
    split_ifs with hi
    · have : 2 * ((i : ℕ) / 2) = (i : ℕ) := by omega
      rw [this] at e1
      exact e1.trans herr
    · have : 2 * ((i : ℕ) / 2) + 1 = (i : ℕ) := by omega
      rw [this] at e2
      exact e2.trans herr
  · have hgood := hno t ht ((d + 1) / 2) (by unfold nBlk; omega)
    obtain ⟨e1, -⟩ := gOut_err (K0 := K0O d n δ r0 R0) t ((d + 1) / 2) hB8 x hgood
    rw [blkPair_dither d x t] at e1
    rw [hzz]
    simp only [draw]
    unfold eZtO
    push_cast
    have h2 : (2 : ℝ) / 2 ^ ((parO d n δ).B / 2) = (4 / 2 ^ ((parO d n δ).B / 2)) / 2 := by ring
    rw [h2, ← sub_div, abs_div, abs_two]
    exact div_le_div_of_nonneg_right (e1.trans herr) (by norm_num)

/-- `P(E_bitsᶜ) ≤ 2^{-p}/4`. -/
theorem ebitsO_bad {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ}
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) :
    (extO n δ r0 R0 a h).μ (EbitsO n δ r0 R0 a h)ᶜ ≤ ENNReal.ofReal (1 / 2 ^ (parO d n δ).p / 4) := by
  set W := extO n δ r0 R0 a h
  have hW := (extO_ok n δ r0 R0 a h).law
  set B := (parO d n δ).B with hB
  have hfst : ∀ S : Set (ℕ → ℝ), W.μ {p | W.gs p ∈ S} ≤ gaussStream S := fun S => by
    rw [← hW.g_law]
    exact Measure.le_map_apply hW.gs_meas.aemeasurable S
  calc W.μ (EbitsO n δ r0 R0 a h)ᶜ
      ≤ W.μ (⋃ t ∈ Finset.range n, ⋃ q ∈ Finset.range (nBlk d),
          {p | bmInv (blkPair d (W.gs p) (t * nBlk d + q)) ∈ badBM B}) :=
        measure_mono (ebitsO_compl_subset h)
    _ ≤ ∑ t ∈ Finset.range n, ∑ q ∈ Finset.range (nBlk d),
          W.μ {p | bmInv (blkPair d (W.gs p) (t * nBlk d + q)) ∈ badBM B} := by
        refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
        exact measure_biUnion_finset_le _ _
    _ ≤ ∑ t ∈ Finset.range n, ∑ q ∈ Finset.range (nBlk d), ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ) / 2)) := by
        refine Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun q _ => ?_
        exact (hfst {x | bmInv (blkPair d x (t * nBlk d + q)) ∈ badBM B}).trans
          (gauss_bad_le (pairOf_ne d (.inr (t * nBlk d + q))) _)
    _ = ENNReal.ofReal ((n : ℝ) * (nBlk d : ℝ) * (2 : ℝ) ^ (-(B : ℝ) / 2)) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, mul_assoc]
    _ ≤ ENNReal.ofReal (1 / 2 ^ (parO d n δ).p / 4) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hc := coins_arith n d (parO d n δ).p
        rw [hB, parO_B_eq]
        simpa [nBlk] using hc

/-- `P(NoClipᶜ) ≤ 1/(7 N_e)`. -/
theorem noClipO_bad {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ} (hd : 1 ≤ d) (hn : 1 ≤ n)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) :
    (extO n δ r0 R0 a h).μ (NoClipO n δ r0 R0 a h)ᶜ ≤ ENNReal.ofReal (1 / (7 * (parO d n δ).Ne)) := by
  set W := extO n δ r0 R0 a h
  have hW := (extO_ok n δ r0 R0 a h).law
  have := hW.prob
  set c := nzBndO d n δ with hc
  set M : ℝ := 14 * n * (parO d n δ).Ne with hM
  have hNe : 1 ≤ (parO d n δ).Ne := by
    show 1 ≤ 15 * 2 ^ (17 + kDel δ) * d ^ 3 * n ^ 4
    have : 0 < 15 * 2 ^ (17 + kDel δ) * d ^ 3 * n ^ 4 := by positivity
    omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hNe1 : (1 : ℝ) ≤ (parO d n δ).Ne := by exact_mod_cast hNe
  have hM1 : 1 ≤ M := by rw [hM]; nlinarith
  have hM0 : 0 < M := by linarith
  have hL : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hc0 : 0 ≤ c := by rw [hc]; unfold nzBndO; positivity
  have hcM : Real.log M ≤ c ^ 2 := by
    rw [hc]
    unfold nzBndO
    have hs := Real.sq_sqrt hL
    have hs0 := Real.sqrt_nonneg (Real.log M)
    nlinarith
  have hexpc : M ≤ Real.exp (c ^ 2) := by
    calc M = Real.exp (Real.log M) := (Real.exp_log hM0).symm
      _ ≤ Real.exp (c ^ 2) := Real.exp_le_exp.mpr hcM
  have hround : ∀ t, W.μ {p | c ≤ |W.nz t p|} ≤ ENNReal.ofReal (2 / M) := by
    intro t
    have hle := hW.HC_le_m0 t
    have hexp : ∫ p, Real.exp (W.nz t p ^ 2) ∂W.μ ≤ 2 := by
      calc ∫ p, Real.exp (W.nz t p ^ 2) ∂W.μ = ∫ p, (W.μ[fun p => Real.exp (W.nz t p ^ 2) | W.HC t]) p ∂W.μ := by
            rw [integral_condExp hle]
        _ ≤ ∫ _p, (2 : ℝ) ∂W.μ := integral_mono_ae integrable_condExp (integrable_const _) (hW.e_exp t)
        _ = 2 := by simp
    have hm : Measurable (W.nz t) := (hW.meas_nz t).mono (W.𝓕.le (t + 1)) le_rfl
    refine (Uni.uni_subg_tail W.μ (W.nz t) hm (hW.e_int t) hexp c hc0).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (by norm_num) hM0 hexpc
  have hsub : (NoClipO n δ r0 R0 a h)ᶜ ⊆ ⋃ t ∈ Finset.range n, {p | c ≤ |W.nz t p|} := by
    intro p hp
    simp only [NoClipO, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hp
    obtain ⟨t, ht, hlt⟩ := hp
    simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_ofPred_eq]
    exact ⟨t, ht, hlt.le⟩
  calc W.μ (NoClipO n δ r0 R0 a h)ᶜ ≤ W.μ (⋃ t ∈ Finset.range n, {p | c ≤ |W.nz t p|}) := measure_mono hsub
    _ ≤ ∑ t ∈ Finset.range n, W.μ {p | c ≤ |W.nz t p|} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _t ∈ Finset.range n, ENNReal.ofReal (2 / M) := Finset.sum_le_sum fun t _ => hround t
    _ = ENNReal.ofReal (n * (2 / M)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal (1 / (7 * (parO d n δ).Ne)) := by
        congr 1
        rw [hM]
        field_simp
        ring

/-- `N_e ≥ 2^{17 + k}`. -/
theorem neO_ge {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (k : ℕ) : (2 : ℝ) ^ 17 * 2 ^ k ≤ NeO d n k := by
  unfold NeO
  push_cast
  have hd3 : (1 : ℝ) ≤ (d : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hd)
  have hn4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast hn)
  have h0 : (0 : ℝ) ≤ 2 ^ 17 * 2 ^ k := by positivity
  have h1 : (1 : ℝ) ≤ (d : ℝ) ^ 3 * (n : ℝ) ^ 4 := one_le_mul_of_one_le_of_one_le hd3 hn4
  have e : (15 : ℝ) * 2 ^ (17 + k) * d ^ 3 * n ^ 4 = 15 * ((2 ^ 17 * 2 ^ k) * ((d : ℝ) ^ 3 * (n : ℝ) ^ 4)) := by
    rw [pow_add]; ring
  rw [e]
  calc (2 : ℝ) ^ 17 * 2 ^ k = (2 ^ 17 * 2 ^ k) * 1 := (mul_one _).symm
    _ ≤ (2 ^ 17 * 2 ^ k) * ((d : ℝ) ^ 3 * (n : ℝ) ^ 4) := mul_le_mul_of_nonneg_left h1 h0
    _ ≤ 15 * ((2 ^ 17 * 2 ^ k) * ((d : ℝ) ^ 3 * (n : ℝ) ^ 4)) :=
        le_mul_of_one_le_left (mul_nonneg h0 (by positivity)) (by norm_num)

/-- The budget of the bit clause: `2^{-p}/4 + 1/(7 N_e) ≤ δ/8` when `N_e < 2^p`, `N_e ≥ 2^{17} y` and `1/y < δ`. -/
theorem bits_budget {δ Ne P y : ℝ} (hNe0 : 0 < Ne) (hy0 : 0 < y) (hy : 1 / y < δ) (hNeR : 2 ^ 17 * y ≤ Ne)
    (hp : Ne < P) : 1 / P / 4 + 1 / (7 * Ne) ≤ δ / 8 := by
  have e1 : 1 / P ≤ 1 / Ne := one_div_le_one_div_of_le hNe0 hp.le
  have e2 : 1 / Ne ≤ 1 / (2 ^ 17 * y) := one_div_le_one_div_of_le (by positivity) hNeR
  have e3 : 1 / ((2 : ℝ) ^ 17 * y) = 1 / y / 131072 := by ring
  have e4 : 1 / (7 * Ne) = 1 / Ne / 7 := by ring
  have e5 : 0 < 1 / y := by positivity
  rw [e4]
  linarith

/-- **(O4), the bit clause, for BL-O's record.** -/
theorem bitsRecO : BitsRecO := by
  intro d n δ r0 R0 a K orc hI hc Ω _ μ coin loss noise h
  set W := extO n δ r0 R0 a h
  set Ne := (parO d n δ).Ne with hNedef
  set p := (parO d n δ).p with hpdef
  have hδ0 : (0 : ℝ) < δ := by exact_mod_cast hI.hδ0
  have hNe0 : (0 : ℝ) < Ne := by
    have : 0 < 15 * 2 ^ (17 + kDel δ) * d ^ 3 * n ^ 4 := by
      have := hI.hd; have := hI.hn; positivity
    exact_mod_cast this
  refine ⟨1 / 2 ^ p / 4 + 1 / (7 * Ne), by positivity, ?_, ?_⟩
  · have hk := (deltaO_holds d n δ hI.hd hI.hn hI.hδ0 hI.hδ1).1
    set k := kDel δ with hkdef
    have hy0 : (0 : ℝ) < 2 ^ k := by positivity
    have hy : 1 / (2 : ℝ) ^ k < δ := (one_div_lt hδ0 hy0).mp hk
    have hNeR : (2 : ℝ) ^ 17 * 2 ^ k ≤ Ne := neO_ge hI.hd hI.hn k
    have hp : (Ne : ℝ) < 2 ^ p := by
      have h1 : Ne < 2 ^ Ne.size := Nat.lt_size_self _
      have h2 : 2 ^ Ne.size ≤ 2 ^ p :=
        Nat.pow_le_pow_right (by norm_num) (by show Ne.size ≤ 10 * Ne.size + 16 * d.size + 160; omega)
      exact_mod_cast h1.trans_le h2
    exact bits_budget hNe0 hy0 hy hNeR hp
  · show W.μ (EbitsO n δ r0 R0 a h ∩ NoClipO n δ r0 R0 a h)ᶜ ≤ _
    rw [Set.compl_inter]
    calc W.μ ((EbitsO n δ r0 R0 a h)ᶜ ∪ (NoClipO n δ r0 R0 a h)ᶜ)
        ≤ W.μ (EbitsO n δ r0 R0 a h)ᶜ + W.μ (NoClipO n δ r0 R0 a h)ᶜ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (1 / 2 ^ p / 4) + ENNReal.ofReal (1 / (7 * Ne)) :=
          add_le_add (ebitsO_bad h) (noClipO_bad hI.hd hI.hn h)
      _ = ENNReal.ofReal (1 / 2 ^ p / 4 + 1 / (7 * Ne)) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm

end AdversarialBco.Unified.Asm
