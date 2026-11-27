/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.AsmThr
public import AdversarialBco.Unified.BLOPos
public import AdversarialBco.Unified.BLOSep
public import AdversarialBco.Unified.BLOLocal
public import AdversarialBco.Unified.PosMain
public import AdversarialBco.Unified.SepMath

@[expose] public section

/-!
# (POS) for BL-O's record (`PosRecO`)

`posRecO : PosRecO` at `δpos = δ_BL/3 ≤ δ/4`, by this route:

* TRI-OGD-O in rationals is `triPosT` with the field `stSepR` (`posCastO`), whose vectors are SEP outputs at every
  good stage (`posSepO`) and which is measurable (`posFieldMeasO`); with `sepZero`, Theorem TRI-OGD-O against SEP
  outputs (`triPosT_bad_sep`) at `ℓ = ellPosO d n k_δ r0 R0 ≥ log(m_st/δpos)` bounds by `δpos` the probability under
  the fair coins that the position is not good at the radius `36.4 d λ(ρ_h)`, which is at most
  `R = 134 d (ln(2d + 2))^{1/2}` of `df2oPar` (`tri_par_stage`);
* the position of the record reads the coins of the environment below `K0O` only (`posLocalO`), which are known before
  round `0` on the extension (`ExtOK.coin_adapt`), so it is `𝓕 0`-measurable; its bad event is an event of the
  environment's coins, whose law is `coinStream` (`prob_ext`, `NoisyAdv.coin_law`).
-/

open MeasureTheory

namespace AdversarialBco.Unified.Asm

open AdversarialBco AdversarialBco.Poly AdversarialBco.Unified.World AdversarialBco.Unified.BLO
open AdversarialBco.BitRAM (toE coinStream)
open AdversarialBco.Bit.RQ (triMstQ castP)
open AdversarialBco.Uni (sepZero)

/-- `ℓ_pos ≥ log(m_st/δpos)` at `δpos = δ_BL/3`. -/
theorem ellPosO_ge (d n : ℕ) (δ r0 R0 : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    Real.log (Bit.triMst (r0 : ℝ) (R0 : ℝ) / (dBL d n δ / 3)) ≤ ellPosO d n (kDel δ) r0 R0 := by
  have hm1 : 1 ≤ triMstQ r0 R0 := le_max_left _ _
  set k := kDel δ
  set m := triMstQ r0 R0
  set N := 3 * 2 ^ (19 + k) * (d * n) ^ 3 * m with hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : (Bit.triMst (r0 : ℝ) (R0 : ℝ) : ℝ) = (m : ℝ) := by rw [← Bit.RQ.triMst_eq]
  have heq : (Bit.triMst (r0 : ℝ) (R0 : ℝ) : ℝ) / (dBL d n δ / 3) = (N : ℝ) := by
    rw [hm, hN]
    unfold dBL deltaO
    push_cast
    rw [inv_pow]
    field_simp
    rfl
  have hN0 : (0 : ℝ) < N := by
    rw [hN]
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    push_cast
    positivity
  have hpow : (N : ℝ) ≤ 2 ^ ellPosO d n k r0 R0 := by
    have := Nat.le_pow_clog (by norm_num : 1 < 2) N
    exact_mod_cast this
  rw [heq]
  calc Real.log N ≤ Real.log (2 ^ ellPosO d n k r0 R0) := Real.log_le_log hN0 hpow
    _ = ellPosO d n k r0 R0 * Real.log 2 := by rw [Real.log_pow]
    _ ≤ ellPosO d n k r0 R0 := by
        have h2 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          linarith
        have h0 : (0 : ℝ) ≤ ellPosO d n k r0 R0 := Nat.cast_nonneg _
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- **(POS) for BL-O's record.** -/
theorem posRecO : PosRecO := by
  intro d n δ r0 R0 a K orc hI hc Ω _ μ coin loss noise h
  have hprob := h.prob
  have hr0 : (0 : ℝ) < r0 := by exact_mod_cast hI.hr0
  set gs := stSepR orc a r0 R0 with hgsdef
  set ℓ := ellPosO d n (kDel δ) r0 R0 with hℓdef
  set R36 : ℝ := 36.4 * d * pgLam (Bit.triRh d) with hR36
  set S : Set (ℕ → Bool) := {cs | ¬ PgGood d K R36 (some (UniPos.triPosT gs (toE a) r0 R0 ℓ cs))} with hSdef
  have hcast : ∀ cs, castP (posO d n orc δ r0 R0 a cs) = UniPos.triPosT gs (toE a) r0 R0 ℓ cs :=
    fun cs => posCastO d n orc δ r0 R0 a cs hI.hd hI.hr0
  have hgs : ∀ j, Measurable fun q : PgSp d × E d => gs j q.1 q.2 := posFieldMeasO d orc a r0 R0
  have hTm := UniPos.triPosT_meas gs hgs (toE a) r0 R0 ℓ
  have hSm : MeasurableSet S :=
    (PgMeas.pgGoodMeas d K R36 hI.convex hI.compact.isClosed).compl.preimage hTm
  obtain ⟨hδBL0, -, -, -, -⟩ := thrO d n δ hI.hd hI.hn hI.hδ0 hI.hδ1
  obtain ⟨-, -, hle3, -, -, -⟩ := deltaO_holds d n δ hI.hd hI.hn hI.hδ0 hI.hδ1
  have hδ0 : (0 : ℝ) < δ := by exact_mod_cast hI.hδ0
  have hδ1 : (δ : ℝ) < 1 := by exact_mod_cast hI.hδ1
  have hdn3 : (1 : ℝ) ≤ ((d : ℝ) * n) ^ 3 := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hI.hd
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hI.hn
    exact one_le_pow₀ (by nlinarith)
  have hle : dBL d n δ ≤ δ / 4 := by
    have h1 : dBL d n δ ≤ (2 : ℝ)⁻¹ ^ 19 * δ := le_trans hle3 (div_le_self (by positivity) hdn3)
    have h2 : (2 : ℝ)⁻¹ ^ 19 ≤ 1 / 4 := by norm_num
    nlinarith
  set δpos := dBL d n δ / 3 with hδpos
  have hp0 : 0 < δpos := by positivity
  have hp4 : δpos ≤ δ / 4 := by rw [hδpos]; linarith
  have hp1 : δpos < 1 := by linarith
  have hbad : coinStream S ≤ ENNReal.ofReal δpos :=
    UniPos.triPosT_bad_sep sepZero hI.hd K hI.convex hI.compact.isClosed (toE a) (fun i => ⟨a i, rfl⟩) r0 R0
      ⟨r0, rfl⟩ hr0 hI.ball_in hI.ball_out gs hgs
      (posSepO d K orc a r0 R0 hI.hd hI.convex hI.compact.isClosed hI.hr0 hI.ball_in hI.ball_out hI.orc) δpos hp0
      hp1 ℓ (ellPosO_ge d n δ r0 R0 hI.hd hI.hn)
  have hE := extO_ok n δ r0 R0 a h
  -- the position reads the coins below `K0O` only
  set K0 := K0O d n δ r0 R0 with hK0
  let tr : (ℕ → Bool) → ℕ → Bool := fun cs j => if j < K0 then cs j else false
  have hpos : ∀ p : Ω × (ℕ → ℝ), (recO n δ r0 R0 a orc h hI.convex).pos p =
      UniPos.triPosT gs (toE a) r0 R0 ℓ (tr (coin p.1)) := by
    intro p
    show castP (posO d n orc δ r0 R0 a (coin p.1)) = _
    rw [(posLocalO d n orc δ r0 R0 a (coin p.1) (tr (coin p.1)) hI.hδ0 fun j hj => by simp only [tr, show j < K0 from hj, ↓reduceIte]).2, hcast]
  refine ⟨δpos, hp0.le, hp4, ?_, ?_⟩
  · -- known before round `0`
    have htr : Measurable[(extO n δ r0 R0 a h).𝓕 0] fun p : Ω × (ℕ → ℝ) => tr (coin p.1) := by
      refine (meas_pi_iff _).mpr fun j => ?_
      by_cases hj : j < K0
      · simp only [tr, hj, ↓reduceIte]
        refine hE.coin_adapt 0 (Nat.zero_le n) j ?_
        simp only [Bit.Sched.blkStart, hK0, K0O] at hj ⊢
        omega
      · simp only [tr, hj, ↓reduceIte]
        exact measurable_const
    have : (recO n δ r0 R0 a orc h hI.convex).pos = fun p => UniPos.triPosT gs (toE a) r0 R0 ℓ (tr (coin p.1)) :=
      funext hpos
    rw [this]
    exact hTm.comp htr
  · -- good off an event of the coins of probability `δpos`
    have hRle : R36 ≤ (df2oPar d n (dBL d n δ)).R := (Bit.tri_par_stage d hI.hd).2.2
    have hsub : {p | ¬ (recO n δ r0 R0 a orc h hI.convex).Case (dBL d n δ) p} ⊆ {p | p.1 ∈ coin ⁻¹' S} := by
      intro p hp hg
      apply hp
      show PgGood d K (df2oPar d n (dBL d n δ)).R (some ((recO n δ r0 R0 a orc h hI.convex).pos p))
      rw [show (recO n δ r0 R0 a orc h hI.convex).pos p = UniPos.triPosT gs (toE a) r0 R0 ℓ (coin p.1) from
        (hcast (coin p.1))]
      exact pgGood_mono d K _ _ hRle _ hg
    calc (extO n δ r0 R0 a h).μ {p | ¬ (recO n δ r0 R0 a orc h hI.convex).Case (dBL d n δ) p}
        ≤ (extO n δ r0 R0 a h).μ {p | p.1 ∈ coin ⁻¹' S} := measure_mono hsub
      _ = μ (coin ⁻¹' S) := by rw [hE.meas_eq]; exact prob_ext μ _
      _ = coinStream S := by rw [← h.coin_law, Measure.map_apply h.coin_meas hSm]
      _ ≤ ENNReal.ofReal δpos := hbad

end AdversarialBco.Unified.Asm
