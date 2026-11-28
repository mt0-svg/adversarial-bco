/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.Interfaces
public import AdversarialBco.Unified.AsmPos
public import AdversarialBco.Unified.AsmBits

@[expose] public section

/-!
# (POS) and the bit clause for BL-OW's record

`posRecUW : PosRecUW I` and `bitsRecUW : BitsRecUW I` for every `ImplW`: the position, the soundness event and the
coupled world of `recUW` are `recO`'s, and the proofs of `posRecO` (Unified/AsmPos.lean) and `bitsRecO`
(Unified/AsmBits.lean) never read the run case `RunCaseO`, so they are copied here with the case of Theorem UW in its
place. `Case` reads the level only through `R`, which is the same at every level (`parW_R`).
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.UW

open AdversarialBco AdversarialBco.Poly AdversarialBco.Unified.World AdversarialBco.Unified.BLO
open AdversarialBco.Unified.Asm
open AdversarialBco.BitRAM (toE coinStream)
open AdversarialBco.Bit.RQ (triMstQ castP)
open AdversarialBco.Uni (sepZero)

variable {d : ℕ}

/-- **(POS) for BL-OW's record** (`posRecO` at the level `δc`). -/
theorem posRecUW (I : ImplW) : PosRecUW I := by
  intro d n δ r0 R0 a K orc hI _ Ω _ μ coin loss noise h
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
  have hpos : ∀ p : Ω × (ℕ → ℝ), (recUW I n δ r0 R0 a orc h hI.convex).pos p =
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
    have : (recUW I n δ r0 R0 a orc h hI.convex).pos = fun p => UniPos.triPosT gs (toE a) r0 R0 ℓ (tr (coin p.1)) :=
      funext hpos
    rw [this]
    exact hTm.comp htr
  · -- good off an event of the coins of probability `δpos`
    have hRle : R36 ≤ (df2oPar d n (dBL d n δ)).R := (Bit.tri_par_stage d hI.hd).2.2
    have hsub : {p | ¬ (recUW I n δ r0 R0 a orc h hI.convex).Case (refAt I d n δ).δc p} ⊆ {p | p.1 ∈ coin ⁻¹' S} := by
      intro p hp hg
      apply hp
      show PgGood d K (df2oPar d n (dBL d n δ)).R (some ((recUW I n δ r0 R0 a orc h hI.convex).pos p))
      rw [show (recUW I n δ r0 R0 a orc h hI.convex).pos p = UniPos.triPosT gs (toE a) r0 R0 ℓ (coin p.1) from
        (hcast (coin p.1))]
      exact pgGood_mono d K _ _ hRle _ hg
    calc (extO n δ r0 R0 a h).μ {p | ¬ (recUW I n δ r0 R0 a orc h hI.convex).Case (refAt I d n δ).δc p}
        ≤ (extO n δ r0 R0 a h).μ {p | p.1 ∈ coin ⁻¹' S} := measure_mono hsub
      _ = μ (coin ⁻¹' S) := by rw [hE.meas_eq]; exact prob_ext μ _
      _ = coinStream S := by rw [← h.coin_law, Measure.map_apply h.coin_meas hSm]
      _ ≤ ENNReal.ofReal δpos := hbad

/-- **The bit clause for BL-OW's record** (`bitsRecO`). -/
theorem bitsRecUW (I : ImplW) : BitsRecUW I := by
  intro d n δ r0 R0 a K orc hI _ Ω _ μ coin loss noise h
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

end AdversarialBco.UW
