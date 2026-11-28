/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ProgPure
public import AdversarialBco.Unified.AsmRunMeas

@[expose] public section

/-!
# BL-OW's run on the extension is adapted

Unified/AsmRunMeas.lean with BL-O's run replaced by BL-OW's (UW/ProgPure.lean): BL-OW's mode before round `t` is
`trajRW` on the coins below `D t` and the readings of the rounds `< t` (`modeOW_eq_trajRW`, `trajRW_congr`), a reading
of a round `s < n` is `readGW` at the coins below `D' s` and the readings of the rounds `< s` (`rdOW_eq_readGW`, with
`playIntOW`), and every reading of a round `s < n` is known before round `s + 1` (`readsW_meas`). BL-OW's coin layout,
position and draws are BL-O's, so the windows and the locality facts are Theorem U's (`posLocalO`, `drawLocalO`).
-/

open MeasureTheory

namespace AdversarialBco.UW.BLOW

open AdversarialBco AdversarialBco.Poly AdversarialBco.Unified.World AdversarialBco.Unified.BLO
open AdversarialBco.Unified.Asm
open AdversarialBco.Unified (NoisyAdv envWorld)
open AdversarialBco.BitRAM (toE)
open AdversarialBco.BitRAMO (WorldO clip)
open AdversarialBco.Bit.BLP (St Mode extC extC_pre measurable_param)
open AdversarialBco.Poly.Conj1 (fL measurable_fL)

variable {d : ℕ}

/-! ## BL-OW's run from its coins and its readings -/

/-- BL-OW's mode before round `t` on the coins `cs` and the readings `r` of the rounds. -/
noncomputable def trajRW (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (orc : (Fin d → ℚ) → ℕ → Bool) (cs : ℕ → Bool)
    (r : ℕ → ℤ) : ℕ → Mode d
  | 0 => mode0O orc (cfgOW d n orc δ r0 R0 a cs)
  | t + 1 => stepOW (b0OW d n δ) (y0OW d n δ) orc (cfgOW d n orc δ r0 R0 a cs) n (trajRW n δ r0 R0 a orc cs r t) (drawO d n δ r0 R0 cs t).1
      (drawO d n δ r0 R0 cs t).2 (r t)

/-- BL-OW's mode is `trajRW` on the world's coins and BL-OW's readings. -/
theorem modeOW_eq_trajRW (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (w : WorldO d) (t : ℕ) :
    modeOW d n δ r0 R0 a w t = trajRW n δ r0 R0 a w.orc w.cs (readOW d n δ r0 R0 a w) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [show modeOW d n δ r0 R0 a w (t + 1) = stepOW (b0OW d n δ) (y0OW d n δ) w.orc (cfgWW d n δ r0 R0 a w) n (modeOW d n δ r0 R0 a w t)
      (drawO d n δ r0 R0 w.cs t).1 (drawO d n δ r0 R0 w.cs t).2 (readOW d n δ r0 R0 a w t) from rfl, ih]
    rfl

/-- The configuration reads the coins of the prologue only. -/
theorem cfgOW_congr {n : ℕ} {orc : (Fin d → ℚ) → ℕ → Bool} {δ r0 R0 : ℚ} {a : Fin d → ℚ} {cs cs' : ℕ → Bool}
    (hδ : 0 < δ) (h : ∀ j < K0O d n δ r0 R0, cs j = cs' j) :
    cfgOW d n orc δ r0 R0 a cs = cfgOW d n orc δ r0 R0 a cs' := by
  unfold cfgOW
  rw [(posLocalO d n orc δ r0 R0 a cs cs' hδ h).2]

/-- The draw of round `t` reads the coins below `D (t + 1)` only. -/
theorem drawO_congr {n : ℕ} {δ r0 R0 : ℚ} (a : Fin d → ℚ) {cs cs' : ℕ → Bool} (t : ℕ)
    (h : ∀ j < DO d n δ r0 R0 a (t + 1), cs j = cs' j) : drawO d n δ r0 R0 cs t = drawO d n δ r0 R0 cs' t := by
  obtain ⟨h1, h2⟩ := drawLocalO d n δ r0 R0 a cs cs' t
  exact Prod.ext (h1 fun j _ hj => h j (lt_of_lt_of_le hj (DO'_le_DO_succ t))) (h2 fun j _ hj => h j hj)

/-- `trajRW` before round `t` reads the coins below `D t` and the readings of the rounds `< t` only. -/
theorem trajRW_congr {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ} {orc : (Fin d → ℚ) → ℕ → Bool} (hδ : 0 < δ)
    {cs cs' : ℕ → Bool} {r r' : ℕ → ℤ} (t : ℕ) (hc : ∀ j < DO d n δ r0 R0 a t, cs j = cs' j)
    (hr : ∀ s < t, r s = r' s) : trajRW n δ r0 R0 a orc cs r t = trajRW n δ r0 R0 a orc cs' r' t := by
  have hcfg : cfgOW d n orc δ r0 R0 a cs = cfgOW d n orc δ r0 R0 a cs' :=
    cfgOW_congr hδ fun j hj => hc j (lt_of_lt_of_le hj (K0_le_DO t))
  induction t with
  | zero =>
    show mode0O orc (cfgOW d n orc δ r0 R0 a cs) = mode0O orc (cfgOW d n orc δ r0 R0 a cs')
    rw [hcfg]
  | succ t ih =>
    have hc' : ∀ j < DO d n δ r0 R0 a t, cs j = cs' j := fun j hj => hc j (lt_of_lt_of_le hj (DO_mono (Nat.le_succ t)))
    show stepOW (b0OW d n δ) (y0OW d n δ) orc (cfgOW d n orc δ r0 R0 a cs) n (trajRW n δ r0 R0 a orc cs r t) (drawO d n δ r0 R0 cs t).1
        (drawO d n δ r0 R0 cs t).2 (r t) = stepOW (b0OW d n δ) (y0OW d n δ) orc (cfgOW d n orc δ r0 R0 a cs') n
        (trajRW n δ r0 R0 a orc cs' r' t) (drawO d n δ r0 R0 cs' t).1 (drawO d n δ r0 R0 cs' t).2 (r' t)
    rw [hcfg, ih hc' (fun s hs => hr s (Nat.lt_succ_of_lt hs)), drawO_congr a t hc, hr t (Nat.lt_succ_self t)]

/-! ## The readings are adapted -/

section Meas

variable {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ} {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool}
  {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {coin : Ω → ℕ → Bool} {loss : ℕ → Ω → E d → ℝ}
  {noise : ℕ → Ω → ℝ}

/-- BL-OW's reading of round `s` on the extension. -/
noncomputable def rdOW (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (orc : (Fin d → ℚ) → ℕ → Bool) (coin : Ω → ℕ → Bool)
    (loss : ℕ → Ω → E d → ℝ) (noise : ℕ → Ω → ℝ) (s : ℕ) (p : Ω × (ℕ → ℝ)) : ℤ :=
  readOW d n δ r0 R0 a (envWorld orc coin loss noise p.1) s

/-- The play of round `s` at fixed discrete data: the coins `v.1` below `N`, the readings `v.2` of the rounds `< s`. -/
noncomputable def playGW (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (orc : (Fin d → ℚ) → ℕ → Bool) (s N : ℕ)
    (v : (Fin N → Bool) × (Fin s → ℤ)) : Fin d → ℚ :=
  playPtO orc (cfgOW d n orc δ r0 R0 a (extC v.1)) (trajRW n δ r0 R0 a orc (extC v.1) (extZ v.2) s)
    (drawO d n δ r0 R0 (extC v.1) s).1

/-- The reading of round `s` at fixed discrete data, as a function of the point. -/
noncomputable def readGW (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (orc : (Fin d → ℚ) → ℕ → Bool)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (hK : Convex ℝ K) (s N : ℕ)
    (v : (Fin N → Bool) × (Fin s → ℤ)) (p : Ω × (ℕ → ℝ)) : ℤ :=
  clip (cfgOW d n orc δ r0 R0 a (extC v.1)).qO ⌊(2 : ℝ) ^ (parO d n δ).p *
    (fL K (lossO n δ r0 R0 a h hK).L s ((lossO n δ r0 R0 a h hK).lam s p) (toE (playGW n δ r0 R0 a orc s N v)) +
      (extO n δ r0 R0 a h).nz s p)⌋

/-- The reading of a round `s < n` is `readGW` at the coins below `D' s` and the readings of the rounds `< s`. -/
theorem rdOW_eq_readGW (hI : InpU n δ r0 R0 a K orc)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) {s : ℕ} (hs : s < n)
    (p : Ω × (ℕ → ℝ)) :
    rdOW n δ r0 R0 a orc coin loss noise s p = readGW n δ r0 R0 a orc h hI.convex s (DO' d n δ r0 R0 a s)
      ((fun j : Fin (DO' d n δ r0 R0 a s) => coin p.1 j),
        fun i : Fin s => rdOW n δ r0 R0 a orc coin loss noise i p) p := by
  set w := envWorld orc coin loss noise p.1 with hw
  set N := DO' d n δ r0 R0 a s
  set v : (Fin N → Bool) × (Fin s → ℤ) :=
    ((fun j : Fin N => coin p.1 j), fun i : Fin s => rdOW n δ r0 R0 a orc coin loss noise i p) with hv
  have hδ : 0 < δ := hI.hδ0
  have hcs : ∀ j < N, coin p.1 j = extC v.1 j := extC_pre (coin p.1) N
  have hcfg : cfgWW d n δ r0 R0 a w = cfgOW d n orc δ r0 R0 a (extC v.1) :=
    cfgOW_congr hδ fun j hj => hcs j (lt_of_lt_of_le hj ((K0_le_DO s).trans (DO_le_DO' s)))
  have hm : modeOW d n δ r0 R0 a w s = trajRW n δ r0 R0 a orc (extC v.1) (extZ v.2) s :=
    (modeOW_eq_trajRW n δ r0 R0 a w s).trans (trajRW_congr hδ s
      (fun j hj => hcs j (lt_of_lt_of_le hj (DO_le_DO' s)))
      (fun i hi => extZ_pre (fun i => rdOW n δ r0 R0 a orc coin loss noise i p) s i hi))
  have hdr : (drawO d n δ r0 R0 w.cs s).1 = (drawO d n δ r0 R0 (extC v.1) s).1 :=
    (drawLocalO d n δ r0 R0 a w.cs (extC v.1) s).1 fun j _ hj => hcs j hj
  have hpl : playOW d n δ r0 R0 a w s = playGW n δ r0 R0 a orc s N v := by
    unfold playOW playGW
    rw [← hcfg, ← hm, ← hdr]
    rfl
  have hint : toE (playOW d n δ r0 R0 a w s) ∈ interior K :=
    playIntOW d n δ r0 R0 a K w hI.hd hI.hr0 hI.convex hI.ball_in hI.orc s
  have hf : w.f s (toE (playOW d n δ r0 R0 a w s)) = fL K (lossO n δ r0 R0 a h hI.convex).L s
      ((lossO n δ r0 R0 a h hI.convex).lam s p) (toE (playOW d n δ r0 R0 a w s)) :=
    loss_eq_fL h hI.convex hs p hint
  have he : w.noise s = (extO n δ r0 R0 a h).nz s p := ((extO_ok n δ r0 R0 a h).noise s hs p).symm
  show clip (cfgWW d n δ r0 R0 a w).qO ⌊(2 : ℝ) ^ (parO d n δ).p *
    (w.f s (toE (playOW d n δ r0 R0 a w s)) + w.noise s)⌋ = _
  rw [hf, he, hpl, hcfg]
  rfl

/-- At fixed discrete data, the reading of a round `s < n` is known before round `s + 1`. -/
theorem readGW_meas (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) (hK : Convex ℝ K)
    {s : ℕ} (hs : s < n) (N : ℕ) (v : (Fin N → Bool) × (Fin s → ℤ)) :
    Measurable[(extO n δ r0 R0 a h).𝓕 (s + 1)] (readGW n δ r0 R0 a orc h hK s N v) := by
  set W := extO n δ r0 R0 a h
  set F := lossO n δ r0 R0 a h hK
  have hW := (extO_ok n δ r0 R0 a h).law
  have hl : Measurable[W.𝓕 (s + 1)] (F.lam s) := (F.lam_meas s hs).mono (W.𝓕.mono (Nat.le_succ s)) le_rfl
  have hfL : Measurable fun q : F.Λ × E d => fL K F.L s q.1 q.2 :=
    measurable_fL (fun l => (F.adm s hs l).1) (F.meas s hs)
  have h1 : Measurable[W.𝓕 (s + 1)] fun p =>
      fL K F.L s (F.lam s p) (toE (playGW n δ r0 R0 a orc s N v)) :=
    have hc : Measurable[W.𝓕 (s + 1)] fun _ : Ω × (ℕ → ℝ) => toE (playGW n δ r0 R0 a orc s N v) := measurable_const
    hfL.comp (hl.prodMk hc)
  have h2 : Measurable[W.𝓕 (s + 1)] (W.nz s) := hW.e_adapt (s + 1) s (Nat.lt_succ_self s)
  have h3 : Measurable[W.𝓕 (s + 1)] fun p =>
      ⌊(2 : ℝ) ^ (parO d n δ).p * (fL K F.L s (F.lam s p) (toE (playGW n δ r0 R0 a orc s N v)) + W.nz s p)⌋ :=
    Int.measurable_floor.comp ((h1.add h2).const_mul _)
  exact (measurable_of_countable (clip (cfgOW d n orc δ r0 R0 a (extC v.1)).qO)).comp h3

/-- **The readings are adapted**: the reading of a round `i < s ≤ n` is known before round `s`. -/
theorem readsW_meas (hI : InpU n δ r0 R0 a K orc)
    (h : NoisyAdv K n (DO d n δ r0 R0 a) (DO' d n δ r0 R0 a) μ coin loss noise) :
    ∀ s ≤ n, ∀ i < s, Measurable[(extO n δ r0 R0 a h).𝓕 s] (rdOW n δ r0 R0 a orc coin loss noise i) := by
  set W := extO n δ r0 R0 a h
  have hE := extO_ok n δ r0 R0 a h
  intro s
  induction s with
  | zero => intro _ i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ s ih =>
    intro hs i hi
    have hsn : s < n := hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact (ih hsn.le i hi).mono (W.𝓕.mono (Nat.le_succ s)) le_rfl
    · set N := DO' d n δ r0 R0 a i
      have hP : Measurable[W.𝓕 (i + 1)] fun p : Ω × (ℕ → ℝ) =>
          ((fun j : Fin N => coin p.1 j), fun k : Fin i => rdOW n δ r0 R0 a orc coin loss noise k p) := by
        refine Measurable.prodMk ((meas_pi_iff _).mpr fun j => ?_) ((meas_pi_iff _).mpr fun k => ?_)
        · exact hE.coin_adapt (i + 1) hs j (lt_of_lt_of_le j.2 (DO'_le_DO_succ i))
        · exact (ih hsn.le k k.2).mono (W.𝓕.mono (Nat.le_succ i)) le_rfl
      have heq : rdOW n δ r0 R0 a orc coin loss noise i = fun p =>
          readGW n δ r0 R0 a orc h hI.convex i N
            ((fun j : Fin N => coin p.1 j), fun k : Fin i => rdOW n δ r0 R0 a orc coin loss noise k p) p :=
        funext fun p => rdOW_eq_readGW hI h hsn p
      rw [heq]
      exact measurable_param (mX := W.𝓕 (i + 1)) hP (readGW n δ r0 R0 a orc h hI.convex i N)
        fun v => readGW_meas h hI.convex hsn N v

end Meas

end AdversarialBco.UW.BLOW
