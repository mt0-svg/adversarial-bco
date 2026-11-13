/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSetupCall
public import AdversarialBco.Bit.Transfer.XBLSetupRowLink

@[expose] public section

/-!
# BL's setup on the machine: the cells at the end of the setup are `BLInv`

`blinv_mk`: an environment whose registers, slots and arrays hold what the setup leaves (PARAM's copies, the frame
centre, the position, P3's count and flag, the epoch start, P5's mode) satisfies `BLInv` at round `0` with the mode
`mode0`. The machine's test of P5 (`0 < fl` or `2^pF < 2 ε'_num`) is P5's (`mode_cond_iff`).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

theorem prmCopies_cover : ∀ y < 22, 4 ≤ y → ∃ p ∈ prmCopies, p.1 = y := by decide

/-- P5's test on the machine is P5's test. -/
theorem mode_cond_iff {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {cs : ℕ → Bool} (hd : 1 ≤ d)
    (hn : 1 ≤ n) {fl D : ℤ} {xm : ℕ → ℤ} (hD : 0 < D)
    (hfl : 0 < fl ↔ s3bad (NmI d n m A b) (DnI d n m A b) (fun k : Fin d => xm k) D m)
    (hS1 : ∀ j : Fin d, (xm j : ℚ) / D = (posQ d n m A b cs).1 j) :
    (0 < fl ∨ PFZ d n < 2 * epsZ d n) ↔
      (1 / 2 < (cfgOf RoutinesQ d n m A b cs).par.eps ∨ ∃ i, (cfgOf RoutinesQ d n m A b cs).β i ≤ 0) := by
  have e1 : (fun j : Fin d => ((fun k : Fin d => xm k) j : ℚ) / D) = (posQ d n m A b cs).1 := funext hS1
  have h1 : 0 < fl ↔ ∃ i, (cfgOf RoutinesQ d n m A b cs).β i ≤ 0 := by
    rw [hfl, s3bad_iff A b _ D hD, e1]
    rfl
  have h2 : PFZ d n < 2 * epsZ d n ↔ 1 / 2 < (cfgOf RoutinesQ d n m A b cs).par.eps := by
    show _ ↔ 1 / 2 < (par d n).eps
    rw [PieceA.par_eps, half_lt_up_iff, ← PieceA.par_eps, qn_par_eps hd hn, PFZ]
  rw [h1, h2, or_comm]

set_option maxHeartbeats 2000000 in
/-- **The end of the setup is `BLInv`.** -/
theorem blinv_mk {L : Layout} {n m E : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {cs : ℕ → Bool}
    {σ : Env d} {D fl : ℤ} {xm xa xc : ℕ → ℤ} {sf st : ℕ}
    (hd : 1 ≤ d) (hn : 1 ≤ n) (hlay : BLLay L) (hEG : 75 * parG d n + 343 ≤ E) (hEf : sf ≤ E) (hEt : st ≤ E)
    (hrD : σ.nat rD = d) (hrM : σ.nat rM = m) (hrMk : σ.nat rMk = keptCnt A m) (hrOne : σ.nat rOne = 1)
    (hrP : σ.nat rP = (par d n).p) (hrPF : σ.nat rPF = (par d n).pF) (hrNb : σ.nat rNb = Sched.nBlk d)
    (hrB : σ.nat rB = (par d n).B)
    (hsZ : σ.sc sZ = 0) (hsN : σ.sc sN = n) (hcp : ∀ p ∈ prmCopies, σ.sc p.1 = pv d n (p.2 - 30))
    (hsF : σ.sc sFirst = 1) (hsDmu : σ.sc sDmu = 1) (hsK : σ.sc sK = 0) (hsL : σ.sc sL = 0)
    (hsDS : σ.sc sDS = D) (hsMode : σ.sc sMode = ((if 0 < fl ∨ PFZ d n < 2 * epsZ d n then 0 else 2 : ℤ) : ℝ))
    (hfl : 0 < fl ↔ s3bad (NmI d n m A b) (DnI d n m A b) (fun k : Fin d => xm k) D m)
    (haMuS : ∀ k, σ.arr aMuS k = if k < d then (xm k : ℝ) else 0)
    (haAS : ∀ k, σ.arr aAS k = if k < d * d then (xa k : ℝ) else 0)
    (haC : ∀ k, σ.arr aC k = if k < d + 1 then (xc k : ℝ) else 0)
    (haMu : ∀ k, σ.arr aMu k = 0) (hab : ∀ k, σ.arr ab k = 0) (haG : ∀ k, σ.arr aG k = 0)
    (haA : ∀ k, σ.arr aA k = if ∃ j < d, k = 0 + (d + 1) * j then (A0Z d n : ℝ) else 0)
    (haB : ∀ k, σ.arr aB k = if ∃ j < d, k = 0 + (d + 1) * j then (B0Z d n : ℝ) else 0)
    (hD0 : 0 < D) (hDs : D < 2 ^ st) (hxm : ∀ k < d, |xm k| < 2 ^ st) (hxa : ∀ k < d * d, |xa k| < 2 ^ st)
    (hxc : ∀ k < d + 1, |xc k| < 2 ^ sf) (hc0 : 0 < xc 0)
    (hS1 : ∀ j : Fin d, (xm j : ℚ) / D = (posQ d n m A b cs).1 j)
    (hS2 : ∀ i j : Fin d, (xa (d * i + j) : ℚ) / D = (posQ d n m A b cs).2 i j)
    (hc : ∀ j : Fin d, (xc (j + 1) : ℚ) / xc 0 = frameQ d n m A b j)
    (hr : σ.rounds = 0) (hdr : σ.draws = K0Q d n) :
    BLInv L n m (K0Q d n) E (cfgOf RoutinesQ d n m A b cs) (mode0 (cfgOf RoutinesQ d n m A b cs)) 0 σ := by
  obtain ⟨hS, hN, hA⟩ := id hlay
  simp only [oE, rEE, aWE] at hS hN hA
  have cp : ∀ y k, (y, k) ∈ prmCopies → σ.sc y = pv d n (k - 30) := fun y k h => hcp _ h
  have hGE : (2 : ℤ) ^ (75 * parG d n + 343) ≤ 2 ^ E := pow_le_pow_right₀ (by norm_num) hEG
  have hfE : (2 : ℤ) ^ sf ≤ 2 ^ E := pow_le_pow_right₀ (by norm_num) hEf
  have htE : (2 : ℤ) ^ st ≤ 2 ^ E := pow_le_pow_right₀ (by norm_num) hEt
  have hE1 : (2 : ℤ) ≤ 2 ^ E := by
    have : (2 : ℤ) ^ 1 ≤ 2 ^ E := pow_le_pow_right₀ (by norm_num) (by omega)
    simpa using this
  have hnE : (n : ℤ) ≤ 2 ^ E := by
    have h1 : n ≤ 2 ^ parG d n := n_le_G hd hn
    have h2 : (2 : ℤ) ^ parG d n ≤ 2 ^ E := pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 : (n : ℤ) ≤ 2 ^ parG d n := by exact_mod_cast h1
    exact h3.trans h2
  have pvE : ∀ k < 93, |pv d n k| ≤ 2 ^ E := fun k hk => (pv_abs hd hn hk).trans hGE
  have hA0E : |A0Z d n| ≤ 2 ^ E := by rw [← pv_89 hd hn]; exact pvE 89 (by norm_num)
  have hB0E : |B0Z d n| ≤ 2 ^ E := by rw [← pv_90 hd hn]; exact pvE 90 (by norm_num)
  have hmode := mode_cond_iff (cs := cs) hd hn hD0 hfl hS1
  refine ⟨⟨by simp only [nN0]; omega, by simp only [nS0]; omega, by simp only [nA0]; omega⟩,
    ⟨hrD, hrM, hrMk.trans (keptCnt_eq A), hrOne, hrP, hrPF, hrNb, hrB⟩, ⟨hsZ, hsN, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, hr, ?_, ?_, ?_⟩
  -- the constants
  · rw [cp _ 65 (by decide), show 65 - 30 = 35 from rfl, pv_35]; push_cast; rfl
  · rw [cp _ 66 (by decide), show 66 - 30 = 36 from rfl, pv_36]; push_cast; rfl
  · rw [cp _ 64 (by decide), show 64 - 30 = 34 from rfl, pv_34]; push_cast; rfl
  · rw [cp _ 69 (by decide), show 69 - 30 = 39 from rfl, pv_39]
    show _ = (((par d n).eHat⁻¹ : ℚ) : ℝ)
    rw [par_eHat_inv]; push_cast; rfl
  · rw [cp _ 48 (by decide), show 48 - 30 = 18 from rfl, pv_18]; rfl
  · rw [cp _ 70 (by decide), show 70 - 30 = 40 from rfl, pv_40]
    show _ = (((par d n).Lam : ℕ) : ℝ)
    rw [par_Lam]; push_cast; rfl
  · rw [cp _ 121 (by decide), show 121 - 30 = 91 from rfl, pv_91]
    show _ = (((par d n).Rint : ℕ) : ℝ)
    rw [← Rint_eq]; push_cast; rfl
  -- PARAM's rational fields
  · rw [cp _ 99 (by decide), show 99 - 30 = 69 from rfl, pv_69 hd hn, ← qn_par_eps hd hn]; rfl
  · rw [cp _ 100 (by decide), show 100 - 30 = 70 from rfl, pv_70 hd hn, ← qn_par_lam hd hn]; rfl
  · rw [cp _ 101 (by decide), show 101 - 30 = 71 from rfl, pv_71 hd hn, ← qn_par_eta hd hn]; rfl
  · rw [cp _ 103 (by decide), show 103 - 30 = 73 from rfl, pv_73 hd hn, ← qn_par_rho hd hn]; rfl
  · rw [cp _ 104 (by decide), show 104 - 30 = 74 from rfl, pv_74 hd hn, ← qn_par_kapc hd hn]; rfl
  · rw [cp _ 105 (by decide), show 105 - 30 = 75 from rfl, pv_75 hd hn, ← qn_par_nu hd hn]; rfl
  · rw [cp _ 110 (by decide), show 110 - 30 = 80 from rfl, pv_80, ← qn_par_R]; rfl
  · rw [cp _ 111 (by decide), show 111 - 30 = 81 from rfl, pv_81, ← qn_par_sb]; rfl
  · rw [cp _ 115 (by decide), show 115 - 30 = 85 from rfl, pv_85 hd hn, ← qn_par_W hd hn]; rfl
  · rw [cp _ 119 (by decide), show 119 - 30 = 89 from rfl, pv_89 hd hn, ← qn_par_A0 hd hn]; rfl
  · rw [cp _ 120 (by decide), show 120 - 30 = 90 from rfl, pv_90 hd hn, ← qn_par_B0 hd hn]; rfl
  -- the position
  · refine ⟨D, hD0, hsDS, fun j => ⟨xm j, by rw [haMuS, if_pos j.2], hS1 j⟩, fun i j => ⟨xa (d * i + j), ?_, hS2 i j⟩⟩
    have : d * (i : ℕ) + j < d * d := by
      have := i.2; have := j.2; nlinarith
    rw [haAS, if_pos this]
  -- the frame centre
  · refine ⟨xc 0, hc0, by rw [haC, if_pos (by omega)], fun j => ⟨xc (j + 1), ?_, hc j⟩⟩
    rw [haC, if_pos (by omega)]
  -- the mode
  · unfold mode0
    split_ifs with hC
    · show σ.sc sMode = 0
      rw [hsMode, if_pos (hmode.2 hC)]; simp
    · refine ⟨by rw [hsMode, if_neg (fun h => hC (hmode.1 h))]; simp, ?_⟩
      have hA0 : OnG (par d n).p (par d n).A0 := by rw [PieceA.par_A0]; exact onG_rnd_s _ _
      have hB0 : OnG (par d n).p (par d n).B0 := by rw [PieceA.par_B0]; exact onG_rnd_s _ _
      obtain ⟨z1, z2⟩ := onG_zero (par d n).p
      refine ⟨by rw [hsF]; simp [init], ⟨1, one_pos, by rw [hsDmu]; simp, fun j => ⟨0, by rw [haMu]; simp,
        by simp [init]⟩⟩, fun i j => ?_, fun i j => ?_, fun j => ?_, ?_, fun j => ?_, ?_⟩
      · show σ.arr aA (d * i + j) = qn (par d n).p (((par d n).A0 • 1 : Matrix (Fin d) (Fin d) ℚ) i j) ∧ _
        refine ⟨?_, onG_smul_one _ _ hA0 i j⟩
        rw [qn_smul_one, haA]
        by_cases hij : i = j
        · rw [if_pos hij, if_pos ((diag_iff i j).2 hij), qn_par_A0 hd hn]
        · rw [if_neg hij, if_neg (fun h => hij ((diag_iff i j).1 h))]; simp
      · show σ.arr aB (d * i + j) = qn (par d n).p (((par d n).B0 • 1 : Matrix (Fin d) (Fin d) ℚ) i j) ∧ _
        refine ⟨?_, onG_smul_one _ _ hB0 i j⟩
        rw [qn_smul_one, haB]
        by_cases hij : i = j
        · rw [if_pos hij, if_pos ((diag_iff i j).2 hij), qn_par_B0 hd hn]
        · rw [if_neg hij, if_neg (fun h => hij ((diag_iff i j).1 h))]; simp
      · show σ.arr ab j = qn (par d n).p ((0 : Fin d → ℚ) j) ∧ OnG (par d n).p ((0 : Fin d → ℚ) j)
        rw [Pi.zero_apply, z2, hab]; exact ⟨by simp, z1⟩
      · show σ.sc sK = qn (par d n).p 0 ∧ OnG (par d n).p 0
        rw [z2, hsK]; exact ⟨by simp, z1⟩
      · show σ.arr aG j = qn (par d n).p ((0 : Fin d → ℚ) j) ∧ OnG (par d n).p ((0 : Fin d → ℚ) j)
        rw [Pi.zero_apply, z2, haG]; exact ⟨by simp, z1⟩
      · show σ.sc sL = qn (par d n).p 0 ∧ OnG (par d n).p 0
        rw [z2, hsL]; exact ⟨by simp, z1⟩
  -- the coins
  · rw [hdr]; simp [Sched.blkStart]
  -- the slots
  · intro y hy
    simp only [nSP] at hy
    rcases (show y < 4 ∨ (4 ≤ y ∧ y < 22) ∨ 22 ≤ y by omega) with h | h | h
    · interval_cases y
      · exact ⟨0, hsZ.trans (by simp), by simp⟩
      · refine ⟨_, hsMode, ?_⟩
        split_ifs <;> simp [hE1]
      · exact ⟨1, hsF.trans (by simp), by simp; linarith⟩
      · exact ⟨n, hsN.trans (by simp), by rw [abs_of_nonneg (by positivity)]; exact hnE⟩
    · obtain ⟨p, hp, rfl⟩ := prmCopies_cover y h.2 h.1
      exact ⟨_, hcp p hp, pvE _ (prmCopies_ok.1 p hp).2.2.2⟩
    · interval_cases y
      · exact ⟨D, hsDS, by rw [abs_of_pos hD0]; exact hDs.le.trans htE⟩
      · exact ⟨1, hsDmu.trans (by simp), by simp; linarith⟩
      · exact ⟨0, hsK.trans (by simp), by simp⟩
      · exact ⟨0, hsL.trans (by simp), by simp⟩
  -- the arrays
  · intro a ha k hk
    simp only [nAP] at ha
    interval_cases a
    · rw [haMuS]
      split_ifs with h
      · exact ⟨xm k, rfl, (hxm k h).le.trans htE⟩
      · exact ⟨0, by simp, by simp⟩
    · rw [haAS]
      split_ifs with h
      · exact ⟨xa k, rfl, (hxa k h).le.trans htE⟩
      · exact ⟨0, by simp, by simp⟩
    · rw [haC]
      split_ifs with h
      · exact ⟨xc k, rfl, (hxc k h).le.trans hfE⟩
      · exact ⟨0, by simp, by simp⟩
    · exact ⟨0, (haMu k).trans (by simp), by simp⟩
    · rw [haA]
      split_ifs with h
      · exact ⟨_, rfl, hA0E⟩
      · exact ⟨0, by simp, by simp⟩
    · rw [haB]
      split_ifs with h
      · exact ⟨_, rfl, hB0E⟩
      · exact ⟨0, by simp, by simp⟩
    · exact ⟨0, (hab k).trans (by simp), by simp⟩
    · exact ⟨0, (haG k).trans (by simp), by simp⟩

end AdversarialBco.Bit.Transfer.BLM
