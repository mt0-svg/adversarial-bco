/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLHeadR

@[expose] public section

/-!
# BL's round in mode `run` after R1

`XV.runBL`: from BL's invariant in mode `run` at the round `t` (before R1) and the cells after R1 and the dispatch, the
command `xR24; xR57; xRunT xtail` (R2 to R4: the play and the reading; R5 and R7's scalars; R7's tests, R7 to R9 and
the tail) ends in BL's invariant at the round `t + 1` with the mode `step` gives and BL's play recorded as the point of
round `t`, for any tail that satisfies the frozen tail statement (`TailOK`).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-- BL's round in mode `run` after R1: R2 to R4 (the play, the reading), R5 and R7's scalars, `xRunT`. -/
def xRunBL (xtail : Layout → XCmd) (L : Layout) : XCmd := .seq (xR24 L) (.seq (xR57 L) (xRunT xtail L))

/-- The units of `xRunBL`. -/
def runUnits (d m U K : ℕ) : ℕ := r24Units d m + (r57Units d U + (2 + (2 + (midUnits d U + K))))

set_option maxHeartbeats 8000000 in
/-- **BL's round in mode `run` after R1** (`σ0` the environment at the start of the round, `σ` after R1 and the
dispatch): BL plays, reads, and ends in BL's invariant at the next round with the mode `step` gives. -/
theorem XV.runBL {xtail : Layout → XCmd} {Ct kt nS nN nA : ℕ} (hT : TailOK xtail Ct kt nS nN nA)
    {L : Layout} {w : BitRAM.World d} {n m M K0 E ℓa ℓ t : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    {c : Fin d → ℚ} {S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ} {st : St d} {σ0 σ : Env d}
    (hd1 : 1 ≤ d) (hn1 : 1 ≤ n) (hL : LayOK L d ℓa) (hlay : BLLay L) (hblk : blkBL.OK L nS nN nA)
    (hH : RealRAM.HeightLE A b M) {Mh : ℕ} (hHh : RealRAM.HeightLE A b Mh) (hM1 : 1 ≤ Mh) (hME : Mh ≤ 2 ^ E)
    (hI : BLInv L n m K0 E (mkCfg d n m A b c S) (.run st) t σ0) (hP : SamePers σ0 σ) (hr : σ.rounds = t)
    (hdr : σ.draws = Sched.blkStart d K0 (par d n).B (t + 1) 0)
    (hGam : ∀ i : Fin d, σ.arr aGam i = gamI w.cs K0 (par d n).B d t i)
    (hZ : σ.sc sZeta = zetI w.cs K0 (par d n).B d t)
    (hβ : ∀ i, 0 < (mkCfg d n m A b c S).β i) (he1 : (par d n).eps < 1) (hEB : 4 * gsm_prec (par d n).B ≤ E)
    (hdE : d ≤ 2 ^ E)
    (hobs : 0 ≤ ⌊(2 : ℝ) ^ (par d n).p * w.f t
        (BitRAM.toE (playPt (mkCfg d n m A b c S) (.run st) (draw w.cs K0 (par d n).B d t).1))⌋ ∧
      ⌊(2 : ℝ) ^ (par d n).p * w.f t
        (BitRAM.toE (playPt (mkCfg d n m A b c S) (.run st) (draw w.cs K0 (par d n).B d t).1))⌋ ≤
        2 ^ (par d n).p)
    (hnew : ∀ mu' : Fin d → ℚ,
      let ξ := (draw w.cs K0 (par d n).B d t).1
      let ζ := (draw w.cs K0 (par d n).B d t).2
      let obs := ⌊(2 : ℝ) ^ (par d n).p * w.f t (BitRAM.toE (playPt (mkCfg d n m A b c S) (.run st) ξ))⌋
      step RoutinesQ.ap (mkCfg d n m A b c S) n (.run st) ξ ζ obs =
        .run ⟨false, mu', rA' (mkCfg d n m A b c S) st ξ ζ obs, rB' (mkCfg d n m A b c S) st ξ ζ obs,
          rb' (mkCfg d n m A b c S) st ξ ζ obs, rk' (mkCfg d n m A b c S) st ξ ζ obs,
          rG' (mkCfg d n m A b c S) st ξ ζ obs, rl' (mkCfg d n m A b c S) st ξ ζ obs⟩ →
      StBnd (par d n).p E (par d n).Rint ⟨false, mu', rA' (mkCfg d n m A b c S) st ξ ζ obs,
          rB' (mkCfg d n m A b c S) st ξ ζ obs, rb' (mkCfg d n m A b c S) st ξ ζ obs,
          rk' (mkCfg d n m A b c S) st ξ ζ obs, rG' (mkCfg d n m A b c S) st ξ ζ obs,
          rl' (mkCfg d n m A b c S) st ξ ζ obs⟩ ∧
      ∀ x, ellRI (clearQ (rcallL (mkCfg d n m A b c S) st ξ ζ obs n)) = some x →
        (∀ j, |x j| ≤ 2 ^ E) ∧ ellExp (clearQ (rcallL (mkCfg d n m A b c S) st ξ ζ obs n)) ≤ E)
    (hT1 : 130 * (tG d E + E + 1) + 120 < ℓ) (hTa : 130 * (tG d E + E + 1) + 120 < 2 ^ ℓa)
    (hda : d * d + d < 2 ^ ℓa) (hma : 4 + 2 * ((d + 1) * m) < 2 ^ ℓa)
    (hTt : Ct * (d + m + M.size + n.size + (36 * (tG d E + E + 1) + 30) + 1) ^ kt ≤ ℓ)
    (hTta : Ct * (d + m + M.size + n.size + (36 * (tG d E + E + 1) + 30) + 1) ^ kt < 2 ^ ℓa) :
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xRunBL xtail L) σ
      (runUnits d m (tG d E + E + 1) (Ct * (d + m + M.size + n.size + (36 * (tG d E + E + 1) + 30) + 1) ^ kt))
      (RPost L n m K0 E (mkCfg d n m A b c S)
        (step RoutinesQ.ap (mkCfg d n m A b c S) n (.run st) (draw w.cs K0 (par d n).B d t).1
          (draw w.cs K0 (par d n).B d t).2
          ⌊(2 : ℝ) ^ (par d n).p * w.f t
            (BitRAM.toE (playPt (mkCfg d n m A b c S) (.run st) (draw w.cs K0 (par d n).B d t).1))⌋)
        (t + 1) (Function.update σ.pts t
          (BitRAM.toE (playPt (mkCfg d n m A b c S) (.run st) (draw w.cs K0 (par d n).B d t).1)))) := by
  have hlay' := hlay
  obtain ⟨hS, hN, hAr⟩ := hlay'
  simp only [oE, rEE, aWE] at hS hN hAr
  have hU : ∀ {a b : ℕ}, a ≤ b → (2 : ℤ) ^ a ≤ 2 ^ b := fun h => pow_le_pow_right₀ (by norm_num) h
  have hℓ2 : ∀ {a : ℕ}, a < ℓ → (2 : ℝ) ^ a < 2 ^ ℓ := fun h => pow_lt_pow_right₀ (by norm_num) h
  have hEU : E ≤ tG d E + E + 1 := by unfold tG; omega
  have hdU : d ≤ 2 ^ (tG d E + E + 1) := hdE.trans (Nat.pow_le_pow_right (by norm_num) hEU)
  obtain ⟨c0, -, c2p, -⟩ := hI.consts
  have hpE : (par d n).p ≤ E := pow_two_le (hI.sc_abs (y := s2p) (by decide) (by rw [c2p]; push_cast; rfl))
  have hEℓ : E < ℓ := by unfold tG at hT1; omega
  have hsplit : tG d E + E + 1 = E * d + 11 * E + 3 := by unfold tG; ring
  have hℓ24 : 3 * (E * d) + 33 * E + 11 ≤ ℓ := by rw [hsplit] at hT1; omega
  have hEa : E < 2 ^ ℓa := by unfold tG at hTa; omega
  -- R2 to R4
  have hobsℓ : |((⌊(2 : ℝ) ^ (par d n).p * w.f t
      (BitRAM.toE (playPt (mkCfg d n m A b c S) (.run st) (draw w.cs K0 (par d n).B d t).1))⌋ : ℤ) : ℝ)| <
      2 ^ ℓ := by
    have h1 : ((⌊(2 : ℝ) ^ (par d n).p * w.f t
        (BitRAM.toE (playPt (mkCfg d n m A b c S) (.run st) (draw w.cs K0 (par d n).B d t).1))⌋ : ℤ) : ℝ) ≤
        (2 : ℝ) ^ (par d n).p := by exact_mod_cast hobs.2
    rw [abs_of_nonneg (by exact_mod_cast hobs.1)]
    exact lt_of_le_of_lt h1 (hℓ2 (by omega))
  have hoff : 3 + 2 * ((d + 1) * m) ≤ (ctxOf w n m A b).off := by
    show 3 + 2 * ((d + 1) * m) ≤ 3 + 2 * (d + 1) * m
    rw [mul_assoc]
  refine XV.seq (XV.r24 hL hlay hI hP hr hGam rfl hoff
    hma hHh hM1 hME hβ (by rw [PieceA.par_eps]; exact onG_up _ _) he1 (by rw [PieceA.par_lam]; exact onG_rnd_s _ _)
    hEB hdE hd1 hℓ24 (by omega) (by omega) hobsℓ) fun σ1 ⟨rd1, pts1, obs1, ⟨pN, pD, hpN, hpD, epN, epD, hpt, bpN, bpD⟩,
      aWv1, d1, F1⟩ => ?_
  have P1 : SamePers σ σ1 := ⟨fun j hj => F1.1 j (by simp only [N24, rD2]; omega),
    fun y hy => F1.2.1 y (by simp only [S24, sZeta, nSP, tR] at hy ⊢; omega),
    fun a ha k => F1.2.2 a k (by simp only [A24, aGam, nAP] at ha ⊢; omega)⟩
  have hI1 : BLInv L n m K0 E (mkCfg d n m A b c S) (.run st) (t + 1) σ1 :=
    hI.ofPers (hP.trans P1) rd1 (by rw [d1, hdr]; rfl)
  obtain ⟨r0', -, -, r3', -⟩ := hI1.regs
  obtain ⟨c0', -, c2p', c2pF', c2g', -⟩ := hI1.consts
  obtain ⟨p0', -, -, -, p4', -⟩ := hI1.par
  have bsc : ∀ {y : ℕ} {z : ℤ}, y < nSP → σ1.sc y = z → |z| ≤ 2 ^ (tG d E + E + 1) := fun hy hz =>
    (hI1.sc_abs hy hz).trans (hU hEU)
  have bΓ : ∀ i : Fin d, |gamI w.cs K0 (par d n).B d t i| ≤ 2 ^ (tG d E + E + 1) := fun i =>
    (gamI_abs_le _ _ _ _ _ _).trans (hU (by omega))
  have bZ : |zetI w.cs K0 (par d n).B d t| ≤ 2 ^ (tG d E + E + 1) :=
    (zetI_abs_le _ _ _ _ _).trans (hU (by omega))
  have bO : |⌊(2 : ℝ) ^ (par d n).p * w.f t
      (BitRAM.toE (playPt (mkCfg d n m A b c S) (.run st) (draw w.cs K0 (par d n).B d t).1))⌋| ≤
      2 ^ (tG d E + E + 1) := by
    rw [abs_of_nonneg hobs.1]; exact hobs.2.trans (hU (by omega))
  have eΓ : ∀ i : Fin d, σ1.arr aGam i = gamI w.cs K0 (par d n).B d t i := fun i => by
    rw [F1.2.2 _ _ (by simp only [A24, aGam]; omega), hGam]
  have eZ : σ1.sc sZeta = zetI w.cs K0 (par d n).B d t := by
    rw [F1.2.1 _ (by simp only [S24, sZeta, tR]; omega), hZ]
  have hdE' : (d : ℤ) * 2 ^ (2 * (tG d E + E + 1)) ≤ 2 ^ (3 * (tG d E + E + 1)) := by
    have : (d : ℤ) ≤ 2 ^ (tG d E + E + 1) := by exact_mod_cast hdU
    calc (d : ℤ) * 2 ^ (2 * (tG d E + E + 1)) ≤ 2 ^ (tG d E + E + 1) * 2 ^ (2 * (tG d E + E + 1)) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = 2 ^ (3 * (tG d E + E + 1)) := by rw [← pow_add]; ring_nf
  -- R5 and R7's scalars
  refine XV.seq (XV.r57 hL hlay (σ := σ1) (Q := 2 ^ (par d n).p) (F := 2 ^ (par d n).pF)
    (G := 2 ^ (2 * gsm_prec (par d n).B)) (eN := qn (par d n).pF (par d n).eps)
    (kN := qn (par d n).pF (par d n).kapc) (gz := zetI w.cs K0 (par d n).B d t) (pN := pN) (pD := pD)
    (Γ := fun i => gamI w.cs K0 (par d n).B d t i) (Gu := tG d E + E + 1) (E1 := tG d E + E + 1) r0' r3' c0'
    (by rw [c2p']; push_cast; rfl) (by rw [c2pF']; push_cast; rfl) (by rw [c2g']; push_cast; rfl) p0' p4' eZ epN epD
    obs1 eΓ (bsc (y := s2p) (by decide) (by rw [c2p']; push_cast; rfl))
    (bsc (y := s2pF) (by decide) (by rw [c2pF']; push_cast; rfl))
    (bsc (y := s2g) (by decide) (by rw [c2g']; push_cast; rfl)) (bsc (by decide) p0') (bsc (by decide) p4') bZ bpN bpD
    bO bΓ hdE'
    (by omega) (d_pow_lt hdU (by omega)) (by omega) (by omega)) fun σ2 ⟨v1s, _, ⟨c41, c42, c43⟩, d2, F2⟩ => ?_
  have hI2 : BLInv L n m K0 E (mkCfg d n m A b c S) (.run st) (t + 1) σ2 :=
    hI1.frame F2 (fun y h => by simp only [S57, sGG, nSP, tR] at h ⊢; omega)
      (fun j h => by simp only [N57, rD1, rK] at h; omega) (fun _ _ h => h.elim) d2
  have hξ := congrArg Prod.fst (draw_eq (d := d) w.cs K0 (par d n).B t)
  have hζ := congrArg Prod.snd (draw_eq (d := d) w.cs K0 (par d n).B t)
  refine XV.mono (XV.runT hT (σ := σ2) (t := t + 1) (U := tG d E + E + 1) (gz := zetI w.cs K0 (par d n).B d t)
    (pN := pN) (pD := pD) (Γ := fun i => gamI w.cs K0 (par d n).B d t i) hd1 hn1 hL hlay hblk hH hI2
    (F2.2.2.2.2.trans pts1)
    he1.le c41 c42 c43 v1s (fun i => by rw [F2.2.2.1 _ _ id]; exact aWv1 i)
    (fun j => by rw [F2.2.2.1 _ _ id]; exact eΓ j)
    hξ hζ hpt hpD hEU hdU bZ bpN bpD bO bΓ hnew hT1 hTa hda hTt
    hTta) le_rfl fun σ' h => h

end AdversarialBco.Bit.Transfer.BLM
