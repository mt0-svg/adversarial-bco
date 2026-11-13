/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLRunBL
public import AdversarialBco.Bit.Transfer.XBLRoundG
public import AdversarialBco.Bit.Transfer.XBLExp
public import AdversarialBco.Bit.Transfer.XBLRound

@[expose] public section

/-!
# One round of BL's program

`XV.roundRun`: R1 DRAW and the dispatch of the round command `xRound L xRun` in mode `run` (`sMode = 2`): the coins of
round `t` read, then `xRun` from an environment with the same persistent cells, the round count `t`, the draws of the
next round, the draw in `aGam` and `sZeta`, the same points.

`roundBL_of : TailBL → MagBL → ExpBL → RoundBL`: the round contract of Bit/Transfer/XBLRound.lean, with the command
`xRound L (xRunBL xtail L)`; the modes `off` and `guard` by `XV.roundOG`, the mode `run` by `XV.roundRun` and
`XV.runBL`; `MagBL` bounds the next state, `ExpBL` the exponent of R14's point.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix
open AdversarialBco.RealRAM (Strategy polytope)
open AdversarialBco.Bit.Asm

variable {d : ℕ}

/-! ## R1 and the dispatch in mode `run` -/

/-- **R1 and the dispatch in mode `run`**: the round command runs `xRun` after R1, from an environment with the same
persistent cells, the round count `t`, the next round's draws, the draw of round `t` in `aGam` and `sZeta`. -/
theorem XV.roundRun {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {cs : ℕ → Bool}
    (hX : X.wb.cs = cs) {n m K0 E t K : ℕ} {cfg : Cfg d} {st : St d} {σ : Env d} (xRun : XCmd)
    {Q : Env d → Prop} (hI : BLInv L n m K0 E cfg (.run st) t σ) (hB1 : 1 ≤ cfg.par.B)
    (hE : E + 2 < ℓ) (hℓ : 4 * gsm_prec cfg.par.B + 4 ≤ ℓ) (hℓa : 4 * gsm_prec cfg.par.B + 2 < 2 ^ ℓa)
    (hda : d + 2 < 2 ^ ℓa)
    (hrun : ∀ σ1 : Env d, SamePers σ σ1 → σ1.rounds = t → σ1.draws = Sched.blkStart d K0 cfg.par.B (t + 1) 0 →
      (∀ i : Fin d, σ1.arr aGam i = gamI cs K0 cfg.par.B d t i) → σ1.sc sZeta = zetI cs K0 cfg.par.B d t →
      σ1.pts = σ.pts → XRunsB L X ℓa ℓ xRun σ1 K Q) :
    XRunsB L X ℓa ℓ (xRound L xRun) σ (r1Units d cfg.par.B + (1 + (K + 2))) Q := by
  have hlay' := hlay
  obtain ⟨hS, hN, hAr⟩ := hlay'
  simp only [oE, rEE, aWE] at hS hN hAr
  obtain ⟨r0, -, -, r3, -, -, r6, r7⟩ := hI.regs
  obtain ⟨c0, -⟩ := hI.consts
  have hℓ2 : ∀ {a : ℕ}, a < ℓ → (2 : ℤ) ^ a < 2 ^ ℓ := fun h => pow_lt_pow_right₀ (by norm_num) h
  -- R1
  refine XV.seq (XV.r1 hL hlay hX hB1 r7 r0 r3 r6 c0 hI.draws hℓa hℓ hda) fun σ1 ⟨hg1, hz1, d1, F1⟩ => ?_
  have P1 : SamePers σ σ1 := SamePers.ofFrame F1 (fun y h => by simp only [SR1, nSP, sZeta, oBM] at h ⊢; omega)
    (fun j h => by simp only [NR1, rJ, rT, rD2, rB] at h ⊢; omega)
    (fun a k h => by simp only [AR1, aGam, nAP] at h ⊢; omega)
  -- the dispatch
  refine XV.seq (XV.sconst hL (x := sC2) (by pomega) 2 rfl (by norm_num; exact_mod_cast hℓ2 (a := 1) (by omega)))
    fun σ2 e2 => ?_
  subst e2
  have P2 : SamePers σ (σ1.setSc sC2 ((2 : ℚ) : ℝ)) := P1.trans (samePers_setSc (by decide) _)
  have hm2 : (σ1.setSc sC2 ((2 : ℚ) : ℝ)).sc sMode = σ.sc sMode := P2.2.1 _ (by decide)
  have hmode : σ.sc sMode = 2 := hI.mode.1
  have h2ℓ : (2 : ℝ) < 2 ^ ℓ := by exact_mod_cast hℓ2 (a := 1) (by omega)
  refine XV.ifS_f hL (by pomega) (by pomega) (by rw [hm2, hmode]; simpa using h2ℓ) (by rw [scS]; simpa using h2ℓ)
    (by rw [hm2, scS, hmode]; norm_num) ?_
  refine hrun _ P2 (by simp only [Env.setSc_rounds]; rw [F1.2.2.2.1, hI.rounds])
    (by simp only [Env.setSc_draws]; exact d1)
    (fun i => by simp only [Env.setSc_arr]; exact hg1 i) ?_ (by simp only [Env.setSc_pts]; exact F1.2.2.2.2)
  rw [scO _ (by decide)]
  exact hz1


/-! ## The glue of the round -/

/-- The units of R5 and R7's scalars. -/
theorem units_r57 (d U : ℕ) : r57Units d U ≤ 200 * (d + U + 1) := by
  have h : SL.unitsP sl1Et sl1St = (0, 145) := by rfl
  unfold r57Units; rw [h]; simp only [ev]; omega

/-- The units of R7's roots to R9. -/
theorem units_mid (d U : ℕ) : midUnits d U ≤ 1000 * (d + U + 1) ^ 2 := by
  have h2 : SL.unitsP sl2Et sl2St = (276, 356) := by rfl
  have h3 : SL.unitsP sl3Et sl3St = (0, 52) := by rfl
  have e1 : ieBp.units = 36 := rfl
  have e2 : ieGh.units = 19 := rfl
  have e3 : ieGp.units = 5 := rfl
  have e4 : ieLp.units = 21 := rfl
  unfold midUnits r8Units r9aUnits r9bUnits map2Units
  rw [h2, h3, e1, e2, e3, e4]
  simp only [ev]
  nlinarith [Nat.zero_le (d * U), Nat.zero_le (d * d), Nat.zero_le (U * U)]

/-- PARAM's `W` at the magnitude `75 G + 343`. -/
theorem W_abs {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) : |(par d n).W| ≤ 2 ^ (75 * parG d n + 343) := by
  have hW : OnG (par d n).pF (par d n).W := onG_div_pow _ _
  refine grid_abs hW ?_
  rw [qn_par_W hd hn, ← pv_85 hd hn]
  exact pv_abs hd hn (by norm_num)

/-- A coordinate of the routine's point from the call's radius. -/
theorem x_abs (D : CallQ d) (x : Fin d → ℤ) (h : ellRI (clearQ D) = some x) {a : ℕ} (hR : D.R ≤ 2 ^ a)
    (j : Fin d) : |x j| ≤ 2 ^ (a + ellExp (clearQ D)) := by
  have hq : apQ D = some fun i => (x i : ℚ) / 2 ^ ellExp (clearQ D) := by unfold apQ; rw [h]; rfl
  exact hb_x (x j) (ellExp (clearQ D)) a _ D.R (apQ_abs D _ hq j) hR le_rfl

/-- **R10's and R13's tests** on a round in mode `run` that ends in a state after the epoch's first round. -/
theorem run_facts {cfg : Cfg d} {n : ℕ} {st st' : St d} {ξ : Fin d → ℚ} {ζ : ℚ} {obs : ℤ}
    (h : step RoutinesQ.ap cfg n (.run st) ξ ζ obs = .run st') (hf : st'.first = false) :
    frob2 (rB' cfg st ξ ζ obs) ≤ 2 * (cfg.par.Lam : ℚ) ∧
      ¬ (2 * cfg.par.W) ^ 2 < rwmu cfg st ξ ζ obs ⬝ᵥ rwmu cfg st ξ ζ obs := by
  rw [step_run_tail] at h
  by_cases h7 : ra cfg st ξ ζ obs < 1 / 2 ∨ rq cfg st ξ ζ obs < 1 / 2
  · rw [if_pos h7] at h; cases h
  rw [if_neg h7] at h
  unfold tailMode at h
  by_cases h10 : 2 * (cfg.par.Lam : ℚ) < frob2 (rB' cfg st ξ ζ obs) ∨
      2 * (cfg.par.Lam : ℚ) < frob2 (rA' cfg st ξ ζ obs)
  · rw [if_pos h10] at h; cases h
  rw [if_neg h10] at h
  refine ⟨le_of_not_gt fun h' => h10 (Or.inl h'), fun h13 => ?_⟩
  split at h
  · cases h
  · split_ifs at h
    all_goals first | (cases h; done) | (cases h; simp [init] at hf) | exact absurd h13 ‹_›

/-! ## The round -/

set_option maxHeartbeats 8000000 in
/-- **One round of BL's program** (the round contract of Bit/Transfer/XBLRound.lean) from the tail of the round
(`TailBL`), the magnitudes of BL's state (`MagBL`) and the exponent of the routine's point (`ExpBL`). -/
theorem roundBL_of (hT : TailBL) (hM : MagBL) (hX : ExpBL) : RoundBL := by
  obtain ⟨xtail, Ct, kt, nS, nN, nA, hT⟩ := hT
  obtain ⟨Cm, km, hM⟩ := hM
  obtain ⟨Cx, kx, hX⟩ := hX
  refine ⟨fun L => xRound L (xRunBL xtail L), 10 ^ 12 + Ct * 600 ^ kt + 2000, 2 * kt + 4,
    Cm + Cx * 1501727 ^ kx + 500000, km + kx + 1, nS, nN, nA, ?_⟩
  intro d L w n m M E0 E ℓa ℓ t A b σs σ hin hadm ht hloss hL hlay hblk hpos hCn hC hCa hI
  have hd1 := hin.hd
  have hn1 := hin.hn
  have hpar : (cfgOf RoutinesQ d n m A b w.cs).par = par d n := rfl
  have hW0e : ∀ e, d + n.size + e + 1 ≤ (d + m + M.size + n.size + E0 + 1) + e := fun e => by omega
  -- the bound `E`
  have hsz := gl_sz d
  have hG := parG_le (d := d) (n := n) hd1 hn1
  obtain ⟨eM, eX, eB, eW0⟩ := gl_E (d + m + M.size + n.size + E0 + 1) (parG d n) Cm km Cx kx E (by omega)
    (by omega) hCn
  have hB := B_le (d := d) (n := n) hd1
  have hB8 : 8 ≤ (par d n).B := by simp only [par]; omega
  have hgs := gl_gsm (par d n).B
  have hEB : 4 * gsm_prec (par d n).B ≤ E := by omega
  have hdE : d ≤ 2 ^ E := gl_dE d E (by omega)
  have hME : M + 1 ≤ 2 ^ E := gl_sizeM M E (by omega)
  -- the width
  have hW1 : 1 ≤ d + m + M.size + n.size + E + 1 := by omega
  have hCk : 2000 ≤ 10 ^ 12 + Ct * 600 ^ kt + 2000 := by omega
  have hk2 : 2 ≤ 2 * kt + 4 := by omega
  have hUW : tG d E + E + 1 ≤ 12 * (d + m + M.size + n.size + E + 1) ^ 2 :=
    (gl_U d E).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have hT1 := gl_ell _ _ _ _ ℓ hW1 hk2 hCk hUW hC
  have hTa := gl_ell _ _ _ _ (2 ^ ℓa) hW1 hk2 hCk hUW hCa.le
  obtain ⟨hma, hda, hd2⟩ := gl_ma d m _ _ _ (2 ^ ℓa) (by omega) hk2 (by omega) hCa
  have hKt := gl_pow _ 600 _ Ct kt (gl_W1 d m M.size n.size E)
  have hKC : Ct * 600 ^ kt * (d + m + M.size + n.size + E + 1) ^ (2 * kt) ≤
      (10 ^ 12 + Ct * 600 ^ kt + 2000) * (d + m + M.size + n.size + E + 1) ^ (2 * kt + 4) :=
    calc Ct * 600 ^ kt * (d + m + M.size + n.size + E + 1) ^ (2 * kt) ≤
          Ct * 600 ^ kt * (d + m + M.size + n.size + E + 1) ^ (2 * kt + 4) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hW1 (by omega))
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have hTt := (hKt.trans hKC).trans hC
  have hTta := lt_of_le_of_lt (hKt.trans hKC) hCa
  have hE4 := gl_ellE E _ _ _ ℓ (by omega) hCk (by omega) hC
  have hE4a := gl_ellE E _ _ _ (2 ^ ℓa) (by omega) hCk (by omega) hCa.le
  have hBw := gl_Bw (par d n).B (parG d n) d.size n.size (d + m + M.size + n.size + E + 1) hB hG (by omega)
  have hQ4 : 10 ^ 12 * (d + m + M.size + n.size + E + 1) ^ 4 ≤
      (10 ^ 12 + Ct * 600 ^ kt + 2000) * (d + m + M.size + n.size + E + 1) ^ (2 * kt + 4) :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hW1 (by omega))
  -- the modes
  rcases hmo : modeAt RoutinesQ d n m A b σs w.cs t with _ | _ | st
  · -- off
    rw [hmo] at hI
    have hstep : modeAt RoutinesQ d n m A b σs w.cs (t + 1) = .off := by rw [modeAt_succ, hmo]; rfl
    refine XV.mono (XV.roundOG hL hlay (X := ctxOf w n m A b) (cs := w.cs) rfl (xRunBL xtail L)
      (drawAt RoutinesQ d n w.cs t).1 hI (Or.inl rfl) hd1 (by rw [hpar]; omega) (by omega) (by rw [hpar]; omega)
      (by rw [hpar]; omega) hd2) ?_ fun σ' ⟨h1, h2⟩ => ⟨by rw [hstep]; exact h1, by rw [h2, play, hmo]⟩
    exact ((gl_ogt _ _ d _ hW1 (gl_og d _) hBw (by omega))).trans hQ4
  · -- guard
    rw [hmo] at hI
    have hstep : modeAt RoutinesQ d n m A b σs w.cs (t + 1) = .guard := by rw [modeAt_succ, hmo]; rfl
    refine XV.mono (XV.roundOG hL hlay (X := ctxOf w n m A b) (cs := w.cs) rfl (xRunBL xtail L)
      (drawAt RoutinesQ d n w.cs t).1 hI (Or.inr rfl) hd1 (by rw [hpar]; omega) (by omega) (by rw [hpar]; omega)
      (by rw [hpar]; omega) hd2) ?_ fun σ' ⟨h1, h2⟩ => ⟨by rw [hstep]; exact h1, by rw [h2, play, hmo]⟩
    exact ((gl_ogt _ _ d _ hW1 (gl_og d _) hBw (by omega))).trans hQ4
  -- run
  rw [hmo] at hI
  obtain ⟨st0, hst0⟩ := modeAt_run RoutinesQ n m A b σs w.cs t st hmo
  obtain ⟨heps, hβ, -⟩ := mode0_run hst0
  have heps' : (par d n).eps ≤ 1 / 2 := heps
  have he1 : (par d n).eps < 1 := by linarith
  have he0 := eps_nonneg (d := d) (n := n) hd1 hn1
  have hplay : play RoutinesQ d n m A b σs w.cs t =
      playPt (cfgOf RoutinesQ d n m A b w.cs) (.run st) (drawAt RoutinesQ d n w.cs t).1 := by rw [play, hmo]
  have hmem := play_mem (n := n) A b (RoutinesQ.ctr d n m A b) (RoutinesQ.pos d n m A b w.cs) st
    (drawAt RoutinesQ d n w.cs t).1 (hzero_of hin) heps' he0 hβ
  have hobs := obs_bnd hadm t ht (traj RoutinesQ d n m A b σs w.cs (t + 1)).2 _ hmem (par d n).p
  have hmodeS : modeAt RoutinesQ d n m A b σs w.cs (t + 1) =
      step RoutinesQ.ap (cfgOf RoutinesQ d n m A b w.cs) n (.run st) (drawAt RoutinesQ d n w.cs t).1
        (drawAt RoutinesQ d n w.cs t).2 ⌊(2 : ℝ) ^ (par d n).p * w.f t
          (BitRAM.toE (playPt (cfgOf RoutinesQ d n m A b w.cs) (.run st) (drawAt RoutinesQ d n w.cs t).1))⌋ := by
    rw [modeAt_succ, hmo, hloss, hplay]; rfl
  -- the bounds of R14's point
  have hfa := fld_abs (d := d) (n := n) hd1 hn1
  have hda' : (d : ℚ) ≤ 2 ^ (75 * parG d n + 343) := by
    have h1 : d ≤ 2 ^ (75 * parG d n + 343) := (d_le_G (n := n)).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact_mod_cast h1
  refine XV.mono (XV.roundRun (Q := RPost L n m (K0Q d n) E (cfgOf RoutinesQ d n m A b w.cs)
      (modeAt RoutinesQ d n m A b σs w.cs (t + 1)) (t + 1)
      (Function.update σ.pts t (BitRAM.toE (play RoutinesQ d n m A b σs w.cs t))))
    hL hlay (X := ctxOf w n m A b) (cs := w.cs) rfl (xRunBL xtail L) hI
    (by rw [hpar]; omega) (by omega) (by rw [hpar]; omega) (by rw [hpar]; omega) hd2
    (fun σ1 hP hr hdr hGam hZ hpts => XV.mono (XV.runBL hT hd1 hn1 hL hlay hblk hin.height
      (heightLE_succ hin.height) (by omega) hME hI hP hr hdr hGam hZ hβ he1 hEB hdE (by rw [hloss]; exact hobs) ?_
      hT1 hTa hda hma hTt hTta) le_rfl
      fun σ' ⟨h1, h2⟩ => ⟨by rw [hmodeS]; exact h1, by rw [h2, hpts, hplay]; rfl⟩))
    ?_ fun σ' h => h
  · -- the bounds of the next state and of R14's point
    intro mu'
    dsimp only
    intro hst
    have hrun := hmodeS.trans hst
    refine ⟨StBnd_mono (hM d n m M E0 A b hin σs hadm w.cs hpos (t + 1) _ (by omega) hrun) eM, ?_⟩
    intro x hx
    obtain ⟨hF, hWm⟩ := run_facts hst rfl
    have hf := f_abs _ _ _ _ _ hF hfa.2.2.2.2.2.2 (fun j => hb_wmu _ _ hWm j) (W_abs hd1 hn1) hda'
    have hexp : ellExp (clearQ (rcallL (cfgOf RoutinesQ d n m A b w.cs) st (drawAt RoutinesQ d n w.cs t).1
        (drawAt RoutinesQ d n w.cs t).2 ⌊(2 : ℝ) ^ (par d n).p * w.f t
          (BitRAM.toE (playPt (cfgOf RoutinesQ d n m A b w.cs) (.run st) (drawAt RoutinesQ d n w.cs t).1))⌋ n)) ≤
        Cx * (d + n.size + (5 * (75 * parG d n + 343) + 5) + 1) ^ kx :=
      hX d n m _ A b _ _ _ _ _ _ _ _ _ hd1 hn1 (fun i j => onG_rnd_s _ _) hF hf
      (by unfold callRE; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)))
    have hexpE : ellExp (clearQ (rcallL (cfgOf RoutinesQ d n m A b w.cs) st (drawAt RoutinesQ d n w.cs t).1
        (drawAt RoutinesQ d n w.cs t).2 ⌊(2 : ℝ) ^ (par d n).p * w.f t
          (BitRAM.toE (playPt (cfgOf RoutinesQ d n m A b w.cs) (.run st) (drawAt RoutinesQ d n w.cs t).1))⌋ n)) ≤
        Cx * ((d + m + M.size + n.size + E0 + 1) + (5 * (75 * parG d n + 343) + 5)) ^ kx :=
      hexp.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hW0e _) _))
    have hle : 75 * parG d n + 343 + ellExp (clearQ (rcallL (cfgOf RoutinesQ d n m A b w.cs) st
        (drawAt RoutinesQ d n w.cs t).1 (drawAt RoutinesQ d n w.cs t).2 ⌊(2 : ℝ) ^ (par d n).p * w.f t
          (BitRAM.toE (playPt (cfgOf RoutinesQ d n m A b w.cs) (.run st) (drawAt RoutinesQ d n w.cs t).1))⌋ n)) ≤ E :=
      (Nat.add_le_add_left hexpE _).trans eX
    exact ⟨fun j => (x_abs _ x hx (a := 75 * parG d n + 343) hfa.2.2.2.2.2.1 j).trans
      (pow_le_pow_right₀ (by norm_num) hle), hexpE.trans ((Nat.le_add_left _ _).trans eX)⟩
  · -- the units
    have h1 := gl_tot (d + m + M.size + n.size + E + 1) (par d n).B d m (tG d E + E + 1)
      (Ct * (d + m + M.size + n.size + (36 * (tG d E + E + 1) + 30) + 1) ^ kt) (r1Units d (par d n).B)
      (r24Units d m) (r57Units d (tG d E + E + 1)) (midUnits d (tG d E + E + 1)) hW1 (gl_r1 d _) hBw (by omega)
      (units_r24 d m) (units_r57 d _) (units_mid d _) hUW
    have h2 := gl_C (d + m + M.size + n.size + E + 1) Ct kt hW1
    show r1Units d (par d n).B + (1 + (runUnits d m (tG d E + E + 1)
      (Ct * (d + m + M.size + n.size + (36 * (tG d E + E + 1) + 30) + 1) ^ kt) + 2)) ≤ _
    unfold runUnits
    calc _ ≤ _ := h1
      _ ≤ 10 ^ 12 * (d + m + M.size + n.size + E + 1) ^ 4 +
          Ct * 600 ^ kt * (d + m + M.size + n.size + E + 1) ^ (2 * kt) := Nat.add_le_add_left hKt _
      _ ≤ _ := h2
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

end AdversarialBco.Bit.Transfer.BLM
