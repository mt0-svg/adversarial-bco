/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSetupInv
public import AdversarialBco.Bit.Transfer.XBLSetupEpoch
public import AdversarialBco.Bit.Transfer.XBLSplit

@[expose] public section

/-!
# BL's setup on the machine

`xsetupBL L xframe xtri`: the machine's setup (`xsetup`, `d` in `rD`), then P0, PARAM and its copies, `sZ := 0`, the
calls of FRAME and TRI, P3's loop over the input rows, the epoch start and P5's mode. `XV.initBL`: from the
environment after the machine's setup, it ends in `BLInv` at round `0` with the mode `mode0` and no point played,
within `initUnits` units.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-- BL's setup after the machine's. -/
def xinitBL (L : Layout) (xframe xtri : Layout → PrBlk → XCmd) : XCmd :=
  .seq (xprm L) (.seq (toX (VL.sconst L sZ 0)) (.seq (xcalls L xframe xtri) (.seq (xS3 L)
    (.seq (xepoch L) (xmode L)))))

/-- **BL's setup.** -/
def xsetupBL (L : Layout) (xframe xtri : Layout → PrBlk → XCmd) : XCmd :=
  .seq (xsetup L rD) (xinitBL L xframe xtri)

/-- The units of `xinitBL`. -/
def initUnits (d n m sf st : ℕ) : ℕ :=
  (696 * parG d n + 3222) + (1 + (callUnits d sf st + (s3Units d m + (epochUnits d + 6))))

/-- The cells changed after the calls. -/
def Sx (y : ℕ) : Prop := S3 y ∨ SE y ∨ y = sMode ∨ y = 124
def Nx (j : ℕ) : Prop := N3 j ∨ NE j
def Ax (a c : ℕ) : Prop := A3 a c ∨ AE (d := d) a c

/-- `omega` after unfolding the frames of the setup and the cell names. -/
macro "fomega" : tactic => `(tactic| ((try simp only [SC, NC, AC, Sx, Nx, Ax, S3, N3, A3, SE, NE, AE, rD, rM, rMk,
  rOne, rP, rPF, rNb, rB, sZ, sMode, sFirst, sN, s2p, s2pF, s2g, sNe, sLam, sRint, s2eh, sEps, sLamb, sEta, sRho,
  sKapc, sNu, sR, sSb, sW, sA0, sB0, sDS, sDmu, sK, sL, sBadS, sGN, sRQ, tR, rD1, rk, aMuS, aAS, aC, aMu,
  aA, aB, ab, aG, aRw, ne_eq, not_or, not_and, not_exists, not_lt, not_le]) <;> omega))

/-- The position that TRI leaves (`PosIn`, integers below `2^s`) is bounded by `2^s` (`PosBnd`). -/
theorem posBnd_of_posIn {σ : Env d} {o a s n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {c : Fin d → ℚ}
    {S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ} (h : PosIn σ o a s S) : PosBnd (mkCfg d n m A b c S) s := by
  obtain ⟨D, hD0, hDs, -, hmu, hA⟩ := h
  refine ⟨D, hD0, hDs.le, fun j => ?_, fun i j => ?_⟩
  · obtain ⟨x, hx, -, e⟩ := hmu j
    exact ⟨x, hx.le, e⟩
  · obtain ⟨x, hx, -, e⟩ := hA i j
    exact ⟨x, hx.le, e⟩

set_option maxHeartbeats 8000000 in
/-- **BL's setup after the machine's, on the machine.** -/
theorem XV.initBL {L : Layout} {w : BitRAM.World d} {n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    {ℓa ℓ E : ℕ} {xframe xtri : Layout → PrBlk → XCmd} {Cf kf nSf nNf nAf Ct kt nSt nNt nAt : ℕ}
    (hF : FrameSpec xframe Cf kf nSf nNf nAf) (hT : TriSpec xtri Ct kt nSt nNt nAt) (hL : LayOK L d ℓa)
    (hlay : BLLay L) (hOKf : blkS.OK L nSf nNf nAf) (hOKt : blkS.OK L nSt nNt nAt)
    (hd : 1 ≤ d) (hn : 1 ≤ n) (hH : RealRAM.HeightLE A b M) (hM1 : 1 ≤ M)
    (hEG : 75 * parG d n + 343 ≤ E) (hEf : sF Cf kf d m A b ≤ E)
    (hEt : sT Ct kt d n m (sF Cf kf d m A b) A b ≤ E) (hME : M ≤ 2 ^ E) (hmE : m ≤ 2 ^ E)
    (hℓ : 3 * (E * d) + 10 * E + 5 ≤ ℓ) (hℓa : E + 2 * ((d + 1) * m) + 4 < 2 ^ ℓa) :
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xinitBL L xframe xtri) (envSetup rD d)
      (initUnits d n m (sF Cf kf d m A b) (sT Ct kt d n m (sF Cf kf d m A b) A b)) (fun σ =>
        (BLInv L n m (K0Q d n) E (cfgOf RoutinesQ d n m A b w.cs) (mode0 (cfgOf RoutinesQ d n m A b w.cs)) 0 σ ∧
          σ.pts = fun _ => 0) ∧ PosBnd (cfgOf RoutinesQ d n m A b w.cs) (sT Ct kt d n m (sF Cf kf d m A b) A b)) := by
  obtain ⟨hS, hN, hA⟩ := id hlay
  simp only [oE, rEE, aWE] at hS hN hA
  set sf := sF Cf kf d m A b with hsf
  set st := sT Ct kt d n m sf A b with hst
  have hdG : d ≤ 2 ^ parG d n := d_le_G
  have hGE : 2 ^ parG d n ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hEl : 2 ^ E < 2 ^ ℓ := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hE2 : E < 2 ^ E := Nat.lt_two_pow_self
  have hmd : m ≤ (d + 1) * m := Nat.le_mul_of_pos_left m (by omega)
  have hoff : 3 + 2 * ((d + 1) * m) ≤ (ctxOf w n m A b).off := by
    show _ ≤ offOf d m
    unfold offOf; rw [mul_assoc]
  have hGEz : (2 : ℤ) ^ (75 * parG d n + 343) ≤ 2 ^ E := pow_le_pow_right₀ (by norm_num) hEG
  have htE : (2 : ℤ) ^ st ≤ 2 ^ E := pow_le_pow_right₀ (by norm_num) hEt
  have hElz : (2 : ℤ) ^ (E + 1) < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) (by omega)
  have pvE : ∀ k < 93, |pv d n k| ≤ 2 ^ E := fun k hk => (pv_abs hd hn hk).trans hGEz
  -- P0, PARAM, the copies
  refine XV.seq (XV.prm hL (by omega) (by omega) (by omega) hd hn (by omega) (by omega) (by omega) (by omega))
    fun σ1 h1 => ?_
  have c1 : ∀ y k, (y, k) ∈ prmCopies → σ1.sc y = pv d n (k - 30) := fun y k h => h1.cp _ h
  -- `sZ := 0`
  refine XV.seq (XV.sconst hL (x := sZ) (by fomega) 0 rfl (by rw [Rat.cast_zero, abs_zero]; positivity))
    fun σ2 e2 => ?_
  subst e2
  have z2 : (σ1.setSc sZ ((0 : ℚ) : ℝ)).sc sZ = 0 := by simp
  have n2 : (σ1.setSc sZ ((0 : ℚ) : ℝ)).sc sN = n := by
    rw [Env.setSc_sc, if_neg (by decide)]; exact h1.sc.2.2.2.1
  -- FRAME and TRI
  refine XV.seq (XV.calls hF hT hL hOKf hOKt (by omega) (by omega) hd hn (by omega) (by omega)
    (hEt.trans_lt (by omega))
    (hEt.trans_lt (by omega)) h1.nat.1 h1.nat.2.1 h1.nat.2.2.2.1 z2 n2) fun σ3 ⟨hPt, hPos, d3, F3⟩ => ?_
  have ecs : (fun j => w.cs ((σ1.setSc sZ ((0 : ℚ) : ℝ)).draws + j)) = w.cs := by
    funext j; rw [Env.setSc_draws, h1.draws, zero_add]
  rw [ecs] at hPos
  have hPB : PosBnd (cfgOf RoutinesQ d n m A b w.cs) st := posBnd_of_posIn hPos
  obtain ⟨D, xm, xa, hD0, hDs, hsc3, hxm3, hxa3, hS1, hS2⟩ :=
    posIn_fun (σ3.sc sDS) (σ3.arr aMuS) (σ3.arr (aMuS + 1)) st _ hPos
  obtain ⟨xc, hxc3, hc0, hc⟩ := ptIn_fun (σ3.arr aC) sf _ hPt
  have hD3 : σ3.nat rD = d := (F3.1 rD (by fomega)).trans h1.nat.1
  have hM3 : σ3.nat rM = m := (F3.1 rM (by fomega)).trans h1.nat.2.1
  have h13 : σ3.nat rOne = 1 := (F3.1 rOne (by fomega)).trans h1.nat.2.2.2.1
  have hz3 : σ3.sc sZ = 0 := (F3.2.1 sZ (by fomega)).trans z2
  have hk03 : σ3.nat rMk = 0 := (F3.1 rMk (by fomega)).trans h1.nat.2.2.1
  have hb03 : σ3.sc sBadS = 0 := by
    rw [F3.2.1 sBadS (by fomega), Env.setSc_sc, if_neg (by decide)]
    exact h1.sc.2.2.2.2.2.2.2.2
  have hinp := inp_bnd (n := n) A b hH
  have bDS : D ≤ 2 ^ E := hDs.le.trans htE
  have bmu : ∀ k : Fin d, |xm k| ≤ 2 ^ E := fun k => (hxm3 k k.2).2.le.trans htE
  -- P3
  refine XV.seq (XV.s3 (Nm := NmI d n m A b) (Dn := DnI d n m A b) (Mh := (M : ℤ)) (DS := D)
    (muS := fun k : Fin d => xm k) (E := E) hL hlay hD3 hM3 h13 hz3 hsc3 (fun k => (hxm3 k k.2).1) hk03 hb03 hoff
    (by omega) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (by exact_mod_cast hM1) hinp.1 hinp.2
    (by exact_mod_cast hME) (by omega) bDS bmu (by omega) hℓ) fun σ4 ⟨hk4, hfl4, d4, F4⟩ => ?_
  obtain ⟨fl, hfl4', hflb, hfl⟩ : ∃ fl : ℤ, σ4.sc sBadS = fl ∧ |fl| ≤ 1 ∧
      (0 < fl ↔ s3bad (NmI d n m A b) (DnI d n m A b) (fun k : Fin d => xm k) D m) := by
    rcases hfl4 with ⟨e, hb⟩ | ⟨e, hb⟩
    · exact ⟨1, by rw [e]; simp, by norm_num, by simp [hb]⟩
    · exact ⟨0, by rw [e]; simp, by norm_num, by simp [hb]⟩
  have hD4 : σ4.nat rD = d := (F4.1 rD (by fomega)).trans hD3
  have h14 : σ4.nat rOne = 1 := (F4.1 rOne (by fomega)).trans h13
  have hz4 : σ4.sc sZ = 0 := (F4.2.1 sZ (by fomega)).trans hz3
  have s41 : ∀ y, 4 ≤ y → y ≤ 21 → σ4.sc y = σ1.sc y := fun y h h' => by
    rw [F4.2.1 y (by fomega), F3.2.1 y (by fomega), Env.setSc_sc, if_neg (by fomega)]
  have hA04 : σ4.sc sA0 = ((A0Z d n : ℤ) : ℝ) := by
    rw [s41 _ (by decide) (by decide), c1 _ 119 (by decide), show 119 - 30 = 89 from rfl, pv_89 hd hn]
  have hB04 : σ4.sc sB0 = ((B0Z d n : ℤ) : ℝ) := by
    rw [s41 _ (by decide) (by decide), c1 _ 120 (by decide), show 120 - 30 = 90 from rfl, pv_90 hd hn]
  have ba : |A0Z d n| ≤ 2 ^ E := by rw [← pv_89 hd hn]; exact pvE 89 (by norm_num)
  have bb : |B0Z d n| ≤ 2 ^ E := by rw [← pv_90 hd hn]; exact pvE 90 (by norm_num)
  -- the epoch start
  refine XV.seq (XV.epoch hL (by omega) (by omega) (by omega) (E := E) hD4 h14 hz4 hA04 hB04 ba bb (by omega))
    fun σ5 ⟨hF5, hDm5, hA5, hB5, d5, F5⟩ => ?_
  have hz5 : σ5.sc sZ = 0 := (F5.2.1 sZ (by fomega)).trans hz4
  have hfl5 : σ5.sc sBadS = fl := (F5.2.1 sBadS (by fomega)).trans hfl4'
  have hPF5 : σ5.sc s2pF = ((PFZ d n : ℤ) : ℝ) := by
    rw [F5.2.1 s2pF (by fomega), s41 _ (by decide) (by decide), c1 _ 66 (by decide), show 66 - 30 = 36 from rfl,
      pv_36z]
  have hep5 : σ5.sc sEps = ((epsZ d n : ℤ) : ℝ) := by
    rw [F5.2.1 sEps (by fomega), s41 _ (by decide) (by decide), c1 _ 99 (by decide), show 99 - 30 = 69 from rfl,
      pv_69 hd hn]
  have hm5 : σ5.sc sMode = 0 := by
    rw [F5.2.1 sMode (by fomega), F4.2.1 sMode (by fomega), F3.2.1 sMode (by fomega), Env.setSc_sc,
      if_neg (by decide)]
    exact h1.sc.2.1
  have bfl : |fl| < 2 ^ ℓ := hflb.trans_lt (one_lt_pow₀ (by norm_num) (by omega))
  have bPF : |PFZ d n| < 2 ^ ℓ := by
    rw [← pv_36z]
    exact (pvE 36 (by norm_num)).trans_lt ((pow_le_pow_right₀ (by norm_num) (by omega)).trans_lt hElz)
  have bep : |2 * epsZ d n| < 2 ^ ℓ := by
    have h := pvE 69 (by norm_num)
    rw [pv_69 hd hn] at h
    rw [abs_mul, abs_two]
    have e : (2 : ℤ) * 2 ^ E = 2 ^ (E + 1) := by ring
    linarith
  -- P5
  refine XV.mono (XV.mode hL (by omega) hz5 hfl5 hPF5 hep5 hm5 bfl bPF bep (by omega)) le_rfl
    fun σ6 ⟨hm6, d6, F6⟩ => ?_
  have G36 : FrameA Sx Nx (Ax (d := d)) σ3 σ6 :=
    ((F4.mono (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ _ h => Or.inl h)).trans
      (F5.mono (fun _ h => Or.inr (Or.inl h)) (fun _ h => Or.inr h) (fun _ _ h => Or.inr h))).trans
      (F6.mono (fun _ h => Or.inr (Or.inr h)) (fun _ h => h.elim) (fun _ _ h => h.elim))
  have n61 : ∀ j, ¬ NC j → ¬ Nx j → σ6.nat j = σ1.nat j := fun j h h' => (G36.1 j h').trans (F3.1 j h)
  have s61 : ∀ y, y ≠ sZ → ¬ SC y → ¬ Sx y → σ6.sc y = σ1.sc y := fun y h0 h h' => by
    rw [G36.2.1 y h', F3.2.1 y h, Env.setSc_sc, if_neg h0]
  have a61 : ∀ a c, ¬ AC (d := d) a c → ¬ Ax (d := d) a c → σ6.arr a c = 0 := fun a c h h' => by
    rw [G36.2.2.1 a c h', F3.2.2.1 a c h, Env.setSc_arr]; exact h1.arr a c
  have a65 : ∀ a c, σ6.arr a c = σ5.arr a c := fun a c => F6.2.2.1 a c id
  have s65 : ∀ y, y ≠ sMode → y ≠ 124 → σ6.sc y = σ5.sc y := fun y h h' => F6.2.1 y (not_or.2 ⟨h, h'⟩)
  have hk6 : σ6.nat rMk = keptCnt A m := by
    rw [F6.1 rMk id, F5.1 rMk (by fomega), hk4, s3cnt_eq A b m le_rfl]
  refine ⟨⟨blinv_mk (cs := w.cs) (D := D) (fl := fl) (xm := xm) (xa := xa) (xc := xc) (sf := sf) (st := st) hd hn
    hlay hEG hEf hEt ((n61 rD (by fomega) (by fomega)).trans h1.nat.1)
    ((n61 rM (by fomega) (by fomega)).trans h1.nat.2.1) hk6
    ((n61 rOne (by fomega) (by fomega)).trans h1.nat.2.2.2.1)
    ((n61 rP (by fomega) (by fomega)).trans h1.nat.2.2.2.2.1)
    ((n61 rPF (by fomega) (by fomega)).trans h1.nat.2.2.2.2.2.1)
    ((n61 rNb (by fomega) (by fomega)).trans h1.nat.2.2.2.2.2.2.1)
    ((n61 rB (by fomega) (by fomega)).trans h1.nat.2.2.2.2.2.2.2)
    ((G36.2.1 sZ (by fomega)).trans hz3)
    ((s61 sN (by decide) (by fomega) (by fomega)).trans h1.sc.2.2.2.1)
    (fun p hp => ?_)
    ((s65 sFirst (by decide) (by decide)).trans hF5) ((s65 sDmu (by decide) (by decide)).trans hDm5)
    ((s61 sK (by decide) (by fomega) (by fomega)).trans h1.sc.2.2.2.2.2.2.1)
    ((s61 sL (by decide) (by fomega) (by fomega)).trans h1.sc.2.2.2.2.2.2.2.1)
    ((G36.2.1 sDS (by fomega)).trans hsc3) hm6 hfl
    (fun k => ?_) (fun k => ?_) (fun k => ?_)
    (fun k => a61 _ k (by fomega) (by fomega)) (fun k => a61 _ k (by fomega) (by fomega))
    (fun k => a61 _ k (by fomega) (by fomega))
    (fun k => ?_) (fun k => ?_)
    hD0 hDs (fun k hk => (hxm3 k hk).2) (fun k hk => (hxa3 k hk).2) (fun k hk => (hxc3 k hk).2) hc0 hS1 hS2 hc
    (G36.2.2.2.1.trans (F3.2.2.2.1.trans h1.rounds)) (by rw [d6, d5, d4, d3, Env.setSc_draws, h1.draws, zero_add]),
    G36.2.2.2.2.trans (F3.2.2.2.2.trans h1.pts)⟩, hPB⟩
  · obtain ⟨q1, q2⟩ := prmCopies_ok.2.2.2 p hp
    exact (s61 p.1 (by fomega) (by fomega) (by fomega)).trans (h1.cp p hp)
  · split_ifs with hk
    · rw [G36.2.2.1 _ k (by fomega)]; exact (hxm3 k hk).1
    · exact a61 _ k (by fomega) (by fomega)
  · split_ifs with hk
    · rw [G36.2.2.1 _ k (by fomega)]; exact (hxa3 k hk).1
    · exact a61 _ k (by fomega) (by fomega)
  · split_ifs with hk
    · rw [G36.2.2.1 _ k (by fomega)]; exact (hxc3 k hk).1
    · exact a61 _ k (by fomega) (by fomega)
  · split_ifs with hk
    · obtain ⟨j, hj, rfl⟩ := hk
      rw [a65]; exact hA5 j hj
    · exact a61 _ k (by fomega) (fun h => h.elim (fun h' => by simp [A3] at h') (fun h' => hk h'.2))
  · split_ifs with hk
    · obtain ⟨j, hj, rfl⟩ := hk
      rw [a65]; exact hB5 j hj
    · exact a61 _ k (by fomega) (fun h => h.elim (fun h' => by simp [A3] at h') (fun h' => hk h'.2))

end AdversarialBco.Bit.Transfer.BLM
