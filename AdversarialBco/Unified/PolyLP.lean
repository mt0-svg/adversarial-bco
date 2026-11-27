/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XDriver
public import AdversarialBco.Bit.Transfer.XFrameRule
public import AdversarialBco.Bit.Transfer.XBLSetupCall
public import AdversarialBco.Bit.Transfer.XBLSetupPrm
public import AdversarialBco.Bit.Transfer.XBLSetupFacts
public import AdversarialBco.Bit.ApQ.FrameB

@[expose] public section

/-!
# UNI-POLY: the frame centre on the bit machine (`lp_run`)

`LP`: the machine's setup in the layout `LPL` (`d` in `rD`), `m` (input cell `2`) into `rM`, then the frame centre
`xframe LPL blkS`. `lp_run`: from the initial state of the bit machine, the prologue and the code of `LP` run to a
state holding `frameQ d n m A b` in the array `16` (denominator `D` in cell `0`, numerators `x j` in cells `1 + j`,
all below `2^s`), the array `aY = 1` zero, the registers of the two arrays at their bases, the input and the offset in
place, no coin read, no round played, every register above `rg 496` zero; within `CpL` units of cost.

`regMax c` bounds the natural registers the command `c` writes (`regMax_sound`); it gives the clause on the cells
below `-500`. Polynomial bound: `CpL_le`.
-/

namespace AdversarialBco.UniPoly

open BitRAM
open Bit.Transfer
open Bit.RQ (frMhat frameQ)
open Poly.Mach (Layout asz Env Rep Prim)

variable {d : ℕ}

/-! ## The registers a command writes -/

/-- One more than the natural register a leaf writes (`0`: none). -/
def leafReg : Leaf → ℕ
  | .rtoN dst _ => dst + 1
  | .nmul dst _ _ => dst + 1
  | _ => 0

/-- One more than the natural register a fragment primitive writes (`0`: none). -/
def primReg : Prim → ℕ
  | .nconst dst _ => dst + 1
  | .nadd dst _ _ => dst + 1
  | .nsub dst _ _ => dst + 1
  | _ => 0

/-- A bound on the natural registers a command writes: it writes none at or above `regMax c`. -/
def regMax : XCmd → ℕ
  | .skip => 0
  | .prim (.frag p) => primReg p
  | .prim (.leaf l) => leafReg l
  | .seq c₁ c₂ => max (regMax c₁) (regMax c₂)
  | .ifR _ _ c₁ c₂ => max (regMax c₁) (regMax c₂)
  | .ifN _ _ c₁ c₂ => max (regMax c₁) (regMax c₂)
  | .whileR _ _ c => regMax c
  | .whileN _ _ c => regMax c

theorem primReg_sound (w : RealRAM.World d) (s : RealRAM.State d) (p : Prim) (i : ℕ) (hi : primReg p ≤ i) :
    (p.exec w s).nreg i = s.nreg i := by
  cases p <;> simp only [primReg] at hi <;> first | rfl | exact Function.update_of_ne (by omega) _ _

theorem leafReg_sound (X : XCtx d) (s : RealRAM.State d) (l : Leaf) (i : ℕ) (hi : leafReg l ≤ i) :
    (l.exec X s).nreg i = s.nreg i := by
  cases l <;> simp only [leafReg] at hi <;> first | rfl | exact Function.update_of_ne (by omega) _ _

/-- A run of `c` keeps every natural register at or above `regMax c`. -/
theorem regMax_sound {X : XCtx d} {ℓa ℓ : ℕ} {c : XCmd} {s s' : RealRAM.State d} {k : ℕ}
    (h : XExecB X ℓa ℓ c s k s') : ∀ i, regMax c ≤ i → s'.nreg i = s.nreg i := by
  induction h with
  | skip => exact fun _ _ => rfl
  | frag p s _ => exact fun i hi => primReg_sound _ s p i hi
  | leaf l s _ => exact fun i hi => leafReg_sound _ s l i hi
  | seq _ _ ih₁ ih₂ =>
    intro i hi
    simp only [regMax] at hi
    rw [ih₂ i (by omega), ih₁ i (by omega)]
  | ifR_t _ _ _ ih => intro i hi; simp only [regMax] at hi; exact ih i (by omega)
  | ifR_f _ _ _ ih => intro i hi; simp only [regMax] at hi; exact ih i (by omega)
  | ifN_t _ _ _ ih => intro i hi; simp only [regMax] at hi; exact ih i (by omega)
  | ifN_f _ _ _ ih => intro i hi; simp only [regMax] at hi; exact ih i (by omega)
  | whileR_t _ _ _ _ ih₁ ih₂ => intro i hi; rw [ih₂ i hi, ih₁ i hi]
  | whileR_f _ _ => exact fun _ _ => rfl
  | whileN_t _ _ _ _ ih₁ ih₂ => intro i hi; rw [ih₂ i hi, ih₁ i hi]
  | whileN_f _ _ => exact fun _ _ => rfl

/-! ## The frame centre as a `FrameSpec` -/

/-- `frameRule` for the command `xframe` itself. -/
theorem frameSpec_xframe : BLM.FrameSpec xframe (10 ^ 8) 11 135 51 8 := by
  intro d L w n m A b ℓa ℓ B σ hd hL hB e_d e_m hℓ hℓa
  have hW1 : 1 ≤ d + m + (frMhat A b).size + 1 := by omega
  have h9 : (d + m + (frMhat A b).size + 1) ^ 9 ≤ (d + m + (frMhat A b).size + 1) ^ 11 :=
    Nat.pow_le_pow_right hW1 (by norm_num)
  have h2 : (d + m + (frMhat A b).size + 1) ^ 2 ≤ (d + m + (frMhat A b).size + 1) ^ 11 :=
    Nat.pow_le_pow_right hW1 (by norm_num)
  have h0 : 1 ≤ (d + m + (frMhat A b).size + 1) ^ 11 := Nat.one_le_pow _ _ hW1
  have hE := frEx_lt_C d m (frMhat A b)
  have hR := frRegB_le_W d m (frMhat A b)
  have hU := frBrU_le_W d m (frMhat A b) hd
  have h1U := frame1U_le_W d m (frMhat A b)
  have hb := frame1_hb d m (frMhat A b)
  exact XV.mono (XV.frame hL (s := 10 ^ 8 * (d + m + (frMhat A b).size + 1) ^ 11) hd hB e_d e_m (by omega)
    (by omega) (by omega) (hb.trans_le (pow_le_pow_right₀ (by norm_num) hℓ)) hb) (by omega) (fun _ h => h)

/-! ## The program -/

/-- The layout: `100` natural registers, `263` slots, `24` arrays. -/
def LPL : Layout := ⟨100, 263, 24⟩

/-- The array left zero for the caller. -/
def aY : ℕ := 1

/-- `m` (input cell `2`) into `rM`, through the slot `1`. -/
def xmIn : XCmd :=
  .seq (.prim (.frag (.nconst BLM.rM 2))) (.seq (xrdIn LPL 1 BLM.rM) (xrtoN LPL BLM.rM 1))

/-- The setup, `m` into `rM`, the frame centre into the array `16`. -/
def LP : XCmd := .seq (xsetup LPL BLM.rD) (.seq xmIn (xframe LPL BLM.blkS))

/-- The bit size of the integers of the frame centre. -/
def Spl (d m M : ℕ) : ℕ := 10 ^ 8 * (d + m + M.size + 1) ^ 11

/-- The register and value width of the run. -/
def lpL (d m M : ℕ) : ℕ := Spl d m M + offOf d m + 24 * asz d + 400

/-- The cost of the prologue and of `LP`. -/
def CpL (d _n m M : ℕ) : ℕ := (322 + Spl d m M) * xstepCost (lpL d m M) (lpL d m M)

theorem regMax_xsetRS (L : Layout) (k : ℕ) : regMax (xsetRS L k) ≤ L.NN + 4 + k := by
  induction k with
  | zero => simp only [xsetRS, regMax]; omega
  | succ k ih => simp only [xsetRS, regMax, primReg, Poly.Mach.Layout.rS]; omega

theorem regMax_xsetRA (L : Layout) (k : ℕ) : regMax (xsetRA L k) ≤ L.NN + 4 + L.NS + k := by
  induction k with
  | zero => simp only [xsetRA, regMax]; omega
  | succ k ih => simp only [xsetRA, regMax, primReg, Poly.Mach.Layout.rA, Poly.Mach.Layout.rT]; omega

theorem regMax_xsetup (L : Layout) (dv : ℕ) :
    regMax (xsetup L dv) ≤ max (dv + 1) (L.NN + 4 + L.NS + L.NA) := by
  have h1 := regMax_xsetRS L L.NS
  have h2 := regMax_xsetRA L L.NA
  simp only [xsetup, regMax, primReg, leafReg, Poly.Mach.Layout.rZ, Poly.Mach.Layout.rSZ, Poly.Mach.Layout.rT]
  omega

set_option maxRecDepth 100000 in
theorem regMax_xframe : regMax (xframe LPL BLM.blkS) ≤ 400 := by decide +kernel

theorem regMax_LP : regMax LP ≤ 400 := by
  have h1 := regMax_xsetup LPL BLM.rD
  have h4 : max (BLM.rD + 1) (LPL.NN + 4 + LPL.NS + LPL.NA) = 391 := rfl
  rw [h4] at h1
  have h2 := regMax_xframe
  have h3 : regMax xmIn = 2 := rfl
  show max (regMax (xsetup LPL BLM.rD)) (max (regMax xmIn) (regMax (xframe LPL BLM.blkS))) ≤ 400
  omega

/-! ## Polynomial bounds -/

theorem xstepCost_sq {L : ℕ} (h : 1 ≤ L) : xstepCost L L ≤ 65 * L ^ 2 := by
  unfold xstepCost; nlinarith

theorem CpL_le (d n m M : ℕ) : CpL d n m M ≤ 10 ^ 27 * (d + m + n.size + M.size + 1) ^ 33 := by
  have hWV : d + m + M.size + 1 ≤ d + m + n.size + M.size + 1 := by omega
  have hV : (d + m + M.size + 1) ^ 33 ≤ (d + m + n.size + M.size + 1) ^ 33 := Nat.pow_le_pow_left hWV 33
  have hW1 : 1 ≤ d + m + M.size + 1 := by omega
  have hY1 : 1 ≤ (d + m + M.size + 1) ^ 11 := Nat.one_le_pow _ _ hW1
  have hY2 : (d + m + M.size + 1) ^ 2 ≤ (d + m + M.size + 1) ^ 11 := Nat.pow_le_pow_right hW1 (by norm_num)
  have hdm : (d + 1) * m ≤ (d + m + M.size + 1) ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have hdd : asz d ≤ 2 * (d + m + M.size + 1) ^ 2 := by
    unfold asz; rw [sq]
    have : d * d ≤ (d + m + M.size + 1) * (d + m + M.size + 1) := Nat.mul_le_mul (by omega) (by omega)
    have : d ≤ (d + m + M.size + 1) * (d + m + M.size + 1) := le_trans (by omega) (Nat.le_mul_self _)
    omega
  have hoff : offOf d m ≤ 5 * (d + m + M.size + 1) ^ 2 := by
    unfold offOf; rw [Nat.mul_assoc]
    have : 1 ≤ (d + m + M.size + 1) ^ 2 := Nat.one_le_pow _ _ hW1
    omega
  have e33 : ((d + m + M.size + 1) ^ 11) ^ 3 = (d + m + M.size + 1) ^ 33 := by rw [← pow_mul]
  unfold CpL lpL Spl
  generalize (d + m + M.size + 1) ^ 11 = Y at hY1 hY2 e33 ⊢
  generalize (d + m + M.size + 1) ^ 2 = Z at hY2 hdm hdd hoff
  rw [← e33] at hV
  generalize hc : (10 : ℕ) ^ 8 = c
  have hc1 : 1 ≤ c := by rw [← hc]; exact Nat.one_le_pow _ _ (by norm_num)
  have hL : c * Y + offOf d m + 24 * asz d + 400 ≤ 2 * c * Y := by
    have : 453 * Y ≤ c * Y := Nat.mul_le_mul_right Y (by rw [← hc]; norm_num)
    have : 2 * c * Y = c * Y + c * Y := by ring
    omega
  have hS : 322 + c * Y ≤ 2 * c * Y := by
    have : 322 * Y ≤ c * Y := Nat.mul_le_mul_right Y (by rw [← hc]; norm_num)
    have : 2 * c * Y = c * Y + c * Y := by ring
    omega
  generalize hLd : c * Y + offOf d m + 24 * asz d + 400 = L at hL ⊢
  have hL1 : 1 ≤ L := by
    have : 1 ≤ c * Y := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    omega
  have hx := xstepCost_sq hL1
  have hL2 : L ^ 2 ≤ (2 * c * Y) ^ 2 := Nat.pow_le_pow_left hL 2
  calc (322 + c * Y) * xstepCost L L ≤ (2 * c * Y) * (65 * (2 * c * Y) ^ 2) :=
        Nat.mul_le_mul hS (hx.trans (Nat.mul_le_mul_left 65 hL2))
    _ = 520 * c ^ 3 * Y ^ 3 := by ring
    _ ≤ 10 ^ 27 * Y ^ 3 := Nat.mul_le_mul_right _ (by rw [← hc]; norm_num)
    _ ≤ 10 ^ 27 * (d + m + n.size + M.size + 1) ^ 33 := Nat.mul_le_mul_left _ hV

/-! ## The run -/

/-- The input cell `c`, read through the simulation. -/
theorem xsim_cell {w : World d} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    {s : RealRAM.State d} {t : State d} (hs : XSim (ctxOf w n m A b) s t) (j : ℕ) :
    (t.mem ((offOf d m : ℤ) + j) : ℝ) = s.mem j := by
  rw [add_comm]; exact hs.mem j

/-- The state after `LP`. -/
def LPInv (d n m s : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Env d) : Prop :=
  PtIn σ 16 s (frameQ d n m A b) ∧ (∀ k, σ.arr aY k = 0) ∧ σ.draws = 0 ∧ σ.rounds = 0 ∧ σ.pts = fun _ => 0

set_option maxHeartbeats 4000000 in
/-- `m` into `rM`, then the frame centre, from the environment after the setup. -/
theorem XV.lpInit {w : World d} {n m M ℓ : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} (hd : 1 ≤ d)
    (hMh : frMhat A b ≤ M) (hL : LayOK LPL d ℓ) (hS : Spl d m M ≤ ℓ) (hℓ : ℓ < 2 ^ ℓ) (hmℓ : m < ℓ)
    (h3 : 3 ≤ ℓ) :
    XRunsB LPL (ctxOf w n m A b) ℓ ℓ (.seq xmIn (xframe LPL BLM.blkS)) (envSetup BLM.rD d) (3 + Spl d m M)
      (LPInv d n m (10 ^ 8 * (d + m + (frMhat A b).size + 1) ^ 11) A b) := by
  have j2 : (ctxOf w n m A b).inp 2 = m := (BitRAM.Conj1BitSanity.inputMem_small (n := n) A b).2.2
  have hoff : 2 < (ctxOf w n m A b).off := by show 2 < offOf d m; unfold offOf; omega
  have h2 : 2 < 2 ^ ℓ := by omega
  have hm2 : m < 2 ^ ℓ := by omega
  have hW : 10 ^ 8 * (d + m + (frMhat A b).size + 1) ^ 11 ≤ Spl d m M := by
    unfold Spl
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := Nat.size_le_size hMh; omega) 11)
  refine XV.seq (K₁ := 1 + (1 + 1))
    (Q₁ := fun σ => ∃ v : ℝ, σ = (((envSetup BLM.rD d).setNat BLM.rM 2).setSc 1 v).setNat BLM.rM m) ?_
    fun σ hσ => ?_
  · refine XV.seq (XV.nconst hL (i := BLM.rM) (by decide) 2 h2) fun σ1 e => ?_
    subst e
    refine XV.seq (XV.rdIn hL (x := 1) (i := BLM.rM) (by decide) (by decide) (by simpa using hoff)
      (by simpa using h2) (by simp only [nat_setNat_eq, j2]; rw [Int.cast_natCast,
        abs_of_nonneg (by positivity)]; exact_mod_cast hm2)) fun σ2 e => ?_
    subst e
    exact XV.mono (BLM.XV.rtoNat hL (i := BLM.rM) (x := 1) (v := m) (by decide) (by decide)
      (by simp only [sc_setSc_eq, nat_setNat_eq, j2]) hm2 hm2) le_rfl fun σ' e => ⟨_, e⟩
  · obtain ⟨v, rfl⟩ := hσ
    have hOK : BLM.blkS.OK LPL 135 51 8 := by
      simp only [PrBlk.OK, BLM.blkS, LPL, BLM.rD, BLM.rM, BLM.sN, BLM.aC]; omega
    refine XV.mono (frameSpec_xframe d LPL w n m A b ℓ ℓ BLM.blkS _ hd hL hOK
      (by simp [BLM.blkS, envSetup, BLM.rD, BLM.rM]) (by simp [BLM.blkS, BLM.rM]) (hW.trans hS)
      ((hW.trans hS).trans_lt hℓ))
      hW fun σ' ⟨P', d', F'⟩ => ⟨P', fun k => ?_, ?_, ?_, ?_⟩
    · exact (F'.2.2.1 aY k (by simp [BLM.blkS, aY])).trans rfl
    · exact d'.trans rfl
    · exact F'.2.2.2.1.trans rfl
    · exact F'.2.2.2.2.trans rfl

set_option maxHeartbeats 4000000 in
/-- **The frame centre on the bit machine.** -/
theorem lp_run {d n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} (hI : Bit.Asm.InputOK d n m M A b)
    {P : List Instr} (hP : B.CodeAt P 0 (prologue ++ xtr LP 6)) (w : World d) :
    ∃ (k : ℕ) (t1 : State d) (D : ℤ) (x : Fin d → ℤ) (s : ℕ),
      run P w (initBit d n m A b) k = t1 ∧ t1.pc = 6 + xtlen LP ∧ t1.coins = 0 ∧ t1.rounds = 0 ∧
      t1.cost ≤ CpL d n m M ∧ (∀ c : ℤ, c ≤ -500 → t1.mem c = 0) ∧
      (∀ c : ℕ, c < offOf d m → t1.mem c = inputMem d n m A b c) ∧ t1.mem TO = offOf d m ∧
      t1.mem (rg (LPL.rA 16)) = LPL.base d 16 ∧ t1.mem (rg (LPL.rA aY)) = LPL.base d aY ∧
      0 < D ∧ D < 2 ^ s ∧ t1.mem ((offOf d m : ℤ) + LPL.base d 16) = D ∧
      (∀ j : Fin d, |x j| < 2 ^ s ∧ t1.mem ((offOf d m : ℤ) + LPL.base d 16 + 1 + j) = x j ∧
        (x j : ℚ) / D = Bit.RQ.frameQ d n m A b j) ∧
      (∀ k < asz d, t1.mem ((offOf d m : ℤ) + LPL.base d aY + k) = 0) ∧ s ≤ Spl d m M ∧
      t1.pts = fun _ _ => 0 := by
  have hd := hI.hd
  obtain ⟨z, hz⟩ := hI.ball
  have hm := Bit.ApQ.m_pos_of_diam hd n A b hI.diam ⟨z, hz (Metric.mem_closedBall_self zero_le_one)⟩
  have hM1 : 1 ≤ M := le_trans (b ⟨0, hm⟩).den_pos (hI.height.2 ⟨0, hm⟩).2
  have hMh := BLM.frMhat_le_M A b hI.height hM1
  have hdA : d ≤ asz d := by unfold asz; omega
  have hW : 10 ^ 8 * (d + m + (frMhat A b).size + 1) ^ 11 ≤ Spl d m M := by
    unfold Spl
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := Nat.size_le_size hMh; omega) 11)
  generalize hℓ : lpL d m M = ℓ
  have hℓS : Spl d m M ≤ ℓ := by rw [← hℓ]; unfold lpL; omega
  have hℓo : offOf d m + 24 * asz d + 400 ≤ ℓ := by rw [← hℓ]; unfold lpL; omega
  have hm' : m < ℓ := by
    have : m ≤ 2 * (d + 1) * m := Nat.le_mul_of_pos_left m (by omega)
    have : offOf d m = 3 + 2 * (d + 1) * m := rfl
    omega
  have hℓ2 : ℓ < 2 ^ ℓ := Nat.lt_two_pow_self
  have hL : LayOK LPL d ℓ := ⟨by simp only [LPL]; omega, by simp only [LPL, Poly.Mach.Layout.base]; omega⟩
  -- the prologue
  obtain ⟨t6, e6, p6, hs6, c6⟩ := prologue_run (w := w) (n := n) (A := A) (b := b) (ℓa := ℓ) (ℓ := ℓ)
    hP.append_left (by omega) (by omega)
  -- the setup, `m`, the frame centre
  obtain ⟨k, s1, σ1, hk, he, hr, P1, Y1, D1, R1, Q1⟩ := setup_ok hL (dv := BLM.rD) (by decide) (by decide) (by decide)
    (by exact_mod_cast (show d < 2 ^ ℓ by omega)) (n := n) (A := A) (b := b)
    (fun w' => XV.lpInit (w := w') hd hMh hL hℓS hℓ2 hm' (by omega)) w
  have cS : B.CodeAt P 6 (xtr LP 6) := hP.append_right
  obtain ⟨n1, -, t7, e7, p7, hs7, c7⟩ := xtransfer (show (ctxOf w n m A b).off < 2 ^ ℓ by
    show offOf d m < 2 ^ ℓ; omega) (c := LP) he 6 t6 cS p6 hs6
  obtain ⟨D, hD0, hDs, hD, hx⟩ := P1
  choose x hxs hxa hxq using hx
  have hasz : 0 < asz d := by omega
  refine ⟨6 + n1, t7, D, x, _, by rw [B.run_add, e6]; exact e7, p7, ?_, ?_, ?_, ?_, ?_, hs7.off, ?_, ?_,
    hD0, hDs, ?_, fun j => ⟨hxs j, ?_, hxq j⟩, fun k hk => ?_, hW, ?_⟩
  · rw [hs7.coins, hr.draws, D1]
  · rw [hs7.rounds, hr.rounds, R1]
  · -- the cost
    have hk' : k ≤ 321 + Spl d m M := by simp only [LPL] at hk; omega
    have : k * xstepCost ℓ ℓ ≤ (321 + Spl d m M) * xstepCost ℓ ℓ := Nat.mul_le_mul_right _ hk'
    have e : (322 + Spl d m M) * xstepCost ℓ ℓ = xstepCost ℓ ℓ + (321 + Spl d m M) * xstepCost ℓ ℓ := by ring
    unfold CpL; rw [hℓ, e]
    have : (initBit d n m A b).cost = 0 := rfl
    omega
  · -- the registers above those `LP` writes
    intro c hc
    have hc' : c = rg (-c - 4).toNat := by unfold rg; omega
    have h1 := hs7.nreg (-c - 4).toNat
    rw [regMax_sound he (-c - 4).toNat (le_trans regMax_LP (by omega))] at h1
    rw [hc']; exact h1
  · intro c hc
    exact hs7.inp c hc
  · rw [hs7.nreg, hr.rA 16 (by decide)]
  · rw [hs7.nreg, hr.rA aY (by decide)]
  · have h := xsim_cell hs7 (LPL.base d 16)
    have h0 := hr.arr 16 (by decide) 0 hasz
    rw [add_zero] at h0
    rw [h0, hD] at h
    exact_mod_cast h
  · have h := xsim_cell hs7 (LPL.base d 16 + ((j : ℕ) + 1))
    have hj : (j : ℕ) + 1 < asz d := by have := j.2; have := Nat.le_mul_self d; unfold asz; omega
    rw [hr.arr 16 (by decide) ((j : ℕ) + 1) hj, hxa j] at h
    have e : ((offOf d m : ℕ) : ℤ) + ((LPL.base d 16 + ((j : ℕ) + 1) : ℕ) : ℤ) =
        (offOf d m : ℤ) + LPL.base d 16 + 1 + j := by push_cast; ring
    rw [e] at h
    exact_mod_cast h
  · have h := xsim_cell hs7 (LPL.base d aY + k)
    rw [hr.arr aY (by decide) k hk, Y1 k] at h
    have e : ((offOf d m : ℕ) : ℤ) + ((LPL.base d aY + k : ℕ) : ℤ) = (offOf d m : ℤ) + LPL.base d aY + k := by
      push_cast; ring
    rw [e] at h
    exact_mod_cast h
  · -- no point played
    funext r i
    have h := hs7.pts r
    rw [hr.pts, Q1] at h
    have := congrArg (fun v : E d => v i) h
    simpa [toE] using this

end AdversarialBco.UniPoly
