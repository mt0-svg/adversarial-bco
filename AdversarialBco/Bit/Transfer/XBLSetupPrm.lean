/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSetupCopy
public import AdversarialBco.Bit.Transfer.XSetup

@[expose] public section

/-!
# BL's setup on the machine: P0 and PARAM

From `envSetup rD d` (the setup of the registers, `d` in the register `rD` and the slot `0`): `rOne := 1`; `n` (input
cell `1`) into `sN`; `m` (input cell `2`) into `rM`; `1, 2, 4` into the slots `26, 27, 28`; PARAM (`XV.param`); its
values copied into BL's slots (`prmCopies`) and the registers `rP`, `rPF`, `rNb`, `rB`. `XV.prm`: the run ends in
`PrmPost`, within `696 G + 3222` units.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP

variable {d : ℕ}

/-- `omega` after unfolding the names of BL's cells. -/
macro "bomega" : tactic => `(tactic| ((try simp only [rD, rM, rMk, rOne, rP, rPF, rNb, rB, nN0, sZ, sMode, sFirst,
  sN, s2p, s2pF, s2g, sNe, sLam, sRint, s2eh, sEps, sLamb, sEta, sRho, sKapc, sNu, sR, sSb, sW, sA0, sB0, sDS, sDmu,
  sK, sL, nSP, nS0, aMuS, aAS, aC, aMu, aA, aB, ab, aG, nAP, nA0]) <;> omega))

/-- The copies of PARAM's values into BL's slots, `(dst, 30 + k)` for the value `pv d n k`. -/
def prmCopies : List (ℕ × ℕ) :=
  [(s2p, 65), (s2pF, 66), (s2g, 64), (sNe, 48), (sLam, 70), (sRint, 121), (s2eh, 69), (sEps, 99), (sLamb, 100),
    (sEta, 101), (sRho, 103), (sKapc, 104), (sNu, 105), (sR, 110), (sSb, 111), (sW, 115), (sA0, 119), (sB0, 120)]

theorem prmCopies_ok : (∀ p ∈ prmCopies, p.1 < 30 ∧ p.1 ≠ sMode ∧ 30 ≤ p.2 ∧ p.2 - 30 < 93) ∧
    (prmCopies.map Prod.fst).Nodup ∧ (∀ p ∈ prmCopies, ∀ q ∈ prmCopies, p.1 ≠ q.2) ∧
    (∀ p ∈ prmCopies, 4 ≤ p.1 ∧ p.1 ≤ 21) := by decide
/-- P0: `rOne := 1`, `n` into `sN`, `m` into `rM` (through the slot `123`), `1, 2, 4` into the slots `26, 27, 28`. -/
def xp0 (L : Layout) : XCmd :=
  .seq (.prim (.frag (.nconst rOne 1))) (.seq (.prim (.frag (.nconst 8 1))) (.seq (xrdIn L sN 8)
  (.seq (.prim (.frag (.nconst 8 2))) (.seq (xrdIn L 123 8) (.seq (xrtoN L rM 123)
  (.seq (toX (VL.sconst L 26 1)) (.seq (toX (VL.sconst L 27 2)) (toX (VL.sconst L 28 4)))))))))

/-- P0, PARAM and the copies. -/
def xprm (L : Layout) : XCmd :=
  .seq (xp0 L) (.seq (SL.code L parC parSt) (.seq (xcopyS L sMode prmCopies)
  (.seq (xrtoN L rP 53) (.seq (xrtoN L rPF 57) (.seq (xrtoN L rNb 122) (xrtoN L rB 60))))))

/-- The state after P0. -/
structure P0Post (d n m : ℕ) (σ : Env d) : Prop where
  nat : σ.nat rD = d ∧ σ.nat rM = m ∧ σ.nat rOne = 1 ∧ σ.nat rMk = 0
  sc : σ.sc 0 = d ∧ σ.sc sN = n ∧ σ.sc 26 = 1 ∧ σ.sc 27 = 2 ∧ σ.sc 28 = 4 ∧ σ.sc sMode = 0 ∧ σ.sc sFirst = 0 ∧
    σ.sc sDS = 0 ∧ σ.sc sDmu = 0 ∧ σ.sc sK = 0 ∧ σ.sc sL = 0 ∧ σ.sc 29 = 0
  arr : ∀ a k, σ.arr a k = 0
  draws : σ.draws = 0
  rounds : σ.rounds = 0
  pts : σ.pts = (envSetup rD d).pts

/-- The state after `xprm`. -/
structure PrmPost (d n m : ℕ) (σ : Env d) : Prop where
  nat : σ.nat rD = d ∧ σ.nat rM = m ∧ σ.nat rMk = 0 ∧ σ.nat rOne = 1 ∧ σ.nat rP = (par d n).p ∧
    σ.nat rPF = (par d n).pF ∧ σ.nat rNb = Sched.nBlk d ∧ σ.nat rB = (par d n).B
  sc : σ.sc 0 = d ∧ σ.sc sMode = 0 ∧ σ.sc sFirst = 0 ∧ σ.sc sN = n ∧ σ.sc sDS = 0 ∧ σ.sc sDmu = 0 ∧
    σ.sc sK = 0 ∧ σ.sc sL = 0 ∧ σ.sc 29 = 0
  cp : ∀ p ∈ prmCopies, σ.sc p.1 = pv d n (p.2 - 30)
  arr : ∀ a k, σ.arr a k = 0
  draws : σ.draws = 0
  rounds : σ.rounds = 0
  pts : σ.pts = (envSetup rD d).pts

/-- Every value of PARAM is at most `2^(75 G + 343)`. -/
theorem pv_abs {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) {k : ℕ} (hk : k < 93) :
    |pv d n k| ≤ 2 ^ (75 * parG d n + 343) := by
  have h := SL.val_bound parSt 30 (parI d n) [0, 3] parIn parEt parT 44 (parG d n) (SL.chk_get parSt_chk).2
    (par_sem hd hn) (parIn_ok hd hn) k (by rw [parSt_length]; exact hk)
  have hle : ∀ k < 93, (parEt k).1 ≤ 75 ∧ (parEt k).2 ≤ 343 := by decide
  obtain ⟨h1, h2⟩ := hle k hk
  refine h.trans (pow_le_pow_right₀ (by norm_num) ?_)
  unfold ev
  nlinarith

/-- The block count `B = 2 (p + size (n (d + 2)) + 2)` is at most `4 G + 4`. -/
theorem B_le {n : ℕ} (hd : 1 ≤ d) : (par d n).B ≤ 4 * parG d n + 4 := by
  have h3 : d + 2 ≤ 15 * 2 ^ 17 * d ^ 3 := by
    have : d ≤ d ^ 3 := Nat.le_self_pow (by norm_num) d
    norm_num; omega
  have h4 : n ≤ n ^ 4 := Nat.le_self_pow (by norm_num) n
  have h1 : (n * (d + 2)).size ≤ (BLP.Ne d n).size := Nat.size_le_size (by
    unfold BLP.Ne
    calc n * (d + 2) ≤ n ^ 4 * (15 * 2 ^ 17 * d ^ 3) := Nat.mul_le_mul h4 h3
      _ = 15 * 2 ^ 17 * d ^ 3 * n ^ 4 := by ring)
  have hG := parG_ge (d := d) (n := n)
  have e : (par d n).B = 2 * ((par d n).p + (n * (d + 2)).size + 2) := by simp only [par]
  omega

/-- `rtoN` on a slot holding a natural number. -/
theorem XV.rtoNat {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {σ : Env d} {i x v : ℕ}
    (hi : i < L.NN) (hx : x < L.NS) (hv : σ.sc x = ((v : ℤ) : ℝ)) (ha : v < 2 ^ ℓa) (hl : v < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xrtoN L i x) σ 1 (· = σ.setNat i v) :=
  XV.mono (XV.rtoN hL hi hx (by rw [hv]; positivity) (by rw [hv]; exact_mod_cast ha)
    (by rw [hv, abs_of_nonneg (by positivity)]; exact_mod_cast hl)) le_rfl fun σ' e => by
    rw [e, hv, Int.floor_intCast, Int.toNat_natCast]

/-- **P0 on the machine.** -/
theorem XV.p0 {L : Layout} {w : BitRAM.World d} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hNS : 172 ≤ L.NS) (hNN : 48 ≤ L.NN) (hnl : n < 2 ^ ℓ) (hma : m < 2 ^ ℓa)
    (hml : m < 2 ^ ℓ) (h3 : 3 ≤ ℓ) :
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xp0 L) (envSetup rD d) 9 (P0Post d n m) := by
  have hL1 := hL.1
  have j1 : (ctxOf w n m A b).inp 1 = n := (BitRAM.Conj1BitSanity.inputMem_small (n := n) A b).2.1
  have j2 : (ctxOf w n m A b).inp 2 = m := (BitRAM.Conj1BitSanity.inputMem_small (n := n) A b).2.2
  have hoff : (ctxOf w n m A b).off = 3 + 2 * (d + 1) * m := rfl
  refine XV.mono (K := 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))) ?_ (by norm_num) fun _ h => h
  refine XV.seq (XV.nconst hL (i := rOne) (by bomega) 1 (by bomega)) fun σ1 e => ?_
  subst e
  refine XV.seq (XV.nconst hL (i := 8) (by bomega) 1 (by bomega)) fun σ2 e => ?_
  subst e
  refine XV.seq (XV.rdIn hL (x := sN) (i := 8) (by bomega) (by bomega)
    (by simp only [nat_setNat_eq, hoff]; omega) (by simp only [nat_setNat_eq]; omega)
    (by simp only [nat_setNat_eq, j1]; rw [Int.cast_natCast, abs_of_nonneg (by positivity)]; exact_mod_cast hnl))
    fun σ3 e => ?_
  subst e
  refine XV.seq (XV.nconst hL (i := 8) (by bomega) 2 (by bomega)) fun σ4 e => ?_
  subst e
  refine XV.seq (XV.rdIn hL (x := 123) (i := 8) (by bomega) (by bomega)
    (by simp only [nat_setNat_eq, hoff]; omega) (by simp only [nat_setNat_eq]; omega)
    (by simp only [nat_setNat_eq, j2]; rw [Int.cast_natCast, abs_of_nonneg (by positivity)]; exact_mod_cast hml))
    fun σ5 e => ?_
  subst e
  refine XV.seq (XV.rtoNat hL (i := rM) (x := 123) (v := m) (by bomega) (by bomega)
    (by simp only [sc_setSc_eq, nat_setNat_eq, j2]) hma hml) fun σ6 e => ?_
  subst e
  refine XV.seq (XV.constI hL (x := 26) (by bomega) 1 (by
    rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega))) fun σ7 e => ?_
  subst e
  refine XV.seq (XV.constI hL (x := 27) (by bomega) 2 (by
    norm_num; exact lt_of_lt_of_le (by norm_num) (pow_le_pow_right₀ (by norm_num) (by omega : 2 ≤ ℓ))))
    fun σ8 e => ?_
  subst e
  refine XV.mono (XV.constI hL (x := 28) (by bomega) 4 (by
    norm_num; exact lt_of_lt_of_le (by norm_num) (pow_le_pow_right₀ (by norm_num) (by omega : 3 ≤ ℓ))))
    le_rfl fun σ9 e => ?_
  subst e
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun a k => ?_, ?_, ?_, ?_⟩ <;>
    simp [envSetup, j1, rD, rM, rMk, rOne, sN, sMode, sFirst, sDS, sDmu, sK, sL]

set_option maxHeartbeats 1000000 in
/-- **P0, PARAM and the copies on the machine.** -/
theorem XV.prm {L : Layout} {w : BitRAM.World d} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hNS : 172 ≤ L.NS) (hNN : 48 ≤ L.NN) (hNA : 16 ≤ L.NA) (hd : 1 ≤ d)
    (hn : 1 ≤ n) (hT : 75 * parG d n + 343 < ℓ) (hTa : 75 * parG d n + 343 < 2 ^ ℓa) (hma : m < 2 ^ ℓa)
    (hml : m < 2 ^ ℓ) :
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xprm L) (envSetup rD d) (696 * parG d n + 3222) (PrmPost d n m) := by
  have hL1 := hL.1
  have hda := asz_lt hL (a := 0) (by omega)
  unfold asz at hda
  have hdd : d ≤ d * d := Nat.le_mul_self d
  have hG := parG_ge (d := d) (n := n)
  have hB := B_le (n := n) hd
  have h2ℓ : (2 : ℤ) ^ (75 * parG d n + 343) < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) hT
  have hnG : n ≤ 2 ^ parG d n := n_le_G hd hn
  have hdG : d ≤ 2 ^ parG d n := d_le_G
  have hGl : 2 ^ parG d n < 2 ^ ℓ := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hℓ : ℓ < 2 ^ ℓ := Nat.lt_two_pow_self
  refine XV.mono (K := 9 + ((696 * parG d n + 3191) + (prmCopies.length + (1 + (1 + (1 + 1)))))) ?_
    (by rw [show prmCopies.length = 18 from rfl]; omega) fun _ h => h
  refine XV.seq (XV.p0 hL hNS hNN (by omega) hma hml (by omega)) fun σ9 h9 => ?_
  refine XV.seq (XV.param hL hNS (by bomega) hd hn hT hTa h9.sc.1 h9.sc.2.1 h9.sc.2.2.2.2.2.1 h9.sc.2.2.1
    h9.sc.2.2.2.1 h9.sc.2.2.2.2.1 h9.nat.2.2.1) fun σp ⟨hp, dp, Fp⟩ => ?_
  have hpv : ∀ y, 30 ≤ y → y < 123 → σp.sc y = pv d n (y - 30) := fun y h1 h2 => by
    have := hp (y - 30) (by omega)
    rwa [show 30 + (y - 30) = y by omega] at this
  have pz : ∀ y, y < 30 → σp.sc y = σ9.sc y := fun y hy => Fp.2.1 y (by omega)
  have pn : ∀ j, j < 8 → σp.nat j = σ9.nat j := fun j hj => Fp.1 j (by omega)
  obtain ⟨c1, c2, c3, c4⟩ := prmCopies_ok
  refine XV.seq (XV.copyS hL (z := sMode) (by bomega) prmCopies σp
    (by rw [pz _ (by bomega)]; exact h9.sc.2.2.2.2.2.1) (fun p hp' => ?_) c2 c3) fun σc ⟨hc, dc, Fc⟩ => ?_
  · obtain ⟨q1, q2, q3, q4⟩ := c1 p hp'
    refine ⟨by omega, by omega, q2, ?_⟩
    rw [hpv _ q3 (by omega)]
    have := (pv_abs hd hn q4).trans_lt h2ℓ
    exact_mod_cast this
  have cz : ∀ y, (y < 4 ∨ 21 < y) → σc.sc y = σp.sc y := fun y hy => Fc.2.1 y (fun h => by
    obtain ⟨p, hp', e⟩ := List.mem_map.1 h
    have := c4 p hp'
    omega)
  have hcs : ∀ y, 30 ≤ y → y < 123 → σc.sc y = pv d n (y - 30) := fun y h1 h2 => by
    rw [cz y (by omega), hpv y h1 h2]
  refine XV.seq (XV.rtoNat hL (i := rP) (x := 53) (v := (par d n).p) (by bomega) (by bomega)
    (by rw [(hcs 53 (by norm_num) (by norm_num) : σc.sc 53 = ((pv d n 23 : ℤ) : ℝ)), pv_23])
    (by omega) (by omega)) fun σ1 e => ?_
  subst e
  refine XV.seq (XV.rtoNat hL (i := rPF) (x := 57) (v := (par d n).pF) (by bomega) (by bomega)
    (by rw [Env.setNat_sc, (hcs 57 (by norm_num) (by norm_num) : σc.sc 57 = ((pv d n 27 : ℤ) : ℝ)), pv_27])
    (by omega) (by omega)) fun σ2 e => ?_
  subst e
  refine XV.seq (XV.rtoNat hL (i := rNb) (x := 122) (v := Sched.nBlk d) (by bomega) (by bomega)
    (by rw [Env.setNat_sc, Env.setNat_sc,
      (hcs 122 (by norm_num) (by norm_num) : σc.sc 122 = ((pv d n 92 : ℤ) : ℝ)), pv_92])
    (by unfold Sched.nBlk; omega) (by unfold Sched.nBlk; omega)) fun σ3 e => ?_
  subst e
  refine XV.mono (XV.rtoNat hL (i := rB) (x := 60) (v := (par d n).B) (by bomega) (by bomega)
    (by rw [Env.setNat_sc, Env.setNat_sc, Env.setNat_sc,
      (hcs 60 (by norm_num) (by norm_num) : σc.sc 60 = ((pv d n 30 : ℤ) : ℝ)), pv_30])
    (by omega) (by omega)) le_rfl fun σ' e => ?_
  subst e
  have ns : ∀ y, (y < 4 ∨ 21 < y) → y < 30 → σc.sc y = σ9.sc y := fun y h1 h2 => by rw [cz y h1, pz y h2]
  have nn : ∀ j, j < 8 → σc.nat j = σ9.nat j := fun j hj => by rw [Fc.1 j id, pn j hj]
  obtain ⟨n1, n2, n3, n4⟩ := h9.nat
  obtain ⟨s1, s2, -, -, -, s6, s7, s8, s9, s10, s11, s12⟩ := h9.sc
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun p hp' => ?_, fun a k => ?_,
    ?_, ?_, ?_⟩
  · simp only [Env.setNat_nat, rD, rB, rNb, rPF, rP]; simp; rw [nn 0 (by omega)]; exact n1
  · simp only [Env.setNat_nat, rM, rB, rNb, rPF, rP]; simp; rw [nn 1 (by omega)]; exact n2
  · simp only [Env.setNat_nat, rMk, rB, rNb, rPF, rP]; simp; rw [nn 2 (by omega)]; exact n4
  · simp only [Env.setNat_nat, rOne, rB, rNb, rPF, rP]; simp; rw [nn 3 (by omega)]; exact n3
  · simp [Env.setNat_nat, rB, rNb, rPF, rP]
  · simp [Env.setNat_nat, rB, rNb, rPF]
  · simp [Env.setNat_nat, rB, rNb]
  · simp [Env.setNat_nat, rB]
  · simp only [Env.setNat_sc]; rw [ns 0 (by omega) (by omega)]; exact s1
  · simp only [Env.setNat_sc]; rw [ns 1 (by omega) (by omega)]; exact s6
  · simp only [Env.setNat_sc]; rw [ns 2 (by omega) (by omega)]; exact s7
  · simp only [Env.setNat_sc]; rw [ns 3 (by omega) (by omega)]; exact s2
  · simp only [Env.setNat_sc]; rw [ns 22 (by omega) (by omega)]; exact s8
  · simp only [Env.setNat_sc]; rw [ns 23 (by omega) (by omega)]; exact s9
  · simp only [Env.setNat_sc]; rw [ns 24 (by omega) (by omega)]; exact s10
  · simp only [Env.setNat_sc]; rw [ns 25 (by omega) (by omega)]; exact s11
  · simp only [Env.setNat_sc]; rw [ns 29 (by omega) (by omega)]; exact s12
  · obtain ⟨q1, -, q3, q4⟩ := c1 p hp'
    simp only [Env.setNat_sc]
    rw [hc p hp', hpv _ q3 (by omega)]
  · simp only [Env.setNat_arr]
    rw [Fc.2.2.1 a k id, Fp.2.2.1]
    exact h9.arr a k
  · simp only [Env.setNat_draws]; rw [dc, dp]; exact h9.draws
  · simp only [Env.setNat_rounds]; rw [Fc.2.2.2.1, Fp.2.2.2.1]; exact h9.rounds
  · simp only [Env.setNat_pts]; rw [Fc.2.2.2.2, Fp.2.2.2.2]; exact h9.pts

end AdversarialBco.Bit.Transfer.BLM
