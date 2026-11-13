/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSetupPrm
public import AdversarialBco.Bit.Transfer.XBLSetupFacts

@[expose] public section

/-!
# BL's setup on the machine: the calls of FRAME and TRI

`FrameSpec`, `TriSpec`: the bodies of `FrameRule` and `TriRule` for given commands and constants (`Iff.rfl`). `xcalls`:
FRAME into the array `16` of the block `blkS`, the centre copied into `aC`; TRI on the coins from `draws`, its
position (slot `128`, arrays `16`, `17`) copied into `sDS`, `aMuS`, `aAS`. `XV.calls`: the centre is `frameQ` in the
form of the play leaf in `aC`, the position is `posQ` in BL's cells, `K0Q d n` coins read.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ

variable {d : ℕ}

/-! ## The rules as hypotheses -/

/-- The body of `FrameRule` for the command `xframe` and the constants `C, k, nS, nN, nA`. -/
def FrameSpec (xframe : Layout → PrBlk → XCmd) (C k nS nN nA : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (w : BitRAM.World d) (n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (ℓa ℓ : ℕ) (B : PrBlk) (σ : Env d),
    1 ≤ d → LayOK L d ℓa → B.OK L nS nN nA → σ.nat B.rd = d → σ.nat B.rm = m →
    C * (d + m + (frMhat A b).size + 1) ^ k ≤ ℓ → C * (d + m + (frMhat A b).size + 1) ^ k < 2 ^ ℓa →
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xframe L B) σ (C * (d + m + (frMhat A b).size + 1) ^ k) (fun σ' =>
      PtIn σ' B.aW (C * (d + m + (frMhat A b).size + 1) ^ k) (frameQ d n m A b) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => B.o ≤ y) (fun j => B.rE ≤ j) (fun b _ => B.aW ≤ b) σ σ')

theorem frameRule_iff : FrameRule ↔ ∃ xframe C k nS nN nA, FrameSpec xframe C k nS nN nA := Iff.rfl

/-- The body of `TriRule` for the command `xtri` and the constants `C, k, nS, nN, nA`. -/
def TriSpec (xtri : Layout → PrBlk → XCmd) (C k nS nN nA : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (w : BitRAM.World d) (n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (ℓa ℓ s : ℕ) (B : PrBlk) (σ : Env d),
    1 ≤ d → 1 ≤ n → LayOK L d ℓa → B.OK L nS nN nA → σ.nat B.rd = d → σ.nat B.rm = m →
    σ.sc B.sn = n → PtIn σ B.aC s (frameQ d n m A b) →
    C * (d + m + n.size + (frMhat A b).size + s + 1) ^ k ≤ ℓ →
    C * (d + m + n.size + (frMhat A b).size + s + 1) ^ k < 2 ^ ℓa →
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xtri L B) σ (C * (d + m + n.size + (frMhat A b).size + s + 1) ^ k)
      (fun σ' =>
        PosIn σ' B.o B.aW (C * (d + m + n.size + (frMhat A b).size + s + 1) ^ k)
          (posQ d n m A b fun j => w.cs (σ.draws + j)) ∧
        σ'.draws = σ.draws + K0Q d n ∧
        FrameA (fun y => B.o ≤ y) (fun j => B.rE ≤ j) (fun b _ => B.aW ≤ b) σ σ')

theorem triRule_iff : TriRule ↔ ∃ xtri C k nS nN nA, TriSpec xtri C k nS nN nA := Iff.rfl

/-! ## The calls -/

/-- The block of the setup's calls: `d`, `m` in `rD`, `rM`, `n` in `sN`, the centre in `aC`; the routines' own cells
from the slot `128`, the register `48`, the array `16`. -/
def blkS : PrBlk := ⟨rD, rM, sN, aC, 128, 48, 16⟩

/-- FRAME's integers are below `2^(sF ..)`. -/
def sF (C k d m : ℕ) {m' : ℕ} (A : Matrix (Fin m') (Fin d) ℚ) (b : Fin m' → ℚ) : ℕ :=
  C * (d + m + (frMhat A b).size + 1) ^ k

/-- TRI's integers are below `2^(sT ..)`, on FRAME's `s`. -/
def sT (C k d n m s : ℕ) {m' : ℕ} (A : Matrix (Fin m') (Fin d) ℚ) (b : Fin m' → ℚ) : ℕ :=
  C * (d + m + n.size + (frMhat A b).size + s + 1) ^ k

/-- FRAME, the centre into `aC`, TRI, the position into `sDS`, `aMuS`, `aAS`. -/
def xcalls (L : Layout) (xframe xtri : Layout → PrBlk → XCmd) : XCmd :=
  .seq (xframe L blkS) (.seq (.prim (.frag (.nadd 10 rD rOne))) (.seq (xcopyN L sZ 124 16 aC 8 9 10 rOne)
  (.seq (xtri L blkS) (.seq (xset L sDS 128 sZ) (.seq (xcopyN L sZ 124 16 aMuS 8 9 rD rOne)
  (.seq (xnmul 10 rD rD) (xcopyN L sZ 124 17 aAS 8 9 10 rOne)))))))

/-- The units of `xcalls`. -/
def callUnits (d Kf Kt : ℕ) : ℕ :=
  Kf + (1 + ((1 + ((d + 1) * (2 + 6) + 3)) + (Kt + (1 + ((1 + (d * (2 + 6) + 3)) + (1 + (1 + (d * d * (2 + 6) +
    3))))))))

/-- The cells `xcalls` changes. -/
def SC (y : ℕ) : Prop := y = sDS ∨ 124 ≤ y
def NC (j : ℕ) : Prop := j = 8 ∨ j = 9 ∨ j = 10 ∨ 48 ≤ j
def AC (a c : ℕ) : Prop := (a = aC ∧ c < d + 1) ∨ (a = aMuS ∧ c < d) ∨ (a = aAS ∧ c < d * d) ∨ 16 ≤ a

/-- `PtIn` as a function of the cells. -/
theorem ptIn_fun {d : ℕ} (arr : ℕ → ℝ) (s : ℕ) (c : Fin d → ℚ)
    (h : ∃ D : ℤ, 0 < D ∧ D < 2 ^ s ∧ arr 0 = D ∧
      ∀ j : Fin d, ∃ x : ℤ, |x| < 2 ^ s ∧ arr (j + 1) = x ∧ (x : ℚ) / D = c j) :
    ∃ x : ℕ → ℤ, (∀ k < d + 1, arr k = x k ∧ |x k| < 2 ^ s) ∧ 0 < x 0 ∧
      ∀ j : Fin d, (x (j + 1) : ℚ) / x 0 = c j := by
  rcases h with ⟨D, hDpos, hDlt, harr0, hx⟩
  choose xf hx_bound hx_arr hx_eq using hx
  let x : ℕ → ℤ := λ k =>
    if hk0 : k = 0 then D
    else if hk : k - 1 < d then xf ⟨k - 1, hk⟩
    else 0
  refine ⟨x, ?_, ?_, ?_⟩
  · intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      have hx0 : x 0 = D := by simp [x]
      refine ⟨?_, ?_⟩
      · simpa [x] using harr0
      · rw [hx0]
        have habs : |D| = D := abs_of_pos hDpos
        rw [habs]
        exact hDlt
    · have hk_sub_lt : k - 1 < d := by
        have hk_le_d : k ≤ d := by omega
        omega
      have hx_val : x k = xf ⟨k - 1, hk_sub_lt⟩ := by
        simp [x, hk0, hk_sub_lt]
      refine ⟨?_, ?_⟩
      · -- arr k = x k
        rw [hx_val]
        have := hx_arr ⟨k - 1, hk_sub_lt⟩
        have hpos : 1 ≤ k := Nat.one_le_of_lt (Nat.pos_of_ne_zero hk0)
        -- this : arr (↑⟨k-1, hk_sub_lt⟩ + 1) = ↑(xf ⟨k-1, hk_sub_lt⟩)
        -- ↑⟨k-1, hk_sub_lt⟩ = k-1, so this : arr ((k-1) + 1) = ↑(xf ⟨k-1, hk_sub_lt⟩)
        -- And (k-1) + 1 = k
        simpa [Nat.sub_add_cancel hpos] using this
      · -- |x k| < 2 ^ s
        rw [hx_val]
        exact hx_bound ⟨k - 1, hk_sub_lt⟩
  · -- 0 < x 0
    have hx0 : x 0 = D := by simp [x]
    rw [hx0]
    exact hDpos
  · -- ∀ j : Fin d, (x (j + 1) : ℚ) / x 0 = c j
    intro j
    have hx0 : x 0 = D := by simp [x]
    rw [hx0]
    have hx_j1 : x (j.val + 1) = xf j := by
      dsimp [x]
      simp [j.is_lt]
    -- Now (x (j.val + 1) : ℚ) / D = c j
    -- hx_eq j : (xf j : ℚ) / D = c j
    -- And x (j.val + 1) = xf j
    rw [hx_j1]
    exact hx_eq j

/-- `PosIn` as functions of the cells. -/
theorem posIn_fun {d : ℕ} (sc : ℝ) (arr0 arr1 : ℕ → ℝ) (s : ℕ)
    (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ)
    (h : ∃ D : ℤ, 0 < D ∧ D < 2 ^ s ∧ sc = D ∧
      (∀ j : Fin d, ∃ x : ℤ, |x| < 2 ^ s ∧ arr0 j = x ∧ (x : ℚ) / D = S.1 j) ∧
      ∀ i j : Fin d, ∃ x : ℤ, |x| < 2 ^ s ∧ arr1 (d * i + j) = x ∧ (x : ℚ) / D = S.2 i j) :
    ∃ (D : ℤ) (xm xa : ℕ → ℤ), 0 < D ∧ D < 2 ^ s ∧ sc = D ∧
      (∀ k < d, arr0 k = xm k ∧ |xm k| < 2 ^ s) ∧ (∀ k < d * d, arr1 k = xa k ∧ |xa k| < 2 ^ s) ∧
      (∀ j : Fin d, (xm j : ℚ) / D = S.1 j) ∧ ∀ i j : Fin d, (xa (d * i + j) : ℚ) / D = S.2 i j := by
  obtain ⟨D, hD0, hDs, hsc, hm, ha⟩ := h
  choose xmf hxm1 hxm2 hxm3 using hm
  choose xaf hxa1 hxa2 hxa3 using ha
  have hd0 : ∀ k, k < d * d → 0 < d := fun k hk => by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; simp at hk
    · exact h
  refine ⟨D, fun k => if hk : k < d then xmf ⟨k, hk⟩ else 0,
    fun k => if hk : k < d * d then xaf ⟨k / d, Nat.div_lt_of_lt_mul hk⟩ ⟨k % d, Nat.mod_lt _ (hd0 k hk)⟩ else 0,
    hD0, hDs, hsc, fun k hk => ?_, fun k hk => ?_, fun j => ?_, fun i j => ?_⟩
  · simp only [dif_pos hk]; exact ⟨hxm2 ⟨k, hk⟩, hxm1 ⟨k, hk⟩⟩
  · simp only [dif_pos hk]
    have e : d * (k / d) + k % d = k := Nat.div_add_mod k d
    have := hxa2 ⟨k / d, Nat.div_lt_of_lt_mul hk⟩ ⟨k % d, Nat.mod_lt _ (hd0 k hk)⟩
    simp only at this
    rw [e] at this
    exact ⟨this, hxa1 _ _⟩
  · simp only [dif_pos j.2]; exact hxm3 j
  · have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le _) i.2
    have hlt : d * (i : ℕ) + j < d * d := by
      have := i.2; have := j.2; nlinarith
    simp only [dif_pos hlt]
    have h1 : (d * (i : ℕ) + j) / d = i := by
      rw [Nat.mul_add_div hd, Nat.div_eq_of_lt j.2, add_zero]
    have h2 : (d * (i : ℕ) + j) % d = j := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt j.2]
    have e : xaf ⟨(d * (i : ℕ) + j) / d, Nat.div_lt_of_lt_mul hlt⟩ ⟨(d * (i : ℕ) + j) % d, Nat.mod_lt _ hd⟩ =
        xaf i j := by
      congr 1 <;> exact Fin.ext (by simp only [h1, h2])
    rw [e]; exact hxa3 i j

set_option maxHeartbeats 4000000 in
/-- **The calls of FRAME and TRI on the machine.** -/
theorem XV.calls {L : Layout} {w : BitRAM.World d} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    {ℓa ℓ : ℕ} {xframe xtri : Layout → PrBlk → XCmd} {Cf kf nSf nNf nAf Ct kt nSt nNt nAt : ℕ}
    (hF : FrameSpec xframe Cf kf nSf nNf nAf) (hT : TriSpec xtri Ct kt nSt nNt nAt) (hL : LayOK L d ℓa)
    (hOKf : blkS.OK L nSf nNf nAf) (hOKt : blkS.OK L nSt nNt nAt) (hNS : 172 ≤ L.NS) (hNA : 18 ≤ L.NA)
    (hd : 1 ≤ d) (hn : 1 ≤ n)
    (hsf : sF Cf kf d m A b < ℓ) (hsfa : sF Cf kf d m A b < 2 ^ ℓa)
    (hst : sT Ct kt d n m (sF Cf kf d m A b) A b < ℓ) (hsta : sT Ct kt d n m (sF Cf kf d m A b) A b < 2 ^ ℓa)
    {σ : Env d} (hD : σ.nat rD = d) (hM : σ.nat rM = m) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0)
    (hsN : σ.sc sN = n) :
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xcalls L xframe xtri) σ
      (callUnits d (sF Cf kf d m A b) (sT Ct kt d n m (sF Cf kf d m A b) A b)) (fun σ' =>
        PtIn σ' aC (sF Cf kf d m A b) (frameQ d n m A b) ∧
        PosIn σ' sDS aMuS (sT Ct kt d n m (sF Cf kf d m A b) A b)
          (posQ d n m A b fun j => w.cs (σ.draws + j)) ∧
        σ'.draws = σ.draws + K0Q d n ∧ FrameA SC NC (AC (d := d)) σ σ') := by
  have hL1 := hL.1
  have hda := asz_lt hL (a := 0) (by omega)
  unfold asz at hda
  have hdd : d ≤ d * d := Nat.le_mul_self d
  obtain ⟨o1, o2, o3, -, -, -, -⟩ := id hOKf
  simp only [blkS] at o1 o2 o3
  set sf := sF Cf kf d m A b with hsfd
  set st := sT Ct kt d n m sf A b with hstd
  -- FRAME
  refine XV.seq (hF d L w n m A b ℓa ℓ blkS σ hd hL hOKf hD hM hsf.le hsfa) fun σ1 ⟨P1, d1, F1⟩ => ?_
  obtain ⟨xc, hxc, hxc0, hxcj⟩ := ptIn_fun (σ1.arr 16) sf _ P1
  have n1 : ∀ j, j < 48 → σ1.nat j = σ.nat j := fun j hj => F1.1 j (by simp only [blkS]; omega)
  have s1 : ∀ y, y < 128 → σ1.sc y = σ.sc y := fun y hy => F1.2.1 y (by simp only [blkS]; omega)
  have a1 : ∀ a k, a < 16 → σ1.arr a k = σ.arr a k := fun a k ha => F1.2.2.1 a k (by simp only [blkS]; omega)
  -- the centre into `aC`
  refine XV.seq (XV.nadd hL (i := 10) (a := rD) (b := rOne) (by bomega) (by bomega) (by bomega)
    (by rw [n1 _ (by bomega), hD]; omega) (by rw [n1 _ (by bomega), h1]; omega)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.copyN hL (z := sZ) (t := 124) (src := 16) (dst := aC) (nr := 8) (nk := 9) (nn := 10)
    (one := rOne) (E := sf) (N := d + 1) (x := xc) (by bomega) (by bomega)
    (by rw [Env.setNat_sc, s1 _ (by bomega), hz]) (by omega) (by bomega) (by bomega) (by bomega) (by bomega)
    (by bomega) (by bomega) (by decide)
    (by rw [Env.setNat_nat, if_pos rfl, n1 _ (by bomega), n1 _ (by bomega), hD, h1])
    (by rw [Env.setNat_nat, if_neg (by bomega), n1 _ (by bomega), h1]) (by unfold asz; nlinarith)
    (fun k hk => by rw [Env.setNat_arr]; exact (hxc k hk).1) (fun k hk => (hxc k hk).2.le) hsf)
    fun σ3 ⟨c3, d3, F3⟩ => ?_
  have P3 : PtIn σ3 aC sf (frameQ d n m A b) := by
    refine ⟨xc 0, hxc0, lt_of_abs_lt (hxc 0 (by omega)).2, c3 0 (by omega), fun j => ⟨xc (j + 1),
      (hxc (j + 1) (by omega)).2, c3 _ (by omega), hxcj j⟩⟩
  have n3 : ∀ j, j < 48 → j ≠ 8 → j ≠ 9 → j ≠ 10 → σ3.nat j = σ.nat j := fun j hj h8 h9 h10 => by
    rw [F3.1 j (by omega), Env.setNat_nat, if_neg h10, n1 j hj]
  have s3 : ∀ y, y < 124 → σ3.sc y = σ.sc y := fun y hy => by
    rw [F3.2.1 y (by omega), Env.setNat_sc, s1 y (by omega)]
  -- TRI
  refine XV.seq (hT d L w n m A b ℓa ℓ sf blkS σ3 hd hn hL hOKt (by simp only [blkS]; rw [n3 _ (by bomega)
    (by bomega) (by bomega) (by bomega), hD]) (by simp only [blkS]; rw [n3 _ (by bomega) (by bomega) (by bomega)
    (by bomega), hM]) (by simp only [blkS]; rw [s3 _ (by bomega), hsN]) P3 hst.le hsta) fun σ4 ⟨P4, d4, F4⟩ => ?_
  obtain ⟨D, xm, xa, hD0, hDs, hsc, hxm, hxa, hxmj, hxaij⟩ := posIn_fun (σ4.sc 128) (σ4.arr 16) (σ4.arr 17) st _ P4
  have s4 : ∀ y, y < 128 → σ4.sc y = σ3.sc y := fun y hy => F4.2.1 y (by simp only [blkS]; omega)
  have n4 : ∀ j, j < 48 → σ4.nat j = σ3.nat j := fun j hj => F4.1 j (by simp only [blkS]; omega)
  have a4 : ∀ a k, a < 16 → σ4.arr a k = σ3.arr a k := fun a k ha => F4.2.2.1 a k (by simp only [blkS]; omega)
  have hσ4 : σ4.sc sZ = 0 := by rw [s4 _ (by bomega), s3 _ (by bomega), hz]
  have hDl : |(D : ℝ)| < 2 ^ ℓ := by
    rw [abs_of_pos (by exact_mod_cast hD0)]
    exact_mod_cast hDs.trans (pow_lt_pow_right₀ (by norm_num) hst)
  -- the position into `sDS`, `aMuS`, `aAS`
  refine XV.seq (XV.sop2 hL (x := sDS) (a := 128) (b := sZ) (by bomega) (by omega) (by bomega) .add
    (by intro h; cases h) (by rw [hsc]; exact hDl) (by rw [hσ4]; simp)
    (by simp only [RealRAM.Op2.eval, hσ4, add_zero, hsc]; exact hDl)) fun σ5 e5 => ?_
  subst e5
  have n5 : ∀ j, j < 48 → j ≠ 8 → j ≠ 9 → j ≠ 10 → (σ4.setSc sDS (RealRAM.Op2.eval .add (σ4.sc 128)
      (σ4.sc sZ))).nat j = σ.nat j := fun j hj h8 h9 h10 => by
    rw [Env.setSc_nat, n4 j hj, n3 j hj h8 h9 h10]
  refine XV.seq (XV.copyN hL (z := sZ) (t := 124) (src := 16) (dst := aMuS) (nr := 8) (nk := 9) (nn := rD)
    (one := rOne) (E := st) (N := d) (x := xm) (by bomega) (by bomega)
    (by rw [Env.setSc_sc, if_neg (by bomega), hσ4]) (by omega) (by bomega) (by bomega) (by bomega) (by bomega)
    (by bomega) (by bomega) (by decide) (by rw [n5 _ (by bomega) (by bomega) (by bomega) (by bomega), hD])
    (by rw [n5 _ (by bomega) (by bomega) (by bomega) (by bomega), h1]) (by unfold asz; omega)
    (fun k hk => by rw [Env.setSc_arr]; exact (hxm k hk).1) (fun k hk => (hxm k hk).2.le) hst)
    fun σ6 ⟨c6, d6, F6⟩ => ?_
  have n6 : ∀ j, j ≠ 8 → j ≠ 9 → σ6.nat j = (σ4.setSc sDS (RealRAM.Op2.eval .add (σ4.sc 128) (σ4.sc sZ))).nat j :=
    fun j h8 h9 => F6.1 j (by omega)
  refine XV.seq (XV.nmul hL (i := 10) (a := rD) (b := rD) (by bomega) (by bomega) (by bomega)
    (by rw [n6 _ (by bomega) (by bomega), n5 _ (by bomega) (by bomega) (by bomega) (by bomega), hD]; omega)
    (by rw [n6 _ (by bomega) (by bomega), n5 _ (by bomega) (by bomega) (by bomega) (by bomega), hD]; omega)
    (by rw [n6 _ (by bomega) (by bomega), n5 _ (by bomega) (by bomega) (by bomega) (by bomega), hD]; omega))
    fun σ7 e7 => ?_
  subst e7
  have hd6 : σ6.nat rD = d := by rw [n6 _ (by bomega) (by bomega), n5 _ (by bomega) (by bomega) (by bomega)
    (by bomega), hD]
  have h16 : σ6.nat rOne = 1 := by rw [n6 _ (by bomega) (by bomega), n5 _ (by bomega) (by bomega) (by bomega)
    (by bomega), h1]
  have hz6 : σ6.sc sZ = 0 := by rw [F6.2.1 _ (by bomega), Env.setSc_sc, if_neg (by bomega), hσ4]
  refine XV.mono (XV.copyN hL (z := sZ) (t := 124) (src := 17) (dst := aAS) (nr := 8) (nk := 9) (nn := 10)
    (one := rOne) (E := st) (N := d * d) (x := xa) (by bomega) (by bomega)
    (by rw [Env.setNat_sc, hz6]) (by omega) (by bomega) (by bomega) (by bomega) (by bomega)
    (by bomega) (by bomega) (by decide) (by rw [Env.setNat_nat, if_pos rfl, hd6])
    (by rw [Env.setNat_nat, if_neg (by bomega), h16]) (by unfold asz; omega)
    (fun k hk => by
      rw [Env.setNat_arr, F6.2.2.1 _ _ (by bomega), Env.setSc_arr]; exact (hxa k hk).1)
    (fun k hk => (hxa k hk).2.le) hst) le_rfl fun σ8 ⟨c8, d8, F8⟩ => ?_
  have e3 : σ3.draws = σ.draws := by rw [d3, Env.setNat_draws, d1]
  rw [e3] at hxmj hxaij
  have ac : σ8.arr aC = σ3.arr aC := funext fun k => by
    rw [F8.2.2.1 _ _ (by bomega), Env.setNat_arr, F6.2.2.1 _ _ (by bomega), Env.setSc_arr, a4 _ _ (by bomega)]
  have am : ∀ k < d, σ8.arr aMuS k = xm k := fun k hk => by
    rw [F8.2.2.1 _ _ (by bomega), Env.setNat_arr, c6 k hk]
  have hsD : σ8.sc sDS = D := by
    rw [F8.2.1 _ (by bomega), Env.setNat_sc, F6.2.1 _ (by bomega), Env.setSc_sc, if_pos rfl]
    simp only [RealRAM.Op2.eval, hσ4, add_zero, hsc]
  have hdij : ∀ i j : Fin d, d * (i : ℕ) + j < d * d := fun i j => by
    have := i.2; have := j.2; nlinarith
  refine ⟨?_, ⟨D, hD0, hDs, hsD, fun j => ⟨xm j, (hxm j j.2).2, am j j.2, hxmj j⟩,
    fun i j => ⟨xa (d * i + j), (hxa _ (hdij i j)).2, c8 _ (hdij i j), hxaij i j⟩⟩, ?_, ?_⟩
  · unfold PtIn; rw [ac]; exact P3
  · rw [d8, Env.setNat_draws, d6, Env.setSc_draws, d4, e3]
  · have G1 : FrameA SC NC (AC (d := d)) σ σ1 :=
      F1.mono (fun y h => Or.inr (by simp only [blkS] at h; omega)) (fun j h => by
        simp only [blkS] at h; simp only [NC]; omega) (fun b c h => by
        simp only [blkS] at h; simp only [AC]; omega)
    have G3 : FrameA SC NC (AC (d := d)) (σ1.setNat 10 (σ1.nat rD + σ1.nat rOne)) σ3 :=
      F3.mono (fun y h => Or.inr h) (fun j h => by simp only [NC]; omega) (fun b c h => Or.inl h)
    have G4 : FrameA SC NC (AC (d := d)) σ3 σ4 :=
      F4.mono (fun y h => Or.inr (by simp only [blkS] at h; omega)) (fun j h => by
        simp only [blkS] at h; simp only [NC]; omega) (fun b c h => by
        simp only [blkS] at h; simp only [AC]; omega)
    have G6 : FrameA SC NC (AC (d := d)) (σ4.setSc sDS (RealRAM.Op2.eval .add (σ4.sc 128) (σ4.sc sZ))) σ6 :=
      F6.mono (fun y h => Or.inr h) (fun j h => by simp only [NC]; omega) (fun b c h => Or.inr (Or.inl h))
    have G8 : FrameA SC NC (AC (d := d)) (σ6.setNat 10 (σ6.nat rD * σ6.nat rD)) σ8 :=
      F8.mono (fun y h => Or.inr h) (fun j h => by simp only [NC]; omega)
        (fun b c h => Or.inr (Or.inr (Or.inl h)))
    exact ((((((G1.setNat (i := 10) (Or.inr (Or.inr (Or.inl rfl))) _).trans G3).trans G4).setSc (Or.inl rfl) _).trans
      G6).setNat (i := 10) (Or.inr (Or.inr (Or.inl rfl))) _).trans G8

end AdversarialBco.Bit.Transfer.BLM
