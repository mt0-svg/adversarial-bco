/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOTriPreC
public import AdversarialBco.Unified.ProgOTriPreK
public import AdversarialBco.Unified.ProgOTriStK

@[expose] public section

/-!
# BL-O's setup: the prologue of TRI-OGD-O, `TriPreSpec`

`xpreO`: the centre block `xpreC` (the first position `tzP0 D N r₀n r₀d` in the arrays, the frame centre in `aKa`,
the gauge's centre in `aKg`, `r₀n`, `r₀d` in `100`, `101`), the constants block `xpreK` (the cells of `TriKV` and the
constants of `TriKXAt`), then `D r₀d` into `oT` and `2` into `oT + 36` (`xpreT`).
`triPreSpec_of : TriExpS Cs ks → TriPreSpec xpreO (KEv TriKX) (preCf Cs) (preKf ks) 420 48 26`.
-/

namespace AdversarialBco.Unified.ProgO.TriO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM
  AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO AdversarialBco.Unified.ProgO
open AdversarialBco.BitRAM (len)

variable {d : ℕ}

/-! ## The tail -/

/-- `oT := aKa[0] r₀d` (through the slot `120`), `oT + 36 := 2`. -/
def xpreT (L : Layout) : XCmd :=
  .seq (.prim (.frag (.nconst 16 0))) <| .seq (toX (VL.aget L 120 aKa 16)) <|
  .seq (toX (VL.sop2 L .mul 130 120 101)) (toX (VL.sop2 L .add 166 27 sZ))

set_option maxHeartbeats 2000000 in
theorem XV.preT {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hd : 1 ≤ d)
    (hNS : 172 ≤ L.NS) (hNN : 48 ≤ L.NN) (hNA : 26 ≤ L.NA) {D rd : ℤ} (hD : σ.arr aKa 0 = D)
    (h101 : σ.sc 101 = rd) (h27 : σ.sc 27 = 2) (hz : σ.sc sZ = 0) (bD : |D| < 2 ^ ℓ) (bd : |rd| < 2 ^ ℓ)
    (bDd : |D * rd| < 2 ^ ℓ) (hl : 2 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xpreT L) σ 5 (fun σ' =>
      σ'.sc 130 = ((D * rd : ℤ) : ℝ) ∧ σ'.sc 166 = 2 ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = 120 ∨ y = 130 ∨ y = 166) (fun j => j = 16) (fun _ _ => False) σ σ') := by
  have b2 : |(2 : ℤ)| < 2 ^ ℓ := by
    rw [abs_two]; calc (2 : ℤ) < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) hl
  have b0 : |(0 : ℤ)| < 2 ^ ℓ := by rw [abs_zero]; positivity
  refine XV.mono (K := 1 + (2 + (1 + 1))) ?_ le_rfl fun _ h => h
  refine XV.seq (XV.nconst hL (i := 16) (by omega) 0 (by have := hL.1; omega)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.aget hL (x := 120) (a := aKa) (i := 16) (by omega) (by simp only [aKa, aT]; omega) (by omega)
    (by esimp; unfold asz; nlinarith) (by esimp; rw [Env.setNat_arr, hD, ← Int.cast_abs]; exact_mod_cast bD))
    fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.mulI hL (x := 130) (a := 120) (b := 101) (by omega) (by omega) (by omega) (u := D) (v := rd)
    (by esimp; rw [Env.setNat_arr, hD]) (by esimp; exact h101) bD bd bDd) fun σ3 e3 => ?_
  subst e3
  refine XV.mono (XV.addI hL (x := 166) (a := 27) (b := sZ) (by omega) (by omega) (by simp only [sZ]; omega)
    (u := 2) (v := 0) (by esimp; rw [h27]; norm_num) (by esimp; rw [hz]; simp) b2 b0 (by rw [add_zero]; exact b2))
    le_rfl fun σ4 e4 => ?_
  subst e4
  refine ⟨by esimp, by esimp; norm_num, by simp, ?_⟩
  exact ((((FrameA.refl (fun y => y = 120 ∨ y = 130 ∨ y = 166) (fun j => j = 16) (fun _ _ => False) σ).setNat (i := 16) rfl _).setSc (x := 120) (Or.inl rfl) _).setSc (x := 130)
    (Or.inr (Or.inl rfl)) _).setSc (x := 166) (Or.inr (Or.inr rfl)) _


/-! ## The prologue -/

/-- **The prologue of TRI-OGD-O**: the centre block, the constants block, the tail. -/
def xpreO (L : Layout) : XCmdO := .base (.seq (xpreC L) (.seq (xpreK L) (xpreT L)))

/-- The constant of the prologue's bound from the constant `Cs` of `TriExpS`. -/
def preCf (Cs : ℕ) : ℕ := 2 ^ 1030 * (Cs + 4101) ^ 2

/-- The exponent of the prologue's bound from the exponent `ks` of `TriExpS`. -/
def preKf (ks : ℕ) : ℕ := max (2 * max ks 2) 201

/-- The magnitudes of the prologue: from `G ≤ (Cs + 4100) V^{K₂}`, every quantity the blocks bound lies below
`preCf Cs · V^{preKf ks}`. -/
theorem pre_arith {Cs ks V G d T : ℕ} (hV : 1 ≤ V) (hdV : d ≤ V) (hG : G ≤ (Cs + 4100) * V ^ max ks 2)
    (hT : T ≤ 1100 * G) :
    (V + G ≤ (Cs + 4101) * V ^ max ks 2) ∧
    (50000 * (V + G) < preCf Cs * V ^ preKf ks) ∧
    (d * 6 + 6 + 6 + d * d * 5 + 3 + 2 + d * 21 + 3 + 5 + 15 + 7 + (4 * T + 44 + (7 * (d + 10) * (1 + (4 * T + 44) + 2)
      + 2)) + (876 * G + 5280) + 28 + 5 ≤ preCf Cs * V ^ preKf ks) ∧
    (2 ^ 1010 * V ^ 201 ≤ preCf Cs * V ^ preKf ks) ∧ (2 ^ 156 * V ^ 21 ≤ preCf Cs * V ^ preKf ks) ∧
    (14 * (V * V) ≤ preCf Cs * V ^ preKf ks) := by
  set K2 := max ks 2 with hK2
  set P := V ^ K2 with hP
  set Q := V ^ preKf ks with hQ
  have hP1 : 1 ≤ P := Nat.one_le_pow _ _ hV
  have hVV : V * V ≤ P := by
    calc V * V = V ^ 2 := (sq V).symm
      _ ≤ P := Nat.pow_le_pow_right hV (le_max_right _ _)
  have hPP : P * P ≤ Q := by
    calc P * P = V ^ (2 * K2) := by rw [hP, ← pow_add, two_mul]
      _ ≤ Q := Nat.pow_le_pow_right hV (le_max_left _ _)
  have hPQ : P ≤ Q := le_trans (Nat.le_mul_of_pos_left P hP1) hPP
  have h201 : V ^ 201 ≤ Q := Nat.pow_le_pow_right hV (le_max_right _ _)
  have h21 : V ^ 21 ≤ Q := le_trans (Nat.pow_le_pow_right hV (by norm_num)) h201
  set c := Cs + 4101 with hc
  have hc1 : 4101 ≤ c := by omega
  have hB : V + G ≤ c * P := by nlinarith
  have hcc : c ≤ c * c := Nat.le_mul_of_pos_left c (by omega)
  have hccpos : 0 < c * c := Nat.mul_pos (by omega) (by omega)
  have hQcc : Q ≤ c * c * Q := Nat.le_mul_of_pos_left Q hccpos
  have hBQ : V + G ≤ c * c * Q := by
    calc V + G ≤ c * P := hB
      _ ≤ (c * c) * Q := Nat.mul_le_mul hcc hPQ
  have hM : preCf Cs * Q = 2 ^ 1030 * (c * c * Q) := by
    simp only [preCf, ← hc]; ring
  have h2 : (400000 : ℕ) ≤ 2 ^ 1030 :=
    (by norm_num : (400000 : ℕ) ≤ 2 ^ 19).trans (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  have h3 : (2 : ℕ) ^ 1010 ≤ 2 ^ 1030 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have h4 : (2 : ℕ) ^ 156 ≤ 2 ^ 1030 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  rw [hM]
  generalize (2 : ℕ) ^ 1030 = E at h2 h3 h4 ⊢
  generalize (2 : ℕ) ^ 1010 = F at h3 ⊢
  generalize (2 : ℕ) ^ 156 = H at h4 ⊢
  refine ⟨hB, ?_, ?_, ?_, ?_, ?_⟩
  · calc 50000 * (V + G) ≤ 50000 * (c * c * Q) := Nat.mul_le_mul_left _ hBQ
      _ < 400000 * (c * c * Q) := by omega
      _ ≤ E * (c * c * Q) := Nat.mul_le_mul_right _ h2
  · set B := V + G with hBdef
    have hB1 : 1 ≤ B := by omega
    have hdB : d ≤ B := by omega
    have hGB : G ≤ B := by omega
    have e1 : d * d ≤ B * B := Nat.mul_le_mul hdB hdB
    have e2 : 4 * T + 47 ≤ 4447 * B := by omega
    have e3 : d + 10 ≤ 11 * B := by omega
    have e4 : (d + 10) * (4 * T + 47) ≤ (11 * B) * (4447 * B) := Nat.mul_le_mul e3 e2
    have e5 : B ≤ B * B := Nat.le_mul_of_pos_left B hB1
    have e6 : B * B ≤ c * c * Q := by
      calc B * B ≤ (c * P) * (c * P) := Nat.mul_le_mul hB hB
        _ = (c * c) * (P * P) := by ring
        _ ≤ (c * c) * Q := Nat.mul_le_mul_left _ hPP
    have e7 : 7 * (d + 10) * (1 + (4 * T + 44) + 2) = 7 * ((d + 10) * (4 * T + 47)) := by ring
    rw [e7]
    have e8 : (11 * B) * (4447 * B) = 48917 * (B * B) := by ring
    rw [e8] at e4
    clear h3 h4
    calc _ ≤ 400000 * (B * B) := by nlinarith
      _ ≤ 400000 * (c * c * Q) := Nat.mul_le_mul_left _ e6
      _ ≤ E * (c * c * Q) := Nat.mul_le_mul_right _ h2
  · calc F * V ^ 201 ≤ E * Q := Nat.mul_le_mul h3 h201
      _ ≤ E * (c * c * Q) := Nat.mul_le_mul_left _ hQcc
  · calc H * V ^ 21 ≤ E * Q := Nat.mul_le_mul h4 h21
      _ ≤ E * (c * c * Q) := Nat.mul_le_mul_left _ hQcc
  · calc 14 * (V * V) ≤ 400000 * (c * c * Q) := by
          have : V * V ≤ c * c * Q := le_trans hVV (le_trans hPQ hQcc)
          omega
      _ ≤ E * (c * c * Q) := Nat.mul_le_mul_right _ h2

/-! ## The first position -/

/-- The denominators of the centre, `1` past `d`. -/
def adn (a : Fin d → ℚ) : ℕ → ℤ := fun j => if h : j < d then ((a ⟨j, h⟩).den : ℤ) else 1

/-- The numerators of the centre, `0` past `d`. -/
def anm (a : Fin d → ℚ) : ℕ → ℤ := fun j => if h : j < d then (a ⟨j, h⟩).num else 0

theorem adn_pos (a : Fin d → ℚ) (j : ℕ) : 0 < adn a j := by
  unfold adn; split_ifs
  · exact_mod_cast (a _).den_pos
  · norm_num

/-- The magnitudes of the first position below `2^S`, `S` the input size. -/
theorem pre_sizes (δ r0 R0 : ℚ) (a : Fin d → ℚ) :
    pdn (adn a) d ≤ 2 ^ sizeN δ r0 R0 a ∧ |r0.num| < 2 ^ sizeN δ r0 R0 a ∧
    (r0.den : ℤ) < 2 ^ sizeN δ r0 R0 a ∧
    (∀ j < d, |anm a j| * pdn (adn a) d * r0.den < 2 ^ sizeN δ r0 R0 a) ∧
    (∀ j < d, |anm a j| * pdn (adn a) d ≤ 2 ^ sizeN δ r0 R0 a) ∧
    |pdn (adn a) d * r0.num| < 2 ^ sizeN δ r0 R0 a ∧ |pdn (adn a) d * r0.den| < 2 ^ sizeN δ r0 R0 a := by
  have hS : len δ.num + len (δ.den : ℤ) + len r0.num + len (r0.den : ℤ) + len R0.num + len (R0.den : ℤ) +
      ∑ i, (len (a i).num + len ((a i).den : ℤ)) = sizeN δ r0 R0 a := rfl
  set S := sizeN δ r0 R0 a with hSdef
  set SD := ∑ i : Fin d, len ((a i).den : ℤ) with hSD
  rw [Finset.sum_add_distrib] at hS
  have dn0 := adn_pos a
  have hPD : pdn (adn a) d ≤ 2 ^ SD := by
    have h := pdn_le_pow (l := fun j => if h : j < d then len ((a ⟨j, h⟩).den : ℤ) else 0) dn0 (fun j => by
      simp only [adn]; split_ifs with h
      · exact (le_abs_self _).trans (abs_lt_len _).le
      · simp) d
    refine h.trans (pow_le_pow_right₀ (by norm_num) (le_of_eq ?_))
    rw [hSD, ← Fin.sum_univ_eq_sum_range (fun j => if h : j < d then len ((a ⟨j, h⟩).den : ℤ) else 0) d]
    exact Finset.sum_congr rfl fun i _ => by rw [dif_pos i.2]
  have hDpos := pdn_pos dn0 d
  have pS : ∀ m, m ≤ S → (2 : ℤ) ^ m ≤ 2 ^ S := fun m hm => pow_le_pow_right₀ (by norm_num) hm
  have hrn : |r0.num| < 2 ^ len r0.num := abs_lt_len _
  have hrd0 : (0 : ℤ) < r0.den := by exact_mod_cast r0.den_pos
  have hrd : (r0.den : ℤ) < 2 ^ len (r0.den : ℤ) := (le_abs_self _).trans_lt (abs_lt_len _)
  have hP2 : (0 : ℤ) < 2 ^ SD := by positivity
  have hNj : ∀ j < d, ∃ m, |anm a j| < 2 ^ m ∧ m + SD + len (r0.den : ℤ) ≤ S := fun j hj => by
    refine ⟨len (a ⟨j, hj⟩).num, by simp only [anm, dif_pos hj]; exact abs_lt_len _, ?_⟩
    have := Finset.single_le_sum (f := fun i : Fin d => len (a i).num) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ ⟨j, hj⟩)
    omega
  refine ⟨hPD.trans (pS _ (by omega)), hrn.trans_le (pS _ (by omega)), hrd.trans_le (pS _ (by omega)),
    fun j hj => ?_, fun j hj => ?_, ?_, ?_⟩
  · obtain ⟨m, hm, hmS⟩ := hNj j hj
    calc |anm a j| * pdn (adn a) d * r0.den < 2 ^ m * pdn (adn a) d * r0.den :=
          mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hm hDpos) hrd0
      _ ≤ 2 ^ m * 2 ^ SD * 2 ^ len (r0.den : ℤ) := by gcongr
      _ = 2 ^ (m + SD + len (r0.den : ℤ)) := by rw [pow_add, pow_add]
      _ ≤ 2 ^ S := pS _ hmS
  · obtain ⟨m, hm, hmS⟩ := hNj j hj
    calc |anm a j| * pdn (adn a) d ≤ 2 ^ m * 2 ^ SD := mul_le_mul hm.le hPD hDpos.le (by positivity)
      _ = 2 ^ (m + SD) := by rw [pow_add]
      _ ≤ 2 ^ S := pS _ (by omega)
  · rw [abs_mul, abs_of_pos hDpos]
    calc pdn (adn a) d * |r0.num| ≤ 2 ^ SD * |r0.num| := mul_le_mul_of_nonneg_right hPD (abs_nonneg _)
      _ < 2 ^ SD * 2 ^ len r0.num := mul_lt_mul_of_pos_left hrn hP2
      _ = 2 ^ (SD + len r0.num) := by rw [pow_add]
      _ ≤ 2 ^ S := pS _ (by omega)
  · rw [abs_mul, abs_of_pos hDpos, abs_of_pos hrd0]
    calc pdn (adn a) d * r0.den ≤ 2 ^ SD * r0.den := mul_le_mul_of_nonneg_right hPD hrd0.le
      _ < 2 ^ SD * 2 ^ len (r0.den : ℤ) := mul_lt_mul_of_pos_left hrd hP2
      _ = 2 ^ (SD + len (r0.den : ℤ)) := by rw [pow_add]
      _ ≤ 2 ^ S := pS _ (by omega)

/-- The first position is a representation of the input. -/
theorem pre_rep {n : ℕ} {δ r0 R0 : ℚ} (a : Fin d → ℚ) (hr0 : 0 < r0) :
    P0OK d n δ r0 R0 a (pdn (adn a) d) (fun i => cnum (anm a) (adn a) (pdn (adn a) d) i) r0.num r0.den := by
  obtain ⟨s1, s2, s3, -, s5, -, -⟩ := pre_sizes δ r0 R0 a
  have dn0 := adn_pos a
  have hDpos := pdn_pos dn0 d
  have hSW : (2 : ℤ) ^ sizeN δ r0 R0 a < 2 ^ wU d n δ r0 R0 a :=
    pow_lt_pow_right₀ (by norm_num) (by unfold wU; omega)
  refine ⟨hDpos, s1.trans_lt hSW, fun i => ?_, fun i => ?_, Rat.num_pos.2 hr0,
    (le_abs_self _).trans_lt (s2.trans hSW), by exact_mod_cast r0.den_pos, s3.trans hSW, ?_⟩
  · have hq0 : 0 ≤ pdn (adn a) d / adn a i := Int.ediv_nonneg hDpos.le (dn0 i).le
    have hq : pdn (adn a) d / adn a i ≤ pdn (adn a) d := Int.ediv_le_self _ hDpos.le
    show |cnum (anm a) (adn a) (pdn (adn a) d) i| < _
    unfold cnum
    rw [abs_mul, abs_of_nonneg hq0]
    calc |anm a i| * (pdn (adn a) d / adn a i) ≤ |anm a i| * pdn (adn a) d :=
          mul_le_mul_of_nonneg_left hq (abs_nonneg _)
      _ ≤ 2 ^ sizeN δ r0 R0 a := s5 i i.2
      _ < _ := hSW
  · obtain ⟨q, hq⟩ := pdn_dvd (adn a) i.2
    have hq0 : 0 < q := pos_of_mul_pos_right (hq ▸ hDpos) (dn0 i).le
    have hdq : pdn (adn a) d / adn a i = q := by rw [hq, Int.mul_ediv_cancel_left _ (dn0 i).ne']
    have hnmj : anm a i = (a i).num := by simp only [anm, dif_pos i.2, Fin.eta]
    have hdnj : adn a i = (a i).den := by simp only [adn, dif_pos i.2, Fin.eta]
    show ((cnum (anm a) (adn a) (pdn (adn a) d) i : ℤ) : ℚ) / (pdn (adn a) d : ℤ) = a i
    unfold cnum
    rw [hdq, hq, hnmj, hdnj]
    push_cast
    rw [mul_div_mul_right _ _ (by exact_mod_cast hq0.ne' : (q : ℚ) ≠ 0)]
    exact Rat.num_div_den (a i)
  · push_cast; exact Rat.num_div_den r0

/-! ## The contract -/

set_option maxHeartbeats 16000000 in
/-- **The prologue of TRI-OGD-O** (`TriPreSpec`), from the exponents `TriExpS Cs ks` of the constants. -/
theorem triPreSpec_of {Cs ks : ℕ} (hS : TriExpS Cs ks) :
    TriPreSpec xpreO (KEv TriKX) (preCf Cs) (preKf ks) 420 48 26 := by
  intro d L w n δ r0 R0 a ℓa ℓ σ hI hL hR hB hk hℓ hℓa
  obtain ⟨hNS, hNN, hNA⟩ := hR
  obtain ⟨hD, h1, hz, hn, h26, h27, h28⟩ := hB
  have hd := hI.hd
  have hr : 0 < r0 ∧ r0 ≤ R0 := ⟨hI.hr0, hI.hR0⟩
  -- the magnitudes
  have hSW := hS d n δ r0 R0 a hI
  have hK2 := stK_le a hI
  have hkd : kDel δ ≤ len (δ.den : ℤ) := (kDel_le_size hI.hδ0).trans (len_natCast _).ge
  have hTc := tcG_one_le hd
  have hsz : len δ.num + len (δ.den : ℤ) + len r0.num + len (r0.den : ℤ) + len R0.num + len (R0.den : ℤ) +
      ∑ i, (len (a i).num + len ((a i).den : ℤ)) = sizeN δ r0 R0 a := rfl
  have hGe : poG d n (kDel δ) r0 R0 = (triLa (triSQ d) + triLh (triSQ d) + triJaQ d + triBvQ d + 2 * tzP d +
      tGcT d (ellO d n δ r0 R0) + stE d + triETauQ d + stJ d + stEu d + triSQ d) + stK d r0 R0 +
      (kDel δ + d + n.size + len r0.num + len (r0.den : ℤ) + len R0.num + len (R0.den : ℤ) + 4) := by
    unfold poG ellO; ring
  obtain ⟨s1, s2, s3, s4, -, s6, s7⟩ := pre_sizes δ r0 R0 a
  have hWe : WT d n δ r0 R0 a = d + n.size + sizeN δ r0 R0 a + 1 := rfl
  set W := WT d n δ r0 R0 a with hWdef
  set V := W + 1 with hVdef
  have hV1 : 1 ≤ V := by omega
  have hdV : d ≤ V := by omega
  have hG : poG d n (kDel δ) r0 R0 ≤ (Cs + 4100) * V ^ max ks 2 := by
    rw [hGe]
    have e1 : Cs * V ^ ks ≤ Cs * V ^ max ks 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hV1 (le_max_left _ _))
    have e2 : V ^ 2 ≤ V ^ max ks 2 := Nat.pow_le_pow_right hV1 (le_max_right _ _)
    have e3 : V ≤ V ^ 2 := by rw [sq]; exact Nat.le_mul_of_pos_left V hV1
    have hrest : kDel δ + d + n.size + len r0.num + len (r0.den : ℤ) + len R0.num + len (R0.den : ℤ) + 4 ≤ V + 2 := by
      omega
    have e4 : (Cs + 4100) * V ^ max ks 2 = Cs * V ^ max ks 2 + 4100 * V ^ max ks 2 := by ring
    rw [e4]
    linarith
  have hT : tcG d 1 ≤ 1100 * poG d n (kDel δ) r0 R0 := by rw [hGe]; linarith
  obtain ⟨-, A2, A3, -, -, A6⟩ := pre_arith (Cs := Cs) (ks := ks) hV1 hdV hG hT
  have hNa : 2 ^ triNeTQ d (ellO d n δ r0 R0) < 2 ^ ℓa := by
    have hNe := (triExpO d n δ r0 R0 a hI).2.1
    have A4 := (pre_arith (Cs := Cs) (ks := ks) hV1 hdV hG hT).2.2.2.1
    exact (hNe.trans A4).trans_lt hℓa
  have hBa : triBgQ d < 2 ^ ℓa := by
    have hBg : triBgQ d ≤ 2 ^ 156 * d ^ 21 :=
      calc triBgQ d = 4 * triKgQ d := rfl
        _ ≤ 4 * (2 ^ 154 * d ^ 21) := Nat.mul_le_mul_left _ (triKgQ_le hd)
        _ = 2 ^ 156 * d ^ 21 := by ring
    have A5 := (pre_arith (Cs := Cs) (ks := ks) hV1 hdV hG hT).2.2.2.2.1
    exact (hBg.trans ((Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hdV 21)).trans A5)).trans_lt hℓa
  set M := preCf Cs * V ^ preKf ks with hMdef
  have hdd : d * d ≤ V * V := Nat.mul_le_mul hdV hdV
  have hVV : V ≤ V * V := Nat.le_mul_of_pos_left V hV1
  have hSl : sizeN δ r0 R0 a < ℓ := by omega
  have hSℓ : (2 : ℤ) ^ sizeN δ r0 R0 a < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) hSl
  have hU : preCK d + (preKK d n (kDel δ) r0 R0 + 5) ≤ M := by
    simp only [preCK, preKK, srchK, ev]; linarith
  -- the inputs
  set X := (ctxU w n δ r0 R0 a).X with hX
  have hoff : X.off = 8 + 2 * d := rfl
  have i4 : X.inp 4 = r0.num := rfl
  have i5 : X.inp 5 = r0.den := rfl
  have i6 : X.inp 6 = R0.num := rfl
  have i7 : X.inp 7 = R0.den := rfl
  have dn0 := adn_pos a
  have iD : ∀ j < d, X.inp (9 + 2 * j) = adn a j := fun j hj => by
    simp only [adn, dif_pos hj]; exact inputU_den (n := n) (δ := δ) (r0 := r0) (R0 := R0) (a := a) ⟨j, hj⟩
  have iN : ∀ j < d, X.inp (8 + 2 * j) = anm a j := fun j hj => by
    simp only [anm, dif_pos hj]; exact inputU_num (n := n) (δ := δ) (r0 := r0) (R0 := R0) (a := a) ⟨j, hj⟩
  have rep := pre_rep (n := n) (δ := δ) (R0 := R0) a hI.hr0
  -- the run
  unfold xpreO
  refine XVO.ofX ?_
  refine XV.mono (K := preCK d + (preKK d n (kDel δ) r0 R0 + 5)) ?_ hU fun _ h => h
  refine XV.seq (XV.preC (X := X) hL hd (by omega) (by omega) (by omega) dn0 iD iN hoff.ge i4 i5
    (by exact_mod_cast r0.den_pos) (s3.trans hSℓ) (s2.trans hSℓ) (s1.trans_lt hSℓ) (fun j hj => (s4 j hj).trans hSℓ)
    (s6.trans hSℓ) (by omega) (by omega) hD h1 hz h26)
    fun σ1 ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, d1, F1⟩ => ?_
  have hD1 : σ1.nat rD = d := (F1.1 rD (by simp only [NPC, rD]; omega)).trans hD
  have hz1 : σ1.sc sZ = 0 := (F1.2.1 sZ (by simp only [SPC, sZ]; omega)).trans hz
  have hn1 : σ1.sc sN = n := (F1.2.1 sN (by simp only [SPC, sN]; omega)).trans hn
  have hk1 : σ1.sc sKd = ((kDel δ : ℕ) : ℤ) := by
    rw [F1.2.1 sKd (by simp only [SPC, sKd]; omega), hk, Int.cast_natCast]
  have h271 : σ1.sc 27 = 2 := (F1.2.1 27 (by simp only [SPC]; omega)).trans h27
  refine XV.seq (XV.preK (X := X) hL hNS hNN hd hr hD1 hn1 hz1 hk1 c8 c9 i6 i7 (by omega)
    (by omega) (by simp only [ev, tcT]; omega) (by simp only [ev, tcT]; omega) (by simp only [ev, poT]; omega)
    (by simp only [ev, poT]; omega) hNa hBa)
    fun σ2 ⟨k1, k2, k3, k4, d2, F2⟩ => ?_
  have hD2 : σ2.arr aKa 0 = ((pdn (adn a) d : ℤ) : ℝ) := (F2.2.2.1 aKa 0 id).trans c1
  have h1012 : σ2.sc 101 = ((r0.den : ℤ) : ℝ) := (F2.2.1 101 (by norm_num)).trans c9
  have h272 : σ2.sc 27 = 2 := (F2.2.1 27 (by norm_num)).trans h271
  have hz2 : σ2.sc sZ = 0 := (F2.2.1 sZ (by norm_num [sZ])).trans hz1
  have kx2 : TriKXAt d n δ r0 R0 a (pdn (adn a) d) (fun i => cnum (anm a) (adn a) (pdn (adn a) d) i) r0.num
      r0.den σ2 :=
    ⟨rep, hD2, fun i => by rw [F2.2.2.1 _ _ id, c2 i i.2], by rw [F2.2.1 100 (by norm_num), c8],
      h1012, by rw [F2.2.2.1 _ _ id, c3], fun i => by rw [F2.2.2.1 _ _ id, c4 i i.2], k2.cE, k2.cL1, k2.cSh,
      k2.cA, k2.cB, k2.nJ, k2.hn, k2.hd, k2.nj, k2.c2j, k2.nk, k2.c2k, k2.c2K, k2.bb⟩
  refine XV.mono (XV.preT (X := X) hL hd (by omega) (by omega) (by omega) hD2 h1012 h272 hz2
    (by rw [abs_of_pos (pdn_pos dn0 d)]; exact s1.trans_lt hSℓ)
    (by rw [abs_of_pos (by exact_mod_cast r0.den_pos : (0 : ℤ) < r0.den)]; exact s3.trans hSℓ)
    (s7.trans hSℓ) (by omega)) le_rfl fun σ3 ⟨t1, t2, d3, F3⟩ => ?_
  refine ⟨⟨k1.frame F3 ?_ ?_, ⟨_, _, _, _, kx2.frame F3 ?_ ?_ fun _ => ⟨id, id⟩⟩⟩, ?_, ?_,
    ⟨_, _, _, _, rep, ?_⟩, d3.trans (d2.trans d1), ?_⟩
  · rintro k hk (h | h | h) <;> simp only [oT] at h <;> omega
  · norm_num [rD, rT]
  · rintro y h1 h2 (h | h | h) <;> omega
  · norm_num [rNJ, rNj, rNk, rT]
  · rw [F3.1 _ (by norm_num [rT]), k3]
  · rw [F3.1 _ (by norm_num [rT]), k4]
  · refine ⟨fun l => ?_, fun i l => ?_, ?_, ?_⟩
    · rw [F3.2.2.1 _ _ id, F2.2.2.1 _ _ id, c5 l l.2]; rfl
    · rw [F3.2.2.1 _ _ id, F2.2.2.1 _ _ id]
      by_cases hil : i = l
      · subst hil; rw [c6 i i.2]
        simp only [tzP0, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      · have hb : d * (i : ℕ) + l < d * d :=
          calc d * (i : ℕ) + l < d * i + d := by have := l.2; omega
            _ = d * (i + 1) := by ring
            _ ≤ d * d := Nat.mul_le_mul_left _ i.2
        rw [c7 _ hb fun i' hi' => diag_off l.2 hi' fun h => hil (Fin.ext h)]
        simp only [tzP0, Matrix.smul_apply, Matrix.one_apply_ne hil, smul_eq_mul, mul_zero, Int.cast_zero]
    · show σ3.sc 130 = _; rw [t1]; rfl
    · show σ3.sc 166 = _; rw [t2]; norm_num
  · refine ((F1.mono (S' := TriS) (N' := TriN) (Ar' := ATri d) ?_ ?_ ?_).trans
      (F2.mono (S' := TriS) (N' := TriN) (Ar' := ATri d) ?_ ?_ ?_)).trans
      (F3.mono (S' := TriS) (N' := TriN) (Ar' := ATri d) ?_ ?_ ?_)
    · intro y hy; simp only [SPC] at hy; right; omega
    · intro j hj; simp only [NPC] at hj; show 8 ≤ j; omega
    · intro b k hb; right; right; rcases hb with h | h | h | h <;> simp only [h] <;> norm_num
    · intro y hy; right; omega
    · intro j hj; exact hj
    · intro b k hb; exact hb.elim
    · intro y hy; right; omega
    · intro j hj; show 8 ≤ j; omega
    · intro b k hb; exact hb.elim

end AdversarialBco.Unified.ProgO.TriO
