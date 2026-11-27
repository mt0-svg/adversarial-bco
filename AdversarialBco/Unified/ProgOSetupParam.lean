/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PrmKLink
public import AdversarialBco.Unified.ProgOSetupCoins
public import AdversarialBco.Bit.Transfer.XFrameE0

@[expose] public section

/-!
# BL-O's setup: PARAM at `k_δ`

`xparO`: `N_e = NeO d n k_δ = 1966080 · 2^{k_δ} d³ n⁴` into the input slot `4` (`xneO`, from `k_δ` in `sKd`), the
straight line `parStK` (Unified/PrmKV.lean), v2.1's copies `prmCopies` into BL's slots `4, ..., 21`, the registers
`rP`, `rPF`, `rNb`, `rB`. `paramSpecO : ParamSpecO xparO 4200000 1 172 48 0`, from `parGK_le` (PARAM's magnitude is
at most `6000 (k_δ + size d + size n + 1)`), `pvK_abs` and the links of Unified/PrmKLink.lean.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Unified.PrmK
open AdversarialBco.Unified.BudK (parK)
open AdversarialBco.BitRAM (len)

variable {d : ℕ}

/-! ## The magnitudes of PARAM at `k_δ` -/

/-- Every value of the line is at most `2^{75 G + 343}`, `G = parGK d n e`. -/
theorem pvK_abs {n e : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) {k : ℕ} (hk : k < 93) :
    |pvK d n e k| ≤ 2 ^ (75 * parGK d n e + 343) := by
  have h := SL.val_bound parStK 30 (parIK d n e) [0, 3, 4] parIn parEt parT 44 (parGK d n e)
    (SL.chk_get parStK_chk).2 (par_semK hd hn) (parIn_okK hd hn) k (by rw [parStK_length]; exact hk)
  have hle : ∀ k < 93, (parEt k).1 ≤ 75 ∧ (parEt k).2 ≤ 343 := by decide
  obtain ⟨h1, h2⟩ := hle k hk
  refine h.trans (pow_le_pow_right₀ (by norm_num) ?_)
  unfold ev
  nlinarith

/-- **PARAM's magnitude at `k_δ = e`** is linear in `e` and the sizes of `d`, `n`. -/
theorem parGK_le (d n e : ℕ) : parGK d n e ≤ 6000 * (e + d.size + n.size + 1) := by
  have hd2 : d < 2 ^ d.size := Nat.lt_size_self d
  have hn2 : n < 2 ^ n.size := Nat.lt_size_self n
  have hle : (NeO d n e).size ≤ 21 + e + 3 * d.size + 4 * n.size := by
    rw [Nat.size_le]
    unfold NeO
    calc 15 * 2 ^ (17 + e) * d ^ 3 * n ^ 4 = 15 * 2 ^ (17 + e) * (d ^ 3 * n ^ 4) := by ring
      _ ≤ 15 * 2 ^ (17 + e) * ((2 ^ d.size) ^ 3 * (2 ^ n.size) ^ 4) := by gcongr
      _ < 16 * 2 ^ (17 + e) * ((2 ^ d.size) ^ 3 * (2 ^ n.size) ^ 4) :=
          Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right (by norm_num) (by positivity)) (by positivity)
      _ = 2 ^ (21 + e + 3 * d.size + 4 * n.size) := by ring
  have hls : (NeO d n e).size.size ≤ (NeO d n e).size := Nat.size_le.2 Nat.lt_two_pow_self
  have hnd : (n * (d + 2)).size ≤ n.size + (d.size + 2) := by
    rw [Nat.size_le, pow_add]
    have : d + 2 < 2 ^ (d.size + 2) := by
      have h1 : 1 ≤ 2 ^ d.size := Nat.one_le_two_pow
      rw [pow_add]; omega
    exact mul_lt_mul'' hn2 this (Nat.zero_le _) (Nat.zero_le _)
  have hq : (parK d n e).q = 10 * (NeO d n e).size + 16 * d.size + 160 + 2 * (NeO d n e).size.size + 24 := rfl
  have hpF : (parK d n e).pF = 10 * (NeO d n e).size + 16 * d.size + 160 + 2 * (NeO d n e).size + 4 * d.size + 40 :=
    rfl
  have hB : (parK d n e).B = 2 * (10 * (NeO d n e).size + 16 * d.size + 160 + (n * (d + 2)).size + 2) := rfl
  have hBs : (parK d n e).B.size ≤ (parK d n e).B := Nat.size_le.2 Nat.lt_two_pow_self
  unfold parGK Bit.gsm_prec
  rw [hq, hpF] at *
  omega

/-! ## `N_e` into the input slot `4` -/

/-- `8 := k_δ`, `5 := 2^{k_δ}`, `6 := 1966080`, `4 := 1966080 · 2^{k_δ} d³ n⁴` (`d` in slot `0`, `n` in `sN`). -/
def xneO (L : Layout) : XCmd :=
  .seq (xrtoN L 8 sKd) (.seq (xpow2 L 5 9 8 rOne) (.seq (toX (VL.sconst L 6 1966080))
  (.seq (toX (VL.sop2 L .mul 4 6 5)) (.seq (toX (VL.sop2 L .mul 4 4 0)) (.seq (toX (VL.sop2 L .mul 4 4 0))
  (.seq (toX (VL.sop2 L .mul 4 4 0)) (.seq (toX (VL.sop2 L .mul 4 4 sN)) (.seq (toX (VL.sop2 L .mul 4 4 sN))
  (.seq (toX (VL.sop2 L .mul 4 4 sN)) (toX (VL.sop2 L .mul 4 4 sN)))))))))))

/-- The cells `xneO` changes. -/
def SNe (y : ℕ) : Prop := 4 ≤ y ∧ y ≤ 6

set_option maxHeartbeats 2000000 in
theorem XV.neO {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hNS : 172 ≤ L.NS)
    (hNN : 48 ≤ L.NN) {n k : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (h0 : σ.sc 0 = d) (h3 : σ.sc sN = n)
    (hk : σ.sc sKd = k) (h1 : σ.nat rOne = 1) (hNe : (NeO d n k : ℤ) < 2 ^ ℓ) (hkl : k < ℓ) (hka : k < 2 ^ ℓa)
    (h6 : (1966080 : ℤ) < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xneO L) σ (4 * k + 14) (fun σ' => σ'.sc 4 = (NeO d n k : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA SNe (fun j => j = 8 ∨ j = 9) (fun _ _ => False) σ σ') := by
  set A : ℤ := 1966080 * 2 ^ k with hA
  have hA1 : 1 ≤ A := by rw [hA]; have : (1 : ℤ) ≤ 2 ^ k := one_le_pow₀ (by norm_num); linarith
  have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have m : ∀ x v : ℤ, 1 ≤ x → 1 ≤ v → 1 ≤ x * v ∧ x ≤ x * v := fun x v hx hv =>
    ⟨one_le_mul_of_one_le_of_one_le hx hv, le_mul_of_one_le_right (by linarith) hv⟩
  obtain ⟨p2, q2⟩ := m _ _ hA1 hd1
  obtain ⟨p3, q3⟩ := m _ _ p2 hd1
  obtain ⟨p4, q4⟩ := m _ _ p3 hd1
  obtain ⟨p5, q5⟩ := m _ _ p4 hn1
  obtain ⟨p6, q6⟩ := m _ _ p5 hn1
  obtain ⟨p7, q7⟩ := m _ _ p6 hn1
  obtain ⟨p8, q8⟩ := m _ _ p7 hn1
  have eNe : (NeO d n k : ℤ) = A * d * d * d * n * n * n * n := by rw [hA]; unfold NeO; push_cast; ring
  have hN : A * d * d * d * n * n * n * n < 2 ^ ℓ := eNe ▸ hNe
  have ab : ∀ x : ℤ, 1 ≤ x → x ≤ A * d * d * d * n * n * n * n → |x| < 2 ^ ℓ := fun x h0 h1 => by
    rw [abs_of_nonneg (by linarith)]; linarith
  have hdN : (d : ℤ) ≤ A * d * d * d * n * n * n * n := by
    have : (d : ℤ) ≤ A * d := by nlinarith
    linarith
  have hnN : (n : ℤ) ≤ A * d * d * d * n * n * n * n := by
    have : (n : ℤ) ≤ A * d * d * d * n := by nlinarith
    linarith
  have hkl2 : (2 : ℤ) ^ k < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) hkl
  refine XV.mono (K := 1 + ((4 * k + 4) + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))))) ?_ (by omega)
    fun _ h => h
  refine XV.seq (XV.rtoNat hL (i := 8) (x := sKd) (v := k) (by omega) (by simp only [sKd]; omega)
    (by rw [hk]; push_cast; rfl) hka (lt_of_lt_of_le hkl (Nat.lt_two_pow_self).le)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.pow2A hL (p := 5) (i := 9) (n := 8) (one := rOne) (by omega) (by omega) (by omega)
    (by simp only [rOne]; omega) (by decide) (by decide) (W := k) (by simp) (by simp [h1]) hka hkl)
    fun σ2 ⟨c2, d2, F2⟩ => ?_
  refine XV.seq (XV.constI hL (x := 6) (by omega) 1966080 (by rw [abs_of_pos (by norm_num)]; exact h6))
    fun σ3 e3 => ?_
  subst e3
  have s0 : ∀ τ : Env d, FrameA SNe (fun j => j = 8 ∨ j = 9) (fun _ _ => False) σ τ → τ.sc 0 = d :=
    fun τ F => (F.2.1 0 (by simp only [SNe]; omega)).trans h0
  have sn : ∀ τ : Env d, FrameA SNe (fun j => j = 8 ∨ j = 9) (fun _ _ => False) σ τ → τ.sc sN = n :=
    fun τ F => (F.2.1 sN (by simp only [SNe, sN]; omega)).trans h3
  have F3 : FrameA SNe (fun j => j = 8 ∨ j = 9) (fun _ _ => False) σ (σ2.setSc 6 ((1966080 : ℤ) : ℝ)) :=
    ((((FrameA.refl _ _ _ σ).setNat (i := 8) (Or.inl rfl) _).trans
      (F2.mono (fun y h => ⟨by omega, by omega⟩) (fun j h => Or.inr h) (fun _ _ h => h))).setSc
      (x := 6) ⟨by omega, le_rfl⟩ _)
  refine XV.seq (XV.mulIA hL (x := 4) (a := 6) (b := 5) (by omega) (by omega) (by omega) (u := 1966080)
    (v := 2 ^ k) (by simp) (by simp [c2]) (by rw [abs_of_pos (by norm_num)]; exact h6)
    (by rw [abs_of_pos (by positivity)]; exact hkl2) (ab _ hA1 (by linarith))) fun σ4 ⟨c4, d4, F4⟩ => ?_
  have F4' := F3.trans (F4.mono (fun y h => ⟨by omega, by omega⟩) (fun j h => h.elim) (fun _ _ h => h))
  refine XV.seq (XV.mulIA hL (x := 4) (a := 4) (b := 0) (by omega) (by omega) (by omega) (u := A) (v := d)
    c4 (by rw [s0 _ F4']; simp) (ab _ hA1 (by linarith)) (ab _ hd1 hdN) (ab _ p2 (by linarith)))
    fun σ5 ⟨c5, d5, F5⟩ => ?_
  have F5' := F4'.trans (F5.mono (fun y h => ⟨by omega, by omega⟩) (fun j h => h.elim) (fun _ _ h => h))
  refine XV.seq (XV.mulIA hL (x := 4) (a := 4) (b := 0) (by omega) (by omega) (by omega) (u := A * d) (v := d)
    c5 (by rw [s0 _ F5']; simp) (ab _ p2 (by linarith)) (ab _ hd1 hdN) (ab _ p3 (by linarith)))
    fun σ6 ⟨c6, d6, F6⟩ => ?_
  have F6' := F5'.trans (F6.mono (fun y h => ⟨by omega, by omega⟩) (fun j h => h.elim) (fun _ _ h => h))
  refine XV.seq (XV.mulIA hL (x := 4) (a := 4) (b := 0) (by omega) (by omega) (by omega) (u := A * d * d)
    (v := d) c6 (by rw [s0 _ F6']; simp) (ab _ p3 (by linarith)) (ab _ hd1 hdN) (ab _ p4 (by linarith)))
    fun σ7 ⟨c7, d7, F7⟩ => ?_
  have F7' := F6'.trans (F7.mono (fun y h => ⟨by omega, by omega⟩) (fun j h => h.elim) (fun _ _ h => h))
  refine XV.seq (XV.mulIA hL (x := 4) (a := 4) (b := sN) (by omega) (by omega) (by simp only [sN]; omega)
    (u := A * d * d * d) (v := n) c7 (by rw [sn _ F7']; simp) (ab _ p4 (by linarith)) (ab _ hn1 hnN)
    (ab _ p5 (by linarith))) fun σ8 ⟨c8, d8, F8⟩ => ?_
  have F8' := F7'.trans (F8.mono (fun y h => ⟨by omega, by omega⟩) (fun j h => h.elim) (fun _ _ h => h))
  refine XV.seq (XV.mulIA hL (x := 4) (a := 4) (b := sN) (by omega) (by omega) (by simp only [sN]; omega)
    (u := A * d * d * d * n) (v := n) c8 (by rw [sn _ F8']; simp) (ab _ p5 (by linarith)) (ab _ hn1 hnN)
    (ab _ p6 (by linarith))) fun σ9 ⟨c9, d9, F9⟩ => ?_
  have F9' := F8'.trans (F9.mono (fun y h => ⟨by omega, by omega⟩) (fun j h => h.elim) (fun _ _ h => h))
  refine XV.seq (XV.mulIA hL (x := 4) (a := 4) (b := sN) (by omega) (by omega) (by simp only [sN]; omega)
    (u := A * d * d * d * n * n) (v := n) c9 (by rw [sn _ F9']; simp) (ab _ p6 (by linarith)) (ab _ hn1 hnN)
    (ab _ p7 (by linarith))) fun σ10 ⟨c10, d10, F10⟩ => ?_
  have F10' := F9'.trans (F10.mono (fun y h => ⟨by omega, by omega⟩) (fun j h => h.elim) (fun _ _ h => h))
  refine XV.mono (XV.mulIA hL (x := 4) (a := 4) (b := sN) (by omega) (by omega) (by simp only [sN]; omega)
    (u := A * d * d * d * n * n * n) (v := n) c10 (by rw [sn _ F10']; simp) (ab _ p7 (by linarith))
    (ab _ hn1 hnN) (ab _ p8 le_rfl)) le_rfl fun σ11 ⟨c11, d11, F11⟩ => ?_
  refine ⟨by rw [c11, ← eNe]; push_cast; rfl, by rw [d11, d10, d9, d8, d7, d6, d5, d4, Env.setSc_draws, d2]; rfl,
    F10'.trans (F11.mono (fun y h => ⟨by omega, by omega⟩) (fun j h => h.elim) (fun _ _ h => h))⟩

/-! ## PARAM at `k_δ` -/

/-- **PARAM of BL-O**: `N_e` into slot `4`, the line, the copies into BL's slots, the registers `rP, rPF, rNb, rB`. -/
def xparO (L : Layout) : XCmdO :=
  .base (.seq (xneO L) (.seq (SL.code L parC parStK) (.seq (xcopyS L sMode prmCopies)
    (.seq (xrtoN L rP 53) (.seq (xrtoN L rPF 57) (.seq (xrtoN L rNb 122) (xrtoN L rB 60)))))))

set_option maxHeartbeats 8000000 in
/-- **PARAM at `k_δ` on the machine.** -/
theorem paramSpecO : ParamSpecO xparO 4200000 1 172 48 0 := by
  intro d L w n δ r0 R0 a ℓa ℓ σ hI hL hR hrD hrOne h0 hMode hN h26 h27 h28 hKd hℓ hℓa
  obtain ⟨hNS, hNN, -⟩ := hR
  simp only [pow_one] at hℓ hℓa ⊢
  refine XVO.ofX ?_
  have hd := hI.hd
  have hn := hI.hn
  have hk := kDel_le_size hI.hδ0
  have hS : len (δ.den : ℤ) ≤ sizeN δ r0 R0 a := by unfold sizeN; omega
  rw [len_natCast δ.den] at hS
  have hW : wU d n δ r0 R0 a = d + n.size + sizeN δ r0 R0 a + 1 := rfl
  have hds : d.size ≤ d := Nat.size_le.2 Nat.lt_two_pow_self
  have hGb := parGK_le d n (kDel δ)
  have hGe := parG_geK (d := d) (n := n) (e := kDel δ)
  have hNeG := NeO_le_GK (d := d) (n := n) (e := kDel δ)
  have pvA : ∀ k < 93, |pvK d n (kDel δ) k| ≤ 2 ^ (75 * parGK d n (kDel δ) + 343) := fun k hk => pvK_abs hd hn hk
  have hP23 := pvK_23 d n (kDel δ)
  have hP27 := pvK_27 d n (kDel δ)
  have hP30 := pvK_30 d n (kDel δ)
  have hP92 := pvK_92 (d := d) (n := n) (e := kDel δ)
  set W := wU d n δ r0 R0 a with hWdef
  set e := kDel δ with hedef
  set G := parGK d n e with hGdef
  have hGW : G ≤ 6000 * W := by omega
  have hBG : (parK d n e).B ≤ G := by unfold Bit.gsm_prec at hGe; omega
  clear_value W G e
  -- the magnitudes
  have hTl : 75 * G + 343 < ℓ := by omega
  have hTa : 75 * G + 343 < 2 ^ ℓa := by omega
  have hel : e < ℓ := by omega
  have hea : e < 2 ^ ℓa := by omega
  have h2G : 2 ^ G < 2 ^ ℓ := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hNeZ : (NeO d n e : ℤ) < 2 ^ ℓ := by exact_mod_cast hNeG.trans_lt h2G
  have h6 : (1966080 : ℤ) < 2 ^ ℓ :=
    lt_of_lt_of_le (by norm_num : (1966080 : ℤ) < 2 ^ 21) (pow_le_pow_right₀ (by norm_num) (by omega))
  have h2ℓ : (2 : ℤ) ^ (75 * G + 343) < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) hTl
  have hGs : 75 * G + 343 ≤ 4200000 * (W + 1) := by omega
  have hK : (4 * e + 14) + ((696 * G + 3177) + (18 + (1 + (1 + (1 + 1))))) ≤ 4200000 * (W + 1) := by
    have g1 : 696 * G ≤ 696 * (6000 * W) := Nat.mul_le_mul_left _ hGW
    have g2 : e ≤ W := by omega
    linarith
  obtain ⟨gq, gpF, gB, gp, gN⟩ := hGe
  have bp : (parK d n e).p < 2 ^ ℓ ∧ (parK d n e).p < 2 ^ ℓa :=
    ⟨(show (parK d n e).p < ℓ by omega).trans Nat.lt_two_pow_self, by omega⟩
  have bpF : (parK d n e).pF < 2 ^ ℓ ∧ (parK d n e).pF < 2 ^ ℓa :=
    ⟨(show (parK d n e).pF < ℓ by omega).trans Nat.lt_two_pow_self, by omega⟩
  have bB : (parK d n e).B < 2 ^ ℓ ∧ (parK d n e).B < 2 ^ ℓa :=
    ⟨(show (parK d n e).B < ℓ by omega).trans Nat.lt_two_pow_self, by omega⟩
  have bNb : Bit.Sched.nBlk d < 2 ^ ℓ ∧ Bit.Sched.nBlk d < 2 ^ ℓa := by
    unfold Bit.Sched.nBlk; exact ⟨(show (d + 1) / 2 + 1 < ℓ by omega).trans Nat.lt_two_pow_self, by omega⟩
  -- the run
  refine XV.mono (K := (4 * e + 14) + ((696 * G + 3177) + (18 + (1 + (1 + (1 + 1)))))) ?_ hK fun _ h => h
  refine XV.seq (XV.neO hL hNS hNN hd hn h0 hN (by rw [hKd]) hrOne hNeZ hel hea h6) fun σ1 ⟨c1, d1, F1⟩ => ?_
  have s1 : ∀ y, ¬ SNe y → σ1.sc y = σ.sc y := F1.2.1
  refine XV.seq (XV.mono (XV.paramK (e := e) hL hNS (by omega) hd hn (hGdef ▸ hTl) (hGdef ▸ hTa)
    (by rw [s1 0 (by simp only [SNe]; omega), h0]) (by rw [s1 3 (by simp only [SNe]; omega)]; exact hN)
    (by rw [s1 1 (by simp only [SNe]; omega)]; exact hMode) c1 (by rw [s1 26 (by simp only [SNe]; omega), h26])
    (by rw [s1 27 (by simp only [SNe]; omega), h27]) (by rw [s1 28 (by simp only [SNe]; omega), h28])
    (by rw [F1.1 3 (by omega)]; exact hrOne)) (le_of_eq (by rw [hGdef])) fun _ h => h) fun σp ⟨hp, dp, Fp⟩ => ?_
  have hpv : ∀ y, 30 ≤ y → y < 123 → σp.sc y = pvK d n e (y - 30) := fun y h1 h2 => by
    have := hp (y - 30) (by omega)
    rwa [show 30 + (y - 30) = y by omega] at this
  obtain ⟨c1', c2, c3, c4⟩ := prmCopies_ok
  refine XV.seq (XV.copyS hL (z := sMode) (by bomega) prmCopies σp
    (by rw [Fp.2.1 sMode (by simp only [sMode]; omega), s1 sMode (by simp only [SNe, sMode]; omega)]; exact hMode)
    (fun p hp' => ?_) c2 c3) fun σc ⟨hc, dc, Fc⟩ => ?_
  · obtain ⟨q1, q2, q3, q4⟩ := c1' p hp'
    refine ⟨by omega, by omega, q2, ?_⟩
    rw [hpv _ q3 (by omega)]
    have := (pvA _ q4).trans_lt h2ℓ
    exact_mod_cast this
  have cz : ∀ y, (y < 4 ∨ 21 < y) → σc.sc y = σp.sc y := fun y hy => Fc.2.1 y (fun h => by
    obtain ⟨p, hp', e⟩ := List.mem_map.1 h
    have := c4 p hp'
    omega)
  have hcs : ∀ y, 30 ≤ y → y < 123 → σc.sc y = pvK d n e (y - 30) := fun y h1 h2 => by
    rw [cz y (by omega), hpv y h1 h2]
  refine XV.seq (XV.rtoNat hL (i := rP) (x := 53) (v := (parK d n e).p) (by bomega) (by bomega)
    (by rw [(hcs 53 (by norm_num) (by norm_num) : σc.sc 53 = ((pvK d n e 23 : ℤ) : ℝ)), hP23])
    bp.2 bp.1) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.rtoNat hL (i := rPF) (x := 57) (v := (parK d n e).pF) (by bomega) (by bomega)
    (by rw [Env.setNat_sc, (hcs 57 (by norm_num) (by norm_num) : σc.sc 57 = ((pvK d n e 27 : ℤ) : ℝ)), hP27])
    bpF.2 bpF.1) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.rtoNat hL (i := rNb) (x := 122) (v := Bit.Sched.nBlk d) (by bomega) (by bomega)
    (by rw [Env.setNat_sc, Env.setNat_sc,
      (hcs 122 (by norm_num) (by norm_num) : σc.sc 122 = ((pvK d n e 92 : ℤ) : ℝ)), hP92])
    bNb.2 bNb.1) fun σ4 e4 => ?_
  subst e4
  refine XV.mono (XV.rtoNat hL (i := rB) (x := 60) (v := (parK d n e).B) (by bomega) (by bomega)
    (by rw [Env.setNat_sc, Env.setNat_sc, Env.setNat_sc,
      (hcs 60 (by norm_num) (by norm_num) : σc.sc 60 = ((pvK d n e 30 : ℤ) : ℝ)), hP30])
    bB.2 bB.1) le_rfl fun σ' e5 => ?_
  subst e5
  subst hedef
  have cp : ∀ y k, (y, k) ∈ prmCopies →
      (((((σc.setNat rP (parK d n (kDel δ)).p).setNat rPF (parK d n (kDel δ)).pF).setNat rNb (Bit.Sched.nBlk d)).setNat rB
        (parK d n (kDel δ)).B).sc y = pvK d n (kDel δ) (k - 30)) := fun y k h => by
    simp only [Env.setNat_sc]
    obtain ⟨-, -, q3, q4⟩ := c1' _ h
    rw [hc _ h, hpv _ q3 (by omega)]
  refine ⟨⟨⟨by simp; rfl, by simp; rfl, by simp, by simp; rfl⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩,
    fun y h1 h2 => ?_, ?_, ?_⟩
  -- the constants
  · rw [cp _ 65 (by decide), show 65 - 30 = 35 from rfl, pvK_35]; push_cast; rfl
  · rw [cp _ 66 (by decide), show 66 - 30 = 36 from rfl, pvK_36]; push_cast; rfl
  · rw [cp _ 64 (by decide), show 64 - 30 = 34 from rfl, pvK_34]; push_cast; rfl
  · rw [cp _ 69 (by decide), show 69 - 30 = 39 from rfl, pvK_39]
    show _ = (((parK d n (kDel δ)).eHat⁻¹ : ℚ) : ℝ)
    rw [parK_eHat_inv]; push_cast; rfl
  · rw [cp _ 48 (by decide), show 48 - 30 = 18 from rfl, pvK_18]; rfl
  · rw [cp _ 70 (by decide), show 70 - 30 = 40 from rfl, pvK_40]
    show _ = (((parK d n (kDel δ)).Lam : ℕ) : ℝ)
    rw [parK_Lam]; push_cast; rfl
  · rw [cp _ 121 (by decide), show 121 - 30 = 91 from rfl, pvK_91]
    show _ = (((parK d n (kDel δ)).Rint : ℕ) : ℝ)
    rw [← RintK_eq]; push_cast; rfl
  -- PARAM's rational fields
  · rw [cp _ 99 (by decide), show 99 - 30 = 69 from rfl, pvK_69 hd hn, ← qn_parK_eps hd hn]; rfl
  · rw [cp _ 100 (by decide), show 100 - 30 = 70 from rfl, pvK_70 hd hn, ← qn_parK_lam hd hn]; rfl
  · rw [cp _ 101 (by decide), show 101 - 30 = 71 from rfl, pvK_71 hd hn, ← qn_parK_eta hd hn]; rfl
  · rw [cp _ 103 (by decide), show 103 - 30 = 73 from rfl, pvK_73 hd hn, ← qn_parK_rho hd hn]; rfl
  · rw [cp _ 104 (by decide), show 104 - 30 = 74 from rfl, pvK_74 hd hn, ← qn_parK_kapc hd hn]; rfl
  · rw [cp _ 105 (by decide), show 105 - 30 = 75 from rfl, pvK_75 hd hn, ← qn_parK_nu hd hn]; rfl
  · rw [cp _ 110 (by decide), show 110 - 30 = 80 from rfl, pvK_80, ← qn_parK_R]; rfl
  · rw [cp _ 111 (by decide), show 111 - 30 = 81 from rfl, pvK_81, ← qn_parK_sb]; rfl
  · rw [cp _ 115 (by decide), show 115 - 30 = 85 from rfl, pvK_85 hd hn, ← qn_parK_W hd hn]; rfl
  · rw [cp _ 119 (by decide), show 119 - 30 = 89 from rfl, pvK_89 hd hn, ← qn_parK_A0 hd hn]; rfl
  · rw [cp _ 120 (by decide), show 120 - 30 = 90 from rfl, pvK_90 hd hn, ← qn_parK_B0 hd hn]; rfl
  -- the bounds of the slots `4, ..., 21`
  · obtain ⟨p, hp', rfl⟩ := prmCopies_cover _ h2 h1
    obtain ⟨-, -, q3, q4⟩ := c1' p hp'
    refine ⟨pvK d n (kDel δ) (p.2 - 30), cp p.1 p.2 hp', (pvA _ q4).trans (pow_le_pow_right₀ (by norm_num) hGs)⟩
  · simp only [Env.setNat_draws]; rw [dc, dp, d1]
  · have G1 : FrameA SPar (fun j => rP ≤ j) (fun b _ => 8 ≤ b) σ σ1 :=
      F1.mono (fun y h => Or.inl ⟨h.1, by have := h.2; omega⟩) (fun j h => by simp only [rP]; omega)
        (fun _ _ h => h.elim)
    have G2 : FrameA SPar (fun j => rP ≤ j) (fun b _ => 8 ≤ b) σ1 σp :=
      (FrameA.ofP (Ar := fun _ _ => False) Fp).mono (fun y h => by unfold SPar; omega)
        (fun j h => by simp only [rP]; omega) (fun _ _ h => h.elim)
    have G3 : FrameA SPar (fun j => rP ≤ j) (fun b _ => 8 ≤ b) σp σc :=
      Fc.mono (fun y h => by
          obtain ⟨p, hp', rfl⟩ := List.mem_map.1 h
          have := c4 p hp'
          exact Or.inl ⟨this.1, by omega⟩) (fun _ h => h.elim) (fun _ _ h => h.elim)
    have F2 := (G1.trans G2).trans G3
    exact (((F2.setNat (i := rP) le_rfl _).setNat (i := rPF) (by decide) _).setNat (i := rNb) (by decide) _).setNat
      (i := rB) (by decide) _

end AdversarialBco.Unified.ProgO
