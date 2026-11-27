/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.TailOCallT
public import AdversarialBco.Bit.Transfer.XTriBox

@[expose] public section

/-!
# The inputs of BL-O's ELL-O block beyond v2.1's preparation

After v2.1's preparation `xprep` (the inputs of `blkBL` for `clearQ D`), `xpreC` writes what ELL-O's block `blkC`
and its test read besides: `xpreC1` the radius `r/2` reduced (slots `96`, `97`, by v2.1's `xred` on `(r_num, 2 r_den)`),
`erK = 1` (register `32`) and the centre `(1; 0)` (array `12`); `xpreC2` the scale `D' = 2^pF - ε̂` (slot `100`),
`D_S D'` (slot `101`), `r₀` (slots `98`, `99`) and the band offset `κ = kC - p - 4` (register `33`) from the
`xcmc` at the bases `qK` (slots from `800`, registers `64`, `76` to `79`).
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open Matrix

variable {d : ℕ}

/-- `r/2` reduced, `erK = 1`, the centre `(1; 0)`. -/
def xpreC1 (L : Layout) : XCmd :=
  .seq (toX (VL.sop2 L .add 102 85 85)) <|
  .seq (xred L sZ 84 102 113 114 115 96 97) <|
  .seq (.prim (.frag (.nconst 32 1))) <|
  .seq (xzero L 12 sZ 34 rD rOne) <|
  .seq (toX (VL.aset L 12 rD sZ)) <|
  .seq (toX (VL.sconst L 116 ((1 : ℤ) : ℚ))) <|
  .seq (.prim (.frag (.nconst 34 0))) <|
  toX (VL.aset L 12 34 116)

/-- The units of `xpreC1`. -/
def preC1K (d m : ℕ) : ℕ := 1 + (redUnits (m + 1) + (1 + ((d * (2 + 3) + 3) + (2 + (1 + (1 + 2))))))

set_option maxHeartbeats 4000000 in
theorem XV.preC1 {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hS : 117 ≤ L.NS)
    (hN : 35 ≤ L.NN) (hA : 13 ≤ L.NA) (hd1 : 1 ≤ d) {rN rD' : ℤ} {m : ℕ} (hD : σ.nat rD = d)
    (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (h84 : σ.sc 84 = rN) (h85 : σ.sc 85 = rD') (hrD : 0 < rD')
    (brN : |rN| ≤ 2 ^ m) (brD : rD' ≤ 2 ^ m) (hℓ : m + 3 < ℓ) :
    XRunsB L X ℓa ℓ (xpreC1 L) σ (preC1K d m) (fun σ' =>
      σ'.sc 96 = ((rN / (Int.gcd rN (rD' + rD') : ℤ) : ℤ) : ℝ) ∧
      σ'.sc 97 = (((rD' + rD') / (Int.gcd rN (rD' + rD') : ℤ) : ℤ) : ℝ) ∧
      σ'.nat 32 = 1 ∧ σ'.arr 12 0 = 1 ∧ (∀ j : Fin d, σ'.arr 12 (1 + (j : ℕ)) = 0) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => 96 ≤ y ∧ y ≤ 116) (fun j => 32 ≤ j ∧ j ≤ 34) (fun b _ => b = 12) σ σ') := by
  have hL1 := hL.1
  have hda := asz_lt hL (a := 0) (by omega)
  have hdA : d * d + d < 2 ^ ℓa := hda
  have bD2 : rD' + rD' ≤ 2 ^ (m + 1) := by rw [pow_succ]; linarith
  have aD : |rD'| ≤ 2 ^ m := by rw [abs_of_pos hrD]; exact brD
  refine XV.seq (XV.addI hL (x := 102) (a := 85) (b := 85) (u := rD') (v := rD') (by omega) (by omega) (by omega)
    h85 h85 (absZ_lt' aD (by omega)) (absZ_lt' aD (by omega))
    (absZ_lt' (by rw [abs_of_pos (by omega)]; exact bD2) (show m + 1 < ℓ by omega))) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.red hL (z := sZ) (sN := 84) (sD := 102) (sa := 113) (sb := 114) (st := 115) (snum := 96)
    (sden := 97) (s := m + 1) (N := rN) (D := rD' + rD') (by simp only [sZ]; omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by simp only [sZ]; decide)
    (by rw [Env.setSc_sc, if_neg (by simp only [sZ]; omega), hz])
    (by rw [Env.setSc_sc, if_neg (by omega), h84]) (by simp) (by omega)
    (brN.trans (pow_le_pow_right₀ (by norm_num) (by omega))) bD2 (by omega)) fun σ2 ⟨n2, d2', dr2, F2⟩ => ?_
  have q2 : ∀ y, y < 96 → σ2.sc y = σ.sc y := fun y hy => by
    rw [F2.2.1 y (by omega), Env.setSc_sc, if_neg (by omega)]
  refine XV.seq (XV.nconst hL (σ := σ2) (i := 32) (by omega) 1 (by omega)) fun σ3 e3 => ?_
  have nD3 : σ3.nat rD = d := by rw [e3, Env.setNat_nat, if_neg (by simp only [rD]; omega), F2.1 _ id]; exact hD
  have n13 : σ3.nat rOne = 1 := by
    rw [e3, Env.setNat_nat, if_neg (by simp only [rOne]; omega), F2.1 _ id]; exact h1
  have z3 : σ3.sc sZ = 0 := by rw [e3, Env.setNat_sc, q2 _ (by simp only [sZ]; omega), hz]
  refine XV.seq (AdversarialBco.Bit.Transfer.XV.zero hL (σ := σ3) (aR := 12) (sZ := sZ) (nl := 34) (nd := rD)
    (none := rOne) (by omega) (by simp only [sZ]; omega) (by omega) (by simp only [rD]; omega)
    (by simp only [rOne]; omega) (by simp only [rD, rOne]; decide) nD3 n13 hdA z3) fun σ4 ⟨y4, dr4, F4⟩ => ?_
  have nD4 : σ4.nat rD = d := by rw [F4.1 _ (by simp only [rD]; omega), nD3]
  have z4 : σ4.sc sZ = 0 := by rw [F4.2.1 _ id, z3]
  refine XV.seq (XV.aset hL (σ := σ4) (a := 12) (i := rD) (x := sZ) (by omega) (by simp only [rD]; omega)
    (by simp only [sZ]; omega) (by rw [nD4]; unfold asz; nlinarith) (by rw [z4]; simp)) fun σ5 e5 => ?_
  refine XV.seq (XV.constI hL (σ := σ5) (x := 116) (by omega) 1 (by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)))
    fun σ6 e6 => ?_
  refine XV.seq (XV.nconst hL (σ := σ6) (i := 34) (by omega) 0 (by omega)) fun σ7 e7 => ?_
  have n7 : σ7.nat 34 = 0 := by rw [e7]; simp
  refine XV.mono (XV.aset hL (σ := σ7) (a := 12) (i := 34) (x := 116) (by omega) (by omega) (by omega)
    (by rw [n7]; unfold asz; nlinarith) (by rw [e7, e6]; simp; exact one_lt_pow₀ (by norm_num) (by omega))) le_rfl fun σ8 e8 => ?_
  subst e8
  have s7 : ∀ y, y ≠ 116 → σ7.sc y = σ4.sc y := fun y hy => by rw [e7, e6, e5]; simp [hy]
  refine ⟨?_, ?_, ?_, ?_, fun j => ?_, ?_, ?_⟩
  · rw [Env.setArr_sc, s7 _ (by omega), F4.2.1 _ id, e3, Env.setNat_sc]; exact n2
  · rw [Env.setArr_sc, s7 _ (by omega), F4.2.1 _ id, e3, Env.setNat_sc]; exact d2'
  · rw [Env.setArr_nat, e7, e6, e5, Env.setNat_nat, if_neg (by omega)]; simp only [Env.setSc_nat, Env.setArr_nat]
    rw [F4.1 _ (by omega), e3]; simp
  · rw [Env.setArr_arr, n7]; simp [e7, e6]
  · rw [Env.setArr_arr, n7, if_neg (by omega), e7, e6, e5]
    simp only [Env.setNat_arr, Env.setSc_arr, Env.setArr_arr, nD4]
    by_cases hj : 1 + (j : ℕ) = d
    · rw [if_pos ⟨trivial, hj⟩, z4]
    · rw [if_neg (fun h => hj h.2)]; exact y4 _ (by omega)
  · rw [Env.setArr_draws, e7, e6, e5]; simp [dr4, e3, dr2]
  · have G3 : FrameA (fun y => 96 ≤ y ∧ y ≤ 116) (fun j => 32 ≤ j ∧ j ≤ 34) (fun b _ => b = 12) σ σ3 := by
      rw [e3]
      exact ((FrameA.refl _ _ _ σ).setSc (by omega) _ |>.trans
        (F2.mono (fun y h => by omega) (fun _ h => h.elim) (fun _ _ h => h.elim))).setNat (by omega) _
    have G4 := G3.trans (F4.mono (fun _ h => h.elim) (fun j h => by omega) (fun b _ h => h.1))
    rw [e7, e6, e5]
    exact (((G4.setArr rfl _).setSc (by omega) _).setNat (by omega) _).setArr rfl _

/-- The bases of the precision block `xcmc` in the call. -/
def qK : TstLay := ⟨800, 64, 40⟩

/-- The scale `2^pF/D'` with a positive denominator: `D'' = D'`, `PF' = 2^pF` if `D' > 0`; `-D'`, `-2^pF` if
`D' < 0`; `1`, `0` if `D' = 0`. -/
def dpp (Dp : ℤ) : ℤ := if 0 < Dp then Dp else if Dp < 0 then -Dp else 1

def pfp (Dp PF : ℤ) : ℤ := if 0 < Dp then PF else if Dp < 0 then -PF else 0

theorem dpp_pos (Dp : ℤ) : 0 < dpp Dp := by unfold dpp; split_ifs <;> omega

theorem dpp_abs (Dp : ℤ) {m : ℕ} (h : |Dp| ≤ 2 ^ m) : |dpp Dp| ≤ 2 ^ m := by
  have : (1 : ℤ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  unfold dpp; split_ifs
  · exact h
  · rw [abs_neg]; exact h
  · rw [abs_one]; exact this

theorem pfp_abs (Dp PF : ℤ) {m : ℕ} (h : |PF| ≤ 2 ^ m) : |pfp Dp PF| ≤ 2 ^ m := by
  unfold pfp; split_ifs
  · exact h
  · rw [abs_neg]; exact h
  · rw [abs_zero]; positivity

/-- The scale is kept: `PF'/D'' = PF/D'` (with `x/0 = 0`). -/
theorem pfp_div_dpp (Dp PF : ℤ) : ((pfp Dp PF : ℤ) : ℚ) / (dpp Dp : ℤ) = (PF : ℚ) / Dp := by
  unfold pfp dpp
  split_ifs with h1 h2
  · rfl
  · push_cast; rw [neg_div_neg_eq]
  · have : Dp = 0 := by omega
    subst this; simp

/-- The sign normalization of `D'` (slot `100`) and the numerator `PF'` into the slot `103`. -/
def xsgnC (L : Layout) : XCmd :=
  xifS L sZ 100 (toX (VL.sop2 L .add 103 s2pF sZ))
    (xifS L 100 sZ (.seq (toX (VL.sop2 L .sub 100 sZ 100)) (toX (VL.sop2 L .sub 103 sZ s2pF)))
      (.seq (toX (VL.sconst L 100 ((1 : ℤ) : ℚ))) (toX (VL.sconst L 103 ((0 : ℤ) : ℚ)))))

set_option maxHeartbeats 2000000 in
theorem XV.sgnC {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hS : 104 ≤ L.NS)
    {Dp PF : ℤ} {m : ℕ} (hz : σ.sc sZ = 0) (h100 : σ.sc 100 = Dp) (hF : σ.sc s2pF = PF) (bDp : |Dp| ≤ 2 ^ m)
    (bPF : |PF| ≤ 2 ^ m) (hℓ : m + 1 < ℓ) :
    XRunsB L X ℓa ℓ (xsgnC L) σ 6 (fun σ' =>
      σ'.sc 100 = ((dpp Dp : ℤ) : ℝ) ∧ σ'.sc 103 = ((pfp Dp PF : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = 100 ∨ y = 103) (fun _ => False) (fun _ _ => False) σ σ') := by
  have hL1 := hL.1
  have b0 : |(0 : ℝ)| < 2 ^ ℓ := by rw [abs_zero]; positivity
  have bD : |σ.sc 100| < 2 ^ ℓ := by rw [h100]; exact absZ_lt bDp (by omega)
  have bz : |σ.sc sZ| < 2 ^ ℓ := by rw [hz]; exact b0
  rcases lt_trichotomy 0 Dp with hp | h0 | hn
  · refine XV.mono (XV.ifS_t (K := 1) hL (by simp only [sZ]; omega) (by omega) bz bD (by rw [hz, h100]; exact_mod_cast hp)
      (XV.addI hL (x := 103) (a := s2pF) (b := sZ) (u := PF) (v := 0) (by omega) (by simp only [s2pF]; omega)
        (by simp only [sZ]; omega) hF (by rw [hz]; simp) (absZ_lt' bPF (by omega)) (by simp)
        (by simpa using absZ_lt' bPF (show m < ℓ by omega)))) (by omega) fun σ' e => ?_
    subst e
    refine ⟨by rw [Env.setSc_sc, if_neg (by omega), h100]; unfold dpp; rw [if_pos hp],
      by rw [Env.setSc_sc, if_pos rfl]; unfold pfp; rw [if_pos hp]; simp, rfl,
      (FrameA.refl _ _ _ σ).setSc (Or.inr rfl) _⟩
  · subst h0
    have hn' : ¬ σ.sc sZ < σ.sc 100 := by rw [hz, h100]; simp
    have hn'' : ¬ σ.sc 100 < σ.sc sZ := by rw [hz, h100]; simp
    have h1ℓ : |(1 : ℤ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (show ℓ ≠ 0 by omega)
    have h0ℓ : |(0 : ℤ)| < 2 ^ ℓ := by rw [abs_zero]; positivity
    refine XV.mono (Q := fun σ' => σ' = (σ.setSc 100 ((1 : ℤ) : ℝ)).setSc 103 ((0 : ℤ) : ℝ))
      (XV.ifS_f (K := 1 + 1 + 2) hL (by simp only [sZ]; omega) (by omega) bz bD hn'
        (XV.ifS_f (K := 1 + 1) hL (by omega) (by simp only [sZ]; omega) bD bz hn''
          (XV.seq (XV.constI hL (x := 100) (by omega) 1 h1ℓ) fun σ1 e1 => ?_))) (by omega) ?_
    · subst e1; exact XV.constI hL (x := 103) (by omega) 0 h0ℓ
    · intro σ' e
      subst e
      refine ⟨by simp [dpp], by simp [pfp], by simp, ?_⟩
      exact ((FrameA.refl _ _ _ σ).setSc (Or.inl rfl) _).setSc (Or.inr rfl) _
  · have hn' : ¬ σ.sc sZ < σ.sc 100 := by rw [hz, h100]; exact_mod_cast (not_lt.mpr hn.le)
    have hn'' : σ.sc 100 < σ.sc sZ := by rw [hz, h100]; exact_mod_cast hn
    have bnD : |0 - Dp| ≤ 2 ^ m := by rw [zero_sub, abs_neg]; exact bDp
    have bnF : |0 - PF| ≤ 2 ^ m := by rw [zero_sub, abs_neg]; exact bPF
    refine XV.mono (Q := fun σ' => σ' = (σ.setSc 100 ((0 - Dp : ℤ) : ℝ)).setSc 103 ((0 - PF : ℤ) : ℝ))
      (XV.ifS_f (K := 1 + 1 + 1) hL (by simp only [sZ]; omega) (by omega) bz bD hn'
        (XV.ifS_t (K := 1 + 1) hL (by omega) (by simp only [sZ]; omega) bD bz hn''
          (XV.seq (XV.subI hL (x := 100) (a := sZ) (b := 100) (u := 0) (v := Dp) (by omega)
            (by simp only [sZ]; omega) (by omega) (by rw [hz]; simp) h100 (by simp)
            (absZ_lt' bDp (show m < ℓ by omega)) (absZ_lt' bnD (show m < ℓ by omega))) fun σ1 e1 => ?_)))
      (by omega) ?_
    · subst e1
      exact XV.subI hL (x := 103) (a := sZ) (b := s2pF) (u := 0) (v := PF) (by omega)
        (by simp only [sZ]; omega) (by simp only [s2pF]; omega)
        (by rw [Env.setSc_sc, if_neg (by simp only [sZ]; omega), hz]; simp)
        (by rw [Env.setSc_sc, if_neg (by simp only [s2pF]; omega), hF]) (by simp)
        (absZ_lt' bPF (show m < ℓ by omega)) (absZ_lt' bnF (show m < ℓ by omega))
    · intro σ' e
      subst e
      have hp' : ¬ 0 < Dp := by omega
      refine ⟨by simp [dpp, hp', hn], by simp [pfp, hp', hn], by simp, ?_⟩
      exact ((FrameA.refl _ _ _ σ).setSc (Or.inl rfl) _).setSc (Or.inr rfl) _

/-- `D'`, its normalization, `D_S D''`, `r₀`, `κ`. -/
def xpreC2 (L : Layout) : XCmd :=
  .seq (toX (VL.sop2 L .sub 100 s2pF sEps)) <|
  .seq (xsgnC L) <|
  .seq (toX (VL.sop2 L .mul 101 sDS 100)) <|
  .seq (xcmc L qK) <|
  .seq (toX (VL.sop2 L .add 98 800 sZ)) <|
  .seq (toX (VL.sop2 L .add 99 801 sZ)) <|
  .seq (.prim (.frag (.nsub 33 64 rP))) <|
  .seq (.prim (.frag (.nconst 34 4))) <|
  .prim (.frag (.nsub 33 33 34))

/-- The units of `xpreC2`. -/
def preC2K (m : ℕ) : ℕ := 1 + (6 + (1 + (200 * (m + 1) + (1 + (1 + (1 + (1 + 1)))))))

theorem cmcK_leC {p G : ℕ} {N D : ℤ} (hN : 0 ≤ N) (hD : 0 < D) (hNG : N ≤ 2 ^ G) : cmcK p N D ≤ p + G + 4 := by
  obtain ⟨h0, h1⟩ := ceil_quot_le hN hD
  have : (0 - (0 - N) / D).toNat ≤ 2 ^ G := by
    have : ((0 - (0 - N) / D).toNat : ℤ) ≤ 2 ^ G := by rw [Int.toNat_of_nonneg h0]; exact h1.trans hNG
    exact_mod_cast this
  have := Nat.clog_le_of_le_pow this
  unfold cmcK; omega

set_option maxHeartbeats 4000000 in
theorem XV.preC2 {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hS : 856 ≤ L.NS)
    (hN : 80 ≤ L.NN) (hA : 44 ≤ L.NA) {rn rd Rn0 Rd0 Rn PF eh DS : ℤ} {p m : ℕ}
    (i4 : X.inp 4 = rn) (i5 : X.inp 5 = rd) (i6 : X.inp 6 = Rn0) (i7 : X.inp 7 = Rd0) (hoff : 8 ≤ X.off)
    (hrn : 0 < rn) (hrd : 0 < rd) (hR0n : 0 < Rn0) (hR0d : 0 < Rd0) (hRn : 0 ≤ Rn) (hPF : 0 < PF)
    (hz : σ.sc sZ = 0) (h1 : σ.nat rOne = 1) (hp : σ.nat rP = p) (hR : σ.sc sR = Rn) (hF : σ.sc s2pF = PF)
    (heh : σ.sc sEps = eh) (hDS : σ.sc sDS = DS)
    (brn : rn ≤ 2 ^ m) (brd : rd ≤ 2 ^ m) (bR0n : Rn0 ≤ 2 ^ m) (bR0d : Rd0 ≤ 2 ^ m) (bRn : Rn ≤ 2 ^ m)
    (bPF : PF ≤ 2 ^ m) (beh : |eh| ≤ 2 ^ m) (bDS : |DS| ≤ 2 ^ m) (hpm : p ≤ m) (hℓ : 12 * m + 40 ≤ ℓ)
    (hℓa : 12 * m + 40 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xpreC2 L) σ (preC2K m) (fun σ' =>
      σ'.sc 100 = ((dpp (PF - eh) : ℤ) : ℝ) ∧ σ'.sc 103 = ((pfp (PF - eh) PF : ℤ) : ℝ) ∧
      σ'.sc 101 = ((DS * dpp (PF - eh) : ℤ) : ℝ) ∧ σ'.sc 98 = rn ∧
      σ'.sc 99 = rd ∧ σ'.nat 33 = cmcK p (6 * Rn * Rn0 * rd * rd) (PF * Rd0 * rn * rn) - p - 4 ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => (98 ≤ y ∧ y ≤ 103) ∨ 800 ≤ y) (fun j => j = 33 ∨ j = 34 ∨ j = 64 ∨ (76 ≤ j ∧ j < 80))
        (fun _ _ => False) σ σ') := by
  have hL1 := hL.1
  have aPF : |PF| ≤ 2 ^ m := by rw [abs_of_pos hPF]; exact bPF
  have bD' : |PF - eh| ≤ 2 ^ (m + 1) := absI_sub_le aPF beh
  have bdpp := dpp_abs (PF - eh) bD'
  have bDD : |DS * dpp (PF - eh)| ≤ 2 ^ (m + (m + 1)) := absI_mul_le bDS bdpp
  set S : ℕ → Prop := fun y => (98 ≤ y ∧ y ≤ 103) ∨ 800 ≤ y with hSd
  set N : ℕ → Prop := fun j => j = 33 ∨ j = 34 ∨ j = 64 ∨ (76 ≤ j ∧ j < 80) with hNd
  refine XV.seq (XV.subI hL (x := 100) (a := s2pF) (b := sEps) (u := PF) (v := eh) (by omega)
    (by simp only [s2pF]; omega) (by simp only [sEps]; omega) hF heh (absZ_lt' aPF (by omega))
    (absZ_lt' beh (by omega)) (absZ_lt' bD' (by omega))) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.sgnC hL (by omega) (m := m + 1) (Dp := PF - eh) (PF := PF)
    (by rw [Env.setSc_sc, if_neg (by simp only [sZ]; omega), hz]) (by simp)
    (by rw [Env.setSc_sc, if_neg (by simp only [s2pF]; omega), hF]) bD'
    (aPF.trans (pow_le_pow_right₀ (by norm_num) (by omega))) (by omega)) fun σ2 ⟨g100, g103, dr2, F2⟩ => ?_
  have k2 : ∀ y, y < 100 → σ2.sc y = σ.sc y := fun y hy => by
    rw [F2.2.1 y (by omega), Env.setSc_sc, if_neg (by omega)]
  refine XV.seq (XV.mulI hL (σ := σ2) (x := 101) (a := sDS) (b := 100) (u := DS) (v := dpp (PF - eh)) (by omega)
    (by simp only [sDS]; omega) (by omega) (by rw [k2 _ (by simp only [sDS]; omega), hDS]) g100
    (absZ_lt' bDS (by omega)) (absZ_lt' bdpp (by omega)) (absZ_lt' bDD (by omega))) fun σ2' e2 => ?_
  subst e2
  have k2' : ∀ y, y < 100 → (σ2.setSc 101 ((DS * dpp (PF - eh) : ℤ) : ℝ)).sc y = σ.sc y :=
    fun y hy => by rw [Env.setSc_sc, if_neg (by omega), k2 y hy]
  have G2 : FrameA S N (fun _ _ => False) σ (σ2.setSc 101 ((DS * dpp (PF - eh) : ℤ) : ℝ)) :=
    ((((FrameA.refl S N (fun _ _ => False) σ).setSc (Or.inl ⟨by omega, by omega⟩) _).trans
      (F2.mono (fun y h => Or.inl (by omega)) (fun _ h => h.elim) (fun _ _ h => h))).setSc
        (Or.inl ⟨by omega, by omega⟩) _)
  refine XV.seq (XV.cmc hL (σ := σ2.setSc 101 ((DS * dpp (PF - eh) : ℤ) : ℝ))
    (Q := qK) ⟨⟨by decide, hS⟩, ⟨by decide, hN⟩, ⟨by decide, hA⟩⟩ i4 i5 i6 i7 hoff hrn hrd hR0n hR0d hRn hPF
    (by rw [k2' _ (by simp only [sZ]; omega), hz]) (by rw [G2.1 _ (by simp only [hNd, rOne]; omega), h1])
    (by rw [G2.1 _ (by simp only [hNd, rP]; omega), hp])
    (by rw [k2' _ (by simp only [sR]; omega), hR]) (by rw [k2' _ (by simp only [s2pF]; omega), hF])
    brn brd bR0n bR0d bRn bPF hpm hℓ hℓa) fun σ3 ⟨c0, c1, cK, _, dr3, F3⟩ => ?_
  set K := cmcK p (6 * Rn * Rn0 * rd * rd) (PF * Rd0 * rn * rn) with hK
  have hKle : K ≤ p + (4 * m + 3) + 4 := by
    have hN0 : 0 ≤ 6 * Rn * Rn0 * rd * rd := by positivity
    have hD0 : 0 < PF * Rd0 * rn * rn := by positivity
    have h6 : (6 : ℤ) ≤ 2 ^ 3 := by norm_num
    have hNG : 6 * Rn * Rn0 * rd * rd ≤ 2 ^ (4 * m + 3) := by
      calc 6 * Rn * Rn0 * rd * rd ≤ 2 ^ 3 * 2 ^ m * 2 ^ m * 2 ^ m * 2 ^ m := by
            gcongr
        _ = 2 ^ (4 * m + 3) := by ring
    exact cmcK_leC hN0 hD0 hNG
  have hKp : p + 4 ≤ K := by rw [hK]; unfold cmcK; omega
  have aZ : σ3.sc sZ = 0 := by
    rw [F3.2.1 _ (by simp only [qK, sZ]; omega), k2' _ (by simp only [sZ]; omega), hz]
  have arn : |rn| ≤ 2 ^ m := by rw [abs_of_pos hrn]; exact brn
  have ard : |rd| ≤ 2 ^ m := by rw [abs_of_pos hrd]; exact brd
  have n64 : σ3.nat 64 = K := by simpa [qK] using cK
  have nP : σ3.nat rP = p := by
    rw [F3.1 _ (by simp only [qK, rP]; omega), G2.1 _ (by simp only [hNd, rP]; omega), hp]
  have s100 : σ3.sc 100 = ((dpp (PF - eh) : ℤ) : ℝ) := by
    rw [F3.2.1 _ (by simp only [qK]; omega), Env.setSc_sc, if_neg (by omega), g100]
  have s103 : σ3.sc 103 = ((pfp (PF - eh) PF : ℤ) : ℝ) := by
    rw [F3.2.1 _ (by simp only [qK]; omega), Env.setSc_sc, if_neg (by omega), g103]
  have s101 : σ3.sc 101 = ((DS * dpp (PF - eh) : ℤ) : ℝ) := by
    rw [F3.2.1 _ (by simp only [qK]; omega)]; simp
  refine XV.seq (XV.addI hL (σ := σ3) (x := 98) (a := 800) (b := sZ) (u := rn) (v := 0) (by omega) (by omega)
    (by simp only [sZ]; omega) (by simpa [qK] using c0) (by rw [aZ]; simp) (absZ_lt' arn (by omega)) (by simp)
    (by simpa using absZ_lt' arn (show m < ℓ by omega))) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.addI hL (x := 99) (a := 801) (b := sZ) (u := rd) (v := 0) (by omega) (by omega)
    (by simp only [sZ]; omega) (by rw [Env.setSc_sc, if_neg (by omega)]; simpa [qK] using c1)
    (by rw [Env.setSc_sc, if_neg (by simp only [sZ]; omega), aZ]; simp) (absZ_lt' ard (by omega)) (by simp)
    (by simpa using absZ_lt' ard (show m < ℓ by omega))) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.nsub hL (i := 33) (a := 64) (b := rP) (by omega) (by omega) (by simp only [rP]; omega)
    (by simp [n64]; omega) (by simp [nP]; omega) (by simp [n64, nP]; omega)) fun σ6 e6 => ?_
  subst e6
  refine XV.seq (XV.nconst hL (i := 34) (by omega) 4 (by omega)) fun σ7 e7 => ?_
  subst e7
  refine XV.mono (XV.nsub hL (i := 33) (a := 33) (b := 34) (by omega) (by omega) (by omega)
    (by simp [n64, nP]; omega) (by simp; omega) (by simp [n64, nP]; omega)) le_rfl fun σ8 e8 => ?_
  subst e8
  refine ⟨by simp [s100], by simp [s103], by simp [s101], by simp, by simp, by simp [n64, nP], by simp [dr3, dr2], ?_⟩
  have G : FrameA S N (fun _ _ => False) (σ2.setSc 101 ((DS * dpp (PF - eh) : ℤ) : ℝ)) σ3 :=
    F3.mono (fun y h => Or.inr (by simpa [qK] using h)) (fun j h => by simp only [qK] at h; simp only [hNd]; omega)
      (fun _ _ h => h)
  exact ((((G2.trans G).setSc (Or.inl ⟨by omega, by omega⟩) _).setSc (Or.inl ⟨by omega, by omega⟩) _).setNat
    (Or.inl rfl) _ |>.setNat (Or.inr (Or.inl rfl)) _).setNat (Or.inl rfl) _

end AdversarialBco.Unified.ProgO
