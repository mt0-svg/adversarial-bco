/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOTriPreR

@[expose] public section

/-!
# BL-O's setup: the first position of TRI-OGD-O on the machine

`xpreC`: from the input cells, the common denominator `D = ∏ den_i` of the centre `a` (`xdenL`, slot `135`), `r₀n`,
`r₀d` into the slots `100`, `101`, `D r₀n` into `140`; the array `aT + 1` zeroed on its `d²` cells (`xzeroM`); then one
loop over `i < d` (`xcenB`): `N_i = num_i (D / den_i)` into `aKa[1 + i]`, `N_i r₀d` into `aT[i]`, `0` into
`aKg[1 + i]`, `D r₀n` into `aT + 1` at `d i + i`; last `aKa[0] := D`, `aKg[0] := 1`. `XV.preC`.
-/

namespace AdversarialBco.Unified.ProgO.TriO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO AdversarialBco.Unified.ProgO

variable {d : ℕ}

/-! ## The zero loop -/

/-- `aR[l] := sZ` for `l < M`, `M` in the register `nm`. -/
def xzeroM (L : Layout) (aR sZ nl nm none : ℕ) : XCmd := xforN nl nm none (toX (VL.aset L aR nl sZ))

theorem XV.zeroM {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {aR sZ nl nm none M : ℕ}
    (hR : aR < L.NA) (hsZ : sZ < L.NS) (hnl : nl < L.NN) (hnm : nm < L.NN) (hno : none < L.NN)
    (ld : nl ≠ nm) (lo : nl ≠ none) (hσm : σ.nat nm = M) (hσ1 : σ.nat none = 1) (hM : M ≤ asz d)
    (hMa : M < 2 ^ ℓa) (eZ : σ.sc sZ = 0) :
    XRunsB L X ℓa ℓ (xzeroM L aR sZ nl nm none) σ (M * (2 + 3) + 3)
      (fun σ' => (∀ l < M, σ'.arr aR l = 0) ∧ σ'.draws = σ.draws ∧
        FrameA (fun _ => False) (fun j => j = nl) (fun b k => b = aR ∧ k < M) σ σ') := by
  let J : ℕ → Env d → Prop := fun j σ' => (∀ j' < j, σ'.arr aR j' = 0) ∧ σ'.draws = σ.draws ∧ σ'.sc sZ = 0 ∧
    FrameA (fun _ => False) (fun j => j = nl) (fun b k => b = aR ∧ k < j) σ σ'
  refine XV.mono (XV.forN hL hnl hnm hno ld lo M 2 hMa J σ hσm hσ1
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, by rw [Env.setNat_sc]; exact eZ,
      (FrameA.refl (fun _ => False) (fun j => j = nl) (fun b k => b = aR ∧ k < 0) σ).setNat rfl 0⟩ ?_) le_rfl
    fun σ' ⟨⟨h1, h2, _, h4⟩, _⟩ => ⟨h1, h2, h4⟩
  intro j hj σ' ⟨hy, hd', hz, hF⟩ hjt hjn hj1
  refine XV.mono (XV.aset hL hR hnl hsZ (by rw [hjt]; omega) (by rw [hz]; simp)) le_rfl fun σ1 e1 => ?_
  subst e1
  refine ⟨by rw [Env.setArr_nat]; exact hjt, by rw [Env.setArr_nat]; exact hjn, by rw [Env.setArr_nat]; exact hj1,
    fun j' hj' => ?_, by rw [Env.setNat_draws, Env.setArr_draws]; exact hd',
    by rw [Env.setNat_sc, Env.setArr_sc]; exact hz, ?_⟩
  · rw [Env.setNat_arr, Env.setArr_arr]
    by_cases h : j' = j
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, by rw [hjt, h]⟩), hz]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h' => h (by rw [h'.2, hjt]))]
      exact hy j' (by omega)
  · exact ((hF.mono (fun _ h => h) (fun _ h => h) (fun b k h => ⟨h.1, by omega⟩)).setArr
      ⟨rfl, by rw [hjt]; omega⟩ _).setNat rfl _

/-! ## The loop of the centre -/

/-- One coordinate `i` (in the register `11`) of the first position: `N_i = num_i (D / den_i)` (inputs `8 + 2 i`,
`9 + 2 i` through the register `12`, `D` in `135`) into `aKa[1 + i]`; `N_i r₀d` (`r₀d` in `101`) into `aT[i]`; `0`
into `aKg[1 + i]`; `D r₀n` (slot `140`) into `aT + 1` at `(d + 1) i` (register `15`). -/
def xcenB (L : Layout) : XCmd :=
  .seq (xrdIn L 136 12) <| .seq (.prim (.frag (.nadd 12 12 rOne))) <| .seq (xrdIn L 137 12) <|
  .seq (.prim (.frag (.nadd 12 12 rOne))) <| .seq (xsidiv L 138 135 137) <|
  .seq (toX (VL.sop2 L .mul 138 136 138)) <| .seq (.prim (.frag (.nadd 14 11 rOne))) <|
  .seq (toX (VL.aset L aKa 14 138)) <| .seq (toX (VL.sop2 L .mul 139 138 101)) <|
  .seq (toX (VL.aset L aT 11 139)) <| .seq (toX (VL.aset L aKg 14 sZ)) <|
  .seq (toX (VL.aset L (aT + 1) 15 140)) <| .seq (.prim (.frag (.nadd 15 15 rD))) (.prim (.frag (.nadd 15 15 rOne)))

/-- The slots, registers and arrays of the loop. -/
def SCen (y : ℕ) : Prop := 136 ≤ y ∧ y ≤ 139
def NCen (j : ℕ) : Prop := 11 ≤ j ∧ j ≤ 15
def ACen (b _ : ℕ) : Prop := b = aKa ∨ b = aT ∨ b = aKg ∨ b = aT + 1

/-- The invariant of the loop at `t` from the state `σ0`. -/
def JCen (nm dn : ℕ → ℤ) (D rn rd : ℤ) (σ0 : Env d) (t : ℕ) (σ' : Env d) : Prop :=
  σ'.nat 12 = 8 + 2 * t ∧ σ'.nat 15 = (d + 1) * t ∧ σ'.draws = σ0.draws ∧ FrameA SCen NCen ACen σ0 σ' ∧
    (∀ i < t, σ'.arr aKa (1 + i) = ((cnum nm dn D i : ℤ) : ℝ)) ∧
    (∀ i < t, σ'.arr aT i = ((cnum nm dn D i * rd : ℤ) : ℝ)) ∧ (∀ i < t, σ'.arr aKg (1 + i) = 0) ∧
    (∀ i < t, σ'.arr (aT + 1) (d * i + i) = ((D * rn : ℤ) : ℝ)) ∧
    (∀ m < d * d, (∀ i < t, m ≠ d * i + i) → σ'.arr (aT + 1) m = 0)

theorem diag_inj {i i' : ℕ} (h : d * i + i = d * i' + i') : i = i' := by
  have e : (d + 1) * i = (d + 1) * i' := by rw [add_mul, add_mul, one_mul, one_mul]; exact h
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos d) e

theorem diag_off {i l i' : ℕ} (hl : l < d) (hi' : i' < d) (hil : i ≠ l) : d * i + l ≠ d * i' + i' := by
  intro h
  rcases lt_trichotomy i i' with h1 | h1 | h1
  · have : d * (i + 1) ≤ d * i' := Nat.mul_le_mul_left d h1
    rw [mul_add, mul_one] at this; omega
  · subst h1; omega
  · have : d * (i' + 1) ≤ d * i := Nat.mul_le_mul_left d h1
    rw [mul_add, mul_one] at this; omega

set_option maxHeartbeats 8000000 in
theorem XV.cenB {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hNS : 172 ≤ L.NS) (hNN : 48 ≤ L.NN)
    (hNA : 26 ≤ L.NA) {dn nm : ℕ → ℤ} (hdn : ∀ j, 0 < dn j) (hin : ∀ j < d, X.inp (9 + 2 * j) = dn j)
    (hinN : ∀ j < d, X.inp (8 + 2 * j) = nm j) (hoff : 8 + 2 * d ≤ X.off) {D rn rd : ℤ} (hD : D = pdn dn d)
    (hrd : 0 < rd) (hrdl : rd < 2 ^ ℓ) (hP : D < 2 ^ ℓ) (hNP : ∀ j < d, |nm j| * D * rd < 2 ^ ℓ) (hDR : |D * rn| < 2 ^ ℓ)
    (hda : d * d + 2 * d + 10 < 2 ^ ℓa) {σ0 : Env d} (e135 : σ0.sc 135 = D) (e101 : σ0.sc 101 = rd)
    (e140 : σ0.sc 140 = ((D * rn : ℤ) : ℝ)) (eZ : σ0.sc sZ = 0) (t : ℕ) (ht : t < d) (σ' : Env d)
    (hJ : JCen nm dn D rn rd σ0 t σ') (ji : σ'.nat 11 = t) (jn : σ'.nat rD = d) (jo : σ'.nat rOne = 1) :
    XRunsB L X ℓa ℓ (xcenB L) σ' 18 (fun σ'' => σ''.nat 11 = t ∧ σ''.nat rD = d ∧ σ''.nat rOne = 1 ∧
      JCen nm dn D rn rd σ0 (t + 1) (σ''.setNat 11 (t + 1))) := by
  obtain ⟨j12, j15, jdr, jF, A1, A2, A3, A4, A5⟩ := hJ
  have j135 : σ'.sc 135 = D := (jF.2.1 135 (by simp only [SCen]; omega)).trans e135
  have j101 : σ'.sc 101 = rd := (jF.2.1 101 (by simp only [SCen]; omega)).trans e101
  have j140 : σ'.sc 140 = ((D * rn : ℤ) : ℝ) := (jF.2.1 140 (by simp only [SCen]; omega)).trans e140
  have jZ : σ'.sc sZ = 0 := (jF.2.1 sZ (by simp only [SCen, sZ]; omega)).trans eZ
  have hPpos : 0 < D := hD ▸ pdn_pos hdn d
  have hdt : dn t ≤ D := hD ▸ dn_le_pdn hdn ht
  have hd0 := hdn t
  have hq0 : 0 ≤ D / dn t := Int.ediv_nonneg hPpos.le hd0.le
  have hq : D / dn t ≤ D := Int.ediv_le_self _ hPpos.le
  have hnt0 : |nm t| * D ≤ |nm t| * D * rd := le_mul_of_one_le_right (by positivity) (by omega)
  have hnt : |nm t| ≤ |nm t| * D := le_mul_of_one_le_right (abs_nonneg _) (by omega)
  have hcn0 : |cnum nm dn D t| ≤ |nm t| * D := by
    unfold cnum
    rw [abs_mul, abs_of_nonneg hq0]
    exact mul_le_mul_of_nonneg_left hq (abs_nonneg _)
  have hnl : |nm t| < 2 ^ ℓ := hnt.trans_lt (hnt0.trans_lt (hNP t ht))
  have hcn : |cnum nm dn D t| < 2 ^ ℓ := (hcn0.trans hnt0).trans_lt (hNP t ht)
  have hcr : |cnum nm dn D t * rd| < 2 ^ ℓ := by
    rw [abs_mul, abs_of_pos hrd]
    exact (mul_le_mul_of_nonneg_right hcn0 hrd.le).trans_lt (hNP t ht)
  have hgt : d * t + t < asz d := by unfold asz; nlinarith
  refine XV.mono (K := 1 + (1 + (1 + (1 + (1 + (1 + (1 + (2 + (1 + (2 + (2 + (2 + (1 + 1))))))))))))) ?_
    (by norm_num) fun _ h => h
  have eN : ((X.inp (σ'.nat 12) : ℤ) : ℝ) = (nm t : ℝ) := by rw [j12, hinN t ht]
  refine XV.seq (XV.rdIn (X := X) hL (x := 136) (i := 12) (by omega) (by omega) (by rw [j12]; omega)
    (by rw [j12]; omega) (by rw [eN, ← Int.cast_abs]; exact_mod_cast hnl)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.nadd hL (i := 12) (a := 12) (b := rOne) (by omega) (by omega) (by bomega)
    (by esimp; rw [j12]; omega) (by esimp; rw [jo]; omega)) fun σ3 e3 => ?_
  subst e3
  have eD : ((X.inp (((σ'.setSc 136 (X.inp (σ'.nat 12) : ℝ)).setNat 12
      ((σ'.setSc 136 (X.inp (σ'.nat 12) : ℝ)).nat 12 + (σ'.setSc 136 (X.inp (σ'.nat 12) : ℝ)).nat rOne)).nat 12)
      : ℤ) : ℝ) = (dn t : ℝ) := by
    simp only [Env.setNat_nat, if_pos, Env.setSc_nat, j12, jo]
    rw [show 8 + 2 * t + 1 = 9 + 2 * t by ring, hin t ht]
  refine XV.seq (XV.rdIn (X := X) hL (x := 137) (i := 12) (by omega) (by omega) (by esimp; rw [j12, jo]; omega)
    (by esimp; rw [j12, jo]; omega) (by rw [eD, ← Int.cast_abs, abs_of_pos hd0]; exact_mod_cast hdt.trans_lt hP))
    fun σ4 e4 => ?_
  subst e4
  rw [eD]
  refine XV.seq (XV.nadd hL (i := 12) (a := 12) (b := rOne) (by omega) (by omega) (by bomega)
    (by esimp; rw [j12, jo]; omega) (by esimp; rw [jo]; omega)) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.divI hL (x := 138) (a := 135) (b := 137) (by omega) (by omega) (by omega)
    (u := D) (v := dn t) (by simp [j135]) (by simp) (by rw [abs_of_pos hPpos]; exact hP)
    (by rw [abs_of_pos hd0]; exact hdt.trans_lt hP)) fun σ6 e6 => ?_
  subst e6
  refine XV.seq (XV.mulI hL (x := 138) (a := 136) (b := 138) (by omega) (by omega) (by omega)
    (u := nm t) (v := D / dn t) (by simp [eN]) (by simp)
    (hnt.trans_lt (hnt0.trans_lt (hNP t ht))) (by rw [abs_of_nonneg hq0]; exact hq.trans_lt hP) hcn)
    fun σ7 e7 => ?_
  subst e7
  refine XV.seq (XV.nadd hL (i := 14) (a := 11) (b := rOne) (by omega) (by omega) (by bomega)
    (by esimp; rw [ji]; omega) (by esimp; rw [jo]; omega)) fun σ8 e8 => ?_
  subst e8
  refine XV.seq (XV.aset hL (a := aKa) (i := 14) (x := 138) (by simp only [aKa, aT]; omega) (by omega) (by omega)
    (by esimp; rw [ji, jo]; unfold asz; nlinarith)
    (by esimp; rw [← Int.cast_abs]; unfold cnum at hcn; exact_mod_cast hcn)) fun σ9 e9 => ?_
  subst e9
  refine XV.seq (XV.mulI hL (x := 139) (a := 138) (b := 101) (by omega) (by omega) (by omega)
    (u := cnum nm dn D t) (v := rd) (by simp [cnum]) (by simp [j101]) hcn (by rw [abs_of_pos hrd]; exact hrdl) hcr)
    fun σ10 e10 => ?_
  subst e10
  refine XV.seq (XV.aset hL (a := aT) (i := 11) (x := 139) (by simp only [aT]; omega) (by omega) (by omega)
    (by esimp; rw [ji]; unfold asz; nlinarith)
    (by esimp; rw [← Int.cast_abs]; exact_mod_cast hcr)) fun σ11 e11 => ?_
  subst e11
  refine XV.seq (XV.aset hL (a := aKg) (i := 14) (x := sZ) (by simp only [aKg, aT]; omega) (by omega)
    (by simp only [sZ]; omega) (by esimp; rw [ji, jo]; unfold asz; nlinarith)
    (by simp [sZ, jZ])) fun σ12 e12 => ?_
  subst e12
  refine XV.seq (XV.aset hL (a := aT + 1) (i := 15) (x := 140) (by simp only [aT]; omega) (by omega) (by omega)
    (by esimp; rw [j15]; linarith [hgt, show (d + 1) * t = d * t + t by ring])
    (by esimp; rw [j140, ← Int.cast_abs]; exact_mod_cast hDR)) fun σ13 e13 => ?_
  subst e13
  refine XV.seq (XV.nadd hL (i := 15) (a := 15) (b := rD) (by omega) (by omega) (by bomega)
    (by esimp; rw [j15]; nlinarith) (by esimp; rw [jn]; omega)) fun σ14 e14 => ?_
  subst e14
  refine XV.mono (XV.nadd hL (i := 15) (a := 15) (b := rOne) (by omega) (by omega) (by bomega)
    (by esimp; rw [j15, jn]; nlinarith) (by esimp; rw [jo]; omega)) le_rfl fun σ15 e15 => ?_
  subst e15
  refine ⟨by esimp; exact ji, by esimp; exact jn, by esimp; exact jo, by esimp; rw [j12, jo]; ring,
    by esimp; rw [j15, jn, jo]; ring, by simp [jdr], ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_, fun m hm hm' => ?_⟩
  · exact ((((((((((((((jF.setSc (x := 136) ⟨by omega, by omega⟩ _).setNat (i := 12) ⟨by omega, by omega⟩ _).setSc
      (x := 137) ⟨by omega, by omega⟩ _).setNat (i := 12) ⟨by omega, by omega⟩ _).setSc (x := 138)
      ⟨by omega, by omega⟩ _).setSc (x := 138) ⟨by omega, by omega⟩ _).setNat (i := 14) ⟨by omega, by omega⟩ _).setArr
      (b := aKa) (Or.inl rfl) _).setSc (x := 139) ⟨by omega, by omega⟩ _).setArr (b := aT) (Or.inr (Or.inl rfl))
      _).setArr (b := aKg) (Or.inr (Or.inr (Or.inl rfl))) _).setArr (b := aT + 1) (Or.inr (Or.inr (Or.inr rfl)))
      _).setNat (i := 15) ⟨by omega, by omega⟩ _).setNat (i := 15) ⟨by omega, by omega⟩ _).setNat
      (i := 11) ⟨le_rfl, by omega⟩ _
  all_goals simp only [Env.setNat_arr, Env.setArr_arr, Env.setSc_arr, Env.setSc_nat, Env.setNat_nat, Env.setSc_sc,
    Env.setNat_sc, Env.setArr_sc, Env.setArr_nat, aKa, aT, aKg, rOne, rD, sZ, ji, jo, j12, j15, Nat.reduceAdd,
    Nat.reduceEqDiff, ↓reduceIte, true_and, false_and, and_true]
  · split_ifs with h
    · obtain rfl : i = t := by omega
      simp only [cnum]
    · exact A1 i (by omega)
  · split_ifs with h
    · obtain rfl : i = t := h
      rfl
    · exact A2 i (by omega)
  · split_ifs with h
    · rw [jZ]
    · exact A3 i (by omega)
  · split_ifs with h
    · obtain rfl : i = t := diag_inj (h.trans (by ring))
      exact j140
    · have : i ≠ t := fun e => h (by rw [e]; ring)
      exact A4 i (by omega)
  · split_ifs with h
    · exact absurd (h.trans (by ring)) (hm' t (by omega))
    · exact A5 m hm fun i hi => hm' i (by omega)

/-! ## The centre block -/

/-- The head of the centre block: `D` into `135`, `r₀n`, `r₀d` into `100`, `101`, `D r₀n` into `140`, `d²` into the
register `17`. -/
def xpreC1 (L : Layout) : XCmd :=
  .seq (xdenL L) <| .seq (.prim (.frag (.nconst 12 4))) <| .seq (xrdIn L 100 12) <|
  .seq (.prim (.frag (.nconst 12 5))) <| .seq (xrdIn L 101 12) <| .seq (toX (VL.sop2 L .mul 140 135 100))
    (xnmul 17 rD rD)

/-- **The first position**: the head, the zero loop on `aT + 1`, the loop `xcenB`, then `aKa[0] := D`,
`aKg[0] := 1`. -/
def xpreC (L : Layout) : XCmd :=
  .seq (xpreC1 L) <| .seq (xzeroM L (aT + 1) sZ 18 17 rOne) <|
  .seq (.prim (.frag (.nconst 12 8))) <| .seq (.prim (.frag (.nconst 15 0))) <|
  .seq (xforN 11 rD rOne (xcenB L)) <|
  .seq (.prim (.frag (.nconst 16 0))) <| .seq (toX (VL.aset L aKa 16 135)) (toX (VL.aset L aKg 16 26))

/-- The slots and registers of the centre block. -/
def SPC (y : ℕ) : Prop := (100 ≤ y ∧ y ≤ 101) ∨ (135 ≤ y ∧ y ≤ 140)
def NPC (j : ℕ) : Prop := 11 ≤ j ∧ j ≤ 18

set_option maxHeartbeats 4000000 in
theorem XV.preC1 {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hNS : 172 ≤ L.NS)
    (hNN : 48 ≤ L.NN) {dn : ℕ → ℤ} (hdn : ∀ j, 0 < dn j) (hin : ∀ j < d, X.inp (9 + 2 * j) = dn j)
    (hoff : 8 + 2 * d ≤ X.off) {rn rd : ℤ} (hi4 : X.inp 4 = rn) (hi5 : X.inp 5 = rd) (hrd : 0 < rd)
    (hrdl : rd < 2 ^ ℓ) (hrnl : |rn| < 2 ^ ℓ) (hP : pdn dn d < 2 ^ ℓ) (hDR : |pdn dn d * rn| < 2 ^ ℓ)
    (hda : d * d + 2 * d + 10 < 2 ^ ℓa) (hl : 1 ≤ ℓ) (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) :
    XRunsB L X ℓa ℓ (xpreC1 L) σ (d * 6 + 6 + (1 + (1 + (1 + (1 + (1 + 1)))))) (fun σ' =>
      σ'.sc 135 = pdn dn d ∧ σ'.sc 100 = rn ∧ σ'.sc 101 = rd ∧ σ'.sc 140 = ((pdn dn d * rn : ℤ) : ℝ) ∧
      σ'.nat 17 = d * d ∧ σ'.draws = σ.draws ∧ FrameA SPC NPC (fun _ _ => False) σ σ') := by
  have hPpos := pdn_pos hdn d
  unfold xpreC1
  refine XV.seq (XV.denL (X := X) hL hNS hNN hdn hin hoff hD h1 hP (by omega) hl) fun σ1 ⟨e1P, d1, F1⟩ => ?_
  have hD1 : σ1.nat rD = d := (F1.1 rD (by simp only [NDen, rD]; omega)).trans hD
  refine XV.seq (XV.nconst hL (i := 12) (by omega) 4 (by omega)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.rdIn (X := X) hL (x := 100) (i := 12) (by omega) (by omega) (by esimp; omega) (by esimp; omega)
    (by esimp; rw [hi4, ← Int.cast_abs]; exact_mod_cast hrnl)) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.nconst hL (i := 12) (by omega) 5 (by omega)) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.rdIn (X := X) hL (x := 101) (i := 12) (by omega) (by omega) (by esimp; omega) (by esimp; omega)
    (by esimp; rw [hi5, ← Int.cast_abs, abs_of_pos hrd]; exact_mod_cast hrdl)) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.mulI hL (x := 140) (a := 135) (b := 100) (by omega) (by omega) (by omega) (u := pdn dn d) (v := rn)
    (by esimp; exact e1P) (by esimp; rw [hi4]) (by rw [abs_of_pos hPpos]; exact hP) hrnl hDR) fun σ6 e6 => ?_
  subst e6
  refine XV.mono (XV.nmul hL (i := 17) (a := rD) (b := rD) (by omega) (by bomega) (by bomega) (by esimp; rw [hD1]; omega)
    (by esimp; rw [hD1]; omega) (by esimp; rw [hD1]; nlinarith)) le_rfl fun σ7 e7 => ?_
  subst e7
  refine ⟨by esimp; exact e1P, by esimp; rw [hi4], by esimp; rw [hi5], by esimp, by esimp; rw [hD1], by simp [d1], ?_⟩
  exact (((((((F1.mono (fun y h => by simp only [SDen] at h; simp only [SPC]; omega)
    (fun j h => by simp only [NDen] at h; simp only [NPC]; omega) (fun _ _ h => h)).setNat (i := 12)
    (by simp only [NPC]; omega) _).setSc (x := 100) (by simp only [SPC]; omega) _).setNat (i := 12)
    (by simp only [NPC]; omega) _).setSc (x := 101) (by simp only [SPC]; omega) _).setSc (x := 140)
    (by simp only [SPC]; omega) _).setNat (i := 17) (by simp only [NPC]; omega) _)

/-- The units of the centre block. -/
abbrev preCK (d : ℕ) : ℕ := d * 6 + 6 + (1 + (1 + (1 + (1 + (1 + 1))))) + ((d * d) * (2 + 3) + 3 + (1 + (1 +
  (d * (18 + 3) + 3 + (1 + (2 + 2))))))

set_option maxHeartbeats 8000000 in
theorem XV.preC {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hd : 1 ≤ d) (hNS : 172 ≤ L.NS)
    (hNN : 48 ≤ L.NN) (hNA : 26 ≤ L.NA) {dn nm : ℕ → ℤ} (hdn : ∀ j, 0 < dn j)
    (hin : ∀ j < d, X.inp (9 + 2 * j) = dn j) (hinN : ∀ j < d, X.inp (8 + 2 * j) = nm j) (hoff : 8 + 2 * d ≤ X.off)
    {rn rd : ℤ} (hi4 : X.inp 4 = rn) (hi5 : X.inp 5 = rd) (hrd : 0 < rd) (hrdl : rd < 2 ^ ℓ) (hrnl : |rn| < 2 ^ ℓ)
    (hP : pdn dn d < 2 ^ ℓ) (hNP : ∀ j < d, |nm j| * pdn dn d * rd < 2 ^ ℓ) (hDR : |pdn dn d * rn| < 2 ^ ℓ)
    (hda : d * d + 2 * d + 10 < 2 ^ ℓa) (hl : 1 ≤ ℓ) (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1)
    (hz : σ.sc sZ = 0) (h26 : σ.sc 26 = 1) :
    XRunsB L X ℓa ℓ (xpreC L) σ (preCK d) (fun σ' =>
      σ'.arr aKa 0 = ((pdn dn d : ℤ) : ℝ) ∧ (∀ i < d, σ'.arr aKa (1 + i) = ((cnum nm dn (pdn dn d) i : ℤ) : ℝ)) ∧
      σ'.arr aKg 0 = 1 ∧ (∀ i < d, σ'.arr aKg (1 + i) = 0) ∧
      (∀ i < d, σ'.arr aT i = ((cnum nm dn (pdn dn d) i * rd : ℤ) : ℝ)) ∧
      (∀ i < d, σ'.arr (aT + 1) (d * i + i) = ((pdn dn d * rn : ℤ) : ℝ)) ∧
      (∀ m < d * d, (∀ i < d, m ≠ d * i + i) → σ'.arr (aT + 1) m = 0) ∧
      σ'.sc 100 = rn ∧ σ'.sc 101 = rd ∧ σ'.draws = σ.draws ∧ FrameA SPC NPC ACen σ σ') := by
  have hPpos := pdn_pos hdn d
  unfold xpreC
  refine XV.seq (XV.preC1 hL hNS hNN hdn hin hoff hi4 hi5 hrd hrdl hrnl hP hDR hda hl hD h1)
    fun σ1 ⟨p135, p100, p101, p140, p17, d1, F1⟩ => ?_
  have hD1 : σ1.nat rD = d := (F1.1 rD (by simp only [NPC, rD]; omega)).trans hD
  have hO1 : σ1.nat rOne = 1 := (F1.1 rOne (by simp only [NPC, rOne]; omega)).trans h1
  have hz1 : σ1.sc sZ = 0 := (F1.2.1 sZ (by simp only [SPC, sZ]; omega)).trans hz
  have h261 : σ1.sc 26 = 1 := (F1.2.1 26 (by simp only [SPC]; omega)).trans h26
  -- the zero loop
  refine XV.seq (XV.zeroM (X := X) hL (aR := aT + 1) (sZ := sZ) (nl := 18) (nm := 17) (none := rOne)
    (M := d * d) (by simp only [aT]; omega) (by simp only [sZ]; omega) (by omega) (by omega) (by bomega) (by decide)
    (by decide) p17 hO1 (by unfold asz; omega) (by omega) hz1) fun σ2 ⟨z2, d2, F2⟩ => ?_
  have n2 : ∀ j, j ≠ 18 → σ2.nat j = σ1.nat j := fun j h => F2.1 j h
  have s2 : ∀ y, σ2.sc y = σ1.sc y := fun y => F2.2.1 y id
  refine XV.seq (XV.nconst hL (i := 12) (by omega) 8 (by omega)) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.nconst hL (i := 15) (by omega) 0 (by omega)) fun σ4 e4 => ?_
  subst e4
  have k135 : ((σ2.setNat 12 8).setNat 15 0).sc 135 = pdn dn d := by esimp; rw [s2, p135]
  have k101 : ((σ2.setNat 12 8).setNat 15 0).sc 101 = rd := by esimp; rw [s2, p101]
  have k140 : ((σ2.setNat 12 8).setNat 15 0).sc 140 = ((pdn dn d * rn : ℤ) : ℝ) := by esimp; rw [s2, p140]
  have kZ : ((σ2.setNat 12 8).setNat 15 0).sc sZ = 0 := by esimp; rw [s2, hz1]
  have kD : ((σ2.setNat 12 8).setNat 15 0).nat rD = d := by esimp; rw [n2 rD (by decide), hD1]
  have kO : ((σ2.setNat 12 8).setNat 15 0).nat rOne = 1 := by esimp; rw [n2 rOne (by decide), hO1]
  -- the loop
  refine XV.seq (XV.forN hL (i := 11) (n := rD) (one := rOne) (by omega) (by bomega) (by bomega) (by decide)
    (by decide) d 18 (by omega) (JCen nm dn (pdn dn d) rn rd ((σ2.setNat 12 8).setNat 15 0)) _ kD kO
    ⟨by simp, by simp, by simp, (FrameA.refl _ _ _ _).setNat ⟨le_rfl, by omega⟩ _, fun i h => absurd h (by omega),
      fun i h => absurd h (by omega), fun i h => absurd h (by omega), fun i h => absurd h (by omega),
      fun m hm _ => by simp only [Env.setNat_arr]; exact z2 m hm⟩
    fun t ht σ' hJ ji jn jo => XV.cenB hL hNS hNN hNA hdn hin hinN hoff rfl hrd hrdl hP hNP hDR hda k135 k101 k140
      kZ t ht σ' hJ ji jn jo) fun σ5 ⟨⟨j12, j15, jdr, jF, A1, A2, A3, A4, A5⟩, ji, jn, jo⟩ => ?_
  -- `aKa[0] := D`, `aKg[0] := 1`
  have m135 : σ5.sc 135 = pdn dn d := (jF.2.1 135 (by simp only [SCen]; omega)).trans k135
  have m26 : σ5.sc 26 = 1 := by rw [jF.2.1 26 (by simp only [SCen]; omega)]; esimp; rw [s2, h261]
  have m100 : σ5.sc 100 = rn := by rw [jF.2.1 100 (by simp only [SCen]; omega)]; esimp; rw [s2, p100]
  refine XV.seq (XV.nconst hL (i := 16) (by omega) 0 (by omega)) fun σ6 e6 => ?_
  subst e6
  refine XV.seq (XV.aset hL (a := aKa) (i := 16) (x := 135) (by simp only [aKa, aT]; omega) (by omega) (by omega)
    (by esimp; unfold asz; nlinarith) (by esimp; rw [m135, ← Int.cast_abs, abs_of_pos hPpos]; exact_mod_cast hP))
    fun σ7 e7 => ?_
  subst e7
  refine XV.mono (XV.aset hL (a := aKg) (i := 16) (x := 26) (by simp only [aKg, aT]; omega) (by omega) (by omega)
    (by esimp; unfold asz; nlinarith) (by esimp; rw [m26, abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)))
    le_rfl fun σ8 e8 => ?_
  subst e8
  have G : FrameA SPC NPC ACen σ σ1 := F1.mono (fun _ h => h) (fun _ h => h) (fun _ _ h => h.elim)
  have G2 : FrameA SPC NPC ACen σ1 σ2 := F2.mono (fun _ h => h.elim) (fun j h => by simp only [NPC]; omega)
    (fun b k h => by simp only [ACen]; exact Or.inr (Or.inr (Or.inr h.1)))
  have G5 : FrameA SPC NPC ACen ((σ2.setNat 12 8).setNat 15 0) σ5 :=
    jF.mono (fun y h => by simp only [SCen] at h; simp only [SPC]; omega) (fun j h => by
      simp only [NCen] at h; simp only [NPC]; omega) (fun _ _ h => h)
  simp only [Env.setNat_arr, Env.setArr_arr, Env.setSc_arr, Env.setSc_nat, Env.setNat_nat, Env.setSc_sc,
    Env.setNat_sc, Env.setArr_sc, Env.setArr_nat, Env.setArr_draws, Env.setNat_draws, aKa, aT, aKg, Nat.reduceAdd,
    Nat.reduceEqDiff, ↓reduceIte, true_and, false_and, and_true, and_false]
  refine ⟨by rw [m135], fun i hi => ?_, by rw [m26], fun i hi => ?_, fun i hi => ?_, fun i hi => A4 i hi,
    fun m hm hm' => A5 m hm hm', m100, by rw [jF.2.1 101 (by simp only [SCen]; omega), k101], by
      rw [jdr]; simp [d2, d1], ?_⟩
  · (try split_ifs) <;> first | omega | exact A1 i hi
  · (try split_ifs) <;> first | omega | exact A3 i hi
  · exact A2 i hi
  · exact (((G.trans (G2.trans ((((FrameA.refl _ _ _ σ2).setNat (i := 12) (by simp only [NPC]; omega) _).setNat
      (i := 15) (by simp only [NPC]; omega) _).trans G5))).setNat (i := 16) (by simp only [NPC]; omega) _).setArr
      (b := aKa) (Or.inl rfl) _).setArr (b := aKg) (Or.inr (Or.inr (Or.inl rfl))) _

end AdversarialBco.Unified.ProgO.TriO
