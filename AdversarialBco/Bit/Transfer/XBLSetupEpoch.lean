/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSetupRows
public import AdversarialBco.Bit.Transfer.XBLSetupPrm

@[expose] public section

/-!
# BL's setup on the machine: the epoch start and P5's mode

`xepoch`: `first := 1`, `D_μ := 1`, the diagonals of `A'` and `B'` (cells `(d + 1) k`, `k < d`, of `aA` and `aB`) from
the slots `sA0`, `sB0`. `xmode`: `sMode := 2` unless the flag `sBadS` is positive or `2^pF < 2 ε̂`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

/-- The epoch start in mode `run`. -/
def xepoch (L : Layout) : XCmd :=
  .seq (toX (VL.sconst L sFirst 1)) (.seq (toX (VL.sconst L sDmu 1)) (.seq (.prim (.frag (.nadd 10 rD rOne)))
  (.seq (.prim (.frag (.nconst 8 0))) (.seq (xmapE L sZ 128 (.sc sA0) aA 8 10 9 rD rOne)
  (.seq (.prim (.frag (.nconst 8 0))) (xmapE L sZ 128 (.sc sB0) aB 8 10 9 rD rOne))))))

/-- The units of `xepoch`. -/
def epochUnits (d : ℕ) : ℕ := 1 + (1 + (1 + (1 + ((d * (1 + 6) + 3) + (1 + (d * (1 + 6) + 3))))))

/-- The cells `xepoch` changes. -/
def SE (y : ℕ) : Prop := y = sFirst ∨ y = sDmu ∨ 128 ≤ y
def NE (j : ℕ) : Prop := j = 8 ∨ j = 9 ∨ j = 10
def AE (a c : ℕ) : Prop := (a = aA ∨ a = aB) ∧ ∃ k < d, c = 0 + (d + 1) * k

set_option maxHeartbeats 2000000 in
/-- **The epoch start on the machine.** -/
theorem XV.epoch {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hNS : 172 ≤ L.NS) (hNN : 48 ≤ L.NN)
    (hNA : 16 ≤ L.NA) {σ : Env d} {E : ℕ} {a0 b0 : ℤ} (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1)
    (hz : σ.sc sZ = 0) (hA0 : σ.sc sA0 = a0) (hB0 : σ.sc sB0 = b0) (ba : |a0| ≤ 2 ^ E) (bb : |b0| ≤ 2 ^ E)
    (hE : E < ℓ) :
    XRunsB L X ℓa ℓ (xepoch L) σ (epochUnits d) (fun σ' =>
      σ'.sc sFirst = 1 ∧ σ'.sc sDmu = 1 ∧ (∀ k < d, σ'.arr aA (0 + (d + 1) * k) = a0) ∧
      (∀ k < d, σ'.arr aB (0 + (d + 1) * k) = b0) ∧ σ'.draws = σ.draws ∧ FrameA SE NE (AE (d := d)) σ σ') := by
  have hL1 := hL.1
  have hda := asz_lt hL (a := 0) (by omega)
  unfold asz at hda
  have hdd : d ≤ d * d := Nat.le_mul_self d
  have h1l : |((1 : ℚ) : ℝ)| < 2 ^ ℓ := by
    rw [Rat.cast_one, abs_one]; exact_mod_cast Nat.one_lt_two_pow (by omega : ℓ ≠ 0)
  have hcell : ∀ k < d, 0 + (d + 1) * k < asz d := fun k hk => by unfold asz; nlinarith
  refine XV.seq (XV.sconst hL (x := sFirst) (by bomega) 1 rfl h1l) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.sconst hL (x := sDmu) (by bomega) 1 rfl h1l) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.nadd hL (i := 10) (a := rD) (b := rOne) (by bomega) (by bomega) (by bomega)
    (by simp only [Env.setSc_nat, hD]; omega) (by simp only [Env.setSc_nat, h1]; omega)) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.nconst hL (i := 8) (by bomega) 0 (by omega)) fun σ4 e4 => ?_
  subst e4
  set σ4 := (((σ.setSc sFirst ((1 : ℚ) : ℝ)).setSc sDmu ((1 : ℚ) : ℝ)).setNat 10
    (((σ.setSc sFirst ((1 : ℚ) : ℝ)).setSc sDmu ((1 : ℚ) : ℝ)).nat rD +
      ((σ.setSc sFirst ((1 : ℚ) : ℝ)).setSc sDmu ((1 : ℚ) : ℝ)).nat rOne)).setNat 8 0 with hσ4
  have n4 : σ4.nat rD = d ∧ σ4.nat rOne = 1 ∧ σ4.nat 10 = d + 1 ∧ σ4.nat 8 = 0 := by
    simp [hσ4, hD, h1]
  have s4 : ∀ y, y ≠ sFirst → y ≠ sDmu → σ4.sc y = σ.sc y := fun y h h' => by
    simp [hσ4, h, h']
  have G4 : FrameA SE NE (AE (d := d)) σ σ4 :=
    ((((FrameA.refl _ _ _ σ).setSc (Or.inl rfl) _).setSc (Or.inr (Or.inl rfl)) _).setNat
      (i := 10) (Or.inr (Or.inr rfl)) _).setNat (i := 8) (Or.inl rfl) _
  refine XV.seq (XV.mapEx (E := E) (N := d) (base := 0) (st := d + 1) (F := fun _ => a0) hL (z := sZ) (t := 128)
    (e := .sc sA0) (aB := aA) (nr := 8) (nst := 10) (nk := 9) (nn := rD) (none := rOne)
    (by show sA0 < 128; bomega) (by bomega) (by simp only [IE.scr]; omega) (by rw [s4 _ (by bomega) (by bomega), hz])
    (by bomega) (by bomega) (by bomega) (by bomega) (by bomega) (by bomega) (by decide) (by decide) (by decide)
    n4.1 n4.2.1 n4.2.2.2 n4.2.2.1 (by omega) hcell (by omega) (by nlinarith) (by omega) hE
    (fun k hk σ' hF _ _ _ => ?_)) fun σ5 ⟨c5, r5, d5, F5⟩ => ?_
  · have : σ'.sc sA0 = a0 := by rw [hF.2.1 _ (by bomega), s4 _ (by bomega) (by bomega), hA0]
    exact ⟨⟨a0, this, ba⟩, by simp only [IE.eval]; exact this⟩
  have n5 : σ5.nat rD = d ∧ σ5.nat rOne = 1 ∧ σ5.nat 10 = d + 1 := by
    refine ⟨?_, ?_, ?_⟩ <;> rw [F5.1 _ (by bomega)]
    exacts [n4.1, n4.2.1, n4.2.2.1]
  have s5 : ∀ y, y < 128 → σ5.sc y = σ4.sc y := fun y hy => F5.2.1 y (by omega)
  refine XV.seq (XV.nconst hL (i := 8) (by bomega) 0 (by omega)) fun σ6 e6 => ?_
  subst e6
  refine XV.mono (XV.mapEx (E := E) (N := d) (base := 0) (st := d + 1) (F := fun _ => b0) hL (z := sZ) (t := 128)
    (e := .sc sB0) (aB := aB) (nr := 8) (nst := 10) (nk := 9) (nn := rD) (none := rOne)
    (by show sB0 < 128; bomega) (by bomega) (by simp only [IE.scr]; omega)
    (by rw [Env.setNat_sc, s5 _ (by bomega), s4 _ (by bomega) (by bomega), hz])
    (by bomega) (by bomega) (by bomega) (by bomega) (by bomega) (by bomega) (by decide) (by decide) (by decide)
    (by rw [Env.setNat_nat, if_neg (by bomega), n5.1]) (by rw [Env.setNat_nat, if_neg (by bomega), n5.2.1])
    (by rw [Env.setNat_nat, if_pos rfl]) (by rw [Env.setNat_nat, if_neg (by bomega), n5.2.2]) (by omega) hcell
    (by omega) (by nlinarith) (by omega) hE (fun k hk σ' hF _ _ _ => ?_)) le_rfl fun σ7 ⟨c7, r7, d7, F7⟩ => ?_
  · have : σ'.sc sB0 = b0 := by
      rw [hF.2.1 _ (by bomega), Env.setNat_sc, s5 _ (by bomega), s4 _ (by bomega) (by bomega), hB0]
    exact ⟨⟨b0, this, bb⟩, by simp only [IE.eval]; exact this⟩
  have s7 : ∀ y, y < 128 → σ7.sc y = σ4.sc y := fun y hy => by
    rw [F7.2.1 y (by omega), Env.setNat_sc, s5 y hy]
  refine ⟨by rw [s7 _ (by bomega)]; simp [hσ4], by rw [s7 _ (by bomega)]; simp [hσ4], fun k hk => ?_, c7,
    by rw [d7, Env.setNat_draws, d5]; simp [hσ4], ?_⟩
  · rw [F7.2.2.1 _ _ (fun h => by simp only [aA, aB] at h; omega), Env.setNat_arr]; exact c5 k hk
  · have G5 : FrameA SE NE (AE (d := d)) σ4 σ5 :=
      F5.mono (fun y h => Or.inr (Or.inr h)) (fun j h => by simp only [NE]; omega)
        (fun b c h => ⟨Or.inl h.1, h.2⟩)
    have G7 : FrameA SE NE (AE (d := d)) (σ5.setNat 8 0) σ7 :=
      F7.mono (fun y h => Or.inr (Or.inr h)) (fun j h => by simp only [NE]; omega)
        (fun b c h => ⟨Or.inr h.1, h.2⟩)
    exact ((G4.trans G5).setNat (i := 8) (Or.inl rfl) _).trans G7

/-- P5's mode: `sMode := 2` unless the flag is positive or `2^pF < 2 ε̂` (`ε' > 1/2`). -/
def xmode (L : Layout) : XCmd :=
  .seq (toX (VL.sop2 L .add 124 sEps sEps))
  (xifS L sZ sBadS .skip (xifS L s2pF 124 .skip (toX (VL.sconst L sMode 2))))

set_option maxHeartbeats 1000000 in
/-- **P5's mode on the machine.** -/
theorem XV.mode {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hNS : 172 ≤ L.NS) {σ : Env d}
    {fl PF ep : ℤ} (hz : σ.sc sZ = 0) (hfl : σ.sc sBadS = fl) (hPF : σ.sc s2pF = PF) (hep : σ.sc sEps = ep)
    (hm : σ.sc sMode = 0) (bfl : |fl| < 2 ^ ℓ) (bPF : |PF| < 2 ^ ℓ) (bep : |2 * ep| < 2 ^ ℓ) (h2 : 2 < ℓ) :
    XRunsB L X ℓa ℓ (xmode L) σ 6 (fun σ' =>
      σ'.sc sMode = (if 0 < fl ∨ PF < 2 * ep then 0 else 2 : ℤ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = sMode ∨ y = 124) (fun _ => False) (fun _ _ => False) σ σ') := by
  have bep1 : |(ep : ℝ)| < 2 ^ ℓ := by
    have h1 : |ep| ≤ |2 * ep| := by rw [abs_mul]; norm_num; linarith [abs_nonneg ep]
    exact_mod_cast h1.trans_lt bep
  refine XV.mono (K := 1 + 5) ?_ (by norm_num) fun _ h => h
  refine XV.seq (XV.sop2 hL (x := 124) (a := sEps) (b := sEps) (by omega) (by bomega) (by bomega) .add
    (by intro h; cases h) (by rw [hep]; exact bep1) (by rw [hep]; exact bep1)
    (by simp only [RealRAM.Op2.eval, hep]; exact_mod_cast (show |ep + ep| < 2 ^ ℓ by rw [← two_mul]; exact bep)))
    fun σ1 e1 => ?_
  subst e1
  have z1 : (σ.setSc 124 (RealRAM.Op2.eval .add (σ.sc sEps) (σ.sc sEps))).sc sZ = 0 := by
    rw [Env.setSc_sc, if_neg (by bomega), hz]
  have f1 : (σ.setSc 124 (RealRAM.Op2.eval .add (σ.sc sEps) (σ.sc sEps))).sc sBadS = fl := by
    rw [Env.setSc_sc, if_neg (by decide), hfl]
  have p1 : (σ.setSc 124 (RealRAM.Op2.eval .add (σ.sc sEps) (σ.sc sEps))).sc s2pF = PF := by
    rw [Env.setSc_sc, if_neg (by bomega), hPF]
  have e1 : (σ.setSc 124 (RealRAM.Op2.eval .add (σ.sc sEps) (σ.sc sEps))).sc 124 = ((2 * ep : ℤ) : ℝ) := by
    rw [Env.setSc_sc, if_pos rfl]; simp only [RealRAM.Op2.eval, hep]; push_cast; ring
  have m1 : (σ.setSc 124 (RealRAM.Op2.eval .add (σ.sc sEps) (σ.sc sEps))).sc sMode = 0 := by
    rw [Env.setSc_sc, if_neg (by bomega), hm]
  have F1 : FrameA (fun y => y = sMode ∨ y = 124) (fun _ => False) (fun _ _ => False) σ
      (σ.setSc 124 (RealRAM.Op2.eval .add (σ.sc sEps) (σ.sc sEps))) :=
    (FrameA.refl _ _ _ σ).setSc (Or.inr rfl) _
  have h0l : |(σ.setSc 124 (RealRAM.Op2.eval .add (σ.sc sEps) (σ.sc sEps))).sc sZ| < 2 ^ ℓ := by
    rw [z1]; simp
  have hfll : |(σ.setSc 124 (RealRAM.Op2.eval .add (σ.sc sEps) (σ.sc sEps))).sc sBadS| < 2 ^ ℓ := by
    rw [f1]; exact_mod_cast bfl
  by_cases hf : 0 < fl
  · refine XV.mono (XV.ifS_t hL (by bomega) (by simp only [sBadS]; omega) h0l hfll
      (by rw [z1, f1]; exact_mod_cast hf)
      (XV.skip _)) (by omega) fun σ' e => ?_
    subst e
    exact ⟨by rw [m1, if_pos (Or.inl hf)]; simp, rfl, F1⟩
  · have hpl : |(σ.setSc 124 (RealRAM.Op2.eval .add (σ.sc sEps) (σ.sc sEps))).sc s2pF| < 2 ^ ℓ := by
      rw [p1]; exact_mod_cast bPF
    have hel : |(σ.setSc 124 (RealRAM.Op2.eval .add (σ.sc sEps) (σ.sc sEps))).sc 124| < 2 ^ ℓ := by
      rw [e1]; exact_mod_cast bep
    refine XV.mono (XV.ifS_f (K := 3) hL (by bomega) (by simp only [sBadS]; omega) h0l hfll
      (by rw [z1, f1]; exact_mod_cast hf) ?_) le_rfl
      fun _ h => h
    by_cases hp : PF < 2 * ep
    · refine XV.mono (XV.ifS_t hL (by bomega) (by omega) hpl hel (by rw [p1, e1]; exact_mod_cast hp)
        (XV.skip _)) (by omega) fun σ' e => ?_
      subst e
      exact ⟨by rw [m1, if_pos (Or.inr hp)]; simp, rfl, F1⟩
    · have h2l : |((2 : ℚ) : ℝ)| < 2 ^ ℓ := by
        rw [abs_of_pos (by norm_num)]; norm_num
        exact lt_of_lt_of_le (by norm_num) (pow_le_pow_right₀ (by norm_num) (by omega : 2 ≤ ℓ))
      refine XV.mono (XV.ifS_f hL (by bomega) (by omega) hpl hel (by rw [p1, e1]; exact_mod_cast hp)
        (XV.sconst hL (x := sMode) (by bomega) 2 rfl h2l)) le_rfl fun σ' e => ?_
      subst e
      refine ⟨by rw [Env.setSc_sc, if_pos rfl, if_neg (by tauto)]; simp, rfl, F1.setSc (Or.inl rfl) _⟩

end AdversarialBco.Bit.Transfer.BLM
