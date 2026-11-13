/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriStage
public import AdversarialBco.Bit.Transfer.XTriAux

@[expose] public section

/-!
# TRI-M, the initial position and the stages on the machine

* `xinit`, `XV.init`: the initial position `P_0 = (2ĉ, D_c I)/(2 D_c)` from the frame centre.
* `xstages`, `XV.stages`: the `m_st` stages, one `xstage` each, with the invariant `StAt`.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM Matrix

variable {d : ℕ}

/-- The position after stage `j` in the machine: `P_j` in `a`, `a + 1`, `o`, with `2^{1 + j G_c}` in `o + 14` and
`2^j D_j` in `o + 15`. -/
def StAt (σ : Env d) (o a Gc j : ℕ) (P : StZ d) : Prop :=
  (∀ l : Fin d, σ.arr a l = P.mu l) ∧ (∀ i l : Fin d, σ.arr (a + 1) (d * i + l) = P.T i l) ∧ σ.sc o = P.D ∧
    σ.sc (o + 14) = ((2 ^ (1 + j * Gc) : ℤ) : ℝ) ∧ σ.sc (o + 15) = ((2 ^ j * P.D : ℤ) : ℝ)

/-! ## The initial position -/

/-- The initial position `P_0 = (2ĉ, D_c I)/(2 D_c)` from the frame centre in `aC` (`D_c` in cell `0`, `ĉ_i` in cell
`i + 1`): `2 D_c` in `o` and `o + 15`, `2` in `o + 14`, `T̂ = D_c I` in `a + 1`, then `μ̂ = 2ĉ` in `a`. -/
def xinit (L : Layout) (o r a nd aC : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst (r + 3) 0)))
  (.seq (toX (VL.aget L (o + 16) aC (r + 3)))
  (.seq (toX (VL.sop2 L .add o (o + 16) (o + 16)))
  (.seq (toX (VL.sop2 L .add (o + 15) o (o + 1)))
  (.seq (toX (VL.sconst L (o + 14) 2))
  (.seq (xscalI L (o + 1) (o + 40) (o + 16) (a + 1) (r + 4) r (r + 1) (r + 5) nd (r + 25) r)
  (xforN (r + 5) nd r (.seq (.prim (.frag (.nadd (r + 4) (r + 5) r)))
    (.seq (toX (VL.aget L (o + 17) aC (r + 4)))
    (.seq (toX (VL.sop2 L .add (o + 17) (o + 17) (o + 17))) (toX (VL.aset L a (r + 5) (o + 17))))))))))))

/-- The units of `xinit`. -/
abbrev initK (d : ℕ) : ℕ :=
  1 + (2 + (1 + (1 + (1 + (1 + (d * d * (1 + 6) + 3) + (1 + (d * (1 + 6) + 3)) + (d * (1 + (2 + (1 + 2)) + 3) + 3))))))

set_option maxHeartbeats 4000000 in
theorem XV.init {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {o r a nd aC s Gc : ℕ} {Dc : ℤ} {ch : Fin d → ℤ} (hd : 1 ≤ d)
    (hS : o + 41 ≤ L.NS) (hN : r + 26 ≤ L.NN) (hA : a + 2 ≤ L.NA) (hnd : nd < r) (haC : aC < a)
    (hσd : σ.nat nd = d) (hσ1 : σ.nat r = 1) (hσd1 : σ.nat (r + 1) = d + 1) (hσdd : σ.nat (r + 25) = d * d)
    (eZ : σ.sc (o + 1) = 0) (eD : σ.arr aC 0 = Dc) (eC : ∀ i : Fin d, σ.arr aC (i + 1) = ch i)
    (bD : |Dc| ≤ 2 ^ s) (bC : ∀ i, |ch i| ≤ 2 ^ s) (hs : s + 2 < ℓ) :
    XRunsB L X ℓa ℓ (xinit L o r a nd aC) σ (initK d) (fun σ' =>
      StAt σ' o a Gc 0 ⟨2 * Dc, fun i => 2 * ch i, Dc • 1⟩ ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = o ∨ y = o + 14 ∨ y = o + 15 ∨ y = o + 16 ∨ y = o + 17 ∨ o + 40 ≤ y)
        (fun j => r + 3 ≤ j ∧ j < r + 6)
        (fun b c => b = a ∧ c < d ∨ b = a + 1 ∧ c < d * d) σ σ') := by
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  have hda : d * d + d < 2 ^ ℓa := asz_lt hL (show a < L.NA by omega)
  have hcell : ∀ k ≤ d, k < asz d := fun k hk => by unfold asz; have := Nat.mul_pos hd hd; clear * - hk this; omega
  have bDs : |(Dc : ℝ)| < 2 ^ ℓ := tabsR_lt bD (by omega)
  have bD2 : |2 * Dc| ≤ 2 ^ (s + 1) := by
    rw [abs_mul, pow_succ]; norm_num; linarith
  -- `D := 2 D_c`, `2^0 D`, `2^1`
  refine XV.seq (XV.nconst hL (show r + 3 < L.NN by omega) 0 (by positivity)) fun σ1 e1 => ?_
  have G1 : FrameA (fun y => y = o ∨ y = o + 14 ∨ y = o + 15 ∨ y = o + 16 ∨ y = o + 17 ∨ o + 40 ≤ y)
        (fun j => r + 3 ≤ j ∧ j < r + 6)
      (fun b c => b = a ∧ c < d ∨ b = a + 1 ∧ c < d * d) σ σ1 := by
    rw [e1]; exact (FrameA.refl _ _ _ σ).setNat (show r + 3 ≤ r + 3 ∧ r + 3 < r + 6 by omega) 0
  have k1 : σ1.nat (r + 3) = 0 := by rw [e1, nat_setNat_eq]
  refine XV.seq (XV.aget hL (x := o + 16) (a := aC) (i := r + 3) (by omega) (by omega) (by omega)
    (by rw [k1]; exact hcell 0 (Nat.zero_le _))
    (by rw [k1, G1.2.2.1 aC 0 (by omega), eD]; exact bDs)) fun σ2 e2 => ?_
  have v2 : σ2.sc (o + 16) = Dc := by rw [e2, sc_setSc_eq, k1, G1.2.2.1 aC 0 (by omega), eD]
  have G2 : FrameA (fun y => y = o ∨ y = o + 14 ∨ y = o + 15 ∨ y = o + 16 ∨ y = o + 17 ∨ o + 40 ≤ y)
        (fun j => r + 3 ≤ j ∧ j < r + 6)
      (fun b c => b = a ∧ c < d ∨ b = a + 1 ∧ c < d * d) σ σ2 := by
    rw [e2]; exact G1.setSc (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _
  refine XV.seq (XV.sop2 hL (x := o) (a := o + 16) (b := o + 16) (by omega) (by omega) (by omega) .add
    (by intro h; cases h) (by rw [v2]; exact bDs) (by rw [v2]; exact bDs)
    (by rw [v2]; simp only [RealRAM.Op2.eval]; rw [← Int.cast_add]
        exact tabsR_lt (absI_add_le bD bD) (by omega))) fun σ3 e3 => ?_
  have v3 : σ3.sc o = ((2 * Dc : ℤ) : ℝ) := by
    rw [e3, sc_setSc_eq, v2]; simp only [RealRAM.Op2.eval]; push_cast; ring
  have G3 : FrameA (fun y => y = o ∨ y = o + 14 ∨ y = o + 15 ∨ y = o + 16 ∨ y = o + 17 ∨ o + 40 ≤ y)
        (fun j => r + 3 ≤ j ∧ j < r + 6)
      (fun b c => b = a ∧ c < d ∨ b = a + 1 ∧ c < d * d) σ σ3 := by
    rw [e3]; exact G2.setSc (Or.inl rfl) _
  have z3 : σ3.sc (o + 1) = 0 := by rw [G3.2.1 (o + 1) (by omega), eZ]
  refine XV.seq (XV.sop2 hL (x := o + 15) (a := o) (b := o + 1) (by omega) (by omega) (by omega) .add
    (by intro h; cases h) (by rw [v3]; exact tabsR_lt bD2 (by omega)) (by rw [z3]; simp)
    (by rw [v3, z3]; simp only [RealRAM.Op2.eval, add_zero]; exact tabsR_lt bD2 (by omega))) fun σ4 e4 => ?_
  have v4 : σ4.sc (o + 15) = ((2 * Dc : ℤ) : ℝ) := by
    rw [e4, sc_setSc_eq, v3, z3]; simp only [RealRAM.Op2.eval, add_zero]
  have G4 : FrameA (fun y => y = o ∨ y = o + 14 ∨ y = o + 15 ∨ y = o + 16 ∨ y = o + 17 ∨ o + 40 ≤ y)
        (fun j => r + 3 ≤ j ∧ j < r + 6)
      (fun b c => b = a ∧ c < d ∨ b = a + 1 ∧ c < d * d) σ σ4 := by
    rw [e4]; exact G3.setSc (Or.inr (Or.inr (Or.inl rfl))) _
  have h2ℓ : |((2 : ℚ) : ℝ)| < 2 ^ ℓ := by
    rw [show ((2 : ℚ) : ℝ) = ((2 : ℤ) : ℝ) by norm_num]
    exact tabsR_lt (F := 1) (by norm_num) (by omega)
  refine XV.seq (XV.sconst hL (x := o + 14) (by omega) 2 rfl h2ℓ) fun σ5 e5 => ?_
  have G5 : FrameA (fun y => y = o ∨ y = o + 14 ∨ y = o + 15 ∨ y = o + 16 ∨ y = o + 17 ∨ o + 40 ≤ y)
        (fun j => r + 3 ≤ j ∧ j < r + 6)
      (fun b c => b = a ∧ c < d ∨ b = a + 1 ∧ c < d * d) σ σ5 := by
    rw [e5]; exact G4.setSc (Or.inr (Or.inl rfl)) _
  have v5o : σ5.sc o = ((2 * Dc : ℤ) : ℝ) := by rw [e5, sc_setSc_ne _ (by omega), e4, sc_setSc_ne _ (by omega), v3]
  have v5q : σ5.sc (o + 15) = ((2 * Dc : ℤ) : ℝ) := by rw [e5, sc_setSc_ne _ (by omega), v4]
  have v5p : σ5.sc (o + 14) = 2 := by rw [e5, sc_setSc_eq]; norm_num
  have v5d : σ5.sc (o + 16) = Dc := by
    rw [e5, sc_setSc_ne _ (by omega), e4, sc_setSc_ne _ (by omega), e3, sc_setSc_ne _ (by omega), v2]
  have dr5 : σ5.draws = σ.draws := by
    rw [e5, Env.setSc_draws, e4, Env.setSc_draws, e3, Env.setSc_draws, e2, Env.setSc_draws, e1, Env.setNat_draws]
  have n5 : ∀ j, ¬ (r + 3 ≤ j ∧ j < r + 6) → σ5.nat j = σ.nat j := fun j h => G5.1 j h
  -- `T̂ := D_c I`
  refine XV.seq (XV.scalI hL (z := o + 1) (t := o + 40) (s := o + 16) (aB := a + 1) (nr := r + 4) (n1 := r)
    (nd1 := r + 1) (nk := r + 5) (nd := nd) (ndd := r + 25) (none := r) (E := s) (v := Dc) (by omega) (by omega)
    (by omega) (by rw [G5.2.1 (o + 1) (by omega), eZ]) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
    (by simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
      and_true, not_false_eq_true]; omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [n5 nd (by omega), hσd]) (by rw [n5 (r + 25) (by omega), hσdd]) (by rw [n5 r (by omega), hσ1])
    (by rw [n5 r (by omega), hσ1]) (by rw [n5 (r + 1) (by omega), hσd1]) hda v5d bD (by omega))
    fun σ6 ⟨t6, d6, F6⟩ => ?_
  have G6 : FrameA (fun y => y = o ∨ y = o + 14 ∨ y = o + 15 ∨ y = o + 16 ∨ y = o + 17 ∨ o + 40 ≤ y)
        (fun j => r + 3 ≤ j ∧ j < r + 6)
      (fun b c => b = a ∧ c < d ∨ b = a + 1 ∧ c < d * d) σ σ6 :=
    G5.trans (F6.mono (fun y h => by omega) (fun j h => by omega) (fun b c h => Or.inr h))
  have n6 : ∀ j, ¬ (r + 3 ≤ j ∧ j < r + 6) → σ6.nat j = σ.nat j := fun j h => G6.1 j h
  -- `μ̂ := 2ĉ`
  let J : ℕ → Env d → Prop := fun i σ' =>
    (∀ i' (_ : i' < i) (h : i' < d), σ'.arr a i' = ((2 * ch ⟨i', h⟩ : ℤ) : ℝ)) ∧ σ'.draws = σ6.draws ∧
    FrameA (fun y => y = o + 17) (fun j => j = r + 4 ∨ j = r + 5) (fun b c => b = a ∧ c < i) σ6 σ'
  refine XV.mono (XV.forN (L := L) (X := X) (ℓ := ℓ) (i := r + 5) (n := nd) (one := r) hL (by omega) (by omega)
    (by omega) (by omega) (by omega) d (1 + (2 + (1 + 2))) (by omega) J σ6 (by rw [n6 nd (by omega), hσd])
    (by rw [n6 r (by omega), hσ1])
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), by rw [Env.setNat_draws],
      (FrameA.refl _ _ _ σ6).setNat (Or.inr rfl) 0⟩ ?_) le_rfl ?_
  · intro i hi σ' ⟨jA, jd, jF⟩ hki hkn hk1
    refine XV.seq (XV.nadd hL (i := r + 4) (a := r + 5) (b := r) (by omega) (by omega) (by omega)
      (by rw [hki]; omega) (by rw [hk1]; omega)) fun σa ea => ?_
    have ka : σa.nat (r + 4) = i + 1 := by rw [ea, nat_setNat_eq, hki, hk1]
    have aa : σa.arr = σ'.arr := by rw [ea]; rfl
    have ca : σa.arr aC (i + 1) = ch ⟨i, hi⟩ := by
      rw [aa, jF.2.2.1 aC (i + 1) (by omega), F6.2.2.1 aC (i + 1) (by omega), G5.2.2.1 aC (i + 1) (by omega)]
      exact eC ⟨i, hi⟩
    refine XV.seq (XV.aget hL (x := o + 17) (a := aC) (i := r + 4) (by omega) (by omega) (by omega)
      (by rw [ka]; exact hcell (i + 1) hi) (by rw [ka, ca]; exact tabsR_lt (bC _) (by omega))) fun σb eb => ?_
    have vb : σb.sc (o + 17) = ch ⟨i, hi⟩ := by rw [eb, sc_setSc_eq, ka, ca]
    have bC2 : |2 * ch ⟨i, hi⟩| ≤ 2 ^ (s + 1) := by
      rw [abs_mul, pow_succ]; norm_num; linarith [bC ⟨i, hi⟩]
    refine XV.seq (XV.sop2 hL (x := o + 17) (a := o + 17) (b := o + 17) (by omega) (by omega) (by omega) .add
      (by intro h; cases h) (by rw [vb]; exact tabsR_lt (bC _) (by omega))
      (by rw [vb]; exact tabsR_lt (bC _) (by omega))
      (by rw [vb]; simp only [RealRAM.Op2.eval]; rw [← Int.cast_add]
          exact tabsR_lt (absI_add_le (bC _) (bC _)) (by omega))) fun σc ec => ?_
    have vc : σc.sc (o + 17) = ((2 * ch ⟨i, hi⟩ : ℤ) : ℝ) := by
      rw [ec, sc_setSc_eq, vb]; simp only [RealRAM.Op2.eval]; push_cast; ring
    have nc : ∀ j, j ≠ r + 4 → σc.nat j = σ'.nat j := fun j h => by
      rw [ec, Env.setSc_nat, eb, Env.setSc_nat, ea, nat_setNat_ne _ h]
    have kc : σc.nat (r + 5) = i := by rw [nc (r + 5) (by omega), hki]
    refine XV.mono (XV.aset hL (a := a) (i := r + 5) (x := o + 17) (by omega) (by omega) (by omega)
      (by rw [kc]; exact hcell i hi.le) (by rw [vc]; exact tabsR_lt bC2 (by omega))) le_rfl ?_
    rintro σd rfl
    refine ⟨by rw [Env.setArr_nat, kc], by rw [Env.setArr_nat, nc nd (by omega), hkn],
      by rw [Env.setArr_nat, nc r (by omega), hk1], fun i' hi' hd => ?_, ?_, ?_⟩
    · rw [Env.setNat_arr, Env.setArr_arr, kc, vc]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hlt | rfl
      · rw [if_neg (by omega)]
        have : σc.arr = σ'.arr := by rw [ec, Env.setSc_arr, eb, Env.setSc_arr, aa]
        rw [this]; exact jA i' hlt hd
      · rw [if_pos ⟨rfl, rfl⟩]
    · rw [Env.setNat_draws, Env.setArr_draws, ec, Env.setSc_draws, eb, Env.setSc_draws, ea, Env.setNat_draws, jd]
    · have Fc : FrameA (fun y => y = o + 17) (fun j => j = r + 4 ∨ j = r + 5) (fun b c => b = a ∧ c < i + 1)
          σ6 σc := by
        rw [ec, eb, ea]
        exact ((jF.mono (fun _ h => h) (fun _ h => h) (fun b c h => ⟨h.1, by omega⟩)).setNat (Or.inl rfl) _
          |>.setSc rfl _).setSc rfl _
      exact (Fc.setArr ⟨rfl, by rw [kc]; omega⟩ _).setNat (Or.inr rfl) _
  · rintro σ7 ⟨⟨jA, jd, jF⟩, -, -, -⟩
    have s7 : ∀ y, y ≠ o + 17 → y < o + 40 → σ7.sc y = σ5.sc y := fun y h h' => by
      rw [jF.2.1 y h, F6.2.1 y (by omega)]
    refine ⟨⟨fun l => by rw [jA l l.2 l.2], fun i l => by rw [jF.2.2.1 (a + 1) _ (by omega), t6],
      by rw [s7 o (by omega) (by omega), v5o], by rw [s7 (o + 14) (by omega) (by omega), v5p]; norm_num,
      by rw [s7 (o + 15) (by omega) (by omega), v5q]; norm_num⟩, by rw [jd, d6, dr5], ?_⟩
    exact G6.trans (jF.mono (fun y h => by omega) (fun j h => by omega) (fun b c h => Or.inl h))

/-! ## The stages -/

/-- The stages: `for j < m_st` (`j` in `r + 27`, `m_st` in `r + 28`), one stage. -/
def xstages (L : Layout) (o r a nd aC : ℕ) : XCmd := xforN (r + 27) (r + 28) r (xstage L o r a nd aC)

/-- The units of the stages. -/
abbrev stagesK (d M N B mst : ℕ) : ℕ := mst * (stageK d M N B + 3) + 3

/-- The registers the stages may change. -/
abbrev ssN (r : ℕ) (j : ℕ) : Prop := r + 3 ≤ j ∧ j < r + 12 ∨ r + 13 ≤ j ∧ j < r + 24 ∨ j = r + 27

theorem ssN_off {r k : ℕ} (hk : k < 3 ∨ k = 12 ∨ 24 ≤ k ∧ k < 27 ∨ k = 28) : ¬ ssN r (r + k) := by
  simp only [ssN]; omega

theorem ssN_lt {r j : ℕ} (h : j < r) : ¬ ssN r j := by simp only [ssN]; omega

theorem ssN_of_sgN {r j : ℕ} (h : sgN r j) : ssN r j := by simp only [sgN] at h; simp only [ssN]; omega

theorem sgS_off {o k : ℕ} (hk : 1 ≤ k ∧ k < 14 ∨ k = 35) : ¬ sgS o (o + k) := by simp only [sgS]; omega

theorem sgN_off {r k : ℕ} (hk : k < 3 ∨ k = 27 ∨ k = 28) : ¬ sgN r (r + k) := by simp only [sgN]; omega

theorem sgA_lt {a b k : ℕ} (h : b < a) : ¬ sgA d a b k := by simp only [sgA]; omega

set_option maxHeartbeats 4000000 in
theorem XV.stages {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {o r a nd aC n m E mst : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {ch : Fin d → ℤ} {Dc : ℤ}
    (hXi : ∀ k : ℕ, X.inp k = BitRAM.inputMem d n m A b k) (hXo : X.off = 3 + 2 * (d + 1) * m)
    (hS : o + 113 ≤ L.NS) (hN : r + 29 ≤ L.NN) (hA : a + 16 ≤ L.NA) (hnd : nd < r) (haC : aC < a)
    (hσd : σ.nat nd = d) (hσ1 : σ.nat r = 1) (hσd1 : σ.nat (r + 1) = d + 1) (hσM : σ.nat (r + 2) = m + (d + d))
    (hσB : σ.nat (r + 12) = triBgQ d) (hσN : σ.nat (r + 24) = 2 ^ triNeQ d (ellPos d n))
    (hσdd : σ.nat (r + 25) = d * d) (hσm : σ.nat (r + 26) = m) (hσs : σ.nat (r + 28) = mst)
    (hka : 4 + 2 * ((d + 1) * (m + 1)) < 2 ^ ℓa) (hMa : m + (d + d) < 2 ^ ℓa)
    (hNa : 2 ^ triNeQ d (ellPos d n) < 2 ^ ℓa) (hsa : mst < 2 ^ ℓa)
    (hB1 : 1 ≤ triBgQ d) (hBa : 4 * gsm_prec (triBgQ d) + 2 < 2 ^ ℓa)
    (eZ : σ.sc (o + 1) = 0) (eO : σ.sc (o + 2) = 1) (eM : σ.sc (o + 3) = -1)
    (ePB : σ.sc (o + 4) = (tzDC d (ellPos d n)).PB) (eP2 : σ.sc (o + 5) = (tzDC d (ellPos d n)).P2)
    (ePG : σ.sc (o + 6) = (tzDC d (ellPos d n)).PG) (ePj : σ.sc (o + 7) = (tzDC d (ellPos d n)).Pj)
    (eR : σ.sc (o + 8) = (tzDC d (ellPos d n)).R) (eMR : σ.sc (o + 9) = -(tzDC d (ellPos d n)).R)
    (eAl : σ.sc (o + 10) = (tzDC d (ellPos d n)).Al) (eBh : σ.sc (o + 11) = (tzDC d (ellPos d n)).Bh)
    (eMB : σ.sc (o + 12) = ((-(tzDC d (ellPos d n)).Bh : ℤ) : ℝ))
    (eD8 : σ.sc (o + 13) = ((8 * (tzDC d (ellPos d n)).dd : ℤ) : ℝ))
    (eG : σ.sc (o + 35) = ((2 ^ tzGc d (ellPos d n) : ℤ) : ℝ))
    (e0 : StAt σ o a (tzGc d (ellPos d n)) 0
      (tzStage n A b Dc ch (fun j k => X.wb.cs (σ.draws + triLay mst (triLQ d (ellPos d n)) (j, k))) 0))
    (eC : ∀ i : Fin d, σ.arr aC (i + 1) = ch i) (hDc : 0 < Dc)
    (bT : ∀ t < mst, ∀ i l,
      |(tzStage n A b Dc ch (fun j k => X.wb.cs (σ.draws + triLay mst (triLQ d (ellPos d n)) (j, k))) t).T i l| ≤
        2 ^ E)
    (bMu : ∀ t < mst, ∀ l,
      |(tzStage n A b Dc ch (fun j k => X.wb.cs (σ.draws + triLay mst (triLQ d (ellPos d n)) (j, k))) t).mu l| ≤
        2 ^ E)
    (bD : ∀ t < mst,
      |2 ^ t * (tzStage n A b Dc ch (fun j k => X.wb.cs (σ.draws + triLay mst (triLQ d (ellPos d n)) (j, k))) t).D|
        ≤ 2 ^ E)
    (bRB : ∀ t < mst, ∀ k, |onN (tzRowB A b ch (1 + t * tzGc d (ellPos d n)) t
      (tzStage n A b Dc ch (fun j k => X.wb.cs (σ.draws + triLay mst (triLQ d (ellPos d n)) (j, k))) t).D) k| ≤
        2 ^ E)
    (hb : ∀ t < mst, (frMhat A b : ℤ) ^ (d + 2) *
      (tzStage n A b Dc ch (fun j k => X.wb.cs (σ.draws + triLay mst (triLQ d (ellPos d n)) (j, k))) t).D < 2 ^ ℓ)
    (bE : mst * tzGc d (ellPos d n) + 1 ≤ E) (bC : ∀ i, |ch i| ≤ 2 ^ E)
    (bRA : ∀ k l, |onN (tzRowA A b) k l| ≤ 2 ^ E)
    (bPB : |(tzDC d (ellPos d n)).PB| ≤ 2 ^ E) (bP2 : |(tzDC d (ellPos d n)).P2| ≤ 2 ^ E)
    (bPj : |(tzDC d (ellPos d n)).Pj| ≤ 2 ^ E) (bBh : (tzDC d (ellPos d n)).Bh ≤ 2 ^ E)
    (bD8 : |8 * (tzDC d (ellPos d n)).dd| ≤ 2 ^ E) (b4p : 4 * gsm_prec (triBgQ d) ≤ E)
    (bN : 2 ^ triNeQ d (ellPos d n) ≤ 2 ^ E)
    (bNB : ((2 ^ triNeQ d (ellPos d n) : ℕ) : ℤ) * (tzDC d (ellPos d n)).Bh ≤ 2 ^ E)
    (hE : 48 * E + 42 * d + 32 < ℓ) :
    XRunsB L X ℓa ℓ (xstages L o r a nd aC) σ
      (stagesK d (m + (d + d)) (2 ^ triNeQ d (ellPos d n)) (triBgQ d) mst) (fun σ' =>
      StAt σ' o a (tzGc d (ellPos d n)) mst
        (tzStage n A b Dc ch (fun j k => X.wb.cs (σ.draws + triLay mst (triLQ d (ellPos d n)) (j, k))) mst) ∧
      σ'.draws = σ.draws + mst * triLQ d (ellPos d n) ∧ FrameA (sgS o) (ssN r) (sgA d a) σ σ') := by
  set ℓp := ellPos d n with hℓp
  set Gc := tzGc d ℓp with hGc
  set Lc := triLQ d ℓp with hLc
  set ω : ℕ → ℕ → Bool := fun j k => X.wb.cs (σ.draws + triLay mst Lc (j, k)) with hω
  have hLc' : Lc = 2 * triBgQ d * d * 2 ^ triNeQ d ℓp := by rw [hLc]; unfold triLQ; ring
  obtain ⟨hR, hRB, hAl, hAB, hPG, hPGB⟩ := tzDC_ok d ℓp
  let J : ℕ → Env d → Prop := fun t σ' => StAt σ' o a Gc t (tzStage n A b Dc ch ω t) ∧
    σ'.draws = σ.draws + t * Lc ∧ FrameA (sgS o) (ssN r) (sgA d a) σ σ'
  refine XV.mono (XV.forN (L := L) (X := X) (ℓ := ℓ) (i := r + 27) (n := r + 28) (one := r) hL (by omega)
    (by omega) (by omega) (by omega) (by omega) mst (stageK d (m + (d + d)) (2 ^ triNeQ d ℓp) (triBgQ d)) hsa J σ
    hσs hσ1 ⟨?_, by rw [Env.setNat_draws, zero_mul, add_zero],
      (FrameA.refl (sgS o) (ssN r) (sgA d a) σ).setNat (Or.inr (Or.inr rfl)) 0⟩ ?_) le_rfl ?_
  · obtain ⟨e1, e2, e3, e4, e5⟩ := e0
    exact ⟨fun l => by rw [Env.setNat_arr, e1], fun i l => by rw [Env.setNat_arr, e2],
      by rw [Env.setNat_sc, e3], by rw [Env.setNat_sc, e4], by rw [Env.setNat_sc, e5]⟩
  · intro t ht σ' ⟨⟨j1, j2, j3, j4, j5⟩, jd, jF⟩ hkt hkn hk1
    have n' : ∀ q, ¬ ssN r q → σ'.nat q = σ.nat q := fun q h => jF.1 q h
    have s' : ∀ y, ¬ sgS o y → σ'.sc y = σ.sc y := fun y h => jF.2.1 y h
    set P := tzStage n A b Dc ch ω t with hP
    have hPD : P.D = Dc * 2 ^ (1 + t * Gc) := tzStage_D n A b Dc ch ω t
    have hD1 : 1 ≤ P.D := by
      rw [hPD]; exact one_le_mul_of_one_le_of_one_le (by clear * - hDc; omega) (one_le_pow₀ (by norm_num))
    have hGE : Gc ≤ E := by
      have : 1 * Gc ≤ mst * Gc := Nat.mul_le_mul_right _ (by clear * - ht; omega)
      clear * - this bE; omega
    have hPE : 1 + t * Gc ≤ E := by
      have : t * Gc ≤ mst * Gc := Nat.mul_le_mul_right _ ht.le
      clear * - this bE; omega
    have bPD : |P.D| ≤ 2 ^ E := by
      refine le_trans ?_ (bD t ht)
      rw [abs_mul, abs_of_pos (show (0 : ℤ) < 2 ^ t by positivity)]
      exact le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ (by norm_num))
    refine XV.mono (XV.stage hL (o := o) (r := r) (a := a) (nd := nd) (aC := aC) (n := n) (m := m)
      (N := 2 ^ triNeQ d ℓp) (B := triBgQ d) (E := E) (e := 1 + t * Gc) (j := t) (Gc := Gc) (A := A) (b := b)
      (ch := ch) (c := tzDC d ℓp) (P := P) hXi hXo hS (by omega) hA hnd haC
      (by rw [n' nd (ssN_lt hnd), hσd]) (by rw [n' r (ssN_off (k := 0) (by decide)), hσ1])
      (by rw [n' (r + 1) (ssN_off (by decide)), hσd1]) (by rw [n' (r + 2) (ssN_off (by decide)), hσM])
      (by rw [n' (r + 12) (ssN_off (by decide)), hσB]) (by rw [n' (r + 24) (ssN_off (by decide)), hσN])
      (by rw [n' (r + 25) (ssN_off (by decide)), hσdd]) (by rw [n' (r + 26) (ssN_off (by decide)), hσm])
      hka hMa hNa hB1 hBa
      (by rw [s' (o + 1) (sgS_off (by decide)), eZ]) (by rw [s' (o + 2) (sgS_off (by decide)), eO])
      (by rw [s' (o + 3) (sgS_off (by decide)), eM]) (by rw [s' (o + 4) (sgS_off (by decide)), ePB])
      (by rw [s' (o + 5) (sgS_off (by decide)), eP2]) (by rw [s' (o + 6) (sgS_off (by decide)), ePG])
      (by rw [s' (o + 7) (sgS_off (by decide)), ePj]) (by rw [s' (o + 8) (sgS_off (by decide)), eR])
      (by rw [s' (o + 9) (sgS_off (by decide)), eMR]) (by rw [s' (o + 10) (sgS_off (by decide)), eAl])
      (by rw [s' (o + 11) (sgS_off (by decide)), eBh]) (by rw [s' (o + 12) (sgS_off (by decide)), eMB])
      (by rw [s' (o + 13) (sgS_off (by decide)), eD8]) j3 j4 j5
      (by rw [s' (o + 35) (sgS_off (by decide)), eG]) j1 j2
      (fun i => by rw [jF.2.2.1 aC (i + 1) (sgA_lt haC), eC i])
      hR hRB hAl hAB hPG hPGB hD1 (bT t ht) (bMu t ht) bC bPD hPE (bD t ht) hGE bRA (bRB t ht) bPB bP2 bPj
      bBh bD8 b4p bN bNB (hb t ht) hE) le_rfl ?_
    rintro σ'' ⟨m2, t2, D2, P2, Q2, d2, F2⟩
    have hSum : stSum (tzDC d ℓp) P A b ch (1 + t * Gc) t (triBgQ d) (2 ^ triNeQ d ℓp) X.wb.cs σ'.draws =
        tzSum (tzDC d ℓp) P.T P.mu (onN (tzRowA A b)) (onN (tzRowB A b ch (1 + t * Gc) t P.D)) (m + (d + d))
          (tzY d (triBgQ d) (ω t)) (2 ^ triNeQ d ℓp) := by
      unfold stSum
      refine tzSum_congr _ _ _ _ _ _ _ _ (fun u hu => ?_)
      rw [jd]
      exact (stage_coins (d := d) (triBgQ d) (2 ^ triNeQ d ℓp) mst Lc t σ.draws X.wb.cs ht (by rw [hLc']) u hu).symm
    have hnext : tzStage n A b Dc ch ω (t + 1) = tzComp P (tzSum (tzDC d ℓp) P.T P.mu (onN (tzRowA A b))
        (onN (tzRowB A b ch (1 + t * Gc) t P.D)) (m + (d + d)) (tzY d (triBgQ d) (ω t)) (2 ^ triNeQ d ℓp)) Gc := by
      rw [tzStage]
    rw [hSum, ← hnext] at m2 t2 D2 Q2
    refine ⟨by rw [F2.1 (r + 27) (sgN_off (by decide)), hkt],
      by rw [F2.1 (r + 28) (sgN_off (by decide)), hkn], by rw [F2.1 r (sgN_off (k := 0) (by decide)), hk1],
      ⟨fun l => by rw [Env.setNat_arr, m2], fun i l => by rw [Env.setNat_arr, t2], by rw [Env.setNat_sc, D2],
        by rw [Env.setNat_sc, P2, show 1 + t * Gc + Gc = 1 + (t + 1) * Gc by ring],
        by rw [Env.setNat_sc, Q2]⟩, by rw [Env.setNat_draws, d2, jd, hLc']; ring, ?_⟩
    exact (jF.trans (F2.mono (fun y h => h) (fun q h => ssN_of_sgN h)
      (fun b k h => h))).setNat (Or.inr (Or.inr rfl)) _
  · rintro σ' ⟨hJ, -, -, -⟩
    exact hJ

end AdversarialBco.Bit.Transfer
