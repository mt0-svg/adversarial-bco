/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriDraw

@[expose] public section

/-!
# TRI-M, the rows of a stage read on demand

Row `k` of stage `j` into the array `aRow` (cells `0, ..., d - 1`) and its right-hand side `β'` into a slot:

* an input row, `k < m`: the cleared row `frAl A b k` and `frBe A b k * D`, read from the input cells (numerator in the
  cell `3 + 2 e`, denominator in `4 + 2 e`, `e = (d + 1) k + j`): `xdenProd` (the product of the `d + 1`
  denominators), `xrowEnt` (the entries), `xrowBeta` (`β'`), `xinRow` (the three);
* a box row, `k = m + i` or `k = m + d + i`: `± e_i` and `ĉ_i 2^e + 2^j D`, `2^j D - ĉ_i 2^e`.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.TriM Matrix

variable {d : ℕ}

theorem prod_range_abs_le (f : ℕ → ℤ) (M : ℤ) (hM : 1 ≤ M) (N : ℕ) (hf : ∀ j < N, 1 ≤ f j ∧ f j ≤ M) :
    1 ≤ ∏ j ∈ Finset.range N, f j ∧ ∏ j ∈ Finset.range N, f j ≤ M ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    obtain ⟨h1, h2⟩ := ih (fun j hj => hf j (by omega))
    obtain ⟨g1, g2⟩ := hf N (by omega)
    rw [Finset.prod_range_succ, pow_succ]
    exact ⟨by nlinarith, by nlinarith⟩

/-- `for j < nat nn: sD := sD * inp(nI); nI := nI + 2`: the product of the cells `c, c + 2, ...` (`nI` holds `c`). -/
def xdenProd (L : Layout) (sD sT nj nI nn none : ℕ) : XCmd :=
  xforN nj nn none (.seq (xrdIn L sT nI) (.seq (toX (VL.sop2 L .mul sD sD sT))
    (.seq (.prim (.frag (.nadd nI nI none))) (.prim (.frag (.nadd nI nI none))))))

set_option maxHeartbeats 1000000 in
theorem XV.denProd {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {sD sT nj nI nn none N c : ℕ} {Mh : ℤ} {Dn : ℕ → ℤ} (hsD : sD < L.NS) (hsT : sT < L.NS) (hDT : sD ≠ sT)
    (hnj : nj < L.NN) (hnI : nI < L.NN) (hnn : nn < L.NN) (hno : none < L.NN)
    (hne : [nj, nI, nn, none].Nodup) (hσI : σ.nat nI = c) (hσn : σ.nat nn = N) (hσ1 : σ.nat none = 1)
    (hσD : σ.sc sD = 1) (hidx : c + 2 * N ≤ X.off + 1) (hidxa : c + 2 * N < 2 ^ ℓa)
    (hinp : ∀ j < N, X.inp (c + 2 * j) = Dn j) (hM1 : 1 ≤ Mh) (hDn : ∀ j < N, 1 ≤ Dn j ∧ Dn j ≤ Mh)
    (hM : Mh ^ N < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xdenProd L sD sT nj nI nn none) σ (N * (4 + 3) + 3) (fun σ' =>
      σ'.sc sD = ((∏ j ∈ Finset.range N, Dn j : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧ σ'.nat nI = c + 2 * N ∧
      FrameA (fun y => y = sD ∨ y = sT) (fun j => j = nj ∨ j = nI) (fun _ _ => False) σ σ') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne
  obtain ⟨⟨jI, jn, jo⟩, ⟨In, Io⟩, no⟩ := hne
  let J : ℕ → Env d → Prop := fun j σ' => σ'.sc sD = ((∏ j' ∈ Finset.range j, Dn j' : ℤ) : ℝ) ∧
    σ'.draws = σ.draws ∧ σ'.nat nI = c + 2 * j ∧
    FrameA (fun y => y = sD ∨ y = sT) (fun j => j = nj ∨ j = nI) (fun _ _ => False) σ σ'
  refine XV.mono (XV.forN hL hnj hnn hno jn jo N (1 + (1 + (1 + 1))) (by omega) J σ hσn hσ1
    ⟨by simp [hσD], rfl, by simp [Ne.symm jI, hσI],
      (FrameA.refl (fun y => y = sD ∨ y = sT) (fun j => j = nj ∨ j = nI) (fun _ _ => False)
        σ).setNat (Or.inl rfl) 0⟩ ?_) le_rfl fun σ' ⟨⟨h1, h2, h3, h4⟩, _⟩ => ⟨h1, h2, h3, h4⟩
  intro j hj σ' ⟨hD', hd', hI', hF⟩ hjt hjn hj1
  obtain ⟨p1, p2⟩ := prod_range_abs_le Dn Mh hM1 j (fun j' hj' => hDn j' (by omega))
  obtain ⟨g1, g2⟩ := hDn j hj
  have hMj : Mh ^ (j + 1) < 2 ^ ℓ := lt_of_le_of_lt (pow_le_pow_right₀ hM1 (by omega)) hM
  have hMj' : Mh ^ j < 2 ^ ℓ := lt_of_le_of_lt (pow_le_pow_right₀ hM1 (by omega)) hM
  have bT : |((Dn j : ℤ) : ℝ)| < 2 ^ ℓ := by
    rw [abs_of_pos (by exact_mod_cast (by omega : (0 : ℤ) < Dn j))]
    exact_mod_cast lt_of_le_of_lt (g2.trans (le_self_pow₀ hM1 (by omega))) hMj
  refine XV.seq (XV.rdIn hL hsT hnI (by rw [hI']; omega) (by rw [hI']; omega) (by rw [hI', hinp j hj]; exact bT))
    fun σ1 e1 => ?_
  subst e1
  have hpr : ((∏ j' ∈ Finset.range j, Dn j' : ℤ) : ℝ) * (Dn j : ℝ) = ((∏ j' ∈ Finset.range (j + 1), Dn j' : ℤ) : ℝ) := by
    rw [Finset.prod_range_succ]; push_cast; ring
  have hpb : |((∏ j' ∈ Finset.range (j + 1), Dn j' : ℤ) : ℝ)| < 2 ^ ℓ := by
    obtain ⟨q1, q2⟩ := prod_range_abs_le Dn Mh hM1 (j + 1) (fun j' hj' => hDn j' (by omega))
    rw [abs_of_pos (by exact_mod_cast (by omega : (0 : ℤ) < ∏ j' ∈ Finset.range (j + 1), Dn j'))]
    exact_mod_cast lt_of_le_of_lt q2 hMj
  refine XV.seq (XV.sop2 hL hsD hsD hsT .mul (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
    (by simp [hDT, hD']; exact_mod_cast (show |(∏ j' ∈ Finset.range j, Dn j' : ℤ)| < 2 ^ ℓ by
      rw [abs_of_pos (by omega)]; exact lt_of_le_of_lt p2 hMj'))
    (by simp [hI', hinp j hj]; exact bT)
    (by simp only [Env.setSc_sc, ite_true, ite_eq_right_of_eq_false _ _ (eq_false hDT), hD', hI', hinp j hj, RealRAM.Op2.eval, hpr]; exact hpb)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.nadd hL hnI hnI hno (by simp only [Env.setSc_nat, hI']; omega) (by simp only [Env.setSc_nat, hj1]; omega)) fun σ3 e3 => ?_
  subst e3
  refine XV.mono (XV.nadd hL hnI hnI hno (by simp only [Env.setNat_nat, ite_true, Env.setSc_nat, hI', hj1]; omega) (by rw [nat_setNat_ne _ (fun h => Io h.symm)]; simp only [Env.setSc_nat, hj1]; omega)) le_rfl
    fun σ4 e4 => ?_
  subst e4
  have nn1 := Ne.symm jI
  have nn2 := Ne.symm In
  have nn3 := Ne.symm Io
  refine ⟨by simp [jI, hjt], by simp [nn2, hjn], by simp [nn3, hj1], ?_, ?_, ?_, ?_⟩
  · simp [hDT, hD', hI', hinp j hj, RealRAM.Op2.eval]; rw [Finset.prod_range_succ]
  · simp [hd']
  · simp [nn1, hI', nn3, hj1]; ring
  · exact ((((hF.setSc (Or.inr rfl) _).setSc (Or.inl rfl) _).setNat (Or.inr rfl) _).setNat (Or.inr rfl) _).setNat
      (Or.inl rfl) _

/-- Reads registers and slots of an environment built by `setNat`, `setSc`, `setArr`; disequalities by `omega`. -/
macro "trimenv" : tactic =>
  `(tactic| (simp (disch := omega) only [nat_setNat_ne, nat_setNat_eq, sc_setSc_ne, sc_setSc_eq,
    Env.setNat_sc, Env.setSc_nat, Env.setArr_nat, Env.setArr_sc, Env.setNat_arr, Env.setSc_arr, Env.setNat_draws,
    Env.setSc_draws, Env.setArr_draws]))

/-- Proves `[a, b, ...].Nodup` from the disequalities in context. -/
macro "trimnodup" : tactic =>
  `(tactic| ((simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil, not_false_eq_true,
    and_true]; repeat' constructor) <;> omega))

/-- `for j < nat nn: aRow[j] := inp(nI) * (sD / inp(nI + 1)); nI := nI + 2`: the cleared entries of a row. -/
def xrowEnt (L : Layout) (sD sT sN sQ aRow nj nI nn none : ℕ) : XCmd :=
  xforN nj nn none (.seq (xrdIn L sN nI) (.seq (.prim (.frag (.nadd nI nI none))) (.seq (xrdIn L sT nI)
    (.seq (xsidiv L sQ sD sT) (.seq (toX (VL.sop2 L .mul sN sN sQ)) (.seq (toX (VL.aset L aRow nj sN))
      (.prim (.frag (.nadd nI nI none)))))))))

set_option maxHeartbeats 2000000 in
theorem XV.rowEnt {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {sD sT sN sQ aRow nj nI nn none N c : ℕ} {Mh P : ℤ} {Nm Dn : ℕ → ℤ} (hsD : sD < L.NS) (hsT : sT < L.NS)
    (hsN : sN < L.NS) (hsQ : sQ < L.NS) (hss : [sD, sT, sN, sQ].Nodup) (hR : aRow < L.NA)
    (hnj : nj < L.NN) (hnI : nI < L.NN) (hnn : nn < L.NN) (hno : none < L.NN)
    (hne : [nj, nI, nn, none].Nodup) (hσI : σ.nat nI = c) (hσn : σ.nat nn = N) (hσ1 : σ.nat none = 1)
    (hσD : σ.sc sD = P) (hNd : N ≤ d) (hda : d * d + d < 2 ^ ℓa) (hidx : c + 2 * N ≤ X.off)
    (hidxa : c + 2 * N < 2 ^ ℓa)
    (hinpN : ∀ j < N, X.inp (c + 2 * j) = Nm j) (hinpD : ∀ j < N, X.inp (c + 2 * j + 1) = Dn j)
    (hP0 : 0 ≤ P) (hM1 : 1 ≤ Mh) (hNm : ∀ j < N, |Nm j| ≤ Mh) (hDn : ∀ j < N, 1 ≤ Dn j ∧ Dn j ≤ Mh)
    (hb : Mh * P < 2 ^ ℓ) (hMl : Mh < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xrowEnt L sD sT sN sQ aRow nj nI nn none) σ
      (N * (1 + (1 + (1 + (1 + (1 + (2 + 1))))) + 3) + 3)
      (fun σ' => (∀ j < N, σ'.arr aRow j = ((Nm j * (P / Dn j) : ℤ) : ℝ)) ∧ σ'.draws = σ.draws ∧
        σ'.nat nI = c + 2 * N ∧ σ'.sc sD = P ∧
        FrameA (fun y => y = sT ∨ y = sN ∨ y = sQ) (fun j => j = nj ∨ j = nI) (fun b k => b = aRow ∧ k < N)
          σ σ') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne hss
  obtain ⟨⟨jI, jn, jo⟩, ⟨In, Io⟩, no⟩ := hne
  obtain ⟨⟨DT, DN, DQ⟩, ⟨TN, TQ⟩, NQ⟩ := hss
  have hP1 : P < 2 ^ ℓ := lt_of_le_of_lt (le_mul_of_one_le_left hP0 hM1) hb
  let J : ℕ → Env d → Prop := fun j σ' => (∀ j' < j, σ'.arr aRow j' = ((Nm j' * (P / Dn j') : ℤ) : ℝ)) ∧
    σ'.draws = σ.draws ∧ σ'.nat nI = c + 2 * j ∧
    FrameA (fun y => y = sT ∨ y = sN ∨ y = sQ) (fun j => j = nj ∨ j = nI) (fun b k => b = aRow ∧ k < j) σ σ'
  refine XV.mono (XV.forN hL hnj hnn hno jn jo N (1 + (1 + (1 + (1 + (1 + (2 + 1)))))) (by omega) J σ hσn hσ1
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, by trimenv; omega,
      (FrameA.refl (fun y => y = sT ∨ y = sN ∨ y = sQ) (fun j => j = nj ∨ j = nI)
        (fun b k => b = aRow ∧ k < 0) σ).setNat (Or.inl rfl) 0⟩ ?_) le_rfl
    fun σ' ⟨⟨h1, h2, h3, h4⟩, _⟩ => ⟨h1, h2, h3, by rw [h4.2.1 sD (by tauto), hσD], h4⟩
  intro j hj σ' ⟨hy, hd', hI', hF⟩ hjt hjn hj1
  have eD : σ'.sc sD = P := by rw [hF.2.1 sD (by tauto), hσD]
  obtain ⟨g1, g2⟩ := hDn j hj
  have bN : |((Nm j : ℤ) : ℝ)| < 2 ^ ℓ := by
    rw [← Int.cast_abs]; exact_mod_cast lt_of_le_of_lt (hNm j hj) hMl
  have bD : |((Dn j : ℤ) : ℝ)| < 2 ^ ℓ := by
    rw [← Int.cast_abs, abs_of_pos (by omega)]; exact_mod_cast lt_of_le_of_lt g2 hMl
  have bP : |((P : ℤ) : ℝ)| < 2 ^ ℓ := by
    rw [← Int.cast_abs, abs_of_nonneg hP0]; exact_mod_cast hP1
  have hq0 : 0 ≤ P / Dn j := Int.ediv_nonneg hP0 (by omega)
  have hqP : P / Dn j ≤ P := Int.ediv_le_self _ hP0
  have bQ : |((P / Dn j : ℤ) : ℝ)| < 2 ^ ℓ := by
    rw [← Int.cast_abs, abs_of_nonneg hq0]; exact_mod_cast lt_of_le_of_lt hqP hP1
  have bV : |((Nm j * (P / Dn j) : ℤ) : ℝ)| < 2 ^ ℓ := by
    rw [← Int.cast_abs, abs_mul, abs_of_nonneg hq0]
    exact_mod_cast lt_of_le_of_lt (mul_le_mul (hNm j hj) hqP hq0 (by omega)) hb
  have hdl : j < asz d := by unfold asz; nlinarith
  have eN : X.inp (σ'.nat nI) = Nm j := by rw [hI', hinpN j hj]
  refine XV.seq (XV.rdIn hL hsN hnI (by rw [hI']; omega) (by rw [hI']; omega) (by rw [eN]; exact bN))
    fun σ1 e1 => ?_
  have s1 : σ1.sc sN = Nm j ∧ σ1.sc sD = P ∧ σ1.nat nI = c + 2 * j ∧ σ1.nat none = 1 ∧ σ1.nat nj = j := by
    subst e1; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> trimenv <;> simp [eD, hI', hj1, hjt, hinpN j hj]
  refine XV.seq (XV.nadd hL hnI hnI hno (by rw [s1.2.2.1]; omega) (by rw [s1.2.2.2.1]; omega)) fun σ2 e2 => ?_
  have s2 : σ2.sc sN = Nm j ∧ σ2.sc sD = P ∧ σ2.nat nI = c + 2 * j + 1 ∧ σ2.nat none = 1 ∧ σ2.nat nj = j := by
    subst e2; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> trimenv <;> simp [s1]
  have eDn : X.inp (σ2.nat nI) = Dn j := by rw [s2.2.2.1, hinpD j hj]
  refine XV.seq (XV.rdIn hL hsT hnI (by rw [s2.2.2.1]; omega) (by rw [s2.2.2.1]; omega) (by rw [eDn]; exact bD))
    fun σ3 e3 => ?_
  have s3 : σ3.sc sN = Nm j ∧ σ3.sc sD = P ∧ σ3.sc sT = Dn j ∧ σ3.nat nI = c + 2 * j + 1 ∧ σ3.nat none = 1 ∧
      σ3.nat nj = j := by
    subst e3; refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> trimenv <;> simp [s2, hinpD j hj]
  refine XV.seq (XV.sidiv hL hsQ hsD hsT (by rw [s3.2.1]; exact bP) (by rw [s3.2.2.1]; exact bD))
    fun σ4 e4 => ?_
  have s4 : σ4.sc sN = Nm j ∧ σ4.sc sQ = (P / Dn j : ℤ) ∧ σ4.nat nI = c + 2 * j + 1 ∧ σ4.nat none = 1 ∧
      σ4.nat nj = j := by
    subst e4; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> trimenv <;> simp [s3]
  refine XV.seq (XV.sop2 hL hsN hsN hsQ .mul (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
    (by rw [s4.1]; exact bN) (by rw [s4.2.1]; exact bQ)
    (by rw [s4.1, s4.2.1]; simp only [RealRAM.Op2.eval]; exact_mod_cast bV)) fun σ5 e5 => ?_
  have s5 : σ5.sc sN = ((Nm j * (P / Dn j) : ℤ) : ℝ) ∧ σ5.nat nI = c + 2 * j + 1 ∧ σ5.nat none = 1 ∧
      σ5.nat nj = j := by
    subst e5; refine ⟨?_, ?_, ?_, ?_⟩ <;> trimenv <;> simp [s4, RealRAM.Op2.eval]
  refine XV.seq (XV.aset hL hR hnj hsN (by rw [s5.2.2.2]; exact hdl) (by rw [s5.1]; exact bV)) fun σ6 e6 => ?_
  have s6 : σ6.nat nI = c + 2 * j + 1 ∧ σ6.nat none = 1 := by
    subst e6; exact ⟨by trimenv; exact s5.2.1, by trimenv; exact s5.2.2.1⟩
  refine XV.mono (XV.nadd hL hnI hnI hno (by rw [s6.1]; omega) (by rw [s6.2]; omega)) le_rfl fun σ7 e7 => ?_
  have F7 : FrameA (fun y => y = sT ∨ y = sN ∨ y = sQ) (fun j' => j' = nj ∨ j' = nI)
      (fun b k => b = aRow ∧ k < j + 1) σ σ7 := by
    subst e7 e6 e5 e4 e3 e2 e1
    exact (((((((hF.setSc (Or.inr (Or.inl rfl)) _).setNat (Or.inr rfl) _).setSc (Or.inl rfl) _).setSc
      (Or.inr (Or.inr rfl)) _).setSc (Or.inr (Or.inl rfl)) _).mono (fun _ h => h) (fun _ h => h)
      (fun b k h => ⟨h.1, by omega⟩)).setArr ⟨rfl, by trimenv; omega⟩ _).setNat (Or.inr rfl) _
  have a7 : ∀ k, σ7.arr aRow k = if k = j then ((Nm j * (P / Dn j) : ℤ) : ℝ) else σ'.arr aRow k := by
    intro k
    subst e7 e6
    rw [Env.setNat_arr, Env.setArr_arr, s5.2.2.2]
    by_cases hk : k = j
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, hk⟩), ite_eq_left_of_eq_true _ _ (eq_true hk), s5.1]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hk h.2), ite_eq_right_of_eq_false _ _ (eq_false hk)]
      subst e5 e4 e3 e2 e1; trimenv
  have n7 : σ7.nat nj = j ∧ σ7.nat nn = N ∧ σ7.nat none = 1 ∧ σ7.nat nI = c + 2 * (j + 1) ∧
      σ7.draws = σ.draws := by
    subst e7 e6 e5 e4 e3 e2 e1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> trimenv <;> simp [hjt, hjn, hj1, hI', hd'] <;> ring
  refine ⟨n7.1, n7.2.1, n7.2.2.1, fun j' hj' => ?_, by trimenv; exact n7.2.2.2.2, by trimenv; exact n7.2.2.2.1,
    F7.setNat (Or.inl rfl) _⟩
  rw [Env.setNat_arr, a7]
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hlt | rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact hy j' hlt
  · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]

/-- `sB := inp(nI) * (sD / inp(nI + 1)) * sDn`: the cleared right-hand side of a row times `D`. -/
def xrowBeta (L : Layout) (sD sT sN sQ sB sDn nI none : ℕ) : XCmd :=
  .seq (xrdIn L sN nI) (.seq (.prim (.frag (.nadd nI nI none))) (.seq (xrdIn L sT nI)
    (.seq (xsidiv L sQ sD sT) (.seq (toX (VL.sop2 L .mul sN sN sQ)) (toX (VL.sop2 L .mul sB sN sDn))))))

set_option maxHeartbeats 1000000 in
theorem XV.rowBeta {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {sD sT sN sQ sB sDn nI none c : ℕ} {Mh P D Nm Dn : ℤ} (hsD : sD < L.NS) (hsT : sT < L.NS)
    (hsN : sN < L.NS) (hsQ : sQ < L.NS) (hsB : sB < L.NS) (hsDn : sDn < L.NS)
    (hss : [sD, sT, sN, sQ, sB, sDn].Nodup) (hnI : nI < L.NN) (hno : none < L.NN)
    (hσI : σ.nat nI = c) (hσ1 : σ.nat none = 1) (hσD : σ.sc sD = P) (hσDn : σ.sc sDn = D)
    (hidx : c + 2 ≤ X.off) (hidxa : c + 2 < 2 ^ ℓa) (hinpN : X.inp c = Nm) (hinpD : X.inp (c + 1) = Dn)
    (hP1 : 1 ≤ P) (hD1 : 1 ≤ D) (hNm : |Nm| ≤ Mh) (hDn : 1 ≤ Dn ∧ Dn ≤ Mh) (hb : Mh * P * D < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xrowBeta L sD sT sN sQ sB sDn nI none) σ (1 + (1 + (1 + (1 + (1 + 1)))))
      (fun σ' => σ'.sc sB = ((Nm * (P / Dn) * D : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => y = sT ∨ y = sN ∨ y = sQ ∨ y = sB) (fun j => j = nI) (fun _ _ => False) σ σ') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hss
  obtain ⟨⟨DT, DN, DQ, DB, DD⟩, ⟨TN, TQ, TB, TD⟩, ⟨NQ, NB, ND⟩, ⟨QB, QD⟩, BD⟩ := hss
  have hM1 : 1 ≤ Mh := hDn.1.trans hDn.2
  have hPD : P ≤ P * D := le_mul_of_one_le_right (by omega) hD1
  have hMPD : Mh * P ≤ Mh * P * D := le_mul_of_one_le_right (by positivity) hD1
  have hMP : Mh ≤ Mh * P := le_mul_of_one_le_right (by omega) hP1
  have hPM : P ≤ Mh * P := le_mul_of_one_le_left (by omega) hM1
  have hDM : D ≤ Mh * P * D := le_mul_of_one_le_left (by omega) (by nlinarith)
  have cI : ∀ z : ℤ, 0 ≤ z → z < 2 ^ ℓ → |(z : ℝ)| < 2 ^ ℓ := fun z h0 h1 => by
    rw [← Int.cast_abs, abs_of_nonneg h0]; exact_mod_cast h1
  have hq0 : 0 ≤ P / Dn := Int.ediv_nonneg (by omega) (by omega)
  have hqP : P / Dn ≤ P := Int.ediv_le_self _ (by omega)
  have bN : |((Nm : ℤ) : ℝ)| < 2 ^ ℓ := by
    rw [← Int.cast_abs]; exact_mod_cast lt_of_le_of_lt (hNm.trans (hMP.trans hMPD)) hb
  have bD : |((Dn : ℤ) : ℝ)| < 2 ^ ℓ := cI _ (by omega) (by linarith [hDn.2])
  have bP : |((P : ℤ) : ℝ)| < 2 ^ ℓ := cI _ (by omega) (by linarith)
  have bQ : |((P / Dn : ℤ) : ℝ)| < 2 ^ ℓ := cI _ hq0 (by linarith)
  have hv1 : |Nm * (P / Dn)| ≤ Mh * P := by
    rw [abs_mul, abs_of_nonneg hq0]; exact mul_le_mul hNm hqP hq0 (by omega)
  have bV : |((Nm * (P / Dn) : ℤ) : ℝ)| < 2 ^ ℓ := by
    rw [← Int.cast_abs]; exact_mod_cast lt_of_le_of_lt (hv1.trans hMPD) hb
  have bDD : |((D : ℤ) : ℝ)| < 2 ^ ℓ := cI _ (by omega) (by linarith)
  have bW : |((Nm * (P / Dn) * D : ℤ) : ℝ)| < 2 ^ ℓ := by
    rw [← Int.cast_abs, abs_mul, abs_of_pos (by omega : (0 : ℤ) < D)]
    exact_mod_cast lt_of_le_of_lt (mul_le_mul_of_nonneg_right hv1 (by omega)) hb
  refine XV.seq (XV.rdIn hL hsN hnI (by rw [hσI]; omega) (by rw [hσI]; omega) (by rw [hσI, hinpN]; exact bN))
    fun σ1 e1 => ?_
  have s1 : σ1.sc sN = Nm ∧ σ1.sc sD = P ∧ σ1.sc sDn = D ∧ σ1.nat nI = c ∧ σ1.nat none = 1 := by
    subst e1; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> trimenv <;> simp [hσI, hinpN, hσD, hσDn, hσ1]
  refine XV.seq (XV.nadd hL hnI hnI hno (by rw [s1.2.2.2.1]; omega) (by rw [s1.2.2.2.2]; omega)) fun σ2 e2 => ?_
  have s2 : σ2.sc sN = Nm ∧ σ2.sc sD = P ∧ σ2.sc sDn = D ∧ σ2.nat nI = c + 1 := by
    subst e2; refine ⟨?_, ?_, ?_, ?_⟩ <;> trimenv <;> simp [s1]
  refine XV.seq (XV.rdIn hL hsT hnI (by rw [s2.2.2.2]; omega) (by rw [s2.2.2.2]; omega)
    (by rw [s2.2.2.2, hinpD]; exact bD)) fun σ3 e3 => ?_
  have s3 : σ3.sc sN = Nm ∧ σ3.sc sD = P ∧ σ3.sc sDn = D ∧ σ3.sc sT = Dn := by
    subst e3; refine ⟨?_, ?_, ?_, ?_⟩ <;> trimenv <;> simp [s2, hinpD]
  refine XV.seq (XV.sidiv hL hsQ hsD hsT (by rw [s3.2.1]; exact bP) (by rw [s3.2.2.2]; exact bD))
    fun σ4 e4 => ?_
  have s4 : σ4.sc sN = Nm ∧ σ4.sc sQ = (P / Dn : ℤ) ∧ σ4.sc sDn = D := by
    subst e4; refine ⟨?_, ?_, ?_⟩ <;> trimenv <;> simp [s3]
  refine XV.seq (XV.sop2 hL hsN hsN hsQ .mul (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
    (by rw [s4.1]; exact bN) (by rw [s4.2.1]; exact bQ)
    (by rw [s4.1, s4.2.1]; simp only [RealRAM.Op2.eval]; exact_mod_cast bV)) fun σ5 e5 => ?_
  have s5 : σ5.sc sN = ((Nm * (P / Dn) : ℤ) : ℝ) ∧ σ5.sc sDn = D := by
    subst e5; refine ⟨?_, ?_⟩ <;> trimenv <;> simp [s4, RealRAM.Op2.eval]
  refine XV.mono (XV.sop2 hL hsB hsN hsDn .mul (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
    (by rw [s5.1]; exact bV) (by rw [s5.2]; exact bDD)
    (by rw [s5.1, s5.2]; simp only [RealRAM.Op2.eval]; exact_mod_cast bW)) le_rfl fun σ6 e6 => ?_
  refine ⟨?_, ?_, ?_⟩
  · subst e6; trimenv; rw [s5.1, s5.2]; simp only [RealRAM.Op2.eval]; push_cast; ring
  · subst e6 e5 e4 e3 e2 e1; trimenv
  · subst e6 e5 e4 e3 e2 e1
    exact (((((FrameA.refl (fun y => y = sT ∨ y = sN ∨ y = sQ ∨ y = sB) (fun j => j = nI) (fun _ _ => False)
      σ).setSc (Or.inr (Or.inl rfl)) _).setNat rfl _).setSc (Or.inl rfl) _).setSc (Or.inr (Or.inr (Or.inl rfl)))
      _ |>.setSc (Or.inr (Or.inl rfl)) _).setSc (Or.inr (Or.inr (Or.inr rfl))) _

/-- `nI := c0 + 2 (nd1 · nk)`, through `nT`: the address of a row of the input. -/
def xaddr (nI nd1 nk nT c0 : ℕ) : XCmd :=
  .seq (xnmul nI nd1 nk) (.seq (.prim (.frag (.nadd nI nI nI)))
    (.seq (.prim (.frag (.nconst nT c0))) (.prim (.frag (.nadd nI nI nT)))))

theorem XV.addr {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {nI nd1 nk nT c0 D1 K : ℕ} (hnI : nI < L.NN) (hn1 : nd1 < L.NN) (hnk : nk < L.NN) (hnT : nT < L.NN)
    (hne : [nI, nd1, nk, nT].Nodup) (hσ1 : σ.nat nd1 = D1) (hσk : σ.nat nk = K)
    (hb : c0 + 2 * (D1 * K) < 2 ^ ℓa) (hD1 : D1 < 2 ^ ℓa) (hK : K < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xaddr nI nd1 nk nT c0) σ (1 + (1 + (1 + 1)))
      (fun σ' => σ'.nat nI = c0 + 2 * (D1 * K) ∧ σ'.draws = σ.draws ∧
        FrameA (fun _ => False) (fun j => j = nI ∨ j = nT) (fun _ _ => False) σ σ') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne
  obtain ⟨⟨I1, Ik, IT⟩, ⟨n1k, n1T⟩, kT⟩ := hne
  refine XV.seq (XV.nmul hL hnI hn1 hnk (by rw [hσ1]; exact hD1) (by rw [hσk]; exact hK)
    (by rw [hσ1, hσk]; omega)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.nadd hL hnI hnI hnI (by trimenv; rw [hσ1, hσk]; omega) (by trimenv; rw [hσ1, hσk]; omega))
    fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.nconst hL hnT c0 (by omega)) fun σ3 e3 => ?_
  subst e3
  refine XV.mono (XV.nadd hL hnI hnI hnT (by trimenv; rw [hσ1, hσk]; omega) (by trimenv; omega)) le_rfl
    fun σ4 e4 => ?_
  subst e4
  refine ⟨by trimenv; rw [hσ1, hσk]; ring, by trimenv, ?_⟩
  exact (((FrameA.refl (fun _ => False) (fun j => j = nI ∨ j = nT) (fun _ _ => False) σ).setNat (Or.inl rfl)
    _).setNat (Or.inl rfl) _ |>.setNat (Or.inr rfl) _).setNat (Or.inl rfl) _

/-- An input row: `aRow := (Nm j (P / Dn j))_{j < d}` and `sB := Nm d (P / Dn d) sDn`, `P = ∏_{j ≤ d} Dn j`, from
the cells of row `nk` (numerators `3 + 2 ((d + 1) k + j)`, denominators `4 + 2 ((d + 1) k + j)`). -/
def xinRow (L : Layout) (sD sT sN sQ sB sDn aRow nI nT nj nd nd1 nk none : ℕ) : XCmd :=
  .seq (xaddr nI nd1 nk nT 4) (.seq (toX (VL.sconst L sD 1)) (.seq (xdenProd L sD sT nj nI nd1 none)
    (.seq (xaddr nI nd1 nk nT 3) (.seq (xrowEnt L sD sT sN sQ aRow nj nI nd none)
      (xrowBeta L sD sT sN sQ sB sDn nI none)))))

set_option maxHeartbeats 2000000 in
theorem XV.inRow {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {sD sT sN sQ sB sDn aRow nI nT nj nd nd1 nk none k : ℕ} {Mh D : ℤ} {Nm Dn : ℕ → ℤ}
    (hsD : sD < L.NS) (hsT : sT < L.NS) (hsN : sN < L.NS) (hsQ : sQ < L.NS) (hsB : sB < L.NS)
    (hsDn : sDn < L.NS) (hss : [sD, sT, sN, sQ, sB, sDn].Nodup) (hR : aRow < L.NA)
    (hnI : nI < L.NN) (hnT : nT < L.NN) (hnj : nj < L.NN) (hnd : nd < L.NN) (hn1 : nd1 < L.NN)
    (hnk : nk < L.NN) (hno : none < L.NN) (hne : [nI, nT, nj, nd, nd1, nk, none].Nodup)
    (hσd : σ.nat nd = d) (hσd1 : σ.nat nd1 = d + 1) (hσk : σ.nat nk = k) (hσ1 : σ.nat none = 1)
    (hσDn : σ.sc sDn = D) (hoff : 3 + 2 * ((d + 1) * (k + 1)) ≤ X.off)
    (hka : 4 + 2 * ((d + 1) * (k + 1)) < 2 ^ ℓa) (hda : d * d + d < 2 ^ ℓa)
    (hinpN : ∀ j ≤ d, X.inp (3 + 2 * ((d + 1) * k + j)) = Nm j)
    (hinpD : ∀ j ≤ d, X.inp (4 + 2 * ((d + 1) * k + j)) = Dn j)
    (hD1 : 1 ≤ D) (hM1 : 1 ≤ Mh) (hNm : ∀ j ≤ d, |Nm j| ≤ Mh) (hDn : ∀ j ≤ d, 1 ≤ Dn j ∧ Dn j ≤ Mh)
    (hb : Mh ^ (d + 2) * D < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xinRow L sD sT sN sQ sB sDn aRow nI nT nj nd nd1 nk none) σ (18 * d + 28)
      (fun σ' => (∀ j < d, σ'.arr aRow j = ((Nm j * ((∏ j' ∈ Finset.range (d + 1), Dn j') / Dn j) : ℤ) : ℝ)) ∧
        σ'.sc sB = ((Nm d * ((∏ j' ∈ Finset.range (d + 1), Dn j') / Dn d) * D : ℤ) : ℝ) ∧
        σ'.draws = σ.draws ∧
        FrameA (fun y => y = sD ∨ y = sT ∨ y = sN ∨ y = sQ ∨ y = sB) (fun j => j = nI ∨ j = nT ∨ j = nj)
          (fun b k' => b = aRow ∧ k' < d) σ σ') := by
  have hss' := hss
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hss hne
  obtain ⟨⟨DT, DN, DQ, DB, DD⟩, ⟨TN, TQ, TB, TD⟩, ⟨NQ, NB, ND⟩, ⟨QB, QD⟩, BD⟩ := hss
  obtain ⟨⟨IT, Ij, Id, I1, Ik, Io⟩, ⟨Tj, Td, T1, Tk, To⟩, ⟨jd, j1, jk, jo⟩, ⟨d1, dk, dO⟩, ⟨k1, _⟩, ko⟩ := hne
  set P := ∏ j' ∈ Finset.range (d + 1), Dn j' with hP
  obtain ⟨p1, p2⟩ := prod_range_abs_le Dn Mh hM1 (d + 1) (fun j hj => hDn j (by omega))
  have hkk : (d + 1) * (k + 1) = (d + 1) * k + d + 1 := by ring
  have hdk : d + 1 ≤ (d + 1) * (k + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hkd : k + 1 ≤ (d + 1) * (k + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hMp : Mh ^ (d + 2) = Mh * Mh ^ (d + 1) := by ring
  have hM0 : 0 ≤ Mh ^ (d + 1) := by positivity
  have q1 : Mh ^ (d + 2) ≤ Mh ^ (d + 2) * D := le_mul_of_one_le_right (by positivity) hD1
  have q2 : Mh ^ (d + 1) ≤ Mh ^ (d + 2) := by rw [hMp]; exact le_mul_of_one_le_left hM0 hM1
  have q3 : Mh ≤ Mh ^ (d + 2) := by rw [hMp]; exact le_mul_of_one_le_right (by omega) (one_le_pow₀ hM1)
  have bMP : Mh * P ≤ Mh ^ (d + 2) := by rw [hMp]; exact mul_le_mul_of_nonneg_left p2 (by omega)
  have hPow : Mh ^ (d + 1) < 2 ^ ℓ := lt_of_le_of_lt (q2.trans q1) hb
  have hMPl : Mh * P < 2 ^ ℓ := lt_of_le_of_lt (bMP.trans q1) hb
  have hMl : Mh < 2 ^ ℓ := lt_of_le_of_lt (q3.trans q1) hb
  have hMPD : Mh * P * D < 2 ^ ℓ := lt_of_le_of_lt (mul_le_mul_of_nonneg_right bMP (by omega)) hb
  have h1l : |((1 : ℚ) : ℝ)| < 2 ^ ℓ := by
    rw [Rat.cast_one, abs_one]; exact_mod_cast (lt_of_le_of_lt hM1 hMl)
  have ad4 : 4 + 2 * ((d + 1) * k) < 2 ^ ℓa := by omega
  have ad3 : 3 + 2 * ((d + 1) * k) < 2 ^ ℓa := by omega
  have adD : d + 1 < 2 ^ ℓa := by omega
  have adK : k < 2 ^ ℓa := by omega
  have ix1 : 4 + 2 * ((d + 1) * k) + 2 * (d + 1) ≤ X.off + 1 := by omega
  have ix2 : 4 + 2 * ((d + 1) * k) + 2 * (d + 1) < 2 ^ ℓa := by omega
  have ix3 : 3 + 2 * ((d + 1) * k) + 2 * d ≤ X.off := by omega
  have ix4 : 3 + 2 * ((d + 1) * k) + 2 * d < 2 ^ ℓa := by omega
  have ix5 : 3 + 2 * ((d + 1) * k) + 2 * d + 2 ≤ X.off := by omega
  have ix6 : 3 + 2 * ((d + 1) * k) + 2 * d + 2 < 2 ^ ℓa := by omega
  refine XV.mono (K := (1 + (1 + (1 + 1))) + (1 + (((d + 1) * (4 + 3) + 3) + ((1 + (1 + (1 + 1))) +
    ((d * (1 + (1 + (1 + (1 + (1 + (2 + 1))))) + 3) + 3) + (1 + (1 + (1 + (1 + (1 + 1)))))))))) ?_
    (le_of_eq (by ring)) (fun _ h => h)
  -- the address of the denominators
  refine XV.seq (XV.addr hL (c0 := 4) hnI hn1 hnk hnT (by trimnodup) hσd1 hσk ad4 adD adK) fun σ1 h1 => ?_
  obtain ⟨a1, dr1, F1⟩ := h1
  have n1 : ∀ j, j ≠ nI → j ≠ nT → σ1.nat j = σ.nat j := fun j h1 h2 => F1.1 j (fun h => h.elim h1 h2)
  refine XV.seq (XV.sconst hL hsD (1 : ℚ) rfl h1l) fun σ2 e2 => ?_
  subst e2
  have F2 : FrameA (fun y => y = sD) (fun _ => False) (fun _ _ => False) σ1 (σ1.setSc sD ((1 : ℚ) : ℝ)) :=
    (FrameA.refl (fun y => y = sD) (fun _ => False) (fun _ _ => False) σ1).setSc (x := sD) rfl _
  refine XV.seq (XV.denProd hL (N := d + 1) (c := 4 + 2 * ((d + 1) * k)) (Dn := Dn) (Mh := Mh) hsD hsT DT hnj
      hnI hn1 hno (by trimnodup) (by rw [Env.setSc_nat]; exact a1)
      (by rw [Env.setSc_nat, n1 _ (Ne.symm I1) (Ne.symm T1)]; exact hσd1)
      (by rw [Env.setSc_nat, n1 _ (Ne.symm Io) (Ne.symm To)]; exact hσ1)
      (by rw [sc_setSc_eq, Rat.cast_one]) ix1 ix2
      (fun j hj => by rw [show 4 + 2 * ((d + 1) * k) + 2 * j = 4 + 2 * ((d + 1) * k + j) by ring];
                      exact hinpD j (by omega))
      hM1 (fun j hj => hDn j (by omega)) hPow) fun σ3 h3 => ?_
  obtain ⟨e3, dr3, a3, F3⟩ := h3
  have n3 : ∀ j, j ≠ nj → j ≠ nI → σ3.nat j = σ1.nat j := fun j h1 h2 => by
    rw [F3.1 j (fun h => h.elim h1 h2), Env.setSc_nat]
  -- the address of the numerators
  refine XV.seq (XV.addr hL (c0 := 3) hnI hn1 hnk hnT (by trimnodup)
      (by rw [n3 _ (Ne.symm j1) (Ne.symm I1), n1 _ (Ne.symm I1) (Ne.symm T1)]; exact hσd1)
      (by rw [n3 _ (Ne.symm jk) (Ne.symm Ik), n1 _ (Ne.symm Ik) (Ne.symm Tk)]; exact hσk) ad3 adD adK) fun σ4 h4 => ?_
  obtain ⟨a4, dr4, F4⟩ := h4
  have n4 : ∀ j, j ≠ nI → j ≠ nT → σ4.nat j = σ3.nat j := fun j h1 h2 => F4.1 j (fun h => h.elim h1 h2)
  have s4 : ∀ y, σ4.sc y = σ3.sc y := fun y => F4.2.1 y id
  have o4 : σ4.nat none = 1 := by
    rw [n4 _ (Ne.symm Io) (Ne.symm To), n3 _ (Ne.symm jo) (Ne.symm Io), n1 _ (Ne.symm Io) (Ne.symm To)]; exact hσ1
  refine XV.seq (XV.rowEnt hL (N := d) (c := 3 + 2 * ((d + 1) * k)) (Nm := Nm) (Dn := Dn) (Mh := Mh) (P := P)
      hsD hsT hsN hsQ (by trimnodup) hR hnj hnI hnd hno (by trimnodup) a4
      (by rw [n4 _ (Ne.symm Id) (Ne.symm Td), n3 _ (Ne.symm jd) (Ne.symm Id), n1 _ (Ne.symm Id) (Ne.symm Td)]; exact hσd)
      o4 (by rw [s4, e3]) le_rfl hda ix3 ix4
      (fun j hj => by rw [show 3 + 2 * ((d + 1) * k) + 2 * j = 3 + 2 * ((d + 1) * k + j) by ring];
                      exact hinpN j (by omega))
      (fun j hj => by rw [show 3 + 2 * ((d + 1) * k) + 2 * j + 1 = 4 + 2 * ((d + 1) * k + j) by ring];
                      exact hinpD j (by omega))
      (by omega) hM1 (fun j hj => hNm j (by omega)) (fun j hj => hDn j (by omega)) hMPl hMl)
    fun σ5 h5 => ?_
  obtain ⟨e5, dr5, a5, sD5, F5⟩ := h5
  have o5 : σ5.nat none = 1 := by rw [F5.1 none (fun h => h.elim (fun h => jo h.symm) (fun h => Io h.symm)), o4]
  have sDn5 : σ5.sc sDn = D := by
    rw [F5.2.1 sDn (fun h => h.elim (fun h => TD h.symm) (fun h => h.elim (fun h => ND h.symm)
      (fun h => QD h.symm))), s4, F3.2.1 sDn (fun h => h.elim (fun h => DD h.symm) (fun h => TD h.symm)),
      sc_setSc_ne _ (Ne.symm DD), F1.2.1 sDn id]
    exact hσDn
  refine XV.mono (XV.rowBeta hL (c := 3 + 2 * ((d + 1) * k) + 2 * d) (Nm := Nm d) (Dn := Dn d) (Mh := Mh)
      (P := P) (D := D) hsD hsT hsN hsQ hsB hsDn hss' hnI hno a5 o5 sD5 sDn5 ix5 ix6
      (by rw [show 3 + 2 * ((d + 1) * k) + 2 * d = 3 + 2 * ((d + 1) * k + d) by ring]; exact hinpN d le_rfl)
      (by rw [show 3 + 2 * ((d + 1) * k) + 2 * d + 1 = 4 + 2 * ((d + 1) * k + d) by ring]; exact hinpD d le_rfl)
      p1 hD1 (hNm d le_rfl) (hDn d le_rfl) hMPD) le_rfl fun σ6 h6 => ?_
  obtain ⟨e6, dr6, F6⟩ := h6
  refine ⟨fun j hj => by rw [F6.2.2.1 aRow j id]; exact e5 j hj, e6, by
    rw [dr6, dr5, dr4, dr3, Env.setSc_draws, dr1], ?_⟩
  have G1 := F1.mono (S' := fun y => y = sD ∨ y = sT ∨ y = sN ∨ y = sQ ∨ y = sB)
    (N' := fun j => j = nI ∨ j = nT ∨ j = nj) (Ar' := fun b k' => b = aRow ∧ k' < d)
    (fun _ h => h.elim) (fun _ h => h.elim Or.inl (fun h => Or.inr (Or.inl h))) (fun _ _ h => h.elim)
  have G2 := F2.mono (S' := fun y => y = sD ∨ y = sT ∨ y = sN ∨ y = sQ ∨ y = sB)
    (N' := fun j => j = nI ∨ j = nT ∨ j = nj) (Ar' := fun b k' => b = aRow ∧ k' < d)
    (fun _ h => Or.inl h) (fun _ h => h.elim) (fun _ _ h => h.elim)
  have G3 := F3.mono (S' := fun y => y = sD ∨ y = sT ∨ y = sN ∨ y = sQ ∨ y = sB)
    (N' := fun j => j = nI ∨ j = nT ∨ j = nj) (Ar' := fun b k' => b = aRow ∧ k' < d)
    (fun _ h => h.elim Or.inl (fun h => Or.inr (Or.inl h)))
    (fun _ h => h.elim (fun h => Or.inr (Or.inr h)) Or.inl) (fun _ _ h => h.elim)
  have G4 := F4.mono (S' := fun y => y = sD ∨ y = sT ∨ y = sN ∨ y = sQ ∨ y = sB)
    (N' := fun j => j = nI ∨ j = nT ∨ j = nj) (Ar' := fun b k' => b = aRow ∧ k' < d)
    (fun _ h => h.elim) (fun _ h => h.elim Or.inl (fun h => Or.inr (Or.inl h))) (fun _ _ h => h.elim)
  have G5 := F5.mono (S' := fun y => y = sD ∨ y = sT ∨ y = sN ∨ y = sQ ∨ y = sB)
    (N' := fun j => j = nI ∨ j = nT ∨ j = nj) (Ar' := fun b k' => b = aRow ∧ k' < d)
    (fun _ h => Or.inr (h.imp_right fun h' => h'.imp_right Or.inl))
    (fun _ h => h.elim (fun h => Or.inr (Or.inr h)) Or.inl) (fun _ _ h => h)
  have G6 := F6.mono (S' := fun y => y = sD ∨ y = sT ∨ y = sN ∨ y = sQ ∨ y = sB)
    (N' := fun j => j = nI ∨ j = nT ∨ j = nj) (Ar' := fun b k' => b = aRow ∧ k' < d)
    (fun _ h => Or.inr h) (fun _ h => Or.inl h) (fun _ _ h => h.elim)
  exact G1.trans (G2.trans (G3.trans (G4.trans (G5.trans G6))))

end AdversarialBco.Bit.Transfer
