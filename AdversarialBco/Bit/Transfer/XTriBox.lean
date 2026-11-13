/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriRow

@[expose] public section

/-!
# TRI-M, the box rows of a stage

The box rows `± e_i` with their right-hand sides `2^j D ± ĉ_i 2^e` (`xbox`), the zero loop of an array (`xzero`).
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.TriM Matrix

variable {d : ℕ}

/-- `aR[l] := sZ` for `l < d`. -/
def xzero (L : Layout) (aR sZ nl nd none : ℕ) : XCmd := xforN nl nd none (toX (VL.aset L aR nl sZ))

theorem XV.zero {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {aR sZ nl nd none : ℕ}
    (hR : aR < L.NA) (hsZ : sZ < L.NS) (hnl : nl < L.NN) (hnd : nd < L.NN) (hno : none < L.NN)
    (hne : [nl, nd, none].Nodup) (hσd : σ.nat nd = d) (hσ1 : σ.nat none = 1) (hda : d * d + d < 2 ^ ℓa)
    (eZ : σ.sc sZ = 0) :
    XRunsB L X ℓa ℓ (xzero L aR sZ nl nd none) σ (d * (2 + 3) + 3)
      (fun σ' => (∀ l < d, σ'.arr aR l = 0) ∧ σ'.draws = σ.draws ∧
        FrameA (fun _ => False) (fun j => j = nl) (fun b k => b = aR ∧ k < d) σ σ') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne
  obtain ⟨⟨ld, lo⟩, dO⟩ := hne
  let J : ℕ → Env d → Prop := fun j σ' => (∀ j' < j, σ'.arr aR j' = 0) ∧ σ'.draws = σ.draws ∧ σ'.sc sZ = 0 ∧
    FrameA (fun _ => False) (fun j => j = nl) (fun b k => b = aR ∧ k < j) σ σ'
  refine XV.mono (XV.forN hL hnl hnd hno ld lo d 2 (by omega) J σ hσd hσ1
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, by rw [Env.setNat_sc]; exact eZ,
      (FrameA.refl (fun _ => False) (fun j => j = nl) (fun b k => b = aR ∧ k < 0) σ).setNat rfl 0⟩ ?_) le_rfl
    fun σ' ⟨⟨h1, h2, _, h4⟩, _⟩ => ⟨h1, h2, h4⟩
  intro j hj σ' ⟨hy, hd', hz, hF⟩ hjt hjn hj1
  refine XV.mono (XV.aset hL hR hnl hsZ (by rw [hjt]; unfold asz; nlinarith) (by rw [hz]; simp)) le_rfl
    fun σ1 e1 => ?_
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

/-- A box row: `aR := sg e_i` and `sB := s2jD + sg (ĉ_i sPe)`, `sg` in the slot parameter `sOne`, `ĉ_i` in
the cell `i + 1` of `aC`. -/
def xbox (L : Layout) (aR aC sZ sOne sPe s2jD sT sB ni nl nT nd none : ℕ) : XCmd :=
  .seq (xzero L aR sZ nl nd none) (.seq (toX (VL.aset L aR ni sOne)) (.seq (.prim (.frag (.nadd nT ni none)))
    (.seq (toX (VL.aget L sT aC nT)) (.seq (toX (VL.sop2 L .mul sT sT sPe))
      (.seq (toX (VL.sop2 L .mul sT sT sOne)) (toX (VL.sop2 L .add sB s2jD sT)))))))

set_option maxHeartbeats 1000000 in
theorem XV.box {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {aR aC sZ sOne sPe s2jD sT sB ni nl nT nd none E i : ℕ} {sg Pe Q ch : ℤ}
    (hR : aR < L.NA) (hC : aC < L.NA) (hRC : aR ≠ aC) (hsZ : sZ < L.NS) (hsO : sOne < L.NS) (hsP : sPe < L.NS)
    (hs2 : s2jD < L.NS) (hsT : sT < L.NS) (hsB : sB < L.NS) (hss : [sZ, sOne, sPe, s2jD, sT, sB].Nodup)
    (hni : ni < L.NN) (hnl : nl < L.NN) (hnT : nT < L.NN) (hnd : nd < L.NN) (hno : none < L.NN)
    (hne : [ni, nl, nT, nd, none].Nodup) (hi : i < d) (hσi : σ.nat ni = i) (hσd : σ.nat nd = d)
    (hσ1 : σ.nat none = 1) (hda : d * d + d < 2 ^ ℓa)
    (eZ : σ.sc sZ = 0) (eO : σ.sc sOne = sg) (eP : σ.sc sPe = Pe) (e2 : σ.sc s2jD = Q)
    (eC : σ.arr aC (i + 1) = ch) (hsg : |sg| ≤ 1) (bC : |ch| ≤ 2 ^ E) (bP : |Pe| ≤ 2 ^ E) (bQ : |Q| ≤ 2 ^ E)
    (hE : 2 * E + 2 < ℓ) :
    XRunsB L X ℓa ℓ (xbox L aR aC sZ sOne sPe s2jD sT sB ni nl nT nd none) σ
      (d * (2 + 3) + 3 + (2 + (1 + (2 + (1 + (1 + 1))))))
      (fun σ' => (∀ l < d, σ'.arr aR l = if l = i then (sg : ℝ) else 0) ∧
        σ'.sc sB = ((Q + sg * (ch * Pe) : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => y = sT ∨ y = sB) (fun j => j = nl ∨ j = nT) (fun b k => b = aR ∧ k < d) σ σ') := by
  have hss' := hss
  have hne' := hne
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hss hne
  obtain ⟨⟨ZO, ZP, Z2, ZT, ZB⟩, ⟨OP, O2, OT, OB⟩, ⟨P2, PT, PB⟩, ⟨T2, B2⟩, TB⟩ := hss
  obtain ⟨⟨il, iT, id, io⟩, ⟨lT, ld, lo⟩, ⟨Td, To⟩, dO⟩ := hne
  have hE1 : (2 : ℤ) ^ E ≤ 2 ^ (2 * E) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hE2 : (2 : ℤ) ^ (2 * E + 1) < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) (by omega)
  have hE3 : (2 : ℤ) ^ (2 * E) < 2 ^ (2 * E + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  have cR : ∀ z : ℤ, |z| < 2 ^ ℓ → |(z : ℝ)| < 2 ^ ℓ := fun z h => by
    rw [← Int.cast_abs]; exact_mod_cast h
  have bCP : |ch * Pe| ≤ 2 ^ (2 * E) := by rw [two_mul]; exact absI_mul_le bC bP
  have bsCP : |sg * (ch * Pe)| ≤ 2 ^ (2 * E) := by
    rw [abs_mul]; nlinarith [abs_nonneg (ch * Pe), abs_nonneg sg]
  have bsum : |Q + sg * (ch * Pe)| ≤ 2 ^ (2 * E + 1) := absI_add_le (bQ.trans hE1) bsCP
  refine XV.seq (XV.zero hL hR hsZ hnl hnd hno (by trimnodup) hσd hσ1 hda eZ) fun σ1 h1 => ?_
  obtain ⟨a1, dr1, F1⟩ := h1
  have n1 : ∀ j, j ≠ nl → σ1.nat j = σ.nat j := fun j h => F1.1 j h
  have s1 : ∀ y, σ1.sc y = σ.sc y := fun y => F1.2.1 y not_false
  have h1l : (1 : ℤ) < 2 ^ ℓ := one_lt_pow₀ (by norm_num) (by omega)
  have bsg : |((sg : ℤ) : ℝ)| < 2 ^ ℓ := cR _ (lt_of_le_of_lt hsg h1l)
  have bC' : |((ch : ℤ) : ℝ)| < 2 ^ ℓ := cR _ (by linarith)
  have bP' : |((Pe : ℤ) : ℝ)| < 2 ^ ℓ := cR _ (by linarith)
  have bQ' : |((Q : ℤ) : ℝ)| < 2 ^ ℓ := cR _ (by linarith)
  have bCP' : |((ch * Pe : ℤ) : ℝ)| < 2 ^ ℓ := cR _ (by linarith)
  have bCPs : |((ch * Pe * sg : ℤ) : ℝ)| < 2 ^ ℓ := cR _ (by rw [mul_comm]; linarith)
  have bsum' : |((Q + ch * Pe * sg : ℤ) : ℝ)| < 2 ^ ℓ := cR _ (by rw [mul_comm (ch * Pe)]; linarith)
  refine XV.seq (XV.aset hL hR hni hsO (by rw [n1 _ il, hσi]; unfold asz; nlinarith)
    (by rw [s1, eO]; exact bsg)) fun σ2 e2' => ?_
  subst e2'
  refine XV.seq (XV.nadd hL hnT hni hno (by rw [Env.setArr_nat, n1 _ il, hσi]; omega)
    (by rw [Env.setArr_nat, n1 _ (fun h => lo h.symm), hσ1]; omega)) fun σ3 e3 => ?_
  subst e3
  have t3 : ((σ1.setArr aR (σ1.nat ni) (σ1.sc sOne)).setNat nT
      ((σ1.setArr aR (σ1.nat ni) (σ1.sc sOne)).nat ni + (σ1.setArr aR (σ1.nat ni) (σ1.sc sOne)).nat none)).nat nT
      = i + 1 := by
    rw [nat_setNat_eq, Env.setArr_nat, n1 _ il, n1 _ (fun h => lo h.symm), hσi, hσ1]
  have c3 : σ1.arr aC (i + 1) = ch := by rw [F1.2.2.1 aC (i + 1) (fun h => hRC h.1.symm), eC]
  refine XV.seq (XV.aget hL hsT hC hnT (by rw [t3]; unfold asz; nlinarith)
    (by rw [t3, Env.setNat_arr, Env.setArr_arr, ite_eq_right_of_eq_false _ _ (eq_false fun h => hRC h.1.symm), c3];
        exact bC')) fun σ4 e4 => ?_
  subst e4
  set σ3 := (σ1.setArr aR (σ1.nat ni) (σ1.sc sOne)).setNat nT
      ((σ1.setArr aR (σ1.nat ni) (σ1.sc sOne)).nat ni + (σ1.setArr aR (σ1.nat ni) (σ1.sc sOne)).nat none) with hσ3
  have v4 : (σ3.setSc sT (σ3.arr aC (σ3.nat nT))).sc sT = ch ∧ (σ3.setSc sT (σ3.arr aC (σ3.nat nT))).sc sPe = Pe ∧
      (σ3.setSc sT (σ3.arr aC (σ3.nat nT))).sc sOne = sg ∧ (σ3.setSc sT (σ3.arr aC (σ3.nat nT))).sc s2jD = Q := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [sc_setSc_eq, t3, hσ3, Env.setNat_arr, Env.setArr_arr,
        ite_eq_right_of_eq_false _ _ (eq_false fun h => hRC h.1.symm), c3]
    · rw [sc_setSc_ne _ PT, hσ3, Env.setNat_sc, Env.setArr_sc, s1, eP]
    · rw [sc_setSc_ne _ OT, hσ3, Env.setNat_sc, Env.setArr_sc, s1, eO]
    · rw [sc_setSc_ne _ T2, hσ3, Env.setNat_sc, Env.setArr_sc, s1, e2]
  set σ4 := σ3.setSc sT (σ3.arr aC (σ3.nat nT)) with hσ4
  refine XV.seq (XV.sop2 hL hsT hsT hsP .mul (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
    (by rw [v4.1]; exact bC') (by rw [v4.2.1]; exact bP')
    (by rw [v4.1, v4.2.1]; simp only [RealRAM.Op2.eval]; exact_mod_cast bCP')) fun σ5 e5 => ?_
  have v5 : σ5.sc sT = ((ch * Pe : ℤ) : ℝ) ∧ σ5.sc sOne = sg ∧ σ5.sc s2jD = Q := by
    subst e5; refine ⟨?_, ?_, ?_⟩
    · rw [sc_setSc_eq, v4.1, v4.2.1]; simp only [RealRAM.Op2.eval]; push_cast; ring
    · rw [sc_setSc_ne _ OT, v4.2.2.1]
    · rw [sc_setSc_ne _ T2, v4.2.2.2]
  refine XV.seq (XV.sop2 hL hsT hsT hsO .mul (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
    (by rw [v5.1]; exact bCP') (by rw [v5.2.1]; exact bsg)
    (by rw [v5.1, v5.2.1]; simp only [RealRAM.Op2.eval]; exact_mod_cast bCPs)) fun σ6 e6 => ?_
  have v6 : σ6.sc sT = ((ch * Pe * sg : ℤ) : ℝ) ∧ σ6.sc s2jD = Q := by
    subst e6; refine ⟨?_, ?_⟩
    · rw [sc_setSc_eq, v5.1, v5.2.1]; simp only [RealRAM.Op2.eval]; push_cast; ring
    · rw [sc_setSc_ne _ T2, v5.2.2]
  refine XV.mono (XV.sop2 hL hsB hs2 hsT .add (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
    (by rw [v6.2]; exact bQ') (by rw [v6.1]; exact bCPs)
    (by rw [v6.1, v6.2]; simp only [RealRAM.Op2.eval]; exact_mod_cast bsum')) le_rfl fun σ7 e7 => ?_
  have a7 : ∀ b k, σ7.arr b k = σ4.arr b k := fun b k => by subst e7 e6 e5; rfl
  refine ⟨fun l hl => ?_, ?_, ?_, ?_⟩
  · rw [a7, hσ4, Env.setSc_arr, hσ3, Env.setNat_arr, Env.setArr_arr, n1 _ il, hσi]
    by_cases h : l = i
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, h⟩), ite_eq_left_of_eq_true _ _ (eq_true h), s1, eO]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h' => h h'.2), ite_eq_right_of_eq_false _ _ (eq_false h)]
      exact a1 l hl
  · subst e7; rw [sc_setSc_eq, v6.1, v6.2]; simp only [RealRAM.Op2.eval]; push_cast; ring
  · subst e7 e6 e5; rw [Env.setSc_draws, Env.setSc_draws, Env.setSc_draws, hσ4, Env.setSc_draws, hσ3,
      Env.setNat_draws, Env.setArr_draws, dr1]
  · have G1 := F1.mono (S' := fun y => y = sT ∨ y = sB) (N' := fun j => j = nl ∨ j = nT)
      (Ar' := fun b k => b = aR ∧ k < d) (fun _ h => h.elim) (fun _ h => Or.inl h) (fun _ _ h => h)
    have G2 : FrameA (fun y => y = sT ∨ y = sB) (fun j => j = nl ∨ j = nT) (fun b k => b = aR ∧ k < d) σ1 σ7 := by
      subst e7 e6 e5
      exact (((((FrameA.refl (fun y => y = sT ∨ y = sB) (fun j => j = nl ∨ j = nT) (fun b k => b = aR ∧ k < d)
        σ1).setArr ⟨rfl, by rw [n1 _ il, hσi]; exact hi⟩ _).setNat (Or.inr rfl) _).setSc (Or.inl rfl) _).setSc
        (Or.inl rfl) _ |>.setSc (Or.inl rfl) _).setSc (Or.inr rfl) _
    exact G1.trans G2

end AdversarialBco.Bit.Transfer
