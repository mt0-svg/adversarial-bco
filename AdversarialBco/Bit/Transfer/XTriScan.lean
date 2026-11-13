/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriRow

@[expose] public section

/-!
# TRI-M, the scan of the rows on the machine

One row of the scan of `tzKeep` (Transfer/XTriZ.lean): the normalised quotient `qn N β̃` and the sign of `β̃`
(`xqn`), the comparison with the best quotient and the keep (`xtkeep`, with the signed copy `xscale` of the row).
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.TriM Matrix

variable {d : ℕ}

/-- A disequality of indices from the context, in either direction. -/
macro "trimne" : tactic => `(tactic| first | assumption | (apply Ne.symm; assumption) | omega)

/-- `trimenv` with the disequalities from the context. -/
macro "trimenv'" : tactic =>
  `(tactic| (simp (disch := trimne) only [nat_setNat_ne, nat_setNat_eq, sc_setSc_ne, sc_setSc_eq,
    Env.setNat_sc, Env.setSc_nat, Env.setArr_nat, Env.setArr_sc, Env.setNat_arr, Env.setSc_arr, Env.setNat_draws,
    Env.setSc_draws, Env.setArr_draws]))

/-- `(sQN, sQB) := qn sN sBt` and `sSg := sign sBt`; the slot parameters `sZ`, `sOne`, `sMOne` hold `0`, `1`,
`-1`. -/
def xqn (L : Layout) (sZ sOne sMOne sN sBt sQN sQB sSg : ℕ) : XCmd :=
  xifS L sZ sBt
    (.seq (toX (VL.sop2 L .add sQN sN sZ)) (.seq (toX (VL.sop2 L .add sQB sBt sZ))
      (toX (VL.sop2 L .add sSg sOne sZ))))
    (xifS L sBt sZ
      (.seq (toX (VL.sop2 L .sub sQN sZ sN)) (.seq (toX (VL.sop2 L .sub sQB sZ sBt))
        (toX (VL.sop2 L .add sSg sMOne sZ))))
      (.seq (toX (VL.sop2 L .add sQN sZ sZ)) (.seq (toX (VL.sop2 L .add sQB sOne sZ))
        (toX (VL.sop2 L .add sSg sZ sZ)))))

set_option maxHeartbeats 1000000 in
theorem XV.qnRun {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {sZ sOne sMOne sN sBt sQN sQB sSg : ℕ} {N B : ℤ} (hZ : sZ < L.NS) (hO : sOne < L.NS) (hM : sMOne < L.NS)
    (hN : sN < L.NS) (hB : sBt < L.NS) (hQN : sQN < L.NS) (hQB : sQB < L.NS) (hSg : sSg < L.NS)
    (hss : [sZ, sOne, sMOne, sN, sBt, sQN, sQB, sSg].Nodup) (eZ : σ.sc sZ = 0) (eO : σ.sc sOne = 1)
    (eM : σ.sc sMOne = -1) (eN : σ.sc sN = N) (eB : σ.sc sBt = B) (bN : |N| < 2 ^ ℓ) (bB : |B| < 2 ^ ℓ)
    (h1 : (1 : ℤ) < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xqn L sZ sOne sMOne sN sBt sQN sQB sSg) σ 7
      (fun σ' => σ'.sc sQN = (qn N B).1 ∧ σ'.sc sQB = (qn N B).2 ∧ σ'.sc sSg = Int.sign B ∧
        σ'.draws = σ.draws ∧
        FrameA (fun y => y = sQN ∨ y = sQB ∨ y = sSg) (fun _ => False) (fun _ _ => False) σ σ') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil, not_false_eq_true,
    and_true] at hss
  obtain ⟨⟨ZO, ZM, ZN, ZB, ZQN, ZQB, ZS⟩, ⟨OM, ON, OB, OQN, OQB, OS⟩, ⟨MN, MB, MQN, MQB, MS⟩, ⟨NB, NQN, NQB, NS⟩,
    ⟨BQN, BQB, BS⟩, ⟨QNQB, QNS⟩, QBS⟩ := hss
  have cR : ∀ z : ℤ, |z| < 2 ^ ℓ → |(z : ℝ)| < 2 ^ ℓ := fun z h => by
    rw [← Int.cast_abs]; exact_mod_cast h
  have b0 : |((0 : ℤ) : ℝ)| < 2 ^ ℓ := cR 0 (by simp)
  have b1 : |((1 : ℤ) : ℝ)| < 2 ^ ℓ := cR 1 (by simpa using h1)
  have bm1 : |((-1 : ℤ) : ℝ)| < 2 ^ ℓ := cR (-1) (by simpa using h1)
  have bN' := cR N bN
  have bB' := cR B bB
  have bmN : |((-N : ℤ) : ℝ)| < 2 ^ ℓ := cR (-N) (by rwa [abs_neg])
  have bmB : |((-B : ℤ) : ℝ)| < 2 ^ ℓ := cR (-B) (by rwa [abs_neg])
  have hne : ∀ o : RealRAM.Op2, o = .add ∨ o = .sub → o ≠ .div := by
    rintro o (rfl | rfl) <;> simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  -- the three assignments of a branch
  have three : ∀ (σ0 : Env d) (o1 o2 o3 : RealRAM.Op2) (a1 b1 a2 b2 a3 b3 : ℕ) (v1 v2 v3 : ℤ),
      (o1 = .add ∨ o1 = .sub) → (o2 = .add ∨ o2 = .sub) → (o3 = .add ∨ o3 = .sub) →
      a1 < L.NS → b1 < L.NS → a2 < L.NS → b2 < L.NS → a3 < L.NS → b3 < L.NS →
      (∀ y, y ≠ sQN → y ≠ sQB → y ≠ sSg → σ0.sc y = σ.sc y) → σ0.draws = σ.draws →
      (∀ y, y = a1 ∨ y = b1 ∨ y = a2 ∨ y = b2 ∨ y = a3 ∨ y = b3 → y ≠ sQN ∧ y ≠ sQB ∧ y ≠ sSg) →
      |σ0.sc a1| < 2 ^ ℓ → |σ0.sc b1| < 2 ^ ℓ → o1.eval (σ0.sc a1) (σ0.sc b1) = v1 → |(v1 : ℝ)| < 2 ^ ℓ →
      |σ0.sc a2| < 2 ^ ℓ → |σ0.sc b2| < 2 ^ ℓ → o2.eval (σ0.sc a2) (σ0.sc b2) = v2 → |(v2 : ℝ)| < 2 ^ ℓ →
      |σ0.sc a3| < 2 ^ ℓ → |σ0.sc b3| < 2 ^ ℓ → o3.eval (σ0.sc a3) (σ0.sc b3) = v3 → |(v3 : ℝ)| < 2 ^ ℓ →
      FrameA (fun y => y = sQN ∨ y = sQB ∨ y = sSg) (fun _ => False) (fun _ _ => False) σ σ0 →
      XRunsB L X ℓa ℓ (.seq (toX (VL.sop2 L o1 sQN a1 b1)) (.seq (toX (VL.sop2 L o2 sQB a2 b2))
        (toX (VL.sop2 L o3 sSg a3 b3)))) σ0 (1 + (1 + 1))
        (fun σ' => σ'.sc sQN = v1 ∧ σ'.sc sQB = v2 ∧ σ'.sc sSg = v3 ∧ σ'.draws = σ.draws ∧
          FrameA (fun y => y = sQN ∨ y = sQB ∨ y = sSg) (fun _ => False) (fun _ _ => False) σ σ') := by
    intro σ0 o1 o2 o3 a1 b1 a2 b2 a3 b3 v1 v2 v3 ho1 ho2 ho3 ha1 hb1 ha2 hb2 ha3 hb3 _ hd0 hdis
      va1 vb1 ev1 bv1 va2 vb2 ev2 bv2 va3 vb3 ev3 bv3 F0
    obtain ⟨a1Q, a1B, a1S⟩ := hdis a1 (Or.inl rfl)
    obtain ⟨b1Q, b1B, b1S⟩ := hdis b1 (Or.inr (Or.inl rfl))
    obtain ⟨a2Q, a2B, a2S⟩ := hdis a2 (Or.inr (Or.inr (Or.inl rfl)))
    obtain ⟨b2Q, b2B, b2S⟩ := hdis b2 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    obtain ⟨a3Q, a3B, a3S⟩ := hdis a3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    obtain ⟨b3Q, b3B, b3S⟩ := hdis b3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    refine XV.seq (XV.sop2 hL hQN ha1 hb1 o1 (hne o1 ho1) va1 vb1 (by rw [ev1]; exact bv1)) fun σ1 e1 => ?_
    subst e1
    refine XV.seq (XV.sop2 hL hQB ha2 hb2 o2 (hne o2 ho2) (by rw [sc_setSc_ne _ a2Q]; exact va2)
      (by rw [sc_setSc_ne _ b2Q]; exact vb2) (by rw [sc_setSc_ne _ a2Q, sc_setSc_ne _ b2Q, ev2]; exact bv2))
      fun σ2 e2 => ?_
    subst e2
    refine XV.mono (XV.sop2 hL hSg ha3 hb3 o3 (hne o3 ho3)
      (by rw [sc_setSc_ne _ a3B, sc_setSc_ne _ a3Q]; exact va3)
      (by rw [sc_setSc_ne _ b3B, sc_setSc_ne _ b3Q]; exact vb3)
      (by rw [sc_setSc_ne _ a3B, sc_setSc_ne _ a3Q, sc_setSc_ne _ b3B, sc_setSc_ne _ b3Q, ev3]; exact bv3))
      le_rfl fun σ3 e3 => ?_
    subst e3
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [sc_setSc_ne _ QNS, sc_setSc_ne _ QNQB, sc_setSc_eq, ev1]
    · rw [sc_setSc_ne _ QBS, sc_setSc_eq, sc_setSc_ne _ a2Q, sc_setSc_ne _ b2Q, ev2]
    · rw [sc_setSc_eq, sc_setSc_ne _ a3B, sc_setSc_ne _ a3Q, sc_setSc_ne _ b3B, sc_setSc_ne _ b3Q, ev3]
    · simp only [Env.setSc_draws, hd0]
    · exact ((F0.setSc (Or.inl rfl) _).setSc (Or.inr (Or.inl rfl)) _).setSc (Or.inr (Or.inr rfl)) _
  have dis : ∀ y, (y = sZ ∨ y = sOne ∨ y = sMOne ∨ y = sN ∨ y = sBt) → y ≠ sQN ∧ y ≠ sQB ∧ y ≠ sSg := by
    rintro y (rfl | rfl | rfl | rfl | rfl) <;> exact ⟨by assumption, by assumption, by assumption⟩
  have F0 := FrameA.refl (fun y => y = sQN ∨ y = sQB ∨ y = sSg) (fun _ => False) (fun _ _ => False) σ
  rcases lt_trichotomy 0 B with hBp | hB0 | hBn
  · have hq : qn N B = (N, B) := by unfold qn; rw [if_pos hBp]
    refine XV.mono (XV.ifS_t hL hZ hB (by rw [eZ]; simpa using b0) (by rw [eB]; exact bB')
      (by rw [eZ, eB]; exact_mod_cast hBp)
      (three σ .add .add .add sN sZ sBt sZ sOne sZ N B 1 (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hN hZ hB hZ hO hZ
        (fun _ _ _ _ => rfl) rfl (fun y h => dis y (by tauto)) (by rw [eN]; exact bN') (by rw [eZ]; simpa using b0)
        (by rw [eN, eZ]; simp [RealRAM.Op2.eval]) bN' (by rw [eB]; exact bB') (by rw [eZ]; simpa using b0)
        (by rw [eB, eZ]; simp [RealRAM.Op2.eval]) bB' (by rw [eO]; simpa using b1) (by rw [eZ]; simpa using b0)
        (by rw [eO, eZ]; simp [RealRAM.Op2.eval]) b1 F0)) (by norm_num)
      fun σ' ⟨h1, h2, h3, h4, h5⟩ => ⟨by rw [h1, hq], by rw [h2, hq], by rw [h3, Int.sign_eq_one_of_pos hBp]; try simp, h4, h5⟩
  · subst hB0
    have hq : qn N 0 = (0, 1) := by unfold qn; simp
    refine XV.mono (XV.ifS_f hL hZ hB (by rw [eZ]; simpa using b0) (by rw [eB]; simpa using b0)
      (by rw [eZ, eB]; simp)
      (XV.ifS_f hL hB hZ (by rw [eB]; simpa using b0) (by rw [eZ]; simpa using b0) (by rw [eZ, eB]; simp)
      (three σ .add .add .add sZ sZ sOne sZ sZ sZ 0 1 0 (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) hZ hZ hO hZ hZ hZ
        (fun _ _ _ _ => rfl) rfl (fun y h => dis y (by tauto)) (by rw [eZ]; simpa using b0)
        (by rw [eZ]; simpa using b0) (by rw [eZ]; simp [RealRAM.Op2.eval]) b0 (by rw [eO]; simpa using b1)
        (by rw [eZ]; simpa using b0) (by rw [eO, eZ]; simp [RealRAM.Op2.eval]) b1 (by rw [eZ]; simpa using b0)
        (by rw [eZ]; simpa using b0) (by rw [eZ]; simp [RealRAM.Op2.eval]) b0 F0))) (by norm_num)
      fun σ' ⟨h1, h2, h3, h4, h5⟩ => ⟨by rw [h1, hq], by rw [h2, hq], by rw [h3]; try simp, h4, h5⟩
  · have hq : qn N B = (-N, -B) := by unfold qn; rw [if_neg (by omega), if_pos hBn]
    refine XV.mono (XV.ifS_f hL hZ hB (by rw [eZ]; simpa using b0) (by rw [eB]; exact bB')
      (by rw [eZ, eB]; exact_mod_cast (show ¬ (0 : ℤ) < B by omega))
      (XV.ifS_t hL hB hZ (by rw [eB]; exact bB') (by rw [eZ]; simpa using b0) (by rw [eZ, eB]; exact_mod_cast hBn)
      (three σ .sub .sub .add sZ sN sZ sBt sMOne sZ (-N) (-B) (-1) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) hZ hN hZ hB
        hM hZ (fun _ _ _ _ => rfl) rfl (fun y h => dis y (by tauto)) (by rw [eZ]; simpa using b0)
        (by rw [eN]; exact bN') (by rw [eZ, eN]; simp [RealRAM.Op2.eval]) bmN (by rw [eZ]; simpa using b0)
        (by rw [eB]; exact bB') (by rw [eZ, eB]; simp [RealRAM.Op2.eval]) bmB (by rw [eM]; simpa using bm1)
        (by rw [eZ]; simpa using b0) (by rw [eM, eZ]; simp [RealRAM.Op2.eval]) bm1 F0))) (by norm_num)
      fun σ' ⟨h1, h2, h3, h4, h5⟩ => ⟨by rw [h1, hq], by rw [h2, hq], by rw [h3, Int.sign_eq_neg_one_of_neg hBn]; try simp,
        h4, h5⟩

/-- `aK[l] := aRow[l] * sSg` for `l < d`. -/
def xscale (L : Layout) (aK aRow sSg sT nl nd none : ℕ) : XCmd :=
  xforN nl nd none (.seq (toX (VL.aget L sT aRow nl)) (.seq (toX (VL.sop2 L .mul sT sT sSg))
    (toX (VL.aset L aK nl sT))))

set_option maxHeartbeats 1000000 in
theorem XV.scale {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {aK aRow sSg sT nl nd none E : ℕ} {a : Fin d → ℤ} {sg : ℤ} (hK : aK < L.NA) (hR : aRow < L.NA) (hKR : aK ≠ aRow)
    (hsS : sSg < L.NS) (hsT : sT < L.NS) (hST : sSg ≠ sT) (hnl : nl < L.NN) (hnd : nd < L.NN) (hno : none < L.NN)
    (hne : [nl, nd, none].Nodup) (hσd : σ.nat nd = d) (hσ1 : σ.nat none = 1) (hda : d * d + d < 2 ^ ℓa)
    (eS : σ.sc sSg = sg) (eR : ∀ l : Fin d, σ.arr aRow l = a l) (hsg : |sg| ≤ 1) (ba : ∀ l, |a l| ≤ 2 ^ E)
    (hE : E < ℓ) :
    XRunsB L X ℓa ℓ (xscale L aK aRow sSg sT nl nd none) σ (d * (2 + (1 + 2) + 3) + 3)
      (fun σ' => (∀ l : Fin d, σ'.arr aK l = ((sg * a l : ℤ) : ℝ)) ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => y = sT) (fun j => j = nl) (fun b k => b = aK ∧ k < d) σ σ') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil, not_false_eq_true,
    and_true] at hne
  obtain ⟨⟨ld, lo⟩, dO⟩ := hne
  have hEl : (2 : ℤ) ^ E < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) hE
  have cR : ∀ z : ℤ, |z| ≤ 2 ^ E → |(z : ℝ)| < 2 ^ ℓ := fun z h => by
    rw [← Int.cast_abs]; exact_mod_cast lt_of_le_of_lt h hEl
  have bsa : ∀ l, |a l * sg| ≤ 2 ^ E := fun l => by
    rw [abs_mul]; nlinarith [abs_nonneg (a l), abs_nonneg sg, ba l]
  have bs : |sg| ≤ 2 ^ E := hsg.trans (one_le_pow₀ (by norm_num))
  let J : ℕ → Env d → Prop := fun j σ' => (∀ l : Fin d, l.1 < j → σ'.arr aK l = ((sg * a l : ℤ) : ℝ)) ∧
    σ'.draws = σ.draws ∧ FrameA (fun y => y = sT) (fun j => j = nl) (fun b k => b = aK ∧ k < j) σ σ'
  refine XV.mono (XV.forN hL hnl hnd hno ld lo d (2 + (1 + 2)) (by omega) J σ hσd hσ1
    ⟨fun l h => absurd h (Nat.not_lt_zero _), rfl,
      (FrameA.refl (fun y => y = sT) (fun j => j = nl) (fun b k => b = aK ∧ k < 0) σ).setNat rfl 0⟩ ?_) le_rfl
    fun σ' ⟨⟨h1, h2, h3⟩, _⟩ => ⟨fun l => h1 l l.2, h2, h3⟩
  intro j hj σ' ⟨hy, hd', hF⟩ hjt hjn hj1
  have eRj : σ'.arr aRow j = a ⟨j, hj⟩ := by rw [hF.2.2.1 aRow j (fun h => hKR h.1.symm)]; exact eR ⟨j, hj⟩
  have eSj : σ'.sc sSg = sg := by rw [hF.2.1 sSg hST]; exact eS
  have hcell : j < asz d := by unfold asz; nlinarith
  refine XV.seq (XV.aget hL hsT hR hnl (by rw [hjt]; exact hcell) (by rw [hjt, eRj]; exact cR _ (ba _)))
    fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.sop2 hL hsT hsT hsS .mul (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
    (by rw [sc_setSc_eq, hjt, eRj]; exact cR _ (ba _)) (by rw [sc_setSc_ne _ hST, eSj]; exact cR _ bs)
    (by rw [sc_setSc_eq, sc_setSc_ne _ hST, hjt, eRj, eSj]; simp only [RealRAM.Op2.eval]; exact_mod_cast cR _ (bsa _)))
    fun σ2 e2 => ?_
  subst e2
  refine XV.mono (XV.aset hL hK hnl hsT (by rw [Env.setSc_nat, Env.setSc_nat, hjt]; exact hcell)
    (by rw [sc_setSc_eq, sc_setSc_eq, sc_setSc_ne _ hST, hjt, eRj, eSj]; simp only [RealRAM.Op2.eval];
        exact_mod_cast cR _ (bsa _))) le_rfl fun σ3 e3 => ?_
  subst e3
  refine ⟨by simp only [Env.setArr_nat, Env.setSc_nat]; exact hjt, by simp only [Env.setArr_nat, Env.setSc_nat]; exact hjn,
    by simp only [Env.setArr_nat, Env.setSc_nat]; exact hj1, fun l hl => ?_,
    by simp only [Env.setNat_draws, Env.setArr_draws, Env.setSc_draws]; exact hd', ?_⟩
  · rw [Env.setNat_arr, Env.setArr_arr, Env.setSc_nat, Env.setSc_nat, hjt]
    by_cases h : l.1 = j
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, h⟩)]
      simp only [sc_setSc_eq, sc_setSc_ne _ hST, Env.setSc_arr, Env.setSc_nat, hjt, eSj, RealRAM.Op2.eval]
      have : l = ⟨j, hj⟩ := Fin.ext h
      rw [← this] at eRj; rw [eRj]; push_cast; ring
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h' => h h'.2)]
      exact hy l (by omega)
  · exact ((((hF.mono (fun _ h => h) (fun _ h => h) (fun b k h => ⟨h.1, by omega⟩)).setSc rfl _).setSc rfl _).setArr
      ⟨rfl, by simp only [Env.setSc_nat, hjt]; omega⟩ _).setNat rfl _

/-- The keep of the scan: if `sBn * sQB < sQN * sBd` then `sBn := sQN`, `sBd := sQB`, `sBb := sQB`,
`aK := sSg • aRow`. -/
def xtkeep (L : Layout) (sZ sBn sBd sBb sQN sQB sSg sL sR sT aK aRow nl nd none : ℕ) : XCmd :=
  .seq (toX (VL.sop2 L .mul sL sBn sQB)) (.seq (toX (VL.sop2 L .mul sR sQN sBd))
    (xifS L sL sR (.seq (toX (VL.sop2 L .add sBn sQN sZ)) (.seq (toX (VL.sop2 L .add sBd sQB sZ))
      (.seq (toX (VL.sop2 L .add sBb sQB sZ)) (xscale L aK aRow sSg sT nl nd none)))) .skip))

set_option maxHeartbeats 2000000 in
theorem XV.tkeep {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {sZ sBn sBd sBb sQN sQB sSg sL sR sT aK aRow nl nd none E : ℕ} {st : Scan d} {N B : ℤ} {a : Fin d → ℤ}
    (hsZ : sZ < L.NS) (hsBn : sBn < L.NS) (hsBd : sBd < L.NS) (hsBb : sBb < L.NS) (hsQN : sQN < L.NS)
    (hsQB : sQB < L.NS) (hsS : sSg < L.NS) (hsL : sL < L.NS) (hsR : sR < L.NS) (hsT : sT < L.NS)
    (hss : [sZ, sBn, sBd, sBb, sQN, sQB, sSg, sL, sR, sT].Nodup) (hK : aK < L.NA) (hR : aRow < L.NA)
    (hKR : aK ≠ aRow) (hnl : nl < L.NN) (hnd : nd < L.NN) (hno : none < L.NN) (hne : [nl, nd, none].Nodup)
    (hσd : σ.nat nd = d) (hσ1 : σ.nat none = 1) (hda : d * d + d < 2 ^ ℓa)
    (eZ : σ.sc sZ = 0) (eBn : σ.sc sBn = st.bn) (eBd : σ.sc sBd = st.bd) (eBb : σ.sc sBb = st.bb)
    (eK : ∀ l : Fin d, σ.arr aK l = st.row l) (eQN : σ.sc sQN = (qn N B).1) (eQB : σ.sc sQB = (qn N B).2)
    (eS : σ.sc sSg = Int.sign B) (eR : ∀ l : Fin d, σ.arr aRow l = a l)
    (bn : |st.bn| ≤ 2 ^ E) (bd : |st.bd| ≤ 2 ^ E) (bqN : |(qn N B).1| ≤ 2 ^ E) (bqB : |(qn N B).2| ≤ 2 ^ E)
    (ba : ∀ l, |a l| ≤ 2 ^ E) (hE : 2 * E < ℓ) :
    XRunsB L X ℓa ℓ (xtkeep L sZ sBn sBd sBb sQN sQB sSg sL sR sT aK aRow nl nd none) σ (8 * d + 9)
      (fun σ' => σ'.sc sBn = (scanStep st N B a).bn ∧ σ'.sc sBd = (scanStep st N B a).bd ∧
        σ'.sc sBb = (scanStep st N B a).bb ∧ (∀ l : Fin d, σ'.arr aK l = (scanStep st N B a).row l) ∧
        σ'.draws = σ.draws ∧
        FrameA (fun y => y = sBn ∨ y = sBd ∨ y = sBb ∨ y = sL ∨ y = sR ∨ y = sT) (fun j => j = nl)
          (fun b k => b = aK ∧ k < d) σ σ') := by
  have hss' := hss
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil, not_false_eq_true,
    and_true] at hss
  obtain ⟨⟨Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9⟩, ⟨n2, n3, n4, n5, n6, n7, n8, n9⟩, ⟨d3, d4, d5, d6, d7, d8, d9⟩,
    ⟨b4, b5, b6, b7, b8, b9⟩, ⟨N5, N6, N7, N8, N9⟩, ⟨B6, B7, B8, B9⟩, ⟨S7, S8, S9⟩, ⟨L8, L9⟩, R9⟩ := hss
  have h2E : (2 : ℤ) ^ (2 * E) < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) hE
  have hEE : (2 : ℤ) ^ E ≤ 2 ^ (2 * E) := pow_le_pow_right₀ (by norm_num) (by omega)
  have cR : ∀ z : ℤ, |z| ≤ 2 ^ (2 * E) → |(z : ℝ)| < 2 ^ ℓ := fun z h => by
    rw [← Int.cast_abs]; exact_mod_cast lt_of_le_of_lt h h2E
  have cE : ∀ z : ℤ, |z| ≤ 2 ^ E → |(z : ℝ)| < 2 ^ ℓ := fun z h => cR z (h.trans hEE)
  have bm : ∀ x y : ℤ, |x| ≤ 2 ^ E → |y| ≤ 2 ^ E → |x * y| ≤ 2 ^ (2 * E) := fun x y hx hy => by
    rw [two_mul]; exact absI_mul_le hx hy
  have hsg1 : |Int.sign B| ≤ 1 := by
    rcases lt_trichotomy B 0 with h | h | h
    · rw [Int.sign_eq_neg_one_of_neg h]; norm_num
    · subst h; simp
    · rw [Int.sign_eq_one_of_pos h]; norm_num
  have bZ : |((0 : ℤ) : ℝ)| < 2 ^ ℓ := cR 0 (by simp)
  refine XV.mono (K := 1 + (1 + (8 * d + 7))) ?_ (by omega) (fun _ h => h)
  refine XV.seq (XV.sop2 hL hsL hsBn hsQB .mul (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
    (by rw [eBn]; exact cE _ bn) (by rw [eQB]; exact cE _ bqB)
    (by rw [eBn, eQB]; simp only [RealRAM.Op2.eval]; exact_mod_cast cR _ (bm _ _ bn bqB))) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.sop2 hL hsR hsQN hsBd .mul (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
    (by trimenv'; rw [eQN]; exact cE _ bqN) (by trimenv'; rw [eBd]; exact cE _ bd)
    (by trimenv'; rw [eQN, eBd]; simp only [RealRAM.Op2.eval]; exact_mod_cast cR _ (bm _ _ bqN bd)))
    fun σ2 e2 => ?_
  subst e2
  generalize hσ2 : (σ.setSc sL (RealRAM.Op2.mul.eval (σ.sc sBn) (σ.sc sQB))).setSc sR
    (RealRAM.Op2.mul.eval ((σ.setSc sL (RealRAM.Op2.mul.eval (σ.sc sBn) (σ.sc sQB))).sc sQN)
      ((σ.setSc sL (RealRAM.Op2.mul.eval (σ.sc sBn) (σ.sc sQB))).sc sBd)) = σ2
  have v2 : σ2.sc sL = ((st.bn * (qn N B).2 : ℤ) : ℝ) ∧ σ2.sc sR = (((qn N B).1 * st.bd : ℤ) : ℝ) := by
    constructor
    · rw [← hσ2]; trimenv'; rw [eBn, eQB]; simp only [RealRAM.Op2.eval]; push_cast; ring
    · rw [← hσ2]; trimenv'; rw [eQN, eBd]; simp only [RealRAM.Op2.eval]; push_cast; ring
  have s2 : ∀ y, y ≠ sL → y ≠ sR → σ2.sc y = σ.sc y := fun y h1 h2 => by
    rw [← hσ2, sc_setSc_ne _ h2, sc_setSc_ne _ h1]
  have F2 : FrameA (fun y => y = sBn ∨ y = sBd ∨ y = sBb ∨ y = sL ∨ y = sR ∨ y = sT) (fun j => j = nl)
      (fun b k => b = aK ∧ k < d) σ σ2 := by
    rw [← hσ2]
    exact ((FrameA.refl _ _ _ σ).setSc (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _).setSc
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) _
  have n2 : σ2.nat = σ.nat := by rw [← hσ2]; simp only [Env.setSc_nat]
  have a2 : σ2.arr = σ.arr := by rw [← hσ2]; simp only [Env.setSc_arr]
  have d2 : σ2.draws = σ.draws := by rw [← hσ2]; simp only [Env.setSc_draws]
  have eQN2 : σ2.sc sQN = (qn N B).1 := by rw [s2 _ (by trimne) (by trimne), eQN]
  have eQB2 : σ2.sc sQB = (qn N B).2 := by rw [s2 _ (by trimne) (by trimne), eQB]
  have eZ2 : σ2.sc sZ = 0 := by rw [s2 _ (by trimne) (by trimne), eZ]
  have eS2 : σ2.sc sSg = Int.sign B := by rw [s2 _ (by trimne) (by trimne), eS]
  by_cases hc : st.bn * (qn N B).2 < (qn N B).1 * st.bd
  · have hst : scanStep st N B a = ⟨(qn N B).1, (qn N B).2, Int.sign B • a, (qn N B).2⟩ := by
      unfold scanStep; rw [if_pos hc]
    refine XV.mono (XV.ifS_t (K := 1 + (1 + (1 + (d * (2 + (1 + 2) + 3) + 3)))) hL hsL hsR
      (by rw [v2.1]; exact cR _ (bm _ _ bn bqB))
      (by rw [v2.2]; exact cR _ (bm _ _ bqN bd)) (by rw [v2.1, v2.2]; exact_mod_cast hc) ?_) (by omega) (fun _ h => h)
    have bZ' : |(0 : ℝ)| < 2 ^ ℓ := by simpa using bZ
    -- one assignment `x := v + 0` from `σ0`
    have asg : ∀ (σ0 : Env d) (x v : ℕ) (w : ℤ), x < L.NS → v < L.NS → σ0.sc v = w → σ0.sc sZ = 0 →
        |w| ≤ 2 ^ E → XRunsB L X ℓa ℓ (toX (VL.sop2 L .add x v sZ)) σ0 1 (· = σ0.setSc x (w : ℝ)) := by
      intro σ0 x v w hx hv ev ez bw
      refine XV.mono (XV.sop2 hL hx hv hsZ .add (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
        (by rw [ev]; exact cE _ bw) (by rw [ez]; exact bZ')
        (by rw [ev, ez]; simp only [RealRAM.Op2.eval, add_zero]; exact cE _ bw)) le_rfl fun σ' e => ?_
      rw [e, ev, ez]; simp [RealRAM.Op2.eval]
    refine XV.seq (asg σ2 sBn sQN _ hsBn hsQN eQN2 eZ2 bqN) fun σ3 e3 => ?_
    subst e3
    refine XV.seq (asg _ sBd sQB _ hsBd hsQB (by trimenv'; exact eQB2) (by trimenv'; exact eZ2) bqB) fun σ4 e4 => ?_
    subst e4
    refine XV.seq (asg _ sBb sQB _ hsBb hsQB (by trimenv'; exact eQB2) (by trimenv'; exact eZ2) bqB) fun σ5 e5 => ?_
    subst e5
    refine XV.mono (XV.scale hL (E := E) (a := a) (sg := Int.sign B) hK hR hKR hsS hsT (by trimne) hnl hnd hno hne
      (by simp only [Env.setSc_nat, n2]; exact hσd) (by simp only [Env.setSc_nat, n2]; exact hσ1) hda
      (by trimenv'; exact eS2) (fun l => by simp only [Env.setSc_arr, a2]; exact eR l) hsg1 ba
      (by omega)) le_rfl fun σ6 ⟨a6, dr6, F6⟩ => ?_
    rw [hst]
    refine ⟨?_, ?_, ?_, fun l => by rw [a6 l]; simp, ?_, ?_⟩
    · rw [F6.2.1 sBn (by trimne)]; trimenv'
    · rw [F6.2.1 sBd (by trimne)]; trimenv'
    · rw [F6.2.1 sBb (by trimne)]; trimenv'
    · rw [dr6]; simp only [Env.setSc_draws, d2]
    · exact F2.trans ((((FrameA.refl _ _ _ σ2).setSc (Or.inl rfl) _).setSc (Or.inr (Or.inl rfl)) _).setSc
        (Or.inr (Or.inr (Or.inl rfl))) _ |>.trans (F6.mono (fun _ h => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
        (fun _ h => h) (fun _ _ h => h)))
  · have hst : scanStep st N B a = st := by unfold scanStep; rw [if_neg hc]
    refine XV.mono (XV.ifS_f hL hsL hsR (by rw [v2.1]; exact cR _ (bm _ _ bn bqB))
      (by rw [v2.2]; exact cR _ (bm _ _ bqN bd)) (by rw [v2.1, v2.2]; exact_mod_cast hc) (XV.skip σ2))
      (by omega) fun σ' e => ?_
    subst e
    rw [hst]
    refine ⟨by rw [s2 _ (by trimne) (by trimne), eBn], by rw [s2 _ (by trimne) (by trimne), eBd],
      by rw [s2 _ (by trimne) (by trimne), eBb], fun l => ?_, d2, F2⟩
    rw [a2]; exact eK l

end AdversarialBco.Bit.Transfer
