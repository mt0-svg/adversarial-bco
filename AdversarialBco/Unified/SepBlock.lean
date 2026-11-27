/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.SepCM
public import AdversarialBco.Unified.SepGrid

@[expose] public section

/-!
# UNI-SEP on the oracle machine

The SEP block `xsep d L s EV` and its contract `sepBlockOK : SepBlockOK L XO ℓa ℓ s (xsep d L s)`: the integer
procedure `sepE` of SepSpec.lean (the searches of LINE along the coordinates, then the differences) run on the machine
with every value asked from the evaluator block `EV`.

The registers: `n0` the coordinate `i`, `n0 + 1` the constant `1`, `n0 + 2` the constant `d`, `n0 + 3`, `n0 + 4` the
pointers of the point writer, `n0 + 5` the counter of halvings, `n0 + 6` the bound `J + 1`, `n0 + 7` the flag of LINE.
The scalars: `u` the length, `u + 1` the spacing, `u + 2` the start, `u + 3, ..., u + 7` the five values of the window,
`u + 8` the offset of the point asked, `u + 9, ..., u + 14` the six new values of a halving, `u + 15` the constant `4`,
`u + 16` the constant `0`, `u + 17`, `u + 18` the tests, `u + 19`, `u + 20` the output `(s, δ)` of LINE, `u + 21` the
new spacing, `u + 22`, `u + 23` the two new starts, `u + 24` the scratch of the point writer, `u + 25, ..., u + 28` the
differences.
-/

namespace AdversarialBco.Uni

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer

variable {d : ℕ}

/-! ## The point writer -/

/-- Write the point `(2^E; Y + off e_i)` into `aev`, with `Y` from `ay`, `i` in `n0`, `off` in `u + 8`. -/
def xsPt (L : Layout) (s : SepLay) : XCmd :=
  .seq (.prim (.frag (.nconst (s.n0 + 4) 0)))
  (.seq (toX (VL.aset L s.aev (s.n0 + 4) s.cE))
  (.seq (.prim (.frag (.nconst (s.n0 + 3) 0)))
  (.seq (.prim (.frag (.nconst (s.n0 + 4) 1)))
  (.seq (.whileN (s.n0 + 3) (s.n0 + 2)
      (.seq (toX (VL.aget L (s.u + 24) s.ay (s.n0 + 3)))
      (.seq (toX (VL.aset L s.aev (s.n0 + 4) (s.u + 24)))
      (.seq (.prim (.frag (.nadd (s.n0 + 3) (s.n0 + 3) (s.n0 + 1))))
        (.prim (.frag (.nadd (s.n0 + 4) (s.n0 + 4) (s.n0 + 1))))))))
  (.seq (.prim (.frag (.nadd (s.n0 + 4) s.n0 (s.n0 + 1))))
  (.seq (toX (VL.aget L (s.u + 24) s.aev (s.n0 + 4)))
  (.seq (toX (VL.sop2 L .add (s.u + 24) (s.u + 24) (s.u + 8)))
    (toX (VL.aset L s.aev (s.n0 + 4) (s.u + 24))))))))))

theorem eZ_apply (i m : Fin d) (Y : Fin d → ℤ) (c : ℤ) :
    (Y + c • eZ i) m = if m = i then Y m + c else Y m := by
  simp only [eZ, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> ring

set_option maxHeartbeats 4000000 in
theorem sPt_runs {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {s : SepLay} (hs : SepLay.OK L s)
    (hd : 1 ≤ d) {σ : Env d} {Y : Fin d → ℤ} {off : ℤ} {E B : ℕ} (i : Fin d) (hi : σ.nat s.n0 = i)
    (h1 : σ.nat (s.n0 + 1) = 1) (hnd : σ.nat (s.n0 + 2) = d) (hcE : σ.sc s.cE = 2 ^ E)
    (hoff : σ.sc (s.u + 8) = off) (hY : ∀ m : Fin d, σ.arr s.ay m = Y m) (bY : ∀ m, |Y m| ≤ 2 ^ B)
    (boff : |off| ≤ 2 ^ B) (bE : E ≤ B) (hB : B + 1 < ℓ) :
    XRunsB L X ℓa ℓ (xsPt L s) σ (8 * d + 13) (fun σ' =>
      σ'.arr s.aev 0 = 2 ^ E ∧ (∀ m : Fin d, σ'.arr s.aev (1 + (m : ℕ)) = (Y + off • eZ i) m) ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => y = s.u + 24) (fun j => j = s.n0 + 3 ∨ j = s.n0 + 4) (fun b _ => b = s.aev) σ σ') := by
  obtain ⟨⟨h0a, hya, hga, hla, hea⟩, hne, ⟨hvo, hcEs, hL1, hSh, hcA, hcB, hus⟩, ⟨-, hvu, hEu, -, -, -, -⟩,
    ⟨hnJ, hnok, hn0⟩, -⟩ := hs
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil, and_true] at hne
  obtain ⟨⟨-, -, -, h0e⟩, ⟨-, -, hye⟩, -, -⟩ := hne
  have bb : ∀ z : ℤ, |z| ≤ 2 ^ (B + 1) → |z| < 2 ^ ℓ := fun z hz =>
    lt_of_le_of_lt hz (pow_lt_pow_right₀ (by norm_num) hB)
  have bb' : ∀ z : ℤ, |z| ≤ 2 ^ B → |z| < 2 ^ ℓ := fun z hz => bb z (absI_mono hz (by omega))
  have hasz := asz_lt hL hea
  have hlt : ∀ k ≤ d, k < asz d := fun k hk => by unfold asz; nlinarith
  have hka : ∀ k ≤ d, k < 2 ^ ℓa := fun k hk => lt_trans (hlt k hk) hasz
  have bcE : |(2 : ℤ) ^ E| ≤ 2 ^ B := by rw [abs_of_pos (by positivity)]; exact pow_le_pow_right₀ (by norm_num) bE
  refine XV.mono (K := 1 + (2 + (1 + (1 + (((d - 0) * (6 + 2) + 2) + (1 + (2 + (1 + 2)))))))) ?_ (by omega)
    (fun _ h => h)
  refine XV.seq (XV.nconst hL (i := s.n0 + 4) (by omega) 0 (hka 0 (by omega))) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.aset hL (a := s.aev) (i := s.n0 + 4) (x := s.cE) hea (by omega) hcEs
    (by simp; exact hlt 0 (by omega)) (by rw [Env.setNat_sc, hcE]; exact_mod_cast bb' _ bcE)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.nconst hL (i := s.n0 + 3) (by omega) 0 (hka 0 (by omega))) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.nconst hL (i := s.n0 + 4) (by omega) 1 (hka 1 (by omega))) fun σ4 e4 => ?_
  have f0 : σ4.arr s.aev 0 = 2 ^ E := by rw [e4]; simp [hcE]
  have f1 : σ4.nat (s.n0 + 3) = 0 := by rw [e4]; simp
  have f2 : σ4.nat (s.n0 + 4) = 1 := by rw [e4]; simp
  have f3 : σ4.nat (s.n0 + 1) = 1 := by rw [e4]; simp [h1]
  have f4 : σ4.nat (s.n0 + 2) = d := by rw [e4]; simp [hnd]
  have f5 : σ4.nat s.n0 = i := by rw [e4]; simp [hi]
  have f6 : σ4.sc (s.u + 8) = off := by rw [e4]; simp [hoff]
  have f7 : ∀ m : Fin d, σ4.arr s.ay m = Y m := fun m => by rw [e4]; simp [hye, hY m]
  have f8 : σ4.draws = σ.draws := by rw [e4]; simp
  have F4 : FrameA (fun y => y = s.u + 24) (fun j => j = s.n0 + 3 ∨ j = s.n0 + 4) (fun b _ => b = s.aev) σ σ4 := by
    rw [e4]
    exact (FrameA.refl (fun y => y = s.u + 24) (fun j => j = s.n0 + 3 ∨ j = s.n0 + 4) (fun b _ => b = s.aev)
      σ).setNat (Or.inr rfl) _ |>.setArr rfl _ |>.setNat (Or.inl rfl) _ |>.setNat (Or.inr rfl) _
  clear e4
  refine XV.seq (XV.whileN hL (i := s.n0 + 3) (j := s.n0 + 2) (by omega) (by omega)
    (fun t σ' => σ'.nat (s.n0 + 3) = t ∧ σ'.nat (s.n0 + 4) = 1 + t ∧ t ≤ d ∧ σ'.nat (s.n0 + 1) = 1 ∧
      σ'.nat (s.n0 + 2) = d ∧ σ'.nat s.n0 = i ∧
      (∀ m : Fin d, (m : ℕ) < t → σ'.arr s.aev (1 + (m : ℕ)) = Y m) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = s.u + 24) (fun j => j = s.n0 + 3 ∨ j = s.n0 + 4) (fun b k => b = s.aev ∧ 1 ≤ k) σ4 σ')
    d (2 + (2 + (1 + 1))) (fun t σ' hI => by rw [hI.1, hI.2.2.2.2.1]; exact ⟨hka t hI.2.2.1, hka d le_rfl⟩)
    (fun t σ' hI hc => by rw [hI.1, hI.2.2.2.2.1] at hc; exact hc) ?_ 0 σ4
    ⟨f1, by rw [f2], Nat.zero_le _, f3, f4, f5, fun m hm => absurd hm (Nat.not_lt_zero _), f8,
      FrameA.refl _ _ _ σ4⟩) fun σ5 h5 => ?_
  · intro t σ' ⟨hp, hq, htd, h1', hd', hi', hk', hd'', hF'⟩ hc
    rw [hp, hd'] at hc
    have eY : σ'.arr s.ay t = Y ⟨t, hc⟩ := by
      rw [hF'.2.2.1 _ _ (fun h => hye h.1)]; exact f7 ⟨t, hc⟩
    refine XV.seq (XV.aget hL (x := s.u + 24) (a := s.ay) (i := s.n0 + 3) (by omega) hya (by omega)
      (by rw [hp]; exact hlt t hc.le) (by rw [hp, eY]; exact XV.abs_int_lt (bb' _ (bY _)))) fun σ6 e6 => ?_
    subst e6
    refine XV.seq (XV.aset hL (a := s.aev) (i := s.n0 + 4) (x := s.u + 24) hea (by omega) (by omega)
      (by rw [Env.setSc_nat, hq]; exact hlt (1 + t) (by omega))
      (by rw [Env.setSc_sc, ite_eq_left rfl, hp, eY]; exact XV.abs_int_lt (bb' _ (bY _)))) fun σ7 e7 => ?_
    subst e7
    refine XV.seq (XV.nadd hL (i := s.n0 + 3) (a := s.n0 + 3) (b := s.n0 + 1) (by omega) (by omega) (by omega)
      (by simp only [Env.setArr_nat, Env.setSc_nat, hp]; exact hka t hc.le)
      (by simpa [h1'] using hka 1 hd)) fun σ8 e8 => ?_
    subst e8
    refine XV.mono (XV.nadd hL (i := s.n0 + 4) (a := s.n0 + 4) (b := s.n0 + 1) (by omega) (by omega) (by omega)
      (by simpa [hq] using hka (1 + t) (by omega)) (by simpa [h1'] using hka 1 hd)) le_rfl
      fun σ9 e9 => ?_
    subst e9
    refine ⟨by simp [hp, h1'], by simp [hq, h1']; omega, by omega, by simp [h1'], by simp [hd'], by simp [hi'], ?_,
      by simp [hd''], ?_⟩
    · intro m hm
      simp only [Env.setNat_arr, Env.setArr_arr, Env.setSc_nat, hq]
      by_cases hmt : (m : ℕ) = t
      · have hm' : m = ⟨t, hc⟩ := Fin.ext hmt
        subst hm'
        simp [hp, eY]
      · rw [ite_eq_right (by omega)]
        exact hk' m (by omega)
    · exact hF'.setSc rfl _ |>.setArr ⟨rfl, by simp [hq]⟩ _ |>.setNat (Or.inl rfl) _ |>.setNat (Or.inr rfl) _
  obtain ⟨t', ⟨hp, hq, htd, h1', hd', hi', hk', hd'', hF'⟩, hc⟩ := h5
  rw [hp, hd'] at hc
  have ht : t' = d := by omega
  have eYi : σ5.arr s.aev (1 + (i : ℕ)) = Y i := hk' i (by have := i.2; omega)
  have eoff : σ5.sc (s.u + 8) = off := by rw [hF'.2.1 _ (by omega), f6]
  refine XV.seq (XV.nadd hL (i := s.n0 + 4) (a := s.n0) (b := s.n0 + 1) (by omega) (by omega) (by omega)
    (by rw [hi']; exact hka i i.2.le) (by rw [h1']; exact hka 1 hd)) fun σ6 e6 => ?_
  have g6 : σ6.nat (s.n0 + 4) = 1 + i := by rw [e6]; simp [hi', h1']; omega
  have g6a : σ6.arr s.aev (1 + (i : ℕ)) = Y i := by rw [e6]; simp [eYi]
  have g6o : σ6.sc (s.u + 8) = off := by rw [e6]; simp [eoff]
  refine XV.seq (XV.aget hL (x := s.u + 24) (a := s.aev) (i := s.n0 + 4) (by omega) hea (by omega)
    (by rw [g6]; exact hlt (1 + i) (by omega)) (by rw [g6, g6a]; exact XV.abs_int_lt (bb' _ (bY _))))
    fun σ7 e7 => ?_
  rw [g6, g6a] at e7
  subst e7
  have bs := absI_add_le (bY i) boff
  refine XV.seq (XV.addI hL (x := s.u + 24) (a := s.u + 24) (b := s.u + 8) (u := Y i) (v := off) (by omega)
    (by omega) (by omega) (by simp) (by simp [g6o]) (bb' _ (bY _)) (bb' _ boff) (bb _ bs)) fun σ8 e8 => ?_
  subst e8
  refine XV.mono (XV.aset hL (a := s.aev) (i := s.n0 + 4) (x := s.u + 24) hea (by omega) (by omega)
    (by simp [g6]; exact hlt (1 + i) (by omega))
    (by rw [Env.setSc_sc, ite_eq_left rfl]; exact XV.abs_int_lt (bb _ bs))) le_rfl fun σ9 e9 => ?_
  subst e9
  have g60 : σ6.arr s.aev 0 = 2 ^ E := by
    rw [e6]; simp [hF'.2.2.1 s.aev 0 (fun h => by omega), f0]
  have g6k : ∀ m : Fin d, σ6.arr s.aev (1 + (m : ℕ)) = Y m := fun m => by
    rw [e6]; simp [hk' m (by have := m.2; omega)]
  refine ⟨by simp [g6, g60, show (0 : ℕ) ≠ 1 + (i : ℕ) by omega], ?_, by simp [e6, hd''], ?_⟩
  · intro m
    rw [eZ_apply]
    simp only [Env.setSc_arr, Env.setArr_arr, Env.setSc_nat, g6]
    by_cases hmi : m = i
    · subst hmi
      simp
    · have : ¬ (1 + (m : ℕ) = 1 + (i : ℕ)) := fun h => hmi (Fin.ext (by omega))
      simp only [this, and_false, ite_false, hmi]
      exact g6k m
  · rw [e6]
    exact F4.trans (hF'.mono (fun y hy => hy) (fun j hj => hj) (fun b k h => h.1)) |>.setNat (Or.inr rfl) _
      |>.setSc rfl _ |>.setSc rfl _ |>.setArr rfl _

/-! ## A value -/

/-- Ask the value at `Y + off e_i` and copy it into the scalar `x` (`u + 16` holds `0`). -/
def xsEval (L : Layout) (s : SepLay) (EV : XCmdO) (x : ℕ) : XCmdO :=
  .seq (.base (xsPt L s)) (.seq EV (.base (toX (VL.sop2 L .add x s.vout (s.u + 16)))))

/-- The frame of SEP and its evaluator. -/
def SepU (s : SepLay) (Sev Nev : ℕ → Prop) (Arev : ℕ → ℕ → Prop) : Env d → Env d → Prop :=
  FrameA (fun y => sepS s y ∨ Sev y) (fun j => sepN s j ∨ Nev j) (fun b k => sepAr s b k ∨ Arev b k)

set_option maxHeartbeats 4000000 in
theorem sEval_runs {L : Layout} {XO : XCtxO d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {s : SepLay} (hs : SepLay.OK L s)
    (hd : 1 ≤ d) {EV : XCmdO} {Dat : Env d → Prop} {evN : (Fin d → ℤ) → ℤ} {Kev bv : ℕ} {Sev Nev : ℕ → Prop}
    {Arev : ℕ → ℕ → Prop} {Y0 : Fin d → ℤ} {E e1 : ℕ}
    (hEV : EvalOK L XO ℓa ℓ EV Dat s.aev s.vout E (SepDom Y0 E e1) evN Kev Sev Nev Arev)
    (hbv : ∀ X, SepDom Y0 E e1 X → |evN X| < 2 ^ bv) (hDisj : SepDisj s Sev Nev Arev)
    (hStab : Stable Dat (fun y => sepS s y ∨ Sev y) (fun j => sepN s j ∨ Nev j) (fun b k => sepAr s b k ∨ Arev b k))
    {σ0 σ : Env d} (hD0 : Dat σ0) (hU : SepU s Sev Nev Arev σ0 σ) (hdr : σ.draws = σ0.draws)
    {Y : Fin d → ℤ} {off : ℤ} {B : ℕ} (i : Fin d) {x : ℕ} (hx1 : s.u ≤ x) (hx2 : x < s.u + 48)
    (hx24 : x ≠ s.u + 24) (hi : σ.nat s.n0 = i) (h1 : σ.nat (s.n0 + 1) = 1) (hnd : σ.nat (s.n0 + 2) = d)
    (hcE : σ.sc s.cE = 2 ^ E) (hoff : σ.sc (s.u + 8) = off) (hz : σ.sc (s.u + 16) = 0)
    (hY : ∀ m : Fin d, σ.arr s.ay m = Y m) (hdom : SepDom Y0 E e1 (Y + off • eZ i)) (bY : ∀ m, |Y m| ≤ 2 ^ B)
    (boff : |off| ≤ 2 ^ B) (bE : E ≤ B) (hbvB : bv ≤ B) (hB : B + 1 < ℓ) :
    XRunsBO L XO ℓa ℓ (xsEval L s EV x) σ (8 * d + 13 + (Kev + 1)) (fun σ' =>
      σ'.sc x = evN (Y + off • eZ i) ∧ σ'.draws = σ0.draws ∧ SepU s Sev Nev Arev σ0 σ' ∧
      FrameA (fun y => y = s.u + 24 ∨ y = x ∨ y = s.vout ∨ Sev y) (fun j => (j = s.n0 + 3 ∨ j = s.n0 + 4) ∨ Nev j)
        (fun b k => b = s.aev ∨ Arev b k) σ σ') := by
  have hs' := hs
  obtain ⟨⟨h0a, hya, hga, hla, hea⟩, -, ⟨hvo, hcEs, hL1, hSh, hcA, hcB, hus⟩, ⟨-, hvu, hEu, -, -, -, -⟩,
    ⟨hnJ, hnok, hn0⟩, -⟩ := hs'
  obtain ⟨dS, dN, dA⟩ := hDisj
  have bb : ∀ z : ℤ, |z| ≤ 2 ^ (B + 1) → |z| < 2 ^ ℓ := fun z hz =>
    lt_of_le_of_lt hz (pow_lt_pow_right₀ (by norm_num) hB)
  refine XVO.seq (XVO.ofX (sPt_runs hL hs hd i hi h1 hnd hcE hoff hY bY boff bE hB)) fun σ1 ⟨p0, pk, pdr, pF⟩ => ?_
  have F1u : SepU s Sev Nev Arev σ0 σ1 := hU.trans (pF.mono
    (fun y hy => Or.inl (Or.inr ⟨by omega, by omega⟩)) (fun j hj => Or.inl (Or.inr (by omega)))
    (fun b k h => Or.inl (Or.inr (Or.inr (Or.inr h)))))
  have hD1 : Dat σ1 := hStab σ0 σ1 hD0 F1u (by rw [pdr, hdr])
  refine XVO.seq (hEV σ1 (Y + off • eZ i) hD1 hdom p0 pk) fun σ2 ⟨v2, F2, d2⟩ => ?_
  have hz2 : σ2.sc (s.u + 16) = 0 := by
    rw [F2.2.1 _ (fun h => (dS _ h).2.2.2.2.2 ⟨by omega, by omega⟩), pF.2.1 _ (by omega), hz]
  have bv2 : |evN (Y + off • eZ i)| ≤ 2 ^ (B + 1) := absI_mono (hbv _ hdom).le (by omega)
  refine XVO.mono (XVO.ofX (XV.addI hL (x := x) (a := s.vout) (b := s.u + 16) (u := evN (Y + off • eZ i)) (v := 0)
    (by omega) hvo (by omega) v2 (by simp [hz2]) (bb _ bv2) (by simp) (by simpa using bb _ bv2))) le_rfl
    fun σ3 e3 => ?_
  subst e3
  refine ⟨by simp, by simp [d2, pdr, hdr], ?_, ?_⟩
  · exact (F1u.trans (F2.mono (fun y hy => Or.inr hy) (fun j hj => Or.inr hj) (fun b k h => Or.inr h))).setSc
      (Or.inl (Or.inr ⟨hx1, hx2⟩)) _
  · have F : FrameA (fun y => y = s.u + 24 ∨ y = x ∨ y = s.vout ∨ Sev y)
        (fun j => (j = s.n0 + 3 ∨ j = s.n0 + 4) ∨ Nev j) (fun b k => b = s.aev ∨ Arev b k) σ σ2 :=
      (pF.mono (fun y hy => Or.inl hy) (fun j hj => Or.inl hj) (fun b k h => Or.inl h)).trans
        (F2.mono (fun y hy => Or.inr (Or.inr (Or.inr hy))) (fun j hj => Or.inr hj) (fun b k h => Or.inr h))
    exact F.setSc (Or.inr (Or.inl rfl)) _

/-! ## LINE: the windows stay in `[0, len]` -/

/-- A window inside `[0, len]` with values below `2^bv`. -/
def WinOK (len : ℤ) (bv : ℕ) (W : WinZ) : Prop :=
  0 ≤ W.p0 ∧ 0 ≤ W.lam ∧ W.p0 + 4 * W.lam ≤ len ∧ |W.v0| < 2 ^ bv ∧ |W.v1| < 2 ^ bv ∧ |W.v2| < 2 ^ bv ∧
    |W.v3| < 2 ^ bv ∧ |W.v4| < 2 ^ bv

theorem winOK_first {f : ℤ → ℤ} {len : ℤ} {bv : ℕ} (hf : ∀ t, 0 ≤ t → t ≤ len → |f t| < 2 ^ bv) (hl : 0 ≤ len) :
    WinOK len bv (lineFirstZ f len) := by
  have h4 : 0 ≤ len / 4 := Int.ediv_nonneg hl (by norm_num)
  have h4' : 4 * (len / 4) ≤ len := Int.mul_ediv_self_le (by norm_num)
  refine ⟨le_rfl, h4, by simp only [lineFirstZ]; omega, hf _ le_rfl hl, hf _ h4 (by omega), hf _ (by omega) (by omega),
    hf _ (by omega) (by omega), hf _ (by omega) (by omega)⟩

theorem winOK_halve {f : ℤ → ℤ} {len : ℤ} {bv : ℕ} (hf : ∀ t, 0 ≤ t → t ≤ len → |f t| < 2 ^ bv) {W : WinZ}
    (hW : WinOK len bv W) : WinOK len bv (lineHalveZ f W) := by
  obtain ⟨h0, h1, h2, b0, b1, b2, b3, b4⟩ := hW
  have h4 : 0 ≤ W.lam / 4 := Int.ediv_nonneg h1 (by norm_num)
  have h4' : 4 * (W.lam / 4) ≤ W.lam := Int.mul_ediv_self_le (by norm_num)
  rw [lineHalveZ_eq]
  split_ifs
  · exact ⟨by simp only [halveBZ]; omega, h4, by simp only [halveBZ]; omega, b2, hf _ (by omega) (by omega),
      hf _ (by omega) (by omega), hf _ (by omega) (by omega), b3⟩
  · exact ⟨by simp only [halveAZ]; omega, h4, by simp only [halveAZ]; omega, b1, hf _ (by omega) (by omega),
      hf _ (by omega) (by omega), hf _ (by omega) (by omega), b2⟩

theorem lineLoopZ_bound {f : ℤ → ℤ} {len : ℤ} {bv : ℕ} (hf : ∀ t, 0 ≤ t → t ≤ len → |f t| < 2 ^ bv) (cA cB : ℤ) :
    ∀ (j : ℕ) (W : WinZ), WinOK len bv W → ∀ r, lineLoopZ f cA cB j W = some r →
      0 ≤ r.1 ∧ r.1 ≤ len ∧ 0 ≤ r.2 ∧ 4 * r.2 ≤ len := by
  intro j
  induction j with
  | zero =>
    intro W hW r h
    obtain ⟨h0, h1, h2, -⟩ := hW
    rw [lineLoopZ] at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨by simp only; omega, by simp only; omega, h1, by simp only; omega⟩
  | succ j ih =>
    intro W hW r h
    rw [lineLoopZ] at h
    split_ifs at h
    · obtain ⟨h0, h1, h2, -⟩ := hW
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨by simp only; omega, by simp only; omega, h1, by simp only; omega⟩
    · exact ih _ (winOK_halve hf hW) r h

theorem lineZ_bound {f : ℤ → ℤ} {len : ℤ} {bv : ℕ} (hf : ∀ t, 0 ≤ t → t ≤ len → |f t| < 2 ^ bv) (hl : 0 ≤ len)
    (cA cB : ℤ) (J : ℕ) (r : ℤ × ℤ) (h : lineZ f len cA cB J = some r) :
    0 ≤ r.1 ∧ r.1 ≤ len ∧ 0 ≤ r.2 ∧ 4 * r.2 ≤ len :=
  lineLoopZ_bound hf cA cB J _ (winOK_first hf hl) r h

/-! ## LINE: what it reads -/

/-- What LINE reads and never writes, at the coordinate `i` from the point `Y` with the length `len`. -/
structure LEnv (s : SepLay) (Sev Nev : ℕ → Prop) (Arev : ℕ → ℕ → Prop) (σ0 : Env d) (i : Fin d) (J E eτ eu : ℕ)
    (len : ℤ) (Y : Fin d → ℤ) (σ : Env d) : Prop where
  ni : σ.nat s.n0 = i
  n1 : σ.nat (s.n0 + 1) = 1
  nd : σ.nat (s.n0 + 2) = d
  nz : σ.nat (s.n0 + 8) = 0
  nJ : σ.nat s.nJ = J
  cE : σ.sc s.cE = 2 ^ E
  cA : σ.sc s.cA = 2 ^ (E + eτ + 1)
  cB : σ.sc s.cB = 2 ^ eu
  len : σ.sc s.u = len
  four : σ.sc (s.u + 15) = 4
  zero : σ.sc (s.u + 16) = 0
  ay : ∀ m : Fin d, σ.arr s.ay m = Y m
  U : SepU s Sev Nev Arev σ0 σ
  dr : σ.draws = σ0.draws

variable {L : Layout} {s : SepLay} {Sev Nev : ℕ → Prop} {Arev : ℕ → ℕ → Prop} {σ0 : Env d} {i : Fin d}
  {J E eτ eu : ℕ} {len : ℤ} {Y : Fin d → ℤ}

theorem LEnv.frame {σ σ' : Env d} (h : LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ)
    {S N : ℕ → Prop} {A : ℕ → ℕ → Prop} (F : FrameA S N A σ σ') (hU : SepU s Sev Nev Arev σ0 σ')
    (hdr : σ'.draws = σ0.draws)
    (hS : ∀ y, S y → y ≠ s.cE ∧ y ≠ s.cA ∧ y ≠ s.cB ∧ y ≠ s.u ∧ y ≠ s.u + 15 ∧ y ≠ s.u + 16)
    (hN : ∀ j, N j → j ≠ s.n0 ∧ j ≠ s.n0 + 1 ∧ j ≠ s.n0 + 2 ∧ j ≠ s.n0 + 8 ∧ j ≠ s.nJ)
    (hA : ∀ b k, A b k → b ≠ s.ay) : LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ' where
  ni := by rw [F.1 _ (fun h' => (hN _ h').1 rfl), h.ni]
  n1 := by rw [F.1 _ (fun h' => (hN _ h').2.1 rfl), h.n1]
  nd := by rw [F.1 _ (fun h' => (hN _ h').2.2.1 rfl), h.nd]
  nz := by rw [F.1 _ (fun h' => (hN _ h').2.2.2.1 rfl), h.nz]
  nJ := by rw [F.1 _ (fun h' => (hN _ h').2.2.2.2 rfl), h.nJ]
  cE := by rw [F.2.1 _ (fun h' => (hS _ h').1 rfl), h.cE]
  cA := by rw [F.2.1 _ (fun h' => (hS _ h').2.1 rfl), h.cA]
  cB := by rw [F.2.1 _ (fun h' => (hS _ h').2.2.1 rfl), h.cB]
  len := by rw [F.2.1 _ (fun h' => (hS _ h').2.2.2.1 rfl), h.len]
  four := by rw [F.2.1 _ (fun h' => (hS _ h').2.2.2.2.1 rfl), h.four]
  zero := by rw [F.2.1 _ (fun h' => (hS _ h').2.2.2.2.2 rfl), h.zero]
  ay := fun m => by rw [F.2.2.1 _ _ (fun h' => hA _ _ h' rfl), h.ay m]
  U := hU
  dr := hdr

theorem LEnv.setSc (hs : SepLay.OK L s) {σ : Env d} (h : LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ) {x : ℕ}
    (hx1 : s.u + 1 ≤ x) (hx2 : x < s.u + 48) (hx3 : x ≠ s.u + 15) (hx4 : x ≠ s.u + 16) (v : ℝ) :
    LEnv s Sev Nev Arev σ0 i J E eτ eu len Y (σ.setSc x v) := by
  obtain ⟨-, -, -, ⟨-, hvu, hEu, hLu, hSu, hAu, hBu⟩, -, -⟩ := hs
  exact h.frame ((FrameA.refl (fun y => y = x)
    (fun _ => False) (fun _ _ => False) σ).setSc rfl v) (h.U.setSc (Or.inl (Or.inr ⟨by omega, by omega⟩)) v)
    (by simp [h.dr]) (fun y hy => by subst hy; omega) (fun j hj => hj.elim) (fun b k h => h.elim)

theorem LEnv.setNat (hs : SepLay.OK L s) {σ : Env d} (h : LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ) {j : ℕ}
    (hj1 : s.n0 + 3 ≤ j) (hj2 : j < s.n0 + 8) (v : ℕ) :
    LEnv s Sev Nev Arev σ0 i J E eτ eu len Y (σ.setNat j v) := by
  obtain ⟨-, -, -, -, -, ⟨-, hJn, -⟩⟩ := hs
  exact h.frame ((FrameA.refl (fun _ => False)
    (fun j' => j' = j) (fun _ _ => False) σ).setNat rfl v) (h.U.setNat (Or.inl (Or.inr ⟨by omega, by omega⟩)) v)
    (by simp [h.dr]) (fun y hy => hy.elim) (fun j' hj' => by subst hj'; omega) (fun b k h => h.elim)

/-- What a value asked inside LINE keeps: every scalar of SEP but `u + 8`, `u + 24` and `x`, every natural of SEP but
`n0 + 3`, `n0 + 4`, the arrays `ay`, `ag`, `adl`. -/
def SKeep (s : SepLay) (x : ℕ) (σ σ' : Env d) : Prop :=
  (∀ y, s.u ≤ y → y < s.u + 48 → y ≠ s.u + 8 → y ≠ s.u + 24 → y ≠ x → σ'.sc y = σ.sc y) ∧
  (∀ j, ((s.n0 ≤ j ∧ j < s.n0 + 16 ∧ j ≠ s.n0 + 3 ∧ j ≠ s.n0 + 4) ∨ j = s.nok) → σ'.nat j = σ.nat j) ∧
  (∀ b k, (b = s.ay ∨ b = s.ag ∨ b = s.adl) → σ'.arr b k = σ.arr b k)

/-- The units of one value. -/
def sKE (d Kev : ℕ) : ℕ := 8 * d + 13 + (Kev + 1)

set_option maxHeartbeats 4000000 in
theorem sLEval_runs {XO : XCtxO d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hs : SepLay.OK L s) (hd : 1 ≤ d)
    {EV : XCmdO} {Dat : Env d → Prop} {evN : (Fin d → ℤ) → ℤ} {Kev bv : ℕ} {Y0 : Fin d → ℤ} {e1 : ℕ}
    (hEV : EvalOK L XO ℓa ℓ EV Dat s.aev s.vout E (SepDom Y0 E e1) evN Kev Sev Nev Arev)
    (hbv : ∀ X, SepDom Y0 E e1 X → |evN X| < 2 ^ bv) (hDisj : SepDisj s Sev Nev Arev)
    (hStab : Stable Dat (fun y => sepS s y ∨ Sev y) (fun j => sepN s j ∨ Nev j) (fun b k => sepAr s b k ∨ Arev b k))
    (hD0 : Dat σ0) {σ : Env d} (h : LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ) {off : ℤ} {B : ℕ}
    (hoff : σ.sc (s.u + 8) = off) (hdom : SepDom Y0 E e1 (Y + off • eZ i)) (bY : ∀ m, |Y m| ≤ 2 ^ B)
    (boff : |off| ≤ 2 ^ B) (bE : E ≤ B) (hbvB : bv ≤ B) (hB : B + 1 < ℓ) {x : ℕ} (hx1 : s.u + 1 ≤ x)
    (hx2 : x < s.u + 48) (hx8 : x ≠ s.u + 8) (hx15 : x ≠ s.u + 15) (hx16 : x ≠ s.u + 16) (hx24 : x ≠ s.u + 24) :
    XRunsBO L XO ℓa ℓ (xsEval L s EV x) σ (sKE d Kev) (fun σ' =>
      σ'.sc x = evN (Y + off • eZ i) ∧ σ'.sc (s.u + 8) = off ∧ LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ' ∧
        SKeep s x σ σ') := by
  have hs' := hs
  obtain ⟨⟨h0a, hya, hga, hla, hea⟩, hne, ⟨hvo, hcEs, hL1, hSh, hcA, hcB, hus⟩,
    ⟨hsne, hvu, hEu, hLu, hSu, hAu, hBu⟩, ⟨hnJ, hnok, hn0⟩, ⟨hJok, hJn, hokn⟩⟩ := hs'
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne hsne
  obtain ⟨⟨h0y, h0g, h0l, h0e⟩, ⟨hyg, hyl, hye⟩, ⟨hgl, hge⟩, hle⟩ := hne
  obtain ⟨⟨hvE, hvL, hvS, hvA, hvB⟩, -⟩ := hsne
  have hDisj' := hDisj
  obtain ⟨dS, dN, dA⟩ := hDisj'
  refine XVO.mono (sEval_runs hL hs hd hEV hbv hDisj hStab hD0 h.U h.dr i (by omega) hx2 hx24 h.ni h.n1 h.nd
    h.cE hoff h.zero h.ay hdom bY boff bE hbvB hB) (by unfold sKE; omega) fun σ' ⟨hv, hdr', hU', F⟩ => ?_
  have kS : ∀ y, s.u ≤ y → y < s.u + 48 → y ≠ s.u + 24 → y ≠ x → σ'.sc y = σ.sc y := fun y h1 h2 h3 h4 =>
    F.2.1 _ (fun h' => by
      rcases h' with h' | h' | h' | h'
      · exact h3 h'
      · exact h4 h'
      · omega
      · exact (dS _ h').2.2.2.2.2 ⟨h1, h2⟩)
  refine ⟨hv, by rw [kS _ (by omega) (by omega) (by omega) (Ne.symm hx8), hoff], ?_, ?_, ?_, ?_⟩
  · refine h.frame F hU' hdr' (fun y hy => ?_) (fun j hj => ?_) (fun b k hb => ?_)
    · rcases hy with rfl | rfl | rfl | hy
      · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
      · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
      · exact ⟨hvE, hvA, hvB, by omega, by omega, by omega⟩
      · obtain ⟨a1, -, -, a4, a5, a6⟩ := dS _ hy
        exact ⟨a1, a4, a5, fun e => a6 ⟨by omega, by omega⟩, fun e => a6 ⟨by omega, by omega⟩,
          fun e => a6 ⟨by omega, by omega⟩⟩
    · rcases hj with (rfl | rfl) | hj
      · exact ⟨by omega, by omega, by omega, by omega, by omega⟩
      · exact ⟨by omega, by omega, by omega, by omega, by omega⟩
      · obtain ⟨a1, -, a3⟩ := dN _ hj
        exact ⟨fun e => a3 ⟨by omega, by omega⟩, fun e => a3 ⟨by omega, by omega⟩,
          fun e => a3 ⟨by omega, by omega⟩, fun e => a3 ⟨by omega, by omega⟩, a1⟩
    · rcases hb with rfl | hb
      · exact Ne.symm hye
      · exact (dA _ _ hb).2.1
  · exact fun y h1 h2 _ h4 h5 => kS y h1 h2 h4 h5
  · intro j hj
    refine F.1 _ (fun h' => ?_)
    rcases h' with (rfl | rfl) | h'
    · omega
    · omega
    · obtain ⟨-, a2, a3⟩ := dN _ h'
      rcases hj with ⟨h1, h2, -, -⟩ | rfl
      · exact a3 ⟨h1, h2⟩
      · exact a2 rfl
  · intro b k hb
    refine F.2.2.1 _ _ (fun h' => ?_)
    rcases h' with rfl | h'
    · rcases hb with h | h | h
      · exact hye h.symm
      · exact hge h.symm
      · exact hle.1 h.symm
    · obtain ⟨-, a2, a3, a4, -⟩ := dA _ _ h'
      rcases hb with rfl | rfl | rfl
      · exact a2 rfl
      · exact a3 rfl
      · exact a4 rfl

/-- What a run of LINE keeps: every natural of SEP but `n0 + 3`, `n0 + 4`, the arrays `ay`, `ag`, `adl`. -/
def SKeepW (s : SepLay) (σ σ' : Env d) : Prop :=
  (∀ j, ((s.n0 ≤ j ∧ j < s.n0 + 16 ∧ j ≠ s.n0 + 3 ∧ j ≠ s.n0 + 4) ∨ j = s.nok) → σ'.nat j = σ.nat j) ∧
  (∀ b k, (b = s.ay ∨ b = s.ag ∨ b = s.adl) → σ'.arr b k = σ.arr b k)

theorem SKeep.w {x : ℕ} {σ σ' : Env d} (h : SKeep s x σ σ') : SKeepW s σ σ' := ⟨h.2.1, h.2.2⟩

theorem SKeepW.trans {σ σ' σ'' : Env d} (h : SKeepW s σ σ') (h' : SKeepW s σ' σ'') : SKeepW s σ σ'' :=
  ⟨fun j hj => (h'.1 j hj).trans (h.1 j hj), fun b k hb => (h'.2 b k hb).trans (h.2 b k hb)⟩

theorem SKeepW.refl (σ : Env d) : SKeepW s σ σ := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem SKeepW.setSc {σ σ' : Env d} (h : SKeepW s σ σ') (x : ℕ) (v : ℝ) : SKeepW s σ (σ'.setSc x v) :=
  ⟨fun j hj => by simp [h.1 j hj], fun b k hb => by simp [h.2 b k hb]⟩

/-- The window of LINE in the scalars `u + 1, ..., u + 7`. -/
def LWin (s : SepLay) (σ : Env d) (W : WinZ) : Prop :=
  σ.sc (s.u + 2) = W.p0 ∧ σ.sc (s.u + 1) = W.lam ∧ σ.sc (s.u + 3) = W.v0 ∧ σ.sc (s.u + 4) = W.v1 ∧
    σ.sc (s.u + 5) = W.v2 ∧ σ.sc (s.u + 6) = W.v3 ∧ σ.sc (s.u + 7) = W.v4

/-- `off := off + y`. -/
def xsOffAdd (L : Layout) (s : SepLay) (y : ℕ) : XCmd := toX (VL.sop2 L .add (s.u + 8) (s.u + 8) y)

/-- `off := off + y`, then the value at the offset into `x`. -/
def xsStep (L : Layout) (s : SepLay) (EV : XCmdO) (y x : ℕ) : XCmdO := .seq (.base (xsOffAdd L s y)) (xsEval L s EV x)

/-- The bundle of hypotheses of SEP on its evaluator, for the lemmas below. -/
structure SEvH (L : Layout) (XO : XCtxO d) (ℓa ℓ : ℕ) (s : SepLay) (EV : XCmdO) (Dat : Env d → Prop)
    (evN : (Fin d → ℤ) → ℤ) (Kev bv : ℕ) (Sev Nev : ℕ → Prop) (Arev : ℕ → ℕ → Prop) (Y0 : Fin d → ℤ) (E e1 : ℕ)
    (σ0 : Env d) : Prop where
  hL : LayOK L d ℓa
  hs : SepLay.OK L s
  hd : 1 ≤ d
  hEV : EvalOK L XO ℓa ℓ EV Dat s.aev s.vout E (SepDom Y0 E e1) evN Kev Sev Nev Arev
  hbv : ∀ X, SepDom Y0 E e1 X → |evN X| < 2 ^ bv
  hDisj : SepDisj s Sev Nev Arev
  hStab : Stable Dat (fun y => sepS s y ∨ Sev y) (fun j => sepN s j ∨ Nev j) (fun b k => sepAr s b k ∨ Arev b k)
  hD0 : Dat σ0

set_option maxHeartbeats 4000000 in
theorem sStep_runs {XO : XCtxO d} {ℓa ℓ : ℕ} {EV : XCmdO} {Dat : Env d → Prop} {evN : (Fin d → ℤ) → ℤ}
    {Kev bv : ℕ} {Y0 : Fin d → ℤ} {e1 : ℕ} (H : SEvH L XO ℓa ℓ s EV Dat evN Kev bv Sev Nev Arev Y0 E e1 σ0)
    {σ : Env d} (h : LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ) {o c : ℤ} {B : ℕ} {y : ℕ}
    (ho : σ.sc (s.u + 8) = o) (hy : σ.sc y = c) (hyL : y < L.NS)
    (hdom : SepDom Y0 E e1 (Y + (o + c) • eZ i)) (bY : ∀ m, |Y m| ≤ 2 ^ B) (bo : |o| ≤ 2 ^ B) (bc : |c| ≤ 2 ^ B)
    (boc : |o + c| ≤ 2 ^ B) (bE : E ≤ B) (hbvB : bv ≤ B) (hB : B + 1 < ℓ) {x : ℕ} (hx1 : s.u + 1 ≤ x)
    (hx2 : x < s.u + 48) (hx8 : x ≠ s.u + 8) (hx15 : x ≠ s.u + 15) (hx16 : x ≠ s.u + 16) (hx24 : x ≠ s.u + 24) :
    XRunsBO L XO ℓa ℓ (xsStep L s EV y x) σ (1 + sKE d Kev) (fun σ' =>
      σ'.sc x = evN (Y + (o + c) • eZ i) ∧ σ'.sc (s.u + 8) = ((o + c : ℤ) : ℝ) ∧
        LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ' ∧ SKeep s x σ σ') := by
  have hus := H.hs.scs.2.2.2.2.2.2
  have bb : ∀ z : ℤ, |z| ≤ 2 ^ B → |z| < 2 ^ ℓ := fun z hz =>
    lt_of_le_of_lt hz (pow_lt_pow_right₀ (by norm_num) (by omega))
  refine XVO.seq (XVO.ofX (XV.addI H.hL (x := s.u + 8) (a := s.u + 8) (b := y) (u := o) (v := c) (by omega)
    (by omega) hyL ho hy (bb _ bo) (bb _ bc) (bb _ boc))) fun σ1 e1 => ?_
  subst e1
  refine XVO.mono (sLEval_runs H.hL H.hs H.hd H.hEV H.hbv H.hDisj H.hStab H.hD0
    (h.setSc H.hs (x := s.u + 8) (by omega) (by omega) (by omega) (by omega) _) (by simp) hdom bY boc bE hbvB hB
    hx1 hx2 hx8 hx15 hx16 hx24) le_rfl fun σ' ⟨a1, a2, a3, k⟩ => ⟨a1, a2, a3, ?_, k.2.1, k.2.2⟩
  intro z h1 h2 h3 h4 h5
  rw [k.1 z h1 h2 h3 h4 h5]
  simp [h3]

/-! ## LINE: the first window -/

/-- `lam := len/4`, `p0 := 0`, `off := 0`, then the five values at `0, lam, ..., 4 lam`. -/
def xsFirst (L : Layout) (s : SepLay) (EV : XCmdO) : XCmdO :=
  .seq (.base (.seq (xsidiv L (s.u + 1) s.u (s.u + 15))
    (.seq (toX (VL.sop2 L .add (s.u + 2) (s.u + 16) (s.u + 16)))
      (toX (VL.sop2 L .add (s.u + 8) (s.u + 16) (s.u + 16))))))
  (.seq (xsEval L s EV (s.u + 3))
  (.seq (xsStep L s EV (s.u + 1) (s.u + 4))
  (.seq (xsStep L s EV (s.u + 1) (s.u + 5))
  (.seq (xsStep L s EV (s.u + 1) (s.u + 6))
    (xsStep L s EV (s.u + 1) (s.u + 7))))))

theorem bound_of_le {t len : ℤ} {E B : ℕ} (h0 : 0 ≤ t) (h1 : t ≤ len) (hl : len ≤ 2 ^ E) (bE : E ≤ B) :
    |t| ≤ 2 ^ B := by
  rw [abs_of_nonneg h0]
  exact (h1.trans hl).trans (pow_le_pow_right₀ (by norm_num) bE)

set_option maxHeartbeats 8000000 in
theorem sFirst_runs {XO : XCtxO d} {ℓa ℓ : ℕ} {EV : XCmdO} {Dat : Env d → Prop} {evN : (Fin d → ℤ) → ℤ}
    {Kev bv : ℕ} {Y0 : Fin d → ℤ} {e1 : ℕ} (H : SEvH L XO ℓa ℓ s EV Dat evN Kev bv Sev Nev Arev Y0 E e1 σ0)
    {σ : Env d} (h : LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ) {B : ℕ} (hl0 : 0 ≤ len) (hlE : len ≤ 2 ^ E)
    (hdomL : ∀ t, 0 ≤ t → t ≤ len → SepDom Y0 E e1 (Y + t • eZ i)) (bY : ∀ m, |Y m| ≤ 2 ^ B) (bE : E ≤ B)
    (hbvB : bv ≤ B) (hB : B + 1 < ℓ) (h2B : 2 ≤ B) :
    XRunsBO L XO ℓa ℓ (xsFirst L s EV) σ
      (3 + (sKE d Kev + ((1 + sKE d Kev) + ((1 + sKE d Kev) + ((1 + sKE d Kev) + (1 + sKE d Kev)))))) (fun σ' =>
      LWin s σ' (lineFirstZ (fun t => evN (Y + t • eZ i)) len) ∧ LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ' ∧
        SKeepW s σ σ') := by
  have hus := H.hs.scs.2.2.2.2.2.2
  have bb : ∀ z : ℤ, |z| ≤ 2 ^ B → |z| < 2 ^ ℓ := fun z hz =>
    lt_of_le_of_lt hz (pow_lt_pow_right₀ (by norm_num) (by omega))
  have hq : 0 ≤ len / 4 := Int.ediv_nonneg hl0 (by norm_num)
  have hq4 : 4 * (len / 4) ≤ len := Int.mul_ediv_self_le (by norm_num)
  have bt : ∀ t : ℤ, 0 ≤ t → t ≤ len → |t| ≤ 2 ^ B := fun t h0 h1 => bound_of_le h0 h1 hlE bE
  have b4 : |(4 : ℤ)| ≤ 2 ^ B := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, abs_of_pos (by norm_num)]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hbase : XRunsB L XO.X ℓa ℓ (.seq (xsidiv L (s.u + 1) s.u (s.u + 15))
      (.seq (toX (VL.sop2 L .add (s.u + 2) (s.u + 16) (s.u + 16)))
        (toX (VL.sop2 L .add (s.u + 8) (s.u + 16) (s.u + 16))))) σ (1 + (1 + 1)) (fun σ1 =>
      σ1.sc (s.u + 1) = ((len / 4 : ℤ) : ℝ) ∧ σ1.sc (s.u + 2) = ((0 : ℤ) : ℝ) ∧
        σ1.sc (s.u + 8) = ((0 : ℤ) : ℝ) ∧ LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ1 ∧ SKeepW s σ σ1) := by
    refine XV.seq (XV.divI H.hL (x := s.u + 1) (a := s.u) (b := s.u + 15) (u := len) (v := 4) (by omega) (by omega)
      (by omega) h.len (by rw [h.four]; norm_num) (bb _ (bt _ hl0 le_rfl)) (bb _ b4)) fun σa ea => ?_
    subst ea
    refine XV.seq (XV.addI H.hL (x := s.u + 2) (a := s.u + 16) (b := s.u + 16) (u := 0) (v := 0) (by omega)
      (by omega) (by omega) (by simp [h.zero]) (by simp [h.zero]) (by simp) (by simp) (by simp)) fun σb eb => ?_
    subst eb
    refine XV.mono (XV.addI H.hL (x := s.u + 8) (a := s.u + 16) (b := s.u + 16) (u := 0) (v := 0) (by omega)
      (by omega) (by omega) (by simp [h.zero]) (by simp [h.zero]) (by simp) (by simp) (by simp)) le_rfl
      fun σc ec => ?_
    subst ec
    refine ⟨by simp, by simp, by simp, ?_, ((SKeepW.refl σ).setSc _ _).setSc _ _ |>.setSc _ _⟩
    exact ((h.setSc H.hs (x := s.u + 1) (by omega) (by omega) (by omega) (by omega) _).setSc H.hs (x := s.u + 2)
      (by omega) (by omega) (by omega) (by omega) _).setSc H.hs (x := s.u + 8) (by omega) (by omega) (by omega)
      (by omega) _
  refine XVO.seq (XVO.ofX hbase) fun σ1 ⟨l1, p1, o1, E1, k1⟩ => ?_
  refine XVO.seq (sLEval_runs H.hL H.hs H.hd H.hEV H.hbv H.hDisj H.hStab H.hD0 E1 o1
    (hdomL 0 le_rfl hl0) bY (by simp) bE hbvB hB (x := s.u + 3) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)) fun σ2 ⟨v0, o2, E2, k2⟩ => ?_
  have l2 : σ2.sc (s.u + 1) = ((len / 4 : ℤ) : ℝ) := by
    rw [k2.1 _ (by omega) (by omega) (by omega) (by omega) (by omega), l1]
  have e1 : (0 : ℤ) + len / 4 = 1 * (len / 4) := by ring
  have e2 : (0 : ℤ) + len / 4 + len / 4 = 2 * (len / 4) := by ring
  have e3 : (0 : ℤ) + len / 4 + len / 4 + len / 4 = 3 * (len / 4) := by ring
  have e4 : (0 : ℤ) + len / 4 + len / 4 + len / 4 + len / 4 = 4 * (len / 4) := by ring
  refine XVO.seq (sStep_runs H E2 o2 l2 (by omega) (by rw [e1]; exact hdomL _ (by omega) (by omega)) bY
    (by simp) (bt _ hq (by omega)) (by rw [e1]; exact bt _ (by omega) (by omega)) bE hbvB hB (x := s.u + 4)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) fun σ3 ⟨v1, o3, E3, k3⟩ => ?_
  have l3 : σ3.sc (s.u + 1) = ((len / 4 : ℤ) : ℝ) := by
    rw [k3.1 _ (by omega) (by omega) (by omega) (by omega) (by omega), l2]
  refine XVO.seq (sStep_runs H E3 o3 l3 (by omega) (by rw [e2]; exact hdomL _ (by omega) (by omega)) bY
    (by rw [e1]; exact bt _ (by omega) (by omega)) (bt _ hq (by omega)) (by rw [e2]; exact bt _ (by omega) (by omega))
    bE hbvB hB (x := s.u + 5) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun σ4 ⟨v2, o4, E4, k4⟩ => ?_
  have l4 : σ4.sc (s.u + 1) = ((len / 4 : ℤ) : ℝ) := by
    rw [k4.1 _ (by omega) (by omega) (by omega) (by omega) (by omega), l3]
  refine XVO.seq (sStep_runs H E4 o4 l4 (by omega) (by rw [e3]; exact hdomL _ (by omega) (by omega)) bY
    (by rw [e2]; exact bt _ (by omega) (by omega)) (bt _ hq (by omega)) (by rw [e3]; exact bt _ (by omega) (by omega))
    bE hbvB hB (x := s.u + 6) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun σ5 ⟨v3, o5, E5, k5⟩ => ?_
  have l5 : σ5.sc (s.u + 1) = ((len / 4 : ℤ) : ℝ) := by
    rw [k5.1 _ (by omega) (by omega) (by omega) (by omega) (by omega), l4]
  refine XVO.mono (sStep_runs H E5 o5 l5 (by omega) (by rw [e4]; exact hdomL _ (by omega) hq4) bY
    (by rw [e3]; exact bt _ (by omega) (by omega)) (bt _ hq (by omega)) (by rw [e4]; exact bt _ (by omega) hq4)
    bE hbvB hB (x := s.u + 7) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) le_rfl
    fun σ6 ⟨v4, o6, E6, k6⟩ => ?_
  have kk : ∀ y, s.u + 1 ≤ y → y ≤ s.u + 2 → σ6.sc y = σ1.sc y := fun y h1 h2 => by
    rw [k6.1 y (by omega) (by omega) (by omega) (by omega) (by omega), k5.1 y (by omega) (by omega) (by omega)
      (by omega) (by omega), k4.1 y (by omega) (by omega) (by omega) (by omega) (by omega),
      k3.1 y (by omega) (by omega) (by omega) (by omega) (by omega), k2.1 y (by omega) (by omega) (by omega)
      (by omega) (by omega)]
  refine ⟨⟨by rw [kk _ (by omega) le_rfl, p1]; simp [lineFirstZ], by rw [kk _ le_rfl (by omega), l1]; simp [lineFirstZ],
    ?_, ?_, ?_, ?_, ?_⟩, E6, k1.trans (k2.w.trans (k3.w.trans (k4.w.trans (k5.w.trans k6.w))))⟩
  · rw [k6.1 _ (by omega) (by omega) (by omega) (by omega) (by omega), k5.1 _ (by omega) (by omega) (by omega)
      (by omega) (by omega), k4.1 _ (by omega) (by omega) (by omega) (by omega) (by omega),
      k3.1 _ (by omega) (by omega) (by omega) (by omega) (by omega), v0]
    simp [lineFirstZ]
  · rw [k6.1 _ (by omega) (by omega) (by omega) (by omega) (by omega), k5.1 _ (by omega) (by omega) (by omega)
      (by omega) (by omega), k4.1 _ (by omega) (by omega) (by omega) (by omega) (by omega), v1, e1, one_mul]
    simp [lineFirstZ]
  · rw [k6.1 _ (by omega) (by omega) (by omega) (by omega) (by omega), k5.1 _ (by omega) (by omega) (by omega)
      (by omega) (by omega), v2, e2]
    simp [lineFirstZ]
  · rw [k6.1 _ (by omega) (by omega) (by omega) (by omega) (by omega), v3, e3]
    simp [lineFirstZ]
  · rw [v4, e4]
    simp [lineFirstZ]

/-! ## LINE: the test and the choice of a window -/

/-- `t₁ := (v₃ + v₁ - (v₂ + v₂)) cA` into `u + 17`, `t₂ := lam cB` into `u + 18`. -/
def xsTest (L : Layout) (s : SepLay) : XCmd :=
  .seq (toX (VL.sop2 L .add (s.u + 17) (s.u + 6) (s.u + 4)))
  (.seq (toX (VL.sop2 L .add (s.u + 18) (s.u + 5) (s.u + 5)))
  (.seq (toX (VL.sop2 L .sub (s.u + 17) (s.u + 17) (s.u + 18)))
  (.seq (toX (VL.sop2 L .mul (s.u + 17) (s.u + 17) s.cA))
    (toX (VL.sop2 L .mul (s.u + 18) (s.u + 1) s.cB)))))

set_option maxHeartbeats 4000000 in
theorem sTest_runs {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hs : SepLay.OK L s) {σ : Env d}
    (h : LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ) {W : WinZ} {bv B : ℕ} (hW : LWin s σ W)
    (hWok : WinOK len bv W) (hlE : len ≤ 2 ^ E) (hB1 : bv + 2 + (E + eτ + 1) ≤ B) (hB2 : E + eu ≤ B)
    (hB : B < ℓ) :
    XRunsB L X ℓa ℓ (xsTest L s) σ (1 + (1 + (1 + (1 + 1)))) (fun σ' =>
      σ'.sc (s.u + 17) = ((W.sd * 2 ^ (E + eτ + 1) : ℤ) : ℝ) ∧ σ'.sc (s.u + 18) = ((W.lam * 2 ^ eu : ℤ) : ℝ) ∧
        LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ' ∧ LWin s σ' W ∧ SKeepW s σ σ' ∧
        ∀ y, y ≠ s.u + 17 → y ≠ s.u + 18 → σ'.sc y = σ.sc y) := by
  have hs' := hs
  obtain ⟨-, -, ⟨hvo, hcEs, hL1, hSh, hcA, hcB, hus⟩, ⟨-, hvu, hEu, hLu, hSu, hAu, hBu⟩, -, -⟩ := hs'
  obtain ⟨hp0, hl0, hle, b0, b1, b2, b3, b4⟩ := hWok
  obtain ⟨wp, wl, w0, w1, w2, w3, w4⟩ := hW
  have bb : ∀ z : ℤ, ∀ e, |z| ≤ 2 ^ e → e ≤ B → |z| < 2 ^ ℓ := fun z e hz he =>
    lt_of_le_of_lt (absI_mono hz he) (pow_lt_pow_right₀ (by norm_num) hB)
  have m1 := absI_add_le b3.le b1.le
  have m2 := absI_add_le b2.le b2.le
  have m3 := absI_sub_le m1 m2
  have hcA' : |(2 : ℤ) ^ (E + eτ + 1)| ≤ 2 ^ (E + eτ + 1) := bound_two_pow _
  have hcB' : |(2 : ℤ) ^ eu| ≤ 2 ^ eu := bound_two_pow _
  have m4 := absI_mul_le m3 hcA'
  have bl : |W.lam| ≤ 2 ^ E := by rw [abs_of_nonneg hl0]; omega
  have m5 := absI_mul_le bl hcB'
  have ru : ∀ k, s.cA ≠ s.u + k := fun k => by omega
  have rb : ∀ k, s.cB ≠ s.u + k := fun k => by omega
  refine XV.seq (XV.addI hL (x := s.u + 17) (a := s.u + 6) (b := s.u + 4) (u := W.v3) (v := W.v1) (by omega)
    (by omega) (by omega) w3 w1 (bb _ _ b3.le (by omega)) (bb _ _ b1.le (by omega)) (bb _ _ m1 (by omega)))
    fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.addI hL (x := s.u + 18) (a := s.u + 5) (b := s.u + 5) (u := W.v2) (v := W.v2) (by omega)
    (by omega) (by omega) (by simp [w2]) (by simp [w2]) (bb _ _ b2.le (by omega)) (bb _ _ b2.le (by omega))
    (bb _ _ m2 (by omega))) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.subI hL (x := s.u + 17) (a := s.u + 17) (b := s.u + 18) (u := W.v3 + W.v1) (v := W.v2 + W.v2)
    (by omega) (by omega) (by omega) (by simp) (by simp) (bb _ _ m1 (by omega)) (bb _ _ m2 (by omega))
    (bb _ _ m3 (by omega))) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.mulI hL (x := s.u + 17) (a := s.u + 17) (b := s.cA) (u := W.v3 + W.v1 - (W.v2 + W.v2))
    (v := 2 ^ (E + eτ + 1)) (by omega) (by omega) hcA (by simp) (by simp [ru, h.cA]) (bb _ _ m3 (by omega))
    (bb _ _ hcA' (by omega)) (bb _ _ m4 (by omega))) fun σ4 e4 => ?_
  subst e4
  refine XV.mono (XV.mulI hL (x := s.u + 18) (a := s.u + 1) (b := s.cB) (u := W.lam) (v := 2 ^ eu) (by omega)
    (by omega) hcB (by simp [wl]) (by simp [rb, h.cB]) (bb _ _ bl (by omega)) (bb _ _ hcB' (by omega))
    (bb _ _ m5 (by omega))) le_rfl fun σ5 e5 => ?_
  subst e5
  have hsd : W.v3 + W.v1 - (W.v2 + W.v2) = W.sd := by simp only [WinZ.sd]; ring
  refine ⟨by simp [hsd], by simp, ?_, ?_, ?_, fun y h1 h2 => by simp [h1, h2]⟩
  · exact (((((h.setSc hs (x := s.u + 17) (by omega) (by omega) (by omega) (by omega) _).setSc hs (x := s.u + 18)
      (by omega) (by omega) (by omega) (by omega) _).setSc hs (x := s.u + 17) (by omega) (by omega) (by omega)
      (by omega) _).setSc hs (x := s.u + 17) (by omega) (by omega) (by omega) (by omega) _).setSc hs
      (x := s.u + 18) (by omega) (by omega) (by omega) (by omega) _)
  · exact ⟨by simp [wp], by simp [wl], by simp [w0], by simp [w1], by simp [w2], by simp [w3], by simp [w4]⟩
  · exact (SKeepW.refl σ).setSc _ _ |>.setSc _ _ |>.setSc _ _ |>.setSc _ _ |>.setSc _ _

/-- `x := y + 0`. -/
def xsCopy (L : Layout) (s : SepLay) (x y : ℕ) : XCmd := toX (VL.sop2 L .add x y (s.u + 16))

/-- A new window from the scalars `q2, q1, q7, q3, ..., q6`, copied in that order into `u + 2, u + 1, u + 7, u + 3,
..., u + 6`. -/
def xsTake (L : Layout) (s : SepLay) (q2 q1 q7 q3 q4 q5 q6 : ℕ) : XCmd :=
  .seq (xsCopy L s (s.u + 2) q2) (.seq (xsCopy L s (s.u + 1) q1)
  (.seq (xsCopy L s (s.u + 7) q7) (.seq (xsCopy L s (s.u + 3) q3)
  (.seq (xsCopy L s (s.u + 4) q4) (.seq (xsCopy L s (s.u + 5) q5) (xsCopy L s (s.u + 6) q6))))))

/-- The window from `p₂`: `p0 := p₂`, `lam := l`, `v₄ := v₃`, `v₀ := v₂`, `v₁, v₂, v₃ := b₁, b₂, b₃`. -/
def xsTakeB (L : Layout) (s : SepLay) : XCmd :=
  xsTake L s (s.u + 23) (s.u + 21) (s.u + 6) (s.u + 5) (s.u + 12) (s.u + 13) (s.u + 14)

/-- The window from `p₁`: `p0 := p₁`, `lam := l`, `v₄ := v₂`, `v₀ := v₁`, `v₁, v₂, v₃ := a₁, a₂, a₃`. -/
def xsTakeA (L : Layout) (s : SepLay) : XCmd :=
  xsTake L s (s.u + 22) (s.u + 21) (s.u + 5) (s.u + 4) (s.u + 9) (s.u + 10) (s.u + 11)

/-- The spreads `spA` into `u + 17`, `spB` into `u + 18` (scratch `u + 25`), then the window of the smaller one (`A`
on a tie). -/
def xsSelect (L : Layout) (s : SepLay) : XCmd :=
  .seq (toX (VL.sop2 L .sub (s.u + 17) (s.u + 5) (s.u + 11)))
  (.seq (toX (VL.sop2 L .sub (s.u + 25) (s.u + 9) (s.u + 4)))
  (.seq (toX (VL.sop2 L .sub (s.u + 17) (s.u + 17) (s.u + 25)))
  (.seq (toX (VL.sop2 L .sub (s.u + 18) (s.u + 6) (s.u + 14)))
  (.seq (toX (VL.sop2 L .sub (s.u + 25) (s.u + 12) (s.u + 5)))
  (.seq (toX (VL.sop2 L .sub (s.u + 18) (s.u + 18) (s.u + 25)))
    (xifS L (s.u + 18) (s.u + 17) (xsTakeB L s) (xsTakeA L s)))))))

set_option maxHeartbeats 4000000 in
theorem sTake_runs {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hs : SepLay.OK L s) {σ : Env d}
    (h : LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ) {q2 q1 q7 q3 q4 q5 q6 : ℕ} (hq2 : q2 < s.u + 48)
    (hq1 : q1 < s.u + 48) (hq7 : q7 < s.u + 48) (hq3 : q3 < s.u + 48) (hq4 : q4 < s.u + 48) (hq5 : q5 < s.u + 48)
    (hq6 : q6 < s.u + 48) (n1 : q1 ≠ s.u + 2) (n7 : q7 ≠ s.u + 2 ∧ q7 ≠ s.u + 1)
    (n3 : q3 ≠ s.u + 2 ∧ q3 ≠ s.u + 1 ∧ q3 ≠ s.u + 7) (n4 : q4 ≠ s.u + 2 ∧ q4 ≠ s.u + 1 ∧ q4 ≠ s.u + 7 ∧ q4 ≠ s.u + 3)
    (n5 : q5 ≠ s.u + 2 ∧ q5 ≠ s.u + 1 ∧ q5 ≠ s.u + 7 ∧ q5 ≠ s.u + 3 ∧ q5 ≠ s.u + 4)
    (n6 : q6 ≠ s.u + 2 ∧ q6 ≠ s.u + 1 ∧ q6 ≠ s.u + 7 ∧ q6 ≠ s.u + 3 ∧ q6 ≠ s.u + 4 ∧ q6 ≠ s.u + 5)
    {w2 w1 w7 w3 w4 w5 w6 : ℤ} (h2 : σ.sc q2 = w2) (h1 : σ.sc q1 = w1) (h7 : σ.sc q7 = w7) (h3 : σ.sc q3 = w3)
    (h4 : σ.sc q4 = w4) (h5 : σ.sc q5 = w5) (h6 : σ.sc q6 = w6) {B : ℕ} (hB : B < ℓ) (b2 : |w2| ≤ 2 ^ B)
    (b1 : |w1| ≤ 2 ^ B) (b7 : |w7| ≤ 2 ^ B) (b3 : |w3| ≤ 2 ^ B) (b4 : |w4| ≤ 2 ^ B) (b5 : |w5| ≤ 2 ^ B)
    (b6 : |w6| ≤ 2 ^ B) :
    XRunsB L X ℓa ℓ (xsTake L s q2 q1 q7 q3 q4 q5 q6) σ (1 + (1 + (1 + (1 + (1 + (1 + 1)))))) (fun σ' =>
      LWin s σ' ⟨w2, w1, w3, w4, w5, w6, w7⟩ ∧ LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ' ∧ SKeepW s σ σ') := by
  have hus := hs.scs.2.2.2.2.2.2
  have bb : ∀ z : ℤ, |z| ≤ 2 ^ B → |z| < 2 ^ ℓ := fun z hz =>
    lt_of_le_of_lt hz (pow_lt_pow_right₀ (by norm_num) hB)
  have b0 : |(0 : ℤ)| < 2 ^ ℓ := by simp
  have z : ∀ k, k ≠ 16 → s.u + 16 ≠ s.u + k := fun k hk => by omega
  refine XV.seq (XV.addI hL (x := s.u + 2) (a := q2) (b := s.u + 16) (u := w2) (v := 0) (by omega) (by omega)
    (by omega) h2 (by simp [h.zero]) (bb _ b2) b0 (by simpa using bb _ b2)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.addI hL (x := s.u + 1) (a := q1) (b := s.u + 16) (u := w1) (v := 0) (by omega) (by omega)
    (by omega) (by simp [n1, h1]) (by simp [h.zero]) (bb _ b1) b0 (by simpa using bb _ b1)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.addI hL (x := s.u + 7) (a := q7) (b := s.u + 16) (u := w7) (v := 0) (by omega) (by omega)
    (by omega) (by simp [n7, h7]) (by simp [h.zero]) (bb _ b7) b0 (by simpa using bb _ b7)) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.addI hL (x := s.u + 3) (a := q3) (b := s.u + 16) (u := w3) (v := 0) (by omega) (by omega)
    (by omega) (by simp [n3, h3]) (by simp [h.zero]) (bb _ b3) b0 (by simpa using bb _ b3)) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.addI hL (x := s.u + 4) (a := q4) (b := s.u + 16) (u := w4) (v := 0) (by omega) (by omega)
    (by omega) (by simp [n4, h4]) (by simp [h.zero]) (bb _ b4) b0 (by simpa using bb _ b4)) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.addI hL (x := s.u + 5) (a := q5) (b := s.u + 16) (u := w5) (v := 0) (by omega) (by omega)
    (by omega) (by simp [n5, h5]) (by simp [h.zero]) (bb _ b5) b0 (by simpa using bb _ b5)) fun σ6 e6 => ?_
  subst e6
  refine XV.mono (XV.addI hL (x := s.u + 6) (a := q6) (b := s.u + 16) (u := w6) (v := 0) (by omega) (by omega)
    (by omega) (by simp [n6, h6]) (by simp [h.zero]) (bb _ b6) b0 (by simpa using bb _ b6)) le_rfl
    fun σ7 e7 => ?_
  subst e7
  refine ⟨⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩, ?_, ?_⟩
  · exact ((((((h.setSc hs (x := s.u + 2) (by omega) (by omega) (by omega) (by omega) _).setSc hs (x := s.u + 1)
      (by omega) (by omega) (by omega) (by omega) _).setSc hs (x := s.u + 7) (by omega) (by omega) (by omega)
      (by omega) _).setSc hs (x := s.u + 3) (by omega) (by omega) (by omega) (by omega) _).setSc hs
      (x := s.u + 4) (by omega) (by omega) (by omega) (by omega) _).setSc hs (x := s.u + 5) (by omega) (by omega)
      (by omega) (by omega) _).setSc hs (x := s.u + 6) (by omega) (by omega) (by omega) (by omega) _
  · exact (SKeepW.refl σ).setSc _ _ |>.setSc _ _ |>.setSc _ _ |>.setSc _ _ |>.setSc _ _ |>.setSc _ _ |>.setSc _ _

set_option maxHeartbeats 8000000 in
/-- The choice of a halving: with `A = (P₁, l, v₁, a₁, a₂, a₃, v₂)` and `B = (P₂, l, v₂, b₁, b₂, b₃, v₃)` in the
scalars, the window is `B` if `B.sp < A.sp`, else `A`. -/
theorem sSelect_runs {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hs : SepLay.OK L s) {σ : Env d}
    (h : LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ) {P1 P2 l v1 v2 v3 a1 a2 a3 b1 b2 b3 : ℤ}
    (hP1 : σ.sc (s.u + 22) = P1) (hP2 : σ.sc (s.u + 23) = P2) (hl : σ.sc (s.u + 21) = l) (hv1 : σ.sc (s.u + 4) = v1)
    (hv2 : σ.sc (s.u + 5) = v2) (hv3 : σ.sc (s.u + 6) = v3) (ha1 : σ.sc (s.u + 9) = a1)
    (ha2 : σ.sc (s.u + 10) = a2) (ha3 : σ.sc (s.u + 11) = a3) (hb1 : σ.sc (s.u + 12) = b1)
    (hb2 : σ.sc (s.u + 13) = b2) (hb3 : σ.sc (s.u + 14) = b3) {B : ℕ} (hB : B + 2 < ℓ) (bP1 : |P1| ≤ 2 ^ B)
    (bP2 : |P2| ≤ 2 ^ B) (bl : |l| ≤ 2 ^ B) (bv1 : |v1| ≤ 2 ^ B) (bv2 : |v2| ≤ 2 ^ B) (bv3 : |v3| ≤ 2 ^ B)
    (ba1 : |a1| ≤ 2 ^ B) (ba2 : |a2| ≤ 2 ^ B) (ba3 : |a3| ≤ 2 ^ B) (bb1 : |b1| ≤ 2 ^ B) (bb2 : |b2| ≤ 2 ^ B)
    (bb3 : |b3| ≤ 2 ^ B) :
    XRunsB L X ℓa ℓ (xsSelect L s) σ (1 + (1 + (1 + (1 + (1 + (1 + (7 + 2))))))) (fun σ' =>
      LWin s σ' (if (⟨P2, l, v2, b1, b2, b3, v3⟩ : WinZ).sp < (⟨P1, l, v1, a1, a2, a3, v2⟩ : WinZ).sp then
        ⟨P2, l, v2, b1, b2, b3, v3⟩ else ⟨P1, l, v1, a1, a2, a3, v2⟩) ∧
        LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ' ∧ SKeepW s σ σ') := by
  have hus := hs.scs.2.2.2.2.2.2
  have bb : ∀ z : ℤ, ∀ e, |z| ≤ 2 ^ e → e ≤ B + 2 → |z| < 2 ^ ℓ := fun z e hz he =>
    lt_of_le_of_lt (absI_mono hz he) (pow_lt_pow_right₀ (by norm_num) hB)
  have m1 := absI_sub_le bv2 ba3
  have m2 := absI_sub_le ba1 bv1
  have m3 := absI_sub_le m1 m2
  have m4 := absI_sub_le bv3 bb3
  have m5 := absI_sub_le bb1 bv2
  have m6 := absI_sub_le m4 m5
  refine XV.seq (XV.subI hL (x := s.u + 17) (a := s.u + 5) (b := s.u + 11) (u := v2) (v := a3) (by omega)
    (by omega) (by omega) hv2 ha3 (bb _ _ bv2 (by omega)) (bb _ _ ba3 (by omega)) (bb _ _ m1 (by omega)))
    fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.subI hL (x := s.u + 25) (a := s.u + 9) (b := s.u + 4) (u := a1) (v := v1) (by omega)
    (by omega) (by omega) (by simp [ha1]) (by simp [hv1]) (bb _ _ ba1 (by omega)) (bb _ _ bv1 (by omega))
    (bb _ _ m2 (by omega))) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.subI hL (x := s.u + 17) (a := s.u + 17) (b := s.u + 25) (u := v2 - a3) (v := a1 - v1) (by omega)
    (by omega) (by omega) (by simp) (by simp) (bb _ _ m1 (by omega)) (bb _ _ m2 (by omega))
    (bb _ _ m3 (by omega))) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.subI hL (x := s.u + 18) (a := s.u + 6) (b := s.u + 14) (u := v3) (v := b3) (by omega)
    (by omega) (by omega) (by simp [hv3]) (by simp [hb3]) (bb _ _ bv3 (by omega)) (bb _ _ bb3 (by omega))
    (bb _ _ m4 (by omega))) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.subI hL (x := s.u + 25) (a := s.u + 12) (b := s.u + 5) (u := b1) (v := v2) (by omega)
    (by omega) (by omega) (by simp [hb1]) (by simp [hv2]) (bb _ _ bb1 (by omega)) (bb _ _ bv2 (by omega))
    (bb _ _ m5 (by omega))) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.subI hL (x := s.u + 18) (a := s.u + 18) (b := s.u + 25) (u := v3 - b3) (v := b1 - v2) (by omega)
    (by omega) (by omega) (by simp) (by simp) (bb _ _ m4 (by omega)) (bb _ _ m5 (by omega))
    (bb _ _ m6 (by omega))) fun σ6 e6 => ?_
  subst e6
  have h6 := (((((h.setSc hs (x := s.u + 17) (by omega) (by omega) (by omega) (by omega) ((v2 - a3 : ℤ) : ℝ)).setSc hs
    (x := s.u + 25) (by omega) (by omega) (by omega) (by omega) ((a1 - v1 : ℤ) : ℝ)).setSc hs (x := s.u + 17)
    (by omega) (by omega) (by omega) (by omega) ((v2 - a3 - (a1 - v1) : ℤ) : ℝ)).setSc hs (x := s.u + 18) (by omega)
    (by omega) (by omega) (by omega) ((v3 - b3 : ℤ) : ℝ)).setSc hs (x := s.u + 25) (by omega) (by omega) (by omega)
    (by omega) ((b1 - v2 : ℤ) : ℝ)).setSc hs (x := s.u + 18) (by omega) (by omega) (by omega) (by omega)
    ((v3 - b3 - (b1 - v2) : ℤ) : ℝ)
  have k6 : SKeepW s σ _ := (SKeepW.refl σ).setSc (s.u + 17) ((v2 - a3 : ℤ) : ℝ) |>.setSc (s.u + 25) ((a1 - v1 : ℤ) : ℝ)
    |>.setSc (s.u + 17) ((v2 - a3 - (a1 - v1) : ℤ) : ℝ) |>.setSc (s.u + 18) ((v3 - b3 : ℤ) : ℝ)
    |>.setSc (s.u + 25) ((b1 - v2 : ℤ) : ℝ) |>.setSc (s.u + 18) ((v3 - b3 - (b1 - v2) : ℤ) : ℝ)
  by_cases hc : (⟨P2, l, v2, b1, b2, b3, v3⟩ : WinZ).sp < (⟨P1, l, v1, a1, a2, a3, v2⟩ : WinZ).sp
  · rw [ite_eq_left hc]
    refine XV.mono (XV.ifS_t hL (x := s.u + 18) (y := s.u + 17) (by omega) (by omega)
      (by simpa using XV.abs_int_lt (bb _ _ m6 le_rfl)) (by simpa using XV.abs_int_lt (bb _ _ m3 le_rfl))
      (by simp only [WinZ.sp] at hc; simp at hc ⊢; exact_mod_cast hc)
      (sTake_runs hL hs h6 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega, by omega⟩
        ⟨by omega, by omega, by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
        (by simp [hP2]) (by simp [hl]) (by simp [hv3]) (by simp [hv2]) (by simp [hb1]) (by simp [hb2])
        (by simp [hb3]) (by omega) bP2 bl bv3 bv2 bb1 bb2 bb3)) (by omega)
      fun σ' ⟨w, e, k⟩ => ⟨w, e, k6.trans k⟩
  · rw [ite_eq_right hc]
    refine XV.ifS_f hL (x := s.u + 18) (y := s.u + 17) (by omega) (by omega)
      (by simpa using XV.abs_int_lt (bb _ _ m6 le_rfl)) (by simpa using XV.abs_int_lt (bb _ _ m3 le_rfl))
      (by simp only [WinZ.sp] at hc; simp at hc ⊢; exact_mod_cast hc)
      (XV.mono (sTake_runs hL hs h6 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega, by omega⟩
        ⟨by omega, by omega, by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
        (by simp [hP1]) (by simp [hl]) (by simp [hv2]) (by simp [hv1]) (by simp [ha1]) (by simp [ha2])
        (by simp [ha3]) (by omega) bP1 bl bv2 bv1 ba1 ba2 ba3) le_rfl
      fun σ' ⟨w, e, k⟩ => ⟨w, e, k6.trans k⟩)

/-! ## LINE: one halving -/

/-- `l := lam/4`, `p₁ := p0 + lam`, `p₂ := p₁ + lam`, `off := p₁ + l`. -/
def xsHalvePre (L : Layout) (s : SepLay) : XCmd :=
  .seq (xsidiv L (s.u + 21) (s.u + 1) (s.u + 15))
  (.seq (toX (VL.sop2 L .add (s.u + 22) (s.u + 2) (s.u + 1)))
  (.seq (toX (VL.sop2 L .add (s.u + 23) (s.u + 22) (s.u + 1)))
    (toX (VL.sop2 L .add (s.u + 8) (s.u + 22) (s.u + 21)))))

/-- One halving of LINE: the values at `p₁ + l, p₁ + 2l, p₁ + 3l` into `u + 9, ..., u + 11`, at `p₂ + l, p₂ + 2l,
p₂ + 3l` into `u + 12, ..., u + 14`, then the choice. -/
def xsHalve (L : Layout) (s : SepLay) (EV : XCmdO) : XCmdO :=
  .seq (.base (xsHalvePre L s))
  (.seq (xsEval L s EV (s.u + 9))
  (.seq (xsStep L s EV (s.u + 21) (s.u + 10))
  (.seq (xsStep L s EV (s.u + 21) (s.u + 11))
  (.seq (.base (toX (VL.sop2 L .add (s.u + 8) (s.u + 23) (s.u + 21))))
  (.seq (xsEval L s EV (s.u + 12))
  (.seq (xsStep L s EV (s.u + 21) (s.u + 13))
  (.seq (xsStep L s EV (s.u + 21) (s.u + 14))
    (.base (xsSelect L s)))))))))

theorem SKeep.sc' {x : ℕ} {σ σ' : Env d} (k : SKeep s x σ σ') {y : ℕ} {v : ℝ} (hv : σ.sc y = v) (h1 : s.u ≤ y)
    (h2 : y < s.u + 48) (h3 : y ≠ s.u + 8) (h4 : y ≠ s.u + 24) (h5 : y ≠ x) : σ'.sc y = v := by
  rw [k.1 y h1 h2 h3 h4 h5, hv]

theorem SKeep.setSc8 (x : ℕ) (σ : Env d) (v : ℝ) : SKeep s x σ (σ.setSc (s.u + 8) v) :=
  ⟨fun y _ _ h3 _ _ => by simp [h3], fun j _ => by simp, fun b k _ => by simp⟩

theorem LWin.keep {x : ℕ} {σ σ' : Env d} {W : WinZ} (hW : LWin s σ W) (k : SKeep s x σ σ') (hx : s.u + 8 ≤ x) :
    LWin s σ' W :=
  ⟨k.sc' hW.1 (by omega) (by omega) (by omega) (by omega) (by omega),
    k.sc' hW.2.1 (by omega) (by omega) (by omega) (by omega) (by omega),
    k.sc' hW.2.2.1 (by omega) (by omega) (by omega) (by omega) (by omega),
    k.sc' hW.2.2.2.1 (by omega) (by omega) (by omega) (by omega) (by omega),
    k.sc' hW.2.2.2.2.1 (by omega) (by omega) (by omega) (by omega) (by omega),
    k.sc' hW.2.2.2.2.2.1 (by omega) (by omega) (by omega) (by omega) (by omega),
    k.sc' hW.2.2.2.2.2.2 (by omega) (by omega) (by omega) (by omega) (by omega)⟩

local macro "keep!" k:term:max e:term:max : term =>
  `(SKeep.sc' $k $e (by omega) (by omega) (by omega) (by omega) (by omega))

set_option maxHeartbeats 16000000 in
theorem sHalve_runs {XO : XCtxO d} {ℓa ℓ : ℕ} {EV : XCmdO} {Dat : Env d → Prop} {evN : (Fin d → ℤ) → ℤ}
    {Kev bv : ℕ} {Y0 : Fin d → ℤ} {e1 : ℕ} (H : SEvH L XO ℓa ℓ s EV Dat evN Kev bv Sev Nev Arev Y0 E e1 σ0)
    {σ : Env d} (h : LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ) {W : WinZ} (hW : LWin s σ W)
    (hWok : WinOK len bv W) {B : ℕ} (hlE : len ≤ 2 ^ E)
    (hdomL : ∀ t, 0 ≤ t → t ≤ len → SepDom Y0 E e1 (Y + t • eZ i)) (bY : ∀ m, |Y m| ≤ 2 ^ B) (bE : E ≤ B)
    (hbvB : bv ≤ B) (hB : B + 2 < ℓ) (h2B : 2 ≤ B) :
    XRunsBO L XO ℓa ℓ (xsHalve L s EV) σ (6 * sKE d Kev + 24) (fun σ' =>
      LWin s σ' (lineHalveZ (fun t => evN (Y + t • eZ i)) W) ∧ LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ' ∧
        SKeepW s σ σ') := by
  have hus := H.hs.scs.2.2.2.2.2.2
  have bb : ∀ z : ℤ, |z| ≤ 2 ^ B → |z| < 2 ^ ℓ := fun z hz =>
    lt_of_le_of_lt hz (pow_lt_pow_right₀ (by norm_num) (by omega))
  obtain ⟨hp0, hl0, hle, c0, c1, c2, c3, c4⟩ := hWok
  obtain ⟨wp, wl, w0, w1, w2, w3, w4⟩ := id hW
  have hq : 0 ≤ W.lam / 4 := Int.ediv_nonneg hl0 (by norm_num)
  have hq4 : 4 * (W.lam / 4) ≤ W.lam := Int.mul_ediv_self_le (by norm_num)
  have bt : ∀ t : ℤ, 0 ≤ t → t ≤ len → |t| ≤ 2 ^ B := fun t h0 h1 => bound_of_le h0 h1 hlE bE
  have b4 : |(4 : ℤ)| ≤ 2 ^ B := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, abs_of_pos (by norm_num)]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have bvB : ∀ z : ℤ, |z| < 2 ^ bv → |z| ≤ 2 ^ B := fun z hz => absI_mono hz.le hbvB
  have bev : ∀ t, 0 ≤ t → t ≤ len → |evN (Y + t • eZ i)| ≤ 2 ^ B := fun t h0 h1 =>
    bvB _ (H.hbv _ (hdomL t h0 h1))
  refine XVO.mono (K := (1 + (1 + (1 + 1))) + (sKE d Kev + ((1 + sKE d Kev) + ((1 + sKE d Kev) + (1 +
    (sKE d Kev + ((1 + sKE d Kev) + ((1 + sKE d Kev) + (1 + (1 + (1 + (1 + (1 + (1 + (7 + 2)))))))))))))))
    ?_ (by omega) (fun _ h => h)
  have hbase : XRunsB L XO.X ℓa ℓ (xsHalvePre L s) σ (1 + (1 + (1 + 1))) (fun σ1 =>
      σ1.sc (s.u + 21) = ((W.lam / 4 : ℤ) : ℝ) ∧ σ1.sc (s.u + 22) = ((W.p0 + W.lam : ℤ) : ℝ) ∧
        σ1.sc (s.u + 23) = ((W.p0 + W.lam + W.lam : ℤ) : ℝ) ∧
        σ1.sc (s.u + 8) = ((W.p0 + W.lam + W.lam / 4 : ℤ) : ℝ) ∧ LWin s σ1 W ∧
        LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ1 ∧ SKeepW s σ σ1) := by
    refine XV.seq (XV.divI H.hL (x := s.u + 21) (a := s.u + 1) (b := s.u + 15) (u := W.lam) (v := 4) (by omega)
      (by omega) (by omega) wl (by rw [h.four]; norm_num) (bb _ (bt _ hl0 (by omega))) (bb _ b4)) fun σa ea => ?_
    subst ea
    refine XV.seq (XV.addI H.hL (x := s.u + 22) (a := s.u + 2) (b := s.u + 1) (u := W.p0) (v := W.lam) (by omega)
      (by omega) (by omega) (by simp [wp]) (by simp [wl]) (bb _ (bt _ hp0 (by omega))) (bb _ (bt _ hl0 (by omega)))
      (bb _ (bt _ (by omega) (by omega)))) fun σb eb => ?_
    subst eb
    refine XV.seq (XV.addI H.hL (x := s.u + 23) (a := s.u + 22) (b := s.u + 1) (u := W.p0 + W.lam) (v := W.lam)
      (by omega) (by omega) (by omega) (by simp) (by simp [wl]) (bb _ (bt _ (by omega) (by omega)))
      (bb _ (bt _ hl0 (by omega))) (bb _ (bt _ (by omega) (by omega)))) fun σc ec => ?_
    subst ec
    refine XV.mono (XV.addI H.hL (x := s.u + 8) (a := s.u + 22) (b := s.u + 21) (u := W.p0 + W.lam)
      (v := W.lam / 4) (by omega) (by omega) (by omega) (by simp) (by simp) (bb _ (bt _ (by omega) (by omega)))
      (bb _ (bt _ hq (by omega))) (bb _ (bt _ (by omega) (by omega)))) le_rfl fun σd ed => ?_
    subst ed
    refine ⟨by simp, by simp, by simp, by simp,
      ⟨by simp [wp], by simp [wl], by simp [w0], by simp [w1], by simp [w2], by simp [w3], by simp [w4]⟩, ?_,
      (SKeepW.refl σ).setSc _ _ |>.setSc _ _ |>.setSc _ _ |>.setSc _ _⟩
    exact (((h.setSc H.hs (x := s.u + 21) (by omega) (by omega) (by omega) (by omega) _).setSc H.hs
      (x := s.u + 22) (by omega) (by omega) (by omega) (by omega) _).setSc H.hs (x := s.u + 23) (by omega)
      (by omega) (by omega) (by omega) _).setSc H.hs (x := s.u + 8) (by omega) (by omega) (by omega) (by omega) _
  have e23 : W.p0 + W.lam + W.lam = W.p0 + 2 * W.lam := by ring
  refine XVO.seq (XVO.ofX hbase) fun σ1 ⟨l1, p1, p2, o1, W1, E1, k1⟩ => ?_
  rw [e23] at p2
  -- the window from `p₁`
  refine XVO.seq (sLEval_runs H.hL H.hs H.hd H.hEV H.hbv H.hDisj H.hStab H.hD0 E1 o1
    (hdomL _ (by omega) (by omega)) bY (bt _ (by omega) (by omega)) bE hbvB (by omega) (x := s.u + 9) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)) fun σ2 ⟨a1, o2, E2, k2⟩ => ?_
  have l2 := keep! k2 l1
  refine XVO.seq (sStep_runs H E2 o2 l2 (by omega) (hdomL _ (by omega) (by omega)) bY
    (bt _ (by omega) (by omega)) (bt _ hq (by omega)) (bt _ (by omega) (by omega)) bE hbvB (by omega)
    (x := s.u + 10) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) fun σ3 ⟨a2, o3, E3, k3⟩ => ?_
  have r2 : W.p0 + W.lam + W.lam / 4 + W.lam / 4 = W.p0 + W.lam + 2 * (W.lam / 4) := by ring
  rw [r2] at a2 o3
  have l3 := keep! k3 l2
  refine XVO.seq (sStep_runs H E3 o3 l3 (by omega) (hdomL _ (by omega) (by omega)) bY
    (bt _ (by omega) (by omega)) (bt _ hq (by omega)) (bt _ (by omega) (by omega)) bE hbvB (by omega)
    (x := s.u + 11) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) fun σ4 ⟨a3, o4, E4, k4⟩ => ?_
  have r3 : W.p0 + W.lam + 2 * (W.lam / 4) + W.lam / 4 = W.p0 + W.lam + 3 * (W.lam / 4) := by ring
  rw [r3] at a3
  have l4 := keep! k4 l3
  have p24 := keep! k4 (keep! k3 (keep! k2 p2))
  -- the window from `p₂`
  refine XVO.seq (XVO.ofX (XV.addI H.hL (x := s.u + 8) (a := s.u + 23) (b := s.u + 21) (u := W.p0 + 2 * W.lam)
    (v := W.lam / 4) (by omega) (by omega) (by omega) p24 l4 (bb _ (bt _ (by omega) (by omega)))
    (bb _ (bt _ hq (by omega))) (bb _ (bt _ (by omega) (by omega))))) fun σ5 e5 => ?_
  have k5 : SKeep s (s.u + 8) σ4 σ5 := by rw [e5]; exact SKeep.setSc8 _ _ _
  have o5 : σ5.sc (s.u + 8) = ((W.p0 + 2 * W.lam + W.lam / 4 : ℤ) : ℝ) := by rw [e5]; simp
  have E5 : LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ5 := by
    rw [e5]; exact E4.setSc H.hs (x := s.u + 8) (by omega) (by omega) (by omega) (by omega) _
  clear e5
  refine XVO.seq (sLEval_runs H.hL H.hs H.hd H.hEV H.hbv H.hDisj H.hStab H.hD0 E5 o5
    (hdomL _ (by omega) (by omega)) bY (bt _ (by omega) (by omega)) bE hbvB (by omega) (x := s.u + 12) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)) fun σ6 ⟨b1, o6, E6, k6⟩ => ?_
  have l6 := keep! k6 (keep! k5 l4)
  refine XVO.seq (sStep_runs H E6 o6 l6 (by omega) (hdomL _ (by omega) (by omega)) bY
    (bt _ (by omega) (by omega)) (bt _ hq (by omega)) (bt _ (by omega) (by omega)) bE hbvB (by omega)
    (x := s.u + 13) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) fun σ7 ⟨b2, o7, E7, k7⟩ => ?_
  have r5 : W.p0 + 2 * W.lam + W.lam / 4 + W.lam / 4 = W.p0 + 2 * W.lam + 2 * (W.lam / 4) := by ring
  rw [r5] at b2 o7
  have l7 := keep! k7 l6
  refine XVO.mono (XVO.seq (sStep_runs H E7 o7 l7 (by omega) (hdomL _ (by omega) (by omega)) bY
    (bt _ (by omega) (by omega)) (bt _ hq (by omega)) (bt _ (by omega) (by omega)) bE hbvB (by omega)
    (x := s.u + 14) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) fun σ8 ⟨b3, o8, E8, k8⟩ => ?_)
    le_rfl (fun _ h => h)
  have r6 : W.p0 + 2 * W.lam + 2 * (W.lam / 4) + W.lam / 4 = W.p0 + 2 * W.lam + 3 * (W.lam / 4) := by ring
  rw [r6] at b3
  have W8 := (((((((W1.keep k2 (by omega)).keep k3 (by omega)).keep k4 (by omega)).keep k5 (by omega)).keep k6
    (by omega)).keep k7 (by omega)).keep k8 (by omega))
  have l8 := keep! k8 l7
  have p18 := keep! k8 (keep! k7 (keep! k6 (keep! k5 (keep! k4 (keep! k3 (keep! k2 p1))))))
  have p28 := keep! k8 (keep! k7 (keep! k6 (keep! k5 p24)))
  have a18 := keep! k8 (keep! k7 (keep! k6 (keep! k5 (keep! k4 (keep! k3 a1)))))
  have a28 := keep! k8 (keep! k7 (keep! k6 (keep! k5 (keep! k4 a2))))
  have a38 := keep! k8 (keep! k7 (keep! k6 (keep! k5 a3)))
  have b18 := keep! k8 (keep! k7 b1)
  have b28 := keep! k8 b2
  refine XVO.ofX (XV.mono (sSelect_runs H.hL H.hs E8 p18 p28 l8 W8.2.2.2.1 W8.2.2.2.2.1 W8.2.2.2.2.2.1 a18 a28 a38
    b18 b28 b3 hB (bt _ (by omega) (by omega)) (bt _ (by omega) (by omega)) (bt _ hq (by omega)) (bvB _ c1)
    (bvB _ c2) (bvB _ c3) (bev _ (by omega) (by omega)) (bev _ (by omega) (by omega)) (bev _ (by omega) (by omega))
    (bev _ (by omega) (by omega)) (bev _ (by omega) (by omega)) (bev _ (by omega) (by omega))) le_rfl
    fun σ' ⟨w, e, k⟩ => ⟨by rw [lineHalveZ_eq]; exact w, e, ?_⟩)
  exact k1.trans k2.w |>.trans k3.w |>.trans k4.w |>.trans k5.w |>.trans k6.w |>.trans k7.w |>.trans k8.w |>.trans k

/-! ## LINE: the loop -/

/-- Stop: `sres := p0 + lam + lam`, `δres := lam`, the flag `1`, the counter `J + 1`. -/
def xsStop (L : Layout) (s : SepLay) : XCmd :=
  .seq (toX (VL.sop2 L .add (s.u + 19) (s.u + 2) (s.u + 1)))
  (.seq (toX (VL.sop2 L .add (s.u + 19) (s.u + 19) (s.u + 1)))
  (.seq (toX (VL.sop2 L .add (s.u + 20) (s.u + 1) (s.u + 16)))
  (.seq (.prim (.frag (.nconst (s.n0 + 7) 1)))
    (.prim (.frag (.nadd (s.n0 + 5) (s.n0 + 6) (s.n0 + 8)))))))

/-- Fail: the flag `0`, the counter `J + 1`. -/
def xsFail (L : Layout) (s : SepLay) : XCmd :=
  .seq (.prim (.frag (.nconst (s.n0 + 7) 0))) (.prim (.frag (.nadd (s.n0 + 5) (s.n0 + 6) (s.n0 + 8))))

/-- One turn of LINE: the test; on `lam cB < sd cA` a halving (counter below `J`) or the failure, else the stop. -/
def xsBody (L : Layout) (s : SepLay) (EV : XCmdO) : XCmdO :=
  .seq (.base (xsTest L s))
    (xifSO L (s.u + 18) (s.u + 17)
      (.ifN (s.n0 + 5) s.nJ (.seq (xsHalve L s EV) (.base (.prim (.frag (.nadd (s.n0 + 5) (s.n0 + 5) (s.n0 + 1))))))
        (.base (xsFail L s)))
      (.base (xsStop L s)))

/-- LINE: the counter `0`, the bound `J + 1`, the first window, then the turns while the counter is below `J + 1`. -/
def xsLine (L : Layout) (s : SepLay) (EV : XCmdO) : XCmdO :=
  .seq (.base (.seq (.prim (.frag (.nconst (s.n0 + 5) 0))) (.prim (.frag (.nadd (s.n0 + 6) s.nJ (s.n0 + 1))))))
  (.seq (xsFirst L s EV) (.whileN (s.n0 + 5) (s.n0 + 6) (xsBody L s EV)))

/-- The output of LINE: on success the flag `1` and `(s, δ)` in `u + 19`, `u + 20`, on failure the flag `0`. -/
def LOut (s : SepLay) (R : Option (ℤ × ℤ)) (σ : Env d) : Prop :=
  (R = none → σ.nat (s.n0 + 7) = 0) ∧
    ∀ r, R = some r → σ.nat (s.n0 + 7) = 1 ∧ σ.sc (s.u + 19) = r.1 ∧ σ.sc (s.u + 20) = r.2

/-- What LINE keeps outside its own cells: the flag `nok`, the arrays `ay`, `ag`, `adl`. -/
def SKeepA (s : SepLay) (σ σ' : Env d) : Prop :=
  σ'.nat s.nok = σ.nat s.nok ∧ ∀ b k, (b = s.ay ∨ b = s.ag ∨ b = s.adl) → σ'.arr b k = σ.arr b k

theorem SKeepW.a {σ σ' : Env d} (h : SKeepW s σ σ') : SKeepA s σ σ' := ⟨h.1 _ (Or.inr rfl), h.2⟩

theorem SKeepA.trans {σ σ' σ'' : Env d} (h : SKeepA s σ σ') (h' : SKeepA s σ' σ'') : SKeepA s σ σ'' :=
  ⟨h'.1.trans h.1, fun b k hb => (h'.2 b k hb).trans (h.2 b k hb)⟩

theorem SKeepA.refl (σ : Env d) : SKeepA s σ σ := ⟨rfl, fun _ _ _ => rfl⟩

theorem SKeepA.setSc {σ σ' : Env d} (h : SKeepA s σ σ') (x : ℕ) (v : ℝ) : SKeepA s σ (σ'.setSc x v) :=
  ⟨by simp [h.1], fun b k hb => by simp [h.2 b k hb]⟩

theorem SKeepA.setNat {σ σ' : Env d} (h : SKeepA s σ σ') {j : ℕ} (hj : j ≠ s.nok) (v : ℕ) :
    SKeepA s σ (σ'.setNat j v) :=
  ⟨by simp [Ne.symm hj, h.1], fun b k hb => by simp [h.2 b k hb]⟩

theorem LWin.setNat {σ : Env d} {W : WinZ} (hW : LWin s σ W) (j v : ℕ) : LWin s (σ.setNat j v) W := by
  obtain ⟨a, b, c, e, f, g, k⟩ := hW
  exact ⟨by simp [a], by simp [b], by simp [c], by simp [e], by simp [f], by simp [g], by simp [k]⟩

theorem lineLoopZ_stop {f : ℤ → ℤ} {cA cB : ℤ} {j : ℕ} {W : WinZ} (h : W.sd * cA ≤ W.lam * cB) :
    lineLoopZ f cA cB j W = some (W.p0 + 2 * W.lam, W.lam) := by
  cases j <;> rw [lineLoopZ, ite_eq_left h]

theorem lineLoopZ_zero {f : ℤ → ℤ} {cA cB : ℤ} {W : WinZ} (h : ¬ W.sd * cA ≤ W.lam * cB) :
    lineLoopZ f cA cB 0 W = none := by
  rw [lineLoopZ, ite_eq_right h]

theorem lineLoopZ_succ {f : ℤ → ℤ} {cA cB : ℤ} {j : ℕ} {W : WinZ} (h : ¬ W.sd * cA ≤ W.lam * cB) :
    lineLoopZ f cA cB (j + 1) W = lineLoopZ f cA cB j (lineHalveZ f W) := by
  rw [lineLoopZ, ite_eq_right h]

/-- The units of one turn of LINE. -/
def sLB (d Kev : ℕ) : ℕ := (1 + (1 + (1 + (1 + 1)))) + ((6 * sKE d Kev + 24 + 1) + 2 + 2)

/-- The units of LINE. -/
def sLK (d J Kev : ℕ) : ℕ :=
  (1 + 1) + ((3 + (sKE d Kev + ((1 + sKE d Kev) + ((1 + sKE d Kev) + ((1 + sKE d Kev) + (1 + sKE d Kev)))))) +
    ((J + 1 - 0) * (sLB d Kev + 2) + 2))

set_option maxHeartbeats 16000000 in
theorem sLine_runs {XO : XCtxO d} {ℓa ℓ : ℕ} {EV : XCmdO} {Dat : Env d → Prop} {evN : (Fin d → ℤ) → ℤ}
    {Kev bv : ℕ} {Y0 : Fin d → ℤ} {e1 : ℕ} (H : SEvH L XO ℓa ℓ s EV Dat evN Kev bv Sev Nev Arev Y0 E e1 σ0)
    {σ : Env d} (h : LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ) {B : ℕ} (hl0 : 0 ≤ len) (hlE : len ≤ 2 ^ E)
    (hdomL : ∀ t, 0 ≤ t → t ≤ len → SepDom Y0 E e1 (Y + t • eZ i)) (bY : ∀ m, |Y m| ≤ 2 ^ B) (bE : E ≤ B)
    (hbvB : bv ≤ B) (hB1 : bv + 2 + (E + eτ + 1) ≤ B) (hB2 : E + eu ≤ B) (hB : B + 2 < ℓ) (h2B : 2 ≤ B)
    (hJa : J + 1 < 2 ^ ℓa) :
    XRunsBO L XO ℓa ℓ (xsLine L s EV) σ (sLK d J Kev) (fun σ' =>
      LOut s (lineZ (fun t => evN (Y + t • eZ i)) len (2 ^ (E + eτ + 1)) (2 ^ eu) J) σ' ∧
        LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ' ∧ SKeepA s σ σ') := by
  have hus := H.hs.scs.2.2.2.2.2.2
  obtain ⟨hnJ, hnok, hn0⟩ := H.hs.nats
  obtain ⟨hJok, hJn, hokn⟩ := H.hs.nats_ne
  have bb : ∀ z : ℤ, |z| ≤ 2 ^ B → |z| < 2 ^ ℓ := fun z hz =>
    lt_of_le_of_lt hz (pow_lt_pow_right₀ (by norm_num) (by omega))
  have hf : ∀ t, 0 ≤ t → t ≤ len → |evN (Y + t • eZ i)| < 2 ^ bv := fun t h0 h1 => H.hbv _ (hdomL t h0 h1)
  unfold sLK
  -- the counter and its bound
  have hinit : XRunsB L XO.X ℓa ℓ (.seq (.prim (.frag (.nconst (s.n0 + 5) 0)))
      (.prim (.frag (.nadd (s.n0 + 6) s.nJ (s.n0 + 1))))) σ (1 + 1) (fun σ1 =>
      σ1.nat (s.n0 + 5) = 0 ∧ σ1.nat (s.n0 + 6) = J + 1 ∧ LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ1 ∧
        SKeepA s σ σ1) := by
    refine XV.seq (XV.nconst H.hL (i := s.n0 + 5) (by omega) 0 (by omega)) fun σa ea => ?_
    subst ea
    refine XV.mono (XV.nadd H.hL (i := s.n0 + 6) (a := s.nJ) (b := s.n0 + 1) (by omega) (by omega) (by omega)
      (lt_of_eq_of_lt (by simp [show s.nJ ≠ s.n0 + 5 by omega, h.nJ]) (show J < 2 ^ ℓa by omega))
      (lt_of_eq_of_lt (by simp [h.n1]) (show 1 < 2 ^ ℓa by omega))) le_rfl fun σb eb => ?_
    subst eb
    refine ⟨by simp, by simp [show s.nJ ≠ s.n0 + 5 by omega, h.nJ, h.n1], ?_, ?_⟩
    · exact (h.setNat H.hs (j := s.n0 + 5) (by omega) (by omega) _).setNat H.hs (j := s.n0 + 6) (by omega)
        (by omega) _
    · exact ((SKeepA.refl σ).setNat (j := s.n0 + 5) (by omega) _).setNat (j := s.n0 + 6) (by omega) _
  refine XVO.seq (XVO.ofX hinit) fun σ1 ⟨n15, n16, E1, k1⟩ => ?_
  refine XVO.seq (sFirst_runs H E1 hl0 hlE hdomL bY bE hbvB (by omega) h2B) fun σ2 ⟨W2, E2, k2⟩ => ?_
  have n25 : σ2.nat (s.n0 + 5) = 0 := by rw [k2.1 _ (Or.inl ⟨by omega, by omega, by omega, by omega⟩), n15]
  have n26 : σ2.nat (s.n0 + 6) = J + 1 := by rw [k2.1 _ (Or.inl ⟨by omega, by omega, by omega, by omega⟩), n16]
  refine XVO.mono (XVO.whileN H.hL (i := s.n0 + 5) (j := s.n0 + 6) (by omega) (by omega)
    (fun t σ' => σ'.nat (s.n0 + 6) = J + 1 ∧ LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ' ∧ SKeepA s σ σ' ∧
      ((σ'.nat (s.n0 + 5) = t ∧ t ≤ J ∧ ∃ W, LWin s σ' W ∧ WinOK len bv W ∧
        lineLoopZ (fun t => evN (Y + t • eZ i)) (2 ^ (E + eτ + 1)) (2 ^ eu) (J - t) W =
          lineZ (fun t => evN (Y + t • eZ i)) len (2 ^ (E + eτ + 1)) (2 ^ eu) J) ∨
       (σ'.nat (s.n0 + 5) = J + 1 ∧
        LOut s (lineZ (fun t => evN (Y + t • eZ i)) len (2 ^ (E + eτ + 1)) (2 ^ eu) J) σ')))
    (J + 1) (sLB d Kev) ?_ ?_ ?_ 0 σ2 ⟨n26, E2, k1.trans k2.a, Or.inl ⟨n25, Nat.zero_le _,
      lineFirstZ (fun t => evN (Y + t • eZ i)) len, W2, winOK_first hf hl0, rfl⟩⟩) le_rfl ?_
  · rintro t σ' ⟨n6, -, -, hI⟩
    rcases hI with ⟨n5, ht, -⟩ | ⟨n5, -⟩
    · rw [n5, n6]; omega
    · rw [n5, n6]; omega
  · rintro t σ' ⟨n6, -, -, hI⟩ hc
    rcases hI with ⟨n5, ht, -⟩ | ⟨n5, -⟩
    · omega
    · rw [n5, n6] at hc; omega
  · rintro t σ' ⟨n6, E', kA, hI⟩ hc
    rcases hI with ⟨n5, ht, W, hW, hWok, hR⟩ | ⟨n5, -⟩
    swap
    · rw [n5, n6] at hc; omega
    obtain ⟨hp0, hl0', hle, c0, c1, c2, c3, c4⟩ := id hWok
    have m4 : |W.sd * 2 ^ (E + eτ + 1)| ≤ 2 ^ B := by
      have h1 := absI_sub_le (absI_add_le c3.le c1.le) (absI_add_le c2.le c2.le)
      rw [show W.v3 + W.v1 - (W.v2 + W.v2) = W.sd by simp only [WinZ.sd]; ring] at h1
      exact absI_mono (absI_mul_le h1 (bound_two_pow _)) (by omega)
    have m5 : |W.lam * 2 ^ eu| ≤ 2 ^ B := by
      have h1 : |W.lam| ≤ 2 ^ E := by rw [abs_of_nonneg hl0']; omega
      exact absI_mono (absI_mul_le h1 (bound_two_pow _)) (by omega)
    refine XVO.seq (XVO.ofX (sTest_runs H.hL H.hs E' hW hWok hlE hB1 hB2 (by omega)))
      fun σ1 ⟨t17, t18, E1, W1, k1, _⟩ => ?_
    have n15 : σ1.nat (s.n0 + 5) = t := by rw [k1.1 _ (Or.inl ⟨by omega, by omega, by omega, by omega⟩), n5]
    have n16 : σ1.nat (s.n0 + 6) = J + 1 := by rw [k1.1 _ (Or.inl ⟨by omega, by omega, by omega, by omega⟩), n6]
    have kA1 := kA.trans k1.a
    refine XVO.ifS H.hL (x := s.u + 18) (y := s.u + 17) (K := 6 * sKE d Kev + 24 + 1 + 2) (by omega) (by omega)
      (by rw [t18]; exact XV.abs_int_lt (bb _ m5)) (by rw [t17]; exact XV.abs_int_lt (bb _ m4)) (fun hc' => ?_)
      (fun hc' => ?_)
    · have hcz : W.lam * 2 ^ eu < W.sd * 2 ^ (E + eτ + 1) := by rw [t17, t18] at hc'; exact_mod_cast hc'
      have hnot : ¬ W.sd * 2 ^ (E + eτ + 1) ≤ W.lam * 2 ^ eu := not_le.mpr hcz
      refine XVO.ifN H.hL (i := s.n0 + 5) (j := s.nJ) (K := 6 * sKE d Kev + 24 + 1) (by omega) (by omega)
        (by rw [n15]; omega) (by rw [E1.nJ]; omega) (fun hcn => ?_) (fun hcn => ?_)
      · rw [n15, E1.nJ] at hcn
        refine XVO.seq (sHalve_runs H E1 W1 hWok hlE hdomL bY bE hbvB hB h2B) fun σ2 ⟨W2, E2, k2⟩ => ?_
        have n25 : σ2.nat (s.n0 + 5) = t := by
          rw [k2.1 _ (Or.inl ⟨by omega, by omega, by omega, by omega⟩), n15]
        have n26 : σ2.nat (s.n0 + 6) = J + 1 := by
          rw [k2.1 _ (Or.inl ⟨by omega, by omega, by omega, by omega⟩), n16]
        refine XVO.mono (XVO.nadd H.hL (i := s.n0 + 5) (a := s.n0 + 5) (b := s.n0 + 1) (by omega) (by omega)
          (by omega) (by rw [n25]; omega) (by rw [E2.n1]; omega)) le_rfl fun σ3 e3 => ?_
        subst e3
        refine ⟨by simp [n26], E2.setNat H.hs (by omega) (by omega) _, (kA1.trans k2.a).setNat (by omega) _,
          Or.inl ⟨by simp [n25, E2.n1], by omega, _, W2.setNat _ _, winOK_halve hf hWok, ?_⟩⟩
        rw [← hR, show J - t = (J - (t + 1)) + 1 by omega, lineLoopZ_succ hnot]
      · rw [n15, E1.nJ] at hcn
        refine XVO.mono (K := 1 + 1) (XVO.ofX ?_) (by omega) (fun _ h => h)
        refine XV.seq (XV.nconst H.hL (i := s.n0 + 7) (by omega) 0 (by omega)) fun σ2 e2 => ?_
        subst e2
        refine XV.mono (XV.nadd H.hL (i := s.n0 + 5) (a := s.n0 + 6) (b := s.n0 + 8) (by omega) (by omega)
          (by omega) (lt_of_eq_of_lt (by simp [n16]) (show J + 1 < 2 ^ ℓa by omega))
          (lt_of_eq_of_lt (by simp [E1.nz]) (show 0 < 2 ^ ℓa by omega))) le_rfl fun σ3 e3 => ?_
        subst e3
        have hRn : lineZ (fun t => evN (Y + t • eZ i)) len (2 ^ (E + eτ + 1)) (2 ^ eu) J = none := by
          rw [← hR, show J - t = 0 by omega, lineLoopZ_zero hnot]
        refine ⟨by simp [n16], (E1.setNat H.hs (by omega) (by omega) _).setNat H.hs (by omega) (by omega) _,
          (kA1.setNat (by omega) _).setNat (by omega) _, Or.inr ⟨by simp [n16, E1.nz], ?_, ?_⟩⟩
        · intro _; simp
        · intro r hr; rw [hRn] at hr; exact absurd hr (by simp)
    · have hle' : W.sd * 2 ^ (E + eτ + 1) ≤ W.lam * 2 ^ eu := by
        rw [t17, t18] at hc'; push_neg at hc'; exact_mod_cast hc'
      have hRs : lineZ (fun t => evN (Y + t • eZ i)) len (2 ^ (E + eτ + 1)) (2 ^ eu) J =
          some (W.p0 + 2 * W.lam, W.lam) := by
        rw [← hR, lineLoopZ_stop hle']
      obtain ⟨wp, wl, -⟩ := W1
      have bt : ∀ z : ℤ, 0 ≤ z → z ≤ len → |z| ≤ 2 ^ B := fun z h0 h1 => bound_of_le h0 h1 hlE bE
      refine XVO.mono (K := 1 + (1 + (1 + (1 + 1)))) (XVO.ofX ?_) (by omega) (fun _ h => h)
      refine XV.seq (XV.addI H.hL (x := s.u + 19) (a := s.u + 2) (b := s.u + 1) (u := W.p0) (v := W.lam)
        (by omega) (by omega) (by omega) wp wl (bb _ (bt _ hp0 (by omega))) (bb _ (bt _ hl0' (by omega)))
        (bb _ (bt _ (by omega) (by omega)))) fun σ2 e2 => ?_
      subst e2
      refine XV.seq (XV.addI H.hL (x := s.u + 19) (a := s.u + 19) (b := s.u + 1) (u := W.p0 + W.lam)
        (v := W.lam) (by omega) (by omega) (by omega) (by simp) (by simp [wl]) (bb _ (bt _ (by omega) (by omega)))
        (bb _ (bt _ hl0' (by omega))) (bb _ (bt _ (by omega) (by omega)))) fun σ3 e3 => ?_
      subst e3
      refine XV.seq (XV.addI H.hL (x := s.u + 20) (a := s.u + 1) (b := s.u + 16) (u := W.lam) (v := 0)
        (by omega) (by omega) (by omega) (by simp [wl]) (by simp [E1.zero]) (bb _ (bt _ hl0' (by omega)))
        (by simp) (by simpa using bb _ (bt _ hl0' (by omega)))) fun σ4 e4 => ?_
      subst e4
      refine XV.seq (XV.nconst H.hL (i := s.n0 + 7) (by omega) 1 (by omega)) fun σ5 e5 => ?_
      subst e5
      refine XV.mono (XV.nadd H.hL (i := s.n0 + 5) (a := s.n0 + 6) (b := s.n0 + 8) (by omega) (by omega)
        (by omega) (lt_of_eq_of_lt (by simp [n16]) (show J + 1 < 2 ^ ℓa by omega))
          (lt_of_eq_of_lt (by simp [E1.nz]) (show 0 < 2 ^ ℓa by omega))) le_rfl fun σ6 e6 => ?_
      subst e6
      refine ⟨by simp [n16], ?_, ?_, Or.inr ⟨by simp [n16, E1.nz], ?_, ?_⟩⟩
      · exact ((((E1.setSc H.hs (x := s.u + 19) (by omega) (by omega) (by omega) (by omega) _).setSc H.hs
          (x := s.u + 19) (by omega) (by omega) (by omega) (by omega) _).setSc H.hs (x := s.u + 20) (by omega)
          (by omega) (by omega) (by omega) _).setNat H.hs (by omega) (by omega) _).setNat H.hs (by omega)
          (by omega) _
      · exact ((((kA1.setSc _ _).setSc _ _).setSc _ _).setNat (by omega) _).setNat (by omega) _
      · intro hn; rw [hRs] at hn; exact absurd hn (by simp)
      · intro r hr
        rw [hRs, Option.some.injEq] at hr
        subst hr
        refine ⟨by simp, ?_, by simp⟩
        show _ = ((W.p0 + 2 * W.lam : ℤ) : ℝ)
        rw [show W.p0 + 2 * W.lam = W.p0 + W.lam + W.lam by ring]
        simp
  · rintro σ' ⟨t', ⟨n6, E', kA, hI⟩, hc⟩
    rcases hI with ⟨n5, ht, -⟩ | ⟨n5, hO⟩
    · rw [n5, n6] at hc; omega
    · exact ⟨hO, E', kA⟩

end AdversarialBco.Uni
