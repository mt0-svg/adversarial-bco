/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriConst

@[expose] public section

/-!
# TRI-M, the constants on the machine

* `tcG`: the parameter of the bounds of the two straight lines of XTriConst.lean; `tsSt_sem`, `tcSt_sem`: their
  side conditions;
* `xsearch`, `XV.search`: `triSQ d` by the test of the parameter lemma at `s = 4, 5, ...`, into the slot `o + 115`.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM
  AdversarialBco.Bit.Transfer.BLM

variable {d : ℕ}

/-! ## The parameter of the bounds -/

/-- The parameter of the bounds of both lines: the exponents of the powers of two, `d`, `size n` and `triSQ d`. -/
def tcG (d n : ℕ) : ℕ :=
  triLa (triSQ d) + triLh (triSQ d) + triJaQ d + triBvQ d + 2 * tzP d + tzGc d (ellPos d n) + d + n.size + triSQ d

theorem tsSt_sem {d n s : ℕ} (hs : s ≤ triSQ d) :
    ∀ k < tsSt.length, (tsSt.getD k (.cst 0)).Sem (tsV d s) (tcG d n) := by
  intro k hk
  rw [tsSt_length] at hk
  have hLa : triLa s ≤ triLa (triSQ d) := Nat.div_le_div_right (Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left hs 2))
  interval_cases k <;> simp only [tsSt, List.getD_cons_succ, List.getD_cons_zero, SStep.Sem, tsV_9]
  exact ⟨Nat.cast_nonneg _, by exact_mod_cast (show triLa s ≤ tcG d n by unfold tcG; omega)⟩

set_option maxHeartbeats 1000000 in
theorem tcSt_sem {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    ∀ k < tcSt.length, (tcSt.getD k (.cst 0)).Sem (tcV d n) (tcG d n) := by
  intro k hk
  rw [tcSt_length] at hk
  have p : ∀ x : ℕ, x ≤ tcG d n → (0 : ℤ) ≤ x ∧ (x : ℤ) ≤ ((tcG d n : ℕ) : ℤ) :=
    fun x h => ⟨Nat.cast_nonneg x, by exact_mod_cast h⟩
  interval_cases k <;> simp only [tcSt, List.getD_cons_succ, List.getD_cons_zero, SStep.Sem, tcV_22, tcV_23,
    tcV_25, tcV_30, tcV_31, tcV_34, tcV_40 d n hd, tcV_42 d n hd, tcV_46 d n hd, tcV_48 d n hd, tcV_50 d n hd,
    tcV_52 d n hd, tcV_56, tcV_58, tcV_62 d n hd hn, tcV_63 d n hd hn, tcV_67 d n hd hn, tcV_70 d n hd hn,
    tcV_71 d n hd hn, tcV_74 d n hd hn, tcV_77 d n hd hn, tcV_79 d n hd hn] <;>
    first | exact Nat.cast_nonneg _ | exact p _ (by unfold tcG tzGc tzG; omega)

theorem tcG_in {d n x : ℕ} (h : x ≤ tcG d n) : |(x : ℤ)| ≤ 2 ^ ev (tcG d n) (tcInP 0) := by
  rw [abs_of_nonneg (Nat.cast_nonneg x)]
  simp only [tcInP, ev, one_mul, add_zero]
  exact_mod_cast h.trans Nat.lt_two_pow_self.le

theorem tsIn_bound {d n s : ℕ} (hs : s ≤ triSQ d) : ∀ y ∈ [113, 115], |tsIn d s y| ≤ 2 ^ ev (tcG d n) (tcInP y) := by
  intro y hy
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
  rcases hy with rfl | rfl
  · simp only [tsIn, ↓reduceIte]; exact tcG_in (by unfold tcG; omega)
  · simp only [tsIn, Nat.reduceEqDiff, ↓reduceIte]; exact tcG_in (by unfold tcG; omega)

theorem tcIn_bound {d n : ℕ} : ∀ y ∈ [113, 114, 115], |tcIn d n y| ≤ 2 ^ ev (tcG d n) (tcInP y) := by
  intro y hy
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
  rcases hy with rfl | rfl | rfl
  · simp only [tcIn, ↓reduceIte]; exact tcG_in (by unfold tcG; omega)
  · simp only [tcIn, Nat.reduceEqDiff, ↓reduceIte]
    rw [abs_of_nonneg (Nat.cast_nonneg n)]
    simp only [tcInP, ev, one_mul, add_zero]
    have h1 : n < 2 ^ n.size := Nat.lt_size_self n
    have h2 : 2 ^ n.size ≤ 2 ^ tcG d n := Nat.pow_le_pow_right (by norm_num) (by unfold tcG; omega)
    exact_mod_cast (h1.trans_le h2).le
  · simp only [tcIn, Nat.reduceEqDiff, ↓reduceIte]; exact tcG_in (by unfold tcG; omega)

theorem tcC_ok {L : Layout} {o r : ℕ} (hS : o + 245 ≤ L.NS) (hN : r + 31 ≤ L.NN) : (SLC.atB o r tcC).OK L 40 := by
  constructor <;> simp only [SLC.atB, tcC, List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] <;> omega

/-! ## The search of `triSQ d` -/

/-- `125 (2^{L_a(s)} - 1)^2 < 2086812 d^2 L_h(s)`: the parameter lemma's test fails at `s`. -/
def parFails (d s : ℕ) : Prop := 125 * (2 ^ triLa s - 1) ^ 2 < 2086812 * d ^ 2 * triLh s

theorem triSQ_spec (d : ℕ) : 4 ≤ triSQ d ∧ ¬ parFails d (triSQ d) := by
  have h := Nat.find_spec (pg_par_exists d)
  refine ⟨h.1, ?_⟩
  unfold parFails triLa triLh
  exact not_lt.2 h.2

/-- The search: the test at `s` (in `o + 115`), then while it fails, `s := s + 1` and the test again. -/
def xsearch (L : Layout) (o r : ℕ) : XCmd :=
  .seq (SL.code L (SLC.atB o r tcC) (tsSt.map (SStep.shS o)))
    (xwhileS L (o + 132) (o + 133) (.seq (toX (VL.sop2 L .add (o + 115) (o + 115) (o + 2)))
      (SL.code L (SLC.atB o r tcC) (tsSt.map (SStep.shS o)))))

/-- The units of the search. -/
abbrev srchK (d n : ℕ) : ℕ := ev (tcG d n) (4, 44) + (7 * (d + 10) * (1 + ev (tcG d n) (4, 44) + 2) + 2)

/-- The slots and registers the search may change. -/
abbrev srS (o : ℕ) (y : ℕ) : Prop := y = o + 115 ∨ o + 120 ≤ y

/-- The registers the search may change. -/
abbrev srN (r : ℕ) (j : ℕ) : Prop := j = r + 29 ∨ j = r + 30

set_option maxHeartbeats 4000000 in
/-- **The search of `triSQ d`** from `s = 4` in the slot `o + 115`: it ends with `triSQ d` there. -/
theorem XV.search {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {o r n : ℕ}
    (hS : o + 245 ≤ L.NS) (hN : r + 31 ≤ L.NN)
    (hTl : ev (tcG d n) tcT < ℓ) (hTa : ev (tcG d n) tcT < 2 ^ ℓa)
    (e113 : σ.sc (o + 113) = ((d : ℤ) : ℝ)) (e115 : σ.sc (o + 115) = (((4 : ℕ) : ℤ) : ℝ))
    (e1 : σ.sc (o + 1) = 0) (e2 : σ.sc (o + 2) = 1) (e116 : σ.sc (o + 116) = 2) (e117 : σ.sc (o + 117) = 4)
    (er : σ.nat r = 1) :
    XRunsB L X ℓa ℓ (xsearch L o r) σ (srchK d n) (fun σ' =>
      σ'.sc (o + 115) = (((triSQ d : ℕ) : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧ FrameP (srS o) (srN r) σ σ') := by
  have hC := tcC_ok (o := o) (r := r) hS hN
  obtain ⟨hs4, hsP⟩ := triSQ_spec d
  have hΓl : tcG d n + 1 < ℓ := by have := hTl; simp only [ev, tcT] at this; omega
  have hsΓ : triSQ d ≤ tcG d n := by unfold tcG; omega
  have hTle : ∀ k < 14, ev (tcG d n) (tsEt k) < ℓ := fun k hk => by
    refine lt_of_le_of_lt (ev_mono ?_) hTl
    interval_cases k <;> decide
  -- one run of the test from a state holding `s` and the constants
  have run : ∀ (s : ℕ) (σ' : Env d), s ≤ triSQ d → FrameP (srS o) (srN r) σ σ' →
      σ'.sc (o + 115) = ((s : ℤ) : ℝ) →
      XRunsB L X ℓa ℓ (SL.code L (SLC.atB o r tcC) (tsSt.map (SStep.shS o))) σ' (ev (tcG d n) (4, 44))
        (fun σ'' => (∀ k < 14, σ''.sc (o + 120 + k) = tsV d s k) ∧ σ''.sc (o + 115) = σ'.sc (o + 115) ∧
          σ''.draws = σ'.draws ∧ FrameP (srS o) (srN r) σ' σ'') := by
    intro s σ' hs hF h115
    have k113 : σ'.sc (o + 113) = ((d : ℤ) : ℝ) := by rw [hF.2.1 _ (by simp only [srS]; omega), e113]
    have k1 : σ'.sc (o + 1) = 0 := by rw [hF.2.1 _ (by simp only [srS]; omega), e1]
    have k2 : σ'.sc (o + 2) = 1 := by rw [hF.2.1 _ (by simp only [srS]; omega), e2]
    have k116 : σ'.sc (o + 116) = 2 := by rw [hF.2.1 _ (by simp only [srS]; omega), e116]
    have k117 : σ'.sc (o + 117) = 4 := by rw [hF.2.1 _ (by simp only [srS]; omega), e117]
    have kr : σ'.nat r = 1 := by rw [hF.1 _ (by simp only [srN]; omega), er]
    have h := XV.slAt (X := X) (σ := σ') (G := tcG d n) (et := tsEt) (T := tcT) (ι := tsIn d s)
      (ins := [113, 115]) (eIn := tcInP) hL hC tsSt_chk (fun k hk => tsSt_sem hs k hk)
      (by rw [tsSt_length]; decide) hTl hTa (tsIn_bound hs)
      (fun y hy => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
        rcases hy with rfl | rfl
        · rw [Nat.add_comm, k113]; simp only [tsIn, ↓reduceIte]
        · rw [Nat.add_comm, h115]; simp only [tsIn, Nat.reduceEqDiff, ↓reduceIte])
      (by simp only [tcC]; rw [Nat.add_comm, k1]) (by simp only [tcC]; rw [Nat.add_comm, k2])
      (by simp only [tcC]; rw [Nat.add_comm, k116]) (by simp only [tcC]; rw [Nat.add_comm, k117])
      (by simp only [tcC]; rw [Nat.zero_add, kr])
    rw [tsSt_units] at h
    refine XV.mono h le_rfl fun σ'' ⟨hv, hd', hF'⟩ => ⟨fun k hk => ?_, ?_, hd', ?_⟩
    · have := hv k (by rw [tsSt_length]; exact hk)
      simp only [tcC] at this
      rw [show o + 120 + k = 120 + o + k by omega, this]
    · exact hF'.2.1 _ (by simp only [tcC, tsSt_length]; omega)
    · simp only [tcC, tsSt_length] at hF'
      exact hF'.mono (fun y hy => by simp only [srS]; omega) (fun j hj => by simp only [srN]; omega)
  let I : ℕ → Env d → Prop := fun t σ' =>
    σ'.sc (o + 115) = (((4 + t : ℕ) : ℤ) : ℝ) ∧ (∀ k < 14, σ'.sc (o + 120 + k) = tsV d (4 + t) k) ∧
      4 + t ≤ triSQ d ∧ (∀ s', 4 ≤ s' → s' < 4 + t → parFails d s') ∧ σ'.draws = σ.draws ∧
      FrameP (srS o) (srN r) σ σ'
  -- the values compared by the loop
  have cmp : ∀ s (σ' : Env d), (∀ k < 14, σ'.sc (o + 120 + k) = tsV d s k) →
      (σ'.sc (o + 132) < σ'.sc (o + 133) ↔ parFails d s) := by
    intro s σ' hv
    rw [show o + 132 = o + 120 + 12 by omega, show o + 133 = o + 120 + 13 by omega, hv 12 (by omega),
      hv 13 (by omega), tsV_12, tsV_13]
    unfold parFails
    constructor <;> intro h <;> exact_mod_cast h
  have bnd : ∀ s (σ' : Env d), s ≤ triSQ d → (∀ k < 14, σ'.sc (o + 120 + k) = tsV d s k) →
      |σ'.sc (o + 132)| < 2 ^ ℓ ∧ |σ'.sc (o + 133)| < 2 ^ ℓ := by
    intro s σ' hs hv
    have hb := SL.val_bound tsSt 120 (tsIn d s) [113, 115] tcInP tsEt tcT 40 (tcG d n)
      (SL.chk_get tsSt_chk).2 (fun k hk => tsSt_sem hs k hk) (tsIn_bound hs)
    rw [show o + 132 = o + 120 + 12 by omega, show o + 133 = o + 120 + 13 by omega, hv 12 (by omega),
      hv 13 (by omega)]
    exact ⟨absZ_lt (hb 12 (by rw [tsSt_length]; omega)) (hTle 12 (by omega)),
      absZ_lt (hb 13 (by rw [tsSt_length]; omega)) (hTle 13 (by omega))⟩
  refine XV.seq (run 4 σ hs4 (FrameP.refl _ _ σ) e115) fun σ0 ⟨v0, u0, d0, F0⟩ => ?_
  have I0 : I 0 σ0 := ⟨by rw [u0]; exact e115, v0, hs4,
    fun s' h1 h2 => absurd h2 (by omega), d0, F0⟩
  refine XV.mono (XV.whileS hL (by omega) (by omega) I (7 * (d + 10)) (1 + ev (tcG d n) (4, 44))
    (fun t σ' hI => bnd (4 + t) σ' hI.2.2.1 hI.2.1) ?_ ?_ 0 σ0 I0) (by rw [Nat.sub_zero]) ?_
  · intro t σ' ⟨_, hv, ht, _⟩ hlt
    have hf := (cmp _ σ' hv).1 hlt
    have hne : 4 + t ≠ triSQ d := fun h => hsP (h ▸ hf)
    have := (triSQ_bounds d).2
    omega
  · intro t σ' ⟨h115, hv, ht, hmin, hd', hF⟩ hlt
    have hf := (cmp _ σ' hv).1 hlt
    have hne : 4 + t ≠ triSQ d := fun h => hsP (h ▸ hf)
    have h115' : |σ'.sc (o + 115)| < 2 ^ ℓ := by
      rw [h115]; exact natZ_lt (by positivity) (le_refl _) (by omega)
    refine XV.seq (XV.sop2 hL (x := o + 115) (a := o + 115) (b := o + 2) (by omega) (by omega) (by omega) .add
      (by intro h; cases h) h115'
      (by rw [hF.2.1 _ (by simp only [srS]; omega), e2, abs_one]; exact one_lt_pow₀ (by norm_num) (by omega))
      (by
        rw [hF.2.1 (o + 2) (by simp only [srS]; omega), e2, h115]
        simp only [RealRAM.Op2.eval]
        exact_mod_cast natZ_lt (x := ((4 + t + 1 : ℕ) : ℤ)) (by positivity) (le_refl _)
          (by omega))) fun σ1 e1' => ?_
    have F1 : FrameP (srS o) (srN r) σ σ1 := by rw [e1']; exact hF.setSc (Or.inl rfl) _
    have v1 : σ1.sc (o + 115) = (((4 + (t + 1) : ℕ) : ℤ) : ℝ) := by
      rw [e1', sc_setSc_eq, hF.2.1 (o + 2) (by simp only [srS]; omega), e2, h115]
      simp only [RealRAM.Op2.eval]; push_cast; ring
    refine XV.mono (run (4 + (t + 1)) σ1 (by omega) F1 v1) le_rfl fun σ2 ⟨v2, u2, d2, F2⟩ => ?_
    refine ⟨by rw [u2]; exact v1, v2, by omega, fun s' h1 h2 => ?_,
      by rw [d2, e1', Env.setSc_draws, hd'], F1.trans F2⟩
    rcases Nat.lt_or_ge s' (4 + t) with h | h
    · exact hmin s' h1 h
    · rw [show s' = 4 + t by omega]; exact hf
  · rintro σ' ⟨t, ⟨h115, hv, _, hmin, hd', hF⟩, hnlt⟩
    have hok : ¬ parFails d (4 + t) := fun h => hnlt ((cmp _ σ' hv).2 h)
    have hs : triSQ d = 4 + t := triSQ_eq_of d (4 + t) (by omega) (by unfold parFails at hok; omega)
      (fun s' h1 h2 => hmin s' h1 h2)
    exact ⟨by rw [h115, hs], hd', hF⟩

end AdversarialBco.Bit.Transfer
