/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLRowC

@[expose] public section

/-!
# The preparation of BL's calls, part 1: two array loops

* `xredArr`, `XV.redArr`: for the cells `k < K`, the pair `(u_k, v_k)` (`v_k > 0`) of the arrays `an`, `ad` reduced by
  the gcd into the cells `k` of the arrays `on`, `dn`, and the slot `sP` multiplied by every reduced denominator;
* `xscaleArr`, `XV.scaleArr`: for the cells `k < K`, `on[k] := on[k] (D / dn[k]) M` (`D` in `sD`, `M` in `sM`).

Both use the slots `96..104` as scratch and one register `rk` as counter.
-/

namespace AdversarialBco.Bit.Transfer.BLM.PrepM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer.RowP AdversarialBco.Bit.Transfer.BLM.RowM

variable {d : ℕ}

/-- One cell `k` (register `rk`): `96 := an[k]`, `97 := ad[k]`, the reduced pair in `101`, `102`, into `on[k]`,
`dn[k]`, then `sP := sP · 102`. -/
def xredCell (L : Layout) (an ad on dn rk sP : ℕ) : XCmd :=
  .seq (toX (VL.aget L 96 an rk)) (.seq (toX (VL.aget L 97 ad rk)) (.seq (xred L sZ 96 97 98 99 100 101 102)
    (.seq (toX (VL.aset L on rk 101)) (.seq (toX (VL.aset L dn rk 102)) (toX (VL.sop2 L .mul sP sP 102))))))

/-- The reduction of the cells `k < K` (`K` in the register `rn`). -/
def xredArr (L : Layout) (an ad on dn rk rn sP : ℕ) : XCmd := xforN rk rn rOne (xredCell L an ad on dn rk sP)

/-- The units of one cell and of the loop. -/
def redCellUnits (s : ℕ) : ℕ := 2 + (2 + (redUnits s + (2 + (2 + 1))))
def redArrUnits (K s : ℕ) : ℕ := K * (redCellUnits s + 3) + 3

/-- The reduced numerator and denominator of `u / v`. -/
def redN (u v : ℤ) : ℤ := u / (Int.gcd u v : ℤ)
def redD (u v : ℤ) : ℤ := v / (Int.gcd u v : ℤ)

set_option maxHeartbeats 4000000 in
/-- **The reduction of an array of pairs.** -/
theorem XV.redArr {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hNS : 128 ≤ L.NS)
    (hNN : 65 ≤ L.NN)
    {an ad on dn rk rn sP K s S0 : ℕ} {u v : ℕ → ℤ} {P0 : ℤ} (han : an < L.NA) (had : ad < L.NA)
    (hon : on < L.NA) (hdn : dn < L.NA) (harr : [an, ad, on, dn].Nodup) (hrk : rk < L.NN) (hrn : rn < L.NN)
    (hrk1 : rk ≠ rn) (hrk2 : rk ≠ rOne) (hsP : 103 ≤ sP) (hsP' : sP < L.NS)
    (hn : σ.nat rn = K) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (hP : σ.sc sP = P0)
    (hu : ∀ k < K, σ.arr an k = u k) (hv : ∀ k < K, σ.arr ad k = v k)
    (bu : ∀ k < K, |u k| ≤ 2 ^ s) (bv : ∀ k < K, 0 < v k ∧ v k ≤ 2 ^ s) (bP : 0 < P0 ∧ P0 ≤ 2 ^ S0)
    (hK : K ≤ asz d) (hs : S0 + s * K + 1 < ℓ) (hKa : K < 2 ^ ℓa) (hs1 : s + 1 < ℓ) :
    XRunsB L X ℓa ℓ (xredArr L an ad on dn rk rn sP) σ (redArrUnits K s) (fun σ' =>
      (∀ k < K, σ'.arr on k = ((redN (u k) (v k) : ℤ) : ℝ) ∧ σ'.arr dn k = ((redD (u k) (v k) : ℤ) : ℝ)) ∧
      σ'.sc sP = ((P0 * ∏ k ∈ Finset.range K, redD (u k) (v k) : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => (96 ≤ y ∧ y ≤ 102) ∨ y = sP) (fun j => j = rk) (fun a k => (a = on ∨ a = dn) ∧ k < K)
        σ σ') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at harr
  obtain ⟨⟨a1, a2, a3⟩, ⟨a4, a5⟩, a6⟩ := harr
  have hs0 : s + 1 < ℓ := hs1
  have hsl : s < ℓ := by omega
  let J : ℕ → Env d → Prop := fun t σ' =>
    (∀ k < t, σ'.arr on k = ((redN (u k) (v k) : ℤ) : ℝ) ∧ σ'.arr dn k = ((redD (u k) (v k) : ℤ) : ℝ)) ∧
      σ'.sc sP = ((P0 * ∏ k ∈ Finset.range t, redD (u k) (v k) : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => (96 ≤ y ∧ y ≤ 102) ∨ y = sP) (fun j => j = rk) (fun a k => (a = on ∨ a = dn) ∧ k < K) σ σ'
  refine XV.mono (XV.forN hL (i := rk) (n := rn) (one := rOne) (body := xredCell L an ad on dn rk sP) hrk hrn
    (by rwgo) hrk1 hrk2 K (redCellUnits s) hKa J σ hn h1
    ⟨fun k h => absurd h (Nat.not_lt_zero _), by rwenv; rw [hP]; simp, by rwenv,
      (FrameA.refl (fun y => (96 ≤ y ∧ y ≤ 102) ∨ y = sP) (fun j => j = rk)
        (fun a k => (a = on ∨ a = dn) ∧ k < K) σ).setNat rfl _⟩ ?_) le_rfl fun σ' ⟨hJ, _⟩ => hJ
  intro t ht σ' ⟨hA, hR, hdr, hF⟩ htk htn ht1
  obtain ⟨v1, v2⟩ := bv t ht
  have ez : σ'.sc sZ = 0 := by rw [hF.2.1 sZ (by rwgo), hz]
  have eu : σ'.arr an t = u t := by rw [hF.2.2.1 an t (by omega), hu t ht]
  have ev : σ'.arr ad t = v t := by rw [hF.2.2.1 ad t (by omega), hv t ht]
  have hta : σ'.nat rk < asz d := by rw [htk]; omega
  refine XV.seq (XV.aget hL (x := 96) (a := an) (i := rk) (by omega) han hrk hta
    (by rw [htk, eu]; exact XV.abs_int_lt (absI_le_pow (bu t ht) hsl))) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.aget hL (x := 97) (a := ad) (i := rk) (by omega) had hrk (by rwenv; exact hta)
    (by rwenv; rw [htk, ev]; exact XV.abs_int_lt (absI_le_pow (by rw [abs_of_pos v1]; exact v2) hsl)))
    fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.red hL (z := sZ) (sN := 96) (sD := 97) (sa := 98) (sb := 99) (st := 100) (snum := 101)
    (sden := 102) (by rwgo) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by decide) (N := u t) (D := v t) (s := s) (by rwenv; exact ez) (by rwenv; rw [htk, eu])
    (by rwenv; rw [htk, ev]) v1 (bu t ht) v2 hs0) fun σ3 ⟨r1, r2, r3, r4⟩ => ?_
  obtain ⟨g1, g2, g3, g4⟩ := red_bounds (u t) (v t) v1
  have b101 : |redN (u t) (v t)| ≤ 2 ^ s := g2.trans (bu t ht)
  have b102 : |redD (u t) (v t)| ≤ 2 ^ s := by
    unfold redD; rw [abs_of_pos (by omega)]; exact g4.trans v2
  have n3 : σ3.nat rk = t := by rw [r4.1 rk not_false]; rwenv; exact htk
  refine XV.seq (XV.aset hL (a := on) (i := rk) (x := 101) hon hrk (by omega) (by rw [n3]; omega)
    (by rw [r1]; exact XV.abs_int_lt (absI_le_pow b101 hsl))) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.aset hL (a := dn) (i := rk) (x := 102) hdn hrk (by omega) (by rwenv; rw [n3]; omega)
    (by rwenv; rw [r2]; exact XV.abs_int_lt (absI_le_pow b102 hsl))) fun σ5 e5 => ?_
  subst e5
  obtain ⟨p1, p2⟩ := prod_range_abs_le (fun k => redD (u k) (v k)) (2 ^ s) (one_le_pow₀ (by norm_num)) t
    (fun k hk => by
      obtain ⟨_, _, h3, h4⟩ := red_bounds (u k) (v k) (bv k (by omega)).1
      exact ⟨h3, h4.trans (bv k (by omega)).2⟩)
  have bprod : |P0 * ∏ k ∈ Finset.range t, redD (u k) (v k)| ≤ 2 ^ (S0 + s * t) := by
    rw [abs_mul, abs_of_pos bP.1, abs_of_pos (by omega), pow_add, pow_mul]
    exact mul_le_mul bP.2 p2 (by omega) (by positivity)
  have eP : σ3.sc sP = ((P0 * ∏ k ∈ Finset.range t, redD (u k) (v k) : ℤ) : ℝ) := by
    rw [r4.2.1 sP (by omega)]; rwenv; exact hR
  have hst : S0 + s * t + s < ℓ := by nlinarith
  refine XV.mono (XV.mulI hL (x := sP) (a := sP) (b := 102) hsP' hsP' (by omega)
    (u := P0 * ∏ k ∈ Finset.range t, redD (u k) (v k)) (v := redD (u t) (v t)) (by rwenv; exact eP) (by rwenv; exact r2)
    (absI_le_pow bprod (by omega)) (absI_le_pow b102 hsl) (absI_le_pow (absI_mul_le bprod b102) hst)) le_rfl
    fun σ6 e6 => ?_
  subst e6
  have a3' : ∀ a k, σ3.arr a k = σ'.arr a k := fun a k => by
    rw [r4.2.2.1 a k not_false]; rwenv
  refine ⟨by rwenv; exact n3, by rwenv; rw [r4.1 rn not_false]; rwenv; exact htn,
    by rwenv; rw [r4.1 rOne not_false]; rwenv; exact ht1, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
    · simp only [Env.setNat_arr, Env.setSc_arr, Env.setArr_nat, Env.setArr_sc, Env.setArr_arr, n3,
        show k ≠ t by omega, and_false, ite_false, a3']
      exact hA k h
    · subst h
      simp only [Env.setNat_arr, Env.setSc_arr, Env.setArr_nat, Env.setArr_sc, Env.setArr_arr, n3, a6,
        false_and, and_self, ite_true, ite_false, r1, r2]
      exact ⟨rfl, rfl⟩
  · rwenv; rw [Finset.prod_range_succ]; push_cast; ring
  · rwenv; rw [r3]; rwenv; exact hdr
  · have F : FrameA (fun y => (96 ≤ y ∧ y ≤ 102) ∨ y = sP) (fun j => j = rk) (fun a k => (a = on ∨ a = dn) ∧ k < K)
        σ' σ3 :=
      (((FrameA.refl _ _ _ σ').setSc (Or.inl ⟨le_rfl, by norm_num⟩) _).setSc
        (Or.inl ⟨by norm_num, by norm_num⟩) _).trans
        (r4.mono (fun y h => Or.inl (by omega)) (fun _ h => h.elim) (fun _ _ h => h.elim))
    exact ((((hF.trans F).setArr ⟨Or.inl rfl, by rw [n3]; exact ht⟩ _).setArr
      ⟨Or.inr rfl, by rwenv; rw [n3]; exact ht⟩ _).setSc (Or.inr rfl) _).setNat rfl _

/-- One cell `k` (register `rk`): `103 := on[k]`, `104 := dn[k]`, `104 := sD / 104`, `103 := 103 · 104 · sM`, into
`on[k]`. -/
def xscaleCell (L : Layout) (on dn rk sD sM : ℕ) : XCmd :=
  .seq (toX (VL.aget L 103 on rk)) (.seq (toX (VL.aget L 104 dn rk)) (.seq (xsidiv L 104 sD 104)
    (.seq (toX (VL.sop2 L .mul 103 103 104)) (.seq (toX (VL.sop2 L .mul 103 103 sM)) (toX (VL.aset L on rk 103))))))

/-- The scaling of the cells `k < K` (`K` in the register `rn`). -/
def xscaleArr (L : Layout) (on dn rk rn sD sM : ℕ) : XCmd := xforN rk rn rOne (xscaleCell L on dn rk sD sM)

/-- The units of the scaling loop. -/
def scaleArrUnits (K : ℕ) : ℕ := K * (2 + (2 + (1 + (1 + (1 + 2)))) + 3) + 3

set_option maxHeartbeats 4000000 in
/-- **The scaling of an array**: `on[k] := nu_k (D / de_k) M` for `k < K`. -/
theorem XV.scaleArr {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hNS : 128 ≤ L.NS)
    (hNN : 65 ≤ L.NN)
    {on dn rk rn sD sM K s S T : ℕ} {nu de : ℕ → ℤ} {D Mu : ℤ} (hon : on < L.NA) (hdn : dn < L.NA)
    (hod : on ≠ dn) (hrk : rk < L.NN) (hrn : rn < L.NN) (hrk1 : rk ≠ rn) (hrk2 : rk ≠ rOne)
    (hsD : sD < L.NS) (hsM : sM < L.NS) (hsD' : sD ≠ 103 ∧ sD ≠ 104) (hsM' : sM ≠ 103 ∧ sM ≠ 104)
    (hn : σ.nat rn = K) (h1 : σ.nat rOne = 1) (hD : σ.sc sD = D) (hM : σ.sc sM = Mu)
    (hnu : ∀ k < K, σ.arr on k = nu k) (hde : ∀ k < K, σ.arr dn k = de k)
    (bnu : ∀ k < K, |nu k| ≤ 2 ^ s) (bde : ∀ k < K, 1 ≤ de k ∧ de k ≤ 2 ^ s) (bD : 0 ≤ D ∧ D ≤ 2 ^ S)
    (bM : |Mu| ≤ 2 ^ T) (hK : K ≤ asz d) (hs : s + S + T < ℓ) (hKa : K < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xscaleArr L on dn rk rn sD sM) σ (scaleArrUnits K) (fun σ' =>
      (∀ k < K, σ'.arr on k = ((nu k * (D / de k) * Mu : ℤ) : ℝ)) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = 103 ∨ y = 104) (fun j => j = rk) (fun a k => a = on ∧ k < K) σ σ') := by
  have hsl : s < ℓ := by omega
  have hSl : S < ℓ := by omega
  have hTl : T < ℓ := by omega
  let J : ℕ → Env d → Prop := fun t σ' =>
    (∀ k < t, σ'.arr on k = ((nu k * (D / de k) * Mu : ℤ) : ℝ)) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = 103 ∨ y = 104) (fun j => j = rk) (fun a k => a = on ∧ k < t) σ σ'
  refine XV.mono (XV.forN hL (i := rk) (n := rn) (one := rOne) (body := xscaleCell L on dn rk sD sM) hrk hrn
    (by rwgo) hrk1 hrk2 K (2 + (2 + (1 + (1 + (1 + 2))))) hKa J σ hn h1
    ⟨fun k h => absurd h (Nat.not_lt_zero _), by rwenv,
      (FrameA.refl (fun y => y = 103 ∨ y = 104) (fun j => j = rk) (fun a k => a = on ∧ k < 0) σ).setNat rfl _⟩ ?_)
    le_rfl fun σ' ⟨⟨hA, hdr, hF⟩, _⟩ => ⟨hA, hdr, hF.mono (fun _ h => h) (fun _ h => h)
      (fun a k h => ⟨h.1, h.2⟩)⟩
  intro t ht σ' ⟨hA, hdr, hF⟩ htk htn ht1
  obtain ⟨d1, d2⟩ := bde t ht
  have enu : σ'.arr on t = nu t := by rw [hF.2.2.1 on t (by omega), hnu t ht]
  have ede : σ'.arr dn t = de t := by rw [hF.2.2.1 dn t (by omega), hde t ht]
  have eD : σ'.sc sD = D := by rw [hF.2.1 sD (by omega), hD]
  have eM : σ'.sc sM = Mu := by rw [hF.2.1 sM (by omega), hM]
  have hta : σ'.nat rk < asz d := by rw [htk]; omega
  have bq : |D / de t| ≤ 2 ^ S := by
    rw [abs_of_nonneg (Int.ediv_nonneg bD.1 (by omega))]; exact (Int.ediv_le_self _ bD.1).trans bD.2
  have bnq : |nu t * (D / de t)| ≤ 2 ^ (s + S) := absI_mul_le (bnu t ht) bq
  have bnqm : |nu t * (D / de t) * Mu| ≤ 2 ^ (s + S + T) := absI_mul_le bnq bM
  refine XV.seq (XV.aget hL (x := 103) (a := on) (i := rk) (by omega) hon hrk hta
    (by rw [htk, enu]; exact XV.abs_int_lt (absI_le_pow (bnu t ht) hsl))) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.aget hL (x := 104) (a := dn) (i := rk) (by omega) hdn hrk (by rwenv; exact hta)
    (by rwenv; rw [htk, ede]; exact XV.abs_int_lt (absI_le_pow (by rw [abs_of_pos (by omega)]; exact d2) hsl)))
    fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.divI hL (x := 104) (a := sD) (b := 104) (by omega) hsD (by omega) (u := D) (v := de t)
    (by rwenv; exact eD) (by rwenv; rw [htk, ede]) (absI_le_pow (by rw [abs_of_nonneg bD.1]; exact bD.2) hSl)
    (absI_le_pow (by rw [abs_of_pos (by omega)]; exact d2) hsl)) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.mulI hL (x := 103) (a := 103) (b := 104) (by omega) (by omega) (by omega) (u := nu t)
    (v := D / de t) (by rwenv; rw [htk, enu]) (by rwenv) (absI_le_pow (bnu t ht) hsl) (absI_le_pow bq hSl)
    (absI_le_pow bnq (by omega))) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.mulI hL (x := 103) (a := 103) (b := sM) (by omega) (by omega) hsM
    (u := nu t * (D / de t)) (v := Mu) (by rwenv) (by rwenv; exact eM) (absI_le_pow bnq (by omega))
    (absI_le_pow bM hTl) (absI_le_pow bnqm hs)) fun σ5 e5 => ?_
  subst e5
  refine XV.mono (XV.aset hL (a := on) (i := rk) (x := 103) hon hrk (by omega) (by rwenv; exact hta)
    (by rwenv; exact XV.abs_int_lt (absI_le_pow bnqm hs))) le_rfl fun σ6 e6 => ?_
  subst e6
  refine ⟨by rwenv; exact htk, by rwenv; exact htn, by rwenv; exact ht1, ?_, by rwenv; exact hdr, ?_⟩
  · intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
    · simp only [Env.setNat_arr, Env.setArr_arr, Env.setSc_nat, Env.setSc_arr, htk, show k ≠ t by omega,
        and_false, ite_false]
      exact hA k h
    · subst h
      simp only [Env.setNat_arr, Env.setArr_arr, Env.setSc_nat, htk, and_self, ite_true, sc_setSc_eq]
  · exact ((((((hF.mono (fun _ h => h) (fun _ h => h) (fun a k h => ⟨h.1, by omega⟩)).setSc (Or.inl rfl) _).setSc
      (Or.inr rfl) _).setSc (Or.inr rfl) _).setSc (Or.inl rfl) _).setSc (Or.inl rfl) _).setArr
      ⟨rfl, by rwenv; rw [htk]; omega⟩ _ |>.setNat rfl _

end AdversarialBco.Bit.Transfer.BLM.PrepM
