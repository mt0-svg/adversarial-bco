/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.XRunsO
public import AdversarialBco.Unified.SepSpec
public import AdversarialBco.Bit.Transfer.XVec

@[expose] public section

/-!
# UNI-CM on the oracle machine

The CM block `xcm L c` and its contract `cmBlockOK : CMBlockOK L XO ℓa ℓ c (xcm L c)`. From the point `y = N/D` in
array `ap`, the centre `a = Na/Da` in array `aa`, `r₀ = rn/rd` and `2^k` in scalars, the block writes the query point
`cmPt a r₀ k y` into array `aq` as `(Dq; Nq)` with

* `Dq = D Da (2^k rn)`,
* `Nq_i = N_i P - Na_i Q`, `P = (2^k rn + rd + rd) Da`, `Q = (rd + rd) D`,

in integer arithmetic (the constants and `Dq`, then the `d` numerators, `cmLoop_runs`), then asks the oracle
once at that point with the precision `k` (`XVO.orc`). Every intermediate value is below `2^{2b + bt + k + 3}`.
-/

namespace AdversarialBco.Uni

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer

variable {d : ℕ}

/-! ## The values -/

/-- `P = (2^k rn + rd + rd) Da`. -/
def cmP (Da rn rd : ℤ) (k : ℕ) : ℤ := (2 ^ k * rn + rd + rd) * Da

/-- `Q = (rd + rd) D`. -/
def cmQv (D rd : ℤ) : ℤ := (rd + rd) * D

/-- `Dq = D Da (2^k rn)`. -/
def cmDq (D Da rn : ℤ) (k : ℕ) : ℤ := D * Da * (2 ^ k * rn)

/-- The query point of UNI-CM as `Nq/Dq`. -/
theorem cmPt_eq (D Da rn rd : ℤ) (k : ℕ) (Nv Na : Fin d → ℤ) (hD : 0 < D) (hDa : 0 < Da) (hrn : 0 < rn)
    (hrd : 0 < rd) (i : Fin d) :
    cmPt (ptDN Da Na) ((rn : ℚ) / rd) k (ptDN D Nv) i =
      ((Nv i * cmP Da rn rd k - Na i * cmQv D rd : ℤ) : ℚ) / (cmDq D Da rn k : ℚ) := by
  have h1 : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have h2 : (Da : ℚ) ≠ 0 := by exact_mod_cast hDa.ne'
  have h3 : (rn : ℚ) ≠ 0 := by exact_mod_cast hrn.ne'
  have h4 : (rd : ℚ) ≠ 0 := by exact_mod_cast hrd.ne'
  simp only [cmPt, ptDN, cmP, cmQv, cmDq, one_div, inv_pow]
  push_cast
  field_simp
  ring

/-! ## The code -/

/-- The loop: `for n0+1 < d: aq[n0] := ap[n0] P - aa[n0] Q; n0 := n0 + 1`. -/
def xcmLoop (L : Layout) (c : CMLay) : XCmd :=
  xforN (c.n0 + 1) (c.n0 + 2) (c.n0 + 3)
    (.seq (toX (VL.aget L (c.u + 6) c.ap c.n0))
    (.seq (toX (VL.sop2 L .mul (c.u + 6) (c.u + 6) (c.u + 3)))
    (.seq (toX (VL.aget L (c.u + 7) c.aa c.n0))
    (.seq (toX (VL.sop2 L .mul (c.u + 7) (c.u + 7) (c.u + 4)))
    (.seq (toX (VL.sop2 L .sub (c.u + 6) (c.u + 6) (c.u + 7)))
    (.seq (toX (VL.aset L c.aq c.n0 (c.u + 6)))
      (.prim (.frag (.nadd c.n0 c.n0 (c.n0 + 3))))))))))

/-! ## The preamble -/

theorem bound_two_pow (k : ℕ) : |(2 : ℤ) ^ k| ≤ 2 ^ k := by rw [abs_of_pos (by positivity)]

/-! ## The loop -/

set_option maxHeartbeats 4000000 in
theorem cmLoop_runs {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {c : CMLay} (hc : CMLay.OK L c)
    {σ : Env d} {P Q : ℤ} {Nv Na : Fin d → ℤ} {B : ℕ} (hP : σ.sc (c.u + 3) = P) (hQ : σ.sc (c.u + 4) = Q)
    (hr : σ.nat c.n0 = 1) (hn : σ.nat (c.n0 + 2) = d) (h1 : σ.nat (c.n0 + 3) = 1)
    (hNv : ∀ i : Fin d, σ.arr c.ap (1 + (i : ℕ)) = Nv i) (hNa : ∀ i : Fin d, σ.arr c.aa (1 + (i : ℕ)) = Na i)
    (bP : |P| ≤ 2 ^ B) (bQ : |Q| ≤ 2 ^ B) (bNv : ∀ i, |Nv i| ≤ 2 ^ B) (bNa : ∀ i, |Na i| ≤ 2 ^ B)
    (bNvP : ∀ i, |Nv i * P| ≤ 2 ^ B) (bNaQ : ∀ i, |Na i * Q| ≤ 2 ^ B) (hB : B + 1 < ℓ) :
    XRunsB L X ℓa ℓ (xcmLoop L c) σ (d * (10 + 3) + 3) (fun σ' =>
      (∀ i : Fin d, σ'.arr c.aq (1 + (i : ℕ)) = ((Nv i * P - Na i * Q : ℤ) : ℝ)) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = c.u + 6 ∨ y = c.u + 7) (fun j => j = c.n0 + 1 ∨ j = c.n0)
        (fun b' k' => b' = c.aq ∧ 1 ≤ k') σ σ') := by
  obtain ⟨⟨ha, hp, hq⟩, ⟨hqa, hqp⟩, ⟨hs1, hs2, hs3, hs4⟩, -, ⟨hn1, hn2, hn3⟩, -⟩ := hc
  have bb : ∀ z : ℤ, |z| ≤ 2 ^ (B + 1) → |z| < 2 ^ ℓ := fun z hz =>
    lt_of_le_of_lt hz (pow_lt_pow_right₀ (by norm_num) hB)
  have bb' : ∀ z : ℤ, |z| ≤ 2 ^ B → |z| < 2 ^ ℓ := fun z hz => bb z (absI_mono hz (by omega))
  have hasz := asz_lt hL ha
  have hda : d < 2 ^ ℓa := lt_of_le_of_lt (by unfold asz; nlinarith) hasz
  refine XV.mono (XV.forN hL (i := c.n0 + 1) (n := c.n0 + 2) (one := c.n0 + 3) (by omega) (by omega) (by omega)
    (by omega) (by omega) d 10 hda
    (fun t σ' => σ'.nat c.n0 = 1 + t ∧ σ'.draws = σ.draws ∧
      (∀ i : Fin d, (i : ℕ) < t → σ'.arr c.aq (1 + (i : ℕ)) = ((Nv i * P - Na i * Q : ℤ) : ℝ)) ∧
      FrameA (fun y => y = c.u + 6 ∨ y = c.u + 7) (fun j => j = c.n0 + 1 ∨ j = c.n0)
        (fun b' k' => b' = c.aq ∧ 1 ≤ k') σ σ')
    σ hn h1 ⟨by simp [hr], by simp, fun i hi => absurd hi (Nat.not_lt_zero _),
      (FrameA.refl _ _ _ σ).setNat (Or.inl rfl) 0⟩ ?_) le_rfl
    fun σ' ⟨⟨_, hd', hk, hF⟩, _⟩ => ⟨fun i => hk i i.2, hd', hF⟩
  intro t ht σ' ⟨hr', hd', hk', hF'⟩ hkt hkn hk1
  have hidx : 1 + t < asz d := by unfold asz; nlinarith
  have hta : 1 + t < 2 ^ ℓa := lt_trans hidx hasz
  have eP : σ'.sc (c.u + 3) = P := by rw [hF'.2.1 _ (by omega), hP]
  have eQ : σ'.sc (c.u + 4) = Q := by rw [hF'.2.1 _ (by omega), hQ]
  have eNv : σ'.arr c.ap (1 + t) = Nv ⟨t, ht⟩ := by
    rw [hF'.2.2.1 _ _ (fun h => hqp h.1.symm)]; exact hNv ⟨t, ht⟩
  have eNa : σ'.arr c.aa (1 + t) = Na ⟨t, ht⟩ := by
    rw [hF'.2.2.1 _ _ (fun h => hqa h.1.symm)]; exact hNa ⟨t, ht⟩
  have bD := absI_sub_le (bNvP ⟨t, ht⟩) (bNaQ ⟨t, ht⟩)
  refine XV.mono (K := 2 + (1 + (2 + (1 + (1 + (2 + 1)))))) ?_ le_rfl (fun _ h => h)
  refine XV.seq (XV.aget hL (x := c.u + 6) (a := c.ap) (i := c.n0) (by omega) hp (by omega)
    (by rw [hr']; exact hidx) (by rw [hr', eNv]; exact XV.abs_int_lt (bb' _ (bNv _)))) fun σ1 e1 => ?_
  subst e1
  rw [hr', eNv]
  refine XV.seq (XV.mulI hL (x := c.u + 6) (a := c.u + 6) (b := c.u + 3) (u := Nv ⟨t, ht⟩) (v := P) (by omega)
    (by omega) (by omega) (by simp) (by simp [eP]) (bb' _ (bNv _)) (bb' _ bP) (bb' _ (bNvP _))) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.aget hL (x := c.u + 7) (a := c.aa) (i := c.n0) (by omega) ha (by omega)
    (by simp only [Env.setSc_nat, hr']; exact hidx)
    (by simp only [Env.setSc_nat, Env.setSc_arr, hr', eNa]; exact XV.abs_int_lt (bb' _ (bNa _)))) fun σ3 e3 => ?_
  subst e3
  simp only [Env.setSc_nat, Env.setSc_arr, hr', eNa]
  refine XV.seq (XV.mulI hL (x := c.u + 7) (a := c.u + 7) (b := c.u + 4) (u := Na ⟨t, ht⟩) (v := Q) (by omega)
    (by omega) (by omega) (by simp) (by simp [eQ]) (bb' _ (bNa _)) (bb' _ bQ) (bb' _ (bNaQ _))) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.subI hL (x := c.u + 6) (a := c.u + 6) (b := c.u + 7) (u := Nv ⟨t, ht⟩ * P)
    (v := Na ⟨t, ht⟩ * Q) (by omega) (by omega) (by omega) (by simp) (by simp) (bb' _ (bNvP _)) (bb' _ (bNaQ _))
    (bb _ bD)) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.aset hL (a := c.aq) (i := c.n0) (x := c.u + 6) hq (by omega) (by omega)
    (by simp only [Env.setSc_nat, hr']; exact hidx)
    (by rw [Env.setSc_sc, ite_eq_left rfl]; exact XV.abs_int_lt (bb _ bD))) fun σ6 e6 => ?_
  subst e6
  simp only [Env.setSc_nat, hr']
  refine XV.mono (XV.nadd hL (i := c.n0) (a := c.n0) (b := c.n0 + 3) (by omega) (by omega) (by omega)
    (by simp only [Env.setArr_nat, Env.setSc_nat, hr']; exact hta)
    (by simp only [Env.setArr_nat, Env.setSc_nat, hk1]; omega)) le_rfl fun σ7 e7 => ?_
  subst e7
  refine ⟨by simp [hkt], by simp [hkn], by simp [hk1], by simp [hr', hk1]; omega, by simp [hd'], ?_, ?_⟩
  · intro j hj
    simp only [Env.setNat_arr, Env.setArr_arr]
    by_cases hjt : (j : ℕ) = t
    · have hj' : j = ⟨t, ht⟩ := Fin.ext hjt
      subst hj'
      simp
    · rw [ite_eq_right (by omega)]
      exact hk' j (by omega)
  · exact hF'.setSc (Or.inl rfl) _ |>.setSc (Or.inl rfl) _ |>.setSc (Or.inr rfl) _ |>.setSc (Or.inr rfl) _
      |>.setSc (Or.inl rfl) _ |>.setArr ⟨rfl, by omega⟩ _ |>.setNat (Or.inr rfl) _ |>.setNat (Or.inl rfl) _

end AdversarialBco.Uni
