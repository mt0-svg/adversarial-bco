/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLR9b

@[expose] public section

/-!
# BL's round on the machine: R10's sums

`d²` into the register `25`, then `Σ B̂'²` into the slot `89`, `Σ Â'²` into the slot `90` (sums over the `d²` cells of
the arrays `27` and `26`), and `2 Λ Q²` into the slot `88`: R10's tests are `sc 88 < sc 89` and `sc 88 < sc 90`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

/-- `r25 := d²` by `d` additions of `d`. -/
def xdd : XCmd := .seq (.prim (.frag (.nconst 25 0))) (xforN 24 rD rOne (.prim (.frag (.nadd 25 25 rD))))

theorem XV.dd {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {σ : Env d}
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ xdd σ (1 + (d * (1 + 3) + 3)) (fun σ' => σ'.nat 25 = d * d ∧ σ'.draws = σ.draws ∧
      FrameA (fun _ => False) (fun j => j = 24 ∨ j = 25) (fun _ _ => False) σ σ') := by
  obtain ⟨-, hN, -⟩ := hlay
  simp only [rEE] at hN
  refine XV.seq (XV.nconst hL (σ := σ) (i := 25) (by omega) 0 (by positivity)) fun σ0 e0 => ?_
  subst e0
  refine XV.mono (XV.forN hL (i := 24) (n := rD) (one := rOne) (by omega) (by simp only [rD]; omega)
    (by simp only [rOne]; omega) (by decide) (by decide) d 1 (by nlinarith)
    (fun t σ' => σ'.nat 25 = d * t ∧ σ'.draws = σ.draws ∧
      FrameA (fun _ => False) (fun j => j = 24 ∨ j = 25) (fun _ _ => False) σ σ')
    (σ.setNat 25 0) (by simpa [rD] using hD) (by simpa [rOne] using h1)
    ⟨by simp, by simp, ((FrameA.refl _ _ _ σ).setNat (Or.inr rfl) 0).setNat (Or.inl rfl) 0⟩ ?_)
    le_rfl fun σ' ⟨⟨h25, hd', F'⟩, _⟩ => ⟨h25, hd', F'⟩
  intro t ht σ' ⟨h25, hd', F'⟩ hi hn ho
  refine XV.mono (XV.nadd hL (σ := σ') (i := 25) (a := 25) (b := rD) (by omega) (by omega)
    (by simp only [rD]; omega) (by rw [h25]; nlinarith) (by rw [hn]; nlinarith)) le_rfl fun σ'' e => ?_
  subst e
  refine ⟨by simp [hi], by simp [hn], by simp [ho], by simp [h25, hn]; ring, by simp [hd'], ?_⟩
  exact (F'.setNat (Or.inr rfl) _).setNat (Or.inl rfl) _

/-- `r := Σ_{k < d²} aY[k]²`, the cell in the register `22`, the counter in `23`, `d²` in `25`. -/
def xsq2 (L : Layout) (r aY : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst 22 0))) (xfoldE L sZ r tR (.op .mul (.arr aY 22) (.arr aY 22)) 22 rOne 23 25 rOne)

set_option maxHeartbeats 1000000 in
theorem XV.sq2 {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {σ : Env d}
    {r aY E : ℕ} {Bf : ℕ → ℤ} (hr : r < tR) (hr0 : r ≠ sZ) (hY : aY < aWE) (hz : σ.sc sZ = 0)
    (h25 : σ.nat 25 = d * d) (h1 : σ.nat rOne = 1) (eB : ∀ k < d * d, σ.arr aY k = Bf k)
    (bB : ∀ k < d * d, |Bf k| ≤ 2 ^ E) (hE : 2 * E < ℓ) (hℓ : d * d * 2 ^ (2 * E) < 2 ^ ℓ)
    (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xsq2 L r aY) σ (1 + (d * d * (5 + 5) + 4)) (fun σ' =>
      σ'.sc r = ((∑ k ∈ Finset.range (d * d), Bf k * Bf k : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = r ∨ tR ≤ y) (fun j => j = 22 ∨ j = 23) (fun _ _ => False) σ σ') := by
  have hlay' := hlay
  obtain ⟨hS, hN, hA⟩ := hlay'
  simp only [oE, rEE, aWE] at hS hN hA hY
  refine XV.seq (XV.nconst hL (σ := σ) (i := 22) (by omega) 0 (by positivity)) fun σ0 e0 => ?_
  subst e0
  have F0 : FrameA (fun y => y = r ∨ tR ≤ y) (fun j => j = 22 ∨ j = 23) (fun _ _ => False) σ (σ.setNat 22 0) :=
    (FrameA.refl _ _ _ σ).setNat (Or.inl rfl) 0
  have hpow : ∀ k ≤ d * d, |∑ j ∈ Finset.range k, Bf j * Bf j| ≤ d * d * 2 ^ (2 * E) := by
    intro k hk
    calc |∑ j ∈ Finset.range k, Bf j * Bf j| ≤ ∑ j ∈ Finset.range k, |Bf j * Bf j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range k, (2 ^ (2 * E) : ℤ) := Finset.sum_le_sum fun j hj => by
          have hj' : j < d * d := lt_of_lt_of_le (Finset.mem_range.1 hj) hk
          rw [abs_mul, two_mul, pow_add]
          exact mul_le_mul (bB j hj') (bB j hj') (abs_nonneg _) (by positivity)
      _ = (k : ℤ) * 2 ^ (2 * E) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ d * d * 2 ^ (2 * E) := by
          exact_mod_cast Nat.mul_le_mul_right _ hk
  refine XV.mono (XV.foldE hL (σ := σ.setNat 22 0) (z := sZ) (r := r) (t := tR) (nr := 22) (nst := rOne) (nk := 23)
    (nn := 25) (none := rOne) (E := E) (N := d * d) (base := 0) (st := 1)
    (e := .op .mul (.arr aY 22) (.arr aY 22)) (F := fun k => Bf k * Bf k)
    (by simp only [IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega) (by simp [sZ, tR]) hr
    (by simpa [sZ] using hr0) (by simp only [IE.scr, tR]; omega) (by simpa using hz) (by omega)
    (by simp only [rOne]; omega) (by omega) (by omega) (by simp only [rOne]; omega) (by decide) (by decide)
    (by decide) (by simpa using h25) (by simpa [rOne] using h1) (by simp) (by simpa [rOne] using h1) (by omega)
    (by omega) (by have := hL.1; omega) (by simp only [IE.top, IE.mag]; omega) ?_ ?_) le_rfl
    fun σ' ⟨v', _, d', F'⟩ => ⟨v', by simpa using d',
      (F0.trans (F'.mono (fun y h => h) (fun j h => by omega) (fun _ _ h => h)))⟩
  · intro k hk
    have := hpow k hk
    exact lt_of_le_of_lt this (by exact_mod_cast hℓ)
  · intro k hk σ' Fk dk hk' hr'
    have hc : k < asz d := by unfold asz; omega
    have e' : σ'.arr aY (σ'.nat 22) = Bf k := by rw [hr', Fk.2.2.1 _ _ id]; simpa using eB k hk
    refine ⟨?_, ?_⟩
    · exact ⟨⟨by rw [hr']; simpa using hc, Bf k, e', bB k hk⟩, ⟨by rw [hr']; simpa using hc, Bf k, e', bB k hk⟩⟩
    · simp only [IE.eval, RealRAM.Op2.eval, e']; push_cast; ring

/-- `2 Λ Q²` as an expression. -/
def ieLQ : IE :=
  .op .add (.op .mul (.op .mul (.sc sLam) (.sc s2p)) (.sc s2p)) (.op .mul (.op .mul (.sc sLam) (.sc s2p)) (.sc s2p))

/-- R10: `d²`, `Σ B̂'²` into `89`, `Σ Â'²` into `90`, `2 Λ Q²` into `88`. -/
def xR10 (L : Layout) : XCmd :=
  .seq xdd (.seq (xsq2 L 89 aBp) (.seq (xsq2 L 90 aAp) (ieLQ.code L sZ 88 tR)))

/-- The units of `xR10`. -/
def r10Units (d : ℕ) : ℕ :=
  (1 + (d * (1 + 3) + 3)) + ((1 + (d * d * (5 + 5) + 4)) + ((1 + (d * d * (5 + 5) + 4)) + ieLQ.units))

set_option maxHeartbeats 1000000 in
/-- **R10's sums on the machine.** -/
theorem XV.r10 {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {σ : Env d}
    {Q : ℤ} {Lam E : ℕ} {Af Bf : ℕ → ℤ} (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0)
    (eQ : σ.sc s2p = Q) (eL : σ.sc sLam = (Lam : ℤ)) (eA : ∀ k < d * d, σ.arr aAp k = Af k)
    (eB : ∀ k < d * d, σ.arr aBp k = Bf k) (bA : ∀ k < d * d, |Af k| ≤ 2 ^ E) (bB : ∀ k < d * d, |Bf k| ≤ 2 ^ E)
    (bQ : |Q| ≤ 2 ^ E) (bL : |(Lam : ℤ)| ≤ 2 ^ E) (hE : 3 * E + 1 < ℓ) (hℓ : d * d * 2 ^ (2 * E) < 2 ^ ℓ)
    (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xR10 L) σ (r10Units d) (fun σ' =>
      σ'.sc 89 = ((∑ k ∈ Finset.range (d * d), Bf k * Bf k : ℤ) : ℝ) ∧
      σ'.sc 90 = ((∑ k ∈ Finset.range (d * d), Af k * Af k : ℤ) : ℝ) ∧
      σ'.sc 88 = ((2 * (Lam : ℤ) * Q * Q : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = 88 ∨ y = 89 ∨ y = 90 ∨ tR ≤ y) (fun j => j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25)
        (fun _ _ => False) σ σ') := by
  have hlay' := hlay
  obtain ⟨hS, hN, hAr⟩ := hlay'
  simp only [oE, rEE, aWE] at hS hN hAr
  refine XV.seq (XV.dd hL hlay hD h1 hda) fun σ1 ⟨v1, d1, F1⟩ => ?_
  have sc1 : ∀ y, σ1.sc y = σ.sc y := fun y => F1.2.1 y id
  have ar1 : ∀ b k, σ1.arr b k = σ.arr b k := fun b k => F1.2.2.1 b k id
  have n1 : σ1.nat rOne = 1 := by rw [F1.1 _ (by simp [rOne]), h1]
  refine XV.seq (XV.sq2 hL hlay (σ := σ1) (r := 89) (aY := aBp) (E := E) (Bf := Bf) (by simp [tR])
    (by simp [sZ]) (by decide) (by rw [sc1, hz]) v1 n1 (fun k hk => by rw [ar1, eB k hk]) bB (by omega) hℓ hda)
    fun σ2 ⟨v2, d2, F2⟩ => ?_
  have sc2 : ∀ y, y ≠ 89 → y < tR → σ2.sc y = σ.sc y := fun y h h' => by rw [F2.2.1 y (by omega), sc1]
  have ar2 : ∀ b k, σ2.arr b k = σ.arr b k := fun b k => by rw [F2.2.2.1 b k id, ar1]
  have n2 : ∀ j, j ≠ 22 → j ≠ 23 → σ2.nat j = σ1.nat j := fun j a b => F2.1 j (by omega)
  refine XV.seq (XV.sq2 hL hlay (σ := σ2) (r := 90) (aY := aAp) (E := E) (Bf := Af) (by simp [tR])
    (by simp [sZ]) (by decide) (by rw [sc2 _ (by simp [sZ]) (by simp [sZ, tR]), hz])
    (by rw [n2 _ (by decide) (by decide), v1]) (by rw [n2 _ (by simp [rOne]) (by simp [rOne]), n1])
    (fun k hk => by rw [ar2, eA k hk]) bA (by omega) hℓ hda) fun σ3 ⟨v3, d3, F3⟩ => ?_
  have sc3 : ∀ y, y ≠ 89 → y ≠ 90 → y < tR → σ3.sc y = σ.sc y := fun y h h' h'' => by
    rw [F3.2.1 y (by omega), sc2 y h h'']
  have eQ3 : σ3.sc s2p = Q := by rw [sc3 _ (by simp [s2p]) (by simp [s2p]) (by simp [s2p, tR]), eQ]
  have eL3 : σ3.sc sLam = (Lam : ℤ) := by rw [sc3 _ (by simp [sLam]) (by simp [sLam]) (by simp [sLam, tR]), eL]
  refine XV.mono (XV.ieRun hL (σ := σ3) (z := sZ) (x := 88) (t := tR) (E := E) (e := ieLQ)
    (v := 2 * (Lam : ℤ) * Q * Q)
    (by simp only [ieLQ, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; romega) (by romega) (by romega)
    (by simp only [ieLQ, IE.scr, tR]; omega) (by rw [sc3 _ (by simp [sZ]) (by simp [sZ]) (by simp [sZ, tR]), hz])
    (by simp only [ieLQ, IE.Leaves, eQ3, eL3, Int.cast_inj, exists_eq_left', bQ, bL, and_self])
    (by simp only [ieLQ, IE.top, IE.mag]; omega)
    (by simp only [ieLQ, IE.eval, RealRAM.Op2.eval, eQ3, eL3]; push_cast; ring)) le_rfl
    fun σ4 ⟨v4, _, d4, F4⟩ => ?_
  refine ⟨by rw [F4.2.1 89 (by simp [tR]), F3.2.1 89 (by simp [tR]), v2], by rw [F4.2.1 90 (by simp [tR]), v3],
    v4, by rw [d4, d3, d2, d1], ?_⟩
  refine ⟨fun j hj => ?_, fun y hy => ?_, fun b k _ => ?_, ?_, ?_⟩
  · simp only [not_or] at hj
    rw [F4.1 j id, F3.1 j (by omega), F2.1 j (by omega), F1.1 j (by omega)]
  · simp only [not_or, not_le] at hy
    rw [F4.2.1 y (by omega), sc3 y (by omega) (by omega) (by omega)]
  · rw [F4.2.2.1, F3.2.2.1 b k id, ar2]
  · rw [F4.2.2.2.1, F3.2.2.2.1, F2.2.2.2.1, F1.2.2.2.1]
  · rw [F4.2.2.2.2, F3.2.2.2.2, F2.2.2.2.2, F1.2.2.2.2]

end AdversarialBco.Bit.Transfer.BLM
