/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XFrameET

@[expose] public section

/-!
# The loop of ELL-F on the machine

`xfrLoop` runs `frLoop p q capA capa α B nn N Â â` (Bit/RoutQ.lean) in the machine: the matrix `Â` in the array `a0`
(entry `(i, k)` in the cell `d i + k`), the centre `â` in the array `a0 + 1`. Each turn: the rows (`xfrRows`); with no
failing row the point is returned; with a failing row `i` and `α_i·α_i = 0` the procedure fails, else the update of
ELL-R with `j = 1` on the cut `α_i` (`xupd`), and a fail if it fails. The slot `P + 8` gets the outcome: `2` for a
returned point (in the array `a0 + 1`), `1` for a fail, `0` when the `N` turns ran out. Registers: the turn `n0 + 6`,
the bound `n0 + 7`.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## The program -/

/-- One turn of ELL-F. -/
def xfrBody (L : Layout) (B : PrBlk) (P u a0 n0 : ℕ) : XCmd :=
  .seq (xfrRows L B P u a0 n0)
  (xifS L (P + 7) (u + 1) (xellStop L P u n0 (u + 2))
    (xifS L u (P + 2)
      (.seq (xupd L u a0 n0 B.rd (n0 + 4))
        (xifS L u (u + 13) (xellStop L P u n0 (u + 1)) (.prim (.frag (.nadd (n0 + 6) (n0 + 6) (n0 + 4))))))
      (xellStop L P u n0 (u + 1))))

/-- The loop: the turn to `0`, the outcome to `0`, at most `nat (n0 + 7)` turns. -/
def xfrLoop (L : Layout) (B : PrBlk) (P u a0 n0 : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst (n0 + 6) 0))) (.seq (xset L (P + 8) u u)
    (.whileN (n0 + 6) (n0 + 7) (xfrBody L B P u a0 n0)))

/-! ## The steps of `frLoop` -/

section Steps

variable {m p q : ℕ} {capA capa : ℤ} {al : Fin m → Fin d → ℤ} {Bv nn : Fin m → ℤ} {k : ℕ}
  {A : Matrix (Fin d) (Fin d) ℤ} {a : Fin d → ℤ}

/-- The test of a row in `frLoop`. -/
abbrev frT (al : Fin m → Fin d → ℤ) (Bv nn : Fin m → ℤ) (a : Fin d → ℤ) (i : Fin m) : Bool :=
  decide (Bv i - 2 * (al i ⬝ᵥ a) < 0 ∨ (Bv i - 2 * (al i ⬝ᵥ a)) ^ 2 < nn i)

theorem frLoop_ret (h : (List.finRange m).find? (frT al Bv nn a) = none) :
    frLoop p q capA capa al Bv nn (k + 1) A a = some a := by
  rw [frLoop, h]

theorem frLoop_nn0 {i : Fin m} (h : (List.finRange m).find? (frT al Bv nn a) = some i) (h0 : nn i = 0) :
    frLoop p q capA capa al Bv nn (k + 1) A a = none := by
  rw [frLoop, h]; simp [h0]

theorem frLoop_fail {i : Fin m} (h : (List.finRange m).find? (frT al Bv nn a) = some i) (h0 : nn i ≠ 0)
    (hu : ellUpd p q 1 capA capa A a (al i) = none) : frLoop p q capA capa al Bv nn (k + 1) A a = none := by
  rw [frLoop, h]; simp [h0, hu]

theorem frLoop_next {i : Fin m} {A' : Matrix (Fin d) (Fin d) ℤ} {a' : Fin d → ℤ}
    (h : (List.finRange m).find? (frT al Bv nn a) = some i) (h0 : nn i ≠ 0)
    (hu : ellUpd p q 1 capA capa A a (al i) = some (A', a')) :
    frLoop p q capA capa al Bv nn (k + 1) A a = frLoop p q capA capa al Bv nn k A' a' := by
  rw [frLoop, h]; simp [h0, hu]

end Steps

theorem dot_self_nonneg' (v : Fin d → ℤ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

/-! ## The data -/

/-- The state `(Â, â)` of the loop in the machine, within its caps. -/
def FrLSt (a0 : ℕ) (capA capa : ℤ) (A : Matrix (Fin d) (Fin d) ℤ) (a : Fin d → ℤ) (σ : Env d) : Prop :=
  (∀ i k : Fin d, σ.arr a0 (d * i + k) = A i k) ∧ (∀ k : Fin d, σ.arr (a0 + 1) k = a k) ∧
    (∀ i k, |A i k| ≤ capA) ∧ ∀ k, |a k| ≤ capa

/-- The slots the loop changes. -/
abbrev frlS (P u y : ℕ) : Prop := y = P + 2 ∨ y = P + 7 ∨ y = P + 8 ∨ u + 13 ≤ y

/-- The registers the loop changes. -/
abbrev frlN (B : PrBlk) (n0 j : ℕ) : Prop :=
  j = B.rE ∨ (n0 ≤ j ∧ j ≤ n0 + 3) ∨ (n0 + 5 ≤ j ∧ j ≤ n0 + 7) ∨ (n0 + 47 ≤ j ∧ j ≤ n0 + 49)

/-- The arrays the loop changes. -/
abbrev frlA (B : PrBlk) (a0 b _k : ℕ) : Prop := b = B.aW + 1 ∨ (a0 ≤ b ∧ b ≤ a0 + 5)

/-- The outcome of the loop on the result `r`: `2` in `P + 8` and the point in the array `a0 + 1`, or `0`, `1` in
`P + 8` and no point. -/
def FrLoopOut (P a0 : ℕ) (capa : ℤ) (r : Option (Fin d → ℤ)) (σ : Env d) : Prop :=
  (σ.sc (P + 8) = 2 ∧ ∃ x, r = some x ∧ (∀ k : Fin d, σ.arr (a0 + 1) k = x k) ∧ ∀ k, |x k| ≤ capa) ∨
    ((σ.sc (P + 8) = 0 ∨ σ.sc (P + 8) = 1) ∧ r = none)

/-- The units of one turn. -/
def frKb (d m E : ℕ) : ℕ := 4 + (m * (frRowK d + 2) + 2) + (200 * (E + 1) ^ 2 + 8)

/-- The invariant of the loop after `t` turns from `σ`. -/
def FrInv (B : PrBlk) (P u a0 n0 N : ℕ) (r : ℕ → Matrix (Fin d) (Fin d) ℤ → (Fin d → ℤ) → Option (Fin d → ℤ))
    (capA capa : ℤ) (A : Matrix (Fin d) (Fin d) ℤ) (a : Fin d → ℤ) (σ : Env d) (t : ℕ) (σ' : Env d) : Prop :=
  σ'.draws = σ.draws ∧ FrameA (frlS P u) (frlN B n0) (frlA B a0) σ σ' ∧
    σ'.nat (n0 + 6) ≤ N ∧ σ'.nat (n0 + 7) ≤ N ∧
    ((σ'.sc (P + 8) = 0 ∧ σ'.nat (n0 + 7) = N ∧ σ'.nat (n0 + 6) = t ∧
        ∃ A' a', FrLSt a0 capA capa A' a' σ' ∧ r N A a = r (N - t) A' a') ∨
      (σ'.sc (P + 8) = 1 ∧ σ'.nat (n0 + 7) = 0 ∧ r N A a = none) ∨
      (σ'.sc (P + 8) = 2 ∧ σ'.nat (n0 + 7) = 0 ∧
        ∃ x, r N A a = some x ∧ (∀ k : Fin d, σ'.arr (a0 + 1) k = x k) ∧ ∀ k, |x k| ≤ capa))

set_option maxHeartbeats 16000000 in
/-- **The loop of ELL-F on the machine**: `xfrLoop` runs `frLoop p q capA capa α B nn N Â â` from the state `(Â, â)`
in the machine (`FrLSt`), `N` in the register `n0 + 7`, the constants of the rows (`FrEnv`) and of the update with
`j = 1` (`UpdEnv`) in place. -/
theorem XV.frEllLoop {L : Layout} {w : BitRAM.World d} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : PrBlk} {p q P u a0 n0 E N : ℕ} {capA capa : ℤ}
    {A0 : Matrix (Fin d) (Fin d) ℤ} {x0 : Fin d → ℤ}
    (hPu : P + 9 ≤ u) (hS : u + 60 ≤ L.NS) (ha0 : B.aW + 2 ≤ a0) (hA : a0 + 6 ≤ L.NA)
    (hn0 : B.rE + 1 ≤ n0) (hN : n0 + 50 ≤ L.NN) (hrd : B.rd < B.rE) (hrm : B.rm < B.rE)
    (hE : FrEnv B m p P u n0 σ) (hU : UpdEnv u p q 1 capA capa σ) (hSt : FrLSt a0 capA capa A0 x0 σ)
    (hσN : σ.nat (n0 + 7) = N) (hNa : N < 2 ^ ℓa)
    (hMF : (frMhat A b : ℤ) ^ (d + 1) ≤ 2 ^ E) (hpE : p + 1 ≤ E) (hdE : d ≤ E) (hE2 : 2 ≤ E) (hq : 2 * q ≤ E)
    (bkN : |kapN d| ≤ 2 ^ E) (bkD : |kapD d| ≤ 2 ^ E) (hcA0 : 0 ≤ capA) (hca0 : 0 ≤ capa) (bcA : capA ≤ 2 ^ E)
    (bca : capa ≤ 2 ^ E) (hm : m < 2 ^ ℓa) (hka : 4 + 2 * ((d + 1) * (m + 1)) < 2 ^ ℓa)
    (hda : d * d + d < 2 ^ ℓa) (hℓ : 64 * E + 16 < ℓ) :
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xfrLoop L B P u a0 n0) σ (N * (frKb d m E + 2) + 4) (fun σ' =>
      FrLoopOut P a0 capa (frLoop p q capA capa (frAl A b) (fun i => 2 ^ (p + 1) * frBe A b i)
        (fun i => 2 ^ (2 * p) * (frAl A b i ⬝ᵥ frAl A b i)) N A0 x0) σ' ∧ σ'.draws = σ.draws ∧
      FrameA (frlS P u) (frlN B n0) (frlA B a0) σ σ') := by
  set r := frLoop p q capA capa (frAl A b) (fun i => 2 ^ (p + 1) * frBe A b i)
    (fun i => 2 ^ (2 * p) * (frAl A b i ⬝ᵥ frAl A b i)) with hr
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by simp only [abs_zero]; positivity
  have h1 : |(1 : ℝ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  have h2 : |(2 : ℝ)| < 2 ^ ℓ := by
    rw [abs_two]
    have := pow_lt_pow_right₀ (show (1 : ℝ) < 2 by norm_num) (show 1 < ℓ by omega)
    simpa using this
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  have hE' := hE
  obtain ⟨-, -, -, -, z, -, -, -⟩ := hE'
  -- the fixed data along the loop
  have env : ∀ σ', FrameA (frlS P u) (frlN B n0) (frlA B a0) σ σ' →
      FrEnv B m p P u n0 σ' ∧ UpdEnv u p q 1 capA capa σ' := fun σ' hF =>
    ⟨hE.frame hF (fun y h => by simp only [frlS] at h; omega) (fun j h => by simp only [frlN] at h; omega),
      hU.frame hF (fun y h => by simp only [frlS] at h; omega)⟩
  have mR : ∀ σa σb : Env d, FrameA (frRS P u) (frRN B n0) (frRA B a0) σa σb →
      FrameA (frlS P u) (frlN B n0) (frlA B a0) σa σb := fun σa σb hF =>
    hF.mono (fun y h => by simp only [frRS] at h; simp only [frlS]; omega)
      (fun j h => by simp only [frRN] at h; simp only [frlN]; omega)
      (fun b k h => by simp only [frRA] at h; simp only [frlA]; omega)
  have mU : ∀ σa σb : Env d, FrameA (fun y => u + 13 ≤ y) (fun j => n0 ≤ j ∧ j < n0 + 4)
      (fun b k => a0 ≤ b ∧ b < a0 + 6 ∧ b ≠ a0 + 2 ∧ k < d * d) σa σb →
      FrameA (frlS P u) (frlN B n0) (frlA B a0) σa σb := fun σa σb hF =>
    hF.mono (fun y h => by simp only [frlS]; omega) (fun j h => by simp only [frlN]; omega)
      (fun b k h => by simp only [frlA]; omega)
  have mS : ∀ σa σb : Env d, FrameA (fun y => y = P + 8) (fun j => j = n0 + 7) (fun _ _ => False) σa σb →
      FrameA (frlS P u) (frlN B n0) (frlA B a0) σa σb := fun σa σb hF =>
    hF.mono (fun y h => by simp only [frlS]; omega) (fun j h => by simp only [frlN]; omega) (fun _ _ h => h.elim)
  -- the turn
  have hbody : ∀ t σ', FrInv B P u a0 n0 N r capA capa A0 x0 σ t σ' →
      σ'.nat (n0 + 6) < σ'.nat (n0 + 7) →
      XRunsB L (ctxOf w n m A b) ℓa ℓ (xfrBody L B P u a0 n0) σ' (frKb d m E)
        (FrInv B P u a0 n0 N r capA capa A0 x0 σ (t + 1)) := by
    intro t σ' hJ hlt
    obtain ⟨d', F', -, -, hc⟩ := hJ
    rcases hc with ⟨s8, n7, n6, A', a', ⟨mA, ma, bA', ba'⟩, hl⟩ | ⟨-, n7, -⟩ | ⟨-, n7, -⟩
    rotate_left
    · omega
    · omega
    obtain ⟨k, hk⟩ : ∃ k, N - t = k + 1 := ⟨N - t - 1, by omega⟩
    rw [hk] at hl
    obtain ⟨hE', -⟩ := env σ' F'
    have ba2 : ∀ k, |a' k| ≤ 2 ^ E := fun k => (ba' k).trans bca
    unfold frKb
    refine XV.seq (K₂ := 200 * (E + 1) ^ 2 + 8)
      (XV.frRows hL (F := E) (by omega) hS ha0 (by omega) hn0 hN hrd hrm hE' ma ba2 hMF hpE hdE hE2 hm hka hda
        (by omega)) fun σ1 ⟨o1, d1, F1⟩ => ?_
    have G1 := F'.trans (mR σ' σ1 F1)
    have D1 : σ1.draws = σ.draws := d1.trans d'
    obtain ⟨hE1, hU1⟩ := env σ1 G1
    have hE1' := hE1
    obtain ⟨hσd1, -, -, n41, z1, o11, -, -⟩ := hE1'
    have n6' : σ1.nat (n0 + 6) = t := by rw [F1.1 _ (by simp only [frRN]; omega), n6]
    have n7' : σ1.nat (n0 + 7) = N := by rw [F1.1 _ (by simp only [frRN]; omega), n7]
    have s8' : σ1.sc (P + 8) = 0 := by rw [F1.2.1 _ (by simp only [frRS]; omega), s8]
    have mA1 : ∀ i k : Fin d, σ1.arr a0 (d * i + k) = A' i k := fun i k => by
      rw [F1.2.2.1 _ _ (by simp only [frRA]; omega), mA]
    have ma1 : ∀ k : Fin d, σ1.arr (a0 + 1) k = a' k := fun k => by
      rw [F1.2.2.1 _ _ (by simp only [frRA]; omega), ma]
    have hT : frTest A b p a' = frT (frAl A b) (fun i => 2 ^ (p + 1) * frBe A b i)
        (fun i => 2 ^ (2 * p) * (frAl A b i ⬝ᵥ frAl A b i)) a' := rfl
    unfold FrRowsOut at o1
    rw [hT] at o1
    cases hf : (List.finRange m).find? (frT (frAl A b) (fun i => 2 ^ (p + 1) * frBe A b i)
        (fun i => 2 ^ (2 * p) * (frAl A b i ⬝ᵥ frAl A b i)) a') with
    | none =>
      rw [hf] at o1
      obtain ⟨u2, -⟩ := hU1
      refine XV.mono (XV.ifS_t hL (by omega) (by omega) (by rw [o1]; exact h0) (by rw [o11]; exact h1)
        (by rw [o1, o11]; norm_num) (XV.stop hL (w := 2) (by omega) (by omega) (by omega) (by omega) z1 u2 h2))
        (by omega) fun σ2 ⟨s2, m2, d2, F2⟩ => ?_
      unfold FrInv
      refine ⟨d2.trans D1, G1.trans (mS σ1 σ2 F2), by rw [F2.1 _ (by omega), n6']; omega, by rw [m2]; omega,
        Or.inr (Or.inr ⟨s2, m2, a', hl.trans (frLoop_ret hf), fun k => ?_, ba'⟩)⟩
      rw [F2.2.2.1 _ _ (fun h => h), ma1]
    | some i =>
      rw [hf] at o1
      obtain ⟨f1, c1, aa1⟩ := o1
      have hnf : ¬ σ1.sc (P + 7) < σ1.sc (u + 1) := by rw [f1, o11]; exact lt_irrefl 1
      have baa : |((frAl A b i ⬝ᵥ frAl A b i : ℤ) : ℝ)| < 2 ^ ℓ := by
        have bal : ∀ k, |frAl A b i k| ≤ 2 ^ E := fun k => ((frAl_le A b i).2.1 k).trans hMF
        exact XV.abs_int_lt ((abs_dot_le' hdE bal bal).trans_lt (pow_lt_pow_right₀ (by norm_num) (by omega)))
      by_cases hz : (frAl A b i ⬝ᵥ frAl A b i) = 0
      · -- `α_i·α_i = 0`: fail
        have hnn : ¬ σ1.sc u < σ1.sc (P + 2) := by rw [z1, aa1, hz]; simp
        refine XV.mono (XV.ifS_f hL (by omega) (by omega) (by rw [f1]; exact h1) (by rw [o11]; exact h1) hnf
          (XV.ifS_f hL (by omega) (by omega) (by rw [z1]; exact h0) (by rw [aa1]; exact baa) hnn
          (XV.stop hL (w := 1) (by omega) (by omega) (by omega) (by omega) z1 o11 h1))) (by omega)
          fun σ2 ⟨s2, m2, d2, F2⟩ => ?_
        unfold FrInv
        refine ⟨d2.trans D1, G1.trans (mS σ1 σ2 F2), by rw [F2.1 _ (by omega), n6']; omega, by rw [m2]; omega,
          Or.inr (Or.inl ⟨s2, m2, hl.trans (frLoop_nn0 hf (by simp [hz]))⟩)⟩
      · have hpos : 0 < frAl A b i ⬝ᵥ frAl A b i := lt_of_le_of_ne (dot_self_nonneg' _) (Ne.symm hz)
        have hnn0 : (2 : ℤ) ^ (2 * p) * (frAl A b i ⬝ᵥ frAl A b i) ≠ 0 := mul_ne_zero (by positivity) hz
        have hnn : σ1.sc u < σ1.sc (P + 2) := by rw [z1, aa1]; exact_mod_cast hpos
        obtain ⟨e2, e4, eK1, eQ2, eP, eQ, ed1, ekN, ekD, ecA, eca⟩ := hU1
        refine XV.mono (XV.ifS_f hL (by omega) (by omega) (by rw [f1]; exact h1) (by rw [o11]; exact h1) hnf
          (XV.ifS_t hL (by omega) (by omega) (by rw [z1]; exact h0) (by rw [aa1]; exact baa) hnn
          (XV.seq (K₂ := 1 + 2)
          (XV.upd (u := u) (a0 := a0) (n0 := n0) (nd := B.rd) (none := n0 + 4) (E := E) (p := p) (q := q) (j := 1)
            (A := A') (a := a') (c := frAl A b i) (capA := capA) (capa := capa) hL
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) z1 o11 e2 e4 eK1
            eQ2 eP eQ ed1 ekN ekD ecA eca hσd1 n41 mA1 ma1 c1 (fun i k => (bA' i k).trans bcA) ba2
            (fun k => ((frAl_le A b i).2.1 k).trans hMF) hdE (by omega) (by omega) hq bkN bkD hcA0 hca0 bcA bca hℓ)
          fun σ3 ⟨u3, d3, F3⟩ => ?_))) (by omega) fun _ h => h
        have G3 := G1.trans (mU σ1 σ3 F3)
        have D3 : σ3.draws = σ.draws := d3.trans D1
        have z3 : σ3.sc u = 0 := by rw [F3.2.1 _ (by omega), z1]
        have o3 : σ3.sc (u + 1) = 1 := by rw [F3.2.1 _ (by omega), o11]
        have n63 : σ3.nat (n0 + 6) = t := by rw [F3.1 _ (by omega), n6']
        have n73 : σ3.nat (n0 + 7) = N := by rw [F3.1 _ (by omega), n7']
        have n43 : σ3.nat (n0 + 4) = 1 := by rw [F3.1 _ (by omega), n41]
        have s83 : σ3.sc (P + 8) = 0 := by rw [F3.2.1 _ (by omega), s8']
        cases hu : ellUpd p q 1 capA capa A' a' (frAl A b i) with
        | none =>
          rw [hu] at u3
          have u3' : σ3.sc (u + 13) = 1 := u3
          refine XV.mono (XV.ifS_t hL (by omega) (by omega) (by rw [z3]; exact h0) (by rw [u3']; exact h1)
            (by rw [z3, u3']; norm_num) (XV.stop hL (w := 1) (by omega) (by omega) (by omega) (by omega) z3 o3 h1))
            (by omega) fun σ4 ⟨s4, m4, d4, F4⟩ => ?_
          unfold FrInv
          refine ⟨d4.trans D3, G3.trans (mS σ3 σ4 F4), by rw [F4.1 _ (by omega), n63]; omega, by rw [m4]; omega,
            Or.inr (Or.inl ⟨s4, m4, hl.trans (frLoop_fail hf hnn0 hu)⟩)⟩
        | some r' =>
          obtain ⟨A'', a''⟩ := r'
          rw [hu] at u3
          obtain ⟨u13, uA, ua⟩ := u3
          obtain ⟨cA', ca'⟩ := ellUpd_caps hu
          refine XV.mono (XV.ifS_f hL (by omega) (by omega) (by rw [z3]; exact h0) (by rw [u13]; exact h0)
            (by rw [z3, u13]; exact lt_irrefl 0) (XV.nadd hL (i := n0 + 6) (a := n0 + 6) (b := n0 + 4) (by omega)
            (by omega) (by omega) (by rw [n63]; omega) (by rw [n43]; exact hsa))) (by omega) fun σ4 e4 => ?_
          subst e4
          unfold FrInv
          refine ⟨by simp [D3], G3.setNat (by simp only [frlN]; omega) _, by simp [n63, n43]; omega,
            by simp [n73], Or.inl ⟨by simp [s83], by simp [n73], by simp [n63, n43], A'', a'',
              ⟨fun i k => by simp [uA], fun k => by simp [ua], cA', ca'⟩, ?_⟩⟩
          rw [hl, show N - (t + 1) = k by omega]; exact frLoop_next hf hnn0 hu
  -- the loop
  have hb : ∀ t σ', FrInv B P u a0 n0 N r capA capa A0 x0 σ t σ' →
      σ'.nat (n0 + 6) < 2 ^ ℓa ∧ σ'.nat (n0 + 7) < 2 ^ ℓa := fun t σ' h => by
    obtain ⟨-, -, i6, i7, -⟩ := h
    omega
  have hlt : ∀ t σ', FrInv B P u a0 n0 N r capA capa A0 x0 σ t σ' →
      σ'.nat (n0 + 6) < σ'.nat (n0 + 7) → t < N := fun t σ' h hl => by
    obtain ⟨-, -, -, -, hc⟩ := h
    rcases hc with ⟨-, n7, n6, -⟩ | ⟨-, n7, -⟩ | ⟨-, n7, -⟩ <;> omega
  refine XV.mono (Q := fun σ' => ∃ t', FrInv B P u a0 n0 N r capA capa A0 x0 σ t' σ' ∧
      ¬ σ'.nat (n0 + 6) < σ'.nat (n0 + 7)) (XV.seq (K₂ := 1 + ((N - 0) * (frKb d m E + 2) + 2))
    (XV.nconst hL (i := n0 + 6) (by omega) 0 (by positivity)) fun σa ea => ?_)
    (by simp only [Nat.sub_zero]; omega) ?_
  · subst ea
    have za : (σ.setNat (n0 + 6) 0).sc u = 0 := by simp [z]
    refine XV.seq (XV.sop2 hL (x := P + 8) (a := u) (b := u) (by omega) (by omega) (by omega) .add
      (by intro h; cases h) (by rw [za]; exact h0) (by rw [za]; exact h0)
      (by simp only [RealRAM.Op2.eval, za, add_zero]; exact h0)) fun σb eb => ?_
    subst eb
    refine XV.whileN hL (by omega) (by omega) (FrInv B P u a0 n0 N r capA capa A0 x0 σ) N
      (frKb d m E) hb hlt hbody 0 _ ?_
    unfold FrInv
    refine ⟨by simp, ((FrameA.refl (frlS P u) (frlN B n0) (frlA B a0) σ).setNat (by simp only [frlN]; omega) 0).setSc
      (x := P + 8) (Or.inr (Or.inr (Or.inl rfl))) _, by simp, by simp [hσN],
      Or.inl ⟨by simp [RealRAM.Op2.eval, z], by simp [hσN],
      by simp, A0, x0, ?_, by simp⟩⟩
    obtain ⟨mA, ma, bA, ba⟩ := hSt
    exact ⟨fun i k => by simp [mA], fun k => by simp [ma], bA, ba⟩
  · rintro σ' ⟨t', hJ, hnl⟩
    obtain ⟨d', F', i6, -, hc⟩ := hJ
    refine ⟨?_, d', F'⟩
    rcases hc with ⟨s8, n7, n6, A', a', -, hl⟩ | ⟨s8, -, hl⟩ | ⟨s8, -, x, hl, mx, bx⟩
    · rw [show N - t' = 0 by omega] at hl
      exact Or.inr ⟨Or.inl s8, by rw [hl]; rfl⟩
    · exact Or.inr ⟨Or.inr s8, hl⟩
    · exact Or.inl ⟨s8, x, hl, mx, bx⟩

end AdversarialBco.Bit.Transfer
