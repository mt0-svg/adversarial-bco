/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XFrameE0

@[expose] public section

/-!
# The row test of ELL-F on the machine

One test of Procedure ELL-F (`frLoop`, Bit/RoutQ.lean) at the point `â`: the cleared input rows one by one (`xinRow`
with `D = 2^{p+1}`, so the slot `u + 22` gets `B_i = 2^{p+1} β_i`), `v = B_i - 2 α_i·â`, `v²`, `α_i·α_i` and
`nn_i = 2^{2p} α_i·α_i`; the first row with `v < 0` or `v² < nn_i` sets the flag `P + 7`, copies `α_i` into the array
`a0 + 2` and `α_i·α_i` into the slot `P + 2`. The layout is that of ELL-R (`P = o + 3`, `u = o + 15`, `n0 = rE + 1`,
`a0 = aW + 2`); the row goes into the array `aW + 1`, the registers `n0 + 47, n0 + 48, n0 + 49` are `xinRow`'s.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-- The prologue block as an `EllBlk`, for the routines of ELL-R that read only `rd`, `o`, `rE` and `aW`. -/
def frEB (B : PrBlk) : EllBlk :=
  { rd := B.rd, rm := B.rm, sl := 0, sDf := 0, sRn := 0, sRd := 0, srn := 0, srd := 0, sen := 0, sed := 0,
    aH := 0, ag := 0, aP := 0, af := 0, o := B.o, rE := B.rE, aW := B.aW }

/-! ## The program -/

/-- A failing row: `α_i` into the cut `a0 + 2`, the flag `P + 7 := 1`, `P + 2 := α_i·α_i`, the end of the rows. -/
def xfrFound (L : Layout) (B : PrBlk) (P u a0 n0 : ℕ) : XCmd :=
  .seq (xcopy L (frEB B) u (B.aW + 1) (a0 + 2) n0 (n0 + 4))
  (.seq (xset L (P + 7) (u + 1) u) (.seq (xset L (P + 2) (u + 16) u) (.prim (.frag (.nconst (n0 + 5) 0)))))

/-- One row: the cleared row, `u + 13 = α·â`, `u + 14 = v`, `u + 15 = v²`, `u + 16 = α·α`, `u + 17 = nn`, the test. -/
def xfrRowBody (L : Layout) (B : PrBlk) (P u a0 n0 : ℕ) : XCmd :=
  .seq (xinRow L (u + 18) (u + 19) (u + 20) (u + 21) (u + 22) (P + 4) (B.aW + 1) (n0 + 47) (n0 + 48) (n0 + 49) B.rd
    (n0 + 14) B.rE (n0 + 4))
  (.seq (xdot L u (u + 13) (u + 24) (B.aW + 1) (a0 + 1) (n0 + 1) (n0 + 2) B.rd (n0 + 4))
  (.seq ((IE.op .sub (.sc (u + 22)) (.op .add (.sc (u + 13)) (.sc (u + 13)))).code L u (u + 14) (u + 24))
  (.seq ((IE.op .mul (.sc (u + 14)) (.sc (u + 14))).code L u (u + 15) (u + 24))
  (.seq (xdot L u (u + 16) (u + 24) (B.aW + 1) (B.aW + 1) (n0 + 1) (n0 + 2) B.rd (n0 + 4))
  (.seq ((ieMul (P + 5) (u + 16)).code L u (u + 17) (u + 24))
  (xifS L (u + 14) u (xfrFound L B P u a0 n0)
    (xifS L (u + 15) (u + 17) (xfrFound L B P u a0 n0) (.prim (.frag (.nadd B.rE B.rE (n0 + 4)))))))))))

/-- The rows: the flag to `0`, `n0 + 5 := m`, the row index `rE := 0`, the loop. -/
def xfrRows (L : Layout) (B : PrBlk) (P u a0 n0 : ℕ) : XCmd :=
  .seq (xset L (P + 7) u u)
  (.seq (.prim (.frag (.nconst (n0 + 5) 0)))
  (.seq (.prim (.frag (.nadd (n0 + 5) (n0 + 5) B.rm)))
  (.seq (.prim (.frag (.nconst B.rE 0)))
  (.whileN B.rE (n0 + 5) (xfrRowBody L B P u a0 n0)))))

/-! ## The data -/

/-- The test of ELL-F on the cleared row `i` at the point `a`: `B_i - 2 α_i·a < 0` or `(B_i - 2 α_i·a)² < nn_i`,
`B_i = 2^{p+1} β_i`, `nn_i = 2^{2p} α_i·α_i`. -/
def frTest {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (p : ℕ) (a : Fin d → ℤ) (i : Fin m) : Bool :=
  decide (2 ^ (p + 1) * frBe A b i - 2 * (frAl A b i ⬝ᵥ a) < 0 ∨
    (2 ^ (p + 1) * frBe A b i - 2 * (frAl A b i ⬝ᵥ a)) ^ 2 < 2 ^ (2 * p) * (frAl A b i ⬝ᵥ frAl A b i))

/-- The outcome of the rows: the first failing row `i` gives the flag `1`, `α_i` in the array `a0 + 2` and
`α_i·α_i` in the slot `P + 2`; no failing row, the flag `0`. -/
def FrRowsOut {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (p : ℕ) (a : Fin d → ℤ) (P a0 : ℕ)
    (σ : Env d) : Prop :=
  match (List.finRange m).find? (frTest A b p a) with
  | some i => σ.sc (P + 7) = 1 ∧ (∀ k : Fin d, σ.arr (a0 + 2) k = frAl A b i k) ∧
      σ.sc (P + 2) = ((frAl A b i ⬝ᵥ frAl A b i : ℤ) : ℝ)
  | none => σ.sc (P + 7) = 0

/-- The fixed data of the rows: `d`, `m`, `d + 1`, `1` in registers, `0, 1` in `u, u + 1`, `2^{p+1}`, `2^{2p}` in
`P + 4`, `P + 5`. -/
def FrEnv (B : PrBlk) (m p P u n0 : ℕ) (σ : Env d) : Prop :=
  σ.nat B.rd = d ∧ σ.nat B.rm = m ∧ σ.nat (n0 + 14) = d + 1 ∧ σ.nat (n0 + 4) = 1 ∧ σ.sc u = 0 ∧
    σ.sc (u + 1) = 1 ∧ σ.sc (P + 4) = ((2 ^ (p + 1) : ℤ) : ℝ) ∧ σ.sc (P + 5) = ((2 ^ (2 * p) : ℤ) : ℝ)

theorem FrEnv.frame {B : PrBlk} {m p P u n0 : ℕ} {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop} {σ σ' : Env d}
    (h : FrEnv B m p P u n0 σ) (hF : FrameA S N Ar σ σ')
    (hS : ∀ y, S y → y ≠ u ∧ y ≠ u + 1 ∧ y ≠ P + 4 ∧ y ≠ P + 5)
    (hN : ∀ j, N j → j ≠ B.rd ∧ j ≠ B.rm ∧ j ≠ n0 + 14 ∧ j ≠ n0 + 4) : FrEnv B m p P u n0 σ' := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := h
  exact ⟨by rw [hF.1 _ fun h => (hN _ h).1 rfl, e1], by rw [hF.1 _ fun h => (hN _ h).2.1 rfl, e2],
    by rw [hF.1 _ fun h => (hN _ h).2.2.1 rfl, e3], by rw [hF.1 _ fun h => (hN _ h).2.2.2 rfl, e4],
    by rw [hF.2.1 _ fun h => (hS _ h).1 rfl, e5], by rw [hF.2.1 _ fun h => (hS _ h).2.1 rfl, e6],
    by rw [hF.2.1 _ fun h => (hS _ h).2.2.1 rfl, e7], by rw [hF.2.1 _ fun h => (hS _ h).2.2.2 rfl, e8]⟩

/-- The slots the rows change. -/
abbrev frRS (P u y : ℕ) : Prop := y = P + 2 ∨ y = P + 7 ∨ u + 13 ≤ y

/-- The registers the rows change. -/
abbrev frRN (B : PrBlk) (n0 j : ℕ) : Prop :=
  j = B.rE ∨ j = n0 + 1 ∨ j = n0 + 2 ∨ j = n0 + 5 ∨ (n0 + 47 ≤ j ∧ j ≤ n0 + 49)

/-- The arrays the rows change. -/
abbrev frRA (B : PrBlk) (a0 b _k : ℕ) : Prop := b = B.aW + 1 ∨ b = a0 + 2

/-- The units of one row. -/
def frRowK (d : ℕ) : ℕ := 46 * d + 59

/-! ## A failing row -/

set_option maxHeartbeats 2000000 in
/-- The rule of `xfrFound`. -/
theorem XV.frFound {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : PrBlk}
    {P u a0 n0 F : ℕ} {x : Fin d → ℤ} {s : ℤ} (hPu : P + 8 ≤ u) (hS : u + 27 ≤ L.NS) (ha0 : B.aW + 2 ≤ a0)
    (hA : a0 + 3 ≤ L.NA) (hn0 : B.rE + 1 ≤ n0) (hN : n0 + 6 ≤ L.NN) (hrd : B.rd < B.rE)
    (hz : σ.sc u = 0) (h1 : σ.sc (u + 1) = 1) (hσd : σ.nat B.rd = d) (hσ1 : σ.nat (n0 + 4) = 1)
    (hx : ∀ k : Fin d, σ.arr (B.aW + 1) k = x k) (bx : ∀ k, |x k| ≤ 2 ^ F) (hF : F < ℓ)
    (hs : σ.sc (u + 16) = s) (bs : |(s : ℝ)| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xfrFound L B P u a0 n0) σ (d * 8 + 7) (fun σ' =>
      σ'.sc (P + 7) = 1 ∧ (∀ k : Fin d, σ'.arr (a0 + 2) k = x k) ∧ σ'.sc (P + 2) = s ∧ σ'.nat (n0 + 5) = 0 ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => y = P + 2 ∨ y = P + 7 ∨ u + 24 ≤ y) (fun j => j = n0 + 1 ∨ j = n0 + 2 ∨ j = n0 + 5)
        (fun b c => b = a0 + 2 ∧ c < d) σ σ') := by
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by rw [abs_zero]; positivity
  have h1' : |(1 : ℝ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  refine XV.mono (K := (1 + (d * (2 + 6) + 3)) + (1 + (1 + 1))) ?_ (by ring_nf; omega) (fun _ h => h)
  refine XV.seq (XV.copy (B := frEB B) (E := F) (x := x) hL (u := u) (src := B.aW + 1) (dst := a0 + 2) (n0 := n0)
    (one := n0 + 4) (by omega) (by omega) (by omega) (by omega) (by omega) (show B.rd < L.NN by omega)
    (by omega) (show B.rd < n0 + 1 ∨ n0 + 3 ≤ B.rd by omega) (by omega) (show B.rd ≠ n0 + 4 by omega) hz hσd hσ1
    hx bx hF) fun σ1 ⟨m1, d1, F1⟩ => ?_
  have z1 : σ1.sc u = 0 := by rw [F1.2.1 _ (by omega), hz]
  have o1 : σ1.sc (u + 1) = 1 := by rw [F1.2.1 _ (by omega), h1]
  have s1 : σ1.sc (u + 16) = s := by rw [F1.2.1 _ (by omega), hs]
  refine XV.seq (XV.cpy hL (x := P + 7) (y := u + 1) (z := u) (by omega) (by omega) (by omega) z1
    (by rw [o1]; exact h1')) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.cpy hL (x := P + 2) (y := u + 16) (z := u) (by omega) (by omega) (by omega)
    (by rw [sc_setSc_ne _ (by omega), z1]) (by rw [sc_setSc_ne _ (by omega), s1]; exact bs)) fun σ3 e3 => ?_
  subst e3
  refine XV.mono (XV.nconst hL (i := n0 + 5) (by omega) 0 (by positivity)) le_rfl fun σ4 e4 => ?_
  subst e4
  refine ⟨by simp [o1], fun k => by simpa using m1 k, by simp [s1, show u + 16 ≠ P + 7 by omega],
    by simp, by simp [d1], ?_⟩
  have G1 : FrameA (fun y => y = P + 2 ∨ y = P + 7 ∨ u + 24 ≤ y) (fun j => j = n0 + 1 ∨ j = n0 + 2 ∨ j = n0 + 5)
      (fun b c => b = a0 + 2 ∧ c < d) σ σ1 :=
    F1.mono (fun y h => Or.inr (Or.inr h)) (fun j h => by omega) (fun b c h => h)
  exact ((G1.setSc (x := P + 7) (Or.inr (Or.inl rfl)) _).setSc (x := P + 2) (Or.inl rfl) _).setNat
    (i := n0 + 5) (Or.inr (Or.inr rfl)) _

/-! ## The rows on the machine -/

theorem frV_le {x y : ℤ} {F : ℕ} (hF : 2 ≤ F) (hx : |x| ≤ 2 ^ (2 * F)) (hy : |y| ≤ 2 ^ (3 * F)) :
    |x - (y + y)| ≤ 2 ^ (4 * F) :=
  abs_le_pow_mono (abs_sub_le_pow (abs_le_pow_mono hx (by omega)) (abs_add_le_pow hy hy)) (by omega)

set_option maxHeartbeats 16000000 in
/-- **The rows of ELL-F on the machine**: the cleared input rows one by one, up to the first one failing at the point
`a` (array `a0 + 1`): `FrRowsOut`. -/
theorem XV.frRows {L : Layout} {w : BitRAM.World d} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : PrBlk} {p P u a0 n0 F : ℕ} {a : Fin d → ℤ}
    (hPu : P + 8 ≤ u) (hS : u + 60 ≤ L.NS) (ha0 : B.aW + 2 ≤ a0) (hA : a0 + 3 ≤ L.NA)
    (hn0 : B.rE + 1 ≤ n0) (hN : n0 + 50 ≤ L.NN) (hrd : B.rd < B.rE) (hrm : B.rm < B.rE)
    (hE : FrEnv B m p P u n0 σ) (ha : ∀ k : Fin d, σ.arr (a0 + 1) k = a k) (ba : ∀ k, |a k| ≤ 2 ^ F)
    (hMF : (frMhat A b : ℤ) ^ (d + 1) ≤ 2 ^ F) (hpF : p + 1 ≤ F) (hdF : d ≤ F) (hF : 2 ≤ F)
    (hm : m < 2 ^ ℓa) (hka : 4 + 2 * ((d + 1) * (m + 1)) < 2 ^ ℓa) (hda : d * d + d < 2 ^ ℓa)
    (hℓ : 8 * F + 4 < ℓ) :
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xfrRows L B P u a0 n0) σ (4 + (m * (frRowK d + 2) + 2)) (fun σ' =>
      FrRowsOut A b p a P a0 σ' ∧ σ'.draws = σ.draws ∧ FrameA (frRS P u) (frRN B n0) (frRA B a0) σ σ') := by
  have hE' := hE
  obtain ⟨hσd, hσm, -, hσ1, z0, -, -, -⟩ := hE'
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by simp only [abs_zero]; positivity
  have hEw : ∀ σ', FrameA (frRS P u) (frRN B n0) (frRA B a0) σ σ' → FrEnv B m p P u n0 σ' := fun σ' hF =>
    hE.frame hF (fun y h => by simp only [frRS] at h; omega) (fun j h => by simp only [frRN] at h; omega)
  have haw : ∀ σ', FrameA (frRS P u) (frRN B n0) (frRA B a0) σ σ' → ∀ k : Fin d, σ'.arr (a0 + 1) k = a k :=
    fun σ' hF k => by rw [hF.2.2.1 _ _ (fun h => by simp only [frRA] at h; omega), ha]
  -- bounds
  have hM1 : (1 : ℤ) ≤ frMhat A b := by exact_mod_cast (frMhat_le A b).1
  have bal : ∀ i : Fin m, ∀ k, |frAl A b i k| ≤ 2 ^ F := fun i k => ((frAl_le A b i).2.1 k).trans hMF
  have bbe : ∀ i : Fin m, |frBe A b i * 2 ^ (p + 1)| ≤ 2 ^ (2 * F) := fun i => by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ (p + 1)), two_mul, pow_add (2 : ℤ) F F]
    exact mul_le_mul (((frAl_le A b i).2.2).trans hMF) (pow_le_pow_right₀ (by norm_num) hpF) (by positivity)
      (by positivity)
  have hrowb : (frMhat A b : ℤ) ^ (d + 2) * 2 ^ (p + 1) < 2 ^ ℓ := by
    have e2 : (frMhat A b : ℤ) ≤ (frMhat A b : ℤ) ^ (d + 1) := le_self_pow₀ hM1 (by omega)
    calc (frMhat A b : ℤ) ^ (d + 2) * 2 ^ (p + 1) ≤ 2 ^ F * 2 ^ F * 2 ^ F := by
          rw [pow_succ]
          exact mul_le_mul (mul_le_mul hMF (e2.trans hMF) (by positivity) (by positivity))
            (pow_le_pow_right₀ (by norm_num) hpF) (by positivity) (by positivity)
      _ = 2 ^ (F + F + F) := by rw [← pow_add, ← pow_add]
      _ < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) (by omega)
  have hdl : d * 2 ^ (2 * F) < 2 ^ ℓ := d_mul_pow_lt hdF (by omega)
  -- the invariant
  let q : Fin m → Bool := frTest A b p a
  let J : ℕ → Env d → Prop := fun t σ' => σ'.draws = σ.draws ∧ FrameA (frRS P u) (frRN B n0) (frRA B a0) σ σ' ∧
    σ'.nat B.rE ≤ m ∧
    ((σ'.sc (P + 7) = 0 ∧ σ'.nat (n0 + 5) = m ∧ σ'.nat B.rE = t ∧ ∀ i : Fin m, i.1 < t → q i = false) ∨
      (σ'.sc (P + 7) = 1 ∧ σ'.nat (n0 + 5) = 0 ∧ FrRowsOut A b p a P a0 σ'))
  -- the start
  refine XV.mono (K := 1 + (1 + (1 + (1 + ((m - 0) * (frRowK d + 2) + 2))))) ?_ (by rw [Nat.sub_zero]; omega)
    (fun _ h => h)
  refine XV.seq (XV.setZ hL (x := P + 7) (z := u) (by omega) (by omega) z0) fun σ1 ⟨s1, d1, F1⟩ => ?_
  refine XV.seq (XV.nconstA hL (i := n0 + 5) (by omega) 0 (by positivity)) fun σ2 ⟨n2, d2, F2⟩ => ?_
  refine XV.seq (XV.naddA hL (i := n0 + 5) (a := n0 + 5) (b := B.rm) (va := 0) (vb := m) (by omega) (by omega) (by omega) n2
    (by rw [F2.1 _ (by omega), F1.1 _ id, hσm]) (by omega)) fun σ3 ⟨n3, d3, F3⟩ => ?_
  refine XV.seq (XV.nconstA hL (i := B.rE) (by omega) 0 (by positivity)) fun σ4 ⟨n4, d4, F4⟩ => ?_
  have G4 : FrameA (frRS P u) (frRN B n0) (frRA B a0) σ σ4 :=
    ((F1.mono (fun y h => by simp only [frRS]; omega) (fun _ h => h.elim) (fun _ _ h => h.elim)).trans
      (F2.mono (fun _ h => h.elim) (fun j h => by simp only [frRN]; omega) (fun _ _ h => h.elim))).trans
      ((F3.mono (fun _ h => h.elim) (fun j h => by simp only [frRN]; omega) (fun _ _ h => h.elim)).trans
      (F4.mono (fun _ h => h.elim) (fun j h => by simp only [frRN]; omega) (fun _ _ h => h.elim)))
  have J0 : J 0 σ4 := by
    refine ⟨by rw [d4, d3, d2, d1], G4, by rw [n4]; omega, Or.inl ⟨?_, ?_, n4, fun i h => absurd h (by omega)⟩⟩
    · rw [F4.2.1 _ not_false, F3.2.1 _ not_false, F2.2.1 _ not_false, s1]
    · rw [F4.1 _ (by omega), n3]; simp
  -- the loop
  refine XV.mono (XV.whileN hL (i := B.rE) (j := n0 + 5) (by omega) (by omega) J m (frRowK d) ?_ ?_ ?_
    0 σ4 J0) le_rfl fun σ' ⟨t', hJ, hc⟩ => ?_
  · rintro t σ' ⟨-, -, hle, hcase⟩
    rcases hcase with ⟨-, hn, -, -⟩ | ⟨-, hn, -⟩
    · exact ⟨by omega, by rw [hn]; exact hm⟩
    · exact ⟨by omega, by rw [hn]; positivity⟩
  · rintro t σ' ⟨-, -, -, hcase⟩ hlt
    rcases hcase with ⟨-, hn, ht, -⟩ | ⟨-, hn, -⟩
    · omega
    · omega
  · rintro t σt ⟨dt, Ft, -, hcase⟩ hlt
    obtain ⟨q0, qm, qt, qp⟩ : σt.sc (P + 7) = 0 ∧ σt.nat (n0 + 5) = m ∧ σt.nat B.rE = t ∧
        ∀ i : Fin m, i.1 < t → q i = false := by
      rcases hcase with h | ⟨-, hn, -⟩
      · exact h
      · omega
    have htm : t < m := by omega
    set i : Fin m := ⟨t, htm⟩ with hi
    obtain ⟨hσdt, -, hd1t, h1t, z0t, -, p4t, -⟩ := hEw σt Ft
    unfold frRowK
    refine XV.mono (K := (18 * d + 28) + ((d * 10 + 5) + (5 + (3 + ((d * 10 + 5) + (3 + (8 * d + 10)))))))
      ?_ (by omega) (fun _ h => h)
    -- the row
    refine XV.seq (XV.frRow hL (sD := u + 18) (sT := u + 19) (sN := u + 20) (sQ := u + 21) (sB := u + 22)
      (sDn := P + 4) (aRow := B.aW + 1) (nI := n0 + 47) (nT := n0 + 48) (nj := n0 + 49) (nd := B.rd)
      (nd1 := n0 + 14) (nk := B.rE) (none := n0 + 4) (k := t) (D := 2 ^ (p + 1)) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by simp; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by simp; omega) hσdt hd1t qt h1t p4t htm hka hda
      (one_le_pow₀ (by norm_num)) hrowb) fun σr ⟨hα, hβ, dr, Fr⟩ => ?_
    have FR : FrameA (frRS P u) (frRN B n0) (frRA B a0) σ σr := Ft.trans (Fr.mono
      (fun y h => by simp only [frRS]; omega) (fun j h => by simp only [frRN]; omega)
      (fun b' k h => by simp only [frRA]; omega))
    obtain ⟨hσdr, -, -, h1r, z0r, o1r, -, p5r⟩ := hEw σr FR
    have har : ∀ k : Fin d, σr.arr (a0 + 1) k = a k := haw σr FR
    -- `u + 13 = α·a`
    refine XV.seq (XV.dot (E := F) (x := frAl A b i) (y := a) hL (z := u) (r := u + 13) (t := u + 24)
      (ax := B.aW + 1) (ay := a0 + 1) (nr := n0 + 1) (nk := n0 + 2) (nd := B.rd) (none := n0 + 4) (by omega)
      (by omega) (by omega) (by omega) z0r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (nodup4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) hσdr h1r hα har (bal i) ba
      (by omega) hdl) fun σ1 ⟨s1, d1, F1⟩ => ?_
    have c1 : ∀ y, y < u + 24 → y ≠ u + 13 → σ1.sc y = σr.sc y := fun y h h' => F1.2.1 y (by omega)
    have bdot : |frAl A b i ⬝ᵥ a| ≤ 2 ^ (3 * F) :=
      (abs_dot_le' hdF (bal i) ba).trans_eq (by congr 1; ring)
    -- `u + 14 = v`
    set v : ℤ := 2 ^ (p + 1) * frBe A b i - 2 * (frAl A b i ⬝ᵥ a) with hv
    have bv : |v| ≤ 2 ^ (4 * F) := by
      have := frV_le hF (bbe i) bdot
      rwa [show frBe A b i * 2 ^ (p + 1) - ((frAl A b i ⬝ᵥ a) + (frAl A b i ⬝ᵥ a)) = v by rw [hv]; ring] at this
    refine XV.seq (XV.ieRun (E := 4 * F) (e := IE.op .sub (.sc (u + 22)) (.op .add (.sc (u + 13)) (.sc (u + 13))))
      (v := v) hL (x := u + 14) (t := u + 24) (z := u)
      (by simp only [IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega) (by omega) (by omega)
      (by simp only [IE.scr]; omega) (by rw [c1 _ (by omega) (by omega), z0r])
      (by
        simp only [IE.Leaves]
        exact ⟨⟨_, by rw [c1 _ (by omega) (by omega), hβ], abs_le_pow_mono (bbe i) (by omega)⟩,
          ⟨_, s1, abs_le_pow_mono bdot (by omega)⟩, ⟨_, s1, abs_le_pow_mono bdot (by omega)⟩⟩)
      (by simp only [IE.top, IE.mag]; omega)
      (by
        simp only [IE.eval, RealRAM.Op2.eval, c1 (u + 22) (by omega) (by omega), hβ, s1, hv]
        push_cast; ring)) fun σ2 ⟨x2, bx2, d2, P2⟩ => ?_
    have c2 : ∀ y, y < u + 24 → y ≠ u + 14 → σ2.sc y = σ1.sc y := fun y h h' => P2.2.1 y (by omega)
    -- `u + 15 = v²`
    refine XV.seq (XV.ieRun (E := 4 * F) (e := IE.op .mul (.sc (u + 14)) (.sc (u + 14))) (v := v * v) hL
      (x := u + 15) (t := u + 24) (z := u)
      (by simp only [IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega) (by omega) (by omega)
      (by simp only [IE.scr]; omega) (by rw [c2 _ (by omega) (by omega), c1 _ (by omega) (by omega), z0r])
      (by simp only [IE.Leaves]; exact ⟨⟨_, x2, bv⟩, ⟨_, x2, bv⟩⟩)
      (by simp only [IE.top, IE.mag]; omega)
      (by simp only [IE.eval, RealRAM.Op2.eval, x2]; push_cast; ring)) fun σ3 ⟨x3, bx3, d3, P3⟩ => ?_
    have c3 : ∀ y, y < u + 24 → y ≠ u + 15 → σ3.sc y = σ2.sc y := fun y h h' => P3.2.1 y (by omega)
    have ar3 : ∀ k : Fin d, σ3.arr (B.aW + 1) k = frAl A b i k := fun k => by
      rw [P3.2.2.1, P2.2.2.1, F1.2.2.1 _ _ (fun h => h.elim), hα]
    have n3 : ∀ j, j ≠ n0 + 1 → j ≠ n0 + 2 → σ3.nat j = σr.nat j := fun j h h' => by
      rw [P3.1 _ not_false, P2.1 _ not_false, F1.1 _ (by omega)]
    -- `u + 16 = α·α`
    refine XV.seq (XV.dot (E := F) (x := frAl A b i) (y := frAl A b i) hL (z := u) (r := u + 16) (t := u + 24)
      (ax := B.aW + 1) (ay := B.aW + 1) (nr := n0 + 1) (nk := n0 + 2) (nd := B.rd) (none := n0 + 4) (by omega)
      (by omega) (by omega) (by omega) (by rw [c3 _ (by omega) (by omega), c2 _ (by omega) (by omega),
        c1 _ (by omega) (by omega), z0r]) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (nodup4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
      (by rw [n3 _ (by omega) (by omega), hσdr]) (by rw [n3 _ (by omega) (by omega), h1r]) ar3 ar3 (bal i) (bal i)
      (by omega) hdl) fun σ4 ⟨s4, d4, F4⟩ => ?_
    have c4 : ∀ y, y < u + 24 → y ≠ u + 16 → σ4.sc y = σ3.sc y := fun y h h' => F4.2.1 y (by omega)
    have baa : |frAl A b i ⬝ᵥ frAl A b i| ≤ 2 ^ (3 * F) :=
      (abs_dot_le' hdF (bal i) (bal i)).trans_eq (by congr 1; ring)
    -- `u + 17 = nn`
    refine XV.seq (XV.ieRun (E := 4 * F) (e := ieMul (P + 5) (u + 16))
      (v := 2 ^ (2 * p) * (frAl A b i ⬝ᵥ frAl A b i)) hL (x := u + 17) (t := u + 24) (z := u)
      (by simp only [ieMul, IE.WF]; exact ⟨(by intro h; cases h), by omega, by omega⟩) (by omega) (by omega)
      (by simp only [ieMul, IE.scr]; omega)
      (by rw [c4 _ (by omega) (by omega), c3 _ (by omega) (by omega), c2 _ (by omega) (by omega),
        c1 _ (by omega) (by omega), z0r])
      (by
        simp only [ieMul, IE.Leaves]
        exact ⟨⟨_, by rw [c4 _ (by omega) (by omega), c3 _ (by omega) (by omega), c2 _ (by omega) (by omega),
          c1 _ (by omega) (by omega), p5r], abs_pow_le (by omega)⟩, ⟨_, s4, abs_le_pow_mono baa (by omega)⟩⟩)
      (by simp only [ieMul, IE.top, IE.mag]; omega)
      (by
        simp only [ieMul, IE.eval, RealRAM.Op2.eval, s4, c4 (P + 5) (by omega) (by omega),
          c3 (P + 5) (by omega) (by omega), c2 (P + 5) (by omega) (by omega), c1 (P + 5) (by omega) (by omega), p5r]
        push_cast; ring)) fun σ5 ⟨x5, bx5, d5, P5⟩ => ?_
    -- the values at the test
    have e14 : σ5.sc (u + 14) = (v : ℝ) := by
      rw [P5.2.1 _ (by omega), c4 _ (by omega) (by omega), c3 _ (by omega) (by omega), x2]
    have e15 : σ5.sc (u + 15) = ((v * v : ℤ) : ℝ) := by
      rw [P5.2.1 _ (by omega), c4 _ (by omega) (by omega), x3]
    have e16 : σ5.sc (u + 16) = ((frAl A b i ⬝ᵥ frAl A b i : ℤ) : ℝ) := by rw [P5.2.1 _ (by omega), s4]
    have z5 : σ5.sc u = 0 := by
      rw [P5.2.1 _ (by omega), c4 _ (by omega) (by omega), c3 _ (by omega) (by omega), c2 _ (by omega) (by omega),
        c1 _ (by omega) (by omega), z0r]
    have o5 : σ5.sc (u + 1) = 1 := by
      rw [P5.2.1 _ (by omega), c4 _ (by omega) (by omega), c3 _ (by omega) (by omega), c2 _ (by omega) (by omega),
        c1 _ (by omega) (by omega), o1r]
    have ar5 : ∀ k : Fin d, σ5.arr (B.aW + 1) k = frAl A b i k := fun k => by
      rw [P5.2.2.1, F4.2.2.1 _ _ (fun h => h.elim), ar3]
    have n5 : ∀ j, j ≠ n0 + 1 → j ≠ n0 + 2 → σ5.nat j = σr.nat j := fun j h h' => by
      rw [P5.1 _ not_false, F4.1 _ (by omega), n3 _ h h']
    have G5 : FrameA (frRS P u) (frRN B n0) (frRA B a0) σ σ5 :=
      (((FR.trans (F1.mono (fun y h => by simp only [frRS]; omega) (fun j h => by simp only [frRN]; omega)
        (fun _ _ h => h.elim))).trans (FrameA.ofP (P2.mono (fun y h => by simp only [frRS]; omega)
        (fun _ h => h.elim)))).trans ((FrameA.ofP (P3.mono (fun y h => by simp only [frRS]; omega)
        (fun _ h => h.elim))).trans (F4.mono (fun y h => by simp only [frRS]; omega)
        (fun j h => by simp only [frRN]; omega) (fun _ _ h => h.elim)))).trans
        (FrameA.ofP (P5.mono (fun y h => by simp only [frRS]; omega) (fun _ h => h.elim)))
    have rE5 : σ5.nat B.rE = t := by
      rw [n5 _ (by omega) (by omega), Fr.1 _ (by omega), qt]
    have nm5 : σ5.nat (n0 + 5) = m := by
      rw [n5 _ (by omega) (by omega), Fr.1 _ (by omega), qm]
    have b14 : |σ5.sc (u + 14)| < 2 ^ ℓ := by rw [e14]; exact_mod_cast bx2
    have b15 : |σ5.sc (u + 15)| < 2 ^ ℓ := by rw [e15]; exact_mod_cast bx3
    have b17 : |σ5.sc (u + 17)| < 2 ^ ℓ := by rw [x5]; exact_mod_cast bx5
    have b0 : |σ5.sc u| < 2 ^ ℓ := by rw [z5]; exact h0
    have bs16 : |((frAl A b i ⬝ᵥ frAl A b i : ℤ) : ℝ)| < 2 ^ ℓ :=
      XV.abs_int_lt (baa.trans_lt (pow_lt_pow_right₀ (by norm_num) (by omega)))
    have hpq : ∀ j : Fin m, j < i → q j = false := fun j hj => qp j hj
    -- a failing row
    have found : ∀ K, d * 8 + 7 ≤ K → q i = true →
        XRunsB L (ctxOf w n m A b) ℓa ℓ (xfrFound L B P u a0 n0) σ5 K (J (t + 1)) := fun K hK hq => by
      refine XV.mono (XV.frFound hL (B := B) (P := P) (u := u) (a0 := a0) (n0 := n0) (F := F) (x := frAl A b i)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hrd z5 o5
        (by rw [n5 _ (by omega) (by omega), hσdr]) (by rw [n5 _ (by omega) (by omega), h1r]) ar5 (bal i)
        (by omega) e16 bs16) hK fun σ6 ⟨f6, c6, a6, m6, d6, F6⟩ => ?_
      have G6 : FrameA (frRS P u) (frRN B n0) (frRA B a0) σ σ6 := G5.trans (F6.mono
        (fun y h => by simp only [frRS]; omega) (fun j h => by simp only [frRN]; omega)
        (fun b' _ h => by simp only [frRA]; omega))
      refine ⟨by rw [d6, d5, d4, d3, d2, d1, dr, dt], G6, by rw [F6.1 _ (by omega), rE5]; omega,
        Or.inr ⟨f6, m6, ?_⟩⟩
      have hf : (List.finRange m).find? q = some i := find_finRange_some q i hq hpq
      unfold FrRowsOut
      rw [show frTest A b p a = q from rfl, hf]
      exact ⟨f6, c6, a6⟩
    have h15 : σ5.nat (n0 + 4) = 1 := by rw [n5 (n0 + 4) (by omega) (by omega), h1r]
    by_cases hv0 : v < 0
    · -- `v < 0`
      have hq : q i = true := by simp [q, frTest, ← hv, hv0]
      exact XV.mono (XV.ifS_t hL (by omega) (by omega) b14 b0 (by rw [e14, z5]; exact_mod_cast hv0)
        (found _ le_rfl hq)) (by omega) fun _ h => h
    · have hc1 : ¬ σ5.sc (u + 14) < σ5.sc u := by rw [e14, z5]; exact_mod_cast hv0
      by_cases hvn : v * v < 2 ^ (2 * p) * (frAl A b i ⬝ᵥ frAl A b i)
      · -- `v² < nn`
        have hq : q i = true := by simp [q, frTest, ← hv, sq, hvn]
        exact XV.mono (XV.ifS_f hL (by omega) (by omega) b14 b0 hc1 (XV.ifS_t hL (by omega) (by omega) b15 b17
          (by rw [e15, x5]; exact_mod_cast hvn) (found _ le_rfl hq))) (by omega) fun _ h => h
      · -- the next row
        have hq : q i = false := by simp [q, frTest, ← hv, sq, hv0, hvn]
        refine XV.mono (XV.ifS_f hL (by omega) (by omega) b14 b0 hc1 (XV.ifS_f hL (by omega) (by omega) b15 b17
          (by rw [e15, x5]; exact_mod_cast hvn) (XV.nadd hL (i := B.rE) (a := B.rE) (b := n0 + 4) (by omega)
          (by omega) (by omega) (by rw [rE5]; omega) (by rw [h15]; omega))))
          (by omega) fun σ7 e7 => ?_
        subst e7
        refine ⟨by simp [d5, d4, d3, d2, d1, dr, dt], G5.setNat (Or.inl rfl) _, by simp [rE5, h15]; omega,
          Or.inl ⟨?_, ?_, ?_, ?_⟩⟩
        · simp only [Env.setNat_sc]
          rw [P5.2.1 _ (by omega), c4 _ (by omega) (by omega), c3 _ (by omega) (by omega),
            c2 _ (by omega) (by omega), c1 _ (by omega) (by omega), Fr.2.1 _ (by omega), q0]
        · simp [show n0 + 5 ≠ B.rE by omega, nm5]
        · simp [rE5, h15]
        · intro j hj
          by_cases hjt : j.1 < t
          · exact qp j hjt
          · have : j = i := Fin.ext (by simp [hi]; omega)
            rw [this]; exact hq
  -- after the loop
  rcases hJ with ⟨dJ, FJ, -, hcase⟩
  refine ⟨?_, dJ, FJ⟩
  rcases hcase with ⟨q0, qm, qt, qp⟩ | ⟨-, -, hR⟩
  · have hf : (List.finRange m).find? q = none := find_finRange_none q fun j => qp j (by omega)
    unfold FrRowsOut
    rw [show frTest A b p a = q from rfl, hf]
    exact q0
  · exact hR

end AdversarialBco.Bit.Transfer
