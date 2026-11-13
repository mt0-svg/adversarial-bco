/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLDataA
public import AdversarialBco.Bit.Transfer.XBLR10

@[expose] public section

/-!
# The call data of R11 TEST

`xdtC` (both cases): the constants, `P = B' B'ᵀ` in the arrays `20`, `21`, `f = b' - (η'/2) G'` in the arrays `22`,
`23`. Then `xdtF` (the first round of an epoch: `H = 0`, `g = 0`, `ℓ = 0`, `r = 1 - ε'`, `e = (1 - ε')²/(N_e d 8)`) or
`xdtA` (after it: `H = B Bᵀ`, `g = b`, `ℓ = LT - k`, `r = r'/2`, `e = r'²/(N_e d 8)`), on the slot `sFirst`.
-/

namespace AdversarialBco.Bit.Transfer.BLM.DataM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

theorem wk {v : ℤ} {a b : ℕ} (h : |v| ≤ 2 ^ a) (hab : a ≤ b) : |v| ≤ 2 ^ b :=
  h.trans (pow_le_pow_right₀ (by norm_num) hab)

theorem abs_two_pow (k : ℕ) : |(2 ^ k : ℤ)| = 2 ^ k := abs_of_pos (by positivity)

/-! ## Both cases -/

/-- `2 F b'_k - η̂ G'_k` at the turn `k` (the register `30`). -/
def ieF : IE := .op .sub (.op .mul (.sc 267) (.arr 28 30)) (.op .mul (.sc sEta) (.arr 29 30))

/-- The constants, `P`, `f`. -/
def xdtC (L : Layout) : XCmd := .seq (xcst L) (.seq (xgram L 27 aPPn aPPd 266) (xvec L sZ 300 ieF aPfn aPfd 268 rD))

def dtCUnits (d : ℕ) : ℕ := 9 + (gramUnits d + vecUnits d ieF)

set_option maxHeartbeats 4000000 in
theorem XV.dtC {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hlay : BLLay L)
    {E p pF s : ℕ} {eta : ℚ} {Bp : Matrix (Fin d) (Fin d) ℚ} {bp Gp : Fin d → ℚ}
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0)
    (hQ : σ.sc s2p = ((2 ^ p : ℤ) : ℝ)) (hF : σ.sc s2pF = ((2 ^ pF : ℤ) : ℝ))
    (hEta : σ.sc sEta = ((qn pF eta : ℤ) : ℝ)) (heta : OnG pF eta) (bEta : |qn pF eta| ≤ 2 ^ E)
    (hpE : p ≤ E) (hpFE : pF ≤ E)
    (h27 : ∀ i j : Fin d, σ.arr 27 (d * i + j) = qn p (Bp i j) ∧ OnG p (Bp i j) ∧ |qn p (Bp i j)| ≤ 2 ^ E)
    (h28 : ∀ j : Fin d, σ.arr 28 j = qn p (bp j) ∧ OnG p (bp j) ∧ |qn p (bp j)| ≤ 2 ^ E)
    (h29 : ∀ j : Fin d, σ.arr 29 j = qn p (Gp j) ∧ OnG p (Gp j) ∧ |qn p (Gp j)| ≤ 2 ^ E)
    (hs : d + 5 * E + 12 ≤ s) (hℓ : d + 8 * E + 80 < ℓ) (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xdtC L) σ (dtCUnits d) (fun σ' =>
      σ'.sc 260 = ((1 : ℤ) : ℝ) ∧ σ'.sc 262 = ((8 : ℤ) : ℝ) ∧ σ'.sc 263 = ((100 : ℤ) : ℝ) ∧
      σ'.sc 264 = ((128 : ℤ) : ℝ) ∧ σ'.sc 265 = ((799 : ℤ) : ℝ) ∧
      σ'.sc 266 = ((2 ^ p * 2 ^ p : ℤ) : ℝ) ∧ σ'.sc 267 = ((2 * 2 ^ pF : ℤ) : ℝ) ∧
      (∀ i j : Fin d, PairA σ' aPPn aPPd (d * i + j) s ((Bp * Bpᵀ) i j)) ∧
      (∀ j : Fin d, PairA σ' aPfn aPfd j s ((bp - (eta / 2) • Gp) j)) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => (256 ≤ y ∧ y ≤ 268) ∨ 300 ≤ y) (fun j => (19 ≤ j ∧ j ≤ 26) ∨ (29 ≤ j ∧ j ≤ 31))
        (fun b _ => aPPn ≤ b ∧ b ≤ aPfd) σ σ') := by
  have hlay' := hlay
  obtain ⟨hNS, hNN, hNA⟩ := hlay'
  simp only [oE, rEE, aWE] at hNS hNN hNA
  have bQ : |(2 ^ p : ℤ)| ≤ 2 ^ E := by rw [abs_two_pow]; exact pow_le_pow_right₀ (by norm_num) hpE
  have bF : |(2 ^ pF : ℤ)| ≤ 2 ^ E := by rw [abs_two_pow]; exact pow_le_pow_right₀ (by norm_num) hpFE
  refine XV.seq (XV.cst hL hlay hQ hF bQ bF (by omega)) fun σ1 ⟨c0, _, c2, c3, c4, c5, c6, c7, c8, cd, cF⟩ => ?_
  have k1 : ∀ y, ¬(260 ≤ y ∧ y ≤ 268) → σ1.sc y = σ.sc y := cF.2.1
  refine XV.seq (XV.gramPair hL hlay (a := 27) (aN := aPPn) (aD := aPPd) (yD := 266) (E := E) (p := p) (s := s)
    (B := Bp) (by omega) (by dgo) (by dgo) (by dgo) (by dgo) (by dgo) (by omega) (by omega)
    (by rw [cF.1 rD not_false]; exact hD) (by rw [cF.1 rOne not_false]; exact h1)
    (by rw [k1 sZ (by dgo)]; exact hz) c6 (fun i j => by rw [cF.2.2.1 27 _ not_false]; exact h27 i j) hpE
    (by omega) (by omega) hda) fun σ2 ⟨hP, d2, F2⟩ => ?_
  -- what `σ2` keeps
  have k2 : ∀ y, ¬(256 ≤ y ∧ y ≤ 258) → σ2.sc y = σ1.sc y := F2.2.1
  have a2 : ∀ b k, b ≠ aPPn → b ≠ aPPd → σ2.arr b k = σ.arr b k := fun b k h1 h2 => by
    rw [F2.2.2.1 b k (fun h => by rcases h.1 with h | h <;> contradiction), cF.2.2.1 b k not_false]
  have hc28 : ∀ k < d, ∃ z : ℤ, σ.arr 28 k = z ∧ |z| ≤ 2 ^ E := fun k hk =>
    ⟨_, (h28 ⟨k, hk⟩).1, (h28 ⟨k, hk⟩).2.2⟩
  have hc29 : ∀ k < d, ∃ z : ℤ, σ.arr 29 k = z ∧ |z| ≤ 2 ^ E := fun k hk =>
    ⟨_, (h29 ⟨k, hk⟩).1, (h29 ⟨k, hk⟩).2.2⟩
  obtain ⟨hx28, bx28⟩ := floor_cells hc28
  obtain ⟨hx29, bx29⟩ := floor_cells hc29
  have b2F : |(2 * 2 ^ pF : ℤ)| ≤ 2 ^ (2 * E + 1) := by
    rw [abs_of_pos (by positivity), ← pow_succ']; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have b2FQ : |(2 * 2 ^ pF * 2 ^ p : ℤ)| ≤ 2 ^ (2 * E + 1) := by
    rw [abs_of_pos (by positivity), ← pow_succ', ← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have e267 : σ2.sc 267 = ((2 * 2 ^ pF : ℤ) : ℝ) := by rw [k2 267 (by omega)]; exact c7
  have e268 : σ2.sc 268 = ((2 * 2 ^ pF * 2 ^ p : ℤ) : ℝ) := by rw [k2 268 (by omega)]; exact c8
  have eEta : σ2.sc sEta = ((qn pF eta : ℤ) : ℝ) := by rw [k2 sEta (by dgo), k1 sEta (by dgo)]; exact hEta
  refine XV.mono (XV.vec hL hlay (z := sZ) (t := 300) (e := ieF) (aN := aPfn) (aD := aPfd) (yD := 268) (nn := rD)
    (N := d) (E := 2 * E + 1) (F := fun k => 2 * 2 ^ pF * ⌊σ.arr 28 k⌋ - qn pF eta * ⌊σ.arr 29 k⌋)
    (D := 2 * 2 ^ pF * 2 ^ p)
    (by simp only [ieF, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; dgo) (by dgo)
    (by simp only [ieF, IE.scr]; omega) (by rw [k2 sZ (by dgo), k1 sZ (by dgo)]; exact hz) (by dgo) (by dgo)
    (by dgo) (by omega) (by dgo) (by dgo)
    (by rw [F2.1 rD (by dgo), cF.1 rD not_false]; exact hD) (by rw [F2.1 rOne (by dgo), cF.1 rOne not_false]; exact h1)
    e268 b2FQ (by unfold asz; nlinarith) (by omega) (by simp only [ieF, IE.top, IE.mag]; omega) (by omega) ?_) le_rfl
    fun σ3 ⟨hf, d3, F3⟩ => ?_
  · intro k hk σ' hF' _ hk30 _
    have e1 : σ'.sc 267 = ((2 * 2 ^ pF : ℤ) : ℝ) := by rw [hF'.2.1 267 (by omega)]; exact e267
    have e2 : σ'.sc sEta = ((qn pF eta : ℤ) : ℝ) := by rw [hF'.2.1 sEta (by dgo)]; exact eEta
    have e3 : σ'.arr 28 (σ'.nat 30) = ((⌊σ.arr 28 k⌋ : ℤ) : ℝ) := by
      rw [hk30, hF'.2.2.1 28 k (fun h => by simp at h), a2 28 k (by dgo) (by dgo)]; exact hx28 k hk
    have e4 : σ'.arr 29 (σ'.nat 30) = ((⌊σ.arr 29 k⌋ : ℤ) : ℝ) := by
      rw [hk30, hF'.2.2.1 29 k (fun h => by simp at h), a2 29 k (by dgo) (by dgo)]; exact hx29 k hk
    have hk' : σ'.nat 30 < asz d := by rw [hk30]; unfold asz; nlinarith
    refine ⟨⟨⟨⟨_, e1, b2F⟩, hk', _, e3, wk (bx28 k hk) (by omega)⟩, ⟨_, e2, wk bEta (by omega)⟩, hk', _, e4,
      wk (bx29 k hk) (by omega)⟩, ?_⟩
    simp only [ieF, IE.eval, RealRAM.Op2.eval, e1, e2, e3, e4]; push_cast; ring
  -- the pairs
  have hfl28 : ∀ j : Fin d, ⌊σ.arr 28 j⌋ = qn p (bp j) := fun j => by rw [(h28 j).1, Int.floor_intCast]
  have hfl29 : ∀ j : Fin d, ⌊σ.arr 29 j⌋ = qn p (Gp j) := fun j => by rw [(h29 j).1, Int.floor_intCast]
  have k3 : ∀ y, ¬300 ≤ y → σ3.sc y = σ2.sc y := F3.2.1
  refine ⟨by rw [k3 260 (by omega), k2 260 (by omega)]; exact c0, by rw [k3 262 (by omega), k2 262 (by omega)]; exact c2,
    by rw [k3 263 (by omega), k2 263 (by omega)]; exact c3, by rw [k3 264 (by omega), k2 264 (by omega)]; exact c4,
    by rw [k3 265 (by omega), k2 265 (by omega)]; exact c5, by rw [k3 266 (by omega), k2 266 (by omega)]; exact c6,
    by rw [k3 267 (by omega)]; exact e267, fun i j => ?_, fun j => ?_, by rw [d3, d2, cd], ?_⟩
  · exact PairA.keep (hP i j) (F3.2.2.1 _ _ fun h => by rcases h.1 with h | h <;> simp at h)
      (F3.2.2.1 _ _ fun h => by rcases h.1 with h | h <;> simp at h)
  · obtain ⟨u1, u2⟩ := hf j j.2
    have bu : |2 * 2 ^ pF * qn p (bp j) - qn pF eta * qn p (Gp j)| ≤ 2 ^ s := by
      have t1 : |2 * 2 ^ pF * qn p (bp j)| ≤ 2 ^ (2 * E + 1 + E) := absI_mul_le b2F (h28 j).2.2
      have t2 : |qn pF eta * qn p (Gp j)| ≤ 2 ^ (2 * E + 1 + E) := absI_mul_le (wk bEta (by omega)) (h29 j).2.2
      exact wk (absI_sub_le t1 t2) (by omega)
    refine ⟨_, _, by positivity, ?_, ?_, u1, u2, ?_⟩
    · simp only [hfl28, hfl29]; exact bu
    · exact (le_abs_self _).trans (wk b2FQ (by omega))
    · simp only [hfl28, hfl29]
      rw [DataP.f_link bp Gp (fun j => qn p (bp j)) (fun j => qn p (Gp j)) eta (qn pF eta)
        (fun j => eq_qn_div p (h28 j).2.1) (fun j => eq_qn_div p (h29 j).2.1) (eq_qn_div pF heta) j]
  · exact ((cF.mono (fun y h => Or.inl ⟨by omega, h.2⟩) (fun _ h => h.elim) (fun _ _ h => h.elim)).trans
      (F2.mono (fun y h => Or.inl ⟨h.1, by omega⟩) (fun j h => by rcases h with h | h <;> omega)
        (fun b c h => by simp only [aPPn, aPPd, aPfn, aPfd] at h ⊢; omega))).trans
      (F3.mono (fun y h => Or.inr h) (fun j h => by omega) (fun b c h => by simp only [aPPn, aPPd, aPfn, aPfd] at h ⊢; omega))

/-- The static conditions of an expression of the scalar block, leaving the leaves and the value. -/
theorem scOK_of {L : Layout} {E ℓ : ℕ} {σ : Env d} {e : IE} {v : ℤ} (hw : e.WF L 300) (hr : ROs e)
    (hc : 300 + e.scr ≤ L.NS) (hl : e.Leaves E σ) (ht : e.top E < ℓ) (hv : e.eval σ = v) : ScOK L E ℓ σ e v :=
  ⟨hw, hr, hc, hl, ht, hv⟩

/-- The static conditions of an expression of the scalar block, leaving the leaves and the value. -/
macro "scok" : tactic => `(tactic| refine scOK_of
  (by simp only [IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; dgo)
  (by simp only [ROs, RO]; dgo) (by simp only [IE.scr]; omega) ?_ (by simp only [IE.top, IE.mag]; omega) ?_)

theorem one_le_two_pow' (k : ℕ) : (1 : ℤ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)

/-! ## The first round of an epoch -/

abbrev eF2 : IE := .op .sub (.sc s2pF) (.sc sEps)
abbrev eF5 : IE := .op .mul (.op .mul (.sc 262) (.sc sLam)) (.op .mul (.sc s2pF) (.sc s2pF))

/-- `H := 0/1`, `g := 0/1`, `ℓ := 0/1`, `r := (F - ε̂)/F`, `e := (F - ε̂)²/(8 Λ F²)`. -/
def xdtF (L : Layout) : XCmd :=
  .seq xdd (.seq (xvec L sZ 300 (.sc sZ) aPHn aPHd 260 25) (.seq (xvec L sZ 300 (.sc sZ) aPgn aPgd 260 rD)
    (xsix L (.sc sZ) (.sc 260) eF2 (.sc s2pF) (.op .mul eF2 eF2) eF5)))

def dtFUnits (d : ℕ) : ℕ := (1 + (d * (1 + 3) + 3)) + (vecUnits (d * d) (.sc sZ) + (vecUnits d (.sc sZ) +
  sixUnits (.sc sZ) (.sc 260) eF2 (.sc s2pF) (.op .mul eF2 eF2) eF5))

set_option maxHeartbeats 4000000 in
theorem XV.dtF {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hlay : BLLay L)
    {E s Lam : ℕ} {P : Par} {eh : ℤ} (hd : 1 ≤ d)
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (h260 : σ.sc 260 = ((1 : ℤ) : ℝ))
    (h262 : σ.sc 262 = ((8 : ℤ) : ℝ)) (hF : σ.sc s2pF = ((2 ^ P.pF : ℤ) : ℝ)) (heh : σ.sc sEps = eh)
    (hLam : σ.sc sLam = ((Lam : ℤ) : ℝ)) (hpFE : P.pF ≤ E) (beh : |eh| ≤ 2 ^ E) (bLam : |(Lam : ℤ)| ≤ 2 ^ E)
    (hLamE : Lam = d * P.Ne) (hNe : 1 ≤ P.Ne) (heps : P.eps = (eh : ℚ) / ((2 ^ P.pF : ℤ) : ℚ))
    (hs : d + 5 * E + 12 ≤ s) (hℓ : d + 8 * E + 80 < ℓ) (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xdtF L) σ (dtFUnits d) (fun σ' =>
      (∀ i j : Fin d, PairA σ' aPHn aPHd (d * i + j) s ((0 : Matrix (Fin d) (Fin d) ℚ) i j)) ∧
      (∀ j : Fin d, PairA σ' aPgn aPgd j s ((0 : Fin d → ℚ) j)) ∧
      PairS σ' sPl (sPl + 1) s 0 ∧ PairS σ' (sPl + 2) (sPl + 3) s (1 - P.eps) ∧
      PairS σ' (sPl + 4) (sPl + 5) s ((1 - P.eps) ^ 2 / (P.Ne * d * 8)) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => (64 ≤ y ∧ y ≤ 69) ∨ 300 ≤ y) (fun j => j = 24 ∨ j = 25 ∨ j = 29 ∨ j = 30)
        (fun b _ => aPHn ≤ b ∧ b ≤ aPgd) σ σ') := by
  have hlay' := hlay
  obtain ⟨hNS, hNN, hNA⟩ := hlay'
  simp only [oE, rEE, aWE] at hNS hNN hNA
  have b1 : |(1 : ℤ)| ≤ 2 ^ E := by rw [abs_one]; exact one_le_two_pow' E
  have bF : |(2 ^ P.pF : ℤ)| ≤ 2 ^ E := by rw [abs_two_pow]; exact pow_le_pow_right₀ (by norm_num) hpFE
  refine XV.seq (XV.dd hL hlay hD h1 hda) fun σ1 ⟨n25, d1, F1⟩ => ?_
  have s1 : ∀ y, σ1.sc y = σ.sc y := fun y => F1.2.1 y not_false
  have one1 : σ1.nat rOne = 1 := by rw [F1.1 rOne (by dgo)]; exact h1
  refine XV.seq (XV.vec hL hlay (z := sZ) (t := 300) (e := .sc sZ) (aN := aPHn) (aD := aPHd) (yD := 260) (nn := 25)
    (N := d * d) (E := E) (F := fun _ => 0) (D := 1) (by simp only [IE.WF]; dgo) (by dgo)
    (by simp only [IE.scr]; omega) (by rw [s1]; exact hz) (by dgo) (by dgo) (by dgo) (by omega) (by omega) (by dgo)
    n25 one1 (by rw [s1]; exact h260) b1 (by unfold asz; omega) (by omega) (by simp only [IE.top]; omega)
    (by omega) ?_) fun σ2 ⟨v2, d2, F2⟩ => ?_
  · intro k hk σ' hF' _ _ _
    have e : σ'.sc sZ = ((0 : ℤ) : ℝ) := by rw [hF'.2.1 sZ (by dgo), s1, hz]; simp
    exact ⟨⟨0, e, by simp⟩, e⟩
  have s2 : ∀ y < 300, σ2.sc y = σ.sc y := fun y hy => by rw [F2.2.1 y (by omega), s1]
  refine XV.seq (XV.vec hL hlay (z := sZ) (t := 300) (e := .sc sZ) (aN := aPgn) (aD := aPgd) (yD := 260) (nn := rD)
    (N := d) (E := E) (F := fun _ => 0) (D := 1) (by simp only [IE.WF]; dgo) (by dgo)
    (by simp only [IE.scr]; omega) (by rw [s2 sZ (by dgo)]; exact hz) (by dgo) (by dgo) (by dgo) (by omega) (by dgo)
    (by dgo) (by rw [F2.1 rD (by dgo), F1.1 rD (by dgo)]; exact hD) (by rw [F2.1 rOne (by dgo)]; exact one1)
    (by rw [s2 260 (by omega)]; exact h260) b1 (by unfold asz; nlinarith) (by omega) (by simp only [IE.top]; omega)
    (by omega) ?_) fun σ3 ⟨v3, d3, F3⟩ => ?_
  · intro k hk σ' hF' _ _ _
    have e : σ'.sc sZ = ((0 : ℤ) : ℝ) := by rw [hF'.2.1 sZ (by dgo), s2 sZ (by dgo), hz]; simp
    exact ⟨⟨0, e, by simp⟩, e⟩
  have s3 : ∀ y < 300, σ3.sc y = σ.sc y := fun y hy => by rw [F3.2.1 y (by omega), s2 y hy]
  have z3 : σ3.sc sZ = ((0 : ℤ) : ℝ) := by rw [s3 sZ (by dgo), hz]; simp
  have o3 : σ3.sc 260 = ((1 : ℤ) : ℝ) := by rw [s3 260 (by omega)]; exact h260
  have e3 : σ3.sc 262 = ((8 : ℤ) : ℝ) := by rw [s3 262 (by omega)]; exact h262
  have f3 : σ3.sc s2pF = ((2 ^ P.pF : ℤ) : ℝ) := by rw [s3 s2pF (by dgo)]; exact hF
  have h3 : σ3.sc sEps = eh := by rw [s3 sEps (by dgo)]; exact heh
  have l3 : σ3.sc sLam = ((Lam : ℤ) : ℝ) := by rw [s3 sLam (by dgo)]; exact hLam
  have w : ∀ {v : ℤ}, |v| ≤ 2 ^ E → |v| ≤ 2 ^ (E + 10) := fun h => wk h (by omega)
  refine XV.mono (XV.six hL (E := E + 10) (v0 := 0) (v1 := 1) (v2 := 2 ^ P.pF - eh) (v3 := 2 ^ P.pF)
    (v4 := (2 ^ P.pF - eh) ^ 2) (v5 := 8 * Lam * (2 ^ P.pF) ^ 2) (by rw [z3]; simp) ?_ ?_ ?_ ?_ ?_ ?_) le_rfl
    fun σ4 ⟨a64, a65, a66, a67, a68, a69, d4, F4⟩ => ?_
  · scok
    · exact ⟨0, z3, by simp⟩
    · simp only [IE.eval, z3]
  · scok
    · exact ⟨1, o3, w b1⟩
    · simp only [IE.eval, o3]
  · scok
    · exact ⟨⟨_, f3, w bF⟩, ⟨_, h3, w beh⟩⟩
    · simp only [IE.eval, RealRAM.Op2.eval, f3, h3]; push_cast; ring
  · scok
    · exact ⟨_, f3, w bF⟩
    · simp only [IE.eval, f3]
  · scok
    · exact ⟨⟨⟨_, f3, w bF⟩, ⟨_, h3, w beh⟩⟩, ⟨_, f3, w bF⟩, ⟨_, h3, w beh⟩⟩
    · simp only [IE.eval, RealRAM.Op2.eval, f3, h3]; push_cast; ring
  · scok
    · have b8 : |(8 : ℤ)| ≤ 2 ^ (E + 10) := by
        rw [show (8 : ℤ) = 2 ^ 3 by norm_num, abs_two_pow]; exact pow_le_pow_right₀ (by norm_num) (by omega)
      exact ⟨⟨⟨8, e3, b8⟩, ⟨_, l3, w bLam⟩⟩, ⟨_, f3, w bF⟩, ⟨_, f3, w bF⟩⟩
    · simp only [IE.eval, RealRAM.Op2.eval, f3, l3, e3]; push_cast; ring
  -- the pairs
  obtain ⟨g1, g2, -, -, -, -, g7, -, -⟩ := DataP.acc_bound 0 eh (2 ^ P.pF) Lam 0 0 E (by simp) beh bF bLam (by simp)
    (by simp)
  have hF0 : (0 : ℤ) < 2 ^ P.pF := by positivity
  have hL0 : (0 : ℤ) < 8 * Lam * (2 ^ P.pF) ^ 2 := by
    have : 1 ≤ Lam := by rw [hLamE]; nlinarith
    positivity
  have hs' : 5 * E + 8 ≤ s := by omega
  have k4 : ∀ b k, σ4.arr b k = σ3.arr b k := fun b k => F4.2.2.1 b k not_false
  refine ⟨fun i j => ?_, fun j => ?_, ⟨0, 1, one_pos, by simp, one_le_two_pow' s, a64, a65, by simp⟩,
    ⟨_, _, hF0, wk g7 hs', (le_abs_self _).trans (wk bF (by omega)), a66, a67,
      (DataP.radius P.eps 0 eh 0 _ hF0 heps (by simp)).1.symm⟩,
    ⟨_, _, hL0, wk g1 hs', (le_abs_self _).trans (wk g2 hs'), a68, a69,
      (DataP.acc P.eps 0 eh 0 _ P.Ne d Lam hF0 hNe hd hLamE heps (by simp)).1.symm⟩, by rw [d4, d3, d2, d1], ?_⟩
  · have hc : d * i + j < d * d := by nlinarith [i.2, j.2]
    obtain ⟨u1, u2⟩ := v2 _ hc
    refine ⟨0, 1, one_pos, by simp, one_le_two_pow' s, ?_, ?_, by simp⟩
    · rw [k4, F3.2.2.1 _ _ (fun h => by simp only [aPHn, aPgn, aPgd] at h; omega)]; exact u1
    · rw [k4, F3.2.2.1 _ _ (fun h => by simp only [aPHd, aPgn, aPgd] at h; omega)]; exact u2
  · obtain ⟨u1, u2⟩ := v3 _ j.2
    exact ⟨0, 1, one_pos, by simp, one_le_two_pow' s, by rw [k4]; exact u1, by rw [k4]; exact u2, by simp⟩
  · exact ((((F1.mono (fun _ h => h.elim) (fun j h => by omega) (fun _ _ h => h.elim)).trans
      (F2.mono (fun y h => Or.inr h) (fun j h => by omega)
        (fun b c h => by simp only [aPHn, aPHd, aPgd] at h ⊢; omega))).trans
      (F3.mono (fun y h => Or.inr h) (fun j h => by omega)
        (fun b c h => by simp only [aPHn, aPgn, aPgd] at h ⊢; omega))).trans
      (F4.mono (fun y h => h) (fun _ h => h.elim) (fun _ _ h => h.elim)))

end AdversarialBco.Bit.Transfer.BLM.DataM
