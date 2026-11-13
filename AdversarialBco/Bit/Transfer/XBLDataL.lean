/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLDataU
public import AdversarialBco.Bit.Transfer.XBLDataQ

@[expose] public section

/-!
# The call data of R14 LINE

`xdl`: the constants, `Q² D_w` in the slot `269`, `P = B' B'ᵀ` (arrays `20`, `21`) with its integer numerators,
`H = P` again (arrays `16`, `17`), `g = b'` (arrays `18`, `19`), `f = P (ŵ/D_w)` (arrays `22`, `23`: the numerators
`(B̂ B̂ᵀ) ŵ` by `xmatvec` over `Q² D_w`), and the scalars `ℓ = 8 ρ - ê - k' = (8 ρ̂ Ĥ Q - F Q - k̂ F Ĥ)/(F Ĥ Q)`,
`r = s_b (1 - ε)/2`, `e = e_BL = F²/(128 Λ n² R̂²)`, with `F = 2^pF`, `Q = 2^p`.
-/

namespace AdversarialBco.Bit.Transfer.BLM.DataM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

/-- The Gram pairs with their integer numerators: the cells `d i + j` of `aN` hold `(B̂ B̂ᵀ) i j`. -/
theorem XV.gramPairX {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hlay : BLLay L)
    {a aN aD yD E p s : ℕ} {B : Matrix (Fin d) (Fin d) ℚ} (ha : a < L.NA) (haN : aN < L.NA) (haD : aD < L.NA)
    (hNa : aN ≠ a) (hDa : aD ≠ a) (hND : aN ≠ aD) (hyD : yD < L.NS) (hy256 : yD < 256 ∨ 258 < yD)
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (hσD : σ.sc yD = ((2 ^ p * 2 ^ p : ℤ) : ℝ))
    (hB : ∀ i j : Fin d, σ.arr a (d * i + j) = qn p (B i j) ∧ OnG p (B i j) ∧ |qn p (B i j)| ≤ 2 ^ E)
    (hpE : p ≤ E) (hs : d + 2 * E ≤ s) (hℓ : d + 2 * E < ℓ) (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xgram L a aN aD yD) σ (gramUnits d) (fun σ' =>
      (∀ i j : Fin d, PairA σ' aN aD (d * i + j) s ((B * Bᵀ) i j)) ∧
      (∀ i j : Fin d, σ'.arr aN (d * i + j) =
        (((Matrix.of fun i j => qn p (B i j)) * (Matrix.of fun i j => qn p (B i j))ᵀ) i j : ℤ)) ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => 256 ≤ y ∧ y ≤ 258) (fun j => (19 ≤ j ∧ j ≤ 26) ∨ j = 31)
        (fun b c => (b = aN ∨ b = aD) ∧ c < d * d) σ σ') := by
  have hcells : ∀ c < d * d, ∃ z : ℤ, σ.arr a c = z ∧ |z| ≤ 2 ^ E :=
    (RowP.cells_mat (d := d) (fun c => ∃ z : ℤ, σ.arr a c = z ∧ |z| ≤ 2 ^ E)).mp
      fun i j => ⟨_, (hB i j).1, (hB i j).2.2⟩
  obtain ⟨hxs, bxs⟩ := floor_cells hcells
  let Bh : Matrix (Fin d) (Fin d) ℤ := Matrix.of fun i j => qn p (B i j)
  have hxB : ∀ i k : Fin d, ⌊σ.arr a (d * i + k)⌋ = Bh i k := fun i k => by
    rw [(hB i k).1, Int.floor_intCast]; rfl
  have bD : |(2 ^ p * 2 ^ p : ℤ)| < 2 ^ ℓ := by
    rw [← pow_add, abs_of_pos (by positivity)]; exact pow_lt_pow_right₀ (by norm_num) (by omega)
  have hdl : d * 2 ^ (2 * E) < 2 ^ ℓ := by
    have h1 : d < 2 ^ d := Nat.lt_two_pow_self
    have h2 : d * 2 ^ (2 * E) < 2 ^ d * 2 ^ (2 * E) := Nat.mul_lt_mul_of_pos_right h1 (by positivity)
    rw [← pow_add] at h2
    exact lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine XV.mono (XV.gram hL hlay (xs := fun c => ⌊σ.arr a c⌋) (E := E) ha haN haD hNa hDa hND hyD hy256 hD h1
    hz hσD bD hxs bxs (by omega) hdl hda) le_rfl fun σ' ⟨hA, hdr, hF⟩ => ⟨fun i j => ?_, fun i j => ?_, hdr, hF⟩
  · obtain ⟨e1, e2⟩ := hA i i.2 j j.2
    have hg := gram_eq (xs := fun c => ⌊σ.arr a c⌋) hxB i j
    refine ⟨_, _, by positivity, ?_, ?_, e1, e2, ?_⟩
    · rw [hg]
      exact (DataP.gram_bound Bh (fun i j => (hB i j).2.2) i j).trans (pow_le_pow_right₀ (by norm_num) hs)
    · rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    · rw [hg, DataP.gram_link B Bh (fun i j => eq_qn_div p (hB i j).2.1) i j]
  · obtain ⟨e1, -⟩ := hA i i.2 j j.2
    rw [e1, gram_eq (xs := fun c => ⌊σ.arr a c⌋) hxB i j]

/-- `8 ρ̂ (Ĥ Q) - F Q - k̂ (F Ĥ)`. -/
abbrev eL0 : IE :=
  .op .sub (.op .sub (.op .mul (.op .mul (.sc 262) (.sc sRho)) (.op .mul (.sc s2eh) (.sc s2p)))
    (.op .mul (.sc s2pF) (.sc s2p))) (.op .mul (.sc 59) (.op .mul (.sc s2pF) (.sc s2eh)))

/-- `F (Ĥ Q)`. -/
abbrev eL1 : IE := .op .mul (.sc s2pF) (.op .mul (.sc s2eh) (.sc s2p))

/-- `F F`. -/
abbrev eL4 : IE := .op .mul (.sc s2pF) (.sc s2pF)

/-- `(128 Λ) ((n n) (R̂ R̂))`. -/
abbrev eL5 : IE := .op .mul (.op .mul (.sc 264) (.sc sLam)) (.op .mul (.op .mul (.sc sN) (.sc sN)) (.op .mul (.sc sR) (.sc sR)))

/-- `Q² D_w`. -/
abbrev eQD : IE := .op .mul (.sc 266) (.sc 91)

/-- The call data of R14 LINE. -/
def xdl (L : Layout) : XCmd :=
  .seq (xcst L) (.seq (eQD.code L sZ 269 300) (.seq (xgram L 27 aPPn aPPd 266) (.seq (xgram L 27 aPHn aPHd 266)
    (.seq (xvec L sZ 300 (.arr 28 30) aPgn aPgd s2p rD) (.seq (xvec L sZ 300 (.sc sZ) aPfn aPfd 269 rD)
      (.seq (xmatvec L sZ 256 300 aPPn 31 aPfn 19 20 21 rD rOne) (xsix L eL0 eL1 eA2 eA3 eL4 eL5)))))))

def dlUnits (d : ℕ) : ℕ :=
  9 + (eQD.units + (gramUnits d + (gramUnits d + (vecUnits d (.arr 28 30) + (vecUnits d (.sc sZ) +
    ((d * (d * 10 + 9) + 4) + sixUnits eL0 eL1 eA2 eA3 eL4 eL5))))))

set_option maxHeartbeats 8000000 in
theorem XV.dl {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hlay : BLLay L)
    {E p pF s Ne Lam nn : ℕ} {B : Matrix (Fin d) (Fin d) ℚ} {b : Fin d → ℚ} {wh : Fin d → ℤ}
    {rho eHat kp eps sb R : ℚ} {Hh rh kh eh sh Rh Dw : ℤ} (hd : 1 ≤ d) (hn : 1 ≤ nn)
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0)
    (hQ : σ.sc s2p = ((2 ^ p : ℤ) : ℝ)) (hF : σ.sc s2pF = ((2 ^ pF : ℤ) : ℝ))
    (hH : σ.sc s2eh = Hh) (hrh : σ.sc sRho = rh) (hkh : σ.sc 59 = kh) (heh : σ.sc sEps = eh)
    (hsh : σ.sc sSb = sh) (hLam : σ.sc sLam = ((Lam : ℤ) : ℝ)) (hN : σ.sc sN = ((nn : ℤ) : ℝ)) (hR : σ.sc sR = Rh)
    (hDw : σ.sc 91 = Dw)
    (hpE : p ≤ E) (hpFE : pF ≤ E) (bH : |Hh| ≤ 2 ^ E) (brh : |rh| ≤ 2 ^ E) (bkh : |kh| ≤ 2 ^ E)
    (beh : |eh| ≤ 2 ^ E) (bsh : |sh| ≤ 2 ^ E) (bLam : |(Lam : ℤ)| ≤ 2 ^ E) (bn : |(nn : ℤ)| ≤ 2 ^ E)
    (bR : |Rh| ≤ 2 ^ E) (bDw : Dw ≤ 2 ^ E) (hDw0 : 0 < Dw)
    (hH0 : 0 < Hh) (hR0 : 0 < Rh) (hLamE : Lam = d * Ne) (hNe : 1 ≤ Ne)
    (hrho : rho = (rh : ℚ) / ((2 ^ pF : ℤ) : ℚ)) (heHat : eHat = 1 / (Hh : ℚ))
    (hk : kp = (kh : ℚ) / ((2 ^ p : ℤ) : ℚ)) (heps : eps = (eh : ℚ) / ((2 ^ pF : ℤ) : ℚ))
    (hsb : sb = (sh : ℚ) / ((2 ^ pF : ℤ) : ℚ)) (hRq : R = (Rh : ℚ) / ((2 ^ pF : ℤ) : ℚ))
    (hB : ∀ i j : Fin d, σ.arr 27 (d * i + j) = qn p (B i j) ∧ OnG p (B i j) ∧ |qn p (B i j)| ≤ 2 ^ E)
    (hb : ∀ j : Fin d, σ.arr 28 j = qn p (b j) ∧ OnG p (b j) ∧ |qn p (b j)| ≤ 2 ^ E)
    (hw : ∀ j : Fin d, σ.arr 31 j = wh j ∧ |wh j| ≤ 2 ^ E)
    (hs : 2 * d + 5 * E + 12 ≤ s) (hℓ : 4 * d + 10 * E + 100 < ℓ) (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xdl L) σ (dlUnits d) (fun σ' =>
      (∀ i j : Fin d, PairA σ' aPHn aPHd (d * i + j) s ((B * Bᵀ) i j)) ∧
      (∀ j : Fin d, PairA σ' aPgn aPgd j s (b j)) ∧
      (∀ i j : Fin d, PairA σ' aPPn aPPd (d * i + j) s ((B * Bᵀ) i j)) ∧
      (∀ j : Fin d, PairA σ' aPfn aPfd j s (((B * Bᵀ) *ᵥ fun j => (wh j : ℚ) / Dw) j)) ∧
      PairS σ' sPl (sPl + 1) s (8 * rho - eHat - kp) ∧ PairS σ' (sPl + 2) (sPl + 3) s (sb * (1 - eps) / 2) ∧
      PairS σ' (sPl + 4) (sPl + 5) s (1 / (Ne * (128 * (nn : ℚ) ^ 2 * R ^ 2 * d))) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => (64 ≤ y ∧ y ≤ 69) ∨ 256 ≤ y) (fun j => 19 ≤ j ∧ j ≤ 31)
        (fun b _ => aPHn ≤ b ∧ b ≤ aPfd) σ σ') := by
  have hlay' := hlay
  obtain ⟨hNS, hNN, hNA⟩ := hlay'
  simp only [oE, rEE, aWE] at hNS hNN hNA
  have bQ : |(2 ^ p : ℤ)| ≤ 2 ^ E := by rw [abs_two_pow]; exact pow_le_pow_right₀ (by norm_num) hpE
  have bF : |(2 ^ pF : ℤ)| ≤ 2 ^ E := by rw [abs_two_pow]; exact pow_le_pow_right₀ (by norm_num) hpFE
  let Bh : Matrix (Fin d) (Fin d) ℤ := Matrix.of fun i j => qn p (B i j)
  -- the constants
  refine XV.seq (XV.cst hL hlay hQ hF bQ bF (by omega)) fun σ1 ⟨c0, _, c2, c3, c4, c5, c6, c7, c8, cd, cF⟩ => ?_
  have k1 : ∀ y, ¬(260 ≤ y ∧ y ≤ 268) → σ1.sc y = σ.sc y := cF.2.1
  -- `Q² D_w`
  have bQQ : |(2 ^ p * 2 ^ p : ℤ)| ≤ 2 ^ (2 * E) := by
    rw [abs_mul, two_mul, pow_add]; exact mul_le_mul bQ bQ (abs_nonneg _) (by positivity)
  have bDw' : |Dw| ≤ 2 ^ (2 * E) := by
    rw [abs_of_pos hDw0]; exact bDw.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  refine XV.seq (XV.ieRun (E := 2 * E) (v := 2 ^ p * 2 ^ p * Dw) hL
    (by simp only [IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega) (by dgo) (by omega)
    (by simp only [IE.scr]; omega) (by rw [k1 sZ (by dgo)]; exact hz)
    ⟨⟨_, c6, bQQ⟩, ⟨_, by rw [k1 91 (by omega)]; exact hDw, bDw'⟩⟩ (by simp only [IE.top, IE.mag]; omega)
    (by simp only [IE.eval, RealRAM.Op2.eval, c6, k1 91 (by omega), hDw]; push_cast; ring))
    fun σ2 ⟨q2, _, d2, F2⟩ => ?_
  have k2 : ∀ y, y ≠ 269 → y < 300 → σ2.sc y = σ1.sc y := fun y h h' => F2.2.1 y (by omega)
  have n2 : ∀ j, σ2.nat j = σ1.nat j := fun j => F2.1 j not_false
  have a2 : σ2.arr = σ1.arr := F2.2.2.1
  -- `P` with its numerators
  refine XV.seq (XV.gramPairX hL hlay (a := 27) (aN := aPPn) (aD := aPPd) (yD := 266) (E := E) (p := p) (s := s)
    (B := B) (by omega) (by dgo) (by dgo) (by dgo) (by dgo) (by dgo) (by omega) (by omega)
    (by rw [n2, cF.1 rD not_false]; exact hD) (by rw [n2, cF.1 rOne not_false]; exact h1)
    (by rw [k2 sZ (by dgo) (by dgo), k1 sZ (by dgo)]; exact hz) (by rw [k2 266 (by omega) (by omega)]; exact c6)
    (fun i j => by rw [a2, cF.2.2.1 27 _ not_false]; exact hB i j) hpE (by omega) (by omega) hda)
    fun σ3 ⟨hP3, hPx3, d3, F3⟩ => ?_
  have k3 : ∀ y, ¬(256 ≤ y ∧ y ≤ 258) → σ3.sc y = σ2.sc y := F3.2.1
  have a3 : ∀ b k, b ≠ aPPn → b ≠ aPPd → σ3.arr b k = σ.arr b k := fun b k h1 h2 => by
    rw [F3.2.2.1 b k (fun h => by rcases h.1 with h | h <;> contradiction), a2, cF.2.2.1 b k not_false]
  -- `H`
  refine XV.seq (XV.gramPair hL hlay (a := 27) (aN := aPHn) (aD := aPHd) (yD := 266) (E := E) (p := p) (s := s)
    (B := B) (by omega) (by dgo) (by dgo) (by dgo) (by dgo) (by dgo) (by omega) (by omega)
    (by rw [F3.1 rD (by dgo), n2, cF.1 rD not_false]; exact hD)
    (by rw [F3.1 rOne (by dgo), n2, cF.1 rOne not_false]; exact h1)
    (by rw [k3 sZ (by dgo), k2 sZ (by dgo) (by dgo), k1 sZ (by dgo)]; exact hz)
    (by rw [k3 266 (by omega), k2 266 (by omega) (by omega)]; exact c6)
    (fun i j => by rw [a3 27 _ (by dgo) (by dgo)]; exact hB i j) hpE (by omega) (by omega) hda)
    fun σ4 ⟨hH4, d4, F4⟩ => ?_
  have k4 : ∀ y, ¬(256 ≤ y ∧ y ≤ 258) → σ4.sc y = σ2.sc y := fun y h => by rw [F4.2.1 y h, k3 y h]
  have a4 : ∀ b k, b < 16 ∨ 23 < b → σ4.arr b k = σ.arr b k := fun b k hb => by
    rw [F4.2.2.1 b k (fun h => by simp only [aPHn, aPHd] at h; omega), a3 b k (by dgo) (by dgo)]
  have n4 : ∀ j, ¬((19 ≤ j ∧ j ≤ 26) ∨ j = 31) → σ4.nat j = σ.nat j := fun j h => by
    rw [F4.1 j h, F3.1 j h, n2, cF.1 j not_false]
  -- `g`
  refine XV.seq (XV.vecPairQ hL hlay (a := 28) (aN := aPgn) (aD := aPgd) (yQ := s2p) (E := E) (p := p) (s := s)
    (b := b) (by omega) (by dgo) (by dgo) (by dgo) (by dgo) (by dgo) (by dgo)
    (by rw [n4 rD (by dgo)]; exact hD) (by rw [n4 rOne (by dgo)]; exact h1)
    (by rw [k4 sZ (by dgo), k2 sZ (by dgo) (by dgo), k1 sZ (by dgo)]; exact hz)
    (by rw [k4 s2p (by dgo), k2 s2p (by dgo) (by dgo), k1 s2p (by dgo)]; exact hQ)
    (fun j => by rw [a4 28 _ (by omega)]; exact hb j) hpE (by omega) (by omega) hda)
    fun σ5 ⟨hg5, d5, F5⟩ => ?_
  have k5 : ∀ y < 300, ¬(256 ≤ y ∧ y ≤ 258) → σ5.sc y = σ2.sc y := fun y hy h => by
    rw [F5.2.1 y (by omega), k4 y h]
  have n5 : ∀ j, ¬((19 ≤ j ∧ j ≤ 26) ∨ (29 ≤ j ∧ j ≤ 31)) → σ5.nat j = σ.nat j := fun j h => by
    rw [F5.1 j (by omega), n4 j (by omega)]
  -- the denominators of `f`
  obtain ⟨hQD0, bQD⟩ := DataP.QQD_bound p E Dw hpE hDw0 bDw
  refine XV.seq (XV.vec hL hlay (z := sZ) (t := 300) (e := .sc sZ) (aN := aPfn) (aD := aPfd) (yD := 269) (nn := rD)
    (N := d) (E := 3 * E) (F := fun _ => 0) (D := 2 ^ p * 2 ^ p * Dw) (by simp only [IE.WF]; dgo) (by dgo)
    (by simp only [IE.scr]; omega) (by rw [k5 sZ (by dgo) (by dgo), k2 sZ (by dgo) (by dgo), k1 sZ (by dgo)]; exact hz)
    (by dgo) (by dgo) (by dgo) (by omega) (by dgo) (by dgo) (by rw [n5 rD (by dgo)]; exact hD)
    (by rw [n5 rOne (by dgo)]; exact h1) (by rw [k5 269 (by omega) (by omega)]; exact q2)
    (by rw [abs_of_pos hQD0]; exact bQD) (by unfold asz; nlinarith) (by omega) (by simp only [IE.top]; omega)
    (by omega) ?_) fun σ6 ⟨v6, d6, F6⟩ => ?_
  · intro k hk σ' hF' _ _ _
    have e : σ'.sc sZ = ((0 : ℤ) : ℝ) := by
      rw [hF'.2.1 sZ (by dgo), k5 sZ (by dgo) (by dgo), k2 sZ (by dgo) (by dgo), k1 sZ (by dgo), hz]; simp
    exact ⟨⟨0, e, by simp⟩, e⟩
  have k6 : ∀ y < 300, ¬(256 ≤ y ∧ y ≤ 258) → σ6.sc y = σ2.sc y := fun y hy h => by
    rw [F6.2.1 y (by omega), k5 y hy h]
  have n6 : ∀ j, ¬((19 ≤ j ∧ j ≤ 26) ∨ (29 ≤ j ∧ j ≤ 31)) → σ6.nat j = σ.nat j := fun j h => by
    rw [F6.1 j (by omega), n5 j h]
  -- the numerators of `f`
  have bBh : ∀ i j, |Bh i j| ≤ 2 ^ E := fun i j => (hB i j).2.2
  have hM6 : ∀ i k : Fin d, σ6.arr aPPn (d * i + k) = ((Bh * Bhᵀ) i k : ℤ) := fun i k => by
    rw [F6.2.2.1 _ _ (fun h => by simp only [aPPn, aPfn, aPfd] at h; omega),
      F5.2.2.1 _ _ (fun h => by simp only [aPPn, aPgn, aPgd] at h; omega),
      F4.2.2.1 _ _ (fun h => by simp only [aPPn, aPHn, aPHd] at h; omega)]
    exact hPx3 i k
  have hw6 : ∀ k : Fin d, σ6.arr 31 k = wh k := fun k => by
    rw [F6.2.2.1 _ _ (fun h => by simp only [aPfn, aPfd] at h; omega),
      F5.2.2.1 _ _ (fun h => by simp only [aPgn, aPgd] at h; omega),
      F4.2.2.1 _ _ (fun h => by simp only [aPHn, aPHd] at h; omega), a3 31 _ (by dgo) (by dgo)]
    exact (hw k).1
  have hdl : d * 2 ^ (2 * (d + 2 * E)) < 2 ^ ℓ := by
    have h1 : d < 2 ^ d := Nat.lt_two_pow_self
    have h2 : d * 2 ^ (2 * (d + 2 * E)) < 2 ^ d * 2 ^ (2 * (d + 2 * E)) :=
      Nat.mul_lt_mul_of_pos_right h1 (by positivity)
    rw [← pow_add] at h2
    exact lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine XV.seq (XV.matvec hL (z := sZ) (r := 256) (t := 300) (aM := aPPn) (ax := 31) (ay := aPfn) (ni := 19)
    (nr := 20) (nk := 21) (nd := rD) (none := rOne) (E := d + 2 * E) (M := Bh * Bhᵀ) (x := wh) (by dgo) (by omega)
    (by dgo) (by omega) (by rw [k6 sZ (by dgo) (by dgo), k2 sZ (by dgo) (by dgo), k1 sZ (by dgo)]; exact hz)
    (by dgo) (by omega) (by dgo) (by dgo) (by dgo) (by omega) (by omega) (by omega) (by dgo) (by dgo) (by decide)
    (by rw [n6 rD (by dgo)]; exact hD) (by rw [n6 rOne (by dgo)]; exact h1) hM6 hw6
    (fun i k => DataP.gram_bound Bh bBh i k) (fun k => wk (hw k).2 (by omega)) (by omega) hdl)
    fun σ7 ⟨v7, d7, F7⟩ => ?_
  -- the scalars
  have g : ∀ {y : ℕ} {v : ℝ}, y < 256 ∨ (258 < y ∧ y < 269) → σ1.sc y = v → σ7.sc y = v := fun {y v} hy h => by
    rw [F7.2.1 y (by omega), k6 y (by omega) (by omega), k2 y (by omega) (by omega)]; exact h
  have g0 : ∀ {y : ℕ} {v : ℝ}, y < 256 → ¬(260 ≤ y ∧ y ≤ 268) → σ.sc y = v → σ7.sc y = v := fun {y v} hy hy' h =>
    g (Or.inl hy) (by rw [k1 y hy']; exact h)
  have z7 := g0 (by dgo) (by dgo) hz
  have e262 := g (by omega) c2
  have e264 := g (by omega) c4
  have e267 := g (by omega) c7
  have q7 := g0 (by dgo) (by dgo) hQ
  have f7 := g0 (by dgo) (by dgo) hF
  have H7 := g0 (by dgo) (by dgo) hH
  have r7 := g0 (by dgo) (by dgo) hrh
  have k7 := g0 (by omega) (by omega) hkh
  have eh7 := g0 (by dgo) (by dgo) heh
  have sh7 := g0 (by dgo) (by dgo) hsh
  have l7 := g0 (by dgo) (by dgo) hLam
  have N7 := g0 (by dgo) (by dgo) hN
  have R7 := g0 (by dgo) (by dgo) hR
  have w : ∀ {v : ℤ}, |v| ≤ 2 ^ E → |v| ≤ 2 ^ (E + 10) := fun h => wk h (by omega)
  have bc : ∀ c : ℤ, 0 ≤ c → c ≤ 1024 → |c| ≤ 2 ^ (E + 10) := fun c h0 h1 => by
    rw [abs_of_nonneg h0]
    exact h1.trans ((show (1024 : ℤ) = 2 ^ 10 by norm_num) ▸ pow_le_pow_right₀ (by norm_num) (by omega))
  have b2F : |(2 * 2 ^ pF : ℤ)| ≤ 2 ^ (E + 10) := by
    rw [abs_of_pos (by positivity), ← pow_succ']; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have L262 : IE.Leaves (E + 10) σ7 (.sc 262) := ⟨8, e262, bc 8 (by norm_num) (by norm_num)⟩
  have L264 : IE.Leaves (E + 10) σ7 (.sc 264) := ⟨128, e264, bc 128 (by norm_num) (by norm_num)⟩
  have L267 : IE.Leaves (E + 10) σ7 (.sc 267) := ⟨_, e267, b2F⟩
  have LQ : IE.Leaves (E + 10) σ7 (.sc s2p) := ⟨_, q7, w bQ⟩
  have LF : IE.Leaves (E + 10) σ7 (.sc s2pF) := ⟨_, f7, w bF⟩
  have LH : IE.Leaves (E + 10) σ7 (.sc s2eh) := ⟨_, H7, w bH⟩
  have Lr : IE.Leaves (E + 10) σ7 (.sc sRho) := ⟨_, r7, w brh⟩
  have Lk : IE.Leaves (E + 10) σ7 (.sc 59) := ⟨_, k7, w bkh⟩
  have Le : IE.Leaves (E + 10) σ7 (.sc sEps) := ⟨_, eh7, w beh⟩
  have Ls : IE.Leaves (E + 10) σ7 (.sc sSb) := ⟨_, sh7, w bsh⟩
  have LL : IE.Leaves (E + 10) σ7 (.sc sLam) := ⟨_, l7, w bLam⟩
  have LN : IE.Leaves (E + 10) σ7 (.sc sN) := ⟨_, N7, w bn⟩
  have LR : IE.Leaves (E + 10) σ7 (.sc sR) := ⟨_, R7, w bR⟩
  refine XV.mono (XV.six hL (E := E + 10) (v0 := 8 * rh * Hh * 2 ^ p - 2 ^ pF * 2 ^ p - kh * 2 ^ pF * Hh)
    (v1 := 2 ^ pF * Hh * 2 ^ p) (v2 := sh * (2 ^ pF - eh)) (v3 := 2 * (2 ^ pF) ^ 2) (v4 := (2 ^ pF) ^ 2)
    (v5 := 128 * Lam * nn ^ 2 * Rh ^ 2) z7 ?_ ?_ ?_ ?_ ?_ ?_) le_rfl
    fun σ8 ⟨a64, a65, a66, a67, a68, a69, d8, F8⟩ => ?_
  · scok
    · exact ⟨⟨⟨⟨L262, Lr⟩, ⟨LH, LQ⟩⟩, ⟨LF, LQ⟩⟩, ⟨Lk, ⟨LF, LH⟩⟩⟩
    · simp only [IE.eval, RealRAM.Op2.eval, e262, r7, H7, q7, f7, k7]; push_cast; ring
  · scok
    · exact ⟨LF, ⟨LH, LQ⟩⟩
    · simp only [IE.eval, RealRAM.Op2.eval, f7, H7, q7]; push_cast; ring
  · scok
    · exact ⟨Ls, ⟨LF, Le⟩⟩
    · simp only [IE.eval, RealRAM.Op2.eval, sh7, f7, eh7]; push_cast; ring
  · scok
    · exact ⟨L267, LF⟩
    · simp only [IE.eval, RealRAM.Op2.eval, e267, f7]; push_cast; ring
  · scok
    · exact ⟨LF, LF⟩
    · simp only [IE.eval, RealRAM.Op2.eval, f7]; push_cast; ring
  · scok
    · exact ⟨⟨L264, LL⟩, ⟨⟨LN, LN⟩, ⟨LR, LR⟩⟩⟩
    · simp only [IE.eval, RealRAM.Op2.eval, e264, l7, N7, R7]; push_cast; ring
  -- the pairs
  obtain ⟨-, -, l3, l4⟩ := DataP.level_bound rh Hh kh (2 ^ pF) (2 ^ p) E brh bH bkh bF bQ
  obtain ⟨-, -, -, -, g5, g6, -, g8, g9⟩ := DataP.acc_bound sh eh (2 ^ pF) Lam Rh nn E bsh beh bF bLam bR bn
  have hF0 : (0 : ℤ) < 2 ^ pF := by positivity
  have hQ0 : (0 : ℤ) < 2 ^ p := by positivity
  have hLam1 : (1 : ℤ) ≤ Lam := by
    have : 1 ≤ Lam := by rw [hLamE]; nlinarith
    exact_mod_cast this
  have hn1 : (1 : ℤ) ≤ nn := by exact_mod_cast hn
  have p1 : (0 : ℤ) < 2 ^ pF * Hh * 2 ^ p := by positivity
  have p3 : (0 : ℤ) < 2 * (2 ^ pF) ^ 2 := by positivity
  have p5 : (0 : ℤ) < 128 * Lam * nn ^ 2 * Rh ^ 2 := by positivity
  have hs3 : 3 * E + 12 ≤ s := by omega
  have hs5 : 5 * E + 8 ≤ s := by omega
  have k8 : ∀ b c, σ8.arr b c = σ7.arr b c := fun b c => F8.2.2.1 b c not_false
  have k78 : ∀ b c, b ≠ aPfn → σ8.arr b c = σ6.arr b c := fun b c h => by
    rw [k8, F7.2.2.1 b c (fun h' => h h'.1)]
  refine ⟨fun i j => ?_, fun j => ?_, fun i j => ?_, fun j => ?_,
    ⟨_, _, p1, wk l3 hs3, (le_abs_self _).trans (wk l4 hs3), a64, a65,
      (DataP.level rho eHat kp rh Hh kh (2 ^ pF) (2 ^ p) hF0 hH0 hQ0 hrho heHat hk).2.symm⟩,
    ⟨_, _, p3, wk g8 hs5, (le_abs_self _).trans (wk g9 hs5), a66, a67,
      (DataP.radius eps sb eh sh _ hF0 heps hsb).2.symm⟩,
    ⟨_, _, p5, wk g5 hs5, (le_abs_self _).trans (wk g6 hs5), a68, a69,
      (DataP.eBL_link R Rh _ Ne d nn Lam hF0 hR0 hNe hd hn hLamE hRq).symm⟩,
    by rw [d8, d7, d6, d5, d4, d3, d2, cd], ?_⟩
  · refine PairA.keep (hH4 i j) ?_ ?_
    · rw [k78 _ _ (by dgo), F6.2.2.1 _ _ (fun h => by simp only [aPHn, aPfn, aPfd] at h; omega),
        F5.2.2.1 _ _ (fun h => by simp only [aPHn, aPgn, aPgd] at h; omega)]
    · rw [k78 _ _ (by dgo), F6.2.2.1 _ _ (fun h => by simp only [aPHd, aPfn, aPfd] at h; omega),
        F5.2.2.1 _ _ (fun h => by simp only [aPHd, aPgn, aPgd] at h; omega)]
  · refine PairA.keep (hg5 j) ?_ ?_
    · rw [k78 _ _ (by dgo), F6.2.2.1 _ _ (fun h => by simp only [aPgn, aPfn, aPfd] at h; omega)]
    · rw [k78 _ _ (by dgo), F6.2.2.1 _ _ (fun h => by simp only [aPgd, aPfn, aPfd] at h; omega)]
  · refine PairA.keep (hP3 i j) ?_ ?_
    · rw [k78 _ _ (by dgo), F6.2.2.1 _ _ (fun h => by simp only [aPPn, aPfn, aPfd] at h; omega),
        F5.2.2.1 _ _ (fun h => by simp only [aPPn, aPgn, aPgd] at h; omega),
        F4.2.2.1 _ _ (fun h => by simp only [aPPn, aPHn, aPHd] at h; omega)]
    · rw [k78 _ _ (by dgo), F6.2.2.1 _ _ (fun h => by simp only [aPPd, aPfn, aPfd] at h; omega),
        F5.2.2.1 _ _ (fun h => by simp only [aPPd, aPgn, aPgd] at h; omega),
        F4.2.2.1 _ _ (fun h => by simp only [aPPd, aPHn, aPHd] at h; omega)]
  · obtain ⟨-, u2⟩ := v6 j j.2
    refine ⟨_, _, hQD0, ?_, bQD.trans (pow_le_pow_right₀ (by norm_num) (by omega)), by rw [k8]; exact v7 j,
      by rw [k78 _ _ (by dgo)]; exact u2, ?_⟩
    · exact (DataP.gram_mulVec_bound Bh wh bBh (fun j => (hw j).2) j).trans
        (pow_le_pow_right₀ (by norm_num) (by omega))
    · exact (DataP.mulVec_link B Bh wh Dw hDw0 (fun i j => eq_qn_div p (hB i j).2.1) j).symm
  · exact ((((((((cF.mono (fun y h => Or.inr (by omega)) (fun _ h => h.elim) (fun _ _ h => h.elim)).trans
      ((FrameA.ofP (Ar := fun _ _ => False) F2).mono (fun y h => Or.inr (by omega)) (fun _ h => h.elim) (fun _ _ h => h.elim))).trans
      (F3.mono (fun y h => Or.inr (by omega)) (fun j h => by omega)
        (fun b c h => by simp only [aPHn, aPPn, aPPd, aPfd] at h ⊢; omega))).trans
      (F4.mono (fun y h => Or.inr (by omega)) (fun j h => by omega)
        (fun b c h => by simp only [aPHn, aPHd, aPfd] at h ⊢; omega))).trans
      (F5.mono (fun y h => Or.inr (by omega)) (fun j h => by omega)
        (fun b c h => by simp only [aPHn, aPgn, aPgd, aPfd] at h ⊢; omega))).trans
      (F6.mono (fun y h => Or.inr (by omega)) (fun j h => by omega)
        (fun b c h => by simp only [aPHn, aPfn, aPfd] at h ⊢; omega))).trans
      (F7.mono (fun y h => Or.inr (by omega)) (fun j h => by omega)
        (fun b c h => by simp only [aPHn, aPfn, aPfd] at h ⊢; omega))).trans
      (F8.mono (fun y h => by omega) (fun _ h => h.elim) (fun _ _ h => h.elim)))

end AdversarialBco.Bit.Transfer.BLM.DataM
