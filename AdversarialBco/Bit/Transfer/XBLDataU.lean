/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLDataT

@[expose] public section

/-!
# The call data of R11 TEST, after the first round of an epoch

`xdtA`: `H = B Bᵀ` in the arrays `16`, `17`, `g = b` in the arrays `18`, `19`, and the scalars over the grids
`2^{-pF}` (the fields of PARAM), `2^{-p}` (`k'`) and `ê = 1/Ĥ`:
`ℓ = 799/100 ρ - ê - k = (799 ρ̂ Ĥ Q - 100 F Q - 100 k̂ F Ĥ)/(100 F Ĥ Q)`, `r = s_b (1 - ε)/2 = ŝ (F - ε̂)/(2 F²)`,
`e = (s_b (1 - ε))²/(N_e d 8) = (ŝ (F - ε̂))²/(8 Λ F⁴)`, with `F = 2^pF`, `Q = 2^p`.
-/

namespace AdversarialBco.Bit.Transfer.BLM.DataM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

/-- `799 ρ̂ (Ĥ Q) - 100 F Q - 100 k̂ (F Ĥ)`. -/
abbrev eA0 : IE :=
  .op .sub (.op .sub (.op .mul (.op .mul (.sc 265) (.sc sRho)) (.op .mul (.sc s2eh) (.sc s2p)))
    (.op .mul (.op .mul (.sc 263) (.sc s2pF)) (.sc s2p))) (.op .mul (.op .mul (.sc 263) (.sc sK))
      (.op .mul (.sc s2pF) (.sc s2eh)))

/-- `100 F (Ĥ Q)`. -/
abbrev eA1 : IE := .op .mul (.op .mul (.sc 263) (.sc s2pF)) (.op .mul (.sc s2eh) (.sc s2p))

/-- `ŝ (F - ε̂)`. -/
abbrev eA2 : IE := .op .mul (.sc sSb) (.op .sub (.sc s2pF) (.sc sEps))

/-- `(2 F) F`. -/
abbrev eA3 : IE := .op .mul (.sc 267) (.sc s2pF)

/-- `(8 Λ) ((F F) (F F))`. -/
abbrev eA5 : IE :=
  .op .mul (.op .mul (.sc 262) (.sc sLam)) (.op .mul (.op .mul (.sc s2pF) (.sc s2pF)) (.op .mul (.sc s2pF) (.sc s2pF)))

/-- `H := B Bᵀ`, `g := b`, `ℓ`, `r`, `e`. -/
def xdtA (L : Layout) : XCmd :=
  .seq (xgram L aB aPHn aPHd 266) (.seq (xvec L sZ 300 (.arr ab 30) aPgn aPgd s2p rD)
    (xsix L eA0 eA1 eA2 eA3 (.op .mul eA2 eA2) eA5))

def dtAUnits (d : ℕ) : ℕ :=
  gramUnits d + (vecUnits d (.arr ab 30) + sixUnits eA0 eA1 eA2 eA3 (.op .mul eA2 eA2) eA5)

set_option maxHeartbeats 4000000 in
theorem XV.dtA {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hlay : BLLay L)
    {E p pF s Ne Lam : ℕ} {B : Matrix (Fin d) (Fin d) ℚ} {b : Fin d → ℚ} {rho eHat k eps sb : ℚ}
    {Hh rh kh eh sh : ℤ} (hd : 1 ≤ d)
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0)
    (h262 : σ.sc 262 = ((8 : ℤ) : ℝ)) (h263 : σ.sc 263 = ((100 : ℤ) : ℝ)) (h265 : σ.sc 265 = ((799 : ℤ) : ℝ))
    (h266 : σ.sc 266 = ((2 ^ p * 2 ^ p : ℤ) : ℝ)) (h267 : σ.sc 267 = ((2 * 2 ^ pF : ℤ) : ℝ))
    (hQ : σ.sc s2p = ((2 ^ p : ℤ) : ℝ)) (hF : σ.sc s2pF = ((2 ^ pF : ℤ) : ℝ))
    (hH : σ.sc s2eh = Hh) (hrh : σ.sc sRho = rh) (hkh : σ.sc sK = kh) (heh : σ.sc sEps = eh)
    (hsh : σ.sc sSb = sh) (hLam : σ.sc sLam = ((Lam : ℤ) : ℝ))
    (hpE : p ≤ E) (hpFE : pF ≤ E) (bH : |Hh| ≤ 2 ^ E) (brh : |rh| ≤ 2 ^ E) (bkh : |kh| ≤ 2 ^ E)
    (beh : |eh| ≤ 2 ^ E) (bsh : |sh| ≤ 2 ^ E) (bLam : |(Lam : ℤ)| ≤ 2 ^ E)
    (hH0 : 0 < Hh) (hLamE : Lam = d * Ne) (hNe : 1 ≤ Ne)
    (hrho : rho = (rh : ℚ) / ((2 ^ pF : ℤ) : ℚ)) (heHat : eHat = 1 / (Hh : ℚ))
    (hk : k = (kh : ℚ) / ((2 ^ p : ℤ) : ℚ)) (heps : eps = (eh : ℚ) / ((2 ^ pF : ℤ) : ℚ))
    (hsb : sb = (sh : ℚ) / ((2 ^ pF : ℤ) : ℚ))
    (hB : ∀ i j : Fin d, σ.arr aB (d * i + j) = qn p (B i j) ∧ OnG p (B i j) ∧ |qn p (B i j)| ≤ 2 ^ E)
    (hb : ∀ j : Fin d, σ.arr ab j = qn p (b j) ∧ OnG p (b j) ∧ |qn p (b j)| ≤ 2 ^ E)
    (hs : d + 5 * E + 12 ≤ s) (hℓ : d + 8 * E + 80 < ℓ) (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xdtA L) σ (dtAUnits d) (fun σ' =>
      (∀ i j : Fin d, PairA σ' aPHn aPHd (d * i + j) s ((B * Bᵀ) i j)) ∧
      (∀ j : Fin d, PairA σ' aPgn aPgd j s (b j)) ∧
      PairS σ' sPl (sPl + 1) s (799 / 100 * rho - eHat - k) ∧ PairS σ' (sPl + 2) (sPl + 3) s (sb * (1 - eps) / 2) ∧
      PairS σ' (sPl + 4) (sPl + 5) s ((sb * (1 - eps)) ^ 2 / (Ne * d * 8)) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => (64 ≤ y ∧ y ≤ 69) ∨ (256 ≤ y ∧ y ≤ 258) ∨ 300 ≤ y)
        (fun j => (19 ≤ j ∧ j ≤ 26) ∨ (29 ≤ j ∧ j ≤ 31)) (fun b _ => aPHn ≤ b ∧ b ≤ aPgd) σ σ') := by
  have hlay' := hlay
  obtain ⟨hNS, hNN, hNA⟩ := hlay'
  simp only [oE, rEE, aWE] at hNS hNN hNA
  refine XV.seq (XV.gramPair hL hlay (a := aB) (aN := aPHn) (aD := aPHd) (yD := 266) (E := E) (p := p) (s := s)
    (B := B) (by dgo) (by dgo) (by dgo) (by dgo) (by dgo) (by dgo) (by omega) (by omega) hD h1 hz h266 hB hpE
    (by omega) (by omega) hda) fun σ1 ⟨hP, d1, F1⟩ => ?_
  have k1 : ∀ y, ¬(256 ≤ y ∧ y ≤ 258) → σ1.sc y = σ.sc y := F1.2.1
  refine XV.seq (XV.vecPairQ hL hlay (a := ab) (aN := aPgn) (aD := aPgd) (yQ := s2p) (E := E) (p := p) (s := s)
    (b := b) (by dgo) (by dgo) (by dgo) (by dgo) (by dgo) (by dgo) (by dgo)
    (by rw [F1.1 rD (by dgo)]; exact hD) (by rw [F1.1 rOne (by dgo)]; exact h1) (by rw [k1 sZ (by dgo)]; exact hz)
    (by rw [k1 s2p (by dgo)]; exact hQ)
    (fun j => by rw [F1.2.2.1 ab j (fun h => by rcases h.1 with h | h <;> simp at h)]; exact hb j) hpE (by omega)
    (by omega) hda) fun σ2 ⟨hg, d2, F2⟩ => ?_
  have s2 : ∀ y < 300, ¬(256 ≤ y ∧ y ≤ 258) → σ2.sc y = σ.sc y := fun y hy hy' => by
    rw [F2.2.1 y (by omega), k1 y hy']
  have g : ∀ {y : ℕ} {v : ℝ}, y < 256 ∨ (258 < y ∧ y < 300) → σ.sc y = v → σ2.sc y = v := fun hy h => by
    rw [s2 _ (by omega) (by omega)]; exact h
  have z2 := g (by dgo) hz
  have e262 := g (by omega) h262
  have e263 := g (by omega) h263
  have e265 := g (by omega) h265
  have e267 := g (by omega) h267
  have q2 := g (by dgo) hQ
  have f2 := g (by dgo) hF
  have H2 := g (by dgo) hH
  have r2 := g (by dgo) hrh
  have k2 := g (by dgo) hkh
  have eh2 := g (by dgo) heh
  have sh2 := g (by dgo) hsh
  have l2 := g (by dgo) hLam
  have w : ∀ {v : ℤ}, |v| ≤ 2 ^ E → |v| ≤ 2 ^ (E + 10) := fun h => wk h (by omega)
  have bF : |(2 ^ pF : ℤ)| ≤ 2 ^ E := by rw [abs_two_pow]; exact pow_le_pow_right₀ (by norm_num) hpFE
  have bQ : |(2 ^ p : ℤ)| ≤ 2 ^ E := by rw [abs_two_pow]; exact pow_le_pow_right₀ (by norm_num) hpE
  have bc : ∀ c : ℤ, 0 ≤ c → c ≤ 1024 → |c| ≤ 2 ^ (E + 10) := fun c h0 h1 => by
    rw [abs_of_nonneg h0]
    exact h1.trans ((show (1024 : ℤ) = 2 ^ 10 by norm_num) ▸ pow_le_pow_right₀ (by norm_num) (by omega))
  have b2F : |(2 * 2 ^ pF : ℤ)| ≤ 2 ^ (E + 10) := by
    rw [abs_of_pos (by positivity), ← pow_succ']; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have L262 : IE.Leaves (E + 10) σ2 (.sc 262) := ⟨8, e262, bc 8 (by norm_num) (by norm_num)⟩
  have L263 : IE.Leaves (E + 10) σ2 (.sc 263) := ⟨100, e263, bc 100 (by norm_num) (by norm_num)⟩
  have L265 : IE.Leaves (E + 10) σ2 (.sc 265) := ⟨799, e265, bc 799 (by norm_num) (by norm_num)⟩
  have L267 : IE.Leaves (E + 10) σ2 (.sc 267) := ⟨_, e267, b2F⟩
  have LQ : IE.Leaves (E + 10) σ2 (.sc s2p) := ⟨_, q2, w bQ⟩
  have LF : IE.Leaves (E + 10) σ2 (.sc s2pF) := ⟨_, f2, w bF⟩
  have LH : IE.Leaves (E + 10) σ2 (.sc s2eh) := ⟨_, H2, w bH⟩
  have Lr : IE.Leaves (E + 10) σ2 (.sc sRho) := ⟨_, r2, w brh⟩
  have Lk : IE.Leaves (E + 10) σ2 (.sc sK) := ⟨_, k2, w bkh⟩
  have Le : IE.Leaves (E + 10) σ2 (.sc sEps) := ⟨_, eh2, w beh⟩
  have Ls : IE.Leaves (E + 10) σ2 (.sc sSb) := ⟨_, sh2, w bsh⟩
  have LL : IE.Leaves (E + 10) σ2 (.sc sLam) := ⟨_, l2, w bLam⟩
  refine XV.mono (XV.six hL (E := E + 10) (v0 := 799 * rh * Hh * 2 ^ p - 100 * 2 ^ pF * 2 ^ p - 100 * kh * 2 ^ pF * Hh)
    (v1 := 100 * 2 ^ pF * Hh * 2 ^ p) (v2 := sh * (2 ^ pF - eh)) (v3 := 2 * (2 ^ pF) ^ 2)
    (v4 := (sh * (2 ^ pF - eh)) ^ 2) (v5 := 8 * Lam * (2 ^ pF) ^ 4) z2 ?_ ?_ ?_ ?_ ?_ ?_) le_rfl
    fun σ3 ⟨a64, a65, a66, a67, a68, a69, d3, F3⟩ => ?_
  · scok
    · exact ⟨⟨⟨⟨L265, Lr⟩, ⟨LH, LQ⟩⟩, ⟨⟨L263, LF⟩, LQ⟩⟩, ⟨⟨L263, Lk⟩, ⟨LF, LH⟩⟩⟩
    · simp only [IE.eval, RealRAM.Op2.eval, e265, r2, H2, q2, e263, f2, k2]; push_cast; ring
  · scok
    · exact ⟨⟨L263, LF⟩, ⟨LH, LQ⟩⟩
    · simp only [IE.eval, RealRAM.Op2.eval, e263, f2, H2, q2]; push_cast; ring
  · scok
    · exact ⟨Ls, ⟨LF, Le⟩⟩
    · simp only [IE.eval, RealRAM.Op2.eval, sh2, f2, eh2]; push_cast; ring
  · scok
    · exact ⟨L267, LF⟩
    · simp only [IE.eval, RealRAM.Op2.eval, e267, f2]; push_cast; ring
  · scok
    · exact ⟨⟨Ls, ⟨LF, Le⟩⟩, ⟨Ls, ⟨LF, Le⟩⟩⟩
    · simp only [IE.eval, RealRAM.Op2.eval, sh2, f2, eh2]; push_cast; ring
  · scok
    · exact ⟨⟨L262, LL⟩, ⟨⟨LF, LF⟩, ⟨LF, LF⟩⟩⟩
    · simp only [IE.eval, RealRAM.Op2.eval, e262, l2, f2]; push_cast; ring
  -- the pairs
  obtain ⟨l1, l2', -, -⟩ := DataP.level_bound rh Hh kh (2 ^ pF) (2 ^ p) E brh bH bkh bF bQ
  obtain ⟨-, -, g3, g4, -, -, -, g8, g9⟩ := DataP.acc_bound sh eh (2 ^ pF) Lam 0 0 E bsh beh bF bLam (by simp)
    (by simp)
  have hF0 : (0 : ℤ) < 2 ^ pF := by positivity
  have hQ0 : (0 : ℤ) < 2 ^ p := by positivity
  have hLam1 : (1 : ℤ) ≤ Lam := by
    have : 1 ≤ Lam := by rw [hLamE]; nlinarith
    exact_mod_cast this
  have p1 : (0 : ℤ) < 100 * 2 ^ pF * Hh * 2 ^ p := by positivity
  have p3 : (0 : ℤ) < 2 * (2 ^ pF) ^ 2 := by positivity
  have p5 : (0 : ℤ) < 8 * Lam * (2 ^ pF) ^ 4 := by positivity
  have hs3 : 3 * E + 12 ≤ s := by omega
  have hs5 : 5 * E + 8 ≤ s := by omega
  have k3 : ∀ b c, σ3.arr b c = σ2.arr b c := fun b c => F3.2.2.1 b c not_false
  refine ⟨fun i j => ?_, fun j => ?_,
    ⟨_, _, p1, wk l1 hs3, (le_abs_self _).trans (wk l2' hs3), a64, a65,
      (DataP.level rho eHat k rh Hh kh (2 ^ pF) (2 ^ p) hF0 hH0 hQ0 hrho heHat hk).1.symm⟩,
    ⟨_, _, p3, wk g8 hs5, (le_abs_self _).trans (wk g9 hs5), a66, a67,
      (DataP.radius eps sb eh sh _ hF0 heps hsb).2.symm⟩,
    ⟨_, _, p5, wk g3 hs5, (le_abs_self _).trans (wk g4 hs5), a68, a69,
      (DataP.acc eps sb eh sh _ Ne d Lam hF0 hNe hd hLamE heps hsb).2.symm⟩, by rw [d3, d2, d1], ?_⟩
  · exact PairA.keep (hP i j) (by rw [k3, F2.2.2.1 _ _ (fun h => by simp only [aPHn, aPgn, aPgd] at h; omega)])
      (by rw [k3, F2.2.2.1 _ _ (fun h => by simp only [aPHd, aPgn, aPgd] at h; omega)])
  · exact PairA.keep (hg j) (by rw [k3]) (by rw [k3])
  · exact ((F1.mono (fun y h => Or.inr (Or.inl h)) (fun j h => by omega)
      (fun b c h => by simp only [aPHn, aPHd, aPgd] at h ⊢; omega)).trans
      (F2.mono (fun y h => Or.inr (Or.inr h)) (fun j h => by omega)
        (fun b c h => by simp only [aPHn, aPgn, aPgd] at h ⊢; omega))).trans
      (F3.mono (fun y h => by omega) (fun _ h => h.elim) (fun _ _ h => h.elim))

end AdversarialBco.Bit.Transfer.BLM.DataM
