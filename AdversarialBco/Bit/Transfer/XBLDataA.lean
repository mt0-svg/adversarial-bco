/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLDataS
public import AdversarialBco.Bit.Transfer.XBLDataP
public import AdversarialBco.Bit.Transfer.XBLR5
public import AdversarialBco.Bit.Transfer.XBLRowP

@[expose] public section

/-!
# The call data of BL's round, part 4: pairs from grid numerators

* `XV.cst`: the constants `1, 2, 8, 100, 128, 799` and `Q², 2F, 2FQ` (`Q = 2^p`, `F = 2^pF`) in the slots `260..268`;
* `XV.gramPair`: from the numerators on the grid `2^{-p}` of a matrix `B` (row-major), the pairs of `B Bᵀ`;
* `XV.vecPairQ`: from the numerators on the grid `2^{-p}` of a vector `b`, the pairs of `b`.
-/

namespace AdversarialBco.Bit.Transfer.BLM.DataM

open AdversarialBco AdversarialBco.Poly.Mach Matrix

variable {d : ℕ}

/-- Side conditions on the named cells: `omega`, after unfolding the names. -/
macro "dgo" : tactic => `(tactic| first | omega | decide |
  ((simp only [rD, rM, rMk, rOne, rPF, sZ, sN, s2p, s2pF, s2eh, sNe, sLam, sRint, sEps, sEta, sRho, sR, sSb, sK,
    sFirst, sMode, aB, ab, aPHn, aPHd, aPgn, aPgd, aPPn, aPPd, aPfn, aPfd, sPl, rEE, oE, aWE] at *) <;> omega) |
  fail "dgo")

/-- `rpenv` with the names unfolded in its side conditions. -/
macro "denv" : tactic =>
  `(tactic| (simp (disch := dgo) only [nat_setNat_ne, nat_setNat_eq, sc_setSc_ne, sc_setSc_eq,
    Env.setNat_sc, Env.setSc_nat, Env.setArr_nat, Env.setArr_sc, Env.setNat_arr, Env.setSc_arr, Env.setNat_draws,
    Env.setSc_draws, Env.setArr_draws]))

theorem PairA.keep {σ σ' : Env d} {an ad k s : ℕ} {x : ℚ} (h : PairA σ an ad k s x)
    (h1 : σ'.arr an k = σ.arr an k) (h2 : σ'.arr ad k = σ.arr ad k) : PairA σ' an ad k s x := by
  obtain ⟨u, v, hv, bu, bv, e1, e2, e3⟩ := h
  exact ⟨u, v, hv, bu, bv, by rw [h1, e1], by rw [h2, e2], e3⟩

theorem floor_cells {σ : Env d} {a N E : ℕ} (h : ∀ c < N, ∃ z : ℤ, σ.arr a c = z ∧ |z| ≤ 2 ^ E) :
    (∀ c < N, σ.arr a c = ((⌊σ.arr a c⌋ : ℤ) : ℝ)) ∧ ∀ c < N, |⌊σ.arr a c⌋| ≤ 2 ^ E := by
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨z, hz, -⟩ := h c hc; rw [hz, Int.floor_intCast]
  · obtain ⟨z, hz, bz⟩ := h c hc; rw [hz, Int.floor_intCast]; exact bz

theorem gram_eq {xs : ℕ → ℤ} {Bh : Matrix (Fin d) (Fin d) ℤ} (h : ∀ i k : Fin d, xs (d * i + k) = Bh i k)
    (i j : Fin d) : gramN d xs i j = (Bh * Bhᵀ) i j := by
  simp only [gramN, Matrix.mul_apply, Matrix.transpose_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun k => xs (d * i + k) * xs (d * j + k)) d]
  exact Finset.sum_congr rfl fun k _ => by rw [h i k, h j k]

theorem abs_lt_of_small {ℓ : ℕ} {c : ℤ} (hc : |c| < 4096) (hℓ : 12 ≤ ℓ) : |c| < 2 ^ ℓ :=
  lt_of_lt_of_le hc (by
    have : (2 : ℤ) ^ 12 ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) hℓ
    norm_num at this ⊢; exact this)

/-! ## The constants -/

/-- `260..265 := 1, 2, 8, 100, 128, 799; 266 := Q Q; 267 := 2 F; 268 := 2 F Q`. -/
def xcst (L : Layout) : XCmd :=
  .seq (toX (VL.sconst L 260 ((1 : ℤ) : ℚ))) (.seq (toX (VL.sconst L 261 ((2 : ℤ) : ℚ)))
    (.seq (toX (VL.sconst L 262 ((8 : ℤ) : ℚ))) (.seq (toX (VL.sconst L 263 ((100 : ℤ) : ℚ)))
      (.seq (toX (VL.sconst L 264 ((128 : ℤ) : ℚ))) (.seq (toX (VL.sconst L 265 ((799 : ℤ) : ℚ)))
        (.seq (toX (VL.sop2 L .mul 266 s2p s2p)) (.seq (toX (VL.sop2 L .mul 267 261 s2pF))
          (toX (VL.sop2 L .mul 268 267 s2p)))))))))

set_option maxHeartbeats 1000000 in
theorem XV.cst {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hlay : BLLay L)
    {Q F : ℤ} {E : ℕ} (hQ : σ.sc s2p = Q) (hF : σ.sc s2pF = F) (bQ : |Q| ≤ 2 ^ E) (bF : |F| ≤ 2 ^ E)
    (hℓ : 2 * E + 12 < ℓ) :
    XRunsB L X ℓa ℓ (xcst L) σ 9 (fun σ' =>
      σ'.sc 260 = ((1 : ℤ) : ℝ) ∧ σ'.sc 261 = ((2 : ℤ) : ℝ) ∧ σ'.sc 262 = ((8 : ℤ) : ℝ) ∧
      σ'.sc 263 = ((100 : ℤ) : ℝ) ∧ σ'.sc 264 = ((128 : ℤ) : ℝ) ∧ σ'.sc 265 = ((799 : ℤ) : ℝ) ∧
      σ'.sc 266 = ((Q * Q : ℤ) : ℝ) ∧ σ'.sc 267 = ((2 * F : ℤ) : ℝ) ∧ σ'.sc 268 = ((2 * F * Q : ℤ) : ℝ) ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => 260 ≤ y ∧ y ≤ 268) (fun _ => False) (fun _ _ => False) σ σ') := by
  obtain ⟨hNS, -, -⟩ := hlay
  simp only [oE] at hNS
  have h12 : 12 ≤ ℓ := by omega
  have b2 : |(2 : ℤ)| ≤ 2 ^ 1 := by norm_num
  have bQQ : |Q * Q| < 2 ^ ℓ := absI_le_pow (absI_mul_le bQ bQ) (by omega)
  have b2F : |2 * F| ≤ 2 ^ (1 + E) := absI_mul_le b2 bF
  have b2FQ : |2 * F * Q| < 2 ^ ℓ := absI_le_pow (absI_mul_le b2F bQ) (by omega)
  refine XV.mono (K := 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))) ?_ (by norm_num) fun _ h => h
  refine XV.seq (XV.constI hL (x := 260) (by omega) 1 (abs_lt_of_small (by norm_num) h12)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.constI hL (x := 261) (by omega) 2 (abs_lt_of_small (by norm_num) h12)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.constI hL (x := 262) (by omega) 8 (abs_lt_of_small (by norm_num) h12)) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.constI hL (x := 263) (by omega) 100 (abs_lt_of_small (by norm_num) h12)) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.constI hL (x := 264) (by omega) 128 (abs_lt_of_small (by norm_num) h12)) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.constI hL (x := 265) (by omega) 799 (abs_lt_of_small (by norm_num) h12)) fun σ6 e6 => ?_
  subst e6
  refine XV.seq (XV.mulI hL (x := 266) (a := s2p) (b := s2p) (by omega) (by dgo) (by dgo) (u := Q) (v := Q)
    (by denv; exact hQ) (by denv; exact hQ) (absI_le_pow bQ (by omega)) (absI_le_pow bQ (by omega)) bQQ)
    fun σ7 e7 => ?_
  subst e7
  refine XV.seq (XV.mulI hL (x := 267) (a := 261) (b := s2pF) (by omega) (by omega) (by dgo) (u := 2) (v := F)
    (by denv) (by denv; exact hF) (abs_lt_of_small (by norm_num) h12) (absI_le_pow bF (by omega))
    (absI_le_pow b2F (by omega))) fun σ8 e8 => ?_
  subst e8
  refine XV.mono (XV.mulI hL (x := 268) (a := 267) (b := s2p) (by omega) (by omega) (by dgo) (u := 2 * F) (v := Q)
    (by denv) (by denv; exact hQ) (absI_le_pow b2F (by omega)) (absI_le_pow bQ (by omega)) b2FQ) le_rfl
    fun σ9 e9 => ?_
  subst e9
  refine ⟨by denv, by denv, by denv, by denv, by denv, by denv, by denv, by denv, by denv, by denv, ?_⟩
  exact ((((((((((FrameA.refl _ _ _ σ).setSc ⟨le_rfl, by norm_num⟩ _).setSc ⟨by norm_num, by norm_num⟩ _).setSc
    ⟨by norm_num, by norm_num⟩ _).setSc ⟨by norm_num, by norm_num⟩ _).setSc ⟨by norm_num, by norm_num⟩ _).setSc
    ⟨by norm_num, by norm_num⟩ _).setSc ⟨by norm_num, by norm_num⟩ _).setSc ⟨by norm_num, by norm_num⟩ _).setSc
    ⟨by norm_num, le_rfl⟩ _)

/-! ## Pairs from grid numerators -/

set_option maxHeartbeats 1000000 in
/-- **The Gram pairs**: from `B` on the grid `2^{-p}` (numerators in the cells `d i + j` of `a`, at most `2^E`) and
`yD = 2^p 2^p`, the cells `d i + j` of `aN`, `aD` hold `(B Bᵀ) i j` as a pair below `2^s`. -/
theorem XV.gramPair {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hlay : BLLay L)
    {a aN aD yD E p s : ℕ} {B : Matrix (Fin d) (Fin d) ℚ} (ha : a < L.NA) (haN : aN < L.NA) (haD : aD < L.NA)
    (hNa : aN ≠ a) (hDa : aD ≠ a) (hND : aN ≠ aD) (hyD : yD < L.NS) (hy256 : yD < 256 ∨ 258 < yD)
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (hσD : σ.sc yD = ((2 ^ p * 2 ^ p : ℤ) : ℝ))
    (hB : ∀ i j : Fin d, σ.arr a (d * i + j) = qn p (B i j) ∧ OnG p (B i j) ∧ |qn p (B i j)| ≤ 2 ^ E)
    (hpE : p ≤ E) (hs : d + 2 * E ≤ s) (hℓ : d + 2 * E < ℓ) (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xgram L a aN aD yD) σ (gramUnits d) (fun σ' =>
      (∀ i j : Fin d, PairA σ' aN aD (d * i + j) s ((B * Bᵀ) i j)) ∧ σ'.draws = σ.draws ∧
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
    hz hσD bD hxs bxs (by omega) hdl hda) le_rfl fun σ' ⟨hA, hdr, hF⟩ => ⟨fun i j => ?_, hdr, hF⟩
  obtain ⟨e1, e2⟩ := hA i i.2 j j.2
  have hg := gram_eq (xs := fun c => ⌊σ.arr a c⌋) hxB i j
  refine ⟨_, _, by positivity, ?_, ?_, e1, e2, ?_⟩
  · rw [hg]
    exact (DataP.gram_bound Bh (fun i j => (hB i j).2.2) i j).trans (pow_le_pow_right₀ (by norm_num) hs)
  · rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  · rw [hg, DataP.gram_link B Bh (fun i j => eq_qn_div p (hB i j).2.1) i j]

set_option maxHeartbeats 1000000 in
/-- **The vector pairs**: from `b` on the grid `2^{-p}` (numerators in the cells `j` of `a`, at most `2^E`) and
`yQ = 2^p`, the cells `j` of `aN`, `aD` hold `b j` as a pair below `2^s`. -/
theorem XV.vecPairQ {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hlay : BLLay L)
    {a aN aD yQ E p s : ℕ} {b : Fin d → ℚ} (ha : a < L.NA) (haN : aN < L.NA) (haD : aD < L.NA)
    (hNa : aN ≠ a) (hDa : aD ≠ a) (hND : aN ≠ aD) (hyQ : yQ < 300)
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (hσQ : σ.sc yQ = ((2 ^ p : ℤ) : ℝ))
    (hb : ∀ j : Fin d, σ.arr a j = qn p (b j) ∧ OnG p (b j) ∧ |qn p (b j)| ≤ 2 ^ E)
    (hpE : p ≤ E) (hs : E ≤ s) (hℓ : E < ℓ) (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xvec L sZ 300 (.arr a 30) aN aD yQ rD) σ (vecUnits d (.arr a 30)) (fun σ' =>
      (∀ j : Fin d, PairA σ' aN aD j s (b j)) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => 300 ≤ y) (fun j => j = 30 ∨ j = 29) (fun b c => (b = aN ∨ b = aD) ∧ c < d) σ σ') := by
  have hlay' := hlay
  obtain ⟨hNS, hNN, -⟩ := hlay'
  simp only [oE, rEE] at hNS hNN
  have hcell : ∀ k < d, ∃ z : ℤ, σ.arr a k = z ∧ |z| ≤ 2 ^ E := fun k hk =>
    ⟨_, (hb ⟨k, hk⟩).1, (hb ⟨k, hk⟩).2.2⟩
  obtain ⟨hxs, bxs⟩ := floor_cells hcell
  have bQ : |(2 ^ p : ℤ)| ≤ 2 ^ E := by
    rw [abs_of_pos (by positivity)]; exact pow_le_pow_right₀ (by norm_num) hpE
  refine XV.mono (XV.vec hL hlay (z := sZ) (t := 300) (e := .arr a 30) (N := d) (E := E)
    (F := fun k => ⌊σ.arr a k⌋) (D := 2 ^ p) ⟨ha, by omega⟩ (by dgo) (by simp only [IE.scr]; omega) hz haN haD
    hND hyQ (by dgo) (by dgo) hD h1 hσQ bQ (by unfold asz; nlinarith) (by nlinarith)
    (by simp only [IE.top]; exact hℓ) hℓ ?_) le_rfl fun σ' ⟨hA, hdr, hF⟩ => ⟨fun j => ?_, hdr, hF⟩
  · intro k hk σ' hF' _ hk30 _
    have e : σ'.arr a (σ'.nat 30) = σ.arr a k := by
      rw [hk30, hF'.2.2.1 a k (fun h => hNa h.1.symm)]
    refine ⟨⟨by rw [hk30]; unfold asz; nlinarith, ⌊σ.arr a k⌋, by rw [e]; exact hxs k hk, bxs k hk⟩, ?_⟩
    simp only [IE.eval]; rw [e]; exact hxs k hk
  · obtain ⟨e1, e2⟩ := hA j j.2
    have hq : ⌊σ.arr a j⌋ = qn p (b j) := by rw [(hb j).1, Int.floor_intCast]
    refine ⟨_, _, by positivity, ?_, ?_, e1, e2, ?_⟩
    · rw [hq]; exact (hb j).2.2.trans (pow_le_pow_right₀ (by norm_num) hs)
    · exact (pow_le_pow_right₀ (by norm_num) hpE).trans (pow_le_pow_right₀ (by norm_num) hs)
    · rw [hq]; push_cast; exact (eq_qn_div p (hb j).2.1).symm

end AdversarialBco.Bit.Transfer.BLM.DataM
