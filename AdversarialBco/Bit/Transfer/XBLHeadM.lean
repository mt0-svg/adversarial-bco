/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLHeadQ
public import AdversarialBco.Bit.Transfer.XBLR8M
public import AdversarialBco.Bit.Transfer.XBLR4

@[expose] public section

/-!
# The head of BL's round on the machine

`xMid`: R7's square roots and R13's `s5` (the second line), R8 (`A'`, `B'`), R9 (`b'`, `k'`, `G'`, `l'`), from the
values of the first line in the slots `45 + k`. `XV.mid` runs it from integer inputs at most `2^U`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

/-! ## The bounds of the second and third lines -/

/-- The values of the second line are bounded by their pairs. -/
theorem w2_bound {Q F eh nh : ℤ} {v : ℕ → ℤ} {Gu : ℕ} (bQ : |Q| ≤ 2 ^ Gu) (bF : |F| ≤ 2 ^ Gu)
    (bE : |eh| ≤ 2 ^ Gu) (bN : |nh| ≤ 2 ^ Gu) (bV : ∀ k < 9, |v k| ≤ 2 ^ ev Gu (sl1Et k))
    (p3 : 0 ≤ w2 Q F eh nh v 3) (p5 : 0 ≤ w2 Q F eh nh v 5) (p7 : 0 ≤ w2 Q F eh nh v 7) :
    ∀ k < 14, |w2 Q F eh nh v k| ≤ 2 ^ ev Gu (sl2Et k) := by
  have hinB : ∀ y ∈ sl2Ins, |sl2I Q F eh nh v y| ≤ 2 ^ ev Gu (sl2In y) := by
    intro y hy
    simp only [sl2Ins, List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [sl2I, sl2In, ev, s2p] using bQ
    · simpa [sl2I, sl2In, ev, s2p, s2pF] using bF
    · simpa [sl2I, sl2In, ev, s2p, s2pF, sEta] using bE
    · simpa [sl2I, sl2In, ev, s2p, s2pF, sEta, sNu] using bN
    · simpa [sl2I, sl2In] using bV 0 (by norm_num)
    · simpa [sl2I, sl2In] using bV 1 (by norm_num)
    · simpa [sl2I, sl2In] using bV 2 (by norm_num)
    · simpa [sl2I, sl2In] using bV 3 (by norm_num)
    · simpa [sl2I, sl2In] using bV 4 (by norm_num)
    · simpa [sl2I, sl2In] using bV 5 (by norm_num)
    · simpa [sl2I, sl2In] using bV 7 (by norm_num)
  intro k hk
  exact SL.val_bound sl2St 70 _ sl2Ins sl2In sl2Et sl2T 12 Gu (SL.chk_get sl2St_chk).2
    (fun k hk => by simp only [sl2St_length] at hk; interval_cases k <;> trivial) hinB k
    (by rw [sl2St_length]; exact hk)

/-- The values of the third line are bounded by their pairs. -/
theorem w3_bound {F Q G2 D kY su sv kh yh nh G : ℤ} {Gu : ℕ} (bF : |F| ≤ 2 ^ Gu) (bQ : |Q| ≤ 2 ^ Gu)
    (bD : |D| ≤ 2 ^ Gu) (bK : |kh| ≤ 2 ^ Gu) (bN : |nh| ≤ 2 ^ Gu) (bG : |G| ≤ 2 ^ Gu) (bG2 : |G2| ≤ 2 ^ (2 * Gu))
    (bKY : |kY| ≤ 2 ^ (6 * Gu + 7)) (bY : |yh| ≤ 2 ^ (5 * Gu + 7)) (bsu : |su| ≤ 2 ^ (3 * Gu))
    (bsv : |sv| ≤ 2 ^ (3 * Gu)) :
    ∀ k < 6, |w3 F Q G2 D kY su sv kh yh nh G k| ≤ 2 ^ ev Gu (sl3Et k) := by
  have hinB : ∀ y ∈ sl3Ins, |sl3I F Q G2 D kY su sv kh yh nh G y| ≤ 2 ^ ev Gu (sl3In y) := by
    intro y hy
    simp only [sl3Ins, List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [sl3I, sl3In, sl1Et, ev, s2p, s2pF, sDmu, sK, sNu, s2g, bF, bQ, bG2, bD, bKY, bsu, bsv, bK, bY, bN, bG]
  intro k hk
  exact SL.val_bound sl3St 56 _ sl3Ins sl3In sl3Et sl3T 14 Gu (SL.chk_get sl3St_chk).2
    (fun k hk => by simp only [sl3St_length] at hk; interval_cases k <;> trivial) hinB k
    (by rw [sl3St_length]; exact hk)

/-- `d 2^a < 2^ℓ` from `d ≤ 2^U` and `U + a < ℓ`. -/
theorem d_pow_lt {U a ℓ : ℕ} (hd : d ≤ 2 ^ U) (h : U + a < ℓ) : d * 2 ^ a < 2 ^ ℓ :=
  calc d * 2 ^ a ≤ 2 ^ U * 2 ^ a := Nat.mul_le_mul_right _ hd
    _ = 2 ^ (U + a) := (pow_add 2 U a).symm
    _ < 2 ^ ℓ := Nat.pow_lt_pow_right (by norm_num) h

/-- `ĝ` and `ĝ·μ̂` of R9. -/
theorem r9_g_abs {F Q G yh nh : ℤ} {Bh : Matrix (Fin d) (Fin d) ℤ} {Γ mu : Fin d → ℤ} {U : ℕ} (hF1 : 1 ≤ F)
    (hQ1 : 1 ≤ Q) (hQ : Q ≤ 2 ^ U) (hG1 : 1 ≤ G) (hy : |yh| ≤ 2 ^ (5 * U + 7)) (hn : |nh| ≤ 2 ^ U)
    (hB : ∀ i j, |Bh i j| ≤ 2 ^ U) (hΓ : ∀ j, |Γ j| ≤ 2 ^ U) (hmu : ∀ j, |mu j| ≤ 2 ^ U) (hd : d ≤ 2 ^ U) :
    (∀ j, |rndZ (yh * nh * (Bh *ᵥ Γ) j) (F * Q * Q * G) Q| ≤ 2 ^ (10 * U + 8)) ∧
      |(fun j => rndZ (yh * nh * (Bh *ᵥ Γ) j) (F * Q * Q * G) Q) ⬝ᵥ mu| ≤ 2 ^ (12 * U + 8) := by
  have hg : ∀ j, |rndZ (yh * nh * (Bh *ᵥ Γ) j) (F * Q * Q * G) Q| ≤ 2 ^ (10 * U + 8) := fun j => by
    have hu : |(Bh *ᵥ Γ) j| ≤ 2 ^ (U + U + U) := mulVec_abs_le hB hΓ hd j
    have hn' : |yh * nh * (Bh *ᵥ Γ) j| ≤ 2 ^ (9 * U + 7) := by
      rw [abs_mul, abs_mul]
      calc |yh| * |nh| * |(Bh *ᵥ Γ) j| ≤ 2 ^ (5 * U + 7) * 2 ^ U * 2 ^ (U + U + U) := by gcongr
        _ = 2 ^ (9 * U + 7) := by rw [← pow_add, ← pow_add]; ring_nf
    have hv : 1 ≤ F * Q * Q * G := by
      have := mul_le_mul hF1 hQ1 zero_le_one (by omega)
      have := mul_le_mul this hQ1 zero_le_one (by omega)
      have := mul_le_mul this hG1 zero_le_one (by omega)
      simpa using this
    have := rndZ_abs_pow _ _ Q (9 * U + 7) U hv (by omega) hn' hQ
    rwa [show 9 * U + 7 + U + 1 = 10 * U + 8 by ring] at this
  refine ⟨hg, ?_⟩
  have := dot_abs_le (x := fun j => rndZ (yh * nh * (Bh *ᵥ Γ) j) (F * Q * Q * G) Q) (y := mu) hg hmu hd
  rwa [show 10 * U + 8 + U + U = 12 * U + 8 by ring] at this

/-! ## R7's roots, R8, R9 -/

/-- R7's square roots and `s5`, R8, R9. -/
def xMid (L : Layout) : XCmd := .seq (xR8s L) (.seq (xR8 L) (.seq (xR9a L) (xR9b L)))

/-- The units of `xMid`. -/
def midUnits (d U : ℕ) : ℕ := ev U (SL.unitsP sl2Et sl2St) + (r8Units d + (r9aUnits d (3 * U) + r9bUnits d))

/-- The cells that `xMid` changes. -/
def Smid (y : ℕ) : Prop := y = 30 ∨ (54 ≤ y ∧ y < 84) ∨ tR ≤ y
def Nmid (j : ℕ) : Prop := 19 ≤ j ∧ j ≤ 24
def Amid (b _c : ℕ) : Prop := 26 ≤ b ∧ b < 32

set_option maxHeartbeats 4000000 in
/-- **R7's roots, R8 and R9 on the machine**, from the first line's values `v` in the slots `45 + k`, the state's
numerators in BL's cells and `Γ` in `aGam`, all at most `2^U`. -/
theorem XV.mid {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {σ : Env d}
    {Q F G eh nh D kh lh : ℤ} {v : ℕ → ℤ} {Ah Bh : Matrix (Fin d) (Fin d) ℤ} {Γ mu bh Gh : Fin d → ℤ} {U : ℕ}
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (c1 : σ.sc 41 = 1) (c2 : σ.sc 42 = 2)
    (c4 : σ.sc 43 = 4) (eQ : σ.sc s2p = Q) (eF : σ.sc s2pF = F) (eG : σ.sc s2g = G) (eE : σ.sc sEta = eh)
    (eN : σ.sc sNu = nh) (eDm : σ.sc sDmu = D) (eK : σ.sc sK = kh) (eL : σ.sc sL = lh)
    (eV : ∀ k < 9, σ.sc (45 + k) = v k)
    (eA : ∀ i j : Fin d, σ.arr aA (d * i + j) = Ah i j) (eB : ∀ i j : Fin d, σ.arr aB (d * i + j) = Bh i j)
    (eW : ∀ i : Fin d, σ.arr aWv i = (Ah *ᵥ Γ) i) (eX : ∀ j : Fin d, σ.arr aGam j = Γ j)
    (eMu : ∀ j : Fin d, σ.arr aMu j = mu j) (eb : ∀ j : Fin d, σ.arr ab j = bh j)
    (eGh : ∀ j : Fin d, σ.arr aG j = Gh j)
    (hQ1 : 1 ≤ Q) (hF1 : 1 ≤ F) (hG1 : 1 ≤ G)
    (bQ : |Q| ≤ 2 ^ U) (bF : |F| ≤ 2 ^ U) (bG : |G| ≤ 2 ^ U) (bE : |eh| ≤ 2 ^ U) (bN : |nh| ≤ 2 ^ U)
    (bD : |D| ≤ 2 ^ U) (bK : |kh| ≤ 2 ^ U) (bL : |lh| ≤ 2 ^ U)
    (bA : ∀ i j, |Ah i j| ≤ 2 ^ U) (bB : ∀ i j, |Bh i j| ≤ 2 ^ U) (bX : ∀ j, |Γ j| ≤ 2 ^ U)
    (bMu : ∀ j, |mu j| ≤ 2 ^ U) (bb : ∀ j, |bh j| ≤ 2 ^ U) (bGh : ∀ j, |Gh j| ≤ 2 ^ U) (hdU : d ≤ 2 ^ U)
    (bV : ∀ k < 9, |v k| ≤ 2 ^ ev U (sl1Et k))
    (p3 : 0 ≤ w2 Q F eh nh v 3) (p5 : 0 ≤ w2 Q F eh nh v 5) (p7 : 0 ≤ w2 Q F eh nh v 7)
    (hT : 130 * U + 120 < ℓ) (hTa : 130 * U + 120 < 2 ^ ℓa) (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xMid L) σ (midUnits d U) (fun σ' =>
      (∀ k < 14, σ'.sc (70 + k) = w2 Q F eh nh v k) ∧
      (∀ i j : Fin d, σ'.arr aAp (d * i + j) =
        rndZ (w2 Q F eh nh v 4 * Ah i j * v 4 - w2 Q F eh nh v 11 * (Ah *ᵥ Γ) i * Γ j) (Q * Q * v 4) Q) ∧
      (∀ i j : Fin d, σ'.arr aBp (d * i + j) =
        rndZ (w2 Q F eh nh v 6 * Bh i j * v 4 + w2 Q F eh nh v 13 * (Bh *ᵥ Γ) i * Γ j) (Q * Q * v 4) Q) ∧
      (∀ j : Fin d, σ'.arr 28 j = bh j + rndZ (v 1 * (((Bh *ᵥ Γ) ⬝ᵥ mu) * (Bh *ᵥ Γ) j -
        v 4 * (Bh *ᵥ (Bhᵀ *ᵥ mu)) j)) (F * Q * Q * Q * v 4 * D) Q) ∧
      (∀ j : Fin d, σ'.arr 29 j = Gh j + rndZ (v 0 * nh * (Bh *ᵥ Γ) j) (F * Q * Q * G) Q) ∧
      σ'.sc 59 = ((kh + rndZ (v 1 * (((Bh *ᵥ Γ) ⬝ᵥ mu) * ((Bh *ᵥ Γ) ⬝ᵥ mu) -
        v 4 * ((Bhᵀ *ᵥ mu) ⬝ᵥ (Bhᵀ *ᵥ mu)))) (2 * (F * Q * Q * Q * v 4 * D * D)) Q : ℤ) : ℝ) ∧
      σ'.sc 63 = ((lh + rndZ ((fun j => rndZ (v 0 * nh * (Bh *ᵥ Γ) j) (F * Q * Q * G) Q) ⬝ᵥ mu) (Q * D) Q : ℤ) : ℝ) ∧
      σ'.draws = σ.draws ∧ FrameA Smid Nmid Amid σ σ') := by
  have hlay' := hlay
  obtain ⟨hS, hN, hAr⟩ := hlay'
  simp only [oE, rEE, aWE] at hS hN hAr
  have hU : ∀ {a b : ℕ}, a ≤ b → (2 : ℤ) ^ a ≤ 2 ^ b := fun h => pow_le_pow_right₀ (by norm_num) h
  have hdZ : ∀ {c : ℕ}, U ≤ c → (d : ℤ) ≤ 2 ^ c := fun h => by
    have : (d : ℤ) ≤ 2 ^ U := by exact_mod_cast hdU
    exact this.trans (hU h)
  have hdN : ∀ {c : ℕ}, U ≤ c → d ≤ 2 ^ c := fun h => hdU.trans (Nat.pow_le_pow_right (by norm_num) h)
  have bv : ∀ k < 9, ∀ {c : ℕ}, ev U (sl1Et k) ≤ c → |v k| ≤ 2 ^ c := fun k hk c h => (bV k hk).trans (hU h)
  have bw2 := w2_bound bQ bF bE bN bV p3 p5 p7
  have bw : ∀ k < 14, |w2 Q F eh nh v k| ≤ 2 ^ (31 * U + 28) := fun k hk =>
    (bw2 k hk).trans (hU (by interval_cases k <;> simp [ev, sl2Et] <;> omega))
  -- the products
  have bu : ∀ j, |(Bh *ᵥ Γ) j| ≤ 2 ^ (3 * U) := fun j => by
    have := mulVec_abs_le bB bX hdU j; rwa [show U + U + U = 3 * U by ring] at this
  have bwA : ∀ j, |(Ah *ᵥ Γ) j| ≤ 2 ^ (3 * U) := fun j => by
    have := mulVec_abs_le bA bX hdU j; rwa [show U + U + U = 3 * U by ring] at this
  have bvt : ∀ j, |(Bhᵀ *ᵥ mu) j| ≤ 2 ^ (3 * U) := fun j => by
    have := mulVec_abs_le (M := Bhᵀ) (fun i k => by rw [transpose_apply]; exact bB k i) bMu hdU j
    rwa [show U + U + U = 3 * U by ring] at this
  have bww : ∀ j, |(Bh *ᵥ (Bhᵀ *ᵥ mu)) j| ≤ 2 ^ (5 * U) := fun j => by
    have := mulVec_abs_le bB bvt hdU j; rwa [show U + 3 * U + U = 5 * U by ring] at this
  have bsu : |(Bh *ᵥ Γ) ⬝ᵥ mu| ≤ 2 ^ (3 * (3 * U)) :=
    dot_le_three bu (fun j => (bMu j).trans (hU (by omega))) (hdZ (by omega))
  have bsv : |(Bhᵀ *ᵥ mu) ⬝ᵥ (Bhᵀ *ᵥ mu)| ≤ 2 ^ (3 * (3 * U)) := dot_le_three bvt bvt (hdZ (by omega))
  -- R7's roots and s5
  refine XV.seq (XV.r8s hL hlay (σ := σ) h1 hz c1 c2 c4 eQ eF eE eN eV bQ bF bE bN bV p3 p5 p7 (by omega)
    (by omega)) fun σ1 ⟨w1, d1, F1⟩ => ?_
  have s1 : ∀ y, y < 70 → σ1.sc y = σ.sc y := fun y h => F1.2.1 y (by simp only [S8s, tR]; omega)
  have n1 : ∀ j, j ≠ 19 → j ≠ 20 → σ1.nat j = σ.nat j := fun j a b => F1.1 j (by simp only [N8s]; omega)
  have r1 : ∀ b k, σ1.arr b k = σ.arr b k := fun b k => F1.2.2.1 b k id
  -- R8
  refine XV.seq (XV.r8 hL hlay (σ := σ1) (E := 31 * U + 28) (Q := Q) (G2 := v 4) (a1 := w2 Q F eh nh v 4)
    (a2 := w2 Q F eh nh v 11) (a3 := w2 Q F eh nh v 6) (a4 := w2 Q F eh nh v 13) (Ah := Ah) (Bh := Bh) (Γ := Γ)
    (by rw [n1 _ (by decide) (by decide), hD]) (by rw [n1 _ (by decide) (by decide), h1])
    (by rw [s1 _ (by decide), hz]) (by rw [s1 _ (by decide), eQ])
    (by rw [s1 _ (by decide)]; simpa using eV 4 (by norm_num)) (by simpa using w1 4 (by norm_num))
    (by simpa using w1 11 (by norm_num)) (by simpa using w1 6 (by norm_num)) (by simpa using w1 13 (by norm_num))
    (fun i j => by rw [r1, eA]) (fun i j => by rw [r1, eB]) (fun i => by rw [r1, eW]) (fun j => by rw [r1, eX])
    (bQ.trans (hU (by omega))) (bv 4 (by norm_num) (by simp [ev, sl1Et]; omega)) (bw 4 (by norm_num))
    (bw 11 (by norm_num)) (bw 6 (by norm_num)) (bw 13 (by norm_num)) (fun i j => (bA i j).trans (hU (by omega)))
    (fun i j => (bB i j).trans (hU (by omega))) (fun j => (bX j).trans (hU (by omega)))
    (fun i => (bwA i).trans (hU (by omega))) (fun i => (bu i).trans (hU (by omega))) (by omega)
    (d_pow_lt hdU (by omega)) hda) fun σ2 ⟨u2, a2, b2, d2, F2⟩ => ?_
  have s2 : ∀ y, y < 70 → y ≠ 30 → σ2.sc y = σ.sc y := fun y h h' => by
    rw [F2.2.1 y (by simp only [S8, tR]; omega), s1 y h]
  have n2 : ∀ j, j < 19 → σ2.nat j = σ.nat j := fun j h => by
    rw [F2.1 j (by simp only [N8]; omega), n1 j (by omega) (by omega)]
  have r2 : ∀ b k, b < 26 → σ2.arr b k = σ.arr b k := fun b k h => by
    rw [F2.2.2.1 b k (by simp only [A8, aU, aAp, aBp]; omega), r1]
  -- R9, first part
  refine XV.seq (XV.r9a hL hlay (σ := σ2) (Gu := 3 * U) (Bh := Bh) (mu := mu) (Γ := Γ) (F := F) (Q := Q)
    (G2 := v 4) (D := D) (kY := v 1) (kh := kh) (yh := v 0) (nh := nh) (G := G)
    (by rw [n2 _ (by decide), hD]) (by rw [n2 _ (by decide), h1]) (by rw [s2 _ (by decide) (by decide), hz])
    (by rw [s2 _ (by decide) (by decide), c1]) (by rw [s2 _ (by decide) (by decide), c2])
    (by rw [s2 _ (by decide) (by decide), c4]) (fun i j => by rw [r2 _ _ (by decide), eB])
    (fun j => by rw [r2 _ _ (by decide), eMu]) u2 (by rw [s2 _ (by decide) (by decide), eF])
    (by rw [s2 _ (by decide) (by decide), eQ]) (by rw [s2 _ (by decide) (by decide)]; simpa using eV 4 (by norm_num))
    (by rw [s2 _ (by decide) (by decide), eDm]) (by rw [s2 _ (by decide) (by decide)]; simpa using eV 1 (by norm_num))
    (by rw [s2 _ (by decide) (by decide), eK]) (by rw [s2 _ (by decide) (by decide)]; simpa using eV 0 (by norm_num))
    (by rw [s2 _ (by decide) (by decide), eN]) (by rw [s2 _ (by decide) (by decide), eG])
    (bF.trans (hU (by omega))) (bQ.trans (hU (by omega))) (bD.trans (hU (by omega))) (bK.trans (hU (by omega)))
    (bN.trans (hU (by omega))) (bG.trans (hU (by omega))) (bv 4 (by norm_num) (by simp [ev, sl1Et]; omega))
    (bv 1 (by norm_num) (by simp [ev, sl1Et]; omega)) (bv 0 (by norm_num) (by simp [ev, sl1Et]; omega))
    (fun i j => (bB i j).trans (hU (by omega))) (fun j => (bMu j).trans (hU (by omega))) bu bvt (hdZ (by omega))
    (by omega) (d_pow_lt hdU (by omega)) (by omega) (by omega)) fun σ3 ⟨v31, v28, e54, e55, w3s, d3, F3⟩ => ?_
  have s3 : ∀ y, y < 54 → y ≠ 30 → σ3.sc y = σ.sc y := fun y h h' => by
    rw [F3.2.1 y (by simp only [S9a, tR]; omega), s2 y (by omega) h']
  have s3' : ∀ y, 70 ≤ y → y < 84 → σ3.sc y = σ1.sc y := fun y h h' => by
    rw [F3.2.1 y (by simp only [S9a, tR]; omega), F2.2.1 y (by simp only [S8, tR]; omega)]
  have n3 : ∀ j, j < 19 → σ3.nat j = σ.nat j := fun j h => by
    rw [F3.1 j (by simp only [N9a]; omega), n2 j h]
  have r3 : ∀ b k, b < 26 → σ3.arr b k = σ.arr b k := fun b k h => by
    rw [F3.2.2.1 b k (by simp only [A9a]; omega), r2 b k h]
  have r3u : ∀ k, σ3.arr aU k = σ2.arr aU k := fun k => F3.2.2.1 _ k (by simp only [A9a, aU]; omega)
  have r3a : ∀ b k, (b = aAp ∨ b = aBp) → σ3.arr b k = σ2.arr b k := fun b k h =>
    F3.2.2.1 b k (by simp only [A9a, aAp, aBp] at h ⊢; omega)
  -- the bounds of R9's second part
  have bw3 := w3_bound (F := F) (Q := Q) (G2 := v 4) (D := D) (kY := v 1) (su := (Bh *ᵥ Γ) ⬝ᵥ mu)
    (sv := (Bhᵀ *ᵥ mu) ⬝ᵥ (Bhᵀ *ᵥ mu)) (kh := kh) (yh := v 0) (nh := nh) (G := G) (Gu := 3 * U)
    (bF.trans (hU (by omega))) (bQ.trans (hU (by omega))) (bD.trans (hU (by omega))) (bK.trans (hU (by omega)))
    (bN.trans (hU (by omega))) (bG.trans (hU (by omega))) (bv 4 (by norm_num) (by simp [ev, sl1Et]; omega))
    (bv 1 (by norm_num) (by simp [ev, sl1Et]; omega)) (bv 0 (by norm_num) (by simp [ev, sl1Et]; omega)) bsu bsv
  obtain ⟨bg, bgm⟩ := r9_g_abs (Bh := Bh) (Γ := Γ) (mu := mu) hF1 hQ1 (le_of_abs_le bQ) hG1
    (bv 0 (by norm_num) (by simp [ev, sl1Et])) bN bB bX bMu hdU
  have w30 := w3s 0 (by norm_num)
  have w33 := w3s 3 (by norm_num)
  have w34 := w3s 4 (by norm_num)
  have w35 := w3s 5 (by norm_num)
  rw [w3_0] at w30
  rw [w3_3] at w33
  rw [w3_4] at w34
  rw [w3_5] at w35
  -- R9, second part
  refine XV.mono (XV.r9b hL hlay (σ := σ3) (E := 21 * U + 8) (Q := Q) (kY := v 1)
    (su := (Bh *ᵥ Γ) ⬝ᵥ mu) (G2 := v 4) (Vb := F * Q * Q * Q * v 4 * D) (yv := v 0 * nh) (Vg := F * Q * Q * G)
    (lh := lh) (D := D) (bh := bh) (u := Bh *ᵥ Γ) (w := Bh *ᵥ (Bhᵀ *ᵥ mu)) (Gh := Gh) (mu := mu)
    (by rw [n3 _ (by decide), hD]) (by rw [n3 _ (by decide), h1]) (by rw [s3 _ (by decide) (by decide), hz])
    (by rw [s3 _ (by decide) (by decide), eQ]) (by rw [s3 _ (by decide) (by decide)]; simpa using eV 1 (by norm_num))
    e54 (by rw [s3 _ (by decide) (by decide)]; simpa using eV 4 (by norm_num)) (by simpa using w30)
    (by simpa using w34) (by simpa using w35) (by rw [s3 _ (by decide) (by decide), eL])
    (by rw [s3 _ (by decide) (by decide), eDm]) (fun j => by rw [r3 _ _ (by decide), eb])
    (fun j => by rw [r3u, u2]) v28 (fun j => by rw [r3 _ _ (by decide), eGh]) (fun j => by rw [r3 _ _ (by decide), eMu])
    (bQ.trans (hU (by omega))) (bv 1 (by norm_num) (by simp [ev, sl1Et]; omega)) (bsu.trans (hU (by omega)))
    (bv 4 (by norm_num) (by simp [ev, sl1Et]; omega))
    (by have := bw3 0 (by norm_num); rw [w3_0] at this; exact this.trans (hU (by simp [ev, sl3Et]; omega)))
    (by have := bw3 4 (by norm_num); rw [w3_4] at this; exact this.trans (hU (by simp [ev, sl3Et]; omega)))
    (by have := bw3 5 (by norm_num); rw [w3_5] at this; exact this.trans (hU (by simp [ev, sl3Et]; omega)))
    (bL.trans (hU (by omega))) (bD.trans (hU (by omega))) (fun j => (bb j).trans (hU (by omega)))
    (fun j => (bu j).trans (hU (by omega))) (fun j => (bww j).trans (hU (by omega)))
    (fun j => (bGh j).trans (hU (by omega))) (fun j => (bMu j).trans (hU (by omega)))
    (fun j => (bg j).trans (hU (by omega))) (bgm.trans (hU (by omega))) (by omega) (d_pow_lt hdU (by omega)) hda)
    le_rfl fun σ4 ⟨b28, g31, g29, s62, s63, d4, F4⟩ => ?_
  refine ⟨fun k hk => ?_, fun i j => ?_, fun i j => ?_, b28, g29, ?_, s63, by rw [d4, d3, d2, d1], ?_⟩
  · rw [F4.2.1 _ (by simp only [S9b, tR]; omega), s3' _ (by omega) (by omega)]; exact w1 k hk
  · rw [F4.2.2.1 _ _ (by simp only [A9b, aAp]; omega), r3a _ _ (Or.inl rfl)]; exact a2 i j
  · rw [F4.2.2.1 _ _ (by simp only [A9b, aBp]; omega), r3a _ _ (Or.inr rfl)]; exact b2 i j
  · rw [F4.2.1 _ (by simp only [S9b, tR]; omega)]; simpa using w33
  · refine (F1.mono (fun y h => ?_) (fun j h => ?_) (fun _ _ h => h.elim)).trans
      ((F2.mono (fun y h => ?_) (fun j h => ?_) (fun b c h => ?_)).trans
        ((F3.mono (fun y h => ?_) (fun j h => ?_) (fun b c h => ?_)).trans
          (F4.mono (fun y h => ?_) (fun j h => ?_) (fun b c h => ?_))))
    all_goals first
      | (simp only [S8s, Smid] at h ⊢; omega)
      | (simp only [N8s, Nmid] at h ⊢; omega)
      | (simp only [S8, Smid] at h ⊢; omega)
      | (simp only [N8, Nmid] at h ⊢; omega)
      | (simp only [A8, Amid, aU, aAp, aBp] at h ⊢; omega)
      | (simp only [S9a, Smid] at h ⊢; omega)
      | (simp only [N9a, Nmid] at h ⊢; omega)
      | (simp only [A9a, Amid] at h ⊢; omega)
      | (simp only [S9b, Smid] at h ⊢; omega)
      | (simp only [N9b, Nmid] at h ⊢; omega)
      | (simp only [A9b, Amid] at h ⊢; omega)

end AdversarialBco.Bit.Transfer.BLM
