/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PolyBlk5
public import AdversarialBco.Unified.PolyBlk2

@[expose] public section

/-!
# UNI-POLY, part 9: `ORCB`, the oracle query of `P` answered exactly from the input rows

* `rs_ORCB`: `orc dst src prec` of `P`: the cell `φ dst` gets the answer `rowR` of `ROWMEM` on the normalised point of
  `P`, every other cell unchanged; with `rowR_nrm`, the answer is the membership of that point in the polytope.
-/

namespace AdversarialBco.UniPoly

open AdversarialBco BitRAM BitRAMO RCmd

variable {d : ℕ} {w : World d} {L : ℕ} {t : State d}

theorem abs_nrm_le {y0 yj j B : ℤ} (hB : 1 ≤ B) (hy : |yj| ≤ B) : |nrm y0 yj j| ≤ B := by
  unfold nrm; split_ifs <;> simp_all [abs_neg] <;> linarith

set_option maxHeartbeats 4000000 in
/-- `ORCB dst src`: the cell `φ dst` gets `rowR` on the normalised point of `P` at `a = M (φ src)`. -/
theorem rs_ORCB {dst src a YB M B : ℤ} {m : ℕ} {nm dn : ℕ → ℕ → ℤ}
    (ha : t.mem (φ src) = a) (hYB1 : 1 ≤ YB) (hYB : t.mem cYB = YB) (hd : t.mem 0 = d) (hm : t.mem 2 = m)
    (hz : t.mem cZ = 0) (hAa : t.mem cAa = 0) (hOne : t.mem cOne = 0) (hD1 : t.mem cD1 = 0)
    (hA : t.mem cA = 0) (hC : t.mem cC = 0) (hY0 : t.mem cY0 = 0) (hSg : t.mem cSg = 0) (hI : t.mem cI = 0)
    (hX : t.mem cX = 0) (hV : t.mem cV = 0) (hB0 : t.mem cB = 0)
    (hR : t.mem cR = 0) (hE : t.mem cE = 0) (hS : t.mem cS = 0) (hQ : t.mem cQ = 0) (hJ : t.mem cJ = 0)
    (hYP : t.mem cYP = 0) (hN : t.mem cN = 0) (hE1 : t.mem cE1 = 0) (hDD : t.mem cDD = 0) (hY : t.mem cY = 0)
    (hT : t.mem cT = 0) (hL : t.mem cL = 0) (hRt : t.mem cRt = 0)
    (hYz : ∀ c, YB ≤ c → c ≤ YB + d → t.mem c = 0) (hYBm : 3 + 2 * (((d : ℤ) + 1) * m) ≤ YB)
    (hnm : ∀ i < m, ∀ j : ℕ, j ≤ d → t.mem (3 + 2 * (((d : ℤ) + 1) * i + j)) = nm i j)
    (hdn : ∀ i < m, ∀ j : ℕ, j ≤ d → t.mem (3 + 2 * (((d : ℤ) + 1) * i + j) + 1) = dn i j)
    (hM1 : 1 ≤ M) (hMb : ∀ i < m, ∀ j : ℕ, j ≤ d → |nm i j| ≤ M ∧ 0 < dn i j ∧ dn i j ≤ M)
    (hB : 1 ≤ B) (hyb : ∀ j : ℕ, j ≤ d → |t.mem (φ (a + j))| ≤ B)
    (hLs : len src + 11 ≤ L) (hLdst : len dst + 11 ≤ L) (hLa : ∀ j : ℕ, j ≤ d → len (a + j) + 11 ≤ L)
    (hLV : ((d : ℤ) + 1) * M ^ (d + 1) * B < 2 ^ L) (hLY : YB + d + 1 < 2 ^ L) (hLm : (m : ℤ) + 1 < 2 ^ L)
    (h10 : 10 ≤ L) :
    RS w L (ORCB dst src) t (fun n t' => n ≤ (d + 1) * 25 + m * (d * 19 + 29) + 70 ∧
      t'.mem = Function.update t.mem (φ dst)
        (rowR d m nm dn (fun j => nrm (t.mem (φ a)) (t.mem (φ (a + j))) j)) ∧ Same' t t') := by
  have hYB0 : 0 ≤ YB := by omega
  have hYB3 : 3 ≤ YB := by
    have : (0 : ℤ) ≤ ((d : ℤ) + 1) * m := by positivity
    omega
  have l0 : len (0 : ℤ) ≤ L := by rw [len_zero]; omega
  have hpos : (0 : ℤ) ≤ M ^ (d + 1) * B := by positivity
  have h1MB : (1 : ℤ) ≤ M ^ (d + 1) * B := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM1) hB
  have hdV : ((d : ℤ) + 1) ≤ ((d : ℤ) + 1) * M ^ (d + 1) * B := by
    have := mul_le_mul_of_nonneg_left h1MB (by omega : (0 : ℤ) ≤ (d : ℤ) + 1)
    rw [mul_one, ← mul_assoc] at this; exact this
  have hBV : B ≤ ((d : ℤ) + 1) * M ^ (d + 1) * B := by
    have h2 : (1 : ℤ) ≤ ((d : ℤ) + 1) * M ^ (d + 1) := one_le_mul_of_one_le_of_one_le (by omega) (one_le_pow₀ hM1)
    nlinarith
  have hMV : M ≤ ((d : ℤ) + 1) * M ^ (d + 1) * B := by
    have h2 : M ≤ M ^ (d + 1) := by
      calc M = M ^ 1 := (pow_one M).symm
        _ ≤ M ^ (d + 1) := pow_le_pow_right₀ hM1 (by omega)
    have h3 : M ^ (d + 1) ≤ ((d : ℤ) + 1) * M ^ (d + 1) := le_mul_of_one_le_left (by positivity) (by omega)
    have h4 : ((d : ℤ) + 1) * M ^ (d + 1) ≤ ((d : ℤ) + 1) * M ^ (d + 1) * B :=
      le_mul_of_one_le_right (by positivity) hB
    omega
  have hLd : len ((d : ℤ) + 1) ≤ L := len_of_abs (by rw [abs_of_nonneg (by omega)]) (by omega)
  have hLYd : len (YB + d) ≤ L := len_of_abs (by rw [abs_of_nonneg (by omega)]) (by omega)
  have hLy : ∀ j : ℕ, j ≤ d → len (t.mem (φ (a + j))) ≤ L := fun j hj =>
    len_of_abs ((hyb j hj).trans le_rfl) (by have := hyb j hj; omega)
  have hLA : 3 + 2 * (((d : ℤ) + 1) * m) < 2 ^ L := by omega
  have hrow : ∀ i < m, ∀ j : ℕ, j ≤ d → 3 + 2 * (((d : ℤ) + 1) * i + j) + 1 < YB := fun i hi j hj => by
    have : ((d : ℤ) + 1) * (i + 1) ≤ ((d : ℤ) + 1) * m :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hi) (by positivity)
    have e : ((d : ℤ) + 1) * (i + 1) = ((d : ℤ) + 1) * i + d + 1 := by ring
    omega
  have hrow0 : ∀ i < m, ∀ j : ℕ, j ≤ d → 0 ≤ ((d : ℤ) + 1) * i + j := fun i _ j _ => by positivity
  unfold ORCB; simp only [seqL]
  -- the normalised point into the buffer
  refine RS.seq (rs_COPYN ha hYB0 hYB hd hz hAa hOne hD1 hA hC hY0 hSg hI hX hV hB0 hYz hLs hLa hLy hLYd hLd h10) ?_
  rintro n₁ t₁ ⟨hn₁, m₁, s₁⟩
  have hout : ∀ c, ¬ (YB ≤ c ∧ c ≤ YB + d) → t₁.mem c = t.mem c := fun c hc => by
    rw [m₁]; simp only [hc, ↓reduceIte]
  have e (c : ℤ) (hc : c < 0) : t₁.mem c = t.mem c := hout c (by omega)
  set Y : ℕ → ℤ := fun j => nrm (t.mem (φ a)) (t.mem (φ (a + j))) j with hYd
  have hYv : ∀ j : ℕ, j ≤ d → t₁.mem (YB + j) = Y j := fun j hj => by
    rw [m₁]; simp only [show YB ≤ YB + (j : ℤ) ∧ YB + (j : ℤ) ≤ YB + d by omega, and_self, ↓reduceIte,
      add_sub_cancel_left, hYd]
  -- the rows
  refine RS.seq (rs_ROWMEM (v0 := t₁) (m := m) (YB := YB) (M := M) (B := B) (nm := nm) (dn := dn) (Y := Y) hYB0
    (by rw [e _ (by decide)]; exact hYB) (by rw [hout 0 (by omega)]; exact hd) (by rw [hout 2 (by omega)]; exact hm)
    (by rw [e _ (by decide)]; exact hR) (by rw [e _ (by decide)]; exact hOne) (by rw [e _ (by decide)]; exact hE)
    (by rw [e _ (by decide)]; exact hI)
    (by rw [e _ (by decide)]; exact hS) (by rw [e _ (by decide)]; exact hQ) (by rw [e _ (by decide)]; exact hJ)
    (by rw [e _ (by decide)]; exact hYP) (by rw [e _ (by decide)]; exact hN) (by rw [e _ (by decide)]; exact hE1)
    (by rw [e _ (by decide)]; exact hDD) (by rw [e _ (by decide)]; exact hY) (by rw [e _ (by decide)]; exact hT)
    (by rw [e _ (by decide)]; exact hY0) (by rw [e _ (by decide)]; exact hL) (by rw [e _ (by decide)]; exact hRt)
    (fun i hi j hj => by
      have := hrow i hi j hj; have := hrow0 i hi j hj
      rw [hout _ (by omega)]; exact hnm i hi j hj)
    (fun i hi j hj => by
      have := hrow i hi j hj; have := hrow0 i hi j hj
      rw [hout _ (by omega)]; exact hdn i hi j hj)
    hYv hM1 hB hMb (fun j hj => abs_nrm_le hB (hyb j hj)) hLV hLA hLY hLm h10) ?_
  rintro n₂ t₂ ⟨hn₂, m₂, s₂⟩
  set rv := rowR d m nm dn Y with hrv
  have hφd : φ dst ≤ -1000 := φ_le dst
  have f2R : t₂.mem cR = rv := by rw [m₂, Function.update_self]
  have e2 (c : ℤ) (hc : c ≠ cR) : t₂.mem c = t₁.mem c := by rw [m₂, Function.update_of_ne hc]
  have f2Z : t₂.mem cZ = 0 := by rw [e2 _ (by decide), e _ (by decide), hz]
  have lrv : len rv ≤ L := by
    rcases rowR_cases (d := d) (k := m) (nm := nm) (dn := dn) (Y := Y) with h | h <;> rw [hrv, h]
    · exact l0
    · rw [len_one]; omega
  -- the answer into `φ dst`, `cR` back at `0`
  refine RS.seq (rs_seqI (is := [.add (φ dst) cR cZ, .const cR 0]) (t := t₂)
    ⟨⟨(len_φ _).trans hLdst, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      by rw [f2R]; exact lrv, by rw [f2Z]; exact l0⟩,
     ⟨len_scr (by decide) (by decide) h10, l0⟩, trivial⟩) ?_
  rintro n₃ t₃ ⟨hn₃, rfl⟩
  simp only [List.length_cons, List.length_nil] at hn₃
  have m3 : (runI w [.add (φ dst) cR cZ, .const cR 0] t₂).mem =
      Function.update (Function.update t₂.mem (φ dst) rv) cR 0 := by
    simp only [runI, stepI_add_mem, stepI_const_mem, f2R, f2Z, add_zero]
  have s3 : Same' t₂ (runI w [.add (φ dst) cR cZ, .const cR 0] t₂) := runI_same (by simp [Plain, NJ])
  set t₃ := runI w [.add (φ dst) cR cZ, .const cR 0] t₂ with ht₃
  have e3 (c : ℤ) (h1 : c ≠ cR) (h2 : -1000 < c) (h3 : ¬ (YB ≤ c ∧ c ≤ YB + d)) : t₃.mem c = t.mem c := by
    rw [m3, Function.update_of_ne h1, Function.update_of_ne (by omega), e2 _ h1, hout _ h3]
  -- the buffer back at `0`
  refine (rs_CLEARY (YB := YB) (by rw [e3 _ (by decide) (by decide) (by omega)]; exact hz)
    (by rw [e3 _ (by decide) (by decide) (by omega)]; exact hd)
    (by rw [e3 _ (by decide) (by decide) (by omega)]; exact hYB) hYB0
    (by rw [e3 _ (by decide) (by decide) (by omega)]; exact hOne)
    (by rw [e3 _ (by decide) (by decide) (by omega)]; exact hD1)
    (by rw [e3 _ (by decide) (by decide) (by omega)]; exact hI)
    (by rw [e3 _ (by decide) (by decide) (by omega)]; exact hB0) hLYd hLd h10).mono ?_
  rintro n₄ t₄ ⟨hn₄, m₄, s₄⟩
  refine ⟨by omega, ?_, ((s₁.trans s₂).trans s3).trans s₄⟩
  rw [m₄]
  funext c
  by_cases hc : YB ≤ c ∧ c ≤ YB + d
  · simp only [hc, and_self, ↓reduceIte]
    rw [Function.update_of_ne (by omega), hYz c hc.1 hc.2]
  · simp only [hc, ↓reduceIte]
    rw [m3]
    by_cases hcR : c = cR
    · subst hcR; rw [Function.update_self, Function.update_of_ne (by omega), hR]
    · rw [Function.update_of_ne hcR]
      by_cases hcd : c = φ dst
      · subst hcd; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hcd, Function.update_of_ne hcd, e2 _ hcR, hout _ hc]

end AdversarialBco.UniPoly
