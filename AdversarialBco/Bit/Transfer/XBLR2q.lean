/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLR2p
public import AdversarialBco.Bit.Transfer.XBLInt
public import AdversarialBco.Conj1Bit.Sanity

@[expose] public section

/-!
# BL's round, R2 PLAYPT in mode `run`: the integers of the machine are BL's rationals

The input rows as the input cells hold them (`NmI`, `DnI`: numerator and denominator of each entry), the cleared row
`rowA` over the product of its denominators (`rowA_cast`), BL's point `X'` over one common
denominator (`XQ_int`), and the play from the gauge (`playPt_mach`).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open Matrix AdversarialBco.BitRAM AdversarialBco.Bit.BLP

variable {d : ℕ}

/-- The numerator of the entry `j` of the input row `r`, from its input cell. -/
def NmI (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (r j : ℕ) : ℤ :=
  inputMem d n m A b ((3 + 2 * ((d + 1) * r + j) : ℕ) : ℤ)

/-- The denominator of the entry `j` of the input row `r`, from its input cell. -/
def DnI (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (r j : ℕ) : ℤ :=
  inputMem d n m A b ((4 + 2 * ((d + 1) * r + j) : ℕ) : ℤ)

/-- The product of the denominators of the input row `r`. -/
def PiI (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (r : ℕ) : ℤ :=
  ∏ j' ∈ Finset.range (d + 1), DnI d n m A b r j'

section Rows

variable {n m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)

theorem NmI_eq (i : Fin m) {j : ℕ} (hj : j ≤ d) : NmI d n m A b i j = (entry A b i j).num :=
  Conj1BitSanity.inputMem_num A b i j hj

theorem DnI_eq (i : Fin m) {j : ℕ} (hj : j ≤ d) : DnI d n m A b i j = (entry A b i j).den :=
  Conj1BitSanity.inputMem_den A b i j hj

theorem PiI_pos (i : Fin m) : 0 < PiI d n m A b i :=
  Finset.prod_pos fun j hj => by
    rw [DnI_eq A b i (by simp only [Finset.mem_range] at hj; omega)]
    exact_mod_cast (entry A b i j).den_pos

/-- The cleared entry is the entry times the product of the denominators of its row. -/
theorem rowA_cast (i : Fin m) {j : ℕ} (hj : j ≤ d) :
    (rowA (NmI d n m A b) (DnI d n m A b) d i j : ℚ) = entry A b i j * (PiI d n m A b i : ℚ) := by
  have hdv : DnI d n m A b i j ∣ PiI d n m A b i :=
    Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (by omega))
  have hD0 : (DnI d n m A b i j : ℚ) ≠ 0 := by
    rw [DnI_eq A b i hj]; exact_mod_cast (entry A b i j).den_nz
  unfold rowA
  rw [show (∏ j' ∈ Finset.range (d + 1), DnI d n m A b i j') = PiI d n m A b i from rfl, Int.cast_mul,
    Int.cast_div hdv hD0]
  conv_rhs => rw [← Rat.num_div_den (entry A b i j)]
  rw [NmI_eq A b i hj, DnI_eq A b i hj] at *
  unfold PiI
  push_cast
  field_simp

/-- The row `a_i` over the product of its denominators. -/
theorem rowA_A (i : Fin m) (k : Fin d) :
    (rowA (NmI d n m A b) (DnI d n m A b) d i k : ℚ) / (PiI d n m A b i : ℚ) = A i k := by
  have hP : (PiI d n m A b i : ℚ) ≠ 0 := by exact_mod_cast (PiI_pos A b i).ne'
  rw [rowA_cast A b i k.2.le, mul_div_assoc, div_self hP, mul_one]
  simp [entry]

/-- `b_i` over the product of the denominators of row `i`. -/
theorem rowA_b (i : Fin m) :
    (rowA (NmI d n m A b) (DnI d n m A b) d i d : ℚ) / (PiI d n m A b i : ℚ) = b i := by
  have hP : (PiI d n m A b i : ℚ) ≠ 0 := by exact_mod_cast (PiI_pos A b i).ne'
  rw [rowA_cast A b i le_rfl, mul_div_assoc, div_self hP, mul_one]
  simp [entry]

/-- A row with `a_i = 0` has `â_i = 0`. -/
theorem rowA_zero (i : Fin m) (h : A i = 0) (k : Fin d) : rowA (NmI d n m A b) (DnI d n m A b) d i k = 0 := by
  have h1 := rowA_A (n := n) A b i k
  rw [h, Pi.zero_apply, div_eq_zero_iff] at h1
  rcases h1 with h1 | h1
  · exact_mod_cast h1
  · exact absurd h1 (by exact_mod_cast (PiI_pos A b i).ne')

end Rows

/-- BL's point `X = μ + (1 - λ) A ξ` with `μ = μ̂/Dμ`, `λ = λ̂/PF`, `A = Â/P`, `ξ = Γ/G`, over the common denominator
`Dμ PF P G`. -/
theorem XQ_int (Dm PF P G lh : ℤ) (muh : Fin d → ℤ)
    (ah : Fin d → Fin d → ℤ) (gam : Fin d → ℤ) (hDm : 0 < Dm) (hPF : 0 < PF) (hP : 0 < P) (hG : 0 < G) (j : Fin d) :
    ((fun j => (muh j : ℚ) / Dm) + (1 - (lh : ℚ) / PF) • ((Matrix.of fun i k => (ah i k : ℚ) / P) *ᵥ
        fun k => (gam k : ℚ) / G)) j =
      ((muh j * PF * P * G + (PF - lh) * (∑ k, ah j k * gam k) * Dm : ℤ) : ℚ) / ((Dm * PF * P * G : ℤ) : ℚ) := by
  have h1 : (Dm : ℚ) ≠ 0 := by exact_mod_cast hDm.ne'
  have h2 : (PF : ℚ) ≠ 0 := by exact_mod_cast hPF.ne'
  have h3 : (P : ℚ) ≠ 0 := by exact_mod_cast hP.ne'
  have h4 : (G : ℚ) ≠ 0 := by exact_mod_cast hG.ne'
  have hs : ((Matrix.of fun i k => (ah i k : ℚ) / P) *ᵥ fun k => (gam k : ℚ) / G) j =
      ((∑ k, ah j k * gam k : ℤ) : ℚ) / (P * G) := by
    simp only [mulVec, dotProduct, of_apply]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs]
  push_cast
  field_simp

/-- **The play of mode `run` from the machine's integers.** With `X' = X̂/D_X`, the gauge `b_N/b_D` (`b_D > 0`), `ε'`
on the grid `2^{-pF}` below `1`, and `(pt_N, pt_D) = ptPair b_N b_D 2^pF ε̂`: BL's play is the point with the
denominator `D_S D_X pt_N` and the numerators `μ̂_{S,j} D_X pt_N + (Â_S X̂)_j pt_D`. -/
theorem playPt_mach (cfg : Cfg d) (st : St d) (ξ : Fin d → ℚ) (DS DX bN bD : ℤ) (muS xh : Fin d → ℤ)
    (aS : Fin d → Fin d → ℤ) (hDS : 0 < DS) (hDX : 0 < DX) (hbD : 0 < bD)
    (hmu : ∀ j, (muS j : ℚ) / DS = cfg.μS j) (hA : ∀ i j, (aS i j : ℚ) / DS = cfg.AS i j)
    (hX : ∀ j, XQ cfg st ξ j = (xh j : ℚ) / DX) (hg : (bN : ℚ) / bD = gaugeQ cfg (XQ cfg st ξ))
    (heps : OnG cfg.par.pF cfg.par.eps) (he1 : cfg.par.eps < 1) :
    0 < (ptPair bN bD (2 ^ cfg.par.pF) (qn cfg.par.pF cfg.par.eps)).1 ∧
      0 < (ptPair bN bD (2 ^ cfg.par.pF) (qn cfg.par.pF cfg.par.eps)).2 ∧
      ∀ j, playPt cfg (.run st) ξ j =
        ((muS j * DX * (ptPair bN bD (2 ^ cfg.par.pF) (qn cfg.par.pF cfg.par.eps)).1 +
            (∑ k, aS j k * xh k) * (ptPair bN bD (2 ^ cfg.par.pF) (qn cfg.par.pF cfg.par.eps)).2 : ℤ) : ℚ) /
          ((DS * DX * (ptPair bN bD (2 ^ cfg.par.pF) (qn cfg.par.pF cfg.par.eps)).1 : ℤ) : ℚ) := by
  set F : ℤ := 2 ^ cfg.par.pF with hF
  set eh := qn cfg.par.pF cfg.par.eps with heh
  have hF0 : (0 : ℚ) < (F : ℚ) := by rw [hF]; push_cast; positivity
  have heF : (eh : ℚ) = cfg.par.eps * F := by rw [heh, heps, hF]; push_cast; ring
  have he : eh < F := by
    have : (eh : ℚ) < F := by rw [heF]; nlinarith
    exact_mod_cast this
  obtain ⟨hN, hD⟩ := ptPair_pos (bN := bN) hbD he
  refine ⟨hN, hD, fun j => ?_⟩
  have hpt : ptQ cfg (XQ cfg st ξ) =
      ((ptPair bN bD F eh).1 : ℚ) / (ptPair bN bD F eh).2 := by
    have hε : cfg.par.eps = (eh : ℚ) / F := by rw [heF]; field_simp
    unfold ptQ
    rw [← hg, hε, ptQ_int bN bD eh F hbD (by exact_mod_cast hF0) he]
    unfold ptPair
    split_ifs <;> simp
  have hXf : XQ cfg st ξ = fun k => (xh k : ℚ) / DX := funext hX
  have hmuf : cfg.μS = fun j => (muS j : ℚ) / DS := funext fun j => (hmu j).symm
  have hAf : cfg.AS = Matrix.of fun i k => (aS i k : ℚ) / DS := by
    ext i k; exact (hA i k).symm
  have := play_int DS DX (ptPair bN bD F eh).1 (ptPair bN bD F eh).2 muS aS xh hDS hDX hN hD j
  rw [← hpt, ← hXf, ← hmuf, ← hAf] at this
  rw [← this]
  rfl

end AdversarialBco.Bit.Transfer.BLM
