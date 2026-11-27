/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOR2a

@[expose] public section

/-!
# BL-O's R2 in mode `run`: the integers of the machine are BL-O's rationals

The gauge `gaugeP` of `X' = X̂/D_X` from the counter of the bisection run on `H_n' = hnG H_n` (`gaugeP_mach`: the
pair `(H_n u, D_X 2^jG)`), then the scale `ptO` and the play `playPtO` from that pair (`playPtO_mach`).
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

theorem ptDN_one_zero : ptDN (d := d) 1 0 = 0 := by funext i; simp [ptDN]

theorem l1_ptDN {DX : ℤ} (hDX : 0 < DX) (xh : Fin d → ℤ) :
    l1 (ptDN DX xh) = ((∑ k, |xh k| : ℤ) : ℚ) / DX := by
  have hD : (0 : ℚ) < DX := by exact_mod_cast hDX
  unfold l1 ptDN
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [abs_div, abs_of_pos hD]

theorem ptDN_eq_zero {DX : ℤ} (hDX : 0 < DX) (xh : Fin d → ℤ) : ptDN DX xh = 0 ↔ ∑ k, |xh k| = 0 := by
  have hD : (DX : ℚ) ≠ 0 := by exact_mod_cast hDX.ne'
  constructor
  · intro h
    refine Finset.sum_eq_zero fun k _ => ?_
    have := congrFun h k
    simp only [ptDN, Pi.zero_apply, div_eq_zero_iff, Int.cast_eq_zero] at this
    rcases this with h' | h'
    · simp [h']
    · exact absurd h' hDX.ne'
  · intro h
    funext k
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => abs_nonneg (xh k))).1 h k (Finset.mem_univ _)
    simp [ptDN, abs_eq_zero.1 this]

/-- **The gauge from the machine's counter**: with `S = Σ_k |X̂_k|`, the bisection run on `hnG (2S)/D_X` about
`0 = (1; 0)` gives `gaugeP orc c (X̂/D_X) = 2 S u/(D_X 2^jG)`. -/
theorem gaugeP_mach (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) {DX : ℤ} (hDX : 0 < DX) (xh : Fin d → ℤ)
    (T : (Fin d → ℚ) → Bool) (hT : T = c.T orc c.kC 1) :
    gaugeP orc c (ptDN DX xh) = ((2 * (∑ k, |xh k|) * ((gaugeIt T (ptDN 1 0) (ptDN DX xh)
      ((hnG (2 * ∑ k, |xh k|) : ℤ) / DX : ℚ) c.jG c.jG).2 : ℤ) : ℤ) : ℚ) / ((DX * 2 ^ c.jG : ℤ) : ℚ) := by
  have hD : (DX : ℚ) ≠ 0 := by exact_mod_cast hDX.ne'
  have hS0 : 0 ≤ ∑ k, |xh k| := Finset.sum_nonneg fun k _ => abs_nonneg _
  rcases hS0.lt_or_eq with hS | hS
  · have hX : ptDN DX xh ≠ 0 := fun h => by rw [(ptDN_eq_zero hDX xh).1 h] at hS; exact lt_irrefl _ hS
    have hH : ((hnG (2 * ∑ k, |xh k|) : ℤ) : ℚ) / DX = 2 * l1 (ptDN DX xh) := by
      rw [l1_ptDN hDX, hnG, ite_eq_left (by omega)]; push_cast; ring
    unfold gaugeP gaugeQ
    rw [ite_eq_right hX, ← hT, hH, ptDN_one_zero]
    field_simp
    push_cast
    rw [l1_ptDN hDX]
    field_simp
    push_cast
    ring
  · have hX : ptDN DX xh = 0 := (ptDN_eq_zero hDX xh).2 hS.symm
    unfold gaugeP
    rw [ite_eq_left hX, ← hS]
    simp

/-- **BL-O's scale and play from the machine's integers** (`ptO`, `playPtO`). -/
theorem playPtO_mach (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (st : St d) (ξ : Fin d → ℚ)
    (DS DX bN bD : ℤ) (muS xh : Fin d → ℤ) (aS : Fin d → Fin d → ℤ) (hDS : 0 < DS) (hDX : 0 < DX) (hbD : 0 < bD)
    (hmu : ∀ j, (muS j : ℚ) / DS = c.μS j) (hA : ∀ i j, (aS i j : ℚ) / DS = c.AS i j)
    (hX : ∀ j, XO c st ξ j = (xh j : ℚ) / DX) (hg : (bN : ℚ) / bD = gaugeP orc c (XO c st ξ))
    (heps : OnG c.par.pF c.par.eps) (he1 : c.par.eps < 1) :
    0 < (ptPair bN bD (2 ^ c.par.pF) (qn c.par.pF c.par.eps)).1 ∧
      0 < (ptPair bN bD (2 ^ c.par.pF) (qn c.par.pF c.par.eps)).2 ∧
      ptO orc c (XO c st ξ) = ((ptPair bN bD (2 ^ c.par.pF) (qn c.par.pF c.par.eps)).1 : ℚ) /
        (ptPair bN bD (2 ^ c.par.pF) (qn c.par.pF c.par.eps)).2 ∧
      ∀ j, playPtO orc c (.run st) ξ j =
        ((muS j * DX * (ptPair bN bD (2 ^ c.par.pF) (qn c.par.pF c.par.eps)).1 +
            (∑ k, aS j k * xh k) * (ptPair bN bD (2 ^ c.par.pF) (qn c.par.pF c.par.eps)).2 : ℤ) : ℚ) /
          ((DS * DX * (ptPair bN bD (2 ^ c.par.pF) (qn c.par.pF c.par.eps)).1 : ℤ) : ℚ) := by
  set F : ℤ := 2 ^ c.par.pF with hF
  set eh := qn c.par.pF c.par.eps with heh
  have hF0 : (0 : ℚ) < (F : ℚ) := by rw [hF]; push_cast; positivity
  have heF : (eh : ℚ) = c.par.eps * F := by rw [heh, heps, hF]; push_cast; ring
  have he : eh < F := by
    have : (eh : ℚ) < F := by rw [heF]; nlinarith
    exact_mod_cast this
  obtain ⟨hN, hD⟩ := ptPair_pos (bN := bN) hbD he
  have hpt : ptO orc c (XO c st ξ) = ((ptPair bN bD F eh).1 : ℚ) / (ptPair bN bD F eh).2 := by
    have hε : c.par.eps = (eh : ℚ) / F := by rw [heF]; field_simp
    unfold ptO
    rw [← hg, hε, ptQ_int bN bD eh F hbD (by exact_mod_cast hF0) he]
    unfold ptPair
    split_ifs <;> simp
  refine ⟨hN, hD, hpt, fun j => ?_⟩
  have hXf : XO c st ξ = fun k => (xh k : ℚ) / DX := funext hX
  have hmuf : c.μS = fun j => (muS j : ℚ) / DS := funext fun j => (hmu j).symm
  have hAf : c.AS = Matrix.of fun i k => (aS i k : ℚ) / DS := by
    ext i k; exact (hA i k).symm
  have := play_int DS DX (ptPair bN bD F eh).1 (ptPair bN bD F eh).2 muS aS xh hDS hDX hN hD j
  rw [← hpt, ← hXf, ← hmuf, ← hAf] at this
  rw [← this]
  rfl

end AdversarialBco.Unified.ProgO
