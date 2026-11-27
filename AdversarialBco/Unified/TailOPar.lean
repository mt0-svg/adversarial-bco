/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.TailOSpec

@[expose] public section

/-!
# BL-O's PARAM in the tail's cells

The facts on PARAM that the tail reads, at `parN ne d n`: the fields on the grid `2^{-pF}`, `1/ê` as the integer
`tlHN ne d n`, and the integer constants of BL's invariant (`tl_constsO`).
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St CallQ init LT Lmu eBL)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

theorem tlN_onG_eta (ne d n : ℕ) : OnG (parN ne d n).pF (parN ne d n).eta := onG_div_pow _ _
theorem tlN_onG_rho (ne d n : ℕ) : OnG (parN ne d n).pF (parN ne d n).rho := onG_div_pow _ _
theorem tlN_onG_W (ne d n : ℕ) : OnG (parN ne d n).pF (parN ne d n).W := onG_div_pow _ _
theorem tlN_onG_eps (ne d n : ℕ) : OnG (parN ne d n).pF (parN ne d n).eps := onG_div_pow _ _
theorem tlN_onG_kapc (ne d n : ℕ) : OnG (parN ne d n).pF (parN ne d n).kapc := onG_div_pow _ _
theorem tlN_onG_nu (ne d n : ℕ) : OnG (parN ne d n).pF (parN ne d n).nu := onG_div_pow _ _

/-- `1/ê` as an integer. -/
def tlHN (ne d n : ℕ) : ℤ := 2 ^ ((parN ne d n).p - 3 * ne.size - 6 * d.size - 64)

theorem tlHN_pos (ne d n : ℕ) : 0 < tlHN ne d n := by unfold tlHN; positivity

theorem tlN_eHat (ne d n : ℕ) : (parN ne d n).eHat = 1 / ((tlHN ne d n : ℤ) : ℚ) := by
  rw [tlHN]; push_cast; rfl

theorem tlHN_eq (ne d n : ℕ) : (((parN ne d n).eHat⁻¹ : ℚ) : ℝ) = ((tlHN ne d n : ℤ) : ℝ) := by
  rw [tlN_eHat, one_div, inv_inv]; push_cast; rfl

/-- The integer constants of `BLInv` that the tail reads, at `parN ne d n`. -/
theorem tl_constsO {L : Layout} {n m K0 E ne : ℕ} {cfg : Cfg d} (hpar : cfg.par = parN ne d n) {mo : Mode d}
    {t : ℕ} {σ : Env d} (h : BLInv L n m K0 E cfg mo t σ) :
    σ.sc s2p = (((2 : ℤ) ^ cfg.par.p : ℤ) : ℝ) ∧ |(2 : ℤ) ^ cfg.par.p| ≤ 2 ^ E ∧
    σ.sc s2pF = (((2 : ℤ) ^ cfg.par.pF : ℤ) : ℝ) ∧ |(2 : ℤ) ^ cfg.par.pF| ≤ 2 ^ E ∧
    σ.sc s2g = (((2 : ℤ) ^ (2 * gsm_prec cfg.par.B) : ℤ) : ℝ) ∧ |(2 : ℤ) ^ (2 * gsm_prec cfg.par.B)| ≤ 2 ^ E ∧
    σ.sc s2eh = ((tlHN ne d n : ℤ) : ℝ) ∧ |tlHN ne d n| ≤ 2 ^ E ∧
    σ.sc sLam = ((cfg.par.Lam : ℤ) : ℝ) ∧ |(cfg.par.Lam : ℤ)| ≤ 2 ^ E ∧
    σ.sc sRint = ((cfg.par.Rint : ℤ) : ℝ) ∧ |(cfg.par.Rint : ℤ)| ≤ 2 ^ E ∧
    σ.sc sEta = ((qn cfg.par.pF cfg.par.eta : ℤ) : ℝ) ∧ |qn cfg.par.pF cfg.par.eta| ≤ 2 ^ E ∧
    σ.sc sRho = ((qn cfg.par.pF cfg.par.rho : ℤ) : ℝ) ∧ |qn cfg.par.pF cfg.par.rho| ≤ 2 ^ E ∧
    σ.sc sW = ((qn cfg.par.pF cfg.par.W : ℤ) : ℝ) ∧ |qn cfg.par.pF cfg.par.W| ≤ 2 ^ E := by
  obtain ⟨-, -, c2, c3, c4, c5, -, c7, c8⟩ := h.consts
  obtain ⟨-, -, p2, p3, -, -, -, -, p8, -⟩ := h.par
  have e2 : σ.sc s2p = (((2 : ℤ) ^ cfg.par.p : ℤ) : ℝ) := by rw [c2]; push_cast; rfl
  have e3 : σ.sc s2pF = (((2 : ℤ) ^ cfg.par.pF : ℤ) : ℝ) := by rw [c3]; push_cast; rfl
  have e4 : σ.sc s2g = (((2 : ℤ) ^ (2 * gsm_prec cfg.par.B) : ℤ) : ℝ) := by rw [c4]; push_cast; rfl
  have e5 : σ.sc s2eh = ((tlHN ne d n : ℤ) : ℝ) := by rw [c5, hpar]; exact tlHN_eq ne d n
  have e7 : σ.sc sLam = ((cfg.par.Lam : ℤ) : ℝ) := by rw [c7]; push_cast; rfl
  have e8 : σ.sc sRint = ((cfg.par.Rint : ℤ) : ℝ) := by rw [c8]; push_cast; rfl
  exact ⟨e2, h.slot_abs (by decide) e2, e3, h.slot_abs (by decide) e3, e4, h.slot_abs (by decide) e4, e5,
    h.slot_abs (by decide) e5, e7, h.slot_abs (by decide) e7, e8, h.slot_abs (by decide) e8, p2,
    h.slot_abs (by decide) p2, p3, h.slot_abs (by decide) p3, p8, h.slot_abs (by decide) p8⟩

theorem NeO_pos {d n : ℕ} (k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : 1 ≤ NeO d n k := by
  unfold NeO
  have h1 : 0 < 2 ^ (17 + k) := by positivity
  have h2 : 0 < d ^ 3 := pow_pos (by omega) 3
  have h3 : 0 < n ^ 4 := pow_pos (by omega) 4
  have : 0 < 15 * 2 ^ (17 + k) * d ^ 3 * n ^ 4 := by positivity
  omega

end AdversarialBco.Unified.ProgO
