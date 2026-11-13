/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.ApQ.Ell

@[expose] public section

/-!
# Piece (B) of (PROG-CUT): the frame bounds of `frameQ`

`frameQ_ball`: on `InputOK`, the frame centre `c = frameQ d n m A b` of Bit/RoutQ.lean has
`B̄(c, 1/2) ⊆ K ⊆ B̄(c, n)`, `K = polytope A b` (the frame theorem (i)).

* `d ≥ 2`: Theorem ELL-F (b). `frLoop_main` carries the claim `I_k` (`FInv`) with `ellUpd_step` of Bit/ApQ/Step.lean
  at `ρ = 1/2` (`j = 1`) and ends on the volume count `pb_ell_det_contra`; the start ball `B(0, R)`, `R = 2^{e_R}`,
  contains `B' = B̄(z, 1/2)` by the localisation lemma (`polytope_sub_ball`); a returned point lies in the margin region
  `Q` of the
  cleared rows, and `B̄(c, 1/2) ⊆ K` is the margin (`fr_margin_iff`, `fr_cleared_row`).
* `d = 1`: the read-off `frame1` (`fr_d1_signs`, `fr_d1_readoff`, `fr_d1_centre` of Bit/Frame.lean).
-/

namespace AdversarialBco.Bit.ApQ

open AdversarialBco.Bit.RQ
open AdversarialBco.Poly (oNorm oBall)
open AdversarialBco.RealRAM (polytope HeightLE)
open AdversarialBco.BitRAM (toE)
open AdversarialBco.Bit.Asm (InputOK)
open AdversarialBco.Conj1Poly (polytope_sub_ball isCompact_polytope Rloc)
open Matrix

variable {d m : ℕ}

/-! ## The margin region `Q` and the row test -/

/-- The region `Q = {y | α_i·y + |α_i|/2 ≤ β_i for every i}` of Theorem ELL-F on integer rows. -/
def QF (al : Fin m → Fin d → ℤ) (be : Fin m → ℤ) : Set (Fin d → ℝ) :=
  {y | ∀ i, ∑ j, (al i j : ℝ) * y j + 1 / 2 * Real.sqrt (∑ j, (al i j : ℝ) ^ 2) ≤ be i}

/-- Row `i` fails the test of step 1 at `â` (`D < 0` or `D² < nn_i`, `D = 2^{p+1} β_i - 2 α_i·â`). -/
def rowFail (p : ℕ) (al : Fin m → Fin d → ℤ) (be : Fin m → ℤ) (a : Fin d → ℤ) (i : Fin m) : Prop :=
  2 ^ (p + 1) * be i - 2 * (al i ⬝ᵥ a) < 0 ∨
    (2 ^ (p + 1) * be i - 2 * (al i ⬝ᵥ a)) ^ 2 < 2 ^ (2 * p) * (al i ⬝ᵥ al i)

/-- The claim `I_k` of Theorem ELL-F (b): `A_k ≻ 0`, `B' ⊆ E_k`, `λ_max(A_k) ≤ R² γ^k`, `det A_k ≤ R^{2d} e^{-ωk}`. -/
def FInv (p : ℕ) (R : ℝ) (z0 : Fin d → ℝ) (k : ℕ) (A : Matrix (Fin d) (Fin d) ℤ) (a : Fin d → ℤ) : Prop :=
  Aᵀ = A ∧ (mR p A).PosDef ∧ (∀ x, InB z0 (1 / 2 ^ 1) x → InE (mR p A) (vR p a) x) ∧
    (∀ v, v ⬝ᵥ (mR p A *ᵥ v) ≤ R ^ 2 * gam d ^ k * (v ⬝ᵥ v)) ∧
    (mR p A).det ≤ R ^ (2 * d) * Real.exp (-(95 / (128 * ((d : ℝ) + 1))) * k)

/-- `Λ = R² 2^{6λ_e + 2}`, `R = 2^{e_R}`, `λ_e = e_R + 1`. -/
noncomputable def LamF (eR : ℕ) : ℝ := ((2 : ℝ) ^ eR) ^ 2 * 2 ^ (6 * (eR + 1) + 2)

/-! ## Leaves: the row test and the constants of F3 -/

theorem rowPass_iff (p : ℕ) (al : Fin m → Fin d → ℤ) (be : Fin m → ℤ) (a : Fin d → ℤ) (i : Fin m) :
    ¬ rowFail p al be a i ↔
      ∑ j, (al i j : ℝ) * vR p a j + 1 / 2 * Real.sqrt (∑ j, (al i j : ℝ) ^ 2) ≤ be i := by
  unfold rowFail
  simp only [not_or, not_lt]
  exact fr_test_sq (al i) a (be i) p

theorem rowFail_cut (p : ℕ) (al : Fin m → Fin d → ℤ) (be : Fin m → ℤ) (a : Fin d → ℤ) (i : Fin m)
    (hf : rowFail p al be a i) (x : Fin d → ℝ) (hx : x ∈ QF al be) : vZ (al i) ⬝ᵥ (x - vR p a) < 0 := by
  have h1 : ¬ (∑ j, (al i j : ℝ) * vR p a j + 1 / 2 * Real.sqrt (∑ j, (al i j : ℝ) ^ 2) ≤ be i) :=
    fun h => (rowPass_iff p al be a i).mpr h hf
  have h2 := hx i
  have h3 : vZ (al i) ⬝ᵥ (x - vR p a) = ∑ j, (al i j : ℝ) * x j - ∑ j, (al i j : ℝ) * vR p a j := by
    simp only [vZ, dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [h3]
  have h4 := lt_of_not_ge h1
  linarith

theorem frP_prec (hd : 1 ≤ d) :
    (1 : ℝ) / 2 ^ frP d ≤ (1 / 2 ^ 1) ^ 2 / (64 * (d : ℝ) ^ 2 * ((d : ℝ) + 1)) := by
  unfold frP
  have hc' : ((d : ℝ) ^ 2 * (d + 1)) ≤ 2 ^ Nat.clog 2 (d ^ 2 * (d + 1)) := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) (d ^ 2 * (d + 1))
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rw [pow_add, div_pow, one_pow, div_div, one_div_le_one_div (by positivity) (by positivity)]
  rw [show ((2 : ℝ) ^ 1) ^ 2 * (64 * (d : ℝ) ^ 2 * ((d : ℝ) + 1)) = 2 ^ 8 * ((d : ℝ) ^ 2 * (d + 1)) by norm_num; ring]
  exact mul_le_mul_of_nonneg_left hc' (by positivity)

theorem two_le_frP : 2 * 1 ≤ frP d := by
  unfold frP
  omega

theorem sqrt_LamF (eR : ℕ) : Real.sqrt (LamF eR) = 2 ^ (eR + 3 * (eR + 1) + 1) := by
  unfold LamF
  rw [show ((2 : ℝ) ^ eR) ^ 2 * 2 ^ (6 * (eR + 1) + 2) = (2 ^ (eR + 3 * (eR + 1) + 1)) ^ 2 by ring]
  exact Real.sqrt_sq (by positivity)

theorem frQ_prec (hd : 1 ≤ d) (eR : ℕ) :
    4 / (1 / 2 ^ 1 : ℝ) ≤ 2 ^ frQ d eR ∧
      4 * Real.sqrt (LamF eR) / (1 / 2 ^ 1 * 2 ^ frQ d eR) ≤ 1 / 2 ^ 1 / (64 * d) := by
  have hq : (2 : ℝ) ^ frQ d eR = 2 ^ 14 * 2 ^ (Nat.clog 2 d) * 2 ^ (4 * eR) := by
    unfold frQ
    ring
  have hdc : (d : ℝ) ≤ 2 ^ Nat.clog 2 d := by exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) d
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  constructor
  · rw [hq]
    have h1 : (1 : ℝ) ≤ 2 ^ Nat.clog 2 d := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ 2 ^ (4 * eR) := one_le_pow₀ (by norm_num)
    rw [show (4 : ℝ) / (1 / 2 ^ 1) = 8 by norm_num]
    calc (8 : ℝ) ≤ 2 ^ 14 * 1 * 1 := by norm_num
      _ ≤ _ := by gcongr
  · rw [sqrt_LamF, hq, div_le_div_iff₀ (by positivity) (by positivity)]
    calc 4 * (2 : ℝ) ^ (eR + 3 * (eR + 1) + 1) * (64 * d) = 2 ^ 12 * d * 2 ^ (4 * eR) := by ring
      _ ≤ 2 ^ 12 * 2 ^ Nat.clog 2 d * 2 ^ (4 * eR) := by gcongr
      _ = _ := by ring

theorem capA_F (p eR : ℕ) : (2 : ℝ) ^ p * LamF eR ≤ (((2 : ℤ) ^ (p + 2 * eR + 6 * (eR + 1) + 2) : ℤ) : ℝ) := by
  unfold LamF
  push_cast
  apply le_of_eq
  ring

theorem capa_F (p eR : ℕ) (z : ℝ) (hz : |z| ≤ 2 ^ eR) :
    (2 : ℝ) ^ p * (|z| + Real.sqrt (LamF eR)) ≤ (((2 : ℤ) ^ p * (2 ^ eR + 2 ^ (eR + 3 * (eR + 1) + 1)) : ℤ) : ℝ) := by
  rw [sqrt_LamF]
  push_cast
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem cap_F (hd : 2 ≤ d) (eR k : ℕ) (hk : k ≤ frN d eR) : ((2 : ℝ) ^ eR) ^ 2 * gam d ^ k ≤ LamF eR := by
  have h := pb_cap_general d (eR + 1) k hd (by unfold frN at hk; exact hk)
  unfold LamF
  exact mul_le_mul_of_nonneg_left h (by positivity)

theorem frN_cast (eR : ℕ) : (frN d eR : ℝ) = 2 * d * ((d : ℝ) + 1) * (eR + 1 : ℕ) + 1 := by
  unfold frN
  push_cast
  ring

theorem start_F (p eR : ℕ) :
    mR p (((2 : ℤ) ^ (p + 2 * eR)) • (1 : Matrix (Fin d) (Fin d) ℤ)) =
      (((2 : ℝ) ^ eR) ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  ext i k
  by_cases h : i = k
  · subst h
    simp only [mR, Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    push_cast
    rw [pow_add, ← pow_mul]
    field_simp
    ring
  · simp only [mR, Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply_ne h, smul_eq_mul, mul_zero, Int.cast_zero]

theorem start_symm (p eR : ℕ) :
    (((2 : ℤ) ^ (p + 2 * eR)) • (1 : Matrix (Fin d) (Fin d) ℤ))ᵀ = ((2 : ℤ) ^ (p + 2 * eR)) • 1 := by
  rw [Matrix.transpose_smul, Matrix.transpose_one]

theorem vR_zero (p : ℕ) : vR p (0 : Fin d → ℤ) = 0 := by
  funext i
  simp [vR]

theorem quad_scalar (c : ℝ) (v : Fin d → ℝ) : v ⬝ᵥ ((c • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ v) = c * (v ⬝ᵥ v) := by
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]

theorem det_scalar (c : ℝ) : (c ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ)).det = c ^ (2 * d) := by
  rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, ← pow_mul]

theorem inE_scalar' (c : ℝ) (hc : 0 < c) (x : Fin d → ℝ) (h : x ⬝ᵥ x ≤ c) :
    InE (c • (1 : Matrix (Fin d) (Fin d) ℝ)) 0 x := by
  rw [inE_scalar c hc, sub_zero]
  exact h

/-! ## ELL-F: the iterations (Theorem ELL-F (b)) -/

theorem inB_self' (z0 : Fin d → ℝ) (ρ : ℝ) : InB z0 ρ z0 := by
  unfold InB
  rw [sub_self, dotProduct_zero]
  positivity

theorem frLoop_main (hd : 2 ≤ d) (eR : ℕ) (al : Fin m → Fin d → ℤ) (be : Fin m → ℤ) (z0 : Fin d → ℝ)
    (hz : ∀ x, InB z0 (1 / 2 ^ 1) x → x ∈ QF al be) (hzR : oNorm z0 ≤ 2 ^ eR) :
    ∀ n k A a, k + n = frN d eR → FInv (frP d) (2 ^ eR) z0 k A a →
      ∃ x, frLoop (frP d) (frQ d eR) (2 ^ (frP d + 2 * eR + 6 * (eR + 1) + 2))
        (2 ^ frP d * (2 ^ eR + 2 ^ (eR + 3 * (eR + 1) + 1))) al (fun i => 2 ^ (frP d + 1) * be i)
        (fun i => 2 ^ (2 * frP d) * (al i ⬝ᵥ al i)) n A a = some x ∧ vR (frP d) x ∈ QF al be := by
  have hd1 : 1 ≤ d := by omega
  have hρ : (0 : ℝ) < 1 / 2 ^ 1 := by norm_num
  have hz0 := inB_self' z0 (1 / 2 ^ 1)
  have hR0 : (0 : ℝ) < 2 ^ eR := by positivity
  intro n
  induction n with
  | zero =>
    intro k A a hk hinv
    exfalso
    obtain ⟨_, hpd, hb, _, hdet⟩ := hinv
    have hq := pb_ball_quad (mR (frP d) A) hpd (vR (frP d) a) _ hρ
      (pb_ball_sym (mR (frP d) A) hpd (vR (frP d) a) z0 _ (fun x hx => hb x hx))
    have hdet0 := pb_ball_det (mR (frP d) A) hpd _ hρ.le hq
    have hk' : k = frN d eR := by omega
    have hcontra := pb_ell_det_contra d (eR + 1) hd1 (2 ^ eR) (1 / 2 ^ 1) _ hρ hR0
      (by rw [div_le_iff₀ hρ, pow_succ]; exact le_of_eq (by ring))
      (hdet.trans (le_of_eq (by rw [hk', frN_cast eR, neg_mul])))
    linarith
  | succ n ih =>
    intro k A a hk hinv
    obtain ⟨hs, hpd, hb, hl, hdet⟩ := hinv
    rw [frLoop.eq_2]
    split
    · rename_i hfind
      refine ⟨a, rfl, fun i => ?_⟩
      have := List.find?_eq_none.mp hfind i (List.mem_finRange i)
      exact (rowPass_iff (frP d) al be a i).mp (by simpa [rowFail] using this)
    · rename_i i hfind
      have hf : rowFail (frP d) al be a i := by
        have := List.find?_some hfind
        simpa [rowFail] using this
      have hc : al i ≠ 0 := by
        intro h0
        have := rowFail_cut _ al be a i hf z0 (hz z0 hz0)
        rw [h0, vZ_zero, zero_dotProduct] at this
        exact lt_irrefl _ this
      have hnn : (2 : ℤ) ^ (2 * frP d) * (al i ⬝ᵥ al i) ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ two_ne_zero) (fun h => hc (dotProduct_self_eq_zero.mp h))
      split_ifs with h0
      · exact absurd h0 hnn
      have hcut : ∀ x, InB z0 (1 / 2 ^ 1) x → vZ (al i) ⬝ᵥ (x - vR (frP d) a) ≤ 0 := fun x hx =>
        (rowFail_cut _ al be a i hf x (hz x hx)).le
      have hkN : k + 1 ≤ frN d eR := by omega
      obtain ⟨hq1, hq2⟩ := frQ_prec hd1 eR
      obtain ⟨A', a', hU, hs', hpd', hb', hl', hdet'⟩ := ellUpd_step hd (frP d) (frQ d eR) 1
        (2 ^ (frP d + 2 * eR + 6 * (eR + 1) + 2)) (2 ^ frP d * (2 ^ eR + 2 ^ (eR + 3 * (eR + 1) + 1))) A a (al i) z0
        (((2 : ℝ) ^ eR) ^ 2 * gam d ^ k) (LamF eR) hs hpd hb hl
        (by
          have := cap_F hd eR (k + 1) hkN
          calc gam d * (((2 : ℝ) ^ eR) ^ 2 * gam d ^ k) = ((2 : ℝ) ^ eR) ^ 2 * gam d ^ (k + 1) := by ring
            _ ≤ LamF eR := this)
        hc hcut two_le_frP (frP_prec hd1) hq1 hq2 (capA_F _ _)
        (fun j => capa_F _ _ _ ((AdversarialBco.Poly.LeanAp.abs_apply_le_oNorm z0 j).trans hzR))
      rw [hU]
      refine ih (k + 1) A' a' (by omega) ⟨hs', hpd', hb', fun v => ?_, ?_⟩
      · calc v ⬝ᵥ (mR (frP d) A' *ᵥ v) ≤ gam d * (((2 : ℝ) ^ eR) ^ 2 * gam d ^ k) * (v ⬝ᵥ v) := hl' v
          _ = ((2 : ℝ) ^ eR) ^ 2 * gam d ^ (k + 1) * (v ⬝ᵥ v) := by ring
      · calc (mR (frP d) A').det ≤ Real.exp (-(95 / (128 * ((d : ℝ) + 1)))) * (mR (frP d) A).det := hdet'
          _ ≤ Real.exp (-(95 / (128 * ((d : ℝ) + 1)))) *
              (((2 : ℝ) ^ eR) ^ (2 * d) * Real.exp (-(95 / (128 * ((d : ℝ) + 1))) * k)) :=
              mul_le_mul_of_nonneg_left hdet (Real.exp_pos _).le
          _ = _ := exp_step _ _ k

/-- Theorem ELL-F (b): if `B̄(z₀, 1/2) ⊆ Q ∩ B(0, R)`, ELL-F returns a point of `Q`. -/
theorem frEll_spec (hd : 2 ≤ d) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (z0 : Fin d → ℝ)
    (hz : ∀ x, InB z0 (1 / 2 ^ 1) x →
      x ∈ QF (frAl A b) (frBe A b) ∧ x ⬝ᵥ x ≤ ((2 : ℝ) ^ frER d m (frMhat A b)) ^ 2) :
    ∃ a, frEll A b = some a ∧ vR (frP d) a ∈ QF (frAl A b) (frBe A b) := by
  set eR := frER d m (frMhat A b) with heR
  have hR0 : (0 : ℝ) < ((2 : ℝ) ^ eR) ^ 2 := by positivity
  have hzR : oNorm z0 ≤ 2 ^ eR := by
    have h := (hz z0 (inB_self' z0 _)).2
    rw [← AdversarialBco.Poly.LeanAp.oNorm_sq] at h
    exact (pow_le_pow_iff_left₀ (AdversarialBco.Poly.LeanAp.oNorm_nonneg _) (by positivity) two_ne_zero).mp h
  refine frLoop_main hd eR (frAl A b) (frBe A b) z0 (fun x hx => (hz x hx).1) hzR (frN d eR) 0 _ 0 (by omega) ?_
  refine ⟨start_symm _ _, ?_, fun x hx => ?_, fun v => ?_, ?_⟩
  · rw [start_F]
    exact Matrix.PosDef.one.smul hR0
  · rw [start_F, vR_zero]
    exact inE_scalar' _ hR0 x (hz x hx).2
  · rw [start_F, quad_scalar, pow_zero, mul_one]
  · rw [start_F, det_scalar, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]

/-! ## Leaves: the input, the rows, the localisation lemma -/

theorem frDen_pos (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (i : Fin m) : 0 < frDen A b i := by
  unfold frDen
  exact Nat.mul_pos (Finset.prod_pos fun j _ => (A i j).den_pos) (b i).den_pos

theorem frAl_eq (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (i : Fin m) (j : Fin d) :
    ((frAl A b i j : ℤ) : ℚ) = frDen A b i * A i j := by
  unfold frAl
  exact clr_eq _ _ ((Finset.dvd_prod_of_mem (fun j => (A i j).den) (Finset.mem_univ j)).mul_right _)

theorem frBe_eq (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (i : Fin m) :
    ((frBe A b i : ℤ) : ℚ) = frDen A b i * b i := by
  unfold frBe
  exact clr_eq _ _ (dvd_mul_left _ _)

theorem ball_sub_poly_iff (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (y : Fin d → ℝ) (r : ℝ) (hr : 0 ≤ r) :
    Metric.closedBall (WithLp.toLp 2 y : E d) r ⊆ polytope A b ↔
      ∀ i, ∑ j, (A i j : ℝ) * y j + r * Real.sqrt (∑ j, (A i j : ℝ) ^ 2) ≤ b i := by
  have hin : ∀ i (x : E d), inner ℝ (WithLp.toLp 2 (fun j => (A i j : ℝ)) : E d) x = ∑ j, (A i j : ℝ) * x j := by
    intro i x
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  have hpoly : polytope A b =
      {x : E d | ∀ i, inner ℝ (WithLp.toLp 2 (fun j => (A i j : ℝ)) : E d) x ≤ (b i : ℝ)} := by
    ext x
    simp only [Set.mem_ofPred_eq, hin]
    rfl
  rw [hpoly, fr_margin_iff _ _ _ r hr]
  refine forall_congr' fun i => ?_
  have hn : ‖(WithLp.toLp 2 (fun j => (A i j : ℝ)) : E d)‖ = Real.sqrt (∑ j, (A i j : ℝ) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp only [PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
  rw [hin, hn]

theorem cleared_iff (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (y : Fin d → ℝ) (r : ℝ) :
    (∀ i, ∑ j, (A i j : ℝ) * y j + r * Real.sqrt (∑ j, (A i j : ℝ) ^ 2) ≤ b i) ↔
      ∀ i, ∑ j, (frAl A b i j : ℝ) * y j + r * Real.sqrt (∑ j, (frAl A b i j : ℝ) ^ 2) ≤ frBe A b i := by
  refine forall_congr' fun i => ?_
  exact fr_cleared_row (A i) (b i) (frDen A b i) (by exact_mod_cast frDen_pos A b i) (frAl A b i) (frBe A b i)
    (fun j => frAl_eq A b i j) (frBe_eq A b i) r y

theorem height_frMhat (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : HeightLE A b (frMhat A b) := by
  obtain ⟨⟨hA, hb⟩, -, -⟩ := fr_height A b
  have hle : ∀ x, x ≤ Finset.univ.sup (fun i => (Finset.univ.sup fun j =>
      max (A i j).num.natAbs (A i j).den) ⊔ max (b i).num.natAbs (b i).den) → x ≤ frMhat A b :=
    fun x hx => hx.trans (le_max_right _ _)
  exact ⟨fun i j => ⟨hle _ (hA i j).1, hle _ (hA i j).2⟩, fun i => ⟨hle _ (hb i).1, hle _ (hb i).2⟩⟩

theorem one_le_frMhat (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : 1 ≤ frMhat A b := by
  unfold frMhat
  exact le_max_left _ _

theorem Rloc_lt_R (hd : 1 ≤ d) (M : ℕ) : Rloc d m M + 1 ≤ (2 : ℝ) ^ frER d m M := by
  unfold Rloc frER
  have h := Nat.le_pow_clog (by norm_num : 1 < 2) ((d * m * M ^ (2 * (d + 1))) ^ (d + 1) + 1)
  exact_mod_cast h

theorem m_pos_of_diam (hd : 1 ≤ d) (n : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (hdiam : ∀ x ∈ polytope A b, ∀ y ∈ polytope A b, dist x y ≤ n) (hne : (polytope A b).Nonempty) : 1 ≤ m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exfalso
    have hall : ∀ x : EuclideanSpace ℝ (Fin d), x ∈ polytope A b := fun x i => i.elim0
    obtain ⟨z, -⟩ := hne
    have h := hdiam (z + EuclideanSpace.single ⟨0, hd⟩ ((n : ℝ) + 1)) (hall _) z (hall _)
    rw [dist_eq_norm, add_sub_cancel_left, PiLp.norm_single, Real.norm_eq_abs,
      abs_of_pos (by positivity)] at h
    linarith
  · exact hm

theorem dist_toLp (x y : Fin d → ℝ) : dist (WithLp.toLp 2 x : E d) (WithLp.toLp 2 y) = oNorm (x - y) := by
  rw [EuclideanSpace.dist_eq]
  unfold oNorm
  congr 1
  simp only [Real.dist_eq, dotProduct, Pi.sub_apply, sq, abs_mul_abs_self]

theorem toE_eq (c : Fin d → ℚ) : toE c = WithLp.toLp 2 (fun i => (c i : ℝ)) := by
  rfl

/-! ## The frame theorem (i), `d ≥ 2` -/

theorem frameQ_d2 (hd : 2 ≤ d) {n M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    (hI : InputOK d n m M A b) : Metric.closedBall (toE (frameQ d n m A b)) (1 / 2) ⊆ polytope A b := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨z, hz⟩ := hI.ball
  have hzK : z ∈ polytope A b := hz (Metric.mem_closedBall_self zero_le_one)
  have hm := m_pos_of_diam hd1 n A b hI.diam ⟨z, hzK⟩
  set Mh := frMhat A b with hMh
  have hloc := polytope_sub_ball A b hd1 hm (one_le_frMhat A b) (height_frMhat A b)
    (isCompact_polytope A b n hI.diam)
  have hzR : ‖z‖ ≤ Rloc d m Mh := by
    have := hloc hzK
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  set z0 : Fin d → ℝ := WithLp.ofLp z with hz0
  have hzz : (WithLp.toLp 2 z0 : E d) = z := rfl
  have hRl := Rloc_lt_R hd1 (m := m) Mh
  obtain ⟨a, ha, haQ⟩ := frEll_spec hd A b z0 (fun x hx => by
    have hxz : dist (WithLp.toLp 2 x : E d) z ≤ 1 / 2 := by
      rw [← hzz, dist_toLp]
      unfold InB at hx
      unfold oNorm
      rw [Real.sqrt_le_left (by norm_num)]
      simpa using hx
    refine ⟨?_, ?_⟩
    · have hsub : Metric.closedBall (WithLp.toLp 2 x : E d) (1 / 2) ⊆ polytope A b :=
        (Metric.closedBall_subset_closedBall' (by linarith)).trans hz
      exact (cleared_iff A b x (1 / 2)).mp ((ball_sub_poly_iff A b x (1 / 2) (by norm_num)).mp hsub)
    · have hx1 : ‖(WithLp.toLp 2 x : E d)‖ ≤ ‖z‖ + 1 / 2 := by
        have := norm_le_norm_add_norm_sub' (WithLp.toLp 2 x : E d) z
        rw [← dist_eq_norm] at this
        linarith
      have hx2 : oNorm x ≤ (2 : ℝ) ^ frER d m Mh := by
        rw [AdversarialBco.Poly.LeanAp.oNorm_eq]
        linarith
      rw [← AdversarialBco.Poly.LeanAp.oNorm_sq]
      exact pow_le_pow_left₀ (AdversarialBco.Poly.LeanAp.oNorm_nonneg _) hx2 2)
  have hfr : frameQ d n m A b = fun i => (a i : ℚ) / 2 ^ frP d := by
    have h1 : d ≠ 1 := by omega
    have h0 : d ≠ 0 := by omega
    simp only [frameQ, h1, h0, ↓reduceDIte, ↓reduceIte, ha]
  have hc : toE (frameQ d n m A b) = WithLp.toLp 2 (vR (frP d) a) := by
    rw [hfr, toE_eq]
    congr 1
    funext i
    simp [vR]
  rw [hc]
  exact (ball_sub_poly_iff A b _ (1 / 2) (by norm_num)).mpr ((cleared_iff A b _ (1 / 2)).mpr haQ)

/-! ## Leaves: `d = 1` -/

theorem poly1_iff (A : Matrix (Fin m) (Fin 1) ℚ) (b : Fin m → ℚ) (x : E 1) :
    x ∈ polytope A b ↔ ∀ i, (frAl A b i 0 : ℝ) * x 0 ≤ frBe A b i := by
  show (∀ i, ∑ j, (A i j : ℝ) * x j ≤ (b i : ℝ)) ↔ _
  refine forall_congr' fun i => ?_
  rw [Fin.sum_univ_one]
  have hD : (0 : ℝ) < frDen A b i := by exact_mod_cast frDen_pos A b i
  have hα : (frAl A b i 0 : ℝ) = frDen A b i * (A i 0 : ℝ) := by exact_mod_cast frAl_eq A b i 0
  have hβ : (frBe A b i : ℝ) = frDen A b i * (b i : ℝ) := by exact_mod_cast frBe_eq A b i
  rw [hα, hβ, mul_assoc]
  exact (mul_le_mul_iff_of_pos_left hD).symm

theorem dist1 (x y : E 1) : dist x y = |x 0 - y 0| := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_one, Real.dist_eq, sq_abs, Real.sqrt_sq_eq_abs]

theorem lo_spec (al be : Fin m → ℤ) (h : ∃ i, al i < 0) :
    ∃ lo : ℚ, ((List.finRange m).filterMap fun i => if al i < 0 then some ((be i : ℚ) / al i) else none).max? =
        some lo ∧ (∀ i, al i < 0 → (be i : ℚ) / al i ≤ lo) ∧ ∃ i, al i < 0 ∧ (be i : ℚ) / al i = lo := by
  set L := (List.finRange m).filterMap fun i => if al i < 0 then some ((be i : ℚ) / al i) else none with hL
  have hmem : ∀ i, al i < 0 → (be i : ℚ) / al i ∈ L := by
    intro i hi
    rw [hL, List.mem_filterMap]
    exact ⟨i, List.mem_finRange i, by simp [hi]⟩
  have hmem' : ∀ x ∈ L, ∃ i, al i < 0 ∧ (be i : ℚ) / al i = x := by
    intro x hx
    rw [hL, List.mem_filterMap] at hx
    obtain ⟨i, -, hi⟩ := hx
    by_cases h1 : al i < 0
    · simp only [h1, ↓reduceIte, Option.some.injEq] at hi
      exact ⟨i, h1, hi⟩
    · simp [h1] at hi
  obtain ⟨i0, hi0⟩ := h
  obtain ⟨lo, hlo⟩ := Option.isSome_iff_exists.mp (List.isSome_max?_of_mem (hmem i0 hi0))
  have hs := List.max?_eq_some_iff.mp hlo
  exact ⟨lo, hlo, fun i hi => hs.2 _ (hmem i hi), hmem' lo hs.1⟩

theorem hi_spec (al be : Fin m → ℤ) (h : ∃ i, 0 < al i) :
    ∃ hi : ℚ, ((List.finRange m).filterMap fun i => if 0 < al i then some ((be i : ℚ) / al i) else none).min? =
        some hi ∧ (∀ i, 0 < al i → hi ≤ (be i : ℚ) / al i) ∧ ∃ i, 0 < al i ∧ (be i : ℚ) / al i = hi := by
  set L := (List.finRange m).filterMap fun i => if 0 < al i then some ((be i : ℚ) / al i) else none with hL
  have hmem : ∀ i, 0 < al i → (be i : ℚ) / al i ∈ L := by
    intro i hi
    rw [hL, List.mem_filterMap]
    exact ⟨i, List.mem_finRange i, by simp [hi]⟩
  have hmem' : ∀ x ∈ L, ∃ i, 0 < al i ∧ (be i : ℚ) / al i = x := by
    intro x hx
    rw [hL, List.mem_filterMap] at hx
    obtain ⟨i, -, hi⟩ := hx
    by_cases h1 : 0 < al i
    · simp only [h1, ↓reduceIte, Option.some.injEq] at hi
      exact ⟨i, h1, hi⟩
    · simp [h1] at hi
  obtain ⟨i0, hi0⟩ := h
  obtain ⟨hi, hhi⟩ := Option.isSome_iff_exists.mp (List.isSome_min?_of_mem (hmem i0 hi0))
  have hs := List.min?_eq_some_iff.mp hhi
  exact ⟨hi, hhi, fun i h => hs.2 _ (hmem i h), hmem' hi hs.1⟩

theorem frame1_eq (al be : Fin m → ℤ) (lo hi : ℚ) (hz : ¬ ∃ i, al i = 0 ∧ be i < 0)
    (hlo : ((List.finRange m).filterMap fun i => if al i < 0 then some ((be i : ℚ) / al i) else none).max? = some lo)
    (hhi : ((List.finRange m).filterMap fun i => if 0 < al i then some ((be i : ℚ) / al i) else none).min? = some hi)
    (hw : ¬ hi - lo < 1) : frame1 al be = some ((lo + hi) / 2) := by
  unfold frame1
  simp only [hz, ↓reduceIte, hlo, hhi, hw]

/-! ## The frame theorem (i), `d = 1` -/

theorem frameQ_d1 {n m M : ℕ} {A : Matrix (Fin m) (Fin 1) ℚ} {b : Fin m → ℚ}
    (hI : InputOK 1 n m M A b) : Metric.closedBall (toE (frameQ 1 n m A b)) (1 / 2) ⊆ polytope A b := by
  set al : Fin m → ℤ := fun i => frAl A b i ⟨0, by norm_num⟩ with hal
  set be : Fin m → ℤ := frBe A b with hbe
  have hK : ∀ x : E 1, x ∈ polytope A b ↔ ∀ i, (al i : ℝ) * x 0 ≤ be i := poly1_iff A b
  have hpt : ∀ t : ℝ, (WithLp.toLp 2 (fun _ => t) : E 1) 0 = t := fun t => rfl
  obtain ⟨z, hz⟩ := hI.ball
  have hzK : ∀ t : ℝ, |t - z 0| ≤ 1 → ∀ i, (al i : ℝ) * t ≤ be i := by
    intro t ht
    have hmem : (WithLp.toLp 2 (fun _ => t) : E 1) ∈ polytope A b := by
      apply hz
      rw [Metric.mem_closedBall, dist1, hpt]
      exact ht
    have := (hK _).mp hmem
    simpa only [hpt] using this
  have hz1 : ∀ i, (al i : ℝ) * z 0 ≤ be i := hzK (z 0) (by simp)
  have hsigns := fr_d1_signs (fun i => (al i : ℝ)) (fun i => (be i : ℝ)) n (z 0) hz1
    (fun x y hx hy => by
      have h1 : (WithLp.toLp 2 (fun _ => x) : E 1) ∈ polytope A b := (hK _).mpr (by simpa only [hpt] using hx)
      have h2 : (WithLp.toLp 2 (fun _ => y) : E 1) ∈ polytope A b := (hK _).mpr (by simpa only [hpt] using hy)
      have := hI.diam _ h1 _ h2
      rwa [dist1, hpt, hpt] at this)
  have hz0 : ¬ ∃ i, al i = 0 ∧ be i < 0 := by
    rintro ⟨i, h0, hneg⟩
    have h1 := hz1 i
    rw [h0, Int.cast_zero, zero_mul] at h1
    have : (be i : ℝ) < 0 := by exact_mod_cast hneg
    linarith
  obtain ⟨ilo, hilo⟩ := hsigns.2
  obtain ⟨ihi, hihi⟩ := hsigns.1
  obtain ⟨lo, hlo, hlo1, i1, hi1, hlo2⟩ := lo_spec al be ⟨ilo, by exact_mod_cast hilo⟩
  obtain ⟨hi, hhi, hhi1, i2, hi2, hhi2⟩ := hi_spec al be ⟨ihi, by exact_mod_cast hihi⟩
  have hread : ∀ x : ℝ, (∀ i, (al i : ℝ) * x ≤ be i) ↔ (lo : ℝ) ≤ x ∧ x ≤ hi := fun x =>
    fr_d1_readoff (fun i => (al i : ℝ)) (fun i => (be i : ℝ)) lo hi
      (fun i hi' => by
        have := hlo1 i (by exact_mod_cast hi')
        have h' : (((be i : ℚ) / al i : ℚ) : ℝ) ≤ (lo : ℝ) := by exact_mod_cast this
        push_cast at h'
        exact h')
      ⟨i1, by exact_mod_cast hi1, by rw [← hlo2]; push_cast; rfl⟩
      (fun i hi' => by
        have := hhi1 i (by exact_mod_cast hi')
        have h' : (hi : ℝ) ≤ (((be i : ℚ) / al i : ℚ) : ℝ) := by exact_mod_cast this
        push_cast at h'
        exact h')
      ⟨i2, by exact_mod_cast hi2, by rw [← hhi2]; push_cast; rfl⟩
      (fun i h0 => by
        by_contra hneg
        exact hz0 ⟨i, by exact_mod_cast h0, by exact_mod_cast lt_of_not_ge hneg⟩) x
  have hlo3 := ((hread (z 0 - 1)).mp (hzK _ (by norm_num))).1
  have hhi3 := ((hread (z 0 + 1)).mp (hzK _ (by norm_num))).2
  have hw2 : (1 : ℝ) ≤ (hi : ℝ) - lo := by linarith
  have hw : ¬ hi - lo < 1 := by
    intro h
    have : ((hi - lo : ℚ) : ℝ) < 1 := by exact_mod_cast h
    push_cast at this
    linarith
  have hf1 : frame1 (fun i => frAl A b i ⟨0, by norm_num⟩) (frBe A b) = some ((lo + hi) / 2) :=
    frame1_eq al be lo hi hz0 hlo hhi hw
  have hfr : frameQ 1 n m A b = fun _ => (lo + hi) / 2 := by
    simp only [frameQ, ↓reduceDIte]
    rw [hf1]
  have hc : toE (frameQ 1 n m A b) = WithLp.toLp 2 (fun _ => (((lo + hi) / 2 : ℚ) : ℝ)) := by
    rw [hfr, toE_eq]
  rw [hc]
  intro x hx
  rw [Metric.mem_closedBall, dist1, hpt] at hx
  apply (hK x).mpr
  apply (hread (x 0)).mpr
  refine (fr_d1_centre lo hi hw2 1 1 1 1 1 one_pos one_pos le_rfl le_rfl le_rfl le_rfl).1 (x 0) ?_
  push_cast at hx
  exact hx

/-! ## The frame theorem (i) -/

/-- Piece (B) of (PROG-CUT) the frame theorem (i): on `InputOK`, the frame centre `c = frameQ d n m A b`
has `B̄(c, 1/2) ⊆ K ⊆ B̄(c, n)`, `K = polytope A b`. -/
theorem frameQ_ball {d n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} (hI : InputOK d n m M A b) :
    Metric.closedBall (toE (frameQ d n m A b)) (1 / 2) ⊆ polytope A b ∧
      polytope A b ⊆ Metric.closedBall (toE (frameQ d n m A b)) n := by
  have h1 : Metric.closedBall (toE (frameQ d n m A b)) (1 / 2) ⊆ polytope A b := by
    rcases Nat.lt_or_ge d 2 with hd | hd
    · obtain rfl : d = 1 := by have := hI.hd; omega
      exact frameQ_d1 hI
    · exact frameQ_d2 hd hI
  refine ⟨h1, fun x hx => ?_⟩
  have hc : toE (frameQ d n m A b) ∈ polytope A b := h1 (Metric.mem_closedBall_self (by norm_num))
  rw [Metric.mem_closedBall]
  exact hI.diam x hx _ hc

end AdversarialBco.Bit.ApQ
