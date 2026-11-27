/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Arith.MachN.Code
public import AdversarialBco.Poly.MachPGParts
public import AdversarialBco.Poly.MachPGPar

@[expose] public section

/-!
# The rules of CLAMP-NS and of the pivot test

The code of `MachN/Code.lean` at the layout of PG (naturals `n0 + k`, `k < 20`, scalars `s0 + k`, `k < 64`, arrays
`a0 + k`, `k < 32`). Every rule is exact: CLAMP-NS computes `clampNSMat a b e (cnsJ d a b e)` for every `a`, `b`, `e`
(`runs_clampNSC`), and the pivot loop clears the verdict exactly when a pivot of Gauss-Jordan elimination is `≤ 0`
(`runs_gjTestLoop`).
-/

namespace AdversarialBco.Conj1Arith

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL
  AdversarialBco.Poly.PG Matrix

variable {d : ℕ} {L : Layout} {w : World d}

/-! ## Matrix facts -/

/-- A fill by `0` then a diagonal `c` is `c I`. -/
theorem of_diag_zero (c : ℝ) :
    (Matrix.of fun a b : Fin d => if a = b then c else (Matrix.of fun _ _ : Fin d => (0 : ℝ)) a b) =
      c • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  ext a b
  by_cases h : a = b
  · subst h; simp
  · simp [h, Matrix.one_apply]

/-- The trace of `W W` is the square of the Frobenius norm when `W` is symmetric. -/
theorem trace_mul_self_of_symm (W : Matrix (Fin d) (Fin d) ℝ) (hW : Wᵀ = W) :
    (W * W).trace = ∑ i, ∑ j, W i j ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : W j i = W i j := by rw [← Matrix.transpose_apply W i j, hW]
  rw [this, sq]

/-- `sym Y - m I` is symmetric. -/
theorem symPart_sub_symm (Y : Matrix (Fin d) (Fin d) ℝ) (m : ℝ) :
    (symPart Y - m • (1 : Matrix (Fin d) (Fin d) ℝ))ᵀ = symPart Y - m • 1 := by
  unfold symPart
  rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.transpose_add, Matrix.transpose_transpose, add_comm Yᵀ Y]

/-! ## The values of the straight-line blocks -/

section vals

variable (n : ℕ → ℕ) (f : ℕ → ℝ) (s0 n0 : ℕ)

theorem nsParL_v0 : sEval n (nsParL s0 (s0 + 21) (s0 + 22) (s0 + 48)) f s0 = 0 := by simp only [nsParL]; pg_val
theorem nsParL_v1 : sEval n (nsParL s0 (s0 + 21) (s0 + 22) (s0 + 48)) f (s0 + 1) = 1 / 2 := by
  simp only [nsParL]; pg_val
theorem nsParL_v2 : sEval n (nsParL s0 (s0 + 21) (s0 + 22) (s0 + 48)) f (s0 + 2) = 1 := by simp only [nsParL]; pg_val
theorem nsParL_v3 : sEval n (nsParL s0 (s0 + 21) (s0 + 22) (s0 + 48)) f (s0 + 3) =
    cnMid (f (s0 + 21)) (f (s0 + 22)) := by
  simp only [nsParL]; pg_val; unfold cnMid; ring
theorem nsParL_v5 (hd : f (s0 + 48) = d) : sEval n (nsParL s0 (s0 + 21) (s0 + 22) (s0 + 48)) f (s0 + 5) =
    cnR0 d (f (s0 + 21)) (f (s0 + 22)) := by
  simp only [nsParL]; pg_val; rw [hd]; unfold cnR0 cnHalf; ring
theorem nsParL_v6 (hd : f (s0 + 48) = d) : sEval n (nsParL s0 (s0 + 21) (s0 + 22) (s0 + 48)) f (s0 + 6) =
    cnC0 d (f (s0 + 21)) (f (s0 + 22)) := by
  simp only [nsParL]; pg_val; rw [hd]; unfold cnC0 cnR0 cnHalf; ring
theorem nsParL_v7 (hd : f (s0 + 48) = d) : sEval n (nsParL s0 (s0 + 21) (s0 + 22) (s0 + 48)) f (s0 + 7) =
    (cnC0 d (f (s0 + 21)) (f (s0 + 22)))⁻¹ := by
  simp only [nsParL]; pg_val; rw [hd]; unfold cnC0 cnR0 cnHalf; ring
theorem nsParL_v14 : sEval n (nsParL s0 (s0 + 21) (s0 + 22) (s0 + 48)) f (s0 + 14) = 3 := by
  simp only [nsParL]; pg_val
theorem nsParL_v15 : sEval n (nsParL s0 (s0 + 21) (s0 + 22) (s0 + 48)) f (s0 + 15) = -1 / 2 := by
  simp only [nsParL]; pg_val
theorem nsParL_v16 : sEval n (nsParL s0 (s0 + 21) (s0 + 22) (s0 + 48)) f (s0 + 16) = -1 := by
  simp only [nsParL]; pg_val

/-- The shift `m - a - e` of the first root. -/
theorem nsShA_v13 : sEval n [SI.op2 .sub (s0 + 13) (s0 + 3) (s0 + 21), SI.op2 .sub (s0 + 13) (s0 + 13) (s0 + 36)] f
    (s0 + 13) = f (s0 + 3) - f (s0 + 21) - f (s0 + 36) := by pg_val

/-- The shift `m - b + e` of the second root. -/
theorem nsShB_v13 : sEval n [SI.op2 .sub (s0 + 13) (s0 + 3) (s0 + 22), SI.op2 .add (s0 + 13) (s0 + 13) (s0 + 36)] f
    (s0 + 13) = f (s0 + 3) - f (s0 + 22) + f (s0 + 36) := by pg_val

/-- The scalars `nsParL` writes. -/
theorem nsParL_dst : (nsParL s0 (s0 + 21) (s0 + 22) (s0 + 48)).map SI.dst =
    [s0, s0 + 1, s0 + 2, s0 + 3, s0 + 3, s0 + 4, s0 + 4, s0 + 5, s0 + 5, s0 + 6, s0 + 7, s0 + 14, s0 + 15,
      s0 + 16] := rfl

theorem nsParL_cost : sCost (nsParL s0 (s0 + 21) (s0 + 22) (s0 + 48)) = 14 := by simp [sCost, nsParL, SI.cost]

theorem pgEprL_cost : sCost (pgEprL n0 s0) = 38 := by simp [sCost, pgEprL, SI.cost]

theorem pgEprL_ok {L : Layout} (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) :
    (pgEprL n0 s0).all (SI.ok L) = true := by
  simp only [pgEprL, List.all_cons, List.all_nil, SI.ok, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- The scalars `pgEprL` does not write keep their values. -/
theorem pgEprL_frame {x : ℕ} (h3 : x ≠ s0 + 3) (h4 : x ≠ s0 + 4) (h5 : x ≠ s0 + 5) (h6 : x ≠ s0 + 6)
    (h7 : x ≠ s0 + 7) (h36 : x ≠ s0 + 36) : sEval n (pgEprL n0 s0) f x = f x :=
  sEval_frame n _ f (by simp [pgEprL, SI.dst, h3, h4, h5, h6, h7, h36])

/-- `pgEprL` computes `e' = pgEpr d ρ` from the stage variables. -/
theorem pgEprL_v36 {ρ : ℝ} (hρ : 0 ≤ ρ) (h19 : f (s0 + 19) = ρ) (h21 : f (s0 + 21) = pgTmin d ρ)
    (h22 : f (s0 + 22) = pgLD ρ) (h48 : f (s0 + 48) = d) (h11 : n (n0 + 11) = pgNs d ρ) :
    sEval n (pgEprL n0 s0) f (s0 + 36) = pgEpr d ρ := by
  simp only [pgEprL]
  pg_val
  rw [h19, h21, h22, h48, h11]
  unfold pgEpr pgEP pgEh pgG2 pgKappa pgLam
  have hpos : 0 ≤ 2 * Real.log (1 + ρ) := by
    have : 1 ≤ 1 + ρ := by nlinarith
    nlinarith [Real.log_nonneg this]
  rw [Real.sq_sqrt hpos]
  ring_nf

end vals

/-! ## F1-NS: the parts of CLAMP-NS -/

/-- One Newton-Schulz step. -/
theorem runs_nsStepC {dv one n0 s0 a0 : ℕ} (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS)
    (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv)
    (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) (hdd : σ.nat (n0 + 9) = d * d)
    (h0 : σ.sc s0 = 0) (hh : σ.sc (s0 + 1) = 1 / 2) (ho : σ.sc (s0 + 2) = 1) (hm : σ.sc (s0 + 16) = -1)
    (hI : σ.mat (a0 + 11) = (3 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)) :
    Runs L w (nsStepC L dv one (n0 + 9) n0 s0 (a0 + 7) (a0 + 8) (a0 + 9) (a0 + 11)) σ (kNsStep d)
      (fun σ' => σ'.mat (a0 + 7) =
          (1 / 2 : ℝ) • (σ.mat (a0 + 7) * ((3 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) - σ.mat (a0 + 7) * σ.mat (a0 + 7))) ∧
        Env.Frame σ σ' [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5] [s0 + 8, s0 + 9, s0 + 12]
          [a0 + 7, a0 + 8, a0 + 9]) := by
  unfold nsStepC kNsStep kMmul kMlin
  refine runs_seq (runs_mmul (i := n0) (j := n0 + 1) (l := n0 + 2) (kA := n0 + 3) (kB := n0 + 4) (kC := n0 + 5)
    (C := a0 + 8) (A := a0 + 7) (B := a0 + 7) (s := s0 + 12) (t1 := s0 + 8) (t2 := s0 + 9) σ hdv hone
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp) (by simp; omega) (by simp; omega) (by omega) (by omega) (by omega) (by omega) (by omega) hd h1) fun σ1 h1' => ?_
  obtain ⟨m1, F1, -⟩ := h1'
  refine runs_seq (runs_mlin (dd := n0 + 9) (m := n0) (C := a0 + 8) (A := a0 + 11) (B := a0 + 8) (α := s0 + 2)
    (β := s0 + 16) (t1 := s0 + 8) (t2 := s0 + 9) σ1 (by omega) hone
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F1.1 _ (by simp)).trans hdd) ((F1.1 one (by simp; omega)).trans h1)) fun σ2 h2' => ?_
  obtain ⟨m2, F2, -⟩ := h2'
  have F02 : Env.Frame σ σ2 [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5] [s0 + 8, s0 + 9, s0 + 12]
      [a0 + 7, a0 + 8, a0 + 9] :=
    Env.Frame.trans (Env.Frame.mono F1 (by simp) (by simp) (by simp)) (Env.Frame.mono F2 (by simp) (by simp) (by simp))
  refine runs_seq (runs_mmul (i := n0) (j := n0 + 1) (l := n0 + 2) (kA := n0 + 3) (kB := n0 + 4) (kC := n0 + 5)
    (C := a0 + 9) (A := a0 + 7) (B := a0 + 8) (s := s0 + 12) (t1 := s0 + 8) (t2 := s0 + 9) σ2 hdv hone
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp) (by simp; omega) (by simp; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F02.1 dv (by simp; omega)).trans hd) ((F02.1 one (by simp; omega)).trans h1)) fun σ3 h3' => ?_
  obtain ⟨m3, F3, -⟩ := h3'
  have F03 : Env.Frame σ σ3 [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5] [s0 + 8, s0 + 9, s0 + 12]
      [a0 + 7, a0 + 8, a0 + 9] :=
    Env.Frame.trans F02 (Env.Frame.mono F3 (by simp) (by simp) (by simp))
  refine runs_mono (runs_mlin (dd := n0 + 9) (m := n0) (C := a0 + 7) (A := a0 + 9) (B := a0 + 9) (α := s0 + 1)
    (β := s0) (t1 := s0 + 8) (t2 := s0 + 9) σ3 (by omega) hone
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F03.1 _ (by simp)).trans hdd) ((F03.1 one (by simp; omega)).trans h1)) le_rfl fun σ4 h4' => ?_
  obtain ⟨m4, F4, -⟩ := h4'
  refine ⟨?_, Env.Frame.trans F03 (Env.Frame.mono F4 (by simp) (by simp) (by simp))⟩
  have e31 : σ3.sc (s0 + 1) = 1 / 2 := (F03.2.1 _ (by simp)).trans hh
  have e30 : σ3.sc s0 = 0 := (F03.2.1 _ (by simp)).trans h0
  have e27 : σ2.mat (a0 + 7) = σ.mat (a0 + 7) :=
    Env.mat_of_arr (σ' := σ2) ((F2.2.2.1 _ (by simp)).trans (F1.2.2.1 _ (by simp)))
  have e12 : σ1.sc (s0 + 2) = 1 := (F1.2.1 _ (by simp)).trans ho
  have e116 : σ1.sc (s0 + 16) = -1 := (F1.2.1 _ (by simp)).trans hm
  have e1I : σ1.mat (a0 + 11) = σ.mat (a0 + 11) := Env.mat_of_arr (F1.2.2.1 _ (by simp))
  rw [m4, e31, e30, m3, e27, m2, e12, e116, e1I, hI, m1]
  simp only [one_smul, neg_one_smul, zero_smul, add_zero, sub_eq_add_neg]

/-- `J` Newton-Schulz steps. -/
theorem runs_nsLoopC {dv one n0 s0 a0 : ℕ} (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS)
    (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv)
    (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) (hdd : σ.nat (n0 + 9) = d * d)
    (h0 : σ.sc s0 = 0) (hh : σ.sc (s0 + 1) = 1 / 2) (ho : σ.sc (s0 + 2) = 1) (hm : σ.sc (s0 + 16) = -1)
    (hI : σ.mat (a0 + 11) = (3 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)) (J : ℕ) (hJ : σ.nat (n0 + 8) = J) :
    Runs L w (nsLoopC L dv one (n0 + 9) n0 s0 (a0 + 7) (a0 + 8) (a0 + 9) (a0 + 11)) σ (kNsLoop d J)
      (fun σ' => σ'.mat (a0 + 7) = nsIter (σ.mat (a0 + 7)) J ∧
        Env.Frame σ σ' [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6] [s0 + 8, s0 + 9, s0 + 12]
          [a0 + 7, a0 + 8, a0 + 9]) := by
  unfold nsLoopC kNsLoop
  set i := n0 + 6 with hi_def
  set n := n0 + 8 with hn_def
  have hi : i < L.NN := by
    dsimp [i]; omega
  have hn : n < L.NN := by
    dsimp [n]; omega
  have hin : i ≠ n := by
    dsimp [i, n]; omega
  have hio : i ≠ one := by
    dsimp [i]
    rcases honeb with (h | h)
    · omega
    · omega
  set body := nsStepC L dv one (n0 + 9) n0 s0 (a0 + 7) (a0 + 8) (a0 + 9) (a0 + 11) with hbody_def
  set Jv : ℕ → Env d → Prop := fun t σ' =>
    σ'.mat (a0 + 7) = nsIter (σ.mat (a0 + 7)) t ∧
    Env.Frame σ σ' [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6] [s0 + 8, s0 + 9, s0 + 12] [a0 + 7, a0 + 8, a0 + 9]
  with hJv_def
  have hN : σ.nat n = J := hJ
  have h0_Jv : Jv 0 (σ.setNat i 0) := by
    dsimp [Jv, i]
    refine ⟨?_, ?_⟩
    · have hmat_setNat : (σ.setNat (n0 + 6) 0).mat (a0 + 7) = σ.mat (a0 + 7) := by
        ext k l; simp [Env.mat, Env.setNat_arr]
      simp [nsIter, hmat_setNat]
    · refine Env.Frame.setNat (Env.Frame.refl σ [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6] [s0 + 8, s0 + 9, s0 + 12] [a0 + 7, a0 + 8, a0 + 9]) ?_ 0
      simp
  have hbody_body : ∀ t < J, ∀ σ', Jv t σ' → σ'.nat i = t → σ'.nat n = J → σ'.nat one = 1 →
      Runs L w body σ' (kNsStep d) (fun σ'' => σ''.nat i = t ∧ σ''.nat n = J ∧ σ''.nat one = 1 ∧ Jv (t + 1) (σ''.setNat i (t + 1))) := by
    intro t ht σ' hJv_t hit hnt hone_t
    rcases hJv_t with ⟨hmat_t, hframe_t⟩
    have hdv_t : σ'.nat dv = d := by
      rw [hframe_t.1 dv (by
        intro h; simp at h
        rcases hdvb with (h' | h')
        · omega
        · omega), hd]
    have hone_t' : σ'.nat one = 1 := by
      rw [hframe_t.1 one (by
        intro h; simp at h
        rcases honeb with (h' | h')
        · omega
        · omega), h1]
    have hdd_t : σ'.nat (n0 + 9) = d * d := by
      rw [hframe_t.1 (n0 + 9) (by simp), hdd]
    have h0_t : σ'.sc s0 = 0 := by
      rw [hframe_t.2.1 s0 (by simp), h0]
    have hh_t : σ'.sc (s0 + 1) = 1 / 2 := by
      rw [hframe_t.2.1 (s0 + 1) (by simp), hh]
    have ho_t : σ'.sc (s0 + 2) = 1 := by
      rw [hframe_t.2.1 (s0 + 2) (by simp), ho]
    have hm_t : σ'.sc (s0 + 16) = -1 := by
      rw [hframe_t.2.1 (s0 + 16) (by simp), hm]
    have hI_t : σ'.mat (a0 + 11) = (3 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
      have harr := hframe_t.2.2.1 (a0 + 11) (by simp)
      have hI_entry : ∀ k l : Fin d, σ.mat (a0 + 11) k l = ((3 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)) k l := by
        intro k l; simpa using congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M k l) hI
      ext k l
      calc
        σ'.mat (a0 + 11) k l = σ.arr (a0 + 11) (d * k + l) := by simp [Env.mat, harr]
        _ = σ.mat (a0 + 11) k l := by simp [Env.mat]
        _ = ((3 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)) k l := hI_entry k l
    have hstep := runs_nsStepC (w := w) σ' hn0 hs0 ha0 hdv hone hdvb honeb hdv_t hone_t' hdd_t h0_t hh_t ho_t hm_t hI_t
    have hQ_imp : ∀ σ'', (σ''.mat (a0 + 7) = (1 / 2 : ℝ) • (σ'.mat (a0 + 7) * ((3 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) - σ'.mat (a0 + 7) * σ'.mat (a0 + 7))) ∧ Env.Frame σ' σ'' [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5] [s0 + 8, s0 + 9, s0 + 12] [a0 + 7, a0 + 8, a0 + 9]) → (σ''.nat i = t ∧ σ''.nat n = J ∧ σ''.nat one = 1 ∧ Jv (t + 1) (σ''.setNat i (t + 1))) := by
      intro σ'' ⟨hmat, hframe⟩
      have h_n_i : σ''.nat i = t := by
        have := hframe.1 i (by dsimp [i]; simp)
        rw [this, hit]
      have h_n_n : σ''.nat n = J := by
        have := hframe.1 n (by dsimp [n]; simp)
        rw [this, hnt]
      have h_n_one : σ''.nat one = 1 := by
        have := hframe.1 one (by
          intro h; simp at h
          rcases honeb with (h' | h')
          · omega
          · omega)
        rw [this, hone_t]
      have h_Jv : Jv (t + 1) (σ''.setNat i (t + 1)) := by
        dsimp [Jv]
        refine ⟨?_, ?_⟩
        · have hmat_setNat : (σ''.setNat i (t + 1)).mat (a0 + 7) = σ''.mat (a0 + 7) := by
            ext k l; simp [Env.mat, Env.setNat_arr, i]
          rw [hmat_setNat, hmat, hmat_t]
          rfl
        · have hframe_ext : σ'.Frame σ'' [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6] [s0 + 8, s0 + 9, s0 + 12] [a0 + 7, a0 + 8, a0 + 9] :=
            Env.Frame.mono hframe (by
              intro x hx
              simp [List.mem_cons] at hx ⊢
              rcases hx with (rfl|rfl|rfl|rfl|rfl|rfl) <;> simp) (by simp) (by simp)
          have htrans := Env.Frame.trans hframe_t hframe_ext
          exact Env.Frame.setNat htrans (by dsimp [i]; simp) (t + 1)
      exact ⟨h_n_i, h_n_n, h_n_one, h_Jv⟩
    exact runs_mono hstep le_rfl hQ_imp
  have hfor := runs_forN hi hn hone hin hio J (kNsStep d) Jv σ hN h1 h0_Jv hbody_body
  have hfor' := runs_mono hfor (le_rfl) (fun σ' h => h.1)
  simpa [nsLoopC, kNsLoop, i, n, body, Jv] using hfor'

/-- One root `Y^c = M X_J`, `M = W + (m - c) I` (`m - c` in `s0 + 13`), `X₀ = M/c₀` (`1/c₀` in `s0 + 7`). -/
theorem runs_nsRootC {dv one n0 s0 a0 : ℕ} (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS)
    (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv)
    (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) (hdd : σ.nat (n0 + 9) = d * d)
    (h0 : σ.sc s0 = 0) (hh : σ.sc (s0 + 1) = 1 / 2) (ho : σ.sc (s0 + 2) = 1) (h3 : σ.sc (s0 + 14) = 3)
    (hm : σ.sc (s0 + 16) = -1) (out : ℕ) (hout : out = a0 + 12 ∨ out = a0 + 13) (J : ℕ) (hJ : σ.nat (n0 + 8) = J) :
    Runs L w (nsRootC L dv one (n0 + 9) n0 s0 (a0 + 5) (a0 + 6) (a0 + 7) (a0 + 8) (a0 + 9) (a0 + 11) out) σ
      (kNsRoot d J)
      (fun σ' => σ'.mat out = (σ.mat (a0 + 5) + σ.sc (s0 + 13) • (1 : Matrix (Fin d) (Fin d) ℝ)) *
          nsIter (σ.sc (s0 + 7) • (σ.mat (a0 + 5) + σ.sc (s0 + 13) • (1 : Matrix (Fin d) (Fin d) ℝ))) J ∧
        Env.Frame σ σ' [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6] [s0 + 8, s0 + 9, s0 + 12]
          [a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 11, out]) := by
  unfold nsRootC kNsRoot kMfill kMdiag kMlin kMmul
  refine runs_seq (runs_mfill (dd := n0 + 9) (m := n0) (A := a0 + 11) (z := s0) σ (by omega) hone (by omega)
    (by omega) (by omega) (by omega) (by omega) hdd h1) fun σ1 h1' => ?_
  obtain ⟨m1, F1, -⟩ := h1'
  have F01 : Env.Frame σ σ1 [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6] [s0 + 8, s0 + 9, s0 + 12] [a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 11, out] := Env.Frame.mono F1 (by simp) (by simp) (by simp)
  refine runs_seq (runs_mdiag (i := n0) (k := n0 + 1) (A := a0 + 11) (z := s0 + 13) σ1 hdv hone (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F01.1 dv (by simp; omega)).trans hd) ((F01.1 one (by simp; omega)).trans h1)) fun σ2 h2' => ?_
  obtain ⟨m2, F2, -⟩ := h2'
  have F02 : Env.Frame σ σ2 [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6] [s0 + 8, s0 + 9, s0 + 12] [a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 11, out] := Env.Frame.trans F01 (Env.Frame.mono F2 (by simp) (by simp) (by simp))
  refine runs_seq (runs_mlin (dd := n0 + 9) (m := n0) (C := a0 + 6) (A := a0 + 5) (B := a0 + 11) (α := s0 + 2)
    (β := s0 + 2) (t1 := s0 + 8) (t2 := s0 + 9) σ2 (by omega) hone
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F02.1 _ (by simp)).trans hdd) ((F02.1 one (by simp; omega)).trans h1)) fun σ3 h3' => ?_
  obtain ⟨m3, F3, -⟩ := h3'
  have F03 : Env.Frame σ σ3 [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6] [s0 + 8, s0 + 9, s0 + 12] [a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 11, out] := Env.Frame.trans F02 (Env.Frame.mono F3 (by simp) (by simp) (by simp))
  refine runs_seq (runs_mlin (dd := n0 + 9) (m := n0) (C := a0 + 7) (A := a0 + 6) (B := a0 + 6) (α := s0 + 7)
    (β := s0) (t1 := s0 + 8) (t2 := s0 + 9) σ3 (by omega) hone
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F03.1 _ (by simp)).trans hdd) ((F03.1 one (by simp; omega)).trans h1)) fun σ4 h4' => ?_
  obtain ⟨m4, F4, -⟩ := h4'
  have F04 : Env.Frame σ σ4 [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6] [s0 + 8, s0 + 9, s0 + 12] [a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 11, out] := Env.Frame.trans F03 (Env.Frame.mono F4 (by simp) (by simp) (by simp))
  refine runs_seq (runs_mfill (dd := n0 + 9) (m := n0) (A := a0 + 11) (z := s0) σ4 (by omega) hone (by omega)
    (by omega) (by omega) (by omega) (by omega) ((F04.1 _ (by simp)).trans hdd) ((F04.1 one (by simp; omega)).trans h1)) fun σ5 h5' => ?_
  obtain ⟨m5, F5, -⟩ := h5'
  have F05 : Env.Frame σ σ5 [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6] [s0 + 8, s0 + 9, s0 + 12] [a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 11, out] := Env.Frame.trans F04 (Env.Frame.mono F5 (by simp) (by simp) (by simp))
  refine runs_seq (runs_mdiag (i := n0) (k := n0 + 1) (A := a0 + 11) (z := s0 + 14) σ5 hdv hone (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F05.1 dv (by simp; omega)).trans hd) ((F05.1 one (by simp; omega)).trans h1)) fun σ6 h6' => ?_
  obtain ⟨m6, F6, -⟩ := h6'
  have F06 : Env.Frame σ σ6 [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6] [s0 + 8, s0 + 9, s0 + 12] [a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 11, out] := Env.Frame.trans F05 (Env.Frame.mono F6 (by simp) (by simp) (by simp))
  have e50 : σ4.sc s0 = 0 := (F04.2.1 _ (by simp)).trans h0
  have e514 : σ5.sc (s0 + 14) = 3 := (F05.2.1 _ (by simp)).trans h3
  have hI6 : σ6.mat (a0 + 11) = (3 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [m6, m5, e50, e514, of_diag_zero]
  refine runs_seq (runs_nsLoopC σ6 hn0 hs0 ha0 hdv hone hdvb honeb ((F06.1 dv (by simp; omega)).trans hd)
    ((F06.1 one (by simp; omega)).trans h1) ((F06.1 _ (by simp)).trans hdd) ((F06.2.1 _ (by simp)).trans h0)
    ((F06.2.1 _ (by simp)).trans hh) ((F06.2.1 _ (by simp)).trans ho) ((F06.2.1 _ (by simp)).trans hm) hI6 J
    ((F06.1 _ (by simp)).trans hJ)) fun σ7 h7' => ?_
  obtain ⟨m7, F7⟩ := h7'
  have F07 : Env.Frame σ σ7 [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6] [s0 + 8, s0 + 9, s0 + 12] [a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 11, out] := Env.Frame.trans F06 (Env.Frame.mono F7 (by simp) (by simp) (by simp))
  refine runs_mono (runs_mmul (i := n0) (j := n0 + 1) (l := n0 + 2) (kA := n0 + 3) (kB := n0 + 4) (kC := n0 + 5)
    (C := out) (A := a0 + 6) (B := a0 + 7) (s := s0 + 12) (t1 := s0 + 8) (t2 := s0 + 9) σ7 hdv hone
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp) (by simp; omega) (by simp; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F07.1 dv (by simp; omega)).trans hd) ((F07.1 one (by simp; omega)).trans h1)) le_rfl fun σ8 h8' => ?_
  obtain ⟨m8, F8, -⟩ := h8'
  refine ⟨?_, Env.Frame.trans F07 (Env.Frame.mono F8 (by simp) (by simp) (by simp))⟩
  have eM7 : σ7.mat (a0 + 6) = σ3.mat (a0 + 6) := Env.mat_of_arr (σ' := σ7) ((F7.2.2.1 _ (by simp)).trans
    ((F6.2.2.1 _ (by simp)).trans ((F5.2.2.1 _ (by simp)).trans (F4.2.2.1 _ (by simp)))))
  have eX6 : σ6.mat (a0 + 7) = σ4.mat (a0 + 7) :=
    Env.mat_of_arr (σ' := σ6) ((F6.2.2.1 _ (by simp)).trans (F5.2.2.1 _ (by simp)))
  have e37 : σ3.sc (s0 + 7) = σ.sc (s0 + 7) := F03.2.1 _ (by simp)
  have e30 : σ3.sc s0 = 0 := (F03.2.1 _ (by simp)).trans h0
  have e22 : σ2.sc (s0 + 2) = 1 := (F02.2.1 _ (by simp)).trans ho
  have eW2 : σ2.mat (a0 + 5) = σ.mat (a0 + 5) :=
    Env.mat_of_arr (σ' := σ2) ((F2.2.2.1 _ (by simp)).trans (F1.2.2.1 _ (by simp)))
  have eI2 : σ2.mat (a0 + 11) = σ.sc (s0 + 13) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [m2, m1, (F1.2.1 _ (by simp) : σ1.sc (s0 + 13) = σ.sc (s0 + 13)), h0, of_diag_zero]
  rw [m8, m7, eM7, eX6, m4, e37, e30, m3, e22, eW2, eI2]
  simp only [one_smul, zero_smul, add_zero]

/-- `W := sym Y - m I` (`m` in `s0 + 3`). -/
theorem runs_nsSymC {dv one n0 s0 a0 : ℕ} (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS)
    (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv)
    (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) (hdd : σ.nat (n0 + 9) = d * d)
    (h0 : σ.sc s0 = 0) (hh : σ.sc (s0 + 1) = 1 / 2) (ho : σ.sc (s0 + 2) = 1) (hm : σ.sc (s0 + 16) = -1) :
    Runs L w (nsSymC L dv one (n0 + 9) n0 s0 (a0 + 1) (a0 + 5) (a0 + 8) (a0 + 11)) σ (kNsSym d)
      (fun σ' => σ'.mat (a0 + 5) = symPart (σ.mat (a0 + 1)) - σ.sc (s0 + 3) • (1 : Matrix (Fin d) (Fin d) ℝ) ∧
        Env.Frame σ σ' [n0, n0 + 1, n0 + 2, n0 + 3] [s0 + 8, s0 + 9] [a0 + 5, a0 + 8, a0 + 11]) := by
  unfold nsSymC kNsSym kMtransp kMlin kMfill kMdiag
  refine runs_seq (runs_mtransp (i := n0) (j := n0 + 1) (kA := n0 + 2) (kB := n0 + 3) (B := a0 + 8) (A := a0 + 1)
    (t := s0 + 8) σ hdv hone (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by simp) (by simp; omega) (by simp; omega) hd h1) fun σ1 h1' => ?_
  obtain ⟨m1, F1, -⟩ := h1'
  refine runs_seq (runs_mlin (dd := n0 + 9) (m := n0) (C := a0 + 5) (A := a0 + 1) (B := a0 + 8) (α := s0 + 1)
    (β := s0 + 1) (t1 := s0 + 8) (t2 := s0 + 9) σ1 (by omega) hone (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) ((F1.1 _ (by simp)).trans hdd) ((F1.1 one (by simp; omega)).trans h1)) fun σ2 h2' => ?_
  obtain ⟨m2, F2, -⟩ := h2'
  have F02 : Env.Frame σ σ2 [n0, n0 + 1, n0 + 2, n0 + 3] [s0 + 8, s0 + 9] [a0 + 5, a0 + 8, a0 + 11] :=
    Env.Frame.trans (Env.Frame.mono F1 (by simp) (by simp) (by simp)) (Env.Frame.mono F2 (by simp) (by simp) (by simp))
  refine runs_seq (runs_mfill (dd := n0 + 9) (m := n0) (A := a0 + 11) (z := s0) σ2 (by omega) hone (by omega)
    (by omega) (by omega) (by omega) (by omega) ((F02.1 _ (by simp)).trans hdd) ((F02.1 one (by simp; omega)).trans h1))
    fun σ3 h3' => ?_
  obtain ⟨m3, F3, -⟩ := h3'
  have F03 : Env.Frame σ σ3 [n0, n0 + 1, n0 + 2, n0 + 3] [s0 + 8, s0 + 9] [a0 + 5, a0 + 8, a0 + 11] :=
    Env.Frame.trans F02 (Env.Frame.mono F3 (by simp) (by simp) (by simp))
  refine runs_seq (runs_mdiag (i := n0) (k := n0 + 1) (A := a0 + 11) (z := s0 + 3) σ3 hdv hone (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F03.1 dv (by simp; omega)).trans hd) ((F03.1 one (by simp; omega)).trans h1)) fun σ4 h4' => ?_
  obtain ⟨m4, F4, -⟩ := h4'
  have F04 : Env.Frame σ σ4 [n0, n0 + 1, n0 + 2, n0 + 3] [s0 + 8, s0 + 9] [a0 + 5, a0 + 8, a0 + 11] :=
    Env.Frame.trans F03 (Env.Frame.mono F4 (by simp) (by simp) (by simp))
  refine runs_mono (runs_mlin (dd := n0 + 9) (m := n0) (C := a0 + 5) (A := a0 + 5) (B := a0 + 11) (α := s0 + 2)
    (β := s0 + 16) (t1 := s0 + 8) (t2 := s0 + 9) σ4 (by omega) hone (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) ((F04.1 _ (by simp)).trans hdd) ((F04.1 one (by simp; omega)).trans h1)) le_rfl fun σ5 h5' => ?_
  obtain ⟨m5, F5, -⟩ := h5'
  refine ⟨?_, Env.Frame.trans F04 (Env.Frame.mono F5 (by simp) (by simp) (by simp))⟩
  have e42 : σ4.sc (s0 + 2) = 1 := (F04.2.1 _ (by simp)).trans ho
  have e416 : σ4.sc (s0 + 16) = -1 := (F04.2.1 _ (by simp)).trans hm
  have e33 : σ3.sc (s0 + 3) = σ.sc (s0 + 3) := F03.2.1 _ (by simp)
  have e20 : σ2.sc s0 = 0 := (F02.2.1 _ (by simp)).trans h0
  have e45 : σ4.mat (a0 + 5) = σ2.mat (a0 + 5) :=
    Env.mat_of_arr (σ' := σ4) ((F4.2.2.1 _ (by simp)).trans (F3.2.2.1 _ (by simp)))
  have e11 : σ1.sc (s0 + 1) = 1 / 2 := (F1.2.1 _ (by simp)).trans hh
  have e1Y : σ1.mat (a0 + 1) = σ.mat (a0 + 1) := Env.mat_of_arr (F1.2.2.1 _ (by simp))
  rw [m5, e42, e416, m4, m3, e20, e33, of_diag_zero, e45, m2, e11, m1, e1Y, symPart]
  module

/-- The Frobenius clip of a symmetric `W` at `R₀` (in `s0 + 5`). -/
theorem runs_nsClipC {dv one n0 s0 a0 : ℕ} (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS)
    (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv)
    (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) (hdd : σ.nat (n0 + 9) = d * d)
    (h0 : σ.sc s0 = 0) (hW : (σ.mat (a0 + 5))ᵀ = σ.mat (a0 + 5)) :
    Runs L w (nsClipC L dv one (n0 + 9) n0 s0 (a0 + 5) (a0 + 8)) σ (kNsClip d)
      (fun σ' => σ'.mat (a0 + 5) = frobClip (σ.sc (s0 + 5)) (σ.mat (a0 + 5)) ∧
        Env.Frame σ σ' [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5] [s0 + 8, s0 + 9, s0 + 10, s0 + 11, s0 + 12]
          [a0 + 5, a0 + 8]) := by
  unfold nsClipC kNsClip kMmul kMtrace kMlin
  refine runs_seq (runs_mmul (i := n0) (j := n0 + 1) (l := n0 + 2) (kA := n0 + 3) (kB := n0 + 4) (kC := n0 + 5)
    (C := a0 + 8) (A := a0 + 5) (B := a0 + 5) (s := s0 + 12) (t1 := s0 + 8) (t2 := s0 + 9) σ hdv hone
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp) (by simp; omega) (by simp; omega) (by omega) (by omega) (by omega) (by omega) (by omega) hd h1) fun σ1 h1' => ?_
  obtain ⟨m1, F1, -⟩ := h1'
  refine runs_seq (runs_mtrace (i := n0) (k := n0 + 1) (r := s0 + 10) (A := a0 + 8) (t := s0 + 8) σ1 hdv hone
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F1.1 dv (by simp; omega)).trans hd) ((F1.1 one (by simp; omega)).trans h1)) fun σ2 h2' => ?_
  obtain ⟨c2, F2⟩ := h2'
  have F02 : Env.Frame σ σ2 [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5] [s0 + 8, s0 + 9, s0 + 10, s0 + 11, s0 + 12]
      [a0 + 5, a0 + 8] :=
    Env.Frame.trans (Env.Frame.mono F1 (by simp) (by simp) (by simp)) (Env.Frame.mono F2 (by simp) (by simp) (by simp))
  refine runs_seq_eq (runs_sop1 (L := L) (w := w) (σ := σ2) (x := s0 + 10) (a := s0 + 10) (by omega) (by omega) .sqrt) ?_
  set σ3 := σ2.setSc (s0 + 10) (Op1.sqrt.eval (σ2.sc (s0 + 10))) with hσ3
  have F03 : Env.Frame σ σ3 [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5] [s0 + 8, s0 + 9, s0 + 10, s0 + 11, s0 + 12]
      [a0 + 5, a0 + 8] := Env.Frame.setSc F02 (by simp) _
  have eW3 : σ3.mat (a0 + 5) = σ.mat (a0 + 5) :=
    Env.mat_of_arr (σ' := σ3) ((F2.2.2.1 _ (by simp)).trans (F1.2.2.1 _ (by simp)))
  have e310 : σ3.sc (s0 + 10) = frobNorm (σ.mat (a0 + 5)) := by
    rw [hσ3, Env.setSc_sc, if_pos rfl, c2, m1, trace_mul_self_of_symm _ hW]; rfl
  have e35 : σ3.sc (s0 + 5) = σ.sc (s0 + 5) := by
    rw [hσ3, Env.setSc_sc, if_neg (by omega)]; exact F02.2.1 _ (by simp)
  have e30 : σ3.sc s0 = 0 := by
    rw [hσ3, Env.setSc_sc, if_neg (by omega)]; exact (F02.2.1 _ (by simp)).trans h0
  by_cases hc : σ3.sc (s0 + 5) < σ3.sc (s0 + 10)
  · refine runs_mono (runs_ifS_t (by omega) (by omega) hc (runs_seq_eq (runs_sop2 (L := L) (w := w) (σ := σ3)
      (x := s0 + 11) (a := s0 + 5) (b := s0 + 10) (by omega) (by omega) (by omega) .div)
      (runs_mlin (dd := n0 + 9) (m := n0) (C := a0 + 5) (A := a0 + 5) (B := a0 + 5) (α := s0 + 11) (β := s0)
        (t1 := s0 + 8) (t2 := s0 + 9) _ (by omega) hone
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ((F03.1 _ (by simp)).trans hdd) ((F03.1 one (by simp; omega)).trans h1)))) (by omega) fun σ5 h5 => ?_
    obtain ⟨m5, F5, -⟩ := h5
    refine ⟨?_, Env.Frame.trans (Env.Frame.setSc F03 (by simp) _) (Env.Frame.mono F5 (by simp) (by simp) (by simp))⟩
    have hv : ∀ v : ℝ, (σ3.setSc (s0 + 11) v).sc (s0 + 11) = v := fun v => by simp [Env.setSc_sc]
    have h0' : ∀ v : ℝ, (σ3.setSc (s0 + 11) v).sc s0 = 0 := fun v => by
      rw [Env.setSc_sc, if_neg (by omega)]; exact e30
    have hm' : ∀ v : ℝ, (σ3.setSc (s0 + 11) v).mat (a0 + 5) = σ.mat (a0 + 5) := fun _ => eW3
    rw [m5, hv, h0', hm', zero_smul, add_zero, frobClip, if_pos (by rwa [e35, e310] at hc), e35, e310]
    rfl
  · refine runs_mono (runs_ifS_f (by omega) (by omega) hc (runs_skip _)) (by omega) ?_
    rintro σ' rfl
    refine ⟨?_, F03⟩
    rw [eW3, frobClip, if_neg (by rwa [e35, e310] at hc)]

/-- `Y := m I + (Y^a - Y^b)/2`. -/
theorem runs_nsOutC {dv one n0 s0 a0 : ℕ} (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS)
    (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv)
    (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) (hdd : σ.nat (n0 + 9) = d * d)
    (h0 : σ.sc s0 = 0) (hh : σ.sc (s0 + 1) = 1 / 2) (ho : σ.sc (s0 + 2) = 1) (hmh : σ.sc (s0 + 15) = -1 / 2) :
    Runs L w (nsOutC L dv one (n0 + 9) n0 s0 (a0 + 1) (a0 + 12) (a0 + 13)) σ (kNsOut d)
      (fun σ' => σ'.mat (a0 + 1) = σ.sc (s0 + 3) • (1 : Matrix (Fin d) (Fin d) ℝ) +
          (1 / 2 : ℝ) • (σ.mat (a0 + 12) - σ.mat (a0 + 13)) ∧
        Env.Frame σ σ' [n0, n0 + 1] [s0 + 8, s0 + 9] [a0 + 1]) := by
  unfold nsOutC kNsOut kMlin kMfill kMdiag
  refine runs_seq (runs_mfill (dd := n0 + 9) (m := n0) (A := a0 + 1) (z := s0) σ (by omega) hone (by omega)
    (by omega) (by omega) (by omega) (by omega) hdd h1) fun σ1 h1' => ?_
  obtain ⟨m1, F1, -⟩ := h1'
  refine runs_seq (runs_mdiag (i := n0) (k := n0 + 1) (A := a0 + 1) (z := s0 + 3) σ1 hdv hone (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F1.1 dv (by simp; omega)).trans hd) ((F1.1 one (by simp; omega)).trans h1)) fun σ2 h2' => ?_
  obtain ⟨m2, F2, -⟩ := h2'
  have F02 : Env.Frame σ σ2 [n0, n0 + 1] [s0 + 8, s0 + 9] [a0 + 1] :=
    Env.Frame.trans (Env.Frame.mono F1 (by simp) (by simp) (by simp)) (Env.Frame.mono F2 (by simp) (by simp) (by simp))
  refine runs_seq (runs_mlin (dd := n0 + 9) (m := n0) (C := a0 + 1) (A := a0 + 1) (B := a0 + 12) (α := s0 + 2)
    (β := s0 + 1) (t1 := s0 + 8) (t2 := s0 + 9) σ2 (by omega) hone (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) ((F02.1 _ (by simp)).trans hdd) ((F02.1 one (by simp; omega)).trans h1)) fun σ3 h3' => ?_
  obtain ⟨m3, F3, -⟩ := h3'
  have F03 : Env.Frame σ σ3 [n0, n0 + 1] [s0 + 8, s0 + 9] [a0 + 1] :=
    Env.Frame.trans F02 (Env.Frame.mono F3 (by simp) (by simp) (by simp))
  refine runs_mono (runs_mlin (dd := n0 + 9) (m := n0) (C := a0 + 1) (A := a0 + 1) (B := a0 + 13) (α := s0 + 2)
    (β := s0 + 15) (t1 := s0 + 8) (t2 := s0 + 9) σ3 (by omega) hone (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) ((F03.1 _ (by simp)).trans hdd) ((F03.1 one (by simp; omega)).trans h1)) le_rfl fun σ4 h4' => ?_
  obtain ⟨m4, F4, -⟩ := h4'
  refine ⟨?_, Env.Frame.trans F03 (Env.Frame.mono F4 (by simp) (by simp) (by simp))⟩
  have e32 : σ3.sc (s0 + 2) = 1 := (F03.2.1 _ (by simp)).trans ho
  have e315 : σ3.sc (s0 + 15) = -1 / 2 := (F03.2.1 _ (by simp)).trans hmh
  have e313 : σ3.mat (a0 + 13) = σ.mat (a0 + 13) := Env.mat_of_arr (F03.2.2.1 _ (by simp))
  have e22 : σ2.sc (s0 + 2) = 1 := (F02.2.1 _ (by simp)).trans ho
  have e21 : σ2.sc (s0 + 1) = 1 / 2 := (F02.2.1 _ (by simp)).trans hh
  have e212 : σ2.mat (a0 + 12) = σ.mat (a0 + 12) := Env.mat_of_arr (F02.2.2.1 _ (by simp))
  have e13 : σ1.sc (s0 + 3) = σ.sc (s0 + 3) := F1.2.1 _ (by simp)
  rw [m4, e32, e315, e313, m3, e22, e21, e212, m2, m1, h0, e13, of_diag_zero]
  module

/-- The counts `k`, `⌈log₂ (3k + 3)⌉₊` and `J = 2k + ⌈log₂ (3k + 3)⌉₊ = nsCount k` (`c₀` in `s0 + 6`, `e` in
`s0 + 36`). -/
theorem runs_nsCountC {one n0 s0 : ℕ} (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS)
    (hone : one < L.NN) (honeb : one < n0 ∨ n0 + 20 ≤ one) (h1 : σ.nat one = 1) (k : ℕ)
    (hk : ⌈Real.logb 2 (σ.sc (s0 + 6) / (2 * σ.sc (s0 + 36)))⌉₊ = k) :
    Runs L w (nsCountC L one n0 s0 (s0 + 36)) σ (kNsCount k (Nat.clog 2 (3 * k + 3)))
      (fun σ' => σ'.nat (n0 + 8) = nsCount k ∧ Env.Frame σ σ' [n0 + 6, n0 + 7, n0 + 8] [s0 + 17, s0 + 18] []) := by
  unfold nsCountC kNsCount
  set σ₁ := { σ with sc := sEval σ.nat (nsKL s0 (s0 + 36)) σ.sc } with hσ₁
  have hσ₁_nat_one : σ₁.nat one = 1 := by simpa [hσ₁] using h1
  have hσ₁_sc : σ₁.sc (s0 + 17) = Real.logb 2 (σ.sc (s0 + 6) / (2 * σ.sc (s0 + 36))) := by
    dsimp [σ₁, sEval, nsKL]
    pg_val
    dsimp [Real.logb]
    rw [two_mul]
  have h_ceil_eq_k : ⌈σ₁.sc (s0 + 17)⌉₊ = k := by rw [hσ₁_sc, hk]
  have h_cost1 : sCost (nsKL s0 (s0 + 36)) = 6 := by
    unfold nsKL sCost; simp [SI.cost]
  have h_sprog1 : Runs L w (sprog L (nsKL s0 (s0 + 36))) σ (sCost (nsKL s0 (s0 + 36))) (· = σ₁) := by
    refine runs_sprog (nsKL s0 (s0 + 36)) ?_ σ
    simp [nsKL, SI.ok]
    omega
  have hi1 : n0 + 6 < L.NN := by omega
  have hio1 : n0 + 6 ≠ one := by
    rcases honeb with (h | h)
    · have : one < n0 + 6 := by omega
      omega
    · have : n0 + 6 < one := by omega
      omega
  have hx1 : s0 + 17 < L.NS := by omega
  have ht1 : s0 + 18 < L.NS := by omega
  have hxt1 : s0 + 17 ≠ s0 + 18 := by omega
  have h_nceil1 : Runs L w (nceil L (n0 + 6) one (s0 + 17) (s0 + 18)) σ₁
      (⌈σ₁.sc (s0 + 17)⌉₊ * 4 + 4) (· = (σ₁.setNat (n0 + 6) ⌈σ₁.sc (s0 + 17)⌉₊).setSc (s0 + 18) ⌈σ₁.sc (s0 + 17)⌉₊) := by
    refine runs_nceil σ₁ hi1 hone hio1 hx1 ht1 hxt1 hσ₁_nat_one
  set σ₂ := (σ₁.setNat (n0 + 6) ⌈σ₁.sc (s0 + 17)⌉₊).setSc (s0 + 18) ⌈σ₁.sc (s0 + 17)⌉₊ with hσ₂
  have h_one_ne_n06 : one ≠ n0 + 6 := by
    rcases honeb with (h | h)
    · omega
    · omega
  have h_one_ne_n07 : one ≠ n0 + 7 := by
    rcases honeb with (h | h)
    · omega
    · omega
  have hσ₂_nat_one : σ₂.nat one = 1 := by
    dsimp [σ₂, σ₁]
    simpa [h_one_ne_n06] using h1
  have hσ₂_nat_n06 : σ₂.nat (n0 + 6) = k := by
    dsimp [σ₂]; simp [h_ceil_eq_k]
  set σ₃ := { σ₂ with sc := sEval σ₂.nat (nsCL s0 (n0 + 6)) σ₂.sc } with hσ₃
  have hσ₃_sc : σ₃.sc (s0 + 17) = Real.logb 2 ((3 * k + 3 : ℕ) : ℝ) := by
    dsimp [σ₃]
    dsimp [sEval, nsCL]
    pg_val
    rw [hσ₂_nat_n06]
    dsimp [Real.logb]
  have h_ceil2_eq : ⌈σ₃.sc (s0 + 17)⌉₊ = Nat.clog 2 (3 * k + 3) := by
    rw [hσ₃_sc]
    simpa using Real.natCeil_logb_natCast 2 (3 * k + 3)
  have h_cost2 : sCost (nsCL s0 (n0 + 6)) = 8 := by
    unfold nsCL sCost; simp [SI.cost]
  have h_sprog2 : Runs L w (sprog L (nsCL s0 (n0 + 6))) σ₂ (sCost (nsCL s0 (n0 + 6))) (· = σ₃) := by
    refine runs_sprog (nsCL s0 (n0 + 6)) ?_ σ₂
    simp [nsCL, SI.ok]
    omega
  have hi2 : n0 + 7 < L.NN := by omega
  have hio2 : n0 + 7 ≠ one := by
    rcases honeb with (h | h)
    · have : one < n0 + 7 := by omega
      omega
    · have : n0 + 7 < one := by omega
      omega
  have hx2 : s0 + 17 < L.NS := by omega
  have ht2 : s0 + 18 < L.NS := by omega
  have hxt2 : s0 + 17 ≠ s0 + 18 := by omega
  have h_nceil2 : Runs L w (nceil L (n0 + 7) one (s0 + 17) (s0 + 18)) σ₃
      (⌈σ₃.sc (s0 + 17)⌉₊ * 4 + 4) (· = (σ₃.setNat (n0 + 7) ⌈σ₃.sc (s0 + 17)⌉₊).setSc (s0 + 18) ⌈σ₃.sc (s0 + 17)⌉₊) := by
    refine runs_nceil σ₃ hi2 hone hio2 hx2 ht2 hxt2 hσ₂_nat_one
  set σ₄ := (σ₃.setNat (n0 + 7) ⌈σ₃.sc (s0 + 17)⌉₊).setSc (s0 + 18) ⌈σ₃.sc (s0 + 17)⌉₊ with hσ₄
  have hσ₄_nat_one : σ₄.nat one = 1 := by
    dsimp [σ₄, σ₃, σ₂, σ₁]
    simp [h_one_ne_n06, h_one_ne_n07, h1]
  have hσ₄_nat_n07 : σ₄.nat (n0 + 7) = Nat.clog 2 (3 * k + 3) := by
    dsimp [σ₄]; simp [h_ceil2_eq]
  have hi_nadd1 : n0 + 8 < L.NN := by omega
  have h_nadd1 : Runs L w (nadd (n0 + 8) (n0 + 6) (n0 + 6)) σ₄ 1 (· = σ₄.setNat (n0 + 8) (σ₄.nat (n0 + 6) + σ₄.nat (n0 + 6))) := by
    refine runs_nadd hi_nadd1 (by omega) (by omega)
  set σ₅ := σ₄.setNat (n0 + 8) (σ₄.nat (n0 + 6) + σ₄.nat (n0 + 6)) with hσ₅
  have hσ₅_nat_n08 : σ₅.nat (n0 + 8) = 2 * k := by
    dsimp [σ₅]
    simp
    have h : σ₄.nat (n0 + 6) = k := by
      simpa [σ₄, σ₃] using hσ₂_nat_n06
    rw [h]
    ring
  have h_nadd2 : Runs L w (nadd (n0 + 8) (n0 + 8) (n0 + 7)) σ₅ 1 (· = σ₅.setNat (n0 + 8) (σ₅.nat (n0 + 8) + σ₅.nat (n0 + 7))) := by
    refine runs_nadd hi_nadd1 (by omega) (by omega)
  set σ₆ := σ₅.setNat (n0 + 8) (σ₅.nat (n0 + 8) + σ₅.nat (n0 + 7)) with hσ₆
  have hσ₆_nat_n08 : σ₆.nat (n0 + 8) = nsCount k := by
    dsimp [σ₆, σ₅]
    simp
    have h4 : σ₄.nat (n0 + 6) = k := by
      simpa [σ₄, σ₃] using hσ₂_nat_n06
    have h7 : σ₄.nat (n0 + 7) = Nat.clog 2 (3 * k + 3) := hσ₄_nat_n07
    rw [h4, h7]
    dsimp [nsCount]
    ring
  have h_frame : Env.Frame σ σ₆ [n0 + 6, n0 + 7, n0 + 8] [s0 + 17, s0 + 18] [] := by
    dsimp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, Env.Frame]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      have hi' : i ≠ n0 + 6 ∧ i ≠ n0 + 7 ∧ i ≠ n0 + 8 := by
        simpa using hi
      rcases hi' with ⟨hi1, hi2, hi3⟩
      simp [hi1, hi2, hi3]
    · intro x hx
      have hx' : x ≠ s0 + 17 ∧ x ≠ s0 + 18 := by
        simpa using hx
      rcases hx' with ⟨hx1, hx2⟩
      have h_dst1 : x ∉ (nsKL s0 (s0 + 36)).map SI.dst := by
        simp [nsKL, SI.dst, hx1, hx2]
      have h_dst2 : x ∉ (nsCL s0 (n0 + 6)).map SI.dst := by
        simp [nsCL, SI.dst, hx1, hx2]
      simp [sEval_frame, h_dst1, h_dst2, hx2]
    · intro a ha; simp
    · rfl
    · rfl
    · rfl
  have h_total_cost : sCost (nsKL s0 (s0 + 36)) + (⌈σ₁.sc (s0 + 17)⌉₊ * 4 + 4) +
      sCost (nsCL s0 (n0 + 6)) + (⌈σ₃.sc (s0 + 17)⌉₊ * 4 + 4) + 1 + 1 = kNsCount k (Nat.clog 2 (3 * k + 3)) := by
    rw [h_cost1, h_cost2, h_ceil_eq_k, h_ceil2_eq]
    dsimp [kNsCount]
    omega
  have h_inner : Runs L w (nadd (n0 + 8) (n0 + 8) (n0 + 7)) σ₅ 1 (· = σ₆) := h_nadd2
  have h_seq_EF : Runs L w (.seq (nadd (n0 + 8) (n0 + 6) (n0 + 6)) (nadd (n0 + 8) (n0 + 8) (n0 + 7))) σ₄
      (1 + 1) (· = σ₆) :=
    runs_seq_eq h_nadd1 h_inner
  have h_seq_DEF : Runs L w (.seq (nceil L (n0 + 7) one (s0 + 17) (s0 + 18))
      (.seq (nadd (n0 + 8) (n0 + 6) (n0 + 6)) (nadd (n0 + 8) (n0 + 8) (n0 + 7)))) σ₃
      ((⌈σ₃.sc (s0 + 17)⌉₊ * 4 + 4) + (1 + 1)) (· = σ₆) :=
    runs_seq_eq h_nceil2 h_seq_EF
  have h_seq_CDEF : Runs L w (.seq (sprog L (nsCL s0 (n0 + 6)))
      (.seq (nceil L (n0 + 7) one (s0 + 17) (s0 + 18))
        (.seq (nadd (n0 + 8) (n0 + 6) (n0 + 6)) (nadd (n0 + 8) (n0 + 8) (n0 + 7))))) σ₂
      (sCost (nsCL s0 (n0 + 6)) + ((⌈σ₃.sc (s0 + 17)⌉₊ * 4 + 4) + (1 + 1))) (· = σ₆) :=
    runs_seq_eq h_sprog2 h_seq_DEF
  have h_seq_BCDEF : Runs L w (.seq (nceil L (n0 + 6) one (s0 + 17) (s0 + 18))
      (.seq (sprog L (nsCL s0 (n0 + 6)))
        (.seq (nceil L (n0 + 7) one (s0 + 17) (s0 + 18))
          (.seq (nadd (n0 + 8) (n0 + 6) (n0 + 6)) (nadd (n0 + 8) (n0 + 8) (n0 + 7)))))) σ₁
      ((⌈σ₁.sc (s0 + 17)⌉₊ * 4 + 4) + (sCost (nsCL s0 (n0 + 6)) + ((⌈σ₃.sc (s0 + 17)⌉₊ * 4 + 4) + (1 + 1)))) (· = σ₆) :=
    runs_seq_eq h_nceil1 h_seq_CDEF
  have h_chain : Runs L w (.seq (sprog L (nsKL s0 (s0 + 36)))
      (.seq (nceil L (n0 + 6) one (s0 + 17) (s0 + 18))
        (.seq (sprog L (nsCL s0 (n0 + 6)))
          (.seq (nceil L (n0 + 7) one (s0 + 17) (s0 + 18))
            (.seq (nadd (n0 + 8) (n0 + 6) (n0 + 6)) (nadd (n0 + 8) (n0 + 8) (n0 + 7))))))) σ
      (sCost (nsKL s0 (s0 + 36)) + ((⌈σ₁.sc (s0 + 17)⌉₊ * 4 + 4) + (sCost (nsCL s0 (n0 + 6)) + ((⌈σ₃.sc (s0 + 17)⌉₊ * 4 + 4) + (1 + 1))))) (· = σ₆) :=
    runs_seq_eq h_sprog1 h_seq_BCDEF
  rw [h_cost1, h_cost2, h_ceil_eq_k, h_ceil2_eq] at h_chain
  refine runs_mono h_chain le_rfl ?_
  intro σ' (rfl : σ' = σ₆)
  exact ⟨hσ₆_nat_n08, h_frame⟩

set_option maxHeartbeats 1000000 in
/-- CLAMP-NS at the bounds `a` (`s0 + 21`), `b` (`s0 + 22`), the tolerance `e` (`s0 + 36`) on the array `a0 + 1`. -/
theorem runs_clampNSC {dv one n0 s0 a0 : ℕ} (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS)
    (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv)
    (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) (hdd : σ.nat (n0 + 9) = d * d)
    (a b e : ℝ) (ha : σ.sc (s0 + 21) = a) (hb : σ.sc (s0 + 22) = b) (he : σ.sc (s0 + 36) = e)
    (hdR : σ.sc (s0 + 48) = d) :
    Runs L w (clampNSC L dv one (n0 + 9) n0 s0 (a0 + 1) (a0 + 5) (a0 + 6) (a0 + 7) (a0 + 8) (a0 + 9) (a0 + 11)
        (a0 + 12) (a0 + 13) (s0 + 21) (s0 + 22) (s0 + 36) (s0 + 48)) σ
      (kClampNS d (cnK d a b e) (Nat.clog 2 (3 * cnK d a b e + 3)) (cnsJ d a b e))
      (fun σ' => σ'.mat (a0 + 1) = clampNSMat a b e (cnsJ d a b e) (σ.mat (a0 + 1)) ∧
        Env.Frame σ σ' (pgTmpN n0) (pgTmpS s0)
          [a0 + 1, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 11, a0 + 12, a0 + 13]) := by
  unfold clampNSC kClampNS
  -- the parameters
  have hP := runs_sprog (L := L) (w := w) (nsParL s0 (s0 + 21) (s0 + 22) (s0 + 48)) (by
    simp only [nsParL, List.all_cons, List.all_nil, SI.ok, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    omega) σ
  rw [nsParL_cost] at hP
  refine runs_seq_eq hP ?_
  set σ1 : Env d := { σ with sc := sEval σ.nat (nsParL s0 (s0 + 21) (s0 + 22) (s0 + 48)) σ.sc } with hσ1
  have fr1 : ∀ x, x ∉ [s0, s0 + 1, s0 + 2, s0 + 3, s0 + 4, s0 + 5, s0 + 6, s0 + 7, s0 + 14, s0 + 15, s0 + 16] →
      σ1.sc x = σ.sc x := fun x hx => sEval_frame _ _ _ (by
    rw [nsParL_dst]; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
  have F1 : Env.Frame σ σ1 [] [s0, s0 + 1, s0 + 2, s0 + 3, s0 + 4, s0 + 5, s0 + 6, s0 + 7, s0 + 14, s0 + 15, s0 + 16]
      [] := ⟨fun _ _ => rfl, fr1, fun _ _ => rfl, rfl, rfl, rfl⟩
  have e36 : σ1.sc (s0 + 36) = e := (fr1 _ (by simp)).trans he
  have v0 : σ1.sc s0 = 0 := nsParL_v0 σ.nat σ.sc s0
  have v1 : σ1.sc (s0 + 1) = 1 / 2 := nsParL_v1 σ.nat σ.sc s0
  have v2 : σ1.sc (s0 + 2) = 1 := nsParL_v2 σ.nat σ.sc s0
  have v3 : σ1.sc (s0 + 3) = cnMid a b := by rw [← ha, ← hb]; exact nsParL_v3 σ.nat σ.sc s0
  have v5 : σ1.sc (s0 + 5) = cnR0 d a b := by rw [← ha, ← hb]; exact nsParL_v5 σ.nat σ.sc s0 hdR
  have v6 : σ1.sc (s0 + 6) = cnC0 d a b := by rw [← ha, ← hb]; exact nsParL_v6 σ.nat σ.sc s0 hdR
  have v7 : σ1.sc (s0 + 7) = (cnC0 d a b)⁻¹ := by rw [← ha, ← hb]; exact nsParL_v7 σ.nat σ.sc s0 hdR
  have v14 : σ1.sc (s0 + 14) = 3 := nsParL_v14 σ.nat σ.sc s0
  have v15 : σ1.sc (s0 + 15) = -1 / 2 := nsParL_v15 σ.nat σ.sc s0
  have v16 : σ1.sc (s0 + 16) = -1 := nsParL_v16 σ.nat σ.sc s0
  -- the count
  refine runs_seq (runs_nsCountC σ1 hn0 hs0 hone honeb h1 (cnK d a b e) (by rw [v6, e36]; rfl)) fun σ2 h2' => ?_
  obtain ⟨c2, F2⟩ := h2'
  have hpar : ∀ σ' : Env d, Env.Frame σ2 σ' [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6] [s0 + 8, s0 + 9, s0 + 10, s0 + 11, s0 + 12, s0 + 13, s0 + 17, s0 + 18] [a0 + 1, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 11, a0 + 12, a0 + 13] → ∀ p, p ∉ [s0 + 8, s0 + 9, s0 + 10, s0 + 11, s0 + 12, s0 + 13, s0 + 17, s0 + 18] → σ'.sc p = σ1.sc p :=
    fun σ' G p hp => (G.2.1 p hp).trans (F2.2.1 p (fun h => hp (by simp at h ⊢; omega)))
  have hnat : ∀ σ' : Env d, Env.Frame σ2 σ' [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6] [s0 + 8, s0 + 9, s0 + 10, s0 + 11, s0 + 12, s0 + 13, s0 + 17, s0 + 18] [a0 + 1, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 11, a0 + 12, a0 + 13] → σ'.nat dv = d ∧ σ'.nat one = 1 ∧
      σ'.nat (n0 + 9) = d * d ∧ σ'.nat (n0 + 8) = cnsJ d a b e := fun σ' G =>
    ⟨(G.1 dv (by simp; omega)).trans ((F2.1 dv (by simp; omega)).trans hd),
      (G.1 one (by simp; omega)).trans ((F2.1 one (by simp; omega)).trans h1),
      (G.1 _ (by simp)).trans ((F2.1 _ (by simp)).trans hdd), (G.1 _ (by simp)).trans c2⟩
  have G2 : Env.Frame σ2 σ2 [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6] [s0 + 8, s0 + 9, s0 + 10, s0 + 11, s0 + 12, s0 + 13, s0 + 17, s0 + 18] [a0 + 1, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 11, a0 + 12, a0 + 13] := Env.Frame.refl _ _ _ _
  obtain ⟨d2, o2, dd2, -⟩ := hnat σ2 G2
  -- `W := sym Y - m I`, then its clip
  refine runs_seq (runs_nsSymC σ2 hn0 hs0 ha0 hdv hone hdvb honeb d2 o2 dd2
    ((hpar σ2 G2 _ (by simp)).trans v0) ((hpar σ2 G2 _ (by simp)).trans v1) ((hpar σ2 G2 _ (by simp)).trans v2)
    ((hpar σ2 G2 _ (by simp)).trans v16)) fun σ3 h3' => ?_
  obtain ⟨m3, F3⟩ := h3'
  have G3 : Env.Frame σ2 σ3 [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6] [s0 + 8, s0 + 9, s0 + 10, s0 + 11, s0 + 12, s0 + 13, s0 + 17, s0 + 18] [a0 + 1, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 11, a0 + 12, a0 + 13] := Env.Frame.mono F3 (by simp) (by simp) (by simp)
  obtain ⟨d3, o3, dd3, -⟩ := hnat σ3 G3
  refine runs_seq (runs_nsClipC σ3 hn0 hs0 ha0 hdv hone hdvb honeb d3 o3 dd3 ((hpar σ3 G3 _ (by simp)).trans v0)
    (by rw [m3]; exact symPart_sub_symm _ _)) fun σ4 h4' => ?_
  obtain ⟨m4, F4⟩ := h4'
  have G4 : Env.Frame σ2 σ4 [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6] [s0 + 8, s0 + 9, s0 + 10, s0 + 11, s0 + 12, s0 + 13, s0 + 17, s0 + 18] [a0 + 1, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 11, a0 + 12, a0 + 13] := Env.Frame.trans G3 (Env.Frame.mono F4 (by simp) (by simp) (by simp))
  -- the first root
  have hPa := runs_sprog (L := L) (w := w)
    [SI.op2 .sub (s0 + 13) (s0 + 3) (s0 + 21), SI.op2 .sub (s0 + 13) (s0 + 13) (s0 + 36)] (by simp [SI.ok]; omega) σ4
  rw [show sCost [SI.op2 .sub (s0 + 13) (s0 + 3) (s0 + 21), SI.op2 .sub (s0 + 13) (s0 + 13) (s0 + 36)] = 2 by
    simp [sCost, SI.cost]] at hPa
  refine runs_seq_eq hPa ?_
  set σ5 : Env d := { σ4 with sc := (sEval σ4.nat
    [SI.op2 .sub (s0 + 13) (s0 + 3) (s0 + 21), SI.op2 .sub (s0 + 13) (s0 + 13) (s0 + 36)] σ4.sc) } with hσ5
  have G5 : Env.Frame σ2 σ5 [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6] [s0 + 8, s0 + 9, s0 + 10, s0 + 11, s0 + 12, s0 + 13, s0 + 17, s0 + 18] [a0 + 1, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 11, a0 + 12, a0 + 13] := Env.Frame.trans G4
    ⟨fun _ _ => rfl, fun x hx => sEval_frame _ _ _ (by simp [SI.dst]; simp at hx; omega), fun _ _ => rfl, rfl, rfl, rfl⟩
  have e513 : σ5.sc (s0 + 13) = cnMid a b - a - e := by
    rw [show σ5.sc (s0 + 13) = σ4.sc (s0 + 3) - σ4.sc (s0 + 21) - σ4.sc (s0 + 36) from nsShA_v13 σ4.nat σ4.sc s0, hpar σ4 G4 _ (by simp), hpar σ4 G4 _ (by simp), hpar σ4 G4 _ (by simp), v3,
      (fr1 _ (by simp)).trans ha, e36]
  obtain ⟨d5, o5, dd5, J5⟩ := hnat σ5 G5
  refine runs_seq (runs_nsRootC σ5 hn0 hs0 ha0 hdv hone hdvb honeb d5 o5 dd5 ((hpar σ5 G5 _ (by simp)).trans v0)
    ((hpar σ5 G5 _ (by simp)).trans v1) ((hpar σ5 G5 _ (by simp)).trans v2) ((hpar σ5 G5 _ (by simp)).trans v14)
    ((hpar σ5 G5 _ (by simp)).trans v16) (a0 + 12) (Or.inl rfl) (cnsJ d a b e) J5) fun σ6 h6' => ?_
  obtain ⟨m6, F6⟩ := h6'
  have G6 : Env.Frame σ2 σ6 [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6] [s0 + 8, s0 + 9, s0 + 10, s0 + 11, s0 + 12, s0 + 13, s0 + 17, s0 + 18] [a0 + 1, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 11, a0 + 12, a0 + 13] := Env.Frame.trans G5 (Env.Frame.mono F6 (by simp) (by simp) (by simp))
  -- the second root
  have hPb := runs_sprog (L := L) (w := w)
    [SI.op2 .sub (s0 + 13) (s0 + 3) (s0 + 22), SI.op2 .add (s0 + 13) (s0 + 13) (s0 + 36)] (by simp [SI.ok]; omega) σ6
  rw [show sCost [SI.op2 .sub (s0 + 13) (s0 + 3) (s0 + 22), SI.op2 .add (s0 + 13) (s0 + 13) (s0 + 36)] = 2 by
    simp [sCost, SI.cost]] at hPb
  refine runs_seq_eq hPb ?_
  set σ7 : Env d := { σ6 with sc := (sEval σ6.nat
    [SI.op2 .sub (s0 + 13) (s0 + 3) (s0 + 22), SI.op2 .add (s0 + 13) (s0 + 13) (s0 + 36)] σ6.sc) } with hσ7
  have G7 : Env.Frame σ2 σ7 [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6] [s0 + 8, s0 + 9, s0 + 10, s0 + 11, s0 + 12, s0 + 13, s0 + 17, s0 + 18] [a0 + 1, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 11, a0 + 12, a0 + 13] := Env.Frame.trans G6
    ⟨fun _ _ => rfl, fun x hx => sEval_frame _ _ _ (by simp [SI.dst]; simp at hx; omega), fun _ _ => rfl, rfl, rfl, rfl⟩
  have e713 : σ7.sc (s0 + 13) = cnMid a b - b + e := by
    rw [show σ7.sc (s0 + 13) = σ6.sc (s0 + 3) - σ6.sc (s0 + 22) + σ6.sc (s0 + 36) from nsShB_v13 σ6.nat σ6.sc s0, hpar σ6 G6 _ (by simp), hpar σ6 G6 _ (by simp), hpar σ6 G6 _ (by simp), v3,
      (fr1 _ (by simp)).trans hb, e36]
  obtain ⟨d7, o7, dd7, J7⟩ := hnat σ7 G7
  refine runs_seq (runs_nsRootC σ7 hn0 hs0 ha0 hdv hone hdvb honeb d7 o7 dd7 ((hpar σ7 G7 _ (by simp)).trans v0)
    ((hpar σ7 G7 _ (by simp)).trans v1) ((hpar σ7 G7 _ (by simp)).trans v2) ((hpar σ7 G7 _ (by simp)).trans v14)
    ((hpar σ7 G7 _ (by simp)).trans v16) (a0 + 13) (Or.inr rfl) (cnsJ d a b e) J7) fun σ8 h8' => ?_
  obtain ⟨m8, F8⟩ := h8'
  have G8 : Env.Frame σ2 σ8 [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6] [s0 + 8, s0 + 9, s0 + 10, s0 + 11, s0 + 12, s0 + 13, s0 + 17, s0 + 18] [a0 + 1, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 11, a0 + 12, a0 + 13] := Env.Frame.trans G7 (Env.Frame.mono F8 (by simp) (by simp) (by simp))
  obtain ⟨d8, o8, dd8, -⟩ := hnat σ8 G8
  -- the output
  refine runs_mono (runs_nsOutC σ8 hn0 hs0 ha0 hdv hone hdvb honeb d8 o8 dd8 ((hpar σ8 G8 _ (by simp)).trans v0)
    ((hpar σ8 G8 _ (by simp)).trans v1) ((hpar σ8 G8 _ (by simp)).trans v2) ((hpar σ8 G8 _ (by simp)).trans v15))
    le_rfl fun σ9 h9' => ?_
  obtain ⟨m9, F9⟩ := h9'
  have G9 : Env.Frame σ2 σ9 [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6] [s0 + 8, s0 + 9, s0 + 10, s0 + 11, s0 + 12, s0 + 13, s0 + 17, s0 + 18] [a0 + 1, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 11, a0 + 12, a0 + 13] := Env.Frame.trans G8 (Env.Frame.mono F9 (by simp) (by simp) (by simp))
  refine ⟨?_, Env.Frame.trans (Env.Frame.mono F1 (by simp) (by simp [pgTmpS]) (by simp))
    (Env.Frame.trans (Env.Frame.mono F2 (by simp [pgTmpN]) (by simp [pgTmpS]) (by simp))
      (Env.Frame.mono G9 (by simp [pgTmpN]) (by simp [pgTmpS]) (by simp)))⟩
  have eYa : σ8.mat (a0 + 12) = σ6.mat (a0 + 12) := Env.mat_of_arr (σ' := σ8) (F8.2.2.1 _ (by simp))
  have eW7 : σ7.mat (a0 + 5) = σ4.mat (a0 + 5) := Env.mat_of_arr (σ' := σ7) (F6.2.2.1 _ (by simp))
  have eY2 : σ2.mat (a0 + 1) = σ.mat (a0 + 1) := Env.mat_of_arr (σ' := σ2) (F2.2.2.1 _ (by simp))
  have e83 : σ8.sc (s0 + 3) = cnMid a b := (hpar σ8 G8 _ (by simp)).trans v3
  have e77 : σ7.sc (s0 + 7) = (cnC0 d a b)⁻¹ := (hpar σ7 G7 _ (by simp)).trans v7
  have e57 : σ5.sc (s0 + 7) = (cnC0 d a b)⁻¹ := (hpar σ5 G5 _ (by simp)).trans v7
  have e35 : σ3.sc (s0 + 5) = cnR0 d a b := (hpar σ3 G3 _ (by simp)).trans v5
  have e23 : σ2.sc (s0 + 3) = cnMid a b := (hpar σ2 G2 _ (by simp)).trans v3
  rw [m9, e83, eYa, m6, m8, e77, e713, eW7, e57, e513, show σ5.mat (a0 + 5) = σ4.mat (a0 + 5) from rfl, m4, e35, m3,
    eY2, e23]
  unfold clampNSMat clampNSRoot clipSym
  have k1 : ∀ W : Matrix (Fin d) (Fin d) ℝ, W + (cnMid a b - a - e) • (1 : Matrix (Fin d) (Fin d) ℝ) =
      cnMid a b • 1 + W - (a + e) • 1 := fun W => by module
  have k2 : ∀ W : Matrix (Fin d) (Fin d) ℝ, W + (cnMid a b - b + e) • (1 : Matrix (Fin d) (Fin d) ℝ) =
      cnMid a b • 1 + W - (b - e) • 1 := fun W => by module
  rw [k1, k2]

/-- The move and the projection of a descent step with CLAMP-NS, at the stage variables of the ratio `ρ`. -/
theorem runs_pgUpdNS {dv one n0 s0 a0 : ℕ} (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS)
    (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv)
    (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) (hdd : σ.nat (n0 + 9) = d * d)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : σ.sc (s0 + 19) = ρ) (htmin : σ.sc (s0 + 21) = pgTmin d ρ)
    (hLD : σ.sc (s0 + 22) = pgLD ρ) (hdR : σ.sc (s0 + 48) = d) (hN : σ.nat (n0 + 11) = pgNs d ρ) :
    Runs L w (pgUpdNS L dv one n0 s0 a0) σ (kUpdNS d (nsK d ρ) (Nat.clog 2 (3 * nsK d ρ + 3)) (nsCount (nsK d ρ)))
      (fun σ' => WithLp.toLp 2 (σ'.vec a0) =
          ballClip (σ.sc (s0 + 23)) (WithLp.toLp 2 (σ.vec a0 + σ.sc (s0 + 30) • σ.vec (a0 + 10))) ∧
        σ'.mat (a0 + 1) = clampNSRoutine.run d (pgTmin d ρ) (pgLD ρ) (pgEpr d ρ)
          (σ.mat (a0 + 1) + σ.sc (s0 + 30) • σ.mat (a0 + 14)) ∧
        Env.Frame σ σ' (pgTmpN n0) (pgTmpS s0 ++ [s0 + 34, s0 + 35, s0 + 36])
          [a0, a0 + 1, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 11, a0 + 12, a0 + 13]) := by
  unfold pgUpdNS kUpdNS
  refine runs_seq (runs_vaxpy (i := n0) (y := a0) (x := a0 + 10) (α := s0 + 30) (t1 := s0 + 8) (t2 := s0 + 9) σ hdv
    hone (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) hd h1) fun σ1 h1' => ?_
  obtain ⟨v1, F01, -⟩ := h1'
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := σ1) (x := s0 + 2) (by omega) 1) ?_
  set σ2 := σ1.setSc (s0 + 2) ((1 : ℚ) : ℝ) with hσ2
  have F02 : Env.Frame σ σ2 [n0] [s0 + 2, s0 + 8, s0 + 9] [a0] :=
    Env.Frame.setSc (Env.Frame.mono F01 (by simp) (by simp) (by simp)) (by simp) _
  refine runs_seq (runs_mlin (m := n0) (C := a0 + 1) (A := a0 + 1) (B := a0 + 14) (α := s0 + 2) (β := s0 + 30)
    (t1 := s0 + 8) (t2 := s0 + 9) σ2 (by omega) hone (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F02.1 _ (by simp)).trans hdd) ((F02.1 one (by simp; omega)).trans h1)) fun σ3 h3 => ?_
  obtain ⟨m3, F23, -⟩ := h3
  have F03 : Env.Frame σ σ3 [n0] [s0 + 2, s0 + 8, s0 + 9] [a0, a0 + 1] :=
    Env.Frame.trans (Env.Frame.mono F02 (by simp) (by simp) (by simp))
      (Env.Frame.mono F23 (by simp) (by simp) (by simp))
  refine runs_seq (runs_vnorm (i := n0) (r := s0 + 34) (x := a0) (t1 := s0 + 8) (t2 := s0 + 9) σ3 hdv hone
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F03.1 dv (by simp; omega)).trans hd) ((F03.1 one (by simp; omega)).trans h1)) fun σ4 h4 => ?_
  obtain ⟨c4, F34⟩ := h4
  have F04 : Env.Frame σ σ4 [n0] [s0 + 2, s0 + 8, s0 + 9, s0 + 34] [a0, a0 + 1] :=
    Env.Frame.trans (Env.Frame.mono F03 (by simp) (by simp) (by simp))
      (Env.Frame.mono F34 (by simp) (by simp) (by simp))
  have v4 : σ4.vec a0 = σ3.vec a0 := Env.vec_of_arr (F34.2.2.1 _ (by simp))
  refine runs_seq (runs_clip (i := n0) (R := s0 + 23) (r := s0 + 34) (q := s0 + 35) (y := a0) (t := s0 + 8) σ4 hdv
    hone (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F04.1 dv (by simp; omega)).trans hd) ((F04.1 one (by simp; omega)).trans h1)
    (by rw [c4, v4, norm_toLp_eq])) fun σ5 h5 => ?_
  obtain ⟨v5, F45⟩ := h5
  have F05 : Env.Frame σ σ5 [n0] [s0 + 2, s0 + 8, s0 + 9, s0 + 34, s0 + 35] [a0, a0 + 1] :=
    Env.Frame.trans (Env.Frame.mono F04 (by simp) (by simp) (by simp))
      (Env.Frame.mono F45 (by simp) (by simp) (by simp))
  have s5 : ∀ x, x ≠ s0 + 2 → x ≠ s0 + 8 → x ≠ s0 + 9 → x ≠ s0 + 34 → x ≠ s0 + 35 → σ5.sc x = σ.sc x :=
    fun x h2 h8 h9 h34 h35 => F05.2.1 x (by simp [h2, h8, h9, h34, h35])
  have n5 : ∀ i, i ≠ n0 → σ5.nat i = σ.nat i := fun i hi => F05.1 i (by simp [hi])
  -- `e'` from the stage variables
  refine runs_mono (K := sCost (pgEprL n0 s0) + kClampNS d (cnK d (pgTmin d ρ) (pgLD ρ) (pgEpr d ρ))
      (Nat.clog 2 (3 * cnK d (pgTmin d ρ) (pgLD ρ) (pgEpr d ρ) + 3)) (cnsJ d (pgTmin d ρ) (pgLD ρ) (pgEpr d ρ)))
    ?_ (by rw [pgEprL_cost]; exact le_rfl) (fun _ h => h)
  refine runs_seq_eq (runs_sprog (L := L) (w := w) (pgEprL n0 s0) (pgEprL_ok s0 n0 hn0 hs0) σ5) ?_
  set σ6 : Env d := { σ5 with sc := sEval σ5.nat (pgEprL n0 s0) σ5.sc } with hσ6
  have s6 : ∀ x, x ≠ s0 + 3 → x ≠ s0 + 4 → x ≠ s0 + 5 → x ≠ s0 + 6 → x ≠ s0 + 7 → x ≠ s0 + 36 →
      σ6.sc x = σ5.sc x := fun x h3 h4 h5 h6 h7 h36 => pgEprL_frame _ _ _ _ h3 h4 h5 h6 h7 h36
  have e36 : σ6.sc (s0 + 36) = pgEpr d ρ :=
    pgEprL_v36 σ5.nat σ5.sc s0 n0 hρ0 ((s5 _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans hρ)
      ((s5 _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans htmin)
      ((s5 _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans hLD)
      ((s5 _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans hdR) ((n5 _ (by omega)).trans hN)
  have F56 : Env.Frame σ5 σ6 [] [s0 + 3, s0 + 4, s0 + 5, s0 + 6, s0 + 7, s0 + 36] [] :=
    ⟨fun _ _ => rfl, fun x hx => s6 x (by simp at hx; omega) (by simp at hx; omega) (by simp at hx; omega)
      (by simp at hx; omega) (by simp at hx; omega) (by simp at hx; omega), fun _ _ => rfl, rfl, rfl, rfl⟩
  have F06 : Env.Frame σ σ6 [n0] [s0 + 2, s0 + 3, s0 + 4, s0 + 5, s0 + 6, s0 + 7, s0 + 8, s0 + 9, s0 + 34, s0 + 35,
      s0 + 36] [a0, a0 + 1] :=
    Env.Frame.trans (Env.Frame.mono F05 (by simp) (by simp) (by simp))
      (Env.Frame.mono F56 (by simp) (by simp) (by simp))
  have sc6 : ∀ k, k ∈ [21, 22, 48] → σ6.sc (s0 + k) = σ.sc (s0 + k) := fun k hk =>
    F06.2.1 _ (by simp at hk; rcases hk with rfl | rfl | rfl <;> simp)
  refine runs_mono (runs_clampNSC (L := L) (w := w) σ6 hn0 hs0 ha0 hdv hone hdvb honeb
    ((F06.1 dv (by simp; omega)).trans hd) ((F06.1 one (by simp; omega)).trans h1) ((F06.1 _ (by simp)).trans hdd)
    (pgTmin d ρ) (pgLD ρ) (pgEpr d ρ) ((sc6 21 (by simp)).trans htmin) ((sc6 22 (by simp)).trans hLD) e36
    ((sc6 48 (by simp)).trans hdR)) le_rfl fun σ7 h7 => ?_
  obtain ⟨m7, F67⟩ := h7
  have v3 : σ3.vec a0 = σ.vec a0 + σ.sc (s0 + 30) • σ.vec (a0 + 10) := by
    rw [Env.vec_of_arr (F23.2.2.1 _ (by simp)), show σ2.vec a0 = σ1.vec a0 from rfl, v1]
  refine ⟨?_, ?_, ?_⟩
  · rw [Env.vec_of_arr (F67.2.2.1 _ (by simp)), show σ6.vec a0 = σ5.vec a0 from rfl, v5, v4, v3,
      F34.2.1 _ (by simp), F03.2.1 _ (by simp)]
  · rw [m7, show σ6.mat (a0 + 1) = σ5.mat (a0 + 1) from rfl, Env.mat_of_arr (F45.2.2.1 _ (by simp)),
      Env.mat_of_arr (F34.2.2.1 _ (by simp)), m3]
    have e2 : σ2.sc (s0 + 2) = 1 := by simp [hσ2]
    have e30 : σ2.sc (s0 + 30) = σ.sc (s0 + 30) := F02.2.1 _ (by simp)
    rw [e2, e30, one_smul, Env.mat_of_arr (F02.2.2.1 _ (by simp)), Env.mat_of_arr (F02.2.2.1 _ (by simp))]
    rfl
  · exact Env.Frame.trans (Env.Frame.mono F06 (by simp [pgTmpN]) (by simp [pgTmpS]) (by simp))
      (Env.Frame.mono F67 (by simp [pgTmpN]) (by simp [pgTmpS]) (by simp))

/-! ## F2: the pivot test -/

/-- The pivots of Gauss-Jordan elimination on `T` (in `a0 + 18`, with `1` in `a0 + 17`), each tested before its
step: the verdict `s0 + 39` is kept if every pivot is positive, else cleared. -/
theorem runs_gjTestLoop {dv one n0 s0 a0 : ℕ} (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS)
    (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv)
    (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1)
    (T : Matrix (Fin d) (Fin d) ℝ) (hA0 : σ.mat (a0 + 18) = T) (hB0 : σ.mat (a0 + 17) = 1)
    (hrk0 : σ.nat (n0 + 5) = 0) (ho : σ.sc (s0 + 2) = 1) (hz : σ.sc s0 = 0) :
    Runs L w (forN (n0 + 2) dv one (gjPivotT L dv one n0 (n0 + 1) (n0 + 2) (n0 + 4) (n0 + 5) (n0 + 6) (n0 + 7)
        (a0 + 18) (a0 + 17) (s0 + 12) (s0 + 13) (s0 + 2) (s0 + 14) (s0 + 8) (s0 + 9) s0 (s0 + 39) (s0 + 10))) σ
      (d * (kPivT d + 3) + 3)
      (fun σ' => σ'.sc (s0 + 39) = (if ∀ k : Fin d, 0 < (gjRun T k).1 k k then σ.sc (s0 + 39) else 0) ∧
        Env.Frame σ σ' [n0, n0 + 1, n0 + 2, n0 + 4, n0 + 5, n0 + 6, n0 + 7]
          [s0 + 8, s0 + 9, s0 + 10, s0 + 12, s0 + 13, s0 + 14, s0 + 39] [a0 + 17, a0 + 18]) := by
  have gj_succ : ∀ t (ht : t < d), (∀ k : Fin d, (k : ℕ) < t + 1 → 0 < (gjRun T k).1 k k) ↔
      ((∀ k : Fin d, (k : ℕ) < t → 0 < (gjRun T k).1 k k) ∧ 0 < (gjRun T t).1 ⟨t, ht⟩ ⟨t, ht⟩) := by
    intro t ht
    constructor
    · intro h; exact ⟨fun k hk => h k (by omega), h ⟨t, ht⟩ (by simp)⟩
    · rintro ⟨h, h'⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
      · exact h k hk
      · obtain rfl : k = ⟨t, ht⟩ := Fin.ext hk
        exact h'
  let J : ℕ → Env d → Prop := fun t σ' => (σ'.mat (a0 + 18), σ'.mat (a0 + 17)) = gjRun T t ∧
    σ'.nat (n0 + 5) = d * t ∧
    σ'.sc (s0 + 39) = (if ∀ k : Fin d, (k : ℕ) < t → 0 < (gjRun T k).1 k k then σ.sc (s0 + 39) else 0) ∧
    Env.Frame σ σ' [n0, n0 + 1, n0 + 2, n0 + 4, n0 + 5, n0 + 6, n0 + 7] [s0 + 8, s0 + 9, s0 + 10, s0 + 12, s0 + 13, s0 + 14, s0 + 39] [a0 + 17, a0 + 18]
  refine runs_mono (runs_forN (L := L) (w := w) (i := n0 + 2) (n := dv) (one := one) (by omega) hdv hone (by omega) (by omega) d (kPivT d)
    J σ hd h1 ?_ ?_) le_rfl (fun σ' h => ⟨?_, h.1.2.2.2⟩)
  · refine ⟨?_, by simp [hrk0], ?_, Env.Frame.setNat (Env.Frame.refl σ _ _ _) (by simp) 0⟩
    · show (σ.mat (a0 + 18), σ.mat (a0 + 17)) = gjRun T 0
      rw [hA0, hB0]; rfl
    · rw [if_pos (fun k hk => absurd hk (Nat.not_lt_zero _))]; rfl
  · intro t ht σ' hJ ekk ed e1
    obtain ⟨mAB, erk, ev, F'⟩ := hJ
    have eo : σ'.sc (s0 + 2) = 1 := (F'.2.1 _ (by simp)).trans ho
    have ez : σ'.sc s0 = 0 := (F'.2.1 _ (by simp)).trans hz
    unfold gjPivotT kPivT
    refine runs_seq_eq (runs_nadd (L := L) (w := w) (σ := σ') (i := n0 + 6) (a := n0 + 5) (b := n0 + 2) (by omega) (by omega) (by omega)) ?_
    set σ1 := σ'.setNat (n0 + 6) (σ'.nat (n0 + 5) + σ'.nat (n0 + 2)) with hσ1
    have e1' : σ1.nat (n0 + 6) = d * t + t := by simp [hσ1, erk, ekk]
    have hi1 : σ1.nat (n0 + 6) < asz d := by rw [e1', asz]; nlinarith
    refine runs_seq_eq (runs_aget (L := L) (w := w) (σ := σ1) (x := s0 + 10) (a := a0 + 18) (i := n0 + 6) (by omega) (by omega) (by omega)
      hi1) ?_
    set σ2 := σ1.setSc (s0 + 10) (σ1.arr (a0 + 18) (σ1.nat (n0 + 6))) with hσ2
    have s2q : σ2.sc (s0 + 10) = (gjRun T t).1 ⟨t, ht⟩ ⟨t, ht⟩ := by
      have : σ2.sc (s0 + 10) = σ'.mat (a0 + 18) ⟨t, ht⟩ ⟨t, ht⟩ := by
        simp only [hσ2, Env.setSc_sc, if_pos rfl, e1']; rfl
      rw [this, show σ'.mat (a0 + 18) = (gjRun T t).1 from congrArg Prod.fst mAB]
    have s2z : σ2.sc s0 = 0 := by rw [hσ2, Env.setSc_sc, if_neg (by omega)]; exact ez
    have hif : Runs L w (ifS L s0 (s0 + 10) .skip (sconst L (s0 + 39) 0)) σ2 3
        (fun σ3 => Env.Frame σ2 σ3 [] [s0 + 39] [] ∧
          σ3.sc (s0 + 39) = if 0 < (gjRun T t).1 ⟨t, ht⟩ ⟨t, ht⟩ then σ2.sc (s0 + 39) else 0) := by
      by_cases hp : σ2.sc s0 < σ2.sc (s0 + 10)
      · refine runs_mono (runs_ifS_t (by omega) (by omega) hp (runs_skip σ2)) (by norm_num) ?_
        rintro σ3 rfl
        rw [s2z, s2q] at hp
        exact ⟨Env.Frame.refl _ _ _ _, by rw [if_pos hp]⟩
      · refine runs_mono (runs_ifS_f (by omega) (by omega) hp (runs_sconst (L := L) (w := w) (σ := σ2) (x := s0 + 39) (by omega) 0))
          (by norm_num) ?_
        rintro σ3 rfl
        rw [s2z, s2q] at hp
        exact ⟨Env.Frame.setSc (Env.Frame.refl _ _ _ _) (by simp) _, by rw [if_neg hp]; simp⟩
    refine runs_seq hif fun σ3 h3 => ?_
    obtain ⟨F23, e3v⟩ := h3
    have n3 : ∀ x, x ≠ n0 + 6 → σ3.nat x = σ'.nat x := fun x hx => by
      rw [F23.1 x (by simp)]; simp [hσ2, hσ1, hx]
    have o3 : σ3.sc (s0 + 2) = 1 := by
      rw [F23.2.1 (s0 + 2) (by simp), hσ2, Env.setSc_sc, if_neg (by omega)]; exact eo
    refine runs_mono (runs_gjPivot σ3 ⟨t, ht⟩ hdv hone (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by simp) (by simp; omega) (by omega) (by simp)
      ((n3 dv (by omega)).trans ed) ((n3 one (by omega)).trans e1) ((n3 _ (by omega)).trans erk)
      ((n3 _ (by omega)).trans ekk) o3) le_rfl fun σ4 h4 => ?_
    obtain ⟨mAB4, erk4, F34⟩ := h4
    have F'2 : Env.Frame σ' σ2 [n0 + 6] [s0 + 10] [] :=
      Env.Frame.setSc (Env.Frame.setNat (Env.Frame.refl σ' _ _ _) (by simp) _) (by simp) _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [F34.1 (n0 + 2) (by simp), n3 (n0 + 2) (by omega)]; exact ekk
    · rw [F34.1 dv (by simp; omega), n3 dv (by omega)]; exact ed
    · rw [F34.1 one (by simp; omega), n3 one (by omega)]; exact e1
    · show (σ4.mat (a0 + 18), σ4.mat (a0 + 17)) = gjRun T (t + 1)
      have e3m : (σ3.mat (a0 + 18), σ3.mat (a0 + 17)) = (σ'.mat (a0 + 18), σ'.mat (a0 + 17)) := by
        rw [Env.mat_of_arr (σ' := σ3) ((F23.2.2.1 _ (by simp)).trans (F'2.2.2.1 _ (by simp))),
          Env.mat_of_arr (σ' := σ3) ((F23.2.2.1 _ (by simp)).trans (F'2.2.2.1 _ (by simp)))]
      rw [mAB4, gjRun, dif_pos ht, e3m, mAB]
    · simp [erk4]; ring
    · show σ4.sc (s0 + 39) = _
      have e2v : σ2.sc (s0 + 39) = σ'.sc (s0 + 39) := by rw [hσ2, Env.setSc_sc, if_neg (by omega)]; rfl
      rw [F34.2.1 (s0 + 39) (by simp), e3v, e2v, ev]
      by_cases hP : 0 < (gjRun T t).1 ⟨t, ht⟩ ⟨t, ht⟩
      · rw [if_pos hP]
        by_cases hA : ∀ k : Fin d, (k : ℕ) < t → 0 < (gjRun T k).1 k k
        · rw [if_pos hA, if_pos ((gj_succ t ht).2 ⟨hA, hP⟩)]
        · rw [if_neg hA, if_neg (fun h => hA ((gj_succ t ht).1 h).1)]
      · rw [if_neg hP, if_neg (fun h => hP ((gj_succ t ht).1 h).2)]
    · exact Env.Frame.setNat (Env.Frame.trans F' (Env.Frame.trans (Env.Frame.mono F'2 (by simp) (by simp) (by simp))
        (Env.Frame.trans (Env.Frame.mono F23 (by simp) (by simp) (by simp)) (Env.Frame.mono F34 (by simp) (by simp) (by simp))))) (by simp) (t + 1)
  · rw [h.1.2.2.1]
    by_cases hall : ∀ k : Fin d, 0 < (gjRun T k).1 k k
    · rw [if_pos hall, if_pos (fun k _ => hall k)]
    · rw [if_neg hall, if_neg (fun h' => hall fun k => h' k k.2)]

/-- The third clause of a basic verdict by the pivots of `Q̂ - (5/8)(κ/d) I` (`-κ/d` in `s0 + 32`). -/
theorem runs_pgVerdC3P {dv one n0 s0 a0 : ℕ} (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS)
    (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv)
    (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) (hdd : σ.nat (n0 + 9) = d * d) :
    Runs L w (pgVerdC3P L dv one n0 s0 a0) σ (kVerdC3P d)
      (fun σ' => σ'.sc (s0 + 39) = (if ∀ k : Fin d, 0 < (gjRun (σ.mat (a0 + 16) -
            ((-5 / 8 : ℝ) * σ.sc (s0 + 32)) • (1 : Matrix (Fin d) (Fin d) ℝ)) k).1 k k then σ.sc (s0 + 39) else 0) ∧
        Env.Frame σ σ' [n0, n0 + 1, n0 + 2, n0 + 4, n0 + 5, n0 + 6, n0 + 7]
          [s0, s0 + 2, s0 + 8, s0 + 9, s0 + 10, s0 + 12, s0 + 13, s0 + 14, s0 + 36, s0 + 39, s0 + 47, s0 + 51]
          [a0 + 17, a0 + 18]) := by
  unfold pgVerdC3P kVerdC3P kMfill kMdiag kMlin
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := σ) (x := s0) (by omega) 0) ?_
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := σ.setSc s0 ((0 : ℚ) : ℝ)) (x := s0 + 2) (by omega) 1) ?_
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := (σ.setSc s0 ((0 : ℚ) : ℝ)).setSc (s0 + 2) ((1 : ℚ) : ℝ))
    (x := s0 + 47) (by omega) (-5 / 8)) ?_
  set σ3 := ((σ.setSc s0 ((0 : ℚ) : ℝ)).setSc (s0 + 2) ((1 : ℚ) : ℝ)).setSc (s0 + 47) ((-5 / 8 : ℚ) : ℝ) with hσ3
  refine runs_seq_eq (runs_sop2 (L := L) (w := w) (σ := σ3) (x := s0 + 51) (a := s0 + 47) (b := s0 + 32) (by omega) (by omega) (by omega)
    .mul) ?_
  set σ4 := σ3.setSc (s0 + 51) (Op2.mul.eval (σ3.sc (s0 + 47)) (σ3.sc (s0 + 32))) with hσ4
  have F04 : Env.Frame σ σ4 [n0, n0 + 1, n0 + 2, n0 + 4, n0 + 5, n0 + 6, n0 + 7] [s0, s0 + 2, s0 + 8, s0 + 9, s0 + 36, s0 + 47, s0 + 51] [a0 + 17, a0 + 18] :=
    Env.Frame.setSc (Env.Frame.setSc (Env.Frame.setSc (Env.Frame.setSc (Env.Frame.refl σ _ _ _) (by simp) _)
      (by simp) _) (by simp) _) (by simp) _
  have e40 : σ4.sc s0 = 0 := by simp [hσ4, hσ3]
  have e42 : σ4.sc (s0 + 2) = 1 := by simp [hσ4, hσ3]
  have e451 : σ4.sc (s0 + 51) = (-5 / 8 : ℝ) * σ.sc (s0 + 32) := by simp [hσ4, hσ3, Op2.eval] <;> norm_num
  refine runs_seq (runs_mfill (dd := n0 + 9) (m := n0) (A := a0 + 17) (z := s0) σ4 (by omega) hone (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F04.1 _ (by simp)).trans hdd) ((F04.1 one (by simp; omega)).trans h1)) fun σ5 h5' => ?_
  obtain ⟨m5, F5, -⟩ := h5'
  have F05 : Env.Frame σ σ5 [n0, n0 + 1, n0 + 2, n0 + 4, n0 + 5, n0 + 6, n0 + 7] [s0, s0 + 2, s0 + 8, s0 + 9, s0 + 36, s0 + 47, s0 + 51] [a0 + 17, a0 + 18] := Env.Frame.trans F04 (Env.Frame.mono F5 (by simp) (by simp) (by simp))
  refine runs_seq (runs_mdiag (i := n0) (k := n0 + 2) (A := a0 + 17) (z := s0 + 51) σ5 hdv hone (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) ((F05.1 dv (by simp; omega)).trans hd) ((F05.1 one (by simp; omega)).trans h1)) fun σ6 h6' => ?_
  obtain ⟨m6, F6, -⟩ := h6'
  have F06 : Env.Frame σ σ6 [n0, n0 + 1, n0 + 2, n0 + 4, n0 + 5, n0 + 6, n0 + 7] [s0, s0 + 2, s0 + 8, s0 + 9, s0 + 36, s0 + 47, s0 + 51] [a0 + 17, a0 + 18] := Env.Frame.trans F05 (Env.Frame.mono F6 (by simp) (by simp) (by simp))
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := σ6) (x := s0 + 36) (by omega) (-1)) ?_
  set σ7 := σ6.setSc (s0 + 36) ((-1 : ℚ) : ℝ) with hσ7
  have F07 : Env.Frame σ σ7 [n0, n0 + 1, n0 + 2, n0 + 4, n0 + 5, n0 + 6, n0 + 7] [s0, s0 + 2, s0 + 8, s0 + 9, s0 + 36, s0 + 47, s0 + 51] [a0 + 17, a0 + 18] := Env.Frame.setSc F06 (by simp) _
  have e72 : σ7.sc (s0 + 2) = 1 := by
    rw [hσ7, Env.setSc_sc, if_neg (by omega), F6.2.1 _ (by simp), F5.2.1 _ (by simp)]; exact e42
  have e736 : σ7.sc (s0 + 36) = -1 := by simp [hσ7]
  have eM7 : σ7.mat (a0 + 17) = ((-5 / 8 : ℝ) * σ.sc (s0 + 32)) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [show σ7.mat (a0 + 17) = σ6.mat (a0 + 17) from rfl, m6, m5, e40, F5.2.1 (s0 + 51) (by simp), e451, of_diag_zero]
  have eA7 : σ7.mat (a0 + 16) = σ.mat (a0 + 16) := Env.mat_of_arr (F07.2.2.1 _ (by simp))
  refine runs_seq (runs_mlin (dd := n0 + 9) (m := n0) (C := a0 + 18) (A := a0 + 16) (B := a0 + 17) (α := s0 + 2)
    (β := s0 + 36) (t1 := s0 + 8) (t2 := s0 + 9) σ7 (by omega) hone (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F07.1 _ (by simp)).trans hdd) ((F07.1 one (by simp; omega)).trans h1)) fun σ8 h8' => ?_
  obtain ⟨m8, F8, -⟩ := h8'
  have F08 : Env.Frame σ σ8 [n0, n0 + 1, n0 + 2, n0 + 4, n0 + 5, n0 + 6, n0 + 7] [s0, s0 + 2, s0 + 8, s0 + 9, s0 + 36, s0 + 47, s0 + 51] [a0 + 17, a0 + 18] := Env.Frame.trans F07 (Env.Frame.mono F8 (by simp) (by simp) (by simp))
  refine runs_seq (runs_mfill (dd := n0 + 9) (m := n0) (A := a0 + 17) (z := s0) σ8 (by omega) hone (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F08.1 _ (by simp)).trans hdd) ((F08.1 one (by simp; omega)).trans h1)) fun σ9 h9' => ?_
  obtain ⟨m9, F9, -⟩ := h9'
  have F09 : Env.Frame σ σ9 [n0, n0 + 1, n0 + 2, n0 + 4, n0 + 5, n0 + 6, n0 + 7] [s0, s0 + 2, s0 + 8, s0 + 9, s0 + 36, s0 + 47, s0 + 51] [a0 + 17, a0 + 18] := Env.Frame.trans F08 (Env.Frame.mono F9 (by simp) (by simp) (by simp))
  refine runs_seq (runs_mdiag (i := n0) (k := n0 + 2) (A := a0 + 17) (z := s0 + 2) σ9 hdv hone (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) ((F09.1 dv (by simp; omega)).trans hd) ((F09.1 one (by simp; omega)).trans h1)) fun σ10 h10' => ?_
  obtain ⟨m10, F10, -⟩ := h10'
  have F010 : Env.Frame σ σ10 [n0, n0 + 1, n0 + 2, n0 + 4, n0 + 5, n0 + 6, n0 + 7] [s0, s0 + 2, s0 + 8, s0 + 9, s0 + 36, s0 + 47, s0 + 51] [a0 + 17, a0 + 18] := Env.Frame.trans F09 (Env.Frame.mono F10 (by simp) (by simp) (by simp))
  refine runs_seq_eq (runs_nconst (L := L) (w := w) (σ := σ10) (i := n0 + 5) (by omega) 0) ?_
  set σ11 := σ10.setNat (n0 + 5) 0 with hσ11
  have F011 : Env.Frame σ σ11 [n0, n0 + 1, n0 + 2, n0 + 4, n0 + 5, n0 + 6, n0 + 7] [s0, s0 + 2, s0 + 8, s0 + 9, s0 + 36, s0 + 47, s0 + 51] [a0 + 17, a0 + 18] := Env.Frame.setNat F010 (by simp) 0
  have e82 : σ8.sc (s0 + 2) = 1 := (F8.2.1 _ (by simp)).trans e72
  have e70 : σ7.sc s0 = 0 := by
    rw [hσ7, Env.setSc_sc, if_neg (by omega), F6.2.1 _ (by simp), F5.2.1 _ (by simp)]; exact e40
  have e80 : σ8.sc s0 = 0 := (F8.2.1 _ (by simp)).trans e70
  have hA : σ11.mat (a0 + 18) = σ.mat (a0 + 16) - ((-5 / 8 : ℝ) * σ.sc (s0 + 32)) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [show σ11.mat (a0 + 18) = σ10.mat (a0 + 18) from rfl,
      Env.mat_of_arr (σ' := σ10) ((F10.2.2.1 (a0 + 18) (by simp)).trans (F9.2.2.1 (a0 + 18) (by simp))), m8, e72, e736, eM7, eA7]
    module
  have hB : σ11.mat (a0 + 17) = 1 := by
    rw [show σ11.mat (a0 + 17) = σ10.mat (a0 + 17) from rfl, m10, m9, e80, F9.2.1 (s0 + 2) (by simp), e82,
      of_diag_zero, one_smul]
  have o11 : σ11.sc (s0 + 2) = 1 := (F10.2.1 _ (by simp)).trans ((F9.2.1 _ (by simp)).trans e82)
  have z11 : σ11.sc s0 = 0 := (F10.2.1 _ (by simp)).trans ((F9.2.1 _ (by simp)).trans e80)
  refine runs_mono (runs_gjTestLoop σ11 hn0 hs0 ha0 hdv hone hdvb honeb ((F011.1 dv (by simp; omega)).trans hd)
    ((F011.1 one (by simp; omega)).trans h1) _ hA hB (by simp [hσ11]) o11 z11) le_rfl fun σ12 h12' => ?_
  obtain ⟨v12, F12⟩ := h12'
  refine ⟨by rw [v12, F011.2.1 (s0 + 39) (by simp)], Env.Frame.trans (Env.Frame.mono F011 (by simp) (by simp) (by simp))
    (Env.Frame.mono F12 (by simp) (by simp) (by simp))⟩

end AdversarialBco.Conj1Arith
