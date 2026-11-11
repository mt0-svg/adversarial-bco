/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachPGLeaves
public import AdversarialBco.Poly.MachPGGJ

@[expose] public section

/-! # The leaves of the code of PG

`pgParts : PgParts`: the rules of the membership test `pgMemQ`, the matrix `g gᵀ - 1` (`pgGGcode`), the move
`pgUpd`, Gauss-Jordan (`gjCode`, from `MachPGGJ.lean`) and the three parts of a basic verdict, proved through the rules
of `Runs` only; hence `pgLeaves : PgLeaves`, the hypothesis of `runs_pgCode` (`MachPG.lean`). -/

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL
  Matrix

namespace AdversarialBco.Poly.PG

/-- `if x < y then z := 0`. -/
theorem runs_clr {d : ℕ} {L : Layout} {w : World d} {x y z : ℕ} (σ : Env d) (hx : x < L.NS) (hy : y < L.NS)
    (hz : z < L.NS) :
    Runs L w (ifS L x y (sconst L z 0) .skip) σ 2
      (fun σ' => σ'.sc z = (if σ.sc x < σ.sc y then 0 else σ.sc z) ∧ Env.Frame σ σ' [] [z] []) := by
  by_cases h : σ.sc x < σ.sc y
  · refine runs_mono (runs_ifS_t hx hy h (runs_sconst hz 0)) le_rfl (fun σ' e => ?_)
    subst e
    exact ⟨by simp [h], Env.Frame.setSc (Env.Frame.refl σ _ _ _) (by simp) _⟩
  · refine runs_mono (runs_ifS_f hx hy h (runs_skip σ)) le_rfl (fun σ' e => ?_)
    subst σ'
    exact ⟨by simp [h], Env.Frame.refl σ _ _ _⟩

theorem runs_pgVerdC12 {d : ℕ} {L : Layout} {w : World d} {dv one n0 s0 a0 : ℕ}
    (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN)
    (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d)
    (h1 : σ.nat one = 1) :
    Runs L w (pgVerdC12 L dv one n0 s0 a0) σ (kVerdC12 d)
      (fun σ' => σ'.sc (s0 + 39) = (if σ.sc (s0 + 37) ≤ 43 / 320 ∧
          Real.sqrt (σ.vec (a0 + 15) ⬝ᵥ σ.vec (a0 + 15)) ≤ 3 / 4 * σ.sc (s0 + 28) then 1 else 0) ∧
        Env.Frame σ σ' [n0] [s0 + 8, s0 + 9, s0 + 38, s0 + 39, s0 + 47] []) := by
  unfold pgVerdC12 kVerdC12
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := σ) (x := s0 + 39) (by omega) 1) ?_
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := σ.setSc (s0 + 39) ((1 : ℚ) : ℝ)) (x := s0 + 47)
    (by omega) (43 / 320)) ?_
  set σ2 := (σ.setSc (s0 + 39) ((1 : ℚ) : ℝ)).setSc (s0 + 47) ((43 / 320 : ℚ) : ℝ) with hσ2
  have F02 : Env.Frame σ σ2 [] [s0 + 39, s0 + 47] [] :=
    Env.Frame.setSc (Env.Frame.setSc (Env.Frame.refl σ _ _ _) (by simp) _) (by simp) _
  refine runs_seq (runs_clr (L := L) (w := w) σ2 (x := s0 + 47) (y := s0 + 37) (z := s0 + 39) (by omega) (by omega)
    (by omega)) fun σ3 h3 => ?_
  obtain ⟨c3, F23⟩ := h3
  have F03 : Env.Frame σ σ3 [] [s0 + 39, s0 + 47] [] :=
    Env.Frame.trans F02 (Env.Frame.mono F23 (by simp) (by simp) (by simp))
  refine runs_seq (runs_vnorm (i := n0) (r := s0 + 38) (x := a0 + 15) (t1 := s0 + 8) (t2 := s0 + 9) σ3 hdv hone
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F03.1 dv (by simp)).trans hd) ((F03.1 one (by simp)).trans h1)) fun σ4 h4 => ?_
  obtain ⟨c4, F34⟩ := h4
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := σ4) (x := s0 + 47) (by omega) (3 / 4)) ?_
  refine runs_seq_eq (runs_sop2 (L := L) (w := w) (σ := σ4.setSc (s0 + 47) ((3 / 4 : ℚ) : ℝ)) (x := s0 + 47)
    (a := s0 + 47) (b := s0 + 28) (by omega) (by omega) (by omega) .mul) ?_
  set σ6 := (σ4.setSc (s0 + 47) ((3 / 4 : ℚ) : ℝ)).setSc (s0 + 47)
    (Op2.eval .mul ((σ4.setSc (s0 + 47) ((3 / 4 : ℚ) : ℝ)).sc (s0 + 47))
      ((σ4.setSc (s0 + 47) ((3 / 4 : ℚ) : ℝ)).sc (s0 + 28))) with hσ6
  have F46 : Env.Frame σ4 σ6 [] [s0 + 47] [] :=
    Env.Frame.setSc (Env.Frame.setSc (Env.Frame.refl σ4 _ _ _) (by simp) _) (by simp) _
  refine runs_mono (runs_clr (L := L) (w := w) σ6 (x := s0 + 47) (y := s0 + 38) (z := s0 + 39) (by omega) (by omega)
    (by omega)) le_rfl fun σ7 h7 => ?_
  obtain ⟨c7, F67⟩ := h7
  have s4 : ∀ x ∉ [s0 + 38, s0 + 8, s0 + 9], σ4.sc x = σ3.sc x := F34.2.1
  have e28 : σ4.sc (s0 + 28) = σ.sc (s0 + 28) :=
    (s4 _ (by simp)).trans (F03.2.1 _ (by simp))
  have e47 : σ6.sc (s0 + 47) = 3 / 4 * σ.sc (s0 + 28) := by
    rw [hσ6]; simp [Op2.eval, e28]
  have e38 : σ6.sc (s0 + 38) = Real.sqrt (σ.vec (a0 + 15) ⬝ᵥ σ.vec (a0 + 15)) := by
    rw [F46.2.1 _ (by simp), c4, Env.vec_of_arr (F03.2.2.1 _ (by simp))]
  have e39 : σ6.sc (s0 + 39) = if (43 / 320 : ℝ) < σ.sc (s0 + 37) then 0 else 1 := by
    rw [F46.2.1 _ (by simp), s4 _ (by simp), c3]
    simp [hσ2]
  refine ⟨?_, ?_⟩
  · rw [c7, e47, e38, e39]
    by_cases hP : σ.sc (s0 + 37) ≤ 43 / 320 <;>
      by_cases hQ : Real.sqrt (σ.vec (a0 + 15) ⬝ᵥ σ.vec (a0 + 15)) ≤ 3 / 4 * σ.sc (s0 + 28)
    · simp [hP, hQ, not_lt.mpr hP, not_lt.mpr hQ]
    · simp [hP, hQ, not_le.mp hQ]
    · simp [hP, hQ, not_le.mp hP, not_lt.mpr hQ]
    · simp [hP, hQ, not_le.mp hQ]
  · exact Env.Frame.trans (Env.Frame.mono F03 (by simp) (by simp) (by simp))
      (Env.Frame.trans (Env.Frame.mono F34 (by simp) (by simp) (by simp))
        (Env.Frame.trans (Env.Frame.mono F46 (by simp) (by simp) (by simp))
          (Env.Frame.mono F67 (by simp) (by simp) (by simp))))

theorem runs_pgVerdNorm {d : ℕ} {L : Layout} {w : World d} {dv one n0 s0 a0 : ℕ}
    (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN)
    (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d)
    (h1 : σ.nat one = 1) (hdd : σ.nat (n0 + 9) = d * d) :
    Runs L w (pgVerdNorm L dv one n0 s0 a0) σ (kVerdNorm d)
      (fun σ' => σ'.sc (s0 + 37) = ((σ.nat (n0 + 12) : ℝ))⁻¹ * σ.sc (s0 + 37) ∧
        σ'.vec (a0 + 15) = ((σ.nat (n0 + 12) : ℝ))⁻¹ • σ.vec (a0 + 15) ∧
        σ'.mat (a0 + 16) = ((σ.nat (n0 + 12) : ℝ))⁻¹ • σ.mat (a0 + 16) ∧
        Env.Frame σ σ' [n0] [s0, s0 + 2, s0 + 8, s0 + 9, s0 + 37, s0 + 45, s0 + 46] [a0 + 15, a0 + 16]) := by
  unfold pgVerdNorm kVerdNorm
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := σ) (x := s0) (by omega) 0) ?_
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := σ.setSc s0 ((0 : ℚ) : ℝ)) (x := s0 + 2) (by omega) 1) ?_
  set σ2 := (σ.setSc s0 ((0 : ℚ) : ℝ)).setSc (s0 + 2) ((1 : ℚ) : ℝ) with hσ2
  refine runs_seq_eq (runs_ncast (L := L) (w := w) (σ := σ2) (x := s0 + 45) (i := n0 + 12) (by omega) (by omega)) ?_
  set σ3 := σ2.setSc (s0 + 45) (σ2.nat (n0 + 12)) with hσ3
  refine runs_seq_eq (runs_sop2 (L := L) (w := w) (σ := σ3) (x := s0 + 46) (a := s0 + 2) (b := s0 + 45) (by omega)
    (by omega) (by omega) .div) ?_
  set σ4 := σ3.setSc (s0 + 46) (Op2.eval .div (σ3.sc (s0 + 2)) (σ3.sc (s0 + 45))) with hσ4
  refine runs_seq_eq (runs_sop2 (L := L) (w := w) (σ := σ4) (x := s0 + 37) (a := s0 + 46) (b := s0 + 37) (by omega)
    (by omega) (by omega) .mul) ?_
  set σ5 := σ4.setSc (s0 + 37) (Op2.eval .mul (σ4.sc (s0 + 46)) (σ4.sc (s0 + 37))) with hσ5
  have e46 : σ5.sc (s0 + 46) = ((σ.nat (n0 + 12) : ℝ))⁻¹ := by
    simp [hσ5, hσ4, hσ3, hσ2, Op2.eval]
  have e0 : σ5.sc s0 = 0 := by simp [hσ5, hσ4, hσ3, hσ2]
  have F05 : Env.Frame σ σ5 [] [s0, s0 + 2, s0 + 37, s0 + 45, s0 + 46] [] :=
    Env.Frame.setSc (Env.Frame.setSc (Env.Frame.setSc (Env.Frame.setSc (Env.Frame.setSc (Env.Frame.refl σ _ _ _)
      (by simp) _) (by simp) _) (by simp) _) (by simp) _) (by simp) _
  have e37 : σ5.sc (s0 + 37) = ((σ.nat (n0 + 12) : ℝ))⁻¹ * σ.sc (s0 + 37) := by
    simp [hσ5, hσ4, hσ3, hσ2, Op2.eval]
  refine runs_seq (runs_vscale (i := n0) (y := a0 + 15) (α := s0 + 46) (t := s0 + 8) σ5 hdv hone (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ((F05.1 dv (by simp)).trans hd)
    ((F05.1 one (by simp)).trans h1)) fun σ6 h6 => ?_
  obtain ⟨v6, F56, -⟩ := h6
  refine runs_mono (runs_mlin (m := n0) (C := a0 + 16) (A := a0 + 16) (B := a0 + 16) (α := s0 + 46) (β := s0)
    (t1 := s0 + 8) (t2 := s0 + 9) σ6 (by omega) hone (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F56.1 _ (by simp)).trans ((F05.1 _ (by simp)).trans hdd))
    ((F56.1 _ (by simp; omega)).trans ((F05.1 one (by simp)).trans h1))) le_rfl fun σ7 h7 => ?_
  obtain ⟨m7, F67, -⟩ := h7
  have s6 : ∀ x ∉ [s0 + 8], σ6.sc x = σ5.sc x := F56.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [F67.2.1 _ (by simp), s6 _ (by simp), e37]
  · rw [Env.vec_of_arr (F67.2.2.1 _ (by simp)), v6, e46, Env.vec_of_arr (F05.2.2.1 _ (by simp))]
  · rw [m7, s6 _ (by simp), s6 _ (by simp), e46, e0, zero_smul, add_zero,
      Env.mat_of_arr (F56.2.2.1 _ (by simp)), Env.mat_of_arr (F05.2.2.1 _ (by simp))]
  · exact Env.Frame.trans (Env.Frame.mono F05 (by simp) (by simp) (by simp))
      (Env.Frame.trans (Env.Frame.mono F56 (by simp) (by simp) (by simp))
        (Env.Frame.mono F67 (by simp) (by simp) (by simp)))

theorem Env.Frame.setMat_self {d : ℕ} (σ : Env d) (a : ℕ) (M : Matrix (Fin d) (Fin d) ℝ) (ns ss : List ℕ) :
    Env.Frame σ (σ.setMat a M) ns ss [a] :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun b hb => by
    have hba : b ≠ a := by simpa using hb
    funext k; simp [hba], rfl, rfl, rfl⟩

theorem runs_pgVerdC3 {d : ℕ} {L : Layout} {w : World d} {dv one n0 s0 a0 : ℕ}
    (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN)
    (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d)
    (h1 : σ.nat one = 1) (hdd : σ.nat (n0 + 9) = d * d) :
    Runs L w (pgVerdC3 L dv one n0 s0 a0) σ (kVerdC3 d)
      (fun σ' => σ'.sc (s0 + 39) = (if 0 < (cfc (Spec.fn .step 0 0)
            (symPart (((-5 / 8 : ℝ) * σ.sc (s0 + 32)) • (1 : Matrix (Fin d) (Fin d) ℝ) - σ.mat (a0 + 16)))).trace
          then 0 else σ.sc (s0 + 39)) ∧
        Env.Frame σ σ' [n0, n0 + 2] [s0, s0 + 2, s0 + 8, s0 + 9, s0 + 36, s0 + 39, s0 + 44, s0 + 47, s0 + 51]
          [a0 + 17, a0 + 18]) := by
  unfold pgVerdC3 kVerdC3
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := σ) (x := s0) (by omega) 0) ?_
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := σ.setSc s0 ((0 : ℚ) : ℝ)) (x := s0 + 2) (by omega) 1) ?_
  refine runs_seq_eq (runs_sconst (L := L) (w := w)
    (σ := (σ.setSc s0 ((0 : ℚ) : ℝ)).setSc (s0 + 2) ((1 : ℚ) : ℝ)) (x := s0 + 47) (by omega) (-5 / 8)) ?_
  set σ3 := ((σ.setSc s0 ((0 : ℚ) : ℝ)).setSc (s0 + 2) ((1 : ℚ) : ℝ)).setSc (s0 + 47) ((-5 / 8 : ℚ) : ℝ) with hσ3
  refine runs_seq_eq (runs_sop2 (L := L) (w := w) (σ := σ3) (x := s0 + 51) (a := s0 + 47) (b := s0 + 32) (by omega)
    (by omega) (by omega) .mul) ?_
  set σ4 := σ3.setSc (s0 + 51) (Op2.eval .mul (σ3.sc (s0 + 47)) (σ3.sc (s0 + 32))) with hσ4
  have F04 : Env.Frame σ σ4 [] [s0, s0 + 2, s0 + 47, s0 + 51] [] :=
    Env.Frame.setSc (Env.Frame.setSc (Env.Frame.setSc (Env.Frame.setSc (Env.Frame.refl σ _ _ _)
      (by simp) _) (by simp) _) (by simp) _) (by simp) _
  have e51 : σ4.sc (s0 + 51) = -5 / 8 * σ.sc (s0 + 32) := by
    simp [hσ4, hσ3, Op2.eval]
  have e0 : σ4.sc s0 = 0 := by simp [hσ4, hσ3]
  have e2 : σ4.sc (s0 + 2) = 1 := by simp [hσ4, hσ3]
  refine runs_seq (runs_mfill (m := n0) (A := a0 + 17) (z := s0) σ4 (by omega) hone (by omega) (by omega) (by omega)
    (by omega) (by omega) ((F04.1 _ (by simp)).trans hdd) ((F04.1 one (by simp)).trans h1)) fun σ5 h5 => ?_
  obtain ⟨m5, F45, -⟩ := h5
  refine runs_seq (runs_mdiag (i := n0) (k := n0 + 2) (A := a0 + 17) (z := s0 + 51) σ5 hdv hone (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F45.1 dv (by simp; omega)).trans ((F04.1 dv (by simp)).trans hd))
    ((F45.1 one (by simp; omega)).trans ((F04.1 one (by simp)).trans h1))) fun σ6 h6 => ?_
  obtain ⟨m6, F56, -⟩ := h6
  have F06 : Env.Frame σ σ6 [n0, n0 + 2] [s0, s0 + 2, s0 + 47, s0 + 51] [a0 + 17] :=
    Env.Frame.trans (Env.Frame.mono F04 (by simp) (by simp) (by simp))
      (Env.Frame.trans (Env.Frame.mono F45 (by simp) (by simp) (by simp))
        (Env.Frame.mono F56 (by simp) (by simp) (by simp)))
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := σ6) (x := s0 + 36) (by omega) (-1)) ?_
  set σ7 := σ6.setSc (s0 + 36) ((-1 : ℚ) : ℝ) with hσ7
  have F07 : Env.Frame σ σ7 [n0, n0 + 2] [s0, s0 + 2, s0 + 36, s0 + 47, s0 + 51] [a0 + 17] :=
    Env.Frame.setSc (Env.Frame.mono F06 (by simp) (by simp) (by simp)) (by simp) _
  refine runs_seq (runs_mlin (m := n0) (C := a0 + 17) (A := a0 + 17) (B := a0 + 16) (α := s0 + 2) (β := s0 + 36)
    (t1 := s0 + 8) (t2 := s0 + 9) σ7 (by omega) hone (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F07.1 _ (by simp)).trans hdd) ((F07.1 one (by simp; omega)).trans h1)) fun σ8 h8 => ?_
  obtain ⟨m8, F78, -⟩ := h8
  have M8 : σ8.mat (a0 + 17) = ((-5 / 8 : ℝ) * σ.sc (s0 + 32)) • (1 : Matrix (Fin d) (Fin d) ℝ) - σ.mat (a0 + 16) := by
    have s72 : σ7.sc (s0 + 2) = 1 := by
      rw [hσ7, Env.setSc_sc, if_neg (by omega), F56.2.1 _ (by simp), F45.2.1 _ (by simp), e2]
    have s736 : σ7.sc (s0 + 36) = -1 := by simp [hσ7]
    have s551 : σ5.sc (s0 + 51) = σ4.sc (s0 + 51) := F45.2.1 _ (by simp)
    have m716 : σ7.mat (a0 + 16) = σ.mat (a0 + 16) := Env.mat_of_arr (F07.2.2.1 _ (by simp))
    have m717 : σ7.mat (a0 + 17) = σ6.mat (a0 + 17) := rfl
    rw [m8, s72, s736, m716, m717, m6, m5, s551, e51, e0]
    ext a b
    by_cases hab : a = b
    · subst hab; simp; ring
    · simp [hab, Matrix.one_apply]
  refine runs_seq_eq (runs_mspec (L := L) (w := w) (σ := σ8) (a := a0 + 18) (src := a0 + 17) (x := s0) (y := s0)
    (by omega) (by omega) (by omega) (by omega) .step) ?_
  set σ9 := σ8.setMat (a0 + 18) (cfc (Spec.fn .step (σ8.sc s0) (σ8.sc s0)) (symPart (σ8.mat (a0 + 17)))) with hσ9
  have s80 : σ8.sc s0 = 0 := by
    rw [F78.2.1 _ (by simp), hσ7, Env.setSc_sc, if_neg (by omega), F56.2.1 _ (by simp), F45.2.1 _ (by simp), e0]
  refine runs_seq (runs_mtrace (i := n0) (k := n0 + 2) (r := s0 + 44) (A := a0 + 18) (t := s0 + 8) σ9 hdv hone
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F78.1 dv (by simp; omega)).trans ((F07.1 dv (by simp; omega)).trans hd))
    ((F78.1 one (by simp; omega)).trans ((F07.1 one (by simp; omega)).trans h1))) fun σ10 h10 => ?_
  obtain ⟨c10, F910⟩ := h10
  refine runs_mono (runs_clr (L := L) (w := w) σ10 (x := s0) (y := s0 + 44) (z := s0 + 39) (by omega) (by omega)
    (by omega)) le_rfl fun σ11 h11 => ?_
  obtain ⟨c11, F1011⟩ := h11
  have s10_0 : σ10.sc s0 = 0 := by rw [F910.2.1 _ (by simp)]; exact s80
  have s10_44 : σ10.sc (s0 + 44) = (cfc (Spec.fn .step 0 0)
      (symPart (((-5 / 8 : ℝ) * σ.sc (s0 + 32)) • (1 : Matrix (Fin d) (Fin d) ℝ) - σ.mat (a0 + 16)))).trace := by
    rw [c10, hσ9, Env.mat_setMat, s80, M8]
  have s10_39 : σ10.sc (s0 + 39) = σ.sc (s0 + 39) := by
    rw [F910.2.1 _ (by simp), show σ9.sc = σ8.sc from rfl, F78.2.1 _ (by simp), F07.2.1 _ (by simp)]
  refine ⟨?_, ?_⟩
  · rw [c11, s10_0, s10_44, s10_39]
  · exact Env.Frame.trans (Env.Frame.mono F07 (by simp) (by simp) (by simp))
      (Env.Frame.trans (Env.Frame.mono F78 (by simp) (by simp) (by simp))
        (Env.Frame.trans (Env.Frame.mono (Env.Frame.setMat_self σ8 (a0 + 18) _ [] []) (by simp) (by simp) (by simp))
          (Env.Frame.trans (Env.Frame.mono F910 (by simp) (by simp) (by simp))
            (Env.Frame.mono F1011 (by simp) (by simp) (by simp)))))

theorem runs_pgGGcode {d : ℕ} {L : Layout} {w : World d} {dv one n0 s0 a0 : ℕ}
    (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN)
    (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d)
    (h1 : σ.nat one = 1) (hdd : σ.nat (n0 + 9) = d * d) :
    Runs L w (pgGGcode L dv one n0 s0 a0) σ (kGG d)
      (fun σ' => σ'.mat (a0 + 11) = vecMulVec (σ.vec (a0 + 4)) (σ.vec (a0 + 4)) - 1 ∧ σ'.sc s0 = 0 ∧
        σ'.sc (s0 + 2) = 1 ∧
        Env.Frame σ σ' [n0, n0 + 1, n0 + 2] [s0, s0 + 2, s0 + 8, s0 + 9, s0 + 10, s0 + 36] [a0 + 11]) := by
  unfold pgGGcode kGG
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := σ) (x := s0) (by omega) 0) ?_
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := σ.setSc s0 ((0 : ℚ) : ℝ)) (x := s0 + 2) (by omega) 1) ?_
  refine runs_seq_eq (runs_sconst (L := L) (w := w)
    (σ := (σ.setSc s0 ((0 : ℚ) : ℝ)).setSc (s0 + 2) ((1 : ℚ) : ℝ)) (x := s0 + 36) (by omega) (-1)) ?_
  set σ3 := ((σ.setSc s0 ((0 : ℚ) : ℝ)).setSc (s0 + 2) ((1 : ℚ) : ℝ)).setSc (s0 + 36) ((-1 : ℚ) : ℝ) with hσ3
  have F03 : Env.Frame σ σ3 [] [s0, s0 + 2, s0 + 36] [] :=
    Env.Frame.setSc (Env.Frame.setSc (Env.Frame.setSc (Env.Frame.refl σ _ _ _) (by simp) _) (by simp) _)
      (by simp) _
  have e0 : σ3.sc s0 = 0 := by simp [hσ3]
  have e2 : σ3.sc (s0 + 2) = 1 := by simp [hσ3]
  have e36 : σ3.sc (s0 + 36) = -1 := by simp [hσ3]
  refine runs_seq (runs_mfill (m := n0) (A := a0 + 11) (z := s0) σ3 (by omega) hone (by omega) (by omega) (by omega)
    (by omega) (by omega) ((F03.1 _ (by simp)).trans hdd) ((F03.1 one (by simp)).trans h1)) fun σ4 h4 => ?_
  obtain ⟨m4, F34, -⟩ := h4
  refine runs_seq (runs_mdiag (i := n0) (k := n0 + 2) (A := a0 + 11) (z := s0 + 36) σ4 hdv hone (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F34.1 dv (by simp; omega)).trans ((F03.1 dv (by simp)).trans hd))
    ((F34.1 one (by simp; omega)).trans ((F03.1 one (by simp)).trans h1))) fun σ5 h5 => ?_
  obtain ⟨m5, F45, -⟩ := h5
  have F05 : Env.Frame σ σ5 [n0, n0 + 2] [s0, s0 + 2, s0 + 36] [a0 + 11] :=
    Env.Frame.trans (Env.Frame.mono F03 (by simp) (by simp) (by simp))
      (Env.Frame.trans (Env.Frame.mono F34 (by simp) (by simp) (by simp))
        (Env.Frame.mono F45 (by simp) (by simp) (by simp)))
  have s5 : ∀ x, σ5.sc x = σ3.sc x := fun x => (F45.2.1 x (by simp)).trans (F34.2.1 x (by simp))
  refine runs_mono (runs_rankOne (i := n0) (j := n0 + 1) (k := n0 + 2) (A := a0 + 11) (α := s0 + 2) (β := s0 + 2)
    (u := a0 + 4) (v := a0 + 4) (t1 := s0 + 8) (t2 := s0 + 9) (t3 := s0 + 10) σ5 hdv hone (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F05.1 dv (by simp; omega)).trans hd) ((F05.1 one (by simp; omega)).trans h1)) le_rfl fun σ6 h6 => ?_
  obtain ⟨m6, F56, -⟩ := h6
  have g5 : σ5.vec (a0 + 4) = σ.vec (a0 + 4) := Env.vec_of_arr (F05.2.2.1 _ (by simp))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [m6, m5, m4, s5, show σ4.sc (s0 + 36) = σ3.sc (s0 + 36) from F34.2.1 _ (by simp), e2, e36, e0, g5]
    ext a b
    by_cases hab : a = b
    · subst hab; simp [Matrix.one_apply]; ring
    · simp [hab, Matrix.one_apply]
  · rw [F56.2.1 _ (by simp), s5, e0]
  · rw [F56.2.1 _ (by simp), s5, e2]
  · exact Env.Frame.trans (Env.Frame.mono F05 (by simp) (by simp) (by simp))
      (Env.Frame.mono F56 (by simp) (by simp) (by simp))

/-- `if R < r then (q := R / r; y := q y)`, with `r = ‖y‖`: the radial clip of `y` to the ball of radius `R`. -/
theorem runs_clip {d : ℕ} {L : Layout} {w : World d} {dv one i R r q y t : ℕ} (σ : Env d) (hdv : dv < L.NN)
    (hone : one < L.NN) (hi : i < L.NN) (hy : y < L.NA) (hR : R < L.NS) (hr : r < L.NS) (hq : q < L.NS)
    (ht : t < L.NS) (hidv : i ≠ dv) (hione : i ≠ one) (hqt : q ≠ t) (hd : σ.nat dv = d) (h1 : σ.nat one = 1)
    (hrv : σ.sc r = ‖WithLp.toLp 2 (σ.vec y)‖) :
    Runs L w (ifS L R r (.seq (sop2 L .div q R r) (vscale L dv one i y q t)) .skip) σ (d * 8 + 5)
      (fun σ' => WithLp.toLp 2 (σ'.vec y) = ballClip (σ.sc R) (WithLp.toLp 2 (σ.vec y)) ∧
        Env.Frame σ σ' [i] [q, t] [y]) := by
  by_cases hc : σ.sc R < σ.sc r
  · refine runs_mono (K := (1 + (d * 8 + 3)) + 1) (runs_ifS_t hR hr hc
      (runs_seq_eq (runs_sop2 (L := L) (w := w) (σ := σ) hq hR hr .div)
        (runs_vscale (i := i) (y := y) (α := q) (t := t) (σ.setSc q (Op2.eval .div (σ.sc R) (σ.sc r))) hdv hone hi
          hy hq ht hidv hione hqt hd h1))) (by omega) fun σ' h => ?_
    obtain ⟨v', F', -⟩ := h
    refine ⟨?_, Env.Frame.trans (Env.Frame.setSc (Env.Frame.refl σ _ _ _) (by simp) _)
      (Env.Frame.mono F' (by simp) (by simp) (by simp))⟩
    rw [v', ballClip, if_pos (by rw [← hrv]; exact hc), ← hrv]
    simp [Op2.eval]
    rfl
  · refine runs_mono (runs_ifS_f hR hr hc (runs_skip σ)) (by omega) fun σ' e => ?_
    subst σ'
    refine ⟨?_, Env.Frame.refl σ _ _ _⟩
    rw [ballClip, if_neg (by rw [← hrv]; exact hc)]

theorem runs_pgUpd {d : ℕ} {L : Layout} {w : World d} {dv one n0 s0 a0 : ℕ}
    (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN)
    (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d)
    (h1 : σ.nat one = 1) (hdd : σ.nat (n0 + 9) = d * d) :
    Runs L w (pgUpd L dv one n0 s0 a0) σ (kUpd d)
      (fun σ' => WithLp.toLp 2 (σ'.vec a0) =
          ballClip (σ.sc (s0 + 23)) (WithLp.toLp 2 (σ.vec a0 + σ.sc (s0 + 30) • σ.vec (a0 + 10))) ∧
        σ'.mat (a0 + 1) = cfc (Spec.fn .clamp (σ.sc (s0 + 21)) (σ.sc (s0 + 22)))
          (symPart (σ.mat (a0 + 1) + σ.sc (s0 + 30) • σ.mat (a0 + 14))) ∧
        Env.Frame σ σ' [n0] [s0 + 2, s0 + 8, s0 + 9, s0 + 34, s0 + 35] [a0, a0 + 1]) := by
  unfold pgUpd kUpd
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
  refine runs_mono (runs_mspec (L := L) (w := w) (σ := σ5) (a := a0 + 1) (src := a0 + 1) (x := s0 + 21)
    (y := s0 + 22) (by omega) (by omega) (by omega) (by omega) .clamp) le_rfl fun σ6 e6 => ?_
  subst e6
  have F05 : Env.Frame σ σ5 [n0] [s0 + 2, s0 + 8, s0 + 9, s0 + 34, s0 + 35] [a0, a0 + 1] :=
    Env.Frame.trans (Env.Frame.mono F04 (by simp) (by simp) (by simp))
      (Env.Frame.mono F45 (by simp) (by simp) (by simp))
  have s5 : ∀ x, x ≠ s0 + 2 → x ≠ s0 + 8 → x ≠ s0 + 9 → x ≠ s0 + 34 → x ≠ s0 + 35 → σ5.sc x = σ.sc x :=
    fun x h2 h8 h9 h34 h35 => F05.2.1 x (by simp [h2, h8, h9, h34, h35])
  have v3 : σ3.vec a0 = σ.vec a0 + σ.sc (s0 + 30) • σ.vec (a0 + 10) := by
    rw [Env.vec_of_arr (F23.2.2.1 _ (by simp)), show σ2.vec a0 = σ1.vec a0 from rfl, v1]
  refine ⟨?_, ?_, ?_⟩
  · rw [Env.vec_of_arr (Env.Frame.setMat_self σ5 (a0 + 1) _ [] [] |>.2.2.1 _ (by simp)), v5, v4, v3,
      F34.2.1 _ (by simp), F03.2.1 _ (by simp)]
  · rw [Env.mat_setMat, s5 _ (by omega) (by omega) (by omega) (by omega) (by omega),
      s5 _ (by omega) (by omega) (by omega) (by omega) (by omega), Env.mat_of_arr (F45.2.2.1 _ (by simp)),
      Env.mat_of_arr (F34.2.2.1 _ (by simp)), m3]
    have e2 : σ2.sc (s0 + 2) = 1 := by simp [hσ2]
    have e30 : σ2.sc (s0 + 30) = σ.sc (s0 + 30) := F02.2.1 _ (by simp)
    rw [e2, e30, one_smul, Env.mat_of_arr (F02.2.2.1 _ (by simp)), Env.mat_of_arr (F02.2.2.1 _ (by simp))]
  · exact Env.Frame.trans F05 (Env.Frame.mono (Env.Frame.setMat_self σ5 (a0 + 1) _ [] []) (by simp) (by simp)
      (by simp))

open Classical in
theorem runs_pgMemQ {d : ℕ} {L : Layout} {w : World d} {dv one n0 s0 a0 muv Av : ℕ}
    (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN)
    (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d)
    (h1 : σ.nat one = 1) (hmuv : muv < L.NA) (hAv : Av < L.NA) (hmub : muv < a0 ∨ a0 + 32 ≤ muv)
    (hAb : Av < a0 ∨ a0 + 32 ≤ Av) :
    Runs L w (pgMemQ L dv one n0 s0 a0 muv Av) σ (kMemQ d)
      (fun σ' => σ'.sc (s0 + 15) =
          (if WithLp.toLp 2 (σ.vec (a0 + 6)) ∈ pgBodySet w.K (σ.vec muv) (σ.mat Av) (σ.sc (s0 + 42)) then 1 else 0) ∧
        Env.Frame σ σ' [n0, n0 + 1, n0 + 2] [s0 + 8, s0 + 9, s0 + 11, s0 + 15, s0 + 16, s0 + 17] [a0 + 7]) := by
  unfold pgMemQ kMemQ
  refine runs_seq (runs_memAff (i := n0) (j := n0 + 1) (k := n0 + 2) (o := s0 + 15) (mu := muv) (T := Av)
    (y := a0 + 6) (tmp := a0 + 7) (c := s0 + 16) (s := s0 + 11) (t1 := s0 + 8) (t2 := s0 + 9) σ hdv hone
    (by omega) (by omega) (by omega) (by omega) hmuv hAv (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hd h1) fun σ1 h1' => ?_
  obtain ⟨c1, t1, F01, -⟩ := h1'
  refine runs_seq (runs_vnorm (i := n0) (r := s0 + 17) (x := a0 + 7) (t1 := s0 + 8) (t2 := s0 + 9) σ1 hdv hone
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ((F01.1 dv (by simp; omega)).trans hd) ((F01.1 one (by simp; omega)).trans h1)) fun σ2 h2 => ?_
  obtain ⟨c2, F12⟩ := h2
  refine runs_mono (runs_clr (L := L) (w := w) σ2 (x := s0 + 42) (y := s0 + 17) (z := s0 + 15) (by omega) (by omega)
    (by omega)) le_rfl fun σ3 h3 => ?_
  obtain ⟨c3, F23⟩ := h3
  have e42 : σ2.sc (s0 + 42) = σ.sc (s0 + 42) := (F12.2.1 _ (by simp)).trans (F01.2.1 _ (by simp))
  have e15 : σ2.sc (s0 + 15) = σ1.sc (s0 + 15) := F12.2.1 _ (by simp)
  have e17 : σ2.sc (s0 + 17) =
      ‖WithLp.toLp 2 (σ.mat Av *ᵥ σ.vec (a0 + 6) + σ.vec muv)‖ := by
    rw [c2, t1, norm_toLp_eq]
  refine ⟨?_, ?_⟩
  · set v := WithLp.toLp 2 (σ.mat Av *ᵥ σ.vec (a0 + 6) + σ.vec muv) with hv
    have hmem : (WithLp.toLp 2 (σ.vec (a0 + 6)) ∈ pgBodySet w.K (σ.vec muv) (σ.mat Av) (σ.sc (s0 + 42))) ↔
        (v ∈ w.K ∧ ‖v‖ ≤ σ.sc (s0 + 42)) := Iff.rfl
    rw [c3, e42, e15, e17, c1]
    by_cases hP : v ∈ w.K <;> by_cases hQ : ‖v‖ ≤ σ.sc (s0 + 42)
    · rw [if_neg (not_lt.mpr hQ), if_pos hP, if_pos (hmem.2 ⟨hP, hQ⟩)]
    · rw [if_pos (not_le.mp hQ), if_neg (fun h => hQ (hmem.1 h).2)]
    · rw [if_neg (not_lt.mpr hQ), if_neg hP, if_neg (fun h => hP (hmem.1 h).1)]
    · rw [if_pos (not_le.mp hQ), if_neg (fun h => hQ (hmem.1 h).2)]
  · exact Env.Frame.trans (Env.Frame.mono F01 (by simp) (by simp) (by simp))
      (Env.Frame.trans (Env.Frame.mono F12 (by simp) (by simp) (by simp))
        (Env.Frame.mono F23 (by simp) (by simp) (by simp)))

theorem pgParts : PgParts where
  memQ := runs_pgMemQ
  ggcode := runs_pgGGcode
  upd := runs_pgUpd
  gjCode := runs_gjCode
  verdNorm := runs_pgVerdNorm
  verdC12 := runs_pgVerdC12
  verdC3 := runs_pgVerdC3

/-- The leaves of the code of PG, the hypothesis of `runs_pgCode`. -/
theorem pgLeaves : PgLeaves := pgParts.leaves

end AdversarialBco.Poly.PG
