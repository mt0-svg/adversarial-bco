/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachPGLin
public import AdversarialBco.Poly.MachMat

@[expose] public section

/-!
# Procedure PG in VL: what the rules of the loops read

The hypothesis `PgLeaves`: the rules of the straight-line parts of the PG code that the loops call (one step of the
descent, one sample, the three clauses of a verdict) and the rule of `mmul`. The descent move on `PgSp d` read off its
parts (`pgMove_mu`, `pgMove_mat`), the frames across draws and the states of a loop (`PgAt`, `PgStageVars`), and the
rules of one sample of a basic verdict (`runs_pgSample`) and of the composition (`runs_pgCompC`). The rules of the
loops of PG-N with CLAMP-NS (Conj1Arith/MachN/Loops.lean) are built on them.
-/

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL
  Matrix
open scoped RealInnerProductSpace

namespace AdversarialBco.Poly.PG

/-- The rules of the straight-line parts of the PG code that the loop rules call, and the rule of `mmul`. -/
structure PgLeaves : Prop where
  stepM : ∀ {d : ℕ} {L : Layout} {w : World d} {dv one n0 s0 a0 muv Av : ℕ}
      (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN)
      (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1)
      (hmuv : muv < L.NA) (hAv : Av < L.NA) (hmub : muv < a0 ∨ a0 + 32 ≤ muv) (hAb : Av < a0 ∨ a0 + 32 ≤ Av) (hdd : σ.nat (n0 + 9) = d * d),
      Runs L w (pgStep L dv one n0 s0 a0 muv Av) σ (kStep d (σ.nat (n0 + 10)))
        (fun σ' =>
          let g : Fin d → ℝ := fun c => w.gs (σ.draws + c)
          let F := piTilde (pgBodySet w.K (σ.vec muv) (σ.mat Av) (σ.sc (s0 + 42))) (σ.sc (s0 + 19)) (σ.nat (n0 + 10))
            (WithLp.toLp 2 (σ.mat (a0 + 1) *ᵥ g + σ.vec a0))
          let B := (gjRun (σ.mat (a0 + 1)) d).2
          let G := vecMulVec g g - 1
          WithLp.toLp 2 (σ'.vec a0) =
              ballClip (σ.sc (s0 + 23)) (WithLp.toLp 2 (σ.vec a0 + σ.sc (s0 + 30) • (F • (B *ᵥ g)))) ∧
            σ'.mat (a0 + 1) = cfc (Spec.fn .clamp (σ.sc (s0 + 21)) (σ.sc (s0 + 22)))
              (symPart (σ.mat (a0 + 1) + σ.sc (s0 + 30) • ((F / 2) • (B * G + (B * G)ᵀ) + σ.sc (s0 + 32) • B))) ∧
            σ'.vec (a0 + 2) = σ.vec (a0 + 2) + σ.vec a0 ∧ σ'.mat (a0 + 3) = σ.mat (a0 + 3) + σ.mat (a0 + 1) ∧
            σ'.draws = σ.draws + d ∧
            Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0) (pgTmpS s0 ++ [s0 + 31, s0 + 34, s0 + 35, s0 + 36])
              [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12,
                a0 + 13, a0 + 14])
  sampleM : ∀ {d : ℕ} {L : Layout} {w : World d} {dv one n0 s0 a0 muv Av : ℕ}
      (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN)
      (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1)
      (hmuv : muv < L.NA) (hAv : Av < L.NA) (hmub : muv < a0 ∨ a0 + 32 ≤ muv) (hAb : Av < a0 ∨ a0 + 32 ≤ Av) (hdd : σ.nat (n0 + 9) = d * d),
      Runs L w (pgSample L dv one n0 s0 a0 muv Av) σ (kSample d (σ.nat (n0 + 10)))
        (fun σ' =>
          let g : Fin d → ℝ := fun c => w.gs (σ.draws + c)
          let F := piTilde (pgBodySet w.K (σ.vec muv) (σ.mat Av) (σ.sc (s0 + 42))) (σ.sc (s0 + 19)) (σ.nat (n0 + 10))
            (WithLp.toLp 2 (σ.mat (a0 + 3) *ᵥ g + σ.vec (a0 + 2)))
          σ'.sc (s0 + 37) = σ.sc (s0 + 37) + F ∧ σ'.vec (a0 + 15) = σ.vec (a0 + 15) + F • g ∧
            σ'.mat (a0 + 16) = σ.mat (a0 + 16) + F • (vecMulVec g g - 1) ∧ σ'.draws = σ.draws + d ∧
            Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0) (pgTmpS s0 ++ [s0 + 36, s0 + 37])
              [a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 11, a0 + 15, a0 + 16])
  verdNorm : ∀ {d : ℕ} {L : Layout} {w : World d} {dv one n0 s0 a0 : ℕ}
      (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN)
      (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1)
      (hdd : σ.nat (n0 + 9) = d * d),
      Runs L w (pgVerdNorm L dv one n0 s0 a0) σ (kVerdNorm d)
        (fun σ' => σ'.sc (s0 + 37) = ((σ.nat (n0 + 12) : ℝ))⁻¹ * σ.sc (s0 + 37) ∧
          σ'.vec (a0 + 15) = ((σ.nat (n0 + 12) : ℝ))⁻¹ • σ.vec (a0 + 15) ∧
          σ'.mat (a0 + 16) = ((σ.nat (n0 + 12) : ℝ))⁻¹ • σ.mat (a0 + 16) ∧
          Env.Frame σ σ' [n0] [s0, s0 + 2, s0 + 8, s0 + 9, s0 + 37, s0 + 45, s0 + 46] [a0 + 15, a0 + 16])
  verdC12 : ∀ {d : ℕ} {L : Layout} {w : World d} {dv one n0 s0 a0 : ℕ}
      (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN)
      (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1),
      Runs L w (pgVerdC12 L dv one n0 s0 a0) σ (kVerdC12 d)
        (fun σ' => σ'.sc (s0 + 39) = (if σ.sc (s0 + 37) ≤ 43 / 320 ∧
            Real.sqrt (σ.vec (a0 + 15) ⬝ᵥ σ.vec (a0 + 15)) ≤ 3 / 4 * σ.sc (s0 + 28) then 1 else 0) ∧
          Env.Frame σ σ' [n0] [s0 + 8, s0 + 9, s0 + 38, s0 + 39, s0 + 47] [])
  verdC3 : ∀ {d : ℕ} {L : Layout} {w : World d} {dv one n0 s0 a0 : ℕ}
      (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN)
      (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1)
      (hdd : σ.nat (n0 + 9) = d * d),
      Runs L w (pgVerdC3 L dv one n0 s0 a0) σ (kVerdC3 d)
        (fun σ' => σ'.sc (s0 + 39) = (if 0 < (cfc (Spec.fn .step 0 0)
              (symPart (((-5 / 8 : ℝ) * σ.sc (s0 + 32)) • (1 : Matrix (Fin d) (Fin d) ℝ) - σ.mat (a0 + 16)))).trace
            then 0 else σ.sc (s0 + 39)) ∧
          Env.Frame σ σ' [n0, n0 + 2] [s0, s0 + 2, s0 + 8, s0 + 9, s0 + 36, s0 + 39, s0 + 44, s0 + 47, s0 + 51]
            [a0 + 17, a0 + 18])
  mmul : ∀ {d : ℕ} {L : Layout} {w : World d} {dv one i j l kA kB kC C A B s t1 t2 : ℕ} (σ : Env d) (hdv : dv < L.NN) (hone : one < L.NN)
      (hi : i < L.NN) (hj : j < L.NN) (hl : l < L.NN) (hkA : kA < L.NN) (hkB : kB < L.NN) (hkC : kC < L.NN)
      (hC : C < L.NA) (hA : A < L.NA) (hB : B < L.NA) (hs : s < L.NS) (ht1 : t1 < L.NS) (ht2 : t2 < L.NS)
      (hN : [i, j, l, kA, kB, kC].Nodup) (hdvN : dv ∉ [i, j, l, kA, kB, kC]) (honeN : one ∉ [i, j, l, kA, kB, kC])
      (hCA : C ≠ A) (hCB : C ≠ B) (hs1 : s ≠ t1) (hs2 : s ≠ t2) (h12 : t1 ≠ t2) (hd : σ.nat dv = d)
      (h1 : σ.nat one = 1),
      Runs L w (mmul L dv one i j l kA kB kC C A B s t1 t2) σ (d * (d * (d * 11 + 12) + 6) + 4)
        (fun σ' => σ'.mat C = σ.mat A * σ.mat B ∧ Env.Frame σ σ' [i, j, l, kA, kB, kC] [s, t1, t2] [C] ∧
          ∀ m, d * d ≤ m → σ'.arr C m = σ.arr C m)

end AdversarialBco.Poly.PG

namespace AdversarialBco.Poly.PG

variable {d : ℕ}

/-! ## The math of a step -/

/-- The body of a stage: `K ∩ B̄(0, R)` in the position `P`. -/
def pgKi (K : Set (EuclideanSpace ℝ (Fin d))) (R : ℝ) (P : PgSp d) : Set (EuclideanSpace ℝ (Fin d)) :=
  posBody (K ∩ Metric.closedBall 0 R) (pgMu P) (pgOp P)

theorem pgMu_add_pgOp (X : PgSp d) (g : EuclideanSpace ℝ (Fin d)) :
    pgMu X + pgOp X g = WithLp.toLp 2 (pgMat X *ᵥ WithLp.ofLp g + fun i => pgMu X i) := by
  rw [pgOp_apply]; ext i; simp [add_comm]

theorem pgKi_eq (K : Set (EuclideanSpace ℝ (Fin d))) (R : ℝ) (P : PgSp d) :
    pgKi K R P = pgBodySet K (fun i => pgMu P i) (pgMat P) R := by
  ext y
  simp only [pgKi, posBody, pgBodySet, Set.mem_ofPred_eq, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right,
    pgMu_add_pgOp]

theorem pgFt_eq (K' : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (X : PgSp d) (g : EuclideanSpace ℝ (Fin d)) :
    pgFt K' ρ X g = piTilde K' ρ (pgJb d ρ) (WithLp.toLp 2 (pgMat X *ᵥ WithLp.ofLp g + fun i => pgMu X i)) := by
  rw [pgFt, pgMu_add_pgOp]

theorem pgMu_smul (c : ℝ) (x : PgSp d) : pgMu (c • x) = c • pgMu x := by ext i; simp [pgMu]

theorem pgMat_smul (c : ℝ) (x : PgSp d) : pgMat (c • x) = c • pgMat x := by ext i j; simp [pgMat]

theorem pgMu_add (x y : PgSp d) : pgMu (x + y) = pgMu x + pgMu y := by ext i; simp [pgMu]

theorem pgMat_add (x y : PgSp d) : pgMat (x + y) = pgMat x + pgMat y := by ext i j; simp [pgMat]

theorem pgMu_zero : pgMu (0 : PgSp d) = 0 := by ext i; simp [pgMu]

theorem pgMat_zero : pgMat (0 : PgSp d) = 0 := by ext i j; simp [pgMat]

/-- The descent move read off its parts: `x - s V(x, g)`. -/
theorem pgMove_mu (K' : Set (EuclideanSpace ℝ (Fin d))) (ρ s : ℝ) (X : PgSp d) (g : EuclideanSpace ℝ (Fin d)) :
    pgMu (X - s • pgV K' ρ X g) = WithLp.toLp 2 ((fun i => pgMu X i) +
      (-s) • (pgFt K' ρ X g • ((pgMat X)⁻¹ *ᵥ WithLp.ofLp g))) := by
  rw [pgMu_sub, pgMu_smul, pgV, pgMu_pgPack]
  ext i; simp; ring

theorem pgMove_mat (K' : Set (EuclideanSpace ℝ (Fin d))) (ρ s : ℝ) (X : PgSp d) (g : EuclideanSpace ℝ (Fin d)) :
    pgMat (X - s • pgV K' ρ X g) = pgMat X + (-s) • ((pgFt K' ρ X g / 2) •
      ((pgMat X)⁻¹ * (vecMulVec (WithLp.ofLp g) (WithLp.ofLp g) - 1) +
        ((pgMat X)⁻¹ * (vecMulVec (WithLp.ofLp g) (WithLp.ofLp g) - 1))ᵀ) + (-(pgKappa / d)) • (pgMat X)⁻¹) := by
  rw [pgMat_sub, pgMat_smul, pgV, pgMat_pgPack]
  simp only [pgGG]
  module

theorem pgTmin_pos {ρ : ℝ} (hd : 1 ≤ d) (hρ : 1 ≤ ρ) : 0 < pgTmin d ρ := by
  have hlog : 0 < Real.log (1 + ρ) := Real.log_pos (by linarith)
  have hlam : 0 < pgLam ρ := Real.sqrt_pos.2 (by linarith)
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  unfold pgTmin
  positivity

/-- A point of `D` has a positive definite matrix. -/
theorem pgMat_posDef {ρ : ℝ} (hd : 1 ≤ d) (hρ : 1 ≤ ρ) {X : PgSp d} (hX : X ∈ pgDom d ρ) : (pgMat X).PosDef :=
  posDef_of_lower _ (pgDom_mat hX).1 _ (pgTmin_pos hd hρ) fun v => ((pgDom_mat hX).2.2 v).1

/-! ## Frames across draws, and the variables of a stage -/

theorem frameD_of_frame {σ σ' : Env d} {ns ss as : List ℕ} (h : Env.Frame σ σ' ns ss as) :
    Env.Frame σ { σ' with draws := σ.draws } ns ss as :=
  ⟨h.1, h.2.1, h.2.2.1, rfl, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem frameD_trans {σ σ₁ σ₂ : Env d} {ns ss as : List ℕ} (h₁ : Env.Frame σ { σ₁ with draws := σ.draws } ns ss as)
    (h₂ : Env.Frame σ₁ { σ₂ with draws := σ₁.draws } ns ss as) : Env.Frame σ { σ₂ with draws := σ.draws } ns ss as :=
  ⟨fun i hi => (h₂.1 i hi).trans (h₁.1 i hi), fun x hx => (h₂.2.1 x hx).trans (h₁.2.1 x hx),
    fun a ha => (h₂.2.2.1 a ha).trans (h₁.2.2.1 a ha), rfl, h₂.2.2.2.2.1.trans h₁.2.2.2.2.1,
    h₂.2.2.2.2.2.trans h₁.2.2.2.2.2⟩

theorem Env.vec_of_arr {σ σ' : Env d} {a : ℕ} (h : σ'.arr a = σ.arr a) : σ'.vec a = σ.vec a := by
  unfold Env.vec; rw [h]

theorem Env.mat_of_arr {σ σ' : Env d} {a : ℕ} (h : σ'.arr a = σ.arr a) : σ'.mat a = σ.mat a := by
  unfold Env.mat; rw [h]

/-- The point `X` held in the arrays `xm` (`μ`) and `xT` (`T`). -/
def PgAt (σ : Env d) (xm xT : ℕ) (X : PgSp d) : Prop := σ.vec xm = (fun i => pgMu X i) ∧ σ.mat xT = pgMat X

theorem PgAt.of_frame {σ σ' : Env d} {xm xT : ℕ} {X : PgSp d} (h : PgAt σ xm xT X) {ns ss as : List ℕ}
    (hF : Env.Frame σ σ' ns ss as) (hm : xm ∉ as) (hT : xT ∉ as) : PgAt σ' xm xT X :=
  ⟨(Env.vec_of_arr (hF.2.2.1 xm hm)).trans h.1, (Env.mat_of_arr (hF.2.2.1 xT hT)).trans h.2⟩

/-- The variables of a stage at the ratio `ρ`. -/
def PgStageVars (σ : Env d) (n0 s0 : ℕ) (ρ : ℝ) : Prop :=
  σ.nat (n0 + 9) = d * d ∧ σ.nat (n0 + 10) = pgJb d ρ ∧ σ.nat (n0 + 11) = pgNs d ρ ∧ σ.nat (n0 + 12) = pgNT d ρ ∧
    σ.sc (s0 + 19) = ρ ∧ σ.sc (s0 + 21) = pgTmin d ρ ∧ σ.sc (s0 + 22) = pgLD ρ ∧ σ.sc (s0 + 23) = pgKappa * ρ ∧
    σ.sc (s0 + 28) = pgTaub d ρ ∧ σ.sc (s0 + 30) = -pgStepSize d ρ ∧ σ.sc (s0 + 32) = -(pgKappa / d) ∧
    σ.sc (s0 + 48) = d

theorem PgStageVars.of_frame {σ σ' : Env d} {n0 s0 : ℕ} {ρ : ℝ} (h : PgStageVars σ n0 s0 ρ) {ns ss as : List ℕ}
    (hF : Env.Frame σ σ' ns ss as) (hn : ∀ k ∈ [9, 10, 11, 12], n0 + k ∉ ns)
    (hs : ∀ k ∈ [19, 21, 22, 23, 28, 30, 32, 48], s0 + k ∉ ss) : PgStageVars σ' n0 s0 ρ := by
  obtain ⟨h9, h10, h11, h12, h19, h21, h22, h23, h28, h30, h32, h48⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hn hs
  exact ⟨(hF.1 _ hn.1).trans h9, (hF.1 _ hn.2.1).trans h10, (hF.1 _ hn.2.2.1).trans h11,
    (hF.1 _ hn.2.2.2).trans h12, (hF.2.1 _ hs.1).trans h19, (hF.2.1 _ hs.2.1).trans h21,
    (hF.2.1 _ hs.2.2.1).trans h22, (hF.2.1 _ hs.2.2.2.1).trans h23, (hF.2.1 _ hs.2.2.2.2.1).trans h28,
    (hF.2.1 _ hs.2.2.2.2.2.1).trans h30, (hF.2.1 _ hs.2.2.2.2.2.2.1).trans h32, (hF.2.1 _ hs.2.2.2.2.2.2.2).trans h48⟩

/-! ## The verdict -/

theorem runs_pgSample {L : Layout} {w : World d} {dv one n0 s0 a0 muv Av : ℕ} {ρ : ℝ} {P X : PgSp d}
    (hL : PgLeaves) (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN)
    (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d)
    (h1 : σ.nat one = 1) (hmuv : muv < L.NA) (hAv : Av < L.NA) (hmub : muv < a0 ∨ a0 + 32 ≤ muv)
    (hAb : Av < a0 ∨ a0 + 32 ≤ Av) (hV : PgStageVars σ n0 s0 ρ) (hP : PgAt σ muv Av P)
    (hX : PgAt σ (a0 + 2) (a0 + 3) X) :
    Runs L w (pgSample L dv one n0 s0 a0 muv Av) σ (kSample d (pgJb d ρ))
      (fun σ' => σ'.sc (s0 + 37) = σ.sc (s0 + 37) + pgFt (pgKi w.K (σ.sc (s0 + 42)) P) ρ X
            (WithLp.toLp 2 fun c => w.gs (σ.draws + c)) ∧
        σ'.vec (a0 + 15) = σ.vec (a0 + 15) + pgFt (pgKi w.K (σ.sc (s0 + 42)) P) ρ X
            (WithLp.toLp 2 fun c => w.gs (σ.draws + c)) • (fun c : Fin d => w.gs (σ.draws + c)) ∧
        σ'.mat (a0 + 16) = σ.mat (a0 + 16) + pgFt (pgKi w.K (σ.sc (s0 + 42)) P) ρ X
            (WithLp.toLp 2 fun c => w.gs (σ.draws + c)) • pgGG (WithLp.toLp 2 fun c => w.gs (σ.draws + c)) ∧
        σ'.draws = σ.draws + d ∧
        Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0) (pgTmpS s0 ++ [s0 + 36, s0 + 37])
          [a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 11, a0 + 15, a0 + 16]) := by
  obtain ⟨hdd, hjb, -, -, hρ, -⟩ := hV
  obtain ⟨hPm, hPA⟩ := hP
  obtain ⟨hXm, hXT⟩ := hX
  have h := hL.sampleM (w := w) σ hn0 hs0 ha0 hdv hone hdvb honeb hd h1 hmuv hAv hmub hAb hdd
  rw [hjb] at h
  refine runs_mono h le_rfl ?_
  intro σ' hσ'
  dsimp only at hσ'
  obtain ⟨e1, e2, e3, e4, e5⟩ := hσ'
  have hF : piTilde (pgBodySet w.K (σ.vec muv) (σ.mat Av) (σ.sc (s0 + 42))) (σ.sc (s0 + 19)) (pgJb d ρ)
      (WithLp.toLp 2 (σ.mat (a0 + 3) *ᵥ (fun c : Fin d => w.gs (σ.draws + c)) + σ.vec (a0 + 2))) =
      pgFt (pgKi w.K (σ.sc (s0 + 42)) P) ρ X (WithLp.toLp 2 fun c => w.gs (σ.draws + c)) := by
    rw [pgFt_eq, pgKi_eq, hPm, hPA, hXm, hXT, hρ]
  rw [hF] at e1 e2 e3
  exact ⟨e1, e2, e3, e4, e5⟩

theorem sqrt_dot_ofLp (y : EuclideanSpace ℝ (Fin d)) :
    Real.sqrt (WithLp.ofLp y ⬝ᵥ WithLp.ofLp y) = ‖y‖ := by
  rw [← norm_sq_eq_dot, Real.sqrt_sq (norm_nonneg _)]

/-! ## The composition -/

theorem runs_pgCompC {d : ℕ} {L : Layout} {w : World d} {dv one n0 s0 a0 muv Av : ℕ}
    (hL : PgLeaves) (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN)
    (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1)
    (hmuv : muv < L.NA) (hAv : Av < L.NA) (hmub : muv < a0 ∨ a0 + 32 ≤ muv) (hAb : Av < a0 ∨ a0 + 32 ≤ Av) (hmuA : muv ≠ Av) (hdd : σ.nat (n0 + 9) = d * d) :
    Runs L w (pgCompC L dv one n0 s0 a0 muv Av) σ (kCompC d)
      (fun σ' => σ'.vec muv = σ.vec muv + σ.mat Av *ᵥ σ.vec (a0 + 19) ∧ σ'.mat Av = σ.mat Av * σ.mat (a0 + 20) ∧
        Env.Frame σ σ' [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6] [s0 + 2, s0 + 8, s0 + 9, s0 + 11]
          [muv, Av, a0 + 21, a0 + 22]) := by
  unfold pgCompC kCompC
  refine runs_seq (runs_matvec σ hdv hone (by omega) (by omega) (by omega) (by omega) hAv (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hd h1) fun σ1 h1' => ?_
  obtain ⟨hv1, hF1, -⟩ := h1'
  have hd1 : σ1.nat dv = d := by rw [hF1.1 _ (by simp <;> omega)]; exact hd
  have h11 : σ1.nat one = 1 := by rw [hF1.1 _ (by simp <;> omega)]; exact h1
  refine runs_seq_eq (runs_sconst (by omega) 1) ?_
  refine runs_seq (runs_vaxpy _ hdv hone (by omega) hmuv (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by rw [Env.setSc_nat]; exact hd1) (by rw [Env.setSc_nat]; exact h11))
    fun σ3 h3 => ?_
  obtain ⟨hv3, hF3, -⟩ := h3
  have hF13 : Env.Frame σ1 σ3 [n0] [s0 + 2, s0 + 8, s0 + 9] [muv] :=
    Env.Frame.trans (Env.Frame.setSc (Env.Frame.refl σ1 _ _ _) (by simp) _) (Env.Frame.mono hF3 (by simp) (by simp) (by simp))
  have hd3 : σ3.nat dv = d := by rw [hF13.1 _ (by simp <;> omega)]; exact hd1
  have h13 : σ3.nat one = 1 := by rw [hF13.1 _ (by simp <;> omega)]; exact h11
  refine runs_seq (hL.mmul σ3 hdv hone (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hAv (by omega) (by omega) (by omega) (by omega) (by simp) (by simp <;> omega) (by simp <;> omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) hd3 h13) fun σ4 h4 => ?_
  obtain ⟨hm4, hF4, -⟩ := h4
  have hdd4 : σ4.nat (n0 + 9) = d * d := by
    rw [hF4.1 _ (by simp), hF13.1 _ (by simp), hF1.1 _ (by simp)]; exact hdd
  have h14 : σ4.nat one = 1 := by rw [hF4.1 _ (by simp <;> omega)]; exact h13
  refine runs_mono (runs_mcopy σ4 (by omega) hone (by omega) hAv (by omega) (by omega) (by omega) (by omega) hdd4 h14)
    le_rfl ?_
  rintro σ5 ⟨hm5, hF5, -⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [Env.vec_of_arr (hF5.2.2.1 _ (by simp <;> omega)), Env.vec_of_arr (hF4.2.2.1 _ (by simp <;> omega)), hv3]
    rw [show (σ1.setSc (s0 + 2) ((1 : ℚ) : ℝ)).vec muv = σ1.vec muv from rfl,
      show (σ1.setSc (s0 + 2) ((1 : ℚ) : ℝ)).vec (a0 + 22) = σ1.vec (a0 + 22) from rfl, Env.setSc_sc, if_pos rfl,
      Env.vec_of_arr (hF1.2.2.1 _ (by simp <;> omega)), hv1]
    simp
  · rw [hm5, hm4, Env.mat_of_arr (hF13.2.2.1 _ (by simp <;> omega)), Env.mat_of_arr (hF13.2.2.1 _ (by simp <;> omega)),
      Env.mat_of_arr (hF1.2.2.1 _ (by simp <;> omega)), Env.mat_of_arr (hF1.2.2.1 _ (by simp <;> omega))]
  · exact Env.Frame.trans (Env.Frame.mono hF1 (by simp) (by simp) (by simp))
      (Env.Frame.trans (Env.Frame.mono hF13 (by simp) (by simp) (by simp))
        (Env.Frame.trans (Env.Frame.mono hF4 (by simp) (by simp) (by simp))
          (Env.Frame.mono hF5 (by simp) (by simp) (by simp))))

end AdversarialBco.Poly.PG
