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
# Procedure PG in VL: the rules of the loops

The rules of the descent (`runs_pgStep`, `runs_pgDesc`), of a basic verdict (`runs_pgSample`, `runs_pgVerd`), of the
amplified test (`runs_pgTestC`), of the composition (`runs_pgCompC`) and of one repeat (`runs_pgRep`), each read off
the procedure of PgProc.lean (`pgDescent`, `pgVerdict`, `pgTest`).

They take as a hypothesis `PgLeaves`, the rules of the straight-line parts they call (one step of the descent, one
sample, the three clauses of a verdict) and the rule of `mmul`.
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

theorem pgMu_sum {ι : Type*} (s : Finset ι) (f : ι → PgSp d) : pgMu (∑ i ∈ s, f i) = ∑ i ∈ s, pgMu (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pgMu_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pgMu_add, ih]

theorem pgMat_sum {ι : Type*} (s : Finset ι) (f : ι → PgSp d) : pgMat (∑ i ∈ s, f i) = ∑ i ∈ s, pgMat (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pgMat_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pgMat_add, ih]

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

/-! ## One step of the descent -/

theorem runs_pgStep {L : Layout} {w : World d} {dv one n0 s0 a0 muv Av : ℕ} {ρ : ℝ} {P X S : PgSp d}
    (hL : PgLeaves) (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN)
    (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d)
    (h1 : σ.nat one = 1) (hmuv : muv < L.NA) (hAv : Av < L.NA) (hmub : muv < a0 ∨ a0 + 32 ≤ muv)
    (hAb : Av < a0 ∨ a0 + 32 ≤ Av) (hd1 : 1 ≤ d) (hρ1 : 1 ≤ ρ) (hV : PgStageVars σ n0 s0 ρ)
    (hP : PgAt σ muv Av P) (hX : PgAt σ a0 (a0 + 1) X) (hXD : X ∈ pgDom d ρ) (hS : PgAt σ (a0 + 2) (a0 + 3) S) :
    Runs L w (pgStep L dv one n0 s0 a0 muv Av) σ (kStep d (pgJb d ρ))
      (fun σ' => PgAt σ' a0 (a0 + 1) (pgProj d ρ (X - pgStepSize d ρ • pgV (pgKi w.K (σ.sc (s0 + 42)) P) ρ X
            (WithLp.toLp 2 fun c => w.gs (σ.draws + c)))) ∧
        PgAt σ' (a0 + 2) (a0 + 3) (S + X) ∧ σ'.draws = σ.draws + d ∧
        Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0) (pgTmpS s0 ++ [s0 + 31, s0 + 34, s0 + 35, s0 + 36])
          [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12,
            a0 + 13, a0 + 14]) := by
  obtain ⟨hdd, hjb, -, -, hρ, htmin, htmax, hkr, -, hnegs, hkd, -⟩ := hV
  obtain ⟨hPm, hPA⟩ := hP
  obtain ⟨hXm, hXT⟩ := hX
  obtain ⟨hSm, hST⟩ := hS
  have hstep := hL.stepM (w := w) σ hn0 hs0 ha0 hdv hone hdvb honeb hd h1 hmuv hAv hmub hAb hdd
  rw [hjb] at hstep
  refine runs_mono hstep le_rfl ?_
  intro σ' hσ'
  dsimp only at hσ'
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hσ'
  set gv : Fin d → ℝ := fun c => w.gs (σ.draws + c) with hgv
  set K' := pgKi w.K (σ.sc (s0 + 42)) P with hK'
  have hB : (gjRun (pgMat X) d).2 = (pgMat X)⁻¹ := gjRun_inv _ (pgMat_posDef hd1 hρ1 hXD)
  have hF : piTilde (pgBodySet w.K (σ.vec muv) (σ.mat Av) (σ.sc (s0 + 42))) (σ.sc (s0 + 19)) (pgJb d ρ)
      (WithLp.toLp 2 (σ.mat (a0 + 1) *ᵥ gv + σ.vec a0)) = pgFt K' ρ X (WithLp.toLp 2 gv) := by
    rw [pgFt_eq, hK', pgKi_eq, hPm, hPA, hXm, hXT, hρ]
  rw [hF, hXT, hB, hXm, hnegs, hkr] at e1
  rw [hF, hXT, hB, hnegs, hkd, htmin, htmax] at e2
  refine ⟨?_, ?_, e5, e6⟩
  · rw [pgProj_eq hd1 hρ1]
    unfold pgProjF
    refine ⟨?_, ?_⟩
    · rw [pgMu_pgPack, pgMove_mu]
      rw [show σ'.vec a0 = WithLp.ofLp (WithLp.toLp 2 (σ'.vec a0)) from rfl, e1]
    · rw [pgMat_pgPack, pgMove_mat, e2]
  · refine ⟨?_, ?_⟩
    · rw [e3, hSm, hXm, pgMu_add]; all_goals rfl
    · rw [e4, hST, hXT, pgMat_add]

/-! ## The descent -/

theorem pgIter_mem {K' : Set (EuclideanSpace ℝ (Fin d))} {ρ : ℝ} (hd1 : 1 ≤ d) (hρ1 : 1 ≤ ρ)
    (a : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) :
    sgdIter (pgProj d ρ) (pgV K' ρ) (pgStepSize d ρ) (pgX1 d ρ) a t ∈ pgDom d ρ := by
  cases t with
  | zero => exact pgX1_mem d ρ hd1 hρ1
  | succ t => simp only [sgdIter]; rw [pgProj_eq hd1 hρ1]; exact pgProjF_mem hd1 hρ1 _

theorem runs_pgDesc {L : Layout} {w : World d} {dv one n0 s0 a0 muv Av : ℕ} {ρ : ℝ} {P : PgSp d}
    (hL : PgLeaves) (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN)
    (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d)
    (h1 : σ.nat one = 1) (hmuv : muv < L.NA) (hAv : Av < L.NA) (hmub : muv < a0 ∨ a0 + 32 ≤ muv)
    (hAb : Av < a0 ∨ a0 + 32 ≤ Av) (hd1 : 1 ≤ d) (hρ1 : 1 ≤ ρ) (hV : PgStageVars σ n0 s0 ρ)
    (hP : PgAt σ muv Av P) :
    Runs L w (pgDesc L dv one n0 s0 a0 muv Av) σ (kDesc d (pgJb d ρ) (pgNs d ρ))
      (fun σ' => PgAt σ' (a0 + 2) (a0 + 3) (pgDescent (pgKi w.K (σ.sc (s0 + 42)) P) ρ
            (fun k => WithLp.toLp 2 fun c => w.gs (σ.draws + k * d + c))) ∧
        σ'.draws = σ.draws + pgNs d ρ * d ∧
        Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0 ++ [n0 + 13])
          (pgTmpS s0 ++ [s0 + 31, s0 + 33, s0 + 34, s0 + 35, s0 + 36, s0 + 45])
          [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12,
            a0 + 13, a0 + 14]) := by
  have hV0 := hV
  obtain ⟨hdd, -, hNs, -, -, htmin, -, -, -, -, -, -⟩ := hV0
  set K' := pgKi w.K (σ.sc (s0 + 42)) P with hK'
  set a : ℕ → EuclideanSpace ℝ (Fin d) := fun k => WithLp.toLp 2 fun c => w.gs (σ.draws + k * d + c) with ha
  set it : ℕ → PgSp d := sgdIter (pgProj d ρ) (pgV K' ρ) (pgStepSize d ρ) (pgX1 d ρ) a with hit
  have hsub : ∀ {ns ss as : List ℕ} {σ' : Env d}, Env.Frame σ { σ' with draws := σ.draws } ns ss as →
      (∀ i ∈ ns, i ∈ pgTmpN n0 ++ [n0 + 13]) →
      (∀ x ∈ ss, x ∈ pgTmpS s0 ++ [s0 + 31, s0 + 33, s0 + 34, s0 + 35, s0 + 36, s0 + 45]) →
      (∀ b ∈ as, b ∈ [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11,
        a0 + 12, a0 + 13, a0 + 14]) →
      Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0 ++ [n0 + 13])
        (pgTmpS s0 ++ [s0 + 31, s0 + 33, s0 + 34, s0 + 35, s0 + 36, s0 + 45])
        [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12,
          a0 + 13, a0 + 14] := fun h hn hs ha => Env.Frame.mono h hn hs ha
  -- the invariant of the loop
  let J : ℕ → Env d → Prop := fun t σ' => PgStageVars σ' n0 s0 ρ ∧ PgAt σ' muv Av P ∧
    σ'.sc (s0 + 42) = σ.sc (s0 + 42) ∧ σ'.nat dv = d ∧ PgAt σ' a0 (a0 + 1) (it t) ∧
    PgAt σ' (a0 + 2) (a0 + 3) (∑ t' ∈ Finset.range t, it t') ∧ σ'.draws = σ.draws + t * d ∧
    Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0 ++ [n0 + 13])
      (pgTmpS s0 ++ [s0 + 31, s0 + 33, s0 + 34, s0 + 35, s0 + 36, s0 + 45])
      [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12,
        a0 + 13, a0 + 14]
  unfold pgDesc kDesc
  -- the start: `x := (0, t_min I)`, the sums `:= 0`
  refine runs_seq_eq (runs_sconst (by omega) 0) ?_
  set σ1 := σ.setSc s0 ((0 : ℚ) : ℝ) with hσ1
  have h1z : σ1.sc s0 = 0 := by simp [σ1]
  have hF1 : Env.Frame σ σ1 [] [s0] [] := Env.Frame.setSc (Env.Frame.refl σ [] [s0] []) (by simp) _
  refine runs_seq (runs_vfill σ1 hdv hone (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp [σ1, hd]) (by simp [σ1, h1])) fun σ2 h2 => ?_
  obtain ⟨hv2, hF2, -⟩ := h2
  refine runs_seq (runs_mfill σ2 (by omega) hone (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [hF2.1 _ (by simp <;> omega)]; simp [σ1, hdd]) (by rw [hF2.1 _ (by simp <;> omega)]; simp [σ1, h1]))
    fun σ3 h3 => ?_
  obtain ⟨hm3, hF3, -⟩ := h3
  refine runs_seq (runs_mdiag σ3 hdv hone (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by rw [hF3.1 _ (by simp <;> omega), hF2.1 _ (by simp <;> omega)]; simp [σ1, hd])
    (by rw [hF3.1 _ (by simp <;> omega), hF2.1 _ (by simp <;> omega)]; simp [σ1, h1])) fun σ4 h4 => ?_
  obtain ⟨hm4, hF4, -⟩ := h4
  have hF14 : Env.Frame σ σ4 [n0, n0 + 2] [s0] [a0, a0 + 1] :=
    Env.Frame.trans (Env.Frame.mono hF1 (by simp) (by simp) (by simp))
      (Env.Frame.trans (Env.Frame.mono hF2 (by simp) (by simp) (by simp))
        (Env.Frame.trans (Env.Frame.mono hF3 (by simp) (by simp) (by simp))
          (Env.Frame.mono hF4 (by simp) (by simp) (by simp))))
  refine runs_seq (runs_vfill σ4 hdv hone (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [hF14.1 _ (by simp <;> omega)]; exact hd) (by rw [hF14.1 _ (by simp <;> omega)]; exact h1)) fun σ5 h5 => ?_
  obtain ⟨hv5, hF5, -⟩ := h5
  refine runs_seq (runs_mfill σ5 (by omega) hone (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [hF5.1 _ (by simp <;> omega), hF14.1 _ (by simp <;> omega)]; exact hdd)
    (by rw [hF5.1 _ (by simp <;> omega), hF14.1 _ (by simp <;> omega)]; exact h1)) fun σ6 h6 => ?_
  obtain ⟨hm6, hF6, -⟩ := h6
  have hF16 : Env.Frame σ σ6 [n0, n0 + 2] [s0] [a0, a0 + 1, a0 + 2, a0 + 3] :=
    Env.Frame.trans (Env.Frame.mono hF14 (by simp) (by simp) (by simp))
      (Env.Frame.trans (Env.Frame.mono hF5 (by simp) (by simp) (by simp))
        (Env.Frame.mono hF6 (by simp) (by simp) (by simp)))
  have hz4 : σ4.sc s0 = 0 := by rw [hF4.2.1 _ (by simp), hF3.2.1 _ (by simp), hF2.2.1 _ (by simp), h1z]
  have hJ0 : J 0 (σ6.setNat (n0 + 13) 0) := by
    have hF : Env.Frame σ (σ6.setNat (n0 + 13) 0) [n0, n0 + 2, n0 + 13] [s0] [a0, a0 + 1, a0 + 2, a0 + 3] :=
      Env.Frame.setNat (Env.Frame.mono hF16 (by simp) (by simp) (by simp)) (by simp) 0
    refine ⟨hV.of_frame hF (by simp <;> omega) (by simp <;> omega), hP.of_frame hF (by simp <;> omega) (by simp <;> omega),
      hF.2.1 _ (by simp <;> omega), (hF.1 _ (by simp <;> omega)).trans hd, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · show σ6.vec a0 = _
      rw [Env.vec_of_arr (hF6.2.2.1 a0 (by simp <;> omega)), Env.vec_of_arr (hF5.2.2.1 a0 (by simp <;> omega)),
        Env.vec_of_arr (hF4.2.2.1 a0 (by simp <;> omega)), Env.vec_of_arr (hF3.2.2.1 a0 (by simp <;> omega)), hv2, h1z]
      simp [it, sgdIter, pgX1, pgMu_pgPack]
    · show σ6.mat (a0 + 1) = _
      have hz2 : σ2.sc s0 = 0 := by rw [hF2.2.1 s0 (by simp), h1z]
      have e21 : σ3.sc (s0 + 21) = pgTmin d ρ := by
        rw [hF3.2.1 (s0 + 21) (by simp), hF2.2.1 (s0 + 21) (by simp), hσ1, Env.setSc_sc,
          ite_cond_eq_false _ _ (eq_false (show s0 + 21 ≠ s0 by omega)), htmin]
      rw [Env.mat_of_arr (hF6.2.2.1 (a0 + 1) (by simp <;> omega)),
        Env.mat_of_arr (hF5.2.2.1 (a0 + 1) (by simp <;> omega)), hm4, hm3, e21, hz2]
      simp only [it, sgdIter, pgX1, pgMat_pgPack]
      ext i j
      simp [Matrix.one_apply]
    · show σ6.vec (a0 + 2) = _
      rw [Env.vec_of_arr (hF6.2.2.1 _ (by simp <;> omega)), hv5, hz4]
      simp [pgMu_zero]
    · show σ6.mat (a0 + 3) = _
      rw [hm6, hF5.2.1 _ (by simp), hz4]
      ext i j
      simp [pgMat_zero]
    · show σ6.draws = σ.draws + 0 * d
      rw [hF16.2.2.2.1]; simp
    · exact frameD_of_frame (Env.Frame.mono hF (by simp [pgTmpN]) (by simp [pgTmpS]) (by simp))
  -- the loop
  have hnat6 : ∀ k, k ∉ [n0, n0 + 2] → σ6.nat k = σ.nat k := fun k hk => hF16.1 k hk
  refine runs_seq (runs_forN (by omega) (by omega) hone (by omega) (by omega) (pgNs d ρ) (kStep d (pgJb d ρ)) J σ6
    (by rw [hnat6 _ (by simp <;> omega)]; exact hNs) (by rw [hnat6 _ (by simp <;> omega)]; exact h1) hJ0
    ?_) fun σ7 h7 => ?_
  · intro t ht σ' hJ hi hn h1'
    obtain ⟨hV', hP', hR', hd', hX', hS', hdr', hF'⟩ := hJ
    have hstep := runs_pgStep hL (w := w) (X := it t) (S := ∑ t' ∈ Finset.range t, it t') σ' hn0 hs0 ha0 hdv hone
      hdvb honeb hd' h1' hmuv hAv hmub hAb hd1 hρ1 hV' hP' hX' (pgIter_mem hd1 hρ1 a t) hS'
    refine runs_mono hstep le_rfl fun σ'' ⟨e1, e2, e3, e4⟩ => ?_
    have hF'' : Env.Frame σ' { σ'' with draws := σ'.draws } (pgTmpN n0 ++ [n0 + 13])
        (pgTmpS s0 ++ [s0 + 31, s0 + 33, s0 + 34, s0 + 35, s0 + 36, s0 + 45])
        [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12,
          a0 + 13, a0 + 14] := Env.Frame.mono e4 (fun i hi => List.mem_append_left _ hi)
          (fun x hx => List.mem_append.2 ((List.mem_append.1 hx).imp id (fun h => by simp at h ⊢; omega)))
          (by simp)
    have hσ''n : ∀ k, k ∉ pgTmpN n0 → σ''.nat k = σ'.nat k := fun k hk => e4.1 k hk
    refine ⟨by rw [hσ''n _ (by simp [pgTmpN] <;> omega)]; exact hi, by rw [hσ''n _ (by simp [pgTmpN] <;> omega)]; exact hn,
      by rw [hσ''n _ (by simp [pgTmpN] <;> omega)]; exact h1', ?_⟩
    have hF3' : Env.Frame σ' { (σ''.setNat (n0 + 13) (t + 1)) with draws := σ'.draws }
        (pgTmpN n0 ++ [n0 + 13]) (pgTmpS s0 ++ [s0 + 31, s0 + 33, s0 + 34, s0 + 35, s0 + 36, s0 + 45])
        [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12,
          a0 + 13, a0 + 14] := Env.Frame.setNat hF'' (by simp) _
    have hga : (WithLp.toLp 2 fun c : Fin d => w.gs (σ'.draws + c) : EuclideanSpace ℝ (Fin d)) = a t := by
      simp only [a, hdr']
    rw [hga] at e1
    have hV3 := hV'.of_frame hF3' (by simp [pgTmpN] <;> omega) (by simp [pgTmpS] <;> omega)
    have hP3 := hP'.of_frame hF3' (by simp <;> omega) (by simp <;> omega)
    refine ⟨hV3, hP3, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show σ''.sc (s0 + 42) = _
      rw [hF''.2.1 _ (by simp [pgTmpS] <;> omega)]; exact hR'
    · exact (hF3'.1 dv (by simp [pgTmpN] <;> omega)).trans hd'
    · rw [hR'] at e1
      exact e1
    · show PgAt σ'' (a0 + 2) (a0 + 3) _
      rw [Finset.sum_range_succ]; exact e2
    · show σ''.draws = σ.draws + (t + 1) * d
      rw [e3, hdr']; ring
    · exact frameD_trans hF' hF3'
  -- the average
  obtain ⟨hJ7, -, -, h17⟩ := h7
  obtain ⟨hV7, -, -, hd7, -, hS7, hdr7, hF7⟩ := hJ7
  refine runs_seq_eq (runs_sconst (by omega) 1) ?_
  refine runs_seq_eq (runs_ncast (by omega) (by omega)) ?_
  refine runs_seq_eq (runs_sop2 (by omega) (by omega) (by omega) .div) ?_
  refine runs_seq_eq (runs_sconst (by omega) 0) ?_
  set σ8 := ((((σ7.setSc (s0 + 2) ((1 : ℚ) : ℝ)).setSc (s0 + 45) ((σ7.setSc (s0 + 2) ((1 : ℚ) : ℝ)).nat (n0 + 11))).setSc
    (s0 + 33) (Op2.div.eval (((σ7.setSc (s0 + 2) ((1 : ℚ) : ℝ)).setSc (s0 + 45)
      ((σ7.setSc (s0 + 2) ((1 : ℚ) : ℝ)).nat (n0 + 11))).sc (s0 + 2))
      (((σ7.setSc (s0 + 2) ((1 : ℚ) : ℝ)).setSc (s0 + 45) ((σ7.setSc (s0 + 2) ((1 : ℚ) : ℝ)).nat (n0 + 11))).sc
        (s0 + 45)))).setSc s0 ((0 : ℚ) : ℝ)) with hσ8
  have hF8 : Env.Frame σ7 σ8 [] [s0, s0 + 2, s0 + 33, s0 + 45] [] :=
    Env.Frame.setSc (Env.Frame.setSc (Env.Frame.setSc (Env.Frame.setSc (Env.Frame.refl σ7 _ _ _) (by simp) _)
      (by simp) _) (by simp) _) (by simp) _
  have hinv : σ8.sc (s0 + 33) = ((pgNs d ρ : ℕ) : ℝ)⁻¹ := by
    have hN7 : σ7.nat (n0 + 11) = pgNs d ρ := hV7.2.2.1
    simp [σ8, Op2.eval, hN7, (show s0 + 33 ≠ s0 by omega), (show s0 + 45 ≠ s0 + 2 by omega)]
  refine runs_seq (runs_vscale σ8 hdv hone (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [hF8.1 _ (by simp)]; exact hd7) (by rw [hF8.1 _ (by simp)]; exact h17)) fun σ9 h9 => ?_
  obtain ⟨hv9, hF9, -⟩ := h9
  refine runs_mono (runs_mlin σ9 (by omega) hone (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [hF9.1 _ (by simp <;> omega), hF8.1 _ (by simp)]; exact hV7.1)
    (by rw [hF9.1 _ (by simp <;> omega), hF8.1 _ (by simp)]; exact h17)) le_rfl ?_
  rintro σ' ⟨hm', hF', -⟩
  have hF89 : Env.Frame σ7 σ' [n0] [s0, s0 + 2, s0 + 8, s0 + 9, s0 + 33, s0 + 45] [a0 + 2, a0 + 3] :=
    Env.Frame.trans (Env.Frame.mono hF8 (by simp) (by simp) (by simp))
      (Env.Frame.trans (Env.Frame.mono hF9 (by simp) (by simp) (by simp))
        (Env.Frame.mono hF' (by simp) (by simp) (by simp)))
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Env.vec_of_arr (hF'.2.2.1 _ (by simp <;> omega)), hv9, hinv,
      Env.vec_of_arr (hF8.2.2.1 _ (by simp)), hS7.1]
    simp only [pgDescent, sgdAvg, pgMu_smul]
    rfl
  · rw [hm', hF9.2.1 _ (by simp <;> omega), hF9.2.1 _ (by simp <;> omega), Env.mat_of_arr (hF9.2.2.1 _ (by simp <;> omega)),
      hinv, Env.mat_of_arr (hF8.2.2.1 _ (by simp)), hS7.2]
    have hz8 : σ8.sc s0 = 0 := by simp [σ8]
    rw [hz8, zero_smul, add_zero]
    simp only [pgDescent, sgdAvg, pgMat_smul]
    rfl
  · rw [hF'.2.2.2.1, hF9.2.2.2.1]
    show σ7.draws = _
    rw [hdr7]
  · exact frameD_trans hF7 (frameD_of_frame (Env.Frame.mono hF89 (by simp [pgTmpN]) (by simp [pgTmpS]) (by simp)))


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

theorem dot_symPart_mulVec (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    v ⬝ᵥ (symPart M *ᵥ v) = v ⬝ᵥ (M *ᵥ v) := by
  have h : v ⬝ᵥ (Mᵀ *ᵥ v) = v ⬝ᵥ (M *ᵥ v) := by
    rw [Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec]
  simp only [symPart, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add, h,
    smul_eq_mul]
  ring

theorem sqrt_dot_ofLp (y : EuclideanSpace ℝ (Fin d)) :
    Real.sqrt (WithLp.ofLp y ⬝ᵥ WithLp.ofLp y) = ‖y‖ := by
  rw [← norm_sq_eq_dot, Real.sqrt_sq (norm_nonneg _)]

open Classical in
/-- The value the code gives to a basic verdict is its indicator. -/
theorem pgVerdict_code (K' : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (X : PgSp d)
    (ws : ℕ → EuclideanSpace ℝ (Fin d)) :
    (if 0 < (cfc (Spec.fn .step 0 0) (symPart (((-5 / 8 : ℝ) * -(pgKappa / d)) • (1 : Matrix (Fin d) (Fin d) ℝ) -
        ((pgNT d ρ : ℝ))⁻¹ • ∑ i ∈ Finset.range (pgNT d ρ), pgFt K' ρ X (ws i) • pgGG (ws i)))).trace then (0 : ℝ)
      else if ((pgNT d ρ : ℝ))⁻¹ * ∑ i ∈ Finset.range (pgNT d ρ), pgFt K' ρ X (ws i) ≤ 43 / 320 ∧
          Real.sqrt ((((pgNT d ρ : ℝ))⁻¹ • ∑ i ∈ Finset.range (pgNT d ρ), pgFt K' ρ X (ws i) • (fun c => ws i c)) ⬝ᵥ
            (((pgNT d ρ : ℝ))⁻¹ • ∑ i ∈ Finset.range (pgNT d ρ), pgFt K' ρ X (ws i) • (fun c => ws i c))) ≤
            3 / 4 * pgTaub d ρ then 1 else 0) =
      if pgVerdict K' ρ X ws then 1 else 0 := by
  set n := pgNT d ρ
  set Qh := ((n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, pgFt K' ρ X (ws i) • pgGG (ws i) with hQh
  have hN := symPart_isHermitian ((((-5 / 8 : ℝ) * -(pgKappa / d)) • (1 : Matrix (Fin d) (Fin d) ℝ) - Qh))
  have hstep : Spec.fn .step 0 0 = fun x : ℝ => if 0 < x then (1 : ℝ) else 0 := rfl
  have hC : ¬ 0 < (cfc (Spec.fn .step 0 0) (symPart (((-5 / 8 : ℝ) * -(pgKappa / d)) •
      (1 : Matrix (Fin d) (Fin d) ℝ) - Qh))).trace ↔
      ∀ v : Fin d → ℝ, 5 / 8 * (pgKappa / d) * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Qh *ᵥ v) := by
    rw [not_lt, hstep, trace_step_le_zero_iff _ hN]
    refine forall_congr' fun v => ?_
    rw [dot_symPart_mulVec, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul]
    constructor <;> intro h <;> linarith
  have hA : ∀ x : ℝ, x ≤ 43 / 320 ↔ x ≤ 1.075 * pgKappa := fun x => by norm_num [pgKappa]
  have hB : Real.sqrt ((((n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, pgFt K' ρ X (ws i) • (fun c => ws i c)) ⬝ᵥ
      (((n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, pgFt K' ρ X (ws i) • (fun c => ws i c))) =
      ‖((n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, pgFt K' ρ X (ws i) • ws i‖ := by
    rw [← sqrt_dot_ofLp]
    simp only [WithLp.ofLp_smul, WithLp.ofLp_sum]
  by_cases hT : 0 < (cfc (Spec.fn .step 0 0) (symPart (((-5 / 8 : ℝ) * -(pgKappa / d)) •
      (1 : Matrix (Fin d) (Fin d) ℝ) - Qh))).trace
  · rw [if_pos hT, if_neg]
    intro hv
    simp only [pgVerdict] at hv
    exact (hC.2 hv.2.2) hT
  · rw [if_neg hT]
    have h3 := hC.1 hT
    by_cases h12 : ((n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, pgFt K' ρ X (ws i) ≤ 43 / 320 ∧
        Real.sqrt ((((n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, pgFt K' ρ X (ws i) • (fun c => ws i c)) ⬝ᵥ
          (((n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, pgFt K' ρ X (ws i) • (fun c => ws i c))) ≤ 3 / 4 * pgTaub d ρ
    · rw [if_pos h12, if_pos]
      simp only [pgVerdict]
      exact ⟨(hA _).1 h12.1, hB ▸ h12.2, h3⟩
    · rw [if_neg h12, if_neg]
      intro hv
      simp only [pgVerdict] at hv
      exact h12 ⟨(hA _).2 hv.1, hB ▸ hv.2.1⟩


open Classical in
/-- One basic verdict at `x̄ = X`: the count `s0 + 40` grows by the indicator of `pgVerdict` on the next `n_T` vectors. -/
theorem runs_pgVerd {L : Layout} {w : World d} {dv one n0 s0 a0 muv Av : ℕ} {ρ : ℝ} {P X : PgSp d}
    (hL : PgLeaves) (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN)
    (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d)
    (h1 : σ.nat one = 1) (hmuv : muv < L.NA) (hAv : Av < L.NA) (hmub : muv < a0 ∨ a0 + 32 ≤ muv)
    (hAb : Av < a0 ∨ a0 + 32 ≤ Av) (hV : PgStageVars σ n0 s0 ρ) (hP : PgAt σ muv Av P)
    (hX : PgAt σ (a0 + 2) (a0 + 3) X) :
    Runs L w (pgVerd L dv one n0 s0 a0 muv Av) σ (kVerd d (pgJb d ρ) (pgNT d ρ))
      (fun σ' => σ'.sc (s0 + 40) = σ.sc (s0 + 40) + (if pgVerdict (pgKi w.K (σ.sc (s0 + 42)) P) ρ X
            (fun k => WithLp.toLp 2 fun c => w.gs (σ.draws + k * d + c)) then 1 else 0) ∧
        σ'.draws = σ.draws + pgNT d ρ * d ∧
        Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0 ++ [n0 + 13])
          (pgTmpS s0 ++ [s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 51])
          [a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 11, a0 + 15, a0 + 16, a0 + 17, a0 + 18]) := by
  have hV0 := hV
  obtain ⟨hdd, -, -, hNT, -, -, -, -, htaub, -, hkd, -⟩ := hV0
  set K' := pgKi w.K (σ.sc (s0 + 42)) P with hK'
  set ws : ℕ → EuclideanSpace ℝ (Fin d) := fun k => WithLp.toLp 2 fun c => w.gs (σ.draws + k * d + c) with hws
  set F : ℕ → ℝ := fun i => pgFt K' ρ X (ws i) with hFdef
  let J : ℕ → Env d → Prop := fun t σ' => PgStageVars σ' n0 s0 ρ ∧ PgAt σ' muv Av P ∧
    PgAt σ' (a0 + 2) (a0 + 3) X ∧ σ'.sc (s0 + 42) = σ.sc (s0 + 42) ∧ σ'.nat dv = d ∧
    σ'.sc (s0 + 40) = σ.sc (s0 + 40) ∧ σ'.sc (s0 + 37) = ∑ i ∈ Finset.range t, F i ∧
    σ'.vec (a0 + 15) = ∑ i ∈ Finset.range t, F i • (fun c => ws i c) ∧
    σ'.mat (a0 + 16) = ∑ i ∈ Finset.range t, F i • pgGG (ws i) ∧ σ'.draws = σ.draws + t * d ∧
    Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0 ++ [n0 + 13])
      (pgTmpS s0 ++ [s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 51])
      [a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 11, a0 + 15, a0 + 16, a0 + 17, a0 + 18]
  unfold pgVerd kVerd
  -- the accumulators `:= 0`
  refine runs_seq_eq (runs_sconst (by omega) 0) ?_
  refine runs_seq_eq (runs_sconst (by omega) 0) ?_
  set σ1 := (σ.setSc s0 ((0 : ℚ) : ℝ)).setSc (s0 + 37) ((0 : ℚ) : ℝ) with hσ1
  have h1z : σ1.sc s0 = 0 := by simp [σ1]
  have h37 : σ1.sc (s0 + 37) = 0 := by simp [σ1]
  have hF1 : Env.Frame σ σ1 [] [s0, s0 + 37] [] :=
    Env.Frame.setSc (Env.Frame.setSc (Env.Frame.refl σ [] [s0, s0 + 37] []) (by simp) _) (by simp) _
  refine runs_seq (runs_vfill σ1 hdv hone (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [hF1.1 _ (by simp)]; exact hd) (by rw [hF1.1 _ (by simp)]; exact h1)) fun σ2 h2 => ?_
  obtain ⟨hv2, hF2, -⟩ := h2
  refine runs_seq (runs_mfill σ2 (by omega) hone (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [hF2.1 _ (by simp <;> omega), hF1.1 _ (by simp)]; exact hdd)
    (by rw [hF2.1 _ (by simp <;> omega), hF1.1 _ (by simp)]; exact h1)) fun σ3 h3 => ?_
  obtain ⟨hm3, hF3, -⟩ := h3
  have hF13 : Env.Frame σ σ3 [n0] [s0, s0 + 37] [a0 + 15, a0 + 16] :=
    Env.Frame.trans (Env.Frame.mono hF1 (by simp) (by simp) (by simp))
      (Env.Frame.trans (Env.Frame.mono hF2 (by simp) (by simp) (by simp))
        (Env.Frame.mono hF3 (by simp) (by simp) (by simp)))
  have hJ0 : J 0 (σ3.setNat (n0 + 13) 0) := by
    have hF : Env.Frame σ (σ3.setNat (n0 + 13) 0) [n0, n0 + 13] [s0, s0 + 37] [a0 + 15, a0 + 16] :=
      Env.Frame.setNat (Env.Frame.mono hF13 (by simp) (by simp) (by simp)) (by simp) 0
    refine ⟨hV.of_frame hF (by simp <;> omega) (by simp <;> omega),
      hP.of_frame hF (by simp <;> omega) (by simp <;> omega), hX.of_frame hF (by simp) (by simp),
      hF.2.1 _ (by simp), (hF.1 _ (by simp <;> omega)).trans hd, hF.2.1 _ (by simp), ?_, ?_, ?_, ?_, ?_⟩
    · show σ3.sc (s0 + 37) = _
      rw [hF3.2.1 _ (by simp), hF2.2.1 _ (by simp), h37, Finset.sum_range_zero]
    · show σ3.vec (a0 + 15) = _
      rw [Env.vec_of_arr (hF3.2.2.1 _ (by simp)), hv2, h1z, Finset.sum_range_zero]
      rfl
    · show σ3.mat (a0 + 16) = _
      rw [hm3, hF2.2.1 _ (by simp), h1z, Finset.sum_range_zero]
      ext i j
      simp
    · show σ3.draws = σ.draws + 0 * d
      rw [hF13.2.2.2.1]; simp
    · exact frameD_of_frame (Env.Frame.mono hF (by simp [pgTmpN]) (by simp [pgTmpS]) (by simp))
  -- the samples
  have hnat3 : ∀ k, k ∉ [n0] → σ3.nat k = σ.nat k := fun k hk => hF13.1 k hk
  refine runs_seq (runs_forN (by omega) (by omega) hone (by omega) (by omega) (pgNT d ρ) (kSample d (pgJb d ρ)) J σ3
    (by rw [hnat3 _ (by simp)]; exact hNT) (by rw [hnat3 _ (by simp <;> omega)]; exact h1) hJ0
    ?_) fun σ7 h7 => ?_
  · intro t ht σ' hJ hi hn h1'
    obtain ⟨hV', hP', hX', hR', hd', h40', hk', hb', hQ', hdr', hF'⟩ := hJ
    have hs := runs_pgSample hL (w := w) σ' hn0 hs0 ha0 hdv hone hdvb honeb hd' h1' hmuv hAv hmub hAb hV' hP' hX'
    refine runs_mono hs le_rfl fun σ'' ⟨e1, e2, e3, e4, e5⟩ => ?_
    have hσ''n : ∀ k, k ∉ pgTmpN n0 → σ''.nat k = σ'.nat k := fun k hk => e5.1 k hk
    refine ⟨by rw [hσ''n _ (by simp [pgTmpN] <;> omega)]; exact hi, by rw [hσ''n _ (by simp [pgTmpN] <;> omega)]; exact hn,
      by rw [hσ''n _ (by simp [pgTmpN] <;> omega)]; exact h1', ?_⟩
    have hF'' : Env.Frame σ' { σ'' with draws := σ'.draws } (pgTmpN n0 ++ [n0 + 13])
        (pgTmpS s0 ++ [s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 51])
        [a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 11, a0 + 15, a0 + 16, a0 + 17, a0 + 18] :=
      Env.Frame.mono e5 (fun i hi => List.mem_append_left _ hi)
        (fun x hx => List.mem_append.2 ((List.mem_append.1 hx).imp id (fun h => by simp at h ⊢; omega)))
        (fun b hb => by simp at hb ⊢; omega)
    have hF3' : Env.Frame σ' { (σ''.setNat (n0 + 13) (t + 1)) with draws := σ'.draws }
        (pgTmpN n0 ++ [n0 + 13])
        (pgTmpS s0 ++ [s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 51])
        [a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 11, a0 + 15, a0 + 16, a0 + 17, a0 + 18] :=
      Env.Frame.setNat hF'' (by simp) _
    have hga : (WithLp.toLp 2 fun c : Fin d => w.gs (σ'.draws + c) : EuclideanSpace ℝ (Fin d)) = ws t := by
      simp only [ws, hdr']
    have hgf : (fun c : Fin d => w.gs (σ'.draws + c)) = fun c => ws t c := by
      simp only [ws, hdr']
    rw [hga, hR'] at e1 e2 e3
    rw [hgf] at e2
    have hV3 := hV'.of_frame hF3' (by simp [pgTmpN] <;> omega) (by simp [pgTmpS] <;> omega)
    have hP3 := hP'.of_frame hF3' (by simp <;> omega) (by simp <;> omega)
    have hX3 := hX'.of_frame hF3' (by simp) (by simp)
    refine ⟨hV3, hP3, hX3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show σ''.sc (s0 + 42) = _
      rw [e5.2.1 _ (by simp [pgTmpS] <;> omega)]; exact hR'
    · exact (hF3'.1 dv (by simp [pgTmpN] <;> omega)).trans hd'
    · show σ''.sc (s0 + 40) = _
      rw [e5.2.1 _ (by simp [pgTmpS] <;> omega)]; exact h40'
    · show σ''.sc (s0 + 37) = _
      rw [e1, hk', Finset.sum_range_succ]
    · show σ''.vec (a0 + 15) = _
      rw [e2, hb', Finset.sum_range_succ]
    · show σ''.mat (a0 + 16) = _
      rw [e3, hQ', Finset.sum_range_succ]
    · show σ''.draws = σ.draws + (t + 1) * d
      rw [e4, hdr']; ring
    · exact frameD_trans hF' hF3'
  -- the averages and the three clauses
  obtain ⟨hJ7, -, -, h17⟩ := h7
  obtain ⟨hV7, -, -, -, hd7, h407, hk7, hb7, hQ7, hdr7, hF7⟩ := hJ7
  refine runs_seq (hL.verdNorm σ7 hn0 hs0 ha0 hdv hone hdvb honeb hd7 h17 hV7.1) fun σ8 h8 => ?_
  obtain ⟨n37, n15, n16, hF8⟩ := h8
  have hd8 : σ8.nat dv = d := by rw [hF8.1 _ (by simp <;> omega)]; exact hd7
  have h18 : σ8.nat one = 1 := by rw [hF8.1 _ (by simp <;> omega)]; exact h17
  refine runs_seq (hL.verdC12 σ8 hn0 hs0 ha0 hdv hone hdvb honeb hd8 h18) fun σ9 h9 => ?_
  obtain ⟨v9, hF9⟩ := h9
  have hd9 : σ9.nat dv = d := by rw [hF9.1 _ (by simp <;> omega)]; exact hd8
  have h19 : σ9.nat one = 1 := by rw [hF9.1 _ (by simp <;> omega)]; exact h18
  have hdd9 : σ9.nat (n0 + 9) = d * d := by
    rw [hF9.1 _ (by simp), hF8.1 _ (by simp)]; exact hV7.1
  refine runs_seq (hL.verdC3 σ9 hn0 hs0 ha0 hdv hone hdvb honeb hd9 h19 hdd9) fun σ10 h10 => ?_
  obtain ⟨v10, hF10⟩ := h10
  refine runs_mono (runs_sop2 (by omega) (by omega) (by omega) .add) le_rfl ?_
  rintro σ' rfl
  have hn7 : σ7.nat (n0 + 12) = pgNT d ρ := hV7.2.2.2.1
  have hkd9 : σ9.sc (s0 + 32) = -(pgKappa / d) := by
    rw [hF9.2.1 _ (by simp), hF8.2.1 _ (by simp)]; exact hV7.2.2.2.2.2.2.2.2.2.2.1
  have htb8 : σ8.sc (s0 + 28) = pgTaub d ρ := by
    rw [hF8.2.1 _ (by simp)]; exact hV7.2.2.2.2.2.2.2.2.1
  have hm9 : σ9.mat (a0 + 16) = σ8.mat (a0 + 16) := Env.mat_of_arr (hF9.2.2.1 _ (by simp))
  have h409 : σ10.sc (s0 + 40) = σ.sc (s0 + 40) := by
    rw [hF10.2.1 _ (by simp), hF9.2.1 _ (by simp), hF8.2.1 _ (by simp)]; exact h407
  refine ⟨?_, ?_, ?_⟩
  · simp only [Env.setSc_sc, if_true, Op2.eval]
    rw [h409, v10, v9, hkd9, hm9, n16, n37, n15, htb8, hn7, hk7, hb7, hQ7]
    congr 1
    exact pgVerdict_code K' ρ X ws
  · show σ10.draws = _
    rw [hF10.2.2.2.1, hF9.2.2.2.1, hF8.2.2.2.1, hdr7]
  · have hF810 : Env.Frame σ7 (σ10.setSc (s0 + 40) (Op2.add.eval (σ10.sc (s0 + 40)) (σ10.sc (s0 + 39)))) [n0, n0 + 2]
        [s0, s0 + 2, s0 + 8, s0 + 9, s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 44, s0 + 45, s0 + 46, s0 + 47,
          s0 + 51] [a0 + 15, a0 + 16, a0 + 17, a0 + 18] :=
      Env.Frame.trans (Env.Frame.mono hF8 (by simp) (by simp) (by simp))
        (Env.Frame.trans (Env.Frame.mono hF9 (by simp) (by simp) (by simp))
          (Env.Frame.trans (Env.Frame.mono hF10 (by simp) (by simp) (by simp))
            (Env.Frame.setSc (Env.Frame.refl σ10 _ _ _) (by simp) _)))
    exact frameD_trans hF7 (frameD_of_frame (Env.Frame.mono hF810 (by simp [pgTmpN]) (by simp [pgTmpS]) (by simp)))

/-! ## The amplified test -/

open Classical in
theorem pgTest_count (K' : Set (EuclideanSpace ℝ (Fin d))) (ρ δ : ℝ) (X : PgSp d)
    (wsT : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) :
    ((pgMT δ : ℝ) * ((1 : ℚ) / 2 : ℚ) <
        ∑ v ∈ Finset.range (pgMT δ), if pgVerdict K' ρ X (wsT v) then (1 : ℝ) else 0) ↔ pgTest K' ρ δ X wsT := by
  rw [pgTest, Finset.sum_boole]
  push_cast
  constructor <;> intro h <;> linarith

open Classical in
/-- The amplified test at `x̄ = X`: `pass` (`s0 + 49`) is the indicator of `pgTest` on the next `m_T n_T` vectors. -/
theorem runs_pgTestC {L : Layout} {w : World d} {dv one n0 s0 a0 muv Av : ℕ} {ρ δ : ℝ} {P X : PgSp d}
    (hL : PgLeaves) (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN)
    (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d)
    (h1 : σ.nat one = 1) (hmuv : muv < L.NA) (hAv : Av < L.NA) (hmub : muv < a0 ∨ a0 + 32 ≤ muv)
    (hAb : Av < a0 ∨ a0 + 32 ≤ Av) (hV : PgStageVars σ n0 s0 ρ) (hP : PgAt σ muv Av P)
    (hX : PgAt σ (a0 + 2) (a0 + 3) X) (hmT : σ.nat (n0 + 14) = pgMT δ) :
    Runs L w (pgTestC L dv one n0 s0 a0 muv Av) σ (kTest d (pgJb d ρ) (pgNT d ρ) (pgMT δ))
      (fun σ' => σ'.sc (s0 + 49) = (if pgTest (pgKi w.K (σ.sc (s0 + 42)) P) ρ δ X
            (fun v k => WithLp.toLp 2 fun c => w.gs (σ.draws + (v * pgNT d ρ + k) * d + c)) then 1 else 0) ∧
        σ'.draws = σ.draws + pgMT δ * (pgNT d ρ * d) ∧
        Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0 ++ [n0 + 13, n0 + 15])
          (pgTmpS s0 ++ [s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 49,
            s0 + 51])
          [a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 11, a0 + 15, a0 + 16, a0 + 17, a0 + 18]) := by
  set K' := pgKi w.K (σ.sc (s0 + 42)) P with hK'
  set wsT : ℕ → ℕ → EuclideanSpace ℝ (Fin d) :=
    fun v k => WithLp.toLp 2 fun c => w.gs (σ.draws + (v * pgNT d ρ + k) * d + c) with hwsT
  set cnt : ℕ → ℝ := fun t => ∑ v ∈ Finset.range t, if pgVerdict K' ρ X (wsT v) then (1 : ℝ) else 0 with hcnt
  let J : ℕ → Env d → Prop := fun t σ' => PgStageVars σ' n0 s0 ρ ∧ PgAt σ' muv Av P ∧
    PgAt σ' (a0 + 2) (a0 + 3) X ∧ σ'.sc (s0 + 42) = σ.sc (s0 + 42) ∧ σ'.nat dv = d ∧
    σ'.nat (n0 + 14) = pgMT δ ∧ σ'.sc (s0 + 40) = cnt t ∧ σ'.draws = σ.draws + t * (pgNT d ρ * d) ∧
    Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0 ++ [n0 + 13, n0 + 15])
      (pgTmpS s0 ++ [s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 49,
        s0 + 51])
      [a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 11, a0 + 15, a0 + 16, a0 + 17, a0 + 18]
  unfold pgTestC kTest
  refine runs_seq_eq (runs_sconst (by omega) 0) ?_
  set σ1 := σ.setSc (s0 + 40) ((0 : ℚ) : ℝ) with hσ1
  have hF1 : Env.Frame σ (σ1.setNat (n0 + 15) 0) [n0 + 15] [s0 + 40] [] :=
    Env.Frame.setNat (Env.Frame.setSc (Env.Frame.refl σ [n0 + 15] [s0 + 40] []) (by simp) _) (by simp) 0
  have hJ0 : J 0 (σ1.setNat (n0 + 15) 0) := by
    refine ⟨hV.of_frame hF1 (by simp <;> omega) (by simp <;> omega),
      hP.of_frame hF1 (by simp) (by simp), hX.of_frame hF1 (by simp) (by simp),
      hF1.2.1 _ (by simp), (hF1.1 _ (by simp <;> omega)).trans hd, (hF1.1 _ (by simp)).trans hmT, ?_, ?_, ?_⟩
    · show σ1.sc (s0 + 40) = _
      simp [σ1, cnt]
    · show σ.draws = σ.draws + 0 * (pgNT d ρ * d)
      simp
    · exact frameD_of_frame (Env.Frame.mono hF1 (by simp) (by simp) (by simp))
  have hσ1n : ∀ k, k ≠ n0 + 15 → (σ1.setNat (n0 + 15) 0).nat k = σ.nat k := fun k hk => hF1.1 k (by simpa using hk)
  refine runs_seq (runs_forN (by omega) (by omega) hone (by omega) (by omega) (pgMT δ)
    (kVerd d (pgJb d ρ) (pgNT d ρ)) J σ1 (by rw [show σ1.nat (n0 + 14) = σ.nat (n0 + 14) from rfl]; exact hmT)
    (by rw [show σ1.nat one = σ.nat one from rfl]; exact h1) hJ0 ?_) fun σ7 h7 => ?_
  · intro t ht σ' hJ hi hn h1'
    obtain ⟨hV', hP', hX', hR', hd', hm', hc', hdr', hF'⟩ := hJ
    have hs := runs_pgVerd hL (w := w) σ' hn0 hs0 ha0 hdv hone hdvb honeb hd' h1' hmuv hAv hmub hAb hV' hP' hX'
    refine runs_mono hs le_rfl fun σ'' ⟨e1, e2, e3⟩ => ?_
    have hσ''n : ∀ k, k ∉ pgTmpN n0 ++ [n0 + 13] → σ''.nat k = σ'.nat k := fun k hk => e3.1 k hk
    refine ⟨by rw [hσ''n _ (by simp [pgTmpN] <;> omega)]; exact hi, by rw [hσ''n _ (by simp [pgTmpN] <;> omega)]; exact hn,
      by rw [hσ''n _ (by simp [pgTmpN] <;> omega)]; exact h1', ?_⟩
    have hF'' : Env.Frame σ' { σ'' with draws := σ'.draws } (pgTmpN n0 ++ [n0 + 13, n0 + 15])
        (pgTmpS s0 ++ [s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 49,
          s0 + 51])
        [a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 11, a0 + 15, a0 + 16, a0 + 17, a0 + 18] :=
      Env.Frame.mono e3 (fun i hi => List.mem_append.2 ((List.mem_append.1 hi).imp id (fun h => by simp at h ⊢; omega)))
        (fun x hx => List.mem_append.2 ((List.mem_append.1 hx).imp id (fun h => by simp at h ⊢; omega)))
        (fun b hb => by simp at hb ⊢; omega)
    have hF3' : Env.Frame σ' { (σ''.setNat (n0 + 15) (t + 1)) with draws := σ'.draws }
        (pgTmpN n0 ++ [n0 + 13, n0 + 15])
        (pgTmpS s0 ++ [s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 49,
          s0 + 51])
        [a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 11, a0 + 15, a0 + 16, a0 + 17, a0 + 18] :=
      Env.Frame.setNat hF'' (by simp) _
    have hws : (fun k => WithLp.toLp 2 fun c : Fin d => w.gs (σ'.draws + k * d + c) :
        ℕ → EuclideanSpace ℝ (Fin d)) = wsT t := by
      funext k
      simp only [wsT, hdr']
      congr 1
      funext c
      congr 1
      ring
    rw [hws, hR'] at e1
    have hV3 := hV'.of_frame hF3' (by simp [pgTmpN] <;> omega) (by simp [pgTmpS] <;> omega)
    have hP3 := hP'.of_frame hF3' (by simp <;> omega) (by simp <;> omega)
    have hX3 := hX'.of_frame hF3' (by simp) (by simp)
    refine ⟨hV3, hP3, hX3, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show σ''.sc (s0 + 42) = _
      rw [e3.2.1 _ (by simp [pgTmpS] <;> omega)]; exact hR'
    · exact (hF3'.1 dv (by simp [pgTmpN] <;> omega)).trans hd'
    · exact (hF3'.1 (n0 + 14) (by simp [pgTmpN])).trans hm'
    · show σ''.sc (s0 + 40) = _
      rw [e1, hc', hcnt]
      simp only [Finset.sum_range_succ]
      rfl
    · show σ''.draws = σ.draws + (t + 1) * (pgNT d ρ * d)
      rw [e2, hdr']; ring
    · exact frameD_trans hF' hF3'
  -- the majority
  obtain ⟨hJ7, -, -, h17⟩ := h7
  obtain ⟨-, -, -, -, -, hm7, hc7, hdr7, hF7⟩ := hJ7
  refine runs_seq_eq (runs_ncast (by omega) (by omega)) ?_
  refine runs_seq_eq (runs_sconst (by omega) (1 / 2)) ?_
  refine runs_seq_eq (runs_sop2 (by omega) (by omega) (by omega) .mul) ?_
  refine runs_seq_eq (runs_sconst (by omega) 0) ?_
  set σ8 := (((σ7.setSc (s0 + 45) (σ7.nat (n0 + 14))).setSc (s0 + 1) ((1 / 2 : ℚ) : ℝ)).setSc (s0 + 45)
    (Op2.mul.eval (((σ7.setSc (s0 + 45) (σ7.nat (n0 + 14))).setSc (s0 + 1) ((1 / 2 : ℚ) : ℝ)).sc (s0 + 45))
      (((σ7.setSc (s0 + 45) (σ7.nat (n0 + 14))).setSc (s0 + 1) ((1 / 2 : ℚ) : ℝ)).sc (s0 + 1)))).setSc (s0 + 49)
    ((0 : ℚ) : ℝ) with hσ8
  have hF8 : Env.Frame σ7 σ8 [] [s0 + 1, s0 + 45, s0 + 49] [] :=
    Env.Frame.setSc (Env.Frame.setSc (Env.Frame.setSc (Env.Frame.setSc (Env.Frame.refl σ7 _ _ _) (by simp) _)
      (by simp) _) (by simp) _) (by simp) _
  have h45 : σ8.sc (s0 + 45) = (pgMT δ : ℝ) * ((1 / 2 : ℚ) : ℝ) := by
    simp [σ8, Op2.eval, hm7]
  have h40 : σ8.sc (s0 + 40) = cnt (pgMT δ) := by
    rw [hF8.2.1 _ (by simp)]; exact hc7
  have hfin : ∀ σ' : Env d, Env.Frame σ8 σ' [] [s0 + 49] [] → σ'.sc (s0 + 49) =
      (if pgTest K' ρ δ X wsT then 1 else 0) → σ'.sc (s0 + 49) = (if pgTest K' ρ δ X wsT then 1 else 0) ∧
        σ'.draws = σ.draws + pgMT δ * (pgNT d ρ * d) ∧
        Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0 ++ [n0 + 13, n0 + 15])
          (pgTmpS s0 ++ [s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 49,
            s0 + 51])
          [a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 11, a0 + 15, a0 + 16, a0 + 17, a0 + 18] := by
    intro σ' hF hv
    refine ⟨hv, ?_, ?_⟩
    · rw [hF.2.2.2.1, hF8.2.2.2.1, hdr7]
    · have hF8' : Env.Frame σ7 σ' [] [s0 + 1, s0 + 45, s0 + 49] [] :=
        Env.Frame.trans hF8 (Env.Frame.mono hF (by simp) (by simp) (by simp))
      exact frameD_trans hF7 (frameD_of_frame (Env.Frame.mono hF8' (by simp) (by simp [pgTmpS]) (by simp)))
  have hcount := pgTest_count K' ρ δ X wsT
  by_cases hc : σ8.sc (s0 + 45) < σ8.sc (s0 + 40)
  · refine runs_mono (runs_ifS_t (by omega) (by omega) hc (runs_sconst (by omega) 1)) le_rfl ?_
    rintro σ' rfl
    have hT : pgTest K' ρ δ X wsT := hcount.1 (by rw [h45, h40] at hc; exact hc)
    exact hfin _ (Env.Frame.setSc (Env.Frame.refl σ8 _ _ _) (by simp) _) (by simp [hT])
  · refine runs_mono (runs_ifS_f (by omega) (by omega) hc (runs_skip σ8)) le_rfl ?_
    rintro σ' rfl
    have hT : ¬ pgTest K' ρ δ X wsT := fun hT => hc (by rw [h45, h40]; exact hcount.2 hT)
    exact hfin _ (Env.Frame.refl σ8 _ _ _) (by simp [σ8, hT])

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

/-! ## One repeat -/

open Classical in
/-- One repeat at the ratio `ρ`: the descent on the next `N` vectors, the test on the `m_T n_T` after them, and the
average kept in `a0 + 19`, `a0 + 20` with `found := 1` if none was kept before and the test passes. -/
theorem runs_pgRep {L : Layout} {w : World d} {dv one n0 s0 a0 muv Av : ℕ} {ρ δ : ℝ} {P : PgSp d}
    (hL : PgLeaves) (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN)
    (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d)
    (h1 : σ.nat one = 1) (hmuv : muv < L.NA) (hAv : Av < L.NA) (hmub : muv < a0 ∨ a0 + 32 ≤ muv)
    (hAb : Av < a0 ∨ a0 + 32 ≤ Av) (hd1 : 1 ≤ d) (hρ1 : 1 ≤ ρ) (hV : PgStageVars σ n0 s0 ρ) (hP : PgAt σ muv Av P)
    (hmT : σ.nat (n0 + 14) = pgMT δ) (hf : σ.sc (s0 + 41) = 0 ∨ σ.sc (s0 + 41) = 1) :
    Runs L w (pgRep L dv one n0 s0 a0 muv Av) σ
      (kRep d (pgJb d ρ) (pgNs d ρ) (pgNT d ρ) (pgMT δ))
      (fun σ' =>
        let D := pgDescent (pgKi w.K (σ.sc (s0 + 42)) P) ρ (fun k => WithLp.toLp 2 fun c => w.gs (σ.draws + k * d + c))
        let T := pgTest (pgKi w.K (σ.sc (s0 + 42)) P) ρ δ D
          (fun v k => WithLp.toLp 2 fun c => w.gs (σ.draws + pgNs d ρ * d + (v * pgNT d ρ + k) * d + c))
        (σ.sc (s0 + 41) = 0 → T → σ'.sc (s0 + 41) = 1 ∧ PgAt σ' (a0 + 19) (a0 + 20) D) ∧
        (¬ (σ.sc (s0 + 41) = 0 ∧ T) → σ'.sc (s0 + 41) = σ.sc (s0 + 41) ∧ σ'.arr (a0 + 19) = σ.arr (a0 + 19) ∧
          σ'.arr (a0 + 20) = σ.arr (a0 + 20)) ∧
        σ'.draws = σ.draws + (pgNs d ρ + pgMT δ * pgNT d ρ) * d ∧
        Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0 ++ [n0 + 13, n0 + 15])
          (pgTmpS s0 ++ [s0 + 31, s0 + 33, s0 + 34, s0 + 35, s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 41,
            s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 49, s0 + 51])
          [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12,
            a0 + 13, a0 + 14, a0 + 15, a0 + 16, a0 + 17, a0 + 18, a0 + 19, a0 + 20]) := by
  set K' := pgKi w.K (σ.sc (s0 + 42)) P with hK'
  set D := pgDescent K' ρ (fun k => WithLp.toLp 2 fun c => w.gs (σ.draws + k * d + c)) with hD
  set T := pgTest K' ρ δ D
    (fun v k => WithLp.toLp 2 fun c => w.gs (σ.draws + pgNs d ρ * d + (v * pgNT d ρ + k) * d + c)) with hT
  unfold pgRep kRep
  refine runs_seq (runs_pgDesc hL σ hn0 hs0 ha0 hdv hone hdvb honeb hd h1 hmuv hAv hmub hAb hd1 hρ1 hV hP)
    fun σ1 h1' => ?_
  obtain ⟨hX1, hdr1, hF1⟩ := h1'
  rw [← hK', ← hD] at hX1
  have hFn1 : ∀ k, k ∉ pgTmpN n0 ++ [n0 + 13] → σ1.nat k = σ.nat k := fun k hk => hF1.1 k hk
  have hFs1 : ∀ x, x ∉ pgTmpS s0 ++ [s0 + 31, s0 + 33, s0 + 34, s0 + 35, s0 + 36, s0 + 45] → σ1.sc x = σ.sc x :=
    fun x hx => hF1.2.1 x hx
  have hV1 := hV.of_frame hF1 (by simp [pgTmpN] <;> omega) (by simp [pgTmpS] <;> omega)
  have hP1 := hP.of_frame hF1 (by simp <;> omega) (by simp <;> omega)
  refine runs_seq (runs_pgTestC hL (δ := δ) σ1 hn0 hs0 ha0 hdv hone hdvb honeb
    ((hFn1 _ (by simp [pgTmpN] <;> omega)).trans hd) ((hFn1 _ (by simp [pgTmpN] <;> omega)).trans h1) hmuv hAv hmub hAb
    hV1 hP1 hX1 ((hFn1 _ (by simp [pgTmpN])).trans hmT)) fun σ2 h2 => ?_
  obtain ⟨hpass, hdr2, hF2⟩ := h2
  rw [hFs1 _ (by simp [pgTmpS]), ← hK', hdr1] at hpass
  rw [← hT] at hpass
  have hF12 : Env.Frame σ { σ2 with draws := σ.draws } (pgTmpN n0 ++ [n0 + 13, n0 + 15])
      (pgTmpS s0 ++ [s0 + 31, s0 + 33, s0 + 34, s0 + 35, s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 41,
        s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 49, s0 + 51])
      [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12,
        a0 + 13, a0 + 14, a0 + 15, a0 + 16, a0 + 17, a0 + 18, a0 + 19, a0 + 20] :=
    frameD_trans (Env.Frame.mono hF1 (fun i hi => List.mem_append.2 ((List.mem_append.1 hi).imp id (fun h => by simp at h ⊢; omega)))
        (fun x hx => List.mem_append.2 ((List.mem_append.1 hx).imp id (fun h => by simp at h ⊢; omega)))
        (fun b hb => by simp at hb ⊢; omega))
      (Env.Frame.mono hF2 (fun i hi => hi)
        (fun x hx => List.mem_append.2 ((List.mem_append.1 hx).imp id (fun h => by simp at h ⊢; omega)))
        (fun b hb => by simp at hb ⊢; omega))
  have h41 : σ2.sc (s0 + 41) = σ.sc (s0 + 41) := by
    rw [hF2.2.1 _ (by simp [pgTmpS] <;> omega), hFs1 _ (by simp [pgTmpS] <;> omega)]
  have h19 : σ2.arr (a0 + 19) = σ.arr (a0 + 19) := by
    rw [hF2.2.2.1 _ (by simp), hF1.2.2.1 _ (by simp)]
  have h20 : σ2.arr (a0 + 20) = σ.arr (a0 + 20) := by
    rw [hF2.2.2.1 _ (by simp), hF1.2.2.1 _ (by simp)]
  have hX2 := hX1.of_frame hF2 (by simp) (by simp)
  have hdr2' : σ2.draws = σ.draws + (pgNs d ρ + pgMT δ * pgNT d ρ) * d := by rw [hdr2, hdr1]; ring
  have hd2 : σ2.nat dv = d := by
    rw [hF2.1 _ (by simp [pgTmpN] <;> omega), hFn1 _ (by simp [pgTmpN] <;> omega)]; exact hd
  have h12 : σ2.nat one = 1 := by
    rw [hF2.1 _ (by simp [pgTmpN] <;> omega), hFn1 _ (by simp [pgTmpN] <;> omega)]; exact h1
  have hdd2 : σ2.nat (n0 + 9) = d * d := by
    rw [hF2.1 _ (by simp [pgTmpN]), hFn1 _ (by simp [pgTmpN])]; exact hV.1
  -- the keep
  refine runs_seq_eq (runs_sconst (by omega) 0) ?_
  refine runs_seq_eq (runs_sconst (by omega) 1) ?_
  set σ3 := (σ2.setSc s0 ((0 : ℚ) : ℝ)).setSc (s0 + 2) ((1 : ℚ) : ℝ) with hσ3
  have hF3 : Env.Frame σ2 σ3 [] [s0, s0 + 2] [] :=
    Env.Frame.setSc (Env.Frame.setSc (Env.Frame.refl σ2 _ _ _) (by simp) _) (by simp) _
  have e0 : σ3.sc s0 = 0 := by simp [σ3]
  have e2 : σ3.sc (s0 + 2) = 1 := by simp [σ3]
  have e41 : σ3.sc (s0 + 41) = σ.sc (s0 + 41) := by rw [hF3.2.1 _ (by simp), h41]
  have e49 : σ3.sc (s0 + 49) = if T then 1 else 0 := by rw [hF3.2.1 _ (by simp), hpass]
  have hfin : ∀ σ' : Env d, Env.Frame σ3 σ' [n0] [s0 + 8, s0 + 41] [a0 + 19, a0 + 20] →
      (σ.sc (s0 + 41) = 0 → T → σ'.sc (s0 + 41) = 1 ∧ PgAt σ' (a0 + 19) (a0 + 20) D) →
      (¬ (σ.sc (s0 + 41) = 0 ∧ T) → σ'.sc (s0 + 41) = σ.sc (s0 + 41) ∧ σ'.arr (a0 + 19) = σ.arr (a0 + 19) ∧
          σ'.arr (a0 + 20) = σ.arr (a0 + 20)) →
      (σ.sc (s0 + 41) = 0 → T → σ'.sc (s0 + 41) = 1 ∧ PgAt σ' (a0 + 19) (a0 + 20) D) ∧
        (¬ (σ.sc (s0 + 41) = 0 ∧ T) → σ'.sc (s0 + 41) = σ.sc (s0 + 41) ∧ σ'.arr (a0 + 19) = σ.arr (a0 + 19) ∧
          σ'.arr (a0 + 20) = σ.arr (a0 + 20)) ∧
        σ'.draws = σ.draws + (pgNs d ρ + pgMT δ * pgNT d ρ) * d ∧
        Env.Frame σ { σ' with draws := σ.draws } (pgTmpN n0 ++ [n0 + 13, n0 + 15])
          (pgTmpS s0 ++ [s0 + 31, s0 + 33, s0 + 34, s0 + 35, s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 41,
            s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 49, s0 + 51])
          [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12,
            a0 + 13, a0 + 14, a0 + 15, a0 + 16, a0 + 17, a0 + 18, a0 + 19, a0 + 20] := by
    intro σ' hF hA hB
    refine ⟨hA, hB, ?_, ?_⟩
    · rw [hF.2.2.2.1, hF3.2.2.2.1, hdr2']
    · have hF' : Env.Frame σ2 σ' [n0] [s0, s0 + 2, s0 + 8, s0 + 41] [a0 + 19, a0 + 20] :=
        Env.Frame.trans (Env.Frame.mono hF3 (by simp) (by simp) (by simp)) (Env.Frame.mono hF (by simp) (by simp) (by simp))
      exact frameD_trans hF12 (frameD_of_frame (Env.Frame.mono hF' (by simp [pgTmpN]) (by simp [pgTmpS]) (by simp)))
  have h19' : σ3.arr (a0 + 19) = σ.arr (a0 + 19) := by rw [hF3.2.2.1 _ (by simp), h19]
  have h20' : σ3.arr (a0 + 20) = σ.arr (a0 + 20) := by rw [hF3.2.2.1 _ (by simp), h20]
  rcases hf with hf0 | hf1
  · -- nothing kept before
    have hc1 : σ3.sc (s0 + 41) < σ3.sc (s0 + 2) := by rw [e41, e2, hf0]; norm_num
    by_cases hTp : T
    · have hc2 : σ3.sc s0 < σ3.sc (s0 + 49) := by rw [e0, e49, if_pos hTp]; norm_num
      refine runs_ifS_t (by omega) (by omega) hc1 (runs_ifS_t (by omega) (by omega) hc2
        (runs_seq_eq (runs_sconst (by omega) 1) (runs_seq (runs_vcopy _ hdv hone (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by rw [Env.setSc_nat, hF3.1 _ (by simp)]; exact hd2)
          (by rw [Env.setSc_nat, hF3.1 _ (by simp)]; exact h12)) fun σ4 h4 => ?_)))
      obtain ⟨hv4, hF4, -⟩ := h4
      refine runs_mono (runs_mcopy σ4 (by omega) hone (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by rw [hF4.1 _ (by simp <;> omega), Env.setSc_nat, hF3.1 _ (by simp)]; exact hdd2)
        (by rw [hF4.1 _ (by simp <;> omega), Env.setSc_nat, hF3.1 _ (by simp)]; exact h12)) le_rfl ?_
      rintro σ5 ⟨hm5, hF5, -⟩
      have hF35 : Env.Frame σ3 σ5 [n0] [s0 + 8, s0 + 41] [a0 + 19, a0 + 20] :=
        Env.Frame.trans (Env.Frame.setSc (Env.Frame.refl σ3 _ _ _) (by simp) _)
          (Env.Frame.trans (Env.Frame.mono hF4 (by simp) (by simp) (by simp))
            (Env.Frame.mono hF5 (by simp) (by simp) (by simp)))
      refine hfin σ5 hF35 (fun _ _ => ⟨?_, ?_, ?_⟩) (fun h => absurd ⟨hf0, hTp⟩ h)
      · rw [hF5.2.1 _ (by simp), hF4.2.1 _ (by simp)]; simp
      · rw [Env.vec_of_arr (hF5.2.2.1 _ (by simp)), hv4]
        exact hX2.1
      · rw [hm5, Env.mat_of_arr (hF4.2.2.1 _ (by simp))]
        exact hX2.2
    · have hc2 : ¬ σ3.sc s0 < σ3.sc (s0 + 49) := by rw [e0, e49, if_neg hTp]; norm_num
      refine runs_mono (runs_ifS_t (by omega) (by omega) hc1 (runs_ifS_f (by omega) (by omega) hc2 (runs_skip σ3)))
        (by omega) ?_
      rintro σ' rfl
      exact hfin σ3 (Env.Frame.refl σ3 _ _ _) (fun _ h => absurd h hTp) (fun _ => ⟨e41, h19', h20'⟩)
  · -- a repeat was kept before
    have hc1 : ¬ σ3.sc (s0 + 41) < σ3.sc (s0 + 2) := by rw [e41, e2, hf1]; norm_num
    refine runs_mono (runs_ifS_f (by omega) (by omega) hc1 (runs_skip σ3)) (by omega) ?_
    rintro σ' rfl
    exact hfin σ3 (Env.Frame.refl σ3 _ _ _) (fun h => by rw [hf1] at h; norm_num at h) (fun _ => ⟨e41, h19', h20'⟩)

end AdversarialBco.Poly.PG
