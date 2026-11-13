/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2PropGTools
public import AdversarialBco.Poly.Df2ApMeasProof
public import AdversarialBco.Poly.PgMeasProof
public import AdversarialBco.Poly.PgLemmasProof

@[expose] public section

/-!
# DF2-O: one round of D0 at a good position

One round of the learner with a general gauge (`df2RoundGa`): the point played from a state (`rX`, `rPt`, `rPoint`),
the round from the modes `run` and `guard` (`roundGa_run`, `roundGa_guard`), and the line of DF2-O never returns the
mode `off` (`df2NextAP_ne_off`). At a good position (`GoodPos`: `B̄(0, 1) ⊆ S(K) ⊆ B̄(0, R)`), with a gauge at least
the exact one, a round from a mode other than `off` plays a point of the interior of `K` and does not reach `off`
(`round_good`).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix ENNReal

namespace AdversarialBco.Poly.PropG

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly ApMeas

variable {d : ℕ}

/-! ## 1. One round -/

/-- The sample `X = μ + (1 - λ) A ξ` of a round in the mode `run st`. -/
noncomputable def rX (p : Df2OPar) (st : Df2St d) (ξ : Fin d → ℝ) : Fin d → ℝ := st.mu + (1 - p.lam) • (st.A *ᵥ ξ)

/-- The gauge factor `max (1, ga(X)/(1 - ε))`. -/
noncomputable def rPt (p : Df2OPar) (ga : E d → ℝ) (st : Df2St d) (ξ : Fin d → ℝ) : ℝ :=
  max 1 (ga (WithLp.toLp 2 (rX p st ξ)) / (1 - p.eps))

/-- The point `S⁻¹(X/pt)` of a round in the mode `run st`. -/
noncomputable def rPoint (p : Df2OPar) (Ps : PgSp d) (ga : E d → ℝ) (st : Df2St d) (ξ : Fin d → ℝ) : E d :=
  pgMu Ps + pgOp Ps (WithLp.toLp 2 ((rPt p ga st ξ)⁻¹ • rX p st ξ))

open Classical in
theorem roundGa_run (p : Df2OPar) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ga : E d → ℝ) (ap : ApFun d)
    (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ) (st : Df2St d) :
    df2RoundGa p n K Ps ga ap ft nt ξ ζ (.run st) =
      if rPoint p Ps ga st ξ ∈ K then
        (rPoint p Ps ga st ξ, df2NextAP ap p n (df2Keps K Ps p.R p.eps) st ξ (st.A *ᵥ ξ)
          (rPt p ga st ξ * (ft (rPoint p Ps ga st ξ) + nt + ζ) / 2 + 2 * (rPt p ga st ξ - 1) / p.eps))
      else (0, .off) := rfl

open Classical in
theorem roundGa_guard (p : Df2OPar) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ga : E d → ℝ) (ap : ApFun d)
    (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ) :
    df2RoundGa p n K Ps ga ap ft nt ξ ζ .guard =
      if pgMu Ps + pgOp Ps 0 ∈ K then (pgMu Ps + pgOp Ps 0, Df2Mode.guard) else (0, Df2Mode.off) := rfl

theorem guard_ne_off : (Df2Mode.guard : Df2Mode d) ≠ .off := nofun

theorem run_ne_off (st : Df2St d) : Df2Mode.run st ≠ .off := nofun

theorem elim_ne_off {α : Type*} {o : Option α} {g : α → Df2Mode d} (hg : ∀ x, g x ≠ .off) :
    o.elim Df2Mode.guard g ≠ .off := by
  cases o with
  | none => exact guard_ne_off
  | some x => exact hg x

/-- The rest of a round never switches the learner off. -/
theorem df2NextAP_ne_off (ap : ApFun d) (p : Df2OPar) (n : ℕ) (Keps : Set (Fin d → ℝ)) (st : Df2St d)
    (ξ w : Fin d → ℝ) (Y : ℝ) : df2NextAP ap p n Keps st ξ w Y ≠ .off := by
  rw [nextE_eq]
  unfold nextE
  dsimp only
  split_ifs <;> try exact guard_ne_off
  all_goals
    refine elim_ne_off fun pt => ?_
    split_ifs <;> first | exact guard_ne_off | exact run_ne_off _ | exact elim_ne_off fun mu => run_ne_off _

attribute [local fun_prop] measurable_st_mu measurable_st_A

/-! ## 2. A good position -/

/-- The conclusion of `PgGood` for the position `Ps`. -/
structure GoodPos (K : Set (E d)) (R : ℝ) (Ps : PgSp d) : Prop where
  det : (pgMat Ps).det ≠ 0
  ball : Metric.closedBall 0 1 ⊆ posBody K (pgMu Ps) (pgOp Ps)
  sub : posBody K (pgMu Ps) (pgOp Ps) ⊆ Metric.closedBall 0 R

theorem kp_eq {K : Set (E d)} {R : ℝ} {Ps : PgSp d} (h : GoodPos K R Ps) :
    df2Kp K Ps R = posBody K (pgMu Ps) (pgOp Ps) :=
  kp_eq_posBody K Ps R h.sub

theorem kp_ball {K : Set (E d)} {R : ℝ} {Ps : PgSp d} (h : GoodPos K R Ps) :
    Metric.closedBall 0 1 ⊆ df2Kp K Ps R := by
  rw [kp_eq h]; exact h.ball

theorem zero_mem_interior_posBody {K : Set (E d)} {R : ℝ} {Ps : PgSp d} (h : GoodPos K R Ps) :
    (0 : E d) ∈ interior (posBody K (pgMu Ps) (pgOp Ps)) :=
  interior_mono h.ball (mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds 0 one_pos))

/-- The sample divided by its gauge factor lies in `(1 - ε) K'` and its point in the interior of `K`. -/
theorem rPoint_good (p : Df2OPar) {K : Set (E d)} (hK : Convex ℝ K) (hKc : IsClosed K) {Ps : PgSp d}
    (hP : GoodPos K p.R Ps) (hε : 0 < p.eps) (hε1 : p.eps < 1) (ga : E d → ℝ)
    (hga : ∀ x, gauge (df2Kp K Ps p.R) x ≤ ga x) (st : Df2St d) (ξ : Fin d → ℝ) :
    (1 - p.eps)⁻¹ • ((rPt p ga st ξ)⁻¹ • (WithLp.toLp 2 (rX p st ξ) : E d)) ∈ df2Kp K Ps p.R ∧
      rPoint p Ps ga st ξ ∈ interior K := by
  have hc := kp_convex_of K hK Ps p.R
  have h1 := kp_ball hP
  have hg := gauge_pt_le (df2Kp K Ps p.R) hc h1 p.eps hε hε1 (WithLp.toLp 2 (rX p st ξ))
    (ga (WithLp.toLp 2 (rX p st ξ))) (hga _)
  refine ⟨gauge_smul_mem _ hc (kp_closed_of K hKc Ps p.R) h1 p.eps hε1 _ hg, ?_⟩
  have hi : (rPt p ga st ξ)⁻¹ • (WithLp.toLp 2 (rX p st ξ) : E d) ∈ interior (df2Kp K Ps p.R) :=
    gauge_lt_one_interior _ hc h1 _ (hg.trans_lt (by linarith))
  rw [kp_eq hP] at hi
  exact posBody_interior K Ps hP.det _ hi

/-- On a good position, a round from a mode other than `off`, with a gauge at least the exact one, plays a point of
the interior of `K` and does not switch off. -/
theorem round_good (p : Df2OPar) (n : ℕ) {K : Set (E d)} (hK : Convex ℝ K) (hKc : IsClosed K) {Ps : PgSp d}
    (hP : GoodPos K p.R Ps) (hε : 0 < p.eps) (hε1 : p.eps < 1) (ga : E d → ℝ)
    (hga : ∀ x, gauge (df2Kp K Ps p.R) x ≤ ga x) (ap : ApFun d) (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ)
    {m : Df2Mode d} (hm : m ≠ .off) :
    (df2RoundGa p n K Ps ga ap ft nt ξ ζ m).1 ∈ interior K ∧ (df2RoundGa p n K Ps ga ap ft nt ξ ζ m).2 ≠ .off := by
  classical
  cases m with
  | off => exact absurd rfl hm
  | guard =>
    have h0 : pgMu Ps + pgOp Ps 0 ∈ interior K := posBody_interior K Ps hP.det 0 (zero_mem_interior_posBody hP)
    rw [roundGa_guard, ite_eq_left (interior_subset h0)]
    exact ⟨h0, guard_ne_off⟩
  | run st =>
    have hx := (rPoint_good p hK hKc hP hε hε1 ga hga st ξ).2
    rw [roundGa_run, ite_eq_left (interior_subset hx)]
    exact ⟨hx, df2NextAP_ne_off _ _ _ _ _ _ _ _⟩

end AdversarialBco.Poly.PropG
