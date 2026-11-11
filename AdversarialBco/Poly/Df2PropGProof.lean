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
# PO Lemma TV and Proposition G for DF2-O

Proof of `Df2PropG` of `Df2Layer2.lean` (theorem `df2PropG`), by the hybrid argument,
with no Pinsker inequality.

* The hybrid `H_k` runs the rounds `t < k` with the bisection gauge `π~` and the rounds `t ≥ k` with the exact gauge,
  on the same world; `Φ_k` sums the losses at the points the exact gauge plays from the modes of `H_k`. `H_0` is D0,
  and on the case of the analysis the regret of DJ is at most `Φ_n - inf + n R η/ε` (Lemma G (iii)).
* One step `H_k → H_{k+1}` costs `η (R + 7)/ε` in probability: resample the dither of round `k` (`world_resample`);
  nothing else reads it before round `k + 1`, and the observation of round `k` is affine in it, with the two gauges
  giving two affine maps whose one-dimensional laws differ by at most the bound of `gauss_affine_le`.
* The events are measurable: on the case of the analysis every loss is read in the interior of `K`, where it is
  continuous, and the exact gauge is the rational infimum of `gauge_eq_iInf_rat`; the hybrids are run with these
  measurable versions (`fT`, `gR`), which agree with the true ones on the case.
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

theorem roundGa_off (p : Df2OPar) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ga : E d → ℝ) (ap : ApFun d)
    (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ) :
    df2RoundGa p n K Ps ga ap ft nt ξ ζ .off = (0, .off) := rfl

open Classical in
theorem roundGa_guard (p : Df2OPar) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ga : E d → ℝ) (ap : ApFun d)
    (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ) :
    df2RoundGa p n K Ps ga ap ft nt ξ ζ .guard =
      if pgMu Ps + pgOp Ps 0 ∈ K then (pgMu Ps + pgOp Ps 0, Df2Mode.guard) else (0, Df2Mode.off) := rfl

/-- The point of a round reads neither the loss, nor the noise, nor the dither. -/
theorem roundGa_fst (p : Df2OPar) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ga : E d → ℝ) (ap : ApFun d)
    (ft ft' : E d → ℝ) (nt nt' : ℝ) (ξ : Fin d → ℝ) (ζ ζ' : ℝ) (m : Df2Mode d) :
    (df2RoundGa p n K Ps ga ap ft nt ξ ζ m).1 = (df2RoundGa p n K Ps ga ap ft' nt' ξ ζ' m).1 := by
  cases m with
  | off => rfl
  | guard => rfl
  | run st =>
    rw [roundGa_run, roundGa_run]
    split_ifs <;> rfl

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

/-! ## 2. Measurability of one round -/

open Classical in
theorem roundGa_code (p : Df2OPar) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ga : E d → ℝ) (ap : ApFun d)
    (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ) (m : Df2Mode d) :
    df2RoundGa p n K Ps ga ap ft nt ξ ζ m =
      if m.code.1 = 0 then ((0 : E d), Df2Mode.off)
      else if m.code.1 = 1 then df2RoundGa p n K Ps ga ap ft nt ξ ζ .guard
      else df2RoundGa p n K Ps ga ap ft nt ξ ζ (.run m.code.2) := by
  cases m <;> simp [Df2Mode.code, roundGa_off]

attribute [local fun_prop] measurable_st_mu measurable_st_A

theorem meas_roundGa {X : Type*} [MeasurableSpace X] (p : Df2OPar) (n : ℕ) (K : Set (E d)) (hK : IsClosed K)
    {Ps : X → PgSp d} (hPs : Measurable Ps) {ga : X → E d → ℝ} (hga : Measurable fun q : X × E d => ga q.1 q.2)
    {F : X → E d → ℝ} (hF : Measurable fun q : X × E d => F q.1 q.2) {nt ζ : X → ℝ} (hnt : Measurable nt)
    (hζ : Measurable ζ) {ξ : X → Fin d → ℝ} (hξ : Measurable ξ) {m : X → Df2Mode d} (hm : Measurable m) :
    Measurable fun x => df2RoundGa p n K (Ps x) (ga x) apCall (F x) (nt x) (ξ x) (ζ x) (m x) := by
  classical
  have hc : Measurable fun x => (m x).code := measurable_mode_code.comp hm
  have hst : Measurable fun x => (m x).code.2 := measurable_snd.comp hc
  have htag : Measurable fun x => (m x).code.1 := measurable_fst.comp hc
  have hpos : Measurable fun q : PgSp d × E d => pgMu q.1 + pgOp q.1 q.2 := (pg_continuous d).2.2.measurable
  have htoLp : Measurable fun v : Fin d → ℝ => (WithLp.toLp 2 v : E d) := (PiLp.continuous_toLp 2 _).measurable
  rw [funext fun x => roundGa_code p n K (Ps x) (ga x) apCall (F x) (nt x) (ξ x) (ζ x) (m x)]
  refine Measurable.ite (htag (measurableSet_singleton 0)) measurable_const
    (Measurable.ite (htag (measurableSet_singleton 1)) ?_ ?_)
  · simp only [roundGa_guard]
    have h0 : Measurable fun x => pgMu (Ps x) + pgOp (Ps x) 0 := hpos.comp (hPs.prodMk measurable_const)
    exact Measurable.ite (hK.measurableSet.preimage h0) (h0.prodMk measurable_const) measurable_const
  · simp only [roundGa_run]
    have hX : Measurable fun x => rX p (m x).code.2 (ξ x) := by
      unfold rX; fun_prop
    have hPt : Measurable fun x => rPt p (ga x) (m x).code.2 (ξ x) := by
      unfold rPt
      exact measurable_const.max ((hga.comp (measurable_id.prodMk (htoLp.comp hX))).div_const _)
    have hPoint : Measurable fun x => rPoint p (Ps x) (ga x) (m x).code.2 (ξ x) := by
      unfold rPoint
      exact hpos.comp (hPs.prodMk (htoLp.comp (hPt.inv.smul hX)))
    have hY : Measurable fun x => rPt p (ga x) (m x).code.2 (ξ x) *
        (F x (rPoint p (Ps x) (ga x) (m x).code.2 (ξ x)) + nt x + ζ x) / 2 +
          2 * (rPt p (ga x) (m x).code.2 (ξ x) - 1) / p.eps := by
      have hFx : Measurable fun x => F x (rPoint p (Ps x) (ga x) (m x).code.2 (ξ x)) :=
        hF.comp (measurable_id.prodMk hPoint)
      fun_prop
    have hN : Measurable fun x => df2NextAP apCall p n (df2Keps K (Ps x) p.R p.eps) (m x).code.2 (ξ x)
        ((m x).code.2.A *ᵥ ξ x) (rPt p (ga x) (m x).code.2 (ξ x) *
          (F x (rPoint p (Ps x) (ga x) (m x).code.2 (ξ x)) + nt x + ζ x) / 2 +
            2 * (rPt p (ga x) (m x).code.2 (ξ x) - 1) / p.eps) :=
      (df2NextAP_measurable p n (fun P => df2Keps K P p.R p.eps) (keps_graph K hK p.R p.eps)).comp
        (hPs.prodMk (hst.prodMk (hξ.prodMk hY)))
    exact Measurable.ite (hK.measurableSet.preimage hPoint) (hPoint.prodMk hN) measurable_const

/-! ## 3. A good position -/

/-- The conclusion of `PgGood` for the position `Ps`. -/
structure GoodPos (K : Set (E d)) (R : ℝ) (Ps : PgSp d) : Prop where
  det : (pgMat Ps).det ≠ 0
  ball : Metric.closedBall 0 1 ⊆ posBody K (pgMu Ps) (pgOp Ps)
  sub : posBody K (pgMu Ps) (pgOp Ps) ⊆ Metric.closedBall 0 R

theorem kp_convex {K : Set (E d)} (hK : Convex ℝ K) (Ps : PgSp d) (R : ℝ) : Convex ℝ (df2Kp K Ps R) :=
  kp_convex_of K hK Ps R

theorem kp_closed {K : Set (E d)} (hK : IsClosed K) (Ps : PgSp d) (R : ℝ) : IsClosed (df2Kp K Ps R) :=
  kp_closed_of K hK Ps R

theorem kp_sub (K : Set (E d)) (Ps : PgSp d) (R : ℝ) : df2Kp K Ps R ⊆ Metric.closedBall 0 R :=
  kp_sub_ball K Ps R

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

/-- In the mode `run st` on a good position, the point is in `K`, so the round is the observation and `df2NextAP`. -/
theorem round_good_run (p : Df2OPar) (n : ℕ) {K : Set (E d)} (hK : Convex ℝ K) (hKc : IsClosed K) {Ps : PgSp d}
    (hP : GoodPos K p.R Ps) (hε : 0 < p.eps) (hε1 : p.eps < 1) (ga : E d → ℝ)
    (hga : ∀ x, gauge (df2Kp K Ps p.R) x ≤ ga x) (ap : ApFun d) (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ)
    (st : Df2St d) :
    df2RoundGa p n K Ps ga ap ft nt ξ ζ (.run st) =
      (rPoint p Ps ga st ξ, df2NextAP ap p n (df2Keps K Ps p.R p.eps) st ξ (st.A *ᵥ ξ)
          (rPt p ga st ξ * (ft (rPoint p Ps ga st ξ) + nt + ζ) / 2 + 2 * (rPt p ga st ξ - 1) / p.eps)) := by
  classical
  rw [roundGa_run, ite_eq_left (interior_subset (rPoint_good p hK hKc hP hε hε1 ga hga st ξ).2)]

/-- The round only reads the loss in the interior of `K`, on a good position. -/
theorem round_congr_ft (p : Df2OPar) (n : ℕ) {K : Set (E d)} (hK : Convex ℝ K) (hKc : IsClosed K) {Ps : PgSp d}
    (hP : GoodPos K p.R Ps) (hε : 0 < p.eps) (hε1 : p.eps < 1) (ga : E d → ℝ)
    (hga : ∀ x, gauge (df2Kp K Ps p.R) x ≤ ga x) (ap : ApFun d) (ft ft' : E d → ℝ)
    (hft : ∀ x ∈ interior K, ft x = ft' x) (nt : ℝ) (ξ : Fin d → ℝ) (ζ : ℝ) (m : Df2Mode d) :
    df2RoundGa p n K Ps ga ap ft nt ξ ζ m = df2RoundGa p n K Ps ga ap ft' nt ξ ζ m := by
  cases m with
  | off => rfl
  | guard => rfl
  | run st =>
    rw [round_good_run p n hK hKc hP hε hε1 ga hga, round_good_run p n hK hKc hP hε hε1 ga hga,
      hft _ (rPoint_good p hK hKc hP hε hε1 ga hga st ξ).2]

/-- The two gauges at the sample of a round in the mode `run st`, and the losses at their points (Lemma G (iii)). -/
theorem pts_cmp (p : Df2OPar) {K : Set (E d)} (hK : Convex ℝ K) (hKc : IsClosed K) {Ps : PgSp d}
    (hP : GoodPos K p.R Ps) (hε : 0 < p.eps) (hε1 : p.eps < 1) {η : ℝ} (hη : 0 ≤ η) (gJ : E d → ℝ)
    (hJ1 : ∀ x, gauge (df2Kp K Ps p.R) x ≤ gJ x) (hJ2 : ∀ x, gJ x ≤ (1 + η) * gauge (df2Kp K Ps p.R) x)
    (st : Df2St d) (ξ : Fin d → ℝ) (f : E d → ℝ) (hf : AdmLoss K f) :
    1 ≤ rPt p (gauge (df2Kp K Ps p.R)) st ξ ∧ rPt p (gauge (df2Kp K Ps p.R)) st ξ ≤ rPt p gJ st ξ ∧
      rPt p gJ st ξ ≤ (1 + η) * rPt p (gauge (df2Kp K Ps p.R)) st ξ ∧
      |f (rPoint p Ps gJ st ξ) - f (rPoint p Ps (gauge (df2Kp K Ps p.R)) st ξ)| ≤
        p.R * (rPt p gJ st ξ / rPt p (gauge (df2Kp K Ps p.R)) st ξ - 1) / p.eps := by
  set Kp := df2Kp K Ps p.R with hKp
  set X : E d := WithLp.toLp 2 (rX p st ξ) with hX
  have hpp := pt_pip (gauge Kp X) (gJ X) p.eps η hε1 (gauge_nonneg X) (hJ1 X) (hJ2 X) hη
  refine ⟨hpp.1, hpp.2.1, hpp.2.2, ?_⟩
  have hF : ConvexOn ℝ Kp (fun y => f (pgMu Ps + pgOp Ps y)) := by
    rw [hKp, kp_eq hP]; exact convexOn_posBody K _ _ f hf.1
  have hF01 : ∀ y ∈ Kp, f (pgMu Ps + pgOp Ps y) ∈ Set.Icc (0 : ℝ) 1 := fun y hy =>
    hf.2 _ (by rw [hKp, kp_eq hP] at hy; exact hy)
  have hlip : ∀ a b : E d, (1 - p.eps)⁻¹ • a ∈ Kp → (1 - p.eps)⁻¹ • b ∈ Kp →
      f (pgMu Ps + pgOp Ps b) - f (pgMu Ps + pgOp Ps a) ≤ ‖b - a‖ / p.eps := fun a b ha hb =>
    convex_lip_eps Kp (kp_convex_of K hK Ps p.R) (kp_ball hP) _ hF hF01 p.eps hε hε1 a b ha hb
  have hmem0 := (rPoint_good p hK hKc hP hε hε1 (gauge Kp) (fun x => le_rfl) st ξ).1
  have hmemJ := (rPoint_good p hK hKc hP hε hε1 gJ hJ1 st ξ).1
  exact pts_lip Kp p.R (kp_sub_ball K Ps p.R) (fun y => f (pgMu Ps + pgOp Ps y)) p.eps hε hε1 hlip X _ _
    hpp.1 hpp.2.1 hmem0 hmemJ

/-! ## 4. The hybrids on the world -/

/-- The data of `Df2PropG` besides the dimension. -/
structure GCtx (d : ℕ) where
  n : ℕ
  r0 : ℝ
  R0 : ℝ
  δ : ℝ
  K : Set (E d)
  f : ℕ → E d → ℝ

/-- The outcomes `ω = (gs, noise)`. -/
abbrev Om : Type := (ℕ → ℝ) × (ℕ → ℝ)

namespace GCtx

variable (c : GCtx d)

/-- The hypotheses of `Df2PropG` on the data. -/
def Hyp : Prop := Df2WorldHyp d c.n c.r0 c.R0 c.δ c.K c.f

noncomputable def p : Df2OPar := df2oPar d c.n c.δ

def W (ω : Om) : World d := df2World c.K c.f ω

noncomputable def N0 : ℕ := df2oN0 d c.r0 c.R0 c.p.δ1

noncomputable def Ps (ω : Om) : PgSp d := df2oPs d c.n c.r0 c.R0 c.δ (c.W ω)

abbrev Kp (P : PgSp d) : Set (E d) := df2Kp c.K P c.p.R

open Classical in
/-- The exact gauge of `K'` as a rational infimum, a measurable function of the position and the point; it is the
gauge on a good position (`gauge_eq_iInf_rat`). -/
noncomputable def gR (P : PgSp d) (x : E d) : ℝ :=
  ⨅ q : ℚ, if 0 < q ∧ (q : ℝ)⁻¹ • x ∈ c.Kp P then (q : ℝ) else ‖x‖

/-- The bisection gauge of DJ. -/
noncomputable def gJ (P : PgSp d) : E d → ℝ := piTilde (c.Kp P) c.p.R c.p.j

open Classical in
/-- The loss of round `t < n` on the interior of `K`, `0` elsewhere and at the rounds `t ≥ n`. -/
noncomputable def fT (t : ℕ) : E d → ℝ := if t < c.n then (interior c.K).indicator (c.f t) else 0

noncomputable def xi (ω : Om) (t : ℕ) : Fin d → ℝ := df2oXi c.N0 ω.1 t

noncomputable def ze (ω : Om) (t : ℕ) : ℝ := df2oZeta d c.N0 ω.1 t

/-- Round `t` with the gauge `ga`, on the measurable versions of the losses. -/
noncomputable def rnd (ga : E d → ℝ) (ω : Om) (t : ℕ) (m : Df2Mode d) : E d × Df2Mode d :=
  df2RoundGa c.p c.n c.K (c.Ps ω) ga apCall (c.fT t) (ω.2 t) (c.xi ω t) (c.ze ω t) m

/-- The gauge of round `t` in the hybrid `H_k`. -/
noncomputable def hGa (k t : ℕ) (P : PgSp d) : E d → ℝ := if t < k then c.gJ P else c.gR P

noncomputable def mode0 (ω : Om) : Df2Mode d := df2oMode0 d c.n c.r0 c.R0 c.δ (c.W ω)

/-- The mode of the hybrid `H_k` before round `t`. -/
noncomputable def hMode (k : ℕ) (ω : Om) : ℕ → Df2Mode d
  | 0 => c.mode0 ω
  | t + 1 => (c.rnd (c.hGa k t (c.Ps ω)) ω t (hMode k ω t)).2

/-- The point the exact gauge plays from the mode of `H_k` before round `t`. -/
noncomputable def ePt (k : ℕ) (ω : Om) (t : ℕ) : E d := (c.rnd (c.gR (c.Ps ω)) ω t (c.hMode k ω t)).1

/-- `Φ_k`. -/
noncomputable def Phi (k : ℕ) (ω : Om) : ℝ := ∑ t ∈ Finset.range c.n, c.fT t (c.ePt k ω t)

noncomputable def c0 : ℝ := sInf ((fun y => ∑ t ∈ Finset.range c.n, c.f t y) '' c.K)

def Case (ω : Om) : Prop := Df2Case d c.n c.r0 c.R0 c.δ (c.W ω)

/-- The event `E_k` at the level `B`. -/
def Ev (B : ℝ) (k : ℕ) : Set Om := {ω | c.Case ω ∧ B < c.Phi k ω - c.c0}

/-- `η_g = R 2^{-j}`. -/
noncomputable def η : ℝ := c.p.R / 2 ^ c.p.j

/-! ### Parameters -/

variable {c}

theorem Hyp.hd (h : c.Hyp) : 1 ≤ d := h.1
theorem Hyp.hn (h : c.Hyp) : 1 ≤ c.n := h.2.1
theorem Hyp.hδ0 (h : c.Hyp) : 0 < c.δ := h.2.2.2.2.1
theorem Hyp.hδ1 (h : c.Hyp) : c.δ < 1 := h.2.2.2.2.2.1
theorem Hyp.closed (h : c.Hyp) : IsClosed c.K := h.2.2.2.2.2.2.1.isClosed
theorem Hyp.convex (h : c.Hyp) : Convex ℝ c.K := h.2.2.2.2.2.2.2.1
theorem Hyp.adv (h : c.Hyp) {t : ℕ} (ht : t < c.n) : AdmLoss c.K (c.f t) := h.2.2.2.2.2.2.2.2.2.2 t ht

theorem eps_pos (h : c.Hyp) : 0 < c.p.eps := par_eps_pos d c.n c.δ h.hd h.hn h.hδ0 h.hδ1

theorem one_le_R (h : c.Hyp) : 1 ≤ c.p.R := par_one_le_R d c.n c.δ h.hd

theorem δ1_pos (h : c.Hyp) : 0 < c.p.δ1 := par_δ1_pos d c.n c.δ h.hd h.hn h.hδ0

theorem δ1_le (h : c.Hyp) : c.p.δ1 ≤ 1 := par_δ1_le d c.n c.δ h.hδ1

theorem η_nonneg (h : c.Hyp) : 0 ≤ c.η := div_nonneg (zero_le_one.trans (one_le_R h)) (by positivity)

theorem param_sum (h : c.Hyp) : c.n * (c.η * (c.p.R + 7) / c.p.eps) ≤ c.p.δ1 :=
  par_sum d c.n c.δ h.hd h.hn h.hδ0 h.hδ1

/-! ### The case of the analysis -/

theorem case_pos {ω : Om} (hc : c.Case ω) : df2oPos d c.n c.r0 c.R0 c.δ (c.W ω) = some (c.Ps ω) := by
  obtain ⟨P, hP, -⟩ := hc.1
  simp only [Ps, df2oPs, hP, Option.getD_some]

theorem case_good {ω : Om} (hc : c.Case ω) : GoodPos c.K c.p.R (c.Ps ω) := by
  obtain ⟨P, hP, h1, h2, h3, -⟩ := hc.1
  have : c.Ps ω = P := by simp only [Ps, df2oPs, hP, Option.getD_some]
  rw [this]
  exact ⟨h1, h2, h3⟩

theorem case_eps {ω : Om} (hc : c.Case ω) : c.p.eps ≤ 1 / 2 := hc.2

theorem kp_good {ω : Om} (hc : c.Case ω) :
    Metric.closedBall 0 1 ⊆ c.Kp (c.Ps ω) := kp_ball (case_good hc)

theorem gR_eq (h : c.Hyp) {ω : Om} (hc : c.Case ω) : c.gR (c.Ps ω) = gauge (c.Kp (c.Ps ω)) := by
  funext x
  exact (PgMeas.gauge_eq_iInf_rat _ (kp_convex h.convex _ _) (kp_good hc) x).symm

theorem lemmaB_at (h : c.Hyp) {ω : Om} (hc : c.Case ω) (x : E d) :
    gauge (c.Kp (c.Ps ω)) x ≤ c.gJ (c.Ps ω) x ∧ c.gJ (c.Ps ω) x ≤ (1 + c.η) * gauge (c.Kp (c.Ps ω)) x := by
  have hB := lemmaB d (c.Kp (c.Ps ω)) c.p.R (one_le_R h) (kp_convex h.convex _ _) (kp_closed h.closed _ _)
    (kp_good hc) (kp_sub _ _ _) c.p.j c.η le_rfl x
  exact ⟨hB.1, hB.2.2⟩

theorem gJ_ge (h : c.Hyp) {ω : Om} (hc : c.Case ω) (x : E d) : gauge (c.Kp (c.Ps ω)) x ≤ c.gJ (c.Ps ω) x :=
  (lemmaB_at h hc x).1

theorem gJ_le (h : c.Hyp) {ω : Om} (hc : c.Case ω) (x : E d) :
    c.gJ (c.Ps ω) x ≤ (1 + c.η) * gauge (c.Kp (c.Ps ω)) x :=
  (lemmaB_at h hc x).2

theorem gR_ge (h : c.Hyp) {ω : Om} (hc : c.Case ω) (x : E d) : gauge (c.Kp (c.Ps ω)) x ≤ c.gR (c.Ps ω) x := by
  rw [gR_eq h hc]

theorem hGa_ge (h : c.Hyp) {ω : Om} (hc : c.Case ω) (k t : ℕ) (x : E d) :
    gauge (c.Kp (c.Ps ω)) x ≤ c.hGa k t (c.Ps ω) x := by
  unfold hGa
  split_ifs
  · exact gJ_ge h hc x
  · exact gR_ge h hc x

theorem mode0_ne_off {ω : Om} (hc : c.Case ω) : c.mode0 ω ≠ .off := by
  unfold mode0 df2oMode0
  rw [case_pos hc]
  split_ifs with h1
  · exact absurd h1 (not_lt.mpr (case_eps hc))
  · exact run_ne_off _

theorem eps_lt_one {ω : Om} (hc : c.Case ω) : c.p.eps < 1 := by linarith [case_eps hc]

theorem hMode_ne_off (h : c.Hyp) {ω : Om} (hc : c.Case ω) (k t : ℕ) : c.hMode k ω t ≠ .off := by
  induction t with
  | zero => exact mode0_ne_off hc
  | succ t ih =>
    exact (round_good c.p c.n h.convex h.closed (case_good hc) (eps_pos h) (eps_lt_one hc) _
      (hGa_ge h hc k t) apCall _ _ _ _ ih).2

theorem ePt_interior (h : c.Hyp) {ω : Om} (hc : c.Case ω) (k t : ℕ) : c.ePt k ω t ∈ interior c.K :=
  (round_good c.p c.n h.convex h.closed (case_good hc) (eps_pos h) (eps_lt_one hc) _
    (gR_ge h hc) apCall _ _ _ _ (hMode_ne_off h hc k t)).1

theorem fT_eq (t : ℕ) (ht : t < c.n) {x : E d} (hx : x ∈ interior c.K) : c.fT t x = c.f t x := by
  simp only [fT, ht, ↓reduceIte, Set.indicator_of_mem hx]

/-! ### The two ends -/

theorem hMode_zero (h : c.Hyp) {ω : Om} (hc : c.Case ω) (t : ℕ) (ht : t ≤ c.n) :
    c.hMode 0 ω t = df2zMode d c.n c.r0 c.R0 c.δ (c.W ω) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ht' : t < c.n := by omega
    have e1 : c.hMode 0 ω (t + 1) = (df2RoundGa c.p c.n c.K (c.Ps ω) (gauge (c.Kp (c.Ps ω))) apCall (c.fT t)
        (ω.2 t) (c.xi ω t) (c.ze ω t) (c.hMode 0 ω t)).2 := by
      simp only [hMode, rnd, hGa, Nat.not_lt_zero, ↓reduceIte, gR_eq h hc]
    have e2 : df2zMode d c.n c.r0 c.R0 c.δ (c.W ω) (t + 1) = (df2RoundGa c.p c.n c.K (c.Ps ω)
        (gauge (c.Kp (c.Ps ω))) apCall (c.f t) (ω.2 t) (c.xi ω t) (c.ze ω t)
        (df2zMode d c.n c.r0 c.R0 c.δ (c.W ω) t)).2 := by
      show (df2zRoundAt d c.n c.r0 c.R0 c.δ (c.W ω) (0 + t) _).2 = _
      rw [Nat.zero_add]
      rfl
    rw [e1, e2, ih ht'.le, round_congr_ft c.p c.n h.convex h.closed (case_good hc) (eps_pos h) (eps_lt_one hc)
      (gauge (c.Kp (c.Ps ω))) (fun x => le_rfl) apCall (c.fT t) (c.f t) (fun x hx => fT_eq t ht' hx)]

theorem ePt_zero (h : c.Hyp) {ω : Om} (hc : c.Case ω) (t : ℕ) (ht : t < c.n) :
    c.ePt 0 ω t = df2zPlay d c.n c.r0 c.R0 c.δ (c.W ω) t := by
  show (df2RoundGa c.p c.n c.K (c.Ps ω) (c.gR (c.Ps ω)) apCall (c.fT t) (ω.2 t) (c.xi ω t) (c.ze ω t)
    (c.hMode 0 ω t)).1 = (df2RoundGa c.p c.n c.K (c.Ps ω) (gauge (c.Kp (c.Ps ω))) apCall (c.f t) (ω.2 t)
      (c.xi ω t) (c.ze ω t) (df2zMode d c.n c.r0 c.R0 c.δ (c.W ω) t)).1
  rw [hMode_zero h hc t ht.le, gR_eq h hc]
  exact roundGa_fst _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem phi_zero (h : c.Hyp) {ω : Om} (hc : c.Case ω) :
    c.Phi 0 ω - c.c0 = regretPts c.K c.f (df2zPlay d c.n c.r0 c.R0 c.δ (c.W ω)) c.n := by
  unfold Phi regretPts c0
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' : t < c.n := Finset.mem_range.mp ht
  rw [fT_eq t ht' (ePt_interior h hc 0 t), ePt_zero h hc t ht']

theorem hMode_n (h : c.Hyp) {ω : Om} (hc : c.Case ω) (t : ℕ) (ht : t ≤ c.n) :
    c.hMode c.n ω t = df2oMode d c.n c.r0 c.R0 c.δ (c.W ω) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ht' : t < c.n := by omega
    have e1 : c.hMode c.n ω (t + 1) = (df2RoundGa c.p c.n c.K (c.Ps ω) (c.gJ (c.Ps ω)) apCall (c.fT t)
        (ω.2 t) (c.xi ω t) (c.ze ω t) (c.hMode c.n ω t)).2 := by
      simp only [hMode, rnd, hGa, ht', ↓reduceIte]
    have e2 : df2oMode d c.n c.r0 c.R0 c.δ (c.W ω) (t + 1) = (df2RoundGa c.p c.n c.K (c.Ps ω)
        (c.gJ (c.Ps ω)) apCall (c.f t) (ω.2 t) (c.xi ω t) (c.ze ω t)
        (df2oMode d c.n c.r0 c.R0 c.δ (c.W ω) t)).2 := by
      show (df2oRoundAt d c.n c.r0 c.R0 c.δ (c.W ω) (0 + t) _).2 = _
      rw [Nat.zero_add]
      exact congrArg Prod.snd (df2Round_eq_Ga _ _ _ _ _ _ _ _ _)
    rw [e1, e2, ih ht'.le, round_congr_ft c.p c.n h.convex h.closed (case_good hc) (eps_pos h) (eps_lt_one hc) _
      (gJ_ge h hc) apCall (c.fT t) (c.f t) (fun x hx => fT_eq t ht' hx)]

theorem play_n (h : c.Hyp) {ω : Om} (hc : c.Case ω) (t : ℕ) (ht : t < c.n) :
    df2oPlay d c.n c.r0 c.R0 c.δ (c.W ω) t = (df2RoundGa c.p c.n c.K (c.Ps ω) (c.gJ (c.Ps ω)) apCall (c.fT t)
      (ω.2 t) (c.xi ω t) (c.ze ω t) (c.hMode c.n ω t)).1 := by
  show (df2Round c.p c.n c.K (c.Ps ω) (c.f t) (ω.2 t) (c.xi ω t) (c.ze ω t)
    (df2oMode d c.n c.r0 c.R0 c.δ (c.W ω) t)).1 = _
  rw [df2Round_eq_Ga, ← hMode_n h hc t ht.le]
  exact roundGa_fst _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem regret_le (h : c.Hyp) {ω : Om} (hc : c.Case ω) :
    regretPts c.K c.f (df2oPlay d c.n c.r0 c.R0 c.δ (c.W ω)) c.n ≤
      c.Phi c.n ω - c.c0 + c.n * (c.p.R * c.η / c.p.eps) := by
  have hε := eps_pos h
  have hR := one_le_R h
  have hη := η_nonneg h
  have hb : 0 ≤ c.p.R * c.η / c.p.eps := by positivity
  have key : ∀ t < c.n, c.f t (df2oPlay d c.n c.r0 c.R0 c.δ (c.W ω) t) ≤
      c.fT t (c.ePt c.n ω t) + c.p.R * c.η / c.p.eps := by
    intro t ht
    rw [fT_eq t ht (ePt_interior h hc c.n t), play_n h hc t ht]
    show _ ≤ c.f t (df2RoundGa c.p c.n c.K (c.Ps ω) (c.gR (c.Ps ω)) apCall (c.fT t) (ω.2 t) (c.xi ω t) (c.ze ω t)
      (c.hMode c.n ω t)).1 + _
    rw [gR_eq h hc]
    have hm := hMode_ne_off h hc c.n t
    rcases hmt : c.hMode c.n ω t with _ | _ | st
    · exact absurd hmt hm
    · rw [roundGa_guard, roundGa_guard]; linarith
    · have hP := case_good hc
      rw [round_good_run c.p c.n h.convex h.closed hP hε (eps_lt_one hc) _ (gJ_ge h hc),
        round_good_run c.p c.n h.convex h.closed hP hε (eps_lt_one hc) (gauge (c.Kp (c.Ps ω))) (fun x => le_rfl)]
      obtain ⟨h1, -, h3, h4⟩ := pts_cmp c.p h.convex h.closed hP hε (eps_lt_one hc) hη (c.gJ (c.Ps ω))
        (gJ_ge h hc) (gJ_le h hc) st (c.xi ω t) (c.f t) (h.adv ht)
      have hu : rPt c.p (c.gJ (c.Ps ω)) st (c.xi ω t) / rPt c.p (gauge (c.Kp (c.Ps ω))) st (c.xi ω t) - 1 ≤ c.η := by
        have hpos : 0 < rPt c.p (gauge (c.Kp (c.Ps ω))) st (c.xi ω t) := by linarith
        have : rPt c.p (c.gJ (c.Ps ω)) st (c.xi ω t) / rPt c.p (gauge (c.Kp (c.Ps ω))) st (c.xi ω t) ≤ 1 + c.η := by
          rw [div_le_iff₀ hpos]; linarith
        linarith
      have h5 : c.p.R * (rPt c.p (c.gJ (c.Ps ω)) st (c.xi ω t) / rPt c.p (gauge (c.Kp (c.Ps ω))) st (c.xi ω t) - 1) /
          c.p.eps ≤ c.p.R * c.η / c.p.eps := by gcongr
      have := (abs_le.mp (h4.trans h5)).2
      dsimp only
      linarith
  unfold regretPts Phi c0
  have hs : ∑ t ∈ Finset.range c.n, c.f t (df2oPlay d c.n c.r0 c.R0 c.δ (c.W ω) t) ≤
      ∑ t ∈ Finset.range c.n, (c.fT t (c.ePt c.n ω t) + c.p.R * c.η / c.p.eps) :=
    Finset.sum_le_sum fun t ht => key t (Finset.mem_range.mp ht)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  linarith

/-! ### Measurability -/

theorem meas_omega (d n : ℕ) (r0 R0 δ1 : ℝ) : Measurable fun gs : ℕ → ℝ => df2oOmega d n r0 R0 δ1 gs := by
  have htoLp : Measurable fun v : Fin d → ℝ => (WithLp.toLp 2 v : E d) := (PiLp.continuous_toLp 2 _).measurable
  unfold df2oOmega
  refine Measurable.of_eval fun i => Measurable.of_eval fun r => ?_
  refine Measurable.prodMk (Measurable.of_eval fun k => ?_)
    (Measurable.of_eval fun v => Measurable.of_eval fun k => ?_)
  · exact htoLp.comp (Measurable.of_eval fun _ => measurable_pi_apply _)
  · exact htoLp.comp (Measurable.of_eval fun _ => measurable_pi_apply _)

theorem meas_pos_isSome (h : c.Hyp) :
    MeasurableSet {ω : Om | (df2oPos d c.n c.r0 c.R0 c.δ (c.W ω)).isSome} :=
  (PgMeas.pgMeas d c.K c.r0 c.R0 c.p.δ1 h.closed).1.preimage
    ((meas_omega d c.n c.r0 c.R0 c.p.δ1).comp measurable_fst)

theorem meas_Ps (h : c.Hyp) : Measurable c.Ps :=
  (PgMeas.pgMeas d c.K c.r0 c.R0 c.p.δ1 h.closed).2.comp ((meas_omega d c.n c.r0 c.R0 c.p.δ1).comp measurable_fst)

theorem pgGood_iff (K : Set (E d)) (R : ℝ) (o : Option (PgSp d)) :
    PgGood d K R o ↔ o.isSome ∧ PgGood d K R (some (o.getD 0)) := by
  cases o with
  | none => simp [PgGood]
  | some P => simp

theorem meas_case (h : c.Hyp) : MeasurableSet {ω | c.Case ω} := by
  have hG : MeasurableSet {ω : Om | PgGood d c.K c.p.R (some (c.Ps ω))} :=
    (PgMeas.pgGoodMeas d c.K c.p.R h.convex h.closed).preimage (meas_Ps h)
  have he : {ω | c.Case ω} = ({ω : Om | (df2oPos d c.n c.r0 c.R0 c.δ (c.W ω)).isSome} ∩
      {ω : Om | PgGood d c.K c.p.R (some (c.Ps ω))}) ∩ {_ω : Om | c.p.eps ≤ 1 / 2} := by
    ext ω
    show PgGood d c.K c.p.R (df2oPos d c.n c.r0 c.R0 c.δ (c.W ω)) ∧ c.p.eps ≤ 1 / 2 ↔ _
    rw [pgGood_iff]
    rfl
  rw [he]
  exact ((meas_pos_isSome h).inter hG).inter (MeasurableSet.const _)

theorem meas_mode0 (h : c.Hyp) : Measurable c.mode0 := by
  classical
  have he : c.mode0 = fun ω => if (df2oPos d c.n c.r0 c.R0 c.δ (c.W ω)).isSome then
      (if 1 / 2 < c.p.eps then Df2Mode.off else Df2Mode.run (df2Init c.p d)) else Df2Mode.off := by
    funext ω
    unfold mode0 df2oMode0
    cases df2oPos d c.n c.r0 c.R0 c.δ (c.W ω) <;> rfl
  rw [he]
  exact Measurable.ite (meas_pos_isSome h) measurable_const measurable_const

theorem kp_graph (h : c.Hyp) : MeasurableSet {q : PgSp d × E d | q.2 ∈ c.Kp q.1} :=
  ((h.closed.preimage (pg_continuous d).2.2).inter
    (isClosed_le (continuous_norm.comp continuous_snd) continuous_const)).measurableSet

theorem meas_gR (h : c.Hyp) : Measurable fun q : PgSp d × E d => c.gR q.1 q.2 :=
  gaugeRat_meas c.Kp (kp_graph h)

theorem meas_gJ (h : c.Hyp) : Measurable fun q : PgSp d × E d => c.gJ q.1 q.2 :=
  PgMeas.piTilde_family_measurable c.Kp (kp_graph h) c.p.R c.p.j

theorem meas_fT (h : c.Hyp) (t : ℕ) : Measurable (c.fT t) := by
  unfold fT
  split_ifs with ht
  · exact measurable_indicator_interior c.K (c.f t) (h.adv ht).1
  · exact measurable_const

theorem meas_xi (t : ℕ) : Measurable fun ω : Om => c.xi ω t :=
  Measurable.of_eval fun i => (measurable_pi_apply (c.N0 + t * (d + 1) + (i : ℕ))).comp measurable_fst

theorem meas_ze (t : ℕ) : Measurable fun ω : Om => c.ze ω t :=
  ((measurable_pi_apply _).comp measurable_fst).div_const 2

theorem meas_noise (t : ℕ) : Measurable fun ω : Om => ω.2 t := (measurable_pi_apply t).comp measurable_snd

theorem meas_hGa (h : c.Hyp) (k t : ℕ) :
    Measurable fun q : Om × E d => c.hGa k t (c.Ps q.1) q.2 := by
  have hq : Measurable fun q : Om × E d => (c.Ps q.1, q.2) := ((meas_Ps h).comp measurable_fst).prodMk measurable_snd
  by_cases htk : t < k
  · have e : c.hGa k t = c.gJ := by funext P; simp only [hGa, htk, ↓reduceIte]
    rw [e]
    have h2 := (meas_gJ h).comp hq
    simp only [Function.comp_def] at h2
    exact h2
  · have e : c.hGa k t = c.gR := by funext P; simp only [hGa, htk, ↓reduceIte]
    rw [e]
    have h2 := (meas_gR h).comp hq
    simp only [Function.comp_def] at h2
    exact h2

theorem meas_rnd (h : c.Hyp) {ga : Om → E d → ℝ} (hga : Measurable fun q : Om × E d => ga q.1 q.2) (t : ℕ)
    {m : Om → Df2Mode d} (hm : Measurable m) : Measurable fun ω => c.rnd (ga ω) ω t (m ω) :=
  meas_roundGa c.p c.n c.K h.closed (meas_Ps h) hga ((meas_fT h t).comp measurable_snd) (meas_noise t)
    (meas_ze t) (meas_xi t) hm

theorem meas_hMode (h : c.Hyp) (k t : ℕ) : Measurable fun ω => c.hMode k ω t := by
  induction t with
  | zero => exact meas_mode0 h
  | succ t ih => exact (meas_rnd h (meas_hGa h k t) t ih).snd

theorem meas_ePt (h : c.Hyp) (k t : ℕ) : Measurable fun ω => c.ePt k ω t :=
  (meas_rnd h ((meas_gR h).comp (((meas_Ps h).comp measurable_fst).prodMk measurable_snd)) t
    (meas_hMode h k t)).fst

theorem meas_Phi (h : c.Hyp) (k : ℕ) : Measurable (c.Phi k) :=
  Finset.measurable_sum _ fun t _ => (meas_fT h t).comp (meas_ePt h k t)

theorem meas_Ev (h : c.Hyp) (B : ℝ) (k : ℕ) : MeasurableSet (c.Ev B k) :=
  (meas_case h).inter (measurableSet_lt measurable_const ((meas_Phi h k).sub_const _))

/-! ### One step: the dither of round `k` -/

/-- The term of the stream that holds the dither of round `k`. -/
noncomputable def ix (k : ℕ) : ℕ := c.N0 + k * (d + 1) + d

/-- The world with the dither of round `k` replaced by `z`. -/
noncomputable def U (k : ℕ) (ω : Om) (z : ℝ) : Om := (Function.update ω.1 (c.ix k) z, ω.2)

theorem N0_le_ix (k : ℕ) : c.N0 ≤ c.ix k := le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

theorem ix_lt_spare {k : ℕ} (hk : k < c.n) : c.ix k < df2oSpare d c.n c.r0 c.R0 c.p.δ1 := by
  have h1 : (k + 1) * (d + 1) ≤ c.n * (d + 1) := Nat.mul_le_mul_right _ hk
  show c.N0 + k * (d + 1) + d < c.N0 + c.n * (d + 1)
  nlinarith

theorem idxA_ne {k : ℕ} (hk : k < c.n) (i r k' : ℕ) (j : Fin d) :
    df2oIdxA d c.n c.r0 c.R0 c.p.δ1 i r k' j ≠ c.ix k := by
  have hs := ix_lt_spare hk
  have hN := N0_le_ix (c := c) k
  unfold df2oIdxA
  dsimp only
  split_ifs with hin
  · obtain ⟨hi, hr, hk'⟩ := hin
    have hlt := sum_range_add_lt (df2oPgBlock d (df2oPgDelta c.r0 c.R0 c.p.δ1)) i (pgStages c.r0 c.R0) _ hi
      (idxA_lt _ _ _ r k' j d hr hk' (by unfold df2oPgW; omega) j.isLt)
    have e : c.N0 = ∑ i' ∈ Finset.range (pgStages c.r0 c.R0), df2oPgBlock d (df2oPgDelta c.r0 c.R0 c.p.δ1) i' := rfl
    have e2 : df2oPgOff d (df2oPgDelta c.r0 c.R0 c.p.δ1) i =
        ∑ i' ∈ Finset.range i, df2oPgBlock d (df2oPgDelta c.r0 c.R0 c.p.δ1) i' := rfl
    intro he
    rw [e2] at he
    rw [← e] at hlt
    linarith
  · intro he
    omega

theorem idxT_ne {k : ℕ} (hk : k < c.n) (i r v k' : ℕ) (j : Fin d) :
    df2oIdxT d c.n c.r0 c.R0 c.p.δ1 i r v k' j ≠ c.ix k := by
  have hs := ix_lt_spare hk
  have hN := N0_le_ix (c := c) k
  unfold df2oIdxT
  dsimp only
  split_ifs with hin
  · obtain ⟨hi, hr, hv, hk'⟩ := hin
    have hlt := sum_range_add_lt (df2oPgBlock d (df2oPgDelta c.r0 c.R0 c.p.δ1)) i (pgStages c.r0 c.R0) _ hi
      (idxT_lt _ (pgNs d (pgRhoStage d i)) _ _ r v k' j d hr hv hk' j.isLt)
    have e : c.N0 = ∑ i' ∈ Finset.range (pgStages c.r0 c.R0), df2oPgBlock d (df2oPgDelta c.r0 c.R0 c.p.δ1) i' := rfl
    have e2 : df2oPgOff d (df2oPgDelta c.r0 c.R0 c.p.δ1) i =
        ∑ i' ∈ Finset.range i, df2oPgBlock d (df2oPgDelta c.r0 c.R0 c.p.δ1) i' := rfl
    intro he
    rw [e2] at he
    rw [← e] at hlt
    unfold df2oPgW at he
    linarith
  · intro he
    omega

theorem omega_U {k : ℕ} (hk : k < c.n) (ω : Om) (z : ℝ) :
    df2oOmega d c.n c.r0 c.R0 c.p.δ1 (c.U k ω z).1 = df2oOmega d c.n c.r0 c.R0 c.p.δ1 ω.1 := by
  funext i r
  simp only [df2oOmega, U]
  congr 1
  · funext k'
    congr 1
    funext j
    exact Function.update_of_ne (idxA_ne hk i r k' j) _ _
  · funext v k'
    congr 1
    funext j
    exact Function.update_of_ne (idxT_ne hk i r v k' j) _ _

theorem pos_U {k : ℕ} (hk : k < c.n) (ω : Om) (z : ℝ) :
    df2oPos d c.n c.r0 c.R0 c.δ (c.W (c.U k ω z)) = df2oPos d c.n c.r0 c.R0 c.δ (c.W ω) := by
  show pg d c.K c.r0 c.R0 c.p.δ1 (df2oOmega d c.n c.r0 c.R0 c.p.δ1 (c.U k ω z).1) =
    pg d c.K c.r0 c.R0 c.p.δ1 (df2oOmega d c.n c.r0 c.R0 c.p.δ1 ω.1)
  rw [omega_U hk]

theorem Ps_U {k : ℕ} (hk : k < c.n) (ω : Om) (z : ℝ) : c.Ps (c.U k ω z) = c.Ps ω := by
  unfold Ps df2oPs; rw [pos_U hk]

theorem case_U {k : ℕ} (hk : k < c.n) (ω : Om) (z : ℝ) : c.Case (c.U k ω z) ↔ c.Case ω := by
  unfold Case Df2Case; rw [pos_U hk]; exact Iff.rfl

theorem mode0_U {k : ℕ} (hk : k < c.n) (ω : Om) (z : ℝ) : c.mode0 (c.U k ω z) = c.mode0 ω := by
  unfold mode0 df2oMode0; rw [pos_U hk]

theorem xi_U (k : ℕ) (ω : Om) (z : ℝ) (t : ℕ) : c.xi (c.U k ω z) t = c.xi ω t := by
  funext j
  exact Function.update_of_ne (round_idx_ne c.N0 d k t j j.isLt) _ _

theorem ze_U (k : ℕ) (ω : Om) (z : ℝ) {t : ℕ} (ht : t ≠ k) : c.ze (c.U k ω z) t = c.ze ω t := by
  unfold ze df2oZeta
  rw [show (c.U k ω z).1 (c.N0 + t * (d + 1) + d) = ω.1 (c.N0 + t * (d + 1) + d) from
    Function.update_of_ne (round_idx_ne_dither c.N0 d k t ht) _ _]

theorem ze_U_self (k : ℕ) (ω : Om) (z : ℝ) : c.ze (c.U k ω z) k = z / 2 := by
  unfold ze df2oZeta
  rw [show (c.U k ω z).1 (c.N0 + k * (d + 1) + d) = z from Function.update_self _ _ _]

theorem rnd_U {k : ℕ} (hk : k < c.n) (ga : E d → ℝ) (ω : Om) (z : ℝ) {t : ℕ} (ht : t ≠ k) (m : Df2Mode d) :
    c.rnd ga (c.U k ω z) t m = c.rnd ga ω t m := by
  unfold rnd; rw [Ps_U hk, xi_U, ze_U k ω z ht]; rfl

/-! ### One step: the hybrids before and after round `k` -/

theorem hMode_U {k : ℕ} (hk : k < c.n) (k' : ℕ) (ω : Om) (z : ℝ) {t : ℕ} (ht : t ≤ k) :
    c.hMode k' (c.U k ω z) t = c.hMode k' ω t := by
  induction t with
  | zero => exact mode0_U hk ω z
  | succ t ih =>
    show (c.rnd (c.hGa k' t (c.Ps (c.U k ω z))) (c.U k ω z) t (c.hMode k' (c.U k ω z) t)).2 =
      (c.rnd (c.hGa k' t (c.Ps ω)) ω t (c.hMode k' ω t)).2
    rw [Ps_U hk, ih (by omega), rnd_U hk _ ω z (by omega)]

theorem hMode_succ (k : ℕ) (ω : Om) {t : ℕ} (ht : t ≤ k) : c.hMode k ω t = c.hMode (k + 1) ω t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h1 : t < k := by omega
    show (c.rnd (c.hGa k t (c.Ps ω)) ω t (c.hMode k ω t)).2 = (c.rnd (c.hGa (k + 1) t (c.Ps ω)) ω t (c.hMode (k + 1) ω t)).2
    rw [ih (by omega)]
    simp only [hGa, h1, show t < k + 1 by omega, ↓reduceIte]

theorem ePt_U {k : ℕ} (hk : k < c.n) (k' : ℕ) (ω : Om) (z : ℝ) {t : ℕ} (ht : t ≤ k) :
    c.ePt k' (c.U k ω z) t = c.ePt k' ω t := by
  show (c.rnd (c.gR (c.Ps (c.U k ω z))) (c.U k ω z) t (c.hMode k' (c.U k ω z) t)).1 =
    (c.rnd (c.gR (c.Ps ω)) ω t (c.hMode k' ω t)).1
  rw [hMode_U hk k' ω z ht, Ps_U hk]
  unfold rnd
  rw [Ps_U hk, xi_U]
  exact roundGa_fst _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem ePt_succ (k : ℕ) (ω : Om) {t : ℕ} (ht : t ≤ k) : c.ePt k ω t = c.ePt (k + 1) ω t := by
  unfold ePt; rw [hMode_succ k ω ht]

/-- The modes of the exact-gauge rounds from round `k + 1` on, started in the mode `m`. -/
noncomputable def cMode (k : ℕ) (ω : Om) (m : Df2Mode d) : ℕ → Df2Mode d
  | 0 => m
  | s + 1 => (c.rnd (c.gR (c.Ps ω)) ω (k + 1 + s) (cMode k ω m s)).2

/-- The losses of the rounds after `k`, from the mode `m` before round `k + 1`. -/
noncomputable def Cont (k : ℕ) (ω : Om) (m : Df2Mode d) : ℝ :=
  ∑ s ∈ Finset.range (c.n - (k + 1)), c.fT (k + 1 + s) (c.rnd (c.gR (c.Ps ω)) ω (k + 1 + s) (c.cMode k ω m s)).1

/-- The losses of the rounds up to `k` in the hybrid `H_k'`. -/
noncomputable def Pre (k k' : ℕ) (ω : Om) : ℝ := ∑ t ∈ Finset.range (k + 1), c.fT t (c.ePt k' ω t)

theorem hMode_cont (k k' : ℕ) (hk' : k' ≤ k + 1) (ω : Om) (s : ℕ) :
    c.hMode k' ω (k + 1 + s) = c.cMode k ω (c.hMode k' ω (k + 1)) s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    show (c.rnd (c.hGa k' (k + 1 + s) (c.Ps ω)) ω (k + 1 + s) (c.hMode k' ω (k + 1 + s))).2 =
      (c.rnd (c.gR (c.Ps ω)) ω (k + 1 + s) (c.cMode k ω (c.hMode k' ω (k + 1)) s)).2
    rw [ih]
    simp only [hGa, show ¬ (k + 1 + s < k') by omega, ↓reduceIte]

theorem phi_split {k : ℕ} (hk : k < c.n) (k' : ℕ) (hk' : k' ≤ k + 1) (ω : Om) :
    c.Phi k' ω = c.Pre k k' ω + c.Cont k ω (c.hMode k' ω (k + 1)) := by
  unfold Phi Pre Cont
  rw [show c.n = k + 1 + (c.n - (k + 1)) by omega, Finset.sum_range_add, ← show c.n = k + 1 + (c.n - (k + 1)) by omega]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold ePt
  rw [hMode_cont k k' hk' ω s]

theorem cMode_U {k : ℕ} (hk : k < c.n) (ω : Om) (z : ℝ) (m : Df2Mode d) (s : ℕ) :
    c.cMode k (c.U k ω z) m s = c.cMode k ω m s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    show (c.rnd (c.gR (c.Ps (c.U k ω z))) (c.U k ω z) (k + 1 + s) (c.cMode k (c.U k ω z) m s)).2 =
      (c.rnd (c.gR (c.Ps ω)) ω (k + 1 + s) (c.cMode k ω m s)).2
    rw [ih, Ps_U hk, rnd_U hk _ ω z (by omega)]

theorem Cont_U {k : ℕ} (hk : k < c.n) (ω : Om) (z : ℝ) (m : Df2Mode d) :
    c.Cont k (c.U k ω z) m = c.Cont k ω m := by
  unfold Cont
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [cMode_U hk, Ps_U hk, rnd_U hk _ ω z (by omega)]

theorem Pre_U {k : ℕ} (hk : k < c.n) (k' : ℕ) (ω : Om) (z : ℝ) : c.Pre k k' (c.U k ω z) = c.Pre k k' ω := by
  unfold Pre
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [ePt_U hk k' ω z (by have := Finset.mem_range.mp ht; omega)]

theorem Pre_succ (k : ℕ) (ω : Om) : c.Pre k k ω = c.Pre k (k + 1) ω := by
  unfold Pre
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [ePt_succ k ω (by have := Finset.mem_range.mp ht; omega)]

/-- The mode after round `k` of the world with dither `z`, for the gauge `ga` of round `k`. -/
noncomputable def Mz (k : ℕ) (ga : E d → ℝ) (ω : Om) (z : ℝ) : Df2Mode d :=
  (df2RoundGa c.p c.n c.K (c.Ps ω) ga apCall (c.fT k) (ω.2 k) (c.xi ω k) (z / 2) (c.hMode k ω k)).2

theorem hMode_U_succ {k : ℕ} (hk : k < c.n) (k' : ℕ) {ω : Om} (hmk : c.hMode k' ω k = c.hMode k ω k) (z : ℝ) :
    c.hMode k' (c.U k ω z) (k + 1) = c.Mz k (c.hGa k' k (c.Ps ω)) ω z := by
  show (c.rnd (c.hGa k' k (c.Ps (c.U k ω z))) (c.U k ω z) k (c.hMode k' (c.U k ω z) k)).2 = _
  rw [hMode_U hk k' ω z le_rfl, hmk, Ps_U hk]
  unfold rnd Mz
  rw [Ps_U hk, xi_U, ze_U_self]
  rfl

/-- The event of a section, after round `k`. -/
def Gs (B : ℝ) (k : ℕ) (ω : Om) (m : Df2Mode d) : Prop := c.Case ω ∧ B < c.Pre k k ω + c.Cont k ω m - c.c0

theorem sec_k {k : ℕ} (hk : k < c.n) (B : ℝ) (ω : Om) :
    {z | c.U k ω z ∈ c.Ev B k} = {z | c.Gs B k ω (c.Mz k (c.gR (c.Ps ω)) ω z)} := by
  ext z
  simp only [Set.mem_ofPred_eq, Ev, Gs]
  rw [case_U hk, phi_split hk k (by omega), Pre_U hk, Cont_U hk, hMode_U_succ hk k rfl z]
  simp only [hGa, lt_irrefl, ↓reduceIte]

theorem sec_k1 {k : ℕ} (hk : k < c.n) (B : ℝ) (ω : Om) :
    {z | c.U k ω z ∈ c.Ev B (k + 1)} = {z | c.Gs B k ω (c.Mz k (c.gJ (c.Ps ω)) ω z)} := by
  ext z
  simp only [Set.mem_ofPred_eq, Ev, Gs]
  rw [case_U hk, phi_split hk (k + 1) le_rfl, Pre_U hk, Cont_U hk,
    hMode_U_succ hk (k + 1) (hMode_succ k ω le_rfl).symm z, ← Pre_succ]
  simp only [hGa, Nat.lt_succ_self, ↓reduceIte]

/-! ### One step: one Gaussian coordinate -/

theorem meas_gR_at (h : c.Hyp) {X : Type*} [MeasurableSpace X] (P : PgSp d) :
    Measurable fun q : X × E d => c.gR P q.2 := by
  have hq : Measurable fun q : X × E d => (P, q.2) := measurable_const.prodMk measurable_snd
  have h2 := (meas_gR h).comp hq
  simp only [Function.comp_def] at h2
  exact h2

theorem meas_cMode (h : c.Hyp) (k : ℕ) (ω : Om) (s : ℕ) : Measurable fun m : Df2Mode d => c.cMode k ω m s := by
  induction s with
  | zero => exact measurable_id
  | succ s ih =>
    exact (meas_roundGa c.p c.n c.K h.closed measurable_const (meas_gR_at h (c.Ps ω))
      ((meas_fT h (k + 1 + s)).comp measurable_snd) measurable_const measurable_const measurable_const ih).snd

theorem meas_Cont (h : c.Hyp) (k : ℕ) (ω : Om) : Measurable (c.Cont k ω) :=
  Finset.measurable_sum _ fun s _ => (meas_fT h (k + 1 + s)).comp
    (meas_roundGa c.p c.n c.K h.closed measurable_const (meas_gR_at h (c.Ps ω))
      ((meas_fT h (k + 1 + s)).comp measurable_snd) measurable_const measurable_const measurable_const
      (meas_cMode h k ω s)).fst

theorem meas_Gs (h : c.Hyp) (B : ℝ) (k : ℕ) (ω : Om) : MeasurableSet {m : Df2Mode d | c.Gs B k ω m} :=
  (MeasurableSet.const _).inter
    (measurableSet_lt measurable_const ((measurable_const.add (meas_Cont h k ω)).sub_const _))

/-- The cost of resampling the dither of round `k` with the bisection gauge at round `k` in place of the exact one. -/
theorem pw (h : c.Hyp) {k : ℕ} (hk : k < c.n) (B : ℝ) (ω : Om) :
    gaussianReal 0 1 {z | c.Gs B k ω (c.Mz k (c.gJ (c.Ps ω)) ω z)} ≤
      gaussianReal 0 1 {z | c.Gs B k ω (c.Mz k (c.gR (c.Ps ω)) ω z)} +
        ENNReal.ofReal (c.η * (2 + (c.p.R + 4) / c.p.eps) + c.η * |ω.2 k|) := by
  classical
  by_cases hc : c.Case ω
  swap
  · have he : {z | c.Gs B k ω (c.Mz k (c.gJ (c.Ps ω)) ω z)} = ∅ := by
      ext z
      simp only [Gs, hc, false_and, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
    rw [he, measure_empty]
    exact bot_le
  have hε := eps_pos h
  have hε1 := eps_lt_one hc
  have hP := case_good hc
  have hη := η_nonneg h
  have hR := one_le_R h
  rcases hm : c.hMode k ω k with _ | _ | st
  · exact absurd hm (hMode_ne_off h hc k k)
  · have e : ∀ ga : E d → ℝ, c.Mz k ga ω = fun _ => (if pgMu (c.Ps ω) + pgOp (c.Ps ω) 0 ∈ c.K then
        ((pgMu (c.Ps ω) + pgOp (c.Ps ω) 0 : E d), Df2Mode.guard) else (0, Df2Mode.off)).2 := by
      intro ga
      funext z
      simp only [Mz, hm, roundGa_guard]
    rw [e, e]
    exact le_self_add
  · rw [gR_eq h hc]
    set ξ := c.xi ω k with hξ
    set e := ω.2 k with he
    set N : ℝ → Df2Mode d := fun y =>
      df2NextAP apCall c.p c.n (df2Keps c.K (c.Ps ω) c.p.R c.p.eps) st ξ (st.A *ᵥ ξ) y with hN
    have hNm : Measurable N := by
      have h2 := (df2NextAP_measurable c.p c.n (fun P => df2Keps c.K P c.p.R c.p.eps)
        (keps_graph c.K h.closed c.p.R c.p.eps)).comp
          ((measurable_const (a := c.Ps ω)).prodMk ((measurable_const (a := st)).prodMk
            ((measurable_const (a := ξ)).prodMk (measurable_id (α := ℝ)))))
      simp only [Function.comp_def] at h2
      exact h2
    set T : Set ℝ := {y | c.Gs B k ω (N y)} with hT
    have hTm : MeasurableSet T := hNm (meas_Gs h B k ω)
    obtain ⟨h1, h2, h3, h4⟩ := pts_cmp c.p h.convex h.closed hP hε hε1 hη (c.gJ (c.Ps ω)) (gJ_ge h hc)
      (gJ_le h hc) st ξ (c.f k) (h.adv hk)
    set pt0 := rPt c.p (gauge (df2Kp c.K (c.Ps ω) c.p.R)) st ξ with hpt0
    set ptJ := rPt c.p (c.gJ (c.Ps ω)) st ξ with hptJ
    have hxJ := (rPoint_good c.p h.convex h.closed hP hε hε1 _ (gJ_ge h hc) st ξ).2
    have hx0 := (rPoint_good c.p h.convex h.closed hP hε hε1 (gauge (df2Kp c.K (c.Ps ω) c.p.R))
      (fun x => le_rfl) st ξ).2
    set FJ := c.fT k (rPoint c.p (c.Ps ω) (c.gJ (c.Ps ω)) st ξ) with hFJ
    set F0 := c.fT k (rPoint c.p (c.Ps ω) (gauge (df2Kp c.K (c.Ps ω) c.p.R)) st ξ) with hF0
    have hFJe : FJ = c.f k (rPoint c.p (c.Ps ω) (c.gJ (c.Ps ω)) st ξ) := fT_eq k hk hxJ
    have hF0e : F0 = c.f k (rPoint c.p (c.Ps ω) (gauge (df2Kp c.K (c.Ps ω) c.p.R)) st ξ) := fT_eq k hk hx0
    have hFJ01 := (h.adv hk).2 _ (interior_subset hxJ)
    have hpos : 0 < pt0 := by linarith
    set aJ := ptJ * (FJ + e) / 2 + 2 * (ptJ - 1) / c.p.eps with haJ
    set a0 := pt0 * (F0 + e) / 2 + 2 * (pt0 - 1) / c.p.eps with ha0
    have eJ : {z | c.Gs B k ω (c.Mz k (c.gJ (c.Ps ω)) ω z)} =
        {z | aJ + (1 + (ptJ / pt0 - 1)) * (pt0 / 4) * z ∈ T} := by
      ext z
      simp only [Set.mem_ofPred_eq, Mz, hm, round_good_run c.p c.n h.convex h.closed hP hε hε1 _ (gJ_ge h hc), hT]
      have hY : ptJ * (FJ + e + z / 2) / 2 + 2 * (ptJ - 1) / c.p.eps =
          aJ + (1 + (ptJ / pt0 - 1)) * (pt0 / 4) * z := by
        rw [haJ]; field_simp; ring
      rw [← hY]
    have e0 : {z | c.Gs B k ω (c.Mz k (gauge (df2Kp c.K (c.Ps ω) c.p.R)) ω z)} =
        {z | a0 + (pt0 / 4) * z ∈ T} := by
      ext z
      simp only [Set.mem_ofPred_eq, Mz, hm,
        round_good_run c.p c.n h.convex h.closed hP hε hε1 (gauge (df2Kp c.K (c.Ps ω) c.p.R)) (fun x => le_rfl), hT]
      have hY : pt0 * (F0 + e + z / 2) / 2 + 2 * (pt0 - 1) / c.p.eps = a0 + (pt0 / 4) * z := by
        rw [ha0]; ring
      rw [← hY]
    rw [eJ, e0]
    have hu : 0 ≤ ptJ / pt0 - 1 := by rw [sub_nonneg, le_div_iff₀ hpos]; linarith
    calc gaussianReal 0 1 {z | aJ + (1 + (ptJ / pt0 - 1)) * (pt0 / 4) * z ∈ T}
        ≤ gaussianReal 0 1 {z | a0 + (pt0 / 4) * z ∈ T} +
            ENNReal.ofReal ((ptJ / pt0 - 1) + |aJ - a0| / (2 * (pt0 / 4))) :=
          gauss_affine_le aJ a0 (pt0 / 4) (ptJ / pt0 - 1) (by positivity) hu T hTm
      _ ≤ gaussianReal 0 1 {z | a0 + (pt0 / 4) * z ∈ T} +
            ENNReal.ofReal (c.η * (2 + (c.p.R + 4) / c.p.eps) + c.η * |e|) := by
          refine add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_)
          have hs := step_arith pt0 ptJ c.η F0 FJ e c.p.R c.p.eps h1 h2 h3 hε (by linarith)
            (by rw [hFJe]; exact hFJ01.1) (by rw [hFJe]; exact hFJ01.2)
            (by rw [hFJe, hF0e]; exact h4)
          have : c.η * (2 + |e| + (c.p.R + 4) / c.p.eps) = c.η * (2 + (c.p.R + 4) / c.p.eps) + c.η * |e| := by ring
          rw [← this]
          exact hs

theorem gaussStream_prob : IsProbabilityMeasure gaussStream := by
  unfold gaussStream; infer_instance

theorem meas_U (k : ℕ) : Measurable fun q : Om × ℝ => c.U k q.1 q.2 :=
  (measurable_update'.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
    (measurable_snd.comp measurable_fst)

/-! ### One step -/

theorem step (h : c.Hyp) (hε : c.p.eps ≤ 1 / 2) (ν : Measure (ℕ → ℝ)) (hν : NoiseOK ν) (B : ℝ) (k : ℕ)
    (hk : k < c.n) :
    (gaussStream.prod ν) (c.Ev B (k + 1)) ≤
      (gaussStream.prod ν) (c.Ev B k) + ENNReal.ofReal (c.η * (c.p.R + 7) / c.p.eps) := by
  have := hν.1
  have := gaussStream_prob
  have he := eps_pos h
  have hη := η_nonneg h
  have hR := one_le_R h
  set a := c.η * (2 + (c.p.R + 4) / c.p.eps) with ha
  have ha0 : 0 ≤ a := by positivity
  have hmeas : Measurable fun ω : Om => gaussianReal 0 1 {z | c.U k ω z ∈ c.Ev B k} :=
    measurable_measure_prodMk_left ((meas_Ev h B k).preimage (meas_U k))
  rw [world_resample ν (c.ix k) _ (meas_Ev h B (k + 1))]
  calc ∫⁻ ω, gaussianReal 0 1 {z | (Function.update ω.1 (c.ix k) z, ω.2) ∈ c.Ev B (k + 1)} ∂(gaussStream.prod ν)
      = ∫⁻ ω, gaussianReal 0 1 {z | c.Gs B k ω (c.Mz k (c.gJ (c.Ps ω)) ω z)} ∂(gaussStream.prod ν) := by
        congr 1
        funext ω
        rw [← sec_k1 hk]
        rfl
    _ ≤ ∫⁻ ω, (gaussianReal 0 1 {z | c.U k ω z ∈ c.Ev B k} + ENNReal.ofReal (a + c.η * |ω.2 k|))
          ∂(gaussStream.prod ν) := by
        refine lintegral_mono fun ω => ?_
        rw [sec_k hk]
        exact pw h hk B ω
    _ = ∫⁻ ω, gaussianReal 0 1 {z | c.U k ω z ∈ c.Ev B k} ∂(gaussStream.prod ν) +
          ∫⁻ ω, ENNReal.ofReal (a + c.η * |ω.2 k|) ∂(gaussStream.prod ν) := lintegral_add_left hmeas _
    _ ≤ (gaussStream.prod ν) (c.Ev B k) + ENNReal.ofReal (a + c.η) := by
        rw [world_resample ν (c.ix k) _ (meas_Ev h B k)]
        refine add_le_add le_rfl ?_
        exact lintegral_noise_le gaussStream ν k (noise_abs_lintegral ν hν k) a c.η ha0 hη
    _ ≤ (gaussStream.prod ν) (c.Ev B k) + ENNReal.ofReal (c.η * (c.p.R + 7) / c.p.eps) := by
        gcongr
        rw [ha, le_div_iff₀ he]
        have h3 : (c.p.R + 4) / c.p.eps * c.p.eps = c.p.R + 4 := div_mul_cancel₀ _ he.ne'
        nlinarith

theorem steps (h : c.Hyp) (hε : c.p.eps ≤ 1 / 2) (ν : Measure (ℕ → ℝ)) (hν : NoiseOK ν) (B : ℝ) :
    ∀ k ≤ c.n, (gaussStream.prod ν) (c.Ev B k) ≤
      (gaussStream.prod ν) (c.Ev B 0) + k * ENNReal.ofReal (c.η * (c.p.R + 7) / c.p.eps) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    calc (gaussStream.prod ν) (c.Ev B (k + 1))
        ≤ (gaussStream.prod ν) (c.Ev B k) + ENNReal.ofReal (c.η * (c.p.R + 7) / c.p.eps) :=
          c.step h hε ν hν B k (by omega)
      _ ≤ (gaussStream.prod ν) (c.Ev B 0) + k * ENNReal.ofReal (c.η * (c.p.R + 7) / c.p.eps) +
            ENNReal.ofReal (c.η * (c.p.R + 7) / c.p.eps) := by gcongr; exact ih (by omega)
      _ = (gaussStream.prod ν) (c.Ev B 0) + ((k + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (c.η * (c.p.R + 7) / c.p.eps) := by
          push_cast; ring

end GCtx

/-! ## 5. Proposition G -/

theorem df2PropG : Df2PropG := by
  intro d n r0 R0 δ K f hH ν hν B
  let c : GCtx d := ⟨n, r0, R0, δ, K, f⟩
  have h : c.Hyp := hH
  by_cases hε : (df2oPar d n δ).eps ≤ 1 / 2
  swap
  · have he : {ω : Om | Df2Case d n r0 R0 δ (df2World K f ω) ∧
        B + 1 < regretPts K f (df2oPlay d n r0 R0 δ (df2World K f ω)) n} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun hc => absurd hc.2 hε
    rw [he, measure_empty]
    exact bot_le
  have hsub : {ω : Om | Df2Case d n r0 R0 δ (df2World K f ω) ∧
      B + 1 < regretPts K f (df2oPlay d n r0 R0 δ (df2World K f ω)) n} ⊆ c.Ev B n := by
    rintro ω ⟨hc, hB⟩
    refine ⟨hc, ?_⟩
    have h1 : regretPts K f (df2oPlay d n r0 R0 δ (df2World K f ω)) n ≤
        c.Phi c.n ω - c.c0 + c.n * (c.p.R * c.η / c.p.eps) := c.regret_le h hc
    have h2 : (c.n : ℝ) * (c.p.R * c.η / c.p.eps) ≤ 1 := by
      have hp := c.param_sum h
      have hδ1 : c.p.δ1 ≤ 1 := GCtx.δ1_le h
      have : (c.n : ℝ) * (c.p.R * c.η / c.p.eps) ≤ c.n * (c.η * (c.p.R + 7) / c.p.eps) := by
        have he := c.eps_pos h
        have hη := GCtx.η_nonneg h
        have hR := c.one_le_R h
        have : c.p.R * c.η ≤ c.η * (c.p.R + 7) := by nlinarith
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right this he.le) (Nat.cast_nonneg _)
      linarith
    show B < c.Phi c.n ω - c.c0
    linarith
  have h0 : c.Ev B 0 = {ω : Om | Df2Case d n r0 R0 δ (df2World K f ω) ∧
      B < regretPts K f (df2zPlay d n r0 R0 δ (df2World K f ω)) n} := by
    ext ω
    simp only [GCtx.Ev, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hc, hB⟩
      exact ⟨hc, (c.phi_zero h hc) ▸ hB⟩
    · rintro ⟨hc, hB⟩
      exact ⟨hc, (c.phi_zero h hc).symm ▸ hB⟩
  calc (gaussStream.prod ν) {ω : Om | Df2Case d n r0 R0 δ (df2World K f ω) ∧
        B + 1 < regretPts K f (df2oPlay d n r0 R0 δ (df2World K f ω)) n}
      ≤ (gaussStream.prod ν) (c.Ev B n) := measure_mono hsub
    _ ≤ (gaussStream.prod ν) (c.Ev B 0) + n * ENNReal.ofReal (c.η * (c.p.R + 7) / c.p.eps) :=
        c.steps h hε ν hν B n le_rfl
    _ ≤ _ := by
        rw [h0]
        gcongr
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (c.param_sum h)

end AdversarialBco.Poly.PropG
