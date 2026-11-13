/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.ShadowIface
public import AdversarialBco.Poly.Df2WorldDetProof
public import AdversarialBco.Poly.Df2EvAdMeas
public import AdversarialBco.Poly.Df2EvSIDQ
public import AdversarialBco.Poly.Df2EvSISDF
public import AdversarialBco.Poly.Df2EvYProof
public import AdversarialBco.Poly.Poly32OTop

@[expose] public section

/-!
# The regret of a run record on the good event

* `df2DetF_holds`: DET for an epoch context with a routine per round (`df2CtxAtF`), from proved inputs
  ((O7): `DetBase.hap` reads `∀ s, ApSpec (c.ap s)`);
* `RunRec`: a run record `ρ = (n, δ, K, f, q, ap, ξ, nt, ζ)`, its round `rnd`, modes `mode`, plays `play`, means
  `mean`, and the context `ctxAt a` and path `pathAt a` of its virtual epoch started before round `a`;
* `RunRec.det` (Lemma (O1-GEN)): at a good position (`PgGood`), with `ε ≤ 1/2`, admissible losses, `EpochOK` of every
  virtual epoch at the horizon `n - a`, and the Azuma inequality between the losses played and their means, the
  regret over the `n` rounds is at most `B_n = 2 ρ/η + n ε + (2 n log(7/δe))^{1/2}`.

The proof is that of DET for D0 (Poly/Df2WorldDetProof.lean), with the context, path, modes and means of D0
replaced by those of the record; the routine of round `t` is `ap t`, which the epoch started at `a` reads at its round
`t - a`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix

namespace AdversarialBco.Bit.Cpl

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Layer2

variable {d : ℕ}

/-- DET with a routine per round: the epoch context `df2CtxAtF` meets (a) and (b5') on every path with admissible
losses and the five events, when every routine meets `ApSpec`. -/
theorem df2DetF_holds {n : ℕ} {δ : ℝ} {Kt : Set (E d)} (ap : ℕ → ApFun d) (π : Df2Path d) {m : ℕ} (hd : 1 ≤ d)
    (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1) (heps : (df2oPar d n δ).eps ≤ 1 / 2) (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (hbody : Df2Body d (df2oPar d n δ).R Kt) (hap : ∀ s, ApSpec (ap s)) (hadm : ∀ s < m, AdmLoss Kt (π.g s))
    (evG : (df2CtxAtF d n δ Kt ap).EvG π m) (evY : (df2CtxAtF d n δ Kt ap).EvY π m)
    (evLQ : (df2CtxAtF d n δ Kt ap).EvLQ π m) (evSDF : (df2CtxAtF d n δ Kt ap).EvSDF π m)
    (evDQ : (df2CtxAtF d n δ Kt ap).EvDQ π m) : (df2CtxAtF d n δ Kt ap).EpochOK π m :=
  (DetHyp.mk (DetBase.mk (c := df2CtxAtF d n δ Kt ap) df2LayerOne_holds lemmaW SIF.df2SIFacts_holds hd hn hδ0 hδ1
    rfl heps (df2RowsHold d n δ hd hn hδ0 hδ1 heps) hm1 hmn hbody hap hadm) evG evY evLQ evSDF evDQ).epoch_ok

/-- A run record: the horizon `n`, the confidence `δ`, the body `K`, the losses `f`, the
position `q`, the routine `ap t` of round `t`, the draws `xi`, the noises `nt` and the dithers `ze`. -/
structure RunRec (d : ℕ) where
  n : ℕ
  δ : ℝ
  K : Set (E d)
  f : ℕ → E d → ℝ
  q : PgSp d
  ap : ℕ → ApFun d
  xi : ℕ → Fin d → ℝ
  nt : ℕ → ℝ
  ze : ℕ → ℝ

namespace RunRec

variable (ρ : RunRec d)

/-- The parameters of the learner. -/
noncomputable abbrev p : Df2OPar := df2oPar d ρ.n ρ.δ

/-- The positioned body `K~ ∩ B_R`. -/
abbrev Kt : Set (E d) := df2Kp ρ.K ρ.q ρ.p.R

/-- Round `t` of the record from the mode `m`, at the exact gauge of the positioned body. -/
noncomputable def rnd (t : ℕ) (m : Df2Mode d) : E d × Df2Mode d :=
  df2RoundGa ρ.p ρ.n ρ.K ρ.q (gauge ρ.Kt) (ρ.ap t) (ρ.f t) (ρ.nt t) (ρ.xi t) (ρ.ze t) m

/-- The mode before round `a + s`, started in the mode `m` before round `a`. -/
noncomputable def frm (ρ : RunRec d) (a : ℕ) (m : Df2Mode d) : ℕ → Df2Mode d
  | 0 => m
  | s + 1 => (ρ.rnd (a + s) (frm ρ a m s)).2

/-- The mode before round `t`. -/
noncomputable def mode (t : ℕ) : Df2Mode d := ρ.frm 0 (.run (df2Init ρ.p d)) t

/-- The play of round `t`. -/
noncomputable def play (t : ℕ) : E d := (ρ.rnd t (ρ.mode t)).1

/-- The mean of the loss of round `t` given the past (the play does not read the routine, the noise or the dither). -/
noncomputable def mean (t : ℕ) : ℝ :=
  ∫ z, ρ.f t (df2RoundGa ρ.p ρ.n ρ.K ρ.q (gauge ρ.Kt) apCall (ρ.f t) 0 z 0 (ρ.mode t)).1 ∂gaussK d

/-- The positioned loss of round `t`, `g_t(y) = f_t(μ_q + T_q y)/2`. -/
noncomputable def g (t : ℕ) (y : E d) : ℝ := ρ.f t (pgMu ρ.q + pgOp ρ.q y) / 2

/-- The context of the virtual epoch started before round `a`. -/
noncomputable def ctxAt (a : ℕ) : Df2Ctx d := df2CtxAtF d ρ.n ρ.δ ρ.Kt fun s => ρ.ap (a + s)

/-- The path of the virtual epoch started before round `a`. -/
noncomputable def pathAt (a : ℕ) : Df2Path d :=
  ⟨fun s => ρ.g (a + s), fun s => (ρ.nt (a + s) + ρ.ze (a + s)) / 2, fun s => ρ.xi (a + s)⟩

/-- At a position where the guard centre and every play lie in `K`, the next mode of a round is that of the epoch map
of the epoch started at `a`, at its round `s`. -/
theorem rnd_snd (hK0 : pgMu ρ.q + pgOp ρ.q 0 ∈ ρ.K)
    (hplay : ∀ X : Fin d → ℝ, pgMu ρ.q + pgOp ρ.q
      (WithLp.toLp 2 ((df2Pip ρ.p ρ.Kt (WithLp.toLp 2 X))⁻¹ • X)) ∈ ρ.K)
    (a s : ℕ) (m : Df2Mode d) :
    (ρ.rnd (a + s) m).2 = (df2RoundE (ρ.ctxAt a) ((ρ.ctxAt a).ap s) ((ρ.pathAt a).g s) ((ρ.pathAt a).e s)
      ((ρ.pathAt a).xi s) m).2 := by
  cases m with
  | off => rfl
  | guard =>
    simp only [rnd, df2RoundGa, df2RoundE, hK0, ↓reduceIte]
  | run st =>
    have h := hplay (st.mu + (1 - ρ.p.lam) • (st.A *ᵥ ρ.xi (a + s)))
    simp only [df2Pip] at h
    simp only [rnd, df2RoundGa, df2RoundE, h, ↓reduceIte]
    congr 1
    simp only [g, pathAt, ctxAt, df2CtxAtF, df2Pip]
    ring

theorem frm_add (a : ℕ) (m : Df2Mode d) (s s' : ℕ) : ρ.frm a m (s + s') = ρ.frm (a + s) (ρ.frm a m s) s' := by
  induction s' with
  | zero => rfl
  | succ s' ih =>
    rw [← Nat.add_assoc, frm, frm, ih, Nat.add_assoc]

theorem mode_add (a s : ℕ) : ρ.mode (a + s) = ρ.frm a (ρ.mode a) s := by
  unfold mode
  rw [frm_add, Nat.zero_add]

theorem frm_fresh
    (hround : ∀ a s m, (ρ.rnd (a + s) m).2 = (df2RoundE (ρ.ctxAt a) ((ρ.ctxAt a).ap s) ((ρ.pathAt a).g s)
      ((ρ.pathAt a).e s) ((ρ.pathAt a).xi s) m).2)
    (a s : ℕ) : ρ.frm a (.run (df2Init ρ.p d)) s = (ρ.ctxAt a).mode (ρ.pathAt a) s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [frm, ih, hround]
    rfl

/-- The mean of the loss of round `t`, at a running mode, is at most twice the mean of the extension. -/
theorem mean_le (t : ℕ) (st : Df2St d) (hmode : ρ.mode t = .run st)
    (hplay : ∀ X : Fin d → ℝ, pgMu ρ.q + pgOp ρ.q
      (WithLp.toLp 2 ((df2Pip ρ.p ρ.Kt (WithLp.toLp 2 X))⁻¹ • X)) ∈ ρ.K)
    (hf01 : ∀ x ∈ ρ.K, ρ.f t x ∈ Set.Icc (0 : ℝ) 1) (heps : 0 < ρ.p.eps) (L : ℝ)
    (hlip : ∀ x y, |df2Ext ρ.p ρ.Kt (ρ.g t) x - df2Ext ρ.p ρ.Kt (ρ.g t) y| ≤ L * ‖x - y‖) :
    ρ.mean t ≤
      2 * ∫ z, df2Ext ρ.p ρ.Kt (ρ.g t)
        (WithLp.toLp 2 st.mu + (1 - ρ.p.lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) st.A z) ∂(stdGaussian (E d)) := by
  unfold mean
  rw [hmode]
  set p := ρ.p with hp
  set Kt := ρ.Kt with hKt
  set ext := df2Ext p Kt (ρ.g t) with hext
  set Ps := ρ.q with hPs
  set X : (Fin d → ℝ) → Fin d → ℝ := fun z => st.mu + (1 - p.lam) • (st.A *ᵥ z) with hX
  have hpt : ∀ z, (df2RoundGa p ρ.n ρ.K Ps (gauge Kt) apCall (ρ.f t) 0 z 0 (.run st)).1 =
      pgMu Ps + pgOp Ps (WithLp.toLp 2 ((df2Pip p Kt (WithLp.toLp 2 (X z)))⁻¹ • X z)) := by
    intro z
    have h := hplay (X z)
    simp only [df2Pip, hX] at h
    simp only [df2RoundGa]
    split_ifs with hc
    · rfl
    · exact absurd h hc
  have hle : ∀ z, ρ.f t (pgMu Ps + pgOp Ps (WithLp.toLp 2 ((df2Pip p Kt (WithLp.toLp 2 (X z)))⁻¹ • X z))) ≤
      2 * ext (WithLp.toLp 2 (X z)) := by
    intro z
    have hin := hplay (X z)
    have h0 := (hf01 _ hin).1
    have hpip : 1 ≤ df2Pip p Kt (WithLp.toLp 2 (X z)) := le_max_left _ _
    simp only [hext, df2Ext, g]
    rw [WithLp.toLp_smul] at hin h0 ⊢
    have h2 : 0 ≤ 2 * (df2Pip p Kt (WithLp.toLp 2 (X z)) - 1) / p.eps := by
      apply div_nonneg _ heps.le; linarith
    nlinarith
  have hcont : Continuous fun u : E d =>
      ext (WithLp.toLp 2 st.mu + (1 - p.lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) st.A u) := by
    have hlip' : LipschitzWith (Real.toNNReal |L|) ext := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (abs_nonneg L)]
      exact (hlip x y).trans (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _))
    exact hlip'.continuous.comp (by fun_prop : Continuous fun u : E d =>
      WithLp.toLp 2 st.mu + (1 - p.lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) st.A u)
  have hint : Integrable (fun u : E d => ext (WithLp.toLp 2 st.mu +
      (1 - p.lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) st.A u)) (stdGaussian (E d)) := by
    have := integrable_lip_affine ext L hlip (WithLp.toLp 2 st.mu) ((1 - p.lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) st.A)
    simpa using this
  have hXz : ∀ z, ext (WithLp.toLp 2 (X z)) = (fun u : E d => ext (WithLp.toLp 2 st.mu +
      (1 - p.lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) st.A u)) (WithLp.toLp 2 z) := by
    intro z
    show ext _ = ext _
    congr 1
  simp_rw [hpt]
  calc _ ≤ ∫ z, 2 * ext (WithLp.toLp 2 (X z)) ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => (hf01 _ (hplay _)).1) ?_
          (Filter.Eventually.of_forall hle)
        refine Integrable.const_mul ?_ 2
        simp_rw [hXz]
        exact integrable_pi_toLp _ hcont hint
    _ = _ := by
        rw [integral_const_mul]
        congr 1
        simp_rw [hXz]
        exact integral_pi_toLp _ hcont

/-- Lemma (O1-GEN): the regret of a run record on the good event. -/
theorem det (hd : 1 ≤ d) (hn : 1 ≤ ρ.n) (hδ0 : 0 < ρ.δ) (hδ1 : ρ.δ < 1) (hKc : IsClosed ρ.K)
    (hKcv : Convex ℝ ρ.K) (hfA : ∀ t < ρ.n, AdmLoss ρ.K (ρ.f t)) (hq : PgGood d ρ.K ρ.p.R (some ρ.q))
    (heps : ρ.p.eps ≤ 1 / 2) (hep : ∀ a < ρ.n, (ρ.ctxAt a).EpochOK (ρ.pathAt a) (ρ.n - a))
    (haz : ∑ t ∈ Finset.range ρ.n, ρ.f t (ρ.play t) ≤
      ∑ t ∈ Finset.range ρ.n, ρ.mean t + Real.sqrt (2 * ρ.n * Real.log (7 / ρ.p.δe))) :
    regretPts ρ.K ρ.f ρ.play ρ.n ≤ bReg d ρ.n ρ.δ := by
  have RH := rowHyp_of d ρ.n ρ.δ hd hn hδ0 hδ1 heps
  have hL := RH.L_pos
  have hdR := RH.d_pos
  have hnR : (0 : ℝ) < ρ.n := by exact_mod_cast (by omega : 0 < ρ.n)
  have heps0 : 0 < ρ.p.eps := by rw [RH.eps]; positivity
  have heps1 : ρ.p.eps < 1 := by linarith
  have hrho : 0 ≤ ρ.p.rho / ρ.p.eta := by
    rw [RH.rho, RH.eta]; positivity
  obtain ⟨hdet, -, -, -⟩ := good_unpack hq
  have hKt : ρ.Kt = posBody ρ.K (pgMu ρ.q) (pgOp ρ.q) := df2Kp_eq_posBody hq
  have hbody : Df2Body d ρ.p.R ρ.Kt := body_good hKc hKcv hq
  obtain ⟨hconv, hclosed, hb1', hbR', -⟩ := hbody
  have h0Kt : (0 : E d) ∈ ρ.Kt := hb1' (Metric.mem_closedBall_self zero_le_one)
  have hK0 : pgMu ρ.q + pgOp ρ.q 0 ∈ ρ.K := h0Kt.1
  have hplayKt : ∀ X : E d, (df2Pip ρ.p ρ.Kt X)⁻¹ • X ∈ ρ.Kt := by
    intro X
    have h := play_mem _ _ hconv hclosed hb1' heps0 heps1 X
    have h2 := hconv.smul_mem_of_zero_mem h0Kt h (t := 1 - ρ.p.eps) ⟨by linarith, by linarith⟩
    rwa [smul_smul, mul_inv_cancel₀ (by linarith : (1 - ρ.p.eps) ≠ 0), one_smul] at h2
  have hplay : ∀ X : Fin d → ℝ, pgMu ρ.q + pgOp ρ.q
      (WithLp.toLp 2 ((df2Pip ρ.p ρ.Kt (WithLp.toLp 2 X))⁻¹ • X)) ∈ ρ.K := by
    intro X
    have h := hplayKt (WithLp.toLp 2 X)
    rw [← WithLp.toLp_smul] at h
    exact h.1
  -- the positioned losses
  have hadm : ∀ t < ρ.n, AdmLoss ρ.Kt (ρ.g t) := by
    intro t ht
    obtain ⟨hcv, h01⟩ := hfA t ht
    refine ⟨⟨hconv, ?_⟩, fun y hy => ?_⟩
    · intro y1 hy1 y2 hy2 a b ha hb hab
      have hx := affine_comb ρ.q y1 y2 a b hab
      have := hcv.2 hy1.1 hy2.1 ha hb hab
      simp only [g, smul_eq_mul] at this ⊢
      rw [hx]
      linarith
    · have := h01 _ hy.1
      simp only [g, Set.mem_Icc] at this ⊢
      constructor <;> linarith [this.1, this.2]
  have hX1 := fun t (ht : t < ρ.n) =>
    (SIF.df2SIFacts_holds d ρ.n ρ.δ ρ.Kt (ρ.g t) hd hn hδ0 hδ1 heps
      ⟨hconv, hclosed, hb1', hbR', (body_good hKc hKcv hq).2.2.2.2⟩ (hadm t ht)).1
  -- the modes
  have hround := ρ.rnd_snd hK0 hplay
  have hfresh := ρ.frm_fresh hround
  have hmode0 : ρ.mode 0 = .run (df2Init ρ.p d) := rfl
  -- the regret
  unfold regretPts bReg
  have hKne : ρ.K.Nonempty := ⟨_, hK0⟩
  have hlow : ∑ t ∈ Finset.range ρ.n, ρ.mean t - 2 * (ρ.p.rho / ρ.p.eta) - ρ.n * ρ.p.eps ≤
      sInf ((fun y => ∑ t ∈ Finset.range ρ.n, ρ.f t y) '' ρ.K) := by
    apply le_csInf (hKne.image _)
    rintro _ ⟨x, hx, rfl⟩
    -- the point `x'' = (1 - ε) S x` of `K_ε`
    have hdetU : IsUnit (pgMat ρ.q).det := Ne.isUnit hdet
    set y : E d := WithLp.toLp 2 ((pgMat ρ.q)⁻¹ *ᵥ WithLp.ofLp (x - pgMu ρ.q)) with hy
    have hSy : pgMu ρ.q + pgOp ρ.q y = x := by
      simp only [hy, pgOp, Matrix.toEuclideanCLM_toLp, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetU,
        Matrix.one_mulVec, WithLp.toLp_ofLp]
      abel
    have hyKt : y ∈ ρ.Kt := by
      rw [hKt]
      show pgMu ρ.q + pgOp ρ.q y ∈ ρ.K
      rw [hSy]; exact hx
    set x'' : Fin d → ℝ := (1 - ρ.p.eps) • WithLp.ofLp y with hx''
    have hne1 : (1 - ρ.p.eps) ≠ 0 := by linarith
    have hxK : x'' ∈ df2KepsOf ρ.Kt ρ.p.eps := by
      show WithLp.toLp 2 ((1 - ρ.p.eps)⁻¹ • x'') ∈ ρ.Kt
      rw [hx'', smul_smul, inv_mul_cancel₀ hne1, one_smul, WithLp.toLp_ofLp]
      exact hyKt
    -- prop:shrink and the extension on `K_ε`
    have hpt : ∀ t < ρ.n, 2 * df2Ext ρ.p ρ.Kt (ρ.g t) (WithLp.toLp 2 x'') ≤ ρ.f t x + ρ.p.eps := by
      intro t ht
      rw [(hX1 t ht).2.2.2 x'' hxK]
      have hsm : WithLp.toLp 2 x'' = (1 - ρ.p.eps) • y + ρ.p.eps • (0 : E d) := by
        rw [hx'', WithLp.toLp_smul, WithLp.toLp_ofLp, smul_zero, add_zero]
      rw [hsm]
      have hc := (hadm t ht).1.2 hyKt h0Kt (by linarith : (0 : ℝ) ≤ 1 - ρ.p.eps) heps0.le (by ring)
      have hy01 := (hadm t ht).2 y hyKt
      have h001 := (hadm t ht).2 0 h0Kt
      have hfx : ρ.g t y = ρ.f t x / 2 := by simp only [g, hSy]
      have h0half : ρ.g t 0 ≤ 1 / 2 := by
        have := (hfA t ht).2 _ hK0
        simp only [g]; linarith [this.2]
      simp only [smul_eq_mul] at hc
      nlinarith [hy01.1, h001.1]
    -- the epochs of the run
    have hQ : ∀ k a, ρ.n - a = k → a ≤ ρ.n → ρ.mode a = .run (df2Init ρ.p d) →
        ∑ t ∈ Finset.Ico a ρ.n, (ρ.mean t - 2 * df2Ext ρ.p ρ.Kt (ρ.g t) (WithLp.toLp 2 x'')) ≤
          2 * (ρ.p.rho / ρ.p.eta) := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k IH =>
      intro a hk ha hfa
      rcases Nat.lt_or_ge a ρ.n with han | han
      swap
      · obtain rfl : a = ρ.n := le_antisymm ha han
        simp only [Finset.Ico_self, Finset.sum_empty]
        positivity
      have hmode : ∀ s, ρ.mode (a + s) = (ρ.ctxAt a).mode (ρ.pathAt a) s := fun s => by
        rw [mode_add, hfa, hfresh]
      have hstep : ∀ s, a + s < ρ.n → (∃ st, (ρ.ctxAt a).mode (ρ.pathAt a) s = .run st) →
          ρ.mean (a + s) - 2 * df2Ext ρ.p ρ.Kt (ρ.g (a + s)) (WithLp.toLp 2 x'') ≤
          2 * ((ρ.ctxAt a).ebar (ρ.pathAt a) s -
            df2Ext (ρ.ctxAt a).p (ρ.ctxAt a).Kt ((ρ.pathAt a).g s) (WithLp.toLp 2 x'')) := by
        rintro s hs ⟨st, hst⟩
        have h := ρ.mean_le (a + s) st ((hmode s).trans hst) hplay (hfA (a + s) hs).2 heps0 _
          (hX1 (a + s) hs).2.2.1
        have hst' : (ρ.ctxAt a).st (ρ.pathAt a) s = st := by
          simp [Df2Ctx.st, hst, Df2Mode.stOr]
        have he : (ρ.ctxAt a).ebar (ρ.pathAt a) s =
            ∫ z, df2Ext ρ.p ρ.Kt (ρ.g (a + s))
              (WithLp.toLp 2 st.mu + (1 - ρ.p.lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) st.A z)
              ∂(stdGaussian (E d)) := by
          rw [Df2Ctx.ebar, hst']
          rfl
        have he2 : df2Ext (ρ.ctxAt a).p (ρ.ctxAt a).Kt ((ρ.pathAt a).g s) (WithLp.toLp 2 x'') =
            df2Ext ρ.p ρ.Kt (ρ.g (a + s)) (WithLp.toLp 2 x'') := rfl
        rw [he, he2]
        linarith
      have hrun0 : ∃ st, (ρ.ctxAt a).mode (ρ.pathAt a) 0 = .run st := ⟨_, rfl⟩
      have hrunS : ∀ s, (ρ.ctxAt a).cont (ρ.pathAt a) s →
          ∃ st, (ρ.ctxAt a).mode (ρ.pathAt a) (s + 1) = .run st := by
        rintro s ⟨st, h, -⟩
        exact ⟨st, h⟩
      have hsplit : ∀ r, r < ρ.n - a → (∀ s < r, (ρ.ctxAt a).cont (ρ.pathAt a) s) →
          ∑ t ∈ Finset.Ico a (a + (r + 1)), (ρ.mean t - 2 * df2Ext ρ.p ρ.Kt (ρ.g t) (WithLp.toLp 2 x'')) ≤
          2 * (ρ.ctxAt a).eReg (ρ.pathAt a) r x'' := by
        intro r hr hcont
        rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, Df2Ctx.eReg, Finset.mul_sum]
        refine Finset.sum_le_sum fun s hs => hstep s (by rw [Finset.mem_range] at hs; omega) ?_
        rw [Finset.mem_range] at hs
        rcases s with _ | s
        · exact hrun0
        · exact hrunS s (hcont s (by omega))
      rcases hep a han with ⟨r, hr, hcont, hfire, hreg⟩ | ⟨hcont, hreg⟩
      · have h1 := hsplit r hr hcont
        have h2 := hreg x'' hxK
        have hfa' : ρ.mode (a + (r + 1)) = .run (df2Init ρ.p d) := by
          rw [hmode]; exact hfire
        have h3 := IH (ρ.n - (a + (r + 1))) (by omega) (a + (r + 1)) rfl (by omega) hfa'
        rw [← Finset.sum_Ico_consecutive _ (by omega : a ≤ a + (r + 1)) (by omega : a + (r + 1) ≤ ρ.n)]
        linarith
      · have h1 := hsplit (ρ.n - a - 1) (by omega) (fun s hs => hcont s (by omega))
        have h2 := hreg x'' hxK
        have hn' : a + (ρ.n - a - 1 + 1) = ρ.n := by omega
        rw [hn'] at h1
        have : (ρ.ctxAt a).p.rho / (ρ.ctxAt a).p.eta = ρ.p.rho / ρ.p.eta := rfl
        linarith
    have h0 := hQ ρ.n 0 (Nat.sub_zero ρ.n) (Nat.zero_le ρ.n) hmode0
    rw [← Finset.range_eq_Ico] at h0
    have h1 : ∑ t ∈ Finset.range ρ.n, 2 * df2Ext ρ.p ρ.Kt (ρ.g t) (WithLp.toLp 2 x'') ≤
        ∑ t ∈ Finset.range ρ.n, (ρ.f t x + ρ.p.eps) :=
      Finset.sum_le_sum fun t ht => hpt t (Finset.mem_range.mp ht)
    rw [Finset.sum_sub_distrib] at h0
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    simp only
    linarith
  linarith

end RunRec

end AdversarialBco.Bit.Cpl
