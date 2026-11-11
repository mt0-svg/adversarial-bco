/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2WorldLay
public import AdversarialBco.Poly.Df2Layer2Proof
public import AdversarialBco.Poly.PgProcBase

@[expose] public section

/-!
# Lemma 8.8 on the world

`df2VEWorldOf_holds : Df2VEWorldOf`. For a start round `a < n`, the world with the filtration `𝒢w` of
Df2WorldLay.lean is an instance of setting (E) (`setE_world`) with the position as parameter. The body of the
instance at a position `q` is `kTh q = K~ ∩ B_R` when `q` meets `PgGood`, else `B_R`; its losses are
`f_{a+s}(S⁻¹ ·)/2`, else `0`. On the case of the analysis the context and the path of the instance are those of
D0 (`df2zCtx`, `df2zPath`) at the rounds `s < n - a`, and the epoch reads no other round (`ctx_epochOK_congr`).

(L1) for the instance (`epochMeas_world`) comes from `Df2ApCallMeas` and `PgGoodMeas` alone: the gauge of a family
of convex bodies containing `B̄(0, 1)` is measurable once membership is (`gauge_family_measurable`); the extension
reads the loss at `x/pip(x)`, of gauge at most `1 - ε`, so inside the body, whose image under `S⁻¹` lies in the
interior of `K` (`play_interior`), where a convex loss agrees with the measurable `(interior K).piecewise f 0`.
-/

open MeasureTheory ProbabilityTheory Matrix
open AdversarialBco.RealRAM

namespace AdversarialBco.Poly

namespace Layer2

variable {d : ℕ}

/-! ## Locality of the epoch -/

theorem ctx_mode_congr (c : Df2Ctx d) (π π' : Df2Path d) (m : ℕ)
    (h : ∀ s < m, π.g s = π'.g s ∧ π.e s = π'.e s ∧ π.xi s = π'.xi s) : ∀ s ≤ m, c.mode π s = c.mode π' s
  | 0, _ => rfl
  | s + 1, hs => by
    obtain ⟨h1, h2, h3⟩ := h s (by omega)
    simp only [Df2Ctx.mode, ctx_mode_congr c π π' m h s (by omega), h1, h2, h3]

/-- The epoch at the horizon `m ≥ 1` reads the path at the rounds `s < m` only. -/
theorem ctx_epochOK_congr (c : Df2Ctx d) (π π' : Df2Path d) (m : ℕ) (hm : 1 ≤ m)
    (h : ∀ s < m, π.g s = π'.g s ∧ π.e s = π'.e s ∧ π.xi s = π'.xi s) : c.EpochOK π m ↔ c.EpochOK π' m := by
  have hmode := ctx_mode_congr c π π' m h
  have hst : ∀ s ≤ m, c.st π s = c.st π' s := fun s hs => by simp only [Df2Ctx.st, hmode s hs]
  have heReg : ∀ r < m, ∀ x, c.eReg π r x = c.eReg π' r x := by
    intro r hr x
    simp only [Df2Ctx.eReg]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hsm : s < m := by rw [Finset.mem_range] at hs; omega
    simp only [Df2Ctx.ebar, hst s hsm.le, (h s hsm).1]
  have hcont : ∀ s < m, (c.cont π s ↔ c.cont π' s) := fun s hs => by
    simp only [Df2Ctx.cont, hmode (s + 1) hs]
  have hfire : ∀ s < m, (c.fire π s ↔ c.fire π' s) := fun s hs => by
    simp only [Df2Ctx.fire, hmode (s + 1) hs]
  unfold Df2Ctx.EpochOK
  exact or_congr (exists_congr fun r => and_congr_right fun hr => and_congr
    (forall₂_congr fun s hs => hcont s (by omega)) (and_congr (hfire r hr)
      (forall₂_congr fun x _ => by rw [heReg r hr x])))
    (and_congr (forall₂_congr fun s hs => hcont s hs)
      (forall₂_congr fun x _ => by rw [heReg (m - 1) (by omega) x]))

/-! ## The bodies and the losses of the instance -/

open Classical in
/-- The body of the instance at the position `q`: `K~ ∩ B_R` on `PgGood`, else `B_R`. -/
noncomputable def kTh (n : ℕ) (δ : ℝ) (K : Set (E d)) (q : PgSp d) : Set (E d) :=
  if PgGood d K (df2oPar d n δ).R (some q) then df2Kp K q (df2oPar d n δ).R
  else df2Kp Set.univ 0 (df2oPar d n δ).R

open Classical in
/-- The loss of round `s` of the instance at the position `q`: `f_{a+s}(S⁻¹ y)/2` on `PgGood`, else `0`. -/
noncomputable def gTh (n : ℕ) (δ : ℝ) (K : Set (E d)) (f : ℕ → E d → ℝ) (a s : ℕ) (q : PgSp d) : E d → ℝ :=
  if PgGood d K (df2oPar d n δ).R (some q) then fun y => f (a + s) (pgMu q + pgOp q y) / 2 else 0

theorem kTh_good {n : ℕ} {δ : ℝ} {K : Set (E d)} {q : PgSp d} (hq : PgGood d K (df2oPar d n δ).R (some q)) :
    kTh n δ K q = df2Kp K q (df2oPar d n δ).R := by
  classical
  simp [kTh, hq]

theorem kTh_bad {n : ℕ} {δ : ℝ} {K : Set (E d)} {q : PgSp d} (hq : ¬ PgGood d K (df2oPar d n δ).R (some q)) :
    kTh n δ K q = df2Kp Set.univ 0 (df2oPar d n δ).R := by
  classical
  simp [kTh, hq]

theorem df2Kp_univ (q : PgSp d) (R : ℝ) : df2Kp (Set.univ : Set (E d)) q R = Metric.closedBall 0 R := by
  ext y; simp [df2Kp]

theorem good_unpack {K : Set (E d)} {R : ℝ} {q : PgSp d} (hq : PgGood d K R (some q)) :
    (pgMat q).det ≠ 0 ∧ Metric.closedBall 0 1 ⊆ posBody K (pgMu q) (pgOp q) ∧
      posBody K (pgMu q) (pgOp q) ⊆ Metric.closedBall 0 R ∧
      pgMw (posBody K (pgMu q) (pgOp q)) ≤ 1.27 * Real.sqrt (d + 1) / d := by
  obtain ⟨P, hP, h⟩ := hq
  cases Option.some_injective _ hP
  exact h

theorem df2Kp_eq_posBody {K : Set (E d)} {R : ℝ} {q : PgSp d} (hq : PgGood d K R (some q)) :
    df2Kp K q R = posBody K (pgMu q) (pgOp q) := by
  ext y
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  have := (good_unpack hq).2.2.1 h
  rwa [mem_closedBall_zero_iff] at this

theorem pgOp_surjective {q : PgSp d} (hdet : (pgMat q).det ≠ 0) : Function.Surjective (pgOp q) := by
  intro w
  refine ⟨WithLp.toLp 2 ((pgMat q)⁻¹ *ᵥ WithLp.ofLp w), ?_⟩
  rw [pgOp_apply, WithLp.ofLp_toLp, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (Ne.isUnit hdet), Matrix.one_mulVec, WithLp.toLp_ofLp]

theorem affine_comb (q : PgSp d) (x y : E d) (a b : ℝ) (hab : a + b = 1) :
    pgMu q + pgOp q (a • x + b • y) = a • (pgMu q + pgOp q x) + b • (pgMu q + pgOp q y) := by
  rw [map_add, map_smul, map_smul, smul_add, smul_add]
  have : pgMu q = a • pgMu q + b • pgMu q := by rw [← add_smul, hab, one_smul]
  nth_rewrite 1 [this]
  abel

theorem convex_posBody {K : Set (E d)} (hK : Convex ℝ K) (q : PgSp d) : Convex ℝ (posBody K (pgMu q) (pgOp q)) := by
  intro x hx y hy a b ha hb hab
  show pgMu q + pgOp q (a • x + b • y) ∈ K
  rw [affine_comb q x y a b hab]
  exact hK hx hy ha hb hab

theorem isClosed_posBody {K : Set (E d)} (hK : IsClosed K) (q : PgSp d) :
    IsClosed (posBody K (pgMu q) (pgOp q)) :=
  hK.preimage (continuous_const.add (pgOp q).continuous)

theorem body_good {K : Set (E d)} (hKc : IsClosed K) (hKconv : Convex ℝ K) {R : ℝ} {q : PgSp d}
    (hq : PgGood d K R (some q)) : Df2Body d R (df2Kp K q R) := by
  obtain ⟨_, hb1, hbR, hmw⟩ := good_unpack hq
  rw [df2Kp_eq_posBody hq]
  exact ⟨convex_posBody hKconv q, isClosed_posBody hKc q, hb1, hbR, hmw⟩

theorem body_bad {R : ℝ} (hR : 1 ≤ R) (hmw : 1 / R ≤ df2Mw d) (q : PgSp d) :
    Df2Body d R (df2Kp (Set.univ : Set (E d)) q R) := by
  rw [df2Kp_univ]
  exact ⟨convex_closedBall _ _, Metric.isClosed_closedBall, Metric.closedBall_subset_closedBall hR, subset_rfl,
    (pgMw_closedBall_le R (by linarith)).trans hmw⟩

theorem body_kTh {n : ℕ} {δ : ℝ} {K : Set (E d)} (hKc : IsClosed K) (hKconv : Convex ℝ K)
    (hR : 1 ≤ (df2oPar d n δ).R) (hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d) (q : PgSp d) :
    Df2Body d (df2oPar d n δ).R (kTh n δ K q) := by
  by_cases hq : PgGood d K (df2oPar d n δ).R (some q)
  · rw [kTh_good hq]; exact body_good hKc hKconv hq
  · rw [kTh_bad hq]; exact body_bad hR hmw 0

theorem adm_gTh {n : ℕ} {δ : ℝ} {K : Set (E d)} (hKconv : Convex ℝ K) (hKc : IsClosed K)
    (hR : 1 ≤ (df2oPar d n δ).R) (hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d) {f : ℕ → E d → ℝ} {a s : ℕ}
    (hf : AdmLoss K (f (a + s))) (q : PgSp d) : AdmLoss (kTh n δ K q) (gTh n δ K f a s q) := by
  have hbody := body_kTh hKc hKconv hR hmw q (n := n) (δ := δ)
  by_cases hq : PgGood d K (df2oPar d n δ).R (some q)
  · rw [kTh_good hq] at hbody ⊢
    simp only [gTh, hq, ↓reduceIte]
    refine ⟨⟨hbody.1, fun x hx y hy a b ha hb hab => ?_⟩, fun x hx => ?_⟩
    · have := hf.1.2 hx.1 hy.1 ha hb hab
      simp only [smul_eq_mul] at this ⊢
      rw [affine_comb q x y a b hab]
      linarith
    · have := hf.2 _ hx.1
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · rw [kTh_bad hq] at hbody ⊢
    simp only [gTh, hq, ↓reduceIte]
    exact ⟨convexOn_const 0 hbody.1, fun _ _ => ⟨le_rfl, zero_le_one⟩⟩

/-! ## (L1) for the instance -/

theorem mem_kTh_meas {n : ℕ} {δ : ℝ} {K : Set (E d)} (hKc : IsClosed K) (hKconv : Convex ℝ K)
    (hG : PgGoodMeas) : MeasurableSet {p : PgSp d × E d | p.2 ∈ kTh n δ K p.1} := by
  have hset : {p : PgSp d × E d | p.2 ∈ kTh n δ K p.1} =
      Set.ite {p | PgGood d K (df2oPar d n δ).R (some p.1)}
        {p | pgMu p.1 + pgOp p.1 p.2 ∈ K ∧ ‖p.2‖ ≤ (df2oPar d n δ).R} {p | ‖p.2‖ ≤ (df2oPar d n δ).R} := by
    ext p
    by_cases hq : PgGood d K (df2oPar d n δ).R (some p.1)
    · simp [Set.ite, kTh, hq, df2Kp]
    · simp [Set.ite, kTh, hq, df2Kp]
  rw [hset]
  refine MeasurableSet.ite (measurable_fst (hG d K _ hKconv hKc)) ?_ ?_
  · exact ((hKc.preimage (pg_continuous d).2.2).inter
      (isClosed_le continuous_snd.norm continuous_const)).measurableSet
  · exact (isClosed_le continuous_snd.norm continuous_const).measurableSet

theorem gauge_kTh_meas {n : ℕ} {δ : ℝ} {K : Set (E d)} (hKc : IsClosed K) (hKconv : Convex ℝ K)
    (hG : PgGoodMeas) (hR : 1 ≤ (df2oPar d n δ).R) (hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d) :
    Measurable fun p : PgSp d × E d => gauge (kTh n δ K p.1) p.2 :=
  gauge_family_measurable _ (mem_kTh_meas hKc hKconv hG) (fun q => (body_kTh hKc hKconv hR hmw q).1)
    (fun q => (body_kTh hKc hKconv hR hmw q).2.2.1)

/-- The point of `K` at which the extension reads the loss lies in the interior of `K`. -/
theorem play_interior {K : Set (E d)} (hKconv : Convex ℝ K) {p : Df2OPar} {q : PgSp d}
    (hq : PgGood d K p.R (some q)) (heps0 : 0 < p.eps) (heps1 : p.eps < 1) (x : E d) :
    pgMu q + pgOp q ((df2Pip p (df2Kp K q p.R) x)⁻¹ • x) ∈ interior K := by
  obtain ⟨hdet, hb1, _, _⟩ := good_unpack hq
  set C := df2Kp K q p.R
  have hC : C = posBody K (pgMu q) (pgOp q) := df2Kp_eq_posBody hq
  have hconv : Convex ℝ C := hC ▸ convex_posBody hKconv q
  have hnhds : C ∈ nhds (0 : E d) :=
    Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos) (hC ▸ hb1)
  have hpip1 : 1 ≤ df2Pip p C x := le_max_left _ _
  have hpip2 : gauge C x / (1 - p.eps) ≤ df2Pip p C x := le_max_right _ _
  have hpos : 0 < df2Pip p C x := by linarith
  have hg : gauge C ((df2Pip p C x)⁻¹ • x) < 1 := by
    rw [gauge_smul_of_nonneg (inv_nonneg.mpr hpos.le), smul_eq_mul]
    have h1e : 0 < 1 - p.eps := by linarith
    have : gauge C x ≤ (1 - p.eps) * df2Pip p C x := by
      rw [div_le_iff₀ h1e] at hpip2; linarith
    rw [inv_mul_lt_iff₀ hpos]
    nlinarith [gauge_nonneg (s := C) x]
  have hint := (gauge_lt_one_iff_mem_interior hconv hnhds).mp hg
  exact affine_interior_mem K C (pgMu q) (pgOp q) (pgOp_surjective hdet) (fun y hy => hy.1) _ hint

open Classical in
theorem measurable_piecewise_interior {K : Set (E d)} {g : E d → ℝ} (hg : ConvexOn ℝ K g) :
    Measurable ((interior K).piecewise g 0) := by
  exact ContinuousOn.measurable_piecewise hg.continuousOn_interior continuousOn_const
    isOpen_interior.measurableSet

theorem ext_kTh_meas {n : ℕ} {δ : ℝ} {K : Set (E d)} (hKc : IsClosed K) (hKconv : Convex ℝ K)
    (hG : PgGoodMeas) (hR : 1 ≤ (df2oPar d n δ).R) (hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d)
    (heps0 : 0 < (df2oPar d n δ).eps) (heps1 : (df2oPar d n δ).eps < 1) {f : ℕ → E d → ℝ} {a s : ℕ}
    (hf : ConvexOn ℝ K (f (a + s))) :
    Measurable fun p : PgSp d × E d => df2Ext (df2oPar d n δ) (kTh n δ K p.1) (gTh n δ K f a s p.1) p.2 := by
  classical
  set P : PgSp d × E d → ℝ := fun p => df2Pip (df2oPar d n δ) (kTh n δ K p.1) p.2 with hPdef
  have hP : Measurable P :=
    measurable_const.max ((gauge_kTh_meas hKc hKconv hG hR hmw).div_const _)
  set F := (interior K).piecewise (f (a + s)) 0
  have hF : Measurable F := measurable_piecewise_interior hf
  have hGs : MeasurableSet {p : PgSp d × E d | PgGood d K (df2oPar d n δ).R (some p.1)} :=
    measurable_fst (hG d K _ hKconv hKc)
  have hpt : Measurable fun p : PgSp d × E d => pgMu p.1 + pgOp p.1 ((P p)⁻¹ • p.2) :=
    (pg_continuous d).2.2.measurable.comp (measurable_fst.prodMk (hP.inv.smul measurable_snd))
  have heq : (fun p : PgSp d × E d => df2Ext (df2oPar d n δ) (kTh n δ K p.1) (gTh n δ K f a s p.1) p.2) =
      fun p => P p * (if PgGood d K (df2oPar d n δ).R (some p.1) then F (pgMu p.1 + pgOp p.1 ((P p)⁻¹ • p.2)) / 2 else 0) +
        2 * (P p - 1) / (df2oPar d n δ).eps := by
    funext p
    by_cases hq : PgGood d K (df2oPar d n δ).R (some p.1)
    · have hin := play_interior hKconv hq heps0 heps1 p.2
      have hk := kTh_good (n := n) (δ := δ) hq
      simp only [hPdef, hk, df2Ext, gTh, hq, ↓reduceIte, F]
      rw [Set.piecewise_eq_of_mem _ _ _ hin]
    · simp [df2Ext, hPdef, gTh, hq]
  rw [heq]
  exact (hP.mul (Measurable.ite hGs ((hF.comp hpt).div_const 2) measurable_const)).add
    (((hP.sub measurable_const).const_mul 2).div_const _)

theorem next_kTh_meas {n : ℕ} {δ : ℝ} {K : Set (E d)} (hd : 1 ≤ d) (hKc : IsClosed K) (hKconv : Convex ℝ K)
    (hG : PgGoodMeas) (hAp : Df2ApCallMeas) :
    Measurable fun x : PgSp d × Df2St d × (Fin d → ℝ) × ℝ =>
      df2NextAP apCall (df2oPar d n δ) n (df2KepsOf (kTh n δ K x.1) (df2oPar d n δ).eps) x.2.1 x.2.2.1
        (x.2.1.A *ᵥ x.2.2.1) x.2.2.2 := by
  classical
  have h1 := hAp d n δ K hd hKc hKconv
  have h2 := (hAp d n δ Set.univ hd isClosed_univ convex_univ).comp
    (measurable_const.prodMk measurable_snd : Measurable fun x : PgSp d × Df2St d × (Fin d → ℝ) × ℝ =>
      ((0 : PgSp d), x.2))
  have heq : (fun x : PgSp d × Df2St d × (Fin d → ℝ) × ℝ =>
      df2NextAP apCall (df2oPar d n δ) n (df2KepsOf (kTh n δ K x.1) (df2oPar d n δ).eps) x.2.1 x.2.2.1
        (x.2.1.A *ᵥ x.2.2.1) x.2.2.2) = fun x =>
      if PgGood d K (df2oPar d n δ).R (some x.1) then
        df2NextAP apCall (df2oPar d n δ) n (df2KepsOf (df2Kp K x.1 (df2oPar d n δ).R) (df2oPar d n δ).eps) x.2.1
          x.2.2.1 (x.2.1.A *ᵥ x.2.2.1) x.2.2.2
      else df2NextAP apCall (df2oPar d n δ) n (df2KepsOf (df2Kp Set.univ 0 (df2oPar d n δ).R)
          (df2oPar d n δ).eps) x.2.1 x.2.2.1 (x.2.1.A *ᵥ x.2.2.1) x.2.2.2 := by
    funext x
    by_cases hq : PgGood d K (df2oPar d n δ).R (some x.1) <;> simp [kTh, hq]
  rw [heq]
  exact Measurable.ite (measurable_fst (hG d K _ hKconv hKc)) h1 h2

/-- (L1) for the instance of the world. -/
theorem epochMeas_world {n : ℕ} {δ : ℝ} {K : Set (E d)} (hd : 1 ≤ d) (hKc : IsClosed K) (hKconv : Convex ℝ K)
    (hG : PgGoodMeas) (hAp : Df2ApCallMeas) (hR : 1 ≤ (df2oPar d n δ).R)
    (hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d) (heps0 : 0 < (df2oPar d n δ).eps) (heps1 : (df2oPar d n δ).eps < 1)
    {f : ℕ → E d → ℝ} (hf : f ∈ Advs K n) (a : ℕ) :
    Df2EpochMeas (df2oPar d n δ) n (n - a) (kTh n δ K) (fun s => gTh n δ K f a s) apCall :=
  ⟨gauge_kTh_meas hKc hKconv hG hR hmw,
    fun s hs => ext_kTh_meas hKc hKconv hG hR hmw heps0 heps1 (hf (a + s) (by omega)).1,
    next_kTh_meas hd hKc hKconv hG hAp⟩

/-! ## The position as parameter -/

theorem measurable_pi_gen {Ω ι : Type*} {β : ι → Type*} [∀ i, MeasurableSpace (β i)] {m : MeasurableSpace Ω}
    {g : Ω → ∀ i, β i} (h : ∀ i, Measurable[m] fun x => g x i) : Measurable[m] g :=
  measurable_pi_iff.mpr h

/-- The stream of PG is measurable before round `0` of every instance: PG never reads the indices of `lay`. -/
theorem omega_meas_𝒢w (n : ℕ) (r0 R0 δ1 : ℝ) (a : ℕ) :
    Measurable[𝒢w (df2oN0 d r0 R0 δ1) (df2oSpare d n r0 R0 δ1) n d a 0]
      fun ω : WΩ => df2oOmega d n r0 R0 δ1 ω.1 := by
  have hW : ∀ i, df2oPgW d (df2oPgDelta r0 R0 δ1) i = pgNs d (pgRhoStage d i) +
      pgMT (df2oPgDelta r0 R0 δ1) * pgNT d (pgRhoStage d i) := fun _ => rfl
  have hN0 : df2oN0 d r0 R0 δ1 =
      mrOff (pgJr (df2oPgDelta r0 R0 δ1)) d (df2oPgW d (df2oPgDelta r0 R0 δ1)) (pgStages r0 R0) := rfl
  have hS : df2oSpare d n r0 R0 δ1 = mrOff (pgJr (df2oPgDelta r0 R0 δ1)) d (df2oPgW d (df2oPgDelta r0 R0 δ1))
      (pgStages r0 R0) + n * (d + 1) := rfl
  have hA : ∀ i r k (c : Fin d), gσ (df2oIdxA d n r0 R0 δ1 i r k c) ≤
      𝒢w (df2oN0 d r0 R0 δ1) (df2oSpare d n r0 R0 δ1) n d a 0 := fun i r k c =>
    gσ_le_𝒢w _ _ _ _ 0 _ (by
      rintro ⟨s', _, c', h⟩
      rw [idxA_eq, hN0] at h
      exact mrA_ne_lay _ _ _ _ _ _ _ _ _ hW hS i r k c a s' c' h.symm)
  have hT : ∀ i r v k (c : Fin d), gσ (df2oIdxT d n r0 R0 δ1 i r v k c) ≤
      𝒢w (df2oN0 d r0 R0 δ1) (df2oSpare d n r0 R0 δ1) n d a 0 := fun i r v k c =>
    gσ_le_𝒢w _ _ _ _ 0 _ (by
      rintro ⟨s', _, c', h⟩
      rw [idxT_eq, hN0] at h
      exact mrT_ne_lay _ _ _ _ _ _ _ _ _ hW hS i r v k c a s' c' h.symm)
  unfold df2oOmega
  refine measurable_pi_gen fun i => measurable_pi_gen fun r => Measurable.prodMk
    (measurable_pi_gen fun k => ?_) (measurable_pi_gen fun v => measurable_pi_gen fun k => ?_)
  · exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_of fun c => meas_coord _ (hA i r k c))
  · exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_of fun c => meas_coord _ (hT i r v k c))

theorem theta_meas (hPG : PgMeas) {n : ℕ} {r0 R0 δ : ℝ} {K : Set (E d)} (hKc : IsClosed K) (f : ℕ → E d → ℝ)
    (a : ℕ) : Measurable[𝒢w (df2oN0 d r0 R0 (df2oPar d n δ).δ1) (df2oSpare d n r0 R0 (df2oPar d n δ).δ1) n d a 0]
      fun ω : WΩ => df2oPs d n r0 R0 δ (df2World K f ω) :=
  (hPG d K r0 R0 (df2oPar d n δ).δ1 hKc).2.comp (omega_meas_𝒢w n r0 R0 (df2oPar d n δ).δ1 a)

theorem case_good {n : ℕ} {r0 R0 δ : ℝ} {w : World d} (h : Df2Case d n r0 R0 δ w) :
    PgGood d w.K (df2oPar d n δ).R (some (df2oPs d n r0 R0 δ w)) := by
  obtain ⟨P, hP, hrest⟩ := h.1
  have : df2oPs d n r0 R0 δ w = P := by simp [df2oPs, hP]
  rw [this]
  exact ⟨P, rfl, hrest⟩

theorem eps_pos_of_rows {p : Df2OPar} {d n : ℕ} (H : RowHyp p d n) : 0 < p.eps := by
  rw [H.eps]
  have := H.L504
  have hd' : (0 : ℝ) < d := by exact_mod_cast H.hd
  have hn' : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast H.hn)
  positivity

/-! ## Lemma 8.8 on the world -/

/-- `Df2VEWorldOf`: each virtual epoch of D0 is an instance of setting (E), so E1-loc bounds it. -/
theorem df2VEWorldOf_holds : Df2VEWorldOf := by
  intro E1 PAP PGM PGG APM d n r0 R0 δ K f hW ν hν a ha
  obtain ⟨hd, hn, _, _, hδ0, hδ1, hKcpt, hKconv, _, _, hf⟩ := hW
  have hKc := hKcpt.isClosed
  have := hν.1
  by_cases heps : (df2oPar d n δ).eps ≤ 1 / 2
  swap
  · exact (measure_mono (show _ ⊆ (∅ : Set WΩ) from fun ω hω => heps hω.1.2)).trans (by simp)
  have H := rowHyp_of d n δ hd hn hδ0 hδ1 heps
  have hR := row_one_le_R _ d n H
  have hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d := by rw [H.R]; exact inv_R_le_df2Mw d hd
  have heps0 := eps_pos_of_rows H
  have heps1 : (df2oPar d n δ).eps < 1 := by linarith
  have hAp : ApSpec (d := d) apCall := fun Q a0 r R P w e =>
    ⟨fun h1 h2 h3 h4 h5 h6 h7 => (PAP d Q a0 r R P w e).1 hd h1 h2 h3 h4 h5 h6 h7, (PAP d Q a0 r R P w e).2⟩
  have hB := E1 d n (n - a) δ hd hn (by omega) (by omega) hδ0 hδ1 heps (PgSp d) (kTh n δ K)
    (fun s => gTh n δ K f a s) apCall (body_kTh hKc hKconv hR hmw)
    (fun q s hs => adm_gTh hKconv hKc hR hmw (hf (a + s) (by omega)) q) hAp
    (epochMeas_world hd hKc hKconv PGG APM hR hmw heps0 heps1 hf a) WΩ (gaussStream.prod ν) inferInstance
    (𝒢w (df2oN0 d r0 R0 (df2oPar d n δ).δ1) (df2oSpare d n r0 R0 (df2oPar d n δ).δ1) n d a)
    (fun ω => df2oPs d n r0 R0 δ (df2World K f ω))
    (xiL (df2oN0 d r0 R0 (df2oPar d n δ).δ1) (df2oSpare d n r0 R0 (df2oPar d n δ).δ1) n d a)
    (eL (df2oN0 d r0 R0 (df2oPar d n δ).δ1) (df2oSpare d n r0 R0 (df2oPar d n δ).δ1) n d a)
    (theta_meas PGM hKc f a) (setE_world _ _ n a lemmaNZProd ν hν le_rfl)
  refine (measure_mono fun ω hω => ?_).trans hB
  obtain ⟨hcase, hnot⟩ := hω
  have hgood : PgGood d K (df2oPar d n δ).R (some (df2oPs d n r0 R0 δ (df2World K f ω))) := case_good hcase
  simp only [Set.mem_ofPred_eq]
  rw [kTh_good hgood]
  refine fun hok => hnot ((ctx_epochOK_congr _ _ (df2zPath d n r0 R0 δ (df2World K f ω) a) (n - a) (by omega)
    fun s hs => ⟨?_, ?_, ?_⟩).mp hok)
  · simp only [gTh, hgood, ↓reduceIte]
    rfl
  · have hlt : a + s < n := by omega
    simp [eL, lay, hlt, df2zPath, df2oZeta, df2World]
  · have hlt : a + s < n := by omega
    funext c
    simp [xiL, lay, hlt, df2zPath, df2oXi, df2World]

end Layer2

end AdversarialBco.Poly
