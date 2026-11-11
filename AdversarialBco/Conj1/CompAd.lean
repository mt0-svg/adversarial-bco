/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1.WorldAd
public import AdversarialBco.Conj1.Top
public import AdversarialBco.Poly.Df2PropGAdProof
public import AdversarialBco.Poly.Df2CompProof

@[expose] public section

/-!
# The composition in strategy form

`df2ORegretMeasAd_of`: the regret clause of DF2-O against a strategy (`Df2ORegretMeasAd`, Top.lean) from Lemma 8.8
and the Azuma event on the world of a loss process (`Df2VEWorldAd`, `Df2AzWorldAd`, WorldAd.lean), Lemma 8.10
(`Df2WorldDet`), Proposition 8.11 (`Df2PropGAd`), Theorem 8.3 and the trivial bound, as `df2CompOf_holds`
(Df2CompProof.lean) does for a fixed sequence.

* Proposition 8.11 takes the regret of DJ against the losses the strategy chose on the run to the regret of D0 in the
  comparison world `cmpWorld`; only that run meets the world layer.
* `cmpProc`: the comparison run as a loss process. Its parameter before round `t` is the history `(x̃, õ)` of the
  measurable hybrid `H_0` of Proposition 8.11 (`PropGAd.ACtx.hS`), which is `cmpLoss` on the case of the analysis
  (`cmpProc_loss`). The history before round `t` reads the stream at `prefixIdx … t` and the noise before `t` only, so
  it factors through the truncation `trunc t`, which is `prefixσ … t`-measurable (`hS_meas_prefix`).
* On the case, the regret of D0 in `cmpWorld` is its regret in the world of `cmpProc` (`regretPts_congr`,
  `df2zPlay_congr`), and `Df2WorldDet` reduces it to the virtual epochs and the Azuma event of that world.
-/

open MeasureTheory ProbabilityTheory
open AdversarialBco.RealRAM

namespace AdversarialBco.Poly.Conj1

open Layer2

variable {d : ℕ}

/-! ## The truncation of a world to what the run reads before round `t` -/

open Classical in
/-- The world `ω` with every term of the stream outside `prefixIdx … t` and every noise term from round `t` on set
to `0`. -/
noncomputable def trunc (N0 S n d t : ℕ) (ω : WΩ) : WΩ :=
  (fun i => if i ∈ prefixIdx N0 S n d t then ω.1 i else 0, fun j => if j < t then ω.2 j else 0)

theorem trunc_meas (N0 S n d t : ℕ) : Measurable[prefixSeq N0 S n d t] (trunc N0 S n d t) := by
  classical
  unfold trunc
  have h1 : Measurable[prefixSeq N0 S n d t] fun ω : WΩ => fun i => if i ∈ prefixIdx N0 S n d t then ω.1 i else 0 :=
    measurable_pi_of fun i => by
      by_cases hi : i ∈ prefixIdx N0 S n d t
      · simp only [hi, ↓reduceIte]
        exact meas_coord i (gσ_le_prefixSeq N0 S n d t i hi)
      · simp only [hi, ↓reduceIte]
        exact measurable_const
  have h2 : Measurable[prefixSeq N0 S n d t] fun ω : WΩ => fun j => if j < t then ω.2 j else 0 :=
    measurable_pi_of fun j => by
      by_cases hj : j < t
      · simp only [hj, ↓reduceIte]
        exact meas_noise_prefixSeq N0 S n d t j hj
      · simp only [hj, ↓reduceIte]
        exact measurable_const
  exact h1.prodMk h2

theorem blk_mem_prefixIdx (N0 S n d t u c : ℕ) (hut : u < t) (hun : u < n) (hc : c < d + 1) :
    N0 + u * (d + 1) + c ∈ prefixIdx N0 S n d t := by
  refine Or.inl ?_
  have h1 : u + 1 ≤ min t n := Nat.lt_min.mpr ⟨hut, hun⟩
  have h2 : (u + 1) * (d + 1) ≤ min t n * (d + 1) := Nat.mul_le_mul_right _ h1
  have h3 : u * (d + 1) + c < (u + 1) * (d + 1) := by rw [Nat.succ_mul]; omega
  show N0 + u * (d + 1) + c < N0 + min t n * (d + 1)
  omega

theorem trunc_fst (N0 S n d t i : ℕ) (hi : i ∈ prefixIdx N0 S n d t) (ω : WΩ) :
    (trunc N0 S n d t ω).1 i = ω.1 i := by
  classical
  simp only [trunc, hi, ↓reduceIte]

theorem trunc_snd (N0 S n d t j : ℕ) (hj : j < t) (ω : WΩ) : (trunc N0 S n d t ω).2 j = ω.2 j := by
  classical
  simp only [trunc, hj, ↓reduceIte]

/-- The stream of PG is unchanged by the truncation: PG reads `prefixIdx … t` only. -/
theorem omega_trunc (n : ℕ) (r0 R0 δ1 : ℝ) (t : ℕ) (ω : WΩ) :
    df2oOmega d n r0 R0 δ1 (trunc (df2oN0 d r0 R0 δ1) (df2oSpare d n r0 R0 δ1) n d t ω).1 =
      df2oOmega d n r0 R0 δ1 ω.1 := by
  have hW : ∀ i, df2oPgW d (df2oPgDelta r0 R0 δ1) i = pgNs d (pgRhoStage d i) +
      pgMT (df2oPgDelta r0 R0 δ1) * pgNT d (pgRhoStage d i) := fun _ => rfl
  have hA : ∀ i r k (c : Fin d),
      df2oIdxA d n r0 R0 δ1 i r k c ∈ prefixIdx (df2oN0 d r0 R0 δ1) (df2oSpare d n r0 R0 δ1) n d t :=
    fun i r k c => by
      rw [idxA_eq]
      exact mrA_mem_prefixIdx _ _ _ _ _ _ _ (fun i => pgNT d (pgRhoStage d i)) _ _ hW i r k c
  have hT : ∀ i r v k (c : Fin d),
      df2oIdxT d n r0 R0 δ1 i r v k c ∈ prefixIdx (df2oN0 d r0 R0 δ1) (df2oSpare d n r0 R0 δ1) n d t :=
    fun i r v k c => by
      rw [idxT_eq]
      exact mrT_mem_prefixIdx _ _ _ _ _ _ _ _ _ _ hW i r v k c
  funext i r
  unfold df2oOmega
  simp only [trunc_fst _ _ _ _ _ _ (hA i r _ _), trunc_fst _ _ _ _ _ _ (hT i r _ _ _)]

/-! ## The history of the hybrid `H_0` before round `t` is known before round `t` -/

section Hist

open PropGAd

variable (c : ACtx d)

/-- The first `d + 1` terms after `N0` of a round. -/
noncomputable abbrev N0c : ℕ := df2oN0 d c.r0 c.R0 c.p.δ1

/-- The spare index of the data. -/
noncomputable abbrev Sc : ℕ := df2oSpare d c.n c.r0 c.R0 c.p.δ1

theorem stepA_congr (ga : E d → ℝ) {ω ω' : WΩ} (t : ℕ) (s : HSt d) (hP : c.Ps ω = c.Ps ω')
    (hn : ω.2 t = ω'.2 t) (hx : c.xi ω t = c.xi ω' t) (hz : c.ze ω t = c.ze ω' t) :
    c.stepA ga ω t s = c.stepA ga ω' t s := by
  simp only [ACtx.stepA, ACtx.pJ, ACtx.rndA, hP, hn, hx, hz]

/-- The hybrid before round `t` reads the position, the first mode, and the noise and draws of the rounds `u < t`. -/
theorem hS_congr (k : ℕ) {ω ω' : WΩ} (hP : c.Ps ω = c.Ps ω') (h0 : c.mode0 ω = c.mode0 ω') :
    ∀ t, (∀ u < t, ω.2 u = ω'.2 u ∧ c.xi ω u = c.xi ω' u ∧ c.ze ω u = c.ze ω' u) → c.hS k ω t = c.hS k ω' t
  | 0, _ => by simp only [ACtx.hS, h0]
  | t + 1, h => by
    have ih := hS_congr k hP h0 t fun u hu => h u (by omega)
    obtain ⟨hn, hx, hz⟩ := h t (by omega)
    show c.stepA (c.hGa k t (c.Ps ω)) ω t (c.hS k ω t) = c.stepA (c.hGa k t (c.Ps ω')) ω' t (c.hS k ω' t)
    rw [ih, hP]
    exact stepA_congr c _ t _ hP hn hx hz

theorem pos_trunc (t : ℕ) (ω : WΩ) :
    df2oPos d c.n c.r0 c.R0 c.δ (c.W (trunc (N0c c) (Sc c) c.n d t ω)) = df2oPos d c.n c.r0 c.R0 c.δ (c.W ω) :=
  congrArg (pg d c.K c.r0 c.R0 c.p.δ1) (omega_trunc c.n c.r0 c.R0 c.p.δ1 t ω)

theorem Ps_trunc (t : ℕ) (ω : WΩ) : c.Ps (trunc (N0c c) (Sc c) c.n d t ω) = c.Ps ω := by
  show (df2oPos d c.n c.r0 c.R0 c.δ (c.W _)).getD 0 = (df2oPos d c.n c.r0 c.R0 c.δ (c.W ω)).getD 0
  rw [pos_trunc]

theorem mode0_trunc (t : ℕ) (ω : WΩ) : c.mode0 (trunc (N0c c) (Sc c) c.n d t ω) = c.mode0 ω := by
  show df2oMode0 d c.n c.r0 c.R0 c.δ (c.W _) = df2oMode0 d c.n c.r0 c.R0 c.δ (c.W ω)
  unfold df2oMode0
  rw [pos_trunc]

theorem xi_trunc {t u : ℕ} (hut : u < t) (hun : u < c.n) (ω : WΩ) :
    c.xi (trunc (N0c c) (Sc c) c.n d t ω) u = c.xi ω u := by
  funext j
  exact trunc_fst _ _ _ _ _ _ (blk_mem_prefixIdx _ _ _ _ _ _ _ hut hun (by omega)) ω

theorem ze_trunc {t u : ℕ} (hut : u < t) (hun : u < c.n) (ω : WΩ) :
    c.ze (trunc (N0c c) (Sc c) c.n d t ω) u = c.ze ω u := by
  show (trunc (N0c c) (Sc c) c.n d t ω).1 _ / 2 = ω.1 _ / 2
  congr 1
  exact trunc_fst _ _ _ _ _ _ (blk_mem_prefixIdx _ _ _ _ _ _ _ hut hun (by omega)) ω

/-- The hybrid `H_0` before round `t ≤ n` is measurable for the sigma-field of the run before round `t`. -/
theorem hS_meas_prefix (h : c.Hyp) {t : ℕ} (ht : t ≤ c.n) :
    Measurable[prefixSeq (N0c c) (Sc c) c.n d t] fun ω => c.hS 0 ω t := by
  have he : (fun ω => c.hS 0 ω t) = (fun ω => c.hS 0 ω t) ∘ trunc (N0c c) (Sc c) c.n d t := by
    funext ω
    refine hS_congr c 0 (Ps_trunc c t ω).symm (mode0_trunc c t ω).symm t fun u hu => ⟨?_, ?_, ?_⟩
    · exact (trunc_snd _ _ _ _ _ _ hu ω).symm
    · exact (xi_trunc c hu (by omega) ω).symm
    · exact (ze_trunc c hu (by omega) ω).symm
  rw [he]
  exact (ACtx.meas_hS h 0 t).comp (trunc_meas _ _ _ _ _)

/-! ## The comparison run as a loss process -/

theorem meas_restr (t : ℕ) :
    Measurable fun l : (ℕ → E d) × (ℕ → ℝ) => ((fun i : Fin t => l.1 i), (fun i : Fin t => l.2 i)) := by
  fun_prop

/-- The comparison run of Proposition 8.11 as a loss process: the loss of round `t` is the strategy at the history of
the rounds before `t`, read off the hybrid `H_0`. -/
noncomputable def cmpProc (h : c.Hyp) : Df2LossProc d c.n (N0c c) (Sc c) c.K where
  Λ := (ℕ → E d) × (ℕ → ℝ)
  L t l := c.σ t (fun i : Fin t => l.1 i) (fun i : Fin t => l.2 i)
  lam t ω := (c.hS 0 ω t).2
  adm _ ht _ := h.adm ht _ _
  meas t ht y hy := ((h.σ t ht).2 y (interior_subset hy)).comp (meas_restr t)
  lam_meas _ ht := (hS_meas_prefix c h ht.le).snd

variable {c}

/-- On the case, the loss process is the comparison loss at every round `t ≤ n`. -/
theorem cmpProc_loss (h : c.Hyp) {ω : WΩ} (hc : c.Case ω) {t : ℕ} (ht : t ≤ c.n) :
    (cmpProc c h).loss ω t = cmpLoss d c.n c.r0 c.R0 c.δ c.K c.σ t ω := by
  obtain ⟨hx, ho⟩ := ACtx.hS_obs h hc 0 t ht (ACtx.hS_zero h hc t ht).2
  have e1 : (fun i : Fin t => (c.hS 0 ω t).2.1 i) = fun i : Fin t => cmpPts d c.n c.r0 c.R0 c.δ c.K c.σ ω i :=
    funext fun i => hx i i.2
  have e2 : (fun i : Fin t => (c.hS 0 ω t).2.2 i) = obsAd c.σ ω.2 (cmpPts d c.n c.r0 c.R0 c.δ c.K c.σ ω) t :=
    funext fun i => ho i i.2
  show c.σ t (fun i : Fin t => (c.hS 0 ω t).2.1 i) (fun i : Fin t => (c.hS 0 ω t).2.2 i) = _
  rw [e1, e2]
  rfl

end Hist

/-! ## The regret of D0 reads the losses below `n` -/

theorem regretPts_congr (K : Set (E d)) {f f' : ℕ → E d → ℝ} {x x' : ℕ → E d} (n : ℕ)
    (hf : ∀ t < n, f t = f' t) (hx : ∀ t < n, x t = x' t) : regretPts K f x n = regretPts K f' x' n := by
  unfold regretPts
  have hs : (fun y => ∑ t ∈ Finset.range n, f t y) = fun y => ∑ t ∈ Finset.range n, f' t y :=
    funext fun y => Finset.sum_congr rfl fun t ht => by rw [hf t (Finset.mem_range.mp ht)]
  rw [hs, Finset.sum_congr rfl fun t ht => by rw [hf t (Finset.mem_range.mp ht), hx t (Finset.mem_range.mp ht)]]

theorem df2zPlay_congr (n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) (ω : WΩ) {f f' : ℕ → E d → ℝ} (t : ℕ)
    (h : ∀ u ≤ t, f u = f' u) :
    df2zPlay d n r0 R0 δ (df2World K f ω) t = df2zPlay d n r0 R0 δ (df2World K f' ω) t := by
  unfold df2zPlay
  rw [PropGAd.df2zMode_congr n r0 R0 δ K ω f f' t fun u hu => h u hu.le]
  simp only [df2zRoundAt, df2oPs, df2oPos, df2World, h t le_rfl]

/-! ## The composition -/

/-- The regret clause against a strategy from the world layer of a loss process, Lemma 8.10, Proposition 8.11,
Theorem 8.3 and the trivial bound. -/
theorem df2ORegretMeasAd_of (VE : Df2VEWorldAd) (AZ : Df2AzWorldAd) (WD : Df2WorldDet) (PG : Df2PropGAd)
    (PGT : PgThm) (_ : PgMeas) (_ : PgGoodMeas) (TR : Df2Trivial) : Df2ORegretMeasAd := by
  refine ⟨10 ^ 22, ?_⟩
  intro d hd n hn r0 R0 δ hr0 hr0R0 hδ0 hδ1 K hKc hKcv hball hKR σ hσ ν hν
  have := hν.1
  have h0K : (0 : E d) ∈ K := hball (Metric.mem_closedBall_self hr0.le)
  have hδ1pos := par_δ1_pos d n δ hd hn hδ0
  have hδ1le := par_δ1_le d n δ
  set x : WΩ → ℕ → E d := fun ω => df2oPlayAd n r0 R0 δ K σ ω.2 ω.1 with hxdef
  have hxfix : ∀ ω t, x ω t = df2oPlay d n r0 R0 δ (df2World K (lossAd σ ω.2 (x ω)) ω) t :=
    fun ω t => df2oPlayAd_fix n r0 R0 δ K σ ω.2 ω.1 t
  set thr := (10 : ℝ) ^ 22 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n * Real.log (2 * d * n / δ) ^ 5 with hthr
  show (gaussStream.prod ν) {ω : WΩ | thr < regretPts K (lossAd σ ω.2 (x ω)) (x ω) n} ≤ ENNReal.ofReal δ
  by_cases heps : (df2oPar d n δ).eps ≤ 1 / 2
  swap
  · -- outside the regime the regret is at most `n ≤ thr`
    have hn' := comp_trivial TR d n δ hd hn hδ0 hδ1 (lt_of_not_ge heps)
    have : {ω : WΩ | thr < regretPts K (lossAd σ ω.2 (x ω)) (x ω) n} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have := regret_le_n K n _ (lossAd_mem hσ ω.2 (x ω)) (x ω)
        (fun t _ => hxfix ω t ▸ Layer2.df2oPlay_mem n r0 R0 δ (df2World K (lossAd σ ω.2 (x ω)) ω) h0K t) ⟨0, h0K⟩
      linarith
    rw [this, measure_empty]
    simp
  -- the regime
  set B := 2 * ((df2oPar d n δ).rho / (df2oPar d n δ).eta) + n * (df2oPar d n δ).eps +
    Real.sqrt (2 * n * Real.log (7 / (df2oPar d n δ).δe)) with hB
  have RH := rowHyp_of d n δ hd hn hδ0 hδ1 heps
  have hBt : B + 1 ≤ thr := comp_thresh _ d n δ RH hδ0 hδ1 rfl rfl
  set μ := gaussStream.prod ν with hμ
  have hbody : Df2BodyHyp d n r0 R0 δ K := ⟨hd, hn, hr0, hr0R0, hδ0, hδ1, hKc, hKcv, hball, hKR⟩
  -- the bad positions
  set S : Set (ℕ → ℕ → PgRound d) := {y | ¬ PgGood d K (134 * d * Real.sqrt (Real.log (2 * d + 2)))
    (pg d K r0 R0 (df2oPar d n δ).δ1 y)} with hS
  have hpos : μ {ω | ¬ Df2Case d n r0 R0 δ (df2World K (lossAd σ ω.2 (x ω)) ω)} ≤
      ENNReal.ofReal (df2oPar d n δ).δ1 := by
    have hsub : {ω : WΩ | ¬ Df2Case d n r0 R0 δ (df2World K (lossAd σ ω.2 (x ω)) ω)} ⊆
        (df2oOmega d n r0 R0 (df2oPar d n δ).δ1 ⁻¹' S) ×ˢ Set.univ := by
      intro ω hω
      exact ⟨fun hg => hω ⟨hg, heps⟩, Set.mem_univ _⟩
    calc μ _ ≤ μ ((df2oOmega d n r0 R0 (df2oPar d n δ).δ1 ⁻¹' S) ×ˢ Set.univ) := measure_mono hsub
      _ = gaussStream (df2oOmega d n r0 R0 (df2oPar d n δ).δ1 ⁻¹' S) := by
          rw [hμ, Measure.prod_prod, measure_univ, mul_one]
      _ ≤ (gaussStream.map (df2oOmega d n r0 R0 (df2oPar d n δ).δ1)) S :=
          Measure.le_map_apply (df2oOmega_measurable d n r0 R0 _).aemeasurable S
      _ = pgMeasure d S := by rw [df2oOmega_law]
      _ ≤ ENNReal.ofReal (df2oPar d n δ).δ1 :=
          PGT d K r0 R0 _ hd hKcv hKc.isClosed hr0 hr0R0 hball hKR hδ1pos (by linarith)
  -- the comparison run as a loss process
  let c : PropGAd.ACtx d := ⟨⟨n, r0, R0, δ, K, fun _ _ => 0⟩, σ⟩
  have h : c.Hyp := ⟨⟨hd, hn, hr0, hr0R0, hδ0, hδ1, hKc, hKcv, hball, hKR,
    fun _ _ => ⟨convexOn_const 0 hKcv, fun _ _ => ⟨le_rfl, zero_le_one⟩⟩⟩, hσ, PropGAd.caraInterior⟩
  let F : Df2LossProcOf d n r0 R0 δ K := cmpProc c h
  -- D0 in the comparison world, in the case of the analysis
  have hD0 : μ {ω | Df2Case d n r0 R0 δ (cmpWorld d n r0 R0 δ K σ ω) ∧
      B < regretPts K (fun t => cmpLoss d n r0 R0 δ K σ t ω) (df2zPlay d n r0 R0 δ (cmpWorld d n r0 R0 δ K σ ω)) n} ≤
      ∑ a ∈ Finset.range n, ENNReal.ofReal (149 / 168 * (df2oPar d n δ).δe) +
        ENNReal.ofReal ((df2oPar d n δ).δe / 7) := by
    have hsub : {ω | Df2Case d n r0 R0 δ (cmpWorld d n r0 R0 δ K σ ω) ∧
        B < regretPts K (fun t => cmpLoss d n r0 R0 δ K σ t ω)
          (df2zPlay d n r0 R0 δ (cmpWorld d n r0 R0 δ K σ ω)) n} ⊆
        (⋃ a ∈ Finset.range n, {ω | Df2Case d n r0 R0 δ (df2World K (F.loss ω) ω) ∧
          ¬ (df2zCtx d n r0 R0 δ (df2World K (F.loss ω) ω)).EpochOK
            (df2zPath d n r0 R0 δ (df2World K (F.loss ω) ω) a) (n - a)}) ∪
        {ω | Df2Case d n r0 R0 δ (df2World K (F.loss ω) ω) ∧ ¬ Df2AzPath d n r0 R0 δ (df2World K (F.loss ω) ω)} := by
      rintro ω ⟨hc, hlt⟩
      have hc' : c.Case ω := hc
      have hcF : Df2Case d n r0 R0 δ (df2World K (F.loss ω) ω) := hc
      have hf : ∀ t ≤ n, cmpLoss d n r0 R0 δ K σ t ω = F.loss ω t := fun t ht => (cmpProc_loss h hc' ht).symm
      have hreg : regretPts K (fun t => cmpLoss d n r0 R0 δ K σ t ω)
          (df2zPlay d n r0 R0 δ (cmpWorld d n r0 R0 δ K σ ω)) n =
          regretPts K (F.loss ω) (df2zPlay d n r0 R0 δ (df2World K (F.loss ω) ω)) n :=
        regretPts_congr K n (fun t ht => hf t ht.le)
          (fun t ht => df2zPlay_congr n r0 R0 δ K ω t fun u hu => hf u (by omega))
      by_contra hno
      simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_range, not_or, not_exists,
        not_and, not_not] at hno
      have hW : Df2WorldHyp d n r0 R0 δ K (F.loss ω) :=
        ⟨hd, hn, hr0, hr0R0, hδ0, hδ1, hKc, hKcv, hball, hKR, F.loss_mem ω⟩
      have := WD d n r0 R0 δ K (F.loss ω) hW (df2World K (F.loss ω) ω) rfl rfl hcF
        (fun a ha => hno.1 a ha hcF) (hno.2 hcF)
      linarith
    calc _ ≤ _ := measure_mono hsub
      _ ≤ μ (⋃ a ∈ Finset.range n, {ω | Df2Case d n r0 R0 δ (df2World K (F.loss ω) ω) ∧
            ¬ (df2zCtx d n r0 R0 δ (df2World K (F.loss ω) ω)).EpochOK
              (df2zPath d n r0 R0 δ (df2World K (F.loss ω) ω) a) (n - a)}) +
          μ {ω | Df2Case d n r0 R0 δ (df2World K (F.loss ω) ω) ∧
            ¬ Df2AzPath d n r0 R0 δ (df2World K (F.loss ω) ω)} :=
          measure_union_le _ _
      _ ≤ _ := by
          gcongr
          · refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun a ha => ?_)
            exact VE d n r0 R0 δ K hbody F ν hν a (Finset.mem_range.mp ha)
          · exact AZ d n r0 R0 δ K hbody F ν hν
  -- Proposition 8.11: DJ against the strategy, to D0 in the comparison world
  have hG := PG d n r0 R0 δ K σ ⟨hd, hn, hr0, hr0R0, hδ0, hδ1, hKc, hKcv, hball, hKR, hσ⟩ ν hν B x
    (fun ω t _ => hxfix ω t)
  have hsub : {ω : WΩ | thr < regretPts K (lossAd σ ω.2 (x ω)) (x ω) n} ⊆
      {ω | ¬ Df2Case d n r0 R0 δ (df2World K (lossAd σ ω.2 (x ω)) ω)} ∪
        {ω | Df2Case d n r0 R0 δ (df2World K (lossAd σ ω.2 (x ω)) ω) ∧
          B + 1 < regretPts K (lossAd σ ω.2 (x ω)) (x ω) n} := by
    intro ω hω
    by_cases hc : Df2Case d n r0 R0 δ (df2World K (lossAd σ ω.2 (x ω)) ω)
    · exact Or.inr ⟨hc, lt_of_le_of_lt hBt hω⟩
    · exact Or.inl hc
  have he0 : 0 ≤ (df2oPar d n δ).δe := by
    show 0 ≤ 4 * (df2oPar d n δ).δ1 / (5 * n)
    positivity
  calc μ _ ≤ μ {ω | ¬ Df2Case d n r0 R0 δ (df2World K (lossAd σ ω.2 (x ω)) ω)} +
        μ {ω | Df2Case d n r0 R0 δ (df2World K (lossAd σ ω.2 (x ω)) ω) ∧
          B + 1 < regretPts K (lossAd σ ω.2 (x ω)) (x ω) n} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (df2oPar d n δ).δ1 + ((∑ a ∈ Finset.range n, ENNReal.ofReal (149 / 168 * (df2oPar d n δ).δe) +
          ENNReal.ofReal ((df2oPar d n δ).δe / 7)) + ENNReal.ofReal (df2oPar d n δ).δ1) := by
        gcongr
        exact hG.trans (by gcongr)
    _ = ENNReal.ofReal (2 * (df2oPar d n δ).δ1 + n * (149 / 168 * (df2oPar d n δ).δe) +
          (df2oPar d n δ).δe / 7) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal (comp_prob d n δ hd hn hδ0)

end AdversarialBco.Poly.Conj1
