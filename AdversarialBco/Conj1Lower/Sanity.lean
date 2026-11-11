/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1Lower
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Sanity checks of the statement `TheoremConj1Lower` (AdversarialBco/StatementConj1Lower.lean)

* The hypotheses are satisfiable together: `d = 4·10^6`, `n = d^10`, the constant learner on the seed space `Unit`
  (`hyps_satisfiable`, `constLearner_mem`). So the claim speaks of at least one learner for every `d` and `n`.
* The bound is positive (`bound_pos`) and at most `n/2` (`bound_le_half`), while the regret of every learner of the
  class against every strategy of the class is at most `n/2` (`regretAd_le_half`): the claim is not false by size.
* The existential is not witnessed for free: the zero strategy is in the class (`zeroStrat_mem`), its regret is `0`
  for every play rule (`regretAd_zero`), so it fails the conclusion against every learner (`zeroStrat_fails`).
* The class of strategies contains a nonconstant loss (`normStrat_mem`, `normStrat_nonconst`) and a strategy that
  reads the plays (`chase_mem`, `chase_reads`).
* The run: the transcript's points are the points played (`transcript_fst`), its observations are those of
  `obsAd` (`transcript_snd`), the losses of the regret are the losses the learner faced (`lossAd_plays`), and the
  observation of round `t` is the loss of round `t` at the point of round `t` plus the noise (`obs_last`).
  Non-anticipation: the loss of round `t` reads the points before `t` only (`lossAd_congr`), and the point of round
  `t` reads the strategy of the rounds before `t` only (`plays_congr`). The points of the rounds `t < n` of a rule of
  the class are in `K` (`plays_mem`).
* One model with `TheoremConj1Upper`: the unit ball meets its body hypotheses at `r₀ = R₀ = 1`, the class of the lower
  bound is inside `Strats`, and the noiseless game is its noise law `dirac 0` (`upper_instance`, `noiseOK_dirac`).
* Integrability is automatic on the class (`integrable_regretAd`): for
  every strategy of `StratsLip` and every learner of `IsLearnerAd` on the unit ball, the regret is integrable. The
  transcript is measurable in the seed (`measurable_transcript`); the loss at the point played is measurable since a
  strategy of the class, read at `clip y`, is measurable in the history and continuous in `y`, hence jointly
  measurable (`measurable_strat_clip`); the comparator `sInf` over the ball is an infimum over a dense sequence
  (`sInf_image_eq_iInf`, `exists_dense_ball`); and `|regret| ≤ n`.
* A learner that randomises at every round (m4): `gaussLearner`, seeds `ℕ → ℝ` under `gaussStream`, plays
  `clip (ω t • e)` in round `t`; it is a learner of the class (`gaussLearner_mem`), its play of round `t` changes with
  the draw `ω t` alone (`gaussLearner_fresh`), and the hypotheses and the conjunct `Integrable` hold for it
  (`gaussLearner_hyps`).
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Lower.Sanity

open RealRAM

variable {d : ℕ}

/-! ## The run -/

/-- The points of the transcript are the points played. -/
theorem transcript_fst (σ : Strategy d) (ε : ℕ → ℝ) (p : Policy d) :
    ∀ t, (transcript σ ε p t).1 = fun i : Fin t => plays σ ε p i
  | 0 => funext fun i => i.elim0
  | t + 1 => by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [transcript, plays]
    · simp [transcript, transcript_fst σ ε p t]

/-- The observations of the transcript are those of `obsAd` at the points played. -/
theorem transcript_snd (σ : Strategy d) (ε : ℕ → ℝ) (p : Policy d) :
    ∀ t, (transcript σ ε p t).2 = obsAd σ ε (plays σ ε p) t
  | 0 => funext fun i => i.elim0
  | t + 1 => by
    have ih := transcript_snd σ ε p t
    have hf := transcript_fst σ ε p t
    simp only [transcript, obsAd]
    rw [← ih, ← hf]
    rfl

/-- The losses of the regret are the losses the learner faced: the loss of round `t` at the points played is the loss
that `σ` chose from the transcript before round `t`. -/
theorem lossAd_plays (σ : Strategy d) (ε : ℕ → ℝ) (p : Policy d) (t : ℕ) :
    lossAd σ ε (plays σ ε p) t = σ t (transcript σ ε p t).1 (transcript σ ε p t).2 := by
  rw [transcript_fst, transcript_snd]
  rfl

/-- The observation of round `t` is the loss of round `t` at the point of round `t`, plus the noise. -/
theorem obs_last (σ : Strategy d) (ε : ℕ → ℝ) (p : Policy d) (t : ℕ) :
    (transcript σ ε p (t + 1)).2 (Fin.last t) = lossAd σ ε (plays σ ε p) t (plays σ ε p t) + ε t := by
  rw [lossAd_plays]
  simp [transcript, plays]

/-- The observations of the rounds before `t` read the points of the rounds before `t` only. -/
theorem obsAd_congr (σ : Strategy d) (ε : ℕ → ℝ) {x y : ℕ → E d} :
    ∀ t, (∀ i < t, x i = y i) → obsAd σ ε x t = obsAd σ ε y t
  | 0, _ => rfl
  | t + 1, h => by
    have ih := obsAd_congr σ ε t fun i hi => h i (by omega)
    have hx : (fun i : Fin t => x i) = fun i : Fin t => y i := funext fun i => h i (by omega)
    simp only [obsAd, ih, hx, h t (by omega)]

/-- Non-anticipation of the strategy: the loss of round `t` reads the points of the rounds before `t` only. -/
theorem lossAd_congr (σ : Strategy d) (ε : ℕ → ℝ) {x y : ℕ → E d} (t : ℕ) (h : ∀ i < t, x i = y i) :
    lossAd σ ε x t = lossAd σ ε y t := by
  have hx : (fun i : Fin t => x i) = fun i : Fin t => y i := funext fun i => h i i.2
  simp only [lossAd, obsAd_congr σ ε t h, hx]

/-- The transcript of the rounds before `t` reads the strategy of the rounds before `t` only. -/
theorem transcript_congr {σ σ' : Strategy d} (ε : ℕ → ℝ) (p : Policy d) :
    ∀ t, (∀ u < t, σ u = σ' u) → transcript σ ε p t = transcript σ' ε p t
  | 0, _ => rfl
  | t + 1, h => by
    have ih := transcript_congr ε p t fun u hu => h u (by omega)
    simp only [transcript, ih, h t (by omega)]

/-- Non-anticipation of the learner: the point of round `t` reads the strategy of the rounds before `t` only, that is
the losses of the rounds before `t`. -/
theorem plays_congr {σ σ' : Strategy d} (ε : ℕ → ℝ) (p : Policy d) (t : ℕ) (h : ∀ u < t, σ u = σ' u) :
    plays σ ε p t = plays σ' ε p t := by
  simp only [plays, transcript_congr ε p t h]

/-- The points of the rounds `t < n` of a rule with values in `K` are in `K`. -/
theorem plays_mem {K : Set (E d)} {n : ℕ} (σ : Strategy d) (ε : ℕ → ℝ) (p : Policy d)
    (hp : ∀ t < n, ∀ x o, p t x o ∈ K) {t : ℕ} (ht : t < n) : plays σ ε p t ∈ K :=
  hp t ht _ _

/-! ## The hypotheses -/

/-- The constant learner, on the seed space `Unit`, plays the centre of the ball at every round; it is a learner of
the class for every `n`. -/
theorem constLearner_mem (n : ℕ) :
    IsLearnerAd (Ω := Unit) (Metric.closedBall (0 : E d) 1) n (fun _ _ _ _ => 0) :=
  fun _ _ => ⟨measurable_const, fun _ _ _ => Metric.mem_closedBall_self zero_le_one⟩

/-- The hypotheses of `TheoremConj1Lower` hold together: `d = 4·10^6`, `n = d^10`, the seed space `Unit` with its Dirac
measure, and the constant learner. -/
theorem hyps_satisfiable :
    ∃ d n : ℕ, 4000000 ≤ d ∧ d ^ 10 ≤ n ∧ IsProbabilityMeasure (Measure.dirac ()) ∧
      IsLearnerAd (Ω := Unit) (Metric.closedBall (0 : E d) 1) n (fun _ _ _ _ => 0) :=
  ⟨4000000, 4000000 ^ 10, le_rfl, le_rfl, inferInstance, constLearner_mem _⟩

/-! ## The bound -/

theorem log_ge_one {d : ℕ} (hd : 4000000 ≤ d) : 1 ≤ Real.log d := by
  have hd' : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- The bound of `TheoremConj1Lower` is positive. -/
theorem bound_pos {d n : ℕ} (hd : 4000000 ≤ d) (hn : 1 ≤ n) :
    0 < 7 / 10 ^ 9 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d := by
  have hd' : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog := log_ge_one hd
  have h1 : 0 < (d : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have h2 : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have h3 : 0 < Real.log d := by linarith
  positivity

/-- The bound of `TheoremConj1Lower` is at most `n/2` in its range. -/
theorem bound_le_half {d n : ℕ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) :
    7 / 10 ^ 9 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤ n / 2 := by
  have hd' : (4000000 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : ((d : ℝ) ^ 10) ≤ n := by exact_mod_cast hn
  have hlog := log_ge_one hd
  have hd1 : (1 : ℝ) ≤ d := by linarith
  have h32 : (d : ℝ) ^ (3 / 2 : ℝ) ≤ (d : ℝ) ^ 5 := by
    calc (d : ℝ) ^ (3 / 2 : ℝ) ≤ (d : ℝ) ^ (5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num)
      _ = (d : ℝ) ^ 5 := by norm_cast
  have h5 : (d : ℝ) ^ 5 ≤ Real.sqrt n := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    calc ((d : ℝ) ^ 5) ^ 2 = (d : ℝ) ^ 10 := by ring
      _ ≤ (n : ℝ) := hn'
  have hs : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (by positivity)
  have hpos : 0 ≤ 7 / 10 ^ 9 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n := by positivity
  calc 7 / 10 ^ 9 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d
      ≤ 7 / 10 ^ 9 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n := div_le_self hpos hlog
    _ ≤ 7 / 10 ^ 9 * Real.sqrt n * Real.sqrt n := by
        have := mul_le_mul_of_nonneg_right (h32.trans h5) hs
        nlinarith
    _ = 7 / 10 ^ 9 * n := by rw [mul_assoc, hsq]
    _ ≤ n / 2 := by
        have : (0 : ℝ) ≤ n := by positivity
        linarith

/-- The regret of a rule with values in the unit ball against a strategy of the class is at most `n/2`: each round
costs at most `1/4` times the diameter `2`. -/
theorem regretAd_le_half {n : ℕ} {σ : Strategy d} (hσ : σ ∈ StratsLip (Metric.closedBall (0 : E d) 1) n)
    (p : Policy d) (hp : ∀ t < n, ∀ x o, p t x o ∈ Metric.closedBall (0 : E d) 1) :
    regretAd (Metric.closedBall 0 1) σ p n ≤ n / 2 := by
  set K := Metric.closedBall (0 : E d) 1
  set x := plays σ (fun _ => 0) p
  set f := lossAd σ (fun _ => 0) x
  have hne : ((fun y => ∑ t ∈ Finset.range n, f t y) '' K).Nonempty :=
    (Set.nonempty_of_mem (Metric.mem_closedBall_self zero_le_one)).image _
  have key : ∀ y ∈ K, ∑ t ∈ Finset.range n, f t (x t) - n / 2 ≤ ∑ t ∈ Finset.range n, f t y := by
    intro y hy
    have h : ∀ t ∈ Finset.range n, f t (x t) - 1 / 2 ≤ f t y := by
      intro t ht
      have htn := Finset.mem_range.1 ht
      have hxt : x t ∈ K := plays_mem σ _ p hp htn
      have hlip := ((hσ.2 t htn (fun i : Fin t => x i) (obsAd σ (fun _ => 0) x t)
        (obsAd σ (fun _ => 0) x t)).2 (x t) hxt y hy)
      have hdist : dist (x t) y ≤ 2 := by
        calc dist (x t) y ≤ dist (x t) 0 + dist 0 y := dist_triangle _ _ _
          _ ≤ 1 + 1 := by
            gcongr
            · exact Metric.mem_closedBall.1 hxt
            · rw [dist_comm]; exact Metric.mem_closedBall.1 hy
          _ = 2 := by norm_num
      have : f t (x t) - f t y ≤ 1 / 2 := by
        have := (abs_le.1 hlip).2
        simp only [f, lossAd] at this ⊢
        linarith
      linarith
    have := Finset.sum_le_sum h
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    linarith
  have hle : ∑ t ∈ Finset.range n, f t (x t) - n / 2 ≤ sInf ((fun y => ∑ t ∈ Finset.range n, f t y) '' K) :=
    le_csInf hne (by rintro _ ⟨y, hy, rfl⟩; exact key y hy)
  show ∑ t ∈ Finset.range n, f t (x t) - sInf ((fun y => ∑ t ∈ Finset.range n, f t y) '' K) ≤ n / 2
  linarith

/-! ## The zero strategy does not witness the claim -/

/-- The zero strategy: the loss `0` at every round. -/
def zeroStrat (d : ℕ) : Strategy d := fun _ _ _ _ => 0

theorem zeroStrat_mem {K : Set (E d)} (hK : Convex ℝ K) (n : ℕ) : zeroStrat d ∈ StratsLip K n := by
  refine ⟨fun t _ => ⟨fun x o => ⟨convexOn_const 0 hK, fun _ _ => ⟨le_rfl, zero_le_one⟩⟩,
    fun _ _ => measurable_const⟩, fun t _ x o o' => ⟨rfl, fun y _ z _ => ?_⟩⟩
  simp only [zeroStrat, sub_self, abs_zero]
  positivity

/-- The regret against the zero strategy is `0`, for every play rule. -/
theorem regretAd_zero {K : Set (E d)} (hK : K.Nonempty) (p : Policy d) (n : ℕ) :
    regretAd K (zeroStrat d) p n = 0 := by
  have h : (fun y => ∑ t ∈ Finset.range n, lossAd (zeroStrat d) (fun _ => 0)
      (plays (zeroStrat d) (fun _ => 0) p) t y) '' K = {0} := by
    simp only [lossAd, zeroStrat, Finset.sum_const_zero]
    exact hK.image_const 0
  unfold regretAd regretPts
  rw [h, csInf_singleton]
  simp [lossAd, zeroStrat]

/-- The zero strategy fails the conclusion of `TheoremConj1Lower` against every learner. -/
theorem zeroStrat_fails {d n : ℕ} (hd : 4000000 ≤ d) (hn : d ^ 10 ≤ n) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (pol : Lower.Learner Ω d) :
    ¬ 7 / 10 ^ 9 * (d : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt n / Real.log d ≤
        ∫ ω, regretAd (Metric.closedBall 0 1) (zeroStrat d) (fun t => pol t ω) n ∂μ := by
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_pow _ _ (by omega)) hn
  have hpos := bound_pos hd hn1
  have h0 : (fun ω => regretAd (Metric.closedBall (0 : E d) 1) (zeroStrat d) (fun t => pol t ω) n) = fun _ => 0 :=
    funext fun ω => regretAd_zero ⟨0, Metric.mem_closedBall_self zero_le_one⟩ _ n
  rw [h0, integral_zero]
  linarith

/-! ## The class contains a nonconstant loss and a strategy that reads the plays -/

/-- The loss `1/2 + ‖y‖/4` at every round. -/
noncomputable def normStrat (d : ℕ) : Strategy d := fun _ _ _ y => 1 / 2 + ‖y‖ / 4

theorem normStrat_mem (n : ℕ) : normStrat d ∈ StratsLip (Metric.closedBall (0 : E d) 1) n := by
  have hK : Convex ℝ (Metric.closedBall (0 : E d) 1) := convex_closedBall _ _
  refine ⟨fun t _ => ⟨fun x o => ⟨?_, fun y hy => ?_⟩, fun _ _ => measurable_const⟩,
    fun t _ x o o' => ⟨rfl, fun y _ z _ => ?_⟩⟩
  · have h := (convexOn_const (1 / 2 : ℝ) hK).add ((convexOn_norm hK).smul (by norm_num : (0 : ℝ) ≤ 1 / 4))
    refine h.congr fun y _ => ?_
    simp only [normStrat, smul_eq_mul, Pi.add_apply]
    ring
  · have h1 := Metric.mem_closedBall.1 hy
    rw [dist_zero_right] at h1
    simp only [normStrat, Set.mem_Icc]
    constructor <;> nlinarith [norm_nonneg y]
  · simp only [normStrat, dist_eq_norm]
    rw [show 1 / 2 + ‖y‖ / 4 - (1 / 2 + ‖z‖ / 4) = (‖y‖ - ‖z‖) / 4 by ring, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    gcongr
    exact abs_norm_sub_norm_le y z

/-- The loss of `normStrat` is not constant on the unit ball, in every dimension `d ≥ 1`. -/
theorem normStrat_nonconst (hd : 1 ≤ d) (t : ℕ) (x : Fin t → E d) (o : Fin t → ℝ) :
    ∃ y ∈ Metric.closedBall (0 : E d) 1, ∃ z ∈ Metric.closedBall (0 : E d) 1,
      normStrat d t x o y ≠ normStrat d t x o z := by
  refine ⟨0, Metric.mem_closedBall_self zero_le_one, EuclideanSpace.single ⟨0, hd⟩ 1, ?_, ?_⟩
  · simp [Metric.mem_closedBall]
  · simp only [normStrat, norm_zero]
    have hn : ‖(EuclideanSpace.single ⟨0, hd⟩ (1 : ℝ) : E d)‖ = 1 := by simp
    rw [hn]
    norm_num

/-- The clip of a point to the unit ball, `v / max 1 ‖v‖`. -/
noncomputable def clip (v : E d) : E d := (max 1 ‖v‖)⁻¹ • v

theorem norm_clip_le (v : E d) : ‖clip v‖ ≤ 1 := by
  have hm : 0 < max 1 ‖v‖ := lt_of_lt_of_le one_pos (le_max_left _ _)
  rw [clip, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hm, inv_mul_le_iff₀ hm, mul_one]
  exact le_max_right _ _

theorem continuous_clip : Continuous (clip : E d → E d) := by
  unfold clip
  exact (continuous_const.max continuous_norm).inv₀ (fun v => (lt_of_lt_of_le one_pos (le_max_left _ _)).ne')
    |>.smul continuous_id

/-- A strategy that reads the plays: from round `1` on, the linear loss `1/2 + ⟪c, y⟫/4`, with `c` the last point
played clipped to the unit ball. -/
noncomputable def chase (d : ℕ) : Strategy d := fun t x _ y =>
  if h : 0 < t then 1 / 2 + inner ℝ (clip (x ⟨t - 1, by omega⟩)) y / 4 else 1 / 2

theorem chase_mem (n : ℕ) : chase d ∈ StratsLip (Metric.closedBall (0 : E d) 1) n := by
  have hK : Convex ℝ (Metric.closedBall (0 : E d) 1) := convex_closedBall _ _
  refine ⟨fun t _ => ⟨fun x o => ⟨?_, fun y hy => ?_⟩, fun y _ => ?_⟩, fun t _ x o o' => ⟨rfl, fun y _ z _ => ?_⟩⟩
  · unfold chase
    split_ifs with h
    · refine ⟨hK, fun a _ b _ r s _ _ hrs => le_of_eq ?_⟩
      simp only [smul_eq_mul, inner_add_right, inner_smul_right]
      have : r * (1 / 2) + s * (1 / 2) = 1 / 2 := by rw [← add_mul, hrs, one_mul]
      linear_combination (-1 : ℝ) * this
    · exact convexOn_const _ hK
  · have h1 : ‖y‖ ≤ 1 := by simpa using Metric.mem_closedBall.1 hy
    unfold chase
    split_ifs with h
    · have hc := norm_clip_le (x ⟨t - 1, by omega⟩)
      have hi := abs_real_inner_le_norm (clip (x ⟨t - 1, by omega⟩)) y
      have : ‖clip (x ⟨t - 1, by omega⟩)‖ * ‖y‖ ≤ 1 := by nlinarith [norm_nonneg y, norm_nonneg (clip (x ⟨t - 1, by omega⟩))]
      have := abs_le.1 (hi.trans this)
      constructor <;> linarith [this.1, this.2]
    · norm_num
  · unfold chase
    split_ifs with h
    · have hc : Continuous fun v : E d => 1 / 2 + inner ℝ (clip v) y / 4 :=
        continuous_const.add ((continuous_clip.inner continuous_const).div_const _)
      exact hc.measurable.comp ((measurable_pi_apply _).comp measurable_fst)
    · exact measurable_const
  · unfold chase
    split_ifs with h
    · have hc := norm_clip_le (x ⟨t - 1, by omega⟩)
      rw [show 1 / 2 + inner ℝ (clip (x ⟨t - 1, by omega⟩)) y / 4 - (1 / 2 + inner ℝ (clip (x ⟨t - 1, by omega⟩)) z / 4)
          = inner ℝ (clip (x ⟨t - 1, by omega⟩)) (y - z) / 4 by rw [inner_sub_right]; ring,
        abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4), dist_eq_norm]
      gcongr
      calc |inner ℝ (clip (x ⟨t - 1, by omega⟩)) (y - z)| ≤ ‖clip (x ⟨t - 1, by omega⟩)‖ * ‖y - z‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ 1 * ‖y - z‖ := by gcongr
        _ = ‖y - z‖ := one_mul _
    · simp only [sub_self, abs_zero]
      positivity

/-- `chase` reads the plays: in round `1`, at the point `e = (1, 0, ..., 0)`, its loss is `1/2` after the play `0`
and `3/4` after the play `e`. -/
theorem chase_reads (hd : 1 ≤ d) (o : Fin 1 → ℝ) :
    chase d 1 (fun _ => 0) o (EuclideanSpace.single ⟨0, hd⟩ 1) = 1 / 2 ∧
      chase d 1 (fun _ => EuclideanSpace.single ⟨0, hd⟩ 1) o (EuclideanSpace.single ⟨0, hd⟩ 1) = 3 / 4 := by
  have hn : ‖(EuclideanSpace.single ⟨0, hd⟩ (1 : ℝ) : E d)‖ = 1 := by
    simp
  constructor
  · simp [chase, clip]
  · simp only [chase, clip, hn, max_self, inv_one, one_smul, Nat.one_pos, dite_true]
    rw [real_inner_self_eq_norm_sq, hn]
    norm_num

/-! ## One model with `TheoremConj1Upper` -/

theorem pastNoise_le (t : ℕ) : pastNoise t ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
  (Measurable.of_eval fun i : Fin t => measurable_pi_apply (i : ℕ)).comap_le

/-- The noiseless game satisfies the noise hypothesis of `TheoremConj1Upper`. -/
theorem noiseOK_dirac : NoiseOK (Measure.dirac (0 : ℕ → ℝ)) := by
  refine ⟨inferInstance, fun t => ⟨?_, ?_, ?_⟩⟩
  · have hm : Measurable fun ε : ℕ → ℝ => Real.exp (ε t ^ 2) :=
      Real.measurable_exp.comp ((measurable_pi_apply t).pow_const 2)
    exact integrable_dirac' hm.stronglyMeasurable enorm_lt_top
  · have h : (fun ε : ℕ → ℝ => ε t) =ᵐ[Measure.dirac 0] 0 := by
      filter_upwards [ae_eq_dirac' (a := (0 : ℕ → ℝ)) (measurable_pi_apply t)] with ε hε
      simpa using hε
    exact (condExp_congr_ae h).trans (by rw [condExp_zero])
  · have hm : Measurable fun ε : ℕ → ℝ => Real.exp (ε t ^ 2) :=
      Real.measurable_exp.comp ((measurable_pi_apply t).pow_const 2)
    have h : (fun ε : ℕ → ℝ => Real.exp (ε t ^ 2)) =ᵐ[Measure.dirac 0] fun _ => (1 : ℝ) := by
      filter_upwards [ae_eq_dirac' (a := (0 : ℕ → ℝ)) hm] with ε hε
      simpa using hε
    filter_upwards [condExp_congr_ae (m := pastNoise t) h] with ε hε
    rw [hε, condExp_const (pastNoise_le t)]
    norm_num

/-- The game of `TheoremConj1Lower` is an instance of that of `TheoremConj1Upper`: the unit ball meets the body
hypotheses at `r₀ = R₀ = 1`, every strategy of the class is in `Strats`, the noise law `dirac 0` meets `NoiseOK`, and
the regret is `regretPts` of the losses `lossAd` with the noise `0`. -/
theorem upper_instance (n : ℕ) :
    IsCompact (Metric.closedBall (0 : E d) 1) ∧ Convex ℝ (Metric.closedBall (0 : E d) 1) ∧
      Metric.closedBall (0 : E d) 1 ⊆ Metric.closedBall 0 1 ∧ (0 : ℝ) < 1 ∧
      StratsLip (Metric.closedBall (0 : E d) 1) n ⊆ Strats (Metric.closedBall (0 : E d) 1) n ∧
      NoiseOK (Measure.dirac (0 : ℕ → ℝ)) ∧
      ∀ (σ : Strategy d) (p : Policy d), regretAd (Metric.closedBall 0 1) σ p n =
        regretPts (Metric.closedBall 0 1) (lossAd σ (fun _ => 0) (plays σ (fun _ => 0) p))
          (plays σ (fun _ => 0) p) n :=
  ⟨isCompact_closedBall _ _, convex_closedBall _ _, subset_rfl, one_pos, fun _ hσ => hσ.1, noiseOK_dirac,
    fun _ _ => rfl⟩


/-! ## Integrability over the class -/

theorem clip_mem (v : E d) : clip v ∈ Metric.closedBall (0 : E d) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right]; exact norm_clip_le v

theorem clip_of_mem {v : E d} (hv : v ∈ Metric.closedBall (0 : E d) 1) : clip v = v := by
  have h1 : ‖v‖ ≤ 1 := by simpa using Metric.mem_closedBall.1 hv
  simp [clip, max_eq_left h1]

/-- A loss with `|f y - f z| ≤ dist y z / 4` on `K` is continuous on `K`. -/
theorem continuousOn_of_lip {K : Set (E d)} {f : E d → ℝ} (hf : ∀ y ∈ K, ∀ z ∈ K, |f y - f z| ≤ dist y z / 4) :
    ContinuousOn f K := by
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  refine ⟨ε, hε, fun a ha hab => ?_⟩
  rw [Real.dist_eq]
  have := hf a ha b hb
  have h0 : 0 ≤ dist a b := dist_nonneg
  linarith

/-- The `sInf` over a set of a function continuous on it is the infimum over a dense sequence of the set. -/
theorem sInf_image_eq_iInf {K : Set (E d)} (u : ℕ → E d) (hu : ∀ i, u i ∈ K) (hd : K ⊆ closure (Set.range u))
    (F : E d → ℝ) (hF : ContinuousOn F K) (hb : ∀ y ∈ K, 0 ≤ F y) :
    sInf (F '' K) = ⨅ i, F (u i) := by
  have hbdd : BddBelow (F '' K) := ⟨0, by rintro _ ⟨y, hy, rfl⟩; exact hb y hy⟩
  have hbdd' : BddBelow (Set.range fun i => F (u i)) := ⟨0, by rintro _ ⟨i, rfl⟩; exact hb _ (hu i)⟩
  apply le_antisymm
  · exact le_ciInf fun i => csInf_le hbdd ⟨u i, hu i, rfl⟩
  · refine le_csInf ⟨F (u 0), u 0, hu 0, rfl⟩ ?_
    rintro _ ⟨y, hy, rfl⟩
    have hsub : Set.range u ⊆ K := by rintro _ ⟨i, rfl⟩; exact hu i
    have hmem := ((hF y hy).mono hsub).mem_closure_image (hd hy)
    have hcl : F '' Set.range u ⊆ Set.Ici (⨅ i, F (u i)) := by
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ciInf_le hbdd' i
    exact closure_minimal hcl isClosed_Ici hmem

/-- A dense sequence of the unit ball. -/
theorem exists_dense_ball : ∃ u : ℕ → E d, (∀ i, u i ∈ Metric.closedBall (0 : E d) 1) ∧
    Metric.closedBall (0 : E d) 1 ⊆ closure (Set.range u) := by
  obtain ⟨t, hts, htc, hcl⟩ := (TopologicalSpace.IsSeparable.of_separableSpace
    (Metric.closedBall (0 : E d) 1)).exists_countable_dense_subset
  have hne : t.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have := hcl (Metric.mem_closedBall_self (x := (0 : E d)) zero_le_one)
    simp [h] at this
  obtain ⟨u, rfl⟩ := htc.exists_eq_range hne
  exact ⟨u, fun i => hts ⟨i, rfl⟩, hcl⟩

theorem measurable_snoc {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {t : ℕ} {f : α → Fin t → β}
    {g : α → β} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => Fin.snoc (α := fun _ => β) (f a) (g a) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]; exact hg
  · simp only [Fin.snoc_castSucc]; exact (measurable_pi_apply j).comp hf

/-- The loss of a strategy of the class, read at the point `clip y`, is jointly measurable in the history and `y`. -/
theorem measurable_strat_clip {n t : ℕ} {σ : Strategy d} (hσ : σ ∈ StratsLip (Metric.closedBall (0 : E d) 1) n)
    (ht : t < n) :
    Measurable fun q : E d × ((Fin t → E d) × (Fin t → ℝ)) => σ t q.2.1 q.2.2 (clip q.1) := by
  have hc : ∀ h : (Fin t → E d) × (Fin t → ℝ), Continuous fun y : E d => σ t h.1 h.2 (clip y) := fun h =>
    (continuousOn_of_lip (hσ.2 t ht h.1 h.2 h.2).2).comp_continuous continuous_clip clip_mem
  have hm : ∀ y : E d, Measurable fun h : (Fin t → E d) × (Fin t → ℝ) => σ t h.1 h.2 (clip y) := fun y =>
    (hσ.1 t ht).2 (clip y) (clip_mem y)
  exact measurable_uncurry_of_continuous_of_measurable (u := fun (y : E d) (h : (Fin t → E d) × (Fin t → ℝ)) => σ t h.1 h.2 (clip y)) hc hm

/-- The transcript is measurable in the seed. -/
theorem measurable_transcript {n : ℕ} {σ : Strategy d} (hσ : σ ∈ StratsLip (Metric.closedBall (0 : E d) 1) n)
    {Ω : Type} [MeasurableSpace Ω] {pol : Learner Ω d} (hpol : IsLearnerAd (Metric.closedBall 0 1) n pol) :
    ∀ t ≤ n, Measurable fun ω => transcript σ (fun _ => 0) (fun t => pol t ω) t
  | 0, _ => measurable_const
  | t + 1, ht => by
    have ih := measurable_transcript hσ hpol t (by omega)
    have hy : Measurable fun ω => pol t ω (transcript σ (fun _ => 0) (fun t => pol t ω) t).1
        (transcript σ (fun _ => 0) (fun t => pol t ω) t).2 :=
      (hpol t (by omega)).1.comp (measurable_id.prodMk (ih.fst.prodMk ih.snd))
    have hl : Measurable fun ω => σ t (transcript σ (fun _ => 0) (fun t => pol t ω) t).1
        (transcript σ (fun _ => 0) (fun t => pol t ω) t).2 (pol t ω (transcript σ (fun _ => 0) (fun t => pol t ω) t).1
        (transcript σ (fun _ => 0) (fun t => pol t ω) t).2) := by
      have := (measurable_strat_clip hσ (t := t) (by omega)).comp (hy.prodMk ih)
      convert this using 1
      funext ω
      simp only [Function.comp_apply]
      rw [clip_of_mem ((hpol t (by omega)).2 _ _ _)]
    simp only [transcript]
    exact (measurable_snoc ih.fst hy).prodMk (measurable_snoc ih.snd (hl.add measurable_const))

/-- The loss of round `t < n` at the point of round `t` is measurable in the seed. -/
theorem measurable_loss_play {n : ℕ} {σ : Strategy d} (hσ : σ ∈ StratsLip (Metric.closedBall (0 : E d) 1) n)
    {Ω : Type} [MeasurableSpace Ω] {pol : Learner Ω d} (hpol : IsLearnerAd (Metric.closedBall 0 1) n pol)
    {t : ℕ} (ht : t < n) :
    Measurable fun ω => σ t (transcript σ (fun _ => 0) (fun t => pol t ω) t).1
      (transcript σ (fun _ => 0) (fun t => pol t ω) t).2 (pol t ω (transcript σ (fun _ => 0) (fun t => pol t ω) t).1
      (transcript σ (fun _ => 0) (fun t => pol t ω) t).2) := by
  have ih := measurable_transcript hσ hpol t ht.le
  have hy : Measurable fun ω => pol t ω (transcript σ (fun _ => 0) (fun t => pol t ω) t).1
      (transcript σ (fun _ => 0) (fun t => pol t ω) t).2 :=
    (hpol t ht).1.comp (measurable_id.prodMk (ih.fst.prodMk ih.snd))
  have := (measurable_strat_clip hσ ht).comp (hy.prodMk ih)
  convert this using 1
  funext ω
  simp only [Function.comp_apply]
  rw [clip_of_mem ((hpol t ht).2 _ _ _)]

/-- Integrability is automatic on the class: for every strategy of `StratsLip` and every learner of `IsLearnerAd` on
the unit ball, the regret is integrable. So the conjunct `Integrable` of `TheoremConj1Lower` cannot make it false. -/
theorem integrable_regretAd {n : ℕ} {σ : Strategy d} (hσ : σ ∈ StratsLip (Metric.closedBall (0 : E d) 1) n)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {pol : Learner Ω d}
    (hpol : IsLearnerAd (Metric.closedBall 0 1) n pol) :
    Integrable (fun ω => regretAd (Metric.closedBall 0 1) σ (fun t => pol t ω) n) μ := by
  obtain ⟨u, hu, hd⟩ := exists_dense_ball (d := d)
  have hval : ∀ t < n, ∀ x o, ∀ y ∈ Metric.closedBall (0 : E d) 1, σ t x o y ∈ Set.Icc (0 : ℝ) 1 :=
    fun t ht x o y hy => ((hσ.1 t ht).1 x o).2 y hy
  set A : Ω → ℝ := fun ω => ∑ t ∈ Finset.range n, σ t (transcript σ (fun _ => 0) (fun t => pol t ω) t).1
      (transcript σ (fun _ => 0) (fun t => pol t ω) t).2 (pol t ω (transcript σ (fun _ => 0) (fun t => pol t ω) t).1
      (transcript σ (fun _ => 0) (fun t => pol t ω) t).2) with hA
  set F : Ω → E d → ℝ := fun ω y => ∑ t ∈ Finset.range n, σ t (transcript σ (fun _ => 0) (fun t => pol t ω) t).1
      (transcript σ (fun _ => 0) (fun t => pol t ω) t).2 y with hF
  have hFnn : ∀ ω, ∀ y ∈ Metric.closedBall (0 : E d) 1, 0 ≤ F ω y := fun ω y hy =>
    Finset.sum_nonneg fun t ht => (hval t (Finset.mem_range.1 ht) _ _ y hy).1
  have hFle : ∀ ω, ∀ y ∈ Metric.closedBall (0 : E d) 1, F ω y ≤ n := fun ω y hy => by
    rw [hF]
    calc _ ≤ ∑ t ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun t ht => (hval t (Finset.mem_range.1 ht) _ _ y hy).2
      _ = n := by simp
  have hR : (fun ω => regretAd (Metric.closedBall 0 1) σ (fun t => pol t ω) n) = fun ω => A ω - ⨅ i, F ω (u i) := by
    funext ω
    unfold regretAd regretPts
    simp_rw [lossAd_plays]
    rw [sInf_image_eq_iInf u hu hd (F ω) ?_ (hFnn ω)]
    · rfl
    · exact continuousOn_finsetSum _ fun t ht =>
        continuousOn_of_lip (hσ.2 t (Finset.mem_range.1 ht) _ (transcript σ (fun _ => 0) (fun t => pol t ω) t).2
          (transcript σ (fun _ => 0) (fun t => pol t ω) t).2).2
  rw [hR]
  have hAm : Measurable A := Finset.measurable_sum _ fun t ht => measurable_loss_play hσ hpol (Finset.mem_range.1 ht)
  have hIm : Measurable fun ω => ⨅ i, F ω (u i) := Measurable.iInf fun i =>
    Finset.measurable_sum _ fun t ht =>
      ((hσ.1 t (Finset.mem_range.1 ht)).2 (u i) (hu i)).comp
        (measurable_transcript hσ hpol t (Finset.mem_range.1 ht).le)
  refine Integrable.of_bound (hAm.sub hIm).aestronglyMeasurable n (Filter.Eventually.of_forall fun ω => ?_)
  have hA0 : 0 ≤ A ω := Finset.sum_nonneg fun t ht => (hval t (Finset.mem_range.1 ht) _ _ _ ((hpol t
    (Finset.mem_range.1 ht)).2 _ _ _)).1
  have hA1 : A ω ≤ n := by
    rw [hA]
    calc _ ≤ ∑ t ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun t ht =>
          (hval t (Finset.mem_range.1 ht) _ _ _ ((hpol t (Finset.mem_range.1 ht)).2 _ _ _)).2
      _ = n := by simp
  have hbdd : BddBelow (Set.range fun i => F ω (u i)) := ⟨0, by rintro _ ⟨i, rfl⟩; exact hFnn ω _ (hu i)⟩
  have hI0 : 0 ≤ ⨅ i, F ω (u i) := le_ciInf fun i => hFnn ω _ (hu i)
  have hI1 : ⨅ i, F ω (u i) ≤ n := (ciInf_le hbdd 0).trans (hFle ω _ (hu 0))
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-! ## A learner that randomises at every round -/

/-- The Gaussian stream is a probability measure. -/
instance : IsProbabilityMeasure gaussStream := by
  unfold gaussStream; infer_instance

/-- A learner with fresh randomness at every round: seeds in `ℕ → ℝ` under `gaussStream`, and in round `t` the play
`clip (ω t • e)`, `e = (1, 0, ..., 0)`, the `t`-th Gaussian draw along `e` clipped to the ball. -/
noncomputable def gaussLearner (d : ℕ) (hd : 1 ≤ d) : Learner (ℕ → ℝ) d := fun t ω _ _ =>
  clip (ω t • (EuclideanSpace.single ⟨0, hd⟩ (1 : ℝ) : E d))

/-- `gaussLearner` is a learner of the class, for every `n`. -/
theorem gaussLearner_mem (hd : 1 ≤ d) (n : ℕ) :
    IsLearnerAd (Metric.closedBall (0 : E d) 1) n (gaussLearner d hd) := by
  intro t _
  refine ⟨?_, fun ω x o => clip_mem _⟩
  exact continuous_clip.measurable.comp (((measurable_pi_apply t).comp measurable_fst).smul_const _)

/-- `gaussLearner` reads a fresh draw at every round: two seeds that differ only at index `t` give different plays in
round `t`, whatever the history. -/
theorem gaussLearner_fresh (hd : 1 ≤ d) (t : ℕ) (x : Fin t → E d) (o : Fin t → ℝ) :
    gaussLearner d hd t (Function.update 0 t 1) x o ≠ gaussLearner d hd t 0 x o := by
  have hn : ‖(EuclideanSpace.single ⟨0, hd⟩ (1 : ℝ) : E d)‖ = 1 := by simp
  simp only [gaussLearner, Function.update_self, Pi.zero_apply, zero_smul, one_smul]
  intro h
  have h0 : clip (0 : E d) = 0 := by simp [clip]
  rw [h0, clip_of_mem (by rw [Metric.mem_closedBall, dist_zero_right, hn])] at h
  have := congrArg norm h
  rw [hn, norm_zero] at this
  exact one_ne_zero this

/-- With `gaussLearner` under `gaussStream`, the hypotheses of `TheoremConj1Lower` hold for a learner that randomises
at every round, and the conjunct `Integrable` holds against every strategy of the class. -/
theorem gaussLearner_hyps (hd : 1 ≤ d) (n : ℕ) {σ : Strategy d}
    (hσ : σ ∈ StratsLip (Metric.closedBall (0 : E d) 1) n) :
    IsProbabilityMeasure gaussStream ∧ IsLearnerAd (Metric.closedBall (0 : E d) 1) n (gaussLearner d hd) ∧
      Integrable (fun ω => regretAd (Metric.closedBall 0 1) σ (fun t => gaussLearner d hd t ω) n) gaussStream :=
  ⟨inferInstance, gaussLearner_mem hd n, integrable_regretAd hσ gaussStream (gaussLearner_mem hd n)⟩


end AdversarialBco.Lower.Sanity
