/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2PropGAdTools
public import AdversarialBco.Poly.Df2PropGProof

@[expose] public section

/-!
# Proposition G against a strategy

Proof of `Df2PropGAdOf` (Df2PropGAd.lean), theorem `df2PropGAdOf`, by the hybrid argument of Df2PropGProof.lean with
the state of a hybrid widened to `(mode, x̃, õ)`: the points and observations of the earlier rounds that the strategy
reads (Proposition 8.11).

* The hybrid `H_k` runs the rounds `t < k` with the bisection gauge and the rounds `t ≥ k` with the exact gauge. In
  every hybrid the strategy is fed the point `x̃_t` that the bisection map gives from the mode of the hybrid and the
  draw of round `t`, and the observation `õ_t = g_t(x̃_t) + ε_t` (no dither); the loss of round `t` is
  `g_t = σ t x̃_{<t} õ_{<t}`. `H_0` is the comparison run of the statement, `H_n` is DJ against the strategy.
* One step `H_k → H_{k+1}` resamples the dither of round `k`: the state before round `k + 1` is the mode after round
  `k`, which reads the dither through the observation of round `k`, and the history `x̃_{≤k}, õ_{≤k}`, which does not
  read it and is the same in the two hybrids.
* Measurability: on the case of the analysis every point read is in the interior of `K`, where the strategy is
  jointly measurable (`CaraInterior`); the hybrids are run with the strategy extended by `0` off the interior (`gL`)
  and the comparator as an infimum over the rational points of the interior (`C0`).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix ENNReal

namespace AdversarialBco.Poly.PropGAd

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly ApMeas PropG
open Classical

variable {d : ℕ}

/-- The state of a hybrid before a round: the mode, the points `x̃` and the observations `õ` of the earlier rounds. -/
abbrev HSt (d : ℕ) : Type := Df2Mode d × (ℕ → E d) × (ℕ → ℝ)

/-- The data of `Df2PropGAd`: those of `Df2PropG` (with any loss sequence, never read) and the strategy. -/
structure ACtx (d : ℕ) extends GCtx d where
  σ : Strategy d

namespace ACtx

variable (c : ACtx d)

/-- The hypotheses: those of `Df2PropG` on the data, the strategy in the class, and the Carathéodory lemma. -/
def Hyp : Prop := c.toGCtx.Hyp ∧ c.σ ∈ Strats c.K c.n ∧ CaraInterior

/-- The loss of round `t` read off the history `(x, o)`: the strategy at the points and observations of the rounds
before `t`, on the interior of `K`, `0` elsewhere and from round `n` on. -/
noncomputable def gL (t : ℕ) (x : ℕ → E d) (o : ℕ → ℝ) : E d → ℝ :=
  if t < c.n then (interior c.K).indicator (c.σ t (fun i : Fin t => x i) (fun i : Fin t => o i)) else 0

/-- Round `t` with the gauge `ga` and the loss `ft`. -/
noncomputable def rndA (ga : E d → ℝ) (ω : Om) (t : ℕ) (ft : E d → ℝ) (m : Df2Mode d) : E d × Df2Mode d :=
  df2RoundGa c.p c.n c.K (c.Ps ω) ga apCall ft (ω.2 t) (c.xi ω t) (c.ze ω t) m

/-- The point that DJ's bisection map gives from the mode `m` at round `t`. -/
noncomputable def pJ (ω : Om) (t : ℕ) (m : Df2Mode d) : E d := (c.rndA (c.gJ (c.Ps ω)) ω t 0 m).1

/-- One round with the gauge `ga`: the mode after the round; the point `x̃_t` and the observation
`õ_t = g_t(x̃_t) + ε_t` appended to the history. -/
noncomputable def stepA (ga : E d → ℝ) (ω : Om) (t : ℕ) (s : HSt d) : HSt d :=
  ((c.rndA ga ω t (c.gL t s.2.1 s.2.2) s.1).2, Function.update s.2.1 t (c.pJ ω t s.1),
    Function.update s.2.2 t (c.gL t s.2.1 s.2.2 (c.pJ ω t s.1) + ω.2 t))

/-- The state of the hybrid `H_k` before round `t`. -/
noncomputable def hS (k : ℕ) (ω : Om) : ℕ → HSt d
  | 0 => (c.mode0 ω, 0, 0)
  | t + 1 => c.stepA (c.hGa k t (c.Ps ω)) ω t (hS k ω t)

/-- The point the exact gauge plays from the mode of `H_k` before round `t`. -/
noncomputable def ePtA (k : ℕ) (ω : Om) (t : ℕ) : E d := (c.rndA (c.gR (c.Ps ω)) ω t 0 (c.hS k ω t).1).1

/-- The comparator of the history `(x, o)`: the infimum of the cumulated loss over the rational points of the
interior of `K`. -/
noncomputable def C0 (x : ℕ → E d) (o : ℕ → ℝ) : ℝ :=
  ⨅ q : Fin d → ℚ, if (WithLp.toLp 2 (fun i => (q i : ℝ)) : E d) ∈ interior c.K then
    ∑ t ∈ Finset.range c.n, c.gL t x o (WithLp.toLp 2 (fun i => (q i : ℝ))) else (c.n : ℝ)

/-- `Φ_k`: the regret of the exact-gauge points of `H_k` against its losses. -/
noncomputable def PhiA (k : ℕ) (ω : Om) : ℝ :=
  ∑ t ∈ Finset.range c.n, c.gL t (c.hS k ω c.n).2.1 (c.hS k ω c.n).2.2 (c.ePtA k ω t) -
    c.C0 (c.hS k ω c.n).2.1 (c.hS k ω c.n).2.2

/-- The event `E_k` at the level `B`. -/
def EvA (B : ℝ) (k : ℕ) : Set Om := {ω | c.Case ω ∧ B < c.PhiA k ω}

variable {c}

/-! ### Hypotheses -/

theorem Hyp.g (h : c.Hyp) : c.toGCtx.Hyp := h.1
theorem Hyp.σ (h : c.Hyp) : c.σ ∈ Strats c.K c.n := h.2.1
theorem Hyp.cara (h : c.Hyp) : CaraInterior := h.2.2

theorem Hyp.adm (h : c.Hyp) {t : ℕ} (ht : t < c.n) (x : Fin t → E d) (o : Fin t → ℝ) : AdmLoss c.K (c.σ t x o) :=
  (h.σ t ht).1 x o

theorem Hyp.zero_int (h : c.Hyp) : (0 : E d) ∈ interior c.K := by
  have hr := h.g.2.2.1
  have hb := h.g.2.2.2.2.2.2.2.2.1
  exact interior_mono hb (mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds 0 hr))

/-! ### The loss read off a history -/

theorem gL_eq (t : ℕ) (ht : t < c.n) (x : ℕ → E d) (o : ℕ → ℝ) {y : E d} (hy : y ∈ interior c.K) :
    c.gL t x o y = c.σ t (fun i : Fin t => x i) (fun i : Fin t => o i) y := by
  simp only [gL, ht, ↓reduceIte, Set.indicator_of_mem hy]

/-- On a history that agrees with the points `z` and their observations below `t`, the loss read off the history is
the loss `lossAd σ ε z t` on the interior. -/
theorem gL_eq_lossAd {t : ℕ} (ht : t < c.n) {x : ℕ → E d} {o : ℕ → ℝ} {ε : ℕ → ℝ} {z : ℕ → E d}
    (hx : ∀ i < t, x i = z i) (ho : ∀ i (hi : i < t), o i = obsAd c.σ ε z t ⟨i, hi⟩) {y : E d}
    (hy : y ∈ interior c.K) : c.gL t x o y = lossAd c.σ ε z t y := by
  rw [gL_eq t ht x o hy]
  have e1 : (fun i : Fin t => x i) = fun i : Fin t => z i := funext fun i => hx i i.2
  have e2 : (fun i : Fin t => o i) = obsAd c.σ ε z t := funext fun i => ho i i.2
  rw [e1, e2]
  rfl

/-! ### One round on the case -/

theorem eps_lt_one' {ω : Om} (hc : c.Case ω) : c.p.eps < 1 := GCtx.eps_lt_one hc

theorem rndA_good (h : c.Hyp) {ω : Om} (hc : c.Case ω) {ga : E d → ℝ}
    (hga : ∀ x, gauge (c.Kp (c.Ps ω)) x ≤ ga x) (t : ℕ) (ft : E d → ℝ) {m : Df2Mode d} (hm : m ≠ .off) :
    (c.rndA ga ω t ft m).1 ∈ interior c.K ∧ (c.rndA ga ω t ft m).2 ≠ .off :=
  round_good c.p c.n h.g.convex h.g.closed (GCtx.case_good hc) (GCtx.eps_pos h.g) (GCtx.eps_lt_one hc) ga hga
    apCall ft _ _ _ hm

theorem rndA_fst (ga : E d → ℝ) (ω : Om) (t : ℕ) (ft ft' : E d → ℝ) (m : Df2Mode d) :
    (c.rndA ga ω t ft m).1 = (c.rndA ga ω t ft' m).1 :=
  roundGa_fst _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem rndA_congr (h : c.Hyp) {ω : Om} (hc : c.Case ω) {ga : E d → ℝ}
    (hga : ∀ x, gauge (c.Kp (c.Ps ω)) x ≤ ga x) (t : ℕ) {ft ft' : E d → ℝ}
    (hft : ∀ x ∈ interior c.K, ft x = ft' x) (m : Df2Mode d) : c.rndA ga ω t ft m = c.rndA ga ω t ft' m :=
  round_congr_ft c.p c.n h.g.convex h.g.closed (GCtx.case_good hc) (GCtx.eps_pos h.g) (GCtx.eps_lt_one hc) ga hga
    apCall ft ft' hft _ _ _ m

theorem pJ_good (h : c.Hyp) {ω : Om} (hc : c.Case ω) (t : ℕ) {m : Df2Mode d} (hm : m ≠ .off) :
    c.pJ ω t m ∈ interior c.K :=
  (rndA_good h hc (GCtx.gJ_ge h.g hc) t 0 hm).1

/-! ### The hybrids on the case -/

theorem hS_fst_succ (k t : ℕ) (ω : Om) :
    (c.hS k ω (t + 1)).1 = (c.rndA (c.hGa k t (c.Ps ω)) ω t (c.gL t (c.hS k ω t).2.1 (c.hS k ω t).2.2)
      (c.hS k ω t).1).2 := rfl

theorem hS_x_succ (k t : ℕ) (ω : Om) :
    (c.hS k ω (t + 1)).2.1 = Function.update (c.hS k ω t).2.1 t (c.pJ ω t (c.hS k ω t).1) := rfl

theorem hS_o_succ (k t : ℕ) (ω : Om) :
    (c.hS k ω (t + 1)).2.2 = Function.update (c.hS k ω t).2.2 t
      (c.gL t (c.hS k ω t).2.1 (c.hS k ω t).2.2 (c.pJ ω t (c.hS k ω t).1) + ω.2 t) := rfl

theorem hS_ne_off (h : c.Hyp) {ω : Om} (hc : c.Case ω) (k t : ℕ) : (c.hS k ω t).1 ≠ .off := by
  induction t with
  | zero => exact GCtx.mode0_ne_off hc
  | succ t ih => exact (rndA_good h hc (GCtx.hGa_ge h.g hc k t) t _ ih).2

/-- The history of a hybrid is written once: the entries below `t` do not change after round `t`. -/
theorem hS_prefix (k : ℕ) (ω : Om) (t : ℕ) :
    ∀ j i, i < t → (c.hS k ω (t + j)).2.1 i = (c.hS k ω t).2.1 i ∧ (c.hS k ω (t + j)).2.2 i = (c.hS k ω t).2.2 i
  | 0, i, _ => ⟨rfl, rfl⟩
  | j + 1, i, hi => by
    have ih := hS_prefix k ω t j i hi
    have hne : i ≠ t + j := by omega
    rw [show t + (j + 1) = t + j + 1 by omega, hS_x_succ, hS_o_succ, Function.update_of_ne hne,
      Function.update_of_ne hne]
    exact ih

theorem hS_x_le (k : ℕ) (ω : Om) {t t' : ℕ} (htt : t ≤ t') {i : ℕ} (hi : i < t) :
    (c.hS k ω t').2.1 i = (c.hS k ω t).2.1 i := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le htt
  exact (hS_prefix k ω t j i hi).1

theorem hS_o_le (k : ℕ) (ω : Om) {t t' : ℕ} (htt : t ≤ t') {i : ℕ} (hi : i < t) :
    (c.hS k ω t').2.2 i = (c.hS k ω t).2.2 i := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le htt
  exact (hS_prefix k ω t j i hi).2

theorem hS_x_self (k : ℕ) (ω : Om) (t : ℕ) : (c.hS k ω (t + 1)).2.1 t = c.pJ ω t (c.hS k ω t).1 := by
  rw [hS_x_succ, Function.update_self]

theorem hS_o_self (k : ℕ) (ω : Om) (t : ℕ) :
    (c.hS k ω (t + 1)).2.2 t = c.gL t (c.hS k ω t).2.1 (c.hS k ω t).2.2 (c.pJ ω t (c.hS k ω t).1) + ω.2 t := by
  rw [hS_o_succ, Function.update_self]

/-- On the case, a hybrid feeds the strategy the points `z` and their observations, as soon as its points are `z`. -/
theorem hS_obs (h : c.Hyp) {ω : Om} (hc : c.Case ω) (k : ℕ) {z : ℕ → E d} :
    ∀ t ≤ c.n, (∀ i < t, (c.hS k ω (i + 1)).2.1 i = z i) →
      (∀ i < t, (c.hS k ω t).2.1 i = z i) ∧ ∀ i (hi : i < t), (c.hS k ω t).2.2 i = obsAd c.σ ω.2 z t ⟨i, hi⟩
  | 0, _, _ => ⟨fun i hi => absurd hi (Nat.not_lt_zero i), fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | t + 1, ht, hz => by
    obtain ⟨hx, ho⟩ := hS_obs h hc k t (by omega) fun i hi => hz i (by omega)
    have hzt : c.pJ ω t (c.hS k ω t).1 = z t := by rw [← hS_x_self]; exact hz t (by omega)
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [hS_x_le k ω (Nat.le_succ t) hi]; exact hx i hi
      · exact hz i hi
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl
      · rw [hS_o_le k ω (Nat.le_succ t) hi', ho i hi', obsAd_le c.σ ω.2 z (Nat.le_succ t) i hi']
      · rw [hS_o_self, hzt, show (⟨i, hi⟩ : Fin (i + 1)) = Fin.last i from rfl, obsAd_last,
          gL_eq_lossAd (by omega) hx ho (by rw [← hzt]; exact pJ_good h hc i (hS_ne_off h hc k i))]
/-! ### The comparator of a history -/

/-- On a history that agrees below `n` with the points `z` and their observations, the loss read off the history is
`lossAd σ ε z t` on the interior at every round `t < n`. -/
theorem gL_eq_of_hist {X : ℕ → E d} {O : ℕ → ℝ} {ε : ℕ → ℝ} {z : ℕ → E d} (hX : ∀ i < c.n, X i = z i)
    (hO : ∀ i (hi : i < c.n), O i = obsAd c.σ ε z c.n ⟨i, hi⟩) {t : ℕ} (ht : t < c.n) {y : E d}
    (hy : y ∈ interior c.K) : c.gL t X O y = lossAd c.σ ε z t y :=
  gL_eq_lossAd ht (fun i hi => hX i (by omega))
    (fun i hi => by rw [hO i (by omega), obsAd_le c.σ ε z ht.le i hi]) hy

theorem C0_eq (h : c.Hyp) {X : ℕ → E d} {O : ℕ → ℝ} {ε : ℕ → ℝ} {z : ℕ → E d} (hX : ∀ i < c.n, X i = z i)
    (hO : ∀ i (hi : i < c.n), O i = obsAd c.σ ε z c.n ⟨i, hi⟩) :
    c.C0 X O = sInf ((fun y => ∑ t ∈ Finset.range c.n, lossAd c.σ ε z t y) '' c.K) := by
  have hcv := convexOn_sum_range c.K h.g.convex c.n (lossAd c.σ ε z) (fun t ht => (h.adm ht _ _).1)
    (fun t ht => (h.adm ht _ _).2)
  rw [sInf_image_eq_iInf_rat c.K ⟨0, h.zero_int⟩ _ hcv.1 c.n hcv.2]
  unfold C0
  refine iInf_congr fun q => ?_
  split_ifs with hq
  · exact Finset.sum_congr rfl fun t ht => gL_eq_of_hist hX hO (Finset.mem_range.mp ht) hq
  · rfl

end ACtx

/-! ## The comparison run -/

section Cmp

variable (n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) (σ : Strategy d) (ω : Om)

theorem df2zFrom_congr (f f' : ℕ → E d → ℝ) (a : ℕ) (m : Df2Mode d) :
    ∀ s, (∀ u < s, f (a + u) = f' (a + u)) →
      df2zFrom d n r0 R0 δ (df2World K f ω) a m s = df2zFrom d n r0 R0 δ (df2World K f' ω) a m s
  | 0, _ => rfl
  | s + 1, hs => by
    have ih := df2zFrom_congr f f' a m s fun u hu => hs u (by omega)
    show (df2zRoundAt d n r0 R0 δ (df2World K f ω) (a + s) (df2zFrom d n r0 R0 δ (df2World K f ω) a m s)).2 =
      (df2zRoundAt d n r0 R0 δ (df2World K f' ω) (a + s) (df2zFrom d n r0 R0 δ (df2World K f' ω) a m s)).2
    rw [ih]
    simp only [df2zRoundAt, df2oPs, df2oPos, df2World, hs s (by omega)]

theorem df2zMode_congr (f f' : ℕ → E d → ℝ) (t : ℕ) (ht : ∀ u < t, f u = f' u) :
    df2zMode d n r0 R0 δ (df2World K f ω) t = df2zMode d n r0 R0 δ (df2World K f' ω) t := by
  unfold df2zMode
  exact df2zFrom_congr n r0 R0 δ K ω f f' 0 _ t fun u hu => by simpa using ht u hu

theorem df2oRoundAt_fst_congr (f f' : ℕ → E d → ℝ) (t : ℕ) (m : Df2Mode d) :
    (df2oRoundAt d n r0 R0 δ (df2World K f ω) t m).1 = (df2oRoundAt d n r0 R0 δ (df2World K f' ω) t m).1 := by
  unfold df2oRoundAt
  rw [df2Round_eq_Ga, df2Round_eq_Ga]
  exact roundGa_fst _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem cmpPref_eq : ∀ t, ∀ u < t, cmpPref d n r0 R0 δ K σ ω t u = cmpPts d n r0 R0 δ K σ ω u
  | 0, u, hu => absurd hu (Nat.not_lt_zero u)
  | t + 1, u, hu => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hlt | rfl
    · rw [cmpPref, Function.update_of_ne (Nat.ne_of_lt hlt)]
      exact cmpPref_eq t u hlt
    · rfl

/-- The point `x̃_t` of the comparison run is the bisection point from the mode of D0 in the comparison world. -/
theorem cmpPts_fix (t : ℕ) :
    cmpPts d n r0 R0 δ K σ ω t = (df2oRoundAt d n r0 R0 δ (cmpWorld d n r0 R0 δ K σ ω) t
      (df2zMode d n r0 R0 δ (cmpWorld d n r0 R0 δ K σ ω) t)).1 := by
  show (Function.update (cmpPref d n r0 R0 δ K σ ω t) t _) t = _
  rw [Function.update_self]
  have hl : ∀ u < t, lossAd σ ω.2 (cmpPref d n r0 R0 δ K σ ω t) u = cmpLoss d n r0 R0 δ K σ u ω := fun u hu =>
    lossAd_congr σ ω.2 u fun i hi => cmpPref_eq n r0 R0 δ K σ ω t i (by omega)
  rw [df2zMode_congr n r0 R0 δ K ω _ (fun u => cmpLoss d n r0 R0 δ K σ u ω) t hl]
  exact df2oRoundAt_fst_congr n r0 R0 δ K ω _ _ t _

end Cmp

namespace ACtx

variable {c : ACtx d}

/-! ### `H_0` is the comparison run -/

/-- The comparison world of the data. -/
noncomputable abbrev W0 (c : ACtx d) (ω : Om) : World d := cmpWorld d c.n c.r0 c.R0 c.δ c.K c.σ ω

/-- The comparison points of the data. -/
noncomputable abbrev z0 (c : ACtx d) (ω : Om) : ℕ → E d := cmpPts d c.n c.r0 c.R0 c.δ c.K c.σ ω

theorem hS_zero (h : c.Hyp) {ω : Om} (hc : c.Case ω) :
    ∀ t ≤ c.n, (c.hS 0 ω t).1 = df2zMode d c.n c.r0 c.R0 c.δ (c.W0 ω) t ∧
      ∀ i < t, (c.hS 0 ω (i + 1)).2.1 i = c.z0 ω i
  | 0, _ => ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | t + 1, ht => by
    obtain ⟨hm, hz⟩ := hS_zero h hc t (by omega)
    obtain ⟨hx, ho⟩ := hS_obs h hc 0 t (by omega) hz
    have hft : ∀ y ∈ interior c.K, c.gL t (c.hS 0 ω t).2.1 (c.hS 0 ω t).2.2 y = cmpLoss d c.n c.r0 c.R0 c.δ c.K c.σ t ω y :=
      fun y hy => gL_eq_lossAd (by omega) hx ho hy
    have hga : c.hGa 0 t (c.Ps ω) = gauge (c.Kp (c.Ps ω)) := by
      simp only [GCtx.hGa, Nat.not_lt_zero, ↓reduceIte]; exact GCtx.gR_eq h.g hc
    refine ⟨?_, fun i hi => ?_⟩
    · rw [hS_fst_succ, hga, rndA_congr h hc (fun x => le_rfl) t hft, hm]
      show _ = (df2zRoundAt d c.n c.r0 c.R0 c.δ (c.W0 ω) (0 + t) _).2
      rw [Nat.zero_add]
      rfl
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact hz i hi
      · show _ = cmpPts d c.n c.r0 c.R0 c.δ c.K c.σ ω i
        rw [hS_x_self, cmpPts_fix, ← hm]
        unfold pJ
        rw [rndA_fst _ _ _ 0 (cmpLoss d c.n c.r0 c.R0 c.δ c.K c.σ i ω)]
        unfold rndA df2oRoundAt
        rw [df2Round_eq_Ga]
        rfl

theorem ePtA_zero (h : c.Hyp) {ω : Om} (hc : c.Case ω) (t : ℕ) (ht : t < c.n) :
    c.ePtA 0 ω t = df2zPlay d c.n c.r0 c.R0 c.δ (c.W0 ω) t := by
  unfold ePtA
  rw [(hS_zero h hc t ht.le).1, GCtx.gR_eq h.g hc, rndA_fst _ _ _ 0 (cmpLoss d c.n c.r0 c.R0 c.δ c.K c.σ t ω)]
  rfl

theorem ePtA_int (h : c.Hyp) {ω : Om} (hc : c.Case ω) (k t : ℕ) : c.ePtA k ω t ∈ interior c.K :=
  (rndA_good h hc (GCtx.gR_ge h.g hc) t 0 (hS_ne_off h hc k t)).1

theorem phiA_zero (h : c.Hyp) {ω : Om} (hc : c.Case ω) :
    c.PhiA 0 ω = regretPts c.K (fun t => cmpLoss d c.n c.r0 c.R0 c.δ c.K c.σ t ω)
      (df2zPlay d c.n c.r0 c.R0 c.δ (c.W0 ω)) c.n := by
  obtain ⟨hX, hO⟩ := hS_obs h hc 0 c.n le_rfl (hS_zero h hc c.n le_rfl).2
  unfold PhiA regretPts
  rw [C0_eq h hX hO]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.mp ht
  rw [gL_eq_of_hist hX hO ht' (ePtA_int h hc 0 t), ePtA_zero h hc t ht']
  rfl

/-! ### `H_n` is DJ against the strategy -/

section DJ

variable (x : Om → ℕ → E d)

/-- The world of the losses the strategy chose on the run of DJ. -/
noncomputable abbrev Wx (c : ACtx d) (ω : Om) : World d := df2World c.K (lossAd c.σ ω.2 (x ω)) ω

variable {x}

theorem hS_n (h : c.Hyp) (hx : ∀ ω, ∀ t < c.n, x ω t = df2oPlay d c.n c.r0 c.R0 c.δ (Wx x c ω) t) {ω : Om}
    (hc : c.Case ω) :
    ∀ t ≤ c.n, (c.hS c.n ω t).1 = df2oMode d c.n c.r0 c.R0 c.δ (Wx x c ω) t ∧
      ∀ i < t, (c.hS c.n ω (i + 1)).2.1 i = x ω i
  | 0, _ => ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | t + 1, ht => by
    obtain ⟨hm, hz⟩ := hS_n h hx hc t (by omega)
    obtain ⟨hxx, ho⟩ := hS_obs h hc c.n t (by omega) hz
    have hft : ∀ y ∈ interior c.K, c.gL t (c.hS c.n ω t).2.1 (c.hS c.n ω t).2.2 y = lossAd c.σ ω.2 (x ω) t y :=
      fun y hy => gL_eq_lossAd (by omega) hxx ho hy
    have hga : c.hGa c.n t (c.Ps ω) = c.gJ (c.Ps ω) := by
      simp only [GCtx.hGa, show t < c.n by omega, ↓reduceIte]
    refine ⟨?_, fun i hi => ?_⟩
    · rw [hS_fst_succ, hga, rndA_congr h hc (GCtx.gJ_ge h.g hc) t hft, hm]
      show _ = (df2oRoundAt d c.n c.r0 c.R0 c.δ (Wx x c ω) (0 + t) _).2
      rw [Nat.zero_add]
      unfold df2oRoundAt
      rw [df2Round_eq_Ga]
      rfl
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact hz i hi
      · rw [hS_x_self, hx ω i (by omega), hm]
        unfold pJ df2oPlay
        rw [rndA_fst _ _ _ 0 (lossAd c.σ ω.2 (x ω) i)]
        unfold rndA df2oRoundAt
        rw [df2Round_eq_Ga]
        rfl

/-- The regret of DJ against the losses of the run is at most `Φ_n + n R η/ε` (Lemma G (iii)). -/
theorem regretA_le (h : c.Hyp) (hx : ∀ ω, ∀ t < c.n, x ω t = df2oPlay d c.n c.r0 c.R0 c.δ (Wx x c ω) t) {ω : Om}
    (hc : c.Case ω) :
    regretPts c.K (lossAd c.σ ω.2 (x ω)) (x ω) c.n ≤ c.PhiA c.n ω + c.n * (c.p.R * c.η / c.p.eps) := by
  have hε := GCtx.eps_pos h.g
  have hη := GCtx.η_nonneg h.g
  have hzn := (hS_n h hx hc c.n le_rfl).2
  obtain ⟨hX, hO⟩ := hS_obs h hc c.n c.n le_rfl hzn
  have hb : 0 ≤ c.p.R * c.η / c.p.eps := div_nonneg (mul_nonneg (by linarith [GCtx.one_le_R h.g]) hη) hε.le
  have key : ∀ t < c.n, lossAd c.σ ω.2 (x ω) t (x ω t) ≤
      c.gL t (c.hS c.n ω c.n).2.1 (c.hS c.n ω c.n).2.2 (c.ePtA c.n ω t) + c.p.R * c.η / c.p.eps := by
    intro t ht
    rw [gL_eq_of_hist hX hO ht (ePtA_int h hc c.n t), ← hzn t ht, hS_x_self]
    have hm := hS_ne_off h hc c.n t
    unfold pJ ePtA
    rw [GCtx.gR_eq h.g hc]
    set f := lossAd c.σ ω.2 (x ω) t with hf
    have hfa : AdmLoss c.K f := h.adm ht _ _
    rcases hmt : (c.hS c.n ω t).1 with _ | _ | st
    · exact absurd hmt hm
    · unfold rndA; rw [roundGa_guard, roundGa_guard]; linarith
    · have hP := GCtx.case_good hc
      have hε1 := GCtx.eps_lt_one hc
      unfold rndA
      rw [round_good_run c.p c.n h.g.convex h.g.closed hP hε hε1 _ (GCtx.gJ_ge h.g hc),
        round_good_run c.p c.n h.g.convex h.g.closed hP hε hε1 (gauge (c.Kp (c.Ps ω))) (fun x => le_rfl)]
      obtain ⟨h1, -, h3, h4⟩ := pts_cmp c.p h.g.convex h.g.closed hP hε hε1 hη (c.gJ (c.Ps ω))
        (GCtx.gJ_ge h.g hc) (GCtx.gJ_le h.g hc) st (c.xi ω t) f hfa
      have hpos : 0 < rPt c.p (gauge (c.Kp (c.Ps ω))) st (c.xi ω t) := by linarith
      have hu : rPt c.p (c.gJ (c.Ps ω)) st (c.xi ω t) / rPt c.p (gauge (c.Kp (c.Ps ω))) st (c.xi ω t) - 1 ≤
          c.η := by
        have : rPt c.p (c.gJ (c.Ps ω)) st (c.xi ω t) / rPt c.p (gauge (c.Kp (c.Ps ω))) st (c.xi ω t) ≤
            1 + c.η := by
          rw [div_le_iff₀ hpos]; linarith
        linarith
      have h5 : c.p.R * (rPt c.p (c.gJ (c.Ps ω)) st (c.xi ω t) / rPt c.p (gauge (c.Kp (c.Ps ω))) st (c.xi ω t) -
          1) / c.p.eps ≤ c.p.R * c.η / c.p.eps := by
        have hR : 0 ≤ c.p.R := by linarith [GCtx.one_le_R h.g]
        gcongr
      have := (abs_le.mp (h4.trans h5)).2
      dsimp only
      linarith
  unfold regretPts PhiA
  rw [C0_eq h hX hO]
  have hs : ∑ t ∈ Finset.range c.n, lossAd c.σ ω.2 (x ω) t (x ω t) ≤
      ∑ t ∈ Finset.range c.n, (c.gL t (c.hS c.n ω c.n).2.1 (c.hS c.n ω c.n).2.2 (c.ePtA c.n ω t) +
        c.p.R * c.η / c.p.eps) :=
    Finset.sum_le_sum fun t ht => key t (Finset.mem_range.mp ht)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  linarith

end DJ
/-! ### Measurability -/

section Meas

variable (h : c.Hyp)
include h

theorem meas_gL (t : ℕ) : Measurable fun q : ((ℕ → E d) × (ℕ → ℝ)) × E d => c.gL t q.1.1 q.1.2 q.2 := by
  by_cases ht : t < c.n
  · have hC := h.cara d ((Fin t → E d) × (Fin t → ℝ)) c.K (fun p => c.σ t p.1 p.2) (fun p => (h.adm ht p.1 p.2).1)
      (fun y hy => (h.σ t ht).2 y (interior_subset hy))
    have h2 := measurable_restrict_indicator c.K (c.σ t) hC
    simp only [gL, ht, ↓reduceIte]
    exact h2
  · simp only [gL, ht, ↓reduceIte, Pi.zero_apply]
    exact measurable_const

theorem meas_gL_comp {X : Type*} [MeasurableSpace X] (t : ℕ) {x : X → ℕ → E d} {o : X → ℕ → ℝ} {y : X → E d}
    (hx : Measurable x) (ho : Measurable o) (hy : Measurable y) : Measurable fun a => c.gL t (x a) (o a) (y a) :=
  (meas_gL h t).comp ((hx.prodMk ho).prodMk hy)

theorem meas_C0 : Measurable fun q : (ℕ → E d) × (ℕ → ℝ) => c.C0 q.1 q.2 := by
  have hG : ∀ y : E d, Measurable fun q : (ℕ → E d) × (ℕ → ℝ) => ∑ t ∈ Finset.range c.n, c.gL t q.1 q.2 y :=
    fun y => Finset.measurable_sum _ fun t _ => meas_gL_comp h t measurable_fst measurable_snd measurable_const
  have h2 := measurable_iInf_rat (interior c.K) (fun (q : (ℕ → E d) × (ℕ → ℝ)) y => ∑ t ∈ Finset.range c.n, c.gL t q.1 q.2 y) hG (c.n : ℝ)
  exact h2

theorem meas_rndA {X : Type*} [MeasurableSpace X] (t : ℕ) {ga : X → E d → ℝ}
    (hga : Measurable fun q : X × E d => ga q.1 q.2) {w : X → Om} (hw : Measurable w) {F : X → E d → ℝ}
    (hF : Measurable fun q : X × E d => F q.1 q.2) {m : X → Df2Mode d} (hm : Measurable m) :
    Measurable fun a => c.rndA (ga a) (w a) t (F a) (m a) :=
  meas_roundGa c.p c.n c.K h.g.closed ((GCtx.meas_Ps h.g).comp hw) hga hF ((GCtx.meas_noise t).comp hw)
    ((GCtx.meas_ze t).comp hw) ((GCtx.meas_xi t).comp hw) hm

theorem meas_gJ_at {X : Type*} [MeasurableSpace X] {w : X → Om} (hw : Measurable w) :
    Measurable fun q : X × E d => c.gJ (c.Ps (w q.1)) q.2 := by
  have h2 := (GCtx.meas_gJ h.g).comp (((GCtx.meas_Ps h.g).comp (hw.comp measurable_fst)).prodMk measurable_snd)
  simp only [Function.comp_def] at h2
  exact h2

theorem meas_gR_of {X : Type*} [MeasurableSpace X] {w : X → Om} (hw : Measurable w) :
    Measurable fun q : X × E d => c.gR (c.Ps (w q.1)) q.2 := by
  have h2 := (GCtx.meas_gR h.g).comp (((GCtx.meas_Ps h.g).comp (hw.comp measurable_fst)).prodMk measurable_snd)
  simp only [Function.comp_def] at h2
  exact h2

theorem meas_pJ {X : Type*} [MeasurableSpace X] (t : ℕ) {w : X → Om} (hw : Measurable w) {m : X → Df2Mode d}
    (hm : Measurable m) : Measurable fun a => c.pJ (w a) t (m a) :=
  (meas_rndA h t (meas_gJ_at h hw) hw measurable_const hm).fst

theorem meas_stepA {X : Type*} [MeasurableSpace X] (t : ℕ) {ga : X → E d → ℝ}
    (hga : Measurable fun q : X × E d => ga q.1 q.2) {w : X → Om} (hw : Measurable w) {s : X → HSt d}
    (hs : Measurable s) : Measurable fun a => c.stepA (ga a) (w a) t (s a) := by
  have hx : Measurable fun a => (s a).2.1 := hs.snd.fst
  have ho : Measurable fun a => (s a).2.2 := hs.snd.snd
  have hF : Measurable fun q : X × E d => c.gL t (s q.1).2.1 (s q.1).2.2 q.2 :=
    meas_gL_comp h t (hx.comp measurable_fst) (ho.comp measurable_fst) measurable_snd
  have hp := meas_pJ h t hw hs.fst
  have hmode := (meas_rndA h t hga hw (F := fun a => c.gL t (s a).2.1 (s a).2.2) hF hs.fst).snd
  have hobs : Measurable fun a => c.gL t (s a).2.1 (s a).2.2 (c.pJ (w a) t (s a).1) + (w a).2 t :=
    (meas_gL_comp h t hx ho hp).add ((GCtx.meas_noise t).comp hw)
  exact hmode.prodMk ((measurable_update_pair t).comp ((hx.prodMk ho).prodMk (hp.prodMk hobs)))

theorem meas_hS (k t : ℕ) : Measurable fun ω => c.hS k ω t := by
  induction t with
  | zero => exact (GCtx.meas_mode0 h.g).prodMk measurable_const
  | succ t ih => exact meas_stepA h t (GCtx.meas_hGa h.g k t) measurable_id ih

theorem meas_ePtA (k t : ℕ) : Measurable fun ω => c.ePtA k ω t :=
  (meas_rndA h t (meas_gR_of h measurable_id) measurable_id measurable_const (meas_hS h k t).fst).fst

theorem meas_PhiA (k : ℕ) : Measurable (c.PhiA k) :=
  (Finset.measurable_sum _ fun t _ =>
    meas_gL_comp h t (meas_hS h k c.n).snd.fst (meas_hS h k c.n).snd.snd (meas_ePtA h k t)).sub
    ((meas_C0 h).comp (meas_hS h k c.n).snd)

theorem meas_EvA (B : ℝ) (k : ℕ) : MeasurableSet (c.EvA B k) :=
  (GCtx.meas_case h.g).inter (measurableSet_lt measurable_const (meas_PhiA h k))

end Meas

/-! ### One step: the dither of round `k` -/

theorem rndA_U {k : ℕ} (hk : k < c.n) (ga : E d → ℝ) (ω : Om) (z : ℝ) {t : ℕ} (ht : t ≠ k) (ft : E d → ℝ)
    (m : Df2Mode d) : c.rndA ga (c.U k ω z) t ft m = c.rndA ga ω t ft m := by
  unfold rndA; rw [GCtx.Ps_U hk, GCtx.xi_U, GCtx.ze_U k ω z ht]; rfl

theorem pJ_U {k : ℕ} (hk : k < c.n) (ω : Om) (z : ℝ) (t : ℕ) (m : Df2Mode d) :
    c.pJ (c.U k ω z) t m = c.pJ ω t m := by
  unfold pJ rndA; rw [GCtx.Ps_U hk, GCtx.xi_U]
  exact roundGa_fst _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem stepA_U {k : ℕ} (hk : k < c.n) (ga : E d → ℝ) (ω : Om) (z : ℝ) {t : ℕ} (ht : t ≠ k) (s : HSt d) :
    c.stepA ga (c.U k ω z) t s = c.stepA ga ω t s := by
  unfold stepA; rw [rndA_U hk ga ω z ht, pJ_U hk]; rfl

theorem hS_U {k : ℕ} (hk : k < c.n) (k' : ℕ) (ω : Om) (z : ℝ) {t : ℕ} (ht : t ≤ k) :
    c.hS k' (c.U k ω z) t = c.hS k' ω t := by
  induction t with
  | zero =>
    show (c.mode0 (c.U k ω z), (0 : ℕ → E d), (0 : ℕ → ℝ)) = (c.mode0 ω, 0, 0)
    rw [GCtx.mode0_U hk]
  | succ t ih =>
    show c.stepA (c.hGa k' t (c.Ps (c.U k ω z))) (c.U k ω z) t (c.hS k' (c.U k ω z) t) =
      c.stepA (c.hGa k' t (c.Ps ω)) ω t (c.hS k' ω t)
    rw [GCtx.Ps_U hk, ih (by omega), stepA_U hk _ ω z (by omega)]

theorem hS_succ (k : ℕ) (ω : Om) {t : ℕ} (ht : t ≤ k) : c.hS k ω t = c.hS (k + 1) ω t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h1 : t < k := by omega
    show c.stepA (c.hGa k t (c.Ps ω)) ω t (c.hS k ω t) = c.stepA (c.hGa (k + 1) t (c.Ps ω)) ω t (c.hS (k + 1) ω t)
    rw [ih (by omega)]
    simp only [GCtx.hGa, h1, show t < k + 1 by omega, ↓reduceIte]

theorem ePtA_U {k : ℕ} (hk : k < c.n) (k' : ℕ) (ω : Om) (z : ℝ) {t : ℕ} (ht : t ≤ k) :
    c.ePtA k' (c.U k ω z) t = c.ePtA k' ω t := by
  unfold ePtA; rw [hS_U hk k' ω z ht]; unfold rndA; rw [GCtx.Ps_U hk, GCtx.xi_U]
  exact roundGa_fst _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem ePtA_succ (k : ℕ) (ω : Om) {t : ℕ} (ht : t ≤ k) : c.ePtA k ω t = c.ePtA (k + 1) ω t := by
  unfold ePtA; rw [hS_succ k ω ht]

variable (c) in
/-- The states of the exact-gauge rounds from round `k + 1` on, started in the state `s` before round `k + 1`. -/
noncomputable def cS (k : ℕ) (ω : Om) (s : HSt d) : ℕ → HSt d
  | 0 => s
  | j + 1 => c.stepA (c.gR (c.Ps ω)) ω (k + 1 + j) (cS k ω s j)

variable (c) in
/-- The exact-gauge point of round `k + 1 + j` of the continuation. -/
noncomputable def cPt (k : ℕ) (ω : Om) (s : HSt d) (j : ℕ) : E d :=
  (c.rndA (c.gR (c.Ps ω)) ω (k + 1 + j) 0 (c.cS k ω s j).1).1

variable (c) in
/-- `Φ` as a function of the state before round `k + 1`, the exact-gauge points of the rounds up to `k` being those of
`H_k`. -/
noncomputable def Val (k : ℕ) (ω : Om) (s : HSt d) : ℝ :=
  ∑ t ∈ Finset.range (k + 1), c.gL t (c.cS k ω s (c.n - (k + 1))).2.1 (c.cS k ω s (c.n - (k + 1))).2.2 (c.ePtA k ω t) +
    ∑ j ∈ Finset.range (c.n - (k + 1)),
      c.gL (k + 1 + j) (c.cS k ω s (c.n - (k + 1))).2.1 (c.cS k ω s (c.n - (k + 1))).2.2 (c.cPt k ω s j) -
    c.C0 (c.cS k ω s (c.n - (k + 1))).2.1 (c.cS k ω s (c.n - (k + 1))).2.2

variable (c) in
/-- The history after round `k`, the same in `H_k` and `H_{k+1}`, read by neither the dither nor the gauge. -/
noncomputable def Hk (k : ℕ) (ω : Om) : (ℕ → E d) × (ℕ → ℝ) := (c.stepA (c.gR (c.Ps ω)) ω k (c.hS k ω k)).2

variable (c) in
/-- The mode after round `k` with the dither `z`, for the gauge `ga` of round `k`. -/
noncomputable def MzA (k : ℕ) (ga : E d → ℝ) (ω : Om) (z : ℝ) : Df2Mode d :=
  (df2RoundGa c.p c.n c.K (c.Ps ω) ga apCall (c.gL k (c.hS k ω k).2.1 (c.hS k ω k).2.2) (ω.2 k) (c.xi ω k) (z / 2)
    (c.hS k ω k).1).2

variable (c) in
/-- The event of a section, after round `k`. -/
def GsA (B : ℝ) (k : ℕ) (ω : Om) (s : HSt d) : Prop := c.Case ω ∧ B < c.Val k ω s

theorem hS_cont (k k' : ℕ) (hk' : k' ≤ k + 1) (ω : Om) (j : ℕ) :
    c.hS k' ω (k + 1 + j) = c.cS k ω (c.hS k' ω (k + 1)) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show c.stepA (c.hGa k' (k + 1 + j) (c.Ps ω)) ω (k + 1 + j) (c.hS k' ω (k + 1 + j)) =
      c.stepA (c.gR (c.Ps ω)) ω (k + 1 + j) (c.cS k ω (c.hS k' ω (k + 1)) j)
    rw [ih]
    simp only [GCtx.hGa, show ¬ (k + 1 + j < k') by omega, ↓reduceIte]

theorem sum_range_split (f : ℕ → ℝ) {a n : ℕ} (h : a ≤ n) :
    ∑ t ∈ Finset.range n, f t = ∑ t ∈ Finset.range a, f t + ∑ j ∈ Finset.range (n - a), f (a + j) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, Finset.sum_range_add]

theorem phiA_split {k : ℕ} (hk : k < c.n) (k' : ℕ) (hk' : k' ≤ k + 1) (ω : Om)
    (hpre : ∀ t ≤ k, c.ePtA k' ω t = c.ePtA k ω t) : c.PhiA k' ω = c.Val k ω (c.hS k' ω (k + 1)) := by
  have hn : c.hS k' ω c.n = c.cS k ω (c.hS k' ω (k + 1)) (c.n - (k + 1)) := by
    rw [← hS_cont k k' hk' ω, show k + 1 + (c.n - (k + 1)) = c.n by omega]
  unfold PhiA Val
  rw [hn, sum_range_split _ (show k + 1 ≤ c.n by omega)]
  congr 2
  · exact Finset.sum_congr rfl fun t ht => by rw [hpre t (by have := Finset.mem_range.mp ht; omega)]
  · refine Finset.sum_congr rfl fun j _ => ?_
    unfold ePtA cPt
    rw [hS_cont k k' hk' ω j]

theorem cS_U {k : ℕ} (hk : k < c.n) (ω : Om) (z : ℝ) (s : HSt d) (j : ℕ) :
    c.cS k (c.U k ω z) s j = c.cS k ω s j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show c.stepA (c.gR (c.Ps (c.U k ω z))) (c.U k ω z) (k + 1 + j) (c.cS k (c.U k ω z) s j) =
      c.stepA (c.gR (c.Ps ω)) ω (k + 1 + j) (c.cS k ω s j)
    rw [ih, GCtx.Ps_U hk, stepA_U hk _ ω z (by omega)]

theorem Val_U {k : ℕ} (hk : k < c.n) (ω : Om) (z : ℝ) (s : HSt d) : c.Val k (c.U k ω z) s = c.Val k ω s := by
  have hc : c.cS k (c.U k ω z) s (c.n - (k + 1)) = c.cS k ω s (c.n - (k + 1)) := cS_U hk ω z s _
  have hp : ∀ j, c.cPt k (c.U k ω z) s j = c.cPt k ω s j := fun j => by
    unfold cPt; rw [cS_U hk, GCtx.Ps_U hk, rndA_U hk _ ω z (by omega)]
  unfold Val
  rw [hc]
  simp only [hp]
  congr 2
  exact Finset.sum_congr rfl fun t ht => by
    rw [ePtA_U hk k ω z (by have := Finset.mem_range.mp ht; omega)]

theorem hS_U_succ {k : ℕ} (hk : k < c.n) (k' : ℕ) {ω : Om} (hmk : c.hS k' ω k = c.hS k ω k) (z : ℝ) :
    c.hS k' (c.U k ω z) (k + 1) = (c.MzA k (c.hGa k' k (c.Ps ω)) ω z, c.Hk k ω) := by
  show c.stepA (c.hGa k' k (c.Ps (c.U k ω z))) (c.U k ω z) k (c.hS k' (c.U k ω z) k) = _
  rw [hS_U hk k' ω z le_rfl, hmk, GCtx.Ps_U hk]
  refine Prod.ext ?_ ?_
  · show (c.rndA _ (c.U k ω z) k _ _).2 = _
    unfold rndA MzA
    rw [GCtx.Ps_U hk, GCtx.xi_U, GCtx.ze_U_self]
    rfl
  · simp only [Hk, stepA, pJ_U hk]
    rfl

theorem sec_kA {k : ℕ} (hk : k < c.n) (B : ℝ) (ω : Om) :
    {z | c.U k ω z ∈ c.EvA B k} = {z | c.GsA B k ω (c.MzA k (c.gR (c.Ps ω)) ω z, c.Hk k ω)} := by
  ext z
  simp only [Set.mem_ofPred_eq, EvA, GsA]
  rw [GCtx.case_U hk, phiA_split hk k (by omega) _ (fun _ _ => rfl), Val_U hk, hS_U_succ hk k rfl z]
  simp only [GCtx.hGa, lt_irrefl, ↓reduceIte]

theorem sec_k1A {k : ℕ} (hk : k < c.n) (B : ℝ) (ω : Om) :
    {z | c.U k ω z ∈ c.EvA B (k + 1)} = {z | c.GsA B k ω (c.MzA k (c.gJ (c.Ps ω)) ω z, c.Hk k ω)} := by
  ext z
  simp only [Set.mem_ofPred_eq, EvA, GsA]
  rw [GCtx.case_U hk, phiA_split hk (k + 1) le_rfl _ (fun t ht => (ePtA_succ k _ ht).symm), Val_U hk,
    hS_U_succ hk (k + 1) (hS_succ k ω le_rfl).symm z]
  simp only [GCtx.hGa, Nat.lt_succ_self, ↓reduceIte]

section MeasSec

variable (h : c.Hyp)
include h

theorem meas_cS (k : ℕ) (ω : Om) (j : ℕ) : Measurable fun s : HSt d => c.cS k ω s j := by
  induction j with
  | zero => exact measurable_id
  | succ j ih =>
    exact meas_stepA h (k + 1 + j) (GCtx.meas_gR_at h.g (c.Ps ω)) measurable_const ih

theorem meas_Val (k : ℕ) (ω : Om) : Measurable fun s : HSt d => c.Val k ω s := by
  have hf := meas_cS h k ω (c.n - (k + 1))
  refine ((Finset.measurable_sum _ fun t _ => meas_gL_comp h t hf.snd.fst hf.snd.snd measurable_const).add
    (Finset.measurable_sum _ fun j _ => meas_gL_comp h (k + 1 + j) hf.snd.fst hf.snd.snd ?_)).sub
    ((meas_C0 h).comp hf.snd)
  exact (meas_rndA h (k + 1 + j) (GCtx.meas_gR_at h.g (c.Ps ω)) measurable_const measurable_const
    (meas_cS h k ω j).fst).fst

theorem meas_GsA (B : ℝ) (k : ℕ) (ω : Om) : MeasurableSet {s : HSt d | c.GsA B k ω s} :=
  (MeasurableSet.const _).inter (measurableSet_lt measurable_const (meas_Val h k ω))

end MeasSec
/-! ### One step: one Gaussian coordinate -/

/-- The cost of resampling the dither of round `k` with the bisection gauge at round `k` in place of the exact one. -/
theorem pwA (h : c.Hyp) {k : ℕ} (hk : k < c.n) (B : ℝ) (ω : Om) :
    gaussianReal 0 1 {z | c.GsA B k ω (c.MzA k (c.gJ (c.Ps ω)) ω z, c.Hk k ω)} ≤
      gaussianReal 0 1 {z | c.GsA B k ω (c.MzA k (c.gR (c.Ps ω)) ω z, c.Hk k ω)} +
        ENNReal.ofReal (c.η * (2 + (c.p.R + 4) / c.p.eps) + c.η * |ω.2 k|) := by
  classical
  by_cases hc : c.Case ω
  swap
  · have he : {z | c.GsA B k ω (c.MzA k (c.gJ (c.Ps ω)) ω z, c.Hk k ω)} = ∅ := by
      ext z
      simp only [GsA, hc, false_and, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
    rw [he, measure_empty]
    exact bot_le
  have hε := GCtx.eps_pos h.g
  have hε1 := GCtx.eps_lt_one hc
  have hP := GCtx.case_good hc
  have hη := GCtx.η_nonneg h.g
  have hR := GCtx.one_le_R h.g
  have hfa : AdmLoss c.K (c.σ k (fun i : Fin k => (c.hS k ω k).2.1 i) (fun i : Fin k => (c.hS k ω k).2.2 i)) :=
    h.adm hk _ _
  have hgf : ∀ y ∈ interior c.K, c.gL k (c.hS k ω k).2.1 (c.hS k ω k).2.2 y =
      c.σ k (fun i : Fin k => (c.hS k ω k).2.1 i) (fun i : Fin k => (c.hS k ω k).2.2 i) y :=
    fun y hy => gL_eq k hk _ _ hy
  rcases hm : (c.hS k ω k).1 with _ | _ | st
  · exact absurd hm (hS_ne_off h hc k k)
  · have e : ∀ ga : E d → ℝ, c.MzA k ga ω = fun _ => (if pgMu (c.Ps ω) + pgOp (c.Ps ω) 0 ∈ c.K then
        ((pgMu (c.Ps ω) + pgOp (c.Ps ω) 0 : E d), Df2Mode.guard) else (0, Df2Mode.off)).2 := by
      intro ga
      funext z
      simp only [MzA, hm, roundGa_guard]
    rw [e, e]
    exact le_self_add
  · rw [GCtx.gR_eq h.g hc]
    set ξ := c.xi ω k with hξ
    set e := ω.2 k with he
    set N : ℝ → Df2Mode d := fun y =>
      df2NextAP apCall c.p c.n (df2Keps c.K (c.Ps ω) c.p.R c.p.eps) st ξ (st.A *ᵥ ξ) y with hN
    have hNm : Measurable N := by
      have h2 := (df2NextAP_measurable c.p c.n (fun P => df2Keps c.K P c.p.R c.p.eps)
        (keps_graph c.K h.g.closed c.p.R c.p.eps)).comp
          ((measurable_const (a := c.Ps ω)).prodMk ((measurable_const (a := st)).prodMk
            ((measurable_const (a := ξ)).prodMk (measurable_id (α := ℝ)))))
      simp only [Function.comp_def] at h2
      exact h2
    set T : Set ℝ := {y | c.GsA B k ω (N y, c.Hk k ω)} with hT
    have hTm : MeasurableSet T := (hNm.prodMk measurable_const) (meas_GsA h B k ω)
    obtain ⟨h1, h2, h3, h4⟩ := pts_cmp c.p h.g.convex h.g.closed hP hε hε1 hη (c.gJ (c.Ps ω)) (GCtx.gJ_ge h.g hc)
      (GCtx.gJ_le h.g hc) st ξ _ hfa
    set pt0 := rPt c.p (gauge (df2Kp c.K (c.Ps ω) c.p.R)) st ξ with hpt0
    set ptJ := rPt c.p (c.gJ (c.Ps ω)) st ξ with hptJ
    have hxJ := (rPoint_good c.p h.g.convex h.g.closed hP hε hε1 _ (GCtx.gJ_ge h.g hc) st ξ).2
    have hx0 := (rPoint_good c.p h.g.convex h.g.closed hP hε hε1 (gauge (df2Kp c.K (c.Ps ω) c.p.R))
      (fun x => le_rfl) st ξ).2
    set FJ := c.gL k (c.hS k ω k).2.1 (c.hS k ω k).2.2 (rPoint c.p (c.Ps ω) (c.gJ (c.Ps ω)) st ξ) with hFJ
    set F0 := c.gL k (c.hS k ω k).2.1 (c.hS k ω k).2.2
      (rPoint c.p (c.Ps ω) (gauge (df2Kp c.K (c.Ps ω) c.p.R)) st ξ) with hF0
    have hFJe : FJ = c.σ k (fun i : Fin k => (c.hS k ω k).2.1 i) (fun i : Fin k => (c.hS k ω k).2.2 i)
        (rPoint c.p (c.Ps ω) (c.gJ (c.Ps ω)) st ξ) := hgf _ hxJ
    have hF0e : F0 = c.σ k (fun i : Fin k => (c.hS k ω k).2.1 i) (fun i : Fin k => (c.hS k ω k).2.2 i)
        (rPoint c.p (c.Ps ω) (gauge (df2Kp c.K (c.Ps ω) c.p.R)) st ξ) := hgf _ hx0
    have hFJ01 := hfa.2 _ (interior_subset hxJ)
    have hpos : 0 < pt0 := by linarith
    set aJ := ptJ * (FJ + e) / 2 + 2 * (ptJ - 1) / c.p.eps with haJ
    set a0 := pt0 * (F0 + e) / 2 + 2 * (pt0 - 1) / c.p.eps with ha0
    have eJ : {z | c.GsA B k ω (c.MzA k (c.gJ (c.Ps ω)) ω z, c.Hk k ω)} =
        {z | aJ + (1 + (ptJ / pt0 - 1)) * (pt0 / 4) * z ∈ T} := by
      ext z
      simp only [Set.mem_ofPred_eq, MzA, hm,
        round_good_run c.p c.n h.g.convex h.g.closed hP hε hε1 _ (GCtx.gJ_ge h.g hc), hT]
      have hY : ptJ * (FJ + e + z / 2) / 2 + 2 * (ptJ - 1) / c.p.eps =
          aJ + (1 + (ptJ / pt0 - 1)) * (pt0 / 4) * z := by
        rw [haJ]; field_simp; ring
      rw [← hY]
    have e0 : {z | c.GsA B k ω (c.MzA k (gauge (df2Kp c.K (c.Ps ω) c.p.R)) ω z, c.Hk k ω)} =
        {z | a0 + (pt0 / 4) * z ∈ T} := by
      ext z
      simp only [Set.mem_ofPred_eq, MzA, hm,
        round_good_run c.p c.n h.g.convex h.g.closed hP hε hε1 (gauge (df2Kp c.K (c.Ps ω) c.p.R))
          (fun x => le_rfl), hT]
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

/-! ### One step -/

theorem stepE (h : c.Hyp) (hε : c.p.eps ≤ 1 / 2) (ν : Measure (ℕ → ℝ)) (hν : NoiseOK ν) (B : ℝ) (k : ℕ) (hk : k < c.n) :
    (gaussStream.prod ν) (c.EvA B (k + 1)) ≤
      (gaussStream.prod ν) (c.EvA B k) + ENNReal.ofReal (c.η * (c.p.R + 7) / c.p.eps) := by
  have := hν.1
  have := GCtx.gaussStream_prob
  have he := GCtx.eps_pos h.g
  have hη := GCtx.η_nonneg h.g
  have hR := GCtx.one_le_R h.g
  set a := c.η * (2 + (c.p.R + 4) / c.p.eps) with ha
  have ha0 : 0 ≤ a := by positivity
  have hmeas : Measurable fun ω : Om => gaussianReal 0 1 {z | c.U k ω z ∈ c.EvA B k} :=
    measurable_measure_prodMk_left ((meas_EvA h B k).preimage (GCtx.meas_U k))
  rw [world_resample ν (c.ix k) _ (meas_EvA h B (k + 1))]
  calc ∫⁻ ω, gaussianReal 0 1 {z | (Function.update ω.1 (c.ix k) z, ω.2) ∈ c.EvA B (k + 1)} ∂(gaussStream.prod ν)
      = ∫⁻ ω, gaussianReal 0 1 {z | c.GsA B k ω (c.MzA k (c.gJ (c.Ps ω)) ω z, c.Hk k ω)}
          ∂(gaussStream.prod ν) := by
        congr 1
        funext ω
        rw [← sec_k1A hk]
        rfl
    _ ≤ ∫⁻ ω, (gaussianReal 0 1 {z | c.U k ω z ∈ c.EvA B k} + ENNReal.ofReal (a + c.η * |ω.2 k|))
          ∂(gaussStream.prod ν) := by
        refine lintegral_mono fun ω => ?_
        rw [sec_kA hk]
        exact pwA h hk B ω
    _ = ∫⁻ ω, gaussianReal 0 1 {z | c.U k ω z ∈ c.EvA B k} ∂(gaussStream.prod ν) +
          ∫⁻ ω, ENNReal.ofReal (a + c.η * |ω.2 k|) ∂(gaussStream.prod ν) := lintegral_add_left hmeas _
    _ ≤ (gaussStream.prod ν) (c.EvA B k) + ENNReal.ofReal (a + c.η) := by
        rw [world_resample ν (c.ix k) _ (meas_EvA h B k)]
        refine add_le_add le_rfl ?_
        exact lintegral_noise_le gaussStream ν k (noise_abs_lintegral ν hν k) a c.η ha0 hη
    _ ≤ (gaussStream.prod ν) (c.EvA B k) + ENNReal.ofReal (c.η * (c.p.R + 7) / c.p.eps) := by
        gcongr
        rw [ha, le_div_iff₀ he]
        have h3 : (c.p.R + 4) / c.p.eps * c.p.eps = c.p.R + 4 := div_mul_cancel₀ _ he.ne'
        nlinarith

theorem stepsE (h : c.Hyp) (hε : c.p.eps ≤ 1 / 2) (ν : Measure (ℕ → ℝ)) (hν : NoiseOK ν) (B : ℝ) :
    ∀ k ≤ c.n, (gaussStream.prod ν) (c.EvA B k) ≤
      (gaussStream.prod ν) (c.EvA B 0) + k * ENNReal.ofReal (c.η * (c.p.R + 7) / c.p.eps) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    calc (gaussStream.prod ν) (c.EvA B (k + 1))
        ≤ (gaussStream.prod ν) (c.EvA B k) + ENNReal.ofReal (c.η * (c.p.R + 7) / c.p.eps) :=
          stepE h hε ν hν B k (by omega)
      _ ≤ (gaussStream.prod ν) (c.EvA B 0) + k * ENNReal.ofReal (c.η * (c.p.R + 7) / c.p.eps) +
            ENNReal.ofReal (c.η * (c.p.R + 7) / c.p.eps) := by gcongr; exact ih (by omega)
      _ = (gaussStream.prod ν) (c.EvA B 0) +
            ((k + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (c.η * (c.p.R + 7) / c.p.eps) := by
          push_cast; ring

end ACtx

/-! ## Proposition 8.11 -/

theorem df2PropGAdOf : Df2PropGAdOf := by
  intro hC d n r0 R0 δ K σ hH ν hν B x hx
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hH
  let c : ACtx d := ⟨⟨n, r0, R0, δ, K, fun _ _ => 0⟩, σ⟩
  have h : c.Hyp := ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    fun _ _ => ⟨convexOn_const 0 h8, fun _ _ => ⟨le_rfl, zero_le_one⟩⟩⟩, h11, hC⟩
  by_cases hε : (df2oPar d n δ).eps ≤ 1 / 2
  swap
  · have he : {ω : Om | Df2Case d n r0 R0 δ (df2World K (lossAd σ ω.2 (x ω)) ω) ∧
        B + 1 < regretPts K (lossAd σ ω.2 (x ω)) (x ω) n} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun hc => absurd hc.2 hε
    rw [he, measure_empty]
    exact bot_le
  have hsub : {ω : Om | Df2Case d n r0 R0 δ (df2World K (lossAd σ ω.2 (x ω)) ω) ∧
      B + 1 < regretPts K (lossAd σ ω.2 (x ω)) (x ω) n} ⊆ c.EvA B n := by
    rintro ω ⟨hc, hB⟩
    have hc' : c.Case ω := hc
    refine ⟨hc', ?_⟩
    have e1 : regretPts K (lossAd σ ω.2 (x ω)) (x ω) n ≤ c.PhiA c.n ω + c.n * (c.p.R * c.η / c.p.eps) :=
      ACtx.regretA_le h hx hc'
    have e2 : (c.n : ℝ) * (c.p.R * c.η / c.p.eps) ≤ 1 := by
      have hp := GCtx.param_sum h.g
      have hδ1 : c.p.δ1 ≤ 1 := GCtx.δ1_le h.g
      have : (c.n : ℝ) * (c.p.R * c.η / c.p.eps) ≤ c.n * (c.η * (c.p.R + 7) / c.p.eps) := by
        have he := GCtx.eps_pos h.g
        have hη := GCtx.η_nonneg h.g
        have hR := GCtx.one_le_R h.g
        have : c.p.R * c.η ≤ c.η * (c.p.R + 7) := by nlinarith
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right this he.le) (Nat.cast_nonneg _)
      linarith
    show B < c.PhiA c.n ω
    linarith
  have h0 : c.EvA B 0 = {ω : Om | Df2Case d n r0 R0 δ (cmpWorld d n r0 R0 δ K σ ω) ∧
      B < regretPts K (fun t => cmpLoss d n r0 R0 δ K σ t ω) (df2zPlay d n r0 R0 δ (cmpWorld d n r0 R0 δ K σ ω)) n} := by
    ext ω
    simp only [ACtx.EvA, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hc, hB⟩
      exact ⟨hc, (ACtx.phiA_zero h hc) ▸ hB⟩
    · rintro ⟨hc, hB⟩
      exact ⟨hc, (ACtx.phiA_zero h hc).symm ▸ hB⟩
  calc (gaussStream.prod ν) {ω : Om | Df2Case d n r0 R0 δ (df2World K (lossAd σ ω.2 (x ω)) ω) ∧
        B + 1 < regretPts K (lossAd σ ω.2 (x ω)) (x ω) n}
      ≤ (gaussStream.prod ν) (c.EvA B n) := measure_mono hsub
    _ ≤ (gaussStream.prod ν) (c.EvA B 0) + n * ENNReal.ofReal (c.η * (c.p.R + 7) / c.p.eps) :=
        ACtx.stepsE h hε ν hν B n le_rfl
    _ ≤ _ := by
        rw [h0]
        gcongr
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (GCtx.param_sum h.g)

end AdversarialBco.Poly.PropGAd

/-- Proposition 8.11, with the Carathéodory lemma proved (`caraInterior`). -/
theorem AdversarialBco.Poly.PropGAd.df2PropGAd : AdversarialBco.Poly.Df2PropGAd :=
  AdversarialBco.Poly.PropGAd.df2PropGAdOf AdversarialBco.Poly.PropGAd.caraInterior
