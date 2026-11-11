/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementConj1
public import AdversarialBco.Poly.Df2Run
public import AdversarialBco.Poly.MachLang

@[expose] public section

/-!
# DF2-O against a strategy, run by run

* `df2oPlayAd`: the point DF2-O plays in round `t` against a strategy `σ`, built round by round (`prefAd`).
* `df2oPlayAd_fix`: on every run (Gaussian stream `gs`, noise `ε`), it is `df2oPlay` in the fixed world of the losses
  the strategy chose on that run, `lossAd σ ε (df2oPlayAd …)`: the point of round `t` reads the losses of the rounds
  before `t` only (`df2oPlay_congr`), and the loss of round `t` reads the points of the rounds before `t` only
  (`lossAd_congr`). `fix_unique`: below round `n`, that fixed point is unique.
* The machine against a strategy: `runAd_eq_run`, the run of a program against `σ` is its run in the world
  `realised` of the losses the strategy chose on that run; hence `costOKAd_iff` and `playedAd_eq_played`.
-/

open MeasureTheory

namespace AdversarialBco.Poly.Conj1

open AdversarialBco.RealRAM

variable {d : ℕ}


theorem obsAd_congr (σ : Strategy d) (ε : ℕ → ℝ) {x y : ℕ → E d} :
    ∀ t, (∀ i < t, x i = y i) → obsAd σ ε x t = obsAd σ ε y t
  | 0, _ => rfl
  | t + 1, h => by
    have ih := obsAd_congr σ ε t fun i hi => h i (by omega)
    have hx : (fun i : Fin t => x i) = fun i : Fin t => y i := funext fun i => h i (by omega)
    simp only [obsAd, ih, hx, h t (by omega)]

theorem lossAd_congr (σ : Strategy d) (ε : ℕ → ℝ) {x y : ℕ → E d} (t : ℕ) (h : ∀ i < t, x i = y i) :
    lossAd σ ε x t = lossAd σ ε y t := by
  have hx : (fun i : Fin t => x i) = fun i : Fin t => y i := funext fun i => h i i.2
  simp only [lossAd, obsAd_congr σ ε t h, hx]

/-- The point of a round does not read the loss of the round. -/
theorem df2Round_fst_congr (p : Df2OPar) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ft ft' : E d → ℝ) (nt : ℝ)
    (ξ : Fin d → ℝ) (ζ : ℝ) (m : Df2Mode d) :
    (df2Round p n K Ps ft nt ξ ζ m).1 = (df2Round p n K Ps ft' nt ξ ζ m).1 := by
  cases m with
  | off => rfl
  | guard => rfl
  | run st =>
    unfold df2Round
    simp only
    split_ifs <;> rfl

/-- The mode before round `t` reads the losses of the rounds before `t` only. -/
theorem df2oFrom_congr (n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) (f f' : ℕ → E d → ℝ) (ε gs : ℕ → ℝ) (a : ℕ)
    (m : Df2Mode d) :
    ∀ s, (∀ u < s, f (a + u) = f' (a + u)) →
      df2oFrom d n r0 R0 δ ⟨K, f, ε, gs⟩ a m s = df2oFrom d n r0 R0 δ ⟨K, f', ε, gs⟩ a m s
  | 0, _ => rfl
  | s + 1, h => by
    have ih := df2oFrom_congr n r0 R0 δ K f f' ε gs a m s fun u hu => h u (by omega)
    simp only [df2oFrom, df2oRoundAt, df2oPos, ih, h s (by omega)]

theorem df2oMode_congr (n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) (f f' : ℕ → E d → ℝ) (ε gs : ℕ → ℝ) (t : ℕ)
    (h : ∀ u < t, f u = f' u) :
    df2oMode d n r0 R0 δ ⟨K, f, ε, gs⟩ t = df2oMode d n r0 R0 δ ⟨K, f', ε, gs⟩ t := by
  unfold df2oMode
  have h0 : df2oMode0 d n r0 R0 δ ⟨K, f, ε, gs⟩ = df2oMode0 d n r0 R0 δ ⟨K, f', ε, gs⟩ := rfl
  rw [h0]
  exact df2oFrom_congr n r0 R0 δ K f f' ε gs 0 _ t fun u hu => by simpa using h u hu

/-- The point of round `t` reads the losses of the rounds before `t` only. -/
theorem df2oPlay_congr (n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) (f f' : ℕ → E d → ℝ) (ε gs : ℕ → ℝ) (t : ℕ)
    (h : ∀ u < t, f u = f' u) :
    df2oPlay d n r0 R0 δ ⟨K, f, ε, gs⟩ t = df2oPlay d n r0 R0 δ ⟨K, f', ε, gs⟩ t := by
  unfold df2oPlay df2oRoundAt
  rw [df2oMode_congr n r0 R0 δ K f f' ε gs t h]
  exact df2Round_fst_congr _ _ _ _ _ _ _ _ _ _

/-- The points of the rounds before `t` against a strategy (`0` from round `t` on). -/
noncomputable def prefAd (n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) (σ : Strategy d) (ε gs : ℕ → ℝ) : ℕ → ℕ → E d
  | 0 => fun _ => 0
  | t + 1 => Function.update (prefAd n r0 R0 δ K σ ε gs t) t
      (df2oPlay d n r0 R0 δ ⟨K, lossAd σ ε (prefAd n r0 R0 δ K σ ε gs t), ε, gs⟩ t)

/-- The point played in round `t` by DF2-O against the strategy `σ`. -/
noncomputable def df2oPlayAd (n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) (σ : Strategy d) (ε gs : ℕ → ℝ) (t : ℕ) : E d :=
  prefAd n r0 R0 δ K σ ε gs (t + 1) t

theorem prefAd_eq (n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) (σ : Strategy d) (ε gs : ℕ → ℝ) :
    ∀ t, ∀ u < t, prefAd n r0 R0 δ K σ ε gs t u = df2oPlayAd n r0 R0 δ K σ ε gs u
  | 0, u, hu => absurd hu (Nat.not_lt_zero u)
  | t + 1, u, hu => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hlt | rfl
    · rw [prefAd, Function.update_of_ne (Nat.ne_of_lt hlt)]
      exact prefAd_eq n r0 R0 δ K σ ε gs t u hlt
    · rfl

/-- The run against a strategy is the run in the fixed world of the losses it chose on that run. -/
theorem df2oPlayAd_fix (n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) (σ : Strategy d) (ε gs : ℕ → ℝ) (t : ℕ) :
    df2oPlayAd n r0 R0 δ K σ ε gs t =
      df2oPlay d n r0 R0 δ ⟨K, lossAd σ ε (df2oPlayAd n r0 R0 δ K σ ε gs), ε, gs⟩ t := by
  show (Function.update (prefAd n r0 R0 δ K σ ε gs t) t _) t = _
  rw [Function.update_self]
  refine df2oPlay_congr n r0 R0 δ K _ _ ε gs t fun u hu => lossAd_congr σ ε u fun i hi => ?_
  exact prefAd_eq n r0 R0 δ K σ ε gs t i (by omega)

/-- Below round `n`, the run against a strategy has one fixed point. -/
theorem fix_unique (n : ℕ) (r0 R0 δ : ℝ) (K : Set (E d)) (σ : Strategy d) (ε gs : ℕ → ℝ) (x : ℕ → E d)
    (hx : ∀ t < n, x t = df2oPlay d n r0 R0 δ ⟨K, lossAd σ ε x, ε, gs⟩ t) :
    ∀ t < n, x t = df2oPlayAd n r0 R0 δ K σ ε gs t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    rw [hx t ht, df2oPlayAd_fix]
    refine df2oPlay_congr n r0 R0 δ K _ _ ε gs t fun u hu => lossAd_congr σ ε u fun i hi => ?_
    exact ih i (by omega) (by omega)

/-! ## The run of a program against a strategy -/

/-- A step reads the loss of the current round only. -/
theorem step_congr (P : List Instr) (w w' : World d) (s : State d) (hK : w.K = w'.K)
    (hf : w.f s.rounds = w'.f s.rounds) (hn : w.noise = w'.noise) (hg : w.gs = w'.gs) :
    step P w s = step P w' s := by
  obtain ⟨K, f, noise, gs⟩ := w
  obtain ⟨K', f', noise', gs'⟩ := w'
  simp only at hK hf hn hg
  subst hK hn hg
  unfold step
  rcases P[s.pc]? with _ | ins
  · rfl
  · cases ins <;> simp [hf]

variable (P : List Instr) (g : GameAd d) (s0 : State d)

theorem runAd_succ (k : ℕ) : runAd P g s0 (k + 1) = stepAd P g (runAd P g s0 k) := by
  simp only [runAd, Function.iterate_succ_apply']

theorem runAd_rounds_mono {k k' : ℕ} (h : k ≤ k') : (runAd P g s0 k).rounds ≤ (runAd P g s0 k').rounds := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [runAd_succ]; exact ih.trans (Mach.step_rounds P _ _).1

theorem runAd_pts {k k' : ℕ} (h : k ≤ k') (u : ℕ) (hu : u < (runAd P g s0 k).rounds) :
    (runAd P g s0 k').pts u = (runAd P g s0 k).pts u := by
  induction h with
  | refl => rfl
  | step hle ih =>
    rw [runAd_succ, stepAd, Mach.step_pts P _ _ u ((hu.trans_le (runAd_rounds_mono P g s0 hle))), ih]

/-- The point of round `u` is the one the run records from the step at which round `u` is played on. -/
theorem playedAd_eq (k u : ℕ) (hu : u < (runAd P g s0 k).rounds) : playedAd P g s0 u = (runAd P g s0 k).pts u := by
  have hex : ∃ k, u < (runAd P g s0 k).rounds := ⟨k, hu⟩
  unfold playedAd
  rw [dite_eq_left hex]
  exact (runAd_pts P g s0 (Nat.find_min' hex hu) u (Nat.find_spec hex)).symm

/-- The world of the losses that the strategy chose on the run from `s0`. -/
noncomputable def realised : World d := ⟨g.K, lossAd g.σ g.noise (playedAd P g s0), g.noise, g.gs⟩

/-- The run of a program against a strategy is its run in the world of the losses the strategy chose on that run. -/
theorem runAd_eq_run (k : ℕ) : runAd P g s0 k = run P (realised P g s0) s0 k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [runAd_succ, stepAd, show run P (realised P g s0) s0 (k + 1) = step P (realised P g s0)
      (run P (realised P g s0) s0 k) by simp only [run, Function.iterate_succ_apply'], ← ih]
    exact step_congr P _ _ _ rfl (lossAd_congr g.σ g.noise _ fun i hi => (playedAd_eq P g s0 k i hi).symm) rfl rfl

theorem costOKAd_iff (n : ℕ) (B0 B : ℝ) : CostOKAd P g s0 n B0 B ↔ CostOK P (realised P g s0) s0 n B0 B := by
  have h : runAd P g s0 = run P (realised P g s0) s0 := funext (runAd_eq_run P g s0)
  unfold CostOKAd CostOK
  rw [h]

theorem playedAd_eq_played : playedAd P g s0 = played P (realised P g s0) s0 := by
  have h : runAd P g s0 = run P (realised P g s0) s0 := funext (runAd_eq_run P g s0)
  funext t
  unfold playedAd played
  generalize runAd P g s0 = r at h ⊢
  subst h
  rfl

end AdversarialBco.Poly.Conj1
