/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementExplicit

@[expose] public section

/-!
# Lemma 7.13: the policy of a learner with coins

`lemmaMarg` proves `LemmaMarg` of `AdversarialBco/StatementExplicit.lean`: for a learner with coins whose laws are
probability vectors on a finite nonempty `C ⊆ K`, the policy `margPolicy` is a `C`-policy, a Borel function of the
history, and has the learner's law of actions (`ex_marg_law`, by induction on the rounds) and its regret.
-/

open MeasureTheory Real

namespace AdversarialBco.Explicit

/-- `Bern(o)` has nonnegative masses for `o ∈ [0, 1]`. -/
theorem ex_bern_nonneg (o : ℝ) (ho : o ∈ Set.Icc (0 : ℝ) 1) (b : Bool) : 0 ≤ bern o b := by
  unfold bern
  split_ifs
  · exact ho.1
  · linarith [ho.2]

/-- A mixture of probability vectors with nonnegative weights of positive total is a probability vector. -/
theorem ex_mix_prob {B C : Type*} [Fintype B] [Fintype C] (w : B → ℝ) (hw : ∀ b, 0 ≤ w b) (hZ : 0 < ∑ b, w b)
    (p : B → C → ℝ) (hp : ∀ b, p b ∈ probVecs C) :
    (fun y => ∑ b, w b / (∑ b', w b') * p b y) ∈ probVecs C := by
  refine ⟨fun y => Finset.sum_nonneg fun b _ => mul_nonneg (div_nonneg (hw b) hZ.le) ((hp b).1 y), ?_⟩
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp_rw [(hp _).2, mul_one, ← Finset.sum_div]
  exact div_self hZ.ne'

/-- The uniform vector on a nonempty finite set is a probability vector. -/
theorem ex_unif_prob {d : ℕ} (C : Finset (E d)) (hC : C.Nonempty) : (fun _ => 1 / (C.card : ℝ)) ∈ probVecs C := by
  have hc : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  refine ⟨fun _ => by positivity, ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  field_simp

/-- `margPolicy` is a `C`-policy. -/
theorem ex_marg_cpolicy {d : ℕ} (K : Set (E d)) (C : Finset (E d)) (hCK : ↑C ⊆ K) (hC : C.Nonempty)
    (P : (t : ℕ) → (Fin t → C × Bool) → C → ℝ) (hP : ∀ t h, P t h ∈ probVecs C) :
    IsCPolicy K C (margPolicy C P) := by
  refine ⟨hCK, fun t χ hχ => ?_⟩
  unfold margPolicy
  split_ifs with h0 h1
  · refine ex_mix_prob _ (fun b => Finset.prod_nonneg fun s _ => mul_nonneg ((hP _ _).1 _)
      (ex_bern_nonneg _ (hχ s).2 _)) h1 _ fun b => hP _ _
  · exact ex_unif_prob C hC
  · exact ex_unif_prob C hC

/-- The mass of a fixed coin value is a Borel function of the mean. -/
theorem ex_bern_measurable (c : Bool) : Measurable fun o : ℝ => bern o c := by
  cases c
  · simp only [bern, Bool.false_eq_true, ite_false]; fun_prop
  · simp only [bern, ite_true]; fun_prop

/-- `margPolicy` is a Borel function of the history: on the histories with actions `a ∈ C^t` it is a Borel
function of the losses, and the other histories get the uniform vector. -/
theorem ex_marg_meas {d : ℕ} (C : Finset (E d)) (P : (t : ℕ) → (Fin t → C × Bool) → C → ℝ) (t : ℕ) :
    Measurable (margPolicy C P t) := by
  classical
  let W : (Fin t → C) → (Fin t → ℝ) → (Fin t → Bool) → ℝ := fun a o b =>
    ∏ s : Fin t, P s (fun i : Fin s => (a (Fin.castLE s.2.le i), b (Fin.castLE s.2.le i))) (a s) * bern (o s) (b s)
  let G : (Fin t → C) × (Fin t → ℝ) → C → ℝ := fun ao =>
    if 0 < ∑ b : Fin t → Bool, W ao.1 ao.2 b then
      fun y => ∑ b : Fin t → Bool, W ao.1 ao.2 b / (∑ b' : Fin t → Bool, W ao.1 ao.2 b') *
        P t (fun i => (ao.1 i, b i)) y
    else fun _ => 1 / (C.card : ℝ)
  have hW : ∀ a b, Measurable fun o => W a o b := by
    intro a b
    refine Finset.measurable_prod _ fun s _ => ?_
    exact measurable_const.mul ((ex_bern_measurable _).comp (measurable_pi_apply s))
  have hG : Measurable G := by
    refine measurable_from_prod_countable_right fun a => ?_
    have hZ : Measurable fun o => ∑ b : Fin t → Bool, W a o b := Finset.measurable_sum _ fun b _ => hW a b
    refine Measurable.ite (measurableSet_lt measurable_const hZ) ?_ measurable_const
    refine Measurable.of_eval fun y => ?_
    exact Finset.measurable_sum _ fun b _ => ((hW a b).div hZ).mul (by dsimp only; exact measurable_const)
  let S : Set (Fin t → E d × ℝ) := {χ | ∀ i, (χ i).1 ∈ C}
  have hS : MeasurableSet S := by
    have : S = ⋂ i, (fun χ : Fin t → E d × ℝ => (χ i).1) ⁻¹' (C : Set (E d)) := by
      ext χ; simp [S]
    rw [this]
    exact MeasurableSet.iInter fun i => (measurable_fst.comp (measurable_pi_apply i)) C.measurableSet
  let proj : S → (Fin t → C) × (Fin t → ℝ) := fun χ => (fun i => ⟨(χ.1 i).1, χ.2 i⟩, fun i => (χ.1 i).2)
  have hproj : Measurable proj := by
    refine Measurable.prodMk (Measurable.of_eval fun i => ?_) (Measurable.of_eval fun i => ?_)
    · exact (measurable_fst.comp ((measurable_pi_apply i).comp measurable_subtype_coe)).subtype_mk
    · exact measurable_snd.comp ((measurable_pi_apply i).comp measurable_subtype_coe)
  have heq : margPolicy C P t =
      fun χ => if hχ : χ ∈ S then G (proj ⟨χ, hχ⟩) else (fun _ => 1 / (C.card : ℝ)) := by
    funext χ
    unfold margPolicy
    by_cases hχ : χ ∈ S
    · have h' : ∀ i, (χ i).1 ∈ C := hχ
      rw [dite_eq_left h', dite_eq_left hχ]
    · have h' : ¬∀ i, (χ i).1 ∈ C := hχ
      rw [dite_eq_right h', dite_eq_right hχ]
  rw [heq]
  exact Measurable.dite (hG.comp hproj) measurable_const hS

/-- The law of play over `n + 1` rounds, split at the last round. -/
theorem ex_playLaw_succ {d : ℕ} {C : Finset (E d)} (pol : (t : ℕ) → (Fin t → E d × ℝ) → C → ℝ)
    (f : ℕ → E d → ℝ) (n : ℕ) (y : Fin (n + 1) → C) :
    playLaw pol f (n + 1) y =
      playLaw pol f n (Fin.init y) * pol n (fun i => ((Fin.init y i : E d), f i (Fin.init y i))) (y (Fin.last n)) := by
  unfold playLaw
  rw [Fin.prod_univ_castSucc]
  rfl

/-- The law of actions and coins over `n + 1` rounds, split at the last round. -/
theorem ex_coinLaw_succ {d : ℕ} {C : Type*} (pt : C → E d) (P : (t : ℕ) → (Fin t → C × Bool) → C → ℝ)
    (f : ℕ → E d → ℝ) (n : ℕ) (x : Fin (n + 1) → C) (b : Fin (n + 1) → Bool) :
    coinLaw pt P (fun t _ => f t) (n + 1) (fun t => (x t, b t)) =
      coinLaw pt P (fun t _ => f t) n (fun t => (Fin.init x t, Fin.init b t)) *
        (P n (fun i => (Fin.init x i, Fin.init b i)) (x (Fin.last n)) * bern (f n (pt (x (Fin.last n)))) (b (Fin.last n))) := by
  unfold coinLaw
  rw [Fin.prod_univ_castSucc]
  rfl

/-- The value of `margPolicy` on the history of actions `x` and losses `f`. -/
theorem ex_marg_at {d : ℕ} (C : Finset (E d)) (P : (t : ℕ) → (Fin t → C × Bool) → C → ℝ) (f : ℕ → E d → ℝ)
    (t : ℕ) (x : Fin t → C) (y : C) :
    margPolicy C P t (fun i => ((x i : E d), f i (x i))) y =
      if 0 < ∑ b : Fin t → Bool, coinLaw Subtype.val P (fun t _ => f t) t (fun s => (x s, b s)) then
        ∑ b : Fin t → Bool, coinLaw Subtype.val P (fun t _ => f t) t (fun s => (x s, b s)) /
          (∑ b' : Fin t → Bool, coinLaw Subtype.val P (fun t _ => f t) t (fun s => (x s, b' s))) *
            P t (fun i => (x i, b i)) y
      else 1 / (C.card : ℝ) := by
  unfold margPolicy
  have hx : ∀ i, ((fun i => ((x i : E d), f i (x i))) i).1 ∈ C := fun i => (x i).2
  split_ifs with h0 h1 h1
  · rfl
  · exact absurd h0 h1
  · exact absurd h1 h0
  · rfl

/-- The law of play of `margPolicy` is the law of the actions of the learner with coins. -/
theorem ex_marg_law {d : ℕ} (C : Finset (E d)) (P : (t : ℕ) → (Fin t → C × Bool) → C → ℝ)
    (hP : ∀ t h, P t h ∈ probVecs C) (f : ℕ → E d → ℝ) (n : ℕ) (hf : ∀ t < n, ∀ x ∈ C, f t x ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin n → C) :
    playLaw (margPolicy C P) f n x =
      ∑ b : Fin n → Bool, coinLaw Subtype.val P (fun t _ => f t) n fun t => (x t, b t) := by
  classical
  revert hf x
  induction n with
  | zero => intro _ x; simp [playLaw, coinLaw]
  | succ n ih =>
    intro hf x
    have hf' : ∀ t < n, ∀ x ∈ C, f t x ∈ Set.Icc (0 : ℝ) 1 := fun t ht => hf t (by omega)
    rw [ex_playLaw_succ, ih hf' (Fin.init x), ex_marg_at]
    have hW0 : ∀ b : Fin n → Bool,
        0 ≤ coinLaw Subtype.val P (fun t _ => f t) n (fun s => (Fin.init x s, b s)) := by
      intro b
      unfold coinLaw
      refine Finset.prod_nonneg fun s _ => mul_nonneg ?_ (ex_bern_nonneg _ ?_ _)
      · obtain ⟨h1, -⟩ := hP s (fun i : Fin s => (Fin.init x (Fin.castLE s.2.le i), b (Fin.castLE s.2.le i)))
        exact h1 _
      · exact hf' s s.2 _ (Fin.init x s).2
    have hR : ∑ b' : Fin (n + 1) → Bool, coinLaw Subtype.val P (fun t _ => f t) (n + 1) (fun t => (x t, b' t)) =
        ∑ b : Fin n → Bool, coinLaw Subtype.val P (fun t _ => f t) n (fun s => (Fin.init x s, b s)) *
          P n (fun i => (Fin.init x i, b i)) (x (Fin.last n)) := by
      simp_rw [ex_coinLaw_succ]
      rw [← (Fin.snocEquiv (fun _ => Bool)).sum_comp]
      have hs : ∀ (c : Bool) (b : Fin n → Bool), (Fin.snocEquiv (fun _ => Bool)) (c, b) = Fin.snoc b c :=
        fun _ _ => rfl
      simp only [hs, Fin.init_snoc, Fin.snoc_last, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      refine Fintype.sum_congr _ _ fun b => ?_
      rw [Fintype.sum_bool]
      simp only [bern, ite_true, Bool.false_eq_true, ite_false]
      ring
    rw [hR]
    split_ifs with hZ
    · rw [Finset.mul_sum]
      refine Fintype.sum_congr _ _ fun b => ?_
      field_simp
    · have hZ0 : ∑ b : Fin n → Bool, coinLaw Subtype.val P (fun t _ => f t) n (fun s => (Fin.init x s, b s)) = 0 :=
        le_antisymm (not_lt.1 hZ) (Finset.sum_nonneg fun b _ => hW0 b)
      have hb := (Finset.sum_eq_zero_iff_of_nonneg fun b _ => hW0 b).1 hZ0
      rw [hZ0, zero_mul]
      exact (Finset.sum_eq_zero fun b hb' => by rw [hb b hb', zero_mul]).symm

/-- A policy with the law of actions of a learner with coins has its regret. -/
theorem ex_marg_reg {d : ℕ} (K : Set (E d)) (C : Finset (E d)) (pol : (t : ℕ) → (Fin t → E d × ℝ) → C → ℝ)
    (P : (t : ℕ) → (Fin t → C × Bool) → C → ℝ) (f : ℕ → E d → ℝ) (n : ℕ)
    (hlaw : ∀ x : Fin n → C, playLaw pol f n x =
      ∑ b : Fin n → Bool, coinLaw Subtype.val P (fun t _ => f t) n fun t => (x t, b t)) :
    policyReg K C pol f n = coinReg K Subtype.val P f n := by
  unfold policyReg coinReg
  congr 1
  simp_rw [hlaw, Finset.sum_mul]
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => C) (fun _ => Bool)).symm _ _
    fun _ => rfl

/-- Lemma 7.13. -/
theorem lemmaMarg : LemmaMarg := by
  intro d K C hCK hC P hP
  refine ⟨ex_marg_cpolicy K C hCK hC P hP, ex_marg_meas C P, fun n f hf => ?_⟩
  have hf' : ∀ t < n, ∀ x ∈ C, f t x ∈ Set.Icc (0 : ℝ) 1 := fun t ht x hx => (hf t ht).2 x (hCK hx)
  have hlaw := ex_marg_law C P hP f n hf'
  exact ⟨hlaw, ex_marg_reg K C _ P f n hlaw⟩

end AdversarialBco.Explicit
