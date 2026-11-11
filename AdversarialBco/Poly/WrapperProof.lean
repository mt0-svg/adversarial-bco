/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Wrapper

@[expose] public section

/-!
# Lemma D.14, the restart wrapper: proofs

Proof of the interface statement `AdversarialBco.Poly.LemmaW` of `AdversarialBco/Poly/Wrapper.lean`: four leaves
(`wrap_segment_exit`, the point where the segment from a point of `Kτ` to a
point of `Keps \ Kτ` leaves `Kτ`; `lemmaW_a`, `lemmaW_b`, `lemmaW_c`, the three parts), then the assembly `lemmaW`.
-/

/-! ## Leaves -/

theorem AdversarialBco.Poly.wrap_segment_exit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Keps Kτ : Set E) (hconv : Convex ℝ Keps)
    (hKτ : IsClosed Kτ) (hsub : Kτ ⊆ Keps) (y x : E) (hy : y ∈ Kτ) (hx : x ∈ Keps) (hxK : x ∉ Kτ) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, y + t • (x - y) ∈ Kτ ∧ y + t • (x - y) ∈ closure (Keps \ Kτ) := by
  let p : ℝ → E := λ t => y + t • (x - y)
  have hp_cont : Continuous p := by
    unfold p
    exact Continuous.add continuous_const (continuous_id.smul continuous_const)
  let T : Set ℝ := {t | t ∈ Set.Icc (0 : ℝ) 1 ∧ p t ∈ Kτ}
  have hT_closed : IsClosed T := by
    have hIcc_closed : IsClosed (Set.Icc (0 : ℝ) 1) := isClosed_Icc
    have hp_preimage_closed : IsClosed (p⁻¹' Kτ) := hKτ.preimage hp_cont
    have h_eq : T = Set.Icc (0 : ℝ) 1 ∩ p⁻¹' Kτ := by
      ext t; simp [T]
    rw [h_eq]
    exact IsClosed.inter hIcc_closed hp_preimage_closed
  have hT_nonempty : T.Nonempty := by
    have h0_Icc : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have hp0_Kτ : p 0 ∈ Kτ := by
      have : p 0 = y := by
        unfold p; simp
      rw [this]
      exact hy
    exact ⟨0, h0_Icc, hp0_Kτ⟩
  have hT_bddAbove : BddAbove T := by
    refine ⟨1, ?_⟩
    intro t ht
    rcases ht with ⟨ht_Icc, _⟩
    exact ht_Icc.2
  let tstar : ℝ := sSup T
  have htstar_mem_T : tstar ∈ T :=
    IsClosed.csSup_mem hT_closed hT_nonempty hT_bddAbove
  have htstar_Icc : tstar ∈ Set.Icc (0 : ℝ) 1 := htstar_mem_T.1
  have hp_tstar_Kτ : p tstar ∈ Kτ := htstar_mem_T.2
  have htstar_lt_one : tstar < 1 := by
    by_contra! hge
    have htstar_eq_one : tstar = 1 := le_antisymm htstar_Icc.2 hge
    have hp_tstar_eq_x : p tstar = x := by
      calc
        p tstar = y + tstar • (x - y) := rfl
        _ = y + (1 : ℝ) • (x - y) := by rw [htstar_eq_one]
        _ = y + (x - y) := by simp
        _ = x := by abel
    rw [hp_tstar_eq_x] at hp_tstar_Kτ
    exact hxK hp_tstar_Kτ
  have h_conv_mem : ∀ t ∈ Set.Ioc tstar 1, p t ∈ Keps := by
    intro t ht
    rcases ht with ⟨ht_left, ht_right⟩
    have ht_nonneg : 0 ≤ t := by linarith [htstar_Icc.1, ht_left]
    have h_t_in_Icc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht_nonneg, ht_right⟩
    have hy_Keps : y ∈ Keps := hsub hy
    have h_segment_subset : segment ℝ y x ⊆ Keps :=
      (convex_iff_segment_subset.mp hconv) hy_Keps hx
    have hp_t_in_segment : p t ∈ segment ℝ y x := by
      rw [segment_eq_image']
      refine ⟨t, h_t_in_Icc, rfl⟩
    exact h_segment_subset hp_t_in_segment
  have hp_not_Kτ : ∀ t ∈ Set.Ioc tstar 1, p t ∉ Kτ := by
    intro t ht
    rcases ht with ⟨ht_left, ht_right⟩
    intro hp_t_Kτ
    have ht_nonneg : 0 ≤ t := by linarith [htstar_Icc.1, ht_left]
    have ht_Icc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht_nonneg, ht_right⟩
    have ht_T : t ∈ T := ⟨ht_Icc, hp_t_Kτ⟩
    have ht_le_tstar : t ≤ tstar := le_csSup hT_bddAbove ht_T
    linarith
  have hp_tstar_closure : p tstar ∈ closure (Keps \ Kτ) := by
    have hp_cont_at : ContinuousAt p tstar := hp_cont.continuousAt
    have h_tendsto_nhds : Filter.Tendsto p (nhds tstar) (nhds (p tstar)) := hp_cont_at.tendsto
    have h_tendsto : Filter.Tendsto p (nhdsWithin tstar (Set.Ioi tstar)) (nhds (p tstar)) :=
      h_tendsto_nhds.mono_left nhdsWithin_le_nhds
    have h_forall : ∀ t ∈ Set.Ioc tstar 1, p t ∈ Keps \ Kτ := by
      intro t ht
      have h_Keps : p t ∈ Keps := h_conv_mem t ht
      have h_not_Kτ : p t ∉ Kτ := hp_not_Kτ t ht
      exact ⟨h_Keps, h_not_Kτ⟩
    have h_Ioc_mem : Set.Ioc tstar 1 ∈ nhdsWithin tstar (Set.Ioi tstar) :=
      Ioc_mem_nhdsGT htstar_lt_one
    have h_eventually : ∀ᶠ t in nhdsWithin tstar (Set.Ioi tstar), p t ∈ Keps \ Kτ :=
      Filter.eventually_of_mem h_Ioc_mem h_forall
    exact mem_closure_of_tendsto h_tendsto h_eventually
  refine ⟨tstar, htstar_Icc, hp_tstar_Kτ, hp_tstar_closure⟩

theorem AdversarialBco.Poly.lemmaW_a {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Keps Kτ : Set E) (τ : ℕ) (s : ℕ → E → ℝ) (σ : ℕ → ℝ) (xs : ℕ → E)
    (Ereg A₁ A₅ κs : ℝ) (Fire : Prop) (hτ : 1 ≤ τ) (hxs : xs τ ∈ Keps)
    (hprev : ∀ y ∈ Keps, AdversarialBco.Poly.wrapS s (τ - 1) (xs (τ - 1)) ≤ AdversarialBco.Poly.wrapS s (τ - 1) y)
    (hW0 : xs (τ - 1) ∈ Kτ) (hW1 : Ereg ≤ AdversarialBco.Poly.wrapReg s σ τ (xs τ) + A₁)
    (hW4s : Fire → ∀ y ∈ Kτ, AdversarialBco.Poly.wrapReg s σ τ y ≤ -κs)
    (hW5 : s τ (xs (τ - 1)) - s τ (xs τ) ≤ A₅) (hκs : A₁ + A₅ ≤ κs) (hF : Fire) : Ereg ≤ 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hτ
  have hsum_split (x : E) : AdversarialBco.Poly.wrapReg s σ (m + 1) x =
      AdversarialBco.Poly.wrapReg s σ m x + σ (m + 1) - s (m + 1) x := by
    dsimp [AdversarialBco.Poly.wrapReg, AdversarialBco.Poly.wrapS]
    have hσ : ∑ u ∈ Finset.Icc 1 (m + 1), σ u = (∑ u ∈ Finset.Icc 1 m, σ u) + σ (m + 1) := by
      rw [Finset.sum_Icc_succ_top (by omega) σ]
    have hs : ∑ u ∈ Finset.Icc 1 (m + 1), s u x = (∑ u ∈ Finset.Icc 1 m, s u x) + s (m + 1) x := by
      rw [Finset.sum_Icc_succ_top (by omega) (fun u => s u x)]
    rw [hσ, hs]
    ring
  have h_reg_m : AdversarialBco.Poly.wrapReg s σ (m + 1) (xs m) ≤ -κs :=
    hW4s hF (xs m) hW0
  have h_prev' : AdversarialBco.Poly.wrapS s m (xs m) ≤ AdversarialBco.Poly.wrapS s m (xs (m + 1)) :=
    hprev (xs (m + 1)) hxs
  have h_main : AdversarialBco.Poly.wrapReg s σ (m + 1) (xs (m + 1)) ≤
      AdversarialBco.Poly.wrapReg s σ (m + 1) (xs m) + A₅ := by
    rw [hsum_split (xs (m + 1)), hsum_split (xs m)]
    dsimp [AdversarialBco.Poly.wrapReg, AdversarialBco.Poly.wrapS] at *
    linarith
  have h_reg_final : AdversarialBco.Poly.wrapReg s σ (m + 1) (xs (m + 1)) ≤ -κs + A₅ := by
    linarith
  have h_final : Ereg ≤ A₁ + A₅ - κs := by
    linarith
  linarith

theorem AdversarialBco.Poly.lemmaW_b {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Keps Kτ : Set E) (τ : ℕ) (s : ℕ → E → ℝ) (σ : ℕ → ℝ) (xs : ℕ → E)
    (β : E → ℝ) (A₂ κc b : ℝ) (Fire : Prop) (hconv : Convex ℝ Keps) (hKτ : IsClosed Kτ) (hsub : Kτ ⊆ Keps)
    (hS : ConvexOn ℝ Keps (AdversarialBco.Poly.wrapS s τ)) (hxs : xs τ ∈ Keps)
    (hmin : ∀ y ∈ Keps, AdversarialBco.Poly.wrapS s τ (xs τ) ≤ AdversarialBco.Poly.wrapS s τ y)
    (hW2 : ∀ y ∈ Kτ, AdversarialBco.Poly.wrapReg s σ τ y ≤ A₂ - β y)
    (hW3 : ∀ y ∈ Kτ, y ∈ closure (Keps \ Kτ) → b ≤ β y)
    (hW4c : (∀ y ∈ Kτ, AdversarialBco.Poly.wrapReg s σ τ y ≤ -κc) → Fire) (hb : A₂ + κc ≤ b)
    (hout : xs τ ∉ Kτ) : Fire := by
  apply hW4c
  intro y hy
  have hyKeps : y ∈ Keps := hsub hy
  rcases AdversarialBco.Poly.wrap_segment_exit Keps Kτ hconv hKτ hsub y (xs τ) hy hxs hout with
    ⟨t, ht, hy₁Kτ, hy₁closure⟩
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have h_one_minus_t_nonneg : 0 ≤ 1 - t := by linarith
  have hsum : (1 - t) + t = 1 := by ring
  have hy₁_eq : y + t • (xs τ - y) = (1 - t) • y + t • (xs τ) := by
    calc
      y + t • (xs τ - y) = y + (t • (xs τ) - t • y) := by rw [smul_sub]
      _ = (y - t • y) + t • (xs τ) := by abel
      _ = (1 • y - t • y) + t • (xs τ) := by rw [one_smul]
      _ = ((1 - t) • y) + t • (xs τ) := by
        apply congrArg (· + t • (xs τ))
        simpa using (sub_smul 1 t y).symm
  have hS_ineq : AdversarialBco.Poly.wrapS s τ (y + t • (xs τ - y)) ≤
      (1 - t) • AdversarialBco.Poly.wrapS s τ y + t • AdversarialBco.Poly.wrapS s τ (xs τ) := by
    have h := hS.2 hyKeps hxs h_one_minus_t_nonneg ht0 hsum
    calc
      AdversarialBco.Poly.wrapS s τ (y + t • (xs τ - y)) =
          AdversarialBco.Poly.wrapS s τ ((1 - t) • y + t • (xs τ)) := by rw [hy₁_eq]
      _ ≤ (1 - t) • AdversarialBco.Poly.wrapS s τ y + t • AdversarialBco.Poly.wrapS s τ (xs τ) := h
  have hS_y₁_le_S_y : AdversarialBco.Poly.wrapS s τ (y + t • (xs τ - y)) ≤
      AdversarialBco.Poly.wrapS s τ y := by
    have hmin' := hmin y hyKeps
    have htemp : t • AdversarialBco.Poly.wrapS s τ (xs τ) ≤ t • AdversarialBco.Poly.wrapS s τ y :=
      mul_le_mul_of_nonneg_left hmin' ht0
    calc
      AdversarialBco.Poly.wrapS s τ (y + t • (xs τ - y)) ≤
          (1 - t) • AdversarialBco.Poly.wrapS s τ y + t • AdversarialBco.Poly.wrapS s τ (xs τ) := hS_ineq
      _ ≤ (1 - t) • AdversarialBco.Poly.wrapS s τ y + t • AdversarialBco.Poly.wrapS s τ y := by linarith
      _ = ((1 - t) + t) • AdversarialBco.Poly.wrapS s τ y := by rw [add_smul]
      _ = 1 • AdversarialBco.Poly.wrapS s τ y := by simp [hsum]
      _ = AdversarialBco.Poly.wrapS s τ y := by rw [one_smul]
  have hreg : AdversarialBco.Poly.wrapReg s σ τ y ≤
      AdversarialBco.Poly.wrapReg s σ τ (y + t • (xs τ - y)) := by
    unfold AdversarialBco.Poly.wrapReg
    linarith
  have hreg_y₁_W2 : AdversarialBco.Poly.wrapReg s σ τ (y + t • (xs τ - y)) ≤
      A₂ - β (y + t • (xs τ - y)) := hW2 (y + t • (xs τ - y)) hy₁Kτ
  have hbeta : b ≤ β (y + t • (xs τ - y)) := hW3 (y + t • (xs τ - y)) hy₁Kτ hy₁closure
  have hb_ineq : A₂ - β (y + t • (xs τ - y)) ≤ A₂ - b := by linarith
  have hfinal : A₂ - b ≤ -κc := by linarith
  linarith

theorem AdversarialBco.Poly.lemmaW_c {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Keps Kτ Kτ1 : Set E) (τ : ℕ) (s : ℕ → E → ℝ) (σ : ℕ → ℝ) (xs : ℕ → E)
    (β : E → ℝ) (Ereg A₁ A₂ κc b : ℝ) (Fire : Prop) (hsub : Kτ ⊆ Keps) (hβ : ∀ y ∈ Kτ, 0 ≤ β y)
    (hmin : ∀ y ∈ Keps, AdversarialBco.Poly.wrapS s τ (xs τ) ≤ AdversarialBco.Poly.wrapS s τ y)
    (hW1 : Ereg ≤ AdversarialBco.Poly.wrapReg s σ τ (xs τ) + A₁)
    (hW2 : ∀ y ∈ Kτ, AdversarialBco.Poly.wrapReg s σ τ y ≤ A₂ - β y)
    (hW3' : ∀ y ∈ Kτ, β y < b → y ∈ Kτ1)
    (hW4c : (∀ y ∈ Kτ, AdversarialBco.Poly.wrapReg s σ τ y ≤ -κc) → Fire) (hb : A₂ + κc ≤ b)
    (hin : xs τ ∈ Kτ) (hF : ¬ Fire) : xs τ ∈ Kτ1 ∧ Ereg ≤ A₁ + A₂ := by
  have h_not_all : ¬ (∀ y ∈ Kτ, AdversarialBco.Poly.wrapReg s σ τ y ≤ -κc) := by
    intro h_all
    exact hF (hW4c h_all)
  push Not at h_not_all
  rcases h_not_all with ⟨y, hy, hy_not⟩
  have hy_gt : -κc < AdversarialBco.Poly.wrapReg s σ τ y := by linarith
  have hxs_min : AdversarialBco.Poly.wrapS s τ (xs τ) ≤ AdversarialBco.Poly.wrapS s τ y :=
    hmin y (hsub hy)
  have h_wrapReg_xs_ge : AdversarialBco.Poly.wrapReg s σ τ y ≤ AdversarialBco.Poly.wrapReg s σ τ (xs τ) := by
    unfold AdversarialBco.Poly.wrapReg
    exact sub_le_sub_left hxs_min (∑ u ∈ Finset.Icc 1 τ, σ u)
  have hβ_xs_lt_b : β (xs τ) < b := by
    have hW2_xs := hW2 (xs τ) hin
    have h_ineq : -κc < A₂ - β (xs τ) := by linarith
    have h_lt : β (xs τ) < A₂ + κc := by linarith
    linarith
  have h_first : xs τ ∈ Kτ1 := hW3' (xs τ) hin hβ_xs_lt_b
  have h_second : Ereg ≤ A₁ + A₂ := by
    have hW2_xs := hW2 (xs τ) hin
    have hβ_xs_nonneg : 0 ≤ β (xs τ) := hβ (xs τ) hin
    linarith
  exact And.intro h_first h_second

/-! ## Assembly -/

namespace AdversarialBco.Poly

/-- Lemma D.14. -/
theorem lemmaW : LemmaW := by
  intro E _ _ Keps Kτ Kτ1 τ s σ xs β Ereg A₁ A₂ A₅ κs κc b Fire hτ hconv hKτ hsub hsub1 hS hxs hmin hprev hβ hW0 hW1
    hW2 hW3 hW3' hW4s hW4c hW5 hκs hb
  have hB : xs τ ∉ Kτ → Fire :=
    lemmaW_b Keps Kτ τ s σ xs β A₂ κc b Fire hconv hKτ hsub hS hxs hmin hW2 hW3 hW4c hb
  refine ⟨lemmaW_a Keps Kτ τ s σ xs Ereg A₁ A₅ κs Fire hτ hxs hprev hW0 hW1 hW4s hW5 hκs, hB, fun hF => ?_⟩
  have hin : xs τ ∈ Kτ := by
    by_contra h
    exact hF (hB h)
  exact lemmaW_c Keps Kτ Kτ1 τ s σ xs β Ereg A₁ A₂ κc b Fire hsub hβ hmin hW1 hW2 hW3' hW4c hb hin hF

end AdversarialBco.Poly
