/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2Layer2

@[expose] public section

/-!
# The law of the positioning block

`df2oOmega_law : gaussStream.map (df2oOmega d n r0 R0 δ1) = pgMeasure d`. The stream of PG reads the Gaussian stream
at the indices `df2oIdxA` (descent vectors) and `df2oIdxT` (test vectors); these are injective with disjoint ranges
(a mixed-radix layout inside the block of PG, `Nat.pair` past the spare index, `mrA_inj`, `mrT_inj`, `mrA_ne_mrT`).
The image of independent standard Gaussian terms under an injective reindexing is again independent
(`infinitePi_comp_inj`); the descent and the test coordinates split as a product (`infinitePi_sum_prod`); the `d`
coordinates of a vector form a standard Gaussian vector of `E d` (`infinitePi_group`); currying arranges the stages
and the repeats (`Measure.infinitePi_map_curry`).
-/

open MeasureTheory ProbabilityTheory
open AdversarialBco.RealRAM

namespace AdversarialBco.Poly

namespace Layer2

/-! ## The layout of the indices -/

/-- The offset of stage `i` in a mixed-radix layout: `∑_{i' < i} J W_{i'} d`. -/
def mrOff (Jr d : ℕ) (W : ℕ → ℕ) (i : ℕ) : ℕ := ∑ i' ∈ Finset.range i, Jr * W i' * d

open Classical in
/-- The index of coordinate `c` of descent vector `k` of repeat `r` of stage `i` (the layout of `df2oIdxA`). -/
noncomputable def mrA (m Jr d S : ℕ) (Ns W : ℕ → ℕ) (i r k : ℕ) (c : Fin d) : ℕ :=
  if i < m ∧ r < Jr ∧ k < Ns i then mrOff Jr d W i + (r * W i + k) * d + c
  else S + Nat.pair (Nat.pair i r) (Nat.pair (2 * k) c)

open Classical in
/-- The index of coordinate `c` of test vector `k` of verdict `v` of repeat `r` of stage `i` (that of `df2oIdxT`). -/
noncomputable def mrT (m Jr MT d S : ℕ) (Ns NT W : ℕ → ℕ) (i r v k : ℕ) (c : Fin d) : ℕ :=
  if i < m ∧ r < Jr ∧ v < MT ∧ k < NT i then mrOff Jr d W i + (r * W i + Ns i + v * NT i + k) * d + c
  else S + Nat.pair (Nat.pair i r) (Nat.pair (2 * Nat.pair v k + 1) c)

/-- Division with remainder: `x k + c = y k + c'` with `c, c' < k` gives `x = y` and `c = c'`. -/
theorem mr_divmod_inj (k x y c c' : ℕ) (hc : c < k) (hc' : c' < k) (h : x * k + c = y * k + c') :
    x = y ∧ c = c' := by
  have hk : 0 < k := by omega
  have h1 : (x * k + c) / k = x := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hc, Nat.zero_add]
  have h2 : (y * k + c') / k = y := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hc', Nat.zero_add]
  have hxy : x = y := by rw [← h1, ← h2, h]
  subst hxy
  exact ⟨rfl, by omega⟩

/-- An index of stage `i < m` with offset `x < Jr * W i * d` lies below `mrOff Jr d W m`. -/
theorem mrOff_add_lt (Jr d m i x : ℕ) (W : ℕ → ℕ) (hi : i < m) (hx : x < Jr * W i * d) :
    mrOff Jr d W i + x < mrOff Jr d W m := by
  have h1 : mrOff Jr d W (i + 1) = mrOff Jr d W i + Jr * W i * d := by
    simp [mrOff, Finset.sum_range_succ]
  have h2 : mrOff Jr d W (i + 1) ≤ mrOff Jr d W m :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hi) (fun _ _ _ => Nat.zero_le _)
  omega

theorem mr_slot_lt (Jr W d r y : ℕ) (c : ℕ) (hr : r < Jr) (hy : y < W) (hc : c < d) :
    (r * W + y) * d + c < Jr * W * d := by
  have h1 : (r * W + y) * d + c < (r * W + y + 1) * d := by nlinarith
  have h2 : r * W + y + 1 ≤ Jr * W := by
    have : (r + 1) * W ≤ Jr * W := Nat.mul_le_mul_right _ hr
    nlinarith
  calc (r * W + y) * d + c < (r * W + y + 1) * d := h1
    _ ≤ Jr * W * d := Nat.mul_le_mul_right _ h2

/-- The stage of an index in range is determined by the index. -/
theorem mrOff_stage_eq (Jr d i i' x x' : ℕ) (W : ℕ → ℕ) (hx : x < Jr * W i * d) (hx' : x' < Jr * W i' * d)
    (h : mrOff Jr d W i + x = mrOff Jr d W i' + x') : i = i' := by
  rcases lt_trichotomy i i' with hl | hl | hl
  · have := mrOff_add_lt Jr d i' i x W hl hx
    omega
  · exact hl
  · have := mrOff_add_lt Jr d i i' x' W hl hx'
    omega

theorem mrA_inj (m Jr d S : ℕ) (Ns NT W : ℕ → ℕ) (MT : ℕ)
    (hW : ∀ i, W i = Ns i + MT * NT i) (hS : mrOff Jr d W m ≤ S) (i r k i' r' k' : ℕ) (c c' : Fin d)
    (h : mrA m Jr d S Ns W i r k c = mrA m Jr d S Ns W i' r' k' c') :
    i = i' ∧ r = r' ∧ k = k' ∧ c = c' := by
  have hc := c.isLt
  have hc' := c'.isLt
  unfold mrA at h
  split_ifs at h with h1 h2 h2
  · obtain ⟨hi, hr, hk⟩ := h1
    obtain ⟨hi', hr', hk'⟩ := h2
    have hkW : k < W i := by rw [hW i]; omega
    have hkW' : k' < W i' := by rw [hW i']; omega
    have hx := mr_slot_lt Jr (W i) d r k c hr hkW hc
    have hx' := mr_slot_lt Jr (W i') d r' k' c' hr' hkW' hc'
    have hii : i = i' := mrOff_stage_eq Jr d i i' _ _ W hx hx' (by omega)
    subst hii
    obtain ⟨e1, e2⟩ := mr_divmod_inj d (r * W i + k) (r' * W i + k') c c' hc hc' (by omega)
    obtain ⟨e3, e4⟩ := mr_divmod_inj (W i) r r' k k' hkW hkW' e1
    exact ⟨rfl, e3, e4, Fin.ext e2⟩
  · exfalso
    have hkW : k < W i := by rw [hW i]; omega
    have := mrOff_add_lt Jr d m i _ W h1.1 (mr_slot_lt Jr (W i) d r k c h1.2.1 hkW hc)
    omega
  · exfalso
    have hkW : k' < W i' := by rw [hW i']; omega
    have := mrOff_add_lt Jr d m i' _ W h2.1 (mr_slot_lt Jr (W i') d r' k' c' h2.2.1 hkW hc')
    omega
  · have e := Nat.add_left_cancel h
    rw [Nat.pair_eq_pair, Nat.pair_eq_pair, Nat.pair_eq_pair] at e
    exact ⟨e.1.1, e.1.2, by omega, Fin.ext e.2.2⟩

theorem mrT_inj (m Jr MT d S : ℕ) (Ns NT W : ℕ → ℕ)
    (hW : ∀ i, W i = Ns i + MT * NT i) (hS : mrOff Jr d W m ≤ S) (i r v k i' r' v' k' : ℕ) (c c' : Fin d)
    (h : mrT m Jr MT d S Ns NT W i r v k c = mrT m Jr MT d S Ns NT W i' r' v' k' c') :
    i = i' ∧ r = r' ∧ v = v' ∧ k = k' ∧ c = c' := by
  have hc := c.isLt
  have hc' := c'.isLt
  have hy : ∀ i v k, v < MT → k < NT i → Ns i + v * NT i + k < W i := fun i v k hv hk => by
    rw [hW i]
    have : (v + 1) * NT i ≤ MT * NT i := Nat.mul_le_mul_right _ hv
    nlinarith
  have hre : ∀ i r v k, r * W i + Ns i + v * NT i + k = r * W i + (Ns i + v * NT i + k) := fun _ _ _ _ => by ring
  unfold mrT at h
  split_ifs at h with h1 h2 h2
  · obtain ⟨hi, hr, hv, hk⟩ := h1
    obtain ⟨hi', hr', hv', hk'⟩ := h2
    rw [hre, hre] at h
    have hx := mr_slot_lt Jr (W i) d r _ c hr (hy i v k hv hk) hc
    have hx' := mr_slot_lt Jr (W i') d r' _ c' hr' (hy i' v' k' hv' hk') hc'
    have hii : i = i' := mrOff_stage_eq Jr d i i' _ _ W hx hx' (by omega)
    subst hii
    obtain ⟨e1, e2⟩ := mr_divmod_inj d (r * W i + (Ns i + v * NT i + k)) (r' * W i + (Ns i + v' * NT i + k')) c c'
      hc hc' (by omega)
    obtain ⟨e3, e4⟩ := mr_divmod_inj (W i) r r' _ _ (hy i v k hv hk) (hy i v' k' hv' hk') e1
    obtain ⟨e5, e6⟩ := mr_divmod_inj (NT i) v v' k k' hk hk' (by omega)
    exact ⟨rfl, e3, e5, e6, Fin.ext e2⟩
  · exfalso
    rw [hre] at h
    have := mrOff_add_lt Jr d m i _ W h1.1 (mr_slot_lt Jr (W i) d r _ c h1.2.1 (hy i v k h1.2.2.1 h1.2.2.2) hc)
    omega
  · exfalso
    rw [hre] at h
    have := mrOff_add_lt Jr d m i' _ W h2.1
      (mr_slot_lt Jr (W i') d r' _ c' h2.2.1 (hy i' v' k' h2.2.2.1 h2.2.2.2) hc')
    omega
  · have e := Nat.add_left_cancel h
    rw [Nat.pair_eq_pair, Nat.pair_eq_pair, Nat.pair_eq_pair] at e
    have e2 : Nat.pair v k = Nat.pair v' k' := by omega
    rw [Nat.pair_eq_pair] at e2
    exact ⟨e.1.1, e.1.2, e2.1, e2.2, Fin.ext e.2.2⟩

theorem mrA_ne_mrT (m Jr MT d S : ℕ) (Ns NT W : ℕ → ℕ)
    (hW : ∀ i, W i = Ns i + MT * NT i) (hS : mrOff Jr d W m ≤ S) (i r k i' r' v' k' : ℕ) (c c' : Fin d) :
    mrA m Jr d S Ns W i r k c ≠ mrT m Jr MT d S Ns NT W i' r' v' k' c' := by
  -- useful facts from hW
  have hNs_le_W : ∀ i, Ns i ≤ W i := by
    intro i; rw [hW i]; exact Nat.le_add_right _ _
  -- mrOff (i+1) = mrOff i + Jr * W i * d
  have hmroff_succ : ∀ i, mrOff Jr d W (i + 1) = mrOff Jr d W i + Jr * W i * d := by
    intro i; simp [mrOff, Finset.sum_range_succ]
  -- mrOff is monotone
  have hmroff_mono : ∀ {a b : ℕ}, a ≤ b → mrOff Jr d W a ≤ mrOff Jr d W b := by
    intro a b h
    refine Nat.le_induction (le_refl _) (fun k hk hle => ?_) b h
    rw [hmroff_succ k]
    exact le_trans hle (Nat.le_add_right _ _)
  -- helper: if a < Jr * Wi then a*d + c < Jr * Wi * d
  have h_ineq : ∀ {a Wi : ℕ} (c : Fin d), a < Jr * Wi → (a * d + (c : ℕ)) < Jr * Wi * d := by
    intro a Wi c ha
    have ha' : a + 1 ≤ Jr * Wi := Nat.succ_le_of_lt ha
    have hc_lt_d : (c : ℕ) < d := Fin.is_lt c
    nlinarith
  intro heq
  by_cases hi : i < m ∧ r < Jr ∧ k < Ns i
  · rcases hi with ⟨him, hir, hik⟩
    by_cases hi' : i' < m ∧ r' < Jr ∧ v' < MT ∧ k' < NT i'
    · rcases hi' with ⟨hi'm, hi'r, hi'v, hi'k⟩
      -- BOTH IN RANGE
      have hk_lt_Wi : k < W i := lt_of_lt_of_le hik (hNs_le_W i)
      simp [mrA, mrT, him, hir, hik, hi'm, hi'r, hi'v, hi'k] at heq
      by_cases hii' : i = i'
      · -- same stage i = i'
        subst hii'
        -- heq: mrOff Jr d W i + (r * W i + k) * d + c = mrOff Jr d W i + (r' * W i + Ns i + v' * NT i + k') * d + c'
        have heq' : (r * W i + k) * d + (c : ℕ) = (r' * W i + Ns i + v' * NT i + k') * d + (c' : ℕ) := by omega
        have hc_lt_d : (c : ℕ) < d := Fin.is_lt c
        have hc'_lt_d : (c' : ℕ) < d := Fin.is_lt c'
        -- Step 1: c = c' (by taking mod d)
        have hc_eq : (c : ℕ) = (c' : ℕ) := by
          have hmod := congrArg (fun x => x % d) heq'
          simp [Nat.mod_eq_of_lt hc_lt_d, Nat.mod_eq_of_lt hc'_lt_d] at hmod
          exact hmod
        -- Step 2: r*Wi + k = r'*Wi + Ns i + v'*NT i + k' (by dividing by d)
        have hdiv_eq : r * W i + k = r' * W i + Ns i + v' * NT i + k' := by
          have hdiv := congrArg (fun x => x / d) heq'
          have hleft : ((r * W i + k) * d + (c : ℕ)) / d = r * W i + k := by
            apply Nat.div_eq_of_lt_le
            · omega
            · nlinarith
          have hright : ((r' * W i + Ns i + v' * NT i + k') * d + (c' : ℕ)) / d = r' * W i + Ns i + v' * NT i + k' := by
            apply Nat.div_eq_of_lt_le
            · omega
            · nlinarith
          rw [hleft, hright] at hdiv
          exact hdiv
        -- Step 3: Ns i + v'*NT i + k' < W i
        have hsum_lt_Wi : Ns i + v' * NT i + k' < W i := by
          rw [hW i]
          have h1 : v' * NT i + k' < MT * NT i := by
            have hle : v' + 1 ≤ MT := Nat.succ_le_of_lt hi'v
            have h_mul : (v' + 1) * NT i ≤ MT * NT i := Nat.mul_le_mul hle (le_refl _)
            have h_eq : (v' + 1) * NT i = v' * NT i + NT i := by ring
            rw [h_eq] at h_mul
            omega
          omega
        -- Step 4: r = r' (by dividing hdiv_eq by W i)
        have hr_eq : r = r' := by
          have hdiv_r := congrArg (fun x => x / W i) hdiv_eq
          have hleft_r : (r * W i + k) / W i = r := by
            apply Nat.div_eq_of_lt_le
            · omega
            · have : (r + 1) * W i = r * W i + W i := by ring
              rw [this]
              omega
          have hright_r : (r' * W i + Ns i + v' * NT i + k') / W i = r' := by
            apply Nat.div_eq_of_lt_le
            · omega
            · have : (r' + 1) * W i = r' * W i + W i := by ring
              rw [this]
              omega
          rw [hleft_r, hright_r] at hdiv_r
          exact hdiv_r
        -- Step 5: k = Ns i + v'*NT i + k', contradiction with k < Ns i
        rw [hr_eq] at hdiv_eq
        have hk_eq : k = Ns i + v' * NT i + k' := by omega
        rw [hk_eq] at hik
        omega
      · -- i ≠ i'
        rcases Nat.lt_or_gt_of_ne hii' with (hlt | hlt')
        · -- i < i'
          -- Show mrA < mrOff Jr d W (i+1) ≤ mrOff Jr d W i' ≤ mrT
          have h_mrA_lt : (r * W i + k) * d + (c : ℕ) < Jr * W i * d :=
            h_ineq c (by
              -- need: r * W i + k < Jr * W i
              have h1 : r + 1 ≤ Jr := Nat.succ_le_of_lt hir
              have h2 : r * W i + k < r * W i + W i := Nat.add_lt_add_left hk_lt_Wi (r * W i)
              have h3 : r * W i + W i = (r + 1) * W i := by ring
              have h4 : (r + 1) * W i ≤ Jr * W i := Nat.mul_le_mul h1 (le_refl _)
              rw [h3] at h2
              omega)
          have h_mrOff_succ : mrOff Jr d W i + Jr * W i * d = mrOff Jr d W (i + 1) := by
            rw [hmroff_succ i]
          have h_mrA_total_lt : mrOff Jr d W i + (r * W i + k) * d + (c : ℕ) < mrOff Jr d W (i + 1) := by
            omega
          have h_le : mrOff Jr d W (i + 1) ≤ mrOff Jr d W i' := hmroff_mono (Nat.succ_le_of_lt hlt)
          have h_mrT_ge : mrOff Jr d W i' ≤ mrOff Jr d W i' + (r' * W i' + Ns i' + v' * NT i' + k') * d + (c' : ℕ) := by omega
          have h_mrA_lt_mrT : mrOff Jr d W i + (r * W i + k) * d + (c : ℕ) < mrOff Jr d W i' + (r' * W i' + Ns i' + v' * NT i' + k') * d + (c' : ℕ) := by
            omega
          rw [heq] at h_mrA_lt_mrT
          exact lt_irrefl _ h_mrA_lt_mrT
        · -- i' < i
          -- Show mrT < mrOff Jr d W (i'+1) ≤ mrOff Jr d W i ≤ mrA
          have hsum_lt_Wi' : Ns i' + v' * NT i' + k' < W i' := by
            rw [hW i']
            have h1 : v' * NT i' + k' < MT * NT i' := by
              have hle : v' + 1 ≤ MT := Nat.succ_le_of_lt hi'v
              have h_mul : (v' + 1) * NT i' ≤ MT * NT i' := Nat.mul_le_mul hle (le_refl _)
              have h_eq : (v' + 1) * NT i' = v' * NT i' + NT i' := by ring
              rw [h_eq] at h_mul
              omega
            omega
          have h_mrT_lt : (r' * W i' + Ns i' + v' * NT i' + k') * d + (c' : ℕ) < Jr * W i' * d :=
            h_ineq c' (by
              have h1 : r' + 1 ≤ Jr := Nat.succ_le_of_lt hi'r
              have h2 : r' * W i' + (Ns i' + v' * NT i' + k') < r' * W i' + W i' :=
                Nat.add_lt_add_left hsum_lt_Wi' (r' * W i')
              have h3 : r' * W i' + W i' = (r' + 1) * W i' := by ring
              have h4 : (r' + 1) * W i' ≤ Jr * W i' := Nat.mul_le_mul h1 (le_refl _)
              rw [h3] at h2
              omega)
          have h_mrOff_succ : mrOff Jr d W i' + Jr * W i' * d = mrOff Jr d W (i' + 1) := by
            rw [hmroff_succ i']
          have h_mrT_total_lt : mrOff Jr d W i' + (r' * W i' + Ns i' + v' * NT i' + k') * d + (c' : ℕ) < mrOff Jr d W (i' + 1) := by
            omega
          have h_le : mrOff Jr d W (i' + 1) ≤ mrOff Jr d W i := hmroff_mono (Nat.succ_le_of_lt hlt')
          have h_mrA_ge : mrOff Jr d W i ≤ mrOff Jr d W i + (r * W i + k) * d + (c : ℕ) := by omega
          have h_mrT_lt_mrA : mrOff Jr d W i' + (r' * W i' + Ns i' + v' * NT i' + k') * d + (c' : ℕ) < mrOff Jr d W i + (r * W i + k) * d + (c : ℕ) := by
            omega
          rw [← heq] at h_mrT_lt_mrA
          exact lt_irrefl _ h_mrT_lt_mrA
    · -- i' NOT in range, i in range
      simp [mrA, mrT, him, hir, hik] at heq
      -- heq: mrOff Jr d W i + (r * W i + k) * d + c = S + Nat.pair (Nat.pair i' r') (Nat.pair (2 * Nat.pair v' k' + 1) c')
      have h_lt : mrOff Jr d W i + (r * W i + k) * d + (c : ℕ) < S := by
        have hk_lt_Wi : k < W i := lt_of_lt_of_le hik (hNs_le_W i)
        have h_lt' : (r * W i + k) * d + (c : ℕ) < Jr * W i * d :=
          h_ineq c (by
            have h1 : r + 1 ≤ Jr := Nat.succ_le_of_lt hir
            have h2 : r * W i + k < r * W i + W i := Nat.add_lt_add_left hk_lt_Wi (r * W i)
            have h3 : r * W i + W i = (r + 1) * W i := by ring
            have h4 : (r + 1) * W i ≤ Jr * W i := Nat.mul_le_mul h1 (le_refl _)
            rw [h3] at h2
            omega)
        have h_mrOff_succ : mrOff Jr d W i + Jr * W i * d = mrOff Jr d W (i + 1) := by
          rw [hmroff_succ i]
        have h_lt_mrOff : mrOff Jr d W i + (r * W i + k) * d + (c : ℕ) < mrOff Jr d W (i + 1) := by
          omega
        have h_le : mrOff Jr d W (i + 1) ≤ mrOff Jr d W m := hmroff_mono (Nat.succ_le_of_lt him)
        omega
      have h_ge : S ≤ S + Nat.pair (Nat.pair i' r') (Nat.pair (2 * Nat.pair v' k' + 1) c') := by omega
      simp [hi'] at heq
      rw [heq] at h_lt
      omega
  · -- i NOT in range
    by_cases hi' : i' < m ∧ r' < Jr ∧ v' < MT ∧ k' < NT i'
    · -- i' in range, i not: symmetric to above
      rcases hi' with ⟨hi'm, hi'r, hi'v, hi'k⟩
      simp [mrA, mrT, hi'm, hi'r, hi'v, hi'k] at heq
      -- heq: S + Nat.pair (Nat.pair i r) (Nat.pair (2 * k) c) = mrOff Jr d W i' + (r' * W i' + Ns i' + v' * NT i' + k') * d + c'
      have h_lt : mrOff Jr d W i' + (r' * W i' + Ns i' + v' * NT i' + k') * d + (c' : ℕ) < S := by
        have hsum_lt_Wi' : Ns i' + v' * NT i' + k' < W i' := by
          rw [hW i']
          have h1 : v' * NT i' + k' < MT * NT i' := by
            have hle : v' + 1 ≤ MT := Nat.succ_le_of_lt hi'v
            have h_mul : (v' + 1) * NT i' ≤ MT * NT i' := Nat.mul_le_mul hle (le_refl _)
            have h_eq : (v' + 1) * NT i' = v' * NT i' + NT i' := by ring
            rw [h_eq] at h_mul
            omega
          omega
        have h_lt' : (r' * W i' + Ns i' + v' * NT i' + k') * d + (c' : ℕ) < Jr * W i' * d :=
          h_ineq c' (by
            have h1 : r' + 1 ≤ Jr := Nat.succ_le_of_lt hi'r
            have h2 : r' * W i' + (Ns i' + v' * NT i' + k') < r' * W i' + W i' :=
              Nat.add_lt_add_left hsum_lt_Wi' (r' * W i')
            have h3 : r' * W i' + W i' = (r' + 1) * W i' := by ring
            have h4 : (r' + 1) * W i' ≤ Jr * W i' := Nat.mul_le_mul h1 (le_refl _)
            rw [h3] at h2
            omega)
        have h_mrOff_succ : mrOff Jr d W i' + Jr * W i' * d = mrOff Jr d W (i' + 1) := by
          rw [hmroff_succ i']
        have h_lt_mrOff : mrOff Jr d W i' + (r' * W i' + Ns i' + v' * NT i' + k') * d + (c' : ℕ) < mrOff Jr d W (i' + 1) := by
          omega
        have h_le : mrOff Jr d W (i' + 1) ≤ mrOff Jr d W m := hmroff_mono (Nat.succ_le_of_lt hi'm)
        omega
      have h_ge : S ≤ S + Nat.pair (Nat.pair i r) (Nat.pair (2 * k) c) := by omega
      simp [hi] at heq
      rw [← heq] at h_lt
      omega
    · -- both NOT in range
      simp [mrA, mrT, hi, hi'] at heq
      -- heq: S + Nat.pair (Nat.pair i r) (Nat.pair (2 * k) c) = S + Nat.pair (Nat.pair i' r') (Nat.pair (2 * Nat.pair v' k' + 1) c')
      have hpair : Nat.pair (Nat.pair i r) (Nat.pair (2 * k) c) = Nat.pair (Nat.pair i' r') (Nat.pair (2 * Nat.pair v' k' + 1) c') := by omega
      rcases (Nat.pair_eq_pair.mp hpair) with ⟨hp1, hp2⟩
      -- hp2 : Nat.pair (2 * k) c = Nat.pair (2 * Nat.pair v' k' + 1) c'
      rcases (Nat.pair_eq_pair.mp hp2) with ⟨h2k, hc_eq⟩
      -- h2k : 2 * k = 2 * Nat.pair v' k' + 1
      have h_contra := Nat.two_mul_ne_two_mul_add_one (m := Nat.pair v' k') (n := k)
      -- h_contra : 2 * k ≠ 2 * Nat.pair v' k' + 1
      exact h_contra h2k

/-! ## Product measures -/

theorem infinitePi_comp_inj {X J : Type*} [MeasurableSpace X] [Countable J]
    (μ : Measure X) [IsProbabilityMeasure μ] (σ : J → ℕ) (hσ : Function.Injective σ) :
    (Measure.infinitePi fun _ : ℕ => μ).map (fun x : ℕ → X => fun j => x (σ j)) =
      Measure.infinitePi fun _ : J => μ := by
  classical
    apply MeasureTheory.Measure.eq_infinitePi
    intro s t ht
    have hmeas : Measurable (fun (x : ℕ → X) (j : J) => x (σ j)) := by
      refine Measurable.of_eval (fun j => ?_)
      exact measurable_pi_apply (σ j)
    have hmeasSet : MeasurableSet ((s : Set J).pi t) := by
      refine (measurableSet_pi (Finset.countable_toSet s)).mpr ?_
      left
      intro i hi
      exact ht i
    rw [Measure.map_apply hmeas hmeasSet]
    -- define t' : ℕ → Set X
    let t' : ℕ → Set X := fun i =>
      if h : i ∈ Finset.image σ s then
        t (Classical.choose (Finset.mem_image.1 h))
      else Set.univ
    have h_t'_eq : ∀ j ∈ s, t' (σ j) = t j := by
      intro j hj
      dsimp [t']
      have h_mem : σ j ∈ Finset.image σ s :=
        Finset.mem_image.mpr ⟨j, hj, rfl⟩
      simp [h_mem]
      have h_spec := Classical.choose_spec (Finset.mem_image.1 h_mem)
      -- h_spec : Classical.choose (Finset.mem_image.1 h_mem) ∈ s ∧ σ (Classical.choose (Finset.mem_image.1 h_mem)) = σ j
      have h_choose_eq : Classical.choose (Finset.mem_image.1 h_mem) = j := hσ h_spec.2
      rw [h_choose_eq]
    have h_preimage : (fun (x : ℕ → X) (j : J) => x (σ j)) ⁻¹' ((s : Set J).pi t) =
        ((Finset.image σ s : Set ℕ).pi t') := by
      ext x
      constructor
      · intro hx
        have hx' : ∀ j ∈ s, x (σ j) ∈ t j := by
          intro j hj
          have := hx j hj
          simpa using this
        intro i hi
        rw [Finset.mem_coe, Finset.mem_image] at hi
        rcases hi with ⟨j, hj, rfl⟩
        -- Need: x (σ j) ∈ t' (σ j)
        -- We know: x (σ j) ∈ t j, and t' (σ j) = t j
        rw [h_t'_eq j hj]
        exact hx' j hj
      · intro hx j hj
        have hi : σ j ∈ (Finset.image σ s : Set ℕ) := by
          apply Finset.mem_coe.mpr
          exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
        have hx' := hx (σ j) hi
        -- hx' : x (σ j) ∈ t' (σ j)
        -- We need: x (σ j) ∈ t j
        -- Since t' (σ j) = t j, we're done
        rw [h_t'_eq j hj] at hx'
        exact hx'
    rw [h_preimage]
    have hmeas_t' : ∀ i ∈ Finset.image σ s, MeasurableSet (t' i) := by
      intro i hi
      rw [Finset.mem_image] at hi
      rcases hi with ⟨j, hj, rfl⟩
      dsimp [t']
      have h_mem : σ j ∈ Finset.image σ s :=
        Finset.mem_image.mpr ⟨j, hj, rfl⟩
      have h_spec := Classical.choose_spec (Finset.mem_image.1 h_mem)
      -- h_spec : Classical.choose (Finset.mem_image.1 h_mem) ∈ s ∧ σ (Classical.choose (Finset.mem_image.1 h_mem)) = σ j
      have h_eq : Classical.choose (Finset.mem_image.1 h_mem) = j := hσ h_spec.2
      simp [h_mem]
      rw [h_eq]
      exact ht j
    rw [MeasureTheory.Measure.infinitePi_pi (fun _ => μ) hmeas_t']
    -- Now: ∏ i ∈ Finset.image σ s, μ (t' i) = ∏ j ∈ s, μ (t j)
    calc
      ∏ i ∈ Finset.image σ s, μ (t' i) = ∏ j ∈ s, μ (t' (σ j)) := by
        refine Finset.prod_image ?_
        intro x hx y hy h_eq
        exact hσ h_eq
      _ = ∏ j ∈ s, μ (t j) := by
        refine Finset.prod_congr rfl (fun j hj => ?_)
        rw [h_t'_eq j hj]

theorem infinitePi_sum_prod {X α β : Type*} [MeasurableSpace X] [Countable α]
    [Countable β] (μ : Measure X) [IsProbabilityMeasure μ] :
    (Measure.infinitePi fun _ : α ⊕ β => μ).map (fun x : α ⊕ β → X => (fun a => x (Sum.inl a), fun b => x (Sum.inr b))) =
      (Measure.infinitePi fun _ : α => μ).prod (Measure.infinitePi fun _ : β => μ) := by
  let P := fun _ : α ⊕ β => μ
  let f1 : (α ⊕ β → X) → (α → X) := fun x => x ∘ Sum.inl
  let f2 : (α ⊕ β → X) → (β → X) := fun x => x ∘ Sum.inr
  have hf1_meas : Measurable f1 := by
    rw [measurable_pi_iff]
    intro a
    simpa [f1] using measurable_pi_apply (Sum.inl a)
  have hf2_meas : Measurable f2 := by
    rw [measurable_pi_iff]
    intro b
    simpa [f2] using measurable_pi_apply (Sum.inr b)
  have h_map_f1 : (Measure.infinitePi P).map f1 = Measure.infinitePi (fun _ : α => μ) := by
    have h_inj : Function.Injective (Sum.inl : α → α ⊕ β) := by
      exact fun a b h => by injection h
    have := Measure.map_infinitePi_infinitePi_of_inj (P := P) h_inj
    have h_eq : (fun ω i => ω (Sum.inl i)) = f1 := by
      ext ω a; simp [f1]
    simpa [h_eq, P] using this
  have h_map_f2 : (Measure.infinitePi P).map f2 = Measure.infinitePi (fun _ : β => μ) := by
    have h_inj : Function.Injective (Sum.inr : β → α ⊕ β) := by
      exact fun a b h => by injection h
    have := Measure.map_infinitePi_infinitePi_of_inj (P := P) h_inj
    have h_eq : (fun ω i => ω (Sum.inr i)) = f2 := by
      ext ω b; simp [f2]
    simpa [h_eq, P] using this
  let m : (α ⊕ β) → MeasurableSpace ((α ⊕ β → X)) := fun k =>
    MeasurableSpace.comap (fun ω : (α ⊕ β → X) => ω k) (by infer_instance : MeasurableSpace X)
  have h_le : ∀ i, m i ≤ (inferInstance : MeasurableSpace ((α ⊕ β → X))) := by
    intro i
    have hmeas : Measurable (fun ω : (α ⊕ β → X) => ω i) := measurable_pi_apply i
    exact hmeas.comap_le
  have h_indep_fun : iIndepFun (fun (i : α ⊕ β) (ω : (α ⊕ β → X)) => ω i) (Measure.infinitePi P) := by
    refine iIndepFun_infinitePi (X := fun i => id) (by
      intro i
      exact measurable_id)
  have h_indep : iIndep m (Measure.infinitePi P) := by
    rwa [iIndepFun_iff_iIndep] at h_indep_fun
  let S : Set (α ⊕ β) := Set.range Sum.inl
  let T : Set (α ⊕ β) := Set.range Sum.inr
  have hST : Disjoint S T := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext x
    constructor
    · intro h
      rcases h with ⟨hxS, hxT⟩
      rcases hxS with ⟨a, ha⟩
      rcases hxT with ⟨b, hb⟩
      have := congrArg id (ha.trans hb.symm)
      injection this
    · intro h
      exact h.elim
  have h_indep_sup : Indep (⨆ i ∈ S, m i) (⨆ i ∈ T, m i) (Measure.infinitePi P) :=
    indep_iSup_of_disjoint h_le h_indep hST
  -- relate the comap sigma-algebras to the suprema
  have h_comap_f1 : MeasurableSpace.comap f1 (inferInstance : MeasurableSpace (α → X)) = ⨆ i ∈ S, m i := by
    calc
      MeasurableSpace.comap f1 (inferInstance : MeasurableSpace (α → X))
          = MeasurableSpace.comap f1 (⨆ a, (by infer_instance : MeasurableSpace X).comap (fun (f : α → X) => f a)) := by rfl
      _ = ⨆ a, MeasurableSpace.comap f1 ((by infer_instance : MeasurableSpace X).comap (fun (f : α → X) => f a)) := by rw [MeasurableSpace.comap_iSup]
      _ = ⨆ a, (by infer_instance : MeasurableSpace X).comap ((fun (f : α → X) => f a) ∘ f1) := by simp_rw [MeasurableSpace.comap_comp]
      _ = ⨆ a, (by infer_instance : MeasurableSpace X).comap (fun ω => f1 ω a) := by rfl
      _ = ⨆ a, (by infer_instance : MeasurableSpace X).comap (fun ω => ω (Sum.inl a)) := by simp [f1]
      _ = ⨆ a, m (Sum.inl a) := by simp [m]
      _ = ⨆ i ∈ S, m i := by rw [iSup_range]
  have h_comap_f2 : MeasurableSpace.comap f2 (inferInstance : MeasurableSpace (β → X)) = ⨆ i ∈ T, m i := by
    calc
      MeasurableSpace.comap f2 (inferInstance : MeasurableSpace (β → X))
          = MeasurableSpace.comap f2 (⨆ b, (by infer_instance : MeasurableSpace X).comap (fun (f : β → X) => f b)) := by rfl
      _ = ⨆ b, MeasurableSpace.comap f2 ((by infer_instance : MeasurableSpace X).comap (fun (f : β → X) => f b)) := by rw [MeasurableSpace.comap_iSup]
      _ = ⨆ b, (by infer_instance : MeasurableSpace X).comap ((fun (f : β → X) => f b) ∘ f2) := by simp_rw [MeasurableSpace.comap_comp]
      _ = ⨆ b, (by infer_instance : MeasurableSpace X).comap (fun ω => f2 ω b) := by rfl
      _ = ⨆ b, (by infer_instance : MeasurableSpace X).comap (fun ω => ω (Sum.inr b)) := by simp [f2]
      _ = ⨆ b, m (Sum.inr b) := by simp [m]
      _ = ⨆ i ∈ T, m i := by rw [iSup_range]
  have h_indep_fun_f1_f2 : IndepFun f1 f2 (Measure.infinitePi P) := by
    unfold IndepFun Kernel.IndepFun
    rw [h_comap_f1, h_comap_f2]
    exact h_indep_sup
  have h_eq := IndepFun.map_prod_eq_prod_map_map hf1_meas.aemeasurable hf2_meas.aemeasurable h_indep_fun_f1_f2
  -- h_eq : (Measure.infinitePi P).map (fun ω => (f1 ω, f2 ω)) = ((Measure.infinitePi P).map f1).prod ((Measure.infinitePi P).map f2)
  -- We need to relate (fun ω => (f1 ω, f2 ω)) to the original map
  -- They are definitionally equal after unfolding f1 and f2
  have h_goal := h_eq
  -- unfold f1 and f2 in h_goal
  unfold f1 f2 at h_goal
  -- Now h_goal: (Measure.infinitePi P).map (fun ω => (ω ∘ Sum.inl, ω ∘ Sum.inr)) = ((Measure.infinitePi P).map (fun x => x ∘ Sum.inl)).prod ((Measure.infinitePi P).map (fun x => x ∘ Sum.inr))
  -- But the goal is: (Measure.infinitePi P).map (fun x => (fun a => x (Sum.inl a), fun b => x (Sum.inr b))) = ...
  -- These are definitionally equal
  -- Let's check:
  -- (fun ω => (ω ∘ Sum.inl, ω ∘ Sum.inr)) = (fun x => (x ∘ Sum.inl, x ∘ Sum.inr)) = (fun x => (fun a => x (Sum.inl a), fun b => x (Sum.inr b)))
  -- So they are the same
  rw [h_map_f1, h_map_f2] at h_goal
  -- Now h_goal: (Measure.infinitePi P).map (fun ω => (ω ∘ Sum.inl, ω ∘ Sum.inr)) = (Measure.infinitePi (fun _ : α => μ)).prod (Measure.infinitePi (fun _ : β => μ))
  -- The goal: (Measure.infinitePi P).map (fun x => (fun a => x (Sum.inl a), fun b => x (Sum.inr b))) = (Measure.infinitePi (fun _ : α => μ)).prod (Measure.infinitePi (fun _ : β => μ))
  -- The only difference is the lambda, which we proved is definitionally equal
  -- So exact should work
  exact h_goal

theorem infinitePi_group {ι : Type*} [Countable ι] (d : ℕ) :
    (Measure.infinitePi fun _ : ι × Fin d => gaussianReal 0 1).map
        (fun x : ι × Fin d → ℝ => fun k => (WithLp.toLp 2 fun c => x (k, c) : EuclideanSpace ℝ (Fin d))) =
      Measure.infinitePi fun _ : ι => stdGaussian (EuclideanSpace ℝ (Fin d)) := by
  have h_meas_toLp : Measurable (WithLp.toLp (2 : ENNReal) : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) :=
    (PiLp.continuous_toLp (2 : ENNReal) (fun _ : Fin d => ℝ)).measurable
  have h_meas_curry : Measurable (MeasurableEquiv.curry ι (Fin d) ℝ) :=
    (MeasurableEquiv.curry ι (Fin d) ℝ).measurable
  have h_meas_g : Measurable (fun (g : ι → Fin d → ℝ) (k : ι) => WithLp.toLp (2 : ENNReal) (g k)) := by
    rw [measurable_pi_iff]
    intro k
    have : Measurable (fun (g : ι → Fin d → ℝ) => g k) := measurable_pi_apply k
    exact h_meas_toLp.comp this
  have h_map_eq : (fun (x : ι × Fin d → ℝ) (k : ι) => (WithLp.toLp 2 fun c => x (k, c) : EuclideanSpace ℝ (Fin d))) =
      (fun (g : ι → Fin d → ℝ) (k : ι) => WithLp.toLp (2 : ENNReal) (g k)) ∘ (MeasurableEquiv.curry ι (Fin d) ℝ) := by
    ext x k; simp [MeasurableEquiv.curry]
  rw [h_map_eq]
  rw [← Measure.map_map h_meas_g h_meas_curry]
  have h_curry_eq : Measure.map (MeasurableEquiv.curry ι (Fin d) ℝ)
      (Measure.infinitePi fun _ : ι × Fin d => gaussianReal 0 1) =
      Measure.infinitePi fun _ : ι => Measure.infinitePi fun _ : Fin d => gaussianReal 0 1 := by
    rw [Measure.infinitePi_map_curry (μ := fun (_ : ι) (_ : Fin d) => gaussianReal 0 1)]
  rw [h_curry_eq]
  rw [Measure.infinitePi_map_pi (μ := fun _ : ι => Measure.infinitePi fun _ : Fin d => gaussianReal 0 1)
    (hf := fun _ => h_meas_toLp)]
  simp [Measure.infinitePi_eq_pi, map_pi_eq_stdGaussian]

/-! ## The law -/

variable (d : ℕ)

/-- The coordinates of one repeat: descent `(k, c)` and test `((v, k), c)`. -/
abbrev PgCoord : Type := (ℕ × Fin d) ⊕ ((ℕ × ℕ) × Fin d)

/-- The vectors of one repeat read off its coordinates. -/
def pgRoundOf (y : PgCoord d → ℝ) : PgRound d :=
  (fun k => WithLp.toLp 2 fun c => y (Sum.inl (k, c)), fun v k => WithLp.toLp 2 fun c => y (Sum.inr ((v, k), c)))

theorem measurable_pgRoundOf : Measurable (pgRoundOf d) := by
  unfold pgRoundOf
  refine Measurable.prodMk (measurable_pi_iff.mpr fun k => ?_)
    (measurable_pi_iff.mpr fun v => measurable_pi_iff.mpr fun k => ?_)
  · exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.mpr fun c => measurable_pi_apply _)
  · exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.mpr fun c => measurable_pi_apply _)

theorem pgRound_law :
    (Measure.infinitePi fun _ : PgCoord d => gaussianReal 0 1).map (pgRoundOf d) = pgRoundMeasure d := by
  have hsplit : Measurable fun y : PgCoord d → ℝ => (fun a => y (Sum.inl a), fun b => y (Sum.inr b)) :=
    Measurable.prodMk (measurable_pi_iff.mpr fun a => measurable_pi_apply _)
      (measurable_pi_iff.mpr fun b => measurable_pi_apply _)
  have hG1 : Measurable fun x : ℕ × Fin d → ℝ => fun k => (WithLp.toLp 2 fun c => x (k, c) : E d) :=
    measurable_pi_iff.mpr fun k =>
      (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.mpr fun c => measurable_pi_apply _)
  have hG2' : Measurable fun x : (ℕ × ℕ) × Fin d → ℝ => fun p => (WithLp.toLp 2 fun c => x (p, c) : E d) :=
    measurable_pi_iff.mpr fun p =>
      (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.mpr fun c => measurable_pi_apply _)
  have hcur : Measurable (MeasurableEquiv.curry ℕ ℕ (E d)) := (MeasurableEquiv.curry ℕ ℕ (E d)).measurable
  have hG2 : Measurable fun x : (ℕ × ℕ) × Fin d → ℝ => fun v k => (WithLp.toLp 2 fun c => x ((v, k), c) : E d) :=
    hcur.comp hG2'
  have hfac : pgRoundOf d = Prod.map (fun x : ℕ × Fin d → ℝ => fun k => (WithLp.toLp 2 fun c => x (k, c) : E d))
      (fun x : (ℕ × ℕ) × Fin d → ℝ => fun v k => (WithLp.toLp 2 fun c => x ((v, k), c) : E d)) ∘
        fun y : PgCoord d → ℝ => (fun a => y (Sum.inl a), fun b => y (Sum.inr b)) := rfl
  have hG2law : (Measure.infinitePi fun _ : (ℕ × ℕ) × Fin d => gaussianReal 0 1).map
      (fun x : (ℕ × ℕ) × Fin d → ℝ => fun v k => (WithLp.toLp 2 fun c => x ((v, k), c) : E d)) =
      Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => stdGaussian (E d) := by
    have : (fun x : (ℕ × ℕ) × Fin d → ℝ => fun v k => (WithLp.toLp 2 fun c => x ((v, k), c) : E d)) =
        (MeasurableEquiv.curry ℕ ℕ (E d)) ∘ fun x : (ℕ × ℕ) × Fin d → ℝ => fun p => (WithLp.toLp 2 fun c => x (p, c) : E d) :=
      rfl
    rw [this, ← Measure.map_map hcur hG2', infinitePi_group]
    exact Measure.infinitePi_map_curry (fun _ _ => stdGaussian (E d))
  rw [hfac, ← Measure.map_map (hG1.prodMap hG2) hsplit, infinitePi_sum_prod, ← Measure.map_prod_map _ _ hG1 hG2,
    infinitePi_group, hG2law]
  rfl

/-- The coordinates of the stream of PG: stage, repeat, coordinate of the repeat. -/
abbrev PgIdx : Type := ℕ × ℕ × PgCoord d

/-- The stream of PG read off its coordinates. -/
def pgStreamOf (x : PgIdx d → ℝ) : ℕ → ℕ → PgRound d := fun i r => pgRoundOf d fun s => x (i, r, s)

theorem pgStream_law :
    (Measure.infinitePi fun _ : PgIdx d => gaussianReal 0 1).map (pgStreamOf d) = pgMeasure d := by
  have hc1 : Measurable (MeasurableEquiv.curry ℕ (ℕ × PgCoord d) ℝ) := (MeasurableEquiv.curry _ _ _).measurable
  have hc2 : Measurable fun y : ℕ → ℕ × PgCoord d → ℝ => fun i => MeasurableEquiv.curry ℕ (PgCoord d) ℝ (y i) :=
    measurable_pi_iff.mpr fun i => (MeasurableEquiv.curry _ _ _).measurable.comp (measurable_pi_apply i)
  have hR : Measurable fun z : ℕ → ℕ → PgCoord d → ℝ => fun i r => pgRoundOf d (z i r) :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun r =>
      (measurable_pgRoundOf d).comp ((measurable_pi_apply r).comp (measurable_pi_apply i))
  have hfac : pgStreamOf d = (fun z : ℕ → ℕ → PgCoord d → ℝ => fun i r => pgRoundOf d (z i r)) ∘
      (fun y : ℕ → ℕ × PgCoord d → ℝ => fun i => MeasurableEquiv.curry ℕ (PgCoord d) ℝ (y i)) ∘
        MeasurableEquiv.curry ℕ (ℕ × PgCoord d) ℝ := rfl
  rw [hfac, ← Measure.map_map hR (hc2.comp hc1), ← Measure.map_map hc2 hc1,
    Measure.infinitePi_map_curry (fun _ _ => gaussianReal 0 1)]
  rw [Measure.infinitePi_map_pi _ (fun i => (MeasurableEquiv.curry ℕ (PgCoord d) ℝ).measurable)]
  simp_rw [Measure.infinitePi_map_curry (fun (_ : ℕ) (_ : PgCoord d) => gaussianReal 0 1)]
  have hin : (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : PgCoord d => gaussianReal 0 1).map
      (fun (zi : ℕ → PgCoord d → ℝ) (r : ℕ) => pgRoundOf d (zi r)) = pgCoreMeasure d := by
    rw [Measure.infinitePi_map_pi _ (f := fun (_ : ℕ) => pgRoundOf d) (fun _ => measurable_pgRoundOf d), pgRound_law]
    rfl
  rw [Measure.infinitePi_map_pi _ (f := fun (_ : ℕ) (zi : ℕ → PgCoord d → ℝ) (r : ℕ) => pgRoundOf d (zi r))
    (fun _ => measurable_pi_iff.mpr fun r => (measurable_pgRoundOf d).comp (measurable_pi_apply r))]
  simp_rw [hin]
  rfl

/-- The index of the stream read at a coordinate of the stream of PG. -/
noncomputable def pgIdxOf (n : ℕ) (r0 R0 δ1 : ℝ) : PgIdx d → ℕ
  | (i, r, Sum.inl (k, c)) => df2oIdxA d n r0 R0 δ1 i r k c
  | (i, r, Sum.inr ((v, k), c)) => df2oIdxT d n r0 R0 δ1 i r v k c

theorem idxA_eq (n : ℕ) (r0 R0 δ1 : ℝ) (i r k : ℕ) (c : Fin d) :
    df2oIdxA d n r0 R0 δ1 i r k c = mrA (pgStages r0 R0) (pgJr (df2oPgDelta r0 R0 δ1)) d (df2oSpare d n r0 R0 δ1)
      (fun i => pgNs d (pgRhoStage d i)) (df2oPgW d (df2oPgDelta r0 R0 δ1)) i r k c := rfl

theorem idxT_eq (n : ℕ) (r0 R0 δ1 : ℝ) (i r v k : ℕ) (c : Fin d) :
    df2oIdxT d n r0 R0 δ1 i r v k c = mrT (pgStages r0 R0) (pgJr (df2oPgDelta r0 R0 δ1)) (pgMT (df2oPgDelta r0 R0 δ1))
      d (df2oSpare d n r0 R0 δ1) (fun i => pgNs d (pgRhoStage d i)) (fun i => pgNT d (pgRhoStage d i))
      (df2oPgW d (df2oPgDelta r0 R0 δ1)) i r v k c := rfl

theorem pgIdxOf_injective (n : ℕ) (r0 R0 δ1 : ℝ) : Function.Injective (pgIdxOf d n r0 R0 δ1) := by
  have hW : ∀ i, df2oPgW d (df2oPgDelta r0 R0 δ1) i = pgNs d (pgRhoStage d i) +
      pgMT (df2oPgDelta r0 R0 δ1) * pgNT d (pgRhoStage d i) := fun _ => rfl
  have hS : mrOff (pgJr (df2oPgDelta r0 R0 δ1)) d (df2oPgW d (df2oPgDelta r0 R0 δ1)) (pgStages r0 R0) ≤
      df2oSpare d n r0 R0 δ1 := Nat.le_add_right _ _
  rintro ⟨i, r, (⟨k, c⟩ | ⟨⟨v, k⟩, c⟩)⟩ ⟨i', r', (⟨k', c'⟩ | ⟨⟨v', k'⟩, c'⟩)⟩ h
  · simp only [pgIdxOf, idxA_eq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := mrA_inj _ _ _ _ _ _ _ _ hW hS _ _ _ _ _ _ _ _ h
    rfl
  · simp only [pgIdxOf, idxA_eq, idxT_eq] at h
    exact absurd h (mrA_ne_mrT _ _ _ _ _ _ _ _ hW hS _ _ _ _ _ _ _ _ _)
  · simp only [pgIdxOf, idxA_eq, idxT_eq] at h
    exact absurd h.symm (mrA_ne_mrT _ _ _ _ _ _ _ _ hW hS _ _ _ _ _ _ _ _ _)
  · simp only [pgIdxOf, idxT_eq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := mrT_inj _ _ _ _ _ _ _ _ hW hS _ _ _ _ _ _ _ _ _ _ h
    rfl

/-- The law of the positioning block. -/
theorem df2oOmega_law (n : ℕ) (r0 R0 δ1 : ℝ) : gaussStream.map (df2oOmega d n r0 R0 δ1) = pgMeasure d := by
  have hfac : df2oOmega d n r0 R0 δ1 = pgStreamOf d ∘ fun gs : ℕ → ℝ => fun j => gs (pgIdxOf d n r0 R0 δ1 j) := rfl
  have hsel : Measurable fun gs : ℕ → ℝ => fun j => gs (pgIdxOf d n r0 R0 δ1 j) :=
    measurable_pi_iff.mpr fun j => measurable_pi_apply _
  have hst : Measurable (pgStreamOf d) :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun r =>
      (measurable_pgRoundOf d).comp (measurable_pi_iff.mpr fun s => measurable_pi_apply _)
  rw [hfac, ← Measure.map_map hst hsel, gaussStream, infinitePi_comp_inj _ _ (pgIdxOf_injective d n r0 R0 δ1),
    pgStream_law]

end Layer2

end AdversarialBco.Poly
