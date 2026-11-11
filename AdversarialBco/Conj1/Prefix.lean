/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2WorldLay

@[expose] public section

/-!
# The sigma-field of a run before round `t`

On the world `WΩ = (gs, noise)`, `prefixσ N0 S n d t` holds the terms of the Gaussian stream that a run of DF2-O reads
before round `t`, and the noise before round `t`: every term below the block of round `min t n` (`N0` is the first
term of the rounds), and every term of the spare region from `S` on except the fresh terms `S + pair 0 (pair 0 (d + m))`
that the instances of the world read past the horizon (`lay`, Df2WorldLay.lean). A loss chosen by a strategy at round
`t` reads the run before round `t`, hence is `prefixσ … t`-measurable; this module gives what the world layer of A2
needs from that:

* `prefixσ_le_𝒢w`: `prefixσ N0 S n d (a + s) ≤ 𝒢w N0 S n d a s` when `N0 + n (d + 1) ≤ S`: the run before round
  `a + s` is known before round `s` of the instance started at `a` (`prefixIdx_not_fut`);
* the reads of PG (`mrA_mem_prefixIdx`, `mrT_mem_prefixIdx`, for every `t`), the draws of the rounds `u < min t n`
  (`xi_meas_prefixSeq`, `zeta_meas_prefixSeq`) and the noise before `t` (`meas_noise_prefixSeq`) are
  `prefixσ … t`-measurable.
-/

open MeasureTheory ProbabilityTheory

namespace AdversarialBco.Poly.Conj1

open AdversarialBco.RealRAM Layer2

/-- The indices of the Gaussian stream that the run reads before round `t` (`N0` the first term of the rounds, `S`
the spare index, `n` the horizon): every term below the block of round `min t n`, and every term of the spare region
except those that the instances of the world read past the horizon (`lay`). -/
def prefixIdx (N0 S n d t : ℕ) : Set ℕ :=
  {i | i < N0 + min t n * (d + 1)} ∪ {i | S ≤ i ∧ ∀ m, i ≠ S + Nat.pair 0 (Nat.pair 0 (d + m))}

/-- The sigma-field of the run before round `t`: the terms of the Gaussian stream in `prefixIdx`, and the noise of
the rounds before `t`. -/
abbrev prefixSeq (N0 S n d t : ℕ) : MeasurableSpace WΩ :=
  (⨆ i ∈ prefixIdx N0 S n d t, gσ i) ⊔ MeasurableSpace.comap Prod.snd (pastNoise t)

theorem prefixSeq_mono (N0 S n d : ℕ) {s t : ℕ} (h : s ≤ t) : prefixSeq N0 S n d s ≤ prefixSeq N0 S n d t := by
  unfold prefixSeq
  apply sup_le_sup
  · -- iSup part: prefixIdx N0 S n d s ⊆ prefixIdx N0 S n d t
    apply iSup₂_le
    intro i hi
    apply le_iSup₂ (f := fun i (_ : i ∈ prefixIdx N0 S n d t) => gσ i) i
    -- need to show i ∈ prefixIdx N0 S n d t
    rcases hi with (hi | hi)
    · -- i < N0 + min s n * (d + 1)
      left
      have hmin : min s n ≤ min t n := min_le_min h (le_refl n)
      have hle : N0 + min s n * (d + 1) ≤ N0 + min t n * (d + 1) := by
        nlinarith
      exact lt_of_lt_of_le hi hle
    · -- S ≤ i ∧ ∀ m, i ≠ S + Nat.pair 0 (Nat.pair 0 (d + m))
      right
      exact hi
  · -- pastNoise part
    apply MeasurableSpace.comap_mono
    exact pastNoise_mono h

theorem prefixSeq_le (N0 S n d t : ℕ) : prefixSeq N0 S n d t ≤ (inferInstance : MeasurableSpace WΩ) := by
  unfold prefixSeq
  apply sup_le
  · apply iSup₂_le; intro i hi; exact gσ_le i
  · exact (MeasurableSpace.comap_mono (pastNoise_le t)).trans measurable_snd.comap_le

theorem gσ_le_prefixSeq (N0 S n d t i : ℕ) (hi : i ∈ prefixIdx N0 S n d t) : gσ i ≤ prefixSeq N0 S n d t := by
  exact (le_iSup₂ (f := fun i (_ : i ∈ prefixIdx N0 S n d t) => gσ i) i hi).trans le_sup_left

theorem meas_noise_prefixSeq (N0 S n d t j : ℕ) (hj : j < t) :
    Measurable[prefixSeq N0 S n d t] fun ω : WΩ => ω.2 j := by
  have h := meas_noise t j hj
  exact h.mono le_sup_right (le_refl _)

/-- The filtration of the run: the sigma-fields `prefixSeq` before the rounds `t`. -/
def prefixσ (N0 S n d : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace WΩ) where
  seq := prefixSeq N0 S n d
  mono' _ _ h := prefixSeq_mono N0 S n d h
  le' := prefixSeq_le N0 S n d

/-! ## The run before round `a + s` is known before round `s` of the instance started at `a` -/

theorem prefixIdx_not_fut (N0 S n d a s i : ℕ) (hS : N0 + n * (d + 1) ≤ S) (hi : i ∈ prefixIdx N0 S n d (a + s)) :
    i ∉ fut N0 S n d a s := by
  intro hfut
  rcases hfut with ⟨s', hs', c, h_eq⟩
  rw [← h_eq] at hi
  unfold lay at hi
  split_ifs at hi with h
  · -- Case 1: a + s' < n, so hi says: N0 + (a + s') * (d + 1) + c ∈ prefixIdx N0 S n d (a + s)
    have h_le : N0 + (a + s) * (d + 1) ≤ N0 + (a + s') * (d + 1) + (c : ℕ) := by
      have hss' : a + s ≤ a + s' := Nat.add_le_add_left hs' a
      have h_mul : (a + s) * (d + 1) ≤ (a + s') * (d + 1) := Nat.mul_le_mul_right (d + 1) hss'
      omega
    have h_lt_S : N0 + (a + s') * (d + 1) + (c : ℕ) < S := by
      have hc : (c : ℕ) < d + 1 := c.2
      have h1 : N0 + (a + s') * (d + 1) + (c : ℕ) < N0 + ((a + s') * (d + 1) + (d + 1)) := by
        omega
      have h2 : N0 + ((a + s') * (d + 1) + (d + 1)) = N0 + (a + s' + 1) * (d + 1) := by ring
      rw [h2] at h1
      have h_bound : (a + s' + 1) * (d + 1) ≤ n * (d + 1) :=
        Nat.mul_le_mul_right (d + 1) (by omega)
      have h3 : N0 + (a + s' + 1) * (d + 1) ≤ N0 + n * (d + 1) :=
        Nat.add_le_add_left h_bound N0
      have h4 : N0 + n * (d + 1) ≤ S := hS
      omega
    rcases hi with (hi | hi)
    · -- hi: i < N0 + min (a + s) n * (d + 1)
      simp at hi
      have h_min : min (a + s) n ≤ a + s := Nat.min_le_left _ _
      have h_le' : N0 + min (a + s) n * (d + 1) ≤ N0 + (a + s) * (d + 1) := by
        have : min (a + s) n * (d + 1) ≤ (a + s) * (d + 1) :=
          Nat.mul_le_mul_right (d + 1) h_min
        omega
      omega
    · -- hi: S ≤ i ∧ ∀ m, i ≠ S + Nat.pair 0 (Nat.pair 0 (d + m))
      rcases hi with ⟨hSi, _⟩
      omega
  · -- Case 2: n ≤ a + s', so hi says: S + Nat.pair 0 (Nat.pair 0 (d + (s' * (d + 1) + c))) ∈ prefixIdx N0 S n d (a + s)
    rcases hi with (hi | hi)
    · -- hi: i < N0 + min (a + s) n * (d + 1)
      simp at hi
      have h_min : min (a + s) n ≤ n := Nat.min_le_right _ _
      have h_le' : N0 + min (a + s) n * (d + 1) ≤ N0 + n * (d + 1) := by
        have : min (a + s) n * (d + 1) ≤ n * (d + 1) :=
          Nat.mul_le_mul_right (d + 1) h_min
        omega
      have h_le_S : N0 + n * (d + 1) ≤ S := hS
      omega
    · -- hi: S ≤ i ∧ ∀ m, i ≠ S + Nat.pair 0 (Nat.pair 0 (d + m))
      rcases hi with ⟨_, h_ne⟩
      set m := s' * (d + 1) + (c : ℕ) with hm
      apply h_ne m
      simp [hm]

theorem prefixSeq_le_𝒢w (N0 S n d a s : ℕ) (hS : N0 + n * (d + 1) ≤ S) :
    prefixSeq N0 S n d (a + s) ≤ 𝒢w N0 S n d a s := by
  unfold prefixSeq
  have h𝒢w : (𝒢w N0 S n d a : ℕ → MeasurableSpace WΩ) s = (⨆ i ∈ (fut N0 S n d a s)ᶜ, gσ i) ⊔ MeasurableSpace.comap Prod.snd (pastNoise (a + s)) := rfl
  rw [h𝒢w]
  apply sup_le_sup
  · apply iSup₂_le
    intro i hi
    apply le_iSup₂ (f := fun i (_ : i ∈ (fut N0 S n d a s)ᶜ) => gσ i) i
    exact prefixIdx_not_fut N0 S n d a s i hS hi
  · rfl

theorem prefixσ_le_𝒢w (N0 S n d a s : ℕ) (hS : N0 + n * (d + 1) ≤ S) :
    prefixσ N0 S n d (a + s) ≤ 𝒢w N0 S n d a s :=
  prefixSeq_le_𝒢w N0 S n d a s hS

/-! ## What the run reads before round `t` -/

theorem mrA_mem_prefixIdx (m Jr d S n t : ℕ) (Ns NT W : ℕ → ℕ) (MT : ℕ) (hW : ∀ i, W i = Ns i + MT * NT i)
    (i r k : ℕ) (c : Fin d) :
    mrA m Jr d S Ns W i r k c ∈ prefixIdx (mrOff Jr d W m) S n d t := by
  unfold mrA
  split_ifs with h
  · rcases h with ⟨hi, hr, hk⟩
    have hkW : k < W i := by
      rw [hW i]
      omega
    have hslot : (r * W i + k) * d + (c : ℕ) < Jr * W i * d :=
      mr_slot_lt Jr (W i) d r k (c : ℕ) hr hkW c.isLt
    have hoff : mrOff Jr d W i + (r * W i + k) * d + (c : ℕ) < mrOff Jr d W m := by
      simpa [Nat.add_assoc] using mrOff_add_lt Jr d m i ((r * W i + k) * d + (c : ℕ)) W hi hslot
    left
    exact hoff.trans_le (Nat.le_add_right _ _)
  · right
    constructor
    · omega
    · intro m' h_eq
      have h_pair_eq : Nat.pair (Nat.pair i r) (Nat.pair (2 * k) (c : ℕ)) = Nat.pair 0 (Nat.pair 0 (d + m')) := by
        omega
      rcases (Nat.pair_eq_pair.mp h_pair_eq) with ⟨h_pair1, h_pair2⟩
      have h0 : (0 : ℕ) = Nat.pair 0 0 := rfl
      have h_pair1' : Nat.pair i r = Nat.pair 0 0 := by rw [← h0]; exact h_pair1
      rcases (Nat.pair_eq_pair.mp h_pair1') with ⟨hi0, hr0⟩
      rcases (Nat.pair_eq_pair.mp h_pair2) with ⟨h2k0, hc_eq⟩
      omega

theorem mrT_mem_prefixIdx (m Jr MT d S n t : ℕ) (Ns NT W : ℕ → ℕ) (hW : ∀ i, W i = Ns i + MT * NT i)
    (i r v k : ℕ) (c : Fin d) :
    mrT m Jr MT d S Ns NT W i r v k c ∈ prefixIdx (mrOff Jr d W m) S n d t := by
  unfold mrT
  split
  · rename_i h
    rcases h with ⟨hi, hr, hv, hk⟩
    have hW_i : W i = Ns i + MT * NT i := hW i
    have h_lt : Ns i + v * NT i + k < W i := by
      rw [hW_i]
      have hNT_pos : 0 < NT i := by omega
      have hv_mul : v * NT i < MT * NT i := Nat.mul_lt_mul_of_pos_right hv hNT_pos
      nlinarith
    set x := (r * W i + Ns i + v * NT i + k) * d + (c : ℕ) with hx
    have h_slot : x < Jr * W i * d := by
      rw [hx]
      simpa [add_assoc] using mr_slot_lt Jr (W i) d r (Ns i + v * NT i + k) (c : ℕ) hr h_lt (Fin.prop c)
    have h_mrOff : mrOff Jr d W i + x < mrOff Jr d W m :=
      mrOff_add_lt Jr d m i x W hi h_slot
    refine Or.inl ?_
    simpa [hx, add_assoc] using lt_of_lt_of_le h_mrOff (Nat.le_add_right _ _)
  · rename_i h
    apply Or.inr
    constructor
    · omega
    · intro m' h_eq
      have h_pair_eq : Nat.pair (Nat.pair i r) (Nat.pair (2 * Nat.pair v k + 1) (c : ℕ)) = Nat.pair 0 (Nat.pair 0 (d + m')) := by
        omega
      rcases (Nat.pair_eq_pair.mp h_pair_eq) with ⟨h_left, h_right⟩
      rcases (Nat.pair_eq_pair.mp h_right) with ⟨h_odd, h_c⟩
      omega

theorem xi_meas_prefixSeq (N0 S n d t u : ℕ) (hut : u < t) (hun : u < n) :
    Measurable[prefixSeq N0 S n d t] fun ω : WΩ => df2oXi (d := d) N0 ω.1 u := by
  refine measurable_pi_of fun c => ?_
  have hmem : N0 + u * (d + 1) + (c : ℕ) ∈ prefixIdx N0 S n d t := by
    have hu_min : u < min t n := by
      rw [Nat.lt_min]
      exact ⟨hut, hun⟩
    have h_bound : N0 + u * (d + 1) + (c : ℕ) < N0 + min t n * (d + 1) := by
      have : u * (d + 1) + (c : ℕ) < (u + 1) * (d + 1) := by
        have hc : (c : ℕ) < d + 1 := by
          have := c.2
          omega
        nlinarith
      have h_next : (u + 1) * (d + 1) ≤ min t n * (d + 1) := by
        have h_le : u + 1 ≤ min t n := by omega
        exact Nat.mul_le_mul_right (d + 1) h_le
      omega
    refine Or.inl h_bound
  exact meas_coord (N0 + u * (d + 1) + (c : ℕ)) (gσ_le_prefixSeq N0 S n d t (N0 + u * (d + 1) + (c : ℕ)) hmem)

theorem zeta_meas_prefixSeq (N0 S n d t u : ℕ) (hut : u < t) (hun : u < n) :
    Measurable[prefixSeq N0 S n d t] fun ω : WΩ => df2oZeta d N0 ω.1 u := by
  have hmin : u < min t n := (Nat.lt_min.mpr ⟨hut, hun⟩)
  have h_succ : u + 1 ≤ min t n := Nat.succ_le_of_lt hmin
  have h_lt : N0 + u * (d + 1) + d < N0 + min t n * (d + 1) := by
    have h1 : u * (d + 1) + d < (u + 1) * (d + 1) := by
      calc
        u * (d + 1) + d < u * (d + 1) + (d + 1) := by omega
        _ = (u + 1) * (d + 1) := by rw [Nat.succ_mul]
    have h2 : (u + 1) * (d + 1) ≤ (min t n) * (d + 1) :=
      Nat.mul_le_mul_right (d + 1) h_succ
    omega
  have hmem : N0 + u * (d + 1) + d ∈ prefixIdx N0 S n d t := Or.inl h_lt
  have hmeas : Measurable[prefixSeq N0 S n d t] fun ω : WΩ => ω.1 (N0 + u * (d + 1) + d) :=
    meas_coord (N0 + u * (d + 1) + d) (gσ_le_prefixSeq N0 S n d t (N0 + u * (d + 1) + d) hmem)
  simpa [df2oZeta] using hmeas.div_const 2

end AdversarialBco.Poly.Conj1
