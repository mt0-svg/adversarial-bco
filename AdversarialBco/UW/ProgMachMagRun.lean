/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ProgMachMagDefs
public import AdversarialBco.UW.ProgLinkStep
public import AdversarialBco.Unified.MagRun

@[expose] public section

/-!
# The magnitudes of BL-OW's run

The BL-OW copy of Unified/MagStep.lean and Unified/MagRun.lean. BL-OW's round in mode `run` is BL-O's R7 to R15
(`tailY`, UW/ProgLinkStep.lean) at the weighted observation `Y'^w = rnd_p(φ' clip(Y', y0))` instead of `Y'`. With
`y0 ≥ 0`, `φ' ∈ [0, 1]` and `|clip(Y', y0)| ≤ |Y'|`, and `rnd_p` keeps a bound that is a power of two, so
`|Y'^w| ≤ T^14` as for `Y'` at the unit `T = 2^N` (`ywQ_abs`), and BL-O's bounds of one round (`commit_bnd`,
`init_bnd`) apply to `tailY` at any observation below `T^14` (`tailY_bnd`).

* `rnd_abs_pow`: `|x| ≤ 2^N` gives `|rnd_p x| ≤ 2^N`;
* `ywQ_abs`: `|Y| ≤ 2^N` gives `|ywQ p b0 y0 ξ Y| ≤ 2^N` for `y0 ≥ 0`;
* `tailY_bnd`: one round of R7 to R15 keeps the bounds `StI`;
* `modeOW_run0`, `run_bndOW`: BL-OW's state in every round in mode `run` is in `StI`.
-/

namespace AdversarialBco.UW.ProgW

open AdversarialBco AdversarialBco.Unified.BLO AdversarialBco.Unified.BudK
open AdversarialBco.Bit.BLP (Par St Mode init rnd)
open AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Unified.ProgO (cfgV InU wU)
open AdversarialBco.Unified.MagO (CfgBO Y_bndO apO_abs clip_abs)
open AdversarialBco.UW.BLOW (parOW cfgWW modeOW modeOW_succ b0OW y0OW ywQ readOW)
open AdversarialBco.BitRAMO (WorldO)
open Matrix

variable {d : ℕ}

/-- **`rnd_p` keeps a bound `2^N`**: `2^N` lies on the grid `2^{-p}`, and `rnd_p` is monotone. -/
theorem rnd_abs_pow (p N : ℕ) {x : ℚ} (hx : |x| ≤ 2 ^ N) : |rnd p x| ≤ 2 ^ N := by
  unfold rnd
  have hk : (0 : ℚ) < 2 ^ p := by positivity
  rw [abs_div, abs_of_pos hk, div_le_iff₀ hk]
  obtain ⟨h1, h2⟩ := abs_le.1 hx
  have hz : (((2 : ℤ) ^ (N + p) : ℤ) : ℚ) = 2 ^ N * 2 ^ p := by push_cast; ring
  have m2 := mul_le_mul_of_nonneg_right h2 hk.le
  have m1 := mul_le_mul_of_nonneg_right h1 hk.le
  have u : ⌊x * 2 ^ p + 1 / 2⌋ ≤ (2 : ℤ) ^ (N + p) := by
    rw [Int.floor_le_iff, hz]; linarith
  have l : -((2 : ℤ) ^ (N + p)) ≤ ⌊x * 2 ^ p + 1 / 2⌋ := by
    rw [Int.le_floor, Int.cast_neg, hz]; linarith
  have u' : ((⌊x * 2 ^ p + 1 / 2⌋ : ℤ) : ℚ) ≤ 2 ^ N * 2 ^ p := by rw [← hz]; exact_mod_cast u
  have l' : -(2 ^ N * 2 ^ p : ℚ) ≤ ((⌊x * 2 ^ p + 1 / 2⌋ : ℤ) : ℚ) := by
    rw [← hz]; exact_mod_cast l
  rw [abs_le]
  exact ⟨l', u'⟩

/-- **R5w keeps a bound `2^N`** for `y0 ≥ 0`. -/
theorem ywQ_abs (p N : ℕ) {b0 y0 : ℚ} (hy0 : 0 ≤ y0) (ξ : Fin d → ℚ) {Y : ℚ} (hY : |Y| ≤ 2 ^ N) :
    |ywQ p b0 y0 ξ Y| ≤ 2 ^ N := by
  unfold ywQ
  apply rnd_abs_pow
  have hφ0 : (0 : ℚ) ≤ min 1 (max 0 (b0 + 1 - ξ ⬝ᵥ ξ)) := le_min zero_le_one (le_max_left _ _)
  have hφ1 : min 1 (max 0 (b0 + 1 - ξ ⬝ᵥ ξ)) ≤ (1 : ℚ) := min_le_left _ _
  have hc : |max (-y0) (min y0 Y)| ≤ |Y| := by
    rw [abs_le]
    refine ⟨le_max_of_le_right (le_min (by linarith [abs_nonneg Y]) (neg_abs_le Y)),
      max_le (by linarith [abs_nonneg Y]) ((min_le_right _ _).trans (le_abs_self Y))⟩
  rw [abs_mul, abs_of_nonneg hφ0]
  calc min 1 (max 0 (b0 + 1 - ξ ⬝ᵥ ξ)) * |max (-y0) (min y0 Y)| ≤ 1 * |Y| :=
        mul_le_mul hφ1 hc (abs_nonneg _) zero_le_one
    _ ≤ 2 ^ N := by rw [one_mul]; exact hY

/-- **R7 to R15 keep the bounds** at any observation below `T^14`. -/
theorem tailY_bnd (orc : (Fin d → ℚ) → ℕ → Bool) {c : CfgO d} {T : ℚ} (hc : CfgBO T c) (n : ℕ) {st : St d}
    {t : ℕ} (hs : StI T c.par.Rint t st) (ξ : Fin d → ℚ) (hξ : ∀ i, |ξ i| ≤ T) {Y : ℚ} (hY : |Y| ≤ T ^ 14)
    {st' : St d} (h : tailY orc c n st ξ Y = .run st') : StI T c.par.Rint (t + 1) st' := by
  have hcb : CfgB T (cfgV c) := hc.cb
  have hs' : StI T (cfgV c).par.Rint t st := hs
  simp only [tailY] at h
  repeat' (first | split at h | split_ifs at h)
  all_goals (try (cases h))
  all_goals first
    | exact init_bnd (by linarith [hcb.T4]) (Nat.cast_nonneg _) _ hcb.A0 hcb.B0 _
    | exact commit_bnd hcb hs' ξ hξ _ (apO_abs orc c _ _ ‹_›) _ _ ‹_› _ hY

/-- **A mode `run` of BL-OW at round `t` comes from a mode `run` at round `0`.** -/
theorem modeOW_run0 (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (w : WorldO d) :
    ∀ t (st : St d), modeOW d n δ r0 R0 a w t = .run st → ∃ st0, modeOW d n δ r0 R0 a w 0 = .run st0
  | 0, st, h => ⟨st, h⟩
  | t + 1, st, h => by
    rw [modeOW_succ] at h
    rcases hm : modeOW d n δ r0 R0 a w t with _ | _ | st1
    · rw [hm, stepOW_og _ _ _ _ _ (Or.inl rfl)] at h; cases h
    · rw [hm, stepOW_og _ _ _ _ _ (Or.inr rfl)] at h; cases h
    · exact modeOW_run0 n δ r0 R0 a w t st1 hm

/-- **The bounds in every round of BL-OW in mode `run`**, at a unit `T = 2^N`. -/
theorem run_bndOW (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (w : WorldO d) {N : ℕ}
    (hc : CfgBO (2 ^ N) (cfgWW d n δ r0 R0 a w)) (hB : ((parO d n δ).B : ℚ) ≤ 2 ^ N) (hB8 : 8 ≤ (parO d n δ).B)
    (hy0 : 0 ≤ y0OW d n δ) :
    ∀ t (st : St d), modeOW d n δ r0 R0 a w t = .run st → StI (2 ^ N) (parO d n δ).Rint t st
  | 0, st, h => by
    have h0 : mode0O w.orc (cfgWW d n δ r0 R0 a w) = .run st := h
    obtain ⟨-, e⟩ := Unified.MagO.mode0O_run h0
    subst e
    exact init_bnd (by positivity) (Nat.cast_nonneg _) _ hc.cb.A0 hc.cb.B0 _
  | t + 1, st, h => by
    have hξ := draw_abs (d := d) w.cs (K0O d n δ r0 R0) (parO d n δ).B t hB8
    rw [modeOW_succ] at h
    rcases hm : modeOW d n δ r0 R0 a w t with _ | _ | st1
    · rw [hm, stepOW_og _ _ _ _ _ (Or.inl rfl)] at h; cases h
    · rw [hm, stepOW_og _ _ _ _ _ (Or.inr rfl)] at h; cases h
    rw [hm, stepOW_tailY] at h
    have hs := run_bndOW n δ r0 R0 a w hc hB hB8 hy0 t st1 hm
    have hξ' : ∀ i, |(drawO d n δ r0 R0 w.cs t).1 i| ≤ 2 ^ N := fun i => (hξ.1 i).trans hB
    have hY := Y_bndO w.orc hc hs _ _ (readOW d n δ r0 R0 a w t) hξ' (hξ.2.trans hB)
      (by exact_mod_cast clip_abs _ _)
    refine tailY_bnd w.orc hc n hs _ hξ' ?_ h
    rw [← pow_mul] at hY ⊢
    exact ywQ_abs _ _ hy0 _ hY

end AdversarialBco.UW.ProgW
