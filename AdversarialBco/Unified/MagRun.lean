/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.MagStep

@[expose] public section

/-!
# The magnitudes of BL-O's run, part C: the run and `magBLO`

The bounds of BL-O's run `trajO`. A mode `run` at round `t` comes from a mode `run` at round `0` (`modeO_run0`), so
`ε' ≤ 1/2` (`mode0O_run`) and the configuration is bounded at `T = 2^K`, `K = pF + 8` (`fld_unit`, `qO_le`). By
induction over the rounds (`run_bndO`, with `step_bndO`, the draws at most `B ≤ T` by `draw_abs`, the reading
clipped), BL-O's state in round `t ≤ n` has `A', B'` entries at most `T`, `μ'` in the box of radius `R_int` and the
sums at most `t T^30`; their numerators on the grid `2^{-p}` are at most `T^33 = 2^{33K}`, and `33 K ≤ 20000 W`
(`Ku_le`). No bound on the position is used: the reading is clipped and the rowless configuration has no kept row.
-/

namespace AdversarialBco.Unified.MagO

open AdversarialBco AdversarialBco.Unified.BLO AdversarialBco.Unified.BudK
open AdversarialBco.Bit.BLP (Par St Mode init rnd)
open AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Unified.ProgO (cfgV InU wU MagBLO)
open AdversarialBco.BitRAMO (WorldO)

variable {d : ℕ}

/-- **A mode `run` at round `t` comes from a mode `run` at round `0`.** -/
theorem modeO_run0 (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (w : WorldO d) :
    ∀ t (st : St d), modeO d n δ r0 R0 a w t = .run st → ∃ st0, modeO d n δ r0 R0 a w 0 = .run st0
  | 0, st, h => ⟨st, h⟩
  | t + 1, st, h => by
    unfold modeO at h
    simp only [trajO] at h
    rcases hm : (trajO d n δ r0 R0 a w t).1 with _ | _ | st1
    · rw [hm] at h; cases h
    · rw [hm] at h; cases h
    · exact modeO_run0 n δ r0 R0 a w t st1 hm

/-- The first mode `run`: `ε' ≤ 1/2` and BL's initial state. -/
theorem mode0O_run {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d} {st : St d} (h : mode0O orc c = .run st) :
    c.par.eps ≤ 1 / 2 ∧ st = init c.par d := by
  unfold mode0O at h
  by_cases h1 : 1 / 2 < c.par.eps
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : crossOK orc c
    · rw [if_pos h2] at h; cases h; exact ⟨not_lt.1 h1, rfl⟩
    · rw [if_neg h2] at h; cases h

/-- **The bounds in every round in mode `run`.** -/
theorem run_bndO (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (w : WorldO d) {T : ℚ}
    (hc : CfgBO T (cfgW d n δ r0 R0 a w)) (hB : ((parO d n δ).B : ℚ) ≤ T) (hB8 : 8 ≤ (parO d n δ).B) :
    ∀ t (st : St d), modeO d n δ r0 R0 a w t = .run st → StI T (parO d n δ).Rint t st
  | 0, st, h => by
    have h0 : mode0O w.orc (cfgW d n δ r0 R0 a w) = .run st := h
    obtain ⟨-, e⟩ := mode0O_run h0
    subst e
    exact init_bnd (by linarith [hc.cb.T4]) (Nat.cast_nonneg _) _ hc.cb.A0 hc.cb.B0 _
  | t + 1, st, h => by
    have hξ := draw_abs (d := d) w.cs (K0O d n δ r0 R0) (parO d n δ).B t hB8
    unfold modeO at h
    simp only [trajO] at h
    rcases hm : (trajO d n δ r0 R0 a w t).1 with _ | _ | st1
    · rw [hm] at h; cases h
    · rw [hm] at h; cases h
    rw [hm] at h
    have hs := run_bndO n δ r0 R0 a w hc hB hB8 t st1 hm
    refine step_bndO w.orc hc n hs _ _ _ (fun i => (hξ.1 i).trans hB) (hξ.2.trans hB) ?_ h
    exact_mod_cast clip_abs _ _

/-- **`magBLO`: the magnitudes of BL-O's state**, on every input and world. -/
theorem magBLO : MagBLO := by
  refine ⟨20000, 1, ?_⟩
  intro d n E0 δ r0 R0 a hI w _ t st ht hst
  have hd := hI.hd
  have hn := hI.hn
  obtain ⟨st0, h0⟩ := modeO_run0 n δ r0 R0 a w t st hst
  have h0' : mode0O w.orc (cfgW d n δ r0 R0 a w) = .run st0 := h0
  obtain ⟨heps, -⟩ := mode0O_run h0'
  obtain ⟨hT4, hdT, hnT, -, he0, heI, hlam, hkap, hnu, hLam, hA0, hB0, hRint, -, hBT, hpK, -⟩ :=
    fld_unit d n (kDel δ) hd hn
  have hcb : CfgB (2 ^ Ku d n (kDel δ)) (cfgV (cfgW d n δ r0 R0 a w)) :=
    ⟨hT4, hdT, fun i => i.elim0, fun i => i.elim0, he0, heps, heI, hlam, hkap, hnu, hLam, hA0, hB0, hRint⟩
  have hclip : (2 : ℚ) ^ (cfgW d n δ r0 R0 a w).qO ≤
      2 ^ (cfgW d n δ r0 R0 a w).par.p * 2 ^ Ku d n (kDel δ) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (qO_le _ d n (kDel δ) hd rfl rfl)
  have hc : CfgBO (2 ^ Ku d n (kDel δ)) (cfgW d n δ r0 R0 a w) := ⟨hcb, hclip⟩
  have hBe : (parK d n (kDel δ)).B = 2 * ((parK d n (kDel δ)).p + (n * (d + 2)).size + 2) := rfl
  have hp160 := (pF_ge d n (kDel δ)).1
  have hB8 : 8 ≤ (parK d n (kDel δ)).B := by rw [hBe]; omega
  have hs := run_bndO n δ r0 R0 a w hc hBT hB8 t st hst
  have hKW := Ku_le d n δ r0 R0 a hI.hδ0
  set K := Ku d n (kDel δ) with hKdef
  have hT2 : (2 : ℚ) ≤ 2 ^ K := by linarith
  have hT1 : (1 : ℚ) ≤ 2 ^ K := by linarith
  have hp : (2 : ℚ) ^ (parO d n δ).p ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hpK
  have key : ∀ x : ℚ, |x| ≤ ((2 : ℚ) ^ K) ^ 31 →
      |qn (parO d n δ).p x| ≤ 2 ^ (20000 * (wU d n δ r0 R0 a + E0 + 1) ^ 1) := fun x hx => by
    have h := qn_bnd hT2 hp hx
    have h2 : ((2 : ℚ) ^ K) ^ (31 + 2) ≤ 2 ^ (20000 * (wU d n δ r0 R0 a + E0 + 1) ^ 1) := by
      rw [← pow_mul]; exact pow_le_pow_right₀ (by norm_num) (by rw [pow_one]; omega)
    exact_mod_cast h.trans h2
  have hsum : ∀ y : ℚ, |y| ≤ t * ((2 : ℚ) ^ K) ^ 30 → |y| ≤ ((2 : ℚ) ^ K) ^ 31 := fun y hy => by
    have ht' : (t : ℚ) ≤ 2 ^ K := (by exact_mod_cast ht : (t : ℚ) ≤ n).trans hnT
    have h30 : (0 : ℚ) ≤ ((2 : ℚ) ^ K) ^ 30 := by positivity
    calc |y| ≤ t * ((2 : ℚ) ^ K) ^ 30 := hy
      _ ≤ 2 ^ K * ((2 : ℚ) ^ K) ^ 30 := mul_le_mul_of_nonneg_right ht' h30
      _ = ((2 : ℚ) ^ K) ^ 31 := by ring
  have hent : ∀ y : ℚ, |y| ≤ 2 ^ K → |y| ≤ ((2 : ℚ) ^ K) ^ 31 := fun y hy =>
    bnd_up hT1 (pw1 hy) (by norm_num)
  exact ⟨fun i j => key _ (hent _ (hs.A i j)), fun i j => key _ (hent _ (hs.B i j)), fun j => key _ (hsum _ (hs.b j)),
    key _ (hsum _ hs.k), fun j => key _ (hsum _ (hs.G j)), key _ (hsum _ hs.l), hs.mu⟩

end AdversarialBco.Unified.MagO
