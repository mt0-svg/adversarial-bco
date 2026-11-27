/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOTst

@[expose] public section

/-!
# BL-O's R2 in mode `run`, the data of the gauge

After v2.1's `xR2x` (`X' = X̂/D_X`, `X̂` in `aXh`, `D_X` in `sDX`), the gauge `gaugeP` of `X'` needs, in the form of
the play leaf, the point `(D_X; X̂)` (array `aXD`) and the centre `0 = (1; 0)` (array `aA0`); the radius
`2 |X'|₁ = H_n/D_X` with `H_n = 2 Σ_k |X̂_k|` (slot `sHn`); and the step count `jG = p + 4 + clog₂(2 d R_int)` with
`2^jG`. The gauge runs on `H_n' = H_n` if `H_n > 0` and `H_n' = 1` otherwise (slot `300`): at `X' = 0` the product
`H_n u` of the tail is `0` whatever the counter `u`, and `gaugeP` is `0` there.

* `xpts`: `aXD`, `aA0`, `sHa = Σ_k |X̂_k|` (one pass, `|x|` by a test on the sign);
* `xjG`: `jG` into the register `rJG`, `2^jG` into the slot `302`;
* `xhn`: `sHn = 2 sHa`, `H_n'` into `300`, `D_X` into `301`.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

/-! ## The cells -/

/-- The point `X'` as `(D_X; X̂)`. -/
abbrev aXD : ℕ := 32
/-- The gauge's centre `0` as `(1; 0)`. -/
abbrev aA0 : ℕ := 33
/-- The gauge's test point. -/
abbrev aTP : ℕ := 34
/-- `Σ_k |X̂_k|`. -/
abbrev sHa : ℕ := 290
/-- `H_n = 2 Σ_k |X̂_k|`. -/
abbrev sHn : ℕ := 291
/-- A scratch slot. -/
abbrev sT2 : ℕ := 292
/-- `2 d R_int`. -/
abbrev s2dR : ℕ := 293
/-- The doubling slot of `xclogS`. -/
abbrev sW2 : ℕ := 294
/-- The loop counter of `xpts`. -/
abbrev rk2 : ℕ := 36
/-- The loop counter plus one. -/
abbrev rk3 : ℕ := 37
/-- `clog₂(2 d R_int)`. -/
abbrev rcl : ℕ := 38
/-- `4`, then the counter of `xpow2`. -/
abbrev rc4 : ℕ := 39
/-- The gauge's step count `jG`. -/
abbrev rJG : ℕ := 40
/-- The test's answer. -/
abbrev rGt : ℕ := 41

/-- `qomega` with the cells of R2 unfolded. -/
macro "r2omega" : tactic => `(tactic| ((try simp only [aXD, aA0, aTP, sHa, sHn, sT2, s2dR, sW2, rk2, rk3, rcl, rc4,
  rJG, rGt] at *) <;> qomega))

/-! ## The point and the centre -/

/-- `aXD := (D_X; X̂)`, `aA0 := (1; 0)`, `sHa := Σ_k |X̂_k|`. -/
def xpts (L : Layout) : XCmd :=
  .seq (.prim (.frag (.nconst rk2 0))) <|
  .seq (toX (VL.aset L aXD rk2 sDX)) <|
  .seq (toX (VL.sconst L sT2 1)) <|
  .seq (toX (VL.aset L aA0 rk2 sT2)) <|
  .seq (toX (VL.sconst L sHa 0)) <|
  xforN rk2 rD rOne (
    .seq (.prim (.frag (.nadd rk3 rk2 rOne))) <|
    .seq (toX (VL.aget L sT2 aXh rk2)) <|
    .seq (toX (VL.aset L aXD rk3 sT2)) <|
    .seq (toX (VL.aset L aA0 rk3 sZ)) <|
    xifS L sT2 sZ (toX (VL.sop2 L .sub sHa sHa sT2)) (toX (VL.sop2 L .add sHa sHa sT2)))

/-- The entries of `X̂` as a sequence, `0` from `d` on. -/
def xhN (xh : Fin d → ℤ) (k : ℕ) : ℤ := if h : k < d then xh ⟨k, h⟩ else 0

theorem xhN_fin (xh : Fin d → ℤ) (k : Fin d) : xhN xh k = xh k := by simp [xhN]

theorem sum_xhN (xh : Fin d → ℤ) : ∑ k ∈ Finset.range d, |xhN xh k| = ∑ k, |xh k| := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => |xhN xh k|) d]
  simp only [xhN_fin]

set_option maxHeartbeats 4000000 in
/-- **The point and the centre of the gauge**, and `Σ_k |X̂_k|`; `X̂`, `D_X` below `2^B`, `d ≤ 2^B`. -/
theorem XV.pts {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hNS : sW2 < L.NS)
    (hNN : rk3 < L.NN) (hNA : aTP < L.NA) (hd1 : 1 ≤ d) {DX : ℤ} {xh : Fin d → ℤ} {B : ℕ}
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (hDX : σ.sc sDX = DX)
    (hxh : ∀ k : Fin d, σ.arr aXh k = xh k) (bDX : |DX| ≤ 2 ^ B) (bxh : ∀ k, |xh k| ≤ 2 ^ B) (hdB : d ≤ 2 ^ B)
    (hℓ : 2 * B + 1 < ℓ) :
    XRunsB L X ℓa ℓ (xpts L) σ (1 + (2 + (1 + (2 + (1 + (d * (1 + (2 + (2 + (2 + 3))) + 3) + 3))))))
      (fun σ' => σ'.arr aXD 0 = DX ∧ (∀ k : Fin d, σ'.arr aXD (1 + k) = xh k) ∧ σ'.arr aA0 0 = 1 ∧
        (∀ k : Fin d, σ'.arr aA0 (1 + k) = 0) ∧ σ'.sc sHa = ((∑ k, |xh k| : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => y = sHa ∨ y = sT2) (fun j => j = rk2 ∨ j = rk3) (fun b _ => b = aXD ∨ b = aA0) σ σ') := by
  have hasz : ∀ j ≤ d, j < asz d := fun j hj => by unfold asz; nlinarith
  have hda : d < 2 ^ ℓa := lt_of_le_of_lt (by unfold asz; nlinarith) (asz_lt hL (a := 0) (by r2omega))
  have hb : ∀ z : ℤ, |z| ≤ 2 ^ (2 * B) → |z| < 2 ^ ℓ := fun z hz =>
    lt_of_le_of_lt hz (pow_lt_pow_right₀ (by norm_num) (by r2omega))
  have hBB : ∀ z : ℤ, |z| ≤ 2 ^ B → |z| ≤ 2 ^ (2 * B) := fun z hz =>
    hz.trans (pow_le_pow_right₀ (by norm_num) (by r2omega))
  have hxN : ∀ k, |xhN xh k| ≤ 2 ^ B := fun k => by
    unfold xhN; split_ifs with h
    · exact bxh _
    · simp
  have hS : ∀ t ≤ d, |(∑ k ∈ Finset.range t, |xhN xh k|)| ≤ 2 ^ (2 * B) := fun t ht => by
    rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
    calc ∑ k ∈ Finset.range t, |xhN xh k| ≤ ∑ _k ∈ Finset.range t, (2 : ℤ) ^ B :=
          Finset.sum_le_sum fun k _ => hxN k
      _ = t * 2 ^ B := by simp
      _ ≤ 2 ^ B * 2 ^ B := mul_le_mul_of_nonneg_right (by exact_mod_cast ht.trans hdB) (by positivity)
      _ = 2 ^ (2 * B) := by rw [two_mul, pow_add]
  have h1ℓ : |(1 : ℤ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by r2omega)
  -- the prefix
  have hXA : aXD ≠ aA0 := by decide
  refine XV.seq (XV.nconst hL (i := rk2) (by r2omega) 0 (by positivity)) fun σ1 e1 => ?_
  have k1 : σ1.nat rk2 = 0 := by rw [e1]; simp
  refine XV.seq (XV.aset hL (σ := σ1) (a := aXD) (i := rk2) (x := sDX) (by r2omega) (by r2omega) (by r2omega)
    (by rw [k1]; exact hasz 0 (by r2omega))
    (by rw [e1, Env.setNat_sc, hDX]; exact XV.abs_int_lt (hb _ (hBB _ bDX)))) fun σ2 e2 => ?_
  have k2 : σ2.nat rk2 = 0 := by rw [e2, Env.setArr_nat, k1]
  refine XV.seq (XV.constI hL (σ := σ2) (x := sT2) (by r2omega) 1 h1ℓ) fun σ3 e3 => ?_
  have k3 : σ3.nat rk2 = 0 := by rw [e3, Env.setSc_nat, k2]
  refine XV.seq (XV.aset hL (σ := σ3) (a := aA0) (i := rk2) (x := sT2) (by r2omega) (by r2omega) (by r2omega)
    (by rw [k3]; exact hasz 0 (by r2omega))
    (by rw [e3, Env.setSc_sc, ite_eq_left rfl]; exact XV.abs_int_lt h1ℓ)) fun σ4 e4 => ?_
  refine XV.seq (XV.constI hL (σ := σ4) (x := sHa) (by r2omega) 0 (by simp)) fun σ5 e5 => ?_
  have F5 : FrameA (fun y => y = sHa ∨ y = sT2) (fun j => j = rk2 ∨ j = rk3) (fun b _ => b = aXD ∨ b = aA0) σ σ5 := by
    rw [e5, e4, e3, e2, e1]
    exact (((((FrameA.refl _ _ _ σ).setNat (Or.inl rfl) _).setArr (Or.inl rfl) _).setSc (Or.inr rfl) _).setArr
      (Or.inr rfl) _).setSc (Or.inl rfl) _
  have v5X : σ5.arr aXD 0 = DX := by
    rw [e5, Env.setSc_arr, e4, Env.setArr_arr, ite_eq_right (fun h => hXA h.1), e3, Env.setSc_arr, e2,
      Env.setArr_arr, ite_eq_left ⟨rfl, k1.symm⟩, e1, Env.setNat_sc, hDX]
  have v5A : σ5.arr aA0 0 = 1 := by
    rw [e5, Env.setSc_arr, e4, Env.setArr_arr, ite_eq_left ⟨rfl, k3.symm⟩, e3, Env.setSc_sc, ite_eq_left rfl]; simp
  have v5S : σ5.sc sHa = ((0 : ℤ) : ℝ) := by rw [e5, Env.setSc_sc, ite_eq_left rfl]
  have v5d : σ5.draws = σ.draws := by rw [e5, e4, e3, e2, e1]; simp
  have n5 : σ5.nat rD = d := by rw [F5.1 _ (by r2omega), hD]
  have o5 : σ5.nat rOne = 1 := by rw [F5.1 _ (by r2omega), h1]
  -- the loop
  let J : ℕ → Env d → Prop := fun t σ' => σ'.arr aXD 0 = DX ∧ (∀ k < t, σ'.arr aXD (1 + k) = xhN xh k) ∧
    σ'.arr aA0 0 = 1 ∧ (∀ k < t, σ'.arr aA0 (1 + k) = 0) ∧
    σ'.sc sHa = ((∑ k ∈ Finset.range t, |xhN xh k| : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
    FrameA (fun y => y = sHa ∨ y = sT2) (fun j => j = rk2 ∨ j = rk3) (fun b _ => b = aXD ∨ b = aA0) σ σ'
  refine XV.mono (XV.forN hL (i := rk2) (n := rD) (one := rOne) (by r2omega) (by simp only [rD, rk3] at *; omega)
    (by simp only [rOne, rk3] at *; omega) (by decide) (by decide) d (1 + (2 + (2 + (2 + 3)))) hda J σ5 n5 o5
    ⟨by rw [Env.setNat_arr, v5X], fun k hk => absurd hk (by r2omega), by rw [Env.setNat_arr, v5A],
      fun k hk => absurd hk (by r2omega), by rw [Env.setNat_sc, v5S]; simp, by rw [Env.setNat_draws, v5d],
      F5.setNat (Or.inl rfl) 0⟩ ?_) le_rfl ?_
  · intro t ht σ' ⟨j0, jX, j1, jA, jS, jd, F⟩ hk hn ho
    have eXh : σ'.arr aXh t = xh ⟨t, ht⟩ := by
      rw [F.2.2.1 aXh t (by simp only [aXh, aXD, aA0]; omega)]; exact hxh ⟨t, ht⟩
    have ez : σ'.sc sZ = 0 := by rw [F.2.1 sZ (by simp only [sZ, sHa, sT2]; omega), hz]
    have bt : |xh ⟨t, ht⟩| ≤ 2 ^ (2 * B) := hBB _ (bxh _)
    set S := ∑ k ∈ Finset.range t, |xhN xh k| with hSdef
    have bS : |S| ≤ 2 ^ (2 * B) := hS t (by r2omega)
    have bS1 : |(S + |xh ⟨t, ht⟩|)| ≤ 2 ^ (2 * B) := by
      have e : S + |xh ⟨t, ht⟩| = ∑ k ∈ Finset.range (t + 1), |xhN xh k| := by
        rw [Finset.sum_range_succ, hSdef]; simp [xhN, ht]
      rw [e]; exact hS (t + 1) (by r2omega)
    have hne3 : rk2 ≠ rk3 := by decide
    -- `rk3 := rk2 + 1`
    refine XV.seq (XV.nadd hL (i := rk3) (a := rk2) (b := rOne) (by r2omega) (by r2omega)
      (by simp only [rOne, rk3] at *; omega) (by rw [hk]; omega) (by rw [ho]; omega)) fun σa ea => ?_
    have a2 : σa.nat rk2 = t := by rw [ea]; simp [hk]
    have a3 : σa.nat rk3 = t + 1 := by rw [ea]; simp [hk, ho]
    have aS : σa.sc = σ'.sc := by rw [ea]; rfl
    have aA : σa.arr = σ'.arr := by rw [ea]; rfl
    have aD : σa.draws = σ'.draws := by rw [ea]; rfl
    have aF : FrameA (fun y => y = sHa ∨ y = sT2) (fun j => j = rk2 ∨ j = rk3) (fun b _ => b = aXD ∨ b = aA0) σ σa := by
      rw [ea]; exact F.setNat (Or.inr rfl) _
    -- `sT2 := X̂_t`
    refine XV.seq (XV.aget hL (σ := σa) (x := sT2) (a := aXh) (i := rk2) (by r2omega)
      (by simp only [aXh, aTP] at *; omega) (by r2omega) (by rw [a2]; exact hasz t (by r2omega))
      (by rw [a2, aA, eXh]; exact XV.abs_int_lt (hb _ bt))) fun σb eb => ?_
    have b2 : σb.nat rk2 = t := by rw [eb]; simp [a2]
    have b3 : σb.nat rk3 = t + 1 := by rw [eb]; simp [a3]
    have bT : σb.sc sT2 = xh ⟨t, ht⟩ := by rw [eb]; simp [a2, aA, eXh]
    have bA : σb.arr = σ'.arr := by rw [eb, Env.setSc_arr, aA]
    have bSc : ∀ y, y ≠ sT2 → σb.sc y = σ'.sc y := fun y hy => by rw [eb, Env.setSc_sc, ite_eq_right hy, aS]
    have bD : σb.draws = σ'.draws := by rw [eb, Env.setSc_draws, aD]
    have bF : FrameA (fun y => y = sHa ∨ y = sT2) (fun j => j = rk2 ∨ j = rk3) (fun b _ => b = aXD ∨ b = aA0) σ σb := by
      rw [eb]; exact aF.setSc (Or.inr rfl) _
    -- `aXD[t + 1] := X̂_t`
    refine XV.seq (XV.aset hL (σ := σb) (a := aXD) (i := rk3) (x := sT2) (by r2omega) (by r2omega) (by r2omega)
      (by rw [b3]; exact hasz (t + 1) (by r2omega)) (by rw [bT]; exact XV.abs_int_lt (hb _ bt))) fun σc ec => ?_
    have c2 : σc.nat rk2 = t := by rw [ec, Env.setArr_nat, b2]
    have cT : σc.sc sT2 = xh ⟨t, ht⟩ := by rw [ec, Env.setArr_sc, bT]
    have cSc : ∀ y, y ≠ sT2 → σc.sc y = σ'.sc y := fun y hy => by rw [ec, Env.setArr_sc, bSc y hy]
    have cA : ∀ b k, σc.arr b k = if b = aXD ∧ k = t + 1 then (xh ⟨t, ht⟩ : ℝ) else σ'.arr b k := fun b k => by
      rw [ec, Env.setArr_arr, b3, bT, bA]
    have cD : σc.draws = σ'.draws := by rw [ec, Env.setArr_draws, bD]
    have cF : FrameA (fun y => y = sHa ∨ y = sT2) (fun j => j = rk2 ∨ j = rk3) (fun b _ => b = aXD ∨ b = aA0) σ σc := by
      rw [ec]; exact bF.setArr (Or.inl rfl) _
    have cn : σc.nat = σb.nat := by rw [ec, Env.setArr_nat]
    -- `aA0[t + 1] := 0`
    refine XV.seq (XV.aset hL (σ := σc) (a := aA0) (i := rk3) (x := sZ) (by r2omega) (by r2omega) (by r2omega)
      (by rw [cn, b3]; exact hasz (t + 1) (by r2omega))
      (by rw [cSc _ (by decide), ez]; simp only [abs_zero]; positivity)) fun σd ed => ?_
    have dn : σd.nat = σb.nat := by rw [ed, Env.setArr_nat, cn]
    have dT : σd.sc sT2 = xh ⟨t, ht⟩ := by rw [ed, Env.setArr_sc, cT]
    have dZ : σd.sc sZ = 0 := by rw [ed, Env.setArr_sc, cSc _ (by decide), ez]
    have dS : σd.sc sHa = (S : ℝ) := by rw [ed, Env.setArr_sc, cSc _ (by decide), jS]
    have dA : ∀ b k, σd.arr b k = if b = aA0 ∧ k = t + 1 then 0 else σc.arr b k := fun b k => by
      rw [ed, Env.setArr_arr, cn, b3, cSc _ (by decide), ez]
    have dD : σd.draws = σ.draws := by rw [ed, Env.setArr_draws, cD, jd]
    have dF : FrameA (fun y => y = sHa ∨ y = sT2) (fun j => j = rk2 ∨ j = rk3) (fun b _ => b = aXD ∨ b = aA0) σ σd := by
      rw [ed]; exact cF.setArr (Or.inr rfl) _
    -- the end of the turn, from `sHa := S + |X̂_t|`
    have fin : ∀ σe : Env d, σe = σd.setSc sHa (((S + |xh ⟨t, ht⟩| : ℤ)) : ℝ) →
        σe.nat rk2 = t ∧ σe.nat rD = d ∧ σe.nat rOne = 1 ∧ J (t + 1) (σe.setNat rk2 (t + 1)) := by
      intro σe ee
      have en : σe.nat = σb.nat := by rw [ee, Env.setSc_nat, dn]
      have bn : ∀ j, j ≠ rk3 → σb.nat j = σ'.nat j := fun j hj => by
        rw [eb, Env.setSc_nat, ea, Env.setNat_nat, ite_eq_right hj]
      refine ⟨by rw [en, b2], by rw [en, bn _ (by decide), hn], by rw [en, bn _ (by decide), ho], ?_, ?_, ?_, ?_, ?_,
        by rw [Env.setNat_draws, ee, Env.setSc_draws, dD], ?_⟩
      · rw [Env.setNat_arr, ee, Env.setSc_arr, dA, ite_eq_right (fun h => absurd h.1 (by decide)), cA, ite_eq_right (by r2omega), j0]
      · intro k hk'
        rw [Env.setNat_arr, ee, Env.setSc_arr, dA, ite_eq_right (fun h => absurd h.1 (by decide)), cA]
        by_cases hkt : k = t
        · subst hkt; rw [ite_eq_left ⟨rfl, by r2omega⟩, xhN_fin xh ⟨k, ht⟩]
        · rw [ite_eq_right (fun h => hkt (by r2omega)), jX k (by r2omega)]
      · rw [Env.setNat_arr, ee, Env.setSc_arr, dA, ite_eq_right (by r2omega), cA, ite_eq_right (fun h => absurd h.1 (by decide)), j1]
      · intro k hk'
        rw [Env.setNat_arr, ee, Env.setSc_arr, dA]
        by_cases hkt : k = t
        · subst hkt; rw [ite_eq_left ⟨rfl, by r2omega⟩]
        · rw [ite_eq_right (fun h => hkt (by r2omega)), cA, ite_eq_right (fun h => absurd h.1 (by decide)), jA k (by r2omega)]
      · rw [Env.setNat_sc, ee, Env.setSc_sc, ite_eq_left rfl, Finset.sum_range_succ, ← hSdef]
        simp [xhN, ht]
      · rw [ee]; exact (dF.setSc (Or.inl rfl) _).setNat (Or.inl rfl) _
    -- the sign test
    have bx : |(xh ⟨t, ht⟩ : ℝ)| < 2 ^ ℓ := XV.abs_int_lt (hb _ bt)
    by_cases hneg : xh ⟨t, ht⟩ < 0
    · refine XV.mono (XV.ifS_t hL (σ := σd) (x := sT2) (y := sZ) (by r2omega) (by r2omega) (by rw [dT]; exact bx)
        (by rw [dZ]; simp) (by rw [dT, dZ]; exact_mod_cast hneg)
        (XV.subI hL (x := sHa) (a := sHa) (b := sT2) (u := S) (v := xh ⟨t, ht⟩) (by r2omega) (by r2omega) (by r2omega)
          dS dT (hb _ bS) (hb _ bt) ?_)) (by r2omega) fun σe ee => fin σe (by rw [ee, abs_of_neg hneg, sub_eq_add_neg])
      have e : S - xh ⟨t, ht⟩ = S + |xh ⟨t, ht⟩| := by rw [abs_of_neg hneg]; ring
      rw [e]; exact hb _ bS1
    · replace hneg := not_lt.1 hneg
      refine XV.mono (XV.ifS_f hL (σ := σd) (x := sT2) (y := sZ) (by r2omega) (by r2omega) (by rw [dT]; exact bx)
        (by rw [dZ]; simp) (by rw [dT, dZ]; exact_mod_cast not_lt.2 hneg)
        (XV.addI hL (x := sHa) (a := sHa) (b := sT2) (u := S) (v := xh ⟨t, ht⟩) (by r2omega) (by r2omega) (by r2omega)
          dS dT (hb _ bS) (hb _ bt) (by rw [← abs_of_nonneg hneg]; exact hb _ bS1))) le_rfl
        fun σe ee => fin σe (by rw [ee, abs_of_nonneg hneg])
  · rintro σ' ⟨⟨j0, jX, j1, jA, jS, jd, F⟩, -⟩
    refine ⟨j0, fun k => by rw [jX k k.2, xhN_fin], j1, fun k => jA k k.2, by rw [jS, sum_xhN], jd, F⟩

/-! ## The step count of the gauge -/

/-- `jG = p + clog₂(2 d R_int) + 4`. -/
def jGv (p d Ri : ℕ) : ℕ := p + Nat.clog 2 (2 * d * Ri) + 4

/-- `s2dR := 2 d R_int`, `rJG := jG`, `sc 302 := 2^jG`. -/
def xjG (L : Layout) : XCmd :=
  .seq (toX (VL.ncast L s2dR rD)) <|
  .seq (toX (VL.sop2 L .add s2dR s2dR s2dR)) <|
  .seq (toX (VL.sop2 L .mul s2dR s2dR sRint)) <|
  .seq (xclogS L sW2 s2dR rcl rOne) <|
  .seq (.prim (.frag (.nadd rJG rP rcl))) <| .seq (.prim (.frag (.nconst rc4 4))) <|
  .seq (.prim (.frag (.nadd rJG rJG rc4))) <|
  xpow2 L 302 rc4 rJG rOne

set_option maxHeartbeats 2000000 in
/-- **The step count of the gauge** `jG` and `2^jG`; `d`, `R_int` below `2^B`, `p ≤ B`. -/
theorem XV.jG {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hNS : 302 < L.NS)
    (hNN : rJG < L.NN) (hNA : 0 < L.NA) {p Ri B : ℕ} (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1)
    (hp : σ.nat rP = p) (hR : σ.sc sRint = (Ri : ℝ)) (hRB : Ri ≤ 2 ^ B) (hdB : d ≤ 2 ^ B) (hpB : p ≤ B)
    (hℓ : 4 * B + 8 < ℓ) (hℓa : 4 * B + 8 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xjG L) σ (1 + (1 + (1 + ((4 * (2 * B + 1) + 4) + (1 + (1 + (1 + (4 * jGv p d Ri + 4))))))))
      (fun σ' => σ'.nat rJG = jGv p d Ri ∧ σ'.sc 302 = 2 ^ jGv p d Ri ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => y = s2dR ∨ y = sW2 ∨ y = 302) (fun j => j = rcl ∨ j = rc4 ∨ j = rJG) (fun _ _ => False)
          σ σ') := by
  have hda : d < 2 ^ ℓa := lt_of_le_of_lt (by unfold asz; nlinarith) (asz_lt hL hNA)
  have hb : ∀ z : ℤ, |z| ≤ 2 ^ (2 * B + 1) → |z| < 2 ^ ℓ := fun z hz =>
    lt_of_le_of_lt hz (pow_lt_pow_right₀ (by norm_num) (by r2omega))
  have bd : |(d : ℤ)| ≤ 2 ^ (2 * B + 1) := by
    rw [abs_of_nonneg (by positivity)]
    exact (show (d : ℤ) ≤ 2 ^ B by exact_mod_cast hdB).trans (pow_le_pow_right₀ (by norm_num) (by r2omega))
  have bdd : |(d : ℤ) + d| ≤ 2 ^ (2 * B + 1) := by
    rw [abs_of_nonneg (by positivity), pow_succ, pow_mul]
    have : (d : ℤ) ≤ 2 ^ B := by exact_mod_cast hdB
    have : (2 : ℤ) ^ B ≤ (2 ^ 2) ^ B := pow_le_pow_left₀ (by norm_num) (by norm_num) B
    linarith
  have hRd : ((d : ℤ) + d) * Ri = ((2 * d * Ri : ℕ) : ℤ) := by push_cast; ring
  have bv : ((d : ℤ) + d) * Ri ≤ 2 ^ (2 * B + 1) := by
    rw [hRd]
    have : 2 * d * Ri ≤ 2 ^ (2 * B + 1) := by
      calc 2 * d * Ri ≤ 2 * 2 ^ B * 2 ^ B := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hdB) hRB
        _ = 2 ^ (2 * B + 1) := by ring
    exact_mod_cast this
  have bR : |(Ri : ℤ)| ≤ 2 ^ (2 * B + 1) := by
    rw [abs_of_nonneg (by positivity)]
    exact (show (Ri : ℤ) ≤ 2 ^ B by exact_mod_cast hRB).trans (pow_le_pow_right₀ (by norm_num) (by r2omega))
  have hv0 : 0 ≤ ((d : ℤ) + d) * Ri := by positivity
  -- `2 d R_int`
  refine XV.seq (XV.ncastI hL (x := s2dR) (i := rD) (by r2omega) (by r2omega) (by rw [hD]; exact hda)) fun σ1 e1 => ?_
  have s1 : σ1.sc s2dR = ((d : ℤ) : ℝ) := by rw [e1]; simp [hD]
  refine XV.seq (XV.addI hL (σ := σ1) (x := s2dR) (a := s2dR) (b := s2dR) (u := d) (v := d) (by r2omega) (by r2omega)
    (by r2omega) s1 s1 (hb _ bd) (hb _ bd) (hb _ bdd)) fun σ2 e2 => ?_
  have s2 : σ2.sc s2dR = (((d : ℤ) + d : ℤ) : ℝ) := by rw [e2]; simp
  have s2R : σ2.sc sRint = ((Ri : ℤ) : ℝ) := by rw [e2, e1]; simp [hR]
  refine XV.seq (XV.mulI hL (σ := σ2) (x := s2dR) (a := s2dR) (b := sRint) (u := d + d) (v := Ri) (by r2omega)
    (by r2omega) (by r2omega) s2 s2R (hb _ bdd) (hb _ bR) (hb _ (by rw [abs_of_nonneg hv0]; exact bv))) fun σ3 e3 => ?_
  have s3 : σ3.sc s2dR = ((((d : ℤ) + d) * Ri : ℤ) : ℝ) := by rw [e3]; simp
  have n3 : σ3.nat = σ.nat := by rw [e3, e2, e1]; rfl
  have d3 : σ3.draws = σ.draws := by rw [e3, e2, e1]; rfl
  have F3 : FrameA (fun y => y = s2dR ∨ y = sW2 ∨ y = 302) (fun j => j = rcl ∨ j = rc4 ∨ j = rJG)
      (fun _ _ => False) σ σ3 := by
    rw [e3, e2, e1]
    exact (((FrameA.refl _ _ _ σ).setSc (Or.inl rfl) _).setSc (Or.inl rfl) _).setSc (Or.inl rfl) _
  -- `clog₂`
  have hcl : Nat.clog 2 (2 * d * Ri) ≤ 2 * B + 1 := Nat.clog_le_of_le_pow (by
    calc 2 * d * Ri ≤ 2 * 2 ^ B * 2 ^ B := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hdB) hRB
      _ = 2 ^ (2 * B + 1) := by ring)
  refine XV.seq (XV.clogS hL (σ := σ3) (w := sW2) (x := s2dR) (c := rcl) (one := rOne) (G := 2 * B + 1) (by r2omega)
    (by r2omega) (by r2omega) (by simp only [rOne, rJG] at *; omega) (by decide) (by decide) s3 hv0 bv
    (by rw [n3, h1]) (by r2omega) (by r2omega)) fun σ4 ⟨c4, d4, F4⟩ => ?_
  rw [hRd, Int.toNat_natCast] at c4
  have o4 : σ4.nat rOne = 1 := by rw [F4.1 _ (by decide), n3, h1]
  have p4 : σ4.nat rP = p := by rw [F4.1 _ (by decide), n3, hp]
  have F4' : FrameA (fun y => y = s2dR ∨ y = sW2 ∨ y = 302) (fun j => j = rcl ∨ j = rc4 ∨ j = rJG)
      (fun _ _ => False) σ σ4 :=
    F3.trans (FrameA.ofP (F4.mono (fun y h => Or.inr (Or.inl h)) (fun j h => Or.inl h)))
  -- `jG`
  refine XV.seq (XV.nadd hL (σ := σ4) (i := rJG) (a := rP) (b := rcl) hNN (by simp only [rP, rJG] at *; omega)
    (by simp only [rcl, rJG] at *; omega) (by rw [p4]; omega) (by rw [c4]; omega)) fun σ5 e5 => ?_
  have j5 : σ5.nat rJG = p + Nat.clog 2 (2 * d * Ri) := by rw [e5]; simp [p4, c4]
  have o5 : σ5.nat rOne = 1 := by rw [e5]; simp [o4]
  have F5 : FrameA (fun y => y = s2dR ∨ y = sW2 ∨ y = 302) (fun j => j = rcl ∨ j = rc4 ∨ j = rJG)
      (fun _ _ => False) σ σ5 := by rw [e5]; exact F4'.setNat (Or.inr (Or.inr rfl)) _
  refine XV.seq (XV.nconst hL (σ := σ5) (i := rc4) (by simp only [rc4, rJG] at *; omega) 4 (by r2omega))
    fun σ6 e6 => ?_
  have j6 : σ6.nat rJG = p + Nat.clog 2 (2 * d * Ri) := by rw [e6]; simp [j5]
  have f6 : σ6.nat rc4 = 4 := by rw [e6]; simp
  have o6 : σ6.nat rOne = 1 := by rw [e6]; simp [o5]
  have F6 : FrameA (fun y => y = s2dR ∨ y = sW2 ∨ y = 302) (fun j => j = rcl ∨ j = rc4 ∨ j = rJG)
      (fun _ _ => False) σ σ6 := by rw [e6]; exact F5.setNat (Or.inr (Or.inl rfl)) _
  refine XV.seq (XV.nadd hL (σ := σ6) (i := rJG) (a := rJG) (b := rc4) hNN hNN
    (by simp only [rc4, rJG] at *; omega) (by rw [j6]; omega) (by rw [f6]; omega)) fun σ7 e7 => ?_
  have j7 : σ7.nat rJG = jGv p d Ri := by rw [e7]; simp [j6, f6, jGv]
  have o7 : σ7.nat rOne = 1 := by rw [e7]; simp [o6]
  have F7 : FrameA (fun y => y = s2dR ∨ y = sW2 ∨ y = 302) (fun j => j = rcl ∨ j = rc4 ∨ j = rJG)
      (fun _ _ => False) σ σ7 := by rw [e7]; exact F6.setNat (Or.inr (Or.inr rfl)) _
  have d7 : σ7.draws = σ.draws := by rw [e7, e6, e5]; simp [d4, d3]
  have hjG : jGv p d Ri ≤ 3 * B + 5 := by unfold jGv; omega
  refine XV.mono (XV.pow2 hL (σ := σ7) (p := 302) (i := rc4) (n := rJG) (one := rOne) hNS
    (by simp only [rc4, rJG] at *; omega) hNN (by simp only [rOne, rJG] at *; omega) (by decide) (by decide)
    (W := jGv p d Ri) j7 o7 (by r2omega) (by r2omega)) le_rfl fun σ8 ⟨q8, _, F8⟩ => ?_
  refine ⟨by rw [F8.1 _ (by simp), j7], q8, by rw [F8.2.2.2.1, d7], ?_⟩
  exact F7.trans ⟨fun j hj => F8.1 j (by simp only [List.mem_singleton]; omega), fun y hy => F8.2.1 y (by
    simp only [List.mem_singleton]; omega), fun b k _ => by rw [F8.2.2.1], F8.2.2.2.2.1, F8.2.2.2.2.2⟩

/-! ## The radius of the gauge -/

/-- The gauge's numerator: `H_n` when positive, else `1`. -/
def hnG (Hn : ℤ) : ℤ := if 0 < Hn then Hn else 1

/-- `sHn := 2 sHa`; `sc 300 := hnG sHn`; `sc 301 := D_X`. -/
def xhn (L : Layout) : XCmd :=
  .seq (toX (VL.sop2 L .add sHn sHa sHa)) <|
  .seq (xifS L sZ sHn (toX (VL.sop2 L .add 300 sHn sZ)) (toX (VL.sconst L 300 1))) <|
  toX (VL.sop2 L .add 301 sDX sZ)

set_option maxHeartbeats 1000000 in
/-- **The radius of the gauge**: `H_n = 2 sHa`, the gauge's numerator `hnG H_n` and denominator `D_X`. -/
theorem XV.hn {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hNS : 301 < L.NS)
    {Ha DX : ℤ} {B : ℕ} (hz : σ.sc sZ = 0) (hHa : σ.sc sHa = Ha) (hDX : σ.sc sDX = DX) (bHa : |Ha| ≤ 2 ^ B)
    (bDX : |DX| ≤ 2 ^ B) (hℓ : B + 1 < ℓ) :
    XRunsB L X ℓa ℓ (xhn L) σ (1 + (3 + 1)) (fun σ' => σ'.sc sHn = ((2 * Ha : ℤ) : ℝ) ∧
      σ'.sc 300 = ((hnG (2 * Ha) : ℤ) : ℝ) ∧ σ'.sc 301 = DX ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = sHn ∨ y = 300 ∨ y = 301) (fun _ => False) (fun _ _ => False) σ σ') := by
  have hb : ∀ z : ℤ, |z| ≤ 2 ^ (B + 1) → |z| < 2 ^ ℓ := fun z hz =>
    lt_of_le_of_lt hz (pow_lt_pow_right₀ (by norm_num) (by r2omega))
  have b1 : |Ha| ≤ 2 ^ (B + 1) := bHa.trans (pow_le_pow_right₀ (by norm_num) (by r2omega))
  have bD : |DX| ≤ 2 ^ (B + 1) := bDX.trans (pow_le_pow_right₀ (by norm_num) (by r2omega))
  have b2 : |Ha + Ha| ≤ 2 ^ (B + 1) := by rw [pow_succ]; exact (abs_add_le _ _).trans (by linarith)
  have h1ℓ : |(1 : ℤ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by r2omega)
  refine XV.seq (XV.addI hL (x := sHn) (a := sHa) (b := sHa) (u := Ha) (v := Ha) (by r2omega) (by r2omega)
    (by r2omega) hHa hHa (hb _ b1) (hb _ b1) (hb _ b2)) fun σ1 e1 => ?_
  have s1n : σ1.sc sHn = ((Ha + Ha : ℤ) : ℝ) := by rw [e1]; simp
  have s1z : σ1.sc sZ = ((0 : ℤ) : ℝ) := by rw [e1]; simp [hz]
  have s1D : σ1.sc sDX = DX := by rw [e1]; simp [hDX]
  refine XV.seq (Q₁ := fun σ2 => σ2 = σ1.setSc 300 ((hnG (2 * Ha) : ℤ) : ℝ)) ?_ fun σ2 e2 => ?_
  · by_cases hpos : 0 < Ha + Ha
    · refine XV.mono (XV.ifS_t hL (x := sZ) (y := sHn) (by r2omega) (by r2omega) (by rw [s1z]; simp)
        (by rw [s1n]; exact XV.abs_int_lt (hb _ b2)) (by rw [s1z, s1n]; exact_mod_cast hpos)
        (XV.addI hL (x := 300) (a := sHn) (b := sZ) (u := Ha + Ha) (v := 0) (by r2omega) (by r2omega) (by r2omega)
          s1n s1z (hb _ b2) (by simp) (by simpa using hb _ b2))) (by r2omega) fun σ' e' => ?_
      rw [e']; unfold hnG; rw [ite_eq_left (by r2omega)]; congr 2; ring
    · refine XV.mono (XV.ifS_f hL (x := sZ) (y := sHn) (by r2omega) (by r2omega) (by rw [s1z]; simp)
        (by rw [s1n]; exact XV.abs_int_lt (hb _ b2)) (by rw [s1z, s1n]; exact_mod_cast hpos)
        (XV.constI hL (x := 300) (by r2omega) 1 h1ℓ)) le_rfl fun σ' e' => ?_
      rw [e']; unfold hnG; rw [ite_eq_right (by r2omega)]
  · have s2z : σ2.sc sZ = ((0 : ℤ) : ℝ) := by rw [e2]; simp [s1z]
    have s2D : σ2.sc sDX = DX := by rw [e2]; simp [s1D]
    refine XV.mono (XV.addI hL (σ := σ2) (x := 301) (a := sDX) (b := sZ) (u := DX) (v := 0) (by r2omega) (by r2omega)
      (by r2omega) s2D s2z (hb _ bD) (by simp) (by simpa using hb _ bD)) le_rfl fun σ3 e3 => ?_
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [e3, e2]; simp [s1n]; ring
    · rw [e3, e2]; simp
    · rw [e3]; simp
    · rw [e3, e2, e1]; simp
    · rw [e3, e2, e1]
      exact (((FrameA.refl _ _ _ σ).setSc (Or.inl rfl) _).setSc (Or.inr (Or.inl rfl)) _).setSc
        (Or.inr (Or.inr rfl)) _

end AdversarialBco.Unified.ProgO
