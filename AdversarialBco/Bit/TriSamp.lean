/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import Mathlib
public import AdversarialBco.Bit.TriCore
public import AdversarialBco.Bit.GsSpec
public import AdversarialBco.Poly.PgProcProof

@[expose] public section

/-!
# The position theorem, the parameters, the sampler and the stage geometry

The parameters of the core at dimension `d` with the rational majorants of (ROW-TRI): `triLa`, `triLh`, `triS` (Lemma
PAR's length), the box `triRa`, `triRh`, `triJa`, `triR`, `triA`, `triB`, its squared diameter `triD2`, the minorant
`triElo` of `e_h(ρ_h)`, the sampler bits `triKg`, the coupling error `triEpsG`, the bound `triGu` of the subgradient,
the rounding `triBv`, `triBu`, `triRound`, the number of steps `triNe` and the step `triJs`. The sampler of a vector draw
at `B` bits per coin block (`gsCell`, `bmCos`, `gsVec`, `gsOmega`, `gsCells`, `gsEps`, `gsLaw`). The stage geometry: the
cube `triCube`, its rows `triRowsA`, `triRowsB`, the number of stages `triMst`, the draw `triDraw` read off the coins and
the coin layout `triLay`.

The leaves:

* the row (R) of the parameters: `tri_par_box` (the box meets the conditions of the lemma that the box holds a
  minimiser), `tri_par_Gu` (the
  bound of the subgradient), `tri_par_stage` (the radii of the stages);
* the sampler: `gs_sure` (the sure bound of a draw), `gs_cell_law` (the law of the cell of a uniform variable),
  `gs_coin_block` (a block of `B` fair coins has the law of that cell), `gs_g_law` (the law of the exact draw),
  `gs_cells_ae`, `gs_pair_law`, `coin_curry_inj`, `readCoins_facts`, `readCoins_meas`;
* the rounding: `tri_round_err`, `tri_round_meas`, `tri_V_meas`;
* the stages: `rows_norm_le` (a polytope containing the unit ball has `‖a_k‖ ≤ b_k`, zero rows allowed),
  `tri_rows_pull` (the rows of a polytope in a position), `tri_cube_mid`, `posBody_closed`, `tri_poly_cc`, `tri_mst`,
  `tri_lay_inj` (the coin layout is injective).

Each lemma sits in a namespace `AdversarialBco.Bit.Aux_<name>` with its helpers, the lemma itself at
`AdversarialBco.Bit.<name>`.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

namespace AdversarialBco.Bit

open AdversarialBco.Poly

/-! The parameters of the core at dimension `d` (with the rational majorants of
(ROW-TRI)). -/

/-- `L(s) = ⌊5 s²/7⌋`. -/
def triLa (s : ℕ) : ℕ := 5 * s ^ 2 / 7

/-- `L_h(s) = ⌈50 s²/69⌉`. -/
def triLh (s : ℕ) : ℕ := (50 * s ^ 2 + 68) / 69

/-- The parameter lemma's length `s`: the least `s ≥ 4` with (C_s). -/
noncomputable def triS (d : ℕ) : ℕ := Nat.find (pg_par_exists d)

/-- `ρ_a = 2^L - 1`, the radius of the bodies of the core. -/
noncomputable def triRa (d : ℕ) : ℝ := 2 ^ triLa (triS d) - 1

/-- `ρ_h = 2^{L_h} - 1`, the radius of the analysis. -/
noncomputable def triRh (d : ℕ) : ℝ := 2 ^ triLh (triS d) - 1

/-- `j_a`: the least `j` with `9 d s ≤ 2^j`. -/
noncomputable def triJa (d : ℕ) : ℕ := Nat.clog 2 (9 * d * triS d)

/-- `r = 2^{L-3}`. -/
noncomputable def triR (d : ℕ) : ℝ := 2 ^ (triLa (triS d) - 3)

/-- `a = 2^{-j_a}`. -/
noncomputable def triA (d : ℕ) : ℝ := 1 / 2 ^ triJa d

/-- `b = 161 · 2^{L-10}`. -/
noncomputable def triB (d : ℕ) : ℝ := 161 * 2 ^ (triLa (triS d) - 10)

/-- `Δ² = 4 d r² + d (b - a)² + 2 d (d - 1) b²`, the squared diameter of the box. -/
noncomputable def triD2 (d : ℕ) : ℝ :=
  4 * d * triR d ^ 2 + d * (triB d - triA d) ^ 2 + 2 * d * (d - 1) * triB d ^ 2

/-- `e_lo = κ²/(922 d² (7/5) L_h (627/4000) ρ_h)`, a rational minorant of `e_h(ρ_h)`. -/
noncomputable def triElo (d : ℕ) : ℝ :=
  pgKappa ^ 2 / (922 * (d : ℝ) ^ 2 * (7 / 5 * triLh (triS d)) * (627 / 4000 * triRh d))

/-- `k_g`: the sampler reads `B_g = 4 k_g` bits per coordinate, with `2 ε_G ≤ e_lo/8`. -/
noncomputable def triKg (d : ℕ) : ℕ :=
  max 2 (Nat.clog 2 ⌈16 * triB d * (d + 1) * d * (8 * d + 2) / triElo d⌉₊)

/-- `ε_G = b (d + 1) d (8 d + 2)/2^{k_g}`, a majorant of the coupling error of the objective on the box. -/
noncomputable def triEpsG (d : ℕ) : ℝ := triB d * (d + 1) * d * (8 * d + 2) / 2 ^ triKg d

/-- `G_up = ⌊(8 d k_g)^{1/2}⌋ + 2 + 2^{j_a}/8`, a rational majorant of the bound `G` of the subgradient. -/
noncomputable def triGu (d : ℕ) : ℝ := (Nat.sqrt (8 * d * triKg d) : ℝ) + 2 + 2 ^ triJa d / 8

/-- `B_v`: the grid `2^{-B_v}` of the rounded subgradient, with `β_up Δ ≤ e_lo/8`. -/
noncomputable def triBv (d : ℕ) : ℕ := Nat.clog 4 ⌈64 * (d + 1) ^ 2 * triD2 d / triElo d ^ 2⌉₊

/-- `β_up = (d + 1) 2^{-B_v}`, a majorant of the rounding error `(d + d²)^{1/2} 2^{-B_v}`. -/
noncomputable def triBu (d : ℕ) : ℝ := (d + 1) / 2 ^ triBv d

/-- `n`: the horizon `N' = 2^n` for an integer majorant `ℓ` of `log(1/δ')`. -/
noncomputable def triNe (d ℓ : ℕ) : ℕ :=
  Nat.clog 2 ⌈16 * triD2 d * (2 * (3 / 2 * (triGu d + triBu d)) ^ 2 + 4 * triGu d ^ 2 * ℓ) / (9 * triElo d ^ 2)⌉₊

/-- `j_s`: the step `s' = 2^{-j_s}`, the largest power of two with `s'² (G_up + β_up)² N' ≤ Δ²`. -/
noncomputable def triJs (d ℓ : ℕ) : ℕ := Nat.clog 4 ⌈(triGu d + triBu d) ^ 2 * 2 ^ triNe d ℓ / triD2 d⌉₊

/-- The rounding of every coordinate down to the grid `2^{-B_v}`. -/
noncomputable def triRound {d : ℕ} (Bv : ℕ) (v : PgSp d) : PgSp d :=
  WithLp.toLp 2 fun k => (⌊v k * 2 ^ Bv⌋ : ℝ) / 2 ^ Bv

/-- The uniform law on `(0, 1]`. -/
noncomputable abbrev unif01 : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)

/-- The cell of `u ∈ (0, 1]` at `B` bits, `⌈2^B u⌉ - 1`: the integer that a block of `B` coins reads. -/
noncomputable def gsCell (B : ℕ) (u : ℝ) : ℕ := (⌈(2 : ℝ) ^ B * u⌉ - 1).toNat

/-- The cosine output of Box and Muller at `(u, w)`. -/
noncomputable def bmCos (p : ℝ × ℝ) : ℝ := Real.sqrt (-2 * Real.log p.1) * Real.cos (2 * Real.pi * p.2)

/-- One vector draw of the sampler: coordinate `i` is the cosine output of Procedure BM-INT on the blocks `UW i`. -/
noncomputable def gsVec (d B : ℕ) (UW : Fin d → ℕ × ℕ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i => ((gsSpec B (UW i).1 (UW i).2).1 : ℝ) / 2 ^ (2 * gsm_prec B)

/-- The coupling space of one vector draw: `d` independent uniform pairs on `(0, 1]²`. -/
noncomputable def gsOmega (d : ℕ) : Measure (Fin d → ℝ × ℝ) := Measure.pi fun _ => unif01.prod unif01

/-- The cells of a point of the coupling space. -/
noncomputable def gsCells (d B : ℕ) (ω : Fin d → ℝ × ℝ) : Fin d → ℕ × ℕ :=
  fun i => (gsCell B (ω i).1, gsCell B (ω i).2)

/-- The tolerance of one coordinate: `2^{-B}` (the theorem BM-INT) plus the Box-Muller rounding
`2^{1-B/2} + 2π B^{1/2} 2^{-B}`
(`boxMuller_coupling`). -/
noncomputable def gsEps (B : ℕ) : ℝ :=
  1 / 2 ^ B + ((2 : ℝ) ^ (1 - (B : ℝ) / 2) + 2 * Real.pi * Real.sqrt B * (2 : ℝ) ^ (-(B : ℝ)))

/-- The law of one vector draw of the sampler at `B` bits per coin block. -/
noncomputable def gsLaw (d B : ℕ) : Measure (EuclideanSpace ℝ (Fin d)) :=
  (gsOmega d).map fun ω => gsVec d B (gsCells d B ω)

section

variable {d : ℕ}

/-- The cube `{y | |y_i - c_i| ≤ s for every i}`. -/
def triCube (c : EuclideanSpace ℝ (Fin d)) (s : ℝ) : Set (EuclideanSpace ℝ (Fin d)) := {y | ∀ i, |y i - c i| ≤ s}

/-- The rows of `K ∩ triCube c s`: the rows `A` of `K`, then `e_i` and `-e_i`. -/
noncomputable def triRowsA {m : ℕ} (A : Fin m → EuclideanSpace ℝ (Fin d)) : Fin (m + (d + d)) → EuclideanSpace ℝ (Fin d) :=
  Fin.append A (Fin.append (fun i => EuclideanSpace.single i 1) (fun i => -EuclideanSpace.single i 1))

/-- The right-hand sides of `K ∩ triCube c s`: `b`, then `c_i + s` and `s - c_i`. -/
noncomputable def triRowsB {m : ℕ} (b : Fin m → ℝ) (c : EuclideanSpace ℝ (Fin d)) (s : ℝ) : Fin (m + (d + d)) → ℝ :=
  Fin.append b (Fin.append (fun i => c i + s) (fun i => s - c i))

/-- The number of stages `max 1 ⌈log₂ ⌈R0/r0⌉⌉`. -/
noncomputable def triMst (r0 R0 : ℝ) : ℕ := max 1 (Nat.clog 2 ⌈R0 / r0⌉₊)

/-- Draw `t` of a coin stream `x`: coordinate `i` reads the blocks `2 (t d + i)` and `2 (t d + i) + 1` of `B` coins. -/
noncomputable def triDraw (d B : ℕ) (x : ℕ → Bool) (t : ℕ) : EuclideanSpace ℝ (Fin d) :=
  gsVec d B fun i => ((AdversarialBco.BitRAM.readCoins x (2 * (t * d + i) * B) B).toNat,
    (AdversarialBco.BitRAM.readCoins x ((2 * (t * d + i) + 1) * B) B).toNat)

/-- The coin of stage `j`, place `k`, in the stream of the procedure: `j L + k` for the `mst` stages of `L` coins,
the rest after them. -/
def triLay (mst L : ℕ) (p : ℕ × ℕ) : ℕ := if p.1 < mst ∧ p.2 < L then p.1 * L + p.2 else mst * L + Nat.pair p.1 p.2

end

instance tri_isProb_coinLaw : IsProbabilityMeasure AdversarialBco.BitRAM.coinLaw := by
  constructor
  simp only [AdversarialBco.BitRAM.coinLaw, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel] <;> norm_num

instance tri_isProb_coinStream : IsProbabilityMeasure AdversarialBco.BitRAM.coinStream := by
  unfold AdversarialBco.BitRAM.coinStream; infer_instance

instance tri_isProb_unif01 : IsProbabilityMeasure unif01 := by
  constructor; simp

instance tri_isProb_gsLaw (d B : ℕ) : IsProbabilityMeasure (gsLaw d B) := by
  unfold gsLaw gsOmega; infer_instance

end AdversarialBco.Bit

namespace AdversarialBco.Bit.Aux_gs_sure


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.gs_sure (d B : ℕ) (hB : 8 ≤ B) (UW : Fin d → ℕ × ℕ)
    (hUW : ∀ i, (UW i).1 < 2 ^ B ∧ (UW i).2 < 2 ^ B) : ‖gsVec d B UW‖ ≤ Real.sqrt (2 * d * B) := by
  have hcomp : ∀ i, |gsVec d B UW i| ≤ Real.sqrt (2 * B) := by
    intro i
    have hi := hUW i
    have hspec := gsSpec_err B (UW i).1 (UW i).2 hB hi.1 hi.2
    simpa [gsVec] using hspec.2.2.1
  have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * (B : ℝ)) := Real.sqrt_nonneg _
  have hnorm_sq : ‖gsVec d B UW‖ ^ 2 ≤ 2 * (d : ℝ) * (B : ℝ) := by
    calc
      ‖gsVec d B UW‖ ^ 2 = ∑ i : Fin d, ‖(gsVec d B UW).ofLp i‖ ^ 2 := by
        simpa using EuclideanSpace.norm_sq_eq (gsVec d B UW)
      _ = ∑ i : Fin d, |gsVec d B UW i| ^ 2 := by simp
      _ ≤ ∑ i : Fin d, (Real.sqrt (2 * B)) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hi := hcomp i
        have habs_nonneg : 0 ≤ |gsVec d B UW i| := abs_nonneg _
        have hsq : |gsVec d B UW i| ^ 2 ≤ (Real.sqrt (2 * B)) ^ 2 := by
          calc
            |gsVec d B UW i| ^ 2 = |gsVec d B UW i| * |gsVec d B UW i| := by ring
            _ ≤ Real.sqrt (2 * B) * Real.sqrt (2 * B) :=
              mul_le_mul hi hi habs_nonneg hsqrt_nonneg
            _ = (Real.sqrt (2 * B)) ^ 2 := by ring
        exact hsq
      _ = ∑ i : Fin d, (2 * (B : ℝ)) := by
        have hnonneg : 0 ≤ (2 : ℝ) * (B : ℝ) := by positivity
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Real.sq_sqrt hnonneg]
      _ = (d : ℝ) * (2 * (B : ℝ)) := by simp
      _ = 2 * (d : ℝ) * (B : ℝ) := by ring
  exact Real.le_sqrt_of_sq_le hnorm_sq

end AdversarialBco.Bit.Aux_gs_sure

namespace AdversarialBco.Bit.Aux_gs_cell_law


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.gs_cell_law (B n : ℕ) :
    unif01.map (gsCell B) {n} = if n < 2 ^ B then (2⁻¹ : ℝ≥0∞) ^ B else 0 := by
  -- gsCell B is measurable (composition of measurable functions, ℤ has DiscreteMeasurableSpace)
  have h_meas_gsCell : Measurable (gsCell B) := by
    unfold gsCell
    have h1 : Measurable (fun u : ℝ => (2 : ℝ) ^ B * u) :=
      measurable_const.mul measurable_id
    have h2 : Measurable (fun x : ℝ => ⌈x⌉) := Int.measurable_ceil
    have h3 : Measurable (fun z : ℤ => z - 1) := measurable_sub_const 1
    have h4 : Measurable (Int.toNat : ℤ → ℕ) := Measurable.of_discrete
    have h_comp1 : Measurable (fun u : ℝ => ⌈(2 : ℝ) ^ B * u⌉) :=
      Measurable.comp h2 h1
    have h_comp2 : Measurable (fun u : ℝ => ⌈(2 : ℝ) ^ B * u⌉ - 1) :=
      Measurable.comp h3 h_comp1
    exact Measurable.comp h4 h_comp2
  -- Apply Measure.map_apply to express the LHS as unif01 (gsCell B ⁻¹' {n})
  rw [Measure.map_apply h_meas_gsCell (measurableSet_singleton n)]
  -- Now goal: unif01 (gsCell B ⁻¹' {n}) = if n < 2 ^ B then (2⁻¹ : ℝ≥0∞) ^ B else 0
  -- unif01 = volume.restrict (Ioc 0 1), so unif01 s = volume (s ∩ Ioc 0 1)
  -- Similarly, unif01.map f {j} = unif01 (f ⁻¹' {j}) = volume ((f ⁻¹' {j}) ∩ Ioc 0 1)
  -- Key lemma: on Ioc 0 1, gsCell B u = n ↔ ⌈(2:ℝ)^B * u⌉ = (n:ℤ)+1
  have h_preimage_eq : (gsCell B ⁻¹' {n}) ∩ Set.Ioc (0 : ℝ) 1 =
      ((fun u : ℝ => ⌈(2 : ℝ) ^ B * u⌉) ⁻¹' {(n : ℤ) + 1}) ∩ Set.Ioc (0 : ℝ) 1 := by
    ext u
    constructor
    · intro ⟨h, hu⟩
      have h_preimage : gsCell B u ∈ {n} := Set.mem_preimage.mp h
      have h_gsCell_eq : gsCell B u = n := Set.mem_singleton_iff.mp h_preimage
      have hu_pos : 0 < u := (Set.mem_Ioc.mp hu).1
      have hpos : 0 < (2 : ℝ) ^ B * u := by
        have hpow : 0 < (2 : ℝ) ^ B := pow_pos (by norm_num) B
        exact mul_pos hpow hu_pos
      have hceil_pos : 1 ≤ ⌈(2 : ℝ) ^ B * u⌉ := by
        have hceil_pos' : 0 < ⌈(2 : ℝ) ^ B * u⌉ := Int.ceil_pos.mpr hpos
        omega
      have hsub_nonneg : 0 ≤ ⌈(2 : ℝ) ^ B * u⌉ - 1 := by omega
      have h_gsCell_val : gsCell B u = (⌈(2 : ℝ) ^ B * u⌉ - 1).toNat := rfl
      rw [h_gsCell_val] at h_gsCell_eq
      -- From h_gsCell_eq: (⌈...⌉ - 1).toNat = n (as ℕ)
      -- Since ⌈...⌉ - 1 ≥ 0, toNat is the identity
      have h_int_eq : (⌈(2 : ℝ) ^ B * u⌉ - 1 : ℤ) = (n : ℤ) := by
        have h_val : ((⌈(2 : ℝ) ^ B * u⌉ - 1).toNat : ℤ) = ⌈(2 : ℝ) ^ B * u⌉ - 1 :=
          Int.toNat_of_nonneg hsub_nonneg
        have h_nat : ((⌈(2 : ℝ) ^ B * u⌉ - 1).toNat : ℤ) = (n : ℤ) := by rw [h_gsCell_eq]
        rw [h_val] at h_nat
        exact h_nat
      -- So ⌈(2:ℝ)^B * u⌉ = (n:ℤ) + 1
      have h_ceil_eq : ⌈(2 : ℝ) ^ B * u⌉ = (n : ℤ) + 1 := by omega
      exact ⟨by rw [Set.mem_preimage, Set.mem_singleton_iff, h_ceil_eq], hu⟩
    · intro ⟨h, hu⟩
      -- h : u ∈ (fun u => ⌈(2:ℝ)^B * u⌉) ⁻¹' {(n:ℤ)+1}
      have h_ceil_eq : ⌈(2 : ℝ) ^ B * u⌉ = (n : ℤ) + 1 := by
        have : ⌈(2 : ℝ) ^ B * u⌉ ∈ ({(n : ℤ) + 1} : Set ℤ) := Set.mem_preimage.mp h
        exact Set.mem_singleton_iff.mp this
      have hu_pos : 0 < u := (Set.mem_Ioc.mp hu).1
      have hpos : 0 < (2 : ℝ) ^ B * u := by
        have hpow : 0 < (2 : ℝ) ^ B := pow_pos (by norm_num) B
        exact mul_pos hpow hu_pos
      have hceil_pos : 1 ≤ ⌈(2 : ℝ) ^ B * u⌉ := by
        have hceil_pos' : 0 < ⌈(2 : ℝ) ^ B * u⌉ := Int.ceil_pos.mpr hpos
        omega
      -- From h_ceil_eq: ⌈(2:ℝ)^B * u⌉ = (n:ℤ)+1
      have h_sub_eq : ⌈(2 : ℝ) ^ B * u⌉ - 1 = (n : ℤ) := by omega
      have hsub_nonneg : 0 ≤ ⌈(2 : ℝ) ^ B * u⌉ - 1 := by omega
      -- Need to show: gsCell B u = n
      have h_gsCell_val : gsCell B u = (⌈(2 : ℝ) ^ B * u⌉ - 1).toNat := rfl
      have h_toNat_eq : (⌈(2 : ℝ) ^ B * u⌉ - 1).toNat = n := by
        have h_int : ((⌈(2 : ℝ) ^ B * u⌉ - 1).toNat : ℤ) = (n : ℤ) := by
          rw [Int.toNat_of_nonneg hsub_nonneg, h_sub_eq]
        exact Nat.cast_inj.mp h_int
      have h_preimage : gsCell B u ∈ ({n} : Set ℕ) := by
        rw [Set.mem_singleton_iff, h_gsCell_val, h_toNat_eq]
      exact ⟨h_preimage, hu⟩
  -- unif01 = volume.restrict (Ioc 0 1), so unif01 s = volume (s ∩ Ioc 0 1)
  -- Using h_preimage_eq, the two preimages have the same intersection with Ioc 0 1
  have h_unif01_eq : unif01 (gsCell B ⁻¹' {n}) = unif01 ((fun u : ℝ => ⌈(2 : ℝ) ^ B * u⌉) ⁻¹' {(n : ℤ) + 1}) := by
    have h1 : unif01 (gsCell B ⁻¹' {n}) = volume ((gsCell B ⁻¹' {n}) ∩ Set.Ioc (0 : ℝ) 1) := by
      simpa [unif01] using Measure.restrict_apply (measurableSet_Ioc) (μ := volume) (s := Set.Ioc (0 : ℝ) 1) (t := gsCell B ⁻¹' {n})
    have h2 : volume (((fun u : ℝ => ⌈(2 : ℝ) ^ B * u⌉) ⁻¹' {(n : ℤ) + 1}) ∩ Set.Ioc (0 : ℝ) 1) = unif01 ((fun u : ℝ => ⌈(2 : ℝ) ^ B * u⌉) ⁻¹' {(n : ℤ) + 1}) := by
      simpa [unif01] using (Measure.restrict_apply (measurableSet_Ioc) (μ := volume) (s := Set.Ioc (0 : ℝ) 1) (t := (fun u : ℝ => ⌈(2 : ℝ) ^ B * u⌉) ⁻¹' {(n : ℤ) + 1})).symm
    calc
      unif01 (gsCell B ⁻¹' {n}) = volume ((gsCell B ⁻¹' {n}) ∩ Set.Ioc (0 : ℝ) 1) := h1
      _ = volume (((fun u : ℝ => ⌈(2 : ℝ) ^ B * u⌉) ⁻¹' {(n : ℤ) + 1}) ∩ Set.Ioc (0 : ℝ) 1) := by rw [h_preimage_eq]
      _ = unif01 ((fun u : ℝ => ⌈(2 : ℝ) ^ B * u⌉) ⁻¹' {(n : ℤ) + 1}) := by rw [h2]
  rw [h_unif01_eq]
  -- Now use Measure.map_apply for the ceil function
  have h_meas_ceil : Measurable (fun u : ℝ => ⌈(2 : ℝ) ^ B * u⌉) := by
    have h1 : Measurable (fun u : ℝ => (2 : ℝ) ^ B * u) :=
      measurable_const.mul measurable_id
    have h2 : Measurable (fun x : ℝ => ⌈x⌉) := Int.measurable_ceil
    exact Measurable.comp h2 h1
  have h_map_ceil := Measure.map_apply (μ := unif01) h_meas_ceil (measurableSet_singleton (x := ((n : ℤ) + 1 : ℤ)))
  -- h_map_ceil: (unif01.map (fun u => ⌈(2:ℝ)^B * u⌉)) {(n:ℤ)+1} = unif01 ((fun u => ⌈(2:ℝ)^B * u⌉) ⁻¹' {(n:ℤ)+1})
  -- We want the reverse direction
  rw [← h_map_ceil]
  -- Now goal: (unif01.map (fun u => ⌈(2:ℝ)^B * u⌉)) {(n:ℤ)+1} = if n < 2 ^ B then (2⁻¹ : ℝ≥0∞) ^ B else 0
  -- This is exactly dyadic_law with j = (n:ℤ)+1
  rw [dyadic_law B ((n : ℤ) + 1)]
  -- Now goal: (if 1 ≤ (n:ℤ)+1 ∧ (n:ℤ)+1 ≤ 2 ^ B then ENNReal.ofReal ((2:ℝ) ^ (-(B:ℝ))) else 0) =
  --            if n < 2 ^ B then (2⁻¹ : ℝ≥0∞) ^ B else 0
  -- Need to rewrite the condition 1 ≤ (n:ℤ)+1 ∧ (n:ℤ)+1 ≤ 2 ^ B to n < 2 ^ B
  -- And convert ENNReal.ofReal ((2:ℝ) ^ (-(B:ℝ))) to (2⁻¹ : ℝ≥0∞) ^ B
  -- First, rewrite the condition
  have h_cond : (1 ≤ (n : ℤ) + 1 ∧ (n : ℤ) + 1 ≤ 2 ^ B) ↔ n < 2 ^ B := by
    constructor
    · intro ⟨h1, h2⟩
      have h_n_lt : (n : ℤ) < (2 ^ B : ℤ) := by omega
      exact_mod_cast h_n_lt
    · intro h
      have h_n_lt : (n : ℤ) < (2 ^ B : ℤ) := by exact_mod_cast h
      constructor
      · have : 0 ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
        omega
      · omega
  -- Now rewrite the if condition using h_cond
  by_cases h_n_lt : n < 2 ^ B
  · -- n < 2^B: both sides should be the same
    rw [if_pos h_n_lt]
    -- LHS: (if 1 ≤ (n:ℤ)+1 ∧ (n:ℤ)+1 ≤ 2 ^ B then ... else 0)
    -- Since n < 2^B, the condition holds, so we take the then branch
    have h_cond_true : 1 ≤ (n : ℤ) + 1 ∧ (n : ℤ) + 1 ≤ 2 ^ B := by
      -- From h_n_lt: n < 2^B, we need to show the condition
      have h_n_lt_int : (n : ℤ) < (2 ^ B : ℤ) := by exact_mod_cast h_n_lt
      constructor
      · have : 0 ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
        omega
      · omega
    rw [if_pos h_cond_true]
    -- Now goal: ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ))) = (2⁻¹ : ℝ≥0∞) ^ B
    -- Convert using the lemmas
    calc
      ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ))) = ENNReal.ofReal (((2 : ℝ) ^ (B : ℝ))⁻¹) := by
        rw [Real.rpow_neg (show 0 ≤ (2 : ℝ) from by norm_num) (B : ℝ)]
      _ = (ENNReal.ofReal ((2 : ℝ) ^ (B : ℝ)))⁻¹ := by
        rw [ENNReal.ofReal_inv_of_pos (by
          -- (2:ℝ)^(B:ℝ) > 0
          exact Real.rpow_pos_of_pos (by norm_num) (B : ℝ))]
      _ = (ENNReal.ofReal ((2 : ℝ) ^ B))⁻¹ := by
        rw [Real.rpow_natCast (2 : ℝ) B]
      _ = (ENNReal.ofReal (2 : ℝ) ^ B)⁻¹ := by
        rw [ENNReal.ofReal_pow (by norm_num : 0 ≤ (2 : ℝ)) B]
      _ = ((2 : ℝ≥0∞) ^ B)⁻¹ := by
        have h : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
        rw [h]
      _ = (2⁻¹ : ℝ≥0∞) ^ B := by
        rw [← ENNReal.inv_pow]
  · -- n ≥ 2^B: both sides should be 0
    rw [if_neg h_n_lt]
    -- LHS: (if 1 ≤ (n:ℤ)+1 ∧ (n:ℤ)+1 ≤ 2 ^ B then ... else 0)
    -- Since n ≥ 2^B, the condition fails
    have h_cond_false : ¬ (1 ≤ (n : ℤ) + 1 ∧ (n : ℤ) + 1 ≤ 2 ^ B) :=
      mt h_cond.mp h_n_lt
    rw [if_neg h_cond_false]

end AdversarialBco.Bit.Aux_gs_cell_law

namespace AdversarialBco.Bit.Aux_gs_coin_block


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

section
open AdversarialBco.BitRAM

/-- `readCoins cs c k` is nonnegative. -/
theorem gcb_readCoins_nonneg (cs : ℕ → Bool) (c k : ℕ) : 0 ≤ readCoins cs c k := by
  induction' k with k ih
  · rfl
  · dsimp [readCoins]
    have : 0 ≤ (if cs (c + k) then (1 : ℤ) else 0) := by
      split <;> norm_num
    nlinarith

/-- `readCoins cs c k` is bounded above by `2^k - 1`. -/
theorem gcb_readCoins_lt_two_pow (cs : ℕ → Bool) (c k : ℕ) : readCoins cs c k < (2 : ℤ) ^ k := by
  induction' k with k ih
  · dsimp [readCoins]; norm_num
  · dsimp [readCoins]
    have hbit : (if cs (c + k) then (1 : ℤ) else 0) ≤ 1 := by
      split <;> norm_num
    have h2k : (2 : ℤ) ^ k * 2 = (2 : ℤ) ^ (k + 1) := by ring
    nlinarith

/-- `readCoins` is measurable in `cs`. -/
theorem gcb_measurable_readCoins (c k : ℕ) : Measurable (fun (cs : ℕ → Bool) => readCoins cs c k) := by
  induction' k with k ih
  · -- k = 0: readCoins cs c 0 = 0
    have : (fun (cs : ℕ → Bool) => readCoins cs c 0) = fun _ => (0 : ℤ) := by
      ext cs; rfl
    rw [this]
    exact measurable_const
  · -- k+1: readCoins cs c (k+1) = 2 * readCoins cs c k + (if cs (c+k) then 1 else 0)
    have h_eq : (fun (cs : ℕ → Bool) => readCoins cs c (k + 1)) =
        (fun cs => (2 : ℤ) * readCoins cs c k + (if cs (c + k) then (1 : ℤ) else 0)) := by
      ext cs; rfl
    rw [h_eq]
    refine Measurable.add (Measurable.mul measurable_const ih) ?_
    refine Measurable.ite ?_ measurable_const measurable_const
    -- the set {cs | cs (c+k) = true} is measurable
    have hmeas : MeasurableSet {cs : ℕ → Bool | cs (c + k)} := by
      have : {cs : ℕ → Bool | cs (c + k)} = (fun (f : ℕ → Bool) => f (c + k)) ⁻¹' {true} := by
        ext cs; simp
      rw [this]
      exact (measurable_pi_apply (c + k)) (measurableSet_singleton _)
    exact hmeas

/-- `(readCoins cs c B).toNat` is measurable as a function to `ℕ`. -/
theorem gcb_measurable_toNat_readCoins (c B : ℕ) :
    Measurable (fun (cs : ℕ → Bool) => (readCoins cs c B).toNat) := by
  -- The function is ℤ → ℕ via Int.toNat, composed with the measurable ℤ-valued function
  have : (fun (cs : ℕ → Bool) => (readCoins cs c B).toNat) =
      Int.toNat ∘ (fun (cs : ℕ → Bool) => readCoins cs c B) := by
    ext cs; rfl
  rw [this]
  refine Measurable.comp ?_ (gcb_measurable_readCoins c B)
  -- Int.toNat is measurable since ℕ has discrete σ-algebra
  exact Measurable.of_discrete

end

theorem _root_.AdversarialBco.Bit.gs_coin_block (B c : ℕ) :
    AdversarialBco.BitRAM.coinStream.map (fun cs => (AdversarialBco.BitRAM.readCoins cs c B).toNat) =
      unif01.map (gsCell B) := by
  refine Measure.ext_of_singleton fun n => ?_
  have h_meas_left : Measurable (fun (cs : ℕ → Bool) => (AdversarialBco.BitRAM.readCoins cs c B).toNat) :=
    gcb_measurable_toNat_readCoins c B
  -- Left side: coinStream.map ... {n} = coinStream {cs | (readCoins cs c B).toNat = n}
  rw [Measure.map_apply h_meas_left (MeasurableSet.singleton n)]
  -- Right side: use gs_cell_law which gives exactly the measure of the singleton
  rw [gs_cell_law B n]
  by_cases hn : n < 2 ^ B
  · -- Case n < 2^B: both sides equal (2⁻¹ : ℝ≥0∞) ^ B
    rw [if_pos hn]
    -- Goal: coinStream ((fun cs => ...) ⁻¹' {n}) = (2⁻¹ : ℝ≥0∞) ^ B
    -- The preimage: since readCoins cs c B is nonnegative and < 2^B, toNat = n ↔ readCoins = n
    have h_preimage : (fun (cs : ℕ → Bool) => (AdversarialBco.BitRAM.readCoins cs c B).toNat) ⁻¹' {n} =
        {cs | AdversarialBco.BitRAM.readCoins cs c B = (n : ℤ)} := by
      ext cs
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h
        have h_nonneg : 0 ≤ AdversarialBco.BitRAM.readCoins cs c B :=
          gcb_readCoins_nonneg cs c B
        have h_toNat_eq : (AdversarialBco.BitRAM.readCoins cs c B).toNat = n := h
        have h_eq : (AdversarialBco.BitRAM.readCoins cs c B) = ((AdversarialBco.BitRAM.readCoins cs c B).toNat : ℤ) := by
          simpa [Int.toNat_of_nonneg h_nonneg]
        have : (AdversarialBco.BitRAM.readCoins cs c B) = (n : ℤ) := by
          rw [h_eq, h_toNat_eq]
        simpa [this]
      · intro h
        have h_nonneg : 0 ≤ AdversarialBco.BitRAM.readCoins cs c B :=
          gcb_readCoins_nonneg cs c B
        have h_eq : AdversarialBco.BitRAM.readCoins cs c B = (n : ℤ) := h
        calc
          (AdversarialBco.BitRAM.readCoins cs c B).toNat = (n : ℤ).toNat := by rw [h_eq]
          _ = n := by simp
    rw [h_preimage]
    -- Now use gsm_readCoins_law
    have hz0 : 0 ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    have hz : (n : ℤ) < (2 : ℤ) ^ B := by
      exact_mod_cast hn
    rw [gsm_readCoins_law c B (n : ℤ) hz0 hz]
  · -- Case ¬ n < 2^B, i.e., n ≥ 2^B: both sides equal 0
    rw [if_neg (by omega)]
    -- Goal: coinStream ((fun cs => ...) ⁻¹' {n}) = 0
    -- Since readCoins cs c B < 2^B, its toNat is < 2^B, so cannot equal n
    have h_empty : (fun (cs : ℕ → Bool) => (AdversarialBco.BitRAM.readCoins cs c B).toNat) ⁻¹' {n} = ∅ := by
      ext cs
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      have h_lt : AdversarialBco.BitRAM.readCoins cs c B < (2 : ℤ) ^ B :=
        gcb_readCoins_lt_two_pow cs c B
      have h_nonneg : 0 ≤ AdversarialBco.BitRAM.readCoins cs c B :=
        gcb_readCoins_nonneg cs c B
      have hpos : 0 < (2 : ℤ) ^ B := by
        apply pow_pos (by norm_num) B
      have h_lt' : (AdversarialBco.BitRAM.readCoins cs c B).toNat < ((2 : ℤ) ^ B).toNat := by
        -- Int.toNat_lt_toNat requires 0 < m
        exact ((Int.toNat_lt_toNat hpos).mpr h_lt)
      have h_toNat_lt : (AdversarialBco.BitRAM.readCoins cs c B).toNat < 2 ^ B := by
        have : ((2 : ℤ) ^ B).toNat = 2 ^ B := by norm_cast
        simpa [this] using h_lt'
      have hn' : 2 ^ B ≤ n := by omega
      omega
    rw [h_empty]
    simp

end AdversarialBco.Bit.Aux_gs_coin_block

namespace AdversarialBco.Bit.Aux_gs_g_law


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.gs_g_law (d : ℕ) :
    (gsOmega d).map (fun ω => WithLp.toLp 2 fun i => bmCos (ω i)) = stdGaussian (EuclideanSpace ℝ (Fin d)) := by
  rcases boxMuller_law with ⟨h_cos, h_sin⟩
  dsimp [gsOmega]
  have h_meas_toLp : Measurable (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) :=
    WithLp.measurable_toLp 2 (Fin d → ℝ)
  have h_meas_bmCos : Measurable bmCos := by
    unfold bmCos
    fun_prop
  have h_meas_f : Measurable (fun (ω : Fin d → ℝ × ℝ) (i : Fin d) => bmCos (ω i)) := by
    refine Measurable.of_eval ?_
    intro i
    exact h_meas_bmCos.comp (measurable_pi_apply i)
  calc
    (Measure.pi (fun _ : Fin d => unif01.prod unif01)).map (fun ω => WithLp.toLp 2 fun i => bmCos (ω i))
        = ((Measure.pi (fun _ : Fin d => unif01.prod unif01)).map (fun ω i => bmCos (ω i))).map (WithLp.toLp 2) := by
      exact (Measure.map_map h_meas_toLp h_meas_f).symm
    _ = (Measure.pi (fun i : Fin d => (unif01.prod unif01).map bmCos)).map (WithLp.toLp 2) := by
      rw [MeasureTheory.Measure.pi_map_pi]
      intro i
      exact h_meas_bmCos.aemeasurable
    _ = (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map (WithLp.toLp 2) := by
      unfold bmCos
      rw [h_cos]
    _ = stdGaussian (EuclideanSpace ℝ (Fin d)) := by
      rw [ProbabilityTheory.map_pi_eq_stdGaussian]

end AdversarialBco.Bit.Aux_gs_g_law

namespace AdversarialBco.Bit.Aux_tri_par_box


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_par_box (d : ℕ) (hd : 1 ≤ d) :
    1 ≤ triRa d ∧ 1.05 * triRa d ≤ triRh d ∧ pgKappa * triRa d ≤ triR d ∧ 0 < triA d ∧
      triA d ≤ pgTmin d (triRa d) ∧ triA d ≤ 1 ∧ 1 ≤ triB d ∧ pgLD (triRa d) ≤ triB d := by
  have hs4 : 4 ≤ triS d := (Nat.find_spec (pg_par_exists d)).1
  have hL10 : 10 ≤ triLa (triS d) := by
    unfold triLa
    have : 16 ≤ triS d ^ 2 := by nlinarith
    omega
  obtain ⟨hL1, hLLh⟩ := pg_par_c (triS d) hs4
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) < triS d := by exact_mod_cast (show 0 < triS d by omega)
  have hds : (0 : ℝ) < 9 * d * triS d := by positivity
  have hja : (9 * d * triS d : ℝ) ≤ 2 ^ triJa d := by
    have := Nat.le_pow_clog (by norm_num : 1 < 2) (9 * d * triS d)
    unfold triJa
    exact_mod_cast this
  obtain ⟨-, hk, hld, hinv, hinv1, hb1⟩ := sp_box_par (triLa (triS d)) (triJa d) d (triS d) hL10 hds hja
  have hpow1 : (2 : ℝ) ≤ 2 ^ triLa (triS d) := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ triLa (triS d) := pow_le_pow_right₀ (by norm_num) (by unfold triLa; exact hL1)
  have hpowh : 2 * (2 : ℝ) ^ triLa (triS d) ≤ 2 ^ triLh (triS d) := by
    rw [← pow_succ']
    exact pow_le_pow_right₀ (by norm_num) (by unfold triLa triLh; omega)
  have hlam : pgLam (triRa d) ≤ triS d := by
    unfold pgLam triRa
    rw [show (1 : ℝ) + (2 ^ triLa (triS d) - 1) = 2 ^ triLa (triS d) by ring, Real.log_pow]
    calc Real.sqrt (2 * ((triLa (triS d) : ℕ) * Real.log 2)) ≤ Real.sqrt ((triS d : ℝ) ^ 2) := by
          apply Real.sqrt_le_sqrt
          have := pg_par_lam_a (triS d)
          unfold triLa
          linarith
      _ = triS d := Real.sqrt_sq hs0.le
  have hlam0 : 0 < pgLam (triRa d) := by
    unfold pgLam triRa
    apply Real.sqrt_pos.2
    have : (1 : ℝ) < 1 + (2 ^ triLa (triS d) - 1) := by linarith
    have := Real.log_pos this
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold triRa; linarith
  · unfold triRa triRh; nlinarith
  · unfold triRa triR pgKappa; exact hk
  · unfold triA; positivity
  · unfold triA pgTmin
    rw [one_div]
    refine hinv.trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    have := mul_le_mul_of_nonneg_left hlam (by positivity : (0 : ℝ) ≤ 9 * d)
    exact this
  · unfold triA; rw [one_div]; exact hinv1
  · unfold triB; exact hb1
  · unfold pgLD triRa triB pgKappa pgPB
    calc (1 / 8 : ℝ) * (1254 / 1000) * (2 ^ triLa (triS d) - 1) = 627 / 4000 * (2 ^ triLa (triS d) - 1) := by ring
      _ ≤ _ := hld

end AdversarialBco.Bit.Aux_tri_par_box

namespace AdversarialBco.Bit.Aux_tri_par_Gu


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_par_Gu (d : ℕ) (hd : 1 ≤ d) :
    0 ≤ triGu d ∧
      1 + (Real.sqrt (8 * d * triKg d) + pgKappa / (Real.sqrt d * triA d)) ^ 2 ≤ triGu d ^ 2 := by
  have hdpos : (0 : ℝ) < d := by
    have h : 0 < d := by omega
    exact mod_cast h
  have hsqrt_d_ge_one : (1 : ℝ) ≤ Real.sqrt (d : ℝ) := by
    calc
      (1 : ℝ) = Real.sqrt ((1 : ℕ) : ℝ) := by norm_num
      _ ≤ Real.sqrt (d : ℝ) := Real.sqrt_le_sqrt (by exact mod_cast hd)
  have hsqrt_d_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdpos
  have htriGu_nonneg : 0 ≤ triGu d := by
    unfold triGu
    positivity
  set M := Real.sqrt (8 * (d : ℝ) * (triKg d : ℝ)) with hM
  set c := pgKappa / (Real.sqrt (d : ℝ) * triA d) with hc
  have hM_nonneg : 0 ≤ M := Real.sqrt_nonneg _
  have hc_nonneg : 0 ≤ c := by
    rw [hc]
    have hpgKappa_nonneg : 0 ≤ pgKappa := by unfold pgKappa; norm_num
    have htriA_nonneg : 0 ≤ triA d := by
      unfold triA
      positivity
    positivity
  have hsum_nonneg : 0 ≤ M + c := by nlinarith
  have hM_bound : M ≤ (Nat.sqrt (8 * d * triKg d) : ℝ) + 1 := by
    rw [hM]
    have hpos : 0 ≤ (8 * (d : ℝ) * (triKg d : ℝ)) := by positivity
    have hpos_sqrt : 0 < (Nat.sqrt (8 * d * triKg d) : ℝ) + 1 := by
      have : 0 ≤ (Nat.sqrt (8 * d * triKg d) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have h_lt_nat : (8 * d * triKg d : ℕ) < ((Nat.sqrt (8 * d * triKg d) : ℕ) + 1) ^ 2 := by
      -- Nat.lt_succ_sqrt gives n < (Nat.sqrt n).succ * (Nat.sqrt n).succ = (Nat.sqrt n + 1)^2
      have h := Nat.lt_succ_sqrt (8 * d * triKg d)
      -- h : 8*d*triKg d < (Nat.sqrt (8*d*triKg d)).succ * (Nat.sqrt (8*d*triKg d)).succ
      -- We need to rewrite succ * succ as (sqrt + 1)^2
      simpa [pow_two, add_comm] using h
    have h_lt_real : (8 * (d : ℝ) * (triKg d : ℝ)) < (((Nat.sqrt (8 * d * triKg d) : ℕ) + 1 : ℝ)) ^ 2 := by
      exact mod_cast h_lt_nat
    have h_lt : Real.sqrt (8 * (d : ℝ) * (triKg d : ℝ)) < (Nat.sqrt (8 * d * triKg d) : ℝ) + 1 :=
      (Real.sqrt_lt' hpos_sqrt).mpr h_lt_real
    exact le_of_lt h_lt
  have hc_bound : c ≤ (2 ^ triJa d) / 8 := by
    rw [hc]
    unfold pgKappa triA
    have hpow_pos : 0 < (2 : ℝ) ^ triJa d := by positivity
    have hcalc : (1 / 8 : ℝ) / (Real.sqrt (d : ℝ) * (1 / (2 : ℝ) ^ triJa d)) = ((2 : ℝ) ^ triJa d) / (8 * Real.sqrt (d : ℝ)) := by
      field_simp [hsqrt_d_pos.ne.symm, hpow_pos.ne.symm]
    rw [hcalc]
    have hineq : ((2 : ℝ) ^ triJa d) / (8 * Real.sqrt (d : ℝ)) ≤ ((2 : ℝ) ^ triJa d) / 8 := by
      have ha : 0 ≤ (2 : ℝ) ^ triJa d := by positivity
      have hden' : 0 < (8 : ℝ) := by norm_num
      have h8le : (8 : ℝ) ≤ 8 * Real.sqrt (d : ℝ) := by
        nlinarith
      exact div_le_div_of_nonneg_left ha hden' h8le
    exact hineq
  have hsum_bound : M + c ≤ triGu d - 1 := by
    unfold triGu
    nlinarith
  have hgoal2 : 1 + (M + c) ^ 2 ≤ triGu d ^ 2 := by
    have hx : M + c ≤ triGu d - 1 := hsum_bound
    have hx' : 1 + (M + c) ≤ triGu d := by nlinarith
    have h_sq : 1 + (M + c) ^ 2 ≤ (1 + (M + c)) ^ 2 := by
      nlinarith
    have h_sq2 : (1 + (M + c)) ^ 2 ≤ triGu d ^ 2 := by
      nlinarith
    nlinarith
  rw [hM, hc]
  exact And.intro htriGu_nonneg hgoal2

end AdversarialBco.Bit.Aux_tri_par_Gu

namespace AdversarialBco.Bit.Aux_tri_round_err


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_round_err {d : ℕ} (Bv : ℕ) (v : PgSp d) :
    ‖triRound Bv v - v‖ ≤ (d + 1) / 2 ^ Bv := by
  have hpos : 0 < (2 : ℝ) ^ Bv := pow_pos (by norm_num) Bv
  have hpos_ne : (2 : ℝ) ^ Bv ≠ 0 := by linarith
  have hcard : Fintype.card (Fin d ⊕ Fin d × Fin d) = d + d * d := by
    simp [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod]
  have hcard_bound : (d + d * d : ℝ) ≤ ((d : ℝ) + 1) ^ 2 := by
    have hd : (d : ℝ) ≥ 0 := by exact mod_cast (Nat.zero_le _)
    nlinarith
  have hcoordinate_bound (k : Fin d ⊕ Fin d × Fin d) : 0 ≤ v k - (triRound Bv v) k ∧ v k - (triRound Bv v) k < ((2 : ℝ) ^ Bv)⁻¹ := by
    dsimp [triRound]
    have hfloor_le : (⌊v k * (2 : ℝ) ^ Bv⌋ : ℝ) ≤ v k * (2 : ℝ) ^ Bv := by
      exact mod_cast Int.floor_le (v k * (2 : ℝ) ^ Bv)
    have hlt_floor_add : v k * (2 : ℝ) ^ Bv < (⌊v k * (2 : ℝ) ^ Bv⌋ : ℝ) + 1 := by
      exact mod_cast Int.lt_floor_add_one (v k * (2 : ℝ) ^ Bv)
    constructor
    · -- 0 ≤ v k - (⌊v k * 2^Bv⌋) / 2^Bv
      have hdiv : (⌊v k * (2 : ℝ) ^ Bv⌋ : ℝ) / (2 : ℝ) ^ Bv ≤ v k := by
        calc
          (⌊v k * (2 : ℝ) ^ Bv⌋ : ℝ) / (2 : ℝ) ^ Bv ≤ (v k * (2 : ℝ) ^ Bv) / (2 : ℝ) ^ Bv :=
            div_le_div_of_nonneg_right hfloor_le (by positivity)
          _ = v k := by field_simp [hpos_ne]
      linarith
    · -- v k - (⌊v k * 2^Bv⌋) / 2^Bv < (2^Bv)⁻¹
      have hdiv : v k < (⌊v k * (2 : ℝ) ^ Bv⌋ : ℝ) / (2 : ℝ) ^ Bv + ((2 : ℝ) ^ Bv)⁻¹ := by
        calc
          v k = (v k * (2 : ℝ) ^ Bv) / (2 : ℝ) ^ Bv := by field_simp [hpos_ne]
          _ < ((⌊v k * (2 : ℝ) ^ Bv⌋ : ℝ) + 1) / (2 : ℝ) ^ Bv :=
            div_lt_div_of_pos_right hlt_floor_add hpos
          _ = (⌊v k * (2 : ℝ) ^ Bv⌋ : ℝ) / (2 : ℝ) ^ Bv + 1 / (2 : ℝ) ^ Bv := by ring
          _ = (⌊v k * (2 : ℝ) ^ Bv⌋ : ℝ) / (2 : ℝ) ^ Bv + ((2 : ℝ) ^ Bv)⁻¹ := by ring
      linarith
  have hsq_sum : ‖triRound Bv v - v‖ ^ 2 ≤ ((d : ℝ) + 1) ^ 2 * (((2 : ℝ) ^ Bv)⁻¹) ^ 2 := by
    have hnorm_sq_eq : ‖triRound Bv v - v‖ ^ 2 = ∑ k : Fin d ⊕ Fin d × Fin d, (v k - (triRound Bv v) k) ^ 2 := by
      rw [EuclideanSpace.norm_eq]
      have h_nonneg_sq : 0 ≤ ∑ i : Fin d ⊕ Fin d × Fin d, ‖(triRound Bv v - v) i‖ ^ 2 := by
        positivity
      rw [Real.sq_sqrt h_nonneg_sq]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h := hcoordinate_bound k
      rcases h with ⟨hle, hlt⟩
      have habs : ‖(triRound Bv v - v) k‖ = v k - (triRound Bv v) k := by
        have hsub : (triRound Bv v - v) k = (triRound Bv v) k - v k := rfl
        rw [hsub]
        have hsub' : (triRound Bv v) k - v k = -(v k - (triRound Bv v) k) := by ring
        rw [hsub', norm_neg, Real.norm_eq_abs, abs_of_nonneg hle]
      rw [habs]
    rw [hnorm_sq_eq]
    calc
      ∑ k : Fin d ⊕ Fin d × Fin d, (v k - (triRound Bv v) k) ^ 2 ≤
          ∑ k : Fin d ⊕ Fin d × Fin d, (((2 : ℝ) ^ Bv)⁻¹) ^ 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        have h := hcoordinate_bound k
        rcases h with ⟨hle, hlt⟩
        have hsq_bound : (v k - (triRound Bv v) k) ^ 2 ≤ (((2 : ℝ) ^ Bv)⁻¹) ^ 2 := by
          nlinarith
        exact hsq_bound
      _ = (Fintype.card (Fin d ⊕ Fin d × Fin d) : ℝ) * (((2 : ℝ) ^ Bv)⁻¹) ^ 2 := by simp
      _ = (d + d * d : ℝ) * (((2 : ℝ) ^ Bv)⁻¹) ^ 2 := by simp [hcard]
      _ ≤ ((d : ℝ) + 1) ^ 2 * (((2 : ℝ) ^ Bv)⁻¹) ^ 2 := by
        nlinarith
  have hnorm_nonneg : 0 ≤ ‖triRound Bv v - v‖ := by positivity
  have htarget_nonneg : 0 ≤ (d + 1 : ℝ) / (2 : ℝ) ^ Bv := by
    have hd : 0 ≤ (d : ℝ) := by exact mod_cast (Nat.zero_le _)
    positivity
  have h_sq_eq : ((d + 1 : ℝ) / (2 : ℝ) ^ Bv) ^ 2 = ((d : ℝ) + 1) ^ 2 * (((2 : ℝ) ^ Bv)⁻¹) ^ 2 := by
    field_simp [hpos_ne]
  nlinarith

end AdversarialBco.Bit.Aux_tri_round_err

namespace AdversarialBco.Bit.Aux_tri_round_meas


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_round_meas {d : ℕ} (Bv : ℕ) : Measurable (triRound (d := d) Bv) := by
  unfold triRound
  refine Measurable.comp (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin d ⊕ Fin d × Fin d => ℝ)).measurable ?_
  refine Measurable.of_eval ?_
  intro k
  have h_proj : Measurable (fun (v : PgSp d) => v k) :=
    (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d ⊕ Fin d × Fin d => ℝ) (i := k)).continuous.measurable
  have h_mul : Measurable (fun (v : PgSp d) => v k * (2 : ℝ) ^ Bv) :=
    h_proj.mul measurable_const
  have h_floor_int : Measurable (fun (v : PgSp d) => ⌊v k * (2 : ℝ) ^ Bv⌋) :=
    Int.measurable_floor.comp h_mul
  have h_cast : Measurable (fun (v : PgSp d) => (⌊v k * (2 : ℝ) ^ Bv⌋ : ℝ)) :=
    (Measurable.of_discrete (f := (Int.cast : ℤ → ℝ))).comp h_floor_int
  exact h_cast.div measurable_const

end AdversarialBco.Bit.Aux_tri_round_meas

namespace AdversarialBco.Bit.Aux_tri_V_meas


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_V_meas {d : ℕ} (u : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hu : Measurable u) : Measurable (Function.uncurry (triV u)) := by
  -- Let z(p) = pgMu p.1 + pgOp p.1 p.2
  let z : PgSp d × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun p => pgMu p.1 + pgOp p.1 p.2
  have hz_cont : Continuous z := (pg_continuous d).2.2
  have hz_meas : Measurable z := hz_cont.measurable
  have huz_meas : Measurable (u ∘ z) := hu.comp hz_meas
  -- Use measurable_comap_iff to convert from PiLp (WithLp) to the underlying Pi type
  -- The MeasurableSpace on PiLp is MeasurableSpace.comap ofLp
  rw [measurable_comap_iff (g := WithLp.ofLp (p := 2) (V := (Fin d ⊕ Fin d × Fin d) → ℝ))]
  -- Now the goal is: Measurable (WithLp.ofLp ∘ (Function.uncurry (triV u)))
  -- which has target type (Fin d ⊕ Fin d × Fin d) → ℝ
  refine (measurable_pi_iff (X := fun (_ : Fin d ⊕ Fin d × Fin d) => ℝ)).2 ?_
  intro k
  rcases k with (i | ⟨i, j⟩)
  · -- Sum.inl i: the vector coordinate
    -- (WithLp.ofLp ∘ (Function.uncurry (triV u))) p (Sum.inl i) = (u (z p)) i
    have h_eq : (fun (p : PgSp d × EuclideanSpace ℝ (Fin d)) =>
      (WithLp.ofLp ((Function.uncurry (triV u)) p)) (Sum.inl i)) = fun p => (u (z p)) i := by
      ext p
      dsimp [triV, z]
      rfl
    have h_coord_meas : Measurable (fun (v : EuclideanSpace ℝ (Fin d)) => v i) :=
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).measurable
    have h_target : Measurable (fun (p : PgSp d × EuclideanSpace ℝ (Fin d)) => (u (z p)) i) :=
      h_coord_meas.comp huz_meas
    simpa [h_eq, Function.comp] using h_target
  · -- Sum.inr (i, j): the matrix coordinate
    -- (WithLp.ofLp ∘ (Function.uncurry (triV u))) p (Sum.inr (i, j)) =
    --   (if j ≤ i then (u (z p)) i * (p.2 j) else 0) - (if i = j then pgKappa / d / pgMat p.1 i i else 0)
    have h_eq : (fun (p : PgSp d × EuclideanSpace ℝ (Fin d)) =>
      (WithLp.ofLp ((Function.uncurry (triV u)) p)) (Sum.inr (i, j))) =
      fun p => ((if j ≤ i then (u (z p)) i * (p.2 j) else 0) -
        (if i = j then pgKappa / d / pgMat p.1 i i else 0)) := by
      ext p
      dsimp [triV, z]
      rfl
    have h_uzi : Measurable (fun (p : PgSp d × EuclideanSpace ℝ (Fin d)) => (u (z p)) i) :=
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).measurable.comp huz_meas
    have h_yj : Measurable (fun (p : PgSp d × EuclideanSpace ℝ (Fin d)) => p.2 j) :=
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) j).measurable.comp measurable_snd
    have h_mat : Measurable (fun (p : PgSp d × EuclideanSpace ℝ (Fin d)) => pgMat p.1 i i) := by
      have h_cont : Continuous (fun (p : PgSp d × EuclideanSpace ℝ (Fin d)) => pgMat p.1 i i) := by
        -- pgMat p.1 i i = p.1 (Sum.inr (i, i)), which is continuous in p.1
        have : (fun (x : PgSp d) => x (Sum.inr (i, i))) = fun x => pgMat x i i := by
          ext x; rfl
        -- Actually, pgMat x i i = x (Sum.inr (i, i)) by definition
        -- So this is just the projection x ↦ x (Sum.inr (i, i)) composed with fst
        refine (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d ⊕ Fin d × Fin d => ℝ) (Sum.inr (i, i))).comp continuous_fst
      exact h_cont.measurable
    have h_first_if : Measurable (fun (p : PgSp d × EuclideanSpace ℝ (Fin d)) =>
      if j ≤ i then (u (z p)) i * (p.2 j) else 0) := by
      by_cases hji : j ≤ i
      · -- When j ≤ i is true, the condition is always true, so the if reduces to the true branch
        have : (fun (p : PgSp d × EuclideanSpace ℝ (Fin d)) => if j ≤ i then (u (z p)) i * (p.2 j) else 0) =
          fun p => (u (z p)) i * (p.2 j) := by
          ext p; simp [hji]
        rw [this]
        exact Measurable.mul h_uzi h_yj
      · -- When j ≤ i is false, the condition is always false, so the if reduces to the false branch
        have : (fun (p : PgSp d × EuclideanSpace ℝ (Fin d)) => if j ≤ i then (u (z p)) i * (p.2 j) else 0) =
          fun _ => (0 : ℝ) := by
          ext p; simp [hji]
        rw [this]
        exact measurable_const
    have h_second_if : Measurable (fun (p : PgSp d × EuclideanSpace ℝ (Fin d)) =>
      if i = j then pgKappa / d / pgMat p.1 i i else 0) := by
      by_cases hij : i = j
      · have : (fun (p : PgSp d × EuclideanSpace ℝ (Fin d)) => if i = j then pgKappa / d / pgMat p.1 i i else 0) =
          fun p => pgKappa / d / pgMat p.1 i i := by
          ext p; simp [hij]
        rw [this]
        exact Measurable.div measurable_const h_mat
      · have : (fun (p : PgSp d × EuclideanSpace ℝ (Fin d)) => if i = j then pgKappa / d / pgMat p.1 i i else 0) =
          fun _ => (0 : ℝ) := by
          ext p; simp [hij]
        rw [this]
        exact measurable_const
    have h_target : Measurable (fun (p : PgSp d × EuclideanSpace ℝ (Fin d)) =>
      ((if j ≤ i then (u (z p)) i * (p.2 j) else 0) -
        (if i = j then pgKappa / d / pgMat p.1 i i else 0))) :=
      Measurable.sub h_first_if h_second_if
    simpa [h_eq, Function.comp] using h_target

end AdversarialBco.Bit.Aux_tri_V_meas

namespace AdversarialBco.Bit.Aux_coin_curry_inj


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.coin_curry_inj {α κ : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (f : ℕ × κ → ℕ) (hf : Function.Injective f) :
    (Measure.infinitePi fun _ : ℕ => ν).map (fun x (j : ℕ) (k : κ) => x (f (j, k))) =
      Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : κ => ν := by
  have h_eq : (fun (x : ℕ → α) (j : ℕ) (k : κ) => x (f (j, k))) =
      (MeasurableEquiv.curry ℕ κ α) ∘ (fun (x : ℕ → α) (p : ℕ × κ) => x (f p)) := by
    ext x j k
    rfl
  rw [h_eq]
  have h_meas : Measurable (fun (x : ℕ → α) (p : ℕ × κ) => x (f p)) := by
    refine Measurable.of_eval (fun p => ?_)
    exact measurable_pi_apply (f p)
  rw [← Measure.map_map (MeasurableEquiv.curry ℕ κ α).measurable h_meas]
  rw [MeasureTheory.Measure.map_infinitePi_infinitePi_of_inj hf]
  rw [MeasureTheory.Measure.infinitePi_map_curry (fun (_ : ℕ) (_ : κ) => ν)]

end AdversarialBco.Bit.Aux_coin_curry_inj

namespace AdversarialBco.Bit.Aux_readCoins_facts


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.readCoins_facts (cs cs' : ℕ → Bool) (c k : ℕ) :
    0 ≤ AdversarialBco.BitRAM.readCoins cs c k ∧ AdversarialBco.BitRAM.readCoins cs c k < 2 ^ k ∧
      AdversarialBco.BitRAM.readCoins cs c k = AdversarialBco.BitRAM.readCoins (fun i => cs (c + i)) 0 k ∧
      ((∀ i, c ≤ i → i < c + k → cs i = cs' i) →
        AdversarialBco.BitRAM.readCoins cs c k = AdversarialBco.BitRAM.readCoins cs' c k) := by
  induction k with
  | zero =>
      simp [AdversarialBco.BitRAM.readCoins]
  | succ k ih =>
      rcases ih with ⟨h0, h1, h2, h3⟩
      simp only [AdversarialBco.BitRAM.readCoins]
      have h0' : 0 ≤ 2 * AdversarialBco.BitRAM.readCoins cs c k + (if cs (c + k) then (1 : ℤ) else 0) := by
        have hpos1 : 0 ≤ (2 : ℤ) * AdversarialBco.BitRAM.readCoins cs c k := by
          nlinarith
        have hpos2 : 0 ≤ (if cs (c + k) then (1 : ℤ) else 0) := by
          split_ifs <;> norm_num
        omega
      have h1' : 2 * AdversarialBco.BitRAM.readCoins cs c k + (if cs (c + k) then (1 : ℤ) else 0) < (2 : ℤ) ^ (k + 1) := by
        have hk : AdversarialBco.BitRAM.readCoins cs c k ≤ (2 : ℤ) ^ k - 1 := by
          omega
        have hbound : (if cs (c + k) then (1 : ℤ) else 0) ≤ 1 := by
          split_ifs <;> norm_num
        omega
      have h2' : 2 * AdversarialBco.BitRAM.readCoins cs c k + (if cs (c + k) then (1 : ℤ) else 0) =
          2 * AdversarialBco.BitRAM.readCoins (fun i => cs (c + i)) 0 k + (if cs (c + (0 + k)) then (1 : ℤ) else 0) := by
        simp [h2]
      have h3' : (∀ i, c ≤ i → i < c + (k + 1) → cs i = cs' i) →
          (2 * AdversarialBco.BitRAM.readCoins cs c k + (if cs (c + k) then (1 : ℤ) else 0) =
           2 * AdversarialBco.BitRAM.readCoins cs' c k + (if cs' (c + k) then (1 : ℤ) else 0)) := by
        intro h
        have hck : cs (c + k) = cs' (c + k) := h (c + k) (by omega) (by omega)
        have h_ih_restricted : ∀ i, c ≤ i → i < c + k → cs i = cs' i := by
          intro i hi1 hi2
          apply h i hi1
          omega
        have h_eq_k := h3 h_ih_restricted
        simp [hck, h_eq_k]
      exact And.intro h0' (And.intro h1' (And.intro h2' h3'))

end AdversarialBco.Bit.Aux_readCoins_facts

namespace AdversarialBco.Bit.Aux_readCoins_meas


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.readCoins_meas (c k : ℕ) :
    Measurable (fun cs : ℕ → Bool => AdversarialBco.BitRAM.readCoins cs c k) := by
  induction' k with k ih
  · simp [AdversarialBco.BitRAM.readCoins]
  · have h_ite : Measurable (fun cs : ℕ → Bool => if cs (c + k) then (1 : ℤ) else (0 : ℤ)) := by
      have h_bool_meas : Measurable (fun (b : Bool) => if b then (1 : ℤ) else (0 : ℤ)) :=
        Measurable.of_discrete
      have h_proj_meas : Measurable (fun cs : ℕ → Bool => cs (c + k)) :=
        measurable_pi_apply (c + k)
      exact h_bool_meas.comp h_proj_meas
    have eq : (fun cs : ℕ → Bool => AdversarialBco.BitRAM.readCoins cs c (k + 1)) =
      (fun cs => (2 : ℤ) * AdversarialBco.BitRAM.readCoins cs c k +
        (if cs (c + k) then (1 : ℤ) else (0 : ℤ))) := by
      ext cs; simp [AdversarialBco.BitRAM.readCoins]
    rw [eq]
    refine Measurable.add ?_ h_ite
    refine (measurable_const (a := (2 : ℤ))).mul ih

end AdversarialBco.Bit.Aux_readCoins_meas

namespace AdversarialBco.Bit.Aux_gs_cells_ae


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.gs_cells_ae (d B : ℕ) :
    ∀ᵐ ω ∂(gsOmega d), ∀ i, (gsCells d B ω i).1 < 2 ^ B ∧ (gsCells d B ω i).2 < 2 ^ B := by
  -- For u ∈ Ioc 0 1, we have gsCell B u < 2^B
  have h_cell_bound (u : ℝ) (hu : u ∈ Set.Ioc (0 : ℝ) 1) : gsCell B u < 2 ^ B := by
    rcases hu with ⟨hu0, hu1⟩
    have hpos : 0 < (2 : ℝ) ^ B * u := by
      have hp : 0 < (2 : ℝ) ^ B := pow_pos (by norm_num) B
      exact mul_pos hp hu0
    have hle : (2 : ℝ) ^ B * u ≤ (2 : ℝ) ^ B := by
      have hp : 0 ≤ (2 : ℝ) ^ B := pow_nonneg (by norm_num) B
      nlinarith
    have hceil_pos : (0 : ℤ) < ⌈(2 : ℝ) ^ B * u⌉ := by
      rw [Int.ceil_pos]
      exact hpos
    have hceil_le : ⌈(2 : ℝ) ^ B * u⌉ ≤ (2 ^ B : ℤ) := by
      rw [Int.ceil_le]
      push_cast
      exact hle
    have hsub_lt : (⌈(2 : ℝ) ^ B * u⌉ - 1 : ℤ) < (2 ^ B : ℤ) := by
      omega
    have hpos_pow : (2 ^ B : ℕ) ≠ 0 := by
      apply pow_ne_zero
      omega
    have h := (Int.toNat_lt_of_ne_zero hpos_pow).mpr hsub_lt
    simpa [gsCell] using h
  -- Almost every u under unif01 is in Ioc 0 1
  have h_ae_unif01 : ∀ᵐ u ∂unif01, u ∈ Set.Ioc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioc
  -- Hence almost every u under unif01 satisfies gsCell B u < 2^B
  have h_ae_cell : ∀ᵐ u ∂unif01, gsCell B u < 2 ^ B := by
    filter_upwards [h_ae_unif01] with u hu
    exact h_cell_bound u hu
  -- Almost every pair under unif01.prod unif01 has both coordinates in Ioc 0 1
  have h_ae_prod_mem : ∀ᵐ (z : ℝ × ℝ) ∂(unif01.prod unif01), z ∈ (Set.Ioc (0 : ℝ) 1) ×ˢ (Set.Ioc (0 : ℝ) 1) := by
    rw [MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem]
    · filter_upwards [h_ae_unif01] with u hu
      filter_upwards [h_ae_unif01] with v hv
      exact Set.mem_prod.mpr ⟨hu, hv⟩
    · exact measurableSet_Ioc.prod measurableSet_Ioc
  -- Therefore almost every pair satisfies the cell bound
  have h_ae_prod : ∀ᵐ (z : ℝ × ℝ) ∂(unif01.prod unif01), gsCell B z.1 < 2 ^ B ∧ gsCell B z.2 < 2 ^ B := by
    filter_upwards [h_ae_prod_mem] with z hz
    rcases Set.mem_prod.mp hz with ⟨hz1, hz2⟩
    exact ⟨h_cell_bound z.1 hz1, h_cell_bound z.2 hz2⟩
  -- Now extend to Fin d using ae_all_iff and the marginal property of Measure.pi
  rw [MeasureTheory.ae_all_iff]
  intro i
  -- The i-th projection is quasi measure preserving from the pi measure to the marginal
  have h_qmp : MeasureTheory.Measure.QuasiMeasurePreserving (fun ω : Fin d → ℝ × ℝ => ω i)
      (gsOmega d) (unif01.prod unif01) :=
    MeasureTheory.Measure.quasiMeasurePreserving_eval (fun _ : Fin d => unif01.prod unif01) i
  -- Pull back the almost-everywhere statement
  exact h_qmp.ae h_ae_prod

end AdversarialBco.Bit.Aux_gs_cells_ae

namespace AdversarialBco.Bit.Aux_gs_pair_law


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.gs_pair_law {α : Type*} [MeasurableSpace α] (U : Measure α) [IsProbabilityMeasure U]
    (d : ℕ) :
    (Measure.infinitePi fun _ : Fin d × Fin 2 => U).map (fun w (i : Fin d) => (w (i, 0), w (i, 1))) =
      Measure.pi fun _ : Fin d => U.prod U := by
  have h_meas_curry : Measurable (MeasurableEquiv.curry (Fin d) (Fin 2) α) :=
    (MeasurableEquiv.curry (Fin d) (Fin 2) α).measurable
  have h_meas_pair : Measurable (fun (v : Fin d → Fin 2 → α) (i : Fin d) => (v i 0, v i 1)) := by
    fun_prop
  have h_fun_eq : (fun (w : Fin d × Fin 2 → α) (i : Fin d) => (w (i, 0), w (i, 1))) =
      (fun (v : Fin d → Fin 2 → α) (i : Fin d) => (v i 0, v i 1)) ∘
        (MeasurableEquiv.curry (Fin d) (Fin 2) α) := by
    ext w i
    · rfl
    · rfl
  calc
    (Measure.infinitePi fun _ : Fin d × Fin 2 => U).map (fun w (i : Fin d) => (w (i, 0), w (i, 1)))
        = (Measure.infinitePi fun _ : Fin d × Fin 2 => U).map
          ((fun (v : Fin d → Fin 2 → α) (i : Fin d) => (v i 0, v i 1)) ∘
            (MeasurableEquiv.curry (Fin d) (Fin 2) α)) := by rw [h_fun_eq]
    _ = ((Measure.infinitePi fun _ : Fin d × Fin 2 => U).map
            (MeasurableEquiv.curry (Fin d) (Fin 2) α)).map
          (fun (v : Fin d → Fin 2 → α) (i : Fin d) => (v i 0, v i 1)) := by
      rw [Measure.map_map h_meas_pair h_meas_curry]
    _ = (Measure.infinitePi fun i : Fin d => Measure.infinitePi fun j : Fin 2 => U).map
        (fun (v : Fin d → Fin 2 → α) (i : Fin d) => (v i 0, v i 1)) := by
      rw [MeasureTheory.Measure.infinitePi_map_curry (μ := fun (_ : Fin d) (_ : Fin 2) => U)]
    _ = (Measure.pi fun i : Fin d => Measure.infinitePi fun _ : Fin 2 => U).map
        (fun (v : Fin d → Fin 2 → α) (i : Fin d) => (v i 0, v i 1)) := by
      rw [MeasureTheory.Measure.infinitePi_eq_pi (μ := fun (_ : Fin d) => Measure.infinitePi fun _ : Fin 2 => U)]
    _ = Measure.pi fun i : Fin d => (Measure.infinitePi fun _ : Fin 2 => U).map
        (fun x : Fin 2 → α => (x 0, x 1)) := by
      simpa using MeasureTheory.Measure.pi_map_pi (μ := fun (_ : Fin d) => Measure.infinitePi fun _ : Fin 2 => U)
        (f := fun (_ : Fin d) => (fun (x : Fin 2 → α) => (x 0, x 1))) (hf := fun _ => by fun_prop)
    _ = Measure.pi fun _ : Fin d => U.prod U := by
      have h_infinitePi_eq_pi : Measure.infinitePi (fun _ : Fin 2 => U) = Measure.pi (fun _ : Fin 2 => U) :=
        MeasureTheory.Measure.infinitePi_eq_pi (μ := fun (_ : Fin 2) => U)
      have hpair : (Measure.infinitePi fun _ : Fin 2 => U).map (fun x : Fin 2 → α => (x 0, x 1)) = U.prod U := by
        rw [h_infinitePi_eq_pi]
        have hmp := MeasureTheory.measurePreserving_piFinTwo (μ := fun (_ : Fin 2) => U)
        simpa [MeasurableEquiv.piFinTwo_apply] using hmp.map_eq
      simp [hpair]

end AdversarialBco.Bit.Aux_gs_pair_law

namespace AdversarialBco.Bit.Aux_rows_norm_le


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.rows_norm_le {d m : ℕ} (α : Fin m → EuclideanSpace ℝ (Fin d)) (β : Fin m → ℝ)
    (hB : Metric.closedBall 0 1 ⊆ {y | ∀ k, inner ℝ (α k) y ≤ β k}) (k : Fin m) : ‖α k‖ ≤ β k := by
  by_cases hzero : α k = 0
  · rw [hzero, norm_zero]
    have hmem : (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      rw [Metric.mem_closedBall, dist_self]
      norm_num
    have hsub := hB hmem
    have hinner := hsub k
    simpa [hzero, inner_zero_right] using hinner
  · have hnorm_pos : 0 < ‖α k‖ := (norm_pos_iff.mpr hzero)
    set y := (‖α k‖⁻¹ : ℝ) • α k with hy
    have hynorm : ‖y‖ = 1 := by
      show ‖(‖α k‖⁻¹ : ℝ) • α k‖ = 1
      calc
        ‖(‖α k‖⁻¹ : ℝ) • α k‖ = ‖(‖α k‖⁻¹ : ℝ)‖ * ‖α k‖ := by rw [norm_smul]
        _ = ‖α k‖⁻¹ * ‖α k‖ := by rw [norm_inv, norm_norm]
        _ = 1 := by field_simp [hnorm_pos.ne']
    have hmem : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hynorm]
    have hsub := hB hmem
    have hinner := hsub k
    have hcalc : inner ℝ (α k) y = ‖α k‖ := by
      show inner ℝ (α k) ((‖α k‖⁻¹ : ℝ) • α k) = ‖α k‖
      rw [real_inner_smul_right]
      have hsq : inner ℝ (α k) (α k) = ‖α k‖ ^ 2 := by
        have h := inner_self_eq_norm_sq (𝕜 := ℝ) (α k)
        simpa using h
      rw [hsq]
      calc
        ‖α k‖⁻¹ * ‖α k‖ ^ 2 = (‖α k‖⁻¹ * ‖α k‖) * ‖α k‖ := by ring
        _ = 1 * ‖α k‖ := by field_simp [hnorm_pos.ne']
        _ = ‖α k‖ := by simp
    rw [hcalc] at hinner
    exact hinner

end AdversarialBco.Bit.Aux_rows_norm_le

namespace AdversarialBco.Bit.Aux_tri_rows_pull


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_rows_pull {d m : ℕ} (α : Fin m → EuclideanSpace ℝ (Fin d)) (β : Fin m → ℝ)
    (μ : EuclideanSpace ℝ (Fin d)) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    posBody {y | ∀ k, inner ℝ (α k) y ≤ β k} μ A =
      {z | ∀ k, inner ℝ (ContinuousLinearMap.adjoint A (α k)) z ≤ β k - inner ℝ (α k) μ} := by
  ext z
  simp [posBody]
  constructor
  · intro h k
    have hk := h k
    rw [inner_add_right] at hk
    rw [← ContinuousLinearMap.adjoint_inner_left A z (α k)] at hk
    rw [le_sub_iff_add_le]
    rw [add_comm]
    exact hk
  · intro h k
    have hk := h k
    rw [le_sub_iff_add_le] at hk
    rw [add_comm] at hk
    simpa [inner_add_right, ContinuousLinearMap.adjoint_inner_left A z (α k)] using hk

end AdversarialBco.Bit.Aux_tri_rows_pull

namespace AdversarialBco.Bit.Aux_tri_cube_mid


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_cube_mid {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K)
    (c : EuclideanSpace ℝ (Fin d)) (hc : c ∈ K) (s : ℝ) (hs : 0 ≤ s) :
    c ∈ K ∩ triCube c s ∧ (K ∩ triCube c s ⊆ K ∩ triCube c (2 * s)) ∧
      ∀ x ∈ K ∩ triCube c (2 * s), midpoint ℝ c x ∈ K ∩ triCube c s := by
  have hhalf_pos : 0 < (1/2 : ℝ) := by norm_num
  have hmid_eq : ∀ (a b : EuclideanSpace ℝ (Fin d)), midpoint ℝ a b = (1/2 : ℝ) • (a + b) := by
    intro a b
    rw [midpoint_eq_smul_add ℝ a b]
    have : (⅟2 : ℝ) = (1/2 : ℝ) := by norm_num
    rw [this]
  refine ⟨?_, ?_, ?_⟩
  · -- c ∈ K ∩ triCube c s
    refine ⟨hc, ?_⟩
    intro i
    simp [sub_self, abs_zero, hs]
  · -- K ∩ triCube c s ⊆ K ∩ triCube c (2 * s)
    intro x hx
    rcases hx with ⟨hxK, hxTri⟩
    refine ⟨hxK, ?_⟩
    intro i
    have h := hxTri i
    nlinarith
  · -- ∀ x ∈ K ∩ triCube c (2 * s), midpoint ℝ c x ∈ K ∩ triCube c s
    intro x hx
    rcases hx with ⟨hxK, hxTri⟩
    have hmidK : midpoint ℝ c x ∈ K := hK.midpoint_mem hc hxK
    have hmidTri : midpoint ℝ c x ∈ triCube c s := by
      intro i
      have hmid_val : (midpoint ℝ c x) i = (1/2 : ℝ) * (c i + x i) := by
        rw [hmid_eq c x, PiLp.smul_apply, PiLp.add_apply]
        rfl
      have hdiff : (midpoint ℝ c x) i - c i = (1/2 : ℝ) * (x i - c i) := by
        rw [hmid_val]
        ring
      rw [hdiff]
      rw [abs_mul]
      have habs_half : |(1/2 : ℝ)| = (1/2 : ℝ) := abs_of_pos hhalf_pos
      rw [habs_half]
      have hbound : |x i - c i| ≤ 2 * s := hxTri i
      nlinarith
    exact ⟨hmidK, hmidTri⟩

end AdversarialBco.Bit.Aux_tri_cube_mid

namespace AdversarialBco.Bit.Aux_posBody_closed


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.posBody_closed {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hKc : Convex ℝ K)
    (hKcl : IsClosed K) (μ : EuclideanSpace ℝ (Fin d)) (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    Convex ℝ (posBody K μ A) ∧ IsClosed (posBody K μ A) := by
  let f : EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] EuclideanSpace ℝ (Fin d) :=
    (A : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)).toAffineMap +
    AffineMap.const ℝ (EuclideanSpace ℝ (Fin d)) μ
  have hf_cont : Continuous f := by
    have : (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) = fun y => A y + μ := by
      ext y
      simp [f, AffineMap.coe_add, AffineMap.coe_const]
    rw [this]
    exact A.continuous.add continuous_const
  have h_eq : posBody K μ A = f ⁻¹' K := by
    ext y
    simp [posBody, f, AffineMap.coe_add, AffineMap.coe_const, add_comm]
  have h_closed : IsClosed (posBody K μ A) := by
    rw [h_eq]
    exact IsClosed.preimage hf_cont hKcl
  have h_convex : Convex ℝ (posBody K μ A) := by
    rw [h_eq]
    exact Convex.affine_preimage f hKc
  exact And.intro h_convex h_closed

end AdversarialBco.Bit.Aux_posBody_closed

namespace AdversarialBco.Bit.Aux_tri_mst


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_mst (r0 R0 : ℝ) (hr0 : 0 < r0) :
    1 ≤ triMst r0 R0 ∧ R0 ≤ 2 ^ triMst r0 R0 * r0 := by
  have h1 : 1 ≤ triMst r0 R0 := by
    unfold triMst
    exact le_max_left _ _
  have h2 : R0 ≤ 2 ^ triMst r0 R0 * r0 := by
    have hdiv : R0 / r0 ≤ (⌈R0 / r0⌉₊ : ℝ) := Nat.le_ceil (R0 / r0)
    have hclog_nat : ⌈R0 / r0⌉₊ ≤ 2 ^ Nat.clog 2 ⌈R0 / r0⌉₊ := by
      have h2pos : 1 < 2 := by norm_num
      exact Nat.le_pow_clog h2pos _
    have hcast : (⌈R0 / r0⌉₊ : ℝ) ≤ ((2 ^ Nat.clog 2 ⌈R0 / r0⌉₊ : ℕ) : ℝ) := by
      exact mod_cast hclog_nat
    have hpow : ((2 ^ Nat.clog 2 ⌈R0 / r0⌉₊ : ℕ) : ℝ) ≤ ((2 ^ (max 1 (Nat.clog 2 ⌈R0 / r0⌉₊)) : ℕ) : ℝ) := by
      have h2one : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
      have hle : (Nat.clog 2 ⌈R0 / r0⌉₊ : ℕ) ≤ max 1 (Nat.clog 2 ⌈R0 / r0⌉₊) := le_max_right _ _
      have hpow' : (2 : ℝ) ^ (Nat.clog 2 ⌈R0 / r0⌉₊ : ℕ) ≤ (2 : ℝ) ^ (max 1 (Nat.clog 2 ⌈R0 / r0⌉₊) : ℕ) :=
        pow_le_pow_right₀ h2one hle
      simpa [Nat.cast_pow] using hpow'
    have htri : ((2 ^ (max 1 (Nat.clog 2 ⌈R0 / r0⌉₊)) : ℕ) : ℝ) = (2 ^ triMst r0 R0 : ℝ) := by
      simp [triMst, Nat.cast_pow]
    have hchain : R0 / r0 ≤ (2 ^ triMst r0 R0 : ℝ) := by
      calc
        R0 / r0 ≤ (⌈R0 / r0⌉₊ : ℝ) := hdiv
        _ ≤ ((2 ^ Nat.clog 2 ⌈R0 / r0⌉₊ : ℕ) : ℝ) := hcast
        _ ≤ ((2 ^ (max 1 (Nat.clog 2 ⌈R0 / r0⌉₊)) : ℕ) : ℝ) := hpow
        _ = (2 ^ triMst r0 R0 : ℝ) := htri
    apply (div_le_iff₀ hr0).mp
    simpa using hchain
  exact And.intro h1 h2

end AdversarialBco.Bit.Aux_tri_mst

namespace AdversarialBco.Bit.Aux_tri_lay_inj


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_lay_inj (mst L : ℕ) : Function.Injective (triLay mst L) := by
  intro p q h
  simp [triLay] at h
  split_ifs at h
  · -- both in first branch: p.1 * L + p.2 = q.1 * L + q.2
    rename_i hp hq
    rcases hp with ⟨hp₁, hp₂⟩
    rcases hq with ⟨hq₁, hq₂⟩
    have hp_mod : (p.1 * L + p.2) % L = p.2 := by
      rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add]
      rw [Nat.mod_eq_of_lt hp₂]
      exact Nat.mod_eq_of_lt hp₂
    have hq_mod : (q.1 * L + q.2) % L = q.2 := by
      rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add]
      rw [Nat.mod_eq_of_lt hq₂]
      exact Nat.mod_eq_of_lt hq₂
    have hmod : p.2 = q.2 := by
      calc
        p.2 = (p.1 * L + p.2) % L := by rw [hp_mod]
        _ = (q.1 * L + q.2) % L := by rw [h]
        _ = q.2 := by rw [hq_mod]
    have hmul : p.1 * L = q.1 * L := by
      rw [hmod] at h
      -- h : p.1 * L + q.2 = q.1 * L + q.2
      exact Nat.add_right_cancel h
    have hLpos : 0 < L := by
      by_contra hL
      have hL0 : L = 0 := Nat.eq_zero_of_not_pos hL
      rw [hL0] at hp₂
      exact Nat.not_lt_zero _ hp₂
    have hdiv : p.1 = q.1 :=
      Nat.eq_of_mul_eq_mul_right hLpos hmul
    exact Prod.ext hdiv hmod
  · -- first branch (p) vs second branch (q): p.1 * L + p.2 = mst * L + Nat.pair q.1 q.2
    rename_i hp hq
    rcases hp with ⟨hp₁, hp₂⟩
    have h_lt : p.1 * L + p.2 < mst * L := by
      have h_succ : p.1 + 1 ≤ mst := Nat.succ_le_of_lt hp₁
      have h_mul : (p.1 + 1) * L ≤ mst * L := Nat.mul_le_mul_right L h_succ
      have h_lt' : p.1 * L + p.2 < p.1 * L + L := Nat.add_lt_add_left hp₂ (p.1 * L)
      have h_eq : p.1 * L + L = (p.1 + 1) * L := by ring
      rw [h_eq] at h_lt'
      exact lt_of_lt_of_le h_lt' h_mul
    have h_ge : mst * L ≤ mst * L + Nat.pair q.1 q.2 := Nat.le_add_right _ _
    rw [h] at h_lt
    omega
  · -- first branch (q) vs second branch (p): q.1 * L + q.2 = mst * L + Nat.pair p.1 p.2
    rename_i hp hq
    rcases hq with ⟨hq₁, hq₂⟩
    have h_lt : q.1 * L + q.2 < mst * L := by
      have h_succ : q.1 + 1 ≤ mst := Nat.succ_le_of_lt hq₁
      have h_mul : (q.1 + 1) * L ≤ mst * L := Nat.mul_le_mul_right L h_succ
      have h_lt' : q.1 * L + q.2 < q.1 * L + L := Nat.add_lt_add_left hq₂ (q.1 * L)
      have h_eq : q.1 * L + L = (q.1 + 1) * L := by ring
      rw [h_eq] at h_lt'
      exact lt_of_lt_of_le h_lt' h_mul
    have h_ge : mst * L ≤ mst * L + Nat.pair p.1 p.2 := Nat.le_add_right _ _
    rw [← h] at h_lt
    omega
  · -- both in second branch: mst * L + Nat.pair p.1 p.2 = mst * L + Nat.pair q.1 q.2
    rename_i hp hq
    have hpair : Nat.pair p.1 p.2 = Nat.pair q.1 q.2 :=
      Nat.add_left_cancel h
    rcases (Nat.pair_eq_pair.mp hpair) with ⟨h₁, h₂⟩
    exact Prod.ext h₁ h₂

end AdversarialBco.Bit.Aux_tri_lay_inj

namespace AdversarialBco.Bit.Aux_tri_par_stage


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_par_stage (d : ℕ) (hd : 1 ≤ d) :
    3 * (36.4 * d * pgLam (triRh d)) ≤ triRa d ∧ 2 * Real.sqrt d ≤ triRa d ∧
      36.4 * d * pgLam (triRh d) ≤ 134 * d * Real.sqrt (Real.log (2 * d + 2)) := by
  have hspec := Nat.find_spec (pg_par_exists d)
  have hs : 4 ≤ triS d := hspec.1
  have hC_nat : 2086812 * d ^ 2 * triLh (triS d) ≤ 125 * (2 ^ triLa (triS d) - 1) ^ 2 := by
    simpa [triS, triLa, triLh] using hspec.2
  have h_pow_nat : 1 ≤ (2 : ℕ) ^ triLa (triS d) := Nat.one_le_pow' (triLa (triS d)) 1
  have hRa_nonneg : 0 ≤ triRa d := by
    rw [triRa]
    have h : (1 : ℝ) ≤ (2 : ℝ) ^ (triLa (triS d) : ℕ) := by exact_mod_cast h_pow_nat
    linarith
  have hC_real : 2086812 * (d : ℝ) ^ 2 * (triLh (triS d) : ℝ) ≤ 125 * (triRa d) ^ 2 := by
    rw [triRa]
    -- hC_nat: 2086812 * d ^ 2 * triLh (triS d) ≤ 125 * (2 ^ triLa (triS d) - 1) ^ 2
    -- We need to cast to ℝ
    -- Using mod_cast since all parts are nonnegative
    -- But mod_cast may need the subtraction condition
    have h := hC_nat
    -- The RHS: (2 ^ triLa (triS d) - 1) in ℕ, cast to ℝ
    -- We have: (2 : ℝ) ^ (triLa (triS d) : ℕ) - 1 = triRa d
    -- So we can rewrite the goal using this
    -- Actually, let's use `exact_mod_cast` directly
    -- mod_cast h should work if we provide the condition that 1 ≤ 2 ^ triLa (triS d)
    have h_sub : 1 ≤ (2 : ℕ) ^ triLa (triS d) := h_pow_nat
    -- Now use `exact_mod_cast` with this condition
    -- But `exact_mod_cast` doesn't take extra hypotheses...
    -- Let's use `apply` with `mod_cast`
    -- `mod_cast h` will try to cast both sides
    -- The issue is the subtraction: `mod_cast` needs to know that `1 ≤ 2 ^ triLa (triS d)`
    -- We can use `exact_mod_cast (h.trans ?_)` or similar
    -- Actually, let's use `simpa [Nat.cast_sub h_sub, Nat.cast_pow] using mod_cast h`
    simpa [Nat.cast_sub h_sub, Nat.cast_pow] using mod_cast h
  have hLam_eq : pgLam (triRh d) = Real.sqrt (2 * (triLh (triS d) : ℝ) * Real.log 2) := by
    rw [pgLam, triRh]
    have h_add : 1 + ((2 : ℝ) ^ (triLh (triS d) : ℕ) - 1) = (2 : ℝ) ^ (triLh (triS d) : ℕ) := by ring
    calc
      Real.sqrt (2 * Real.log (1 + ((2 : ℝ) ^ (triLh (triS d) : ℕ) - 1))) = Real.sqrt (2 * Real.log ((2 : ℝ) ^ (triLh (triS d) : ℕ))) := by rw [h_add]
      _ = Real.sqrt (2 * ((triLh (triS d) : ℝ) * Real.log 2)) := by rw [Real.log_pow]
      _ = Real.sqrt (2 * (triLh (triS d) : ℝ) * Real.log 2) := by ring
  have hLam_nonneg : 1 ≤ pgLam (triRh d) := by
    rw [hLam_eq]
    have hLh_ge_one : (1 : ℝ) ≤ (triLh (triS d) : ℝ) := by
      have hLh_pos : 0 < triLh (triS d) := by
        rw [triLh]
        apply Nat.div_pos
        · have h_sq : 16 ≤ (triS d) ^ 2 := by nlinarith
          nlinarith
        · norm_num
      have hLh_ge_one_nat : 1 ≤ triLh (triS d) := by omega
      exact_mod_cast hLh_ge_one_nat
    have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have h_inner : (1 : ℝ) ≤ 2 * (triLh (triS d) : ℝ) * Real.log 2 := by
      have h_log2_gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
      nlinarith
    have h_nonneg : 0 ≤ 2 * (triLh (triS d) : ℝ) * Real.log 2 := by
      have h_nonneg_log : 0 ≤ Real.log 2 := by linarith
      positivity
    have h_sq : (1 : ℝ) ^ 2 ≤ 2 * (triLh (triS d) : ℝ) * Real.log 2 := by
      -- (1)^2 = 1, and h_inner gives 1 ≤ 2 * Lh * log 2
      simpa [sq] using h_inner
    calc
      (1 : ℝ) = Real.sqrt ((1 : ℝ) ^ 2) := by norm_num
      _ ≤ Real.sqrt (2 * (triLh (triS d) : ℝ) * Real.log 2) := Real.sqrt_le_sqrt h_sq
      _ = Real.sqrt (2 * (triLh (triS d) : ℝ) * Real.log 2) := rfl
  have h_first : 3 * (36.4 * (d : ℝ) * pgLam (triRh d)) ≤ triRa d := by
    have h_goal : 3 * ((364 : ℝ) / 10) * (d : ℝ) * Real.sqrt (2 * (triLh (triS d) : ℝ) * Real.log 2) ≤ triRa d := by
      apply pg_par_b (d : ℝ) (triLh (triS d) : ℝ) (triRa d) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hRa_nonneg hC_real
    have h36 : (36.4 : ℝ) = (364 : ℝ) / 10 := by norm_num
    rw [hLam_eq, h36]
    -- Goal: 3 * ((364 : ℝ) / 10 * ↑d * Real.sqrt (2 * ↑(triLh (triS d)) * Real.log 2)) ≤ triRa d
    -- h_goal: 3 * ((364 : ℝ) / 10) * ↑d * Real.sqrt (2 * ↑(triLh (triS d)) * Real.log 2) ≤ triRa d
    -- Need to reassociate
    simpa [mul_assoc] using h_goal
  have h_second : 2 * Real.sqrt (d : ℝ) ≤ triRa d := by
    -- pg_par_b2 expects: 2 * Real.sqrt d ≤ ρ given 1 ≤ d, 1 ≤ lam, and 3*(364/10)*d*lam ≤ ρ
    -- We have h_first: 3 * (36.4 * d * pgLam (triRh d)) ≤ triRa d
    -- But pg_par_b2 expects: 3 * (364/10) * d * lam ≤ ρ
    -- So we need to convert h_first
    have h_first' : 3 * ((364 : ℝ) / 10) * (d : ℝ) * pgLam (triRh d) ≤ triRa d := by
      have h36 : (36.4 : ℝ) = (364 : ℝ) / 10 := by norm_num
      rw [h36] at h_first
      simpa [mul_assoc] using h_first
    apply pg_par_b2 (d : ℝ) (pgLam (triRh d)) (triRa d) (by exact_mod_cast hd) hLam_nonneg h_first'
  have h_third : 36.4 * (d : ℝ) * pgLam (triRh d) ≤ 134 * (d : ℝ) * Real.sqrt (Real.log (2 * (d : ℝ) + 2)) := by
    -- Using pg_par_d
    have hmin : ∀ s', 4 ≤ s' → s' < triS d →
      ¬ (2086812 * d ^ 2 * ((50 * s' ^ 2 + 68) / 69) ≤ 125 * (2 ^ (5 * s' ^ 2 / 7) - 1) ^ 2) := by
      intro s' hs'_ge hs'_lt
      have h_not' := Nat.find_min (pg_par_exists d) hs'_lt
      -- h_not' : ¬ (4 ≤ s' ∧ 2086812 * d ^ 2 * ((50 * s' ^ 2 + 68) / 69) ≤ 125 * (2 ^ (5 * s' ^ 2 / 7) - 1) ^ 2)
      intro h_ineq
      apply h_not'
      exact And.intro hs'_ge h_ineq
    have h_pg_par_d := pg_par_d (triS d) d hs hd hmin
    -- h_pg_par_d : (364/10)^2 * (2 * (((50 * s^2 + 68)/69 : ℕ) : ℝ) * Real.log 2) ≤ 134^2 * Real.log (2 * d + 2)
    -- We need to relate this to our goal
    -- Goal: 36.4 * d * pgLam (triRh d) ≤ 134 * d * Real.sqrt (Real.log (2 * d + 2))
    -- Using hLam_eq: pgLam (triRh d) = Real.sqrt (2 * (triLh (triS d) : ℝ) * Real.log 2)
    -- triLh (triS d) = (50 * (triS d)^2 + 68) / 69
    -- So the LHS of h_pg_par_d is (364/10)^2 * (2 * (triLh (triS d) : ℝ) * Real.log 2)
    -- And we need: 36.4 * d * Real.sqrt (2 * (triLh (triS d) : ℝ) * Real.log 2) ≤ 134 * d * Real.sqrt (Real.log (2*d+2))
    -- Note: 36.4 = 364/10
    -- Let A = (364/10) * d * Real.sqrt (2 * (triLh (triS d) : ℝ) * Real.log 2)
    -- We have: (364/10)^2 * (2 * (triLh (triS d) : ℝ) * Real.log 2) ≤ 134^2 * Real.log (2*d+2)
    -- Taking square root (all nonnegative):
    -- (364/10) * Real.sqrt (2 * (triLh (triS d) : ℝ) * Real.log 2) ≤ 134 * Real.sqrt (Real.log (2*d+2))
    -- Multiply by d ≥ 0: done
    rw [hLam_eq]
    -- Goal: 36.4 * (d : ℝ) * Real.sqrt (2 * (triLh (triS d) : ℝ) * Real.log 2) ≤ 134 * (d : ℝ) * Real.sqrt (Real.log (2 * (d : ℝ) + 2))
    have hd_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
    have h_nonneg_right : 0 ≤ 134 * Real.sqrt (Real.log (2 * (d : ℝ) + 2)) := by
      have h_nonneg_log : 0 ≤ Real.log (2 * (d : ℝ) + 2) := by
        -- 2*d + 2 ≥ 2 > 1, so log is positive
        have h_arg : (1 : ℝ) < 2 * (d : ℝ) + 2 := by
          have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
          linarith
        exact le_of_lt (Real.log_pos h_arg)
      positivity
    -- Rewrite h_pg_par_d using triLh definition
    have h_pg_par_d' : ((364 : ℝ) / 10) ^ 2 * (2 * (triLh (triS d) : ℝ) * Real.log 2) ≤
        (134 : ℝ) ^ 2 * Real.log (2 * (d : ℝ) + 2) := by
      -- h_pg_par_d has ↑((50 * triS d ^ 2 + 68) / 69) instead of (triLh (triS d) : ℝ)
      -- But triLh (triS d) = (50 * (triS d)^2 + 68) / 69
      simpa [triLh] using h_pg_par_d
    -- Let A = (364/10) * sqrt(2 * Lh * log 2), B = 134 * sqrt(log(2*d+2))
    -- Then h_pg_par_d' says A^2 ≤ B^2
    -- Since A ≥ 0 and B ≥ 0, we get A ≤ B
    have h_nonneg_left : 0 ≤ (364 : ℝ) / 10 * Real.sqrt (2 * (triLh (triS d) : ℝ) * Real.log 2) := by
      have h_nonneg_log : 0 ≤ Real.log 2 := by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
      positivity
    have h_nonneg_right : 0 ≤ 134 * Real.sqrt (Real.log (2 * (d : ℝ) + 2)) := by
      have h_nonneg_log : 0 ≤ Real.log (2 * (d : ℝ) + 2) := by
        have h_arg : (1 : ℝ) < 2 * (d : ℝ) + 2 := by
          have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
          linarith
        exact le_of_lt (Real.log_pos h_arg)
      positivity
    have h_sqrt_ineq : (364 : ℝ) / 10 * Real.sqrt (2 * (triLh (triS d) : ℝ) * Real.log 2) ≤
        134 * Real.sqrt (Real.log (2 * (d : ℝ) + 2)) := by
      have h_sq : ((364 : ℝ) / 10 * Real.sqrt (2 * (triLh (triS d) : ℝ) * Real.log 2)) ^ 2 ≤
          (134 * Real.sqrt (Real.log (2 * (d : ℝ) + 2))) ^ 2 := by
        have h_nonneg_inner : 0 ≤ 2 * (triLh (triS d) : ℝ) * Real.log 2 := by
          have h_nonneg_log : 0 ≤ Real.log 2 := by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
          positivity
        have h_nonneg_log2 : 0 ≤ Real.log (2 * (d : ℝ) + 2) := by
          have h_arg : (1 : ℝ) < 2 * (d : ℝ) + 2 := by
            have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
            linarith
          exact le_of_lt (Real.log_pos h_arg)
        calc
          ((364 : ℝ) / 10 * Real.sqrt (2 * (triLh (triS d) : ℝ) * Real.log 2)) ^ 2 =
              ((364 : ℝ) / 10) ^ 2 * (Real.sqrt (2 * (triLh (triS d) : ℝ) * Real.log 2)) ^ 2 := by ring
          _ = ((364 : ℝ) / 10) ^ 2 * (2 * (triLh (triS d) : ℝ) * Real.log 2) := by
            rw [Real.sq_sqrt h_nonneg_inner]
          _ ≤ (134 : ℝ) ^ 2 * Real.log (2 * (d : ℝ) + 2) := h_pg_par_d'
          _ = (134 * Real.sqrt (Real.log (2 * (d : ℝ) + 2))) ^ 2 := by
            calc
              (134 : ℝ) ^ 2 * Real.log (2 * (d : ℝ) + 2) = (134 : ℝ) ^ 2 * (Real.sqrt (Real.log (2 * (d : ℝ) + 2))) ^ 2 := by
                rw [Real.sq_sqrt h_nonneg_log2]
              _ = (134 * Real.sqrt (Real.log (2 * (d : ℝ) + 2))) ^ 2 := by ring
      -- Now take square roots using the lemma that a^2 ≤ b^2 and a,b ≥ 0 implies a ≤ b
      nlinarith
    -- Now multiply both sides by (d : ℝ) ≥ 0
    have hd_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
    -- Goal: 36.4 * ↑d * √(2 * ↑(triLh (triS d)) * Real.log 2) ≤ 134 * ↑d * √(Real.log (2 * ↑d + 2))
    -- Note: 36.4 = 364/10
    have h36 : (36.4 : ℝ) = (364 : ℝ) / 10 := by norm_num
    rw [h36]
    -- Goal: (364/10) * ↑d * √(2 * ↑(triLh (triS d)) * Real.log 2) ≤ 134 * ↑d * √(Real.log (2 * ↑d + 2))
    -- This is: ↑d * ((364/10) * √(...)) ≤ ↑d * (134 * √(...))
    -- Since ↑d ≥ 0, we can factor it out
    -- Actually, the goal is already in the right form: multiply h_sqrt_ineq by d
    -- Using `mul_le_mul_of_nonneg_left` with hd_nonneg
    -- But note the associativity: (364/10) * d * sqrt(...) vs d * ((364/10) * sqrt(...))
    -- Let's use `nlinarith` or `gcongr` or just `apply mul_le_mul_of_nonneg_left`
    -- The goal: (364/10) * ↑d * √(...) ≤ 134 * ↑d * √(...)
    -- This is: ↑d * ((364/10) * √(...)) ≤ ↑d * (134 * √(...))
    -- Using `mul_le_mul_of_nonneg_left h_sqrt_ineq hd_nonneg` after reassociating
    -- But the LHS is (364/10) * d * sqrt, not d * ((364/10) * sqrt)
    -- Let's use `ring` or `simp [mul_assoc]` to rearrange
    -- Actually, we can use `gcongr` or just:
    calc
      ((364 : ℝ) / 10) * (d : ℝ) * Real.sqrt (2 * (triLh (triS d) : ℝ) * Real.log 2) =
          (d : ℝ) * (((364 : ℝ) / 10) * Real.sqrt (2 * (triLh (triS d) : ℝ) * Real.log 2)) := by ring
      _ ≤ (d : ℝ) * (134 * Real.sqrt (Real.log (2 * (d : ℝ) + 2))) :=
        mul_le_mul_of_nonneg_left h_sqrt_ineq hd_nonneg
      _ = 134 * (d : ℝ) * Real.sqrt (Real.log (2 * (d : ℝ) + 2)) := by ring
  exact And.intro h_first (And.intro h_second h_third)

end AdversarialBco.Bit.Aux_tri_par_stage

namespace AdversarialBco.Bit.Aux_tri_poly_cc


open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
open AdversarialBco.Poly AdversarialBco.Bit

theorem _root_.AdversarialBco.Bit.tri_poly_cc {d m : ℕ} (A : Fin m → EuclideanSpace ℝ (Fin d)) (b : Fin m → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    Convex ℝ {y | ∀ k, inner ℝ (A k) y ≤ b k} ∧ IsClosed {y | ∀ k, inner ℝ (A k) y ≤ b k} ∧
      Convex ℝ (triCube c s) ∧ IsClosed (triCube c s) := by
  have h_poly_eq : {y | ∀ k, inner ℝ (A k) y ≤ b k} = ⋂ k, {y | inner ℝ (A k) y ≤ b k} := by
    ext y; simp
  have h_poly_convex : Convex ℝ {y | ∀ k, inner ℝ (A k) y ≤ b k} := by
    rw [h_poly_eq]
    apply convex_iInter
    intro k
    apply convex_halfSpace_le ?_ (b k)
    exact LinearMap.isLinear ((innerₗ (EuclideanSpace ℝ (Fin d))) (A k))
  have h_poly_closed : IsClosed {y | ∀ k, inner ℝ (A k) y ≤ b k} := by
    rw [h_poly_eq]
    apply isClosed_iInter
    intro k
    apply isClosed_le ?_ ?_
    · exact continuous_const.inner continuous_id
    · exact continuous_const
  have h_cube_eq : triCube c s = ⋂ i, {y | |y i - c i| ≤ s} := by
    ext y
    rw [triCube, Set.mem_iInter]
    simp
  have h_slice_convex (i : Fin d) : Convex ℝ {y : EuclideanSpace ℝ (Fin d) | |y i - c i| ≤ s} := by
    have h_eq : {y : EuclideanSpace ℝ (Fin d) | |y i - c i| ≤ s} = {y : EuclideanSpace ℝ (Fin d) | y i - c i ≤ s} ∩ {y : EuclideanSpace ℝ (Fin d) | c i - s ≤ y i} := by
      ext y; simp [abs_sub_le_iff, add_comm]
    rw [h_eq]
    apply Convex.inter
    · have h_half : {y : EuclideanSpace ℝ (Fin d) | y i - c i ≤ s} = {y | (EuclideanSpace.projₗ i) y ≤ s + c i} := by
        ext y; simp [EuclideanSpace.projₗ]
      rw [h_half]
      apply convex_halfSpace_le ?_ (s + c i)
      exact LinearMap.isLinear (EuclideanSpace.projₗ i)
    · have h_half : {y : EuclideanSpace ℝ (Fin d) | c i - s ≤ y i} = {y | (-(EuclideanSpace.projₗ i)) y ≤ s - c i} := by
        ext y; simp [EuclideanSpace.projₗ, add_comm]
      rw [h_half]
      apply convex_halfSpace_le ?_ (s - c i)
      exact LinearMap.isLinear (-(EuclideanSpace.projₗ i))
  have h_slice_closed (i : Fin d) : IsClosed {y : EuclideanSpace ℝ (Fin d) | |y i - c i| ≤ s} := by
    have h_eq : {y : EuclideanSpace ℝ (Fin d) | |y i - c i| ≤ s} = {y : EuclideanSpace ℝ (Fin d) | y i - c i ≤ s} ∩ {y : EuclideanSpace ℝ (Fin d) | c i - s ≤ y i} := by
      ext y; simp [abs_sub_le_iff, add_comm]
    rw [h_eq]
    apply IsClosed.inter
    · apply isClosed_le ?_ ?_
      · exact (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).sub continuous_const
      · exact continuous_const
    · apply isClosed_le ?_ ?_
      · exact continuous_const
      · exact PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i
  have h_cube_convex : Convex ℝ (triCube c s) := by
    rw [h_cube_eq]
    apply convex_iInter
    intro i
    exact h_slice_convex i
  have h_cube_closed : IsClosed (triCube c s) := by
    rw [h_cube_eq]
    apply isClosed_iInter
    intro i
    exact h_slice_closed i
  exact And.intro h_poly_convex (And.intro h_poly_closed (And.intro h_cube_convex h_cube_closed))

end AdversarialBco.Bit.Aux_tri_poly_cc
