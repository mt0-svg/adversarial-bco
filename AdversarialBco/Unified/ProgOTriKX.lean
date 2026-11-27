/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOTriStage

@[expose] public section

/-!
# TRI-OGD-O on the oracle machine: the constants of the core step

`TriKX`, the predicate `KX` of `TriStepSpec` and `TriStageSpec` (Unified/ProgOTriStage.lean): the constants the core
step reads besides v2.1's (`TriKV`), each in a fixed cell outside the cells v2.1's pieces of a stage write
(`triKX_stable : KXStable TriKX`).

* the frame centre `a = N_a/D_a` as `(D_a; N_a)` in the array `aKa` and `r₀ = r_n/r_d` in the slots `sR0n`, `sR0d`
  (CM's centre and radius in the stage test, and the cube `|· - a|_∞ ≤ 2^{j+1} r₀`), a representation `P0OK`;
* the centre `0` of the stage gauge as `(1; 0)` in the array `aKg`;
* SEP's constants (`e_L = 0`): `2^E`, `2^{E-e₁}`, `2^{e_τ+4}`, `2^{E+e_τ+1}`, `2^{e_u}` in `sCE`, `sCL1`, `sCSh`, `sCA`,
  `sCB` with `E = stE d`, `e₁ = stE1 d`, `e_τ = triETauQ d`, `e_u = stEu d`, and `J = e_τ + 3` in the register `rNJ`;
* the gauge's constants: `H = 2^{stEH}/1` in `sHn`, `sHd`, the steps `stJ` in `rNj` and `2^{stJ}` in `sC2j`;
* CM's precision `stK d r₀ R₀` in `rNk` and `2^{stK}` in `sC2k`;
* the scale `2^K` of the base point, `K = tKZ d ℓ`, in `sC2K`, and the divisor `2^{stEu + 1}` of SEP's vector in `sBb`.

Here `ℓ = ellO d n δ r₀ R₀`. The slots lie in `100, ..., 112` (below `oT`), the registers in `rT + 30, ..., rT + 32`,
the arrays are `aT + 16`, `aT + 17`.
-/

namespace AdversarialBco.Unified.ProgO.TriO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM
open AdversarialBco.Unified.ProgO

variable {d : ℕ}

/-! ## The cells -/

/-- The array of the frame centre `(D_a; N_a)`. -/
abbrev aKa : ℕ := aT + 16
/-- The array of the gauge's centre `(1; 0)`. -/
abbrev aKg : ℕ := aT + 17
/-- The slot of `r_n`. -/
abbrev sR0n : ℕ := 100
/-- The slot of `r_d`. -/
abbrev sR0d : ℕ := 101
/-- The slot of `2^E`. -/
abbrev sCE : ℕ := 102
/-- The slot of `2^{E - e₁}`. -/
abbrev sCL1 : ℕ := 103
/-- The slot of `2^{e_τ + 4}`. -/
abbrev sCSh : ℕ := 104
/-- The slot of `2^{E + e_τ + 1}`. -/
abbrev sCA : ℕ := 105
/-- The slot of `2^{e_u}`. -/
abbrev sCB : ℕ := 106
/-- The slot of `2^{stEH}`. -/
abbrev sHn : ℕ := 107
/-- The slot of `1`, the denominator of the gauge's `H`. -/
abbrev sHd : ℕ := 108
/-- The slot of `2^{stJ}`. -/
abbrev sC2j : ℕ := 109
/-- The slot of `2^{stK}`. -/
abbrev sC2k : ℕ := 110
/-- The slot of `2^K`, `K = tKZ d ℓ`. -/
abbrev sC2K : ℕ := 111
/-- The slot of `2^{stEu + 1}`. -/
abbrev sBb : ℕ := 112
/-- The register of SEP's `J = e_τ + 3`. -/
abbrev rNJ : ℕ := rT + 30
/-- The register of the gauge's steps `stJ`. -/
abbrev rNj : ℕ := rT + 31
/-- The register of CM's precision `stK`. -/
abbrev rNk : ℕ := rT + 32

/-! ## The constants -/

/-- **The constants of the core step** at a representation `(D_a, N_a, r_n, r_d)` of the frame. -/
structure TriKXAt (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (Da : ℤ) (Na : Fin d → ℤ) (rn rd : ℤ) (σ : Env d) :
    Prop where
  rep : P0OK d n δ r0 R0 a Da Na rn rd
  ka0 : σ.arr aKa 0 = Da
  ka : ∀ i : Fin d, σ.arr aKa (1 + (i : ℕ)) = Na i
  r0n : σ.sc sR0n = rn
  r0d : σ.sc sR0d = rd
  kg0 : σ.arr aKg 0 = 1
  kg : ∀ i : Fin d, σ.arr aKg (1 + (i : ℕ)) = 0
  cE : σ.sc sCE = ((2 ^ stE d : ℤ) : ℝ)
  cL1 : σ.sc sCL1 = ((2 ^ (stE d - stE1 d) : ℤ) : ℝ)
  cSh : σ.sc sCSh = ((2 ^ (triETauQ d + 4) : ℤ) : ℝ)
  cA : σ.sc sCA = ((2 ^ (stE d + triETauQ d + 1) : ℤ) : ℝ)
  cB : σ.sc sCB = ((2 ^ stEu d : ℤ) : ℝ)
  nJ : σ.nat rNJ = triETauQ d + 3
  hn : σ.sc sHn = ((2 ^ stEH d : ℤ) : ℝ)
  hd : σ.sc sHd = 1
  nj : σ.nat rNj = stJ d
  c2j : σ.sc sC2j = ((2 ^ stJ d : ℤ) : ℝ)
  nk : σ.nat rNk = stK d r0 R0
  c2k : σ.sc sC2k = ((2 ^ stK d r0 R0 : ℤ) : ℝ)
  c2K : σ.sc sC2K = ((2 ^ tKZ d (ellO d n δ r0 R0) : ℤ) : ℝ)
  bb : σ.sc sBb = ((tBb d : ℤ) : ℝ)

/-- **The constants of the core step** (`KX`): `TriKXAt` at some representation of the frame. -/
def TriKX : KPred := fun d n δ r0 R0 a σ =>
  ∃ (Da : ℤ) (Na : Fin d → ℤ) (rn rd : ℤ), TriKXAt d n δ r0 R0 a Da Na rn rd σ

/-- The constants survive every change that keeps their cells. -/
theorem TriKXAt.frame {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ} {Da : ℤ} {Na : Fin d → ℤ} {rn rd : ℤ}
    {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop} {σ σ' : Env d} (h : TriKXAt d n δ r0 R0 a Da Na rn rd σ)
    (hF : FrameA S N Ar σ σ') (hS : ∀ y, 100 ≤ y → y ≤ 112 → ¬ S y)
    (hN : ¬ N rNJ ∧ ¬ N rNj ∧ ¬ N rNk) (hA : ∀ k, ¬ Ar aKa k ∧ ¬ Ar aKg k) :
    TriKXAt d n δ r0 R0 a Da Na rn rd σ' := by
  obtain ⟨n1, n2, n3⟩ := hN
  have s : ∀ y, 100 ≤ y → y ≤ 112 → σ'.sc y = σ.sc y := fun y h1 h2 => hF.2.1 _ (hS y h1 h2)
  have ka : ∀ k, σ'.arr aKa k = σ.arr aKa k := fun k => hF.2.2.1 _ _ (hA k).1
  have kg : ∀ k, σ'.arr aKg k = σ.arr aKg k := fun k => hF.2.2.1 _ _ (hA k).2
  exact ⟨h.rep, (ka 0).trans h.ka0, fun i => (ka _).trans (h.ka i), (s _ le_rfl (by norm_num)).trans h.r0n,
    (s _ (by norm_num) (by norm_num)).trans h.r0d, (kg 0).trans h.kg0, fun i => (kg _).trans (h.kg i),
    (s _ (by norm_num) (by norm_num)).trans h.cE, (s _ (by norm_num) (by norm_num)).trans h.cL1,
    (s _ (by norm_num) (by norm_num)).trans h.cSh, (s _ (by norm_num) (by norm_num)).trans h.cA,
    (s _ (by norm_num) (by norm_num)).trans h.cB, (hF.1 _ n1).trans h.nJ,
    (s _ (by norm_num) (by norm_num)).trans h.hn, (s _ (by norm_num) (by norm_num)).trans h.hd,
    (hF.1 _ n2).trans h.nj, (s _ (by norm_num) (by norm_num)).trans h.c2j, (hF.1 _ n3).trans h.nk,
    (s _ (by norm_num) (by norm_num)).trans h.c2k, (s _ (by norm_num) (by norm_num)).trans h.c2K,
    (s _ (by norm_num) le_rfl).trans h.bb⟩

/-- The constants of the core step lie outside the cells of v2.1's pieces of a stage. -/
theorem triKX_stable : KXStable TriKX := by
  intro d n δ r0 R0 a σ σ' ⟨Da, Na, rn, rd, h⟩ hF
  exact ⟨Da, Na, rn, rd, h.frame hF (fun y h1 h2 h => by simp only [oT] at h; omega)
    (by simp only [rNJ, rNj, rNk, rT]; omega) (fun k => by simp only [aKa, aKg, aT]; omega)⟩

end AdversarialBco.Unified.ProgO.TriO
