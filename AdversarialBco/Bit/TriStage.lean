/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.TriSamp2
public import AdversarialBco.Bit.ShadowIface

@[expose] public section

/-!
# The stages of TRI-OGD: the sampler's block and the good stages

`triBg d = 4 k_g`, the coins of one block of the sampler (`triBg_ge`: at least `8`), and `TriStageGood`, what holds
after the first `i` stages: a good position for `K ∩ triCube c (2^{i+1} r0)` at the radius `36.4 d λ(ρ_h)`. The
stages of TRI-OGD-O (Unified/PosStage.lean) are stated with them.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius

namespace AdversarialBco.Bit

open AdversarialBco.Poly

/-- The core on the polytope `{y | ⟪α_k, y⟫ ≤ β_k}` with the parameters of dimension `d` and the integer majorant `ℓ`
of `log(1/δ')`, on the draws `y`: the average of `N' = 2^n` steps of rounded projected subgradient descent on the
box, from `(0, I)`. -/
noncomputable def triCoreOut (d : ℕ) {m : ℕ} (α : Fin m → EuclideanSpace ℝ (Fin d)) (β : Fin m → ℝ) (ℓ : ℕ)
    (y : ℕ → EuclideanSpace ℝ (Fin d)) : PgSp d :=
  triAvg (triR d) (triA d) (triB d) (1 / 2 ^ triJs d ℓ) (fun x w => triRound (triBv d) (triV (triU α β) x w)) y
    (2 ^ triNe d ℓ)

/-- **The core theorem, on rows**: for a polytope `K = {y | ⟪α_k, y⟫ ≤ β_k}` with
`PgBody K ρ_a`, an integer `ℓ ≥ log(1/δ)`, and draws independent with the law of the sampler at `B_g = 4 k_g` bits,
the core returns a good position for `K` at the radius `36.4 d λ(ρ_h)` outside an event of probability `δ`. -/
theorem triCoreRows (d : ℕ) (hd : 1 ≤ d) {m : ℕ} (α : Fin m → EuclideanSpace ℝ (Fin d)) (β : Fin m → ℝ)
    (hK : PgBody {y | ∀ k, inner ℝ (α k) y ≤ β k} (triRa d)) (ℓ : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hℓ : Real.log (1 / δ) ≤ ℓ)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (y : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hy : ∀ t, Measurable (y t)) (hind : iIndepFun y P)
    (hlaw : ∀ t, P.map (y t) = gsLaw d (4 * triKg d))
    (hyM : ∀ t ω, ‖y t ω‖ ≤ Real.sqrt (2 * d * (4 * triKg d : ℕ))) :
    P {ω | ¬ PgGood d {y | ∀ k, inner ℝ (α k) y ≤ β k} (36.4 * d * pgLam (triRh d))
      (some (triCoreOut d α β ℓ fun t => y t ω))} ≤ ENNReal.ofReal δ := by
  set K := {y : EuclideanSpace ℝ (Fin d) | ∀ k, inner ℝ (α k) y ≤ β k} with hKdef
  obtain ⟨hρa, hρρ, hr, ha0, ha, ha1, hb1, hb⟩ := tri_par_box d hd
  obtain ⟨hGu0, hGu⟩ := tri_par_Gu d hd
  obtain ⟨hD0, hrow⟩ := tri_par_row d ℓ hd δ hδ0 hδ1 hℓ
  have hαβ : ∀ k, ‖α k‖ ≤ β k := rows_norm_le α β hK.2.2.1
  have hkg : 2 ≤ triKg d := le_max_left _ _
  have hB8 : 8 ≤ 4 * triKg d := by omega
  obtain ⟨hlip, hgn⟩ := tri_gauge K hK.1 hK.2.2.1
  have hb0 : 0 ≤ triB d := by linarith
  -- the coupling of the objective on the box
  have hcpl : ∀ x ∈ triBox d (triR d) (triA d) (triB d),
      |∫ w, gauge K (pgMu x + pgOp x w) ∂(gsLaw d (4 * triKg d)) - posK K (pgMu x) (pgOp x)| ≤ triEpsG d := by
    intro x hx
    have h1 := gs_cpl d (4 * triKg d) hB8 (gauge K) hlip (fun z => by rw [abs_of_nonneg (hgn z).1]; exact (hgn z).2)
      (pgMu x) (pgOp x)
    have h2 := tri_opNorm (triR d) (triA d) (triB d) ha0.le x hx
    have h3 := tri_epsG_le d (triKg d) hd hkg (triB d) hb0
    have hε : 0 ≤ gsEps (4 * triKg d) := by unfold gsEps; positivity
    unfold posK posF
    refine h1.trans ((mul_le_mul_of_nonneg_right h2 (by positivity)).trans ?_)
    unfold triEpsG
    convert h3 using 2
  have hVt : Measurable (Function.uncurry fun x w => triRound (triBv d) (triV (triU α β) x w)) :=
    (tri_round_meas (triBv d)).comp (tri_V_meas (triU α β) (triU_meas α β))
  have hβ : ∀ x ∈ triBox d (triR d) (triA d) (triB d), ∀ w, ‖w‖ ≤ Real.sqrt (8 * d * triKg d) →
      ‖triRound (triBv d) (triV (triU α β) x w) - triV (triU α β) x w‖ ≤ triBu d :=
    fun x _ w _ => tri_round_err (triBv d) _
  have hΔ0 : 0 < Real.sqrt (triD2 d) := Real.sqrt_pos.2 hD0
  have hΔ : 4 * d * triR d ^ 2 + d * (triB d - triA d) ^ 2 + 2 * d * (d - 1) * triB d ^ 2 ≤
      Real.sqrt (triD2 d) ^ 2 := by rw [Real.sq_sqrt hD0.le]; rfl
  have hyM' : ∀ t ω, ‖y t ω‖ ≤ Real.sqrt (8 * d * triKg d) := by
    intro t ω
    refine (hyM t ω).trans (le_of_eq ?_)
    congr 1
    push_cast
    ring
  have := triCore d hd (triRa d) (triRh d) hρa hρρ K hK (triU α β) (fun z => (triU_spec α β hαβ z).1)
    (fun z => (triU_spec α β hαβ z).2.1) (fun z => (triU_spec α β hαβ z).2.2) (triR d) (triA d) (triB d) hr ha0
    ha ha1 hb1 hb (gsLaw d (4 * triKg d)) (triEpsG d) hcpl
    (fun x w => triRound (triBv d) (triV (triU α β) x w)) hVt (Real.sqrt (8 * d * triKg d)) (triBu d)
    (by unfold triBu; positivity) hβ (triGu d) (Real.sqrt (triD2 d)) (1 / 2 ^ triJs d ℓ) hGu0 hGu hΔ0 hΔ
    (by positivity) (2 ^ triNe d ℓ) (by positivity) δ hδ0 hδ1 hrow P y hy hind hlaw hyM'
  exact this

open AdversarialBco.Poly

variable {d : ℕ}

/-! ## The stages -/

/-- `B_g = 4 k_g`, the coins of one block of the sampler. -/
noncomputable def triBg (d : ℕ) : ℕ := 4 * triKg d

/-- What holds after the first `i` stages: nothing after none; after stage `i`, a good position for
`K ∩ triCube c (2^{i+1} r0)` at the radius `36.4 d λ(ρ_h)`. -/
def TriStageGood (K : Set (EuclideanSpace ℝ (Fin d))) (c : EuclideanSpace ℝ (Fin d)) (r0 : ℝ) :
    ℕ → PgSp d → Prop
  | 0, _ => True
  | i + 1, P => PgGood d (K ∩ triCube c (2 ^ (i + 1) * r0)) (36.4 * d * pgLam (triRh d)) (some P)

theorem triBg_ge (d : ℕ) : 8 ≤ triBg d := by
  have := le_max_left 2 (Nat.clog 2 ⌈16 * triB d * (d + 1) * d * (8 * d + 2) / triElo d⌉₊)
  unfold triBg triKg; omega

end AdversarialBco.Bit
