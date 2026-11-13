/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1.Cara
public import AdversarialBco.Poly.Df2WorldVE

@[expose] public section

/-!
# The instance of an epoch with a loss parameter

The instance of an epoch at the start round `a` with the parameter enlarged from the position `q` to the pair `(q, l)`,
`l` the parameter of the loss process: the body is `kTh q`, and the loss of round `s` is `f_{a+s}(S⁻¹ ·)/2` on
`PgGood`. `ext_kTh_measAd`: the extension `df2Ext` of that loss is jointly measurable in `((q, l), y)`, from the
Carathéodory lemma on the interior of `K` (`Conj1.measurable_piecewise_interior`). `lamAt`: the loss parameter read by
round `s` of the instance.
-/

open MeasureTheory ProbabilityTheory Matrix
open AdversarialBco.RealRAM

namespace AdversarialBco.Poly.Conj1

open Layer2

variable {d : ℕ}

/-! ## (L1) for the instance with the loss parameter -/

theorem ext_kTh_measAd {n : ℕ} {δ : ℝ} {K : Set (E d)} (hKc : IsClosed K) (hKconv : Convex ℝ K)
    (hG : PgGoodMeas) (hR : 1 ≤ (df2oPar d n δ).R) (hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d)
    (heps0 : 0 < (df2oPar d n δ).eps) (heps1 : (df2oPar d n δ).eps < 1) {Λ : Type} [MeasurableSpace Λ]
    {L : ℕ → Λ → E d → ℝ} {a s : ℕ} (hconv : ∀ l, ConvexOn ℝ K (L (a + s) l))
    (hm : ∀ y ∈ interior K, Measurable fun l => L (a + s) l y) :
    Measurable fun p : (PgSp d × Λ) × E d =>
      df2Ext (df2oPar d n δ) (kTh n δ K p.1.1) (gTh n δ K (fun t => L t p.1.2) a s p.1.1) p.2 := by
  classical
  set P : (PgSp d × Λ) × E d → ℝ := fun p => df2Pip (df2oPar d n δ) (kTh n δ K p.1.1) p.2 with hPdef
  have hP : Measurable P :=
    measurable_const.max (((gauge_kTh_meas hKc hKconv hG hR hmw).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).div_const _)
  set F : Λ × E d → ℝ := fun p => (interior K).piecewise (L (a + s) p.1) 0 p.2 with hFdef
  have hF : Measurable F := Conj1.measurable_piecewise_interior K (L (a + s)) hconv hm
  have hGs : MeasurableSet {p : (PgSp d × Λ) × E d | PgGood d K (df2oPar d n δ).R (some p.1.1)} :=
    (measurable_fst.comp measurable_fst) (hG d K _ hKconv hKc)
  have hpt : Measurable fun p : (PgSp d × Λ) × E d => pgMu p.1.1 + pgOp p.1.1 ((P p)⁻¹ • p.2) :=
    (pg_continuous d).2.2.measurable.comp ((measurable_fst.comp measurable_fst).prodMk (hP.inv.smul measurable_snd))
  have heq : (fun p : (PgSp d × Λ) × E d =>
      df2Ext (df2oPar d n δ) (kTh n δ K p.1.1) (gTh n δ K (fun t => L t p.1.2) a s p.1.1) p.2) =
      fun p => P p * (if PgGood d K (df2oPar d n δ).R (some p.1.1) then
          F (p.1.2, pgMu p.1.1 + pgOp p.1.1 ((P p)⁻¹ • p.2)) / 2 else 0) +
        2 * (P p - 1) / (df2oPar d n δ).eps := by
    funext p
    by_cases hq : PgGood d K (df2oPar d n δ).R (some p.1.1)
    · have hin := play_interior hKconv hq heps0 heps1 p.2
      have hk := kTh_good (n := n) (δ := δ) hq
      simp only [hPdef, hk, df2Ext, gTh, hq, ↓reduceIte, hFdef]
      rw [Set.piecewise_eq_of_mem _ _ _ hin]
    · simp [df2Ext, hPdef, gTh, hq]
  rw [heq]
  exact (hP.mul (Measurable.ite hGs ((hF.comp ((measurable_snd.comp measurable_fst).prodMk hpt)).div_const 2)
    measurable_const)).add (((hP.sub measurable_const).const_mul 2).div_const _)

/-! ## The parameter of the instance -/

/-- The loss parameter read by round `s` of the instance at the start round `a`: `lam (a + s)` below the horizon,
`lam a` past it (never read). -/
noncomputable def lamAt {Λ : Type} (n : ℕ) (lam : ℕ → WΩ → Λ) (a s : ℕ) (ω : WΩ) : Λ :=
  if a + s < n then lam (a + s) ω else lam a ω

end AdversarialBco.Poly.Conj1
