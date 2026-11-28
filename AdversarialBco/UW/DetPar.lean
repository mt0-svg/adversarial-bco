/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.Interfaces

@[expose] public section

/-!
# DET at the table T4U: the hypotheses without the events

`DetBase` (Poly/Df2DetMain.lean) reads its parameters through the record `c.p` alone: the closed forms
`Df2ParFix c.p`, the facts of SI at `c.p` and the rows at `c.p`. This file gives them at the table T4U of Theorem UW:

* `df2ParFix_parW`: `parW d n u` has the closed forms of DET, as `df2oPar d n δ` does;
* `detBaseW`: `DetBase` for a context at T4U, from the rows and the facts of SI at T4U. The confidence `δ` of
  `DetBase` is read by no lemma of DET; it is set to `1/2`.

Every lemma of Poly/Df2Det*.lean stated on `DetBase` or `DetHyp` then holds on a context at T4U.
-/

namespace AdversarialBco.UW

open AdversarialBco.Poly

variable {d : ℕ}

/-- T4U has the closed forms of the parameters that DET reads. -/
theorem df2ParFix_parW (d n : ℕ) (u : ℝ) : Df2ParFix (parW d n u) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The hypotheses of DET without the events for a context at T4U (`c.p = parW d c.n u`), from the rows and the
facts of SI at T4U. -/
theorem detBaseW {c : Df2Ctx d} {π : Df2Path d} {m : ℕ} {u : ℝ} (hp : c.p = parW d c.n u) (hd : 1 ≤ d)
    (hn : 1 ≤ c.n) (heps : c.p.eps ≤ 1 / 2) (rows : Df2Rows c.p d c.n)
    (SI : ∀ g, AdmLoss c.Kt g → Df2SIAt c.p c.Kt g) (hm1 : 1 ≤ m) (hmn : m ≤ c.n) (body : Df2Body d c.p.R c.Kt)
    (hap : ∀ s, ApSpec (c.ap s)) (adm : ∀ s < m, AdmLoss c.Kt (π.g s)) : DetBase c (1 / 2) π m where
  L1 := df2LayerOne_holds
  W := lemmaW
  SI := SI
  hd := hd
  hn := hn
  hδ0 := by norm_num
  hδ1 := by norm_num
  hpar := hp ▸ df2ParFix_parW d c.n u
  heps := heps
  rows := rows
  hm1 := hm1
  hmn := hmn
  body := body
  hap := hap
  adm := adm

end AdversarialBco.UW
