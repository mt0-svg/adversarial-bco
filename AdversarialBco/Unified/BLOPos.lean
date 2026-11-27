/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.BLOParam

@[expose] public section

/-!
# BL-O: TRI-OGD-O in rationals against `triPosT`

* `posCastO : PosCastO`: the cast of BL-O's position `posO` (Unified/BLOSpec.lean) is `UniPos.triPosT`
  (Unified/PosStage.lean) with the real field `stSepR`;
* `posFieldMeasO : PosFieldMeasO`: the real field vanishes off the countable set of rational points, so it is
  measurable (`triPosT_bad_sep`'s `hgs`).
-/

namespace AdversarialBco.Unified.BLO

open AdversarialBco AdversarialBco.Poly AdversarialBco.Bit AdversarialBco.Bit.RQ
open AdversarialBco.Bit.BLP (cM)
open AdversarialBco.BitRAM (toE)

variable {d : ℕ}

/-! ## The constants of TRI-OGD-O -/

theorem triNeT_eq (d ℓ : ℕ) : triNeTQ d ℓ = UniPos.triNeT d ℓ := by
  unfold triNeTQ UniPos.triNeT
  rw [triNe_eq]

theorem triGuT_cast (d : ℕ) : (triGuTQ d : ℝ) = UniPos.triGuT d := by
  unfold triGuTQ UniPos.triGuT
  push_cast
  rw [triGu_cast]

theorem triJsT_eq (d ℓ : ℕ) : triJsTQ d ℓ = UniPos.triJsT d ℓ := by
  unfold triJsTQ UniPos.triJsT
  rw [← natCeil_ratCast]
  push_cast
  rw [triGuT_cast, triBu_cast, triNeT_eq, triD2_cast]

theorem triLT_eq (d ℓ : ℕ) : triLTQ d ℓ = UniPos.triLT d ℓ := by
  unfold triLTQ UniPos.triLT
  rw [triNeT_eq, triBg_eq]

/-! ## The core, the stages, the position -/

theorem toE_injective {z z' : Fin d → ℚ} (h : toE z = toE z') : z = z' := by
  funext i
  have := congrArg (fun v : E d => v i) h
  simpa [toE] using this

theorem triCoreOutT_cast (d ℓ : ℕ) (u : (Fin d → ℚ) → Fin d → ℚ) (g : E d → E d)
    (hU : ∀ z, g (toE z) = toE (u z)) (y : ℕ → Fin d → ℚ) :
    UniPos.triCoreOutT d ℓ g (fun t => toE (y t)) = castP (triCoreOutOQ d ℓ u y) := by
  unfold UniPos.triCoreOutT triCoreOutOQ
  have hV : ∀ x w, (fun x w => triRound (triBvQ d) (triV g x w)) (castP x) (toE w) =
      castP ((fun x w => triRoundQ (triBvQ d) (triVQ u x w)) x w) := by
    intro x w
    simp only
    rw [triV_cast u g hU x w, triRound_cast]
  rw [← triR_cast, ← triA_cast, ← triB_cast, ← triNeT_eq, ← triJsT_eq, ← triBv_eq]
  have hs : ((1 : ℝ) / 2 ^ triJsTQ d ℓ) = ((1 / 2 ^ triJsTQ d ℓ : ℚ) : ℝ) := by push_cast; ring
  rw [hs]
  exact triAvg_cast _ _ _ _ _ _ hV y _

theorem triStepT_cast (gsQ : ℕ → PosQ d → (Fin d → ℚ) → Fin d → ℚ) (gsR : ℕ → PgSp d → E d → E d) (ℓ j : ℕ)
    (P : PosQ d) (x : ℕ → Bool) (hg : ∀ z, gsR j (castP P) (toE z) = toE (gsQ j P z)) :
    UniPos.triStepT gsR ℓ j (castP P) x = castP (triStepOQ gsQ ℓ j P x) := by
  unfold UniPos.triStepT triStepOQ
  have hD : (fun t => triDraw d (triBg d) x t) = fun t => toE (triDrawQ d (triBgQ d) x t) := by
    funext t
    rw [triDraw_cast, triBg_eq]
  rw [hD, triCoreOutT_cast d ℓ (gsQ j P) (gsR j (castP P)) hg, pgComp_cast]

theorem triStageNT_cast (gsQ : ℕ → PosQ d → (Fin d → ℚ) → Fin d → ℚ) (gsR : ℕ → PgSp d → E d → E d)
    (hg : ∀ j P z, gsR j (castP P) (toE z) = toE (gsQ j P z)) (c : Fin d → ℚ) (r0 : ℚ) (ℓ : ℕ)
    (ω : ℕ → ℕ → Bool) (J : ℕ) :
    UniPos.triStageNT gsR (toE c) (r0 : ℝ) ℓ ω J = castP (triStageNOQ gsQ c r0 ℓ ω J) := by
  induction J with
  | zero =>
    show pgPack (toE c) ((r0 : ℝ) • 1) = pgPack (toE c) (cM (r0 • 1))
    congr 1
    ext i j
    simp only [cM, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  | succ J ih =>
    show UniPos.triStepT gsR ℓ J (UniPos.triStageNT gsR (toE c) (r0 : ℝ) ℓ ω J) (ω J) =
      castP (triStepOQ gsQ ℓ J (triStageNOQ gsQ c r0 ℓ ω J) (ω J))
    rw [ih, triStepT_cast gsQ gsR ℓ J _ _ (hg J _)]

theorem stSepR_cast (orc : (Fin d → ℚ) → ℕ → Bool) (a : Fin d → ℚ) (r0 R0 : ℚ) (j : ℕ) (P : PosQ d)
    (z : Fin d → ℚ) : stSepR orc a r0 R0 j (castP P) (toE z) = toE (stSep orc a r0 R0 j P z) := by
  have hex : ∃ q : PosQ d × (Fin d → ℚ), castP q.1 = castP P ∧ toE q.2 = toE z := ⟨(P, z), rfl, rfl⟩
  unfold stSepR
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := Classical.choose_spec hex
  rw [castP_injective h1, toE_injective h2]

theorem posCastO : PosCastO := by
  intro d n orc δ r0 R0 a cs _ _
  unfold posO triPosOQ UniPos.triPosT
  rw [← triMst_eq, ← triLT_eq, triStageNT_cast _ _ (fun j P z => stSepR_cast orc a r0 R0 j P z)]

/-! ## The measurability of the field -/

theorem posFieldMeasO : PosFieldMeasO := by
  intro d orc a r0 R0 j
  apply UniPos.upos_measurable_of_countable _ _ UniPos.upos_countable_ratPt
  rintro ⟨P, z⟩ hq
  simp only [stSepR]
  rw [dif_neg]
  rintro ⟨q, h1, h2⟩
  apply hq
  refine ⟨fun k => ?_, fun i => ?_⟩
  · rw [← h1]
    rcases k with i | ⟨i, i'⟩
    · exact ⟨q.1.1 i, rfl⟩
    · exact ⟨q.1.2 i i', rfl⟩
  · rw [← h2]
    exact ⟨q.2 i, rfl⟩

/-! ## From TRI-OGD-O's good position to the configuration's -/

/-- A good position of `triPosT`'s output in the sense of `PgGood` is a good position of BL-O's configuration. -/
theorem goodPos_of_pgGood (d n : ℕ) (orc : (Fin d → ℚ) → ℕ → Bool) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (cs : ℕ → Bool)
    (K : Set (E d)) (Rg : ℝ) (h : PgGood d K Rg (some (castP (posO d n orc δ r0 R0 a cs)))) :
    GoodPos K (cfgO d n orc δ r0 R0 a cs) Rg := by
  obtain ⟨P, hP, -, h1, h2, -⟩ := h
  cases hP
  exact ⟨h1, h2⟩

end AdversarialBco.Unified.BLO
