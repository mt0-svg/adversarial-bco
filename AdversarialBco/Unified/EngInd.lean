/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EngRec

@[expose] public section

/-!
# Step 1 of SHADOW for BL-O's record: the induction `IND(t)`

The facts of Bit/BLEngine.lean for BL-O's record `recO` (Unified/AsmRec.lean) at `k = k_δ`:

* the epoch start: `ε ≤ ε' ≤ 1/2` (`eps_factsK`, Theorem BUD at `k`), and `0 < ε < 1` at P°'s parameters in the case
  `ε ≤ 1/4` (`eps01`, with `deltaO_lt_one`);
* the frame of BL-O's configuration on an input of `TheoremUnified` (`frameW`), and a good position of `PgGood` as a
  good position of BL-O's configuration (`goodPos_of_pg`);
* the round: the algebra `y_alg'` of the coupled observation with the shift `(m, r)` named.
-/

open MeasureTheory

namespace AdversarialBco.Unified.Eng

open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.Layer2 AdversarialBco.Bit.Cpl
open AdversarialBco.Unified.World AdversarialBco.Unified.BLO AdversarialBco.Unified.Asm
open AdversarialBco.Unified.BudK (BudOK RunCaseK poK parK budO)
open AdversarialBco.Bit.BLP (Par St Mode init refX refPt cV cM opN)
open AdversarialBco.BitRAM (toE)
open AdversarialBco.Poly.Conj1 (fL)
open Matrix

variable {d : ℕ}

/-! ## The epoch start -/

theorem deltaO_lt_one (d n k : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) : deltaO d n k < 1 :=
  (BudK.deltaO_le d n k hd hn).trans_lt (Bit.Asm.deltaBL_lt_one hd hn)

/-- Lemma ENC on `ε` at `k`: `0 < ε ≤ ε' ≤ 1/2` and `ε' - ε ≤ w_ε`. -/
theorem eps_factsK {d n k : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (hc : RunCaseK d n k) (hbud : BudOK d n k) :
    0 < (poK d n k).eps ∧ (poK d n k).eps ≤ ((parK d n k).eps : ℝ) ∧ ((parK d n k).eps : ℝ) ≤ 1 / 2 ∧
      ((parK d n k).eps : ℝ) - (poK d n k).eps ≤ BudK.we d n k := by
  have H := rowHyp_of d n (deltaO d n k) hd hn (deltaO_pos d n k hd hn) (deltaO_lt_one d n k hd hn)
    (hc.trans (by norm_num))
  have h0 : 0 < (poK d n k).eps := eps_pos_of_rows H
  have h1 := hbud.enc.eps_le
  have h2 := hbud.enc.eps_rel
  have htp0 : 0 ≤ BudK.tp d n k := by unfold BudK.tp; positivity
  have htp1 : BudK.tp d n k ≤ 1 := by
    unfold BudK.tp; rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hc' : (poK d n k).eps ≤ 1 / 4 := hc
  unfold BudK.eps at h1 h2
  unfold BudK.we BudK.eps
  generalize ((parK d n k).eps : ℝ) = e' at *
  generalize (poK d n k).eps = e at *
  generalize BudK.tp d n k = tp at *
  refine ⟨h0, h1, ?_, ?_⟩ <;> nlinarith

/-- The frame of BL-O's configuration on an input of `TheoremUnified`. -/
theorem frameW {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ} {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool}
    (hI : InpU n δ r0 R0 a K orc) (w : BitRAMO.WorldO d) : FrameO K orc (cfgW d n δ r0 R0 a w) :=
  ⟨hI.convex, hI.compact.isClosed, hI.hr0, hI.hrR, hI.ball_in, hI.ball_out, hI.orc⟩

/-- A good position of `PgGood` is a good position of BL-O's configuration. -/
theorem goodPos_of_pg {K : Set (E d)} {c : CfgO d} {R : ℝ} (h : PgGood d K R (some c.S)) : GoodPos K c R := by
  obtain ⟨P, hP, -, h1, h2, -⟩ := h
  obtain rfl := Option.some_inj.1 hP
  exact ⟨h1, h2⟩

/-! ## The round -/

/-- The algebra of the coupled observation with the shift `(m, r)` named. -/
theorem y_alg' {pto pt' F0 F1 nz Z e e' m r : ℝ} (hp : pto ≠ 0) (hr : r = pt' / pto)
    (hm : m = (pt' / pto - 1) * nz + (pt' * F1 - pto * F0 + 4 * (pt' - 1) / e' - 4 * (pto - 1) / e) / pto) :
    pto * (F0 / 2 + (nz + (m + r * Z / 2)) / 2) + 2 * (pto - 1) / e =
      pt' * (F1 + nz + Z / 2) / 2 + 2 * (pt' - 1) / e' := by
  subst hr hm
  field_simp
  ring

section Rec

variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {K : Set (E d)} {coin : Ω → ℕ → Bool}
  {loss : ℕ → Ω → E d → ℝ} {noise : ℕ → Ω → ℝ} {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ}
  {orc : (Fin d → ℚ) → ℕ → Bool}

set_option hygiene false in
local notation "BB" => recO n δ r0 R0 a orc h hI.convex
set_option hygiene false in
local notation "WE" => extO n δ r0 R0 a h
set_option hygiene false in
local notation "WW" => envWorld orc coin loss noise ω.1
set_option hygiene false in
local notation "CC" => cfgW d n δ r0 R0 a (envWorld orc coin loss noise ω.1)
set_option hygiene false in
local notation "DB" => dBL d n δ

/-- `0 < ε < 1` at P°'s parameters in the case `ε ≤ 1/4`. -/
theorem eps01 (hI : InpU n δ r0 R0 a K orc) (hc : RunCaseO d n δ) :
    0 < (df2oPar d n (dBL d n δ)).eps ∧ (df2oPar d n (dBL d n δ)).eps < 1 := by
  have H := rowHyp_of d n (dBL d n δ) hI.hd hI.hn (deltaO_pos d n _ hI.hd hI.hn)
    (deltaO_lt_one d n _ hI.hd hI.hn) (hc.trans (by norm_num))
  have hc' : (df2oPar d n (dBL d n δ)).eps ≤ 1 / 4 := hc
  exact ⟨eps_pos_of_rows H, by linarith⟩

end Rec

end AdversarialBco.Unified.Eng
