/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLDataV

@[expose] public section

/-!
# The call data of BL's round, part 3: the scalars

`xsix`, `XV.six`: six expressions into the slots `64..69` (the pairs `ℓ`, `r`, `e` of a call), scratch from the slot
`300`. Each expression reads only slots below `64` or in `70..299` (`ROs`), which the block leaves alone, so all six
are evaluated in the environment before the block.
-/

namespace AdversarialBco.Bit.Transfer.BLM.DataM

open AdversarialBco AdversarialBco.Poly.Mach

variable {d : ℕ}

/-- The slots that the block reads and keeps: below `64`, and `70..299`. -/
def RO (y : ℕ) : Prop := y < 64 ∨ (70 ≤ y ∧ y < 300)

/-- Every slot that the expression reads is in `RO`. -/
def ROs : IE → Prop
  | .sc y => RO y
  | .arr _ _ => True
  | .op _ a b => ROs a ∧ ROs b
  | .ediv a b => ROs a ∧ ROs b

/-- Two environments with the same registers and arrays and the same `RO` slots. -/
def SameRO (σ σ' : Env d) : Prop := σ'.nat = σ.nat ∧ σ'.arr = σ.arr ∧ ∀ y, RO y → σ'.sc y = σ.sc y

theorem ROs.eval {σ σ' : Env d} (h : SameRO σ σ') : ∀ {e : IE}, ROs e → e.eval σ' = e.eval σ
  | .sc _, hr => h.2.2 _ hr
  | .arr _ _, _ => by simp only [IE.eval, h.1, h.2.1]
  | .op _ _ _, hr => by simp only [IE.eval, ROs.eval h hr.1, ROs.eval h hr.2]
  | .ediv _ _, hr => by simp only [IE.eval, ROs.eval h hr.1, ROs.eval h hr.2]

theorem ROs.leaves {E : ℕ} {σ σ' : Env d} (h : SameRO σ σ') : ∀ {e : IE}, ROs e → e.Leaves E σ → e.Leaves E σ'
  | .sc _, hr, hl => by simp only [IE.Leaves, h.2.2 _ hr]; exact hl
  | .arr _ _, _, hl => by simp only [IE.Leaves, h.1, h.2.1]; exact hl
  | .op _ _ _, hr, hl => ⟨ROs.leaves h hr.1 hl.1, ROs.leaves h hr.2 hl.2⟩
  | .ediv _ _, hr, hl => ⟨ROs.leaves h hr.1 hl.1, ROs.leaves h hr.2 hl.2⟩

/-- The conditions of one expression of the block: in the layout, reading `RO` slots below `300`, leaves below `2^E`,
top exponent below `ℓ`, value `v` in `σ`. -/
def ScOK (L : Layout) (E ℓ : ℕ) (σ : Env d) (e : IE) (v : ℤ) : Prop :=
  e.WF L 300 ∧ ROs e ∧ 300 + e.scr ≤ L.NS ∧ e.Leaves E σ ∧ e.top E < ℓ ∧ e.eval σ = v

/-- One expression of the block into the slot `x`, from an environment with the `RO` slots of `σ0`. -/
theorem XV.ieRO {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {x E : ℕ} {e : IE} {σ0 σ : Env d}
    {v : ℤ} (hx : 64 ≤ x ∧ x ≤ 69) (hz : σ0.sc sZ = 0) (hok : ScOK L E ℓ σ0 e v) (hR : SameRO σ0 σ) :
    XRunsB L X ℓa ℓ (e.code L sZ x 300) σ e.units (fun σ' =>
      σ'.sc x = v ∧ SameRO σ0 σ' ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = x ∨ 300 ≤ y) (fun _ => False) (fun _ _ => False) σ σ') := by
  obtain ⟨hw, hro, hS, hl, htop, hv⟩ := hok
  have hz' : σ.sc sZ = 0 := by rw [hR.2.2 sZ (Or.inl (by rwgo))]; exact hz
  refine XV.mono (XV.ieRun (E := E) hL hw (by rwgo) (by omega) hS hz' (ROs.leaves hR hro hl) htop
    (by rw [ROs.eval hR hro]; exact hv)) le_rfl fun σ' ⟨h1, _, h3, h4⟩ => ⟨h1, ?_, h3, FrameA.ofP h4⟩
  refine ⟨?_, ?_, fun y hy => ?_⟩
  · rw [funext fun j => h4.1 j not_false]; exact hR.1
  · rw [h4.2.2.1]; exact hR.2.1
  · rw [h4.2.1 y (by unfold RO at hy; omega)]; exact hR.2.2 y hy

/-- `64 := e0; ...; 69 := e5`. -/
def xsix (L : Layout) (e0 e1 e2 e3 e4 e5 : IE) : XCmd :=
  .seq (e0.code L sZ 64 300) (.seq (e1.code L sZ 65 300) (.seq (e2.code L sZ 66 300) (.seq (e3.code L sZ 67 300)
    (.seq (e4.code L sZ 68 300) (e5.code L sZ 69 300)))))

/-- The units of `xsix`. -/
def sixUnits (e0 e1 e2 e3 e4 e5 : IE) : ℕ :=
  e0.units + (e1.units + (e2.units + (e3.units + (e4.units + e5.units))))

set_option maxHeartbeats 2000000 in
/-- **The scalars**: the slots `64..69` get the values of `e0, ..., e5` in `σ`; only these slots and those from `300`
on change. -/
theorem XV.six {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {E : ℕ}
    {e0 e1 e2 e3 e4 e5 : IE} {v0 v1 v2 v3 v4 v5 : ℤ} (hz : σ.sc sZ = 0) (h0 : ScOK L E ℓ σ e0 v0)
    (h1 : ScOK L E ℓ σ e1 v1) (h2 : ScOK L E ℓ σ e2 v2) (h3 : ScOK L E ℓ σ e3 v3) (h4 : ScOK L E ℓ σ e4 v4)
    (h5 : ScOK L E ℓ σ e5 v5) :
    XRunsB L X ℓa ℓ (xsix L e0 e1 e2 e3 e4 e5) σ (sixUnits e0 e1 e2 e3 e4 e5) (fun σ' =>
      σ'.sc 64 = v0 ∧ σ'.sc 65 = v1 ∧ σ'.sc 66 = v2 ∧ σ'.sc 67 = v3 ∧ σ'.sc 68 = v4 ∧ σ'.sc 69 = v5 ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => (64 ≤ y ∧ y ≤ 69) ∨ 300 ≤ y) (fun _ => False) (fun _ _ => False) σ σ') := by
  have R0 : SameRO σ σ := ⟨rfl, rfl, fun _ _ => rfl⟩
  have M : ∀ {x : ℕ} {σ1 σ2 : Env d}, 64 ≤ x ∧ x ≤ 69 →
      FrameA (fun y => y = x ∨ 300 ≤ y) (fun _ => False) (fun _ _ => False) σ1 σ2 →
      FrameA (fun y => (64 ≤ y ∧ y ≤ 69) ∨ 300 ≤ y) (fun _ => False) (fun _ _ => False) σ1 σ2 :=
    fun hx F => F.mono (fun y h => by omega) (fun _ h => h) (fun _ _ h => h)
  refine XV.seq (XV.ieRO hL (x := 64) (by norm_num) hz h0 R0) fun σ1 ⟨a1, R1, d1, F1⟩ => ?_
  refine XV.seq (XV.ieRO hL (x := 65) (by norm_num) hz h1 R1) fun σ2 ⟨a2, R2, d2, F2⟩ => ?_
  refine XV.seq (XV.ieRO hL (x := 66) (by norm_num) hz h2 R2) fun σ3 ⟨a3, R3, d3, F3⟩ => ?_
  refine XV.seq (XV.ieRO hL (x := 67) (by norm_num) hz h3 R3) fun σ4 ⟨a4, R4, d4, F4⟩ => ?_
  refine XV.seq (XV.ieRO hL (x := 68) (by norm_num) hz h4 R4) fun σ5 ⟨a5, R5, d5, F5⟩ => ?_
  refine XV.mono (XV.ieRO hL (x := 69) (by norm_num) hz h5 R5) le_rfl fun σ6 ⟨a6, _, d6, F6⟩ => ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, a6, ?_, ?_⟩
  · rw [F6.2.1 64 (by omega), F5.2.1 64 (by omega), F4.2.1 64 (by omega), F3.2.1 64 (by omega),
      F2.2.1 64 (by omega)]; exact a1
  · rw [F6.2.1 65 (by omega), F5.2.1 65 (by omega), F4.2.1 65 (by omega), F3.2.1 65 (by omega)]; exact a2
  · rw [F6.2.1 66 (by omega), F5.2.1 66 (by omega), F4.2.1 66 (by omega)]; exact a3
  · rw [F6.2.1 67 (by omega), F5.2.1 67 (by omega)]; exact a4
  · rw [F6.2.1 68 (by omega)]; exact a5
  · rw [d6, d5, d4, d3, d2, d1]
  · exact (((((M (by norm_num) F1).trans (M (by norm_num) F2)).trans (M (by norm_num) F3)).trans
      (M (by norm_num) F4)).trans (M (by norm_num) F5)).trans (M (by norm_num) F6)

end AdversarialBco.Bit.Transfer.BLM.DataM
