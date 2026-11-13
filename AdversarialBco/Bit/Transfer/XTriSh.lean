/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSetupSL

@[expose] public section

/-!
# Straight lines at a base

The straight lines of XBLSetupSL.lean name their slots absolutely, so their static test runs by computation. A routine
whose block starts at a variable slot `o` runs the line with every slot moved by `o` and every register by `r`:

* `IE.shS`, `SStep.shS`: the slot leaves moved by `o`;
* `SL.val_shS`, `SL.chk_shS`, `SL.unitsP_shS`: the values, the static test and the units do not move;
* `SLC.atB`, `XV.slAt`: the rule of the moved line, from the static test of the line at its own slots.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer.BLM

variable {d : ℕ}

/-- The expression with every slot leaf moved by `o`. -/
def IE.shS (o : ℕ) : IE → IE
  | .sc y => .sc (y + o)
  | .arr a i => .arr a i
  | .op p a b => .op p (IE.shS o a) (IE.shS o b)
  | .ediv a b => .ediv (IE.shS o a) (IE.shS o b)

theorem slZ_shS (o : ℕ) (g : ℕ → ℤ) : ∀ e : IE, slZ g (e.shS o) = slZ (fun y => g (y + o)) e
  | .sc _ => rfl
  | .arr _ _ => rfl
  | .op p a b => by
    cases p <;> simp only [IE.shS, slZ, slZ_shS o g a, slZ_shS o g b]
  | .ediv a b => by simp only [IE.shS, slZ, slZ_shS o g a, slZ_shS o g b]

theorem ieLvB_shS (o : ℕ) (P : ℕ → Bool) : ∀ e : IE, ieLvB P (e.shS o) = ieLvB (fun y => P (y + o)) e
  | .sc _ => rfl
  | .arr _ _ => rfl
  | .op p a b => by
    cases p <;> simp only [IE.shS, ieLvB, ieLvB_shS o P a, ieLvB_shS o P b]
  | .ediv a b => by simp only [IE.shS, ieLvB, ieLvB_shS o P a, ieLvB_shS o P b]

theorem ieMag_shS (o : ℕ) (f : ℕ → ℕ × ℕ) : ∀ e : IE, ieMag f (e.shS o) = ieMag (fun y => f (y + o)) e
  | .sc _ => rfl
  | .arr _ _ => rfl
  | .op p a b => by
    cases p <;> simp only [IE.shS, ieMag, ieMag_shS o f a, ieMag_shS o f b]
  | .ediv a b => by simp only [IE.shS, ieMag, ieMag_shS o f a]

theorem ieTop_shS (o : ℕ) (f : ℕ → ℕ × ℕ) : ∀ e : IE, ieTop f (e.shS o) = ieTop (fun y => f (y + o)) e
  | .sc _ => rfl
  | .arr _ _ => rfl
  | .op p a b => by
    have h := ieMag_shS o f (.op p a b)
    simp only [IE.shS] at h
    simp only [IE.shS, ieTop, h, ieTop_shS o f a, ieTop_shS o f b]
  | .ediv a b => by simp only [IE.shS, ieTop, ieMag_shS o f a, ieTop_shS o f a, ieTop_shS o f b]

theorem scr_shS (o : ℕ) : ∀ e : IE, (e.shS o).scr = e.scr
  | .sc _ => rfl
  | .arr _ _ => rfl
  | .op p a b => by simp only [IE.shS, IE.scr, scr_shS o a, scr_shS o b]
  | .ediv a b => by simp only [IE.shS, IE.scr, scr_shS o a, scr_shS o b]

theorem units_shS (o : ℕ) : ∀ e : IE, (e.shS o).units = e.units
  | .sc _ => rfl
  | .arr _ _ => rfl
  | .op p a b => by simp only [IE.shS, IE.units, units_shS o a, units_shS o b]
  | .ediv a b => by simp only [IE.shS, IE.units, units_shS o a, units_shS o b]

/-- The step with its slot leaves moved by `o`. -/
def SStep.shS (o : ℕ) : SStep → SStep
  | .ie e => .ie (e.shS o)
  | s => s

theorem getD_shS (o : ℕ) : ∀ (st : List SStep) (k : ℕ),
    (st.map (SStep.shS o)).getD k (.cst 0) = SStep.shS o (st.getD k (.cst 0))
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: rest, k + 1 => getD_shS o rest k

theorem sem_shS (o b : ℕ) (ι v : ℕ → ℤ) (s : SStep) :
    (SStep.shS o s).sem (b + o) ι v = s.sem b (fun y => ι (y + o)) v := by
  cases s with
  | ie e =>
    simp only [SStep.shS, SStep.sem, slZ_shS]
    congr 1
    funext y
    simp only [Nat.add_lt_add_iff_right, Nat.add_sub_add_right]
  | _ => rfl

theorem SL.val_shS (o : ℕ) (st : List SStep) (b : ℕ) (ι : ℕ → ℤ) (k : ℕ) :
    SL.val (st.map (SStep.shS o)) (b + o) ι k = SL.val st b (fun y => ι (y + o)) k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [SL.val_eq, SL.val_eq, getD_shS, sem_shS]
    congr 1
    funext j
    split_ifs with h
    · exact ih j h
    · rfl

theorem chk_shS (o b k : ℕ) (ins : List ℕ) (eIn et : ℕ → ℕ × ℕ) (T : ℕ × ℕ) (S : ℕ) (s : SStep) :
    (SStep.shS o s).chk (b + o) k (ins.map (· + o)) (fun y => eIn (y - o)) et T S = s.chk b k ins eIn et T S := by
  cases s with
  | ie e =>
    simp only [SStep.shS, SStep.chk, ieLvB_shS, ieMag_shS, ieTop_shS, scr_shS]
    have h1 : (fun y => (decide (y + o < b + o) && (ins.map (· + o)).contains (y + o)) ||
        (decide (b + o ≤ y + o) && decide (y + o < b + o + k))) =
        fun y => (decide (y < b) && ins.contains y) || (decide (b ≤ y) && decide (y < b + k)) := by
      funext y
      have hc : (ins.map (· + o)).contains (y + o) = ins.contains y := by
        rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
        exact ⟨fun ⟨a, ha, he⟩ => by rw [show y = a by omega]; exact ha, fun h => ⟨y, h, rfl⟩⟩
      rw [hc]
      simp only [Nat.add_lt_add_iff_right, Nat.add_le_add_iff_right, show b + o + k = b + k + o by omega]
    have h2 : (fun y => if y + o < b + o then eIn (y + o - o) else et (y + o - (b + o))) =
        fun y => if y < b then eIn y else et (y - b) := by
      funext y
      simp only [Nat.add_lt_add_iff_right, Nat.add_sub_cancel, Nat.add_sub_add_right]
    rw [h1, h2]
  | _ => rfl

theorem SL.chkAux_shS (o b : ℕ) (ins : List ℕ) (eIn et : ℕ → ℕ × ℕ) (T : ℕ × ℕ) (S : ℕ) :
    ∀ (st : List SStep) (k : ℕ), SL.chkAux (b + o) (ins.map (· + o)) (fun y => eIn (y - o)) et T S
      (st.map (SStep.shS o)) k = SL.chkAux b ins eIn et T S st k
  | [], _ => rfl
  | s :: rest, k => by
    simp only [List.map_cons, SL.chkAux, chk_shS, SL.chkAux_shS o b ins eIn et T S rest (k + 1)]

theorem SL.chk_shS (o b : ℕ) (ins : List ℕ) (eIn et : ℕ → ℕ × ℕ) (T : ℕ × ℕ) (S : ℕ) (st : List SStep) :
    SL.chk (b + o) (ins.map (· + o)) (fun y => eIn (y - o)) et T S (st.map (SStep.shS o)) =
      SL.chk b ins eIn et T S st := by
  simp only [SL.chk, SL.chkAux_shS, List.all_map]
  congr 1
  congr 1
  funext y
  simp only [Function.comp_apply, Nat.add_lt_add_iff_right]

theorem SL.unitsP_shS (o : ℕ) (et : ℕ → ℕ × ℕ) :
    ∀ st : List SStep, SL.unitsP et (st.map (SStep.shS o)) = SL.unitsP et st
  | [] => rfl
  | s :: rest => by
    have h : (SStep.shS o s).unitsP et = s.unitsP et := by
      cases s with
      | ie e => simp only [SStep.shS, SStep.unitsP, units_shS]
      | _ => rfl
    simp only [List.map_cons, SL.unitsP, h, SL.unitsP_shS o et rest]

theorem Sem_shS (o : ℕ) (v : ℕ → ℤ) (G : ℕ) (s : SStep) : (SStep.shS o s).Sem v G ↔ s.Sem v G := by
  cases s <;> rfl

/-- The cells of a straight line with its slots moved by `o` and its registers by `r`. -/
def SLC.atB (o r : ℕ) (C : SLC) : SLC :=
  ⟨C.b + o, C.t + o, C.z + o, C.one + o, C.two + o, C.four + o, C.r1 + r, C.r2 + r, C.n1 + r⟩

set_option maxHeartbeats 1000000 in
/-- **The run of a straight line at a base**: the line `st` with its slots moved by `o` (`st.map (SStep.shS o)`, the
cells `SLC.atB o r C`) runs as `XV.sl` from the static test of `st` at its own slots. Its input `y ∈ ins` is the slot
`y + o`; the slot `C.b + o + k` ends holding the value of step `k` of `st`. -/
theorem XV.slAt {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {C : SLC} {S G o r : ℕ}
    (hC : (SLC.atB o r C).OK L S) {st : List SStep} {ι : ℕ → ℤ} {ins : List ℕ} {eIn et : ℕ → ℕ × ℕ} {T : ℕ × ℕ}
    (hchk : SL.chk C.b ins eIn et T S st = true)
    (hsem : ∀ k < st.length, (st.getD k (.cst 0)).Sem (SL.val st C.b ι) G)
    (hlen : C.b + st.length ≤ C.t) (hT : ev G T < ℓ) (hTa : ev G T < 2 ^ ℓa)
    (hinB : ∀ y ∈ ins, |ι y| ≤ 2 ^ ev G (eIn y))
    {σ : Env d} (hin : ∀ y ∈ ins, σ.sc (y + o) = ι y)
    (hz : σ.sc (C.z + o) = 0) (h1 : σ.sc (C.one + o) = 1) (h2 : σ.sc (C.two + o) = 2)
    (h4 : σ.sc (C.four + o) = 4) (hn1 : σ.nat (C.n1 + r) = 1) :
    XRunsB L X ℓa ℓ (SL.code L (SLC.atB o r C) (st.map (SStep.shS o))) σ (ev G (SL.unitsP et st)) (fun σ' =>
      (∀ k < st.length, σ'.sc (C.b + o + k) = SL.val st C.b ι k) ∧ σ'.draws = σ.draws ∧
      FrameP (fun y => (C.b + o ≤ y ∧ y < C.b + o + st.length) ∨ C.t + o ≤ y)
        (fun j => j = C.r1 + r ∨ j = C.r2 + r) σ σ') := by
  have hval : ∀ k, SL.val (st.map (SStep.shS o)) (C.b + o) (fun y => ι (y - o)) k = SL.val st C.b ι k := by
    intro k
    rw [SL.val_shS]
    congr 1
    funext y
    simp only [Nat.add_sub_cancel]
  have hlen' : (st.map (SStep.shS o)).length = st.length := List.length_map _
  have h := XV.sl (X := X) hL hC (st := st.map (SStep.shS o)) (ι := fun y => ι (y - o)) (ins := ins.map (· + o))
    (eIn := fun y => eIn (y - o)) (et := et) (T := T) (G := G)
    (by simp only [SLC.atB]; rw [SL.chk_shS]; exact hchk)
    (fun k hk => by
      rw [hlen'] at hk
      rw [getD_shS, Sem_shS]
      have hv : SL.val (st.map (SStep.shS o)) (C.b + o) (fun y => ι (y - o)) = SL.val st C.b ι := funext hval
      simp only [SLC.atB]; rw [hv]; exact hsem k hk)
    (by simp only [SLC.atB, hlen']; omega) hT hTa
    (fun y hy => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hy
      simp only [Nat.add_sub_cancel]; exact hinB a ha)
    (fun y hy => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hy
      simp only [Nat.add_sub_cancel]; exact hin a ha)
    hz h1 h2 h4 hn1
  rw [SL.unitsP_shS] at h
  refine XV.mono h le_rfl fun σ' ⟨hv, hd, hF⟩ => ⟨fun k hk => ?_, hd, ?_⟩
  · have := hv k (by rw [hlen']; exact hk)
    simp only [SLC.atB] at this
    rw [this, hval]
  · simp only [SLC.atB, hlen'] at hF
    exact hF

end AdversarialBco.Bit.Transfer
