/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XDriver

@[expose] public section

/-!
# The setup of the registers from the input

`xsetup L dv`, a command of the extended language, run from the zero state: `rS x := x`; `rZ := NS`; the natural
variable `dv` reads `d` from the input cell `0` (through the scalar `0`, by `rdIn` and `rtoN`); `rSZ := d² + d` (by
`nmul`, `nadd`); `rA a := NS + 1 + a (d² + d)`. `xsetup_exec`: it runs within `NS + 2 NA + 7` units to a state that
represents `envSetup dv d` (natural variable `dv` and scalar `0` hold `d`, everything else `0`). This is the setup the
driver `prog_okR` (XDrvReach.lean) asks for; the other inputs (`n`, `m`, the entries of `A` and `b`) are read later by
`XV.rdIn` at addresses computed with `XV.nmul`, `XV.nadd`.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach
open Function

variable {d : ℕ}

/-- `rS x := x` for `x < k`. -/
def xsetRS (L : Layout) : ℕ → XCmd
  | 0 => .skip
  | k + 1 => .seq (xsetRS L k) (.prim (.frag (.nconst (L.rS k) k)))

/-- `rA a := rT + nat (rS 0)`, `rT := rT + rSZ`, for `a < k` (with `rS 0` holding `0`). -/
def xsetRA (L : Layout) : ℕ → XCmd
  | 0 => .skip
  | k + 1 => .seq (xsetRA L k) (.seq (.prim (.frag (.nadd (L.rA k) L.rT (L.rS 0))))
      (.prim (.frag (.nadd L.rT L.rT L.rSZ))))

/-- The setup. -/
def xsetup (L : Layout) (dv : ℕ) : XCmd :=
  .seq (xsetRS L L.NS) (.seq (.prim (.frag (.nconst L.rZ L.NS)))
    (.seq (.prim (.frag (.nconst dv 0))) (.seq (.prim (.leaf (.rdIn (L.rS 0) dv)))
    (.seq (.prim (.leaf (.rtoN dv (L.rS 0)))) (.seq (.prim (.leaf (.nmul L.rSZ dv dv)))
    (.seq (.prim (.frag (.nadd L.rSZ L.rSZ dv))) (.seq (.prim (.frag (.nconst L.rT (L.NS + 1))))
      (xsetRA L L.NA))))))))

/-- The environment after the setup: `d` in the natural variable `dv` and in the scalar `0`. -/
noncomputable def envSetup (dv d : ℕ) : Env d where
  nat := fun i => if i = dv then d else 0
  sc := fun x => if x = 0 then (d : ℝ) else 0
  arr := fun _ _ => 0
  draws := 0
  rounds := 0
  pts := fun _ => 0

variable {X : XCtx d} {ℓa ℓ : ℕ} {L : Layout}

theorem exec_xsetRS (hL : LayOK L d ℓa) (k : ℕ) (hk : k ≤ L.NS) (s : RealRAM.State d) :
    ∃ s', XExecB X ℓa ℓ (xsetRS L k) s k s' ∧ s'.mem = s.mem ∧ s'.draws = s.draws ∧ s'.rounds = s.rounds ∧
      s'.pts = s.pts ∧ (∀ x < k, s'.nreg (L.rS x) = x) ∧ (∀ r, (∀ x < k, r ≠ L.rS x) → s'.nreg r = s.nreg r) := by
  induction k with
  | zero => exact ⟨s, .skip s, rfl, rfl, rfl, rfl, fun x hx => absurd hx (Nat.not_lt_zero _), fun r _ => rfl⟩
  | succ k ih =>
    obtain ⟨s₁, e₁, m₁, d₁, r₁, p₁, h₁, o₁⟩ := ih (by omega)
    have hp : PrimOK ℓa ℓ s₁ (.nconst (L.rS k) k) := by
      have := hL.1; unfold Layout.rS; constructor <;> omega
    refine ⟨_, XExecB.seq e₁ (XExecB.frag _ s₁ hp), m₁, d₁, r₁, p₁, fun x hx => ?_, fun r hr => ?_⟩
    · show update s₁.nreg (L.rS k) k (L.rS x) = x
      by_cases hxk : x = k
      · subst hxk; simp
      · rw [update_of_ne (by unfold Layout.rS; omega)]; exact h₁ x (by omega)
    · show update s₁.nreg (L.rS k) k r = s.nreg r
      rw [update_of_ne (hr k (by omega))]; exact o₁ r fun x hx => hr x (by omega)

theorem exec_xsetRA (hL : LayOK L d ℓa) (k : ℕ) (hk : k ≤ L.NA) (s : RealRAM.State d) (h0 : s.nreg (L.rS 0) = 0)
    (hNS : 1 ≤ L.NS) (hb : s.nreg L.rT + L.NA * s.nreg L.rSZ < 2 ^ ℓa) :
    ∃ s', XExecB X ℓa ℓ (xsetRA L k) s (2 * k) s' ∧ s'.mem = s.mem ∧ s'.draws = s.draws ∧ s'.rounds = s.rounds ∧
      s'.pts = s.pts ∧ (∀ a < k, s'.nreg (L.rA a) = s.nreg L.rT + a * s.nreg L.rSZ) ∧
      s'.nreg L.rT = s.nreg L.rT + k * s.nreg L.rSZ ∧
      (∀ r, r ≠ L.rT → (∀ a < k, r ≠ L.rA a) → s'.nreg r = s.nreg r) := by
  have hL1 := hL.1
  induction k with
  | zero =>
    exact ⟨s, .skip s, rfl, rfl, rfl, rfl, fun a ha => absurd ha (Nat.not_lt_zero _), by simp, fun r _ _ => rfl⟩
  | succ k ih =>
    obtain ⟨s₁, e₁, m₁, d₁, r₁, p₁, h₁, t₁, o₁⟩ := ih (by omega)
    have hkb : s.nreg L.rT + k * s.nreg L.rSZ + s.nreg L.rSZ ≤ s.nreg L.rT + L.NA * s.nreg L.rSZ := by
      have : (k + 1) * s.nreg L.rSZ ≤ L.NA * s.nreg L.rSZ := Nat.mul_le_mul_right _ hk
      rw [Nat.succ_mul] at this; omega
    have hSZ : s.nreg L.rSZ ≤ s.nreg L.rT + L.NA * s.nreg L.rSZ := by omega
    have hS0 : s₁.nreg (L.rS 0) = 0 := by
      rw [o₁ _ (by unfold Layout.rS Layout.rT; omega) (fun a _ => by unfold Layout.rS Layout.rA; omega)]; exact h0
    have hSZ1 : s₁.nreg L.rSZ = s.nreg L.rSZ :=
      o₁ _ (by unfold Layout.rSZ Layout.rT; omega) (fun a _ => by unfold Layout.rSZ Layout.rA; omega)
    have hp1 : PrimOK ℓa ℓ s₁ (.nadd (L.rA k) L.rT (L.rS 0)) := by
      refine ⟨by unfold Layout.rA; omega, ⟨by unfold Layout.rT; omega, by rw [t₁]; omega⟩,
        ⟨by unfold Layout.rS; omega, by rw [hS0]; omega⟩⟩
    set s₂ := (Prim.nadd (L.rA k) L.rT (L.rS 0)).exec X.rw s₁ with hs₂
    have n₂ : ∀ r, r ≠ L.rA k → s₂.nreg r = s₁.nreg r := fun r hr => by
      show update s₁.nreg (L.rA k) _ r = _; rw [update_of_ne hr]
    have hT2 : s₂.nreg L.rT = s₁.nreg L.rT := n₂ _ (by unfold Layout.rT Layout.rA; omega)
    have hSZ2 : s₂.nreg L.rSZ = s.nreg L.rSZ := by rw [n₂ _ (by unfold Layout.rSZ Layout.rA; omega), hSZ1]
    have hp2 : PrimOK ℓa ℓ s₂ (.nadd L.rT L.rT L.rSZ) := by
      refine ⟨by unfold Layout.rT; omega, ⟨by unfold Layout.rT; omega, by rw [hT2, t₁]; omega⟩,
        ⟨by unfold Layout.rSZ; omega, by rw [hSZ2]; omega⟩⟩
    have e : XExecB X ℓa ℓ (xsetRA L (k + 1)) s (2 * k + (1 + 1)) ((Prim.nadd L.rT L.rT L.rSZ).exec X.rw s₂) :=
      XExecB.seq e₁ (XExecB.seq (XExecB.frag _ s₁ hp1) (XExecB.frag _ s₂ hp2))
    refine ⟨(Prim.nadd L.rT L.rT L.rSZ).exec X.rw s₂, by rw [show 2 * (k + 1) = 2 * k + (1 + 1) by ring]; exact e,
      m₁, d₁, r₁, p₁, fun a ha => ?_, ?_,
      fun r hrT hr => ?_⟩
    · show update s₂.nreg L.rT _ (L.rA a) = _
      rw [update_of_ne (by unfold Layout.rT Layout.rA; omega)]
      by_cases hak : a = k
      · subst hak
        show update s₁.nreg (L.rA a) (s₁.nreg L.rT + s₁.nreg (L.rS 0)) (L.rA a) = _
        rw [update_self, hS0, t₁]; ring
      · rw [n₂ _ (by unfold Layout.rA; omega)]; exact h₁ a (by omega)
    · show update s₂.nreg L.rT (s₂.nreg L.rT + s₂.nreg L.rSZ) L.rT = _
      rw [update_self, hT2, hSZ2, t₁, Nat.succ_mul]; ring
    · show update s₂.nreg L.rT _ r = _
      rw [update_of_ne hrT, n₂ _ (hr k (by omega))]
      exact o₁ r hrT fun a ha => hr a (by omega)

/-- The setup represents `envSetup dv d`, within `NS + 2 NA + 7` units. -/
theorem xsetup_exec (hL : LayOK L d ℓa) {dv : ℕ} (hdv : dv < L.NN) (hNS : 1 ≤ L.NS) (hNA : 1 ≤ L.NA)
    (hX0 : X.inp 0 = d) (hoff : 1 ≤ X.off) (hdl : (d : ℝ) < 2 ^ ℓ) :
    ∃ s, XExecB X ℓa ℓ (xsetup L dv) zeroState (L.NS + 2 * L.NA + 7) s ∧ Rep L (envSetup dv d) s := by
  have hL1 := hL.1
  have hL2 := hL.2
  have hbase : L.NS + 1 + L.NA * asz d < 2 ^ ℓa := hL2
  have hasz : asz d ≤ L.NA * asz d := Nat.le_mul_of_pos_left _ hNA
  have hdd : d * d + d < 2 ^ ℓa := by have : asz d = d * d + d := rfl; omega
  have hd2 : d < 2 ^ ℓa := by
    have : d ≤ d * d + d := Nat.le_add_left _ _
    omega
  -- the scalar registers
  obtain ⟨s₁, e₁, m₁, d₁, r₁, p₁, h₁, o₁⟩ := exec_xsetRS (X := X) (ℓ := ℓ) hL L.NS le_rfl (zeroState (d := d))
  have z₁ : ∀ r, (∀ x < L.NS, r ≠ L.rS x) → s₁.nreg r = 0 := fun r hr => o₁ r hr
  -- `rZ := NS`
  have hp2 : PrimOK ℓa ℓ s₁ (.nconst L.rZ L.NS) := ⟨by unfold Layout.rZ; omega, by omega⟩
  set s₂ := (Prim.nconst L.rZ L.NS).exec X.rw s₁
  -- `dv := 0`
  have hp3 : PrimOK ℓa ℓ s₂ (.nconst dv 0) := ⟨by omega, by positivity⟩
  set s₃ := (Prim.nconst dv 0).exec X.rw s₂
  have n₃ : ∀ r, r ≠ dv → r ≠ L.rZ → s₃.nreg r = s₁.nreg r := fun r h1 h2 => by
    show update (update s₁.nreg L.rZ L.NS) dv 0 r = _
    rw [update_of_ne h1, update_of_ne h2]
  have hS3 : s₃.nreg (L.rS 0) = 0 := by
    rw [n₃ _ (by unfold Layout.rS; omega) (by unfold Layout.rS Layout.rZ; omega)]; exact h₁ 0 hNS
  have hdv3 : s₃.nreg dv = 0 := by show update _ dv 0 dv = 0; rw [update_self]
  -- `sc 0 := d` from the input
  have hl4 : LeafOK X ℓa ℓ s₃ (.rdIn (L.rS 0) dv) := by
    refine ⟨⟨by unfold Layout.rS; omega, by rw [hS3]; positivity⟩, ⟨by omega, by rw [hdv3]; positivity⟩,
      by rw [hdv3]; omega, ?_⟩
    rw [hdv3, hX0]; push_cast; rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact hdl
  set s₄ := (Leaf.rdIn (L.rS 0) dv).exec X s₃
  have m₄ : s₄.mem = update (fun _ => 0) 0 (d : ℝ) := by
    show update s₃.mem (s₃.nreg (L.rS 0)) (X.inp (s₃.nreg dv) : ℝ) = _
    rw [hS3, hdv3, hX0]
    have : s₃.mem = fun _ => 0 := m₁
    rw [this]; push_cast; rfl
  have hS4 : s₄.nreg (L.rS 0) = 0 := hS3
  -- `dv := d`
  have hl5 : LeafOK X ℓa ℓ s₄ (.rtoN dv (L.rS 0)) := by
    have hv : s₄.mem (s₄.nreg (L.rS 0)) = d := by rw [hS4, m₄, update_self]
    refine ⟨by omega, ⟨by unfold Layout.rS; omega, by rw [hS4]; positivity⟩, by rw [hv]; positivity, ?_, ?_⟩
    · rw [hv]; exact_mod_cast hd2
    · rw [hv, abs_of_nonneg (Nat.cast_nonneg _)]; exact hdl
  set s₅ := (Leaf.rtoN dv (L.rS 0)).exec X s₄
  have hdv5 : s₅.nreg dv = d := by
    show update s₄.nreg dv (⌊s₄.mem (s₄.nreg (L.rS 0))⌋).toNat dv = d
    rw [update_self, hS4, m₄, update_self, Int.floor_natCast, Int.toNat_natCast]
  -- `rSZ := d * d + d`
  have hl6 : LeafOK X ℓa ℓ s₅ (.nmul L.rSZ dv dv) := by
    refine ⟨by unfold Layout.rSZ; omega, ⟨by omega, by rw [hdv5]; exact hd2⟩, ⟨by omega, by rw [hdv5]; exact hd2⟩, ?_⟩
    rw [hdv5]; omega
  set s₆ := (Leaf.nmul L.rSZ dv dv).exec X s₅
  have hSZ6 : s₆.nreg L.rSZ = d * d := by
    show update s₅.nreg L.rSZ (s₅.nreg dv * s₅.nreg dv) L.rSZ = _; rw [update_self, hdv5]
  have hdv6 : s₆.nreg dv = d := by
    show update s₅.nreg L.rSZ _ dv = _; rw [update_of_ne (by unfold Layout.rSZ; omega)]; exact hdv5
  have hp7 : PrimOK ℓa ℓ s₆ (.nadd L.rSZ L.rSZ dv) :=
    ⟨by unfold Layout.rSZ; omega, ⟨by unfold Layout.rSZ; omega, by rw [hSZ6]; omega⟩, ⟨by omega, by rw [hdv6]; exact hd2⟩⟩
  set s₇ := (Prim.nadd L.rSZ L.rSZ dv).exec X.rw s₆
  have hSZ7 : s₇.nreg L.rSZ = asz d := by
    show update s₆.nreg L.rSZ (s₆.nreg L.rSZ + s₆.nreg dv) L.rSZ = _; rw [update_self, hSZ6, hdv6]; rfl
  -- `rT := NS + 1`
  have hp8 : PrimOK ℓa ℓ s₇ (.nconst L.rT (L.NS + 1)) := ⟨by unfold Layout.rT; omega, by omega⟩
  set s₈ := (Prim.nconst L.rT (L.NS + 1)).exec X.rw s₇
  have hT8 : s₈.nreg L.rT = L.NS + 1 := by show update _ L.rT _ L.rT = _; rw [update_self]
  have hSZ8 : s₈.nreg L.rSZ = asz d := by
    show update _ L.rT _ L.rSZ = _; rw [update_of_ne (by unfold Layout.rT Layout.rSZ; omega)]; exact hSZ7
  -- the registers of `s₈` below the array registers
  have n₈ : ∀ r, r ≠ L.rT → r ≠ L.rSZ → s₈.nreg r = s₅.nreg r := fun r h1 h2 => by
    show update (update (update s₅.nreg L.rSZ _) L.rSZ _) L.rT _ r = _
    rw [update_of_ne h1, update_of_ne h2, update_of_ne h2]
  have n₅ : ∀ r, r ≠ dv → s₅.nreg r = s₃.nreg r := fun r h => by
    show update s₄.nreg dv _ r = _; rw [update_of_ne h]; rfl
  have hS8 : s₈.nreg (L.rS 0) = 0 := by
    rw [n₈ _ (by unfold Layout.rS Layout.rT; omega) (by unfold Layout.rS Layout.rSZ; omega),
      n₅ _ (by unfold Layout.rS; omega)]; exact hS3
  -- the array registers
  obtain ⟨s₉, e₉, m₉, d₉, r₉, p₉, h₉, -, o₉⟩ := exec_xsetRA (X := X) (ℓ := ℓ) hL L.NA le_rfl s₈ hS8 hNS
    (by rw [hT8, hSZ8]; exact hbase)
  have e : XExecB X ℓa ℓ (xsetup L dv) zeroState (L.NS + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 2 * L.NA)))))))) s₉ :=
    XExecB.seq e₁ (XExecB.seq (XExecB.frag _ s₁ hp2) (XExecB.seq (XExecB.frag _ s₂ hp3)
      (XExecB.seq (XExecB.leaf _ s₃ hl4) (XExecB.seq (XExecB.leaf _ s₄ hl5) (XExecB.seq (XExecB.leaf _ s₅ hl6)
      (XExecB.seq (XExecB.frag _ s₆ hp7) (XExecB.seq (XExecB.frag _ s₇ hp8) e₉)))))))
  refine ⟨s₉, by convert e using 1; ring, ?_⟩
  have hm9 : s₉.mem = update (fun _ => 0) 0 (d : ℝ) := by rw [m₉]; exact m₄
  -- the registers of `s₉` outside the array registers and `rT`
  have n₉ : ∀ r, r ≠ L.rT → r ≠ L.rSZ → (∀ a < L.NA, r ≠ L.rA a) → s₉.nreg r = s₅.nreg r := fun r h1 h2 h3 => by
    rw [o₉ r h1 h3, n₈ r h1 h2]
  have nRS : ∀ x < L.NS, s₉.nreg (L.rS x) = x := fun x hx => by
    rw [n₉ _ (by unfold Layout.rS Layout.rT; omega) (by unfold Layout.rS Layout.rSZ; omega)
      (fun a _ => by unfold Layout.rS Layout.rA; omega), n₅ _ (by unfold Layout.rS; omega),
      n₃ _ (by unfold Layout.rS; omega) (by unfold Layout.rS Layout.rZ; omega)]
    exact h₁ x hx
  refine ⟨fun i hi => ?_, ?_, nRS, fun a ha => ?_, fun x hx => ?_, ?_, fun a ha k hk => ?_, ?_, ?_, ?_⟩
  · rw [n₉ _ (by unfold Layout.rT; omega) (by unfold Layout.rSZ; omega) (fun a _ => by unfold Layout.rA; omega)]
    show _ = if i = dv then d else 0
    by_cases hid : i = dv
    · subst hid; simp only [↓reduceIte]; exact hdv5
    · simp only [hid, ↓reduceIte]; rw [n₅ _ hid, n₃ _ hid (by unfold Layout.rZ; omega)]
      exact z₁ i fun x _ => by unfold Layout.rS; omega
  · rw [n₉ _ (by unfold Layout.rZ Layout.rT; omega) (by unfold Layout.rZ Layout.rSZ; omega)
      (fun a _ => by unfold Layout.rZ Layout.rA; omega), n₅ _ (by unfold Layout.rZ; omega)]
    show update (update s₁.nreg L.rZ L.NS) dv 0 L.rZ = _
    rw [update_of_ne (by unfold Layout.rZ; omega), update_self]
  · rw [h₉ a ha, hT8, hSZ8]; unfold Layout.base; ring
  · rw [hm9]
    show _ = if x = 0 then (d : ℝ) else 0
    by_cases hx0 : x = 0
    · subst hx0; simp
    · simp only [hx0, ↓reduceIte]; rw [update_of_ne hx0]
  · rw [hm9, update_of_ne (by omega)]
  · rw [hm9, update_of_ne (by unfold Layout.base; omega)]; rfl
  · rw [d₉]; show s₁.draws = 0; rw [d₁]; rfl
  · rw [r₉]; show s₁.rounds = 0; rw [r₁]; rfl
  · rw [p₉]; show s₁.pts = _; rw [p₁]; rfl

end AdversarialBco.Bit.Transfer
