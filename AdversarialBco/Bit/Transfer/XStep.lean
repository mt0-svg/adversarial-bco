/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XIsqrt

@[expose] public section

/-!
# Integer-valued step rules, frames by predicates

* `FrameP S N σ σ'`: `σ'` agrees with `σ` outside the scalars in `S` and the naturals in `N` (the coin counter
  aside), with `refl`, `trans`, `mono`, `setSc`, `setNat`, `draws` and `of_frame`.
* The scalar primitives on integer values: `XV.constI`, `XV.addI`, `XV.subI`, `XV.mulI`, `XV.divI` (the Euclidean
  quotient), `XV.ncastI` (a natural into a scalar), and the naturals `XV.nsub`; each states its result as the cast
  of an integer, its bounds on integers.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach

variable {d : ℕ}

/-- `σ'` agrees with `σ` outside the scalars in `S` and the naturals in `N`; the coin counter is not constrained. -/
def FrameP (S N : ℕ → Prop) (σ σ' : Env d) : Prop :=
  (∀ j, ¬ N j → σ'.nat j = σ.nat j) ∧ (∀ y, ¬ S y → σ'.sc y = σ.sc y) ∧ σ'.arr = σ.arr ∧
    σ'.rounds = σ.rounds ∧ σ'.pts = σ.pts

namespace FrameP

variable {S N S' N' : ℕ → Prop} {σ σ' σ'' : Env d}

theorem refl (S N : ℕ → Prop) (σ : Env d) : FrameP S N σ σ := ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem trans (h : FrameP S N σ σ') (h' : FrameP S N σ' σ'') : FrameP S N σ σ'' :=
  ⟨fun j hj => (h'.1 j hj).trans (h.1 j hj), fun y hy => (h'.2.1 y hy).trans (h.2.1 y hy),
    h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1, h'.2.2.2.2.trans h.2.2.2.2⟩

theorem mono (h : FrameP S N σ σ') (hS : ∀ y, S y → S' y) (hN : ∀ j, N j → N' j) : FrameP S' N' σ σ' :=
  ⟨fun j hj => h.1 j (fun e => hj (hN j e)), fun y hy => h.2.1 y (fun e => hy (hS y e)), h.2.2⟩

theorem setSc (h : FrameP S N σ σ') {x : ℕ} (hx : S x) (v : ℝ) : FrameP S N σ (σ'.setSc x v) := by
  refine ⟨h.1, fun y hy => ?_, h.2.2⟩
  have hne : y ≠ x := fun e => hy (e ▸ hx)
  simp [hne, h.2.1 y hy]

theorem setNat (h : FrameP S N σ σ') {i : ℕ} (hi : N i) (v : ℕ) : FrameP S N σ (σ'.setNat i v) := by
  refine ⟨fun j hj => ?_, h.2.1, h.2.2⟩
  have hne : j ≠ i := fun e => hj (e ▸ hi)
  simp [hne, h.1 j hj]

theorem draws (h : FrameP S N σ σ') (k : ℕ) : FrameP S N σ { σ' with draws := k } := h

theorem of_frame {l n : List ℕ} (h : Frame l n σ σ') (hS : ∀ y ∈ l, S y) (hN : ∀ j ∈ n, N j) :
    FrameP S N σ σ' :=
  ⟨fun j hj => h.1 j (fun e => hj (hN j e)), fun y hy => h.2.1 y (fun e => hy (hS y e)), h.2.2.1, h.2.2.2.2⟩

end FrameP

namespace XV

variable {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d}

theorem abs_int_lt {v : ℤ} (h : |v| < 2 ^ ℓ) : |(v : ℝ)| < 2 ^ ℓ := by
  rw [← Int.cast_abs]; exact_mod_cast h

theorem constI (hL : LayOK L d ℓa) {x : ℕ} (hx : x < L.NS) (c : ℤ) (hc : |c| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (toX (VL.sconst L x c)) σ 1 (· = σ.setSc x (c : ℝ)) :=
  mono (sconst hL hx (c : ℚ) (Rat.den_intCast c) (by rw [Rat.cast_intCast]; exact abs_int_lt hc)) le_rfl
    (fun σ' e => by rw [e, Rat.cast_intCast])

theorem addI (hL : LayOK L d ℓa) {x a b : ℕ} (hx : x < L.NS) (ha : a < L.NS) (hb : b < L.NS) {u v : ℤ}
    (hu : σ.sc a = u) (hv : σ.sc b = v) (bu : |u| < 2 ^ ℓ) (bv : |v| < 2 ^ ℓ) (br : |u + v| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (toX (VL.sop2 L .add x a b)) σ 1 (· = σ.setSc x ((u + v : ℤ) : ℝ)) := by
  have e : RealRAM.Op2.eval .add (σ.sc a) (σ.sc b) = ((u + v : ℤ) : ℝ) := by
    rw [hu, hv]; simp [RealRAM.Op2.eval]
  exact mono (sop2 hL hx ha hb .add (by intro h; cases h) (by rw [hu]; exact abs_int_lt bu)
    (by rw [hv]; exact abs_int_lt bv) (by rw [e]; exact abs_int_lt br)) le_rfl (fun σ' h => by rw [h, e])

theorem subI (hL : LayOK L d ℓa) {x a b : ℕ} (hx : x < L.NS) (ha : a < L.NS) (hb : b < L.NS) {u v : ℤ}
    (hu : σ.sc a = u) (hv : σ.sc b = v) (bu : |u| < 2 ^ ℓ) (bv : |v| < 2 ^ ℓ) (br : |u - v| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (toX (VL.sop2 L .sub x a b)) σ 1 (· = σ.setSc x ((u - v : ℤ) : ℝ)) := by
  have e : RealRAM.Op2.eval .sub (σ.sc a) (σ.sc b) = ((u - v : ℤ) : ℝ) := by
    rw [hu, hv]; simp [RealRAM.Op2.eval]
  exact mono (sop2 hL hx ha hb .sub (by intro h; cases h) (by rw [hu]; exact abs_int_lt bu)
    (by rw [hv]; exact abs_int_lt bv) (by rw [e]; exact abs_int_lt br)) le_rfl (fun σ' h => by rw [h, e])

theorem mulI (hL : LayOK L d ℓa) {x a b : ℕ} (hx : x < L.NS) (ha : a < L.NS) (hb : b < L.NS) {u v : ℤ}
    (hu : σ.sc a = u) (hv : σ.sc b = v) (bu : |u| < 2 ^ ℓ) (bv : |v| < 2 ^ ℓ) (br : |u * v| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (toX (VL.sop2 L .mul x a b)) σ 1 (· = σ.setSc x ((u * v : ℤ) : ℝ)) := by
  have e : RealRAM.Op2.eval .mul (σ.sc a) (σ.sc b) = ((u * v : ℤ) : ℝ) := by
    rw [hu, hv]; simp [RealRAM.Op2.eval]
  exact mono (sop2 hL hx ha hb .mul (by intro h; cases h) (by rw [hu]; exact abs_int_lt bu)
    (by rw [hv]; exact abs_int_lt bv) (by rw [e]; exact abs_int_lt br)) le_rfl (fun σ' h => by rw [h, e])

theorem divI (hL : LayOK L d ℓa) {x a b : ℕ} (hx : x < L.NS) (ha : a < L.NS) (hb : b < L.NS) {u v : ℤ}
    (hu : σ.sc a = u) (hv : σ.sc b = v) (bu : |u| < 2 ^ ℓ) (bv : |v| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xsidiv L x a b) σ 1 (· = σ.setSc x ((u / v : ℤ) : ℝ)) :=
  mono (sidiv hL hx ha hb (by rw [hu]; exact abs_int_lt bu) (by rw [hv]; exact abs_int_lt bv)) le_rfl
    (fun σ' h => by rw [h, hu, hv, Int.floor_intCast, Int.floor_intCast])

theorem ncastI (hL : LayOK L d ℓa) {x i : ℕ} (hx : x < L.NS) (hi : i < L.NN) (hv : σ.nat i < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (toX (VL.ncast L x i)) σ 1 (· = σ.setSc x ((σ.nat i : ℤ) : ℝ)) :=
  mono ((VB.runsB_prim (w := X.rw) (ℓa := ℓa) (ℓ := ℓ) (VL.runs_ncast hx hi) fun _ hs =>
    ⟨VB.regOK_rS hL hs hx, VB.regOK_nat hL hi (by rw [hs.nat i hi]; exact hv)⟩).toX X) le_rfl
    (fun σ' h => by rw [h, Int.cast_natCast])

theorem nsub (hL : LayOK L d ℓa) {i a b : ℕ} (hi : i < L.NN) (ha : a < L.NN) (hb : b < L.NN)
    (hva : σ.nat a < 2 ^ ℓa) (hvb : σ.nat b < 2 ^ ℓa) (hba : σ.nat b ≤ σ.nat a) :
    XRunsB L X ℓa ℓ (.prim (.frag (.nsub i a b))) σ 1 (· = σ.setNat i (σ.nat a - σ.nat b)) :=
  (VB.runsB_nsub (w := X.rw) (ℓ := ℓ) hL hi ha hb hva hvb hba).toX X

end XV

end AdversarialBco.Bit.Transfer
