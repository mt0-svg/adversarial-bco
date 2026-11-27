/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XDriver
public import AdversarialBco.Bit.Transfer.XBLSplit
public import AdversarialBco.Bit.Transfer.XBLMag
public import AdversarialBco.Bit.ApQ.FrameB
public import AdversarialBco.Bit.BLEngine
public import AdversarialBco.Conj1.RunAd
public import AdversarialBco.Bit.Transfer.XBLSetupBL
public import AdversarialBco.Bit.Transfer.XBLMagLem

@[expose] public section

/-!
# Polynomial bounds uniform in the input

`PolyB S X f`: `f ≤ c X^k` on the inputs `S`, with `c` and `k` uniform; closed under sums, products, powers, bit
lengths and `2^size`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ
  AdversarialBco.Bit.Asm
open AdversarialBco.RealRAM (Strategy polytope HeightLE)

/-! ## Polynomial bounds, uniformly over the inputs -/

/-- `f ≤ c X^k` on `S`, for some `c`, `k` that do not depend on the input. -/
def PolyB {ι : Type*} (S : ι → Prop) (X f : ι → ℕ) : Prop := ∃ c k : ℕ, ∀ i, S i → f i ≤ c * X i ^ k

namespace PolyB

variable {ι : Type*} {S : ι → Prop} {X f g : ι → ℕ}

theorem mono (h : PolyB S X g) (hfg : ∀ i, S i → f i ≤ g i) : PolyB S X f := by
  obtain ⟨c, k, h⟩ := h
  exact ⟨c, k, fun i hi => (hfg i hi).trans (h i hi)⟩

theorem const (c : ℕ) : PolyB S X (fun _ => c) := ⟨c, 0, fun i _ => by simp⟩

theorem self : PolyB S X X := ⟨1, 1, fun i _ => by simp⟩

theorem le_X (h : ∀ i, S i → f i ≤ X i) : PolyB S X f := self.mono h

theorem add (hX : ∀ i, S i → 1 ≤ X i) (hf : PolyB S X f) (hg : PolyB S X g) :
    PolyB S X (fun i => f i + g i) := by
  obtain ⟨c1, k1, h1⟩ := hf
  obtain ⟨c2, k2, h2⟩ := hg
  refine ⟨c1 + c2, k1 + k2, fun i hi => ?_⟩
  have e1 : X i ^ k1 ≤ X i ^ (k1 + k2) := Nat.pow_le_pow_right (hX i hi) (by omega)
  have e2 : X i ^ k2 ≤ X i ^ (k1 + k2) := Nat.pow_le_pow_right (hX i hi) (by omega)
  calc f i + g i ≤ c1 * X i ^ k1 + c2 * X i ^ k2 := Nat.add_le_add (h1 i hi) (h2 i hi)
    _ ≤ c1 * X i ^ (k1 + k2) + c2 * X i ^ (k1 + k2) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ e1) (Nat.mul_le_mul_left _ e2)
    _ = (c1 + c2) * X i ^ (k1 + k2) := (add_mul _ _ _).symm

theorem mul (hf : PolyB S X f) (hg : PolyB S X g) : PolyB S X (fun i => f i * g i) := by
  obtain ⟨c1, k1, h1⟩ := hf
  obtain ⟨c2, k2, h2⟩ := hg
  refine ⟨c1 * c2, k1 + k2, fun i hi => ?_⟩
  calc f i * g i ≤ (c1 * X i ^ k1) * (c2 * X i ^ k2) := Nat.mul_le_mul (h1 i hi) (h2 i hi)
    _ = c1 * c2 * X i ^ (k1 + k2) := by rw [pow_add]; ring

theorem pow (hf : PolyB S X f) (j : ℕ) : PolyB S X (fun i => f i ^ j) := by
  obtain ⟨c, k, h⟩ := hf
  refine ⟨c ^ j, k * j, fun i hi => ?_⟩
  calc f i ^ j ≤ (c * X i ^ k) ^ j := Nat.pow_le_pow_left (h i hi) j
    _ = c ^ j * X i ^ (k * j) := by rw [mul_pow, ← pow_mul]

theorem size (hf : PolyB S X f) : PolyB S X (fun i => (f i).size) :=
  hf.mono fun _ _ => Nat.size_le.2 Nat.lt_two_pow_self

theorem two_pow_size_le (x : ℕ) : 2 ^ x.size ≤ 2 * x + 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  have hs : 0 < x.size := Nat.size_pos.2 hx
  have h2 : 2 ^ (x.size - 1) ≤ x := Nat.lt_size.1 (by omega)
  have e : 2 ^ x.size = 2 * 2 ^ (x.size - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

theorem two_pow_size (hX : ∀ i, S i → 1 ≤ X i) (hf : PolyB S X f) : PolyB S X (fun i => 2 ^ (f i).size) :=
  (((const 2).mul hf).add hX (const 1)).mono fun i _ => two_pow_size_le (f i)

end PolyB

/-! ## The inputs -/

variable {d : ℕ}

/-! ## The polynomial bounds -/

theorem len_natCast_le (x : ℕ) : BitRAM.len (x : ℤ) ≤ x := by
  unfold BitRAM.len
  rw [Int.natAbs_natCast]
  exact Nat.size_le.2 Nat.lt_two_pow_self

end AdversarialBco.Bit.Transfer.BLM
