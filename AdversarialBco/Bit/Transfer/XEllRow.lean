/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBmRun

@[expose] public section

/-!
# One row of the matrix step of ELL-R

Step 7 of Procedure ELL-R (the paper's section on the projections) writes
`Â'_{ik} = rnd(κ_N((d + 1)ŝ Â_{ik} - 2 v̂_i v̂_k)/(κ_D (d + 1)ŝ))`, `rnd(u/v) = ⌊(2u + v)/(2v)⌋`.

* `FrameA`: what a routine that writes array cells leaves unchanged.
* `ellEntry`: the entry as the program computes it.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach

variable {d : ℕ}

/-- The environment changed only on the registers `N`, the scalars `S` and the array cells `Ar`. -/
def FrameA (S N : ℕ → Prop) (Ar : ℕ → ℕ → Prop) (σ σ' : Env d) : Prop :=
  (∀ j, ¬ N j → σ'.nat j = σ.nat j) ∧ (∀ y, ¬ S y → σ'.sc y = σ.sc y) ∧
    (∀ b k, ¬ Ar b k → σ'.arr b k = σ.arr b k) ∧ σ'.rounds = σ.rounds ∧ σ'.pts = σ.pts

namespace FrameA

variable {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop} {σ σ' σ'' : Env d}

theorem refl (S N : ℕ → Prop) (Ar : ℕ → ℕ → Prop) (σ : Env d) : FrameA S N Ar σ σ :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl⟩

theorem trans (h : FrameA S N Ar σ σ') (h' : FrameA S N Ar σ' σ'') : FrameA S N Ar σ σ'' :=
  ⟨fun j hj => (h'.1 j hj).trans (h.1 j hj), fun y hy => (h'.2.1 y hy).trans (h.2.1 y hy),
    fun b k hb => (h'.2.2.1 b k hb).trans (h.2.2.1 b k hb), h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.trans h.2.2.2.2⟩

theorem setSc (h : FrameA S N Ar σ σ') {x : ℕ} (hx : S x) (v : ℝ) : FrameA S N Ar σ (σ'.setSc x v) := by
  refine ⟨h.1, fun y hy => ?_, h.2.2⟩
  have hne : y ≠ x := fun e => hy (e ▸ hx)
  simp [hne, h.2.1 y hy]

theorem setNat (h : FrameA S N Ar σ σ') {i : ℕ} (hi : N i) (v : ℕ) : FrameA S N Ar σ (σ'.setNat i v) := by
  refine ⟨fun j hj => ?_, h.2.1, h.2.2⟩
  have hne : j ≠ i := fun e => hj (e ▸ hi)
  simp [hne, h.1 j hj]

theorem setArr (h : FrameA S N Ar σ σ') {b k : ℕ} (hk : Ar b k) (v : ℝ) :
    FrameA S N Ar σ (σ'.setArr b k v) := by
  refine ⟨h.1, h.2.1, fun b' k' hb => ?_, h.2.2.2⟩
  have : ¬ (b' = b ∧ k' = k) := fun ⟨e1, e2⟩ => hb (e1 ▸ e2 ▸ hk)
  simp [this, h.2.2.1 b' k' hb]

end FrameA

/-- The entry of the matrix step as the program computes it: `t = (a c1 - (vi vk + vi vk)) κN`, then
`(t + t + D)/(2D)` by the Euclidean quotient. -/
def ellEntry (c1 kN D D2 a vi vk : ℤ) : ℤ :=
  ((a * c1 - (vi * vk + vi * vk)) * kN + (a * c1 - (vi * vk + vi * vk)) * kN + D) / D2

theorem XV.aget {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {x a i : ℕ}
    (hx : x < L.NS) (ha : a < L.NA) (hi : i < L.NN) (hk : σ.nat i < asz d) (hv : |σ.arr a (σ.nat i)| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (toX (VL.aget L x a i)) σ 2 (· = σ.setSc x (σ.arr a (σ.nat i))) :=
  (VB.runsB_aget (w := X.rw) hL hx ha hi hk hv).toX X

theorem XV.aset {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {a i x : ℕ}
    (ha : a < L.NA) (hi : i < L.NN) (hx : x < L.NS) (hk : σ.nat i < asz d) (hv : |σ.sc x| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (toX (VL.aset L a i x)) σ 2 (· = σ.setArr a (σ.nat i) (σ.sc x)) :=
  (VB.runsB_aset (w := X.rw) hL ha hi hx hk hv).toX X

theorem absI_mul_le {x y : ℤ} {a b : ℕ} (hx : |x| ≤ 2 ^ a) (hy : |y| ≤ 2 ^ b) : |x * y| ≤ 2 ^ (a + b) := by
  rw [abs_mul, pow_add]; exact mul_le_mul hx hy (abs_nonneg _) (pow_nonneg (by norm_num) _)

theorem absI_add_le {x y : ℤ} {a : ℕ} (hx : |x| ≤ 2 ^ a) (hy : |y| ≤ 2 ^ a) : |x + y| ≤ 2 ^ (a + 1) := by
  rw [pow_succ]; exact (abs_add_le x y).trans (by linarith)

theorem absI_sub_le {x y : ℤ} {a : ℕ} (hx : |x| ≤ 2 ^ a) (hy : |y| ≤ 2 ^ a) : |x - y| ≤ 2 ^ (a + 1) := by
  rw [pow_succ]; exact (abs_sub x y).trans (by linarith)

theorem absI_mono {x : ℤ} {a b : ℕ} (hx : |x| ≤ 2 ^ a) (hab : a ≤ b) : |x| ≤ 2 ^ b :=
  hx.trans (pow_le_pow_right₀ (by norm_num) hab)

theorem absI_ediv_le (x y : ℤ) : |x / y| ≤ |x| := by
  rw [← Int.natCast_natAbs, ← Int.natCast_natAbs]
  exact_mod_cast Int.natAbs_ediv_le_natAbs x y

end AdversarialBco.Bit.Transfer
