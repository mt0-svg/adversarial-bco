/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XEllTest

@[expose] public section

/-!
# The loop of ELL-R on the machine

The pieces of the loop of ELL-R on the machine: the matrix `Â` in the array `a0` (entry `(i, k)` in the cell
`d i + k`), the centre `â` in the array `a0 + 1`, the kept point in the slots `P + 1`, `P + 2` and the array `kb`
(`LoopLay`, `LoopSt`, `KeptOK`); the environment of the update (`UpdEnv`); the stop on the kept point (`xellStop`,
`XV.stop`); the outcome in the slot `P + 8`: `2` for a returned point (in the array `a0 + 1`), `1` for a stop on the
kept point, `0` when the `N` turns ran out (`LoopOut`). Registers: the turn `n0 + 6`, the bound `n0 + 7`.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## The program -/

/-- The outcome `v` (a slot holding `1` or `2`) into `P + 8`, and the end of the loop. -/
def xellStop (L : Layout) (P u n0 v : ℕ) : XCmd :=
  .seq (xset L (P + 8) v u) (.prim (.frag (.nconst (n0 + 7) 0)))

/-! ## The data -/

/-- The constants of the update step in the slots `u + 2, ..., u + 12`. -/
def UpdEnv (u p q j : ℕ) (capA capa : ℤ) (σ : Env d) : Prop :=
  σ.sc (u + 2) = 2 ∧ σ.sc (u + 3) = 4 ∧ σ.sc (u + 4) = (((2 : ℤ) ^ (p - 2 * j) : ℤ) : ℝ) ∧
    σ.sc (u + 5) = (2 : ℤ) ^ (2 * q) ∧ σ.sc (u + 6) = (2 : ℤ) ^ p ∧ σ.sc (u + 7) = (2 : ℤ) ^ q ∧
    σ.sc (u + 8) = (d : ℤ) + 1 ∧ σ.sc (u + 9) = kapN d ∧ σ.sc (u + 10) = kapD d ∧ σ.sc (u + 11) = capA ∧
    σ.sc (u + 12) = capa

theorem UpdEnv.frame {u p q j : ℕ} {capA capa : ℤ} {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop} {σ σ' : Env d}
    (h : UpdEnv u p q j capA capa σ) (hF : FrameA S N Ar σ σ') (hS : ∀ y, S y → y < u + 2 ∨ u + 12 < y) :
    UpdEnv u p q j capA capa σ' := by
  have e : ∀ y, u + 2 ≤ y → y ≤ u + 12 → σ'.sc y = σ.sc y := fun y h1 h2 =>
    hF.2.1 y fun hs => by rcases hS y hs with h | h <;> omega
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨by rw [e _ (by omega) (by omega), h2], by rw [e _ (by omega) (by omega), h3],
    by rw [e _ (by omega) (by omega), h4], by rw [e _ (by omega) (by omega), h5],
    by rw [e _ (by omega) (by omega), h6], by rw [e _ (by omega) (by omega), h7],
    by rw [e _ (by omega) (by omega), h8], by rw [e _ (by omega) (by omega), h9],
    by rw [e _ (by omega) (by omega), h10], by rw [e _ (by omega) (by omega), h11],
    by rw [e _ (by omega) (by omega), h12]⟩

/-- The kept point within its bounds: the point below `capa`, the value below `2^{6F+1}`. -/
def KeptOK (capa : ℤ) (F : ℕ) (kept : Option ((Fin d → ℤ) × ℤ)) : Prop :=
  ∀ b W, kept = some (b, W) → (∀ k, |b k| ≤ capa) ∧ |W| ≤ 2 ^ (6 * F + 1)

/-- The cells of the loop above the bases: the layout of the tests, the outcome `P + 8`, the registers `n0 + 6`,
`n0 + 7`. -/
structure LoopLay (L : Layout) (B : EllBlk) (P u a0 kb n0 : ℕ) : Prop where
  test : TestLay L B P u a0 kb n0 (n0 + 4) (n0 + 5)
  PS : P + 9 ≤ u
  nN : n0 + 8 ≤ L.NN

/-- The outcome of the loop on the result `r`: `2` in `P + 8` and the point in the array `a0 + 1`, or `0`, `1` in
`P + 8` and `r` the kept point. -/
def LoopOut (P a0 kb : ℕ) (capa : ℤ) (F : ℕ) (r : Option (Fin d → ℤ)) (σ : Env d) : Prop :=
  (σ.sc (P + 8) = 2 ∧ ∃ x, r = some x ∧ (∀ k : Fin d, σ.arr (a0 + 1) k = x k) ∧ ∀ k, |x k| ≤ capa) ∨
    ((σ.sc (P + 8) = 0 ∨ σ.sc (P + 8) = 1) ∧
      ∃ kept, KeptOK capa F kept ∧ KeptIn P kb kept σ ∧ r = kept.map Prod.fst)

theorem ellV_le {I : EllI d} {s F : ℕ} {a : Fin d → ℤ} (ba : ∀ k, |a k| ≤ 2 ^ F) (hσF : ellSz I ≤ F)
    (hsF : s + 1 ≤ F) (hdF : d ≤ F) :
    |(I.Df : ℤ) * (a ⬝ᵥ (I.P *ᵥ a)) - 2 ^ (s + 1) * (I.f ⬝ᵥ a)| ≤ 2 ^ (6 * F + 1) := by
  have bw : ∀ k, |(I.P *ᵥ a) k| ≤ 2 ^ (3 * F) := fun k =>
    abs_le_pow_mono (abs_mulVec_le' hdF (ellP_le hσF) ba k) (by omega)
  exact abs_sub_le_pow (abs_le_pow_mono (abs_mul_le_pow (ellDf_le hσF) (abs_dot_le' hdF ba bw)) (by omega))
    (abs_le_pow_mono (abs_mul_le_pow (abs_pow_le hsF) (abs_dot_le' hdF (ellF_le hσF) ba)) (by omega))

/-! ## The loop on the machine -/

/-- The state `st` of the loop in the machine, within its bounds. -/
def LoopSt (P a0 kb : ℕ) (capA capa : ℤ) (F : ℕ) (st : ESt d) (σ : Env d) : Prop :=
  (∀ i k : Fin d, σ.arr a0 (d * i + k) = st.A i k) ∧ (∀ k : Fin d, σ.arr (a0 + 1) k = st.a k) ∧
    KeptIn P kb st.kept σ ∧ (∀ i k, |st.A i k| ≤ capA) ∧ (∀ k, |st.a k| ≤ capa) ∧ KeptOK capa F st.kept

theorem LoopSt.frame {P a0 kb : ℕ} {capA capa : ℤ} {F : ℕ} {st : ESt d} {σ σ' : Env d}
    (h : LoopSt P a0 kb capA capa F st σ) (hA : ∀ k, σ'.arr a0 k = σ.arr a0 k)
    (ha : ∀ k, σ'.arr (a0 + 1) k = σ.arr (a0 + 1) k) (h1 : σ'.sc (P + 1) = σ.sc (P + 1))
    (h2 : σ'.sc (P + 2) = σ.sc (P + 2)) (hk : ∀ k, σ'.arr kb k = σ.arr kb k) : LoopSt P a0 kb capA capa F st σ' := by
  obtain ⟨mA, ma, mK, bA, ba, bK⟩ := h
  exact ⟨fun i k => (hA _).trans (mA i k), fun k => (ha _).trans (ma k), mK.frame h1 h2 hk, bA, ba, bK⟩

/-- The rule of `xellStop`: the value `w` of the slot `v` into `P + 8`, the bound `n0 + 7` to `0`. -/
theorem XV.stop {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {P u n0 v : ℕ} {w : ℝ}
    (hP : P + 8 < L.NS) (hv : v < L.NS) (hu : u < L.NS) (hn : n0 + 7 < L.NN) (hz : σ.sc u = 0)
    (hw : σ.sc v = w) (bw : |w| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xellStop L P u n0 v) σ 2 (fun σ' => σ'.sc (P + 8) = w ∧ σ'.nat (n0 + 7) = 0 ∧
      σ'.draws = σ.draws ∧ FrameA (fun y => y = P + 8) (fun j => j = n0 + 7) (fun _ _ => False) σ σ') := by
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by simp only [abs_zero]; positivity
  have e : RealRAM.Op2.eval .add (σ.sc v) (σ.sc u) = w := by simp [RealRAM.Op2.eval, hw, hz]
  refine XV.seq (K₂ := 1) (XV.sop2 hL (x := P + 8) (a := v) (b := u) hP hv hu .add (by intro h; cases h)
    (by rw [hw]; exact bw) (by rw [hz]; exact h0) (by rw [e]; exact bw)) fun σ1 e1 => ?_
  subst e1
  refine XV.mono (XV.nconst hL hn 0 (by positivity)) le_rfl fun σ2 e2 => ?_
  subst e2
  refine ⟨by simp [e], by simp, by simp, ?_⟩
  exact ((FrameA.refl (fun y => y = P + 8) (fun j => j = n0 + 7) (fun _ _ => False) σ).setSc rfl _).setNat rfl 0

end AdversarialBco.Bit.Transfer
