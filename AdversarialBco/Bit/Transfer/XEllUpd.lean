/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XVec
public import AdversarialBco.Bit.RoutQ

@[expose] public section

/-!
# The update step of ELL-R and ELL-F on the machine

`xupd` computes `ellUpd p q j capA capa A a c` (Bit/RoutQ.lean): from `Â` (array `a0`, row-major), `â` (array
`a0 + 1`) and the cut `c` (array `a0 + 2`), `v = Â c` (array `a0 + 3`), `ŝ = c·v`, the test (K1), `X = ŝ 2^{2q}/2^p`,
`t = ⌊√X⌋`, `â'` (array `a0 + 5`), `Â'` (array `a0 + 4`), the caps (K2), and the copy of `Â'`, `â'` back into `Â`, `â`.
The slot `u + 13` ends at `1` when (K1) or (K2) acts (`none`), at `0` otherwise.

Slots from the base `u`, read only: `u` holds `0`, `u + 1, u + 2, u + 3` hold `1, 2, 4`, `u + 4` holds `2^{p-2j}`,
`u + 5` holds `2^{2q}`, `u + 6` holds `2^p`, `u + 7` holds `2^q`, `u + 8` holds `d + 1`, `u + 9` holds `κ_N`, `u + 10`
holds `κ_D`, `u + 11` holds `capA`, `u + 12` holds `capa`. Written: `u + 13` (the flag), `u + 14` (`ŝ`), `u + 15`
(`2^{p-2j} |c|²`), `u + 16` (`X`), `u + 17` (`t`), `u + 18` (`(d + 1) t`), `u + 19` (`2 (d + 1) t`),
`u + 20, ..., u + 23` (`(d + 1)ŝ`, `κ_N`, `κ_D (d + 1)ŝ`, twice that, the scalars of the entry `ieEll`), scratch from
`u + 24`. Registers `n0, ..., n0 + 3`; `nd` holds `d`, `none` holds `1`.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## Commands that read no coin -/

theorem IE.noCoins_code (L : Layout) (z : ℕ) : ∀ (e : IE) (x t : ℕ), (e.code L z x t).noCoins = true
  | .sc _, _, _ => noCoins_toX _
  | .arr _ _, _, _ => noCoins_toX _
  | .op _ a b, _, _ => by
    simp [IE.code, XCmd.noCoins, IE.noCoins_code L z a, IE.noCoins_code L z b, noCoins_toX]
  | .ediv a b, _, _ => by
    simp [IE.code, XCmd.noCoins, XPrim.noCoins, Leaf.noCoins, xsidiv, IE.noCoins_code L z a,
      IE.noCoins_code L z b]

theorem noCoins_xellRowH (L : Layout) (z o aA aV aB ni nr nk nd none : ℕ) :
    (xellRowH L z o aA aV aB ni nr nk nd none).noCoins = true := by
  simp [xellRowH, xforN, XCmd.noCoins, XPrim.noCoins, IE.noCoins_code, noCoins_toX]


/-! ## Bounds -/

theorem abs_dot_le {x y : Fin d → ℤ} {a b : ℕ} (hx : ∀ k, |x k| ≤ 2 ^ a) (hy : ∀ k, |y k| ≤ 2 ^ b) :
    |x ⬝ᵥ y| ≤ d * 2 ^ (a + b) := by
  unfold dotProduct
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |x i * y i| ≤ ∑ _i : Fin d, (2 : ℤ) ^ (a + b) := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, pow_add]; exact mul_le_mul (hx i) (hy i) (abs_nonneg _) (by positivity)
    _ = d * 2 ^ (a + b) := by simp

theorem d_mul_pow_le {E k : ℕ} (hd : d ≤ E) : (d : ℤ) * 2 ^ k ≤ 2 ^ (E + k) := by
  rw [pow_add]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have h1 : d < 2 ^ d := Nat.lt_two_pow_self
  have h2 : 2 ^ d ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) hd
  exact_mod_cast (h1.trans_le h2).le

theorem abs_dot_le' {x y : Fin d → ℤ} {a b E : ℕ} (hd : d ≤ E) (hx : ∀ k, |x k| ≤ 2 ^ a)
    (hy : ∀ k, |y k| ≤ 2 ^ b) : |x ⬝ᵥ y| ≤ 2 ^ (E + (a + b)) :=
  (abs_dot_le hx hy).trans (d_mul_pow_le hd)

theorem abs_mulVec_le' {M : Matrix (Fin d) (Fin d) ℤ} {x : Fin d → ℤ} {a b E : ℕ} (hd : d ≤ E)
    (hM : ∀ i k, |M i k| ≤ 2 ^ a) (hx : ∀ k, |x k| ≤ 2 ^ b) (i : Fin d) : |(M *ᵥ x) i| ≤ 2 ^ (E + (a + b)) :=
  abs_dot_le' hd (hM i) hx

theorem abs_le_pow_mono {x : ℤ} {a b : ℕ} (h : |x| ≤ 2 ^ a) (hab : a ≤ b) : |x| ≤ 2 ^ b :=
  h.trans (pow_le_pow_right₀ (by norm_num) hab)

/-! ## The program -/

/-- `x * y` on two slots. -/
def ieMul (a b : ℕ) : IE := .op .mul (.sc a) (.sc b)

/-- The prologue: the flag to `0`, `κ_N` into `u + 21`, `v = Â c`, `ŝ = c·v`, `2^{p-2j} |c|²`. -/
def xupdV (L : Layout) (u a0 n0 nd none : ℕ) : XCmd :=
  .seq (toX (VL.sop2 L .add (u + 13) u u))
  (.seq (toX (VL.sop2 L .add (u + 21) (u + 9) u))
  (.seq (xmatvec L u (u + 24) (u + 25) a0 (a0 + 2) (a0 + 3) n0 (n0 + 1) (n0 + 2) nd none)
  (.seq (xdot L u (u + 14) (u + 25) (a0 + 2) (a0 + 3) (n0 + 1) (n0 + 2) nd none)
  (.seq (xdot L u (u + 15) (u + 25) (a0 + 2) (a0 + 2) (n0 + 1) (n0 + 2) nd none)
  ((ieMul (u + 4) (u + 15)).code L u (u + 15) (u + 24))))))

theorem d_mul_pow_lt {E k ℓ : ℕ} (hd : d ≤ E) (h : E + k < ℓ) : d * 2 ^ k < 2 ^ ℓ := by
  have h1 : d < 2 ^ d := Nat.lt_two_pow_self
  have h2 : 2 ^ d ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) hd
  calc d * 2 ^ k < 2 ^ E * 2 ^ k := Nat.mul_lt_mul_of_pos_right (h1.trans_le h2) (by positivity)
    _ = 2 ^ (E + k) := by rw [pow_add]
    _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) h.le

theorem nodup5 {a b c e f : ℕ} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ e) (h4 : a ≠ f) (h5 : b ≠ c) (h6 : b ≠ e)
    (h7 : b ≠ f) (h8 : c ≠ e) (h9 : c ≠ f) (h10 : e ≠ f) : [a, b, c, e, f].Nodup := by
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

theorem nodup4 {a b c e : ℕ} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ e) (h5 : b ≠ c) (h6 : b ≠ e) (h8 : c ≠ e) :
    [a, b, c, e].Nodup := by
  simp [h1, h2, h3, h5, h6, h8]

set_option maxHeartbeats 4000000 in
/-- The rule of the prologue `xupdV`: inputs below `2^E`, `d ≤ E`, `64 E + 16 < ℓ`. -/
theorem XV.updV {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {u a0 n0 nd none E : ℕ}
    {A : Matrix (Fin d) (Fin d) ℤ} {c : Fin d → ℤ} {K1 kN : ℤ}
    (hS : u + 60 ≤ L.NS) (hA0 : a0 + 6 ≤ L.NA) (hN0 : n0 + 4 ≤ L.NN) (hnd : nd < L.NN) (hno : none < L.NN)
    (hnd0 : nd < n0 ∨ n0 + 4 ≤ nd) (hno0 : none < n0 ∨ n0 + 4 ≤ none) (hndo : nd ≠ none)
    (hz : σ.sc u = 0) (hσd : σ.nat nd = d) (hσ1 : σ.nat none = 1) (hK1 : σ.sc (u + 4) = K1)
    (hkN : σ.sc (u + 9) = kN) (hA : ∀ i k : Fin d, σ.arr a0 (d * i + k) = A i k)
    (hc : ∀ k : Fin d, σ.arr (a0 + 2) k = c k) (bA : ∀ i k, |A i k| ≤ 2 ^ E) (bc : ∀ k, |c k| ≤ 2 ^ E)
    (bK1 : |K1| ≤ 2 ^ E) (bkN : |kN| ≤ 2 ^ E) (hdE : d ≤ E) (hℓ : 64 * E + 16 < ℓ) :
    XRunsB L X ℓa ℓ (xupdV L u a0 n0 nd none) σ (10 * d * d + 29 * d + 19) (fun σ' =>
      σ'.sc (u + 13) = 0 ∧ σ'.sc (u + 21) = kN ∧ (∀ k : Fin d, σ'.arr (a0 + 3) k = (A *ᵥ c) k) ∧
      σ'.sc (u + 14) = c ⬝ᵥ (A *ᵥ c) ∧ σ'.sc (u + 15) = K1 * (c ⬝ᵥ c) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => u + 13 ≤ y) (fun j => n0 ≤ j ∧ j < n0 + 4) (fun b k => b = a0 + 3 ∧ k < d) σ σ') := by
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by rw [abs_zero]; positivity
  have bkN' : |(kN : ℝ)| < 2 ^ ℓ := XV.abs_int_lt (lt_of_le_of_lt bkN (pow_lt_pow_right₀ (by norm_num) (by omega)))
  -- the flag, the copy of `κ_N`
  refine XV.mono (K := 1 + (1 + ((d * (d * 10 + 9) + 4) + ((d * 10 + 5) + ((d * 10 + 5) + 3)))))
    (XV.seq (XV.sop2 hL (x := u + 13) (a := u) (b := u) (by omega) (by omega) (by omega) .add (by intro h; cases h)
      (by rw [hz]; exact h0) (by rw [hz]; exact h0) (by simp only [RealRAM.Op2.eval, hz, add_zero]; exact h0))
      fun σ1 e1 => ?_) (by ring_nf; omega) fun _ h => h
  subst e1
  refine XV.seq (XV.sop2 hL (x := u + 21) (a := u + 9) (b := u) (by omega) (by omega) (by omega) .add
    (by intro h; cases h) (by simp [hkN]; exact bkN') (by simp [hz]) (by simp [RealRAM.Op2.eval, hkN, hz]; exact bkN'))
    fun σ2 e2 => ?_
  subst e2
  set σ2 := (σ.setSc (u + 13) (RealRAM.Op2.eval .add (σ.sc u) (σ.sc u))).setSc (u + 21)
    (RealRAM.Op2.eval .add ((σ.setSc (u + 13) (RealRAM.Op2.eval .add (σ.sc u) (σ.sc u))).sc (u + 9))
      ((σ.setSc (u + 13) (RealRAM.Op2.eval .add (σ.sc u) (σ.sc u))).sc u)) with hσ2
  have F2 : FrameA (fun y => u + 13 ≤ y) (fun j => n0 ≤ j ∧ j < n0 + 4) (fun b k => b = a0 + 3 ∧ k < d) σ σ2 :=
    ((FrameA.refl _ _ _ σ).setSc (by omega) _).setSc (by omega) _
  have s2_13 : σ2.sc (u + 13) = 0 := by simp [hσ2, RealRAM.Op2.eval, hz]
  have s2_21 : σ2.sc (u + 21) = kN := by simp [hσ2, RealRAM.Op2.eval, hz, hkN]
  have z2 : σ2.sc u = 0 := by rw [F2.2.1 u (by omega), hz]
  -- `v = Â c`
  have hdl : d * 2 ^ (2 * E) < 2 ^ ℓ := d_mul_pow_lt hdE (by omega)
  refine XV.seq (XV.matvec (E := E) (M := A) (x := c) hL (by omega) (by omega) (by omega) (by omega) z2
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hnd hno
    (nodup5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hndo)
    (by rw [F2.1 nd (by omega), hσd]) (by rw [F2.1 none (by omega), hσ1])
    (fun i k => by rw [F2.2.2.1 a0 _ (fun h => by omega), hA]) (fun k => by rw [F2.2.2.1 (a0 + 2) _
      (fun h => by omega), hc]) bA bc (by omega) hdl) fun σ3 ⟨v3, d3, F3⟩ => ?_
  have F3' := F2.trans (F3.mono (fun y h => by omega) (fun j h => by omega) (fun b k h => h))
  have z3 : σ3.sc u = 0 := by rw [F3'.2.1 u (by omega), hz]
  have bv : ∀ k, |(A *ᵥ c) k| ≤ 2 ^ (3 * E) := fun k =>
    abs_le_pow_mono (abs_mulVec_le' hdE bA bc k) (by omega)
  have bc3 : ∀ k, |c k| ≤ 2 ^ (3 * E) := fun k => abs_le_pow_mono (bc k) (by omega)
  have c3 : ∀ k : Fin d, σ3.arr (a0 + 2) k = c k := fun k => by
    rw [F3'.2.2.1 (a0 + 2) k (fun h => by omega), hc]
  -- `ŝ = c·v`
  refine XV.seq (XV.dot (E := 3 * E) (x := c) (y := A *ᵥ c) hL (by omega) (by omega) (by omega) (by omega) z3
    (by omega) (by omega) (by omega) (by omega) hnd hno
    (nodup4 (by omega) (by omega) (by omega) (by omega) (by omega) hndo)
    (by rw [F3'.1 nd (by omega), hσd]) (by rw [F3'.1 none (by omega), hσ1]) c3 v3 bc3 bv (by omega)
    (d_mul_pow_lt hdE (by omega))) fun σ4 ⟨s4, d4, F4⟩ => ?_
  have F4' := F3'.trans (F4.mono (fun y h => by omega) (fun j h => by omega) (fun b k h => h.elim))
  have z4 : σ4.sc u = 0 := by rw [F4'.2.1 u (by omega), hz]
  -- `|c|²`
  refine XV.seq (XV.dot (E := E) (x := c) (y := c) hL (by omega) (by omega) (by omega) (by omega) z4
    (by omega) (by omega) (by omega) (by omega) hnd hno
    (nodup4 (by omega) (by omega) (by omega) (by omega) (by omega) hndo)
    (by rw [F4'.1 nd (by omega), hσd]) (by rw [F4'.1 none (by omega), hσ1])
    (fun k => by rw [F4'.2.2.1 (a0 + 2) k (fun h => by omega), hc])
    (fun k => by rw [F4'.2.2.1 (a0 + 2) k (fun h => by omega), hc]) bc bc (by omega) hdl) fun σ5 ⟨s5, d5, F5⟩ => ?_
  have F5' := F4'.trans (F5.mono (fun y h => by omega) (fun j h => by omega) (fun b k h => h.elim))
  have z5 : σ5.sc u = 0 := by rw [F5'.2.1 u (by omega), hz]
  -- `2^{p-2j} |c|²`
  have bcc : |c ⬝ᵥ c| ≤ 2 ^ (3 * E) := abs_le_pow_mono (abs_dot_le' hdE bc bc) (by omega)
  have L6 : (ieMul (u + 4) (u + 15)).Leaves (3 * E) σ5 := by
    simp only [ieMul, IE.Leaves]
    refine ⟨⟨K1, by rw [F5'.2.1 (u + 4) (by omega), hK1], abs_le_pow_mono bK1 (by omega)⟩, ⟨c ⬝ᵥ c, s5, bcc⟩⟩
  refine XV.mono (XV.ieRun (E := 3 * E) (e := ieMul (u + 4) (u + 15)) (v := K1 * (c ⬝ᵥ c)) hL (x := u + 15)
    (t := u + 24) (z := u) (by simp only [ieMul, IE.WF]; exact ⟨(by intro h; cases h), by omega, by omega⟩)
    (by omega) (by omega) (by simp only [ieMul, IE.scr]; omega) z5
    L6
    (by simp only [ieMul, IE.top, IE.mag]; omega)
    (by simp only [ieMul, IE.eval, RealRAM.Op2.eval, s5, F5'.2.1 (u + 4) (by omega), hK1]; push_cast; ring))
    le_rfl fun σ6 ⟨s6, _, d6, P6⟩ => ?_
  have F6 := F5'.trans (FrameA.ofP (Ar := fun b k => b = a0 + 3 ∧ k < d) (P6.mono (fun y h => by omega)
    (fun _ h => h.elim)))
  refine ⟨?_, ?_, ?_, ?_, by rw [s6]; push_cast; ring, by rw [d6, d5, d4, d3]; rfl, F6⟩
  · rw [P6.2.1 _ (by omega), F5.2.1 _ (by omega), F4.2.1 _ (by omega), F3.2.1 _ (by omega), s2_13]
  · rw [P6.2.1 _ (by omega), F5.2.1 _ (by omega), F4.2.1 _ (by omega), F3.2.1 _ (by omega), s2_21]
  · intro k; rw [P6.2.2.1, F5.2.2.1 _ _ id, F4.2.2.1 _ _ id, v3]
  · rw [P6.2.1 _ (by omega), F5.2.1 _ (by omega), s4]

theorem FrameA.ofList {S N : List ℕ} {P Q : ℕ → Prop} {Ar : ℕ → ℕ → Prop} {σ σ' : Env d} (h : Frame S N σ σ')
    (hS : ∀ y ∈ S, P y) (hN : ∀ j ∈ N, Q j) : FrameA P Q Ar σ σ' :=
  ⟨fun j hj => h.1 j fun h' => hj (hN j h'), fun y hy => h.2.1 y fun h' => hy (hS y h'),
    fun b k _ => by rw [h.2.2.1], h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- `X = ŝ 2^{2q} / 2^p` (Euclidean quotient). -/
def updX (p q : ℕ) (s : ℤ) : ℤ := s * 2 ^ (2 * q) / 2 ^ p

/-- `t = ⌊√X⌋`. -/
def updT (p q : ℕ) (s : ℤ) : ℤ := (Nat.sqrt (updX p q s).toNat : ℤ)

/-- `X`, `t = ⌊√X⌋`, `(d + 1) t`, `2 (d + 1) t`. -/
def xupdT (L : Layout) (u : ℕ) : XCmd :=
  .seq ((IE.ediv (ieMul (u + 14) (u + 5)) (.sc (u + 6))).code L u (u + 16) (u + 24))
  (.seq (xisqrt L (u + 16) (u + 17) (u + 24) (u + 25) (u + 26) u (u + 1) (u + 2) (u + 3))
  (.seq ((ieMul (u + 8) (u + 17)).code L u (u + 18) (u + 24))
  ((IE.op .add (.sc (u + 18)) (.sc (u + 18))).code L u (u + 19) (u + 24))))

theorem updX_nonneg {p q : ℕ} {s : ℤ} (hs : 0 ≤ s) : 0 ≤ updX p q s :=
  Int.ediv_nonneg (mul_nonneg hs (by positivity)) (by positivity)

theorem updX_le {p q E : ℕ} {s : ℤ} (hs : |s| ≤ 2 ^ (7 * E)) (hq : 2 * q ≤ E) : |updX p q s| ≤ 2 ^ (8 * E) := by
  unfold updX
  refine (absI_ediv_le _ _).trans ?_
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ (2 * q))]
  calc |s| * 2 ^ (2 * q) ≤ 2 ^ (7 * E) * 2 ^ E :=
        mul_le_mul hs (pow_le_pow_right₀ (by norm_num) hq) (by positivity) (by positivity)
    _ = 2 ^ (8 * E) := by rw [← pow_add]; ring_nf

theorem updT_le {p q E : ℕ} {s : ℤ} (hs : |s| ≤ 2 ^ (7 * E)) (hq : 2 * q ≤ E) : |updT p q s| ≤ 2 ^ (4 * E) := by
  have hX := updX_le (p := p) hs hq
  unfold updT
  rw [abs_of_nonneg (by positivity)]
  have h1 : (updX p q s).toNat ≤ 2 ^ (8 * E) := by
    rw [Int.toNat_le]; push_cast; exact (le_abs_self _).trans hX
  have h2 : Nat.sqrt (updX p q s).toNat ≤ 2 ^ (4 * E) := by
    calc Nat.sqrt (updX p q s).toNat ≤ Nat.sqrt ((2 ^ (4 * E)) ^ 2) :=
          Nat.sqrt_le_sqrt (h1.trans_eq (by rw [← pow_mul]; ring_nf))
      _ = 2 ^ (4 * E) := Nat.sqrt_eq' _
  exact_mod_cast h2

set_option maxHeartbeats 2000000 in
/-- The rule of `xupdT`. -/
theorem XV.updT {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {u p q E : ℕ} {s dp1 : ℤ}
    (hS : u + 60 ≤ L.NS) (hz : σ.sc u = 0) (h1 : σ.sc (u + 1) = 1) (h2 : σ.sc (u + 2) = 2)
    (h4 : σ.sc (u + 3) = 4) (hs : σ.sc (u + 14) = s) (hQ : σ.sc (u + 5) = (2 : ℤ) ^ (2 * q))
    (hP : σ.sc (u + 6) = (2 : ℤ) ^ p) (hd1 : σ.sc (u + 8) = dp1) (hs0 : 0 ≤ s) (bs : |s| ≤ 2 ^ (7 * E))
    (hq : 2 * q ≤ E) (hp : p ≤ E) (bd1 : |dp1| ≤ 2 ^ E) (hℓ : 64 * E + 16 < ℓ) :
    XRunsB L X ℓa ℓ (xupdT L u) σ (100 * E + 40) (fun σ' =>
      σ'.sc (u + 17) = updT p q s ∧ σ'.sc (u + 18) = dp1 * updT p q s ∧
      σ'.sc (u + 19) = dp1 * updT p q s + dp1 * updT p q s ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => (u + 16 ≤ y ∧ y ≤ u + 19) ∨ u + 24 ≤ y) (fun _ => False) (fun _ _ => False) σ σ') := by
  have bQ : |(2 : ℤ) ^ (2 * q)| ≤ 2 ^ (7 * E) := by
    rw [abs_of_pos (by positivity)]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hX0 := updX_nonneg (p := p) (q := q) hs0
  have bX := updX_le (p := p) bs hq
  have bP : |(2 : ℤ) ^ p| ≤ 2 ^ (7 * E) := by
    rw [abs_of_pos (by positivity)]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have L1 : (IE.ediv (ieMul (u + 14) (u + 5)) (.sc (u + 6))).Leaves (7 * E) σ := by
    simp only [ieMul, IE.Leaves]
    exact ⟨⟨⟨s, hs, bs⟩, ⟨_, by exact_mod_cast hQ, bQ⟩⟩, ⟨_, by exact_mod_cast hP, bP⟩⟩
  have T1 : (IE.ediv (ieMul (u + 14) (u + 5)) (.sc (u + 6))).top (7 * E) < ℓ := by
    simp only [ieMul, IE.top, IE.mag]; omega
  have V1 : (IE.ediv (ieMul (u + 14) (u + 5)) (.sc (u + 6))).eval σ = ((updX p q s : ℤ) : ℝ) := by
    simp only [ieMul, IE.eval, RealRAM.Op2.eval, hs, hQ, hP, updX]
    norm_cast
    simp only [Int.floor_intCast, Int.floor_natCast]
  -- `X`
  refine XV.mono (K := 5 + ((12 * (8 * E + 1) + 8) + (3 + 3))) (XV.seq (XV.ieRun (E := 7 * E)
    (e := IE.ediv (ieMul (u + 14) (u + 5)) (.sc (u + 6))) (v := updX p q s) hL
    (x := u + 16) (t := u + 24) (z := u) (by simp only [ieMul, IE.WF]; exact ⟨⟨(by intro h; cases h), by omega,
      by omega⟩, by omega⟩) (by omega) (by omega) (by simp only [ieMul, IE.scr]; omega) hz
    L1 T1 V1) fun σ1 ⟨x1, b1, d1, P1⟩ => ?_) (by omega) fun _ h => h
  -- `t = ⌊√X⌋`
  set n := (updX p q s).toNat with hn
  have hnX : ((n : ℤ) : ℝ) = (updX p q s : ℝ) := by rw [hn, Int.toNat_of_nonneg hX0]
  have hn8 : n ≤ 2 ^ (8 * E) := by rw [hn, Int.toNat_le]; push_cast; exact (le_abs_self _).trans bX
  have z1 : σ1.sc u = 0 := by rw [P1.2.1 u (by omega), hz]
  have hsize : n.size ≤ 8 * E + 1 := Nat.size_le.2 (by
    calc n ≤ 2 ^ (8 * E) := hn8
      _ < 2 ^ (8 * E + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hnd9 : [u + 16, u + 17, u + 24, u + 25, u + 26, u, u + 1, u + 2, u + 3].Nodup := by simp
  refine XV.seq (XV.mono (XV.isqrt hL (r := u + 16)
    (dd := u + 17) (q := u + 24) (t := u + 25) (n1 := u + 26) (z := u) (one := u + 1) (two := u + 2)
    (four := u + 3) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) hnd9
    (n := n) (by rw [x1, ← hnX]; push_cast; rfl) z1 (by rw [P1.2.1 _ (by omega), h1])
    (by rw [P1.2.1 _ (by omega), h2]) (by rw [P1.2.1 _ (by omega), h4])
    (by calc 4 * n + 4 ≤ 2 ^ (8 * E + 3) := by have := Nat.two_pow_pos (8 * E); rw [pow_add]; omega
          _ < 2 ^ ℓ := Nat.pow_lt_pow_right (by norm_num) (by omega))) (by omega) fun σ' h => h)
    fun σ2 ⟨t2, _, F2⟩ => ?_
  have bt : |Transfer.updT p q s| ≤ 2 ^ (4 * E) := updT_le bs hq
  have t2' : σ2.sc (u + 17) = Transfer.updT p q s := by rw [t2]; simp [Transfer.updT, hn]
  have z2 : σ2.sc u = 0 := by rw [F2.2.1 u (by simp), z1]
  have d2 : σ2.sc (u + 8) = dp1 := by rw [F2.2.1 _ (by simp), P1.2.1 _ (by omega), hd1]
  -- `(d + 1) t`
  refine XV.seq (XV.ieRun (E := 4 * E) (e := ieMul (u + 8) (u + 17)) (v := dp1 * Transfer.updT p q s) hL
    (x := u + 18)
    (t := u + 24) (z := u) (by simp only [ieMul, IE.WF]; exact ⟨(by intro h; cases h), by omega, by omega⟩)
    (by omega) (by omega) (by simp only [ieMul, IE.scr]; omega) z2
    (by simp only [ieMul, IE.Leaves]; exact ⟨⟨dp1, d2, abs_le_pow_mono bd1 (by omega)⟩, ⟨_, t2', bt⟩⟩)
    (by simp only [ieMul, IE.top, IE.mag]; omega)
    (by simp only [ieMul, IE.eval, RealRAM.Op2.eval, d2, t2']; push_cast; ring)) fun σ3 ⟨x3, b3, d3, P3⟩ => ?_
  have bT : |dp1 * Transfer.updT p q s| ≤ 2 ^ (5 * E) := by
    rw [abs_mul]
    calc |dp1| * |Transfer.updT p q s| ≤ 2 ^ E * 2 ^ (4 * E) := mul_le_mul bd1 bt (abs_nonneg _) (by positivity)
      _ = 2 ^ (5 * E) := by rw [← pow_add]; ring_nf
  have z3 : σ3.sc u = 0 := by rw [P3.2.1 u (by omega), z2]
  -- `2 (d + 1) t`
  refine XV.mono (XV.ieRun (E := 5 * E) (e := IE.op .add (.sc (u + 18)) (.sc (u + 18)))
    (v := dp1 * Transfer.updT p q s + dp1 * Transfer.updT p q s) hL (x := u + 19) (t := u + 24) (z := u)
    (by simp only [IE.WF]; exact ⟨(by intro h; cases h), by omega, by omega⟩)
    (by omega) (by omega) (by simp only [IE.scr]; omega) z3
    (by simp only [IE.Leaves]; exact ⟨⟨_, x3, bT⟩, ⟨_, x3, bT⟩⟩)
    (by simp only [IE.top, IE.mag]; omega)
    (by simp only [IE.eval, RealRAM.Op2.eval, x3]; push_cast; ring)) le_rfl fun σ4 ⟨x4, _, d4, P4⟩ => ?_
  refine ⟨by rw [P4.2.1 _ (by omega), P3.2.1 _ (by omega), t2'], by rw [P4.2.1 _ (by omega), x3]; norm_cast,
    by rw [x4]; norm_cast,
    by rw [d4, d3, F2.2.2.2.1, d1], ?_⟩
  exact (((FrameA.ofP (P1.mono (fun y h => by omega) (fun _ h => h))).trans (FrameA.ofList F2
    (fun y hy => by simp at hy; omega) (fun j hj => by simp at hj))).trans
    (FrameA.ofP (P3.mono (fun y h => by omega) (fun _ h => h)))).trans
    (FrameA.ofP (P4.mono (fun y h => by omega) (fun _ h => h)))

/-! ## The new state -/

/-- `â'_i = â_i - rnd(v_i 2^q / ((d + 1) t))`. -/
def upda (q : ℕ) (t : ℤ) (a v : Fin d → ℤ) : Fin d → ℤ := fun i => a i - RQ.rndI (v i * 2 ^ q) ((d + 1) * t)

/-- `Â'_{ik} = rnd(κ_N ((d + 1)ŝ Â_{ik} - 2 v_i v_k) / (κ_D (d + 1)ŝ))`. -/
def updM (s : ℤ) (A : Matrix (Fin d) (Fin d) ℤ) (v : Fin d → ℤ) : Matrix (Fin d) (Fin d) ℤ :=
  fun i k => RQ.rndI (kapN d * ((d + 1) * s * A i k - 2 * v i * v k)) (kapD d * (d + 1) * s)

/-- `ellUpd` with its intermediate values named. -/
theorem ellUpd_eq (p q j : ℕ) (capA capa : ℤ) (A : Matrix (Fin d) (Fin d) ℤ) (a c : Fin d → ℤ) :
    ellUpd p q j capA capa A a c =
      if c ⬝ᵥ (A *ᵥ c) < 2 ^ (p - 2 * j) * (c ⬝ᵥ c) then none else
      if (∃ i k, capA < |updM (c ⬝ᵥ (A *ᵥ c)) A (A *ᵥ c) i k|) ∨
          (∃ i, capa < |upda q (updT p q (c ⬝ᵥ (A *ᵥ c))) a (A *ᵥ c) i|) then none else
      some (updM (c ⬝ᵥ (A *ᵥ c)) A (A *ᵥ c), upda q (updT p q (c ⬝ᵥ (A *ᵥ c))) a (A *ᵥ c)) := by
  simp only [ellUpd, Arr.get2_ofFn', Arr.get_ofFn', updM, upda, updT, updX]
  rfl

theorem ellEntry_eq (s : ℤ) (A : Matrix (Fin d) (Fin d) ℤ) (v : Fin d → ℤ) (i k : Fin d) :
    ellEntry ((d + 1) * s) (kapN d) (kapD d * ((d + 1) * s)) (kapD d * ((d + 1) * s) + kapD d * ((d + 1) * s))
      (A i k) (v i) (v k) = updM s A v i k := by
  unfold ellEntry updM RQ.rndI; congr 1 <;> ring

/-- `â_i - (2 v_i 2^q + (d + 1) t) / (2 (d + 1) t)` as an expression: `â` in the array `a0 + 1`, `v` in `a0 + 3`, at the
register `nk`; `2^q`, `(d + 1) t`, `2 (d + 1) t` in the slots `u + 7`, `u + 18`, `u + 19`. -/
def ieAp (u a0 nk : ℕ) : IE :=
  .op .sub (.arr (a0 + 1) nk) (.ediv (.op .add (.op .add (.op .mul (.arr (a0 + 3) nk) (.sc (u + 7)))
    (.op .mul (.arr (a0 + 3) nk) (.sc (u + 7)))) (.sc (u + 18))) (.sc (u + 19)))

/-- `â'` into the array `a0 + 5`, the scalars of the entry, `Â'` into the array `a0 + 4` row by row. -/
def xupdA (L : Layout) (u a0 n0 nd none : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst (n0 + 1) 0)))
  (.seq (xmapE L u (u + 24) (ieAp u a0 (n0 + 2)) (a0 + 5) (n0 + 1) none (n0 + 2) nd none)
  (.seq ((ieMul (u + 8) (u + 14)).code L u (u + 20) (u + 24))
  (.seq ((ieMul (u + 10) (u + 20)).code L u (u + 22) (u + 24))
  (.seq ((IE.op .add (.sc (u + 22)) (.sc (u + 22))).code L u (u + 23) (u + 24))
  (.seq (.prim (.frag (.nconst (n0 + 1) 0)))
  (xforN n0 nd none (xellRowH L u (u + 20) a0 (a0 + 3) (a0 + 4) n0 (n0 + 1) (n0 + 2) nd none)))))))

theorem abs_mul_le_pow {x y : ℤ} {a b : ℕ} (hx : |x| ≤ 2 ^ a) (hy : |y| ≤ 2 ^ b) : |x * y| ≤ 2 ^ (a + b) := by
  rw [abs_mul, pow_add]; exact mul_le_mul hx hy (abs_nonneg _) (by positivity)

set_option maxHeartbeats 8000000 in
/-- The rule of `xupdA`. -/
theorem XV.updA {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {u a0 n0 nd none E q : ℕ}
    {A : Matrix (Fin d) (Fin d) ℤ} {a v : Fin d → ℤ} {s t : ℤ}
    (hS : u + 60 ≤ L.NS) (hA0 : a0 + 6 ≤ L.NA) (hN0 : n0 + 4 ≤ L.NN) (hnd : nd < L.NN) (hno : none < L.NN)
    (hnd0 : nd < n0 ∨ n0 + 4 ≤ nd) (hno0 : none < n0 ∨ n0 + 4 ≤ none) (hndo : nd ≠ none)
    (hz : σ.sc u = 0) (hσd : σ.nat nd = d) (hσ1 : σ.nat none = 1)
    (hQ : σ.sc (u + 7) = (2 : ℤ) ^ q) (hd1 : σ.sc (u + 8) = (d : ℤ) + 1) (hkD : σ.sc (u + 10) = kapD d)
    (hs : σ.sc (u + 14) = s) (hT : σ.sc (u + 18) = ((d : ℤ) + 1) * t)
    (hT2 : σ.sc (u + 19) = ((d : ℤ) + 1) * t + ((d : ℤ) + 1) * t) (hkN : σ.sc (u + 21) = kapN d)
    (hA : ∀ i k : Fin d, σ.arr a0 (d * i + k) = A i k) (ha : ∀ k : Fin d, σ.arr (a0 + 1) k = a k)
    (hv : ∀ k : Fin d, σ.arr (a0 + 3) k = v k)
    (bA : ∀ i k, |A i k| ≤ 2 ^ E) (ba : ∀ k, |a k| ≤ 2 ^ E) (bv : ∀ k, |v k| ≤ 2 ^ (3 * E))
    (bs : |s| ≤ 2 ^ (7 * E)) (bt : |t| ≤ 2 ^ (4 * E)) (hq : q ≤ E) (bd1 : (d : ℤ) + 1 ≤ 2 ^ E)
    (bkN : |kapN d| ≤ 2 ^ E) (bkD : |kapD d| ≤ 2 ^ E) (hE1 : 1 ≤ E) (hℓ : 64 * E + 16 < ℓ) :
    XRunsB L X ℓa ℓ (xupdA L u a0 n0 nd none) σ (50 * d * d + 40 * d + 20) (fun σ' =>
      (∀ k : Fin d, σ'.arr (a0 + 5) k = upda q t a v k) ∧
      (∀ i k : Fin d, σ'.arr (a0 + 4) (d * i + k) = updM s A v i k) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => u + 20 ≤ y) (fun j => n0 ≤ j ∧ j < n0 + 4)
        (fun b c => (b = a0 + 5 ∧ c < d) ∨ (b = a0 + 4 ∧ c < d * d)) σ σ') := by
  have hda := asz_lt hL (a := a0) (by omega)
  have hdl : ∀ k < d, k < asz d := fun k hk => by unfold asz; nlinarith
  have bd1' : |(d : ℤ) + 1| ≤ 2 ^ E := by rw [abs_of_pos (by positivity)]; exact bd1
  have bQ : |(2 : ℤ) ^ q| ≤ 2 ^ E := by
    rw [abs_of_pos (by positivity)]; exact pow_le_pow_right₀ (by norm_num) hq
  have bT : |((d : ℤ) + 1) * t| ≤ 2 ^ (5 * E) := by
    have := abs_mul_le_pow bd1' bt; rwa [show E + 4 * E = 5 * E by ring] at this
  have bT2 : |((d : ℤ) + 1) * t + ((d : ℤ) + 1) * t| ≤ 2 ^ (6 * E) := by
    calc _ ≤ |((d : ℤ) + 1) * t| + |((d : ℤ) + 1) * t| := abs_add_le _ _
      _ ≤ 2 ^ (5 * E) + 2 ^ (5 * E) := add_le_add bT bT
      _ ≤ 2 ^ (6 * E) := by
        have : (2 : ℤ) ^ (5 * E) * 2 ≤ 2 ^ (6 * E) := by
          rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
        linarith
  -- `â'`
  refine XV.mono (K := 1 + ((d * (16 + 6) + 3) + (3 + (3 + (3 + (1 + (d * ((d * (41 + (2 + 1) + 3) + 3) + 3) +
    3)))))))
    (XV.seq (XV.nconst hL (i := n0 + 1) (by omega) 0 (by positivity)) fun σ0 e0 => ?_) (by nlinarith) fun _ h => h
  subst e0
  refine XV.seq (XV.mapE (E := 6 * E) (N := d) (base := 0) (st := 1) (F := vext (upda q t a v)) hL
    (z := u) (t := u + 24) (e := ieAp u a0 (n0 + 2)) (aB := a0 + 5) (nr := n0 + 1) (nst := none) (nk := n0 + 2)
    (nn := nd) (none := none)
    (by simp only [ieAp, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega) (by omega)
    (by simp only [ieAp, IE.scr]; omega) (by simpa using hz) (by omega) (by omega) hno (by omega) hnd hno
    (nodup4 (by omega) (by omega) (by omega) (by omega) (by omega) hndo) (by omega) (by omega)
    (by simp; rw [if_neg (by omega), hσd]) (by simp; rw [if_neg (by omega), hσ1]) (by simp)
    (by simp; rw [if_neg (by omega), hσ1]) one_pos (fun k hk => by simpa using hdl k hk)
    (by unfold asz at hda; nlinarith) (by unfold asz at hda; nlinarith) (by have := hL.1; omega)
    (by simp only [ieAp, IE.top, IE.mag]; omega) ?_) fun σ1 ⟨a1, r1, d1, F1⟩ => ?_
  · intro k hk σ' hF hd hkt hkr
    have hkr' : σ'.nat (n0 + 1) = k := by simpa using hkr
    have e1 : σ'.arr (a0 + 1) k = a ⟨k, hk⟩ := by
      rw [hF.2.2.1 _ _ (fun h => by omega)]; exact ha ⟨k, hk⟩
    have e3 : σ'.arr (a0 + 3) k = v ⟨k, hk⟩ := by
      rw [hF.2.2.1 _ _ (fun h => by omega)]; exact hv ⟨k, hk⟩
    have e7 : σ'.sc (u + 7) = (2 : ℤ) ^ q := by rw [hF.2.1 _ (by omega)]; simpa using hQ
    have e18 : σ'.sc (u + 18) = ((d : ℤ) + 1) * t := by rw [hF.2.1 _ (by omega)]; simpa using hT
    have e19 : σ'.sc (u + 19) = ((d : ℤ) + 1) * t + ((d : ℤ) + 1) * t := by rw [hF.2.1 _ (by omega)]; simpa using hT2
    have hk' : σ'.nat (n0 + 2) < asz d := by rw [hkt]; exact hdl k hk
    refine ⟨⟨⟨hk', a ⟨k, hk⟩, by rw [hkt, e1], abs_le_pow_mono (ba _) (by omega)⟩,
      ⟨⟨⟨⟨hk', v ⟨k, hk⟩, by rw [hkt, e3], abs_le_pow_mono (bv _) (by omega)⟩,
        ⟨_, by exact_mod_cast e7, abs_le_pow_mono bQ (by omega)⟩⟩,
        ⟨⟨hk', v ⟨k, hk⟩, by rw [hkt, e3], abs_le_pow_mono (bv _) (by omega)⟩,
        ⟨_, by exact_mod_cast e7, abs_le_pow_mono bQ (by omega)⟩⟩⟩,
        ⟨_, by exact_mod_cast e18, abs_le_pow_mono bT (by omega)⟩⟩,
      ⟨_, by exact_mod_cast e19, bT2⟩⟩, ?_⟩
    simp only [ieAp, IE.eval, RealRAM.Op2.eval, hkt, e1, e3, e7, e18, e19]
    rw [vext_lt _ hk]
    norm_cast
    rw [Int.floor_intCast, Int.floor_intCast]
    simp only [upda, RQ.rndI]
    congr 2 <;> push_cast <;> ring
  -- the scalars of the entry
  have F1' : FrameA (fun y => u + 24 ≤ y) (fun j => n0 ≤ j ∧ j < n0 + 4) (fun b c => b = a0 + 5 ∧ c < d) σ σ1 :=
    ((FrameA.refl _ _ _ σ).setNat (by omega) 0).trans (F1.mono (fun _ h => h) (fun j h => by omega)
      (fun b c h => ⟨h.1, by omega⟩))
  have z1 : σ1.sc u = 0 := by rw [F1'.2.1 u (by omega), hz]
  have s1 : σ1.sc (u + 14) = s := by rw [F1'.2.1 _ (by omega), hs]
  have c1v : ∀ y, y < u + 24 → σ1.sc y = σ.sc y := fun y hy => F1'.2.1 y (by omega)
  have bc1 : |((d : ℤ) + 1) * s| ≤ 2 ^ (8 * E) := by
    have := abs_mul_le_pow bd1' bs; rwa [show E + 7 * E = 8 * E by ring] at this
  have L2 : (ieMul (u + 8) (u + 14)).Leaves (7 * E) σ1 := by
    simp only [ieMul, IE.Leaves]
    exact ⟨⟨_, by rw [c1v _ (by omega), hd1]; norm_cast, abs_le_pow_mono bd1' (by omega)⟩, ⟨s, s1, bs⟩⟩
  refine XV.seq (XV.ieRun (E := 7 * E) (e := ieMul (u + 8) (u + 14)) (v := ((d : ℤ) + 1) * s) hL (x := u + 20)
    (t := u + 24) (z := u) (by simp only [ieMul, IE.WF]; exact ⟨(by intro h; cases h), by omega, by omega⟩)
    (by omega) (by omega) (by simp only [ieMul, IE.scr]; omega) z1
    L2
    (by simp only [ieMul, IE.top, IE.mag]; omega)
    (by simp only [ieMul, IE.eval, RealRAM.Op2.eval, c1v (u + 8) (by omega), hd1, s1]; push_cast; ring))
    fun σ2 ⟨x2, _, d2, P2⟩ => ?_
  have z2 : σ2.sc u = 0 := by rw [P2.2.1 u (by omega), z1]
  have bD : |kapD d * (((d : ℤ) + 1) * s)| ≤ 2 ^ (9 * E) := by
    have := abs_mul_le_pow bkD bc1; rwa [show E + 8 * E = 9 * E by ring] at this
  have L3 : (ieMul (u + 10) (u + 20)).Leaves (8 * E) σ2 := by
    simp only [ieMul, IE.Leaves]
    exact ⟨⟨_, by rw [P2.2.1 _ (by omega), c1v _ (by omega), hkD], abs_le_pow_mono bkD (by omega)⟩, ⟨_, x2, bc1⟩⟩
  refine XV.seq (XV.ieRun (E := 8 * E) (e := ieMul (u + 10) (u + 20)) (v := kapD d * (((d : ℤ) + 1) * s)) hL
    (x := u + 22) (t := u + 24) (z := u) (by simp only [ieMul, IE.WF]; exact ⟨(by intro h; cases h), by omega,
      by omega⟩) (by omega) (by omega) (by simp only [ieMul, IE.scr]; omega) z2
    L3
    (by simp only [ieMul, IE.top, IE.mag]; omega)
    (by simp only [ieMul, IE.eval, RealRAM.Op2.eval, P2.2.1 (u + 10) (by omega), c1v (u + 10) (by omega), hkD,
      x2]; push_cast; ring)) fun σ3 ⟨x3, _, d3, P3⟩ => ?_
  have z3 : σ3.sc u = 0 := by rw [P3.2.1 u (by omega), z2]
  refine XV.seq (XV.ieRun (E := 9 * E) (e := IE.op .add (.sc (u + 22)) (.sc (u + 22)))
    (v := kapD d * (((d : ℤ) + 1) * s) + kapD d * (((d : ℤ) + 1) * s)) hL (x := u + 23) (t := u + 24) (z := u)
    (by simp only [IE.WF]; exact ⟨(by intro h; cases h), by omega, by omega⟩) (by omega) (by omega)
    (by simp only [IE.scr]; omega) z3 (by simp only [IE.Leaves]; exact ⟨⟨_, x3, bD⟩, ⟨_, x3, bD⟩⟩)
    (by simp only [IE.top, IE.mag]; omega)
    (by simp only [IE.eval, RealRAM.Op2.eval, x3]; push_cast; ring)) fun σ4 ⟨x4, _, d4, P4⟩ => ?_
  have bD2 : |kapD d * (((d : ℤ) + 1) * s) + kapD d * (((d : ℤ) + 1) * s)| ≤ 2 ^ (10 * E) := by
    calc _ ≤ |kapD d * (((d : ℤ) + 1) * s)| + |kapD d * (((d : ℤ) + 1) * s)| := abs_add_le _ _
      _ ≤ 2 ^ (9 * E) + 2 ^ (9 * E) := add_le_add bD bD
      _ ≤ 2 ^ (10 * E) := by
        have : (2 : ℤ) ^ (9 * E) * 2 ≤ 2 ^ (10 * E) := by
          rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
        linarith
  -- the frame so far
  have P24 : FrameA (fun y => u + 20 ≤ y) (fun j => n0 ≤ j ∧ j < n0 + 4) (fun b c => b = a0 + 5 ∧ c < d) σ σ4 :=
    ((F1'.mono (fun y h => by omega) (fun _ h => h) (fun _ _ h => h)).trans
      (FrameA.ofP (P2.mono (fun y h => by omega) (fun _ h => h.elim)))).trans
      ((FrameA.ofP (P3.mono (fun y h => by omega) (fun _ h => h.elim))).trans
      (FrameA.ofP (P4.mono (fun y h => by omega) (fun _ h => h.elim))))
  have o20 : σ4.sc (u + 20) = (((((d : ℤ) + 1) * s : ℤ)) : ℝ) := by rw [P4.2.1 _ (by omega), P3.2.1 _ (by omega), x2]
  have o21 : σ4.sc (u + 21) = kapN d := by
    rw [P4.2.1 _ (by omega), P3.2.1 _ (by omega), P2.2.1 _ (by omega), c1v _ (by omega), hkN]
  have z4 : σ4.sc u = 0 := by rw [P4.2.1 u (by omega), z3]
  have d4' : σ4.draws = σ.draws := by rw [d4, d3, d2, d1]; rfl
  have o22 : σ4.sc (u + 22) = (((kapD d * (((d : ℤ) + 1) * s) : ℤ)) : ℝ) := by rw [P4.2.1 _ (by omega), x3]
  -- `Â'`, row by row
  refine XV.seq (XV.nconst hL (i := n0 + 1) (by omega) 0 (by positivity)) fun σ5 e5 => ?_
  subst e5
  let J : ℕ → Env d → Prop := fun i σ' => σ'.nat (n0 + 1) = d * i ∧ σ'.draws = σ.draws ∧
    (∀ i' (h : i' < i) (hd : i' < d) (k : Fin d), σ'.arr (a0 + 4) (d * i' + k) = updM s A v ⟨i', hd⟩ k) ∧
    FrameA (fun y => u + 24 ≤ y) (fun j => j = n0 ∨ j = n0 + 1 ∨ j = n0 + 2) (fun b c => b = a0 + 4 ∧ c < d * i)
      (σ4.setNat (n0 + 1) 0) σ'
  have hnd4 : (σ4.setNat (n0 + 1) 0).nat nd = d := by
    rw [Env.setNat_nat, if_neg (by omega), P24.1 nd (by omega), hσd]
  have hno4 : (σ4.setNat (n0 + 1) 0).nat none = 1 := by
    rw [Env.setNat_nat, if_neg (by omega), P24.1 none (by omega), hσ1]
  refine XV.mono (XV.forN hL (i := n0) (n := nd) (one := none) (body := xellRowH L u (u + 20) a0 (a0 + 3) (a0 + 4)
    n0 (n0 + 1) (n0 + 2) nd none) (by omega) hnd hno (by omega) (by omega) d (d * (41 + (2 + 1) + 3) + 3)
    (by unfold asz at hda; nlinarith) J _ hnd4 hno4
    ⟨by rw [Env.setNat_nat, if_neg (by omega)]; simp, by simp [d4'], fun i' h => absurd h (Nat.not_lt_zero _),
      (FrameA.refl _ _ _ _).setNat (Or.inl rfl) 0⟩ ?_) le_rfl fun σ' ⟨⟨_, hd, hy, hF⟩, _⟩ => ?_
  · intro i hi σ' ⟨hr, hd, hy, hF⟩ hit hid hi1
    have sc' : ∀ y, y < u + 24 → σ'.sc y = σ4.sc y := fun y hy => hF.2.1 y (by omega)
    have bAi : ∀ k < d, |vext (A ⟨i, hi⟩) k| ≤ 2 ^ (10 * E) := fun k hk => by
      rw [vext_lt _ hk]; exact abs_le_pow_mono (bA _ _) (by omega)
    have bVv : ∀ k < d, |vext v k| ≤ 2 ^ (10 * E) := fun k hk => by
      rw [vext_lt _ hk]; exact abs_le_pow_mono (bv _) (by omega)
    refine XV.mono (XV.noDraws (XV.ellRowH hL (z := u) (o := u + 20) (aA := a0) (aV := a0 + 3) (aB := a0 + 4) (ni := n0)
      (nr := n0 + 1) (nk := n0 + 2) (nd := nd) (none := none) (by omega) (by omega)
      (by rw [sc' u (by omega), z4]) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) hnd hno (nodup5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) hndo) hi hit hr hid hi1 (c1 := ((d : ℤ) + 1) * s) (kN := kapN d)
      (D := kapD d * (((d : ℤ) + 1) * s)) (D2 := kapD d * (((d : ℤ) + 1) * s) + kapD d * (((d : ℤ) + 1) * s))
      (by rw [sc' _ (by omega), o20]) (by rw [sc' _ (by omega), o21]) (by rw [sc' _ (by omega), o22])
      (by rw [sc' _ (by omega), x4]) (Ai := vext (A ⟨i, hi⟩)) (Vv := vext v)
      (fun k hk => by
        rw [hF.2.2.1 a0 _ (fun h => by omega), Env.setNat_arr, P24.2.2.1 a0 _ (fun h => by omega), vext_lt _ hk]
        exact hA ⟨i, hi⟩ ⟨k, hk⟩)
      (fun k hk => by
        rw [hF.2.2.1 (a0 + 3) _ (fun h => by omega), Env.setNat_arr, P24.2.2.1 (a0 + 3) _ (fun h => by omega),
          vext_lt _ hk]
        exact hv ⟨k, hk⟩)
      (e := 10 * E) (by omega) (abs_le_pow_mono bc1 (by omega)) (abs_le_pow_mono bkN (by omega))
      (abs_le_pow_mono bD (by omega)) bD2 bAi bVv (by unfold asz at hda; exact hda)) (noCoins_xellRowH ..)) le_rfl
      fun σ'' ⟨⟨hk'', hr'', hF''⟩, hd''⟩ => ?_
    refine ⟨by rw [hF''.1 n0 (by omega), hit], by rw [hF''.1 nd (by omega), hid],
      by rw [hF''.1 none (by omega), hi1], ?_, ?_, ?_, ?_⟩
    · rw [Env.setNat_nat, if_neg (by omega), hr'']; ring
    · simp only [Env.setNat_draws, hd'', hd]
    · intro i' hi' hd' k
      simp only [Env.setNat_arr]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hlt | rfl
      · have hcell : d * i' + k < d * i := by
          have := k.2; have : d * (i' + 1) ≤ d * i := Nat.mul_le_mul_left d hlt; nlinarith
        rw [hF''.2.2.1 _ _ (fun h => by omega)]; exact hy i' hlt hd' k
      · rw [hk'' k k.2, vext_lt _ hi, vext_lt _ k.2, vext_lt _ k.2]
        exact_mod_cast ellEntry_eq s A v ⟨i', hd'⟩ k
    · exact (hF.mono (fun _ h => h) (fun _ h => h) (fun b c h => ⟨h.1, by nlinarith [h.2]⟩)).trans
        ((hF''.mono (fun _ h => h) (fun _ h => by omega) (fun b c h => ⟨h.1, by nlinarith [h.2.2]⟩)).setNat
          (Or.inl rfl) _)
  · refine ⟨fun k => ?_, fun i k => by rw [hy i i.2 i.2 k], hd, ?_⟩
    · rw [hF.2.2.1 _ _ (fun h => by omega), Env.setNat_arr]
      have := a1 k k.2
      simp only [zero_add, one_mul] at this
      rw [P4.2.2.1, P3.2.2.1, P2.2.2.1, this, vext_lt _ k.2]
    · exact (P24.mono (fun _ h => h) (fun _ h => h) (fun b c h => Or.inl h)).trans
        (((FrameA.refl _ _ _ σ4).setNat (by omega) 0).trans hF |>.mono (fun y h => by omega) (fun j h => by omega)
          (fun b c h => Or.inr ⟨h.1, by nlinarith [h.2]⟩))

/-! ## The caps and the copy -/

/-- A matrix read row-major on the naturals, `0` outside. -/
def mext (M : Matrix (Fin d) (Fin d) ℤ) (c : ℕ) : ℤ :=
  if h : c < d * d then M ⟨c / d, Nat.div_lt_of_lt_mul h⟩ ⟨c % d, Nat.mod_lt _ (by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp at h
    · exact hd)⟩ else 0

theorem mext_cell (M : Matrix (Fin d) (Fin d) ℤ) (i k : Fin d) : mext M (d * i + k) = M i k := by
  have hk := k.2
  have hi := i.2
  have hc : d * i + k < d * d := by nlinarith
  unfold mext
  rw [dif_pos hc]
  congr 1 <;> ext <;> simp [Nat.mul_add_div (by omega : 0 < d), Nat.div_eq_of_lt hk, Nat.mul_add_mod,
    Nat.mod_eq_of_lt hk]

theorem cap_lt_iff {cap x : ℤ} (h : 0 ≤ cap) : cap < |x| ↔ cap * cap < x * x := by
  rw [← abs_mul_abs_self x]
  exact (mul_self_lt_mul_self_iff h (abs_nonneg x))

/-- The caps (K2) into the flag `u + 13`; if it stays `0`, the copy of `Â'`, `â'` into `Â`, `â`. -/
def xupdC (L : Layout) (u a0 n0 nd none : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst (n0 + 1) 0)))
  (.seq (xanyE L u (u + 13) (u + 1) (u + 24) (ieMul (u + 12) (u + 12))
      (.op .mul (.arr (a0 + 5) (n0 + 2)) (.arr (a0 + 5) (n0 + 2))) (n0 + 1) none (n0 + 2) nd none)
  (.seq (xnmul (n0 + 3) nd nd)
  (.seq (.prim (.frag (.nconst (n0 + 1) 0)))
  (.seq (xanyE L u (u + 13) (u + 1) (u + 24) (ieMul (u + 11) (u + 11))
      (.op .mul (.arr (a0 + 4) (n0 + 2)) (.arr (a0 + 4) (n0 + 2))) (n0 + 1) none (n0 + 2) (n0 + 3) none)
  (xifS L u (u + 13) .skip
    (.seq (.prim (.frag (.nconst (n0 + 1) 0)))
    (.seq (xmapE L u (u + 24) (.arr (a0 + 4) (n0 + 2)) a0 (n0 + 1) none (n0 + 2) (n0 + 3) none)
    (.seq (.prim (.frag (.nconst (n0 + 1) 0)))
    (xmapE L u (u + 24) (.arr (a0 + 5) (n0 + 2)) (a0 + 1) (n0 + 1) none (n0 + 2) nd none)))))))))

theorem mext_eq {f : ℕ → ℝ} {M : Matrix (Fin d) (Fin d) ℤ} (h : ∀ i k : Fin d, f (d * i + k) = M i k) {c : ℕ}
    (hc : c < d * d) : f c = mext M c := by
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hc)
  have := h ⟨c / d, Nat.div_lt_of_lt_mul hc⟩ ⟨c % d, Nat.mod_lt _ hd⟩
  rw [show d * (c / d) + c % d = c from Nat.div_add_mod c d] at this
  rw [this]; unfold mext; rw [dif_pos hc]

theorem abs_mext_le {M : Matrix (Fin d) (Fin d) ℤ} {B : ℤ} (h : ∀ i k, |M i k| ≤ B) (hB : 0 ≤ B) (c : ℕ) :
    |mext M c| ≤ B := by
  unfold mext; split_ifs
  · exact h _ _
  · simpa using hB

theorem abs_vext_le {x : Fin d → ℤ} {B : ℤ} (h : ∀ k, |x k| ≤ B) (hB : 0 ≤ B) (k : ℕ) : |vext x k| ≤ B := by
  unfold vext; split_ifs
  · exact h _
  · simpa using hB

theorem capM_iff {cap : ℤ} (h0 : 0 ≤ cap) (M : Matrix (Fin d) (Fin d) ℤ) :
    (∃ i k, cap < |M i k|) ↔ ∃ c < d * d, cap * cap < mext M c * mext M c := by
  constructor
  · rintro ⟨i, k, h⟩
    have hk := k.2
    have hi := i.2
    refine ⟨d * i + k, by nlinarith, ?_⟩
    rw [mext_cell]; exact (cap_lt_iff h0).1 h
  · rintro ⟨c, hc, h⟩
    unfold mext at h; rw [dif_pos hc] at h
    exact ⟨_, _, (cap_lt_iff h0).2 h⟩

theorem capV_iff {cap : ℤ} (h0 : 0 ≤ cap) (x : Fin d → ℤ) :
    (∃ i, cap < |x i|) ↔ ∃ k < d, cap * cap < vext x k * vext x k := by
  constructor
  · rintro ⟨i, h⟩
    exact ⟨i, i.2, by rw [vext_lt _ i.2]; exact (cap_lt_iff h0).1 h⟩
  · rintro ⟨k, hk, h⟩
    rw [vext_lt _ hk] at h
    exact ⟨_, (cap_lt_iff h0).2 h⟩

set_option maxHeartbeats 8000000 in
/-- The rule of `xupdC`: the flag `u + 13` goes from `0` to `1` when a cap fails; otherwise `Â'`, `â'` are copied into
`Â`, `â`. -/
theorem XV.updC {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {u a0 n0 nd none E : ℕ}
    {A' : Matrix (Fin d) (Fin d) ℤ} {a' : Fin d → ℤ} {capA capa : ℤ}
    (hS : u + 60 ≤ L.NS) (hA0 : a0 + 6 ≤ L.NA) (hN0 : n0 + 4 ≤ L.NN) (hnd : nd < L.NN) (hno : none < L.NN)
    (hnd0 : nd < n0 ∨ n0 + 4 ≤ nd) (hno0 : none < n0 ∨ n0 + 4 ≤ none) (hndo : nd ≠ none)
    (hz : σ.sc u = 0) (h1 : σ.sc (u + 1) = 1) (hf : σ.sc (u + 13) = 0) (hcA : σ.sc (u + 11) = capA)
    (hca : σ.sc (u + 12) = capa) (hσd : σ.nat nd = d) (hσ1 : σ.nat none = 1)
    (hA' : ∀ i k : Fin d, σ.arr (a0 + 4) (d * i + k) = A' i k) (ha' : ∀ k : Fin d, σ.arr (a0 + 5) k = a' k)
    (bA' : ∀ i k, |A' i k| ≤ 2 ^ (10 * E + 3)) (ba' : ∀ k, |a' k| ≤ 2 ^ (10 * E + 3))
    (hcA0 : 0 ≤ capA) (hca0 : 0 ≤ capa) (bcA : capA ≤ 2 ^ E) (bca : capa ≤ 2 ^ E) (hℓ : 64 * E + 16 < ℓ) :
    XRunsB L X ℓa ℓ (xupdC L u a0 n0 nd none) σ (25 * d * d + 25 * d + 20) (fun σ' =>
      (((∃ i k, capA < |A' i k|) ∨ (∃ i, capa < |a' i|)) → σ'.sc (u + 13) = 1) ∧
      (¬ ((∃ i k, capA < |A' i k|) ∨ (∃ i, capa < |a' i|)) → σ'.sc (u + 13) = 0 ∧
        (∀ i k : Fin d, σ'.arr a0 (d * i + k) = A' i k) ∧ ∀ k : Fin d, σ'.arr (a0 + 1) k = a' k) ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => y = u + 13 ∨ u + 24 ≤ y) (fun j => n0 ≤ j ∧ j < n0 + 4)
        (fun b c => (b = a0 ∧ c < d * d) ∨ (b = a0 + 1 ∧ c < d)) σ σ') := by
  have hda := asz_lt hL (a := a0) (by omega)
  have hdd : d * d < 2 ^ ℓa := by unfold asz at hda; nlinarith
  have hdl : d < 2 ^ ℓa := by unfold asz at hda; nlinarith
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  have hcd : ∀ k < d, 0 + 1 * k < asz d := fun k hk => by unfold asz; nlinarith
  have hcdd : ∀ k < d * d, 0 + 1 * k < asz d := fun k hk => by unfold asz; nlinarith
  have hB : (0 : ℤ) ≤ 2 ^ (10 * E + 3) := by positivity
  have bca' : |capa| ≤ 2 ^ (10 * E + 3) := by
    rw [abs_of_nonneg hca0]; exact bca.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have bcA' : |capA| ≤ 2 ^ (10 * E + 3) := by
    rw [abs_of_nonneg hcA0]; exact bcA.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by rw [abs_zero]; positivity
  have h1' : |(1 : ℝ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  have nAr : ∀ b c, b = a0 + 4 ∨ b = a0 + 5 → ¬ ((b = a0 ∧ c < d * d) ∨ (b = a0 + 1 ∧ c < d)) := by
    intro b c hb h; rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  -- (K2) on `â'`
  refine XV.mono (K := 1 + ((d * (3 + 5 + 6) + 3) + (1 + (1 + ((d * d * (3 + 5 + 6) + 3) +
    ((1 + ((d * d * (2 + 6) + 3) + (1 + (d * (2 + 6) + 3)))) + 2))))))
    (XV.seq (XV.nconst hL (i := n0 + 1) (by omega) 0 (by positivity)) fun σ0 e0 => ?_) (by nlinarith) fun _ h => h
  subst e0
  refine XV.seq (XV.anyE (E := 10 * E + 3) (N := d) (base := 0) (st := 1) (F1 := fun _ => capa * capa)
    (F2 := fun k => vext a' k * vext a' k) hL (z := u) (f := u + 13) (one := u + 1) (t := u + 24)
    (e1 := ieMul (u + 12) (u + 12)) (e2 := .op .mul (.arr (a0 + 5) (n0 + 2)) (.arr (a0 + 5) (n0 + 2)))
    (nr := n0 + 1) (nst := none) (nk := n0 + 2) (nn := nd) (none := none)
    (by simp only [ieMul, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega)
    (by simp only [IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp only [ieMul, IE.scr]; omega) (by simp only [IE.scr]; omega) (by simpa using hz) (by simpa using h1)
    (by omega) hno (by omega) hnd hno (nodup4 (by omega) (by omega) (by omega) (by omega) (by omega) hndo)
    (by omega) (by omega) (by simp; rw [if_neg (by omega), hσd]) (by simp; rw [if_neg (by omega), hσ1]) (by simp)
    (by simp; rw [if_neg (by omega), hσ1]) hdl (by simpa using hdl) hsa
    (by simp only [ieMul, IE.top, IE.mag]; omega) (by simp only [IE.top, IE.mag]; omega) ?_)
    fun σ1 ⟨f1, g1, r1, d1, Fr1⟩ => ?_
  · intro k hk σ' hF hd hkt hkr
    have G := ((FrameA.refl _ _ (fun _ _ => False) σ).setNat (N := fun j => j = n0 + 2 ∨ j = n0 + 1)
      (Or.inr rfl) 0).trans hF
    have e5 : σ'.arr (a0 + 5) k = a' ⟨k, hk⟩ := by rw [G.2.2.1 _ _ (fun h => h)]; exact ha' ⟨k, hk⟩
    have e12 : σ'.sc (u + 12) = capa := by rw [G.2.1 _ (by omega)]; exact hca
    have hk' : σ'.nat (n0 + 2) < asz d := by rw [hkt]; simpa using hcd k hk
    refine ⟨⟨⟨⟨capa, e12, bca'⟩, ⟨capa, e12, bca'⟩⟩, ?_⟩, ⟨⟨⟨hk', a' ⟨k, hk⟩, by rw [hkt, e5], ba' _⟩,
      ⟨hk', a' ⟨k, hk⟩, by rw [hkt, e5], ba' _⟩⟩, ?_⟩⟩
    · simp only [ieMul, IE.eval, RealRAM.Op2.eval, e12]; norm_cast
    · simp only [IE.eval, RealRAM.Op2.eval, hkt, e5, vext_lt _ hk]; norm_cast
  -- the frame from `σ`
  let S : ℕ → Prop := fun y => y = u + 13 ∨ u + 24 ≤ y
  let N : ℕ → Prop := fun j => n0 ≤ j ∧ j < n0 + 4
  have G1 : FrameA S N (fun _ _ => False) σ σ1 :=
    ((FrameA.refl _ _ _ σ).setNat (by omega) 0).trans (Fr1.mono (fun _ h => h) (fun j h => by omega) (fun _ _ h => h))
  have nd1 : σ1.nat nd = d := by rw [G1.1 nd (by omega), hσd]
  have fl1 : σ1.sc (u + 13) = if ∃ k < d, capa * capa < vext a' k * vext a' k then 1 else 0 := by
    split_ifs with hc
    · exact f1 hc
    · rw [g1 (fun k hk h => hc ⟨k, hk, h⟩)]; simpa using hf
  -- `d²`, (K2) on `Â'`
  refine XV.seq (XV.nmul hL (i := n0 + 3) (a := nd) (b := nd) (by omega) hnd hnd (by rw [nd1]; exact hdl)
    (by rw [nd1]; exact hdl) (by rw [nd1]; exact hdd)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.nconst hL (i := n0 + 1) (by omega) 0 (by positivity)) fun σ3 e3 => ?_
  subst e3
  have G3 : FrameA S N (fun _ _ => False) σ ((σ1.setNat (n0 + 3) (σ1.nat nd * σ1.nat nd)).setNat (n0 + 1) 0) :=
    (G1.setNat (by omega) _).setNat (by omega) 0
  refine XV.seq (XV.anyE (E := 10 * E + 3) (N := d * d) (base := 0) (st := 1) (F1 := fun _ => capA * capA)
    (F2 := fun k => mext A' k * mext A' k) hL (z := u) (f := u + 13) (one := u + 1) (t := u + 24)
    (e1 := ieMul (u + 11) (u + 11)) (e2 := .op .mul (.arr (a0 + 4) (n0 + 2)) (.arr (a0 + 4) (n0 + 2)))
    (nr := n0 + 1) (nst := none) (nk := n0 + 2) (nn := n0 + 3) (none := none)
    (by simp only [ieMul, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega)
    (by simp only [IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp only [ieMul, IE.scr]; omega) (by simp only [IE.scr]; omega)
    (by rw [G3.2.1 u (by omega), hz]) (by rw [G3.2.1 _ (by omega), h1])
    (by omega) hno (by omega) (by omega) hno (nodup4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    (by omega) (by omega) (by simp [nd1]) (by rw [G3.1 none (by omega), hσ1]) (by simp)
    (by rw [G3.1 none (by omega), hσ1]) hdd (by simpa using hdd) hsa
    (by simp only [ieMul, IE.top, IE.mag]; omega) (by simp only [IE.top, IE.mag]; omega) ?_)
    fun σ4 ⟨f4, g4, r4, d4, Fr4⟩ => ?_
  · intro k hk σ' hF hd hkt hkr
    have G := G3.trans (hF.mono (fun _ h => h) (fun j h => by omega) (fun _ _ h => h))
    have e4 : σ'.arr (a0 + 4) k = mext A' k := by
      rw [G.2.2.1 _ _ (fun h => h)]; exact mext_eq (f := σ.arr (a0 + 4)) hA' hk
    have e11 : σ'.sc (u + 11) = capA := by rw [G.2.1 _ (by omega)]; exact hcA
    have hk' : σ'.nat (n0 + 2) < asz d := by rw [hkt]; simpa using hcdd k hk
    refine ⟨⟨⟨⟨capA, e11, bcA'⟩, ⟨capA, e11, bcA'⟩⟩, ?_⟩, ⟨⟨⟨hk', mext A' k, by rw [hkt, e4],
      abs_mext_le bA' hB k⟩, ⟨hk', mext A' k, by rw [hkt, e4], abs_mext_le bA' hB k⟩⟩, ?_⟩⟩
    · simp only [ieMul, IE.eval, RealRAM.Op2.eval, e11]; norm_cast
    · simp only [IE.eval, RealRAM.Op2.eval, hkt, e4]; norm_cast
  set σ3 := (σ1.setNat (n0 + 3) (σ1.nat nd * σ1.nat nd)).setNat (n0 + 1) 0 with hσ3
  have G4 : FrameA S N (fun _ _ => False) σ σ4 :=
    G3.trans (Fr4.mono (fun _ h => h) (fun j h => by omega) (fun _ _ h => h))
  have z4 : σ4.sc u = 0 := by rw [G4.2.1 u (by omega), hz]
  have C1 := capV_iff hca0 a'
  have C2 := capM_iff hcA0 A'
  -- the copy
  by_cases hC : (∃ i k, capA < |A' i k|) ∨ (∃ i, capa < |a' i|)
  · have fl : σ4.sc (u + 13) = 1 := by
      by_cases h2 : ∃ k < d * d, capA * capA < mext A' k * mext A' k
      · exact f4 h2
      · rw [g4 (fun k hk h => h2 ⟨k, hk, h⟩), hσ3]
        simp only [Env.setNat_sc]
        rw [fl1, if_pos]
        rcases hC with h | h
        · exact absurd (C2.1 h) h2
        · exact C1.1 h
    refine XV.mono (XV.ifS_t hL (by omega) (by omega) (by rw [z4]; exact h0) (by rw [fl]; exact h1')
      (by rw [z4, fl]; norm_num) (XV.skip σ4)) (by nlinarith) fun σ' e => ?_
    subst e
    exact ⟨fun _ => fl, fun h => absurd hC h, by rw [d4, hσ3]; simp [d1],
      G4.mono (fun _ h => h) (fun _ h => h) (fun _ _ h => h.elim)⟩
  · have fl : σ4.sc (u + 13) = 0 := by
      rw [g4 (fun k hk h => hC (Or.inl (C2.2 ⟨k, hk, h⟩))), hσ3]
      simp only [Env.setNat_sc]
      rw [fl1, if_neg (fun h => hC (Or.inr (C1.2 h)))]
    have hCf := eq_false hC
    clear f1 g1 f4 g4 C1 C2 fl1 hC
    refine XV.ifS_f hL (by omega) (by omega) (by rw [z4]; exact h0) (by rw [fl]; exact h0)
      (by rw [z4, fl]; exact lt_irrefl _) ?_
    refine XV.seq (XV.nconst hL (i := n0 + 1) (by omega) 0 (by positivity)) fun σ5 e5 => ?_
    subst e5
    have G5 : FrameA S N (fun _ _ => False) σ (σ4.setNat (n0 + 1) 0) := G4.setNat (by omega) 0
    have nd5 : (σ4.setNat (n0 + 1) 0).nat (n0 + 3) = d * d := by
      rw [Env.setNat_nat, if_neg (by omega), Fr4.1 _ (by omega), hσ3]; simp [nd1]
    refine XV.seq (XV.mapE (E := 10 * E + 3) (N := d * d) (base := 0) (st := 1) (F := mext A') hL (z := u)
      (t := u + 24) (e := .arr (a0 + 4) (n0 + 2)) (aB := a0) (nr := n0 + 1) (nst := none) (nk := n0 + 2)
      (nn := n0 + 3) (none := none) (by simp only [IE.WF]; omega) (by omega) (by simp only [IE.scr]; omega)
      (by rw [G5.2.1 u (by omega), hz]) (by omega) (by omega) hno (by omega) (by omega) hno
      (nodup4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) (by omega) (by omega) nd5
      (by rw [G5.1 none (by omega), hσ1]) (by simp) (by rw [G5.1 none (by omega), hσ1]) one_pos hcdd hdd
      (by simpa using hdd) hsa (by simp only [IE.top]; omega) ?_) fun σ6 ⟨m6, r6, d6, Fr6⟩ => ?_
    · intro k hk σ' hF hd hkt hkr
      have e4 : σ'.arr (a0 + 4) k = mext A' k := by
        rw [hF.2.2.1 _ _ (fun h => by omega), G5.2.2.1 _ _ (fun h => h)]
        exact mext_eq (f := σ.arr (a0 + 4)) hA' hk
      exact ⟨⟨by rw [hkt]; simpa using hcdd k hk, mext A' k, by rw [hkt, e4], abs_mext_le bA' hB k⟩,
        by simp only [IE.eval, hkt, e4]⟩
    have G6 : FrameA S N (fun b c => (b = a0 ∧ c < d * d) ∨ (b = a0 + 1 ∧ c < d)) σ σ6 :=
      (G5.mono (fun _ h => h) (fun _ h => h) (fun _ _ h => h.elim)).trans
        (Fr6.mono (fun y h => Or.inr h) (fun j h => by omega) (fun b c h => Or.inl ⟨h.1, by simpa using h.2.2⟩))
    refine XV.seq (XV.nconst hL (i := n0 + 1) (by omega) 0 (by positivity)) fun σ7 e7 => ?_
    subst e7
    have G7 := G6.setNat (show N (n0 + 1) by omega) 0
    refine XV.mono (XV.mapE (E := 10 * E + 3) (N := d) (base := 0) (st := 1) (F := vext a') hL (z := u)
      (t := u + 24) (e := .arr (a0 + 5) (n0 + 2)) (aB := a0 + 1) (nr := n0 + 1) (nst := none) (nk := n0 + 2)
      (nn := nd) (none := none) (by simp only [IE.WF]; omega) (by omega) (by simp only [IE.scr]; omega)
      (by rw [G7.2.1 u (by omega), hz]) (by omega) (by omega) hno (by omega) hnd hno
      (nodup4 (by omega) (by omega) (by omega) (by omega) (by omega) hndo) (by omega) (by omega)
      (by rw [G7.1 nd (by omega), hσd]) (by rw [G7.1 none (by omega), hσ1]) (by simp)
      (by rw [G7.1 none (by omega), hσ1]) one_pos hcd hdl (by simpa using hdl) hsa (by simp only [IE.top]; omega) ?_)
      le_rfl fun σ8 ⟨m8, r8, d8, Fr8⟩ => ?_
    · intro k hk σ' hF hd hkt hkr
      have e5 : σ'.arr (a0 + 5) k = vext a' k := by
        rw [hF.2.2.1 _ _ (fun h => by omega), G7.2.2.1 _ _ (nAr _ _ (Or.inr rfl)), vext_lt _ hk]
        exact ha' ⟨k, hk⟩
      exact ⟨⟨by rw [hkt]; simpa using hcd k hk, vext a' k, by rw [hkt, e5], abs_vext_le ba' hB k⟩,
        by simp only [IE.eval, hkt, e5]⟩
    have G8 : FrameA S N (fun b c => (b = a0 ∧ c < d * d) ∨ (b = a0 + 1 ∧ c < d)) σ σ8 :=
      G7.trans (Fr8.mono (fun y h => Or.inr h) (fun j h => by omega) (fun b c h => Or.inr ⟨h.1, by simpa using h.2.2⟩))
    refine ⟨fun h => (of_eq_false hCf h).elim, fun _ => ⟨?_, fun i k => ?_, fun k => ?_⟩, ?_, G8⟩
    · rw [Fr8.2.1 _ (by omega), Env.setNat_sc, Fr6.2.1 _ (by omega), Env.setNat_sc, fl]
    · have hc : d * i + k < d * d := by have := i.2; have := k.2; nlinarith
      rw [Fr8.2.2.1 _ _ (fun h => by omega), Env.setNat_arr]
      have := m6 _ hc
      simp only [zero_add, one_mul] at this
      rw [this, mext_cell]
    · have := m8 k k.2
      simp only [zero_add, one_mul] at this
      rw [this, vext_lt _ k.2]
    · rw [d8, Env.setNat_draws, d6, Env.setNat_draws, d4, hσ3]; simp [d1]

/-! ## The update step -/

/-- The update step `ellUpd p q j capA capa A a c` in place: the prologue, (K1), then `X`, `t`, the new state, the caps
and the copy. -/
def xupd (L : Layout) (u a0 n0 nd none : ℕ) : XCmd :=
  .seq (xupdV L u a0 n0 nd none)
  (xifS L (u + 14) (u + 15) (toX (VL.sop2 L .add (u + 13) (u + 1) u))
    (.seq (xupdT L u) (.seq (xupdA L u a0 n0 nd none) (xupdC L u a0 n0 nd none))))

/-- The output of the update step: the flag `u + 13` is `1` on `none`; on `some (A', a')` it is `0` and the arrays
`a0`, `a0 + 1` hold the new state. -/
def UpdOut (u a0 : ℕ) : Option (Matrix (Fin d) (Fin d) ℤ × (Fin d → ℤ)) → Env d → Prop
  | none, σ => σ.sc (u + 13) = 1
  | some (A', a'), σ => σ.sc (u + 13) = 0 ∧ (∀ i k : Fin d, σ.arr a0 (d * i + k) = A' i k) ∧
      ∀ k : Fin d, σ.arr (a0 + 1) k = a' k

theorem abs_add_le_pow {x y : ℤ} {a : ℕ} (hx : |x| ≤ 2 ^ a) (hy : |y| ≤ 2 ^ a) : |x + y| ≤ 2 ^ (a + 1) :=
  calc |x + y| ≤ |x| + |y| := abs_add_le _ _
    _ ≤ 2 ^ a + 2 ^ a := add_le_add hx hy
    _ = 2 ^ (a + 1) := by ring

theorem abs_sub_le_pow {x y : ℤ} {a : ℕ} (hx : |x| ≤ 2 ^ a) (hy : |y| ≤ 2 ^ a) : |x - y| ≤ 2 ^ (a + 1) := by
  rw [sub_eq_add_neg]; exact abs_add_le_pow hx (by rwa [abs_neg])

theorem abs_rndI_le {x y : ℤ} {a : ℕ} (hx : |x| ≤ 2 ^ a) (hy : |y| ≤ 2 ^ (a + 1)) :
    |RQ.rndI x y| ≤ 2 ^ (a + 2) := by
  unfold RQ.rndI
  refine (absI_ediv_le _ _).trans ?_
  have h2 : |2 * x| ≤ 2 ^ (a + 1) := by rw [abs_mul, pow_succ, abs_two]; linarith
  exact abs_add_le_pow h2 hy

theorem abs_updM_le {E : ℕ} {s : ℤ} {A : Matrix (Fin d) (Fin d) ℤ} {v : Fin d → ℤ} (hE1 : 1 ≤ E)
    (bs : |s| ≤ 2 ^ (7 * E)) (bA : ∀ i k, |A i k| ≤ 2 ^ E) (bv : ∀ k, |v k| ≤ 2 ^ (3 * E))
    (bd1 : |(d : ℤ) + 1| ≤ 2 ^ E) (bkN : |kapN d| ≤ 2 ^ E) (bkD : |kapD d| ≤ 2 ^ E) (i k : Fin d) :
    |updM s A v i k| ≤ 2 ^ (10 * E + 3) := by
  unfold updM
  have h2 : |(2 : ℤ)| ≤ 2 ^ 1 := by norm_num
  have b1 : |((d : ℤ) + 1) * s * A i k| ≤ 2 ^ (9 * E) :=
    abs_le_pow_mono (abs_mul_le_pow (abs_mul_le_pow bd1 bs) (bA i k)) (by omega)
  have b2 : |2 * v i * v k| ≤ 2 ^ (9 * E) :=
    abs_le_pow_mono (abs_mul_le_pow (abs_mul_le_pow h2 (bv i)) (bv k)) (by omega)
  have b3 : |kapN d * (((d : ℤ) + 1) * s * A i k - 2 * v i * v k)| ≤ 2 ^ (10 * E + 1) :=
    abs_le_pow_mono (abs_mul_le_pow bkN (abs_sub_le_pow b1 b2)) (by omega)
  have b4 : |kapD d * ((d : ℤ) + 1) * s| ≤ 2 ^ (10 * E + 1 + 1) :=
    abs_le_pow_mono (abs_mul_le_pow (abs_mul_le_pow bkD bd1) bs) (by omega)
  exact (abs_rndI_le b3 b4).trans (pow_le_pow_right₀ (by norm_num) (by omega))

theorem abs_upda_le {E q : ℕ} {t : ℤ} {a v : Fin d → ℤ} (hq : q ≤ E) (ba : ∀ k, |a k| ≤ 2 ^ E)
    (bv : ∀ k, |v k| ≤ 2 ^ (3 * E)) (bt : |t| ≤ 2 ^ (4 * E)) (bd1 : |(d : ℤ) + 1| ≤ 2 ^ E) (k : Fin d) :
    |upda q t a v k| ≤ 2 ^ (5 * E + 3) := by
  unfold upda
  have bQ : |(2 : ℤ) ^ q| ≤ 2 ^ E := by
    rw [abs_of_pos (by positivity)]; exact pow_le_pow_right₀ (by norm_num) hq
  have b1 : |v k * 2 ^ q| ≤ 2 ^ (5 * E) := abs_le_pow_mono (abs_mul_le_pow (bv k) bQ) (by omega)
  have b2 : |((d : ℤ) + 1) * t| ≤ 2 ^ (5 * E + 1) := abs_le_pow_mono (abs_mul_le_pow bd1 bt) (by omega)
  exact (abs_sub_le_pow (a := 5 * E + 2) (abs_le_pow_mono (ba k) (by omega)) (abs_rndI_le b1 b2)).trans
    (pow_le_pow_right₀ (by norm_num) (by omega))

theorem upd_units_le {E : ℕ} (hdE : d ≤ E) : (10 * d * d + 29 * d + 19) + ((100 * E + 40 +
    ((50 * d * d + 40 * d + 20) + (25 * d * d + 25 * d + 20))) + 2) ≤ 200 * (E + 1) ^ 2 := by
  have := Nat.mul_le_mul hdE hdE
  nlinarith

theorem dot_self_nonneg (c : Fin d → ℤ) : 0 ≤ c ⬝ᵥ c :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (c i)

set_option maxHeartbeats 8000000 in
/-- **The rule of the update step.** Inputs below `2^E`, `d ≤ E`, `p ≤ E`, `2q ≤ E`, caps in `[0, 2^E]`,
`64 E + 16 < ℓ`. -/
theorem XV.upd {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {u a0 n0 nd none E p q j : ℕ}
    {A : Matrix (Fin d) (Fin d) ℤ} {a c : Fin d → ℤ} {capA capa : ℤ}
    (hS : u + 60 ≤ L.NS) (hA0 : a0 + 6 ≤ L.NA) (hN0 : n0 + 4 ≤ L.NN) (hnd : nd < L.NN) (hno : none < L.NN)
    (hnd0 : nd < n0 ∨ n0 + 4 ≤ nd) (hno0 : none < n0 ∨ n0 + 4 ≤ none) (hndo : nd ≠ none)
    (hz : σ.sc u = 0) (h1 : σ.sc (u + 1) = 1) (h2 : σ.sc (u + 2) = 2) (h4 : σ.sc (u + 3) = 4)
    (hK1 : σ.sc (u + 4) = (((2 : ℤ) ^ (p - 2 * j) : ℤ) : ℝ)) (hQ2 : σ.sc (u + 5) = (2 : ℤ) ^ (2 * q))
    (hP : σ.sc (u + 6) = (2 : ℤ) ^ p) (hQ : σ.sc (u + 7) = (2 : ℤ) ^ q) (hd1 : σ.sc (u + 8) = (d : ℤ) + 1)
    (hkN : σ.sc (u + 9) = kapN d) (hkD : σ.sc (u + 10) = kapD d) (hcA : σ.sc (u + 11) = capA)
    (hca : σ.sc (u + 12) = capa) (hσd : σ.nat nd = d) (hσ1 : σ.nat none = 1)
    (hA : ∀ i k : Fin d, σ.arr a0 (d * i + k) = A i k) (ha : ∀ k : Fin d, σ.arr (a0 + 1) k = a k)
    (hc : ∀ k : Fin d, σ.arr (a0 + 2) k = c k)
    (bA : ∀ i k, |A i k| ≤ 2 ^ E) (ba : ∀ k, |a k| ≤ 2 ^ E) (bc : ∀ k, |c k| ≤ 2 ^ E)
    (hdE : d ≤ E) (hE1 : 1 ≤ E) (hp : p ≤ E) (hq : 2 * q ≤ E) (bkN : |kapN d| ≤ 2 ^ E) (bkD : |kapD d| ≤ 2 ^ E)
    (hcA0 : 0 ≤ capA) (hca0 : 0 ≤ capa) (bcA : capA ≤ 2 ^ E) (bca : capa ≤ 2 ^ E) (hℓ : 64 * E + 16 < ℓ) :
    XRunsB L X ℓa ℓ (xupd L u a0 n0 nd none) σ (200 * (E + 1) ^ 2) (fun σ' =>
      UpdOut u a0 (ellUpd p q j capA capa A a c) σ' ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => u + 13 ≤ y) (fun j => n0 ≤ j ∧ j < n0 + 4)
        (fun b k => a0 ≤ b ∧ b < a0 + 6 ∧ b ≠ a0 + 2 ∧ k < d * d) σ σ') := by
  have bd1 : (d : ℤ) + 1 ≤ 2 ^ E := by
    have : d + 1 ≤ 2 ^ E := by have := Nat.lt_two_pow_self (n := E); omega
    exact_mod_cast this
  have bd1' : |(d : ℤ) + 1| ≤ 2 ^ E := by rw [abs_of_pos (by positivity)]; exact bd1
  have bK1 : |(2 : ℤ) ^ (p - 2 * j)| ≤ 2 ^ E := by
    rw [abs_of_pos (by positivity)]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have bv : ∀ k, |(A *ᵥ c) k| ≤ 2 ^ (3 * E) := fun k =>
    abs_le_pow_mono (abs_mulVec_le' hdE bA bc k) (by omega)
  have bs : |c ⬝ᵥ (A *ᵥ c)| ≤ 2 ^ (7 * E) :=
    abs_le_pow_mono (abs_dot_le' hdE (fun k => abs_le_pow_mono (bc k) (by omega : E ≤ 3 * E)) bv) (by omega)
  have bcc : |(2 : ℤ) ^ (p - 2 * j) * (c ⬝ᵥ c)| ≤ 2 ^ (5 * E) :=
    abs_le_pow_mono (abs_mul_le_pow bK1 (abs_dot_le' hdE bc bc)) (by omega)
  have hdd := Nat.mul_le_mul hdE hdE
  have hlt : ∀ k : ℕ, k ≤ 7 * E → (2 : ℤ) ^ k < 2 ^ ℓ := fun k hk =>
    pow_lt_pow_right₀ (by norm_num) (by omega)
  have cdd : ∀ k, k < d → k < d * d := fun k hk => lt_of_lt_of_le hk (Nat.le_mul_self d)
  refine XV.mono (K := (10 * d * d + 29 * d + 19) + ((100 * E + 40 + ((50 * d * d + 40 * d + 20) +
    (25 * d * d + 25 * d + 20))) + 2))
    (XV.seq (XV.updV (E := E) (K1 := 2 ^ (p - 2 * j)) (kN := kapN d) (A := A) (c := c) hL hS hA0 hN0 hnd hno hnd0
      hno0 hndo hz hσd hσ1 hK1 hkN hA hc bA bc bK1 bkN hdE hℓ) fun σ1 ⟨f13, f21, v1, s1, k1, d1, F1⟩ => ?_)
    (upd_units_le hdE) fun _ h => h
  have e1 : ∀ y, y < u + 13 → σ1.sc y = σ.sc y := fun y hy => F1.2.1 y (by omega)
  have bs' : |(σ1.sc (u + 14))| < 2 ^ ℓ := by
    rw [s1]; exact XV.abs_int_lt (lt_of_le_of_lt bs (hlt _ le_rfl))
  have bk' : |(σ1.sc (u + 15))| < 2 ^ ℓ := by
    rw [k1, ← Int.cast_mul]; exact XV.abs_int_lt (lt_of_le_of_lt bcc (hlt _ (by omega)))
  by_cases hK : c ⬝ᵥ (A *ᵥ c) < 2 ^ (p - 2 * j) * (c ⬝ᵥ c)
  · -- (K1)
    have h0 : |(0 : ℝ)| < 2 ^ ℓ := by rw [abs_zero]; positivity
    have h1' : |(1 : ℝ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
    refine XV.mono (XV.ifS_t hL (by omega) (by omega) bs' bk'
      (by rw [s1, k1, ← Int.cast_mul]; exact_mod_cast hK)
      (XV.sop2 hL (x := u + 13) (a := u + 1) (b := u) (by omega) (by omega) (by omega) .add (by intro h; cases h)
        (by rw [e1 _ (by omega), h1]; exact h1') (by rw [e1 _ (by omega), hz]; exact h0)
        (by simp only [RealRAM.Op2.eval, e1 _ (show u + 1 < u + 13 by omega), e1 u (by omega), h1, hz, add_zero];
            exact h1'))) (Nat.le_add_left _ _) fun σ' e => ?_
    subst e
    rw [ellUpd_eq, if_pos hK]
    refine ⟨by simp [UpdOut, RealRAM.Op2.eval, e1 _ (show u + 1 < u + 13 by omega), e1 u (by omega), h1, hz],
      by simp [d1],
      ((F1.mono (fun _ h => h) (fun _ h => h) (fun b k h => ⟨by omega, by omega, by omega, cdd k h.2⟩)).setSc
        (by omega) _)⟩
  · have hs0 : 0 ≤ c ⬝ᵥ (A *ᵥ c) :=
      le_trans (mul_nonneg (by positivity) (dot_self_nonneg c)) (not_lt.1 hK)
    refine XV.ifS_f hL (by omega) (by omega) bs' bk' (by rw [s1, k1, ← Int.cast_mul]; exact_mod_cast hK) ?_
    -- `X`, `t`
    refine XV.seq (XV.updT (E := E) (s := c ⬝ᵥ (A *ᵥ c)) (dp1 := (d : ℤ) + 1) (p := p) (q := q) hL hS
      (by rw [e1 _ (by omega), hz]) (by rw [e1 _ (by omega), h1]) (by rw [e1 _ (by omega), h2])
      (by rw [e1 _ (by omega), h4]) s1 (by rw [e1 _ (by omega), hQ2]) (by rw [e1 _ (by omega), hP])
      (by rw [e1 _ (by omega), hd1]; norm_cast) hs0 bs hq hp bd1' hℓ) fun σ2 ⟨t17, t18, t19, d2, F2⟩ => ?_
    have e2 : ∀ y, y < u + 16 → σ2.sc y = σ1.sc y := fun y hy => F2.2.1 y (by omega)
    have bt := updT_le (p := p) bs hq
    -- the new state
    refine XV.seq (XV.updA (E := E) (q := q) (A := A) (a := a) (v := A *ᵥ c) (s := c ⬝ᵥ (A *ᵥ c))
      (t := Transfer.updT p q (c ⬝ᵥ (A *ᵥ c))) hL hS hA0 hN0 hnd hno hnd0 hno0 hndo
      (by rw [e2 _ (by omega), e1 _ (by omega), hz]) (by rw [F2.1 nd id, F1.1 nd (by omega), hσd])
      (by rw [F2.1 none id, F1.1 none (by omega), hσ1]) (by rw [e2 _ (by omega), e1 _ (by omega), hQ])
      (by rw [e2 _ (by omega), e1 _ (by omega), hd1]) (by rw [e2 _ (by omega), e1 _ (by omega), hkD])
      (by rw [e2 _ (by omega), s1]) (by rw [t18]; norm_cast) (by rw [t19]; norm_cast)
      (by rw [F2.2.1 _ (by omega), f21])
      (fun i k => by rw [F2.2.2.1 _ _ id, F1.2.2.1 _ _ (fun h => absurd h.1 (by omega)), hA])
      (fun k => by rw [F2.2.2.1 _ _ id, F1.2.2.1 _ _ (fun h => absurd h.1 (by omega)), ha])
      (fun k => by rw [F2.2.2.1 _ _ id, v1]) bA ba bv bs bt (by omega) bd1 bkN bkD hE1 hℓ)
      fun σ3 ⟨a5, A4, d3, F3⟩ => ?_
    -- the caps and the copy
    refine XV.mono (XV.updC (E := E) (A' := updM (c ⬝ᵥ (A *ᵥ c)) A (A *ᵥ c))
      (a' := upda q (Transfer.updT p q (c ⬝ᵥ (A *ᵥ c))) a (A *ᵥ c)) hL hS hA0 hN0 hnd hno hnd0 hno0 hndo
      (by rw [F3.2.1 _ (by omega), e2 _ (by omega), e1 _ (by omega), hz])
      (by rw [F3.2.1 _ (by omega), e2 _ (by omega), e1 _ (by omega), h1])
      (by rw [F3.2.1 _ (by omega), e2 _ (by omega), f13])
      (by rw [F3.2.1 _ (by omega), e2 _ (by omega), e1 _ (by omega), hcA])
      (by rw [F3.2.1 _ (by omega), e2 _ (by omega), e1 _ (by omega), hca])
      (by rw [F3.1 nd (by omega), F2.1 nd id, F1.1 nd (by omega), hσd])
      (by rw [F3.1 none (by omega), F2.1 none id, F1.1 none (by omega), hσ1]) A4 a5
      (abs_updM_le hE1 bs bA bv bd1' bkN bkD)
      (fun k => abs_le_pow_mono (abs_upda_le (by omega) ba bv bt bd1' k) (by omega))
      hcA0 hca0 bcA bca hℓ) le_rfl fun σ4 ⟨c1, c0, d4, F4⟩ => ?_
    rw [ellUpd_eq, if_neg hK]
    refine ⟨?_, by rw [d4, d3, d2, d1], ?_⟩
    · split_ifs with hC
      · exact c1 hC
      · exact c0 hC
    · exact ((F1.mono (fun _ h => h) (fun _ h => h) (fun b k h => ⟨by omega, by omega, by omega, cdd k h.2⟩)).trans
        (F2.mono (fun y h => by omega) (fun _ h => h.elim) (fun _ _ h => h.elim))).trans
        ((F3.mono (fun y h => by omega) (fun _ h => h) (fun b k h => by
          rcases h with ⟨h, h'⟩ | ⟨h, h'⟩
          · exact ⟨by omega, by omega, by omega, cdd k h'⟩
          · exact ⟨by omega, by omega, by omega, h'⟩)).trans
        (F4.mono (fun y h => by omega) (fun _ h => h) (fun b k h => by
          rcases h with ⟨h, h'⟩ | ⟨h, h'⟩
          · exact ⟨by omega, by omega, by omega, h'⟩
          · exact ⟨by omega, by omega, by omega, cdd k h'⟩)))

end AdversarialBco.Bit.Transfer
