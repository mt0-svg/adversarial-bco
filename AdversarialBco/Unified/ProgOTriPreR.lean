/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOTriPreV
public import AdversarialBco.Unified.ProgOSetupP0

@[expose] public section

/-!
# BL-O's setup: the run of the constants line of TRI-OGD-O

`poG`: the parameter of the bounds of `poSt` (the exponents of the powers of two, `k`, `d`, `size n`, `triSQ d` and the
bit lengths of `r₀`, `R₀`); `poSt_sem`: the side conditions of the steps; `poIn_bound`: the bounds of the inputs;
`poC`: the cells of the line (values from `120`, scratch from `250`).
-/

namespace AdversarialBco.Unified.ProgO.TriO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM
  AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Unified.BLO AdversarialBco.Unified.ProgO
open AdversarialBco.BitRAM (len)

/-- The parameter of the bounds of the line. -/
def poG (d n k : ℕ) (r0 R0 : ℚ) : ℕ :=
  triLa (triSQ d) + triLh (triSQ d) + triJaQ d + triBvQ d + 2 * tzP d + tGcT d (ellPosO d n k r0 R0) + stE d +
    triETauQ d + stJ d + stEu d + triSQ d + stK d r0 R0 + k + d + n.size + len r0.num + len (r0.den : ℤ) +
    len R0.num + len (R0.den : ℤ) + 4

set_option maxHeartbeats 8000000 in
theorem poSt_sem {d n k : ℕ} {r0 R0 : ℚ} (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) :
    ∀ j < poSt.length, (poSt.getD j (.cst 0)).Sem (poV d n k r0 R0) (poG d n k r0 R0) := by
  intro j hj
  rw [poSt_length] at hj
  have p : ∀ x : ℕ, x ≤ poG d n k r0 R0 → (0 : ℤ) ≤ x ∧ (x : ℤ) ≤ ((poG d n k r0 R0 : ℕ) : ℤ) :=
    fun x h => ⟨Nat.cast_nonneg x, by exact_mod_cast h⟩
  interval_cases j <;> simp only [poSt, List.getD_cons_succ, List.getD_cons_zero, SStep.Sem, poV_22, poV_23,
    poV_25, poV_30, poV_31, poV_34, poV_40 d n k r0 R0 hd, poV_42 d n k r0 R0 hd, poV_46 d n k r0 R0 hd,
    poV_48 d n k r0 R0 hd, poV_50 d n k r0 R0 hd, poV_52 d n k r0 R0 hd, poV_58 d n k r0 R0 hr, poV_60,
    poV_62 d n k r0 R0 hr, poV_66 d n k r0 R0 hd hr, poV_68 d n k r0 R0 hd hr, poV_74 d n k r0 R0 hd hr,
    poV_77 d n k r0 R0 hd hr, poV_78 d n k r0 R0 hd hr, poV_81 d n k r0 R0 hd hr, poV_84 d n k r0 R0 hd hr,
    poV_86 d n k r0 R0 hd hr, poV_92, poV_96 d n k r0 R0 hd, poV_99 d n k r0 R0 hd, poV_100 d n k r0 R0 hd,
    poV_101 d n k r0 R0 hd, poV_103 d n k r0 R0 hd, poV_104 d n k r0 R0 hd, poV_106 d n k r0 R0 hd,
    poV_108 d n k r0 R0 hd, poV_110 d n k r0 R0 hd, poV_115 d n k r0 R0 hd hr, poV_117 d n k r0 R0 hd,
    poV_21, poV_122 d n k r0 R0 hr, poV_124 d n k r0 R0 hd hr] <;>
    first | exact Nat.cast_nonneg _ | exact p _ (by simp only [poG, tGcT, tGT, tKZ, stJ]; omega)

theorem poG_in {d n k : ℕ} {r0 R0 : ℚ} {z : ℤ} (h : len z ≤ poG d n k r0 R0) :
    |z| ≤ 2 ^ ev (poG d n k r0 R0) (poInP 0) := by
  simp only [poInP, ev, one_mul, add_zero]
  exact (abs_lt_len z).le.trans (pow_le_pow_right₀ (by norm_num) (by exact_mod_cast h))

theorem poG_nat {d n k : ℕ} {r0 R0 : ℚ} {x : ℕ} (h : x ≤ poG d n k r0 R0) :
    |(x : ℤ)| ≤ 2 ^ ev (poG d n k r0 R0) (poInP 0) := by
  rw [abs_of_nonneg (Nat.cast_nonneg x)]
  simp only [poInP, ev, one_mul, add_zero]
  exact_mod_cast h.trans Nat.lt_two_pow_self.le

theorem poIn_bound {d n k : ℕ} {r0 R0 : ℚ} :
    ∀ y ∈ poIns, |poIn d n k r0 R0 y| ≤ 2 ^ ev (poG d n k r0 R0) (poInP y) := by
  intro y hy
  simp only [poIns, List.mem_cons, List.mem_nil_iff, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [poIn, Nat.reduceEqDiff, ↓reduceIte]
  · exact poG_nat (by unfold poG; omega)
  · exact poG_in (by unfold poG; omega)
  · exact poG_in (by unfold poG; omega)
  · exact poG_nat (by unfold poG; omega)
  · rw [abs_of_nonneg (Nat.cast_nonneg n)]
    simp only [poInP, ev, one_mul, add_zero]
    have h1 : n < 2 ^ n.size := Nat.lt_size_self n
    have h2 : 2 ^ n.size ≤ 2 ^ poG d n k r0 R0 := Nat.pow_le_pow_right (by norm_num) (by unfold poG; omega)
    exact_mod_cast (h1.trans_le h2).le
  · exact poG_nat (by unfold poG; omega)
  · exact poG_in (by unfold poG; omega)
  · exact poG_in (by unfold poG; omega)

/-- The cells of the line: the values from `120`, the scratch from `250` (`40` slots), `0, 1, 2, 4` in the slots
`1, 2, 116, 117`, the scratch registers `29`, `30`, `1` in the register `0`. -/
def poC : SLC := ⟨120, 250, 1, 2, 116, 117, 29, 30, 0⟩

theorem poC_ok {L : Layout} {o r : ℕ} (hS : o + 290 ≤ L.NS) (hN : r + 31 ≤ L.NN) : (SLC.atB o r poC).OK L 40 := by
  constructor <;> simp only [SLC.atB, poC, List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] <;> omega

end AdversarialBco.Unified.ProgO.TriO
