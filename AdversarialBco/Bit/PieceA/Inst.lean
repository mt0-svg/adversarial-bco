/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.PieceA.Regime
public import AdversarialBco.Bit.PieceA.Reg

@[expose] public section

/-!
# Piece A: BL's constants as a `Reg`

`reg d n` reads the base constants of `Bud` at `(d, n)`; every derived constant of `Bud` is the one of `Reg` at
`reg d n` by definition, and `reg_ok` proves `Reg.OK (reg d n)` in `RunCase` from the regime facts of
Bit/PieceA/Regime.lean and the links of Bit/PieceA/Defs.lean.
-/

namespace AdversarialBco.Bit.PieceA

open AdversarialBco.Bit.BLP (po par)

open AdversarialBco.Bit.Asm (RunCase deltaBL)

/-- BL's base constants at `(d, n)`. -/
noncomputable def reg (d n : ℕ) : Reg where
  d := d
  n := n
  Ne := BLP.Bud.Ne d n
  de := BLP.Bud.de d n
  Le := BLP.Bud.Le d n
  lam := BLP.Bud.lam d n
  eta := BLP.Bud.eta d n
  eps := BLP.Bud.eps d n
  rho := BLP.Bud.rho d n
  R := BLP.Bud.R d n
  kc := BLP.Bud.kc d n
  tp := BLP.Bud.tp d n
  eh := BLP.Bud.eh d n
  t2 := 2 ^ ((par d n).B / 2)
  Q := BLP.Bud.Ne d n ^ ((1 : ℝ) / 40)

example (d n : ℕ) : BLP.Bud.sel d n = (reg d n).sel := rfl
example (d n : ℕ) : BLP.Bud.val d n = (reg d n).val := rfl
example (d n : ℕ) : BLP.Bud.kap0 d n = (reg d n).kap0 := rfl
example (d n : ℕ) : BLP.Bud.hTr d n 3 = (reg d n).hTr 3 := rfl
example (d n : ℕ) : BLP.Bud.Dw d n = (reg d n).Dw := rfl

/-- `2^{B/2} 2^{-p} = 4 · 2^{size(n(d + 2))} > 4 n (d + 2)`. -/
theorem t2_tp (d n : ℕ) : 4 * (n : ℝ) * ((d : ℝ) + 2) ≤ (2 : ℝ) ^ ((par d n).B / 2) * BLP.Bud.tp d n := by
  have hB : (par d n).B / 2 = pB d n + (n * (d + 2)).size + 2 := by
    show 2 * (pB d n + (n * (d + 2)).size + 2) / 2 = _
    omega
  have hlt := Nat.lt_size_self (n * (d + 2))
  have hlt' : ((n * (d + 2) : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ (n * (d + 2)).size := by
    exact_mod_cast hlt
  rw [hB, bud_tp, u, pow_add, pow_add]
  push_cast at hlt'
  have h2p : (0 : ℝ) < 2 ^ pB d n := by positivity
  field_simp
  nlinarith

/-- `Reg.OK` at BL's constants in `RunCase`. -/
theorem reg_ok (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (h : RunCase d n) : (reg d n).OK := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he4 := eps_le_of_runCase d n hd hn h
  have he2 : eps d n ≤ 1 / 2 := by linarith
  have hNe : BLP.Bud.Ne d n = Ne d n := rfl
  have hN0 : (0 : ℝ) ≤ Ne d n := by unfold Ne; positivity
  refine
    { hd := hd'
      hn := hn'
      hNe := ?_
      hde := ?_
      hLe := ?_
      hlam := ?_
      heta := ?_
      heps := ?_
      hrho := ?_
      hkc := ?_
      heps4 := ?_
      hN700 := ?_
      hL1 := ?_
      hd15 := ?_
      hn4 := ?_
      hnge := ?_
      hL40 := ?_
      hQ0 := ?_
      hQ := ?_
      htp0 := ?_
      htp := ?_
      heh1 := ?_
      heh2 := ?_
      hR1 := ?_
      hR2 := ?_
      ht20 := ?_
      ht2 := ?_ }
  · show BLP.Bud.Ne d n = 15 * 2 ^ 17 * (d : ℝ) ^ 3 * (n : ℝ) ^ 4
    rw [hNe, Ne, NeN]; push_cast; ring
  · show BLP.Bud.de d n = 1 / BLP.Bud.Ne d n
    exact po_de d n hd hn
  · show BLP.Bud.Le d n = 36 * Real.log (BLP.Bud.Ne d n)
    rw [bud_Le d n hd hn]; rfl
  · show BLP.Bud.lam d n = 1 / (725 * (d : ℝ) * BLP.Bud.Le d n ^ 2)
    rw [bud_lam d n hd hn, bud_Le d n hd hn]; rfl
  · show BLP.Bud.eta d n = Real.sqrt d / (BLP.Bud.Le d n * Real.sqrt n)
    rw [bud_eta d n hd hn, bud_Le d n hd hn]; rfl
  · show BLP.Bud.eps d n = 14500 * (d : ℝ) * Real.sqrt d * BLP.Bud.Le d n ^ 5 / Real.sqrt n
    rw [bud_eps d n hd hn, bud_Le d n hd hn]; rfl
  · show BLP.Bud.rho d n = 1450 * (d : ℝ) ^ 2 * BLP.Bud.Le d n ^ 3
    rw [bud_rho d n hd hn, bud_Le d n hd hn]; rfl
  · show BLP.Bud.kc d n = BLP.Bud.eta d n * BLP.Bud.lam d n / (4 * (1 - BLP.Bud.lam d n) ^ 2)
    rw [bud_kc d n hd hn, bud_eta d n hd hn, bud_lam d n hd hn]; rfl
  · show BLP.Bud.eps d n ≤ 1 / 4
    rw [bud_eps d n hd hn]; exact he4
  · exact regime_N hd hn he2
  · show 17467 ≤ BLP.Bud.Le d n
    rw [bud_Le d n hd hn]; exact regime_Le hd hn (regime_N hd hn he2)
  · exact regime_d15 hd hn he2
  · exact regime_n4 hd
  · show 29000 ^ 2 * (d : ℝ) ^ 3 * BLP.Bud.Le d n ^ 10 ≤ (n : ℝ)
    rw [bud_Le d n hd hn]; exact regime_n_ge hd hn he2
  · show (10 * BLP.Bud.Le d n) ^ 40 ≤ _
    rw [bud_Le d n hd hn]; exact regime_Le40 hd hn (regime_N hd hn he2)
  · show (0 : ℝ) < BLP.Bud.Ne d n ^ ((1 : ℝ) / 40)
    have : (0 : ℝ) < Ne d n := lt_trans (by positivity) (regime_N hd hn he2)
    exact Real.rpow_pos_of_pos this _
  · show (BLP.Bud.Ne d n ^ ((1 : ℝ) / 40)) ^ 40 = BLP.Bud.Ne d n
    have hN0' : (0 : ℝ) ≤ BLP.Bud.Ne d n := hN0
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0']; norm_num
  · show (0 : ℝ) < BLP.Bud.tp d n
    rw [bud_tp]; unfold u; positivity
  · exact regime_u hd hn
  · have := (regime_eh hd hn).1
    rw [← bud_eh, ← bud_tp] at this; exact this
  · have := (regime_eh hd hn).2
    rw [← bud_eh, ← bud_tp] at this; exact this
  · exact ref_R_lower hd
  · exact ref_R_upper hd
  · show (0 : ℝ) < 2 ^ ((par d n).B / 2)
    positivity
  · exact t2_tp d n

end AdversarialBco.Bit.PieceA
