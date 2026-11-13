/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriRule

@[expose] public section

/-!
# The work term of TRI-M and `TriRule`

* `triWs`: every quantity `XV.tri` bounds, as a polynomial in the parameters of TRI-M (`triK_eq`);
* `tri_work`: these quantities below `triC * W ^ (210 * 4)`, `W = d + m + size n + size M̂ + s + 1`;
* `triRule`: **`TriRule`**, with `xtri`, 245 slots, 31 registers and 16 arrays.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM
  AdversarialBco.Bit.Transfer.BLM

/-- The units of one draw of the core (`coreBK`), with `U` for the units of one product. -/
def coreBKs (d M U : ℕ) : ℕ :=
  1 + (d * (5 + 6) + 3) + (1 + (d * d * (5 + 6) + 3) + (d * (U + 2 + 3) + 3 + step1K d M))

/-- The units of the core (`coreK`), with `U` for the units of one product. -/
def coreKs (d M N U : ℕ) : ℕ :=
  1 + (d * (1 + 6) + 3) + (1 + (d * d * (1 + 6) + 3) + (1 + (d * (1 + 6) + 3)) + (1 + (d * (1 + 6) + 3) +
    (1 + (d * d * (1 + 6) + 3) + (N * (coreBKs d M U + 3) + 3))))

/-- The units of TRI-M (`triK`), with `G` for `tcG d n` and `U` for the units of one product. -/
def triKs (d M N U mst G : ℕ) : ℕ :=
  15 + (ev G (4, 44) + (7 * (d + 10) * (1 + ev G (4, 44) + 2) + 2) + (ev G (636, 3897) + (11 + (1 + (1 + 1))))) +
    (initK d + (mst * (coreKs d M N U + stageCK d + 3) + 3))

theorem triK_eq (d n m : ℕ) : triK d n m = triKs d (m + (d + d)) (2 ^ triNeQ d (ellPos d n))
    (bmUnits (triBgQ d)) (triMstQ (1 / 2) n) (tcG d n) := rfl

/-- Every quantity `XV.tri` bounds: the units, the exponent of the magnitudes, the registers. -/
def triWs (d m s z mst N U G Gc La Bv P Ja Gt Ne : ℕ) : ℕ :=
  triKs d (m + (d + d)) N U mst G +
    (48 * (s + z * (d + 2) + mst * (Gc + La + d) + mst * Gc + mst + Bv + 2 * P + Ja + La + Gt + Ne + 4 * P + d +
      20) + 42 * d + 32) +
    (d * d + m + (d + d) + 2) + N + ev G tcT + (4 + 2 * ((d + 1) * (m + 1))) + (4 * P + 2) +
    (s + 1 + mst * (Gc + La + d))

theorem triWs_mono {d m s z mst N U G Gc La Bv P Ja Gt Ne V : ℕ} (hd : d ≤ V) (hm : m ≤ V) (hs : s ≤ V)
    (hz : z ≤ V) (hmst : mst ≤ V) (hN : N ≤ V) (hU : U ≤ V) (hG : G ≤ V) (hGc : Gc ≤ V) (hLa : La ≤ V)
    (hBv : Bv ≤ V) (hP : P ≤ V) (hJa : Ja ≤ V) (hGt : Gt ≤ V) (hNe : Ne ≤ V) :
    triWs d m s z mst N U G Gc La Bv P Ja Gt Ne ≤ triWs V V V V V V V V V V V V V V V := by
  unfold triWs triKs coreKs coreBKs ev tcT step1K scanBK stageCK matmulK mmRowK initK
  gcongr

theorem triWs_poly {V : ℕ} (hV : 1 ≤ V) : triWs V V V V V V V V V V V V V V V ≤ 10 ^ 6 * V ^ 4 := by
  have h1 : V ≤ V ^ 4 := Nat.le_self_pow (by norm_num) V
  have h2 : V ^ 2 ≤ V ^ 4 := Nat.pow_le_pow_right hV (by norm_num)
  have h3 : V ^ 3 ≤ V ^ 4 := Nat.pow_le_pow_right hV (by norm_num)
  have h0 : 1 ≤ V ^ 4 := Nat.one_le_pow _ _ (by omega)
  unfold triWs triKs coreKs coreBKs ev tcT step1K scanBK stageCK matmulK mmRowK initK
  dsimp only
  ring_nf
  linarith

/-- The constant of the work term of TRI-M. -/
def triC : ℕ := 10 ^ 6 * 2 ^ (1100 * 4) + 1

theorem tri_two_pow_ge {c j J : ℕ} (hc : c ≤ 2 ^ j) (hj : j ≤ J) : c ≤ 2 ^ J :=
  hc.trans (Nat.pow_le_pow_right (by norm_num) hj)

/-- The quantities of `XV.tri` below `triC * W ^ (210 * 4)`, `W = d + m + size n + z + s + 1`. -/
theorem tri_work {d n m s z W : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (hW : d + m + n.size + z + s + 1 = W) :
    triWs d m s z (triMstQ (1 / 2) n) (2 ^ triNeQ d (ellPos d n)) (bmUnits (triBgQ d)) (tcG d n)
      (tzGc d (ellPos d n)) (triLa (triSQ d)) (triBvQ d) (gsm_prec (triBgQ d)) (triJaQ d) (tzG d (ellPos d n))
      (triNeQ d (ellPos d n)) < triC * W ^ (210 * 4) := by
  have hW1 : 1 ≤ W := by omega
  have hV : ∀ {a c e : ℕ}, a ≤ c * W ^ e → c ≤ 2 ^ 1100 → e ≤ 210 → a ≤ 2 ^ 1100 * W ^ 210 :=
    fun h hc he => h.trans (Nat.mul_le_mul hc (Nat.pow_le_pow_right hW1 he))
  have hL : ∀ {a : ℕ}, a ≤ 5000 * W → a ≤ 2 ^ 1100 * W ^ 210 :=
    fun h => hV (e := 1) (by rw [pow_one]; exact h) (tri_two_pow_ge (j := 13) (by norm_num) (by norm_num))
      (by norm_num)
  have hds : d.size ≤ d := Nat.size_le.2 Nat.lt_two_pow_self
  have hp := ellPos_le n hd hn
  have hmst := mst_le n hn
  have hLa := triLa_le_lin hd
  have hBv := triBvQ_le_lin hd
  have hJa := triJaQ_le_lin hd
  have hLh := triLh_le_lin hd
  have hSQ := (triSQ_bounds d).2
  have hNe := triNeQ_le_lin hd (ellPos d n)
  have hJs := triJsQ_le_lin hd (ellPos d n)
  have hGc := tzGc_le_lin hd (ellPos d n)
  have hGt : tzG d (ellPos d n) = triBvQ d + triJsQ d (ellPos d n) + triJaQ d := rfl
  have hdW : d ≤ W := by omega
  have hW21 : W ≤ W ^ 21 := Nat.le_self_pow (by norm_num) _
  have hP : gsm_prec (triBgQ d) ≤ 2 ^ 158 * W ^ 21 :=
    (tzP_le hd).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hdW 21))
  have hBg1 : 1 ≤ triBgQ d := by
    have : 2 ≤ triKgQ d := le_max_left _ _
    unfold triBgQ; omega
  have hU : bmUnits (triBgQ d) ≤ (24 * 2 ^ (158 * 2)) * W ^ (21 * 2) := by
    refine (bmUnits_le hBg1).trans ?_
    calc 24 * gsm_prec (triBgQ d) ^ 2 ≤ 24 * (2 ^ 158 * W ^ 21) ^ 2 := by gcongr
      _ = (24 * 2 ^ (158 * 2)) * W ^ (21 * 2) := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_assoc]
  have hN : 2 ^ triNeQ d (ellPos d n) ≤ (2 ^ 1000 * 30) * W ^ 201 := by
    refine (pow_triNeQ_le hd _).trans ?_
    calc 2 ^ 1000 * d ^ 200 * (ellPos d n + 1) ≤ 2 ^ 1000 * W ^ 200 * (30 * W) := by gcongr; omega
      _ = (2 ^ 1000 * 30) * W ^ 201 := by generalize (2 : ℕ) ^ 1000 = c; ring
  have hG : tcG d n ≤ (5019 + 2 ^ 159) * W ^ 21 := by
    have h1 : tcG d n ≤ 5019 * W + 2 * gsm_prec (triBgQ d) := by
      unfold tcG tzP; omega
    calc tcG d n ≤ 5019 * W ^ 21 + 2 * (2 ^ 158 * W ^ 21) := by omega
      _ = (5019 + 2 ^ 159) * W ^ 21 := by ring
  have hc1 : 24 * 2 ^ (158 * 2) ≤ 2 ^ 1100 := tri_two_pow_ge (j := 5 + 158 * 2)
    ((Nat.mul_le_mul_right _ (by norm_num : 24 ≤ 2 ^ 5)).trans_eq (pow_add _ _ _).symm) (by norm_num)
  have hc2 : 2 ^ 1000 * 30 ≤ 2 ^ 1100 := tri_two_pow_ge (j := 1000 + 5)
    ((Nat.mul_le_mul_left _ (by norm_num : 30 ≤ 2 ^ 5)).trans_eq (pow_add _ _ _).symm) (by norm_num)
  have hc3 : 5019 + 2 ^ 159 ≤ 2 ^ 1100 := tri_two_pow_ge (j := 160) (by norm_num) (by norm_num)
  have hc4 : 2 ^ 158 ≤ 2 ^ 1100 := tri_two_pow_ge le_rfl (by norm_num)
  have hV1 : 1 ≤ 2 ^ 1100 * W ^ 210 :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ (by omega)))
  have hX : triWs d m s z (triMstQ (1 / 2) n) (2 ^ triNeQ d (ellPos d n)) (bmUnits (triBgQ d)) (tcG d n)
      (tzGc d (ellPos d n)) (triLa (triSQ d)) (triBvQ d) (gsm_prec (triBgQ d)) (triJaQ d) (tzG d (ellPos d n))
      (triNeQ d (ellPos d n)) ≤ 10 ^ 6 * (2 ^ 1100 * W ^ 210) ^ 4 :=
    (triWs_mono (hL (by omega)) (hL (by omega)) (hL (by omega)) (hL (by omega)) (hL (by omega))
      (hV hN hc2 (by norm_num)) (hV hU hc1 (by norm_num)) (hV hG hc3 (by norm_num)) (hL (by omega))
      (hL (by omega)) (hL (by omega)) (hV hP hc4 (by norm_num)) (hL (by omega)) (hL (by omega))
      (hL (by omega))).trans (triWs_poly hV1)
  have he : (2 ^ 1100 * W ^ 210) ^ 4 = 2 ^ (1100 * 4) * W ^ (210 * 4) := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
  rw [he, ← mul_assoc] at hX
  have h1 : 0 < W ^ (210 * 4) := pow_pos hW1 _
  unfold triC
  rw [add_mul, one_mul]
  generalize 10 ^ 6 * 2 ^ (1100 * 4) = c at hX ⊢
  generalize W ^ (210 * 4) = Y at hX h1 ⊢
  omega

/-- **`TriRule`**: TRI-M on the machine, within `triC * W ^ (210 * 4)` units, with 245 slots, 31 registers and
16 arrays above the bases of its block. -/
theorem triRule : TriRule := by
  refine ⟨xtri, triC, 210 * 4, 245, 31, 16, ?_⟩
  intro d L w n m A b ℓa ℓ s B σ hd hn hL hB hσd hσm hσn hPt hCl hCa
  have hw := tri_work (m := m) (s := s) (z := (frMhat A b).size) hd hn rfl
  have hN0 := Nat.zero_le (2 ^ triNeQ d (ellPos d n))
  unfold triWs at hw
  generalize triC * (d + m + n.size + (frMhat A b).size + s + 1) ^ (210 * 4) = K at hw hCl hCa ⊢
  exact XV.tri hd hn hL hB hσd hσm hσn hPt (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by unfold triE tzP; omega) (by omega) ((triK_eq d n m).trans_le (by omega))

end AdversarialBco.Bit.Transfer
