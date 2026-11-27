/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOSetup
public import AdversarialBco.Bit.Transfer.XTriMag
public import AdversarialBco.Bit.Transfer.XTriM

@[expose] public section

/-!
# BL-O's setup: the coin count

After TRI-OGD-O has read `L' = LposO` coins, the prologue completes its `P0O` blocks of `2B` coins: `xcoinsO` reads
`m = K0O - L' = 2B ⌈L'/(2B)⌉ - L'` coins in one leaf, `m` computed from `B` (register `rB`) and `L'` (slot `sLp`) as
`((L' + 2B - 1) / (2B)) 2B - L'` in the slots `130, ..., 134`.

The magnitudes: `LposO ≤ 2^{1200 (W + 1)}` (`LposO_le`, from v2.1's linear bounds `triNeQ_le_lin` and `triKgQ_le`
on TRI's parameters) and `B ≤ 1000 (W + 1)` (`parO_B_le`), `W = wU d n δ r0 R0 a`.
`coinsSpecO : CoinsSpecO xcoinsO 4096 1 172 48 0`.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.RQ (triMstQ triNeQ triBgQ triKgQ)
open AdversarialBco.BitRAM (len)

variable {d : ℕ}

/-! ## The magnitudes -/

theorem len_natCast (m : ℕ) : len (m : ℤ) = m.size := by
  simp [len]

/-- `k_δ ≤ size den`. -/
theorem kDel_le_size {δ : ℚ} (h0 : 0 < δ) : kDel δ ≤ δ.den.size := by
  rw [kDel_eq h0]
  apply Nat.size_le_size
  have hb : 1 ≤ δ.num.toNat := by have := Rat.num_pos.2 h0; omega
  obtain ⟨c, hc⟩ : ∃ c, δ.num.toNat = c + 1 := ⟨δ.num.toNat - 1, by omega⟩
  rw [hc]
  apply Nat.div_le_of_le_mul
  have h1 : 1 ≤ δ.den := δ.den_pos
  have e : δ.den + (c + 1) - 1 = δ.den + c := by omega
  rw [e]
  nlinarith

/-- The number of TRI's stages is at most `len R0_num + len r0_den + 1`. -/
theorem triMstQ_le {r0 R0 : ℚ} (h0 : 0 < r0) (h1 : r0 ≤ R0) :
    triMstQ r0 R0 ≤ len R0.num + len (r0.den : ℤ) + 1 := by
  unfold triMstQ
  refine max_le (by omega) ?_
  have hR : 0 < R0 := lt_of_lt_of_le h0 h1
  have hRn : (0 : ℚ) < R0.num := by exact_mod_cast Rat.num_pos.2 hR
  have hrn1 : (1 : ℚ) ≤ r0.num := by exact_mod_cast Rat.num_pos.2 h0
  have e1 : (R0.num : ℚ) = R0 * R0.den := (Rat.mul_den_eq_num R0).symm
  have e2 : (r0.num : ℚ) = r0 * r0.den := (Rat.mul_den_eq_num r0).symm
  have hRd : (1 : ℚ) ≤ R0.den := by exact_mod_cast R0.den_pos
  have hq : R0 / r0 ≤ ((R0.num.natAbs * r0.den : ℕ) : ℚ) := by
    have hnat : ((R0.num.natAbs : ℕ) : ℚ) = R0.num := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos hRn]
    push_cast
    rw [hnat, div_le_iff₀ h0]
    have e3 : (R0.num : ℚ) * r0.den * r0 = R0.num * r0.num := by rw [e2]; ring
    rw [e3]
    have h3 : R0 ≤ (R0.num : ℚ) := by rw [e1]; nlinarith
    have h4 : (R0.num : ℚ) ≤ R0.num * r0.num := by nlinarith
    linarith
  apply Nat.clog_le_of_le_pow
  have a1 : R0.num.natAbs < 2 ^ len R0.num := Nat.lt_size_self _
  have a2 : r0.den < 2 ^ len (r0.den : ℤ) := by rw [len_natCast]; exact Nat.lt_size_self _
  refine (Nat.ceil_le.2 hq).trans ((Nat.mul_le_mul a1.le a2.le).trans ?_)
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- TRI-OGD-O's confidence exponent. -/
theorem ellPosO_le (d n k : ℕ) (r0 R0 : ℚ) :
    ellPosO d n k r0 R0 ≤ 21 + k + 3 * (d + n.size) + triMstQ r0 R0 := by
  unfold ellPosO
  apply Nat.clog_le_of_le_pow
  have h1 : d * n ≤ 2 ^ (d + n.size) := by
    rw [pow_add]; exact Nat.mul_le_mul Nat.lt_two_pow_self.le (Nat.lt_size_self n).le
  have h2 : (d * n) ^ 3 ≤ 2 ^ (3 * (d + n.size)) :=
    calc (d * n) ^ 3 ≤ (2 ^ (d + n.size)) ^ 3 := Nat.pow_le_pow_left h1 3
      _ = 2 ^ (3 * (d + n.size)) := by rw [← pow_mul, mul_comm]
  have h3 : triMstQ r0 R0 ≤ 2 ^ triMstQ r0 R0 := Nat.lt_two_pow_self.le
  calc 3 * 2 ^ (19 + k) * (d * n) ^ 3 * triMstQ r0 R0
      ≤ 2 ^ 2 * 2 ^ (19 + k) * 2 ^ (3 * (d + n.size)) * 2 ^ triMstQ r0 R0 := by gcongr; norm_num
    _ = 2 ^ (21 + k + 3 * (d + n.size) + triMstQ r0 R0) := by
      rw [← pow_add, ← pow_add, ← pow_add]; congr 1; omega

/-- **The coins of TRI-OGD-O**, `LposO ≤ 2^{1200 (W + 1)}`. -/
theorem LposO_le {n : ℕ} {δ r0 R0 : ℚ} (a : Fin d → ℚ) (hI : InU d n δ r0 R0) :
    LposO d n δ r0 R0 ≤ 2 ^ (1200 * (wU d n δ r0 R0 a + 1)) := by
  have hd := hI.hd
  have hM := triMstQ_le hI.hr0 hI.hR0
  have hk := kDel_le_size hI.hδ0
  have hS : len R0.num + len (r0.den : ℤ) + len (δ.den : ℤ) ≤ sizeN δ r0 R0 a := by unfold sizeN; omega
  rw [len_natCast δ.den] at hS
  have hW : wU d n δ r0 R0 a = d + n.size + sizeN δ r0 R0 a + 1 := rfl
  have hlp := ellPosO_le d n (kDel δ) r0 R0
  have hNe := AdversarialBco.Bit.TriM.triNeQ_le_lin hd (ellPosO d n (kDel δ) r0 R0)
  have hKg := AdversarialBco.Bit.TriM.triKgQ_le hd
  unfold LposO triLTQ triNeTQ triBgQ
  have b1 : triMstQ r0 R0 ≤ 2 ^ triMstQ r0 R0 := Nat.lt_two_pow_self.le
  have b2 : 2 ^ (triNeQ d (ellPosO d n (kDel δ) r0 R0) + 1) ≤
      2 ^ (1001 + 200 * d + ellPosO d n (kDel δ) r0 R0) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have b3 : 2 * d * (4 * triKgQ d) ≤ 2 ^ (157 + 22 * d) := by
    have hd2 : d ≤ 2 ^ d := Nat.lt_two_pow_self.le
    have h21 : d ^ 21 ≤ 2 ^ (21 * d) :=
      calc d ^ 21 ≤ (2 ^ d) ^ 21 := Nat.pow_le_pow_left hd2 21
        _ = 2 ^ (21 * d) := by rw [← pow_mul, mul_comm]
    calc 2 * d * (4 * triKgQ d) ≤ 2 * 2 ^ d * (4 * (2 ^ 154 * 2 ^ (21 * d))) := by gcongr; exact hKg.trans (by gcongr)
      _ = 2 ^ (157 + 22 * d) := by ring
  calc triMstQ r0 R0 * (2 ^ (triNeQ d (ellPosO d n (kDel δ) r0 R0) + 1) * (2 * d * (4 * triKgQ d)))
      ≤ 2 ^ triMstQ r0 R0 * (2 ^ (1001 + 200 * d + ellPosO d n (kDel δ) r0 R0) * 2 ^ (157 + 22 * d)) := by
        gcongr
    _ = 2 ^ (triMstQ r0 R0 + (1001 + 200 * d + ellPosO d n (kDel δ) r0 R0 + (157 + 22 * d))) := by
        rw [← pow_add, ← pow_add]
    _ ≤ 2 ^ (1200 * (wU d n δ r0 R0 a + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **PARAM's block length**, `B ≤ 1000 (W + 1)`. -/
theorem parO_B_le {n : ℕ} {δ r0 R0 : ℚ} (a : Fin d → ℚ) (hI : InU d n δ r0 R0) :
    (parO d n δ).B ≤ 1000 * (wU d n δ r0 R0 a + 1) := by
  have hk := kDel_le_size hI.hδ0
  have hS : len (δ.den : ℤ) ≤ sizeN δ r0 R0 a := by unfold sizeN; omega
  rw [len_natCast δ.den] at hS
  have hW : wU d n δ r0 R0 a = d + n.size + sizeN δ r0 R0 a + 1 := rfl
  have hB : (parO d n δ).B =
      2 * (10 * (NeO d n (kDel δ)).size + 16 * d.size + 160 + (n * (d + 2)).size + 2) := rfl
  have hd2 : d < 2 ^ d := Nat.lt_two_pow_self
  have hn2 : n < 2 ^ n.size := Nat.lt_size_self n
  have h1 : (NeO d n (kDel δ)).size ≤ 21 + kDel δ + 3 * d + 4 * n.size := by
    rw [Nat.size_le]
    unfold NeO
    calc 15 * 2 ^ (17 + kDel δ) * d ^ 3 * n ^ 4 = 15 * 2 ^ (17 + kDel δ) * (d ^ 3 * n ^ 4) := by ring
      _ ≤ 15 * 2 ^ (17 + kDel δ) * ((2 ^ d) ^ 3 * (2 ^ n.size) ^ 4) := by gcongr
      _ < 16 * 2 ^ (17 + kDel δ) * ((2 ^ d) ^ 3 * (2 ^ n.size) ^ 4) :=
          Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right (by norm_num) (by positivity)) (by positivity)
      _ = 2 ^ (21 + kDel δ + 3 * d + 4 * n.size) := by ring
  have h2 : d.size ≤ d := Nat.size_le.2 hd2
  have h3 : (n * (d + 2)).size ≤ n.size + (d + 2) := by
    rw [Nat.size_le, pow_add]
    exact mul_lt_mul'' hn2 (Nat.lt_two_pow_self) (Nat.zero_le _) (Nat.zero_le _)
  rw [hB]
  omega

/-! ## The block -/

/-- The coin count: `130 := B`, `131 := 2B`, `132 := L' + 2B - 1`, `133 := ((L' + 2B - 1)/(2B)) 2B`,
`134 := 133 - L'`, register `8 := 134`, then `8` coins into slot `135`. -/
def xcoinsO (L : Layout) : XCmdO :=
  .base (.seq (toX (VL.ncast L 130 rB)) (.seq (toX (VL.sop2 L .add 131 130 130))
    (.seq (toX (VL.sop2 L .add 132 sLp 131)) (.seq (toX (VL.sop2 L .sub 132 132 26))
    (.seq (xsidiv L 133 132 131) (.seq (toX (VL.sop2 L .mul 133 133 131))
    (.seq (toX (VL.sop2 L .sub 134 133 sLp)) (.seq (xrtoN L 8 134) (xcoins L 135 8)))))))))

set_option maxHeartbeats 4000000 in
/-- **The coin count on the machine.** -/
theorem coinsSpecO : CoinsSpecO xcoinsO 4096 1 172 48 0 := by
  intro d L w n δ r0 R0 a ℓa ℓ σ hI hL hR hBas hP hLp hℓ hℓa
  obtain ⟨hNS, hNN, -⟩ := hR
  simp only [pow_one] at hℓ hℓa ⊢
  refine XVO.ofX ?_
  have hLw := LposO_le a hI
  have hBw := parO_B_le a hI
  have hB0 := parO_B_pos d n δ
  have hK := LposO_le_K0O d n δ r0 R0
  have h26 : σ.sc 26 = 1 := hBas.2.2.2.2.1
  have hrB : σ.nat rB = (parO d n δ).B := hP.regs.2.2.2
  set W := wU d n δ r0 R0 a with hWdef
  set Lp := LposO d n δ r0 R0 with hLpdef
  set B := (parO d n δ).B with hBdef
  set q := (Lp + 2 * B - 1) / (2 * B) with hqdef
  have hKe : K0O d n δ r0 R0 = 2 * B * q := rfl
  set K := K0O d n δ r0 R0 with hKdef
  have hKle : 2 * B * q ≤ Lp + 2 * B - 1 := by rw [mul_comm]; exact Nat.div_mul_le_self _ _
  have hqle : q ≤ Lp + 2 * B - 1 := Nat.div_le_self _ _
  set m := K - Lp with hmdef
  have hm : m < 2 * B := by omega
  -- the magnitudes
  have hE : Lp + 2 * B < 2 ^ ℓ := by
    have h2B : 2 * B < 2 ^ (2000 * (W + 1)) :=
      lt_of_le_of_lt (by omega) (Nat.lt_two_pow_self (n := 2000 * (W + 1)))
    have hL2 : Lp ≤ 2 ^ (2000 * (W + 1)) := hLw.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    calc Lp + 2 * B < 2 ^ (2000 * (W + 1)) * 2 := by omega
      _ = 2 ^ (2000 * (W + 1) + 1) := (pow_succ _ _).symm
      _ ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hEZ : (Lp : ℤ) + 2 * B < 2 ^ ℓ := by exact_mod_cast hE
  have ab : ∀ z : ℤ, 0 ≤ z → z ≤ (Lp : ℤ) + 2 * B → |z| < 2 ^ ℓ := fun z h0 h1 =>
    abs_lt.2 ⟨by linarith [pow_pos (show (0 : ℤ) < 2 by norm_num) ℓ], by linarith⟩
  have e1 : ((Lp + 2 * B - 1 : ℕ) : ℤ) = (Lp : ℤ) + (B + B) - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e2 : ((2 * B : ℕ) : ℤ) = (B : ℤ) + B := by push_cast; ring
  have hqZ : ((Lp : ℤ) + (B + B) - 1) / (B + B) = (q : ℤ) := by rw [hqdef, Int.natCast_div, e1, e2]
  have hmZ : (q : ℤ) * (B + B) - Lp = (m : ℤ) := by
    rw [hmdef, Nat.cast_sub hK, hKe]; push_cast; ring
  have hqZle : (q : ℤ) * (B + B) ≤ (Lp : ℤ) + 2 * B := by
    have : ((2 * B * q : ℕ) : ℤ) ≤ ((Lp + 2 * B - 1 : ℕ) : ℤ) := by exact_mod_cast hKle
    rw [e1] at this; push_cast at this; linarith
  have hqZle' : (q : ℤ) ≤ (Lp : ℤ) + 2 * B := by
    have : ((q : ℕ) : ℤ) ≤ ((Lp + 2 * B - 1 : ℕ) : ℤ) := by exact_mod_cast hqle
    rw [e1] at this; linarith
  have hla : 4096 * (W + 1) < 2 ^ ℓa := hℓa
  clear_value W Lp B q K m
  clear hWdef hLpdef hBdef hqdef hKdef hmdef
  -- the run
  refine XV.mono (K := 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))) ?_ (by omega) fun _ h => h
  refine XV.seq (XV.ncastI hL (x := 130) (i := rB) (by omega) (by bomega) (by rw [hrB]; omega)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.addI hL (x := 131) (a := 130) (b := 130) (by omega) (by omega) (by omega) (u := B) (v := B)
    (by simp [hrB]) (by simp [hrB]) (ab _ (by omega) (by omega)) (ab _ (by omega) (by omega))
    (ab _ (by omega) (by omega))) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.addI hL (x := 132) (a := sLp) (b := 131) (by omega) (by simp only [sLp]; omega)
    (by omega) (u := Lp) (v := B + B) (by simp [hLp]) (by simp) (ab _ (by omega) (by omega))
    (ab _ (by omega) (by omega)) (ab _ (by omega) (by omega))) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.subI hL (x := 132) (a := 132) (b := 26) (by omega) (by omega) (by omega)
    (u := Lp + (B + B)) (v := 1) (by simp) (by simp [h26]) (ab _ (by omega) (by omega))
    (ab _ (by norm_num) (by omega)) (ab _ (by omega) (by omega))) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.divI hL (x := 133) (a := 132) (b := 131) (by omega) (by omega) (by omega)
    (u := Lp + (B + B) - 1) (v := B + B) (by simp) (by simp) (ab _ (by omega) (by omega))
    (ab _ (by omega) (by omega))) fun σ5 e5 => ?_
  subst e5
  rw [hqZ] at *
  refine XV.seq (XV.mulI hL (x := 133) (a := 133) (b := 131) (by omega) (by omega) (by omega)
    (u := q) (v := B + B) (by simp) (by simp) (ab _ (by omega) hqZle')
    (ab _ (by omega) (by omega)) (ab _ (by omega) hqZle)) fun σ6 e6 => ?_
  subst e6
  refine XV.seq (XV.subI hL (x := 134) (a := 133) (b := sLp) (by omega) (by omega) (by simp only [sLp]; omega)
    (u := q * (B + B)) (v := Lp) (by simp) (by simp [hLp]) (ab _ (by omega) hqZle)
    (ab _ (by omega) (by omega)) (ab _ (by rw [hmZ]; omega) (by rw [hmZ]; omega))) fun σ7 e7 => ?_
  subst e7
  refine XV.seq (XV.rtoNat hL (i := 8) (x := 134) (v := m) (by omega) (by omega) (by simp [hmZ]) (by omega)
    (by omega)) fun σ8 e8 => ?_
  subst e8
  refine XV.mono (XV.coins hL (x := 135) (i := 8) (by omega) (by omega) (by simp; omega) (by simp; omega)) le_rfl
    fun σ9 e9 => ?_
  subst e9
  refine ⟨by simp, ?_⟩
  refine ⟨fun j hj => ?_, fun y hy => ?_, fun b k _ => rfl, rfl, rfl⟩
  · dsimp only
    simp only [Env.setSc_nat, Env.setNat_nat]
    split_ifs <;> omega
  · dsimp only
    simp only [Env.setSc_sc, Env.setNat_sc]
    split_ifs <;> first | omega | rfl

end AdversarialBco.Unified.ProgO
