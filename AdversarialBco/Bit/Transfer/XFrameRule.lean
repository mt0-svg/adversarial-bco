/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XFrameW

@[expose] public section

/-!
# The frame centre on the machine: `FrameRule`

`xframe L B` computes `frameQ d n m A b`: the start constants (`0`, `1` in the slots `o + 15`, `o + 16`, `1` in the
register `rE + 5`), then the read-off F2 for `d = 1` (`XV.frame1`) or ELL-F for `d ≥ 2` (`XV.frameBr`). The block uses
135 slots, 51 registers and 8 arrays; the work term is `10^8 W^11`, `W = d + m + size M̂ + 1`.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.RQ

variable {d : ℕ}

/-- **The frame centre** `xframe L B`. -/
def xframe (L : Layout) (B : PrBlk) : XCmd :=
  .seq (toX (VL.sconst L (B.o + 15) 0))
  (.seq (toX (VL.sconst L (B.o + 16) 1))
  (.seq (.prim (.frag (.nconst (B.rE + 5) 1)))
    (.ifN (B.rE + 5) B.rd (xframeBr L B (B.o + 3) (B.o + 15) (B.o + 75) (B.aW + 2) (B.rE + 1)) (xframe1 L B))))

/-- The units of the read-off F2 (`d = 1`). -/
def frame1U (d m : ℕ) : ℕ := 9 + ((m * ((18 * d + 28) + (2 + 12) + 3) + 3) + 21)

theorem two_le_of_lt_two_pow {A ℓa : ℕ} (hA : 2 ≤ A) (h : A < 2 ^ ℓa) : 2 ≤ ℓa := by
  by_contra hc
  have : 2 ^ ℓa ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

set_option maxHeartbeats 4000000 in
/-- The rule of `xframe`. -/
theorem XV.frame {L : Layout} {w : BitRAM.World d} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    {ℓa ℓ s : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : PrBlk} (hd : 1 ≤ d) (hB : B.OK L 135 51 8)
    (e_d : σ.nat B.rd = d) (e_m : σ.nat B.rm = m) (hℓ : 64 * frEx d m (frMhat A b) + 16 < ℓ)
    (hs : frEx d m (frMhat A b) < s) (hℓa : frRegB d m (frMhat A b) < 2 ^ ℓa)
    (hb1 : 2 * ((frMhat A b : ℤ) ^ (d + 1) * (frMhat A b : ℤ) ^ (d + 1)) < 2 ^ ℓ)
    (hs1 : 2 * ((frMhat A b : ℤ) ^ (d + 1) * (frMhat A b : ℤ) ^ (d + 1)) < 2 ^ s) :
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xframe L B) σ (3 + (frBrU d m (frMhat A b) + frame1U d m + 2)) (fun σ' =>
      PtIn σ' B.aW s (frameQ d n m A b) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => B.o ≤ y) (fun j => B.rE ≤ j) (fun b _ => B.aW ≤ b) σ σ') := by
  obtain ⟨hoS, hrN, haA, hrd, hrm, -, -⟩ := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, r11, r12, r13, r14⟩ := fr_regs hd hℓa
  have hR2 : 2 ≤ frRegB d m (frMhat A b) := by
    unfold frRegB
    have := Nat.one_le_pow 3 (d + m + frG d m (frMhat A b) + 1) (by omega)
    omega
  have hsa : 1 < 2 ^ ℓa := by omega
  have hℓ3 : 3 ≤ ℓ := by omega
  have hℓa2 : 2 ≤ ℓa := two_le_of_lt_two_pow hR2 hℓa
  refine XV.mono (K := 1 + (1 + (1 + (frBrU d m (frMhat A b) + frame1U d m + 2)))) ?_ (by omega) (fun _ h => h)
  refine XV.seq (XV.sconstA hL (x := B.o + 15) (by omega) 0 (small_lt (by norm_num) hℓ3))
    fun σ1 ⟨v1, d1, F1⟩ => ?_
  refine XV.seq (XV.sconstA hL (x := B.o + 16) (by omega) 1 (small_lt (by norm_num) hℓ3))
    fun σ2 ⟨v2, d2, F2⟩ => ?_
  refine XV.seq (XV.nconstA hL (i := B.rE + 5) (by omega) 1 hsa) fun σ3 ⟨v3, d3, F3⟩ => ?_
  have G : FrameA (fun y => B.o ≤ y) (fun j => B.rE ≤ j) (fun b _ => B.aW ≤ b) σ σ3 :=
    ((F1.mono (fun y h => by omega) (fun _ h => h.elim) (fun _ _ h => h.elim)).trans
      (F2.mono (fun y h => by omega) (fun _ h => h.elim) (fun _ _ h => h.elim))).trans
      (F3.mono (fun _ h => h.elim) (fun _ h => by omega) (fun _ _ h => h.elim))
  have z3 : σ3.sc (B.o + 15) = 0 := by rw [F3.2.1 _ id, F2.2.1 _ (by omega), v1, Int.cast_zero]
  have o3 : σ3.sc (B.o + 16) = 1 := by rw [F3.2.1 _ id, v2, Int.cast_one]
  have dr3 : σ3.draws = σ.draws := by rw [d3, d2, d1]
  have e_d3 : σ3.nat B.rd = d := by rw [G.1 _ (by omega), e_d]
  have e_m3 : σ3.nat B.rm = m := by rw [G.1 _ (by omega), e_m]
  by_cases hd2 : 2 ≤ d
  · -- ELL-F
    refine XV.mono (XV.ifN_t hL (by omega) (by omega) (by rw [v3]; exact hsa) (by rw [e_d3]; omega)
      (by rw [v3, e_d3]; omega)
      (XV.frameBr hL (B := B) (P := B.o + 3) (u := B.o + 15) (c := B.o + 75) (a0 := B.aW + 2) (n0 := B.rE + 1)
        hd2 rfl rfl rfl rfl rfl (by omega) (by omega) (by omega) hrd hrm e_d3 e_m3 z3 o3 v3 hℓ hs hℓa))
      (by omega) ?_
    rintro σ' ⟨out, dr, F⟩
    exact ⟨out, dr.trans dr3, G.trans F⟩
  · -- the read-off
    have hd1 : d = 1 := by omega
    refine XV.mono (XV.ifN_f hL (by omega) (by omega) (by rw [v3]; exact hsa) (by rw [e_d3]; omega)
      (by rw [v3, e_d3]; omega)
      (XV.frame1 hL (B := B) (s := s) hd1 (by omega) (by omega) (by omega) hrd hrm e_d3 e_m3 r12 r11 r13 hℓa2
        hb1 hs1)) (by unfold frame1U; omega) ?_
    rintro σ' ⟨out, dr, F⟩
    exact ⟨out, dr.trans dr3, G.trans F⟩

/-! ## The work term -/

theorem frame1U_le_W (d m M : ℕ) : frame1U d m ≤ 96 * (d + m + Nat.size M + 1) ^ 2 := by
  set W := d + m + Nat.size M + 1 with hW
  have hWpos : 1 ≤ W := by omega
  have hmW : m ≤ W := by omega
  have hdW : d + 1 ≤ W := by omega
  have e : frame1U d m = m * (18 * d + 45) + 33 := by unfold frame1U; ring
  rw [e]
  calc m * (18 * d + 45) + 33 ≤ W * (18 * W + 45) + 33 := by nlinarith
    _ = 18 * W ^ 2 + 45 * W + 33 := by ring
    _ ≤ 96 * W ^ 2 := by nlinarith

/-- **Interface II, the frame centre** (`FrameRule`): `xframe`, within `10^8 W^11` units, with 135 slots,
51 registers and 8 arrays above the bases of its block. -/
theorem frameRule : FrameRule := by
  refine ⟨xframe, 10 ^ 8, 11, 135, 51, 8, ?_⟩
  intro d L w n m A b ℓa ℓ B σ hd hL hB e_d e_m hℓ hℓa
  have hW1 : 1 ≤ d + m + (frMhat A b).size + 1 := by omega
  have h9 : (d + m + (frMhat A b).size + 1) ^ 9 ≤ (d + m + (frMhat A b).size + 1) ^ 11 :=
    Nat.pow_le_pow_right hW1 (by norm_num)
  have h2 : (d + m + (frMhat A b).size + 1) ^ 2 ≤ (d + m + (frMhat A b).size + 1) ^ 11 :=
    Nat.pow_le_pow_right hW1 (by norm_num)
  have h0 : 1 ≤ (d + m + (frMhat A b).size + 1) ^ 11 := Nat.one_le_pow _ _ hW1
  have hE := frEx_lt_C d m (frMhat A b)
  have hR := frRegB_le_W d m (frMhat A b)
  have hU := frBrU_le_W d m (frMhat A b) hd
  have h1U := frame1U_le_W d m (frMhat A b)
  have hb := frame1_hb d m (frMhat A b)
  exact XV.mono (XV.frame hL (s := 10 ^ 8 * (d + m + (frMhat A b).size + 1) ^ 11) hd hB e_d e_m (by omega)
    (by omega) (by omega) (hb.trans_le (pow_le_pow_right₀ (by norm_num) hℓ)) hb) (by omega) (fun _ h => h)

end AdversarialBco.Bit.Transfer
