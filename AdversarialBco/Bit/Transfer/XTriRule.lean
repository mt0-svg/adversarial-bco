/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriConsts
public import AdversarialBco.Bit.Transfer.XTriChain
public import AdversarialBco.Bit.Transfer.XTriMag

@[expose] public section

/-!
# TRI-M on the machine

* `xtri`: the constants block, the initial position from the frame centre, the stages;
* `triE`, `triK`: the exponent of the magnitudes and the units of `xtri`;
* the bounds `XV.stages` reads, from the bounds of a stage (`stage_D_le`, `stage_entries_le`) and the rows;
* `XV.tri`: `xtri` computes `posQ d n m A b` on the coins from `draws`, reading `K0Q d n` coins.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM
  AdversarialBco.Bit.Transfer.BLM

variable {d : ℕ}

/-- TRI-M: the constants, `P_0` from the frame centre in `B.aC`, then the `m_st` stages. -/
def xtri (L : Layout) (B : PrBlk) : XCmd :=
  .seq (xconsts L B.rd B.rm B.sn B.o B.rE)
  (.seq (xinit L B.o B.rE B.aW B.rd B.aC) (xstages L B.o B.rE B.aW B.rd B.aC))

/-- The exponent of the magnitudes of TRI-M (`s` the bits of the frame centre, `z` those of `M̂`). -/
def triE (d n s z : ℕ) : ℕ :=
  s + z * (d + 2) + triMstQ (1 / 2) n * (tzGc d (ellPos d n) + triLa (triSQ d) + d) +
    triMstQ (1 / 2) n * tzGc d (ellPos d n) + triMstQ (1 / 2) n + triBvQ d + 2 * tzP d + triJaQ d +
    triLa (triSQ d) + tzG d (ellPos d n) + triNeQ d (ellPos d n) + 4 * gsm_prec (triBgQ d) + d + 20

/-- The units of TRI-M. -/
abbrev triK (d n m : ℕ) : ℕ :=
  constsK d n + (initK d + stagesK d (m + (d + d)) (2 ^ triNeQ d (ellPos d n)) (triBgQ d) (triMstQ (1 / 2) n))

/-! ## The bounds of the stages -/

theorem two_pow_le_two_pow {a b : ℕ} (h : a ≤ b) : (2 : ℤ) ^ a ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) h

theorem frMhat_pow_le {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (k : ℕ) :
    (frMhat A b : ℤ) ^ k ≤ 2 ^ ((frMhat A b).size * k) := by
  rw [pow_mul]
  exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast (Nat.lt_size_self _).le) k

theorem tri_bT {m : ℕ} {n : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {Dc : ℤ} {ch : Fin d → ℤ}
    {ω : ℕ → ℕ → Bool} {s E mst : ℕ} (hC : ∀ i, |ch i| ≤ 2 ^ s) (hD : |Dc| ≤ 2 ^ s)
    (hE : s + 1 + mst * (tzGc d (ellPos d n) + triLa (triSQ d) + d) ≤ E) {t : ℕ} (ht : t ≤ mst) :
    (∀ i l, |(tzStage n A b Dc ch ω t).T i l| ≤ 2 ^ E) ∧ ∀ l, |(tzStage n A b Dc ch ω t).mu l| ≤ 2 ^ E := by
  obtain ⟨h1, h2⟩ := stage_entries_le n A b Dc ch ω s hC hD t
  have hx := Nat.mul_le_mul_right (tzGc d (ellPos d n) + triLa (triSQ d) + d) ht
  have he : s + 1 + t * (tzGc d (ellPos d n) + triLa (triSQ d) + d) ≤ E := by omega
  exact ⟨fun i l => (h2 i l).trans (two_pow_le_two_pow he), fun l => (h1 l).trans (two_pow_le_two_pow he)⟩

theorem tri_bD {m : ℕ} {n : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {Dc : ℤ} {ch : Fin d → ℤ}
    {ω : ℕ → ℕ → Bool} {s E mst : ℕ} (hD0 : 0 < Dc) (hD : Dc < 2 ^ s)
    (hE : mst + s + 1 + mst * tzGc d (ellPos d n) ≤ E) {t : ℕ} (ht : t ≤ mst) :
    |2 ^ t * (tzStage n A b Dc ch ω t).D| ≤ 2 ^ E := by
  obtain ⟨h0, h1⟩ := stage_D_le n A b Dc ch ω s hD0 hD t
  have hx := Nat.mul_le_mul_right (tzGc d (ellPos d n)) ht
  rw [abs_of_pos (by positivity)]
  calc (2 : ℤ) ^ t * (tzStage n A b Dc ch ω t).D ≤ 2 ^ t * 2 ^ (s + 1 + t * tzGc d (ellPos d n)) :=
        mul_le_mul_of_nonneg_left h1.le (by positivity)
    _ = 2 ^ (t + (s + 1 + t * tzGc d (ellPos d n))) := (pow_add _ _ _).symm
    _ ≤ 2 ^ E := two_pow_le_two_pow (by omega)

theorem tri_bRA {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) {E : ℕ}
    (hE : (frMhat A b).size * (d + 1) ≤ E) (k : ℕ) (l : Fin d) : |onN (tzRowA A b) k l| ≤ 2 ^ E := by
  unfold onN
  split_ifs with hk
  · exact (tzRowA_abs_le A b ⟨k, hk⟩ l).trans ((frMhat_pow_le A b _).trans (two_pow_le_two_pow hE))
  · simp only [Pi.zero_apply, abs_zero]; positivity

theorem tri_bRB {m : ℕ} {n : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {Dc : ℤ} {ch : Fin d → ℤ}
    {ω : ℕ → ℕ → Bool} {s E mst : ℕ} (hD0 : 0 < Dc) (hD : Dc < 2 ^ s) (hC : ∀ i, |ch i| ≤ 2 ^ s)
    (hE : (frMhat A b).size * (d + 1) + mst + s + 3 + mst * tzGc d (ellPos d n) ≤ E) {t : ℕ} (ht : t ≤ mst) (k : ℕ) :
    |onN (tzRowB A b ch (1 + t * tzGc d (ellPos d n)) t (tzStage n A b Dc ch ω t).D) k| ≤ 2 ^ E := by
  obtain ⟨h0, h1⟩ := stage_D_le n A b Dc ch ω s hD0 hD t
  have hx := Nat.mul_le_mul_right (tzGc d (ellPos d n)) ht
  set z := (frMhat A b).size
  set Q := z * (d + 1) + t + (s + 1 + t * tzGc d (ellPos d n)) with hQ
  unfold onN
  split_ifs with hk
  · refine (tzRowB_abs_le A b ch _ t _ (2 ^ s) h0.le (by positivity) hC ⟨k, hk⟩).trans ?_
    have e1 : (frMhat A b : ℤ) ^ (d + 1) * (tzStage n A b Dc ch ω t).D ≤ 2 ^ Q := by
      calc (frMhat A b : ℤ) ^ (d + 1) * (tzStage n A b Dc ch ω t).D
          ≤ 2 ^ (z * (d + 1)) * 2 ^ (s + 1 + t * tzGc d (ellPos d n)) :=
            mul_le_mul (frMhat_pow_le A b _) h1.le h0.le (by positivity)
        _ = 2 ^ (z * (d + 1) + (s + 1 + t * tzGc d (ellPos d n))) := (pow_add _ _ _).symm
        _ ≤ 2 ^ Q := two_pow_le_two_pow (by omega)
    have e2 : (2 : ℤ) ^ s * 2 ^ (1 + t * tzGc d (ellPos d n)) ≤ 2 ^ Q := by
      rw [← pow_add]; exact two_pow_le_two_pow (by omega)
    have e3 : (2 : ℤ) ^ t * (tzStage n A b Dc ch ω t).D ≤ 2 ^ Q := by
      calc (2 : ℤ) ^ t * (tzStage n A b Dc ch ω t).D ≤ 2 ^ t * 2 ^ (s + 1 + t * tzGc d (ellPos d n)) :=
            mul_le_mul_of_nonneg_left h1.le (by positivity)
        _ = 2 ^ (t + (s + 1 + t * tzGc d (ellPos d n))) := (pow_add _ _ _).symm
        _ ≤ 2 ^ Q := two_pow_le_two_pow (by omega)
    have e4 : (2 : ℤ) ^ (Q + 2) ≤ 2 ^ E := two_pow_le_two_pow (by omega)
    rw [pow_add] at e4
    have e5 : (0 : ℤ) ≤ 2 ^ Q := by positivity
    linarith
  · simp only [abs_zero]; positivity

theorem tri_hb {m : ℕ} {n : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {Dc : ℤ} {ch : Fin d → ℤ}
    {ω : ℕ → ℕ → Bool} {s ℓ mst : ℕ} (hD0 : 0 < Dc) (hD : Dc < 2 ^ s)
    (hE : (frMhat A b).size * (d + 2) + s + 1 + mst * tzGc d (ellPos d n) ≤ ℓ) {t : ℕ} (ht : t ≤ mst) :
    (frMhat A b : ℤ) ^ (d + 2) * (tzStage n A b Dc ch ω t).D < 2 ^ ℓ := by
  obtain ⟨h0, h1⟩ := stage_D_le n A b Dc ch ω s hD0 hD t
  have hx := Nat.mul_le_mul_right (tzGc d (ellPos d n)) ht
  calc (frMhat A b : ℤ) ^ (d + 2) * (tzStage n A b Dc ch ω t).D
      < 2 ^ ((frMhat A b).size * (d + 2)) * 2 ^ (s + 1 + t * tzGc d (ellPos d n)) :=
        mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (frMhat_pow_le A b _) h1 h0.le (by positivity)
    _ = 2 ^ ((frMhat A b).size * (d + 2) + (s + 1 + t * tzGc d (ellPos d n))) := (pow_add _ _ _).symm
    _ ≤ 2 ^ ℓ := two_pow_le_two_pow (by omega)

/-- The constants of a draw against `2^E`. -/
theorem tri_bDC {n E : ℕ} (hE : triBvQ d + 2 * tzP d + triJaQ d + triLa (triSQ d) + tzG d (ellPos d n) +
      triNeQ d (ellPos d n) + d + 8 ≤ E) :
    |(tzDC d (ellPos d n)).PB| ≤ 2 ^ E ∧ |(tzDC d (ellPos d n)).P2| ≤ 2 ^ E ∧
      |(tzDC d (ellPos d n)).Pj| ≤ 2 ^ E ∧ (tzDC d (ellPos d n)).Bh ≤ 2 ^ E ∧
      |8 * (tzDC d (ellPos d n)).dd| ≤ 2 ^ E ∧ 2 ^ triNeQ d (ellPos d n) ≤ 2 ^ E ∧
      ((2 ^ triNeQ d (ellPos d n) : ℕ) : ℤ) * (tzDC d (ellPos d n)).Bh ≤ 2 ^ E := by
  have hBh : (tzDC d (ellPos d n)).Bh ≤ 2 ^ (8 + triLa (triSQ d) + tzG d (ellPos d n)) := by
    show (161 : ℤ) * 2 ^ (triLa (triSQ d) - 10 + tzG d (ellPos d n)) ≤ _
    calc (161 : ℤ) * 2 ^ (triLa (triSQ d) - 10 + tzG d (ellPos d n))
        ≤ 2 ^ 8 * 2 ^ (triLa (triSQ d) + tzG d (ellPos d n)) :=
          mul_le_mul (by norm_num) (two_pow_le_two_pow (by omega)) (by positivity) (by positivity)
      _ = 2 ^ (8 + triLa (triSQ d) + tzG d (ellPos d n)) := by rw [← pow_add, Nat.add_assoc]
  refine ⟨?_, ?_, ?_, hBh.trans (two_pow_le_two_pow (by omega)), ?_, Nat.pow_le_pow_right (by norm_num) (by omega),
    ?_⟩
  · show |(2 : ℤ) ^ triBvQ d| ≤ _
    rw [abs_of_pos (by positivity)]; exact two_pow_le_two_pow (by omega)
  · show |(2 : ℤ) ^ (2 * tzP d)| ≤ _
    rw [abs_of_pos (by positivity)]; exact two_pow_le_two_pow (by omega)
  · show |(2 : ℤ) ^ triJaQ d| ≤ _
    rw [abs_of_pos (by positivity)]; exact two_pow_le_two_pow (by omega)
  · show |8 * (d : ℤ)| ≤ _
    rw [abs_of_nonneg (by positivity)]
    have h1 : (d : ℤ) ≤ 2 ^ d := by exact_mod_cast Nat.lt_two_pow_self.le
    calc 8 * (d : ℤ) ≤ 2 ^ 3 * 2 ^ d := by norm_num; linarith
      _ = 2 ^ (3 + d) := (pow_add _ _ _).symm
      _ ≤ 2 ^ E := two_pow_le_two_pow (by omega)
  · push_cast
    calc (2 : ℤ) ^ triNeQ d (ellPos d n) * (tzDC d (ellPos d n)).Bh
        ≤ 2 ^ triNeQ d (ellPos d n) * 2 ^ (8 + triLa (triSQ d) + tzG d (ellPos d n)) :=
          mul_le_mul_of_nonneg_left hBh (by positivity)
      _ = 2 ^ (triNeQ d (ellPos d n) + (8 + triLa (triSQ d) + tzG d (ellPos d n))) := (pow_add _ _ _).symm
      _ ≤ 2 ^ E := two_pow_le_two_pow (by omega)

/-! ## TRI-M on the machine -/

set_option maxHeartbeats 16000000 in
/-- **TRI-M on the machine**: `xtri` computes `posQ d n m A b` on the coins from `draws`, reading `K0Q d n`
coins, within `triK d n m` units, under bounds on the registers and the magnitudes. -/
theorem XV.tri {L : Layout} {w : BitRAM.World d} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    {ℓa ℓ s K : ℕ} {B : PrBlk} {σ : Env d} (hd : 1 ≤ d) (hn : 1 ≤ n) (hL : LayOK L d ℓa)
    (hB : B.OK L 245 31 16) (hσd : σ.nat B.rd = d) (hσm : σ.nat B.rm = m) (hσn : σ.sc B.sn = n)
    (hPt : PtIn σ B.aC s (frameQ d n m A b))
    (hda : d * d + m + (d + d) + 2 < 2 ^ ℓa) (hNa : 2 ^ triNeQ d (ellPos d n) < 2 ^ ℓa)
    (hTl : ev (tcG d n) tcT < ℓ) (hTa : ev (tcG d n) tcT < 2 ^ ℓa)
    (hka : 4 + 2 * ((d + 1) * (m + 1)) < 2 ^ ℓa) (hsa : triMstQ (1 / 2) n < 2 ^ ℓa)
    (hBa : 4 * gsm_prec (triBgQ d) + 2 < 2 ^ ℓa)
    (hE : 48 * triE d n s (frMhat A b).size + 42 * d + 32 < ℓ)
    (hK : s + 1 + triMstQ (1 / 2) n * (tzGc d (ellPos d n) + triLa (triSQ d) + d) < K)
    (hU : triK d n m ≤ K) :
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xtri L B) σ K (fun σ' =>
      PosIn σ' B.o B.aW K (posQ d n m A b fun j => w.cs (σ.draws + j)) ∧ σ'.draws = σ.draws + K0Q d n ∧
      FrameA (fun y => B.o ≤ y) (fun j => B.rE ≤ j) (fun b _ => B.aW ≤ b) σ σ') := by
  obtain ⟨hoS, hrN, haA, hrd, hrm, hsn, haC⟩ := hB
  obtain ⟨Dc, hDc0, hDcs, eD, hx⟩ := hPt
  choose ch hch using hx
  have hC : ∀ i, |ch i| ≤ 2 ^ s := fun i => (hch i).1.le
  have hDs : |Dc| ≤ 2 ^ s := by rw [abs_of_pos hDc0]; exact hDcs.le
  -- the exponent `E`
  have hE0 : s + (frMhat A b).size * (d + 2) + triMstQ (1 / 2) n * (tzGc d (ellPos d n) + triLa (triSQ d) + d) +
      triMstQ (1 / 2) n * tzGc d (ellPos d n) + triMstQ (1 / 2) n + triBvQ d + 2 * tzP d + triJaQ d +
      triLa (triSQ d) + tzG d (ellPos d n) + triNeQ d (ellPos d n) + 4 * gsm_prec (triBgQ d) + d + 20 =
      triE d n s (frMhat A b).size := rfl
  have hz : (frMhat A b).size * (d + 1) ≤ (frMhat A b).size * (d + 2) := Nat.mul_le_mul_left _ (by omega)
  have hB1 : 1 ≤ triBgQ d := by
    have := le_max_left 2 (Nat.clog 2 ⌈16 * triBQ d * (d + 1) * d * (8 * d + 2) / triEloQ d⌉₊)
    unfold triBgQ triKgQ; omega
  refine XV.mono (K := triK d n m) ?_ hU (fun _ h => h)
  unfold xtri
  -- the constants
  refine XV.seq (XV.consts (X := ctxOf w n m A b) hL hd hn (by omega) (by omega) hrd hrm hsn hσd hσm hσn hda hNa
    hTl hTa) fun σ1 ⟨a1, a2, a3, a12, a24, a25, a26, a28, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13,
      c35, d1, F1⟩ => ?_
  have eD1 : σ1.arr B.aC 0 = Dc := by rw [F1.2.2.1 _ _ id, eD]
  have eC1 : ∀ i : Fin d, σ1.arr B.aC (i + 1) = ch i := fun i => by rw [F1.2.2.1 _ _ id, (hch i).2.1]
  have hσd1 : σ1.nat B.rd = d := by rw [F1.1 _ (show ¬ B.rE ≤ B.rd by omega), hσd]
  -- the initial position
  refine XV.seq (XV.init (Gc := tzGc d (ellPos d n)) hL hd (by omega) (by omega) (by omega) hrd haC hσd1 a1 a2 a25
    c1 eD1 eC1 hDs hC (by omega)) fun σ2 ⟨st2, d2, F2⟩ => ?_
  have k2 : ∀ k, (0 < k ∧ k < 14) ∨ (17 < k ∧ k < 40) → σ2.sc (B.o + k) = σ1.sc (B.o + k) := fun k hk =>
    F2.2.1 _ (show ¬ (B.o + k = B.o ∨ B.o + k = B.o + 14 ∨ B.o + k = B.o + 15 ∨ B.o + k = B.o + 16 ∨
      B.o + k = B.o + 17 ∨ B.o + 40 ≤ B.o + k) by omega)
  have j2 : ∀ k, k < 3 ∨ 6 ≤ k → σ2.nat (B.rE + k) = σ1.nat (B.rE + k) := fun k hk =>
    F2.1 _ (show ¬ (B.rE + 3 ≤ B.rE + k ∧ B.rE + k < B.rE + 6) by omega)
  have eC2 : ∀ i : Fin d, σ2.arr B.aC (i + 1) = ch i := fun i => by
    rw [F2.2.2.1 _ _ (show ¬ (B.aC = B.aW ∧ (i : ℕ) + 1 < d ∨ B.aC = B.aW + 1 ∧ (i : ℕ) + 1 < d * d) by omega),
      eC1 i]
  -- the stages
  refine XV.mono (XV.stages (X := ctxOf w n m A b) (n := n) (m := m) (A := A) (b := b) (Dc := Dc) (ch := ch)
    (E := triE d n s (frMhat A b).size) (mst := triMstQ (1 / 2) n) hL (fun _ => rfl) rfl (by omega) (by omega)
    (by omega) hrd haC (by rw [F2.1 _ (show ¬ (B.rE + 3 ≤ B.rd ∧ B.rd < B.rE + 6) by omega), hσd1])
    (by rw [← Nat.add_zero B.rE, j2 0 (by omega), Nat.add_zero, a1]) (by rw [j2 1 (by omega), a2])
    (by rw [j2 2 (by omega), a3]) (by rw [j2 12 (by omega), a12]) (by rw [j2 24 (by omega), a24])
    (by rw [j2 25 (by omega), a25]) (by rw [j2 26 (by omega), a26]) (by rw [j2 28 (by omega), a28])
    hka (by omega) hNa hsa hB1 hBa (by rw [k2 1 (by omega), c1]) (by rw [k2 2 (by omega), c2])
    (by rw [k2 3 (by omega), c3]) (by rw [k2 4 (by omega), c4]) (by rw [k2 5 (by omega), c5])
    (by rw [k2 6 (by omega), c6]) (by rw [k2 7 (by omega), c7]) (by rw [k2 8 (by omega), c8])
    (by rw [k2 9 (by omega), c9]) (by rw [k2 10 (by omega), c10]) (by rw [k2 11 (by omega), c11])
    (by rw [k2 12 (by omega), c12]) (by rw [k2 13 (by omega), c13]) (by rw [k2 35 (by omega), c35])
    st2 eC2 hDc0
    (fun t ht => (tri_bT hC hDs (by omega) ht.le).1) (fun t ht => (tri_bT hC hDs (by omega) ht.le).2)
    (fun t ht => tri_bD hDc0 hDcs (by omega) ht.le) (fun t ht => tri_bRB hDc0 hDcs hC (by omega) ht.le)
    (fun t ht => tri_hb hDc0 hDcs (by omega) ht.le) (by omega)
    (fun i => (hC i).trans (two_pow_le_two_pow (by omega))) (tri_bRA A b (by omega))
    (tri_bDC (by omega)).1 (tri_bDC (by omega)).2.1 (tri_bDC (by omega)).2.2.1 (tri_bDC (by omega)).2.2.2.1
    (tri_bDC (by omega)).2.2.2.2.1 (by omega) (tri_bDC (by omega)).2.2.2.2.2.1 (tri_bDC (by omega)).2.2.2.2.2.2
    hE) le_rfl ?_
  rintro σ3 ⟨st3, d3, F3⟩
  have hσ2 : σ2.draws = σ.draws := by rw [d2, d1]
  rw [hσ2] at st3 d3
  have hc : frameQ d n m A b = fun i => (ch i : ℚ) / Dc := funext fun i => ((hch i).2.2).symm
  have hpos : posQ d n m A b (fun j => w.cs (σ.draws + j)) =
      (fun i => ((tzPos n A b Dc ch (fun j => w.cs (σ.draws + j))).mu i : ℚ) /
          (tzPos n A b Dc ch (fun j => w.cs (σ.draws + j))).D,
        fun i l => ((tzPos n A b Dc ch (fun j => w.cs (σ.draws + j))).T i l : ℚ) /
          (tzPos n A b Dc ch (fun j => w.cs (σ.draws + j))).D) :=
    tzPos_eq hd n A b Dc hDc0 ch (frameQ d n m A b) hc _
  have hst : StAt σ3 B.o B.aW (tzGc d (ellPos d n)) (triMstQ (1 / 2) n)
      (tzPos n A b Dc ch (fun j => w.cs (σ.draws + j))) := st3
  obtain ⟨hD0, hDlt⟩ := stage_D_le n A b Dc ch
    (fun j k => w.cs (σ.draws + triLay (triMstQ (1 / 2) n) (triLQ d (ellPos d n)) (j, k))) s hDc0 hDcs
    (triMstQ (1 / 2) n)
  obtain ⟨hmu, hT⟩ := stage_entries_le n A b Dc ch
    (fun j k => w.cs (σ.draws + triLay (triMstQ (1 / 2) n) (triLQ d (ellPos d n)) (j, k))) s hC hDs
    (triMstQ (1 / 2) n)
  have hKD : s + 1 + triMstQ (1 / 2) n * tzGc d (ellPos d n) ≤ K := by
    have := Nat.mul_le_mul_left (triMstQ (1 / 2) n)
      (show tzGc d (ellPos d n) ≤ tzGc d (ellPos d n) + triLa (triSQ d) + d by omega)
    omega
  have hKE : (2 : ℤ) ^ (s + 1 + triMstQ (1 / 2) n * (tzGc d (ellPos d n) + triLa (triSQ d) + d)) < 2 ^ K :=
    pow_lt_pow_right₀ (by norm_num) hK
  refine ⟨⟨(tzPos n A b Dc ch (fun j => w.cs (σ.draws + j))).D, hD0, hDlt.trans_le (two_pow_le_two_pow hKD),
    hst.2.2.1, fun j => ⟨_, (hmu j).trans_lt hKE, hst.1 j, by rw [hpos]; rfl⟩,
    fun i j => ⟨_, (hT i j).trans_lt hKE, hst.2.1 i j, by rw [hpos]; rfl⟩⟩, d3, ?_⟩
  exact (F1.mono (fun _ h => h) (fun _ h => h) (fun _ _ h => h.elim)).trans
    ((F2.mono (fun y h => by omega) (fun j h => by omega) (fun b c h => by omega)).trans
      (F3.mono (fun y h => by unfold sgS at h; omega) (fun j h => by unfold ssN at h; omega) (fun _ _ h => h.1)))

end AdversarialBco.Bit.Transfer
