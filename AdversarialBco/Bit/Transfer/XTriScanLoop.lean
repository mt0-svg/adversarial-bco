/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriBox
public import AdversarialBco.Bit.Transfer.XTriScan
public import AdversarialBco.Bit.Transfer.XTriM
public import AdversarialBco.Conj1Bit.Sanity
public import AdversarialBco.Bit.Transfer.XFrameLem

@[expose] public section

/-!
# TRI-M, the rows of a stage and the scan on the machine

Row `k` of a stage (`xrowK`): an input row `k < m` cleared from its cells (`xinRow`), else the box row `±e_i` with its
right-hand side (`xbox`). The scan of `tzKeep` over the rows `k < m + 2d` (`xscanL`), and `A = T̂ᵀ row` (`xmatvecT`).
-/

open AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.Transfer AdversarialBco.Bit.TriM Matrix


theorem AdversarialBco.Bit.TriM.frAl_inp {d m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (k : Fin m)
    (j : Fin d) :
    (BitRAM.entry A b k j).num * ((∏ j' ∈ Finset.range (d + 1), ((BitRAM.entry A b k j').den : ℤ)) /
      ((BitRAM.entry A b k j).den : ℤ)) = frAl A b k j := by
  -- entry A b k j = A k j since j : Fin d
  have h_entry_j : BitRAM.entry A b k j = A k j := by
    dsimp [BitRAM.entry]
    simp [j.2]
  rw [h_entry_j]
  -- Expand frAl = clr (frDen A b k) (A k j) = (A k j).num * (((frDen A b k / (A k j).den : ℕ) : ℤ))
  dsimp [frAl, clr]
  -- Goal: (A k j).num * (P / ((A k j).den : ℤ)) = (A k j).num * (((frDen A b k / (A k j).den : ℕ) : ℤ))
  -- where P = ∏ j' ∈ range (d+1), ((entry A b k j').den : ℤ)
  -- First, prove P = (frDen A b k : ℤ)
  have hP : (∏ j' ∈ Finset.range (d + 1), ((BitRAM.entry A b k j').den : ℤ)) = (frDen A b k : ℤ) := by
    rw [Finset.prod_range_succ]
    -- Split into product over range d times the last term (j' = d)
    have hlast : (BitRAM.entry A b k d) = b k := by
      simp [BitRAM.entry]
    rw [hlast]
    -- Now: (∏ j' ∈ range d, ((entry A b k j').den : ℤ)) * ((b k).den : ℤ) = (frDen A b k : ℤ)
    have hfirst : (∏ j' ∈ Finset.range d, ((BitRAM.entry A b k j').den : ℤ)) = (∏ j : Fin d, ((A k j).den : ℤ)) := by
      rw [Finset.prod_fin_eq_prod_range (fun j : Fin d => ((A k j).den : ℤ))]
      refine Finset.prod_congr rfl fun i hi => ?_
      have hi_lt : i < d := Finset.mem_range.1 hi
      dsimp [BitRAM.entry]
      simp [hi_lt]
    rw [hfirst]
    -- Now: (∏ j : Fin d, ((A k j).den : ℤ)) * ((b k).den : ℤ) = (frDen A b k : ℤ)
    dsimp [frDen]
    simp
  rw [hP]


theorem AdversarialBco.Bit.TriM.frBe_inp {d m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (k : Fin m) :
    (BitRAM.entry A b k d).num * ((∏ j' ∈ Finset.range (d + 1), ((BitRAM.entry A b k j').den : ℤ)) /
      ((BitRAM.entry A b k d).den : ℤ)) = frBe A b k := by
  unfold frBe clr
  have h_entry_d : BitRAM.entry A b k d = b k := by
    unfold BitRAM.entry
    simp
  rw [h_entry_d]
  congr 1
  have h_prod : (∏ j' ∈ Finset.range (d + 1), ((BitRAM.entry A b k j').den : ℤ)) = ((frDen A b k : ℕ) : ℤ) := by
    unfold frDen
    rw [Finset.prod_range_succ]
    have h_last : ((BitRAM.entry A b k d).den : ℤ) = ((b k).den : ℤ) := by
      unfold BitRAM.entry
      simp
    rw [h_last]
    have h_first : (∏ j' ∈ Finset.range d, ((BitRAM.entry A b k j').den : ℤ)) = ((∏ j : Fin d, (A k j).den : ℕ) : ℤ) := by
      calc
        (∏ j' ∈ Finset.range d, ((BitRAM.entry A b k j').den : ℤ))
            = (∏ i : Fin d, ((BitRAM.entry A b k (i.val : ℕ)).den : ℤ)) := by
          simpa using (Fin.prod_univ_eq_prod_range (α := ℤ) (fun x => ((BitRAM.entry A b k x).den : ℤ)) d).symm
        _ = (∏ i : Fin d, ((A k i).den : ℤ)) := by
          refine Finset.prod_congr rfl (fun i _ => ?_)
          unfold BitRAM.entry
          simp [i.is_lt]
        _ = ((∏ j : Fin d, (A k j).den : ℕ) : ℤ) := by simp [Nat.cast_prod]
    rw [h_first]
    simp [Nat.cast_mul]
  rw [h_prod]
  rw [← Int.natCast_div]

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach

variable {d : ℕ}

/-! ## The rows of a stage by their index -/

section Rows

variable {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (ch : Fin d → ℤ) (e js : ℕ) (D : ℤ)

theorem tzRowA_in {k : ℕ} (hk : k < m) (hk' : k < m + (d + d)) : tzRowA A b ⟨k, hk'⟩ = frAl A b ⟨k, hk⟩ := by
  have : (⟨k, hk'⟩ : Fin (m + (d + d))) = Fin.castAdd (d + d) ⟨k, hk⟩ := rfl
  rw [this, tzRowA, Fin.append_left]

theorem tzRowB_in {k : ℕ} (hk : k < m) (hk' : k < m + (d + d)) :
    tzRowB A b ch e js D ⟨k, hk'⟩ = frBe A b ⟨k, hk⟩ * D := by
  have : (⟨k, hk'⟩ : Fin (m + (d + d))) = Fin.castAdd (d + d) ⟨k, hk⟩ := rfl
  rw [this, tzRowB, Fin.append_left]

/-- The entries of the input rows against `M̂`. -/
theorem entry_le (k : Fin m) (j : ℕ) :
    |(BitRAM.entry A b k j).num| ≤ (frMhat A b : ℤ) ∧ 1 ≤ ((BitRAM.entry A b k j).den : ℤ) ∧
      ((BitRAM.entry A b k j).den : ℤ) ≤ frMhat A b := by
  obtain ⟨-, hA, hb⟩ := frMhat_le A b
  have h1 : 1 ≤ ((BitRAM.entry A b k j).den : ℤ) := by exact_mod_cast (BitRAM.entry A b k j).den_pos
  unfold BitRAM.entry
  split_ifs with h
  · obtain ⟨h2, h3⟩ := hA k ⟨j, h⟩
    refine ⟨by rw [Int.abs_eq_natAbs]; exact_mod_cast h2, ?_, by exact_mod_cast h3⟩
    simpa [BitRAM.entry, h] using h1
  · obtain ⟨h2, h3⟩ := hb k
    refine ⟨by rw [Int.abs_eq_natAbs]; exact_mod_cast h2, ?_, by exact_mod_cast h3⟩
    simpa [BitRAM.entry, h] using h1


theorem tzRowA_bp' {k : ℕ} (hk' : k < m + (d + d)) (hkm : m ≤ k) (hi : k - m < d) :
    tzRowA A b ⟨k, hk'⟩ = Pi.single ⟨k - m, hi⟩ 1 := by
  have : (⟨k, hk'⟩ : Fin (m + (d + d))) = Fin.natAdd m (Fin.castAdd d ⟨k - m, hi⟩) := Fin.ext (by simp; omega)
  rw [this, tzRowA, Fin.append_right, Fin.append_left]

theorem tzRowB_bp' {k : ℕ} (hk' : k < m + (d + d)) (hkm : m ≤ k) (hi : k - m < d) :
    tzRowB A b ch e js D ⟨k, hk'⟩ = ch ⟨k - m, hi⟩ * 2 ^ e + 2 ^ js * D := by
  have : (⟨k, hk'⟩ : Fin (m + (d + d))) = Fin.natAdd m (Fin.castAdd d ⟨k - m, hi⟩) := Fin.ext (by simp; omega)
  rw [this, tzRowB, Fin.append_right, Fin.append_left]

theorem tzRowA_bm' {k : ℕ} (hk' : k < m + (d + d)) (hkm : m + d ≤ k) (hi : k - m - d < d) :
    tzRowA A b ⟨k, hk'⟩ = -Pi.single ⟨k - m - d, hi⟩ 1 := by
  have : (⟨k, hk'⟩ : Fin (m + (d + d))) = Fin.natAdd m (Fin.natAdd d ⟨k - m - d, hi⟩) := Fin.ext (by simp; omega)
  rw [this, tzRowA, Fin.append_right, Fin.append_right]

theorem tzRowB_bm' {k : ℕ} (hk' : k < m + (d + d)) (hkm : m + d ≤ k) (hi : k - m - d < d) :
    tzRowB A b ch e js D ⟨k, hk'⟩ = 2 ^ js * D - ch ⟨k - m - d, hi⟩ * 2 ^ e := by
  have : (⟨k, hk'⟩ : Fin (m + (d + d))) = Fin.natAdd m (Fin.natAdd d ⟨k - m - d, hi⟩) := Fin.ext (by simp; omega)
  rw [this, tzRowB, Fin.append_right, Fin.append_right]

end Rows

/-- `trimnodup` closing the disequalities from the context. -/
macro "trimnodup'" : tactic =>
  `(tactic| ((simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    not_false_eq_true, and_true]; repeat' constructor) <;> trimne))

/-! ## Row `k` of a stage -/

/-- Row `k` into the array `aRow` (cells `0, ..., d - 1`) and its right-hand side at the stage position into the slot
`sB`: the input row `k < m` from its cells (`sDn` holds the stage denominator `D`), else the box row `e_{k-m}` (sign
slot `sSg := 1`), else `-e_{k-m-d}` (`sSg := -1`); `sPe` holds `2^e`, `s2jD` holds `2^j D`, `aC` the frame centre. -/
def xrowK (L : Layout) (sD sT sN sQ sB sDn aRow aC sZ sSg sPe s2jD nI nT nj nd nd1 nk nm ni nl none : ℕ) : XCmd :=
  .ifN nk nm (xinRow L sD sT sN sQ sB sDn aRow nI nT nj nd nd1 nk none)
    (.seq (.prim (.frag (.nsub ni nk nm)))
      (.ifN ni nd
        (.seq (toX (VL.sconst L sSg 1)) (xbox L aRow aC sZ sSg sPe s2jD sT sB ni nl nT nd none))
        (.seq (.prim (.frag (.nsub ni ni nd))) (.seq (toX (VL.sconst L sSg (-1)))
          (xbox L aRow aC sZ sSg sPe s2jD sT sB ni nl nT nd none)))))

/-- The units of `xbox`. -/
abbrev boxK (d : ℕ) : ℕ := d * (2 + 3) + 3 + (2 + (1 + (2 + (1 + (1 + 1)))))

set_option maxHeartbeats 4000000 in
theorem XV.rowK {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {sD sT sN sQ sB sDn aRow aC sZ sSg sPe s2jD nI nT nj nd nd1 nk nm ni nl none k e js E n m : ℕ}
    {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {ch : Fin d → ℤ} {D : ℤ}
    (hXi : ∀ c : ℕ, X.inp c = BitRAM.inputMem d n m A b c) (hXo : X.off = 3 + 2 * (d + 1) * m) (hk : k < m + (d + d))
    (hsD : sD < L.NS) (hsT : sT < L.NS) (hsN : sN < L.NS) (hsQ : sQ < L.NS) (hsB : sB < L.NS)
    (hsDn : sDn < L.NS) (hsZ : sZ < L.NS) (hsS : sSg < L.NS) (hsP : sPe < L.NS) (hs2 : s2jD < L.NS)
    (hss : [sD, sT, sN, sQ, sB, sDn, sZ, sSg, sPe, s2jD].Nodup) (hR : aRow < L.NA) (hC : aC < L.NA)
    (hRC : aRow ≠ aC) (hnI : nI < L.NN) (hnT : nT < L.NN) (hnj : nj < L.NN) (hnd : nd < L.NN)
    (hn1 : nd1 < L.NN) (hnk : nk < L.NN) (hnm : nm < L.NN) (hni : ni < L.NN) (hnl : nl < L.NN)
    (hno : none < L.NN) (hne : [nI, nT, nj, nd, nd1, nk, nm, ni, nl, none].Nodup)
    (hσd : σ.nat nd = d) (hσd1 : σ.nat nd1 = d + 1) (hσk : σ.nat nk = k) (hσm : σ.nat nm = m)
    (hσ1 : σ.nat none = 1) (eDn : σ.sc sDn = D) (eZ : σ.sc sZ = 0) (eP : σ.sc sPe = ((2 ^ e : ℤ) : ℝ))
    (e2 : σ.sc s2jD = ((2 ^ js * D : ℤ) : ℝ)) (eC : ∀ i : Fin d, σ.arr aC (i + 1) = ch i)
    (hka : 4 + 2 * ((d + 1) * (m + 1)) < 2 ^ ℓa) (hda : d * d + d < 2 ^ ℓa) (hma : m + (d + d) < 2 ^ ℓa)
    (hD1 : 1 ≤ D) (bC : ∀ i, |ch i| ≤ 2 ^ E) (bP : (2 : ℤ) ^ e ≤ 2 ^ E) (bQ : |2 ^ js * D| ≤ 2 ^ E)
    (hE : 2 * E + 2 < ℓ) (hb : (frMhat A b : ℤ) ^ (d + 2) * D < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xrowK L sD sT sN sQ sB sDn aRow aC sZ sSg sPe s2jD nI nT nj nd nd1 nk nm ni nl none) σ
      (18 * d + 29)
      (fun σ' => (∀ l : Fin d, σ'.arr aRow l = tzRowA A b ⟨k, hk⟩ l) ∧ σ'.sc sB = tzRowB A b ch e js D ⟨k, hk⟩ ∧
        σ'.draws = σ.draws ∧
        FrameA (fun y => y = sD ∨ y = sT ∨ y = sN ∨ y = sQ ∨ y = sB ∨ y = sSg)
          (fun j => j = nI ∨ j = nT ∨ j = nj ∨ j = ni ∨ j = nl) (fun a k' => a = aRow ∧ k' < d) σ σ') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hss hne
  casesm* _ ∧ _
  obtain ⟨hM1, -, -⟩ := frMhat_le A b
  have hM1' : (1 : ℤ) ≤ frMhat A b := by exact_mod_cast hM1
  by_cases hkm : k < m
  · refine XV.mono (XV.ifN_t hL hnk hnm (by rw [hσk]; omega) (by rw [hσm]; omega) (by rw [hσk, hσm]; exact hkm)
      (XV.inRow hL (k := k) (Mh := frMhat A b) (D := D) (Nm := fun j => (BitRAM.entry A b ⟨k, hkm⟩ j).num)
        (Dn := fun j => (BitRAM.entry A b ⟨k, hkm⟩ j).den) hsD hsT hsN hsQ hsB hsDn (by trimnodup') hR hnI hnT
        hnj hnd hn1 hnk hno (by trimnodup') hσd hσd1 hσk hσ1 eDn ?_ ?_ hda ?_ ?_ hD1 hM1'
        (fun j _ => (entry_le A b _ j).1) (fun j _ => (entry_le A b _ j).2) hb)) (by omega) ?_
    · rw [hXo]
      have := Nat.mul_le_mul_left (d + 1) (show k + 1 ≤ m by omega)
      nlinarith
    · have := Nat.mul_le_mul_left (d + 1) (show k + 1 ≤ m + 1 by omega)
      omega
    · intro j hj; rw [hXi]; exact BitRAM.Conj1BitSanity.inputMem_num (n := n) A b ⟨k, hkm⟩ j hj
    · intro j hj; rw [hXi]; exact BitRAM.Conj1BitSanity.inputMem_den (n := n) A b ⟨k, hkm⟩ j hj
    · rintro σ' ⟨hrow, hsB', hdr, hF⟩
      refine ⟨fun l => ?_, ?_, hdr, hF.mono (fun _ h => ?_) (fun _ h => ?_) (fun _ _ h => h)⟩
      · rw [hrow l l.2, tzRowA_in A b hkm hk, ← frAl_inp]
      · rw [hsB', tzRowB_in A b ch e js D hkm hk, ← frBe_inp]
      · rcases h with h | h | h | h | h <;> simp [h]
      · rcases h with h | h | h <;> simp [h]
  · have hkm' : m ≤ k := by omega
    refine XV.mono (XV.ifN_f (K := 1 + ((1 + (1 + boxK d)) + 2)) hL hnk hnm (by rw [hσk]; omega)
      (by rw [hσm]; omega) (by rw [hσk, hσm]; exact hkm) ?_) (by simp only [boxK]; omega) (fun _ h => h)
    refine XV.seq (XV.nsub hL hni hnk hnm (by rw [hσk]; omega) (by rw [hσm]; omega)
      (by rw [hσk, hσm]; exact hkm')) fun σ1 e1 => ?_
    subst e1
    have i1 : (σ.setNat ni (σ.nat nk - σ.nat nm)).nat ni = k - m := by rw [nat_setNat_eq, hσk, hσm]
    have F1 : FrameA (fun y => y = sD ∨ y = sT ∨ y = sN ∨ y = sQ ∨ y = sB ∨ y = sSg)
        (fun j => j = nI ∨ j = nT ∨ j = nj ∨ j = ni ∨ j = nl) (fun a k' => a = aRow ∧ k' < d) σ
        (σ.setNat ni (σ.nat nk - σ.nat nm)) :=
      (FrameA.refl (fun y => y = sD ∨ y = sT ∨ y = sN ∨ y = sQ ∨ y = sB ∨ y = sSg)
        (fun j => j = nI ∨ j = nT ∨ j = nj ∨ j = ni ∨ j = nl) (fun a k' => a = aRow ∧ k' < d) σ).setNat
        (by simp) _
    have n1 : ∀ j, j ≠ ni → (σ.setNat ni (σ.nat nk - σ.nat nm)).nat j = σ.nat j := fun j h => nat_setNat_ne _ h
    have s1 : ∀ y, (σ.setNat ni (σ.nat nk - σ.nat nm)).sc y = σ.sc y := fun y => by rw [Env.setNat_sc]
    have a1 : (σ.setNat ni (σ.nat nk - σ.nat nm)).arr = σ.arr := by rw [Env.setNat_arr]
    have dr1 : (σ.setNat ni (σ.nat nk - σ.nat nm)).draws = σ.draws := by rw [Env.setNat_draws]
    generalize σ.setNat ni (σ.nat nk - σ.nat nm) = σ1 at i1 F1 n1 s1 a1 dr1
    have d1 : σ1.nat nd = d := by rw [n1 _ (by trimne), hσd]
    have o1 : σ1.nat none = 1 := by rw [n1 _ (by trimne), hσ1]
    have hPe : (0 : ℤ) < 2 ^ e := by positivity
    have bP' : |(2 : ℤ) ^ e| ≤ 2 ^ E := by rw [abs_of_pos hPe]; exact bP
    have h1l : |((1 : ℚ) : ℝ)| < 2 ^ ℓ := by
      rw [Rat.cast_one, abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
    have h1l' : |((-1 : ℚ) : ℝ)| < 2 ^ ℓ := by
      rw [Rat.cast_neg, Rat.cast_one, abs_neg, abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
    -- the closing step, common to the two box rows
    have close : ∀ (i : ℕ) (hi : i < d) (sg : ℤ) (σ2 σ3 : Env d), σ2.arr = σ1.arr → σ2.draws = σ1.draws →
        FrameA (fun y => y = sD ∨ y = sT ∨ y = sN ∨ y = sQ ∨ y = sB ∨ y = sSg)
          (fun j => j = nI ∨ j = nT ∨ j = nj ∨ j = ni ∨ j = nl) (fun a k' => a = aRow ∧ k' < d) σ1 σ2 →
        (tzRowA A b ⟨k, hk⟩ = sg • Pi.single ⟨i, hi⟩ 1) →
        (tzRowB A b ch e js D ⟨k, hk⟩ = 2 ^ js * D + sg * (ch ⟨i, hi⟩ * 2 ^ e)) →
        ((∀ l < d, σ3.arr aRow l = if l = i then (sg : ℝ) else 0) ∧
          σ3.sc sB = ((2 ^ js * D + sg * (ch ⟨i, hi⟩ * 2 ^ e) : ℤ) : ℝ) ∧ σ3.draws = σ2.draws ∧
          FrameA (fun y => y = sT ∨ y = sB) (fun j => j = nl ∨ j = nT) (fun a k => a = aRow ∧ k < d) σ2 σ3) →
        (∀ l : Fin d, σ3.arr aRow l = tzRowA A b ⟨k, hk⟩ l) ∧ σ3.sc sB = tzRowB A b ch e js D ⟨k, hk⟩ ∧
          σ3.draws = σ.draws ∧
          FrameA (fun y => y = sD ∨ y = sT ∨ y = sN ∨ y = sQ ∨ y = sB ∨ y = sSg)
            (fun j => j = nI ∨ j = nT ∨ j = nj ∨ j = ni ∨ j = nl) (fun a k' => a = aRow ∧ k' < d) σ σ3 := by
      intro i hi sg σ2 σ3 _ hd2 F2 hA hB ⟨hrow, hsB', hd3, F3⟩
      refine ⟨fun l => ?_, by rw [hsB', hB], by rw [hd3, hd2, dr1], ?_⟩
      · rw [hrow l l.2, hA, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
        by_cases h : (l : ℕ) = i
        · simp [h, Fin.ext_iff]
        · simp [h, Fin.ext_iff]
      · exact F1.trans (F2.trans (F3.mono (fun _ h => by rcases h with h | h <;> simp [h])
          (fun _ h => by rcases h with h | h <;> simp [h]) (fun _ _ h => h)))
    by_cases hkd : k - m < d
    · refine XV.mono (XV.ifN_t (K := 1 + boxK d) hL hni hnd (by rw [i1]; omega) (by rw [d1]; omega)
        (by rw [i1, d1]; exact hkd) ?_) (by omega) (fun _ h => h)
      refine XV.seq (XV.sconst hL hsS 1 rfl h1l) fun σ2 e2' => ?_
      subst e2'
      refine XV.mono (XV.box hL (i := k - m) (sg := 1) (Pe := 2 ^ e) (Q := 2 ^ js * D) (ch := ch ⟨k - m, hkd⟩)
        (E := E) hR hC hRC hsZ hsS hsP hs2 hsT hsB (by trimnodup') hni hnl hnT hnd hno (by trimnodup') hkd
        (by rw [Env.setSc_nat, i1]) (by rw [Env.setSc_nat, d1]) (by rw [Env.setSc_nat, o1]) hda
        (by rw [sc_setSc_ne _ (by trimne), s1, eZ]) (by rw [sc_setSc_eq]; simp)
        (by rw [sc_setSc_ne _ (by trimne), s1, eP]) (by rw [sc_setSc_ne _ (by trimne), s1, e2])
        (by rw [Env.setSc_arr, a1]; exact eC ⟨k - m, hkd⟩) (by norm_num) (bC _) bP' bQ hE) le_rfl ?_
      refine fun σ3 h3 => close (k - m) hkd 1 _ σ3 (by rw [Env.setSc_arr]) (by rw [Env.setSc_draws])
        ((FrameA.refl _ _ _ σ1).setSc (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) _) ?_ ?_ h3
      · rw [tzRowA_bp' A b hk hkm' hkd, one_smul]
      · rw [tzRowB_bp' A b ch e js D hk hkm' hkd]; ring
    · have hkd' : k - m - d < d := by omega
      refine XV.ifN_f (K := 1 + (1 + boxK d)) hL hni hnd (by rw [i1]; omega) (by rw [d1]; omega)
        (by rw [i1, d1]; exact hkd) ?_
      refine XV.seq (XV.nsub hL hni hni hnd (by rw [i1]; omega) (by rw [d1]; omega) (by rw [i1, d1]; omega))
        fun σ2 e2' => ?_
      subst e2'
      have i2 : (σ1.setNat ni (σ1.nat ni - σ1.nat nd)).nat ni = k - m - d := by rw [nat_setNat_eq, i1, d1]
      refine XV.seq (XV.sconst hL hsS (-1) rfl h1l') fun σ3 e3' => ?_
      subst e3'
      refine XV.mono (XV.box hL (i := k - m - d) (sg := -1) (Pe := 2 ^ e) (Q := 2 ^ js * D)
        (ch := ch ⟨k - m - d, hkd'⟩) (E := E) hR hC hRC hsZ hsS hsP hs2 hsT hsB (by trimnodup') hni hnl hnT hnd
        hno (by trimnodup') hkd' (by rw [Env.setSc_nat, i2])
        (by rw [Env.setSc_nat, nat_setNat_ne _ (by trimne), d1])
        (by rw [Env.setSc_nat, nat_setNat_ne _ (by trimne), o1]) hda
        (by rw [sc_setSc_ne _ (by trimne), Env.setNat_sc, s1, eZ]) (by rw [sc_setSc_eq]; simp)
        (by rw [sc_setSc_ne _ (by trimne), Env.setNat_sc, s1, eP])
        (by rw [sc_setSc_ne _ (by trimne), Env.setNat_sc, s1, e2])
        (by rw [Env.setSc_arr, Env.setNat_arr, a1]; exact eC ⟨k - m - d, hkd'⟩) (by norm_num) (bC _) bP' bQ hE)
        le_rfl ?_
      refine fun σ4 h4 => close (k - m - d) hkd' (-1) _ σ4 (by rw [Env.setSc_arr, Env.setNat_arr])
        (by rw [Env.setSc_draws, Env.setNat_draws])
        (((FrameA.refl _ _ _ σ1).setNat (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _).setSc
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) _) ?_ ?_ h4
      · rw [tzRowA_bm' A b hk (by omega) hkd', neg_one_smul]
      · rw [tzRowB_bm' A b ch e js D hk (by omega) hkd']; ring

/-! ## The scan of the rows -/

theorem dot_abs_le {x y : Fin d → ℤ} {E : ℕ} (bx : ∀ l, |x l| ≤ 2 ^ E) (by' : ∀ l, |y l| ≤ 2 ^ E) :
    |x ⬝ᵥ y| ≤ 2 ^ (2 * E + d) := by
  have h1 : |x ⬝ᵥ y| ≤ d * 2 ^ (2 * E) := by
    unfold dotProduct
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ l ∈ (Finset.univ : Finset (Fin d)), |x l * y l| ≤ 2 ^ (2 * E) := fun l _ => by
      rw [two_mul]; exact absI_mul_le (bx l) (by' l)
    refine (Finset.sum_le_sum this).trans ?_
    simp
  have h2 : (d : ℤ) ≤ 2 ^ d := by exact_mod_cast (Nat.lt_two_pow_self).le
  calc |x ⬝ᵥ y| ≤ d * 2 ^ (2 * E) := h1
    _ ≤ 2 ^ d * 2 ^ (2 * E) := by gcongr
    _ = 2 ^ (2 * E + d) := by rw [pow_add]; ring

/-- The scan of the rows `k < M`: `(bn, bd, bb, row) := scan0`, then for each `k` the command `row` puts row `k` into
`aRow` and its right-hand side into `sB`, `N_k := aRow ⬝ ŵ` (`aW`), `β̃_k := sB - aRow ⬝ μ̂` (`aMu`), and the keep;
scratch from the slot `t`. -/
def xscanL (L : Layout) (row : XCmd) (sZ sOne sMOne sB sN sTd sBt sQN sQB sSg sBn sBd sBb sL sR sT t aRow aK aW aMu
    nk nM nr nq nd none nl : ℕ) : XCmd :=
  .seq (toX (VL.sop2 L .add sBn sZ sZ)) (.seq (toX (VL.sop2 L .add sBd sOne sZ))
    (.seq (toX (VL.sop2 L .add sBb sOne sZ)) (.seq (xzero L aK sZ nl nd none)
      (xforN nk nM none (.seq row (.seq (xdot L sZ sN t aRow aW nr nq nd none)
        (.seq (xdot L sZ sTd t aRow aMu nr nq nd none) (.seq (toX (VL.sop2 L .sub sBt sB sTd))
          (.seq (xqn L sZ sOne sMOne sN sBt sQN sQB sSg)
            (xtkeep L sZ sBn sBd sBb sQN sQB sSg sL sR sT aK aRow nl nd none))))))))))

/-- The units of one row of `xscanL` after the row command. -/
abbrev scanBK (d : ℕ) : ℕ := d * 10 + 5 + (d * 10 + 5 + (1 + (7 + (8 * d + 9))))

/-- A slot outside a frame of the form `y = a ∨ t ≤ y`. -/
theorem frS1 {y a t : ℕ} (h1 : y ≠ a) (h2 : y < t) : ¬ (y = a ∨ t ≤ y) := by omega

set_option maxHeartbeats 8000000 in
/-- The rule of `xscanL`: the state of the scan of the rows `k < M` with `N_k = a_k ⬝ ŵ`, `β̃_k = b_k - a_k ⬝ μ̂`. The
row command is given by its rule on every environment reached by the loop. -/
theorem XV.scanL {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {row : XCmd}
    {sZ sOne sMOne sB sN sTd sBt sQN sQB sSg sBn sBd sBb sL sR sT t aRow aK aW aMu nk nM nr nq nd none nl M Kr
      E : ℕ}
    {Ss Ns Srow Nrow : ℕ → Prop} {As Arow : ℕ → ℕ → Prop} {ra : ℕ → Fin d → ℤ} {rb : ℕ → ℤ} {w mu : Fin d → ℤ}
    (h0 : sZ < t) (h1 : sOne < t) (h2 : sMOne < t) (h3 : sB < t) (h4 : sN < t) (h5 : sTd < t) (h6 : sBt < t)
    (h7 : sQN < t) (h8 : sQB < t) (h9 : sSg < t) (h10 : sBn < t) (h11 : sBd < t) (h12 : sBb < t) (h13 : sL < t)
    (h14 : sR < t) (h15 : sT < t) (hS : t + 3 ≤ L.NS)
    (hss : [sZ, sOne, sMOne, sB, sN, sTd, sBt, sQN, sQB, sSg, sBn, sBd, sBb, sL, sR, sT].Nodup)
    (hRw : aRow < L.NA) (hK : aK < L.NA) (hW : aW < L.NA) (hMu : aMu < L.NA) (hKR : aK ≠ aRow)
    (hnk : nk < L.NN) (hnM : nM < L.NN) (hnr : nr < L.NN) (hnq : nq < L.NN) (hnd : nd < L.NN) (hno : none < L.NN)
    (hnl : nl < L.NN) (hne : [nk, nM, nr, nq, nd, none, nl].Nodup)
    (hσd : σ.nat nd = d) (hσ1 : σ.nat none = 1) (hσM : σ.nat nM = M) (hda : d * d + d < 2 ^ ℓa)
    (hMa : M < 2 ^ ℓa) (eZ : σ.sc sZ = 0) (eO : σ.sc sOne = 1) (eM : σ.sc sMOne = -1)
    (eW : ∀ l : Fin d, σ.arr aW l = w l) (eMu : ∀ l : Fin d, σ.arr aMu l = mu l)
    (hSs : ∀ y, (y = sB ∨ y = sN ∨ y = sTd ∨ y = sBt ∨ y = sQN ∨ y = sQB ∨ y = sSg ∨ y = sBn ∨ y = sBd ∨ y = sBb ∨
      y = sL ∨ y = sR ∨ y = sT ∨ t ≤ y) → Ss y) (hSrow : ∀ y, Srow y → Ss y)
    (hNs : ∀ j, (j = nk ∨ j = nr ∨ j = nq ∨ j = nl) → Ns j) (hNrow : ∀ j, Nrow j → Ns j)
    (hAs : ∀ a k, (a = aRow ∧ k < d ∨ a = aK ∧ k < d) → As a k) (hArow : ∀ a k, Arow a k → As a k)
    (cS : ¬ Ss sZ ∧ ¬ Ss sOne ∧ ¬ Ss sMOne) (cN : ¬ Ns nd ∧ ¬ Ns none ∧ ¬ Ns nM)
    (cA : ∀ l, ¬ As aW l ∧ ¬ As aMu l)
    (cRow : ¬ Srow sBn ∧ ¬ Srow sBd ∧ ¬ Srow sBb ∧ ¬ Nrow nk ∧ ∀ l, ¬ Arow aK l)
    (hrow : ∀ k < M, ∀ σ' : Env d, FrameA Ss Ns As σ σ' → σ'.draws = σ.draws → σ'.nat nk = k →
      XRunsB L X ℓa ℓ row σ' Kr (fun σ'' => (∀ l : Fin d, σ''.arr aRow l = ra k l) ∧ σ''.sc sB = rb k ∧
        σ''.draws = σ'.draws ∧ FrameA Srow Nrow Arow σ' σ''))
    (bR : ∀ k < M, ∀ l, |ra k l| ≤ 2 ^ E) (bB : ∀ k < M, |rb k| ≤ 2 ^ E) (bW : ∀ l, |w l| ≤ 2 ^ E)
    (bMu : ∀ l, |mu l| ≤ 2 ^ E) (hE : 4 * E + 2 * d + 4 < ℓ) :
    XRunsB L X ℓa ℓ (xscanL L row sZ sOne sMOne sB sN sTd sBt sQN sQB sSg sBn sBd sBb sL sR sT t aRow aK aW aMu
        nk nM nr nq nd none nl) σ
      (1 + (1 + (1 + (d * (2 + 3) + 3 + (M * (Kr + scanBK d + 3) + 3)))))
      (fun σ' => σ'.sc sBn = (scan (fun k => ra k ⬝ᵥ w) (fun k => rb k - ra k ⬝ᵥ mu) ra M).bn ∧
        σ'.sc sBd = (scan (fun k => ra k ⬝ᵥ w) (fun k => rb k - ra k ⬝ᵥ mu) ra M).bd ∧
        σ'.sc sBb = (scan (fun k => ra k ⬝ᵥ w) (fun k => rb k - ra k ⬝ᵥ mu) ra M).bb ∧
        (∀ l : Fin d, σ'.arr aK l = (scan (fun k => ra k ⬝ᵥ w) (fun k => rb k - ra k ⬝ᵥ mu) ra M).row l) ∧
        σ'.draws = σ.draws ∧ FrameA Ss Ns As σ σ') := by
  obtain ⟨cZ, cO, cM⟩ := cS
  obtain ⟨cd, c1, cMM⟩ := cN
  obtain ⟨rBn, rBd, rBb, rnk, rK⟩ := cRow
  have hNS : ∀ y, y < t → y < L.NS := fun y h => by omega
  have h2E : 2 * E < ℓ := by omega
  have hE1 : E ≤ 2 * E + d + 1 := by omega
  have hE2 : 2 * E + d ≤ 2 * E + d + 1 := by omega
  have hE3 : 2 * (2 * E + d + 1) < ℓ := by omega
  have cR : ∀ z : ℤ, |z| < 2 ^ ℓ → |(z : ℝ)| < 2 ^ ℓ := fun z h => by
    rw [← Int.cast_abs]; exact_mod_cast h
  have hE' : ∀ a, a ≤ 2 * E + d + 1 → (2 : ℤ) ^ a < 2 ^ ℓ := fun a ha =>
    pow_lt_pow_right₀ (by norm_num) (by omega)
  have hdl : d * 2 ^ (2 * E) < 2 ^ ℓ := by
    have h2 : d < 2 ^ d := Nat.lt_two_pow_self
    calc d * 2 ^ (2 * E) ≤ 2 ^ d * 2 ^ (2 * E) := Nat.mul_le_mul_right _ h2.le
      _ = 2 ^ (2 * E + d) := by rw [← pow_add]; ring_nf
      _ < 2 ^ ℓ := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h1ℓ : (1 : ℤ) < 2 ^ ℓ := one_lt_pow₀ (by norm_num) (by omega)
  have hMk : ∀ k, k < M → k + 1 ≤ M := fun k h => h
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hss hne
  casesm* _ ∧ _
  generalize hNd : (fun k => ra k ⬝ᵥ w) = N
  generalize hBd : (fun k => rb k - ra k ⬝ᵥ mu) = B
  have bN : ∀ k < M, |N k| ≤ 2 ^ (2 * E + d + 1) := fun k hk => by
    rw [← hNd]
    exact (dot_abs_le (bR k hk) bW).trans (pow_le_pow_right₀ (by norm_num) hE2)
  have bBk : ∀ k < M, |B k| ≤ 2 ^ (2 * E + d + 1) := fun k hk => by
    rw [← hBd]
    have := dot_abs_le (bR k hk) bMu
    have hb := bB k hk
    have h1 : (2 : ℤ) ^ E ≤ 2 ^ (2 * E + d) := pow_le_pow_right₀ (by norm_num) (by omega)
    calc |rb k - ra k ⬝ᵥ mu| ≤ |rb k| + |ra k ⬝ᵥ mu| := abs_sub _ _
      _ ≤ 2 ^ (2 * E + d) + 2 ^ (2 * E + d) := by linarith
      _ = 2 ^ (2 * E + d + 1) := by ring
  have h1l : |((1 : ℤ) : ℝ)| < 2 ^ ℓ := cR 1 (by rw [abs_one]; exact h1ℓ)
  have h0l : |(0 : ℝ)| < 2 ^ ℓ := by rw [abs_zero]; positivity
  -- the start of the scan
  refine XV.seq (XV.sop2 hL (x := sBn) (a := sZ) (b := sZ) (hNS _ h10) (hNS _ h0) (hNS _ h0) .add
    (by intro h; cases h) (by rw [eZ]; exact h0l) (by rw [eZ]; exact h0l)
    (by simp only [RealRAM.Op2.eval, eZ, add_zero]; exact h0l)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.sop2 hL (x := sBd) (a := sOne) (b := sZ) (hNS _ h11) (hNS _ h1) (hNS _ h0) .add
    (by intro h; cases h) (by rw [sc_setSc_ne _ (by trimne), eO]; exact_mod_cast h1l)
    (by rw [sc_setSc_ne _ (by trimne), eZ]; exact h0l)
    (by simp only [RealRAM.Op2.eval]; rw [sc_setSc_ne _ (by trimne), sc_setSc_ne _ (by trimne), eO, eZ, add_zero];
        exact_mod_cast h1l)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.sop2 hL (x := sBb) (a := sOne) (b := sZ) (hNS _ h12) (hNS _ h1) (hNS _ h0) .add
    (by intro h; cases h) (by trimenv'; rw [eO]; exact_mod_cast h1l) (by trimenv'; rw [eZ]; exact h0l)
    (by simp only [RealRAM.Op2.eval]; trimenv'; rw [eO, eZ, add_zero]; exact_mod_cast h1l)) fun σ3 e3 => ?_
  subst e3
  generalize hσ3 : ((σ.setSc sBn (RealRAM.Op2.add.eval (σ.sc sZ) (σ.sc sZ))).setSc sBd
      (RealRAM.Op2.add.eval ((σ.setSc sBn (RealRAM.Op2.add.eval (σ.sc sZ) (σ.sc sZ))).sc sOne)
        ((σ.setSc sBn (RealRAM.Op2.add.eval (σ.sc sZ) (σ.sc sZ))).sc sZ))).setSc sBb
      (RealRAM.Op2.add.eval (((σ.setSc sBn (RealRAM.Op2.add.eval (σ.sc sZ) (σ.sc sZ))).setSc sBd
        (RealRAM.Op2.add.eval ((σ.setSc sBn (RealRAM.Op2.add.eval (σ.sc sZ) (σ.sc sZ))).sc sOne)
          ((σ.setSc sBn (RealRAM.Op2.add.eval (σ.sc sZ) (σ.sc sZ))).sc sZ))).sc sOne)
        (((σ.setSc sBn (RealRAM.Op2.add.eval (σ.sc sZ) (σ.sc sZ))).setSc sBd
          (RealRAM.Op2.add.eval ((σ.setSc sBn (RealRAM.Op2.add.eval (σ.sc sZ) (σ.sc sZ))).sc sOne)
            ((σ.setSc sBn (RealRAM.Op2.add.eval (σ.sc sZ) (σ.sc sZ))).sc sZ))).sc sZ)) = σ3
  have v3 : σ3.sc sBn = 0 ∧ σ3.sc sBd = 1 ∧ σ3.sc sBb = 1 ∧ σ3.nat = σ.nat ∧ σ3.arr = σ.arr ∧
      σ3.draws = σ.draws ∧ FrameA Ss Ns As σ σ3 := by
    rw [← hσ3]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · trimenv'; simp only [RealRAM.Op2.eval, eZ, add_zero]
    · trimenv'; simp only [RealRAM.Op2.eval, eZ, eO, add_zero]
    · trimenv'; simp only [RealRAM.Op2.eval, eZ, eO, add_zero]
    · simp only [Env.setSc_nat]
    · simp only [Env.setSc_arr]
    · simp only [Env.setSc_draws]
    · exact (((FrameA.refl Ss Ns As σ).setSc (hSs _ (by simp)) _).setSc (hSs _ (by simp)) _).setSc
        (hSs _ (by simp)) _
  obtain ⟨v3n, v3d, v3b, n3, a3, dr3, F3⟩ := v3
  refine XV.seq (XV.zero hL hK (hNS _ h0) hnl hnd hno (by trimnodup') (by rw [n3, hσd]) (by rw [n3, hσ1]) hda
    (by rw [F3.2.1 _ cZ, eZ])) fun σ4 h4 => ?_
  obtain ⟨z4, dr4, F4⟩ := h4
  have F4' : FrameA Ss Ns As σ σ4 :=
    F3.trans (F4.mono (fun _ h => h.elim) (fun j h => hNs j (by simp [h])) (fun a k h => hAs a k (Or.inr h)))
  have n4 : ∀ j, j ≠ nl → σ4.nat j = σ.nat j := fun j h => by rw [F4.1 j h, n3]
  let J : ℕ → Env d → Prop := fun k σ' => σ'.draws = σ.draws ∧ FrameA Ss Ns As σ σ' ∧
    σ'.sc sBn = (scan N B ra k).bn ∧ σ'.sc sBd = (scan N B ra k).bd ∧ σ'.sc sBb = (scan N B ra k).bb ∧
    ∀ l : Fin d, σ'.arr aK l = (scan N B ra k).row l
  refine XV.mono (XV.forN hL hnk hnM hno (by trimne) (by trimne) M (Kr + scanBK d) hMa J σ4
    (by rw [n4 _ (by trimne), hσM]) (by rw [n4 _ (by trimne), hσ1]) ⟨by rw [Env.setNat_draws, dr4, dr3],
      F4'.setNat (hNs _ (Or.inl rfl)) _, by rw [Env.setNat_sc, F4.2.1 _ not_false, v3n]; simp [scan, scan0],
      by rw [Env.setNat_sc, F4.2.1 _ not_false, v3d]; simp [scan, scan0],
      by rw [Env.setNat_sc, F4.2.1 _ not_false, v3b]; simp [scan, scan0],
      fun l => by rw [Env.setNat_arr, z4 l l.2]; simp [scan, scan0]⟩ ?_) le_rfl
    (fun σ' ⟨⟨dr', F', hbn, hbd, hbb, hrw⟩, _⟩ => ⟨hbn, hbd, hbb, hrw, dr', F'⟩)
  intro k hk σ' ⟨dr', F', hbn, hbd, hbb, hrw⟩ hk' hM' h1'
  -- the row
  refine XV.seq (hrow k hk σ' F' dr' hk') fun σ1 ⟨r1, b1, dr1, G1⟩ => ?_
  have F1 : FrameA Ss Ns As σ σ1 := F'.trans (G1.mono hSrow hNrow hArow)
  have k1 : σ1.nat nk = k := by rw [G1.1 _ rnk, hk']
  -- N_k
  refine XV.seq (XV.dot hL (z := sZ) (r := sN) (t := t) (ax := aRow) (ay := aW) (nr := nr) (nk := nq)
    (x := ra k) (y := w) (E := E) h0 h4 (by trimne) hS (by rw [F1.2.1 _ cZ, eZ]) hRw hW hnr hnq hnd hno
    (by trimnodup') (by rw [F1.1 _ cd, hσd]) (by rw [F1.1 _ c1, hσ1]) r1
    (fun l => by rw [F1.2.2.1 _ _ (cA l).1, eW]) (bR k hk) bW h2E hdl) fun σ2 ⟨s2, dr2, G2⟩ => ?_
  have F2 : FrameA Ss Ns As σ σ2 := F1.trans (G2.mono (fun y h => hSs y (by rcases h with h | h <;> simp [h]))
    (fun j h => hNs j (by rcases h with h | h <;> simp [h])) (fun _ _ h => h.elim))
  -- a_k ⬝ μ̂
  refine XV.seq (XV.dot hL (z := sZ) (r := sTd) (t := t) (ax := aRow) (ay := aMu) (nr := nr) (nk := nq)
    (x := ra k) (y := mu) (E := E) h0 h5 (by trimne) hS (by rw [F2.2.1 _ cZ, eZ]) hRw hMu hnr hnq hnd hno
    (by trimnodup') (by rw [F2.1 _ cd, hσd]) (by rw [F2.1 _ c1, hσ1])
    (fun l => by rw [G2.2.2.1 _ _ (fun h => h), r1])
    (fun l => by rw [F2.2.2.1 _ _ (cA l).2, eMu]) (bR k hk) bMu h2E hdl) fun σ3 ⟨s3, dr3', G3⟩ => ?_
  have F3' : FrameA Ss Ns As σ σ3 := F2.trans (G3.mono (fun y h => hSs y (by rcases h with h | h <;> simp [h]))
    (fun j h => hNs j (by rcases h with h | h <;> simp [h])) (fun _ _ h => h.elim))
  have sB3 : σ3.sc sB = rb k := by rw [G3.2.1 _ (frS1 (by trimne) h3), G2.2.1 _ (frS1 (by trimne) h3), b1]
  have sN3 : σ3.sc sN = N k := by rw [G3.2.1 _ (frS1 (by trimne) h4), s2, ← hNd]
  have bmu : |ra k ⬝ᵥ mu| ≤ 2 ^ (2 * E + d) := dot_abs_le (bR k hk) bMu
  have bmu' : |((ra k ⬝ᵥ mu : ℤ) : ℝ)| < 2 ^ ℓ := cR _ (lt_of_le_of_lt bmu (hE' _ hE2))
  have brb' : |((rb k : ℤ) : ℝ)| < 2 ^ ℓ := cR _ (lt_of_le_of_lt (bB k hk) (hE' _ hE1))
  have bBk' : |((B k : ℤ) : ℝ)| < 2 ^ ℓ := cR _ (lt_of_le_of_lt (bBk k hk) (hE' _ le_rfl))
  have bNk' : |((N k : ℤ) : ℝ)| < 2 ^ ℓ := cR _ (lt_of_le_of_lt (bN k hk) (hE' _ le_rfl))
  have eB : ((rb k : ℤ) : ℝ) - ((ra k ⬝ᵥ mu : ℤ) : ℝ) = ((B k : ℤ) : ℝ) := by rw [← hBd]; push_cast; ring
  -- β̃_k
  refine XV.seq (XV.sop2 hL (x := sBt) (a := sB) (b := sTd) (hNS _ h6) (hNS _ h3) (hNS _ h5) .sub
    (by intro h; cases h) (by rw [sB3]; exact brb') (by rw [s3]; exact bmu')
    (by simp only [RealRAM.Op2.eval]; rw [sB3, s3, eB]; exact bBk')) fun σ4 e4 => ?_
  subst e4
  have sBt4 : (σ3.setSc sBt (RealRAM.Op2.sub.eval (σ3.sc sB) (σ3.sc sTd))).sc sBt = B k := by
    rw [sc_setSc_eq, sB3, s3, ← eB]; simp only [RealRAM.Op2.eval]
  have F4 : FrameA Ss Ns As σ (σ3.setSc sBt (RealRAM.Op2.sub.eval (σ3.sc sB) (σ3.sc sTd))) :=
    F3'.setSc (hSs _ (by simp)) _
  have s4 : ∀ y, y ≠ sBt → (σ3.setSc sBt (RealRAM.Op2.sub.eval (σ3.sc sB) (σ3.sc sTd))).sc y = σ3.sc y :=
    fun y h => sc_setSc_ne _ h
  have a4 : (σ3.setSc sBt (RealRAM.Op2.sub.eval (σ3.sc sB) (σ3.sc sTd))).arr = σ3.arr := Env.setSc_arr _ _ _
  have dr4' : (σ3.setSc sBt (RealRAM.Op2.sub.eval (σ3.sc sB) (σ3.sc sTd))).draws = σ3.draws :=
    Env.setSc_draws _ _ _
  have n4' : (σ3.setSc sBt (RealRAM.Op2.sub.eval (σ3.sc sB) (σ3.sc sTd))).nat = σ3.nat := Env.setSc_nat _ _ _
  generalize σ3.setSc sBt (RealRAM.Op2.sub.eval (σ3.sc sB) (σ3.sc sTd)) = σ4 at sBt4 F4 s4 a4 dr4' n4'
  have sN4 : σ4.sc sN = N k := by rw [s4 _ (by trimne), sN3]
  -- the normalised quotient
  refine XV.seq (XV.qnRun hL (sZ := sZ) (sOne := sOne) (sMOne := sMOne) (sN := sN) (sBt := sBt) (sQN := sQN)
    (sQB := sQB) (sSg := sSg) (N := N k) (B := B k) (hNS _ h0) (hNS _ h1) (hNS _ h2) (hNS _ h4) (hNS _ h6)
    (hNS _ h7) (hNS _ h8) (hNS _ h9) (by trimnodup') (by rw [F4.2.1 _ cZ, eZ]) (by rw [F4.2.1 _ cO, eO])
    (by rw [F4.2.1 _ cM, eM]) sN4 sBt4 (by exact_mod_cast (Int.cast_abs (R := ℝ) ▸ bNk'))
    (by exact_mod_cast (Int.cast_abs (R := ℝ) ▸ bBk')) h1ℓ) fun σ5 ⟨q5, b5, g5, dr5, G5⟩ => ?_
  have F5 : FrameA Ss Ns As σ σ5 := F4.trans (G5.mono (fun y h => hSs y (by
    rcases h with h | h | h <;> simp [h])) (fun _ h => h.elim) (fun _ _ h => h.elim))
  -- the state of the scan is untouched since σ'
  have keepS : ∀ y, ¬ Srow y → y ≠ sN → y < t → y ≠ sTd → y ≠ sBt → y ≠ sQN → y ≠ sQB → y ≠ sSg →
      σ5.sc y = σ'.sc y := fun y hr hN ht hT hB hq1 hq2 hq3 => by
    rw [G5.2.1 _ (by rintro (h | h | h) <;> [exact hq1 h; exact hq2 h; exact hq3 h]), s4 _ hB,
      G3.2.1 _ (frS1 hT ht), G2.2.1 _ (frS1 hN ht), G1.2.1 _ hr]
  have arK : ∀ l, σ5.arr aK l = σ'.arr aK l := fun l => by
    rw [G5.2.2.1 _ _ (fun h => h), a4, G3.2.2.1 _ _ (fun h => h), G2.2.2.1 _ _ (fun h => h), G1.2.2.1 _ _ (rK l)]
  have arR : ∀ l : Fin d, σ5.arr aRow l = ra k l := fun l => by
    rw [G5.2.2.1 _ _ (fun h => h), a4, G3.2.2.1 _ _ (fun h => h), G2.2.2.1 _ _ (fun h => h), r1]
  obtain ⟨sbn, sbd, sbd', -, -, -⟩ := scan_bound N B ra k (2 ^ (2 * E + d + 1)) (2 ^ E) (2 ^ (2 * E + d + 1))
    (by positivity) (by positivity) (one_le_pow₀ (by norm_num)) (fun j hj => bN j (by omega))
    (fun j hj => bR j (by omega)) (fun j hj => bBk j (by omega))
  have bq1 : |(qn (N k) (B k)).1| ≤ 2 ^ (2 * E + d + 1) := (qn_fst_bound _ _).trans (bN k hk)
  have bq2 : |(qn (N k) (B k)).2| ≤ 2 ^ (2 * E + d + 1) := by
    rw [abs_of_pos (qn_pos _ _)]
    exact (qn_snd_le_max _ _).trans (max_le (one_le_pow₀ (by norm_num)) (bBk k hk))
  -- the keep
  refine XV.mono (XV.tkeep hL (sZ := sZ) (sBn := sBn) (sBd := sBd) (sBb := sBb) (sQN := sQN) (sQB := sQB)
    (sSg := sSg) (sL := sL) (sR := sR) (sT := sT) (aK := aK) (aRow := aRow) (nl := nl) (nd := nd) (none := none)
    (E := 2 * E + d + 1) (st := scan N B ra k) (N := N k) (B := B k) (a := ra k) (hNS _ h0) (hNS _ h10)
    (hNS _ h11) (hNS _ h12) (hNS _ h7) (hNS _ h8) (hNS _ h9) (hNS _ h13) (hNS _ h14) (hNS _ h15) (by trimnodup')
    hK hRw hKR hnl hnd hno (by trimnodup') (by rw [F5.1 _ cd, hσd]) (by rw [F5.1 _ c1, hσ1]) hda
    (by rw [F5.2.1 _ cZ, eZ]) (by rw [keepS _ rBn (by trimne) h10 (by trimne) (by trimne) (by trimne) (by trimne)
      (by trimne), hbn]) (by rw [keepS _ rBd (by trimne) h11 (by trimne) (by trimne) (by trimne) (by trimne)
      (by trimne), hbd]) (by rw [keepS _ rBb (by trimne) h12 (by trimne) (by trimne) (by trimne) (by trimne)
      (by trimne), hbb]) (fun l => by rw [arK, hrw]) q5 b5 g5 arR sbn
    (by rw [abs_of_pos sbd]; exact sbd') bq1 bq2
    (fun l => (bR k hk l).trans (pow_le_pow_right₀ (by norm_num) hE1)) hE3) le_rfl ?_
  rintro σ6 ⟨sn6, sd6, sb6, rw6, dr6, G6⟩
  have F6 : FrameA Ss Ns As σ σ6 := F5.trans (G6.mono (fun y h => hSs y (by
    rcases h with h | h | h | h | h | h <;> simp [h])) (fun j h => hNs j (by simp [h]))
    (fun a k' h => hAs a k' (Or.inr h)))
  refine ⟨by rw [G6.1 _ (by trimne), G5.1 _ not_false, n4', G3.1 _ (by rintro (h | h) <;> exact absurd h (by trimne)), G2.1 _ (by rintro (h | h) <;> exact absurd h (by trimne)), k1], by rw [F6.1 _ cMM, hσM], by rw [F6.1 _ c1, hσ1],
    by rw [Env.setNat_draws]; rw [dr6, dr5, dr4', dr3', dr2, dr1, dr'], F6.setNat (hNs _ (Or.inl rfl)) _,
    by rw [Env.setNat_sc, sn6]; rfl, by rw [Env.setNat_sc, sd6]; rfl, by rw [Env.setNat_sc, sb6]; rfl,
    fun l => by rw [Env.setNat_arr, rw6]; rfl⟩

/-! ## `A = Mᵀ x` -/

/-- `y := Mᵀ *ᵥ x`, `M` row-major in the array `aM` (entry `(k, i)` in the cell `d k + i`, read down the column `i`
with the stride `d`), `x` and `y` in the cells `0, ..., d - 1` of the arrays `ax`, `ay`. -/
def xmatvecT (L : Layout) (z r t aM ax ay ni nr nk nd none : ℕ) : XCmd :=
  xforN ni nd none (.seq (.prim (.frag (.nconst nr 0))) (.seq (.prim (.frag (.nadd nr nr ni)))
    (.seq (xfoldE L z r t (.op .mul (.arr aM nr) (.arr ax nk)) nr nd nk nd none) (toX (VL.aset L ay ni r)))))

set_option maxHeartbeats 2000000 in
/-- The rule of `xmatvecT`, entries below `2^E`, `d 2^(2E) < 2^ℓ`. -/
theorem XV.matvecT {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {z r t aM ax ay ni nr nk nd none E : ℕ} {M : Matrix (Fin d) (Fin d) ℤ} {x : Fin d → ℤ} (hz : z < t)
    (hrt : r < t) (hrz : r ≠ z) (hS : t + 3 ≤ L.NS) (hz0 : σ.sc z = 0) (haM : aM < L.NA) (hax : ax < L.NA)
    (hay : ay < L.NA) (hyM : ay ≠ aM) (hyx : ay ≠ ax) (hni : ni < L.NN) (hnr : nr < L.NN) (hnk : nk < L.NN)
    (hnd : nd < L.NN) (hno : none < L.NN) (hne : [ni, nr, nk, nd, none].Nodup) (hσd : σ.nat nd = d)
    (hσ1 : σ.nat none = 1) (hM : ∀ i k : Fin d, σ.arr aM (d * i + k) = M i k) (hx : ∀ k : Fin d, σ.arr ax k = x k)
    (bM : ∀ i k, |M i k| ≤ 2 ^ E) (bx : ∀ k, |x k| ≤ 2 ^ E) (hE : 2 * E < ℓ) (hℓ : d * 2 ^ (2 * E) < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xmatvecT L z r t aM ax ay ni nr nk nd none) σ (d * (1 + (1 + (d * 10 + 4 + 2)) + 3) + 3)
      (fun σ' => (∀ i : Fin d, σ'.arr ay i = (Mᵀ *ᵥ x) i) ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => y = r ∨ t ≤ y) (fun j => j = ni ∨ j = nk ∨ j = nr) (fun b c => b = ay ∧ c < d) σ σ') := by
  have hne' := hne
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne'
  obtain ⟨⟨ir, ik, id, io⟩, ⟨rk, rd, ro⟩, ⟨kd, ko⟩, dO⟩ := hne'
  have hda := asz_lt hL hax
  have hdl : ∀ k < d, k < asz d := fun k hk => by unfold asz; nlinarith
  let J : ℕ → Env d → Prop := fun i σ' => σ'.draws = σ.draws ∧
    (∀ i' (h : i' < i) (hd : i' < d), σ'.arr ay i' = (Mᵀ *ᵥ x) ⟨i', hd⟩) ∧
    FrameA (fun y => y = r ∨ t ≤ y) (fun j => j = ni ∨ j = nk ∨ j = nr) (fun b c => b = ay ∧ c < i) σ σ'
  refine XV.mono (XV.forN hL hni hnd hno id io d (1 + (1 + (d * 10 + 4 + 2))) (by unfold asz at hda; nlinarith) J σ
    hσd hσ1 ⟨rfl, fun i' h => absurd h (Nat.not_lt_zero _),
      (FrameA.refl _ _ _ σ).setNat (Or.inl rfl) 0⟩ ?_) le_rfl
    fun σ' ⟨⟨hd, hy, hF⟩, _⟩ => ⟨fun i => hy i i.2 i.2, hd, hF.mono (fun _ h => h) (fun _ h => h)
      (fun b c h => ⟨h.1, h.2⟩)⟩
  intro i hi σ' ⟨hd, hy, hF⟩ hit hid hi1
  refine XV.seq (XV.nconst hL hnr 0 (by positivity)) fun σ0 e0 => ?_
  subst e0
  refine XV.seq (XV.nadd hL hnr hnr hni (by simp) (by rw [nat_setNat_ne _ ir, hit]; unfold asz at hda; nlinarith))
    fun σ0' e0' => ?_
  subst e0'
  have r0 : ((σ'.setNat nr 0).setNat nr ((σ'.setNat nr 0).nat nr + (σ'.setNat nr 0).nat ni)).nat nr = i := by
    simp [ir, hit]
  generalize hσ0 : (σ'.setNat nr 0).setNat nr ((σ'.setNat nr 0).nat nr + (σ'.setNat nr 0).nat ni) = σ0 at r0
  have F0 : FrameA (fun y => y = r ∨ t ≤ y) (fun j => j = ni ∨ j = nk ∨ j = nr) (fun b c => b = ay ∧ c < i) σ σ0 := by
    rw [← hσ0]; exact (hF.setNat (Or.inr (Or.inr rfl)) _).setNat (Or.inr (Or.inr rfl)) _
  have n0 : ∀ j, j ≠ nr → σ0.nat j = σ'.nat j := fun j h => by rw [← hσ0]; simp [h]
  have s0 : σ0.sc = σ'.sc := by rw [← hσ0]; simp
  have a0 : σ0.arr = σ'.arr := by rw [← hσ0]; simp
  have dr0 : σ0.draws = σ'.draws := by rw [← hσ0]; simp
  let col : Fin d → ℤ := fun k => M k ⟨i, hi⟩
  refine XV.seq (XV.foldE (E := E) (N := d) (base := i) (st := d) (F := fun k => vext col k * vext x k) hL
    (by simp only [IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; exact ⟨⟨haM, hnr⟩, hax, hnk⟩) hz hrt
    hrz (by simp only [IE.scr]; omega) (by rw [F0.2.1 z (by omega), hz0]) hnr hnd hnk hnd hno
    (by simp [rk, rd, ro, kd, ko, dO]) (Ne.symm rd) (Ne.symm kd) (by rw [n0 _ (Ne.symm rd), hid])
    (by rw [n0 _ (Ne.symm ro), hi1]) r0 (by rw [n0 _ (Ne.symm rd), hid])
    (by unfold asz at hda; nlinarith) (by unfold asz at hda; nlinarith) (by unfold asz at hda; nlinarith)
    (by simp only [IE.top, IE.mag]; omega) ?_ ?_) fun σ1 ⟨s1, r1, d1, F1⟩ => ?_
  · intro k hk
    exact lt_of_le_of_lt (abs_partial_le (fun j _ => abs_vext_mul_le (fun _ => bM _ _) bx j) k hk)
      (by have := Nat.mul_le_mul_right (2 ^ (2 * E)) hk; exact_mod_cast lt_of_le_of_lt this hℓ)
  · intro k hk σ2 hF2 hd2 hkt hkr
    have hFF := F0.trans (hF2.mono (fun _ h => h) (fun _ h => by tauto) (fun _ _ h => h.elim))
    have hcell : i + d * k < d * d := by nlinarith
    have aM' : σ2.arr aM (i + d * k) = M ⟨k, hk⟩ ⟨i, hi⟩ := by
      rw [hFF.2.2.1 aM _ (fun h => hyM h.1.symm), show i + d * k = d * k + i by ring]; exact hM ⟨k, hk⟩ ⟨i, hi⟩
    have ax' : σ2.arr ax k = x ⟨k, hk⟩ := by
      rw [hFF.2.2.1 ax k (fun h => hyx h.1.symm)]; exact hx ⟨k, hk⟩
    refine ⟨⟨⟨by rw [hkr]; unfold asz; omega, M ⟨k, hk⟩ ⟨i, hi⟩, by rw [hkr, aM'], bM _ _⟩,
      ⟨by rw [hkt]; exact hdl k hk, x ⟨k, hk⟩, by rw [hkt, ax'], bx _⟩⟩, ?_⟩
    simp only [IE.eval, RealRAM.Op2.eval, hkr, hkt, aM', ax', vext_lt col hk, vext_lt x hk, col]; push_cast; ring
  · have hFF := F0.trans (F1.mono (fun _ h => h) (fun _ h => by tauto) (fun _ _ h => h.elim))
    have n1 : σ1.nat ni = i := by rw [F1.1 ni (by omega), n0 _ ir, hit]
    refine XV.mono (XV.aset hL (a := ay) (i := ni) (x := r) hay hni (by omega) (by rw [n1]; exact hdl i hi)
      (by rw [s1]; exact XV.abs_int_lt (lt_of_le_of_lt (abs_partial_le (fun j _ => abs_vext_mul_le
        (fun _ => bM _ _) bx j) d le_rfl) (by exact_mod_cast hℓ)))) le_rfl fun σ2 e2 => ?_
    subst e2
    have hval : ((∑ k ∈ Finset.range d, vext col k * vext x k : ℤ) : ℝ) = ((Mᵀ *ᵥ x) ⟨i, hi⟩ : ℤ) := by
      rw [sum_vext]; simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, col]
    refine ⟨by simp [n1], by rw [Env.setArr_nat, F1.1 nd (by omega), n0 _ (Ne.symm rd), hid],
      by rw [Env.setArr_nat, F1.1 none (by omega), n0 _ (Ne.symm ro), hi1], ?_, ?_, ?_⟩
    · simp [d1, dr0, hd]
    · intro i' hi' hd'
      simp only [Env.setNat_arr, Env.setArr_arr, n1]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hlt | rfl
      · rw [ite_eq_right (by omega), F1.2.2.1 ay i' (fun h => h), a0]; exact hy i' hlt hd'
      · rw [ite_eq_left (by simp), s1, hval]
    · exact ((hFF.mono (fun _ h => h) (fun _ h => h) (fun b c h => ⟨h.1, by omega⟩)).setArr
        ⟨rfl, by simp only [n1]; omega⟩ _).setNat (Or.inl rfl) _

end AdversarialBco.Bit.Transfer
