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
# TRI-M, the rows of a stage on the machine: the input rows and `A = T̂ᵀ row`

The input rows of a stage read from their cells (`frAl_inp`, `frBe_inp`) and bounded against `M̂` (`entry_le`), and the
product `A = T̂ᵀ row` on the machine (`xmatvecT`, `XV.matvecT`).
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


end Rows

/-- `trimnodup` closing the disequalities from the context. -/
macro "trimnodup'" : tactic =>
  `(tactic| ((simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    not_false_eq_true, and_true]; repeat' constructor) <;> trimne))

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
