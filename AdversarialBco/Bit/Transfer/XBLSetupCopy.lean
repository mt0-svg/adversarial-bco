/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSetupLink
public import AdversarialBco.Bit.Transfer.XEllSet

@[expose] public section

/-!
# BL's setup on the machine: copies

`xcopyS`: slots `dst := src` over a list of pairs; `XV.copyN`: the first `N` cells of an array into another (as
`xcopyA` of XEllOut.lean, for any count `N` in a register, with the frame of exactly the cells written).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach

variable {d : ℕ} {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ}

/-- `dst := src + z` for every pair `(dst, src)` of the list. -/
def xcopyS (L : Layout) (z : ℕ) : List (ℕ × ℕ) → XCmd
  | [] => .skip
  | p :: ps => .seq (xset L p.1 p.2 z) (xcopyS L z ps)

theorem XV.copyS (hL : LayOK L d ℓa) {z : ℕ} (hz : z < L.NS) :
    ∀ (ps : List (ℕ × ℕ)) (σ : Env d), σ.sc z = 0 →
      (∀ p ∈ ps, p.1 < L.NS ∧ p.2 < L.NS ∧ p.1 ≠ z ∧ |σ.sc p.2| < 2 ^ ℓ) → (ps.map Prod.fst).Nodup →
      (∀ p ∈ ps, ∀ q ∈ ps, p.1 ≠ q.2) →
      XRunsB L X ℓa ℓ (xcopyS L z ps) σ ps.length (fun σ' => (∀ p ∈ ps, σ'.sc p.1 = σ.sc p.2) ∧
        σ'.draws = σ.draws ∧ FrameA (fun y => y ∈ ps.map Prod.fst) (fun _ => False) (fun _ _ => False) σ σ')
  | [], σ, _, _, _, _ => XV.mono (XV.skip σ) le_rfl fun σ' e => by
      subst e; exact ⟨fun _ h => absurd h List.not_mem_nil, rfl, FrameA.refl _ _ _ σ'⟩
  | p :: ps, σ, hz0, hb, hnd, hds => by
    obtain ⟨h1, h2, h3, h4⟩ := hb p List.mem_cons_self
    have hz0' : |σ.sc z| < 2 ^ ℓ := by rw [hz0, abs_zero]; positivity
    refine XV.mono (K := 1 + ps.length) (XV.seq (XV.sop2 hL (x := p.1) (a := p.2) (b := z) h1 h2 hz .add
      (by intro h; cases h) h4 hz0'
      (by simp only [RealRAM.Op2.eval, hz0, add_zero]; exact h4)) fun σ1 e1 => ?_) (by simp; omega) fun _ h => h
    subst e1
    simp only [RealRAM.Op2.eval, hz0, add_zero]
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    obtain ⟨hn1, hn2⟩ := hnd
    refine XV.mono (XV.copyS hL hz ps _ (by rw [sc_setSc_ne _ (Ne.symm h3), hz0])
      (fun q hq => ?_) hn2 (fun q hq r hr => hds q (List.mem_cons_of_mem _ hq) r (List.mem_cons_of_mem _ hr)))
      (by simp) fun σ' ⟨q1, q2, q3⟩ => ⟨fun q hq => ?_, by rw [q2]; rfl, ?_⟩
    · obtain ⟨g1, g2, g3, g4⟩ := hb q (List.mem_cons_of_mem _ hq)
      refine ⟨g1, g2, g3, ?_⟩
      rw [sc_setSc_ne _ (Ne.symm (hds p List.mem_cons_self q (List.mem_cons_of_mem _ hq)))]
      exact g4
    · rcases List.mem_cons.1 hq with rfl | hq
      · rw [q3.2.1 _ (fun h => by
          obtain ⟨r, hr, e⟩ := List.mem_map.1 h
          exact hn1 ⟨r, hr, e⟩), sc_setSc_eq]
      · rw [q1 q hq, sc_setSc_ne _ (Ne.symm (hds p List.mem_cons_self q (List.mem_cons_of_mem _ hq)))]
    · exact ((FrameA.refl _ _ _ σ).setSc (by simp) _).trans
        (q3.mono (fun y hy => by simp only [List.map_cons, List.mem_cons]; exact Or.inr hy) (fun _ h => h)
          (fun _ _ h => h))

/-- `dst[k] := src[k]` for `k < nat nn`; `nr` walks the cells, `nk` counts, `one` holds `1`; scratch from `t`. -/
def xcopyN (L : Layout) (z t src dst nr nk nn one : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst nr 0))) (xmapE L z t (.arr src nr) dst nr one nk nn one)

set_option maxHeartbeats 1000000 in
/-- The first `N` cells of the array `src` into the array `dst` (`nn` holds `N`, `one` holds `1`). -/
theorem XV.copyN (hL : LayOK L d ℓa) {σ : Env d} {z t src dst nr nk nn one E N : ℕ} {x : ℕ → ℤ} (hz : z < t)
    (hS : t + 1 ≤ L.NS) (hz0 : σ.sc z = 0) (hsrc : src < L.NA) (hdst : dst < L.NA) (hsd : src ≠ dst)
    (hnr : nr < L.NN) (hnk : nk < L.NN) (hnn : nn < L.NN) (hone : one < L.NN) (hne : [nr, nk, nn, one].Nodup)
    (hσn : σ.nat nn = N) (hσ1 : σ.nat one = 1) (hN : N ≤ asz d) (hx : ∀ k < N, σ.arr src k = x k)
    (bx : ∀ k < N, |x k| ≤ 2 ^ E) (hE : E < ℓ) :
    XRunsB L X ℓa ℓ (xcopyN L z t src dst nr nk nn one) σ (1 + (N * (2 + 6) + 3)) (fun σ' =>
      (∀ k < N, σ'.arr dst k = x k) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => t ≤ y) (fun j => j = nk ∨ j = nr) (fun b c => b = dst ∧ c < N) σ σ') := by
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  have hda := asz_lt hL hdst
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil, and_true]
    at hne
  obtain ⟨⟨rk, rn, ro⟩, ⟨kn, ko⟩, no⟩ := hne
  refine XV.seq (XV.nconstA hL (i := nr) hnr 0 (by positivity)) fun σ1 ⟨v1, d1, G1⟩ => ?_
  have e1 : ∀ j, j ≠ nr → σ1.nat j = σ.nat j := fun j h => G1.1 j h
  refine XV.mono (XV.mapEx (E := E) (N := N) (base := 0) (st := 1) (F := x) hL (z := z) (t := t)
    (e := .arr src nr) (aB := dst) (nr := nr) (nst := one) (nk := nk) (nn := nn) (none := one)
    (by simp only [IE.WF]; omega) hz (by simp only [IE.scr]; omega) (by rw [G1.2.1 _ id, hz0]) hdst hnr hone
    hnk hnn hone (by simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]; omega) (Ne.symm ro) (Ne.symm ko)
    (by rw [e1 _ (Ne.symm rn), hσn]) (by rw [e1 _ (Ne.symm ro), hσ1]) v1 (by rw [e1 _ (Ne.symm ro), hσ1]) one_pos
    (fun k hk => by omega) (by omega) (by omega) hsa (by simp only [IE.top]; omega)
    (fun k hk σ' hF _ _ hr => ?_)) le_rfl fun σ2 ⟨z2, _, d2, F2⟩ => ?_
  · have ha : σ'.arr src k = ((x k : ℤ) : ℝ) := by
      rw [hF.2.2.1 _ _ (fun h => hsd h.1), G1.2.2.1 _ _ id, hx k hk]
    refine ⟨⟨by rw [hr]; omega, x k, by rw [hr, zero_add, one_mul, ha], bx k hk⟩,
      by simp only [IE.eval]; rw [hr, zero_add, one_mul, ha]⟩
  · refine ⟨fun k hk => ?_, by rw [d2, d1], ?_⟩
    · have := z2 k hk
      rw [zero_add, one_mul] at this
      exact this
    · exact (G1.mono (fun _ h => h.elim) (fun j h => Or.inr h) (fun _ _ h => h.elim)).trans
        (F2.mono (fun y h => h) (fun j h => h) (fun b c h => by
          obtain ⟨hb, k', hk', e⟩ := h
          exact ⟨hb, by omega⟩))

end AdversarialBco.Bit.Transfer.BLM
