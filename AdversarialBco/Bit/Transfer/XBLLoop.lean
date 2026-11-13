/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XVec

@[expose] public section

/-!
# A matrix filled entry by entry

`xmap2E`: for `i < d`, `j < d`, the cell `d i + j` of the array `aB` gets the value of an expression `e` read with the
row `i` in the register `ri`, the column `j` in `nk` and the cell `d i + j` in `nr` (`xmapE` inside `xforN`).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach

variable {d : ℕ}

/-- `nr := 0; for i < nat nn: for j < nat nn: aB[nr] := e; nr := nr + 1`. -/
def xmap2E (L : Layout) (z t : ℕ) (e : IE) (aB nr ri nk nn none : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst nr 0))) (xforN ri nn none (xmapE L z t e aB nr none nk nn none))

/-- The units of `xmap2E` for an expression of `u` units. -/
def map2Units (d u : ℕ) : ℕ := 1 + (d * (d * (u + 6) + 3 + 3) + 3)

set_option maxHeartbeats 1000000 in
/-- The rule of `xmap2E`: the cells `d i + j` of `aB` get `F i j`, and nothing else changes but the scratch from `t`,
the registers `nk`, `nr`, `ri` and those cells. -/
theorem XV.map2E {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {z t aB nr ri nk nn none E : ℕ} {e : IE} {F : ℕ → ℕ → ℤ}
    (hw : e.WF L t) (hz : z < t) (hS : t + 1 + e.scr ≤ L.NS) (hz0 : σ.sc z = 0) (hB : aB < L.NA)
    (hnr : nr < L.NN) (hri : ri < L.NN) (hnk : nk < L.NN) (hnn : nn < L.NN) (hno : none < L.NN)
    (hne : [nr, nk, nn, none].Nodup) (hri' : ri ≠ nr ∧ ri ≠ nk ∧ ri ≠ nn ∧ ri ≠ none)
    (hσn : σ.nat nn = d) (hσ1 : σ.nat none = 1) (hda : d * d + d < 2 ^ ℓa) (htop : e.top E < ℓ)
    (hF : ∀ i < d, ∀ j < d, ∀ σ' : Env d, FrameA (fun y => t ≤ y) (fun r => r = nk ∨ r = nr ∨ r = ri)
        (fun b c => b = aB ∧ c < d * i + j) σ σ' → σ'.draws = σ.draws →
        σ'.nat ri = i → σ'.nat nk = j → σ'.nat nr = d * i + j → e.Leaves E σ' ∧ e.eval σ' = F i j) :
    XRunsB L X ℓa ℓ (xmap2E L z t e aB nr ri nk nn none) σ (map2Units d e.units) (fun σ' =>
      (∀ i j : Fin d, σ'.arr aB (d * i + j) = F i j) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => t ≤ y) (fun r => r = nk ∨ r = nr ∨ r = ri) (fun b c => b = aB ∧ c < d * d) σ σ') := by
  have hne' := hne
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne'
  obtain ⟨⟨rk, rn, ro⟩, ⟨kn, ko⟩, no⟩ := hne'
  obtain ⟨ir, ik, inn, io⟩ := hri'
  refine XV.seq (XV.nconst hL (σ := σ) (i := nr) hnr 0 (by positivity)) fun σ0 e0 => ?_
  subst e0
  let J : ℕ → Env d → Prop := fun i σ' => σ'.nat nr = d * i ∧ σ'.draws = σ.draws ∧
    (∀ i' < i, ∀ j < d, σ'.arr aB (d * i' + j) = F i' j) ∧
    FrameA (fun y => t ≤ y) (fun r => r = nk ∨ r = nr ∨ r = ri) (fun b c => b = aB ∧ c < d * i) σ σ'
  refine XV.mono (XV.forN hL hri hnn hno inn io d (d * (e.units + 6) + 3) (by omega) J (σ.setNat nr 0)
    (by simp [Ne.symm rn, hσn]) (by simp [Ne.symm ro, hσ1])
    ⟨by simp [ir], by simp, fun i' hi' => absurd hi' (Nat.not_lt_zero _),
      ((FrameA.refl _ _ _ σ).setNat (Or.inr (Or.inl rfl)) 0).setNat (Or.inr (Or.inr rfl)) 0⟩ ?_)
    le_rfl fun σ' ⟨⟨_, d', hv, F'⟩, _⟩ =>
      ⟨fun i j => hv i i.2 j j.2, d', F'⟩
  intro i hi σ1 ⟨r1, d1, v1, F1⟩ hi1 hn1 ho1
  have hcell : ∀ k < d, d * i + 1 * k < asz d := fun k hk => by
    unfold asz; have : d * i + d ≤ d * d := by nlinarith
    omega
  have hra : d * i + 1 * d < 2 ^ ℓa := by
    have : d * i + d ≤ d * d := by nlinarith
    omega
  refine XV.mono (XV.mapE (E := E) (N := d) (base := d * i) (st := 1) (F := F i) hL (σ := σ1) (z := z) (t := t)
    (aB := aB) (nr := nr) (nst := none) (nk := nk) (nn := nn) (none := none) (e := e) hw hz hS
    (by rw [F1.2.1 z (by omega), hz0]) hB hnr hno hnk hnn hno hne (Ne.symm ro) (Ne.symm ko) hn1 ho1 r1 ho1 one_pos
    hcell (by omega) hra (by have := hL.1; omega) htop ?_) le_rfl fun σ2 ⟨v2, r2, d2, F2⟩ => ?_
  · intro k hk σ' F' d' hk' hr'
    have hri1 : σ'.nat ri = i := by rw [F'.1 ri (by omega), hi1]
    refine hF i hi k hk σ' ((F1.mono (fun y h => h) (fun r h => h) (fun b c h => ⟨h.1, by omega⟩)).trans
      (F'.mono (fun y h => h) (fun r h => by tauto) (fun b c h => ⟨h.1, by omega⟩))) (d'.trans d1)
      hri1 hk' (by rw [hr']; ring)
  · have hri2 : σ2.nat ri = i := by rw [F2.1 ri (by omega), hi1]
    have hn2 : σ2.nat nn = d := by rw [F2.1 nn (by omega), hn1]
    have ho2 : σ2.nat none = 1 := by rw [F2.1 none (by omega), ho1]
    refine ⟨hri2, hn2, ho2, ?_, by simp [d2, d1], ?_, ?_⟩
    · simp only [Env.setNat_nat, ite_eq_right_iff.2 (fun h => absurd h ir.symm), r2]; ring
    · intro i' hi' j hj
      simp only [Env.setNat_arr]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hlt | rfl
      · rw [F2.2.2.1 aB (d * i' + j) (fun h => by
          have : d * i' + d ≤ d * i := by nlinarith
          omega)]
        exact v1 i' hlt j hj
      · have := v2 j hj
        rwa [one_mul] at this
    · have hd1 : d * i + 1 * d ≤ d * (i + 1) := by ring_nf; omega
      exact ((F1.mono (fun y h => h) (fun r h => h) (fun b c h => ⟨h.1, by nlinarith [h.2]⟩)).trans
        (F2.mono (fun y h => h) (fun r h => by tauto) (fun b c h => ⟨h.1, by omega⟩))).setNat
          (Or.inr (Or.inr rfl)) _

end AdversarialBco.Bit.Transfer.BLM
