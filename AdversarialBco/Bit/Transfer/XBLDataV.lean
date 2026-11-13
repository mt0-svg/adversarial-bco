/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLDataG

@[expose] public section

/-!
# The call data of BL's round, part 2: vectors of pairs

`xvec`, `XV.vec`: for `k < N` (`N` in the register `nn`), `aN[k] := e` (the expression `e` at turn `k`, the register
`30` holding `k`) and `aD[k] := yD`, through two runs of `xmapE` (registers `29`, `30`, scratch from the slot `t`).
-/

namespace AdversarialBco.Bit.Transfer.BLM.DataM

open AdversarialBco AdversarialBco.Poly.Mach

variable {d : ℕ}

/-- `29 := 0; aN[k] := e (k < N); 29 := 0; aD[k] := yD (k < N)`. -/
def xvec (L : Layout) (z t : ℕ) (e : IE) (aN aD yD nn : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst 29 0))) (.seq (xmapE L z t e aN 29 rOne 30 nn rOne)
    (.seq (.prim (.frag (.nconst 29 0))) (xmapE L z t (.sc yD) aD 29 rOne 30 nn rOne)))

/-- The units of `xvec` over `N` cells. -/
def vecUnits (N : ℕ) (e : IE) : ℕ := 1 + ((N * (e.units + 6) + 3) + (1 + (N * (1 + 6) + 3)))

set_option maxHeartbeats 2000000 in
/-- **A vector of pairs**: the cells `k < N` of `aN` get `F k` (the value of `e` at turn `k`), those of `aD` the value
`D` of the slot `yD`; only the slots from `t` on, the registers `29`, `30` and these cells change. -/
theorem XV.vec {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hlay : BLLay L)
    {z t aN aD yD nn N E : ℕ} {e : IE} {F : ℕ → ℤ} {D : ℤ}
    (hw : e.WF L t) (hz : z < t) (hS : t + 1 + e.scr ≤ L.NS) (hz0 : σ.sc z = 0) (haN : aN < L.NA)
    (haD : aD < L.NA) (hND : aN ≠ aD) (hyD : yD < t) (hnn : nn < L.NN) (hnn' : nn ≠ 29 ∧ nn ≠ 30 ∧ nn ≠ rOne)
    (hσn : σ.nat nn = N) (h1 : σ.nat rOne = 1) (hσD : σ.sc yD = D) (bD : |D| ≤ 2 ^ E) (hN : N ≤ asz d)
    (hNa : N < 2 ^ ℓa) (htop : e.top E < ℓ) (hE : E < ℓ)
    (hF : ∀ k < N, ∀ σ' : Env d, FrameA (fun y => t ≤ y) (fun j => j = 30 ∨ j = 29) (fun b c => b = aN ∧ c < k)
        σ σ' → σ'.draws = σ.draws → σ'.nat 30 = k → σ'.nat 29 = k → e.Leaves E σ' ∧ e.eval σ' = F k) :
    XRunsB L X ℓa ℓ (xvec L z t e aN aD yD nn) σ (vecUnits N e) (fun σ' =>
      (∀ k < N, σ'.arr aN k = F k ∧ σ'.arr aD k = D) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => t ≤ y) (fun j => j = 30 ∨ j = 29) (fun b c => (b = aN ∨ b = aD) ∧ c < N) σ σ') := by
  obtain ⟨-, hNN, -⟩ := hlay
  simp only [rEE] at hNN
  obtain ⟨n29, n30, n3⟩ := hnn'
  have hNa' : 1 < 2 ^ ℓa := by have := hL.1; omega
  refine XV.seq (XV.nconst hL (i := 29) (by omega) 0 (by positivity)) fun σ0 e0 => ?_
  subst e0
  refine XV.seq (XV.mapE hL (z := z) (t := t) (aB := aN) (nr := 29) (nst := rOne) (nk := 30) (nn := nn)
    (none := rOne) (E := E) (N := N) (base := 0) (st := 1) (F := F) hw hz hS (by rwenv; exact hz0) haN (by omega)
    (by rwgo) (by omega) hnn (by rwgo)
    (by simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil, and_true];
        refine ⟨⟨by omega, Ne.symm n29, by rwgo⟩, ⟨Ne.symm n30, by rwgo⟩, ?_⟩; simpa using n3)
    (by rwgo) (by rwgo) (by rwenv; exact hσn) (by rwenv; exact h1) (by rwenv) (by rwenv; exact h1) one_pos
    (fun k hk => by unfold asz at hN ⊢; omega) hNa (by omega) hNa' htop ?_) fun σ1 ⟨m1, _, m3, m4⟩ => ?_
  · intro k hk σ' hF' hd hk30 hk29
    have F0 : FrameA (fun y => t ≤ y) (fun j => j = 30 ∨ j = 29) (fun b c => b = aN ∧ c < k) σ σ' :=
      ((FrameA.refl _ _ _ σ).setNat (Or.inr rfl) 0).trans
        (hF'.mono (fun _ h => h) (fun _ h => h) (fun b c h => ⟨h.1, by omega⟩))
    exact hF k hk σ' F0 (by rw [hd]; rfl) hk30 (by rw [hk29]; ring)
  have n1 : ∀ j, j ≠ 29 → j ≠ 30 → σ1.nat j = σ.nat j := fun j h9 h0 => by
    rw [m4.1 j (by omega)]; rwenv
  have eD1 : σ1.sc yD = D := by rw [m4.2.1 yD (by omega)]; rwenv; exact hσD
  have ez1 : σ1.sc z = 0 := by rw [m4.2.1 z (by omega)]; rwenv; exact hz0
  refine XV.seq (XV.nconst hL (i := 29) (by omega) 0 (by positivity)) fun σ2 e2 => ?_
  subst e2
  refine XV.mono (XV.mapE hL (z := z) (t := t) (e := .sc yD) (aB := aD) (nr := 29) (nst := rOne) (nk := 30)
    (nn := nn) (none := rOne) (E := E) (N := N) (base := 0) (st := 1) (F := fun _ => D) (by exact hyD) hz
    (by simp only [IE.scr]; omega) (by rwenv; exact ez1) haD (by omega) (by rwgo) (by omega) hnn (by rwgo)
    (by simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil, and_true];
        refine ⟨⟨by omega, Ne.symm n29, by rwgo⟩, ⟨Ne.symm n30, by rwgo⟩, ?_⟩; simpa using n3)
    (by rwgo) (by rwgo) (by rwenv; rw [n1 nn n29 n30]; exact hσn) (by rwenv; rw [n1 rOne (by rwgo) (by rwgo)]; exact h1)
    (by rwenv) (by rwenv; rw [n1 rOne (by rwgo) (by rwgo)]; exact h1) one_pos
    (fun k hk => by unfold asz at hN ⊢; omega) hNa (by omega) hNa' (by simp only [IE.top]; exact hE) ?_)
    (by simp only [IE.units]; omega) fun σ3 ⟨r1, _, r3, r4⟩ => ?_
  · intro k hk σ' hF' _ _ _
    have e' : σ'.sc yD = D := by rw [hF'.2.1 yD (by omega)]; rwenv; exact eD1
    exact ⟨⟨D, e', bD⟩, e'⟩
  refine ⟨fun k hk => ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [r4.2.2.1 aN k (fun h => hND h.1)]; rwenv; simpa using m1 k hk
  · simpa using r1 k hk
  · rw [r3]; rwenv; rw [m3]; rfl
  · exact (((FrameA.refl _ _ _ σ).setNat (Or.inr rfl) 0).trans
      (m4.mono (fun _ h => h) (fun _ h => h) (fun b c h => ⟨Or.inl h.1, by omega⟩))).setNat (Or.inr rfl) 0
      |>.trans (r4.mono (fun _ h => h) (fun _ h => h) (fun b c h => ⟨Or.inr h.1, by omega⟩))

end AdversarialBco.Bit.Transfer.BLM.DataM
