/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriRow

@[expose] public section

/-!
# TRI-M, the zero loop of an array

`xzero`, `XV.zero`: the zero loop of an array.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.TriM Matrix

variable {d : ℕ}

/-- `aR[l] := sZ` for `l < d`. -/
def xzero (L : Layout) (aR sZ nl nd none : ℕ) : XCmd := xforN nl nd none (toX (VL.aset L aR nl sZ))

theorem XV.zero {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {aR sZ nl nd none : ℕ}
    (hR : aR < L.NA) (hsZ : sZ < L.NS) (hnl : nl < L.NN) (hnd : nd < L.NN) (hno : none < L.NN)
    (hne : [nl, nd, none].Nodup) (hσd : σ.nat nd = d) (hσ1 : σ.nat none = 1) (hda : d * d + d < 2 ^ ℓa)
    (eZ : σ.sc sZ = 0) :
    XRunsB L X ℓa ℓ (xzero L aR sZ nl nd none) σ (d * (2 + 3) + 3)
      (fun σ' => (∀ l < d, σ'.arr aR l = 0) ∧ σ'.draws = σ.draws ∧
        FrameA (fun _ => False) (fun j => j = nl) (fun b k => b = aR ∧ k < d) σ σ') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne
  obtain ⟨⟨ld, lo⟩, dO⟩ := hne
  let J : ℕ → Env d → Prop := fun j σ' => (∀ j' < j, σ'.arr aR j' = 0) ∧ σ'.draws = σ.draws ∧ σ'.sc sZ = 0 ∧
    FrameA (fun _ => False) (fun j => j = nl) (fun b k => b = aR ∧ k < j) σ σ'
  refine XV.mono (XV.forN hL hnl hnd hno ld lo d 2 (by omega) J σ hσd hσ1
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, by rw [Env.setNat_sc]; exact eZ,
      (FrameA.refl (fun _ => False) (fun j => j = nl) (fun b k => b = aR ∧ k < 0) σ).setNat rfl 0⟩ ?_) le_rfl
    fun σ' ⟨⟨h1, h2, _, h4⟩, _⟩ => ⟨h1, h2, h4⟩
  intro j hj σ' ⟨hy, hd', hz, hF⟩ hjt hjn hj1
  refine XV.mono (XV.aset hL hR hnl hsZ (by rw [hjt]; unfold asz; nlinarith) (by rw [hz]; simp)) le_rfl
    fun σ1 e1 => ?_
  subst e1
  refine ⟨by rw [Env.setArr_nat]; exact hjt, by rw [Env.setArr_nat]; exact hjn, by rw [Env.setArr_nat]; exact hj1,
    fun j' hj' => ?_, by rw [Env.setNat_draws, Env.setArr_draws]; exact hd',
    by rw [Env.setNat_sc, Env.setArr_sc]; exact hz, ?_⟩
  · rw [Env.setNat_arr, Env.setArr_arr]
    by_cases h : j' = j
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, by rw [hjt, h]⟩), hz]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h' => h (by rw [h'.2, hjt]))]
      exact hy j' (by omega)
  · exact ((hF.mono (fun _ h => h) (fun _ h => h) (fun b k h => ⟨h.1, by omega⟩)).setArr
      ⟨rfl, by rw [hjt]; omega⟩ _).setNat rfl _

end AdversarialBco.Bit.Transfer
