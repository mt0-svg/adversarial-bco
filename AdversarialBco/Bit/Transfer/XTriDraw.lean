/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriUpd
public import AdversarialBco.Bit.Transfer.XBmRun

@[expose] public section

/-!
# TRI-M, one draw of the core

* `xdraw`, `XV.draw`: the `d` coordinates of a draw, BM-INT on consecutive blocks of `B` coins, into an array.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.TriM Matrix

variable {d : ℕ}

/-- Coordinate `i` of a draw read from the coins at `c`: BM-INT on the blocks `c + 2 B i` and `c + 2 B i + B`. -/
def gsAt (cs : ℕ → Bool) (B c i : ℕ) : ℤ :=
  (gsSpec B (BitRAM.readCoins cs (c + 2 * B * i) B).toNat (BitRAM.readCoins cs (c + 2 * B * i + B) B).toNat).1

/-- The draw: `for i < d: BM-INT; aY[i] := Γ_c`. -/
def xdraw (L : Layout) (o on aY ni nd none : ℕ) : XCmd :=
  xforN ni nd none (.seq (xbmint L o on) (toX (VL.aset L aY ni (o + 40))))

set_option maxHeartbeats 1000000 in
theorem XV.draw {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {o on aY ni nd none B : ℕ}
    (hS : o + 43 ≤ L.NS) (hN : on + 12 ≤ L.NN) (hB : 1 ≤ B) (hσB : σ.nat on = B)
    (hℓa : 4 * gsm_prec B + 2 < 2 ^ ℓa) (hℓ : 4 * gsm_prec B + 4 ≤ ℓ) (hY : aY < L.NA)
    (hni : ni < L.NN) (hnd : nd < L.NN) (hno : none < L.NN) (hid : ni ≠ nd) (hio : ni ≠ none)
    (hoi : ¬ (on ≤ ni ∧ ni < on + 12)) (hod : ¬ (on < nd ∧ nd < on + 12)) (hoo : ¬ (on < none ∧ none < on + 12))
    (hσd : σ.nat nd = d) (hσ1 : σ.nat none = 1) (hda : d * d + d < 2 ^ ℓa)
    (hgs : ∀ U W : ℕ, U < 2 ^ B → W < 2 ^ B → |((gsSpec B U W).1 : ℝ)| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xdraw L o on aY ni nd none) σ (d * (bmUnits B + 2 + 3) + 3) (fun σ' =>
      (∀ i : Fin d, σ'.arr aY i = gsAt X.wb.cs B σ.draws i) ∧ σ'.draws = σ.draws + 2 * B * d ∧
      FrameA (fun y => o ≤ y ∧ y < o + 43) (fun j => j = ni ∨ on < j ∧ j < on + 12) (fun b k => b = aY ∧ k < d)
        σ σ') := by
  have hdl : ∀ k < d, k < asz d := fun k hk => by unfold asz; nlinarith
  have htn : ∀ (cs : ℕ → Bool) (c : ℕ), (BitRAM.readCoins cs c B).toNat < 2 ^ B := fun cs c => by
    obtain ⟨h0, h1⟩ := readCoins_bounds cs c B
    rw [Int.toNat_lt h0]; exact_mod_cast h1
  let J : ℕ → Env d → Prop := fun k σ' => σ'.draws = σ.draws + 2 * B * k ∧ σ'.nat on = B ∧
    (∀ i' (_ : i' < k), σ'.arr aY i' = gsAt X.wb.cs B σ.draws i') ∧
    FrameA (fun y => o ≤ y ∧ y < o + 43) (fun j => j = ni ∨ on < j ∧ j < on + 12) (fun b c => b = aY ∧ c < k) σ σ'
  refine XV.mono (XV.forN hL hni hnd hno hid hio d (bmUnits B + 2) (by omega) J σ hσd hσ1
    ⟨by simp, by rw [nat_setNat_ne _ (fun h => hoi ⟨h.le, by omega⟩), hσB],
      fun _ h => absurd h (Nat.not_lt_zero _),
      (FrameA.refl (fun y => o ≤ y ∧ y < o + 43) (fun j => j = ni ∨ on < j ∧ j < on + 12)
        (fun b c => b = aY ∧ c < 0) σ).setNat (Or.inl rfl) 0⟩ ?_) le_rfl
    fun σ' ⟨⟨hd', _, hy, hF⟩, _⟩ => ⟨fun i => hy i i.2, hd', hF⟩
  intro k hk σ' ⟨hd', hB', hy, hF⟩ hkt hkd hk1
  refine XV.seq (XV.bmint hL hS hN hB hB' hℓa hℓ) fun σ1 ⟨g1, _, d1, F1⟩ => ?_
  have n1 : ∀ j, ¬ (on < j ∧ j < on + 12) → σ1.nat j = σ'.nat j := fun j hj => F1.1 j hj
  have k1 : σ1.nat ni = k := by rw [n1 ni (fun h => hoi ⟨h.1.le, h.2⟩), hkt]
  refine XV.mono (XV.aset hL (a := aY) (i := ni) (x := o + 40) hY hni (by omega) (by rw [k1]; exact hdl k hk)
    (by rw [g1]; exact hgs _ _ (htn _ _) (htn _ _))) le_rfl fun σ2 e2 => ?_
  subst e2
  have F1' : FrameA (fun y => o ≤ y ∧ y < o + 43) (fun j => j = ni ∨ on < j ∧ j < on + 12)
      (fun b c => b = aY ∧ c < k + 1) σ' (σ1.setArr aY (σ1.nat ni) (σ1.sc (o + 40))) :=
    (FrameA.ofP (F1.mono (fun _ h => h) (fun _ h => Or.inr h))).setArr ⟨rfl, by rw [k1]; omega⟩ _
  refine ⟨by rw [Env.setArr_nat, k1], by rw [Env.setArr_nat, n1 nd hod, hkd],
    by rw [Env.setArr_nat, n1 none hoo, hk1], ?_, ?_, ?_, ?_⟩
  · rw [Env.setNat_draws, Env.setArr_draws, d1, hd']; ring
  · rw [nat_setNat_ne _ (fun h => hoi ⟨h.le, by omega⟩), Env.setArr_nat,
      n1 on (fun h => by omega), hB']
  · intro i' hi'
    rw [Env.setNat_arr, Env.setArr_arr, k1]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hlt | rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => by omega), F1.2.2.1]; exact hy i' hlt
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, rfl⟩), g1, hd']; rfl
  · exact ((hF.mono (fun _ h => h) (fun _ h => h) (fun b c h => ⟨h.1, by omega⟩)).trans F1').setNat
      (Or.inl rfl) _

end AdversarialBco.Bit.Transfer
