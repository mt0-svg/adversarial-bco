/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XDriver

@[expose] public section

/-!
# The driver with the plays of the run

The driver of Bit/Transfer/XDriver.lean hands the round an environment with the invariant. A round that reads the
losses of the game (`RoundBL`) also needs the points the run has played so far: in the game world the loss of round
`t` is the strategy's loss on `playedBit` of the rounds before `t`. Here the checkpoints of the driver are states of
the run itself, so the round also gets `playedBit P g s0 i = σ.pts i` for every round `i` already played
(`playedBit_eq`, `runBit_eq_run`).

* `prog_okR`: the driver's program runs, with that hypothesis given to the round, and every round `t < n` played at a
  checkpoint with the invariant, whose point is `playedBit P g s0 t`;
* `prog_ok_frozenR`: the same in the form of the frozen statement.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco BitRAM
open Function

variable {d : ℕ}

/-- The driver's program runs, the round knowing that the points of the rounds already played are those of the run. -/
theorem prog_okR {L : Poly.Mach.Layout} {ℓa ℓ Ks Kr : ℕ} {setup round : XCmd} {Inv : Poly.Mach.«Env» d → Prop}
    {n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} (hH : RealRAM.HeightLE A b M) (g : GameBit d)
    (hoff : offOf d m < 2 ^ ℓa) (h4 : 4 ≤ 2 ^ ℓa) (hd : d + 1 < 2 ^ ℓa)
    (hsetup : ∃ k s1 σ1, k ≤ Ks ∧
      XExecB (ctxOf (gameWorld (prog setup round) g (initBit d n m A b)) n m A b) ℓa ℓ setup zeroState k s1 ∧
      Poly.Mach.Rep L σ1 s1 ∧ Inv σ1)
    (hround : ∀ σ, Inv σ → σ.rounds < n →
      (∀ i < σ.rounds, playedBit (prog setup round) g (initBit d n m A b) i = σ.pts i) →
      XRunsB L (ctxOf (gameWorld (prog setup round) g (initBit d n m A b)) n m A b) ℓa ℓ round σ Kr
        (fun σ' => Inv σ' ∧ σ.rounds < σ'.rounds)) :
    CostOKBit (prog setup round) g (initBit d n m A b) n ((costP ℓa ℓ Ks + 2 * costR ℓa ℓ Kr : ℕ) : ℝ) ∧
      SpaceOKBit (prog setup round) g (initBit d n m A b) n
        (max (inSpace d n m M : ℝ) (ckSpace d n m M ℓa ℓ : ℝ) + ((costP ℓa ℓ Ks + costR ℓa ℓ Kr : ℕ) : ℝ)) ∧
      ∀ t < n, ∃ σ, Inv σ ∧ t < σ.rounds ∧ playedBit (prog setup round) g (initBit d n m A b) t = σ.pts t := by
  obtain ⟨cP, cS, cZ1, cZ2, cR, cJ⟩ := prog_code setup round
  generalize hw : gameWorld (prog setup round) g (initBit d n m A b) = w at hsetup hround
  generalize prog setup round = P at cP cS cZ1 cZ2 cR cJ hw hround ⊢
  have hoffX : (ctxOf w n m A b).off < 2 ^ ℓa := hoff
  have eR : ∀ k, runBit P g (initBit d n m A b) k = run P w (initBit d n m A b) k := fun k => by
    rw [← hw]; cases g; exact Conj1BitSanity.runBit_eq_run P _ _ _ k
  let Start : State d → Prop := fun a => (a.pc = 6 + xtlen setup + 2 ∧ a.mem T1 = 0 ∧ a.mem T2 = 0 ∧
    ∃ s σ, XSim (ctxOf w n m A b) s a ∧ Poly.Mach.Rep L σ s ∧ Inv σ ∧ Clean ℓa ℓ s) ∧
    ∃ k, a = run P w (initBit d n m A b) k
  -- the prologue, the setup and the first zeroing
  obtain ⟨t6, e6, p6, hs6, c6⟩ := prologue_run (w := w) (n := n) (A := A) (b := b) (ℓ := ℓ) cP hoff hd
  obtain ⟨k, s1, σ1, hk, he, hr, hinv⟩ := hsetup
  obtain ⟨n1, -, t7, e7, p7, hs7, c7⟩ := xtransfer hoffX he 6 t6 cS p6 hs6
  obtain ⟨t8, e8, p8, hs8, z1, z2, c8⟩ := zero_scratch cZ1 cZ2 p7 hs7
  have hj0 : run P w (initBit d n m A b) (6 + n1 + 2) = t8 := by
    rw [B.run_add, B.run_add, e6]
    exact (congrArg (fun t => run P w t 2) e7).trans e8
  have hst : Start (run P w (initBit d n m A b) (6 + n1 + 2)) := by
    refine ⟨?_, _, rfl⟩
    rw [hj0]
    exact ⟨p8, z1, z2, s1, σ1, hs8, hr, hinv, he.clean (clean_zero (fun _ => rfl) (fun _ => rfl))⟩
  have hc0 : (run P w (initBit d n m A b) (6 + n1 + 2)).cost ≤ (initBit d n m A b).cost + costP ℓa ℓ Ks := by
    rw [hj0]
    have : k * xstepCost ℓa ℓ ≤ Ks * xstepCost ℓa ℓ := Nat.mul_le_mul_right _ hk
    show t8.cost ≤ 0 + costP ℓa ℓ Ks
    unfold costP; omega
  -- the checkpoints
  have hS : ∀ a, Start a → SpaceLE a (ckSpace d n m M ℓa ℓ : ℝ) := by
    rintro a ⟨⟨-, h1, h2, s, σ, hs, -, -, hcl⟩, -⟩
    have := space_checkpoint (ℓi := len (d : ℤ) + len (n : ℤ) + len (m : ℤ) + len (M : ℤ)) hs hcl h1 h2
      (fun j _ => Conj1BitSanity.len_inputMem_le hH _) hoffX h4
    unfold ckSpace
    exact this
  -- a round
  have hseg : ∀ a, Start a → a.rounds < n → ∃ j, Start (run P w a j) ∧ a.rounds < (run P w a j).rounds ∧
      (run P w a j).cost ≤ a.cost + costR ℓa ℓ Kr := by
    rintro a ⟨⟨hpc, -, -, s, σ, hs, hr, hinv, hcl⟩, ka, rfl⟩ hlt
    have hσ : σ.rounds < n := by rw [← hr.rounds, ← hs.rounds]; exact hlt
    have hpl : ∀ i < σ.rounds, playedBit P g (initBit d n m A b) i = σ.pts i := fun i hi => by
      have hi' : i < (runBit P g (initBit d n m A b) ka).rounds := by
        rw [eR, hs.rounds, hr.rounds]; exact hi
      rw [Conj1BitSanity.playedBit_eq P g _ ka i hi', eR, hs.pts, hr.pts]
    obtain ⟨k, s', σ', hk, he, hr', hinv', hlt'⟩ := hround σ hinv hσ hpl s hr
    obtain ⟨n1, -, t1, e1, p1, hs1, c1⟩ := xtransfer hoffX he _ _ cR hpc hs
    obtain ⟨t2, e2, p2, hs2, c2⟩ := xsim_jmp cJ p1 hs1
    obtain ⟨t3, e3, p3, hs3, z1, z2, c3⟩ := zero_scratch cZ1 cZ2 p2 hs2
    have hr3 : run P w (run P w (initBit d n m A b) ka) (n1 + 1 + 2) = t3 := by
      rw [B.run_add, B.run_add]
      exact (congrArg (fun t => run P w t 2) ((congrArg (fun t => run P w t 1) e1).trans e2)).trans e3
    refine ⟨n1 + 1 + 2, ?_, ?_, ?_⟩
    · refine ⟨?_, ka + (n1 + 1 + 2), by simp only [B.run_add]⟩
      rw [hr3]
      exact ⟨p3, z1, z2, s', σ', hs3, hr', hinv', he.clean hcl⟩
    · rw [hr3, hs3.rounds, hr'.rounds, hs.rounds, hr.rounds]
      exact hlt'
    · have : k * xstepCost ℓa ℓ ≤ Kr * xstepCost ℓa ℓ := Nat.mul_le_mul_right _ hk
      rw [hr3]
      unfold costR; omega
  -- every round `t < n` is played at some checkpoint
  have hall : ∀ t < n, ∃ a, Start a ∧ t < a.rounds := by
    intro t ht
    suffices H : ∀ j a, Start a → t + 1 - a.rounds ≤ j → ∃ a', Start a' ∧ t < a'.rounds from H _ _ hst le_rfl
    intro j
    induction j with
    | zero => exact fun a ha h => ⟨a, ha, by omega⟩
    | succ j ih =>
      intro a ha h
      by_cases hlt : t < a.rounds
      · exact ⟨a, ha, hlt⟩
      · obtain ⟨j', h1, h2, -⟩ := hseg a ha (by omega)
        exact ih _ h1 (by omega)
  obtain ⟨hC, hSp⟩ := driver_bit g hw.symm Start (input_spaceLE hH) (6 + n1 + 2) hst hc0 hS hseg
  refine ⟨hC, hSp, fun t ht => ?_⟩
  obtain ⟨_, ⟨⟨-, -, -, s, σ, hs, hr, hinv, -⟩, ka, rfl⟩, hta⟩ := hall t ht
  have hσ : t < σ.rounds := by rw [← hr.rounds, ← hs.rounds]; exact hta
  have hi' : t < (runBit P g (initBit d n m A b) ka).rounds := by rw [eR]; exact hta
  refine ⟨σ, hinv, hσ, ?_⟩
  rw [Conj1BitSanity.playedBit_eq P g _ ka t hi', eR, hs.pts, hr.pts]

/-- `prog_okR` in the form of the frozen statement. -/
theorem prog_ok_frozenR {L : Poly.Mach.Layout} {ℓa ℓ Ks Kr : ℕ} {setup round : XCmd} {Inv : Poly.Mach.«Env» d → Prop}
    {n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} (hH : RealRAM.HeightLE A b M) (g : GameBit d)
    (hoff : offOf d m < 2 ^ ℓa) (h4 : 4 ≤ 2 ^ ℓa) (hd : d + 1 < 2 ^ ℓa)
    (hsetup : ∃ k s1 σ1, k ≤ Ks ∧
      XExecB (ctxOf (gameWorld (prog setup round) g (initBit d n m A b)) n m A b) ℓa ℓ setup zeroState k s1 ∧
      Poly.Mach.Rep L σ1 s1 ∧ Inv σ1)
    (hround : ∀ σ, Inv σ → σ.rounds < n →
      (∀ i < σ.rounds, playedBit (prog setup round) g (initBit d n m A b) i = σ.pts i) →
      XRunsB L (ctxOf (gameWorld (prog setup round) g (initBit d n m A b)) n m A b) ℓa ℓ round σ Kr
        (fun σ' => Inv σ' ∧ σ.rounds < σ'.rounds))
    (c : ℝ) (k : ℕ) (hc : 0 ≤ c) (hd1 : 1 ≤ d) (hn : 1 ≤ n) (hm : 1 ≤ m) (hM : 1 ≤ M)
    (hBc : ((costP ℓa ℓ Ks + 2 * costR ℓa ℓ Kr : ℕ) : ℝ) ≤ c * ((d : ℝ) * m * (n.size + 1) * (M.size + 1)) ^ k)
    (hBs : max (inSpace d n m M : ℝ) (ckSpace d n m M ℓa ℓ : ℝ) + ((costP ℓa ℓ Ks + costR ℓa ℓ Kr : ℕ) : ℝ) ≤
      c * ((d : ℝ) * m * (n.size + 1) * (M.size + 1)) ^ k) :
    CostOKBit (prog setup round) g (initBit d n m A b) n
        (c * (4 / Real.log 2 ^ 2) ^ k * ((d : ℝ) * m * Real.log (2 * d * n) * Real.log (2 * M)) ^ k) ∧
      SpaceOKBit (prog setup round) g (initBit d n m A b) n
        (c * (4 / Real.log 2 ^ 2) ^ k * ((d : ℝ) * m * Real.log (2 * d * n) * Real.log (2 * M)) ^ k) ∧
      ∀ t < n, ∃ σ, Inv σ ∧ t < σ.rounds ∧ playedBit (prog setup round) g (initBit d n m A b) t = σ.pts t := by
  obtain ⟨h1, h2, h3⟩ := prog_okR hH g hoff h4 hd hsetup hround
  have hf := frozen_form d m n M k c hc hd1 hn hm hM
  exact ⟨costOKBit_mono h1 (hBc.trans hf), spaceOKBit_mono h2 (hBs.trans hf), h3⟩

end AdversarialBco.Bit.Transfer
