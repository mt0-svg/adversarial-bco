/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XDrvReach
public import AdversarialBco.Bit.Transfer.XBLRound
public import AdversarialBco.Bit.Transfer.XBLMag
public import AdversarialBco.Bit.ApQ.FrameB
public import AdversarialBco.Bit.BLEngine
public import AdversarialBco.Conj1.RunAd

@[expose] public section

/-!
# BL's program driver: the invariant and the round

* `play_in_K`: every play of BL's pure run is in the polytope (mode `off`: the frame centre, `frameQ_ball`; mode
  `guard`: `μ_S`, inside since mode `run` held at the start, every kept `β̃_i > 0`; mode `run`: `play_mem`);
* `DrvInv`: the invariant at a checkpoint of the driver, BL's invariant before some round `t ≤ n` with the points of
  the rounds before `t` BL's plays;
* `RoundSpec`: the body of `RoundBL` for a given command and constants;
* `drv_round`: the hypothesis `hround` of `prog_okR` from `RoundSpec`, in the game world, the losses of the world
  read on the points of the run (`lossAd_congr`, `traj_hist`).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ
  AdversarialBco.Bit.Asm Matrix
open AdversarialBco.BitRAM (toE playedBit GameBit State initBit Instr)
open AdversarialBco.RealRAM (Strategy polytope HeightLE)

variable {d : ℕ}

/-! ## The plays are in the polytope -/

/-- Mode `guard` comes only after mode `run` at the start. -/
theorem modeAt_guard (R : Routines) (n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d)
    (cs : ℕ → Bool) : ∀ t : ℕ, modeAt R d n m A b σ cs t = .guard → ∃ st0, mode0 (cfgOf R d n m A b cs) = .run st0
  | 0, h => by
    unfold modeAt at h
    simp only [traj] at h
    unfold mode0 at h
    split_ifs at h
  | t + 1, h => by
    unfold modeAt at h
    simp only [traj] at h
    rcases hm : (traj R d n m A b σ cs t).1 with _ | _ | st1
    · rw [hm] at h; cases h
    · exact modeAt_guard R n m A b σ cs t hm
    · exact modeAt_run R n m A b σ cs t st1 hm

/-- **Every play of BL's pure run is in the polytope.** -/
theorem play_in_K {n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} (hI : InputOK d n m M A b)
    (σ : Strategy d) (cs : ℕ → Bool) (t : ℕ) : toE (play RoutinesQ d n m A b σ cs t) ∈ polytope A b := by
  have hd := hI.hd
  have hn := hI.hn
  unfold play
  rcases hmo : modeAt RoutinesQ d n m A b σ cs t with _ | _ | st
  · exact (ApQ.frameQ_ball hI).1 (Metric.mem_closedBall_self (by norm_num))
  · obtain ⟨st0, h0⟩ := modeAt_guard RoutinesQ n m A b σ cs t hmo
    obtain ⟨-, hβ, -⟩ := mode0_run h0
    intro i
    have key : A i ⬝ᵥ (cfgOf RoutinesQ d n m A b cs).μS ≤ b i := by
      by_cases hA : A i = 0
      · rw [hA, zero_dotProduct]; exact hzero_of hI i hA
      obtain ⟨k, hk⟩ := kept_get A i hA
      have hβk := hβ k
      have hβe : (cfgOf RoutinesQ d n m A b cs).β k = b i - A i ⬝ᵥ (cfgOf RoutinesQ d n m A b cs).μS := by
        rw [← hk]; rfl
      rw [hβe] at hβk
      linarith
    have e : ∑ j, (A i j : ℝ) * (toE (playPt (cfgOf RoutinesQ d n m A b cs) .guard
        (drawAt RoutinesQ d n cs t).1)) j = ((A i ⬝ᵥ (cfgOf RoutinesQ d n m A b cs).μS : ℚ) : ℝ) := by
      simp [dotProduct, toE, playPt]
    rw [e]
    exact_mod_cast key
  · obtain ⟨st0, h0⟩ := modeAt_run RoutinesQ n m A b σ cs t st hmo
    obtain ⟨heps, hβ, -⟩ := mode0_run h0
    exact play_mem A b _ _ st _ (hzero_of hI) heps (eps_nonneg hd hn) hβ

/-! ## The invariant of the driver and the round -/

/-- The invariant at a checkpoint of the driver: BL's invariant before some round `t ≤ n`, with the mode of BL's
pure run before round `t` and the points of the rounds before `t` BL's plays. -/
def DrvInv (L : Layout) (n m E : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σs : Strategy d)
    (cs : ℕ → Bool) (σ : Env d) : Prop :=
  ∃ t ≤ n, BLInv L n m (K0Q d n) E (cfgOf RoutinesQ d n m A b cs) (modeAt RoutinesQ d n m A b σs cs t) t σ ∧
    ∀ i < t, σ.pts i = toE (play RoutinesQ d n m A b σs cs i)

/-- The body of `RoundBL` for the command `xround` and the constants `C, k, Cn, kn, nS, nN, nA`. -/
def RoundSpec (xround : Layout → XCmd) (C k Cn kn nS nN nA : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (w : BitRAM.World d) (n m M E0 E ℓa ℓ t : ℕ) (A : Matrix (Fin m) (Fin d) ℚ)
    (b : Fin m → ℚ) (σs : Strategy d) (σ : Env d),
    InputOK d n m M A b → AdmStrat (polytope A b) n σs → t < n →
    (∀ x, w.f t x =
      RealRAM.lossAd σs 0 (fun i => BitRAM.toE ((traj RoutinesQ d n m A b σs w.cs (t + 1)).2 i)) t x) →
    LayOK L d ℓa → BLLay L → blkBL.OK L nS nN nA →
    PosBnd (cfgOf RoutinesQ d n m A b w.cs) E0 → Cn * (d + m + M.size + n.size + E0 + 1) ^ kn ≤ E →
    C * (d + m + M.size + n.size + E + 1) ^ k ≤ ℓ → C * (d + m + M.size + n.size + E + 1) ^ k < 2 ^ ℓa →
    BLInv L n m (K0Q d n) E (cfgOf RoutinesQ d n m A b w.cs) (modeAt RoutinesQ d n m A b σs w.cs t) t σ →
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xround L) σ (C * (d + m + M.size + n.size + E + 1) ^ k) (fun σ' =>
      BLInv L n m (K0Q d n) E (cfgOf RoutinesQ d n m A b w.cs) (modeAt RoutinesQ d n m A b σs w.cs (t + 1))
        (t + 1) σ' ∧
      σ'.pts = Function.update σ.pts t (BitRAM.toE (play RoutinesQ d n m A b σs w.cs t)))

theorem roundSpec_of (h : RoundBL) : ∃ (xround : Layout → XCmd) (C k Cn kn nS nN nA : ℕ),
    RoundSpec xround C k Cn kn nS nN nA := h

/-- **The hypothesis `hround` of `prog_okR`** in the game world of the program `P`, from `RoundSpec`. -/
theorem drv_round {xround : Layout → XCmd} {C k Cn kn nS nN nA : ℕ} (hR : RoundSpec xround C k Cn kn nS nN nA)
    {L : Layout} {n m M E0 E ℓa ℓ : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} (hI : InputOK d n m M A b)
    (g : GameBit d) (hσ : AdmStrat (polytope A b) n g.σ) (hL : LayOK L d ℓa) (hlay : BLLay L)
    (hOK : blkBL.OK L nS nN nA) (hP : PosBnd (cfgOf RoutinesQ d n m A b g.cs) E0)
    (hE : Cn * (d + m + M.size + n.size + E0 + 1) ^ kn ≤ E)
    (hℓ : C * (d + m + M.size + n.size + E + 1) ^ k ≤ ℓ) (hℓa : C * (d + m + M.size + n.size + E + 1) ^ k < 2 ^ ℓa)
    (P : List Instr) (s0 : State d) :
    ∀ σ, DrvInv L n m E A b g.σ g.cs σ → σ.rounds < n → (∀ i < σ.rounds, playedBit P g s0 i = σ.pts i) →
      XRunsB L (ctxOf (gameWorld P g s0) n m A b) ℓa ℓ (xround L) σ (C * (d + m + M.size + n.size + E + 1) ^ k)
        (fun σ' => DrvInv L n m E A b g.σ g.cs σ' ∧ σ.rounds < σ'.rounds) := by
  rintro σ ⟨t, -, hinv, hpts⟩ hlt hpl
  have hrt : σ.rounds = t := hinv.rounds
  have ht : t < n := by omega
  have hw : ∀ x, (gameWorld P g s0).f t x = RealRAM.lossAd g.σ 0
      (fun i => toE ((traj RoutinesQ d n m A b g.σ (gameWorld P g s0).cs (t + 1)).2 i)) t x := fun x => by
    show RealRAM.lossAd g.σ 0 (playedBit P g s0) t x = _
    rw [Poly.Conj1.lossAd_congr g.σ 0 t (y := fun i => toE ((traj RoutinesQ d n m A b g.σ g.cs (t + 1)).2 i))
      (fun i hi => by rw [hpl i (by omega), hpts i hi, traj_hist RoutinesQ d n m A b g.σ g.cs (t + 1) i (by omega)])]
    rfl
  refine XV.mono (hR d L (gameWorld P g s0) n m M E0 E ℓa ℓ t A b g.σ σ hI hσ ht hw hL hlay hOK hP hE hℓ hℓa hinv)
    le_rfl ?_
  rintro σ' ⟨hinv', hpts'⟩
  refine ⟨⟨t + 1, ht, hinv', fun i hi => ?_⟩, by rw [hinv'.rounds]; omega⟩
  rw [hpts']
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
  · rw [Function.update_of_ne h.ne]; exact hpts i h
  · rw [Function.update_self]; rfl

/-- The invariant after the setup: round `0`, the mode `mode0`, no point yet. -/
theorem drv_init {L : Layout} {n m E : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} (σs : Strategy d)
    (cs : ℕ → Bool) {σ : Env d}
    (h : BLInv L n m (K0Q d n) E (cfgOf RoutinesQ d n m A b cs) (mode0 (cfgOf RoutinesQ d n m A b cs)) 0 σ) :
    DrvInv L n m E A b σs cs σ :=
  ⟨0, Nat.zero_le _, h, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

/-- The plays of the program are BL's plays: from the checkpoint of `prog_okR` at which round `t` is played. -/
theorem drv_play {L : Layout} {n m E : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {σs : Strategy d}
    {cs : ℕ → Bool} {x : AdversarialBco.E d} {t : ℕ}
    (h : ∃ σ, DrvInv L n m E A b σs cs σ ∧ t < σ.rounds ∧ x = σ.pts t) :
    x = toE (play RoutinesQ d n m A b σs cs t) := by
  obtain ⟨σ, ⟨t', -, hinv, hpts⟩, ht, rfl⟩ := h
  exact hpts t (by rw [← hinv.rounds]; exact ht)

end AdversarialBco.Bit.Transfer.BLM
