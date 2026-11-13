/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XDrvPoly
public import AdversarialBco.Bit.Transfer.XFrameRule
public import AdversarialBco.Bit.Transfer.XTriWork
public import AdversarialBco.Bit.BLRunOK
public import AdversarialBco.Bit.BLPosQ
public import AdversarialBco.Bit.BLPosTri
public import AdversarialBco.Bit.BLRoundC2
public import AdversarialBco.Bit.BLRoundPlay
public import AdversarialBco.Bit.PieceB
public import AdversarialBco.Bit.PieceA.BudA
public import AdversarialBco.Bit.ApQ.Spec

@[expose] public section

/-!
# BL's program and the upper bound

* `progBL`: the program `prog (xsetupBL L xframe xtri) (xround L)` on the layout `DrvK.L` of the constants;
* `drv_main`: on every input of the frozen statement, against every admissible strategy and on every coin sequence,
  the cost and space clauses with `C' (d m log (2 d n) log (2 M))^k` and the plays of the rounds `t < n` BL's pure
  plays: the setup by `setupBL_ok'`, the rounds by `drv_round`, the driver by `prog_ok_frozenR`, the parameters by
  `drv_poly`;
* `drv_machOK`, `drv_link`: `MachOK` and `BLLink` for `progBL`;
* `theoremConj1UpperBit_of_roundBL`: `RoundBL → TheoremConj1UpperBit`, through `theoremConj1UpperBit_of`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ
  AdversarialBco.Bit.Asm
open AdversarialBco.BitRAM (toE playedBit GameBit initBit Instr CostOKBit SpaceOKBit)
open AdversarialBco.RealRAM (Strategy polytope)

/-- BL's program on the layout of the constants `K`. -/
def progBL (xframe xtri : Layout → PrBlk → XCmd) (xround : Layout → XCmd) (K : DrvK) : List Instr :=
  prog (xsetupBL K.L xframe xtri) (xround K.L)

namespace DrvK

variable (K : DrvK)

theorem blLay : BLLay K.L := by
  simp only [BLLay, DrvK.L, oE, rEE, aWE]
  omega

theorem blkBL_okK : blkBL.OK K.L K.nS K.nN K.nA :=
  blkBL_ok (by simp only [DrvK.L, oE]; omega) (by simp only [DrvK.L, rEE]; omega) (by simp only [DrvK.L, aWE]; omega)

theorem blkS_okF : blkS.OK K.L K.nSf K.nNf K.nAf := by
  simp only [PrBlk.OK, blkS, DrvK.L, rD, rM, sN, aC]
  omega

theorem blkS_okT : blkS.OK K.L K.nSt K.nNt K.nAt := by
  simp only [PrBlk.OK, blkS, DrvK.L, rD, rM, sN, aC]
  omega

end DrvK

/-- **BL's program on one input**: the cost and space clauses with `C' (d m log (2 d n) log (2 M))^k`,
`C' = c (4 / (log 2)^2)^k`, and the plays of the rounds `t < n` BL's pure plays. -/
theorem drv_main {xframe xtri : Layout → PrBlk → XCmd} {xround : Layout → XCmd} (K : DrvK)
    (hR : RoundSpec xround K.C K.k K.Cn K.kn K.nS K.nN K.nA) (hF : FrameSpec xframe K.Cf K.kf K.nSf K.nNf K.nAf)
    (hT : TriSpec xtri K.Ct K.kt K.nSt K.nNt K.nAt) : ∃ c k : ℕ,
    ∀ (d n m M : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ), InputOK d n m M A b →
    ∀ σs : Strategy d, AdmStrat (polytope A b) n σs → ∀ cs : ℕ → Bool,
      CostOKBit (progBL xframe xtri xround K) ⟨σs, cs⟩ (initBit d n m A b) n
          ((c : ℝ) * (4 / Real.log 2 ^ 2) ^ k * ((d : ℝ) * m * Real.log (2 * d * n) * Real.log (2 * M)) ^ k) ∧
        SpaceOKBit (progBL xframe xtri xround K) ⟨σs, cs⟩ (initBit d n m A b) n
          ((c : ℝ) * (4 / Real.log 2 ^ 2) ^ k * ((d : ℝ) * m * Real.log (2 * d * n) * Real.log (2 * M)) ^ k) ∧
        ∀ t < n, playedBit (progBL xframe xtri xround K) ⟨σs, cs⟩ (initBit d n m A b) t =
          toE (play RoutinesQ d n m A b σs cs t) := by
  obtain ⟨c, k, hck⟩ := drv_poly K
  refine ⟨c, k, fun d n m M A b hI σs hσ cs => ?_⟩
  unfold progBL
  have hd := hI.hd
  have hn := hI.hn
  have hm := inputOK_m_pos hI
  have hM := inputOK_M_pos hI
  have hQ := K.Q_lt d n m M A b
  have hQ' := hQ
  unfold DrvK.Q at hQ'
  have hKr : K.Kr d n m M A b < 2 ^ K.ella d n m M A b := by omega
  have hLay : LayOK K.L d (K.ella d n m M A b) := by
    unfold LayOK
    omega
  have hE := (Nat.le_add_left (K.Cn * (d + m + M.size + n.size + K.E0 d n m A b + 1) ^ K.kn)
    (K.ES d n m M A b)).trans_eq (rfl : _ = K.E d n m M A b)
  have hES : K.ES d n m M A b ≤ K.E d n m M A b := Nat.le_add_right _ _
  unfold DrvK.ES at hES
  have hME : M ≤ 2 ^ K.E d n m M A b :=
    (Nat.lt_size_self M).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hmE : m ≤ 2 ^ K.E d n m M A b := (Nat.lt_two_pow_self (n := m)).le.trans
    (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hℓs : 3 * (K.E d n m M A b * d) + 10 * K.E d n m M A b + 5 ≤ K.ell d n m M A b := by
    unfold DrvK.ell
    omega
  have hℓr : K.Kr d n m M A b ≤ K.ell d n m M A b := by
    unfold DrvK.ell
    omega
  obtain ⟨ks, s1, σ1, hks, hex, hrep, ⟨hinv, -⟩, hpos⟩ :=
    setupBL_ok' hF hT hLay K.blLay K.blkS_okF K.blkS_okT hd hn hI.height hM (by omega) (by omega) (by omega) hME hmE
      hℓs (by omega) (gameWorld (prog (xsetupBL K.L xframe xtri) (xround K.L)) ⟨σs, cs⟩ (initBit d n m A b))
  have hround := drv_round hR hI ⟨σs, cs⟩ hσ hLay K.blLay K.blkBL_okK hpos hE hℓr hKr
    (prog (xsetupBL K.L xframe xtri) (xround K.L)) (initBit d n m A b)
  obtain ⟨h1, h2, h3⟩ := prog_ok_frozenR hI.height ⟨σs, cs⟩ (by omega) (by omega) (by omega)
    ⟨ks, s1, σ1, hks, hex, hrep, drv_init σs cs hinv⟩ hround (c : ℝ) k (Nat.cast_nonneg c) hd hn hm hM
    (by
      have h := (hck d n m M A b hI).1
      unfold DrvK.cost DrvK.Kr at h
      exact_mod_cast h)
    (by
      have h := (hck d n m M A b hI).2
      unfold DrvK.space DrvK.Kr at h
      exact_mod_cast h)
  exact ⟨h1, h2, fun t ht => drv_play (h3 t ht)⟩

/-- **`MachOK` for BL's program.** -/
theorem drv_machOK {xframe xtri : Layout → PrBlk → XCmd} {xround : Layout → XCmd} (K : DrvK)
    (hR : RoundSpec xround K.C K.k K.Cn K.kn K.nS K.nN K.nA) (hF : FrameSpec xframe K.Cf K.kf K.nSf K.nNf K.nAf)
    (hT : TriSpec xtri K.Ct K.kt K.nSt K.nNt K.nAt) : ∃ (C' : ℝ) (k : ℕ), MachOK (progBL xframe xtri xround K) C' k := by
  obtain ⟨c, k, h⟩ := drv_main K hR hF hT
  refine ⟨(c : ℝ) * (4 / Real.log 2 ^ 2) ^ k, k, fun d n m M A b hI σs hσ cs => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h d n m M A b hI σs hσ cs
  refine ⟨h1, h2, fun t ht => ?_⟩
  rw [h3 t ht]
  exact play_in_K hI σs cs t

/-- **`BLLink` for BL's program**, on every input (the hypothesis `RunCase` unused). -/
theorem drv_link {xframe xtri : Layout → PrBlk → XCmd} {xround : Layout → XCmd} (K : DrvK)
    (hR : RoundSpec xround K.C K.k K.Cn K.kn K.nS K.nN K.nA) (hF : FrameSpec xframe K.Cf K.kf K.nSf K.nNf K.nAf)
    (hT : TriSpec xtri K.Ct K.kt K.nSt K.nNt K.nAt) : BLLink (progBL xframe xtri xround K) RoutinesQ := by
  obtain ⟨c, k, h⟩ := drv_main K hR hF hT
  intro d n m M A b hI _ σs hσ cs t ht
  exact (h d n m M A b hI σs hσ cs).2.2 t ht

/-- **The upper bound of the frozen statement from `RoundBL`.** -/
theorem theoremConj1UpperBit_of_roundBL (h : RoundBL) : TheoremConj1UpperBit := by
  obtain ⟨xround, C, k, Cn, kn, nS, nN, nA, hR⟩ := roundSpec_of h
  obtain ⟨xframe, Cf, kf, nSf, nNf, nAf, hF⟩ := frameRule_iff.1 frameRule
  obtain ⟨xtri, Ct, kt, nSt, nNt, nAt, hT⟩ := triRule_iff.1 triRule
  let K : DrvK := ⟨C, k, Cn, kn, nS, nN, nA, Cf, kf, nSf, nNf, nAf, Ct, kt, nSt, nNt, nAt⟩
  obtain ⟨C', k', hM⟩ := drv_machOK K hR hF hT
  exact theoremConj1UpperBit_of (blInst (progBL xframe xtri xround K) RoutinesQ) C' k'
    ⟨hM, runOK_of (drv_link K hR hF hT) ApQ.o3SpecQ_apQ posLocalQ PieceA.budA PieceB.bitsB PieceB.measDrawB RC.playC
      RC.roundC, posInst_routinesQ _⟩

end AdversarialBco.Bit.Transfer.BLM
