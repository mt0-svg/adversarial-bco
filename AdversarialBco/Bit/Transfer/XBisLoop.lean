/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XEllLoop

@[expose] public section

/-!
# The loop of BIS-R on the machine

`xbisLoop` runs `bisLoop I N lo hi kept` (Bit/RoutQ.lean) for `d = 1`: the interval `[lo, hi]` in the slots `P + 9`,
`P + 10`, the kept point in `P + 1`, `P + 2` and the array `kb`. Each turn: the midpoint `(lo + hi)/2` into `P + 11`
and the cell `0` of the array `a0 + 1`, the tests (`xtest` at the scale `2^s`), then on a cut the test `c = 0`
(`xtestEnd`) and the halving by the sign of `c₀`. The outcome in `P + 8` as for ELL-R (`XEllLoop.lean`).
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## The program -/

/-- The midpoint `(lo + hi)/2` (`2` in `u + 2`) into `P + 11` and the cell `0` of the array `a0 + 1`. -/
def xbisMid (L : Layout) (P u a0 n0 : ℕ) : XCmd :=
  .seq ((IE.ediv (.op .add (.sc (P + 9)) (.sc (P + 10))) (.sc (u + 2))).code L u (u + 13) (u + 14))
  (.seq (xset L (P + 11) (u + 13) u)
  (.seq (.prim (.frag (.nconst (n0 + 3) 0))) (toX (VL.aset L (a0 + 1) (n0 + 3) (P + 11)))))

/-- The halving: `hi := mid` when the entry `c₀` of the cut is positive, else `lo := mid`; the next turn. -/
def xbisHalve (L : Layout) (P u a0 n0 : ℕ) : XCmd :=
  .seq (toX (VL.aget L (u + 13) (a0 + 2) (n0 + 3)))
  (.seq (xifS L u (u + 13) (xset L (P + 10) (P + 11) u) (xset L (P + 9) (P + 11) u))
    (.prim (.frag (.nadd (n0 + 6) (n0 + 6) (n0 + 4)))))

/-- One turn of BIS-R. -/
def xbisBody (L : Layout) (B : EllBlk) (rowc : XCmd) (P u a0 kb n0 : ℕ) : XCmd :=
  .seq (xbisMid L P u a0 n0)
  (.seq (xtest L B rowc P u a0 kb n0 (n0 + 4) (n0 + 5))
  (xifS L u P (xellStop L P u n0 (u + 2))
    (.seq (xtestEnd L B P u a0 n0 (n0 + 4))
      (xifS L u P (xellStop L P u n0 (u + 1)) (xbisHalve L P u a0 n0)))))

/-- The loop: the turn to `0`, the outcome to `0`, at most `nat (n0 + 7)` turns. -/
def xbisLoop (L : Layout) (B : EllBlk) (rowc : XCmd) (P u a0 kb n0 : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst (n0 + 6) 0))) (.seq (xset L (P + 8) u u)
    (.whileN (n0 + 6) (n0 + 7) (xbisBody L B rowc P u a0 kb n0)))

/-! ## Unfolding `bisLoop` -/

theorem bisLoop_ret {I : EllI d} {k : ℕ} {lo hi : ℤ} {kept : Option ((Fin d → ℤ) × ℤ)} {x : Fin d → ℤ}
    (h : ellTest I (I.lam + 1) (fun _ => (lo + hi) / 2) kept = .ret x) : bisLoop I (k + 1) lo hi kept = some x := by
  rw [bisLoop, h]

theorem bisLoop_zero {I : EllI d} {k : ℕ} {lo hi : ℤ} {kept kept' : Option ((Fin d → ℤ) × ℤ)} {c : Fin d → ℤ}
    (h : ellTest I (I.lam + 1) (fun _ => (lo + hi) / 2) kept = .cut c kept') (hc : c = 0) :
    bisLoop I (k + 1) lo hi kept = kept'.map Prod.fst := by
  rw [bisLoop, h]; simp [hc]

theorem bisLoop_hi {I : EllI d} {k : ℕ} {lo hi : ℤ} {kept kept' : Option ((Fin d → ℤ) × ℤ)} {c : Fin d → ℤ}
    (h : ellTest I (I.lam + 1) (fun _ => (lo + hi) / 2) kept = .cut c kept') (hc : c ≠ 0) (hs : 0 < ∑ i, c i) :
    bisLoop I (k + 1) lo hi kept = bisLoop I k lo ((lo + hi) / 2) kept' := by
  rw [bisLoop, h]; simp [hc, hs]

theorem bisLoop_lo {I : EllI d} {k : ℕ} {lo hi : ℤ} {kept kept' : Option ((Fin d → ℤ) × ℤ)} {c : Fin d → ℤ}
    (h : ellTest I (I.lam + 1) (fun _ => (lo + hi) / 2) kept = .cut c kept') (hc : c ≠ 0) (hs : ¬ 0 < ∑ i, c i) :
    bisLoop I (k + 1) lo hi kept = bisLoop I k ((lo + hi) / 2) hi kept' := by
  rw [bisLoop, h]; simp [hc, hs]

theorem abs_mid_le {lo hi M : ℤ} (hl : |lo| ≤ M) (hh : |hi| ≤ M) : |(lo + hi) / 2| ≤ M := by
  rw [abs_le] at hl hh ⊢
  constructor <;> omega

/-! ## The loop on the machine -/

/-- The cells of BIS-R above those of ELL-R: the interval and the midpoint in `P + 9, P + 10, P + 11`. -/
structure BisLay (L : Layout) (B : EllBlk) (P u a0 kb n0 : ℕ) : Prop where
  loop : LoopLay L B P u a0 kb n0
  PS : P + 12 ≤ u

/-- The slots BIS-R may change. -/
abbrev bisS (B : EllBlk) (P u : ℕ) (SR : ℕ → Prop) (y : ℕ) : Prop :=
  ((P ≤ y ∧ y ≤ P + 11 ∧ (y < P + 3 ∨ P + 6 < y)) ∨ u + 13 ≤ y ∨ y = B.o + 2) ∨ SR y

/-- The invariant of BIS-R after `t` turns from `σ`, as `LoopInv` with the interval `[lo, hi]` (below `M`) in the
place of the state of ELL-R. -/
def BisInv (B : EllBlk) (I : EllI d) (P u a0 n0 F N : ℕ) (M : ℤ) (SR NR AR : ℕ → Prop) (lo0 hi0 : ℤ)
    (kept0 : Option ((Fin d → ℤ) × ℤ)) (σ : Env d) (t : ℕ) (σ' : Env d) : Prop :=
  σ'.draws = σ.draws ∧ FrameA (bisS B P u SR) (loopN B n0 NR) (loopA B a0 AR) σ σ' ∧
    σ'.nat (n0 + 6) ≤ N ∧ σ'.nat (n0 + 7) ≤ N ∧
    ((σ'.sc (P + 8) = 0 ∧ σ'.nat (n0 + 7) = N ∧ σ'.nat (n0 + 6) = t ∧
        ∃ (lo hi : ℤ) (kept : Option ((Fin d → ℤ) × ℤ)), σ'.sc (P + 9) = lo ∧ σ'.sc (P + 10) = hi ∧ |lo| ≤ M ∧
          |hi| ≤ M ∧ KeptIn P (a0 + 6) kept σ' ∧ KeptOK M F kept ∧
          bisLoop I N lo0 hi0 kept0 = bisLoop I (N - t) lo hi kept) ∨
      (σ'.sc (P + 8) = 1 ∧ σ'.nat (n0 + 7) = 0 ∧
        ∃ kept, KeptOK M F kept ∧ KeptIn P (a0 + 6) kept σ' ∧ bisLoop I N lo0 hi0 kept0 = kept.map Prod.fst) ∨
      (σ'.sc (P + 8) = 2 ∧ σ'.nat (n0 + 7) = 0 ∧
        ∃ x, bisLoop I N lo0 hi0 kept0 = some x ∧ (∀ k : Fin d, σ'.arr (a0 + 1) k = x k) ∧ ∀ k, |x k| ≤ M))

/-- The units of one turn. -/
def bisKb (d m Kr : ℕ) : ℕ := 9 + (testK d m Kr + (tKE d + 8 + 2))

set_option maxHeartbeats 4000000 in
/-- The rule of `xbisMid`. -/
theorem XV.bisMid {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {P u a0 n0 F : ℕ}
    {lo hi : ℤ} (hd : 1 ≤ d) (hPu : P + 12 ≤ u) (hS : u + 18 ≤ L.NS) (hA : a0 + 1 < L.NA) (hN : n0 + 3 < L.NN)
    (hz : σ.sc u = 0) (h2 : σ.sc (u + 2) = 2) (hlo : σ.sc (P + 9) = lo) (hhi : σ.sc (P + 10) = hi)
    (blo : |lo| ≤ 2 ^ F) (bhi : |hi| ≤ 2 ^ F) (hF : 1 ≤ F) (hℓ : F + 1 < ℓ) :
    XRunsB L X ℓa ℓ (xbisMid L P u a0 n0) σ 9 (fun σ' =>
      σ'.sc (P + 11) = (((lo + hi) / 2 : ℤ) : ℝ) ∧ σ'.arr (a0 + 1) 0 = (((lo + hi) / 2 : ℤ) : ℝ) ∧
      σ'.nat (n0 + 3) = 0 ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => y = P + 11 ∨ u + 13 ≤ y) (fun j => j = n0 + 3) (fun b k => b = a0 + 1 ∧ k = 0) σ σ') := by
  have hda := asz_lt hL hA
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by simp only [abs_zero]; positivity
  have b2 : |(2 : ℤ)| ≤ 2 ^ F := by
    rw [abs_two]; exact le_trans (by norm_num) (pow_le_pow_right₀ (by norm_num) hF)
  have bm : |(lo + hi) / 2| ≤ 2 ^ F := abs_mid_le blo bhi
  have bmℓ : |(((lo + hi) / 2 : ℤ) : ℝ)| < 2 ^ ℓ := absR_lt bm (by omega)
  refine XV.seq (K₂ := 4) (XV.ieRun (E := F) (e := IE.ediv (.op .add (.sc (P + 9)) (.sc (P + 10))) (.sc (u + 2)))
    (v := (lo + hi) / 2) hL (x := u + 13) (t := u + 14) (z := u)
    (by simp only [IE.WF]; exact ⟨⟨(by intro h; cases h), by omega, by omega⟩, by omega⟩) (by omega) (by omega)
    (by simp only [IE.scr]; omega) hz
    (by simp only [IE.Leaves]; exact ⟨⟨⟨lo, hlo, blo⟩, ⟨hi, hhi, bhi⟩⟩, ⟨2, by rw [h2]; norm_num, b2⟩⟩)
    (by simp only [IE.top, IE.mag]; omega) (by
      simp only [IE.eval, RealRAM.Op2.eval, hlo, hhi, h2]
      rw [show (lo : ℝ) + hi = ((lo + hi : ℤ) : ℝ) by push_cast; ring, Int.floor_intCast,
        show (2 : ℝ) = ((2 : ℤ) : ℝ) by norm_num, Int.floor_intCast])) fun σ1 ⟨m1, _, d1, F1⟩ => ?_
  have z1 : σ1.sc u = 0 := by rw [F1.2.1 _ (by omega), hz]
  have e1 : RealRAM.Op2.eval .add (σ1.sc (u + 13)) (σ1.sc u) = (((lo + hi) / 2 : ℤ) : ℝ) := by
    simp [RealRAM.Op2.eval, m1, z1]
  refine XV.seq (K₂ := 3) (XV.sop2 hL (x := P + 11) (a := u + 13) (b := u) (by omega) (by omega) (by omega) .add
    (by intro h; cases h) (by rw [m1]; exact bmℓ) (by rw [z1]; exact h0) (by rw [e1]; exact bmℓ)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (K₂ := 2) (XV.nconst hL (i := n0 + 3) hN 0 (by positivity)) fun σ3 e3 => ?_
  subst e3
  refine XV.mono (XV.aset hL (a := a0 + 1) (i := n0 + 3) (x := P + 11) hA hN (by omega)
    (by simp; unfold asz at hda ⊢; nlinarith [Nat.zero_le d]) (by simp [e1]; exact bmℓ)) le_rfl fun σ4 e4 => ?_
  subst e4
  refine ⟨by simp [e1], by simp [e1], by simp, by simp [d1], ?_⟩
  have G1 : FrameA (fun y => y = P + 11 ∨ u + 13 ≤ y) (fun j => j = n0 + 3) (fun b k => b = a0 + 1 ∧ k = 0) σ σ1 :=
    (FrameA.ofP F1).mono (fun y h => by rcases h with h | h <;> omega) (fun _ h => h.elim) (fun _ _ h => h)
  exact ((G1.setSc (Or.inl rfl) _).setNat rfl 0).setArr ⟨rfl, by simp⟩ _


set_option maxHeartbeats 16000000 in
/-- **The loop of BIS-R on the machine** (`d = 1`): `xbisLoop` runs `bisLoop I N lo0 hi0 kept0` from the interval
`[lo0, hi0]` in the slots `P + 9`, `P + 10` and the kept point in the machine, `N` in the register `n0 + 7`, the
constants of the tests (`TestEnv` at the scale `2^{λ+1}`) and `2` in `u + 2` in place; the interval stays below `M`. -/
theorem XV.bisLoop {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk} {I : EllI d}
    {nS nN nA P u a0 kb n0 F G Kr N : ℕ} {rowc : XCmd} {Ctx : Env d → Prop} {SR NR AR : ℕ → Prop}
    {M lo0 hi0 : ℤ} {kept0 : Option ((Fin d → ℤ) × ℤ)} (hB : B.OK L nS nN nA) (hav : B.Avoid SR NR AR)
    (hrow : RowProv L X ℓa ℓ I B rowc Ctx SR NR AR Kr) (hctx : CtxOK B Ctx SR NR AR)
    (lay : BisLay L B P u a0 kb n0) (hd : d = 1) (hT : TestEnv B I (I.lam + 1) P u (n0 + 4) σ)
    (h2 : σ.sc (u + 2) = 2) (hC : Ctx σ) (hlo : σ.sc (P + 9) = lo0) (hhi : σ.sc (P + 10) = hi0)
    (blo : |lo0| ≤ M) (bhi : |hi0| ≤ M) (hK : KeptIn P kb kept0 σ) (bK : KeptOK M F kept0)
    (hN : σ.nat (n0 + 7) = N) (hNa : N < 2 ^ ℓa) (bM : M ≤ 2 ^ F)
    (hσF : ellSz I ≤ F) (hsF : 2 * (I.lam + 1) + 1 ≤ F) (hdF : d ≤ F)
    (hFG : F + 2 * ellSz I + d + (I.lam + 1) + 2 ≤ G) (hm : I.m < 2 ^ ℓa) (hℓ : 64 * G + 16 < ℓ) :
    XRunsB L X ℓa ℓ (xbisLoop L B rowc P u a0 kb n0) σ (N * (bisKb d I.m Kr + 2) + 4) (fun σ' =>
      LoopOut P a0 kb M F (bisLoop I N lo0 hi0 kept0) σ' ∧ σ'.draws = σ.draws ∧
      FrameA (bisS B P u SR) (loopN B n0 NR) (loopA B a0 AR) σ σ') := by
  have hrow' := hrow
  obtain ⟨hsr, hnr, har, -⟩ := hrow'
  obtain ⟨⟨tl, -, nNN⟩, PS⟩ := lay
  have tl' := tl
  obtain ⟨oP, Pu, uS, wa, kbe, aA, rn, -, -, -⟩ := tl'
  subst kbe
  have hT' := hT
  obtain ⟨-, z, -, -, -, -, -, -⟩ := hT'
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by simp only [abs_zero]; positivity
  have h1 : |(1 : ℝ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  have h2ℓ : |(2 : ℝ)| < 2 ^ ℓ := by
    rw [abs_two]
    have := pow_lt_pow_right₀ (show (1 : ℝ) < 2 by norm_num) (show 1 < ℓ by omega)
    simpa using this
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  have hda := asz_lt hL (show a0 + 2 < L.NA by omega)
  have hasz : 0 < asz d := by unfold asz; nlinarith
  have hsum : ∀ c : Fin d → ℤ, ∑ i, c i = c ⟨0, by omega⟩ := fun c => by
    have e : (Finset.univ : Finset (Fin d)) = {⟨0, by omega⟩} := by
      ext i
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff, Fin.ext_iff]
      have := i.2; omega
    rw [e, Finset.sum_singleton]
  -- the fixed data along the loop
  have hS0 : ∀ y, bisS B P u SR y → (B.o ≤ y ∧ y ≠ u ∧ y ≠ u + 1 ∧ (y < P + 3 ∨ P + 6 < y)) ∨ SR y :=
    fun y h => by
      rcases h with h | h
      · left; omega
      · right; exact h
  have hN0 : ∀ j, loopN B n0 NR j → (B.rE ≤ j ∧ j ≠ n0 + 4) ∨ NR j := fun j h => by
    rcases h with h | h
    · left; omega
    · right; exact h
  have hA0 : ∀ b k, loopA B a0 AR b k → B.aW ≤ b ∨ AR b := fun b k h => by
    rcases h with h | h
    · left; omega
    · right; exact h
  have env : ∀ σ', σ'.draws = σ.draws → FrameA (bisS B P u SR) (loopN B n0 NR) (loopA B a0 AR) σ σ' →
      TestEnv B I (I.lam + 1) P u (n0 + 4) σ' ∧ σ'.sc (u + 2) = 2 ∧ Ctx σ' := fun σ' hd' hF =>
    ⟨TestEnv.frame hB hav hsr hnr har (by omega) (by omega) (by omega) hT hF hS0 hN0 hA0,
      by
        rw [hF.2.1 _ (fun h => by
          rcases h with h | h
          · omega
          · have := hsr _ h; omega), h2],
      hctx σ σ' hC hd' (hF.mono (fun y h => by
        rcases hS0 y h with h | h
        · exact Or.inl h.1
        · exact Or.inr h) (fun j h => by
        rcases hN0 j h with h | h
        · exact Or.inl h.1
        · exact Or.inr h) hA0)⟩
  -- the frames of the pieces
  have mM : ∀ σa σb : Env d, FrameA (fun y => y = P + 11 ∨ u + 13 ≤ y) (fun j => j = n0 + 3)
      (fun b k => b = a0 + 1 ∧ k = 0) σa σb → FrameA (bisS B P u SR) (loopN B n0 NR) (loopA B a0 AR) σa σb :=
    fun σa σb hF => hF.mono (fun y h => Or.inl (by omega)) (fun j h => Or.inl (by omega))
      (fun b k h => Or.inl (by omega))
  have mT : ∀ σa σb : Env d, FrameA
      (fun y => y = P ∨ y = P + 1 ∨ y = P + 2 ∨ y = P + 7 ∨ u + 13 ≤ y ∨ y = B.o + 2 ∨ SR y)
      (fun j => j = B.rE ∨ (n0 ≤ j ∧ j ≤ n0 + 2) ∨ j = n0 + 5 ∨ NR j)
      (fun b _ => b = B.aW + 1 ∨ b = a0 + 2 ∨ b = a0 + 3 ∨ b = a0 + 6 ∨ AR b) σa σb →
      FrameA (bisS B P u SR) (loopN B n0 NR) (loopA B a0 AR) σa σb := fun σa σb hF =>
    hF.mono (fun y h => by
      rcases h with h | h | h | h | h | h | h
      all_goals first | exact Or.inr h | exact Or.inl (by omega)) (fun j h => by
      rcases h with h | h | h | h
      all_goals first | exact Or.inr h | exact Or.inl (by omega)) (fun b k h => by
      rcases h with h | h | h | h | h
      all_goals first | exact Or.inr h | exact Or.inl (by omega))
  have mE : ∀ σa σb : Env d, FrameA (fun y => y = P ∨ u + 16 ≤ y) (fun j => j = n0 + 1 ∨ j = n0 + 2)
      (fun _ _ => False) σa σb → FrameA (bisS B P u SR) (loopN B n0 NR) (loopA B a0 AR) σa σb := fun σa σb hF =>
    hF.mono (fun y h => Or.inl (by omega)) (fun j h => Or.inl (by omega)) (fun _ _ h => h.elim)
  have mS : ∀ σa σb : Env d, FrameA (fun y => y = P + 8) (fun j => j = n0 + 7) (fun _ _ => False) σa σb →
      FrameA (bisS B P u SR) (loopN B n0 NR) (loopA B a0 AR) σa σb := fun σa σb hF =>
    hF.mono (fun y h => Or.inl (by omega)) (fun j h => Or.inl (by omega)) (fun _ _ h => h.elim)
  -- cells the tests keep
  have nTN : ∀ j, n0 + 3 ≤ j → j ≠ n0 + 5 → ¬ (j = B.rE ∨ (n0 ≤ j ∧ j ≤ n0 + 2) ∨ j = n0 + 5 ∨ NR j) := by
    intro j hj1 hj2 h
    rcases h with h | h | h | h
    · omega
    · omega
    · omega
    · have := hnr j h; omega
  have nTS : ∀ y, P + 8 ≤ y → y ≤ P + 11 → ¬ (y = P ∨ y = P + 1 ∨ y = P + 2 ∨ y = P + 7 ∨ u + 13 ≤ y ∨
      y = B.o + 2 ∨ SR y) := by
    intro y hy1 hy2 h
    rcases h with h | h | h | h | h | h | h
    all_goals first | omega | exact absurd (hsr _ h) (by omega)
  have nTA : ¬ (a0 + 1 = B.aW + 1 ∨ a0 + 1 = a0 + 2 ∨ a0 + 1 = a0 + 3 ∨ a0 + 1 = a0 + 6 ∨ AR (a0 + 1)) := by
    intro h
    rcases h with h | h | h | h | h
    all_goals first | omega | exact absurd (har _ h) (by omega)
  -- the turn
  have hbody : ∀ t σ', BisInv B I P u a0 n0 F N M SR NR AR lo0 hi0 kept0 σ t σ' →
      σ'.nat (n0 + 6) < σ'.nat (n0 + 7) →
      XRunsB L X ℓa ℓ (xbisBody L B rowc P u a0 (a0 + 6) n0) σ' (bisKb d I.m Kr)
        (BisInv B I P u a0 n0 F N M SR NR AR lo0 hi0 kept0 σ (t + 1)) := by
    intro t σ' hJ hlt
    obtain ⟨d', F', -, -, hc⟩ := hJ
    rcases hc with ⟨s8, n7, n6, lo, hi, kept, ml, mh, bl, bh, mK, bK', hl⟩ | ⟨-, n7, -⟩ | ⟨-, n7, -⟩
    rotate_left
    · omega
    · omega
    obtain ⟨k, hk⟩ : ∃ k, N - t = k + 1 := ⟨N - t - 1, by omega⟩
    rw [hk] at hl
    obtain ⟨hT0, h2', -⟩ := env σ' d' F'
    obtain ⟨-, z', -, -, -, -, -, -⟩ := hT0
    have bm : |((lo + hi) / 2)| ≤ M := abs_mid_le bl bh
    have bmF : |((lo + hi) / 2)| ≤ 2 ^ F := bm.trans bM
    unfold bisKb
    refine XV.seq (K₂ := testK d I.m Kr + (tKE d + 8 + 2)) (XV.bisMid (X := X) hL (lo := lo) (hi := hi) (F := F)
      (by omega) PS (by omega) (by omega) (by omega) z' h2' ml mh (bl.trans bM) (bh.trans bM) (by omega)
      (by omega)) fun σ1 ⟨m1, a1, r1, d1, F1⟩ => ?_
    have G1 := F'.trans (mM σ' σ1 F1)
    have D1 : σ1.draws = σ.draws := d1.trans d'
    obtain ⟨hT1, -, hC1⟩ := env σ1 D1 G1
    have ha1 : ∀ k : Fin d, σ1.arr (a0 + 1) k = (fun _ => ((lo + hi) / 2)) k := fun k => by
      have hk0 := k.2
      rw [show (k : ℕ) = 0 by omega, a1]
    have hK1 : KeptIn P (a0 + 6) kept σ1 :=
      mK.frame (F1.2.1 _ (by omega)) (F1.2.1 _ (by omega)) (fun k => F1.2.2.1 _ _ (by omega))
    refine XV.seq (K₂ := tKE d + 8 + 2)
      (XV.test (X := X) (s := I.lam + 1) (a := fun _ => ((lo + hi) / 2)) hL hB hav hrow hctx tl hT1 hC1 hK1
        (fun b W h => (bK' b W h).2) ha1 (fun _ => bmF) hσF hsF hdF hm (by omega)) fun σ2 ⟨o2, d2, F2⟩ => ?_
    have G2 := G1.trans (mT σ1 σ2 F2)
    have D2 : σ2.draws = σ.draws := d2.trans D1
    obtain ⟨hT2, -, -⟩ := env σ2 D2 G2
    have hT2' := hT2
    obtain ⟨-, z2, -, -, -, -, -, -⟩ := hT2'
    have n62 : σ2.nat (n0 + 6) = t := by rw [F2.1 _ (nTN _ (by omega) (by omega)), F1.1 _ (by omega), n6]
    have n72 : σ2.nat (n0 + 7) = N := by rw [F2.1 _ (nTN _ (by omega) (by omega)), F1.1 _ (by omega), n7]
    have n32 : σ2.nat (n0 + 3) = 0 := by rw [F2.1 _ (nTN _ (by omega) (by omega)), r1]
    have m2 : σ2.sc (P + 11) = (((lo + hi) / 2 : ℤ) : ℝ) := by rw [F2.2.1 _ (nTS _ (by omega) (by omega)), m1]
    have l2 : σ2.sc (P + 9) = lo := by
      rw [F2.2.1 _ (nTS _ (by omega) (by omega)), F1.2.1 _ (by omega), ml]
    have h2' : σ2.sc (P + 10) = hi := by
      rw [F2.2.1 _ (nTS _ (by omega) (by omega)), F1.2.1 _ (by omega), mh]
    cases hte : ellTest I (I.lam + 1) (fun _ => ((lo + hi) / 2)) kept with
    | ret x =>
      rw [hte] at o2
      have o2' : σ2.sc P = 1 := o2
      have ex : x = fun _ => ((lo + hi) / 2) := ellTest_ret I (I.lam + 1) (fun _ => ((lo + hi) / 2)) x kept hte
      have u22 : σ2.sc (u + 2) = 2 := (env σ2 D2 G2).2.1
      refine XV.mono (XV.ifS_t hL (by omega) (by omega) (by rw [z2]; exact h0) (by rw [o2']; exact h1)
        (by rw [z2, o2']; norm_num) (XV.stop hL (w := 2) (by omega) (by omega) (by omega) (by omega) z2 u22 h2ℓ))
        (by omega) fun σ3 ⟨s3, m3, d3, F3⟩ => ?_
      unfold BisInv
      refine ⟨d3.trans D2, G2.trans (mS σ2 σ3 F3), by rw [F3.1 _ (by omega), n62]; omega, by rw [m3]; omega,
        Or.inr (Or.inr ⟨s3, m3, x, hl.trans (bisLoop_ret hte), fun k => ?_, fun k => ?_⟩)⟩
      · rw [F3.2.2.1 _ _ (fun h => h), F2.2.2.1 _ _ nTA, ha1, ex]
      · rw [ex]; exact bm
    | cut c kept' =>
      rw [hte] at o2
      obtain ⟨p2, c2, k2⟩ := o2
      have p2' : σ2.sc P = 0 := p2
      have bc : ∀ k, |c k| ≤ 2 ^ G := fun k =>
        abs_le_pow_mono
          (ellCut_le I (I.lam + 1) F (fun _ => ((lo + hi) / 2)) c kept kept' (fun _ => bmF) hte k) hFG
      have bK2 : KeptOK M F kept' := by
        rcases (ellTest_cut I (I.lam + 1) (fun _ => ((lo + hi) / 2)) c kept kept' hte).2 with e | e
        · rw [e]; exact bK'
        · rw [e]
          intro b W h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨fun _ => bm, ellV_le (fun _ => bmF) hσF (by omega) hdF⟩
      refine XV.mono (XV.ifS_f hL (by omega) (by omega) (by rw [z2]; exact h0) (by rw [p2']; exact h0)
        (by rw [z2, p2']; exact lt_irrefl 0) (XV.seq (K₂ := 8)
        (XV.testEnd (X := X) (G := G) (c := c) hL hB tl hT2 c2 bc (by omega)) fun σ3 ⟨r3, c3, d3, F3⟩ => ?_))
        (by unfold tKE; omega) fun _ h => h
      have G3 := G2.trans (mE σ2 σ3 F3)
      have D3 : σ3.draws = σ.draws := d3.trans D2
      obtain ⟨hT3, -, -⟩ := env σ3 D3 G3
      have hT3' := hT3
      obtain ⟨-, z3, o3, n43, -, -, -, -⟩ := hT3'
      have n63 : σ3.nat (n0 + 6) = t := by rw [F3.1 _ (by omega), n62]
      have n73 : σ3.nat (n0 + 7) = N := by rw [F3.1 _ (by omega), n72]
      have n33 : σ3.nat (n0 + 3) = 0 := by rw [F3.1 _ (by omega), n32]
      have m3 : σ3.sc (P + 11) = (((lo + hi) / 2 : ℤ) : ℝ) := by rw [F3.2.1 _ (by omega), m2]
      have l3 : σ3.sc (P + 9) = lo := by rw [F3.2.1 _ (by omega), l2]
      have h3 : σ3.sc (P + 10) = hi := by rw [F3.2.1 _ (by omega), h2']
      have s83 : σ3.sc (P + 8) = 0 := by
        rw [F3.2.1 _ (by omega), F2.2.1 _ (nTS _ (by omega) (by omega)), F1.2.1 _ (by omega), s8]
      have hK3 : KeptIn P (a0 + 6) kept' σ3 := k2.frame (F3.2.1 _ (by omega)) (F3.2.1 _ (by omega))
        (fun k => F3.2.2.1 _ _ (fun h => h))
      have c03 : σ3.arr (a0 + 2) 0 = c ⟨0, by omega⟩ := by
        rw [F3.2.2.1 _ _ (fun h => h)]; exact c2 ⟨0, by omega⟩
      by_cases hc0 : c = 0
      · -- the gradient vanishes: stop on the kept point
        have r3' : σ3.sc P = 1 := r3 hc0
        refine XV.mono (XV.ifS_t hL (by omega) (by omega) (by rw [z3]; exact h0) (by rw [r3']; exact h1)
          (by rw [z3, r3']; norm_num) (XV.stop hL (w := 1) (by omega) (by omega) (by omega) (by omega) z3 o3 h1))
          (by omega) fun σ4 ⟨s4, m4, d4, F4⟩ => ?_
        unfold BisInv
        refine ⟨d4.trans D3, G3.trans (mS σ3 σ4 F4), by rw [F4.1 _ (by omega), n63]; omega, by rw [m4]; omega,
          Or.inr (Or.inl ⟨s4, m4, kept', bK2, ?_, hl.trans (bisLoop_zero hte hc0)⟩)⟩
        exact hK3.frame (F4.2.1 _ (by omega)) (F4.2.1 _ (by omega)) (fun k => F4.2.2.1 _ _ (fun h => h))
      · -- the halving
        have r3' : σ3.sc P = 0 := c3 hc0
        have bc0 : |((c ⟨0, by omega⟩ : ℤ) : ℝ)| < 2 ^ ℓ := absR_lt (bc _) (by omega)
        refine XV.mono (XV.ifS_f hL (by omega) (by omega) (by rw [z3]; exact h0) (by rw [r3']; exact h0)
          (by rw [z3, r3']; exact lt_irrefl 0) (XV.seq (K₂ := 4)
          (XV.aget hL (x := u + 13) (a := a0 + 2) (i := n0 + 3) (by omega) (by omega) (by omega)
            (by rw [n33]; exact hasz) (by rw [n33, c03]; exact bc0)) fun σ4 e4 => ?_)) (by omega) fun _ h => h
        have c04 : σ4.sc (u + 13) = c ⟨0, by omega⟩ := by rw [e4]; simp [n33, c03]
        have z4 : σ4.sc u = 0 := by rw [e4]; simp [z3]
        have m4 : σ4.sc (P + 11) = (((lo + hi) / 2 : ℤ) : ℝ) := by
          rw [e4]; simp only [Env.setSc_sc, show P + 11 ≠ u + 13 by omega, ↓reduceIte, m3]
        have l4 : σ4.sc (P + 9) = lo := by
          rw [e4]; simp only [Env.setSc_sc, show P + 9 ≠ u + 13 by omega, ↓reduceIte, l3]
        have h4 : σ4.sc (P + 10) = hi := by
          rw [e4]; simp only [Env.setSc_sc, show P + 10 ≠ u + 13 by omega, ↓reduceIte, h3]
        have bmid : |((((lo + hi) / 2) : ℤ) : ℝ)| < 2 ^ ℓ := absR_lt bmF (by omega)
        have em : RealRAM.Op2.eval .add (σ4.sc (P + 11)) (σ4.sc u) = (((lo + hi) / 2 : ℤ) : ℝ) := by
          simp [RealRAM.Op2.eval, m4, z4]
        obtain ⟨lo', elo⟩ : ∃ x : ℤ, x = if 0 < c ⟨0, by omega⟩ then lo else (lo + hi) / 2 := ⟨_, rfl⟩
        obtain ⟨hi', ehi⟩ : ∃ x : ℤ, x = if 0 < c ⟨0, by omega⟩ then (lo + hi) / 2 else hi := ⟨_, rfl⟩
        refine XV.seq (K₁ := 3) (K₂ := 1) (Q₁ := fun σ5 => σ5.sc (P + 9) = lo' ∧ σ5.sc (P + 10) = hi' ∧
          σ5.draws = σ4.draws ∧ FrameA (fun y => y = P + 9 ∨ y = P + 10) (fun _ => False) (fun _ _ => False) σ4 σ5)
          ?_ fun σ5 ⟨l5, h5, d5, F5⟩ => ?_
        · by_cases hpos : 0 < c ⟨0, by omega⟩
          · refine XV.mono (XV.ifS_t hL (by omega) (by omega) (by rw [z4]; exact h0) (by rw [c04]; exact bc0)
              (by rw [z4, c04]; exact_mod_cast hpos) (XV.sop2 hL (x := P + 10) (a := P + 11) (b := u) (by omega)
              (by omega) (by omega) .add (by intro h; cases h) (by rw [m4]; exact bmid) (by rw [z4]; exact h0)
              (by rw [em]; exact bmid))) (by omega) fun σ5 e5 => ?_
            subst e5
            refine ⟨?_, ?_, by simp, (FrameA.refl _ _ _ σ4).setSc (Or.inr rfl) _⟩
            · rw [elo]; simp [hpos, l4]
            · rw [ehi]; simp [hpos, em]
          · refine XV.mono (XV.ifS_f hL (by omega) (by omega) (by rw [z4]; exact h0) (by rw [c04]; exact bc0)
              (by rw [z4, c04]; exact_mod_cast hpos) (XV.sop2 hL (x := P + 9) (a := P + 11) (b := u) (by omega)
              (by omega) (by omega) .add (by intro h; cases h) (by rw [m4]; exact bmid) (by rw [z4]; exact h0)
              (by rw [em]; exact bmid))) (by omega) fun σ5 e5 => ?_
            subst e5
            refine ⟨?_, ?_, by simp, (FrameA.refl _ _ _ σ4).setSc (Or.inl rfl) _⟩
            · rw [elo]; simp [hpos, em]
            · rw [ehi]; simp [hpos, h4]
        have G4 : FrameA (bisS B P u SR) (loopN B n0 NR) (loopA B a0 AR) σ σ4 := by
          rw [e4]; exact G3.setSc (Or.inl (Or.inr (Or.inl le_rfl))) _
        have e5 : ∀ y, ¬ (y = P + 9 ∨ y = P + 10) → y ≠ u + 13 → σ5.sc y = σ3.sc y := fun y hy hy' => by
          rw [F5.2.1 _ hy, e4]; simp [hy']
        have n65 : σ5.nat (n0 + 6) = t := by rw [F5.1 _ id, e4]; simp [n63]
        have n45 : σ5.nat (n0 + 4) = 1 := by rw [F5.1 _ id, e4]; simp [n43]
        have n75 : σ5.nat (n0 + 7) = N := by rw [F5.1 _ id, e4]; simp [n73]
        have D5 : σ5.draws = σ.draws := by rw [d5, e4]; simp [D3]
        have G5 : FrameA (bisS B P u SR) (loopN B n0 NR) (loopA B a0 AR) σ σ5 :=
          G4.trans (F5.mono (fun y h => Or.inl (Or.inl ⟨by omega, by omega, by omega⟩)) (fun _ h => h.elim)
            (fun _ _ h => h.elim))
        have hK5 : KeptIn P (a0 + 6) kept' σ5 := hK3.frame (e5 _ (by omega) (by omega)) (e5 _ (by omega) (by omega))
          (fun k => by rw [F5.2.2.1 _ _ id, e4]; simp)
        have s85 : σ5.sc (P + 8) = 0 := by rw [e5 _ (by omega) (by omega), s83]
        refine XV.mono (XV.nadd hL (i := n0 + 6) (a := n0 + 6) (b := n0 + 4) (by omega) (by omega) (by omega)
          (by rw [n65]; omega) (by rw [n45]; exact hsa)) le_rfl fun σ6 e6 => ?_
        subst e6
        unfold BisInv
        refine ⟨by simp [D5], G5.setNat (Or.inl (by omega)) _, by simp [n65, n45]; omega, by simp [n75],
          Or.inl ⟨by simp [s85], by simp [n75], by simp [n65, n45], lo', hi', kept', by simp [l5], by simp [h5], ?_,
            ?_, hK5.frame (by simp) (by simp) (fun k => by simp), bK2, ?_⟩⟩
        · rw [elo]; split_ifs
          · exact bl
          · exact bm
        · rw [ehi]; split_ifs
          · exact bm
          · exact bh
        · rw [hl, show N - (t + 1) = k by omega, elo, ehi]
          by_cases hpos : 0 < c ⟨0, by omega⟩
          · simp only [hpos, ↓reduceIte]
            exact bisLoop_hi hte hc0 (by rw [hsum]; exact hpos)
          · simp only [hpos, ↓reduceIte]
            exact bisLoop_lo hte hc0 (by rw [hsum]; exact hpos)
  -- the loop
  have hb : ∀ t σ', BisInv B I P u a0 n0 F N M SR NR AR lo0 hi0 kept0 σ t σ' →
      σ'.nat (n0 + 6) < 2 ^ ℓa ∧ σ'.nat (n0 + 7) < 2 ^ ℓa := fun t σ' h => by
    obtain ⟨-, -, i6, i7, -⟩ := h
    omega
  have hlt : ∀ t σ', BisInv B I P u a0 n0 F N M SR NR AR lo0 hi0 kept0 σ t σ' →
      σ'.nat (n0 + 6) < σ'.nat (n0 + 7) → t < N := fun t σ' h hl => by
    obtain ⟨-, -, -, -, hc⟩ := h
    rcases hc with ⟨-, n7, n6, -⟩ | ⟨-, n7, -⟩ | ⟨-, n7, -⟩ <;> omega
  refine XV.mono (Q := fun σ' => ∃ t', BisInv B I P u a0 n0 F N M SR NR AR lo0 hi0 kept0 σ t' σ' ∧
      ¬ σ'.nat (n0 + 6) < σ'.nat (n0 + 7)) (XV.seq (K₂ := 1 + ((N - 0) * (bisKb d I.m Kr + 2) + 2))
    (XV.nconst hL (X := X) (i := n0 + 6) (by omega) 0 (by positivity)) fun σa ea => ?_)
    (by simp only [Nat.sub_zero]; omega) ?_
  · subst ea
    have za : (σ.setNat (n0 + 6) 0).sc u = 0 := by simp [z]
    refine XV.seq (XV.sop2 hL (x := P + 8) (a := u) (b := u) (by omega) (by omega) (by omega) .add
      (by intro h; cases h) (by rw [za]; exact h0) (by rw [za]; exact h0)
      (by simp only [RealRAM.Op2.eval, za, add_zero]; exact h0)) fun σb eb => ?_
    subst eb
    refine XV.whileN hL (by omega) (by omega) (BisInv B I P u a0 n0 F N M SR NR AR lo0 hi0 kept0 σ) N
      (bisKb d I.m Kr) hb hlt hbody 0 _ ?_
    unfold BisInv
    refine ⟨by simp, ((FrameA.refl _ _ _ σ).setNat (Or.inl (by omega)) 0).setSc (Or.inl (Or.inl ⟨by omega,
      by omega, by omega⟩)) _, by simp, by simp [hN], Or.inl ⟨by simp [RealRAM.Op2.eval, z], by simp [hN], by simp,
      lo0, hi0, kept0, by simp [hlo], by simp [hhi], blo, bhi, ?_, bK, by simp⟩⟩
    exact hK.frame (by simp) (by simp) (fun k => by simp)
  · rintro σ' ⟨t', hJ, hnl⟩
    obtain ⟨d', F', i6, -, hc⟩ := hJ
    refine ⟨?_, d', F'⟩
    rcases hc with ⟨s8, n7, n6, lo, hi, kept, -, -, -, -, mK, bK', hl⟩ | ⟨s8, -, kept, bK', mK, hl⟩ |
      ⟨s8, -, x, hl, mx, bx⟩
    · rw [show N - t' = 0 by omega] at hl
      exact Or.inr ⟨Or.inl s8, kept, bK', mK, by rw [hl]; rfl⟩
    · exact Or.inr ⟨Or.inr s8, kept, bK', mK, hl⟩
    · exact Or.inl ⟨s8, x, hl, mx, bx⟩

end AdversarialBco.Bit.Transfer
