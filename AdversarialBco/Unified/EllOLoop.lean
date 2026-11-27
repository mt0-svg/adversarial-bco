/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EllSpec
public import AdversarialBco.Unified.XRunsO
public import AdversarialBco.Bit.Transfer.XBisLoop

@[expose] public section

/-!
# UNI-ELL (c): the loops of ELL-O and BIS-O on the oracle machine, for any test command

The loops of ELL-R and BIS-R on the machine with the tests of one iteration (`xtest`, Bit/Transfer/XEllTest.lean)
replaced by a command `tc` of the oracle language: `tc` computes the outcome `tf a kept` of a test function `tf`
(`TestOut`) and writes only its frame `TS`, `TN`, `TA`. The rest of a turn is ELL-R's (`xtestEnd`, `xupd`, `xellStop`;
the halving of BIS-R). The pure loops `loopT` and `bisT` are the iterations of ELL-R and BIS-R over `tf`; `ellLoopO`
and `bisLoopO` are their instances (EllSpec.lean).
-/

namespace AdversarialBco.Uni.EllO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## The loops as functions of the test -/

/-- ELL-R's iterations over the test function `tf`, `k` of them left. -/
def loopT (tf : (Fin d → ℤ) → Option ((Fin d → ℤ) × ℤ) → Cut d) (p q j : ℕ) (capA capa : ℤ) :
    ℕ → ESt d → Option (Fin d → ℤ)
  | 0, st => st.kept.map Prod.fst
  | k + 1, st =>
    match tf st.a st.kept with
    | .ret x => some x
    | .cut c kept =>
      if c = 0 then kept.map Prod.fst else
      match ellUpd p q j capA capa st.A st.a c with
      | none => kept.map Prod.fst
      | some (A', a') => loopT tf p q j capA capa k ⟨A', a', kept⟩

/-- BIS-R's iterations over the test function `tf`, `k` of them left. -/
def bisT (tf : (Fin d → ℤ) → Option ((Fin d → ℤ) × ℤ) → Cut d) :
    ℕ → ℤ → ℤ → Option ((Fin d → ℤ) × ℤ) → Option (Fin d → ℤ)
  | 0, _, _, kept => kept.map Prod.fst
  | k + 1, lo, hi, kept =>
    match tf (fun _ => (lo + hi) / 2) kept with
    | .ret x => some x
    | .cut c kept' =>
      if c = 0 then kept'.map Prod.fst else
      if 0 < ∑ i, c i then bisT tf k lo ((lo + hi) / 2) kept' else bisT tf k ((lo + hi) / 2) hi kept'

section Pure

variable {tf : (Fin d → ℤ) → Option ((Fin d → ℤ) × ℤ) → Cut d} {p q j k : ℕ} {capA capa : ℤ}

theorem loopT_ret {st : ESt d} {x : Fin d → ℤ} (h : tf st.a st.kept = .ret x) :
    loopT tf p q j capA capa (k + 1) st = some x := by
  rw [loopT, h]

theorem loopT_zero {st : ESt d} {c : Fin d → ℤ} {kept : Option ((Fin d → ℤ) × ℤ)}
    (h : tf st.a st.kept = .cut c kept) (hc : c = 0) : loopT tf p q j capA capa (k + 1) st = kept.map Prod.fst := by
  rw [loopT, h]; simp [hc]

theorem loopT_fail {st : ESt d} {c : Fin d → ℤ} {kept : Option ((Fin d → ℤ) × ℤ)}
    (h : tf st.a st.kept = .cut c kept) (hc : c ≠ 0) (hu : ellUpd p q j capA capa st.A st.a c = none) :
    loopT tf p q j capA capa (k + 1) st = kept.map Prod.fst := by
  rw [loopT, h]; simp [hc, hu]

theorem loopT_next {st : ESt d} {c : Fin d → ℤ} {kept : Option ((Fin d → ℤ) × ℤ)}
    {A' : Matrix (Fin d) (Fin d) ℤ} {a' : Fin d → ℤ} (h : tf st.a st.kept = .cut c kept) (hc : c ≠ 0)
    (hu : ellUpd p q j capA capa st.A st.a c = some (A', a')) :
    loopT tf p q j capA capa (k + 1) st = loopT tf p q j capA capa k ⟨A', a', kept⟩ := by
  rw [loopT, h]; simp [hc, hu]

theorem bisT_ret {lo hi : ℤ} {kept : Option ((Fin d → ℤ) × ℤ)} {x : Fin d → ℤ}
    (h : tf (fun _ => (lo + hi) / 2) kept = .ret x) : bisT tf (k + 1) lo hi kept = some x := by
  rw [bisT, h]

theorem bisT_zero {lo hi : ℤ} {kept kept' : Option ((Fin d → ℤ) × ℤ)} {c : Fin d → ℤ}
    (h : tf (fun _ => (lo + hi) / 2) kept = .cut c kept') (hc : c = 0) :
    bisT tf (k + 1) lo hi kept = kept'.map Prod.fst := by
  rw [bisT, h]; simp [hc]

theorem bisT_hi {lo hi : ℤ} {kept kept' : Option ((Fin d → ℤ) × ℤ)} {c : Fin d → ℤ}
    (h : tf (fun _ => (lo + hi) / 2) kept = .cut c kept') (hc : c ≠ 0) (hs : 0 < ∑ i, c i) :
    bisT tf (k + 1) lo hi kept = bisT tf k lo ((lo + hi) / 2) kept' := by
  rw [bisT, h]; simp [hc, hs]

theorem bisT_lo {lo hi : ℤ} {kept kept' : Option ((Fin d → ℤ) × ℤ)} {c : Fin d → ℤ}
    (h : tf (fun _ => (lo + hi) / 2) kept = .cut c kept') (hc : c ≠ 0) (hs : ¬ 0 < ∑ i, c i) :
    bisT tf (k + 1) lo hi kept = bisT tf k ((lo + hi) / 2) hi kept' := by
  rw [bisT, h]; simp [hc, hs]

end Pure

/-! ## The programs -/

/-- One turn of ELL-O: the test command `tc`, then ELL-R's end of the turn. -/
def xbodyT (L : Layout) (B : EllBlk) (tc : XCmdO) (P u a0 n0 : ℕ) : XCmdO :=
  .seq tc
  (xifSO L u P (.base (xellStop L P u n0 (u + 2)))
    (.seq (.base (xtestEnd L B P u a0 n0 (n0 + 4)))
      (xifSO L u P (.base (xellStop L P u n0 (u + 1)))
        (.seq (.base (xupd L u a0 n0 B.rd (n0 + 4)))
          (xifSO L u (u + 13) (.base (xellStop L P u n0 (u + 1)))
            (.base (.prim (.frag (.nadd (n0 + 6) (n0 + 6) (n0 + 4))))))))))

/-- The loop of ELL-O: the turn to `0`, the outcome to `0`, at most `nat (n0 + 7)` turns. -/
def xloopT (L : Layout) (B : EllBlk) (tc : XCmdO) (P u a0 n0 : ℕ) : XCmdO :=
  .seq (.base (.prim (.frag (.nconst (n0 + 6) 0)))) (.seq (.base (xset L (P + 8) u u))
    (.whileN (n0 + 6) (n0 + 7) (xbodyT L B tc P u a0 n0)))

/-- One turn of BIS-O: the midpoint, the test command `tc`, then BIS-R's end of the turn. -/
def xbisBodyT (L : Layout) (B : EllBlk) (tc : XCmdO) (P u a0 n0 : ℕ) : XCmdO :=
  .seq (.base (xbisMid L P u a0 n0))
  (.seq tc
  (xifSO L u P (.base (xellStop L P u n0 (u + 2)))
    (.seq (.base (xtestEnd L B P u a0 n0 (n0 + 4)))
      (xifSO L u P (.base (xellStop L P u n0 (u + 1))) (.base (xbisHalve L P u a0 n0))))))

/-- The loop of BIS-O. -/
def xbisLoopT (L : Layout) (B : EllBlk) (tc : XCmdO) (P u a0 n0 : ℕ) : XCmdO :=
  .seq (.base (.prim (.frag (.nconst (n0 + 6) 0)))) (.seq (.base (xset L (P + 8) u u))
    (.whileN (n0 + 6) (n0 + 7) (xbisBodyT L B tc P u a0 n0)))

/-! ## The frames -/

/-- The slots the loop of ELL-O may change: those of ELL-R's end of a turn and the test's `TS`. -/
abbrev lpS (P u : ℕ) (TS : ℕ → Prop) (y : ℕ) : Prop := (y = P ∨ y = P + 8 ∨ u + 13 ≤ y) ∨ TS y

/-- The registers the loop of ELL-O may change. -/
abbrev lpN (n0 : ℕ) (TN : ℕ → Prop) (j : ℕ) : Prop := ((n0 ≤ j ∧ j ≤ n0 + 3) ∨ (n0 + 6 ≤ j ∧ j ≤ n0 + 7)) ∨ TN j

/-- The array cells the loop of ELL-O may change. -/
abbrev lpA (a0 : ℕ) (TA : ℕ → ℕ → Prop) (b k : ℕ) : Prop := (a0 ≤ b ∧ b ≤ a0 + 5) ∨ TA b k

/-- The slots the loop of BIS-O may change. -/
abbrev bpS (P u : ℕ) (TS : ℕ → Prop) (y : ℕ) : Prop :=
  (y = P ∨ y = P + 8 ∨ y = P + 9 ∨ y = P + 10 ∨ y = P + 11 ∨ u + 13 ≤ y) ∨ TS y

/-- The array cells the loop of BIS-O may change. -/
abbrev bpA (a0 : ℕ) (TA : ℕ → ℕ → Prop) (b k : ℕ) : Prop := (b = a0 + 1 ∧ k = 0) ∨ TA b k

/-! ## The loop of ELL-O -/

/-- The invariant of the loop after `t` turns from `σ`, over `loopT`. -/
def InvT (tf : (Fin d → ℤ) → Option ((Fin d → ℤ) × ℤ) → Cut d) (p q j : ℕ) (capA capa : ℤ) (P u a0 n0 F N : ℕ)
    (TS TN : ℕ → Prop) (TA : ℕ → ℕ → Prop) (st : ESt d) (σ : Env d) (t : ℕ) (σ' : Env d) : Prop :=
  σ'.draws = σ.draws ∧ FrameA (lpS P u TS) (lpN n0 TN) (lpA a0 TA) σ σ' ∧
    σ'.nat (n0 + 6) ≤ N ∧ σ'.nat (n0 + 7) ≤ N ∧
    ((σ'.sc (P + 8) = 0 ∧ σ'.nat (n0 + 7) = N ∧ σ'.nat (n0 + 6) = t ∧
        ∃ st' : ESt d, LoopSt P a0 (a0 + 6) capA capa F st' σ' ∧
          loopT tf p q j capA capa N st = loopT tf p q j capA capa (N - t) st') ∨
      (σ'.sc (P + 8) = 1 ∧ σ'.nat (n0 + 7) = 0 ∧
        ∃ kept, KeptOK capa F kept ∧ KeptIn P (a0 + 6) kept σ' ∧ loopT tf p q j capA capa N st = kept.map Prod.fst) ∨
      (σ'.sc (P + 8) = 2 ∧ σ'.nat (n0 + 7) = 0 ∧
        ∃ x, loopT tf p q j capA capa N st = some x ∧ (∀ k : Fin d, σ'.arr (a0 + 1) k = x k) ∧ ∀ k, |x k| ≤ capa))

/-- The units of one turn of ELL-O with a test of `Kt` units. -/
def kbT (d E Kt : ℕ) : ℕ := Kt + (tKE d + (200 * (E + 1) ^ 2 + (1 + 2) + 2) + 2)

set_option maxHeartbeats 16000000 in
/-- **The loop of ELL-O on the oracle machine**: `xloopT` runs `loopT tf N st` from the state `st` in the machine,
for a test command `tc` computing `tf` (`htest`) whose frame avoids the state of the loop, when the context `Ctx`
(which holds the constants of the tests and of the update) survives every change of the loop. -/
theorem XVO.loopT {L : Layout} {XO : XCtxO d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk} {I : EllI d}
    {nS nN nA P u a0 n0 F E N Kt p q j : ℕ} {tc : XCmdO} {tf : (Fin d → ℤ) → Option ((Fin d → ℤ) × ℤ) → Cut d}
    {Ctx : Env d → Prop} {TS TN : ℕ → Prop} {TA : ℕ → ℕ → Prop} {capA capa : ℤ} {st : ESt d}
    (hB : B.OK L nS nN nA) (lay : LoopLay L B P u a0 (a0 + 6) n0)
    (hCT : ∀ σ', Ctx σ' → TestEnv B I p P u (n0 + 4) σ' ∧ UpdEnv u p q j capA capa σ')
    (henv : ∀ σa σb, Ctx σa → σb.draws = σa.draws → FrameA (lpS P u TS) (lpN n0 TN) (lpA a0 TA) σa σb → Ctx σb)
    (hTS : ¬ TS (P + 8)) (hTN6 : ¬ TN (n0 + 6)) (hTN7 : ¬ TN (n0 + 7)) (hTA : ∀ k, ¬ TA a0 k ∧ ¬ TA (a0 + 1) k)
    (htest : ∀ σ' (a : Fin d → ℤ) kept, Ctx σ' → KeptIn P (a0 + 6) kept σ' → KeptOK capa F kept →
      (∀ k : Fin d, σ'.arr (a0 + 1) k = a k) → (∀ k, |a k| ≤ capa) →
      XRunsBO L XO ℓa ℓ tc σ' Kt (fun σ1 => TestOut P a0 (a0 + 6) (tf a kept) σ1 ∧ σ1.draws = σ'.draws ∧
        FrameA TS TN TA σ' σ1))
    (hret : ∀ a kept x, tf a kept = .ret x → x = a)
    (hcut : ∀ a kept c kept', (∀ k, |a k| ≤ capa) → KeptOK capa F kept → tf a kept = .cut c kept' →
      (∀ k, |c k| ≤ 2 ^ E) ∧ KeptOK capa F kept')
    (hC : Ctx σ) (hS : LoopSt P a0 (a0 + 6) capA capa F st σ) (hN : σ.nat (n0 + 7) = N) (hNa : N < 2 ^ ℓa)
    (hcA0 : 0 ≤ capA) (hca0 : 0 ≤ capa) (bcA : capA ≤ 2 ^ E) (bca : capa ≤ 2 ^ E)
    (hdE : d ≤ E) (hpE : p ≤ E) (hq : 2 * q ≤ E) (hE1 : 1 ≤ E) (bkN : |kapN d| ≤ 2 ^ E) (bkD : |kapD d| ≤ 2 ^ E)
    (hℓ : 64 * E + 16 < ℓ) :
    XRunsBO L XO ℓa ℓ (xloopT L B tc P u a0 n0) σ (N * (kbT d E Kt + 2) + 4) (fun σ' =>
      LoopOut P a0 (a0 + 6) capa F (loopT tf p q j capA capa N st) σ' ∧ σ'.draws = σ.draws ∧
      FrameA (lpS P u TS) (lpN n0 TN) (lpA a0 TA) σ σ') := by
  obtain ⟨tl, PS, nNN⟩ := lay
  have tl' := tl
  obtain ⟨oP, Pu, uS, wa, -, aA, rn, -, -, -⟩ := tl'
  have hB' := hB
  obtain ⟨-, -, -, hrd, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hB'
  obtain ⟨⟨⟨hσd0, -⟩, z, -, -, -, -, -, -⟩, -⟩ := hCT σ hC
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by simp only [abs_zero]; positivity
  have h1 : |(1 : ℝ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  have h2 : |(2 : ℝ)| < 2 ^ ℓ := by
    rw [abs_two]
    have := pow_lt_pow_right₀ (show (1 : ℝ) < 2 by norm_num) (show 1 < ℓ by omega)
    simpa using this
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  -- the frames of the pieces
  have mE : ∀ σa σb : Env d, FrameA (fun y => y = P ∨ u + 16 ≤ y) (fun j => j = n0 + 1 ∨ j = n0 + 2)
      (fun _ _ => False) σa σb → FrameA (lpS P u TS) (lpN n0 TN) (lpA a0 TA) σa σb := fun σa σb hF =>
    hF.mono (fun y h => Or.inl (by omega)) (fun j h => Or.inl (by omega)) (fun _ _ h => h.elim)
  have mU : ∀ σa σb : Env d, FrameA (fun y => u + 13 ≤ y) (fun j => n0 ≤ j ∧ j < n0 + 4)
      (fun b k => a0 ≤ b ∧ b < a0 + 6 ∧ b ≠ a0 + 2 ∧ k < d * d) σa σb →
      FrameA (lpS P u TS) (lpN n0 TN) (lpA a0 TA) σa σb := fun σa σb hF =>
    hF.mono (fun y h => Or.inl (by omega)) (fun j h => Or.inl (by omega)) (fun b k h => Or.inl (by omega))
  have mS : ∀ σa σb : Env d, FrameA (fun y => y = P + 8) (fun j => j = n0 + 7) (fun _ _ => False) σa σb →
      FrameA (lpS P u TS) (lpN n0 TN) (lpA a0 TA) σa σb := fun σa σb hF =>
    hF.mono (fun y h => Or.inl (by omega)) (fun j h => Or.inl (by omega)) (fun _ _ h => h.elim)
  -- the turn
  have hbody : ∀ t σ', InvT tf p q j capA capa P u a0 n0 F N TS TN TA st σ t σ' →
      σ'.nat (n0 + 6) < σ'.nat (n0 + 7) →
      XRunsBO L XO ℓa ℓ (xbodyT L B tc P u a0 n0) σ' (kbT d E Kt)
        (InvT tf p q j capA capa P u a0 n0 F N TS TN TA st σ (t + 1)) := by
    intro t σ' hJ hlt
    obtain ⟨d', F', -, -, hc⟩ := hJ
    rcases hc with ⟨s8, n7, n6, st', ⟨mA, ma, mK, bA', ba', bK'⟩, hl⟩ | ⟨-, n7, -⟩ | ⟨-, n7, -⟩
    rotate_left
    · omega
    · omega
    obtain ⟨k, hk⟩ : ∃ k, N - t = k + 1 := ⟨N - t - 1, by omega⟩
    rw [hk] at hl
    have hC' : Ctx σ' := henv σ σ' hC d' F'
    unfold kbT
    refine XVO.seq (K₂ := tKE d + (200 * (E + 1) ^ 2 + (1 + 2) + 2) + 2)
      (htest σ' st'.a st'.kept hC' mK bK' ma ba') fun σ1 ⟨o1, d1, F1⟩ => ?_
    have G1 := F'.trans (F1.mono (fun y h => Or.inr h) (fun j h => Or.inr h) (fun b k h => Or.inr h))
    have D1 : σ1.draws = σ.draws := d1.trans d'
    have hC1 : Ctx σ1 := henv σ σ1 hC D1 G1
    obtain ⟨hT1, hU1⟩ := hCT σ1 hC1
    have hT1' := hT1
    obtain ⟨-, z1, -, -, -, -, -, -⟩ := hT1'
    have n6' : σ1.nat (n0 + 6) = t := by rw [F1.1 _ hTN6, n6]
    have n7' : σ1.nat (n0 + 7) = N := by rw [F1.1 _ hTN7, n7]
    have s8' : σ1.sc (P + 8) = 0 := by rw [F1.2.1 _ hTS, s8]
    have mA1 : ∀ i k : Fin d, σ1.arr a0 (d * i + k) = st'.A i k := fun i k => by
      rw [F1.2.2.1 _ _ (hTA _).1, mA]
    have ma1 : ∀ k : Fin d, σ1.arr (a0 + 1) k = st'.a k := fun k => by
      rw [F1.2.2.1 _ _ (hTA _).2, ma]
    cases hte : tf st'.a st'.kept with
    | ret x =>
      rw [hte] at o1
      have o1' : σ1.sc P = 1 := o1
      have ex : x = st'.a := hret _ _ _ hte
      obtain ⟨u2, -⟩ := hU1
      refine XVO.mono (XVO.ifS_t hL (by omega) (by omega) (by rw [z1]; exact h0) (by rw [o1']; exact h1)
        (by rw [z1, o1']; norm_num)
        (XVO.ofX (XV.stop hL (w := 2) (by omega) (by omega) (by omega) (by omega) z1 u2 h2)))
        (by omega) fun σ2 ⟨s2, m2, d2, F2⟩ => ?_
      unfold InvT
      refine ⟨d2.trans D1, G1.trans (mS σ1 σ2 F2), by rw [F2.1 _ (by omega), n6']; omega, by rw [m2]; omega,
        Or.inr (Or.inr ⟨s2, m2, x, hl.trans (loopT_ret hte), fun k => ?_, fun k => ?_⟩)⟩
      · rw [F2.2.2.1 _ _ (fun h => h), ma1, ex]
      · rw [ex]; exact ba' k
    | cut c kept' =>
      rw [hte] at o1
      obtain ⟨p1, c1, k1⟩ := o1
      have p1' : σ1.sc P = 0 := p1
      obtain ⟨bc, bK1⟩ := hcut _ _ _ _ ba' bK' hte
      refine XVO.mono (XVO.ifS_f hL (by omega) (by omega) (by rw [z1]; exact h0) (by rw [p1']; exact h0)
        (by rw [z1, p1']; exact lt_irrefl 0) (XVO.seq (K₂ := 200 * (E + 1) ^ 2 + (1 + 2) + 2)
        (XVO.ofX (XV.testEnd (X := XO.X) (G := E) (c := c) hL hB tl hT1 c1 bc (by omega)))
        fun σ2 ⟨r2, c2, d2, F2⟩ => ?_)) (by unfold tKE; omega) fun _ h => h
      have G2 := G1.trans (mE σ1 σ2 F2)
      have D2 : σ2.draws = σ.draws := d2.trans D1
      have hC2 : Ctx σ2 := henv σ σ2 hC D2 G2
      obtain ⟨hT2, hU2⟩ := hCT σ2 hC2
      have hT2' := hT2
      obtain ⟨⟨hσd, -⟩, z2, o2, n42, -, -, -, -⟩ := hT2'
      have n62 : σ2.nat (n0 + 6) = t := by rw [F2.1 _ (by omega), n6']
      have n72 : σ2.nat (n0 + 7) = N := by rw [F2.1 _ (by omega), n7']
      have s82 : σ2.sc (P + 8) = 0 := by rw [F2.2.1 _ (by omega), s8']
      by_cases hc0 : c = 0
      · -- the cut vanishes: stop on the kept point
        have r2' : σ2.sc P = 1 := r2 hc0
        refine XVO.mono (XVO.ifS_t hL (by omega) (by omega) (by rw [z2]; exact h0) (by rw [r2']; exact h1)
          (by rw [z2, r2']; norm_num)
          (XVO.ofX (XV.stop hL (w := 1) (by omega) (by omega) (by omega) (by omega) z2 o2 h1)))
          (by omega) fun σ3 ⟨s3, m3, d3, F3⟩ => ?_
        unfold InvT
        refine ⟨d3.trans D2, G2.trans (mS σ2 σ3 F3), by rw [F3.1 _ (by omega), n62]; omega, by rw [m3]; omega,
          Or.inr (Or.inl ⟨s3, m3, kept', bK1, ?_, hl.trans (loopT_zero hte hc0)⟩)⟩
        exact k1.frame (by rw [F3.2.1 _ (by omega), F2.2.1 _ (by omega)])
          (by rw [F3.2.1 _ (by omega), F2.2.1 _ (by omega)])
          (fun k => by rw [F3.2.2.1 _ _ (fun h => h), F2.2.2.1 _ _ (fun h => h)])
      · -- the update
        have r2' : σ2.sc P = 0 := c2 hc0
        obtain ⟨e2, e4, eK1, eQ2, eP, eQ, ed1, ekN, ekD, ecA, eca⟩ := hU2
        refine XVO.mono (XVO.ifS_f hL (by omega) (by omega) (by rw [z2]; exact h0) (by rw [r2']; exact h0)
          (by rw [z2, r2']; exact lt_irrefl 0) (XVO.seq (K₂ := 1 + 2)
          (XVO.ofX (XV.upd (X := XO.X) (u := u) (a0 := a0) (n0 := n0) (nd := B.rd) (none := n0 + 4) (E := E)
            (p := p) (q := q) (j := j) (A := st'.A) (a := st'.a) (c := c) (capA := capA) (capa := capa) hL
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) z2 o2 e2 e4 eK1
            eQ2 eP eQ ed1 ekN ekD ecA eca hσd n42
            (fun i k => by rw [F2.2.2.1 _ _ (fun h => h), mA1])
            (fun k => by rw [F2.2.2.1 _ _ (fun h => h), ma1])
            (fun k => by rw [F2.2.2.1 _ _ (fun h => h), c1])
            (fun i k => (bA' i k).trans bcA) (fun k => (ba' k).trans bca) bc hdE hE1 hpE hq bkN bkD hcA0 hca0
            bcA bca hℓ))
          fun σ3 ⟨u3, d3, F3⟩ => ?_)) (by omega) fun _ h => h
        have G3 := G2.trans (mU σ2 σ3 F3)
        have D3 : σ3.draws = σ.draws := d3.trans D2
        have z3 : σ3.sc u = 0 := by rw [F3.2.1 _ (by omega), z2]
        have o3 : σ3.sc (u + 1) = 1 := by rw [F3.2.1 _ (by omega), o2]
        have n63 : σ3.nat (n0 + 6) = t := by rw [F3.1 _ (by omega), n62]
        have n73 : σ3.nat (n0 + 7) = N := by rw [F3.1 _ (by omega), n72]
        have n43 : σ3.nat (n0 + 4) = 1 := by rw [F3.1 _ (by omega), n42]
        have s83 : σ3.sc (P + 8) = 0 := by rw [F3.2.1 _ (by omega), s82]
        have hK3 : KeptIn P (a0 + 6) kept' σ3 := k1.frame (by rw [F3.2.1 _ (by omega), F2.2.1 _ (by omega)])
          (by rw [F3.2.1 _ (by omega), F2.2.1 _ (by omega)])
          (fun k => by rw [F3.2.2.1 _ _ (by omega), F2.2.2.1 _ _ (fun h => h)])
        cases hu : ellUpd p q j capA capa st'.A st'.a c with
        | none =>
          rw [hu] at u3
          have u3' : σ3.sc (u + 13) = 1 := u3
          refine XVO.mono (XVO.ifS_t hL (by omega) (by omega) (by rw [z3]; exact h0) (by rw [u3']; exact h1)
            (by rw [z3, u3']; norm_num)
            (XVO.ofX (XV.stop hL (w := 1) (by omega) (by omega) (by omega) (by omega) z3 o3 h1)))
            (by omega) fun σ4 ⟨s4, m4, d4, F4⟩ => ?_
          unfold InvT
          refine ⟨d4.trans D3, G3.trans (mS σ3 σ4 F4), by rw [F4.1 _ (by omega), n63]; omega, by rw [m4]; omega,
            Or.inr (Or.inl ⟨s4, m4, kept', bK1, ?_, hl.trans (loopT_fail hte hc0 hu)⟩)⟩
          exact hK3.frame (F4.2.1 _ (by omega)) (F4.2.1 _ (by omega)) (fun k => F4.2.2.1 _ _ (fun h => h))
        | some r =>
          obtain ⟨A', a'⟩ := r
          rw [hu] at u3
          obtain ⟨u13, uA, ua⟩ := u3
          obtain ⟨cA', ca'⟩ := ellUpd_caps hu
          refine XVO.mono (XVO.ifS_f hL (by omega) (by omega) (by rw [z3]; exact h0) (by rw [u13]; exact h0)
            (by rw [z3, u13]; exact lt_irrefl 0) (XVO.nadd hL (i := n0 + 6) (a := n0 + 6) (b := n0 + 4) (by omega)
            (by omega) (by omega) (by rw [n63]; omega) (by rw [n43]; exact hsa))) (by omega) fun σ4 e4 => ?_
          subst e4
          unfold InvT
          refine ⟨by simp [D3], G3.setNat (Or.inl (by omega)) _, by simp [n63, n43]; omega,
            by simp [n73], Or.inl ⟨by simp [s83], by simp [n73], by simp [n63, n43], ⟨A', a', kept'⟩,
              ⟨fun i k => by simp [uA], fun k => by simp [ua], ?_, cA', ca', bK1⟩, ?_⟩⟩
          · exact hK3.frame (by simp) (by simp) (fun k => by simp)
          · rw [hl, loopT_next hte hc0 hu, show N - (t + 1) = k by omega]
  -- the loop
  have hb : ∀ t σ', InvT tf p q j capA capa P u a0 n0 F N TS TN TA st σ t σ' →
      σ'.nat (n0 + 6) < 2 ^ ℓa ∧ σ'.nat (n0 + 7) < 2 ^ ℓa := fun t σ' h => by
    obtain ⟨-, -, i6, i7, -⟩ := h
    omega
  have hlt : ∀ t σ', InvT tf p q j capA capa P u a0 n0 F N TS TN TA st σ t σ' →
      σ'.nat (n0 + 6) < σ'.nat (n0 + 7) → t < N := fun t σ' h hl => by
    obtain ⟨-, -, -, -, hc⟩ := h
    rcases hc with ⟨-, n7, n6, -⟩ | ⟨-, n7, -⟩ | ⟨-, n7, -⟩ <;> omega
  refine XVO.mono (Q := fun σ' => ∃ t', InvT tf p q j capA capa P u a0 n0 F N TS TN TA st σ t' σ' ∧
      ¬ σ'.nat (n0 + 6) < σ'.nat (n0 + 7)) (XVO.seq (K₂ := 1 + ((N - 0) * (kbT d E Kt + 2) + 2))
    (XVO.nconst hL (XO := XO) (ℓ := ℓ) (i := n0 + 6) (by omega) 0 (by positivity)) fun σa ea => ?_)
    (by simp only [Nat.sub_zero]; omega) ?_
  · subst ea
    have za : (σ.setNat (n0 + 6) 0).sc u = 0 := by simp [z]
    refine XVO.seq (XVO.ofX (XV.sop2 hL (x := P + 8) (a := u) (b := u) (by omega) (by omega) (by omega) .add
      (by intro h; cases h) (by rw [za]; exact h0) (by rw [za]; exact h0)
      (by simp only [RealRAM.Op2.eval, za, add_zero]; exact h0))) fun σb eb => ?_
    subst eb
    refine XVO.whileN hL (by omega) (by omega) (InvT tf p q j capA capa P u a0 n0 F N TS TN TA st σ) N
      (kbT d E Kt) hb hlt hbody 0 _ ?_
    unfold InvT
    refine ⟨by simp, ((FrameA.refl _ _ _ σ).setNat (Or.inl (by omega)) 0).setSc (Or.inl (by omega)) _,
      by simp, by simp [hN], Or.inl ⟨by simp [RealRAM.Op2.eval, z], by simp [hN], by simp, st, ?_, by simp⟩⟩
    exact hS.frame (fun k => by simp) (fun k => by simp) (by simp) (by simp) (fun k => by simp)
  · rintro σ' ⟨t', hJ, hnl⟩
    obtain ⟨d', F', i6, -, hc⟩ := hJ
    refine ⟨?_, d', F'⟩
    rcases hc with ⟨s8, n7, n6, st', ⟨-, -, mK, -, -, bK'⟩, hl⟩ | ⟨s8, -, kept, bK, mK, hl⟩ |
      ⟨s8, -, x, hl, mx, bx⟩
    · rw [show N - t' = 0 by omega] at hl
      exact Or.inr ⟨Or.inl s8, st'.kept, bK', mK, by rw [hl]; rfl⟩
    · exact Or.inr ⟨Or.inr s8, kept, bK, mK, hl⟩
    · exact Or.inl ⟨s8, x, hl, mx, bx⟩

/-! ## The loop of BIS-O -/

/-- The invariant of BIS-O after `t` turns from `σ`, over `bisT`. -/
def BisInvT (tf : (Fin d → ℤ) → Option ((Fin d → ℤ) × ℤ) → Cut d) (P u a0 n0 F N : ℕ) (M : ℤ)
    (TS TN : ℕ → Prop) (TA : ℕ → ℕ → Prop) (lo0 hi0 : ℤ) (kept0 : Option ((Fin d → ℤ) × ℤ)) (σ : Env d) (t : ℕ)
    (σ' : Env d) : Prop :=
  σ'.draws = σ.draws ∧ FrameA (bpS P u TS) (lpN n0 TN) (bpA a0 TA) σ σ' ∧
    σ'.nat (n0 + 6) ≤ N ∧ σ'.nat (n0 + 7) ≤ N ∧
    ((σ'.sc (P + 8) = 0 ∧ σ'.nat (n0 + 7) = N ∧ σ'.nat (n0 + 6) = t ∧
        ∃ (lo hi : ℤ) (kept : Option ((Fin d → ℤ) × ℤ)), σ'.sc (P + 9) = lo ∧ σ'.sc (P + 10) = hi ∧ |lo| ≤ M ∧
          |hi| ≤ M ∧ KeptIn P (a0 + 6) kept σ' ∧ KeptOK M F kept ∧
          bisT tf N lo0 hi0 kept0 = bisT tf (N - t) lo hi kept) ∨
      (σ'.sc (P + 8) = 1 ∧ σ'.nat (n0 + 7) = 0 ∧
        ∃ kept, KeptOK M F kept ∧ KeptIn P (a0 + 6) kept σ' ∧ bisT tf N lo0 hi0 kept0 = kept.map Prod.fst) ∨
      (σ'.sc (P + 8) = 2 ∧ σ'.nat (n0 + 7) = 0 ∧
        ∃ x, bisT tf N lo0 hi0 kept0 = some x ∧ (∀ k : Fin d, σ'.arr (a0 + 1) k = x k) ∧ ∀ k, |x k| ≤ M))

/-- The units of one turn of BIS-O with a test of `Kt` units. -/
def bkbT (d Kt : ℕ) : ℕ := 9 + (Kt + (tKE d + 8 + 2))

set_option maxHeartbeats 16000000 in
/-- **The loop of BIS-O on the oracle machine** (`d = 1`): `xbisLoopT` runs `bisT tf N lo0 hi0 kept0` from the
interval in the slots `P + 9`, `P + 10` and the kept point in the machine, for a test command `tc` computing `tf`. -/
theorem XVO.bisLoopT {L : Layout} {XO : XCtxO d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk}
    {I : EllI d} {nS nN nA P u a0 n0 F G N Kt s : ℕ} {tc : XCmdO}
    {tf : (Fin d → ℤ) → Option ((Fin d → ℤ) × ℤ) → Cut d} {Ctx : Env d → Prop} {TS TN : ℕ → Prop}
    {TA : ℕ → ℕ → Prop} {M lo0 hi0 : ℤ} {kept0 : Option ((Fin d → ℤ) × ℤ)}
    (hB : B.OK L nS nN nA) (lay : BisLay L B P u a0 (a0 + 6) n0) (hd : d = 1)
    (hCT : ∀ σ', Ctx σ' → TestEnv B I s P u (n0 + 4) σ' ∧ σ'.sc (u + 2) = 2)
    (henv : ∀ σa σb, Ctx σa → σb.draws = σa.draws → FrameA (bpS P u TS) (lpN n0 TN) (bpA a0 TA) σa σb → Ctx σb)
    (hTS : ∀ y, P + 8 ≤ y → y ≤ P + 11 → ¬ TS y) (hTN : ∀ j, n0 + 3 ≤ j → j ≠ n0 + 4 → j ≠ n0 + 5 → ¬ TN j)
    (hTA : ∀ k, ¬ TA (a0 + 1) k)
    (htest : ∀ σ' (a : Fin d → ℤ) kept, Ctx σ' → KeptIn P (a0 + 6) kept σ' → KeptOK M F kept →
      (∀ k : Fin d, σ'.arr (a0 + 1) k = a k) → (∀ k, |a k| ≤ M) →
      XRunsBO L XO ℓa ℓ tc σ' Kt (fun σ1 => TestOut P a0 (a0 + 6) (tf a kept) σ1 ∧ σ1.draws = σ'.draws ∧
        FrameA TS TN TA σ' σ1))
    (hret : ∀ a kept x, tf a kept = .ret x → x = a)
    (hcut : ∀ a kept c kept', (∀ k, |a k| ≤ M) → KeptOK M F kept → tf a kept = .cut c kept' →
      (∀ k, |c k| ≤ 2 ^ G) ∧ KeptOK M F kept')
    (hC : Ctx σ) (hlo : σ.sc (P + 9) = lo0) (hhi : σ.sc (P + 10) = hi0)
    (blo : |lo0| ≤ M) (bhi : |hi0| ≤ M) (hK : KeptIn P (a0 + 6) kept0 σ) (bK : KeptOK M F kept0)
    (hN : σ.nat (n0 + 7) = N) (hNa : N < 2 ^ ℓa) (bM : M ≤ 2 ^ F) (hF1 : 1 ≤ F) (hFG : F ≤ G)
    (hℓ : 64 * G + 16 < ℓ) :
    XRunsBO L XO ℓa ℓ (xbisLoopT L B tc P u a0 n0) σ (N * (bkbT d Kt + 2) + 4) (fun σ' =>
      LoopOut P a0 (a0 + 6) M F (bisT tf N lo0 hi0 kept0) σ' ∧ σ'.draws = σ.draws ∧
      FrameA (bpS P u TS) (lpN n0 TN) (bpA a0 TA) σ σ') := by
  obtain ⟨⟨tl, -, nNN⟩, PS⟩ := lay
  have tl' := tl
  obtain ⟨oP, Pu, uS, wa, -, aA, rn, -, -, -⟩ := tl'
  obtain ⟨⟨-, z, -, -, -, -, -, -⟩, -⟩ := hCT σ hC
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
  -- the frames of the pieces
  have mM : ∀ σa σb : Env d, FrameA (fun y => y = P + 11 ∨ u + 13 ≤ y) (fun j => j = n0 + 3)
      (fun b k => b = a0 + 1 ∧ k = 0) σa σb → FrameA (bpS P u TS) (lpN n0 TN) (bpA a0 TA) σa σb :=
    fun σa σb hF => hF.mono (fun y h => Or.inl (by omega)) (fun j h => Or.inl (by omega))
      (fun b k h => Or.inl h)
  have mE : ∀ σa σb : Env d, FrameA (fun y => y = P ∨ u + 16 ≤ y) (fun j => j = n0 + 1 ∨ j = n0 + 2)
      (fun _ _ => False) σa σb → FrameA (bpS P u TS) (lpN n0 TN) (bpA a0 TA) σa σb := fun σa σb hF =>
    hF.mono (fun y h => Or.inl (by omega)) (fun j h => Or.inl (by omega)) (fun _ _ h => h.elim)
  have mS : ∀ σa σb : Env d, FrameA (fun y => y = P + 8) (fun j => j = n0 + 7) (fun _ _ => False) σa σb →
      FrameA (bpS P u TS) (lpN n0 TN) (bpA a0 TA) σa σb := fun σa σb hF =>
    hF.mono (fun y h => Or.inl (by omega)) (fun j h => Or.inl (by omega)) (fun _ _ h => h.elim)
  -- the turn
  have hbody : ∀ t σ', BisInvT tf P u a0 n0 F N M TS TN TA lo0 hi0 kept0 σ t σ' →
      σ'.nat (n0 + 6) < σ'.nat (n0 + 7) →
      XRunsBO L XO ℓa ℓ (xbisBodyT L B tc P u a0 n0) σ' (bkbT d Kt)
        (BisInvT tf P u a0 n0 F N M TS TN TA lo0 hi0 kept0 σ (t + 1)) := by
    intro t σ' hJ hlt
    obtain ⟨d', F', -, -, hc⟩ := hJ
    rcases hc with ⟨s8, n7, n6, lo, hi, kept, ml, mh, bl, bh, mK, bK', hl⟩ | ⟨-, n7, -⟩ | ⟨-, n7, -⟩
    rotate_left
    · omega
    · omega
    obtain ⟨k, hk⟩ : ∃ k, N - t = k + 1 := ⟨N - t - 1, by omega⟩
    rw [hk] at hl
    obtain ⟨⟨-, z', -, -, -, -, -, -⟩, h2'⟩ := hCT σ' (henv σ σ' hC d' F')
    have bm : |((lo + hi) / 2)| ≤ M := abs_mid_le bl bh
    have bmF : |((lo + hi) / 2)| ≤ 2 ^ F := bm.trans bM
    unfold bkbT
    refine XVO.seq (K₂ := Kt + (tKE d + 8 + 2)) (XVO.ofX (XV.bisMid (X := XO.X) hL (lo := lo) (hi := hi) (F := F)
      (by omega) PS (by omega) (by omega) (by omega) z' h2' ml mh (bl.trans bM) (bh.trans bM) hF1
      (by omega))) fun σ1 ⟨m1, a1, r1, d1, F1⟩ => ?_
    have G1 := F'.trans (mM σ' σ1 F1)
    have D1 : σ1.draws = σ.draws := d1.trans d'
    have hC1 : Ctx σ1 := henv σ σ1 hC D1 G1
    have ha1 : ∀ k : Fin d, σ1.arr (a0 + 1) k = (fun _ => ((lo + hi) / 2)) k := fun k => by
      have hk0 := k.2
      rw [show (k : ℕ) = 0 by omega, a1]
    have hK1 : KeptIn P (a0 + 6) kept σ1 :=
      mK.frame (F1.2.1 _ (by omega)) (F1.2.1 _ (by omega)) (fun k => F1.2.2.1 _ _ (by omega))
    refine XVO.seq (K₂ := tKE d + 8 + 2)
      (htest σ1 (fun _ => ((lo + hi) / 2)) kept hC1 hK1 bK' ha1 (fun _ => bm)) fun σ2 ⟨o2, d2, F2⟩ => ?_
    have G2 := G1.trans (F2.mono (fun y h => Or.inr h) (fun j h => Or.inr h) (fun b k h => Or.inr h))
    have D2 : σ2.draws = σ.draws := d2.trans D1
    have hC2 : Ctx σ2 := henv σ σ2 hC D2 G2
    obtain ⟨hT2, u22⟩ := hCT σ2 hC2
    have hT2' := hT2
    obtain ⟨-, z2, -, -, -, -, -, -⟩ := hT2'
    have n62 : σ2.nat (n0 + 6) = t := by rw [F2.1 _ (hTN _ (by omega) (by omega) (by omega)), F1.1 _ (by omega), n6]
    have n72 : σ2.nat (n0 + 7) = N := by rw [F2.1 _ (hTN _ (by omega) (by omega) (by omega)), F1.1 _ (by omega), n7]
    have n32 : σ2.nat (n0 + 3) = 0 := by rw [F2.1 _ (hTN _ le_rfl (by omega) (by omega)), r1]
    have m2 : σ2.sc (P + 11) = (((lo + hi) / 2 : ℤ) : ℝ) := by rw [F2.2.1 _ (hTS _ (by omega) le_rfl), m1]
    have l2 : σ2.sc (P + 9) = lo := by
      rw [F2.2.1 _ (hTS _ (by omega) (by omega)), F1.2.1 _ (by omega), ml]
    have h2'' : σ2.sc (P + 10) = hi := by
      rw [F2.2.1 _ (hTS _ (by omega) (by omega)), F1.2.1 _ (by omega), mh]
    cases hte : tf (fun _ => ((lo + hi) / 2)) kept with
    | ret x =>
      rw [hte] at o2
      have o2' : σ2.sc P = 1 := o2
      have ex : x = fun _ => ((lo + hi) / 2) := hret _ _ _ hte
      refine XVO.mono (XVO.ifS_t hL (by omega) (by omega) (by rw [z2]; exact h0) (by rw [o2']; exact h1)
        (by rw [z2, o2']; norm_num)
        (XVO.ofX (XV.stop hL (w := 2) (by omega) (by omega) (by omega) (by omega) z2 u22 h2ℓ)))
        (by omega) fun σ3 ⟨s3, m3, d3, F3⟩ => ?_
      unfold BisInvT
      refine ⟨d3.trans D2, G2.trans (mS σ2 σ3 F3), by rw [F3.1 _ (by omega), n62]; omega, by rw [m3]; omega,
        Or.inr (Or.inr ⟨s3, m3, x, hl.trans (bisT_ret hte), fun k => ?_, fun k => ?_⟩)⟩
      · rw [F3.2.2.1 _ _ (fun h => h), F2.2.2.1 _ _ (hTA _), ha1, ex]
      · rw [ex]; exact bm
    | cut c kept' =>
      rw [hte] at o2
      obtain ⟨p2, c2, k2⟩ := o2
      have p2' : σ2.sc P = 0 := p2
      obtain ⟨bc, bK2⟩ := hcut _ _ _ _ (fun _ => bm) bK' hte
      refine XVO.mono (XVO.ifS_f hL (by omega) (by omega) (by rw [z2]; exact h0) (by rw [p2']; exact h0)
        (by rw [z2, p2']; exact lt_irrefl 0) (XVO.seq (K₂ := 8)
        (XVO.ofX (XV.testEnd (X := XO.X) (G := G) (c := c) hL hB tl hT2 c2 bc (by omega)))
        fun σ3 ⟨r3, c3, d3, F3⟩ => ?_)) (by unfold tKE; omega) fun _ h => h
      have G3 := G2.trans (mE σ2 σ3 F3)
      have D3 : σ3.draws = σ.draws := d3.trans D2
      obtain ⟨hT3, -⟩ := hCT σ3 (henv σ σ3 hC D3 G3)
      have hT3' := hT3
      obtain ⟨-, z3, o3, n43, -, -, -, -⟩ := hT3'
      have n63 : σ3.nat (n0 + 6) = t := by rw [F3.1 _ (by omega), n62]
      have n73 : σ3.nat (n0 + 7) = N := by rw [F3.1 _ (by omega), n72]
      have n33 : σ3.nat (n0 + 3) = 0 := by rw [F3.1 _ (by omega), n32]
      have m3 : σ3.sc (P + 11) = (((lo + hi) / 2 : ℤ) : ℝ) := by rw [F3.2.1 _ (by omega), m2]
      have l3 : σ3.sc (P + 9) = lo := by rw [F3.2.1 _ (by omega), l2]
      have h3 : σ3.sc (P + 10) = hi := by rw [F3.2.1 _ (by omega), h2'']
      have s83 : σ3.sc (P + 8) = 0 := by
        rw [F3.2.1 _ (by omega), F2.2.1 _ (hTS _ le_rfl (by omega)), F1.2.1 _ (by omega), s8]
      have hK3 : KeptIn P (a0 + 6) kept' σ3 := k2.frame (F3.2.1 _ (by omega)) (F3.2.1 _ (by omega))
        (fun k => F3.2.2.1 _ _ (fun h => h))
      have c03 : σ3.arr (a0 + 2) 0 = c ⟨0, by omega⟩ := by
        rw [F3.2.2.1 _ _ (fun h => h)]; exact c2 ⟨0, by omega⟩
      by_cases hc0 : c = 0
      · -- the cut vanishes: stop on the kept point
        have r3' : σ3.sc P = 1 := r3 hc0
        refine XVO.mono (XVO.ifS_t hL (by omega) (by omega) (by rw [z3]; exact h0) (by rw [r3']; exact h1)
          (by rw [z3, r3']; norm_num)
          (XVO.ofX (XV.stop hL (w := 1) (by omega) (by omega) (by omega) (by omega) z3 o3 h1)))
          (by omega) fun σ4 ⟨s4, m4, d4, F4⟩ => ?_
        unfold BisInvT
        refine ⟨d4.trans D3, G3.trans (mS σ3 σ4 F4), by rw [F4.1 _ (by omega), n63]; omega, by rw [m4]; omega,
          Or.inr (Or.inl ⟨s4, m4, kept', bK2, ?_, hl.trans (bisT_zero hte hc0)⟩)⟩
        exact hK3.frame (F4.2.1 _ (by omega)) (F4.2.1 _ (by omega)) (fun k => F4.2.2.1 _ _ (fun h => h))
      · -- the halving
        have r3' : σ3.sc P = 0 := c3 hc0
        have bc0 : |((c ⟨0, by omega⟩ : ℤ) : ℝ)| < 2 ^ ℓ := absR_lt (bc _) (by omega)
        refine XVO.mono (XVO.ifS_f hL (by omega) (by omega) (by rw [z3]; exact h0) (by rw [r3']; exact h0)
          (by rw [z3, r3']; exact lt_irrefl 0) (XVO.ofX (XV.seq (K₂ := 4)
          (XV.aget hL (x := u + 13) (a := a0 + 2) (i := n0 + 3) (by omega) (by omega) (by omega)
            (by rw [n33]; exact hasz) (by rw [n33, c03]; exact bc0)) fun σ4 e4 => ?_))) (by omega) fun _ h => h
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
        have G4 : FrameA (bpS P u TS) (lpN n0 TN) (bpA a0 TA) σ σ4 := by
          rw [e4]; exact G3.setSc (Or.inl (by omega)) _
        have e5 : ∀ y, ¬ (y = P + 9 ∨ y = P + 10) → y ≠ u + 13 → σ5.sc y = σ3.sc y := fun y hy hy' => by
          rw [F5.2.1 _ hy, e4]; simp [hy']
        have n65 : σ5.nat (n0 + 6) = t := by rw [F5.1 _ id, e4]; simp [n63]
        have n45 : σ5.nat (n0 + 4) = 1 := by rw [F5.1 _ id, e4]; simp [n43]
        have n75 : σ5.nat (n0 + 7) = N := by rw [F5.1 _ id, e4]; simp [n73]
        have D5 : σ5.draws = σ.draws := by rw [d5, e4]; simp [D3]
        have G5 : FrameA (bpS P u TS) (lpN n0 TN) (bpA a0 TA) σ σ5 :=
          G4.trans (F5.mono (fun y h => Or.inl (by omega)) (fun _ h => h.elim) (fun _ _ h => h.elim))
        have hK5 : KeptIn P (a0 + 6) kept' σ5 := hK3.frame (e5 _ (by omega) (by omega)) (e5 _ (by omega) (by omega))
          (fun k => by rw [F5.2.2.1 _ _ id, e4]; simp)
        have s85 : σ5.sc (P + 8) = 0 := by rw [e5 _ (by omega) (by omega), s83]
        refine XV.mono (XV.nadd hL (i := n0 + 6) (a := n0 + 6) (b := n0 + 4) (by omega) (by omega) (by omega)
          (by rw [n65]; omega) (by rw [n45]; exact hsa)) le_rfl fun σ6 e6 => ?_
        subst e6
        unfold BisInvT
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
            exact bisT_hi hte hc0 (by rw [hsum]; exact hpos)
          · simp only [hpos, ↓reduceIte]
            exact bisT_lo hte hc0 (by rw [hsum]; exact hpos)
  -- the loop
  have hb : ∀ t σ', BisInvT tf P u a0 n0 F N M TS TN TA lo0 hi0 kept0 σ t σ' →
      σ'.nat (n0 + 6) < 2 ^ ℓa ∧ σ'.nat (n0 + 7) < 2 ^ ℓa := fun t σ' h => by
    obtain ⟨-, -, i6, i7, -⟩ := h
    omega
  have hlt : ∀ t σ', BisInvT tf P u a0 n0 F N M TS TN TA lo0 hi0 kept0 σ t σ' →
      σ'.nat (n0 + 6) < σ'.nat (n0 + 7) → t < N := fun t σ' h hl => by
    obtain ⟨-, -, -, -, hc⟩ := h
    rcases hc with ⟨-, n7, n6, -⟩ | ⟨-, n7, -⟩ | ⟨-, n7, -⟩ <;> omega
  refine XVO.mono (Q := fun σ' => ∃ t', BisInvT tf P u a0 n0 F N M TS TN TA lo0 hi0 kept0 σ t' σ' ∧
      ¬ σ'.nat (n0 + 6) < σ'.nat (n0 + 7)) (XVO.seq (K₂ := 1 + ((N - 0) * (bkbT d Kt + 2) + 2))
    (XVO.nconst hL (XO := XO) (ℓ := ℓ) (i := n0 + 6) (by omega) 0 (by positivity)) fun σa ea => ?_)
    (by simp only [Nat.sub_zero]; omega) ?_
  · subst ea
    have za : (σ.setNat (n0 + 6) 0).sc u = 0 := by simp [z]
    refine XVO.seq (XVO.ofX (XV.sop2 hL (x := P + 8) (a := u) (b := u) (by omega) (by omega) (by omega) .add
      (by intro h; cases h) (by rw [za]; exact h0) (by rw [za]; exact h0)
      (by simp only [RealRAM.Op2.eval, za, add_zero]; exact h0))) fun σb eb => ?_
    subst eb
    refine XVO.whileN hL (by omega) (by omega) (BisInvT tf P u a0 n0 F N M TS TN TA lo0 hi0 kept0 σ) N
      (bkbT d Kt) hb hlt hbody 0 _ ?_
    unfold BisInvT
    refine ⟨by simp, ((FrameA.refl _ _ _ σ).setNat (Or.inl (by omega)) 0).setSc (Or.inl (by omega)) _, by simp,
      by simp [hN], Or.inl ⟨by simp [RealRAM.Op2.eval, z], by simp [hN], by simp,
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

end AdversarialBco.Uni.EllO
