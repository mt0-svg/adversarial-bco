/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XEllTest

@[expose] public section

/-!
# The loop of ELL-R on the machine

`xellLoop` runs `ellLoop I N st` (Bit/RoutQ.lean) from the state `st` in the machine: the matrix `Â` in the array `a0`
(entry `(i, k)` in the cell `d i + k`), the centre `â` in the array `a0 + 1`, the kept point in the slots `P + 1`,
`P + 2` and the array `kb`. Each turn: the tests (`xtest` at the scale `2^p`), then on a cut the test `c = 0`
(`xtestEnd`) and the update (`xupd`). The slot `P + 8` gets the outcome: `2` for a returned point (in the array
`a0 + 1`), `1` for a stop on the kept point, `0` when the `N` turns ran out (the kept point). Registers: the turn `n0 + 6`,
the bound `n0 + 7`.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## The program -/

/-- The outcome `v` (a slot holding `1` or `2`) into `P + 8`, and the end of the loop. -/
def xellStop (L : Layout) (P u n0 v : ℕ) : XCmd :=
  .seq (xset L (P + 8) v u) (.prim (.frag (.nconst (n0 + 7) 0)))

/-- One turn of ELL-R. -/
def xellBody (L : Layout) (B : EllBlk) (rowc : XCmd) (P u a0 kb n0 : ℕ) : XCmd :=
  .seq (xtest L B rowc P u a0 kb n0 (n0 + 4) (n0 + 5))
  (xifS L u P (xellStop L P u n0 (u + 2))
    (.seq (xtestEnd L B P u a0 n0 (n0 + 4))
      (xifS L u P (xellStop L P u n0 (u + 1))
        (.seq (xupd L u a0 n0 B.rd (n0 + 4))
          (xifS L u (u + 13) (xellStop L P u n0 (u + 1)) (.prim (.frag (.nadd (n0 + 6) (n0 + 6) (n0 + 4)))))))))

/-- The loop: the turn to `0`, the outcome to `0`, at most `nat (n0 + 7)` turns. -/
def xellLoop (L : Layout) (B : EllBlk) (rowc : XCmd) (P u a0 kb n0 : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst (n0 + 6) 0))) (.seq (xset L (P + 8) u u)
    (.whileN (n0 + 6) (n0 + 7) (xellBody L B rowc P u a0 kb n0)))

/-! ## The data -/

/-- The constants of the update step in the slots `u + 2, ..., u + 12`. -/
def UpdEnv (u p q j : ℕ) (capA capa : ℤ) (σ : Env d) : Prop :=
  σ.sc (u + 2) = 2 ∧ σ.sc (u + 3) = 4 ∧ σ.sc (u + 4) = (((2 : ℤ) ^ (p - 2 * j) : ℤ) : ℝ) ∧
    σ.sc (u + 5) = (2 : ℤ) ^ (2 * q) ∧ σ.sc (u + 6) = (2 : ℤ) ^ p ∧ σ.sc (u + 7) = (2 : ℤ) ^ q ∧
    σ.sc (u + 8) = (d : ℤ) + 1 ∧ σ.sc (u + 9) = kapN d ∧ σ.sc (u + 10) = kapD d ∧ σ.sc (u + 11) = capA ∧
    σ.sc (u + 12) = capa

theorem UpdEnv.frame {u p q j : ℕ} {capA capa : ℤ} {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop} {σ σ' : Env d}
    (h : UpdEnv u p q j capA capa σ) (hF : FrameA S N Ar σ σ') (hS : ∀ y, S y → y < u + 2 ∨ u + 12 < y) :
    UpdEnv u p q j capA capa σ' := by
  have e : ∀ y, u + 2 ≤ y → y ≤ u + 12 → σ'.sc y = σ.sc y := fun y h1 h2 =>
    hF.2.1 y fun hs => by rcases hS y hs with h | h <;> omega
  obtain ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨by rw [e _ (by omega) (by omega), h2], by rw [e _ (by omega) (by omega), h3],
    by rw [e _ (by omega) (by omega), h4], by rw [e _ (by omega) (by omega), h5],
    by rw [e _ (by omega) (by omega), h6], by rw [e _ (by omega) (by omega), h7],
    by rw [e _ (by omega) (by omega), h8], by rw [e _ (by omega) (by omega), h9],
    by rw [e _ (by omega) (by omega), h10], by rw [e _ (by omega) (by omega), h11],
    by rw [e _ (by omega) (by omega), h12]⟩

/-- The kept point within its bounds: the point below `capa`, the value below `2^{6F+1}`. -/
def KeptOK (capa : ℤ) (F : ℕ) (kept : Option ((Fin d → ℤ) × ℤ)) : Prop :=
  ∀ b W, kept = some (b, W) → (∀ k, |b k| ≤ capa) ∧ |W| ≤ 2 ^ (6 * F + 1)

/-- The cells of the loop above the bases: the layout of the tests, the outcome `P + 8`, the registers `n0 + 6`,
`n0 + 7`. -/
structure LoopLay (L : Layout) (B : EllBlk) (P u a0 kb n0 : ℕ) : Prop where
  test : TestLay L B P u a0 kb n0 (n0 + 4) (n0 + 5)
  PS : P + 9 ≤ u
  nN : n0 + 8 ≤ L.NN

/-- The outcome of the loop on the result `r`: `2` in `P + 8` and the point in the array `a0 + 1`, or `0`, `1` in
`P + 8` and `r` the kept point. -/
def LoopOut (P a0 kb : ℕ) (capa : ℤ) (F : ℕ) (r : Option (Fin d → ℤ)) (σ : Env d) : Prop :=
  (σ.sc (P + 8) = 2 ∧ ∃ x, r = some x ∧ (∀ k : Fin d, σ.arr (a0 + 1) k = x k) ∧ ∀ k, |x k| ≤ capa) ∨
    ((σ.sc (P + 8) = 0 ∨ σ.sc (P + 8) = 1) ∧
      ∃ kept, KeptOK capa F kept ∧ KeptIn P kb kept σ ∧ r = kept.map Prod.fst)

/-- The units of one turn. -/
def ellKb (d m Kr E : ℕ) : ℕ := testK d m Kr + (tKE d + (200 * (E + 1) ^ 2 + (1 + 2) + 2) + 2)

theorem ellV_le {I : EllI d} {s F : ℕ} {a : Fin d → ℤ} (ba : ∀ k, |a k| ≤ 2 ^ F) (hσF : ellSz I ≤ F)
    (hsF : s + 1 ≤ F) (hdF : d ≤ F) :
    |(I.Df : ℤ) * (a ⬝ᵥ (I.P *ᵥ a)) - 2 ^ (s + 1) * (I.f ⬝ᵥ a)| ≤ 2 ^ (6 * F + 1) := by
  have bw : ∀ k, |(I.P *ᵥ a) k| ≤ 2 ^ (3 * F) := fun k =>
    abs_le_pow_mono (abs_mulVec_le' hdF (ellP_le hσF) ba k) (by omega)
  exact abs_sub_le_pow (abs_le_pow_mono (abs_mul_le_pow (ellDf_le hσF) (abs_dot_le' hdF ba bw)) (by omega))
    (abs_le_pow_mono (abs_mul_le_pow (abs_pow_le hsF) (abs_dot_le' hdF (ellF_le hσF) ba)) (by omega))

theorem ellLoop_ret {I : EllI d} {k : ℕ} {st : ESt d} {x : Fin d → ℤ} (h : ellTest I I.p st.a st.kept = .ret x) :
    ellLoop I (k + 1) st = some x := by
  rw [ellLoop, h]

theorem ellLoop_zero {I : EllI d} {k : ℕ} {st : ESt d} {c : Fin d → ℤ} {kept : Option ((Fin d → ℤ) × ℤ)}
    (h : ellTest I I.p st.a st.kept = .cut c kept) (hc : c = 0) : ellLoop I (k + 1) st = kept.map Prod.fst := by
  rw [ellLoop, h]; simp [hc]

theorem ellLoop_fail {I : EllI d} {k : ℕ} {st : ESt d} {c : Fin d → ℤ} {kept : Option ((Fin d → ℤ) × ℤ)}
    {capA capa : ℤ} (hcA : capA = (2 : ℤ) ^ I.p * I.Lam) (hca : capa = (2 : ℤ) ^ I.p * (I.Rb + I.LamH))
    (h : ellTest I I.p st.a st.kept = .cut c kept) (hc : c ≠ 0) (hu : ellUpd I.p I.q I.j capA capa st.A st.a c = none) :
    ellLoop I (k + 1) st = kept.map Prod.fst := by
  subst hcA hca
  rw [ellLoop, h]; simp [hc, hu]

theorem ellLoop_next {I : EllI d} {k : ℕ} {st : ESt d} {c : Fin d → ℤ} {kept : Option ((Fin d → ℤ) × ℤ)}
    {A' : Matrix (Fin d) (Fin d) ℤ} {a' : Fin d → ℤ} {capA capa : ℤ} (hcA : capA = (2 : ℤ) ^ I.p * I.Lam)
    (hca : capa = (2 : ℤ) ^ I.p * (I.Rb + I.LamH)) (h : ellTest I I.p st.a st.kept = .cut c kept) (hc : c ≠ 0)
    (hu : ellUpd I.p I.q I.j capA capa st.A st.a c = some (A', a')) :
    ellLoop I (k + 1) st = ellLoop I k ⟨A', a', kept⟩ := by
  subst hcA hca
  rw [ellLoop, h]; simp [hc, hu]

/-! ## The loop on the machine -/

/-- The state `st` of the loop in the machine, within its bounds. -/
def LoopSt (P a0 kb : ℕ) (capA capa : ℤ) (F : ℕ) (st : ESt d) (σ : Env d) : Prop :=
  (∀ i k : Fin d, σ.arr a0 (d * i + k) = st.A i k) ∧ (∀ k : Fin d, σ.arr (a0 + 1) k = st.a k) ∧
    KeptIn P kb st.kept σ ∧ (∀ i k, |st.A i k| ≤ capA) ∧ (∀ k, |st.a k| ≤ capa) ∧ KeptOK capa F st.kept

theorem LoopSt.frame {P a0 kb : ℕ} {capA capa : ℤ} {F : ℕ} {st : ESt d} {σ σ' : Env d}
    (h : LoopSt P a0 kb capA capa F st σ) (hA : ∀ k, σ'.arr a0 k = σ.arr a0 k)
    (ha : ∀ k, σ'.arr (a0 + 1) k = σ.arr (a0 + 1) k) (h1 : σ'.sc (P + 1) = σ.sc (P + 1))
    (h2 : σ'.sc (P + 2) = σ.sc (P + 2)) (hk : ∀ k, σ'.arr kb k = σ.arr kb k) : LoopSt P a0 kb capA capa F st σ' := by
  obtain ⟨mA, ma, mK, bA, ba, bK⟩ := h
  exact ⟨fun i k => (hA _).trans (mA i k), fun k => (ha _).trans (ma k), mK.frame h1 h2 hk, bA, ba, bK⟩

/-- The slots the loop may change. -/
abbrev loopS (B : EllBlk) (P u : ℕ) (SR : ℕ → Prop) (y : ℕ) : Prop :=
  (y = P ∨ y = P + 1 ∨ y = P + 2 ∨ y = P + 7 ∨ y = P + 8 ∨ u + 13 ≤ y ∨ y = B.o + 2) ∨ SR y

/-- The registers the loop may change. -/
abbrev loopN (B : EllBlk) (n0 : ℕ) (NR : ℕ → Prop) (j : ℕ) : Prop :=
  (j = B.rE ∨ (n0 ≤ j ∧ j ≤ n0 + 3) ∨ (n0 + 5 ≤ j ∧ j ≤ n0 + 7)) ∨ NR j

/-- The array cells the loop may change. -/
abbrev loopA (B : EllBlk) (a0 : ℕ) (AR : ℕ → Prop) (b _k : ℕ) : Prop :=
  (b = B.aW + 1 ∨ (a0 ≤ b ∧ b ≤ a0 + 6)) ∨ AR b

/-- The invariant of the loop after `t` turns from `σ`: the turns still running (outcome `0`, the turn `t` in
`n0 + 6`, a state of the loop with `ellLoop I (N - t)` left), or stopped on the kept point (outcome `1`) or on a
returned point (outcome `2`), the bound `n0 + 7` then `0`. -/
def LoopInv (B : EllBlk) (I : EllI d) (P u a0 n0 F N : ℕ) (capA capa : ℤ) (SR NR AR : ℕ → Prop) (st : ESt d)
    (σ : Env d) (t : ℕ) (σ' : Env d) : Prop :=
  σ'.draws = σ.draws ∧ FrameA (loopS B P u SR) (loopN B n0 NR) (loopA B a0 AR) σ σ' ∧
    σ'.nat (n0 + 6) ≤ N ∧ σ'.nat (n0 + 7) ≤ N ∧
    ((σ'.sc (P + 8) = 0 ∧ σ'.nat (n0 + 7) = N ∧ σ'.nat (n0 + 6) = t ∧
        ∃ st' : ESt d, LoopSt P a0 (a0 + 6) capA capa F st' σ' ∧ ellLoop I N st = ellLoop I (N - t) st') ∨
      (σ'.sc (P + 8) = 1 ∧ σ'.nat (n0 + 7) = 0 ∧
        ∃ kept, KeptOK capa F kept ∧ KeptIn P (a0 + 6) kept σ' ∧ ellLoop I N st = kept.map Prod.fst) ∨
      (σ'.sc (P + 8) = 2 ∧ σ'.nat (n0 + 7) = 0 ∧
        ∃ x, ellLoop I N st = some x ∧ (∀ k : Fin d, σ'.arr (a0 + 1) k = x k) ∧ ∀ k, |x k| ≤ capa))

/-- The rule of `xellStop`: the value `w` of the slot `v` into `P + 8`, the bound `n0 + 7` to `0`. -/
theorem XV.stop {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {P u n0 v : ℕ} {w : ℝ}
    (hP : P + 8 < L.NS) (hv : v < L.NS) (hu : u < L.NS) (hn : n0 + 7 < L.NN) (hz : σ.sc u = 0)
    (hw : σ.sc v = w) (bw : |w| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xellStop L P u n0 v) σ 2 (fun σ' => σ'.sc (P + 8) = w ∧ σ'.nat (n0 + 7) = 0 ∧
      σ'.draws = σ.draws ∧ FrameA (fun y => y = P + 8) (fun j => j = n0 + 7) (fun _ _ => False) σ σ') := by
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by simp only [abs_zero]; positivity
  have e : RealRAM.Op2.eval .add (σ.sc v) (σ.sc u) = w := by simp [RealRAM.Op2.eval, hw, hz]
  refine XV.seq (K₂ := 1) (XV.sop2 hL (x := P + 8) (a := v) (b := u) hP hv hu .add (by intro h; cases h)
    (by rw [hw]; exact bw) (by rw [hz]; exact h0) (by rw [e]; exact bw)) fun σ1 e1 => ?_
  subst e1
  refine XV.mono (XV.nconst hL hn 0 (by positivity)) le_rfl fun σ2 e2 => ?_
  subst e2
  refine ⟨by simp [e], by simp, by simp, ?_⟩
  exact ((FrameA.refl (fun y => y = P + 8) (fun j => j = n0 + 7) (fun _ _ => False) σ).setSc rfl _).setNat rfl 0

set_option maxHeartbeats 16000000 in
/-- **The loop of ELL-R on the machine**: `xellLoop` runs `ellLoop I N st` from the state `st` in the machine
(`LoopSt`), `N` in the register `n0 + 7`, the constants of the tests (`TestEnv` at the scale `2^p`) and of the update
(`UpdEnv`) in place. The point `â` stays below `capa ≤ 2^F`, the matrix below `capA ≤ 2^E`, every cut below `2^E`. -/
theorem XV.ellLoop {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk} {I : EllI d}
    {nS nN nA P u a0 kb n0 F E Kr N : ℕ} {rowc : XCmd} {Ctx : Env d → Prop} {SR NR AR : ℕ → Prop}
    {capA capa : ℤ} {st : ESt d} (hB : B.OK L nS nN nA) (hav : B.Avoid SR NR AR)
    (hrow : RowProv L X ℓa ℓ I B rowc Ctx SR NR AR Kr) (hctx : CtxOK B Ctx SR NR AR)
    (lay : LoopLay L B P u a0 kb n0) (hT : TestEnv B I I.p P u (n0 + 4) σ)
    (hU : UpdEnv u I.p I.q I.j capA capa σ) (hC : Ctx σ) (hS : LoopSt P a0 kb capA capa F st σ)
    (hN : σ.nat (n0 + 7) = N) (hNa : N < 2 ^ ℓa)
    (hcA : capA = (2 : ℤ) ^ I.p * I.Lam) (hca : capa = (2 : ℤ) ^ I.p * (I.Rb + I.LamH))
    (hcA0 : 0 ≤ capA) (hca0 : 0 ≤ capa) (bcA : capA ≤ 2 ^ E) (bca : capa ≤ 2 ^ F)
    (hσF : ellSz I ≤ F) (hpF : 2 * I.p + 1 ≤ F) (hdF : d ≤ F) (hFE : F + 2 * ellSz I + d + I.p + 2 ≤ E)
    (hq : 2 * I.q ≤ E) (bkN : |kapN d| ≤ 2 ^ E) (bkD : |kapD d| ≤ 2 ^ E) (hm : I.m < 2 ^ ℓa)
    (hℓ : 64 * E + 16 < ℓ) :
    XRunsB L X ℓa ℓ (xellLoop L B rowc P u a0 kb n0) σ (N * (ellKb d I.m Kr E + 2) + 4) (fun σ' =>
      LoopOut P a0 kb capa F (ellLoop I N st) σ' ∧ σ'.draws = σ.draws ∧
      FrameA (loopS B P u SR) (loopN B n0 NR) (loopA B a0 AR) σ σ') := by
  have hrow' := hrow
  obtain ⟨hsr, hnr, har, -⟩ := hrow'
  obtain ⟨tl, PS, nNN⟩ := lay
  have tl' := tl
  obtain ⟨oP, Pu, uS, wa, kbe, aA, rn, -, -, -⟩ := tl'
  subst kbe
  have hB' := hB
  obtain ⟨-, -, -, hrd, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hB'
  have hT' := hT
  obtain ⟨-, z, -, -, -, -, -, -⟩ := hT'
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by simp only [abs_zero]; positivity
  have h1 : |(1 : ℝ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  have h2 : |(2 : ℝ)| < 2 ^ ℓ := by
    rw [abs_two]
    have := pow_lt_pow_right₀ (show (1 : ℝ) < 2 by norm_num) (show 1 < ℓ by omega)
    simpa using this
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  -- the fixed data along the loop
  have hS0 : ∀ y, loopS B P u SR y → (B.o ≤ y ∧ y ≠ u ∧ y ≠ u + 1 ∧ (y < P + 3 ∨ P + 6 < y)) ∨ SR y :=
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
  have env : ∀ σ', σ'.draws = σ.draws → FrameA (loopS B P u SR) (loopN B n0 NR) (loopA B a0 AR) σ σ' →
      TestEnv B I I.p P u (n0 + 4) σ' ∧ UpdEnv u I.p I.q I.j capA capa σ' ∧ Ctx σ' := fun σ' hd hF =>
    ⟨TestEnv.frame hB hav hsr hnr har (by omega) (by omega) (by omega) hT hF hS0 hN0 hA0,
      hU.frame hF (fun y h => by
        rcases h with h | h
        · omega
        · have := hsr y h; omega),
      hctx σ σ' hC hd (hF.mono (fun y h => by
        rcases hS0 y h with h | h
        · exact Or.inl h.1
        · exact Or.inr h) (fun j h => by
        rcases hN0 j h with h | h
        · exact Or.inl h.1
        · exact Or.inr h) hA0)⟩
  -- the frames of the pieces
  have mT : ∀ σa σb : Env d, FrameA
      (fun y => y = P ∨ y = P + 1 ∨ y = P + 2 ∨ y = P + 7 ∨ u + 13 ≤ y ∨ y = B.o + 2 ∨ SR y)
      (fun j => j = B.rE ∨ (n0 ≤ j ∧ j ≤ n0 + 2) ∨ j = n0 + 5 ∨ NR j)
      (fun b _ => b = B.aW + 1 ∨ b = a0 + 2 ∨ b = a0 + 3 ∨ b = a0 + 6 ∨ AR b) σa σb →
      FrameA (loopS B P u SR) (loopN B n0 NR) (loopA B a0 AR) σa σb := fun σa σb hF =>
    hF.mono (fun y h => by
      rcases h with h | h | h | h | h | h | h
      all_goals first | exact Or.inr h | exact Or.inl (by omega)) (fun j h => by
      rcases h with h | h | h | h
      all_goals first | exact Or.inr h | exact Or.inl (by omega)) (fun b k h => by
      rcases h with h | h | h | h | h
      all_goals first | exact Or.inr h | exact Or.inl (by omega))
  have mE : ∀ σa σb : Env d, FrameA (fun y => y = P ∨ u + 16 ≤ y) (fun j => j = n0 + 1 ∨ j = n0 + 2)
      (fun _ _ => False) σa σb → FrameA (loopS B P u SR) (loopN B n0 NR) (loopA B a0 AR) σa σb := fun σa σb hF =>
    hF.mono (fun y h => Or.inl (by omega)) (fun j h => Or.inl (by omega)) (fun _ _ h => h.elim)
  have mU : ∀ σa σb : Env d, FrameA (fun y => u + 13 ≤ y) (fun j => n0 ≤ j ∧ j < n0 + 4)
      (fun b k => a0 ≤ b ∧ b < a0 + 6 ∧ b ≠ a0 + 2 ∧ k < d * d) σa σb →
      FrameA (loopS B P u SR) (loopN B n0 NR) (loopA B a0 AR) σa σb := fun σa σb hF =>
    hF.mono (fun y h => Or.inl (by omega)) (fun j h => Or.inl (by omega)) (fun b k h => Or.inl (by omega))
  have mS : ∀ σa σb : Env d, FrameA (fun y => y = P + 8) (fun j => j = n0 + 7) (fun _ _ => False) σa σb →
      FrameA (loopS B P u SR) (loopN B n0 NR) (loopA B a0 AR) σa σb := fun σa σb hF =>
    hF.mono (fun y h => Or.inl (by omega)) (fun j h => Or.inl (by omega)) (fun _ _ h => h.elim)
  -- cells the tests keep
  have nTN : ∀ j, n0 + 3 ≤ j → j ≠ n0 + 5 → ¬ (j = B.rE ∨ (n0 ≤ j ∧ j ≤ n0 + 2) ∨ j = n0 + 5 ∨ NR j) := by
    intro j hj1 hj2 h
    rcases h with h | h | h | h
    · omega
    · omega
    · omega
    · have := hnr j h; omega
  have nTS : ¬ (P + 8 = P ∨ P + 8 = P + 1 ∨ P + 8 = P + 2 ∨ P + 8 = P + 7 ∨ u + 13 ≤ P + 8 ∨ P + 8 = B.o + 2 ∨
      SR (P + 8)) := by
    intro h
    rcases h with h | h | h | h | h | h | h
    all_goals first | omega | exact absurd (hsr _ h) (by omega)
  have nTA : ∀ b, (b = a0 ∨ b = a0 + 1) → ¬ (b = B.aW + 1 ∨ b = a0 + 2 ∨ b = a0 + 3 ∨ b = a0 + 6 ∨ AR b) := by
    intro b hb h
    rcases h with h | h | h | h | h
    all_goals first | omega | exact absurd (har _ h) (by omega)
  -- the turn
  have hbody : ∀ t σ', LoopInv B I P u a0 n0 F N capA capa SR NR AR st σ t σ' →
      σ'.nat (n0 + 6) < σ'.nat (n0 + 7) →
      XRunsB L X ℓa ℓ (xellBody L B rowc P u a0 (a0 + 6) n0) σ' (ellKb d I.m Kr E)
        (LoopInv B I P u a0 n0 F N capA capa SR NR AR st σ (t + 1)) := by
    intro t σ' hJ hlt
    obtain ⟨d', F', -, -, hc⟩ := hJ
    rcases hc with ⟨s8, n7, n6, st', ⟨mA, ma, mK, bA', ba', bK'⟩, hl⟩ | ⟨-, n7, -⟩ | ⟨-, n7, -⟩
    rotate_left
    · omega
    · omega
    obtain ⟨k, hk⟩ : ∃ k, N - t = k + 1 := ⟨N - t - 1, by omega⟩
    rw [hk] at hl
    obtain ⟨hT', -, hC'⟩ := env σ' d' F'
    have ba2 : ∀ k, |st'.a k| ≤ 2 ^ F := fun k => (ba' k).trans bca
    unfold ellKb
    refine XV.seq (K₂ := tKE d + (200 * (E + 1) ^ 2 + (1 + 2) + 2) + 2)
      (XV.test (X := X) (s := I.p) hL hB hav hrow hctx tl hT' hC' mK (fun b W h => (bK' b W h).2) ma ba2 hσF hpF
        hdF hm (by omega)) fun σ1 ⟨o1, d1, F1⟩ => ?_
    have G1 := F'.trans (mT σ' σ1 F1)
    have D1 : σ1.draws = σ.draws := d1.trans d'
    obtain ⟨hT1, hU1, -⟩ := env σ1 D1 G1
    have hT1' := hT1
    obtain ⟨-, z1, -, -, -, -, -, -⟩ := hT1'
    have n6' : σ1.nat (n0 + 6) = t := by rw [F1.1 _ (nTN _ (by omega) (by omega)), n6]
    have n7' : σ1.nat (n0 + 7) = N := by rw [F1.1 _ (nTN _ (by omega) (by omega)), n7]
    have s8' : σ1.sc (P + 8) = 0 := by rw [F1.2.1 _ nTS, s8]
    have mA1 : ∀ i k : Fin d, σ1.arr a0 (d * i + k) = st'.A i k := fun i k => by
      rw [F1.2.2.1 _ _ (nTA _ (Or.inl rfl)), mA]
    have ma1 : ∀ k : Fin d, σ1.arr (a0 + 1) k = st'.a k := fun k => by
      rw [F1.2.2.1 _ _ (nTA _ (Or.inr rfl)), ma]
    cases hte : ellTest I I.p st'.a st'.kept with
    | ret x =>
      rw [hte] at o1
      have o1' : σ1.sc P = 1 := o1
      have ex : x = st'.a := ellTest_ret I I.p st'.a x st'.kept hte
      obtain ⟨u2, -⟩ := hU1
      refine XV.mono (XV.ifS_t hL (by omega) (by omega) (by rw [z1]; exact h0) (by rw [o1']; exact h1)
        (by rw [z1, o1']; norm_num) (XV.stop hL (w := 2) (by omega) (by omega) (by omega) (by omega) z1 u2 h2))
        (by omega) fun σ2 ⟨s2, m2, d2, F2⟩ => ?_
      unfold LoopInv
      refine ⟨d2.trans D1, G1.trans (mS σ1 σ2 F2), by rw [F2.1 _ (by omega), n6']; omega, by rw [m2]; omega,
        Or.inr (Or.inr ⟨s2, m2, x, hl.trans (ellLoop_ret hte), fun k => ?_, fun k => ?_⟩)⟩
      · rw [F2.2.2.1 _ _ (fun h => h), ma1, ex]
      · rw [ex]; exact ba' k
    | cut c kept' =>
      rw [hte] at o1
      obtain ⟨p1, c1, k1⟩ := o1
      have p1' : σ1.sc P = 0 := p1
      have bc : ∀ k, |c k| ≤ 2 ^ E := fun k =>
        abs_le_pow_mono (ellCut_le I I.p F st'.a c st'.kept kept' ba2 hte k) hFE
      have bK1 : KeptOK capa F kept' := by
        rcases (ellTest_cut I I.p st'.a c st'.kept kept' hte).2 with e | e
        · rw [e]; exact bK'
        · rw [e]
          intro b W h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨ba', ellV_le ba2 hσF (by omega) hdF⟩
      refine XV.mono (XV.ifS_f hL (by omega) (by omega) (by rw [z1]; exact h0) (by rw [p1']; exact h0)
        (by rw [z1, p1']; exact lt_irrefl 0) (XV.seq (K₂ := 200 * (E + 1) ^ 2 + (1 + 2) + 2)
        (XV.testEnd (X := X) (G := E) (c := c) hL hB tl hT1 c1 bc (by omega)) fun σ2 ⟨r2, c2, d2, F2⟩ => ?_))
        (by unfold tKE; omega) fun _ h => h
      have G2 := G1.trans (mE σ1 σ2 F2)
      have D2 : σ2.draws = σ.draws := d2.trans D1
      obtain ⟨hT2, hU2, -⟩ := env σ2 D2 G2
      have hT2' := hT2
      obtain ⟨⟨hσd, -⟩, z2, o2, n42, -, -, -, -⟩ := hT2'
      have n62 : σ2.nat (n0 + 6) = t := by rw [F2.1 _ (by omega), n6']
      have n72 : σ2.nat (n0 + 7) = N := by rw [F2.1 _ (by omega), n7']
      have s82 : σ2.sc (P + 8) = 0 := by rw [F2.2.1 _ (by omega), s8']
      by_cases hc0 : c = 0
      · -- the gradient vanishes: stop on the kept point
        have r2' : σ2.sc P = 1 := r2 hc0
        refine XV.mono (XV.ifS_t hL (by omega) (by omega) (by rw [z2]; exact h0) (by rw [r2']; exact h1)
          (by rw [z2, r2']; norm_num) (XV.stop hL (w := 1) (by omega) (by omega) (by omega) (by omega) z2 o2 h1))
          (by omega) fun σ3 ⟨s3, m3, d3, F3⟩ => ?_
        unfold LoopInv
        refine ⟨d3.trans D2, G2.trans (mS σ2 σ3 F3), by rw [F3.1 _ (by omega), n62]; omega, by rw [m3]; omega,
          Or.inr (Or.inl ⟨s3, m3, kept', bK1, ?_, hl.trans (ellLoop_zero hte hc0)⟩)⟩
        exact k1.frame (by rw [F3.2.1 _ (by omega), F2.2.1 _ (by omega)])
          (by rw [F3.2.1 _ (by omega), F2.2.1 _ (by omega)])
          (fun k => by rw [F3.2.2.1 _ _ (fun h => h), F2.2.2.1 _ _ (fun h => h)])
      · -- the update
        have r2' : σ2.sc P = 0 := c2 hc0
        obtain ⟨e2, e4, eK1, eQ2, eP, eQ, ed1, ekN, ekD, ecA, eca⟩ := hU2
        refine XV.mono (XV.ifS_f hL (by omega) (by omega) (by rw [z2]; exact h0) (by rw [r2']; exact h0)
          (by rw [z2, r2']; exact lt_irrefl 0) (XV.seq (K₂ := 1 + 2)
          (XV.upd (X := X) (u := u) (a0 := a0) (n0 := n0) (nd := B.rd) (none := n0 + 4) (E := E) (p := I.p)
            (q := I.q) (j := I.j) (A := st'.A) (a := st'.a) (c := c) (capA := capA) (capa := capa) hL
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) z2 o2 e2 e4 eK1
            eQ2 eP eQ ed1 ekN ekD ecA eca hσd n42
            (fun i k => by rw [F2.2.2.1 _ _ (fun h => h), mA1])
            (fun k => by rw [F2.2.2.1 _ _ (fun h => h), ma1])
            (fun k => by rw [F2.2.2.1 _ _ (fun h => h), c1])
            (fun i k => (bA' i k).trans bcA)
            (fun k => (ba2 k).trans (pow_le_pow_right₀ (by norm_num) (by omega))) bc (by omega) (by omega)
            (by omega) hq bkN bkD hcA0 hca0 bcA (bca.trans (pow_le_pow_right₀ (by norm_num) (by omega))) hℓ)
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
        cases hu : ellUpd I.p I.q I.j capA capa st'.A st'.a c with
        | none =>
          rw [hu] at u3
          have u3' : σ3.sc (u + 13) = 1 := u3
          refine XV.mono (XV.ifS_t hL (by omega) (by omega) (by rw [z3]; exact h0) (by rw [u3']; exact h1)
            (by rw [z3, u3']; norm_num) (XV.stop hL (w := 1) (by omega) (by omega) (by omega) (by omega) z3 o3 h1))
            (by omega) fun σ4 ⟨s4, m4, d4, F4⟩ => ?_
          unfold LoopInv
          refine ⟨d4.trans D3, G3.trans (mS σ3 σ4 F4), by rw [F4.1 _ (by omega), n63]; omega, by rw [m4]; omega,
            Or.inr (Or.inl ⟨s4, m4, kept', bK1, ?_, hl.trans (ellLoop_fail hcA hca hte hc0 hu)⟩)⟩
          exact hK3.frame (F4.2.1 _ (by omega)) (F4.2.1 _ (by omega)) (fun k => F4.2.2.1 _ _ (fun h => h))
        | some r =>
          obtain ⟨A', a'⟩ := r
          rw [hu] at u3
          obtain ⟨u13, uA, ua⟩ := u3
          obtain ⟨cA', ca'⟩ := ellUpd_caps hu
          refine XV.mono (XV.ifS_f hL (by omega) (by omega) (by rw [z3]; exact h0) (by rw [u13]; exact h0)
            (by rw [z3, u13]; exact lt_irrefl 0) (XV.nadd hL (i := n0 + 6) (a := n0 + 6) (b := n0 + 4) (by omega)
            (by omega) (by omega) (by rw [n63]; omega) (by rw [n43]; exact hsa))) (by omega) fun σ4 e4 => ?_
          subst e4
          unfold LoopInv
          refine ⟨by simp [D3], G3.setNat (Or.inl (by omega)) _, by simp [n63, n43]; omega,
            by simp [n73], Or.inl ⟨by simp [s83], by simp [n73], by simp [n63, n43], ⟨A', a', kept'⟩,
              ⟨fun i k => by simp [uA], fun k => by simp [ua], ?_, cA', ca', bK1⟩, ?_⟩⟩
          · exact hK3.frame (by simp) (by simp) (fun k => by simp)
          · rw [hl, ellLoop_next hcA hca hte hc0 hu, show N - (t + 1) = k by omega]
  -- the loop
  have hb : ∀ t σ', LoopInv B I P u a0 n0 F N capA capa SR NR AR st σ t σ' →
      σ'.nat (n0 + 6) < 2 ^ ℓa ∧ σ'.nat (n0 + 7) < 2 ^ ℓa := fun t σ' h => by
    obtain ⟨-, -, i6, i7, -⟩ := h
    omega
  have hlt : ∀ t σ', LoopInv B I P u a0 n0 F N capA capa SR NR AR st σ t σ' →
      σ'.nat (n0 + 6) < σ'.nat (n0 + 7) → t < N := fun t σ' h hl => by
    obtain ⟨-, -, -, -, hc⟩ := h
    rcases hc with ⟨-, n7, n6, -⟩ | ⟨-, n7, -⟩ | ⟨-, n7, -⟩ <;> omega
  refine XV.mono (Q := fun σ' => ∃ t', LoopInv B I P u a0 n0 F N capA capa SR NR AR st σ t' σ' ∧
      ¬ σ'.nat (n0 + 6) < σ'.nat (n0 + 7)) (XV.seq (K₂ := 1 + ((N - 0) * (ellKb d I.m Kr E + 2) + 2))
    (XV.nconst hL (X := X) (i := n0 + 6) (by omega) 0 (by positivity)) fun σa ea => ?_)
    (by simp only [Nat.sub_zero]; omega) ?_
  · subst ea
    have za : (σ.setNat (n0 + 6) 0).sc u = 0 := by simp [z]
    refine XV.seq (XV.sop2 hL (x := P + 8) (a := u) (b := u) (by omega) (by omega) (by omega) .add
      (by intro h; cases h) (by rw [za]; exact h0) (by rw [za]; exact h0)
      (by simp only [RealRAM.Op2.eval, za, add_zero]; exact h0)) fun σb eb => ?_
    subst eb
    refine XV.whileN hL (by omega) (by omega) (LoopInv B I P u a0 n0 F N capA capa SR NR AR st σ) N
      (ellKb d I.m Kr E) hb hlt hbody 0 _ ?_
    unfold LoopInv
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

end AdversarialBco.Bit.Transfer
