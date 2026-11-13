/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XEllUpd
public import AdversarialBco.Bit.Transfer.XEllLem

@[expose] public section

/-!
# The tests of one iteration of ELL-R and BIS-R on the machine

`xtest` computes `ellTest I s a kept` (Bit/RoutQ.lean) for the point `a` in the array `a0 + 1`: (T1) the ball, (T2)
the rows, supplied one by one by the row command of the block (`RowProv`), (T3) the quadratic constraint, (T4) the
gradient of the objective and the kept point. The cut goes into the array `a0 + 2`, the outcome into the slot `P`
(`1` for a returned point, `0` for a cut), the kept point into the slots `P + 1` (flag), `P + 2` (value) and the array
`kb`.

Slots: `P + 3, ..., P + 6` hold `2^s, 2^{s+1}, 2^{2s}, 2^{2s+1}`, `P + 7` is the found flag of (T2); `u, u + 1` hold
`0, 1`; the slots from `u + 13` are scratch. Registers: the row index `B.rE`, `n0, ..., n0 + 3`, `one` (holding `1`),
`nm` (the bound of the row loop).
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## The program -/

/-- (T1): `u + 14 = 2^{2s} R_n²`, `u + 15 = (a·a) R_d²`. -/
def xtestA (L : Layout) (B : EllBlk) (P u a0 n0 one : ℕ) : XCmd :=
  .seq (xdot L u (u + 13) (u + 24) (a0 + 1) (a0 + 1) (n0 + 1) (n0 + 2) B.rd one)
  (.seq ((IE.op .mul (ieMul (P + 5) B.sRn) (.sc B.sRn)).code L u (u + 14) (u + 24))
  ((IE.op .mul (ieMul (u + 13) B.sRd) (.sc B.sRd)).code L u (u + 15) (u + 24)))

/-- Copy the array `src` (cells `0, ..., d - 1`) into the array `dst`. -/
def xcopy (L : Layout) (B : EllBlk) (u src dst n0 one : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst (n0 + 1) 0)))
    (xmapE L u (u + 24) (.arr src (n0 + 2)) dst (n0 + 1) one (n0 + 2) B.rd one)

/-- `x := y + 0`. -/
def xset (L : Layout) (x y z : ℕ) : XCmd := toX (VL.sop2 L .add x y z)

/-- One turn of the row loop (T2): row `i` by the row command, `u + 13 = α_i·a`, `u + 14 = 2^s β_i`; on a violated
row, copy `α_i` into the cut, set the found flag and end the loop; else next row. -/
def xrowBody (L : Layout) (B : EllBlk) (rowc : XCmd) (P u a0 n0 one nm : ℕ) : XCmd :=
  .seq rowc
  (.seq (xdot L u (u + 13) (u + 24) (B.aW + 1) (a0 + 1) (n0 + 1) (n0 + 2) B.rd one)
  (.seq ((ieMul (P + 3) (B.o + 2)).code L u (u + 14) (u + 24))
  (xifS L (u + 14) (u + 13)
    (.seq (xcopy L B u (B.aW + 1) (a0 + 2) n0 one) (.seq (xset L (P + 7) (u + 1) u) (.prim (.frag (.nconst nm 0)))))
    (.prim (.frag (.nadd B.rE B.rE one))))))

/-- (T2): the found flag to `0`, `nm := m`, the row index to `0`, the loop. -/
def xrows (L : Layout) (B : EllBlk) (rowc : XCmd) (P u a0 n0 one nm : ℕ) : XCmd :=
  .seq (xset L (P + 7) u u)
  (.seq (.prim (.frag (.nconst nm 0)))
  (.seq (.prim (.frag (.nadd nm nm B.rm)))
  (.seq (.prim (.frag (.nconst B.rE 0)))
  (.whileN B.rE nm (xrowBody L B rowc P u a0 n0 one nm)))))

/-- (T3): `v = H a` (array `a0 + 3`), `u + 13 = a·v`, `u + 14 = g·a`, `u + 15 = 2^{2s+1} ℓ`,
`u + 16 = a·v - 2^{s+1} g·a`. -/
def xtestQ (L : Layout) (B : EllBlk) (P u a0 n0 one : ℕ) : XCmd :=
  .seq (xmatvec L u (u + 13) (u + 24) B.aH (a0 + 1) (a0 + 3) n0 (n0 + 1) (n0 + 2) B.rd one)
  (.seq (xdot L u (u + 13) (u + 24) (a0 + 1) (a0 + 3) (n0 + 1) (n0 + 2) B.rd one)
  (.seq (xdot L u (u + 14) (u + 24) B.ag (a0 + 1) (n0 + 1) (n0 + 2) B.rd one)
  (.seq ((ieMul (P + 6) B.sl).code L u (u + 15) (u + 24))
  ((IE.op .sub (.sc (u + 13)) (ieMul (P + 4) (u + 14))).code L u (u + 16) (u + 24)))))

/-- The cut of (T3): `c_k = v_k - 2^s g_k`. -/
def xcutQ (L : Layout) (B : EllBlk) (P u a0 n0 one : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst (n0 + 1) 0)))
    (xmapE L u (u + 24) (.op .sub (.arr (a0 + 3) (n0 + 2)) (.op .mul (.sc (P + 3)) (.arr B.ag (n0 + 2))))
      (a0 + 2) (n0 + 1) one (n0 + 2) B.rd one)

/-- (T4): `w = P a` (array `a0 + 3`), the gradient `c_k = D_f w_k - 2^s f_k`, `u + 13 = a·w`, `u + 14 = f·a`,
`u + 15 = V = D_f a·w - 2^{s+1} f·a`. -/
def xtestV (L : Layout) (B : EllBlk) (P u a0 n0 one : ℕ) : XCmd :=
  .seq (xmatvec L u (u + 13) (u + 24) B.aP (a0 + 1) (a0 + 3) n0 (n0 + 1) (n0 + 2) B.rd one)
  (.seq (.prim (.frag (.nconst (n0 + 1) 0)))
  (.seq (xmapE L u (u + 24) (.op .sub (.op .mul (.sc B.sDf) (.arr (a0 + 3) (n0 + 2)))
      (.op .mul (.sc (P + 3)) (.arr B.af (n0 + 2)))) (a0 + 2) (n0 + 1) one (n0 + 2) B.rd one)
  (.seq (xdot L u (u + 13) (u + 24) (a0 + 1) (a0 + 3) (n0 + 1) (n0 + 2) B.rd one)
  (.seq (xdot L u (u + 14) (u + 24) B.af (a0 + 1) (n0 + 1) (n0 + 2) B.rd one)
  ((IE.op .sub (ieMul B.sDf (u + 13)) (ieMul (P + 4) (u + 14))).code L u (u + 15) (u + 24))))))

/-- The new kept point: `a` with the value `V` (slot `u + 15`). -/
def xkeepNew (L : Layout) (B : EllBlk) (P u a0 kb n0 one : ℕ) : XCmd :=
  .seq (xcopy L B u (a0 + 1) kb n0 one) (.seq (xset L (P + 2) (u + 15) u) (xset L (P + 1) (u + 1) u))

/-- The kept point: replaced when there is none or when `V` is smaller. -/
def xkeep (L : Layout) (B : EllBlk) (P u a0 kb n0 one : ℕ) : XCmd :=
  xifS L u (P + 1) (xifS L (u + 15) (P + 2) (xkeepNew L B P u a0 kb n0 one) .skip)
    (xkeepNew L B P u a0 kb n0 one)

/-- The end of (T4): `u + 16 = 1` iff the gradient has a nonzero entry; the outcome `0` (cut) or `1` (return). -/
def xtestEnd (L : Layout) (B : EllBlk) (P u a0 n0 one : ℕ) : XCmd :=
  .seq (xset L (u + 16) u u)
  (.seq (.seq (.prim (.frag (.nconst (n0 + 1) 0))) (xanyE L u (u + 16) (u + 1) (u + 24) (.sc u)
      (.op .mul (.arr (a0 + 2) (n0 + 2)) (.arr (a0 + 2) (n0 + 2))) (n0 + 1) one (n0 + 2) B.rd one))
  (xifS L u (u + 16) (xset L P u u) (xset L P (u + 1) u)))

/-- The tests of one iteration. -/
def xtest (L : Layout) (B : EllBlk) (rowc : XCmd) (P u a0 kb n0 one nm : ℕ) : XCmd :=
  .seq (xtestA L B P u a0 n0 one)
  (xifS L (u + 14) (u + 15) (.seq (xcopy L B u (a0 + 1) (a0 + 2) n0 one) (xset L P u u))
  (.seq (xrows L B rowc P u a0 n0 one nm)
  (xifS L u (P + 7) (xset L P u u)
  (.seq (xtestQ L B P u a0 n0 one)
  (xifS L (u + 15) (u + 16) (.seq (xcutQ L B P u a0 n0 one) (xset L P u u))
  (.seq (xtestV L B P u a0 n0 one)
  (.seq (xkeep L B P u a0 kb n0 one) (xtestEnd L B P u a0 n0 one))))))))

/-! ## The outputs -/

/-- The kept point in the slots `P + 1` (flag), `P + 2` (value) and the array `kb`. -/
def KeptIn (P kb : ℕ) : Option ((Fin d → ℤ) × ℤ) → Env d → Prop
  | none, σ => σ.sc (P + 1) = 0
  | some (b, W), σ => σ.sc (P + 1) = 1 ∧ (∀ k : Fin d, σ.arr kb k = b k) ∧ σ.sc (P + 2) = W

/-- The outcome of the tests: `1` in the slot `P` for a returned point; `0` for a cut, the cut in the array `a0 + 2`
and the kept point. -/
def TestOut (P a0 kb : ℕ) : Cut d → Env d → Prop
  | .ret _, σ => σ.sc P = 1
  | .cut c kept, σ => σ.sc P = 0 ∧ (∀ k : Fin d, σ.arr (a0 + 2) k = c k) ∧ KeptIn P kb kept σ

/-! ## The layout and the fixed data -/

/-- The cells of the tests above the bases of the block: the slots `P, ..., P + 7` below `u`, the slots from `u` up to
`u + 59`, the arrays `a0, ..., a0 + 6`, the registers `n0, ..., n0 + 5`. -/
structure TestLay (L : Layout) (B : EllBlk) (P u a0 kb n0 one nm : ℕ) : Prop where
  oP : B.o + 3 ≤ P
  Pu : P + 8 ≤ u
  uS : u + 60 ≤ L.NS
  wa : B.aW + 2 ≤ a0
  kb : kb = a0 + 6
  aA : a0 + 7 ≤ L.NA
  rn : B.rE + 1 ≤ n0
  one : one = n0 + 4
  nm : nm = n0 + 5
  nN : n0 + 6 ≤ L.NN

/-- The fixed data of the tests: the problem (`EllIn`), `0, 1` in `u, u + 1`, `1` in the register `one`, the scales
`2^s, 2^{s+1}, 2^{2s}, 2^{2s+1}` in `P + 3, ..., P + 6`. -/
def TestEnv (B : EllBlk) (I : EllI d) (s P u one : ℕ) (σ : Env d) : Prop :=
  EllIn B I σ ∧ σ.sc u = 0 ∧ σ.sc (u + 1) = 1 ∧ σ.nat one = 1 ∧
  σ.sc (P + 3) = ((2 ^ s : ℤ) : ℝ) ∧ σ.sc (P + 4) = ((2 ^ (s + 1) : ℤ) : ℝ) ∧
  σ.sc (P + 5) = ((2 ^ (2 * s) : ℤ) : ℝ) ∧ σ.sc (P + 6) = ((2 ^ (2 * s + 1) : ℤ) : ℝ)

/-- The fixed data survive a change that avoids them: slots above `B.o` other than `u, u + 1, P + 3, ..., P + 6` or
the row command's own; registers above `B.rE` other than `one`, or the row command's own; arrays above `B.aW` or the
row command's own. -/
theorem TestEnv.frame {B : EllBlk} {I : EllI d} {s P u one : ℕ} {L : Layout} {nS nN nA : ℕ}
    {SR NR AR S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop} {σ σ' : Env d}
    (hB : B.OK L nS nN nA) (hav : B.Avoid SR NR AR) (hsr : ∀ y, SR y → y < B.o) (hnr : ∀ j, NR j → j < B.rE)
    (har : ∀ b, AR b → b < B.aW) (hu : B.o ≤ u) (hP : B.o ≤ P) (hone : B.rE ≤ one)
    (hT : TestEnv B I s P u one σ) (hF : FrameA S N Ar σ σ')
    (hS : ∀ y, S y → (B.o ≤ y ∧ y ≠ u ∧ y ≠ u + 1 ∧ (y < P + 3 ∨ P + 6 < y)) ∨ SR y)
    (hN : ∀ j, N j → (B.rE ≤ j ∧ j ≠ one) ∨ NR j) (hA : ∀ b k, Ar b k → B.aW ≤ b ∨ AR b) :
    TestEnv B I s P u one σ' := by
  obtain ⟨-, -, -, hrd, hrm, hsl, hsDf, hsRn, hsRd, hsrn, hsrd, hsen, hsed, haH, hag, haP, haf⟩ := hB
  obtain ⟨nrd, nrm, nsl, nsDf, nsRn, nsRd, nsrn, nsrd, nsen, nsed, naH, nag, naP, naf⟩ := hav
  obtain ⟨⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14⟩, z, o, n1, p3, p4, p5, p6⟩ := hT
  have nS1 : ∀ y, y < B.o → ¬ SR y → ¬ S y := fun y hy hr h => by
    rcases hS y h with h' | h'
    · omega
    · exact hr h'
  have nS2 : ∀ y, B.o ≤ y → (y = u ∨ y = u + 1 ∨ (P + 3 ≤ y ∧ y ≤ P + 6)) → ¬ S y := fun y hy hy' h => by
    rcases hS y h with h' | h'
    · omega
    · exact absurd (hsr y h') (by omega)
  have nN1 : ∀ j, j < B.rE → ¬ NR j → ¬ N j := fun j hj hr h => by
    rcases hN j h with h' | h'
    · omega
    · exact hr h'
  have nN2 : ¬ N one := fun h => by
    rcases hN one h with h' | h'
    · omega
    · exact absurd (hnr one h') (by omega)
  have nA1 : ∀ b k, b < B.aW → ¬ AR b → ¬ Ar b k := fun b k hb hr h => by
    rcases hA b k h with h' | h'
    · omega
    · exact hr h'
  refine ⟨⟨by rw [hF.1 _ (nN1 _ hrd nrd), e1], by rw [hF.1 _ (nN1 _ hrm nrm), e2],
    by rw [hF.2.1 _ (nS1 _ hsl nsl), e3], by rw [hF.2.1 _ (nS1 _ hsDf nsDf), e4],
    by rw [hF.2.1 _ (nS1 _ hsRn nsRn), e5], by rw [hF.2.1 _ (nS1 _ hsRd nsRd), e6],
    by rw [hF.2.1 _ (nS1 _ hsrn nsrn), e7], by rw [hF.2.1 _ (nS1 _ hsrd nsrd), e8],
    by rw [hF.2.1 _ (nS1 _ hsen nsen), e9], by rw [hF.2.1 _ (nS1 _ hsed nsed), e10],
    fun i j => by rw [hF.2.2.1 _ _ (nA1 _ _ haH naH), e11], fun j => by rw [hF.2.2.1 _ _ (nA1 _ _ hag nag), e12],
    fun i j => by rw [hF.2.2.1 _ _ (nA1 _ _ haP naP), e13], fun j => by rw [hF.2.2.1 _ _ (nA1 _ _ haf naf), e14]⟩,
    by rw [hF.2.1 _ (nS2 _ hu (Or.inl rfl)), z], by rw [hF.2.1 _ (nS2 _ (by omega) (Or.inr (Or.inl rfl))), o],
    by rw [hF.1 _ nN2, n1], by rw [hF.2.1 _ (nS2 _ (by omega) (Or.inr (Or.inr ⟨le_rfl, by omega⟩))), p3],
    by rw [hF.2.1 _ (nS2 _ (by omega) (Or.inr (Or.inr ⟨by omega, by omega⟩))), p4],
    by rw [hF.2.1 _ (nS2 _ (by omega) (Or.inr (Or.inr ⟨by omega, by omega⟩))), p5],
    by rw [hF.2.1 _ (nS2 _ (by omega) (Or.inr (Or.inr ⟨by omega, le_rfl⟩))), p6]⟩

/-- The same, for a change of the tests' own cells only. -/
theorem TestEnv.frame_own {B : EllBlk} {I : EllI d} {s P u one : ℕ} {L : Layout} {nS nN nA : ℕ}
    {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop} {σ σ' : Env d}
    (hB : B.OK L nS nN nA) (hu : B.o ≤ u) (hP : B.o ≤ P) (hone : B.rE ≤ one)
    (hT : TestEnv B I s P u one σ) (hF : FrameA S N Ar σ σ')
    (hS : ∀ y, S y → B.o ≤ y ∧ y ≠ u ∧ y ≠ u + 1 ∧ (y < P + 3 ∨ P + 6 < y))
    (hN : ∀ j, N j → B.rE ≤ j ∧ j ≠ one) (hA : ∀ b k, Ar b k → B.aW ≤ b) :
    TestEnv B I s P u one σ' :=
  TestEnv.frame (SR := fun _ => False) (NR := fun _ => False) (AR := fun _ => False) hB
    ⟨id, id, id, id, id, id, id, id, id, id, id, id, id, id⟩ (fun _ h => h.elim) (fun _ h => h.elim)
    (fun _ h => h.elim) hu hP hone hT hF (fun y h => Or.inl (hS y h)) (fun j h => Or.inl (hN j h))
    (fun b k h => Or.inl (hA b k h))

/-! ## Bounds on the problem -/

theorem abs_le_sz {I : EllI d} {x : ℤ} (h : x.natAbs ≤ ellMx I) : |x| ≤ 2 ^ ellSz I := by
  have := Nat.lt_size_self (ellMx I)
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h.trans this.le

theorem abs_le_sz' {I : EllI d} {x : ℕ} (h : x ≤ ellMx I) : |(x : ℤ)| ≤ 2 ^ ellSz I :=
  abs_le_sz (x := (x : ℤ)) (by simpa using h)

/-! ## Copy -/

set_option maxHeartbeats 2000000 in
/-- The rule of `xcopy`: the cells `0, ..., d - 1` of `src` into `dst`. -/
theorem XV.copy {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk}
    {u src dst n0 one E : ℕ} {x : Fin d → ℤ} (hu : u + 27 ≤ L.NS) (hsrc : src < L.NA) (hdst : dst < L.NA)
    (hsd : src ≠ dst) (hn0 : n0 + 3 ≤ L.NN) (hrd : B.rd < L.NN) (hone : one < L.NN)
    (hrd0 : B.rd < n0 + 1 ∨ n0 + 3 ≤ B.rd) (hone0 : one < n0 + 1 ∨ n0 + 3 ≤ one) (hro : B.rd ≠ one)
    (hz : σ.sc u = 0) (hσd : σ.nat B.rd = d) (hσ1 : σ.nat one = 1)
    (hx : ∀ k : Fin d, σ.arr src k = x k) (bx : ∀ k, |x k| ≤ 2 ^ E) (hE : E < ℓ) :
    XRunsB L X ℓa ℓ (xcopy L B u src dst n0 one) σ (1 + (d * (2 + 6) + 3)) (fun σ' =>
      (∀ k : Fin d, σ'.arr dst k = x k) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => u + 24 ≤ y) (fun j => j = n0 + 1 ∨ j = n0 + 2) (fun b c => b = dst ∧ c < d) σ σ') := by
  have hda := asz_lt hL hdst
  have hdl : d < 2 ^ ℓa := by unfold asz at hda; nlinarith
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  have hcd : ∀ k < d, 0 + 1 * k < asz d := fun k hk => by unfold asz; nlinarith
  refine XV.seq (XV.nconst hL (i := n0 + 1) (by omega) 0 (by positivity)) fun σ0 e0 => ?_
  subst e0
  refine XV.mono (XV.mapE (E := E) (N := d) (base := 0) (st := 1) (F := vext x) hL (z := u) (t := u + 24)
    (e := .arr src (n0 + 2)) (aB := dst) (nr := n0 + 1) (nst := one) (nk := n0 + 2) (nn := B.rd) (none := one)
    (by simp only [IE.WF]; omega) (by omega) (by simp only [IE.scr]; omega) (by simpa using hz) hdst (by omega)
    hone (by omega) hrd hone (nodup4 (by omega) (by omega) (by omega) (by omega) (by omega) hro) (by omega)
    (by omega) (by simp; rw [if_neg (by omega), hσd]) (by simp; rw [if_neg (by omega), hσ1]) (by simp)
    (by simp; rw [if_neg (by omega), hσ1]) one_pos hcd hdl (by simpa using hdl) hsa (by simp only [IE.top]; omega)
    ?_) le_rfl fun σ1 ⟨m1, r1, d1, F1⟩ => ?_
  · intro k hk σ' hF hd hkt hkr
    have e : σ'.arr src k = vext x k := by
      rw [hF.2.2.1 _ _ (fun h => hsd h.1), Env.setNat_arr, vext_lt _ hk]; exact hx ⟨k, hk⟩
    exact ⟨⟨by rw [hkt]; simpa using hcd k hk, vext x k, by rw [hkt, e], abs_vext_le bx (by positivity) k⟩,
      by simp only [IE.eval, hkt, e]⟩
  · refine ⟨fun k => ?_, by rw [d1]; simp, ?_⟩
    · have := m1 k k.2
      simp only [zero_add, one_mul] at this
      rw [this, vext_lt _ k.2]
    · exact ((FrameA.refl _ _ _ σ).setNat (Or.inl rfl) 0).trans
        (F1.mono (fun _ h => h) (fun j h => by omega) (fun b c h => ⟨h.1, by simpa using h.2.2⟩))

/-! ## (T1) -/

set_option maxHeartbeats 4000000 in
/-- (T1) on the machine: `u + 13 = a·a`, `u + 14 = 2^{2s} R_n²`, `u + 15 = (a·a) R_d²`. -/
theorem XV.testA {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk} {I : EllI d}
    {nS nN nA s P u a0 kb n0 one nm F : ℕ} {a : Fin d → ℤ} (hB : B.OK L nS nN nA)
    (lay : TestLay L B P u a0 kb n0 one nm) (hT : TestEnv B I s P u one σ)
    (ha : ∀ k : Fin d, σ.arr (a0 + 1) k = a k) (ba : ∀ k, |a k| ≤ 2 ^ F) (hσF : ellSz I ≤ F)
    (hsF : 2 * s + 1 ≤ F) (hdF : d ≤ F) (hℓ : 64 * F + 16 < ℓ) :
    XRunsB L X ℓa ℓ (xtestA L B P u a0 n0 one) σ (d * 10 + 5 + (5 + 5)) (fun σ' =>
      σ'.sc (u + 13) = ((a ⬝ᵥ a : ℤ) : ℝ) ∧ σ'.sc (u + 14) = ((2 ^ (2 * s) * I.R.num ^ 2 : ℤ) : ℝ) ∧
      σ'.sc (u + 15) = (((a ⬝ᵥ a) * (I.R.den : ℤ) ^ 2 : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => u + 13 ≤ y) (fun j => j = n0 + 1 ∨ j = n0 + 2) (fun _ _ => False) σ σ') := by
  obtain ⟨-, -, -, hrd, -, -, -, hsRn, hsRd, -, -, -, -, -, -, -, -⟩ := hB
  obtain ⟨oP, Pu, uS, wa, -, aA, rn, onee, -, nN⟩ := lay
  subst onee
  obtain ⟨⟨e1, -, -, -, e5, e6, -, -, -, -, -, -, -, -⟩, z, -, n1, -, -, p5, -⟩ := hT
  obtain ⟨-, -, -, -, -, -, -, -, mRn, mRd, -, -, -, -⟩ := ellMx_le I
  have hpF : ∀ k, k ≤ F → (2 : ℤ) ^ k ≤ 2 ^ F := fun k hk => pow_le_pow_right₀ (by norm_num) hk
  have bRn : |I.R.num| ≤ 2 ^ F := (abs_le_sz mRn).trans (hpF _ hσF)
  have bRd : |(I.R.den : ℤ)| ≤ 2 ^ F := (abs_le_sz' mRd).trans (hpF _ hσF)
  have b2s : |(2 : ℤ) ^ (2 * s)| ≤ 2 ^ F := by rw [abs_of_pos (by positivity)]; exact hpF _ (by omega)
  have baa : |a ⬝ᵥ a| ≤ 2 ^ (3 * F) := abs_le_pow_mono (abs_dot_le' hdF ba ba) (by omega)
  -- `a·a`
  refine XV.seq (XV.dot (E := F) (x := a) (y := a) hL (z := u) (r := u + 13) (t := u + 24) (nr := n0 + 1)
    (nk := n0 + 2) (nd := B.rd) (none := n0 + 4) (by omega) (by omega) (by omega) (by omega) z (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (nodup4 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)) e1 n1 ha ha ba ba (by omega) (d_mul_pow_lt hdF (by omega))) fun σ1 ⟨s1, d1, F1⟩ => ?_
  have c1 : ∀ y, y < u + 13 → σ1.sc y = σ.sc y := fun y hy => F1.2.1 y (by omega)
  -- `2^{2s} R_n²`
  have L2 : (IE.op .mul (ieMul (P + 5) B.sRn) (.sc B.sRn)).Leaves F σ1 := by
    simp only [ieMul, IE.Leaves]
    exact ⟨⟨⟨_, by rw [c1 _ (by omega), p5], b2s⟩, ⟨_, by rw [c1 _ (by omega), e5], bRn⟩⟩,
      ⟨_, by rw [c1 _ (by omega), e5], bRn⟩⟩
  refine XV.seq (XV.ieRun (E := F) (e := IE.op .mul (ieMul (P + 5) B.sRn) (.sc B.sRn))
    (v := 2 ^ (2 * s) * I.R.num ^ 2) hL (x := u + 14) (t := u + 24) (z := u)
    (by simp only [ieMul, IE.WF]; exact ⟨(by intro h; cases h), ⟨(by intro h; cases h), by omega, by omega⟩,
      by omega⟩) (by omega) (by omega) (by simp only [ieMul, IE.scr]; omega) (by rw [c1 _ (by omega), z]) L2
    (by simp only [ieMul, IE.top, IE.mag]; omega)
    (by simp only [ieMul, IE.eval, RealRAM.Op2.eval, c1 (P + 5) (by omega),
      c1 B.sRn (by omega), p5, e5]; push_cast; ring)) fun σ2 ⟨x2, _, d2, P2⟩ => ?_
  have c2 : ∀ y, y < u + 14 → σ2.sc y = σ1.sc y := fun y hy => P2.2.1 y (by omega)
  -- `(a·a) R_d²`
  have L3 : (IE.op .mul (ieMul (u + 13) B.sRd) (.sc B.sRd)).Leaves (3 * F) σ2 := by
    simp only [ieMul, IE.Leaves]
    have bRd' := abs_le_pow_mono bRd (show F ≤ 3 * F by omega)
    have r6 : σ2.sc B.sRd = ((I.R.den : ℤ) : ℝ) := by rw [c2 _ (by omega), c1 _ (by omega), e6]; norm_cast
    exact ⟨⟨⟨_, by rw [c2 _ (by omega), s1], baa⟩, ⟨_, r6, bRd'⟩⟩, ⟨_, r6, bRd'⟩⟩
  refine XV.mono (XV.ieRun (E := 3 * F) (e := IE.op .mul (ieMul (u + 13) B.sRd) (.sc B.sRd))
    (v := (a ⬝ᵥ a) * (I.R.den : ℤ) ^ 2) hL (x := u + 15) (t := u + 24) (z := u)
    (by simp only [ieMul, IE.WF]; exact ⟨(by intro h; cases h), ⟨(by intro h; cases h), by omega, by omega⟩,
      by omega⟩) (by omega) (by omega) (by simp only [ieMul, IE.scr]; omega)
    (by rw [c2 _ (by omega), c1 _ (by omega), z]) L3 (by simp only [ieMul, IE.top, IE.mag]; omega)
    (by simp only [ieMul, IE.eval, RealRAM.Op2.eval, c2 (u + 13) (by omega),
      c2 B.sRd (by omega), c1 B.sRd (by omega), s1, e6]; push_cast; ring))
    le_rfl fun σ3 ⟨x3, _, d3, P3⟩ => ?_
  refine ⟨by rw [P3.2.1 _ (by omega), P2.2.1 _ (by omega), s1], by rw [P3.2.1 _ (by omega), x2], x3,
    by rw [d3, d2, d1], ?_⟩
  have G1 : FrameA (fun y => u + 13 ≤ y) (fun j => j = n0 + 1 ∨ j = n0 + 2) (fun _ _ => False) σ σ1 :=
    F1.mono (fun y h => by rcases h with h | h <;> omega) (fun j h => by rcases h with h | h <;> omega) (fun _ _ h => h)
  have G2 : FrameA (fun y => u + 13 ≤ y) (fun j => j = n0 + 1 ∨ j = n0 + 2) (fun _ _ => False) σ1 σ2 :=
    FrameA.ofP (P2.mono (fun y h => by rcases h with h | h <;> omega) (fun _ h => h.elim))
  have G3 : FrameA (fun y => u + 13 ≤ y) (fun j => j = n0 + 1 ∨ j = n0 + 2) (fun _ _ => False) σ2 σ3 :=
    FrameA.ofP (P3.mono (fun y h => by rcases h with h | h <;> omega) (fun _ h => h.elim))
  exact (G1.trans G2).trans G3

/-! ## (T2), the rows -/

theorem absR_lt {x : ℤ} {a ℓ : ℕ} (h : |x| ≤ 2 ^ a) (ha : a < ℓ) : |((x : ℤ) : ℝ)| < 2 ^ ℓ := by
  have h' : |x| < 2 ^ ℓ := h.trans_lt (pow_lt_pow_right₀ (by norm_num) ha)
  exact_mod_cast h'

theorem abs_pow_le {a F : ℕ} (h : a ≤ F) : |(2 : ℤ) ^ a| ≤ 2 ^ F := by
  rw [abs_of_pos (by positivity)]; exact pow_le_pow_right₀ (by norm_num) h

theorem ellAl_le {I : EllI d} {F : ℕ} (hσF : ellSz I ≤ F) (i : Fin I.m) (k : Fin d) : |I.α i k| ≤ 2 ^ F :=
  (abs_le_sz ((ellMx_le I).1 i k)).trans (pow_le_pow_right₀ (by norm_num) hσF)

theorem ellBe_le {I : EllI d} {F : ℕ} (hσF : ellSz I ≤ F) (i : Fin I.m) : |I.β i| ≤ 2 ^ F :=
  (abs_le_sz ((ellMx_le I).2.1 i)).trans (pow_le_pow_right₀ (by norm_num) hσF)

theorem find_finRange_none {m : ℕ} (p : Fin m → Bool) (h : ∀ j, p j = false) :
    (List.finRange m).find? p = none := by
  rw [List.find?_eq_none]; intro j _; simp [h j]

/-- The outcome of (T2) at the point `a`: the first violated row `i` gives the flag `1` in `P + 7` and `α_i` in the
array `a0 + 2`; no violated row, the flag `0`. -/
def RowsOut (I : EllI d) (s : ℕ) (a : Fin d → ℤ) (P a0 : ℕ) (σ : Env d) : Prop :=
  match (List.finRange I.m).find? (fun i => decide (2 ^ s * I.β i < I.α i ⬝ᵥ a)) with
  | some i => σ.sc (P + 7) = 1 ∧ ∀ k : Fin d, σ.arr (a0 + 2) k = I.α i k
  | none => σ.sc (P + 7) = 0

set_option maxHeartbeats 8000000 in
/-- (T2) on the machine: the rows one by one from the row command, up to the first violated one. -/
theorem XV.rows {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk} {I : EllI d}
    {nS nN nA s P u a0 kb n0 one nm F Kr : ℕ} {rowc : XCmd} {Ctx : Env d → Prop} {SR NR AR : ℕ → Prop}
    {a : Fin d → ℤ} (hB : B.OK L nS nN nA) (hav : B.Avoid SR NR AR)
    (hrow : RowProv L X ℓa ℓ I B rowc Ctx SR NR AR Kr) (hctx : CtxOK B Ctx SR NR AR)
    (lay : TestLay L B P u a0 kb n0 one nm) (hT : TestEnv B I s P u one σ) (hC : Ctx σ)
    (ha : ∀ k : Fin d, σ.arr (a0 + 1) k = a k) (ba : ∀ k, |a k| ≤ 2 ^ F) (hσF : ellSz I ≤ F) (hsF : s ≤ F)
    (hdF : d ≤ F) (hm : I.m < 2 ^ ℓa) (hℓ : 64 * F + 16 < ℓ) :
    XRunsB L X ℓa ℓ (xrows L B rowc P u a0 n0 one nm) σ (4 + (I.m * (Kr + d * 20 + 20) + 2)) (fun σ' =>
      RowsOut I s a P a0 σ' ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = P + 7 ∨ u + 13 ≤ y ∨ y = B.o + 2 ∨ SR y)
        (fun j => j = B.rE ∨ j = n0 + 1 ∨ j = n0 + 2 ∨ j = n0 + 5 ∨ NR j)
        (fun b _ => b = B.aW + 1 ∨ b = a0 + 2 ∨ AR b) σ σ') := by
  have hB' := hB
  obtain ⟨hS0, hN0, hA0, hrd, hrm, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hB'
  obtain ⟨hsr, hnr, har, hrun⟩ := hrow
  obtain ⟨oP, Pu, uS, wa, -, aA, rn, onee, nme, nN⟩ := lay
  subst onee nme
  have hT' := hT
  obtain ⟨⟨hσd, hσm, -, -, -, -, -, -, -, -, -, -, -, -⟩, z0, o1, n1, p3, -, -, -⟩ := hT'
  have hℓ0 : 0 < ℓ := by omega
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by simp only [abs_zero]; positivity
  have h1 : |(1 : ℝ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  have hda := asz_lt hL (show a0 + 1 < L.NA by omega)
  have hdl : d < 2 ^ ℓa := by unfold asz at hda; nlinarith
  -- the frame of the loop
  let Sw : ℕ → Prop := fun y => y = P + 7 ∨ u + 13 ≤ y ∨ y = B.o + 2 ∨ SR y
  let Nw : ℕ → Prop := fun j => j = B.rE ∨ j = n0 + 1 ∨ j = n0 + 2 ∨ j = n0 + 5 ∨ NR j
  let Aw : ℕ → ℕ → Prop := fun b _ => b = B.aW + 1 ∨ b = a0 + 2 ∨ AR b
  have hSw : ∀ y, Sw y → (B.o ≤ y ∧ y ≠ u ∧ y ≠ u + 1 ∧ (y < P + 3 ∨ P + 6 < y)) ∨ SR y := fun y h => by
    rcases h with h | h | h | h
    · left; omega
    · left; omega
    · left; omega
    · right; exact h
  have hNw : ∀ j, Nw j → (B.rE ≤ j ∧ j ≠ n0 + 4) ∨ NR j := fun j h => by
    rcases h with h | h | h | h | h
    · left; omega
    · left; omega
    · left; omega
    · left; omega
    · right; exact h
  have hAw : ∀ b k, Aw b k → B.aW ≤ b ∨ AR b := fun b k h => by
    rcases h with h | h | h
    · left; omega
    · left; omega
    · right; exact h
  have hctx' : ∀ σ', σ'.draws = σ.draws → FrameA Sw Nw Aw σ σ' → Ctx σ' := fun σ' hd hF =>
    hctx σ σ' hC hd (hF.mono (fun y h => by
      rcases h with h | h | h | h
      · left; omega
      · left; omega
      · left; omega
      · right; exact h) (fun j h => by
      rcases h with h | h | h | h | h
      · left; omega
      · left; omega
      · left; omega
      · left; omega
      · right; exact h) (fun b k h => hAw b k h))
  have hTw : ∀ σ', FrameA Sw Nw Aw σ σ' → TestEnv B I s P u (n0 + 4) σ' := fun σ' hF =>
    TestEnv.frame hB hav hsr hnr har (by omega) (by omega) (by omega) hT hF hSw hNw hAw
  have haw : ∀ σ', FrameA Sw Nw Aw σ σ' → ∀ k : Fin d, σ'.arr (a0 + 1) k = a k := fun σ' hF k => by
    rw [hF.2.2.1 _ _ (fun h => by
      rcases h with h | h | h
      · omega
      · omega
      · exact absurd (har _ h) (by omega)), ha]
  -- the invariant
  let p : Fin I.m → Bool := fun i => decide (2 ^ s * I.β i < I.α i ⬝ᵥ a)
  let J : ℕ → Env d → Prop := fun t σ' => σ'.draws = σ.draws ∧ FrameA Sw Nw Aw σ σ' ∧ σ'.nat B.rE ≤ I.m ∧
    ((σ'.sc (P + 7) = 0 ∧ σ'.nat (n0 + 5) = I.m ∧ σ'.nat B.rE = t ∧ ∀ i : Fin I.m, i.1 < t → p i = false) ∨
      (σ'.sc (P + 7) = 1 ∧ σ'.nat (n0 + 5) = 0 ∧ RowsOut I s a P a0 σ'))
  -- the start
  refine XV.mono (K := 1 + (1 + (1 + (1 + ((I.m - 0) * (Kr + d * 20 + 18 + 2) + 2)))))
    (XV.seq (XV.sop2 hL (x := P + 7) (a := u) (b := u) (by omega) (by omega) (by omega) .add
    (by intro h; cases h) (by rw [z0]; exact h0) (by rw [z0]; exact h0)
    (by simp only [RealRAM.Op2.eval, z0, add_zero]; exact h0)) fun σ1 e1 => ?_) (le_of_eq (by rw [Nat.sub_zero]; ring))
    fun _ h => h
  subst e1
  refine XV.seq (XV.nconst hL (i := n0 + 5) (by omega) 0 (by positivity)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.nadd hL (i := n0 + 5) (a := n0 + 5) (b := B.rm) (by omega) (by omega) (by omega)
    (by simp) (by simp; rw [if_neg (by omega), hσm]; exact hm)) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.nconst hL (i := B.rE) (by omega) 0 (by positivity)) fun σ4 e4 => ?_
  subst e4
  set σ4 := ((((σ.setSc (P + 7) (RealRAM.Op2.eval .add (σ.sc u) (σ.sc u))).setNat (n0 + 5) 0).setNat (n0 + 5)
    (((σ.setSc (P + 7) (RealRAM.Op2.eval .add (σ.sc u) (σ.sc u))).setNat (n0 + 5) 0).nat (n0 + 5) +
      ((σ.setSc (P + 7) (RealRAM.Op2.eval .add (σ.sc u) (σ.sc u))).setNat (n0 + 5) 0).nat B.rm)).setNat B.rE 0)
    with hσ4
  have F4 : FrameA Sw Nw Aw σ σ4 :=
    ((((FrameA.refl Sw Nw Aw σ).setSc (Or.inl rfl) _).setNat (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _).setNat
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _).setNat (Or.inl rfl) _
  have J0 : J 0 σ4 := by
    refine ⟨by simp [hσ4], F4, by simp [hσ4], Or.inl ⟨?_, ?_, by simp [hσ4], fun i h => absurd h (by omega)⟩⟩
    · simp [hσ4, RealRAM.Op2.eval, z0]
    · simp [hσ4, hσm, show B.rm ≠ n0 + 5 by omega, show n0 + 5 ≠ B.rE by omega, show B.rE ≠ n0 + 5 by omega]
  -- the loop
  refine XV.mono (XV.whileN hL (i := B.rE) (j := n0 + 5) (by omega) (by omega) J I.m (Kr + d * 20 + 18) ?_ ?_ ?_
    0 σ4 J0) le_rfl fun σ' ⟨t', hJ, hc⟩ => ?_
  · rintro t σ' ⟨-, -, hle, hcase⟩
    rcases hcase with ⟨-, hn, -, -⟩ | ⟨-, hn, -⟩
    · exact ⟨by omega, by rw [hn]; exact hm⟩
    · exact ⟨by omega, by rw [hn]; positivity⟩
  · rintro t σ' ⟨-, -, -, hcase⟩ hlt
    rcases hcase with ⟨-, hn, ht, -⟩ | ⟨-, hn, -⟩
    · omega
    · omega
  · rintro t σt ⟨dt, Ft, -, hcase⟩ hlt
    obtain ⟨q0, qm, qt, qp⟩ : σt.sc (P + 7) = 0 ∧ σt.nat (n0 + 5) = I.m ∧ σt.nat B.rE = t ∧
        ∀ i : Fin I.m, i.1 < t → p i = false := by
      rcases hcase with h | ⟨-, hn, -⟩
      · exact h
      · omega
    have htm : t < I.m := by omega
    have hlt' : σt.nat B.rE < I.m := by omega
    let i : Fin I.m := ⟨t, htm⟩
    have hTt := hTw σt Ft
    obtain ⟨-, z0t, o1t, n1t, p3t, -, -, -⟩ := hTt
    -- the row
    refine XV.mono (K := Kr + ((d * 10 + 5) + (3 + (d * 8 + 7))))
      (XV.seq (hrun σt (hctx' σt dt Ft) hlt') fun σr ⟨hα, hβ, dr, Fr⟩ => ?_) (by omega) fun _ h => h
    have ei : (⟨σt.nat B.rE, hlt'⟩ : Fin I.m) = i := Fin.ext qt
    rw [ei] at hα hβ
    have FR : FrameA Sw Nw Aw σ σr := Ft.trans (Fr.mono (fun y h => by
      rcases h with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))) (fun j h => Or.inr (Or.inr (Or.inr (Or.inr h)))) (fun b k h => by
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)))
    have hTr := hTw σr FR
    obtain ⟨⟨hσdr, -, -, -, -, -, -, -, -, -, -, -, -, -⟩, z0r, o1r, n1r, p3r, -, -, -⟩ := hTr
    -- `u + 13 = α_i·a`
    refine XV.seq (XV.dot (E := F) (x := I.α i) (y := a) hL (z := u) (r := u + 13) (t := u + 24)
      (ax := B.aW + 1) (ay := a0 + 1) (nr := n0 + 1) (nk := n0 + 2) (nd := B.rd) (none := n0 + 4) (by omega)
      (by omega) (by omega) (by omega) z0r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (nodup4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) hσdr n1r hα (haw σr FR)
      (ellAl_le hσF i) ba (by omega) (d_mul_pow_lt hdF (by omega))) fun σ1 ⟨s1, d1, F1⟩ => ?_
    have c1 : ∀ y, y < u + 13 → σ1.sc y = σr.sc y := fun y hy => F1.2.1 y (by omega)
    -- `u + 14 = 2^s β_i`
    have L2 : (ieMul (P + 3) (B.o + 2)).Leaves F σ1 := by
      simp only [ieMul, IE.Leaves]
      exact ⟨⟨_, by rw [c1 _ (by omega), p3r], abs_pow_le hsF⟩, ⟨_, by rw [c1 _ (by omega), hβ], ellBe_le hσF i⟩⟩
    refine XV.seq (XV.ieRun (E := F) (e := ieMul (P + 3) (B.o + 2)) (v := 2 ^ s * I.β i) hL (x := u + 14)
      (t := u + 24) (z := u) (by simp only [ieMul, IE.WF]; exact ⟨(by intro h; cases h), by omega, by omega⟩)
      (by omega) (by omega) (by simp only [ieMul, IE.scr]; omega) (by rw [c1 _ (by omega), z0r]) L2
      (by simp only [ieMul, IE.top, IE.mag]; omega)
      (by simp only [ieMul, IE.eval, RealRAM.Op2.eval, c1 (P + 3) (by omega), c1 (B.o + 2) (by omega), p3r, hβ];
          push_cast; ring)) fun σ2 ⟨x2, bx2, d2, P2⟩ => ?_
    have s1' : σ2.sc (u + 13) = ((I.α i ⬝ᵥ a : ℤ) : ℝ) := by rw [P2.2.1 _ (by omega), s1]
    have bdot : |I.α i ⬝ᵥ a| ≤ 2 ^ (F + (F + F)) := abs_dot_le' hdF (ellAl_le hσF i) ba
    have G2 : FrameA Sw Nw Aw σ σ2 := (FR.trans (F1.mono (fun y h => by
      rcases h with h | h
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inl (by omega))) (fun j h => by
      rcases h with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inl h)) (fun _ _ h => h.elim))).trans
      (FrameA.ofP (P2.mono (fun y h => by
      rcases h with h | h
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inl (by omega))) (fun _ h => h.elim)))
    have hTw2 := hTw σ2 G2
    obtain ⟨⟨hσd2, -, -, -, -, -, -, -, -, -, -, -, -, -⟩, z02, o12, n12, -, -, -, -⟩ := hTw2
    have hvx : |σ2.sc (u + 14)| < 2 ^ ℓ := by rw [x2]; exact_mod_cast bx2
    have hvy : |σ2.sc (u + 13)| < 2 ^ ℓ := by rw [s1']; exact absR_lt bdot (by omega)
    have hpq : ∀ j : Fin I.m, j < i → p j = false := fun j hj => qp j hj
    by_cases hv : 2 ^ s * I.β i < I.α i ⬝ᵥ a
    · -- a violated row: copy `α_i`, the flag, end
      have hc : σ2.sc (u + 14) < σ2.sc (u + 13) := by rw [x2, s1']; exact_mod_cast hv
      refine XV.mono (XV.ifS_t hL (by omega) (by omega) hvx hvy hc (XV.mono (K := (1 + (d * (2 + 6) + 3)) + (1 + 1)) (XV.seq (XV.copy (E := F) (x := I.α i) hL
        (B := B) (u := u) (src := B.aW + 1) (dst := a0 + 2) (n0 := n0) (one := n0 + 4) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) z02 hσd2 n12
        (fun k => by rw [P2.2.2.1, F1.2.2.1 _ _ (fun h => h.elim), hα]) (ellAl_le hσF i) (by omega))
        fun σ5 ⟨m5, d5, F5⟩ => ?_) le_rfl fun _ h => h)) (K' := d * 8 + 7) (by ring_nf; omega) fun _ h => h
      · -- `P + 7 := 1`, `nm := 0`
        have z05 : σ5.sc u = 0 := by rw [F5.2.1 _ (by omega), z02]
        have o15 : σ5.sc (u + 1) = 1 := by rw [F5.2.1 _ (by omega), o12]
        refine XV.seq (XV.sop2 hL (x := P + 7) (a := u + 1) (b := u) (by omega) (by omega) (by omega) .add
          (by intro h; cases h) (by rw [o15]; exact h1) (by rw [z05]; exact h0)
          (by simp only [RealRAM.Op2.eval, o15, z05, add_zero]; exact h1)) fun σ6 e6 => ?_
        subst e6
        refine XV.mono (XV.nconst hL (i := n0 + 5) (by omega) 0 (by positivity)) (by omega) fun σ7 e7 => ?_
        subst e7
        have G7 : FrameA Sw Nw Aw σ ((σ5.setSc (P + 7) (RealRAM.Op2.eval .add (σ5.sc (u + 1)) (σ5.sc u))).setNat
            (n0 + 5) 0) :=
          ((G2.trans (F5.mono (fun y h => Or.inr (Or.inl (by omega))) (fun j h => by
            rcases h with h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inl h))) (fun b k h => Or.inr (Or.inl h.1)))).setSc (Or.inl rfl) _).setNat
            (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _
        refine ⟨by simp [d5, d2, d1, dr, dt], G7, ?_, Or.inr ⟨?_, by simp, ?_⟩⟩
        · simp; rw [if_neg (by omega), F5.1 _ (by omega), P2.1 _ not_false, F1.1 _ (by omega), Fr.1 _ ?_, qt]
          · omega
          · exact fun h => absurd (hnr _ h) (by omega)
        · simp [RealRAM.Op2.eval, o15, z05]
        · have hf : (List.finRange I.m).find? p = some i :=
            find_finRange_some p i (by simp [p, hv]) hpq
          unfold RowsOut
          rw [show (fun i => decide (2 ^ s * I.β i < I.α i ⬝ᵥ a)) = p from rfl, hf]
          refine ⟨by simp [RealRAM.Op2.eval, o15, z05], fun k => ?_⟩
          simp only [Env.setNat_arr]
          simpa using m5 k
    · -- no violation: next row
      have hc : ¬ σ2.sc (u + 14) < σ2.sc (u + 13) := by rw [x2, s1']; exact_mod_cast hv
      have hrE2 : σ2.nat B.rE = t := by
        rw [P2.1 _ not_false, F1.1 _ (by omega), Fr.1 _ (fun h => absurd (hnr _ h) (by omega)), qt]
      refine XV.mono (XV.ifS_f hL (by omega) (by omega) hvx hvy hc (XV.nadd hL (i := B.rE) (a := B.rE)
        (b := n0 + 4) (by omega) (by omega) (by omega) (by rw [hrE2]; omega) (by rw [n12]; omega)))
        (K' := d * 8 + 7) (by omega) fun σ7 e7 => ?_
      subst e7
      refine ⟨by simp [d2, d1, dr, dt], G2.setNat (Or.inl rfl) _, by simp [hrE2, n12]; omega, Or.inl ⟨?_, ?_, ?_, ?_⟩⟩
      · simp only [Env.setNat_sc]
        rw [P2.2.1 _ (by omega), F1.2.1 _ (by omega), Fr.2.1 _ (by
          rintro (h | h)
          · omega
          · exact absurd (hsr _ h) (by omega)), q0]
      · simp; rw [if_neg (by omega), P2.1 _ not_false, F1.1 _ (by omega), Fr.1 _ ?_, qm]
        exact fun h => absurd (hnr _ h) (by omega)
      · simp [hrE2, n12]
      · intro j hj
        by_cases hjt : j.1 < t
        · exact qp j hjt
        · have : j = i := Fin.ext (by simp [i]; omega)
          subst this
          simpa [p] using hv
  -- after the loop
  rcases hJ with ⟨dJ, FJ, -, hcase⟩
  refine ⟨?_, dJ, FJ⟩
  rcases hcase with ⟨q0, qm, qt, qp⟩ | ⟨-, -, hR⟩
  · have ht : I.m ≤ t' := by omega
    have hf : (List.finRange I.m).find? p = none :=
      find_finRange_none p fun j => qp j (by omega)
    unfold RowsOut
    rw [show (fun i => decide (2 ^ s * I.β i < I.α i ⬝ᵥ a)) = p from rfl, hf]
    exact q0
  · exact hR

/-! ## (T3) -/

theorem ellH_le {I : EllI d} {F : ℕ} (hσF : ellSz I ≤ F) (i k : Fin d) : |I.H i k| ≤ 2 ^ F :=
  (abs_le_sz ((ellMx_le I).2.2.1 i k)).trans (pow_le_pow_right₀ (by norm_num) hσF)

theorem ellP_le {I : EllI d} {F : ℕ} (hσF : ellSz I ≤ F) (i k : Fin d) : |I.P i k| ≤ 2 ^ F :=
  (abs_le_sz ((ellMx_le I).2.2.2.1 i k)).trans (pow_le_pow_right₀ (by norm_num) hσF)

theorem ellG_le {I : EllI d} {F : ℕ} (hσF : ellSz I ≤ F) (k : Fin d) : |I.g k| ≤ 2 ^ F :=
  (abs_le_sz ((ellMx_le I).2.2.2.2.1 k)).trans (pow_le_pow_right₀ (by norm_num) hσF)

theorem ellF_le {I : EllI d} {F : ℕ} (hσF : ellSz I ≤ F) (k : Fin d) : |I.f k| ≤ 2 ^ F :=
  (abs_le_sz ((ellMx_le I).2.2.2.2.2.1 k)).trans (pow_le_pow_right₀ (by norm_num) hσF)

theorem ellL_le {I : EllI d} {F : ℕ} (hσF : ellSz I ≤ F) : |I.ℓ| ≤ 2 ^ F :=
  (abs_le_sz (ellMx_le I).2.2.2.2.2.2.1).trans (pow_le_pow_right₀ (by norm_num) hσF)

theorem ellDf_le {I : EllI d} {F : ℕ} (hσF : ellSz I ≤ F) : |(I.Df : ℤ)| ≤ 2 ^ F :=
  (abs_le_sz' (ellMx_le I).2.2.2.2.2.2.2.1).trans (pow_le_pow_right₀ (by norm_num) hσF)

set_option maxHeartbeats 8000000 in
/-- (T3) on the machine: `v = H a` into the array `a0 + 3`, `u + 15 = 2^{2s+1} ℓ`,
`u + 16 = a·v - 2^{s+1} g·a`. -/
theorem XV.testQ {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk} {I : EllI d}
    {nS nN nA s P u a0 kb n0 one nm F : ℕ} {a : Fin d → ℤ} (hB : B.OK L nS nN nA)
    (lay : TestLay L B P u a0 kb n0 one nm) (hT : TestEnv B I s P u one σ)
    (ha : ∀ k : Fin d, σ.arr (a0 + 1) k = a k) (ba : ∀ k, |a k| ≤ 2 ^ F) (hσF : ellSz I ≤ F)
    (hsF : 2 * s + 1 ≤ F) (hdF : d ≤ F) (hℓ : 64 * F + 16 < ℓ) :
    XRunsB L X ℓa ℓ (xtestQ L B P u a0 n0 one) σ (d * (d * 10 + 9) + 4 + (d * 10 + 5 + (d * 10 + 5 + (3 + 5))))
      (fun σ' => σ'.sc (u + 15) = ((2 ^ (2 * s + 1) * I.ℓ : ℤ) : ℝ) ∧
        σ'.sc (u + 16) = ((a ⬝ᵥ (I.H *ᵥ a) - 2 ^ (s + 1) * (I.g ⬝ᵥ a) : ℤ) : ℝ) ∧
        (∀ k : Fin d, σ'.arr (a0 + 3) k = (I.H *ᵥ a) k) ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => u + 13 ≤ y) (fun j => n0 ≤ j ∧ j ≤ n0 + 2) (fun b c => b = a0 + 3 ∧ c < d) σ σ') := by
  obtain ⟨-, -, -, hrd, -, hsl, -, -, -, -, -, -, -, haH, hag, -, -⟩ := hB
  obtain ⟨oP, Pu, uS, wa, -, aA, rn, onee, -, nN⟩ := lay
  subst onee
  obtain ⟨⟨e1, -, e3, -, -, -, -, -, -, -, e11, e12, -, -⟩, z, -, n1, -, p4, -, p6⟩ := hT
  have bv : ∀ k, |(I.H *ᵥ a) k| ≤ 2 ^ (3 * F) := fun k =>
    abs_le_pow_mono (abs_mulVec_le' hdF (ellH_le hσF) ba k) (by omega)
  have ba3 : ∀ k, |a k| ≤ 2 ^ (3 * F) := fun k => abs_le_pow_mono (ba k) (by omega)
  -- `v = H a`
  refine XV.seq (XV.matvec (E := F) (M := I.H) (x := a) hL (z := u) (r := u + 13) (t := u + 24) (aM := B.aH)
    (ax := a0 + 1) (ay := a0 + 3) (ni := n0) (nr := n0 + 1) (nk := n0 + 2) (nd := B.rd) (none := n0 + 4)
    (by omega) (by omega) (by omega) (by omega) z (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (nodup5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)) e1 n1 e11 ha (ellH_le hσF) ba (by omega) (d_mul_pow_lt hdF (by omega))) fun σ1 ⟨m1, d1, F1⟩ => ?_
  have c1 : ∀ y, y < u + 13 → σ1.sc y = σ.sc y := fun y hy => F1.2.1 y (by omega)
  have ha1 : ∀ k : Fin d, σ1.arr (a0 + 1) k = a k := fun k => by
    rw [F1.2.2.1 _ _ (fun h => absurd h.1 (by omega)), ha]
  have hg1 : ∀ k : Fin d, σ1.arr B.ag k = I.g k := fun k => by
    rw [F1.2.2.1 _ _ (fun h => absurd h.1 (by omega)), e12]
  have hd1 : σ1.nat B.rd = d := by rw [F1.1 _ (by omega), e1]
  have n11 : σ1.nat (n0 + 4) = 1 := by rw [F1.1 _ (by omega), n1]
  -- `u + 13 = a·v`
  refine XV.seq (XV.dot (E := 3 * F) (x := a) (y := I.H *ᵥ a) hL (z := u) (r := u + 13) (t := u + 24)
    (nr := n0 + 1) (nk := n0 + 2) (nd := B.rd) (none := n0 + 4) (by omega) (by omega) (by omega) (by omega)
    (by rw [c1 _ (by omega), z]) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (nodup4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) hd1 n11 ha1 m1 ba3 bv (by omega)
    (d_mul_pow_lt hdF (by omega))) fun σ2 ⟨s2, d2, F2⟩ => ?_
  have c2 : ∀ y, y < u + 13 → σ2.sc y = σ.sc y := fun y hy => by rw [F2.2.1 y (by omega), c1 y hy]
  -- `u + 14 = g·a`
  refine XV.seq (XV.dot (E := F) (x := I.g) (y := a) hL (z := u) (r := u + 14) (t := u + 24)
    (nr := n0 + 1) (nk := n0 + 2) (nd := B.rd) (none := n0 + 4) (by omega) (by omega) (by omega) (by omega)
    (by rw [c2 _ (by omega), z]) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (nodup4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) (by rw [F2.1 _ (by omega), hd1])
    (by rw [F2.1 _ (by omega), n11]) (fun k => by rw [F2.2.2.1 _ _ (fun h => h.elim), hg1])
    (fun k => by rw [F2.2.2.1 _ _ (fun h => h.elim), ha1]) (ellG_le hσF) ba (by omega)
    (d_mul_pow_lt hdF (by omega))) fun σ3 ⟨s3, d3, F3⟩ => ?_
  have c3 : ∀ y, y < u + 13 → σ3.sc y = σ.sc y := fun y hy => by rw [F3.2.1 y (by omega), c2 y hy]
  have s23 : σ3.sc (u + 13) = ((a ⬝ᵥ (I.H *ᵥ a) : ℤ) : ℝ) := by rw [F3.2.1 _ (by omega), s2]
  -- `u + 15 = 2^{2s+1} ℓ`
  have L4 : (ieMul (P + 6) B.sl).Leaves F σ3 := by
    simp only [ieMul, IE.Leaves]
    exact ⟨⟨_, by rw [c3 _ (by omega), p6], abs_pow_le (by omega)⟩, ⟨_, by rw [c3 _ (by omega), e3], ellL_le hσF⟩⟩
  refine XV.seq (XV.ieRun (E := F) (e := ieMul (P + 6) B.sl) (v := 2 ^ (2 * s + 1) * I.ℓ) hL (x := u + 15)
    (t := u + 24) (z := u) (by simp only [ieMul, IE.WF]; exact ⟨(by intro h; cases h), by omega, by omega⟩)
    (by omega) (by omega) (by simp only [ieMul, IE.scr]; omega) (by rw [c3 _ (by omega), z]) L4
    (by simp only [ieMul, IE.top, IE.mag]; omega)
    (by simp only [ieMul, IE.eval, RealRAM.Op2.eval, c3 (P + 6) (by omega), c3 B.sl (by omega), p6, e3];
        push_cast; ring)) fun σ4 ⟨x4, _, d4, P4⟩ => ?_
  have e4 : ∀ y, y ≠ u + 15 → y < u + 24 → σ4.sc y = σ3.sc y := fun y h1 h2 => P4.2.1 y (by
    rintro (h | h)
    · exact h1 h
    · omega)
  -- `u + 16 = a·v - 2^{s+1} g·a`
  have L5 : (IE.op .sub (.sc (u + 13)) (ieMul (P + 4) (u + 14))).Leaves (5 * F) σ4 := by
    simp only [ieMul, IE.Leaves]
    refine ⟨⟨_, by rw [e4 _ (by omega) (by omega), s23],
      abs_le_pow_mono (abs_dot_le' hdF ba bv) (by omega)⟩, ⟨_, by rw [e4 _ (by omega) (by omega), c3 _ (by omega), p4],
      abs_pow_le (by omega)⟩, ⟨_, by rw [e4 _ (by omega) (by omega), s3],
      abs_le_pow_mono (abs_dot_le' hdF (ellG_le hσF) ba) (by omega)⟩⟩
  refine XV.mono (XV.ieRun (E := 5 * F) (e := IE.op .sub (.sc (u + 13)) (ieMul (P + 4) (u + 14)))
    (v := a ⬝ᵥ (I.H *ᵥ a) - 2 ^ (s + 1) * (I.g ⬝ᵥ a)) hL (x := u + 16) (t := u + 24) (z := u)
    (by simp only [ieMul, IE.WF]; exact ⟨(by intro h; cases h), by omega, (by intro h; cases h), by omega, by omega⟩)
    (by omega) (by omega) (by simp only [ieMul, IE.scr]; omega) (by rw [e4 _ (by omega) (by omega), c3 _ (by omega), z])
    L5 (by simp only [ieMul, IE.top, IE.mag]; omega)
    (by simp only [ieMul, IE.eval, RealRAM.Op2.eval, e4 (u + 13) (by omega) (by omega),
        e4 (P + 4) (by omega) (by omega), e4 (u + 14) (by omega) (by omega), s23, c3 (P + 4) (by omega), p4, s3];
        push_cast; ring)) le_rfl fun σ5 ⟨x5, _, d5, P5⟩ => ?_
  refine ⟨by rw [P5.2.1 _ (by omega), x4], x5, fun k => by rw [P5.2.2.1, P4.2.2.1, F3.2.2.1 _ _ (fun h => h.elim),
    F2.2.2.1 _ _ (fun h => h.elim), m1], by rw [d5, d4, d3, d2, d1], ?_⟩
  have G1 : FrameA (fun y => u + 13 ≤ y) (fun j => n0 ≤ j ∧ j ≤ n0 + 2) (fun b c => b = a0 + 3 ∧ c < d) σ σ1 :=
    F1.mono (fun y h => by rcases h with h | h <;> omega) (fun j h => by rcases h with h | h | h <;> omega)
      (fun _ _ h => h)
  have G2 : FrameA (fun y => u + 13 ≤ y) (fun j => n0 ≤ j ∧ j ≤ n0 + 2) (fun b c => b = a0 + 3 ∧ c < d) σ1 σ2 :=
    F2.mono (fun y h => by rcases h with h | h <;> omega) (fun j h => by rcases h with h | h <;> omega)
      (fun _ _ h => h.elim)
  have G3 : FrameA (fun y => u + 13 ≤ y) (fun j => n0 ≤ j ∧ j ≤ n0 + 2) (fun b c => b = a0 + 3 ∧ c < d) σ2 σ3 :=
    F3.mono (fun y h => by rcases h with h | h <;> omega) (fun j h => by rcases h with h | h <;> omega)
      (fun _ _ h => h.elim)
  have G4 : FrameA (fun y => u + 13 ≤ y) (fun j => n0 ≤ j ∧ j ≤ n0 + 2) (fun b c => b = a0 + 3 ∧ c < d) σ3 σ4 :=
    FrameA.ofP (P4.mono (fun y h => by rcases h with h | h <;> omega) (fun _ h => h.elim))
  have G5 : FrameA (fun y => u + 13 ≤ y) (fun j => n0 ≤ j ∧ j ≤ n0 + 2) (fun b c => b = a0 + 3 ∧ c < d) σ4 σ5 :=
    FrameA.ofP (P5.mono (fun y h => by rcases h with h | h <;> omega) (fun _ h => h.elim))
  exact (((G1.trans G2).trans G3).trans G4).trans G5

set_option maxHeartbeats 4000000 in
/-- The cut of (T3) on the machine: `c = v - 2^s g` into the array `a0 + 2`, `v` in the array `a0 + 3`. -/
theorem XV.cutQ {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk} {I : EllI d}
    {nS nN nA s P u a0 kb n0 one nm F : ℕ} {v : Fin d → ℤ} (hB : B.OK L nS nN nA)
    (lay : TestLay L B P u a0 kb n0 one nm) (hT : TestEnv B I s P u one σ)
    (hv : ∀ k : Fin d, σ.arr (a0 + 3) k = v k) (bv : ∀ k, |v k| ≤ 2 ^ (3 * F)) (hσF : ellSz I ≤ F)
    (hsF : 2 * s + 1 ≤ F) (hℓ : 64 * F + 16 < ℓ) :
    XRunsB L X ℓa ℓ (xcutQ L B P u a0 n0 one) σ (1 + (d * (7 + 6) + 3)) (fun σ' =>
      (∀ k : Fin d, σ'.arr (a0 + 2) k = (v - (2 ^ s : ℤ) • I.g) k) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => u + 24 ≤ y) (fun j => j = n0 + 1 ∨ j = n0 + 2) (fun b c => b = a0 + 2 ∧ c < d) σ σ') := by
  obtain ⟨-, -, -, hrd, -, -, -, -, -, -, -, -, -, -, hag, -, -⟩ := hB
  obtain ⟨oP, Pu, uS, wa, -, aA, rn, onee, -, nN⟩ := lay
  subst onee
  obtain ⟨⟨e1, -, -, -, -, -, -, -, -, -, -, e12, -, -⟩, z, -, n1, p3, -, -, -⟩ := hT
  have hda := asz_lt hL (show a0 + 2 < L.NA by omega)
  have hdl : d < 2 ^ ℓa := by unfold asz at hda; nlinarith
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  have hcd : ∀ k < d, 0 + 1 * k < asz d := fun k hk => by unfold asz; nlinarith
  refine XV.seq (XV.nconst hL (i := n0 + 1) (by omega) 0 (by positivity)) fun σ0 e0 => ?_
  subst e0
  refine XV.mono (XV.mapE (E := 3 * F) (N := d) (base := 0) (st := 1) (F := vext (v - (2 ^ s : ℤ) • I.g)) hL
    (z := u) (t := u + 24) (e := .op .sub (.arr (a0 + 3) (n0 + 2)) (.op .mul (.sc (P + 3)) (.arr B.ag (n0 + 2))))
    (aB := a0 + 2) (nr := n0 + 1) (nst := n0 + 4) (nk := n0 + 2) (nn := B.rd) (none := n0 + 4)
    (by simp only [IE.WF]; exact ⟨(by intro h; cases h), ⟨by omega, by omega⟩, (by intro h; cases h), by omega,
      by omega, by omega⟩) (by omega) (by simp only [IE.scr]; omega) (by simpa using z) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (nodup4 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)) (by omega) (by omega) (by simp; rw [if_neg (by omega), e1]) (by simpa using n1)
    (by simp) (by simpa using n1) one_pos hcd hdl (by simpa using hdl) hsa
    (by simp only [IE.top, IE.mag]; omega) ?_) le_rfl fun σ1 ⟨m1, r1, d1, F1⟩ => ?_
  · intro k hk σ' hF hd hkt hkr
    have ev : σ'.arr (a0 + 3) k = v ⟨k, hk⟩ := by
      rw [hF.2.2.1 _ _ (fun h => absurd h.1 (by omega)), Env.setNat_arr]; exact hv ⟨k, hk⟩
    have eg : σ'.arr B.ag k = I.g ⟨k, hk⟩ := by
      rw [hF.2.2.1 _ _ (fun h => absurd h.1 (by omega)), Env.setNat_arr]; exact e12 ⟨k, hk⟩
    have ep : σ'.sc (P + 3) = ((2 ^ s : ℤ) : ℝ) := by rw [hF.2.1 _ (by omega)]; simpa using p3
    have hka : k < asz d := by simpa using hcd k hk
    simp only [IE.Leaves, IE.eval, RealRAM.Op2.eval, hkt, ev, eg, ep]
    refine ⟨⟨⟨hka, _, rfl, bv _⟩, ⟨_, rfl, abs_pow_le (by omega)⟩, hka, _, rfl,
      abs_le_pow_mono (ellG_le hσF _) (by omega)⟩, ?_⟩
    rw [vext_lt _ hk]; simp [Pi.sub_apply, smul_eq_mul]
  · refine ⟨fun k => ?_, by rw [d1]; simp, ?_⟩
    · have := m1 k k.2
      simp only [zero_add, one_mul] at this
      rw [this, vext_lt _ k.2]
    · exact ((FrameA.refl _ _ _ σ).setNat (Or.inl rfl) 0).trans
        (F1.mono (fun _ h => h) (fun j h => by rcases h with h | h <;> omega)
          (fun b c h => ⟨h.1, by simpa using h.2.2⟩))

set_option maxHeartbeats 8000000 in
/-- (T4) on the machine: `w = P a` into the array `a0 + 3`, the gradient `D_f w - 2^s f` into the array `a0 + 2`,
`u + 15 = V = D_f a·w - 2^{s+1} f·a`. -/
theorem XV.testV {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk} {I : EllI d}
    {nS nN nA s P u a0 kb n0 one nm F : ℕ} {a : Fin d → ℤ} (hB : B.OK L nS nN nA)
    (lay : TestLay L B P u a0 kb n0 one nm) (hT : TestEnv B I s P u one σ)
    (ha : ∀ k : Fin d, σ.arr (a0 + 1) k = a k) (ba : ∀ k, |a k| ≤ 2 ^ F) (hσF : ellSz I ≤ F)
    (hsF : 2 * s + 1 ≤ F) (hdF : d ≤ F) (hℓ : 64 * F + 16 < ℓ) :
    XRunsB L X ℓa ℓ (xtestV L B P u a0 n0 one) σ
      (d * (d * 10 + 9) + 4 + (1 + ((d * (9 + 6) + 3) + (d * 10 + 5 + (d * 10 + 5 + 7))))) (fun σ' =>
      (∀ k : Fin d, σ'.arr (a0 + 2) k = (I.P *ᵥ ((I.Df : ℤ) • a) - (2 ^ s : ℤ) • I.f) k) ∧
      σ'.sc (u + 15) = (((I.Df : ℤ) * (a ⬝ᵥ (I.P *ᵥ a)) - 2 ^ (s + 1) * (I.f ⬝ᵥ a) : ℤ) : ℝ) ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => u + 13 ≤ y) (fun j => n0 ≤ j ∧ j ≤ n0 + 2) (fun b c => (b = a0 + 2 ∨ b = a0 + 3) ∧ c < d)
        σ σ') := by
  obtain ⟨-, -, -, hrd, -, -, hsDf, -, -, -, -, -, -, -, -, haP, haf⟩ := hB
  obtain ⟨oP, Pu, uS, wa, -, aA, rn, onee, -, nN⟩ := lay
  subst onee
  obtain ⟨⟨e1, -, -, e4, -, -, -, -, -, -, -, -, e13, e14⟩, z, -, n1, p3, p4, -, -⟩ := hT
  have hda := asz_lt hL (show a0 + 2 < L.NA by omega)
  have hdl : d < 2 ^ ℓa := by unfold asz at hda; nlinarith
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  have hcd : ∀ k < d, 0 + 1 * k < asz d := fun k hk => by unfold asz; nlinarith
  have bw : ∀ k, |(I.P *ᵥ a) k| ≤ 2 ^ (3 * F) := fun k =>
    abs_le_pow_mono (abs_mulVec_le' hdF (ellP_le hσF) ba k) (by omega)
  have ba3 : ∀ k, |a k| ≤ 2 ^ (3 * F) := fun k => abs_le_pow_mono (ba k) (by omega)
  -- `w = P a`
  refine XV.seq (XV.matvec (E := F) (M := I.P) (x := a) hL (z := u) (r := u + 13) (t := u + 24) (aM := B.aP)
    (ax := a0 + 1) (ay := a0 + 3) (ni := n0) (nr := n0 + 1) (nk := n0 + 2) (nd := B.rd) (none := n0 + 4)
    (by omega) (by omega) (by omega) (by omega) z (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (nodup5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)) e1 n1 e13 ha (ellP_le hσF) ba (by omega) (d_mul_pow_lt hdF (by omega))) fun σ1 ⟨m1, d1, F1⟩ => ?_
  have c1 : ∀ y, y < u + 13 → σ1.sc y = σ.sc y := fun y hy => F1.2.1 y (by omega)
  have ha1 : ∀ k : Fin d, σ1.arr (a0 + 1) k = a k := fun k => by
    rw [F1.2.2.1 _ _ (fun h => absurd h.1 (by omega)), ha]
  have hf1 : ∀ k : Fin d, σ1.arr B.af k = I.f k := fun k => by
    rw [F1.2.2.1 _ _ (fun h => absurd h.1 (by omega)), e14]
  have hd1 : σ1.nat B.rd = d := by rw [F1.1 _ (by omega), e1]
  have n11 : σ1.nat (n0 + 4) = 1 := by rw [F1.1 _ (by omega), n1]
  -- the gradient
  refine XV.seq (XV.nconst hL (i := n0 + 1) (by omega) 0 (by positivity)) fun σ0 e0 => ?_
  subst e0
  refine XV.seq (XV.mapE (E := 3 * F) (N := d) (base := 0) (st := 1)
      (F := vext (I.P *ᵥ ((I.Df : ℤ) • a) - (2 ^ s : ℤ) • I.f)) hL (z := u) (t := u + 24)
      (e := .op .sub (.op .mul (.sc B.sDf) (.arr (a0 + 3) (n0 + 2))) (.op .mul (.sc (P + 3)) (.arr B.af (n0 + 2))))
      (aB := a0 + 2) (nr := n0 + 1) (nst := n0 + 4) (nk := n0 + 2) (nn := B.rd) (none := n0 + 4)
      (by simp only [IE.WF]; exact ⟨(by intro h; cases h), ⟨(by intro h; cases h), by omega, by omega, by omega⟩,
        (by intro h; cases h), by omega, by omega, by omega⟩) (by omega) (by simp only [IE.scr]; omega)
      (by simpa [c1 u (by omega)] using z) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (nodup4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) (by omega) (by omega)
      (by simp; rw [if_neg (by omega), hd1]) (by simpa using n11) (by simp)
      (by simpa using n11) one_pos hcd hdl (by simpa using hdl) hsa
      (by simp only [IE.top, IE.mag]; omega) ?_) fun σ2 ⟨m2, r2, d2, F2⟩ => ?_
  · intro k hk σ' hF hd hkt hkr
    have ew : σ'.arr (a0 + 3) k = (I.P *ᵥ a) ⟨k, hk⟩ := by
      rw [hF.2.2.1 _ _ (fun h => absurd h.1 (by omega)), Env.setNat_arr]; exact m1 ⟨k, hk⟩
    have ef : σ'.arr B.af k = I.f ⟨k, hk⟩ := by
      rw [hF.2.2.1 _ _ (fun h => absurd h.1 (by omega)), Env.setNat_arr]; exact hf1 ⟨k, hk⟩
    have ep : σ'.sc (P + 3) = ((2 ^ s : ℤ) : ℝ) := by rw [hF.2.1 _ (by omega), Env.setNat_sc, c1 _ (by omega)]; simpa using p3
    have eD : σ'.sc B.sDf = ((I.Df : ℤ) : ℝ) := by
      rw [hF.2.1 _ (by omega), Env.setNat_sc, c1 _ (by omega), e4]; norm_cast
    have hka : k < asz d := by simpa using hcd k hk
    simp only [IE.Leaves, IE.eval, RealRAM.Op2.eval, hkt, ew, ef, ep, eD]
    refine ⟨⟨⟨⟨_, rfl, abs_le_pow_mono (ellDf_le hσF) (by omega)⟩, hka, _, rfl, bw _⟩, ⟨_, rfl, abs_pow_le (by omega)⟩,
      hka, _, rfl, abs_le_pow_mono (ellF_le hσF _) (by omega)⟩, ?_⟩
    rw [vext_lt _ hk]; simp only [Pi.sub_apply, mulVec_smul_int, Pi.smul_apply, smul_eq_mul]; push_cast; ring
  have c2 : ∀ y, y < u + 13 → σ2.sc y = σ.sc y := fun y hy => by
    rw [F2.2.1 y (by omega), Env.setNat_sc, c1 y hy]
  have ha2 : ∀ k : Fin d, σ2.arr (a0 + 1) k = a k := fun k => by
    rw [F2.2.2.1 _ _ (fun h => absurd h.1 (by omega)), Env.setNat_arr, ha1]
  have hw2 : ∀ k : Fin d, σ2.arr (a0 + 3) k = (I.P *ᵥ a) k := fun k => by
    rw [F2.2.2.1 _ _ (fun h => absurd h.1 (by omega)), Env.setNat_arr, m1]
  have hf2 : ∀ k : Fin d, σ2.arr B.af k = I.f k := fun k => by
    rw [F2.2.2.1 _ _ (fun h => absurd h.1 (by omega)), Env.setNat_arr, hf1]
  have hd2 : σ2.nat B.rd = d := by
    rw [F2.1 _ (fun h => by rcases h with h | h <;> omega)]; simp; rw [if_neg (by omega), hd1]
  have n12 : σ2.nat (n0 + 4) = 1 := by
    rw [F2.1 _ (fun h => by rcases h with h | h <;> omega)]; simpa using n11
  -- `u + 13 = a·w`
  refine XV.seq (XV.dot (E := 3 * F) (x := a) (y := I.P *ᵥ a) hL (z := u) (r := u + 13) (t := u + 24)
    (nr := n0 + 1) (nk := n0 + 2) (nd := B.rd) (none := n0 + 4) (by omega) (by omega) (by omega) (by omega)
    (by rw [c2 _ (by omega), z]) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (nodup4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) hd2 n12 ha2 hw2 ba3 bw (by omega)
    (d_mul_pow_lt hdF (by omega))) fun σ3 ⟨s3, d3, F3⟩ => ?_
  have c3 : ∀ y, y < u + 13 → σ3.sc y = σ.sc y := fun y hy => by rw [F3.2.1 y (by omega), c2 y hy]
  -- `u + 14 = f·a`
  refine XV.seq (XV.dot (E := F) (x := I.f) (y := a) hL (z := u) (r := u + 14) (t := u + 24)
    (nr := n0 + 1) (nk := n0 + 2) (nd := B.rd) (none := n0 + 4) (by omega) (by omega) (by omega) (by omega)
    (by rw [c3 _ (by omega), z]) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (nodup4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) (by rw [F3.1 _ (by omega), hd2])
    (by rw [F3.1 _ (by omega), n12]) (fun k => by rw [F3.2.2.1 _ _ (fun h => h.elim), hf2])
    (fun k => by rw [F3.2.2.1 _ _ (fun h => h.elim), ha2]) (ellF_le hσF) ba (by omega)
    (d_mul_pow_lt hdF (by omega))) fun σ4 ⟨s4, d4, F4⟩ => ?_
  have c4 : ∀ y, y < u + 13 → σ4.sc y = σ.sc y := fun y hy => by rw [F4.2.1 y (by omega), c3 y hy]
  have s34 : σ4.sc (u + 13) = ((a ⬝ᵥ (I.P *ᵥ a) : ℤ) : ℝ) := by rw [F4.2.1 _ (by omega), s3]
  -- `u + 15 = V`
  have eD : σ4.sc B.sDf = ((I.Df : ℤ) : ℝ) := by rw [c4 _ (by omega), e4]; norm_cast
  have L5 : (IE.op .sub (ieMul B.sDf (u + 13)) (ieMul (P + 4) (u + 14))).Leaves (5 * F) σ4 := by
    simp only [ieMul, IE.Leaves]
    exact ⟨⟨⟨_, eD, abs_le_pow_mono (ellDf_le hσF) (by omega)⟩, ⟨_, s34,
      abs_le_pow_mono (abs_dot_le' hdF ba bw) (by omega)⟩⟩, ⟨⟨_, by rw [c4 _ (by omega), p4],
      abs_pow_le (by omega)⟩, ⟨_, s4, abs_le_pow_mono (abs_dot_le' hdF (ellF_le hσF) ba) (by omega)⟩⟩⟩
  refine XV.mono (XV.ieRun (E := 5 * F) (e := IE.op .sub (ieMul B.sDf (u + 13)) (ieMul (P + 4) (u + 14)))
    (v := (I.Df : ℤ) * (a ⬝ᵥ (I.P *ᵥ a)) - 2 ^ (s + 1) * (I.f ⬝ᵥ a)) hL (x := u + 15) (t := u + 24) (z := u)
    (by simp only [ieMul, IE.WF]; exact ⟨(by intro h; cases h), ⟨(by intro h; cases h), by omega, by omega⟩,
      (by intro h; cases h), by omega, by omega⟩)
    (by omega) (by omega) (by simp only [ieMul, IE.scr]; omega) (by rw [c4 _ (by omega), z])
    L5 (by simp only [ieMul, IE.top, IE.mag]; omega)
    (by simp only [ieMul, IE.eval, RealRAM.Op2.eval, eD, s34, c4 (P + 4) (by omega), p4, s4]; push_cast; ring))
    le_rfl fun σ5 ⟨x5, _, d5, P5⟩ => ?_
  refine ⟨fun k => by
    have e2 := m2 k k.2
    simp only [zero_add, one_mul] at e2
    rw [P5.2.2.1, F4.2.2.1 _ _ (fun h => h.elim), F3.2.2.1 _ _ (fun h => h.elim), e2, vext_lt _ k.2],
    x5, by rw [d5, d4, d3, d2]; simpa using d1, ?_⟩
  have G1 : FrameA (fun y => u + 13 ≤ y) (fun j => n0 ≤ j ∧ j ≤ n0 + 2)
      (fun b c => (b = a0 + 2 ∨ b = a0 + 3) ∧ c < d) σ σ1 :=
    F1.mono (fun y h => by rcases h with h | h <;> omega) (fun j h => by rcases h with h | h | h <;> omega)
      (fun _ _ h => ⟨Or.inr h.1, h.2⟩)
  have G2 : FrameA (fun y => u + 13 ≤ y) (fun j => n0 ≤ j ∧ j ≤ n0 + 2)
      (fun b c => (b = a0 + 2 ∨ b = a0 + 3) ∧ c < d) σ1 σ2 :=
    ((FrameA.refl _ _ _ σ1).setNat (show n0 ≤ n0 + 1 ∧ n0 + 1 ≤ n0 + 2 by omega) 0).trans
      (F2.mono (fun y h => by omega) (fun j h => by rcases h with h | h <;> omega)
        (fun b c h => ⟨Or.inl h.1, by simpa using h.2.2⟩))
  have G3 : FrameA (fun y => u + 13 ≤ y) (fun j => n0 ≤ j ∧ j ≤ n0 + 2)
      (fun b c => (b = a0 + 2 ∨ b = a0 + 3) ∧ c < d) σ2 σ3 :=
    F3.mono (fun y h => by rcases h with h | h <;> omega) (fun j h => by rcases h with h | h <;> omega)
      (fun _ _ h => h.elim)
  have G4 : FrameA (fun y => u + 13 ≤ y) (fun j => n0 ≤ j ∧ j ≤ n0 + 2)
      (fun b c => (b = a0 + 2 ∨ b = a0 + 3) ∧ c < d) σ3 σ4 :=
    F4.mono (fun y h => by rcases h with h | h <;> omega) (fun j h => by rcases h with h | h <;> omega)
      (fun _ _ h => h.elim)
  have G5 : FrameA (fun y => u + 13 ≤ y) (fun j => n0 ≤ j ∧ j ≤ n0 + 2)
      (fun b c => (b = a0 + 2 ∨ b = a0 + 3) ∧ c < d) σ4 σ5 :=
    FrameA.ofP (P5.mono (fun y h => by rcases h with h | h <;> omega) (fun _ h => h.elim))
  exact (((G1.trans G2).trans G3).trans G4).trans G5

/-! ## The kept point and the end of (T4) -/

/-- The kept point after (T4) at the point `a` with the value `V` (as in `ellTest`). -/
def newKept (a : Fin d → ℤ) (V : ℤ) : Option ((Fin d → ℤ) × ℤ) → Option ((Fin d → ℤ) × ℤ)
  | none => some (a, V)
  | some (b, W) => if V < W then some (a, V) else some (b, W)

set_option maxHeartbeats 4000000 in
/-- The new kept point: `a` into the array `kb`, `V` into `P + 2`, the flag `1` into `P + 1`. -/
theorem XV.keepNew {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk} {I : EllI d}
    {nS nN nA s P u a0 kb n0 one nm F : ℕ} {a : Fin d → ℤ} {V : ℤ} (hB : B.OK L nS nN nA)
    (lay : TestLay L B P u a0 kb n0 one nm) (hT : TestEnv B I s P u one σ)
    (ha : ∀ k : Fin d, σ.arr (a0 + 1) k = a k) (ba : ∀ k, |a k| ≤ 2 ^ F) (hV : σ.sc (u + 15) = V)
    (bV : |((V : ℤ) : ℝ)| < 2 ^ ℓ) (hℓ : 64 * F + 16 < ℓ) :
    XRunsB L X ℓa ℓ (xkeepNew L B P u a0 kb n0 one) σ ((1 + (d * (2 + 6) + 3)) + (1 + 1)) (fun σ' =>
      KeptIn P kb (some (a, V)) σ' ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = P + 1 ∨ y = P + 2 ∨ u + 24 ≤ y) (fun j => j = n0 + 1 ∨ j = n0 + 2)
        (fun b c => b = kb ∧ c < d) σ σ') := by
  obtain ⟨-, -, -, hrd, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hB
  obtain ⟨oP, Pu, uS, wa, kbe, aA, rn, onee, -, nN⟩ := lay
  subst onee kbe
  obtain ⟨⟨e1, -, -, -, -, -, -, -, -, -, -, -, -, -⟩, z, o1, n1, -, -, -, -⟩ := hT
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by simp only [abs_zero]; positivity
  have h1 : |(1 : ℝ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  refine XV.seq (XV.copy (E := F) (x := a) hL (B := B) (u := u) (src := a0 + 1) (dst := a0 + 6) (n0 := n0)
    (one := n0 + 4) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) z e1 n1 ha ba (by omega)) fun σ1 ⟨m1, d1, F1⟩ => ?_
  have c1 : ∀ y, y < u + 24 → σ1.sc y = σ.sc y := fun y hy => F1.2.1 y (by omega)
  refine XV.seq (XV.sop2 hL (x := P + 2) (a := u + 15) (b := u) (by omega) (by omega) (by omega) .add
    (by intro h; cases h) (by rw [c1 _ (by omega), hV]; exact bV) (by rw [c1 _ (by omega), z]; exact h0)
    (by simp only [RealRAM.Op2.eval, c1 (u + 15) (by omega), c1 u (by omega), hV, z, add_zero]; exact bV))
    fun σ2 e2 => ?_
  subst e2
  refine XV.mono (XV.sop2 hL (x := P + 1) (a := u + 1) (b := u) (by omega) (by omega) (by omega) .add
    (by intro h; cases h) (by simp; rw [if_neg (by omega), c1 _ (by omega), o1]; exact h1)
    (by simp; rw [if_neg (by omega), c1 _ (by omega), z]; exact h0)
    (by simp [RealRAM.Op2.eval]; rw [if_neg (by omega), if_neg (by omega), c1 _ (by omega), c1 _ (by omega), o1, z];
        simpa using h1)) le_rfl fun σ3 e3 => ?_
  subst e3
  refine ⟨⟨?_, fun k => ?_, ?_⟩, by simp [d1], ?_⟩
  · simp [RealRAM.Op2.eval]; rw [if_neg (by omega), if_neg (by omega), c1 _ (by omega), c1 _ (by omega), o1, z]; simp
  · simp only [Env.setSc_arr]; exact m1 k
  · simp [RealRAM.Op2.eval]; rw [c1 _ (by omega), c1 _ (by omega), hV, z]; simp
  · have G : FrameA (fun y => y = P + 1 ∨ y = P + 2 ∨ u + 24 ≤ y) (fun j => j = n0 + 1 ∨ j = n0 + 2)
        (fun b c => b = a0 + 6 ∧ c < d) σ σ1 := F1.mono (fun y h => Or.inr (Or.inr h)) (fun j h => h) (fun b c h => h)
    exact (G.setSc (Or.inr (Or.inl rfl)) _).setSc (Or.inl rfl) _

set_option maxHeartbeats 4000000 in
/-- The kept point on the machine: replaced by `(a, V)` when there is none or when `V` is smaller. -/
theorem XV.keep {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk} {I : EllI d}
    {nS nN nA s P u a0 kb n0 one nm F G : ℕ} {a : Fin d → ℤ} {V : ℤ} {kept : Option ((Fin d → ℤ) × ℤ)}
    (hB : B.OK L nS nN nA) (lay : TestLay L B P u a0 kb n0 one nm) (hT : TestEnv B I s P u one σ)
    (hK : KeptIn P kb kept σ) (bW : ∀ b W, kept = some (b, W) → |W| ≤ 2 ^ G)
    (ha : ∀ k : Fin d, σ.arr (a0 + 1) k = a k) (ba : ∀ k, |a k| ≤ 2 ^ F) (hV : σ.sc (u + 15) = V)
    (bV : |V| ≤ 2 ^ G) (hG : G < ℓ) (hℓ : 64 * F + 16 < ℓ) :
    XRunsB L X ℓa ℓ (xkeep L B P u a0 kb n0 one) σ ((1 + (d * (2 + 6) + 3)) + (1 + 1) + 3) (fun σ' =>
      KeptIn P kb (newKept a V kept) σ' ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = P + 1 ∨ y = P + 2 ∨ u + 24 ≤ y) (fun j => j = n0 + 1 ∨ j = n0 + 2)
        (fun b c => b = kb ∧ c < d) σ σ') := by
  have lay' := lay
  obtain ⟨oP, Pu, uS, -, -, -, -, -, -, -⟩ := lay'
  have hT' := hT
  obtain ⟨-, z, -, -, -, -, -, -⟩ := hT'
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by simp only [abs_zero]; positivity
  have h1 : |(1 : ℝ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  have bV' : |σ.sc (u + 15)| < 2 ^ ℓ := by rw [hV]; exact absR_lt bV hG
  have hNew := XV.keepNew (X := X) hL hB lay hT ha ba hV (absR_lt bV hG) hℓ
  cases kept with
  | none =>
    have hc : ¬ σ.sc u < σ.sc (P + 1) := by rw [z, hK]; simp
    exact XV.mono (XV.ifS_f hL (by omega) (by omega) (by rw [z]; exact h0) (by rw [hK]; exact h0) hc hNew)
      (by omega) fun σ' h => h
  | some bW' =>
    obtain ⟨b, W⟩ := bW'
    obtain ⟨k1, kb1, kW⟩ := hK
    have hc : σ.sc u < σ.sc (P + 1) := by rw [z, k1]; norm_num
    have bW2 : |σ.sc (P + 2)| < 2 ^ ℓ := by rw [kW]; exact absR_lt (bW b W rfl) hG
    by_cases hVW : V < W
    · have hc2 : σ.sc (u + 15) < σ.sc (P + 2) := by rw [hV, kW]; exact_mod_cast hVW
      refine XV.mono (XV.ifS_t hL (by omega) (by omega) (by rw [z]; exact h0) (by rw [k1]; exact h1) hc
        (XV.ifS_t hL (by omega) (by omega) bV' bW2 hc2 hNew)) (by omega) fun σ' h => ?_
      simpa [newKept, hVW] using h
    · have hc2 : ¬ σ.sc (u + 15) < σ.sc (P + 2) := by rw [hV, kW]; exact_mod_cast hVW
      refine XV.mono (XV.ifS_t hL (by omega) (by omega) (by rw [z]; exact h0) (by rw [k1]; exact h1) hc
        (XV.ifS_f hL (by omega) (by omega) bV' bW2 hc2 (XV.skip σ))) (by omega) fun σ' h => ?_
      rw [h]
      exact ⟨by simpa [newKept, hVW] using (show KeptIn P kb (some (b, W)) σ from ⟨k1, kb1, kW⟩), rfl,
        FrameA.refl _ _ _ σ⟩

set_option maxHeartbeats 4000000 in
/-- The end of (T4) on the machine: the outcome `1` (return) into `P` when the gradient `c` in the array `a0 + 2` is
`0`, else `0` (cut). -/
theorem XV.testEnd {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk} {I : EllI d}
    {nS nN nA s P u a0 kb n0 one nm G : ℕ} {c : Fin d → ℤ} (hB : B.OK L nS nN nA)
    (lay : TestLay L B P u a0 kb n0 one nm) (hT : TestEnv B I s P u one σ)
    (hc : ∀ k : Fin d, σ.arr (a0 + 2) k = c k) (bc : ∀ k, |c k| ≤ 2 ^ G) (hG : 2 * G < ℓ) :
    XRunsB L X ℓa ℓ (xtestEnd L B P u a0 n0 one) σ (1 + ((1 + (d * (1 + 5 + 6) + 3)) + (1 + 2))) (fun σ' =>
      (c = 0 → σ'.sc P = 1) ∧ (c ≠ 0 → σ'.sc P = 0) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = P ∨ u + 16 ≤ y) (fun j => j = n0 + 1 ∨ j = n0 + 2) (fun _ _ => False) σ σ') := by
  obtain ⟨-, -, -, hrd, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hB
  obtain ⟨oP, Pu, uS, wa, -, aA, rn, onee, -, nN⟩ := lay
  subst onee
  obtain ⟨⟨e1, -, -, -, -, -, -, -, -, -, -, -, -, -⟩, z, o1, n1, -, -, -, -⟩ := hT
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by simp only [abs_zero]; positivity
  have h1 : |(1 : ℝ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  have hda := asz_lt hL (show a0 + 2 < L.NA by omega)
  have hdl : d < 2 ^ ℓa := by unfold asz at hda; nlinarith
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  have hcd : ∀ k < d, k < asz d := fun k hk => by unfold asz; nlinarith
  -- `u + 16 := 0`
  refine XV.seq (XV.sop2 hL (x := u + 16) (a := u) (b := u) (by omega) (by omega) (by omega) .add
    (by intro h; cases h) (by rw [z]; exact h0) (by rw [z]; exact h0)
    (by simp only [RealRAM.Op2.eval, z, add_zero]; exact h0)) fun σ1 e1' => ?_
  subst e1'
  set σ1 := σ.setSc (u + 16) (RealRAM.Op2.eval .add (σ.sc u) (σ.sc u)) with hσ1
  have z1 : σ1.sc u = 0 := by simp [hσ1, z]
  have o11 : σ1.sc (u + 1) = 1 := by simp [hσ1, o1]
  have f1 : σ1.sc (u + 16) = 0 := by simp [hσ1, RealRAM.Op2.eval, z]
  -- the scan
  refine XV.seq (Q₁ := fun σ' => ((∃ k < d, (0 : ℤ) < vext c k * vext c k) → σ'.sc (u + 16) = 1) ∧
      ((∀ k < d, ¬ (0 : ℤ) < vext c k * vext c k) → σ'.sc (u + 16) = (σ1.setNat (n0 + 1) 0).sc (u + 16)) ∧
      σ'.nat (n0 + 1) = 0 + 1 * d ∧ σ'.draws = (σ1.setNat (n0 + 1) 0).draws ∧
      FrameA (fun y => y = u + 16 ∨ u + 24 ≤ y) (fun j => j = n0 + 2 ∨ j = n0 + 1) (fun _ _ => False)
        (σ1.setNat (n0 + 1) 0) σ')
    (XV.seq (XV.nconst hL (i := n0 + 1) (by omega) 0 (by positivity)) fun σ0 e0 => ?_)
    fun σ2 ⟨y2, n2, _, d2, F2⟩ => ?_
  · subst e0
    refine XV.anyE (E := G) (N := d) (base := 0) (st := 1) (F1 := fun _ => 0) (F2 := fun k => vext c k * vext c k)
      hL (z := u) (f := u + 16) (one := u + 1) (t := u + 24) (e1 := .sc u)
      (e2 := .op .mul (.arr (a0 + 2) (n0 + 2)) (.arr (a0 + 2) (n0 + 2))) (nr := n0 + 1) (nst := n0 + 4)
      (nk := n0 + 2) (nn := B.rd) (none := n0 + 4) (by simp only [IE.WF]; omega)
      (by simp only [IE.WF]; exact ⟨(by intro h; cases h), ⟨by omega, by omega⟩, by omega, by omega⟩)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by simp only [IE.scr]; omega)
      (by simp only [IE.scr]; omega) (by simpa using z1) (by simpa using o11) (by omega) (by omega) (by omega)
      (by omega) (by omega) (nodup4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) (by omega)
      (by omega) (by simp [hσ1, show B.rd ≠ n0 + 1 by omega, e1])
      (by simpa [hσ1] using n1) (by simp) (by simpa [hσ1] using n1) hdl
      (by simpa using hdl) hsa (by simp only [IE.top]; omega) (by simp only [IE.top, IE.mag]; omega) ?_
    intro k hk σ' hF hd hkt hkr
    have ec : σ'.arr (a0 + 2) k = c ⟨k, hk⟩ := by
      rw [hF.2.2.1 _ _ (fun h => h.elim), Env.setNat_arr]; exact hc ⟨k, hk⟩
    have ez : σ'.sc u = 0 := by rw [hF.2.1 _ (by omega), Env.setNat_sc, z1]
    simp only [IE.Leaves, IE.eval, RealRAM.Op2.eval, hkt, ec, ez]
    refine ⟨⟨⟨0, by simp, by simp⟩, by simp⟩, ⟨⟨hcd k hk, _, rfl, bc _⟩, hcd k hk, _, rfl, bc _⟩, ?_⟩
    rw [vext_lt _ hk]; push_cast; ring
  -- the outcome
  have z2 : σ2.sc u = 0 := by rw [F2.2.1 _ (by omega), Env.setNat_sc, z1]
  have o2 : σ2.sc (u + 1) = 1 := by rw [F2.2.1 _ (by omega), Env.setNat_sc, o11]
  have G2 : FrameA (fun y => y = P ∨ u + 16 ≤ y) (fun j => j = n0 + 1 ∨ j = n0 + 2) (fun _ _ => False) σ σ2 :=
    ((((FrameA.refl _ _ _ σ).setSc (Or.inr le_rfl) _)).setNat (Or.inl rfl) 0).trans
      (F2.mono (fun y h => by rcases h with h | h <;> omega) (fun j h => by rcases h with h | h <;> omega)
        (fun _ _ h => h))
  have hiff : c ≠ 0 ↔ ∃ k < d, (0 : ℤ) < vext c k * vext c k := by
    constructor
    · intro hne
      obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
      exact ⟨k, k.2, by simp only [vext_lt _ k.2]; exact mul_self_pos.2 hk⟩
    · rintro ⟨k, hk, hlt⟩ h0'
      simp only [vext_lt _ hk, h0', Pi.zero_apply, mul_zero, lt_self_iff_false] at hlt
  by_cases hc0 : c = 0
  · have hall : ∀ k < d, ¬ (0 : ℤ) < vext c k * vext c k := by
      intro k hk hlt; exact (hiff.2 ⟨k, hk, hlt⟩) hc0
    have f2 : σ2.sc (u + 16) = 0 := by rw [n2 hall, Env.setNat_sc, f1]
    refine XV.mono (XV.ifS_f hL (by omega) (by omega) (by rw [z2]; exact h0) (by rw [f2]; exact h0)
      (by rw [z2, f2]; exact lt_irrefl 0) (XV.sop2 hL (x := P) (a := u + 1) (b := u) (by omega) (by omega)
      (by omega) .add (by intro h; cases h) (by rw [o2]; exact h1) (by rw [z2]; exact h0)
      (by simp only [RealRAM.Op2.eval, o2, z2, add_zero]; exact h1))) le_rfl fun σ3 e3 => ?_
    subst e3
    refine ⟨fun _ => by simp [RealRAM.Op2.eval, o2, z2], fun h => absurd hc0 h, by simp [d2, hσ1], ?_⟩
    exact G2.setSc (Or.inl rfl) _
  · have f2 : σ2.sc (u + 16) = 1 := y2 (hiff.1 hc0)
    refine XV.mono (XV.ifS_t hL (by omega) (by omega) (by rw [z2]; exact h0) (by rw [f2]; exact h1)
      (by rw [z2, f2]; exact zero_lt_one) (XV.sop2 hL (x := P) (a := u) (b := u) (by omega) (by omega)
      (by omega) .add (by intro h; cases h) (by rw [z2]; exact h0) (by rw [z2]; exact h0)
      (by simp only [RealRAM.Op2.eval, z2, add_zero]; exact h0))) (by omega) fun σ3 e3 => ?_
    subst e3
    refine ⟨fun h => absurd h hc0, fun _ => by simp [RealRAM.Op2.eval, z2], by simp [d2, hσ1], ?_⟩
    exact G2.setSc (Or.inl rfl) _

/-! ## The tests of one iteration -/

theorem KeptIn.frame {P kb : ℕ} {kept : Option ((Fin d → ℤ) × ℤ)} {σ σ' : Env d} (h : KeptIn P kb kept σ)
    (h1 : σ'.sc (P + 1) = σ.sc (P + 1)) (h2 : σ'.sc (P + 2) = σ.sc (P + 2))
    (hk : ∀ k, σ'.arr kb k = σ.arr kb k) : KeptIn P kb kept σ' := by
  cases kept with
  | none => exact h1.trans h
  | some bW =>
    obtain ⟨b, W⟩ := bW
    obtain ⟨k1, kb1, kW⟩ := h
    exact ⟨h1.trans k1, fun k => (hk k).trans (kb1 k), h2.trans kW⟩

/-- `ellTest` when the ball, the rows and the quadratic constraint pass. -/
theorem ellTest_T4 {I : EllI d} {s : ℕ} {a : Fin d → ℤ} {kept : Option ((Fin d → ℤ) × ℤ)}
    (h1 : ¬ 2 ^ (2 * s) * I.R.num ^ 2 < (a ⬝ᵥ a) * (I.R.den : ℤ) ^ 2)
    (h2 : (List.finRange I.m).find? (fun i => decide (2 ^ s * I.β i < I.α i ⬝ᵥ a)) = none)
    (h3 : ¬ 2 ^ (2 * s + 1) * I.ℓ < a ⬝ᵥ (I.H *ᵥ a) - 2 ^ (s + 1) * (I.g ⬝ᵥ a)) :
    ellTest I s a kept =
      if I.P *ᵥ ((I.Df : ℤ) • a) - (2 ^ s : ℤ) • I.f = 0 then .ret a else
        .cut (I.P *ᵥ ((I.Df : ℤ) • a) - (2 ^ s : ℤ) • I.f)
          (newKept a ((I.Df : ℤ) * (a ⬝ᵥ (I.P *ᵥ a)) - 2 ^ (s + 1) * (I.f ⬝ᵥ a)) kept) := by
  unfold ellTest
  rw [if_neg h1, h2]
  simp only [if_neg h3]
  cases kept with
  | none => rfl
  | some bW => obtain ⟨b, W⟩ := bW; rfl

/-- The units of the pieces of `xtest`: (T1), (T2), (T3), (T4), the kept point, the end of (T4). -/
def tKA (d : ℕ) : ℕ := d * 10 + 5 + (5 + 5)
def tKR (d m Kr : ℕ) : ℕ := 4 + (m * (Kr + d * 20 + 20) + 2)
def tKQ (d : ℕ) : ℕ := d * (d * 10 + 9) + 4 + (d * 10 + 5 + (d * 10 + 5 + (3 + 5)))
def tKV (d : ℕ) : ℕ := d * (d * 10 + 9) + 4 + (1 + ((d * (9 + 6) + 3) + (d * 10 + 5 + (d * 10 + 5 + 7))))
def tKK (d : ℕ) : ℕ := (1 + (d * (2 + 6) + 3)) + (1 + 1) + 3
def tKE (d : ℕ) : ℕ := 1 + ((1 + (d * (1 + 5 + 6) + 3)) + (1 + 2))
def tE3 (d : ℕ) : ℕ := tKV d + (tKK d + tKE d)
def tE2 (d : ℕ) : ℕ := tKQ d + (tE3 d + 2)
def tE1 (d m Kr : ℕ) : ℕ := tKR d m Kr + (tE2 d + 2)
/-- The units of `xtest`. -/
def testK (d m Kr : ℕ) : ℕ := tKA d + (tE1 d m Kr + 2)

set_option maxHeartbeats 16000000 in
/-- **The tests of one iteration on the machine**: `xtest` computes `ellTest I s a kept`, the point `a` in the array
`a0 + 1`, the kept point in `P + 1`, `P + 2`, `kb` (values below `2^{6F+1}`). -/
theorem XV.test {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk} {I : EllI d}
    {nS nN nA s P u a0 kb n0 one nm F Kr : ℕ} {rowc : XCmd} {Ctx : Env d → Prop} {SR NR AR : ℕ → Prop}
    {a : Fin d → ℤ} {kept : Option ((Fin d → ℤ) × ℤ)} (hB : B.OK L nS nN nA) (hav : B.Avoid SR NR AR)
    (hrow : RowProv L X ℓa ℓ I B rowc Ctx SR NR AR Kr) (hctx : CtxOK B Ctx SR NR AR)
    (lay : TestLay L B P u a0 kb n0 one nm) (hT : TestEnv B I s P u one σ) (hC : Ctx σ)
    (hK : KeptIn P kb kept σ) (bW : ∀ b W, kept = some (b, W) → |W| ≤ 2 ^ (6 * F + 1))
    (ha : ∀ k : Fin d, σ.arr (a0 + 1) k = a k) (ba : ∀ k, |a k| ≤ 2 ^ F) (hσF : ellSz I ≤ F)
    (hsF : 2 * s + 1 ≤ F) (hdF : d ≤ F) (hm : I.m < 2 ^ ℓa) (hℓ : 64 * F + 16 < ℓ) :
    XRunsB L X ℓa ℓ (xtest L B rowc P u a0 kb n0 one nm) σ (testK d I.m Kr) (fun σ' =>
      TestOut P a0 kb (ellTest I s a kept) σ' ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = P ∨ y = P + 1 ∨ y = P + 2 ∨ y = P + 7 ∨ u + 13 ≤ y ∨ y = B.o + 2 ∨ SR y)
        (fun j => j = B.rE ∨ (n0 ≤ j ∧ j ≤ n0 + 2) ∨ j = n0 + 5 ∨ NR j)
        (fun b _ => b = B.aW + 1 ∨ b = a0 + 2 ∨ b = a0 + 3 ∨ b = kb ∨ AR b) σ σ') := by
  have hrow' := hrow
  obtain ⟨hsr, hnr, har, -⟩ := hrow'
  have lay' := lay
  obtain ⟨oP, Pu, uS, wa, kbe, aA, rn, onee, nme, nN⟩ := lay'
  have hB' := hB
  obtain ⟨-, -, -, hrd, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hB'
  have hT' := hT
  obtain ⟨-, z, o1, -, -, -, -, -⟩ := hT'
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by simp only [abs_zero]; positivity
  have h1 : |(1 : ℝ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  -- the frames
  let S0 : ℕ → Prop := fun y => y = P ∨ y = P + 7 ∨ u + 13 ≤ y ∨ y = B.o + 2 ∨ SR y
  let N0 : ℕ → Prop := fun j => j = B.rE ∨ (n0 ≤ j ∧ j ≤ n0 + 2) ∨ j = n0 + 5 ∨ NR j
  let A0 : ℕ → ℕ → Prop := fun b _ => b = B.aW + 1 ∨ b = a0 + 2 ∨ b = a0 + 3 ∨ AR b
  have hS0 : ∀ y, S0 y → (B.o ≤ y ∧ y ≠ u ∧ y ≠ u + 1 ∧ (y < P + 3 ∨ P + 6 < y)) ∨ SR y := fun y h => by
    rcases h with h | h | h | h | h
    · left; omega
    · left; omega
    · left; omega
    · left; omega
    · right; exact h
  have hN0 : ∀ j, N0 j → (B.rE ≤ j ∧ j ≠ one) ∨ NR j := fun j h => by
    rcases h with h | h | h | h
    · left; omega
    · left; omega
    · left; omega
    · right; exact h
  have hA0 : ∀ b k, A0 b k → B.aW ≤ b ∨ AR b := fun b k h => by
    rcases h with h | h | h | h
    · left; omega
    · left; omega
    · left; omega
    · right; exact h
  have hT0 : ∀ σ', FrameA S0 N0 A0 σ σ' → TestEnv B I s P u one σ' := fun σ' hF =>
    TestEnv.frame hB hav hsr hnr har (by omega) (by omega) (by omega) hT hF hS0 hN0 hA0
  have hC0 : ∀ σ', σ'.draws = σ.draws → FrameA S0 N0 A0 σ σ' → Ctx σ' := fun σ' hd hF =>
    hctx σ σ' hC hd (hF.mono (fun y h => by
      rcases hS0 y h with h | h
      · exact Or.inl h.1
      · exact Or.inr h) (fun j h => by
      rcases hN0 j h with h | h
      · exact Or.inl h.1
      · exact Or.inr h) hA0)
  have ha0 : ∀ σ', FrameA S0 N0 A0 σ σ' → ∀ k : Fin d, σ'.arr (a0 + 1) k = a k := fun σ' hF k => by
    rw [hF.2.2.1 _ _ (fun h => by
      rcases h with h | h | h | h
      · omega
      · omega
      · omega
      · exact absurd (har _ h) (by omega)), ha]
  have hK0 : ∀ σ', FrameA S0 N0 A0 σ σ' → KeptIn P kb kept σ' := fun σ' hF =>
    hK.frame (hF.2.1 _ (fun h => by
      rcases h with h | h | h | h | h
      · omega
      · omega
      · omega
      · omega
      · exact absurd (hsr _ h) (by omega))) (hF.2.1 _ (fun h => by
      rcases h with h | h | h | h | h
      · omega
      · omega
      · omega
      · omega
      · exact absurd (hsr _ h) (by omega))) (fun k => hF.2.2.1 _ _ (fun h => by
      rcases h with h | h | h | h
      · omega
      · omega
      · omega
      · exact absurd (har _ h) (by omega)))
  have hfin : ∀ σ', FrameA S0 N0 A0 σ σ' →
      FrameA (fun y => y = P ∨ y = P + 1 ∨ y = P + 2 ∨ y = P + 7 ∨ u + 13 ≤ y ∨ y = B.o + 2 ∨ SR y)
        (fun j => j = B.rE ∨ (n0 ≤ j ∧ j ≤ n0 + 2) ∨ j = n0 + 5 ∨ NR j)
        (fun b _ => b = B.aW + 1 ∨ b = a0 + 2 ∨ b = a0 + 3 ∨ b = kb ∨ AR b) σ σ' := fun σ' hF =>
    hF.mono (fun y h => by
      rcases h with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))) (fun j h => h) (fun b k h => by
      rcases h with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
  -- bounds
  obtain ⟨-, -, -, -, -, -, -, -, mRn, mRd, -, -, -, -⟩ := ellMx_le I
  have bRn : |I.R.num| ≤ 2 ^ F := (abs_le_sz mRn).trans (pow_le_pow_right₀ (by norm_num) hσF)
  have bRd : |(I.R.den : ℤ)| ≤ 2 ^ F := (abs_le_sz' mRd).trans (pow_le_pow_right₀ (by norm_num) hσF)
  have bv : ∀ k, |(I.H *ᵥ a) k| ≤ 2 ^ (3 * F) := fun k =>
    abs_le_pow_mono (abs_mulVec_le' hdF (ellH_le hσF) ba k) (by omega)
  have bw : ∀ k, |(I.P *ᵥ a) k| ≤ 2 ^ (3 * F) := fun k =>
    abs_le_pow_mono (abs_mulVec_le' hdF (ellP_le hσF) ba k) (by omega)
  -- (T1)
  refine XV.seq (XV.testA (X := X) hL hB lay hT ha ba hσF hsF hdF hℓ) fun σ1 ⟨t13, t14, t15, d1, F1⟩ => ?_
  have G1 : FrameA S0 N0 A0 σ σ1 :=
    F1.mono (fun y h => Or.inr (Or.inr (Or.inl h))) (fun j h => by
      rcases h with h | h
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inl (by omega))) (fun _ _ h => h.elim)
  have b14 : |2 ^ (2 * s) * I.R.num ^ 2| ≤ 2 ^ (F + (F + F)) :=
    abs_mul_le_pow (abs_pow_le (by omega)) (by rw [pow_two]; exact abs_mul_le_pow bRn bRn)
  have b15 : |(a ⬝ᵥ a) * (I.R.den : ℤ) ^ 2| ≤ 2 ^ (F + (F + F) + (F + F)) :=
    abs_mul_le_pow (abs_dot_le' hdF ba ba) (by rw [pow_two]; exact abs_mul_le_pow bRd bRd)
  have v14 : |σ1.sc (u + 14)| < 2 ^ ℓ := by rw [t14]; exact absR_lt b14 (by omega)
  have v15 : |σ1.sc (u + 15)| < 2 ^ ℓ := by rw [t15]; exact absR_lt b15 (by omega)
  by_cases c1 : 2 ^ (2 * s) * I.R.num ^ 2 < (a ⬝ᵥ a) * (I.R.den : ℤ) ^ 2
  · -- the ball: cut with `a`
    have hc : σ1.sc (u + 14) < σ1.sc (u + 15) := by rw [t14, t15]; exact_mod_cast c1
    have hT1 := hT0 σ1 G1
    obtain ⟨⟨e1, -, -, -, -, -, -, -, -, -, -, -, -, -⟩, z1, -, n1, -, -, -, -⟩ := hT1
    subst onee
    refine XV.mono (XV.ifS_t hL (by omega) (by omega) v14 v15 hc (XV.seq (K₂ := 1) (XV.copy (E := F) (x := a) hL
      (B := B) (u := u) (src := a0 + 1) (dst := a0 + 2) (n0 := n0) (one := n0 + 4) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) z1 e1 n1
      (ha0 σ1 G1) ba (by omega)) fun σ2 ⟨m2, d2, F2⟩ => ?_)) (K' := tE1 d I.m Kr + 2)
      (by unfold tE1 tKR tE2 tKQ tE3 tKV tKK tKE; ring_nf; omega) fun _ h => h
    have G2 : FrameA S0 N0 A0 σ σ2 := G1.trans (F2.mono (fun y h => Or.inr (Or.inr (Or.inl (by omega))))
      (fun j h => by
        rcases h with h | h
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inl (by omega))) (fun b c h => Or.inr (Or.inl h.1)))
    have z2 : σ2.sc u = 0 := by rw [F2.2.1 _ (by omega), z1]
    refine XV.mono (XV.sop2 hL (x := P) (a := u) (b := u) (by omega) (by omega) (by omega) .add
      (by intro h; cases h) (by rw [z2]; exact h0) (by rw [z2]; exact h0)
      (by simp only [RealRAM.Op2.eval, z2, add_zero]; exact h0)) le_rfl fun σ3 e3 => ?_
    subst e3
    have G3 : FrameA S0 N0 A0 σ _ := G2.setSc (Or.inl rfl) (RealRAM.Op2.eval .add (σ2.sc u) (σ2.sc u))
    have e : ellTest I s a kept = .cut a kept := by unfold ellTest; rw [if_pos c1]
    rw [e]
    refine ⟨⟨by simp [RealRAM.Op2.eval, z2], fun k => by simp only [Env.setSc_arr]; exact m2 k, hK0 _ G3⟩,
      by simp [d2, d1], hfin _ G3⟩
  · -- (T2)
    have hc : ¬ σ1.sc (u + 14) < σ1.sc (u + 15) := by rw [t14, t15]; exact_mod_cast c1
    refine XV.ifS_f hL (by omega) (by omega) v14 v15 hc ?_
    refine XV.seq (XV.rows (X := X) hL hB hav hrow hctx lay (hT0 σ1 G1) (hC0 σ1 d1 G1) (ha0 σ1 G1) ba hσF
      (by omega) hdF hm hℓ) fun σ2 ⟨r2, d2, F2⟩ => ?_
    have G2 : FrameA S0 N0 A0 σ σ2 := G1.trans (F2.mono (fun y h => by
      rcases h with h | h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))) (fun j h => by
      rcases h with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))) (fun b k h => by
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))))
    have hT2 := hT0 σ2 G2
    obtain ⟨-, z2, -, -, -, -, -, -⟩ := hT2
    unfold RowsOut at r2
    cases hf : (List.finRange I.m).find? (fun i => decide (2 ^ s * I.β i < I.α i ⬝ᵥ a)) with
    | some i =>
      rw [hf] at r2
      obtain ⟨f2, c2⟩ := r2
      have hc2 : σ2.sc u < σ2.sc (P + 7) := by rw [z2, f2]; norm_num
      refine XV.mono (XV.ifS_t hL (by omega) (by omega) (by rw [z2]; exact h0) (by rw [f2]; exact h1) hc2
        (XV.sop2 hL (x := P) (a := u) (b := u) (by omega) (by omega) (by omega) .add
        (by intro h; cases h) (by rw [z2]; exact h0) (by rw [z2]; exact h0)
        (by simp only [RealRAM.Op2.eval, z2, add_zero]; exact h0)))
        (K' := tE2 d + 2)
        (by unfold tE2 tKQ tE3 tKV tKK tKE; ring_nf; omega) fun σ3 e3 => ?_
      subst e3
      have G3 : FrameA S0 N0 A0 σ _ := G2.setSc (Or.inl rfl) (RealRAM.Op2.eval .add (σ2.sc u) (σ2.sc u))
      have e : ellTest I s a kept = .cut (I.α i) kept := by unfold ellTest; rw [if_neg c1, hf]
      rw [e]
      refine ⟨⟨by simp [RealRAM.Op2.eval, z2], fun k => by simp only [Env.setSc_arr]; exact c2 k, hK0 _ G3⟩,
        by simp [d2, d1], hfin _ G3⟩
    | none =>
      rw [hf] at r2
      have hc2 : ¬ σ2.sc u < σ2.sc (P + 7) := by rw [z2, r2]; exact lt_irrefl 0
      refine XV.mono (XV.ifS_f hL (by omega) (by omega) (by rw [z2]; exact h0) (by rw [r2]; exact h0) hc2 ?_)
        le_rfl fun _ h => h
      -- (T3)
      refine XV.seq (XV.testQ (X := X) hL hB lay (hT0 σ2 G2) (ha0 σ2 G2) ba hσF hsF hdF hℓ)
        fun σ3 ⟨q15, q16, q3, d3, F3⟩ => ?_
      have G3 : FrameA S0 N0 A0 σ σ3 := G2.trans (F3.mono (fun y h => Or.inr (Or.inr (Or.inl h)))
        (fun j h => Or.inr (Or.inl h)) (fun b c h => Or.inr (Or.inr (Or.inl h.1))))
      have b15' : |2 ^ (2 * s + 1) * I.ℓ| ≤ 2 ^ (F + F) := abs_mul_le_pow (abs_pow_le (by omega)) (ellL_le hσF)
      have b16 : |a ⬝ᵥ (I.H *ᵥ a) - 2 ^ (s + 1) * (I.g ⬝ᵥ a)| ≤ 2 ^ (5 * F + 1) :=
        abs_sub_le_pow (abs_le_pow_mono (abs_dot_le' hdF ba bv) (by omega))
          (abs_le_pow_mono (abs_mul_le_pow (abs_pow_le (show s + 1 ≤ F by omega))
            (abs_dot_le' hdF (ellG_le hσF) ba)) (by omega))
      have v15' : |σ3.sc (u + 15)| < 2 ^ ℓ := by rw [q15]; exact absR_lt b15' (by omega)
      have v16 : |σ3.sc (u + 16)| < 2 ^ ℓ := by rw [q16]; exact absR_lt b16 (by omega)
      by_cases c3 : 2 ^ (2 * s + 1) * I.ℓ < a ⬝ᵥ (I.H *ᵥ a) - 2 ^ (s + 1) * (I.g ⬝ᵥ a)
      · -- the quadratic constraint: cut with `H a - 2^s g`
        have hc3 : σ3.sc (u + 15) < σ3.sc (u + 16) := by rw [q15, q16]; exact_mod_cast c3
        refine XV.mono (XV.ifS_t hL (by omega) (by omega) v15' v16 hc3 (XV.seq (K₂ := 1) (XV.cutQ (X := X) (v := I.H *ᵥ a)
          hL hB lay (hT0 σ3 G3) q3 bv hσF hsF hℓ) fun σ4 ⟨m4, d4, F4⟩ => ?_))
          (K' := tE3 d + 2)
          (by unfold tE3 tKV tKK tKE; ring_nf; omega) fun _ h => h
        have G4 : FrameA S0 N0 A0 σ σ4 := G3.trans (F4.mono (fun y h => Or.inr (Or.inr (Or.inl (by omega))))
          (fun j h => by
            rcases h with h | h
            · exact Or.inr (Or.inl (by omega))
            · exact Or.inr (Or.inl (by omega))) (fun b c h => Or.inr (Or.inl h.1)))
        have hT4 := hT0 σ4 G4
        obtain ⟨-, z4, -, -, -, -, -, -⟩ := hT4
        refine XV.mono (XV.sop2 hL (x := P) (a := u) (b := u) (by omega) (by omega) (by omega) .add
          (by intro h; cases h) (by rw [z4]; exact h0) (by rw [z4]; exact h0)
          (by simp only [RealRAM.Op2.eval, z4, add_zero]; exact h0)) le_rfl fun σ5 e5 => ?_
        subst e5
        have G5 : FrameA S0 N0 A0 σ _ := G4.setSc (Or.inl rfl) (RealRAM.Op2.eval .add (σ4.sc u) (σ4.sc u))
        have e : ellTest I s a kept = .cut (I.H *ᵥ a - (2 ^ s : ℤ) • I.g) kept := by
          unfold ellTest; rw [if_neg c1, hf, if_pos c3]
        rw [e]
        refine ⟨⟨by simp [RealRAM.Op2.eval, z4], fun k => by simp only [Env.setSc_arr]; exact m4 k, hK0 _ G5⟩,
          by simp [d4, d3, d2, d1], hfin _ G5⟩
      · -- (T4)
        have hc3 : ¬ σ3.sc (u + 15) < σ3.sc (u + 16) := by rw [q15, q16]; exact_mod_cast c3
        refine XV.ifS_f hL (by omega) (by omega) v15' v16 hc3 ?_
        refine XV.seq (XV.testV (X := X) hL hB lay (hT0 σ3 G3) (ha0 σ3 G3) ba hσF hsF hdF hℓ)
          fun σ4 ⟨g4, V4, d4, F4⟩ => ?_
        have G4 : FrameA S0 N0 A0 σ σ4 := G3.trans (F4.mono (fun y h => Or.inr (Or.inr (Or.inl h)))
          (fun j h => Or.inr (Or.inl h)) (fun b c h => by
            rcases h.1 with h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inl h))))
        have bV : |(I.Df : ℤ) * (a ⬝ᵥ (I.P *ᵥ a)) - 2 ^ (s + 1) * (I.f ⬝ᵥ a)| ≤ 2 ^ (6 * F + 1) :=
          abs_sub_le_pow (abs_le_pow_mono (abs_mul_le_pow (ellDf_le hσF) (abs_dot_le' hdF ba bw)) (by omega))
            (abs_le_pow_mono (abs_mul_le_pow (abs_pow_le (show s + 1 ≤ F by omega))
              (abs_dot_le' hdF (ellF_le hσF) ba)) (by omega))
        refine XV.seq (XV.keep (X := X) (G := 6 * F + 1) hL hB lay (hT0 σ4 G4) (hK0 σ4 G4) bW (ha0 σ4 G4) ba V4 bV
          (by omega) hℓ) fun σ5 ⟨k5, d5, F5⟩ => ?_
        have hT5 : TestEnv B I s P u one σ5 := TestEnv.frame_own hB (by omega) (by omega) (by omega) (hT0 σ4 G4) F5
          (fun y h => by rcases h with h | h | h <;> omega) (fun j h => by rcases h with h | h <;> omega)
          (fun b k h => by omega)
        have bc : ∀ k, |(I.P *ᵥ ((I.Df : ℤ) • a) - (2 ^ s : ℤ) • I.f) k| ≤ 2 ^ (4 * F + 1) := fun k => by
          simp only [Pi.sub_apply, mulVec_smul_int, Pi.smul_apply, smul_eq_mul]
          exact abs_sub_le_pow (abs_le_pow_mono (abs_mul_le_pow (ellDf_le hσF) (bw k)) (by omega))
            (abs_le_pow_mono (abs_mul_le_pow (abs_pow_le (show s ≤ F by omega)) (ellF_le hσF k)) (by omega))
        refine XV.mono (XV.testEnd (X := X) (G := 4 * F + 1) (c := I.P *ᵥ ((I.Df : ℤ) • a) - (2 ^ s : ℤ) • I.f) hL hB
          lay hT5 (fun k => by rw [F5.2.2.1 _ _ (fun h => by omega), g4]) bc (by omega)) le_rfl
          fun σ6 ⟨r6, c6, d6, F6⟩ => ?_
        have G6 : FrameA (fun y => y = P ∨ y = P + 1 ∨ y = P + 2 ∨ y = P + 7 ∨ u + 13 ≤ y ∨ y = B.o + 2 ∨ SR y)
            (fun j => j = B.rE ∨ (n0 ≤ j ∧ j ≤ n0 + 2) ∨ j = n0 + 5 ∨ NR j)
            (fun b _ => b = B.aW + 1 ∨ b = a0 + 2 ∨ b = a0 + 3 ∨ b = kb ∨ AR b) σ σ6 :=
          ((hfin σ4 G4).trans (F5.mono (fun y h => by
            rcases h with h | h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))) (fun j h => by
            rcases h with h | h
            · exact Or.inr (Or.inl (by omega))
            · exact Or.inr (Or.inl (by omega))) (fun b c h => Or.inr (Or.inr (Or.inr (Or.inl h.1)))))).trans
          (F6.mono (fun y h => by
            rcases h with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))) (fun j h => by
            rcases h with h | h
            · exact Or.inr (Or.inl (by omega))
            · exact Or.inr (Or.inl (by omega))) (fun _ _ h => h.elim))
        have hK6 : KeptIn P kb (newKept a ((I.Df : ℤ) * (a ⬝ᵥ (I.P *ᵥ a)) - 2 ^ (s + 1) * (I.f ⬝ᵥ a)) kept) σ6 :=
          k5.frame (F6.2.1 _ (fun h => by rcases h with h | h <;> omega))
            (F6.2.1 _ (fun h => by rcases h with h | h <;> omega)) (fun k => F6.2.2.1 _ _ (fun h => h.elim))
        rw [ellTest_T4 c1 hf c3]
        refine ⟨?_, by rw [d6, d5, d4, d3, d2, d1], G6⟩
        split_ifs with hg
        · exact r6 hg
        · exact ⟨c6 hg, fun k => by rw [F6.2.2.1 _ _ (fun h => h.elim), F5.2.2.1 _ _ (fun h => by omega), g4], hK6⟩

end AdversarialBco.Bit.Transfer
