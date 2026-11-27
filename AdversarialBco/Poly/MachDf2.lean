/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachSI
public import AdversarialBco.Poly.MachMat
public import AdversarialBco.Poly.MachGauge
public import AdversarialBco.Poly.Df2Run
public import AdversarialBco.Poly.MachAPBase

@[expose] public section

/-! # DF2-O in VL

The program of the learner DF2-O (`df2oPlay`, Df2Run.lean) in the variable language, in the layout `df2L`: naturals `0`
to `13` shared (`d, n, 1`, loop counters), `14` to `29` AP, `30` to `49` PG, `50` to `63` DF2; scalars `0` to `2` the
inputs `r₀, R₀, δ`, `3` to `127` DF2 (the parameters in `3` to `18`), `128` to `191` PG, `192` to `319` AP; arrays `0`,
`1` the positioning `μ, A`, `2` to `15` DF2, `16` to `47` AP, `48` to `79` PG, `80` to `95` DF2.

* `df2Params`: the parameters `df2oPar d n δ` into the scalars `3` to `18` and the natural `7`. -/

namespace AdversarialBco.Poly.Mach.VL

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly Matrix

variable {d : ℕ} {w : World d}

/-- The layout of the final program: `64` natural variables, `320` scalars, `96` arrays. -/
def df2L : Layout := ⟨64, 320, 96⟩

/-! ## The parameters -/

open SI in
/-- `δ₁ = min (δ/3) (e⁻¹⁴/(d n)³)` into `3`. -/
def parB3 : List SI :=
  [cast 30 0, cast 31 1, const 32 3, op2 .div 33 2 32, op2 .mul 34 30 31, op2 .mul 35 34 34, op2 .mul 35 35 34,
    const 36 (-14), op1 .exp 36 36, op2 .div 37 36 35, .smin 3 33 37]

open SI in
/-- `δ_e = 4 δ₁/(5 n)` into `4`. -/
def parB4 : List SI := [const 38 4, op2 .mul 39 38 3, cast 31 1, const 40 5, op2 .mul 41 40 31, op2 .div 4 39 41]

open SI in
/-- `L_e = 36 log (1/δ_e)` into `5`. -/
def parB5 : List SI := [const 42 1, op2 .div 43 42 4, op1 .log 43 43, const 44 36, op2 .mul 5 44 43]

open SI in
/-- `λ = 1/(725 d L_e²)` into `6`. -/
def parB6 : List SI :=
  [const 42 1, const 45 725, cast 30 0, op2 .mul 46 45 30, op2 .mul 47 5 5, op2 .mul 46 46 47, op2 .div 6 42 46]

open SI in
/-- `ε = 20 · 725 · d √d L_e⁵/√n` into `10`. -/
def parB10 : List SI :=
  [const 48 20, const 45 725, op2 .mul 48 48 45, cast 30 0, op1 .sqrt 49 30, op2 .mul 50 30 49, op2 .mul 48 48 50,
    op2 .mul 47 5 5, op2 .mul 51 47 47, op2 .mul 51 51 5, op2 .mul 48 48 51, cast 31 1, op1 .sqrt 52 31,
    op2 .div 10 48 52]

open SI in
/-- `R = 134 d √(log (2d + 2))` into `17`. -/
def parB17 : List SI :=
  [const 53 2, cast 30 0, op2 .mul 54 53 30, op2 .add 54 54 53, op1 .log 54 54, op1 .sqrt 54 54, const 55 134,
    op2 .mul 55 55 30, op2 .mul 17 55 54]

open SI in
/-- `η = √d/(L_e √n)` into `7`. -/
def parB7 : List SI := [cast 30 0, op1 .sqrt 49 30, cast 31 1, op1 .sqrt 52 31, op2 .mul 56 5 52, op2 .div 7 49 56]

open SI in
/-- `σ² = 1/(8 L_e)` into `8`. -/
def parB8 : List SI := [const 42 1, const 57 8, op2 .mul 57 57 5, op2 .div 8 42 57]

open SI in
/-- `ρ = 2 · 725 · d² L_e³` into `9`. -/
def parB9 : List SI :=
  [const 53 2, const 45 725, op2 .mul 58 53 45, cast 30 0, op2 .mul 59 30 30, op2 .mul 58 58 59, op2 .mul 47 5 5,
    op2 .mul 60 47 5, op2 .mul 9 58 60]

open SI in
/-- `κ, θ, α, c₁, γ = 1/4, 1, 1/4, 8, 1/100` into `11` to `15`. -/
def parBC : List SI := [const 11 (1 / 4), const 12 1, const 13 (1 / 4), const 14 8, const 15 (1 / 100)]

open SI in
/-- `κ₀ = 1/(1 - λ)²` into `16`. -/
def parB16 : List SI := [const 42 1, op2 .sub 61 42 6, op2 .mul 61 61 61, op2 .div 16 42 61]

open SI in
/-- `s_b = δ_e²/(R (R + 1))` into `18`. -/
def parB18 : List SI := [op2 .mul 62 4 4, const 42 1, op2 .add 63 17 42, op2 .mul 63 17 63, op2 .div 18 62 63]

open SI in
/-- `log₂ (n R (R + 7)/(δ₁ ε))` into `64`. -/
def parB64 : List SI :=
  [const 64 7, op2 .add 64 17 64, op2 .mul 64 17 64, cast 31 1, op2 .mul 64 31 64, op2 .mul 65 3 10,
    op2 .div 64 64 65, op1 .log 64 64, const 53 2, op1 .log 66 53, op2 .div 64 64 66]

section blocks

variable (n : ℕ → ℕ) (f : ℕ → ℝ)

theorem parB3_val : sEval n parB3 f 3 = min (f 2 / 3) (Real.exp (-14) / ((n 0 : ℝ) * n 1) ^ 3) := by
  simp only [sEval, parB3, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval, Op1.eval]
  norm_num
  ring_nf

/-- The tactic of the block values: unfold the block, read the updates, normalize. -/
macro "par_val" : tactic => `(tactic| (
  simp only [sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval, Op1.eval]
  norm_num [df2C0, df2oClam, Real.logb]
  try ring_nf
  try simp))

theorem parB4_val : sEval n parB4 f 4 = 4 * f 3 / (5 * n 1) := by
  simp only [parB4]; par_val

theorem parB5_val : sEval n parB5 f 5 = df2C0 * Real.log (1 / f 4) := by
  simp only [parB5]; par_val

theorem parB6_val : sEval n parB6 f 6 = 1 / (df2oClam * n 0 * f 5 ^ 2) := by
  simp only [parB6]; par_val

theorem parB10_val :
    sEval n parB10 f 10 = 20 * df2oClam * (n 0 * Real.sqrt (n 0)) * f 5 ^ 5 / Real.sqrt (n 1) := by
  simp only [parB10]; par_val

theorem parB17_val : sEval n parB17 f 17 = 134 * n 0 * Real.sqrt (Real.log (2 * n 0 + 2)) := by
  simp only [parB17]; par_val

theorem parB7_val : sEval n parB7 f 7 = Real.sqrt (n 0) / (f 5 * Real.sqrt (n 1)) := by
  simp only [parB7]; par_val

theorem parB8_val : sEval n parB8 f 8 = 1 / (8 * f 5) := by
  simp only [parB8]; par_val

theorem parB9_val : sEval n parB9 f 9 = 2 * df2oClam * (n 0 : ℝ) ^ 2 * f 5 ^ 3 := by
  simp only [parB9]; par_val

theorem parBC_val : sEval n parBC f 11 = 1 / 4 ∧ sEval n parBC f 12 = 1 ∧ sEval n parBC f 13 = 1 / 4 ∧
    sEval n parBC f 14 = 8 ∧ sEval n parBC f 15 = 1 / 100 := by
  simp only [parBC]; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> par_val

theorem parB16_val : sEval n parB16 f 16 = ((1 - f 6) ^ 2)⁻¹ := by
  simp only [parB16]
  simp only [sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval]
  norm_num [sq]

theorem parB18_val : sEval n parB18 f 18 = f 4 ^ 2 / (f 17 * (f 17 + 1)) := by
  simp only [parB18]; par_val

theorem parB64_val : sEval n parB64 f 64 = Real.logb 2 (n 1 * f 17 * (f 17 + 7) / (f 3 * f 10)) := by
  simp only [parB64]; par_val

end blocks
/-- The parameter code before the ceiling. -/
def parSI : List SI :=
  parB3 ++ parB4 ++ parB5 ++ parB6 ++ parB10 ++ parB17 ++ parB7 ++ parB8 ++ parB9 ++ parBC ++ parB16 ++ parB18 ++
    parB64

theorem parSI_val {n : ℕ} {δ : ℝ} (nf : ℕ → ℕ) (f : ℕ → ℝ) (hd : nf 0 = d) (hn : nf 1 = n) (hδ : f 2 = δ) :
    let F := sEval nf parSI f
    let p := df2oPar d n δ
    F 3 = p.δ1 ∧ F 4 = p.δe ∧ F 5 = p.Le ∧ F 6 = p.lam ∧ F 7 = p.eta ∧ F 8 = p.sig2 ∧ F 9 = p.rho ∧
      F 10 = p.eps ∧ F 11 = p.kap ∧ F 12 = p.theta ∧ F 13 = p.alpha ∧ F 14 = p.c1 ∧ F 15 = p.gam ∧ F 16 = p.k0 ∧
      F 17 = p.R ∧ F 18 = p.sb ∧ ⌈F 64⌉₊ = p.j := by
  intro F p
  have e : F = sEval nf parB64 (sEval nf parB18 (sEval nf parB16 (sEval nf parBC (sEval nf parB9 (sEval nf parB8
      (sEval nf parB7 (sEval nf parB17 (sEval nf parB10 (sEval nf parB6 (sEval nf parB5 (sEval nf parB4
        (sEval nf parB3 f)))))))))))) := by
    simp only [F, parSI, sEval_append]
  have hC := parBC_val nf (sEval nf parB9 (sEval nf parB8 (sEval nf parB7 (sEval nf parB17 (sEval nf parB10
    (sEval nf parB6 (sEval nf parB5 (sEval nf parB4 (sEval nf parB3 f)))))))))
  rw [e]
  simp (disch := decide) only [sEval_frame, parB3_val, parB4_val, parB5_val, parB6_val, parB10_val, parB17_val,
    parB7_val, parB8_val, parB9_val, parB16_val, parB18_val, parB64_val, hC, hd, hn, hδ]
  simp only [p, df2oPar, and_self]

theorem sCost_parSI : sCost parSI = 98 := by decide

theorem parSI_ok : parSI.all (SI.ok df2L) = true := by
  simp only [parSI, List.all_append, Bool.and_eq_true]
  decide

/-- The parameter code writes only the scalars `3` to `67`. -/
theorem parSI_dst {x : ℕ} (hx : x < 3 ∨ 67 < x) : x ∉ parSI.map SI.dst := by
  have h : (parSI.map SI.dst).all (fun y => 3 ≤ y && y ≤ 67) = true := by decide
  intro hm
  have := List.all_eq_true.1 h x hm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  omega

/-- The parameters: `1` into the natural `2`, the parameters `df2oPar d n δ` into the scalars `3` to `18` and the
natural `7`; scratch scalars `30` to `67`. -/
def df2Params : Cmd := .seq (nconst 2 1) (.seq (sprog df2L parSI) (nceil df2L 7 2 64 67))

/-- The scalars `3` to `18` and the natural `7` hold the parameters `p`. -/
def ParRep (p : Df2OPar) (σ : Env d) : Prop :=
  σ.sc 3 = p.δ1 ∧ σ.sc 4 = p.δe ∧ σ.sc 5 = p.Le ∧ σ.sc 6 = p.lam ∧ σ.sc 7 = p.eta ∧ σ.sc 8 = p.sig2 ∧
    σ.sc 9 = p.rho ∧ σ.sc 10 = p.eps ∧ σ.sc 11 = p.kap ∧ σ.sc 12 = p.theta ∧ σ.sc 13 = p.alpha ∧
    σ.sc 14 = p.c1 ∧ σ.sc 15 = p.gam ∧ σ.sc 16 = p.k0 ∧ σ.sc 17 = p.R ∧ σ.sc 18 = p.sb ∧ σ.nat 7 = p.j

/-- `ParRep` survives a frame that keeps the natural `7` and the scalars `3` to `18`. -/
theorem ParRep.frame {p : Df2OPar} {σ σ' : Env d} {ns ss as : List ℕ} (h : ParRep p σ)
    (hF : Env.Frame σ σ' ns ss as) (hns : 7 ∉ ns) (hss : ∀ x ∈ ss, x < 3 ∨ 18 < x) : ParRep p σ' := by
  obtain ⟨Fn, Fs, -⟩ := hF
  have e : ∀ x, 3 ≤ x → x ≤ 18 → σ'.sc x = σ.sc x := fun x h1 h2 =>
    Fs x (fun hx => by have := hss x hx; omega)
  obtain ⟨h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, hj⟩ := h
  exact ⟨by rw [e 3 (by norm_num) (by norm_num), h3], by rw [e 4 (by norm_num) (by norm_num), h4],
    by rw [e 5 (by norm_num) (by norm_num), h5], by rw [e 6 (by norm_num) (by norm_num), h6],
    by rw [e 7 (by norm_num) (by norm_num), h7], by rw [e 8 (by norm_num) (by norm_num), h8],
    by rw [e 9 (by norm_num) (by norm_num), h9], by rw [e 10 (by norm_num) (by norm_num), h10],
    by rw [e 11 (by norm_num) (by norm_num), h11], by rw [e 12 (by norm_num) (by norm_num), h12],
    by rw [e 13 (by norm_num) (by norm_num), h13], by rw [e 14 (by norm_num) (by norm_num), h14],
    by rw [e 15 (by norm_num) (by norm_num), h15], by rw [e 16 (by norm_num) (by norm_num), h16],
    by rw [e 17 (by norm_num) (by norm_num), h17], by rw [e 18 (by norm_num) (by norm_num), h18],
    by rw [Fn 7 hns, hj]⟩

theorem runs_df2Params {n : ℕ} {δ : ℝ} (σ : Env d) (hd : σ.nat 0 = d) (hn : σ.nat 1 = n) (hδ : σ.sc 2 = δ) :
    Runs df2L w df2Params σ ((df2oPar d n δ).j * 4 + 103)
      (fun σ' => ParRep (df2oPar d n δ) σ' ∧ σ'.nat 2 = 1 ∧ Env.Frame σ σ' [2, 7] (List.range' 3 65) []) := by
  obtain ⟨h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, hj⟩ :=
    parSI_val (d := d) (n := n) (Function.update σ.nat 2 1) σ.sc (by simp [hd]) (by simp [hn]) hδ
  have hs := runs_seq_eq (runs_nconst (L := df2L) (w := w) (σ := σ) (by decide) 1)
    (runs_seq_eq (runs_sprog (L := df2L) (w := w) parSI parSI_ok (σ.setNat 2 1))
      (runs_nceil (L := df2L) (w := w) { σ.setNat 2 1 with sc := sEval (σ.setNat 2 1).nat parSI (σ.setNat 2 1).sc }
        (i := 7) (one := 2) (x := 64) (t := 67) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by simp)))
  have hJ : ⌈sEval (σ.setNat 2 1).nat parSI (σ.setNat 2 1).sc 64⌉₊ = (df2oPar d n δ).j := hj
  refine runs_mono hs (by simp only [sCost_parSI, hJ]; omega) (fun σ' e => ?_)
  subst e
  simp only [hJ]
  have k : ∀ x, x ≠ 67 →
      (({ σ.setNat 2 1 with sc := sEval (σ.setNat 2 1).nat parSI (σ.setNat 2 1).sc } : Env d).setNat 7
        (df2oPar d n δ).j |>.setSc 67 ((df2oPar d n δ).j : ℝ)).sc x =
        sEval (σ.setNat 2 1).nat parSI (σ.setNat 2 1).sc x :=
    fun x hx => by simp only [Env.setSc_sc, hx, ite_false, Env.setNat_sc]
  refine ⟨⟨by rw [k 3 (by decide)]; exact h3, by rw [k 4 (by decide)]; exact h4, by rw [k 5 (by decide)]; exact h5,
    by rw [k 6 (by decide)]; exact h6, by rw [k 7 (by decide)]; exact h7, by rw [k 8 (by decide)]; exact h8,
    by rw [k 9 (by decide)]; exact h9, by rw [k 10 (by decide)]; exact h10, by rw [k 11 (by decide)]; exact h11,
    by rw [k 12 (by decide)]; exact h12, by rw [k 13 (by decide)]; exact h13, by rw [k 14 (by decide)]; exact h14,
    by rw [k 15 (by decide)]; exact h15, by rw [k 16 (by decide)]; exact h16, by rw [k 17 (by decide)]; exact h17,
    by rw [k 18 (by decide)]; exact h18, by simp⟩, by simp, ?_⟩
  · refine ⟨fun i hi => ?_, fun x hx => ?_, fun a _ => rfl, rfl, rfl, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      simp [hi.1, hi.2]
    · simp only [List.mem_range'_1, not_and_or, not_le, not_lt] at hx
      have h67 : x ≠ 67 := by omega
      simp only [Env.setSc_sc, h67, ite_false, Env.setNat_sc]
      exact sEval_frame _ _ _ (parSI_dst (by omega))

/-! ## The position and the state of an epoch -/

/-- The affine map of a position on a vector of coordinates. -/
theorem pg_affine (Ps : PgSp d) (y : Fin d → ℝ) :
    pgMu Ps + pgOp Ps (WithLp.toLp 2 y) = WithLp.toLp 2 (pgMat Ps *ᵥ y + fun i => Ps (Sum.inl i)) := by
  rw [pgOp, Matrix.toEuclideanCLM_toLp, pgMu, ← WithLp.toLp_add, add_comm]

/-- The arrays `0` and `1` hold the position `Ps`. -/
def PosRep (Ps : PgSp d) (σ : Env d) : Prop := σ.vec 0 = (fun i => Ps (Sum.inl i)) ∧ σ.mat 1 = pgMat Ps

/-- The fields of the state `st` of an epoch: `first` in the scalar `23` (`1` or `0`), `μ, P, Σ, A, b` in the arrays
`2` to `6`, `k` in the scalar `24`, `Ĝ` in the array `7`, `l` in the scalar `25`, the ball `(ctr, r)` in the array `8`
and the scalar `26`. -/
def StRep (st : Df2St d) (σ : Env d) : Prop :=
  σ.sc 23 = (if st.first then 1 else 0) ∧ σ.vec 2 = st.mu ∧ σ.mat 3 = st.P ∧ σ.mat 4 = st.S ∧ σ.mat 5 = st.A ∧
    σ.vec 6 = st.b ∧ σ.sc 24 = st.k ∧ σ.vec 7 = st.G ∧ σ.sc 25 = st.l ∧ σ.vec 8 = st.ctr ∧ σ.sc 26 = st.r

/-- The mode in the scalar `22` (`0` off, `1` guard, `2` run) and, in a round of DF2, the state of the epoch. -/
def ModeRep : Df2Mode d → Env d → Prop
  | .off, σ => σ.sc 22 = 0
  | .guard, σ => σ.sc 22 = 1
  | .run st, σ => σ.sc 22 = 2 ∧ StRep st σ

/-! ## Part A of a round: the draws and the point played

Scalars: `19, 20, 21, 27` hold `1/2, 3/2, 0, 1`; `28` the answer of the play test; `29` the last draw `g`; `30` the
factor `pt`; `33` holds `1 - λ`; `34` to `40` the membership in `K'` (`40` its answer); `41` to `51` the gauge (`51`
its value); `52`, `53` hold `π̃/(1 - ε)` and `1/pt`; `54` the membership of the point; `59` holds `1 - ε`. Arrays:
`9` the draw `ξ`, `10` the vector `w = A ξ`, `11` the sample `X`, `12` the input of the membership tests, `13` the
point `μ_S + A_S y`, `14` the point played. -/

/-- `40 := [y ∈ K']` for the array `12`, `K' = df2Kp K Ps R`: `34 := [A_S y + μ_S ∈ K]` (`13 := A_S y + μ_S`),
`39 := |y|`, then `40 := 0` if `R < |y|`, else `40 := 34`. -/
def memKp : Cmd :=
  .seq (memAff df2L 0 2 3 4 5 34 0 1 12 13 35 36 37 38)
    (.seq (vnorm df2L 0 2 3 39 12 37 38) (ifS df2L 17 39 (sconst df2L 40 0) (smov df2L 40 34)))

/-- The steps of `memKp`. -/
def kMemKp (d : ℕ) : ℕ := d * (d * 10 + 9) + d * 20 + 17

/-- The gauge `π̃(X)` of `K'` (the array `11`) into the scalar `51`, `j` halvings (natural `7`) of `[|X|/R, |X|]`. -/
def gaugeKp : Cmd := gaugeBis df2L memKp 0 2 3 8 7 11 12 17 40 51 41 42 43 44 45 46 47 48 49 50

/-- The play test: if the scalar `54` is positive, the point played (array `14`) is the array `13` and `28 := 1`;
else it is `0` and `28 := 0`. -/
def aTest : Cmd :=
  ifS df2L 21 54 (.seq (vcopy df2L 0 2 3 14 13 37) (sconst df2L 28 1))
    (.seq (vfill df2L 0 2 3 14 21) (sconst df2L 28 0))

/-- Mode off: the point `0`. -/
def aOff : Cmd := .seq (vfill df2L 0 2 3 14 21) (sconst df2L 28 0)

/-- Mode guard: the point `μ_S + A_S 0` and its test. -/
def aGuard : Cmd := .seq (vfill df2L 0 2 3 12 21) (.seq (memAff df2L 0 2 3 4 5 54 0 1 12 13 35 36 37 38) aTest)

open SI in
/-- A round of DF2, the sample: `w := A ξ` (array `10`), `33 := 1 - λ`, `X := μ + (1 - λ) w` (array `11`). -/
def aRun1 : Cmd :=
  .seq (matvec df2L 0 2 3 4 5 10 5 9 35 37 38) <|
  .seq (sprog df2L [op2 .sub 33 27 6]) <|
  .seq (vcopy df2L 0 2 3 11 2 37) (vaxpy df2L 0 2 3 11 10 33 37 38)

open SI in
/-- A round of DF2, the point from the gauge value (scalar `51`): `pt := max 1 (π̃/(1 - ε))` (scalar `30`),
`y := X/pt`, the point `μ_S + A_S y` and its test. -/
def aRun2 : Cmd :=
  .seq (sprog df2L [op2 .sub 59 27 10, op2 .div 52 51 59, .smax 30 27 52, op2 .div 53 27 30]) <|
  .seq (vcopy df2L 0 2 3 12 11 37) <|
  .seq (vscale df2L 0 2 3 12 53 37) <|
  .seq (memAff df2L 0 2 3 4 5 54 0 1 12 13 35 36 37 38) aTest

/-- A round of DF2, the point: the sample `X`, its gauge `π̃(X)` in `K'`, the point. -/
def aRun : Cmd := .seq aRun1 (.seq gaugeKp aRun2)

open SI in
/-- Part A of a round: the constants, the `d + 1` draws (`ξ` into the array `9`, `g` into the scalar `29`), then the
point by the mode (scalar `22`: below `1/2` off, below `3/2` guard, else run). -/
def df2A : Cmd :=
  .seq (sprog df2L [const 19 (1 / 2), const 20 (3 / 2), const 21 0, const 27 1]) <|
  .seq (vgauss df2L 0 2 3 9 37) <|
  .seq (gauss df2L 29) (ifS df2L 22 19 aOff (ifS df2L 22 20 aGuard aRun))

open Classical in
/-- The rule of `memKp`. -/
theorem runs_memKp (Ps : PgSp d) (σ : Env d) (hd : σ.nat 0 = d) (h1 : σ.nat 2 = 1) (hP : PosRep Ps σ) :
    Runs df2L w memKp σ (kMemKp d) (fun σ' =>
      σ'.sc 40 = (if WithLp.toLp 2 (σ.vec 12) ∈ df2Kp w.K Ps (σ.sc 17) then 1 else 0) ∧
        Env.Frame σ σ' [3, 4, 5] [34, 35, 36, 37, 38, 39, 40] [13]) := by
  have hm := runs_memAff (L := df2L) (w := w) σ (dv := 0) (one := 2) (i := 3) (j := 4) (k := 5) (o := 34) (mu := 0)
    (T := 1) (y := 12) (tmp := 13) (c := 35) (s := 36) (t1 := 37) (t2 := 38)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hd h1
  refine runs_mono (K := (d * (d * 10 + 9) + d * 11 + 9) + ((d * 9 + 5) + 3)) (runs_seq hm (fun σ1 h1' => ?_))
    (by unfold kMemKp; ring_nf; omega) (fun σ' h => h)
  obtain ⟨o1, -, F1, -⟩ := h1'
  have hd1 : σ1.nat 0 = d := by rw [F1.1 0 (by decide), hd]
  have h11 : σ1.nat 2 = 1 := by rw [F1.1 2 (by decide), h1]
  refine runs_seq (runs_vnorm (L := df2L) (w := w) σ1 (dv := 0) (one := 2) (i := 3) (r := 39) (x := 12) (t1 := 37)
    (t2 := 38)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hd1 h11) (fun σ2 h2 => ?_)
  obtain ⟨n2, F2⟩ := h2
  have F12 : Env.Frame σ σ2 [3, 4, 5] [34, 35, 36, 37, 38, 39, 40] [13] :=
    Env.Frame.trans (Env.Frame.mono F1 (by simp) (by simp) (by simp)) (Env.Frame.mono F2 (by simp) (by simp) (by simp))
  have e12 : σ1.vec 12 = σ.vec 12 := funext fun r => by simp only [Env.vec]; rw [F1.2.2.1 12 (by decide)]
  have e17 : σ2.sc 17 = σ.sc 17 := F12.2.1 17 (by decide)
  have e34 : σ2.sc 34 = σ1.sc 34 := F2.2.1 34 (by decide)
  have hK : (WithLp.toLp 2 (σ.mat 1 *ᵥ σ.vec 12 + σ.vec 0) ∈ w.K) ↔
      pgMu Ps + pgOp Ps (WithLp.toLp 2 (σ.vec 12)) ∈ w.K := by
    rw [pg_affine, hP.1, hP.2]
  have hn : ‖WithLp.toLp 2 (σ.vec 12)‖ = σ2.sc 39 := by rw [n2, e12, norm_toLp_eq]
  by_cases hR : σ2.sc 17 < σ2.sc 39
  · refine runs_mono (runs_ifS_t (by decide) (by decide) hR (runs_sconst (L := df2L) (w := w) (σ := σ2)
      (x := 40) (by decide) 0)) (by norm_num) (fun σ' e => ?_)
    subst e
    refine ⟨?_, Env.Frame.setSc F12 (by decide) _⟩
    have : WithLp.toLp 2 (σ.vec 12) ∉ df2Kp w.K Ps (σ.sc 17) := fun h => by
      have := h.2; rw [hn, ← e17] at this; linarith
    simp [this]
  · refine runs_ifS_f (by decide) (by decide) hR (runs_mono (runs_smov (L := df2L) (w := w) (σ := σ2) (x := 40)
      (y := 34) (by decide) (by decide)) le_rfl (fun σ' e => ?_))
    subst e
    refine ⟨?_, Env.Frame.setSc F12 (by decide) _⟩
    have hle : ‖WithLp.toLp 2 (σ.vec 12)‖ ≤ σ.sc 17 := by rw [hn, ← e17]; exact not_lt.1 hR
    have : (WithLp.toLp 2 (σ.vec 12) ∈ df2Kp w.K Ps (σ.sc 17)) ↔
        pgMu Ps + pgOp Ps (WithLp.toLp 2 (σ.vec 12)) ∈ w.K := ⟨fun h => h.1, fun h => ⟨h, hle⟩⟩
    simp only [Env.setSc_sc, ite_true, e34, o1]
    exact if_congr (hK.trans this.symm) rfl rfl


/-- A vector off the arrays of a frame. -/
theorem Env.Frame.vec_eq {σ σ' : Env d} {ns ss as : List ℕ} (h : Env.Frame σ σ' ns ss as) {a : ℕ} (ha : a ∉ as) :
    σ'.vec a = σ.vec a := funext fun i => by simp only [Env.vec]; rw [h.2.2.1 a ha]

/-- A matrix off the arrays of a frame. -/
theorem Env.Frame.mat_eq {σ σ' : Env d} {ns ss as : List ℕ} (h : Env.Frame σ σ' ns ss as) {a : ℕ} (ha : a ∉ as) :
    σ'.mat a = σ.mat a := by funext i j; simp only [Env.mat]; rw [h.2.2.1 a ha]

/-- `PosRep` survives a frame off the arrays `0` and `1`. -/
theorem PosRep.frame {Ps : PgSp d} {σ σ' : Env d} {ns ss as : List ℕ} (h : PosRep Ps σ)
    (hF : Env.Frame σ σ' ns ss as) (h0 : 0 ∉ as) (h1 : 1 ∉ as) : PosRep Ps σ' := by
  refine ⟨?_, ?_⟩
  · rw [← h.1]; funext i; simp only [Env.vec]; rw [hF.2.2.1 0 h0]
  · rw [← h.2]; funext i j; simp only [Env.mat]; rw [hF.2.2.1 1 h1]

open Classical in
/-- The rule of `gaugeKp`: `memKp` keeps the position and `R`. -/
theorem runs_gaugeKp (Ps : PgSp d) (σ : Env d) (hd : σ.nat 0 = d) (h1 : σ.nat 2 = 1) (hP : PosRep Ps σ) :
    Runs df2L w gaugeKp σ (σ.nat 7 * (d * 15 + kMemKp d + 16) + d * 9 + 15)
      (fun σ' => σ'.sc 51 = piTilde (df2Kp w.K Ps (σ.sc 17)) (σ.sc 17) (σ.nat 7) (WithLp.toLp 2 (σ.vec 11)) ∧
        Env.Frame σ σ' [3, 8, 3, 4, 5] [41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 34, 35, 36, 37, 38, 39, 40]
          [12, 13] ∧ PosRep Ps σ' ∧ σ'.sc 17 = σ.sc 17) := by
  have h := runs_gaugeBis (L := df2L) (w := w) (memQ := memKp) (dv := 0) (one := 2) (i := 3) (jj := 8) (jv := 7)
    (x := 11) (yv := 12) (ρ := 17) (qo := 40) (pv := 51) (nx := 41) (sl := 42) (su := 43) (mid := 44) (inv := 45)
    (z := 46) (h := 47) (o := 48) (t1 := 49) (t2 := 50) (df2Kp w.K Ps (σ.sc 17))
    (fun σ' => PosRep Ps σ' ∧ σ'.sc 17 = σ.sc 17) (kMemKp d) [3, 4, 5] [34, 35, 36, 37, 38, 39, 40] [13] σ
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd h1 ⟨hP, rfl⟩
    (fun σ' hI hd' h1' => runs_mono (runs_memKp Ps σ' hd' h1' hI.1) le_rfl (fun σ'' ⟨e, F⟩ =>
      ⟨by rw [e, hI.2], F, hI.1.frame F (by decide) (by decide), by rw [F.2.1 17 (by decide), hI.2]⟩))
    (fun σ' σ'' hI F => ⟨hI.1.frame F (by decide) (by decide), by rw [F.2.1 17 (by decide), hI.2]⟩)
  exact runs_mono h le_rfl (fun σ' ⟨e, F, hI⟩ => ⟨e, F, hI.1, hI.2⟩)
open Classical in
/-- The rule of `aTest`. -/
theorem runs_aTest (P : Prop) (x : Fin d → ℝ) (σ : Env d) (hd : σ.nat 0 = d) (h1 : σ.nat 2 = 1)
    (h0 : σ.sc 21 = 0) (h54 : σ.sc 54 = if P then 1 else 0) (h13 : σ.vec 13 = x) :
    Runs df2L w aTest σ (d * 7 + 6)
      (fun σ' => σ'.vec 14 = (if P then x else 0) ∧ σ'.sc 28 = (if P then 1 else 0) ∧
        Env.Frame σ σ' [3] [28, 37] [14]) := by
  by_cases hP : P
  · have hc : σ.sc 21 < σ.sc 54 := by simp [h0, h54, hP]
    refine runs_mono (runs_ifS_t (by decide) (by decide) hc (runs_seq (runs_vcopy (L := df2L) (w := w) σ (dv := 0)
      (one := 2) (i := 3) (y := 14) (x := 13) (t := 37)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd h1)
      (fun σ1 h => runs_mono (runs_sconst (L := df2L) (w := w) (σ := σ1) (x := 28) (by decide) 1) le_rfl
        (fun σ2 e => e ▸ (show _ from ?_))))) (by omega) (fun σ' h => h)
    obtain ⟨e1, F1, -⟩ := h
    refine ⟨?_, ?_, ?_⟩
    · show σ1.vec 14 = _; rw [e1, h13]; simp [hP]
    · simp [hP]
    · exact Env.Frame.setSc (Env.Frame.mono F1 (by simp) (by simp) (by simp)) (by decide) _
  · have hc : ¬ σ.sc 21 < σ.sc 54 := by simp [h0, h54, hP]
    refine runs_mono (runs_ifS_f (by decide) (by decide) hc (runs_seq (runs_vfill (L := df2L) (w := w) σ (dv := 0)
      (one := 2) (i := 3) (y := 14) (z := 21)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd h1)
      (fun σ1 h => runs_mono (runs_sconst (L := df2L) (w := w) (σ := σ1) (x := 28) (by decide) 0) le_rfl
        (fun σ2 e => e ▸ (show _ from ?_))))) (by omega) (fun σ' h => h)
    obtain ⟨e1, F1, -⟩ := h
    refine ⟨?_, ?_, ?_⟩
    · show σ1.vec 14 = _; rw [e1, h0]; simp [hP]; rfl
    · simp [hP]
    · exact Env.Frame.setSc (Env.Frame.mono F1 (by simp) (by simp) (by simp)) (by decide) _

/-- The rule of `aOff`. -/
theorem runs_aOff (σ : Env d) (hd : σ.nat 0 = d) (h1 : σ.nat 2 = 1) (h0 : σ.sc 21 = 0) :
    Runs df2L w aOff σ (d * 5 + 4) (fun σ' => σ'.vec 14 = 0 ∧ σ'.sc 28 = 0 ∧ Env.Frame σ σ' [3] [28] [14]) := by
  refine runs_mono (K := d * 5 + 3 + 1) (runs_seq (runs_vfill (L := df2L) (w := w) σ (dv := 0) (one := 2) (i := 3)
    (y := 14) (z := 21)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd h1)
    (fun σ1 h => runs_mono (runs_sconst (L := df2L) (w := w) (σ := σ1) (x := 28) (by decide) 0) le_rfl
      (fun σ2 e => ?_))) le_rfl (fun σ' h => h)
  obtain ⟨e1, F1, -⟩ := h
  subst e
  refine ⟨?_, by simp, Env.Frame.setSc (ss := [28]) (Env.Frame.mono F1 (by simp) (by simp) (by simp)) (by decide) _⟩
  show σ1.vec 14 = _; rw [e1, h0]; rfl

open Classical in
/-- The rule of `aGuard`: the point `μ_S + A_S 0` if it is in `K`, else `0`. -/
theorem runs_aGuard (Ps : PgSp d) (σ : Env d) (hd : σ.nat 0 = d) (h1 : σ.nat 2 = 1) (h0 : σ.sc 21 = 0)
    (hP : PosRep Ps σ) :
    Runs df2L w aGuard σ (d * (d * 10 + 9) + d * 23 + 18)
      (fun σ' => WithLp.toLp 2 (σ'.vec 14) = (if pgMu Ps + pgOp Ps 0 ∈ w.K then pgMu Ps + pgOp Ps 0 else 0) ∧
        σ'.sc 28 = (if pgMu Ps + pgOp Ps 0 ∈ w.K then 1 else 0) ∧
        Env.Frame σ σ' [3, 4, 5] [28, 34, 35, 36, 37, 38, 54] [12, 13, 14]) := by
  refine runs_mono (K := d * 5 + 3 + ((d * (d * 10 + 9) + d * 11 + 9) + (d * 7 + 6)))
    (runs_seq (runs_vfill (L := df2L) (w := w) σ (dv := 0) (one := 2) (i := 3) (y := 12) (z := 21)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd h1)
        (fun σ1 h1' => ?_)) (by ring_nf; omega) (fun σ' h => h)
  obtain ⟨e1, F1, -⟩ := h1'
  have hd1 : σ1.nat 0 = d := by rw [F1.1 0 (by decide), hd]
  have h11 : σ1.nat 2 = 1 := by rw [F1.1 2 (by decide), h1]
  have hP1 : PosRep Ps σ1 := hP.frame F1 (by decide) (by decide)
  refine runs_seq (runs_memAff (L := df2L) (w := w) σ1 (dv := 0) (one := 2) (i := 3) (j := 4) (k := 5) (o := 54)
    (mu := 0) (T := 1) (y := 12) (tmp := 13) (c := 35) (s := 36) (t1 := 37) (t2 := 38)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hd1 h11) (fun σ2 h2 => ?_)
  obtain ⟨o2, v2, F2, -⟩ := h2
  have hx : WithLp.toLp 2 (σ2.vec 13) = pgMu Ps + pgOp Ps 0 := by
    rw [v2, e1, hP1.1, hP1.2, ← WithLp.toLp_zero 2 (V := Fin d → ℝ), pg_affine]; simp only [h0]; rfl
  have h54 : σ2.sc 54 = if pgMu Ps + pgOp Ps 0 ∈ w.K then 1 else 0 := by
    rw [o2, ← v2, hx]
  refine runs_mono (runs_aTest (pgMu Ps + pgOp Ps 0 ∈ w.K) (σ2.vec 13) σ2 (by rw [F2.1 0 (by decide), hd1])
    (by rw [F2.1 2 (by decide), h11]) (by rw [F2.2.1 21 (by decide), F1.2.1 21 (by decide), h0]) h54 rfl) le_rfl
    (fun σ3 ⟨e3, s3, F3⟩ => ⟨?_, s3, ?_⟩)
  · rw [e3]; split_ifs <;> simp [hx]
  · exact Env.Frame.trans (Env.Frame.mono F1 (by simp) (by simp) (by simp))
      (Env.Frame.trans (Env.Frame.mono F2 (by simp) (by simp) (by simp)) (Env.Frame.mono F3 (by simp) (by simp)
        (by simp)))

/-- The rule of `aRun1`. -/
theorem runs_aRun1 (σ : Env d) (hd : σ.nat 0 = d) (h1 : σ.nat 2 = 1) (h27 : σ.sc 27 = 1) :
    Runs df2L w aRun1 σ (d * (d * 10 + 9) + d * 18 + 11)
      (fun σ' => σ'.vec 10 = σ.mat 5 *ᵥ σ.vec 9 ∧
        σ'.vec 11 = σ.vec 2 + (1 - σ.sc 6) • (σ.mat 5 *ᵥ σ.vec 9) ∧
        Env.Frame σ σ' [3, 4, 5] [33, 35, 37, 38] [10, 11]) := by
  refine runs_mono (K := d * (d * 10 + 9) + 4 + (sCost [SI.op2 .sub 33 27 6] + ((d * 7 + 3) + (d * 11 + 3))))
    (runs_seq (runs_matvec (L := df2L) (w := w) σ (dv := 0) (one := 2) (i := 3) (j := 4) (k := 5) (y := 10) (A := 5)
      (x := 9) (s := 35) (t1 := 37) (t2 := 38) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd h1) (fun σ1 h1' => ?_))
    (by simp only [sCost, List.map, SI.cost, List.sum_cons, List.sum_nil]; ring_nf; omega) (fun σ' h => h)
  obtain ⟨e1, F1, -⟩ := h1'
  have hd1 : σ1.nat 0 = d := by rw [F1.1 0 (by decide), hd]
  have h11 : σ1.nat 2 = 1 := by rw [F1.1 2 (by decide), h1]
  refine runs_seq_eq (runs_sprog (L := df2L) (w := w) [SI.op2 .sub 33 27 6] (by decide) σ1) ?_
  set σ2 : Env d := { σ1 with sc := sEval σ1.nat [SI.op2 .sub 33 27 6] σ1.sc }
  have F2 : Env.Frame σ1 σ2 [] [33] [] := ⟨fun _ _ => rfl, fun x hx => by
    simp only [σ2, sEval, List.foldl, SI.step, SI.dst, SI.val]
    rw [Function.update_of_ne (by simpa using hx)], fun _ _ => rfl, rfl, rfl, rfl⟩
  have s33 : σ2.sc 33 = 1 - σ.sc 6 := by
    simp only [σ2, sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_self, Op2.eval]
    rw [F1.2.1 27 (by decide), F1.2.1 6 (by decide), h27]
  refine runs_seq (runs_vcopy (L := df2L) (w := w) σ2 (dv := 0) (one := 2) (i := 3) (y := 11) (x := 2) (t := 37)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd1 h11)
      (fun σ3 h3 => ?_)
  obtain ⟨e3, F3, -⟩ := h3
  refine runs_mono (runs_vaxpy (L := df2L) (w := w) σ3 (dv := 0) (one := 2) (i := 3) (y := 11) (x := 10) (α := 33)
    (t1 := 37) (t2 := 38) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by rw [F3.1 0 (by decide)]; exact hd1)
        (by rw [F3.1 2 (by decide)]; exact h11))
    le_rfl (fun σ4 h4 => ?_)
  obtain ⟨e4, F4, -⟩ := h4
  have v10 : σ3.vec 10 = σ.mat 5 *ᵥ σ.vec 9 := by
    rw [Env.Frame.vec_eq F3 (by decide), show σ2.vec 10 = σ1.vec 10 from rfl, e1]
  refine ⟨by rw [Env.Frame.vec_eq F4 (by decide), v10], ?_, ?_⟩
  · rw [e4, e3, v10, F3.2.1 33 (by decide), s33]
    show σ1.vec 2 + _ = _
    rw [Env.Frame.vec_eq F1 (by decide)]
  · exact Env.Frame.trans (Env.Frame.mono F1 (by simp) (by simp) (by simp)) (Env.Frame.trans
      (Env.Frame.mono F2 (by simp) (by simp) (by simp)) (Env.Frame.trans (Env.Frame.mono F3 (by simp) (by simp)
        (by simp)) (Env.Frame.mono F4 (by simp) (by simp) (by simp))))

open Classical in
/-- The rule of `aRun2`. -/
theorem runs_aRun2 (Ps : PgSp d) (σ : Env d) (hd : σ.nat 0 = d) (h1 : σ.nat 2 = 1) (h0 : σ.sc 21 = 0)
    (h27 : σ.sc 27 = 1) (hP : PosRep Ps σ) :
    Runs df2L w aRun2 σ (d * (d * 10 + 9) + d * 33 + 30)
      (fun σ' => σ'.sc 30 = max 1 (σ.sc 51 / (1 - σ.sc 10)) ∧
        WithLp.toLp 2 (σ'.vec 14) = (if pgMu Ps + pgOp Ps (WithLp.toLp 2 ((σ'.sc 30)⁻¹ • σ.vec 11)) ∈ w.K then
          pgMu Ps + pgOp Ps (WithLp.toLp 2 ((σ'.sc 30)⁻¹ • σ.vec 11)) else 0) ∧
        σ'.sc 28 = (if pgMu Ps + pgOp Ps (WithLp.toLp 2 ((σ'.sc 30)⁻¹ • σ.vec 11)) ∈ w.K then 1 else 0) ∧
        Env.Frame σ σ' [3, 4, 5] [28, 30, 35, 36, 37, 38, 52, 53, 54, 59] [12, 13, 14]) := by
  let l : List SI := [SI.op2 .sub 59 27 10, SI.op2 .div 52 51 59, SI.smax 30 27 52, SI.op2 .div 53 27 30]
  refine runs_mono (K := sCost l + ((d * 7 + 3) + ((d * 8 + 3) + ((d * (d * 10 + 9) + d * 11 + 9) + (d * 7 + 6)))))
    (runs_seq_eq (runs_sprog (L := df2L) (w := w) l (by decide) σ) ?_)
    (by simp only [l, sCost, List.map, SI.cost, List.sum_cons, List.sum_nil]; ring_nf; omega) (fun σ' h => h)
  set σ1 : Env d := { σ with sc := sEval σ.nat l σ.sc }
  have F1 : Env.Frame σ σ1 [] [30, 52, 53, 59] [] := ⟨fun _ _ => rfl, fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [σ1, l, sEval, List.foldl, SI.step, SI.dst, SI.val]
    simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2], fun _ _ => rfl, rfl, rfl, rfl⟩
  have s30 : σ1.sc 30 = max 1 (σ.sc 51 / (1 - σ.sc 10)) := by
    simp only [σ1, l, sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval]
    simp [h27]
  have s53 : σ1.sc 53 = (σ1.sc 30)⁻¹ := by
    rw [s30]
    simp only [σ1, l, sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval]
    simp [h27]
  refine runs_seq (runs_vcopy (L := df2L) (w := w) σ1 (dv := 0) (one := 2) (i := 3) (y := 12) (x := 11) (t := 37)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd h1)
      (fun σ2 h2 => ?_)
  obtain ⟨e2, F2, -⟩ := h2
  have hd2 : σ2.nat 0 = d := by rw [F2.1 0 (by decide)]; exact hd
  have h12 : σ2.nat 2 = 1 := by rw [F2.1 2 (by decide)]; exact h1
  refine runs_seq (runs_vscale (L := df2L) (w := w) σ2 (dv := 0) (one := 2) (i := 3) (y := 12) (α := 53) (t := 37)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) hd2 h12) (fun σ3 h3 => ?_)
  obtain ⟨e3, F3, -⟩ := h3
  have hd3 : σ3.nat 0 = d := by rw [F3.1 0 (by decide)]; exact hd2
  have h13 : σ3.nat 2 = 1 := by rw [F3.1 2 (by decide)]; exact h12
  have v12 : σ3.vec 12 = (σ1.sc 30)⁻¹ • σ.vec 11 := by
    rw [e3, e2, F2.2.1 53 (by decide), s53]; rfl
  have hP3 : PosRep Ps σ3 := ((hP.frame F1 (by decide) (by decide)).frame F2 (by decide) (by decide)).frame F3
    (by decide) (by decide)
  refine runs_seq (runs_memAff (L := df2L) (w := w) σ3 (dv := 0) (one := 2) (i := 3) (j := 4) (k := 5) (o := 54)
    (mu := 0) (T := 1) (y := 12) (tmp := 13) (c := 35) (s := 36) (t1 := 37) (t2 := 38)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hd3 h13) (fun σ4 h4 => ?_)
  obtain ⟨o4, v4, F4, -⟩ := h4
  set x := pgMu Ps + pgOp Ps (WithLp.toLp 2 ((σ1.sc 30)⁻¹ • σ.vec 11)) with hxdef
  have hx : WithLp.toLp 2 (σ4.vec 13) = x := by rw [v4, v12, hP3.1, hP3.2, hxdef, pg_affine]
  have h54 : σ4.sc 54 = if x ∈ w.K then 1 else 0 := by rw [o4, ← v4, hx]
  have h0' : σ4.sc 21 = 0 := by
    rw [F4.2.1 21 (by decide), F3.2.1 21 (by decide), F2.2.1 21 (by decide), F1.2.1 21 (by decide), h0]
  refine runs_mono (runs_aTest (x ∈ w.K) (σ4.vec 13) σ4 (by rw [F4.1 0 (by decide)]; exact hd3)
    (by rw [F4.1 2 (by decide)]; exact h13) h0' h54 rfl) le_rfl (fun σ5 ⟨e5, s5, F5⟩ => ?_)
  have F : Env.Frame σ σ5 [3, 4, 5] [28, 30, 35, 36, 37, 38, 52, 53, 54, 59] [12, 13, 14] :=
    Env.Frame.trans (Env.Frame.mono F1 (by simp) (by simp) (by simp)) (Env.Frame.trans
    (Env.Frame.mono F2 (by simp) (by simp) (by simp)) (Env.Frame.trans (Env.Frame.mono F3 (by simp) (by simp)
      (by simp)) (Env.Frame.trans (Env.Frame.mono F4 (by simp) (by simp) (by simp))
        (Env.Frame.mono F5 (by simp) (by simp) (by simp)))))
  have e30 : σ5.sc 30 = σ1.sc 30 := by
    rw [F5.2.1 30 (by decide), F4.2.1 30 (by decide), F3.2.1 30 (by decide), F2.2.1 30 (by decide)]
  refine ⟨by rw [e30, s30], ?_, by rw [s5, e30], F⟩
  rw [e5, e30]; split_ifs
  · exact hx
  · rfl

/-- The steps of `aRun`. -/
def kARun (d j : ℕ) : ℕ :=
  d * (d * 10 + 9) + d * 18 + 11 + (j * (d * 15 + kMemKp d + 16) + d * 9 + 15 + (d * (d * 10 + 9) + d * 33 + 30))

open Classical in
/-- The rule of `aRun`: the vector `w = A ξ`, the factor `pt` and the point of a round of DF2. -/
theorem runs_aRun (Ps : PgSp d) (p : Df2OPar) (st : Df2St d) (σ : Env d) (hd : σ.nat 0 = d)
    (h1 : σ.nat 2 = 1) (h0 : σ.sc 21 = 0) (h27 : σ.sc 27 = 1) (hP : PosRep Ps σ) (hpar : ParRep p σ)
    (hst : StRep st σ) :
    Runs df2L w aRun σ (kARun d p.j)
      (fun σ' => σ'.vec 10 = st.A *ᵥ σ.vec 9 ∧
        σ'.sc 30 = max 1 (piTilde (df2Kp w.K Ps p.R) p.R p.j
          (WithLp.toLp 2 (st.mu + (1 - p.lam) • (st.A *ᵥ σ.vec 9))) / (1 - p.eps)) ∧
        WithLp.toLp 2 (σ'.vec 14) =
          (if pgMu Ps + pgOp Ps (WithLp.toLp 2 ((σ'.sc 30)⁻¹ • (st.mu + (1 - p.lam) • (st.A *ᵥ σ.vec 9)))) ∈ w.K
            then pgMu Ps + pgOp Ps (WithLp.toLp 2 ((σ'.sc 30)⁻¹ • (st.mu + (1 - p.lam) • (st.A *ᵥ σ.vec 9))))
            else 0) ∧
        σ'.sc 28 = (if pgMu Ps + pgOp Ps (WithLp.toLp 2 ((σ'.sc 30)⁻¹ • (st.mu + (1 - p.lam) • (st.A *ᵥ σ.vec 9))))
          ∈ w.K then 1 else 0) ∧
        Env.Frame σ σ' [3, 4, 5, 8] ([28, 30, 59] ++ List.range' 33 22) [10, 11, 12, 13, 14]) := by
  obtain ⟨-, -, -, p6, -, -, -, p10, -, -, -, -, -, -, p17, -, pj⟩ := hpar
  obtain ⟨-, s2, -, -, s5, -⟩ := hst
  refine runs_seq (runs_aRun1 σ hd h1 h27) (fun σ1 h1' => ?_)
  obtain ⟨v10, v11, F1⟩ := h1'
  have hd1 : σ1.nat 0 = d := by rw [F1.1 0 (by decide)]; exact hd
  have h11 : σ1.nat 2 = 1 := by rw [F1.1 2 (by decide)]; exact h1
  have hj1 : σ1.nat 7 = p.j := by rw [F1.1 7 (by decide)]; exact pj
  refine runs_seq (runs_mono (runs_gaugeKp (w := w) Ps σ1 hd1 h11 (hP.frame F1 (by decide) (by decide)))
    (le_of_eq (by rw [hj1])) (fun σ' h => h)) (fun σ2 h2 => ?_)
  obtain ⟨g51, F2, hP2, -⟩ := h2
  have hd2 : σ2.nat 0 = d := by rw [F2.1 0 (by decide)]; exact hd1
  have h12 : σ2.nat 2 = 1 := by rw [F2.1 2 (by decide)]; exact h11
  have h02 : σ2.sc 21 = 0 := by rw [F2.2.1 21 (by decide), F1.2.1 21 (by decide)]; exact h0
  have h272 : σ2.sc 27 = 1 := by rw [F2.2.1 27 (by decide), F1.2.1 27 (by decide)]; exact h27
  refine runs_mono (runs_aRun2 (w := w) Ps σ2 hd2 h12 h02 h272 hP2) le_rfl (fun σ3 h3 => ?_)
  obtain ⟨s30, v14, s28, F3⟩ := h3
  have e11 : σ2.vec 11 = st.mu + (1 - p.lam) • (st.A *ᵥ σ.vec 9) := by
    rw [Env.Frame.vec_eq F2 (by decide), v11, s2, s5, p6]
  have e51 : σ2.sc 51 / (1 - σ2.sc 10) = piTilde (df2Kp w.K Ps p.R) p.R p.j
      (WithLp.toLp 2 (st.mu + (1 - p.lam) • (st.A *ᵥ σ.vec 9))) / (1 - p.eps) := by
    rw [g51, F2.2.1 10 (by decide), F1.2.1 10 (by decide), F1.2.1 17 (by decide), p17, p10, hj1,
      ← Env.Frame.vec_eq F2 (by decide), e11]
  refine ⟨?_, by rw [s30, e51], by rw [v14, e11], by rw [s28, e11], ?_⟩
  · rw [Env.Frame.vec_eq F3 (by decide), Env.Frame.vec_eq F2 (by decide), v10, s5]
  · exact Env.Frame.trans (Env.Frame.mono F1 (by decide) (by decide) (by decide)) (Env.Frame.trans
      (Env.Frame.mono F2 (by decide) (by decide) (by decide)) (Env.Frame.mono F3 (by decide) (by decide) (by decide)))

/-- The factor `pt` of a round of DF2 from the state `st` and the draw `ξ`. -/
noncomputable def df2Pt (p : Df2OPar) (K : Set (E d)) (Ps : PgSp d) (st : Df2St d) (ξ : Fin d → ℝ) : ℝ :=
  max 1 (piTilde (df2Kp K Ps p.R) p.R p.j (WithLp.toLp 2 (st.mu + (1 - p.lam) • (st.A *ᵥ ξ))) / (1 - p.eps))

/-- The point tested in a round of DF2. -/
noncomputable def df2Pnt (p : Df2OPar) (K : Set (E d)) (Ps : PgSp d) (st : Df2St d) (ξ : Fin d → ℝ) : E d :=
  pgMu Ps + pgOp Ps (WithLp.toLp 2 ((df2Pt p K Ps st ξ)⁻¹ • (st.mu + (1 - p.lam) • (st.A *ᵥ ξ))))

open Classical in
/-- The point played in a round, by mode. -/
theorem df2Round_fst (p : Df2OPar) (n : ℕ) (K : Set (E d)) (Ps : PgSp d) (ft : E d → ℝ) (nt : ℝ) (ξ : Fin d → ℝ)
    (ζ : ℝ) (m : Df2Mode d) : (df2Round p n K Ps ft nt ξ ζ m).1 = match m with
      | .off => 0
      | .guard => if pgMu Ps + pgOp Ps 0 ∈ K then pgMu Ps + pgOp Ps 0 else 0
      | .run st => if df2Pnt p K Ps st ξ ∈ K then df2Pnt p K Ps st ξ else 0 := by
  cases m with
  | off => rfl
  | guard => simp only [df2Round]; split_ifs <;> rfl
  | run st => unfold df2Round; dsimp only; rw [apply_ite Prod.fst]; rfl

open Classical in
/-- What part A leaves for part B, by mode: guard, the answer of the test; run, `w = A ξ`, `pt` and the answer. -/
def AOut (p : Df2OPar) (K : Set (E d)) (Ps : PgSp d) (ξ : Fin d → ℝ) : Df2Mode d → Env d → Prop
  | .off, _ => True
  | .guard, σ => σ.sc 28 = if pgMu Ps + pgOp Ps 0 ∈ K then 1 else 0
  | .run st, σ => σ.vec 10 = st.A *ᵥ ξ ∧ σ.sc 30 = df2Pt p K Ps st ξ ∧
      σ.sc 28 = if df2Pnt p K Ps st ξ ∈ K then 1 else 0

/-- A frame with the draws set on both sides. -/
theorem Env.Frame.setDraws {σ σ' : Env d} {ns ss as : List ℕ} (h : Env.Frame σ σ' ns ss as) (k : ℕ) :
    Env.Frame { σ with draws := k } { σ' with draws := k } ns ss as :=
  ⟨h.1, h.2.1, h.2.2.1, rfl, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- The steps of part A. -/
def kDf2A (d j : ℕ) : ℕ := d * 6 + 12 + (d * 5 + 4) + (d * (d * 10 + 9) + d * 23 + 18) + kARun d j

/-- The constants of a round: the scalars `19, 20, 21, 27` hold `1/2, 3/2, 0, 1`. -/
def CstRep (σ : Env d) : Prop := σ.sc 19 = 1 / 2 ∧ σ.sc 20 = 3 / 2 ∧ σ.sc 21 = 0 ∧ σ.sc 27 = 1

open Classical in
/-- The rule of part A, in every mode: the draws of the round, the point played, what part B reads. -/
theorem runs_df2A (Ps : PgSp d) (p : Df2OPar) (m : Df2Mode d) (σ : Env d) (hd : σ.nat 0 = d)
    (h1 : σ.nat 2 = 1) (hP : PosRep Ps σ) (hpar : ParRep p σ) (hm : ModeRep m σ) :
    Runs df2L w df2A σ (kDf2A d p.j)
      (fun σ' => σ'.vec 9 = (fun c : Fin d => w.gs (σ.draws + c)) ∧ σ'.sc 29 = w.gs (σ.draws + d) ∧
        σ'.draws = σ.draws + (d + 1) ∧
        (∀ n ft nt ζ, WithLp.toLp 2 (σ'.vec 14) = (df2Round p n w.K Ps ft nt (σ'.vec 9) ζ m).1) ∧
        AOut p w.K Ps (σ'.vec 9) m σ' ∧ CstRep σ' ∧
        Env.Frame σ { σ' with draws := σ.draws } [3, 4, 5, 8] ([19, 20, 21] ++ List.range' 27 33)
          [9, 10, 11, 12, 13, 14]) := by
  let l : List SI := [SI.const 19 (1 / 2), SI.const 20 (3 / 2), SI.const 21 0, SI.const 27 1]
  refine runs_mono (K := sCost l + ((d * 6 + 3) + (1 + (kDf2A d p.j - (d * 6 + 8)))))
    (runs_seq_eq (runs_sprog (L := df2L) (w := w) l (by decide) σ) ?_)
    (by simp only [l, sCost, List.map, SI.cost, List.sum_cons, List.sum_nil]; unfold kDf2A; omega)
    (fun σ' h => h)
  set σ1 : Env d := { σ with sc := sEval σ.nat l σ.sc }
  have F1 : Env.Frame σ σ1 [] [19, 20, 21, 27] [] := ⟨fun _ _ => rfl, fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [σ1, l, sEval, List.foldl, SI.step, SI.dst, SI.val]
    simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2], fun _ _ => rfl, rfl, rfl, rfl⟩
  have s19 : σ1.sc 19 = 1 / 2 := by simp [σ1, l, sEval, SI.step, SI.dst, SI.val]
  have s20 : σ1.sc 20 = 3 / 2 := by simp [σ1, l, sEval, SI.step, SI.dst, SI.val]
  have s21 : σ1.sc 21 = 0 := by simp [σ1, l, sEval, SI.step, SI.dst, SI.val]
  have s27 : σ1.sc 27 = 1 := by simp [σ1, l, sEval, SI.step, SI.dst, SI.val]
  refine runs_seq (runs_vgauss (L := df2L) (w := w) σ1 (dv := 0) (one := 2) (i := 3) (y := 9) (t := 37)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd h1) (fun σ2 h2 => ?_)
  obtain ⟨v9, dr2, n2, s2, a2, r2, p2, -⟩ := h2
  refine runs_seq_eq (runs_gauss (L := df2L) (w := w) (σ := σ2) (x := 29) (by decide)) ?_
  set σ3 : Env d := { σ2.setSc 29 (w.gs σ2.draws) with draws := σ2.draws + 1 } with hσ3
  have F3 : Env.Frame σ { σ3 with draws := σ.draws } [3, 4, 5, 8] ([19, 20, 21] ++ List.range' 27 33)
      [9, 10, 11, 12, 13, 14] := by
    refine ⟨fun i hi => ?_, fun x hx => ?_, fun a ha => ?_, rfl, ?_, ?_⟩
    · show σ2.nat i = _; rw [n2 i (by rintro rfl; simp at hi)]
    · show (σ2.setSc 29 (w.gs σ2.draws)).sc x = _
      have h29 : x ≠ 29 := by rintro rfl; simp at hx
      have h37 : x ≠ 37 := by rintro rfl; simp at hx
      simp only [Env.setSc_sc, h29, ite_false]; rw [s2 x h37, F1.2.1 x (by simp at hx ⊢; omega)]
    · show σ2.arr a = _; rw [a2 a (by rintro rfl; simp at ha)]
    · show σ2.rounds = _; rw [r2]
    · show σ2.pts = _; rw [p2]
  have hd3 : σ3.nat 0 = d := by rw [F3.1 0 (by decide)]; exact hd
  have h13 : σ3.nat 2 = 1 := by rw [F3.1 2 (by decide)]; exact h1
  have e3 : ∀ x, x ∉ [19, 20, 21] ++ List.range' 27 33 → σ3.sc x = σ.sc x := F3.2.1
  have hP3 : PosRep Ps σ3 := (hP.frame F3 (by decide) (by decide) : PosRep Ps { σ3 with draws := σ.draws })
  have hpar3 : ParRep p σ3 := (hpar.frame F3 (by decide) (by decide) : ParRep p { σ3 with draws := σ.draws })
  have h21 : σ3.sc 21 = 0 := by show (σ2.setSc 29 (w.gs σ2.draws)).sc 21 = 0; simp [s2 21 (by decide), s21]
  have h27 : σ3.sc 27 = 1 := by show (σ2.setSc 29 (w.gs σ2.draws)).sc 27 = 1; simp [s2 27 (by decide), s27]
  have h19 : σ3.sc 19 = 1 / 2 := by show (σ2.setSc 29 (w.gs σ2.draws)).sc 19 = _; simp [s2 19 (by decide), s19]
  have h20 : σ3.sc 20 = 3 / 2 := by show (σ2.setSc 29 (w.gs σ2.draws)).sc 20 = _; simp [s2 20 (by decide), s20]
  have v93 : σ3.vec 9 = fun c : Fin d => w.gs (σ.draws + c) := by
    show σ2.vec 9 = _; rw [v9]
  have s293 : σ3.sc 29 = w.gs (σ.draws + d) := by show (σ2.setSc 29 (w.gs σ2.draws)).sc 29 = _; simp [dr2]; rfl
  have dr3 : σ3.draws = σ.draws + (d + 1) := by show σ2.draws + 1 = _; rw [dr2]; rfl
  have fin : ∀ σ' (ns ss as : List ℕ), Env.Frame σ3 σ' ns ss as → (∀ i ∈ ns, i ∈ [3, 4, 5, 8]) →
      (∀ x ∈ ss, x ∈ [19, 20, 21] ++ List.range' 27 33) → (∀ a ∈ as, a ∈ [9, 10, 11, 12, 13, 14]) → 29 ∉ ss →
      9 ∉ as → (∀ x ∈ [19, 20, 21, 27], x ∉ ss) → σ'.vec 9 = (fun c : Fin d => w.gs (σ.draws + c)) ∧
        σ'.sc 29 = w.gs (σ.draws + d) ∧
        σ'.draws = σ.draws + (d + 1) ∧ σ'.vec 9 = σ3.vec 9 ∧ CstRep σ' ∧
        Env.Frame σ { σ' with draws := σ.draws } [3, 4, 5, 8] ([19, 20, 21] ++ List.range' 27 33)
          [9, 10, 11, 12, 13, 14] := fun σ' ns ss as Fb hn hs ha h29 h9 hc =>
    ⟨by rw [Env.Frame.vec_eq Fb h9, v93], by rw [Fb.2.1 29 h29, s293], by rw [Fb.2.2.2.1, dr3],
      Env.Frame.vec_eq Fb h9, ⟨by rw [Fb.2.1 19 (hc 19 (by simp)), h19], by rw [Fb.2.1 20 (hc 20 (by simp)), h20],
        by rw [Fb.2.1 21 (hc 21 (by simp)), h21], by rw [Fb.2.1 27 (hc 27 (by simp)), h27]⟩,
      Env.Frame.trans F3 (Env.Frame.mono (Env.Frame.setDraws Fb σ.draws) hn hs ha)⟩
  cases m with
  | off =>
    have hc : σ3.sc 22 < σ3.sc 19 := by rw [h19, e3 22 (by decide), hm]; norm_num
    refine runs_mono (runs_ifS_t (by decide) (by decide) hc (runs_aOff (w := w) σ3 hd3 h13 h21))
      (by unfold kDf2A; omega) (fun σ' h => ?_)
    obtain ⟨v14, -, Fb⟩ := h
    obtain ⟨a, b, c, e9, cst, f⟩ := fin σ' _ _ _ Fb (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    refine ⟨a, b, c, fun n ft nt ζ => by rw [df2Round_fst, v14]; rfl, trivial, cst, f⟩
  | guard =>
    have hc1 : ¬ σ3.sc 22 < σ3.sc 19 := by rw [h19, e3 22 (by decide), hm]; norm_num
    have hc2 : σ3.sc 22 < σ3.sc 20 := by rw [h20, e3 22 (by decide), hm]; norm_num
    refine runs_mono (runs_ifS_f (by decide) (by decide) hc1 (runs_ifS_t (by decide) (by decide) hc2
      (runs_aGuard (w := w) Ps σ3 hd3 h13 h21 hP3))) (by unfold kDf2A; omega) (fun σ' h => ?_)
    obtain ⟨v14, s28, Fb⟩ := h
    obtain ⟨a, b, c, e9, cst, f⟩ := fin σ' _ _ _ Fb (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    exact ⟨a, b, c, fun n ft nt ζ => by rw [df2Round_fst, v14], s28, cst, f⟩
  | run st =>
    obtain ⟨hm2, hst⟩ := hm
    have hst3 : StRep st σ3 := by
      obtain ⟨t23, t2, t3, t4, t5, t6, t24, t7, t25, t8, t26⟩ := hst
      refine ⟨by rw [e3 23 (by decide), t23], by rw [← t2]; exact Env.Frame.vec_eq F3 (by decide),
        by rw [← t3]; exact Env.Frame.mat_eq F3 (by decide), by rw [← t4]; exact Env.Frame.mat_eq F3 (by decide),
        by rw [← t5]; exact Env.Frame.mat_eq F3 (by decide), by rw [← t6]; exact Env.Frame.vec_eq F3 (by decide),
        by rw [e3 24 (by decide), t24], by rw [← t7]; exact Env.Frame.vec_eq F3 (by decide),
        by rw [e3 25 (by decide), t25], by rw [← t8]; exact Env.Frame.vec_eq F3 (by decide),
        by rw [e3 26 (by decide), t26]⟩
    have hc1 : ¬ σ3.sc 22 < σ3.sc 19 := by rw [h19, e3 22 (by decide), hm2]; norm_num
    have hc2 : ¬ σ3.sc 22 < σ3.sc 20 := by rw [h20, e3 22 (by decide), hm2]; norm_num
    refine runs_mono (runs_ifS_f (by decide) (by decide) hc1 (runs_ifS_f (by decide) (by decide) hc2
      (runs_aRun (w := w) Ps p st σ3 hd3 h13 h21 h27 hP3 hpar3 hst3))) (by unfold kDf2A; omega)
      (fun σ' h => ?_)
    obtain ⟨v10, s30, v14, s28, Fb⟩ := h
    obtain ⟨a, b, c, e9, cst, f⟩ := fin σ' _ _ _ Fb (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    have hpt : σ'.sc 30 = df2Pt p w.K Ps st (σ'.vec 9) := by rw [s30, e9]; rfl
    have hpnt : pgMu Ps + pgOp Ps (WithLp.toLp 2 ((σ'.sc 30)⁻¹ • (st.mu + (1 - p.lam) • (st.A *ᵥ σ3.vec 9)))) =
        df2Pnt p w.K Ps st (σ'.vec 9) := by rw [hpt, e9]; rfl
    refine ⟨a, b, c, fun n ft nt ζ => by rw [df2Round_fst, v14, hpnt], ⟨by rw [v10, e9], hpt, by rw [s28, hpnt]⟩,
      cst, f⟩


/-! ## Part B of a round: the observation and the next mode

Scalars: `31` holds `Y`, `32` the observation; `60` to `108` the steps of `df2Next`; `110` to `120` the membership
codes of the regions; AP from `192`. Arrays: `15` the vector `u = P w`; `80` to `92` the new fields and the
temporaries (`P', Σ', A', b', Ĝ'` in `80` to `84`, `z` in `86`, the point of AP in `87`, `ctr'` in `90`, `w_μ` in `91`,
the new `μ` in `92`), `93` the input of the membership codes, `95` their product `P y`. -/

open SI in
/-- `Y := pt (O + ζ)/2 + 2 (pt - 1)/ε`, `ζ = g/2`, from the observation (scalar `32`). -/
def yCode : Cmd :=
  sprog df2L [op2 .mul 60 29 19, op2 .add 60 32 60, op2 .mul 60 30 60, op2 .mul 60 60 19, op2 .sub 61 30 27,
    const 62 2, op2 .mul 61 62 61, op2 .div 61 61 10, op2 .add 31 60 61]

/-- The mode guard. -/
def toGuard : Cmd := sconst df2L 22 1

/-- `y ∈ K_ε` for the array `93`, the answer in the scalar `40`: `12 := 93/(1 - ε)` (the scalar `110` holds
`1/(1 - ε)`), then `memKp`. -/
def memKeps : Cmd := .seq (vcopy df2L 0 2 3 12 93 37) (.seq (vscale df2L 0 2 3 12 110 37) memKp)

open SI in
/-- `116 := [y ∈ K_ε ∧ Φ(y) ≤ thr]` after `memKeps`, `Φ(y) = ½ yᵀ P y - bᵀ y + k` from the array `Pa`, the array `ba`,
the scalar `kv` and the threshold in the scalar `thr`. -/
def phiTest (Pa ba kv thr : ℕ) : Cmd :=
  .seq (matvec df2L 0 2 3 4 5 95 Pa 93 117 118 119) <|
  .seq (vdot df2L 0 2 3 114 93 95 118 119) <|
  .seq (vdot df2L 0 2 3 115 ba 93 118 119) <|
  .seq (sprog df2L [op2 .mul 113 114 19, op2 .sub 113 113 115, op2 .add 113 113 kv]) <|
  ifS df2L thr 113 (sconst df2L 116 0) (smov df2L 116 40)

/-- The membership code of the region `R⁻` of the first call of AP: `K_ε` in the first round of an epoch, else
`K_ε ∩ {Φ_{t-1} ≤ (c₁ - γ) ρ}` (threshold in the scalar `111`). -/
def memRm : Cmd := .seq memKeps (ifS df2L 21 23 (smov df2L 116 40) (phiTest 3 6 24 111))

/-- The membership code of the region `R_{t+1}` of the second call of AP: `K_ε ∩ {Φ_t ≤ c₁ ρ}` (threshold in the
scalar `112`), `Φ_t` from `P', b', k'`. -/
def memRp : Cmd := .seq memKeps (phiTest 80 83 81 112)

/-- The variables of the first call of AP: centre `ctr`, matrix `P'`, point `z`, radius `r`, cap `R`, accuracy in
the scalar `91`, answer in `92` and the array `87`. -/
def apV1 : AP.APVars :=
  { dv := 0, one := 2, nB := 14, sB := 192, aB := 16, a0 := 8, P := 80, w := 86, out := 87, qv := 93, r := 26,
    R := 17, e := 91, ok := 92, qo := 116 }

/-- The variables of the second call of AP: centre `ctr'`, matrix `P'`, point `w_μ`, radius `r'` (scalar `100`),
cap `R`, accuracy in the scalar `106`, answer in `108` and the array `92`. -/
def apV2 : AP.APVars :=
  { dv := 0, one := 2, nB := 14, sB := 192, aB := 16, a0 := 90, P := 80, w := 91, out := 92, qv := 93, r := 100,
    R := 17, e := 106, ok := 108, qo := 116 }

open SI in
/-- The scalars of `df2Next` before its first test: `u := P w` (array `15`), `|ξ|²` (`63`), `1 - λ` (`64`),
`c = η κ λ κ₀ Y` (`65`), `a = 1 - c` (`66`), `q = a + c |ξ|²` (`67`). -/
def nx1 : Cmd :=
  .seq (matvec df2L 0 2 3 4 5 15 3 10 35 37 38) <|
  .seq (vdot df2L 0 2 3 63 9 9 37 38) <|
  sprog df2L [op2 .sub 64 27 6, op2 .mul 65 7 11, op2 .mul 65 65 6, op2 .mul 65 65 16, op2 .mul 65 65 31,
    op2 .sub 66 27 65, op2 .mul 67 65 63, op2 .add 67 66 67]

/-- `P' = a P + c u uᵀ` (array `80`). -/
def nx2P : Cmd := .seq (mcopy df2L 9 2 3 80 3 37) (rankOne df2L 0 2 3 4 5 80 66 65 15 15 37 38 35)

open SI in
/-- The scalars of `Σ'`. -/
def nx2SL : List SI := [op2 .div 68 27 66, op2 .div 69 65 67, op2 .mul 70 69 68, op2 .sub 70 21 70]

/-- `Σ' = a⁻¹ Σ - (c/q) a⁻¹ w wᵀ` (array `81`). -/
def nx2S : Cmd :=
  .seq (sprog df2L nx2SL) (.seq (mcopy df2L 9 2 3 81 4 37) (rankOne df2L 0 2 3 4 5 81 68 70 10 10 37 38 35))

open SI in
/-- The scalars of `A'`. -/
def nx2AL : List SI := [op2 .div 71 66 67, op1 .sqrt 71 71, op2 .add 71 27 71, op2 .div 72 69 71, op1 .sqrt 73 66,
    op2 .div 74 27 73, op2 .mul 75 72 74, op2 .sub 75 21 75]

/-- `A' = (√a)⁻¹ A - c' (√a)⁻¹ w ξᵀ` (array `82`). -/
def nx2A : Cmd :=
  .seq (sprog df2L nx2AL) (.seq (mcopy df2L 9 2 3 82 5 37) (rankOne df2L 0 2 3 4 5 82 74 75 10 9 37 38 35))

open SI in
/-- The scalars of `b'`, `k'`, `Ĝ'`, `l'`. -/
def nx2BL : List SI := [op2 .mul 78 65 76, op2 .sub 79 21 65, op2 .mul 80 76 76, op2 .sub 80 80 77,
    op2 .mul 80 80 65, op2 .mul 80 80 19, op2 .add 81 24 80, op2 .div 82 31 64, op2 .mul 83 82 76,
    op2 .add 84 25 83]

/-- `b' = b + c (u·μ) u - c P μ` (array `83`), `k'` (scalar `81`), `Ĝ' = Ĝ + (Y/(1 - λ)) u` (array `84`),
`l'` (scalar `84`). -/
def nx2B : Cmd :=
  .seq (matvec df2L 0 2 3 4 5 89 3 2 35 37 38) <|
  .seq (vdot df2L 0 2 3 76 15 2 37 38) <|
  .seq (vdot df2L 0 2 3 77 2 89 37 38) <|
  .seq (sprog df2L nx2BL) <|
  .seq (vcopy df2L 0 2 3 83 6 37) <|
  .seq (vaxpy df2L 0 2 3 83 15 78 37 38) <|
  .seq (vaxpy df2L 0 2 3 83 89 79 37 38) <|
  .seq (vcopy df2L 0 2 3 84 7 37) (vaxpy df2L 0 2 3 84 15 82 37 38)

/-- The updates: `P' = a P + c u uᵀ`, `Σ' = a⁻¹ Σ - (c/q) a⁻¹ w wᵀ`, `A' = (√a)⁻¹ A - c' (√a)⁻¹ w ξᵀ`,
`b' = b + c (u·μ) u - c P μ`, `k'`, `Ĝ' = Ĝ + (Y/(1 - λ)) u`, `l'`. -/
def nx2 : Cmd := .seq nx2P (.seq nx2S (.seq nx2A nx2B))

open SI in
/-- The traces of `P'`, `Σ'` (`85`, `86`) and `d/δ_e` (`87`). -/
def nx3 : Cmd :=
  .seq (mtrace df2L 0 2 3 5 85 80 37) <|
  .seq (mtrace df2L 0 2 3 5 86 81 37) (sprog df2L [cast 87 0, op2 .div 87 87 4])

open SI in
/-- `z = Σ' (b' - (η/2) Ĝ')` (array `86`), `|z|` (`89`), `R/δ_e³` (`90`). -/
def nx4 : Cmd :=
  .seq (vcopy df2L 0 2 3 85 83 37) <|
  .seq (sprog df2L [op2 .mul 88 7 19, op2 .sub 88 21 88]) <|
  .seq (vaxpy df2L 0 2 3 85 84 88 37 38) <|
  .seq (matvec df2L 0 2 3 4 5 86 81 85 35 37 38) <|
  .seq (vnorm df2L 0 2 3 89 86 37 38) <|
  sprog df2L [op2 .mul 90 4 4, op2 .mul 90 90 4, op2 .div 90 17 90]

open SI in
/-- The constants of the regions and the accuracy of the first call: `1/(1 - ε)` (`110`), `(c₁ - γ) ρ` (`111`),
`c₁ ρ` (`112`), `min 1 (α ρ/2)` (`91`). -/
def nx5 : Cmd :=
  sprog df2L [op2 .sub 110 27 10, op2 .div 110 27 110, op2 .sub 111 14 15, op2 .mul 111 111 9, op2 .mul 112 14 9,
    op2 .mul 91 13 9, op2 .mul 91 91 19, .smin 91 27 91]

open SI in
/-- The restart test from the point `pt` of AP (array `87`): `η (l' - Ĝ'·pt) - 2 Φ_t(pt)` (`96`) against
`-(θ ρ)` (`98`). -/
def nx6 : Cmd :=
  .seq (vdot df2L 0 2 3 93 84 87 37 38) <|
  .seq (matvec df2L 0 2 3 4 5 88 80 87 35 37 38) <|
  .seq (vdot df2L 0 2 3 94 87 88 37 38) <|
  .seq (vdot df2L 0 2 3 95 83 87 37 38) <|
  sprog df2L [op2 .sub 96 84 93, op2 .mul 96 7 96, op2 .mul 97 94 19, op2 .sub 97 97 95, op2 .add 97 97 81,
    const 102 2, op2 .mul 97 102 97, op2 .sub 96 96 97, op2 .mul 98 12 9, op2 .sub 98 21 98]

open SI in
/-- The second ball and `w_μ`: `ctr' = (1 - s_b) pt` (array `90`), `r' = s_b (1 - ε)` (`100`),
`w_μ = μ - (η Y/((1 - λ) q)) w` (array `91`), `|w_μ|` (`103`) and its cap `R + η √(16 d n L_e/δ_e)` (`104`). -/
def nx7 : Cmd :=
  .seq (sprog df2L [op2 .sub 99 27 18, op2 .sub 100 27 10, op2 .mul 100 18 100, op2 .mul 101 7 31,
    op2 .mul 102 64 67, op2 .div 101 101 102, op2 .sub 101 21 101]) <|
  .seq (vcopy df2L 0 2 3 90 87 37) <|
  .seq (vscale df2L 0 2 3 90 99 37) <|
  .seq (vcopy df2L 0 2 3 91 2 37) <|
  .seq (vaxpy df2L 0 2 3 91 10 101 37 38) <|
  .seq (vnorm df2L 0 2 3 103 91 37 38) <|
  sprog df2L [const 104 16, cast 105 0, op2 .mul 104 104 105, cast 105 1, op2 .mul 104 104 105,
    op2 .mul 104 104 5, op2 .div 104 104 4, op1 .sqrt 104 104, op2 .mul 104 7 104, op2 .add 104 17 104]

open SI in
/-- The accuracy of the second call, `1/(16 n² max 1 (4 R² tr P'))` (`106`). -/
def nx8 : Cmd :=
  sprog df2L [const 106 4, op2 .mul 107 17 17, op2 .mul 106 106 107, op2 .mul 106 106 85, .smax 106 27 106,
    const 107 16, cast 105 1, op2 .mul 105 105 105, op2 .mul 107 107 105, op2 .mul 107 107 106,
    op2 .div 106 27 107]

/-- The new state of an epoch from the new fields. -/
def nxCommit : Cmd :=
  .seq (sconst df2L 23 0) <|
  .seq (vcopy df2L 0 2 3 2 92 37) <|
  .seq (mcopy df2L 9 2 3 3 80 37) <|
  .seq (mcopy df2L 9 2 3 4 81 37) <|
  .seq (mcopy df2L 9 2 3 5 82 37) <|
  .seq (vcopy df2L 0 2 3 6 83 37) <|
  .seq (smov df2L 24 81) <|
  .seq (vcopy df2L 0 2 3 7 84 37) <|
  .seq (smov df2L 25 84) <|
  .seq (vcopy df2L 0 2 3 8 90 37) (smov df2L 26 100)


open SI in
/-- The start of an epoch (`df2Init`): `first := 1`, `μ, b, Ĝ, ctr := 0`, `k, l := 0`, `r := 1 - ε`,
`P := σ⁻² I`, `Σ := σ² I`, `A := σ I`. -/
def stInit : Cmd :=
  .seq (sprog df2L [const 23 1, const 24 0, const 25 0, op2 .sub 26 27 10, op2 .div 56 27 8, op1 .sqrt 57 8]) <|
  .seq (vfill df2L 0 2 3 2 21) <|
  .seq (vfill df2L 0 2 3 6 21) <|
  .seq (vfill df2L 0 2 3 7 21) <|
  .seq (vfill df2L 0 2 3 8 21) <|
  .seq (mfill df2L 9 2 3 3 21) <|
  .seq (mdiag df2L 0 2 3 5 3 56) <|
  .seq (mfill df2L 9 2 3 4 21) <|
  .seq (mdiag df2L 0 2 3 5 4 8) <|
  .seq (mfill df2L 9 2 3 5 21) (mdiag df2L 0 2 3 5 5 57)

/-- After the second call of AP. -/
def nxC6 : Cmd := .seq nx8 (.seq (AP.apCode df2L memRp apV2) (ifS df2L 21 108 nxCommit toGuard))

/-- After the restart test. -/
def nxC5 : Cmd := .seq nx7 (ifS df2L 104 103 toGuard nxC6)

/-- After the first call of AP. -/
def nxC4 : Cmd := .seq nx6 (ifS df2L 98 96 nxC5 stInit)

/-- After the test on `z`. -/
def nxC3 : Cmd := .seq nx5 (.seq (AP.apCode df2L memRm apV1) (ifS df2L 21 92 nxC4 toGuard))

/-- After the test on the traces. -/
def nxC2 : Cmd := .seq nx4 (ifS df2L 90 89 toGuard nxC3)

/-- After the test on `a` and `q`. -/
def nxC1 : Cmd := .seq nx2 (.seq nx3 (ifS df2L 87 85 toGuard (ifS df2L 87 86 toGuard nxC2)))

/-- `df2Next` in VL. -/
def nextCode : Cmd := .seq nx1 (ifS df2L 21 66 (ifS df2L 21 67 nxC1 toGuard) toGuard)

/-- Part B of a round: off, nothing; guard, off unless the test passed; run, off unless the test passed, else `Y`
and `df2Next`. -/
def df2B : Cmd :=
  ifS df2L 22 19 .skip (ifS df2L 22 20 (ifS df2L 21 28 .skip (sconst df2L 22 0))
    (ifS df2L 21 28 (.seq yCode nextCode) (sconst df2L 22 0)))

/-! ## `df2Next` in stages, as the code runs it -/

/-- The new fields of a round of DF2 after its first test. -/
structure NxF (d : ℕ) where
  P : Matrix (Fin d) (Fin d) ℝ
  S : Matrix (Fin d) (Fin d) ℝ
  A : Matrix (Fin d) (Fin d) ℝ
  b : Fin d → ℝ
  k : ℝ
  G : Fin d → ℝ
  l : ℝ

/-- `c = η κ λ κ₀ Y`. -/
noncomputable def nxC (p : Df2OPar) (Y : ℝ) : ℝ := p.eta * p.kap * p.lam * p.k0 * Y

/-- `q = 1 - c + c |ξ|²`. -/
noncomputable def nxQ (p : Df2OPar) (ξ : Fin d → ℝ) (Y : ℝ) : ℝ := (1 - nxC p Y) + nxC p Y * (ξ ⬝ᵥ ξ)

/-- The new fields `P', Σ', A', b', k', Ĝ', l'`. -/
noncomputable def nxFields (p : Df2OPar) (st : Df2St d) (ξ w : Fin d → ℝ) (Y : ℝ) : NxF d :=
  let u := st.P *ᵥ w
  let g := (Y / (1 - p.lam)) • u
  let c := nxC p Y
  let a := 1 - c
  let q := nxQ p ξ Y
  let c' := c / q / (1 + Real.sqrt (a / q))
  ⟨a • st.P + c • vecMulVec u u, a⁻¹ • (st.S - (c / q) • vecMulVec w w),
    (Real.sqrt a)⁻¹ • (st.A - c' • vecMulVec w ξ), st.b + c • ((u ⬝ᵥ st.mu) • u - st.P *ᵥ st.mu),
    st.k + c / 2 * ((u ⬝ᵥ st.mu) ^ 2 - st.mu ⬝ᵥ (st.P *ᵥ st.mu)), st.G + g, st.l + g ⬝ᵥ st.mu⟩

open Classical in
/-- After the test on `w_μ`: the second call of AP. -/
noncomputable def nxT6 (p : Df2OPar) (n : ℕ) (Keps : Set (Fin d → ℝ)) (F : NxF d) (ctr' : Fin d → ℝ) (r' : ℝ)
    (wmu : Fin d → ℝ) : Df2Mode d :=
  match apCall {y | y ∈ Keps ∧ df2Phi F.P F.b F.k y ≤ p.c1 * p.rho} ctr' r' p.R F.P wmu
      (1 / (16 * n ^ 2 * max 1 (4 * p.R ^ 2 * F.P.trace))) with
  | none => .guard
  | some mu' => .run ⟨false, mu', F.P, F.S, F.A, F.b, F.k, F.G, F.l, ctr', r'⟩

open Classical in
/-- After the restart test: the test on `w_μ`. -/
noncomputable def nxT5 (p : Df2OPar) (n : ℕ) (Keps : Set (Fin d → ℝ)) (F : NxF d) (ctr' : Fin d → ℝ) (r' : ℝ)
    (wmu : Fin d → ℝ) : Df2Mode d :=
  if p.R + p.eta * Real.sqrt (16 * d * n * p.Le / p.δe) < oNorm wmu then .guard else nxT6 p n Keps F ctr' r' wmu

open Classical in
/-- From the point `pt` of the first call: the restart test. -/
noncomputable def nxT4 (p : Df2OPar) (n : ℕ) (Keps : Set (Fin d → ℝ)) (st : Df2St d) (ξ w : Fin d → ℝ) (Y : ℝ)
    (F : NxF d) (pt : Fin d → ℝ) : Df2Mode d :=
  if p.eta * (F.l - F.G ⬝ᵥ pt) - 2 * df2Phi F.P F.b F.k pt ≤ -(p.theta * p.rho) then .run (df2Init p d) else
    nxT5 p n Keps F ((1 - p.sb) • pt) (p.sb * (1 - p.eps)) (st.mu - (p.eta * Y / ((1 - p.lam) * nxQ p ξ Y)) • w)

open Classical in
/-- The region of the first call of AP. -/
noncomputable def nxRm (p : Df2OPar) (Keps : Set (Fin d → ℝ)) (st : Df2St d) : Set (Fin d → ℝ) :=
  if st.first then Keps else {y | y ∈ Keps ∧ df2Phi st.P st.b st.k y ≤ (p.c1 - p.gam) * p.rho}

open Classical in
/-- After the test on `z`: the first call of AP. -/
noncomputable def nxT3 (p : Df2OPar) (n : ℕ) (Keps : Set (Fin d → ℝ)) (st : Df2St d) (ξ w : Fin d → ℝ) (Y : ℝ)
    (F : NxF d) (z : Fin d → ℝ) : Df2Mode d :=
  match apCall (nxRm p Keps st) st.ctr st.r p.R F.P z (min 1 (p.alpha * p.rho / 2)) with
  | none => .guard
  | some pt => nxT4 p n Keps st ξ w Y F pt

open Classical in
/-- After the test on the traces: `z` and its test. -/
noncomputable def nxT2 (p : Df2OPar) (n : ℕ) (Keps : Set (Fin d → ℝ)) (st : Df2St d) (ξ w : Fin d → ℝ) (Y : ℝ)
    (F : NxF d) : Df2Mode d :=
  if p.R / p.δe ^ 3 < oNorm (F.S *ᵥ (F.b - (p.eta / 2) • F.G)) then .guard else
    nxT3 p n Keps st ξ w Y F (F.S *ᵥ (F.b - (p.eta / 2) • F.G))

open Classical in
/-- After the test on `a` and `q`: the test on the traces. -/
noncomputable def nxT1 (p : Df2OPar) (n : ℕ) (Keps : Set (Fin d → ℝ)) (st : Df2St d) (ξ w : Fin d → ℝ) (Y : ℝ)
    (F : NxF d) : Df2Mode d :=
  if d / p.δe < F.P.trace ∨ d / p.δe < F.S.trace then .guard else nxT2 p n Keps st ξ w Y F

open Classical in
/-- `df2Next` in stages. -/
theorem df2Next_eq (p : Df2OPar) (n : ℕ) (Keps : Set (Fin d → ℝ)) (st : Df2St d) (ξ w : Fin d → ℝ) (Y : ℝ) :
    df2Next p n Keps st ξ w Y = if 1 - nxC p Y ≤ 0 ∨ nxQ p ξ Y ≤ 0 then .guard else
      nxT1 p n Keps st ξ w Y (nxFields p st ξ w Y) := rfl

/-! ## The rules of part B -/

/-- The steps of a block `mcopy`, `rankOne`. -/
def kBlk (d : ℕ) : ℕ := d * d * 7 + 3 + (d * (d * 16 + 6) + 4)

/-- The steps of `nx2B`. -/
def kNx2B (d : ℕ) : ℕ := d * (d * 10 + 9) + 4 + ((d * 9 + 4) + ((d * 9 + 4) + (10 + ((d * 7 + 3) + ((d * 11 + 3) +
  ((d * 11 + 3) + ((d * 7 + 3) + (d * 11 + 3))))))))

/-- The rule of `nx2P`. -/
theorem runs_nx2P (σ : Env d) (hd : σ.nat 0 = d) (h1 : σ.nat 2 = 1) (h9 : σ.nat 9 = d * d) :
    Runs df2L w nx2P σ (d * d * 7 + 3 + (d * (d * 16 + 6) + 4))
      (fun σ' => σ'.mat 80 = σ.sc 66 • σ.mat 3 + σ.sc 65 • vecMulVec (σ.vec 15) (σ.vec 15) ∧
        Env.Frame σ σ' [3, 4, 5] [35, 37, 38] [80]) := by
  refine runs_seq (runs_mcopy (L := df2L) (w := w) σ (dd := 9) (one := 2) (m := 3) (B := 80) (A := 3) (t := 37)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h9 h1)
      (fun σ1 h1' => ?_)
  obtain ⟨e1, F1, -⟩ := h1'
  refine runs_mono (runs_rankOne (L := df2L) (w := w) σ1 (dv := 0) (one := 2) (i := 3) (j := 4) (k := 5) (A := 80)
    (α := 66) (β := 65) (u := 15) (v := 15) (t1 := 37) (t2 := 38) (t3 := 35) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [F1.1 0 (by decide), hd]) (by rw [F1.1 2 (by decide), h1])) le_rfl (fun σ2 h2 => ?_)
  obtain ⟨e2, F2, -⟩ := h2
  refine ⟨?_, Env.Frame.trans (Env.Frame.mono F1 (by simp) (by simp) (by simp))
    (Env.Frame.mono F2 (by simp) (by simp) (by simp))⟩
  rw [e2, e1, F1.2.1 66 (by decide), F1.2.1 65 (by decide), Env.Frame.vec_eq F1 (by decide)]

/-- The rule of `nx2S`. -/
theorem runs_nx2S (σ : Env d) (hd : σ.nat 0 = d) (h1 : σ.nat 2 = 1) (h9 : σ.nat 9 = d * d) (h21 : σ.sc 21 = 0)
    (h27 : σ.sc 27 = 1) :
    Runs df2L w nx2S σ (4 + (d * d * 7 + 3 + (d * (d * 16 + 6) + 4)))
      (fun σ' => σ'.mat 81 = (σ.sc 66)⁻¹ • (σ.mat 4 - (σ.sc 65 / σ.sc 67) • vecMulVec (σ.vec 10) (σ.vec 10)) ∧
        σ'.sc 69 = σ.sc 65 / σ.sc 67 ∧ Env.Frame σ σ' [3, 4, 5] [35, 37, 38, 68, 69, 70] [81]) := by
  refine runs_seq_eq (runs_sprog (L := df2L) (w := w) nx2SL (by decide) σ) ?_
  set σ1 : Env d := { σ with sc := sEval σ.nat nx2SL σ.sc }
  have F1 : Env.Frame σ σ1 [] [68, 69, 70] [] := ⟨fun _ _ => rfl, fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [σ1, nx2SL, sEval, List.foldl, SI.step, SI.dst, SI.val]
    simp [hx.1, hx.2.1, hx.2.2], fun _ _ => rfl, rfl, rfl, rfl⟩
  have s68 : σ1.sc 68 = (σ.sc 66)⁻¹ := by
    simp only [σ1, nx2SL, sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval]
    simp [h27]
  have s69 : σ1.sc 69 = σ.sc 65 / σ.sc 67 := by
    simp only [σ1, nx2SL, sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval]
    simp
  have s70 : σ1.sc 70 = -(σ.sc 65 / σ.sc 67 * (σ.sc 66)⁻¹) := by
    simp only [σ1, nx2SL, sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval]
    simp [h21, h27]
  refine runs_seq (runs_mcopy (L := df2L) (w := w) σ1 (dd := 9) (one := 2) (m := 3) (B := 81) (A := 4) (t := 37)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h9 h1)
      (fun σ2 h2 => ?_)
  obtain ⟨e2, F2, -⟩ := h2
  refine runs_mono (runs_rankOne (L := df2L) (w := w) σ2 (dv := 0) (one := 2) (i := 3) (j := 4) (k := 5) (A := 81)
    (α := 68) (β := 70) (u := 10) (v := 10) (t1 := 37) (t2 := 38) (t3 := 35) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [F2.1 0 (by decide)]; exact hd) (by rw [F2.1 2 (by decide)]; exact h1)) le_rfl (fun σ3 h3 => ?_)
  obtain ⟨e3, F3, -⟩ := h3
  refine ⟨?_, by rw [F3.2.1 69 (by decide), F2.2.1 69 (by decide), s69], Env.Frame.trans
    (Env.Frame.mono F1 (by simp) (by simp) (by simp)) (Env.Frame.trans (Env.Frame.mono F2 (by simp) (by simp)
      (by simp)) (Env.Frame.mono F3 (by simp) (by simp) (by simp)))⟩
  rw [e3, e2, F2.2.1 68 (by decide), F2.2.1 70 (by decide), s68, s70, Env.Frame.vec_eq F2 (by decide)]
  show _ • σ.mat 4 + _ • vecMulVec (σ.vec 10) (σ.vec 10) = _
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

/-- The rule of `nx2A`. -/
theorem runs_nx2A (σ : Env d) (hd : σ.nat 0 = d) (h1 : σ.nat 2 = 1) (h9 : σ.nat 9 = d * d) (h21 : σ.sc 21 = 0)
    (h27 : σ.sc 27 = 1) :
    Runs df2L w nx2A σ (8 + (d * d * 7 + 3 + (d * (d * 16 + 6) + 4)))
      (fun σ' => σ'.mat 82 = (Real.sqrt (σ.sc 66))⁻¹ • (σ.mat 5 - (σ.sc 69 / (1 + Real.sqrt (σ.sc 66 / σ.sc 67))) •
          vecMulVec (σ.vec 10) (σ.vec 9)) ∧
        Env.Frame σ σ' [3, 4, 5] [35, 37, 38, 71, 72, 73, 74, 75] [82]) := by
  refine runs_seq_eq (runs_sprog (L := df2L) (w := w) nx2AL (by decide) σ) ?_
  set σ1 : Env d := { σ with sc := sEval σ.nat nx2AL σ.sc }
  have F1 : Env.Frame σ σ1 [] [71, 72, 73, 74, 75] [] := ⟨fun _ _ => rfl, fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [σ1, nx2AL, sEval, List.foldl, SI.step, SI.dst, SI.val]
    simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2], fun _ _ => rfl, rfl, rfl, rfl⟩
  have s74 : σ1.sc 74 = (Real.sqrt (σ.sc 66))⁻¹ := by
    simp only [σ1, nx2AL, sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval, Op1.eval]
    simp [h27]
  have s75 : σ1.sc 75 = -(σ.sc 69 / (1 + Real.sqrt (σ.sc 66 / σ.sc 67)) * (Real.sqrt (σ.sc 66))⁻¹) := by
    simp only [σ1, nx2AL, sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval, Op1.eval]
    simp [h21, h27]
  refine runs_seq (runs_mcopy (L := df2L) (w := w) σ1 (dd := 9) (one := 2) (m := 3) (B := 82) (A := 5) (t := 37)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h9 h1)
      (fun σ2 h2 => ?_)
  obtain ⟨e2, F2, -⟩ := h2
  refine runs_mono (runs_rankOne (L := df2L) (w := w) σ2 (dv := 0) (one := 2) (i := 3) (j := 4) (k := 5) (A := 82)
    (α := 74) (β := 75) (u := 10) (v := 9) (t1 := 37) (t2 := 38) (t3 := 35) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [F2.1 0 (by decide)]; exact hd) (by rw [F2.1 2 (by decide)]; exact h1)) le_rfl (fun σ3 h3 => ?_)
  obtain ⟨e3, F3, -⟩ := h3
  refine ⟨?_, Env.Frame.trans (Env.Frame.mono F1 (by simp) (by simp) (by simp)) (Env.Frame.trans
    (Env.Frame.mono F2 (by simp) (by simp) (by simp)) (Env.Frame.mono F3 (by simp) (by simp) (by simp)))⟩
  rw [e3, e2, F2.2.1 74 (by decide), F2.2.1 75 (by decide), s74, s75, Env.Frame.vec_eq F2 (by decide),
    Env.Frame.vec_eq F2 (by decide)]
  show _ • σ.mat 5 + _ • vecMulVec (σ.vec 10) (σ.vec 9) = _
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

/-- The rule of `nx2B`. -/
theorem runs_nx2B (σ : Env d) (hd : σ.nat 0 = d) (h1 : σ.nat 2 = 1) (h19 : σ.sc 19 = 1 / 2) (h21 : σ.sc 21 = 0) :
    Runs df2L w nx2B σ (d * (d * 10 + 9) + 4 + ((d * 9 + 4) + ((d * 9 + 4) + (10 + ((d * 7 + 3) + ((d * 11 + 3) +
      ((d * 11 + 3) + ((d * 7 + 3) + (d * 11 + 3)))))))))
      (fun σ' => σ'.vec 83 = σ.vec 6 + σ.sc 65 • ((σ.vec 15 ⬝ᵥ σ.vec 2) • σ.vec 15 - σ.mat 3 *ᵥ σ.vec 2) ∧
        σ'.sc 81 = σ.sc 24 + σ.sc 65 / 2 * ((σ.vec 15 ⬝ᵥ σ.vec 2) ^ 2 - σ.vec 2 ⬝ᵥ (σ.mat 3 *ᵥ σ.vec 2)) ∧
        σ'.vec 84 = σ.vec 7 + (σ.sc 31 / σ.sc 64) • σ.vec 15 ∧
        σ'.sc 84 = σ.sc 25 + (σ.sc 31 / σ.sc 64) * (σ.vec 15 ⬝ᵥ σ.vec 2) ∧
        Env.Frame σ σ' [3, 4, 5] ([35, 37, 38] ++ List.range' 76 9) [83, 84, 89]) := by
  refine runs_seq (runs_matvec (L := df2L) (w := w) σ (dv := 0) (one := 2) (i := 3) (j := 4) (k := 5) (y := 89) (A := 3)
    (x := 2) (s := 35) (t1 := 37) (t2 := 38) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd h1) (fun σ1 h1' => ?_)
  obtain ⟨e1, F1, -⟩ := h1'
  have hd1 : σ1.nat 0 = d := by rw [F1.1 0 (by decide), hd]
  have h11 : σ1.nat 2 = 1 := by rw [F1.1 2 (by decide), h1]
  refine runs_seq (runs_vdot (L := df2L) (w := w) σ1 (dv := 0) (one := 2) (i := 3) (r := 76) (x := 15) (y := 2)
    (t1 := 37) (t2 := 38) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hd1 h11) (fun σ2 h2 => ?_)
  obtain ⟨e2, F2⟩ := h2
  have hd2 : σ2.nat 0 = d := by rw [F2.1 0 (by decide), hd1]
  have h12 : σ2.nat 2 = 1 := by rw [F2.1 2 (by decide), h11]
  refine runs_seq (runs_vdot (L := df2L) (w := w) σ2 (dv := 0) (one := 2) (i := 3) (r := 77) (x := 2) (y := 89)
    (t1 := 37) (t2 := 38) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hd2 h12) (fun σ3 h3 => ?_)
  obtain ⟨e3, F3⟩ := h3
  have hd3 : σ3.nat 0 = d := by rw [F3.1 0 (by decide), hd2]
  have h13 : σ3.nat 2 = 1 := by rw [F3.1 2 (by decide), h12]
  have G3 : Env.Frame σ σ3 [3, 4, 5] ([35, 37, 38] ++ List.range' 76 9) [83, 84, 89] :=
    Env.Frame.trans (Env.Frame.mono F1 (by simp) (by simp) (by simp)) (Env.Frame.trans
      (Env.Frame.mono F2 (by simp) (by simp) (by simp)) (Env.Frame.mono F3 (by simp) (by simp) (by simp)))
  have v89 : σ3.vec 89 = σ.mat 3 *ᵥ σ.vec 2 := by
    rw [Env.Frame.vec_eq F3 (by decide), Env.Frame.vec_eq F2 (by decide), e1]
  have s76 : σ3.sc 76 = σ.vec 15 ⬝ᵥ σ.vec 2 := by
    rw [F3.2.1 76 (by decide), e2, Env.Frame.vec_eq F1 (by decide), Env.Frame.vec_eq F1 (by decide)]
  have s77 : σ3.sc 77 = σ.vec 2 ⬝ᵥ (σ.mat 3 *ᵥ σ.vec 2) := by
    rw [e3, Env.Frame.vec_eq F2 (by decide), Env.Frame.vec_eq F2 (by decide), Env.Frame.vec_eq F1 (by decide), e1]
  refine runs_seq_eq (runs_sprog (L := df2L) (w := w) nx2BL (by decide) σ3) ?_
  set σ4 : Env d := { σ3 with sc := sEval σ3.nat nx2BL σ3.sc }
  have F4 : Env.Frame σ3 σ4 [] (List.range' 78 7) [] := ⟨fun _ _ => rfl, fun x hx => by
    simp only [List.range', List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp only [σ4, nx2BL, sEval, List.foldl, SI.step, SI.dst, SI.val]
    simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2],
    fun _ _ => rfl, rfl, rfl, rfl⟩
  have k65 : σ3.sc 65 = σ.sc 65 := G3.2.1 65 (by decide)
  have s78 : σ4.sc 78 = σ.sc 65 * (σ.vec 15 ⬝ᵥ σ.vec 2) := by
    simp only [σ4, nx2BL, sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval]
    simp [k65, s76]
  have s79 : σ4.sc 79 = -σ.sc 65 := by
    simp only [σ4, nx2BL, sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval]
    simp [k65, G3.2.1 21 (by decide), h21]
  have s81 : σ4.sc 81 = σ.sc 24 + σ.sc 65 / 2 * ((σ.vec 15 ⬝ᵥ σ.vec 2) ^ 2 - σ.vec 2 ⬝ᵥ (σ.mat 3 *ᵥ σ.vec 2)) := by
    simp only [σ4, nx2BL, sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval]
    simp [k65, s76, s77, G3.2.1 19 (by decide), h19, G3.2.1 24 (by decide)]
    ring
  have s82 : σ4.sc 82 = σ.sc 31 / σ.sc 64 := by
    simp only [σ4, nx2BL, sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval]
    simp [G3.2.1 31 (by decide), G3.2.1 64 (by decide)]
  have s84 : σ4.sc 84 = σ.sc 25 + (σ.sc 31 / σ.sc 64) * (σ.vec 15 ⬝ᵥ σ.vec 2) := by
    simp only [σ4, nx2BL, sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval]
    simp [s76, G3.2.1 31 (by decide), G3.2.1 64 (by decide), G3.2.1 25 (by decide)]
  have G4 : Env.Frame σ σ4 [3, 4, 5] ([35, 37, 38] ++ List.range' 76 9) [83, 84, 89] :=
    Env.Frame.trans G3 (Env.Frame.mono F4 (by simp) (by intro x hx; simp at hx ⊢; omega) (by simp))
  have v4 : ∀ a ∈ [2, 6, 7, 15], σ4.vec a = σ.vec a := by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rw [show σ4.vec a = σ3.vec a from rfl]
    rcases ha with rfl | rfl | rfl | rfl <;> exact Env.Frame.vec_eq G3 (by decide)
  refine runs_seq (runs_vcopy (L := df2L) (w := w) σ4 (dv := 0) (one := 2) (i := 3) (y := 83) (x := 6) (t := 37)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd3 h13)
      (fun σ5 h5 => ?_)
  obtain ⟨e5, F5, -⟩ := h5
  have hd5 : σ5.nat 0 = d := by rw [F5.1 0 (by decide)]; exact hd3
  have h15 : σ5.nat 2 = 1 := by rw [F5.1 2 (by decide)]; exact h13
  refine runs_seq (runs_vaxpy (L := df2L) (w := w) σ5 (dv := 0) (one := 2) (i := 3) (y := 83) (x := 15) (α := 78)
    (t1 := 37) (t2 := 38) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hd5 h15) (fun σ6 h6 => ?_)
  obtain ⟨e6, F6, -⟩ := h6
  have hd6 : σ6.nat 0 = d := by rw [F6.1 0 (by decide)]; exact hd5
  have h16 : σ6.nat 2 = 1 := by rw [F6.1 2 (by decide)]; exact h15
  refine runs_seq (runs_vaxpy (L := df2L) (w := w) σ6 (dv := 0) (one := 2) (i := 3) (y := 83) (x := 89) (α := 79)
    (t1 := 37) (t2 := 38) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hd6 h16) (fun σ7 h7 => ?_)
  obtain ⟨e7, F7, -⟩ := h7
  have hd7 : σ7.nat 0 = d := by rw [F7.1 0 (by decide)]; exact hd6
  have h17 : σ7.nat 2 = 1 := by rw [F7.1 2 (by decide)]; exact h16
  refine runs_seq (runs_vcopy (L := df2L) (w := w) σ7 (dv := 0) (one := 2) (i := 3) (y := 84) (x := 7) (t := 37)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd7 h17)
      (fun σ8 h8 => ?_)
  obtain ⟨e8, F8, -⟩ := h8
  have hd8 : σ8.nat 0 = d := by rw [F8.1 0 (by decide)]; exact hd7
  have h18 : σ8.nat 2 = 1 := by rw [F8.1 2 (by decide)]; exact h17
  refine runs_mono (runs_vaxpy (L := df2L) (w := w) σ8 (dv := 0) (one := 2) (i := 3) (y := 84) (x := 15) (α := 82)
    (t1 := 37) (t2 := 38) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hd8 h18) le_rfl (fun σ9 h9 => ?_)
  obtain ⟨e9, F9, -⟩ := h9
  have H : Env.Frame σ4 σ9 [3] [37, 38] [83, 84] :=
    Env.Frame.trans (Env.Frame.mono F5 (by simp) (by simp) (by simp)) (Env.Frame.trans
      (Env.Frame.mono F6 (by simp) (by simp) (by simp)) (Env.Frame.trans
        (Env.Frame.mono F7 (by simp) (by simp) (by simp)) (Env.Frame.trans
          (Env.Frame.mono F8 (by simp) (by simp) (by simp)) (Env.Frame.mono F9 (by simp) (by simp) (by simp)))))
  have u5 : σ5.vec 15 = σ.vec 15 := by rw [Env.Frame.vec_eq F5 (by decide)]; exact v4 15 (by simp)
  refine ⟨?_, ?_, ?_, ?_, Env.Frame.trans G4 (Env.Frame.mono H (by simp) (by simp) (by simp))⟩
  · rw [Env.Frame.vec_eq F9 (by decide), Env.Frame.vec_eq F8 (by decide), e7, e6, e5, F6.2.1 79 (by decide),
      F5.2.1 79 (by decide), F5.2.1 78 (by decide), s78, s79, u5, Env.Frame.vec_eq F6 (by decide),
      Env.Frame.vec_eq F5 (by decide), show σ4.vec 89 = σ3.vec 89 from rfl, v89, v4 6 (by simp)]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  · rw [H.2.1 81 (by decide), s81]
  · have u8 : σ8.vec 15 = σ.vec 15 := by
      rw [Env.Frame.vec_eq (a := 15) F8 (by decide), Env.Frame.vec_eq (a := 15) F7 (by decide),
        Env.Frame.vec_eq (a := 15) F6 (by decide), u5]
    have w7 : σ7.vec 7 = σ.vec 7 := by
      rw [Env.Frame.vec_eq (a := 7) F7 (by decide), Env.Frame.vec_eq (a := 7) F6 (by decide),
        Env.Frame.vec_eq (a := 7) F5 (by decide)]
      exact v4 7 (by simp)
    rw [e9, e8, F8.2.1 82 (by decide), F7.2.1 82 (by decide), F6.2.1 82 (by decide), F5.2.1 82 (by decide), s82,
      u8, w7]
  · rw [H.2.1 84 (by decide), s84]

/-- The new fields in the arrays `80` to `84` and the scalars `81`, `84`. -/
def NxRep (F : NxF d) (σ : Env d) : Prop :=
  σ.mat 80 = F.P ∧ σ.mat 81 = F.S ∧ σ.mat 82 = F.A ∧ σ.vec 83 = F.b ∧ σ.sc 81 = F.k ∧ σ.vec 84 = F.G ∧ σ.sc 84 = F.l

/-- The rule of `nx2`: the new fields `nxFields`. -/
theorem runs_nx2 (p : Df2OPar) (st : Df2St d) (ξ wv : Fin d → ℝ) (Y : ℝ) (σ : Env d) (hd : σ.nat 0 = d)
    (h1 : σ.nat 2 = 1) (h9 : σ.nat 9 = d * d) (h19 : σ.sc 19 = 1 / 2) (h21 : σ.sc 21 = 0) (h27 : σ.sc 27 = 1)
    (hst : StRep st σ) (hξ : σ.vec 9 = ξ) (hw : σ.vec 10 = wv) (hu : σ.vec 15 = st.P *ᵥ wv) (hY : σ.sc 31 = Y)
    (h64 : σ.sc 64 = 1 - p.lam) (h65 : σ.sc 65 = nxC p Y) (h66 : σ.sc 66 = 1 - nxC p Y)
    (h67 : σ.sc 67 = nxQ p ξ Y) :
    Runs df2L w nx2 σ (d * d * 79 + d * 92 + 70) (fun σ' => NxRep (nxFields p st ξ wv Y) σ' ∧
      Env.Frame σ σ' [3, 4, 5] ([35, 37, 38] ++ List.range' 68 17) [80, 81, 82, 83, 84, 89]) := by
  obtain ⟨-, hmu, hP, hS, hA, hb, hk, hG, hl, -, -⟩ := hst
  refine runs_mono (K := kBlk d + ((4 + kBlk d) + ((8 + kBlk d) + kNx2B d)))
    (runs_seq (runs_nx2P (w := w) σ hd h1 h9) (fun σ1 h1' => ?_)) (le_of_eq (by simp only [kBlk, kNx2B]; ring))
    (fun σ' h => h)
  obtain ⟨P1, F1⟩ := h1'
  have G1 : Env.Frame σ σ1 [3, 4, 5] ([35, 37, 38] ++ List.range' 68 17) [80, 81, 82, 83, 84, 89] :=
    Env.Frame.mono F1 (by simp) (by simp) (by simp)
  refine runs_seq (runs_nx2S (w := w) σ1 (by rw [G1.1 0 (by decide), hd]) (by rw [G1.1 2 (by decide), h1])
    (by rw [G1.1 9 (by decide), h9]) (by rw [G1.2.1 21 (by decide), h21]) (by rw [G1.2.1 27 (by decide), h27]))
    (fun σ2 h2 => ?_)
  obtain ⟨S2, s69, F2⟩ := h2
  have G2 : Env.Frame σ σ2 [3, 4, 5] ([35, 37, 38] ++ List.range' 68 17) [80, 81, 82, 83, 84, 89] :=
    Env.Frame.trans G1 (Env.Frame.mono F2 (by simp) (by intro x hx; simp at hx ⊢; omega) (by simp))
  refine runs_seq (runs_nx2A (w := w) σ2 (by rw [G2.1 0 (by decide), hd]) (by rw [G2.1 2 (by decide), h1])
    (by rw [G2.1 9 (by decide), h9]) (by rw [G2.2.1 21 (by decide), h21]) (by rw [G2.2.1 27 (by decide), h27]))
    (fun σ3 h3 => ?_)
  obtain ⟨A3, F3⟩ := h3
  have G3 : Env.Frame σ σ3 [3, 4, 5] ([35, 37, 38] ++ List.range' 68 17) [80, 81, 82, 83, 84, 89] :=
    Env.Frame.trans G2 (Env.Frame.mono F3 (by simp) (by intro x hx; simp at hx ⊢; omega) (by simp))
  refine runs_mono (runs_nx2B (w := w) σ3 (by rw [G3.1 0 (by decide), hd]) (by rw [G3.1 2 (by decide), h1])
    (by rw [G3.2.1 19 (by decide), h19]) (by rw [G3.2.1 21 (by decide), h21])) le_rfl (fun σ4 h4 => ?_)
  obtain ⟨b4, k4, G4', l4, F4⟩ := h4
  have G4 : Env.Frame σ σ4 [3, 4, 5] ([35, 37, 38] ++ List.range' 68 17) [80, 81, 82, 83, 84, 89] :=
    Env.Frame.trans G3 (Env.Frame.mono F4 (by simp) (by intro x hx; simp at hx ⊢; omega) (by simp))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, G4⟩
  · rw [Env.Frame.mat_eq F4 (by decide), Env.Frame.mat_eq F3 (by decide), Env.Frame.mat_eq F2 (by decide), P1, h66,
      h65, hP, hu]
    rfl
  · rw [Env.Frame.mat_eq F4 (by decide), Env.Frame.mat_eq F3 (by decide), S2, G1.2.1 66 (by decide),
      G1.2.1 65 (by decide), G1.2.1 67 (by decide), Env.Frame.mat_eq G1 (by decide), Env.Frame.vec_eq G1 (by decide),
      h66, h65, h67, hS, hw]
    rfl
  · rw [Env.Frame.mat_eq F4 (by decide), A3, s69, G2.2.1 66 (by decide), G2.2.1 67 (by decide),
      G1.2.1 65 (by decide), G1.2.1 67 (by decide), Env.Frame.mat_eq G2 (by decide),
      Env.Frame.vec_eq (a := 10) G2 (by decide), Env.Frame.vec_eq (a := 9) G2 (by decide), h66, h65, h67, hA, hw, hξ]
    rfl
  · rw [b4, Env.Frame.vec_eq (a := 6) G3 (by decide), G3.2.1 65 (by decide), Env.Frame.vec_eq (a := 15) G3 (by decide),
      Env.Frame.vec_eq (a := 2) G3 (by decide), Env.Frame.mat_eq G3 (by decide), hb, h65, hu, hmu, hP]
    rfl
  · rw [k4, G3.2.1 24 (by decide), G3.2.1 65 (by decide), Env.Frame.vec_eq (a := 15) G3 (by decide),
      Env.Frame.vec_eq (a := 2) G3 (by decide), Env.Frame.mat_eq G3 (by decide), hk, h65, hu, hmu, hP]
    rfl
  · rw [G4', Env.Frame.vec_eq (a := 7) G3 (by decide), G3.2.1 31 (by decide), G3.2.1 64 (by decide),
      Env.Frame.vec_eq (a := 15) G3 (by decide), hG, hY, h64, hu]
    rfl
  · rw [l4, G3.2.1 25 (by decide), G3.2.1 31 (by decide), G3.2.1 64 (by decide),
      Env.Frame.vec_eq (a := 15) G3 (by decide), Env.Frame.vec_eq (a := 2) G3 (by decide), hl, hY, h64, hu, hmu]
    show _ = st.l + ((Y / (1 - p.lam)) • (st.P *ᵥ wv)) ⬝ᵥ st.mu
    rw [smul_dotProduct, smul_eq_mul]

/-- The rule of `nx1`: `u = P w`, `1 - λ`, `c`, `a = 1 - c`, `q`. -/
theorem runs_nx1 (p : Df2OPar) (P : Matrix (Fin d) (Fin d) ℝ) (ξ wv : Fin d → ℝ) (Y : ℝ) (σ : Env d)
    (hd : σ.nat 0 = d) (h1 : σ.nat 2 = 1) (h27 : σ.sc 27 = 1) (hpar : ParRep p σ) (hP : σ.mat 3 = P)
    (hξ : σ.vec 9 = ξ) (hw : σ.vec 10 = wv) (hY : σ.sc 31 = Y) :
    Runs df2L w nx1 σ (d * (d * 10 + 9) + 4 + ((d * 9 + 4) + 8))
      (fun σ' => σ'.vec 15 = P *ᵥ wv ∧ σ'.sc 64 = 1 - p.lam ∧ σ'.sc 65 = nxC p Y ∧ σ'.sc 66 = 1 - nxC p Y ∧
        σ'.sc 67 = nxQ p ξ Y ∧ Env.Frame σ σ' [3, 4, 5] [35, 37, 38, 63, 64, 65, 66, 67] [15]) := by
  refine runs_seq (runs_matvec (L := df2L) (w := w) σ (dv := 0) (one := 2) (i := 3) (j := 4) (k := 5) (y := 15) (A := 3)
    (x := 10) (s := 35) (t1 := 37) (t2 := 38) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd h1) (fun σ1 h1' => ?_)
  obtain ⟨e1, F1, -⟩ := h1'
  have hd1 : σ1.nat 0 = d := by rw [F1.1 0 (by decide), hd]
  have h11 : σ1.nat 2 = 1 := by rw [F1.1 2 (by decide), h1]
  refine runs_seq (runs_vdot (L := df2L) (w := w) σ1 (dv := 0) (one := 2) (i := 3) (r := 63) (x := 9) (y := 9)
    (t1 := 37) (t2 := 38) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hd1 h11) (fun σ2 h2 => ?_)
  obtain ⟨e2, F2⟩ := h2
  refine runs_mono (runs_sprog (L := df2L) (w := w) _ (by decide) σ2) le_rfl (fun σ3 e3 => ?_)
  subst e3
  have G2 : Env.Frame σ σ2 [3, 4, 5] [35, 37, 38, 63] [15] :=
    Env.Frame.trans (Env.Frame.mono F1 (by simp) (by simp) (by simp)) (Env.Frame.mono F2 (by simp) (by simp) (by simp))
  obtain ⟨-, -, -, h6, h7, -, -, -, h11', -, -, -, -, h16, -, -, -⟩ := hpar
  have s63 : σ2.sc 63 = ξ ⬝ᵥ ξ := by rw [e2, Env.Frame.vec_eq F1 (by decide), hξ]
  have r : ∀ x ∈ [6, 7, 11, 16, 21, 27, 31], σ2.sc x = σ.sc x := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact G2.2.1 _ (by decide)
  have c65 : sEval σ2.nat [SI.op2 .sub 64 27 6, SI.op2 .mul 65 7 11, SI.op2 .mul 65 65 6, SI.op2 .mul 65 65 16,
      SI.op2 .mul 65 65 31, SI.op2 .sub 66 27 65, SI.op2 .mul 67 65 63, SI.op2 .add 67 66 67] σ2.sc 65 = nxC p Y := by
    simp only [sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval]
    simp [r 6 (by simp), r 7 (by simp), r 11 (by simp), r 16 (by simp), r 31 (by simp), h6, h7, h11', h16, hY, nxC]
  refine ⟨?_, ?_, c65, ?_, ?_, ?_⟩
  · show σ2.vec 15 = _
    rw [Env.Frame.vec_eq F2 (by decide), e1, hP, hw]
  · simp only [sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval]
    simp [r 27 (by simp), r 6 (by simp), h27, h6]
  · simp only [sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval] at c65 ⊢
    simp at c65 ⊢
    rw [← c65, r 27 (by simp), h27]
  · simp only [sEval, List.foldl, SI.step, SI.dst, SI.val, Function.update_apply, Op2.eval]
    simp [r 27 (by simp), r 6 (by simp), r 7 (by simp), r 11 (by simp), r 16 (by simp), r 31 (by simp), h27, h6, h7,
      h11', h16, hY, s63, nxQ, nxC]
  · exact Env.Frame.trans (Env.Frame.mono G2 (by simp) (by simp) (by simp)) ⟨fun _ _ => rfl, fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp only [sEval, List.foldl, SI.step, SI.dst, SI.val]
      simp [hx.2.2.2.2.1, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2], fun _ _ => rfl, rfl, rfl, rfl⟩

/-- The steps of `memKeps`. -/
def kMemKeps (d : ℕ) : ℕ := d * (d * 10 + 9) + d * 35 + 23

open Classical in
/-- The rule of `memKeps`: the scalar `40` answers whether `110 · y ∈ K'` for the array `93`. -/
theorem runs_memKeps (Ps : PgSp d) (σ : Env d) (hd : σ.nat 0 = d) (h1 : σ.nat 2 = 1) (hP : PosRep Ps σ) :
    Runs df2L w memKeps σ (kMemKeps d) (fun σ' =>
      σ'.sc 40 = (if WithLp.toLp 2 (σ.sc 110 • σ.vec 93) ∈ df2Kp w.K Ps (σ.sc 17) then 1 else 0) ∧
        Env.Frame σ σ' [3, 4, 5] (List.range' 34 7) [12, 13]) := by
  refine runs_mono (K := d * 7 + 3 + (d * 8 + 3 + kMemKp d)) ?_ (le_of_eq (by unfold kMemKeps kMemKp; ring))
    (fun σ' h => h)
  refine runs_seq (runs_vcopy (L := df2L) (w := w) σ (dv := 0) (one := 2) (i := 3) (y := 12) (x := 93) (t := 37)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd h1)
      (fun σ1 h1' => ?_)
  obtain ⟨e1, F1, -⟩ := h1'
  have hd1 : σ1.nat 0 = d := by rw [F1.1 0 (by decide), hd]
  have h11 : σ1.nat 2 = 1 := by rw [F1.1 2 (by decide), h1]
  refine runs_seq (runs_vscale (L := df2L) (w := w) σ1 (dv := 0) (one := 2) (i := 3) (y := 12) (α := 110) (t := 37)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) hd1 h11) (fun σ2 h2 => ?_)
  obtain ⟨e2, F2, -⟩ := h2
  have hd2 : σ2.nat 0 = d := by rw [F2.1 0 (by decide), hd1]
  have h12 : σ2.nat 2 = 1 := by rw [F2.1 2 (by decide), h11]
  refine runs_mono (runs_memKp (w := w) Ps σ2 hd2 h12 ((hP.frame F1 (by decide) (by decide)).frame F2 (by decide)
    (by decide))) le_rfl (fun σ3 h3 => ?_)
  obtain ⟨o3, F3⟩ := h3
  refine ⟨?_, Env.Frame.trans (Env.Frame.mono F1 (by simp) (by simp) (by simp)) (Env.Frame.trans
    (Env.Frame.mono F2 (by simp) (by simp) (by simp)) (Env.Frame.mono F3 (by simp) (by simp) (by simp)))⟩
  rw [o3, e2, e1, F1.2.1 110 (by decide), F2.2.1 17 (by decide), F1.2.1 17 (by decide)]

/-- The scalars that the membership codes of the regions write. -/
def memS : List ℕ := List.range' 34 7 ++ List.range' 113 7

/-- What the membership code of the first call of AP reads: the position, `R`, `1/(1 - ε)`, `1/2`, `0`, `first`,
`P, b, k` and the threshold `(c₁ - γ) ρ`. -/
def Iq1 (p : Df2OPar) (Ps : PgSp d) (st : Df2St d) (σ : Env d) : Prop :=
  PosRep Ps σ ∧ σ.sc 17 = p.R ∧ σ.sc 110 = (1 - p.eps)⁻¹ ∧ σ.sc 19 = 1 / 2 ∧ σ.sc 21 = 0 ∧
    σ.sc 23 = (if st.first then 1 else 0) ∧ σ.mat 3 = st.P ∧ σ.vec 6 = st.b ∧ σ.sc 24 = st.k ∧
    σ.sc 111 = (p.c1 - p.gam) * p.rho

theorem Iq1.frame {p : Df2OPar} {Ps : PgSp d} {st : Df2St d} {σ σ' : Env d} {ns ss as : List ℕ}
    (h : Iq1 p Ps st σ) (hF : Env.Frame σ σ' ns ss as) (hss : ∀ x ∈ [17, 110, 19, 21, 23, 24, 111], x ∉ ss)
    (has : ∀ a ∈ [0, 1, 3, 6], a ∉ as) : Iq1 p Ps st σ' := by
  obtain ⟨hP, h17, h110, h19, h21, h23, h3, h6, h24, h111⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hss has
  exact ⟨hP.frame hF has.1 has.2.1, by rw [hF.2.1 17 hss.1, h17], by rw [hF.2.1 110 hss.2.1, h110],
    by rw [hF.2.1 19 hss.2.2.1, h19], by rw [hF.2.1 21 hss.2.2.2.1, h21], by rw [hF.2.1 23 hss.2.2.2.2.1, h23],
    by rw [Env.Frame.mat_eq hF has.2.2.1, h3], by rw [Env.Frame.vec_eq hF has.2.2.2, h6],
    by rw [hF.2.1 24 hss.2.2.2.2.2.1, h24], by rw [hF.2.1 111 hss.2.2.2.2.2.2, h111]⟩

/-- The steps of the membership codes of the regions. -/
def kMemR (d : ℕ) : ℕ := kMemKeps d + (d * (d * 10 + 9) + d * 18 + 20)

/-- What the membership code of the second call of AP reads: the position, `R`, `1/(1 - ε)`, `1/2`, the new
`P', b', k'` and the threshold `c₁ ρ`. -/
def Iq2 (p : Df2OPar) (Ps : PgSp d) (F : NxF d) (σ : Env d) : Prop :=
  PosRep Ps σ ∧ σ.sc 17 = p.R ∧ σ.sc 110 = (1 - p.eps)⁻¹ ∧ σ.sc 19 = 1 / 2 ∧ σ.mat 80 = F.P ∧ σ.vec 83 = F.b ∧
    σ.sc 81 = F.k ∧ σ.sc 112 = p.c1 * p.rho

theorem Iq2.frame {p : Df2OPar} {Ps : PgSp d} {F : NxF d} {σ σ' : Env d} {ns ss as : List ℕ}
    (h : Iq2 p Ps F σ) (hF : Env.Frame σ σ' ns ss as) (hss : ∀ x ∈ [17, 110, 19, 81, 112], x ∉ ss)
    (has : ∀ a ∈ [0, 1, 80, 83], a ∉ as) : Iq2 p Ps F σ' := by
  obtain ⟨hP, h17, h110, h19, h80, h83, h81, h112⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hss has
  exact ⟨hP.frame hF has.1 has.2.1, by rw [hF.2.1 17 hss.1, h17], by rw [hF.2.1 110 hss.2.1, h110],
    by rw [hF.2.1 19 hss.2.2.1, h19], by rw [Env.Frame.mat_eq hF has.2.2.1, h80],
    by rw [Env.Frame.vec_eq hF has.2.2.2, h83], by rw [hF.2.1 81 hss.2.2.2.1, h81],
    by rw [hF.2.1 112 hss.2.2.2.2, h112]⟩

end AdversarialBco.Poly.Mach.VL
