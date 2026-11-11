/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachAPEll
public import AdversarialBco.Poly.MachSI
public import AdversarialBco.Poly.MachMat

@[expose] public section

/-!
# The subroutine AP in VL: the constants, the start, the end and the loop of ELL-cap

`runs_ellConstsCode` reads the constants `τ`, `ℓ₁`, `N`, `J`, `B` of `ellConsts` off the code, whose scalar blocks are
lists of scalar instructions (`sprogThen`, from `MachSI`); `runs_ellInitCode` the start `A = R² I`, `a = 0`;
`runs_ellFinalCode` the end; `runs_ellCapCode` the whole procedure, through the loop invariant
`ERel ((ellIt ..)^[t] start)`.
-/

namespace AdversarialBco.Poly.AP

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL Matrix

variable {d : ℕ} {L : Layout} {w : World d} {memQ : Cmd} {V : APVars}

/-! ## Scalar blocks followed by a command -/

/-- A list of scalar instructions followed by the command `c`. -/
def sprogThen (L : Layout) (l : List SI) (c : Cmd) : Cmd := l.foldr (fun i acc => .seq (i.cmd L) acc) c

theorem runs_sprogThen (l : List SI) (hl : l.all (SI.ok L) = true) {c : Cmd} {σ : Env d} {K : ℕ}
    {Post : Env d → Prop} (h : Runs L w c { σ with sc := sEval σ.nat l σ.sc } K Post) :
    Runs L w (sprogThen L l c) σ (sCost l + K) Post := by
  induction l generalizing σ with
  | nil => exact runs_mono h (by simp [sCost]) (fun _ h => h)
  | cons i l ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hl
    have key : Runs L w (.seq (i.cmd L) (sprogThen L l c)) σ (i.cost + (sCost l + K)) Post :=
      runs_seq (i.runs_cmd hl.1 σ) (fun σ' e => by subst e; exact ih hl.2 h)
    exact runs_mono key (le_of_eq (by simp [sCost, add_assoc])) (fun _ h => h)

/-- `runs_sprogThen` with the cost of the block given by an equation, so that no cost is computed by unification. -/
theorem runs_sprogThen' (l : List SI) (hl : l.all (SI.ok L) = true) {n : ℕ} (hn : sCost l = n) {c : Cmd} {σ : Env d}
    {K : ℕ} {Post : Env d → Prop} (h : Runs L w c { σ with sc := sEval σ.nat l σ.sc } K Post) :
    Runs L w (sprogThen L l c) σ (n + K) Post := hn ▸ runs_sprogThen l hl h

theorem Env.frame_sEval (σ : Env d) (l : List SI) :
    Env.Frame σ { σ with sc := sEval σ.nat l σ.sc } [] (l.map SI.dst) [] :=
  ⟨fun _ _ => rfl, fun _ hx => sEval_frame _ _ _ hx, fun _ _ => rfl, rfl, rfl, rfl⟩

/-! ## The constants -/

/-- The first scalar block of the constants: `θ`, `ε_Q`, `τ`, `ℓ₁` and the real number whose ceiling is `N - 1`. -/
def consC1 (V : APVars) : List SI :=
  [.op2 .add (V.sB + 110) V.R (V.sB + 110),
   .op2 .mul (V.sB + 107) (V.sB + 107) (V.sB + 110),
   .const (V.sB + 116) 3,
   .op2 .mul (V.sB + 110) (V.sB + 116) (V.sB + 107),
   .op2 .mul (V.sB + 110) (V.sB + 110) V.R,
   .op2 .div (V.sB + 110) V.e (V.sB + 110),
   .const (V.sB + 117) 1,
   .smin (V.sB + 108) (V.sB + 117) (V.sB + 110),
   .op2 .mul (V.sB + 109) (V.sB + 108) V.r,
   .const (V.sB + 116) 2,
   .op2 .div (V.sB + 109) (V.sB + 109) (V.sB + 116),
   .cast (V.sB + 112) V.dv,
   .const (V.sB + 116) 36,
   .op2 .mul (V.sB + 110) V.R V.R,
   .op2 .mul (V.sB + 110) (V.sB + 116) (V.sB + 110),
   .op1 .sqrt (V.sB + 111) (V.sB + 112),
   .op2 .mul (V.sB + 110) (V.sB + 110) (V.sB + 111),
   .op2 .div (V.sB + 100) (V.sB + 109) (V.sB + 110),
   .op2 .mul (V.sB + 101) V.r (V.sB + 109),
   .const (V.sB + 116) 24,
   .op2 .mul (V.sB + 110) (V.sB + 116) V.R,
   .op2 .div (V.sB + 101) (V.sB + 101) (V.sB + 110),
   .const (V.sB + 116) 2,
   .op2 .mul (V.sB + 110) (V.sB + 116) (V.sB + 112),
   .op2 .add (V.sB + 111) (V.sB + 112) (V.sB + 117),
   .op2 .mul (V.sB + 110) (V.sB + 110) (V.sB + 111),
   .op2 .mul (V.sB + 111) (V.sB + 116) V.R,
   .op2 .mul (V.sB + 114) (V.sB + 108) V.r,
   .op2 .div (V.sB + 111) (V.sB + 111) (V.sB + 114),
   .op1 .log (V.sB + 111) (V.sB + 111),
   .op2 .mul (V.sB + 110) (V.sB + 110) (V.sB + 111)]

/-- The second scalar block of the constants: the real number whose ceiling is `J`, and `log 2`. -/
def consC2 (V : APVars) : List SI :=
  [.op2 .mul (V.sB + 110) V.r (V.sB + 100),
   .const (V.sB + 116) 8,
   .op2 .div (V.sB + 110) (V.sB + 116) (V.sB + 110),
   .op1 .log (V.sB + 110) (V.sB + 110),
   .const (V.sB + 116) 2,
   .op1 .log (V.sB + 113) (V.sB + 116),
   .op2 .div (V.sB + 110) (V.sB + 110) (V.sB + 113)]

/-- The third scalar block of the constants: `η_min` and the real number whose ceiling is `B`. -/
def consC3 (V : APVars) : List SI :=
  [.cast (V.sB + 110) (V.nB + 10),
   .op2 .add (V.sB + 110) (V.sB + 110) (V.sB + 117),
   .const (V.sB + 116) 3,
   .op2 .mul (V.sB + 111) (V.sB + 116) (V.sB + 112),
   .op2 .mul (V.sB + 110) (V.sB + 111) (V.sB + 110),
   .const (V.sB + 116) 0,
   .op2 .sub (V.sB + 110) (V.sB + 116) (V.sB + 110),
   .op2 .mul (V.sB + 110) (V.sB + 113) (V.sB + 110),
   .op1 .exp (V.sB + 110) (V.sB + 110),
   .op2 .mul (V.sB + 115) (V.sB + 100) (V.sB + 101),
   .const (V.sB + 116) 1600,
   .op2 .div (V.sB + 115) (V.sB + 115) (V.sB + 116),
   .op2 .mul (V.sB + 115) (V.sB + 115) (V.sB + 110),
   .const (V.sB + 116) 3,
   .op2 .mul (V.sB + 110) (V.sB + 116) V.R,
   .op2 .mul (V.sB + 111) V.r (V.sB + 115),
   .op2 .div (V.sB + 110) (V.sB + 110) (V.sB + 111),
   .op1 .log (V.sB + 110) (V.sB + 110),
   .op2 .div (V.sB + 110) (V.sB + 110) (V.sB + 113)]

theorem ellConstsCode_eq : ellConstsCode L V =
    .seq (mtrace L V.dv V.one V.nB (V.nB + 2) (V.sB + 107) V.P (V.sB + 110)) (
    .seq (vnorm L V.dv V.one V.nB (V.sB + 110) V.w (V.sB + 111) (V.sB + 116)) (
    sprogThen L (consC1 V) (
    .seq (nceil L (V.nB + 9) V.one (V.sB + 110) (V.sB + 114)) (
    .seq (nadd (V.nB + 9) (V.nB + 9) V.one) (
    sprogThen L (consC2 V) (
    .seq (nceil L (V.nB + 10) V.one (V.sB + 110) (V.sB + 114)) (
    sprogThen L (consC3 V) (nceil L (V.nB + 11) V.one (V.sB + 110) (V.sB + 114))))))))) := by
  simp only [ellConstsCode, sprogThen, consC1, consC2, consC3, List.foldr_cons, List.foldr_nil, SI.cmd]

theorem sCost_consC1 : sCost (consC1 V) = 33 := by simp [sCost, consC1, SI.cost]
theorem sCost_consC2 : sCost (consC2 V) = 7 := by simp [sCost, consC2, SI.cost]
theorem sCost_consC3 : sCost (consC3 V) = 19 := by simp [sCost, consC3, SI.cost]

/-- The tactic of the block values: unfold the block, read the updates, the index inequalities by `omega`. -/
macro "cons_val" : tactic => `(tactic| (
  simp (disch := omega) only [sEval, List.foldl_cons, List.foldl_nil, SI.step, SI.dst, SI.val,
    Function.update_self, Function.update_of_ne, Op2.eval, Op1.eval, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero, and_self, and_true, true_and]))

theorem consC1_val (n : ℕ → ℕ) (f : ℕ → ℝ) (hR : V.R < V.sB ∨ V.sB + 128 ≤ V.R)
    (hr : V.r < V.sB ∨ V.sB + 128 ≤ V.r) (he : V.e < V.sB ∨ V.sB + 128 ≤ V.e) :
    sEval n (consC1 V) f (V.sB + 100) = min 1 (f V.e / (3 * (f (V.sB + 107) * (f V.R + f (V.sB + 110))) * f V.R)) *
        f V.r / 2 / (36 * (f V.R * f V.R) * Real.sqrt (n V.dv)) ∧
    sEval n (consC1 V) f (V.sB + 101) = f V.r * (min 1 (f V.e / (3 * (f (V.sB + 107) * (f V.R + f (V.sB + 110))) *
        f V.R)) * f V.r / 2) / (24 * f V.R) ∧
    sEval n (consC1 V) f (V.sB + 110) = 2 * (n V.dv : ℝ) * ((n V.dv : ℝ) + 1) * Real.log (2 * f V.R /
        (min 1 (f V.e / (3 * (f (V.sB + 107) * (f V.R + f (V.sB + 110))) * f V.R)) * f V.r)) ∧
    sEval n (consC1 V) f (V.sB + 112) = n V.dv ∧ sEval n (consC1 V) f (V.sB + 117) = 1 := by
  simp only [consC1]; cons_val

theorem consC2_val (n : ℕ → ℕ) (f : ℕ → ℝ) (hr : V.r < V.sB ∨ V.sB + 128 ≤ V.r) :
    sEval n (consC2 V) f (V.sB + 110) = Real.log (8 / (f V.r * f (V.sB + 100))) / Real.log 2 ∧
    sEval n (consC2 V) f (V.sB + 113) = Real.log 2 := by
  simp only [consC2]; cons_val

theorem consC3_val (n : ℕ → ℕ) (f : ℕ → ℝ) (hR : V.R < V.sB ∨ V.sB + 128 ≤ V.R)
    (hr : V.r < V.sB ∨ V.sB + 128 ≤ V.r) :
    sEval n (consC3 V) f (V.sB + 110) = Real.log (3 * f V.R / (f V.r * (f (V.sB + 100) * f (V.sB + 101) / 1600 *
        Real.exp (f (V.sB + 113) * (0 - 3 * f (V.sB + 112) * ((n (V.nB + 10) : ℝ) + f (V.sB + 117))))))) /
        f (V.sB + 113) := by
  simp only [consC3]; cons_val

theorem ellConsts_code (r R e : ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) {k : EllConsts}
    (hk : ellConsts r R P w e = k) :
    k.τ = min 1 (e / (3 * (P.trace * (R + oNorm w)) * R)) * r / 2 / (36 * (R * R) * Real.sqrt d) ∧
    k.ℓ1 = r * (min 1 (e / (3 * (P.trace * (R + oNorm w)) * R)) * r / 2) / (24 * R) ∧
    k.N = ⌈2 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (2 * R / (min 1 (e / (3 * (P.trace * (R + oNorm w)) * R)) * r))⌉₊
      + 1 ∧
    k.J = ⌈Real.log (8 / (r * k.τ)) / Real.log 2⌉₊ ∧
    k.B = ⌈Real.log (3 * R / (r * (k.τ * k.ℓ1 / 1600 *
      Real.exp (Real.log 2 * (0 - 3 * (d : ℝ) * ((k.J : ℝ) + 1)))))) / Real.log 2⌉₊ := by
  subst hk
  have h2 : ∀ x : ℝ, Real.exp (Real.log 2 * (0 - x)) = (2 : ℝ) ^ (-x) := fun x => by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]; ring_nf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [ellConsts, sq, Real.logb, h2]

/-- The step bound of the constants. -/
def kCons (d N J B : ℕ) : ℕ :=
  (d * 8 + 5) + ((d * 9 + 5) + (33 + (((N - 1) * 4 + 4) + (1 + (7 + ((J * 4 + 4) + (19 + (B * 4 + 4))))))))

/-- The natural variables the constants write. -/
abbrev consN (V : APVars) : List ℕ := [V.nB, V.nB + 2, V.nB + 9, V.nB + 10, V.nB + 11]
/-- The scalars the constants write. -/
abbrev consS (V : APVars) : List ℕ := List.range' (V.sB + 100) 18

/-- Inclusion in the lists of the constants. -/
macro "subC" : tactic => `(tactic| (intro j hj; simp only [consN, consS, consC1, consC2, consC3, List.map_cons,
  List.map_nil, SI.dst, List.mem_cons, List.mem_range'_1, List.not_mem_nil, or_false] at hj ⊢ <;> omega))

/-- The scalar instructions of a block are well formed. -/
macro "cons_ok" : tactic => `(tactic| (simp only [consC1, consC2, consC3, List.all_cons, List.all_nil, SI.ok,
  Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]; (repeat' apply And.intro) <;> lay))

/-- A scalar outside the destinations of a block. -/
macro "cons_nd" : tactic => `(tactic| (simp only [consC1, consC2, consC3, List.map_cons, List.map_nil, SI.dst] <;>
  nmem_tac))

set_option maxHeartbeats 4000000 in
/-- The rule of the constants of ELL-cap. -/
theorem runs_ellConstsCode {nsQ ssQ asQ : List ℕ} (hp : V.Ok L nsQ ssQ asQ) (σ : Env d) (hd : σ.nat V.dv = d)
    (h1 : σ.nat V.one = 1) {k : EllConsts}
    (hk : ellConsts (σ.sc V.r) (σ.sc V.R) (σ.mat V.P) (σ.vec V.w) (σ.sc V.e) = k) :
    Runs L w (ellConstsCode L V) σ (kCons d k.N k.J k.B) (fun σ' => σ'.sc (V.sB + 100) = k.τ ∧
      σ'.sc (V.sB + 101) = k.ℓ1 ∧ σ'.nat (V.nB + 9) = k.N ∧ σ'.nat (V.nB + 10) = k.J ∧ σ'.nat (V.nB + 11) = k.B ∧
      Env.Frame σ σ' (consN V) (consS V) []) := by
  layout_facts
  obtain ⟨kτ, kℓ, kN, kJ, kB⟩ := ellConsts_code (σ.sc V.r) (σ.sc V.R) (σ.sc V.e) (σ.mat V.P) (σ.vec V.w) hk
  rw [ellConstsCode_eq]; unfold kCons
  refine runs_seq (runs_mtrace σ (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay)
    (by omega) (by lay) (by lay) (by omega) hd h1) (fun σ1 h1' => ?_)
  obtain ⟨t1, f1⟩ := h1'
  refine runs_seq (runs_vnorm σ1 (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay)
    (by omega) (by omega) (by omega) (by rw [f1.1 _ (by nmem_tac), hd]) (by rw [f1.1 _ (by nmem_tac), h1]))
    (fun σ2 h2' => ?_)
  obtain ⟨t2, f2⟩ := h2'
  have F2 : Env.Frame σ σ2 (consN V) (consS V) [] :=
    Env.Frame.trans (Env.Frame.mono f1 (by subC) (by subC) (by simp)) (Env.Frame.mono f2 (by subC) (by subC) (by simp))
  have n2 : σ2.nat V.dv = d := by rw [F2.1 _ (by nmem_tac), hd]
  have o2 : σ2.nat V.one = 1 := by rw [F2.1 _ (by nmem_tac), h1]
  have a107 : σ2.sc (V.sB + 107) = (σ.mat V.P).trace := by rw [f2.2.1 _ (by nmem_tac), t1]
  have a110 : σ2.sc (V.sB + 110) = oNorm (σ.vec V.w) := by rw [t2, Env.Frame.vec f1 (by simp)]; rfl
  have aR : σ2.sc V.R = σ.sc V.R := F2.2.1 _ (by nmem_tac)
  have ar : σ2.sc V.r = σ.sc V.r := F2.2.1 _ (by nmem_tac)
  have ae : σ2.sc V.e = σ.sc V.e := F2.2.1 _ (by nmem_tac)
  refine runs_sprogThen' (consC1 V) (by cons_ok) sCost_consC1 ?_
  generalize e3 : ({ σ2 with sc := sEval σ2.nat (consC1 V) σ2.sc } : Env d) = σ3
  have F3 : Env.Frame σ σ3 (consN V) (consS V) [] := by
    rw [← e3]; exact Env.Frame.trans F2 (Env.Frame.mono (Env.frame_sEval σ2 _) (by simp) (by subC) (by simp))
  obtain ⟨v100, v101, v110, v112, v117⟩ := consC1_val (V := V) σ2.nat σ2.sc hp.RB hp.rB hp.eB
  rw [a107, a110, aR, ar, ae, n2] at v100 v110; rw [a107, a110, aR, ar, ae] at v101
  rw [n2] at v112
  have s3 : σ3.sc = sEval σ2.nat (consC1 V) σ2.sc := by rw [← e3]
  have N3 : σ3.nat = σ2.nat := by rw [← e3]
  have hN : ⌈σ3.sc (V.sB + 110)⌉₊ + 1 = k.N := by rw [s3, v110, kN]
  have o3 : σ3.nat V.one = 1 := by rw [N3, o2]
  refine runs_seq (runs_mono (runs_nceil σ3 (by lay) (by lay) (by lay) (by lay) (by lay) (by omega) o3)
    (le_of_eq (by rw [← hN, Nat.add_sub_cancel])) (fun _ h => h)) (fun σ4 e4 => ?_)
  refine runs_seq (runs_nadd (by lay) (by lay) (by lay)) (fun σ5 e5 => ?_)
  have F5 : Env.Frame σ σ5 (consN V) (consS V) [] := by
    rw [e5, e4]
    exact Env.Frame.setNat (Env.Frame.setSc (Env.Frame.setNat F3 (by simp) _) (by simp only [consS, List.mem_range'_1]; omega) _) (by simp) _
  have N5 : σ5.nat (V.nB + 9) = k.N := by
    rw [e5, e4]; simp only [Env.setNat_nat, Env.setSc_nat, if_true]; rw [if_neg (by lay), o3, hN]
  have o5 : σ5.nat V.one = 1 := by
    rw [e5, e4]; simp only [Env.setNat_nat, Env.setSc_nat]; rw [if_neg (by lay), if_neg (by lay), o3]
  have s5 : ∀ x, x ≠ V.sB + 114 → σ5.sc x = σ3.sc x := fun x hx => by
    rw [e5, e4]; simp only [Env.setNat_sc, Env.setSc_sc]; rw [if_neg hx]
  refine runs_sprogThen' (consC2 V) (by cons_ok) sCost_consC2 ?_
  generalize e6 : ({ σ5 with sc := sEval σ5.nat (consC2 V) σ5.sc } : Env d) = σ6
  have F6 : Env.Frame σ σ6 (consN V) (consS V) [] := by
    rw [← e6]; exact Env.Frame.trans F5 (Env.Frame.mono (Env.frame_sEval σ5 _) (by simp) (by subC) (by simp))
  obtain ⟨w110, w113⟩ := consC2_val (V := V) σ5.nat σ5.sc hp.rB
  have s6 : σ6.sc = sEval σ5.nat (consC2 V) σ5.sc := by rw [← e6]
  have N6 : σ6.nat = σ5.nat := by rw [← e6]
  have r5 : σ5.sc V.r = σ.sc V.r := F5.2.1 _ (by nmem_tac)
  have c100 : σ5.sc (V.sB + 100) = k.τ := by rw [s5 _ (by omega), s3, v100, kτ]
  have hJ : ⌈σ6.sc (V.sB + 110)⌉₊ = k.J := by rw [s6, w110, r5, c100, kJ]
  have d6 : ∀ x, x ∉ (consC2 V).map SI.dst → σ6.sc x = σ5.sc x := fun x hx => by rw [s6]; exact sEval_frame _ _ _ hx
  refine runs_seq (runs_mono (runs_nceil σ6 (by lay) (by lay) (by lay) (by lay) (by lay) (by omega)
    (by rw [N6, o5])) (le_of_eq (by rw [hJ])) (fun _ h => h)) (fun σ7 e7 => ?_)
  have F7 : Env.Frame σ σ7 (consN V) (consS V) [] := by
    rw [e7]; exact Env.Frame.setSc (Env.Frame.setNat F6 (by simp) _) (by simp only [consS, List.mem_range'_1]; omega) _
  have s7 : ∀ x, x ≠ V.sB + 114 → σ7.sc x = σ6.sc x := fun x hx => by
    rw [e7]; simp only [Env.setNat_sc, Env.setSc_sc]; rw [if_neg hx]
  have J7 : σ7.nat (V.nB + 10) = k.J := by rw [e7]; simp only [Env.setNat_nat, Env.setSc_nat, if_true, hJ]
  have N7 : σ7.nat (V.nB + 9) = k.N := by
    rw [e7]; simp only [Env.setNat_nat, Env.setSc_nat]; rw [if_neg (by omega), N6, N5]
  have o7 : σ7.nat V.one = 1 := by
    rw [e7]; simp only [Env.setNat_nat, Env.setSc_nat]; rw [if_neg (by lay), N6, o5]
  refine runs_sprogThen' (consC3 V) (by cons_ok) sCost_consC3 ?_
  generalize e8 : ({ σ7 with sc := sEval σ7.nat (consC3 V) σ7.sc } : Env d) = σ8
  have F8 : Env.Frame σ σ8 (consN V) (consS V) [] := by
    rw [← e8]; exact Env.Frame.trans F7 (Env.Frame.mono (Env.frame_sEval σ7 _) (by simp) (by subC) (by simp))
  have s8 : σ8.sc = sEval σ7.nat (consC3 V) σ7.sc := by rw [← e8]
  have N8 : σ8.nat = σ7.nat := by rw [← e8]
  have d8 : ∀ x, x ∉ (consC3 V).map SI.dst → σ8.sc x = σ7.sc x := fun x hx => by rw [s8]; exact sEval_frame _ _ _ hx
  have r7 : σ7.sc V.r = σ.sc V.r := F7.2.1 _ (by nmem_tac)
  have R7 : σ7.sc V.R = σ.sc V.R := F7.2.1 _ (by nmem_tac)
  have g100 : σ7.sc (V.sB + 100) = k.τ := by rw [s7 _ (by omega), d6 _ (by cons_nd), c100]
  have g101 : σ7.sc (V.sB + 101) = k.ℓ1 := by
    rw [s7 _ (by omega), d6 _ (by cons_nd), s5 _ (by omega), s3, v101, kℓ]
  have g112 : σ7.sc (V.sB + 112) = d := by rw [s7 _ (by omega), d6 _ (by cons_nd), s5 _ (by omega), s3, v112]
  have g113 : σ7.sc (V.sB + 113) = Real.log 2 := by rw [s7 _ (by omega), s6, w113]
  have g117 : σ7.sc (V.sB + 117) = 1 := by rw [s7 _ (by omega), d6 _ (by cons_nd), s5 _ (by omega), s3, v117]
  have hB : ⌈σ8.sc (V.sB + 110)⌉₊ = k.B := by
    rw [s8, consC3_val _ _ hp.RB hp.rB, g100, g101, g112, g113, g117, r7, R7, J7, kB]
  refine runs_mono (runs_nceil σ8 (by lay) (by lay) (by lay) (by lay) (by lay) (by omega) (by rw [N8, o7]))
    (le_of_eq (by rw [hB])) (fun σ9 e9 => ?_)
  subst e9
  refine ⟨?_, ?_, ?_, ?_, ?_, Env.Frame.setSc (Env.Frame.setNat F8 (by simp) _) (by simp only [consS, List.mem_range'_1]; omega) _⟩
  · simp only [Env.setNat_sc, Env.setSc_sc]; rw [if_neg (by omega), d8 _ (by cons_nd), g100]
  · simp only [Env.setNat_sc, Env.setSc_sc]; rw [if_neg (by omega), d8 _ (by cons_nd), g101]
  · simp only [Env.setNat_nat, Env.setSc_nat]; rw [if_neg (by omega), N8, N7]
  · simp only [Env.setNat_nat, Env.setSc_nat]; rw [if_neg (by omega), N8, J7]
  · simp only [Env.setNat_nat, Env.setSc_nat, if_true, hB]

/-! ## The start and the end -/

/-- The natural variables, scalars and arrays the start writes. -/
abbrev initN (V : APVars) : List ℕ := [V.nB, V.nB + 2, V.nB + 12]
/-- The scalars the start writes. -/
abbrev initS (V : APVars) : List ℕ := [V.sB + 102, V.sB + 103, V.sB + 104, V.sB + 106, V.sB + 110]
/-- The arrays the start writes. -/
abbrev initA (V : APVars) : List ℕ := [V.aB + 9, V.aB + 10]

/-- The step bound of the start. -/
def kInit (d : ℕ) : ℕ :=
  (d * 4 + 4) + (1 + ((d * d * 5 + 3) + (1 + ((d * 7 + 4) + ((d * 5 + 3) + (1 + (1 + 1)))))))

/-- Inclusion in the lists of the start. -/
macro "subI" : tactic => `(tactic| (intro j hj; simp only [initN, initS, initA, List.mem_cons, List.not_mem_nil,
  or_false] at hj ⊢ <;> omega))

/-- The rule of the start of ELL-cap: `A = R² I`, `a = 0`, no recorded point, running. -/
theorem runs_ellInitCode {nsQ ssQ asQ : List ℕ} (hp : V.Ok L nsQ ssQ asQ) (σ : Env d) (hd : σ.nat V.dv = d)
    (h1 : σ.nat V.one = 1) (P : Matrix (Fin d) (Fin d) ℝ) (w' : Fin d → ℝ) :
    Runs L w (ellInitCode L V) σ (kInit d) (fun σ' =>
      ERel V P w' (some (.inl ⟨(σ.sc V.R ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ), 0, none⟩)) σ' ∧
      σ'.sc (V.sB + 106) = 0 ∧ Env.Frame σ σ' (initN V) (initS V) (initA V)) := by
  layout_facts
  unfold ellInitCode kInit
  refine runs_seq (runs_nsq σ (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by omega) (by lay) (by lay) hd h1)
    (fun σ1 h1' => ?_)
  obtain ⟨q1, f1⟩ := h1'
  have F1 : Env.Frame σ σ1 (initN V) (initS V) (initA V) := Env.Frame.mono f1 (by subI) (by simp) (by simp)
  refine runs_seq (runs_sconst (by lay) 0) (fun σ2 e2 => ?_)
  have F2 : Env.Frame σ σ2 (initN V) (initS V) (initA V) := by rw [e2]; exact Env.Frame.setSc F1 (by simp) _
  have n2 : σ2.nat V.dv = d := by rw [F2.1 _ (by nmem_tac), hd]
  have o2 : σ2.nat V.one = 1 := by rw [F2.1 _ (by nmem_tac), h1]
  refine runs_seq (runs_mfill σ2 (by lay) (by lay) (by lay) (by lay) (by lay) (by omega) (by lay)
    (by rw [e2, Env.setSc_nat, q1]) o2) (fun σ3 h3 => ?_)
  obtain ⟨m3, f3, -⟩ := h3
  have F3 : Env.Frame σ σ3 (initN V) (initS V) (initA V) := Env.Frame.trans F2 (Env.Frame.mono f3 (by subI) (by simp) (by subI))
  have n3 : σ3.nat V.dv = d := by rw [F3.1 _ (by nmem_tac), hd]
  have o3 : σ3.nat V.one = 1 := by rw [F3.1 _ (by nmem_tac), h1]
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σ4 e4 => ?_)
  have F4 : Env.Frame σ σ4 (initN V) (initS V) (initA V) := by rw [e4]; exact Env.Frame.setSc F3 (by simp) _
  refine runs_seq (runs_mdiag σ4 (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by omega)
    (by lay) (by lay) (by rw [e4, Env.setSc_nat, n3]) (by rw [e4, Env.setSc_nat, o3])) (fun σ5 h5 => ?_)
  obtain ⟨m5, f5, -⟩ := h5
  have F5 : Env.Frame σ σ5 (initN V) (initS V) (initA V) := Env.Frame.trans F4 (Env.Frame.mono f5 (by subI) (by simp) (by subI))
  refine runs_seq (runs_vfill σ5 (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay)
    (by rw [F5.1 _ (by nmem_tac), hd]) (by rw [F5.1 _ (by nmem_tac), h1])) (fun σ6 h6 => ?_)
  obtain ⟨v6, f6, -⟩ := h6
  have F6 : Env.Frame σ σ6 (initN V) (initS V) (initA V) := Env.Frame.trans F5 (Env.Frame.mono f6 (by subI) (by simp) (by subI))
  refine runs_seq (runs_sconst (by lay) 0) (fun σ7 e7 => ?_)
  refine runs_seq (runs_sconst (by lay) 1) (fun σ8 e8 => ?_)
  refine runs_mono (runs_sconst (by lay) 1) le_rfl (fun σ9 e9 => ?_)
  have z106 : σ5.sc (V.sB + 106) = 0 := by
    rw [f5.2.1 _ (by simp), e4, Env.setSc_sc, if_neg (by omega), f3.2.1 _ (by simp), e2, Env.setSc_sc, if_pos rfl]
    norm_num
  have hA : σ6.mat (V.aB + 9) = (σ.sc V.R ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [Env.Frame.mat f6 (by simp), m5, e4, Env.setSc_mat, Env.setSc_sc, if_pos rfl, m3, e2, Env.setSc_sc,
      if_pos rfl, F3.2.1 _ (by nmem_tac)]
    ext a b; by_cases h : a = b <;> simp [h, Op2.eval, sq, Matrix.one_apply]
  have ha : σ6.vec (V.aB + 10) = 0 := by rw [v6, z106]; rfl
  subst e9 e8 e7
  refine ⟨⟨by simp, by simp [show V.sB + 102 ≠ V.sB + 103 by omega], ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [Env.setSc_mat, Env.setSc_mat, Env.setSc_mat, hA]
  · rw [Env.setSc_vec, Env.setSc_vec, Env.setSc_vec, ha]
  · simp only [BestRel, Env.setSc_sc]
    rw [if_neg (by omega), if_neg (by omega), if_true, Rat.cast_zero]
  · simp only [Env.setSc_sc]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), f6.2.1 _ (by simp), z106]
  · exact Env.Frame.setSc (Env.Frame.setSc (Env.Frame.setSc F6 (by simp) _) (by simp) _) (by simp) _

/-- What ELL-cap returns from the state of its loop. -/
def ellOut : Option (EllSt d ⊕ (Fin d → ℝ)) → Option (Fin d → ℝ)
  | some (.inr μ) => some μ
  | some (.inl st) => st.best
  | none => none

/-- The answer of AP in its variables `ok`, `out`. -/
def APOut (V : APVars) : Option (Fin d → ℝ) → Env d → Prop
  | none, σ => σ.sc V.ok = 0
  | some x, σ => σ.sc V.ok = 1 ∧ σ.vec V.out = x

/-- The step bound of the end. -/
def kFin (d : ℕ) : ℕ := d * 7 + 9

/-- The rule of the end of ELL-cap. -/
theorem runs_ellFinalCode {nsQ ssQ asQ : List ℕ} (hp : V.Ok L nsQ ssQ asQ) (σ : Env d) (hd : σ.nat V.dv = d)
    (h1 : σ.nat V.one = 1) (h106 : σ.sc (V.sB + 106) = 0) {P : Matrix (Fin d) (Fin d) ℝ} {w' : Fin d → ℝ}
    (o : Option (EllSt d ⊕ (Fin d → ℝ))) (ho : ERel V P w' o σ) :
    Runs L w (ellFinalCode L V) σ (kFin d) (fun σ' =>
      APOut V (ellOut o) σ' ∧ Env.Frame σ σ' [V.nB] [V.ok, V.sB + 110] [V.out]) := by
  layout_facts
  unfold ellFinalCode kFin
  have copy : ∀ x, x < L.NA → Runs L w (.seq (vcopy L V.dv V.one V.nB V.out x (V.sB + 110)) (sconst L V.ok 1)) σ
      (d * 7 + 3 + 1) (fun σ' => σ'.sc V.ok = 1 ∧ σ'.vec V.out = σ.vec x ∧
        Env.Frame σ σ' [V.nB] [V.ok, V.sB + 110] [V.out]) := fun x hx =>
    runs_seq (runs_vcopy σ (by lay) (by lay) (by lay) (by lay) hx (by lay) (by lay) (by lay) hd h1) (fun σ1 h1' =>
      runs_mono (runs_sconst (by lay) 1) le_rfl (fun σ2 e2 => by
        obtain ⟨v1, f1, -⟩ := h1'
        subst e2
        exact ⟨by simp, by rw [Env.setSc_vec, v1],
          Env.Frame.setSc (Env.Frame.mono f1 (by simp) (by simp) (by simp)) (by simp) _⟩))
  rcases o with _ | st | μ
  · obtain ⟨z103, -⟩ := ho
    refine runs_mono (runs_ifS_f (by lay) (by lay) (by rw [h106, z103]; exact lt_irrefl 0)
      (runs_sconst (by lay) 0)) (by omega) (fun σ' e => ?_)
    subst e
    exact ⟨by simp [ellOut, APOut], Env.Frame.setSc (Env.Frame.refl σ _ _ _) (by simp) _⟩
  · obtain ⟨o103, o102, -, -, hb⟩ := ho
    refine runs_mono (K := d * 7 + 3 + 1 + 2 + 1) (runs_ifS_t (by lay) (by lay)
      (by rw [h106, o103]; exact one_pos) ?_) (by omega) (fun _ h => h)
    refine runs_mono (K := d * 7 + 3 + 1 + 2) (runs_ifS_t (by lay) (by lay)
      (by rw [h106, o102]; exact one_pos) ?_) (by omega) (fun _ h => h)
    rcases hst : st.best with _ | b
    · rw [hst] at hb
      refine runs_mono (runs_ifS_f (by lay) (by lay) (by rw [h106, hb]; exact lt_irrefl 0)
        (runs_sconst (by lay) 0)) (by omega) (fun σ' e => ?_)
      subst e
      exact ⟨by simp [ellOut, APOut, hst], Env.Frame.setSc (Env.Frame.refl σ _ _ _) (by simp) _⟩
    · rw [hst] at hb
      obtain ⟨b104, b11, -⟩ := hb
      refine runs_mono (runs_ifS_t (by lay) (by lay) (by rw [h106, b104]; exact one_pos) (copy _ (by lay)))
        (by omega) (fun σ' h => ?_)
      obtain ⟨k1, v1, f1⟩ := h
      exact ⟨by simp only [ellOut, APOut, hst]; exact ⟨k1, by rw [v1, b11]⟩, f1⟩
  · obtain ⟨o103, o102, a10⟩ := ho
    refine runs_mono (K := d * 7 + 3 + 1 + 2 + 2) (runs_ifS_t (by lay) (by lay)
      (by rw [h106, o103]; exact one_pos) ?_) (by omega) (fun _ h => h)
    refine runs_mono (runs_ifS_f (by lay) (by lay) (by rw [h106, o102]; exact lt_irrefl 0) (copy _ (by lay)))
      (by omega) (fun σ' h => ?_)
    obtain ⟨k1, v1, f1⟩ := h
    exact ⟨by simp only [ellOut, APOut]; exact ⟨k1, by rw [v1, a10]⟩, f1⟩

/-! ## ELL-cap -/

theorem ellCap_eq {Q : Set (Fin d → ℝ)} {a0 : Fin d → ℝ} {r R : ℝ} {P : Matrix (Fin d) (Fin d) ℝ}
    {w' : Fin d → ℝ} {e : ℝ} (h : ¬ R < r) :
    ellCap Q a0 r R P w' e = ellOut (ellLoop Q a0 r R P w' (ellConsts r R P w' e) (ellConsts r R P w' e).N) := by
  simp only [ellCap, if_neg h]
  generalize ellLoop Q a0 r R P w' (ellConsts r R P w' e) (ellConsts r R P w' e).N = o
  rcases o with _ | st | μ <;> rfl

/-- The step bound of ELL-cap. -/
def kCap (d Kq N J B : ℕ) : ℕ :=
  (kCons d N J B + (kInit d + ((N * (kES d Kq B J + 2 + 3) + 3) + kFin d))) + 2

/-- Inclusion in the lists of AP. -/
macro "subAP" : tactic => `(tactic| (intro j hj; simp only [apN, apS, apA, consN, consS, initN, initS, initA,
  stepS, stepA, List.mem_append, List.mem_cons, List.mem_range'_1, List.not_mem_nil, or_false] at hj ⊢ <;> omega))

set_option maxHeartbeats 8000000 in
/-- The rule of ELL-cap: it answers `ellCap` on its inputs in `ok`, `out`. -/
theorem runs_ellCapCode {Q : Set (Fin d → ℝ)} {Iq : Env d → Prop} {Kq : ℕ} {nsQ ssQ asQ : List ℕ}
    (hp : V.Ok L nsQ ssQ asQ) (hmem : MemRule L w memQ V Q Iq Kq nsQ ssQ asQ) (hIq : IqRule V Iq)
    (σ : Env d) (hd : σ.nat V.dv = d) (h1 : σ.nat V.one = 1) (hI : Iq σ) (h0 : 0 < d) {k : EllConsts}
    (hk : ellConsts (σ.sc V.r) (σ.sc V.R) (σ.mat V.P) (σ.vec V.w) (σ.sc V.e) = k) :
    Runs L w (ellCapCode L memQ V) σ (kCap d Kq k.N k.J k.B) (fun σ' =>
      APOut V (ellCap Q (σ.vec V.a0) (σ.sc V.r) (σ.sc V.R) (σ.mat V.P) (σ.vec V.w) (σ.sc V.e)) σ' ∧
      KP Iq nsQ ssQ asQ (apN V) (apS V) (apA V) σ σ') := by
  layout_facts
  have liftF : ∀ σa σb (ns ss as : List ℕ), KP Iq nsQ ssQ asQ (apN V) (apS V) (apA V) σ σa →
      Env.Frame σa σb ns ss as → (∀ j ∈ ns, j ∈ apN V) → (∀ j ∈ ss, j ∈ apS V) → (∀ j ∈ as, j ∈ apA V) →
      KP Iq nsQ ssQ asQ (apN V) (apS V) (apA V) σ σb :=
    fun σa σb ns ss as g f hn hs ha => keep_own hIq (fun _ h => h) (fun _ h => h) (fun _ h => h) g f hn hs ha
  have hON9 : ∀ j ∈ List.range' V.nB 9, j ∈ apN V := by subAP
  have hOS : ∀ j ∈ stepS V, j ∈ apS V := by subAP
  have hOA : ∀ j ∈ stepA V, j ∈ apA V := by subAP
  unfold ellCapCode kCap
  by_cases hRr : σ.sc V.R < σ.sc V.r
  · refine runs_mono (runs_ifS_t (by lay) (by lay) hRr (runs_sconst (by lay) 0)) (by omega) (fun σ' e => ?_)
    subst e
    have hc : ellCap Q (σ.vec V.a0) (σ.sc V.r) (σ.sc V.R) (σ.mat V.P) (σ.vec V.w) (σ.sc V.e) = none := by
      simp only [ellCap, if_pos hRr]
    rw [hc]
    exact ⟨by simp [APOut], liftF _ _ _ _ _ (keep_refl hI) (frame_setSc _ _ _) (by simp) (by simp [apS])
      (by simp)⟩
  refine runs_mono (K := (kCons d k.N k.J k.B + (kInit d + ((k.N * (kES d Kq k.B k.J + 2 + 3) + 3) + kFin d))) + 2)
    (runs_ifS_f (by lay) (by lay) hRr ?_) le_rfl (fun _ h => h)
  refine runs_seq (runs_ellConstsCode hp σ hd h1 hk) (fun σ1 h1' => ?_)
  obtain ⟨c100, c101, cN, cJ, cB, f1⟩ := h1'
  have g1 : KP Iq nsQ ssQ asQ (apN V) (apS V) (apA V) σ σ1 :=
    liftF _ _ _ _ _ (keep_refl hI) f1 (by subAP) (by subAP) (by simp)
  have d1 : σ1.nat V.dv = d := by rw [f1.1 _ (by nmem_tac), hd]
  have o1 : σ1.nat V.one = 1 := by rw [f1.1 _ (by nmem_tac), h1]
  refine runs_seq (runs_ellInitCode hp σ1 d1 o1 (σ.mat V.P) (σ.vec V.w)) (fun σ2 h2' => ?_)
  obtain ⟨e2, z2, f2⟩ := h2'
  rw [f1.2.1 _ (by nmem_tac)] at e2
  have g2 := liftF _ _ _ _ _ g1 f2 (by subAP) (by subAP) (by subAP)
  have d2 : σ2.nat V.dv = d := by rw [f2.1 _ (by nmem_tac), d1]
  have o2 : σ2.nat V.one = 1 := by rw [f2.1 _ (by nmem_tac), o1]
  have N2 : σ2.nat (V.nB + 9) = k.N := by rw [f2.1 _ (by nmem_tac), cN]
  have τ2 : σ2.sc (V.sB + 100) = k.τ := by rw [f2.2.1 _ (by nmem_tac), c100]
  have ℓ2 : σ2.sc (V.sB + 101) = k.ℓ1 := by rw [f2.2.1 _ (by nmem_tac), c101]
  have J2 : σ2.nat (V.nB + 10) = k.J := by rw [f2.1 _ (by nmem_tac), cJ]
  have B2 : σ2.nat (V.nB + 11) = k.B := by rw [f2.1 _ (by nmem_tac), cB]
  have P2 : σ2.mat V.P = σ.mat V.P := by rw [Env.Frame.mat f2 (by nmem_tac), Env.Frame.mat f1 (by simp)]
  have w2 : σ2.vec V.w = σ.vec V.w := by rw [Env.Frame.vec f2 (by nmem_tac), Env.Frame.vec f1 (by simp)]
  have a2 : σ2.vec V.a0 = σ.vec V.a0 := by rw [Env.Frame.vec f2 (by nmem_tac), Env.Frame.vec f1 (by simp)]
  have r2 : σ2.sc V.r = σ.sc V.r := by rw [f2.2.1 _ (by nmem_tac), f1.2.1 _ (by nmem_tac)]
  have R2 : σ2.sc V.R = σ.sc V.R := by rw [f2.2.1 _ (by nmem_tac), f1.2.1 _ (by nmem_tac)]
  refine runs_seq (runs_forN (by lay) (by lay) (by lay) (by omega) (by lay) k.N (kES d Kq k.B k.J + 2)
    (fun t σ' => ERel V (σ.mat V.P) (σ.vec V.w)
        ((ellIt Q (σ.vec V.a0) (σ.sc V.r) (σ.sc V.R) (σ.mat V.P) (σ.vec V.w) k)^[t]
          (some (.inl ⟨(σ.sc V.R ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ), 0, none⟩))) σ' ∧
      KP Iq nsQ ssQ asQ (List.range' V.nB 9) (stepS V) (stepA V) σ2 σ') σ2 N2 o2
    ⟨e2.of_eq rfl rfl rfl rfl rfl rfl rfl,
      keep_own hIq hON9 hOS hOA (keep_refl g2.1) (frame_setNat _ _ _) (by simp) (by simp) (by simp)⟩ ?_)
    (fun σ3 h3' => ?_)
  · intro t _ σ' hJ hi hn ho
    obtain ⟨eR, kp⟩ := hJ
    have dd : σ'.nat V.dv = d := by rw [kp.nat (by nmem_tac) hp.dv_nQ, d2]
    have z' : σ'.sc (V.sB + 106) = 0 := by rw [kp.sc (by nmemST) (hp.sB_sQ (by omega) (by omega)), z2]
    have cP : σ'.mat V.P = σ.mat V.P := by rw [kp.mat (by nmemST) hp.P_aQ, P2]
    have cw : σ'.vec V.w = σ.vec V.w := by rw [kp.vec (by nmemST) hp.w_aQ, w2]
    have ca : σ'.vec V.a0 = σ.vec V.a0 := by rw [kp.vec (by nmemST) hp.a0_aQ, a2]
    have cr : σ'.sc V.r = σ.sc V.r := by rw [kp.sc (by nmemST) hp.r_sQ, r2]
    have cR : σ'.sc V.R = σ.sc V.R := by rw [kp.sc (by nmemST) hp.R_sQ, R2]
    have cτ : σ'.sc (V.sB + 100) = k.τ := by rw [kp.sc (by nmemST) (hp.sB_sQ (by omega) (by omega)), τ2]
    have cℓ : σ'.sc (V.sB + 101) = k.ℓ1 := by rw [kp.sc (by nmemST) (hp.sB_sQ (by omega) (by omega)), ℓ2]
    have cJ' : σ'.nat (V.nB + 10) = k.J := by rw [kp.nat (by nmem_tac) (hp.nN_nQ (by omega) (by omega)), J2]
    have cB' : σ'.nat (V.nB + 11) = k.B := by rw [kp.nat (by nmem_tac) (hp.nN_nQ (by omega) (by omega)), B2]
    have keepN : ∀ σ'', σ'' = σ' → KP Iq nsQ ssQ asQ (List.range' V.nB 9) (stepS V) (stepA V) σ2
        (σ''.setNat (V.nB + 8) (t + 1)) := fun σ'' e => by
      subst e; exact keep_own hIq hON9 hOS hOA kp (frame_setNat _ _ _) (by simp) (by simp) (by simp)
    rcases hc : (ellIt Q (σ.vec V.a0) (σ.sc V.r) (σ.sc V.R) (σ.mat V.P) (σ.vec V.w) k)^[t]
      (some (.inl ⟨(σ.sc V.R ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ), 0, none⟩)) with _ | st | μ
    · rw [hc] at eR
      refine runs_mono (runs_ifS_f (by lay) (by lay) (by rw [z', eR.2]; exact lt_irrefl 0) (runs_skip σ'))
        (by omega) (fun σ'' e => ?_)
      refine ⟨by rw [e, hi], by rw [e, hn], by rw [e, ho], ?_, keepN σ'' e⟩
      rw [Function.iterate_succ_apply', hc, e]
      exact eR.of_eq rfl rfl rfl rfl rfl rfl rfl
    · rw [hc] at eR
      have eR' : ERel V (σ'.mat V.P) (σ'.vec V.w) (some (.inl st)) σ' := by rw [cP, cw]; exact eR
      refine runs_mono (runs_ifS_t (by lay) (by lay) (by rw [z', eR.2.1]; exact one_pos)
        (runs_ellStepCode hp hmem hIq σ' dd (by rw [kp.nat (by nmem_tac) hp.one_nQ, o2]) kp.1 h0 k cτ cℓ cJ' cB'
          st eR')) (by omega) (fun σ'' h'' => ?_)
      obtain ⟨r'', k''⟩ := h''
      rw [cP, cw, ca, cr, cR] at r''
      refine ⟨by rw [k''.nat (by nmem_tac) (hp.nN_nQ (by omega) (by omega)), hi],
        by rw [k''.nat (by nmem_tac) (hp.nN_nQ (by omega) (by omega)), hn],
        by rw [k''.nat (by nmem_tac) hp.one_nQ, ho], ?_,
        keep_own hIq hON9 hOS hOA (keep_trans kp (keep_mono k'' (by subAP) (fun _ h => h) (fun _ h => h)))
          (frame_setNat _ _ _) (by simp) (by simp) (by simp)⟩
      rw [Function.iterate_succ_apply', hc]
      exact r''.of_eq rfl rfl rfl rfl rfl rfl rfl
    · rw [hc] at eR
      refine runs_mono (runs_ifS_f (by lay) (by lay) (by rw [z', eR.2.1]; exact lt_irrefl 0) (runs_skip σ'))
        (by omega) (fun σ'' e => ?_)
      refine ⟨by rw [e, hi], by rw [e, hn], by rw [e, ho], ?_, keepN σ'' e⟩
      rw [Function.iterate_succ_apply', hc, e]
      exact eR.of_eq rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨⟨eR3, kp3⟩, -, -, o3⟩ := h3'
  have z3 : σ3.sc (V.sB + 106) = 0 := by rw [kp3.sc (by nmemST) (hp.sB_sQ (by omega) (by omega)), z2]
  have d3 : σ3.nat V.dv = d := by rw [kp3.nat (by nmem_tac) hp.dv_nQ, d2]
  refine runs_mono (runs_ellFinalCode hp σ3 d3 o3 z3 _ eR3) le_rfl (fun σ4 h4 => ?_)
  obtain ⟨out4, f4⟩ := h4
  refine ⟨?_, liftF _ _ _ _ _ (keep_trans g2 (keep_mono kp3 (by subAP) (by subAP) (by subAP))) f4 (by subAP)
    (by subAP) (by subAP)⟩
  rw [ellCap_eq hRr, hk, ellLoop_eq_iterate]
  exact out4

end AdversarialBco.Poly.AP
