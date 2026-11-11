/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachAPCap
public import AdversarialBco.Poly.APMathCost

@[expose] public section

/-!
# The subroutine AP in VL: procedure ELL-1

For `d = 1`, `runs_ellOneCode`: the code of ELL-1 answers `ellOne` on the entries `0` of its arrays within
`kOne Kq (oneCnt R p w e)` steps; `oneCnt` bounds the bisection count without reading `a₀`. `runs_ellOneTurn` is one
halving of the bisection.
-/

namespace AdversarialBco.Poly.AP

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL Matrix

variable {d : ℕ} {L : Layout} {w : World d} {memQ : Cmd} {V : APVars}

/-- The first scalar block of ELL-1: the zero `sB + 64` and `|a₀|` in `sB + 63`. -/
def oneC1 (V : APVars) : List SI :=
  [.const (V.sB + 64) 0, .op2 .sub (V.sB + 71) (V.sB + 64) (V.sB + 60), .smax (V.sB + 63) (V.sB + 60) (V.sB + 71)]

/-- The second scalar block of ELL-1: `w' = max (-R) (min R w)` in `sB + 65`. -/
def oneC2 (V : APVars) : List SI :=
  [.smin (V.sB + 71) V.R (V.sB + 61), .op2 .sub (V.sB + 72) (V.sB + 64) V.R,
   .smax (V.sB + 65) (V.sB + 72) (V.sB + 71)]

/-- The third scalar block of ELL-1: `ξ` in `sB + 66` and `log₂ (|w' - a₀|/ξ)` in `sB + 71`. -/
def oneC3 (V : APVars) : List SI :=
  [.op2 .sub (V.sB + 71) (V.sB + 64) (V.sB + 61),
   .smax (V.sB + 71) (V.sB + 61) (V.sB + 71),
   .op2 .add (V.sB + 71) V.R (V.sB + 71),
   .op2 .mul (V.sB + 71) (V.sB + 62) (V.sB + 71),
   .op2 .div (V.sB + 66) V.e (V.sB + 71),
   .op2 .sub (V.sB + 71) (V.sB + 65) (V.sB + 60),
   .op2 .sub (V.sB + 72) (V.sB + 64) (V.sB + 71),
   .smax (V.sB + 71) (V.sB + 71) (V.sB + 72),
   .op2 .div (V.sB + 71) (V.sB + 71) (V.sB + 66),
   .op1 .log (V.sB + 71) (V.sB + 71),
   .const (V.sB + 73) 2,
   .op1 .log (V.sB + 72) (V.sB + 73),
   .op2 .div (V.sB + 71) (V.sB + 71) (V.sB + 72)]

theorem ellOneCode_eq : ellOneCode L memQ V =
    .seq (nconst (V.nB + 13) 0) (
    .seq (aget L (V.sB + 60) V.a0 (V.nB + 13)) (
    .seq (aget L (V.sB + 61) V.w (V.nB + 13)) (
    .seq (aget L (V.sB + 62) V.P (V.nB + 13)) (
    sprogThen L (oneC1 V) (
    ifS L V.R V.r (sconst L V.ok 0) (
    ifS L V.R (V.sB + 63) (sconst L V.ok 0) (
    .seq (aset L V.qv (V.nB + 13) (V.sB + 60)) (
    .seq memQ (
    ifS L (V.sB + 64) V.qo
      (sprogThen L (oneC2 V) (
       .seq (aset L V.qv (V.nB + 13) (V.sB + 65)) (
       .seq memQ (
       ifS L (V.sB + 64) V.qo
         (.seq (aset L V.out (V.nB + 13) (V.sB + 65)) (sconst L V.ok 1))
         (sprogThen L (oneC3 V) (
          .seq (nceil L (V.nB + 14) V.one (V.sB + 71) (V.sB + 74)) (
          .seq (smov L (V.sB + 67) (V.sB + 60)) (
          .seq (smov L (V.sB + 68) (V.sB + 65)) (
          .seq (sconst L (V.sB + 70) (1 / 2)) (
          .seq (forN (V.nB + 15) (V.nB + 14) V.one (ellOneTurn L memQ V)) (
          .seq (aset L V.out (V.nB + 13) (V.sB + 67)) (sconst L V.ok 1))))))))))))
      (sconst L V.ok 0)))))))))) := by
  simp only [ellOneCode, sprogThen, oneC1, oneC2, oneC3, List.foldr_cons, List.foldr_nil, SI.cmd]

theorem oneC1_val (n : ℕ → ℕ) (f : ℕ → ℝ) :
    sEval n (oneC1 V) f (V.sB + 63) = max (f (V.sB + 60)) (0 - f (V.sB + 60)) ∧
    sEval n (oneC1 V) f (V.sB + 64) = 0 ∧ sEval n (oneC1 V) f (V.sB + 60) = f (V.sB + 60) := by
  simp only [oneC1]; cons_val

theorem oneC2_val (n : ℕ → ℕ) (f : ℕ → ℝ) (hR : V.R < V.sB ∨ V.sB + 128 ≤ V.R) :
    sEval n (oneC2 V) f (V.sB + 65) = max (f (V.sB + 64) - f V.R) (min (f V.R) (f (V.sB + 61))) := by
  simp only [oneC2]; cons_val

theorem oneC3_val (n : ℕ → ℕ) (f : ℕ → ℝ) (hR : V.R < V.sB ∨ V.sB + 128 ≤ V.R)
    (he : V.e < V.sB ∨ V.sB + 128 ≤ V.e) :
    sEval n (oneC3 V) f (V.sB + 71) = Real.log (max (f (V.sB + 65) - f (V.sB + 60))
      (f (V.sB + 64) - (f (V.sB + 65) - f (V.sB + 60))) / (f V.e / (f (V.sB + 62) * (f V.R +
      max (f (V.sB + 61)) (f (V.sB + 64) - f (V.sB + 61)))))) / Real.log 2 := by
  simp only [oneC3]; cons_val

theorem vec_setArr_one (σ : Env 1) (a : ℕ) (v : ℝ) : (σ.setArr a 0 v).vec a = fun _ => v := by
  funext i
  have hi : (i : ℕ) = 0 := Nat.lt_one_iff.1 i.isLt
  simp [Env.vec, hi]

theorem sCost_oneC1 : sCost (oneC1 V) = 5 := by simp [sCost, oneC1, SI.cost]
theorem sCost_oneC2 : sCost (oneC2 V) = 7 := by simp [sCost, oneC2, SI.cost]
theorem sCost_oneC3 : sCost (oneC3 V) = 17 := by simp [sCost, oneC3, SI.cost]

theorem ellOne_noQ {Q : Set ℝ} {a0 r R p w e : ℝ} (h1 : ¬ R < r) (h2 : ¬ R < |a0|) (ha : a0 ∉ Q) :
    ellOne Q a0 r R p w e = none := by
  simp only [ellOne, h1, h2, or_self, ha, not_false_eq_true, ↓reduceIte]

theorem ellOne_clamp {Q : Set ℝ} {a0 r R p w e : ℝ} (h1 : ¬ R < r) (h2 : ¬ R < |a0|) (ha : a0 ∈ Q)
    (hw : max (-R) (min R w) ∈ Q) : ellOne Q a0 r R p w e = some (max (-R) (min R w)) := by
  simp only [ellOne, h1, h2, or_self, ha, not_true_eq_false, hw, ↓reduceIte]

theorem ellOne_bisect {Q : Set ℝ} {a0 r R p w e : ℝ} (h1 : ¬ R < r) (h2 : ¬ R < |a0|) (ha : a0 ∈ Q)
    (hw : max (-R) (min R w) ∉ Q) : ellOne Q a0 r R p w e =
      some (oBisectLo (· ∈ Q) a0 (max (-R) (min R w))
        ⌈Real.log (|max (-R) (min R w) - a0| / (e / (p * (R + |w|)))) / Real.log 2⌉₊).1 := by
  simp only [ellOne, h1, h2, or_self, ha, not_true_eq_false, hw, ↓reduceIte, Real.logb]

theorem oBisectLo_succ_pos {Pr : ℝ → Prop} {lo hi : ℝ} {t : ℕ}
    (h : Pr (((oBisectLo Pr lo hi t).1 + (oBisectLo Pr lo hi t).2) / 2)) :
    oBisectLo Pr lo hi (t + 1) =
      (((oBisectLo Pr lo hi t).1 + (oBisectLo Pr lo hi t).2) / 2, (oBisectLo Pr lo hi t).2) := by
  simp only [oBisectLo]; rw [if_pos h]

theorem oBisectLo_succ_neg {Pr : ℝ → Prop} {lo hi : ℝ} {t : ℕ}
    (h : ¬ Pr (((oBisectLo Pr lo hi t).1 + (oBisectLo Pr lo hi t).2) / 2)) :
    oBisectLo Pr lo hi (t + 1) =
      ((oBisectLo Pr lo hi t).1, ((oBisectLo Pr lo hi t).1 + (oBisectLo Pr lo hi t).2) / 2) := by
  simp only [oBisectLo]; rw [if_neg h]

/-- The scalars a halving writes. -/
abbrev turnS (V : APVars) : List ℕ := [V.sB + 67, V.sB + 68, V.sB + 69]

set_option maxHeartbeats 4000000 in
/-- One halving of the bisection of ELL-1: the midpoint `m` replaces `lo` (in `sB + 67`) if `m ∈ Q`, else `hi`
(in `sB + 68`). -/
theorem runs_ellOneTurn {Q : Set (Fin d → ℝ)} {Iq : Env d → Prop} {Kq : ℕ} {nsQ ssQ asQ : List ℕ}
    (hp : V.Ok L nsQ ssQ asQ) (hmem : MemRule L w memQ V Q Iq Kq nsQ ssQ asQ) (hIq : IqRule V Iq) (hd1 : d = 1)
    (σ : Env d) (hd : σ.nat V.dv = d) (h1 : σ.nat V.one = 1) (hI : Iq σ) (h13 : σ.nat (V.nB + 13) = 0)
    (h64 : σ.sc (V.sB + 64) = 0) (h70 : σ.sc (V.sB + 70) = ((1 / 2 : ℚ) : ℝ)) :
    Runs L w (ellOneTurn L memQ V) σ (Kq + 7) (fun σ' =>
      ((fun _ => (σ.sc (V.sB + 67) + σ.sc (V.sB + 68)) / 2) ∈ Q →
        σ'.sc (V.sB + 67) = (σ.sc (V.sB + 67) + σ.sc (V.sB + 68)) / 2 ∧ σ'.sc (V.sB + 68) = σ.sc (V.sB + 68)) ∧
      ((fun _ => (σ.sc (V.sB + 67) + σ.sc (V.sB + 68)) / 2) ∉ Q →
        σ'.sc (V.sB + 67) = σ.sc (V.sB + 67) ∧ σ'.sc (V.sB + 68) = (σ.sc (V.sB + 67) + σ.sc (V.sB + 68)) / 2) ∧
      KP Iq nsQ ssQ asQ [] (turnS V) [V.qv] σ σ') := by
  subst hd1
  layout_facts
  have hOS : ∀ j ∈ turnS V, j ∈ apS V := by subAP
  have hOA : ∀ j ∈ [V.qv], j ∈ apA V := by subAP
  unfold ellOneTurn
  refine runs_mono (K := 1 + (1 + (2 + (Kq + 3)))) ?_ (by omega) (fun _ h => h)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .add) (fun σ1 e1 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σ2 e2 => ?_)
  have n2 : σ2.nat = σ.nat := by rw [e2, e1]; rfl
  have m2 : σ2.sc (V.sB + 69) = (σ.sc (V.sB + 67) + σ.sc (V.sB + 68)) / 2 := by
    rw [e2, e1]; simp (disch := omega) only [Env.setSc_sc, Op2.eval, if_pos, if_neg, ↓reduceIte]
    rw [h70, mul_half_rat]
  refine runs_seq (runs_aset (by lay) (by lay) (by lay) (by rw [n2, h13]; unfold asz; omega)) (fun σ3 e3 => ?_)
  have v3 : σ3.vec V.qv = fun _ => (σ.sc (V.sB + 67) + σ.sc (V.sB + 68)) / 2 := by
    rw [e3, n2, h13, m2]; exact vec_setArr_one _ _ _
  have k3 : KP Iq nsQ ssQ asQ [] (turnS V) [V.qv] σ σ3 := by
    have f2 : Env.Frame σ σ2 [] (turnS V) [] := by
      rw [e2, e1]
      exact Env.Frame.setSc (Env.Frame.setSc (Env.Frame.refl σ _ _ _) (by simp) _) (by simp) _
    rw [e3]
    exact keep_own hIq (by simp) hOS hOA (keep_own hIq (by simp) hOS hOA (keep_refl hI) f2 (by simp) (fun _ h => h)
      (by simp)) (frame_setArr _ _ _ _) (by simp) (by simp) (by simp)
  have d3 : σ3.nat V.dv = 1 := by rw [k3.nat (by simp) hp.dv_nQ, hd]
  have o3 : σ3.nat V.one = 1 := by rw [k3.nat (by simp) hp.one_nQ, h1]
  refine runs_seq (hmem σ3 k3.1 d3 o3) (fun σ4 h4 => ?_)
  obtain ⟨q4, f4, I4⟩ := h4
  have k4 : KP Iq nsQ ssQ asQ [] (turnS V) [V.qv] σ σ4 := keep_mem k3 f4 I4
  rw [v3] at q4
  have z4 : σ4.sc (V.sB + 64) = 0 := by rw [k4.sc (by simp only [turnS]; nmem_tac) (hp.sB_sQ (by omega) (by omega)), h64]
  have s67 : σ4.sc (V.sB + 67) = σ.sc (V.sB + 67) := by
    rw [f4.2.1 _ (hp.sB_sQ (by omega) (by omega)), e3, Env.setArr_sc, e2, e1]
    simp (disch := omega) only [Env.setSc_sc, if_pos, if_neg, ↓reduceIte]
  have s68 : σ4.sc (V.sB + 68) = σ.sc (V.sB + 68) := by
    rw [f4.2.1 _ (hp.sB_sQ (by omega) (by omega)), e3, Env.setArr_sc, e2, e1]
    simp (disch := omega) only [Env.setSc_sc, if_pos, if_neg, ↓reduceIte]
  have s69 : σ4.sc (V.sB + 69) = (σ.sc (V.sB + 67) + σ.sc (V.sB + 68)) / 2 := by
    rw [f4.2.1 _ (hp.sB_sQ (by omega) (by omega)), e3, Env.setArr_sc, m2]
  by_cases hm : (fun _ => (σ.sc (V.sB + 67) + σ.sc (V.sB + 68)) / 2) ∈ Q
  · rw [if_pos hm] at q4
    refine runs_mono (runs_ifS_t (by lay) (by lay) (by rw [z4, q4]; exact one_pos) (runs_smov (by lay) (by lay)))
      (by omega) (fun σ5 e5 => ?_)
    subst e5
    refine ⟨fun _ => ⟨by simp [s69], by simp only [Env.setSc_sc]; rw [if_neg (by omega), s68]⟩,
      fun h => absurd hm h, keep_own hIq (by simp) hOS hOA k4 (frame_setSc _ _ _) (by simp) (by simp) (by simp)⟩
  · rw [if_neg hm] at q4
    refine runs_mono (runs_ifS_f (by lay) (by lay) (by rw [z4, q4]; exact lt_irrefl 0)
      (runs_smov (by lay) (by lay))) (by omega) (fun σ5 e5 => ?_)
    subst e5
    refine ⟨fun h => absurd h hm, fun _ => ⟨by simp only [Env.setSc_sc]; rw [if_neg (by omega), s67], by simp [s69]⟩,
      keep_own hIq (by simp) hOS hOA k4 (frame_setSc _ _ _) (by simp) (by simp) (by simp)⟩

/-- The bisection count of ELL-1 in the step bound, read off `R`, `p`, `w`, `e` only. -/
noncomputable def oneCnt (R p wv e : ℝ) : ℕ := ⌈Real.logb 2 (2 * R / |e / (p * (R + |wv|))|)⌉₊

/-- The step bound of the bisection branch of ELL-1 with `c` halvings. -/
def kOneC (Kq c : ℕ) : ℕ := 17 + ((c * 4 + 4) + (1 + (1 + (1 + ((c * (Kq + 7 + 3) + 3) + (2 + 1))))))
/-- The step bound of ELL-1 after the test `a₀ ∈ Q`. -/
def kOneB (Kq c : ℕ) : ℕ := 7 + (2 + (Kq + (kOneC Kq c + 2)))
/-- The step bound of ELL-1 after the stops (c0). -/
def kOneA (Kq c : ℕ) : ℕ := 2 + (Kq + (kOneB Kq c + 1))
/-- The step bound of ELL-1 with `c` halvings. -/
def kOne (Kq c : ℕ) : ℕ := 1 + (2 + (2 + (2 + (5 + ((kOneA Kq c + 2) + 2)))))

theorem kOneC_mono {Kq c c' : ℕ} (h : c ≤ c') : kOneC Kq c ≤ kOneC Kq c' := by
  unfold kOneC
  have h1 := Nat.mul_le_mul_right 4 h
  have h2 := Nat.mul_le_mul_right (Kq + 7 + 3) h
  omega

theorem kOne_mono {Kq c c' : ℕ} (h : c ≤ c') : kOne Kq c ≤ kOne Kq c' := by
  unfold kOne kOneA kOneB
  have := kOneC_mono (Kq := Kq) h
  omega

/-- Inclusion in the lists of AP for ELL-1. -/
macro "subO" : tactic => `(tactic| (intro j hj; simp only [apN, apS, apA, oneC1, oneC2, oneC3, turnS, List.map_cons,
  List.map_nil, SI.dst, List.mem_cons, List.mem_range'_1, List.not_mem_nil, or_false] at hj ⊢ <;> omega))

/-- A variable inside the lists of AP for ELL-1. -/
macro "inO" : tactic => `(tactic| (simp only [List.mem_cons, List.mem_range'_1, List.not_mem_nil, or_false] <;>
  omega))

/-- The scalar instructions of a block of ELL-1 are well formed. -/
macro "one_ok" : tactic => `(tactic| (simp only [oneC1, oneC2, oneC3, List.all_cons, List.all_nil, SI.ok,
  Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]; (repeat' apply And.intro) <;> lay))

/-- A scalar outside the destinations of a block of ELL-1. -/
macro "one_nd" : tactic => `(tactic| (simp only [oneC1, oneC2, oneC3, List.map_cons, List.map_nil, SI.dst] <;>
  nmem_tac))

set_option maxHeartbeats 16000000 in
open Classical in
/-- The rule of ELL-1 (`d = 1`): it answers `ellOne` on the entries `0` of `a₀`, `w`, `P` in `ok`, `out`. -/
theorem runs_ellOneCode {Q : Set (Fin d → ℝ)} {Iq : Env d → Prop} {Kq : ℕ} {nsQ ssQ asQ : List ℕ}
    (hp : V.Ok L nsQ ssQ asQ) (hmem : MemRule L w memQ V Q Iq Kq nsQ ssQ asQ) (hIq : IqRule V Iq) (hd1 : d = 1)
    (σ : Env d) (hd : σ.nat V.dv = d) (h1 : σ.nat V.one = 1) (hI : Iq σ) :
    Runs L w (ellOneCode L memQ V) σ (kOne Kq (oneCnt (σ.sc V.R) (σ.arr V.P 0) (σ.arr V.w 0) (σ.sc V.e)))
      (fun σ' => APOut V ((ellOne {x | (fun _ => x) ∈ Q} (σ.arr V.a0 0) (σ.sc V.r) (σ.sc V.R) (σ.arr V.P 0)
        (σ.arr V.w 0) (σ.sc V.e)).map (fun x _ => x)) σ' ∧ KP Iq nsQ ssQ asQ (apN V) (apS V) (apA V) σ σ') := by
  subst hd1
  layout_facts
  have _hRB := hp.RB
  have _hrB := hp.rB
  have _heB := hp.eB
  let G : Env 1 → Prop := KP Iq nsQ ssQ asQ (apN V) (List.range' V.sB 128) (V.qv :: List.range' V.aB 14) σ
  have hS : ∀ j ∈ List.range' V.sB 128, j ∈ apS V := by subO
  have hA : ∀ j ∈ V.qv :: List.range' V.aB 14, j ∈ apA V := by subO
  have liftF : ∀ σa σb (ns ss as : List ℕ), G σa → Env.Frame σa σb ns ss as → (∀ j ∈ ns, j ∈ apN V) →
      (∀ j ∈ ss, j ∈ List.range' V.sB 128) → (∀ j ∈ as, j ∈ V.qv :: List.range' V.aB 14) → G σb :=
    fun σa σb ns ss as g f hn hs ha => keep_own hIq (fun _ h => h) hS hA g f hn hs ha
  have scG : ∀ σa (x : ℕ) (v : ℝ), x ∈ List.range' V.sB 128 → G σa → G (σa.setSc x v) := fun σa x v hx g =>
    liftF _ _ _ _ _ g (frame_setSc _ _ _) (by simp) (by simpa using hx) (by simp)
  have fin0 : ∀ σa (v : ℝ), G σa → KP Iq nsQ ssQ asQ (apN V) (apS V) (apA V) σ (σa.setSc V.ok v) := fun σa v g =>
    keep_own hIq (fun _ h => h) (fun _ h => h) (fun _ h => h) (keep_mono g (fun _ h => h) hS hA) (frame_setSc _ _ _)
      (by simp) (by simp [apS]) (by simp)
  have fin1 : ∀ σa (k : ℕ) (x v : ℝ), G σa →
      KP Iq nsQ ssQ asQ (apN V) (apS V) (apA V) σ ((σa.setArr V.out k x).setSc V.ok v) := fun σa k x v g =>
    keep_own hIq (fun _ h => h) (fun _ h => h) (fun _ h => h)
      (keep_own hIq (fun _ h => h) (fun _ h => h) (fun _ h => h) (keep_mono g (fun _ h => h) hS hA)
        (frame_setArr _ _ _ _) (by simp) (by simp) (by simp [apA]))
      (frame_setSc _ _ _) (by simp) (by simp [apS]) (by simp)
  have memS : ∀ σa, G σa → σa.nat V.dv = 1 → σa.nat V.one = 1 → ∀ x : ℝ, σa.vec V.qv = (fun _ => x) →
      Runs L w memQ σa Kq (fun σb => σb.sc V.qo = (if (fun _ => x) ∈ Q then 1 else 0) ∧
        Env.Frame σa σb nsQ ssQ asQ ∧ G σb) :=
    fun σa g hd' ho' x hv => runs_mono (hmem σa g.1 hd' ho') le_rfl (fun σb h => by
      obtain ⟨q, f, I⟩ := h
      exact ⟨by rw [q, hv], f, keep_mem g f I⟩)
  have gR : ∀ σa, G σa → σa.sc V.R = σ.sc V.R := fun σa g => g.sc (by nmem_tac) hp.R_sQ
  have gr : ∀ σa, G σa → σa.sc V.r = σ.sc V.r := fun σa g => g.sc (by nmem_tac) hp.r_sQ
  have ge : ∀ σa, G σa → σa.sc V.e = σ.sc V.e := fun σa g => g.sc (by nmem_tac) hp.e_sQ
  have gd : ∀ σa, G σa → σa.nat V.dv = 1 := fun σa g => by rw [g.nat (by simp only [apN]; nmem_tac) hp.dv_nQ, hd]
  have go : ∀ σa, G σa → σa.nat V.one = 1 := fun σa g => by rw [g.nat (by simp only [apN]; nmem_tac) hp.one_nQ, h1]
  have g13 : ∀ σa σb : Env 1, σb.nat (V.nB + 13) = 0 → Env.Frame σb σa nsQ ssQ asQ → σa.nat (V.nB + 13) = 0 :=
    fun σa σb h f => by rw [f.1 _ (hp.nN_nQ (by omega) (by omega)), h]
  have qS : ∀ (σa σb : Env 1) (x : ℕ), V.sB ≤ x → x < V.sB + 128 → Env.Frame σb σa nsQ ssQ asQ → σa.sc x = σb.sc x :=
    fun σa σb x h1 h2 f => f.2.1 _ (hp.sB_sQ h1 h2)
  rw [ellOneCode_eq]; unfold kOne
  refine runs_seq (runs_nconst (by lay) 0) (fun σ1 e1 => ?_)
  have n1 : σ1.nat (V.nB + 13) = 0 := by rw [e1]; simp
  have g1 : G σ1 := by rw [e1]; exact liftF _ _ _ _ _ (keep_refl hI) (frame_setNat _ _ _) (by subO) (by simp) (by simp)
  refine runs_seq (runs_aget (by lay) (by lay) (by lay) (by rw [n1]; unfold asz; omega)) (fun σ2 e2 => ?_)
  refine runs_seq (runs_aget (by lay) (by lay) (by lay) (by rw [e2, Env.setSc_nat, n1]; unfold asz; omega))
    (fun σ3 e3 => ?_)
  refine runs_seq (runs_aget (by lay) (by lay) (by lay)
    (by rw [e3, Env.setSc_nat, e2, Env.setSc_nat, n1]; unfold asz; omega)) (fun σ4 e4 => ?_)
  have g4 : G σ4 := by rw [e4, e3, e2]; exact scG _ _ _ (by inO) (scG _ _ _ (by inO) (scG _ _ _ (by inO) g1))
  have n4 : σ4.nat (V.nB + 13) = 0 := by rw [e4, e3, e2]; simp only [Env.setSc_nat]; exact n1
  have v60 : σ4.sc (V.sB + 60) = σ.arr V.a0 0 := by
    rw [e4, e3, e2, e1]
    simp (disch := omega) only [Env.setSc_sc, Env.setSc_arr, Env.setSc_nat, Env.setNat_arr, Env.setNat_nat, if_pos,
      if_neg, ↓reduceIte]
  have v61 : σ4.sc (V.sB + 61) = σ.arr V.w 0 := by
    rw [e4, e3, e2, e1]
    simp (disch := omega) only [Env.setSc_sc, Env.setSc_arr, Env.setSc_nat, Env.setNat_arr, Env.setNat_nat, if_pos,
      if_neg, ↓reduceIte]
  have v62 : σ4.sc (V.sB + 62) = σ.arr V.P 0 := by
    rw [e4, e3, e2, e1]
    simp (disch := omega) only [Env.setSc_sc, Env.setSc_arr, Env.setSc_nat, Env.setNat_arr, Env.setNat_nat, if_pos,
      if_neg, ↓reduceIte]
  refine runs_sprogThen' (oneC1 V) (by one_ok) sCost_oneC1 ?_
  generalize e5 : ({ σ4 with sc := sEval σ4.nat (oneC1 V) σ4.sc } : Env 1) = σ5
  obtain ⟨c63, c64, c60⟩ := oneC1_val (V := V) σ4.nat σ4.sc
  have s5 : σ5.sc = sEval σ4.nat (oneC1 V) σ4.sc := by rw [← e5]
  have g5 : G σ5 := by rw [← e5]; exact liftF _ _ _ _ _ g4 (Env.frame_sEval σ4 _) (by simp) (by subO) (by simp)
  have N5 : σ5.nat = σ4.nat := by rw [← e5]
  have d5 : ∀ x, x ∉ (oneC1 V).map SI.dst → σ5.sc x = σ4.sc x := fun x hx => by rw [s5]; exact sEval_frame _ _ _ hx
  have w63 : σ5.sc (V.sB + 63) = |σ.arr V.a0 0| := by rw [s5, c63, v60, max_zero_sub]
  have w64 : σ5.sc (V.sB + 64) = 0 := by rw [s5, c64]
  have w60 : σ5.sc (V.sB + 60) = σ.arr V.a0 0 := by rw [s5, c60, v60]
  have w61 : σ5.sc (V.sB + 61) = σ.arr V.w 0 := by rw [d5 _ (by one_nd), v61]
  have w62 : σ5.sc (V.sB + 62) = σ.arr V.P 0 := by rw [d5 _ (by one_nd), v62]
  by_cases hRr : σ.sc V.R < σ.sc V.r
  · refine runs_mono (runs_ifS_t (by lay) (by lay) (by rw [gR σ5 g5, gr σ5 g5]; exact hRr) (runs_sconst (by lay) 0))
      (by omega) (fun σ' e' => ?_)
    subst e'
    have hres : ellOne {x | (fun _ => x) ∈ Q} (σ.arr V.a0 0) (σ.sc V.r) (σ.sc V.R) (σ.arr V.P 0) (σ.arr V.w 0)
        (σ.sc V.e) = none := by unfold ellOne; rw [if_pos (Or.inl hRr)]
    rw [hres]
    exact ⟨by simp [APOut], fin0 _ _ g5⟩
  refine runs_ifS_f (by lay) (by lay) (by rw [gR σ5 g5, gr σ5 g5]; exact hRr) ?_
  by_cases hRa : σ.sc V.R < |σ.arr V.a0 0|
  · refine runs_mono (runs_ifS_t (by lay) (by lay) (by rw [gR σ5 g5, w63]; exact hRa) (runs_sconst (by lay) 0))
      (by omega) (fun σ' e' => ?_)
    subst e'
    have hres : ellOne {x | (fun _ => x) ∈ Q} (σ.arr V.a0 0) (σ.sc V.r) (σ.sc V.R) (σ.arr V.P 0) (σ.arr V.w 0)
        (σ.sc V.e) = none := by unfold ellOne; rw [if_pos (Or.inr hRa)]
    rw [hres]
    exact ⟨by simp [APOut], fin0 _ _ g5⟩
  refine runs_ifS_f (by lay) (by lay) (by rw [gR σ5 g5, w63]; exact hRa) ?_
  have hR0 : 0 ≤ σ.sc V.R := le_trans (abs_nonneg _) (not_lt.1 hRa)
  unfold kOneA
  refine runs_seq (runs_aset (by lay) (by lay) (by lay) (by rw [N5, n4]; unfold asz; omega)) (fun σ6 e6 => ?_)
  have g6 : G σ6 := by rw [e6]; exact liftF _ _ _ _ _ g5 (frame_setArr _ _ _ _) (by simp) (by simp) (by simp)
  have v6 : σ6.vec V.qv = fun _ => σ.arr V.a0 0 := by rw [e6, N5, n4, w60]; exact vec_setArr_one _ _ _
  refine runs_seq (memS σ6 g6 (gd σ6 g6) (go σ6 g6) _ v6) (fun σ7 h7 => ?_)
  obtain ⟨q7, f7, g7⟩ := h7
  have x64 : σ7.sc (V.sB + 64) = 0 := by rw [qS _ _ _ (by omega) (by omega) f7, e6, Env.setArr_sc, w64]
  by_cases haQ : (fun _ => σ.arr V.a0 0) ∈ Q
  swap
  · rw [if_neg haQ] at q7
    refine runs_mono (runs_ifS_f (by lay) (by lay) (by rw [x64, q7]; exact lt_irrefl 0) (runs_sconst (by lay) 0))
      (by unfold kOneB; omega) (fun σ' e' => ?_)
    subst e'
    have hres : ellOne {x | (fun _ => x) ∈ Q} (σ.arr V.a0 0) (σ.sc V.r) (σ.sc V.R) (σ.arr V.P 0) (σ.arr V.w 0)
        (σ.sc V.e) = none := ellOne_noQ hRr hRa haQ
    rw [hres]
    exact ⟨by simp [APOut], fin0 _ _ g7⟩
  rw [if_pos haQ] at q7
  refine runs_ifS_t (by lay) (by lay) (by rw [x64, q7]; exact one_pos) ?_
  unfold kOneB
  refine runs_sprogThen' (oneC2 V) (by one_ok) sCost_oneC2 ?_
  generalize e8 : ({ σ7 with sc := sEval σ7.nat (oneC2 V) σ7.sc } : Env 1) = σ8
  have s8 : σ8.sc = sEval σ7.nat (oneC2 V) σ7.sc := by rw [← e8]
  have N8 : σ8.nat = σ7.nat := by rw [← e8]
  have g8 : G σ8 := by rw [← e8]; exact liftF _ _ _ _ _ g7 (Env.frame_sEval σ7 _) (by simp) (by subO) (by simp)
  have d8 : ∀ x, x ∉ (oneC2 V).map SI.dst → σ8.sc x = σ7.sc x := fun x hx => by rw [s8]; exact sEval_frame _ _ _ hx
  have x61 : σ7.sc (V.sB + 61) = σ.arr V.w 0 := by rw [qS _ _ _ (by omega) (by omega) f7, e6, Env.setArr_sc, w61]
  have n7 : σ7.nat (V.nB + 13) = 0 := g13 _ _ (by rw [e6, Env.setArr_nat, N5, n4]) f7
  have y65 : σ8.sc (V.sB + 65) = max (-σ.sc V.R) (min (σ.sc V.R) (σ.arr V.w 0)) := by
    rw [s8, oneC2_val _ _ hp.RB, x64, x61, gR σ7 g7, zero_sub]
  refine runs_seq (runs_aset (by lay) (by lay) (by lay) (by rw [N8, n7]; unfold asz; omega)) (fun σ9 e9 => ?_)
  have g9 : G σ9 := by rw [e9]; exact liftF _ _ _ _ _ g8 (frame_setArr _ _ _ _) (by simp) (by simp) (by simp)
  have v9 : σ9.vec V.qv = fun _ => max (-σ.sc V.R) (min (σ.sc V.R) (σ.arr V.w 0)) := by
    rw [e9, N8, n7, y65]; exact vec_setArr_one _ _ _
  refine runs_seq (memS σ9 g9 (gd σ9 g9) (go σ9 g9) _ v9) (fun σ10 h10 => ?_)
  obtain ⟨q10, f10, g10⟩ := h10
  have n10 : σ10.nat (V.nB + 13) = 0 := g13 _ _ (by rw [e9, Env.setArr_nat, N8, n7]) f10
  have z10 : ∀ x, V.sB ≤ x → x < V.sB + 128 → σ10.sc x = σ8.sc x := fun x h1 h2 => by
    rw [qS _ _ _ h1 h2 f10, e9, Env.setArr_sc]
  have u64 : σ10.sc (V.sB + 64) = 0 := by rw [z10 _ (by omega) (by omega), d8 _ (by one_nd), x64]
  by_cases hwQ : (fun _ => max (-σ.sc V.R) (min (σ.sc V.R) (σ.arr V.w 0))) ∈ Q
  · rw [if_pos hwQ] at q10
    refine runs_mono (K := (2 + 1) + 1) ?_ (by unfold kOneC; omega) (fun _ h => h)
    refine runs_ifS_t (by lay) (by lay) (by rw [u64, q10]; exact one_pos) ?_
    refine runs_seq (runs_aset (by lay) (by lay) (by lay) (by rw [n10]; unfold asz; omega)) (fun σ11 e11 => ?_)
    refine runs_mono (runs_sconst (by lay) 1) le_rfl (fun σ12 e12 => ?_)
    subst e12 e11
    rw [ellOne_clamp hRr hRa haQ hwQ]
    simp only [Option.map_some, APOut]
    refine ⟨⟨by simp, ?_⟩, fin1 _ _ _ _ g10⟩
    rw [Env.setSc_vec, n10, z10 _ (by omega) (by omega), y65]; exact vec_setArr_one _ _ _
  rw [if_neg hwQ] at q10
  refine runs_ifS_f (by lay) (by lay) (by rw [u64, q10]; exact lt_irrefl 0) ?_
  have hcl : |max (-σ.sc V.R) (min (σ.sc V.R) (σ.arr V.w 0))| ≤ σ.sc V.R := by
    have := abs_clamp_le (σ.sc V.R) (σ.arr V.w 0) hR0; rwa [zero_sub] at this
  obtain ⟨c, hc⟩ : ∃ c, ⌈Real.log (|max (-σ.sc V.R) (min (σ.sc V.R) (σ.arr V.w 0)) - σ.arr V.a0 0| /
      (σ.sc V.e / (σ.arr V.P 0 * (σ.sc V.R + |σ.arr V.w 0|)))) / Real.log 2⌉₊ = c := ⟨_, rfl⟩
  have hcnt : c ≤ oneCnt (σ.sc V.R) (σ.arr V.P 0) (σ.arr V.w 0) (σ.sc V.e) := by
    rw [← hc]
    exact ceil_logb_abs_le (max (-σ.sc V.R) (min (σ.sc V.R) (σ.arr V.w 0)) - σ.arr V.a0 0)
      (σ.sc V.e / (σ.arr V.P 0 * (σ.sc V.R + |σ.arr V.w 0|))) (σ.sc V.R) hR0
      (abs_sub_le_two_mul hcl (not_lt.1 hRa))
  refine runs_mono (K := kOneC Kq c) ?_ (kOneC_mono hcnt) (fun _ h => h)
  unfold kOneC
  refine runs_sprogThen' (oneC3 V) (by one_ok) sCost_oneC3 ?_
  generalize e11 : ({ σ10 with sc := sEval σ10.nat (oneC3 V) σ10.sc } : Env 1) = σ11
  have s11 : σ11.sc = sEval σ10.nat (oneC3 V) σ10.sc := by rw [← e11]
  have N11 : σ11.nat = σ10.nat := by rw [← e11]
  have g11 : G σ11 := by rw [← e11]; exact liftF _ _ _ _ _ g10 (Env.frame_sEval σ10 _) (by simp) (by subO) (by simp)
  have d11 : ∀ x, x ∉ (oneC3 V).map SI.dst → σ11.sc x = σ10.sc x := fun x hx => by
    rw [s11]; exact sEval_frame _ _ _ hx
  have u60 : σ10.sc (V.sB + 60) = σ.arr V.a0 0 := by
    rw [z10 _ (by omega) (by omega), d8 _ (by one_nd), qS _ _ _ (by omega) (by omega) f7, e6, Env.setArr_sc, w60]
  have u61 : σ10.sc (V.sB + 61) = σ.arr V.w 0 := by rw [z10 _ (by omega) (by omega), d8 _ (by one_nd), x61]
  have u62 : σ10.sc (V.sB + 62) = σ.arr V.P 0 := by
    rw [z10 _ (by omega) (by omega), d8 _ (by one_nd), qS _ _ _ (by omega) (by omega) f7, e6, Env.setArr_sc, w62]
  have u65 : σ10.sc (V.sB + 65) = max (-σ.sc V.R) (min (σ.sc V.R) (σ.arr V.w 0)) := by
    rw [z10 _ (by omega) (by omega), y65]
  have c71 : ⌈σ11.sc (V.sB + 71)⌉₊ = c := by
    rw [s11, oneC3_val _ _ hp.RB hp.eB, u60, u61, u62, u64, u65, gR σ10 g10, ge σ10 g10, max_zero_sub, max_zero_sub,
      hc]
  have o11 : σ11.nat V.one = 1 := by rw [N11]; exact go σ10 g10
  refine runs_seq (runs_mono (runs_nceil σ11 (by lay) (by lay) (by lay) (by lay) (by lay) (by omega) o11)
    (le_of_eq (by rw [c71])) (fun _ h => h)) (fun σ12 e12 => ?_)
  refine runs_seq (runs_smov (by lay) (by lay)) (fun σ13 e13 => ?_)
  refine runs_seq (runs_smov (by lay) (by lay)) (fun σ14 e14 => ?_)
  refine runs_seq (runs_sconst (by lay) (1 / 2)) (fun σ15 e15 => ?_)
  have g15 : G σ15 := by
    rw [e15, e14, e13, e12]
    exact scG _ _ _ (by inO) (scG _ _ _ (by inO) (scG _ _ _ (by inO) (scG _ _ _ (by inO)
      (liftF _ _ _ _ _ g11 (frame_setNat _ _ _) (by subO) (by simp) (by simp)))))
  have n15 : σ15.nat (V.nB + 13) = 0 := by
    rw [e15, e14, e13, e12]; simp (disch := omega) only [Env.setSc_nat, Env.setNat_nat, if_neg, ↓reduceIte]; rw [N11, n10]
  have c15 : σ15.nat (V.nB + 14) = c := by
    rw [e15, e14, e13, e12]; simp only [Env.setSc_nat, Env.setNat_nat, if_true]; exact c71
  have o15 : σ15.nat V.one = 1 := go σ15 g15
  have p64 : σ15.sc (V.sB + 64) = 0 := by
    rw [e15, e14, e13, e12]; simp (disch := omega) only [Env.setSc_sc, Env.setNat_sc, if_neg]
    rw [d11 _ (by one_nd), u64]
  have p70 : σ15.sc (V.sB + 70) = ((1 / 2 : ℚ) : ℝ) := by
    rw [e15]; simp only [Env.setSc_sc, if_true]
  have p67 : σ15.sc (V.sB + 67) = σ.arr V.a0 0 := by
    rw [e15, e14, e13, e12]; simp (disch := omega) only [Env.setSc_sc, Env.setNat_sc, if_neg, if_pos, ↓reduceIte]
    rw [d11 _ (by one_nd), u60]
  have p68 : σ15.sc (V.sB + 68) = max (-σ.sc V.R) (min (σ.sc V.R) (σ.arr V.w 0)) := by
    rw [e15, e14, e13, e12]; simp (disch := omega) only [Env.setSc_sc, Env.setNat_sc, if_neg, if_pos, ↓reduceIte]
    rw [d11 _ (by one_nd), u65]
  refine runs_seq (runs_forN (i := V.nB + 15) (n := V.nB + 14) (by lay) (by lay) (by lay) (by omega) (by lay) c
    (Kq + 7) (fun t σ' => G σ' ∧ σ'.nat (V.nB + 13) = 0 ∧ σ'.sc (V.sB + 64) = 0 ∧
      σ'.sc (V.sB + 70) = ((1 / 2 : ℚ) : ℝ) ∧
      σ'.sc (V.sB + 67) = (oBisectLo (· ∈ {x : ℝ | (fun _ => x) ∈ Q}) (σ.arr V.a0 0)
        (max (-σ.sc V.R) (min (σ.sc V.R) (σ.arr V.w 0))) t).1 ∧
      σ'.sc (V.sB + 68) = (oBisectLo (· ∈ {x : ℝ | (fun _ => x) ∈ Q}) (σ.arr V.a0 0)
        (max (-σ.sc V.R) (min (σ.sc V.R) (σ.arr V.w 0))) t).2) σ15 c15 o15 ?_ ?_) (fun σ16 h16 => ?_)
  · refine ⟨liftF _ _ _ _ _ g15 (frame_setNat _ _ _) (by subO) (by simp) (by simp), ?_, ?_, ?_, ?_, ?_⟩
    · simp (disch := omega) only [Env.setNat_nat, if_neg]; exact n15
    · rw [Env.setNat_sc, p64]
    · rw [Env.setNat_sc, p70]
    · rw [Env.setNat_sc, p67]; rfl
    · rw [Env.setNat_sc, p68]; rfl
  · intro t _ σ' ⟨gt, n13, z64, h70, l67, l68⟩ hit hin ho
    refine runs_mono (runs_ellOneTurn hp hmem hIq rfl σ' (gd σ' gt) ho gt.1 n13 z64 h70) le_rfl (fun σ'' h'' => ?_)
    obtain ⟨hT, hF, k''⟩ := h''
    have G'' : G σ'' := keep_trans gt (keep_mono k'' (by simp) (by subO) (by simp))
    have nn : ∀ j, V.nB ≤ j → j < V.nB + 16 → σ''.nat j = σ'.nat j := fun j h1 h2 =>
      k''.nat (by simp) (hp.nN_nQ h1 h2)
    refine ⟨by rw [nn _ (by omega) (by omega), hit], by rw [nn _ (by omega) (by omega), hin],
      by rw [k''.nat (by simp) hp.one_nQ, ho], liftF _ _ _ _ _ G'' (frame_setNat _ _ _) (by subO) (by simp) (by simp),
      ?_, ?_, ?_, ?_⟩
    · simp (disch := omega) only [Env.setNat_nat, if_neg]; rw [nn _ (by omega) (by omega), n13]
    · rw [Env.setNat_sc, k''.sc (by simp only [turnS]; nmem_tac) (hp.sB_sQ (by omega) (by omega)), z64]
    · rw [Env.setNat_sc, k''.sc (by simp only [turnS]; nmem_tac) (hp.sB_sQ (by omega) (by omega)), h70]
    · rw [Env.setNat_sc]
      by_cases hm : (fun _ => (σ'.sc (V.sB + 67) + σ'.sc (V.sB + 68)) / 2) ∈ Q
      · obtain ⟨e67, e68⟩ := hT hm
        rw [l67, l68] at hm
        rw [e67, e68, oBisectLo_succ_pos (Pr := (· ∈ {x : ℝ | (fun _ => x) ∈ Q})) hm, l67, l68]
        exact ⟨rfl, rfl⟩
      · obtain ⟨e67, e68⟩ := hF hm
        rw [l67, l68] at hm
        rw [e67, e68, oBisectLo_succ_neg (Pr := (· ∈ {x : ℝ | (fun _ => x) ∈ Q})) hm, l67, l68]
        exact ⟨rfl, rfl⟩
  obtain ⟨⟨g16, n16, -, -, l67, -⟩, -⟩ := h16
  refine runs_seq (runs_aset (by lay) (by lay) (by lay) (by rw [n16]; unfold asz; omega)) (fun σ17 e17 => ?_)
  refine runs_mono (runs_sconst (by lay) 1) le_rfl (fun σ18 e18 => ?_)
  subst e18 e17
  rw [ellOne_bisect hRr hRa haQ hwQ, hc]
  simp only [Option.map_some, APOut]
  refine ⟨⟨by simp, ?_⟩, fin1 _ _ _ _ g16⟩
  rw [Env.setSc_vec, n16, l67]; exact vec_setArr_one _ _ _

end AdversarialBco.Poly.AP
