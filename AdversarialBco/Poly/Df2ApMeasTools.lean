/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2Oracle

@[expose] public section

/-!
# The projection routine `apCall` is measurable in a parameter

Every procedure of `AdversarialBco/Poly/Df2Oracle.lean` (bisection, the gauge value, LINE, SEP, the central cut,
ELL-cap, ELL-1, `apCall`) is measurable as a function of a parameter `x : X` on which its arguments depend
measurably; the body `Q x` enters through its graph `{(x, y) | y ∈ Q x}`, a measurable set (`GraphMeas`). The routine
`apCall` itself is measurable by `meas_apCall`.

Mathlib has no σ-algebra on `Option α` at the pin: the scoped instance `instOpt` is the comap of
`Option α → α ⊕ Unit`, so that `some` is measurable, `{o | o.isSome}` is measurable, and `Option.elim`, `bind`,
`map` of measurable maps are measurable (`meas_optElim`, `meas_optBind`, `meas_optMap`). The records `LineWin`,
`EllSt`, `EllConsts` get the comap of the tuple of their fields. A loop run a measurable number of times is measurable
(`measurable_natDep`).
-/

open MeasureTheory Matrix
open scoped Matrix

namespace AdversarialBco.Poly.ApMeas

open AdversarialBco.Poly

/-! ## Comap instances -/

theorem measurable_comap_iff {α β γ : Type*} [MeasurableSpace α] [mγ : MeasurableSpace γ] (g : β → γ)
    {f : α → β} : Measurable[_, mγ.comap g] f ↔ Measurable (g ∘ f) := by
  rw [measurable_iff_comap_le, measurable_iff_comap_le, MeasurableSpace.comap_comp]

/-! ## A σ-algebra on `Option α` -/

/-- `none ↦ inr ()`, `some a ↦ inl a`. -/
def optCode {α : Type*} (o : Option α) : α ⊕ Unit := o.elim (Sum.inr ()) Sum.inl

/-- The σ-algebra of `Option α`: the comap of `optCode`. -/
scoped instance instOpt {α : Type*} [MeasurableSpace α] : MeasurableSpace (Option α) :=
  MeasurableSpace.comap optCode inferInstance

section Opt

variable {X α β : Type*} [MeasurableSpace X] [MeasurableSpace α] [MeasurableSpace β]

theorem measurable_opt_iff {f : X → Option α} : Measurable f ↔ Measurable fun x => optCode (f x) :=
  measurable_comap_iff optCode

theorem measurable_optCode : Measurable (optCode : Option α → α ⊕ Unit) := comap_measurable _

theorem measurable_some' : Measurable (fun a : α => (some a : Option α)) := by
  rw [measurable_opt_iff]
  exact measurable_inl

theorem measurableSet_isSome : MeasurableSet {o : Option α | o.isSome = true} := by
  have h : {o : Option α | o.isSome = true} = optCode ⁻¹' Set.range Sum.inl := by
    ext o
    cases o <;> simp [optCode]
  rw [h]
  exact measurable_optCode measurableSet_range_inl

theorem measurable_getD (a : α) : Measurable (fun o : Option α => o.getD a) := by
  have h : (fun o : Option α => o.getD a) = (Sum.elim id fun _ : Unit => a) ∘ optCode := by
    funext o
    cases o <;> rfl
  rw [h]
  exact (measurable_id.sumElim measurable_const).comp measurable_optCode

theorem meas_optIsSome {o : X → Option α} (ho : Measurable o) :
    MeasurableSet {x | (o x).isSome = true} :=
  ho measurableSet_isSome

/-- `Option.elim` of measurable maps is measurable. -/
theorem meas_optElim {o : X → Option α} (ho : Measurable o) {a : X → β} (ha : Measurable a)
    {b : X → α → β} (hb : Measurable fun p : X × α => b p.1 p.2) :
    Measurable fun x => (o x).elim (a x) (b x) := by
  classical
  rcases isEmpty_or_nonempty α with hα | ⟨⟨a0⟩⟩
  · have h : (fun x => (o x).elim (a x) (b x)) = a := by
      funext x
      cases hx : o x with
      | none => rfl
      | some y => exact isEmptyElim y
    rw [h]
    exact ha
  · have h : (fun x => (o x).elim (a x) (b x)) =
        fun x => if (o x).isSome = true then b x ((o x).getD a0) else a x := by
      funext x
      cases o x <;> rfl
    rw [h]
    exact Measurable.ite (meas_optIsSome ho) (hb.comp (measurable_id.prodMk ((measurable_getD a0).comp ho))) ha

theorem meas_optBind {o : X → Option α} (ho : Measurable o) {g : X → α → Option β}
    (hg : Measurable fun p : X × α => g p.1 p.2) : Measurable fun x => (o x).bind (g x) := by
  have h : (fun x => (o x).bind (g x)) = fun x => (o x).elim none (g x) := by
    funext x
    cases o x <;> rfl
  rw [h]
  exact meas_optElim ho measurable_const hg

theorem meas_optMap {o : X → Option α} (ho : Measurable o) {g : X → α → β}
    (hg : Measurable fun p : X × α => g p.1 p.2) : Measurable fun x => (o x).map (g x) := by
  have h : (fun x => (o x).map (g x)) = fun x => (o x).elim none (fun y => some (g x y)) := by
    funext x
    cases o x <;> rfl
  rw [h]
  exact meas_optElim ho measurable_const (measurable_some'.comp hg)

theorem meas_optSome {f : X → α} (hf : Measurable f) : Measurable fun x => (some (f x) : Option α) :=
  measurable_some'.comp hf

end Opt

/-! ## Loops run a measurable number of times -/

theorem measurable_natDep {X β : Type*} [MeasurableSpace X] [MeasurableSpace β] {F : ℕ → X → β}
    (hF : ∀ j, Measurable (F j)) {N : X → ℕ} (hN : Measurable N) : Measurable fun x => F (N x) x := by
  have h : Measurable fun p : X × ℕ => F p.2 p.1 := measurable_from_prod_countable_left fun j => hF j
  exact h.comp (measurable_id.prodMk hN)

/-! ## The records of the procedures -/

/-- The fields of a window of LINE. -/
def lineWinCode (W : LineWin) : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ := (W.p0, W.lam, W.v0, W.v1, W.v2, W.v3, W.v4)

scoped instance instLineWin : MeasurableSpace LineWin := MeasurableSpace.comap lineWinCode inferInstance

/-- The fields of a state of ELL. -/
def ellStCode {d : ℕ} (s : EllSt d) : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × Option (Fin d → ℝ) :=
  (s.A, s.a, s.best)

scoped instance instEllSt {d : ℕ} : MeasurableSpace (EllSt d) := MeasurableSpace.comap ellStCode inferInstance

/-- The fields of the constants of ELL-cap. -/
def ellConstsCode (k : EllConsts) : ℝ × ℝ × ℕ × ℕ × ℕ := (k.τ, k.ℓ1, k.N, k.J, k.B)

scoped instance instEllConsts : MeasurableSpace EllConsts := MeasurableSpace.comap ellConstsCode inferInstance

section Records

variable {X : Type*} [MeasurableSpace X]

theorem measurable_lineWin_iff {f : X → LineWin} : Measurable f ↔ Measurable fun x => lineWinCode (f x) :=
  measurable_comap_iff lineWinCode

theorem measurable_lineWin_code : Measurable (lineWinCode) := comap_measurable _

theorem meas_lineWin_mk {p0 lam v0 v1 v2 v3 v4 : X → ℝ} (h0 : Measurable p0) (h1 : Measurable lam)
    (h2 : Measurable v0) (h3 : Measurable v1) (h4 : Measurable v2) (h5 : Measurable v3) (h6 : Measurable v4) :
    Measurable fun x => (⟨p0 x, lam x, v0 x, v1 x, v2 x, v3 x, v4 x⟩ : LineWin) := by
  rw [measurable_lineWin_iff]
  exact h0.prodMk (h1.prodMk (h2.prodMk (h3.prodMk (h4.prodMk (h5.prodMk h6)))))

theorem measurable_lineWin_p0 : Measurable LineWin.p0 := measurable_fst.comp measurable_lineWin_code
theorem measurable_lineWin_lam : Measurable LineWin.lam :=
  measurable_fst.comp (measurable_snd.comp measurable_lineWin_code)
theorem measurable_lineWin_v1 : Measurable LineWin.v1 :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_lineWin_code)))
theorem measurable_lineWin_v2 : Measurable LineWin.v2 :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp measurable_lineWin_code))))
theorem measurable_lineWin_v3 : Measurable LineWin.v3 :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp measurable_lineWin_code)))))

theorem measurable_ellSt_iff {d : ℕ} {f : X → EllSt d} : Measurable f ↔ Measurable fun x => ellStCode (f x) :=
  measurable_comap_iff ellStCode

theorem measurable_ellSt_code {d : ℕ} : Measurable (ellStCode : EllSt d → _) := comap_measurable _

theorem meas_ellSt_mk {d : ℕ} {A : X → Matrix (Fin d) (Fin d) ℝ} {a : X → Fin d → ℝ}
    {b : X → Option (Fin d → ℝ)} (hA : Measurable A) (ha : Measurable a) (hb : Measurable b) :
    Measurable fun x => (⟨A x, a x, b x⟩ : EllSt d) := by
  rw [measurable_ellSt_iff]
  exact hA.prodMk (ha.prodMk hb)

theorem measurable_ellSt_A {d : ℕ} : Measurable (EllSt.A : EllSt d → _) :=
  measurable_fst.comp measurable_ellSt_code
theorem measurable_ellSt_a {d : ℕ} : Measurable (EllSt.a : EllSt d → _) :=
  measurable_fst.comp (measurable_snd.comp measurable_ellSt_code)
theorem measurable_ellSt_best {d : ℕ} : Measurable (EllSt.best : EllSt d → _) :=
  measurable_snd.comp (measurable_snd.comp measurable_ellSt_code)

theorem measurable_ellConsts_iff {f : X → EllConsts} : Measurable f ↔ Measurable fun x => ellConstsCode (f x) :=
  measurable_comap_iff ellConstsCode

theorem measurable_ellConsts_code : Measurable ellConstsCode := comap_measurable _

theorem measurable_ellConsts_τ : Measurable EllConsts.τ := measurable_fst.comp measurable_ellConsts_code
theorem measurable_ellConsts_ℓ1 : Measurable EllConsts.ℓ1 :=
  measurable_fst.comp (measurable_snd.comp measurable_ellConsts_code)
theorem measurable_ellConsts_N : Measurable EllConsts.N :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_ellConsts_code))
theorem measurable_ellConsts_J : Measurable EllConsts.J :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_ellConsts_code)))
theorem measurable_ellConsts_B : Measurable EllConsts.B :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_ellConsts_code)))

end Records

/-! ## Bodies depending on a parameter -/

/-- The graph of a family of bodies is measurable. -/
def GraphMeas {X : Type*} [MeasurableSpace X] {d : ℕ} (Q : X → Set (Fin d → ℝ)) : Prop :=
  MeasurableSet {p : X × (Fin d → ℝ) | p.2 ∈ Q p.1}

theorem GraphMeas.mem {X : Type*} [MeasurableSpace X] {d : ℕ} {Q : X → Set (Fin d → ℝ)} (hQ : GraphMeas Q)
    {y : X → Fin d → ℝ} (hy : Measurable y) : MeasurableSet {x | y x ∈ Q x} :=
  hQ.preimage (f := fun x => (x, y x)) (measurable_id.prodMk hy)

theorem measurable_oNorm {d : ℕ} : Measurable (oNorm : (Fin d → ℝ) → ℝ) := by
  unfold oNorm
  exact (continuous_id.dotProduct continuous_id).measurable.sqrt

/-! ## The procedures, one by one -/

theorem meas_oBisect {X : Type*} [MeasurableSpace X] (Pr : X → ℝ → Prop)
    (hPr : MeasurableSet {p : X × ℝ | Pr p.1 p.2}) (lo hi : X → ℝ) (hlo : Measurable lo) (hhi : Measurable hi)
    (j : ℕ) : Measurable fun x => oBisect (Pr x) (lo x) (hi x) j := by
  classical
  induction j with
  | zero => exact hlo.prodMk hhi
  | succ j ih =>
    have hm : Measurable fun x => ((oBisect (Pr x) (lo x) (hi x) j).1 + (oBisect (Pr x) (lo x) (hi x) j).2) / 2 :=
      (ih.fst.add ih.snd).div_const 2
    have hS : MeasurableSet {x | Pr x (((oBisect (Pr x) (lo x) (hi x) j).1 + (oBisect (Pr x) (lo x) (hi x) j).2) / 2)} :=
      hPr.preimage (f := fun x => (x, _)) (measurable_id.prodMk hm)
    simp only [oBisect]
    exact Measurable.ite hS (ih.fst.prodMk hm) (hm.prodMk ih.snd)

theorem meas_oBisectLo {X : Type*} [MeasurableSpace X] (Pr : X → ℝ → Prop)
    (hPr : MeasurableSet {p : X × ℝ | Pr p.1 p.2}) (lo hi : X → ℝ) (hlo : Measurable lo) (hhi : Measurable hi)
    (j : ℕ) : Measurable fun x => oBisectLo (Pr x) (lo x) (hi x) j := by
  classical
  induction j with
  | zero => exact hlo.prodMk hhi
  | succ j ih =>
    have hm : Measurable fun x => ((oBisectLo (Pr x) (lo x) (hi x) j).1 + (oBisectLo (Pr x) (lo x) (hi x) j).2) / 2 :=
      (ih.fst.add ih.snd).div_const 2
    have hS : MeasurableSet {x | Pr x (((oBisectLo (Pr x) (lo x) (hi x) j).1 + (oBisectLo (Pr x) (lo x) (hi x) j).2) / 2)} :=
      hPr.preimage (f := fun x => (x, _)) (measurable_id.prodMk hm)
    simp only [oBisectLo]
    exact Measurable.ite hS (hm.prodMk ih.snd) (ih.fst.prodMk hm)

theorem meas_oGaugeValCap {X : Type*} [MeasurableSpace X] {d : ℕ} (Q : X → Set (Fin d → ℝ)) (hQ : GraphMeas Q)
    (a0 : X → Fin d → ℝ) (r R : X → ℝ) (B : X → ℕ) (y : X → Fin d → ℝ) (η : X → ℝ) (ha0 : Measurable a0)
    (hr : Measurable r) (hR : Measurable R) (hB : Measurable B) (hy : Measurable y) (hη : Measurable η) :
    Measurable fun x => oGaugeValCap (Q x) (a0 x) (r x) (R x) (B x) (y x) (η x) := by
  rw [measurable_opt_iff]
  -- define the components of oGaugeVal
  let Pr : X → ℝ → Prop := fun x t => 0 < t ∧ a0 x + t⁻¹ • (y x - a0 x) ∈ Q x
  have hPr : MeasurableSet {p : X × ℝ | Pr p.1 p.2} := by
    have hpos : MeasurableSet {p : X × ℝ | 0 < p.2} :=
      measurableSet_lt measurable_const measurable_snd
    have hmem : MeasurableSet {p : X × ℝ | a0 p.1 + (p.2)⁻¹ • (y p.1 - a0 p.1) ∈ Q p.1} := by
      have hf : Measurable fun (p : X × ℝ) => (p.1, a0 p.1 + (p.2)⁻¹ • (y p.1 - a0 p.1)) := by
        refine measurable_fst.prodMk ?_
        refine (ha0.comp measurable_fst).add ?_
        refine (measurable_snd.inv).smul ?_
        exact (hy.comp measurable_fst).sub (ha0.comp measurable_fst)
      exact hQ.preimage hf
    exact hpos.inter hmem
  let lo : X → ℝ := fun x => oNorm (y x - a0 x) / (2 * R x)
  have hlo : Measurable lo := by
    unfold lo
    have hnum : Measurable fun x : X => oNorm (y x - a0 x) := measurable_oNorm.comp (hy.sub ha0)
    have hden : Measurable fun x : X => (2 : ℝ) * R x := measurable_const.mul hR
    exact hnum.div hden
  let hi : X → ℝ := fun x => oNorm (y x - a0 x) / r x
  have hhi : Measurable hi := by
    unfold hi
    have hnum : Measurable fun x : X => oNorm (y x - a0 x) := measurable_oNorm.comp (hy.sub ha0)
    exact hnum.div hr
  have h_valSteps : Measurable fun x => oValSteps (a0 x) (r x) (y x) (η x) := by
    unfold oValSteps
    have h_inner : Measurable fun x : X => oNorm (y x - a0 x) / (r x * η x) := by
      have hnum : Measurable fun x : X => oNorm (y x - a0 x) := measurable_oNorm.comp (hy.sub ha0)
      have hden : Measurable fun x : X => r x * η x := hr.mul hη
      exact hnum.div hden
    have h_logb : Measurable fun x : X => Real.logb 2 (oNorm (y x - a0 x) / (r x * η x)) := by
      have hlog : Measurable fun x : X => Real.log (oNorm (y x - a0 x) / (r x * η x)) :=
        Real.measurable_log.comp h_inner
      have hconst : Measurable fun _ : X => Real.log 2 := measurable_const
      exact hlog.div hconst
    exact h_logb.nat_ceil
  have h_oBisect_nat : ∀ j : ℕ, Measurable fun x => oBisect (Pr x) (lo x) (hi x) j :=
    fun j => meas_oBisect Pr hPr lo hi hlo hhi j
  have h_oBisect : Measurable fun x => oBisect (Pr x) (lo x) (hi x) (oValSteps (a0 x) (r x) (y x) (η x)) :=
    measurable_natDep h_oBisect_nat h_valSteps
  have h_eq : MeasurableSet {x | y x = a0 x} := measurableSet_eq_fun hy ha0
  -- the inner oGaugeVal expression (inlined)
  have h_inner : Measurable fun x =>
      (if y x = a0 x then 0 else (oBisect (Pr x) (lo x) (hi x) (oValSteps (a0 x) (r x) (y x) (η x))).2) :=
    Measurable.ite h_eq measurable_const (measurable_snd.comp h_oBisect)
  -- the condition B < oValSteps
  have h_cond : MeasurableSet {x | B x < oValSteps (a0 x) (r x) (y x) (η x)} :=
    measurableSet_lt hB h_valSteps
  -- combine: if B < oValSteps then Sum.inr () else Sum.inl (inner)
  have h_final : (fun x => optCode (oGaugeValCap (Q x) (a0 x) (r x) (R x) (B x) (y x) (η x))) =
      (fun x => if B x < oValSteps (a0 x) (r x) (y x) (η x) then Sum.inr () else Sum.inl
        ((if y x = a0 x then 0 else (oBisect (Pr x) (lo x) (hi x) (oValSteps (a0 x) (r x) (y x) (η x))).2))) := by
    ext x
    unfold oGaugeValCap optCode oGaugeVal
    split <;> rfl
  rw [h_final]
  refine Measurable.ite h_cond measurable_const (measurable_inl.comp h_inner)

theorem meas_lineFirst {X : Type*} [MeasurableSpace X] (ev : X → ℝ → ℝ → Option ℝ)
    (hev : Measurable fun p : X × ℝ × ℝ => ev p.1 p.2.1 p.2.2) (ℓ τ : X → ℝ) (hℓ : Measurable ℓ)
    (hτ : Measurable τ) : Measurable fun x => lineFirst (ev x) (ℓ x) (τ x) := by
  unfold lineFirst
  simp only [Option.bind_eq_bind, Option.pure_def]
  have hη : Measurable fun x => τ x * (ℓ x / 4) / 400 := (hτ.mul (hℓ.div_const 4)).div_const 400
  refine meas_optBind (hev.comp (measurable_id.prodMk (measurable_const.prodMk hη))) ?_
  refine meas_optBind (hev.comp (measurable_fst.prodMk ((hℓ.comp measurable_fst).div_const 4 |>.prodMk
    (hη.comp measurable_fst)))) ?_
  refine meas_optBind (hev.comp ((measurable_fst.comp measurable_fst).prodMk
    (((hℓ.comp (measurable_fst.comp measurable_fst)).div_const 4).const_mul 2 |>.prodMk
    (hη.comp (measurable_fst.comp measurable_fst))))) ?_
  refine meas_optBind (hev.comp ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
    (((hℓ.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).div_const 4).const_mul 3 |>.prodMk
    (hη.comp (measurable_fst.comp (measurable_fst.comp measurable_fst)))))) ?_
  refine meas_optBind (hev.comp ((measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
    (((hℓ.comp (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst)))).div_const 4).const_mul 4
    |>.prodMk (hη.comp (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))))))) ?_
  refine meas_optSome (meas_lineWin_mk measurable_const ?_ ?_ ?_ ?_ ?_ ?_)
  · exact (hℓ.comp (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))))).div_const 4
  · exact measurable_snd.comp (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst)))
  · exact measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))
  · exact measurable_snd.comp (measurable_fst.comp measurable_fst)
  · exact measurable_snd.comp measurable_fst
  · exact measurable_snd

attribute [local fun_prop] measurable_lineWin_p0 measurable_lineWin_lam measurable_lineWin_v1
  measurable_lineWin_v2 measurable_lineWin_v3

theorem meas_ev_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {ev : X → ℝ → ℝ → Option ℝ}
    (hev : Measurable fun p : X × ℝ × ℝ => ev p.1 p.2.1 p.2.2) {f : Y → X} {a b : Y → ℝ} (hf : Measurable f)
    (ha : Measurable a) (hb : Measurable b) : Measurable fun y => ev (f y) (a y) (b y) :=
  hev.comp (hf.prodMk (ha.prodMk hb))

theorem meas_lineHalve {X : Type*} [MeasurableSpace X] (ev : X → ℝ → ℝ → Option ℝ)
    (hev : Measurable fun p : X × ℝ × ℝ => ev p.1 p.2.1 p.2.2) (τ : X → ℝ) (hτ : Measurable τ) :
    Measurable fun p : X × LineWin => lineHalve (ev p.1) (τ p.1) p.2 := by
  unfold lineHalve
  simp only [Option.bind_eq_bind, Option.pure_def]
  refine meas_optBind (meas_ev_comp hev (by fun_prop) (by fun_prop) (by fun_prop)) ?_
  refine meas_optBind (meas_ev_comp hev (by fun_prop) (by fun_prop) (by fun_prop)) ?_
  refine meas_optBind (meas_ev_comp hev (by fun_prop) (by fun_prop) (by fun_prop)) ?_
  refine meas_optBind (meas_ev_comp hev (by fun_prop) (by fun_prop) (by fun_prop)) ?_
  refine meas_optBind (meas_ev_comp hev (by fun_prop) (by fun_prop) (by fun_prop)) ?_
  refine meas_optBind (meas_ev_comp hev (by fun_prop) (by fun_prop) (by fun_prop)) ?_
  refine meas_optSome (Measurable.ite ?_ ?_ ?_)
  · refine measurableSet_lt ?_ ?_
    · unfold LineWin.spread; fun_prop
    · unfold LineWin.spread; fun_prop
  · exact meas_lineWin_mk (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
      (by fun_prop)
  · exact meas_lineWin_mk (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
      (by fun_prop)

theorem meas_lineLoop {X : Type*} [MeasurableSpace X] (ev : X → ℝ → ℝ → Option ℝ)
    (hev : Measurable fun p : X × ℝ × ℝ => ev p.1 p.2.1 p.2.2) (τ : X → ℝ) (hτ : Measurable τ) (j : ℕ) :
    Measurable fun p : X × LineWin => lineLoop (ev p.1) (τ p.1) j p.2 := by
  induction j with
  | zero =>
    unfold lineLoop
    have h_sd : Measurable fun (p : X × LineWin) => p.2.sd := by
      dsimp [LineWin.sd]
      exact ((measurable_lineWin_v3.comp measurable_snd).add
        (measurable_lineWin_v1.comp measurable_snd)).sub
        ((measurable_lineWin_v2.comp measurable_snd).const_mul 2)
    have h_bound : Measurable fun (p : X × LineWin) => (τ p.1) * (p.2.lam) / 2 :=
      ((hτ.comp measurable_fst).mul (measurable_lineWin_lam.comp measurable_snd)).div_const 2
    have h_cond : MeasurableSet {p : X × LineWin | p.2.sd ≤ (τ p.1) * (p.2.lam) / 2} :=
      measurableSet_le h_sd h_bound
    refine Measurable.ite h_cond ?_ ?_
    · refine meas_optSome ?_
      have hp0 : Measurable fun (p : X × LineWin) => p.2.p0 := measurable_lineWin_p0.comp measurable_snd
      have hlam : Measurable fun (p : X × LineWin) => p.2.lam := measurable_lineWin_lam.comp measurable_snd
      exact (hp0.add (hlam.const_mul 2)).prodMk hlam
    · exact measurable_const
  | succ j ih =>
    unfold lineLoop
    have h_sd : Measurable fun (p : X × LineWin) => p.2.sd := by
      dsimp [LineWin.sd]
      exact ((measurable_lineWin_v3.comp measurable_snd).add
        (measurable_lineWin_v1.comp measurable_snd)).sub
        ((measurable_lineWin_v2.comp measurable_snd).const_mul 2)
    have h_bound : Measurable fun (p : X × LineWin) => (τ p.1) * (p.2.lam) / 2 :=
      ((hτ.comp measurable_fst).mul (measurable_lineWin_lam.comp measurable_snd)).div_const 2
    have h_cond : MeasurableSet {p : X × LineWin | p.2.sd ≤ (τ p.1) * (p.2.lam) / 2} :=
      measurableSet_le h_sd h_bound
    have h_lineHalve : Measurable fun p : X × LineWin => lineHalve (ev p.1) (τ p.1) p.2 :=
      meas_lineHalve ev hev τ hτ
    have h_cont : Measurable fun (q : (X × LineWin) × LineWin) => lineLoop (ev q.1.1) (τ q.1.1) j q.2 := by
      have : (fun q : (X × LineWin) × LineWin => lineLoop (ev q.1.1) (τ q.1.1) j q.2) =
        (fun p : X × LineWin => lineLoop (ev p.1) (τ p.1) j p.2) ∘ (fun q => (q.1.1, q.2)) := rfl
      rw [this]
      exact ih.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    refine Measurable.ite h_cond ?_ ?_
    · refine meas_optSome ?_
      have hp0 : Measurable fun (p : X × LineWin) => p.2.p0 := measurable_lineWin_p0.comp measurable_snd
      have hlam : Measurable fun (p : X × LineWin) => p.2.lam := measurable_lineWin_lam.comp measurable_snd
      exact (hp0.add (hlam.const_mul 2)).prodMk hlam
    · exact meas_optBind h_lineHalve h_cont

theorem meas_line {X : Type*} [MeasurableSpace X] (ev : X → ℝ → ℝ → Option ℝ)
    (hev : Measurable fun p : X × ℝ × ℝ => ev p.1 p.2.1 p.2.2) (ℓ τ : X → ℝ) (J : X → ℕ) (hℓ : Measurable ℓ)
    (hτ : Measurable τ) (hJ : Measurable J) : Measurable fun x => line (ev x) (ℓ x) (τ x) (J x) := by
  let F : ℕ → X → Option (ℝ × ℝ) := fun j x => line (ev x) (ℓ x) (τ x) j
  have hF : ∀ j, Measurable (F j) := by
    intro j
    unfold F
    have h_first : Measurable fun x => lineFirst (ev x) (ℓ x) (τ x) :=
      meas_lineFirst ev hev ℓ τ hℓ hτ
    have h_loop : Measurable fun p : X × LineWin => lineLoop (ev p.1) (τ p.1) j p.2 :=
      meas_lineLoop ev hev τ hτ j
    have h_bind := meas_optBind h_first (g := fun x w => lineLoop (ev x) (τ x) j w) h_loop
    simpa [line, Option.bind_eq_bind, Option.pure_def] using h_bind
  have h_main : Measurable fun x => F (J x) x :=
    measurable_natDep hF hJ
  simpa [F] using h_main

theorem meas_sepCoord {X : Type*} [MeasurableSpace X] {d : ℕ} (ev : X → (Fin d → ℝ) → ℝ → Option ℝ)
    (hev : Measurable fun p : X × (Fin d → ℝ) × ℝ => ev p.1 p.2.1 p.2.2) (τ L : X → ℝ) (J : X → ℕ)
    (hτ : Measurable τ) (hL : Measurable L) (hJ : Measurable J) (i : Fin d) :
    Measurable fun p : X × SepSt d => sepCoord (ev p.1) (τ p.1) (L p.1) (J p.1) i p.2 := by
  unfold sepCoord
  simp only [Option.bind_eq_bind, Option.pure_def]
  -- First meas_optBind: the line call
  have h_smul : Measurable fun p : (X × SepSt d) × ℝ × ℝ => p.2.1 • oUnit i :=
    ((measurable_fst.comp measurable_snd : Measurable fun p : (X × SepSt d) × ℝ × ℝ => p.2.1).smul
      (measurable_const (a := oUnit i) : Measurable fun _ : (X × SepSt d) × ℝ × ℝ => oUnit i))
  have h_fst1 : Measurable fun p : (X × SepSt d) × ℝ × ℝ => p.1.2.1 :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have h_add : Measurable fun p : (X × SepSt d) × ℝ × ℝ => p.1.2.1 + p.2.1 • oUnit i :=
    h_fst1.add h_smul
  have hev' : Measurable fun p : (X × SepSt d) × ℝ × ℝ => ev p.1.1 (p.1.2.1 + p.2.1 • oUnit i) p.2.2 :=
    hev.comp ((measurable_fst.comp measurable_fst).prodMk
      (h_add.prodMk (measurable_snd.comp measurable_snd)))
  have hℓ' : Measurable fun p : X × SepSt d => p.2.2.1 :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  let τ_fun : X × SepSt d → ℝ := fun p => τ p.1
  let J_fun : X × SepSt d → ℕ := fun p => J p.1
  have hτ_fun : Measurable τ_fun := hτ.comp measurable_fst
  have hJ_fun : Measurable J_fun := hJ.comp measurable_fst
  refine meas_optBind (meas_line (ev := fun (p : X × SepSt d) (s : ℝ) (η : ℝ) => ev p.1 (p.2.1 + s • oUnit i) η)
    hev' (fun p => p.2.2.1) τ_fun J_fun hℓ' hτ_fun hJ_fun)
    (meas_optSome ?_)
  · -- the tuple (p.1.2.1 + r.1 • oUnit i, τ p.1 * r.2 / (16 * L p.1), Function.update p.1.2.2.2 i r.2)
    have h_smul' : Measurable fun p : (X × SepSt d) × (ℝ × ℝ) => p.2.1 • oUnit i :=
      ((measurable_fst.comp measurable_snd : Measurable fun p : (X × SepSt d) × (ℝ × ℝ) => p.2.1).smul
        (measurable_const (a := oUnit i) : Measurable fun _ : (X × SepSt d) × (ℝ × ℝ) => oUnit i))
    have h_fst2 : Measurable fun p : (X × SepSt d) × (ℝ × ℝ) => p.1.2.1 :=
      measurable_fst.comp (measurable_snd.comp measurable_fst)
    have h_add' : Measurable fun p : (X × SepSt d) × (ℝ × ℝ) => p.1.2.1 + p.2.1 • oUnit i :=
      h_fst2.add h_smul'
    have h_tau : Measurable fun p : (X × SepSt d) × (ℝ × ℝ) => τ p.1.1 :=
      hτ.comp (measurable_fst.comp measurable_fst)
    have h_L : Measurable fun p : (X × SepSt d) × (ℝ × ℝ) => L p.1.1 :=
      hL.comp (measurable_fst.comp measurable_fst)
    have h_eta : Measurable fun p : (X × SepSt d) × (ℝ × ℝ) => p.2.2 :=
      measurable_snd.comp measurable_snd
    have h_num : Measurable fun p : (X × SepSt d) × (ℝ × ℝ) => (τ p.1.1) * p.2.2 :=
      h_tau.mul h_eta
    have h_denom : Measurable fun p : (X × SepSt d) × (ℝ × ℝ) => (16 : ℝ) * L p.1.1 :=
      (measurable_const (a := (16 : ℝ))).mul h_L
    have h_update : Measurable fun p : (X × SepSt d) × (ℝ × ℝ) => Function.update p.1.2.2.2 i p.2.2 :=
      (measurable_update' (a := i)).comp
        ((measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk
          (measurable_snd.comp measurable_snd))
    refine (h_add'.prodMk ((h_num.div h_denom).prodMk h_update))

theorem meas_sepCoords {X : Type*} [MeasurableSpace X] {d : ℕ} (ev : X → (Fin d → ℝ) → ℝ → Option ℝ)
    (hev : Measurable fun p : X × (Fin d → ℝ) × ℝ => ev p.1 p.2.1 p.2.2) (y0 : X → Fin d → ℝ)
    (τ ℓ1 L : X → ℝ) (J : X → ℕ) (hy0 : Measurable y0) (hτ : Measurable τ) (hℓ1 : Measurable ℓ1)
    (hL : Measurable L) (hJ : Measurable J) (k : ℕ) :
    Measurable fun x => sepCoords (ev x) (y0 x) (τ x) (ℓ1 x) (L x) (J x) k := by
  induction' k with k ih
  · -- k = 0
    unfold sepCoords
    refine meas_optSome ?_
    exact hy0.prodMk (hℓ1.prodMk measurable_const)
  · -- k = k + 1
    unfold sepCoords
    by_cases hk : k < d
    · -- case k < d
      simp [hk]
      refine meas_optBind ih ?_
      exact meas_sepCoord ev hev τ L J hτ hL hJ ⟨k, hk⟩
    · -- case ¬ (k < d)
      simp [hk]
      simpa using ih

theorem meas_oValsAll {X : Type*} [MeasurableSpace X] {d : ℕ} (ev : X → (Fin d → ℝ) → ℝ → Option ℝ)
    (hev : Measurable fun p : X × (Fin d → ℝ) × ℝ => ev p.1 p.2.1 p.2.2) (pts : X → Fin d → Fin d → ℝ)
    (η : X → Fin d → ℝ) (hpts : Measurable pts) (hη : Measurable η) :
    Measurable fun x => oValsAll (ev x) (pts x) (η x) := by
  classical
  have h_ev_i (i : Fin d) : Measurable fun x : X => ev x ((pts x) i) ((η x) i) := by
    have h_g_i : Measurable fun x : X => (x, (pts x) i, (η x) i) := by
      have h1 : Measurable fun x : X => (pts x) i := (measurable_pi_apply i).comp hpts
      have h2 : Measurable fun x : X => (η x) i := (measurable_pi_apply i).comp hη
      exact measurable_id.prodMk (h1.prodMk h2)
    exact hev.comp h_g_i
  have h_set : MeasurableSet {x : X | ∀ i, (ev x ((pts x) i) ((η x) i)).isSome = true} := by
    have h_each (i : Fin d) : MeasurableSet {x : X | (ev x ((pts x) i) ((η x) i)).isSome = true} :=
      meas_optIsSome (h_ev_i i)
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter h_each
  have h_eq : (fun x : X => oValsAll (ev x) (pts x) (η x)) =
      (fun x : X => if (∀ i, (ev x ((pts x) i) ((η x) i)).isSome = true) then
        some (fun i => (ev x ((pts x) i) ((η x) i)).getD 0) else none) := by
    funext x
    unfold oValsAll
    by_cases h : ∀ i, (ev x ((pts x) i) ((η x) i)).isSome = true
    · simp [h]
      funext i
      exact Option.get_eq_getD _
    · simp [h]
  rw [h_eq]
  refine Measurable.ite h_set ?_ measurable_const
  refine meas_optSome ?_
  refine Measurable.of_eval (fun i => ?_)
  exact (measurable_getD 0).comp (h_ev_i i)

theorem measurable_oMin {d : ℕ} : Measurable (oMin : (Fin d → ℝ) → ℝ) := by
  unfold oMin
  by_cases h : 0 < d
  · simp only [h, ↓reduceDIte]
    exact (Continuous.finset_inf'_apply (f := fun i (δ : Fin d → ℝ) => δ i) _ fun i _ => continuous_apply i).measurable
  · simp only [h, ↓reduceDIte]
    exact measurable_const

theorem meas_sep {X : Type*} [MeasurableSpace X] {d : ℕ} (ev : X → (Fin d → ℝ) → ℝ → Option ℝ)
    (hev : Measurable fun p : X × (Fin d → ℝ) × ℝ => ev p.1 p.2.1 p.2.2) (y0 : X → Fin d → ℝ)
    (τ ℓ1 L : X → ℝ) (J : X → ℕ) (hy0 : Measurable y0) (hτ : Measurable τ) (hℓ1 : Measurable ℓ1)
    (hL : Measurable L) (hJ : Measurable J) :
    Measurable fun x => sep (ev x) (y0 x) (τ x) (ℓ1 x) (L x) (J x) := by
  unfold sep
  simp only [Option.bind_eq_bind, Option.pure_def]
  refine meas_optBind (meas_sepCoords ev hev y0 τ ℓ1 L J hy0 hτ hℓ1 hL hJ d) ?_
  refine meas_optBind (hev.comp (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
    (((hτ.comp measurable_fst).mul (measurable_oMin.comp (measurable_snd.comp (measurable_snd.comp
      measurable_snd)))).div_const 400)))) ?_
  refine meas_optBind (meas_oValsAll (fun q : (X × SepSt d) × ℝ => ev q.1.1)
    (hev.comp ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)) _ _
    (by fun_prop) (by fun_prop)) ?_
  refine meas_optBind (meas_oValsAll (fun q : ((X × SepSt d) × ℝ) × (Fin d → ℝ) => ev q.1.1.1)
    (hev.comp ((measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
      measurable_snd)) _ _ (by fun_prop) (by fun_prop)) ?_
  exact meas_optSome (by fun_prop)

theorem meas_ccUpdate {d : ℕ} :
    Measurable fun p : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ) => ccUpdate p.1 p.2.1 p.2.2 := by
  unfold ccUpdate
  simp
  let s : (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ)) → ℝ := fun p => Real.sqrt (p.2.2 ⬝ᵥ (p.1 *ᵥ p.2.2))
  let v : (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ)) → (Fin d → ℝ) := fun p => p.1 *ᵥ p.2.2
  have h_mulVec : Measurable v := by
    refine Continuous.measurable ?_
    apply Continuous.matrix_mulVec
    · exact continuous_fst
    · exact continuous_snd.comp continuous_snd
  have h_dot : Measurable fun (p : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ)) =>
      p.2.2 ⬝ᵥ (p.1 *ᵥ p.2.2) := by
    refine Continuous.measurable ?_
    apply Continuous.dotProduct
    · exact continuous_snd.comp continuous_snd
    · apply Continuous.matrix_mulVec
      · exact continuous_fst
      · exact continuous_snd.comp continuous_snd
  have h_sqrt : Measurable s := by
    apply Measurable.sqrt
    exact h_dot
  have h_inv : Measurable fun (p : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ)) => (s p)⁻¹ := by
    apply Measurable.inv
    exact h_sqrt
  have h_b : Measurable fun (p : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ)) => (s p)⁻¹ • v p := by
    apply Measurable.smul h_inv h_mulVec
  have h_vecMulVec : Measurable fun (p : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ)) =>
      Matrix.vecMulVec (v p) (v p) := by
    refine Continuous.measurable ?_
    apply Continuous.matrix_vecMulVec
    · apply Continuous.matrix_mulVec
      · exact continuous_fst
      · exact continuous_snd.comp continuous_snd
    · apply Continuous.matrix_mulVec
      · exact continuous_fst
      · exact continuous_snd.comp continuous_snd
  have h_inner : Measurable fun (p : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ)) =>
      (s p)⁻¹ • Matrix.vecMulVec (v p) (v p) := by
    apply Measurable.smul h_inv h_vecMulVec
  have h_inner2 : Measurable fun (p : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ)) =>
      (s p)⁻¹ • ((s p)⁻¹ • Matrix.vecMulVec (v p) (v p)) := by
    apply Measurable.smul h_inv h_inner
  refine Measurable.prodMk ?_ ?_
  · apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply]
    let A_ij : (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ)) → ℝ := fun p => p.1 i j
    let v_i : (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ)) → ℝ := fun p => (p.1 *ᵥ p.2.2) i
    let v_j : (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ)) → ℝ := fun p => (p.1 *ᵥ p.2.2) j
    let sqrt_dot : (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ)) → ℝ := fun p => Real.sqrt (p.2.2 ⬝ᵥ (p.1 *ᵥ p.2.2))
    let inv_sqrt_dot : (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ)) → ℝ := fun p => (Real.sqrt (p.2.2 ⬝ᵥ (p.1 *ᵥ p.2.2)))⁻¹
    have h_A_ij : Measurable A_ij := by
      have h_p1 : Measurable fun (p : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ)) => p.1 := measurable_fst
      have h_eval : Measurable fun (M : Matrix (Fin d) (Fin d) ℝ) => M i j := by
        have h1 : Measurable fun (M : Matrix (Fin d) (Fin d) ℝ) => M i := measurable_pi_apply i
        have h2 : Measurable fun (w : (Fin d) → ℝ) => w j := measurable_pi_apply j
        exact h2.comp h1
      exact h_eval.comp h_p1
    have h_v_i : Measurable v_i := by
      have h_eval : Measurable fun (w : (Fin d) → ℝ) => w i := measurable_pi_apply i
      exact h_eval.comp h_mulVec
    have h_v_j : Measurable v_j := by
      have h_eval : Measurable fun (w : (Fin d) → ℝ) => w j := measurable_pi_apply j
      exact h_eval.comp h_mulVec
    have h_sqrt_dot : Measurable sqrt_dot := h_sqrt
    have h_inv_sqrt_dot : Measurable inv_sqrt_dot := h_inv
    have h_v_prod : Measurable fun p => v_i p * v_j p := by
      apply Measurable.mul h_v_i h_v_j
    have h_inner_prod : Measurable fun p => inv_sqrt_dot p * (v_i p * v_j p) := by
      apply Measurable.mul h_inv_sqrt_dot h_v_prod
    have h_inner_prod2 : Measurable fun p => inv_sqrt_dot p * (inv_sqrt_dot p * (v_i p * v_j p)) := by
      apply Measurable.mul h_inv_sqrt_dot h_inner_prod
    have h_const2_smul : Measurable fun p => (2 / ((d : ℝ) + 1)) * (inv_sqrt_dot p * (inv_sqrt_dot p * (v_i p * v_j p))) := by
      have h_const : Measurable fun (_ : (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ))) => (2 / ((d : ℝ) + 1)) := measurable_const
      apply Measurable.mul h_const h_inner_prod2
    have h_sub : Measurable fun p => A_ij p - (2 / ((d : ℝ) + 1)) * (inv_sqrt_dot p * (inv_sqrt_dot p * (v_i p * v_j p))) := by
      apply Measurable.sub h_A_ij h_const2_smul
    have h_const1_smul : Measurable fun p => ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) * (A_ij p - (2 / ((d : ℝ) + 1)) * (inv_sqrt_dot p * (inv_sqrt_dot p * (v_i p * v_j p)))) := by
      have h_const : Measurable fun (_ : (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ))) => ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) := measurable_const
      apply Measurable.mul h_const h_sub
    simpa [A_ij, v_i, v_j, sqrt_dot, inv_sqrt_dot]
  · apply Measurable.of_eval
    intro i
    simp [Pi.sub_apply, Pi.smul_apply]
    let a_i : (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ)) → ℝ := fun p => p.2.1 i
    let v_i : (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ)) → ℝ := fun p => (p.1 *ᵥ p.2.2) i
    let sqrt_dot : (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ)) → ℝ := fun p => Real.sqrt (p.2.2 ⬝ᵥ (p.1 *ᵥ p.2.2))
    let inv_sqrt_dot : (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ)) → ℝ := fun p => (Real.sqrt (p.2.2 ⬝ᵥ (p.1 *ᵥ p.2.2)))⁻¹
    have h_a_i : Measurable a_i := by
      have h_p21 : Measurable fun (p : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ)) => p.2.1 :=
        measurable_fst.comp measurable_snd
      have h_eval : Measurable fun (w : (Fin d) → ℝ) => w i := measurable_pi_apply i
      exact h_eval.comp h_p21
    have h_v_i : Measurable v_i := by
      have h_eval : Measurable fun (w : (Fin d) → ℝ) => w i := measurable_pi_apply i
      exact h_eval.comp h_mulVec
    have h_sqrt_dot : Measurable sqrt_dot := h_sqrt
    have h_inv_sqrt_dot : Measurable inv_sqrt_dot := h_inv
    have h_prod : Measurable fun p => inv_sqrt_dot p * v_i p := by
      apply Measurable.mul h_inv_sqrt_dot h_v_i
    have h_const_smul : Measurable fun p => ((d : ℝ) + 1)⁻¹ * (inv_sqrt_dot p * v_i p) := by
      have h_const : Measurable fun (_ : (Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ))) => ((d : ℝ) + 1)⁻¹ := measurable_const
      apply Measurable.mul h_const h_prod
    have h_sub : Measurable fun p => a_i p - ((d : ℝ) + 1)⁻¹ * (inv_sqrt_dot p * v_i p) := by
      apply Measurable.sub h_a_i h_const_smul
    simpa [a_i, v_i, sqrt_dot, inv_sqrt_dot]

theorem meas_ellConsts {d : ℕ} :
    Measurable fun p : ℝ × ℝ × Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × ℝ =>
      ellConsts p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 := by
  unfold ellConsts
  dsimp only
  refine measurable_ellConsts_iff.2 ?_
  dsimp only [ellConstsCode]
  -- Goal: Measurable fun x => (τ, ℓ1, N, J, B)
  set r := fun (x : ℝ × ℝ × Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × ℝ) => x.1 with hr
  set R := fun (x : ℝ × ℝ × Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × ℝ) => x.2.1 with hR
  set P := fun (x : ℝ × ℝ × Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × ℝ) => x.2.2.1 with hP
  set w := fun (x : ℝ × ℝ × Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × ℝ) => x.2.2.2.1 with hw
  set e := fun (x : ℝ × ℝ × Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × ℝ) => x.2.2.2.2 with he
  have hr_meas : Measurable r := by rw [hr]; exact measurable_fst
  have hR_meas : Measurable R := by rw [hR]; exact measurable_fst.comp measurable_snd
  have hP_meas : Measurable P := by
    rw [hP]
    exact measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hw_meas : Measurable w := by
    rw [hw]
    exact measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have he_meas : Measurable e := by
    rw [he]
    exact measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  -- LF = P.trace * (R + oNorm w)
  set LF := fun x => (P x).trace * (R x + oNorm (w x)) with hLF
  have hLF_meas : Measurable LF := by
    rw [hLF]
    refine ((Continuous.matrix_trace ?_).measurable).mul ?_
    · -- P is continuous: P = fst ∘ snd ∘ snd
      exact continuous_fst.comp (continuous_snd.comp continuous_snd)
    · -- R + oNorm w
      refine hR_meas.add ?_
      exact measurable_oNorm.comp hw_meas
  -- θ = min 1 (e / (3 * LF * R))
  set θ := fun x => min 1 (e x / (3 * LF x * R x)) with hθ
  have hθ_meas : Measurable θ := by
    rw [hθ]
    refine Measurable.min measurable_const ?_
    refine (he_meas.div ((measurable_const.mul hLF_meas).mul hR_meas))
  -- εQ = θ * r / 2
  set εQ := fun x => θ x * r x / 2 with hεQ
  have hεQ_meas : Measurable εQ := by
    rw [hεQ]
    refine (hθ_meas.mul hr_meas).div measurable_const
  -- τ = εQ / (36 * R^2 * sqrt(d))
  set τ_expr := fun x => εQ x / (36 * R x ^ 2 * Real.sqrt (d : ℝ)) with hτ_expr
  have hτ_meas : Measurable τ_expr := by
    rw [hτ_expr]
    refine hεQ_meas.div ?_
    -- 36 * R^2 * sqrt(d) is a product of measurable/continuous functions
    -- Since d is fixed, sqrt(d) is constant, hence measurable
    refine ((measurable_const.mul (hR_meas.pow_const 2)).mul ?_)
    exact measurable_const
  -- ℓ1 = r * εQ / (24 * R)
  set ℓ1_expr := fun x => r x * εQ x / (24 * R x) with hℓ1_expr
  have hℓ1_meas : Measurable ℓ1_expr := by
    rw [hℓ1_expr]
    refine (hr_meas.mul hεQ_meas).div ((measurable_const.mul hR_meas))
  -- N = ⌈2 * d * (d + 1) * log(2 * R / (θ * r))⌉₊ + 1
  set N_expr := fun x => ⌈2 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (2 * R x / (θ x * r x))⌉₊ + 1 with hN_expr
  have hN_meas : Measurable N_expr := by
    rw [hN_expr]
    refine (Measurable.nat_ceil ?_).add measurable_const
    -- 2 * d * (d + 1) * log(2 * R / (θ * r))
    -- This is a product of constants and measurable functions
    refine ((measurable_const.mul ?_).mul ?_)
    · -- d + 1 (constant)
      exact (measurable_const : Measurable fun _ => (d : ℝ)).add measurable_const
    · -- log(2 * R / (θ * r))
      refine Real.measurable_log.comp ?_
      refine ((measurable_const.mul hR_meas).div (hθ_meas.mul hr_meas))
  -- J = ⌈logb 2 (8 / (r * τ))⌉₊
  set J_expr := fun x => ⌈Real.logb 2 (8 / (r x * τ_expr x))⌉₊ with hJ_expr
  have hJ_meas : Measurable J_expr := by
    rw [hJ_expr]
    refine Measurable.nat_ceil ?_
    simp [Real.logb]
    refine (Real.measurable_log.comp ?_).div (Real.measurable_log.comp measurable_const)
    · -- 8 / (r x * τ_expr x)
      refine measurable_const.div (hr_meas.mul hτ_meas)
  -- ηmin = τ * ℓ1 / 1600 * 2 ^ (-(3 * d * (J + 1)))
  set ηmin_expr := fun x => τ_expr x * ℓ1_expr x / 1600 * (2 : ℝ) ^ (-(3 * (d : ℝ) * ((J_expr x : ℝ) + 1))) with hηmin_expr
  have hηmin_meas : Measurable ηmin_expr := by
    rw [hηmin_expr]
    refine ((hτ_meas.mul hℓ1_meas).div measurable_const).mul ?_
    -- (2 : ℝ) ^ exponent
    -- This is Real.rpow with constant base 2 (which is > 0, hence continuous)
    have h_base_ne_zero : (2 : ℝ) ≠ 0 := by norm_num
    refine (Real.continuous_const_rpow h_base_ne_zero).measurable.comp ?_
    -- exponent = -(3 * d * ((J_expr x : ℝ) + 1))
    have hJ_meas_real : Measurable fun x => (J_expr x : ℝ) :=
      Measurable.of_discrete.comp hJ_meas
    have h_inner : Measurable fun x => (3 : ℝ) * (d : ℝ) * ((J_expr x : ℝ) + 1) :=
      ((measurable_const (a := (3 : ℝ) * (d : ℝ))).mul (hJ_meas_real.add measurable_const))
    refine h_inner.neg
  -- B = ⌈logb 2 (3 * R / (r * ηmin))⌉₊
  set B_expr := fun x => ⌈Real.logb 2 (3 * R x / (r x * ηmin_expr x))⌉₊ with hB_expr
  have hB_meas : Measurable B_expr := by
    rw [hB_expr]
    refine Measurable.nat_ceil ?_
    simp [Real.logb]
    refine (Real.measurable_log.comp ?_).div (Real.measurable_log.comp measurable_const)
    · -- 3 * R / (r * ηmin)
      refine ((measurable_const.mul hR_meas).div (hr_meas.mul hηmin_meas))
  -- Combine all five components
  refine Measurable.prodMk hτ_meas (Measurable.prodMk hℓ1_meas (Measurable.prodMk hN_meas (Measurable.prodMk hJ_meas hB_meas)))

theorem meas_ellRecord {d : ℕ} :
    Measurable fun p : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × Option (Fin d → ℝ) × (Fin d → ℝ) =>
      ellRecord p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  have h_ellF_cont : Continuous fun (x : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ)) =>
      ellF x.1 x.2.1 x.2.2 := by
    unfold ellF
    refine Continuous.mul continuous_const ?_
    refine Continuous.dotProduct ?_ ?_
    · refine Continuous.sub ?_ ?_
      · exact continuous_snd.comp continuous_snd
      · exact continuous_fst.comp continuous_snd
    · refine Continuous.matrix_mulVec ?_ ?_
      · exact continuous_fst
      · refine Continuous.sub ?_ ?_
        · exact continuous_snd.comp continuous_snd
        · exact continuous_fst.comp continuous_snd
  have h_ellF_meas : Measurable fun (x : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ)) =>
      ellF x.1 x.2.1 x.2.2 :=
    h_ellF_cont.measurable
  have h_eq : (fun p : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × Option (Fin d → ℝ) × (Fin d → ℝ) =>
      ellRecord p.1 p.2.1 p.2.2.1 p.2.2.2) =
      fun p => (p.2.2.1).elim (some p.2.2.2)
        (fun b => if ellF p.1 p.2.1 p.2.2.2 < ellF p.1 p.2.1 b then some p.2.2.2 else some b) := by
    funext p
    rcases p with ⟨P, w, best, a⟩
    cases best <;> rfl
  rw [h_eq]
  refine meas_optElim (measurable_fst.comp (measurable_snd.comp measurable_snd)) ?_ ?_
  · refine measurable_some'.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  · let X := Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × Option (Fin d → ℝ) × (Fin d → ℝ)
    let f : X × (Fin d → ℝ) → ℝ := fun x => ellF x.1.1 x.1.2.1 x.1.2.2.2
    let g : X × (Fin d → ℝ) → ℝ := fun x => ellF x.1.1 x.1.2.1 x.2
    have hf_meas : Measurable f := by
      have : f = (fun (x : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ)) => ellF x.1 x.2.1 x.2.2) ∘
          (fun x => (x.1.1, x.1.2.1, x.1.2.2.2)) := by
        ext x; rfl
      rw [this]
      refine h_ellF_meas.comp ?_
      refine (measurable_fst.comp measurable_fst).prodMk ?_
      refine ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk ?_)
      exact measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
    have hg_meas : Measurable g := by
      have : g = (fun (x : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × (Fin d → ℝ)) => ellF x.1 x.2.1 x.2.2) ∘
          (fun x => (x.1.1, x.1.2.1, x.2)) := by
        ext x; rfl
      rw [this]
      refine h_ellF_meas.comp ?_
      refine (measurable_fst.comp measurable_fst).prodMk ?_
      refine ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk ?_)
      exact measurable_snd
    have h_cond : MeasurableSet {x | f x < g x} :=
      measurableSet_lt hf_meas hg_meas
    refine Measurable.ite h_cond ?_ ?_
    · refine measurable_some'.comp
        (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_fst)))
    · refine measurable_some'.comp measurable_snd

theorem meas_ccUpdate_comp {Y : Type*} [MeasurableSpace Y] {d : ℕ} {A : Y → Matrix (Fin d) (Fin d) ℝ}
    {a c : Y → Fin d → ℝ} (hA : Measurable A) (ha : Measurable a) (hc : Measurable c) :
    Measurable fun y => ccUpdate (A y) (a y) (c y) :=
  meas_ccUpdate.comp (hA.prodMk (ha.prodMk hc))

theorem meas_ellStep {X : Type*} [MeasurableSpace X] {d : ℕ} (Q : X → Set (Fin d → ℝ)) (hQ : GraphMeas Q)
    (a0 : X → Fin d → ℝ) (r R : X → ℝ) (P : X → Matrix (Fin d) (Fin d) ℝ) (w : X → Fin d → ℝ)
    (k : X → EllConsts) (ha0 : Measurable a0) (hr : Measurable r) (hR : Measurable R) (hP : Measurable P)
    (hw : Measurable w) (hk : Measurable k) :
    Measurable fun p : X × EllSt d => ellStep (Q p.1) (a0 p.1) (r p.1) (R p.1) (P p.1) (w p.1) (k p.1) p.2 := by
  classical
  have hA : Measurable fun p : X × EllSt d => p.2.A := measurable_ellSt_A.comp measurable_snd
  have ha : Measurable fun p : X × EllSt d => p.2.a := measurable_ellSt_a.comp measurable_snd
  have hb : Measurable fun p : X × EllSt d => p.2.best := measurable_ellSt_best.comp measurable_snd
  have hmv : Measurable fun p : X × EllSt d => P p.1 *ᵥ (p.2.a - w p.1) := by
    have hc : Continuous fun q : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) => q.1 *ᵥ q.2 :=
      Continuous.matrix_mulVec continuous_fst continuous_snd
    exact hc.measurable.comp ((hP.comp measurable_fst).prodMk (ha.sub (hw.comp measurable_fst)))
  have hrec : Measurable fun p : X × EllSt d => ellRecord (P p.1) (w p.1) p.2.best p.2.a :=
    meas_ellRecord.comp ((hP.comp measurable_fst).prodMk ((hw.comp measurable_fst).prodMk (hb.prodMk ha)))
  -- the call of SEP on the gauge
  have hsep : Measurable fun p : X × EllSt d =>
      sep (oGaugeValCap (Q p.1) (a0 p.1) (r p.1) (R p.1) (k p.1).B) p.2.a (k p.1).τ (k p.1).ℓ1 (1 / r p.1) (k p.1).J := by
    refine meas_sep (fun p : X × EllSt d => oGaugeValCap (Q p.1) (a0 p.1) (r p.1) (R p.1) (k p.1).B) ?_ _ _ _ _ _
      ha ((measurable_ellConsts_τ.comp hk).comp measurable_fst) ((measurable_ellConsts_ℓ1.comp hk).comp measurable_fst)
      (measurable_const.div (hr.comp measurable_fst)) ((measurable_ellConsts_J.comp hk).comp measurable_fst)
    have hQ' : GraphMeas fun q : (X × EllSt d) × (Fin d → ℝ) × ℝ => Q q.1.1 :=
      hQ.preimage ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)
    exact meas_oGaugeValCap (fun q : (X × EllSt d) × (Fin d → ℝ) × ℝ => Q q.1.1) hQ' _ _ _ _ _ _
      (ha0.comp (measurable_fst.comp measurable_fst)) (hr.comp (measurable_fst.comp measurable_fst))
      (hR.comp (measurable_fst.comp measurable_fst))
      ((measurable_ellConsts_B.comp hk).comp (measurable_fst.comp measurable_fst))
      (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)
  have hmatch : (fun p : X × EllSt d => ellStep (Q p.1) (a0 p.1) (r p.1) (R p.1) (P p.1) (w p.1) (k p.1) p.2) =
      fun p => if R p.1 < oNorm p.2.a then
          some (.inl ⟨(ccUpdate p.2.A p.2.a p.2.a).1, (ccUpdate p.2.A p.2.a p.2.a).2, p.2.best⟩)
        else if p.2.a ∉ Q p.1 then
          (sep (oGaugeValCap (Q p.1) (a0 p.1) (r p.1) (R p.1) (k p.1).B) p.2.a (k p.1).τ (k p.1).ℓ1 (1 / r p.1)
            (k p.1).J).elim none fun q =>
              if q.2 = 0 then none
              else some (.inl ⟨(ccUpdate p.2.A p.2.a q.2).1, (ccUpdate p.2.A p.2.a q.2).2, p.2.best⟩)
        else if P p.1 *ᵥ (p.2.a - w p.1) = 0 then some (.inr p.2.a)
        else some (.inl ⟨(ccUpdate p.2.A p.2.a (P p.1 *ᵥ (p.2.a - w p.1))).1,
          (ccUpdate p.2.A p.2.a (P p.1 *ᵥ (p.2.a - w p.1))).2, ellRecord (P p.1) (w p.1) p.2.best p.2.a⟩) := by
    funext p
    unfold ellStep
    split_ifs <;> try rfl
    split <;> rename_i h <;> rw [h] <;> rfl
  rw [hmatch]
  have hmk : ∀ {c : X × EllSt d → Fin d → ℝ} {bst : X × EllSt d → Option (Fin d → ℝ)}, Measurable c →
      Measurable bst → Measurable fun p : X × EllSt d =>
        (some (.inl ⟨(ccUpdate p.2.A p.2.a (c p)).1, (ccUpdate p.2.A p.2.a (c p)).2, bst p⟩) :
          Option (EllSt d ⊕ (Fin d → ℝ))) :=
    fun hc hbst => measurable_some'.comp (measurable_inl.comp
      (meas_ellSt_mk (meas_ccUpdate_comp hA ha hc).fst (meas_ccUpdate_comp hA ha hc).snd hbst))
  refine Measurable.ite (measurableSet_lt (hR.comp measurable_fst) (measurable_oNorm.comp ha)) (hmk ha hb) ?_
  refine Measurable.ite ?_ ?_ ?_
  · exact (hQ.preimage (measurable_fst.prodMk ha)).compl
  · refine meas_optElim hsep measurable_const ?_
    refine Measurable.ite ?_ measurable_const ?_
    · exact (measurable_snd.comp measurable_snd) (measurableSet_singleton 0)
    · exact measurable_some'.comp (measurable_inl.comp (meas_ellSt_mk
        (meas_ccUpdate_comp (hA.comp measurable_fst) (ha.comp measurable_fst) (measurable_snd.comp measurable_snd)).fst
        (meas_ccUpdate_comp (hA.comp measurable_fst) (ha.comp measurable_fst) (measurable_snd.comp measurable_snd)).snd
        (hb.comp measurable_fst)))
  · refine Measurable.ite (hmv (measurableSet_singleton 0)) (measurable_some'.comp (measurable_inr.comp ha)) ?_
    exact hmk hmv hrec

theorem meas_ellLoop {X : Type*} [MeasurableSpace X] {d : ℕ} (Q : X → Set (Fin d → ℝ)) (hQ : GraphMeas Q)
    (a0 : X → Fin d → ℝ) (r R : X → ℝ) (P : X → Matrix (Fin d) (Fin d) ℝ) (w : X → Fin d → ℝ)
    (k : X → EllConsts) (ha0 : Measurable a0) (hr : Measurable r) (hR : Measurable R) (hP : Measurable P)
    (hw : Measurable w) (hk : Measurable k) (j : ℕ) :
    Measurable fun x => ellLoop (Q x) (a0 x) (r x) (R x) (P x) (w x) (k x) j := by
  induction j with
  | zero =>
      have h_cont : Continuous fun (t : ℝ) => t ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) := by
        continuity
      have hA : Measurable fun x : X => (R x ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ) :=
        h_cont.measurable.comp hR
      have ha : Measurable fun _ : X => (0 : Fin d → ℝ) := measurable_const
      have hb : Measurable fun _ : X => (none : Option (Fin d → ℝ)) := measurable_const
      have h_record : Measurable fun x : X => (⟨(R x ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ), 0, none⟩ : EllSt d) :=
        meas_ellSt_mk hA ha hb
      have h0 : (fun x => ellLoop (Q x) (a0 x) (r x) (R x) (P x) (w x) (k x) 0) =
                fun x => some (.inl ⟨(R x ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ), 0, none⟩) := by
        ext x; rfl
      rw [h0]
      exact measurable_some'.comp (measurable_inl.comp h_record)
  | succ j ih =>
      have hstep : (fun x => ellLoop (Q x) (a0 x) (r x) (R x) (P x) (w x) (k x) (j + 1)) =
          (fun x => ((ellLoop (Q x) (a0 x) (r x) (R x) (P x) (w x) (k x) j)).elim
            none (fun s => Sum.elim (fun st => ellStep (Q x) (a0 x) (r x) (R x) (P x) (w x) (k x) st)
                                    (fun μ => some (Sum.inr μ)) s)) := by
        funext x
        cases hx : ellLoop (Q x) (a0 x) (r x) (R x) (P x) (w x) (k x) j
        · simp [ellLoop, Option.elim, hx]
        · rename_i val
          cases val
          · simp [ellLoop, Option.elim, hx]
          · simp [ellLoop, Option.elim, hx]
      rw [hstep]
      refine meas_optElim ih measurable_const ?_
      have h_left : Measurable fun (p : X × EllSt d) =>
          ellStep (Q p.1) (a0 p.1) (r p.1) (R p.1) (P p.1) (w p.1) (k p.1) p.2 :=
        meas_ellStep Q hQ a0 r R P w k ha0 hr hR hP hw hk
      have h_right : Measurable fun (p : X × (Fin d → ℝ)) => some (Sum.inr p.2) :=
        (measurable_some' (α := EllSt d ⊕ (Fin d → ℝ))).comp (measurable_inr.comp measurable_snd)
      let e := MeasurableEquiv.prodSumDistrib X (EllSt d) (Fin d → ℝ)
      have h_sum : Measurable (Sum.elim
        (fun (p : X × EllSt d) => ellStep (Q p.1) (a0 p.1) (r p.1) (R p.1) (P p.1) (w p.1) (k p.1) p.2)
        (fun (p : X × (Fin d → ℝ)) => some (Sum.inr p.2))) :=
        Measurable.sumElim h_left h_right
      have h_eq : (fun (p : X × (EllSt d ⊕ (Fin d → ℝ))) =>
          Sum.elim (fun st => ellStep (Q p.1) (a0 p.1) (r p.1) (R p.1) (P p.1) (w p.1) (k p.1) st)
                   (fun μ => some (Sum.inr μ)) p.2) =
          (Sum.elim
            (fun (p : X × EllSt d) => ellStep (Q p.1) (a0 p.1) (r p.1) (R p.1) (P p.1) (w p.1) (k p.1) p.2)
            (fun (p : X × (Fin d → ℝ)) => some (Sum.inr p.2))) ∘ e := by
        ext p
        cases p with | mk x s =>
        cases s with
        | inl st => rfl
        | inr μ => rfl
      rw [h_eq]
      exact h_sum.comp e.measurable

theorem meas_ellCap {X : Type*} [MeasurableSpace X] {d : ℕ} (Q : X → Set (Fin d → ℝ)) (hQ : GraphMeas Q)
    (a0 : X → Fin d → ℝ) (r R : X → ℝ) (P : X → Matrix (Fin d) (Fin d) ℝ) (w : X → Fin d → ℝ) (e : X → ℝ)
    (ha0 : Measurable a0) (hr : Measurable r) (hR : Measurable R) (hP : Measurable P) (hw : Measurable w)
    (he : Measurable e) :
    Measurable fun x => ellCap (Q x) (a0 x) (r x) (R x) (P x) (w x) (e x) := by
  let k : X → EllConsts := fun x => ellConsts (r x) (R x) (P x) (w x) (e x)
  have hk : Measurable k :=
    meas_ellConsts.comp (hr.prodMk (hR.prodMk (hP.prodMk (hw.prodMk he))))
  have hkN : Measurable fun x => (k x).N := measurable_ellConsts_N.comp hk
  have hF (j : ℕ) : Measurable fun x =>
      match ellLoop (Q x) (a0 x) (r x) (R x) (P x) (w x) (k x) j with
      | some (.inr μ) => some μ
      | some (.inl st) => st.best
      | none => none := by
    have ho : Measurable fun x => ellLoop (Q x) (a0 x) (r x) (R x) (P x) (w x) (k x) j :=
      meas_ellLoop Q hQ a0 r R P w k ha0 hr hR hP hw hk j
    have ha : Measurable fun (_ : X) => (none : Option (Fin d → ℝ)) := measurable_const
    have hb : Measurable fun (p : X × (EllSt d ⊕ (Fin d → ℝ))) =>
      (Sum.elim EllSt.best some) p.2 := by
      refine (Measurable.sumElim measurable_ellSt_best measurable_some').comp measurable_snd
    have heq : (fun x => (ellLoop (Q x) (a0 x) (r x) (R x) (P x) (w x) (k x) j).elim none
        (Sum.elim (fun (st : EllSt d) => st.best) some)) = (fun x => match ellLoop (Q x) (a0 x) (r x) (R x) (P x) (w x) (k x) j with
      | some (.inr μ) => some μ
      | some (.inl st) => st.best
      | none => none) := by
      ext x
      cases h : ellLoop (Q x) (a0 x) (r x) (R x) (P x) (w x) (k x) j
      · simp [Option.elim]
      · case some val =>
        cases h2 : val
        · case inl st => simp [Option.elim, Sum.elim]
        · case inr μ => simp [Option.elim, Sum.elim]
    have h := meas_optElim ho ha (b := fun (_x : X) (s : EllSt d ⊕ (Fin d → ℝ)) =>
      Sum.elim (fun (st : EllSt d) => st.best) some s) hb
    rw [heq] at h
    exact h
  have h_main : Measurable fun x =>
      match ellLoop (Q x) (a0 x) (r x) (R x) (P x) (w x) (k x) ((k x).N) with
      | some (.inr μ) => some μ
      | some (.inl st) => st.best
      | none => none :=
    measurable_natDep hF hkN
  have h_cond : MeasurableSet {x | R x < r x} :=
    measurableSet_lt hR hr
  have h_if : Measurable fun x => if R x < r x then (none : Option (Fin d → ℝ)) else
      match ellLoop (Q x) (a0 x) (r x) (R x) (P x) (w x) (k x) ((k x).N) with
      | some (.inr μ) => some μ
      | some (.inl st) => st.best
      | none => none :=
    Measurable.ite h_cond measurable_const h_main
  dsimp [ellCap, k]
  exact h_if

theorem meas_ellOne {X : Type*} [MeasurableSpace X] (Q : X → Set ℝ) (hQ : MeasurableSet {p : X × ℝ | p.2 ∈ Q p.1})
    (a0 r R p w e : X → ℝ) (ha0 : Measurable a0) (hr : Measurable r) (hR : Measurable R) (hp : Measurable p)
    (hw : Measurable w) (he : Measurable e) :
    Measurable fun x => ellOne (Q x) (a0 x) (r x) (R x) (p x) (w x) (e x) := by
  classical
  have h_ellOne_eq : (fun x => ellOne (Q x) (a0 x) (r x) (R x) (p x) (w x) (e x)) =
      fun x =>
        if R x < r x ∨ R x < |a0 x| then none
        else if a0 x ∉ Q x then none
        else
          let w' := max (-R x) (min (R x) (w x))
          if w' ∈ Q x then some w'
          else
            let ξ := e x / (p x * (R x + |w x|))
            some (oBisectLo (· ∈ Q x) (a0 x) w' ⌈Real.logb 2 (|w' - a0 x| / ξ)⌉₊).1 := by
    ext x; simp [ellOne]
  rw [h_ellOne_eq]
  -- First conditional: R x < r x ∨ R x < |a0 x|
  have h_cond1 : MeasurableSet {x | R x < r x ∨ R x < |a0 x|} := by
    have h1 : MeasurableSet {x | R x < r x} := measurableSet_lt hR hr
    have h2 : MeasurableSet {x | R x < |a0 x|} := measurableSet_lt hR (Measurable.abs ha0)
    exact h1.union h2
  refine Measurable.ite h_cond1 measurable_const ?_
  -- Second conditional: a0 x ∉ Q x
  have hQmem_a0 : MeasurableSet {x | a0 x ∈ Q x} :=
    hQ.preimage (f := fun x => (x, a0 x)) (measurable_id.prodMk ha0)
  have h_cond2 : MeasurableSet {x | a0 x ∉ Q x} := hQmem_a0.compl
  refine Measurable.ite h_cond2 measurable_const ?_
  -- Define w' for convenience
  let w' : X → ℝ := fun x => max (-R x) (min (R x) (w x))
  have hw' : Measurable w' := by
    unfold w'
    exact (hR.neg).max (hR.min hw)
  -- Third conditional: w' x ∈ Q x
  have hQmem_w' : MeasurableSet {x | w' x ∈ Q x} :=
    hQ.preimage (f := fun x => (x, w' x)) (measurable_id.prodMk hw')
  refine Measurable.ite hQmem_w' ?_ ?_
  · -- w' x ∈ Q x branch: some w'
    exact measurable_some'.comp hw'
  · -- else branch: let ξ := ...; some (oBisectLo ...).1
    let ξ : X → ℝ := fun x => e x / (p x * (R x + |w x|))
    have hξ : Measurable ξ := by
      unfold ξ
      exact he.div (hp.mul (hR.add (Measurable.abs hw)))
    let N : X → ℕ := fun x => ⌈Real.logb 2 (|w' x - a0 x| / ξ x)⌉₊
    have hN : Measurable N := by
      unfold N
      have h_logb2 : Measurable (Real.logb 2) := by
        have : Real.logb 2 = fun x => Real.log x / Real.log 2 := by
          ext x; rfl
        rw [this]
        exact Real.measurable_log.div measurable_const
      refine Measurable.nat_ceil ?_
      refine h_logb2.comp ?_
      exact ((Measurable.abs (hw'.sub ha0)).div hξ)
    -- Now use measurable_natDep
    let F : ℕ → X → ℝ := fun j x => (oBisectLo (· ∈ Q x) (a0 x) (w' x) j).1
    have hF : ∀ j, Measurable (F j) := by
      intro j
      have h := meas_oBisectLo (fun x y => y ∈ Q x) hQ (fun x => a0 x) w' ha0 hw' j
      simpa [F] using h.fst
    have h_main : Measurable fun x => F (N x) x := measurable_natDep hF hN
    have h_goal_eq : (fun x => some (F (N x) x)) = (fun x =>
      let ξ := e x / (p x * (R x + |w x|))
      some (oBisectLo (· ∈ Q x) (a0 x) (max (-R x) (min (R x) (w x))) ⌈Real.logb 2 (|(max (-R x) (min (R x) (w x))) - a0 x| / ξ)⌉₊).1) := by
      ext x; simp [F, N, ξ, w']
    rw [h_goal_eq]
    exact measurable_some'.comp h_main

theorem meas_apCall {X : Type*} [MeasurableSpace X] {d : ℕ} (Q : X → Set (Fin d → ℝ)) (hQ : GraphMeas Q)
    (a0 : X → Fin d → ℝ) (r R : X → ℝ) (P : X → Matrix (Fin d) (Fin d) ℝ) (w : X → Fin d → ℝ) (e : X → ℝ)
    (ha0 : Measurable a0) (hr : Measurable r) (hR : Measurable R) (hP : Measurable P) (hw : Measurable w)
    (he : Measurable e) :
    Measurable fun x => apCall (Q x) (a0 x) (r x) (R x) (P x) (w x) (e x) := by
  by_cases h : d = 1
  · subst h
    let Q1 : X → Set ℝ := fun x => {t : ℝ | (fun _ : Fin 1 => t) ∈ Q x}
    have hQ1 : MeasurableSet {p : X × ℝ | p.2 ∈ Q1 p.1} := by
      have hφ : Measurable (fun (p : X × ℝ) => (p.1, (fun _ : Fin 1 => p.2))) := by
        refine (measurable_fst.prodMk ?_)
        rw [measurable_pi_iff]
        intro i
        exact measurable_snd
      exact hQ.preimage hφ
    have ha0_coord : Measurable (fun x : X => a0 x 0) :=
      (measurable_pi_apply 0).comp ha0
    have hP_coord : Measurable (fun x : X => P x 0 0) := by
      have : Measurable (fun (M : Matrix (Fin 1) (Fin 1) ℝ) => M 0 0) :=
        (measurable_pi_apply (0 : Fin 1)).comp (measurable_pi_apply (0 : Fin 1))
      exact this.comp hP
    have hw_coord : Measurable (fun x : X => w x 0) :=
      (measurable_pi_apply 0).comp hw
    have h_ellOne : Measurable fun x => ellOne (Q1 x) (a0 x 0) (r x) (R x) (P x 0 0) (w x 0) (e x) :=
      meas_ellOne Q1 hQ1 (fun x => a0 x 0) (fun x => r x) (fun x => R x) (fun x => P x 0 0) (fun x => w x 0) (fun x => e x)
        ha0_coord hr hR hP_coord hw_coord he
    have hg : Measurable (fun (p : X × ℝ) => fun (_ : Fin 1) => p.2) := by
      rw [measurable_pi_iff]
      intro i
      exact measurable_snd
    have hap : (fun x => apCall (Q x) (a0 x) (r x) (R x) (P x) (w x) (e x)) =
               (fun x => ((ellOne (Q1 x) (a0 x 0) (r x) (R x) (P x 0 0) (w x 0) (e x)).map fun t _ => t)) := by
      ext x
      simp [apCall, Q1]
    rw [hap]
    exact meas_optMap h_ellOne hg
  · have hap : (fun x => apCall (Q x) (a0 x) (r x) (R x) (P x) (w x) (e x)) =
               (fun x => ellCap (Q x) (a0 x) (r x) (R x) (P x) (w x) (e x)) := by
      ext x
      simp [apCall, h]
    rw [hap]
    exact meas_ellCap Q hQ a0 r R P w e ha0 hr hR hP hw he

end AdversarialBco.Poly.ApMeas
