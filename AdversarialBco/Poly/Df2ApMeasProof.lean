/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.Df2Layer2
public import AdversarialBco.Poly.Df2ApMeasTools
public import AdversarialBco.Poly.PgProcBase

@[expose] public section

/-!
# (L1) for `apCall`: the round map of DF2-O is measurable jointly in the position

Proof of `Df2ApCallMeas` of `Df2Layer2.lean` (theorem `df2ApCallMeas`): `df2NextAP apCall`, the rest of a round
after the observation, is a measurable function of the position, the state, the draw and the observation.

The state and the mode carry the comap σ-algebras of `Df2St.code` and `Df2Mode.code` (`Df2Layer2.lean`). The
arithmetic of the round is continuous or measurable (`Real.sqrt`, inverses); the regions `R⁻` and `R_{t+1}` have
measurable graphs, since `K` is closed and `(P, y) ↦ μ_P + A_P y` is continuous; the two calls of `apCall` are
measurable in their arguments by `meas_apCall` (`Df2ApMeasTools.lean`).
-/

open MeasureTheory Matrix
open scoped Matrix

namespace AdversarialBco.Poly.ApMeas

open AdversarialBco AdversarialBco.Poly AdversarialBco.RealRAM

section States

variable {d : ℕ} {X : Type*} [MeasurableSpace X]

theorem measurable_st_iff {f : X → Df2St d} : Measurable f ↔ Measurable fun x => (f x).code :=
  measurable_comap_iff Df2St.code

theorem measurable_st_code : Measurable (Df2St.code : Df2St d → _) := comap_measurable _

theorem measurable_mode_iff {f : X → Df2Mode d} : Measurable f ↔ Measurable fun x => (f x).code :=
  measurable_comap_iff Df2Mode.code

theorem measurable_mode_code : Measurable (Df2Mode.code : Df2Mode d → _) := comap_measurable _

theorem measurable_st_first : Measurable (Df2St.first : Df2St d → Bool) :=
  measurable_fst.comp measurable_st_code
theorem measurable_st_mu : Measurable (Df2St.mu : Df2St d → Fin d → ℝ) :=
  measurable_fst.comp (measurable_snd.comp measurable_st_code)
theorem measurable_st_P : Measurable (Df2St.P : Df2St d → Matrix (Fin d) (Fin d) ℝ) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_st_code))
theorem measurable_st_S : Measurable (Df2St.S : Df2St d → Matrix (Fin d) (Fin d) ℝ) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_st_code)))
theorem measurable_st_A : Measurable (Df2St.A : Df2St d → Matrix (Fin d) (Fin d) ℝ) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp measurable_st_code))))
theorem measurable_st_b : Measurable (Df2St.b : Df2St d → Fin d → ℝ) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp measurable_st_code)))))
theorem measurable_st_k : Measurable (Df2St.k : Df2St d → ℝ) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_st_code))))))
theorem measurable_st_G : Measurable (Df2St.G : Df2St d → Fin d → ℝ) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_st_code)))))))
theorem measurable_st_l : Measurable (Df2St.l : Df2St d → ℝ) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp measurable_st_code))))))))
theorem measurable_st_ctr : Measurable (Df2St.ctr : Df2St d → Fin d → ℝ) :=
  measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp measurable_st_code)))))))))
theorem measurable_st_r : Measurable (Df2St.r : Df2St d → ℝ) :=
  measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp (measurable_snd.comp measurable_st_code)))))))))

theorem meas_st_mk {first : X → Bool} {mu : X → Fin d → ℝ} {P S A : X → Matrix (Fin d) (Fin d) ℝ}
    {b : X → Fin d → ℝ} {k : X → ℝ} {G : X → Fin d → ℝ} {l : X → ℝ} {ctr : X → Fin d → ℝ} {r : X → ℝ}
    (h1 : Measurable first) (h2 : Measurable mu) (h3 : Measurable P) (h4 : Measurable S) (h5 : Measurable A)
    (h6 : Measurable b) (h7 : Measurable k) (h8 : Measurable G) (h9 : Measurable l) (h10 : Measurable ctr)
    (h11 : Measurable r) :
    Measurable fun x => (⟨first x, mu x, P x, S x, A x, b x, k x, G x, l x, ctr x, r x⟩ : Df2St d) := by
  rw [measurable_st_iff]
  exact h1.prodMk (h2.prodMk (h3.prodMk (h4.prodMk (h5.prodMk (h6.prodMk (h7.prodMk (h8.prodMk (h9.prodMk
    (h10.prodMk h11)))))))))

theorem meas_run {f : X → Df2St d} (hf : Measurable f) : Measurable fun x => Df2Mode.run (f x) := by
  rw [measurable_mode_iff]
  exact measurable_const.prodMk hf

end States

/-! ## The regions of the two calls -/

theorem keps_graph {d : ℕ} (K : Set (E d)) (hK : IsClosed K) (R ε : ℝ) :
    MeasurableSet {p : PgSp d × (Fin d → ℝ) | p.2 ∈ df2KepsOf (df2Kp K p.1 R) ε} := by
  have hc : Continuous fun p : PgSp d × (Fin d → ℝ) =>
      (p.1, (WithLp.toLp 2 ((1 - ε)⁻¹ • p.2) : EuclideanSpace ℝ (Fin d))) :=
    continuous_fst.prodMk ((PiLp.continuous_toLp 2 _).comp (by fun_prop))
  have h1 : MeasurableSet {p : PgSp d × (Fin d → ℝ) |
      pgMu p.1 + pgOp p.1 (WithLp.toLp 2 ((1 - ε)⁻¹ • p.2)) ∈ K} :=
    (hK.preimage ((pg_continuous d).2.2.comp hc)).measurableSet
  have h2 : MeasurableSet {p : PgSp d × (Fin d → ℝ) |
      ‖(WithLp.toLp 2 ((1 - ε)⁻¹ • p.2) : EuclideanSpace ℝ (Fin d))‖ ≤ R} :=
    measurableSet_le ((continuous_snd.comp hc).norm.measurable) measurable_const
  exact h1.inter h2

/-! ## The round map -/

open Classical in
/-- `df2NextAP` with its two `match` on the routine's answers written as `Option.elim`. -/
noncomputable def nextE {d : ℕ} (ap : ApFun d) (p : Df2OPar) (n : ℕ) (Keps : Set (Fin d → ℝ)) (st : Df2St d)
    (ξ w : Fin d → ℝ) (Y : ℝ) : Df2Mode d :=
  let u := st.P *ᵥ w
  let g := (Y / (1 - p.lam)) • u
  let c := p.eta * p.kap * p.lam * p.k0 * Y
  let a := 1 - c
  let q := a + c * (ξ ⬝ᵥ ξ)
  if a ≤ 0 ∨ q ≤ 0 then .guard else
  let P' := a • st.P + c • vecMulVec u u
  let S' := a⁻¹ • (st.S - (c / q) • vecMulVec w w)
  let c' := c / q / (1 + Real.sqrt (a / q))
  let A' := (Real.sqrt a)⁻¹ • (st.A - c' • vecMulVec w ξ)
  let b' := st.b + c • ((u ⬝ᵥ st.mu) • u - st.P *ᵥ st.mu)
  let k' := st.k + c / 2 * ((u ⬝ᵥ st.mu) ^ 2 - st.mu ⬝ᵥ (st.P *ᵥ st.mu))
  let G' := st.G + g
  let l' := st.l + g ⬝ᵥ st.mu
  if d / p.δe < P'.trace ∨ d / p.δe < S'.trace then .guard else
  let z := S' *ᵥ (b' - (p.eta / 2) • G')
  if p.R / p.δe ^ 3 < oNorm z then .guard else
  let Rm : Set (Fin d → ℝ) :=
    if st.first then Keps else {y | y ∈ Keps ∧ df2Phi st.P st.b st.k y ≤ (p.c1 - p.gam) * p.rho}
  (ap Rm st.ctr st.r p.R P' z (min 1 (p.alpha * p.rho / 2))).elim .guard fun pt =>
    if p.eta * (l' - G' ⬝ᵥ pt) - 2 * df2Phi P' b' k' pt ≤ -(p.theta * p.rho) then .run (df2Init p d) else
    let ctr' := (1 - p.sb) • pt
    let r' := p.sb * (1 - p.eps)
    let wmu := st.mu - (p.eta * Y / ((1 - p.lam) * q)) • w
    if p.R + p.eta * Real.sqrt (16 * d * n * p.Le / p.δe) < oNorm wmu then .guard else
    let Rp : Set (Fin d → ℝ) := {y | y ∈ Keps ∧ df2Phi P' b' k' y ≤ p.c1 * p.rho}
    (ap Rp ctr' r' p.R P' wmu (1 / (16 * n ^ 2 * max 1 (4 * p.R ^ 2 * P'.trace)))).elim .guard fun mu' =>
      .run ⟨false, mu', P', S', A', b', k', G', l', ctr', r'⟩

theorem nextE_eq {d : ℕ} (ap : ApFun d) (p : Df2OPar) (n : ℕ) (Keps : Set (Fin d → ℝ)) (st : Df2St d)
    (ξ w : Fin d → ℝ) (Y : ℝ) : df2NextAP ap p n Keps st ξ w Y = nextE ap p n Keps st ξ w Y := by
  unfold df2NextAP nextE
  dsimp only
  split_ifs <;> try rfl
  all_goals
    split
    · next heq => rw [heq]; rfl
    · next pt heq =>
      rw [heq]
      dsimp only [Option.elim]
      all_goals
        split_ifs <;> try rfl
        split
        · next heq2 => rw [heq2]
        · next mu heq2 => rw [heq2]

attribute [local fun_prop] measurable_st_first measurable_st_mu measurable_st_P measurable_st_S measurable_st_A
  measurable_st_b measurable_st_k measurable_st_G measurable_st_l measurable_st_ctr measurable_st_r measurable_oNorm

scoped instance instSCMatrix (m n : Type*) [Countable m] [Countable n] : SecondCountableTopology (Matrix m n ℝ) :=
  inferInstanceAs (SecondCountableTopology (m → n → ℝ))

section
variable {X : Type*} [MeasurableSpace X]

theorem mset_or {p q : X → Prop} (hp : MeasurableSet {x | p x}) (hq : MeasurableSet {x | q x}) :
    MeasurableSet {x | p x ∨ q x} := hp.union hq
theorem mset_and {p q : X → Prop} (hp : MeasurableSet {x | p x}) (hq : MeasurableSet {x | q x}) :
    MeasurableSet {x | p x ∧ q x} := hp.inter hq
theorem mset_le {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g) : MeasurableSet {x | f x ≤ g x} :=
  measurableSet_le hf hg
theorem mset_lt {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g) : MeasurableSet {x | f x < g x} :=
  measurableSet_lt hf hg
end

section
variable {d : ℕ}

theorem df2Phi_continuous : Continuous fun q : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) × ℝ × (Fin d → ℝ) =>
    df2Phi q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  unfold df2Phi; fun_prop

variable {X : Type*} [MeasurableSpace X]

theorem graphMeas_ite_bool {b : X → Bool} (hb : Measurable b) {Q1 Q2 : X → Set (Fin d → ℝ)} (h1 : GraphMeas Q1)
    (h2 : GraphMeas Q2) : GraphMeas fun x => if b x = true then Q1 x else Q2 x := by
  unfold GraphMeas at *
  have h : {p : X × (Fin d → ℝ) | p.2 ∈ if b p.1 = true then Q1 p.1 else Q2 p.1} =
      ({p | b p.1 = true} ∩ {p | p.2 ∈ Q1 p.1}) ∪ ({p | b p.1 = false} ∩ {p | p.2 ∈ Q2 p.1}) := by
    ext p
    by_cases hb1 : b p.1 = true <;> simp [hb1]
  rw [h]
  exact (((hb.comp measurable_fst) (measurableSet_singleton true)).inter h1).union
    (((hb.comp measurable_fst) (measurableSet_singleton false)).inter h2)

theorem graphMeas_sub {Q : X → Set (Fin d → ℝ)} (hQ : GraphMeas Q) {F : X → (Fin d → ℝ) → ℝ}
    (hF : Measurable fun q : X × (Fin d → ℝ) => F q.1 q.2) (c : ℝ) :
    GraphMeas fun x => {y | y ∈ Q x ∧ F x y ≤ c} :=
  hQ.inter (measurableSet_le hF measurable_const)

theorem graphMeas_comp {Y : Type*} [MeasurableSpace Y] {Q : Y → Set (Fin d → ℝ)}
    (hQ : MeasurableSet {q : Y × (Fin d → ℝ) | q.2 ∈ Q q.1}) {g : X → Y} (hg : Measurable g) :
    GraphMeas fun x => Q (g x) :=
  hQ.preimage ((hg.comp measurable_fst).prodMk measurable_snd)

@[fun_prop]
theorem meas_df2Phi {P : X → Matrix (Fin d) (Fin d) ℝ} {b : X → Fin d → ℝ}
    {k : X → ℝ} {y : X → Fin d → ℝ} (hP : Measurable P) (hb : Measurable b) (hk : Measurable k)
    (hy : Measurable y) : Measurable fun x => df2Phi (P x) (b x) (k x) (y x) :=
  df2Phi_continuous.measurable.comp (hP.prodMk (hb.prodMk (hk.prodMk hy)))

/-- The round map after the observation is measurable for any family of regions `Keps` with a measurable graph. -/
theorem df2NextAP_measurable (p : Df2OPar) (n : ℕ) (Keps : PgSp d → Set (Fin d → ℝ))
    (hK : MeasurableSet {q : PgSp d × (Fin d → ℝ) | q.2 ∈ Keps q.1}) :
    Measurable fun x : PgSp d × Df2St d × (Fin d → ℝ) × ℝ =>
      df2NextAP apCall p n (Keps x.1) x.2.1 x.2.2.1 (x.2.1.A *ᵥ x.2.2.1) x.2.2.2 := by
  simp only [nextE_eq]
  unfold nextE
  dsimp only
  refine Measurable.ite ?_ measurable_const ?_
  · refine mset_or (mset_le ?_ measurable_const) (mset_le ?_ measurable_const) <;> fun_prop
  refine Measurable.ite ?_ measurable_const ?_
  · refine mset_or (mset_lt measurable_const ?_) (mset_lt measurable_const ?_) <;> fun_prop
  refine Measurable.ite ?_ measurable_const ?_
  · refine mset_lt measurable_const ?_; fun_prop
  refine meas_optElim ?_ measurable_const ?_
  · refine meas_apCall _ ?_ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
    · exact graphMeas_ite_bool (by fun_prop) (graphMeas_comp hK (by fun_prop))
        (graphMeas_sub (graphMeas_comp hK (by fun_prop)) (by fun_prop) _)
    all_goals fun_prop
  refine Measurable.ite ?_ measurable_const ?_
  · refine mset_le ?_ measurable_const; fun_prop
  refine Measurable.ite ?_ measurable_const ?_
  · refine mset_lt measurable_const ?_; fun_prop
  refine meas_optElim ?_ measurable_const ?_
  · refine meas_apCall _ ?_ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
    · exact graphMeas_sub (graphMeas_comp hK (by fun_prop)) (by fun_prop) _
    all_goals fun_prop
  exact meas_run (meas_st_mk measurable_const (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) measurable_const)

end

/-- (L1) for `apCall`: `Df2ApCallMeas` of `Df2Layer2.lean`. -/
theorem df2ApCallMeas : Df2ApCallMeas := by
  intro d n δ K _ hK _
  exact df2NextAP_measurable (df2oPar d n δ) n
    (fun Ps => df2KepsOf (df2Kp K Ps (df2oPar d n δ).R) (df2oPar d n δ).eps) (keps_graph K hK _ _)

end AdversarialBco.Poly.ApMeas
