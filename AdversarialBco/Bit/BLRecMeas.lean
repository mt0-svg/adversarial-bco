/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.BLEngine
public import AdversarialBco.Bit.ShadowMeas
public import AdversarialBco.Poly.Df2ApMeasProof

@[expose] public section

/-!
# (O4-M) for BL's record: the measurability lemmas

The lemmas behind the measurability of the shift and the advice of BL's record: a function of a countable measurable
parameter and of the point, measurable in the point at each value, is measurable (`measurable_param`); the coin
sequence of a prefix (`extC`, `extC_pre`); the measurability of the matrix and vector operations (`m_mulVec`, `m_dot`,
`m_vmv`, `m_tr`, `m_addM`, `m_smulM`), of P°'s test (`refTest_meas`), of the selection of the selection lemma
(`selT_meas`), and `meas_shapeY`.
-/

open MeasureTheory
open scoped Matrix

namespace AdversarialBco.Bit.BLP

open AdversarialBco.BitRAM
open AdversarialBco.RealRAM (Strategy lossAd polytope)
open AdversarialBco.Poly
open AdversarialBco.Poly.Layer2 (kTh WΩ rowHyp_of row_one_le_R inv_R_le_df2Mw body_kTh)
open AdversarialBco.Poly.Conj1 (fL)
open AdversarialBco.Bit.Cpl
open AdversarialBco.Bit.Asm

variable {d : ℕ}

/-! ## Countable parameters and coin prefixes -/

/-- A function of a measurable parameter with countably many values and of the point, measurable in the point at each
value of the parameter, is measurable. -/
theorem measurable_param {X Y V : Type*} {mX : MeasurableSpace X} [MeasurableSpace Y] [MeasurableSpace V]
    [Countable V] [MeasurableSingletonClass V] {P : X → V} (hP : Measurable P) (g : V → X → Y)
    (hg : ∀ v, Measurable (g v)) : Measurable fun x => g (P x) x := by
  have h : Measurable fun p : X × V => g p.2 p.1 := measurable_from_prod_countable_left hg
  exact h.comp (measurable_id.prodMk hP)

/-- The coin sequence of a prefix, `false` past it. -/
def extC {N : ℕ} (c : Fin N → Bool) : ℕ → Bool := fun j => if h : j < N then c ⟨j, h⟩ else false

theorem extC_pre (cs : ℕ → Bool) (N : ℕ) : ∀ j < N, cs j = extC (fun j : Fin N => cs j) j :=
  fun j hj => by simp [extC, hj]

/-! ## The shift -/

variable {R : Routines} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {σ : Strategy d}

/-! ## The advice -/

/-! ### Measurability of the matrix operations -/

section MatMeas

variable {Y : Type*} [MeasurableSpace Y]

theorem m_mulVec {M : Y → Matrix (Fin d) (Fin d) ℝ} {v : Y → Fin d → ℝ} (hM : Measurable M) (hv : Measurable v) :
    Measurable fun y => M y *ᵥ v y :=
  (Continuous.matrix_mulVec continuous_fst continuous_snd).measurable.comp (hM.prodMk hv)

theorem m_dot {u v : Y → Fin d → ℝ} (hu : Measurable u) (hv : Measurable v) : Measurable fun y => u y ⬝ᵥ v y :=
  (Continuous.dotProduct continuous_fst continuous_snd).measurable.comp (hu.prodMk hv)

theorem m_vmv {u v : Y → Fin d → ℝ} (hu : Measurable u) (hv : Measurable v) :
    Measurable fun y => Matrix.vecMulVec (u y) (v y) := by
  have h : Continuous fun z : (Fin d → ℝ) × (Fin d → ℝ) => (Matrix.vecMulVec z.1 z.2 : Matrix (Fin d) (Fin d) ℝ) :=
    Continuous.matrix_vecMulVec continuous_fst continuous_snd
  exact h.measurable.comp (hu.prodMk hv)

theorem m_tr {M : Y → Matrix (Fin d) (Fin d) ℝ} (hM : Measurable M) : Measurable fun y => (M y)ᵀ :=
  (continuous_id.matrix_transpose).measurable.comp hM

theorem m_addM {M N : Y → Matrix (Fin d) (Fin d) ℝ} (hM : Measurable M) (hN : Measurable N) :
    Measurable fun y => M y + N y := by
  have : OpensMeasurableSpace (Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (OpensMeasurableSpace ((Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)))
  exact continuous_add.measurable.comp (hM.prodMk hN)

theorem m_smulM {c : Y → ℝ} {M : Y → Matrix (Fin d) (Fin d) ℝ} (hc : Measurable c) (hM : Measurable M) :
    Measurable fun y => c y • M y := by
  have : OpensMeasurableSpace (ℝ × Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (OpensMeasurableSpace (ℝ × (Fin d → Fin d → ℝ)))
  exact (continuous_fst.smul continuous_snd).measurable.comp (hc.prodMk hM)

end MatMeas

/-- `refTest` is measurable in P°'s state, the draw and the observation. -/
theorem refTest_meas (p : Df2OPar) :
    Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => refTest p y.1 y.2.1 y.2.2 := by
  have hA : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => y.1.A := ApMeas.measurable_st_A.comp measurable_fst
  have hP : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => y.1.P := ApMeas.measurable_st_P.comp measurable_fst
  have hb : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => y.1.b := ApMeas.measurable_st_b.comp measurable_fst
  have hk : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => y.1.k := ApMeas.measurable_st_k.comp measurable_fst
  have hG : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => y.1.G := ApMeas.measurable_st_G.comp measurable_fst
  have hl : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => y.1.l := ApMeas.measurable_st_l.comp measurable_fst
  have hmu : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => y.1.mu := ApMeas.measurable_st_mu.comp measurable_fst
  have hξ : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => y.2.1 := measurable_fst.comp measurable_snd
  have hY : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => y.2.2 := measurable_snd.comp measurable_snd
  have hu := m_mulVec hP (m_mulVec hA hξ)
  have hg : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ =>
      (y.2.2 / (1 - p.lam)) • (y.1.P *ᵥ (y.1.A *ᵥ y.2.1)) := (hY.div_const _).smul hu
  have hc : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ => p.eta * p.kap * p.lam * p.k0 * y.2.2 :=
    measurable_const.mul hY
  have hPmu := m_mulVec hP hmu
  have hum := m_dot hu hmu
  have hP' : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ =>
      (1 - p.eta * p.kap * p.lam * p.k0 * y.2.2) • y.1.P + (p.eta * p.kap * p.lam * p.k0 * y.2.2) •
        Matrix.vecMulVec (y.1.P *ᵥ (y.1.A *ᵥ y.2.1)) (y.1.P *ᵥ (y.1.A *ᵥ y.2.1)) :=
    m_addM (m_smulM (measurable_const.sub hc) hP) (m_smulM hc (m_vmv hu hu))
  have hb' : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ =>
      y.1.b + (p.eta * p.kap * p.lam * p.k0 * y.2.2) •
        (((y.1.P *ᵥ (y.1.A *ᵥ y.2.1)) ⬝ᵥ y.1.mu) • (y.1.P *ᵥ (y.1.A *ᵥ y.2.1)) - y.1.P *ᵥ y.1.mu) :=
    hb.add (hc.smul ((hum.smul hu).sub hPmu))
  have hk' : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ =>
      y.1.k + p.eta * p.kap * p.lam * p.k0 * y.2.2 / 2 *
        (((y.1.P *ᵥ (y.1.A *ᵥ y.2.1)) ⬝ᵥ y.1.mu) ^ 2 - y.1.mu ⬝ᵥ (y.1.P *ᵥ y.1.mu)) :=
    hk.add ((hc.div_const 2).mul ((hum.pow_const 2).sub (m_dot hmu hPmu)))
  have hG' : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ =>
      y.1.G + (y.2.2 / (1 - p.lam)) • (y.1.P *ᵥ (y.1.A *ᵥ y.2.1)) := hG.add hg
  have hl' : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ =>
      y.1.l + ((y.2.2 / (1 - p.lam)) • (y.1.P *ᵥ (y.1.A *ᵥ y.2.1))) ⬝ᵥ y.1.mu := hl.add (m_dot hg hmu)
  have h1 : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ =>
      p.eta * (y.1.l + ((y.2.2 / (1 - p.lam)) • (y.1.P *ᵥ (y.1.A *ᵥ y.2.1))) ⬝ᵥ y.1.mu) -
        2 * (y.1.k + p.eta * p.kap * p.lam * p.k0 * y.2.2 / 2 *
          (((y.1.P *ᵥ (y.1.A *ᵥ y.2.1)) ⬝ᵥ y.1.mu) ^ 2 - y.1.mu ⬝ᵥ (y.1.P *ᵥ y.1.mu))) :=
    (hl'.const_mul _).sub (hk'.const_mul _)
  have h2 : Measurable fun y : Df2St d × (Fin d → ℝ) × ℝ =>
      (2 : ℕ) • (y.1.b + (p.eta * p.kap * p.lam * p.k0 * y.2.2) •
        (((y.1.P *ᵥ (y.1.A *ᵥ y.2.1)) ⬝ᵥ y.1.mu) • (y.1.P *ᵥ (y.1.A *ᵥ y.2.1)) - y.1.P *ᵥ y.1.mu)) -
      p.eta • (y.1.G + (y.2.2 / (1 - p.lam)) • (y.1.P *ᵥ (y.1.A *ᵥ y.2.1))) :=
    ((continuous_const_smul (2 : ℕ)).measurable.comp hb').sub (hG'.const_smul p.eta)
  exact h1.prodMk (h2.prodMk hP')

open Classical in
/-- The selection of the selection lemma is measurable in the test function and the ball, at fixed threshold, point and
decision. -/
theorem selT_meas {Y : Type*} [MeasurableSpace Y] {κ : Y → ℝ} {h : Y → Fin d → ℝ}
    {P : Y → Matrix (Fin d) (Fin d) ℝ} {c0 : Y → Fin d → ℝ} {r : Y → ℝ} (hκ : Measurable κ) (hh : Measurable h)
    (hP : Measurable P) (hc0 : Measurable c0) (hr : Measurable r) (T : ℝ) (p : Fin d → ℝ) (fire : Bool) :
    Measurable fun y => selT (κ y) (h y) (P y) T (c0 y) (r y) p fire := by
  have hPP := m_addM hP (m_tr hP)
  have hgr : Measurable fun y => h y - (P y + (P y)ᵀ) *ᵥ c0 y := hh.sub (m_mulVec hPP hc0)
  have hpc : Measurable fun _ : Y => p := measurable_const
  obtain ⟨V, hV⟩ : ∃ V : Y → Fin d → ℝ, V = fun y =>
      if h y - (P y + (P y)ᵀ) *ᵥ c0 y = 0 then (fun i : Fin d => if (i : ℕ) = 0 then (1 : ℝ) else 0)
      else (oNorm (h y - (P y + (P y)ᵀ) *ᵥ c0 y))⁻¹ • (-(h y - (P y + (P y)ᵀ) *ᵥ c0 y)) := ⟨_, rfl⟩
  have hv : Measurable V := by
    rw [hV]
    exact Measurable.ite (hgr (measurableSet_singleton 0)) measurable_const
      ((ApMeas.measurable_oNorm.comp hgr).inv.smul hgr.neg)
  obtain ⟨DV, hDV⟩ : ∃ DV : Y → Fin d → ℝ, DV = fun y => (c0 y + r y • V y) - p := ⟨_, rfl⟩
  have hdv : Measurable DV := by rw [hDV]; exact (hc0.add (hr.smul hv)).sub_const p
  have hFp : Measurable fun y => κ y + h y ⬝ᵥ p - p ⬝ᵥ (P y *ᵥ p) :=
    (hκ.add (m_dot hh hpc)).sub (m_dot hpc (m_mulVec hP hpc))
  obtain ⟨A0, hA0⟩ : ∃ A0 : Y → ℝ, A0 = fun y => κ y + h y ⬝ᵥ p - p ⬝ᵥ (P y *ᵥ p) - T := ⟨_, rfl⟩
  have hα0 : Measurable A0 := by rw [hA0]; exact hFp.sub_const T
  obtain ⟨A1, hA1⟩ : ∃ A1 : Y → ℝ, A1 = fun y => (h y - (P y + (P y)ᵀ) *ᵥ p) ⬝ᵥ DV y := ⟨_, rfl⟩
  have hα1 : Measurable A1 := by rw [hA1]; exact m_dot (hh.sub (m_mulVec hPP hpc)) hdv
  obtain ⟨A2, hA2⟩ : ∃ A2 : Y → ℝ, A2 = fun y => DV y ⬝ᵥ (P y *ᵥ DV y) := ⟨_, rfl⟩
  have hα2 : Measurable A2 := by rw [hA2]; exact m_dot hdv (m_mulVec hP hdv)
  have hthen : Measurable fun y => p + (2 * A0 y / (Real.sqrt (A1 y ^ 2 + 4 * A0 y * A2 y) - A1 y)) • DV y :=
    hpc.add (((hα0.const_mul 2).div (((hα1.pow_const 2).add ((hα0.const_mul 4).mul hα2)).sqrt.sub
      hα1)).smul hdv)
  have hset : MeasurableSet {y | fire = true ∧ T < κ y + h y ⬝ᵥ p - p ⬝ᵥ (P y *ᵥ p)} :=
    ApMeas.mset_and (MeasurableSet.const _) (ApMeas.mset_lt measurable_const hFp)
  subst hA2 hA1 hA0 hDV hV
  exact Measurable.ite hset hthen measurable_const

section MeasB

variable (hd : 1 ≤ d) (hn : 1 ≤ n) (hc : RunCase d n)
include hd hn hc

omit hd hn hc in
theorem meas_shapeY {Y : Type*} [MeasurableSpace Y] {P L e C : Y → ℝ} (hP : Measurable P) (hL : Measurable L)
    (he : Measurable e) (hC : Measurable C) (c : ℝ) :
    Measurable fun y => P y * (L y + e y + C y) / 2 + 2 * (P y - 1) / c := by
  fun_prop

end MeasB

end AdversarialBco.Bit.BLP
