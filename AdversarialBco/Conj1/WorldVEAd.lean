/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1.WorldAd
public import AdversarialBco.Conj1.Cara
public import AdversarialBco.Poly.Df2WorldVE

@[expose] public section

/-!
# Lemma 8.8 on the world of a loss process

`df2VEWorldAdOf_holds : Df2VEWorldAdOf`. As `df2VEWorldOf_holds` (Df2WorldVE.lean), with the parameter of the
instance at the start round `a` enlarged from the position `q` to the pair `(q, l)`, `l` the parameter of the loss
process: the body is `kTh q`, the loss of round `s` is `gTh` of the losses `L · l` (`f_{a+s}(S⁻¹ ·)/2` on `PgGood`),
and round `s` reads the pair `(q, lam (a + s))`, which is measurable before round `s` of the instance
(`prefixσ_le_𝒢w`). (L1) for the instance (`epochMeasAd`) needs the loss jointly measurable in `(l, y)` on the
interior of `K`, which is the Carathéodory lemma (`Conj1.measurable_piecewise_interior`).

`df2VEWorld_of_ad`: the constant process gives back `Df2VEWorld`.
-/

open MeasureTheory ProbabilityTheory Matrix
open AdversarialBco.RealRAM

namespace AdversarialBco.Poly.Conj1

open Layer2

variable {d : ℕ}

/-! ## (L1) for the instance with the loss parameter -/

theorem ext_kTh_measAd {n : ℕ} {δ : ℝ} {K : Set (E d)} (hKc : IsClosed K) (hKconv : Convex ℝ K)
    (hG : PgGoodMeas) (hR : 1 ≤ (df2oPar d n δ).R) (hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d)
    (heps0 : 0 < (df2oPar d n δ).eps) (heps1 : (df2oPar d n δ).eps < 1) {Λ : Type} [MeasurableSpace Λ]
    {L : ℕ → Λ → E d → ℝ} {a s : ℕ} (hconv : ∀ l, ConvexOn ℝ K (L (a + s) l))
    (hm : ∀ y ∈ interior K, Measurable fun l => L (a + s) l y) :
    Measurable fun p : (PgSp d × Λ) × E d =>
      df2Ext (df2oPar d n δ) (kTh n δ K p.1.1) (gTh n δ K (fun t => L t p.1.2) a s p.1.1) p.2 := by
  classical
  set P : (PgSp d × Λ) × E d → ℝ := fun p => df2Pip (df2oPar d n δ) (kTh n δ K p.1.1) p.2 with hPdef
  have hP : Measurable P :=
    measurable_const.max (((gauge_kTh_meas hKc hKconv hG hR hmw).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).div_const _)
  set F : Λ × E d → ℝ := fun p => (interior K).piecewise (L (a + s) p.1) 0 p.2 with hFdef
  have hF : Measurable F := Conj1.measurable_piecewise_interior K (L (a + s)) hconv hm
  have hGs : MeasurableSet {p : (PgSp d × Λ) × E d | PgGood d K (df2oPar d n δ).R (some p.1.1)} :=
    (measurable_fst.comp measurable_fst) (hG d K _ hKconv hKc)
  have hpt : Measurable fun p : (PgSp d × Λ) × E d => pgMu p.1.1 + pgOp p.1.1 ((P p)⁻¹ • p.2) :=
    (pg_continuous d).2.2.measurable.comp ((measurable_fst.comp measurable_fst).prodMk (hP.inv.smul measurable_snd))
  have heq : (fun p : (PgSp d × Λ) × E d =>
      df2Ext (df2oPar d n δ) (kTh n δ K p.1.1) (gTh n δ K (fun t => L t p.1.2) a s p.1.1) p.2) =
      fun p => P p * (if PgGood d K (df2oPar d n δ).R (some p.1.1) then
          F (p.1.2, pgMu p.1.1 + pgOp p.1.1 ((P p)⁻¹ • p.2)) / 2 else 0) +
        2 * (P p - 1) / (df2oPar d n δ).eps := by
    funext p
    by_cases hq : PgGood d K (df2oPar d n δ).R (some p.1.1)
    · have hin := play_interior hKconv hq heps0 heps1 p.2
      have hk := kTh_good (n := n) (δ := δ) hq
      simp only [hPdef, hk, df2Ext, gTh, hq, ↓reduceIte, hFdef]
      rw [Set.piecewise_eq_of_mem _ _ _ hin]
    · simp [df2Ext, hPdef, gTh, hq]
  rw [heq]
  exact (hP.mul (Measurable.ite hGs ((hF.comp ((measurable_snd.comp measurable_fst).prodMk hpt)).div_const 2)
    measurable_const)).add (((hP.sub measurable_const).const_mul 2).div_const _)

/-- (L1) for the instance of the world of a loss process at the start round `a`. -/
theorem epochMeasAd {n : ℕ} {δ : ℝ} {K : Set (E d)} (hd : 1 ≤ d) (hKc : IsClosed K) (hKconv : Convex ℝ K)
    (hG : PgGoodMeas) (hAp : Df2ApCallMeas) (hR : 1 ≤ (df2oPar d n δ).R)
    (hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d) (heps0 : 0 < (df2oPar d n δ).eps) (heps1 : (df2oPar d n δ).eps < 1)
    {Λ : Type} [MeasurableSpace Λ] {L : ℕ → Λ → E d → ℝ} (hadm : ∀ t < n, ∀ l, AdmLoss K (L t l))
    (hm : ∀ t < n, ∀ y ∈ interior K, Measurable fun l => L t l y) (a : ℕ) :
    Df2EpochMeas (df2oPar d n δ) n (n - a) (fun x : PgSp d × Λ => kTh n δ K x.1)
      (fun s x => gTh n δ K (fun t => L t x.2) a s x.1) apCall := by
  refine ⟨?_, fun s hs => ?_, ?_⟩
  · have h := gauge_kTh_meas (n := n) (δ := δ) hKc hKconv hG hR hmw
    have hg : Measurable fun x : (PgSp d × Λ) × E d => (x.1.1, x.2) :=
      (measurable_fst.comp measurable_fst).prodMk measurable_snd
    have h2 := h.comp hg
    rw [Function.comp_def] at h2
    exact h2
  · exact ext_kTh_measAd hKc hKconv hG hR hmw heps0 heps1 (fun l => (hadm (a + s) (by omega) l).1)
      (hm (a + s) (by omega))
  · have h := next_kTh_meas (n := n) (δ := δ) hd hKc hKconv hG hAp
    have hg : Measurable fun x : (PgSp d × Λ) × Df2St d × (Fin d → ℝ) × ℝ => (x.1.1, x.2) :=
      (measurable_fst.comp measurable_fst).prodMk measurable_snd
    have h2 := h.comp hg
    rw [Function.comp_def] at h2
    exact h2

/-! ## The parameter of the instance -/

/-- The loss parameter read by round `s` of the instance at the start round `a`: `lam (a + s)` below the horizon,
`lam a` past it (never read). -/
noncomputable def lamAt {Λ : Type} (n : ℕ) (lam : ℕ → WΩ → Λ) (a s : ℕ) (ω : WΩ) : Λ :=
  if a + s < n then lam (a + s) ω else lam a ω

theorem lamAt_meas {N0 S n : ℕ} (hS : N0 + n * (d + 1) ≤ S) {Λ : Type} [MeasurableSpace Λ] {lam : ℕ → WΩ → Λ}
    (hlam : ∀ t < n, Measurable[prefixσ N0 S n d t] (lam t)) {a : ℕ} (ha : a < n) (s : ℕ) :
    Measurable[𝒢w N0 S n d a s] (lamAt n lam a s) := by
  unfold lamAt
  by_cases h : a + s < n
  · simp only [h, ↓reduceIte]
    exact (hlam (a + s) h).mono (prefixσ_le_𝒢w N0 S n d a s hS) le_rfl
  · simp only [h, ↓reduceIte]
    have h0 : prefixσ N0 S n d a ≤ 𝒢w N0 S n d a 0 := prefixσ_le_𝒢w N0 S n d a 0 hS
    exact (hlam a ha).mono (h0.trans ((𝒢w N0 S n d a).mono (Nat.zero_le s))) le_rfl

/-- The position returned by PG reads only `K` and the Gaussian stream. -/
theorem ps_world_eq {n : ℕ} {r0 R0 δ : ℝ} (K : Set (E d)) (f g : ℕ → E d → ℝ) (ω : WΩ) :
    df2oPs d n r0 R0 δ (df2World K f ω) = df2oPs d n r0 R0 δ (df2World K g ω) := rfl

theorem ps_world_meas (hPG : PgMeas) {n : ℕ} {r0 R0 δ : ℝ} {K : Set (E d)} (hKc : IsClosed K)
    (f : WΩ → ℕ → E d → ℝ) (a : ℕ) :
    Measurable[𝒢w (df2oN0 d r0 R0 (df2oPar d n δ).δ1) (df2oSpare d n r0 R0 (df2oPar d n δ).δ1) n d a 0]
      fun ω : WΩ => df2oPs d n r0 R0 δ (df2World K (f ω) ω) := by
  have h := theta_meas hPG (n := n) (r0 := r0) (R0 := R0) (δ := δ) hKc (fun _ _ => 0) a
  have he : (fun ω : WΩ => df2oPs d n r0 R0 δ (df2World K (f ω) ω)) =
      fun ω : WΩ => df2oPs d n r0 R0 δ (df2World K (fun _ _ => 0) ω) :=
    funext fun ω => ps_world_eq K (f ω) _ ω
  rw [he]
  exact h

/-! ## Lemma 8.8 on the world of a loss process -/

/-- `Df2VEWorldAdOf`: each virtual epoch of D0 on the world of a loss process is an instance of the adapted setting
(E), so E1-loc in its adapted form bounds it. -/
theorem df2VEWorldAdOf_holds : Df2VEWorldAdOf := by
  intro E1 PAP PGM PGG APM d n r0 R0 δ K hB F ν hν a ha
  obtain ⟨hd, hn, _, _, hδ0, hδ1, hKcpt, hKconv, _, _⟩ := hB
  have hKc := hKcpt.isClosed
  have := hν.1
  by_cases heps : (df2oPar d n δ).eps ≤ 1 / 2
  swap
  · exact (measure_mono (show _ ⊆ (∅ : Set WΩ) from fun ω hω => heps hω.1.2)).trans (by simp)
  have H := rowHyp_of d n δ hd hn hδ0 hδ1 heps
  have hR := row_one_le_R _ d n H
  have hmw : 1 / (df2oPar d n δ).R ≤ df2Mw d := by rw [H.R]; exact inv_R_le_df2Mw d hd
  have heps0 := eps_pos_of_rows H
  have heps1 : (df2oPar d n δ).eps < 1 := by linarith
  have hAp : ApSpec (d := d) apCall := fun Q a0 r R P w e =>
    ⟨fun h1 h2 h3 h4 h5 h6 h7 => (PAP d Q a0 r R P w e).1 hd h1 h2 h3 h4 h5 h6 h7, (PAP d Q a0 r R P w e).2⟩
  set θ : ℕ → WΩ → PgSp d × F.Λ := fun s ω => (df2oPs d n r0 R0 δ (df2World K (F.loss ω) ω), lamAt n F.lam a s ω)
    with hθ
  have hθm : ∀ s, Measurable[𝒢w (df2oN0 d r0 R0 (df2oPar d n δ).δ1) (df2oSpare d n r0 R0 (df2oPar d n δ).δ1)
      n d a s] (θ s) := fun s =>
    ((ps_world_meas PGM hKc F.loss a).mono ((𝒢w _ _ n d a).mono (Nat.zero_le s)) le_rfl).prodMk
      (lamAt_meas le_rfl F.lam_meas ha s)
  have hBd := E1 d n (n - a) δ hd hn (by omega) (by omega) hδ0 hδ1 heps (PgSp d × F.Λ)
    (fun x => kTh n δ K x.1) (fun s x => gTh n δ K (fun t => F.L t x.2) a s x.1) apCall
    (fun x => body_kTh hKc hKconv hR hmw x.1)
    (fun x s hs => adm_gTh (f := fun t => F.L t x.2) hKconv hKc hR hmw (F.adm (a + s) (by omega) x.2) x.1) hAp
    (epochMeasAd hd hKc hKconv PGG APM hR hmw heps0 heps1 F.adm F.meas a) WΩ (gaussStream.prod ν) inferInstance
    (𝒢w (df2oN0 d r0 R0 (df2oPar d n δ).δ1) (df2oSpare d n r0 R0 (df2oPar d n δ).δ1) n d a) θ
    (xiL (df2oN0 d r0 R0 (df2oPar d n δ).δ1) (df2oSpare d n r0 R0 (df2oPar d n δ).δ1) n d a)
    (eL (df2oN0 d r0 R0 (df2oPar d n δ).δ1) (df2oSpare d n r0 R0 (df2oPar d n δ).δ1) n d a) hθm (fun _ _ => rfl)
    (setE_world _ _ n a lemmaNZProd ν hν le_rfl)
  refine (measure_mono fun ω hω => ?_).trans hBd
  obtain ⟨hcase, hnot⟩ := hω
  have hgood : PgGood d K (df2oPar d n δ).R (some (df2oPs d n r0 R0 δ (df2World K (F.loss ω) ω))) :=
    case_good hcase
  simp only [Set.mem_ofPred_eq, hθ]
  rw [kTh_good hgood]
  refine fun hok => hnot ((ctx_epochOK_congr _ _ (df2zPath d n r0 R0 δ (df2World K (F.loss ω) ω) a) (n - a)
    (by omega) fun s hs => ⟨?_, ?_, ?_⟩).mp hok)
  · have hlt : a + s < n := by omega
    simp only [gTh, hgood, ↓reduceIte, lamAt, hlt]
    rfl
  · have hlt : a + s < n := by omega
    simp [eL, lay, hlt, df2zPath, df2oZeta, df2World]
  · have hlt : a + s < n := by omega
    funext c
    simp [xiL, lay, hlt, df2zPath, df2oXi, df2World]

/-! ## The constant process -/

/-- The constant loss process of a sequence of admissible losses. -/
def constProc {n N0 S : ℕ} {K : Set (E d)} {f : ℕ → E d → ℝ} (hf : f ∈ Advs K n) : Df2LossProc d n N0 S K where
  Λ := Unit
  L t _ := f t
  lam _ _ := ()
  adm t ht _ := hf t ht
  meas _ _ _ _ := measurable_const
  lam_meas _ _ := measurable_const

theorem constProc_loss {n N0 S : ℕ} {K : Set (E d)} {f : ℕ → E d → ℝ} (hf : f ∈ Advs K n) (ω : WΩ) :
    (constProc (N0 := N0) (S := S) hf).loss ω = f := rfl

/-- The constant process gives back `Df2VEWorld`: the adapted statement is no weaker. -/
theorem df2VEWorld_of_ad (h : Df2VEWorldAd) : Df2VEWorld := by
  intro d n r0 R0 δ K f hW ν hν a ha
  obtain ⟨hd, hn, hr0, hr, hδ0, hδ1, hKc, hKconv, hball, hsub, hf⟩ := hW
  exact h d n r0 R0 δ K ⟨hd, hn, hr0, hr, hδ0, hδ1, hKc, hKconv, hball, hsub⟩ (constProc hf) ν hν a ha

end AdversarialBco.Poly.Conj1
