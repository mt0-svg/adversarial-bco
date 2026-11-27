/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EllOCut

@[expose] public section

/-!
# UNI-ELL: statements (a) and (b) of ELL-O and BIS-O

UNI-ELL (the paper's appendix on rational ellipsoid methods). The proof of ELL-R (b) (Bit/ApQ/Ell.lean) with the region
`Q = QK ∩ region` in place of the rows' region, and the cut condition of a test asked only on the ball
`B' = B̄(z₀, ρ)`, `ρ = 2^{-j}`, whose points have their `ρ`-neighbourhood in `Q`: the SEP cut of step 2 keeps `B'`
(`sep_branch`), the exact cuts of steps 1 and 3 keep all of `Q`, the objective cut of step 4 keeps `B'` or records a
good point.

* `ellTestO_spec`: one test (`TOK`, the cut condition on `B'`, the cut vector nonzero).
* `ellLoopO_main`, `ellO_spec`: the induction of ELL-R on the claim `I_k` (`EInvO`), with `ellUpd_step` for a step.
* `bisLoopO_main`, `bisO_spec`: BIS-O.
* `ball_existsO`: `B' = B̄(p_θ, ρ)`, `p_θ = (1 - θ) p* + θ a₀`, `ρ ≤ θ min(r, 1)`: `B̄(p_θ, 2ρ) ⊆ Q` (the ball of (HQ-O)
  has radius `2r`) and every point of `B'` within `e` of the minimum.
* `ellOAcc : EllOAcc` (statement (b)); `ellOCert : EllOCert` (statement (a)).
-/

namespace AdversarialBco.Uni.EllO

open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.LeanAp Matrix
open AdversarialBco.Bit.RQ (EllI Cut ESt ellUpd ellTest)
open AdversarialBco.Bit.ApQ (vR vZ mR InE InB gam regionI GI gG updK VI ghI)

variable {d : ℕ}

/-! ## The region and the objective -/

theorem regionO_eq (I : EllOI d) : regionO I = regionI I.base := by
  ext y
  simp only [regionO, regionI, EllOI.base, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun i => i.elim0, h1, h2⟩
  · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩

/-! ## Good points and the kept point, on a region `Q` -/

/-- `x/2^s` lies in `Q` within `e` of the minimum of `G` on `Q`. -/
def GoodQ (I : EllI d) (Q : Set (Fin d → ℝ)) (s : ℕ) (x : Fin d → ℤ) : Prop :=
  vR s x ∈ Q ∧ ∀ y ∈ Q, GI I (vR s x) ≤ GI I y + I.e

/-- The kept point lies in `Q` and carries its value `V = 2^{2s+1} D_f G`. -/
def KOK (I : EllI d) (Q : Set (Fin d → ℝ)) (s : ℕ) (kept : Option ((Fin d → ℤ) × ℤ)) : Prop :=
  ∀ b W, kept = some (b, W) → vR s b ∈ Q ∧ (W : ℝ) = 2 ^ (2 * s + 1) * I.Df * GI I (vR s b)

/-- The kept point is good. -/
def KGood (I : EllI d) (Q : Set (Fin d → ℝ)) (s : ℕ) (kept : Option ((Fin d → ℤ) × ℤ)) : Prop :=
  ∃ b W, kept = some (b, W) ∧ GoodQ I Q s b

/-- What a test of ELL-O guarantees: a returned point is good; a cut `c ≠ 0` keeps the kept point well formed, and
good once good, and has every point of `B' = B̄(z₀, ρ)` on its side `c·(z - â/2^s) ≤ 0` unless the new kept point is
good. -/
def TOK (I : EllI d) (Q : Set (Fin d → ℝ)) (z0 : Fin d → ℝ) (ρ : ℝ) (s : ℕ) (a : Fin d → ℤ)
    (kept : Option ((Fin d → ℤ) × ℤ)) : Cut d → Prop
  | .ret x => GoodQ I Q s x
  | .cut c kept' => KOK I Q s kept' ∧ (KGood I Q s kept → KGood I Q s kept') ∧ c ≠ 0 ∧
      ∀ z, InB z0 ρ z → vZ c ⬝ᵥ (z - vR s a) ≤ 0 ∨ KGood I Q s kept'

theorem updK_okQ (I : EllI d) (Q : Set (Fin d → ℝ)) (s : ℕ) (a : Fin d → ℤ) (V : ℤ)
    (kept : Option ((Fin d → ℤ) × ℤ)) (hk : KOK I Q s kept) (hin : vR s a ∈ Q)
    (hV : (V : ℝ) = 2 ^ (2 * s + 1) * I.Df * GI I (vR s a)) : KOK I Q s (updK a V kept) := by
  intro b W hbW
  cases kept with
  | none =>
    simp only [updK, Option.some.injEq, Prod.mk.injEq] at hbW
    obtain ⟨rfl, rfl⟩ := hbW
    exact ⟨hin, hV⟩
  | some bw =>
    obtain ⟨b0, W0⟩ := bw
    simp only [updK] at hbW
    split_ifs at hbW
    · simp only [Option.some.injEq, Prod.mk.injEq] at hbW
      obtain ⟨rfl, rfl⟩ := hbW
      exact ⟨hin, hV⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at hbW
      obtain ⟨rfl, rfl⟩ := hbW
      exact hk _ _ rfl

theorem updK_monoQ (I : EllI d) (Q : Set (Fin d → ℝ)) (s : ℕ) (a : Fin d → ℤ) (V : ℤ)
    (kept : Option ((Fin d → ℤ) × ℤ)) (hDf : 0 < I.Df) (hk : KOK I Q s kept) (hin : vR s a ∈ Q)
    (hV : (V : ℝ) = 2 ^ (2 * s + 1) * I.Df * GI I (vR s a)) (hg : KGood I Q s kept) :
    KGood I Q s (updK a V kept) := by
  obtain ⟨b, W, rfl, hb⟩ := hg
  have hbk := hk b W rfl
  have hpos : (0 : ℝ) < 2 ^ (2 * s + 1) * I.Df := mul_pos (by positivity) (by exact_mod_cast hDf)
  simp only [updK]
  split_ifs with hVW
  · refine ⟨a, V, rfl, hin, fun y hy => ?_⟩
    have hlt : (V : ℝ) < W := by exact_mod_cast hVW
    rw [hV, hbk.2] at hlt
    have := lt_of_mul_lt_mul_left hlt hpos.le
    linarith [hb.2 y hy]
  · exact ⟨b, W, rfl, hb⟩

theorem updK_goodQ (I : EllI d) (Q : Set (Fin d → ℝ)) (s : ℕ) (a : Fin d → ℤ) (V : ℤ)
    (kept : Option ((Fin d → ℤ) × ℤ)) (hDf : 0 < I.Df) (hk : KOK I Q s kept)
    (hV : (V : ℝ) = 2 ^ (2 * s + 1) * I.Df * GI I (vR s a)) (hg : GoodQ I Q s a) :
    KGood I Q s (updK a V kept) := by
  have hpos : (0 : ℝ) < 2 ^ (2 * s + 1) * I.Df := mul_pos (by positivity) (by exact_mod_cast hDf)
  cases kept with
  | none => exact ⟨a, V, rfl, hg⟩
  | some bw =>
    obtain ⟨b, W⟩ := bw
    simp only [updK]
    split_ifs with hVW
    · exact ⟨a, V, rfl, hg⟩
    · have hbk := hk b W rfl
      refine ⟨b, W, rfl, hbk.1, fun y hy => ?_⟩
      have hle : (W : ℝ) ≤ V := by exact_mod_cast not_lt.mp hVW
      rw [hV, hbk.2] at hle
      have := le_of_mul_le_mul_left hle hpos
      linarith [hg.2 y hy]

theorem keptGood_mapQ (I : EllI d) (Q : Set (Fin d → ℝ)) (s : ℕ) (kept : Option ((Fin d → ℤ) × ℤ))
    (h : KGood I Q s kept) : ∃ x, kept.map Prod.fst = some x ∧ GoodQ I Q s x := by
  obtain ⟨b, W, rfl, hb⟩ := h
  exact ⟨b, rfl, hb⟩

/-! ## The hypotheses of (HQ-O) on the ball `B'` -/

/-- The hypotheses of statement (b) and the ball `B' = B̄(z₀, ρ)`, `ρ = 2^{-j}`: its points have their
`ρ`-neighbourhood in `Q = QK ∩ region` and lie within `e` of the minimum of `G` on `Q`. -/
structure HypO (I : EllOI d) (T : (Fin d → ℚ) → Bool) (QK : Set (Fin d → ℝ)) (RK η : ℝ) (z0 : Fin d → ℝ) : Prop
    where
  hSA : SepAcc
  hGA : GaugeAcc
  hd : 1 ≤ d
  hR : 1 ≤ I.R
  hP : (I.P.map ((↑) : ℤ → ℝ)).PosSemidef
  hH : (I.H.map ((↑) : ℤ → ℝ)).PosSemidef
  hDf : 0 < I.Df
  he : 0 < I.e
  hQ : Convex ℝ QK
  hcl : IsClosed QK
  hQR : QK ⊆ oBall 0 RK
  hball : oBall (qR I.c) ((2 : ℝ)⁻¹ ^ I.erK) ⊆ QK
  hc : oNorm (qR I.c) ≤ I.R
  hT : TestCert T QK (qR I.c) η
  hη0 : 0 ≤ η
  hη : η ≤ (2 : ℝ)⁻¹ ^ I.eK
  hz : ∀ x, InB z0 (1 / 2 ^ I.base.j) x → oBall x (1 / 2 ^ I.base.j) ⊆ QK ∩ regionI I.base ∧
    ∀ y ∈ QK ∩ regionI I.base, GI I.base x ≤ GI I.base y + I.base.e

theorem inB_oBall {z0 x : Fin d → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) : InB z0 ρ x ↔ oNorm (x - z0) ≤ ρ := by
  unfold InB oNorm
  rw [Real.sqrt_le_left hρ]

theorem HypO.mem {I : EllOI d} {T : (Fin d → ℚ) → Bool} {QK : Set (Fin d → ℝ)} {RK η : ℝ} {z0 : Fin d → ℝ}
    (h : HypO I T QK RK η z0) {x : Fin d → ℝ} (hx : InB z0 (1 / 2 ^ I.base.j) x) : x ∈ QK ∩ regionI I.base :=
  (h.hz x hx).1 (show oNorm (x - x) ≤ 1 / 2 ^ I.base.j by rw [sub_self, oNorm_zero]; positivity)

theorem ip_eq (j : ℕ) : (2 : ℝ)⁻¹ ^ j = 1 / 2 ^ j := by rw [inv_pow, one_div]

/-! ## One test -/

theorem box_norm (I : EllOI d) (s : ℕ) (a : Fin d → ℤ) (hR : 0 < I.R)
    (h1 : ¬ 2 ^ (2 * s) * I.R.num ^ 2 < (a ⬝ᵥ a) * (I.R.den : ℤ) ^ 2) : oNorm (vR s a) ≤ I.R := by
  replace h1 := not_lt.mp h1
  have hc : ((a ⬝ᵥ a : ℤ) : ℝ) * (I.R.den : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * s) * (I.R.num : ℝ) ^ 2 := by
    exact_mod_cast h1
  have hRr : (0 : ℝ) < I.R := by exact_mod_cast hR
  have hden : (0 : ℝ) < I.R.den := by exact_mod_cast I.R.den_pos
  have hsq : oNorm (vR s a) ^ 2 ≤ (I.R : ℝ) ^ 2 := by
    rw [oNorm_sq, Bit.ApQ.vR_eq, dotProduct_smul, smul_dotProduct, ← Bit.ApQ.dotZ_cast, Rat.cast_def]
    simp only [smul_eq_mul]
    have : (1 / 2 ^ s : ℝ) * (1 / 2 ^ s * ((a ⬝ᵥ a : ℤ) : ℝ)) = ((a ⬝ᵥ a : ℤ) : ℝ) / 2 ^ (2 * s) := by
      field_simp
      ring
    rw [this, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  exact (pow_le_pow_iff_left₀ (oNorm_nonneg _) hRr.le two_ne_zero).1 hsq

/-- Steps 3 and 4 (`ellTest` of the rowless problem, its box passing) at a centre in `QK`. -/
theorem ellTest_specQ (I : EllOI d) (QK : Set (Fin d → ℝ)) (z0 : Fin d → ℝ) (ρ : ℝ) (s : ℕ) (a : Fin d → ℤ)
    (kept : Option ((Fin d → ℤ) × ℤ)) (hR : 0 < I.R) (hP : (I.P.map ((↑) : ℤ → ℝ)).PosSemidef)
    (hH : (I.H.map ((↑) : ℤ → ℝ)).PosSemidef) (hDf : 0 < I.Df) (he : 0 ≤ I.e)
    (hk : KOK I.base (QK ∩ regionI I.base) s kept)
    (h1 : ¬ 2 ^ (2 * s) * I.R.num ^ 2 < (a ⬝ᵥ a) * (I.R.den : ℤ) ^ 2) (hK : vR s a ∈ QK)
    (hB : ∀ z, InB z0 ρ z → z ∈ QK ∩ regionI I.base ∧
      ∀ y ∈ QK ∩ regionI I.base, GI I.base z ≤ GI I.base y + I.base.e)
    (hz0 : InB z0 ρ z0) :
    TOK I.base (QK ∩ regionI I.base) z0 ρ s a kept (ellTest I.base s a kept) := by
  set Q := QK ∩ regionI I.base with hQdef
  have hR' : 0 < I.base.R := hR
  have hfind : (List.finRange I.base.m).find? (fun i => decide (2 ^ s * I.base.β i < I.base.α i ⬝ᵥ a)) = none := by
    rw [List.find?_eq_none]; intro i _; exact i.elim0
  have h1' : ¬ 2 ^ (2 * s) * I.base.R.num ^ 2 < (a ⬝ᵥ a) * (I.base.R.den : ℤ) ^ 2 := h1
  unfold ellTest
  simp only [h1', ↓reduceIte, hfind]
  have h2 : ∀ i, I.base.α i ⬝ᵥ a ≤ 2 ^ s * I.base.β i := fun i => i.elim0
  have hz0Q := (hB z0 hz0).1
  by_cases h3 : 2 ^ (2 * s + 1) * I.base.ℓ < a ⬝ᵥ (I.base.H *ᵥ a) - 2 ^ (s + 1) * (I.base.g ⬝ᵥ a)
  · simp only [h3, ↓reduceIte]
    have hs : ∀ y ∈ Q, vZ (I.base.H *ᵥ a - (2 ^ s : ℤ) • I.base.g) ⬝ᵥ (y - vR s a) < 0 :=
      fun y hy => Bit.ApQ.cut_psi I.base s a hH h3 y hy.2
    refine ⟨hk, id, fun hc => ?_, fun z hz => Or.inl (hs z (hB z hz).1).le⟩
    have := hs z0 hz0Q
    rw [hc, Bit.ApQ.vZ_zero, zero_dotProduct] at this
    exact lt_irrefl _ this
  simp only [h3, ↓reduceIte]
  have hin : vR s a ∈ regionI I.base := Bit.ApQ.test_in I.base s a hR' h1' h2 h3
  have hinQ : vR s a ∈ Q := ⟨hK, hin⟩
  have hV := Bit.ApQ.V_eq I.base s a hDf
  have hok := updK_okQ I.base Q s a (VI I.base s a) kept hk hinQ hV
  show TOK I.base Q z0 ρ s a kept
    (if ghI I.base s a = 0 then .ret a else .cut (ghI I.base s a) (updK a (VI I.base s a) kept))
  have hcpos : (0 : ℝ) < 2 ^ s * I.base.Df := mul_pos (by positivity) (by exact_mod_cast hDf)
  split_ifs with hg
  · show GoodQ I.base Q s a
    refine ⟨hinQ, fun y _ => ?_⟩
    have hgg : gG I.base (vR s a) = 0 := by
      have := Bit.ApQ.gh_eq I.base s a hDf
      rw [hg, Bit.ApQ.vZ_zero] at this
      exact (smul_eq_zero.mp this.symm).resolve_left hcpos.ne'
    have h := Bit.ApQ.GI_conv I.base hP (vR s a) y
    rw [hgg, zero_dotProduct, add_zero] at h
    have : (0 : ℝ) ≤ I.base.e := by exact_mod_cast he
    linarith
  · refine ⟨hok, updK_monoQ I.base Q s a _ kept hDf hk hinQ hV, hg, ?_⟩
    intro z hz
    by_cases hcut : vZ (ghI I.base s a) ⬝ᵥ (z - vR s a) ≤ 0
    · exact Or.inl hcut
    · right
      apply updK_goodQ I.base Q s a _ kept hDf hk hV
      refine ⟨hinQ, fun y hy => ?_⟩
      rw [Bit.ApQ.gh_eq I.base s a hDf, smul_dotProduct, smul_eq_mul] at hcut
      have hpos := pos_of_mul_pos_right (lt_of_not_ge hcut) hcpos.le
      have h := Bit.ApQ.GI_conv I.base hP (vR s a) z
      have := (hB z hz).2 y hy
      linarith

/-- **One test of ELL-O** (steps 1 to 4) keeps `TOK` on the ball `B'`. -/
theorem ellTestO_spec {I : EllOI d} {T : (Fin d → ℚ) → Bool} {QK : Set (Fin d → ℝ)} {RK η : ℝ}
    {z0 : Fin d → ℝ} (h : HypO I T QK RK η z0) (s : ℕ) (a : Fin d → ℤ) (kept : Option ((Fin d → ℤ) × ℤ))
    (hk : KOK I.base (QK ∩ regionI I.base) s kept) :
    TOK I.base (QK ∩ regionI I.base) z0 (1 / 2 ^ I.base.j) s a kept (ellTestO I T s a kept) := by
  set Q := QK ∩ regionI I.base with hQdef
  have hR0 : 0 < I.R := lt_of_lt_of_le one_pos h.hR
  have hρ : (0 : ℝ) ≤ 1 / 2 ^ I.base.j := by positivity
  have hz0 : InB z0 (1 / 2 ^ I.base.j) z0 := Bit.ApQ.inB_self z0 _
  have hz0Q := h.mem hz0
  unfold ellTestO
  by_cases h1 : 2 ^ (2 * s) * I.R.num ^ 2 < (a ⬝ᵥ a) * (I.R.den : ℤ) ^ 2
  · simp only [h1, ↓reduceIte]
    have hs : ∀ y ∈ Q, vZ a ⬝ᵥ (y - vR s a) < 0 := fun y hy => Bit.ApQ.cut_out I.base s a hR0 h1 y hy.2
    refine ⟨hk, id, fun hc => ?_, fun z hz => Or.inl (hs z (h.mem hz)).le⟩
    have := hs z0 hz0Q
    rw [hc, Bit.ApQ.vZ_zero, zero_dotProduct] at this
    exact lt_irrefl _ this
  simp only [h1, ↓reduceIte]
  by_cases hT : T (ptDN (2 ^ s) a) = true
  · simp only [hT, ↓reduceIte]
    have hK : vR s a ∈ QK := by
      have := (h.hT (ptDN (2 ^ s) a)).1 hT
      rwa [qR_ptDN_pow] at this
    exact ellTest_specQ I QK z0 _ s a kept hR0 h.hP h.hH h.hDf h.he.le hk h1 hK
      (fun z hz => ⟨h.mem hz, (h.hz z hz).2⟩) hz0
  · have hrej : T (ptDN (2 ^ s) a) = false := by simpa using hT
    simp only [hrej, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨Y, G, hsep, hG, hcut⟩ := sep_branch h.hSA h.hGA I T QK RK η s a h.hd h.hR h.hQ h.hcl h.hQR h.hball
      h.hc h.hT h.hη0 h.hη (box_norm I s a hR0 h1) hrej
    rw [hsep]
    refine ⟨hk, id, hG, fun z hz => Or.inl (hcut z ?_ ?_).le⟩
    · rw [ip_eq]; exact fun x hx => ((h.hz z hz).1 hx).1
    · exact (h.mem hz).2.2.2

/-! ## ELL-O: the iterations -/

/-- The claim `I_k` of ELL-R on `Q`. -/
def EInvO (I : EllOI d) (Q : Set (Fin d → ℝ)) (z0 : Fin d → ℝ) (k : ℕ) (st : ESt d) : Prop :=
  KOK I.base Q I.base.p st.kept ∧ (KGood I.base Q I.base.p st.kept ∨
    (st.Aᵀ = st.A ∧ (mR I.base.p st.A).PosDef ∧
      (∀ x, InB z0 (1 / 2 ^ I.base.j) x → InE (mR I.base.p st.A) (vR I.base.p st.a) x) ∧
      (∀ v, v ⬝ᵥ (mR I.base.p st.A *ᵥ v) ≤ (I.base.Rb : ℝ) ^ 2 * gam d ^ k * (v ⬝ᵥ v)) ∧
      (mR I.base.p st.A).det ≤ (I.base.Rb : ℝ) ^ (2 * d) * Real.exp (-(95 / (128 * ((d : ℝ) + 1))) * k)))

theorem ellLoopO_main {I : EllOI d} {T : (Fin d → ℚ) → Bool} {QK : Set (Fin d → ℝ)} {RK η : ℝ}
    {z0 : Fin d → ℝ} (h : HypO I T QK RK η z0) (hd : 2 ≤ d) :
    ∀ n k (st : ESt d), k + n = I.base.N → EInvO I (QK ∩ regionI I.base) z0 k st →
      ∃ x, ellLoopO I T n st = some x ∧ GoodQ I.base (QK ∩ regionI I.base) I.base.p x := by
  set Q := QK ∩ regionI I.base with hQdef
  have hd1 : 1 ≤ d := by omega
  have hRb := h.hR
  have hρ : (0 : ℝ) < 1 / 2 ^ I.base.j := by positivity
  have hz0 := Bit.ApQ.inB_self z0 (1 / 2 ^ I.base.j)
  have hRb1 : (1 : ℝ) ≤ I.base.Rb := by exact_mod_cast (Bit.ApQ.Rb_spec I.base h.hR).1
  intro n
  induction n with
  | zero =>
    intro k st hk hinv
    obtain ⟨_, hg | ⟨_, hpd, hb, _, hdet⟩⟩ := hinv
    · exact keptGood_mapQ I.base Q _ _ hg
    · exfalso
      have hq := Bit.pb_ball_quad (mR I.base.p st.A) hpd (vR I.base.p st.a) _ hρ
        (Bit.pb_ball_sym (mR I.base.p st.A) hpd (vR I.base.p st.a) z0 _ (fun x hx => hb x hx))
      have hdet0 := Bit.pb_ball_det (mR I.base.p st.A) hpd _ hρ.le hq
      have hk' : k = I.base.N := by omega
      have hcontra := Bit.pb_ell_det_contra d I.base.lam hd1 I.base.Rb (1 / 2 ^ I.base.j) _ hρ (by linarith)
        (by rw [div_le_iff₀ hρ]; exact Bit.ApQ.Rb_rho I.base)
        (hdet.trans (le_of_eq (by rw [hk', Bit.ApQ.N_cast I.base, neg_mul])))
      linarith
  | succ n ih =>
    intro k st hk hinv
    have htest := ellTestO_spec h I.base.p st.a st.kept hinv.1
    rw [ellLoopO.eq_2]
    rcases hT : ellTestO I T I.base.p st.a st.kept with x | ⟨c, kept'⟩
    · rw [hT] at htest
      exact ⟨x, rfl, htest⟩
    · rw [hT] at htest
      obtain ⟨hok', hmono, hc, hside⟩ := htest
      simp only []
      by_cases hkg : KGood I.base Q I.base.p kept'
      · split_ifs with hc0
        · exact keptGood_mapQ I.base Q _ _ hkg
        · rcases hU : ellUpd I.base.p I.base.q I.base.j ((2 : ℤ) ^ I.base.p * I.base.Lam)
              ((2 : ℤ) ^ I.base.p * (I.base.Rb + I.base.LamH)) st.A st.a c with _ | ⟨A', a'⟩
          · exact keptGood_mapQ I.base Q _ _ hkg
          · exact ih (k + 1) ⟨A', a', kept'⟩ (by omega) ⟨hok', Or.inl hkg⟩
      · obtain ⟨_, hg | ⟨hs, hpd, hb, hl, hdet⟩⟩ := hinv
        · exact absurd (hmono hg) hkg
        have hcut : ∀ x, InB z0 (1 / 2 ^ I.base.j) x → vZ c ⬝ᵥ (x - vR I.base.p st.a) ≤ 0 := fun x hx =>
          (hside x hx).resolve_right hkg
        have hkN : k + 1 ≤ I.base.N := by omega
        obtain ⟨hq1, hq2⟩ := Bit.ApQ.q_prec I.base hd1 (Bit.ApQ.Rb_spec I.base h.hR).1
        obtain ⟨A', a', hU, hs', hpd', hb', hl', hdet'⟩ := Bit.ApQ.ellUpd_step hd I.base.p I.base.q I.base.j
          ((2 : ℤ) ^ I.base.p * I.base.Lam) ((2 : ℤ) ^ I.base.p * (I.base.Rb + I.base.LamH)) st.A st.a c z0
          ((I.base.Rb : ℝ) ^ 2 * gam d ^ k) (I.base.Lam : ℝ) hs hpd hb hl
          (by
            have := Bit.ApQ.cap_gam I.base hd (k + 1) hkN
            calc gam d * ((I.base.Rb : ℝ) ^ 2 * gam d ^ k) = (I.base.Rb : ℝ) ^ 2 * gam d ^ (k + 1) := by ring
              _ ≤ (I.base.Lam : ℝ) := this)
          hc hcut (Bit.ApQ.two_j_le_p I.base) (Bit.ApQ.p_prec I.base hd1) hq1 hq2 (le_of_eq (by push_cast; ring))
          (by
            intro i
            have hz0R : |z0 i| ≤ I.base.Rb :=
              (abs_apply_le_oNorm z0 i).trans (Bit.ApQ.mem_region_norm I.base h.hR (h.mem hz0).2)
            rw [Bit.ApQ.sqrt_Lam I.base]
            push_cast
            exact mul_le_mul_of_nonneg_left (by linarith) (by positivity))
        simp only [hc, ↓reduceIte]
        rw [hU]
        refine ih (k + 1) ⟨A', a', kept'⟩ (by omega) ⟨hok', Or.inr ⟨hs', hpd', hb', fun v => ?_, ?_⟩⟩
        · calc v ⬝ᵥ (mR I.base.p A' *ᵥ v) ≤ gam d * ((I.base.Rb : ℝ) ^ 2 * gam d ^ k) * (v ⬝ᵥ v) := hl' v
            _ = (I.base.Rb : ℝ) ^ 2 * gam d ^ (k + 1) * (v ⬝ᵥ v) := by ring
        · calc (mR I.base.p A').det ≤ Real.exp (-(95 / (128 * ((d : ℝ) + 1)))) * (mR I.base.p st.A).det := hdet'
            _ ≤ Real.exp (-(95 / (128 * ((d : ℝ) + 1)))) *
                ((I.base.Rb : ℝ) ^ (2 * d) * Real.exp (-(95 / (128 * ((d : ℝ) + 1))) * k)) :=
                mul_le_mul_of_nonneg_left hdet (Real.exp_pos _).le
            _ = _ := Bit.ApQ.exp_step _ _ k

theorem ellO_spec {I : EllOI d} {T : (Fin d → ℚ) → Bool} {QK : Set (Fin d → ℝ)} {RK η : ℝ}
    {z0 : Fin d → ℝ} (h : HypO I T QK RK η z0) (hd : 2 ≤ d) :
    ∃ x, ellO I T = some x ∧ GoodQ I.base (QK ∩ regionI I.base) I.base.p x := by
  have hRb1 : (1 : ℝ) ≤ I.base.Rb := by exact_mod_cast (Bit.ApQ.Rb_spec I.base h.hR).1
  have hRb2 : (0 : ℝ) < (I.base.Rb : ℝ) ^ 2 := by positivity
  apply ellLoopO_main h hd I.base.N 0 _ (by omega)
  refine ⟨fun b W hbW => by simp at hbW, Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · show ((((2 : ℤ) ^ I.base.p * (I.base.Rb : ℤ) ^ 2) • (1 : Matrix (Fin d) (Fin d) ℤ)))ᵀ = _
    rw [Matrix.transpose_smul, Matrix.transpose_one]
  · rw [Bit.ApQ.start_mR]
    exact Matrix.PosDef.one.smul hRb2
  · intro x hx
    show InE (mR I.base.p (((2 : ℤ) ^ I.base.p * (I.base.Rb : ℤ) ^ 2) • (1 : Matrix (Fin d) (Fin d) ℤ)))
      (vR I.base.p 0) x
    rw [Bit.ApQ.start_mR, Bit.ApQ.inE_scalar _ hRb2]
    have : vR I.base.p (0 : Fin d → ℤ) = 0 := by funext i; simp [vR]
    rw [this, sub_zero, ← oNorm_sq]
    exact pow_le_pow_left₀ (oNorm_nonneg _) (Bit.ApQ.mem_region_norm I.base h.hR (h.mem hx).2) 2
  · intro v
    show v ⬝ᵥ (mR I.base.p (((2 : ℤ) ^ I.base.p * (I.base.Rb : ℤ) ^ 2) • (1 : Matrix (Fin d) (Fin d) ℤ)) *ᵥ v) ≤ _
    rw [Bit.ApQ.start_mR, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    simp
  · show (mR I.base.p (((2 : ℤ) ^ I.base.p * (I.base.Rb : ℤ) ^ 2) • (1 : Matrix (Fin d) (Fin d) ℤ))).det ≤ _
    rw [Bit.ApQ.start_mR, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, ← pow_mul]
    simp

/-! ## BIS-O: the halvings (`d = 1`) -/

/-- The claim of BIS-O with `n` halvings left. -/
def BInvO (I : EllOI 1) (Q : Set (Fin 1 → ℝ)) (z0 : Fin 1 → ℝ) (n : ℕ) (lo hi : ℤ)
    (kept : Option ((Fin 1 → ℤ) × ℤ)) : Prop :=
  KOK I.base Q (I.base.lam + 1) kept ∧ (KGood I.base Q (I.base.lam + 1) kept ∨
    (hi - lo = 2 * I.base.Rb * 2 ^ n ∧ ∀ x, InB z0 (1 / 2 ^ I.base.j) x →
      (lo : ℝ) / 2 ^ (I.base.lam + 1) ≤ x 0 ∧ x 0 ≤ (hi : ℝ) / 2 ^ (I.base.lam + 1)))

theorem bisLoopO_main {I : EllOI 1} {T : (Fin 1 → ℚ) → Bool} {QK : Set (Fin 1 → ℝ)} {RK η : ℝ}
    {z0 : Fin 1 → ℝ} (h : HypO I T QK RK η z0) :
    ∀ n lo hi kept, BInvO I (QK ∩ regionI I.base) z0 n lo hi kept →
      ∃ x, bisLoopO I T n lo hi kept = some x ∧ GoodQ I.base (QK ∩ regionI I.base) (I.base.lam + 1) x := by
  set Q := QK ∩ regionI I.base with hQdef
  have hρ : (0 : ℝ) < 1 / 2 ^ I.base.j := by positivity
  intro n
  induction n with
  | zero =>
    intro lo hi kept hinv
    obtain ⟨_, hg | ⟨hw, hB⟩⟩ := hinv
    · exact keptGood_mapQ I.base Q _ _ hg
    · exfalso
      exact Bit.ApQ.bis_contra z0 _ hρ lo hi (I.base.lam + 1) I.base.Rb (by simpa using hw)
        (by simpa using Bit.ApQ.Rb_rho I.base) (by omega) hB
  | succ n ih =>
    intro lo hi kept hinv
    have htest := ellTestO_spec h (I.base.lam + 1) (fun _ => (lo + hi) / 2) kept hinv.1
    simp only [bisLoopO.eq_2]
    rcases hT : ellTestO I T (I.base.lam + 1) (fun _ => (lo + hi) / 2) kept with x | ⟨c, kept'⟩
    · rw [hT] at htest
      exact ⟨x, rfl, htest⟩
    · rw [hT] at htest
      obtain ⟨hok', hmono, hc, hside⟩ := htest
      simp only []
      by_cases hkg : KGood I.base Q (I.base.lam + 1) kept'
      · split_ifs with hc0 hpos
        · exact keptGood_mapQ I.base Q _ _ hkg
        · exact ih _ _ _ ⟨hok', Or.inl hkg⟩
        · exact ih _ _ _ ⟨hok', Or.inl hkg⟩
      · obtain ⟨_, hg | ⟨hw, hB⟩⟩ := hinv
        · exact absurd (hmono hg) hkg
        have hcut : ∀ x, InB z0 (1 / 2 ^ I.base.j) x →
            (c 0 : ℝ) * (x 0 - (((lo + hi) / 2 : ℤ) : ℝ) / 2 ^ (I.base.lam + 1)) ≤ 0 := fun x hx => by
          have := (hside x hx).resolve_right hkg
          rwa [Bit.ApQ.dot_fin_one] at this
        obtain ⟨hm1, hm2⟩ := Bit.ApQ.bis_mid lo hi I.base.Rb n hw
        have hsum : ∑ i, c i = c 0 := Fin.sum_univ_one c
        simp only [hc, ↓reduceIte]
        rw [hsum]
        split_ifs with hpos
        · refine ih _ _ _ ⟨hok', Or.inr ⟨hm1, fun x hx => ⟨(hB x hx).1, ?_⟩⟩⟩
          have h1 := hcut x hx
          have hc0' : (0 : ℝ) < c 0 := by exact_mod_cast hpos
          by_contra hcon
          replace hcon := lt_of_not_ge hcon
          have := mul_pos hc0' (sub_pos.mpr hcon)
          linarith
        · have hcneg : c 0 < 0 := by
            rcases lt_trichotomy (c 0) 0 with h' | h' | h'
            · exact h'
            · exfalso
              apply hc
              funext i
              rw [Subsingleton.elim i 0]
              exact h'
            · exact absurd h' hpos
          refine ih _ _ _ ⟨hok', Or.inr ⟨hm2, fun x hx => ⟨?_, (hB x hx).2⟩⟩⟩
          have h1 := hcut x hx
          have hc0' : (c 0 : ℝ) < 0 := by exact_mod_cast hcneg
          by_contra hcon
          replace hcon := lt_of_not_ge hcon
          have := mul_pos_of_neg_of_neg hc0' (sub_neg.mpr hcon)
          linarith

theorem bisO_spec {I : EllOI 1} {T : (Fin 1 → ℚ) → Bool} {QK : Set (Fin 1 → ℝ)} {RK η : ℝ}
    {z0 : Fin 1 → ℝ} (h : HypO I T QK RK η z0) :
    ∃ x, bisO I T = some x ∧ GoodQ I.base (QK ∩ regionI I.base) (I.base.lam + 1) x := by
  apply bisLoopO_main h
  refine ⟨fun b W hbW => by simp at hbW, Or.inr ⟨by ring, fun x hx => ?_⟩⟩
  have hxR := Bit.ApQ.mem_region_norm I.base h.hR (h.mem hx).2
  have h0 := (abs_apply_le_oNorm x 0).trans hxR
  rw [abs_le] at h0
  have e1 : ((-((I.base.Rb : ℤ) * 2 ^ (I.base.lam + 1)) : ℤ) : ℝ) / 2 ^ (I.base.lam + 1) = -(I.base.Rb : ℝ) := by
    push_cast; field_simp
  have e2 : (((I.base.Rb : ℤ) * 2 ^ (I.base.lam + 1) : ℤ) : ℝ) / 2 ^ (I.base.lam + 1) = (I.base.Rb : ℝ) := by
    push_cast; field_simp
  rw [e1, e2]
  exact h0

/-! ## The ball `B'` -/

/-- `B' = B̄(p_θ, ρ)`, `p_θ = (1 - θ) p* + θ a₀`, `ρ = 2^{-j} ≤ θ min(r, 1)`: every point of `B'` has its
`ρ`-neighbourhood in `Q = QK ∩ region` and lies within `e` of the minimum of `G` on `Q`. -/
theorem ball_existsO (I : EllOI d) (QK : Set (Fin d → ℝ)) (a0 : Fin d → ℝ) (hR : 1 ≤ I.R) (hr : 0 < I.r)
    (hQ : Convex ℝ QK) (hcl : IsClosed QK) (hball : oBall a0 (2 * (I.r : ℝ)) ⊆ QK ∩ regionI I.base)
    (hP : (I.P.map ((↑) : ℤ → ℝ)).PosSemidef) (hH : (I.H.map ((↑) : ℤ → ℝ)).PosSemidef) (he : 0 < I.e)
    (hDf : 0 < I.Df) :
    ∃ z0 : Fin d → ℝ, ∀ x, InB z0 (1 / 2 ^ I.base.j) x → oBall x (1 / 2 ^ I.base.j) ⊆ QK ∩ regionI I.base ∧
      ∀ y ∈ QK ∩ regionI I.base, GI I.base x ≤ GI I.base y + I.base.e := by
  set Q := QK ∩ regionI I.base with hQdef
  have hQc : Convex ℝ Q := hQ.inter (Bit.ApQ.region_convex I.base hH)
  have hQk : IsCompact Q := (Bit.ApQ.region_compact I.base).inter_left hcl
  have hr' : 0 < I.base.r := hr
  have ha0 : a0 ∈ Q := hball (show oNorm (a0 - a0) ≤ 2 * (I.r : ℝ) by
    rw [sub_self, oNorm_zero]; have : (0 : ℝ) < I.r := by exact_mod_cast hr
    linarith)
  have hc : Continuous (GI I.base) := by unfold GI; fun_prop
  obtain ⟨ps, hps, hmin⟩ := hQk.exists_isMinOn ⟨a0, ha0⟩ hc.continuousOn
  have hmin' : ∀ y ∈ Q, GI I.base ps ≤ GI I.base y := fun y hy => isMinOn_iff.mp hmin y hy
  obtain ⟨hθ0, hθ1, hθe⟩ := Bit.ApQ.theta_spec I.base he
  have hρ := Bit.ApQ.rho_le I.base he hr'
  set θ : ℝ := (I.base.θ : ℝ) with hθdef
  set ρ : ℝ := 1 / 2 ^ I.base.j with hρdef
  have hθ0' : (0 : ℝ) < θ := by rw [hθdef]; exact_mod_cast hθ0
  have hθ1' : θ ≤ 1 := by rw [hθdef]; exact_mod_cast hθ1
  have hρ0 : 0 < ρ := by positivity
  have hρ' : ρ ≤ θ * min (I.r : ℝ) 1 := by
    have := (Rat.cast_le (K := ℝ)).mpr hρ
    push_cast at this
    exact this
  have h2ρ : 2 * ρ ≤ θ * (2 * (I.r : ℝ)) := by
    have : min (I.r : ℝ) 1 ≤ (I.r : ℝ) := min_le_left _ _
    nlinarith
  have hρθ : ρ ≤ θ := by
    have : min (I.r : ℝ) 1 ≤ 1 := min_le_right _ _
    nlinarith
  have hθe' : 3 * θ * (I.base.LG : ℝ) * I.base.Rb ≤ I.base.e := by
    have := (Rat.cast_le (K := ℝ)).mpr hθe
    push_cast at this
    exact this
  have hLG : (0 : ℝ) ≤ I.base.LG := by exact_mod_cast Bit.ApQ.LG_nonneg I.base hP
  have hRb1 : (1 : ℝ) ≤ I.base.Rb := by exact_mod_cast (Bit.ApQ.Rb_spec I.base hR).1
  set z0 := (1 - θ) • ps + θ • a0 with hz0
  -- `B̄(z₀, 2ρ) ⊆ Q`
  have hin2 : ∀ x, oNorm (x - z0) ≤ 2 * ρ → x ∈ Q := by
    intro x hxz
    set w := a0 + θ⁻¹ • (x - z0) with hw
    have hwr : w ∈ Q := by
      apply hball
      show oNorm (w - a0) ≤ 2 * (I.r : ℝ)
      have hwa : w - a0 = θ⁻¹ • (x - z0) := by rw [hw]; abel
      rw [hwa, oNorm_smul, abs_of_pos (inv_pos.mpr hθ0')]
      calc θ⁻¹ * oNorm (x - z0) ≤ θ⁻¹ * (θ * (2 * (I.r : ℝ))) :=
            mul_le_mul_of_nonneg_left (hxz.trans h2ρ) (inv_pos.mpr hθ0').le
        _ = 2 * (I.r : ℝ) := by field_simp
    have hxeq : x = (1 - θ) • ps + θ • w := by
      rw [hw, smul_add, smul_smul, mul_inv_cancel₀ hθ0'.ne', one_smul, hz0]
      abel
    rw [hxeq]
    exact hQc hps hwr (by linarith) hθ0'.le (by ring)
  refine ⟨z0, fun x hx => ⟨fun y hy => hin2 y ?_, fun y hy => ?_⟩⟩
  · have hxz : oNorm (x - z0) ≤ ρ := (inB_oBall hρ0.le).mp hx
    have hyx : oNorm (y - x) ≤ ρ := hy
    calc oNorm (y - z0) ≤ oNorm (y - x) + oNorm (x - z0) := oNorm_sub_sub_le _ _ _
      _ ≤ 2 * ρ := by linarith
  · have hxz : oNorm (x - z0) ≤ ρ := (inB_oBall hρ0.le).mp hx
    have hxQ : x ∈ Q := hin2 x (by linarith)
    have hconv := Bit.ApQ.GI_conv I.base hP x ps
    have hxR := Bit.ApQ.mem_region_norm I.base hR hxQ.2
    have hlip := Bit.ApQ.grad_lip I.base hP hDf x (x - ps) hxR
    have hneg : gG I.base x ⬝ᵥ (ps - x) = -(gG I.base x ⬝ᵥ (x - ps)) := by
      rw [← dotProduct_neg, neg_sub]
    have hd1 : x - ps = θ • (a0 - ps) + (x - z0) := by
      rw [hz0, smul_sub, sub_smul, one_smul]
      abel
    have hnorm : oNorm (x - ps) ≤ 3 * θ * I.base.Rb := by
      rw [hd1]
      have h1 : oNorm (θ • (a0 - ps)) ≤ θ * (2 * I.base.Rb) := by
        rw [oNorm_smul, abs_of_pos hθ0']
        apply mul_le_mul_of_nonneg_left _ hθ0'.le
        have := oNorm_sub_le a0 ps
        have := Bit.ApQ.mem_region_norm I.base hR ha0.2
        have := Bit.ApQ.mem_region_norm I.base hR hps.2
        linarith
      have h3 := oNorm_add_le (θ • (a0 - ps)) (x - z0)
      have h4 : θ ≤ θ * I.base.Rb := le_mul_of_one_le_right hθ0'.le hRb1
      linarith
    have h5 : (I.base.LG : ℝ) * oNorm (x - ps) ≤ I.base.LG * (3 * θ * I.base.Rb) :=
      mul_le_mul_of_nonneg_left hnorm hLG
    have h6 : (I.base.LG : ℝ) * (3 * θ * I.base.Rb) = 3 * θ * I.base.LG * I.base.Rb := by ring
    have h7 := hmin' y hy
    linarith

/-! ## Statement (b) -/

/-- **Statement (b)** of ELL-O and BIS-O, from Lemma SEP on the grid and the accuracy of the bisection gauge. -/
theorem ellOAcc_of (hSA : SepAcc) (hGA : GaugeAcc) : EllOAcc := by
  intro d I T QK RK η a0 hd hR hr he hDf hP hH hQ hcl hQR hball hc hT hη0 hη hB
  rw [regionO_eq] at hB ⊢
  obtain ⟨z0, hz⟩ := ball_existsO I QK a0 hR hr hQ hcl hB hP.posSemidef hH he hDf
  have h : HypO I T QK RK η z0 :=
    ⟨hSA, hGA, hd, hR, hP.posSemidef, hH, hDf, he, hQ, hcl, hQR, hball, hc, hT, hη0, hη, hz⟩
  have hgate : ¬ (I.R < 1 ∨ I.r ≤ 0 ∨ I.e ≤ 0) := by
    simp only [not_or, not_lt, not_le]
    exact ⟨hR, hr, he⟩
  unfold ellOI
  simp only [hgate, ↓reduceIte, show d ≠ 0 by omega]
  rcases Nat.lt_or_ge d 2 with hd2 | hd2
  · obtain rfl : d = 1 := by omega
    simp only [↓reduceIte]
    have hexp : ellExpO I = I.base.lam + 1 := by simp [ellExpO]
    obtain ⟨x, hx, hg⟩ := bisO_spec h
    exact ⟨x, hx, by rw [hexp]; exact hg.1, by rw [hexp]; exact hg.2⟩
  · have h1 : d ≠ 1 := by omega
    simp only [h1, ↓reduceIte]
    have hexp : ellExpO I = I.base.p := by simp [ellExpO, h1]
    obtain ⟨x, hx, hg⟩ := ellO_spec h hd2
    exact ⟨x, hx, by rw [hexp]; exact hg.1, by rw [hexp]; exact hg.2⟩

/-! ## Statement (a) -/

/-- The kept point passed the test `T` and lies in the exact part of the region. -/
def KCert (I : EllOI d) (T : (Fin d → ℚ) → Bool) (s : ℕ) (kept : Option ((Fin d → ℤ) × ℤ)) : Prop :=
  ∀ b W, kept = some (b, W) → T (ptDN (2 ^ s) b) = true ∧ vR s b ∈ regionI I.base

/-- The outcome of a test keeps the certificate: a returned point is certified, a cut carries a certified kept
point. -/
def CCert (I : EllOI d) (T : (Fin d → ℚ) → Bool) (s : ℕ) : Cut d → Prop
  | .ret x => T (ptDN (2 ^ s) x) = true ∧ vR s x ∈ regionI I.base
  | .cut _ k => KCert I T s k

theorem kcert_map (I : EllOI d) (T : (Fin d → ℚ) → Bool) (s : ℕ) (kept : Option ((Fin d → ℤ) × ℤ))
    (h : KCert I T s kept) (x : Fin d → ℤ) (hx : kept.map Prod.fst = some x) :
    T (ptDN (2 ^ s) x) = true ∧ vR s x ∈ regionI I.base := by
  rcases kept with _ | ⟨b, W⟩
  · cases hx
  · simp only [Option.map_some, Option.some.injEq] at hx
    subst hx
    exact h b W rfl

theorem ellTestO_cert (I : EllOI d) (T : (Fin d → ℚ) → Bool) (s : ℕ) (a : Fin d → ℤ)
    (kept : Option ((Fin d → ℤ) × ℤ)) (hR : 0 < I.R) (hk : KCert I T s kept) : CCert I T s (ellTestO I T s a kept) := by
  unfold ellTestO
  by_cases h1 : 2 ^ (2 * s) * I.R.num ^ 2 < (a ⬝ᵥ a) * (I.R.den : ℤ) ^ 2
  · simp only [h1, ↓reduceIte]; exact hk
  simp only [h1, ↓reduceIte]
  by_cases hT : T (ptDN (2 ^ s) a) = true
  · simp only [hT, ↓reduceIte]
    have hfind : (List.finRange I.base.m).find? (fun i => decide (2 ^ s * I.base.β i < I.base.α i ⬝ᵥ a)) = none := by
      rw [List.find?_eq_none]; intro i _; exact i.elim0
    have h1' : ¬ 2 ^ (2 * s) * I.base.R.num ^ 2 < (a ⬝ᵥ a) * (I.base.R.den : ℤ) ^ 2 := h1
    unfold ellTest
    simp only [h1', ↓reduceIte, hfind]
    by_cases h3 : 2 ^ (2 * s + 1) * I.base.ℓ < a ⬝ᵥ (I.base.H *ᵥ a) - 2 ^ (s + 1) * (I.base.g ⬝ᵥ a)
    · simp only [h3, ↓reduceIte]; exact hk
    simp only [h3, ↓reduceIte]
    have hin : vR s a ∈ regionI I.base := Bit.ApQ.test_in I.base s a hR h1' (fun i => i.elim0) h3
    show CCert I T s (if ghI I.base s a = 0 then .ret a else .cut (ghI I.base s a) (updK a (VI I.base s a) kept))
    split_ifs
    · exact ⟨hT, hin⟩
    · intro b W hb
      rcases kept with _ | ⟨b0, W0⟩
      · simp only [updK, Option.some.injEq, Prod.mk.injEq] at hb
        rw [← hb.1]; exact ⟨hT, hin⟩
      · simp only [updK] at hb
        split_ifs at hb
        · simp only [Option.some.injEq, Prod.mk.injEq] at hb
          rw [← hb.1]; exact ⟨hT, hin⟩
        · simp only [Option.some.injEq, Prod.mk.injEq] at hb
          rw [← hb.1]; exact hk b0 W0 rfl
  · have hrej : T (ptDN (2 ^ s) a) = false := by simpa using hT
    simp only [hrej, Bool.false_eq_true, ↓reduceIte]
    split <;> exact hk

theorem ellLoopO_cert (I : EllOI d) (T : (Fin d → ℚ) → Bool) (hR : 0 < I.R) (k : ℕ) (st : ESt d)
    (hk : KCert I T I.base.p st.kept) (x : Fin d → ℤ) (hx : ellLoopO I T k st = some x) :
    T (ptDN (2 ^ I.base.p) x) = true ∧ vR I.base.p x ∈ regionI I.base := by
  induction k generalizing st with
  | zero => exact kcert_map I T _ _ hk x hx
  | succ k ih =>
    have ht := ellTestO_cert I T I.base.p st.a st.kept hR hk
    simp only [ellLoopO] at hx
    cases hc : ellTestO I T I.base.p st.a st.kept with
    | ret x0 =>
      simp only [hc, Option.some.injEq] at hx
      rw [hc] at ht
      subst hx; exact ht
    | cut c kept' =>
      simp only [hc] at hx
      rw [hc] at ht
      split_ifs at hx
      · exact kcert_map I T _ _ ht x hx
      · split at hx
        · exact kcert_map I T _ _ ht x hx
        · exact ih ⟨_, _, kept'⟩ ht hx

theorem bisLoopO_cert (I : EllOI d) (T : (Fin d → ℚ) → Bool) (hR : 0 < I.R) (k : ℕ) (lo hi : ℤ)
    (kept : Option ((Fin d → ℤ) × ℤ)) (hk : KCert I T (I.base.lam + 1) kept) (x : Fin d → ℤ)
    (hx : bisLoopO I T k lo hi kept = some x) :
    T (ptDN (2 ^ (I.base.lam + 1)) x) = true ∧ vR (I.base.lam + 1) x ∈ regionI I.base := by
  induction k generalizing lo hi kept with
  | zero => exact kcert_map I T _ _ hk x hx
  | succ k ih =>
    have ht := ellTestO_cert I T (I.base.lam + 1) (fun _ => (lo + hi) / 2) kept hR hk
    simp only [bisLoopO] at hx
    cases hc : ellTestO I T (I.base.lam + 1) (fun _ => (lo + hi) / 2) kept with
    | ret x0 =>
      simp only [hc, Option.some.injEq] at hx
      rw [hc] at ht
      subst hx; exact ht
    | cut c kept' =>
      simp only [hc] at hx
      rw [hc] at ht
      split_ifs at hx
      · exact kcert_map I T _ _ ht x hx
      · exact ih _ _ kept' ht hx
      · exact ih _ _ kept' ht hx

/-- **Statement (a)** of ELL-O and BIS-O: a point returned passed the test `T`, the quadratic test and the ball
test. -/
theorem ellOCert : EllOCert := by
  intro d I T x h
  unfold ellOI at h
  split_ifs at h with h0 hd0 hd1
  · have hR : 0 < I.R := by
      simp only [not_or, not_lt, not_le] at h0
      exact lt_of_lt_of_le one_pos h0.1
    have hE : ellExpO I = I.base.lam + 1 := by simp [ellExpO, hd1]
    rw [hE, regionO_eq]
    exact bisLoopO_cert I T hR _ _ _ none (fun b W hb => by cases hb) x h
  · have hR : 0 < I.R := by
      simp only [not_or, not_lt, not_le] at h0
      exact lt_of_lt_of_le one_pos h0.1
    have hE : ellExpO I = I.base.p := by simp [ellExpO, hd1]
    rw [hE, regionO_eq]
    exact ellLoopO_cert I T hR _ _ (fun b W hb => by cases hb) x h

end AdversarialBco.Uni.EllO
