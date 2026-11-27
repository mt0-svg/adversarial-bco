/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EngC2b

@[expose] public section

/-!
# Piece C for BL-O, part C2 (c): E13, Lemma SEL and P°'s test call

Bit/BLRoundC2.lean (E13, E15) for BL-O at `k`: BL-O's test statistic `Xi'` against P°'s `Xi°` on `B_R`, Lemma SEL at
BL-O's test point (its call through `apSpecO` on `regO`), and P°'s test call under the advice `advC` (the checked
routine accepts `selV(p', β)` at `e_T = 1`).
-/

namespace AdversarialBco.Unified.EngC

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Unified.BLO AdversarialBco.Unified.Eng AdversarialBco.Unified.Asm
open AdversarialBco.Bit.BLP (Par St Mode init rnd sqrtDn rndM rndV frob2 cV cM opN LT Lmu rB eBL CallQ)
open AdversarialBco.Bit.BLP.RC
open Matrix

variable {d : ℕ}

/-! ## E13: BL's test statistic against P°'s -/

/-- BL's test statistic `Xi'(y) = η'(l' - G'·y) - 2 Φ'(y)` read in `ℝ`. -/
noncomputable def xiBO (c : CfgO d) (r : RV d) (y : Fin d → ℝ) : ℝ :=
  (c.par.eta : ℝ) * ((r.l : ℝ) - cV r.G ⬝ᵥ y) - 2 * df2Phi (cM r.B * (cM r.B)ᵀ) (cV r.b) r.k y

theorem fireO_iff (c : CfgO d) (r : RV d) (p : Fin d → ℚ) :
    fireO c r p ↔ xiBO c r (cV p) ≤ -(c.par.rho : ℝ) + c.par.eHat := by
  unfold fireO
  rw [← Rat.cast_le (K := ℝ)]
  have e : (((c.par.eta * (r.l - r.G ⬝ᵥ p) - 2 * (p ⬝ᵥ ((r.B * r.Bᵀ) *ᵥ p) / 2 - r.b ⬝ᵥ p + r.k)) : ℚ) : ℝ) =
      xiBO c r (cV p) := by
    unfold xiBO df2Phi
    push_cast
    simp only [cV_dot, cM_mulVec, cM_mul, cM_transpose]
    ring
  rw [e]; push_cast; rfl

/-- The objective of BL's test call, `yᵀP'_+y/2 - w'_+·y`. -/
theorem obj_T (c : CfgO d) (st : St d) (r : RV d) (y : Fin d → ℝ) :
    (callTO c st r).obj y = y ⬝ᵥ ((cM r.B * (cM r.B)ᵀ) *ᵥ y) / 2 -
      (cV r.b - ((c.par.eta : ℝ) / 2) • cV r.G) ⬝ᵥ y := by
  have e : ∀ D : CallQ d, D.P = r.B * r.Bᵀ → D.f = r.b - (c.par.eta / 2) • r.G →
      D.obj y = y ⬝ᵥ ((cM r.B * (cM r.B)ᵀ) *ᵥ y) / 2 - (cV r.b - ((c.par.eta : ℝ) / 2) • cV r.G) ⬝ᵥ y := by
    intro D hP hf
    unfold CallQ.obj
    rw [hP, hf]
    change y ⬝ᵥ (cM (r.B * r.Bᵀ) *ᵥ y) / 2 - cV (r.b - (c.par.eta / 2) • r.G) ⬝ᵥ y = _
    rw [cM_mul, cM_transpose, cV_sub, cV_smul]
    push_cast; rfl
  unfold callTO; split <;> exact e _ rfl rfl

/-- `Xi'(y) = η' l' - 2 k' - 2 obj(y)` (Lemma SEL, the expansion of BL's statistic). -/
theorem xiB_obj (c : CfgO d) (st : St d) (r : RV d) (y : Fin d → ℝ) :
    xiBO c r y = (c.par.eta : ℝ) * r.l - 2 * r.k - 2 * (callTO c st r).obj y := by
  rw [obj_T]
  unfold xiBO df2Phi
  simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
  ring
end AdversarialBco.Unified.EngC

namespace AdversarialBco.Unified.Eng.RCHypO

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg
  oNorm_neg oNorm_sub_comm)
open AdversarialBco.Unified.BLO AdversarialBco.Unified.Eng AdversarialBco.Unified.EngC AdversarialBco.Unified.Asm
open AdversarialBco.Unified.BudK (BudOK RunCaseK poK parK)
open AdversarialBco.Bit.BLP (Par St Mode init rnd sqrtDn rndM rndV frob2 cV cM opN LT Lmu rB eBL CallQ)
open AdversarialBco.Bit.BLP.RC
open AdversarialBco.Bit.BLP (refTest selT muOf)
open AdversarialBco.Bit.Cpl (apAdv advOK advPick)
open Matrix

variable {d : ℕ} {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d} {k : ℕ}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z ε : ℝ} {f : E d → ℝ}

theorem eHat_eq (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : ((c.par.eHat : ℚ) : ℝ) = BudK.eh d c.n k := by
  rw [H.par]; rfl

theorem eta_err (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    |(c.par.eta : ℝ) - BudK.eta d c.n k| ≤ BudK.tp d c.n k / 16 * BudK.eta d c.n k := by
  have hη : 0 < BudK.eta d c.n k := H.det.rows.pos_eta
  have h : |((c.par.eta : ℚ) : ℝ) / BudK.eta d c.n k - 1| ≤ BudK.tp d c.n k / 16 := by
    rw [H.par]; exact H.bud.enc.eta_rel
  have e : (c.par.eta : ℝ) - BudK.eta d c.n k = BudK.eta d c.n k * ((c.par.eta : ℝ) / BudK.eta d c.n k - 1) := by
    field_simp
  rw [e, abs_mul, abs_of_pos hη]
  nlinarith [abs_nonneg ((c.par.eta : ℝ) / BudK.eta d c.n k - 1)]

/-- E13: `|Xi' - Xi°| ≤ e_X` on `B_R`. -/
theorem xi_E13 (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f)
    (O : C1OutK d c.n k c.par st ξ' (rvH orc c st ξ' ζ' ε f) (ctxO K c k ap) π s)
    {y : Fin d → ℝ} (hy : oNorm y ≤ BudK.R d c.n k) :
    |xiBO c (rvH orc c st ξ' ζ' ε f) y - (ctxO K c k ap).Xi π s y| ≤
      BudK.eX d c.n k := by
  have S := H.sett
  have hη : 0 < BudK.eta d c.n k := H.det.rows.pos_eta
  have htp := NK.tp_small d c.n k
  have htp0 := (NK.tp_pos d c.n k).le
  have h1 := xi_err (BudK.eta d c.n k) (c.par.eta : ℝ) (BudK.tp d c.n k) ((ctxO K c k ap).ln π s)
    ((rvH orc c st ξ' ζ' ε f).l : ℝ) (BudK.R d c.n k) (BudK.Gb d c.n k) ((s + 1) * BudK.el d c.n k) ((s + 1) * BudK.eg d c.n k)
    ((ctxO K c k ap).Gn π s) (cV (rvH orc c st ξ' ζ' ε f).G) y hη.le H.eta_err htp0 htp H.R0 hy
    S.ln_le S.Gn_le O.errl O.errG
  have h2 := H.phi_err_n O hy
  have hs : (s : ℝ) + 1 ≤ c.n := by exact_mod_cast H.hs
  have hel : 0 ≤ BudK.el d c.n k := by
    have := O.errl; have := abs_nonneg (((rvH orc c st ξ' ζ' ε f).l : ℝ) - (ctxO K c k ap).ln π s)
    have : (0 : ℝ) < s + 1 := by positivity
    by_contra hc; push Not at hc; nlinarith
  have heg : 0 ≤ BudK.eg d c.n k := by
    have := O.errG; have := oNorm_nonneg (cV (rvH orc c st ξ' ζ' ε f).G - (ctxO K c k ap).Gn π s)
    have : (0 : ℝ) < s + 1 := by positivity
    by_contra hc; push Not at hc; nlinarith
  have hR := H.R0
  have e : xiBO c (rvH orc c st ξ' ζ' ε f) y - (ctxO K c k ap).Xi π s y =
      ((c.par.eta : ℝ) * (((rvH orc c st ξ' ζ' ε f).l : ℝ) - cV (rvH orc c st ξ' ζ' ε f).G ⬝ᵥ y) -
        BudK.eta d c.n k * ((ctxO K c k ap).ln π s - (ctxO K c k ap).Gn π s ⬝ᵥ y)) -
      2 * (df2Phi (cM (rvH orc c st ξ' ζ' ε f).B * (cM (rvH orc c st ξ' ζ' ε f).B)ᵀ)
        (cV (rvH orc c st ξ' ζ' ε f).b) (rvH orc c st ξ' ζ' ε f).k y -
        (ctxO K c k ap).PhiN π s y) := by
    unfold xiBO Df2Ctx.Xi
    change (c.par.eta : ℝ) * _ - 2 * _ - (BudK.eta d c.n k * _ - 2 * _) = _
    ring
  rw [e]
  have hA : (s + 1) * BudK.el d c.n k ≤ c.n * BudK.el d c.n k := mul_le_mul_of_nonneg_right hs hel
  have hB : BudK.R d c.n k * ((s + 1) * BudK.eg d c.n k) ≤ BudK.R d c.n k * (c.n * BudK.eg d c.n k) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs heg) hR
  have hAB : BudK.eta d c.n k * (101 / 100) * ((s + 1) * BudK.el d c.n k + BudK.R d c.n k * ((s + 1) * BudK.eg d c.n k)) ≤
      BudK.eta d c.n k * (101 / 100) * (c.n * BudK.el d c.n k + BudK.R d c.n k * c.n * BudK.eg d c.n k) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
  unfold BudK.eX
  have := abs_sub ((c.par.eta : ℝ) * (((rvH orc c st ξ' ζ' ε f).l : ℝ) -
    cV (rvH orc c st ξ' ζ' ε f).G ⬝ᵥ y) - BudK.eta d c.n k * ((ctxO K c k ap).ln π s -
      (ctxO K c k ap).Gn π s ⬝ᵥ y))
    (2 * (df2Phi (cM (rvH orc c st ξ' ζ' ε f).B * (cM (rvH orc c st ξ' ζ' ε f).B)ᵀ)
      (cV (rvH orc c st ξ' ζ' ε f).b) (rvH orc c st ξ' ζ' ε f).k y - (ctxO K c k ap).PhiN π s y))
  rw [abs_mul, abs_two] at this
  change _ ≤ BudK.eta d c.n k * (101 / 100) * (c.n * BudK.el d c.n k + BudK.R d c.n k * c.n * BudK.eg d c.n k) +
    BudK.eta d c.n k * BudK.tp d c.n k / 16 * (21 / 10) * BudK.R d c.n k * BudK.Gb d c.n k + 2 * BudK.ePhi d c.n k
  linarith


/-- P°'s radius of round `s`: `1 - ε` at the first round, `s_b (1 - ε)` after. -/
theorem r_cases (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    (st.first = true ∧ ((ctxO K c k ap).st π s).r = 1 - BudK.eps d c.n k) ∨
      (st.first = false ∧ ((ctxO K c k ap).st π s).r = (poK d c.n k).sb * (1 - BudK.eps d c.n k)) := by
  have hinv := H.sett.inv
  have hfst := H.track.first
  by_cases hf : st.first = true
  · have hs0 : s = 0 := hinv.first.1 (hfst ▸ hf)
    subst hs0
    exact Or.inl ⟨hf, rfl⟩
  · have hf' : ((ctxO K c k ap).st π s).first = false := by rw [← hfst]; simpa using hf
    have hs0 : s ≠ 0 := fun h => by
      have := hinv.first.2 h; rw [hf'] at this; exact Bool.false_ne_true this
    obtain ⟨s0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs0
    have hlt : s0 < (ctxO K c k ap).tau π (s0 + 1 + 1) := by rw [H.tau]; omega
    obtain ⟨-, -, -, -, -, -, hrs⟩ := prev_round H.det hlt
    exact Or.inr ⟨by simpa using hf, hrs⟩

theorem sb_props' (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    0 < (poK d c.n k).sb ∧ BudK.rmin d c.n k ≤ (poK d c.n k).sb * (1 - BudK.eps d c.n k) ∧ (poK d c.n k).sb ≤ 1 := by
  have e := H.det.sb
  change (poK d c.n k).sb = (poK d c.n k).δe ^ 2 / ((poK d c.n k).R * ((poK d c.n k).R + 1)) at e
  have hde := H.sett.de_pos
  have hde1 : (poK d c.n k).δe < 1 := H.det.rows.de_lt
  have hR : 1 ≤ (poK d c.n k).R := H.R_ge
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  rw [e]
  refine ⟨by positivity, ?_, ?_⟩
  · unfold BudK.rmin
    change (poK d c.n k).δe ^ 2 / (2 * (poK d c.n k).R * ((poK d c.n k).R + 1)) ≤ _
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < (poK d c.n k).δe ^ 2 * ((poK d c.n k).R * ((poK d c.n k).R + 1)) := by positivity
    nlinarith
  · rw [div_le_one (by positivity)]; nlinarith

/-- `r_min ≤ r_s ≤ 1` and BL's accuracy of the test call is at most `(δe/d) r_s²/8`. -/
theorem r_props (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) (r : RV d) :
    BudK.rmin d c.n k ≤ ((ctxO K c k ap).st π s).r ∧ ((ctxO K c k ap).st π s).r ≤ 1 ∧
      2 * ((callTO c st r).e : ℝ) ≤
        (ctxO K c k ap).p.δe / d * ((ctxO K c k ap).st π s).r ^ 2 / 4 := by
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  obtain ⟨hsb0, hsbm, hsb1⟩ := H.sb_props'
  have hde := H.sett.de_pos
  have hde1 : (poK d c.n k).δe < 1 := H.det.rows.de_lt
  have hR : 1 ≤ (poK d c.n k).R := H.R_ge
  have hd : (0 : ℝ) < d := by exact_mod_cast H.hd
  have hNe : ((c.par.Ne : ℕ) : ℝ) = 1 / (poK d c.n k).δe := by
    rw [show ((c.par.Ne : ℕ) : ℝ) = BudK.Ne d c.n k by rw [H.par]; exact H.bud.enc.Ne_eq]
    have := H.bud.enc.de_eq
    change (poK d c.n k).δe = 1 / BudK.Ne d c.n k at this
    rw [this, one_div_one_div]
  have hrmin : BudK.rmin d c.n k ≤ 1 / 2 := by
    unfold BudK.rmin
    change (poK d c.n k).δe ^ 2 / (2 * (poK d c.n k).R * ((poK d c.n k).R + 1)) ≤ _
    rw [div_le_iff₀ (by positivity)]; nlinarith
  rcases H.r_cases with ⟨hf, hr⟩ | ⟨hf, hr⟩
  · rw [hr]
    refine ⟨by linarith, by linarith, ?_⟩
    have e : ((callTO c st r).e : ℝ) =
        (1 - (c.par.eps : ℝ)) ^ 2 / (((c.par.Ne : ℕ) : ℝ) * d * 8) := by
      unfold callTO; rw [ite_eq_left hf]; simp only [callO]; push_cast; rfl
    rw [e]
    exact aT_arith _ _ _ _ _ (by linarith) (by linarith) hNe hde hd
  · rw [hr]
    refine ⟨hsbm, ?_, ?_⟩
    · have : 0 ≤ (poK d c.n k).sb * BudK.eps d c.n k := by positivity
      nlinarith
    have hf' : ¬ st.first = true := by simp [hf]
    have e : ((callTO c st r).e : ℝ) =
        ((c.par.sb : ℝ) * (1 - (c.par.eps : ℝ))) ^ 2 / (((c.par.Ne : ℕ) : ℝ) * d * 8) := by
      unfold callTO; rw [ite_eq_right hf']; simp only [callO, rB]; push_cast; rfl
    rw [e]
    have hsb' : (0 : ℝ) < c.par.sb := by exact_mod_cast H.par_pos.1
    have : ((c.par.sb : ℚ) : ℝ) ≤ (poK d c.n k).sb := by rw [H.par]; exact H.bud.enc.sb_le
    have hx0 : (0 : ℝ) ≤ (c.par.sb : ℝ) * (1 - (c.par.eps : ℝ)) := mul_nonneg hsb'.le (by linarith)
    refine aT_arith _ _ _ _ _ hx0 ?_ hNe hde hd
    have h1 : (c.par.sb : ℝ) * (1 - (c.par.eps : ℝ)) ≤ (poK d c.n k).sb * (1 - (c.par.eps : ℝ)) :=
      mul_le_mul_of_nonneg_right this (by linarith)
    have h2 : (poK d c.n k).sb * (1 - (c.par.eps : ℝ)) ≤ (poK d c.n k).sb * (1 - BudK.eps d c.n k) :=
      mul_le_mul_of_nonneg_left (by linarith) hsb0.le
    exact h1.trans h2


theorem callT_e_pos (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) (r : RV d) :
    (0 : ℚ) < (callTO c st r).e := by
  obtain ⟨hsb, heps, hNe, hRint, hR'⟩ := H.par_pos
  have hd : (0 : ℚ) < d := by exact_mod_cast H.hd
  have hNe' : (0 : ℚ) < (c.par.Ne : ℚ) := by exact_mod_cast hNe
  have : 0 < 1 - c.par.eps := by linarith
  unfold callTO; split
  · show 0 < (1 - c.par.eps) ^ 2 / (c.par.Ne * d * 8); positivity
  · show 0 < (c.par.sb * (1 - c.par.eps)) ^ 2 / (c.par.Ne * d * 8); positivity

/-- E15, Lemma SEL at BL's test point `p'`: P°'s point `v₁ = selV(p', β)` is in `R⁻_s`, within `1` of the largest
statistic there, has statistic at most `-θ ρ` exactly when BL fires, and is `p'` when BL does not fire. -/
theorem sel (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f)
    (O : C1OutK d c.n k c.par st ξ' (rvH orc c st ξ' ζ' ε f) (ctxO K c k ap) π s) :
    ∃ p', apO orc c (callTO c st (rvH orc c st ξ' ζ' ε f)) = some p' ∧
      selV (ctxO K c k ap) π s (cV p') (decide (fireO c (rvH orc c st ξ' ζ' ε f) p'))
        ∈ (ctxO K c k ap).Rm π s ∧
      (∀ y ∈ (ctxO K c k ap).Rm π s, (ctxO K c k ap).Xi π s y ≤
        (ctxO K c k ap).Xi π s (selV (ctxO K c k ap) π s (cV p')
          (decide (fireO c (rvH orc c st ξ' ζ' ε f) p'))) + 1) ∧
      ((ctxO K c k ap).Xi π s (selV (ctxO K c k ap) π s (cV p')
          (decide (fireO c (rvH orc c st ξ' ζ' ε f) p'))) ≤
          -((ctxO K c k ap).p.theta * (ctxO K c k ap).p.rho) ↔
        fireO c (rvH orc c st ξ' ζ' ε f) p') ∧
      (¬ fireO c (rvH orc c st ξ' ζ' ε f) p' →
        selV (ctxO K c k ap) π s (cV p')
          (decide (fireO c (rvH orc c st ξ' ζ' ε f) p')) = cV p') := by
  have hs := H.sett.hs'
  obtain ⟨p', hp', hpreg, hpmin⟩ := H.testCall O
  refine ⟨p', hp', ?_⟩
  obtain ⟨hgA, -, hgC⟩ := H.gapT (rvH orc c st ξ' ζ' ε f)
  have hRmR : ∀ y ∈ (ctxO K c k ap).Rm π s, oNorm y ≤ (ctxO K c k ap).p.R := fun y hy => by
    have h := (H.det.Rm_props hs).2.2 hy
    have h' : oNorm (y - 0) ≤ (ctxO K c k ap).p.R := h
    rwa [sub_zero] at h'
  have hpRm : cV p' ∈ (ctxO K c k ap).Rm π s := hgC hpreg
  have hpR := hRmR _ hpRm
  obtain ⟨hrmin, hr1, haT⟩ := H.r_props (rvH orc c st ξ' ζ' ε f)
  have hgood := H.det.good s hs
  have hθ : (ctxO K c k ap).p.theta = 1 := H.det.theta
  obtain ⟨hρ1, hρ2⟩ := H.rho_enc
  have eρ : (ctxO K c k ap).p.rho = BudK.rho d c.n k := rfl
  have heX := H.bud.eX_le
  have hePhi := H.bud.ePhi_le
  have hwr := H.wr0
  have hsel := H.bud.sel_le
  have hde : 0 < (ctxO K c k ap).p.δe := H.sett.de_pos
  have hde1 : (ctxO K c k ap).p.δe < 1 := H.det.rows.de_lt
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  obtain ⟨hhR, hh1⟩ := H.h_props
  have hκ1 := H.kap_props.2
  have hR0 := H.R0
  have hh0 : 0 ≤ BudK.h d c.n k := by
    have : 0 ≤ (1 - (1 - (c.par.eps : ℝ)) / (1 - BudK.eps d c.n k)) * BudK.R d c.n k :=
      mul_nonneg (by linarith) hR0
    linarith
  have heX0 : 0 ≤ BudK.eX d c.n k := by
    have h0 : oNorm (0 : Fin d → ℝ) ≤ BudK.R d c.n k := by
      show Real.sqrt _ ≤ _; simp only [dotProduct_zero, Real.sqrt_zero]; exact hR0
    exact (abs_nonneg _).trans (H.xi_E13 O h0)
  have haT0 : (0 : ℝ) ≤ ((callTO c st (rvH orc c st ξ' ζ' ε f)).e : ℝ) := by
    exact_mod_cast (H.callT_e_pos _).le
  have eLip : BudK.LipF d c.n k = 4 * (ctxO K c k ap).p.R / (ctxO K c k ap).p.δe ^ 2 := rfl
  have hLip0 : 0 ≤ BudK.LipF d c.n k := by rw [eLip]; positivity
  have hrmin0 : 0 ≤ BudK.rmin d c.n k := by
    unfold BudK.rmin; have : 0 ≤ BudK.R d c.n k := hR0; positivity
  -- (H1)
  have hH1 : ∀ y ∈ (ctxO K c k ap).Rm π s,
      (ctxO K c k ap).Xi π s y ≤ (ctxO K c k ap).Xi π s (cV p') +
        (2 * ((callTO c st (rvH orc c st ξ' ζ' ε f)).e : ℝ) + 2 * BudK.eX d c.n k +
          BudK.LipF d c.n k * BudK.h d c.n k) := by
    intro y hy
    obtain ⟨y', hy'Q, hyy'⟩ := hgA y hy
    have hy'R := hRmR y' (hgC hy'Q)
    have h1 := xi_lip H.det hs y hy'R
    have h2 := abs_le.1 (H.xi_E13 O hy'R)
    have h3 := abs_le.1 (H.xi_E13 O hpR)
    have h4 := hpmin y' hy'Q
    have h5 := xiB_obj c st (rvH orc c st ξ' ζ' ε f) y'
    have h6 := xiB_obj c st (rvH orc c st ξ' ζ' ε f) (cV p')
    have h7 : 4 * (ctxO K c k ap).p.R / (ctxO K c k ap).p.δe ^ 2 * oNorm (y - y') ≤
        BudK.LipF d c.n k * BudK.h d c.n k := by
      rw [eLip]; exact mul_le_mul_of_nonneg_left hyy' (by positivity)
    linarith
  -- (H3) and the size of the margin
  have hH3 : (2 * ((callTO c st (rvH orc c st ξ' ζ' ε f)).e : ℝ) + 2 * BudK.eX d c.n k +
      BudK.LipF d c.n k * BudK.h d c.n k) + (2 * BudK.eh d c.n k + BudK.wr d c.n k) ≤
      (ctxO K c k ap).p.δe / d * ((ctxO K c k ap).st π s).r ^ 2 := by
    have h1 : BudK.rmin d c.n k ^ 2 ≤ ((ctxO K c k ap).st π s).r ^ 2 := pow_le_pow_left₀ hrmin0 hrmin 2
    have h2 : (ctxO K c k ap).p.δe / d * BudK.rmin d c.n k ^ 2 ≤
        (ctxO K c k ap).p.δe / d * ((ctxO K c k ap).st π s).r ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have e1 : BudK.selR d c.n k = 3 / 4 * ((ctxO K c k ap).p.δe / d * BudK.rmin d c.n k ^ 2) := by
      unfold BudK.selR; change 3 / 4 * (ctxO K c k ap).p.δe / d * _ = _; ring
    unfold BudK.sel at hsel
    rw [e1] at hsel
    linarith
  have hmarg : (ctxO K c k ap).p.δe / d * ((ctxO K c k ap).st π s).r ^ 2 ≤ 1 := by
    have h1 : ((ctxO K c k ap).st π s).r ^ 2 ≤ 1 := by
      have := hgood.2.2; nlinarith
    have h2 : (ctxO K c k ap).p.δe / d ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have h3 : 0 ≤ ((ctxO K c k ap).st π s).r ^ 2 := sq_nonneg _
    nlinarith
  have hLh : 0 ≤ BudK.LipF d c.n k * BudK.h d c.n k := mul_nonneg hLip0 hh0
  have heh0 : 0 ≤ BudK.eh d c.n k := by have := H.ePhi0; linarith
  have hspec := selT_spec H.hd (refTest (ctxO K c k ap).p ((ctxO K c k ap).st π s) (π.xi s)
      ((ctxO K c k ap).Y π s)).1
    (refTest (ctxO K c k ap).p ((ctxO K c k ap).st π s) (π.xi s) ((ctxO K c k ap).Y π s)).2.1
    (refTest (ctxO K c k ap).p ((ctxO K c k ap).st π s) (π.xi s) ((ctxO K c k ap).Y π s)).2.2
    (-((ctxO K c k ap).p.theta * (ctxO K c k ap).p.rho)) ((ctxO K c k ap).st π s).ctr
    ((ctxO K c k ap).st π s).r (cV p')
    (decide (fireO c (rvH orc c st ξ' ζ' ε f) p')) ((ctxO K c k ap).Rm π s)
    ((ctxO K c k ap).p.δe / d)
    (2 * ((callTO c st (rvH orc c st ξ' ζ' ε f)).e : ℝ) + 2 * BudK.eX d c.n k +
      BudK.LipF d c.n k * BudK.h d c.n k) (2 * BudK.eh d c.n k + BudK.wr d c.n k) (H.det.Rm_props hs).1 hgood.2.1 hgood.2.2
    (fun v => by
      rw [refTest_P]
      have h1 := Pn_lower H.det hs v
      have h2 : 0 ≤ v ⬝ᵥ v := by rw [← oNorm_sq]; positivity
      have h3 : (ctxO K c k ap).p.δe / d ≤ (ctxO K c k ap).p.δe := div_le_self hde.le hd1
      nlinarith)
    hpRm
    (fun y hy => by rw [refTest_F, refTest_F]; exact hH1 y hy)
    (fun hf => by
      rw [refTest_F]
      have hnf : ¬ fireO c (rvH orc c st ξ' ζ' ε f) p' := by simpa using hf
      rw [fireO_iff] at hnf
      rw [H.eHat_eq] at hnf
      have h3 := abs_le.1 (H.xi_E13 O hpR)
      rw [hθ, eρ]
      linarith)
    (fun hf => by
      rw [refTest_F]
      have hfq : fireO c (rvH orc c st ξ' ζ' ε f) p' := by simpa using hf
      rw [fireO_iff] at hfq
      rw [H.eHat_eq] at hfq
      have h3 := abs_le.1 (H.xi_E13 O hpR)
      rw [hθ, eρ]
      linarith)
    hH3 (by linarith) (by linarith)
  obtain ⟨hv1Q, hv1max, hv1iff, hv1eq⟩ := hspec
  refine ⟨hv1Q, fun y hy => ?_, ?_, fun hnf => hv1eq (by simpa using hnf)⟩
  · have := hv1max y hy
    rw [refTest_F, refTest_F] at this
    linarith
  · rw [refTest_F] at hv1iff
    rw [hv1iff, decide_eq_true_iff]


theorem Le2 (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : 2 ≤ (ctxO K c k ap).p.Le := by
  have := H.bud.Le_ge; change 17467 ≤ (poK d c.n k).Le at this; change 2 ≤ (poK d c.n k).Le; linarith

theorem Rm_norm (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) {y : Fin d → ℝ}
    (hy : y ∈ (ctxO K c k ap).Rm π s) : oNorm y ≤ (ctxO K c k ap).p.R := by
  have h := (H.det.Rm_props H.sett.hs').2.2 hy
  have h' : oNorm (y - 0) ≤ (ctxO K c k ap).p.R := h
  rwa [sub_zero] at h'

/-- P°'s test call under the advice returns `v₁ = selV(p', β)` (the checked routine accepts it at `e_T = 1`). -/
theorem tcall_eq (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f)
    (O : C1OutK d c.n k c.par st ξ' (rvH orc c st ξ' ζ' ε f) (ctxO K c k ap) π s)
    (hap : ap s = apAdv (advC K orc c k ap π s st ξ' ζ' ε f)) :
    ∃ p', apO orc c (callTO c st (rvH orc c st ξ' ζ' ε f)) = some p' ∧
      (ctxO K c k ap).tcall π s = some (selV (ctxO K c k ap) π s (cV p')
        (decide (fireO c (rvH orc c st ξ' ζ' ε f) p'))) ∧
      selV (ctxO K c k ap) π s (cV p') (decide (fireO c (rvH orc c st ξ' ζ' ε f) p'))
        ∈ (ctxO K c k ap).Rm π s ∧
      ((ctxO K c k ap).Xi π s (selV (ctxO K c k ap) π s (cV p')
          (decide (fireO c (rvH orc c st ξ' ζ' ε f) p'))) ≤
          -((ctxO K c k ap).p.theta * (ctxO K c k ap).p.rho) ↔
        fireO c (rvH orc c st ξ' ζ' ε f) p') ∧
      (¬ fireO c (rvH orc c st ξ' ζ' ε f) p' →
        selV (ctxO K c k ap) π s (cV p')
          (decide (fireO c (rvH orc c st ξ' ζ' ε f) p')) = cV p') := by
  have hs := H.sett.hs'
  obtain ⟨p', hp', hv1Q, hv1max, hv1iff, hv1eq⟩ := H.sel O
  refine ⟨p', hp', ?_, hv1Q, hv1iff, hv1eq⟩
  have htq := testO_eq orc c st ξ' ζ' (obsO orc c st ξ' f ε) O.ga O.gt hp'
  have hv : (advQO orc c c.n st ξ' ζ' (obsO orc c st ξ' f ε)
      (ctxO K c k ap).p ((ctxO K c k ap).st π s) (π.xi s) ((ctxO K c k ap).Y π s)).1 =
      selV (ctxO K c k ap) π s (cV p')
        (decide (fireO c (rvH orc c st ξ' ζ' ε f) p')) := by
    unfold advQO; rw [htq]
  have heT : (ctxO K c k ap).eT = 1 := eT_one H.det H.Le2
  have hadv : advOK ((ctxO K c k ap).Rm π s) (ctxO K c k ap).p.R ((ctxO K c k ap).Pn π s)
      ((ctxO K c k ap).zz π s) (ctxO K c k ap).eT
      (selV (ctxO K c k ap) π s (cV p')
        (decide (fireO c (rvH orc c st ξ' ζ' ε f) p'))) := by
    refine ⟨hv1Q, H.Rm_norm hv1Q, fun q hq => ?_⟩
    have h1 := hv1max _ hq
    rw [xi_ell H.det hs, xi_ell H.det hs] at h1
    rw [heT]; linarith
  have hpick : advPick (advQO orc c c.n st ξ' ζ' (obsO orc c st ξ' f ε)
      (ctxO K c k ap).p ((ctxO K c k ap).st π s) (π.xi s) ((ctxO K c k ap).Y π s))
      (ctxO K c k ap).eT = (advQO orc c c.n st ξ' ζ' (obsO orc c st ξ' f ε)
      (ctxO K c k ap).p ((ctxO K c k ap).st π s) (π.xi s) ((ctxO K c k ap).Y π s)).1 := by
    unfold advPick; rw [heT]; exact ite_eq_left (by norm_num)
  unfold Df2Ctx.tcall
  change ap s _ _ _ _ _ _ _ = _
  rw [hap]
  unfold apAdv
  rw [hpick, hv]
  exact ite_eq_left hadv



end AdversarialBco.Unified.Eng.RCHypO
