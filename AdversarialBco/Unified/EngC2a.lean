/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EngC1b
public import AdversarialBco.Bit.BLRoundC2

@[expose] public section

/-!
# Piece C for BL-O, part C2 (a): BL-O's calls, its regions against `K_ε`, E12

Bit/BLRoundC2.lean (first part) for BL-O at `k`. BL-O's test call and call of line μ (`callTO`, `callMO`, verbatim
from `stepO`) have no rows: the region of a call is `regO K c D = QKs K c (1 - ε')⁻¹ ∩ regionC D`, the K-part
`{y | μ_S + A_S y/(1 - ε') ∈ K}` read by ELL-O through the CM test (`apSpecO`). Against P°'s `K_ε = (1 - ε) K~`
(`K~ = S(K)` on `PgGood`, `Kt_eq`): `QKs (1 - ε')⁻¹ ⊆ K_ε` (`keps_of_QK`, `ε ≤ ε'` and `S(K)` convex with `0`) and
`κ K_ε ⊆ QKs (1 - ε')⁻¹`, `κ = (1 - ε')/(1 - ε)` (`QK_of_keps`), in place of v2.1's rows at the level `1 - ε'`.
-/

namespace AdversarialBco.Unified.EngC

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg
  oNorm_neg oNorm_sub_comm)
open AdversarialBco.Unified.BLO AdversarialBco.Unified.Eng AdversarialBco.Unified.Asm
open AdversarialBco.Unified.BudK (BudOK RunCaseK poK parK)
open AdversarialBco.Bit.BLP (Par St Mode init rnd sqrtDn rndM rndV frob2 cV cM opN LT Lmu rB eBL CallQ)
open AdversarialBco.Bit.BLP.RC
open AdversarialBco.BitRAM (toE)
open Matrix

variable {d : ℕ}

/-! ## BL-O's round after R10 -/

/-- BL-O's test call (R11) from the values `r` of R5 to R9. -/
def callTO (c : CfgO d) (st : St d) (r : RV d) : CallQ d :=
  if st.first then callO c 0 0 0 (1 - c.par.eps) (r.B * r.Bᵀ) (r.b - (c.par.eta / 2) • r.G)
      ((1 - c.par.eps) ^ 2 / (c.par.Ne * d * 8))
  else callO c (st.B * st.Bᵀ) st.b (LT c.par - st.k) (rB c.par / 2) (r.B * r.Bᵀ)
      (r.b - (c.par.eta / 2) • r.G) (rB c.par ^ 2 / (c.par.Ne * d * 8))

/-- BL-O's fire test (R12) at the test point `p`. -/
abbrev fireO (c : CfgO d) (r : RV d) (p : Fin d → ℚ) : Prop :=
  c.par.eta * (r.l - r.G ⬝ᵥ p) - 2 * (p ⬝ᵥ ((r.B * r.Bᵀ) *ᵥ p) / 2 - r.b ⬝ᵥ p + r.k) ≤ -c.par.rho + c.par.eHat

/-- BL-O's Newton point of line μ (R13). -/
def wmuO (c : CfgO d) (st : St d) (ξ : Fin d → ℚ) (r : RV d) : Fin d → ℚ :=
  st.mu - rnd c.par.p (c.par.eta * r.Y * c.par.nu / r.q) • (st.A *ᵥ ξ)

/-- BL-O's call of line μ (R14). -/
def callMO (c : CfgO d) (n : ℕ) (st : St d) (ξ : Fin d → ℚ) (r : RV d) : CallQ d :=
  callO c (r.B * r.Bᵀ) r.b (Lmu c.par - r.k) (rB c.par / 2) (r.B * r.Bᵀ) ((r.B * r.Bᵀ) *ᵥ wmuO c st ξ r)
    (eBL c.par d n)

/-- BL-O's region of a call: the K-part at the scale `(1 - ε')⁻¹` and the region of the call (`ApSpecO`). -/
def regO (K : Set (E d)) (c : CfgO d) (D : CallQ d) : Set (Fin d → ℝ) :=
  QKs K c (1 - c.par.eps)⁻¹ ∩ regionC D

theorem testO_eq (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (st : St d) (ξ : Fin d → ℚ) (ζ : ℚ) (obs : ℤ)
    (ga : ¬ ((rvO orc c st ξ ζ obs).a < 1 / 2 ∨ (rvO orc c st ξ ζ obs).q < 1 / 2))
    (gt : ¬ (2 * (c.par.Lam : ℚ) < frob2 (rvO orc c st ξ ζ obs).B ∨
      2 * (c.par.Lam : ℚ) < frob2 (rvO orc c st ξ ζ obs).A))
    {p : Fin d → ℚ} (hp : apO orc c (callTO c st (rvO orc c st ξ ζ obs)) = some p) :
    testO orc c st ξ ζ obs = some (p, decide (fireO c (rvO orc c st ξ ζ obs) p)) := by
  unfold testO
  dsimp only [rvO, callTO] at ga gt hp ⊢
  rw [ite_eq_right ga, ite_eq_right gt]
  rw [hp]
  rfl

theorem stepO_fire (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (n : ℕ) (st : St d) (ξ : Fin d → ℚ) (ζ : ℚ)
    (obs : ℤ) (ga : ¬ ((rvO orc c st ξ ζ obs).a < 1 / 2 ∨ (rvO orc c st ξ ζ obs).q < 1 / 2))
    (gt : ¬ (2 * (c.par.Lam : ℚ) < frob2 (rvO orc c st ξ ζ obs).B ∨
      2 * (c.par.Lam : ℚ) < frob2 (rvO orc c st ξ ζ obs).A))
    {p : Fin d → ℚ} (hp : apO orc c (callTO c st (rvO orc c st ξ ζ obs)) = some p)
    (hf : fireO c (rvO orc c st ξ ζ obs) p) :
    stepO orc c n (.run st) ξ ζ obs = .run (init c.par d) := by
  unfold stepO
  dsimp only [rvO, callTO, fireO] at ga gt hp hf ⊢
  rw [ite_eq_right ga, ite_eq_right gt, hp]
  dsimp only
  rw [ite_eq_left hf]

theorem stepO_cont (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (n : ℕ) (st : St d) (ξ : Fin d → ℚ) (ζ : ℚ)
    (obs : ℤ) (ga : ¬ ((rvO orc c st ξ ζ obs).a < 1 / 2 ∨ (rvO orc c st ξ ζ obs).q < 1 / 2))
    (gt : ¬ (2 * (c.par.Lam : ℚ) < frob2 (rvO orc c st ξ ζ obs).B ∨
      2 * (c.par.Lam : ℚ) < frob2 (rvO orc c st ξ ζ obs).A))
    {p : Fin d → ℚ} (hp : apO orc c (callTO c st (rvO orc c st ξ ζ obs)) = some p)
    (hf : ¬ fireO c (rvO orc c st ξ ζ obs) p)
    (hw : ¬ (2 * c.par.W) ^ 2 < wmuO c st ξ (rvO orc c st ξ ζ obs) ⬝ᵥ wmuO c st ξ (rvO orc c st ξ ζ obs))
    {mu' : Fin d → ℚ} (hm : apO orc c (callMO c n st ξ (rvO orc c st ξ ζ obs)) = some mu') :
    stepO orc c n (.run st) ξ ζ obs = .run ⟨false, mu', (rvO orc c st ξ ζ obs).A, (rvO orc c st ξ ζ obs).B,
      (rvO orc c st ξ ζ obs).b, (rvO orc c st ξ ζ obs).k, (rvO orc c st ξ ζ obs).G, (rvO orc c st ξ ζ obs).l⟩ := by
  unfold stepO
  dsimp only [rvO, callTO, fireO, wmuO, callMO] at ga gt hp hf hw hm ⊢
  rw [ite_eq_right ga, ite_eq_right gt, hp]
  dsimp only
  rw [ite_eq_right hf, ite_eq_right hw, hm]

/-! ## BL-O's regions -/

/-- The region of a call built by `callO`, read in `ℝ^d`. -/
theorem regO_callO (K : Set (E d)) (c : CfgO d) (H : Matrix (Fin d) (Fin d) ℚ) (g : Fin d → ℚ) (ℓ r : ℚ)
    (P : Matrix (Fin d) (Fin d) ℚ) (f : Fin d → ℚ) (e : ℚ) (y : Fin d → ℝ) :
    y ∈ regO K c (callO c H g ℓ r P f e) ↔
      y ∈ QKs K c (1 - c.par.eps)⁻¹ ∧ df2Phi (cM H) (cV g) 0 y ≤ ℓ ∧ oNorm y ≤ c.par.Rint := by
  have e1 : y ⬝ᵥ (H.map ((↑) : ℚ → ℝ) *ᵥ y) / 2 - (fun j => (g j : ℝ)) ⬝ᵥ y = df2Phi (cM H) (cV g) 0 y := by
    unfold df2Phi cM cV; ring
  show y ∈ QKs K c (1 - c.par.eps)⁻¹ ∧
      (y ⬝ᵥ (H.map ((↑) : ℚ → ℝ) *ᵥ y) / 2 - (fun j => (g j : ℝ)) ⬝ᵥ y ≤ (ℓ : ℝ) ∧
        oNorm y ≤ (((c.par.Rint : ℕ) : ℚ) : ℝ)) ↔ _
  rw [e1, Rat.cast_natCast]

/-- The region of a call of BL-O at the level `ℓ₀` for its quadratic `(H, g, k)`. -/
theorem regO_callO_k (K : Set (E d)) (c : CfgO d) (Hq : Matrix (Fin d) (Fin d) ℚ) (g : Fin d → ℚ) (ℓ0 kq r : ℚ)
    (P : Matrix (Fin d) (Fin d) ℚ) (f : Fin d → ℚ) (e : ℚ) (y : Fin d → ℝ) :
    y ∈ regO K c (callO c Hq g (ℓ0 - kq) r P f e) ↔
      y ∈ QKs K c (1 - c.par.eps)⁻¹ ∧ df2Phi (cM Hq) (cV g) kq y ≤ ℓ0 ∧ oNorm y ≤ c.par.Rint := by
  rw [regO_callO]
  unfold df2Phi
  push_cast
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, h3⟩

/-! ## P°'s rounds `u ≤ s` -/

namespace SettK

variable {n k : ℕ} {c : Df2Ctx d} {δ : ℝ} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ}

theorem hu' (S : SettK d n k c δ π s st ξ') {u : ℕ} (hu : u ≤ s) : u ≤ c.tau π (s + 1) := hu.trans S.hs'

theorem Y_le_u (S : SettK d n k c δ π s st ξ') {u : ℕ} (hu : u ≤ s) : |c.Y π u| ≤ BudK.Yb d n k := by
  obtain ⟨he, hg, -⟩ := S.det.evG u (S.hu' hu)
  have hgv := (S.det.adm u (S.det.le_tau_lt (S.hu' hu))).2 _ (S.det.play_keps u).2
  have hLg := S.bud.Lg_le
  have hLgb := NK.Lgb_ge d n k S.bud
  have h := ybar_real (c.pip π u) (gauge c.Kt (WithLp.toLp 2 (c.X π u))) (π.g u (WithLp.toLp 2 (c.play π u)))
    (π.e u) c.p.Le (BudK.Lgb d n k) c.p.eps S.det.rows.pos_eps (by rw [S.hp]; exact S.eps_le) rfl (gauge_nonneg _) hg
    hgv.1 hgv.2 (he.trans (Real.sqrt_le_sqrt (by rw [S.hp, S.hcn]; exact hLg))) hLgb S.det.one_le_Le
  unfold Df2Ctx.Y
  rw [S.hp] at h ⊢
  unfold BudK.Yb BudK.Le BudK.eps
  exact h

theorem xi_le_u (S : SettK d n k c δ π s st ξ') {u : ℕ} (hu : u ≤ s) : oNorm (π.xi u) ≤ BudK.Xi d n k :=
  NK.xi_norm S.det (S.hu' hu) S.hp S.hcn S.bud

theorem opN_PA_u (S : SettK d n k c δ π s st ξ') {u : ℕ} (hu : u ≤ s) :
    opN ((c.st π u).P * (c.st π u).A) ≤ Real.sqrt (BudK.Lam d n k) := by
  have hI := S.det.stInv_le_tau u (S.hu' hu)
  have hsym : (c.st π u).Pᵀ = (c.st π u).P := by
    have := hI.pd.isHermitian; rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hPS : (c.st π u).P * (c.st π u).S = 1 := mul_eq_one_comm.1 hI.SP
  have hsq : ((c.st π u).P * (c.st π u).A) * ((c.st π u).P * (c.st π u).A)ᵀ = (c.st π u).P := by
    rw [Matrix.transpose_mul, hsym, Matrix.mul_assoc, ← Matrix.mul_assoc (c.st π u).A, hI.AA, ← Matrix.mul_assoc,
      hPS, Matrix.one_mul]
  have htr : (c.st π u).P.trace ≤ BudK.Lam d n k := by
    have := AdversarialBco.Poly.trace_le_of_psd (S.det.P_le (S.hu' hu))
    rwa [inv_inv, S.de_c] at this
  rw [Real.le_sqrt (opN_nonneg _) S.Lam_pos.le]
  refine (opN_sq_le_trace _).trans ?_
  rw [hsq]; exact htr

/-- `|ĝ_u| ≤ 1.01 Ȳ Λ^{1/2} Ξ` for `u ≤ s`. -/
theorem ghat_le (S : SettK d n k c δ π s st ξ') {u : ℕ} (hu : u ≤ s) :
    oNorm (c.ghat π u) ≤ 101 / 100 * BudK.Yb d n k * Real.sqrt (BudK.Lam d n k) * BudK.Xi d n k := by
  have hl0 := S.lam_pos; have hl1 := S.lam_small
  have hp : c.p.lam = (poK d n k).lam := by rw [S.hp]
  have h1l : 0 < 1 - c.p.lam := by rw [hp]; linarith
  have hY := S.Y_le_u hu
  have hun : oNorm (c.u π u) ≤ Real.sqrt (BudK.Lam d n k) * BudK.Xi d n k := by
    have e : c.u π u = ((c.st π u).P * (c.st π u).A) *ᵥ π.xi u := by
      unfold Df2Ctx.u Df2Ctx.w; rw [Matrix.mulVec_mulVec]
    rw [e]
    exact (oNorm_mulVec_le _ _).trans (mul_le_mul (S.opN_PA_u hu) (S.xi_le_u hu) (oNorm_nonneg _)
      (Real.sqrt_nonneg _))
  unfold Df2Ctx.ghat
  rw [oNorm_smul, abs_div, abs_of_pos h1l]
  have hinv : 1 / (1 - c.p.lam) ≤ 101 / 100 := by
    rw [div_le_iff₀ h1l, hp]; nlinarith
  have hY0 : 0 ≤ BudK.Yb d n k := (abs_nonneg _).trans hY
  have hX0 : 0 ≤ Real.sqrt (BudK.Lam d n k) * BudK.Xi d n k := mul_nonneg (Real.sqrt_nonneg _) (NK.Xi_nonneg d n k)
  calc |c.Y π u| / (1 - c.p.lam) * oNorm (c.u π u)
      = |c.Y π u| * (1 / (1 - c.p.lam)) * oNorm (c.u π u) := by ring
    _ ≤ BudK.Yb d n k * (101 / 100) * (Real.sqrt (BudK.Lam d n k) * BudK.Xi d n k) :=
        mul_le_mul (mul_le_mul hY hinv (by positivity) hY0) hun (oNorm_nonneg _) (by positivity)
    _ = _ := by ring

/-- E11: `|Ĝ°_{s+1}| ≤ Ḡ`. -/
theorem Gn_le (S : SettK d n k c δ π s st ξ') : oNorm (c.Gn π s) ≤ BudK.Gb d n k := by
  rw [S.det.Gn_sum S.hs']
  refine (AdversarialBco.Poly.oNorm_sum_le' _ _).trans ?_
  refine (Finset.sum_le_sum fun u hu => S.ghat_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hu))).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn : ((s + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast S.hs
  have h0 : 0 ≤ 101 / 100 * BudK.Yb d n k * Real.sqrt (BudK.Lam d n k) * BudK.Xi d n k := by
    have := (abs_nonneg _).trans (S.Y_le_u le_rfl)
    have := NK.Xi_nonneg d n k
    positivity
  unfold BudK.Gb
  calc ((s + 1 : ℕ) : ℝ) * (101 / 100 * BudK.Yb d n k * Real.sqrt (BudK.Lam d n k) * BudK.Xi d n k)
      ≤ n * (101 / 100 * BudK.Yb d n k * Real.sqrt (BudK.Lam d n k) * BudK.Xi d n k) := mul_le_mul_of_nonneg_right hn h0
    _ = _ := by ring

/-- E11: `|l°_{s+1}| ≤ R Ḡ`. -/
theorem ln_le (S : SettK d n k c δ π s st ξ') : |c.ln π s| ≤ BudK.R d n k * BudK.Gb d n k := by
  have hI := S.inv
  have e : c.ln π s = ∑ u ∈ Finset.range (s + 1), c.ghat π u ⬝ᵥ (c.st π u).mu := by
    unfold Df2Ctx.ln; rw [hI.l, Finset.sum_range_succ]
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ u ∈ Finset.range (s + 1), |c.ghat π u ⬝ᵥ (c.st π u).mu| ≤
      101 / 100 * BudK.Yb d n k * Real.sqrt (BudK.Lam d n k) * BudK.Xi d n k * BudK.R d n k := by
    intro u hu
    have hu' : u ≤ s := Nat.lt_succ_iff.1 (Finset.mem_range.1 hu)
    have hmu : oNorm (c.st π u).mu ≤ BudK.R d n k := by
      have := S.det.norm_le_of_keps (S.det.stInv_le_tau u (S.hu' hu')).mu
      rwa [S.hp] at this
    exact (abs_dot_le _ _).trans (mul_le_mul (S.ghat_le hu') hmu (oNorm_nonneg _)
      ((oNorm_nonneg _).trans (S.ghat_le hu')))
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn : ((s + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast S.hs
  have hR : 0 ≤ BudK.R d n k := by
    have := S.det.norm_le_of_keps S.inv.mu; rw [S.hp] at this; exact (oNorm_nonneg _).trans this
  have h0 : 0 ≤ 101 / 100 * BudK.Yb d n k * Real.sqrt (BudK.Lam d n k) * BudK.Xi d n k * BudK.R d n k := by
    have := (abs_nonneg _).trans (S.Y_le_u le_rfl)
    have := NK.Xi_nonneg d n k
    positivity
  unfold BudK.Gb
  calc ((s + 1 : ℕ) : ℝ) * (101 / 100 * BudK.Yb d n k * Real.sqrt (BudK.Lam d n k) * BudK.Xi d n k * BudK.R d n k)
      ≤ n * (101 / 100 * BudK.Yb d n k * Real.sqrt (BudK.Lam d n k) * BudK.Xi d n k * BudK.R d n k) :=
        mul_le_mul_of_nonneg_right hn h0
    _ = _ := by ring

end SettK

/-! ## E12: the constant -/

/-- `e_Φ` from its three parts, for `j ≤ n` rounds of the fields. -/
theorem ePhi_geK {d n k : ℕ} (R DP eb ek a j : ℝ) (hR : R = BudK.R d n k) (hR0 : 0 ≤ R) (hDP : DP = BudK.DP d n k)
    (heb : eb = BudK.eb d n k) (hek : ek = BudK.ek d n k) (heb0 : 0 ≤ eb) (hek0 : 0 ≤ ek) (ha : a ≤ j * eb)
    (hj : j ≤ n) (hP : 0 ≤ DP) {x y z : ℝ} (hx : x ≤ DP) (hy : y ≤ a) (hz : z ≤ j * ek) :
    R ^ 2 / 2 * x + R * y + z ≤ BudK.ePhi d n k := by
  unfold BudK.ePhi
  rw [← hR, ← hDP, ← heb, ← hek]
  have h1 : R ^ 2 / 2 * x ≤ R ^ 2 / 2 * DP := mul_le_mul_of_nonneg_left hx (by positivity)
  have h2 : R * y ≤ R * (n * eb) := mul_le_mul_of_nonneg_left (hy.trans (ha.trans
    (mul_le_mul_of_nonneg_right hj heb0))) hR0
  have h3 : z ≤ n * ek := hz.trans (mul_le_mul_of_nonneg_right hj hek0)
  nlinarith

end AdversarialBco.Unified.EngC

namespace AdversarialBco.Unified.Eng.RCHypO

open AdversarialBco AdversarialBco.Poly
open AdversarialBco.Poly.LeanAp (oNorm_eq oNorm_add_le oNorm_sub_le oNorm_smul abs_dot_le oNorm_sq oNorm_nonneg
  oNorm_neg oNorm_sub_comm)
open AdversarialBco.Poly.Layer2 (kTh kTh_good)
open AdversarialBco.Unified.BLO AdversarialBco.Unified.Eng AdversarialBco.Unified.EngC AdversarialBco.Unified.Asm
open AdversarialBco.Unified.BudK (BudOK RunCaseK poK parK)
open AdversarialBco.Bit.BLP (Par St Mode init rnd sqrtDn rndM rndV frob2 cV cM opN LT Lmu rB eBL CallQ)
open AdversarialBco.Bit.BLP.RC
open AdversarialBco.BitRAM (toE)
open Matrix

variable {d : ℕ} {K : Set (E d)} {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d} {k : ℕ}
  {ap : ℕ → ApFun d} {π : Df2Path d} {s : ℕ} {st : St d} {ξ' : Fin d → ℚ} {ζ' : ℚ} {Z ε : ℝ} {f : E d → ℝ}

/-! ## BL-O's regions against `K_ε` -/

theorem eps_lt (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    BudK.eps d c.n k ≤ ((c.par.eps : ℚ) : ℝ) ∧ ((c.par.eps : ℚ) : ℝ) ≤ 1 / 2 ∧ BudK.eps d c.n k ≤ 1 / 4 ∧
      0 < BudK.eps d c.n k :=
  ⟨H.eps_relH.1, H.eps'_le, H.sett.eps_le, H.sett.eps_pos⟩

theorem body_convex (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : Convex ℝ (bodyS K c) :=
  convex_posBodyO H.frame.1 _ _

theorem zero_mem_body (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : (0 : E d) ∈ bodyS K c :=
  H.goodPos.1 (Metric.mem_closedBall_self zero_le_one)

theorem cast_inv_eps (c : CfgO d) : (((1 - c.par.eps)⁻¹ : ℚ) : ℝ) = (1 - ((c.par.eps : ℚ) : ℝ))⁻¹ := by
  push_cast; ring

/-- BL-O's K-part `QKs (1 - ε')⁻¹` lies in `K_ε`. -/
theorem keps_of_QK (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) {y : Fin d → ℝ}
    (hy : y ∈ QKs K c (1 - c.par.eps)⁻¹) : y ∈ (ctxO K c k ap).Keps := by
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  have h1 : 0 < 1 - BudK.eps d c.n k := by linarith
  have h1' : 0 < 1 - ((c.par.eps : ℚ) : ℝ) := by linarith
  have hy' : WithLp.toLp 2 ((1 - ((c.par.eps : ℚ) : ℝ))⁻¹ • y) ∈ bodyS K c := by
    have hy2 : WithLp.toLp 2 ((((1 - c.par.eps)⁻¹ : ℚ) : ℝ) • y) ∈ bodyS K c := hy
    rwa [cast_inv_eps] at hy2
  show WithLp.toLp 2 ((1 - BudK.eps d c.n k)⁻¹ • y) ∈ (ctxO K c k ap).Kt
  rw [H.Kt_eq]
  have ht0 : 0 ≤ (1 - ((c.par.eps : ℚ) : ℝ)) / (1 - BudK.eps d c.n k) := div_nonneg h1'.le h1.le
  have ht1 : (1 - ((c.par.eps : ℚ) : ℝ)) / (1 - BudK.eps d c.n k) ≤ 1 := (div_le_one h1).2 (by linarith)
  have e : WithLp.toLp 2 ((1 - BudK.eps d c.n k)⁻¹ • y) = ((1 - ((c.par.eps : ℚ) : ℝ)) / (1 - BudK.eps d c.n k)) •
      WithLp.toLp 2 ((1 - ((c.par.eps : ℚ) : ℝ))⁻¹ • y) := by
    rw [← WithLp.toLp_smul, smul_smul]
    congr 2
    field_simp
  rw [e]
  exact H.body_convex.smul_mem_of_zero_mem H.zero_mem_body hy' ⟨ht0, ht1⟩

/-- `κ K_ε` lies in BL-O's K-part, `κ = (1 - ε')/(1 - ε)`. -/
theorem QK_of_keps (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) {y : Fin d → ℝ}
    (hy : y ∈ (ctxO K c k ap).Keps) :
    ((1 - ((c.par.eps : ℚ) : ℝ)) / (1 - BudK.eps d c.n k)) • y ∈ QKs K c (1 - c.par.eps)⁻¹ := by
  obtain ⟨he, he', he4, he0⟩ := H.eps_lt
  have h1 : 0 < 1 - BudK.eps d c.n k := by linarith
  have h1' : 0 < 1 - ((c.par.eps : ℚ) : ℝ) := by linarith
  have hy' : WithLp.toLp 2 ((1 - BudK.eps d c.n k)⁻¹ • y) ∈ bodyS K c := by
    rw [← H.Kt_eq]; exact hy
  show WithLp.toLp 2 ((((1 - c.par.eps)⁻¹ : ℚ) : ℝ) •
    (((1 - ((c.par.eps : ℚ) : ℝ)) / (1 - BudK.eps d c.n k)) • y)) ∈ bodyS K c
  have e : (((1 - c.par.eps)⁻¹ : ℚ) : ℝ) • (((1 - ((c.par.eps : ℚ) : ℝ)) / (1 - BudK.eps d c.n k)) • y) =
      (1 - BudK.eps d c.n k)⁻¹ • y := by
    rw [smul_smul, cast_inv_eps]
    congr 1
    field_simp
  rw [e]; exact hy'

theorem keps_norm (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) {y : Fin d → ℝ}
    (hy : y ∈ (ctxO K c k ap).Keps) : oNorm y ≤ BudK.R d c.n k :=
  H.det.norm_le_of_keps hy

theorem R_le_Rint (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : BudK.R d c.n k ≤ (c.par.Rint : ℝ) :=
  H.R_le_par.trans H.parR_le_Rint

theorem R_ge (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : 1 ≤ BudK.R d c.n k := H.one_le_R

/-! ## E12: BL-O's quadratics against P°'s -/

theorem eb0 (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : 0 ≤ BudK.eb d c.n k := by
  have h := H.errb
  have h0 := oNorm_nonneg (cV (rvH orc c st ξ' ζ' ε f).b - (ctxO K c k ap).bn π s)
  have hs : (0 : ℝ) < s + 1 := by positivity
  by_contra hc; push_neg at hc; nlinarith

theorem ek0 (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : 0 ≤ BudK.ek d c.n k := by
  have h := H.errk
  have h0 := abs_nonneg ((((rvH orc c st ξ' ζ' ε f).k : ℚ) : ℝ) - (ctxO K c k ap).kn π s)
  have hs : (0 : ℝ) < s + 1 := by positivity
  by_contra hc; push_neg at hc; nlinarith

theorem DP0 (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : 0 ≤ BudK.DP d c.n k := by
  have := H.hb0; have := H.sett.Lam_pos; unfold BudK.DP; positivity

/-- E12 at round `s` (BL's state before the round against P°'s `Φ°_s`). -/
theorem phi_err_s (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) {y : Fin d → ℝ} (hy : oNorm y ≤ BudK.R d c.n k) :
    |df2Phi (cM st.B * (cM st.B)ᵀ) (cV st.b) st.k y -
      df2Phi ((ctxO K c k ap).st π s).P ((ctxO K c k ap).st π s).b
        ((ctxO K c k ap).st π s).k y| ≤ BudK.ePhi d c.n k := by
  have S := H.sett
  refine (phi_diff _ _ _ _ _ _ _ y hy).trans ?_
  have hs : (s : ℝ) ≤ c.n := by exact_mod_cast H.hs.le
  exact ePhi_geK _ _ _ _ _ (s : ℝ) rfl H.R0 rfl rfl rfl H.eb0 H.ek0 le_rfl hs H.DP0 H.P'_err.1 S.track.errb
    S.track.errk

/-- BL's `P'_+ = B'_+ B'_+ᵀ` against P°'s `P'`. -/
theorem Pp_err (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f)
    (O : C1OutK d c.n k c.par st ξ' (rvH orc c st ξ' ζ' ε f) (ctxO K c k ap) π s) :
    opN (cM (rvH orc c st ξ' ζ' ε f).B * (cM (rvH orc c st ξ' ζ' ε f).B)ᵀ -
        (ctxO K c k ap).Pn π s) ≤ BudK.DP d c.n k ∧
      opN (cM (rvH orc c st ξ' ζ' ε f).B * (cM (rvH orc c st ξ' ζ' ε f).B)ᵀ) ≤
        10201 / 10000 * BudK.Lam d c.n k := by
  have S := H.sett
  obtain ⟨H0, hB0, hH0⟩ := O.hB
  set cx := ctxO K c k ap
  have e : cM (rvH orc c st ξ' ζ' ε f).B * (cM (rvH orc c st ξ' ζ' ε f).B)ᵀ =
      (1 + H0) * cx.Pn π s * (1 + H0)ᵀ := by
    rw [hB0, Matrix.transpose_mul]
    calc (1 + H0) * (cx.Pn π s * cx.An π s) * ((cx.Pn π s * cx.An π s)ᵀ * (1 + H0)ᵀ) =
        (1 + H0) * ((cx.Pn π s * cx.An π s) * (cx.Pn π s * cx.An π s)ᵀ) * (1 + H0)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [S.PnAn_sq]
  have hPn : opN (cx.Pn π s) ≤ BudK.Lam d c.n k := by
    have h := opN_mul_le (cx.Pn π s * cx.An π s) (cx.Pn π s * cx.An π s)ᵀ
    rw [S.PnAn_sq, opN_transpose] at h
    have h2 := S.opN_PnAn
    have h0 := opN_nonneg (cx.Pn π s * cx.An π s)
    have : Real.sqrt (BudK.Lam d c.n k) * Real.sqrt (BudK.Lam d c.n k) = BudK.Lam d c.n k := Real.mul_self_sqrt S.Lam_pos.le
    nlinarith
  rw [e]
  have hb := H.bud.hb_le
  have hb0 := H.hb0
  have hT : BudK.hTr d c.n k (s + 1) ≤ BudK.hb d c.n k := H.bud.hTr_le (s + 1) H.hs
  obtain ⟨h1, h2⟩ := PP_err _ _ _ _ (hH0.trans hT) hPn
  refine ⟨h1.trans (le_of_eq (by unfold BudK.DP; ring)), h2.trans ?_⟩
  have : (1 + BudK.hb d c.n k) ^ 2 ≤ 10201 / 10000 := by nlinarith
  exact mul_le_mul_of_nonneg_right this S.Lam_pos.le

/-- E12 at round `s + 1` (BL's new fields against P°'s `Φ'`). -/
theorem phi_err_n (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f)
    (O : C1OutK d c.n k c.par st ξ' (rvH orc c st ξ' ζ' ε f) (ctxO K c k ap) π s)
    {y : Fin d → ℝ} (hy : oNorm y ≤ BudK.R d c.n k) :
    |df2Phi (cM (rvH orc c st ξ' ζ' ε f).B * (cM (rvH orc c st ξ' ζ' ε f).B)ᵀ)
        (cV (rvH orc c st ξ' ζ' ε f).b) (rvH orc c st ξ' ζ' ε f).k y -
      (ctxO K c k ap).PhiN π s y| ≤ BudK.ePhi d c.n k := by
  refine (phi_diff _ _ _ _ _ _ _ y hy).trans ?_
  have hs : (s : ℝ) + 1 ≤ c.n := by exact_mod_cast H.hs
  exact ePhi_geK _ _ _ _ _ ((s : ℝ) + 1) rfl H.R0 rfl rfl rfl H.eb0 H.ek0 le_rfl hs H.DP0 (H.Pp_err O).1 O.errb O.errk

theorem rho_pos (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : 0 < BudK.rho d c.n k := H.det.rows.pos_rho

theorem wr0 (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) : 0 ≤ BudK.wr d c.n k := by
  have := H.rho_pos; have := NK.tp_pos d c.n k; unfold BudK.wr; positivity

/-- `ρ - w_ρ ≤ ρ' ≤ ρ` (Lemma ENC). -/
theorem rho_enc (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    (c.par.rho : ℝ) ≤ BudK.rho d c.n k ∧ BudK.rho d c.n k - BudK.wr d c.n k ≤ (c.par.rho : ℝ) := by
  have hρ := H.rho_pos
  rw [H.par]
  refine ⟨H.bud.enc.rho_le, ?_⟩
  have h := (abs_le.1 H.bud.enc.rho_rel).1
  have e : ((parK d c.n k).rho : ℝ) = (((parK d c.n k).rho : ℝ) / BudK.rho d c.n k) * BudK.rho d c.n k := by
    field_simp
  unfold BudK.wr
  rw [e]
  nlinarith

/-- The two levels of the test region: BL's `L_T = 7.99 ρ' - ê` against P°'s `(c₁ - γ) ρ`, with the drop
`D = e_Φ + ê + 8 w_ρ` of the gap. -/
theorem LT_lev (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    ((LT c.par : ℚ) : ℝ) + BudK.ePhi d c.n k ≤
        ((ctxO K c k ap).p.c1 - (ctxO K c k ap).p.gam) * (ctxO K c k ap).p.rho ∧
      ((ctxO K c k ap).p.c1 - (ctxO K c k ap).p.gam) * (ctxO K c k ap).p.rho -
          (BudK.ePhi d c.n k + BudK.eh d c.n k + 8 * BudK.wr d c.n k) + BudK.ePhi d c.n k ≤ ((LT c.par : ℚ) : ℝ) := by
  rw [LT_cast, H.det.c1, H.det.gam]
  obtain ⟨h1, h2⟩ := H.rho_enc
  have h3 := H.bud.ePhi_le
  have h4 := H.wr0
  have e : ((c.par.eHat : ℚ) : ℝ) = BudK.eh d c.n k := by rw [H.par]; rfl
  rw [e]
  have e2 : (ctxO K c k ap).p.rho = BudK.rho d c.n k := rfl
  rw [e2]
  constructor <;> nlinarith

/-- The two levels of line μ: BL's `L_μ = 8 ρ' - ê` against P°'s `c₁ ρ`. -/
theorem Lmu_lev (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) :
    ((Lmu c.par : ℚ) : ℝ) + BudK.ePhi d c.n k ≤ (ctxO K c k ap).p.c1 * (ctxO K c k ap).p.rho ∧
      (ctxO K c k ap).p.c1 * (ctxO K c k ap).p.rho -
          (BudK.ePhi d c.n k + BudK.eh d c.n k + 8 * BudK.wr d c.n k) + BudK.ePhi d c.n k ≤ ((Lmu c.par : ℚ) : ℝ) := by
  rw [Lmu_cast, H.det.c1]
  obtain ⟨h1, h2⟩ := H.rho_enc
  have h3 := H.bud.ePhi_le
  have h4 := H.wr0
  have e : ((c.par.eHat : ℚ) : ℝ) = BudK.eh d c.n k := by rw [H.par]; rfl
  rw [e]
  have e2 : (ctxO K c k ap).p.rho = BudK.rho d c.n k := rfl
  rw [e2]
  constructor <;> nlinarith

/-- A point of BL-O's region of a call at the level `ℓ₀` is in `K_ε` and under P°'s level `L`. -/
theorem in_of_region (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) (Hq : Matrix (Fin d) (Fin d) ℚ)
    (g : Fin d → ℚ) (ℓ0 kq r : ℚ) (P : Matrix (Fin d) (Fin d) ℚ) (fq : Fin d → ℚ) (e : ℚ)
    (Po : Matrix (Fin d) (Fin d) ℝ) (bo : Fin d → ℝ) (ko : ℝ)
    (herr : ∀ y, oNorm y ≤ BudK.R d c.n k → |df2Phi (cM Hq) (cV g) kq y - df2Phi Po bo ko y| ≤ BudK.ePhi d c.n k)
    (L : ℝ) (hL : (ℓ0 : ℝ) + BudK.ePhi d c.n k ≤ L) {y : Fin d → ℝ}
    (hy : y ∈ regO K c (callO c Hq g (ℓ0 - kq) r P fq e)) :
    y ∈ (ctxO K c k ap).Keps ∧ df2Phi Po bo ko y ≤ L := by
  obtain ⟨h1, h2, -⟩ := (regO_callO_k K c _ _ _ _ _ _ _ _ y).1 hy
  have hk := H.keps_of_QK h1
  have := (abs_le.1 (herr y (H.keps_norm hk))).1
  exact ⟨hk, by linarith⟩

/-- A point of BL-O's K-part under P°'s level `L - D` is in BL-O's region at the level `ℓ₀`. -/
theorem region_of_in (H : RCHypO K orc c k ap π s st ξ' ζ' Z ε f) (Hq : Matrix (Fin d) (Fin d) ℚ)
    (g : Fin d → ℚ) (ℓ0 kq r : ℚ) (P : Matrix (Fin d) (Fin d) ℚ) (fq : Fin d → ℚ) (e : ℚ)
    (Po : Matrix (Fin d) (Fin d) ℝ) (bo : Fin d → ℝ) (ko : ℝ)
    (herr : ∀ y, oNorm y ≤ BudK.R d c.n k → |df2Phi (cM Hq) (cV g) kq y - df2Phi Po bo ko y| ≤ BudK.ePhi d c.n k)
    (L D : ℝ) (hL : L - D + BudK.ePhi d c.n k ≤ (ℓ0 : ℝ)) {y : Fin d → ℝ}
    (hy : y ∈ QKs K c (1 - c.par.eps)⁻¹) (hΦ : df2Phi Po bo ko y ≤ L - D) :
    y ∈ regO K c (callO c Hq g (ℓ0 - kq) r P fq e) := by
  have hk := H.keps_of_QK hy
  have hR := H.keps_norm hk
  have := (abs_le.1 (herr y hR)).2
  exact (regO_callO_k K c _ _ _ _ _ _ _ _ y).2 ⟨hy, by linarith, hR.trans H.R_le_Rint⟩

end AdversarialBco.Unified.Eng.RCHypO
