/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLTailSpec
public import AdversarialBco.Bit.Transfer.XBLR13
public import AdversarialBco.Bit.Transfer.XBLRt
public import AdversarialBco.Bit.Transfer.XBLEll

@[expose] public section

/-!
# The tail of BL's round, part a: the pure links and the cells of the tail

* The parameters that the tail reads lie on the grid `2^{-pF}` (`η'`, `ρ'`, `W'`), `ê = 1/H` with `H` a power of two.
* The modes of the tail's stages (`m14`, `m13`, `m12`, `m11`): `tailMode` is R10's test, then `m11` (`tailMode_eq`).
* The calls: `callTOf` as `callOf` with the data of `DataT`; `apQ` from `ellRI`.
* R12 and R13 on the integers the machine computes (`tl_r12_dec`, `tl_wmu`, `tl_r13_dec`); the point of a call is
  at most `2^(X + E)` when `R_int ≤ 2^E` (`tl_pt_abs`).
* `TIn`: the cells that the tail reads (BLInv at `E`, the points, the slots `41..43, 59, 63, 72`, the arrays
  `25..29`), stable under every frame of the tail's segments (`TIn.frame`).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## The parameters on the grid -/

theorem tl_onG_eta (d n : ℕ) : OnG (par d n).pF (par d n).eta := onG_div_pow _ _

theorem tl_onG_rho (d n : ℕ) : OnG (par d n).pF (par d n).rho := onG_div_pow _ _

theorem tl_onG_W (d n : ℕ) : OnG (par d n).pF (par d n).W := onG_div_pow _ _

/-- `1/ê` as an integer. -/
def tlH (d n : ℕ) : ℤ := 2 ^ ((par d n).p - 3 * (BLP.Ne d n).size - 6 * d.size - 64)

theorem tlH_pos (d n : ℕ) : 0 < tlH d n := by unfold tlH; positivity

theorem tl_eHat (d n : ℕ) : (par d n).eHat = 1 / ((tlH d n : ℤ) : ℚ) := by
  rw [tlH]; push_cast; rfl

theorem tlH_eq (d n : ℕ) : (((par d n).eHat⁻¹ : ℚ) : ℝ) = ((tlH d n : ℤ) : ℝ) := by
  rw [tl_eHat, one_div, inv_inv]; push_cast; rfl

/-- A point of the grid as its numerator over `2^k`. -/
theorem tl_grid (k : ℕ) {x : ℚ} (h : OnG k x) : x = ((qn k x : ℤ) : ℚ) / (((2 : ℤ) ^ k : ℤ) : ℚ) := by
  push_cast; exact eq_qn_div k h

/-! ## The modes of the stages -/

/-- R14 LINE and R15 COMMIT. -/
def m14 (cfg : Cfg d) (n : ℕ) (Ap Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ) (kp lp : ℚ)
    (wmu : Fin d → ℚ) : Mode d :=
  match RoutinesQ.ap (callLOf cfg n Bp bp kp wmu) with
  | none => .guard
  | some mu' => .run ⟨false, mu', Ap, Bp, bp, kp, Gp, lp⟩

/-- R13's guard, then R14 and R15. -/
def m13 (cfg : Cfg d) (n : ℕ) (Ap Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ) (kp lp : ℚ)
    (wmu : Fin d → ℚ) : Mode d :=
  if (2 * cfg.par.W) ^ 2 < wmu ⬝ᵥ wmu then .guard else m14 cfg n Ap Bp bp Gp kp lp wmu

/-- R12 FIRE at the test point `p'`, then R13 to R15. -/
def m12 (cfg : Cfg d) (n : ℕ) (Ap Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ) (kp lp : ℚ)
    (wmu p' : Fin d → ℚ) : Mode d :=
  if cfg.par.eta * (lp - Gp ⬝ᵥ p') - 2 * (p' ⬝ᵥ ((Bp * Bpᵀ) *ᵥ p') / 2 - bp ⬝ᵥ p' + kp) ≤
      -cfg.par.rho + cfg.par.eHat then .run (init cfg.par d) else m13 cfg n Ap Bp bp Gp kp lp wmu

/-- R11 TEST, then R12 to R15. -/
def m11 (cfg : Cfg d) (n : ℕ) (st : St d) (Ap Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ) (kp lp : ℚ)
    (wmu : Fin d → ℚ) : Mode d :=
  match RoutinesQ.ap (callTOf cfg st Bp bp Gp) with
  | none => .guard
  | some p' => m12 cfg n Ap Bp bp Gp kp lp wmu p'

theorem tailMode_eq (cfg : Cfg d) (n : ℕ) (st : St d) (Ap Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ)
    (kp lp : ℚ) (wmu : Fin d → ℚ) :
    tailMode RoutinesQ.ap cfg n st Ap Bp bp Gp kp lp wmu =
      if 2 * (cfg.par.Lam : ℚ) < frob2 Bp ∨ 2 * (cfg.par.Lam : ℚ) < frob2 Ap then .guard else
        m11 cfg n st Ap Bp bp Gp kp lp wmu := by
  unfold tailMode m11 m12 m13 m14
  rfl

/-! ## The calls -/

theorem tl_callT (cfg : Cfg d) (st : St d) (Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ) :
    callTOf cfg st Bp bp Gp =
      callOf cfg (if st.first then 0 else st.B * st.Bᵀ) (if st.first then 0 else st.b)
        (if st.first then 0 else LT cfg.par - st.k) (if st.first then 1 - cfg.par.eps else BLP.rB cfg.par / 2)
        (Bp * Bpᵀ) (bp - (cfg.par.eta / 2) • Gp)
        (if st.first then (1 - cfg.par.eps) ^ 2 / (cfg.par.Ne * d * 8)
          else BLP.rB cfg.par ^ 2 / (cfg.par.Ne * d * 8)) := by
  unfold callTOf; cases st.first <;> rfl

theorem tl_ap_none (D : CallQ d) (h : ellRI (clearQ D) = none) : RoutinesQ.ap D = none := by
  show apQ D = none
  unfold apQ; rw [h]; rfl

theorem tl_ap_some (D : CallQ d) (x : Fin d → ℤ) (h : ellRI (clearQ D) = some x) :
    RoutinesQ.ap D = some fun i => (x i : ℚ) / 2 ^ ellExp (clearQ D) := by
  show apQ D = _
  unfold apQ; rw [h]; rfl

/-- The point of a call is in the box of radius `R_int`. -/
theorem tl_pt_abs (cfg : Cfg d) (H : Matrix (Fin d) (Fin d) ℚ) (g : Fin d → ℚ) (ℓq r : ℚ)
    (P : Matrix (Fin d) (Fin d) ℚ) (f : Fin d → ℚ) (e : ℚ) (x : Fin d → ℤ) (E : ℕ)
    (h : ellRI (clearQ (callOf cfg H g ℓq r P f e)) = some x) (hR : (cfg.par.Rint : ℤ) ≤ 2 ^ E) (j : Fin d) :
    |x j| ≤ 2 ^ (ellExp (clearQ (callOf cfg H g ℓq r P f e)) + E) := by
  have hb := ellRI_box _ x h
  have hR' : (clearQ (callOf cfg H g ℓq r P f e)).R = ((cfg.par.Rint : ℕ) : ℚ) := rfl
  rw [hR', Rat.num_natCast, Rat.den_natCast] at hb
  have h1 := num_le_of_box x 1 (cfg.par.Rint : ℤ) _ one_pos (by positivity) (by simpa using hb) j
  rw [pow_add]
  have h2 : (0 : ℤ) ≤ 2 ^ ellExp (clearQ (callOf cfg H g ℓq r P f e)) := by positivity
  calc |x j| = |x j| * 1 := (mul_one _).symm
    _ ≤ _ := h1
    _ ≤ _ := mul_le_mul_of_nonneg_left hR h2

/-! ## R12 and R13 on the machine's integers -/

/-- **R12's test** on the numerators. -/
theorem tl_r12_dec (P : Par) (Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp p' : Fin d → ℚ) (kp lp : ℚ)
    (F Q D H eh rh lh kh : ℤ) (Bh : Matrix (Fin d) (Fin d) ℤ) (bh Gh x : Fin d → ℤ)
    (hF : 0 < F) (hQ : 0 < Q) (hD : 0 < D) (hH : 0 < H)
    (eE : P.eta = (eh : ℚ) / F) (eR : P.rho = (rh : ℚ) / F) (eHt : P.eHat = 1 / (H : ℚ))
    (eB : Bp = Matrix.of fun a b => (Bh a b : ℚ) / Q) (eb : bp = fun k => (bh k : ℚ) / Q)
    (eG : Gp = fun k => (Gh k : ℚ) / Q) (ek : kp = (kh : ℚ) / Q) (el : lp = (lh : ℚ) / Q)
    (ex : p' = fun k => (x k : ℚ) / D) :
    (P.eta * (lp - Gp ⬝ᵥ p') - 2 * (p' ⬝ᵥ ((Bp * Bpᵀ) *ᵥ p') / 2 - bp ⬝ᵥ p' + kp) ≤ -P.rho + P.eHat) ↔
      eh * (lh * D - Gh ⬝ᵥ x) * Q * D * H -
          F * H * ((Bhᵀ *ᵥ x) ⬝ᵥ (Bhᵀ *ᵥ x) - (bh ⬝ᵥ x) * Q * D - (bh ⬝ᵥ x) * Q * D + kh * Q * D * D +
            kh * Q * D * D) ≤
        (F - rh * H) * Q * Q * D * D := by
  subst eB eb eG ek el ex
  rw [eE, eR, eHt]
  exact r12_mach F Q D H eh lh kh rh Bh Gh bh x hF hQ hD hH

/-- `w_μ` over the denominator the machine computes. -/
theorem tl_wmu (P : Par) (st : St d) (s5 : ℤ) (Γ mu : Fin d → ℤ) (Dm : ℤ) (Ah : Matrix (Fin d) (Fin d) ℤ)
    (hDm : 0 < Dm) (hmu : ∀ j, (mu j : ℚ) / Dm = st.mu j) (hA : ∀ i j, OnG P.p (st.A i j))
    (hAh : ∀ i j, Ah i j = qn P.p (st.A i j)) :
    wmuOf P st s5 Γ = fun j =>
      ((mu j * 2 ^ P.p * 2 ^ P.p * 2 ^ (2 * gsm_prec P.B) - s5 * (Ah *ᵥ Γ) j * Dm : ℤ) : ℚ) /
        ((Dm * 2 ^ P.p * 2 ^ P.p * 2 ^ (2 * gsm_prec P.B) : ℤ) : ℚ) := by
  have hQ : (0 : ℤ) < 2 ^ P.p := by positivity
  have hG : (0 : ℤ) < 2 ^ (2 * gsm_prec P.B) := by positivity
  have h := (r13_s5w 1 (2 ^ P.p) (2 ^ (2 * gsm_prec P.B)) Dm 1 0 0 0 s5 0 Ah Γ mu one_pos hQ hG hDm one_pos).2.1
  have eA : st.A = Matrix.of fun a b => ((Ah a b : ℤ) : ℚ) / (((2 : ℤ) ^ P.p : ℤ) : ℚ) := by
    ext i j
    rw [Matrix.of_apply, hAh, ← tl_grid P.p (hA i j)]
  have emu : st.mu = fun k => (mu k : ℚ) / Dm := funext fun k => (hmu k).symm
  funext j
  have hj := h j
  unfold wmuOf
  rw [eA, emu]
  push_cast at hj ⊢
  rw [hj]
  congr 1 <;> ring

/-- **R13's guard** on the numerators. -/
theorem tl_r13_dec (P : Par) (st : St d) (s5 : ℤ) (Γ mu : Fin d → ℤ) (Dm F Wh : ℤ) (Ah : Matrix (Fin d) (Fin d) ℤ)
    (hDm : 0 < Dm) (hF : 0 < F) (hmu : ∀ j, (mu j : ℚ) / Dm = st.mu j) (hA : ∀ i j, OnG P.p (st.A i j))
    (hAh : ∀ i j, Ah i j = qn P.p (st.A i j)) (hW : P.W = (Wh : ℚ) / F) :
    (2 * P.W) ^ 2 < wmuOf P st s5 Γ ⬝ᵥ wmuOf P st s5 Γ ↔
      4 * Wh * Wh * (Dm * 2 ^ P.p * 2 ^ P.p * 2 ^ (2 * gsm_prec P.B)) *
          (Dm * 2 ^ P.p * 2 ^ P.p * 2 ^ (2 * gsm_prec P.B)) <
        (fun j => mu j * 2 ^ P.p * 2 ^ P.p * 2 ^ (2 * gsm_prec P.B) - s5 * (Ah *ᵥ Γ) j * Dm) ⬝ᵥ
          (fun j => mu j * 2 ^ P.p * 2 ^ P.p * 2 ^ (2 * gsm_prec P.B) - s5 * (Ah *ᵥ Γ) j * Dm) * F * F := by
  rw [tl_wmu P st s5 Γ mu Dm Ah hDm hmu hA hAh, hW]
  set Dw : ℤ := Dm * 2 ^ P.p * 2 ^ P.p * 2 ^ (2 * gsm_prec P.B) with hDwd
  set wn : Fin d → ℤ := fun j => mu j * 2 ^ P.p * 2 ^ P.p * 2 ^ (2 * gsm_prec P.B) - s5 * (Ah *ᵥ Γ) j * Dm with hwn
  have hDw : (0 : ℚ) < Dw := by rw [hDwd]; push_cast; positivity
  have edot : ((fun j => (wn j : ℚ) / Dw) ⬝ᵥ fun j => (wn j : ℚ) / Dw) = ((wn ⬝ᵥ wn : ℤ) : ℚ) / ((Dw : ℚ) ^ 2) := by
    simp only [dotProduct]; push_cast; rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : (2 * ((Wh : ℚ) / F)) ^ 2 = ((4 * Wh * Wh : ℤ) : ℚ) / ((F : ℚ) ^ 2) := by push_cast; ring
  have hF' : (0 : ℚ) < F := by exact_mod_cast hF
  rw [edot, e2, div_lt_div_iff₀ (by positivity) (by positivity)]
  have e3 : ((4 * Wh * Wh : ℤ) : ℚ) * (Dw : ℚ) ^ 2 = ((4 * Wh * Wh * Dw * Dw : ℤ) : ℚ) := by push_cast; ring
  have e4 : ((wn ⬝ᵥ wn : ℤ) : ℚ) * (F : ℚ) ^ 2 = ((wn ⬝ᵥ wn * F * F : ℤ) : ℚ) := by push_cast; ring
  rw [e3, e4, Int.cast_lt]

/-! ## The cells of the tail -/

/-- **The cells that the tail reads**, at the round `t`: BL's invariant at `E`, the points, the constants `1, 2, 4`,
the round's values `A'`, `B'`, `b'`, `G'`, `k'`, `l'` on the grid `2^{-p}` (numerators at most `2^E₁`), `ŝ5`, and
`Â Γ` in the array `aWv`. -/
structure TIn (L : Layout) (n m K0 E E1 : ℕ) (cfg : Cfg d) (st : St d) (t : ℕ) (P0 : ℕ → EuclideanSpace ℝ (Fin d))
    (Ap Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ) (kp lp : ℚ) (s5 : ℤ) (Γ : Fin d → ℤ) (σ : Env d) :
    Prop where
  inv : BLInv L n m K0 E cfg (.run st) t σ
  pts : σ.pts = P0
  c1 : σ.sc 41 = 1
  c2 : σ.sc 42 = 2
  c4 : σ.sc 43 = 4
  hA : ∀ i j : Fin d, σ.arr 26 (d * i + j) = qn cfg.par.p (Ap i j) ∧ OnG cfg.par.p (Ap i j) ∧
    |qn cfg.par.p (Ap i j)| ≤ 2 ^ E1
  hB : ∀ i j : Fin d, σ.arr 27 (d * i + j) = qn cfg.par.p (Bp i j) ∧ OnG cfg.par.p (Bp i j) ∧
    |qn cfg.par.p (Bp i j)| ≤ 2 ^ E1
  hb : ∀ j : Fin d, σ.arr 28 j = qn cfg.par.p (bp j) ∧ OnG cfg.par.p (bp j) ∧ |qn cfg.par.p (bp j)| ≤ 2 ^ E1
  hG : ∀ j : Fin d, σ.arr 29 j = qn cfg.par.p (Gp j) ∧ OnG cfg.par.p (Gp j) ∧ |qn cfg.par.p (Gp j)| ≤ 2 ^ E1
  hk : σ.sc 59 = qn cfg.par.p kp
  hkg : OnG cfg.par.p kp
  hkb : |qn cfg.par.p kp| ≤ 2 ^ E1
  hl : σ.sc 63 = qn cfg.par.p lp
  hlg : OnG cfg.par.p lp
  hlb : |qn cfg.par.p lp| ≤ 2 ^ E1
  hs : σ.sc 72 = s5
  hsb : |s5| ≤ 2 ^ E1
  hw : ∀ i : Fin d, σ.arr aWv i = ((fun i j => qn cfg.par.p (st.A i j) : Matrix (Fin d) (Fin d) ℤ) *ᵥ Γ) i
  hΓ : ∀ j, |Γ j| ≤ 2 ^ E1
  hE : E ≤ E1

/-- `TIn` under a frame that avoids its cells and reads no coin. -/
theorem TIn.frame {L : Layout} {n m K0 E E1 : ℕ} {cfg : Cfg d} {st : St d} {t : ℕ}
    {P0 : ℕ → EuclideanSpace ℝ (Fin d)} {Ap Bp : Matrix (Fin d) (Fin d) ℚ} {bp Gp : Fin d → ℚ} {kp lp : ℚ}
    {s5 : ℤ} {Γ : Fin d → ℤ} {σ σ' : Env d} {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop}
    (h : TIn L n m K0 E E1 cfg st t P0 Ap Bp bp Gp kp lp s5 Γ σ) (hF : FrameA S N Ar σ σ')
    (hS : ∀ y, S y → nSP ≤ y ∧ y ≠ 41 ∧ y ≠ 42 ∧ y ≠ 43 ∧ y ≠ 59 ∧ y ≠ 63 ∧ y ≠ 72)
    (hN : ∀ j, N j → 8 ≤ j) (hA : ∀ a k, Ar a k → nAP ≤ a ∧ (a < 25 ∨ 29 < a)) (hd : σ'.draws = σ.draws) :
    TIn L n m K0 E E1 cfg st t P0 Ap Bp bp Gp kp lp s5 Γ σ' := by
  have sc : ∀ y, (y = 41 ∨ y = 42 ∨ y = 43 ∨ y = 59 ∨ y = 63 ∨ y = 72) → σ'.sc y = σ.sc y := fun y hy =>
    hF.2.1 y fun hSy => by have := hS y hSy; omega
  have ar : ∀ a k, 25 ≤ a → a ≤ 29 → σ'.arr a k = σ.arr a k := fun a k h1 h2 =>
    hF.2.2.1 a k fun hAr => by have := hA a k hAr; omega
  refine ⟨h.inv.frame hF (fun y hy => (hS y hy).1) hN (fun a k hk => (hA a k hk).1) hd, by rw [hF.2.2.2.2, h.pts],
    by rw [sc 41 (by omega), h.c1], by rw [sc 42 (by omega), h.c2], by rw [sc 43 (by omega), h.c4],
    fun i j => by rw [ar 26 _ (by omega) (by omega)]; exact h.hA i j,
    fun i j => by rw [ar 27 _ (by omega) (by omega)]; exact h.hB i j,
    fun j => by rw [ar 28 _ (by omega) (by omega)]; exact h.hb j,
    fun j => by rw [ar 29 _ (by omega) (by omega)]; exact h.hG j,
    by rw [sc 59 (by omega), h.hk], h.hkg, h.hkb, by rw [sc 63 (by omega), h.hl], h.hlg, h.hlb,
    by rw [sc 72 (by omega), h.hs], h.hsb, fun i => by rw [ar aWv _ (by decide) (by decide)]; exact h.hw i, h.hΓ,
    h.hE⟩

/-- A persistent slot holding an integer is bounded by `2^E`. -/
theorem BLInv.slot_abs {L : Layout} {n m K0 E : ℕ} {cfg : Cfg d} {mo : Mode d} {t : ℕ} {σ : Env d}
    (h : BLInv L n m K0 E cfg mo t σ) {y : ℕ} (hy : y < nSP) {v : ℤ} (hv : σ.sc y = v) : |v| ≤ 2 ^ E := by
  obtain ⟨z, hz, bz⟩ := h.bnd.1 y hy
  rw [hv] at hz
  rw [Int.cast_injective hz]; exact bz

/-- A persistent array cell holding an integer is bounded by `2^E`. -/
theorem BLInv.arr_abs {L : Layout} {n m K0 E : ℕ} {cfg : Cfg d} {mo : Mode d} {t : ℕ} {σ : Env d}
    (h : BLInv L n m K0 E cfg mo t σ) {a k : ℕ} (ha : a < nAP) (hk : k < asz d) {v : ℤ} (hv : σ.arr a k = v) :
    |v| ≤ 2 ^ E := by
  obtain ⟨z, hz, bz⟩ := h.bnd.2 a ha k hk
  rw [hv] at hz
  rw [Int.cast_injective hz]; exact bz

end AdversarialBco.Bit.Transfer.BLM
