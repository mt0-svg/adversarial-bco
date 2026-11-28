/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.BLOGeom

@[expose] public section

/-!
# BL-OW as a pure function on `ℚ`

BL-OW is BL-O (Unified/BLOSpec.lean) with three changes, here in rationals.

* **PARAM-W** (`parOW`, `uOW`, `b0OW`, `y0OW`). The floor `N_0 = 15 · 2^17 d³ n⁴` (`n0O`) and its logarithm enclosed by
  Theorem U's routine at Theorem U's working bits `q`: `L_00 = lnQ q N_0 - lnErr q N_0 ≤ ln N_0 ≤ L_01 = lnQ q N_0 +
  lnErr q N_0` (`lf0`, `lf1`), and `l_2 = lnQ q 2 + lnErr q 2 ≥ ln 2` (`l2O`). The scaling
  `u' = up_p(1 + k_δ l_2/(7 d L_00))` (`uOW`) and its root `r_u = sqrtDn q u'` (`ruOW`). The thresholds
  `b0 = up_p(2d + 2 + 36 L_01)` (`b0OW`), `ι⁺ = up_p((r_n + 2^{-q})/(14500 d r_d (36 L_00)^5 r_u))` (`iotaOW`, an upper
  enclosure of `1/ε(u')`) and `y0 = up_p(10 + 18 ι⁺ + 10 sqrtUp_q(12 L_01))` (`y0OW`). The parameters `λ', η', ε', σ²',
  ρ', κ_c', ν', A_0, B_0` are those of Theorem U's PARAM (`parN`) with `L_f' = 36 L_00`, `L_f⁺ = 36 L_01` in place of
  `L_e'`, `L_e⁺`, the factor `r_u` in `η'` and `r_u + 2^{-q}` in `ε'`; every other field (the precisions, the coin
  count `B`, `N_e`, `Λ`, `R'`, `s_b'`, `W'`, `R_int`, `ê`) is `parO`'s, at the level `N_e = 2^{k_δ} N_0` (the level
  reading of the caps). There is no cap `u_cap`: `u' = u_up` on every input. In the case of
  the assembly (`ε(u_δ) ≤ 1/8`) the cap never binds, and off the case the program only has to meet the machine
  clauses; when `ε' > 1/2` the mode is `off`, as in BL-O.
* **R5w** (`ywQ`): after R5, `Y'^w = rnd_p(φ' clip(Y', y0))` with `φ' = min(1, max(0, b0 + 1 - |ξ'|²))`,
  `clip(Y', y0) = max(-y0, min(y0, Y'))`.
* R7 (`c' = κ_c' Y'^w`), R9 (`g' = rnd_p(Y'^w ν' u')`) and R13 (`s_5 = rnd_p(η' Y'^w ν'/q')`) read `Y'^w`
  (`stepOW`). Nothing else reads `Y'`.

The configuration is BL-O's `CfgO` at `parOW` (`cfgOW`): the position, the frame, the CM test, the gauge play, the
calls and the first mode are BL-O's functions. The run `trajOW` is `trajO` with `stepOW`; the coins, the draws and the
windows are BL-O's (`parOW` has `parO`'s `B` and the prologue is BL-O's).
-/

namespace AdversarialBco.UW.BLOW

open AdversarialBco AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Par St Mode init rnd up dn sqrtDn sqrtUp rndV rndM frob2 lnQ lnErr LT Lmu rB eBL
  CallQ)
open AdversarialBco.BitRAM (toE)
open AdversarialBco.BitRAMO (clip WeakMemOracle)
open Matrix

variable {d : ℕ}

/-! ## PARAM-W -/

/-- The floor `N_0 = 15 · 2^17 d³ n⁴`. -/
def n0O (d n : ℕ) : ℕ := NeO d n 0

/-- `L_00 = lnQ q N_0 - lnErr q N_0 ≤ ln N_0`. -/
def lf0 (d n : ℕ) (δ : ℚ) : ℚ := lnQ (parO d n δ).q (n0O d n) - lnErr (parO d n δ).q (n0O d n)

/-- `L_01 = lnQ q N_0 + lnErr q N_0 ≥ ln N_0`. -/
def lf1 (d n : ℕ) (δ : ℚ) : ℚ := lnQ (parO d n δ).q (n0O d n) + lnErr (parO d n δ).q (n0O d n)

/-- `l_2 = lnQ q 2 + lnErr q 2 ≥ ln 2`. -/
def l2O (d n : ℕ) (δ : ℚ) : ℚ := lnQ (parO d n δ).q 2 + lnErr (parO d n δ).q 2

/-- The scaling `u' = up_p(1 + k_δ l_2/(7 d L_00))`. -/
def uOW (d n : ℕ) (δ : ℚ) : ℚ := up (parO d n δ).p (1 + kDel δ * l2O d n δ / (7 * d * lf0 d n δ))

/-- `r_u = sqrtDn_q u' ≤ u'^{1/2}`. -/
def ruOW (d n : ℕ) (δ : ℚ) : ℚ := sqrtDn (parO d n δ).q (uOW d n δ)

/-- `ι⁺ = up_p((r_n + 2^{-q})/(14500 d r_d (36 L_00)^5 r_u)) ≥ 1/ε(u')`. -/
def iotaOW (d n : ℕ) (δ : ℚ) : ℚ :=
  up (parO d n δ).p ((sqrtDn (parO d n δ).q n + 1 / 2 ^ (parO d n δ).q) /
    (14500 * d * sqrtDn (parO d n δ).q d * (36 * lf0 d n δ) ^ 5 * ruOW d n δ))

/-- The weight threshold `b0 = up_p(2d + 2 + 36 L_01)`. -/
def b0OW (d n : ℕ) (δ : ℚ) : ℚ := up (parO d n δ).p (2 * d + 2 + 36 * lf1 d n δ)

/-- The clip threshold `y0 = up_p(10 + 18 ι⁺ + 10 sqrtUp_q(12 L_01))`. -/
def y0OW (d n : ℕ) (δ : ℚ) : ℚ :=
  up (parO d n δ).p (10 + 18 * iotaOW d n δ + 10 * sqrtUp (parO d n δ).q (12 * lf1 d n δ))

/-- **PARAM-W**: `parO` with the parameters of T4U at the floor `L_f` and the scaling `u'`. -/
def parOW (d n : ℕ) (δ : ℚ) : Par :=
  let P := parO d n δ
  let rn := sqrtDn P.q n
  let rd := sqrtDn P.q d
  let ru := ruOW d n δ
  let Le := 36 * lf0 d n δ
  let Lehi := 36 * lf1 d n δ
  let lam := rnd P.pF (1 / (725 * d * Le ^ 2))
  let eta := rnd P.pF (rd / (Le * rn * ru))
  let s := sqrtUp P.q (rnd P.pF (1 / (8 * Le)))
  { P with
    Le := Le
    eps := up P.pF (14500 * d * (rd + 1 / 2 ^ P.q) * Lehi ^ 5 * (ru + 1 / 2 ^ P.q) / rn)
    lam := lam
    eta := eta
    sig2 := rnd P.pF (1 / (8 * Le))
    rho := dn P.pF (1450 * d ^ 2 * Le ^ 3)
    kapc := rnd P.pF (eta * lam / (4 * (1 - lam) ^ 2))
    nu := rnd P.pF (1 / (1 - lam))
    A0 := rnd P.p s
    B0 := rnd P.p (1 / s) }

/-- `parOW` keeps `parO`'s fields outside the parameters of T4U. -/
theorem parOW_p (d n : ℕ) (δ : ℚ) : (parOW d n δ).p = (parO d n δ).p := rfl
theorem parOW_q (d n : ℕ) (δ : ℚ) : (parOW d n δ).q = (parO d n δ).q := rfl
theorem parOW_pF (d n : ℕ) (δ : ℚ) : (parOW d n δ).pF = (parO d n δ).pF := rfl
theorem parOW_Ne (d n : ℕ) (δ : ℚ) : (parOW d n δ).Ne = (parO d n δ).Ne := rfl
theorem parOW_Lam (d n : ℕ) (δ : ℚ) : (parOW d n δ).Lam = (parO d n δ).Lam := rfl
theorem parOW_R (d n : ℕ) (δ : ℚ) : (parOW d n δ).R = (parO d n δ).R := rfl
theorem parOW_sb (d n : ℕ) (δ : ℚ) : (parOW d n δ).sb = (parO d n δ).sb := rfl
theorem parOW_W (d n : ℕ) (δ : ℚ) : (parOW d n δ).W = (parO d n δ).W := rfl
theorem parOW_eHat (d n : ℕ) (δ : ℚ) : (parOW d n δ).eHat = (parO d n δ).eHat := rfl

theorem parOW_eps (d n : ℕ) (δ : ℚ) : (parOW d n δ).eps =
    up (parO d n δ).pF (14500 * d * (sqrtDn (parO d n δ).q d + 1 / 2 ^ (parO d n δ).q) * (36 * lf1 d n δ) ^ 5 *
      (ruOW d n δ + 1 / 2 ^ (parO d n δ).q) / sqrtDn (parO d n δ).q n) := rfl

/-! ## R5w and the round -/

/-- **R5w**: `Y'^w = rnd_p(φ' clip(Y', y0))`, `φ' = min(1, max(0, b0 + 1 - |ξ'|²))`. -/
def ywQ (p : ℕ) (b0 y0 : ℚ) (ξ : Fin d → ℚ) (Y : ℚ) : ℚ :=
  rnd p (min 1 (max 0 (b0 + 1 - ξ ⬝ᵥ ξ)) * max (-y0) (min y0 Y))

/-- The round of BL-OW after the play (R5 YOBS, R5w, R7 FACTOR to R15 COMMIT): `stepO` with `Y'^w` read by R7, R9
and R13. -/
def stepOW (b0 y0 : ℚ) (orc : (Fin d → ℚ) → ℕ → Bool) (c : CfgO d) (n : ℕ) (mo : Mode d) (ξ : Fin d → ℚ) (ζ : ℚ)
    (obs : ℤ) : Mode d :=
  match mo with
  | .off => .off
  | .guard => .guard
  | .run st =>
    let P := c.par
    let w := st.A *ᵥ ξ
    let X := XO c st ξ
    let pt := ptO orc c X
    -- R5 YOBS
    let Y := rnd P.p (pt * ((obs : ℚ) / 2 ^ P.p + ζ) / 2 + 2 * (pt - 1) / P.eps)
    -- R5w
    let Yw := ywQ P.p b0 y0 ξ Y
    -- R7 FACTOR
    let cc := P.kapc * Yw
    let a := 1 - cc
    let q := a + cc * (ξ ⬝ᵥ ξ)
    if a < 1 / 2 ∨ q < 1 / 2 then .guard else
    let s1 := sqrtDn P.p (1 / a)
    let s3 := sqrtDn P.p a
    let rq := sqrtDn P.p q
    let s2 := rnd P.p (cc / (s3 * rq * (s3 + rq)))
    let s4 := rnd P.p (cc / (s3 + rq))
    -- R8 PAIR
    let A' := rndM P.p (s1 • st.A - s2 • vecMulVec w ξ)
    let B' := rndM P.p (s3 • st.B + s4 • vecMulVec (st.B *ᵥ ξ) ξ)
    -- R9 INCR
    let u := st.B *ᵥ ξ
    let v := st.Bᵀ *ᵥ st.mu
    let b' := st.b + rndV P.p (cc • ((u ⬝ᵥ st.mu) • u - st.B *ᵥ v))
    let k' := st.k + rnd P.p (cc / 2 * ((u ⬝ᵥ st.mu) ^ 2 - v ⬝ᵥ v))
    let g := rndV P.p ((Yw * P.nu) • u)
    let G' := st.G + g
    let l' := st.l + rnd P.p (g ⬝ᵥ st.mu)
    -- R10 TRACE
    if 2 * (P.Lam : ℚ) < frob2 B' ∨ 2 * (P.Lam : ℚ) < frob2 A' then .guard else
    let Pp := B' * B'ᵀ
    let wp := b' - (P.eta / 2) • G'
    -- R11 TEST
    let callT : CallQ d :=
      if st.first then callO c 0 0 0 (1 - P.eps) Pp wp ((1 - P.eps) ^ 2 / (P.Ne * d * 8))
      else callO c (st.B * st.Bᵀ) st.b (LT P - st.k) (rB P / 2) Pp wp (rB P ^ 2 / (P.Ne * d * 8))
    match apO orc c callT with
    | none => .guard
    | some p' =>
      -- R12 FIRE
      if P.eta * (l' - G' ⬝ᵥ p') - 2 * (p' ⬝ᵥ (Pp *ᵥ p') / 2 - b' ⬝ᵥ p' + k') ≤ -P.rho + P.eHat then
        .run (init P d)
      else
      -- R13 WMU
      let s5 := rnd P.p (P.eta * Yw * P.nu / q)
      let wmu := st.mu - s5 • w
      if (2 * P.W) ^ 2 < wmu ⬝ᵥ wmu then .guard else
      -- R14 LINE
      match apO orc c (callO c Pp b' (Lmu P - k') (rB P / 2) Pp (Pp *ᵥ wmu) (eBL P d n)) with
      | none => .guard
      -- R15 COMMIT
      | some mu' => .run ⟨false, mu', A', B', b', k', G', l'⟩

/-! ## The prologue and the run -/

/-- BL-OW's configuration: BL-O's at `parOW`. -/
def cfgOW (d n : ℕ) (orc : (Fin d → ℚ) → ℕ → Bool) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (cs : ℕ → Bool) : CfgO d :=
  ⟨parOW d n δ, n, a, r0, R0, (posO d n orc δ r0 R0 a cs).1, (posO d n orc δ r0 R0 a cs).2⟩

/-- The configuration on the world `w`. -/
def cfgWW (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (w : BitRAMO.WorldO d) : CfgO d := cfgOW d n w.orc δ r0 R0 a w.cs

/-- BL-OW's run on the world `w`: the mode before round `t` and the points played in the rounds `< t`. -/
noncomputable def trajOW (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (w : BitRAMO.WorldO d) :
    ℕ → Mode d × (ℕ → Fin d → ℚ)
  | 0 => (mode0O w.orc (cfgWW d n δ r0 R0 a w), fun _ => 0)
  | t + 1 =>
    let c := cfgWW d n δ r0 R0 a w
    let prev := trajOW d n δ r0 R0 a w t
    let dr := drawO d n δ r0 R0 w.cs t
    let x := playPtO w.orc c prev.1 dr.1
    let o : ℤ := clip c.qO ⌊(2 : ℝ) ^ c.par.p * (w.f t (toE x) + w.noise t)⌋
    (stepOW (b0OW d n δ) (y0OW d n δ) w.orc c n prev.1 dr.1 dr.2 o, Function.update prev.2 t x)

/-- BL-OW's mode before round `t`. -/
noncomputable def modeOW (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (w : BitRAMO.WorldO d) (t : ℕ) : Mode d :=
  (trajOW d n δ r0 R0 a w t).1

/-- BL-OW's play of round `t`, a rational point. -/
noncomputable def playOW (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (w : BitRAMO.WorldO d) (t : ℕ) : Fin d → ℚ :=
  playPtO w.orc (cfgWW d n δ r0 R0 a w) (modeOW d n δ r0 R0 a w t) (drawO d n δ r0 R0 w.cs t).1

/-- BL-OW's reading of round `t`: `clip q ⌊2^p (f_t(x'_t) + noise_t)⌋`. -/
noncomputable def readOW (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (w : BitRAMO.WorldO d) (t : ℕ) : ℤ :=
  clip (cfgWW d n δ r0 R0 a w).qO
    ⌊(2 : ℝ) ^ (parO d n δ).p * (w.f t (toE (playOW d n δ r0 R0 a w t)) + w.noise t)⌋

theorem modeOW_succ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (w : BitRAMO.WorldO d) (t : ℕ) :
    modeOW d n δ r0 R0 a w (t + 1) = stepOW (b0OW d n δ) (y0OW d n δ) w.orc (cfgWW d n δ r0 R0 a w) n
      (modeOW d n δ r0 R0 a w t) (drawO d n δ r0 R0 w.cs t).1 (drawO d n δ r0 R0 w.cs t).2
      (readOW d n δ r0 R0 a w t) := rfl

/-! ## The plays are interior -/

theorem stepOW_run {b0 y0 : ℚ} {orc : (Fin d → ℚ) → ℕ → Bool} {c : CfgO d} {n : ℕ} {mo : Mode d} {ξ : Fin d → ℚ}
    {ζ : ℚ} {obs : ℤ} {st' : St d} (h : stepOW b0 y0 orc c n mo ξ ζ obs = .run st') : ∃ st, mo = .run st := by
  cases mo with
  | off => simp [stepOW] at h
  | guard => simp [stepOW] at h
  | run st => exact ⟨st, rfl⟩

theorem modeOW_run (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (w : BitRAMO.WorldO d) :
    ∀ (t : ℕ) (st : St d), modeOW d n δ r0 R0 a w t = .run st →
      ∃ st0, mode0O w.orc (cfgWW d n δ r0 R0 a w) = .run st0 := by
  intro t
  induction t with
  | zero => intro st h; exact ⟨st, h⟩
  | succ t ih =>
    intro st h
    simp only [modeOW, trajOW] at h
    obtain ⟨st1, h1⟩ := stepOW_run h
    exact ih st1 h1

theorem lf1_nonneg (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 ≤ lf1 d n δ := by
  have hne : 1 ≤ n0O d n := by
    unfold n0O NeO
    have : 0 < 15 * 2 ^ (17 + 0) * d ^ 3 * n ^ 4 := by positivity
    omega
  have hq : 1 ≤ (parO d n δ).q := by rw [parO_q]; omega
  have hL := Bit.PieceA.lnQ_err (parO d n δ).q (n0O d n) hq hne
  have hlog : 0 ≤ Real.log (n0O d n) := Real.log_nonneg (by exact_mod_cast hne)
  have h : (0 : ℝ) ≤ ((lf1 d n δ : ℚ) : ℝ) := by
    unfold lf1; push_cast
    linarith [(abs_le.1 hL).1]
  exact_mod_cast h

theorem ruOW_nonneg (d n : ℕ) (δ : ℚ) : 0 ≤ ruOW d n δ := by unfold ruOW sqrtDn; positivity

/-- `ε' ≥ 0` at PARAM-W (for `n = 0` the division by `sqrtDn q 0 = 0` gives `0`). -/
theorem eps_parOW_nonneg (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) : 0 ≤ (parOW d n δ).eps := by
  rw [parOW_eps]
  apply up_nonneg
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [sqrtDn]
  have h1 := lf1_nonneg d n δ hd hn
  have hru := ruOW_nonneg d n δ
  have hrn : 0 ≤ sqrtDn (parO d n δ).q n := by unfold sqrtDn; positivity
  have hrd : 0 ≤ sqrtDn (parO d n δ).q d := by unfold sqrtDn; positivity
  apply div_nonneg _ hrn
  positivity

/-- **The plays of BL-OW are interior** (`PlayIntO` for BL-OW): on every world, good position or not. -/
theorem playIntOW (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K : Set (E d)) (w : BitRAMO.WorldO d) (hd : 1 ≤ d)
    (hr0 : 0 < r0) (hK : Convex ℝ K) (hball : Metric.closedBall (toE a) (r0 : ℝ) ⊆ K) (horc : WeakMemOracle K w.orc)
    (t : ℕ) : toE (playOW d n δ r0 R0 a w t) ∈ interior K := by
  have hr0' : (0 : ℝ) < r0 := by exact_mod_cast hr0
  have ha : toE a ∈ interior K := by
    rw [mem_interior]
    exact ⟨Metric.ball (toE a) r0, Metric.ball_subset_closedBall.trans hball, Metric.isOpen_ball,
      Metric.mem_ball_self hr0'⟩
  unfold playOW
  rcases hm : modeOW d n δ r0 R0 a w t with _ | _ | st
  · exact ha
  · exact ha
  · obtain ⟨st0, h0⟩ := modeOW_run d n δ r0 R0 a w t st hm
    obtain ⟨hcross, heps⟩ := mode0O_run h0
    have hball' : Metric.closedBall (toE (cfgWW d n δ r0 R0 a w).a) ((cfgWW d n δ r0 R0 a w).r0 : ℝ) ⊆ K := hball
    have heps0 : 0 ≤ (cfgWW d n δ r0 R0 a w).par.eps := eps_parOW_nonneg d n δ hd
    exact play_int hK hd hr0' hball' horc hcross heps0 heps
      (XO (cfgWW d n δ r0 R0 a w) st (drawO d n δ r0 R0 w.cs t).1)

end AdversarialBco.UW.BLOW
