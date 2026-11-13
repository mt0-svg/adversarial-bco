/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLHeadM
public import AdversarialBco.Bit.Transfer.XBLHeadB
public import AdversarialBco.Bit.Transfer.XBLMag

@[expose] public section

/-!
# BL's round in mode `run` after R5: R7's tests, R7 to R9, the tail

`XV.runT`: from BL's invariant in mode `run` and the first line's values in the slots `45 + k` (R5, R7's scalars),
the command `xifS 0 51 guard (xifS 0 53 guard (xMid; xtail))` ends in BL's invariant with the mode `step` gives, for
any tail `xtail` that satisfies the frozen tail statement (`TailOK`, the body of `TailBL`).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-- The body of `TailBL` for one command. -/
def TailOK (xtail : Layout → XCmd) (C k nS nN nA : ℕ) : Prop :=
    ∀ (d : ℕ) (L : Layout) (w : BitRAM.World d) (n m M K0 E E1 ℓa ℓ t : ℕ) (A : Matrix (Fin m) (Fin d) ℚ)
      (b : Fin m → ℚ) (c : Fin d → ℚ) (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ) (st : St d)
      (Ap Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ) (kp lp : ℚ) (s5 : ℤ) (Γ : Fin d → ℤ)
      (P0 : ℕ → EuclideanSpace ℝ (Fin d)) (σ : Env d),
      1 ≤ d → 1 ≤ n → LayOK L d ℓa → BLLay L → blkBL.OK L nS nN nA → RealRAM.HeightLE A b M →
      OnG (par d n).pF (par d n).eps → 0 ≤ (par d n).eps → (par d n).eps ≤ 1 → E ≤ E1 →
      BLInv L n m K0 E (mkCfg d n m A b c S) (.run st) t σ → σ.pts = P0 →
      σ.sc 41 = 1 → σ.sc 42 = 2 → σ.sc 43 = 4 →
      (∀ i j : Fin d, σ.arr 26 (d * i + j) = qn (par d n).p (Ap i j) ∧ OnG (par d n).p (Ap i j) ∧
        |qn (par d n).p (Ap i j)| ≤ 2 ^ E1) →
      (∀ i j : Fin d, σ.arr 27 (d * i + j) = qn (par d n).p (Bp i j) ∧ OnG (par d n).p (Bp i j) ∧
        |qn (par d n).p (Bp i j)| ≤ 2 ^ E1) →
      (∀ j : Fin d, σ.arr 28 j = qn (par d n).p (bp j) ∧ OnG (par d n).p (bp j) ∧
        |qn (par d n).p (bp j)| ≤ 2 ^ E1) →
      (∀ j : Fin d, σ.arr 29 j = qn (par d n).p (Gp j) ∧ OnG (par d n).p (Gp j) ∧
        |qn (par d n).p (Gp j)| ≤ 2 ^ E1) →
      σ.sc 59 = qn (par d n).p kp → OnG (par d n).p kp → |qn (par d n).p kp| ≤ 2 ^ E1 →
      σ.sc 63 = qn (par d n).p lp → OnG (par d n).p lp → |qn (par d n).p lp| ≤ 2 ^ E1 →
      σ.sc 72 = s5 → |s5| ≤ 2 ^ E1 →
      (∀ i : Fin d, σ.arr aWv i = ((fun i j => qn (par d n).p (st.A i j) : Matrix (Fin d) (Fin d) ℤ) *ᵥ Γ) i) →
      (∀ j, |Γ j| ≤ 2 ^ E1) →
      (∀ mu' : Fin d → ℚ,
        tailMode RoutinesQ.ap (mkCfg d n m A b c S) n st Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ) =
          .run ⟨false, mu', Ap, Bp, bp, kp, Gp, lp⟩ →
        StBnd (par d n).p E (par d n).Rint ⟨false, mu', Ap, Bp, bp, kp, Gp, lp⟩ ∧
        ∀ x, ellRI (clearQ (callLOf (mkCfg d n m A b c S) n Bp bp kp (wmuOf (par d n) st s5 Γ))) = some x →
          (∀ j, |x j| ≤ 2 ^ E) ∧
          ellExp (clearQ (callLOf (mkCfg d n m A b c S) n Bp bp kp (wmuOf (par d n) st s5 Γ))) ≤ E) →
      C * (d + m + M.size + n.size + E1 + 1) ^ k ≤ ℓ → C * (d + m + M.size + n.size + E1 + 1) ^ k < 2 ^ ℓa →
      XRunsB L (ctxOf w n m A b) ℓa ℓ (xtail L) σ (C * (d + m + M.size + n.size + E1 + 1) ^ k)
        (RPost L n m K0 E (mkCfg d n m A b c S)
          (tailMode RoutinesQ.ap (mkCfg d n m A b c S) n st Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ)) t P0)

/-! ## Facts -/

/-- `ε' > 0`. -/
theorem eps_pos' {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 < (par d n).eps := by
  have hLe := Le_ge_one hd hn
  rw [PieceA.par_Le] at hLe
  have hee : 0 ≤ PieceA.ee d n := by unfold PieceA.ee lnErr; positivity
  have hL : 0 < 36 * (PieceA.L0 d n + PieceA.ee d n) := by linarith
  have hrn : 0 < sqrtDn (par d n).q n := by
    unfold sqrtDn
    apply div_pos _ (by positivity)
    have h1 : 1 ≤ ⌊(n : ℚ) * 4 ^ (par d n).q⌋₊ := by
      rw [Nat.one_le_floor_iff]
      have : (1 : ℚ) ≤ n := by exact_mod_cast hn
      have : (1 : ℚ) ≤ 4 ^ (par d n).q := one_le_pow₀ (by norm_num)
      nlinarith
    have : 0 < Nat.sqrt ⌊(n : ℚ) * 4 ^ (par d n).q⌋₊ := Nat.sqrt_pos.2 (by omega)
    exact_mod_cast this
  have hrd : 0 ≤ sqrtDn (par d n).q d := by unfold sqrtDn; positivity
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have hs : 0 < sqrtDn (par d n).q d + 1 / 2 ^ (par d n).q := by positivity
  have hx : 0 < 14500 * (d : ℚ) * (sqrtDn (par d n).q d + 1 / 2 ^ (par d n).q) *
      (36 * (PieceA.L0 d n + PieceA.ee d n)) ^ 5 / sqrtDn (par d n).q n :=
    div_pos (mul_pos (mul_pos (mul_pos (by norm_num) hd') hs) (pow_pos hL 5)) hrn
  rw [PieceA.par_eps]
  unfold up
  apply div_pos _ (by positivity)
  exact_mod_cast Int.ceil_pos.2 (mul_pos hx (by positivity))

/-- A persistent slot holding the integer `z`: `|z| ≤ 2^E`. -/
theorem BLInv.sc_abs {L : Layout} {n m K0 E : ℕ} {cfg : Cfg d} {mo : Mode d} {t : ℕ} {σ : Env d}
    (h : BLInv L n m K0 E cfg mo t σ) {y : ℕ} (hy : y < nSP) {z : ℤ} (hz : σ.sc y = z) : |z| ≤ 2 ^ E := by
  obtain ⟨z', e', b'⟩ := h.bnd.1 y hy
  have : z = z' := by exact_mod_cast hz.symm.trans e'
  rw [this]; exact b'

/-- A persistent array cell holding the integer `z`: `|z| ≤ 2^E`. -/
theorem BLInv.arr_abs {L : Layout} {n m K0 E : ℕ} {cfg : Cfg d} {mo : Mode d} {t : ℕ} {σ : Env d}
    (h : BLInv L n m K0 E cfg mo t σ) {a k : ℕ} (ha : a < nAP) (hk : k < asz d) {z : ℤ} (hz : σ.arr a k = z) :
    |z| ≤ 2 ^ E := by
  obtain ⟨z', e', b'⟩ := h.bnd.2 a ha k hk
  have : z = z' := by exact_mod_cast hz.symm.trans e'
  rw [this]; exact b'

theorem idx_lt (i j : Fin d) : d * i + j < asz d := by
  unfold asz; have := i.2; have := j.2; nlinarith

theorem idx1_lt (j : Fin d) : (j : ℕ) < asz d := by
  unfold asz; have := j.2; nlinarith

theorem pow_two_le {p E : ℕ} (h : |((2 : ℤ) ^ p)| ≤ 2 ^ E) : p ≤ E := by
  rw [abs_of_pos (by positivity)] at h
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℤ) < 2)).1 h

/-! ## R7's tests, R7 to R9, the tail -/

/-- R7's tests (`v1 6 > 0` or `v1 8 > 0` leave for `guard`), then R7's roots to R9 and the tail. -/
def xRunT (xtail : Layout → XCmd) (L : Layout) : XCmd :=
  xifS L sZ 51 (xG L) (xifS L sZ 53 (xG L) (.seq (xMid L) (xtail L)))

set_option maxHeartbeats 16000000 in
/-- **R7's tests, R7 to R9 and the tail** from BL's invariant in mode `run` at the round `t` (after R1 and the play)
and the first line's values in the slots `45 + k`: the invariant with the mode `step` gives. -/
theorem XV.runT {xtail : Layout → XCmd} {Ct kt nS nN nA : ℕ} (hT : TailOK xtail Ct kt nS nN nA)
    {L : Layout} {w : BitRAM.World d} {n m M K0 E U ℓa ℓ t : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    {c : Fin d → ℚ} {S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ} {st : St d} {σ : Env d}
    {P0 : ℕ → EuclideanSpace ℝ (Fin d)} {ξ : Fin d → ℚ} {ζ : ℚ} {obs gz pN pD : ℤ} {Γ : Fin d → ℤ}
    (hd1 : 1 ≤ d) (hn1 : 1 ≤ n) (hL : LayOK L d ℓa) (hlay : BLLay L) (hblk : blkBL.OK L nS nN nA)
    (hH : RealRAM.HeightLE A b M) (hI : BLInv L n m K0 E (mkCfg d n m A b c S) (.run st) t σ) (hp : σ.pts = P0)
    (he1 : (par d n).eps ≤ 1) (c1 : σ.sc 41 = 1) (c2 : σ.sc 42 = 2) (c4 : σ.sc 43 = 4)
    (eV : ∀ k < 9, σ.sc (45 + k) = v1 (2 ^ (par d n).p) (2 ^ (par d n).pF) (2 ^ (2 * gsm_prec (par d n).B))
      (qn (par d n).pF (par d n).eps) (qn (par d n).pF (par d n).kapc) gz pN pD (Γ ⬝ᵥ Γ) obs k)
    (eW : ∀ i : Fin d, σ.arr aWv i = ((fun i j => qn (par d n).p (st.A i j) : Matrix (Fin d) (Fin d) ℤ) *ᵥ Γ) i)
    (eX : ∀ j : Fin d, σ.arr aGam j = Γ j)
    (hξ : ξ = fun i => (Γ i : ℚ) / 2 ^ (2 * gsm_prec (par d n).B))
    (hζ : ζ = (gz : ℚ) / 2 ^ (2 * gsm_prec (par d n).B) / 2)
    (hpt : ptQ (mkCfg d n m A b c S) (XQ (mkCfg d n m A b c S) st ξ) = (pN : ℚ) / pD) (hD : 0 < pD)
    (hEU : E ≤ U) (hdU : d ≤ 2 ^ U) (bZ : |gz| ≤ 2 ^ U) (bN : |pN| ≤ 2 ^ U) (bD : |pD| ≤ 2 ^ U)
    (bO : |obs| ≤ 2 ^ U) (bΓ : ∀ j, |Γ j| ≤ 2 ^ U)
    (hnew : ∀ mu' : Fin d → ℚ, step RoutinesQ.ap (mkCfg d n m A b c S) n (.run st) ξ ζ obs =
        .run ⟨false, mu', rA' (mkCfg d n m A b c S) st ξ ζ obs, rB' (mkCfg d n m A b c S) st ξ ζ obs,
          rb' (mkCfg d n m A b c S) st ξ ζ obs, rk' (mkCfg d n m A b c S) st ξ ζ obs,
          rG' (mkCfg d n m A b c S) st ξ ζ obs, rl' (mkCfg d n m A b c S) st ξ ζ obs⟩ →
      StBnd (par d n).p E (par d n).Rint ⟨false, mu', rA' (mkCfg d n m A b c S) st ξ ζ obs,
          rB' (mkCfg d n m A b c S) st ξ ζ obs, rb' (mkCfg d n m A b c S) st ξ ζ obs,
          rk' (mkCfg d n m A b c S) st ξ ζ obs, rG' (mkCfg d n m A b c S) st ξ ζ obs,
          rl' (mkCfg d n m A b c S) st ξ ζ obs⟩ ∧
      ∀ x, ellRI (clearQ (rcallL (mkCfg d n m A b c S) st ξ ζ obs n)) = some x →
        (∀ j, |x j| ≤ 2 ^ E) ∧ ellExp (clearQ (rcallL (mkCfg d n m A b c S) st ξ ζ obs n)) ≤ E)
    (hT1 : 130 * U + 120 < ℓ) (hTa : 130 * U + 120 < 2 ^ ℓa) (hda : d * d + d < 2 ^ ℓa)
    (hTt : Ct * (d + m + M.size + n.size + (36 * U + 30) + 1) ^ kt ≤ ℓ)
    (hTta : Ct * (d + m + M.size + n.size + (36 * U + 30) + 1) ^ kt < 2 ^ ℓa) :
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xRunT xtail L) σ
      (2 + (2 + (midUnits d U + Ct * (d + m + M.size + n.size + (36 * U + 30) + 1) ^ kt)))
      (RPost L n m K0 E (mkCfg d n m A b c S) (step RoutinesQ.ap (mkCfg d n m A b c S) n (.run st) ξ ζ obs) t P0) := by
  have hlay' := hlay
  obtain ⟨hS, hN, hAr⟩ := hlay'
  simp only [oE, rEE, aWE] at hS hN hAr
  have hpar : (mkCfg d n m A b c S).par = par d n := rfl
  have hU : ∀ {a b : ℕ}, a ≤ b → (2 : ℤ) ^ a ≤ 2 ^ b := fun h => pow_le_pow_right₀ (by norm_num) h
  have hℓ2 : ∀ {a : ℕ}, a < ℓ → (2 : ℝ) ^ a < 2 ^ ℓ := fun h => pow_lt_pow_right₀ (by norm_num) h
  obtain ⟨r0, -, -, r3, -⟩ := hI.regs
  obtain ⟨c0, -, c2p, c2pF, c2g, -⟩ := hI.consts
  obtain ⟨p0, -, p2, -, p4, p5, -⟩ := hI.par
  obtain ⟨-, -, ⟨Dm, hDm, eDm, hmu⟩, hAst, hBst, hbst, ⟨hkst, hko⟩, hGst, ⟨hlst, hlo⟩⟩ := hI.mode
  choose muN hmuN using hmu
  -- the grid facts of the parameters
  have heps : OnG (par d n).pF (par d n).eps := by rw [PieceA.par_eps]; exact onG_up _ _
  have hkap : OnG (par d n).pF (par d n).kapc := by rw [PieceA.par_kapc]; exact onG_rnd_s _ _
  have heta : OnG (par d n).pF (par d n).eta := by rw [PieceA.par_eta]; exact onG_rnd_s _ _
  have hnu : OnG (par d n).pF (par d n).nu := by rw [PieceA.par_nu]; exact onG_rnd_s _ _
  have he0 : 0 < (par d n).eps := eps_pos' hd1 hn1
  have hp1 : 1 ≤ (par d n).p := by
    show 1 ≤ 10 * (BLP.Ne d n).size + 16 * d.size + 160
    omega
  -- R5 and R7's tests
  obtain ⟨hY, hc⟩ := head_Yc (mkCfg d n m A b c S) st ξ ζ obs pN pD gz Γ (2 * gsm_prec (par d n).B) hD hpt hζ hξ
    heps he0 hkap
  obtain ⟨t1, t2⟩ := head_tests (mkCfg d n m A b c S) st ξ ζ obs pN pD gz Γ (2 * gsm_prec (par d n).B) hξ hc
  rw [hpar] at hY hc t1 t2
  rw [show (2 : ℚ) ^ (par d n).p = (((2 : ℤ) ^ (par d n).p : ℤ) : ℚ) by push_cast; rfl] at hY
  -- the integers
  generalize hQ : (2 : ℤ) ^ (par d n).p = Q at eV hY hc t1 t2
  generalize hF : (2 : ℤ) ^ (par d n).pF = F at eV hY hc t1 t2
  generalize hG : (2 : ℤ) ^ (2 * gsm_prec (par d n).B) = G at eV hY hc t1 t2
  generalize heN : qn (par d n).pF (par d n).eps = eN at eV hY hc t1 t2
  generalize hkN : qn (par d n).pF (par d n).kapc = kN at eV hY hc t1 t2
  generalize hv : v1 Q F G eN kN gz pN pD (Γ ⬝ᵥ Γ) obs = v at eV t1 t2
  generalize hyh : yHat Q F G pN pD obs gz eN = yh at hY hc
  have h0 : v 0 = yh := by rw [← hv, v1_0, hyh]
  have h1 : v 1 = kN * yh := by rw [← hv, v1_1, hyh]
  have h2 : v 2 = F * Q := by rw [← hv, v1_2]
  have h3 : v 3 = F * Q - kN * yh := by rw [← hv, v1_3, hyh]
  have h4 : v 4 = G * G := by rw [← hv, v1_4]
  have h5 : v 5 = (F * Q - kN * yh) * (G * G) + kN * yh * (Γ ⬝ᵥ Γ) := by rw [← hv, v1_5, hyh]
  have h7 : v 7 = F * Q * (G * G) := by rw [← hv, v1_7]
  have hQ1 : 1 ≤ Q := by rw [← hQ]; exact one_le_pow₀ (by norm_num)
  have hF1 : 1 ≤ F := by rw [← hF]; exact one_le_pow₀ (by norm_num)
  have hG1 : 1 ≤ G := by rw [← hG]; exact one_le_pow₀ (by norm_num)
  have hD1 : 1 ≤ Dm := hDm
  -- the cells
  have eQ : σ.sc s2p = Q := by rw [← hQ, c2p]; push_cast; rfl
  have eF : σ.sc s2pF = F := by rw [← hF, c2pF]; push_cast; rfl
  have eG : σ.sc s2g = G := by rw [← hG, c2g]; push_cast; rfl
  have bsc : ∀ {y : ℕ} {z : ℤ}, y < nSP → σ.sc y = z → |z| ≤ 2 ^ U := fun hy hz =>
    (hI.sc_abs hy hz).trans (hU hEU)
  have barr : ∀ {a k : ℕ} {z : ℤ}, a < nAP → k < asz d → σ.arr a k = z → |z| ≤ 2 ^ U := fun ha hk hz =>
    (hI.arr_abs ha hk hz).trans (hU hEU)
  have bQ : |Q| ≤ 2 ^ U := bsc (by decide) eQ
  have bF : |F| ≤ 2 ^ U := bsc (by decide) eF
  have bG : |G| ≤ 2 ^ U := bsc (by decide) eG
  have bE : |eN| ≤ 2 ^ U := bsc (y := sEps) (by decide) (by rw [← heN]; exact p0)
  have bK : |kN| ≤ 2 ^ U := bsc (y := sKapc) (by decide) (by rw [← hkN]; exact p4)
  have bEh : |qn (par d n).pF (par d n).eta| ≤ 2 ^ U := bsc (by decide) p2
  have bNu : |qn (par d n).pF (par d n).nu| ≤ 2 ^ U := bsc (by decide) p5
  have bDm : |Dm| ≤ 2 ^ U := bsc (by decide) eDm
  have bk : |qn (par d n).p st.k| ≤ 2 ^ U := bsc (by decide) hkst
  have bl : |qn (par d n).p st.l| ≤ 2 ^ U := bsc (by decide) hlst
  have bA : ∀ i j : Fin d, |qn (par d n).p (st.A i j)| ≤ 2 ^ U := fun i j =>
    barr (by decide) (idx_lt i j) (hAst i j).1
  have bB : ∀ i j : Fin d, |qn (par d n).p (st.B i j)| ≤ 2 ^ U := fun i j =>
    barr (by decide) (idx_lt i j) (hBst i j).1
  have bb : ∀ j : Fin d, |qn (par d n).p (st.b j)| ≤ 2 ^ U := fun j =>
    barr (by decide) (idx1_lt j) (hbst j).1
  have bGh : ∀ j : Fin d, |qn (par d n).p (st.G j)| ≤ 2 ^ U := fun j =>
    barr (by decide) (idx1_lt j) (hGst j).1
  have bMu : ∀ j : Fin d, |muN j| ≤ 2 ^ U := fun j => barr (by decide) (idx1_lt j) (hmuN j).1
  have bGG : |Γ ⬝ᵥ Γ| ≤ 2 ^ (3 * U) := by
    have := dot_abs_le bΓ bΓ hdU; rwa [show U + U + U = 3 * U by ring] at this
  have bV : ∀ k < 9, |v k| ≤ 2 ^ ev U (sl1Et k) := by
    rw [← hv]; exact v1_bound bQ bF bG bE bK bZ bN bD bO bGG
  have bvℓ : ∀ k < 9, |((v k : ℤ) : ℝ)| < 2 ^ ℓ := fun k hk => by
    have h' : ev U (sl1Et k) < ℓ := by interval_cases k <;> simp [ev, sl1Et] <;> omega
    have : ((|v k| : ℤ) : ℝ) ≤ ((2 ^ ev U (sl1Et k) : ℤ) : ℝ) := by exact_mod_cast bV k hk
    rw [Int.cast_abs] at this; push_cast at this
    exact lt_of_le_of_lt this (hℓ2 h')
  have hz0 : |σ.sc sZ| < 2 ^ ℓ := by rw [c0]; simp
  have e51 : σ.sc 51 = ((v 6 : ℤ) : ℝ) := by simpa using eV 6 (by norm_num)
  have e53 : σ.sc 53 = ((v 8 : ℤ) : ℝ) := by simpa using eV 8 (by norm_num)
  have hstepG : ∀ (h : ra (mkCfg d n m A b c S) st ξ ζ obs < 1 / 2 ∨ rq (mkCfg d n m A b c S) st ξ ζ obs < 1 / 2),
      step RoutinesQ.ap (mkCfg d n m A b c S) n (.run st) ξ ζ obs = .guard := fun h => by
    rw [step_run_tail, if_pos h]
  -- the first test
  by_cases h6 : 0 < v 6
  · refine XV.mono (XV.ifS_t hL (by romega) (by romega) hz0 (by rw [e51]; exact bvℓ 6 (by norm_num))
      (by rw [c0, e51]; exact_mod_cast h6) (XV.guard hL hI hp (by omega))) (by omega) fun σ' h => ?_
    rwa [hstepG (Or.inl (t1.2 h6))]
  refine XV.mono (K := 2 + (midUnits d U + Ct * (d + m + M.size + n.size + (36 * U + 30) + 1) ^ kt) + 2)
    (XV.ifS_f hL (by romega) (by romega) hz0 (by rw [e51]; exact bvℓ 6 (by norm_num))
      (by rw [c0, e51]; exact_mod_cast h6) ?_) (by omega) fun σ' h => h
  -- the second test
  by_cases h8 : 0 < v 8
  · refine XV.mono (XV.ifS_t hL (by romega) (by romega) hz0 (by rw [e53]; exact bvℓ 8 (by norm_num))
      (by rw [c0, e53]; exact_mod_cast h8) (XV.guard hL hI hp (by omega))) (by omega) fun σ' h => ?_
    rwa [hstepG (Or.inr (t2.2 h8))]
  refine XV.mono (K := midUnits d U + Ct * (d + m + M.size + n.size + (36 * U + 30) + 1) ^ kt + 2)
    (XV.ifS_f hL (by romega) (by romega) hz0 (by rw [e53]; exact bvℓ 8 (by norm_num))
      (by rw [c0, e53]; exact_mod_cast h8) ?_) (by omega) fun σ' h => h
  have ha : ¬ ra (mkCfg d n m A b c S) st ξ ζ obs < 1 / 2 := fun h => h6 (t1.1 h)
  have hq : ¬ rq (mkCfg d n m A b c S) st ξ ζ obs < 1 / 2 := fun h => h8 (t2.1 h)
  -- R8 and R9 in the integers
  have hξG : (fun i => (Γ i : ℚ) / ((G : ℤ) : ℚ)) = ξ := by
    rw [hξ, ← hG]; funext i; push_cast; rfl
  have hη : (par d n).eta = (qn (par d n).pF (par d n).eta : ℚ) / ((F : ℤ) : ℚ) := by
    rw [← hF]; exact eq_of_onG heta rfl
  have hν : (par d n).nu = (qn (par d n).pF (par d n).nu : ℚ) / ((F : ℤ) : ℚ) := by
    rw [← hF]; exact eq_of_onG hnu rfl
  have hAm : st.A = Matrix.of fun a b => (qn (par d n).p (st.A a b) : ℚ) / Q := by
    ext a b; rw [Matrix.of_apply, ← hQ]; exact eq_of_onG (hAst a b).2 rfl
  have hBm : st.B = Matrix.of fun a b => (qn (par d n).p (st.B a b) : ℚ) / Q := by
    ext a b; rw [Matrix.of_apply, ← hQ]; exact eq_of_onG (hBst a b).2 rfl
  have hbv : st.b = fun k => (qn (par d n).p (st.b k) : ℚ) / Q := by
    funext k; rw [← hQ]; exact eq_of_onG (hbst k).2 rfl
  have hkv : st.k = (qn (par d n).p st.k : ℚ) / Q := by rw [← hQ]; exact eq_of_onG hko rfl
  have hlv : st.l = (qn (par d n).p st.l : ℚ) / Q := by rw [← hQ]; exact eq_of_onG hlo rfl
  have hmv : st.mu = fun k => (muN k : ℚ) / Dm := by funext k; exact (hmuN k).2.symm
  obtain ⟨rA, rB, r5, p6, p8, hv23, hv75⟩ := head_r8 (mkCfg d n m A b c S) st ζ obs Q F G kN yh
    (qn (par d n).pF (par d n).eta) (qn (par d n).pF (par d n).nu) Γ v
    (fun i j => qn (par d n).p (st.A i j)) (fun i j => qn (par d n).p (st.B i j)) hp1 hQ.symm
    (by omega) (by omega) h0 h1 h2 h3 h4 h5 h7 (by rw [hξG]; exact hY) (by rw [hξG]; exact hc) hη hν hAm hBm
    (by rw [hξG]; exact ha) (by rw [hξG]; exact hq)
  obtain ⟨rb, rk, rG, rl⟩ := head_r9 (mkCfg d n m A b c S) st ζ obs Q F G Dm kN yh
    (qn (par d n).pF (par d n).nu) (qn (par d n).p st.k) (qn (par d n).p st.l) Γ muN
    (fun j => qn (par d n).p (st.b j)) (fun j => qn (par d n).p (st.G j)) (fun i j => qn (par d n).p (st.B i j))
    hQ.symm (by omega) (by omega) (by omega) (by rw [hξG]; exact hY) (by rw [hξG]; exact hc) hν hBm hbv hkv
    (fun j => (hGst j).2) (fun j => rfl) hlv hmv
  rw [hξG] at rA rB r5 rb rk rG rl
  simp only [hpar] at rA rB rb rk rG rl
  -- the nonnegative radicands
  have hv2 : 0 < v 2 := by rw [h2]; positivity
  have hv7 : 0 < v 7 := by rw [h7]; positivity
  have hv3 : 0 < v 3 := by omega
  have hv5 : 0 < v 5 := by omega
  have p3 : 0 ≤ w2 Q F (qn (par d n).pF (par d n).eta) (qn (par d n).pF (par d n).nu) v 3 := by
    rw [w2_3]; apply Int.ediv_nonneg (by positivity) (by omega)
  have p5' : 0 ≤ w2 Q F (qn (par d n).pF (par d n).eta) (qn (par d n).pF (par d n).nu) v 5 := by
    rw [w2_5]; apply Int.ediv_nonneg (by positivity) hv2.le
  have p7 : 0 ≤ w2 Q F (qn (par d n).pF (par d n).eta) (qn (par d n).pF (par d n).nu) v 7 := by
    rw [w2_7]; apply Int.ediv_nonneg (by positivity) hv7.le
  have bw2 := w2_bound bQ bF bEh bNu bV p3 p5' p7
  have bw : ∀ k < 14, |w2 Q F (qn (par d n).pF (par d n).eta) (qn (par d n).pF (par d n).nu) v k| ≤
      2 ^ (31 * U + 28) := fun k hk => (bw2 k hk).trans (hU (by interval_cases k <;> simp [ev, sl2Et] <;> omega))
  have bY : |yh| ≤ 2 ^ (5 * U + 7) := by rw [← h0]; exact (bV 0 (by norm_num)).trans (hU (by simp [ev, sl1Et]))
  have leU : ∀ {z : ℤ}, |z| ≤ 2 ^ U → z ≤ 2 ^ U := fun h => (le_abs_self _).trans h
  -- R7's roots to R9
  refine XV.seq (XV.mid hL hlay (σ := σ) (Q := Q) (F := F) (G := G) (eh := qn (par d n).pF (par d n).eta)
    (nh := qn (par d n).pF (par d n).nu) (D := Dm) (kh := qn (par d n).p st.k) (lh := qn (par d n).p st.l) (v := v)
    (Ah := fun i j => qn (par d n).p (st.A i j)) (Bh := fun i j => qn (par d n).p (st.B i j)) (Γ := Γ) (mu := muN)
    (bh := fun j => qn (par d n).p (st.b j)) (Gh := fun j => qn (par d n).p (st.G j)) (U := U)
    r0 r3 c0 c1 c2 c4 eQ eF eG p2 p5 eDm hkst hlst eV (fun i j => (hAst i j).1) (fun i j => (hBst i j).1) eW eX
    (fun j => (hmuN j).1) (fun j => (hbst j).1) (fun j => (hGst j).1) hQ1 hF1 hG1 bQ bF bG bEh bNu bDm bk bl
    bA bB bΓ bMu bb bGh hdU bV p3 p5' p7 hT1 hTa hda) fun σ5 ⟨w2s, aA5, aB5, a28, a29, s59, s63, d5, F5⟩ => ?_
  rw [h4] at aA5 aB5 a28 s59
  rw [h1] at a28 s59
  rw [h0] at a29 s63
  -- the tail's inputs
  have hI5 : BLInv L n m K0 E (mkCfg d n m A b c S) (.run st) t σ5 :=
    hI.frame F5 (fun y h => by simp only [Smid, nSP, tR] at h ⊢; omega) (fun j h => by simp only [Nmid] at h; omega)
      (fun a k h => by simp only [Amid, nAP] at h ⊢; omega) d5
  have sc5 : ∀ y, ¬ Smid y → σ5.sc y = σ.sc y := fun y h => F5.2.1 y h
  have c1' : σ5.sc 41 = 1 := by rw [sc5 41 (by simp only [Smid, tR]; omega), c1]
  have c2' : σ5.sc 42 = 2 := by rw [sc5 42 (by simp only [Smid, tR]; omega), c2]
  have c4' : σ5.sc 43 = 4 := by rw [sc5 43 (by simp only [Smid, tR]; omega), c4]
  have hE1 : E ≤ 36 * U + 30 := by omega
  have hstep : step RoutinesQ.ap (mkCfg d n m A b c S) n (.run st) ξ ζ obs =
      tailMode RoutinesQ.ap (mkCfg d n m A b c S) n st (rA' (mkCfg d n m A b c S) st ξ ζ obs)
        (rB' (mkCfg d n m A b c S) st ξ ζ obs) (rb' (mkCfg d n m A b c S) st ξ ζ obs)
        (rG' (mkCfg d n m A b c S) st ξ ζ obs) (rk' (mkCfg d n m A b c S) st ξ ζ obs)
        (rl' (mkCfg d n m A b c S) st ξ ζ obs)
        (wmuOf (par d n) st (w2 Q F (qn (par d n).pF (par d n).eta) (qn (par d n).pF (par d n).nu) v 2) Γ) := by
    rw [step_run_tail, if_neg (by tauto)]
    congr 1
    rw [hξ]
    refine head_wmu (mkCfg d n m A b c S) st ζ obs n _ Γ hpar ?_
    rw [hpar, ← hξ, r5, hpar]
  refine XV.mono (hT d L w n m M K0 E (36 * U + 30) ℓa ℓ t A b c S st (rA' (mkCfg d n m A b c S) st ξ ζ obs)
    (rB' (mkCfg d n m A b c S) st ξ ζ obs) (rb' (mkCfg d n m A b c S) st ξ ζ obs)
    (rG' (mkCfg d n m A b c S) st ξ ζ obs) (rk' (mkCfg d n m A b c S) st ξ ζ obs)
    (rl' (mkCfg d n m A b c S) st ξ ζ obs)
    (w2 Q F (qn (par d n).pF (par d n).eta) (qn (par d n).pF (par d n).nu) v 2) Γ P0 σ5 hd1 hn1 hL hlay hblk hH
    heps he0.le he1 hE1 hI5 (F5.2.2.2.2.trans hp) c1' c2' c4'
    (fun i j => ⟨by rw [aA5 i j, (rA i j).2], (rA i j).1, ?_⟩)
    (fun i j => ⟨by rw [aB5 i j, (rB i j).2], (rB i j).1, ?_⟩)
    (fun j => ⟨by rw [a28 j, (rb j).2, Int.cast_add], (rb j).1, ?_⟩)
    (fun j => ⟨by rw [a29 j, (rG j).2, Int.cast_add], (rG j).1, ?_⟩)
    (by rw [s59, rk.2]) rk.1 ?_ (by rw [s63, rl.2]) rl.1 ?_
    (by simpa using w2s 2 (by norm_num)) ((bw 2 (by norm_num)).trans (hU (by omega)))
    (fun i => by rw [F5.2.2.1 _ _ (by simp only [Amid, aWv]; omega)]; exact eW i)
    (fun j => (bΓ j).trans (hU (by omega))) ?_ hTt hTta) le_rfl fun σ' h => by rwa [hstep]
  · rw [(rA i j).2]
    exact (hb_Ap _ _ Q G _ Γ U (31 * U + 28) (bw 4 (by norm_num)) (bw 11 (by norm_num)) bA bΓ hQ1 (leU bQ) hG1
      (leU bG) hdU i j).trans (hU (by omega))
  · rw [(rB i j).2]
    exact (hb_Bp _ _ Q G _ Γ U (31 * U + 28) (bw 6 (by norm_num)) (bw 13 (by norm_num)) bB bΓ hQ1 (leU bQ) hG1
      (leU bG) hdU i j).trans (hU (by omega))
  · rw [(rb j).2]
    exact (hb_bp F Q G Dm kN yh _ Γ muN _ U hF1 (leU bF) hQ1 (leU bQ) hG1 (leU bG) hD1 (leU bDm) bK bY bB bΓ bMu bb
      hdU j).trans (hU (by omega))
  · rw [(rG j).2]
    exact (hb_Gp F Q G yh _ _ Γ _ U hF1 hQ1 (leU bQ) hG1 bY bNu bB bΓ bGh hdU j).trans (hU (by omega))
  · rw [rk.2]
    exact (hb_kp F Q G Dm kN yh _ _ Γ muN U hF1 (leU bF) hQ1 (leU bQ) hG1 (leU bG) hD1 (leU bDm) bK bY bk bB bΓ bMu
      hdU).trans (hU (by omega))
  · rw [rl.2]
    exact (hb_lp F Q G Dm yh _ _ _ Γ muN U hF1 hQ1 (leU bQ) hG1 hD1 bY bNu bl bB bΓ bMu hdU).trans (hU (by omega))
  · intro mu' hm
    obtain ⟨b1, b2⟩ := hnew mu' (hstep.trans hm)
    refine ⟨b1, fun x hx => ?_⟩
    have hw : wmuOf (par d n) st (w2 Q F (qn (par d n).pF (par d n).eta) (qn (par d n).pF (par d n).nu) v 2) Γ =
        rwmu (mkCfg d n m A b c S) st ξ ζ obs := by
      rw [hξ]
      refine (head_wmu (mkCfg d n m A b c S) st ζ obs n _ Γ hpar ?_).symm
      rw [hpar, ← hξ, r5, hpar]
    rw [hw] at hx ⊢
    exact b2 x hx

end AdversarialBco.Bit.Transfer.BLM
