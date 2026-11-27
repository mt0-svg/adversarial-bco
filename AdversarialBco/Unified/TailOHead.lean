/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.TailOTail

@[expose] public section

/-!
# BL-O's round after R5: R7's tests, R7 to R9, the tail

BL's round after R5 for BL-O: from BL-O's invariant in mode `run` at round
`t + 1` (after the reading) and the first line's values in the slots `45 + k` (R5, R7's scalars), the command
`xRunTO` (R7's two tests, `xMid`: R7's roots, R8, R9, then a tail meeting `TailOKO`) ends in BL-O's invariant with the
mode `stepO` gives. v2.1's pure lemmas of the head run at `cfgH` (TailOPure.lean), a configuration of BL whose gauge
at `X'` is BL-O's, so that its `pt'` is BL-O's (`ptO_eq`).
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.Transfer
open AdversarialBco.Bit.Transfer.BLM AdversarialBco.Bit.RQ
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St CallQ init LT Lmu eBL frob2)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

/-- R7's tests (`v1 6 > 0` or `v1 8 > 0` leave for `guard`), then R7's roots to R9 and the tail. -/
def xRunTO (xtail : Layout → XCmdO) (L : Layout) : XCmdO :=
  xifSO L sZ 51 (.base (xG L)) (xifSO L sZ 53 (.base (xG L)) (.seq (.base (xMid L)) (xtail L)))

set_option maxHeartbeats 16000000 in
/-- **R7's tests, R7 to R9 and the tail of BL-O** from BL-O's invariant in mode `run` at the round `t + 1` and the
first line's values in the slots `45 + k`: the invariant with the mode `stepO` gives. -/
theorem XVO.runTO {xtail : Layout → XCmdO} {Ct kt nS nN nA : ℕ} (hT : TailOKO xtail Ct kt nS nN nA)
    {R : RdO d} {U : ℕ} {st : St d} {σ : Env d} {P0 : ℕ → EuclideanSpace ℝ (Fin d)} {ξ : Fin d → ℚ} {ζ : ℚ}
    {obs gz pN pD : ℤ} {Γ : Fin d → ℤ}
    (hIn : InU d R.n R.δ R.r0 R.R0) (hL : LayOK R.L d R.ℓa) (hlay : BLLay R.L) (hroom : RoomO R.L nS nN nA)
    (hI : BLInv R.L R.n 0 R.K0 R.E (cfgV R.c) (.run st) (R.t + 1) σ) (hp : σ.pts = P0)
    (c1 : σ.sc 41 = 1) (c2 : σ.sc 42 = 2) (c4 : σ.sc 43 = 4)
    (eV : ∀ k < 9, σ.sc (45 + k) = v1 (2 ^ R.c.par.p) (2 ^ R.c.par.pF) (2 ^ (2 * gsm_prec R.c.par.B))
      (qn R.c.par.pF R.c.par.eps) (qn R.c.par.pF R.c.par.kapc) gz pN pD (Γ ⬝ᵥ Γ) obs k)
    (eW : ∀ i : Fin d, σ.arr aWv i = ((fun i j => qn R.c.par.p (st.A i j) : Matrix (Fin d) (Fin d) ℤ) *ᵥ Γ) i)
    (eX : ∀ j : Fin d, σ.arr aGam j = Γ j)
    (hξ : ξ = fun i => (Γ i : ℚ) / 2 ^ (2 * gsm_prec R.c.par.B))
    (hζ : ζ = (gz : ℚ) / 2 ^ (2 * gsm_prec R.c.par.B) / 2)
    (hpt : ptO R.w.orc R.c (XO R.c st ξ) = (pN : ℚ) / pD) (hD : 0 < pD)
    (hEU : R.E ≤ U) (hdU : d ≤ 2 ^ U) (bZ : |gz| ≤ 2 ^ U) (bN : |pN| ≤ 2 ^ U) (bD : |pD| ≤ 2 ^ U)
    (bO : |obs| ≤ 2 ^ U) (bΓ : ∀ j, |Γ j| ≤ 2 ^ U)
    (hnew : ∀ mu' : Fin d → ℚ, BLO.stepO R.w.orc R.c R.n (.run st) ξ ζ obs =
        .run ⟨false, mu', rA' (cfgH R.w.orc R.c st ξ) st ξ ζ obs, rB' (cfgH R.w.orc R.c st ξ) st ξ ζ obs,
          rb' (cfgH R.w.orc R.c st ξ) st ξ ζ obs, rk' (cfgH R.w.orc R.c st ξ) st ξ ζ obs,
          rG' (cfgH R.w.orc R.c st ξ) st ξ ζ obs, rl' (cfgH R.w.orc R.c st ξ) st ξ ζ obs⟩ →
      StBnd R.c.par.p R.E R.c.par.Rint ⟨false, mu', rA' (cfgH R.w.orc R.c st ξ) st ξ ζ obs,
          rB' (cfgH R.w.orc R.c st ξ) st ξ ζ obs, rb' (cfgH R.w.orc R.c st ξ) st ξ ζ obs,
          rk' (cfgH R.w.orc R.c st ξ) st ξ ζ obs, rG' (cfgH R.w.orc R.c st ξ) st ξ ζ obs,
          rl' (cfgH R.w.orc R.c st ξ) st ξ ζ obs⟩ ∧
      ∀ x, apI R.w.orc R.c (callLO R.c R.n (rB' (cfgH R.w.orc R.c st ξ) st ξ ζ obs)
          (rb' (cfgH R.w.orc R.c st ξ) st ξ ζ obs) (rk' (cfgH R.w.orc R.c st ξ) st ξ ζ obs)
          (rwmu (cfgH R.w.orc R.c st ξ) st ξ ζ obs)) = some x →
        (∀ j, |x j| ≤ 2 ^ R.E) ∧ ellExpO (clearO (callLO R.c R.n (rB' (cfgH R.w.orc R.c st ξ) st ξ ζ obs)
          (rb' (cfgH R.w.orc R.c st ξ) st ξ ζ obs) (rk' (cfgH R.w.orc R.c st ξ) st ξ ζ obs)
          (rwmu (cfgH R.w.orc R.c st ξ) st ξ ζ obs))) ≤ R.E)
    (hT1 : 130 * U + 120 < R.ℓ) (hTa : 130 * U + 120 < 2 ^ R.ℓa) (hda : d * d + d < 2 ^ R.ℓa)
    (hTt : Ct * (R.W + (36 * U + 30) + 1) ^ kt ≤ R.ℓ)
    (hTta : Ct * (R.W + (36 * U + 30) + 1) ^ kt < 2 ^ R.ℓa) :
    R.RunsO (xRunTO xtail R.L) σ (2 + (2 + (midUnits d U + Ct * (R.W + (36 * U + 30) + 1) ^ kt)))
      (RPost R.L R.n 0 R.K0 R.E (cfgV R.c) (BLO.stepO R.w.orc R.c R.n (.run st) ξ ζ obs) (R.t + 1) P0) := by
  have hd1 := hIn.hd
  have hn1 := hIn.hn
  have hlay' := hlay
  obtain ⟨hS, hN, hAr⟩ := hlay'
  simp only [oE, rEE, aWE] at hS hN hAr
  set H := cfgH R.w.orc R.c st ξ with hHdef
  have hparH : H.par = R.c.par := rfl
  have hparV : (cfgV R.c).par = R.c.par := rfl
  have hU : ∀ {a b : ℕ}, a ≤ b → (2 : ℤ) ^ a ≤ 2 ^ b := fun h => pow_le_pow_right₀ (by norm_num) h
  have hℓ2 : ∀ {a : ℕ}, a < R.ℓ → (2 : ℝ) ^ a < 2 ^ R.ℓ := fun h => pow_lt_pow_right₀ (by norm_num) h
  obtain ⟨r0, -, -, r3, -⟩ := hI.regs
  obtain ⟨c0, -, c2p, c2pF, c2g, -⟩ := hI.consts
  obtain ⟨p0, -, p2, -, p4, p5, -⟩ := hI.par
  obtain ⟨-, -, ⟨Dm, hDm, eDm, hmu⟩, hAst, hBst, hbst, ⟨hkst, hko⟩, hGst, ⟨hlst, hlo⟩⟩ := hI.mode
  choose muN hmuN using hmu
  -- the grid facts of the parameters
  have heps : OnG R.c.par.pF R.c.par.eps := tlN_onG_eps _ _ _
  have hkap : OnG R.c.par.pF R.c.par.kapc := tlN_onG_kapc _ _ _
  have heta : OnG R.c.par.pF R.c.par.eta := tlN_onG_eta _ _ _
  have hnu : OnG R.c.par.pF R.c.par.nu := tlN_onG_nu _ _ _
  have he0 : 0 < R.c.par.eps := eps_posK d R.n (kDel R.δ) hd1 hn1
  have hp1 : 1 ≤ R.c.par.p := by
    show 1 ≤ 10 * (NeO d R.n (kDel R.δ)).size + 16 * d.size + 160
    omega
  -- R5 and R7's tests
  have hptH : Bit.BLP.ptQ H (Bit.BLP.XQ H st ξ) = (pN : ℚ) / pD := (ptO_eq R.w.orc R.c st ξ).symm.trans hpt
  obtain ⟨hY, hc⟩ := head_Yc H st ξ ζ obs pN pD gz Γ (2 * gsm_prec R.c.par.B) hD hptH hζ hξ heps he0 hkap
  obtain ⟨t1, t2⟩ := head_tests H st ξ ζ obs pN pD gz Γ (2 * gsm_prec R.c.par.B) hξ hc
  rw [hparH] at hY hc t1 t2
  rw [show (2 : ℚ) ^ R.c.par.p = (((2 : ℤ) ^ R.c.par.p : ℤ) : ℚ) by push_cast; rfl] at hY
  -- the integers
  generalize hQ : (2 : ℤ) ^ R.c.par.p = Q at eV hY hc t1 t2
  generalize hF : (2 : ℤ) ^ R.c.par.pF = F at eV hY hc t1 t2
  generalize hG : (2 : ℤ) ^ (2 * gsm_prec R.c.par.B) = G at eV hY hc t1 t2
  generalize heN : qn R.c.par.pF R.c.par.eps = eN at eV hY hc t1 t2
  generalize hkN : qn R.c.par.pF R.c.par.kapc = kN at eV hY hc t1 t2
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
  have bEh : |qn R.c.par.pF R.c.par.eta| ≤ 2 ^ U := bsc (by decide) p2
  have bNu : |qn R.c.par.pF R.c.par.nu| ≤ 2 ^ U := bsc (by decide) p5
  have bDm : |Dm| ≤ 2 ^ U := bsc (by decide) eDm
  have bk : |qn R.c.par.p st.k| ≤ 2 ^ U := bsc (by decide) hkst
  have bl : |qn R.c.par.p st.l| ≤ 2 ^ U := bsc (by decide) hlst
  have bA : ∀ i j : Fin d, |qn R.c.par.p (st.A i j)| ≤ 2 ^ U := fun i j =>
    barr (by decide) (idx_lt i j) (hAst i j).1
  have bB : ∀ i j : Fin d, |qn R.c.par.p (st.B i j)| ≤ 2 ^ U := fun i j =>
    barr (by decide) (idx_lt i j) (hBst i j).1
  have bb : ∀ j : Fin d, |qn R.c.par.p (st.b j)| ≤ 2 ^ U := fun j =>
    barr (by decide) (idx1_lt j) (hbst j).1
  have bGh : ∀ j : Fin d, |qn R.c.par.p (st.G j)| ≤ 2 ^ U := fun j =>
    barr (by decide) (idx1_lt j) (hGst j).1
  have bMu : ∀ j : Fin d, |muN j| ≤ 2 ^ U := fun j => barr (by decide) (idx1_lt j) (hmuN j).1
  have bGG : |Γ ⬝ᵥ Γ| ≤ 2 ^ (3 * U) := by
    have := dot_abs_le bΓ bΓ hdU; rwa [show U + U + U = 3 * U by ring] at this
  have bV : ∀ k < 9, |v k| ≤ 2 ^ ev U (sl1Et k) := by
    rw [← hv]; exact v1_bound bQ bF bG bE bK bZ bN bD bO bGG
  have bvℓ : ∀ k < 9, |((v k : ℤ) : ℝ)| < 2 ^ R.ℓ := fun k hk => by
    have h' : ev U (sl1Et k) < R.ℓ := by interval_cases k <;> simp [ev, sl1Et] <;> omega
    have : ((|v k| : ℤ) : ℝ) ≤ ((2 ^ ev U (sl1Et k) : ℤ) : ℝ) := by exact_mod_cast bV k hk
    rw [Int.cast_abs] at this; push_cast at this
    exact lt_of_le_of_lt this (hℓ2 h')
  have hz0 : |σ.sc sZ| < 2 ^ R.ℓ := by rw [c0]; simp
  have e51 : σ.sc 51 = ((v 6 : ℤ) : ℝ) := by simpa using eV 6 (by norm_num)
  have e53 : σ.sc 53 = ((v 8 : ℤ) : ℝ) := by simpa using eV 8 (by norm_num)
  have hstepG : ∀ (h : ra H st ξ ζ obs < 1 / 2 ∨ rq H st ξ ζ obs < 1 / 2),
      BLO.stepO R.w.orc R.c R.n (.run st) ξ ζ obs = .guard := fun h => by
    rw [stepO_run, if_pos h]
  -- the first test
  by_cases h6 : 0 < v 6
  · refine XVO.mono (XVO.ifS_t hL (by romega) (by romega) hz0 (by rw [e51]; exact bvℓ 6 (by norm_num))
      (by rw [c0, e51]; exact_mod_cast h6) (XVO.ofX (XV.guard hL hI hp (by omega)))) (by omega) fun σ' h => ?_
    rwa [hstepG (Or.inl (t1.2 h6))]
  refine XVO.mono (K := 2 + (midUnits d U + Ct * (R.W + (36 * U + 30) + 1) ^ kt) + 2)
    (XVO.ifS_f hL (by romega) (by romega) hz0 (by rw [e51]; exact bvℓ 6 (by norm_num))
      (by rw [c0, e51]; exact_mod_cast h6) ?_) (by omega) fun σ' h => h
  -- the second test
  by_cases h8 : 0 < v 8
  · refine XVO.mono (XVO.ifS_t hL (by romega) (by romega) hz0 (by rw [e53]; exact bvℓ 8 (by norm_num))
      (by rw [c0, e53]; exact_mod_cast h8) (XVO.ofX (XV.guard hL hI hp (by omega)))) (by omega) fun σ' h => ?_
    rwa [hstepG (Or.inr (t2.2 h8))]
  refine XVO.mono (K := midUnits d U + Ct * (R.W + (36 * U + 30) + 1) ^ kt + 2)
    (XVO.ifS_f hL (by romega) (by romega) hz0 (by rw [e53]; exact bvℓ 8 (by norm_num))
      (by rw [c0, e53]; exact_mod_cast h8) ?_) (by omega) fun σ' h => h
  have ha : ¬ ra H st ξ ζ obs < 1 / 2 := fun h => h6 (t1.1 h)
  have hq : ¬ rq H st ξ ζ obs < 1 / 2 := fun h => h8 (t2.1 h)
  -- R8 and R9 in the integers
  have hξG : (fun i => (Γ i : ℚ) / ((G : ℤ) : ℚ)) = ξ := by
    rw [hξ, ← hG]; funext i; push_cast; rfl
  have hη : R.c.par.eta = (qn R.c.par.pF R.c.par.eta : ℚ) / ((F : ℤ) : ℚ) := by
    rw [← hF]; exact eq_of_onG heta rfl
  have hν : R.c.par.nu = (qn R.c.par.pF R.c.par.nu : ℚ) / ((F : ℤ) : ℚ) := by
    rw [← hF]; exact eq_of_onG hnu rfl
  have hAm : st.A = Matrix.of fun a b => (qn R.c.par.p (st.A a b) : ℚ) / Q := by
    ext a b; rw [Matrix.of_apply, ← hQ]; exact eq_of_onG (hAst a b).2 rfl
  have hBm : st.B = Matrix.of fun a b => (qn R.c.par.p (st.B a b) : ℚ) / Q := by
    ext a b; rw [Matrix.of_apply, ← hQ]; exact eq_of_onG (hBst a b).2 rfl
  have hbv : st.b = fun k => (qn R.c.par.p (st.b k) : ℚ) / Q := by
    funext k; rw [← hQ]; exact eq_of_onG (hbst k).2 rfl
  have hkv : st.k = (qn R.c.par.p st.k : ℚ) / Q := by rw [← hQ]; exact eq_of_onG hko rfl
  have hlv : st.l = (qn R.c.par.p st.l : ℚ) / Q := by rw [← hQ]; exact eq_of_onG hlo rfl
  have hmv : st.mu = fun k => (muN k : ℚ) / Dm := by funext k; exact (hmuN k).2.symm
  obtain ⟨rA, rB, r5, p6, p8, hv23, hv75⟩ := head_r8 H st ζ obs Q F G kN yh
    (qn R.c.par.pF R.c.par.eta) (qn R.c.par.pF R.c.par.nu) Γ v
    (fun i j => qn R.c.par.p (st.A i j)) (fun i j => qn R.c.par.p (st.B i j)) hp1 hQ.symm
    (by omega) (by omega) h0 h1 h2 h3 h4 h5 h7 (by rw [hξG]; exact hY) (by rw [hξG]; exact hc) hη hν hAm hBm
    (by rw [hξG]; exact ha) (by rw [hξG]; exact hq)
  obtain ⟨rb, rk, rG, rl⟩ := head_r9 H st ζ obs Q F G Dm kN yh
    (qn R.c.par.pF R.c.par.nu) (qn R.c.par.p st.k) (qn R.c.par.p st.l) Γ muN
    (fun j => qn R.c.par.p (st.b j)) (fun j => qn R.c.par.p (st.G j)) (fun i j => qn R.c.par.p (st.B i j))
    hQ.symm (by omega) (by omega) (by omega) (by rw [hξG]; exact hY) (by rw [hξG]; exact hc) hν hBm hbv hkv
    (fun j => (hGst j).2) (fun j => rfl) hlv hmv
  rw [hξG] at rA rB r5 rb rk rG rl
  simp only [hparH] at rA rB rb rk rG rl
  -- the nonnegative radicands
  have hv2 : 0 < v 2 := by rw [h2]; positivity
  have hv7 : 0 < v 7 := by rw [h7]; positivity
  have hv3 : 0 < v 3 := by omega
  have hv5 : 0 < v 5 := by omega
  have p3 : 0 ≤ w2 Q F (qn R.c.par.pF R.c.par.eta) (qn R.c.par.pF R.c.par.nu) v 3 := by
    rw [w2_3]; apply Int.ediv_nonneg (by positivity) (by omega)
  have p5' : 0 ≤ w2 Q F (qn R.c.par.pF R.c.par.eta) (qn R.c.par.pF R.c.par.nu) v 5 := by
    rw [w2_5]; apply Int.ediv_nonneg (by positivity) hv2.le
  have p7 : 0 ≤ w2 Q F (qn R.c.par.pF R.c.par.eta) (qn R.c.par.pF R.c.par.nu) v 7 := by
    rw [w2_7]; apply Int.ediv_nonneg (by positivity) hv7.le
  have bw2 := w2_bound bQ bF bEh bNu bV p3 p5' p7
  have bw : ∀ k < 14, |w2 Q F (qn R.c.par.pF R.c.par.eta) (qn R.c.par.pF R.c.par.nu) v k| ≤
      2 ^ (31 * U + 28) := fun k hk => (bw2 k hk).trans (hU (by interval_cases k <;> simp [ev, sl2Et] <;> omega))
  have bY : |yh| ≤ 2 ^ (5 * U + 7) := by rw [← h0]; exact (bV 0 (by norm_num)).trans (hU (by simp [ev, sl1Et]))
  have leU : ∀ {z : ℤ}, |z| ≤ 2 ^ U → z ≤ 2 ^ U := fun h => (le_abs_self _).trans h
  -- R7's roots to R9
  refine XVO.seq (XVO.ofX (XV.mid hL hlay (σ := σ) (Q := Q) (F := F) (G := G) (eh := qn R.c.par.pF R.c.par.eta)
    (nh := qn R.c.par.pF R.c.par.nu) (D := Dm) (kh := qn R.c.par.p st.k) (lh := qn R.c.par.p st.l) (v := v)
    (Ah := fun i j => qn R.c.par.p (st.A i j)) (Bh := fun i j => qn R.c.par.p (st.B i j)) (Γ := Γ) (mu := muN)
    (bh := fun j => qn R.c.par.p (st.b j)) (Gh := fun j => qn R.c.par.p (st.G j)) (U := U)
    r0 r3 c0 c1 c2 c4 eQ eF eG p2 p5 eDm hkst hlst eV (fun i j => (hAst i j).1) (fun i j => (hBst i j).1) eW eX
    (fun j => (hmuN j).1) (fun j => (hbst j).1) (fun j => (hGst j).1) hQ1 hF1 hG1 bQ bF bG bEh bNu bDm bk bl
    bA bB bΓ bMu bb bGh hdU bV p3 p5' p7 hT1 hTa hda)) fun σ5 ⟨w2s, aA5, aB5, a28, a29, s59, s63, d5, F5⟩ => ?_
  rw [h4] at aA5 aB5 a28 s59
  rw [h1] at a28 s59
  rw [h0] at a29 s63
  -- the tail's inputs
  have hI5 : BLInv R.L R.n 0 R.K0 R.E (cfgV R.c) (.run st) (R.t + 1) σ5 :=
    hI.frame F5 (fun y h => by simp only [Smid, nSP, tR] at h ⊢; omega) (fun j h => by simp only [Nmid] at h; omega)
      (fun a k h => by simp only [Amid, nAP] at h ⊢; omega) d5
  have sc5 : ∀ y, ¬ Smid y → σ5.sc y = σ.sc y := fun y h => F5.2.1 y h
  have c1' : σ5.sc 41 = 1 := by rw [sc5 41 (by simp only [Smid, tR]; omega), c1]
  have c2' : σ5.sc 42 = 2 := by rw [sc5 42 (by simp only [Smid, tR]; omega), c2]
  have c4' : σ5.sc 43 = 4 := by rw [sc5 43 (by simp only [Smid, tR]; omega), c4]
  have hE1 : R.E ≤ 36 * U + 30 := by omega
  have hw : rwmu H st ξ ζ obs =
      wmuOf R.c.par st (w2 Q F (qn R.c.par.pF R.c.par.eta) (qn R.c.par.pF R.c.par.nu) v 2) Γ :=
    head_wmuO H st ξ ζ obs R.c.par _ Γ hparH hξ (by rw [r5])
  have hstep : BLO.stepO R.w.orc R.c R.n (.run st) ξ ζ obs =
      tailModeO R.w.orc R.c R.n st (rA' H st ξ ζ obs) (rB' H st ξ ζ obs) (rb' H st ξ ζ obs) (rG' H st ξ ζ obs)
        (rk' H st ξ ζ obs) (rl' H st ξ ζ obs)
        (wmuOf R.c.par st (w2 Q F (qn R.c.par.pF R.c.par.eta) (qn R.c.par.pF R.c.par.nu) v 2) Γ) := by
    rw [stepO_run, if_neg (by tauto), hw]
  have hTI : TIn R.L R.n 0 R.K0 R.E (36 * U + 30) (cfgV R.c) st (R.t + 1) P0 (rA' H st ξ ζ obs)
      (rB' H st ξ ζ obs) (rb' H st ξ ζ obs) (rG' H st ξ ζ obs) (rk' H st ξ ζ obs) (rl' H st ξ ζ obs)
      (w2 Q F (qn R.c.par.pF R.c.par.eta) (qn R.c.par.pF R.c.par.nu) v 2) Γ σ5 := by
    refine ⟨hI5, F5.2.2.2.2.trans hp, c1', c2', c4',
      fun i j => ⟨by rw [hparV, aA5 i j, (rA i j).2], (rA i j).1, ?_⟩,
      fun i j => ⟨by rw [hparV, aB5 i j, (rB i j).2], (rB i j).1, ?_⟩,
      fun j => ⟨by rw [hparV, a28 j, (rb j).2, Int.cast_add], (rb j).1, ?_⟩,
      fun j => ⟨by rw [hparV, a29 j, (rG j).2, Int.cast_add], (rG j).1, ?_⟩,
      by rw [hparV, s59, rk.2], rk.1, ?_, by rw [hparV, s63, rl.2], rl.1, ?_,
      by simpa using w2s 2 (by norm_num), (bw 2 (by norm_num)).trans (hU (by omega)),
      fun i => by rw [F5.2.2.1 _ _ (by simp only [Amid, aWv]; omega)]; exact eW i,
      fun j => (bΓ j).trans (hU (by omega)), hE1⟩
    · rw [hparV, (rA i j).2]
      exact (hb_Ap _ _ Q G _ Γ U (31 * U + 28) (bw 4 (by norm_num)) (bw 11 (by norm_num)) bA bΓ hQ1 (leU bQ) hG1
        (leU bG) hdU i j).trans (hU (by omega))
    · rw [hparV, (rB i j).2]
      exact (hb_Bp _ _ Q G _ Γ U (31 * U + 28) (bw 6 (by norm_num)) (bw 13 (by norm_num)) bB bΓ hQ1 (leU bQ) hG1
        (leU bG) hdU i j).trans (hU (by omega))
    · rw [hparV, (rb j).2]
      exact (hb_bp F Q G Dm kN yh _ Γ muN _ U hF1 (leU bF) hQ1 (leU bQ) hG1 (leU bG) hD1 (leU bDm) bK bY bB bΓ bMu
        bb hdU j).trans (hU (by omega))
    · rw [hparV, (rG j).2]
      exact (hb_Gp F Q G yh _ _ Γ _ U hF1 hQ1 (leU bQ) hG1 bY bNu bB bΓ bGh hdU j).trans (hU (by omega))
    · rw [hparV, rk.2]
      exact (hb_kp F Q G Dm kN yh _ _ Γ muN U hF1 (leU bF) hQ1 (leU bQ) hG1 (leU bG) hD1 (leU bDm) bK bY bk bB bΓ
        bMu hdU).trans (hU (by omega))
    · rw [hparV, rl.2]
      exact (hb_lp F Q G Dm yh _ _ _ Γ muN U hF1 hQ1 (leU bQ) hG1 hD1 bY bNu bl bB bΓ bMu hdU).trans (hU (by omega))
  have hpost : TPostO R.w.orc R.c R.n R.E (rA' H st ξ ζ obs) (rB' H st ξ ζ obs) (rb' H st ξ ζ obs)
      (rG' H st ξ ζ obs) (rk' H st ξ ζ obs) (rl' H st ξ ζ obs)
      (wmuOf R.c.par st (w2 Q F (qn R.c.par.pF R.c.par.eta) (qn R.c.par.pF R.c.par.nu) v 2) Γ)
      (tailModeO R.w.orc R.c R.n st (rA' H st ξ ζ obs) (rB' H st ξ ζ obs) (rb' H st ξ ζ obs) (rG' H st ξ ζ obs)
        (rk' H st ξ ζ obs) (rl' H st ξ ζ obs)
        (wmuOf R.c.par st (w2 Q F (qn R.c.par.pF R.c.par.eta) (qn R.c.par.pF R.c.par.nu) v 2) Γ)) := by
    intro mu' hm
    obtain ⟨b1, b2⟩ := hnew mu' (hstep.trans hm)
    rw [← hw]
    exact ⟨b1, b2⟩
  exact XVO.mono (hT d R (36 * U + 30) st _ _ _ _ _ _ _ Γ P0 σ5 hIn hL hlay hroom hTI hpost hTt hTta) le_rfl
    fun σ' h => by rwa [hstep]

end AdversarialBco.Unified.ProgO
