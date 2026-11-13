/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLTailRd

@[expose] public section

/-!
# The tail of BL's round, part e: R10 TRACE and the theorem `tailBL_of`

`xtail`: R10's sums (`xR10`), the two trace guards `sc 88 < sc 89` (`B'`) and `sc 88 < sc 90` (`A'`), then R11 to R15
(`xT11`). `XV.t10`: from `TIn`, it ends in `RPost` with the mode `tailMode`. `tailBL_of`: the frozen `TailBL` of
Bit/Transfer/XBLTailSpec.lean from `CallBL`, `DataT`, `DataL`, `CommitBL`, `FireBL`, `ExpBL`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

theorem r10Units_eq (d : ℕ) : r10Units d = 20 * d * d + 4 * d + 25 := by
  unfold r10Units; rw [show ieLQ.units = 11 from rfl]; ring

theorem r12Units_eq (d X : ℕ) : r12Units d X = 10 * d * d + 41 * d + 4 * X + 83 := by
  unfold r12Units; rw [show ieT1.units = 47 from rfl, show ieT2.units = 13 from rfl]; ring

theorem r13Units_eq (d : ℕ) : r13Units d = 31 * d + 30 := by
  unfold r13Units
  rw [show ieWn.units = 15 from rfl, show ieDw.units = 7 from rfl, show ieL13.units = 9 from rfl,
    show ieR13.units = 5 from rfl]
  ring

/-- **The tail of BL's round**: R10, its two guards, then R11 to R15. -/
def xtail (xdt xcall xfire xdl xcom : Layout → XCmd) (L : Layout) : XCmd :=
  .seq (xR10 L) (xifS L 88 89 (xG L) (xifS L 88 90 (xG L) (xT11 xdt xcall xfire xdl xcom L)))

set_option maxHeartbeats 2000000 in
/-- **R10 TRACE on the machine**, then R11 to R15. -/
theorem XV.t10 {xdt xfire xdl xcall xcom : Layout → XCmd} {Ct kt Cf kf Cl kl Ca ka nS nN nA Cc kc : ℕ}
    (hdt : DTSpec xdt Ct kt) (hfire : FireSpec xfire Cf kf) (hdl : DLSpec xdl Cl kl)
    (hcall : CallSpec xcall Ca ka nS nN nA) (hcom : ComSpec xcom Cc kc)
    {L : Layout} {w : BitRAM.World d} {n m M K0 E E1 ℓa ℓ t : ℕ} {A : Matrix (Fin m) (Fin d) ℚ}
    {b : Fin m → ℚ} {c : Fin d → ℚ} {S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ} {st : St d}
    {Ap Bp : Matrix (Fin d) (Fin d) ℚ} {bp Gp : Fin d → ℚ} {kp lp : ℚ} {s5 : ℤ} {Γ : Fin d → ℤ}
    {P0 : ℕ → EuclideanSpace ℝ (Fin d)} {σ : Env d} {Xb : ℕ}
    (hd1 : 1 ≤ d) (hn : 1 ≤ n) (hL : LayOK L d ℓa) (hlay : BLLay L) (hok : blkBL.OK L nS nN nA)
    (hM : RealRAM.HeightLE A b M) (he : OnG (par d n).pF (par d n).eps) (he0 : 0 ≤ (par d n).eps)
    (he1 : (par d n).eps ≤ 1)
    (hT : TIn L n m K0 E E1 (mkCfg d n m A b c S) st t P0 Ap Bp bp Gp kp lp s5 Γ σ)
    (hX : frob2 Bp ≤ 2 * ((par d n).Lam : ℚ) → ellExp (clearQ (callTOf (mkCfg d n m A b c S) st Bp bp Gp)) ≤ Xb)
    (hpost : TPost (mkCfg d n m A b c S) n E Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ)
      (tailMode RoutinesQ.ap (mkCfg d n m A b c S) n st Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ)))
    (hr1 : 3 * E1 + 1 < ℓ) (hr2 : d * d * 2 ^ (2 * E1) < 2 ^ ℓ)
    (hℓt : Ct * (d + E1 + 1) ^ kt ≤ ℓ) (hℓat : Ct * (d + E1 + 1) ^ kt < 2 ^ ℓa)
    (hℓc : Ca * (d + m + M.size + E1 + Ct * (d + E1 + 1) ^ kt + 1) ^ ka ≤ ℓ)
    (hℓac : Ca * (d + m + M.size + E1 + Ct * (d + E1 + 1) ^ kt + 1) ^ ka < 2 ^ ℓa)
    (hg1 : 7 * (4 * E1 + 2 * Xb + 3 * d) + 3 * d + 3 < ℓ)
    (hg2 : d * 2 ^ (2 * (4 * E1 + 2 * Xb + 3 * d)) < 2 ^ ℓ) (hXa : Xb < 2 ^ ℓa)
    (hℓf : Cf * (d + E + 1) ^ kf ≤ ℓ) (hℓaf : Cf * (d + E + 1) ^ kf < 2 ^ ℓa)
    (hℓa : 4 * (2 * E1 + d) + 1 < ℓ) (hℓb : 5 * (8 * E1 + 3 * d + 2) < ℓ)
    (hℓc' : d * 2 ^ (2 * (8 * E1 + 3 * d + 2)) < 2 ^ ℓ) (hda : d * d + d < 2 ^ ℓa)
    (hℓ1 : Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl ≤ ℓ) (hℓa1 : Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl < 2 ^ ℓa)
    (hℓ2 : Ca * (d + m + M.size + E1 + Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl + 1) ^ ka ≤ ℓ)
    (hℓa2 : Ca * (d + m + M.size + E1 + Cl * (d + (8 * E1 + 3 * d + 2) + 1) ^ kl + 1) ^ ka < 2 ^ ℓa)
    (hℓ3 : Cc * (d + E + 1) ^ kc ≤ ℓ) (hℓa3 : Cc * (d + E + 1) ^ kc < 2 ^ ℓa) :
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xtail xdt xcall xfire xdl xcom L) σ
      (r10Units d + (u11 Ct kt Cf kf Cl kl Ca ka Cc kc d m M.size E E1 Xb + 4))
      (RPost L n m K0 E (mkCfg d n m A b c S)
        (tailMode RoutinesQ.ap (mkCfg d n m A b c S) n st Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ)) t P0) := by
  set cfg := mkCfg d n m A b c S with hcfg
  have hℓ : 1 ≤ ℓ := by omega
  have pE : (2 : ℤ) ^ E ≤ 2 ^ E1 := pow_le_pow_right₀ (by norm_num) hT.hE
  obtain ⟨eQ, bQ, -, -, -, -, -, -, eL, bL, -⟩ := tl_consts hT.inv
  set Ah : Matrix (Fin d) (Fin d) ℤ := fun i j => qn (par d n).p (Ap i j) with hAh
  set Bh : Matrix (Fin d) (Fin d) ℤ := fun i j => qn (par d n).p (Bp i j) with hBh
  have eA : ∀ k < d * d, σ.arr aAp k = flatM Ah k := fun k hk => by
    obtain ⟨i, j, rfl⟩ := tl_flat_cover k hk; rw [tl_flat_eq]; exact (hT.hA i j).1
  have eB : ∀ k < d * d, σ.arr aBp k = flatM Bh k := fun k hk => by
    obtain ⟨i, j, rfl⟩ := tl_flat_cover k hk; rw [tl_flat_eq]; exact (hT.hB i j).1
  have bA : ∀ k < d * d, |flatM Ah k| ≤ 2 ^ E1 := fun k hk => by
    obtain ⟨i, j, rfl⟩ := tl_flat_cover k hk; rw [tl_flat_eq]; exact (hT.hA i j).2.2
  have bB : ∀ k < d * d, |flatM Bh k| ≤ 2 ^ E1 := fun k hk => by
    obtain ⟨i, j, rfl⟩ := tl_flat_cover k hk; rw [tl_flat_eq]; exact (hT.hB i j).2.2
  -- R10's sums
  refine XV.seq (XV.r10 hL hlay (σ := σ) (Q := 2 ^ (par d n).p) (Lam := (par d n).Lam) (E := E1) (Af := flatM Ah)
    (Bf := flatM Bh) hT.inv.regs.1 hT.inv.regs.2.2.2.1 hT.inv.consts.1 eQ eL eA eB bA bB (bQ.trans pE)
    (bL.trans pE) hr1 hr2 hda) fun σ1 ⟨v89, v90, v88, d1, F1⟩ => ?_
  have hT1 := hT.frame F1 (fun y hy => by simp only [tR, nSP] at hy ⊢; omega) (fun j hj => by omega)
    (fun a k hk => hk.elim) d1
  have hdB := frob2_flat (par d n).p (par d n).Lam Bp (flatM Bh) (fun i j => tl_flat_eq Bh i j)
    (fun i j => (hT.hB i j).2.1)
  have hdA := frob2_flat (par d n).p (par d n).Lam Ap (flatM Ah) (fun i j => tl_flat_eq Ah i j)
    (fun i j => (hT.hA i j).2.1)
  obtain ⟨t88, t89⟩ := tl_r10_test_abs d ((par d n).Lam : ℤ) (2 ^ (par d n).p) (flatM Bh) E1 ℓ (bL.trans pE)
    (bQ.trans pE) bB hr1 hr2
  obtain ⟨-, t90⟩ := tl_r10_test_abs d ((par d n).Lam : ℤ) (2 ^ (par d n).p) (flatM Ah) E1 ℓ (bL.trans pE)
    (bQ.trans pE) bA hr1 hr2
  have hS := hlay.1
  have s88 : 88 < L.NS := by simp only [oE] at hS; omega
  have s89 : 89 < L.NS := by simp only [oE] at hS; omega
  have s90 : 90 < L.NS := by simp only [oE] at hS; omega
  have r88 : |σ1.sc 88| < 2 ^ ℓ := by rw [v88]; exact t88
  by_cases hc1 : σ1.sc 88 < σ1.sc 89
  · -- the trace guard of `B'`
    have h1 : 2 * (cfg.par.Lam : ℚ) < frob2 Bp := by rw [v88, v89, Int.cast_lt] at hc1; exact hdB.2 hc1
    rw [tailMode_eq]; simp only [h1, true_or, ↓reduceIte]
    exact XV.mono (XV.ifS_t hL s88 s89 r88 (by rw [v89]; exact t89) hc1 (XV.guard hL hT1.inv hT1.pts hℓ))
      (by omega) fun _ h => h
  · have h1 : ¬ 2 * (cfg.par.Lam : ℚ) < frob2 Bp := fun h => hc1 (by
      rw [v88, v89, Int.cast_lt]; exact hdB.1 h)
    by_cases hc2 : σ1.sc 88 < σ1.sc 90
    · -- the trace guard of `A'`
      have h2 : 2 * (cfg.par.Lam : ℚ) < frob2 Ap := by rw [v88, v90, Int.cast_lt] at hc2; exact hdA.2 hc2
      rw [tailMode_eq]; simp only [h1, h2, or_true, ↓reduceIte]
      exact XV.mono (XV.ifS_f hL s88 s89 r88 (by rw [v89]; exact t89) hc1
        (XV.ifS_t hL s88 s90 r88 (by rw [v90]; exact t90) hc2 (XV.guard hL hT1.inv hT1.pts hℓ)))
        (by omega) fun _ h => h
    · -- R11 to R15
      have h2 : ¬ 2 * (cfg.par.Lam : ℚ) < frob2 Ap := fun h => hc2 (by
        rw [v88, v90, Int.cast_lt]; exact hdA.1 h)
      have em : tailMode RoutinesQ.ap cfg n st Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ) =
          m11 cfg n st Ap Bp bp Gp kp lp (wmuOf (par d n) st s5 Γ) := by
        rw [tailMode_eq]; simp only [h1, h2, or_self, ↓reduceIte]
      rw [em] at hpost ⊢
      exact XV.ifS_f hL s88 s89 r88 (by rw [v89]; exact t89) hc1
        (XV.ifS_f hL s88 s90 r88 (by rw [v90]; exact t90) hc2
          (XV.t11 hdt hfire hdl hcall hcom hd1 hn hL hlay hok hM he he0 he1 hT1 (hX (not_lt.1 h1)) hpost hℓt hℓat
            hℓc hℓac hg1 hg2 hXa hℓf hℓaf hℓa hℓb hℓc' hda hℓ1 hℓa1 hℓ2 hℓa2 hℓ3 hℓa3))

set_option maxHeartbeats 4000000 in
/-- **The tail of BL's round (R10 to R15) on the machine**: the frozen `TailBL`. -/
theorem tailBL_of : CallBL → DataT → DataL → CommitBL → FireBL → ExpBL → TailBL := by
  rintro ⟨xcall, Ca, ka, nS, nN, nA, hcall⟩ ⟨xdt, Ct, kt, hdt⟩ ⟨xdl, Cl, kl, hdl⟩ ⟨xcom, Cc, kc, hcom⟩
    ⟨xfire, Cf, kf, hfire⟩ ⟨Cx, kx, hexp⟩
  obtain ⟨C, k, hpoly⟩ := tl_poly Cx kx Ct kt Ca ka Cl kl Cc kc Cf kf
  refine ⟨xtail xdt xcall xfire xdl xcom, C, k, nS, nN, nA, ?_⟩
  intro d L w n m M K0 E E1 ℓa ℓ t A b c S st Ap Bp bp Gp kp lp s5 Γ P0 σ hd1 hn hL hlay hok hM he he0 he1 hE
    hI hp c1 c2 c4 hA hB hb hG hk hkg hkb hl hlg hlb hs hsb hw hΓ hpost hℓ hℓa
  set Xb := Cx * (d + n.size + (2 * E1 + 1) + 1) ^ kx with hXb
  have hZ := hpoly d m M.size n.size E1 Xb le_rfl
  have hT : TIn L n m K0 E E1 (mkCfg d n m A b c S) st t P0 Ap Bp bp Gp kp lp s5 Γ σ :=
    ⟨hI, hp, c1, c2, c4, hA, hB, hb, hG, hk, hkg, hkb, hl, hlg, hlb, hs, hsb, hw, hΓ, hE⟩
  have hcm : Cc * (d + E + 1) ^ kc ≤ Cc * (d + E1 + 1) ^ kc :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hfi : Cf * (d + E + 1) ^ kf ≤ Cf * (d + E1 + 1) ^ kf :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hpw1 := (tl_pow_req d E1 (4 * E1 + 2 * Xb + 3 * d) ℓ).1 (by omega)
  have hpw2 := (tl_pow_req d E1 (4 * E1 + 2 * Xb + 3 * d) ℓ).2 (by omega)
  have hpw3 := (tl_pow_req d E1 (8 * E1 + 3 * d + 2) ℓ).2 (by omega)
  -- the exponent of R11's point
  have hX : frob2 Bp ≤ 2 * ((par d n).Lam : ℚ) →
      ellExp (clearQ (callTOf (mkCfg d n m A b c S) st Bp bp Gp)) ≤ Xb := by
    intro hfr
    have bE := (tl_consts hI).2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [tl_callT]
    refine hexp d n m (2 * E1 + 1) A b c S _ _ _ Bp _ _ _ hd1 hn (fun i j => (hB i j).2.1) hfr
      (fun j => tl_wp_grid (par d n).p (par d n).pF E1 (par d n).eta bp Gp (tl_onG_eta d n)
        (fun j => (hb j).2.1) (fun j => (hG j).2.1) (bE.trans (pow_le_pow_right₀ (by norm_num) hE))
        (fun j => (hb j).2.2) (fun j => (hG j).2.2) j) ?_
    cases st.first
    · exact List.Mem.tail _ (List.Mem.head _)
    · exact List.Mem.head _
  refine XV.mono (XV.t10 hdt hfire hdl hcall hcom hd1 hn hL hlay hok hM he he0 he1 hT hX hpost (by omega) hpw1
    (by omega) (by omega) (by omega) (by omega) (by omega) hpw2 (by omega) (by omega) (by omega) (by omega)
    (by omega) hpw3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) ?_ fun _ h => h
  rw [r10Units_eq]
  unfold u11 u12 u13 u14
  rw [r12Units_eq, r13Units_eq]
  omega

end AdversarialBco.Bit.Transfer.BLM
