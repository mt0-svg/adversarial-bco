/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ProgMachSplit
public import AdversarialBco.Unified.ProgOR1
public import AdversarialBco.Unified.ProgOOG
public import AdversarialBco.Unified.ProgOR3

@[expose] public section

/-!
# R1a, R1b, the play in the modes `off` and `guard`, R3 at BL-OW's round

The BL-OW copies of the specifications of R1a and R1b (Unified/ProgOR1.lean), of the play in the modes `off` and `guard`
(Unified/ProgOOG.lean) and of R3 (Unified/ProgOR3.lean): the same commands (`xR1a`, `xR1b`, `xOG`, `xR3`) and constants,
the proofs read at `RdW`.
None of these blocks reads a field in which `parOW` differs from `parO`.
-/

namespace AdversarialBco.UW.ProgW

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Unified.ProgO
open AdversarialBco.Bit.BLP (Cfg Mode St)
open AdversarialBco.Bit (gsm_prec)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

/-- A block's facts from the invariant: `2 p_B ≤ E`. -/
theorem prec_le_EW {R : RdW d} {σ : Env d} (hI : R.Inv σ) : 2 * gsm_prec R.pB ≤ R.E := by
  obtain ⟨-, -, -, -, c2g, -⟩ := hI.consts
  exact pow_two_le (hI.sc_abs (y := s2g) (by decide) (by rw [c2g]; push_cast; rfl))



/-- The bit widths and the budget of R1a and R1b from a round's hypotheses. -/
theorem r1_widthsW {R : RdW d} {σ : Env d} (hH : R.Hyp kR1 (R.bud kR1)) (hI : R.Inv σ) :
    4 * gsm_prec R.pB + 2 < 2 ^ R.ℓa ∧ 4 * gsm_prec R.pB + 4 ≤ R.ℓ ∧ d + 2 < 2 ^ R.ℓa ∧
      r1aUnits d R.pB ≤ R.bud kR1 ∧ bmUnits R.pB + 18 ≤ R.bud kR1 := by
  have hg := prec_le_EW hI
  have hdW : d ≤ R.W := by show d ≤ wU d R.n R.δ R.r0 R.R0 R.a; unfold wU; omega
  set x := R.W + R.E + 1 with hx
  have hx1 : 1 ≤ x := by omega
  obtain ⟨p1, p2, p3⟩ := pow3_facts hx1
  have hb : R.bud kR1 = 400 * x ^ 3 := rfl
  have hEx : R.E + 1 ≤ x := by omega
  have hgx : gsm_prec R.pB + 1 ≤ x := by omega
  have hbm : bmUnits R.pB ≤ 300 * x ^ 2 :=
    (Unified.ProgO.bmUnits_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hgx 2))
  have hnb : Bit.Sched.nBlk d - 1 ≤ x := by unfold Bit.Sched.nBlk; omega
  have hr1 : r1aUnits d R.pB ≤ 400 * x ^ 3 := by
    unfold r1aUnits
    have : (Bit.Sched.nBlk d - 1) * (bmUnits R.pB + 18) ≤ x * (300 * x ^ 2 + 18) :=
      Nat.mul_le_mul hnb (by omega)
    have e : x * (300 * x ^ 2 + 18) = 300 * x ^ 3 + 18 * x := by ring
    omega
  have hK1 : 4 * gsm_prec R.pB + 4 ≤ R.bud kR1 := by rw [hb]; omega
  have hd : d + 2 < R.bud kR1 := by rw [hb]; omega
  exact ⟨by have := hH.hℓa; omega, hK1.trans hH.hℓ, lt_of_lt_of_le hd (le_of_lt hH.hℓa), hr1.trans_eq hb.symm,
    by rw [hb]; omega⟩

/-! ## The two contracts -/

theorem specR1aW : SpecR1aW (fun L => .base (xR1a L)) kR1 := by
  intro d R σ hH hI
  obtain ⟨w1, w2, w3, w4, -⟩ := r1_widthsW hH hI
  obtain ⟨r0, -, -, r3, -, -, r6, r7⟩ := hI.regs
  obtain ⟨c0, -⟩ := hI.consts
  refine XVO.mono (XVO.ofX (Unified.ProgO.XV.r1a hH.lay (blLay_of hH.room le_rfl le_rfl le_rfl) (cs := R.w.cs) rfl
    (Unified.ProgO.parO_B_pos _ _ _) r7 r0 r3 r6 c0 hI.draws w1 w2 w3)) w4 fun σ' ⟨hg, hd, F⟩ => ?_
  exact ⟨SamePers.ofFrame F (fun y h => by simp only [SR1a] at h; uomega) (fun j h => by simp only [NR1a] at h; uomega)
    (fun a k h => by simp only [AR1] at h; uomega), by rw [F.2.2.2.1, hI.rounds], hd, hg⟩

theorem specR1bW : SpecR1bW (fun L => .base (xR1b L)) kR1 := by
  intro d R σ0 σ hH hI hP hdr
  obtain ⟨w1, w2, w3, -, w5⟩ := r1_widthsW hH hI
  obtain ⟨r0, -, -, r3, -, -, r6, r7⟩ := hI.regs
  obtain ⟨c0, -⟩ := hI.consts
  have eN : ∀ j < 8, σ.nat j = σ0.nat j := hP.1
  refine XVO.mono (XVO.ofX (Unified.ProgO.XV.r1b hH.lay (blLay_of hH.room le_rfl le_rfl le_rfl) (cs := R.w.cs) rfl
    (Unified.ProgO.parO_B_pos _ _ _) (by rw [eN _ (by decide), r7]; rfl) (by rw [eN _ (by decide), r0]) (by rw [eN _ (by decide), r3])
    (by rw [eN _ (by decide), r6]) (by rw [hP.2.1 _ (by decide), c0]) hdr w1 w2 w3)) w5 fun σ' ⟨hz, hd, F⟩ => ?_
  refine ⟨hz, F.2.2.2.1, hd, (FrameC.ofA F).mono (fun y h => ?_) (fun j h => ?_) (fun _ _ h => h.elim)⟩
  · rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by simp only [oBM, tR] at h ⊢; omega)
  · simp only [NR1a, NScr] at h ⊢; uomega


theorem specOGW : SpecOGW (fun L => .base (Unified.ProgO.xOG L)) kOG := by
  intro d R σ0 σ hH hI hmo hA
  have hNS : sC1 < R.L.NS := by have := hH.room.1; simp only [kOG, sC1] at *; omega
  have hNN : rk < R.L.NN := by have := hH.room.2.1; simp only [kOG, rk] at *; omega
  have hNA : aPl < R.L.NA := by have := hH.room.2.2; simp only [kOG, aPl] at *; omega
  have hdW : d ≤ R.W := by show d ≤ wU d R.n R.δ R.r0 R.R0 R.a; unfold wU; omega
  have hb : R.bud kOG = 20 * (R.W + R.E + 1) := by simp [RdW.bud, kOG]
  have hEℓ : R.E < R.ℓ := by have := hH.hℓ; omega
  have hda : d + 2 < 2 ^ R.ℓa := by have := hH.hℓa; omega
  obtain ⟨r0, -, -, r3, -⟩ := hI.regs
  have eN : ∀ j < 8, σ.nat j = σ0.nat j := hA.pers.1
  have eA : ∀ k, σ.arr aC k = σ0.arr aC k := hA.pers.2.2 aC (by decide)
  have hℓ2 : ∀ {z : ℤ}, |z| ≤ 2 ^ R.E → |(z : ℝ)| < 2 ^ R.ℓ := fun hz => by
    have : (2 : ℝ) ^ R.E < 2 ^ R.ℓ := pow_lt_pow_right₀ (by norm_num) hEℓ
    rw [← Int.cast_abs]
    exact lt_of_le_of_lt (by exact_mod_cast hz) this
  have hd1 : 1 ≤ d := hH.inU.hd
  have hbC : ∀ j ≤ d, |σ.arr aC j| < 2 ^ R.ℓ := fun j hj => by
    obtain ⟨z, hz, bz⟩ := hI.bnd.2 aC (by decide) j (Unified.ProgO.le_asz hd1 hj)
    rw [eA, hz]; exact hℓ2 bz
  refine XVO.mono (XVO.ofX (Unified.ProgO.XV.og hH.lay hNS hNN hNA hH.inU.hd (by rw [eN _ (by decide), r0]) (by rw [eN _ (by decide), r3])
    hda hbC)) (by rw [hb]; nlinarith) fun σ' ⟨hc, hdr, F⟩ => ?_
  have hpers : SamePers σ σ' := SamePers.ofFrame F (fun y h => by simp only [SOG] at h; subst h; decide)
    (fun j h => by rcases h with h | h <;> subst h <;> decide) (fun a k h => by simp only [AOG] at h; subst h; decide)
  have hplay : R.play = R.c.a := by
    show playPtO R.w.orc R.c R.mo R.ξ = R.c.a
    rcases hmo with h | h <;> rw [h] <;> rfl
  refine ⟨⟨hA.pers.trans hpers, by rw [F.2.2.2.1, hA.rounds], by rw [hdr, hA.draws], fun i => ?_⟩, ?_, ?_⟩
  · rw [F.2.2.1 aGam i (by simp [AOG, aGam, aPl])]; exact hA.gam i
  · obtain ⟨D, hD, h0, hj⟩ := hI.ctr
    refine ⟨D, hD, by rw [hc 0 (Nat.zero_le _), eA, h0], fun j => ?_⟩
    obtain ⟨x, hx, hq⟩ := hj j
    exact ⟨x, by rw [hc _ (by omega), eA, hx], by rw [hplay]; exact hq⟩
  · intro j hj
    rw [hc j hj]; exact hbC j hj

theorem specR3W : SpecR3W xR3 kR3 := by
  intro d R σ0 σ hH hI hP hr hpt
  have hNS : 272 ≤ R.L.NS := hH.room.1
  have hNN : 11 ≤ R.L.NN := hH.room.2.1
  obtain ⟨-, -, -, r3, r4, -, -, r7⟩ := hI.regs
  obtain ⟨-, c1, c2, -, c4, -, c6, -⟩ := hI.consts
  have eN : ∀ j < 8, σ.nat j = σ0.nat j := hP.1
  have eS : ∀ y < nSP, σ.sc y = σ0.sc y := hP.2.1
  have hnE : R.n ≤ 2 ^ R.E := by
    have h := hI.sc_abs (y := sN) (by decide) (z := (R.n : ℤ)) (by rw [c1]; push_cast; rfl)
    rw [abs_of_nonneg (by positivity)] at h
    exact_mod_cast h
  have hNeE : R.c.par.Ne ≤ 2 ^ R.E := by
    have h := hI.sc_abs (y := sNe) (by decide) (z := (R.c.par.Ne : ℤ)) (by rw [c6]; push_cast; rfl)
    rw [abs_of_nonneg (by positivity)] at h
    exact_mod_cast h
  have hBE : R.c.par.B ≤ R.E := by
    have h : 2 * gsm_prec R.c.par.B ≤ R.E := pow_two_le (hI.sc_abs (y := s2g) (by decide) (by rw [c4]; push_cast; rfl))
    have : R.c.par.B ≤ gsm_prec R.c.par.B := by unfold gsm_prec; omega
    omega
  have hpE : R.c.par.p ≤ R.E := pow_two_le (hI.sc_abs (y := s2p) (by decide) (by rw [c2]; push_cast; rfl))
  have hb : R.bud kR3 = 400 * (R.W + R.E + 1) := by simp [RdW.bud, kR3]
  have hℓ := hH.hℓ
  have hℓa := hH.hℓa
  rw [hb] at hℓ hℓa
  refine XVO.mono (K := 300 * (R.E + 1) + 1) (XVO.seq (XVO.ofX (Unified.ProgO.XV.qO hH.lay (E := R.E) hNS hNN (by rw [eS _ (by decide), c1]) (by rw [eS _ (by decide), c6]; rfl)
    (by rw [eN _ (by decide), r7]; rfl) (by rw [eN _ (by decide), r4]; rfl) (by rw [eN _ (by decide), r3]) hnE hNeE
    hBE hpE (by omega) (by omega))) fun σ1 h1 => ?_) (by rw [hb]; omega) fun _ h => h
  obtain ⟨q1, T1⟩ := h1
  have p1 : σ1.nat rP = R.c.par.p := by rw [T1.1 _ (by decide), eN _ (by decide), r4]; rfl
  set S := 9 + 4 * Nat.sqrt (14 * R.n * R.c.par.Ne).size + Nat.sqrt (2 * R.c.par.B) with hS
  have hSle : S ≤ 9 + 4 * (2 * R.E + 5) + 2 * R.E := by
    have hsz : (14 * R.n * R.c.par.Ne).size ≤ 2 * R.E + 5 := by
      have hnNe : R.n * R.c.par.Ne ≤ 2 ^ (2 * R.E) := by
        calc R.n * R.c.par.Ne ≤ 2 ^ R.E * 2 ^ R.E := Nat.mul_le_mul hnE hNeE
          _ = 2 ^ (2 * R.E) := by rw [← pow_add]; ring_nf
      rw [Nat.size_le]
      have : 2 ^ (2 * R.E + 5) = 32 * 2 ^ (2 * R.E) := by rw [pow_add]; ring
      have : 14 * R.n * R.c.par.Ne = 14 * (R.n * R.c.par.Ne) := by ring
      have := Nat.mul_le_mul_left 14 hnNe
      have := Nat.one_le_two_pow (n := 2 * R.E)
      omega
    have := (Nat.sqrt_le_self (14 * R.n * R.c.par.Ne).size).trans hsz
    have := (Nat.sqrt_le_self (2 * R.c.par.B)).trans (le_refl _)
    omega
  have hcl : Nat.clog 2 S ≤ S := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hq : σ1.nat rQO = R.c.qO := q1
  have hqℓ : σ1.nat rQO < R.ℓ := by rw [q1]; omega
  have hW : 1 ≤ R.W + R.E + 1 := by omega
  refine XVO.mono (XVO.obsR hH.lay (x := sObs) (p := rP) (q := rQO) (by simp only [sObs]; omega)
    (by simp only [rP]; omega) (by simp only [rQO]; omega) (by rw [p1]; omega) hqℓ (by rw [p1]; omega)
    (by omega)) (by omega) fun σ2 e2 => ?_
  subst e2
  have r1 : σ1.rounds = R.t + 1 := by rw [T1.2.2.2.2.1, hr]
  have hfb : fbE R.ctx.X σ1 = R.w.f R.t (toE R.play) + R.w.noise R.t := by
    unfold fbE
    rw [ite_eq_right (by omega), r1, Nat.add_sub_cancel, T1.2.2.2.2.2, hpt]
    rfl
  refine ⟨?_, by simp [T1.2.2.2.2.1], by simp [T1.2.2.2.1], ?_, ?_, ?_⟩
  · simp only [Env.setSc_sc, ite_true, hq, p1, hfb]
    rfl
  · intro j hj
    simp only [Env.setSc_nat]
    exact T1.1 j (by simp only [NScr] at hj; omega)
  · intro y hy
    simp only [SR3, not_or] at hy
    rw [Env.setSc_sc, ite_eq_right hy.1]
    exact T1.2.1 y (by simp only [tR] at hy; omega)
  · intro b k _
    simp only [Env.setSc_arr, T1.2.2.1]

theorem progR1aW : ProgR1aW := ⟨_, _, specR1aW⟩

theorem progR1bW : ProgR1bW := ⟨_, _, specR1bW⟩

theorem progOGW : ProgOGW := ⟨_, _, specOGW⟩

theorem progR3W : ProgR3W := ⟨_, _, specR3W⟩

end AdversarialBco.UW.ProgW
