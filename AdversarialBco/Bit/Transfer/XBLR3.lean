/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLR2q

@[expose] public section

/-!
# BL's round on the machine, R3 PLAY and the round in the modes `off` and `guard`

The play leaf reads a point in the form of the play leaf (`ptE`); `ptE_eq` reads it as BL's rational point. In mode
`off` BL plays the frame centre (the array `aC`), in mode `guard` the position centre `μ_S`, written into the play
buffer `aPl` with the denominator `D_S` (`xR3g`). `BLInv.next` carries the invariant to the next round when the
persistent cells are unchanged. `xRound L xRun` is the round: R1, then the dispatch on the mode, `xRun` in mode `run`;
`XV.roundOG` is the round in the modes `off` and `guard`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix
open AdversarialBco.BitRAM (toE)

variable {d : ℕ}

/-! ## The play leaf -/

theorem ptE_eq {σ : Env d} {v : ℕ} {D : ℤ} {u : Fin d → ℤ} {q : Fin d → ℚ} (h0 : σ.arr v 0 = (D : ℝ))
    (hu : ∀ j : Fin d, σ.arr v (1 + j) = (u j : ℝ)) (hq : ∀ j, (u j : ℚ) / D = q j) : ptE σ v = toE q := by
  unfold ptE toE
  congr 1
  funext j
  rw [hu j, h0, ← hq j]
  push_cast
  rfl

theorem ptE_of_rep {σ : Env d} {v : ℕ} {c : Fin d → ℚ} (h : PtRep σ v c) : ptE σ v = toE c := by
  obtain ⟨D, -, h0, hj⟩ := h
  choose u hu hq using hj
  exact ptE_eq h0 (fun j => by rw [add_comm]; exact hu j) hq

/-! ## The invariant at the next round -/

/-- The persistent cells of `σ'` are those of `σ`. -/
def SamePers (σ σ' : Env d) : Prop :=
  (∀ j < 8, σ'.nat j = σ.nat j) ∧ (∀ y < nSP, σ'.sc y = σ.sc y) ∧ ∀ a < nAP, ∀ k, σ'.arr a k = σ.arr a k

theorem modeRep_pers {σ σ' : Env d} {p : ℕ} {mo : Mode d} (hs : SamePers σ σ') (h : ModeRep σ p mo) :
    ModeRep σ' p mo := by
  obtain ⟨-, hS, hA⟩ := hs
  have e : ∀ y < nSP, σ'.sc y = σ.sc y := hS
  cases mo with
  | off => simp only [ModeRep] at h ⊢; rw [e _ (by decide), h]
  | guard => simp only [ModeRep] at h ⊢; rw [e _ (by decide), h]
  | run st =>
    obtain ⟨h0, h1, ⟨Dm, hDm, hDm', hmu⟩, h3, h4, h5, h6, h7, h8⟩ := h
    refine ⟨by rw [e _ (by decide), h0], by rw [e _ (by decide), h1], ⟨Dm, hDm, by rw [e _ (by decide), hDm'],
      fun j => by rw [hA _ (by decide)]; exact hmu j⟩, fun i j => by rw [hA _ (by decide)]; exact h3 i j,
      fun i j => by rw [hA _ (by decide)]; exact h4 i j, fun j => by rw [hA _ (by decide)]; exact h5 j,
      by rw [e _ (by decide)]; exact h6, fun j => by rw [hA _ (by decide)]; exact h7 j,
      by rw [e _ (by decide)]; exact h8⟩

/-- The invariant passes to the next round when the persistent cells are unchanged, one round was played and the
coins of the round were read. -/
theorem BLInv.next {L : Layout} {n m K0 E : ℕ} {cfg : Cfg d} {mo : Mode d} {t : ℕ} {σ σ' : Env d}
    (h : BLInv L n m K0 E cfg mo t σ) (hs : SamePers σ σ') (hr : σ'.rounds = t + 1)
    (hd : σ'.draws = Sched.blkStart d K0 cfg.par.B (t + 1) 0) : BLInv L n m K0 E cfg mo (t + 1) σ' := by
  obtain ⟨hN, hS, hA⟩ := hs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := h.regs
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ := h.consts
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10⟩ := h.par
  obtain ⟨DS, hDS, hDS', hmu, hAS⟩ := h.pos
  obtain ⟨Dc, hDc, hDc', hc⟩ := h.ctr
  refine ⟨h.lay, ?_, ?_, ?_, ⟨DS, hDS, by rw [hS _ (by decide), hDS'], fun j => by rw [hA _ (by decide)]; exact hmu j,
    fun i j => by rw [hA _ (by decide)]; exact hAS i j⟩, ⟨Dc, hDc, by rw [hA _ (by decide), hDc'],
    fun j => by rw [hA _ (by decide)]; exact hc j⟩, modeRep_pers ⟨hN, hS, hA⟩ h.mode, hr, hd,
    ⟨fun y hy => by rw [hS y hy]; exact h.bnd.1 y hy, fun a ha k hk => by rw [hA a ha]; exact h.bnd.2 a ha k hk⟩⟩
  · exact ⟨by rw [hN _ (by decide), r0], by rw [hN _ (by decide), r1], by rw [hN _ (by decide), r2],
      by rw [hN _ (by decide), r3], by rw [hN _ (by decide), r4], by rw [hN _ (by decide), r5],
      by rw [hN _ (by decide), r6], by rw [hN _ (by decide), r7]⟩
  · exact ⟨by rw [hS _ (by decide), c0], by rw [hS _ (by decide), c1], by rw [hS _ (by decide), c2],
      by rw [hS _ (by decide), c3], by rw [hS _ (by decide), c4], by rw [hS _ (by decide), c5],
      by rw [hS _ (by decide), c6], by rw [hS _ (by decide), c7], by rw [hS _ (by decide), c8]⟩
  · exact ⟨by rw [hS _ (by decide), p0], by rw [hS _ (by decide), p1], by rw [hS _ (by decide), p2],
      by rw [hS _ (by decide), p3], by rw [hS _ (by decide), p4], by rw [hS _ (by decide), p5],
      by rw [hS _ (by decide), p6], by rw [hS _ (by decide), p7], by rw [hS _ (by decide), p8],
      by rw [hS _ (by decide), p9], by rw [hS _ (by decide), p10]⟩

theorem SamePers.trans {σ σ' σ'' : Env d} (h : SamePers σ σ') (h' : SamePers σ' σ'') : SamePers σ σ'' :=
  ⟨fun j hj => (h'.1 j hj).trans (h.1 j hj), fun y hy => (h'.2.1 y hy).trans (h.2.1 y hy),
    fun a ha k => (h'.2.2 a ha k).trans (h.2.2 a ha k)⟩

/-- A frame whose cells avoid the persistent ones keeps them. -/
theorem SamePers.ofFrame {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop} {σ σ' : Env d} (h : FrameA S N Ar σ σ')
    (hS : ∀ y, S y → nSP ≤ y) (hN : ∀ j, N j → 8 ≤ j) (hA : ∀ a k, Ar a k → nAP ≤ a) : SamePers σ σ' :=
  ⟨fun j hj => h.1 j fun h' => by have := hN j h'; omega, fun y hy => h.2.1 y fun h' => by have := hS y h'; omega,
    fun a ha k => h.2.2.1 a k fun h' => by have := hA a k h'; omega⟩

/-! ## The guard's play buffer -/

/-- `μ̂_{S,k}`, `k` in the register `rk`. -/
def ieMuS : IE := .arr aMuS rk

/-- R3 in mode `guard`: the play buffer `(D_S, μ̂_S)`. -/
def xR3g (L : Layout) : XCmd :=
  .seq (.prim (.frag (.nconst rr 0)))
  (.seq (toX (VL.aset L aPl rr sDS))
  (.seq (.prim (.frag (.nconst rr 1)))
    (xmapE L sZ tR ieMuS aPl rr rOne rk rD rOne)))

/-- The units of `xR3g`. -/
def r3gUnits (d : ℕ) : ℕ := 1 + (2 + (1 + (d * (2 + 6) + 3)))

theorem XV.r3g {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {σ : Env d}
    {E : ℕ} {DS : ℤ} {muS : Fin d → ℤ} (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0)
    (hDS : σ.sc sDS = DS) (hmu : ∀ k : Fin d, σ.arr aMuS k = muS k) (bDS : |DS| ≤ 2 ^ E)
    (bmu : ∀ k, |muS k| ≤ 2 ^ E) (hE : E < ℓ) (hd1 : 1 ≤ d) :
    XRunsB L X ℓa ℓ (xR3g L) σ (r3gUnits d) (fun σ' =>
      σ'.arr aPl 0 = (DS : ℝ) ∧ (∀ k : Fin d, σ'.arr aPl (1 + k) = (muS k : ℝ)) ∧
      σ'.draws = σ.draws ∧ FrameA SP NP AP σ σ') := by
  obtain ⟨hS, hN, hAr⟩ := hlay
  simp only [oE, rEE, aWE] at hS hN hAr
  have hda := asz_lt hL (a := 0) (by omega)
  have hℓ2 : (2 : ℤ) ^ E < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) hE
  refine XV.seq (XV.nconst hL (σ := σ) (i := rr) (by pomega) 0 (by positivity)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.aset hL (a := aPl) (i := rr) (x := sDS) (by pomega) (by pomega) (by pomega)
    (by simp only [Env.setNat_nat, ↓reduceIte]; unfold asz; nlinarith)
    (by simp only [Env.setNat_sc, hDS]; exact XV.abs_int_lt (lt_of_le_of_lt bDS hℓ2))) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.nconst hL (i := rr) (by pomega) 1 (by have := hL.1; omega)) fun σ3 e3 => ?_
  subst e3
  set σ3 := ((σ.setNat rr 0).setArr aPl ((σ.setNat rr 0).nat rr) ((σ.setNat rr 0).sc sDS)).setNat rr 1 with hσ3
  have s3 : ∀ y, σ3.sc y = σ.sc y := fun y => by simp only [hσ3, Env.setNat_sc, Env.setArr_sc]
  have n3 : ∀ j, j ≠ rr → σ3.nat j = σ.nat j := fun j h => by
    simp only [hσ3, Env.setNat_nat, Env.setArr_nat]; rw [ite_eq_right h, ite_eq_right h]
  have a3 : ∀ b k, b ≠ aPl → σ3.arr b k = σ.arr b k := fun b k h => by
    simp only [hσ3, Env.setNat_arr, Env.setArr_arr]; rw [ite_eq_right (fun h' => h h'.1)]
  have c30 : σ3.arr aPl 0 = (DS : ℝ) := by
    simp only [hσ3, Env.setNat_arr, Env.setArr_arr, Env.setNat_nat, Env.setNat_sc, ↓reduceIte]; simp [hDS]
  have F3 : FrameA SP NP AP σ σ3 :=
    (((FrameA.refl SP NP AP σ).setNat (i := rr) (by simp [NP]) _).setArr rfl _).setNat (i := rr) (by simp [NP]) _
  have d3 : σ3.draws = σ.draws := by simp only [hσ3, Env.setNat_draws, Env.setArr_draws]
  refine XV.mono (XV.mapE (E := E) (N := d) (base := 1) (st := 1) (F := vext muS) hL (σ := σ3) (z := sZ) (t := tR)
    (aB := aPl) (nr := rr) (nst := rOne) (nk := rk) (nn := rD) (none := rOne) (e := ieMuS)
    (by simp [ieMuS, IE.WF]; pomega) (by pomega) (by simp only [ieMuS, IE.scr]; pomega)
    (by rw [s3, hz]) (by pomega) (by pomega) (by pomega) (by pomega)
    (by pomega) (by pomega) (by decide) (by decide) (by decide)
    (by rw [n3 _ (by pomega), hD]) (by rw [n3 _ (by pomega), h1])
    (by simp [hσ3]) (by rw [n3 _ (by pomega), h1]) one_pos
    (fun k hk => by unfold asz; nlinarith) (by unfold asz at hda; nlinarith) (by unfold asz at hda; nlinarith)
    (by have := hL.1; omega) (by simp only [ieMuS, IE.top]; exact hE) ?_) (by simp [ieMuS, IE.units])
    fun σ4 ⟨x4, _, d4, F4⟩ => ?_
  · intro k hk σ' F' d' hk' hr'
    have ar' : σ'.arr aMuS k = muS ⟨k, hk⟩ := by
      rw [F'.2.2.1 aMuS k (fun h' => by simp at h'), a3 _ _ (by pomega)]; exact hmu ⟨k, hk⟩
    have hkd : k < asz d := by unfold asz; nlinarith
    refine ⟨⟨by rw [hk']; exact hkd, muS ⟨k, hk⟩, by rw [hk', ar'], bmu _⟩, ?_⟩
    simp only [ieMuS, IE.eval, hk', ar']
    rw [vext_lt _ hk]
  refine ⟨?_, fun k => ?_, by rw [d4, d3], F3.trans (F4.mono incSP_t incNP_k (fun b k h => h.1))⟩
  · rw [F4.2.2.1 _ _ (fun h => by omega), c30]
  · have := x4 k k.2
    rw [one_mul, vext_lt _ k.2] at this
    exact this

/-! ## The round in the modes `off` and `guard` -/

/-- The modes `off` and `guard`: play the frame centre (`sMode = 0`) or the position centre (`sMode = 1`). -/
def xOG (L : Layout) : XCmd :=
  .seq (toX (VL.sconst L sC2 1)) (xifS L sMode sC2 (xplay L aC) (.seq (xR3g L) (xplay L aPl)))

/-- BL's round: R1 DRAW, then the dispatch on the mode, `xRun` in mode `run` (`sMode = 2`). -/
def xRound (L : Layout) (xRun : XCmd) : XCmd :=
  .seq (xR1 L) (.seq (toX (VL.sconst L sC2 2)) (xifS L sMode sC2 (xOG L) xRun))

/-- The units of the round in the modes `off` and `guard`. -/
def ogUnits (d B : ℕ) : ℕ := r1Units d B + (1 + ((1 + (r3gUnits d + (d + 2) + 2)) + 1))

theorem samePers_setSc {σ : Env d} {y : ℕ} (hy : nSP ≤ y) (v : ℝ) : SamePers σ (σ.setSc y v) :=
  SamePers.ofFrame ((FrameA.refl (fun z => z = y) (fun _ => False) (fun _ _ => False) σ).setSc rfl v)
    (fun _ h => h ▸ hy) (fun _ h => h.elim) (fun _ _ h => h.elim)

theorem samePers_play {σ : Env d} (r : ℕ) (p : ℕ → E d) : SamePers σ { σ with rounds := r, pts := p } :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- **The round in the modes `off` and `guard`**: BL plays `playPt cfg mo ξ` (the frame centre, or `μ_S`), reads the
coins of R1, and the invariant holds at the next round with the same mode (`step` keeps `off` and `guard`). -/
theorem XV.roundOG {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {cs : ℕ → Bool}
    (hX : X.wb.cs = cs) {n m K0 E t : ℕ} {cfg : Cfg d} {mo : Mode d} {σ : Env d} (xRun : XCmd) (ξ : Fin d → ℚ)
    (hI : BLInv L n m K0 E cfg mo t σ) (hmo : mo = .off ∨ mo = .guard) (hd1 : 1 ≤ d) (hB1 : 1 ≤ cfg.par.B)
    (hE : E + 2 < ℓ) (hℓ : 4 * gsm_prec cfg.par.B + 4 ≤ ℓ) (hℓa : 4 * gsm_prec cfg.par.B + 2 < 2 ^ ℓa)
    (hda : d + 2 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xRound L xRun) σ (ogUnits d cfg.par.B) (fun σ' =>
      BLInv L n m K0 E cfg mo (t + 1) σ' ∧ σ'.pts = Function.update σ.pts t (toE (playPt cfg mo ξ))) := by
  have hlay' := hlay
  obtain ⟨hS, hN, hAr⟩ := hlay'
  simp only [oE, rEE, aWE] at hS hN hAr
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := hI.regs
  obtain ⟨c0, -⟩ := hI.consts
  have hℓ2 : ∀ {a : ℕ}, a < ℓ → (2 : ℤ) ^ a < 2 ^ ℓ := fun h => pow_lt_pow_right₀ (by norm_num) h
  have hmode : σ.sc sMode = 0 ∨ σ.sc sMode = 1 := by
    have := hI.mode
    rcases hmo with rfl | rfl
    · exact Or.inl this
    · exact Or.inr this
  -- R1
  refine XV.seq (XV.r1 hL hlay hX hB1 r7 r0 r3 r6 c0 hI.draws hℓa hℓ hda) fun σ1 ⟨_, _, d1, F1⟩ => ?_
  have P1 : SamePers σ σ1 := SamePers.ofFrame F1 (fun y h => by simp only [SR1, nSP, sZeta, oBM] at h ⊢; omega)
    (fun j h => by simp only [NR1, rJ, rT, rD2, rB] at h ⊢; omega) (fun a k h => by simp only [AR1, aGam, nAP] at h ⊢; omega)
  -- the dispatch
  refine XV.seq (XV.sconst hL (x := sC2) (by pomega) 2 rfl (by norm_num; exact_mod_cast hℓ2 (a := 1) (by omega)))
    fun σ2 e2 => ?_
  subst e2
  have P2 : SamePers σ (σ1.setSc sC2 ((2 : ℚ) : ℝ)) := P1.trans (samePers_setSc (by decide) _)
  have hm2 : (σ1.setSc sC2 ((2 : ℚ) : ℝ)).sc sMode = σ.sc sMode := P2.2.1 _ (by decide)
  have hb2 : ∀ v : ℝ, (v = 0 ∨ v = 1 ∨ v = 2) → |v| < 2 ^ ℓ := fun v hv => by
    have : (2 : ℝ) < 2 ^ ℓ := by exact_mod_cast hℓ2 (a := 1) (by omega)
    rcases hv with rfl | rfl | rfl <;> simp <;> linarith
  refine XV.mono (K := 1 + (r3gUnits d + (d + 2) + 2) + 1) (XV.ifS_t hL (by pomega) (by pomega) (hb2 _ (by rw [hm2]; tauto))
    (hb2 _ (by simp)) (by rw [hm2, scS]; rcases hmode with h | h <;> rw [h] <;> norm_num) ?_)
    le_rfl fun σ' h => h
  set σ2 := σ1.setSc sC2 ((2 : ℚ) : ℝ) with hσ2
  refine XV.seq (XV.sconst hL (x := sC2) (by pomega) 1 rfl (hb2 _ (by simp))) fun σ3 e3 => ?_
  subst e3
  have P3 : SamePers σ (σ2.setSc sC2 ((1 : ℚ) : ℝ)) := P2.trans (samePers_setSc (by decide) _)
  have hm3 : (σ2.setSc sC2 ((1 : ℚ) : ℝ)).sc sMode = σ.sc sMode := P3.2.1 _ (by decide)
  have hr3 : (σ2.setSc sC2 ((1 : ℚ) : ℝ)).rounds = t := by
    simp only [hσ2, Env.setSc_rounds]; rw [F1.2.2.2.1, hI.rounds]
  have hd3 : (σ2.setSc sC2 ((1 : ℚ) : ℝ)).draws = Sched.blkStart d K0 cfg.par.B (t + 1) 0 := by
    simp only [hσ2, Env.setSc_draws]; exact d1
  have hp3 : (σ2.setSc sC2 ((1 : ℚ) : ℝ)).pts = σ.pts := by simp only [hσ2, Env.setSc_pts]; exact F1.2.2.2.2
  have hda' : ∀ j ≤ d, j < asz d := fun j hj => by unfold asz; nlinarith
  rcases hmo with rfl | rfl
  · -- off: play the frame centre
    have hm0 : σ.sc sMode = 0 := hI.mode
    refine XV.mono (XV.ifS_t hL (by pomega) (by pomega) (hb2 _ (by rw [hm3, hm0]; simp)) (hb2 _ (by simp))
      (by rw [hm3, hm0, scS]; norm_num)
      (XV.play hL hd1 (v := aC) (by pomega) fun j hj => ?_)) (by omega) fun σ' e' => ?_
    · rw [P3.2.2 _ (by decide)]
      obtain ⟨z, hz, bz⟩ := hI.bnd.2 aC (by decide) j (hda' j hj)
      rw [hz]; exact XV.abs_int_lt (lt_of_le_of_lt bz (hℓ2 (by omega)))
    subst e'
    refine ⟨hI.next (P3.trans (samePers_play _ _)) (by rw [hr3]) (by exact hd3), ?_⟩
    simp only [hp3, hr3, playPt]
    congr 1
    rw [ptE_of_rep (σ := σ2.setSc sC2 ((1 : ℚ) : ℝ))]
    obtain ⟨D, hD, h0, hj⟩ := hI.ctr
    exact ⟨D, hD, by rw [P3.2.2 _ (by decide), h0], fun j => by rw [P3.2.2 _ (by decide)]; exact hj j⟩
  · -- guard: play the position centre
    have hm1 : σ.sc sMode = 1 := hI.mode
    obtain ⟨DS, hDS, hDS', hmu, -⟩ := hI.pos
    choose muS hmuS hmuq using hmu
    have bDS : |DS| ≤ 2 ^ E := by
      obtain ⟨z, hz, bz⟩ := hI.bnd.1 sDS (by decide)
      rw [hDS'] at hz; rw [show DS = z by exact_mod_cast hz]; exact bz
    have bmu : ∀ k, |muS k| ≤ 2 ^ E := fun k => by
      obtain ⟨z, hz, bz⟩ := hI.bnd.2 aMuS (by decide) k (hda' k k.2.le)
      rw [hmuS k] at hz; rw [show muS k = z by exact_mod_cast hz]; exact bz
    refine XV.mono (XV.ifS_f hL (by pomega) (by pomega) (hb2 _ (by rw [hm3, hm1]; simp)) (hb2 _ (by simp))
      (by rw [hm3, hm1, scS]; norm_num) (XV.seq (XV.r3g hL hlay (σ := σ2.setSc sC2 ((1 : ℚ) : ℝ)) (E := E) (DS := DS) (muS := muS)
        (by rw [P3.1 _ (by decide), r0]) (by rw [P3.1 _ (by decide), r3]) (by rw [P3.2.1 _ (by decide), c0])
        (by rw [P3.2.1 _ (by decide), hDS']) (fun k => by rw [P3.2.2 _ (by decide), hmuS k]) bDS bmu (by omega) hd1)
        fun σ4 ⟨a40, a4k, d4, F4⟩ => ?_)) le_rfl fun σ' h => h
    have P4 : SamePers σ σ4 := P3.trans (SamePers.ofFrame F4 (fun y h => by simp only [SP, sPtN, sPtD, sC1, sC2, tR, nSP] at h ⊢; omega)
      (fun j h => by simp only [NP, rr, rk] at h ⊢; omega) (fun a k h => by simp only [AP, aPl, nAP] at h ⊢; omega))
    refine XV.mono (XV.play hL hd1 (v := aPl) (by pomega) fun j hj => ?_) le_rfl fun σ' e' => ?_
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [a40]; exact XV.abs_int_lt (lt_of_le_of_lt bDS (hℓ2 (by omega)))
      · obtain ⟨k, rfl⟩ : ∃ k, j = 1 + k := ⟨j - 1, by omega⟩
        rw [a4k ⟨k, by omega⟩]; exact XV.abs_int_lt (lt_of_le_of_lt (bmu _) (hℓ2 (by omega)))
    subst e'
    have hr4 : σ4.rounds = t := by rw [F4.2.2.2.1, hr3]
    refine ⟨hI.next (P4.trans (samePers_play _ _)) (by rw [hr4]) (by rw [d4, hd3]), ?_⟩
    simp only [F4.2.2.2.2, hp3, hr4, playPt]
    congr 1
    exact ptE_eq a40 a4k hmuq

end AdversarialBco.Bit.Transfer.BLM
