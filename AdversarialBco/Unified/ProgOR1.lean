/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOSplit

@[expose] public section

/-!
# R1a and R1b, the draw blocks and the dither block of BL-O's round

v2.1's R1 (Bit/Transfer/XBLR1.lean) runs BM-INT on the `nBlk d` blocks of the round in one loop. BL-O splits it: R1a
(`xR1a`) runs the loop body `xR1body` on the blocks `0, ..., nBlk d - 2`, which give `Γ_0, ..., Γ_{d-1}` (block `j`
gives `Γ_{2j}`, `Γ_{2j+1}`), before the play; R1b (`xR1b`) runs it on the last block `(d + 1)/2 = nBlk d - 1`, which
gives `Γ_ζ`, after the reading. Both run on the bit machine's language, under `base`.

`progR1a : ProgR1a` and `progR1b : ProgR1b`, the contracts `SpecR1a`, `SpecR1b` of ProgOSplit.lean.
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Bit.BLP (Cfg Mode St)
open AdversarialBco.Bit (gsm_prec)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

/-- The bound `nBlk d - 1` of R1a's loop. -/
abbrev rX : ℕ := 22

/-- `lomega` with `rX` unfolded. -/
macro "uomega" : tactic => `(tactic| ((try simp only [rX] at *) <;> lomega))

/-- R1a: `rD2 := d + 2`, `rX := nBlk d - 1`, then BM-INT on the blocks `0, ..., nBlk d - 2`. -/
def xR1a (L : Layout) : XCmd :=
  .seq (.prim (.frag (.nadd rD2 rD rOne))) (.seq (.prim (.frag (.nadd rD2 rD2 rOne)))
    (.seq (.prim (.frag (.nsub rX rNb rOne))) (xforN rJ rX rOne (xR1body L))))

/-- R1b: `rD2 := d + 2`, `rJ := nBlk d - 1`, then BM-INT on the last block. -/
def xR1b (L : Layout) : XCmd :=
  .seq (.prim (.frag (.nadd rD2 rD rOne))) (.seq (.prim (.frag (.nadd rD2 rD2 rOne)))
    (.seq (.prim (.frag (.nsub rJ rNb rOne))) (xR1body L)))

/-- The units of R1a. -/
def r1aUnits (d B : ℕ) : ℕ := (Bit.Sched.nBlk d - 1) * (bmUnits B + 18) + 6

/-- The cells R1a changes. -/
def SR1a (y : ℕ) : Prop := oBM ≤ y ∧ y < oBM + 43
def NR1a (j : ℕ) : Prop := j = rJ ∨ j = rT ∨ j = rD2 ∨ j = rX ∨ (rB < j ∧ j < rB + 12)

/-- The slots R1b changes. -/
def SR1bB (y : ℕ) : Prop := y = sZeta ∨ (oBM ≤ y ∧ y < oBM + 43)

set_option maxHeartbeats 1000000 in
/-- **R1a on the bit machine's language**: from the start of round `t` on the schedule, `Γ_i` (`i < d`) and the
coins of the blocks `0, ..., nBlk d - 2`. -/
theorem XV.r1a {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {cs : ℕ → Bool}
    (hX : X.wb.cs = cs) {K0 B t : ℕ} {σ : Env d} (hB1 : 1 ≤ B) (hB : σ.nat rB = B) (hD : σ.nat rD = d)
    (h1 : σ.nat rOne = 1) (hNb : σ.nat rNb = Bit.Sched.nBlk d) (hz : σ.sc sZ = 0)
    (hdr : σ.draws = Bit.Sched.blkStart d K0 B t 0) (hℓa : 4 * gsm_prec B + 2 < 2 ^ ℓa)
    (hℓ : 4 * gsm_prec B + 4 ≤ ℓ) (hda : d + 2 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xR1a L) σ (r1aUnits d B) (fun σ' =>
      (∀ i : Fin d, σ'.arr aGam i = gamI cs K0 B d t i) ∧
      σ'.draws = Bit.Sched.blkStart d K0 B t (Bit.Sched.nBlk d - 1) ∧ FrameA SR1a NR1a (AR1 d) σ σ') := by
  have hlay' := hlay
  obtain ⟨hS, hN, hA⟩ := hlay'
  have hnb : 2 * Bit.Sched.nBlk d ≤ d + 3 := by unfold Bit.Sched.nBlk; omega
  have hnb' : d ≤ 2 * (Bit.Sched.nBlk d - 1) := by unfold Bit.Sched.nBlk; omega
  have hzn : Bit.Sched.nBlk d - 1 = (d + 1) / 2 := by unfold Bit.Sched.nBlk; omega
  refine XV.mono (K := 1 + (1 + (1 + ((Bit.Sched.nBlk d - 1) * (bmUnits B + 15 + 3) + 3)))) ?_
    (by unfold r1aUnits; ring_nf; omega) fun _ h => h
  refine XV.seq (XV.nadd hL (σ := σ) (i := rD2) (a := rD) (b := rOne) (by uomega) (by uomega) (by uomega)
    (by rw [hD]; omega) (by rw [h1]; omega)) fun σ0 e0 => ?_
  subst e0
  refine XV.seq (XV.nadd hL (i := rD2) (a := rD2) (b := rOne) (by uomega) (by uomega) (by uomega)
    (by simp [hD]; omega) (by rw [Env.setNat_nat, ite_eq_right (by uomega), h1]; omega)) fun σ0 e0 => ?_
  subst e0
  set σ1 := (σ.setNat rD2 (σ.nat rD + σ.nat rOne)).setNat rD2
    ((σ.setNat rD2 (σ.nat rD + σ.nat rOne)).nat rD2 + (σ.setNat rD2 (σ.nat rD + σ.nat rOne)).nat rOne) with hσ1
  have n1 : σ1.nat rNb = Bit.Sched.nBlk d := by simp [hσ1, hNb]
  have o1 : σ1.nat rOne = 1 := by simp [hσ1, h1]
  refine XV.seq (XV.nsub hL (σ := σ1) (i := rX) (a := rNb) (b := rOne) (by uomega) (by uomega) (by uomega)
    (by rw [n1]; omega) (by rw [o1]; omega) (by rw [n1, o1]; unfold Bit.Sched.nBlk; omega)) fun σ0 e0 => ?_
  subst e0
  set σ0 := σ1.setNat rX (σ1.nat rNb - σ1.nat rOne) with hσ0
  have F0 : FrameA SR1a NR1a (AR1 d) σ σ0 :=
    (((FrameA.refl _ _ _ σ).setNat (Or.inr (Or.inr (Or.inl rfl))) _).setNat (Or.inr (Or.inr (Or.inl rfl))) _).setNat
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _
  have dd0 : σ0.nat rD2 = d + 2 := by simp [hσ0, hσ1, hD, h1]
  have x0 : σ0.nat rX = Bit.Sched.nBlk d - 1 := by simp [hσ0, n1, o1]
  have o0 : σ0.nat rOne = 1 := by simp [hσ0, o1]
  let J : ℕ → Env d → Prop := fun j σ' => σ'.draws = Bit.Sched.blkStart d K0 B t j ∧ σ'.nat rD2 = d + 2 ∧
    (∀ i, i < d → i < 2 * j → σ'.arr aGam i = gamI cs K0 B d t i) ∧ FrameA SR1a NR1a (AR1 d) σ σ'
  refine XV.mono (XV.forN hL (i := rJ) (n := rX) (one := rOne) (body := xR1body L) (by uomega) (by uomega)
    (by uomega) (by uomega) (by uomega) (Bit.Sched.nBlk d - 1) (bmUnits B + 15) (by omega) J σ0 x0 o0
    ⟨by simp [hσ0, hσ1, hdr], by simp [dd0], fun i _ h => absurd h (by omega), F0.setNat (Or.inl rfl) 0⟩ ?_) le_rfl
    fun σ' ⟨⟨hd', _, ha', F'⟩, _⟩ => ⟨fun i => ha' i i.2 (by omega), hd', F'⟩
  intro j hj σ' ⟨hd', hdd', ha', F'⟩ hjj hjn hj1
  have nB : σ'.nat rB = B := by rw [F'.1 rB (by simp only [NR1a]; uomega), hB]
  have nD : σ'.nat rD = d := by rw [F'.1 rD (by simp only [NR1a]; uomega), hD]
  have zz : σ'.sc sZ = 0 := by rw [F'.2.1 sZ (by simp only [SR1a]; uomega), hz]
  refine XV.mono (XV.r1body hL hlay hX hB1 nB nD hj1 hdd' hjj zz hd' hℓa hℓ (by omega) hda) le_rfl
    fun σ'' ⟨hd'', ha'', hz'', F''⟩ => ?_
  have nJ : σ''.nat rJ = j := by rw [F''.1 rJ (by simp only [NB1]; uomega), hjj]
  have nN : σ''.nat rX = Bit.Sched.nBlk d - 1 := by rw [F''.1 rX (by simp only [NB1]; uomega), hjn]
  have nO : σ''.nat rOne = 1 := by rw [F''.1 rOne (by simp only [NB1]; uomega), hj1]
  have nD2 : σ''.nat rD2 = d + 2 := by rw [F''.1 rD2 (by simp only [NB1]; uomega), hdd']
  refine ⟨nJ, nN, nO, by simp [hd''], by simp [nD2], fun i hi hi2 => ?_, ?_⟩
  · simp only [Env.setNat_arr]
    by_cases hij : i = 2 * j ∨ i = 2 * j + 1
    · exact ha'' i hi hij
    · rw [F''.2.2.1 aGam i (fun h => hij h.2.2)]
      exact ha' i hi (by omega)
  · refine (F'.trans (F''.mono (fun y hy => ?_) (fun i hi => ?_) (fun a k hk => ⟨hk.1, hk.2.1⟩))).setNat
      (Or.inl rfl) _
    · rcases hy with h | h
      · exact absurd h.2 (by omega)
      · exact h
    · rcases hi with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

set_option maxHeartbeats 1000000 in
/-- **R1b on the bit machine's language**: from the coins `blkStart t (nBlk d - 1)`, `Γ_ζ` and the coins of the
start of round `t + 1`. -/
theorem XV.r1b {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {cs : ℕ → Bool}
    (hX : X.wb.cs = cs) {K0 B t : ℕ} {σ : Env d} (hB1 : 1 ≤ B) (hB : σ.nat rB = B) (hD : σ.nat rD = d)
    (h1 : σ.nat rOne = 1) (hNb : σ.nat rNb = Bit.Sched.nBlk d) (hz : σ.sc sZ = 0)
    (hdr : σ.draws = Bit.Sched.blkStart d K0 B t (Bit.Sched.nBlk d - 1)) (hℓa : 4 * gsm_prec B + 2 < 2 ^ ℓa)
    (hℓ : 4 * gsm_prec B + 4 ≤ ℓ) (hda : d + 2 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xR1b L) σ (bmUnits B + 18) (fun σ' =>
      σ'.sc sZeta = zetI cs K0 B d t ∧ σ'.draws = Bit.Sched.blkStart d K0 B (t + 1) 0 ∧
      FrameA SR1bB NR1a (fun _ _ => False) σ σ') := by
  have hlay' := hlay
  obtain ⟨hS, hN, hA⟩ := hlay'
  have hzn : Bit.Sched.nBlk d - 1 = (d + 1) / 2 := by unfold Bit.Sched.nBlk; omega
  have hnb : Bit.Sched.nBlk d - 1 + 1 = Bit.Sched.nBlk d := by unfold Bit.Sched.nBlk; omega
  refine XV.mono (K := 1 + (1 + (1 + (bmUnits B + 15)))) ?_ (by omega) fun _ h => h
  refine XV.seq (XV.nadd hL (σ := σ) (i := rD2) (a := rD) (b := rOne) (by uomega) (by uomega) (by uomega)
    (by rw [hD]; omega) (by rw [h1]; omega)) fun σ0 e0 => ?_
  subst e0
  refine XV.seq (XV.nadd hL (i := rD2) (a := rD2) (b := rOne) (by uomega) (by uomega) (by uomega)
    (by simp [hD]; omega) (by rw [Env.setNat_nat, ite_eq_right (by uomega), h1]; omega)) fun σ0 e0 => ?_
  subst e0
  set σ1 := (σ.setNat rD2 (σ.nat rD + σ.nat rOne)).setNat rD2
    ((σ.setNat rD2 (σ.nat rD + σ.nat rOne)).nat rD2 + (σ.setNat rD2 (σ.nat rD + σ.nat rOne)).nat rOne) with hσ1
  have n1 : σ1.nat rNb = Bit.Sched.nBlk d := by simp [hσ1, hNb]
  have o1 : σ1.nat rOne = 1 := by simp [hσ1, h1]
  refine XV.seq (XV.nsub hL (σ := σ1) (i := rJ) (a := rNb) (b := rOne) (by uomega) (by uomega) (by uomega)
    (by rw [n1]; omega) (by rw [o1]; omega) (by rw [n1, o1]; unfold Bit.Sched.nBlk; omega)) fun σ0 e0 => ?_
  subst e0
  set σ0 := σ1.setNat rJ (σ1.nat rNb - σ1.nat rOne) with hσ0
  have F0 : FrameA SR1bB NR1a (fun _ _ => False) σ σ0 :=
    (((FrameA.refl _ _ _ σ).setNat (Or.inr (Or.inr (Or.inl rfl))) _).setNat (Or.inr (Or.inr (Or.inl rfl))) _).setNat
      (Or.inl rfl) _
  have dd0 : σ0.nat rD2 = d + 2 := by simp [hσ0, hσ1, hD, h1]
  have j0 : σ0.nat rJ = Bit.Sched.nBlk d - 1 := by simp [hσ0, n1, o1]
  refine XV.mono (XV.r1body hL hlay hX hB1 (by simp [hσ0, hσ1, hB]) (by simp [hσ0, hσ1, hD]) (by simp [hσ0, o1])
    dd0 j0 (by simp [hσ0, hσ1, hz]) (by simp [hσ0, hσ1, hdr]) hℓa hℓ (by unfold Bit.Sched.nBlk; omega) hda) le_rfl
    fun σ' ⟨hd', _, hz', F'⟩ => ⟨hz' hzn.symm, ?_, ?_⟩
  · rw [hd', hnb, blkStart_next]
  · refine F0.trans (F'.mono (fun y hy => ?_) (fun i hi => ?_) (fun a k hk => ?_))
    · rcases hy with h | h
      · exact Or.inl h.1
      · exact Or.inr h
    · rcases hi with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · obtain ⟨-, hk, hk'⟩ := hk
      rcases hk' with h | h <;> omega

/-! ## The units -/

theorem bmUnits_le (B : ℕ) : bmUnits B ≤ 300 * (gsm_prec B + 1) ^ 2 := by
  unfold bmUnits gsm_prec
  have hs : Nat.size B ≤ B := Nat.size_le.2 (Nat.lt_two_pow_self)
  have h2 : (B - 1) * (24 * (B + 2 * Nat.size B + 4) + 41) ≤ B * (24 * (B + 2 * Nat.size B + 4) + 41) :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  nlinarith

/-- `B ≥ 1` at `parO`. -/
theorem parO_B_pos (d n : ℕ) (δ : ℚ) : 1 ≤ (parO d n δ).B := by
  show 1 ≤ 2 * (_ + _ + 2)
  omega

/-- A block's facts from BL-O's invariant: `2 p_B ≤ E`. -/
theorem prec_le_E {R : RdO d} {σ : Env d} (hI : R.Inv σ) : 2 * gsm_prec R.pB ≤ R.E := by
  obtain ⟨-, -, -, -, c2g, -⟩ := hI.consts
  exact pow_two_le (hI.sc_abs (y := s2g) (by decide) (by rw [c2g]; push_cast; rfl))

/-- The room of BL's layout from a block's room. -/
theorem blLay_of {L : Layout} {nS nN nA : ℕ} (h : RoomO L nS nN nA) (hS : oE + 3 ≤ nS) (hN : rEE + 1 ≤ nN)
    (hA : aWE + 2 ≤ nA) : BLLay L :=
  ⟨hS.trans h.1, hN.trans h.2.1, hA.trans h.2.2⟩

/-- The constants of R1a and R1b. -/
def kR1 : BlkK := ⟨400, 3, 0, 0, oE + 3, rEE + 1, aWE + 2⟩

/-- `x ≤ x^3` and `x^2 ≤ x^3` for `x ≥ 1`. -/
theorem pow3_facts {x : ℕ} (hx : 1 ≤ x) : x ≤ x ^ 3 ∧ x ^ 2 ≤ x ^ 3 ∧ 1 ≤ x ^ 3 := by
  refine ⟨?_, Nat.pow_le_pow_right hx (by norm_num), Nat.one_le_pow _ _ hx⟩
  calc x = x ^ 1 := (pow_one x).symm
    _ ≤ x ^ 3 := Nat.pow_le_pow_right hx (by norm_num)

/-- The bit widths and the budget of R1a and R1b from a round's hypotheses. -/
theorem r1_widths {R : RdO d} {σ : Env d} (hH : R.Hyp kR1 (R.bud kR1)) (hI : R.Inv σ) :
    4 * gsm_prec R.pB + 2 < 2 ^ R.ℓa ∧ 4 * gsm_prec R.pB + 4 ≤ R.ℓ ∧ d + 2 < 2 ^ R.ℓa ∧
      r1aUnits d R.pB ≤ R.bud kR1 ∧ bmUnits R.pB + 18 ≤ R.bud kR1 := by
  have hg := prec_le_E hI
  have hdW : d ≤ R.W := by show d ≤ wU d R.n R.δ R.r0 R.R0 R.a; unfold wU; omega
  set x := R.W + R.E + 1 with hx
  have hx1 : 1 ≤ x := by omega
  obtain ⟨p1, p2, p3⟩ := pow3_facts hx1
  have hb : R.bud kR1 = 400 * x ^ 3 := rfl
  have hEx : R.E + 1 ≤ x := by omega
  have hgx : gsm_prec R.pB + 1 ≤ x := by omega
  have hbm : bmUnits R.pB ≤ 300 * x ^ 2 :=
    (bmUnits_le _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hgx 2))
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

theorem specR1a : SpecR1a (fun L => .base (xR1a L)) kR1 := by
  intro d R σ hH hI
  obtain ⟨w1, w2, w3, w4, -⟩ := r1_widths hH hI
  obtain ⟨r0, -, -, r3, -, -, r6, r7⟩ := hI.regs
  obtain ⟨c0, -⟩ := hI.consts
  refine XVO.mono (XVO.ofX (XV.r1a hH.lay (blLay_of hH.room le_rfl le_rfl le_rfl) (cs := R.w.cs) rfl
    (parO_B_pos _ _ _) r7 r0 r3 r6 c0 hI.draws w1 w2 w3)) w4 fun σ' ⟨hg, hd, F⟩ => ?_
  exact ⟨SamePers.ofFrame F (fun y h => by simp only [SR1a] at h; uomega) (fun j h => by simp only [NR1a] at h; uomega)
    (fun a k h => by simp only [AR1] at h; uomega), by rw [F.2.2.2.1, hI.rounds], hd, hg⟩

theorem specR1b : SpecR1b (fun L => .base (xR1b L)) kR1 := by
  intro d R σ0 σ hH hI hP hdr
  obtain ⟨w1, w2, w3, -, w5⟩ := r1_widths hH hI
  obtain ⟨r0, -, -, r3, -, -, r6, r7⟩ := hI.regs
  obtain ⟨c0, -⟩ := hI.consts
  have eN : ∀ j < 8, σ.nat j = σ0.nat j := hP.1
  refine XVO.mono (XVO.ofX (XV.r1b hH.lay (blLay_of hH.room le_rfl le_rfl le_rfl) (cs := R.w.cs) rfl
    (parO_B_pos _ _ _) (by rw [eN _ (by decide), r7]; rfl) (by rw [eN _ (by decide), r0]) (by rw [eN _ (by decide), r3])
    (by rw [eN _ (by decide), r6]) (by rw [hP.2.1 _ (by decide), c0]) hdr w1 w2 w3)) w5 fun σ' ⟨hz, hd, F⟩ => ?_
  refine ⟨hz, F.2.2.2.1, hd, (FrameC.ofA F).mono (fun y h => ?_) (fun j h => ?_) (fun _ _ h => h.elim)⟩
  · rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by simp only [oBM, tR] at h ⊢; omega)
  · simp only [NR1a, NScr] at h ⊢; uomega

theorem progR1a : ProgR1a := ⟨_, _, specR1a⟩

theorem progR1b : ProgR1b := ⟨_, _, specR1b⟩

end AdversarialBco.Unified.ProgO
