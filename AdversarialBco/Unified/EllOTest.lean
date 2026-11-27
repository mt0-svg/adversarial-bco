/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.EllOLoop

@[expose] public section

/-!
# UNI-ELL (c): step 2 of ELL-O on the oracle machine

The tests of one iteration of ELL-O (`ellTestO`, EllSpec.lean) as a command of the oracle language, `xtestO`: the ball
test of ELL-R (`xtestA`); the test point `(2^s; a)` into the array `tp` (`xtpt`) and the test block `TB`; on an
accept, the tests of ELL-R on the rowless problem (`xtest` with no row); on a reject, `Y₀ = 2^{E-s} a` into SEP's array
`ay0` (`xscale`), the SEP command `SC`, and its cut `G` (or `0` on a failure) into the cut array (`xcopy`, `xzero`).
The rule `XVO.testO` is stated for any test block and any SEP command meeting their contracts, through the function
`sepF` that the SEP command computes from the centre; `ellTestO` is `tfO` at `sepF = sepE (evO ..)` (`ellTestO_eq`).
-/

namespace AdversarialBco.Uni.EllO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## The test as a function of the SEP step -/

/-- `ellTestO` with the SEP step a function `sepF` of the centre. -/
def tfO (Ib : EllI d) (T : (Fin d → ℚ) → Bool) (s : ℕ) (sepF : (Fin d → ℤ) → Option ((Fin d → ℤ) × (Fin d → ℤ)))
    (a : Fin d → ℤ) (kept : Option ((Fin d → ℤ) × ℤ)) : Cut d :=
  if 2 ^ (2 * s) * Ib.R.num ^ 2 < (a ⬝ᵥ a) * (Ib.R.den : ℤ) ^ 2 then .cut a kept
  else if T (ptDN (2 ^ s) a) then ellTest Ib s a kept
  else
    match sepF a with
    | none => .cut 0 kept
    | some (_, G) => .cut G kept

/-- The SEP step of ELL-O at the scale `2^s`, as a function of the centre. -/
def sepO (I : EllOI d) (T : (Fin d → ℚ) → Bool) (s : ℕ) (a : Fin d → ℤ) :
    Option ((Fin d → ℤ) × (Fin d → ℤ)) :=
  sepE (I.evO T (I.sepEx s)) ((2 : ℤ) ^ (I.sepEx s - s) • a) (I.sepEx s) I.e1 I.eτ I.eL I.eu

theorem ellTestO_eq (I : EllOI d) (T : (Fin d → ℚ) → Bool) (s : ℕ) :
    ellTestO I T s = tfO I.base T s (sepO I T s) := rfl

/-! ## The pieces in the base language -/

/-- The test point `(2^s; a)` into the array `tp`: cell `0` from the slot `P + 3` (the index register `zr` holds `0`),
cells `1, ..., d` from the array `a0 + 1`. -/
def xtpt (L : Layout) (B : EllBlk) (P u a0 n0 tp zr : ℕ) : XCmd :=
  .seq (toX (VL.aset L tp zr (P + 3)))
  (.seq (.prim (.frag (.nconst (n0 + 1) 1)))
    (xmapE L u (u + 24) (.arr (a0 + 1) (n0 + 2)) tp (n0 + 1) (n0 + 4) (n0 + 2) B.rd (n0 + 4)))

/-- `dst := c a`, the factor `c` in the slot `cF`, `a` in the array `a0 + 1`. -/
def xscale (L : Layout) (B : EllBlk) (u a0 n0 cF dst : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst (n0 + 1) 0)))
    (xmapE L u (u + 24) (.op .mul (.sc cF) (.arr (a0 + 1) (n0 + 2))) dst (n0 + 1) (n0 + 4) (n0 + 2) B.rd (n0 + 4))

/-- `dst := 0` on the cells `0, ..., d - 1`. -/
def xzero (L : Layout) (B : EllBlk) (u n0 dst : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst (n0 + 1) 0)))
    (xmapE L u (u + 24) (.sc u) dst (n0 + 1) (n0 + 4) (n0 + 2) B.rd (n0 + 4))

set_option maxHeartbeats 2000000 in
/-- The rule of `xtpt`. -/
theorem XV.tpt {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk}
    {P u a0 n0 tp zr F s : ℕ} {a : Fin d → ℤ} (hd : 1 ≤ d) (hu : u + 27 ≤ L.NS) (hP : P + 3 < L.NS)
    (hsrc : a0 + 1 < L.NA) (htp : tp < L.NA) (hsd : a0 + 1 ≠ tp) (hn0 : n0 + 5 ≤ L.NN) (hrd : B.rd < L.NN)
    (hzr : zr < L.NN) (hrd0 : B.rd < n0 + 1 ∨ n0 + 5 ≤ B.rd) (hz : σ.sc u = 0) (hσd : σ.nat B.rd = d)
    (hσ1 : σ.nat (n0 + 4) = 1) (hσz : σ.nat zr = 0) (hp3 : σ.sc (P + 3) = ((2 ^ s : ℤ) : ℝ))
    (hx : ∀ k : Fin d, σ.arr (a0 + 1) k = a k) (bx : ∀ k, |a k| ≤ 2 ^ F) (hs : s < ℓ) (hF : F < ℓ) :
    XRunsB L X ℓa ℓ (xtpt L B P u a0 n0 tp zr) σ (2 + (1 + (d * (2 + 6) + 3))) (fun σ' =>
      σ'.arr tp 0 = ((2 ^ s : ℤ) : ℝ) ∧ (∀ k : Fin d, σ'.arr tp (1 + (k : ℕ)) = a k) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => u + 24 ≤ y) (fun j => j = n0 + 1 ∨ j = n0 + 2) (fun b c => b = tp ∧ c < d + 1) σ σ') := by
  have hda := asz_lt hL htp
  have hdl : d < 2 ^ ℓa := by unfold asz at hda; nlinarith
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  have hcd : ∀ k < d, 1 + 1 * k < asz d := fun k hk => by unfold asz; nlinarith
  have hd1l : d + 1 < 2 ^ ℓa := by unfold asz at hda; nlinarith
  have h2s : |(((2 ^ s : ℤ) : ℤ) : ℝ)| < 2 ^ ℓ := by
    rw [Int.cast_pow, Int.cast_ofNat, abs_of_pos (by positivity)]
    exact pow_lt_pow_right₀ (by norm_num) hs
  refine XV.seq (XV.aset hL (a := tp) (i := zr) (x := P + 3) htp hzr hP (by rw [hσz]; unfold asz; nlinarith)
    (by rw [hp3]; exact h2s)) fun σ0 e0 => ?_
  subst e0
  refine XV.seq (XV.nconst hL (i := n0 + 1) (by omega) 1 hsa) fun σ1 e1 => ?_
  subst e1
  refine XV.mono (XV.mapE (E := F) (N := d) (base := 1) (st := 1) (F := vext a) hL (z := u) (t := u + 24)
    (e := .arr (a0 + 1) (n0 + 2)) (aB := tp) (nr := n0 + 1) (nst := n0 + 4) (nk := n0 + 2) (nn := B.rd)
    (none := n0 + 4) (by simp only [IE.WF]; omega) (by omega) (by simp only [IE.scr]; omega) (by simpa using hz) htp
    (by omega) (by omega) (by omega) hrd (by omega)
    (nodup4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) (by omega) (by omega)
    (by simp; rw [if_neg (by omega), hσd]) (by simp [hσ1]) (by simp)
    (by simp [hσ1]) one_pos hcd (by omega) (by omega) hsa
    (by simp only [IE.top]; omega) ?_) le_rfl fun σ2 ⟨m2, r2, d2, F2⟩ => ?_
  · intro k hk σ' hF hd' hkt hkr
    have e : σ'.arr (a0 + 1) k = vext a k := by
      rw [hF.2.2.1 _ _ (fun h => hsd h.1), Env.setNat_arr, Env.setArr_arr, if_neg (fun h => hsd h.1),
        vext_lt _ hk]
      exact hx ⟨k, hk⟩
    exact ⟨⟨by rw [hkt]; unfold asz; nlinarith, vext a k, by rw [hkt, e], abs_vext_le bx (by positivity) k⟩,
      by simp only [IE.eval, hkt, e]⟩
  · refine ⟨?_, fun k => ?_, by rw [d2]; simp, ?_⟩
    · rw [F2.2.2.1 _ _ (fun h => by omega)]
      simp [hσz, hp3]
    · have := m2 k k.2
      simp only [one_mul] at this
      rw [this, vext_lt _ k.2]
    · refine ((((FrameA.refl _ _ _ σ).setArr ⟨rfl, ?_⟩ _).setNat (Or.inl rfl) 1).trans
        (F2.mono (fun _ h => h) (fun j h => by omega) (fun b c h => ⟨h.1, by omega⟩)))
      rw [hσz]; omega

set_option maxHeartbeats 2000000 in
/-- The rule of `xscale`. -/
theorem XV.scale {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk}
    {u a0 n0 cF dst F G : ℕ} {a : Fin d → ℤ} (hu : u + 29 ≤ L.NS) (hcF : cF < u + 24)
    (hsrc : a0 + 1 < L.NA) (hdst : dst < L.NA) (hsd : a0 + 1 ≠ dst) (hn0 : n0 + 5 ≤ L.NN) (hrd : B.rd < L.NN)
    (hrd0 : B.rd < n0 + 1 ∨ n0 + 5 ≤ B.rd) (hz : σ.sc u = 0) (hσd : σ.nat B.rd = d)
    (hσ1 : σ.nat (n0 + 4) = 1) (hc : σ.sc cF = ((2 ^ G : ℤ) : ℝ))
    (hx : ∀ k : Fin d, σ.arr (a0 + 1) k = a k) (bx : ∀ k, |a k| ≤ 2 ^ F) (hG : G ≤ F) (hF : F + F < ℓ) :
    XRunsB L X ℓa ℓ (xscale L B u a0 n0 cF dst) σ (1 + (d * (4 + 6) + 3)) (fun σ' =>
      (∀ k : Fin d, σ'.arr dst k = ((2 : ℤ) ^ G • a) k) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => u + 24 ≤ y) (fun j => j = n0 + 1 ∨ j = n0 + 2) (fun b c => b = dst ∧ c < d) σ σ') := by
  have hda := asz_lt hL hdst
  have hdl : d < 2 ^ ℓa := by unfold asz at hda; nlinarith
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  have hcd : ∀ k < d, 0 + 1 * k < asz d := fun k hk => by unfold asz; nlinarith
  refine XV.seq (XV.nconst hL (i := n0 + 1) (by omega) 0 (by positivity)) fun σ0 e0 => ?_
  subst e0
  refine XV.mono (XV.mapE (E := F) (N := d) (base := 0) (st := 1) (F := vext ((2 : ℤ) ^ G • a)) hL (z := u)
    (t := u + 24) (e := .op .mul (.sc cF) (.arr (a0 + 1) (n0 + 2))) (aB := dst) (nr := n0 + 1) (nst := n0 + 4)
    (nk := n0 + 2) (nn := B.rd) (none := n0 + 4)
    (by simp only [IE.WF]; exact ⟨(by intro h; cases h), hcF, by omega, by omega⟩) (by omega)
    (by simp only [IE.scr]; omega) (by simpa using hz) hdst (by omega) (by omega) (by omega) hrd (by omega)
    (nodup4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) (by omega) (by omega)
    (by simp; rw [if_neg (by omega), hσd]) (by simp [hσ1]) (by simp)
    (by simp [hσ1]) one_pos hcd hdl (by simpa using hdl) hsa
    (by simp only [IE.top, IE.mag]; omega) ?_) le_rfl fun σ1 ⟨m1, r1, d1, F1⟩ => ?_
  · intro k hk σ' hF hd' hkt hkr
    have e : σ'.arr (a0 + 1) k = a ⟨k, hk⟩ := by
      rw [hF.2.2.1 _ _ (fun h => hsd h.1), Env.setNat_arr]; exact hx ⟨k, hk⟩
    have ec : σ'.sc cF = ((2 ^ G : ℤ) : ℝ) := by rw [hF.2.1 _ (by omega)]; simpa using hc
    simp only [IE.Leaves, IE.eval, RealRAM.Op2.eval, hkt, e, ec]
    refine ⟨⟨⟨_, rfl, abs_pow_le hG⟩, by unfold asz; nlinarith, _, rfl, bx _⟩, ?_⟩
    rw [vext_lt _ hk]; simp [smul_eq_mul]
  · refine ⟨fun k => ?_, by rw [d1]; simp, ?_⟩
    · have := m1 k k.2
      simp only [zero_add, one_mul] at this
      rw [this, vext_lt _ k.2]
    · exact ((FrameA.refl _ _ _ σ).setNat (Or.inl rfl) 0).trans
        (F1.mono (fun _ h => h) (fun j h => by omega) (fun b c h => ⟨h.1, by simpa using h.2.2⟩))

set_option maxHeartbeats 2000000 in
/-- The rule of `xzero`. -/
theorem XV.zero {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk}
    {u n0 dst : ℕ} (hu : u + 27 ≤ L.NS) (hdst : dst < L.NA) (hn0 : n0 + 5 ≤ L.NN) (hrd : B.rd < L.NN)
    (hrd0 : B.rd < n0 + 1 ∨ n0 + 5 ≤ B.rd) (hz : σ.sc u = 0) (hσd : σ.nat B.rd = d)
    (hσ1 : σ.nat (n0 + 4) = 1) (hℓ : 1 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xzero L B u n0 dst) σ (1 + (d * (1 + 6) + 3)) (fun σ' =>
      (∀ k : Fin d, σ'.arr dst k = ((0 : Fin d → ℤ) k : ℝ)) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => u + 24 ≤ y) (fun j => j = n0 + 1 ∨ j = n0 + 2) (fun b c => b = dst ∧ c < d) σ σ') := by
  have hda := asz_lt hL hdst
  have hdl : d < 2 ^ ℓa := by unfold asz at hda; nlinarith
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  have hcd : ∀ k < d, 0 + 1 * k < asz d := fun k hk => by unfold asz; nlinarith
  refine XV.seq (XV.nconst hL (i := n0 + 1) (by omega) 0 (by positivity)) fun σ0 e0 => ?_
  subst e0
  refine XV.mono (XV.mapE (E := 0) (N := d) (base := 0) (st := 1) (F := fun _ => 0) hL (z := u)
    (t := u + 24) (e := .sc u) (aB := dst) (nr := n0 + 1) (nst := n0 + 4)
    (nk := n0 + 2) (nn := B.rd) (none := n0 + 4)
    (by simp only [IE.WF]; omega) (by omega) (by simp only [IE.scr]; omega) (by simpa using hz) hdst (by omega)
    (by omega) (by omega) hrd (by omega)
    (nodup4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) (by omega) (by omega)
    (by simp; rw [if_neg (by omega), hσd]) (by simp [hσ1]) (by simp)
    (by simp [hσ1]) one_pos hcd hdl (by simpa using hdl) hsa
    (by simp only [IE.top]; omega) ?_) le_rfl fun σ1 ⟨m1, r1, d1, F1⟩ => ?_
  · intro k hk σ' hF hd' hkt hkr
    have e : σ'.sc u = 0 := by rw [hF.2.1 _ (by omega)]; simpa using hz
    simp only [IE.Leaves, IE.eval, e]
    exact ⟨⟨0, by simp, by simp⟩, by simp⟩
  · refine ⟨fun k => ?_, by rw [d1]; simp, ?_⟩
    · have := m1 k k.2
      simp only [zero_add, one_mul] at this
      rw [this]; simp
    · exact ((FrameA.refl _ _ _ σ).setNat (Or.inl rfl) 0).trans
        (F1.mono (fun _ h => h) (fun j h => by omega) (fun b c h => ⟨h.1, by simpa using h.2.2⟩))

/-! ## Step 2 of ELL-O -/

/-- The tests of one iteration of ELL-O at the scale `2^s` (`P + 3` holds `2^s`): the ball test; the test point and
the test block `TB` (answer in the register `ans`, `zr` holds `0`); on an accept, ELL-R's tests without rows; on a
reject, `Y₀ = 2^{E-s} a` (the factor in the slot `cF`) into SEP's array, the SEP command `SC`, its cut or `0`. -/
def xtestO (L : Layout) (B : EllBlk) (TB SC : XCmdO) (sl : SepLay) (P u a0 n0 tp ans zr cF : ℕ) : XCmdO :=
  .seq (.base (xtestA L B P u a0 n0 (n0 + 4)))
  (xifSO L (u + 14) (u + 15)
    (.base (.seq (xcopy L B u (a0 + 1) (a0 + 2) n0 (n0 + 4)) (xset L P u u)))
    (.seq (.base (xtpt L B P u a0 n0 tp zr))
    (.seq TB
    (.ifN zr ans
      (.base (xtest L B .skip P u a0 (a0 + 6) n0 (n0 + 4) (n0 + 5)))
      (.seq (.base (xscale L B u a0 n0 cF sl.ay0))
      (.seq SC
      (.ifN zr sl.nok
        (.base (.seq (xcopy L B u sl.ag (a0 + 2) n0 (n0 + 4)) (xset L P u u)))
        (.base (.seq (xzero L B u n0 (a0 + 2)) (xset L P u u))))))))))

/-- The slots the step may change: ELL-R's tests, the test block's `St`, the SEP command's `SS`. -/
abbrev tsO (B : EllBlk) (P u : ℕ) (St SS : ℕ → Prop) (y : ℕ) : Prop :=
  (y = P ∨ y = P + 1 ∨ y = P + 2 ∨ y = P + 7 ∨ u + 13 ≤ y ∨ y = B.o + 2) ∨ St y ∨ SS y

/-- The registers the step may change. -/
abbrev tnO (B : EllBlk) (n0 ans : ℕ) (Nt SN : ℕ → Prop) (j : ℕ) : Prop :=
  (j = B.rE ∨ (n0 ≤ j ∧ j ≤ n0 + 2) ∨ j = n0 + 5 ∨ j = ans) ∨ Nt j ∨ SN j

/-- The array cells the step may change. -/
abbrev taO (B : EllBlk) (a0 tp ay0 : ℕ) (Art SA : ℕ → ℕ → Prop) (b k : ℕ) : Prop :=
  (b = B.aW + 1 ∨ b = a0 + 2 ∨ b = a0 + 3 ∨ b = a0 + 6 ∨ b = tp ∨ b = ay0) ∨ Art b k ∨ SA b k

/-- The cells the step changes before its last writes (it keeps the kept point and the centre). -/
abbrev s1O (u : ℕ) (St SS : ℕ → Prop) (y : ℕ) : Prop := u + 13 ≤ y ∨ St y ∨ SS y

abbrev n1O (n0 ans : ℕ) (Nt SN : ℕ → Prop) (j : ℕ) : Prop := (n0 ≤ j ∧ j ≤ n0 + 2) ∨ j = ans ∨ Nt j ∨ SN j

abbrev a1O (a0 tp ay0 : ℕ) (Art SA : ℕ → ℕ → Prop) (b k : ℕ) : Prop :=
  b = tp ∨ b = ay0 ∨ b = a0 + 2 ∨ Art b k ∨ SA b k

/-- The units of the step after the ball test, with a test block of `Kt` units and a SEP command of `Ks`. -/
def tORest (d Kt Ks : ℕ) : ℕ :=
  (2 + (1 + (d * (2 + 6) + 3))) + (Kt + ((testK d 0 0 + ((1 + (d * (4 + 6) + 3)) + (Ks +
    ((1 + (d * (2 + 6) + 3)) + 1 + 2)))) + 2))

/-- The units of the step. -/
def testOU (d Kt Ks : ℕ) : ℕ := tKA d + (tORest d Kt Ks + 2)

set_option maxHeartbeats 16000000 in
/-- **Step 2 of ELL-O on the oracle machine**: `xtestO` computes `tfO Ib T s sepF a kept` (TestOut), the centre `a`
in the array `a0 + 1`, for a test block `TB` answering `T` (`TestOK`) and a SEP command `SC` computing `sepF a` from
`Y₀ = 2^{E-s} a` (`SepOut`), whose cells lie below the bases of ELL-R's block, when the context `Cx` (which holds the
constants of the tests, `0` in `zr`, `2^{E-s}` in `cF` and the test block's data) survives the changes of the step. -/
theorem XVO.testO {L : Layout} {XO : XCtxO d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk}
    {Ib : EllI d} {nS nN nA s P u a0 n0 F G tp ans zr cF E Kt Ks bt : ℕ} {TB SC : XCmdO} {sl : SepLay}
    {T : (Fin d → ℚ) → Bool} {sepF : (Fin d → ℤ) → Option ((Fin d → ℤ) × (Fin d → ℤ))}
    {Cx Dat : Env d → Prop} {St Nt SS SN : ℕ → Prop} {Art SA : ℕ → ℕ → Prop}
    {a : Fin d → ℤ} {kept : Option ((Fin d → ℤ) × ℤ)}
    (hd : 1 ≤ d) (hB : B.OK L nS nN nA) (hm : Ib.m = 0)
    (lay : TestLay L B P u a0 (a0 + 6) n0 (n0 + 4) (n0 + 5))
    (htp : tp < L.NA) (htpa : tp < a0 ∨ a0 + 6 < tp) (hay0 : sl.ay0 < L.NA)
    (hay0a : sl.ay0 < a0 ∨ a0 + 6 < sl.ay0) (hag : sl.ag < L.NA) (hag2 : sl.ag ≠ a0 + 2) (hok : sl.nok < B.rE)
    (hans : ans < B.rE) (hzr : zr < B.rE) (hcF : cF < B.o)
    (hSt : ∀ y, St y → y < B.o) (hNt : ∀ j, Nt j → j < B.rE ∧ j ≠ zr)
    (hArt : ∀ b k, Art b k → b < a0 ∨ a0 + 6 < b)
    (hSS : ∀ y, SS y → y < B.o) (hSN : ∀ j, SN j → j < B.rE ∧ j ≠ zr)
    (hSA : ∀ b k, SA b k → b < a0 ∨ a0 + 6 < b)
    (hCT : ∀ σ', Cx σ' → TestEnv B Ib s P u (n0 + 4) σ' ∧ σ'.nat zr = 0 ∧
      σ'.sc cF = ((2 ^ (E - s) : ℤ) : ℝ) ∧ Dat σ')
    (henv : ∀ σa σb, Cx σa → σb.draws = σa.draws →
      FrameA (tsO B P u St SS) (tnO B n0 ans Nt SN) (taO B a0 tp sl.ay0 Art SA) σa σb → Cx σb)
    (hTB : TestOK L XO ℓa ℓ TB Dat tp ans bt T Kt St Nt Art)
    (hSC : ∀ σ', Cx σ' → (∀ i : Fin d, σ'.arr sl.ay0 i = ((2 : ℤ) ^ (E - s) • a) i) →
      XRunsBO L XO ℓa ℓ SC σ' Ks (fun σ'' => SepOut sl (sepF a) σ'' ∧ FrameA SS SN SA σ' σ'' ∧
        σ''.draws = σ'.draws))
    (bG : ∀ Y Gv, sepF a = some (Y, Gv) → ∀ k, |Gv k| ≤ 2 ^ G)
    (hC : Cx σ) (hK : KeptIn P (a0 + 6) kept σ) (bW : ∀ b W, kept = some (b, W) → |W| ≤ 2 ^ (6 * F + 1))
    (ha : ∀ k : Fin d, σ.arr (a0 + 1) k = a k) (ba : ∀ k, |a k| ≤ 2 ^ F) (hσF : ellSz Ib ≤ F)
    (hsF : 2 * s + 1 ≤ F) (hdF : d ≤ F) (hEs : E - s ≤ F) (hFb : F < bt) (hG : G < ℓ) (hℓ : 64 * F + 16 < ℓ) :
    XRunsBO L XO ℓa ℓ (xtestO L B TB SC sl P u a0 n0 tp ans zr cF) σ (testOU d Kt Ks) (fun σ' =>
      TestOut P a0 (a0 + 6) (tfO Ib T s sepF a kept) σ' ∧ σ'.draws = σ.draws ∧
      FrameA (tsO B P u St SS) (tnO B n0 ans Nt SN) (taO B a0 tp sl.ay0 Art SA) σ σ') := by
  have lay' := lay
  obtain ⟨oP, Pu, uS, wa, -, aA, rn, -, -, nNN⟩ := lay'
  have hB' := hB
  obtain ⟨hoS, hrN, haA, hrd, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hB'
  obtain ⟨hT0, -, -, -⟩ := hCT σ hC
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by simp only [abs_zero]; positivity
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  -- the frames
  have m1 : ∀ σa σb : Env d, FrameA (s1O u St SS) (n1O n0 ans Nt SN) (a1O a0 tp sl.ay0 Art SA) σa σb →
      FrameA (tsO B P u St SS) (tnO B n0 ans Nt SN) (taO B a0 tp sl.ay0 Art SA) σa σb := fun σa σb hF =>
    hF.mono (fun y h => by
      rcases h with h | h | h
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)) (fun j h => by
      rcases h with h | h | h | h
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)) (fun b k h => by
      rcases h with h | h | h | h | h
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h))
  have hK1 : ∀ σ', FrameA (s1O u St SS) (n1O n0 ans Nt SN) (a1O a0 tp sl.ay0 Art SA) σ σ' →
      KeptIn P (a0 + 6) kept σ' := fun σ' hF =>
    hK.frame (hF.2.1 _ (fun h => by
      rcases h with h | h | h
      · omega
      · have := hSt _ h; omega
      · have := hSS _ h; omega)) (hF.2.1 _ (fun h => by
      rcases h with h | h | h
      · omega
      · have := hSt _ h; omega
      · have := hSS _ h; omega)) (fun k => hF.2.2.1 _ _ (fun h => by
      rcases h with h | h | h | h | h
      · omega
      · omega
      · omega
      · have := hArt _ _ h; omega
      · have := hSA _ _ h; omega))
  have ha1 : ∀ σ', FrameA (s1O u St SS) (n1O n0 ans Nt SN) (a1O a0 tp sl.ay0 Art SA) σ σ' →
      ∀ k : Fin d, σ'.arr (a0 + 1) k = a k := fun σ' hF k => by
    rw [hF.2.2.1 _ _ (fun h => by
      rcases h with h | h | h | h | h
      · omega
      · omega
      · omega
      · have := hArt _ _ h; omega
      · have := hSA _ _ h; omega), ha]
  -- bounds
  obtain ⟨-, -, -, -, -, -, -, -, mRn, mRd, -, -, -, -⟩ := ellMx_le Ib
  have bRn : |Ib.R.num| ≤ 2 ^ F := (abs_le_sz mRn).trans (pow_le_pow_right₀ (by norm_num) hσF)
  have bRd : |(Ib.R.den : ℤ)| ≤ 2 ^ F := (abs_le_sz' mRd).trans (pow_le_pow_right₀ (by norm_num) hσF)
  -- the ball test
  refine XVO.seq (XVO.ofX (XV.testA (X := XO.X) hL hB lay hT0 ha ba hσF hsF hdF hℓ))
    fun σ1 ⟨t13, t14, t15, d1, F1⟩ => ?_
  have G1 : FrameA (s1O u St SS) (n1O n0 ans Nt SN) (a1O a0 tp sl.ay0 Art SA) σ σ1 :=
    F1.mono (fun y h => Or.inl h) (fun j h => Or.inl (by omega)) (fun _ _ h => h.elim)
  have hC1 : Cx σ1 := henv σ σ1 hC d1 (m1 σ σ1 G1)
  obtain ⟨⟨⟨e1, -⟩, z1, -, n1, p31, -, -, -⟩, zr1, -, -⟩ := hCT σ1 hC1
  have b14 : |2 ^ (2 * s) * Ib.R.num ^ 2| ≤ 2 ^ (F + (F + F)) :=
    abs_mul_le_pow (abs_pow_le (by omega)) (by rw [pow_two]; exact abs_mul_le_pow bRn bRn)
  have b15 : |(a ⬝ᵥ a) * (Ib.R.den : ℤ) ^ 2| ≤ 2 ^ (F + (F + F) + (F + F)) :=
    abs_mul_le_pow (abs_dot_le' hdF ba ba) (by rw [pow_two]; exact abs_mul_le_pow bRd bRd)
  have v14 : |σ1.sc (u + 14)| < 2 ^ ℓ := by rw [t14]; exact absR_lt b14 (by omega)
  have v15 : |σ1.sc (u + 15)| < 2 ^ ℓ := by rw [t15]; exact absR_lt b15 (by omega)
  by_cases c1 : 2 ^ (2 * s) * Ib.R.num ^ 2 < (a ⬝ᵥ a) * (Ib.R.den : ℤ) ^ 2
  · -- the ball: cut with `a`
    have hc : σ1.sc (u + 14) < σ1.sc (u + 15) := by rw [t14, t15]; exact_mod_cast c1
    refine XVO.mono (XVO.ifS_t hL (by omega) (by omega) v14 v15 hc (XVO.ofX (XV.seq (K₂ := 1)
      (XV.copy (E := F) (x := a) hL (B := B) (u := u) (src := a0 + 1) (dst := a0 + 2) (n0 := n0) (one := n0 + 4)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) z1 e1 n1 (ha1 σ1 G1) ba (by omega)) fun σ2 ⟨m2, d2, F2⟩ => ?_)))
      (by unfold tORest; omega) fun _ h => h
    have G2 : FrameA (s1O u St SS) (n1O n0 ans Nt SN) (a1O a0 tp sl.ay0 Art SA) σ σ2 :=
      G1.trans (F2.mono (fun y h => Or.inl (by omega)) (fun j h => Or.inl (by omega))
        (fun b c h => Or.inr (Or.inr (Or.inl h.1))))
    have z2 : σ2.sc u = 0 := by rw [F2.2.1 _ (by omega), z1]
    refine XV.mono (XV.sop2 hL (x := P) (a := u) (b := u) (by omega) (by omega) (by omega) .add
      (by intro h; cases h) (by rw [z2]; exact h0) (by rw [z2]; exact h0)
      (by simp only [RealRAM.Op2.eval, z2, add_zero]; exact h0)) le_rfl fun σ3 e3 => ?_
    subst e3
    have e : tfO Ib T s sepF a kept = .cut a kept := by unfold tfO; rw [if_pos c1]
    rw [e]
    refine ⟨⟨by simp [RealRAM.Op2.eval, z2], fun k => by simp only [Env.setSc_arr]; exact m2 k,
      (hK1 σ2 G2).frame (by simp) (by simp) (fun k => by simp)⟩, by simp [d2, d1],
      (m1 σ σ2 G2).setSc (Or.inl (Or.inl rfl)) _⟩
  · have hc : ¬ σ1.sc (u + 14) < σ1.sc (u + 15) := by rw [t14, t15]; exact_mod_cast c1
    refine XVO.mono (XVO.ifS_f hL (by omega) (by omega) v14 v15 hc ?_) le_rfl fun _ h => h
    unfold tORest
    -- the test point
    refine XVO.seq (XVO.ofX (XV.tpt (X := XO.X) (a := a) (s := s) (F := F) hL (B := B) (P := P) (u := u)
      (a0 := a0) (n0 := n0) (tp := tp) (zr := zr) hd (by omega) (by omega) (by omega) htp (by omega) (by omega)
      (by omega) (by omega) (by omega) z1 e1 n1 zr1 p31 (ha1 σ1 G1) ba (by omega) (by omega)))
      fun σ2 ⟨q0, q1, d2, F2⟩ => ?_
    have G2 : FrameA (s1O u St SS) (n1O n0 ans Nt SN) (a1O a0 tp sl.ay0 Art SA) σ σ2 :=
      G1.trans (F2.mono (fun y h => Or.inl (by omega)) (fun j h => Or.inl (by omega))
        (fun b c h => Or.inl h.1))
    have D2 : σ2.draws = σ.draws := d2.trans d1
    obtain ⟨-, -, -, hD2⟩ := hCT σ2 (henv σ σ2 hC D2 (m1 σ σ2 G2))
    -- the test block
    refine XVO.seq (hTB σ2 (2 ^ s) a hD2 (by positivity) (pow_lt_pow_right₀ (by norm_num) (by omega))
      (fun i => (ba i).trans_lt (pow_lt_pow_right₀ (by norm_num) hFb)) q0 q1) fun σ3 ⟨an3, F3, d3⟩ => ?_
    have G3 : FrameA (s1O u St SS) (n1O n0 ans Nt SN) (a1O a0 tp sl.ay0 Art SA) σ σ3 :=
      G2.trans (F3.mono (fun y h => Or.inr (Or.inl h)) (fun j h => Or.inr (Or.inr (Or.inl h)))
        (fun b k h => Or.inr (Or.inr (Or.inr (Or.inl h)))))
    have D3 : σ3.draws = σ.draws := d3.trans D2
    have hC3 : Cx σ3 := henv σ σ3 hC D3 (m1 σ σ3 G3)
    obtain ⟨hT3, zr3, cF3, -⟩ := hCT σ3 hC3
    have hT3' := hT3
    obtain ⟨⟨e3, -⟩, z3, -, n3, -, -, -, -⟩ := hT3'
    have va3 : σ3.nat ans < 2 ^ ℓa := by rw [an3]; split_ifs <;> omega
    by_cases hT : T (ptDN (2 ^ s) a) = true
    · -- an accept: ELL-R's tests without rows
      have hlt : σ3.nat zr < σ3.nat ans := by rw [zr3, an3, if_pos hT]; omega
      refine XVO.mono (XVO.ifN_t hL (by omega) (by omega) (by rw [zr3]; omega) va3 hlt
        (XVO.ofX (XV.test (X := XO.X) (rowc := .skip) (Ctx := fun _ => True) (SR := fun _ => False)
          (NR := fun _ => False) (AR := fun _ => False) (s := s) (a := a) (kept := kept) (F := F) (Kr := 0) hL hB
          ⟨id, id, id, id, id, id, id, id, id, id, id, id, id, id⟩
          ⟨fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim,
            fun _ _ h => absurd h (by rw [hm]; exact Nat.not_lt_zero _)⟩
          (fun _ _ _ _ _ => trivial) lay hT3 trivial (hK1 σ3 G3) bW (ha1 σ3 G3) ba hσF hsF hdF
          (by rw [hm]; positivity) hℓ)))
        (by rw [hm]; omega) fun σ4 ⟨o4, d4, F4⟩ => ?_
      have e : tfO Ib T s sepF a kept = ellTest Ib s a kept := by unfold tfO; rw [if_neg c1, if_pos hT]
      rw [e]
      refine ⟨o4, d4.trans D3, (m1 σ σ3 G3).trans (F4.mono (fun y h => Or.inl ?_) (fun j h => Or.inl ?_)
        (fun b k h => Or.inl ?_))⟩
      · rcases h with h | h | h | h | h | h | h
        all_goals first | omega | exact h.elim
      · rcases h with h | h | h | h
        all_goals first | omega | exact h.elim
      · rcases h with h | h | h | h | h
        all_goals first | omega | exact h.elim
    · -- a reject: the SEP cut
      have hge : ¬ σ3.nat zr < σ3.nat ans := by
        rw [zr3, an3, if_neg hT]; omega
      refine XVO.mono (K := (1 + (d * (4 + 6) + 3)) + (Ks + ((1 + (d * (2 + 6) + 3)) + 1 + 2)) + 2)
        (XVO.ifN_f hL (by omega) (by omega) (by rw [zr3]; omega) va3 hge ?_) (by omega)
        fun _ h => h
      refine XVO.seq (XVO.ofX (XV.scale (X := XO.X) hL (B := B) (u := u) (a0 := a0) (n0 := n0) (cF := cF)
        (dst := sl.ay0) (F := F) (G := E - s) (a := a) (by omega) (by omega) (by omega) hay0 (by omega) (by omega)
        (by omega) (by omega) z3 e3 n3 cF3 (ha1 σ3 G3) ba hEs (by omega))) fun σ4 ⟨y4, d4, F4⟩ => ?_
      have G4 : FrameA (s1O u St SS) (n1O n0 ans Nt SN) (a1O a0 tp sl.ay0 Art SA) σ σ4 :=
        G3.trans (F4.mono (fun y h => Or.inl (by omega)) (fun j h => Or.inl (by omega))
          (fun b c h => Or.inr (Or.inl h.1)))
      have D4 : σ4.draws = σ.draws := d4.trans D3
      refine XVO.seq (hSC σ4 (henv σ σ4 hC D4 (m1 σ σ4 G4)) y4) fun σ5 ⟨o5, F5, d5⟩ => ?_
      have G5 : FrameA (s1O u St SS) (n1O n0 ans Nt SN) (a1O a0 tp sl.ay0 Art SA) σ σ5 :=
        G4.trans (F5.mono (fun y h => Or.inr (Or.inr h)) (fun j h => Or.inr (Or.inr (Or.inr h)))
          (fun b k h => Or.inr (Or.inr (Or.inr (Or.inr h)))))
      have D5 : σ5.draws = σ.draws := d5.trans D4
      obtain ⟨hT5, zr5, -, -⟩ := hCT σ5 (henv σ σ5 hC D5 (m1 σ σ5 G5))
      obtain ⟨⟨e5, -⟩, z5, -, n5, -, -, -, -⟩ := hT5
      have ez : tfO Ib T s sepF a kept = match sepF a with
          | none => .cut 0 kept
          | some (_, Gv) => .cut Gv kept := by
        unfold tfO; rw [if_neg c1, if_neg hT]
      rw [ez]
      cases hs : sepF a with
      | none =>
        rw [hs] at o5
        have ok5 : σ5.nat sl.nok = 0 := o5
        refine XVO.mono (XVO.ifN_f hL (by omega) (by omega) (by rw [zr5]; omega) (by rw [ok5]; omega)
          (by rw [zr5, ok5]; omega) (XVO.ofX (XV.seq (K₂ := 1) (XV.zero hL (B := B) (u := u) (n0 := n0)
            (dst := a0 + 2) (by omega) (by omega) (by omega) (by omega) (by omega) z5 e5 n5 (by omega))
          fun σ6 ⟨m6, d6, F6⟩ => ?_))) (by omega) fun _ h => h
        have G6 : FrameA (s1O u St SS) (n1O n0 ans Nt SN) (a1O a0 tp sl.ay0 Art SA) σ σ6 :=
          G5.trans (F6.mono (fun y h => Or.inl (by omega)) (fun j h => Or.inl (by omega))
            (fun b c h => Or.inr (Or.inr (Or.inl h.1))))
        have z6 : σ6.sc u = 0 := by rw [F6.2.1 _ (by omega), z5]
        refine XV.mono (XV.sop2 hL (x := P) (a := u) (b := u) (by omega) (by omega) (by omega) .add
          (by intro h; cases h) (by rw [z6]; exact h0) (by rw [z6]; exact h0)
          (by simp only [RealRAM.Op2.eval, z6, add_zero]; exact h0)) le_rfl fun σ7 e7 => ?_
        subst e7
        refine ⟨⟨by simp [RealRAM.Op2.eval, z6], fun k => by simp only [Env.setSc_arr]; exact m6 k,
          (hK1 σ6 G6).frame (by simp) (by simp) (fun k => by simp)⟩, by simp [d6, D5],
          (m1 σ σ6 G6).setSc (Or.inl (Or.inl rfl)) _⟩
      | some p =>
        obtain ⟨Y, Gv⟩ := p
        rw [hs] at o5
        obtain ⟨ok5, hYG⟩ := o5
        have bGv := bG Y Gv hs
        refine XVO.mono (XVO.ifN_t hL (by omega) (by omega) (by rw [zr5]; omega) (by rw [ok5]; omega)
          (by rw [zr5, ok5]; omega) (XVO.ofX (XV.seq (K₂ := 1) (XV.copy (E := G) (x := Gv) hL (B := B) (u := u)
            (src := sl.ag) (dst := a0 + 2) (n0 := n0) (one := n0 + 4) (by omega) hag (by omega) hag2 (by omega)
            (by omega) (by omega) (by omega) (by omega) (by omega) z5 e5 n5 (fun k => (hYG k).2) bGv hG)
          fun σ6 ⟨m6, d6, F6⟩ => ?_))) (by omega) fun _ h => h
        have G6 : FrameA (s1O u St SS) (n1O n0 ans Nt SN) (a1O a0 tp sl.ay0 Art SA) σ σ6 :=
          G5.trans (F6.mono (fun y h => Or.inl (by omega)) (fun j h => Or.inl (by omega))
            (fun b c h => Or.inr (Or.inr (Or.inl h.1))))
        have z6 : σ6.sc u = 0 := by rw [F6.2.1 _ (by omega), z5]
        refine XV.mono (XV.sop2 hL (x := P) (a := u) (b := u) (by omega) (by omega) (by omega) .add
          (by intro h; cases h) (by rw [z6]; exact h0) (by rw [z6]; exact h0)
          (by simp only [RealRAM.Op2.eval, z6, add_zero]; exact h0)) le_rfl fun σ7 e7 => ?_
        subst e7
        refine ⟨⟨by simp [RealRAM.Op2.eval, z6], fun k => by simp only [Env.setSc_arr]; exact m6 k,
          (hK1 σ6 G6).frame (by simp) (by simp) (fun k => by simp)⟩, by simp [d6, D5],
          (m1 σ σ6 G6).setSc (Or.inl (Or.inl rfl)) _⟩

end AdversarialBco.Uni.EllO
