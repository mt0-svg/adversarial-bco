/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XEllJ
public import AdversarialBco.Bit.Transfer.XEllReg

@[expose] public section

/-!
# The start of ELL-R on the machine

From `d` and the registers of `XV.ellJ` and `XV.ellSetR`: `d`, `d²(d + 1)` and their logarithms (`XV.ellS0`); the
exponent, the scales of the tests and the constants of the update step in their slots (`XV.ellSlots`); the start
state `Â = 2^p R̄² I`, `â = 0`, no kept point (`XV.ellArr`).
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## Bounds -/

theorem ellJ_le {d : ℕ} (I : EllI d) (hd : 1 ≤ d) (hr : 0 < I.r) (he : 0 < I.e) :
    I.j ≤ 6 * ellSz I + d + 3 := by
  have hb := ellJ_bounds I hd hr he
  have hj := ellJ_eq I hr he
  dsimp only at hb hj
  rw [hj.2.2]
  exact clog_le_of_le hb.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem ellLam_le {d : ℕ} (I : EllI d) (hd : 1 ≤ d) (hr : 0 < I.r) (he : 0 < I.e) :
    I.lam ≤ 7 * ellSz I + d + 3 ∧ I.p ≤ 12 * ellSz I + 5 * d + 12 ∧ I.q ≤ 34 * ellSz I + 6 * d + 24 ∧
      Nat.clog 2 I.Rb ≤ ellSz I := by
  have h_clog_Rb : Nat.clog 2 I.Rb ≤ ellSz I := by
    have h_lt : I.Rb < 2 ^ ellSz I := ellRb_lt I
    have h_le : I.Rb ≤ 2 ^ ellSz I := Nat.le_of_lt h_lt
    rw [Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
    exact h_le
  have h_j : I.j ≤ 6 * ellSz I + d + 3 := ellJ_le I hd hr he
  have h_clog_d : Nat.clog 2 d ≤ d := clog_bounds.2.1 d
  have h_clog_d2 : Nat.clog 2 (d ^ 2 * (d + 1)) ≤ 3 * d := clog_bounds.2.2 d hd
  dsimp only [EllI.lam, EllI.p, EllI.q]
  omega

theorem kapN_le {d : ℕ} (hd : 1 ≤ d) : |kapN d| ≤ 2 ^ (3 * d + 2) := by
  have h1 : (d : ℤ) ≤ 2 ^ d := by exact_mod_cast Nat.lt_two_pow_self.le
  have h2 : 2 * (d : ℤ) + 1 ≤ 2 ^ (d + 1) := by
    have : (d : ℤ) + 1 ≤ 2 ^ d := by exact_mod_cast Nat.lt_two_pow_self
    rw [pow_succ]; linarith
  rw [kapN, abs_of_nonneg (by positivity), show 3 * d + 2 = d + 2 * (d + 1) by ring, pow_add, pow_mul']
  exact mul_le_mul h1 (pow_le_pow_left₀ (by positivity) h2 2) (by positivity) (by positivity)

theorem kapD_le {d : ℕ} (hd : 1 ≤ d) : |kapD d| ≤ 2 ^ (3 * d + 2) := by
  have h0 : (0 : ℤ) ≤ (d : ℤ) - 1 := by
    have : (1 : ℤ) ≤ d := by exact_mod_cast hd
    linarith
  have h1 : (d : ℤ) - 1 ≤ 2 ^ d := by
    have : (d : ℤ) ≤ 2 ^ d := by exact_mod_cast Nat.lt_two_pow_self.le
    linarith
  have h2 : (d : ℤ) + 1 ≤ 2 ^ d := by exact_mod_cast Nat.lt_two_pow_self
  rw [kapD, abs_of_nonneg (mul_nonneg (by positivity) h0), show 3 * d + 2 = 2 + d * 2 + d by ring, pow_add,
    pow_add, pow_mul, show (4 : ℤ) = 2 ^ 2 by norm_num]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2 2) (by positivity)) h1 h0
    (by positivity)

theorem small_lt {v : ℤ} {ℓ : ℕ} (hv : |v| ≤ 4) (hℓ : 3 ≤ ℓ) : |v| < 2 ^ ℓ :=
  calc |v| ≤ 4 := hv
    _ < 2 ^ 3 := by norm_num
    _ ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) hℓ

theorem two_pow_ge (d : ℕ) : (d : ℤ) + 1 ≤ 2 ^ d := by exact_mod_cast Nat.lt_two_pow_self

/-- A step adds its slot in front of the table when the change avoids the slots of the table. -/
theorem ScAre.cons' {σ σ' : Env d} {l : List (ℕ × ℝ)} {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop} {x : ℕ} {v : ℝ}
    (h : ScAre σ l) (hF : FrameA S N Ar σ σ') (hl : ∀ p ∈ l, ¬ S p.1) (hv : σ'.sc x = v) :
    ScAre σ' ((x, v) :: l) := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact hv
  · rw [hF.2.1 _ (hl p hp), h p hp]

/-- `xpow2` with the value as an integer, the count of draws and the frame as predicates. -/
theorem XV.pow2A {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {p i n one : ℕ}
    (hp : p < L.NS) (hi : i < L.NN) (hn : n < L.NN) (ho : one < L.NN) (hin : i ≠ n) (hio : i ≠ one)
    {W : ℕ} (hW : σ.nat n = W) (h1 : σ.nat one = 1) (hWa : W < 2 ^ ℓa) (hWl : W < ℓ) :
    XRunsB L X ℓa ℓ (xpow2 L p i n one) σ (4 * W + 4) (fun σ' => σ'.sc p = ((2 ^ W : ℤ) : ℝ) ∧
      σ'.draws = σ.draws ∧ FrameA (fun y => y = p) (fun j => j = i) (fun _ _ => False) σ σ') :=
  XV.mono (XV.pow2 hL hp hi hn ho hin hio hW h1 hWa hWl) le_rfl fun _ ⟨e, _, hF⟩ =>
    ⟨by rw [e]; push_cast; ring, hF.2.2.2.1, FrameA.ofList hF (by simp) (by simp)⟩


/-! ## Expressions of the constants -/

/-- A sum `x := a + b` by the code of `IE.op .add`, for integers below `2^E`. -/
theorem XV.addIE {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {z x a b t E : ℕ}
    {va vb : ℤ} (ha : a < t) (hb : b < t) (hz : z < t) (hx : x < t) (hS : t + 2 ≤ L.NS) (hz0 : σ.sc z = 0)
    (hva : σ.sc a = va) (hvb : σ.sc b = vb) (ba : |va| ≤ 2 ^ E) (bb : |vb| ≤ 2 ^ E) (hE : E + 1 < ℓ) :
    XRunsB L X ℓa ℓ ((IE.op .add (.sc a) (.sc b)).code L z x t) σ 3 (XV.ExprPost ℓ σ x t (va + vb)) :=
  XV.ieRun (E := E) hL (by simp only [IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega) hz hx
    (by simp only [IE.scr]; omega) hz0 (by simp only [IE.Leaves]; exact ⟨⟨va, hva, ba⟩, ⟨vb, hvb, bb⟩⟩)
    (by simp only [IE.top, IE.mag]; omega) (by simp only [IE.eval, RealRAM.Op2.eval, hva, hvb]; push_cast; ring)

/-- `κ_N = d (2d + 1)²` from `d` in the slot `y` and `1` in the slot `o`. -/
def ieKapN (y o : ℕ) : IE :=
  .op .mul (.op .mul (.sc y) (.op .add (.op .add (.sc y) (.sc y)) (.sc o)))
    (.op .add (.op .add (.sc y) (.sc y)) (.sc o))

/-- `κ_D = 4 (d + 1)² (d - 1)` from `d`, `1`, `4` in the slots `y`, `o`, `f`. -/
def ieKapD (y o f : ℕ) : IE :=
  .op .mul (.op .mul (.op .mul (.op .add (.sc y) (.sc o)) (.op .add (.sc y) (.sc o))) (.op .sub (.sc y) (.sc o)))
    (.sc f)

theorem XV.kapNI {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {z x y o t : ℕ}
    (hy : y < t) (ho : o < t) (hz : z < t) (hx : x < t) (hS : t + 12 ≤ L.NS) (hz0 : σ.sc z = 0)
    (hvy : σ.sc y = ((d : ℤ) : ℝ)) (hvo : σ.sc o = ((1 : ℤ) : ℝ)) (hℓ : 3 * d + 4 < ℓ) :
    XRunsB L X ℓa ℓ ((ieKapN y o).code L z x t) σ 13 (XV.ExprPost ℓ σ x t (kapN d)) := by
  have bd : |(d : ℤ)| ≤ 2 ^ d := by
    rw [abs_of_nonneg (by positivity)]; exact_mod_cast (Nat.lt_two_pow_self).le
  have b1 : |(1 : ℤ)| ≤ 2 ^ d := one_le_two_pow d
  exact XV.ieRun (E := d) hL (by simp only [ieKapN, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega)
    hz hx (by simp only [ieKapN, IE.scr]; omega) hz0
    (by simp only [ieKapN, IE.Leaves]; exact ⟨⟨⟨_, hvy, bd⟩, ⟨⟨⟨_, hvy, bd⟩, ⟨_, hvy, bd⟩⟩, ⟨_, hvo, b1⟩⟩⟩,
      ⟨⟨⟨_, hvy, bd⟩, ⟨_, hvy, bd⟩⟩, ⟨_, hvo, b1⟩⟩⟩)
    (by simp only [ieKapN, IE.top, IE.mag]; omega)
    (by simp only [ieKapN, IE.eval, RealRAM.Op2.eval, hvy, hvo, kapN]; push_cast; ring)

theorem XV.kapDI {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {z x y o f t : ℕ}
    (hy : y < t) (ho : o < t) (hf : f < t) (hz : z < t) (hx : x < t) (hS : t + 12 ≤ L.NS) (hz0 : σ.sc z = 0)
    (hvy : σ.sc y = ((d : ℤ) : ℝ)) (hvo : σ.sc o = ((1 : ℤ) : ℝ)) (hvf : σ.sc f = ((4 : ℤ) : ℝ))
    (hℓ : 4 * d + 12 < ℓ) :
    XRunsB L X ℓa ℓ ((ieKapD y o f).code L z x t) σ 13 (XV.ExprPost ℓ σ x t (kapD d)) := by
  have bd : |(d : ℤ)| ≤ 2 ^ (d + 2) := by
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have b1 : |(1 : ℤ)| ≤ 2 ^ (d + 2) := one_le_two_pow _
  have b4 : |(4 : ℤ)| ≤ 2 ^ (d + 2) := by
    rw [abs_of_pos (by norm_num)]
    calc (4 : ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (d + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  exact XV.ieRun (E := d + 2) hL
    (by simp only [ieKapD, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega)
    hz hx (by simp only [ieKapD, IE.scr]; omega) hz0
    (by simp only [ieKapD, IE.Leaves]; exact ⟨⟨⟨⟨⟨_, hvy, bd⟩, ⟨_, hvo, b1⟩⟩, ⟨⟨_, hvy, bd⟩, ⟨_, hvo, b1⟩⟩⟩,
      ⟨⟨_, hvy, bd⟩, ⟨_, hvo, b1⟩⟩⟩, ⟨_, hvf, b4⟩⟩)
    (by simp only [ieKapD, IE.top, IE.mag]; omega)
    (by simp only [ieKapD, IE.eval, RealRAM.Op2.eval, hvy, hvo, hvf, kapD]; push_cast; ring)
set_option maxHeartbeats 1000000 in
/-- The rule of `xmapE`: the cells `base + st k`, `k < N`, of the array `aB` get the values `F k`, and no other cell changes. -/
theorem XV.mapEx {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {z t aB nr nst nk nn none E N base st : ℕ} {e : IE} {F : ℕ → ℤ}
    (hw : e.WF L t) (hz : z < t) (hS : t + 1 + e.scr ≤ L.NS) (hz0 : σ.sc z = 0) (hB : aB < L.NA)
    (hnr : nr < L.NN) (hnst : nst < L.NN) (hnk : nk < L.NN) (hnn : nn < L.NN) (hno : none < L.NN)
    (hne : [nr, nk, nn, none].Nodup) (hsr : nst ≠ nr) (hsk : nst ≠ nk)
    (hσn : σ.nat nn = N) (hσ1 : σ.nat none = 1) (hσr : σ.nat nr = base) (hσs : σ.nat nst = st) (hst : 0 < st)
    (hcell : ∀ k < N, base + st * k < asz d) (hNa : N < 2 ^ ℓa) (hra : base + st * N < 2 ^ ℓa)
    (hsa : st < 2 ^ ℓa) (htop : e.top E < ℓ)
    (hF : ∀ k < N, ∀ σ' : Env d, FrameA (fun y => t ≤ y) (fun j => j = nk ∨ j = nr)
        (fun b c => b = aB ∧ ∃ k' < k, c = base + st * k') σ σ' → σ'.draws = σ.draws →
        σ'.nat nk = k → σ'.nat nr = base + st * k → e.Leaves E σ' ∧ e.eval σ' = F k) :
    XRunsB L X ℓa ℓ (xmapE L z t e aB nr nst nk nn none) σ (N * (e.units + 6) + 3) (fun σ' =>
      (∀ k < N, σ'.arr aB (base + st * k) = F k) ∧ σ'.nat nr = base + st * N ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => t ≤ y) (fun j => j = nk ∨ j = nr) (fun b c => b = aB ∧ ∃ k' < N, c = base + st * k')
        σ σ') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne
  obtain ⟨⟨rk, rn, ro⟩, ⟨kn, ko⟩, -⟩ := hne
  refine XV.mono (XV.forN hL hnk hnn hno kn ko N (e.units + (2 + 1)) hNa
    (fun k σ' => σ'.nat nr = base + st * k ∧ σ'.draws = σ.draws ∧
      (∀ k' < k, σ'.arr aB (base + st * k') = F k') ∧
      FrameA (fun y => t ≤ y) (fun j => j = nk ∨ j = nr) (fun b c => b = aB ∧ ∃ k' < k, c = base + st * k') σ σ')
    σ hσn hσ1 ⟨by simp [rk, hσr], rfl, fun k hk => absurd hk (Nat.not_lt_zero k),
      (FrameA.refl _ _ _ σ).setNat (Or.inl rfl) 0⟩ ?_) (by ring_nf; omega)
    fun σ' ⟨⟨hr, hd, hk, hF'⟩, _⟩ => ⟨hk, hr, hd, hF'⟩
  intro k hk σ' ⟨hr, hd, hkk, hF'⟩ hkt hkn hk1
  obtain ⟨hl, hv⟩ := hF k hk σ' hF' hd hkt hr
  have hst' : σ'.nat nst = st := by rw [hF'.1 nst (by omega), hσs]
  refine XV.seq (XV.ieRun (E := E) hL (x := t) (t := t + 1) (hw.mono (by omega)) (by omega) (by omega) hS
    (by rw [hF'.2.1 z (by omega), hz0]) hl htop hv) fun σ1 ⟨v1, b1, d1, P1⟩ => ?_
  have n1 : σ1.nat = σ'.nat := funext fun j => P1.1 j not_false
  have hkN : base + st * k < base + st * N := by
    have := Nat.mul_lt_mul_of_pos_left hk hst; omega
  refine XV.seq (XV.aset hL (a := aB) (i := nr) (x := t) hB hnr (by omega)
    (by rw [n1, hr]; exact hcell k hk) (by rw [v1]; exact XV.abs_int_lt b1)) fun σ2 e2 => ?_
  subst e2
  refine XV.mono (XV.nadd hL (i := nr) (a := nr) (b := nst) hnr hnr hnst
    (by simp only [Env.setArr_nat, n1, hr]; omega) (by simp only [Env.setArr_nat, n1, hst']; exact hsa)) le_rfl
    fun σ3 e3 => ?_
  subst e3
  refine ⟨by simp [Ne.symm rk, hkt, n1], by simp [Ne.symm rn, hkn, n1], by simp [Ne.symm ro, hk1, n1], ?_, ?_, ?_,
    ?_⟩
  · simp [rk, hr, hst', n1]; ring
  · simp [d1, hd]
  · intro k' hk'
    simp only [Env.setNat_arr, Env.setArr_arr, Env.setArr_nat, n1, hr, P1.2.2.1]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hlt | rfl
    · have : base + st * k' ≠ base + st * k := by
        have := Nat.mul_lt_mul_of_pos_left hlt hst; omega
      simp only [this, and_false, ite_false]; exact hkk k' hlt
    · simp only [and_self, ite_true, v1]
  · have hP : FrameA (fun y => t ≤ y) (fun j => j = nk ∨ j = nr)
        (fun b c => b = aB ∧ ∃ k' < k + 1, c = base + st * k') σ' σ1 :=
      FrameA.ofP (P1.mono (fun y hy => by omega) (fun _ h => h.elim))
    refine (((hF'.mono (fun _ h => h) (fun _ h => h)
      (fun b c h => ⟨h.1, h.2.imp fun k' hk' => ⟨Nat.lt_succ_of_lt hk'.1, hk'.2⟩⟩)).trans
      hP).setArr ⟨rfl, k, Nat.lt_succ_self k, by simp only [n1, hr]⟩ _ |>.setNat (Or.inr rfl) _).setNat (Or.inl rfl) _

/-! ## `d`, `d²(d + 1)` and their logarithms -/

/-- `d (d) (d + 1)` from `d` in the slot `y` and `1` in the slot `o`. -/
def ieD3 (y o : ℕ) : IE := .op .mul (.op .mul (.sc y) (.sc y)) (.op .add (.sc y) (.sc o))

/-- `d` into the slot `c + 13`, `d²(d + 1)` into `c + 21`, `lg(d²(d + 1))` into the register `n0 + 17` and `lg d`
into `n0 + 18`; `c + 12` is scratch. -/
def xellS0 (L : Layout) (B : EllBlk) (u c n0 : ℕ) : XCmd :=
  .seq (toX (VL.ncast L (c + 13) B.rd))
  (.seq ((ieD3 (c + 13) (u + 1)).code L u (c + 21) (c + 24))
  (.seq (xclogS L (c + 12) (c + 21) (n0 + 17) (n0 + 4))
    (xclogS L (c + 12) (c + 13) (n0 + 18) (n0 + 4))))

theorem d3_le (d : ℕ) : (d : ℤ) * d * ((d : ℤ) + 1) ≤ 2 ^ (3 * d) := by
  have h1 : (d : ℤ) ≤ 2 ^ d := by exact_mod_cast Nat.lt_two_pow_self.le
  have h2 := two_pow_ge d
  rw [show 3 * d = d + d + d by ring, pow_add, pow_add]
  exact mul_le_mul (mul_le_mul h1 h1 (by positivity) (by positivity)) h2 (by positivity) (by positivity)

theorem d3_toNat (d : ℕ) : ((d : ℤ) * d * ((d : ℤ) + 1)).toNat = d ^ 2 * (d + 1) := by
  rw [show (d : ℤ) * d * ((d : ℤ) + 1) = ((d ^ 2 * (d + 1) : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]

set_option maxHeartbeats 2000000 in
/-- The rule of `xellS0`. -/
theorem XV.ellS0 {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk} {u c n0 : ℕ}
    (hrd : B.rd < L.NN) (hc : u + 2 ≤ c) (hS : c + 60 ≤ L.NS) (hN : n0 + 19 ≤ L.NN) (hdv : σ.nat B.rd = d)
    (hz : σ.sc u = 0) (h1 : σ.sc (u + 1) = 1) (hone : σ.nat (n0 + 4) = 1) (hda : 3 * d < 2 ^ ℓa)
    (hℓ : 3 * d + 4 < ℓ) :
    XRunsB L X ℓa ℓ (xellS0 L B u c n0) σ (24 * d + 16) (fun σ' =>
      σ'.sc (c + 13) = ((d : ℤ) : ℝ) ∧ σ'.nat (n0 + 17) = Nat.clog 2 (d ^ 2 * (d + 1)) ∧
      σ'.nat (n0 + 18) = Nat.clog 2 d ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = c + 12 ∨ y = c + 13 ∨ c + 21 ≤ y) (fun j => j = n0 + 17 ∨ j = n0 + 18)
        (fun _ _ => False) σ σ') := by
  have bd : |(d : ℤ)| ≤ 2 ^ d := by
    rw [abs_of_nonneg (by positivity)]; exact_mod_cast Nat.lt_two_pow_self.le
  have b1 : |(1 : ℤ)| ≤ 2 ^ d := one_le_two_pow d
  refine XV.mono (K := 1 + (7 + ((4 * (3 * d) + 4) + (4 * (3 * d) + 4)))) ?_ (by omega) (fun _ h => h)
  refine XV.seq (XV.ncastA hL (x := c + 13) (i := B.rd) (v := d) (by omega) hrd hdv (by omega))
    fun σ1 ⟨v1, d1, G1⟩ => ?_
  have z1 : σ1.sc u = 0 := by rw [G1.2.1 _ (by omega), hz]
  have o1 : σ1.sc (u + 1) = ((1 : ℤ) : ℝ) := by rw [G1.2.1 _ (by omega), h1, Int.cast_one]
  refine XV.seq (XV.ieRun (E := d) (e := ieD3 (c + 13) (u + 1)) (v := (d : ℤ) * d * ((d : ℤ) + 1)) (ℓ := ℓ)
    (X := X) hL (z := u) (x := c + 21) (t := c + 24)
    (by simp only [ieD3, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega) (by omega) (by omega)
    (by simp only [ieD3, IE.scr]; omega) z1
    (by simp only [ieD3, IE.Leaves]; exact ⟨⟨⟨_, v1, bd⟩, ⟨_, v1, bd⟩⟩, ⟨_, v1, bd⟩, ⟨_, o1, b1⟩⟩)
    (by simp only [ieD3, IE.top, IE.mag]; omega)
    (by simp only [ieD3, IE.eval, RealRAM.Op2.eval, v1, o1]; push_cast; ring)) fun σ2 ⟨v2, _, d2, F2⟩ => ?_
  have n2 : σ2.nat (n0 + 4) = 1 := by rw [F2.1 _ id, G1.1 _ id, hone]
  refine XV.seq (XV.clogS hL (G := 3 * d) (w := c + 12) (x := c + 21) (c := n0 + 17) (one := n0 + 4) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) v2 (by positivity) (d3_le d) n2 (by omega) (by omega))
    fun σ3 ⟨n3, d3, F3⟩ => ?_
  have v3 : σ3.sc (c + 13) = ((d : ℤ) : ℝ) := by rw [F3.2.1 _ (by omega), F2.2.1 _ (by omega), v1]
  have n3' : σ3.nat (n0 + 4) = 1 := by rw [F3.1 _ (by omega), n2]
  refine XV.mono (XV.clogS hL (G := 3 * d) (w := c + 12) (x := c + 13) (c := n0 + 18) (one := n0 + 4) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) v3 (by positivity)
    ((show (d : ℤ) ≤ 2 ^ d by exact_mod_cast Nat.lt_two_pow_self.le).trans
      (pow_le_pow_right₀ (by norm_num) (by omega))) n3' (by omega) (by omega)) le_rfl fun σ4 ⟨n4, d4, F4⟩ => ?_
  refine ⟨by rw [F4.2.1 _ (by omega), v3], by rw [F4.1 _ (by omega), n3, d3_toNat],
    by rw [n4, Int.toNat_natCast], by rw [d4, d3, d2, d1], ?_⟩
  exact (((G1.mono (fun y h => by omega) (fun _ h => h.elim) (fun _ _ h => h)).trans
    ((FrameA.ofP F2).mono (fun y h => by omega) (fun _ h => h.elim) (fun _ _ h => h))).trans
    ((FrameA.ofP F3).mono (fun y h => by omega) (fun j h => by omega) (fun _ _ h => h))).trans
    ((FrameA.ofP F4).mono (fun y h => by omega) (fun j h => by omega) (fun _ _ h => h))

/-! ## The exponent, the scales and the constants of the update step -/

/-- The slot constants of ELL-R: the exponent `p` into `o + 1`; `2^p, 2^{p+1}, 2^{2p}, 2^{2p+1}` into `P + 3, ..., P + 6`;
the constants of the update step (`UpdEnv`) into `u + 2, ..., u + 12`; `2^p R̄²` into `c + 20`. The registers hold the
exponents (`XV.ellSetR`); `n0 + 46` is scratch, `c + 14, ...` too. -/
def xellSlots (L : Layout) (B : EllBlk) (P u c n0 : ℕ) : XCmd :=
  (.seq (toX (VL.ncast L (B.o + 1) (n0 + 22)))
  (.seq (xpow2 L (P + 3) (n0 + 46) (n0 + 22) (n0 + 4))
  (.seq (xpow2 L (P + 4) (n0 + 46) (n0 + 34) (n0 + 4))
  (.seq (xpow2 L (P + 5) (n0 + 46) (n0 + 35) (n0 + 4))
  (.seq (xpow2 L (P + 6) (n0 + 46) (n0 + 36) (n0 + 4))
  (.seq (xpow2 L (u + 4) (n0 + 46) (n0 + 38) (n0 + 4))
  (.seq (xpow2 L (u + 5) (n0 + 46) (n0 + 39) (n0 + 4))
  (.seq (xpow2 L (u + 6) (n0 + 46) (n0 + 22) (n0 + 4))
  (.seq (xpow2 L (u + 7) (n0 + 46) (n0 + 30) (n0 + 4))
  (.seq (xpow2 L (c + 14) (n0 + 46) (n0 + 45) (n0 + 4))
  (.seq (xpow2 L (c + 15) (n0 + 46) (n0 + 42) (n0 + 4))
  (.seq (toX (VL.sconst L (u + 2) ((2 : ℤ) : ℚ)))
  (.seq (toX (VL.sconst L (u + 3) ((4 : ℤ) : ℚ)))
  (.seq (toX (VL.ncast L (u + 8) (n0 + 14)))
  (.seq ((ieKapN (c + 13) (u + 1)).code L u (u + 9) (c + 24))
  (.seq ((ieKapD (c + 13) (u + 1) (u + 3)).code L u (u + 10) (c + 24))
  (.seq ((IE.op .mul (.sc (c)) (.sc (c))).code L u (c + 16) (c + 24))
  (.seq ((IE.op .mul (.sc (c + 16)) (.sc (c + 14))).code L u (c + 17) (c + 24))
  (.seq ((IE.op .mul (.sc (u + 6)) (.sc (c + 17))).code L u (u + 11) (c + 24))
  (.seq ((IE.op .mul (.sc (c)) (.sc (c + 15))).code L u (c + 18) (c + 24))
  (.seq ((IE.op .add (.sc (c)) (.sc (c + 18))).code L u (c + 19) (c + 24))
  (.seq ((IE.op .mul (.sc (u + 6)) (.sc (c + 19))).code L u (u + 12) (c + 24))
  ((IE.op .mul (.sc (u + 6)) (.sc (c + 16))).code L u (c + 20) (c + 24))))))))))))))))))))))))

set_option maxHeartbeats 16000000 in
/-- The rule of `xellSlots`. -/
theorem XV.ellSlots {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk}
    {P u c n0 p q j lam E : ℕ} {Rb : ℤ} (hP : B.o + 3 ≤ P) (hPu : P + 8 ≤ u) (hc : u + 13 ≤ c)
    (hS : c + 60 ≤ L.NS) (hN : n0 + 47 ≤ L.NN)
    (hz : σ.sc u = 0) (h1 : σ.sc (u + 1) = 1) (hR : σ.sc c = Rb) (hdc : σ.sc (c + 13) = ((d : ℤ) : ℝ))
    (r4 : σ.nat (n0 + 4) = 1) (r14 : σ.nat (n0 + 14) = d + 1) (r22 : σ.nat (n0 + 22) = p)
    (r30 : σ.nat (n0 + 30) = q) (r34 : σ.nat (n0 + 34) = p + 1) (r35 : σ.nat (n0 + 35) = 2 * p)
    (r36 : σ.nat (n0 + 36) = 2 * p + 1) (r38 : σ.nat (n0 + 38) = p - 2 * j) (r39 : σ.nat (n0 + 39) = 2 * q)
    (r42 : σ.nat (n0 + 42) = 3 * lam + 1) (r45 : σ.nat (n0 + 45) = 6 * lam + 2)
    (bR : |Rb| ≤ 2 ^ E) (bRR : |Rb * Rb| ≤ 2 ^ E) (b6 : |(2 : ℤ) ^ (6 * lam + 2)| ≤ 2 ^ E)
    (bLam : |Rb * Rb * 2 ^ (6 * lam + 2)| ≤ 2 ^ E) (bp : |(2 : ℤ) ^ p| ≤ 2 ^ E)
    (b3 : |(2 : ℤ) ^ (3 * lam + 1)| ≤ 2 ^ E) (bLH : |Rb * 2 ^ (3 * lam + 1)| ≤ 2 ^ E)
    (bRL : |Rb + Rb * 2 ^ (3 * lam + 1)| ≤ 2 ^ E)
    (hpa : 2 * q + 2 * p + 6 * lam + d + 3 < 2 ^ ℓa) (hpl : 2 * q + 2 * p + 6 * lam + 3 < ℓ)
    (hE : 2 * E + 1 < ℓ) (hdl : 4 * d + 12 < ℓ) :
    XRunsB L X ℓa ℓ (xellSlots L B P u c n0) σ (32 * p + 12 * q + 36 * lam + 111) (fun σ' =>
      σ'.sc (B.o + 1) = ((p : ℤ) : ℝ) ∧
      σ'.sc (P + 3) = ((2 ^ p : ℤ) : ℝ) ∧ σ'.sc (P + 4) = ((2 ^ (p + 1) : ℤ) : ℝ) ∧
      σ'.sc (P + 5) = ((2 ^ (2 * p) : ℤ) : ℝ) ∧ σ'.sc (P + 6) = ((2 ^ (2 * p + 1) : ℤ) : ℝ) ∧
      UpdEnv u p q j (2 ^ p * (Rb * Rb * 2 ^ (6 * lam + 2))) (2 ^ p * (Rb + Rb * 2 ^ (3 * lam + 1))) σ' ∧
      σ'.sc (c + 20) = ((2 ^ p * (Rb * Rb) : ℤ) : ℝ) ∧ σ'.sc u = 0 ∧ σ'.sc (u + 1) = 1 ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = B.o + 1 ∨ (P + 3 ≤ y ∧ y ≤ P + 6) ∨ (u + 2 ≤ y ∧ y ≤ u + 12) ∨ c + 14 ≤ y)
        (fun i => i = n0 + 46) (fun _ _ => False) σ σ') := by
  have R0 : RegsAre σ [(n0 + 4, 1), (n0 + 14, d + 1), (n0 + 22, p), (n0 + 30, q), (n0 + 34, p + 1),
      (n0 + 35, 2 * p), (n0 + 36, 2 * p + 1), (n0 + 38, p - 2 * j), (n0 + 39, 2 * q), (n0 + 42, 3 * lam + 1),
      (n0 + 45, 6 * lam + 2)] := fun x hx => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have S0 : ScAre σ [(u, (0 : ℝ)), (u + 1, 1), (c, (Rb : ℝ)), (c + 13, ((d : ℤ) : ℝ))] := fun x hx => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have H0 := FrameA.refl (fun y => y = B.o + 1 ∨ (P + 3 ≤ y ∧ y ≤ P + 6) ∨ (u + 2 ≤ y ∧ y ≤ u + 12) ∨ c + 14 ≤ y)
    (fun i => i = n0 + 46) (fun _ _ => False) σ
  refine XV.mono (K :=
1 + ((4 * (p) + 4) + ((4 * (p + 1) + 4) + ((4 * (2 * p) + 4) + ((4 * (2 * p + 1) + 4) + ((4 * (p - 2 * j) + 4) + ((4 * (2 * q) + 4) + ((4 * (p) + 4) + ((4 * (q) + 4) + ((4 * (6 * lam + 2) + 4) + ((4 * (3 * lam + 1) + 4) + (1 + (1 + (1 + (13 + (13 + (3 + (3 + (3 + (3 + (3 + (3 + (3))))))))))))))))))))))
    ) ?_ (by omega) (fun _ h => h)
  refine XV.seq (XV.ncastA hL (x := B.o + 1) (i := n0 + 22) (v := p) (by omega) (by omega) (R0.get (by simp))
    (by omega)) fun σ1 ⟨v1, d1, G1⟩ => ?_
  have R1 := R0.frame G1 (by simp <;> omega)
  have S1 := S0.cons' G1 (by simp <;> omega) v1
  have H1 := H0.trans (G1.mono (fun y h => by omega) (fun j h => by first | omega | exact h.elim) (fun _ _ h => h))
  refine XV.seq (XV.pow2A hL (p := P + 3) (i := n0 + 46) (n := n0 + 22) (one := n0 + 4) (W := p) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (R1.get (by simp)) (R1.get (by simp))
    (by omega) (by omega)) fun σ2 ⟨v2, d2, G2⟩ => ?_
  have R2 := R1.frame G2 (by simp <;> omega)
  have S2 := S1.cons' G2 (by simp <;> omega) v2
  have H2 := H1.trans (G2.mono (fun y h => by omega) (fun j h => by first | omega | exact h.elim) (fun _ _ h => h))
  refine XV.seq (XV.pow2A hL (p := P + 4) (i := n0 + 46) (n := n0 + 34) (one := n0 + 4) (W := p + 1) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (R2.get (by simp)) (R2.get (by simp))
    (by omega) (by omega)) fun σ3 ⟨v3, d3, G3⟩ => ?_
  have R3 := R2.frame G3 (by simp <;> omega)
  have S3 := S2.cons' G3 (by simp <;> omega) v3
  have H3 := H2.trans (G3.mono (fun y h => by omega) (fun j h => by first | omega | exact h.elim) (fun _ _ h => h))
  refine XV.seq (XV.pow2A hL (p := P + 5) (i := n0 + 46) (n := n0 + 35) (one := n0 + 4) (W := 2 * p) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (R3.get (by simp)) (R3.get (by simp))
    (by omega) (by omega)) fun σ4 ⟨v4, d4, G4⟩ => ?_
  have R4 := R3.frame G4 (by simp <;> omega)
  have S4 := S3.cons' G4 (by simp <;> omega) v4
  have H4 := H3.trans (G4.mono (fun y h => by omega) (fun j h => by first | omega | exact h.elim) (fun _ _ h => h))
  refine XV.seq (XV.pow2A hL (p := P + 6) (i := n0 + 46) (n := n0 + 36) (one := n0 + 4) (W := 2 * p + 1) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (R4.get (by simp)) (R4.get (by simp))
    (by omega) (by omega)) fun σ5 ⟨v5, d5, G5⟩ => ?_
  have R5 := R4.frame G5 (by simp <;> omega)
  have S5 := S4.cons' G5 (by simp <;> omega) v5
  have H5 := H4.trans (G5.mono (fun y h => by omega) (fun j h => by first | omega | exact h.elim) (fun _ _ h => h))
  refine XV.seq (XV.pow2A hL (p := u + 4) (i := n0 + 46) (n := n0 + 38) (one := n0 + 4) (W := p - 2 * j) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (R5.get (by simp)) (R5.get (by simp))
    (by omega) (by omega)) fun σ6 ⟨v6, d6, G6⟩ => ?_
  have R6 := R5.frame G6 (by simp <;> omega)
  have S6 := S5.cons' G6 (by simp <;> omega) v6
  have H6 := H5.trans (G6.mono (fun y h => by omega) (fun j h => by first | omega | exact h.elim) (fun _ _ h => h))
  refine XV.seq (XV.pow2A hL (p := u + 5) (i := n0 + 46) (n := n0 + 39) (one := n0 + 4) (W := 2 * q) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (R6.get (by simp)) (R6.get (by simp))
    (by omega) (by omega)) fun σ7 ⟨v7, d7, G7⟩ => ?_
  have R7 := R6.frame G7 (by simp <;> omega)
  have S7 := S6.cons' G7 (by simp <;> omega) v7
  have H7 := H6.trans (G7.mono (fun y h => by omega) (fun j h => by first | omega | exact h.elim) (fun _ _ h => h))
  refine XV.seq (XV.pow2A hL (p := u + 6) (i := n0 + 46) (n := n0 + 22) (one := n0 + 4) (W := p) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (R7.get (by simp)) (R7.get (by simp))
    (by omega) (by omega)) fun σ8 ⟨v8, d8, G8⟩ => ?_
  have R8 := R7.frame G8 (by simp <;> omega)
  have S8 := S7.cons' G8 (by simp <;> omega) v8
  have H8 := H7.trans (G8.mono (fun y h => by omega) (fun j h => by first | omega | exact h.elim) (fun _ _ h => h))
  refine XV.seq (XV.pow2A hL (p := u + 7) (i := n0 + 46) (n := n0 + 30) (one := n0 + 4) (W := q) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (R8.get (by simp)) (R8.get (by simp))
    (by omega) (by omega)) fun σ9 ⟨v9, d9, G9⟩ => ?_
  have R9 := R8.frame G9 (by simp <;> omega)
  have S9 := S8.cons' G9 (by simp <;> omega) v9
  have H9 := H8.trans (G9.mono (fun y h => by omega) (fun j h => by first | omega | exact h.elim) (fun _ _ h => h))
  refine XV.seq (XV.pow2A hL (p := c + 14) (i := n0 + 46) (n := n0 + 45) (one := n0 + 4) (W := 6 * lam + 2) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (R9.get (by simp)) (R9.get (by simp))
    (by omega) (by omega)) fun σ10 ⟨v10, d10, G10⟩ => ?_
  have R10 := R9.frame G10 (by simp <;> omega)
  have S10 := S9.cons' G10 (by simp <;> omega) v10
  have H10 := H9.trans (G10.mono (fun y h => by omega) (fun j h => by first | omega | exact h.elim) (fun _ _ h => h))
  refine XV.seq (XV.pow2A hL (p := c + 15) (i := n0 + 46) (n := n0 + 42) (one := n0 + 4) (W := 3 * lam + 1) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (R10.get (by simp)) (R10.get (by simp))
    (by omega) (by omega)) fun σ11 ⟨v11, d11, G11⟩ => ?_
  have R11 := R10.frame G11 (by simp <;> omega)
  have S11 := S10.cons' G11 (by simp <;> omega) v11
  have H11 := H10.trans (G11.mono (fun y h => by omega) (fun j h => by first | omega | exact h.elim) (fun _ _ h => h))
  refine XV.seq (XV.sconstA hL (x := u + 2) (by omega) 2 (small_lt (by norm_num) (by omega)))
    fun σ12 ⟨v12, d12, G12⟩ => ?_
  have R12 := R11.frame G12 (by simp <;> omega)
  have S12 := S11.cons' G12 (by simp <;> omega) v12
  have H12 := H11.trans (G12.mono (fun y h => by omega) (fun j h => by first | omega | exact h.elim) (fun _ _ h => h))
  refine XV.seq (XV.sconstA hL (x := u + 3) (by omega) 4 (small_lt (by norm_num) (by omega)))
    fun σ13 ⟨v13, d13, G13⟩ => ?_
  have R13 := R12.frame G13 (by simp <;> omega)
  have S13 := S12.cons' G13 (by simp <;> omega) v13
  have H13 := H12.trans (G13.mono (fun y h => by omega) (fun j h => by first | omega | exact h.elim) (fun _ _ h => h))
  refine XV.seq (XV.ncastA hL (x := u + 8) (i := n0 + 14) (v := d + 1) (by omega) (by omega) (R13.get (by simp))
    (by omega)) fun σ14 ⟨v14, d14, G14⟩ => ?_
  have R14 := R13.frame G14 (by simp <;> omega)
  have S14 := S13.cons' G14 (by simp <;> omega) v14
  have H14 := H13.trans (G14.mono (fun y h => by omega) (fun j h => by first | omega | exact h.elim) (fun _ _ h => h))
  refine XV.seq (XV.kapNI hL (z := u) (x := u + 9) (y := c + 13) (o := u + 1) (t := c + 24) (by omega) (by omega)
    (by omega) (by omega) (by omega) (S14.get (by simp)) (S14.get (by simp)) (S14.get (by simp))
    (by omega)) fun σ15 ⟨v15, _, d15, G15⟩ => ?_
  have K15 : FrameA (fun y => y = u + 9 ∨ c + 24 ≤ y) (fun _ => False) (fun _ _ => False) σ14 σ15 :=
    FrameA.ofP G15
  have R15 := R14.frame K15 (by simp)
  have S15 := S14.cons' K15 (by simp <;> omega) v15
  have H15 := H14.trans (K15.mono (fun y h => by omega) (fun _ h => h.elim) (fun _ _ h => h))
  refine XV.seq (XV.kapDI hL (z := u) (x := u + 10) (y := c + 13) (o := u + 1) (f := u + 3) (t := c + 24) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (S15.get (by simp)) (S15.get (by simp))
    (S15.get (by simp)) (S15.get (by simp)) (by omega)) fun σ16 ⟨v16, _, d16, G16⟩ => ?_
  have K16 : FrameA (fun y => y = u + 10 ∨ c + 24 ≤ y) (fun _ => False) (fun _ _ => False) σ15 σ16 :=
    FrameA.ofP G16
  have R16 := R15.frame K16 (by simp)
  have S16 := S15.cons' K16 (by simp <;> omega) v16
  have H16 := H15.trans (K16.mono (fun y h => by omega) (fun _ h => h.elim) (fun _ _ h => h))
  refine XV.seq (XV.mulIE (E := E) (ℓ := ℓ) (X := X) hL (z := u) (x := c + 16) (t := c + 24) (a := c) (b := c) (va := Rb)
    (vb := Rb) (by omega) (by omega) (by omega) (by omega) (by omega) (S16.get (by simp))
    (S16.get (by simp)) (S16.get (by simp)) bR bR (by omega)) fun σ17 ⟨v17, _, d17, G17⟩ => ?_
  have K17 : FrameA (fun y => y = c + 16 ∨ c + 24 ≤ y) (fun _ => False) (fun _ _ => False) σ16 σ17 :=
    FrameA.ofP G17
  have R17 := R16.frame K17 (by simp)
  have S17 := S16.cons' K17 (by simp <;> omega) v17
  have H17 := H16.trans (K17.mono (fun y h => by omega) (fun _ h => h.elim) (fun _ _ h => h))
  refine XV.seq (XV.mulIE (E := E) (ℓ := ℓ) (X := X) hL (z := u) (x := c + 17) (t := c + 24) (a := c + 16) (b := c + 14) (va := Rb * Rb)
    (vb := 2 ^ (6 * lam + 2)) (by omega) (by omega) (by omega) (by omega) (by omega) (S17.get (by simp))
    (S17.get (by simp)) (S17.get (by simp)) bRR b6 (by omega)) fun σ18 ⟨v18, _, d18, G18⟩ => ?_
  have K18 : FrameA (fun y => y = c + 17 ∨ c + 24 ≤ y) (fun _ => False) (fun _ _ => False) σ17 σ18 :=
    FrameA.ofP G18
  have R18 := R17.frame K18 (by simp)
  have S18 := S17.cons' K18 (by simp <;> omega) v18
  have H18 := H17.trans (K18.mono (fun y h => by omega) (fun _ h => h.elim) (fun _ _ h => h))
  refine XV.seq (XV.mulIE (E := E) (ℓ := ℓ) (X := X) hL (z := u) (x := u + 11) (t := c + 24) (a := u + 6) (b := c + 17) (va := 2 ^ p)
    (vb := Rb * Rb * 2 ^ (6 * lam + 2)) (by omega) (by omega) (by omega) (by omega) (by omega) (S18.get (by simp))
    (S18.get (by simp)) (S18.get (by simp)) bp bLam (by omega)) fun σ19 ⟨v19, _, d19, G19⟩ => ?_
  have K19 : FrameA (fun y => y = u + 11 ∨ c + 24 ≤ y) (fun _ => False) (fun _ _ => False) σ18 σ19 :=
    FrameA.ofP G19
  have R19 := R18.frame K19 (by simp)
  have S19 := S18.cons' K19 (by simp <;> omega) v19
  have H19 := H18.trans (K19.mono (fun y h => by omega) (fun _ h => h.elim) (fun _ _ h => h))
  refine XV.seq (XV.mulIE (E := E) (ℓ := ℓ) (X := X) hL (z := u) (x := c + 18) (t := c + 24) (a := c) (b := c + 15) (va := Rb)
    (vb := 2 ^ (3 * lam + 1)) (by omega) (by omega) (by omega) (by omega) (by omega) (S19.get (by simp))
    (S19.get (by simp)) (S19.get (by simp)) bR b3 (by omega)) fun σ20 ⟨v20, _, d20, G20⟩ => ?_
  have K20 : FrameA (fun y => y = c + 18 ∨ c + 24 ≤ y) (fun _ => False) (fun _ _ => False) σ19 σ20 :=
    FrameA.ofP G20
  have R20 := R19.frame K20 (by simp)
  have S20 := S19.cons' K20 (by simp <;> omega) v20
  have H20 := H19.trans (K20.mono (fun y h => by omega) (fun _ h => h.elim) (fun _ _ h => h))
  refine XV.seq (XV.addIE (E := E) (ℓ := ℓ) (X := X) hL (z := u) (x := c + 19) (t := c + 24) (a := c) (b := c + 18) (va := Rb)
    (vb := Rb * 2 ^ (3 * lam + 1)) (by omega) (by omega) (by omega) (by omega) (by omega) (S20.get (by simp))
    (S20.get (by simp)) (S20.get (by simp)) bR bLH (by omega)) fun σ21 ⟨v21, _, d21, G21⟩ => ?_
  have K21 : FrameA (fun y => y = c + 19 ∨ c + 24 ≤ y) (fun _ => False) (fun _ _ => False) σ20 σ21 :=
    FrameA.ofP G21
  have R21 := R20.frame K21 (by simp)
  have S21 := S20.cons' K21 (by simp <;> omega) v21
  have H21 := H20.trans (K21.mono (fun y h => by omega) (fun _ h => h.elim) (fun _ _ h => h))
  refine XV.seq (XV.mulIE (E := E) (ℓ := ℓ) (X := X) hL (z := u) (x := u + 12) (t := c + 24) (a := u + 6) (b := c + 19) (va := 2 ^ p)
    (vb := Rb + Rb * 2 ^ (3 * lam + 1)) (by omega) (by omega) (by omega) (by omega) (by omega) (S21.get (by simp))
    (S21.get (by simp)) (S21.get (by simp)) bp bRL (by omega)) fun σ22 ⟨v22, _, d22, G22⟩ => ?_
  have K22 : FrameA (fun y => y = u + 12 ∨ c + 24 ≤ y) (fun _ => False) (fun _ _ => False) σ21 σ22 :=
    FrameA.ofP G22
  have R22 := R21.frame K22 (by simp)
  have S22 := S21.cons' K22 (by simp <;> omega) v22
  have H22 := H21.trans (K22.mono (fun y h => by omega) (fun _ h => h.elim) (fun _ _ h => h))
  refine XV.mono (XV.mulIE (E := E) (ℓ := ℓ) (X := X) hL (z := u) (x := c + 20) (t := c + 24) (a := u + 6) (b := c + 16) (va := 2 ^ p)
    (vb := Rb * Rb) (by omega) (by omega) (by omega) (by omega) (by omega) (S22.get (by simp))
    (S22.get (by simp)) (S22.get (by simp)) bp bRR (by omega)) le_rfl fun σ23 ⟨v23, _, d23, G23⟩ => ?_
  have K23 : FrameA (fun y => y = c + 20 ∨ c + 24 ≤ y) (fun _ => False) (fun _ _ => False) σ22 σ23 :=
    FrameA.ofP G23
  have R23 := R22.frame K23 (by simp)
  have S23 := S22.cons' K23 (by simp <;> omega) v23
  have H23 := H22.trans (K23.mono (fun y h => by omega) (fun _ h => h.elim) (fun _ _ h => h))
  refine ⟨S23.get (by simp), S23.get (by simp), S23.get (by simp), S23.get (by simp), S23.get (by simp),
    ⟨S23.get (by simp), S23.get (by simp), S23.get (by simp), S23.get (by simp), S23.get (by simp),
      S23.get (by simp), S23.get (by simp), S23.get (by simp), S23.get (by simp), S23.get (by simp),
      S23.get (by simp)⟩, S23.get (by simp), S23.get (by simp), S23.get (by simp), ?_, H23⟩
  rw [d23, d22, d21, d20, d19, d18, d17, d16, d15, d14, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]

/-! ## The start state -/

/-- `x := 0` from a slot `z` holding `0`. -/
theorem XV.setZ {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {x z : ℕ} (hx : x < L.NS)
    (hz : z < L.NS) (hz0 : σ.sc z = 0) :
    XRunsB L X ℓa ℓ (xset L x z z) σ 1 (fun σ' => σ'.sc x = 0 ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = x) (fun _ => False) (fun _ _ => False) σ σ') := by
  have h0 : |σ.sc z| < 2 ^ ℓ := by rw [hz0, abs_zero]; positivity
  refine XV.mono (XV.sop2 hL (x := x) (a := z) (b := z) hx hz hz .add (by intro h; cases h) h0 h0
    (by simp [RealRAM.Op2.eval, hz0])) le_rfl fun σ' e => ?_
  subst e
  exact ⟨by simp [RealRAM.Op2.eval, hz0], by simp,
    (FrameA.refl (fun y => y = x) (fun _ => False) (fun _ _ => False) σ).setSc rfl _⟩

/-- The start state of ELL-R: `Â = D I` (`D` in the slot `c + 20`) into the cells `d i + k` of the array `a0`, `â = 0`
into the cells of `a0 + 1`, no kept point (`0` in `P + 1`). The register `n0 + 11` walks the cells, `n0 + 13` counts. -/
def xellArr (L : Layout) (B : EllBlk) (P u c a0 n0 : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst (n0 + 11) 0)))
  (.seq (xmapE L u (c + 24) (.sc u) a0 (n0 + 11) (n0 + 4) (n0 + 13) (n0 + 15) (n0 + 4))
  (.seq (.prim (.frag (.nconst (n0 + 11) 0)))
  (.seq (xmapE L u (c + 24) (.sc (c + 20)) a0 (n0 + 11) (n0 + 14) (n0 + 13) B.rd (n0 + 4))
  (.seq (.prim (.frag (.nconst (n0 + 11) 0)))
  (.seq (xmapE L u (c + 24) (.sc u) (a0 + 1) (n0 + 11) (n0 + 4) (n0 + 13) B.rd (n0 + 4))
    (xset L (P + 1) u u))))))

theorem diag_cell {d i k k' : ℕ} (hi : i < d) (hk : k < d) (hk' : k' < d) (e : d * i + k = 0 + (d + 1) * k') :
    i = k := by
  have h1 : (d * i + k) % d = k := by rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hk
  have h2 : (0 + (d + 1) * k') % d = k' := by
    rw [show 0 + (d + 1) * k' = d * k' + k' by ring, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hk'
  have hkk : k = k' := by rw [← h1, ← h2, e]
  subst hkk
  have : d * i = d * k := by
    have : d * i + k = d * k + k := by rw [e]; ring
    omega
  exact Nat.eq_of_mul_eq_mul_left (by omega) this

set_option maxHeartbeats 4000000 in
/-- The rule of `xellArr`. -/
theorem XV.ellArr {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk}
    {P u c a0 n0 E : ℕ} {D : ℤ} (hd : 1 ≤ d) (hPu : P + 2 ≤ u) (hc : u + 2 ≤ c) (hS : c + 26 ≤ L.NS)
    (hA : a0 + 2 ≤ L.NA) (hrd : B.rd < n0) (hN : n0 + 16 ≤ L.NN)
    (hz : σ.sc u = 0) (hD : σ.sc (c + 20) = D) (bD : |D| ≤ 2 ^ E) (hE : E < ℓ)
    (r4 : σ.nat (n0 + 4) = 1) (r14 : σ.nat (n0 + 14) = d + 1) (r15 : σ.nat (n0 + 15) = d * d)
    (hdv : σ.nat B.rd = d) :
    XRunsB L X ℓa ℓ (xellArr L B P u c a0 n0) σ (7 * (d * d) + 14 * d + 13) (fun σ' =>
      (∀ i k : Fin d, σ'.arr a0 (d * i + k) = ((D • (1 : Matrix (Fin d) (Fin d) ℤ)) i k : ℤ)) ∧
      (∀ k : Fin d, σ'.arr (a0 + 1) k = ((0 : Fin d → ℤ) k : ℤ)) ∧ σ'.sc (P + 1) = 0 ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = P + 1 ∨ c + 24 ≤ y) (fun j => j = n0 + 11 ∨ j = n0 + 13)
        (fun b _ => b = a0 ∨ b = a0 + 1) σ σ') := by
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  have hda := asz_lt hL (show a0 + 1 < L.NA by omega)
  unfold asz at hda
  have hd1 : d + 1 ≤ d * d + d := by nlinarith
  have hdd : (d + 1) * d = d * d + d := by ring
  have h0 : |(0 : ℤ)| ≤ 2 ^ E := by simp
  have hne : ∀ nn, nn = n0 + 15 ∨ nn = B.rd → [n0 + 11, n0 + 13, nn, n0 + 4].Nodup := fun nn hnn => by
    simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil, and_true,
      not_false_eq_true]; omega
  refine XV.mono (K := 1 + ((d * d * 7 + 3) + (1 + ((d * 7 + 3) + (1 + ((d * 7 + 3) + 1)))))) ?_
    (le_of_eq (by ring)) (fun _ h => h)
  -- `Â := 0`
  refine XV.seq (XV.nconstA hL (i := n0 + 11) (by omega) 0 (by positivity)) fun σ1 ⟨v1, d1, G1⟩ => ?_
  have e1 : ∀ j, j ≠ n0 + 11 → σ1.nat j = σ.nat j := fun j h => G1.1 j h
  refine XV.seq (XV.mapE (E := E) (N := d * d) (base := 0) (st := 1) (F := fun _ => 0) hL (z := u) (t := c + 24)
    (e := .sc u) (aB := a0) (nr := n0 + 11) (nst := n0 + 4) (nk := n0 + 13) (nn := n0 + 15) (none := n0 + 4)
    (by simp only [IE.WF]; omega) (by omega) (by simp only [IE.scr]; omega) (by rw [G1.2.1 _ id, hz]) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (hne _ (Or.inl rfl)) (by omega) (by omega)
    (by rw [e1 _ (by omega), r15]) (by rw [e1 _ (by omega), r4]) v1 (by rw [e1 _ (by omega), r4]) one_pos
    (fun k hk => by unfold asz; omega) (by omega) (by omega) hsa (by simp only [IE.top, IE.mag]; omega)
    (fun k _ σ' hF _ _ _ => ⟨⟨0, by rw [hF.2.1 _ (by omega), G1.2.1 _ id, hz]; simp, h0⟩,
      by simp only [IE.eval]; rw [hF.2.1 _ (by omega), G1.2.1 _ id, hz]; simp⟩)) fun σ2 ⟨z2, _, d2, F2⟩ => ?_
  have r2 : ∀ j, j ≠ n0 + 11 → j ≠ n0 + 13 → σ2.nat j = σ.nat j := fun j h h' => by
    rw [F2.1 _ (by omega), e1 _ h]
  -- the diagonal
  refine XV.seq (XV.nconstA hL (i := n0 + 11) (by omega) 0 (by positivity)) fun σ3 ⟨v3, d3, G3⟩ => ?_
  have r3 : ∀ j, j ≠ n0 + 11 → j ≠ n0 + 13 → σ3.nat j = σ.nat j := fun j h h' => by rw [G3.1 _ h, r2 _ h h']
  have s3 : ∀ y, y < c + 24 → σ3.sc y = σ.sc y := fun y hy => by
    rw [G3.2.1 _ id, F2.2.1 _ (by omega), G1.2.1 _ id]
  refine XV.seq (XV.mapEx (E := E) (N := d) (base := 0) (st := d + 1) (F := fun _ => D) hL (z := u)
    (t := c + 24) (e := .sc (c + 20)) (aB := a0) (nr := n0 + 11) (nst := n0 + 14) (nk := n0 + 13) (nn := B.rd)
    (none := n0 + 4) (by simp only [IE.WF]; omega) (by omega) (by simp only [IE.scr]; omega)
    (by rw [s3 _ (by omega), hz]) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (hne _ (Or.inr rfl)) (by omega) (by omega) (by rw [r3 _ (by omega) (by omega), hdv])
    (by rw [r3 _ (by omega) (by omega), r4]) v3 (by rw [r3 _ (by omega) (by omega), r14]) (by omega)
    (fun k hk => by unfold asz; nlinarith [Nat.mul_le_mul_left (d + 1) (show k + 1 ≤ d by omega)])
    (by omega) (by omega) (by omega) (by simp only [IE.top, IE.mag]; omega)
    (fun k _ σ' hF _ _ _ => ⟨⟨D, by rw [hF.2.1 _ (by omega), s3 _ (by omega), hD], bD⟩,
      by simp only [IE.eval]; rw [hF.2.1 _ (by omega), s3 _ (by omega), hD]⟩)) fun σ4 ⟨z4, _, d4, F4⟩ => ?_
  have r4' : ∀ j, j ≠ n0 + 11 → j ≠ n0 + 13 → σ4.nat j = σ.nat j := fun j h h' => by
    rw [F4.1 _ (by omega), r3 _ h h']
  -- `â := 0`
  refine XV.seq (XV.nconstA hL (i := n0 + 11) (by omega) 0 (by positivity)) fun σ5 ⟨v5, d5, G5⟩ => ?_
  have r5 : ∀ j, j ≠ n0 + 11 → j ≠ n0 + 13 → σ5.nat j = σ.nat j := fun j h h' => by rw [G5.1 _ h, r4' _ h h']
  have s5 : ∀ y, y < c + 24 → σ5.sc y = σ.sc y := fun y hy => by
    rw [G5.2.1 _ id, F4.2.1 _ (by omega), s3 _ hy]
  refine XV.seq (XV.mapE (E := E) (N := d) (base := 0) (st := 1) (F := fun _ => 0) hL (z := u) (t := c + 24)
    (e := .sc u) (aB := a0 + 1) (nr := n0 + 11) (nst := n0 + 4) (nk := n0 + 13) (nn := B.rd) (none := n0 + 4)
    (by simp only [IE.WF]; omega) (by omega) (by simp only [IE.scr]; omega) (by rw [s5 _ (by omega), hz])
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (hne _ (Or.inr rfl)) (by omega) (by omega)
    (by rw [r5 _ (by omega) (by omega), hdv]) (by rw [r5 _ (by omega) (by omega), r4]) v5
    (by rw [r5 _ (by omega) (by omega), r4]) one_pos (fun k hk => by unfold asz; nlinarith) (by omega)
    (by omega) hsa (by simp only [IE.top, IE.mag]; omega)
    (fun k _ σ' hF _ _ _ => ⟨⟨0, by rw [hF.2.1 _ (by omega), s5 _ (by omega), hz]; simp, h0⟩,
      by simp only [IE.eval]; rw [hF.2.1 _ (by omega), s5 _ (by omega), hz]; simp⟩)) fun σ6 ⟨z6, _, d6, F6⟩ => ?_
  have s6 : ∀ y, y < c + 24 → σ6.sc y = σ.sc y := fun y hy => by rw [F6.2.1 _ (by omega), s5 _ hy]
  -- no kept point
  refine XV.mono (XV.setZ hL (x := P + 1) (z := u) (by omega) (by omega) (by rw [s6 _ (by omega), hz])) le_rfl
    fun σ7 ⟨v7, d7, G7⟩ => ?_
  refine ⟨fun i k => ?_, fun k => ?_, v7, by rw [d7, d6, d5, d4, d3, d2, d1], ?_⟩
  · rw [G7.2.2.1 _ _ id, F6.2.2.1 _ _ (by omega), G5.2.2.1 _ _ id]
    by_cases hik : i = k
    · subst hik
      have := z4 i i.isLt
      rw [show 0 + (d + 1) * (i : ℕ) = d * i + i by ring] at this
      rw [this]; simp [Matrix.smul_apply, Matrix.one_apply]
    · have hcell : d * (i : ℕ) + k < d * d := by
        nlinarith [Nat.mul_le_mul_left d (show (i : ℕ) + 1 ≤ d by omega), k.isLt]
      rw [F4.2.2.1 _ _ (fun h => by
          obtain ⟨_, k', hk', e⟩ := h
          exact hik (Fin.ext (diag_cell i.isLt k.isLt hk' e))), G3.2.2.1 _ _ id]
      have := z2 _ hcell
      rw [zero_add, one_mul] at this
      rw [this]; simp [Matrix.smul_apply, Matrix.one_apply, hik]
  · rw [G7.2.2.1 _ _ id]
    have := z6 k k.isLt
    rw [zero_add, one_mul] at this
    rw [this]; simp
  · exact ((((((G1.mono (fun _ h => h.elim) (fun j h => Or.inl h) (fun _ _ h => h.elim)).trans
      (F2.mono (fun y h => Or.inr h) (fun j h => by omega) (fun b _ h => Or.inl h.1))).trans
      (G3.mono (fun _ h => h.elim) (fun j h => Or.inl h) (fun _ _ h => h.elim))).trans
      (F4.mono (fun y h => Or.inr h) (fun j h => by omega) (fun b _ h => Or.inl h.1))).trans
      (G5.mono (fun _ h => h.elim) (fun j h => Or.inl h) (fun _ _ h => h.elim))).trans
      (F6.mono (fun y h => Or.inr h) (fun j h => by omega) (fun b _ h => Or.inr h.1))).trans
      (G7.mono (fun y h => Or.inl h) (fun _ h => h.elim) (fun _ _ h => h.elim))

end AdversarialBco.Bit.Transfer
