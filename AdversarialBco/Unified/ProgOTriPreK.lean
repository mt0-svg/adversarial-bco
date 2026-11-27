/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOTriPreR
public import AdversarialBco.Bit.Transfer.XTriConsts
public import AdversarialBco.Bit.Transfer.XTriMag
public import AdversarialBco.Unified.ProgOSetupCoins

@[expose] public section

/-!
# BL-O's setup: the constants of TRI-OGD-O on the machine

`xpreK`: v2.1's prologue `xtcPro` at the bases `oT = 130`, `rT = 8`; the inputs `k_δ`, `r₀n`, `r₀d`, `R₀n`, `R₀d` of
the line into the slots `240, 241, 242, 248, 249`; v2.1's search of `triSQ d` (`xsearch`, at `n = 1`); the line `poSt`;
the copies of the constants of a draw into `oT + 4, ..., oT + 13`, `2^{G_c'}` into `oT + 35` and the constants of the
core step into the slots `102 - 112`; then `B_g`, `2^{n_e'}`, `m_st`, `e_τ + 3`, `stJ`, `stK` into the registers
`rT + 12`, `rT + 24`, `rT + 28`, `rT + 30`, `rT + 31`, `rT + 32`. `XV.preK`.
-/

namespace AdversarialBco.Unified.ProgO.TriO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM
  AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Unified.BLO AdversarialBco.Unified.ProgO
open AdversarialBco.BitRAM (len)

variable {d : ℕ}

/-! ## The search at `n = 1` -/

theorem mst_half_one : triMstQ (1 / 2) ((1 : ℕ) : ℚ) = 1 := by
  have h2 : Nat.clog 2 2 = 1 := by simpa using Nat.clog_pow 2 1 (by norm_num)
  unfold triMstQ
  rw [show ((1 : ℕ) : ℚ) / (1 / 2) = ((2 : ℕ) : ℚ) by norm_num, Nat.ceil_natCast, h2]
  rfl

theorem ellPos_one_le (d : ℕ) : ellPos d 1 ≤ 21 + 3 * d := by
  unfold ellPos
  rw [mst_half_one]
  apply Nat.clog_le_of_le_pow
  have h1 : d ^ 3 ≤ 2 ^ (3 * d) := by
    rw [mul_comm, pow_mul]; exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le 3
  calc 3 * 2 ^ 19 * (d * 1) ^ 3 * 1 ≤ 2 ^ 2 * 2 ^ 19 * 2 ^ (3 * d) := by
        rw [mul_one, mul_one]; gcongr; norm_num
    _ = 2 ^ (21 + 3 * d) := by rw [← pow_add, ← pow_add]

/-- v2.1's parameter of the search at `n = 1`. -/
theorem tcG_one_le {d : ℕ} (hd : 1 ≤ d) : tcG d 1 ≤ 1100 * (d + 2 * tzP d + 4) := by
  have hLa := triLa_le_lin hd
  have hLh := triLh_le_lin hd
  have hJa := triJaQ_le_lin hd
  have hBv := triBvQ_le_lin hd
  have hGc := tzGc_le_lin hd (ellPos d 1)
  have hE := ellPos_one_le d
  have hS := (triSQ_bounds d).2
  unfold tcG
  rw [Nat.size_one]
  omega

/-! ## The inputs of the line -/

/-- `k_δ`, `r₀n`, `r₀d` (from `sKd`, `100`, `101`) and `R₀n`, `R₀d` (input cells `6`, `7`) into the input slots
`240, 241, 242, 248, 249` of the line. -/
def xpreIn (L : Layout) : XCmd :=
  .seq (toX (VL.sop2 L .add 240 sKd sZ)) <| .seq (toX (VL.sop2 L .add 241 100 sZ)) <|
  .seq (toX (VL.sop2 L .add 242 101 sZ)) <| .seq (.prim (.frag (.nconst 12 6))) <| .seq (xrdIn L 248 12) <|
  .seq (.prim (.frag (.nconst 12 7))) (xrdIn L 249 12)

/-- The slots of the inputs. -/
def SIn (y : ℕ) : Prop := y = 240 ∨ y = 241 ∨ y = 242 ∨ y = 248 ∨ y = 249

set_option maxHeartbeats 2000000 in
theorem XV.preIn {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hS : 250 ≤ L.NS)
    (hN : 13 ≤ L.NN) {k : ℕ} {rn rd Rn Rd : ℤ} (hk : σ.sc sKd = (k : ℤ)) (h100 : σ.sc 100 = rn)
    (h101 : σ.sc 101 = rd) (hz : σ.sc sZ = 0) (i6 : X.inp 6 = Rn) (i7 : X.inp 7 = Rd) (hoff : 8 ≤ X.off)
    (hkl : (k : ℤ) < 2 ^ ℓ) (bn : |rn| < 2 ^ ℓ) (bd : |rd| < 2 ^ ℓ) (bN : |Rn| < 2 ^ ℓ) (bD : |Rd| < 2 ^ ℓ)
    (ha : 8 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xpreIn L) σ 7 (fun σ' =>
      σ'.sc 240 = (k : ℤ) ∧ σ'.sc 241 = rn ∧ σ'.sc 242 = rd ∧ σ'.sc 248 = Rn ∧ σ'.sc 249 = Rd ∧
      σ'.draws = σ.draws ∧ FrameA SIn (fun j => j = 12) (fun _ _ => False) σ σ') := by
  have b0 : |(0 : ℤ)| < 2 ^ ℓ := by rw [abs_zero]; positivity
  have bk : |(k : ℤ)| < 2 ^ ℓ := by rw [abs_of_nonneg (by positivity)]; exact hkl
  refine XV.mono (K := 1 + (1 + (1 + (1 + (1 + (1 + 1)))))) ?_ (by norm_num) fun _ h => h
  refine XV.seq (XV.addI hL (x := 240) (a := sKd) (b := sZ) (by omega) (by simp only [sKd]; omega)
    (by simp only [sZ]; omega) (u := k) (v := 0) hk (by rw [hz]; simp) bk b0 (by rw [add_zero]; exact bk))
    fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.addI hL (x := 241) (a := 100) (b := sZ) (by omega) (by omega) (by simp only [sZ]; omega)
    (u := rn) (v := 0) (by esimp; exact h100) (by esimp; rw [hz]; simp) bn b0 (by rw [add_zero]; exact bn))
    fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.addI hL (x := 242) (a := 101) (b := sZ) (by omega) (by omega) (by simp only [sZ]; omega)
    (u := rd) (v := 0) (by esimp; exact h101) (by esimp; rw [hz]; simp) bd b0 (by rw [add_zero]; exact bd))
    fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.nconst hL (i := 12) (by omega) 6 (by omega)) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.rdIn (X := X) hL (x := 248) (i := 12) (by omega) (by omega) (by esimp; omega) (by esimp; omega)
    (by esimp; rw [i6, ← Int.cast_abs]; exact_mod_cast bN)) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.nconst hL (i := 12) (by omega) 7 (by omega)) fun σ6 e6 => ?_
  subst e6
  refine XV.mono (XV.rdIn (X := X) hL (x := 249) (i := 12) (by omega) (by omega) (by esimp; omega)
    (by esimp; omega) (by esimp; rw [i7, ← Int.cast_abs]; exact_mod_cast bD)) le_rfl fun σ7 e7 => ?_
  subst e7
  refine ⟨by esimp; push_cast; ring, by esimp; push_cast; ring, by esimp; push_cast; ring, by esimp; rw [i6],
    by esimp; rw [i7], by simp, ?_⟩
  exact (((((((FrameA.refl SIn (fun j => j = 12) (fun _ _ => False) σ).setSc (x := 240) (Or.inl rfl) _).setSc
    (x := 241) (Or.inr (Or.inl rfl)) _).setSc (x := 242) (Or.inr (Or.inr (Or.inl rfl))) _).setNat (i := 12) rfl
    _).setSc (x := 248) (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _).setNat (i := 12) rfl _).setSc (x := 249)
    (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) _

theorem poG_ge (d n k : ℕ) (r0 R0 : ℚ) :
    d ≤ poG d n k r0 R0 ∧ k ≤ poG d n k r0 R0 ∧ n.size ≤ poG d n k r0 R0 ∧ len r0.num ≤ poG d n k r0 R0 ∧
      len (r0.den : ℤ) ≤ poG d n k r0 R0 ∧ len R0.num ≤ poG d n k r0 R0 ∧ len (R0.den : ℤ) ≤ poG d n k r0 R0 ∧
      2 ≤ poG d n k r0 R0 ∧ triETauQ d + 3 ≤ poG d n k r0 R0 ∧ stJ d ≤ poG d n k r0 R0 ∧
      stK d r0 R0 ≤ poG d n k r0 R0 ∧ len R0.num + len (r0.den : ℤ) + 1 ≤ poG d n k r0 R0 := by
  unfold poG
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-! ## The constants block -/

/-- The copies `(target, source)`: the constants of a draw into `oT + 4, ..., oT + 13`, `2^{G_c'}` into `oT + 35`, the
constants of the core step into `102 - 112`, from the slots `250 + k` of the line (`1` from `oT + 2`). -/
def poCp : List (ℕ × ℕ) :=
  [(134, 299), (135, 329), (136, 330), (137, 282), (138, 332), (139, 333), (140, 335), (141, 338), (142, 339),
   (143, 340), (165, 341), (102, 355), (103, 357), (104, 359), (105, 361), (106, 362), (107, 363), (108, 132),
   (109, 364), (110, 375), (111, 366), (112, 368)]

/-- **The constants block**: the prologue, the inputs, the search of `triSQ d`, the line, the copies, the registers. -/
def xpreK (L : Layout) : XCmd :=
  .seq (xtcPro L rD rD sN 130 8) <| .seq (xpreIn L) <| .seq (xsearch L 130 8) <|
  .seq (SL.code L (SLC.atB 130 8 poC) (poSt.map (SStep.shS 130))) <| .seq (xcopyS L 131 poCp) <|
  .seq (xrtoN L 20 289) <| .seq (xrtoN L 32 319) <| .seq (xrtoN L 36 309) <| .seq (xrtoN L 38 369) <|
  .seq (xrtoN L 39 353) (xrtoN L 40 374)

/-- The constants of the core step in their cells (the fields of `TriKXAt` past the frame centre). -/
structure KXC (d n : ℕ) (δ r0 R0 : ℚ) (σ : Env d) : Prop where
  cE : σ.sc sCE = ((2 ^ stE d : ℤ) : ℝ)
  cL1 : σ.sc sCL1 = ((2 ^ (stE d - stE1 d) : ℤ) : ℝ)
  cSh : σ.sc sCSh = ((2 ^ (triETauQ d + 4) : ℤ) : ℝ)
  cA : σ.sc sCA = ((2 ^ (stE d + triETauQ d + 1) : ℤ) : ℝ)
  cB : σ.sc sCB = ((2 ^ stEu d : ℤ) : ℝ)
  nJ : σ.nat rNJ = triETauQ d + 3
  hn : σ.sc sHn = ((2 ^ stEH d : ℤ) : ℝ)
  hd : σ.sc sHd = 1
  nj : σ.nat rNj = stJ d
  c2j : σ.sc sC2j = ((2 ^ stJ d : ℤ) : ℝ)
  nk : σ.nat rNk = stK d r0 R0
  c2k : σ.sc sC2k = ((2 ^ stK d r0 R0 : ℤ) : ℝ)
  c2K : σ.sc sC2K = ((2 ^ tKZ d (ellO d n δ r0 R0) : ℤ) : ℝ)
  bb : σ.sc sBb = ((tBb d : ℤ) : ℝ)

/-- The units of the constants block. -/
abbrev preKK (d n k : ℕ) (r0 R0 : ℚ) : ℕ :=
  15 + (7 + (srchK d 1 + (ev (poG d n k r0 R0) (876, 5280) + (22 + (1 + (1 + (1 + (1 + (1 + 1)))))))))

set_option maxHeartbeats 16000000 in
theorem XV.preK {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hS : 420 ≤ L.NS)
    (hN : 48 ≤ L.NN) {n : ℕ} {δ r0 R0 : ℚ} (hd : 1 ≤ d) (hr : 0 < r0 ∧ r0 ≤ R0) (hD : σ.nat rD = d)
    (hn : σ.sc sN = n) (hz : σ.sc sZ = 0) (hk : σ.sc sKd = ((kDel δ : ℕ) : ℤ)) (h100 : σ.sc 100 = r0.num)
    (h101 : σ.sc 101 = (r0.den : ℤ)) (i6 : X.inp 6 = R0.num) (i7 : X.inp 7 = R0.den) (hoff : 8 ≤ X.off)
    (hda : d * d + d + (d + d) + 2 < 2 ^ ℓa) (hTl : ev (tcG d 1) tcT < ℓ) (hTa : ev (tcG d 1) tcT < 2 ^ ℓa)
    (hGl : ev (poG d n (kDel δ) r0 R0) poT < ℓ) (hGa : ev (poG d n (kDel δ) r0 R0) poT < 2 ^ ℓa)
    (hNa : 2 ^ triNeTQ d (ellO d n δ r0 R0) < 2 ^ ℓa) (hBa : triBgQ d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xpreK L) σ (preKK d n (kDel δ) r0 R0) (fun σ' =>
      TriKV d n δ r0 R0 σ' ∧ KXC d n δ r0 R0 σ' ∧ σ'.nat rT = 1 ∧ σ'.nat (rT + 28) = triMstQ r0 R0 ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => (102 ≤ y ∧ y ≤ 112) ∨ 130 ≤ y) (fun j => 8 ≤ j) (fun _ _ => False) σ σ') := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩ := poG_ge d n (kDel δ) r0 R0
  set k := kDel δ with hkk
  set G := poG d n k r0 R0 with hG
  have hGl1 : G + 1 < ℓ := by have := hGl; simp only [ev, poT] at this; omega
  have hGa1 : G + 1 < 2 ^ ℓa := by have := hGa; simp only [ev, poT] at this; omega
  have hpG : ∀ x : ℕ, x ≤ G → (2 : ℤ) ^ x < 2 ^ ℓ := fun x hx => pow_lt_pow_right₀ (by norm_num) (by omega)
  have hlen : ∀ z : ℤ, len z ≤ G → |z| < 2 ^ ℓ := fun z h => (abs_lt_len z).trans_le
    (pow_le_pow_right₀ (by norm_num) (by have := hpG _ h; omega))
  have hp : ∀ x : ℕ, x ≤ G + 1 → x + 4 < 2 ^ ℓ := fun x hx => by
    have h1 : 2 ^ (G + 2) ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hGl1
    have h2 : G + 1 < 2 ^ (G + 1) := Nat.lt_two_pow_self
    rw [pow_succ] at h1; omega
  have hdG : d ≤ G := g1
  have hkG : k ≤ G := g2
  have hsG : n.size ≤ G := g3
  have hnG : n < 2 ^ G := (Nat.lt_size_self n).trans_le (Nat.pow_le_pow_right (by norm_num) hsG)
  have hn4 : n + 4 < 2 ^ ℓ := by
    have h1 : 2 ^ (G + 2) ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hGl1
    have h2 : 2 ^ 2 ≤ 2 ^ G := Nat.pow_le_pow_right (by norm_num) g8
    rw [pow_succ, pow_succ] at h1; omega
  unfold xpreK
  -- the prologue
  refine XV.seq (XV.tcPro (n := n) hL (nd := rD) (rm := rD) (sn := sN) (o := 130) (r := 8) (m := d) (by omega)
    (by omega) (by decide) (by decide) (by decide) hD hD hn hda (hp d (by omega)) hn4)
    fun σ1 ⟨a1, a2, a3, a25, a26, c1, c2, c3, c116, c117, c115, c113, c114, d1, F1⟩ => ?_
  have k1 : ∀ y, y < 130 → σ1.sc y = σ.sc y := fun y hy => F1.2.1 y (by omega)
  -- the inputs
  refine XV.seq (XV.preIn (X := X) hL (by omega) (by omega) (k := k) (rn := r0.num) (rd := (r0.den : ℤ))
    (Rn := R0.num) (Rd := (R0.den : ℤ)) (by rw [k1 _ (by simp only [sKd]; omega), hk])
    (by rw [k1 _ (by omega), h100]) (by rw [k1 _ (by omega), h101]) (by rw [k1 _ (by simp only [sZ]; omega), hz])
    i6 i7 hoff (by exact_mod_cast (hp k (by omega)).trans' (by omega)) (hlen _ g4)
    (hlen _ g5) (hlen _ g6)
    (hlen _ g7) (by have := hL.1; omega))
    fun σ2 ⟨q240, q241, q242, q248, q249, d2, F2⟩ => ?_
  have k2 : ∀ y, ¬ SIn y → σ2.sc y = σ1.sc y := fun y h => F2.2.1 y h
  have j2 : ∀ j, j ≠ 12 → σ2.nat j = σ1.nat j := fun j h => F2.1 j h
  -- the search
  refine XV.seq (XV.search (n := 1) hL (o := 130) (r := 8) (by omega) (by omega) hTl hTa
    (by rw [k2 _ (by simp only [SIn]; omega), c113]) (by rw [k2 _ (by simp only [SIn]; omega), c115])
    (by rw [k2 _ (by simp only [SIn]; omega), c1]) (by rw [k2 _ (by simp only [SIn]; omega), c2])
    (by rw [k2 _ (by simp only [SIn]; omega), c116]) (by rw [k2 _ (by simp only [SIn]; omega), c117])
    (by rw [j2 8 (by omega), a1])) fun σ3 ⟨s3, d3, F3⟩ => ?_
  have k3 : ∀ y, ¬ srS 130 y → σ3.sc y = σ2.sc y := fun y h => F3.2.1 y h
  have j3 : ∀ j, ¬ srN 8 j → σ3.nat j = σ2.nat j := fun j h => F3.1 j h
  -- the line
  have hchk : SL.chk poC.b poIns poInP poEt poT 40 poSt = true := by simp only [poC]; exact poSt_chk
  have hsem : ∀ j < poSt.length, (poSt.getD j (.cst 0)).Sem (SL.val poSt poC.b (poIn d n k r0 R0)) G := by
    simp only [poC]; exact fun j hj => poSt_sem hd hr j hj
  have hlen : poC.b + poSt.length ≤ poC.t := by simp only [poC, poSt_length]; norm_num
  have h := XV.slAt (X := X) (σ := σ3) (C := poC) (S := 40) (G := G) (o := 130) (r := 8) (et := poEt) (T := poT)
    (ι := poIn d n k r0 R0) (ins := poIns) (eIn := poInP) (st := poSt) hL (poC_ok (by omega) (by omega))
    hchk hsem hlen hGl hGa poIn_bound
    (fun y hy => by
      simp only [poIns, List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [k3 _ (by simp only [srS]; omega), q240]; simp [poIn]
      · rw [k3 _ (by simp only [srS]; omega), q241]; simp [poIn]
      · rw [k3 _ (by simp only [srS]; omega), q242]; simp [poIn]
      · rw [k3 _ (by simp only [srS]; omega), k2 _ (by simp only [SIn]; omega), c113]; simp [poIn]
      · rw [k3 _ (by simp only [srS]; omega), k2 _ (by simp only [SIn]; omega), c114]; simp [poIn]
      · rw [s3]; simp [poIn]
      · rw [k3 _ (by simp only [srS]; omega), q248]; simp [poIn]
      · rw [k3 _ (by simp only [srS]; omega), q249]; simp [poIn])
    (by show σ3.sc (1 + 130) = 0
        rw [k3 _ (by simp only [srS]; omega), k2 _ (by simp only [SIn]; omega), c1])
    (by show σ3.sc (2 + 130) = 1
        rw [k3 _ (by simp only [srS]; omega), k2 _ (by simp only [SIn]; omega), c2])
    (by show σ3.sc (116 + 130) = 2
        rw [k3 _ (by simp only [srS]; omega), k2 _ (by simp only [SIn]; omega), c116])
    (by show σ3.sc (117 + 130) = 4
        rw [k3 _ (by simp only [srS]; omega), k2 _ (by simp only [SIn]; omega), c117])
    (by show σ3.nat (0 + 8) = 1
        rw [j3 _ (by simp only [srN]; omega), j2 _ (by omega), a1])
  rw [poSt_units] at h
  refine XV.seq h fun σ4 ⟨v4, d4, F4⟩ => ?_
  have vS : ∀ j < 126, σ4.sc (250 + j) = ((poV d n k r0 R0 j : ℤ) : ℝ) := fun j hj => by
    have h' := v4 j (by rw [poSt_length]; exact hj)
    rw [show poC.b + 130 + j = 250 + j by simp only [poC]] at h'
    exact h'
  have k4 : ∀ y, y < 250 → σ4.sc y = σ3.sc y := fun y hy =>
    F4.2.1 y (by simp only [poC, poSt_length]; omega)
  have j4 : ∀ j, j < 37 → σ4.nat j = σ3.nat j := fun j hj => F4.1 j (by simp only [poC]; omega)
  have hbv := SL.val_bound poSt 120 (poIn d n k r0 R0) poIns poInP poEt poT 40 G (SL.chk_get poSt_chk).2
    (fun j hj => poSt_sem hd hr j hj) poIn_bound
  have bS : ∀ j < 126, ple (poEt j) poT = true → ∀ y, y = 250 + j → |σ4.sc y| < 2 ^ ℓ := fun j hj hpl y hy => by
    rw [hy, vS j hj]; exact absZ_lt (hbv j (by rw [poSt_length]; exact hj)) ((ev_mono hpl).trans_lt hGl)
  have bZ : ∀ j < 126, ple (poEt j) poT = true → |poV d n k r0 R0 j| < 2 ^ ℓ := fun j hj hpl =>
    (hbv j (by rw [poSt_length]; exact hj)).trans_lt (pow_lt_pow_right₀ (by norm_num) ((ev_mono hpl).trans_lt hGl))
  -- the copies
  have c132 : σ4.sc 132 = 1 := by
    rw [k4 _ (by omega), k3 _ (by simp only [srS]; omega), k2 _ (by simp only [SIn]; omega), c2]
  refine XV.seq (XV.copyS hL (z := 131) (by omega) poCp σ4
    (by rw [k4 _ (by omega), k3 _ (by simp only [srS]; omega), k2 _ (by simp only [SIn]; omega), c1])
    (by
      intro p hp
      simp only [poCp, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> refine ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, ?_⟩
      · exact bS 49 (by norm_num) (by decide) _ rfl
      · exact bS 79 (by norm_num) (by decide) _ rfl
      · exact bS 80 (by norm_num) (by decide) _ rfl
      · exact bS 32 (by norm_num) (by decide) _ rfl
      · exact bS 82 (by norm_num) (by decide) _ rfl
      · exact bS 83 (by norm_num) (by decide) _ rfl
      · exact bS 85 (by norm_num) (by decide) _ rfl
      · exact bS 88 (by norm_num) (by decide) _ rfl
      · exact bS 89 (by norm_num) (by decide) _ rfl
      · exact bS 90 (by norm_num) (by decide) _ rfl
      · exact bS 91 (by norm_num) (by decide) _ rfl
      · exact bS 105 (by norm_num) (by decide) _ rfl
      · exact bS 107 (by norm_num) (by decide) _ rfl
      · exact bS 109 (by norm_num) (by decide) _ rfl
      · exact bS 111 (by norm_num) (by decide) _ rfl
      · exact bS 112 (by norm_num) (by decide) _ rfl
      · exact bS 113 (by norm_num) (by decide) _ rfl
      · dsimp only; rw [c132, abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
      · exact bS 114 (by norm_num) (by decide) _ rfl
      · exact bS 125 (by norm_num) (by decide) _ rfl
      · exact bS 116 (by norm_num) (by decide) _ rfl
      · exact bS 118 (by norm_num) (by decide) _ rfl)
    (by decide)
    (by
      intro p hp q hq
      simp only [poCp, List.mem_cons, List.mem_nil_iff, or_false] at hp hq
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) fun σ5 ⟨v5, d5, F5⟩ => ?_
  have k5 : ∀ y, y ∉ poCp.map Prod.fst → σ5.sc y = σ4.sc y := fun y h => F5.2.1 y h
  have cpv : ∀ x j, (x, 250 + j) ∈ poCp → j < 126 → σ5.sc x = ((poV d n k r0 R0 j : ℤ) : ℝ) :=
    fun x j hm hj => (v5 _ hm).trans (vS j hj)
  have nF : ∀ y, y ∉ poCp.map Prod.fst ↔ ¬ ((102 ≤ y ∧ y ≤ 112) ∨ (134 ≤ y ∧ y ≤ 143) ∨ y = 165) := fun y => by
    simp only [poCp, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false]; omega
  have rv : ∀ j < 126, ∀ y, y = 250 + j → σ5.sc y = ((poV d n k r0 R0 j : ℤ) : ℝ) := fun j hj y hy => by
    rw [hy, k5 _ ((nF _).2 (by omega)), vS j hj]
  -- the registers
  have hBg : triBgQ d < 2 ^ ℓ := by
    have := bZ 39 (by norm_num) (by decide); rw [poV_39 d n k r0 R0 hd] at this
    rw [abs_of_nonneg (by positivity)] at this; exact_mod_cast this
  refine XV.seq (XV.rtoNat hL (i := 20) (x := 289) (v := triBgQ d) (by omega) (by omega)
    (by rw [rv 39 (by norm_num) _ rfl, poV_39 d n k r0 R0 hd]) hBa hBg) fun σ6 e6 => ?_
  subst e6
  have hNl : 2 ^ triNeTQ d (ellO d n δ r0 R0) < 2 ^ ℓ := by
    have := bZ 69 (by norm_num) (by decide); rw [poV_69 d n k r0 R0 hd hr] at this
    rw [abs_of_nonneg (by positivity)] at this; exact_mod_cast this
  refine XV.seq (XV.rtoNat hL (i := 32) (x := 319) (v := 2 ^ triNeTQ d (ellO d n δ r0 R0)) (by omega) (by omega)
    (by rw [Env.setNat_sc, rv 69 (by norm_num) _ rfl, poV_69 d n k r0 R0 hd hr]) hNa hNl) fun σ7 e7 => ?_
  subst e7
  have hmG : triMstQ r0 R0 ≤ G := (triMstQ_le hr.1 hr.2).trans g12
  refine XV.seq (XV.rtoNat hL (i := 36) (x := 309) (v := triMstQ r0 R0) (by omega) (by omega)
    (by simp only [Env.setNat_sc]; rw [rv 59 (by norm_num) _ rfl, poV_59 d n k r0 R0 hr]) (by omega)
    (by have := hp _ (by omega : triMstQ r0 R0 ≤ G + 1); omega)) fun σ8 e8 => ?_
  subst e8
  have heG : triETauQ d + 3 ≤ G := g9
  refine XV.seq (XV.rtoNat hL (i := 38) (x := 369) (v := triETauQ d + 3) (by omega) (by omega)
    (by simp only [Env.setNat_sc]; rw [rv 119 (by norm_num) _ rfl, poV_119 d n k r0 R0 hd]) (by omega)
    (by have := hp _ (by omega : triETauQ d + 3 ≤ G + 1); omega)) fun σ9 e9 => ?_
  subst e9
  have hJG : stJ d ≤ G := g10
  refine XV.seq (XV.rtoNat hL (i := 39) (x := 353) (v := stJ d) (by omega) (by omega)
    (by simp only [Env.setNat_sc]; rw [rv 103 (by norm_num) _ rfl, poV_103 d n k r0 R0 hd]) (by omega)
    (by have := hp _ (by omega : stJ d ≤ G + 1); omega)) fun σ10 e10 => ?_
  subst e10
  have hKG : stK d r0 R0 ≤ G := g11
  refine XV.mono (XV.rtoNat hL (i := 40) (x := 374) (v := stK d r0 R0) (by omega) (by omega)
    (by simp only [Env.setNat_sc]; rw [rv 124 (by norm_num) _ rfl, poV_124 d n k r0 R0 hd hr]) (by omega)
    (by have := hp _ (by omega : stK d r0 R0 ≤ G + 1); omega)) le_rfl fun σ11 e11 => ?_
  subst e11
  -- the cells before the copies
  have R5 : ∀ j, j < 37 → j ≠ 12 → σ5.nat j = σ1.nat j := fun j hj h12 => by
    rw [F5.1 j id, j4 j hj, j3 j (by simp only [srN]; omega), j2 j h12]
  have S5 : ∀ y, y < 245 → y ∉ poCp.map Prod.fst → ¬ SIn y → σ5.sc y = σ1.sc y := fun y hy h1 h2 => by
    rw [k5 y h1, k4 y (by omega), k3 y (by simp only [srS]; omega), k2 y h2]
  have cp : ∀ x j, (x, 250 + j) ∈ poCp → j < 126 → ∀ v : ℤ, poV d n k r0 R0 j = v →
      ((((((σ5.setNat 20 (triBgQ d)).setNat 32 (2 ^ triNeTQ d (ellO d n δ r0 R0))).setNat 36 (triMstQ r0 R0)).setNat
        38 (triETauQ d + 3)).setNat 39 (stJ d)).setNat 40 (stK d r0 R0)).sc x = (v : ℝ) := fun x j hm hj v hv => by
    simp only [Env.setNat_sc]; rw [cpv x j hm hj, hv]
  refine ⟨⟨?_, ?_, by simp, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, by simp [rNJ], ?_, ?_, by simp [rNj], ?_, by simp [rNk], ?_, ?_, ?_⟩,
    ?_, by simp, by simp [d5, d4, d3, d2, d1], ?_⟩
  · simp only [Env.setNat_nat, rD]; rw [R5 0 (by omega) (by omega)]; exact (F1.1 0 (by omega)).trans hD
  · simp only [Env.setNat_nat, rT]; rw [R5 9 (by omega) (by omega)]; exact a2
  · simp only [Env.setNat_nat, rT]; rw [R5 33 (by omega) (by omega)]; exact a25
  · simp only [Env.setNat_sc, oT]
    rw [S5 131 (by omega) ((nF _).2 (by omega)) (by simp only [SIn]; omega)]; exact c1
  · simp only [Env.setNat_sc, oT]
    rw [S5 132 (by omega) ((nF _).2 (by omega)) (by simp only [SIn]; omega)]; exact c2
  · simp only [Env.setNat_sc, oT]
    rw [S5 133 (by omega) ((nF _).2 (by omega)) (by simp only [SIn]; omega)]; exact c3
  · rw [cp _ 49 (by decide) (by norm_num) _ (poV_49 d n k r0 R0 hd)]; simp [tzDCO]
  · exact cp _ 79 (by decide) (by norm_num) _ (poV_79 d n k r0 R0 hd)
  · exact cp _ 80 (by decide) (by norm_num) _ (poV_80 d n k r0 R0 hd hr)
  · rw [cp _ 32 (by decide) (by norm_num) _ (poV_32 d n k r0 R0)]; simp [tzDCO]
  · exact cp _ 82 (by decide) (by norm_num) _ (poV_82 d n k r0 R0 hd hr)
  · rw [cp _ 83 (by decide) (by norm_num) _ (poV_83 d n k r0 R0 hd hr), Int.cast_neg]
  · exact cp _ 85 (by decide) (by norm_num) _ (poV_85 d n k r0 R0 hd hr)
  · exact cp _ 88 (by decide) (by norm_num) _ (poV_88 d n k r0 R0 hd hr)
  · exact cp _ 89 (by decide) (by norm_num) _ (poV_89 d n k r0 R0 hd hr)
  · exact cp _ 90 (by decide) (by norm_num) _ (poV_90 d n k r0 R0)
  · exact cp _ 91 (by decide) (by norm_num) _ (poV_91 d n k r0 R0 hd hr)
  · exact cp _ 105 (by decide) (by norm_num) _ (poV_105 d n k r0 R0 hd)
  · exact cp _ 107 (by decide) (by norm_num) _ (poV_107 d n k r0 R0 hd)
  · exact cp _ 109 (by decide) (by norm_num) _ (poV_109 d n k r0 R0 hd)
  · exact cp _ 111 (by decide) (by norm_num) _ (poV_111 d n k r0 R0 hd)
  · exact cp _ 112 (by decide) (by norm_num) _ (poV_112 d n k r0 R0 hd)
  · exact cp _ 113 (by decide) (by norm_num) _ (poV_113 d n k r0 R0 hd)
  · simp only [Env.setNat_sc, sHd]; rw [v5 (108, 132) (by decide)]; exact c132
  · exact cp _ 114 (by decide) (by norm_num) _ (poV_114 d n k r0 R0 hd)
  · exact cp _ 125 (by decide) (by norm_num) _ (poV_125 d n k r0 R0 hd hr)
  · exact cp _ 116 (by decide) (by norm_num) _ (poV_116 d n k r0 R0 hd hr)
  · exact cp _ 118 (by decide) (by norm_num) _ (poV_118 d n k r0 R0 hd)
  · simp only [Env.setNat_nat, rT]; rw [R5 8 (by omega) (by omega)]; exact a1
  · have G1 : FrameA (fun y => (102 ≤ y ∧ y ≤ 112) ∨ 130 ≤ y) (fun j => 8 ≤ j) (fun _ _ => False) σ σ1 :=
      F1.mono (fun y h => Or.inr h) (fun _ h => h) (fun _ _ h => h)
    have G2 : FrameA (fun y => (102 ≤ y ∧ y ≤ 112) ∨ 130 ≤ y) (fun j => 8 ≤ j) (fun _ _ => False) σ1 σ2 :=
      F2.mono (fun y h => by simp only [SIn] at h; omega) (fun j h => by omega) (fun _ _ h => h)
    have G3 : FrameA (fun y => (102 ≤ y ∧ y ≤ 112) ∨ 130 ≤ y) (fun j => 8 ≤ j) (fun _ _ => False) σ2 σ3 :=
      (FrameA.ofP (Ar := fun _ _ => False) F3).mono (fun y h => by simp only [srS] at h; omega)
        (fun j h => by simp only [srN] at h; omega) (fun _ _ h => h)
    have G4 : FrameA (fun y => (102 ≤ y ∧ y ≤ 112) ∨ 130 ≤ y) (fun j => 8 ≤ j) (fun _ _ => False) σ3 σ4 :=
      (FrameA.ofP (Ar := fun _ _ => False) F4).mono (fun y h => by simp only [poC, poSt_length] at h; omega)
        (fun j h => by simp only [poC] at h; omega) (fun _ _ h => h)
    have G5 : FrameA (fun y => (102 ≤ y ∧ y ≤ 112) ∨ 130 ≤ y) (fun j => 8 ≤ j) (fun _ _ => False) σ4 σ5 :=
      F5.mono (fun y h => by
        simp only [poCp, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at h; omega)
        (fun _ h => h.elim) (fun _ _ h => h)
    exact ((((((G1.trans (G2.trans (G3.trans (G4.trans G5)))).setNat (by omega) _).setNat (by omega) _).setNat
      (by omega) _).setNat (by omega) _).setNat (by omega) _).setNat (by omega) _

end AdversarialBco.Unified.ProgO.TriO
