/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLEndInv
public import AdversarialBco.Bit.Transfer.XBLSetupPrm
public import AdversarialBco.Bit.Transfer.XEllUpd

@[expose] public section

/-!
# R15 COMMIT on the machine

`xcommit L`: `first := 0`; `D_μ := 2^e` with `e` from the slot `oE + 1` (`xrtoN`, then `xpow2`); the numerators of
`μ'` from the array `aWE`; `A'`, `B'` (`d²` cells) from the arrays `26`, `27`, `b'`, `G'` (`d` cells) from `28`, `29`;
`k'`, `l'` from the slots `59`, `63`. `commitBL : CommitBL` with `C = 64`, `k = 2`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-- R15, the point: `first := 0`, `D_μ := 2^e`, the numerators of `μ'` into `aMu`. -/
def xcomMu (L : Layout) : XCmd :=
  .seq (xrtoN L 8 (oE + 1)) (.seq (xpow2 L sDmu 9 8 rOne) (.seq (toX (VL.sconst L sFirst 0))
    (xcopyN L sZ 128 aWE aMu 10 11 rD rOne)))

/-- R15, the grid values: `A'`, `B'`, `b'`, `G'` into `aA`, `aB`, `ab`, `aG`, `k'`, `l'` into `sK`, `sL`. -/
def xcomArr (L : Layout) : XCmd :=
  .seq (xnmul 12 rD rD) (.seq (xcopyN L sZ 128 26 aA 10 11 12 rOne) (.seq (xcopyN L sZ 128 27 aB 10 11 12 rOne)
    (.seq (xcopyN L sZ 128 28 ab 10 11 rD rOne) (.seq (xcopyN L sZ 128 29 aG 10 11 rD rOne)
    (xcopyS L sZ [(sK, 59), (sL, 63)])))))

/-- **R15 COMMIT.** -/
def xcommit (L : Layout) : XCmd := .seq (xcomMu L) (xcomArr L)

set_option maxHeartbeats 2000000 in
/-- The rule of `xcomMu`. -/
theorem XV.comMu {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L)
    {σ : Env d} {E e : ℕ} {x : Fin d → ℤ} (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0)
    (hout : EllOut blkBL (some x) e σ) (bx : ∀ j, |x j| ≤ 2 ^ E) (he : e ≤ E) (hE : E < ℓ) (hEa : E < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xcomMu L) σ (4 * E + d * 8 + 10) (fun σ' =>
      σ'.sc sFirst = 0 ∧ σ'.sc sDmu = ((2 ^ e : ℤ) : ℝ) ∧ (∀ k < d, σ'.arr aMu k = vext x k) ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => y = sFirst ∨ y = sDmu ∨ 128 ≤ y) (fun j => 8 ≤ j ∧ j ≤ 11) (fun b c => b = aMu ∧ c < d)
        σ σ') := by
  obtain ⟨hS, hN, hA⟩ := hlay
  simp only [oE, rEE, aWE] at hS hN hA
  obtain ⟨-, he1, hxw⟩ := hout
  have he1' : σ.sc (oE + 1) = ((e : ℤ) : ℝ) := by rw [Int.cast_natCast]; exact he1
  have hel : e < ℓ := by omega
  have hel2 : e < 2 ^ ℓ := lt_of_lt_of_le hel (Nat.lt_two_pow_self).le
  refine XV.mono (K := 1 + ((4 * e + 4) + (1 + (1 + (d * (2 + 6) + 3)))))
    (XV.seq (XV.rtoNat hL (i := 8) (x := oE + 1) (by omega) (by simp only [oE]; omega) he1' (by omega) hel2)
    fun σ1 e1 => ?_) (by omega) fun _ h => h
  subst e1
  refine XV.seq (XV.pow2A hL (p := sDmu) (i := 9) (n := 8) (one := rOne) (by bomega) (by omega) (by omega)
    (by bomega) (by decide) (by decide) (by simp) (by simp only [Env.setNat_nat]; rw [if_neg (by decide), h1])
    (by omega) hel) fun σ2 ⟨v2, d2, F2⟩ => ?_
  refine XV.seq (XV.sconst hL (x := sFirst) (by bomega) 0 rfl (by simp)) fun σ3 e3 => ?_
  subst e3
  have n2 : ∀ j, j ≠ 9 → j ≠ 8 → σ2.nat j = σ.nat j := fun j h h' => by
    rw [F2.1 j h, Env.setNat_nat, if_neg h']
  have s2 : ∀ y, y ≠ sDmu → σ2.sc y = σ.sc y := fun y h => by rw [F2.2.1 y h, Env.setNat_sc]
  have a2 : ∀ b k, σ2.arr b k = σ.arr b k := fun b k => by rw [F2.2.2.1 b k id, Env.setNat_arr]
  refine XV.mono (XV.copyN hL (z := sZ) (t := 128) (src := aWE) (dst := aMu) (nr := 10) (nk := 11) (nn := rD)
    (one := rOne) (E := E) (N := d) (x := vext x) (by bomega) (by omega)
    (by rw [Env.setSc_sc, if_neg (by decide), s2 _ (by decide), hz]) (by simp only [aWE]; omega) (by bomega)
    (by decide) (by omega) (by omega) (by bomega) (by bomega) (by decide)
    (by rw [Env.setSc_nat, n2 _ (by decide) (by decide), hD]) (by rw [Env.setSc_nat, n2 _ (by decide) (by decide), h1])
    (by unfold asz; omega) (fun k hk => ?_) (fun k hk => ?_) hE) le_rfl fun σ4 ⟨c4, d4, F4⟩ => ?_
  · rw [Env.setSc_arr, a2, vext_lt x hk]
    exact hxw ⟨k, hk⟩
  · rw [vext_lt x hk]; exact bx _
  refine ⟨?_, ?_, c4, ?_, ?_⟩
  · rw [F4.2.1 _ (by bomega), Env.setSc_sc, if_pos rfl]; simp
  · rw [F4.2.1 _ (by bomega), Env.setSc_sc, if_neg (by decide)]; exact v2
  · rw [d4, Env.setSc_draws, d2, Env.setNat_draws]
  · have G1 : FrameA (fun y => y = sFirst ∨ y = sDmu ∨ 128 ≤ y) (fun j => 8 ≤ j ∧ j ≤ 11)
        (fun b c => b = aMu ∧ c < d) σ (σ.setNat 8 e) := (FrameA.refl _ _ _ σ).setNat ⟨le_rfl, by omega⟩ _
    have G2 := F2.mono (S' := fun y => y = sFirst ∨ y = sDmu ∨ 128 ≤ y) (N' := fun j => 8 ≤ j ∧ j ≤ 11)
      (Ar' := fun b c => b = aMu ∧ c < d) (fun y h => Or.inr (Or.inl h)) (fun j h => by omega) (fun _ _ h => h.elim)
    have G4 := F4.mono (S' := fun y => y = sFirst ∨ y = sDmu ∨ 128 ≤ y) (N' := fun j => 8 ≤ j ∧ j ≤ 11)
      (Ar' := fun b c => b = aMu ∧ c < d) (fun y h => Or.inr (Or.inr h)) (fun j h => by omega) (fun _ _ h => h)
    exact ((G1.trans G2).setSc (Or.inl rfl) _).trans G4


/-- The cells `xcomArr` changes. -/
def SCom (y : ℕ) : Prop := y = sK ∨ y = sL ∨ 128 ≤ y
def NCom (j : ℕ) : Prop := 8 ≤ j ∧ j ≤ 12
def ACom (d b c : ℕ) : Prop := ((b = aA ∨ b = aB) ∧ c < d * d) ∨ ((b = ab ∨ b = aG) ∧ c < d)

theorem absZ_lt_two_pow {v : ℤ} {E ℓ : ℕ} (h : |v| ≤ 2 ^ E) (hE : E < ℓ) : |(v : ℝ)| < 2 ^ ℓ := by
  have h1 : |(v : ℝ)| ≤ 2 ^ E := by rw [← Int.cast_abs]; exact_mod_cast h
  exact h1.trans_lt (pow_lt_pow_right₀ (by norm_num) hE)

set_option maxHeartbeats 4000000 in
/-- The rule of `xcomArr`. -/
theorem XV.comArr {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L)
    {σ : Env d} {E : ℕ} {fA fB fb fG : ℕ → ℤ} {vk vl : ℤ} (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1)
    (hz : σ.sc sZ = 0) (hA : ∀ k < d * d, σ.arr 26 k = fA k) (hB : ∀ k < d * d, σ.arr 27 k = fB k)
    (hb : ∀ k < d, σ.arr 28 k = fb k) (hG : ∀ k < d, σ.arr 29 k = fG k)
    (bA : ∀ k < d * d, |fA k| ≤ 2 ^ E) (bB : ∀ k < d * d, |fB k| ≤ 2 ^ E)
    (bb : ∀ k < d, |fb k| ≤ 2 ^ E) (bG : ∀ k < d, |fG k| ≤ 2 ^ E)
    (hk : σ.sc 59 = vk) (hl : σ.sc 63 = vl) (bk : |vk| ≤ 2 ^ E) (bl : |vl| ≤ 2 ^ E)
    (hE : E < ℓ) (hdd : d * d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xcomArr L) σ (16 * (d * d) + 16 * d + 19) (fun σ' =>
      (∀ k < d * d, σ'.arr aA k = fA k) ∧ (∀ k < d * d, σ'.arr aB k = fB k) ∧
      (∀ k < d, σ'.arr ab k = fb k) ∧ (∀ k < d, σ'.arr aG k = fG k) ∧ σ'.sc sK = vk ∧ σ'.sc sL = vl ∧
      σ'.draws = σ.draws ∧ FrameA SCom NCom (ACom d) σ σ') := by
  obtain ⟨hS, hN, hAr⟩ := hlay
  simp only [oE, rEE, aWE] at hS hN hAr
  have hda := asz_lt hL (a := 0) (by omega)
  have hd0 : d < 2 ^ ℓa := lt_of_le_of_lt (by unfold asz; omega) hda
  have hNd : d * d ≤ asz d := by unfold asz; omega
  have hNd' : d ≤ asz d := by unfold asz; omega
  refine XV.mono (K := 1 + ((1 + (d * d * (2 + 6) + 3)) + ((1 + (d * d * (2 + 6) + 3)) +
      ((1 + (d * (2 + 6) + 3)) + ((1 + (d * (2 + 6) + 3)) + [(sK, 59), (sL, 63)].length)))))
    (XV.seq (XV.nmul hL (i := 12) (a := rD) (b := rD) (by omega) (by bomega) (by bomega) (by rw [hD]; exact hd0)
      (by rw [hD]; exact hd0) (by rw [hD]; exact hdd)) fun σ1 e1 => ?_) (by simp only [List.length]; omega)
    fun _ h => h
  subst e1
  have n1 : ∀ j, j ≠ 12 → (σ.setNat 12 (σ.nat rD * σ.nat rD)).nat j = σ.nat j := fun j h => by
    rw [Env.setNat_nat, if_neg h]
  have m1 : (σ.setNat 12 (σ.nat rD * σ.nat rD)).nat 12 = d * d := by rw [Env.setNat_nat, if_pos rfl, hD]
  -- `A'`
  refine XV.seq (XV.copyN hL (z := sZ) (t := 128) (src := 26) (dst := aA) (nr := 10) (nk := 11) (nn := 12)
    (one := rOne) (E := E) (N := d * d) (x := fA) (by bomega) (by omega) (by rw [Env.setNat_sc, hz]) (by omega)
    (by bomega) (by decide) (by omega) (by omega) (by omega) (by bomega) (by decide) m1
    (by rw [n1 _ (by decide), h1]) hNd (fun k hk => by rw [Env.setNat_arr, hA k hk]) bA hE)
    fun σ2 ⟨c2, d2, F2⟩ => ?_
  have n2 : ∀ j, j ≠ 10 → j ≠ 11 → σ2.nat j = (σ.setNat 12 (σ.nat rD * σ.nat rD)).nat j := fun j h h' =>
    F2.1 j fun e => e.elim h' h
  have s2 : ∀ y < 128, σ2.sc y = σ.sc y := fun y hy => by rw [F2.2.1 y (by omega), Env.setNat_sc]
  have a2 : ∀ b k, b ≠ aA → σ2.arr b k = σ.arr b k := fun b k h => by
    rw [F2.2.2.1 b k (fun e => h e.1), Env.setNat_arr]
  -- `B'`
  refine XV.seq (XV.copyN hL (z := sZ) (t := 128) (src := 27) (dst := aB) (nr := 10) (nk := 11) (nn := 12)
    (one := rOne) (E := E) (N := d * d) (x := fB) (by bomega) (by omega) (by rw [s2 _ (by bomega), hz]) (by omega)
    (by bomega) (by decide) (by omega) (by omega) (by omega) (by bomega) (by decide)
    (by rw [n2 _ (by decide) (by decide), m1]) (by rw [n2 _ (by decide) (by decide), n1 _ (by decide), h1]) hNd
    (fun k hk => by rw [a2 _ _ (by decide), hB k hk]) bB hE) fun σ3 ⟨c3, d3, F3⟩ => ?_
  have n3 : ∀ j, j ≠ 10 → j ≠ 11 → σ3.nat j = σ2.nat j := fun j h h' => F3.1 j fun e => e.elim h' h
  have s3 : ∀ y < 128, σ3.sc y = σ.sc y := fun y hy => by rw [F3.2.1 y (by omega), s2 y hy]
  have a3 : ∀ b k, b ≠ aA → b ≠ aB → σ3.arr b k = σ.arr b k := fun b k h h' => by
    rw [F3.2.2.1 b k (fun e => h' e.1), a2 b k h]
  -- `b'`
  refine XV.seq (XV.copyN hL (z := sZ) (t := 128) (src := 28) (dst := ab) (nr := 10) (nk := 11) (nn := rD)
    (one := rOne) (E := E) (N := d) (x := fb) (by bomega) (by omega) (by rw [s3 _ (by bomega), hz]) (by omega)
    (by bomega) (by decide) (by omega) (by omega) (by bomega) (by bomega) (by decide)
    (by rw [n3 _ (by decide) (by decide), n2 _ (by decide) (by decide), n1 _ (by decide), hD])
    (by rw [n3 _ (by decide) (by decide), n2 _ (by decide) (by decide), n1 _ (by decide), h1]) hNd'
    (fun k hk => by rw [a3 _ _ (by decide) (by decide), hb k hk]) bb hE) fun σ4 ⟨c4, d4, F4⟩ => ?_
  have n4 : ∀ j, j ≠ 10 → j ≠ 11 → σ4.nat j = σ2.nat j := fun j h h' => by
    rw [F4.1 j fun e => e.elim h' h, n3 j h h']
  have s4 : ∀ y < 128, σ4.sc y = σ.sc y := fun y hy => by rw [F4.2.1 y (by omega), s3 y hy]
  have a4 : ∀ b k, b ≠ aA → b ≠ aB → b ≠ ab → σ4.arr b k = σ.arr b k := fun b k h h' h'' => by
    rw [F4.2.2.1 b k (fun e => h'' e.1), a3 b k h h']
  -- `G'`
  refine XV.seq (XV.copyN hL (z := sZ) (t := 128) (src := 29) (dst := aG) (nr := 10) (nk := 11) (nn := rD)
    (one := rOne) (E := E) (N := d) (x := fG) (by bomega) (by omega) (by rw [s4 _ (by bomega), hz]) (by omega)
    (by bomega) (by decide) (by omega) (by omega) (by bomega) (by bomega) (by decide)
    (by rw [n4 _ (by decide) (by decide), n2 _ (by decide) (by decide), n1 _ (by decide), hD])
    (by rw [n4 _ (by decide) (by decide), n2 _ (by decide) (by decide), n1 _ (by decide), h1]) hNd'
    (fun k hk => by rw [a4 _ _ (by decide) (by decide) (by decide), hG k hk]) bG hE) fun σ5 ⟨c5, d5, F5⟩ => ?_
  have s5 : ∀ y < 128, σ5.sc y = σ.sc y := fun y hy => by rw [F5.2.1 y (by omega), s4 y hy]
  -- `k'`, `l'`
  have hp : ∀ p ∈ [(sK, 59), (sL, 63)], p.1 < L.NS ∧ p.2 < L.NS ∧ p.1 ≠ sZ ∧ |σ5.sc p.2| < 2 ^ ℓ := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨⟨by bomega, by omega, by decide, ?_⟩, ⟨by bomega, by omega, by decide, ?_⟩⟩
    · rw [s5 _ (by omega), hk]; exact absZ_lt_two_pow bk hE
    · rw [s5 _ (by omega), hl]; exact absZ_lt_two_pow bl hE
  refine XV.mono (XV.copyS hL (by bomega) [(sK, 59), (sL, 63)] σ5 (by rw [s5 _ (by bomega), hz]) hp (by decide)
    (by decide)) le_rfl fun σ6 ⟨c6, d6, F6⟩ => ?_
  have a6 : ∀ b k, σ6.arr b k = σ5.arr b k := fun b k => F6.2.2.1 b k id
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, ?_, ?_, ?_, ?_⟩
  · rw [a6, F5.2.2.1 _ _ (fun e => absurd e.1 (by decide)), F4.2.2.1 _ _ (fun e => absurd e.1 (by decide)),
      F3.2.2.1 _ _ (fun e => absurd e.1 (by decide)), c2 k hk]
  · rw [a6, F5.2.2.1 _ _ (fun e => absurd e.1 (by decide)), F4.2.2.1 _ _ (fun e => absurd e.1 (by decide)),
      c3 k hk]
  · rw [a6, F5.2.2.1 _ _ (fun e => absurd e.1 (by decide)), c4 k hk]
  · rw [a6, c5 k hk]
  · rw [c6 (sK, 59) (by simp), s5 _ (by omega), hk]
  · rw [c6 (sL, 63) (by simp), s5 _ (by omega), hl]
  · rw [d6, d5, d4, d3, d2, Env.setNat_draws]
  · have G1 : FrameA SCom NCom (ACom d) σ (σ.setNat 12 (σ.nat rD * σ.nat rD)) :=
      (FrameA.refl _ _ _ σ).setNat (show NCom 12 by simp only [NCom]; omega) _
    have G2 := F2.mono (S' := SCom) (N' := NCom) (Ar' := ACom d) (fun y h => Or.inr (Or.inr h))
      (fun j h => by simp only [NCom]; omega) (fun b c h => Or.inl ⟨Or.inl h.1, h.2⟩)
    have G3 := F3.mono (S' := SCom) (N' := NCom) (Ar' := ACom d) (fun y h => Or.inr (Or.inr h))
      (fun j h => by simp only [NCom]; omega) (fun b c h => Or.inl ⟨Or.inr h.1, h.2⟩)
    have G4 := F4.mono (S' := SCom) (N' := NCom) (Ar' := ACom d) (fun y h => Or.inr (Or.inr h))
      (fun j h => by simp only [NCom]; omega) (fun b c h => Or.inr ⟨Or.inl h.1, h.2⟩)
    have G5 := F5.mono (S' := SCom) (N' := NCom) (Ar' := ACom d) (fun y h => Or.inr (Or.inr h))
      (fun j h => by simp only [NCom]; omega) (fun b c h => Or.inr ⟨Or.inr h.1, h.2⟩)
    have G6 := F6.mono (S' := SCom) (N' := NCom) (Ar' := ACom d)
      (fun y h => by
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at h
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)) (fun _ h => h.elim) (fun _ _ h => h.elim)
    exact ((((G1.trans G2).trans G3).trans G4).trans G5).trans G6


theorem cell_lt (i j : Fin d) : d * (i : ℕ) + j < d * d := by
  have := i.2; have := j.2; nlinarith

theorem not_sCom {y : ℕ} (hy : y < 128) (h1 : y ≠ sK) (h2 : y ≠ sL) : ¬ SCom y := by
  rintro (h | h | h)
  exacts [h1 h, h2 h, by omega]

set_option maxHeartbeats 4000000 in
/-- **R15 COMMIT on the machine** (`CommitBL`, frozen in XBLEnd.lean). -/
theorem commitBL : CommitBL := by
  refine ⟨xcommit, 64, 2, ?_⟩
  intro d L X ℓa ℓ n m K0 E t cfg st Ap Bp bp Gp kp lp x e σ hd hL hlay hI hA hB hb hG h59 hk59 bk59 h63 hl63
    bl63 hout bx he hCl hCa
  have hsq : d * d + d + E + 1 ≤ (d + E + 1) ^ 2 := by
    have h2 : (d + E + 1) ^ 2 = d * d + (2 * d * E + E * E + 2 * d + 2 * E + 1) := by ring
    omega
  have hE : E < ℓ := by omega
  have hEa : E < 2 ^ ℓa := by omega
  have hdd : d * d < 2 ^ ℓa := by omega
  obtain ⟨r0, -, -, r3, -, -, -, -⟩ := hI.regs
  have c0 : σ.sc sZ = 0 := hI.consts.1
  have hE0 : (0 : ℤ) ≤ 2 ^ E := by positivity
  set MA : Matrix (Fin d) (Fin d) ℤ := fun i j => qn cfg.par.p (Ap i j) with hMA
  set MB : Matrix (Fin d) (Fin d) ℤ := fun i j => qn cfg.par.p (Bp i j) with hMB
  set vb : Fin d → ℤ := fun j => qn cfg.par.p (bp j) with hvb
  set vG : Fin d → ℤ := fun j => qn cfg.par.p (Gp j) with hvG
  refine XV.mono (K := (4 * E + d * 8 + 10) + (16 * (d * d) + 16 * d + 19))
    (XV.seq (XV.comMu hL hlay r0 r3 c0 hout bx he hE hEa) fun σ1 ⟨f1, m1, u1, d1, F1⟩ => ?_) (by omega)
    fun _ h => h
  have n1 : ∀ j < 8, σ1.nat j = σ.nat j := fun j hj => F1.1 j fun h => by omega
  have s1 : ∀ y < 128, y ≠ sFirst → y ≠ sDmu → σ1.sc y = σ.sc y := fun y hy h h' =>
    F1.2.1 y fun e => by rcases e with e | e | e <;> [exact h e; exact h' e; omega]
  have a1 : ∀ b k, b ≠ aMu → σ1.arr b k = σ.arr b k := fun b k h => F1.2.2.1 b k fun e => h e.1
  refine XV.mono (XV.comArr hL hlay (fA := mext MA) (fB := mext MB) (fb := vext vb) (fG := vext vG)
    (by rw [n1 _ (by decide), r0]) (by rw [n1 _ (by decide), r3]) (by rw [s1 _ (by decide) (by decide) (by decide), c0])
    (fun k hk => by rw [a1 _ _ (by decide)]; exact mext_eq (fun i j => (hA i j).1) hk)
    (fun k hk => by rw [a1 _ _ (by decide)]; exact mext_eq (fun i j => (hB i j).1) hk)
    (fun k hk => by rw [a1 _ _ (by decide), vext_lt _ hk]; exact (hb ⟨k, hk⟩).1)
    (fun k hk => by rw [a1 _ _ (by decide), vext_lt _ hk]; exact (hG ⟨k, hk⟩).1)
    (fun k _ => abs_mext_le (fun i j => (hA i j).2.2) hE0 k) (fun k _ => abs_mext_le (fun i j => (hB i j).2.2) hE0 k)
    (fun k _ => abs_vext_le (fun j => (hb j).2.2) hE0 k) (fun k _ => abs_vext_le (fun j => (hG j).2.2) hE0 k)
    (by rw [s1 _ (by decide) (by decide) (by decide), h59]) (by rw [s1 _ (by decide) (by decide) (by decide), h63])
    bk59 bl63 hE hdd) le_rfl fun σ2 ⟨cA, cB, cb, cG, sk, sl, d2, F2⟩ => ?_
  have s2 : ∀ y < 128, y ≠ sK → y ≠ sL → σ2.sc y = σ1.sc y := fun y hy h h' => F2.2.1 y (not_sCom hy h h')
  have a2 : ∀ b k, ¬ ACom d b k → σ2.arr b k = σ1.arr b k := fun b k h => F2.2.2.1 b k h
  have hF : FrameA SEnd NEnd AEnd σ σ2 := by
    refine (F1.mono (fun y h => ?_) (fun j h => h.1) (fun b c h => show aMu ≤ b by rw [h.1])).trans
      (F2.mono (fun y h => ?_) (fun j h => h.1) (fun b c h => ?_))
    · rcases h with h | h | h
      exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inr (Or.inr (by simp only [nSP]; omega))))]
    · rcases h with h | h | h
      exacts [Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr (Or.inl h))),
        Or.inr (Or.inr (Or.inr (Or.inr (by simp only [nSP]; omega))))]
    · show aMu ≤ b
      rcases h with ⟨h | h, -⟩ | ⟨h | h, -⟩ <;> subst h <;> decide
  have hst : StRep σ2 cfg.par.p ⟨false, fun j => (x j : ℚ) / 2 ^ e, Ap, Bp, bp, kp, Gp, lp⟩ := by
    refine ⟨?_, ⟨2 ^ e, by positivity, ?_, fun j => ⟨x j, ?_, by push_cast; rfl⟩⟩, fun i j => ⟨?_, (hA i j).2.1⟩,
      fun i j => ⟨?_, (hB i j).2.1⟩, fun j => ⟨?_, (hb j).2.1⟩, ⟨?_, hk59⟩, fun j => ⟨?_, (hG j).2.1⟩, ⟨?_, hl63⟩⟩
    · rw [s2 _ (by decide) (by decide) (by decide), f1]; simp
    · rw [s2 _ (by decide) (by decide) (by decide), m1]
    · rw [a2 _ _ (fun h => by rcases h with ⟨h | h, -⟩ | ⟨h | h, -⟩ <;> exact absurd h (by decide)), u1 j j.2,
        vext_lt x j.2]
    · rw [cA _ (cell_lt i j), mext_cell]
    · rw [cB _ (cell_lt i j), mext_cell]
    · rw [cb _ j.2, vext_lt _ j.2]
    · rw [sk]
    · rw [cG _ j.2, vext_lt _ j.2]
    · rw [sl]
  refine ⟨BLInv.setSt hI hF (by rw [d2, d1]) hst (fun y hy => ?_) (fun a ha k hk => ?_), by rw [d2, d1], hF⟩
  · simp only [nSP] at hy
    by_cases e1 : y = sFirst
    · subst e1
      exact Or.inr ⟨0, by rw [s2 _ (by decide) (by decide) (by decide), f1]; simp, by simp⟩
    by_cases e2 : y = sDmu
    · subst e2
      refine Or.inr ⟨2 ^ e, by rw [s2 _ (by decide) (by decide) (by decide), m1], ?_⟩
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_right₀ (by norm_num) he
    by_cases e3 : y = sK
    · subst e3; exact Or.inr ⟨_, sk, bk59⟩
    by_cases e4 : y = sL
    · subst e4; exact Or.inr ⟨_, sl, bl63⟩
    exact Or.inl (by rw [s2 y (by omega) e3 e4, s1 y (by omega) e1 e2])
  · simp only [nAP] at ha
    by_cases e1 : a = aMu ∧ k < d
    · obtain ⟨rfl, hk'⟩ := e1
      refine Or.inr ⟨vext x k, ?_, abs_vext_le bx hE0 k⟩
      rw [a2 _ _ (fun h => by rcases h with ⟨h | h, -⟩ | ⟨h | h, -⟩ <;> exact absurd h (by decide)), u1 k hk']
    by_cases e2 : a = aA ∧ k < d * d
    · obtain ⟨rfl, hk'⟩ := e2
      exact Or.inr ⟨_, cA k hk', abs_mext_le (fun i j => (hA i j).2.2) hE0 k⟩
    by_cases e3 : a = aB ∧ k < d * d
    · obtain ⟨rfl, hk'⟩ := e3
      exact Or.inr ⟨_, cB k hk', abs_mext_le (fun i j => (hB i j).2.2) hE0 k⟩
    by_cases e4 : a = ab ∧ k < d
    · obtain ⟨rfl, hk'⟩ := e4
      exact Or.inr ⟨_, cb k hk', abs_vext_le (fun j => (hb j).2.2) hE0 k⟩
    by_cases e5 : a = aG ∧ k < d
    · obtain ⟨rfl, hk'⟩ := e5
      exact Or.inr ⟨_, cG k hk', abs_vext_le (fun j => (hG j).2.2) hE0 k⟩
    refine Or.inl ?_
    have hna : ¬ ACom d a k := by
      rintro (⟨h | h, h'⟩ | ⟨h | h, h'⟩)
      exacts [e2 ⟨h, h'⟩, e3 ⟨h, h'⟩, e4 ⟨h, h'⟩, e5 ⟨h, h'⟩]
    rw [a2 a k hna, F1.2.2.1 a k e1]

end AdversarialBco.Bit.Transfer.BLM
