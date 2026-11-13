/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XGcd

@[expose] public section

/-!
# The row provider of BL, part 1: loops with tight frames

The loops of `XVec` (`foldE`, `dot`, `matvec`) change every slot from their scratch base on; the row provider runs
inside the projection routine, whose state lies in slots above the provider's own, so its loops must name the slots
they change.

* `xsdot`, `XV.sdot`: `r := ∑_{k < N} ax[base + st k] ay[k]` (a strided dot product: a column of a row-major matrix
  against a vector), changing `r`, `t1`, `t2` and the registers `nk`, `nr`;
* `xsqsum`, `XV.sqSum`: `f := ∑_{j < N} inp(c + 2 j)²` over input cells two apart.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach

variable {d : ℕ}

/-! ## The strided dot product -/

/-- `r := z + z; for nk < nn: t1 := ax[nr]; t2 := ay[nk]; t1 := t1 * t2; r := r + t1; nr := nr + nst`. -/
def xsdot (L : Layout) (z r t1 t2 ax ay nr nst nk nn none : ℕ) : XCmd :=
  .seq (toX (VL.sop2 L .add r z z)) (xforN nk nn none (.seq (toX (VL.aget L t1 ax nr))
    (.seq (toX (VL.aget L t2 ay nk)) (.seq (toX (VL.sop2 L .mul t1 t1 t2))
      (.seq (toX (VL.sop2 L .add r r t1)) (.prim (.frag (.nadd nr nr nst))))))))

/-- The units of `xsdot` over `N` turns. -/
def sdotUnits (N : ℕ) : ℕ := 1 + (N * (2 + (2 + (1 + (1 + 1))) + 3) + 3)

set_option maxHeartbeats 2000000 in
/-- **The strided dot product**: `r := ∑_{k < N} X k Y k` with `X k` in the cell `base + st k` of `ax` and `Y k` in
the cell `k` of `ay`; only `r`, `t1`, `t2`, `nk`, `nr` change. -/
theorem XV.sdot {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {z r t1 t2 ax ay nr nst nk nn none N base st E : ℕ} {Xv Yv : ℕ → ℤ}
    (hz : z < L.NS) (hr : r < L.NS) (ht1 : t1 < L.NS) (ht2 : t2 < L.NS) (hss : [z, r, t1, t2].Nodup)
    (hax : ax < L.NA) (hay : ay < L.NA) (hnr : nr < L.NN) (hnst : nst < L.NN) (hnk : nk < L.NN) (hnn : nn < L.NN)
    (hno : none < L.NN) (hne : [nr, nk, nn, none].Nodup) (hsr : nst ≠ nr) (hsk : nst ≠ nk)
    (hz0 : σ.sc z = 0) (hσn : σ.nat nn = N) (hσ1 : σ.nat none = 1) (hσr : σ.nat nr = base) (hσs : σ.nat nst = st)
    (hX : ∀ k < N, σ.arr ax (base + st * k) = Xv k) (hY : ∀ k < N, σ.arr ay k = Yv k)
    (hcx : ∀ k < N, base + st * k < asz d) (hcy : N ≤ asz d)
    (bX : ∀ k < N, |Xv k| ≤ 2 ^ E) (bY : ∀ k < N, |Yv k| ≤ 2 ^ E) (hE : 2 * E < ℓ) (hℓ : N * 2 ^ (2 * E) < 2 ^ ℓ)
    (hNa : N < 2 ^ ℓa) (hra : base + st * N < 2 ^ ℓa) (hsa : st < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xsdot L z r t1 t2 ax ay nr nst nk nn none) σ (sdotUnits N) (fun σ' =>
      σ'.sc r = ((∑ k ∈ Finset.range N, Xv k * Yv k : ℤ) : ℝ) ∧ σ'.nat nr = base + st * N ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => y = r ∨ y = t1 ∨ y = t2) (fun j => j = nk ∨ j = nr) (fun _ _ => False) σ σ') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne hss
  obtain ⟨⟨rk, rn, ro⟩, ⟨kn, ko⟩, -⟩ := hne
  obtain ⟨⟨zr, z1, z2⟩, ⟨r1, r2⟩, t12⟩ := hss
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by rw [abs_zero]; positivity
  have bXY : ∀ k < N, |Xv k * Yv k| ≤ ((2 ^ (2 * E) : ℕ) : ℤ) := fun k hk => by
    rw [abs_mul]; push_cast
    calc |Xv k| * |Yv k| ≤ 2 ^ E * 2 ^ E := mul_le_mul (bX k hk) (bY k hk) (abs_nonneg _) (by positivity)
      _ = 2 ^ (2 * E) := by ring
  have hsum : ∀ k ≤ N, |∑ j ∈ Finset.range k, Xv j * Yv j| < 2 ^ ℓ := fun k hk => by
    have h1 : |∑ j ∈ Finset.range k, Xv j * Yv j| ≤ k * ((2 ^ (2 * E) : ℕ) : ℤ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have := Finset.sum_le_card_nsmul (Finset.range k) (fun j => |Xv j * Yv j|) ((2 ^ (2 * E) : ℕ) : ℤ)
        (fun j hj => bXY j (by rw [Finset.mem_range] at hj; omega))
      simpa using this
    have h2 : (k : ℤ) * ((2 ^ (2 * E) : ℕ) : ℤ) ≤ N * 2 ^ (2 * E) := by
      push_cast; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (by positivity)
    have h3 : (N : ℤ) * 2 ^ (2 * E) < 2 ^ ℓ := by exact_mod_cast hℓ
    linarith
  have bE : ∀ k < N, |Xv k| < 2 ^ ℓ ∧ |Yv k| < 2 ^ ℓ ∧ |Xv k * Yv k| < 2 ^ ℓ := fun k hk => by
    have hp : (2 : ℤ) ^ E ≤ 2 ^ (2 * E) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hq : (2 : ℤ) ^ (2 * E) < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) hE
    have := bXY k hk
    push_cast at this
    exact ⟨by linarith [bX k hk], by linarith [bY k hk], by linarith⟩
  refine XV.seq (XV.sop2 hL (x := r) (a := z) (b := z) hr hz hz .add (by intro h; cases h) (by rw [hz0]; exact h0)
    (by rw [hz0]; exact h0) (by simp only [RealRAM.Op2.eval, hz0, add_zero]; exact h0)) fun σ0 e0 => ?_
  subst e0
  have hσ0 : (σ.setSc r (RealRAM.Op2.eval .add (σ.sc z) (σ.sc z))).nat = σ.nat := rfl
  refine XV.mono (XV.forN hL hnk hnn hno kn ko N (2 + (2 + (1 + (1 + 1)))) hNa
    (fun k σ' => σ'.nat nr = base + st * k ∧ σ'.draws = σ.draws ∧
      σ'.sc r = ((∑ j ∈ Finset.range k, Xv j * Yv j : ℤ) : ℝ) ∧
      FrameA (fun y => y = r ∨ y = t1 ∨ y = t2) (fun j => j = nk ∨ j = nr) (fun _ _ => False) σ σ')
    _ (by rw [hσ0, hσn]) (by rw [hσ0, hσ1]) ⟨by simp [rk, hσr], rfl, by simp [RealRAM.Op2.eval, hz0],
      ((FrameA.refl _ _ _ σ).setSc (Or.inl rfl) _).setNat (Or.inl rfl) 0⟩ ?_) le_rfl
    fun σ' ⟨⟨h1, h2, h3, h4⟩, _⟩ => ⟨h3, h1, h2, h4⟩
  intro k hk σ' ⟨hrk, hd, hs, hF⟩ hkt hkn hk1
  have hst' : σ'.nat nst = st := by rw [hF.1 nst (by omega), hσs]
  have eX : σ'.arr ax (σ'.nat nr) = Xv k := by rw [hrk, hF.2.2.1 ax _ id, hX k hk]
  have eY : σ'.arr ay (σ'.nat nk) = Yv k := by rw [hkt, hF.2.2.1 ay _ id, hY k hk]
  obtain ⟨bXk, bYk, bXYk⟩ := bE k hk
  refine XV.seq (XV.aget hL ht1 hax hnr (by rw [hrk]; exact hcx k hk) (by rw [eX]; exact XV.abs_int_lt bXk))
    fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.aget hL ht2 hay hnk (by rw [Env.setSc_nat, hkt]; omega)
    (by rw [Env.setSc_nat, Env.setSc_arr, eY]; exact XV.abs_int_lt bYk)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.mulI hL ht1 ht1 ht2 (u := Xv k) (v := Yv k) (by rpenv; exact eX)
    (by rpenv; exact eY) bXk bYk bXYk) fun σ3 e3 => ?_
  subst e3
  have hsk1 : ((∑ j ∈ Finset.range (k + 1), Xv j * Yv j : ℤ) : ℝ) =
      ((∑ j ∈ Finset.range k, Xv j * Yv j) + Xv k * Yv k : ℤ) := by rw [Finset.sum_range_succ]
  refine XV.seq (XV.addI hL hr hr ht1 (u := ∑ j ∈ Finset.range k, Xv j * Yv j) (v := Xv k * Yv k)
    (by rpenv; exact hs) (by rpenv) (hsum k hk.le) bXYk (by rw [← Finset.sum_range_succ]; exact hsum (k + 1) hk))
    fun σ4 e4 => ?_
  subst e4
  have hkN : base + st * k ≤ base + st * N := by have := Nat.mul_le_mul_left st hk.le; omega
  refine XV.mono (XV.nadd hL (i := nr) (a := nr) (b := nst) hnr hnr hnst
    (by rpenv; rw [hrk]; omega) (by rpenv; rw [hst']; exact hsa)) le_rfl fun σ5 e5 => ?_
  subst e5
  refine ⟨by rpenv; exact hkt, by rpenv; exact hkn, by rpenv; exact hk1, ?_, ?_, ?_, ?_⟩
  · rpenv; rw [hrk, hst']; ring
  · rpenv; exact hd
  · rpenv; rw [hsk1]
  · exact (((((hF.setSc (Or.inr (Or.inl rfl)) _).setSc (Or.inr (Or.inr rfl)) _).setSc (Or.inr (Or.inl rfl)) _).setSc
      (Or.inl rfl) _).setNat (Or.inr rfl) _).setNat (Or.inl rfl) _

/-! ## The sum of the squares of input cells -/

/-- `f := z + z; for nj < nn: t := inp(nI); t := t * t; f := f + t; nI := nI + none; nI := nI + none`. -/
def xsqsum (L : Layout) (z f t nj nI nn none : ℕ) : XCmd :=
  .seq (toX (VL.sop2 L .add f z z)) (xforN nj nn none (.seq (xrdIn L t nI) (.seq (toX (VL.sop2 L .mul t t t))
    (.seq (toX (VL.sop2 L .add f f t)) (.seq (.prim (.frag (.nadd nI nI none))) (.prim (.frag (.nadd nI nI none))))))))

/-- The units of `xsqsum` over `N` turns. -/
def sqUnits (N : ℕ) : ℕ := 1 + (N * (1 + (1 + (1 + (1 + 1))) + 3) + 3)

set_option maxHeartbeats 2000000 in
/-- **The sum of squares**: `f := ∑_{j < N} Nm j²` with `Nm j` the input cell `c + 2 j`; only `f`, `t`, `nj`, `nI`
change, and `nI` ends at `c + 2 N`. -/
theorem XV.sqSum {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {z f t nj nI nn none N c E : ℕ} {Nm : ℕ → ℤ}
    (hz : z < L.NS) (hf : f < L.NS) (ht : t < L.NS) (hss : [z, f, t].Nodup)
    (hnj : nj < L.NN) (hnI : nI < L.NN) (hnn : nn < L.NN) (hno : none < L.NN) (hne : [nj, nI, nn, none].Nodup)
    (hz0 : σ.sc z = 0) (hσI : σ.nat nI = c) (hσn : σ.nat nn = N) (hσ1 : σ.nat none = 1)
    (hidx : c + 2 * N ≤ X.off + 1) (hidxa : c + 2 * N < 2 ^ ℓa) (hinp : ∀ j < N, X.inp (c + 2 * j) = Nm j)
    (bN : ∀ j < N, |Nm j| ≤ 2 ^ E) (hE : 2 * E < ℓ) (hℓ : N * 2 ^ (2 * E) < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xsqsum L z f t nj nI nn none) σ (sqUnits N) (fun σ' =>
      σ'.sc f = ((∑ j ∈ Finset.range N, Nm j * Nm j : ℤ) : ℝ) ∧ σ'.nat nI = c + 2 * N ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = f ∨ y = t) (fun j => j = nj ∨ j = nI) (fun _ _ => False) σ σ') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne hss
  obtain ⟨⟨jI, jn, jo⟩, ⟨In, Io⟩, -⟩ := hne
  obtain ⟨⟨zf, zt⟩, ft⟩ := hss
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by rw [abs_zero]; positivity
  have hNa : N < 2 ^ ℓa := by omega
  have bsq : ∀ k < N, |Nm k * Nm k| ≤ ((2 ^ (2 * E) : ℕ) : ℤ) := fun k hk => by
    rw [abs_mul]; push_cast
    calc |Nm k| * |Nm k| ≤ 2 ^ E * 2 ^ E := mul_le_mul (bN k hk) (bN k hk) (abs_nonneg _) (by positivity)
      _ = 2 ^ (2 * E) := by ring
  have hsum : ∀ k ≤ N, |∑ j ∈ Finset.range k, Nm j * Nm j| < 2 ^ ℓ := fun k hk => by
    have h1 : |∑ j ∈ Finset.range k, Nm j * Nm j| ≤ k * ((2 ^ (2 * E) : ℕ) : ℤ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have := Finset.sum_le_card_nsmul (Finset.range k) (fun j => |Nm j * Nm j|) ((2 ^ (2 * E) : ℕ) : ℤ)
        (fun j hj => bsq j (by rw [Finset.mem_range] at hj; omega))
      simpa using this
    have h2 : (k : ℤ) * ((2 ^ (2 * E) : ℕ) : ℤ) ≤ N * 2 ^ (2 * E) := by
      push_cast; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (by positivity)
    have h3 : (N : ℤ) * 2 ^ (2 * E) < 2 ^ ℓ := by exact_mod_cast hℓ
    linarith
  have bE : ∀ k < N, |Nm k| < 2 ^ ℓ ∧ |Nm k * Nm k| < 2 ^ ℓ := fun k hk => by
    have hp : (2 : ℤ) ^ E ≤ 2 ^ (2 * E) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hq : (2 : ℤ) ^ (2 * E) < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) hE
    have := bsq k hk
    push_cast at this
    exact ⟨by linarith [bN k hk], by linarith⟩
  refine XV.seq (XV.sop2 hL (x := f) (a := z) (b := z) hf hz hz .add (by intro h; cases h) (by rw [hz0]; exact h0)
    (by rw [hz0]; exact h0) (by simp only [RealRAM.Op2.eval, hz0, add_zero]; exact h0)) fun σ0 e0 => ?_
  subst e0
  have hσ0 : (σ.setSc f (RealRAM.Op2.eval .add (σ.sc z) (σ.sc z))).nat = σ.nat := rfl
  refine XV.mono (XV.forN hL hnj hnn hno jn jo N (1 + (1 + (1 + (1 + 1)))) hNa
    (fun k σ' => σ'.nat nI = c + 2 * k ∧ σ'.draws = σ.draws ∧
      σ'.sc f = ((∑ j ∈ Finset.range k, Nm j * Nm j : ℤ) : ℝ) ∧
      FrameA (fun y => y = f ∨ y = t) (fun j => j = nj ∨ j = nI) (fun _ _ => False) σ σ')
    _ (by rw [hσ0, hσn]) (by rw [hσ0, hσ1]) ⟨by rpenv; omega, rfl, by simp [RealRAM.Op2.eval, hz0],
      ((FrameA.refl _ _ _ σ).setSc (Or.inl rfl) _).setNat (Or.inl rfl) 0⟩ ?_) le_rfl
    fun σ' ⟨⟨h1, h2, h3, h4⟩, _⟩ => ⟨h3, h1, h2, h4⟩
  intro k hk σ' ⟨hIk, hd, hs, hF⟩ hkt hkn hk1
  obtain ⟨bNk, bsqk⟩ := bE k hk
  refine XV.seq (XV.rdIn hL ht hnI (by rw [hIk]; omega) (by rw [hIk]; omega)
    (by rw [hIk, hinp k hk]; exact XV.abs_int_lt bNk)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.mulI hL ht ht ht (u := Nm k) (v := Nm k) (by rpenv; rw [hIk, hinp k hk])
    (by rpenv; rw [hIk, hinp k hk]) bNk bNk bsqk) fun σ2 e2 => ?_
  subst e2
  have hsk1 : ((∑ j ∈ Finset.range (k + 1), Nm j * Nm j : ℤ) : ℝ) =
      ((∑ j ∈ Finset.range k, Nm j * Nm j) + Nm k * Nm k : ℤ) := by rw [Finset.sum_range_succ]
  refine XV.seq (XV.addI hL hf hf ht (u := ∑ j ∈ Finset.range k, Nm j * Nm j) (v := Nm k * Nm k)
    (by rpenv; exact hs) (by rpenv) (hsum k hk.le) bsqk (by rw [← Finset.sum_range_succ]; exact hsum (k + 1) hk))
    fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.nadd hL (i := nI) (a := nI) (b := none) hnI hnI hno
    (by rpenv; rw [hIk]; omega) (by rpenv; rw [hk1]; have := hL.1; omega)) fun σ4 e4 => ?_
  subst e4
  refine XV.mono (XV.nadd hL (i := nI) (a := nI) (b := none) hnI hnI hno
    (by rpenv; rw [hIk]; omega) (by rpenv; rw [hk1]; have := hL.1; omega)) le_rfl fun σ5 e5 => ?_
  subst e5
  refine ⟨by rpenv; exact hkt, by rpenv; exact hkn, by rpenv; exact hk1, ?_, ?_, ?_, ?_⟩
  · rpenv; rw [hIk, hk1]; ring
  · rpenv; exact hd
  · rpenv; rw [hsk1]
  · exact ((((((hF.setSc (Or.inr rfl) _).setSc (Or.inr rfl) _).setSc (Or.inl rfl) _).setNat (Or.inr rfl) _).setNat
      (Or.inr rfl) _).setNat (Or.inl rfl) _)

end AdversarialBco.Bit.Transfer
