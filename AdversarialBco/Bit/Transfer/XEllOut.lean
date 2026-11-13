/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XEllSet

@[expose] public section

/-!
# The output of ELL-R and BIS-R, and the constants of BIS-R

`XV.ellOut` turns the outcome of a loop (`LoopOut`) into the output of the projection routine (`EllOut`): the found
point or the kept point copied into the array `aW` and `1` into the slot `o`, or `0` into `o`. `XV.bisSet` sets the
constants of BIS-R.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## Copying a point -/

/-- `dst[k] := src[k]` for `k < nat nn`; `nr` walks the cells, `nk` counts, `one` holds `1`; scratch from `t`. -/
def xcopyA (L : Layout) (z t src dst nr nk nn one : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst nr 0))) (xmapE L z t (.arr src nr) dst nr one nk nn one)

/-- A point `x` extended by `0` to the naturals. -/
def vextZ (x : Fin d → ℤ) (k : ℕ) : ℤ := if h : k < d then x ⟨k, h⟩ else 0

set_option maxHeartbeats 2000000 in
/-- The rule of `xcopyA`. -/
theorem XV.copyA {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {z t src dst nr nk nn one E : ℕ} {x : Fin d → ℤ} (hz : z < t) (hS : t + 1 ≤ L.NS) (hz0 : σ.sc z = 0)
    (hsrc : src < L.NA) (hdst : dst < L.NA) (hsd : src ≠ dst) (hnr : nr < L.NN) (hnk : nk < L.NN)
    (hnn : nn < L.NN) (hone : one < L.NN) (hne : [nr, nk, nn, one].Nodup) (hσn : σ.nat nn = d)
    (hσ1 : σ.nat one = 1) (hx : ∀ k : Fin d, σ.arr src k = x k) (bx : ∀ k, |x k| ≤ 2 ^ E) (hE : E < ℓ) :
    XRunsB L X ℓa ℓ (xcopyA L z t src dst nr nk nn one) σ (1 + (d * (2 + 6) + 3)) (fun σ' =>
      (∀ k : Fin d, σ'.arr dst k = x k) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => t ≤ y) (fun j => j = nk ∨ j = nr) (fun b _ => b = dst) σ σ') := by
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  have hda := asz_lt hL hdst
  unfold asz at hda
  have hdd : d ≤ d * d + d := by omega
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil, and_true]
    at hne
  obtain ⟨⟨rk, rn, ro⟩, ⟨kn, ko⟩, no⟩ := hne
  refine XV.seq (XV.nconstA hL (i := nr) hnr 0 (by positivity)) fun σ1 ⟨v1, d1, G1⟩ => ?_
  have e1 : ∀ j, j ≠ nr → σ1.nat j = σ.nat j := fun j h => G1.1 j h
  refine XV.mono (XV.mapE (E := E) (N := d) (base := 0) (st := 1) (F := vextZ x) hL (z := z) (t := t)
    (e := .arr src nr) (aB := dst) (nr := nr) (nst := one) (nk := nk) (nn := nn) (none := one)
    (by simp only [IE.WF]; omega) hz (by simp only [IE.scr]; omega) (by rw [G1.2.1 _ id, hz0]) hdst hnr hone
    hnk hnn hone (by simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]; omega) (Ne.symm ro) (Ne.symm ko)
    (by rw [e1 _ (Ne.symm rn), hσn]) (by rw [e1 _ (Ne.symm ro), hσ1]) v1 (by rw [e1 _ (Ne.symm ro), hσ1]) one_pos
    (fun k hk => by unfold asz; omega) (by omega) (by omega) hsa (by simp only [IE.top]; omega)
    (fun k hk σ' hF _ _ hr => ?_)) le_rfl fun σ2 ⟨z2, _, d2, F2⟩ => ?_
  · have ha : σ'.arr src k = ((vextZ x k : ℤ) : ℝ) := by
      rw [hF.2.2.1 _ _ (fun h => hsd h.1), G1.2.2.1 _ _ id]
      have := hx ⟨k, hk⟩
      simp only at this
      rw [this, vextZ, dif_pos hk]
    refine ⟨⟨by rw [hr]; unfold asz; omega, vextZ x k, by rw [hr, zero_add, one_mul, ha], ?_⟩,
      by simp only [IE.eval]; rw [hr, zero_add, one_mul, ha]⟩
    rw [vextZ, dif_pos hk]; exact bx _
  · refine ⟨fun k => ?_, by rw [d2, d1], ?_⟩
    · have := z2 k k.isLt
      rw [zero_add, one_mul] at this
      rw [this, vextZ, dif_pos k.isLt]
    · exact (G1.mono (fun _ h => h.elim) (fun j h => Or.inr h) (fun _ _ h => h.elim)).trans
        (F2.mono (fun y h => h) (fun j h => h) (fun b _ h => h.1))

/-! ## The output -/

/-- The output from the outcome of a loop: the found point (`2` in `P + 8`) from the array `a0 + 1`, else the kept
point (`1` in `P + 1`) from the array `a0 + 6`, into the array `aW` with `1` in the slot `o`; else `0` in `o`. -/
def xellOut (L : Layout) (B : EllBlk) (P u a0 n0 : ℕ) : XCmd :=
  xifS L (u + 1) (P + 8)
    (.seq (xcopyA L u (u + 13) (a0 + 1) B.aW (n0 + 11) (n0 + 13) B.rd (n0 + 4)) (toX (VL.sconst L B.o 1)))
    (xifS L u (P + 1)
      (.seq (xcopyA L u (u + 13) (a0 + 6) B.aW (n0 + 11) (n0 + 13) B.rd (n0 + 4)) (toX (VL.sconst L B.o 1)))
      (xset L B.o u u))

set_option maxHeartbeats 4000000 in
/-- The rule of `xellOut`. -/
theorem XV.ellOut {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk}
    {P u a0 n0 F e : ℕ} {capa : ℤ} {r : Option (Fin d → ℤ)} (hP : B.o + 3 ≤ P) (hPu : P + 9 ≤ u)
    (hS : u + 14 ≤ L.NS) (hwa : B.aW + 2 ≤ a0) (hA : a0 + 7 ≤ L.NA) (hrd : B.rd < n0) (hN : n0 + 14 ≤ L.NN)
    (hdv : σ.nat B.rd = d) (hone : σ.nat (n0 + 4) = 1) (hz : σ.sc u = 0) (h1 : σ.sc (u + 1) = 1)
    (he : σ.sc (B.o + 1) = e) (hout : LoopOut P a0 (a0 + 6) capa F r σ) (bca : capa ≤ 2 ^ F) (hF : F + 2 < ℓ) :
    XRunsB L X ℓa ℓ (xellOut L B P u a0 n0) σ (8 * d + 8) (fun σ' =>
      EllOut B r e σ' ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = B.o ∨ u + 13 ≤ y) (fun j => j = n0 + 11 ∨ j = n0 + 13) (fun b _ => b = B.aW) σ σ') := by
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by simp only [abs_zero]; positivity
  have h1' : |(1 : ℝ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  have h2' : |(2 : ℝ)| < 2 ^ ℓ := by
    rw [abs_two]
    have := pow_lt_pow_right₀ (show (1 : ℝ) < 2 by norm_num) (show 1 < ℓ by omega)
    simpa using this
  have hne : [n0 + 11, n0 + 13, B.rd, n0 + 4].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil, and_true,
      not_false_eq_true]; omega
  have b1 : |((1 : ℚ) : ℝ)| < 2 ^ ℓ := by rw [Rat.cast_one]; exact h1'
  -- the end of a copy: `1` into `o`
  have fin : ∀ (σ' : Env d) (x : Fin d → ℤ), (∀ k : Fin d, σ'.arr B.aW k = x k) → σ'.draws = σ.draws →
      FrameA (fun y => u + 13 ≤ y) (fun j => j = n0 + 13 ∨ j = n0 + 11) (fun b _ => b = B.aW) σ σ' →
      XRunsB L X ℓa ℓ (toX (VL.sconst L B.o 1)) σ' 1 (fun σ'' =>
        EllOut B (some x) e σ'' ∧ σ''.draws = σ.draws ∧
        FrameA (fun y => y = B.o ∨ u + 13 ≤ y) (fun j => j = n0 + 11 ∨ j = n0 + 13) (fun b _ => b = B.aW) σ σ'') :=
    fun σ' x hx hd hF => by
      refine XV.mono (XV.sconst hL (x := B.o) (by omega) 1 rfl b1) le_rfl fun σ'' e'' => ?_
      subst e''
      refine ⟨⟨by simp, by simp [show B.o + 1 ≠ B.o by omega]; rw [hF.2.1 _ (by omega), he], fun k => by
        simp [hx k]⟩, by simp [hd], ?_⟩
      exact (hF.mono (S' := fun y => y = B.o ∨ u + 13 ≤ y) (N' := fun j => j = n0 + 11 ∨ j = n0 + 13)
        (fun y h => Or.inr h) (fun j h => by omega) (fun b _ h => h)).setSc (Or.inl rfl) _
  rcases hout with ⟨h8, x, hr, hx, bx⟩ | ⟨h8, kept, bK, hK, hr⟩
  · -- a found point
    subst hr
    refine XV.mono (XV.ifS_t (K := (1 + (d * (2 + 6) + 3)) + 1) hL (by omega) (by omega) (by rw [h1]; exact h1')
      (by rw [h8]; exact h2') (by rw [h1, h8]; norm_num) ?_) (by ring_nf; omega) (fun _ h => h)
    refine XV.seq (XV.copyA (E := F) hL (z := u) (t := u + 13) (src := a0 + 1) (dst := B.aW) (nr := n0 + 11)
      (nk := n0 + 13) (nn := B.rd) (one := n0 + 4) (by omega) (by omega) hz (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) hne hdv hone hx (fun k => (bx k).trans bca) (by omega))
      fun σ1 ⟨x1, d1, F1⟩ => ?_
    exact fin σ1 x x1 d1 (F1.mono (fun y h => h) (fun j h => by omega) (fun b _ h => h))
  · have h8' : ¬ σ.sc (u + 1) < σ.sc (P + 8) := by
      rw [h1]; rcases h8 with h | h <;> rw [h] <;> norm_num
    have b8 : |σ.sc (P + 8)| < 2 ^ ℓ := by rcases h8 with h | h <;> rw [h] <;> assumption
    subst hr
    rcases kept with _ | ⟨b, W⟩
    · -- no point
      have hK' : σ.sc (P + 1) = 0 := hK
      refine XV.mono (XV.ifS_f (K := 1 + 2) hL (by omega) (by omega) (by rw [h1]; exact h1') b8 h8'
        (XV.ifS_f hL (by omega) (by omega) (by rw [hz]; exact h0) (by rw [hK']; exact h0)
          (by rw [hz, hK']; exact lt_irrefl 0) (XV.setZ hL (x := B.o) (z := u) (by omega) (by omega) hz)))
        (by omega) fun σ1 ⟨v1, d1, G1⟩ => ⟨v1, d1, G1.mono (fun y h => Or.inl h) (fun _ h => h.elim)
          (fun _ _ h => h.elim)⟩
    · -- the kept point
      obtain ⟨hK1, hKb, -⟩ := hK
      have bb := (bK b W rfl).1
      refine XV.mono (XV.ifS_f (K := ((1 + (d * (2 + 6) + 3)) + 1) + 1) hL (by omega) (by omega)
        (by rw [h1]; exact h1') b8 h8' (XV.ifS_t hL (by omega) (by omega) (by rw [hz]; exact h0)
          (by rw [hK1]; exact h1') (by rw [hz, hK1]; norm_num) ?_)) (by ring_nf; omega) (fun _ h => h)
      refine XV.seq (XV.copyA (E := F) hL (z := u) (t := u + 13) (src := a0 + 6) (dst := B.aW) (nr := n0 + 11)
        (nk := n0 + 13) (nn := B.rd) (one := n0 + 4) (by omega) (by omega) hz (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) hne hdv hone hKb (fun k => (bb k).trans bca) (by omega))
        fun σ1 ⟨x1, d1, F1⟩ => ?_
      exact fin σ1 b x1 d1 (F1.mono (fun y h => h) (fun j h => by omega) (fun b _ h => h))


/-! ## The constants of BIS-R -/

/-- BIS-R's constants (`d = 1`): `s = λ + 1` into the register `n0 + 7` (the number of halvings) and the slot `o + 1`
(the exponent); `2^s, 2^{s+1}, 2^{2s}, 2^{2s+1}` into `P + 3, ..., P + 6`; `2` into `u + 2`; the interval
`[-R̄ 2^s, R̄ 2^s]` into `P + 9, P + 10`; no kept point (`0` in `P + 1`). -/
def xbisSet (L : Layout) (B : EllBlk) (P u c n0 : ℕ) : XCmd :=
  .seq (.prim (.frag (.nadd (n0 + 7) (n0 + 10) (n0 + 4))))
  (.seq (toX (VL.ncast L (B.o + 1) (n0 + 7)))
  (.seq (.prim (.frag (.nadd (n0 + 14) (n0 + 7) (n0 + 7))))
  (.seq (.prim (.frag (.nadd (n0 + 15) (n0 + 14) (n0 + 4))))
  (.seq (.prim (.frag (.nadd (n0 + 16) (n0 + 7) (n0 + 4))))
  (.seq (xpow2 L (P + 3) (n0 + 17) (n0 + 7) (n0 + 4))
  (.seq (xpow2 L (P + 4) (n0 + 17) (n0 + 16) (n0 + 4))
  (.seq (xpow2 L (P + 5) (n0 + 17) (n0 + 14) (n0 + 4))
  (.seq (xpow2 L (P + 6) (n0 + 17) (n0 + 15) (n0 + 4))
  (.seq (toX (VL.sconst L (u + 2) 2))
  (.seq (toX (VL.sop2 L .mul (P + 10) c (P + 3)))
  (.seq (toX (VL.sop2 L .sub (P + 9) u (P + 10)))
    (xset L (P + 1) u u))))))))))))

/-- The slots `xbisSet` writes. -/
abbrev bisSetS (B : EllBlk) (P u : ℕ) (y : ℕ) : Prop :=
  y = B.o + 1 ∨ y = P + 1 ∨ (P + 3 ≤ y ∧ y ≤ P + 6) ∨ y = P + 9 ∨ y = P + 10 ∨ y = u + 2

set_option maxHeartbeats 4000000 in
/-- The rule of `xbisSet`. -/
theorem XV.bisSet {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk}
    {P u c n0 lam E : ℕ} {Rb : ℤ} (hP : B.o + 3 ≤ P) (hPu : P + 12 ≤ u) (hc : u + 13 ≤ c) (hS : c + 1 ≤ L.NS)
    (hN : n0 + 18 ≤ L.NN) (hz : σ.sc u = 0) (hl : σ.nat (n0 + 10) = lam) (h1 : σ.nat (n0 + 4) = 1)
    (hR : σ.sc c = Rb) (hR0 : 0 ≤ Rb) (bR : Rb ≤ 2 ^ E) (hla : 2 * lam + 3 < 2 ^ ℓa) (hlℓ : E + 2 * lam + 4 < ℓ) :
    XRunsB L X ℓa ℓ (xbisSet L B P u c n0) σ (24 * lam + 57) (fun σ' =>
      σ'.nat (n0 + 7) = lam + 1 ∧ σ'.sc (B.o + 1) = ((lam + 1 : ℕ) : ℝ) ∧
      σ'.sc (P + 3) = ((2 ^ (lam + 1) : ℤ) : ℝ) ∧ σ'.sc (P + 4) = ((2 ^ (lam + 1 + 1) : ℤ) : ℝ) ∧
      σ'.sc (P + 5) = ((2 ^ (2 * (lam + 1)) : ℤ) : ℝ) ∧ σ'.sc (P + 6) = ((2 ^ (2 * (lam + 1) + 1) : ℤ) : ℝ) ∧
      σ'.sc (u + 2) = 2 ∧ σ'.sc (P + 9) = ((-(Rb * 2 ^ (lam + 1)) : ℤ) : ℝ) ∧
      σ'.sc (P + 10) = ((Rb * 2 ^ (lam + 1) : ℤ) : ℝ) ∧ σ'.sc (P + 1) = 0 ∧ σ'.draws = σ.draws ∧
      FrameA (bisSetS B P u) (fun j => j = n0 + 7 ∨ (n0 + 14 ≤ j ∧ j ≤ n0 + 17)) (fun _ _ => False) σ σ') := by
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  refine XV.mono (K := 1 + (1 + (1 + (1 + (1 + ((4 * (lam + 1) + 4) + ((4 * (lam + 1 + 1) + 4) +
    ((4 * (2 * (lam + 1)) + 4) + ((4 * (2 * (lam + 1) + 1) + 4) + (1 + (1 + (1 + 1)))))))))))) ?_ (by ring_nf; omega)
    (fun _ h => h)
  refine XV.seq (XV.nadd hL (i := n0 + 7) (a := n0 + 10) (b := n0 + 4) (by omega) (by omega) (by omega)
    (by rw [hl]; omega) (by rw [h1]; omega)) fun σ1 e1 => ?_
  have n1 : σ1.nat (n0 + 7) = lam + 1 := by rw [e1]; simp [hl, h1]
  have o1 : σ1.nat (n0 + 4) = 1 := by rw [e1]; simp [h1]
  refine XV.seq (XV.ncastI hL (x := B.o + 1) (i := n0 + 7) (by omega) (by omega) (by rw [n1]; omega))
    fun σ2 e2 => ?_
  have n2 : σ2.nat (n0 + 7) = lam + 1 := by rw [e2]; simp [n1]
  have o2 : σ2.nat (n0 + 4) = 1 := by rw [e2]; simp [o1]
  refine XV.seq (XV.nadd hL (i := n0 + 14) (a := n0 + 7) (b := n0 + 7) (by omega) (by omega) (by omega)
    (by rw [n2]; omega) (by rw [n2]; omega)) fun σ3 e3 => ?_
  have n3 : σ3.nat (n0 + 7) = lam + 1 := by rw [e3]; simp [n2]
  have m3 : σ3.nat (n0 + 14) = 2 * (lam + 1) := by rw [e3]; simp [n2]; ring
  have o3 : σ3.nat (n0 + 4) = 1 := by rw [e3]; simp [o2]
  refine XV.seq (XV.nadd hL (i := n0 + 15) (a := n0 + 14) (b := n0 + 4) (by omega) (by omega) (by omega)
    (by rw [m3]; omega) (by rw [o3]; omega)) fun σ4 e4 => ?_
  have n4 : σ4.nat (n0 + 7) = lam + 1 := by rw [e4]; simp [n3]
  have m4 : σ4.nat (n0 + 14) = 2 * (lam + 1) := by rw [e4]; simp [m3]
  have p4 : σ4.nat (n0 + 15) = 2 * (lam + 1) + 1 := by rw [e4]; simp [m3, o3]
  have o4 : σ4.nat (n0 + 4) = 1 := by rw [e4]; simp [o3]
  refine XV.seq (XV.nadd hL (i := n0 + 16) (a := n0 + 7) (b := n0 + 4) (by omega) (by omega) (by omega)
    (by rw [n4]; omega) (by rw [o4]; omega)) fun σ5 e5 => ?_
  have n5 : σ5.nat (n0 + 7) = lam + 1 := by rw [e5]; simp [n4]
  have m5 : σ5.nat (n0 + 14) = 2 * (lam + 1) := by rw [e5]; simp [m4]
  have p5 : σ5.nat (n0 + 15) = 2 * (lam + 1) + 1 := by rw [e5]; simp [p4]
  have q5 : σ5.nat (n0 + 16) = lam + 1 + 1 := by rw [e5]; simp [n4, o4]
  have o5 : σ5.nat (n0 + 4) = 1 := by rw [e5]; simp [o4]
  have z5 : σ5.sc u = 0 := by rw [e5, e4, e3, e2, e1]; simp [show u ≠ B.o + 1 by omega, hz]
  have c5 : σ5.sc c = Rb := by rw [e5, e4, e3, e2, e1]; simp [show c ≠ B.o + 1 by omega, hR]
  have x5 : σ5.sc (B.o + 1) = ((lam + 1 : ℕ) : ℝ) := by rw [e5, e4, e3, e2]; simp [n1]
  have d5 : σ5.draws = σ.draws := by rw [e5, e4, e3, e2, e1]; simp
  have G5 : FrameA (bisSetS B P u) (fun j => j = n0 + 7 ∨ (n0 + 14 ≤ j ∧ j ≤ n0 + 17)) (fun _ _ => False) σ σ5 := by
    rw [e5, e4, e3, e2, e1]
    exact (((((FrameA.refl _ _ _ σ).setNat (Or.inl rfl) _).setSc (Or.inl rfl) _).setNat
      (Or.inr ⟨le_rfl, by omega⟩) _).setNat (Or.inr ⟨by omega, by omega⟩) _).setNat (Or.inr ⟨by omega, by omega⟩) _
  -- the scales
  refine XV.seq (XV.pow2A hL (p := P + 3) (i := n0 + 17) (n := n0 + 7) (one := n0 + 4) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) n5 o5 (by omega) (by omega)) fun σ6 ⟨s6, d6, G6⟩ => ?_
  have e6 : ∀ j, j ≠ n0 + 17 → σ6.nat j = σ5.nat j := fun j h => G6.1 j h
  refine XV.seq (XV.pow2A hL (p := P + 4) (i := n0 + 17) (n := n0 + 16) (one := n0 + 4) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by rw [e6 _ (by omega), q5]) (by rw [e6 _ (by omega), o5])
    (by omega) (by omega)) fun σ7 ⟨s7, d7, G7⟩ => ?_
  have e7 : ∀ j, j ≠ n0 + 17 → σ7.nat j = σ5.nat j := fun j h => (G7.1 j h).trans (e6 j h)
  refine XV.seq (XV.pow2A hL (p := P + 5) (i := n0 + 17) (n := n0 + 14) (one := n0 + 4) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by rw [e7 _ (by omega), m5]) (by rw [e7 _ (by omega), o5])
    (by omega) (by omega)) fun σ8 ⟨s8, d8, G8⟩ => ?_
  have e8 : ∀ j, j ≠ n0 + 17 → σ8.nat j = σ5.nat j := fun j h => (G8.1 j h).trans (e7 j h)
  refine XV.seq (XV.pow2A hL (p := P + 6) (i := n0 + 17) (n := n0 + 15) (one := n0 + 4) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by rw [e8 _ (by omega), p5]) (by rw [e8 _ (by omega), o5])
    (by omega) (by omega)) fun σ9 ⟨s9, d9, G9⟩ => ?_
  have G59 : FrameA (bisSetS B P u) (fun j => j = n0 + 7 ∨ (n0 + 14 ≤ j ∧ j ≤ n0 + 17)) (fun _ _ => False) σ5 σ9 :=
    (((G6.mono (fun y h => by simp only [bisSetS]; omega) (fun j h => Or.inr ⟨by omega, by omega⟩) (fun _ _ h => h)).trans
      (G7.mono (fun y h => by simp only [bisSetS]; omega) (fun j h => Or.inr ⟨by omega, by omega⟩)
        (fun _ _ h => h))).trans
      (G8.mono (fun y h => by simp only [bisSetS]; omega) (fun j h => Or.inr ⟨by omega, by omega⟩)
        (fun _ _ h => h))).trans
      (G9.mono (fun y h => by simp only [bisSetS]; omega) (fun j h => Or.inr ⟨by omega, by omega⟩) (fun _ _ h => h))
  have sc9 : ∀ y, ¬ (P + 3 ≤ y ∧ y ≤ P + 6) → σ9.sc y = σ5.sc y := fun y hy => by
    rw [G9.2.1 _ (by omega), G8.2.1 _ (by omega), G7.2.1 _ (by omega), G6.2.1 _ (by omega)]
  have t3 : σ9.sc (P + 3) = ((2 ^ (lam + 1) : ℤ) : ℝ) := by
    rw [G9.2.1 _ (by omega), G8.2.1 _ (by omega), G7.2.1 _ (by omega), s6]
  have t4 : σ9.sc (P + 4) = ((2 ^ (lam + 1 + 1) : ℤ) : ℝ) := by
    rw [G9.2.1 _ (by omega), G8.2.1 _ (by omega), s7]
  have t5 : σ9.sc (P + 5) = ((2 ^ (2 * (lam + 1)) : ℤ) : ℝ) := by rw [G9.2.1 _ (by omega), s8]
  have z9 : σ9.sc u = 0 := by rw [sc9 _ (by omega), z5]
  have c9 : σ9.sc c = Rb := by rw [sc9 _ (by omega), c5]
  have x9 : σ9.sc (B.o + 1) = ((lam + 1 : ℕ) : ℝ) := by rw [sc9 _ (by omega), x5]
  have n9 : σ9.nat (n0 + 7) = lam + 1 := by rw [G9.1 _ (by omega), e8 _ (by omega), n5]
  have dd9 : σ9.draws = σ.draws := by rw [d9, d8, d7, d6, d5]
  -- `2`, the interval, no kept point
  have bM : |Rb * 2 ^ (lam + 1)| ≤ 2 ^ (E + (lam + 1)) := by
    rw [abs_mul, abs_of_nonneg hR0, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ (lam + 1)), pow_add (2 : ℤ) E (lam + 1)]
    exact mul_le_mul_of_nonneg_right bR (by positivity)
  have bMl : |Rb * 2 ^ (lam + 1)| < 2 ^ ℓ := bM.trans_lt (pow_lt_pow_right₀ (by norm_num) (by omega))
  have bMn : |0 - Rb * 2 ^ (lam + 1)| < 2 ^ ℓ := by rw [zero_sub, abs_neg]; exact bMl
  have bRl : |Rb| < 2 ^ ℓ := by
    rw [abs_of_nonneg hR0]; exact bR.trans_lt (pow_lt_pow_right₀ (by norm_num) (by omega))
  have b2l : |(2 : ℤ) ^ (lam + 1)| < 2 ^ ℓ := by
    rw [abs_of_pos (by positivity)]; exact pow_lt_pow_right₀ (by norm_num) (by omega)
  have b0l : |(0 : ℤ)| < 2 ^ ℓ := by simp
  refine XV.seq (XV.sconstA hL (x := u + 2) (by omega) 2 (small_lt (by norm_num) (by omega)))
    fun σ10 ⟨v10, d10, G10⟩ => ?_
  have e10 : ∀ y, y ≠ u + 2 → σ10.sc y = σ9.sc y := fun y h => G10.2.1 y h
  refine XV.seq (XV.mulI hL (x := P + 10) (a := c) (b := P + 3) (u := Rb) (v := 2 ^ (lam + 1)) (by omega)
    (by omega) (by omega) (by rw [e10 _ (by omega), c9]) (by rw [e10 _ (by omega), t3]) bRl b2l bMl)
    fun σ11 e11 => ?_
  subst e11
  refine XV.seq (XV.subI hL (x := P + 9) (a := u) (b := P + 10) (u := 0) (v := Rb * 2 ^ (lam + 1)) (by omega)
    (by omega) (by omega)
    (by simp only [Env.setSc_sc, show u ≠ P + 10 by omega, ite_false]; rw [e10 _ (by omega), z9, Int.cast_zero])
    (by simp only [Env.setSc_sc, ite_true]) b0l bMl bMn) fun σ12 e12 => ?_
  subst e12
  refine XV.mono (XV.setZ hL (x := P + 1) (z := u) (by omega) (by omega) (by
    simp only [Env.setSc_sc, show u ≠ P + 10 by omega, show u ≠ P + 9 by omega, ite_false]
    rw [e10 _ (by omega), z9])) le_rfl fun σ13 ⟨v13, d13, G13⟩ => ?_
  have sc13 : ∀ y, y ≠ u + 2 → y ≠ P + 10 → y ≠ P + 9 → y ≠ P + 1 → σ13.sc y = σ9.sc y :=
    fun y h1 h2 h3 h4 => by
      rw [G13.2.1 y h4]; simp only [Env.setSc_sc, h2, h3, ite_false]; exact e10 y h1
  have nat13 : ∀ j, σ13.nat j = σ9.nat j := fun j => by
    rw [G13.1 j id]; simp only [Env.setSc_nat]; exact G10.1 j id
  refine ⟨by rw [nat13, n9], by rw [sc13 _ (by omega) (by omega) (by omega) (by omega), x9],
    by rw [sc13 _ (by omega) (by omega) (by omega) (by omega), t3],
    by rw [sc13 _ (by omega) (by omega) (by omega) (by omega), t4],
    by rw [sc13 _ (by omega) (by omega) (by omega) (by omega), t5],
    by rw [sc13 _ (by omega) (by omega) (by omega) (by omega)]; exact s9,
    by rw [G13.2.1 _ (by omega)]; simp only [Env.setSc_sc, show u + 2 ≠ P + 9 by omega,
      show u + 2 ≠ P + 10 by omega, ite_false]; rw [v10]; norm_num,
    by rw [G13.2.1 _ (by omega)]; simp only [Env.setSc_sc, ite_true]; push_cast; ring,
    by rw [G13.2.1 _ (by omega)]; simp only [Env.setSc_sc, show P + 10 ≠ P + 9 by omega, ite_false, ite_true],
    v13, by rw [d13]; exact d10.trans dd9, ?_⟩
  have G10' := (G5.trans G59).trans (G10.mono (fun y h => by simp only [bisSetS]; omega) (fun _ h => h.elim)
    (fun _ _ h => h))
  have h10 : bisSetS B P u (P + 10) := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h9 : bisSetS B P u (P + 9) := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  exact ((G10'.setSc (x := P + 10) h10 _).setSc (x := P + 9) h9 _).trans
    (G13.mono (fun y h => by simp only [bisSetS]; omega) (fun _ h => h.elim) (fun _ _ h => h))

end AdversarialBco.Bit.Transfer
