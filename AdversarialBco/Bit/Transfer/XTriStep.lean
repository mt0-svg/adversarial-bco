/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriScanLoop

@[expose] public section

/-!
# TRI-M, one draw of the core on the machine

The block layout of `xtri`: slots from `o` (`o`: the stage denominator, `o + 1, ..., o + 15` constants, `o + 16, ...,
o + 34` the work of a draw, `o + 35, ..., o + 39` the stage, scratch from `o + 40`), registers from `r` (`r`: `1`,
`r + 1`: `d + 1`, `r + 2`: `m + 2d`, `r + 3, ..., r + 10` the work of a draw), arrays from `a` (`a`, `a + 1`: the stage
`μ̂`, `T̂`; `a + 2`, `a + 3`: the iterate `X̂`; `a + 6`: the draw `Y`; `a + 7, ..., a + 11`: `ẑ`, `ŵ`, the row, the kept
row, `A`). One draw (`xstep1`): `ẑ = X̂_μ 2^{2p} + X̂_T Y`, `ŵ = T̂ ẑ`, the scan of the rows, `A = T̂ᵀ row`, the update:
`X̂ := tzStep1 c T̂ μ̂ ra rb M X̂ Y`.
-/

open AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.Transfer AdversarialBco.Bit.TriM Matrix

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach

variable {d : ℕ}

/-- The slots a draw may change. -/
abbrev stS (o : ℕ) (y : ℕ) : Prop := o + 16 ≤ y ∧ y < o + 35 ∨ o + 40 ≤ y

/-- The registers a draw may change. -/
abbrev stN (r : ℕ) (j : ℕ) : Prop := r + 3 ≤ j ∧ j < r + 11

/-- The cells a draw may change. -/
abbrev stA (d a : ℕ) (b k : ℕ) : Prop := b = a + 2 ∧ k < d ∨ b = a + 3 ∧ k < d * d ∨ a + 7 ≤ b ∧ b < a + 12 ∧ k < d

/-- The slots the row command may change (those of `xrowK` at the layout). -/
abbrev rwS (o : ℕ) (y : ℕ) : Prop :=
  y = o + 29 ∨ y = o + 30 ∨ y = o + 31 ∨ y = o + 32 ∨ y = o + 19 ∨ y = o + 33

/-- The registers the row command may change. -/
abbrev rwN (r : ℕ) (j : ℕ) : Prop := j = r + 8 ∨ j = r + 9 ∨ j = r + 10 ∨ j = r + 7 ∨ j = r + 6

/-- `ẑ_i := X̂_μ,i 2^{2p} + ẑ_i`. -/
def ieZ (aXm aZ sP2 nr : ℕ) : IE := .op .add (.op .mul (.arr aXm nr) (.sc sP2)) (.arr aZ nr)

/-- One draw of the core at the layout. -/
def xstep1 (L : Layout) (row : XCmd) (o r a nd : ℕ) : XCmd :=
  .seq (xmatvec L (o + 1) (o + 20) (o + 40) (a + 3) (a + 6) (a + 7) (r + 7) (r + 4) (r + 5) nd r)
  (.seq (.prim (.frag (.nconst (r + 4) 0)))
  (.seq (xmapE L (o + 1) (o + 40) (ieZ (a + 2) (a + 7) (o + 5) (r + 4)) (a + 7) (r + 4) r (r + 5) nd r)
  (.seq (xmatvec L (o + 1) (o + 20) (o + 40) (a + 1) (a + 7) (a + 8) (r + 7) (r + 4) (r + 5) nd r)
  (.seq (xscanL L row (o + 1) (o + 2) (o + 3) (o + 19) (o + 20) (o + 21) (o + 22) (o + 23) (o + 24) (o + 25)
      (o + 16) (o + 17) (o + 18) (o + 26) (o + 27) (o + 28) (o + 40) (a + 9) (a + 10) (a + 8) a
      (r + 3) (r + 2) (r + 4) (r + 5) nd r (r + 6))
  (.seq (xmatvecT L (o + 1) (o + 20) (o + 40) (a + 1) (a + 10) (a + 11) (r + 7) (r + 4) (r + 5) nd r)
  (.seq (xupdMu L (o + 1) (o + 34) (o + 40) (a + 2) (a + 11) (o + 4) (o + 18) (o + 7) (o + 8) (o + 9) (r + 7) nd r)
  (xtupdT L (o + 1) (o + 34) (o + 40) (a + 3) (a + 11) (a + 6) (o + 4) (o + 18) (o + 5) (o + 7) (o + 6) (o + 13)
      (o + 10) (o + 11) (o + 12) (r + 7) (r + 6) (r + 4) nd r)))))))

/-- The units of `xstep1` with `M` rows. -/
abbrev step1K (d M : ℕ) : ℕ :=
  d * (d * 10 + 9) + 4 + (1 + (d * (7 + 6) + 3 + (d * (d * 10 + 9) + 4 +
    ((1 + (1 + (1 + (d * (2 + 3) + 3 + (M * (18 * d + 29 + scanBK d + 3) + 3))))) +
    (d * (1 + (1 + (d * 10 + 4 + 2)) + 3) + 3 + (d * (11 + (4 + 2) + 3) + 3 + (d * (d * (44 + 3) + 3 + 3) + 3)))))))

theorem abs_tzZ_le {X : PosZ d} {Y : Fin d → ℤ} {P2 : ℤ} {E : ℕ} (bX1 : ∀ i, |X.1 i| ≤ 2 ^ E)
    (bX2 : ∀ i l, |X.2 i l| ≤ 2 ^ E) (bY : ∀ l, |Y l| ≤ 2 ^ E) (bP : |P2| ≤ 2 ^ E) (i : Fin d) :
    |tzZ X Y P2 i| ≤ 2 ^ (2 * E + d + 1) := by
  have h1 : |X.1 i * P2| ≤ 2 ^ (2 * E + d) :=
    (by rw [two_mul]; exact absI_mul_le (bX1 i) bP : |X.1 i * P2| ≤ 2 ^ (2 * E)).trans
      (pow_le_pow_right₀ (by norm_num) (by omega))
  have h2 : |∑ l, X.2 i l * Y l| ≤ 2 ^ (2 * E + d) := dot_abs_le (fun l => bX2 i l) bY
  calc |tzZ X Y P2 i| ≤ |X.1 i * P2| + |∑ l, X.2 i l * Y l| := abs_add_le _ _
    _ ≤ 2 ^ (2 * E + d) + 2 ^ (2 * E + d) := add_le_add h1 h2
    _ = 2 ^ (2 * E + d + 1) := by ring

theorem abs_mulVec_le {M : Matrix (Fin d) (Fin d) ℤ} {x : Fin d → ℤ} {E : ℕ} (bM : ∀ i l, |M i l| ≤ 2 ^ E)
    (bx : ∀ l, |x l| ≤ 2 ^ E) (i : Fin d) : |(M *ᵥ x) i| ≤ 2 ^ (2 * E + d) :=
  dot_abs_le (fun l => bM i l) bx

theorem abs_le_mono {x : ℤ} {E F : ℕ} (h : |x| ≤ 2 ^ E) (hEF : E ≤ F) : |x| ≤ 2 ^ F :=
  h.trans (pow_le_pow_right₀ (by norm_num) hEF)

set_option maxHeartbeats 8000000 in
/-- The rule of `xstep1`: one draw of the core, `X̂ := tzStep1 c T̂ μ̂ ra rb M X̂ Y`; the row command is given by its rule
(that of `xrowK` at the layout) on every environment the draw reaches. -/
theorem XV.step1 {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {row : XCmd}
    {o r a nd M E : ℕ} {c : DC} {T : Matrix (Fin d) (Fin d) ℤ} {mu : Fin d → ℤ} {ra : ℕ → Fin d → ℤ} {rb : ℕ → ℤ}
    {Xp : PosZ d} {Y : Fin d → ℤ}
    (hS : o + 70 ≤ L.NS) (hN : r + 11 ≤ L.NN) (hA : a + 12 ≤ L.NA) (hnd : nd < r)
    (hσd : σ.nat nd = d) (hσ1 : σ.nat r = 1) (hσM : σ.nat (r + 2) = M) (hda : d * d + d < 2 ^ ℓa)
    (hMa : M < 2 ^ ℓa)
    (eZ : σ.sc (o + 1) = 0) (eO : σ.sc (o + 2) = 1) (eM : σ.sc (o + 3) = -1)
    (ePB : σ.sc (o + 4) = c.PB) (eP2 : σ.sc (o + 5) = c.P2) (ePG : σ.sc (o + 6) = c.PG)
    (ePj : σ.sc (o + 7) = c.Pj) (eR : σ.sc (o + 8) = c.R) (eMR : σ.sc (o + 9) = -c.R)
    (eAl : σ.sc (o + 10) = c.Al) (eBh : σ.sc (o + 11) = c.Bh) (eMB : σ.sc (o + 12) = ((-c.Bh : ℤ) : ℝ))
    (eD8 : σ.sc (o + 13) = ((8 * c.dd : ℤ) : ℝ))
    (eMu : ∀ l : Fin d, σ.arr a l = mu l) (eT : ∀ i l : Fin d, σ.arr (a + 1) (d * i + l) = T i l)
    (eXm : ∀ l : Fin d, σ.arr (a + 2) l = Xp.1 l) (eXt : ∀ i l : Fin d, σ.arr (a + 3) (d * i + l) = Xp.2 i l)
    (eY : ∀ l : Fin d, σ.arr (a + 6) l = Y l)
    (hrow : ∀ k < M, ∀ σ' : Env d, FrameA (stS o) (stN r) (stA d a) σ σ' → σ'.draws = σ.draws →
      σ'.nat (r + 3) = k →
      XRunsB L X ℓa ℓ row σ' (18 * d + 29) (fun σ'' => (∀ l : Fin d, σ''.arr (a + 9) l = ra k l) ∧
        σ''.sc (o + 19) = rb k ∧ σ''.draws = σ'.draws ∧
        FrameA (rwS o) (rwN r) (fun b k' => b = a + 9 ∧ k' < d) σ' σ''))
    (bX1 : ∀ i, |Xp.1 i| ≤ 2 ^ E) (bX2 : ∀ i l, |Xp.2 i l| ≤ 2 ^ E) (bY : ∀ l, |Y l| ≤ 2 ^ E)
    (bT : ∀ i l, |T i l| ≤ 2 ^ E) (bMu : ∀ l, |mu l| ≤ 2 ^ E) (bR : ∀ k < M, ∀ l, |ra k l| ≤ 2 ^ E)
    (bB : ∀ k < M, |rb k| ≤ 2 ^ E) (bPB : |c.PB| ≤ 2 ^ E) (bP2 : |c.P2| ≤ 2 ^ E) (bPG : |c.PG| ≤ 2 ^ E)
    (bPj : |c.Pj| ≤ 2 ^ E) (bRR : |c.R| ≤ 2 ^ E) (bAl : |c.Al| ≤ 2 ^ E) (bBh : |c.Bh| ≤ 2 ^ E)
    (bD8 : |8 * c.dd| ≤ 2 ^ E) (hE : 48 * E + 42 * d + 32 < ℓ) :
    XRunsB L X ℓa ℓ (xstep1 L row o r a nd) σ (step1K d M)
      (fun σ' => (∀ l : Fin d, σ'.arr (a + 2) l = (tzStep1 c T mu ra rb M Xp Y).1 l) ∧
        (∀ i l : Fin d, σ'.arr (a + 3) (d * i + l) = (tzStep1 c T mu ra rb M Xp Y).2 i l) ∧
        σ'.draws = σ.draws ∧ FrameA (stS o) (stN r) (stA d a) σ σ') := by
  have hNS : ∀ k, k < 70 → o + k < L.NS := fun k h => by omega
  have hNN : ∀ k, k < 11 → r + k < L.NN := fun k h => by omega
  have hNA : ∀ k, k < 12 → a + k < L.NA := fun k h => by omega
  have hndN : nd < L.NN := by omega
  have hdl : ∀ F, 2 * F + d < ℓ → d * 2 ^ (2 * F) < 2 ^ ℓ := fun F hF => by
    have h2 : d < 2 ^ d := Nat.lt_two_pow_self
    calc d * 2 ^ (2 * F) ≤ 2 ^ d * 2 ^ (2 * F) := Nat.mul_le_mul_right _ h2.le
      _ = 2 ^ (2 * F + d) := by rw [← pow_add]; ring_nf
      _ < 2 ^ ℓ := Nat.pow_lt_pow_right (by norm_num) hF
  have hcell : ∀ k < d, k < asz d := fun k hk => by unfold asz; nlinarith
  -- ẑ, first `X̂_T Y`
  refine XV.seq (XV.matvec hL (z := o + 1) (r := o + 20) (t := o + 40) (aM := a + 3) (ax := a + 6) (ay := a + 7)
    (ni := r + 7) (nr := r + 4) (nk := r + 5) (nd := nd) (none := r) (E := E) (M := Xp.2) (x := Y) (by omega)
    (by omega) (by omega) (by omega) eZ (hNA 3 (by norm_num)) (hNA 6 (by norm_num)) (hNA 7 (by norm_num))
    (by omega) (by omega) (hNN 7 (by norm_num)) (hNN 4 (by norm_num)) (hNN 5 (by norm_num)) hndN
    (hNN 0 (by norm_num)) (by simp; omega) hσd hσ1 eXt eY bX2 bY (by omega) (hdl E (by omega)))
    fun σ1 ⟨z1, dr1, F1⟩ => ?_
  have G1 : FrameA (stS o) (stN r) (stA d a) σ σ1 := F1.mono (fun y h => by simp only [stS]; omega)
    (fun j h => by simp only [stN]; omega) (fun b k h => by simp only [stA]; omega)
  refine XV.seq (XV.nconst hL (hNN 4 (by norm_num)) 0 (by positivity)) fun σ2 e2 => ?_
  subst e2
  have G2 : FrameA (stS o) (stN r) (stA d a) σ (σ1.setNat (r + 4) 0) := G1.setNat (by simp only [stN]; omega) _
  -- ẑ
  have F2 : ∀ k (hk : k < d), ∀ σ' : Env d, FrameA (fun y => o + 40 ≤ y) (fun j => j = r + 5 ∨ j = r + 4)
      (fun b c' => b = a + 7 ∧ 0 ≤ c' ∧ c' < 0 + 1 * k) (σ1.setNat (r + 4) 0) σ' →
      σ'.draws = (σ1.setNat (r + 4) 0).draws → σ'.nat (r + 5) = k → σ'.nat (r + 4) = 0 + 1 * k →
      (ieZ (a + 2) (a + 7) (o + 5) (r + 4)).Leaves (2 * E + d) σ' ∧
        (ieZ (a + 2) (a + 7) (o + 5) (r + 4)).eval σ' = ((tzZ Xp Y c.P2) ⟨k, hk⟩ : ℤ) := by
    intro k hk σ' F' _ _ hr
    have Fσ := G2.trans (F'.mono (fun y h => by simp only [stS]; omega) (fun j h => by simp only [stN]; omega)
      (fun b k' h => by simp only [stA]; omega))
    have hr' : σ'.nat (r + 4) = k := by omega
    have xm : σ'.arr (a + 2) k = Xp.1 ⟨k, hk⟩ := by
      rw [F'.2.2.1 _ _ (by omega), Env.setNat_arr, F1.2.2.1 _ _ (by omega), eXm ⟨k, hk⟩]
    have p2 : σ'.sc (o + 5) = c.P2 := by rw [Fσ.2.1 _ (by simp only [stS]; omega), eP2]
    have zk : σ'.arr (a + 7) k = (Xp.2 *ᵥ Y) ⟨k, hk⟩ := by
      rw [F'.2.2.1 _ _ (by omega), Env.setNat_arr, z1 ⟨k, hk⟩]
    have hE1 : E ≤ 2 * E + d := by omega
    refine ⟨?_, ?_⟩
    · simp only [ieZ, IE.Leaves]
      exact ⟨⟨⟨by rw [hr']; exact hcell k hk, Xp.1 ⟨k, hk⟩, by rw [hr', xm], abs_le_mono (bX1 _) hE1⟩,
        ⟨c.P2, p2, abs_le_mono bP2 hE1⟩⟩,
        ⟨by rw [hr']; exact hcell k hk, (Xp.2 *ᵥ Y) ⟨k, hk⟩, by rw [hr', zk], abs_mulVec_le bX2 bY _⟩⟩
    · simp only [ieZ, IE.eval, RealRAM.Op2.eval, hr', xm, p2, zk, tzZ, Matrix.mulVec, dotProduct]
      push_cast; ring
  refine XV.seq (XV.mono (K := d * (7 + 6) + 3) (XV.mapE hL (z := o + 1) (t := o + 40)
    (e := ieZ (a + 2) (a + 7) (o + 5) (r + 4)) (aB := a + 7) (nr := r + 4) (nst := r) (nk := r + 5) (nn := nd)
    (none := r) (E := 2 * E + d) (N := d) (base := 0) (st := 1) (F := fun k => vext (tzZ Xp Y c.P2) k)
    (by simp only [ieZ, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega) (by omega)
    (by simp only [ieZ, IE.scr]; omega) (by rw [Env.setNat_sc, F1.2.1 _ (by omega), eZ]) (hNA 7 (by norm_num))
    (hNN 4 (by norm_num)) (hNN 0 (by norm_num)) (hNN 5 (by norm_num)) hndN (hNN 0 (by norm_num))
    (by simp; omega) (by omega) (by omega) (by rw [nat_setNat_ne _ (by omega), F1.1 _ (by omega), hσd])
    (by rw [nat_setNat_ne _ (by omega), F1.1 _ (by omega), hσ1]) (by rw [nat_setNat_eq])
    (by rw [nat_setNat_ne _ (by omega), F1.1 _ (by omega), hσ1]) one_pos (fun k hk => by simpa using hcell k hk)
    (by omega) (by omega) (by have := hL.1; omega)
    (by simp only [ieZ, IE.top, IE.mag]; omega)
    (fun k hk σ' F' d' hk' hr => by rw [vext_lt _ hk]; exact F2 k hk σ' F' d' hk' hr)) (by simp)
    (fun _ h => h)) fun σ3 ⟨z3, _, dr3, F3⟩ => ?_
  have G3 : FrameA (stS o) (stN r) (stA d a) σ σ3 := G2.trans (F3.mono (fun y h => by simp only [stS]; omega)
    (fun j h => by simp only [stN]; omega) (fun b k h => by simp only [stA]; omega))
  have zz : ∀ l : Fin d, σ3.arr (a + 7) l = tzZ Xp Y c.P2 l := fun l => by
    have := z3 l l.2; simp only [zero_add, one_mul] at this; rw [this, vext_lt _ l.2]
  -- ŵ = T̂ ẑ
  have E2 : 2 * (2 * E + d + 1) + d < ℓ := by omega
  refine XV.seq (XV.matvec hL (z := o + 1) (r := o + 20) (t := o + 40) (aM := a + 1) (ax := a + 7) (ay := a + 8)
    (ni := r + 7) (nr := r + 4) (nk := r + 5) (nd := nd) (none := r) (E := 2 * E + d + 1) (M := T)
    (x := tzZ Xp Y c.P2) (by omega) (by omega) (by omega) (by omega) (by rw [G3.2.1 _ (by simp only [stS]; omega), eZ])
    (hNA 1 (by norm_num)) (hNA 7 (by norm_num)) (hNA 8 (by norm_num)) (by omega) (by omega) (hNN 7 (by norm_num))
    (hNN 4 (by norm_num)) (hNN 5 (by norm_num)) hndN (hNN 0 (by norm_num)) (by simp; omega)
    (by rw [G3.1 _ (by simp only [stN]; omega), hσd]) (by rw [G3.1 _ (by simp only [stN]; omega), hσ1])
    (fun i l => by rw [G3.2.2.1 _ _ (by simp only [stA]; omega), eT]) zz (fun i l => abs_le_mono (bT i l) (by omega))
    (abs_tzZ_le bX1 bX2 bY bP2) (by omega) (hdl _ E2)) fun σ4 ⟨w4, dr4, F4⟩ => ?_
  have G4 : FrameA (stS o) (stN r) (stA d a) σ σ4 := G3.trans (F4.mono (fun y h => by simp only [stS]; omega)
    (fun j h => by simp only [stN]; omega) (fun b k h => by simp only [stA]; omega))
  -- the scan
  have E3 : 4 * (2 * (2 * E + d + 1) + d) + 2 * d + 4 < ℓ := by omega
  have bw : ∀ l, |(T *ᵥ tzZ Xp Y c.P2) l| ≤ 2 ^ (2 * (2 * E + d + 1) + d) :=
    abs_mulVec_le (fun i l => abs_le_mono (bT i l) (by omega)) (abs_tzZ_le bX1 bX2 bY bP2)
  refine XV.seq (XV.scanL hL (row := row) (sZ := o + 1) (sOne := o + 2) (sMOne := o + 3) (sB := o + 19)
    (sN := o + 20) (sTd := o + 21) (sBt := o + 22) (sQN := o + 23) (sQB := o + 24) (sSg := o + 25) (sBn := o + 16)
    (sBd := o + 17) (sBb := o + 18) (sL := o + 26) (sR := o + 27) (sT := o + 28) (t := o + 40) (aRow := a + 9)
    (aK := a + 10) (aW := a + 8) (aMu := a) (nk := r + 3) (nM := r + 2) (nr := r + 4) (nq := r + 5) (nd := nd)
    (none := r) (nl := r + 6) (M := M) (Kr := 18 * d + 29) (E := 2 * (2 * E + d + 1) + d) (Ss := stS o)
    (Ns := stN r) (Srow := rwS o) (Nrow := rwN r) (As := fun b k => (b = a + 9 ∨ b = a + 10) ∧ k < d)
    (Arow := fun b k' => b = a + 9 ∧ k' < d) (ra := ra) (rb := rb) (w := T *ᵥ tzZ Xp Y c.P2) (mu := mu)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by simp)
    (hNA 9 (by norm_num)) (hNA 10 (by norm_num)) (hNA 8 (by norm_num)) (hNA 0 (by norm_num)) (by omega)
    (hNN 3 (by norm_num)) (hNN 2 (by norm_num)) (hNN 4 (by norm_num)) (hNN 5 (by norm_num)) hndN
    (hNN 0 (by norm_num)) (hNN 6 (by norm_num)) (by simp; omega)
    (by rw [G4.1 _ (by simp only [stN]; omega), hσd]) (by rw [G4.1 _ (by simp only [stN]; omega), hσ1])
    (by rw [G4.1 _ (by simp only [stN]; omega), hσM]) hda hMa
    (by rw [G4.2.1 _ (by simp only [stS]; omega), eZ]) (by rw [G4.2.1 _ (by simp only [stS]; omega), eO])
    (by rw [G4.2.1 _ (by simp only [stS]; omega), eM]) w4
    (fun l => by rw [G4.2.2.1 _ _ (by simp only [stA]; omega), eMu])
    (fun y h => by simp only [stS]; omega) (fun y h => by simp only [stS, rwS] at h ⊢; omega)
    (fun j h => by simp only [stN]; omega) (fun j h => by simp only [stN, rwN] at h ⊢; omega)
    (fun b k h => by omega) (fun b k h => ⟨Or.inl h.1, h.2⟩)
    ⟨by simp only [stS]; omega, by simp only [stS]; omega, by simp only [stS]; omega⟩
    ⟨by simp only [stN]; omega, by simp only [stN]; omega, by simp only [stN]; omega⟩
    (fun l => ⟨by omega, by omega⟩)
    ⟨by simp only [rwS]; omega, by simp only [rwS]; omega, by simp only [rwS]; omega, by simp only [rwN]; omega,
      fun l h => by omega⟩
    (fun k hk σ' F' d' hk' => hrow k hk σ' (G4.trans (F'.mono (fun _ h => h) (fun _ h => h)
      (fun b k h => by simp only [stA]; omega))) (by rw [d', dr4, dr3, Env.setNat_draws, dr1]) hk')
    (fun k hk l => abs_le_mono (bR k hk l) (by omega)) (fun k hk => abs_le_mono (bB k hk) (by omega)) bw
    (fun l => abs_le_mono (bMu l) (by omega)) E3) fun σ5 ⟨bn5, bd5, bb5, rw5, dr5, F5⟩ => ?_
  have G5 : FrameA (stS o) (stN r) (stA d a) σ σ5 := G4.trans (F5.mono (fun _ h => h) (fun _ h => h)
    (fun b k h => by simp only [stA]; omega))
  have hkeep : scan (fun k => ra k ⬝ᵥ (T *ᵥ tzZ Xp Y c.P2)) (fun k => rb k - ra k ⬝ᵥ mu) ra M =
      tzKeep T mu ra rb M (tzZ Xp Y c.P2) := rfl
  rw [hkeep] at bn5 bd5 bb5 rw5
  generalize hK : tzKeep T mu ra rb M (tzZ Xp Y c.P2) = K at bn5 bd5 bb5 rw5
  have E3' : E ≤ 2 * (2 * E + d + 1) + d := by omega
  obtain ⟨-, -, -, brow, bbp, bbl⟩ := scan_bound (fun k => ra k ⬝ᵥ (T *ᵥ tzZ Xp Y c.P2))
    (fun k => rb k - ra k ⬝ᵥ mu) ra M (2 ^ (2 * (2 * (2 * E + d + 1) + d) + d))
    (2 ^ (2 * (2 * E + d + 1) + d)) (2 ^ (2 * (2 * (2 * E + d + 1) + d) + d + 1)) (by positivity) (by positivity)
    (one_le_pow₀ (by norm_num))
    (fun k hk => dot_abs_le (fun l => abs_le_mono (bR k hk l) E3') bw)
    (fun k hk l => abs_le_mono (bR k hk l) E3')
    (fun k hk => by
      have h1 := dot_abs_le (fun l => abs_le_mono (bR k hk l) E3') (fun l => abs_le_mono (bMu l) E3')
      have h2 := abs_le_mono (bB k hk) (show E ≤ 2 * (2 * (2 * E + d + 1) + d) + d by omega)
      calc |rb k - ra k ⬝ᵥ mu| ≤ |rb k| + |ra k ⬝ᵥ mu| := abs_sub _ _
        _ ≤ _ := add_le_add h2 h1
        _ = _ := by ring)
  rw [hkeep, hK] at brow bbp bbl
  -- A = T̂ᵀ row
  refine XV.seq (XV.matvecT hL (z := o + 1) (r := o + 20) (t := o + 40) (aM := a + 1) (ax := a + 10)
    (ay := a + 11) (ni := r + 7) (nr := r + 4) (nk := r + 5) (nd := nd) (none := r)
    (E := 2 * (2 * E + d + 1) + d) (M := T) (x := K.row) (by omega) (by omega) (by omega) (by omega)
    (by rw [G5.2.1 _ (by simp only [stS]; omega), eZ]) (hNA 1 (by norm_num)) (hNA 10 (by norm_num))
    (hNA 11 (by norm_num)) (by omega) (by omega) (hNN 7 (by norm_num)) (hNN 4 (by norm_num))
    (hNN 5 (by norm_num)) hndN (hNN 0 (by norm_num)) (by simp; omega)
    (by rw [G5.1 _ (by simp only [stN]; omega), hσd]) (by rw [G5.1 _ (by simp only [stN]; omega), hσ1])
    (fun i l => by rw [G5.2.2.1 _ _ (by simp only [stA]; omega), eT]) rw5
    (fun i l => abs_le_mono (bT i l) E3') brow (by omega) (hdl _ (by omega))) fun σ6 ⟨A6, dr6, F6⟩ => ?_
  have G6 : FrameA (stS o) (stN r) (stA d a) σ σ6 := G5.trans (F6.mono (fun y h => by simp only [stS]; omega)
    (fun j h => by simp only [stN]; omega) (fun b k h => by simp only [stA]; omega))
  have bA : ∀ i, |(Tᵀ *ᵥ K.row) i| ≤ 2 ^ (2 * (2 * (2 * E + d + 1) + d) + d) :=
    abs_mulVec_le (fun i l => abs_le_mono (bT l i) E3') brow
  have E5 : E ≤ 2 * (2 * (2 * E + d + 1) + d) + d + 1 := by omega
  have E5' : 2 * (2 * (2 * E + d + 1) + d) + d ≤ 2 * (2 * (2 * E + d + 1) + d) + d + 1 := by omega
  have bBb : |K.bb| ≤ 2 ^ (2 * (2 * (2 * E + d + 1) + d) + d + 1) := by rw [abs_of_pos bbp]; exact bbl
  have xm6 : ∀ i : Fin d, σ6.arr (a + 2) i = Xp.1 i := fun i => by
    rw [F6.2.2.1 _ _ (by omega), F5.2.2.1 _ _ (by omega), F4.2.2.1 _ _ (by omega), F3.2.2.1 _ _ (by omega),
      Env.setNat_arr, F1.2.2.1 _ _ (by omega), eXm]
  have bb6 : σ6.sc (o + 18) = K.bb := by rw [F6.2.1 _ (by omega), bb5]
  have cst : ∀ k, k < 16 → σ6.sc (o + k) = σ.sc (o + k) := fun k hk => G6.2.1 _ (by simp only [stS]; omega)
  -- the update of μ̂
  refine XV.seq (XV.updMu hL (z := o + 1) (v := o + 34) (t := o + 40) (aXm := a + 2) (aA := a + 11) (sPB := o + 4)
    (sBb := o + 18) (sPj := o + 7) (sR := o + 8) (sMR := o + 9) (ni := r + 7) (nd := nd) (none := r)
    (E := 2 * (2 * (2 * E + d + 1) + d) + d + 1) (c := c) (Xp := Xp) (A := Tᵀ *ᵥ K.row) (Y := Y) (Bb := K.bb)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by rw [cst 1 (by norm_num), eZ]) (hNA 2 (by norm_num))
    (hNA 11 (by norm_num)) (by omega) (hNN 7 (by norm_num)) hndN (hNN 0 (by norm_num)) (by omega) (by omega)
    (by rw [G6.1 _ (by simp only [stN]; omega), hσd]) (by rw [G6.1 _ (by simp only [stN]; omega), hσ1])
    (by omega) xm6 A6 (by rw [cst 4 (by norm_num), ePB]) bb6 (by rw [cst 7 (by norm_num), ePj])
    (by rw [cst 8 (by norm_num), eR]) (by rw [cst 9 (by norm_num), eMR]) (fun i => abs_le_mono (bX1 i) E5)
    (fun i => abs_le_mono (bA i) E5') (abs_le_mono bPB E5) bBb (abs_le_mono bPj E5) (abs_le_mono bRR E5)
    (by omega)) fun σ7 ⟨m7, dr7, F7⟩ => ?_
  have G7 : FrameA (stS o) (stN r) (stA d a) σ σ7 := G6.trans (F7.mono (fun y h => by simp only [stS]; omega)
    (fun j h => by simp only [stN]; omega) (fun b k h => by simp only [stA]; omega))
  have cst7 : ∀ k, k < 16 → σ7.sc (o + k) = σ.sc (o + k) := fun k hk => G7.2.1 _ (by simp only [stS]; omega)
  have xt7 : ∀ i l : Fin d, σ7.arr (a + 3) (d * i + l) = Xp.2 i l := fun i l => by
    rw [F7.2.2.1 _ _ (by omega), F6.2.2.1 _ _ (by omega), F5.2.2.1 _ _ (by omega), F4.2.2.1 _ _ (by omega),
      F3.2.2.1 _ _ (by omega), Env.setNat_arr, F1.2.2.1 _ _ (by omega), eXt]
  -- the update of T̂
  refine XV.mono (XV.tupdT hL (z := o + 1) (v := o + 34) (t := o + 40) (aXt := a + 3) (aA := a + 11) (aY := a + 6)
    (sPB := o + 4) (sBb := o + 18) (sP2 := o + 5) (sPj := o + 7) (sPG := o + 6) (sD8 := o + 13) (sAl := o + 10)
    (sBh := o + 11) (sMB := o + 12) (ni := r + 7) (nl := r + 6) (nr := r + 4) (nd := nd) (none := r)
    (E := 2 * (2 * (2 * E + d + 1) + d) + d + 1) (c := c) (Xp := Xp) (A := Tᵀ *ᵥ K.row) (Y := Y) (Bb := K.bb)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by simp) (by omega) (by rw [cst7 1 (by norm_num), eZ]) (hNA 3 (by norm_num))
    (hNA 11 (by norm_num)) (hNA 6 (by norm_num)) (by omega) (by omega) (hNN 7 (by norm_num)) (hNN 6 (by norm_num))
    (hNN 4 (by norm_num)) hndN (hNN 0 (by norm_num)) (by simp; omega)
    (by rw [G7.1 _ (by simp only [stN]; omega), hσd]) (by rw [G7.1 _ (by simp only [stN]; omega), hσ1]) hda xt7
    (fun l => by rw [F7.2.2.1 _ _ (by omega), A6])
    (fun l => by rw [G7.2.2.1 _ _ (by simp only [stA]; omega), eY])
    (by rw [cst7 4 (by norm_num), ePB]) (by rw [F7.2.1 _ (by omega), bb6]) (by rw [cst7 5 (by norm_num), eP2])
    (by rw [cst7 7 (by norm_num), ePj]) (by rw [cst7 6 (by norm_num), ePG]) (by rw [cst7 13 (by norm_num), eD8])
    (by rw [cst7 10 (by norm_num), eAl]) (by rw [cst7 11 (by norm_num), eBh]) (by rw [cst7 12 (by norm_num), eMB])
    (fun i l => abs_le_mono (bX2 i l) E5) (fun i => abs_le_mono (bA i) E5') (fun l => abs_le_mono (bY l) E5)
    (abs_le_mono bPB E5) bBb (abs_le_mono bP2 E5) (abs_le_mono bPj E5) (abs_le_mono bPG E5) (abs_le_mono bD8 E5)
    (abs_le_mono bAl E5) (abs_le_mono bBh E5) (by omega)) le_rfl ?_
  rintro σ8 ⟨t8, dr8, F8⟩
  have hst : tzStep1 c T mu ra rb M Xp Y = tzUpd c Xp (Tᵀ *ᵥ K.row) Y K.bb := by rw [tzStep1, hK]
  refine ⟨fun l => by rw [F8.2.2.1 _ _ (by omega), m7, hst], fun i l => by rw [t8, hst],
    by rw [dr8, dr7, dr6, dr5, dr4, dr3, Env.setNat_draws, dr1], G7.trans (F8.mono
      (fun y h => by simp only [stS]; omega) (fun j h => by simp only [stN]; omega)
      (fun b k h => by simp only [stA]; omega))⟩

end AdversarialBco.Bit.Transfer
