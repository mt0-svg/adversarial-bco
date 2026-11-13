/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLRowS
public import AdversarialBco.Bit.Transfer.XBLData

@[expose] public section

/-!
# The call data of BL's round, part 1: the Gram matrix

* `xdot2`, `XV.dot2`: `r := ∑_{k < N} a[bx + k] a[by + k]` (two rows of one array), changing `r`, `t1`, `t2` and the
  registers `nk`, `nx`, `ny`;
* `xgram`, `XV.gram`: for `i, j < d`, `aN[d i + j] := ∑_{k < d} a[d i + k] a[d j + k]` and `aD[d i + j] := yD`: the
  numerators of `B Bᵀ` from those of `B` (row-major in `a`), over one denominator. It changes the slots `256..258`,
  the registers `19..26` and `31`, and the cells below `d²` of `aN` and `aD`.
-/

namespace AdversarialBco.Bit.Transfer.BLM.DataM

open AdversarialBco AdversarialBco.Poly.Mach

variable {d : ℕ}

/-! ## Two rows of one array -/

/-- `r := z + z; for nk < nn: t1 := a[nx]; t2 := a[ny]; t1 := t1 * t2; r := r + t1; nx := nx + none;
ny := ny + none`. -/
def xdot2 (L : Layout) (z r t1 t2 a nx ny nk nn none : ℕ) : XCmd :=
  .seq (toX (VL.sop2 L .add r z z)) (xforN nk nn none (.seq (toX (VL.aget L t1 a nx))
    (.seq (toX (VL.aget L t2 a ny)) (.seq (toX (VL.sop2 L .mul t1 t1 t2))
      (.seq (toX (VL.sop2 L .add r r t1)) (.seq (.prim (.frag (.nadd nx nx none)))
        (.prim (.frag (.nadd ny ny none)))))))))

/-- The units of `xdot2` over `N` turns. -/
def dot2Units (N : ℕ) : ℕ := 1 + (N * (2 + (2 + (1 + (1 + (1 + 1)))) + 3) + 3)

set_option maxHeartbeats 8000000 in
/-- **The dot product of two rows**: `r := ∑_{k < N} X k Y k` with `X k` in the cell `bx + k` and `Y k` in the cell
`by + k` of the array `a`; only `r`, `t1`, `t2`, `nk`, `nx`, `ny` change. -/
theorem XV.dot2 {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {z r t1 t2 a nx ny nk nn none N bx b2 E : ℕ} {Xv Yv : ℕ → ℤ}
    (hz : z < L.NS) (hr : r < L.NS) (ht1 : t1 < L.NS) (ht2 : t2 < L.NS) (hss : [z, r, t1, t2].Nodup)
    (ha : a < L.NA) (hnx : nx < L.NN) (hny : ny < L.NN) (hnk : nk < L.NN) (hnn : nn < L.NN)
    (hno : none < L.NN) (hne : [nx, ny, nk, nn, none].Nodup)
    (hz0 : σ.sc z = 0) (hσn : σ.nat nn = N) (hσ1 : σ.nat none = 1) (hσx : σ.nat nx = bx) (hσy : σ.nat ny = b2)
    (hX : ∀ k < N, σ.arr a (bx + k) = Xv k) (hY : ∀ k < N, σ.arr a (b2 + k) = Yv k)
    (hcx : bx + N ≤ asz d) (hcy : b2 + N ≤ asz d)
    (bX : ∀ k < N, |Xv k| ≤ 2 ^ E) (bY : ∀ k < N, |Yv k| ≤ 2 ^ E) (hE : 2 * E < ℓ) (hℓ : N * 2 ^ (2 * E) < 2 ^ ℓ)
    (hNa : N < 2 ^ ℓa) (hxa : bx + N < 2 ^ ℓa) (hya : b2 + N < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xdot2 L z r t1 t2 a nx ny nk nn none) σ (dot2Units N) (fun σ' =>
      σ'.sc r = ((∑ k ∈ Finset.range N, Xv k * Yv k : ℤ) : ℝ) ∧ σ'.nat nx = bx + N ∧ σ'.nat ny = b2 + N ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => y = r ∨ y = t1 ∨ y = t2) (fun j => j = nk ∨ j = nx ∨ j = ny) (fun _ _ => False) σ σ') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne hss
  obtain ⟨⟨xy, xk, xn, xo⟩, ⟨yk, yn, yo⟩, ⟨kn, ko⟩, -⟩ := hne
  obtain ⟨⟨zr, z1, z2⟩, ⟨r1, r2⟩, t12⟩ := hss
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by rw [abs_zero]; positivity
  have hsum := RowM.abs_sum_mul_lt bX bY hℓ
  have bE : ∀ k < N, |Xv k| < 2 ^ ℓ ∧ |Yv k| < 2 ^ ℓ ∧ |Xv k * Yv k| < 2 ^ ℓ := fun k hk => by
    have hp : (2 : ℤ) ^ E ≤ 2 ^ (2 * E) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hq : (2 : ℤ) ^ (2 * E) < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) hE
    have hxy : |Xv k * Yv k| ≤ 2 ^ (2 * E) := by
      rw [abs_mul]
      calc |Xv k| * |Yv k| ≤ 2 ^ E * 2 ^ E := mul_le_mul (bX k hk) (bY k hk) (abs_nonneg _) (by positivity)
        _ = 2 ^ (2 * E) := by ring
    exact ⟨by linarith [bX k hk], by linarith [bY k hk], by linarith⟩
  refine XV.seq (XV.sop2 hL (x := r) (a := z) (b := z) hr hz hz .add (by intro h; cases h) (by rw [hz0]; exact h0)
    (by rw [hz0]; exact h0) (by simp only [RealRAM.Op2.eval, hz0, add_zero]; exact h0)) fun σ0 e0 => ?_
  subst e0
  have hσ0 : (σ.setSc r (RealRAM.Op2.eval .add (σ.sc z) (σ.sc z))).nat = σ.nat := rfl
  refine XV.mono (XV.forN hL hnk hnn hno kn ko N (2 + (2 + (1 + (1 + (1 + 1))))) hNa
    (fun k σ' => σ'.nat nx = bx + k ∧ σ'.nat ny = b2 + k ∧ σ'.draws = σ.draws ∧
      σ'.sc r = ((∑ j ∈ Finset.range k, Xv j * Yv j : ℤ) : ℝ) ∧
      FrameA (fun y => y = r ∨ y = t1 ∨ y = t2) (fun j => j = nk ∨ j = nx ∨ j = ny) (fun _ _ => False) σ σ')
    _ (by rw [hσ0, hσn]) (by rw [hσ0, hσ1]) ⟨by simp [xk, hσx], by simp [yk, hσy], rfl,
      by simp [RealRAM.Op2.eval, hz0], ((FrameA.refl _ _ _ σ).setSc (Or.inl rfl) _).setNat (Or.inl rfl) 0⟩ ?_)
    le_rfl fun σ' ⟨⟨h1, h2, h3, h4, h5⟩, _⟩ => ⟨h4, h1, h2, h3, h5⟩
  intro k hk σ' ⟨hxk, hyk, hd, hs, hF⟩ hkt hkn hk1
  have eX : σ'.arr a (σ'.nat nx) = Xv k := by rw [hxk, hF.2.2.1 a _ id, hX k hk]
  have eY : σ'.arr a (σ'.nat ny) = Yv k := by rw [hyk, hF.2.2.1 a _ id, hY k hk]
  obtain ⟨bXk, bYk, bXYk⟩ := bE k hk
  refine XV.seq (XV.aget hL ht1 ha hnx (by rw [hxk]; omega) (by rw [eX]; exact XV.abs_int_lt bXk))
    fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.aget hL ht2 ha hny (by rw [Env.setSc_nat, hyk]; omega)
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
  refine XV.seq (XV.nadd hL (i := nx) (a := nx) (b := none) hnx hnx hno
    (by rpenv; rw [hxk]; omega) (by rpenv; rw [hk1]; omega)) fun σ5 e5 => ?_
  subst e5
  refine XV.mono (XV.nadd hL (i := ny) (a := ny) (b := none) hny hny hno
    (by rpenv; rw [hyk]; omega) (by rpenv; rw [hk1]; omega)) le_rfl fun σ6 e6 => ?_
  subst e6
  refine ⟨by rpenv; exact hkt, by rpenv; exact hkn, by rpenv; exact hk1, ?_, ?_, ?_, ?_, ?_⟩
  · rpenv; rw [hxk, hk1]; ring
  · rpenv; rw [hyk, hk1]; ring
  · rpenv; exact hd
  · rpenv; rw [hsk1]
  · exact ((((((hF.setSc (Or.inr (Or.inl rfl)) _).setSc (Or.inr (Or.inr rfl)) _).setSc (Or.inr (Or.inl rfl)) _).setSc
      (Or.inl rfl) _).setNat (Or.inr (Or.inl rfl)) _).setNat (Or.inr (Or.inr rfl)) _).setNat (Or.inl rfl) _

/-! ## The Gram matrix -/

/-- The entry `(i, j)` of `B Bᵀ` from the numerators `xs` of `B`, row-major. -/
def gramN (d : ℕ) (xs : ℕ → ℤ) (i j : ℕ) : ℤ := ∑ k ∈ Finset.range d, xs (d * i + k) * xs (d * j + k)

/-- The turn `j` of a row (`21 = d i`, `22 = d j`, `31 = 0`): `24 := d i; 25 := d j`; `256 := ∑_k a[d i + k]
a[d j + k]`; `23 := d i + j`; `aN[23] := 256; aD[23] := yD; 22 := 22 + d`. -/
def xgramIn (L : Layout) (a aN aD yD : ℕ) : XCmd :=
  .seq (.prim (.frag (.nadd 24 21 31))) (.seq (.prim (.frag (.nadd 25 22 31)))
    (.seq (xdot2 L sZ 256 257 258 a 24 25 26 rD rOne) (.seq (.prim (.frag (.nadd 23 21 20)))
      (.seq (toX (VL.aset L aN 23 256)) (.seq (toX (VL.aset L aD 23 yD)) (.prim (.frag (.nadd 22 22 rD))))))))

/-- The turn `i`: `22 := 0`, the row `i`, `21 := 21 + d`. -/
def xgramOut (L : Layout) (a aN aD yD : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst 22 0))) (.seq (xforN 20 rD rOne (xgramIn L a aN aD yD)) (.prim (.frag (.nadd 21 21 rD))))

/-- `31 := 0; 21 := 0`, then the rows. -/
def xgram (L : Layout) (a aN aD yD : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst 31 0))) (.seq (.prim (.frag (.nconst 21 0))) (xforN 19 rD rOne (xgramOut L a aN aD yD)))

def gIn (d : ℕ) : ℕ := 1 + (1 + (dot2Units d + (1 + (2 + (2 + 1)))))
def gOut (d : ℕ) : ℕ := 1 + ((d * (gIn d + 3) + 3) + 1)

/-- The units of `xgram`. -/
def gramUnits (d : ℕ) : ℕ := 1 + (1 + (d * (gOut d + 3) + 3))

set_option maxHeartbeats 4000000 in
/-- One row `i` of the Gram matrix. -/
theorem XV.gramRow {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hlay : BLLay L)
    {a aN aD yD E i : ℕ} {xs : ℕ → ℤ} {D : ℤ} (ha : a < L.NA) (haN : aN < L.NA) (haD : aD < L.NA)
    (hNa : aN ≠ a) (hDa : aD ≠ a) (hND : aN ≠ aD) (hyD : yD < L.NS) (hy256 : yD < 256 ∨ 258 < yD)
    (hi : i < d) (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (h21 : σ.nat 21 = d * i)
    (h22 : σ.nat 22 = 0) (h31 : σ.nat 31 = 0) (hσD : σ.sc yD = D) (bD : |D| < 2 ^ ℓ)
    (hxs : ∀ c < d * d, σ.arr a c = xs c) (bxs : ∀ c < d * d, |xs c| ≤ 2 ^ E) (hE : 2 * E < ℓ)
    (hℓ : d * 2 ^ (2 * E) < 2 ^ ℓ) (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xforN 20 rD rOne (xgramIn L a aN aD yD)) σ (d * (gIn d + 3) + 3) (fun σ' =>
      (∀ j < d, σ'.arr aN (d * i + j) = gramN d xs i j ∧ σ'.arr aD (d * i + j) = D) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => 256 ≤ y ∧ y ≤ 258) (fun j => j = 20 ∨ (22 ≤ j ∧ j ≤ 26))
        (fun b c => (b = aN ∨ b = aD) ∧ d * i ≤ c ∧ c < d * i + d) σ σ') := by
  obtain ⟨hNS, hNN, -⟩ := hlay
  simp only [rEE, oE] at hNN hNS
  have hd1 : d < 2 ^ ℓa := by omega
  have hdi : d * i + d ≤ d * d := by nlinarith
  let J : ℕ → Env d → Prop := fun j σ' => σ'.nat 22 = d * j ∧
    (∀ j' < j, σ'.arr aN (d * i + j') = gramN d xs i j' ∧ σ'.arr aD (d * i + j') = D) ∧ σ'.draws = σ.draws ∧
    FrameA (fun y => 256 ≤ y ∧ y ≤ 258) (fun j => j = 20 ∨ (22 ≤ j ∧ j ≤ 26))
      (fun b c => (b = aN ∨ b = aD) ∧ d * i ≤ c ∧ c < d * i + j) σ σ'
  refine XV.mono (XV.forN hL (i := 20) (n := rD) (one := rOne) (by omega) (by rwgo) (by rwgo) (by rwgo) (by rwgo)
    d (gIn d) hd1 J σ hD h1
    ⟨by rwenv; rw [h22]; ring, fun j' h => absurd h (Nat.not_lt_zero _), by rwenv,
      (FrameA.refl _ _ _ σ).setNat (Or.inl rfl) 0⟩ ?_) le_rfl fun σ' ⟨⟨_, hA, hdr, hF⟩, _⟩ =>
    ⟨hA, hdr, hF⟩
  intro j hj σ' ⟨h22', hA, hdr, hF⟩ hj20 hjD hj1
  -- what the frame keeps
  have e21 : σ'.nat 21 = d * i := by rw [hF.1 21 (by omega), h21]
  have e31 : σ'.nat 31 = 0 := by rw [hF.1 31 (by omega), h31]
  have ez : σ'.sc sZ = 0 := by rw [hF.2.1 sZ (by rwgo), hz]
  have eD : σ'.sc yD = D := by rw [hF.2.1 yD (by omega), hσD]
  have exs : ∀ c < d * d, σ'.arr a c = xs c := fun c hc => by
    rw [hF.2.2.1 a c (by omega), hxs c hc]
  have hdj : d * j + d ≤ d * d := by nlinarith
  refine XV.seq (XV.nadd hL (i := 24) (a := 21) (b := 31) (by omega) (by omega) (by omega)
    (by rw [e21]; nlinarith) (by rw [e31]; omega)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.nadd hL (i := 25) (a := 22) (b := 31) (by omega) (by omega) (by omega)
    (by rwenv; rw [h22']; nlinarith) (by rwenv; rw [e31]; omega)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.dot2 hL (z := sZ) (r := 256) (t1 := 257) (t2 := 258) (a := a) (nx := 24) (ny := 25) (nk := 26)
    (nn := rD) (none := rOne) (N := d) (bx := d * i) (b2 := d * j) (E := E)
    (Xv := fun k => xs (d * i + k)) (Yv := fun k => xs (d * j + k)) (by rwgo) (by omega) (by omega) (by omega)
    (by decide) ha (by omega) (by omega) (by omega) (by rwgo) (by rwgo) (by decide) (by rwenv; exact ez)
    (by rwenv; exact hjD) (by rwenv; exact hj1) (by rwenv; rw [e21, e31]; ring) (by rwenv; rw [h22', e31]; ring)
    (fun k hk => by rwenv; exact exs _ (by omega)) (fun k hk => by rwenv; exact exs _ (by omega))
    (by unfold asz; omega) (by unfold asz; omega) (fun k hk => bxs _ (by omega)) (fun k hk => bxs _ (by omega)) hE
    hℓ hd1 (by omega) (by omega)) fun σ3 ⟨s1, _, _, s4, s5⟩ => ?_
  have n3 : ∀ j', j' ≠ 24 → j' ≠ 25 → j' ≠ 26 → σ3.nat j' = σ'.nat j' := fun j' h4 h5 h6 => by
    rw [s5.1 j' (by omega)]; rwenv
  have c4' : σ3.nat 21 + σ3.nat 20 = d * i + j := by
    rw [n3 21 (by omega) (by omega) (by omega), n3 20 (by omega) (by omega) (by omega), e21, hj20]
  refine XV.seq (XV.nadd hL (i := 23) (a := 21) (b := 20) (by omega) (by omega) (by omega)
    (by rw [n3 21 (by omega) (by omega) (by omega), e21]; nlinarith)
    (by rw [n3 20 (by omega) (by omega) (by omega), hj20]; omega)) fun σ4 e4 => ?_
  rw [c4'] at e4
  subst e4
  have hgr : |gramN d xs i j| < 2 ^ ℓ :=
    RowM.abs_sum_mul_lt (Xv := fun k => xs (d * i + k)) (Yv := fun k => xs (d * j + k))
      (fun k hk => bxs _ (by omega)) (fun k hk => bxs _ (by omega)) hℓ d le_rfl
  refine XV.seq (XV.aset hL (a := aN) (i := 23) (x := 256) haN (by omega) (by omega)
    (by (try rwenv); unfold asz; omega) (by (try rwenv); rw [s1]; exact XV.abs_int_lt hgr)) fun σ5 e5 => ?_
  subst e5
  have eD3 : σ3.sc yD = D := by rw [s5.2.1 yD (by omega)]; rwenv; exact eD
  refine XV.seq (XV.aset hL (a := aD) (i := 23) (x := yD) haD (by omega) hyD
    (by (try rwenv); unfold asz; omega) (by (try rwenv); rw [eD3]; exact XV.abs_int_lt bD)) fun σ6 e6 => ?_
  subst e6
  refine XV.mono (XV.nadd hL (i := 22) (a := 22) (b := rD) (by omega) (by omega) (by rwgo)
    (by (try rwenv); rw [n3 22 (by omega) (by omega) (by omega), h22']; nlinarith)
    (by (try rwenv); rw [n3 rD (by rwgo) (by rwgo) (by rwgo), hjD]; omega)) le_rfl fun σ7 e7 => ?_
  subst e7
  refine ⟨by rwenv; rw [n3 20 (by omega) (by omega) (by omega)]; exact hj20,
    by rwenv; rw [n3 rD (by rwgo) (by rwgo) (by rwgo)]; exact hjD,
    by rwenv; rw [n3 rOne (by rwgo) (by rwgo) (by rwgo)]; exact hj1, ?_, ?_, ?_, ?_⟩
  · rwenv; rw [n3 22 (by omega) (by omega) (by omega), n3 rD (by rwgo) (by rwgo) (by rwgo), h22', hjD]; ring
  · intro j' hj'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with h | h
    · have hne : d * i + j' ≠ d * i + j := by omega
      have hne' : j' ≠ j := by omega
      have k1 := s5.2.2.1 aN (d * i + j') not_false
      have k2 := s5.2.2.1 aD (d * i + j') not_false
      simp only [Env.setNat_arr] at k1 k2
      simp [Env.setArr_arr, Env.setNat_arr, Env.setArr_nat, hne, hne', k1, k2, hA j' h]
    · subst h
      constructor
      · simp [Env.setArr_arr, Env.setNat_arr, Env.setArr_nat, Env.setNat_sc, hND, s1, gramN]
      · simp [Env.setArr_arr, Env.setNat_arr, Env.setArr_nat, Env.setNat_sc, Env.setArr_sc, hND, Ne.symm hND, eD3]
  · rwenv; rw [s4]; rwenv; exact hdr
  · have F : FrameA (fun y => 256 ≤ y ∧ y ≤ 258) (fun j => j = 20 ∨ (22 ≤ j ∧ j ≤ 26))
        (fun b c => (b = aN ∨ b = aD) ∧ d * i ≤ c ∧ c < d * i + (j + 1)) σ' σ3 :=
      ((((FrameA.refl _ _ _ σ').setNat (Or.inr ⟨by norm_num, by norm_num⟩) _).setNat
        (Or.inr ⟨by norm_num, by norm_num⟩) _).trans
        (s5.mono (fun y h => by omega) (fun j h => by omega) (fun _ _ h => h.elim)))
    refine ((((((hF.mono (fun _ h => h) (fun _ h => h) (fun b c h => ⟨h.1, h.2.1, by omega⟩)).trans F).setNat
      (Or.inr ⟨by norm_num, by norm_num⟩) _).setArr ⟨Or.inl rfl, by (try rwenv); omega, by (try rwenv); omega⟩ _).setArr
      ⟨Or.inr rfl, by (try rwenv); omega, by (try rwenv); omega⟩ _).setNat (Or.inr ⟨by norm_num, by norm_num⟩) _).setNat
      (Or.inl rfl) _

set_option maxHeartbeats 4000000 in
/-- **The Gram matrix**: the cells `d i + j` (`i, j < d`) of `aN` get `∑_{k < d} xs(d i + k) xs(d j + k)` and those
of `aD` the value `D` of the slot `yD`. -/
theorem XV.gram {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hlay : BLLay L)
    {a aN aD yD E : ℕ} {xs : ℕ → ℤ} {D : ℤ} (ha : a < L.NA) (haN : aN < L.NA) (haD : aD < L.NA)
    (hNa : aN ≠ a) (hDa : aD ≠ a) (hND : aN ≠ aD) (hyD : yD < L.NS) (hy256 : yD < 256 ∨ 258 < yD)
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (hσD : σ.sc yD = D) (bD : |D| < 2 ^ ℓ)
    (hxs : ∀ c < d * d, σ.arr a c = xs c) (bxs : ∀ c < d * d, |xs c| ≤ 2 ^ E) (hE : 2 * E < ℓ)
    (hℓ : d * 2 ^ (2 * E) < 2 ^ ℓ) (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xgram L a aN aD yD) σ (gramUnits d) (fun σ' =>
      (∀ i < d, ∀ j < d, σ'.arr aN (d * i + j) = gramN d xs i j ∧ σ'.arr aD (d * i + j) = D) ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => 256 ≤ y ∧ y ≤ 258) (fun j => (19 ≤ j ∧ j ≤ 26) ∨ j = 31)
        (fun b c => (b = aN ∨ b = aD) ∧ c < d * d) σ σ') := by
  have hlay' := hlay
  obtain ⟨hNS, hNN, -⟩ := hlay'
  simp only [rEE, oE] at hNN hNS
  have hd1 : d < 2 ^ ℓa := by omega
  refine XV.seq (XV.nconst hL (i := 31) (by omega) 0 (by positivity)) fun σ0 e0 => ?_
  subst e0
  refine XV.seq (XV.nconst hL (i := 21) (by omega) 0 (by positivity)) fun σ1 e1 => ?_
  subst e1
  let I : ℕ → Env d → Prop := fun i σ' => σ'.nat 21 = d * i ∧ σ'.nat 31 = 0 ∧
    (∀ i' < i, ∀ j < d, σ'.arr aN (d * i' + j) = gramN d xs i' j ∧ σ'.arr aD (d * i' + j) = D) ∧
    σ'.draws = σ.draws ∧
    FrameA (fun y => 256 ≤ y ∧ y ≤ 258) (fun j => (19 ≤ j ∧ j ≤ 26) ∨ j = 31)
      (fun b c => (b = aN ∨ b = aD) ∧ c < d * i) σ σ'
  refine XV.mono (XV.forN hL (i := 19) (n := rD) (one := rOne) (by omega) (by rwgo) (by rwgo) (by rwgo) (by rwgo)
    d (gOut d) hd1 I _ (by rwenv; exact hD) (by rwenv; exact h1)
    ⟨by rwenv; ring, by rwenv, fun i' h => absurd h (Nat.not_lt_zero _), by rwenv,
      (((FrameA.refl _ _ _ σ).setNat (Or.inr rfl) 0).setNat (Or.inl ⟨by norm_num, by norm_num⟩) 0).setNat
        (Or.inl ⟨le_rfl, by norm_num⟩) 0⟩ ?_) le_rfl fun σ' ⟨⟨_, _, hA, hdr, hF⟩, _⟩ =>
    ⟨hA, hdr, hF.mono (fun _ h => h) (fun _ h => h) (fun b c h => ⟨h.1, by nlinarith [h.2]⟩)⟩
  intro i hi σ' ⟨h21, h31, hA, hdr, hF⟩ hi19 hiD hi1
  have ez : σ'.sc sZ = 0 := by rw [hF.2.1 sZ (by rwgo), hz]
  have eD : σ'.sc yD = D := by rw [hF.2.1 yD (by omega), hσD]
  have exs : ∀ c < d * d, σ'.arr a c = xs c := fun c hc => by
    rw [hF.2.2.1 a c (by omega), hxs c hc]
  refine XV.seq (XV.nconst hL (i := 22) (by omega) 0 (by positivity)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.gramRow hL hlay (i := i) (xs := xs) (E := E) ha haN haD hNa hDa hND hyD hy256 hi
    (by rwenv; exact hiD) (by rwenv; exact hi1) (by rwenv; exact ez) (by rwenv; exact h21) (by rwenv)
    (by rwenv; exact h31) (by rwenv; exact eD) bD (fun c hc => by rwenv; exact exs c hc) bxs hE hℓ hda)
    fun σ3 ⟨r1, r2, r3⟩ => ?_
  have n3 : ∀ j', ¬(j' = 20 ∨ (22 ≤ j' ∧ j' ≤ 26)) → σ3.nat j' = σ'.nat j' := fun j' h => by
    rw [r3.1 j' h]; rwenv
  refine XV.mono (XV.nadd hL (i := 21) (a := 21) (b := rD) (by omega) (by omega) (by rwgo)
    (by rw [n3 21 (by omega), h21]; nlinarith) (by rw [n3 rD (by rwgo), hiD]; omega)) le_rfl fun σ4 e4 => ?_
  subst e4
  refine ⟨by rwenv; rw [n3 19 (by omega)]; exact hi19, by rwenv; rw [n3 rD (by rwgo)]; exact hiD,
    by rwenv; rw [n3 rOne (by rwgo)]; exact hi1, ?_, ?_, ?_, ?_, ?_⟩
  · rwenv; rw [n3 21 (by omega), n3 rD (by rwgo), h21, hiD]; ring
  · rwenv; rw [n3 31 (by omega), h31]
  · intro i' hi' j hj
    simp only [Env.setNat_arr]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h | h
    · have hc : d * i' + j < d * i := by nlinarith
      rw [r3.2.2.1 aN _ (fun h' => by omega), r3.2.2.1 aD _ (fun h' => by omega)]
      simp only [Env.setNat_arr]
      exact hA i' h j hj
    · subst h; exact r1 j hj
  · rwenv; rw [r2]; rwenv; exact hdr
  · have F : FrameA (fun y => 256 ≤ y ∧ y ≤ 258) (fun j => (19 ≤ j ∧ j ≤ 26) ∨ j = 31)
        (fun b c => (b = aN ∨ b = aD) ∧ c < d * (i + 1)) σ' σ3 :=
      ((FrameA.refl _ _ _ σ').setNat (Or.inl ⟨by norm_num, by norm_num⟩) _).trans
        (r3.mono (fun _ h => h) (fun j h => Or.inl (by omega)) (fun b c h => ⟨h.1, by nlinarith [h.2.2]⟩))
    exact (((hF.mono (fun _ h => h) (fun _ h => h) (fun b c h => ⟨h.1, by nlinarith [h.2]⟩)).trans F).setNat
      (Or.inl ⟨by norm_num, by norm_num⟩) _).setNat (Or.inl ⟨le_rfl, by norm_num⟩) _

end AdversarialBco.Bit.Transfer.BLM.DataM
