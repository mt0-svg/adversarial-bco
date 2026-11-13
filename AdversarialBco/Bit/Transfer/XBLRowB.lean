/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLRowC

@[expose] public section

/-!
# The row provider of BL, part 4: the right-hand side

With `b̂ D_S` in the slot `104`, `â` in the array `12`, `2^pF` and `ε̂` in `s2pF`, `sEps`, `D₀` in `107`, the
right-hand side `(1 - ε) β̃ = N_β / D_β`, `N_β = (2^pF - ε̂)(b̂ D_S - ∑_l â_l μ̂_l)`, `D_β = 2^pF D₀`. `xbeta` writes the
reduced pair `N_β / g`, `D_β / g` into `122`, `123` and multiplies the slot `116` by `D_β / g`.
-/

namespace AdversarialBco.Bit.Transfer.BLM.RowM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer.RowP

variable {d : ℕ}

/-- The dot product `∑_l â_l μ̂_l`. -/
def dotS (d : ℕ) (ah xmu : ℕ → ℤ) : ℤ := ∑ l ∈ Finset.range d, ah l * xmu l

/-- The right-hand side: `117 := ∑_l â_l μ̂_l`, `118 := b̂ D_S - 117`, `119 := 2^pF - ε̂`, `120 := N_β`,
`121 := D_β`, the reduced pair in `122`, `123`, `116 := 116 · 123`. -/
def xbeta (L : Layout) : XCmd :=
  .seq (.prim (.frag (.nconst 40 0))) (.seq (xsdot L sZ 117 109 110 12 aMuS 40 rOne 33 rD rOne)
    (.seq (toX (VL.sop2 L .sub 118 104 117)) (.seq (toX (VL.sop2 L .sub 119 s2pF sEps))
      (.seq (toX (VL.sop2 L .mul 120 119 118)) (.seq (toX (VL.sop2 L .mul 121 s2pF 107))
        (.seq (xred L sZ 120 121 111 112 113 122 123) (toX (VL.sop2 L .mul 116 116 123))))))))

/-- The units of the right-hand side. -/
def betaUnits (d s : ℕ) : ℕ := 1 + (sdotUnits d + (1 + (1 + (1 + (1 + (redUnits s + 1))))))

set_option maxHeartbeats 4000000 in
/-- **The right-hand side**: the slots `122`, `123` end as `N_β / g`, `D_β / g` (`g = gcd(N_β, D_β)`), the slot
`116` as `R₀ · D_β / g`; only the slots `109..123`, `116` and the registers `33`, `40` change. -/
theorem XV.beta {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hNS : 128 ≤ L.NS)
    (hNN : 64 ≤ L.NN) (hNA : 16 ≤ L.NA) {t s S : ℕ} {ah xmu : ℕ → ℤ} {bD p2 eh D0 R0 : ℤ}
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0) (h104 : σ.sc 104 = bD) (h2p : σ.sc s2pF = p2)
    (hep : σ.sc sEps = eh) (h107 : σ.sc 107 = D0) (h116 : σ.sc 116 = R0)
    (hah : ∀ l < d, σ.arr 12 l = ah l) (hmu : ∀ l < d, σ.arr aMuS l = xmu l)
    (bah : ∀ l < d, |ah l| ≤ 2 ^ t) (bmu : ∀ l < d, |xmu l| ≤ 2 ^ t) (hts : d * 2 ^ (2 * t) ≤ 2 ^ s)
    (h2ts : 2 * t ≤ s)
    (b104 : |bD| ≤ 2 ^ s) (b2p : |p2| ≤ 2 ^ s) (bep : |eh| ≤ 2 ^ s) (b107 : |D0| ≤ 2 ^ s)
    (b118 : |bD - dotS d ah xmu| ≤ 2 ^ s) (b119 : |p2 - eh| ≤ 2 ^ s)
    (b120 : |(p2 - eh) * (bD - dotS d ah xmu)| ≤ 2 ^ s) (hDb : 0 < p2 * D0) (b121 : p2 * D0 ≤ 2 ^ s)
    (b116 : |R0| ≤ 2 ^ S) (hs : S + s + 1 < ℓ) (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xbeta L) σ (betaUnits d s) (fun σ' =>
      σ'.sc 122 = (((p2 - eh) * (bD - dotS d ah xmu) /
        (Int.gcd ((p2 - eh) * (bD - dotS d ah xmu)) (p2 * D0) : ℤ) : ℤ) : ℝ) ∧
      σ'.sc 123 = ((p2 * D0 / (Int.gcd ((p2 - eh) * (bD - dotS d ah xmu)) (p2 * D0) : ℤ) : ℤ) : ℝ) ∧
      σ'.sc 116 = ((R0 * (p2 * D0 / (Int.gcd ((p2 - eh) * (bD - dotS d ah xmu)) (p2 * D0) : ℤ)) : ℤ) : ℝ) ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => 109 ≤ y ∧ y ≤ 123) (fun j => j = 33 ∨ j = 40) (fun _ _ => False) σ σ') := by
  have hla := hL.1
  have hd1 : d < 2 ^ ℓa := by nlinarith
  have hsl : s < ℓ := by omega
  have hSl : S < ℓ := by omega
  refine XV.seq (XV.nconst hL (i := 40) (by omega) 0 (by omega)) fun σ1 e1 => ?_
  subst e1
  -- `117 := ∑_l â_l μ̂_l`
  have hdot : |dotS d ah xmu| ≤ 2 ^ s := (abs_sum_mul_le bah bmu).trans (by exact_mod_cast hts)
  have hdl : d * 2 ^ (2 * t) < 2 ^ ℓ := lt_of_le_of_lt hts (Nat.pow_lt_pow_right (by norm_num) hsl)
  refine XV.seq (XV.sdot hL (z := sZ) (r := 117) (t1 := 109) (t2 := 110) (ax := 12) (ay := aMuS) (nr := 40)
    (nst := rOne) (nk := 33) (nn := rD) (none := rOne) (N := d) (base := 0) (st := 1) (E := t)
    (Xv := ah) (Yv := xmu) (by rwgo) (by omega) (by omega) (by omega) (by decide)
    (by omega) (by rwgo) (by omega) (by rwgo) (by omega) (by rwgo) (by rwgo) (by decide) (by decide) (by decide)
    (by rwenv; exact hz) (by rwenv; exact hD) (by rwenv; exact h1) (by rwenv) (by rwenv; exact h1)
    (fun l hl => by rwenv; rw [zero_add, one_mul]; exact hah l hl) (fun l hl => by rwenv; exact hmu l hl)
    (fun l hl => by unfold asz; nlinarith) (by unfold asz; nlinarith) bah bmu (by omega) hdl hd1 (by omega)
    (by omega)) fun σ2 ⟨s1, s2, s3, s4⟩ => ?_
  have k2 : ∀ y, y ≠ 117 → y ≠ 109 → y ≠ 110 → σ2.sc y = σ.sc y := fun y a b c => by
    rw [s4.2.1 y (by omega)]; rwenv
  -- `118 := b̂ D_S - 117`, `119 := 2^pF - ε̂`, `120 := N_β`, `121 := D_β`
  refine XV.seq (XV.subI hL (x := 118) (a := 104) (b := 117) (by omega) (by omega) (by omega) (u := bD)
    (v := dotS d ah xmu) (by rw [k2 104 (by omega) (by omega) (by omega), h104]) s1 (absI_le_pow b104 hsl)
    (absI_le_pow hdot hsl) (absI_le_pow b118 hsl)) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.subI hL (x := 119) (a := s2pF) (b := sEps) (by omega) (by rwgo) (by rwgo) (u := p2) (v := eh)
    (by rwenv; rw [k2 s2pF (by rwgo) (by rwgo) (by rwgo), h2p])
    (by rwenv; rw [k2 sEps (by rwgo) (by rwgo) (by rwgo), hep]) (absI_le_pow b2p hsl) (absI_le_pow bep hsl)
    (absI_le_pow b119 hsl)) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.mulI hL (x := 120) (a := 119) (b := 118) (by omega) (by omega) (by omega) (u := p2 - eh)
    (v := bD - dotS d ah xmu) (by rwenv) (by rwenv) (absI_le_pow b119 hsl) (absI_le_pow b118 hsl)
    (absI_le_pow b120 hsl)) fun σ5 e5 => ?_
  subst e5
  have b121' : |p2 * D0| ≤ 2 ^ s := by rw [abs_of_pos hDb]; exact b121
  refine XV.seq (XV.mulI hL (x := 121) (a := s2pF) (b := 107) (by omega) (by rwgo) (by omega) (u := p2) (v := D0)
    (by rwenv; rw [k2 s2pF (by rwgo) (by rwgo) (by rwgo), h2p])
    (by rwenv; rw [k2 107 (by omega) (by omega) (by omega), h107]) (absI_le_pow b2p hsl) (absI_le_pow b107 hsl)
    (absI_le_pow b121' hsl)) fun σ6 e6 => ?_
  subst e6
  -- the reduced pair
  refine XV.seq (XV.red hL (z := sZ) (sN := 120) (sD := 121) (sa := 111) (sb := 112) (st := 113) (snum := 122)
    (sden := 123) (by rwgo) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by decide) (N := (p2 - eh) * (bD - dotS d ah xmu)) (D := p2 * D0) (s := s)
    (by rwenv; rw [k2 sZ (by rwgo) (by rwgo) (by rwgo), hz]) (by rwenv) (by rwenv) hDb b120 b121 (by omega))
    fun σ7 ⟨r1, r2, r3, r4⟩ => ?_
  obtain ⟨g1, g2, g3, g4⟩ := red_bounds ((p2 - eh) * (bD - dotS d ah xmu)) (p2 * D0) hDb
  have b123 : |p2 * D0 / (Int.gcd ((p2 - eh) * (bD - dotS d ah xmu)) (p2 * D0) : ℤ)| ≤ 2 ^ s := by
    rw [abs_of_pos (by omega)]; exact g4.trans b121
  -- `116 := 116 · D_β / g`
  refine XV.mono (XV.mulI hL (x := 116) (a := 116) (b := 123) (by omega) (by omega) (by omega) (u := R0)
    (v := p2 * D0 / (Int.gcd ((p2 - eh) * (bD - dotS d ah xmu)) (p2 * D0) : ℤ))
    (by rw [r4.2.1 116 (by omega)]; rwenv; rw [k2 116 (by omega) (by omega) (by omega), h116]) r2
    (absI_le_pow b116 hSl) (absI_le_pow b123 hsl) (absI_le_pow (absI_mul_le b116 b123) (by omega))) le_rfl
    fun σ8 e8 => ?_
  subst e8
  refine ⟨by rwenv; exact r1, by rwenv; exact r2, by rwenv, by rwenv; rw [r3]; rwenv; rw [s3]; rwenv, ?_⟩
  have F2 : FrameA (fun y => 109 ≤ y ∧ y ≤ 123) (fun j => j = 33 ∨ j = 40) (fun _ _ => False) σ σ2 :=
    ((FrameA.refl _ _ _ σ).setNat (Or.inr rfl) 0).trans
      (s4.mono (fun y h => by omega) (fun j h => h) (fun _ _ h => h))
  exact ((((((F2.setSc ⟨by norm_num, by norm_num⟩ _).setSc ⟨by norm_num, by norm_num⟩ _).setSc
    ⟨by norm_num, by norm_num⟩ _).setSc ⟨by norm_num, by norm_num⟩ _).trans
    (r4.mono (fun y h => by omega) (fun _ h => h.elim) (fun _ _ h => h))).setSc ⟨by norm_num, by norm_num⟩ _)

end AdversarialBco.Bit.Transfer.BLM.RowM
