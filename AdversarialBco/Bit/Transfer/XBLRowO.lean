/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLRowB

@[expose] public section

/-!
# The row provider of BL, part 5: the output

With the reduced pairs of the row in the arrays `13`, `14` (entries `q < d`) and the slots `122`, `123` (right-hand
side), and their product of denominators `R` in the slot `116`, `xout` writes the cleared row: `num_q (R / den_q)`
into the cells `q < d` of the array `33` (`aW + 1` of the block) and `num_β (R / den_β)` into the slot `770`
(`o + 2` of the block).
-/

namespace AdversarialBco.Bit.Transfer.BLM.RowM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer.RowP

variable {d : ℕ}

/-- One output cell `q` (register `42`): `124 := den_q`, `124 := R / 124`, `125 := num_q`, `124 := 125 · 124`, into
the cell `q` of the array `33`. -/
def xoutBody (L : Layout) : XCmd :=
  .seq (toX (VL.aget L 124 14 42)) (.seq (xsidiv L 124 116 124) (.seq (toX (VL.aget L 125 13 42))
    (.seq (toX (VL.sop2 L .mul 124 125 124)) (toX (VL.aset L 33 42 124)))))

/-- The output: the cells `q < d`, then the right-hand side into the slot `770`. -/
def xout (L : Layout) : XCmd :=
  .seq (xforN 42 rD rOne (xoutBody L)) (.seq (xsidiv L 124 116 123) (toX (VL.sop2 L .mul 770 122 124)))

/-- The units of the output. -/
def outUnits (d : ℕ) : ℕ := d * (2 + (1 + (2 + (1 + 2))) + 3) + 3 + (1 + 1)

theorem ediv_bounds {R v : ℤ} {S : ℕ} (hR : 0 ≤ R) (hRS : R ≤ 2 ^ S) (hv : 1 ≤ v) : |R / v| ≤ 2 ^ S := by
  rw [abs_of_nonneg (Int.ediv_nonneg hR (by omega))]
  exact (Int.ediv_le_self v hR).trans hRS

set_option maxHeartbeats 4000000 in
/-- **The output**: the cells `q < d` of the array `33` end as `nu_q (R / de_q)`, the slot `770` as
`nb (R / db)`; only the slots `124`, `125`, `770`, the register `42` and the array `33` change. -/
theorem XV.out {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hNS : 771 ≤ L.NS)
    (hNN : 64 ≤ L.NN) (hNA : 34 ≤ L.NA) {s S : ℕ} {nu de : ℕ → ℤ} {nb db R : ℤ}
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (h116 : σ.sc 116 = R) (h122 : σ.sc 122 = nb) (h123 : σ.sc 123 = db)
    (hnu : ∀ q < d, σ.arr 13 q = nu q) (hde : ∀ q < d, σ.arr 14 q = de q)
    (bnu : ∀ q < d, |nu q| ≤ 2 ^ s) (bde : ∀ q < d, 1 ≤ de q ∧ de q ≤ 2 ^ s) (bnb : |nb| ≤ 2 ^ s)
    (bdb : 1 ≤ db ∧ db ≤ 2 ^ s) (hR : 0 ≤ R) (bR : R ≤ 2 ^ S) (hs : s + S < ℓ) (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xout L) σ (outUnits d) (fun σ' =>
      (∀ q < d, σ'.arr 33 q = ((nu q * (R / de q) : ℤ) : ℝ)) ∧ σ'.sc 770 = ((nb * (R / db) : ℤ) : ℝ) ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => y = 124 ∨ y = 125 ∨ y = 770) (fun j => j = 42) (fun a _ => a = 33) σ σ') := by
  have hla := hL.1
  have hd1 : d < 2 ^ ℓa := by nlinarith
  have hsl : s < ℓ := by omega
  have hSl : S < ℓ := by omega
  have bR' : |R| ≤ 2 ^ S := by rw [abs_of_nonneg hR]; exact bR
  let J : ℕ → Env d → Prop := fun q σ' =>
    (∀ q' < q, σ'.arr 33 q' = ((nu q' * (R / de q') : ℤ) : ℝ)) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = 124 ∨ y = 125) (fun j => j = 42) (fun a _ => a = 33) σ σ'
  refine XV.seq (XV.forN hL (i := 42) (n := rD) (one := rOne) (body := xoutBody L) (by omega) (by rwgo)
    (by rwgo) (by rwgo) (by rwgo) d (2 + (1 + (2 + (1 + 2)))) hd1 J σ hD h1
    ⟨fun q' h => absurd h (Nat.not_lt_zero _), by rwenv,
      (FrameA.refl (fun y => y = 124 ∨ y = 125) (fun j => j = 42) (fun a _ => a = 33) σ).setNat rfl _⟩ ?_)
    fun σ' ⟨⟨hA, hdr, hF⟩, _⟩ => ?_
  · intro q hq σ' ⟨hA, hdr, hF⟩ hq42 hqD hq1
    have e116 : σ'.sc 116 = R := by rw [hF.2.1 116 (by omega), h116]
    have e13 : σ'.arr 13 q = nu q := by rw [hF.2.2.1 13 q (by omega), hnu q hq]
    have e14 : σ'.arr 14 q = de q := by rw [hF.2.2.1 14 q (by omega), hde q hq]
    obtain ⟨d1, d2⟩ := bde q hq
    have bq := ediv_bounds hR bR d1
    refine XV.seq (XV.aget hL (x := 124) (a := 14) (i := 42) (by omega) (by omega) (by omega)
      (by rw [hq42]; unfold asz; nlinarith) (by rw [hq42, e14]; exact XV.abs_int_lt (absI_le_pow (by
        rw [abs_of_pos (by omega)]; exact d2) hsl))) fun σ1 e1 => ?_
    subst e1
    refine XV.seq (XV.divI hL (x := 124) (a := 116) (b := 124) (by omega) (by omega) (by omega) (u := R)
      (v := de q) (by rwenv; exact e116) (by rwenv; rw [hq42, e14]) (absI_le_pow bR' hSl)
      (absI_le_pow (by rw [abs_of_pos (by omega)]; exact d2) hsl)) fun σ2 e2 => ?_
    subst e2
    refine XV.seq (XV.aget hL (x := 125) (a := 13) (i := 42) (by omega) (by omega) (by omega)
      (by rwenv; rw [hq42]; unfold asz; nlinarith)
      (by rwenv; rw [hq42, e13]; exact XV.abs_int_lt (absI_le_pow (bnu q hq) hsl))) fun σ3 e3 => ?_
    subst e3
    refine XV.seq (XV.mulI hL (x := 124) (a := 125) (b := 124) (by omega) (by omega) (by omega) (u := nu q)
      (v := R / de q) (by rwenv; rw [hq42, e13]) (by rwenv) (absI_le_pow (bnu q hq) hsl) (absI_le_pow bq hSl)
      (absI_le_pow (absI_mul_le (bnu q hq) bq) hs)) fun σ4 e4 => ?_
    subst e4
    refine XV.mono (XV.aset hL (a := 33) (i := 42) (x := 124) (by omega) (by omega) (by omega)
      (by rwenv; rw [hq42]; unfold asz; nlinarith)
      (by rwenv; exact XV.abs_int_lt (absI_le_pow (absI_mul_le (bnu q hq) bq) hs))) le_rfl fun σ5 e5 => ?_
    subst e5
    refine ⟨by rwenv; exact hq42, by rwenv; exact hqD, by rwenv; exact hq1, ?_, by rwenv; exact hdr, ?_⟩
    · intro q' hq'
      rw [Env.setNat_arr, Env.setArr_arr]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hq' with h | h
      · simp only [Env.setSc_nat, hq42, show q' ≠ q by omega, and_false, ite_false, Env.setSc_arr]
        exact hA q' h
      · subst h
        simp only [Env.setSc_nat, hq42, and_self, ite_true, sc_setSc_eq]
    · exact (((((hF.setSc (Or.inl rfl) _).setSc (Or.inl rfl) _).setSc (Or.inr rfl) _).setSc (Or.inl rfl) _).setArr
        rfl _).setNat rfl _
  · -- the right-hand side
    have e116 : σ'.sc 116 = R := by rw [hF.2.1 116 (by omega), h116]
    have e122 : σ'.sc 122 = nb := by rw [hF.2.1 122 (by omega), h122]
    have e123 : σ'.sc 123 = db := by rw [hF.2.1 123 (by omega), h123]
    have bq := ediv_bounds hR bR bdb.1
    refine XV.seq (XV.divI hL (x := 124) (a := 116) (b := 123) (by omega) (by omega) (by omega) (u := R) (v := db)
      e116 e123 (absI_le_pow bR' hSl) (absI_le_pow (by rw [abs_of_pos (by omega)]; exact bdb.2) hsl))
      fun σ1 e1 => ?_
    subst e1
    refine XV.mono (XV.mulI hL (x := 770) (a := 122) (b := 124) (by omega) (by omega) (by omega) (u := nb)
      (v := R / db) (by rwenv; exact e122) (by rwenv) (absI_le_pow bnb hsl) (absI_le_pow bq hSl)
      (absI_le_pow (absI_mul_le bnb bq) hs)) le_rfl fun σ2 e2 => ?_
    subst e2
    refine ⟨fun q hq => by rwenv; exact hA q hq, by rwenv, by rwenv; exact hdr, ?_⟩
    exact ((hF.mono (fun y h => by omega) (fun j h => h) (fun _ _ h => h)).setSc (Or.inl rfl) _).setSc
      (Or.inr (Or.inr rfl)) _

end AdversarialBco.Bit.Transfer.BLM.RowM
