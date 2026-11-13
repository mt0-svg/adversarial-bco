/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XEllRule

@[expose] public section

/-!
# The projection routine on the machine: `EllRule`

`xell L B rowc` computes `ellRI I` over `2^(ellExp I)`: the start constants (`0`, `1` in the slots `u`, `u + 1`, `1`
in the register `n0 + 4`), the early exits (`R < 1`, `r ≤ 0`, `e ≤ 0`, by numerators and denominators), the constants
up to `λ` (`XV.ellJ`), then ELL-R for `d ≥ 2` (`XV.ellBr`) or BIS-R for `d = 1` (`XV.bisBr`). The layout: `P = o + 3`,
`u = o + 15`, `c = o + 75`, `n0 = rE + 1`, `a0 = aW + 2`; the block uses 135 slots, 48 registers and 9 arrays.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.RQ

variable {d : ℕ}

/-! ## The command -/

/-- The failure exit: `0` into the slot `o`. -/
def xellFail (L : Layout) (B : EllBlk) : XCmd := xset L B.o (B.o + 15) (B.o + 15)

/-- After the start constants: the exits, the constants up to `λ`, the branch. -/
def xellMain (L : Layout) (B : EllBlk) (rowc : XCmd) : XCmd :=
  xifS L B.sRn B.sRd (xellFail L B)
    (xifS L (B.o + 15) B.srn
      (xifS L (B.o + 15) B.sen
        (.seq (xellJ L B (B.o + 15) (B.o + 75) (B.rE + 1))
          (.ifN (B.rE + 5) B.rd
            (xellBr L B rowc (B.o + 3) (B.o + 15) (B.o + 75) (B.aW + 2) (B.rE + 1))
            (xbisBr L B rowc (B.o + 3) (B.o + 15) (B.o + 75) (B.aW + 2) (B.rE + 1))))
        (xellFail L B))
      (xellFail L B))

/-- **The projection routine** `xell L B rowc`. -/
def xell (L : Layout) (B : EllBlk) (rowc : XCmd) : XCmd :=
  .seq (toX (VL.sconst L (B.o + 15) 0))
  (.seq (toX (VL.sconst L (B.o + 16) 1))
  (.seq (.prim (.frag (.nconst (B.rE + 5) 1)))
    (xellMain L B rowc)))

/-! ## The units -/

/-- The units of `XV.ellJ` at `E = 6 s + d + 4`. -/
def ellJU (d s : ℕ) : ℕ := 38 * d + 18 + (10 + (32 + (8 * (6 * s + d + 4) + 9)))

/-- The units of `xellMain`. -/
def ellMU (d m s Kr : ℕ) : ℕ := 6 + ellJU d s + ellBrU d m s Kr + bisBrU d m s Kr

/-- The units of `xell`. -/
def ellRU (d m s Kr : ℕ) : ℕ := 3 + ellMU d m s Kr

/-! ## The result -/

theorem ellRI_none {I : EllI d} (h : I.R < 1 ∨ I.r ≤ 0 ∨ I.e ≤ 0) : ellRI I = none := by
  unfold ellRI; exact ite_eq_left h

theorem ellRI_ell {I : EllI d} (hR : ¬ I.R < 1) (hr : 0 < I.r) (he : 0 < I.e) (hd : 2 ≤ d) :
    ellRI I = ellR I ∧ ellExp I = I.p := by
  refine ⟨?_, ?_⟩
  · unfold ellRI; simp [hR, not_le.2 hr, not_le.2 he, show d ≠ 0 by omega, show d ≠ 1 by omega]
  · unfold ellExp; simp [show d ≠ 1 by omega]

theorem ellRI_bis {I : EllI d} (hR : ¬ I.R < 1) (hr : 0 < I.r) (he : 0 < I.e) (hd : d = 1) :
    ellRI I = bisR I ∧ ellExp I = I.lam + 1 := by
  subst hd
  exact ⟨by simp [ellRI, hR, not_le.2 hr, not_le.2 he], by simp [ellExp]⟩

theorem abs_cast_lt {x : ℤ} {s ℓ : ℕ} (h : |x| ≤ 2 ^ s) (hs : s < ℓ) : |(x : ℝ)| < 2 ^ ℓ :=
  XV.abs_int_lt (h.trans_lt (pow_lt_pow_right₀ (by norm_num) hs))

/-! ## On the machine -/

set_option maxHeartbeats 4000000 in
/-- The rule of `xellMain`, from the start constants. -/
theorem XV.ellMain {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk} {I : EllI d}
    {Kr : ℕ} {rowc : XCmd} {Ctx : Env d → Prop} {SR NR AR : ℕ → Prop} (hd : 1 ≤ d)
    (hB : B.OK L 135 48 9) (hav : B.Avoid SR NR AR) (hrow : RowProv L X ℓa ℓ I B rowc Ctx SR NR AR Kr)
    (hctx : CtxOK B Ctx SR NR AR) (hin : EllIn B I σ) (hC : Ctx σ) (hz : σ.sc (B.o + 15) = 0)
    (h1 : σ.sc (B.o + 16) = 1) (hone : σ.nat (B.rE + 5) = 1)
    (hℓ : 4500 * (ellSz I + d + 2) ≤ ℓ) (hℓa : 1000 * (d + I.m + ellSz I + 1) ^ 3 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xellMain L B rowc) σ (ellMU d I.m (ellSz I) Kr) (fun σ' =>
      EllOut B (ellRI I) (ellExp I) σ' ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => B.o ≤ y ∨ SR y) (fun j => B.rE ≤ j ∨ NR j) (fun b _ => B.aW ≤ b ∨ AR b) σ σ') := by
  have hB' := hB
  obtain ⟨hoS, hrN, haA, hrd, hrm, -, -, hsRn, hsRd, hsrn, -, hsen, -, -, -, -, -⟩ := hB'
  have hin' := hin
  obtain ⟨e_d, -, -, -, e_Rn, e_Rd, e_rn, -, e_en, -, -, -, -, -⟩ := hin'
  obtain ⟨-, rW, -, -, -⟩ := ell_regs (m := I.m) (lam := 0) (by omega) hℓa
  have hs : ellSz I < ℓ := by omega
  have bRn : |σ.sc B.sRn| < 2 ^ ℓ := by rw [e_Rn]; exact abs_cast_lt (ellRn_le le_rfl) hs
  have bRd : |σ.sc B.sRd| < 2 ^ ℓ := by
    have := abs_cast_lt (ellRd_le (I := I) le_rfl) hs
    rw [e_Rd]; simpa using this
  have bz : |σ.sc (B.o + 15)| < 2 ^ ℓ := by rw [hz, abs_zero]; positivity
  have brn : |σ.sc B.srn| < 2 ^ ℓ := by
    rw [e_rn]; exact abs_cast_lt (abs_le_sz (ellMx_le I).2.2.2.2.2.2.2.2.2.2.1) hs
  have ben : |σ.sc B.sen| < 2 ^ ℓ := by
    rw [e_en]; exact abs_cast_lt (abs_le_sz (ellMx_le I).2.2.2.2.2.2.2.2.2.2.2.2.1) hs
  have fail : ∀ σ' : Env d, σ'.sc B.o = 0 → σ'.draws = σ.draws →
      FrameA (fun y => y = B.o) (fun _ => False) (fun _ _ => False) σ σ' → ellRI I = none →
      EllOut B (ellRI I) (ellExp I) σ' ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => B.o ≤ y ∨ SR y) (fun j => B.rE ≤ j ∨ NR j) (fun b _ => B.aW ≤ b ∨ AR b) σ σ' :=
    fun σ' v dr F hn => by
      rw [hn]
      exact ⟨v, dr, F.mono (fun y h => Or.inl (by omega)) (fun _ h => h.elim) (fun _ _ h => h.elim)⟩
  -- `R < 1`
  by_cases hR : I.R < 1
  · have hc : σ.sc B.sRn < σ.sc B.sRd := by
      rw [e_Rn, e_Rd]; exact_mod_cast (ellRI_cond I).1.1 hR
    refine XV.mono (XV.ifS_t hL (by omega) (by omega) bRn bRd hc
      (XV.setZ hL (x := B.o) (z := B.o + 15) (by omega) (by omega) hz)) (by unfold ellMU; omega) ?_
    rintro σ' ⟨v, dr, F⟩
    exact fail σ' v dr F (ellRI_none (Or.inl hR))
  have hc : ¬ σ.sc B.sRn < σ.sc B.sRd := by
    rw [e_Rn, e_Rd]; intro h; exact hR ((ellRI_cond I).1.2 (by exact_mod_cast h))
  -- `r ≤ 0`
  by_cases hr : I.r ≤ 0
  · have hc2 : ¬ σ.sc (B.o + 15) < σ.sc B.srn := by
      rw [hz, e_rn]; intro h
      have h' : (0 : ℤ) < I.r.num := by exact_mod_cast h
      have := (ellRI_cond I).2.1.1 hr; omega
    refine XV.mono (XV.ifS_f hL (by omega) (by omega) bRn bRd hc (XV.ifS_f hL (by omega) (by omega) bz brn hc2
      (XV.setZ hL (x := B.o) (z := B.o + 15) (by omega) (by omega) hz))) (by unfold ellMU; omega) ?_
    rintro σ' ⟨v, dr, F⟩
    exact fail σ' v dr F (ellRI_none (Or.inr (Or.inl hr)))
  have hc2 : σ.sc (B.o + 15) < σ.sc B.srn := by
    rw [hz, e_rn]
    have h' : ¬ I.r.num ≤ 0 := fun h => hr ((ellRI_cond I).2.1.2 h)
    have : (0 : ℤ) < I.r.num := by omega
    exact_mod_cast this
  -- `e ≤ 0`
  by_cases he : I.e ≤ 0
  · have hc3 : ¬ σ.sc (B.o + 15) < σ.sc B.sen := by
      rw [hz, e_en]; intro h
      have h' : (0 : ℤ) < I.e.num := by exact_mod_cast h
      have := (ellRI_cond I).2.2.1 he; omega
    refine XV.mono (XV.ifS_f hL (by omega) (by omega) bRn bRd hc (XV.ifS_t hL (by omega) (by omega) bz brn hc2
      (XV.ifS_f hL (by omega) (by omega) bz ben hc3
      (XV.setZ hL (x := B.o) (z := B.o + 15) (by omega) (by omega) hz)))) (by unfold ellMU; omega) ?_
    rintro σ' ⟨v, dr, F⟩
    exact fail σ' v dr F (ellRI_none (Or.inr (Or.inr he)))
  have hc3 : σ.sc (B.o + 15) < σ.sc B.sen := by
    rw [hz, e_en]
    have h' : ¬ I.e.num ≤ 0 := fun h => he ((ellRI_cond I).2.2.2 h)
    have : (0 : ℤ) < I.e.num := by omega
    exact_mod_cast this
  have hr0 : 0 < I.r := not_le.1 hr
  have he0 : 0 < I.e := not_le.1 he
  -- the constants up to `λ`
  refine XV.mono (K := (((ellJU d (ellSz I) + (ellBrU d I.m (ellSz I) Kr + bisBrU d I.m (ellSz I) Kr + 2)) + 1) + 1)
    + 2) ?_ (by unfold ellMU; omega) (fun _ h => h)
  refine XV.ifS_f hL (by omega) (by omega) bRn bRd hc ?_
  refine XV.ifS_t hL (by omega) (by omega) bz brn hc2 ?_
  refine XV.ifS_t hL (by omega) (by omega) bz ben hc3 ?_
  refine XV.seq (XV.ellJ hL (B := B) (I := I) (u := B.o + 15) (c := B.o + 75) (n0 := B.rE + 1)
    (E := 6 * ellSz I + d + 4) hB (by omega) (by omega) (by omega) (by omega) (by omega) hin hz h1
    (by rw [show B.rE + 1 + 4 = B.rE + 5 by omega]; exact hone) hd hR hr0 he0 le_rfl (by omega) (by omega))
    fun σ4 ⟨c4, j4, cR4, l4, d4, F4⟩ => ?_
  have G4 : FrameA (fun y => B.o ≤ y ∨ SR y) (fun j => B.rE ≤ j ∨ NR j) (fun b _ => B.aW ≤ b ∨ AR b) σ σ4 :=
    F4.mono (fun y h => Or.inl (by omega)) (fun j h => Or.inl (by omega)) (fun _ _ h => h.elim)
  have hin4 : EllIn B I σ4 := EllIn.frame hB hin F4 (fun y h => by omega) (fun j h => by omega) (fun _ _ h => h.elim)
  have hC4 : Ctx σ4 := hctx σ σ4 hC d4 G4
  have hz4 : σ4.sc (B.o + 15) = 0 := by rw [F4.2.1 _ (by omega)]; exact hz
  have h14 : σ4.sc (B.o + 15 + 1) = 1 := by rw [F4.2.1 _ (by omega)]; exact h1
  have hone4 : σ4.nat (B.rE + 1 + 4) = 1 := by rw [F4.1 _ (by omega)]; exact hone
  have hone5 : σ4.nat (B.rE + 5) = 1 := hone4
  have hd4 : σ4.nat B.rd = d := hin4.1
  have post : ∀ σ' : Env d, ∀ r : Option (Fin d → ℤ), ∀ e : ℕ, ellRI I = r → ellExp I = e →
      EllOut B r e σ' ∧ σ'.draws = σ4.draws ∧
        FrameA (fun y => B.o ≤ y ∨ SR y) (fun j => B.rE ≤ j ∨ NR j) (fun b _ => B.aW ≤ b ∨ AR b) σ4 σ' →
      EllOut B (ellRI I) (ellExp I) σ' ∧ σ'.draws = σ.draws ∧
        FrameA (fun y => B.o ≤ y ∨ SR y) (fun j => B.rE ≤ j ∨ NR j) (fun b _ => B.aW ≤ b ∨ AR b) σ σ' :=
    fun σ' r e hr he ⟨out, dr, F⟩ => by
      rw [hr, he]; exact ⟨out, dr.trans d4, G4.trans F⟩
  have hsa : 1 < 2 ^ ℓa := by omega
  by_cases hd2 : 2 ≤ d
  · -- ELL-R
    obtain ⟨eR, eE⟩ := ellRI_ell hR hr0 he0 hd2
    refine XV.mono (XV.ifN_t hL (by omega) (by omega) (by rw [hone5]; exact hsa) (by rw [hd4]; omega)
      (by rw [hone5, hd4]; omega)
      (XV.ellBr hL (B := B) (I := I) (P := B.o + 3) (u := B.o + 15) (c := B.o + 75) (a0 := B.aW + 2)
        (n0 := B.rE + 1) hB hav hrow hctx (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) hin4 hC4 hz4 h14 hone4 c4 j4 cR4 l4 hd2 hr0 he0 hℓ hℓa)) (by omega) ?_
    exact fun σ' h => post σ' _ _ eR eE h
  · -- BIS-R
    have hd1 : d = 1 := by omega
    obtain ⟨eR, eE⟩ := ellRI_bis hR hr0 he0 hd1
    refine XV.mono (XV.ifN_f hL (by omega) (by omega) (by rw [hone5]; exact hsa) (by rw [hd4]; omega)
      (by rw [hone5, hd4]; omega)
      (XV.bisBr hL (B := B) (I := I) (P := B.o + 3) (u := B.o + 15) (c := B.o + 75) (a0 := B.aW + 2)
        (n0 := B.rE + 1) hB hav hrow hctx (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) hin4 hC4 hz4 h14 hone4 c4 l4 hd1 hr0 he0 hℓ hℓa)) (by omega) ?_
    exact fun σ' h => post σ' _ _ eR eE h

set_option maxHeartbeats 1000000 in
/-- The rule of `xell`. -/
theorem XV.ell {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk} {I : EllI d}
    {Kr : ℕ} {rowc : XCmd} {Ctx : Env d → Prop} {SR NR AR : ℕ → Prop} (hd : 1 ≤ d)
    (hB : B.OK L 135 48 9) (hav : B.Avoid SR NR AR) (hrow : RowProv L X ℓa ℓ I B rowc Ctx SR NR AR Kr)
    (hctx : CtxOK B Ctx SR NR AR) (hin : EllIn B I σ) (hC : Ctx σ)
    (hℓ : 4500 * (ellSz I + d + 2) ≤ ℓ) (hℓa : 1000 * (d + I.m + ellSz I + 1) ^ 3 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xell L B rowc) σ (ellRU d I.m (ellSz I) Kr) (fun σ' =>
      EllOut B (ellRI I) (ellExp I) σ' ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => B.o ≤ y ∨ SR y) (fun j => B.rE ≤ j ∨ NR j) (fun b _ => B.aW ≤ b ∨ AR b) σ σ') := by
  have hB' := hB
  obtain ⟨hoS, hrN, haA, -⟩ := hB'
  obtain ⟨-, rW, -, -, -⟩ := ell_regs (m := I.m) (lam := 0) (by omega) hℓa
  have hsa : 1 < 2 ^ ℓa := by omega
  have hℓ3 : 3 ≤ ℓ := by omega
  refine XV.mono (K := 1 + (1 + (1 + ellMU d I.m (ellSz I) Kr))) ?_ (by unfold ellRU; omega) (fun _ h => h)
  refine XV.seq (XV.sconstA hL (x := B.o + 15) (by omega) 0 (small_lt (by norm_num) hℓ3))
    fun σ1 ⟨v1, d1, F1⟩ => ?_
  refine XV.seq (XV.sconstA hL (x := B.o + 16) (by omega) 1 (small_lt (by norm_num) hℓ3))
    fun σ2 ⟨v2, d2, F2⟩ => ?_
  refine XV.seq (XV.nconstA hL (i := B.rE + 5) (by omega) 1 hsa) fun σ3 ⟨v3, d3, F3⟩ => ?_
  have G : FrameA (fun y => y = B.o + 15 ∨ y = B.o + 16) (fun j => j = B.rE + 5) (fun _ _ => False) σ σ3 :=
    ((F1.mono (fun y h => Or.inl h) (fun _ h => h.elim) (fun _ _ h => h)).trans
      (F2.mono (fun y h => Or.inr h) (fun _ h => h.elim) (fun _ _ h => h))).trans
      (F3.mono (fun _ h => h.elim) (fun _ h => h) (fun _ _ h => h))
  have z3 : σ3.sc (B.o + 15) = 0 := by rw [F3.2.1 _ id, F2.2.1 _ (by omega), v1, Int.cast_zero]
  have o3 : σ3.sc (B.o + 16) = 1 := by rw [F3.2.1 _ id, v2, Int.cast_one]
  have dr3 : σ3.draws = σ.draws := by rw [d3, d2, d1]
  have G' : FrameA (fun y => B.o ≤ y ∨ SR y) (fun j => B.rE ≤ j ∨ NR j) (fun b _ => B.aW ≤ b ∨ AR b) σ σ3 :=
    G.mono (fun y h => Or.inl (by omega)) (fun j h => Or.inl (by omega)) (fun _ _ h => h.elim)
  have hin3 : EllIn B I σ3 := EllIn.frame hB hin G (fun y h => by omega) (fun j h => by omega) (fun _ _ h => h.elim)
  refine XV.mono (XV.ellMain hL hd hB hav hrow hctx hin3 (hctx σ σ3 hC dr3 G') z3 o3 v3 hℓ hℓa) le_rfl ?_
  rintro σ' ⟨out, dr, F⟩
  exact ⟨out, dr.trans dr3, G'.trans F⟩

/-! ## The work term -/

theorem ellRU_mono {d m s Kr V : ℕ} (hd : d ≤ V) (hm : m ≤ V) (hs : s ≤ V) (hK : Kr ≤ V) :
    ellRU d m s Kr ≤ ellRU V V V V := by
  unfold ellRU ellMU ellJU ellBrU bisBrU ellKb bisKb testK tKA tE1 tKR tE2 tKQ tE3 tKV tKK tKE ellE
  gcongr

theorem ellRU_poly {V : ℕ} (hV : 1 ≤ V) : ellRU V V V V ≤ 10 ^ 9 * V ^ 5 := by
  have h1 : V ≤ V ^ 5 := Nat.le_self_pow (by norm_num) V
  have h2 : V ^ 2 ≤ V ^ 5 := Nat.pow_le_pow_right hV (by norm_num)
  have h3 : V ^ 3 ≤ V ^ 5 := Nat.pow_le_pow_right hV (by norm_num)
  have h4 : V ^ 4 ≤ V ^ 5 := Nat.pow_le_pow_right hV (by norm_num)
  have h0 : 1 ≤ V ^ 5 := Nat.one_le_pow _ _ (by omega)
  unfold ellRU ellMU ellJU ellBrU bisBrU ellKb bisKb testK tKA tE1 tKR tE2 tKQ tE3 tKV tKK tKE ellE
  ring_nf
  linarith

theorem ellRU_le (d m s Kr : ℕ) : ellRU d m s Kr ≤ 10 ^ 9 * (d + m + s + Kr + 1) ^ 5 :=
  (ellRU_mono (V := d + m + s + Kr + 1) (by omega) (by omega) (by omega) (by omega)).trans (ellRU_poly (by omega))

/-- **Interface II, the projection routine** (`EllRule`): `xell`, within `10^9 W^5` units, with 135 slots,
48 registers and 9 arrays above the bases of its block. -/
theorem ellRule : EllRule := by
  refine ⟨xell, 10 ^ 9, 5, 135, 48, 9, ?_⟩
  intro d L X ℓa ℓ B I rowc Ctx SR NR AR Kr σ hd hL hB hav hrow hctx hin hC hℓ hℓa
  have hW : 1 ≤ d + I.m + ellSz I + 1 := by omega
  have h5 : d + I.m + ellSz I + 1 ≤ (d + I.m + ellSz I + 1) ^ 5 := Nat.le_self_pow (by norm_num) _
  have h35 : (d + I.m + ellSz I + 1) ^ 3 ≤ (d + I.m + ellSz I + 1) ^ 5 := Nat.pow_le_pow_right hW (by norm_num)
  exact XV.mono (XV.ell hL hd hB hav hrow hctx hin hC (by omega) (by omega)) (ellRU_le d I.m (ellSz I) Kr)
    (fun _ h => h)

end AdversarialBco.Bit.Transfer
