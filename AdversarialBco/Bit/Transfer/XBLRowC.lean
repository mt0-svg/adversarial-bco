/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLRowS

@[expose] public section

/-!
# The row provider of BL, part 3: the columns

With the cleared row `â` in the array `12` (common denominator `P`) and `D₀ = D_S P` in the slot `107`, the entry `q`
of `α̃ = A_Sᵀ a` is `N_q / D₀`, `N_q = ∑_l AS(q + d l) â_l` (the numerators of `A_S` in the array `aAS`, row-major).
`xcols` computes, for every `q < d`, the reduced pair `N_q / g_q`, `D₀ / g_q` (`g_q = gcd(N_q, D₀)`) into the cells
`q` of the arrays `13`, `14`, and the product of the reduced denominators into the slot `116`.
-/

namespace AdversarialBco.Bit.Transfer.BLM.RowM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer.RowP

variable {d : ℕ}

/-- The numerator `N_q = ∑_l AS(q + d l) â_l` of the entry `q` of `A_Sᵀ a` over `D_S P`. -/
def colN (d : ℕ) (xa ah : ℕ → ℤ) (q : ℕ) : ℤ := ∑ l ∈ Finset.range d, xa (q + d * l) * ah l

/-- The gcd of `N_q` and `D₀`. -/
def colG (d : ℕ) (xa ah : ℕ → ℤ) (D0 : ℤ) (q : ℕ) : ℤ := (Int.gcd (colN d xa ah q) D0 : ℤ)

theorem abs_sum_mul_le {Xv Yv : ℕ → ℤ} {N E : ℕ} (bX : ∀ k < N, |Xv k| ≤ 2 ^ E) (bY : ∀ k < N, |Yv k| ≤ 2 ^ E) :
    |∑ j ∈ Finset.range N, Xv j * Yv j| ≤ N * 2 ^ (2 * E) := by
  have bXY : ∀ k < N, |Xv k * Yv k| ≤ (2 : ℤ) ^ (2 * E) := fun k hk => by
    rw [abs_mul]
    calc |Xv k| * |Yv k| ≤ 2 ^ E * 2 ^ E := mul_le_mul (bX k hk) (bY k hk) (abs_nonneg _) (by positivity)
      _ = 2 ^ (2 * E) := by ring
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have := Finset.sum_le_card_nsmul (Finset.range N) (fun j => |Xv j * Yv j|) ((2 : ℤ) ^ (2 * E))
    (fun j hj => bXY j (by rw [Finset.mem_range] at hj; omega))
  simpa using this

/-- One column `q` (register `41`): `40 := q`, `108 := N_q`, its reduced pair in `114`, `115`, stored in the cells
`q` of the arrays `13`, `14` and `116 := 116 · D₀ / g_q`. -/
def xcolBody (L : Layout) : XCmd :=
  .seq (.prim (.frag (.nadd 40 41 38))) (.seq (xsdot L sZ 108 109 110 aAS 12 40 rD 33 rD rOne)
    (.seq (xred L sZ 108 107 111 112 113 114 115) (.seq (toX (VL.aset L 13 41 114))
      (.seq (toX (VL.aset L 14 41 115)) (toX (VL.sop2 L .mul 116 116 115))))))

/-- The columns: `116 := 1`, then the columns `q < d`. -/
def xcols (L : Layout) : XCmd := .seq (toX (VL.sconst L 116 ((1 : ℤ) : ℚ))) (xforN 41 rD rOne (xcolBody L))

/-- The units of one column. -/
def colKb (d s : ℕ) : ℕ := 1 + (sdotUnits d + (redUnits s + (2 + (2 + 1))))

/-- The units of the columns. -/
def colUnits (d s : ℕ) : ℕ := 1 + (d * (colKb d s + 3) + 3)

theorem two_mul_le_of_pow {d t s : ℕ} (hd : 1 ≤ d) (h : d * 2 ^ (2 * t) ≤ 2 ^ s) : 2 * t ≤ s := by
  have h1 : 2 ^ (2 * t) ≤ 2 ^ s := le_trans (Nat.le_mul_of_pos_left _ hd) h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1

theorem prod_den_le {D0 : ℤ} {s q : ℕ} (_hD0 : 0 < D0) (bD0 : D0 ≤ 2 ^ s) (f : ℕ → ℤ)
    (hf : ∀ j < q, 1 ≤ D0 / f j ∧ D0 / f j ≤ D0) :
    1 ≤ ∏ j ∈ Finset.range q, D0 / f j ∧ ∏ j ∈ Finset.range q, D0 / f j ≤ 2 ^ (s * q) := by
  obtain ⟨h1, h2⟩ := prod_range_abs_le (fun j => D0 / f j) (2 ^ s) (one_le_pow₀ (by norm_num)) q
    (fun j hj => ⟨(hf j hj).1, (hf j hj).2.trans bD0⟩)
  exact ⟨h1, by rw [pow_mul]; exact h2⟩

set_option maxHeartbeats 4000000 in
/-- **The columns**: the cells `q < d` of the arrays `13`, `14` end as `N_q / g_q`, `D₀ / g_q`, the slot `116` as
`∏_{q < d} D₀ / g_q`; only the slots `108..116`, the registers `33`, `40`, `41` and the cells `q < d` of the arrays
`13`, `14` change. -/
theorem XV.cols {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hNS : 128 ≤ L.NS)
    (hNN : 64 ≤ L.NN) (hNA : 16 ≤ L.NA) {t s : ℕ} {xa ah : ℕ → ℤ} {D0 : ℤ} (hD : σ.nat rD = d)
    (h1 : σ.nat rOne = 1) (h38 : σ.nat 38 = 0) (hz : σ.sc sZ = 0) (h107 : σ.sc 107 = D0) (hD0 : 0 < D0)
    (bD0 : D0 ≤ 2 ^ s) (hxa : ∀ k < d * d, σ.arr aAS k = xa k) (hah : ∀ l < d, σ.arr 12 l = ah l)
    (bxa : ∀ k < d * d, |xa k| ≤ 2 ^ t) (bah : ∀ l < d, |ah l| ≤ 2 ^ t) (hts : d * 2 ^ (2 * t) ≤ 2 ^ s)
    (hs : s * d + s + 1 < ℓ) (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xcols L) σ (colUnits d s) (fun σ' =>
      (∀ q < d, σ'.arr 13 q = ((colN d xa ah q / colG d xa ah D0 q : ℤ) : ℝ) ∧
        σ'.arr 14 q = ((D0 / colG d xa ah D0 q : ℤ) : ℝ)) ∧
      σ'.sc 116 = ((∏ q ∈ Finset.range d, D0 / colG d xa ah D0 q : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => 108 ≤ y ∧ y ≤ 116) (fun j => j = 33 ∨ j = 40 ∨ j = 41)
        (fun a k => (a = 13 ∨ a = 14) ∧ k < d) σ σ') := by
  have hla := hL.1
  have hd1 : d < 2 ^ ℓa := by nlinarith
  have hs0 : s + 1 < ℓ := by nlinarith
  have h1l : |(1 : ℤ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  refine XV.seq (XV.constI hL (x := 116) (by omega) 1 h1l) fun σ0 e0 => ?_
  subst e0
  let J : ℕ → Env d → Prop := fun q σ' =>
    (∀ q' < q, σ'.arr 13 q' = ((colN d xa ah q' / colG d xa ah D0 q' : ℤ) : ℝ) ∧
        σ'.arr 14 q' = ((D0 / colG d xa ah D0 q' : ℤ) : ℝ)) ∧
      σ'.sc 116 = ((∏ q' ∈ Finset.range q, D0 / colG d xa ah D0 q' : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => 108 ≤ y ∧ y ≤ 116) (fun j => j = 33 ∨ j = 40 ∨ j = 41)
        (fun a k => (a = 13 ∨ a = 14) ∧ k < d) σ σ'
  have F0' : FrameA (fun y => 108 ≤ y ∧ y ≤ 116) (fun j => j = 33 ∨ j = 40 ∨ j = 41)
      (fun a k => (a = 13 ∨ a = 14) ∧ k < d) σ (σ.setSc 116 ((1 : ℤ) : ℝ)) :=
    (FrameA.refl _ _ _ σ).setSc ⟨by norm_num, by norm_num⟩ _
  refine XV.mono (XV.forN hL (i := 41) (n := rD) (one := rOne) (body := xcolBody L) (by omega) (by rwgo)
    (by rwgo) (by rwgo) (by rwgo) d (colKb d s) hd1 J _ (by rwenv; exact hD)
    (by rwenv; exact h1)
    ⟨fun q' h => absurd h (Nat.not_lt_zero _), by rwenv; simp, by rwenv,
      F0'.setNat (Or.inr (Or.inr rfl)) _⟩ ?_) le_rfl fun σ' ⟨hJ, _⟩ => hJ
  intro q hq σ' ⟨hA, hR, hdr, hF⟩ hq41 hqD hq1
  have hd0 : 1 ≤ d := by omega
  have h2t : 2 * t < ℓ := by have := two_mul_le_of_pow hd0 hts; omega
  have hsl : s < ℓ := by omega
  have hdl : d * 2 ^ (2 * t) < 2 ^ ℓ := lt_of_le_of_lt hts (Nat.pow_lt_pow_right (by norm_num) hsl)
  -- the cells that the frame keeps
  have e38 : σ'.nat 38 = 0 := by rw [hF.1 38 (by omega), h38]
  have ez : σ'.sc sZ = 0 := by rw [hF.2.1 sZ (by rwgo), hz]
  have e107 : σ'.sc 107 = D0 := by rw [hF.2.1 107 (by omega), h107]
  have exa : ∀ k < d * d, σ'.arr aAS k = xa k := fun k hk => by
    rw [hF.2.2.1 aAS k (by rwgo), hxa k hk]
  have eah : ∀ l < d, σ'.arr 12 l = ah l := fun l hl => by rw [hF.2.2.1 12 l (by omega), hah l hl]
  -- `40 := q`
  refine XV.seq (XV.nadd hL (i := 40) (a := 41) (b := 38) (by omega) (by omega) (by omega)
    (by rw [hq41]; omega) (by rw [e38]; omega)) fun σ1 e1 => ?_
  subst e1
  -- `108 := N_q`
  have bN : |colN d xa ah q| ≤ 2 ^ s :=
    (abs_sum_mul_le (Xv := fun l => xa (q + d * l)) (Yv := ah) (fun l hl => bxa _ (by nlinarith)) bah).trans
      (by exact_mod_cast hts)
  refine XV.seq (XV.sdot hL (z := sZ) (r := 108) (t1 := 109) (t2 := 110) (ax := aAS) (ay := 12) (nr := 40)
    (nst := rD) (nk := 33) (nn := rD) (none := rOne) (N := d) (base := q) (st := d) (E := t)
    (Xv := fun l => xa (q + d * l)) (Yv := ah) (by rwgo) (by omega) (by omega) (by omega) (by decide)
    (by rwgo) (by omega) (by omega) (by rwgo) (by omega) (by rwgo) (by rwgo) (by decide) (by decide) (by decide)
    (by rwenv; exact ez) (by rwenv; exact hqD) (by rwenv; exact hq1) (by rwenv; rw [hq41, e38]; rfl)
    (by rwenv; exact hqD) (fun l hl => by rwenv; exact exa _ (by nlinarith)) (fun l hl => by rwenv; exact eah l hl)
    (fun l hl => by unfold asz; nlinarith) (by unfold asz; nlinarith) (fun l hl => bxa _ (by nlinarith)) bah h2t
    hdl hd1 (by nlinarith) hd1) fun σ2 ⟨s1, s2, s3, s4⟩ => ?_
  -- the reduced pair in `114`, `115`
  have z2 : σ2.sc sZ = 0 := by rw [s4.2.1 sZ (by rwgo)]; rwenv; exact ez
  have d2 : σ2.sc 107 = D0 := by rw [s4.2.1 107 (by omega)]; rwenv; exact e107
  refine XV.seq (XV.red hL (z := sZ) (sN := 108) (sD := 107) (sa := 111) (sb := 112) (st := 113) (snum := 114)
    (sden := 115) (by rwgo) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by decide) (N := colN d xa ah q) (D := D0) (s := s) z2 s1 d2 hD0 bN bD0 hs0) fun σ3 ⟨r1, r2, r3, r4⟩ => ?_
  obtain ⟨g1, g2, g3, g4⟩ := red_bounds (colN d xa ah q) D0 hD0
  -- what `σ3` keeps of `σ'`
  have n3 : ∀ j, j ≠ 33 → j ≠ 40 → σ3.nat j = σ'.nat j := fun j h33 h40 => by
    rw [r4.1 j not_false, s4.1 j (by omega)]; rwenv
  have a3 : ∀ a k, σ3.arr a k = σ'.arr a k := fun a k => by
    rw [r4.2.2.1 a k not_false, s4.2.2.1 a k not_false]; rwenv
  have q3 : σ3.nat 41 = q := by rw [n3 41 (by omega) (by omega), hq41]
  have g2' : |colN d xa ah q / colG d xa ah D0 q| ≤ |colN d xa ah q| := g2
  have g3' : 1 ≤ D0 / colG d xa ah D0 q := g3
  have g4' : D0 / colG d xa ah D0 q ≤ D0 := g4
  have b114 : |(colN d xa ah q / colG d xa ah D0 q : ℤ)| ≤ 2 ^ s := g2'.trans bN
  have b115 : |(D0 / colG d xa ah D0 q : ℤ)| ≤ 2 ^ s := by
    rw [abs_of_pos (by omega)]; exact g4'.trans bD0
  refine XV.seq (XV.aset hL (a := 13) (i := 41) (x := 114) (by omega) (by omega) (by omega)
    (by rw [q3]; unfold asz; nlinarith) (by rw [r1]; exact XV.abs_int_lt (absI_le_pow b114 hsl)))
    fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.aset hL (a := 14) (i := 41) (x := 115) (by omega) (by omega) (by omega)
    (by rwenv; rw [q3]; unfold asz; nlinarith)
    (by rwenv; rw [r2]; exact XV.abs_int_lt (absI_le_pow b115 hsl))) fun σ5 e5 => ?_
  subst e5
  -- `116 := 116 · D₀ / g_q`
  obtain ⟨p1, p2⟩ := prod_den_le (q := q) hD0 bD0 (colG d xa ah D0) fun j hj => by
    obtain ⟨_, _, h3, h4⟩ := red_bounds (colN d xa ah j) D0 hD0
    exact ⟨h3, h4⟩
  have e116 : σ3.sc 116 = ((∏ q' ∈ Finset.range q, D0 / colG d xa ah D0 q' : ℤ) : ℝ) := by
    rw [r4.2.1 116 (by omega), s4.2.1 116 (by omega)]; rwenv; exact hR
  have bq : s * q + s ≤ s * d + s := by nlinarith
  have bprod : |(∏ q' ∈ Finset.range q, D0 / colG d xa ah D0 q' : ℤ)| ≤ 2 ^ (s * q) := by
    rw [abs_of_pos (by omega)]; exact p2
  refine XV.mono (XV.mulI hL (x := 116) (a := 116) (b := 115) (by omega) (by omega) (by omega)
    (u := ∏ q' ∈ Finset.range q, D0 / colG d xa ah D0 q') (v := D0 / colG d xa ah D0 q)
    (by rwenv; exact e116) (by rwenv; exact r2) (absI_le_pow bprod (by nlinarith)) (absI_le_pow b115 hsl)
    (absI_le_pow (absI_mul_le bprod b115) (by nlinarith))) le_rfl fun σ6 e6 => ?_
  subst e6
  refine ⟨by rwenv; exact q3, by rwenv; rw [n3 rD (by rwgo) (by rwgo)]; exact hqD,
    by rwenv; rw [n3 rOne (by rwgo) (by rwgo)]; exact hq1, ?_, ?_, ?_, ?_⟩
  · intro q' hq'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hq' with h | h
    · simp only [Env.setNat_arr, Env.setSc_arr, Env.setArr_nat, Env.setArr_sc, Env.setArr_arr, q3,
        show q' ≠ q by omega, and_false, ite_false, a3]
      exact hA q' h
    · subst h
      simp only [Env.setNat_arr, Env.setSc_arr, Env.setArr_nat, Env.setArr_sc, Env.setArr_arr, q3,
        show (13 : ℕ) ≠ 14 by decide, show (14 : ℕ) ≠ 13 by decide, false_and, and_self,
        ite_true, ite_false, r1, r2]
      exact ⟨rfl, rfl⟩
  · rwenv; rw [Finset.prod_range_succ]
  · rwenv; rw [r3, s3]; rwenv; exact hdr
  · have F : FrameA (fun y => 108 ≤ y ∧ y ≤ 116) (fun j => j = 33 ∨ j = 40 ∨ j = 41)
        (fun a k => (a = 13 ∨ a = 14) ∧ k < d) σ' σ3 :=
      (((FrameA.refl _ _ _ σ').setNat (Or.inr (Or.inl rfl)) _).trans
        (s4.mono (fun y h => by omega) (fun j h => by omega) (fun _ _ h => h.elim))).trans
        (r4.mono (fun y h => by omega) (fun _ h => h.elim) (fun _ _ h => h.elim))
    exact ((((hF.trans F).setArr ⟨Or.inl rfl, by omega⟩ _).setArr ⟨Or.inr rfl, by rwenv; omega⟩ _).setSc
      ⟨by omega, by omega⟩ _).setNat (Or.inr (Or.inr rfl)) _

end AdversarialBco.Bit.Transfer.BLM.RowM
