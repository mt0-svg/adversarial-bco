/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBisLoop
public import AdversarialBco.Bit.Transfer.XEllLem

@[expose] public section

/-!
# The constants of ELL-R and BIS-R on the machine

Before the loops, the projection routine computes from the integer problem in its block: `R̄ = ⌈R⌉₊`, the trace of
`P`, `|f|₁`, the fraction `Nx / Dx = 1/(θ min(r₀, 1))` of `ellJ_eq`, then `j = lg ⌈Nx / Dx⌉`, `lg R̄` and
`λ = lg R̄ + j` in registers. The logarithms come from the doubling loop `xclogS` on a slot.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## The logarithm of a slot -/

/-- `w := 1`, `c := 0`; while `w < x`: `w := w + w`, `c := c + 1`. It ends with `c = lg x`. -/
def xclogS (L : Layout) (w x c one : ℕ) : XCmd :=
  .seq (toX (VL.sconst L w 1)) (.seq (.prim (.frag (.nconst c 0)))
    (xwhileS L w x (.seq (xset L w w w) (.prim (.frag (.nadd c c one))))))

set_option maxHeartbeats 1000000 in
/-- The rule of `xclogS`: for `0 ≤ X ≤ 2^G` in the slot `x`, the register `c` gets `lg X`, within `4 G + 4` units,
changing only `w` and `c`. -/
theorem XV.clogS {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {w x c one G : ℕ} {v : ℤ}
    (hw : w < L.NS) (hx : x < L.NS) (hc : c < L.NN) (ho : one < L.NN) (hwx : w ≠ x) (hco : c ≠ one)
    (hv : σ.sc x = v) (hv0 : 0 ≤ v) (hvG : v ≤ 2 ^ G) (h1 : σ.nat one = 1) (hGa : G < 2 ^ ℓa) (hGl : G < ℓ) :
    XRunsB L X ℓa ℓ (xclogS L w x c one) σ (4 * G + 4) (fun σ' =>
      σ'.nat c = Nat.clog 2 v.toNat ∧ σ'.draws = σ.draws ∧
      FrameP (fun y => y = w) (fun j => j = c) σ σ') := by
  have hpow : ∀ k ≤ G, |(2 : ℝ) ^ k| < 2 ^ ℓ := fun k hk => by
    rw [abs_of_nonneg (by positivity)]
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  have hvℓ : |(v : ℝ)| < 2 ^ ℓ := by
    exact XV.abs_int_lt (lt_of_le_of_lt (by rw [abs_of_nonneg hv0]; exact hvG)
      (pow_lt_pow_right₀ (by norm_num) hGl))
  let I : ℕ → Env d → Prop := fun t σ' => σ'.sc w = 2 ^ t ∧ σ'.nat c = t ∧ σ'.sc x = v ∧ σ'.nat one = 1 ∧
    σ'.draws = σ.draws ∧ FrameP (fun y => y = w) (fun j => j = c) σ σ' ∧ t ≤ G ∧ (t = 0 ∨ (2 : ℤ) ^ (t - 1) < v)
  refine XV.mono (XV.seq (K₁ := 1) (K₂ := 1 + ((G - 0) * (2 + 2) + 2))
    (XV.sconst hL hw 1 rfl (by simpa using hpow 0 (Nat.zero_le _))) (fun σ1 e1 => ?_)) (by omega) (fun _ h => h)
  subst e1
  refine XV.seq (XV.nconst hL hc 0 (by positivity)) fun σ2 e2 => ?_
  subst e2
  have I0 : I 0 ((σ.setSc w ((1 : ℚ) : ℝ)).setNat c 0) := by
    refine ⟨by simp, by simp, by simp [Ne.symm hwx, hv], by simp [Ne.symm hco, h1], by simp,
      ((FrameP.refl (fun y => y = w) (fun j => j = c) σ).setSc rfl _).setNat rfl _, Nat.zero_le _, Or.inl rfl⟩
  refine XV.mono (XV.whileS hL hw hx I G 2 ?_ ?_ ?_ 0 _ I0) le_rfl ?_
  · rintro t σ' ⟨e1, -, e3, -, -, -, ht, -⟩
    exact ⟨by rw [e1]; exact hpow t ht, by rw [e3]; exact hvℓ⟩
  · rintro t σ' ⟨e1, -, e3, -, -, -, -, -⟩ hlt
    rw [e1, e3] at hlt
    by_contra hG
    have : (2 : ℝ) ^ G ≤ 2 ^ t := pow_le_pow_right₀ (by norm_num) (by omega)
    have : (v : ℝ) ≤ 2 ^ G := by exact_mod_cast hvG
    linarith
  · rintro t σ' ⟨e1, e2, e3, e4, e5, e6, ht, -⟩ hlt
    rw [e1, e3] at hlt
    have hlt' : (2 : ℤ) ^ t < v := by exact_mod_cast hlt
    have htG : t < G := by
      by_contra hG
      have : (2 : ℤ) ^ G ≤ 2 ^ t := pow_le_pow_right₀ (by norm_num) (by omega)
      omega
    have hev : RealRAM.Op2.eval .add (σ'.sc w) (σ'.sc w) = 2 ^ (t + 1) := by
      rw [e1, pow_succ]; simp only [RealRAM.Op2.eval]; ring
    refine XV.seq (K₂ := 1) (XV.sop2 hL hw hw hw .add (by intro h; cases h) (by rw [e1]; exact hpow t ht)
      (by rw [e1]; exact hpow t ht) (by rw [hev]; exact hpow (t + 1) htG)) fun σ3 e3' => ?_
    subst e3'
    refine XV.mono (XV.nadd hL hc hc ho (by simp only [Env.setSc_nat, e2]; omega)
      (by simp only [Env.setSc_nat, e4]; omega)) le_rfl
      fun σ4 e4' => ?_
    subst e4'
    refine ⟨by simp [hev], by simp [e2, e4], by simp [Ne.symm hwx, e3], by simp [Ne.symm hco, e4],
      by simp [e5], (e6.setSc rfl _).setNat rfl _, htG, Or.inr (by simpa using hlt')⟩
  · rintro σ' ⟨t, ⟨e1, e2, e3, -, e5, e6, -, h0⟩, hex⟩
    rw [e1, e3, not_lt] at hex
    have hex' : v ≤ 2 ^ t := by exact_mod_cast hex
    refine ⟨?_, e5, e6⟩
    rw [e2, clog_spec v.toNat t (by rw [← Nat.cast_le (α := ℤ), Int.toNat_of_nonneg hv0]; exact_mod_cast hex') ?_]
    rcases h0 with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (by rw [← Nat.cast_lt (α := ℤ), Int.toNat_of_nonneg hv0]; exact_mod_cast h0)

/-! ## Lemmas of the sums -/


theorem abs_eq_sign (x : ℤ) : |x| = x * (1 + 2 * (x / (x * x + 1))) := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    have hdiv : x / (x * x + 1) = 0 := by
      apply Int.ediv_eq_zero_of_lt hx
      nlinarith
    rw [hdiv]
    ring
  · have hx' : x < 0 := by omega
    rw [abs_of_neg hx']
    have hdiv : x / (x * x + 1) = -1 := by
      have hpos : x * x + 1 ≠ 0 := by nlinarith
      have h_eq : (x + x * x + 1) + (x * x + 1) * (-1) = x := by ring
      have h_nonneg : 0 ≤ x + x * x + 1 := by
        have : x ≤ -1 := by omega
        nlinarith
      have h_lt : x + x * x + 1 < |x * x + 1| := by
        have hpos' : 0 < x * x + 1 := by nlinarith
        rw [abs_of_pos hpos']
        nlinarith
      rcases ((Int.ediv_emod_unique'' hpos).mpr ⟨h_eq, h_nonneg, h_lt⟩) with ⟨hdiv, _⟩
      exact hdiv
    rw [hdiv]
    ring

theorem trace_sum {d : ℕ} (P : Matrix (Fin d) (Fin d) ℤ) :
    ∑ k ∈ Finset.range d, (if h : k < d then P ⟨k, h⟩ ⟨k, h⟩ else 0) = P.trace := by
  simp [Matrix.trace, Finset.sum_fin_eq_sum_range]

theorem sum_vext_abs {d : ℕ} (f : Fin d → ℤ) :
    ∑ k ∈ Finset.range d, |vext f k| = ∑ i, |f i| := by
  calc
    ∑ k ∈ Finset.range d, |vext f k|
        = ∑ i : Fin d, |vext f (i.val)| := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => |vext f k|) d]
    _ = ∑ i : Fin d, |f i| := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      simp [vext, i.is_lt]

theorem abs_sum_range_le (F : ℕ → ℤ) (B : ℤ) (h : ∀ j, |F j| ≤ B) (k : ℕ) :
    |∑ j ∈ Finset.range k, F j| ≤ k * B := by
  calc
    |∑ j ∈ Finset.range k, F j| ≤ ∑ j ∈ Finset.range k, |F j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range k, B := Finset.sum_le_sum fun j hj => h j
    _ = k * B := by simp

/-! ## `R̄`, the trace of `P`, `|f|₁` -/

/-- `|x|` of the cell `a[nat i]` without a test, as `x (1 + 2 (x div (x² + 1)))`; `1` in the slot `o`. -/
def ieAbs (a i o : ℕ) : IE :=
  .op .mul (.arr a i) (.op .add (.sc o)
    (.op .add (.ediv (.arr a i) (.op .add (.op .mul (.arr a i) (.arr a i)) (.sc o)))
      (.ediv (.arr a i) (.op .add (.op .mul (.arr a i) (.arr a i)) (.sc o)))))

/-- `⌈a / b⌉ = (a + b - 1) div b` for `b > 0`; `1` in the slot `o`. -/
def ieCeil (a b o : ℕ) : IE := .ediv (.op .sub (.op .add (.sc a) (.sc b)) (.sc o)) (.sc b)

/-- `R̄` into `c`, `tr P` into `c + 1`, `|f|₁` into `c + 2`; registers `n0 + 11, n0 + 12, n0 + 13`, scratch from
`c + 24`; `0, 1` in `u, u + 1`, `1` in the register `n0 + 4`. -/
def xellJa (L : Layout) (B : EllBlk) (u c n0 : ℕ) : XCmd :=
  .seq ((ieCeil B.sRn B.sRd (u + 1)).code L u c (c + 24))
  (.seq (.prim (.frag (.nconst (n0 + 11) 0)))
  (.seq (.prim (.frag (.nadd (n0 + 12) B.rd (n0 + 4))))
  (.seq (xfoldE L u (c + 1) (c + 24) (.arr B.aP (n0 + 11)) (n0 + 11) (n0 + 12) (n0 + 13) B.rd (n0 + 4))
  (.seq (.prim (.frag (.nconst (n0 + 11) 0)))
    (xfoldE L u (c + 2) (c + 24) (ieAbs B.af (n0 + 11) (u + 1)) (n0 + 11) (n0 + 4) (n0 + 13) B.rd (n0 + 4))))))

theorem ellRn_le {I : EllI d} {F : ℕ} (hσF : ellSz I ≤ F) : |I.R.num| ≤ 2 ^ F :=
  (abs_le_sz (ellMx_le I).2.2.2.2.2.2.2.2.1).trans (pow_le_pow_right₀ (by norm_num) hσF)

theorem ellRd_le {I : EllI d} {F : ℕ} (hσF : ellSz I ≤ F) : |(I.R.den : ℤ)| ≤ 2 ^ F :=
  (abs_le_sz' (ellMx_le I).2.2.2.2.2.2.2.2.2.1).trans (pow_le_pow_right₀ (by norm_num) hσF)

theorem one_le_two_pow (E : ℕ) : |(1 : ℤ)| ≤ 2 ^ E := by
  rw [abs_one]; exact one_le_pow₀ (by norm_num)

set_option maxHeartbeats 4000000 in
/-- The rule of `xellJa`. -/
theorem XV.ellJa {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk} {I : EllI d}
    {nS nN nA u c n0 E : ℕ} (hB : B.OK L nS nN nA) (hu : B.o ≤ u) (hc : u + 2 ≤ c) (hS : c + 60 ≤ L.NS)
    (hn : B.rE ≤ n0) (hN : n0 + 14 ≤ L.NN) (hin : EllIn B I σ) (hz : σ.sc u = 0) (h1 : σ.sc (u + 1) = 1)
    (hone : σ.nat (n0 + 4) = 1) (hR : ¬ I.R < 1) (hE : ellSz I + d + 1 ≤ E) (hℓ : 2 * E + 3 < ℓ) :
    XRunsB L X ℓa ℓ (xellJa L B u c n0) σ (38 * d + 18) (fun σ' =>
      σ'.sc c = ((I.Rb : ℤ) : ℝ) ∧ σ'.sc (c + 1) = ((I.P.trace : ℤ) : ℝ) ∧
      σ'.sc (c + 2) = ((∑ i, |I.f i| : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => c ≤ y) (fun j => n0 + 11 ≤ j ∧ j ≤ n0 + 13) (fun _ _ => False) σ σ') := by
  obtain ⟨hNS, hNN, hNA, hrd, -, -, -, hsRn, hsRd, -, -, -, -, -, -, haP, haf⟩ := hB
  obtain ⟨e_d, -, -, -, e_Rn, e_Rd, -, -, -, -, -, -, e_P, e_f⟩ := hin
  have hda := asz_lt hL (show B.aP < L.NA by omega)
  have hσE : ellSz I ≤ E := by omega
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  have bRn := ellRn_le (I := I) hσE
  have bRd := ellRd_le (I := I) hσE
  have hRnd : (I.R.den : ℤ) ≤ I.R.num := by
    have := (ellRI_cond I).1; rw [this] at hR; omega
  have hRd0 : (0 : ℤ) < I.R.den := by exact_mod_cast I.R.pos
  have eRb : (I.R.num + I.R.den - 1) / (I.R.den : ℤ) = (I.Rb : ℤ) := by
    rw [ellRb_eq, Int.toNat_of_nonneg (Int.ediv_nonneg (by omega) hRd0.le)]
  have hdE : (d : ℤ) * 2 ^ ellSz I ≤ 2 ^ E := by
    have h1 : (d : ℤ) ≤ 2 ^ d := by exact_mod_cast (Nat.lt_two_pow_self).le
    calc (d : ℤ) * 2 ^ ellSz I ≤ 2 ^ d * 2 ^ ellSz I := by gcongr
      _ = 2 ^ (d + ellSz I) := by rw [pow_add]
      _ ≤ 2 ^ E := pow_le_pow_right₀ (by norm_num) (by omega)
  have hEℓ : (2 : ℤ) ^ E < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) (by omega)
  -- `R̄`
  refine XV.mono (K := 7 + (1 + (1 + ((d * (2 + 5) + 4) + (1 + (d * (26 + 5) + 4)))))) ?_ (by ring_nf; omega)
    (fun _ h => h)
  refine XV.seq (XV.ieRun (E := E) (e := ieCeil B.sRn B.sRd (u + 1))
    (v := (I.Rb : ℤ)) (ℓ := ℓ) (X := X) hL (z := u) (x := c) (t := c + 24)
    (by simp only [ieCeil, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega)
    (by omega) (by omega) (by simp only [ieCeil, IE.scr]; omega) hz
    (by
      simp only [ieCeil, IE.Leaves]
      exact ⟨⟨⟨⟨_, e_Rn, bRn⟩, ⟨_, by rw [e_Rd, Int.cast_natCast], bRd⟩⟩, ⟨1, by rw [h1, Int.cast_one],
        one_le_two_pow E⟩⟩, ⟨_, by rw [e_Rd, Int.cast_natCast], bRd⟩⟩)
    (by simp only [ieCeil, IE.top, IE.mag]; omega)
    (by
      simp only [ieCeil, IE.eval, RealRAM.Op2.eval, e_Rn, e_Rd, h1]
      rw [show (I.R.num : ℝ) + (I.R.den : ℝ) - 1 = ((I.R.num + I.R.den - 1 : ℤ) : ℝ) by push_cast; ring,
        Int.floor_intCast, show (I.R.den : ℝ) = ((I.R.den : ℤ) : ℝ) by norm_cast, Int.floor_intCast, eRb]))
    fun σ1 ⟨v1, _, d1, F1⟩ => ?_
  have z1 : σ1.sc u = 0 := by rw [F1.2.1 _ (by omega), hz]
  have o1 : σ1.sc (u + 1) = 1 := by rw [F1.2.1 _ (by omega), h1]
  have nd1 : σ1.nat B.rd = d := by rw [F1.1 _ not_false, e_d]
  have no1 : σ1.nat (n0 + 4) = 1 := by rw [F1.1 _ not_false, hone]
  have ar1 : σ1.arr = σ.arr := F1.2.2.1
  refine XV.seq (XV.nconst hL (i := n0 + 11) (by omega) 0 (by positivity))
    fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.nadd hL (i := n0 + 12) (a := B.rd) (b := n0 + 4) (by omega)
    (by omega) (by omega) (by simp only [Env.setNat_nat, show B.rd ≠ n0 + 11 by omega, ↓reduceIte, nd1]; unfold asz at hda; nlinarith)
    (by simp only [Env.setNat_nat, show n0 + 4 ≠ n0 + 11 by omega, ↓reduceIte, no1]; exact hsa)) fun σ3 e3 => ?_
  have n3r : σ3.nat (n0 + 11) = 0 := by rw [e3]; simp
  have n3s : σ3.nat (n0 + 12) = d + 1 := by
    rw [e3]; simp [show B.rd ≠ n0 + 11 by omega, nd1, no1]
  have n3d : σ3.nat B.rd = d := by
    rw [e3]; simp [show B.rd ≠ n0 + 11 by omega, show B.rd ≠ n0 + 12 by omega, nd1]
  have n3o : σ3.nat (n0 + 4) = 1 := by
    rw [e3]; simp [no1]
  have z3 : σ3.sc u = 0 := by rw [e3]; simp [z1]
  have o3 : σ3.sc (u + 1) = 1 := by rw [e3]; simp [o1]
  have c3 : σ3.sc c = ((I.Rb : ℤ) : ℝ) := by rw [e3]; simp [v1]
  have ar3 : σ3.arr = σ.arr := by rw [e3]; simp [ar1]
  have d3 : σ3.draws = σ.draws := by rw [e3]; simp [d1]
  have G3 : FrameA (fun y => c ≤ y) (fun j => n0 + 11 ≤ j ∧ j ≤ n0 + 13) (fun _ _ => False) σ σ3 := by
    rw [e3]
    exact (((FrameA.ofP F1).mono (fun y h => by rcases h with h | h <;> omega) (fun _ h => h.elim)
      (fun _ _ h => h)).setNat ⟨le_rfl, by omega⟩ _).setNat ⟨by omega, by omega⟩ _
  have hdd : d * d + d < 2 ^ ℓa := hda
  -- the trace of `P`
  refine XV.seq (XV.foldE hL (z := u) (r := c + 1) (t := c + 24) (e := .arr B.aP (n0 + 11)) (nr := n0 + 11)
    (nst := n0 + 12) (nk := n0 + 13) (nn := B.rd) (none := n0 + 4) (E := E) (N := d) (base := 0) (st := d + 1)
    (F := fun k => if h : k < d then I.P ⟨k, h⟩ ⟨k, h⟩ else 0) (ℓ := ℓ) (X := X)
    (by simp only [IE.WF]; omega) (by omega) (by omega) (by omega) (by simp only [IE.scr]; omega) z3
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil, and_true,
          not_false_eq_true]
        omega)
    (by omega) (by omega) n3d n3o n3r n3s (by nlinarith) (by nlinarith) (by nlinarith)
    (by simp only [IE.top]; omega)
    (fun k hk => by
      have hb : ∀ j, |(fun k => if h : k < d then I.P ⟨k, h⟩ ⟨k, h⟩ else 0) j| ≤ 2 ^ ellSz I := fun j => by
        dsimp only; split_ifs with h
        · exact ellP_le le_rfl _ _
        · simp
      calc _ ≤ (k : ℤ) * 2 ^ ellSz I := abs_sum_range_le _ _ hb k
        _ ≤ d * 2 ^ ellSz I := by gcongr
        _ ≤ 2 ^ E := hdE
        _ < 2 ^ ℓ := hEℓ)
    (fun k hk σ' G' d' nk' nr' => by
      have ar' : σ'.arr B.aP ((d + 1) * k) = σ.arr B.aP ((d + 1) * k) := by rw [G'.2.2.1 _ _ id, ar3]
      have eP : σ.arr B.aP ((d + 1) * k) = I.P ⟨k, hk⟩ ⟨k, hk⟩ := by
        rw [← e_P ⟨k, hk⟩ ⟨k, hk⟩]; congr 1; simp only; ring
      refine ⟨⟨?_, I.P ⟨k, hk⟩ ⟨k, hk⟩, ?_, ellP_le hσE _ _⟩, ?_⟩
      · rw [nr']; unfold asz; nlinarith
      · rw [nr', zero_add, ar', eP]
      · simp only [IE.eval]; rw [nr', zero_add, ar', eP]; simp [hk]))
    fun σ4 ⟨s4, r4, d4, G4⟩ => ?_
  have z4 : σ4.sc u = 0 := by rw [G4.2.1 _ (by omega), z3]
  have o4 : σ4.sc (u + 1) = 1 := by rw [G4.2.1 _ (by omega), o3]
  have c4 : σ4.sc c = ((I.Rb : ℤ) : ℝ) := by rw [G4.2.1 _ (by omega), c3]
  have n4d : σ4.nat B.rd = d := by rw [G4.1 _ (by omega), n3d]
  have n4o : σ4.nat (n0 + 4) = 1 := by rw [G4.1 _ (by omega), n3o]
  have ar4 : ∀ b k, σ4.arr b k = σ.arr b k := fun b k => by rw [G4.2.2.1 _ _ id, ar3]
  rw [trace_sum] at s4
  -- `|f|₁`
  refine XV.seq (XV.nconst hL (i := n0 + 11) (by omega) 0 (by positivity)) fun σ5 e5 => ?_
  subst e5
  refine XV.mono (XV.foldE hL (z := u) (r := c + 2) (t := c + 24) (e := ieAbs B.af (n0 + 11) (u + 1))
    (nr := n0 + 11) (nst := n0 + 4) (nk := n0 + 13) (nn := B.rd) (none := n0 + 4) (E := E) (N := d) (base := 0)
    (st := 1) (F := fun k => |vext I.f k|) (ℓ := ℓ) (X := X)
    (by simp only [ieAbs, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega) (by omega) (by omega)
    (by omega) (by simp only [ieAbs, IE.scr]; omega) (by simp [z4])
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil, and_true,
          not_false_eq_true]
        omega)
    (by omega) (by omega) (by simp [show B.rd ≠ n0 + 11 by omega, n4d])
    (by simp [n4o]) (by simp) (by simp [n4o])
    (by nlinarith) (by nlinarith) hsa (by simp only [ieAbs, IE.top, IE.mag]; omega)
    (fun k hk => by
      have hb : ∀ j, |(fun k => |vext I.f k|) j| ≤ 2 ^ ellSz I := fun j => by
        dsimp only; rw [abs_abs]; unfold vext; split_ifs with h
        · exact ellF_le le_rfl _
        · simp
      calc _ ≤ (k : ℤ) * 2 ^ ellSz I := abs_sum_range_le _ _ hb k
        _ ≤ d * 2 ^ ellSz I := by gcongr
        _ ≤ 2 ^ E := hdE
        _ < 2 ^ ℓ := hEℓ)
    (fun k hk σ' G' d' nk' nr' => by
      have ef : σ'.arr B.af (σ'.nat (n0 + 11)) = I.f ⟨k, hk⟩ := by
        rw [nr', zero_add, one_mul, G'.2.2.1 _ _ id, Env.setNat_arr, ar4, ← e_f ⟨k, hk⟩]
      have eo : σ'.sc (u + 1) = 1 := by rw [G'.2.1 _ (by omega)]; simp [o4]
      have hA : (IE.arr B.af (n0 + 11)).Leaves E σ' :=
        ⟨by rw [nr']; unfold asz; nlinarith, I.f ⟨k, hk⟩, ef, ellF_le hσE _⟩
      have hO : (IE.sc (u + 1)).Leaves E σ' := ⟨1, by rw [eo, Int.cast_one], one_le_two_pow E⟩
      refine ⟨⟨hA, hO, ⟨hA, ⟨hA, hA⟩, hO⟩, hA, ⟨hA, hA⟩, hO⟩, ?_⟩
      simp only [ieAbs, IE.eval, RealRAM.Op2.eval, ef, eo]
      rw [show ((I.f ⟨k, hk⟩ : ℤ) : ℝ) * (I.f ⟨k, hk⟩ : ℝ) + 1 = ((I.f ⟨k, hk⟩ * I.f ⟨k, hk⟩ + 1 : ℤ) : ℝ) by
        push_cast; ring, Int.floor_intCast, Int.floor_intCast]
      simp only [vext, hk, ↓reduceDIte]
      rw [abs_eq_sign (I.f ⟨k, hk⟩)]
      push_cast; ring))
    le_rfl fun σ6 ⟨s6, r6, d6, G6⟩ => ?_
  rw [sum_vext_abs] at s6
  refine ⟨by rw [G6.2.1 _ (by omega)]; simp [c4], by rw [G6.2.1 _ (by omega)]; simp [s4], s6,
    by rw [d6]; simp [d4, d3], ?_⟩
  have G4' : FrameA (fun y => c ≤ y) (fun j => n0 + 11 ≤ j ∧ j ≤ n0 + 13) (fun _ _ => False) σ3 σ4 :=
    G4.mono (fun y h => by rcases h with h | h <;> omega) (fun j h => by rcases h with h | h <;> omega)
      (fun _ _ h => h)
  have G6' : FrameA (fun y => c ≤ y) (fun j => n0 + 11 ≤ j ∧ j ≤ n0 + 13) (fun _ _ => False)
      (σ4.setNat (n0 + 11) 0) σ6 :=
    G6.mono (fun y h => by rcases h with h | h <;> omega) (fun j h => by rcases h with h | h <;> omega)
      (fun _ _ h => h)
  exact ((G3.trans G4').setNat ⟨le_rfl, by omega⟩ _).trans G6'

end AdversarialBco.Bit.Transfer
