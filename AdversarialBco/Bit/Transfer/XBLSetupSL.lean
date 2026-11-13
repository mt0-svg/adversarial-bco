/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSetupPar
public import AdversarialBco.Bit.Transfer.XEllConst

@[expose] public section

/-!
# BL's setup on the machine: straight-line integer programs

Procedure PARAM is a straight line of about eighty integer steps. This file runs such a line generically.

* `xmercG`, `XV.mercG`: Mercator's fixed-point sum `gsm_mercq q X q` on generic slots (Procedure BM-INT's loop, with
  `q` in a register and `2^q` in a slot), within `8 q + 6` units.
* `SStep`: the kinds of steps (a constant, an integer expression, an integer square root, a power of two, a binary
  logarithm, Mercator's sum, the positive part), each writing one slot of a region; `SL.code` the program of a list of
  steps, `XV.sl` its rule: the slot `b + k` ends holding the value `v k` of step `k`, every value below `2^E`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP

variable {d : ℕ}

/-! ## Mercator's sum on generic slots -/

/-- `S := Σ_{i < q} P_i div (i + 1)` with `P_0 = X`, `P_{i+1} = (P_i X) div 2^q` (`gsm_mercq q X q`): `X` at `Xin`,
`2^q` at `Qs`, `0` at `z`, `1` at `one`; `P_i` at `P`, `i + 1` at `I`, a temporary at `T`; the counter `i`, `q` in the
register `nq`, `1` in the register `none`. -/
def xmercG (L : Layout) (S Xin P I T z one Qs i nq none : ℕ) : XCmd :=
  .seq (toX (VL.sop2 L .add S z z))
  (.seq (toX (VL.sop2 L .add P Xin z))
  (.seq (toX (VL.sop2 L .add I one z))
  (xforN i nq none
    (.seq (xsidiv L T P I)
    (.seq (toX (VL.sop2 L .add S S T))
    (.seq (toX (VL.sop2 L .mul T P Xin))
    (.seq (xsidiv L P T Qs)
    (toX (VL.sop2 L .add I I one)))))))))

theorem XV.mercG {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {S Xin P I T z one Qs i nq none : ℕ} (hTl : T < L.NS) (hil : i < L.NN) (hnl : nq < L.NN) (hol : none < L.NN)
    (hXS : Xin < S) (hzS : z < S) (h1S : one < S) (hQS : Qs < S) (hSP : S < P) (hPI : P < I) (hIT : I < T)
    (hin : i ≠ nq) (hio : i ≠ none)
    {q Xv : ℕ} (hz : σ.sc z = ((0 : ℤ) : ℝ)) (h1 : σ.sc one = ((1 : ℤ) : ℝ)) (hQ : σ.sc Qs = ((2 ^ q : ℤ) : ℝ))
    (hXv : σ.sc Xin = ((Xv : ℤ) : ℝ)) (hXq : Xv ≤ 2 ^ q) (hnq : σ.nat nq = q) (hn1 : σ.nat none = 1)
    (hℓa : q < 2 ^ ℓa) (hℓ : 2 * q < ℓ) :
    XRunsB L X ℓa ℓ (xmercG L S Xin P I T z one Qs i nq none) σ (8 * q + 6) (fun σ' =>
      σ'.sc S = ((gsm_mercq q Xv q : ℕ) : ℤ) ∧ σ'.draws = σ.draws ∧
      FrameP (fun y => y = S ∨ y = P ∨ y = I ∨ y = T) (fun j => j = i) σ σ') := by
  have hSl : S < L.NS := by omega
  have hXl : Xin < L.NS := by omega
  have bq : ∀ z : ℤ, 0 ≤ z → z ≤ 2 ^ (2 * q) → |z| < 2 ^ ℓ := fun z h0 h1 => absI_lt h0 h1 hℓ
  have hXz : (Xv : ℤ) ≤ 2 ^ q := by exact_mod_cast hXq
  have hqq : (2 : ℤ) ^ q ≤ 2 ^ (2 * q) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hq2 : (2 : ℤ) ^ (2 * q) = 2 ^ q * 2 ^ q := by rw [two_mul, pow_add]
  have hqlt : (q : ℤ) + 1 ≤ 2 ^ q := by
    have : q + 1 ≤ 2 ^ q := Nat.lt_two_pow_self
    exact_mod_cast this
  have hmq : ∀ t ≤ q, ((gsm_mercq q Xv t : ℕ) : ℤ) ≤ 2 ^ (2 * q) := fun t ht => by
    have h1 : gsm_mercq q Xv t ≤ t * Xv := bm_mercq_le q Xv t hXq
    have h3 : t * Xv ≤ 2 ^ q * 2 ^ q := Nat.mul_le_mul (le_trans ht Nat.lt_two_pow_self.le) hXq
    have h4 : gsm_mercq q Xv t ≤ 2 ^ (2 * q) := by rw [two_mul, pow_add]; exact le_trans h1 h3
    exact_mod_cast h4
  have hpw : ∀ t, ((gsm_powq q Xv t : ℕ) : ℤ) ≤ 2 ^ q := fun t => by
    have : gsm_powq q Xv t ≤ Xv := bm_powq_le q Xv hXq t
    have : ((gsm_powq q Xv t : ℕ) : ℤ) ≤ Xv := by exact_mod_cast this
    omega
  have hm : ∀ t, ((gsm_mercq q Xv (t + 1) : ℕ) : ℤ) =
      ((gsm_mercq q Xv t : ℕ) : ℤ) + ((gsm_powq q Xv t : ℕ) : ℤ) / ((t + 1 : ℕ) : ℤ) := fun t => by
    unfold gsm_mercq; rw [Finset.sum_range_succ]; push_cast; ring
  have hp : ∀ t, ((gsm_powq q Xv (t + 1) : ℕ) : ℤ) = ((gsm_powq q Xv t : ℕ) : ℤ) * (Xv : ℤ) / 2 ^ q := fun t => by
    rw [gsm_powq]; push_cast; ring
  have z0 : ∀ σ', FrameP (fun y => y = S ∨ y = P ∨ y = I ∨ y = T) (fun j => j = i) σ σ' →
      σ'.sc z = ((0 : ℤ) : ℝ) ∧ σ'.sc one = ((1 : ℤ) : ℝ) ∧ σ'.sc Qs = ((2 ^ q : ℤ) : ℝ) ∧
      σ'.sc Xin = ((Xv : ℤ) : ℝ) := fun σ' hF =>
    ⟨by rw [hF.2.1 z (by omega), hz], by rw [hF.2.1 one (by omega), h1],
     by rw [hF.2.1 Qs (by omega), hQ], by rw [hF.2.1 Xin (by omega), hXv]⟩
  refine XV.mono (K := 1 + (1 + (1 + (q * (5 + 3) + 3)))) ?_ (by omega) (fun _ h => h)
  refine XV.seq (XV.addI hL (x := S) (a := z) (b := z) (u := 0) (v := 0) hSl (by omega) (by omega) hz hz
    (bq _ le_rfl (by nn)) (bq _ le_rfl (by nn)) (bq _ le_rfl (by nn))) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.addI hL (x := P) (a := Xin) (b := z) (u := Xv) (v := 0) (by omega) hXl (by omega)
    (by slot) (by slot) (bq _ (by nn) (by omega)) (bq _ le_rfl (by nn))
    (bq _ (by nn) (by omega))) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.addI hL (x := I) (a := one) (b := z) (u := 1) (v := 0) (by omega) (by omega)
    (by omega) (by slot) (by slot) (bq _ (by norm_num) (by omega))
    (bq _ le_rfl (by nn)) (bq _ (by norm_num) (by omega))) fun σ3 e3 => ?_
  subst e3
  refine XV.mono (XV.forN hL (i := i) (n := nq) (one := none) hil hnl hol hin hio q 5 hℓa
    (fun t σ' => σ'.sc S = ((gsm_mercq q Xv t : ℕ) : ℤ) ∧ σ'.sc P = ((gsm_powq q Xv t : ℕ) : ℤ) ∧
      σ'.sc I = ((t + 1 : ℕ) : ℤ) ∧ σ'.draws = σ.draws ∧
      FrameP (fun y => y = S ∨ y = P ∨ y = I ∨ y = T) (fun j => j = i) σ σ') _
    (by slot) (by slot) ?_ ?_) le_rfl (fun σ' ⟨⟨h1, _, _, hd, hF⟩, _⟩ => ⟨h1, hd, hF⟩)
  · refine ⟨by slot <;> simp [gsm_mercq], by slot <;> simp [gsm_powq], by slot <;> simp, rfl, ?_⟩
    exact ((((FrameP.refl (fun y => y = S ∨ y = P ∨ y = I ∨ y = T) (fun j => j = i) σ).setSc
      (Or.inl rfl) _).setSc (Or.inr (Or.inl rfl)) _).setSc (Or.inr (Or.inr (Or.inl rfl))) _).setNat rfl _
  intro t ht σ' ⟨iS, iP, iI, iD, iF⟩ hi hn h1'
  obtain ⟨c0, c1, c5, cX⟩ := z0 σ' iF
  have hPt := hpw t
  have hP0 : (0 : ℤ) ≤ ((gsm_powq q Xv t : ℕ) : ℤ) := Nat.cast_nonneg _
  have hdiv : ((gsm_powq q Xv t : ℕ) : ℤ) / ((t + 1 : ℕ) : ℤ) ≤ 2 ^ q :=
    le_trans (Int.ediv_le_self _ hP0) hPt
  refine XV.seq (K₂ := 4) (XV.divI hL (x := T) (a := P) (b := I) hTl (by omega) (by omega) iP iI
    (bq _ hP0 (by omega)) (bq _ (by nn) (by push_cast; omega))) fun σa ea => ?_
  subst ea
  refine XV.seq (K₂ := 3) (XV.addI hL (x := S) (a := S) (b := T) (u := ((gsm_mercq q Xv t : ℕ) : ℤ))
    (v := ((gsm_powq q Xv t : ℕ) : ℤ) / ((t + 1 : ℕ) : ℤ)) hSl hSl hTl (by slot) (by slot)
    (bq _ (by nn) (hmq t ht.le)) (bq _ (Int.ediv_nonneg hP0 (by nn)) (by omega))
    (bq _ (by nn) (by rw [← hm]; exact hmq (t + 1) ht))) fun σb eb => ?_
  subst eb
  refine XV.seq (K₂ := 2) (XV.mulI hL (x := T) (a := P) (b := Xin) (u := ((gsm_powq q Xv t : ℕ) : ℤ))
    (v := Xv) hTl (by omega) hXl (by slot) (by slot) (bq _ hP0 (by omega)) (bq _ (by nn)
    (by omega)) (bq _ (by nn) (by rw [hq2]; exact mul_le_mul hPt hXz (by nn) (by nn))))
    fun σc ec => ?_
  subst ec
  refine XV.seq (K₂ := 1) (XV.divI hL (x := P) (a := T) (b := Qs)
    (u := ((gsm_powq q Xv t : ℕ) : ℤ) * Xv) (v := 2 ^ q) (by omega) hTl (by omega) (by slot) (by slot)
    (bq _ (by nn) (by rw [hq2]; exact mul_le_mul hPt hXz (by nn) (by nn)))
    (bq _ (by nn) hqq)) fun σd ed => ?_
  subst ed
  refine XV.mono (XV.addI hL (x := I) (a := I) (b := one) (u := ((t + 1 : ℕ) : ℤ)) (v := 1)
    (by omega) (by omega) (by omega) (by slot) (by slot) (bq _ (by nn) (by push_cast; omega))
    (bq _ (by norm_num) (by omega)) (bq _ (by nn) (by push_cast; omega))) le_rfl fun σe ee => ?_
  subst ee
  refine ⟨by slot, by slot, by slot, ⟨by slot <;> rw [hm], by slot <;> rw [hp], by slot <;> (push_cast; ring),
    by simpa using iD, ?_⟩⟩
  exact (((((iF.setSc (Or.inr (Or.inr (Or.inr rfl))) _).setSc (Or.inl rfl) _).setSc
    (Or.inr (Or.inr (Or.inr rfl))) _).setSc (Or.inr (Or.inl rfl)) _).setSc (Or.inr (Or.inr (Or.inl rfl))) _).setNat
    rfl _

/-! ## Integer expressions on integer leaves, with a bound per leaf

A bound `2^(a G + b)` is the pair `(a, b)` at a parameter `G` (`ev G`); the bound of a value and the largest bound over
the nodes come from the pairs of the leaves (`ieMag`, `ieTop`), on concrete expressions by computation. -/

/-- The integer value of an expression whose slot `y` holds `g y`. -/
def slZ (g : ℕ → ℤ) : IE → ℤ
  | .sc y => g y
  | .arr _ _ => 0
  | .op .add a b => slZ g a + slZ g b
  | .op .sub a b => slZ g a - slZ g b
  | .op .mul a b => slZ g a * slZ g b
  | .op .div _ _ => 0
  | .ediv a b => slZ g a / slZ g b

/-- Every leaf is a slot satisfying `P`; no array cell, no real division. -/
def ieLv (P : ℕ → Prop) : IE → Prop
  | .sc y => P y
  | .arr _ _ => False
  | .op .div _ _ => False
  | .op .add a b => ieLv P a ∧ ieLv P b
  | .op .sub a b => ieLv P a ∧ ieLv P b
  | .op .mul a b => ieLv P a ∧ ieLv P b
  | .ediv a b => ieLv P a ∧ ieLv P b

/-- The same as a test. -/
def ieLvB (P : ℕ → Bool) : IE → Bool
  | .sc y => P y
  | .arr _ _ => false
  | .op .div _ _ => false
  | .op .add a b => ieLvB P a && ieLvB P b
  | .op .sub a b => ieLvB P a && ieLvB P b
  | .op .mul a b => ieLvB P a && ieLvB P b
  | .ediv a b => ieLvB P a && ieLvB P b

/-- `a G + b`. -/
def ev (G : ℕ) (p : ℕ × ℕ) : ℕ := p.1 * G + p.2

/-- The larger pair, entrywise. -/
def pmax (p q : ℕ × ℕ) : ℕ × ℕ := (max p.1 q.1, max p.2 q.2)

/-- `p ≤ q` entrywise. -/
def ple (p q : ℕ × ℕ) : Bool := decide (p.1 ≤ q.1) && decide (p.2 ≤ q.2)

/-- The pair of the bound of the value from the pairs `f y` of the leaves. -/
def ieMag (f : ℕ → ℕ × ℕ) : IE → ℕ × ℕ
  | .sc y => f y
  | .arr _ _ => (0, 0)
  | .op .mul a b => ((ieMag f a).1 + (ieMag f b).1, (ieMag f a).2 + (ieMag f b).2)
  | .op _ a b => ((pmax (ieMag f a) (ieMag f b)).1, (pmax (ieMag f a) (ieMag f b)).2 + 1)
  | .ediv a _ => ieMag f a

/-- The largest pair over the nodes. -/
def ieTop (f : ℕ → ℕ × ℕ) : IE → ℕ × ℕ
  | .sc y => f y
  | .arr _ _ => (0, 0)
  | .op o a b => pmax (ieMag f (.op o a b)) (pmax (ieTop f a) (ieTop f b))
  | .ediv a b => pmax (ieMag f a) (pmax (ieTop f a) (ieTop f b))

theorem ev_mono {G : ℕ} {p q : ℕ × ℕ} (h : ple p q = true) : ev G p ≤ ev G q := by
  simp only [ple, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold ev; have := Nat.mul_le_mul_right G h.1; omega

theorem ev_pmax_l (G : ℕ) (p q : ℕ × ℕ) : ev G p ≤ ev G (pmax p q) := by
  unfold ev pmax; have := Nat.mul_le_mul_right G (le_max_left p.1 q.1); have := le_max_left p.2 q.2; dsimp only
  omega

theorem ev_pmax_r (G : ℕ) (p q : ℕ × ℕ) : ev G q ≤ ev G (pmax p q) := by
  unfold ev pmax; have := Nat.mul_le_mul_right G (le_max_right p.1 q.1); have := le_max_right p.2 q.2; dsimp only
  omega

theorem ieLv_mono {P Q : ℕ → Prop} (h : ∀ y, P y → Q y) : ∀ {e : IE}, ieLv P e → ieLv Q e
  | .sc _, hl => h _ hl
  | .op .add _ _, hl => ⟨ieLv_mono h hl.1, ieLv_mono h hl.2⟩
  | .op .sub _ _, hl => ⟨ieLv_mono h hl.1, ieLv_mono h hl.2⟩
  | .op .mul _ _, hl => ⟨ieLv_mono h hl.1, ieLv_mono h hl.2⟩
  | .ediv _ _, hl => ⟨ieLv_mono h hl.1, ieLv_mono h hl.2⟩

theorem ieLv_of_B {P : ℕ → Bool} : ∀ {e : IE}, ieLvB P e = true → ieLv (fun y => P y = true) e
  | .sc _, h => h
  | .arr _ _, h => by simp [ieLvB] at h
  | .op .div _ _, h => by simp [ieLvB] at h
  | .op .add _ _, h => by simp only [ieLvB, Bool.and_eq_true] at h; exact ⟨ieLv_of_B h.1, ieLv_of_B h.2⟩
  | .op .sub _ _, h => by simp only [ieLvB, Bool.and_eq_true] at h; exact ⟨ieLv_of_B h.1, ieLv_of_B h.2⟩
  | .op .mul _ _, h => by simp only [ieLvB, Bool.and_eq_true] at h; exact ⟨ieLv_of_B h.1, ieLv_of_B h.2⟩
  | .ediv _ _, h => by simp only [ieLvB, Bool.and_eq_true] at h; exact ⟨ieLv_of_B h.1, ieLv_of_B h.2⟩

theorem ieLv_WF {L : Layout} {t : ℕ} : ∀ {e : IE}, ieLv (· < t) e → e.WF L t
  | .sc _, h => h
  | .op .add _ _, h => ⟨by simp, ieLv_WF h.1, ieLv_WF h.2⟩
  | .op .sub _ _, h => ⟨by simp, ieLv_WF h.1, ieLv_WF h.2⟩
  | .op .mul _ _, h => ⟨by simp, ieLv_WF h.1, ieLv_WF h.2⟩
  | .ediv _ _, h => ⟨ieLv_WF h.1, ieLv_WF h.2⟩

theorem ieZ_eval {σ : Env d} {g : ℕ → ℤ} : ∀ {e : IE}, ieLv (fun y => σ.sc y = g y) e → e.eval σ = slZ g e
  | .sc _, h => h
  | .op .add _ _, h => by
    simp only [IE.eval, slZ, ieZ_eval h.1, ieZ_eval h.2, RealRAM.Op2.eval]; push_cast; ring
  | .op .sub _ _, h => by
    simp only [IE.eval, slZ, ieZ_eval h.1, ieZ_eval h.2, RealRAM.Op2.eval]; push_cast; ring
  | .op .mul _ _, h => by
    simp only [IE.eval, slZ, ieZ_eval h.1, ieZ_eval h.2, RealRAM.Op2.eval]; push_cast; ring
  | .ediv _ _, h => by simp only [IE.eval, slZ, ieZ_eval h.1, ieZ_eval h.2, Int.floor_intCast]

theorem ieZ_bound {G : ℕ} {g : ℕ → ℤ} {f : ℕ → ℕ × ℕ} :
    ∀ {e : IE}, ieLv (fun y => |g y| ≤ 2 ^ ev G (f y)) e → |slZ g e| ≤ 2 ^ ev G (ieMag f e)
  | .sc _, h => h
  | .op .add a b, h => by
    have ha := absI_mono (ieZ_bound h.1) (ev_pmax_l G (ieMag f a) (ieMag f b))
    have hb := absI_mono (ieZ_bound h.2) (ev_pmax_r G (ieMag f a) (ieMag f b))
    simpa [slZ, ieMag, ev, Nat.add_assoc] using absI_add_le ha hb
  | .op .sub a b, h => by
    have ha := absI_mono (ieZ_bound h.1) (ev_pmax_l G (ieMag f a) (ieMag f b))
    have hb := absI_mono (ieZ_bound h.2) (ev_pmax_r G (ieMag f a) (ieMag f b))
    simpa [slZ, ieMag, ev, Nat.add_assoc] using absI_sub_le ha hb
  | .op .mul a b, h => by
    have := absI_mul_le (ieZ_bound h.1) (ieZ_bound h.2)
    simp only [slZ, ieMag, ev]
    refine this.trans (le_of_eq ?_)
    congr 1; unfold ev; ring
  | .ediv a b, h => (absI_ediv_le _ _).trans (ieZ_bound h.1)

theorem ieOK {σ : Env d} {G ℓ : ℕ} {g : ℕ → ℤ} {f : ℕ → ℕ × ℕ} :
    ∀ {e : IE}, ieLv (fun y => σ.sc y = g y ∧ |g y| ≤ 2 ^ ev G (f y)) e → ev G (ieTop f e) < ℓ → e.OK ℓ σ
  | .sc y, h, ht => by
    simp only [IE.OK, h.1]
    exact XV.abs_int_lt (lt_of_le_of_lt h.2 (pow_lt_pow_right₀ (by norm_num) ht))
  | .op o a b, h, ht => by
    have hab : ieLv (fun y => σ.sc y = g y ∧ |g y| ≤ 2 ^ ev G (f y)) a ∧
        ieLv (fun y => σ.sc y = g y ∧ |g y| ≤ 2 ^ ev G (f y)) b := by
      cases o
      · exact h
      · exact h
      · exact h
      · exact absurd h id
    have h1 := (ev_pmax_l G _ _).trans_lt ht
    have h2 := (ev_pmax_r G _ _).trans_lt ht
    have hta := (ev_pmax_l G _ _).trans_lt h2
    have htb := (ev_pmax_r G _ _).trans_lt h2
    refine ⟨ieOK hab.1 hta, ieOK hab.2 htb, ?_⟩
    rw [show o.eval (a.eval σ) (b.eval σ) = (IE.op o a b).eval σ from rfl,
      ieZ_eval (ieLv_mono (fun y hy => hy.1) h)]
    exact XV.abs_int_lt (lt_of_le_of_lt (ieZ_bound (ieLv_mono (fun y hy => hy.2) h))
      (pow_lt_pow_right₀ (by norm_num) h1))
  | .ediv a b, h, ht => by
    have h1 := (ev_pmax_l G _ _).trans_lt ht
    have h2 := (ev_pmax_r G _ _).trans_lt ht
    refine ⟨ieOK h.1 ((ev_pmax_l G _ _).trans_lt h2), ieOK h.2 ((ev_pmax_r G _ _).trans_lt h2), ?_⟩
    rw [show ((⌊a.eval σ⌋ / ⌊b.eval σ⌋ : ℤ) : ℝ) = (IE.ediv a b).eval σ from rfl,
      ieZ_eval (ieLv_mono (fun y hy => hy.1) h)]
    exact XV.abs_int_lt (lt_of_le_of_lt (ieZ_bound (ieLv_mono (fun y hy => hy.2) (e := .ediv a b) h))
      (pow_lt_pow_right₀ (by norm_num) h1))

/-- **The package with a bound per leaf**: leaves below `t` holding `g y`, `|g y| ≤ 2^(ev G (f y))`, the largest
pair below `ℓ` at `G`. -/
theorem XV.ieRunP {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {z x t G : ℕ} {e : IE} {σ : Env d}
    {g : ℕ → ℤ} {f : ℕ → ℕ × ℕ} (hz : z < t) (hx : x < t) (hS : t + e.scr ≤ L.NS) (hz0 : σ.sc z = 0)
    (hl : ieLv (fun y => y < t ∧ σ.sc y = g y ∧ |g y| ≤ 2 ^ ev G (f y)) e) (htop : ev G (ieTop f e) < ℓ) :
    XRunsB L X ℓa ℓ (e.code L z x t) σ e.units (XV.ExprPost ℓ σ x t (slZ g e)) := by
  have hw : e.WF L t := ieLv_WF (ieLv_mono (fun y hy => hy.1) hl)
  have hok : e.OK ℓ σ := ieOK (ieLv_mono (fun y hy => hy.2) hl) htop
  have hv : e.eval σ = slZ g e := ieZ_eval (ieLv_mono (fun y hy => hy.2.1) hl)
  have hb := hok.bound
  rw [hv] at hb
  exact XV.mono (XV.ie hL (by omega) e x t σ hw hz hx hS hz0 hok) le_rfl fun σ' h =>
    ⟨by rw [h.1, hv], by exact_mod_cast hb, h.2.1, h.2.2.mono (fun y hy => by omega) (fun _ h => h)⟩

/-! ## Straight lines -/

/-- A step of a straight line; step `k` writes the slot `b + k` of the region, `j` names the value of step `j < k`:
a constant, an integer expression (its leaves in the region or among the input slots below `b`), `⌊√v_j⌋`, `2^{v_j}`,
`⌈lg v_j⌉`, Mercator's sum `gsm_mercq q X q` (`q = v_jq`, `2^q = v_jQ`, `X = v_jX`), `max(v_j, 0)`. -/
inductive SStep
  | cst (c : ℤ)
  | ie (e : IE)
  | sq (j : ℕ)
  | pw (j : ℕ)
  | cl (j : ℕ)
  | mc (jq jQ jX : ℕ)
  | mx (j : ℕ)

/-- The cells of a straight line: the region from `b`, the scratch slots from `t`, the slots `z`, `one`, `two`,
`four` holding `0, 1, 2, 4`, the scratch registers `r1`, `r2`, the register `n1` holding `1`. -/
structure SLC where
  b : ℕ
  t : ℕ
  z : ℕ
  one : ℕ
  two : ℕ
  four : ℕ
  r1 : ℕ
  r2 : ℕ
  n1 : ℕ

/-- The code of step `k`. -/
def SStep.code (L : Layout) (C : SLC) (k : ℕ) : SStep → XCmd
  | .cst c => toX (VL.sconst L (C.b + k) c)
  | .ie e => e.code L C.z (C.b + k) C.t
  | .sq j => .seq (toX (VL.sop2 L .add C.t (C.b + j) C.z))
      (xisqrt L C.t (C.b + k) (C.t + 1) (C.t + 2) (C.t + 3) C.z C.one C.two C.four)
  | .pw j => .seq (xrtoN L C.r1 (C.b + j)) (xpow2 L (C.b + k) C.r2 C.r1 C.n1)
  | .cl j => .seq (xclogS L C.t (C.b + j) C.r1 C.n1) (toX (VL.ncast L (C.b + k) C.r1))
  | .mc jq jQ jX => .seq (xrtoN L C.r1 (C.b + jq))
      (xmercG L (C.b + k) (C.b + jX) C.t (C.t + 1) (C.t + 2) C.z C.one (C.b + jQ) C.r2 C.r1 C.n1)
  | .mx j => .seq (toX (VL.sop2 L .add (C.b + k) (C.b + j) C.z))
      (xifS L (C.b + k) C.z (toX (VL.sop2 L .add (C.b + k) C.z C.z)) .skip)

/-- The value of a step from the values `v` of the steps before it and the inputs `ι` of the slots below `b`. -/
def SStep.sem (b : ℕ) (ι v : ℕ → ℤ) : SStep → ℤ
  | .cst c => c
  | .ie e => slZ (fun y => if y < b then ι y else v (y - b)) e
  | .sq j => Nat.sqrt (v j).toNat
  | .pw j => 2 ^ (v j).toNat
  | .cl j => Nat.clog 2 (v j).toNat
  | .mc jq _ jX => gsm_mercq (v jq).toNat (v jX).toNat (v jq).toNat
  | .mx j => max (v j) 0

/-- The value of step `k` of the straight line `st`. -/
def SL.val (st : List SStep) (b : ℕ) (ι : ℕ → ℤ) (k : ℕ) : ℤ :=
  (st.getD k (.cst 0)).sem b ι (fun j => if h : j < k then SL.val st b ι j else 0)
termination_by k

theorem SL.val_eq (st : List SStep) (b : ℕ) (ι : ℕ → ℤ) (k : ℕ) :
    SL.val st b ι k = (st.getD k (.cst 0)).sem b ι (fun j => if j < k then SL.val st b ι j else 0) := by
  rw [SL.val]; congr 1

/-- The static test of step `k`: what it reads lies before it (or among the inputs `ins`, below `b`); the pair of its
value is at most `et k` (the pairs of the inputs are `eIn`); its largest pair is at most `T`; its scratch fits in `S`
slots. -/
def SStep.chk (b k : ℕ) (ins : List ℕ) (eIn et : ℕ → ℕ × ℕ) (T : ℕ × ℕ) (S : ℕ) : SStep → Bool
  | .cst c => decide (c.natAbs ≤ 2 ^ (et k).2) && ple (et k) T
  | .ie e => ieLvB (fun y => (decide (y < b) && ins.contains y) || (decide (b ≤ y) && decide (y < b + k))) e &&
      ple (ieMag (fun y => if y < b then eIn y else et (y - b)) e) (et k) &&
      ple (ieTop (fun y => if y < b then eIn y else et (y - b)) e) T && decide (e.scr ≤ S)
  | .sq j => decide (j < k) && ple (et j) (et k) && ple ((et j).1, (et j).2 + 3) T && decide (4 ≤ S)
  | .pw j => decide (j < k) && ple (1, 0) (et k) && ple (1, 1) T
  | .cl j => decide (j < k) && ple (et j) (et k) && ple (et j) T && decide (1 ≤ S)
  | .mc jq jQ jX => decide (jq < k) && decide (jQ < k) && decide (jX < k) && ple (2, 0) (et k) && ple (2, 1) T &&
      decide (3 ≤ S)
  | .mx j => decide (j < k) && ple (et j) (et k) && ple (et j) T

/-- The facts a step needs of the values before it: nonnegative arguments, exponents at most `G`, `2^q` and
`X ≤ 2^q` for Mercator's sum. -/
def SStep.Sem (v : ℕ → ℤ) (G : ℕ) : SStep → Prop
  | .sq j => 0 ≤ v j
  | .pw j => 0 ≤ v j ∧ v j ≤ G
  | .cl j => 0 ≤ v j
  | .mc jq jQ jX => 0 ≤ v jq ∧ v jq ≤ G ∧ v jQ = 2 ^ (v jq).toNat ∧ 0 ≤ v jX ∧ v jX ≤ v jQ
  | _ => True

/-- The pair of the units of a step. -/
def SStep.unitsP (et : ℕ → ℕ × ℕ) : SStep → ℕ × ℕ
  | .cst _ => (0, 1)
  | .ie e => (0, e.units)
  | .sq j => (12 * (et j).1, 12 * (et j).2 + 21)
  | .pw _ => (4, 5)
  | .cl j => (4 * (et j).1, 4 * (et j).2 + 5)
  | .mc _ _ _ => (8, 7)
  | .mx _ => (0, 3)

/-- The pair of a value is a bound: `|v_k| ≤ 2^(ev G (et k))` for every step. -/
theorem SL.val_bound (st : List SStep) (b : ℕ) (ι : ℕ → ℤ) (ins : List ℕ) (eIn et : ℕ → ℕ × ℕ) (T : ℕ × ℕ)
    (S G : ℕ) (hchk : ∀ k < st.length, (st.getD k (.cst 0)).chk b k ins eIn et T S = true)
    (hsem : ∀ k < st.length, (st.getD k (.cst 0)).Sem (SL.val st b ι) G)
    (hin : ∀ y ∈ ins, |ι y| ≤ 2 ^ ev G (eIn y)) :
    ∀ k < st.length, |SL.val st b ι k| ≤ 2 ^ ev G (et k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk
  have hc := hchk k hk
  have hs := hsem k hk
  have hp : ∀ {x : ℤ} {a c : ℕ}, |x| ≤ 2 ^ a → a ≤ c → |x| ≤ 2 ^ c := fun h h' => absI_mono h h'
  rw [SL.val_eq]
  generalize st.getD k (.cst 0) = s at hc hs
  cases s with
  | cst c =>
    simp only [SStep.chk, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hc, -⟩ := hc
    simp only [SStep.sem]
    refine hp (a := (et k).2) ?_ (by unfold ev; omega)
    rw [← Int.natCast_natAbs]; exact_mod_cast hc
  | ie e =>
    simp only [SStep.chk, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨hl, hm⟩, -⟩, -⟩ := hc
    simp only [SStep.sem]
    refine hp (ieZ_bound (f := fun y => if y < b then eIn y else et (y - b)) (ieLv_mono ?_ (ieLv_of_B hl)))
      (ev_mono hm)
    intro y hy
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hy
    rcases hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
    · simp only [hy1, ↓reduceIte]; exact hin y hy2
    · have h1 : ¬ y < b := by omega
      have h2 : y - b < k := by omega
      simp only [h1, h2, ↓reduceIte]
      exact ih _ h2 (by omega)
  | sq j =>
    simp only [SStep.chk, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hj, hm⟩, -⟩, -⟩ := hc
    simp only [SStep.Sem] at hs
    simp only [SStep.sem, hj, ↓reduceIte]
    have hb := ih j hj (by omega)
    refine hp (le_trans ?_ hb) (ev_mono hm)
    rw [abs_of_nonneg (by positivity), abs_of_nonneg hs]
    have : Nat.sqrt (SL.val st b ι j).toNat ≤ (SL.val st b ι j).toNat := Nat.sqrt_le_self _
    have h2 : (((SL.val st b ι j).toNat : ℕ) : ℤ) = SL.val st b ι j := Int.toNat_of_nonneg hs
    calc ((Nat.sqrt (SL.val st b ι j).toNat : ℕ) : ℤ) ≤ (((SL.val st b ι j).toNat : ℕ) : ℤ) := by exact_mod_cast this
      _ = _ := h2
  | pw j =>
    simp only [SStep.chk, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hj, hm⟩, -⟩ := hc
    simp only [SStep.Sem] at hs
    simp only [SStep.sem, hj, ↓reduceIte]
    refine hp (a := G) ?_ (le_trans (by unfold ev; omega) (ev_mono hm))
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  | cl j =>
    simp only [SStep.chk, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hj, hm⟩, -⟩, -⟩ := hc
    simp only [SStep.Sem] at hs
    simp only [SStep.sem, hj, ↓reduceIte]
    have hb := ih j hj (by omega)
    rw [abs_of_nonneg hs] at hb
    have hn : (SL.val st b ι j).toNat ≤ 2 ^ ev G (et j) := by
      have : ((SL.val st b ι j).toNat : ℤ) ≤ 2 ^ ev G (et j) := by rw [Int.toNat_of_nonneg hs]; exact hb
      exact_mod_cast this
    have h1 : Nat.clog 2 (SL.val st b ι j).toNat ≤ ev G (et j) := Nat.clog_le_of_le_pow hn
    refine hp (a := ev G (et j)) ?_ (ev_mono hm)
    rw [abs_of_nonneg (by positivity)]
    have : ev G (et j) < 2 ^ ev G (et j) := Nat.lt_two_pow_self
    exact_mod_cast (h1.trans this.le)
  | mc jq jQ jX =>
    simp only [SStep.chk, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨hjq, hjQ⟩, hjX⟩, hm⟩, -⟩, -⟩ := hc
    simp only [SStep.Sem] at hs
    obtain ⟨h0, hG, hQ, hX0, hXQ⟩ := hs
    simp only [SStep.sem, hjq, hjX, ↓reduceIte]
    set q := (SL.val st b ι jq).toNat
    have hqG : q ≤ G := by omega
    have hXq : (SL.val st b ι jX).toNat ≤ 2 ^ q := by
      have : ((SL.val st b ι jX).toNat : ℤ) ≤ 2 ^ q := by rw [Int.toNat_of_nonneg hX0, ← hQ]; exact hXQ
      exact_mod_cast this
    have h1 := bm_mercq_le q _ q hXq
    have h2 : q * (SL.val st b ι jX).toNat ≤ 2 ^ q * 2 ^ q := Nat.mul_le_mul Nat.lt_two_pow_self.le hXq
    refine hp (a := 2 * G) ?_ (le_trans (by unfold ev; omega) (ev_mono hm))
    rw [abs_of_nonneg (by positivity)]
    have h3 : 2 ^ q * 2 ^ q ≤ 2 ^ (2 * G) := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast (h1.trans (h2.trans h3))
  | mx j =>
    simp only [SStep.chk, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hj, hm⟩, -⟩ := hc
    simp only [SStep.sem, hj, ↓reduceIte]
    have hb := ih j hj (by omega)
    refine hp (le_trans ?_ hb) (ev_mono hm)
    rcases le_total (SL.val st b ι j) 0 with h | h
    · rw [max_eq_right h]; simp
    · rw [max_eq_left h]

/-! ## The run of a step -/

/-- The layout of a straight line with `S` scratch slots: the scratch in the layout, the registers distinct, the
constant slots distinct and below the region, the region below the scratch. -/
structure SLC.OK (L : Layout) (C : SLC) (S : ℕ) : Prop where
  hS : C.t + S ≤ L.NS
  hr1 : C.r1 < L.NN
  hr2 : C.r2 < L.NN
  hn1 : C.n1 < L.NN
  r12 : C.r1 ≠ C.r2
  r1n : C.r1 ≠ C.n1
  r2n : C.r2 ≠ C.n1
  zb : C.z < C.b
  ob : C.one < C.b
  tb : C.two < C.b
  fb : C.four < C.b
  nd : [C.z, C.one, C.two, C.four].Nodup
  bt : C.b ≤ C.t

theorem ev_lin (G c e : ℕ) (p : ℕ × ℕ) : ev G (c * p.1, c * p.2 + e) = c * ev G p + e := by
  unfold ev; ring

theorem absZ_lt {x : ℤ} {a ℓ : ℕ} (h : |x| ≤ 2 ^ a) (ha : a < ℓ) : |(x : ℝ)| < 2 ^ ℓ :=
  XV.abs_int_lt (lt_of_le_of_lt h (pow_lt_pow_right₀ (by norm_num) ha))

theorem natZ_lt {x : ℤ} {G ℓ : ℕ} (h0 : 0 ≤ x) (h : x ≤ G) (hG : G < ℓ) : |(x : ℝ)| < 2 ^ ℓ := by
  refine XV.abs_int_lt ?_
  rw [abs_of_nonneg h0]
  have : (G : ℤ) < 2 ^ G := by exact_mod_cast Nat.lt_two_pow_self
  have : (2 : ℤ) ^ G ≤ 2 ^ ℓ := pow_le_pow_right₀ (by norm_num) hG.le
  omega

set_option maxHeartbeats 1000000 in
/-- **The run of step `k`**: from the values of the steps before it in the region, the inputs in their slots and the
constants, the code of the step writes its value into `b + k`, changing only `b + k`, the scratch slots and the
registers `r1`, `r2`. -/
theorem XV.sstep {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {C : SLC} {S G : ℕ} (hC : C.OK L S)
    {st : List SStep} {ι : ℕ → ℤ} {ins : List ℕ} {eIn et : ℕ → ℕ × ℕ} {T : ℕ × ℕ} {k : ℕ} {s : SStep}
    (hs : st.getD k (.cst 0) = s) (hk : C.b + k < C.t)
    (hchk : s.chk C.b k ins eIn et T S = true) (hsem : s.Sem (SL.val st C.b ι) G)
    (hT : ev G T < ℓ) (hTa : ev G T < 2 ^ ℓa) (hbk : |SL.val st C.b ι k| ≤ 2 ^ ev G (et k))
    {σ : Env d} (hin : ∀ y ∈ ins, σ.sc y = ι y ∧ |ι y| ≤ 2 ^ ev G (eIn y))
    (hreg : ∀ j < k, σ.sc (C.b + j) = SL.val st C.b ι j ∧ |SL.val st C.b ι j| ≤ 2 ^ ev G (et j))
    (hz : σ.sc C.z = 0) (h1 : σ.sc C.one = 1) (h2 : σ.sc C.two = 2) (h4 : σ.sc C.four = 4)
    (hn1 : σ.nat C.n1 = 1) :
    XRunsB L X ℓa ℓ (s.code L C k) σ (ev G (s.unitsP et)) (fun σ' =>
      σ'.sc (C.b + k) = SL.val st C.b ι k ∧ σ'.draws = σ.draws ∧
      FrameP (fun y => y = C.b + k ∨ C.t ≤ y) (fun j => j = C.r1 ∨ j = C.r2) σ σ') := by
  obtain ⟨hS, hr1, hr2, hn1l, r12, r1n, r2n, zb, ob, tb, fb, nd, bt⟩ := hC
  have hv := SL.val_eq st C.b ι k
  rw [hs] at hv
  have hTle : ∀ {p : ℕ × ℕ}, ple p T = true → ev G p < ℓ := fun h => lt_of_le_of_lt (ev_mono h) hT
  have hTlea : ∀ {p : ℕ × ℕ}, ple p T = true → ev G p < 2 ^ ℓa := fun h => lt_of_le_of_lt (ev_mono h) hTa
  have hz' : σ.sc C.z = ((0 : ℤ) : ℝ) := by rw [hz]; simp
  cases s with
  | cst c =>
    simp only [SStep.chk, Bool.and_eq_true, decide_eq_true_eq] at hchk
    simp only [SStep.sem] at hv
    have hcT : |c| < 2 ^ ℓ := by
      rw [← hv]; exact lt_of_le_of_lt hbk (pow_lt_pow_right₀ (by norm_num) (hTle hchk.2))
    refine XV.mono (XV.constI hL (x := C.b + k) (by omega) c hcT) (by simp [SStep.unitsP, ev]) fun σ' e => ?_
    subst e
    exact ⟨by simp [hv], rfl, (FrameP.refl _ _ σ).setSc (Or.inl rfl) _⟩
  | ie e =>
    simp only [SStep.chk, Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨hl, -⟩, htop⟩, hsc⟩ := hchk
    simp only [SStep.sem] at hv
    refine XV.mono (XV.ieRunP hL (z := C.z) (x := C.b + k) (t := C.t) (G := G)
      (g := fun y => if y < C.b then ι y else if y - C.b < k then SL.val st C.b ι (y - C.b) else 0)
      (f := fun y => if y < C.b then eIn y else et (y - C.b)) (by omega) hk (by omega) hz ?_ (hTle htop))
      (by simp [SStep.unitsP, ev]) fun σ' h => ⟨by rw [h.1, hv], h.2.2.1,
        h.2.2.2.mono (fun y hy => hy) (fun _ h => h.elim)⟩
    refine ieLv_mono ?_ (ieLv_of_B hl)
    intro y hy
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hy
    rcases hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
    · simp only [hy1, ↓reduceIte]; exact ⟨by omega, (hin y hy2).1, (hin y hy2).2⟩
    · have h1 : ¬ y < C.b := by omega
      have h2 : y - C.b < k := by omega
      simp only [h1, h2, ↓reduceIte]
      have := hreg (y - C.b) h2
      rw [show C.b + (y - C.b) = y by omega] at this
      exact ⟨by omega, this.1, this.2⟩
  | sq j =>
    simp only [SStep.chk, Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨hj, -⟩, hjT⟩, h4S⟩ := hchk
    simp only [SStep.Sem] at hsem
    simp only [SStep.sem, hj, ↓reduceIte] at hv
    obtain ⟨ej, bj⟩ := hreg j hj
    have hjT' : ev G (et j) + 3 < ℓ := by have := hTle hjT; simp only [ev] at this ⊢; omega
    have hnv : (((SL.val st C.b ι j).toNat : ℕ) : ℤ) = SL.val st C.b ι j := Int.toNat_of_nonneg hsem
    have hnb : (SL.val st C.b ι j).toNat ≤ 2 ^ ev G (et j) := by
      have : (((SL.val st C.b ι j).toNat : ℕ) : ℤ) ≤ 2 ^ ev G (et j) := by
        rw [hnv]; exact le_trans (le_abs_self _) bj
      exact_mod_cast this
    have hℓn : 4 * (SL.val st C.b ι j).toNat + 4 < 2 ^ ℓ := by
      have h1 : 1 ≤ 2 ^ ev G (et j) := Nat.one_le_two_pow
      have h2 : 2 ^ (ev G (et j) + 3) < 2 ^ ℓ := Nat.pow_lt_pow_right (by norm_num) hjT'
      rw [pow_add] at h2; omega
    have hsz : (SL.val st C.b ι j).toNat.size ≤ ev G (et j) + 1 :=
      Nat.size_le.2 (lt_of_le_of_lt hnb (Nat.pow_lt_pow_right (by norm_num) (by omega)))
    have hnd : [C.t, C.b + k, C.t + 1, C.t + 2, C.t + 3, C.z, C.one, C.two, C.four].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
        and_true, not_false_eq_true] at nd ⊢
      omega
    refine XV.mono (K := 1 + (12 * (SL.val st C.b ι j).toNat.size + 8)) ?_
      (by rw [SStep.unitsP, ev_lin]; omega) (fun _ h => h)
    refine XV.seq (XV.addI hL (x := C.t) (a := C.b + j) (b := C.z) (u := SL.val st C.b ι j) (v := 0) (by omega)
      (by omega) (by omega) ej hz' (lt_of_le_of_lt bj (pow_lt_pow_right₀ (by norm_num) (by omega))) (by simp)
      (by rw [add_zero]; exact lt_of_le_of_lt bj (pow_lt_pow_right₀ (by norm_num) (by omega)))) fun σ1 e1 => ?_
    subst e1
    refine XV.mono (XV.isqrt hL (r := C.t) (dd := C.b + k) (q := C.t + 1) (t := C.t + 2) (n1 := C.t + 3)
      (z := C.z) (one := C.one) (two := C.two) (four := C.four) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) hnd (n := (SL.val st C.b ι j).toNat)
      (by rw [sc_setSc_eq, add_zero]; exact_mod_cast hnv.symm) (by rw [sc_setSc_ne _ (by omega)]; exact hz)
      (by rw [sc_setSc_ne _ (by omega)]; exact h1) (by rw [sc_setSc_ne _ (by omega)]; exact h2)
      (by rw [sc_setSc_ne _ (by omega)]; exact h4) hℓn) le_rfl fun σ' h => ?_
    refine ⟨by rw [h.1, hv]; push_cast; rfl, by rw [h.2.2.2.2.2.1]; rfl, ?_⟩
    exact ((FrameP.refl _ _ σ).setSc (Or.inr le_rfl) _).trans
      (FrameP.of_frame h.2.2 (fun y hy => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy; omega)
        (fun j hj => by simp at hj))
  | pw j =>
    simp only [SStep.chk, Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨⟨hj, -⟩, h1T⟩ := hchk
    simp only [SStep.Sem] at hsem
    obtain ⟨h0, hjG⟩ := hsem
    simp only [SStep.sem, hj, ↓reduceIte] at hv
    obtain ⟨ej, -⟩ := hreg j hj
    have hGℓ : G + 1 < ℓ := by have := hTle h1T; simpa [ev] using this
    have hGa : G + 1 < 2 ^ ℓa := by have := hTlea h1T; simpa [ev] using this
    have hWv : (((SL.val st C.b ι j).toNat : ℕ) : ℤ) = SL.val st C.b ι j := Int.toNat_of_nonneg h0
    have hWG : (SL.val st C.b ι j).toNat ≤ G := by omega
    refine XV.mono (K := 1 + (4 * (SL.val st C.b ι j).toNat + 4)) ?_ (by simp only [SStep.unitsP, ev]; omega)
      (fun _ h => h)
    refine XV.seq (XV.rtoN hL (i := C.r1) (x := C.b + j) hr1 (by omega) (by rw [ej]; exact_mod_cast h0) ?_
      (by rw [ej]; exact natZ_lt h0 hjG (by omega))) fun σ1 e1 => ?_
    · rw [ej]
      have : SL.val st C.b ι j < 2 ^ ℓa := by
        have : ((G : ℕ) : ℤ) + 1 < 2 ^ ℓa := by exact_mod_cast hGa
        omega
      exact_mod_cast this
    subst e1
    refine XV.mono (XV.pow2 hL (p := C.b + k) (i := C.r2) (n := C.r1) (one := C.n1) (by omega) hr2 hr1 hn1l
      (Ne.symm r12) r2n (W := (SL.val st C.b ι j).toNat) (by simp [ej]) (by simp [Ne.symm r1n, hn1])
      (by omega) (by omega)) le_rfl fun σ' h => ?_
    refine ⟨by rw [h.1, hv]; push_cast; rfl, by rw [h.2.2.2.2.2.1]; rfl, ?_⟩
    exact ((FrameP.refl _ _ σ).setNat (Or.inl rfl) _).trans
      (FrameP.of_frame h.2.2 (fun y hy => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy; omega)
        (fun j hj => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj; exact Or.inr hj))
  | cl j =>
    simp only [SStep.chk, Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨hj, -⟩, hjT⟩, h1S⟩ := hchk
    simp only [SStep.Sem] at hsem
    simp only [SStep.sem, hj, ↓reduceIte] at hv
    obtain ⟨ej, bj⟩ := hreg j hj
    have hE := hTle hjT
    have hEa := hTlea hjT
    have hnb : (SL.val st C.b ι j).toNat ≤ 2 ^ ev G (et j) := by
      have : (((SL.val st C.b ι j).toNat : ℕ) : ℤ) ≤ 2 ^ ev G (et j) := by
        rw [Int.toNat_of_nonneg hsem]; exact le_trans (le_abs_self _) bj
      exact_mod_cast this
    have hcl : Nat.clog 2 (SL.val st C.b ι j).toNat ≤ ev G (et j) := Nat.clog_le_of_le_pow hnb
    refine XV.mono (K := 4 * ev G (et j) + 4 + 1) ?_ (by rw [SStep.unitsP, ev_lin]) (fun _ h => h)
    refine XV.seq (XV.clogS hL (w := C.t) (x := C.b + j) (c := C.r1) (one := C.n1) (G := ev G (et j))
      (by omega) (by omega) hr1 hn1l (by omega) r1n ej hsem (le_trans (le_abs_self _) bj) hn1 hEa hE)
      fun σ1 h1' => ?_
    refine XV.mono (XV.ncastI hL (x := C.b + k) (i := C.r1) (by omega) hr1 (by rw [h1'.1]; omega)) le_rfl
      fun σ' e => ?_
    subst e
    refine ⟨by rw [sc_setSc_eq, h1'.1, hv], by rw [← h1'.2.1]; rfl, ?_⟩
    exact (h1'.2.2.mono (S' := fun y => y = C.b + k ∨ C.t ≤ y) (N' := fun j => j = C.r1 ∨ j = C.r2)
      (fun y hy => Or.inr (by omega)) (fun j hj => Or.inl hj)).setSc (Or.inl rfl) _
  | mc jq jQ jX =>
    simp only [SStep.chk, Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨⟨⟨hjq, hjQ⟩, hjX⟩, -⟩, h2T⟩, h3S⟩ := hchk
    simp only [SStep.Sem] at hsem
    obtain ⟨h0, hqG, hQ, hX0, hXQ⟩ := hsem
    simp only [SStep.sem, hjq, hjX, ↓reduceIte] at hv
    obtain ⟨eq', -⟩ := hreg jq hjq
    obtain ⟨eQ, -⟩ := hreg jQ hjQ
    obtain ⟨eX, -⟩ := hreg jX hjX
    have hGℓ : 2 * G + 1 < ℓ := by have := hTle h2T; simpa [ev] using this
    have hGa : 2 * G + 1 < 2 ^ ℓa := by have := hTlea h2T; simpa [ev] using this
    set q := (SL.val st C.b ι jq).toNat with hqdef
    have hqv : ((q : ℕ) : ℤ) = SL.val st C.b ι jq := Int.toNat_of_nonneg h0
    have hqG' : q ≤ G := by omega
    have hXv : (((SL.val st C.b ι jX).toNat : ℕ) : ℤ) = SL.val st C.b ι jX := Int.toNat_of_nonneg hX0
    have hXq : (SL.val st C.b ι jX).toNat ≤ 2 ^ q := by
      have : (((SL.val st C.b ι jX).toNat : ℕ) : ℤ) ≤ 2 ^ q := by rw [hXv, ← hQ]; exact hXQ
      exact_mod_cast this
    refine XV.mono (K := 1 + (8 * q + 6)) ?_ (by simp only [SStep.unitsP, ev]; omega) (fun _ h => h)
    refine XV.seq (XV.rtoN hL (i := C.r1) (x := C.b + jq) hr1 (by omega) (by rw [eq']; exact_mod_cast h0) ?_
      (by rw [eq']; exact natZ_lt h0 hqG (by omega))) fun σ1 e1 => ?_
    · rw [eq']
      have : SL.val st C.b ι jq < 2 ^ ℓa := by
        have : ((G : ℕ) : ℤ) * 2 + 1 < 2 ^ ℓa := by exact_mod_cast (by omega : G * 2 + 1 < 2 ^ ℓa)
        omega
      exact_mod_cast this
    subst e1
    refine XV.mono (XV.mercG hL (S := C.b + k) (Xin := C.b + jX) (P := C.t) (I := C.t + 1) (T := C.t + 2)
      (z := C.z) (one := C.one) (Qs := C.b + jQ) (i := C.r2) (nq := C.r1) (none := C.n1) (by omega) hr2 hr1 hn1l
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (Ne.symm r12) r2n (q := q)
      (Xv := (SL.val st C.b ι jX).toNat) (by simp [hz]) (by simp [h1])
      (by simp only [Env.setNat_sc]; rw [eQ, hQ])
      (by simp only [Env.setNat_sc]; rw [eX, hXv]) hXq (by simp [eq', hqdef]) (by simp [Ne.symm r1n, hn1])
      (by omega) (by omega)) le_rfl fun σ' h => ?_
    refine ⟨by rw [h.1, hv], by rw [h.2.1]; rfl, ?_⟩
    exact ((FrameP.refl _ _ σ).setNat (Or.inl rfl) _).trans
      (h.2.2.mono (fun y hy => by omega) (fun j hj => Or.inr hj))
  | mx j =>
    simp only [SStep.chk, Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨⟨hj, -⟩, hjT⟩ := hchk
    simp only [SStep.sem, hj, ↓reduceIte] at hv
    obtain ⟨ej, bj⟩ := hreg j hj
    have hb := lt_of_le_of_lt bj (pow_lt_pow_right₀ (by norm_num) (hTle hjT))
    have hb0 : |(0 : ℤ)| < 2 ^ ℓ := by simp
    refine XV.mono (K := 1 + 2) ?_ (by simp [SStep.unitsP, ev]) (fun _ h => h)
    refine XV.seq (XV.addI hL (x := C.b + k) (a := C.b + j) (b := C.z) (u := SL.val st C.b ι j) (v := 0)
      (by omega) (by omega) (by omega) ej hz' hb hb0 (by rw [add_zero]; exact hb)) fun σ1 e1 => ?_
    subst e1
    have hx1 : |(σ.setSc (C.b + k) ((SL.val st C.b ι j + 0 : ℤ) : ℝ)).sc (C.b + k)| < 2 ^ ℓ := by
      rw [sc_setSc_eq, add_zero]; exact XV.abs_int_lt hb
    have hz1 : |(σ.setSc (C.b + k) ((SL.val st C.b ι j + 0 : ℤ) : ℝ)).sc C.z| < 2 ^ ℓ := by
      rw [sc_setSc_ne _ (by omega), hz]; simp
    have hcz : (σ.setSc (C.b + k) ((SL.val st C.b ι j + 0 : ℤ) : ℝ)).sc C.z = ((0 : ℤ) : ℝ) := by
      rw [sc_setSc_ne _ (by omega), hz']
    have hc : (σ.setSc (C.b + k) ((SL.val st C.b ι j + 0 : ℤ) : ℝ)).sc (C.b + k) <
        (σ.setSc (C.b + k) ((SL.val st C.b ι j + 0 : ℤ) : ℝ)).sc C.z ↔ SL.val st C.b ι j < 0 := by
      rw [sc_setSc_eq, hcz, add_zero]; exact_mod_cast Iff.rfl
    by_cases hneg : SL.val st C.b ι j < 0
    · refine XV.ifS_t hL (by omega) (by omega) hx1 hz1 (hc.2 hneg) (XV.mono (XV.addI hL (x := C.b + k)
        (a := C.z) (b := C.z) (u := 0) (v := 0) (by omega) (by omega) (by omega) hcz hcz hb0 hb0
        (by simpa using hb0)) le_rfl fun σ' e => ?_)
      subst e
      refine ⟨by rw [sc_setSc_eq, hv, max_eq_right hneg.le]; simp, rfl, ?_⟩
      exact ((FrameP.refl _ _ σ).setSc (Or.inl rfl) _).setSc (Or.inl rfl) _
    · refine XV.ifS_f hL (by omega) (by omega) hx1 hz1 (fun h => hneg (hc.1 h))
        (XV.mono (XV.skip _) le_rfl fun σ' e => ?_)
      subst e
      refine ⟨by rw [sc_setSc_eq, hv, max_eq_left (not_lt.1 hneg)]; simp, rfl, ?_⟩
      exact (FrameP.refl _ _ σ).setSc (Or.inl rfl) _

/-! ## The run of a straight line -/

/-- The code of the steps `rest`, the first of them being step `k`. -/
def SL.codeAux (L : Layout) (C : SLC) : List SStep → ℕ → XCmd
  | [], _ => .skip
  | s :: rest, k => .seq (s.code L C k) (SL.codeAux L C rest (k + 1))

/-- The code of a straight line. -/
def SL.code (L : Layout) (C : SLC) (st : List SStep) : XCmd := SL.codeAux L C st 0

/-- The pair of the units of a list of steps. -/
def SL.unitsP (et : ℕ → ℕ × ℕ) : List SStep → ℕ × ℕ
  | [] => (0, 0)
  | s :: rest => ((s.unitsP et).1 + (SL.unitsP et rest).1, (s.unitsP et).2 + (SL.unitsP et rest).2)

/-- The static test of the steps `rest`, the first of them being step `k`. -/
def SL.chkAux (b : ℕ) (ins : List ℕ) (eIn et : ℕ → ℕ × ℕ) (T : ℕ × ℕ) (S : ℕ) : List SStep → ℕ → Bool
  | [], _ => true
  | s :: rest, k => s.chk b k ins eIn et T S && SL.chkAux b ins eIn et T S rest (k + 1)

/-- The static test of a straight line: the inputs below the region, every step. -/
def SL.chk (b : ℕ) (ins : List ℕ) (eIn et : ℕ → ℕ × ℕ) (T : ℕ × ℕ) (S : ℕ) (st : List SStep) : Bool :=
  ins.all (· < b) && SL.chkAux b ins eIn et T S st 0

theorem ev_add (G : ℕ) (p q : ℕ × ℕ) : ev G (p.1 + q.1, p.2 + q.2) = ev G p + ev G q := by unfold ev; ring

theorem SL.chkAux_get {b : ℕ} {ins : List ℕ} {eIn et : ℕ → ℕ × ℕ} {T : ℕ × ℕ} {S : ℕ} :
    ∀ (rest : List SStep) (k i : ℕ), SL.chkAux b ins eIn et T S rest k = true → i < rest.length →
      (rest.getD i (.cst 0)).chk b (k + i) ins eIn et T S = true
  | [], _, _, _, hi => absurd hi (by simp)
  | s :: rest, k, 0, h, _ => by
    simp only [SL.chkAux, Bool.and_eq_true] at h; simpa using h.1
  | s :: rest, k, i + 1, h, hi => by
    simp only [SL.chkAux, Bool.and_eq_true] at h
    have := SL.chkAux_get rest (k + 1) i h.2 (by simpa using hi)
    simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem SL.chk_get {b : ℕ} {ins : List ℕ} {eIn et : ℕ → ℕ × ℕ} {T : ℕ × ℕ} {S : ℕ} {st : List SStep}
    (h : SL.chk b ins eIn et T S st = true) :
    (∀ y ∈ ins, y < b) ∧ ∀ k < st.length, (st.getD k (.cst 0)).chk b k ins eIn et T S = true := by
  simp only [SL.chk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, fun k hk => by simpa using SL.chkAux_get st 0 k h.2 hk⟩

theorem SL.drop_cons {st rest : List SStep} {s : SStep} {k : ℕ} (h : st.drop k = s :: rest) :
    k < st.length ∧ st.getD k (.cst 0) = s ∧ st.drop (k + 1) = rest := by
  have hk : k < st.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by omega)] at h
    exact List.cons_ne_nil s rest h.symm
  rw [List.drop_eq_getElem_cons hk] at h
  obtain ⟨h1, h2⟩ := List.cons.inj h
  refine ⟨hk, ?_, h2⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some, h1]

set_option maxHeartbeats 400000 in
/-- **The run of a straight line**: the region `b, ..., b + |st| - 1` ends holding the values of the steps; only the
region, the scratch slots and the registers `r1`, `r2` change; no coin is read. -/
theorem XV.sl {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {C : SLC} {S G : ℕ} (hC : C.OK L S)
    {st : List SStep} {ι : ℕ → ℤ} {ins : List ℕ} {eIn et : ℕ → ℕ × ℕ} {T : ℕ × ℕ}
    (hchk : SL.chk C.b ins eIn et T S st = true)
    (hsem : ∀ k < st.length, (st.getD k (.cst 0)).Sem (SL.val st C.b ι) G)
    (hlen : C.b + st.length ≤ C.t) (hT : ev G T < ℓ) (hTa : ev G T < 2 ^ ℓa)
    (hinB : ∀ y ∈ ins, |ι y| ≤ 2 ^ ev G (eIn y))
    {σ : Env d} (hin : ∀ y ∈ ins, σ.sc y = ι y)
    (hz : σ.sc C.z = 0) (h1 : σ.sc C.one = 1) (h2 : σ.sc C.two = 2) (h4 : σ.sc C.four = 4)
    (hn1 : σ.nat C.n1 = 1) :
    XRunsB L X ℓa ℓ (SL.code L C st) σ (ev G (SL.unitsP et st)) (fun σ' =>
      (∀ k < st.length, σ'.sc (C.b + k) = SL.val st C.b ι k) ∧ σ'.draws = σ.draws ∧
      FrameP (fun y => (C.b ≤ y ∧ y < C.b + st.length) ∨ C.t ≤ y) (fun j => j = C.r1 ∨ j = C.r2) σ σ') := by
  obtain ⟨hinb, hall⟩ := SL.chk_get hchk
  have hbnd := SL.val_bound st C.b ι ins eIn et T S G hall hsem hinB
  have hC' := hC
  obtain ⟨-, -, -, -, -, r1n, r2n, zb, ob, tb, fb, -, -⟩ := hC'
  set R : ℕ → Prop := fun y => (C.b ≤ y ∧ y < C.b + st.length) ∨ C.t ≤ y with hR
  set N : ℕ → Prop := fun j => j = C.r1 ∨ j = C.r2 with hN
  have key : ∀ (rest : List SStep) (k : ℕ) (σ' : Env d), st.drop k = rest →
      (∀ j < k, σ'.sc (C.b + j) = SL.val st C.b ι j) → σ'.draws = σ.draws → FrameP R N σ σ' →
      XRunsB L X ℓa ℓ (SL.codeAux L C rest k) σ' (ev G (SL.unitsP et rest)) (fun σ'' =>
        (∀ k < st.length, σ''.sc (C.b + k) = SL.val st C.b ι k) ∧ σ''.draws = σ.draws ∧ FrameP R N σ σ'') := by
    intro rest
    induction rest with
    | nil =>
      intro k σ' hd hr hdr hF
      have hk : st.length ≤ k := List.drop_eq_nil_iff.1 hd
      exact XV.mono (XV.skip σ') (by simp [SL.unitsP, ev]) fun σ'' e => by
        subst e; exact ⟨fun j hj => hr j (by omega), hdr, hF⟩
    | cons s rest ih =>
      intro k σ' hd hr hdr hF
      obtain ⟨hk, hs, hd'⟩ := SL.drop_cons hd
      have hsc : ∀ y, y < C.b → σ'.sc y = σ.sc y := fun y hy => hF.2.1 y (by simp only [hR]; omega)
      refine XV.mono (XV.seq (XV.sstep hL hC (st := st) (ι := ι) (ins := ins) (eIn := eIn) (et := et) (T := T)
        (G := G) hs (by omega) (by rw [← hs]; exact hall k hk) (by rw [← hs]; exact hsem k hk) hT hTa
        (hbnd k hk) (σ := σ') (fun y hy => ⟨by rw [hsc y (hinb y hy)]; exact hin y hy, hinB y hy⟩)
        (fun j hj => ⟨hr j hj, hbnd j (by omega)⟩) (by rw [hsc _ zb]; exact hz) (by rw [hsc _ ob]; exact h1)
        (by rw [hsc _ tb]; exact h2) (by rw [hsc _ fb]; exact h4)
        (by rw [hF.1 _ (by simp only [hN]; omega)]; exact hn1))
        fun σ1 hσ1 => ih (k + 1) σ1 hd' (fun j hj => ?_) (by rw [hσ1.2.1, hdr]) ?_)
        (by simp only [SL.unitsP, ev_add, le_refl]) fun _ h => h
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · rw [hσ1.2.2.2.1 _ (by omega)]; exact hr j hj
        · subst hj; exact hσ1.1
      · exact hF.trans (hσ1.2.2.mono (fun y hy => by simp only [hR]; omega) (fun j hj => hj))
  exact key st 0 σ (List.drop_zero) (fun j hj => absurd hj (Nat.not_lt_zero _)) rfl (FrameP.refl R N σ)

end AdversarialBco.Bit.Transfer.BLM
