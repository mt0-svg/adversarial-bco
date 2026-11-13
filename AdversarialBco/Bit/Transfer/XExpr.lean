/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XEllRow

@[expose] public section

/-!
# Integer expressions compiled into `XCmd`

Expressions `IE` over the scalar slots and the array cells of an environment (`+`, `-`, `×`, Euclidean quotient), their
value `IE.eval`, their code `IE.code` (the value into a slot `x`, scratch slots from `t`, a slot `z` holding `0`) and
the compiler theorem `XV.ie`. The magnitudes come from the leaves: integer leaves below `2^E` and every node exponent
`IE.top E` below `ℓ` give the run conditions (`IE.OK_of_leaves`).

**The package** `XV.ieRun`: the static conditions, the leaves, the top exponent and the value give the run of the code
with `ExprPost` (the value in `x`, below `2^ℓ`, the count of draws kept, only `x` and the slots from `t` changed). Each
expression of a routine gets one lemma `XV.<name>_run` proved by `XV.ieRun` and four `simp only` calls; `XV.ieEll_run`
(the entry of the matrix step of ELL-R) is the model.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach

variable {d : ℕ}

/-! ## Expressions -/

/-- Integer expressions: a scalar slot, the array cell `a[nat i]`, an operation `+`, `-`, `×` of `Op2`, the Euclidean
quotient. -/
inductive IE
  | sc (y : ℕ)
  | arr (a i : ℕ)
  | op (o : RealRAM.Op2) (a b : IE)
  | ediv (a b : IE)

namespace IE

/-- The value of an expression in an environment. -/
noncomputable def eval (σ : Env d) : IE → ℝ
  | .sc y => σ.sc y
  | .arr a i => σ.arr a (σ.nat i)
  | .op o a b => o.eval (a.eval σ) (b.eval σ)
  | .ediv a b => ((⌊a.eval σ⌋ / ⌊b.eval σ⌋ : ℤ) : ℝ)

/-- The scratch slots of the code. -/
def scr : IE → ℕ
  | .sc _ => 0
  | .arr _ _ => 0
  | .op _ a b => a.scr + b.scr + 2
  | .ediv a b => a.scr + b.scr + 2

/-- The units of the code. -/
def units : IE → ℕ
  | .sc _ => 1
  | .arr _ _ => 2
  | .op _ a b => a.units + b.units + 1
  | .ediv a b => a.units + b.units + 1

/-- The code: the value into the slot `x`, the slots `t, ..., t + scr - 1` as scratch, `z` a slot holding `0`. -/
def code (L : Layout) (z : ℕ) : IE → ℕ → ℕ → XCmd
  | .sc y, x, _ => toX (VL.sop2 L .add x y z)
  | .arr a i, x, _ => toX (VL.aget L x a i)
  | .op o a b, x, t => .seq (.seq (a.code L z t (t + 1)) (b.code L z (t + 1 + a.scr) (t + 2 + a.scr)))
      (toX (VL.sop2 L o x t (t + 1 + a.scr)))
  | .ediv a b, x, t => .seq (.seq (a.code L z t (t + 1)) (b.code L z (t + 1 + a.scr) (t + 2 + a.scr)))
      (xsidiv L x t (t + 1 + a.scr))

/-- The static conditions: the slots read lie below `t`, the arrays and registers in the layout, no real division. -/
def WF (L : Layout) (t : ℕ) : IE → Prop
  | .sc y => y < t
  | .arr a i => a < L.NA ∧ i < L.NN
  | .op o a b => o ≠ .div ∧ a.WF L t ∧ b.WF L t
  | .ediv a b => a.WF L t ∧ b.WF L t

/-- The run conditions: every value below `2^ℓ`, every index in its array. -/
def OK (ℓ : ℕ) (σ : Env d) : IE → Prop
  | .sc y => |σ.sc y| < 2 ^ ℓ
  | .arr a i => σ.nat i < asz d ∧ |σ.arr a (σ.nat i)| < 2 ^ ℓ
  | .op o a b => a.OK ℓ σ ∧ b.OK ℓ σ ∧ |o.eval (a.eval σ) (b.eval σ)| < 2 ^ ℓ
  | .ediv a b => a.OK ℓ σ ∧ b.OK ℓ σ ∧ |((⌊a.eval σ⌋ / ⌊b.eval σ⌋ : ℤ) : ℝ)| < 2 ^ ℓ

theorem OK.bound {ℓ : ℕ} {σ : Env d} : ∀ {e : IE}, e.OK ℓ σ → |e.eval σ| < 2 ^ ℓ
  | .sc _, h => h
  | .arr _ _, h => h.2
  | .op _ _ _, h => h.2.2
  | .ediv _ _, h => h.2.2

theorem WF.mono {L : Layout} {t t' : ℕ} (htt : t ≤ t') : ∀ {e : IE}, e.WF L t → e.WF L t'
  | .sc _, h => lt_of_lt_of_le h htt
  | .arr _ _, h => h
  | .op _ _ _, h => ⟨h.1, WF.mono htt h.2.1, WF.mono htt h.2.2⟩
  | .ediv _ _, h => ⟨WF.mono htt h.1, WF.mono htt h.2⟩

/-- Two environments with the same registers and arrays and the same slots below `t`. -/
def Same (t : ℕ) (σ σ' : Env d) : Prop := σ'.nat = σ.nat ∧ σ'.arr = σ.arr ∧ ∀ y < t, σ'.sc y = σ.sc y

theorem eval_congr {L : Layout} {t : ℕ} {σ σ' : Env d} (h : Same t σ σ') :
    ∀ {e : IE}, e.WF L t → e.eval σ' = e.eval σ
  | .sc _, hw => h.2.2 _ hw
  | .arr _ _, _ => by simp only [eval, h.1, h.2.1]
  | .op _ _ _, hw => by simp only [eval, eval_congr h hw.2.1, eval_congr h hw.2.2]
  | .ediv _ _, hw => by simp only [eval, eval_congr h hw.1, eval_congr h hw.2]

theorem OK_congr {L : Layout} {t ℓ : ℕ} {σ σ' : Env d} (h : Same t σ σ') :
    ∀ {e : IE}, e.WF L t → e.OK ℓ σ → e.OK ℓ σ'
  | .sc _, hw, ho => by simp only [OK, h.2.2 _ hw]; exact ho
  | .arr _ _, _, ho => by simp only [OK, h.1, h.2.1]; exact ho
  | .op _ _ _, hw, ho => ⟨OK_congr h hw.2.1 ho.1, OK_congr h hw.2.2 ho.2.1, by
      rw [eval_congr h hw.2.1, eval_congr h hw.2.2]; exact ho.2.2⟩
  | .ediv _ _, hw, ho => ⟨OK_congr h hw.1 ho.1, OK_congr h hw.2 ho.2.1, by
      rw [eval_congr h hw.1, eval_congr h hw.2]; exact ho.2.2⟩

theorem Same.of_frame {t : ℕ} {S : ℕ → Prop} {σ σ' : Env d} (hS : ∀ y, S y → t ≤ y)
    (h : FrameP S (fun _ => False) σ σ') : Same t σ σ' :=
  ⟨funext fun j => h.1 j id, h.2.2.1, fun y hy => h.2.1 y fun hs => absurd (hS y hs) (by omega)⟩

end IE

/-! ## The compiler theorem for expressions -/

namespace XV

variable {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ}

/-- What the code of an expression does: the value in `x`, the count of draws kept, only `x` and the scratch slots
changed. -/
def IEPost (σ : Env d) (x t s : ℕ) (v : ℝ) (σ' : Env d) : Prop :=
  σ'.sc x = v ∧ σ'.draws = σ.draws ∧ FrameP (fun y => y = x ∨ (t ≤ y ∧ y < t + s)) (fun _ => False) σ σ'

/-- The two operands of a binary node: `a` into `t`, then `b` into `t + 1 + scr a`. -/
theorem iePair {z : ℕ} {a b : IE} {t : ℕ} {σ : Env d}
    (ha : ∀ (x t : ℕ) (σ : Env d), a.WF L t → z < t → x < t → t + a.scr ≤ L.NS → σ.sc z = 0 → a.OK ℓ σ →
      XRunsB L X ℓa ℓ (a.code L z x t) σ a.units (IEPost σ x t a.scr (a.eval σ)))
    (hb : ∀ (x t : ℕ) (σ : Env d), b.WF L t → z < t → x < t → t + b.scr ≤ L.NS → σ.sc z = 0 → b.OK ℓ σ →
      XRunsB L X ℓa ℓ (b.code L z x t) σ b.units (IEPost σ x t b.scr (b.eval σ)))
    (hwa : a.WF L t) (hwb : b.WF L t) (hz : z < t) (hS : t + a.scr + b.scr + 2 ≤ L.NS) (hz0 : σ.sc z = 0)
    (hoa : a.OK ℓ σ) (hob : b.OK ℓ σ) :
    XRunsB L X ℓa ℓ (.seq (a.code L z t (t + 1)) (b.code L z (t + 1 + a.scr) (t + 2 + a.scr))) σ
      (a.units + b.units) (fun σ' => σ'.sc t = a.eval σ ∧ σ'.sc (t + 1 + a.scr) = b.eval σ ∧ σ'.draws = σ.draws ∧
        FrameP (fun y => t ≤ y ∧ y < t + a.scr + b.scr + 2) (fun _ => False) σ σ') := by
  refine seq (ha t (t + 1) σ (hwa.mono (by omega)) (by omega) (by omega) (by omega) hz0 hoa) fun σ1 h1 => ?_
  have hs1 : IE.Same t σ σ1 := IE.Same.of_frame (fun y hy => by omega) h1.2.2
  refine mono (hb (t + 1 + a.scr) (t + 2 + a.scr) σ1 (hwb.mono (by omega)) (by omega) (by omega) (by omega)
    (by rw [hs1.2.2 z hz, hz0]) (IE.OK_congr hs1 hwb hob)) le_rfl fun σ2 h2 => ?_
  refine ⟨?_, by rw [h2.1, IE.eval_congr hs1 hwb], by rw [h2.2.1, h1.2.1], ?_⟩
  · rw [h2.2.2.2.1 t (by omega), h1.1]
  · exact (h1.2.2.mono (fun y hy => by omega) (fun _ h => h)).trans
      (h2.2.2.mono (fun y hy => by omega) (fun _ h => h))

/-- **The compiler theorem for expressions**: the code of `e` puts its value in the slot `x` and changes only `x` and
its scratch slots. -/
theorem ie (hL : LayOK L d ℓa) {z : ℕ} (hzL : z < L.NS) :
    ∀ (e : IE) (x t : ℕ) (σ : Env d), e.WF L t → z < t → x < t → t + e.scr ≤ L.NS → σ.sc z = 0 → e.OK ℓ σ →
      XRunsB L X ℓa ℓ (e.code L z x t) σ e.units (IEPost σ x t e.scr (e.eval σ))
  | .sc y, x, t, σ, hw, hz, hx, hS, hz0, ho => by
    refine mono (sop2 hL (by omega) (by simp only [IE.WF] at hw; omega) hzL .add (by intro h; cases h) ho
      (by rw [hz0]; simp) (by simp only [RealRAM.Op2.eval, hz0, add_zero]; exact ho)) le_rfl fun σ' e => ?_
    subst e
    exact ⟨by simp [RealRAM.Op2.eval, hz0, IE.eval], rfl, (FrameP.refl _ _ σ).setSc (Or.inl rfl) _⟩
  | .arr a i, x, t, σ, hw, hz, hx, hS, hz0, ho => by
    refine mono (XV.aget hL (by omega) hw.1 hw.2 ho.1 ho.2) le_rfl fun σ' e => ?_
    subst e
    exact ⟨by simp [IE.eval], rfl, (FrameP.refl _ _ σ).setSc (Or.inl rfl) _⟩
  | .op o a b, x, t, σ, hw, hz, hx, hS, hz0, ho => by
    simp only [IE.scr] at hS
    refine seq (iePair (ie hL hzL a) (ie hL hzL b) hw.2.1 hw.2.2 hz (by omega) hz0 ho.1 ho.2.1)
      fun σ2 h2 => ?_
    refine mono (sop2 hL (by omega) (by omega) (by omega) o hw.1 (by rw [h2.1]; exact ho.1.bound)
      (by rw [h2.2.1]; exact ho.2.1.bound) (by rw [h2.1, h2.2.1]; exact ho.2.2)) le_rfl fun σ' e => ?_
    subst e
    refine ⟨by simp [IE.eval, h2.1, h2.2.1], by simp [h2.2.2.1], ?_⟩
    exact (h2.2.2.2.mono (S' := fun y => y = x ∨ (t ≤ y ∧ y < t + (a.scr + b.scr + 2)))
      (fun y hy => Or.inr (by omega)) (fun _ h => h)).setSc (Or.inl rfl) _
  | .ediv a b, x, t, σ, hw, hz, hx, hS, hz0, ho => by
    simp only [IE.scr] at hS
    refine seq (iePair (ie hL hzL a) (ie hL hzL b) hw.1 hw.2 hz (by omega) hz0 ho.1 ho.2.1)
      fun σ2 h2 => ?_
    refine mono (sidiv hL (by omega) (by omega) (by omega) (by rw [h2.1]; exact ho.1.bound)
      (by rw [h2.2.1]; exact ho.2.1.bound)) le_rfl fun σ' e => ?_
    subst e
    refine ⟨by simp [IE.eval, h2.1, h2.2.1], by simp [h2.2.2.1], ?_⟩
    exact (h2.2.2.2.mono (S' := fun y => y = x ∨ (t ≤ y ∧ y < t + (a.scr + b.scr + 2)))
      (fun y hy => Or.inr (by omega)) (fun _ h => h)).setSc (Or.inl rfl) _

end XV

/-! ## Magnitudes from the leaves -/

namespace IE

/-- The exponent of a bound on the value, from the bound `2^E` on the leaves. -/
def mag (E : ℕ) : IE → ℕ
  | .sc _ => E
  | .arr _ _ => E
  | .op .mul a b => a.mag E + b.mag E
  | .op _ a b => max (a.mag E) (b.mag E) + 1
  | .ediv a _ => a.mag E

/-- The largest exponent over the nodes. -/
def top (E : ℕ) : IE → ℕ
  | .sc _ => E
  | .arr _ _ => E
  | .op o a b => max ((IE.op o a b).mag E) (max (a.top E) (b.top E))
  | .ediv a b => max (a.mag E) (max (a.top E) (b.top E))

/-- Every leaf is an integer of absolute value at most `2^E`, every index in its array. -/
def Leaves (E : ℕ) (σ : Env d) : IE → Prop
  | .sc y => ∃ v : ℤ, σ.sc y = v ∧ |v| ≤ 2 ^ E
  | .arr a i => σ.nat i < asz d ∧ ∃ v : ℤ, σ.arr a (σ.nat i) = v ∧ |v| ≤ 2 ^ E
  | .op _ a b => a.Leaves E σ ∧ b.Leaves E σ
  | .ediv a b => a.Leaves E σ ∧ b.Leaves E σ

theorem mag_le_top (E : ℕ) : ∀ e : IE, e.mag E ≤ e.top E
  | .sc _ => le_rfl
  | .arr _ _ => le_rfl
  | .op _ _ _ => le_max_left _ _
  | .ediv _ _ => le_max_left _ _

/-- The value of an expression with integer leaves is an integer below `2^mag`. -/
theorem int_of_leaves {L : Layout} {t E : ℕ} {σ : Env d} :
    ∀ {e : IE}, e.WF L t → e.Leaves E σ → ∃ v : ℤ, e.eval σ = v ∧ |v| ≤ 2 ^ e.mag E
  | .sc _, _, h => h
  | .arr _ _, _, h => h.2
  | .op o a b, hw, h => by
    obtain ⟨u, hu, hu'⟩ := int_of_leaves hw.2.1 h.1
    obtain ⟨v, hv, hv'⟩ := int_of_leaves hw.2.2 h.2
    have hm := le_max_left (a.mag E) (b.mag E)
    have hm' := le_max_right (a.mag E) (b.mag E)
    have hp : ∀ {k l : ℕ}, k ≤ l → (2 : ℤ) ^ k ≤ 2 ^ l := fun hkl => pow_le_pow_right₀ (by norm_num) hkl
    cases o with
    | add => exact ⟨u + v, by simp [eval, hu, hv, RealRAM.Op2.eval], by
        simpa [mag, pow_succ, two_mul] using absI_add_le (absI_mono hu' hm) (absI_mono hv' hm')⟩
    | sub => exact ⟨u - v, by simp [eval, hu, hv, RealRAM.Op2.eval], by
        simpa [mag, pow_succ, two_mul] using absI_sub_le (absI_mono hu' hm) (absI_mono hv' hm')⟩
    | mul => exact ⟨u * v, by simp [eval, hu, hv, RealRAM.Op2.eval], absI_mul_le hu' hv'⟩
    | div => exact absurd rfl hw.1
  | .ediv a b, hw, h => by
    obtain ⟨u, hu, hu'⟩ := int_of_leaves hw.1 h.1
    obtain ⟨v, hv, hv'⟩ := int_of_leaves hw.2 h.2
    exact ⟨u / v, by simp [eval, hu, hv], (absI_ediv_le u v).trans hu'⟩

/-- **Bounds from the leaves**: integer leaves below `2^E` and every node exponent below `ℓ` give the run
conditions. -/
theorem OK_of_leaves {L : Layout} {t E ℓ : ℕ} {σ : Env d} :
    ∀ {e : IE}, e.WF L t → e.Leaves E σ → e.top E < ℓ → e.OK ℓ σ
  | .sc _, _, h, hl => by
    obtain ⟨v, hv, hv'⟩ := h
    simp only [OK, hv]
    exact XV.abs_int_lt (lt_of_le_of_lt hv' (pow_lt_pow_right₀ (by norm_num) hl))
  | .arr _ _, _, h, hl => by
    obtain ⟨hk, v, hv, hv'⟩ := h
    refine ⟨hk, ?_⟩
    rw [hv]
    exact XV.abs_int_lt (lt_of_le_of_lt hv' (pow_lt_pow_right₀ (by norm_num) hl))
  | .op o a b, hw, h, hl => by
    simp only [top, max_lt_iff] at hl
    refine ⟨OK_of_leaves hw.2.1 h.1 hl.2.1, OK_of_leaves hw.2.2 h.2 hl.2.2, ?_⟩
    obtain ⟨v, hv, hv'⟩ := int_of_leaves (e := .op o a b) hw h
    rw [show o.eval (a.eval σ) (b.eval σ) = (IE.op o a b).eval σ from rfl, hv]
    exact XV.abs_int_lt (lt_of_le_of_lt hv' (pow_lt_pow_right₀ (by norm_num) hl.1))
  | .ediv a b, hw, h, hl => by
    simp only [top, max_lt_iff] at hl
    refine ⟨OK_of_leaves hw.1 h.1 hl.2.1, OK_of_leaves hw.2 h.2 hl.2.2, ?_⟩
    obtain ⟨v, hv, hv'⟩ := int_of_leaves (e := .ediv a b) hw h
    rw [show ((⌊a.eval σ⌋ / ⌊b.eval σ⌋ : ℤ) : ℝ) = (IE.ediv a b).eval σ from rfl, hv]
    exact XV.abs_int_lt (lt_of_le_of_lt hv' (pow_lt_pow_right₀ (by norm_num) hl.1))

end IE

/-! ## The package -/

namespace XV

variable {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ}

/-- What the code of an expression of integer value `v` does, for its users: `v` in the slot `x`, `|v| < 2^ℓ`, the
count of draws kept, only `x` and the slots from `t` changed. -/
def ExprPost (ℓ : ℕ) (σ : Env d) (x t : ℕ) (v : ℤ) (σ' : Env d) : Prop :=
  σ'.sc x = v ∧ |v| < 2 ^ ℓ ∧ σ'.draws = σ.draws ∧ FrameP (fun y => y = x ∨ t ≤ y) (fun _ => False) σ σ'

/-- **The package**: an expression with static conditions `WF`, integer leaves below `2^E`, top exponent below `ℓ` and
value `v` runs within `e.units` units to `ExprPost`. -/
theorem ieRun (hL : LayOK L d ℓa) {z x t E : ℕ} {e : IE} {σ : Env d} {v : ℤ} (hw : e.WF L t) (hz : z < t)
    (hx : x < t) (hS : t + e.scr ≤ L.NS) (hz0 : σ.sc z = 0) (hl : e.Leaves E σ) (htop : e.top E < ℓ)
    (hv : e.eval σ = v) :
    XRunsB L X ℓa ℓ (e.code L z x t) σ e.units (ExprPost ℓ σ x t v) := by
  have hok := IE.OK_of_leaves hw hl htop
  have hb := hok.bound
  rw [hv] at hb
  exact mono (ie hL (by omega) e x t σ hw hz hx hS hz0 hok) le_rfl fun σ' h =>
    ⟨by rw [h.1, hv], by exact_mod_cast hb, h.2.1, h.2.2.mono (fun y hy => by omega) (fun _ h => h)⟩

end XV

/-! ## The model: the entry and one row of the matrix step of ELL-R -/

/-- `ellEntry c1 kN D D2 A vi vk` as an expression: `A = aA[nr]`, `vi = aV[ni]`, `vk = aV[nk]`, the slots
`o, ..., o + 3` holding `c1, κ_N, D, D2`. -/
def ieEll (o aA aV ni nr nk : ℕ) : IE :=
  let u : IE := .op .mul (.op .sub (.op .mul (.arr aA nr) (.sc o))
    (.op .add (.op .mul (.arr aV ni) (.arr aV nk)) (.op .mul (.arr aV ni) (.arr aV nk)))) (.sc (o + 1))
  .ediv (.op .add (.op .add u u) (.sc (o + 2))) (.sc (o + 3))

/-- The package of `ieEll`: 41 units, scratch `t, ..., t + 29`, inputs below `2^E`, every value below `2^(3E + 4)`. -/
theorem XV.ieEll_run {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {z x t o aA aV ni nr nk E : ℕ}
    {σ : Env d} {c1 kN D D2 A vi vk : ℤ} (hz : z < t) (hx : x < t) (ho : o + 3 < t) (hS : t + 30 ≤ L.NS)
    (hz0 : σ.sc z = 0) (hA : aA < L.NA) (hV : aV < L.NA) (hni : ni < L.NN) (hnr : nr < L.NN) (hnk : nk < L.NN)
    (hr : σ.nat nr < asz d) (hi : σ.nat ni < asz d) (hk : σ.nat nk < asz d) (ha : σ.arr aA (σ.nat nr) = A)
    (hvi : σ.arr aV (σ.nat ni) = vi) (hvk : σ.arr aV (σ.nat nk) = vk) (h0 : σ.sc o = c1) (h1 : σ.sc (o + 1) = kN)
    (h2 : σ.sc (o + 2) = D) (h3 : σ.sc (o + 3) = D2) (bA : |A| ≤ 2 ^ E) (bi : |vi| ≤ 2 ^ E) (bk : |vk| ≤ 2 ^ E)
    (b0 : |c1| ≤ 2 ^ E) (b1 : |kN| ≤ 2 ^ E) (b2 : |D| ≤ 2 ^ E) (b3 : |D2| ≤ 2 ^ E) (he : 3 * E + 4 < ℓ) :
    XRunsB L X ℓa ℓ ((ieEll o aA aV ni nr nk).code L z x t) σ 41
      (XV.ExprPost ℓ σ x t (ellEntry c1 kN D D2 A vi vk)) :=
  XV.ieRun (E := E) hL (by
      simp only [ieEll, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and, and_true, hA, hV, hni, hnr, hnk,
        and_self]
      omega) hz hx hS hz0
    (by simp only [ieEll, IE.Leaves, ha, hvi, hvk, h0, h1, h2, h3, Int.cast_inj, exists_eq_left', hr, hi, hk, bA, bi,
      bk, b0, b1, b2, b3, and_self])
    (by simp only [ieEll, IE.top, IE.mag]; omega)
    (by
      simp only [ieEll, IE.eval, RealRAM.Op2.eval, ha, hvi, hvk, h0, h1, h2, h3]
      rw [ellEntry]; norm_cast; rw [Int.floor_intCast, Int.floor_intCast])

/-- Row `i` with the entry computed by the code of `ieEll` into the slot `o + 4`, scratch from `o + 5`. -/
def xellRowH (L : Layout) (z o aA aV aB ni nr nk nd none : ℕ) : XCmd :=
  xforN nk nd none (.seq ((ieEll o aA aV ni nr nk).code L z (o + 4) (o + 5))
    (.seq (toX (VL.aset L aB nr (o + 4))) (.prim (.frag (.nadd nr nr none)))))

set_option maxHeartbeats 1000000 in
theorem XV.ellRowH {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {z o aA aV aB ni nr nk nd none : ℕ} (hz : z < o + 4) (hS : o + 35 ≤ L.NS) (hz0 : σ.sc z = 0)
    (hA : aA < L.NA) (hV : aV < L.NA) (hB : aB < L.NA)
    (hBA : aB ≠ aA) (hBV : aB ≠ aV) (hni : ni < L.NN) (hnr : nr < L.NN) (hnk : nk < L.NN) (hnd : nd < L.NN)
    (hno : none < L.NN) (hne : [ni, nr, nk, nd, none].Nodup) {i : ℕ} (hi : i < d) (hσi : σ.nat ni = i)
    (hσr : σ.nat nr = d * i) (hσd : σ.nat nd = d) (hσ1 : σ.nat none = 1)
    {c1 kN D D2 : ℤ} (h0 : σ.sc o = c1) (h1 : σ.sc (o + 1) = kN) (h2 : σ.sc (o + 2) = D)
    (h3 : σ.sc (o + 3) = D2) {Ai Vv : ℕ → ℤ} (hAi : ∀ k < d, σ.arr aA (d * i + k) = Ai k)
    (hVv : ∀ k < d, σ.arr aV k = Vv k) {e : ℕ} (he : 3 * e + 4 < ℓ) (bc1 : |c1| ≤ 2 ^ e) (bkN : |kN| ≤ 2 ^ e)
    (bD : |D| ≤ 2 ^ e) (bD2 : |D2| ≤ 2 ^ e) (bA : ∀ k < d, |Ai k| ≤ 2 ^ e) (bV : ∀ k < d, |Vv k| ≤ 2 ^ e)
    (hda : d * d + d < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xellRowH L z o aA aV aB ni nr nk nd none) σ (d * (41 + (2 + 1) + 3) + 3) (fun σ' =>
      (∀ k < d, σ'.arr aB (d * i + k) = (ellEntry c1 kN D D2 (Ai k) (Vv i) (Vv k) : ℝ)) ∧
      σ'.nat nr = d * i + d ∧
      FrameA (fun y => o + 4 ≤ y) (fun j => j = nk ∨ j = nr) (fun b k => b = aB ∧ d * i ≤ k ∧ k < d * i + d) σ σ') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne
  obtain ⟨⟨ir, ik, id, io⟩, ⟨rk, rd, ro⟩, ⟨kd, ko⟩, dO⟩ := hne
  have hdi : d * i + d ≤ d * d := by nlinarith
  set Fr : ℕ → ℕ → Prop := fun b k => b = aB ∧ d * i ≤ k ∧ k < d * i + d with hFr
  refine XV.forN hL hnk hnd hno kd ko d (41 + (2 + 1)) (by omega)
    (fun t σ' => σ'.nat nr = d * i + t ∧
      (∀ k < t, σ'.arr aB (d * i + k) = (ellEntry c1 kN D D2 (Ai k) (Vv i) (Vv k) : ℝ)) ∧
      FrameA (fun y => o + 4 ≤ y) (fun j => j = nk ∨ j = nr) Fr σ σ')
    σ hσd hσ1 ⟨by simp [rk, hσr], fun k hk => absurd hk (Nat.not_lt_zero k),
      (FrameA.refl _ _ _ σ).setNat (Or.inl rfl) 0⟩ ?_ |> fun h => XV.mono h le_rfl
      fun σ' ⟨⟨hr, hk, hF⟩, _⟩ => ⟨hk, hr, hF⟩
  intro t ht σ' ⟨hr, hk, hF⟩ hkt hkd hk1
  -- what the frame keeps
  have ei : σ'.nat ni = i := by rw [hF.1 ni (by omega), hσi]
  have eA : σ'.arr aA (σ'.nat nr) = Ai t := by
    rw [hr, hF.2.2.1 aA (d * i + t) (fun h => hBA h.1.symm), hAi t ht]
  have eVi : σ'.arr aV (σ'.nat ni) = Vv i := by rw [ei, hF.2.2.1 aV i (fun h => hBV h.1.symm), hVv i hi]
  have eVt : σ'.arr aV (σ'.nat nk) = Vv t := by rw [hkt, hF.2.2.1 aV t (fun h => hBV h.1.symm), hVv t ht]
  -- the entry, by its package
  refine XV.seq (XV.ieEll_run hL (x := o + 4) (t := o + 5) (by omega) (by omega) (by omega) (by omega)
    (by rw [hF.2.1 z (by omega), hz0]) hA hV hni hnr hnk (by rw [hr]; unfold asz; nlinarith)
    (by rw [ei]; unfold asz; nlinarith) (by rw [hkt]; unfold asz; nlinarith) eA eVi eVt
    (by rw [hF.2.1 o (by omega), h0]) (by rw [hF.2.1 (o + 1) (by omega), h1]) (by rw [hF.2.1 (o + 2) (by omega), h2])
    (by rw [hF.2.1 (o + 3) (by omega), h3]) (bA t ht) (bV i hi) (bV t ht) bc1 bkN bD bD2 he)
    fun σ1 ⟨v1, b1, _, P1⟩ => ?_
  have n1 : σ1.nat = σ'.nat := funext fun j => P1.1 j not_false
  refine XV.seq (XV.aset hL (a := aB) (i := nr) (x := o + 4) hB hnr (by omega)
    (by rw [n1, hr]; unfold asz; nlinarith) (by rw [v1]; exact XV.abs_int_lt b1)) fun σ2 e2' => ?_
  subst e2'
  refine XV.mono (XV.nadd hL (i := nr) (a := nr) (b := none) hnr hnr hno (by simp [n1, hr]; nlinarith)
    (by simp only [Env.setArr_nat, n1, hk1]; have := hL.1; omega)) le_rfl fun σ3 e3' => ?_
  subst e3'
  refine ⟨by simp [Ne.symm rk, hkt, n1], by simp [Ne.symm rd, hkd, n1], by simp [Ne.symm ro, hk1, n1], ?_, ?_, ?_⟩
  · simp [rk, hr, hk1, n1]; ring
  · intro k hk'
    simp only [Env.setNat_arr, Env.setArr_arr, Env.setArr_nat, n1, hr, P1.2.2.1, true_and]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with hlt | rfl
    · rw [ite_eq_right (by omega)]; exact hk k hlt
    · rw [ite_eq_left rfl, v1]
  · refine (((hF.trans ⟨fun j _ => P1.1 j not_false, fun y hy => P1.2.1 y (by omega), fun b k _ => by
      rw [P1.2.2.1], P1.2.2.2.1, P1.2.2.2.2⟩).setArr ⟨rfl, by simp only [n1, hr]; omega, by
      simp only [n1, hr]; omega⟩ _).setNat (Or.inr rfl) _).setNat (Or.inl rfl) _

end AdversarialBco.Bit.Transfer
