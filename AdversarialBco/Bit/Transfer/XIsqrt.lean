/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XRuns

@[expose] public section

/-!
# Integer square root, powers of two

* `Frame S N σ σ'`: `σ'` differs from `σ` at most at the scalars of `S` and the naturals of `N`.
* `XV.sconst`, `XV.sop2`: the scalar primitives of the fragment as rules of the extended language.
* `xisqrt`: `⌊n^{1/2}⌋` of a nonnegative integer scalar by the digit-by-digit method of Procedure BM-INT (the
  powers of four, then per pass an addition, a comparison, a conditional subtraction and addition, two Euclidean
  quotients); `XV.isqrt`: its rule, within `12 size(n) + 8` units, every value at most `4 n + 4`.
* `xpow2`: `2^W` by doubling, `W` a natural variable (`XV.pow2`).
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach

variable {d : ℕ}

/-- `σ'` differs from `σ` at most at the scalars of `S` and the naturals of `N`. -/
def Frame (S N : List ℕ) (σ σ' : Env d) : Prop :=
  (∀ j, j ∉ N → σ'.nat j = σ.nat j) ∧ (∀ y, y ∉ S → σ'.sc y = σ.sc y) ∧ σ'.arr = σ.arr ∧
    σ'.draws = σ.draws ∧ σ'.rounds = σ.rounds ∧ σ'.pts = σ.pts

theorem Frame.refl (S N : List ℕ) (σ : Env d) : Frame S N σ σ :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Frame.setSc {S N : List ℕ} {σ σ' : Env d} (h : Frame S N σ σ') {x : ℕ} (hx : x ∈ S) (v : ℝ) :
    Frame S N σ (σ'.setSc x v) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, fun y hy => ?_, h3, h4, h5, h6⟩
  have hne : y ≠ x := fun e => hy (e ▸ hx)
  simp [hne, h2 y hy]

theorem Frame.setNat {S N : List ℕ} {σ σ' : Env d} (h : Frame S N σ σ') {i : ℕ} (hi : i ∈ N) (v : ℕ) :
    Frame S N σ (σ'.setNat i v) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun j hj => ?_, h2, h3, h4, h5, h6⟩
  have hne : j ≠ i := fun e => hj (e ▸ hi)
  simp [hne, h1 j hj]

/-- One pass of `xisqrt`: `t := dd + q`; if `t ≤ r`: `r := r - t`, `dd := t + q`; then `dd := dd div 2`,
`q := q div 4`. -/
def xisqrtPass (L : Layout) (r dd q t two four : ℕ) : XCmd :=
  .seq (toX (VL.sop2 L .add t dd q))
  (.seq (xifS L r t .skip (.seq (toX (VL.sop2 L .sub r r t)) (toX (VL.sop2 L .add dd t q))))
  (.seq (xsidiv L dd dd two) (xsidiv L q q four)))

/-- `⌊sqrt n⌋`, digit by digit. The input `n` in the scalar `r`, the output in `dd`, `r` ends at
`n - dd ^ 2`; `q`, `t`, `n1` are scratch; `z`, `one`, `two`, `four` hold `0, 1, 2, 4`. `n1 := n + 1`, `q := 1`;
while `q < n1`: `q := 4 q`; `q := q div 4`; `dd := 0`; while `0 < q`: the pass `xisqrtPass`. -/
def xisqrt (L : Layout) (r dd q t n1 z one two four : ℕ) : XCmd :=
  .seq (toX (VL.sop2 L .add n1 r one))
  (.seq (toX (VL.sconst L q 1))
  (.seq (xwhileS L q n1 (toX (VL.sop2 L .mul q q four)))
  (.seq (xsidiv L q q four)
  (.seq (toX (VL.sconst L dd 0))
  (xwhileS L z q (xisqrtPass L r dd q t two four))))))

/-- `p := 2 ^ (nat n)` by doubling (`i` the counter, `one` holds `1`). -/
def xpow2 (L : Layout) (p i n one : ℕ) : XCmd :=
  .seq (toX (VL.sconst L p 1)) (xforN i n one (toX (VL.sop2 L .add p p p)))

/-! ## Arithmetic of a pass of `xisqrt` -/

theorem isqrt_floor_div (a b : ℕ) : ((⌊(a : ℝ)⌋ / ⌊(b : ℝ)⌋ : ℤ) : ℝ) = ((a / b : ℕ) : ℝ) := by
  rw [Int.floor_natCast, Int.floor_natCast, ← Int.natCast_div, Int.cast_natCast]

theorem isqrt_mul_le {h lo n : ℕ} (hh : h ^ 2 ≤ n) (hlo : lo ^ 2 ≤ n) : h * lo ≤ n := by
  rcases le_total h lo with e | e
  · calc h * lo ≤ lo * lo := Nat.mul_le_mul_right _ e
      _ = lo ^ 2 := (sq lo).symm
      _ ≤ n := hlo
  · calc h * lo ≤ h * h := Nat.mul_le_mul_left _ e
      _ = h ^ 2 := (sq h).symm
      _ ≤ n := hh

theorem isqrt_test {h lo n : ℕ} (hlo : lo ^ 2 ≤ n) :
    (2 * (h * lo) + h ^ 2 ≤ n - lo ^ 2) ↔ (lo + h) ^ 2 ≤ n := by
  constructor <;> intro e
  · have := Nat.add_le_of_le_sub hlo e
    nlinarith
  · apply Nat.le_sub_of_add_le
    nlinarith

theorem isqrt_sub (h lo n : ℕ) :
    n - lo ^ 2 - (2 * (h * lo) + h ^ 2) = n - (lo + h) ^ 2 := by
  rw [Nat.sub_sub]; congr 1; ring

theorem four_pow_div (e : ℕ) : 4 ^ (e + 1) / 4 = 4 ^ e := by
  rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]

theorem two_pow_sq (e : ℕ) : 4 ^ e = (2 ^ e) ^ 2 := by
  rw [← pow_mul, mul_comm, pow_mul]; norm_num

namespace XV

variable {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d}

theorem sconst (hL : LayOK L d ℓa) {x : ℕ} (hx : x < L.NS) (q : ℚ) (hq : q.den = 1) (hv : |(q : ℝ)| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (toX (VL.sconst L x q)) σ 1 (· = σ.setSc x q) :=
  (VB.runsB_sconst (w := X.rw) hL hx q hq hv).toX X

theorem sop2 (hL : LayOK L d ℓa) {x a b : ℕ} (hx : x < L.NS) (ha : a < L.NS) (hb : b < L.NS)
    (o : RealRAM.Op2) (ho : o ≠ .div) (hva : |σ.sc a| < 2 ^ ℓ) (hvb : |σ.sc b| < 2 ^ ℓ)
    (hvr : |o.eval (σ.sc a) (σ.sc b)| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (toX (VL.sop2 L o x a b)) σ 1 (· = σ.setSc x (o.eval (σ.sc a) (σ.sc b))) :=
  (VB.runsB_sop2 (w := X.rw) hL hx ha hb o ho hva hvb hvr).toX X

/-- A natural below `2 ^ ℓ`, read as a scalar, passes the bound of the bounded semantics. -/
theorem abs_nat_lt {v : ℕ} (h : v < 2 ^ ℓ) : |(v : ℝ)| < 2 ^ ℓ := by
  rw [abs_of_nonneg (Nat.cast_nonneg v)]; exact_mod_cast h

end XV

theorem eval_add (a b : ℕ) : RealRAM.Op2.eval .add (a : ℝ) (b : ℝ) = ((a + b : ℕ) : ℝ) := by
  simp [RealRAM.Op2.eval]

theorem eval_mul (a b : ℕ) : RealRAM.Op2.eval .mul (a : ℝ) (b : ℝ) = ((a * b : ℕ) : ℝ) := by
  simp [RealRAM.Op2.eval]

theorem eval_sub {a b : ℕ} (h : b ≤ a) : RealRAM.Op2.eval .sub (a : ℝ) (b : ℝ) = ((a - b : ℕ) : ℝ) := by
  simp [RealRAM.Op2.eval, Nat.cast_sub h]

theorem Frame.trans {S N : List ℕ} {σ σ' σ'' : Env d} (h : Frame S N σ σ') (h' : Frame S N σ' σ'') :
    Frame S N σ σ'' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := h'
  exact ⟨fun j hj => (g1 j hj).trans (h1 j hj), fun y hy => (g2 y hy).trans (h2 y hy), g3.trans h3, g4.trans h4,
    g5.trans h5, g6.trans h6⟩

/-- One pass of `xisqrt`, at `q = h ^ 2`, `dd = 2 h lo`, `r = n - lo ^ 2`: it ends at `q = h ^ 2 div 4`,
`dd = h lo'`, `r = n - lo' ^ 2`, with `lo' = lo + h` if `(lo + h) ^ 2 ≤ n` and `lo' = lo` (and `n < (lo + h) ^ 2`)
otherwise. -/
theorem XV.isqrtPass {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {r dd q t two four : ℕ}
    (hr : r < L.NS) (hdd : dd < L.NS) (hq : q < L.NS) (ht : t < L.NS) (htw : two < L.NS) (hf : four < L.NS)
    (hne : [r, dd, q, t, two, four].Nodup) {n h lo : ℕ}
    (hσq : σ.sc q = ((h ^ 2 : ℕ) : ℝ)) (hσd : σ.sc dd = ((2 * (h * lo) : ℕ) : ℝ))
    (hσr : σ.sc r = ((n - lo ^ 2 : ℕ) : ℝ)) (hσ2 : σ.sc two = 2) (hσ4 : σ.sc four = 4)
    (hlo : lo ^ 2 ≤ n) (hh : h ^ 2 ≤ n) (hℓ : 4 * n + 4 < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xisqrtPass L r dd q t two four) σ 7 (fun σ' => ∃ lo',
      σ'.sc q = ((h ^ 2 / 4 : ℕ) : ℝ) ∧ σ'.sc dd = ((h * lo' : ℕ) : ℝ) ∧ σ'.sc r = ((n - lo' ^ 2 : ℕ) : ℝ) ∧
      lo' ^ 2 ≤ n ∧ ((lo' = lo ∧ n < (lo + h) ^ 2) ∨ lo' = lo + h) ∧ Frame [r, dd, q, t] [] σ σ') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil, and_true] at hne
  obtain ⟨⟨rd, rq, rt, r2, r4⟩, ⟨dq, dt, d2, d4⟩, ⟨qt, q2, q4⟩, ⟨t2, t4⟩, f24⟩ := hne
  have hm : h * lo ≤ n := isqrt_mul_le hh hlo
  have hb : ∀ v : ℕ, v ≤ 4 * n + 4 → |(v : ℝ)| < 2 ^ ℓ := fun v hv => XV.abs_nat_lt (by omega)
  have h2b : |(2 : ℝ)| < 2 ^ ℓ := by
    have := hb 2 (by omega); simpa using this
  have h4b : |(4 : ℝ)| < 2 ^ ℓ := by
    have : (4 : ℕ) < 2 ^ ℓ := by omega
    rw [abs_of_nonneg (by norm_num)]; exact_mod_cast this
  have hσ1 : RealRAM.Op2.eval .add (σ.sc dd) (σ.sc q) = ((2 * (h * lo) + h ^ 2 : ℕ) : ℝ) := by
    rw [hσd, hσq, eval_add]
  refine XV.mono (K := 1 + (4 + (1 + 1))) (XV.seq (XV.sop2 hL ht hdd hq .add (by intro e; cases e)
    (by rw [hσd]; exact hb _ (by omega)) (by rw [hσq]; exact hb _ (by omega))
    (by rw [hσ1]; exact hb _ (by omega))) fun σ1 e1 => ?_) (by norm_num) (fun _ h => h)
  rw [hσ1] at e1
  subst e1
  -- the conditional, to `dd = 2 h lo'`, `r = n - lo' ^ 2`
  have hif : XRunsB L X ℓa ℓ (xifS L r t .skip (.seq (toX (VL.sop2 L .sub r r t)) (toX (VL.sop2 L .add dd t q))))
      (σ.setSc t ((2 * (h * lo) + h ^ 2 : ℕ) : ℝ)) 4 (fun σb => ∃ lo',
        σb.sc dd = ((2 * (h * lo') : ℕ) : ℝ) ∧ σb.sc r = ((n - lo' ^ 2 : ℕ) : ℝ) ∧ σb.sc q = ((h ^ 2 : ℕ) : ℝ) ∧
        lo' ^ 2 ≤ n ∧ ((lo' = lo ∧ n < (lo + h) ^ 2) ∨ lo' = lo + h) ∧ Frame [r, dd, q, t] [] σ σb) := by
    have hF1 : Frame [r, dd, q, t] [] σ (σ.setSc t ((2 * (h * lo) + h ^ 2 : ℕ) : ℝ)) :=
      (Frame.refl _ _ σ).setSc (by simp) _
    have br : |(σ.setSc t ((2 * (h * lo) + h ^ 2 : ℕ) : ℝ)).sc r| < 2 ^ ℓ := by
      simp only [Env.setSc_sc, rt, ↓reduceIte, hσr]; exact hb _ (by omega)
    have bt : |(σ.setSc t ((2 * (h * lo) + h ^ 2 : ℕ) : ℝ)).sc t| < 2 ^ ℓ := by
      simp only [Env.setSc_sc, ↓reduceIte]; exact hb _ (by omega)
    by_cases hc : n - lo ^ 2 < 2 * (h * lo) + h ^ 2
    · refine XV.mono (XV.ifS_t hL hr ht br bt ?_ (XV.skip _)) (by norm_num) (fun σb e => ?_)
      · simp only [Env.setSc_sc, rt, ↓reduceIte, hσr]; exact_mod_cast hc
      · subst e
        refine ⟨lo, by simp [dt, hσd], by simp [rt, hσr], by simp [qt, hσq], hlo, Or.inl ⟨rfl, ?_⟩, hF1⟩
        by_contra hn
        exact absurd ((isqrt_test hlo).2 (not_lt.1 hn)) (not_le.2 hc)
    · have hc' : (lo + h) ^ 2 ≤ n := (isqrt_test hlo).1 (not_lt.1 hc)
      have hm' : h * (lo + h) ≤ n := isqrt_mul_le hh hc'
      have hsub : RealRAM.Op2.eval .sub (((n - lo ^ 2 : ℕ) : ℝ)) (((2 * (h * lo) + h ^ 2 : ℕ) : ℝ)) =
          ((n - (lo + h) ^ 2 : ℕ) : ℝ) := by
        rw [eval_sub (not_lt.1 hc), isqrt_sub]
      refine XV.ifS_f hL hr ht br bt ?_ (XV.seq (K₂ := 1) (XV.sop2 hL hr hr ht .sub (by intro e; cases e) br bt ?_)
        fun σ2 e2 => XV.mono (XV.sop2 hL hdd ht hq .add (by intro e; cases e) ?_ ?_ ?_) le_rfl (fun σb e => ?_))
      · simp only [Env.setSc_sc, rt, ↓reduceIte, hσr]; exact_mod_cast hc
      · simp only [Env.setSc_sc, rt, ↓reduceIte, hσr]; rw [hsub]; exact hb _ (by omega)
      · subst e2; simp only [Env.setSc_sc, (Ne.symm rt), ↓reduceIte]; exact hb _ (by omega)
      · subst e2; simp only [Env.setSc_sc, qt, (Ne.symm rq), ↓reduceIte, hσq]; exact hb _ (by omega)
      · subst e2
        simp only [Env.setSc_sc, qt, (Ne.symm rq), ↓reduceIte, hσq, (Ne.symm rt), ↓reduceIte]
        rw [eval_add]; exact hb _ (by nlinarith)
      · subst e2 e
        refine ⟨lo + h, ?_, ?_, ?_, hc', Or.inr rfl, (hF1.setSc (by simp) _).setSc (by simp) _⟩
        · simp only [Env.setSc_sc, ↓reduceIte, Ne.symm rt, qt, Ne.symm rq, hσq]
          rw [eval_add]; congr 1; ring
        · simp only [Env.setSc_sc, ↓reduceIte, rd, rt, hσr]; exact hsub
        · simp only [Env.setSc_sc, ↓reduceIte, Ne.symm dq, Ne.symm rq, qt, hσq]
  have hnS : ∀ y, y ≠ r → y ≠ dd → y ≠ q → y ≠ t → y ∉ [r, dd, q, t] := by
    intro y h1 h2 h3 h4; simp [h1, h2, h3, h4]
  refine XV.seq hif fun σb ⟨lo', hbd, hbr, hbq, hlo', hcase, hFb⟩ => ?_
  have hb2 : σb.sc two = ((2 : ℕ) : ℝ) := by
    rw [hFb.2.1 two (hnS _ (Ne.symm r2) (Ne.symm d2) (Ne.symm q2) (Ne.symm t2)), hσ2]; norm_num
  have hb4 : σb.sc four = ((4 : ℕ) : ℝ) := by
    rw [hFb.2.1 four (hnS _ (Ne.symm r4) (Ne.symm d4) (Ne.symm q4) (Ne.symm t4)), hσ4]; norm_num
  have hm2 : h * lo' ≤ n := isqrt_mul_le hh hlo'
  refine XV.seq (XV.sidiv hL hdd hdd htw (by rw [hbd]; exact hb _ (by omega)) (by rw [hb2]; exact hb _ (by omega)))
    fun σc ec => ?_
  subst ec
  refine XV.mono (XV.sidiv hL hq hq hf ?_ ?_) le_rfl (fun σ' e => ?_)
  · simp only [Env.setSc_sc, ↓reduceIte, Ne.symm dq, hbq]; exact hb _ (by omega)
  · simp only [Env.setSc_sc, ↓reduceIte, Ne.symm d4, hb4]; exact hb _ (by omega)
  subst e
  refine ⟨lo', ?_, ?_, ?_, hlo', hcase, (hFb.setSc (by simp) _).setSc (by simp) _⟩
  · simp only [Env.setSc_sc, ↓reduceIte, Ne.symm dq, hbq, Ne.symm d4, hb4]
    exact isqrt_floor_div _ _
  · simp only [Env.setSc_sc, ↓reduceIte, dq, hbd, hb2]
    rw [isqrt_floor_div, Nat.mul_div_cancel_left _ (by norm_num)]
  · simp only [Env.setSc_sc, ↓reduceIte, rq, rd, hbr]



theorem Frame.sub {S S' N : List ℕ} {σ σ' : Env d} (hS : ∀ y ∈ S, y ∈ S') (h : Frame S N σ σ') :
    Frame S' N σ σ' :=
  ⟨h.1, fun y hy => h.2.1 y (fun e => hy (hS y e)), h.2.2⟩

theorem isqrt_pow_le {n k : ℕ} (h : k = 0 ∨ 4 ^ (k - 1) ≤ n) : 4 ^ k ≤ 4 * n + 4 := by
  rcases h with rfl | h
  · simp
  · cases k with
    | zero => simp
    | succ j => rw [pow_succ]; simp only [Nat.add_sub_cancel] at h; omega

/-- The rule of `xisqrt`: from `r = n`, the constants `0, 1, 2, 4` in `z, one, two, four` and `4 n + 4 < 2 ^ ℓ`,
it ends with `dd = ⌊sqrt n⌋` and `r = n - ⌊sqrt n⌋ ^ 2`, having changed only the scalars `r, dd, q, t, n1`, within
`12 size(n) + 8` units. -/
theorem XV.isqrt {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {r dd q t n1 z one two four : ℕ} (hr : r < L.NS) (hdd : dd < L.NS) (hq : q < L.NS) (ht : t < L.NS)
    (hn1 : n1 < L.NS) (hz : z < L.NS) (ho : one < L.NS) (htw : two < L.NS) (hf : four < L.NS)
    (hne : [r, dd, q, t, n1, z, one, two, four].Nodup) {n : ℕ} (hσr : σ.sc r = n) (hσz : σ.sc z = 0)
    (hσ1 : σ.sc one = 1) (hσ2 : σ.sc two = 2) (hσ4 : σ.sc four = 4) (hℓ : 4 * n + 4 < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xisqrt L r dd q t n1 z one two four) σ (12 * n.size + 8)
      (fun σ' => σ'.sc dd = (Nat.sqrt n : ℝ) ∧ σ'.sc r = ((n - Nat.sqrt n ^ 2 : ℕ) : ℝ) ∧
        Frame [r, dd, q, t, n1] [] σ σ') := by
  have hne' := hne
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil, and_true] at hne'
  obtain ⟨⟨rd, rq, rt, rn, rz, ro, r2, r4⟩, ⟨dq, dt, dn, dz, do', d2, d4⟩, ⟨qt, qn, qz, qo, q2, q4⟩,
    ⟨tn, tz, tO, t2, t4⟩, ⟨nz, no, n2, n4⟩, -, -, f24⟩ := hne'
  have hb : ∀ v : ℕ, v ≤ 4 * n + 4 → |(v : ℝ)| < 2 ^ ℓ := fun v hv => XV.abs_nat_lt (by omega)
  have hnS : ∀ y, y ≠ r → y ≠ dd → y ≠ q → y ≠ t → y ≠ n1 → y ∉ [r, dd, q, t, n1] := by
    intro y h1 h2 h3 h4 h5; simp [h1, h2, h3, h4, h5]
  have hcst : ∀ σ', Frame [r, dd, q, t, n1] [] σ σ' →
      σ'.sc z = 0 ∧ σ'.sc one = 1 ∧ σ'.sc two = 2 ∧ σ'.sc four = 4 := fun σ' hF =>
    ⟨by rw [hF.2.1 z (hnS _ (Ne.symm rz) (Ne.symm dz) (Ne.symm qz) (Ne.symm tz) (Ne.symm nz)), hσz],
     by rw [hF.2.1 one (hnS _ (Ne.symm ro) (Ne.symm do') (Ne.symm qo) (Ne.symm tO) (Ne.symm no)), hσ1],
     by rw [hF.2.1 two (hnS _ (Ne.symm r2) (Ne.symm d2) (Ne.symm q2) (Ne.symm t2) (Ne.symm n2)), hσ2],
     by rw [hF.2.1 four (hnS _ (Ne.symm r4) (Ne.symm d4) (Ne.symm q4) (Ne.symm t4) (Ne.symm n4)), hσ4]⟩
  have h1b : |(1 : ℝ)| < 2 ^ ℓ := by simpa using hb 1 (by omega)
  have h4b : |(4 : ℝ)| < 2 ^ ℓ := by
    have := hb 4 (by omega); rwa [Nat.cast_ofNat] at this
  have c4 : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
  refine XV.mono (K := 1 + (1 + ((n.size - 0) * (1 + 2) + 2 + (1 + (1 + ((n.size - 0) * (7 + 2) + 2))))))
    ?_ (by omega) (fun _ h => h)
  -- `n1 := n + 1`, `q := 1`
  have e1v : RealRAM.Op2.eval .add (σ.sc r) (σ.sc one) = ((n + 1 : ℕ) : ℝ) := by
    rw [hσr, hσ1]; simp [RealRAM.Op2.eval]
  refine XV.seq (XV.sop2 hL hn1 hr ho .add (by intro e; cases e) (by rw [hσr]; exact hb _ (by omega))
    (by rw [hσ1]; exact h1b) (by rw [e1v]; exact hb _ (by omega))) fun σ1 e1 => ?_
  rw [e1v] at e1
  subst e1
  refine XV.seq (XV.sconst hL hq 1 rfl (by simpa using h1b)) fun σ2 e2 => ?_
  subst e2
  -- the powers of four
  have hloop1 := XV.whileS (X := X) (ℓ := ℓ) (c := toX (VL.sop2 L .mul q q four)) hL hq hn1
    (fun k σ' => Frame [r, dd, q, t, n1] [] σ σ' ∧ σ'.sc r = n ∧ σ'.sc n1 = ((n + 1 : ℕ) : ℝ) ∧
      σ'.sc q = ((4 ^ k : ℕ) : ℝ) ∧ (k = 0 ∨ 4 ^ (k - 1) ≤ n)) n.size 1
    (fun k σ' ⟨_, _, h3, h4, h5⟩ => ⟨by rw [h4]; exact hb _ (isqrt_pow_le h5), by rw [h3]; exact hb _ (by omega)⟩)
    (fun k σ' ⟨_, _, h3, h4, _⟩ hc => by
      rw [h3, h4, Nat.cast_lt] at hc
      exact Nat.lt_size.2 ((Nat.pow_le_pow_left (by norm_num : 2 ≤ 4) k).trans (by omega)))
    (fun k σ' ⟨hF, h2, h3, h4, h5⟩ hc => by
      rw [h3, h4, Nat.cast_lt] at hc
      have h4' : σ'.sc four = ((4 : ℕ) : ℝ) := by rw [(hcst σ' hF).2.2.2, c4]
      refine XV.mono (XV.sop2 hL hq hq hf .mul (by intro e; cases e) (by rw [h4]; exact hb _ (isqrt_pow_le h5))
        (by rw [h4']; exact hb _ (by omega)) ?_) le_rfl (fun σ'' e => ?_)
      · rw [h4, h4', eval_mul, ← pow_succ]; exact hb _ (by rw [pow_succ]; omega)
      · subst e
        refine ⟨hF.setSc (by simp) _, by simp [rq, h2], by simp [Ne.symm qn, h3], ?_, Or.inr (by simpa using
          (show 4 ^ k ≤ n by omega))⟩
        simp only [Env.setSc_sc, ↓reduceIte, h4, h4', eval_mul, ← pow_succ])
  refine XV.seq (hloop1 0 _ ⟨((Frame.refl _ _ σ).setSc (by simp) _).setSc (by simp) _,
    by simp [rq, rn, hσr], by simp [Ne.symm qn], by simp, Or.inl rfl⟩) fun σ3 h3 => ?_
  obtain ⟨K, ⟨hF3, h3r, h3n1, h3q, hK⟩, hex⟩ := h3
  rw [h3n1, h3q, Nat.cast_lt, not_lt] at hex
  have hKs : K ≤ n.size := by
    rcases hK with rfl | hK
    · exact Nat.zero_le _
    · have := Nat.lt_size.2 ((Nat.pow_le_pow_left (by norm_num : 2 ≤ 4) (K - 1)).trans hK)
      omega
  -- `q := q div 4`, `dd := 0`
  have h3f : σ3.sc four = ((4 : ℕ) : ℝ) := by rw [(hcst σ3 hF3).2.2.2, c4]
  refine XV.seq (XV.sidiv hL hq hq hf (by rw [h3q]; exact hb _ (isqrt_pow_le hK)) (by rw [h3f]; exact hb _ (by omega)))
    fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.sconst hL hdd 0 rfl (by simp)) fun σ5 e5 => ?_
  subst e5
  -- the passes
  have hsubS : ∀ y ∈ [r, dd, q, t], y ∈ [r, dd, q, t, n1] := fun y hy => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy ⊢; tauto
  have hne6 : [r, dd, q, t, two, four].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil, and_true]
    exact ⟨⟨rd, rq, rt, r2, r4⟩, ⟨dq, dt, d2, d4⟩, ⟨qt, q2, q4⟩, ⟨t2, t4⟩, f24⟩
  have hloop2 := XV.whileS (X := X) (ℓ := ℓ) (c := xisqrtPass L r dd q t two four) hL hz hq
    (fun i σ' => ∃ e lo : ℕ, e + i = K ∧ Frame [r, dd, q, t, n1] [] σ σ' ∧ σ'.sc q = ((4 ^ e / 4 : ℕ) : ℝ) ∧
      σ'.sc dd = ((2 ^ e * lo : ℕ) : ℝ) ∧ σ'.sc r = ((n - lo ^ 2 : ℕ) : ℝ) ∧ lo ^ 2 ≤ n ∧ n < (lo + 2 ^ e) ^ 2 ∧
      4 ^ e / 4 ≤ n) n.size 7
    (fun i σ' ⟨e, lo, _, hF, hq', _, _, _, _, hE⟩ =>
      ⟨by rw [(hcst σ' hF).1]; simp, by rw [hq']; exact hb _ (by omega)⟩)
    (fun i σ' ⟨e, lo, hei, hF, hq', _, _, _, _, _⟩ hc => by
      rw [(hcst σ' hF).1, hq', Nat.cast_pos] at hc
      have : e ≠ 0 := by rintro rfl; simp at hc
      omega)
    (fun i σ' ⟨e, lo, hei, hF, hq', hd', hr', hlo, hn, hE⟩ hc => by
      rw [(hcst σ' hF).1, hq', Nat.cast_pos] at hc
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by
        rcases Nat.eq_zero_or_pos e with h0 | h0
        · subst h0; simp at hc
        · omega⟩
      have hq2 : 4 ^ (e' + 1) / 4 = (2 ^ e') ^ 2 := by rw [four_pow_div, two_pow_sq]
      have hd2 : 2 ^ (e' + 1) * lo = 2 * (2 ^ e' * lo) := by rw [pow_succ]; ring
      rw [hq2] at hq' hE
      rw [hd2] at hd'
      obtain ⟨-, -, h2', h4'⟩ := hcst σ' hF
      refine XV.mono (XV.isqrtPass hL hr hdd hq ht htw hf hne6 hq' hd' hr' h2' h4' hlo hE hℓ) le_rfl
        (fun σ'' ⟨lo', g1, g2, g3, g4, g5, g6⟩ => ?_)
      refine ⟨e', lo', by omega, hF.trans (g6.sub hsubS), ?_, g2, g3, g4, ?_, ?_⟩
      · rw [g1, ← two_pow_sq]
      · rcases g5 with ⟨rfl, h⟩ | rfl
        · exact h
        · have e2 : lo + 2 ^ e' + 2 ^ e' = lo + 2 ^ (e' + 1) := by rw [pow_succ]; ring
          rw [e2]; exact hn
      · rw [← two_pow_sq] at hE; exact (Nat.div_le_self _ _).trans hE)
  have hI0 : ∃ e lo : ℕ, e + 0 = K ∧ Frame [r, dd, q, t, n1] [] σ
      (((σ3.setSc q ((⌊σ3.sc q⌋ / ⌊σ3.sc four⌋ : ℤ) : ℝ)).setSc dd ((0 : ℚ) : ℝ))) ∧
      ((σ3.setSc q ((⌊σ3.sc q⌋ / ⌊σ3.sc four⌋ : ℤ) : ℝ)).setSc dd ((0 : ℚ) : ℝ)).sc q = ((4 ^ e / 4 : ℕ) : ℝ) ∧
      ((σ3.setSc q ((⌊σ3.sc q⌋ / ⌊σ3.sc four⌋ : ℤ) : ℝ)).setSc dd ((0 : ℚ) : ℝ)).sc dd = ((2 ^ e * lo : ℕ) : ℝ) ∧
      ((σ3.setSc q ((⌊σ3.sc q⌋ / ⌊σ3.sc four⌋ : ℤ) : ℝ)).setSc dd ((0 : ℚ) : ℝ)).sc r = ((n - lo ^ 2 : ℕ) : ℝ) ∧
      lo ^ 2 ≤ n ∧ n < (lo + 2 ^ e) ^ 2 ∧ 4 ^ e / 4 ≤ n := by
    refine ⟨K, 0, rfl, (hF3.setSc (by simp) _).setSc (by simp) _, ?_, by simp, ?_, by simp, ?_, ?_⟩
    · simp only [Env.setSc_sc, ↓reduceIte, Ne.symm dq, h3q, h3f]; exact isqrt_floor_div _ _
    · simp only [Env.setSc_sc, ↓reduceIte, rd, rq, h3r]; simp
    · rw [zero_add, ← two_pow_sq]; omega
    · rcases hK with rfl | hK
      · simp
      · cases K with
        | zero => simp
        | succ j => rw [four_pow_div]; simpa using hK
  refine XV.mono (hloop2 0 _ hI0) le_rfl (fun σ6 ⟨i', ⟨e, lo, _, hF, hq', hd', hr', hlo, hn, _⟩, hex2⟩ => ?_)
  rw [(hcst σ6 hF).1, hq', Nat.cast_pos, not_lt, Nat.le_zero] at hex2
  obtain rfl : e = 0 := by
    cases e with
    | zero => rfl
    | succ j => rw [four_pow_div] at hex2; exact absurd hex2 (by positivity)
  have hsq : lo = Nat.sqrt n := Nat.eq_sqrt'.2 ⟨hlo, by simpa using hn⟩
  subst hsq
  exact ⟨by rw [hd']; simp, hr', hF⟩


/-- The rule of `xpow2`: with `nat n = W < ℓ` and `nat one = 1`, it ends with `p = 2 ^ W` and `nat i = W`, having
changed only the scalar `p` and the natural `i`, within `4 W + 4` units. -/
theorem XV.pow2 {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {p i n one : ℕ}
    (hp : p < L.NS) (hi : i < L.NN) (hn : n < L.NN) (ho : one < L.NN) (hin : i ≠ n) (hio : i ≠ one)
    {W : ℕ} (hW : σ.nat n = W) (h1 : σ.nat one = 1) (hWa : W < 2 ^ ℓa) (hWl : W < ℓ) :
    XRunsB L X ℓa ℓ (xpow2 L p i n one) σ (4 * W + 4)
      (fun σ' => σ'.sc p = 2 ^ W ∧ σ'.nat i = W ∧ Frame [p] [i] σ σ') := by
  have hpow : ∀ k ≤ W, |(2 : ℝ) ^ k| < 2 ^ ℓ := fun k hk => by
    rw [abs_of_nonneg (by positivity)]
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  refine XV.mono (K := 1 + (W * (1 + 3) + 3))
    (XV.seq (XV.sconst hL hp 1 rfl (by simpa using hpow 0 (Nat.zero_le _))) fun σ1 e1 => ?_) (by omega)
    (fun _ h => h)
  subst e1
  refine XV.mono (XV.forN hL hi hn ho hin hio W 1 hWa (fun k σ' => σ'.sc p = 2 ^ k ∧ Frame [p] [i] σ σ') _
    (by simpa using hW) (by simpa using h1) ⟨by simp, ((Frame.refl _ _ σ).setSc (by simp) _).setNat (by simp) _⟩ ?_)
    le_rfl (fun σ' ⟨⟨hp', hF⟩, hi', _, _⟩ => ⟨hp', hi', hF⟩)
  intro k hk σ' ⟨hp', hF⟩ hik hnk h1k
  have hv : RealRAM.Op2.eval .add (σ'.sc p) (σ'.sc p) = 2 ^ (k + 1) := by
    rw [hp', pow_succ]; simp only [RealRAM.Op2.eval]; ring
  refine XV.mono (XV.sop2 hL hp hp hp .add (by intro e; cases e) (by rw [hp']; exact hpow k hk.le)
    (by rw [hp']; exact hpow k hk.le) (by rw [hv]; exact hpow (k + 1) hk)) le_rfl (fun σ'' e => ?_)
  subst e
  exact ⟨hik, hnk, h1k, by simp [hv], (hF.setSc (by simp) _).setNat (by simp) _⟩

end AdversarialBco.Bit.Transfer
