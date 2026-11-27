/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.SepMath

@[expose] public section

/-!
# UNI-SEP: Lemma SEP on the grid

`sepAcc : SepAcc`. The integer routines `lineZ`, `sepZ` of SepSpec.lean compute Procedures LINE and SEP of
Poly/Df2Oracle.lean (`line`, `sep`) exactly, read on the grid: a point `X/2^E`, a length `Λ/2^E`, a value `V/2^{eu}`
(`line_grid`, `sepCoords_grid`, `sep_grid`), for the evaluator `vGrid` that returns `evN X/2^{eu}` at a grid point
`X/2^E` and the exact value elsewhere. Every window and scale is a power of two and every division of the integer
routines is exact while the exponents stay above `0` (`SepInv`), which `E ≥ e₁ + d (2J + 6 + eτ + eL)` gives. Then
`lemmaSEP` (Poly/Df2OracleProof.lean), whose evaluator hypothesis asks accuracy only at the points within `2ℓ₁` of `y⁰`
(grid points here, where the hypothesis of `SepAcc` gives it, and other points, where `vGrid` is exact), gives the
conclusion of `SepAcc`.
-/

namespace AdversarialBco.Uni

open AdversarialBco AdversarialBco.Poly AdversarialBco.Poly.LeanAp Matrix

variable {d : ℕ}

/-! ## The grid -/

theorem gridR_inj {E : ℕ} {X X' : Fin d → ℤ} (h : gridR E X = gridR E X') : X = X' := by
  funext i
  have := congrFun h i
  simp only [gridR] at this
  have h2 : (2 : ℝ) ^ E ≠ 0 := by positivity
  exact_mod_cast (div_left_inj' h2).1 this

theorem gridR_add_single (E : ℕ) (Y : Fin d → ℤ) (S : ℤ) (i : Fin d) :
    gridR E (Y + S • eZ i) = gridR E Y + ((S : ℝ) / 2 ^ E) • oUnit i := by
  funext k
  simp only [gridR, eZ, oUnit, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> push_cast <;> ring

theorem gridR_sub_single (E : ℕ) (Y : Fin d → ℤ) (S : ℤ) (i : Fin d) :
    gridR E (Y - S • eZ i) = gridR E Y - ((S : ℝ) / 2 ^ E) • oUnit i := by
  funext k
  simp only [gridR, eZ, oUnit, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> push_cast <;> ring

open Classical in
/-- The evaluator on the grid: `evN X/2^{eu}` at a grid point `X/2^E`, the value of `h` elsewhere. -/
noncomputable def vGrid (E eu : ℕ) (evN : (Fin d → ℤ) → ℤ) (h : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  if hx : ∃ X, x = gridR E X then (evN hx.choose : ℝ) / 2 ^ eu else h x

theorem vGrid_grid (E eu : ℕ) (evN : (Fin d → ℤ) → ℤ) (h : (Fin d → ℝ) → ℝ) (X : Fin d → ℤ) :
    vGrid E eu evN h (gridR E X) = (evN X : ℝ) / 2 ^ eu := by
  have hx : ∃ X', gridR E X = gridR E X' := ⟨X, rfl⟩
  rw [vGrid, dite_eq_left hx, ← gridR_inj hx.choose_spec]

/-! ## LINE -/

/-- A window of LINE on the grid as a real window. -/
noncomputable def winR (E eu : ℕ) (W : WinZ) : LineWin :=
  ⟨(W.p0 : ℝ) / 2 ^ E, (W.lam : ℝ) / 2 ^ E, (W.v0 : ℝ) / 2 ^ eu, (W.v1 : ℝ) / 2 ^ eu, (W.v2 : ℝ) / 2 ^ eu,
    (W.v3 : ℝ) / 2 ^ eu, (W.v4 : ℝ) / 2 ^ eu⟩

/-- The first window of the halving from `p₁` (real). -/
noncomputable def halveA (φ : ℝ → ℝ) (W : LineWin) : LineWin :=
  ⟨W.p0 + W.lam, W.lam / 4, W.v1, φ (W.p0 + W.lam + W.lam / 4), φ (W.p0 + W.lam + 2 * (W.lam / 4)),
    φ (W.p0 + W.lam + 3 * (W.lam / 4)), W.v2⟩

/-- The second window of the halving from `p₂` (real). -/
noncomputable def halveB (φ : ℝ → ℝ) (W : LineWin) : LineWin :=
  ⟨W.p0 + 2 * W.lam, W.lam / 4, W.v2, φ (W.p0 + 2 * W.lam + W.lam / 4), φ (W.p0 + 2 * W.lam + 2 * (W.lam / 4)),
    φ (W.p0 + 2 * W.lam + 3 * (W.lam / 4)), W.v3⟩

/-- The first window of the halving from `p₁` (integer). -/
def halveAZ (f : ℤ → ℤ) (W : WinZ) : WinZ :=
  ⟨W.p0 + W.lam, W.lam / 4, W.v1, f (W.p0 + W.lam + W.lam / 4), f (W.p0 + W.lam + 2 * (W.lam / 4)),
    f (W.p0 + W.lam + 3 * (W.lam / 4)), W.v2⟩

/-- The second window of the halving from `p₂` (integer). -/
def halveBZ (f : ℤ → ℤ) (W : WinZ) : WinZ :=
  ⟨W.p0 + 2 * W.lam, W.lam / 4, W.v2, f (W.p0 + 2 * W.lam + W.lam / 4), f (W.p0 + 2 * W.lam + 2 * (W.lam / 4)),
    f (W.p0 + 2 * W.lam + 3 * (W.lam / 4)), W.v3⟩

theorem lineFirst_some (ℓ τ : ℝ) (φ : ℝ → ℝ) :
    lineFirst (fun s _ => some (φ s)) ℓ τ =
      some ⟨0, ℓ / 4, φ 0, φ (ℓ / 4), φ (2 * (ℓ / 4)), φ (3 * (ℓ / 4)), φ (4 * (ℓ / 4))⟩ := rfl

theorem lineHalve_some (τ : ℝ) (φ : ℝ → ℝ) (W : LineWin) :
    lineHalve (fun s _ => some (φ s)) τ W =
      some (if (halveB φ W).spread < (halveA φ W).spread then halveB φ W else halveA φ W) := rfl

theorem lineHalveZ_eq (f : ℤ → ℤ) (W : WinZ) :
    lineHalveZ f W = if (halveBZ f W).sp < (halveAZ f W).sp then halveBZ f W else halveAZ f W := rfl

theorem lineHalveZ_lam (f : ℤ → ℤ) (W : WinZ) : (lineHalveZ f W).lam = W.lam / 4 := by
  rw [lineHalveZ_eq]; split_ifs <;> rfl

/-- The one-dimensional evaluator at a grid point is the integer value at the scale `2^{eu}`. -/
def GridFn (E eu : ℕ) (f : ℤ → ℤ) (φ : ℝ → ℝ) : Prop := ∀ S : ℤ, φ ((S : ℝ) / 2 ^ E) = (f S : ℝ) / 2 ^ eu

theorem lineFirst_grid {E eu : ℕ} {f : ℤ → ℤ} {φ : ℝ → ℝ} (hφ : GridFn E eu f φ) (τ : ℝ) (l : ℤ) :
    lineFirst (fun s _ => some (φ s)) (((4 * l : ℤ) : ℝ) / 2 ^ E) τ = some (winR E eu (lineFirstZ f (4 * l))) := by
  rw [lineFirst_some, Option.some.injEq]
  simp only [winR, lineFirstZ]
  rw [show 4 * l / 4 = l by omega]
  congr 1
  all_goals first
    | (rw [← hφ]; congr 1; push_cast; ring)
    | (push_cast; ring)

theorem winR_spread (E eu : ℕ) (V : WinZ) :
    (winR E eu V).spread = (V.sp : ℝ) / 2 ^ eu / ((V.lam : ℝ) / 2 ^ E) := by
  simp only [LineWin.spread, winR, WinZ.sp]; push_cast; ring

theorem halveA_grid {E eu : ℕ} {f : ℤ → ℤ} {φ : ℝ → ℝ} (hφ : GridFn E eu f φ) (W : WinZ) (l : ℤ)
    (hW : W.lam = 4 * l) : halveA φ (winR E eu W) = winR E eu (halveAZ f W) := by
  have hl : W.lam / 4 = l := by omega
  simp only [halveA, halveAZ, winR]
  rw [hl, hW]
  congr 1
  all_goals first
    | (rw [← hφ]; congr 1; push_cast; ring)
    | (push_cast; ring)

theorem halveB_grid {E eu : ℕ} {f : ℤ → ℤ} {φ : ℝ → ℝ} (hφ : GridFn E eu f φ) (W : WinZ) (l : ℤ)
    (hW : W.lam = 4 * l) : halveB φ (winR E eu W) = winR E eu (halveBZ f W) := by
  have hl : W.lam / 4 = l := by omega
  simp only [halveB, halveBZ, winR]
  rw [hl, hW]
  congr 1
  all_goals first
    | (rw [← hφ]; congr 1; push_cast; ring)
    | (push_cast; ring)

theorem lineHalve_grid {E eu : ℕ} {f : ℤ → ℤ} {φ : ℝ → ℝ} (hφ : GridFn E eu f φ) (τ : ℝ) (W : WinZ) (l : ℤ)
    (hl0 : 0 < l) (hW : W.lam = 4 * l) :
    lineHalve (fun s _ => some (φ s)) τ (winR E eu W) = some (winR E eu (lineHalveZ f W)) := by
  rw [lineHalve_some, halveA_grid hφ W l hW, halveB_grid hφ W l hW, lineHalveZ_eq]
  have hlam : (halveAZ f W).lam = l ∧ (halveBZ f W).lam = l := by
    simp only [halveAZ, halveBZ]; omega
  have hpos : (0 : ℝ) < (l : ℝ) / 2 ^ E := by
    have : (0 : ℝ) < l := by exact_mod_cast hl0
    positivity
  have hiff : (winR E eu (halveBZ f W)).spread < (winR E eu (halveAZ f W)).spread ↔
      (halveBZ f W).sp < (halveAZ f W).sp := by
    rw [winR_spread, winR_spread, hlam.1, hlam.2, div_lt_div_iff_of_pos_right hpos,
      div_lt_div_iff_of_pos_right (by positivity)]
    exact Int.cast_lt
  by_cases hc : (halveBZ f W).sp < (halveAZ f W).sp
  · rw [ite_eq_left (hiff.2 hc), ite_eq_left hc]
  · rw [ite_eq_right (mt hiff.1 hc), ite_eq_right hc]

theorem winR_sd (E eu : ℕ) (V : WinZ) : (winR E eu V).sd = (V.sd : ℝ) / 2 ^ eu := by
  simp only [LineWin.sd, winR, WinZ.sd]; push_cast; ring

/-- The stop of LINE read on the grid: `sd ≤ τλ/2` exactly when `sd · 2^{E+eτ+1} ≤ Λ · 2^{eu}`. -/
theorem sd_le_iff (E eu eτ : ℕ) (V : WinZ) :
    (winR E eu V).sd ≤ (2 : ℝ)⁻¹ ^ eτ * (winR E eu V).lam / 2 ↔ V.sd * 2 ^ (E + eτ + 1) ≤ V.lam * 2 ^ eu := by
  have hC : (0 : ℝ) < 2 ^ (eu + E + eτ + 1) := by positivity
  have e1 : (winR E eu V).sd * 2 ^ (eu + E + eτ + 1) = ((V.sd * 2 ^ (E + eτ + 1) : ℤ) : ℝ) := by
    rw [winR_sd]; push_cast; rw [pow_add, pow_add, pow_add, pow_add, pow_add]; field_simp
  have e2 : (2 : ℝ)⁻¹ ^ eτ * (winR E eu V).lam / 2 * 2 ^ (eu + E + eτ + 1) = ((V.lam * 2 ^ eu : ℤ) : ℝ) := by
    simp only [winR]; push_cast; rw [pow_add, pow_add, pow_add, inv_pow]; field_simp
  rw [← mul_le_mul_iff_of_pos_right hC, e1, e2, Int.cast_le]

theorem lineStop_grid (E eu : ℕ) (W : WinZ) :
    some ((winR E eu W).p0 + 2 * (winR E eu W).lam, (winR E eu W).lam) =
      Option.map (fun r : ℤ × ℤ => ((r.1 : ℝ) / 2 ^ E, (r.2 : ℝ) / 2 ^ E)) (some (W.p0 + 2 * W.lam, W.lam)) := by
  rw [Option.map_some, Option.some.injEq]
  simp only [winR]
  congr 1
  push_cast
  ring

/-- The loop of LINE on the grid, while the spacing is `4^j k`, `k > 0`. -/
theorem lineLoop_grid {E eu : ℕ} {f : ℤ → ℤ} {φ : ℝ → ℝ} (hφ : GridFn E eu f φ) (eτ : ℕ) :
    ∀ (j : ℕ) (W : WinZ) (k : ℤ), 0 < k → W.lam = 4 ^ j * k →
      lineLoop (fun s _ => some (φ s)) ((2 : ℝ)⁻¹ ^ eτ) j (winR E eu W) =
        (lineLoopZ f (2 ^ (E + eτ + 1)) (2 ^ eu) j W).map (fun r => ((r.1 : ℝ) / 2 ^ E, (r.2 : ℝ) / 2 ^ E)) := by
  intro j
  induction j with
  | zero =>
    intro W k hk hW
    rw [lineLoop, lineLoopZ]
    by_cases hc : W.sd * 2 ^ (E + eτ + 1) ≤ W.lam * 2 ^ eu
    · rw [ite_eq_left ((sd_le_iff E eu eτ W).2 hc), ite_eq_left hc]
      exact lineStop_grid E eu W
    · rw [ite_eq_right (mt (sd_le_iff E eu eτ W).1 hc), ite_eq_right hc]; rfl
  | succ j ih =>
    intro W k hk hW
    rw [lineLoop, lineLoopZ]
    by_cases hc : W.sd * 2 ^ (E + eτ + 1) ≤ W.lam * 2 ^ eu
    · rw [ite_eq_left ((sd_le_iff E eu eτ W).2 hc), ite_eq_left hc]
      exact lineStop_grid E eu W
    · rw [ite_eq_right (mt (sd_le_iff E eu eτ W).1 hc), ite_eq_right hc]
      have hW4 : W.lam = 4 * (4 ^ j * k) := by rw [hW, pow_succ]; ring
      have hl0 : 0 < 4 ^ j * k := by positivity
      show lineHalve _ _ _ >>= _ = _
      rw [lineHalve_grid hφ _ W (4 ^ j * k) hl0 hW4]
      exact ih (lineHalveZ f W) k hk (by rw [lineHalveZ_lam, hW4]; omega)

/-- LINE on the grid, for a length `4^{J+1} k`, `k > 0`. -/
theorem line_grid {E eu : ℕ} {f : ℤ → ℤ} {φ : ℝ → ℝ} (hφ : GridFn E eu f φ) (eτ J : ℕ) (len k : ℤ) (hk : 0 < k)
    (hlen : len = 4 ^ (J + 1) * k) :
    line (fun s _ => some (φ s)) ((len : ℝ) / 2 ^ E) ((2 : ℝ)⁻¹ ^ eτ) J =
      (lineZ f len (2 ^ (E + eτ + 1)) (2 ^ eu) J).map (fun r => ((r.1 : ℝ) / 2 ^ E, (r.2 : ℝ) / 2 ^ E)) := by
  have h4 : len = 4 * (4 ^ J * k) := by rw [hlen, pow_succ]; ring
  show lineFirst _ _ _ >>= _ = _
  rw [h4, lineFirst_grid hφ]
  exact lineLoop_grid hφ eτ J _ k hk (by simp only [lineFirstZ]; omega)

/-- The output scale of the loop of LINE is the spacing of a window it visited, `4^m k`, `m ≤ j`. -/
theorem lineLoopZ_out (f : ℤ → ℤ) (cA cB : ℤ) :
    ∀ (j : ℕ) (W : WinZ) (k s δ : ℤ), W.lam = 4 ^ j * k → lineLoopZ f cA cB j W = some (s, δ) →
      ∃ m ≤ j, δ = 4 ^ m * k := by
  intro j
  induction j with
  | zero =>
    intro W k s δ hW h
    rw [lineLoopZ] at h
    split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨0, le_rfl, by rw [← h.2, hW]⟩
  | succ j ih =>
    intro W k s δ hW h
    rw [lineLoopZ] at h
    split_ifs at h with hc
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨j + 1, le_rfl, by rw [← h.2, hW]⟩
    · have hW4 : W.lam = 4 * (4 ^ j * k) := by rw [hW, pow_succ]; ring
      obtain ⟨m, hm, e⟩ := ih (lineHalveZ f W) k s δ (by rw [lineHalveZ_lam, hW4]; omega) h
      exact ⟨m, by omega, e⟩

theorem int_pow_div (s t : ℕ) : (2 : ℤ) ^ (s + t) / 2 ^ s = 2 ^ t := by
  rw [pow_add]; exact Int.mul_ediv_cancel_left _ (by positivity)

/-- LINE from a length `2^a`, `a ≥ 2J + 2`, returns a scale `2^b`, `a - 2J - 2 ≤ b ≤ a - 2`. -/
theorem lineZ_pow (f : ℤ → ℤ) (cA cB : ℤ) (J a : ℕ) (ha : 2 * J + 2 ≤ a) (s δ : ℤ)
    (hl : lineZ f (2 ^ a) cA cB J = some (s, δ)) : ∃ b, δ = 2 ^ b ∧ a - 2 * J - 2 ≤ b ∧ b ≤ a - 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, a = 2 * J + 2 + t := ⟨a - (2 * J + 2), by omega⟩
  have h4 : (2 : ℤ) ^ (2 * J + 2 + t) = 4 * (4 ^ J * 2 ^ t) := by
    rw [pow_add, pow_add, pow_mul]; norm_num; ring
  have hW : (lineFirstZ f (2 ^ (2 * J + 2 + t))).lam = 4 ^ J * 2 ^ t := by
    simp only [lineFirstZ]; rw [h4]; omega
  obtain ⟨m, hm, e⟩ := lineLoopZ_out f cA cB J _ _ s δ hW hl
  refine ⟨2 * m + t, ?_, by omega, by omega⟩
  rw [e, pow_add, pow_mul]; norm_num

/-! ## SEP -/

/-- The evaluator of `lemmaSEP` on the grid: `vGrid` at every point and every error. -/
noncomputable def evG (E eu : ℕ) (evN : (Fin d → ℤ) → ℤ) (h : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ → Option ℝ :=
  fun x _ => some (vGrid E eu evN h x)

/-- A state of SEP on the grid as a real state. -/
noncomputable def stR (E : ℕ) (st : SepStZ d) : SepSt d := (gridR E st.1, (st.2.1 : ℝ) / 2 ^ E, gridR E st.2.2)

theorem gridFn_coord (E eu : ℕ) (evN : (Fin d → ℤ) → ℤ) (h : (Fin d → ℝ) → ℝ) (Y : Fin d → ℤ) (i : Fin d) :
    GridFn E eu (fun s => evN (Y + s • eZ i)) (fun s => vGrid E eu evN h (gridR E Y + s • oUnit i)) := by
  intro S
  show vGrid E eu evN h (gridR E Y + ((S : ℝ) / 2 ^ E) • oUnit i) = (evN (Y + S • eZ i) : ℝ) / 2 ^ eu
  rw [← gridR_add_single, vGrid_grid]

theorem oValsAll_evG (E eu : ℕ) (evN : (Fin d → ℤ) → ℤ) (h : (Fin d → ℝ) → ℝ) (x : Fin d → Fin d → ℝ)
    (η : Fin d → ℝ) : oValsAll (evG E eu evN h) x η = some fun i => vGrid E eu evN h (x i) := by
  unfold oValsAll evG; simp

/-- The invariant of the coordinate searches on the grid after `k` coordinates: the length is `2^a` with
`(d - k) c ≤ a ≤ E`, `c = 2J + 6 + eτ + eL`, and the scales found so far are powers of two up to `2^E`. -/
def SepInv (d E J eτ eL k : ℕ) (st : SepStZ d) : Prop :=
  ∃ a, st.2.1 = 2 ^ a ∧ (d - k) * (2 * J + 6 + eτ + eL) ≤ a ∧ a ≤ E ∧
    ∀ i : Fin d, (i : ℕ) < k → ∃ b, st.2.2 i = 2 ^ b ∧ b ≤ E

/-- One coordinate search of SEP on the grid, from a state of the invariant. -/
theorem sepCoord_grid {E eu eτ eL J k : ℕ} (evN : (Fin d → ℤ) → ℤ) (h : (Fin d → ℝ) → ℝ) (i : Fin d)
    (hik : (i : ℕ) = k) (st : SepStZ d) (hst : SepInv d E J eτ eL k st) :
    sepCoord (evG E eu evN h) ((2 : ℝ)⁻¹ ^ eτ) (2 ^ eL) J i (stR E st) =
        (sepCoordZ evN (2 ^ (eτ + 4 + eL)) (2 ^ (E + eτ + 1)) (2 ^ eu) J i st).map (stR E) ∧
      ∀ st', sepCoordZ evN (2 ^ (eτ + 4 + eL)) (2 ^ (E + eτ + 1)) (2 ^ eu) J i st = some st' →
        SepInv d E J eτ eL (k + 1) st' := by
  obtain ⟨Y, len, Δ⟩ := st
  obtain ⟨a, hlen, ha1, ha2, hΔ⟩ := hst
  simp only at hlen hΔ
  subst hlen
  have hdk : d - k = (d - (k + 1)) + 1 := by have := i.2; omega
  rw [hdk, add_one_mul] at ha1
  have eR : sepCoord (evG E eu evN h) ((2 : ℝ)⁻¹ ^ eτ) (2 ^ eL) J i (stR E (Y, 2 ^ a, Δ)) =
      line (fun s _ => some (vGrid E eu evN h (gridR E Y + s • oUnit i))) (((2 ^ a : ℤ) : ℝ) / 2 ^ E)
          ((2 : ℝ)⁻¹ ^ eτ) J >>= fun r =>
        some (gridR E Y + r.1 • oUnit i, (2 : ℝ)⁻¹ ^ eτ * r.2 / (16 * 2 ^ eL), Function.update (gridR E Δ) i r.2) :=
    rfl
  have eZ' : sepCoordZ evN (2 ^ (eτ + 4 + eL)) (2 ^ (E + eτ + 1)) (2 ^ eu) J i (Y, 2 ^ a, Δ) =
      lineZ (fun s => evN (Y + s • eZ i)) (2 ^ a) (2 ^ (E + eτ + 1)) (2 ^ eu) J >>= fun r =>
        some (Y + r.1 • eZ i, r.2 / 2 ^ (eτ + 4 + eL), Function.update Δ i r.2) := rfl
  obtain ⟨t, ht⟩ : ∃ t, a = 2 * J + 2 + t := ⟨a - (2 * J + 2), by omega⟩
  have hlen4 : (2 : ℤ) ^ a = 4 ^ (J + 1) * 2 ^ t := by
    rw [ht, pow_add, show 2 * J + 2 = 2 * (J + 1) by ring, pow_mul]; norm_num
  rw [eR, eZ', line_grid (gridFn_coord E eu evN h Y i) eτ J (2 ^ a) (2 ^ t) (by positivity) hlen4]
  cases hl : lineZ (fun s => evN (Y + s • eZ i)) (2 ^ a) (2 ^ (E + eτ + 1)) (2 ^ eu) J with
  | none => simp
  | some r =>
    obtain ⟨s, δ⟩ := r
    obtain ⟨b, hb, hb1, hb2⟩ := lineZ_pow _ _ _ J a (by omega) s δ hl
    obtain ⟨u, hu⟩ : ∃ u, b = (eτ + 4 + eL) + u := ⟨b - (eτ + 4 + eL), by omega⟩
    have hdiv : δ / 2 ^ (eτ + 4 + eL) = 2 ^ u := by rw [hb, hu, int_pow_div]
    refine ⟨?_, ?_⟩
    · simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, stR, Option.some.injEq, Prod.mk.injEq]
      refine ⟨(gridR_add_single E Y s i).symm, ?_, ?_⟩
      · rw [hdiv, hb, hu]; push_cast; rw [inv_pow, pow_add, pow_add, pow_add]; field_simp; ring
      · funext j; simp only [gridR, Function.update_apply]; split_ifs <;> rfl
    · intro st' hst'
      simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hst'
      subst hst'
      refine ⟨u, hdiv, by omega, by omega, ?_⟩
      intro j hj
      by_cases hji : j = i
      · exact ⟨b, by simp only [Function.update_apply, ite_eq_left hji, hb], by omega⟩
      · have hjk : (j : ℕ) < k := by
          have : (j : ℕ) ≠ k := fun e => hji (Fin.ext (e.trans hik.symm))
          omega
        obtain ⟨b', hb', hb'E⟩ := hΔ j hjk
        exact ⟨b', by simp only [Function.update_apply, ite_eq_right hji]; exact hb', hb'E⟩

/-- The coordinate searches of SEP on the grid. -/
theorem sepCoords_grid {E eu e1 eτ eL J : ℕ} (evN : (Fin d → ℤ) → ℤ) (h : (Fin d → ℝ) → ℝ) (Y0 : Fin d → ℤ)
    (hE : e1 + d * (2 * J + 6 + eτ + eL) ≤ E) :
    ∀ k ≤ d, sepCoords (evG E eu evN h) (gridR E Y0) ((2 : ℝ)⁻¹ ^ eτ) ((2 : ℝ)⁻¹ ^ e1) (2 ^ eL) J k =
        (sepCoordsZ evN Y0 (2 ^ (E - e1)) (2 ^ (eτ + 4 + eL)) (2 ^ (E + eτ + 1)) (2 ^ eu) J k).map (stR E) ∧
      ∀ st, sepCoordsZ evN Y0 (2 ^ (E - e1)) (2 ^ (eτ + 4 + eL)) (2 ^ (E + eτ + 1)) (2 ^ eu) J k = some st →
        SepInv d E J eτ eL k st := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, ?_⟩
    · rw [sepCoords, sepCoordsZ, Option.map_some, Option.some.injEq]
      simp only [stR]
      refine Prod.ext rfl (Prod.ext ?_ ?_)
      · obtain ⟨t, ht⟩ : ∃ t, E = e1 + t := ⟨E - e1, by omega⟩
        rw [ht, Nat.add_sub_cancel_left]; push_cast; rw [pow_add, inv_pow]; field_simp
      · funext i; simp [gridR]
    · intro st hst
      rw [sepCoordsZ, Option.some.injEq] at hst
      subst hst
      exact ⟨E - e1, rfl, by rw [Nat.sub_zero]; omega, by omega, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    have hk' : k < d := by omega
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [sepCoords, sepCoordsZ, ih1]
    cases hz : sepCoordsZ evN Y0 (2 ^ (E - e1)) (2 ^ (eτ + 4 + eL)) (2 ^ (E + eτ + 1)) (2 ^ eu) J k with
    | none => exact ⟨rfl, fun st hst => by simp at hst⟩
    | some st =>
      have key := sepCoord_grid (eu := eu) evN h ⟨k, hk'⟩ rfl st (ih2 st hz)
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, dite_eq_left hk']
      exact key

/-- Procedure SEP on the grid: `sepE` read on the grid is `sep` for the evaluator `evG`. -/
theorem sep_grid {E eu e1 eτ eL : ℕ} (evN : (Fin d → ℤ) → ℤ) (h : (Fin d → ℝ) → ℝ) (Y0 : Fin d → ℤ)
    (hE : e1 + d * (2 * (eL + eτ + 3) + 6 + eτ + eL) ≤ E) :
    sep (evG E eu evN h) (gridR E Y0) ((2 : ℝ)⁻¹ ^ eτ) ((2 : ℝ)⁻¹ ^ e1) (2 ^ eL) (eL + eτ + 3) =
      (sepE evN Y0 E e1 eτ eL eu).map (fun r => (gridR E r.1, fun i => (r.2 i : ℝ) / 2 ^ (eu + 1))) := by
  obtain ⟨hc1, hc2⟩ := sepCoords_grid (eu := eu) evN h Y0 hE d le_rfl
  have eR : sep (evG E eu evN h) (gridR E Y0) ((2 : ℝ)⁻¹ ^ eτ) ((2 : ℝ)⁻¹ ^ e1) (2 ^ eL) (eL + eτ + 3) =
      sepCoords (evG E eu evN h) (gridR E Y0) ((2 : ℝ)⁻¹ ^ eτ) ((2 : ℝ)⁻¹ ^ e1) (2 ^ eL) (eL + eτ + 3) d >>=
        fun st =>
          oValsAll (evG E eu evN h) (fun i => st.1 + st.2.2 i • oUnit i)
              (fun i => (2 : ℝ)⁻¹ ^ eτ * st.2.2 i / 400) >>= fun vp =>
          oValsAll (evG E eu evN h) (fun i => st.1 - st.2.2 i • oUnit i)
              (fun i => (2 : ℝ)⁻¹ ^ eτ * st.2.2 i / 400) >>= fun vm =>
          some (st.1, fun i => (vp i - vm i) / (2 * st.2.2 i)) := rfl
  have eZ' : sepE evN Y0 E e1 eτ eL eu =
      sepCoordsZ evN Y0 (2 ^ (E - e1)) (2 ^ (eτ + 4 + eL)) (2 ^ (E + eτ + 1)) (2 ^ eu) (eL + eτ + 3) d >>=
        fun st => some (st.1, fun i => (evN (st.1 + st.2.2 i • eZ i) - evN (st.1 - st.2.2 i • eZ i)) *
          (2 ^ E / st.2.2 i)) := rfl
  rw [eR, eZ', hc1]
  cases hz : sepCoordsZ evN Y0 (2 ^ (E - e1)) (2 ^ (eτ + 4 + eL)) (2 ^ (E + eτ + 1)) (2 ^ eu) (eL + eτ + 3) d with
  | none => rfl
  | some st =>
    obtain ⟨a, -, -, -, hΔ⟩ := hc2 st hz
    obtain ⟨Y, len, Δ⟩ := st
    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, stR, oValsAll_evG, Option.some.injEq]
    congr 1
    funext i
    obtain ⟨b, hb, hbE⟩ := hΔ i i.2
    simp only at hb
    rw [show gridR E Δ i = (Δ i : ℝ) / 2 ^ E from rfl, ← gridR_add_single, ← gridR_sub_single, vGrid_grid,
      vGrid_grid, hb]
    obtain ⟨t, ht⟩ : ∃ t, E = b + t := ⟨E - b, by omega⟩
    rw [ht, int_pow_div]
    push_cast
    rw [pow_add, pow_add]; field_simp

/-! ## SepAcc -/

theorem ceil_logb_sep (eτ eL : ℕ) : ⌈Real.logb 2 (8 * (2 : ℝ) ^ eL / (2 : ℝ)⁻¹ ^ eτ)⌉₊ = eL + eτ + 3 := by
  have e : 8 * (2 : ℝ) ^ eL / (2 : ℝ)⁻¹ ^ eτ = 2 ^ (eL + eτ + 3) := by
    rw [inv_pow, div_inv_eq_mul, pow_add, pow_add]; norm_num; ring
  rw [e, Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one, Nat.ceil_natCast]

theorem sepAcc : SepAcc := by
  intro d h evN Y0 E e1 eτ eL eu hd hconv hLip hE hacc
  have hev : ∀ x η, oNorm (x - gridR E Y0) ≤ 2 * (2 : ℝ)⁻¹ ^ e1 →
      (2 : ℝ)⁻¹ ^ eτ * (2 : ℝ)⁻¹ ^ e1 / 1600 *
          (2 : ℝ) ^ (-(3 * (d : ℝ) * (⌈Real.logb 2 (8 * (2 : ℝ) ^ eL / (2 : ℝ)⁻¹ ^ eτ)⌉₊ + 1))) ≤ η →
      ∃ v, evG E eu evN h x η = some v ∧ |v - h x| ≤ η := by
    intro x η hx hη
    rw [ceil_logb_sep] at hη
    have e : (2 : ℝ) ^ (-(3 * (d : ℝ) * (((eL + eτ + 3 : ℕ) : ℝ) + 1))) = (2 : ℝ)⁻¹ ^ (3 * d * (eL + eτ + 4)) := by
      rw [Real.rpow_neg (by norm_num),
        show (3 * (d : ℝ) * (((eL + eτ + 3 : ℕ) : ℝ) + 1)) = ((3 * d * (eL + eτ + 4) : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast, inv_pow]
    rw [e] at hη
    have hη0 : 0 ≤ η := le_trans (by positivity) hη
    refine ⟨vGrid E eu evN h x, rfl, ?_⟩
    by_cases hg : ∃ X, x = gridR E X
    · obtain ⟨X, rfl⟩ := hg
      rw [vGrid_grid]
      exact le_trans (hacc X hx) hη
    · rw [vGrid, dite_eq_right hg, sub_self, abs_zero]; exact hη0
  obtain ⟨y, g, hs, hy, hcut⟩ := AdversarialBco.Poly.lemmaSEP d h (2 ^ eL) ((2 : ℝ)⁻¹ ^ eτ) ((2 : ℝ)⁻¹ ^ e1)
    (gridR E Y0) (evG E eu evN h) hd hconv hLip (by positivity)
    (le_trans (pow_le_one₀ (by norm_num) (by norm_num)) (one_le_pow₀ (by norm_num))) (by positivity) hev
  rw [ceil_logb_sep, sep_grid evN h Y0 hE] at hs
  cases hz : sepE evN Y0 E e1 eτ eL eu with
  | none => rw [hz] at hs; simp at hs
  | some r =>
    rw [hz, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨hy', hg'⟩ := hs
    refine ⟨r.1, r.2, rfl, by rw [hy']; exact hy, fun z => ?_⟩
    rw [hy', hg']
    exact hcut z

end AdversarialBco.Uni
