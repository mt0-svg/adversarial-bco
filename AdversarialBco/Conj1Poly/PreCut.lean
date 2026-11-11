/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Poly.PreCode

@[expose] public section

/-!
# The cut of `PRE^b` on raw cells

The loops of `cutCmd` on cells given by their addresses: `W` the first scalar cell, `Fs` the vector `v` then `b`,
`Fa` the centre, `FE` the matrix (row `t` from `FE + d t`), `gB` the row `g` of the data. Each lemma takes the
registers it reads and the order of the regions as hypotheses, and gives the cells it writes as functions of the
cells before it, with the frame of the rest.
-/

namespace AdversarialBco.Conj1Poly

open AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Mach

variable {d : ℕ}

/-- A counted loop: the body moves the counter `a` from `t` to `t + 1` below the fixed bound held in `b`. -/
theorem exec_for {w : World d} {a b : ℕ} {c : Cmd} (N Kb : ℕ) (P : ℕ → State d → Prop)
    (hab : ∀ t S, P t S → S.nreg a = t ∧ S.nreg b = N)
    (hbody : ∀ t S, t < N → P t S → ∃ k S', k ≤ Kb ∧ Exec w c S k S' ∧ P (t + 1) S') (S : State d) (h0 : P 0 S) :
    ∃ k S', k ≤ N * (Kb + 2) + 2 ∧ Exec w (.whileN a b c) S k S' ∧ P N S' := by
  obtain ⟨k, S', t', hk, x, ⟨htN, hP⟩, hn⟩ := exec_whileN_inv (w := w) (a := a) (b := b) (c := c)
    (fun t S => t ≤ N ∧ P t S) N Kb
    (fun t S hI hc => by
      obtain ⟨h1, h2⟩ := hab t S hI.2
      simp only [condN, h1, h2] at hc; exact hc)
    (fun t S hI hc => by
      obtain ⟨h1, h2⟩ := hab t S hI.2
      have ht : t < N := by simp only [condN, h1, h2] at hc; exact hc
      obtain ⟨k, S', hk, x, hP⟩ := hbody t S ht hI.2
      exact ⟨k, S', hk, x, ht, hP⟩) 0 S ⟨Nat.zero_le _, h0⟩
  obtain ⟨h1, h2⟩ := hab t' S' hP
  have : t' = N := by
    simp only [condN, h1, h2, not_lt] at hn
    have := (hab t' S' hP).1
    omega
  subst this
  exact ⟨k, S', by simpa using hk, x, hP⟩

/-! ## `v = E g` and `γ = ⟨g, v⟩` -/

/-- The primitives of `mvBody` after the dot product. -/
theorem mvBody_exec_aux1 {w : World d} {r W Fs gB t p : ℕ} (X : State d)
    (h1 : X.nreg (r + 1) = d) (h6 : X.nreg (r + 6) = Fs) (h9 : X.nreg (r + 9) = 1) (h21 : X.nreg (r + 21) = W)
    (h34 : X.nreg (r + 34) = W + 13) (h36 : X.nreg (r + 36) = W + 15) (h40 : X.nreg (r + 40) = W + 19)
    (h48 : X.nreg (r + 48) = t) (h54 : X.nreg (r + 54) = gB) (h59 : X.nreg (r + 59) = p)
    (hgt : gB + t < W) (hFs : W + 24 ≤ Fs) :
    let Y := [Prim.nadd (r + 51) (r + 6) (r + 48), .op2 .add (r + 51) (r + 34) (r + 21),
      .nadd (r + 52) (r + 54) (r + 48), .op2 .mul (r + 36) (r + 52) (r + 34), .op2 .add (r + 40) (r + 40) (r + 36),
      .nadd (r + 59) (r + 59) (r + 1), .nadd (r + 48) (r + 48) (r + 9)].foldl (fun s p => p.exec w s) X
    Y.mem (Fs + t) = X.mem (W + 13) + X.mem W ∧
      Y.mem (W + 19) = X.mem (W + 19) + X.mem (gB + t) * X.mem (W + 13) ∧
      Y.nreg (r + 48) = t + 1 ∧ Y.nreg (r + 59) = p + d ∧
      (∀ i, i ≠ r + 48 → i ≠ r + 51 → i ≠ r + 52 → i ≠ r + 59 → Y.nreg i = X.nreg i) ∧
      (∀ c, c ≠ W + 15 → c ≠ W + 19 → c ≠ Fs + t → Y.mem c = X.mem c) ∧
      Y.draws = X.draws ∧ Y.rounds = X.rounds ∧ Y.pts = X.pts := by
  intro Y
  have a2 : W + 19 ≠ Fs + t := by omega
  have a3 : W + 13 ≠ Fs + t := by omega
  have a7 : gB ≠ Fs := by omega
  have a1' : Fs + t ≠ W + 15 := by omega
  have a2' : Fs + t ≠ W + 19 := by omega
  refine ⟨?_, ?_, ?_, ?_, fun i i1 i2 i3 i4 => ?_, fun c c1 c2 c3 => ?_, by simp only [Y, List.foldl, Prim.exec],
    by simp only [Y, List.foldl, Prim.exec], by simp only [Y, List.foldl, Prim.exec]⟩
  · simp [Y, List.foldl, Prim.exec, Function.update_apply, Op2.eval, h6, h21, h34, h36, h40, h48, h54, a1', a2']
  · simp [Y, List.foldl, Prim.exec, Op2.eval, h6, h21, h34, h36, h40, h48, h54, a2, a3, a7]
  · simp [Y, List.foldl, Prim.exec, Function.update_apply, h48, h9]
  · simp [Y, List.foldl, Prim.exec, Function.update_apply, h59, h1]
  · simp [Y, List.foldl, Prim.exec, Function.update_apply, i1, i2, i3, i4]
  · simp [Y, List.foldl, Prim.exec, Function.update_apply, h6, h36, h40, h48, c1, c2, c3]

/-- One row of `v = E g`: `v_t = ⟨E_t, g⟩` into `Fs + t`, and `γ += g_t v_t`. -/
theorem mvBody_exec {w : World d} {r W Fs FE gB t : ℕ} {S : State d}
    (e1 : S.nreg (r + 1) = d) (e6 : S.nreg (r + 6) = Fs) (e9 : S.nreg (r + 9) = 1) (e21 : S.nreg (r + 21) = W)
    (e34 : S.nreg (r + 34) = W + 13) (e36 : S.nreg (r + 36) = W + 15) (e40 : S.nreg (r + 40) = W + 19)
    (e48 : S.nreg (r + 48) = t) (e54 : S.nreg (r + 54) = gB) (e59 : S.nreg (r + 59) = FE + d * t)
    (m0 : S.mem W = 0) (ht : t < d) (hg : gB + d ≤ W) (hFs : W + 24 ≤ Fs) (hFE : Fs + d ≤ FE) :
    ∃ k S', k ≤ 7 * d + 11 ∧ Exec w (mvBody r) S k S' ∧
      S'.mem (Fs + t) = ∑ l ∈ Finset.range d, S.mem (FE + d * t + l) * S.mem (gB + l) ∧
      S'.mem (W + 19) = S.mem (W + 19) + S.mem (gB + t) * ∑ l ∈ Finset.range d, S.mem (FE + d * t + l) * S.mem (gB + l) ∧
      S'.nreg (r + 48) = t + 1 ∧ S'.nreg (r + 59) = FE + d * (t + 1) ∧
      Fr S S' (fun i => i = r + 48 ∨ i = r + 49 ∨ i = r + 51 ∨ i = r + 52 ∨ i = r + 59)
        (fun c => c = W + 13 ∨ c = W + 15 ∨ c = W + 19 ∨ c = Fs + t) := by
  -- the dot product `⟨E_t, g⟩` into `W + 13`
  obtain ⟨S1, ed, hacc, hfr1⟩ := dot_exec (w := w) (j := r + 49) (dv := r + 1) (one := r + 9) (pA := r + 59)
    (pB := r + 54) (tA := r + 51) (tB := r + 52) (acc := r + 34) (prod := r + 36) S
    (by omega) (by omega) (by omega) e9 (by rw [e34, e36]; omega)
    (fun k hk => by rw [e1] at hk; rw [e59, e34, e36]; omega)
    (fun k hk => by rw [e1] at hk; rw [e54, e34, e36]; omega)
  obtain ⟨hn1, hm1, hdr1, hro1, hpt1⟩ := hfr1
  rw [e1] at ed hacc
  rw [e34, e59, e54] at hacc
  rw [e34, e36] at hm1
  have r1 : ∀ k, k ≠ 49 → k ≠ 51 → k ≠ 52 → S1.nreg (r + k) = S.nreg (r + k) := fun k h1 h2 h3 =>
    hn1 _ (by omega)
  have f1 := (r1 1 (by omega) (by omega) (by omega)).trans e1
  have f6 := (r1 6 (by omega) (by omega) (by omega)).trans e6
  have f9 := (r1 9 (by omega) (by omega) (by omega)).trans e9
  have f21 := (r1 21 (by omega) (by omega) (by omega)).trans e21
  have f34 := (r1 34 (by omega) (by omega) (by omega)).trans e34
  have f36 := (r1 36 (by omega) (by omega) (by omega)).trans e36
  have f40 := (r1 40 (by omega) (by omega) (by omega)).trans e40
  have f48 := (r1 48 (by omega) (by omega) (by omega)).trans e48
  have f54 := (r1 54 (by omega) (by omega) (by omega)).trans e54
  have f59 := (r1 59 (by omega) (by omega) (by omega)).trans e59
  obtain ⟨y1, y19, y48, y59, yn, ym, ydr, yro, ypt⟩ := mvBody_exec_aux1 (w := w) S1 f1 f6 f9 f21 f34 f36 f40 f48 f54
    f59 (by omega) hFs
  have ep := exec_prims w [Prim.nadd (r + 51) (r + 6) (r + 48), .op2 .add (r + 51) (r + 34) (r + 21),
      .nadd (r + 52) (r + 54) (r + 48), .op2 .mul (r + 36) (r + 52) (r + 34), .op2 .add (r + 40) (r + 40) (r + 36),
      .nadd (r + 59) (r + 59) (r + 1), .nadd (r + 48) (r + 48) (r + 9)] S1
  have g0 : S1.mem W = 0 := (hm1 W (by omega)).trans m0
  have g19 : S1.mem (W + 19) = S.mem (W + 19) := hm1 _ (by omega)
  have ggt : S1.mem (gB + t) = S.mem (gB + t) := hm1 _ (by omega)
  refine ⟨7 * d + 11, _, le_rfl, (Exec.seq ed ep).cost (by simp), ?_, ?_, y48, ?_,
    ⟨fun i hi => ?_, fun c hc => ?_, ydr.trans hdr1, yro.trans hro1, ypt.trans hpt1⟩⟩
  · rw [y1, hacc, g0, add_zero]
  · rw [y19, hacc, g19, ggt]
  · rw [y59]; ring
  · simp only [not_or] at hi
    obtain ⟨h1, h2, h3, h4, h5⟩ := hi
    rw [yn i h1 h3 h4 h5]
    exact hn1 i (by omega)
  · simp only [not_or] at hc
    obtain ⟨h1, h2, h3, h4⟩ := hc
    rw [ym c h2 h3 h4]
    exact hm1 c (by omega)

/-- The loop of `v = E g`: every row of `v`, and `γ = ⟨g, v⟩` from `γ = 0`. -/
theorem mvLoop_exec {w : World d} {r W Fs FE gB : ℕ} {S : State d}
    (e1 : S.nreg (r + 1) = d) (e6 : S.nreg (r + 6) = Fs) (e9 : S.nreg (r + 9) = 1) (e21 : S.nreg (r + 21) = W)
    (e34 : S.nreg (r + 34) = W + 13) (e36 : S.nreg (r + 36) = W + 15) (e40 : S.nreg (r + 40) = W + 19)
    (e48 : S.nreg (r + 48) = 0) (e54 : S.nreg (r + 54) = gB) (e59 : S.nreg (r + 59) = FE)
    (m0 : S.mem W = 0) (m19 : S.mem (W + 19) = 0) (hg : gB + d ≤ W) (hFs : W + 24 ≤ Fs) (hFE : Fs + d ≤ FE) :
    ∃ k S', k ≤ d * (7 * d + 13) + 2 ∧ Exec w (.whileN (r + 48) (r + 1) (mvBody r)) S k S' ∧
      (∀ t < d, S'.mem (Fs + t) = ∑ l ∈ Finset.range d, S.mem (FE + d * t + l) * S.mem (gB + l)) ∧
      S'.mem (W + 19) =
        ∑ t ∈ Finset.range d, S.mem (gB + t) * ∑ l ∈ Finset.range d, S.mem (FE + d * t + l) * S.mem (gB + l) ∧
      Fr S S' (fun i => (r + 48 ≤ i ∧ i ≤ r + 52) ∨ i = r + 59)
        (fun c => c = W + 13 ∨ c = W + 15 ∨ c = W + 19 ∨ (Fs ≤ c ∧ c < Fs + d)) := by
  set P : ℕ → State d → Prop := fun t S' => S'.nreg (r + 48) = t ∧ S'.nreg (r + 1) = d ∧
      S'.nreg (r + 59) = FE + d * t ∧
      (∀ u < t, S'.mem (Fs + u) = ∑ l ∈ Finset.range d, S.mem (FE + d * u + l) * S.mem (gB + l)) ∧
      S'.mem (W + 19) =
        ∑ u ∈ Finset.range t, S.mem (gB + u) * ∑ l ∈ Finset.range d, S.mem (FE + d * u + l) * S.mem (gB + l) ∧
      Fr S S' (fun i => (r + 48 ≤ i ∧ i ≤ r + 52) ∨ i = r + 59)
        (fun c => c = W + 13 ∨ c = W + 15 ∨ c = W + 19 ∨ (Fs ≤ c ∧ c < Fs + d)) with hP
  have hbody : ∀ t S1, t < d → P t S1 → ∃ k S2, k ≤ 7 * d + 11 ∧ Exec w (mvBody r) S1 k S2 ∧ P (t + 1) S2 := by
    rintro t S1 ht ⟨h48, h1, h59, hv, h19, hfr⟩
    obtain ⟨hn, hm, hdr, hro, hpt⟩ := hfr
    have g : ∀ j, j < 48 → S1.nreg (r + j) = S.nreg (r + j) := fun j hj => hn _ (by omega)
    have g54 : S1.nreg (r + 54) = S.nreg (r + 54) := hn _ (by omega)
    have gE : ∀ l < d, S1.mem (FE + d * t + l) = S.mem (FE + d * t + l) := fun l _ => hm _ (by omega)
    have gg : ∀ l < d, S1.mem (gB + l) = S.mem (gB + l) := fun l hl => hm _ (by omega)
    obtain ⟨k1, S2, hk1, x1, y1, y19, y48, y59, yfr⟩ := mvBody_exec (w := w) (r := r) (W := W) (Fs := Fs)
      (FE := FE) (gB := gB) (t := t) (S := S1) h1 ((g 6 (by omega)).trans e6) ((g 9 (by omega)).trans e9)
      ((g 21 (by omega)).trans e21) ((g 34 (by omega)).trans e34) ((g 36 (by omega)).trans e36)
      ((g 40 (by omega)).trans e40) h48 (g54.trans e54) h59 ((hm W (by omega)).trans m0) ht hg hFs hFE
    obtain ⟨hn2, hm2, hdr2, hro2, hpt2⟩ := yfr
    have hsum : ∑ l ∈ Finset.range d, S1.mem (FE + d * t + l) * S1.mem (gB + l) =
        ∑ l ∈ Finset.range d, S.mem (FE + d * t + l) * S.mem (gB + l) :=
      Finset.sum_congr rfl fun l hl => by rw [gE l (Finset.mem_range.1 hl), gg l (Finset.mem_range.1 hl)]
    refine ⟨k1, S2, hk1, x1, y48, ?_, y59, fun u hu => ?_, ?_,
      ⟨fun i hi => ?_, fun c hc => ?_, hdr2.trans hdr, hro2.trans hro, hpt2.trans hpt⟩⟩
    · rw [hn2 _ (by omega)]; exact h1
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu' | rfl
      · rw [hm2 _ (by omega)]; exact hv u hu'
      · rw [y1, hsum]
    · rw [y19, hsum, h19, gg t ht, Finset.sum_range_succ]
    · rw [hn2 i (by omega)]; exact hn i hi
    · simp only [not_or, not_and, not_lt] at hc
      rw [hm2 c (by omega)]
      exact hm c (by omega)
  obtain ⟨k, S', hk, x, -, -, -, hv, h19, hfr⟩ := exec_for (w := w) (a := r + 48) (b := r + 1) (c := mvBody r) d
    (7 * d + 11) P (fun t S' h => ⟨h.1, h.2.1⟩) hbody S
    ⟨e48, e1, by rw [e59, Nat.mul_zero, Nat.add_zero], fun u hu => absurd hu (Nat.not_lt_zero _),
      by rw [m19, Finset.sum_range_zero], Fr.refl _ _ _⟩
  exact ⟨k, S', by rw [show 7 * d + 13 = 7 * d + 11 + 2 by ring]; exact hk, x, hv, h19, hfr⟩

/-! ## `b = v / √γ` and `a' = a - b/(d + 1)` -/

/-- One coordinate: `b_t = inv * v_t` in place of `v_t`, and `a_t -= c b_t`, with `inv` at `W + 20` and `c` at
`W + 8`. -/
theorem baBody_exec {w : World d} {r W Fa Fs t : ℕ} {S : State d}
    (e5 : S.nreg (r + 5) = Fa) (e6 : S.nreg (r + 6) = Fs) (e9 : S.nreg (r + 9) = 1) (e29 : S.nreg (r + 29) = W + 8)
    (e41 : S.nreg (r + 41) = W + 20) (e42 : S.nreg (r + 42) = W + 21) (e48 : S.nreg (r + 48) = t)
    (ht : t < d) (hFa : W + 24 ≤ Fa) (hFs : Fa + d ≤ Fs) :
    ∃ k S', k ≤ 6 ∧ Exec w (baBody r) S k S' ∧
      S'.mem (Fs + t) = S.mem (W + 20) * S.mem (Fs + t) ∧
      S'.mem (Fa + t) = S.mem (Fa + t) - S.mem (W + 8) * (S.mem (W + 20) * S.mem (Fs + t)) ∧
      S'.nreg (r + 48) = t + 1 ∧
      Fr S S' (fun i => i = r + 48 ∨ i = r + 51 ∨ i = r + 52) (fun c => c = W + 21 ∨ c = Fs + t ∨ c = Fa + t) := by
  have a1 : Fs + t ≠ W + 21 := by omega
  have a2 : Fa + t ≠ W + 21 := by omega
  have a3 : Fa + t ≠ Fs + t := by omega
  have a4 : W + 8 ≠ Fs + t := by omega
  have a5 : W + 20 ≠ Fs + t := by omega
  have a6 : W + 21 ≠ Fs + t := by omega
  have a7 : Fs + t ≠ Fa + t := by omega
  have a8 : W + 21 ≠ Fa + t := by omega
  have b1 : Fs ≠ Fa := by omega
  have b2 : Fa ≠ Fs := by omega
  refine ⟨6, _, le_rfl, exec_prims w [.nadd (r + 51) (r + 6) (r + 48), .op2 .mul (r + 51) (r + 41) (r + 51),
    .nadd (r + 52) (r + 5) (r + 48), .op2 .mul (r + 42) (r + 29) (r + 51), .op2 .sub (r + 52) (r + 52) (r + 42),
    .nadd (r + 48) (r + 48) (r + 9)] S, ?_, ?_, ?_, ⟨fun i hi => ?_, fun c hc => ?_, ?_, ?_, ?_⟩⟩
  · simp [List.foldl, Prim.exec, e5, e6, e9, e29, e41, e42, e48, a1, a2, a4, b1, b2, Op2.eval]
  · simp [List.foldl, Prim.exec, e5, e6, e9, e29, e41, e42, e48, a2, a4, b2, Op2.eval]
  · simp [List.foldl, Prim.exec, Function.update_apply, e48, e9]
  · simp only [not_or] at hi
    simp [List.foldl, Prim.exec, Function.update_apply, hi.1, hi.2.1, hi.2.2]
  · simp only [not_or] at hc
    simp [List.foldl, Prim.exec, Function.update_apply, e5, e6, e29, e41, e42, e48, hc.1, hc.2.1, hc.2.2]
  · simp [List.foldl, Prim.exec]
  · simp [List.foldl, Prim.exec]
  · simp [List.foldl, Prim.exec]

/-- The loop of `b` and `a'`. -/
theorem baLoop_exec {w : World d} {r W Fa Fs : ℕ} {S : State d}
    (e1 : S.nreg (r + 1) = d) (e5 : S.nreg (r + 5) = Fa) (e6 : S.nreg (r + 6) = Fs) (e9 : S.nreg (r + 9) = 1)
    (e29 : S.nreg (r + 29) = W + 8) (e41 : S.nreg (r + 41) = W + 20) (e42 : S.nreg (r + 42) = W + 21)
    (e48 : S.nreg (r + 48) = 0) (hFa : W + 24 ≤ Fa) (hFs : Fa + d ≤ Fs) :
    ∃ k S', k ≤ d * 8 + 2 ∧ Exec w (.whileN (r + 48) (r + 1) (baBody r)) S k S' ∧
      (∀ t < d, S'.mem (Fs + t) = S.mem (W + 20) * S.mem (Fs + t)) ∧
      (∀ t < d, S'.mem (Fa + t) = S.mem (Fa + t) - S.mem (W + 8) * (S.mem (W + 20) * S.mem (Fs + t))) ∧
      Fr S S' (fun i => i = r + 48 ∨ i = r + 51 ∨ i = r + 52) (fun c => c = W + 21 ∨ (Fa ≤ c ∧ c < Fs + d)) := by
  set P : ℕ → State d → Prop := fun t S' => S'.nreg (r + 48) = t ∧ S'.nreg (r + 1) = d ∧
      (∀ u < t, S'.mem (Fs + u) = S.mem (W + 20) * S.mem (Fs + u)) ∧
      (∀ u < t, S'.mem (Fa + u) = S.mem (Fa + u) - S.mem (W + 8) * (S.mem (W + 20) * S.mem (Fs + u))) ∧
      (∀ u, t ≤ u → u < d → S'.mem (Fs + u) = S.mem (Fs + u) ∧ S'.mem (Fa + u) = S.mem (Fa + u)) ∧
      Fr S S' (fun i => i = r + 48 ∨ i = r + 51 ∨ i = r + 52) (fun c => c = W + 21 ∨ (Fa ≤ c ∧ c < Fs + d)) with hP
  have hbody : ∀ t S1, t < d → P t S1 → ∃ k S2, k ≤ 6 ∧ Exec w (baBody r) S1 k S2 ∧ P (t + 1) S2 := by
    rintro t S1 ht ⟨h48, h1, hv, ha, hrest, hfr⟩
    obtain ⟨hn, hm, hdr, hro, hpt⟩ := hfr
    have g : ∀ j, j ≠ 48 → j ≠ 51 → j ≠ 52 → S1.nreg (r + j) = S.nreg (r + j) := fun j h1 h2 h3 =>
      hn _ (by omega)
    have g20 : S1.mem (W + 20) = S.mem (W + 20) := hm _ (by omega)
    have g8 : S1.mem (W + 8) = S.mem (W + 8) := hm _ (by omega)
    obtain ⟨hFs0, hFa0⟩ := hrest t le_rfl ht
    obtain ⟨k1, S2, hk1, x1, y1, y2, y48, yfr⟩ := baBody_exec (w := w) (r := r) (W := W) (Fa := Fa) (Fs := Fs)
      (t := t) (S := S1) ((g 5 (by omega) (by omega) (by omega)).trans e5)
      ((g 6 (by omega) (by omega) (by omega)).trans e6)
      ((g 9 (by omega) (by omega) (by omega)).trans e9) ((g 29 (by omega) (by omega) (by omega)).trans e29)
      ((g 41 (by omega) (by omega) (by omega)).trans e41) ((g 42 (by omega) (by omega) (by omega)).trans e42) h48 ht
      hFa hFs
    obtain ⟨hn2, hm2, hdr2, hro2, hpt2⟩ := yfr
    refine ⟨k1, S2, hk1, x1, y48, ?_, fun u hu => ?_, fun u hu => ?_, fun u hu1 hu2 => ?_,
      ⟨fun i hi => ?_, fun c hc => ?_, hdr2.trans hdr, hro2.trans hro, hpt2.trans hpt⟩⟩
    · rw [hn2 _ (by omega)]; exact h1
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu' | rfl
      · rw [hm2 _ (by omega)]; exact hv u hu'
      · rw [y1, g20, hFs0]
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu' | rfl
      · rw [hm2 _ (by omega)]; exact ha u hu'
      · rw [y2, g20, g8, hFs0, hFa0]
    · obtain ⟨b1, b2⟩ := hrest u (by omega) hu2
      exact ⟨(hm2 _ (by omega)).trans b1, (hm2 _ (by omega)).trans b2⟩
    · rw [hn2 i hi]; exact hn i hi
    · simp only [not_or, not_and, not_lt] at hc
      rw [hm2 c (by omega)]
      exact hm c (by omega)
  obtain ⟨k, S', hk, x, -, -, hv, ha, -, hfr⟩ := exec_for (w := w) (a := r + 48) (b := r + 1) (c := baBody r) d 6 P
    (fun t S' h => ⟨h.1, h.2.1⟩) hbody S
    ⟨e48, e1, fun u hu => absurd hu (Nat.not_lt_zero _), fun u hu => absurd hu (Nat.not_lt_zero _),
      fun u _ _ => ⟨rfl, rfl⟩, Fr.refl _ _ _⟩
  exact ⟨k, S', by omega, x, hv, ha, hfr⟩

/-! ## The rank-one update `E' = c₁ (E - c₂ b bᵀ)` -/

/-- One entry: `E_tu := c₁ (E_tu - c₂ b_t b_u)`, with `c₁` at `W + 6` and `c₂` at `W + 7`. -/
theorem r1Inner_exec {w : World d} {r W Fs FE t u : ℕ} {S : State d}
    (e6 : S.nreg (r + 6) = Fs) (e9 : S.nreg (r + 9) = 1) (e27 : S.nreg (r + 27) = W + 6)
    (e28 : S.nreg (r + 28) = W + 7) (e42 : S.nreg (r + 42) = W + 21) (e43 : S.nreg (r + 43) = W + 22)
    (e49 : S.nreg (r + 49) = u) (e51 : S.nreg (r + 51) = Fs + t) (e59 : S.nreg (r + 59) = FE + d * t)
    (ht : t < d) (hu : u < d) (hFs : W + 24 ≤ Fs) (hFE : Fs + d ≤ FE) :
    ∃ k S', k ≤ 7 ∧ Exec w (r1Inner r) S k S' ∧
      S'.mem (FE + d * t + u) =
        S.mem (W + 6) * (S.mem (FE + d * t + u) - S.mem (W + 7) * (S.mem (Fs + t) * S.mem (Fs + u))) ∧
      S'.nreg (r + 49) = u + 1 ∧
      Fr S S' (fun i => i = r + 49 ∨ i = r + 52 ∨ i = r + 61)
        (fun c => c = W + 21 ∨ c = W + 22 ∨ c = FE + d * t + u) := by
  have h_r1Inner : r1Inner r = prims [
    Prim.nadd (r + 52) (r + 6) (r + 49),
    Prim.nadd (r + 61) (r + 59) (r + 49),
    Prim.op2 Op2.mul (r + 42) (r + 51) (r + 52),
    Prim.op2 Op2.mul (r + 42) (r + 28) (r + 42),
    Prim.op2 Op2.sub (r + 43) (r + 61) (r + 42),
    Prim.op2 Op2.mul (r + 61) (r + 27) (r + 43),
    Prim.nadd (r + 49) (r + 49) (r + 9)] := by
    unfold r1Inner prims
    rfl
  rw [h_r1Inner]
  have h_exec := exec_prims w [
    Prim.nadd (r + 52) (r + 6) (r + 49),
    Prim.nadd (r + 61) (r + 59) (r + 49),
    Prim.op2 Op2.mul (r + 42) (r + 51) (r + 52),
    Prim.op2 Op2.mul (r + 42) (r + 28) (r + 42),
    Prim.op2 Op2.sub (r + 43) (r + 61) (r + 42),
    Prim.op2 Op2.mul (r + 61) (r + 27) (r + 43),
    Prim.nadd (r + 49) (r + 49) (r + 9)] S
  let S' := [
    Prim.nadd (r + 52) (r + 6) (r + 49),
    Prim.nadd (r + 61) (r + 59) (r + 49),
    Prim.op2 Op2.mul (r + 42) (r + 51) (r + 52),
    Prim.op2 Op2.mul (r + 42) (r + 28) (r + 42),
    Prim.op2 Op2.sub (r + 43) (r + 61) (r + 42),
    Prim.op2 Op2.mul (r + 61) (r + 27) (r + 43),
    Prim.nadd (r + 49) (r + 49) (r + 9)].foldl (fun s p => Prim.exec w s p) S
  have h_exec' : Exec w (prims [
    Prim.nadd (r + 52) (r + 6) (r + 49),
    Prim.nadd (r + 61) (r + 59) (r + 49),
    Prim.op2 Op2.mul (r + 42) (r + 51) (r + 52),
    Prim.op2 Op2.mul (r + 42) (r + 28) (r + 42),
    Prim.op2 Op2.sub (r + 43) (r + 61) (r + 42),
    Prim.op2 Op2.mul (r + 61) (r + 27) (r + 43),
    Prim.nadd (r + 49) (r + 49) (r + 9)]) S 7 S' := by
    simpa [S'] using h_exec
  have hneq1 : FE + d * t + u ≠ W + 21 := by omega
  have hneq2 : FE + d * t + u ≠ W + 22 := by omega
  have h_mem : S'.mem (FE + d * t + u) = S.mem (W + 6) * (S.mem (FE + d * t + u) - S.mem (W + 7) * (S.mem (Fs + t) * S.mem (Fs + u))) := by
    dsimp [S']
    simp [List.foldl, Prim.exec, Function.update_apply, Op2.eval, e6, e9, e27, e28, e42, e43, e49, e51, e59, hneq1, hneq2]
  have h_nreg : S'.nreg (r + 49) = u + 1 := by
    dsimp [S']
    simp [List.foldl, Prim.exec, Function.update_apply, e6, e9, e27, e28, e42, e43, e49, e51, e59]
  have h_frame : Fr S S' (fun i => i = r + 49 ∨ i = r + 52 ∨ i = r + 61) (fun c => c = W + 21 ∨ c = W + 22 ∨ c = FE + d * t + u) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      have hi' : ¬ (i = r + 49 ∨ i = r + 52 ∨ i = r + 61) := hi
      dsimp [S']
      simp [List.foldl, Prim.exec, Function.update_apply, e6, e9, e27, e28, e42, e43, e49, e51, e59]
      by_cases hi49 : i = r + 49
      · exfalso; exact hi' (Or.inl hi49)
      · by_cases hi52 : i = r + 52
        · exfalso; exact hi' (Or.inr (Or.inl hi52))
        · by_cases hi61 : i = r + 61
          · exfalso; exact hi' (Or.inr (Or.inr hi61))
          · simp [hi49, hi52, hi61]
    · intro c hc
      have hc' : ¬ (c = W + 21 ∨ c = W + 22 ∨ c = FE + d * t + u) := hc
      dsimp [S']
      simp [List.foldl, Prim.exec, Function.update_apply, Op2.eval, e6, e9, e27, e28, e42, e43, e49, e51, e59, hneq1, hneq2]
      by_cases hc21 : c = W + 21
      · exfalso; exact hc' (Or.inl hc21)
      · by_cases hc22 : c = W + 22
        · exfalso; exact hc' (Or.inr (Or.inl hc22))
        · by_cases hcFE : c = FE + d * t + u
          · exfalso; exact hc' (Or.inr (Or.inr hcFE))
          · simp [hc21, hc22, hcFE]
    · dsimp [S']; simp [List.foldl, Prim.exec]
    · dsimp [S']; simp [List.foldl, Prim.exec]
    · dsimp [S']; simp [List.foldl, Prim.exec]
  refine ⟨7, S', by omega, h_exec', h_mem, h_nreg, h_frame⟩

/-- One row of the rank-one update. -/
theorem r1Outer_exec {w : World d} {r W Fs FE t : ℕ} {S : State d}
    (e1 : S.nreg (r + 1) = d) (e6 : S.nreg (r + 6) = Fs) (e9 : S.nreg (r + 9) = 1) (e27 : S.nreg (r + 27) = W + 6)
    (e28 : S.nreg (r + 28) = W + 7) (e42 : S.nreg (r + 42) = W + 21) (e43 : S.nreg (r + 43) = W + 22)
    (e48 : S.nreg (r + 48) = t) (e59 : S.nreg (r + 59) = FE + d * t)
    (ht : t < d) (hFs : W + 24 ≤ Fs) (hFE : Fs + d ≤ FE) :
    ∃ k S', k ≤ 9 * d + 6 ∧ Exec w (r1Outer r) S k S' ∧
      (∀ u < d, S'.mem (FE + d * t + u) =
        S.mem (W + 6) * (S.mem (FE + d * t + u) - S.mem (W + 7) * (S.mem (Fs + t) * S.mem (Fs + u)))) ∧
      S'.nreg (r + 48) = t + 1 ∧ S'.nreg (r + 59) = FE + d * (t + 1) ∧
      Fr S S' (fun i => (r + 48 ≤ i ∧ i ≤ r + 52) ∨ i = r + 59 ∨ i = r + 61)
        (fun c => c = W + 21 ∨ c = W + 22 ∨ (FE + d * t ≤ c ∧ c < FE + d * t + d)) := by
  obtain ⟨S0, hS0⟩ : ∃ S0, S0 = [Prim.nadd (r + 51) (r + 6) (r + 48), .nconst (r + 49) 0].foldl
      (fun s p => p.exec w s) S := ⟨_, rfl⟩
  have x0 := exec_prims w [Prim.nadd (r + 51) (r + 6) (r + 48), .nconst (r + 49) 0] S
  rw [← hS0] at x0
  have n0 : ∀ x, S0.nreg x = if x = r + 49 then 0 else if x = r + 51 then Fs + t else S.nreg x := fun x => by
    subst hS0; simp only [List.foldl, Prim.exec, Function.update_apply, e6, e48]
  have m0 : S0.mem = S.mem := by subst hS0; rfl
  have d0 : S0.draws = S.draws ∧ S0.rounds = S.rounds ∧ S0.pts = S.pts := by subst hS0; exact ⟨rfl, rfl, rfl⟩
  have q0 : ∀ x, x ≠ r + 49 → x ≠ r + 51 → S0.nreg x = S.nreg x := fun x a b => by rw [n0, if_neg a, if_neg b]
  -- the inner loop over the columns
  let RI : ℕ → Prop := fun i => i = r + 49 ∨ i = r + 52 ∨ i = r + 61
  let CI : ℕ → Prop := fun c => c = W + 21 ∨ c = W + 22 ∨ (FE + d * t ≤ c ∧ c < FE + d * t + d)
  let new : ℕ → ℝ := fun u =>
    S.mem (W + 6) * (S.mem (FE + d * t + u) - S.mem (W + 7) * (S.mem (Fs + t) * S.mem (Fs + u)))
  let P : ℕ → State d → Prop := fun u T => T.nreg (r + 49) = u ∧ Fr S0 T RI CI ∧
    ∀ v < d, T.mem (FE + d * t + v) = if v < u then new v else S.mem (FE + d * t + v)
  have hab : ∀ u T, P u T → T.nreg (r + 49) = u ∧ T.nreg (r + 1) = d := fun u T hP =>
    ⟨hP.1, (hP.2.1.1 _ (by simp only [RI]; omega)).trans ((q0 _ (by omega) (by omega)).trans e1)⟩
  have hbody : ∀ u T, u < d → P u T → ∃ k T', k ≤ 7 ∧ Exec w (r1Inner r) T k T' ∧ P (u + 1) T' := by
    rintro u T hu ⟨h49, f, hv⟩
    have g : ∀ x, ¬ RI x → T.nreg x = S0.nreg x := fun x h => f.1 x h
    have nR : ∀ x, x ≠ r + 49 → x ≠ r + 52 → x ≠ r + 61 → ¬ RI x := fun x a b c h => by
      rcases h with h | h | h <;> contradiction
    have mc : ∀ c, c ≠ W + 21 → c ≠ W + 22 → (c < FE + d * t ∨ FE + d * t + d ≤ c) → T.mem c = S.mem c :=
      fun c a b h => (f.2.1 c (fun h' => by rcases h' with h' | h' | h' <;> omega)).trans (by rw [m0])
    obtain ⟨k, T', hk, x, hval, h49', f'⟩ := r1Inner_exec (w := w) (r := r) (W := W) (Fs := Fs) (FE := FE) (t := t)
      (u := u) (S := T)
      ((g _ (nR _ (by omega) (by omega) (by omega))).trans ((q0 _ (by omega) (by omega)).trans e6))
      ((g _ (nR _ (by omega) (by omega) (by omega))).trans ((q0 _ (by omega) (by omega)).trans e9))
      ((g _ (nR _ (by omega) (by omega) (by omega))).trans ((q0 _ (by omega) (by omega)).trans e27))
      ((g _ (nR _ (by omega) (by omega) (by omega))).trans ((q0 _ (by omega) (by omega)).trans e28))
      ((g _ (nR _ (by omega) (by omega) (by omega))).trans ((q0 _ (by omega) (by omega)).trans e42))
      ((g _ (nR _ (by omega) (by omega) (by omega))).trans ((q0 _ (by omega) (by omega)).trans e43))
      h49 ((g _ (nR _ (by omega) (by omega) (by omega))).trans (by rw [n0]; simp))
      ((g _ (nR _ (by omega) (by omega) (by omega))).trans ((q0 _ (by omega) (by omega)).trans e59))
      ht hu hFs hFE
    refine ⟨k, T', hk, x, h49', f.trans (f'.mono (fun i hi => hi) (fun c hc => ?_)), fun v hv' => ?_⟩
    · rcases hc with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    · by_cases hvu : v = u
      · subst hvu
        have a1 : T.mem (W + 6) = S.mem (W + 6) := mc _ (by omega) (by omega) (by omega)
        have a2 : T.mem (W + 7) = S.mem (W + 7) := mc _ (by omega) (by omega) (by omega)
        have a3 : T.mem (Fs + t) = S.mem (Fs + t) := mc _ (by omega) (by omega) (by omega)
        have a4 : T.mem (Fs + v) = S.mem (Fs + v) := mc _ (by omega) (by omega) (by omega)
        have a5 : T.mem (FE + d * t + v) = S.mem (FE + d * t + v) := by rw [hv v hv', if_neg (lt_irrefl v)]
        rw [hval, if_pos (Nat.lt_succ_self v), a1, a2, a3, a4, a5]
      · rw [f'.2.1 _ (fun h' => by rcases h' with h' | h' | h' <;> omega), hv v hv']
        by_cases hlt : v < u
        · rw [if_pos hlt, if_pos (by omega)]
        · rw [if_neg hlt, if_neg (by omega)]
  have hP0 : P 0 S0 := ⟨by rw [n0, if_pos rfl], Fr.refl _ _ _, fun v _ => by
    rw [if_neg (Nat.not_lt_zero v), m0]⟩
  obtain ⟨kL, S1, hkL, xL, ⟨-, f1, hv1⟩⟩ := exec_for (w := w) (a := r + 49) (b := r + 1) (c := r1Inner r) d 7 P
    hab hbody S0 hP0
  -- the last two primitives
  have g1 : ∀ x, ¬ RI x → S1.nreg x = S0.nreg x := fun x h => f1.1 x h
  have k59 : S1.nreg (r + 59) = FE + d * t :=
    (g1 _ (by simp only [RI]; omega)).trans ((q0 _ (by omega) (by omega)).trans e59)
  have k48 : S1.nreg (r + 48) = t := (g1 _ (by simp only [RI]; omega)).trans ((q0 _ (by omega) (by omega)).trans e48)
  have k1 : S1.nreg (r + 1) = d := (g1 _ (by simp only [RI]; omega)).trans ((q0 _ (by omega) (by omega)).trans e1)
  have k9 : S1.nreg (r + 9) = 1 := (g1 _ (by simp only [RI]; omega)).trans ((q0 _ (by omega) (by omega)).trans e9)
  obtain ⟨S2, hS2⟩ : ∃ S2, S2 = [Prim.nadd (r + 59) (r + 59) (r + 1), .nadd (r + 48) (r + 48) (r + 9)].foldl
      (fun s p => p.exec w s) S1 := ⟨_, rfl⟩
  have x2 := exec_prims w [Prim.nadd (r + 59) (r + 59) (r + 1), .nadd (r + 48) (r + 48) (r + 9)] S1
  rw [← hS2] at x2
  have n2 : ∀ x, S2.nreg x = if x = r + 48 then t + 1 else if x = r + 59 then FE + d * t + d else S1.nreg x :=
    fun x => by
      subst hS2
      simp only [List.foldl, Prim.exec, Function.update_apply, k59, k48, k1, k9, show r + 48 ≠ r + 59 by omega,
        show r + 9 ≠ r + 59 by omega, ↓reduceIte]
  have m2 : S2.mem = S1.mem := by subst hS2; rfl
  have d2 : S2.draws = S1.draws ∧ S2.rounds = S1.rounds ∧ S2.pts = S1.pts := by subst hS2; exact ⟨rfl, rfl, rfl⟩
  refine ⟨_, S2, ?_, Exec.seq x0 (Exec.seq xL x2), fun u hu => ?_, by rw [n2, if_pos rfl],
    by rw [n2, if_neg (by omega), if_pos rfl]; ring, ?_⟩
  · simp only [List.length_cons, List.length_nil]; nlinarith
  · rw [m2, hv1 u hu, if_pos hu]
  · refine Fr.trans ⟨fun x hx => ?_, fun c _ => by rw [m0], d0.1, d0.2.1, d0.2.2⟩
      (Fr.trans (f1.mono (fun i hi => ?_) (fun c hc => hc)) ⟨fun x hx => ?_, fun c _ => by rw [m2], d2.1, d2.2.1, d2.2.2⟩)
    · rw [q0 x (fun h => hx (Or.inl ⟨by omega, by omega⟩)) (fun h => hx (Or.inl ⟨by omega, by omega⟩))]
    · rcases hi with h | h | h
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr (Or.inr h)
    · rw [n2, if_neg (fun h => hx (Or.inl ⟨by omega, by omega⟩)), if_neg (fun h => hx (Or.inr (Or.inl h)))]

/-- The rank-one update over every row. -/
theorem r1Loop_exec {w : World d} {r W Fs FE : ℕ} {S : State d}
    (e1 : S.nreg (r + 1) = d) (e6 : S.nreg (r + 6) = Fs) (e9 : S.nreg (r + 9) = 1) (e27 : S.nreg (r + 27) = W + 6)
    (e28 : S.nreg (r + 28) = W + 7) (e42 : S.nreg (r + 42) = W + 21) (e43 : S.nreg (r + 43) = W + 22)
    (e48 : S.nreg (r + 48) = 0) (e59 : S.nreg (r + 59) = FE) (hFs : W + 24 ≤ Fs) (hFE : Fs + d ≤ FE) :
    ∃ k S', k ≤ d * (9 * d + 8) + 2 ∧ Exec w (.whileN (r + 48) (r + 1) (r1Outer r)) S k S' ∧
      (∀ t < d, ∀ u < d, S'.mem (FE + d * t + u) =
        S.mem (W + 6) * (S.mem (FE + d * t + u) - S.mem (W + 7) * (S.mem (Fs + t) * S.mem (Fs + u)))) ∧
      Fr S S' (fun i => (r + 48 ≤ i ∧ i ≤ r + 52) ∨ i = r + 59 ∨ i = r + 61)
        (fun c => c = W + 21 ∨ c = W + 22 ∨ (FE ≤ c ∧ c < FE + d * d)) := by
  -- the rows `k ≠ t` lie outside the row `t`
  have hlo : ∀ k t u, k < t → u < d → d * k + u < d * t := fun k t u hk hu => by
    have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hk)
    rw [Nat.mul_succ] at this
    omega
  have hhi : ∀ k t, t < k → d * t + d ≤ d * k := fun k t hk => by
    have := Nat.mul_le_mul_left d (Nat.succ_le_of_lt hk)
    rwa [Nat.mul_succ] at this
  have hend : ∀ t, t < d → d * t + d ≤ d * d := fun t ht => hhi d t ht
  set P : ℕ → State d → Prop := fun t T => T.nreg (r + 48) = t ∧ T.nreg (r + 1) = d ∧
      T.nreg (r + 59) = FE + d * t ∧
      (∀ k < d, ∀ u < d, T.mem (FE + d * k + u) = if k < t then
        S.mem (W + 6) * (S.mem (FE + d * k + u) - S.mem (W + 7) * (S.mem (Fs + k) * S.mem (Fs + u)))
        else S.mem (FE + d * k + u)) ∧
      Fr S T (fun i => (r + 48 ≤ i ∧ i ≤ r + 52) ∨ i = r + 59 ∨ i = r + 61)
        (fun c => c = W + 21 ∨ c = W + 22 ∨ (FE ≤ c ∧ c < FE + d * d)) with hP
  have hbody : ∀ t T, t < d → P t T → ∃ k T', k ≤ 9 * d + 6 ∧ Exec w (r1Outer r) T k T' ∧ P (t + 1) T' := by
    rintro t T ht ⟨h48, h1, h59, hrows, hfr⟩
    obtain ⟨hn, hm, hdr, hro, hpt⟩ := hfr
    have g : ∀ j, j < 48 → T.nreg (r + j) = S.nreg (r + j) := fun j hj => hn _ (by omega)
    obtain ⟨k1, T', hk1, x1, yrow, y48, y59, yfr⟩ := r1Outer_exec (w := w) (r := r) (W := W) (Fs := Fs) (FE := FE)
      (t := t) (S := T) h1 ((g 6 (by omega)).trans e6) ((g 9 (by omega)).trans e9) ((g 27 (by omega)).trans e27)
      ((g 28 (by omega)).trans e28) ((g 42 (by omega)).trans e42) ((g 43 (by omega)).trans e43) h48 h59 ht hFs hFE
    obtain ⟨hn2, hm2, hdr2, hro2, hpt2⟩ := yfr
    have m6 : T.mem (W + 6) = S.mem (W + 6) := hm _ (by omega)
    have m7 : T.mem (W + 7) = S.mem (W + 7) := hm _ (by omega)
    have mFs : ∀ u < d, T.mem (Fs + u) = S.mem (Fs + u) := fun u hu => hm _ (by omega)
    refine ⟨k1, T', hk1, x1, y48, ?_, y59, fun k hk u hu => ?_,
      ⟨fun i hi => ?_, fun c hc => ?_, hdr2.trans hdr, hro2.trans hro, hpt2.trans hpt⟩⟩
    · rw [hn2 _ (by omega)]; exact h1
    · rcases lt_trichotomy k t with hkt | rfl | hkt
      · have := hlo k t u hkt hu
        rw [hm2 _ (by omega), hrows k hk u hu, ite_eq_left hkt, ite_eq_left (by omega)]
      · rw [yrow u hu, hrows k hk u hu, ite_eq_right (lt_irrefl k), ite_eq_left (Nat.lt_succ_self k), m6, m7, mFs k hk,
          mFs u hu]
      · have := hhi k t hkt
        rw [hm2 _ (by omega), hrows k hk u hu, ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [hn2 i hi]; exact hn i hi
    · simp only [not_or, not_and, not_lt] at hc
      have := hend t ht
      rw [hm2 c (by omega)]
      exact hm c (by omega)
  obtain ⟨k, S', hk, x, -, -, -, hrows, hfr⟩ := exec_for (w := w) (a := r + 48) (b := r + 1) (c := r1Outer r) d
    (9 * d + 6) P (fun t T h => ⟨h.1, h.2.1⟩) hbody S
    ⟨e48, e1, by rw [e59, Nat.mul_zero, Nat.add_zero], fun k _ u _ => by rw [ite_eq_right (Nat.not_lt_zero k)],
      Fr.refl _ _ _⟩
  refine ⟨k, S', by rw [show 9 * d + 8 = 9 * d + 6 + 2 by ring]; exact hk, x, fun t ht u hu => ?_, hfr⟩
  rw [hrows t ht u hu, ite_eq_left ht]

end AdversarialBco.Conj1Poly
