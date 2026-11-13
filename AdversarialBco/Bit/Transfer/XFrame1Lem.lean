/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XFrameLem

@[expose] public section

/-!
# The scan of the read-off F2 (`d = 1`): one step by sign, the invariant

`f1step` by the sign of `α_t`, and what the scan of the first `t` rows holds: the index of a row with `α < 0` when
there is one, the index of a row with `α > 0` when there is one, and the bad-row flag.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Bit.RQ

theorem f1step_neg {al be : ℕ → ℤ} {st : Option ℕ × Option ℕ × Bool} {t : ℕ} (h : al t < 0) :
    f1step al be st t = ((match st.1 with
      | none => some t
      | some k => if be k * al t < be t * al k then some t else some k), st.2.1, st.2.2) := by
  obtain ⟨a, c, e⟩ := st
  cases a <;> simp [f1step, h, not_lt.2 h.le, h.ne]

theorem f1step_pos {al be : ℕ → ℤ} {st : Option ℕ × Option ℕ × Bool} {t : ℕ} (h : 0 < al t) :
    f1step al be st t = (st.1, (match st.2.1 with
      | none => some t
      | some k => if be t * al k < be k * al t then some t else some k), st.2.2) := by
  obtain ⟨a, c, e⟩ := st
  cases c <;> simp [f1step, h, not_lt.2 h.le, h.ne']

theorem f1step_zero {al be : ℕ → ℤ} {st : Option ℕ × Option ℕ × Bool} {t : ℕ} (h : al t = 0) :
    f1step al be st t = (st.1, st.2.1, st.2.2 || decide (be t < 0)) := by
  unfold f1step; simp [h]

theorem forall_lt_succ' {t : ℕ} (P : ℕ → Prop) : (∀ i < t + 1, P i) ↔ (∀ i < t, P i) ∧ P t :=
  ⟨fun h => ⟨fun i hi => h i (by omega), h t (by omega)⟩, fun ⟨h1, h2⟩ i hi => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · exact h1 i h
    · exact h ▸ h2⟩

theorem exists_lt_succ' {t : ℕ} (P : ℕ → Prop) : (∃ i < t + 1, P i) ↔ (∃ i < t, P i) ∨ P t :=
  ⟨fun ⟨i, hi, h⟩ => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | h'
    · exact Or.inl ⟨i, h', h⟩
    · exact Or.inr (h' ▸ h), fun h => h.elim (fun ⟨i, hi, h⟩ => ⟨i, by omega, h⟩) (fun h => ⟨t, by omega, h⟩)⟩

/-- **What the scan holds.** -/
theorem f1scan_spec (al be : ℕ → ℤ) (t : ℕ) :
    (∀ i, (f1scan al be t).1 = some i → i < t ∧ al i < 0) ∧ ((f1scan al be t).1 = none ↔ ∀ i < t, 0 ≤ al i) ∧
      (∀ k, (f1scan al be t).2.1 = some k → k < t ∧ 0 < al k) ∧
      ((f1scan al be t).2.1 = none ↔ ∀ i < t, al i ≤ 0) ∧
      ((f1scan al be t).2.2 = true ↔ ∃ i < t, al i = 0 ∧ be i < 0) := by
  induction t with
  | zero => simp [f1scan]
  | succ t ih =>
    obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ := ih
    rw [f1scan, forall_lt_succ', forall_lt_succ', exists_lt_succ']
    rcases lt_trichotomy (al t) 0 with h | h | h
    · have e2 : (f1step al be (f1scan al be t) t).2 = (f1scan al be t).2 := by
        simp [f1step, not_lt.2 h.le, h.ne]
      have e1 : ∀ i, (f1step al be (f1scan al be t) t).1 = some i → i = t ∨ (f1scan al be t).1 = some i := by
        intro i hi
        rcases hs : (f1scan al be t).1 with _ | k
        · simp [f1step, h, hs] at hi; exact Or.inl hi.symm
        · simp only [f1step, h, ↓reduceIte, hs] at hi
          split_ifs at hi
          · exact Or.inl (Option.some_inj.1 hi).symm
          · exact Or.inr hi
      have e1n : (f1step al be (f1scan al be t) t).1 ≠ none := by
        rcases hs : (f1scan al be t).1 with _ | k
        · simp [f1step, h, hs]
        · simp only [f1step, h, ↓reduceIte, hs]; split_ifs <;> simp
      rw [e2]
      refine ⟨fun i hi => ?_, ⟨fun hn => absurd hn e1n, fun hall => absurd hall.2 (by omega)⟩,
        fun k hk => ?_, ⟨fun hn => ⟨ih4.1 hn, h.le⟩, fun hall => ih4.2 hall.1⟩, ?_⟩
      · rcases e1 i hi with e | e
        · exact ⟨by omega, e ▸ h⟩
        · have := ih1 i e; exact ⟨by omega, this.2⟩
      · have := ih3 k hk; exact ⟨by omega, this.2⟩
      · rw [ih5]; simp only [h.ne, false_and, or_false]
    · rw [f1step_zero h]
      refine ⟨fun i hi => ?_, ⟨fun hn => ⟨ih2.1 hn, h.ge⟩, fun hall => ih2.2 hall.1⟩, fun k hk => ?_,
        ⟨fun hn => ⟨ih4.1 hn, h.le⟩, fun hall => ih4.2 hall.1⟩, ?_⟩
      · have := ih1 i hi; exact ⟨by omega, this.2⟩
      · have := ih3 k hk; exact ⟨by omega, this.2⟩
      · simp only [Bool.or_eq_true, decide_eq_true_eq, ih5, h, true_and]
    · have e1 : (f1step al be (f1scan al be t) t).1 = (f1scan al be t).1 := by
        simp [f1step, not_lt.2 h.le]
      have e3 : (f1step al be (f1scan al be t) t).2.2 = (f1scan al be t).2.2 := by
        simp [f1step, h.ne']
      have e2 : ∀ k, (f1step al be (f1scan al be t) t).2.1 = some k → k = t ∨ (f1scan al be t).2.1 = some k := by
        intro k hk
        rcases hs : (f1scan al be t).2.1 with _ | k'
        · simp [f1step, h, hs] at hk; exact Or.inl hk.symm
        · simp only [f1step, h, ↓reduceIte, hs] at hk
          split_ifs at hk
          · exact Or.inl (Option.some_inj.1 hk).symm
          · exact Or.inr hk
      have e2n : (f1step al be (f1scan al be t) t).2.1 ≠ none := by
        rcases hs : (f1scan al be t).2.1 with _ | k'
        · simp [f1step, h, hs]
        · simp only [f1step, h, ↓reduceIte, hs]; split_ifs <;> simp
      rw [e1, e3]
      refine ⟨fun i hi => ?_, ⟨fun hn => ⟨ih2.1 hn, h.le⟩, fun hall => ih2.2 hall.1⟩, fun k hk => ?_,
        ⟨fun hn => absurd hn e2n, fun hall => absurd hall.2 (by omega)⟩, ?_⟩
      · have := ih1 i hi; exact ⟨by omega, this.2⟩
      · rcases e2 k hk with e | e
        · exact ⟨by omega, e ▸ h⟩
        · have := ih3 k e; exact ⟨by omega, this.2⟩
      · rw [ih5]; simp only [h.ne', false_and, or_false]

/-- **The scan keeps the best ends**: the largest `β/α` over the rows with `α < 0`, the least over `α > 0`. -/
theorem f1scan_opt (al be : ℕ → ℤ) (t : ℕ) :
    (∀ i, (f1scan al be t).1 = some i → ∀ j < t, al j < 0 → (be j : ℚ) / al j ≤ be i / al i) ∧
      (∀ k, (f1scan al be t).2.1 = some k → ∀ j < t, 0 < al j → (be k : ℚ) / al k ≤ be j / al j) := by
  induction t with
  | zero => simp [f1scan]
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨sp1, sp2, sp3, sp4, -⟩ := f1scan_spec al be t
    rw [f1scan]
    rcases lt_trichotomy (al t) 0 with h | h | h
    · have e2 : (f1step al be (f1scan al be t) t).2.1 = (f1scan al be t).2.1 := by simp [f1step, not_lt.2 h.le]
      rw [e2]
      refine ⟨fun i hi j hj hjn => ?_, fun k hk j hj hjp => ?_⟩
      · rcases hs : (f1scan al be t).1 with _ | k
        · simp [f1step, h, hs] at hi
          subst hi
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
          · exact absurd (sp2.1 hs j hj') (by omega)
          · subst hj'; exact le_rfl
        · simp only [f1step, h, ↓reduceIte, hs] at hi
          obtain ⟨-, hkn⟩ := sp1 k hs
          have cmp := frac_lt_iff (be k) (be t) (al k) (al t) (by nlinarith)
          split_ifs at hi with hc
          · obtain rfl := Option.some_inj.1 hi
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
            · exact ((ih1 k hs j hj' hjn).trans_lt (cmp.2 hc)).le
            · subst hj'; exact le_rfl
          · obtain rfl := Option.some_inj.1 hi
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
            · exact ih1 k hs j hj' hjn
            · subst hj'; exact not_lt.1 (fun h' => hc (cmp.1 h'))
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
        · exact ih2 k hk j hj' hjp
        · subst hj'; omega
    · have e1 : (f1step al be (f1scan al be t) t).1 = (f1scan al be t).1 := by simp [f1step, h]
      have e2 : (f1step al be (f1scan al be t) t).2.1 = (f1scan al be t).2.1 := by simp [f1step, h]
      rw [e1, e2]
      refine ⟨fun i hi j hj hjn => ?_, fun k hk j hj hjp => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
        · exact ih1 i hi j hj' hjn
        · subst hj'; omega
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
        · exact ih2 k hk j hj' hjp
        · subst hj'; omega
    · have e1 : (f1step al be (f1scan al be t) t).1 = (f1scan al be t).1 := by simp [f1step, not_lt.2 h.le]
      rw [e1]
      refine ⟨fun i hi j hj hjn => ?_, fun k hk j hj hjp => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
        · exact ih1 i hi j hj' hjn
        · subst hj'; omega
      · rcases hs : (f1scan al be t).2.1 with _ | i
        · simp [f1step, h, hs] at hk
          subst hk
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
          · exact absurd (sp4.1 hs j hj') (by omega)
          · subst hj'; exact le_rfl
        · simp only [f1step, h, ↓reduceIte, hs] at hk
          obtain ⟨-, hip⟩ := sp3 i hs
          have cmp := frac_lt_iff (be t) (be i) (al t) (al i) (by nlinarith)
          split_ifs at hk with hc
          · obtain rfl := Option.some_inj.1 hk
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
            · exact ((cmp.2 hc).trans_le (ih2 i hs j hj' hjp)).le
            · subst hj'; exact le_rfl
          · obtain rfl := Option.some_inj.1 hk
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
            · exact ih2 i hs j hj' hjp
            · subst hj'; exact not_lt.1 (fun h' => hc (cmp.1 h'))

/-- **The read-off F2 is the scan's.** -/
theorem frame1_eq_scan (m : ℕ) (al be : ℕ → ℤ) :
    frame1 (fun i : Fin m => al i) (fun i : Fin m => be i) = f1out al be (f1scan al be m) := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := f1scan_spec al be m
  obtain ⟨o1, o2⟩ := f1scan_opt al be m
  have hlo : ((List.finRange m).filterMap fun i : Fin m =>
      if al i < 0 then some ((be i : ℚ) / al i) else none).max? =
      (f1scan al be m).1.map (fun i => (be i : ℚ) / al i) := by
    rcases hs : (f1scan al be m).1 with _ | i
    · rw [Option.map_none, List.max?_eq_none_iff, List.filterMap_eq_nil_iff]
      intro a _
      have := s2.1 hs a a.2
      simp [not_lt.2 this]
    · obtain ⟨hi, hneg⟩ := s1 i hs
      rw [Option.map_some, List.max?_eq_some_iff]
      refine ⟨List.mem_filterMap.2 ⟨⟨i, hi⟩, List.mem_finRange _, by simp [hneg]⟩, fun b hb => ?_⟩
      obtain ⟨a, -, ha⟩ := List.mem_filterMap.1 hb
      split_ifs at ha with h
      cases ha
      exact o1 i hs a a.2 h
  have hhi : ((List.finRange m).filterMap fun i : Fin m =>
      if 0 < al i then some ((be i : ℚ) / al i) else none).min? =
      (f1scan al be m).2.1.map (fun i => (be i : ℚ) / al i) := by
    rcases hs : (f1scan al be m).2.1 with _ | k
    · rw [Option.map_none, List.min?_eq_none_iff, List.filterMap_eq_nil_iff]
      intro a _
      have := s4.1 hs a a.2
      simp [not_lt.2 this]
    · obtain ⟨hk, hpos⟩ := s3 k hs
      rw [Option.map_some, List.min?_eq_some_iff]
      refine ⟨List.mem_filterMap.2 ⟨⟨k, hk⟩, List.mem_finRange _, by simp [hpos]⟩, fun b hb => ?_⟩
      obtain ⟨a, -, ha⟩ := List.mem_filterMap.1 hb
      split_ifs at ha with h
      cases ha
      exact o2 k hs a a.2 h
  have hbad : (∃ i : Fin m, al i = 0 ∧ be i < 0) ↔ (f1scan al be m).2.2 = true := by
    rw [s5]; exact ⟨fun ⟨i, h⟩ => ⟨i, i.2, h⟩, fun ⟨i, hi, h⟩ => ⟨⟨i, hi⟩, h⟩⟩
  unfold frame1
  simp only [hlo, hhi]
  revert hbad
  rcases f1scan al be m with ⟨a, c, e⟩
  intro hbad
  cases e with
  | true => rw [ite_eq_left (hbad.2 rfl)]; cases a <;> cases c <;> rfl
  | false =>
    rw [ite_eq_right (fun h => by simpa using hbad.1 h)]
    cases a <;> cases c <;> rfl

/-! ## The cleared rows as functions on `ℕ` -/

variable {d : ℕ}

/-- The cleared entry `j` of the input row `t`, `0` past `m` or `d`. -/
def frAlN {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (j t : ℕ) : ℤ :=
  if h : t < m ∧ j < d then frAl A b ⟨t, h.1⟩ ⟨j, h.2⟩ else 0

/-- The cleared right-hand side of the input row `t`, `0` past `m`. -/
def frBeN {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (t : ℕ) : ℤ :=
  if h : t < m then frBe A b ⟨t, h⟩ else 0

theorem frAlN_le {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (j t : ℕ) :
    |frAlN A b j t| ≤ (frMhat A b : ℤ) ^ (d + 1) := by
  unfold frAlN; split_ifs with h
  · exact (frAl_le A b _).2.1 _
  · rw [abs_zero]; positivity

theorem frBeN_le {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (t : ℕ) :
    |frBeN A b t| ≤ (frMhat A b : ℤ) ^ (d + 1) := by
  unfold frBeN; split_ifs with h
  · exact (frAl_le A b _).2.2
  · rw [abs_zero]; positivity

/-- **The frame centre for `d = 1`** is the read-off of the scan over the cleared rows. -/
theorem frameQ_one {n m : ℕ} (A : Matrix (Fin m) (Fin 1) ℚ) (b : Fin m → ℚ) (j : Fin 1) :
    frameQ 1 n m A b j = (f1out (frAlN A b 0) (frBeN A b) (f1scan (frAlN A b 0) (frBeN A b) m)).getD 0 := by
  rw [← frame1_eq_scan]
  have e : frame1 (fun i : Fin m => frAlN A b 0 i) (fun i : Fin m => frBeN A b i) =
      frame1 (fun i => frAl A b i ⟨0, Nat.one_pos⟩) (frBe A b) := by
    congr 1 <;> funext i <;> simp [frAlN, frBeN]
  rw [e]
  unfold frameQ
  simp only [↓reduceDIte]
  rcases frame1 (fun i => frAl A b i ⟨0, Nat.one_pos⟩) (frBe A b) with _ | c <;> rfl

end AdversarialBco.Bit.Transfer
