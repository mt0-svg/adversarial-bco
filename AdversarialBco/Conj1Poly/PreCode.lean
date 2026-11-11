/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Poly.Sim

@[expose] public section

/-!
# Theorem 1.3, the code of the prefix PRE^b and its generic loops

The prefix is written on raw cells. The typed layer of MachVL.lean puts its scalars and arrays at fixed cells from
`0`, where `initPoly` holds the rows, whose number `m` the program does not know in advance.

* Generic tools: `Fr` (what a command leaves unchanged), `exec_whileR_inv`, pure commands (`Cmd.Pure`: no query, draw
  or play) and their independence of the world.
* Generic loops: `dotCmd` (a dot product of two stretches of cells), `sfillCmd` (a strided fill), `naccCmd` (a
  natural accumulation), `chainCmd` (consecutive addresses in consecutive registers).
* The code of PRE^b (Lemma 8.15 of the paper): `setupCmd`, the stages (`stageCmd`, the
  loop body `iterCmd`, the test `testCmd`, the cut `cutCmd`), the frame `frameCmd`, and `preCmd`.

## The layout (`r` is the base of the frame, `r ≥ 4`)

Cells: `0, 1` free, `2` holds `δ`, the rows from `3` to `W₀ = 3 + (d + 1) m`; the 24 scalars from `W₀`; then `F_b`
(`m` cells), `F_a` (`d` cells, the centre), `F_s` (`d + 2` cells: the vector `v` of the cut, then the two scratch
cells of `S(P)`), `F_E` (`d²` cells, the matrix of the ellipsoid, row-major), and `OFF = F_E + d²`.

Registers: `r, ..., r + 10` the frame of `S(P)` (`OFF, d, m, 3, F_b, F_a, F_s, F_s + d, F_s + d + 1, 1, 0`);
`r + 21 + x` the address of the scalar `x < 24`; `r + 45 + k` the natural variables:
`F_E, w, d + 1, i, j, rowB, tA, tB, flag, gB, found, status, tc, d², eRow, 2, bA` for `k = 0, ..., 16`.

Scalars: `0` zero, `1` one half, `2` one, `3` two, `4` one quarter, `5` `d`, `6` `d²/(d² - 1)`, `7` `2/(d + 1)`,
`8` `1/(d + 1)`, `9` `R`, `10` `R²`, `11` `Y`, `12` the real counter, `13` dot, `14` squared norm, `15` product,
`16` left side, `17` norm, `18` norm of the failing row, `19` `γ`, `20` `1/√γ`, `21, 22` temporaries, `23` spare.
-/

open MeasureTheory Matrix

namespace AdversarialBco.Conj1Poly

open AdversarialBco.RealRAM AdversarialBco.Poly.Mach

variable {d : ℕ}

/-! ## Generic tools -/

/-- `s'` agrees with `s` outside the registers `R` and the cells `C`, with the same draws, rounds and points. -/
def Fr (s s' : State d) (R C : ℕ → Prop) : Prop :=
  (∀ i, ¬ R i → s'.nreg i = s.nreg i) ∧ (∀ c, ¬ C c → s'.mem c = s.mem c) ∧
    s'.draws = s.draws ∧ s'.rounds = s.rounds ∧ s'.pts = s.pts

theorem Fr.refl (s : State d) (R C : ℕ → Prop) : Fr s s R C :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Fr.trans {s s1 s2 : State d} {R C : ℕ → Prop} (h1 : Fr s s1 R C) (h2 : Fr s1 s2 R C) : Fr s s2 R C :=
  ⟨fun i hi => (h2.1 i hi).trans (h1.1 i hi), fun c hc => (h2.2.1 c hc).trans (h1.2.1 c hc),
    h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.trans h1.2.2.2.2⟩

theorem Fr.mono {s s' : State d} {R C R' C' : ℕ → Prop} (h : Fr s s' R C) (hR : ∀ i, R i → R' i)
    (hC : ∀ c, C c → C' c) : Fr s s' R' C' :=
  ⟨fun i hi => h.1 i (fun h' => hi (hR i h')), fun c hc => h.2.1 c (fun h' => hc (hC c h')), h.2.2.1, h.2.2.2.1,
    h.2.2.2.2⟩

/-- A `whileR` loop under an invariant `I t` after `t` turns: while the test holds, `t < N`, and the body keeps the
invariant within `Kb` steps. -/
theorem exec_whileR_inv {w : World d} {a b : ℕ} {c : Cmd} (I : ℕ → State d → Prop) (N Kb : ℕ)
    (hbound : ∀ t s, I t s → condR s a b → t < N)
    (hbody : ∀ t s, I t s → condR s a b → ∃ k s', k ≤ Kb ∧ Exec w c s k s' ∧ I (t + 1) s') :
    ∀ t s, I t s → ∃ k s' t', k ≤ (N - t) * (Kb + 2) + 2 ∧ Exec w (.whileR a b c) s k s' ∧ I t' s' ∧
      ¬ condR s' a b := by
  suffices H : ∀ n t s, N - t = n → I t s → ∃ k s' t', k ≤ (N - t) * (Kb + 2) + 2 ∧
      Exec w (.whileR a b c) s k s' ∧ I t' s' ∧ ¬ condR s' a b from fun t s h => H _ t s rfl h
  intro n
  induction n with
  | zero =>
    intro t s hn hI
    by_cases hc : condR s a b
    · have := hbound t s hI hc; omega
    · exact ⟨2, s, t, by omega, Exec.whileR_f hc, hI, hc⟩
  | succ n ih =>
    intro t s hn hI
    by_cases hc : condR s a b
    · obtain ⟨k, s1, hk, he, hI1⟩ := hbody t s hI hc
      obtain ⟨k', s2, t', hk', he', hI2, hc2⟩ := ih (t + 1) s1 (by omega) hI1
      refine ⟨k + 2 + k', s2, t', ?_, Exec.whileR_t hc he he', hI2, hc2⟩
      have : N - t = (N - (t + 1)) + 1 := by omega
      rw [this, Nat.add_mul, one_mul]
      omega
    · exact ⟨2, s, t, by omega, Exec.whileR_f hc, hI, hc⟩

/-- A primitive with no query, draw or play. -/
def PrimPure : Prim → Prop
  | .query _ _ => False
  | .gauss _ => False
  | .play _ _ => False
  | _ => True

/-- A command with no query, draw or play. -/
def CmdPure : Cmd → Prop
  | .skip => True
  | .prim p => PrimPure p
  | .seq c₁ c₂ => CmdPure c₁ ∧ CmdPure c₂
  | .ifR _ _ c₁ c₂ => CmdPure c₁ ∧ CmdPure c₂
  | .ifN _ _ c₁ c₂ => CmdPure c₁ ∧ CmdPure c₂
  | .whileR _ _ c => CmdPure c
  | .whileN _ _ c => CmdPure c

/-- The code of a pure command has no query. -/
theorem cmdPure_noQuery {c : Cmd} (hc : CmdPure c) (o a b : ℕ) : Instr.query a b ∉ c.compile o := by
  induction c generalizing o with
  | skip =>
      simp [Cmd.compile]
  | prim p =>
      have hp : PrimPure p := hc
      simp [Cmd.compile]
      intro hmem
      cases p with
      | query a' b' =>
        simp [PrimPure] at hp
      | _ =>
        simp [Prim.toInstr] at hmem
  | seq c₁ c₂ ih₁ ih₂ =>
      have h₁ : CmdPure c₁ := hc.1
      have h₂ : CmdPure c₂ := hc.2
      dsimp [Cmd.compile]
      intro hmem
      rw [List.mem_append] at hmem
      rcases hmem with (hmem | hmem)
      · exact ih₁ h₁ o hmem
      · exact ih₂ h₂ (o + c₁.len) hmem
  | ifR a' b' c₁ c₂ ih₁ ih₂ =>
      have h₁ : CmdPure c₁ := hc.1
      have h₂ : CmdPure c₂ := hc.2
      dsimp [Cmd.compile]
      intro hmem
      simp only [List.mem_append, List.mem_cons] at hmem
      rcases hmem with (h | h | h | h)
      · -- h : Instr.query a b = Instr.rjlt a' b' (o + c₂.len + 2)
        cases h
      · -- h : Instr.query a b ∈ c₂.compile (o + 1)
        exact ih₂ h₂ (o + 1) h
      · -- h : Instr.query a b = Instr.jmp (o + c₂.len + 2 + c₁.len)
        cases h
      · -- h : Instr.query a b ∈ c₁.compile (o + c₂.len + 2)
        exact ih₁ h₁ (o + c₂.len + 2) h
  | ifN a' b' c₁ c₂ ih₁ ih₂ =>
      have h₁ : CmdPure c₁ := hc.1
      have h₂ : CmdPure c₂ := hc.2
      dsimp [Cmd.compile]
      intro hmem
      simp only [List.mem_append, List.mem_cons] at hmem
      rcases hmem with (h | h | h | h)
      · cases h
      · exact ih₂ h₂ (o + 1) h
      · cases h
      · exact ih₁ h₁ (o + c₂.len + 2) h
  | whileR a' b' c ih =>
      have hc' : CmdPure c := hc
      dsimp [Cmd.compile]
      intro hmem
      simp only [List.mem_append, List.mem_cons] at hmem
      rcases hmem with (h | h | h | h)
      · cases h
      · cases h
      · exact ih hc' (o + 2) h
      · rcases h with (h | h) <;> cases h
  | whileN a' b' c ih =>
      have hc' : CmdPure c := hc
      dsimp [Cmd.compile]
      intro hmem
      simp only [List.mem_append, List.mem_cons] at hmem
      rcases hmem with (h | h | h | h)
      · cases h
      · cases h
      · exact ih hc' (o + 2) h
      · rcases h with (h | h) <;> cases h

/-- A pure command runs the same way in every world. -/
theorem cmdPure_exec_world {c : Cmd} (hc : CmdPure c) {w : World d} {s s' : State d} {k : ℕ}
    (h : Exec w c s k s') (w' : World d) : Exec w' c s k s' := by
  induction h generalizing w' with
  | skip s =>
      exact Exec.skip s
  | prim p s =>
      have hp : PrimPure p := by
        simpa [CmdPure] using hc
      have h_eq : Prim.exec w s p = Prim.exec w' s p := by
        cases p
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · simp [PrimPure] at hp
        · simp [PrimPure] at hp
        · simp [PrimPure] at hp
      simpa [h_eq] using Exec.prim p s
  | seq h₁ h₂ ih₁ ih₂ =>
      rcases hc with ⟨hc₁, hc₂⟩
      exact Exec.seq (ih₁ hc₁ w') (ih₂ hc₂ w')
  | ifR_t hcond h₁ ih₁ =>
      rcases hc with ⟨hc₁, hc₂⟩
      exact Exec.ifR_t hcond (ih₁ hc₁ w')
  | ifR_f hcond h₁ ih₁ =>
      rcases hc with ⟨hc₁, hc₂⟩
      exact Exec.ifR_f hcond (ih₁ hc₂ w')
  | ifN_t hcond h₁ ih₁ =>
      rcases hc with ⟨hc₁, hc₂⟩
      exact Exec.ifN_t hcond (ih₁ hc₁ w')
  | ifN_f hcond h₁ ih₁ =>
      rcases hc with ⟨hc₁, hc₂⟩
      exact Exec.ifN_f hcond (ih₁ hc₂ w')
  | whileR_t hcond h₁ h₂ ih₁ ih₂ =>
      exact Exec.whileR_t hcond (ih₁ hc w') (ih₂ hc w')
  | whileR_f hcond =>
      exact Exec.whileR_f hcond
  | whileN_t hcond h₁ h₂ ih₁ ih₂ =>
      exact Exec.whileN_t hcond (ih₁ hc w') (ih₂ hc w')
  | whileN_f hcond =>
      exact Exec.whileN_f hcond

/-- A pure command keeps the draws, the rounds and the points. -/
theorem cmdPure_exec_keep {c : Cmd} (hc : CmdPure c) {w : World d} {s s' : State d} {k : ℕ}
    (h : Exec w c s k s') : s'.draws = s.draws ∧ s'.rounds = s.rounds ∧ s'.pts = s.pts := by
  induction h with
  | skip s => exact ⟨rfl, rfl, rfl⟩
  | prim p s =>
    have hp : PrimPure p := hc
    cases p <;> first | exact ⟨rfl, rfl, rfl⟩ | exact hp.elim
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨a1, b1, c1⟩ := ih₁ hc.1
    obtain ⟨a2, b2, c2⟩ := ih₂ hc.2
    exact ⟨a2.trans a1, b2.trans b1, c2.trans c1⟩
  | ifR_t _ _ ih => exact ih hc.1
  | ifR_f _ _ ih => exact ih hc.2
  | ifN_t _ _ ih => exact ih hc.1
  | ifN_f _ _ ih => exact ih hc.2
  | whileR_t _ _ _ ih₁ ih₂ =>
    obtain ⟨a1, b1, c1⟩ := ih₁ hc
    obtain ⟨a2, b2, c2⟩ := ih₂ hc
    exact ⟨a2.trans a1, b2.trans b1, c2.trans c1⟩
  | whileR_f _ => exact ⟨rfl, rfl, rfl⟩
  | whileN_t _ _ _ ih₁ ih₂ =>
    obtain ⟨a1, b1, c1⟩ := ih₁ hc
    obtain ⟨a2, b2, c2⟩ := ih₂ hc
    exact ⟨a2.trans a1, b2.trans b1, c2.trans c1⟩
  | whileN_f _ => exact ⟨rfl, rfl, rfl⟩

/-! ## Generic loops -/

/-- `M (N acc) := Σ_{k < N dv} M (N pA + k) · M (N pB + k)`, through the counter `j`, the address registers `tA`,
`tB` and the product cell `M (N prod)`. -/
def dotCmd (j dv one pA pB tA tB acc prod : ℕ) : Cmd :=
  .seq (prims [.nconst j 0, .rconst acc 0])
    (.whileN j dv (prims [.nadd tA pA j, .nadd tB pB j, .op2 .mul prod tA tB, .op2 .add acc acc prod,
      .nadd j j one]))

theorem dot_exec {w : World d} {j dv one pA pB tA tB acc prod : ℕ} (s : State d)
    (hj : j ≠ dv ∧ j ≠ one ∧ j ≠ pA ∧ j ≠ pB ∧ j ≠ acc ∧ j ≠ prod)
    (htA : tA ≠ j ∧ tA ≠ dv ∧ tA ≠ one ∧ tA ≠ pA ∧ tA ≠ pB ∧ tA ≠ tB ∧ tA ≠ acc ∧ tA ≠ prod)
    (htB : tB ≠ j ∧ tB ≠ dv ∧ tB ≠ one ∧ tB ≠ pA ∧ tB ≠ pB ∧ tB ≠ acc ∧ tB ≠ prod)
    (h1 : s.nreg one = 1) (hap : s.nreg acc ≠ s.nreg prod)
    (hA : ∀ k < s.nreg dv, s.nreg pA + k ≠ s.nreg acc ∧ s.nreg pA + k ≠ s.nreg prod)
    (hB : ∀ k < s.nreg dv, s.nreg pB + k ≠ s.nreg acc ∧ s.nreg pB + k ≠ s.nreg prod) :
    ∃ s', Exec w (dotCmd j dv one pA pB tA tB acc prod) s (7 * s.nreg dv + 4) s' ∧
      s'.mem (s.nreg acc) = ∑ k ∈ Finset.range (s.nreg dv), s.mem (s.nreg pA + k) * s.mem (s.nreg pB + k) ∧
      Fr s s' (fun i => i = j ∨ i = tA ∨ i = tB) (fun c => c = s.nreg acc ∨ c = s.nreg prod) := by
  obtain ⟨hjdv, hjone, hjpA, hjpB, hjacc, hjprod⟩ := hj
  obtain ⟨hAj, hAdv, hAone, hApA, hApB, hAB, hAacc, hAprod⟩ := htA
  obtain ⟨hBj, hBdv, hBone, hBpA, hBpB, hBacc, hBprod⟩ := htB
  obtain ⟨N, hN⟩ : ∃ N, N = s.nreg dv := ⟨_, rfl⟩
  let I : ℕ → State d → Prop := fun t S => S.nreg j = t ∧
    S.mem (s.nreg acc) = ∑ k ∈ Finset.range t, s.mem (s.nreg pA + k) * s.mem (s.nreg pB + k) ∧
    Fr s S (fun i => i = j ∨ i = tA ∨ i = tB) (fun c => c = s.nreg acc ∨ c = s.nreg prod)
  have hstep : ∀ t S, t < N → I t S → I (t + 1) ([Prim.nadd tA pA j, .nadd tB pB j, .op2 .mul prod tA tB, .op2 .add acc acc prod,
      .nadd j j one].foldl (fun s p => p.exec w s) S) := by
    rintro t S ht ⟨hjt, hacc, hn, hm, hdr, hro, hpt⟩
    have nR : ∀ x, x ≠ j → x ≠ tA → x ≠ tB → ¬ (x = j ∨ x = tA ∨ x = tB) := fun x a b c h => by
      rcases h with h | h | h <;> contradiction
    have nC : ∀ c, c ≠ s.nreg acc → c ≠ s.nreg prod → ¬ (c = s.nreg acc ∨ c = s.nreg prod) := fun c a b h => by
      rcases h with h | h <;> contradiction
    have epA : S.nreg pA = s.nreg pA := hn pA (nR _ hjpA.symm hApA.symm hBpA.symm)
    have epB : S.nreg pB = s.nreg pB := hn pB (nR _ hjpB.symm hApB.symm hBpB.symm)
    have eacc : S.nreg acc = s.nreg acc := hn acc (nR _ hjacc.symm hAacc.symm hBacc.symm)
    have eprod : S.nreg prod = s.nreg prod := hn prod (nR _ hjprod.symm hAprod.symm hBprod.symm)
    have eone : S.nreg one = 1 := (hn one (nR _ hjone.symm hAone.symm hBone.symm)).trans h1
    have mA : S.mem (s.nreg pA + t) = s.mem (s.nreg pA + t) := hm _ (nC _ (hA t (hN ▸ ht)).1 (hA t (hN ▸ ht)).2)
    have mB : S.mem (s.nreg pB + t) = s.mem (s.nreg pB + t) := hm _ (nC _ (hB t (hN ▸ ht)).1 (hB t (hN ▸ ht)).2)
    have hpa : s.nreg prod ≠ s.nreg acc := fun h => hap h.symm
    have a1 := (hA t (hN ▸ ht)).1; have a2 := (hA t (hN ▸ ht)).2
    have b1 := (hB t (hN ▸ ht)).1; have b2 := (hB t (hN ▸ ht)).2
    simp only [List.foldl, Prim.exec, Op2.eval]
    dsimp only [I]
    simp only [Function.update_apply, hjdv, hjone, hjpA, hjpB, hjacc, hjprod,
      hAj, hAdv, hAone, hApA, hApB, hAB, hAacc, hAprod, hBj, hBdv, hBone, hBpA, hBpB, hBacc, hBprod,
      hjdv.symm, hjone.symm, hjpA.symm, hjpB.symm, hjacc.symm, hjprod.symm, hAj.symm, hAdv.symm, hAone.symm,
      hApA.symm, hApB.symm, hAB.symm, hAacc.symm, hAprod.symm, hBj.symm, hBdv.symm, hBone.symm, hBpA.symm,
      hBpB.symm, hBacc.symm, hBprod.symm, ↓reduceIte, eacc, eprod, epA, epB, eone, hjt, hap, hpa,
      a1, a2, b1, b2]
    refine ⟨trivial, ?_, fun i hi => ?_, fun c hc => ?_, hdr, hro, hpt⟩
    · rw [hacc, mA, mB, Finset.sum_range_succ]
    · have h1' : i ≠ j := fun h => hi (Or.inl h)
      have h2' : i ≠ tA := fun h => hi (Or.inr (Or.inl h))
      have h3' : i ≠ tB := fun h => hi (Or.inr (Or.inr h))
      simp only [Function.update_apply, h1', h2', h3', ↓reduceIte]
      exact hn i hi
    · have h1' : c ≠ s.nreg acc := fun h => hc (Or.inl h)
      have h2' : c ≠ s.nreg prod := fun h => hc (Or.inr h)
      simp only [Function.update_apply, h1', h2', ↓reduceIte]
      exact hm c hc
  have hloop : ∀ u t S, N - t = u → t ≤ N → I t S →
      ∃ S', Exec w (.whileN j dv (prims [.nadd tA pA j, .nadd tB pB j, .op2 .mul prod tA tB,
        .op2 .add acc acc prod, .nadd j j one])) S (7 * (N - t) + 2) S' ∧ I N S' := by
    intro u
    induction u with
    | zero =>
      intro t S hu ht hI
      have htN : t = N := by omega
      subst htN
      have hdv : S.nreg dv = s.nreg dv := hI.2.2.1 dv (fun h => by rcases h with h | h | h <;> simp_all)
      refine ⟨S, (Exec.whileN_f (by simp only [condN, hI.1, hdv]; omega)).cost (by omega), hI⟩
    | succ u ih =>
      intro t S hu ht hI
      have hdv : S.nreg dv = s.nreg dv := hI.2.2.1 dv (fun h => by rcases h with h | h | h <;> simp_all)
      have hc : condN S j dv := by simp only [condN, hI.1, hdv]; omega
      obtain ⟨S', e', hI'⟩ := ih (t + 1) _ (by omega) (by omega) (hstep t S (by omega) hI)
      refine ⟨S', (Exec.whileN_t hc (exec_prims w _ S) e').cost ?_, hI'⟩
      simp only [List.length_cons, List.length_nil]
      omega
  set s0 := [Prim.nconst j 0, Prim.rconst acc 0].foldl (fun s p => p.exec w s) s with hs0
  have hI0 : I 0 s0 := by
    simp only [hs0, List.foldl, Prim.exec]
    refine ⟨by simp, ?_, fun i hi => ?_, fun c hc => ?_, rfl, rfl, rfl⟩
    · simp [Function.update_apply, hjacc.symm]
    · have h1' : i ≠ j := fun h => hi (Or.inl h)
      simp [Function.update_apply, h1']
    · have h1' : c ≠ s.nreg acc := fun h => hc (Or.inl h)
      simp [Function.update_apply, hjacc.symm, h1']
  obtain ⟨S', e', hI'⟩ := hloop N 0 s0 (by omega) (by omega) hI0
  refine ⟨S', (Exec.seq (exec_prims w _ s) e').cost (by simp; omega), by rw [← hN]; exact hI'.2.1, hI'.2.2⟩

/-- `M (N base + N stride · k) := M (N src) + M (N zero)` for `k < N D`, through the counter `i` and the pointer
`ptr` (`z` holds `0`). -/
def sfillCmd (i D one z ptr base stride src zr : ℕ) : Cmd :=
  .seq (prims [.nconst i 0, .nadd ptr base z])
    (.whileN i D (prims [.op2 .add ptr src zr, .nadd ptr ptr stride, .nadd i i one]))

theorem sfill_exec {w : World d} {i D one z ptr base stride src zr : ℕ} (s : State d)
    (hi : i ≠ D ∧ i ≠ one ∧ i ≠ z ∧ i ≠ base ∧ i ≠ stride ∧ i ≠ src ∧ i ≠ zr)
    (hptr : ptr ≠ i ∧ ptr ≠ D ∧ ptr ≠ one ∧ ptr ≠ z ∧ ptr ≠ base ∧ ptr ≠ stride ∧ ptr ≠ src ∧ ptr ≠ zr)
    (h1 : s.nreg one = 1) (hz : s.nreg z = 0)
    (hcell : ∀ k < s.nreg D, s.nreg base + s.nreg stride * k ≠ s.nreg src ∧
      s.nreg base + s.nreg stride * k ≠ s.nreg zr) :
    ∃ s', Exec w (sfillCmd i D one z ptr base stride src zr) s (5 * s.nreg D + 4) s' ∧
      (∀ k < s.nreg D, s'.mem (s.nreg base + s.nreg stride * k) = s.mem (s.nreg src) + s.mem (s.nreg zr)) ∧
      Fr s s' (fun r => r = i ∨ r = ptr) (fun c => ∃ k < s.nreg D, c = s.nreg base + s.nreg stride * k) := by
  obtain ⟨hiD, hione, hiz, hibase, histride, hisrc, hizr⟩ := hi
  obtain ⟨hpi, hpD, hpone, hpz, hpbase, hpstride, hpsrc, hpzr⟩ := hptr
  obtain ⟨N, hN⟩ : ∃ N, N = s.nreg D := ⟨_, rfl⟩
  have nR : ∀ q, q ≠ i → q ≠ ptr → ¬ (q = i ∨ q = ptr) := fun q a b h => by
    rcases h with h | h <;> contradiction
  have nC : ∀ c, (∀ k < N, c ≠ s.nreg base + s.nreg stride * k) →
      ¬ ∃ k < s.nreg D, c = s.nreg base + s.nreg stride * k := fun c h ⟨k, hk, he⟩ => h k (hN ▸ hk) he
  let I : ℕ → State d → Prop := fun t S => S.nreg i = t ∧ S.nreg ptr = s.nreg base + s.nreg stride * t ∧
    (∀ k < t, S.mem (s.nreg base + s.nreg stride * k) = s.mem (s.nreg src) + s.mem (s.nreg zr)) ∧
    Fr s S (fun r => r = i ∨ r = ptr) (fun c => ∃ k < s.nreg D, c = s.nreg base + s.nreg stride * k)
  have hstep : ∀ t S, t < N → I t S → I (t + 1) ([Prim.op2 .add ptr src zr, .nadd ptr ptr stride, .nadd i i one].foldl
      (fun s p => p.exec w s) S) := by
    rintro t S ht ⟨hit, hpt', hcells, hn, hm, hdr, hro, hpt⟩
    have esrc : S.nreg src = s.nreg src := hn src (nR _ (Ne.symm hisrc) (Ne.symm hpsrc))
    have ezr : S.nreg zr = s.nreg zr := hn zr (nR _ (Ne.symm hizr) (Ne.symm hpzr))
    have estride : S.nreg stride = s.nreg stride := hn stride (nR _ (Ne.symm histride) (Ne.symm hpstride))
    have eone : S.nreg one = 1 := (hn one (nR _ (Ne.symm hione) (Ne.symm hpone))).trans h1
    have msrc : S.mem (s.nreg src) = s.mem (s.nreg src) :=
      hm _ (nC _ fun k hk h => (hcell k (hN ▸ hk)).1 h.symm)
    have mzr : S.mem (s.nreg zr) = s.mem (s.nreg zr) :=
      hm _ (nC _ fun k hk h => (hcell k (hN ▸ hk)).2 h.symm)
    simp only [List.foldl, Prim.exec, Op2.eval]
    dsimp only [I]
    simp only [Function.update_apply, hpi, hpi.symm, hione.symm, hpone.symm, hpstride.symm, ↓reduceIte, hit,
      hpt', esrc, ezr, estride, eone, msrc, mzr]
    refine ⟨trivial, by ring, fun k hk => ?_, fun q hq => ?_, fun c hc => ?_, hdr, hro, hpt⟩
    · by_cases hkt : s.nreg base + s.nreg stride * k = s.nreg base + s.nreg stride * t
      · rw [ite_eq_left hkt]
      · rw [ite_eq_right hkt]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
        · exact hcells k hk
        · exact absurd rfl hkt
    · have h1' : q ≠ i := fun h => hq (Or.inl h)
      have h2' : q ≠ ptr := fun h => hq (Or.inr h)
      simp only [Function.update_apply, h1', h2', ↓reduceIte]
      exact hn q hq
    · have hne : c ≠ s.nreg base + s.nreg stride * t := fun h => hc ⟨t, hN ▸ ht, h⟩
      simp only [Function.update_apply, hne, ↓reduceIte]
      exact hm c hc
  have hloop : ∀ u t S, N - t = u → t ≤ N → I t S →
      ∃ S', Exec w (.whileN i D (prims [.op2 .add ptr src zr, .nadd ptr ptr stride, .nadd i i one])) S
        (5 * (N - t) + 2) S' ∧ I N S' := by
    intro u
    induction u with
    | zero =>
      intro t S hu ht hI
      have htN : t = N := by omega
      subst htN
      have hD : S.nreg D = s.nreg D := hI.2.2.2.1 D (nR _ (Ne.symm hiD) (Ne.symm hpD))
      refine ⟨S, (Exec.whileN_f (by simp only [condN, hI.1, hD]; omega)).cost (by omega), hI⟩
    | succ u ih =>
      intro t S hu ht hI
      have hD : S.nreg D = s.nreg D := hI.2.2.2.1 D (nR _ (Ne.symm hiD) (Ne.symm hpD))
      have hc : condN S i D := by simp only [condN, hI.1, hD]; omega
      obtain ⟨S', e', hI'⟩ := ih (t + 1) _ (by omega) (by omega) (hstep t S (by omega) hI)
      refine ⟨S', (Exec.whileN_t hc (exec_prims w _ S) e').cost ?_, hI'⟩
      simp only [List.length_cons, List.length_nil]
      omega
  set s0 := [Prim.nconst i 0, Prim.nadd ptr base z].foldl (fun s p => p.exec w s) s with hs0
  have hI0 : I 0 s0 := by
    simp only [hs0, List.foldl, Prim.exec]
    refine ⟨?_, ?_, fun k hk => absurd hk (Nat.not_lt_zero k), fun q hq => ?_, fun c _ => rfl, rfl, rfl, rfl⟩
    · simp [Function.update_apply, hpi.symm]
    · simp [Function.update_apply, hpi, hibase.symm, hiz.symm, hz]
    · have h1' : q ≠ i := fun h => hq (Or.inl h)
      have h2' : q ≠ ptr := fun h => hq (Or.inr h)
      simp [Function.update_apply, h1', h2']
  obtain ⟨S', e', hI'⟩ := hloop N 0 s0 (by omega) (by omega) hI0
  refine ⟨S', (Exec.seq (exec_prims w _ s) e').cost (by simp; omega), fun k hk => hI'.2.2.1 k (hN ▸ hk), hI'.2.2.2⟩

/-- `N x := N x + N D · N y`, through the counter `i`. -/
def naccCmd (i D one x y : ℕ) : Cmd :=
  .seq (.prim (.nconst i 0)) (.whileN i D (prims [.nadd x x y, .nadd i i one]))

theorem nacc_exec {w : World d} {i D one x y : ℕ} (s : State d)
    (hi : i ≠ D ∧ i ≠ one ∧ i ≠ x ∧ i ≠ y) (hx : x ≠ D ∧ x ≠ one ∧ x ≠ y) (h1 : s.nreg one = 1) :
    ∃ s', Exec w (naccCmd i D one x y) s (4 * s.nreg D + 3) s' ∧ s'.nreg x = s.nreg x + s.nreg D * s.nreg y ∧
      Fr s s' (fun r => r = i ∨ r = x) (fun _ => False) := by
  obtain ⟨hiD, hione, hix, hiy⟩ := hi
  obtain ⟨hxD, hxone, hxy⟩ := hx
  obtain ⟨N, hN⟩ : ∃ N, N = s.nreg D := ⟨_, rfl⟩
  have nR : ∀ q, q ≠ i → q ≠ x → ¬ (q = i ∨ q = x) := fun q a b h => by
    rcases h with h | h <;> contradiction
  let I : ℕ → State d → Prop := fun t S => S.nreg i = t ∧ S.nreg x = s.nreg x + t * s.nreg y ∧
    Fr s S (fun r => r = i ∨ r = x) (fun _ => False)
  have hstep : ∀ t S, I t S → I (t + 1) ([Prim.nadd x x y, .nadd i i one].foldl (fun s p => p.exec w s) S) := by
    rintro t S ⟨hit, hxt, hn, hm, hdr, hro, hpt⟩
    have ey : S.nreg y = s.nreg y := hn y (nR _ (Ne.symm hiy) (Ne.symm hxy))
    have eone : S.nreg one = 1 := (hn one (nR _ (Ne.symm hione) (Ne.symm hxone))).trans h1
    simp only [List.foldl, Prim.exec]
    dsimp only [I]
    simp only [Function.update_apply, hix, hix.symm, hxone.symm, ↓reduceIte, hit, hxt, ey, eone]
    refine ⟨trivial, by ring, fun q hq => ?_, fun c _ => hm c id, hdr, hro, hpt⟩
    have h1' : q ≠ i := fun h => hq (Or.inl h)
    have h2' : q ≠ x := fun h => hq (Or.inr h)
    simp only [Function.update_apply, h1', h2', ↓reduceIte]
    exact hn q hq
  have hloop : ∀ u t S, N - t = u → t ≤ N → I t S →
      ∃ S', Exec w (.whileN i D (prims [.nadd x x y, .nadd i i one])) S (4 * (N - t) + 2) S' ∧ I N S' := by
    intro u
    induction u with
    | zero =>
      intro t S hu ht hI
      have htN : t = N := by omega
      subst htN
      have hD : S.nreg D = s.nreg D := hI.2.2.1 D (nR _ (Ne.symm hiD) (Ne.symm hxD))
      refine ⟨S, (Exec.whileN_f (by simp only [condN, hI.1, hD]; omega)).cost (by omega), hI⟩
    | succ u ih =>
      intro t S hu ht hI
      have hD : S.nreg D = s.nreg D := hI.2.2.1 D (nR _ (Ne.symm hiD) (Ne.symm hxD))
      have hc : condN S i D := by simp only [condN, hI.1, hD]; omega
      obtain ⟨S', e', hI'⟩ := ih (t + 1) _ (by omega) (by omega) (hstep t S hI)
      refine ⟨S', (Exec.whileN_t hc (exec_prims w _ S) e').cost ?_, hI'⟩
      simp only [List.length_cons, List.length_nil]
      omega
  set s0 := (Prim.nconst i 0).exec w s with hs0
  have hI0 : I 0 s0 := by
    simp only [hs0, Prim.exec]
    refine ⟨by simp, by simp [Function.update_apply, hix.symm], fun q hq => ?_, fun c _ => rfl, rfl, rfl, rfl⟩
    have h1' : q ≠ i := fun h => hq (Or.inl h)
    simp [Function.update_apply, h1']
  obtain ⟨S', e', hI'⟩ := hloop N 0 s0 (by omega) (by omega) hI0
  refine ⟨S', (Exec.seq (Exec.prim _ s) e').cost (by omega), ?_, hI'.2.2⟩
  rw [hI'.2.1, hN]

/-- `N (b + x + 1) := N (b + x) + N one` for `x < k`, in order. -/
def chainCmd (b one : ℕ) : ℕ → Cmd
  | 0 => .skip
  | k + 1 => .seq (chainCmd b one k) (.prim (.nadd (b + k + 1) (b + k) one))

theorem chain_exec {w : World d} {b one : ℕ} (k : ℕ) (s : State d) (hone : one < b + 1 ∨ b + k < one)
    (h1 : s.nreg one = 1) :
    ∃ s', Exec w (chainCmd b one k) s k s' ∧ (∀ x ≤ k, s'.nreg (b + x) = s.nreg b + x) ∧
      Fr s s' (fun r => b < r ∧ r ≤ b + k) (fun _ => False) := by
  revert s hone h1
  induction k with
  | zero =>
    intro s hone h1
    refine ⟨s, Exec.skip s, ?_, ?_⟩
    · intro x hx
      have hx0 : x = 0 := by omega
      subst hx0
      simp
    · refine ⟨?_, ?_, rfl, rfl, rfl⟩
      · intro i hi
        rfl
      · intro c hc
        rfl
  | succ k ih =>
    intro s hone h1
    -- ih : ∀ (s : State d), (one < b + 1 ∨ b + k < one) → (s.nreg one = 1) → ∃ s', ...
    have hone_k : one < b + 1 ∨ b + k < one := by
      rcases hone with (h | h)
      · exact Or.inl h
      · omega
    rcases ih s hone_k h1 with ⟨s1, hExec1, hNreg1, hFr1⟩
    rcases hFr1 with ⟨hFr_reg1, hFr_mem1, hFr_draws1, hFr_rounds1, hFr_pts1⟩
    have hone_notin : ∀ i, b < i → i ≤ b + k → i ≠ one := by
      intro i hb_lt hi_le
      rcases hone with (h | h)
      · have hone_le_b : one ≤ b := by omega
        omega
      · omega
    have hone_nreg_eq : s1.nreg one = s.nreg one := by
      apply hFr_reg1 one
      intro h
      exact hone_notin one h.1 h.2 rfl
    let s' : State d := (Prim.nadd (b + k + 1) (b + k) one).exec w s1
    have hExec_prim : Exec w (.prim (.nadd (b + k + 1) (b + k) one)) s1 1 s' := by
      dsimp [s']
      exact Exec.prim (.nadd (b + k + 1) (b + k) one) s1
    have hExec_seq : Exec w (chainCmd b one (k + 1)) s (k + 1) s' := by
      dsimp [chainCmd]
      exact Exec.seq hExec1 hExec_prim
    have hNreg : ∀ x ≤ k + 1, s'.nreg (b + x) = s.nreg b + x := by
      intro x hx
      have hx_cases : x ≤ k ∨ x = k + 1 := by omega
      rcases hx_cases with (hx_le_k | hx_eq)
      · have h_nreg_i : s'.nreg (b + x) = s1.nreg (b + x) := by
          dsimp [s', Prim.exec]
          by_cases h_eq : b + x = b + k + 1
          · have : x = k + 1 := by omega
            omega
          · simp [h_eq]
        rw [h_nreg_i, hNreg1 x hx_le_k]
      · subst hx_eq
        dsimp [s', Prim.exec]
        have h_eq : b + (k + 1) = b + k + 1 := by omega
        simp [h_eq]
        rw [hNreg1 k (le_refl k), hone_nreg_eq]
        omega
    have hFr : Fr s s' (fun r => b < r ∧ r ≤ b + (k + 1)) (fun _ => False) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro i hi
        by_cases hi_eq : i = b + (k + 1)
        · subst hi_eq
          exfalso
          apply hi
          exact ⟨by omega, le_refl _⟩
        · have h_nreg_i : s'.nreg i = s1.nreg i := by
            dsimp [s', Prim.exec]
            have hi_eq' : i ≠ b + k + 1 := by
              intro h; apply hi_eq; omega
            simp [hi_eq']
          rw [h_nreg_i]
          apply hFr_reg1 i
          intro h
          rcases h with ⟨hb_lt_i, hi_le_bk⟩
          apply hi
          exact ⟨hb_lt_i, by omega⟩
      · intro c hc
        dsimp [s', Prim.exec]
        exact hFr_mem1 c hc
      · dsimp [s', Prim.exec]
        rw [hFr_draws1]
      · dsimp [s', Prim.exec]
        rw [hFr_rounds1]
      · dsimp [s', Prim.exec]
        rw [hFr_pts1]
    exact ⟨s', hExec_seq, hNreg, hFr⟩

/-! ## The code of PRE^b -/

/-- The set-up: the frame registers, `W₀`, `d²`, the scalar addresses, the addresses of the frame, the constants,
`R = 2` and `found = 0`. -/
def setupCmd (r : ℕ) : Cmd :=
  .seq (prims [.nconst (r + 9) 1, .nconst (r + 10) 0, .nadd (r + 1) 0 (r + 10), .nadd (r + 2) 2 (r + 10),
      .nconst (r + 3) 3, .nadd (r + 47) (r + 1) (r + 9), .nconst (r + 60) 2, .nconst (r + 46) 3, .nconst (r + 58) 0])
  (.seq (naccCmd (r + 48) (r + 2) (r + 9) (r + 46) (r + 47))
  (.seq (naccCmd (r + 48) (r + 1) (r + 9) (r + 58) (r + 1))
  (.seq (.prim (.nadd (r + 21) (r + 46) (r + 10)))
  (.seq (chainCmd (r + 21) (r + 9) 23)
  (prims [.nadd (r + 4) (r + 44) (r + 9), .nadd (r + 5) (r + 4) (r + 2), .nadd (r + 6) (r + 5) (r + 1),
      .nadd (r + 7) (r + 6) (r + 1), .nadd (r + 8) (r + 7) (r + 9), .nadd (r + 45) (r + 8) (r + 9),
      .nadd r (r + 45) (r + 58),
      .rconst (r + 21) 0, .rconst (r + 22) (1 / 2), .rconst (r + 23) 1, .rconst (r + 24) 2, .rconst (r + 25) (1 / 4),
      .ncast (r + 26) 0,
      .op2 .mul (r + 42) (r + 26) (r + 26), .op2 .sub (r + 43) (r + 42) (r + 23), .op2 .div (r + 27) (r + 42) (r + 43),
      .op2 .add (r + 43) (r + 26) (r + 23), .op2 .div (r + 28) (r + 24) (r + 43), .op2 .div (r + 29) (r + 23) (r + 43),
      .rconst (r + 30) 2, .nconst (r + 55) 0])))))

/-- One row of the test: `dot = ⟨a_i, a⟩`, `nn = |a_i|²`, `lhs = dot + |a_i|/2`; if `b_i < lhs` the row fails (the
flag is cleared, `gB` and the norm kept, the loop left), else the next row. -/
def testBody (r : ℕ) : Cmd :=
  .seq (dotCmd (r + 49) (r + 1) (r + 9) (r + 50) (r + 5) (r + 51) (r + 52) (r + 34) (r + 36))
  (.seq (dotCmd (r + 49) (r + 1) (r + 9) (r + 50) (r + 50) (r + 51) (r + 52) (r + 35) (r + 36))
  (.seq (prims [.op1 .sqrt (r + 38) (r + 35), .op2 .mul (r + 37) (r + 22) (r + 38), .op2 .add (r + 37) (r + 34) (r + 37),
      .nadd (r + 61) (r + 50) (r + 1)])
    (.ifR (r + 61) (r + 37)
      (prims [.nconst (r + 53) 0, .nadd (r + 54) (r + 50) (r + 10), .op2 .add (r + 39) (r + 38) (r + 21),
        .nadd (r + 48) (r + 2) (r + 10)])
      (prims [.nadd (r + 50) (r + 50) (r + 47), .nadd (r + 48) (r + 48) (r + 9)]))))

/-- The test of the centre `a` against every row, margin `1/2`. -/
def testCmd (r : ℕ) : Cmd :=
  .seq (prims [.nconst (r + 48) 0, .nconst (r + 53) 1, .nadd (r + 50) (r + 3) (r + 10)])
    (.whileN (r + 48) (r + 2) (testBody r))

/-- Row `i` of `v = E g`, and `γ += g_i v_i`. -/
def mvBody (r : ℕ) : Cmd :=
  .seq (dotCmd (r + 49) (r + 1) (r + 9) (r + 59) (r + 54) (r + 51) (r + 52) (r + 34) (r + 36))
    (prims [.nadd (r + 51) (r + 6) (r + 48), .op2 .add (r + 51) (r + 34) (r + 21),
      .nadd (r + 52) (r + 54) (r + 48), .op2 .mul (r + 36) (r + 52) (r + 34), .op2 .add (r + 40) (r + 40) (r + 36),
      .nadd (r + 59) (r + 59) (r + 1), .nadd (r + 48) (r + 48) (r + 9)])

/-- `b_i = v_i / √γ` in place of `v_i`, and `a_i -= b_i / (d + 1)`. -/
def baBody (r : ℕ) : Cmd :=
  prims [.nadd (r + 51) (r + 6) (r + 48), .op2 .mul (r + 51) (r + 41) (r + 51),
    .nadd (r + 52) (r + 5) (r + 48), .op2 .mul (r + 42) (r + 29) (r + 51), .op2 .sub (r + 52) (r + 52) (r + 42),
    .nadd (r + 48) (r + 48) (r + 9)]

/-- `E_ij := d²/(d² - 1) (E_ij - 2/(d + 1) b_i b_j)` for the column `j`. -/
def r1Inner (r : ℕ) : Cmd :=
  prims [.nadd (r + 52) (r + 6) (r + 49), .nadd (r + 61) (r + 59) (r + 49),
    .op2 .mul (r + 42) (r + 51) (r + 52), .op2 .mul (r + 42) (r + 28) (r + 42),
    .op2 .sub (r + 43) (r + 61) (r + 42), .op2 .mul (r + 61) (r + 27) (r + 43), .nadd (r + 49) (r + 49) (r + 9)]

/-- The row `i` of the rank-one update. -/
def r1Outer (r : ℕ) : Cmd :=
  .seq (prims [.nadd (r + 51) (r + 6) (r + 48), .nconst (r + 49) 0])
    (.seq (.whileN (r + 49) (r + 1) (r1Inner r))
      (prims [.nadd (r + 59) (r + 59) (r + 1), .nadd (r + 48) (r + 48) (r + 9)]))

/-- The cut `cutUpdate E a g` with `g` the row at `gB`: `ccUpdate`, or `E/4` when `d < 2`. -/
def cutCmd (r : ℕ) : Cmd :=
  .seq (prims [.rconst (r + 40) 0, .nadd (r + 59) (r + 45) (r + 10), .nconst (r + 48) 0])
  (.seq (.whileN (r + 48) (r + 1) (mvBody r))
  (.seq (prims [.op1 .sqrt (r + 42) (r + 40), .op2 .div (r + 41) (r + 23) (r + 42), .nconst (r + 48) 0])
  (.seq (.whileN (r + 48) (r + 1) (baBody r))
  (.ifN (r + 1) (r + 60)
     (.prim (.op2 .mul (r + 45) (r + 25) (r + 45)))
     (.seq (prims [.nadd (r + 59) (r + 45) (r + 10), .nconst (r + 48) 0])
        (.whileN (r + 48) (r + 1) (r1Outer r)))))))

/-- One test of a stage: if every row passes, `status = 1` and the loop is left; on a failing row of positive norm,
the cut and the next count; on a failing zero row, the loop is left with `status = 0`. -/
def iterCmd (r : ℕ) : Cmd :=
  .seq (testCmd r)
    (.ifN (r + 10) (r + 53)
      (prims [.nconst (r + 56) 1, .op2 .add (r + 33) (r + 32) (r + 21)])
      (.ifR (r + 21) (r + 39)
        (.seq (cutCmd r) (prims [.nadd (r + 57) (r + 57) (r + 9), .ncast (r + 33) (r + 57)]))
        (.prim (.op2 .add (r + 33) (r + 32) (r + 21)))))

/-- The stage of radius `R`: `R²`, `Y = 2 d (d + 1) log (2 R) + 1`, `E = R² I`, `a = 0`, at most `⌈Y⌉` tests,
`found := status`, `R := R²`. -/
def stageCmd (r : ℕ) : Cmd :=
  .seq (prims [.op2 .mul (r + 31) (r + 30) (r + 30), .op2 .mul (r + 42) (r + 24) (r + 30), .op1 .log (r + 42) (r + 42),
      .op2 .add (r + 43) (r + 26) (r + 23), .op2 .mul (r + 43) (r + 26) (r + 43), .op2 .mul (r + 43) (r + 24) (r + 43),
      .op2 .mul (r + 32) (r + 43) (r + 42), .op2 .add (r + 32) (r + 32) (r + 23)])
  (.seq (sfillCmd (r + 48) (r + 58) (r + 9) (r + 10) (r + 59) (r + 45) (r + 9) (r + 21) (r + 21))
  (.seq (sfillCmd (r + 48) (r + 1) (r + 9) (r + 10) (r + 59) (r + 45) (r + 47) (r + 31) (r + 21))
  (.seq (sfillCmd (r + 48) (r + 1) (r + 9) (r + 10) (r + 59) (r + 5) (r + 9) (r + 21) (r + 21))
  (.seq (prims [.nconst (r + 57) 0, .rconst (r + 33) 0, .nconst (r + 56) 0])
  (.seq (.whileR (r + 33) (r + 32) (iterCmd r))
  (prims [.nadd (r + 55) (r + 56) (r + 10), .op2 .add (r + 30) (r + 31) (r + 21)]))))))

/-- Row `i` of the frame: `b'_i = b_i - ⟨a_i, a₀⟩` at `F_b + i`. -/
def fbBody (r : ℕ) : Cmd :=
  .seq (dotCmd (r + 49) (r + 1) (r + 9) (r + 50) (r + 5) (r + 51) (r + 52) (r + 34) (r + 36))
    (prims [.nadd (r + 61) (r + 50) (r + 1), .nadd (r + 51) (r + 4) (r + 48), .op2 .sub (r + 51) (r + 61) (r + 34),
      .nadd (r + 50) (r + 50) (r + 47), .nadd (r + 48) (r + 48) (r + 9)])

/-- The frame: the cells `b'_i`, then `1/2`, `n`, `δ` at `OFF`, and the register `2` reset. -/
def frameCmd (r : ℕ) : Cmd :=
  .seq (prims [.nconst (r + 48) 0, .nadd (r + 50) (r + 3) (r + 10)])
  (.seq (.whileN (r + 48) (r + 2) (fbBody r))
  (prims [.rconst r (1 / 2), .nadd (r + 51) r (r + 9), .ncast (r + 51) 1, .nadd (r + 51) (r + 51) (r + 9),
      .nconst (r + 52) 2, .op2 .add (r + 51) (r + 52) (r + 21), .nconst 2 0]))

/-- PRE^b: the set-up, the stages until one returns, the frame. -/
def preCmd (r : ℕ) : Cmd :=
  .seq (setupCmd r) (.seq (.whileN (r + 55) (r + 9) (stageCmd r)) (frameCmd r))

theorem chainCmd_pure (b one : ℕ) : ∀ k, CmdPure (chainCmd b one k)
  | 0 => trivial
  | k + 1 => ⟨chainCmd_pure b one k, trivial⟩

theorem preCmd_pure (r : ℕ) : CmdPure (preCmd r) := by
  simp [preCmd, setupCmd, stageCmd, iterCmd, testCmd, testBody, cutCmd, mvBody, baBody, r1Inner, r1Outer, frameCmd,
    fbBody, dotCmd, sfillCmd, naccCmd, prims, CmdPure, PrimPure, chainCmd_pure]

end AdversarialBco.Conj1Poly
