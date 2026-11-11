/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Poly.Transl
public import AdversarialBco.Poly.MachLang

@[expose] public section

/-!
# Theorem 1.3, the simulation S(P) and Lemma 8.14

`S(P)` replaces each instruction of `P` by a block that runs it on the memory shifted by `OFF`, with every `query`
replaced by the `m` inner products against the rows held in the memory and every `play` preceded by the addition of
the centre `a₀`. The blocks have lengths that depend on the kind of the instruction only (`blockLen`), and the block
of the instruction `p` starts at `τ p = blockStart o P p`, so a jump to `t` becomes a jump to `τ t`; for `t ≥ |P|`,
`τ t` is the end of the code, where the machine halts as `P` does.

Registers. `P` names registers below `r = regBound P` only (`regs_lt_regBound`, (M-a) of the proof of Lemma 8.14). `S(P)` uses the
registers `r, ..., r + 20`: the frame `r` (`OFF`), `r + 1` (`d`), `r + 2` (`m`), `r + 3` (`3`, the first cell of the
rows), `r + 4` (`F_b`, the cells `b'_i = b_i - ⟨a_i, a₀⟩`), `r + 5` (`F_a`, the cells of `a₀`), `r + 6` (`F_z`, the
scratch point), `r + 7` (`F_z + d`, the accumulator), `r + 8` (`F_z + d + 1`, the product), `r + 9` (`1`), `r + 10`
(`0`); the working registers `r + 11, ..., r + 14` (`t₁, ..., t₄`), `r + 15` (`p`), `r + 16` (`q`), `r + 17` (`y`),
`r + 18` (`i`), `r + 19` (`j`), `r + 20` (the flag of the query block).

* `blockCode r st τ ins`: the block of `ins` placed at the address `st`; the query and play blocks are the commands
  `queryCmd`, `playCmd` of the language of MachLang.lean compiled at `st`.
* `SimRel r τ a₀ Am bv s s'`: the relation (R1) to (R6) of the proof of Lemma 8.14 between a state `s` of `P` and a state `s'` of
  `S(P)`; `Framed` is (R6).
* Lemma 8.14, one lemma per kind of instruction (`sim_rconst`, ..., `sim_query`): from related states, the block of the
  instruction at `s.pc` runs in at most `blockSteps d m` steps to a state related to `step P w s`, and the rounds and
  the points stay those of `s'` before its last step (`BlockOK`).
* Corollary SIM-run (`lockstep`): the run of `S(P)` against `σ` is, block by block, the run of `P` against
  `transStrat σ a₀` on `K - a₀`.
-/

open MeasureTheory Matrix

namespace AdversarialBco.Conj1Poly

open AdversarialBco.RealRAM AdversarialBco.Poly.Mach

variable {d m : ℕ}

/-! ## Registers -/

/-- The registers an instruction names. -/
def Instr.regs : Instr → List ℕ
  | .rconst dst _ => [dst]
  | .op2 _ dst a b => [dst, a, b]
  | .op1 _ dst a => [dst, a]
  | .rjlt a b _ => [a, b]
  | .nconst dst _ => [dst]
  | .nadd dst a b => [dst, a, b]
  | .nsub dst a b => [dst, a, b]
  | .njlt a b _ => [a, b]
  | .ncast dst a => [dst, a]
  | .jmp _ => []
  | .spec _ dst src a b => [dst, src, a, b]
  | .query dst src => [dst, src]
  | .gauss dst => [dst]
  | .play dst src => [dst, src]

/-- `ρ_P`: at least `4`, and above every register that `P` names. -/
def regBound (P : List Instr) : ℕ := max 4 ((P.flatMap Instr.regs).foldr max 0 + 1)

theorem le_foldr_max {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact le_max_left _ _
    · exact (ih hx').trans (le_max_right _ _)

/-- (M-a): `P` names no register at or above `regBound P`. -/
theorem regs_lt_regBound {P : List Instr} {ins : Instr} (hins : ins ∈ P) {x : ℕ} (hx : x ∈ Instr.regs ins) :
    x < regBound P := by
  have mem_flat : x ∈ P.flatMap Instr.regs := List.mem_flatMap.2 ⟨ins, hins, hx⟩
  have hle := le_foldr_max mem_flat
  unfold regBound
  omega

/-! ## The blocks -/

/-- The play block: the scratch point `z = y + a₀`, then `play` of `z`, the observation to the shifted cell. -/
def playCmd (r dst src : ℕ) : Cmd :=
  .seq (prims [.nadd (r + 17) src r, .nadd (r + 11) dst r, .nsub (r + 19) (r + 19) (r + 19)])
    (.seq
      (.whileN (r + 19) (r + 1)
        (prims [.nadd (r + 15) (r + 17) (r + 19), .nadd (r + 16) (r + 5) (r + 19), .nadd (r + 12) (r + 6) (r + 19),
          .op2 .add (r + 12) (r + 15) (r + 16), .nadd (r + 19) (r + 19) (r + 9)]))
      (.prim (.play (r + 11) (r + 6))))

/-- The query block: for each row `i`, the accumulator receives `⟨a_i, y⟩` and the row fails if `b'_i < ⟨a_i, y⟩`
(the flag is cleared and the loop left); then the answer, `1` if the flag is set, else `0`, goes to the shifted
cell, after every read of the point. -/
def queryCmd (r dst src : ℕ) : Cmd :=
  .seq (prims [.nadd (r + 17) src r, .nadd (r + 11) dst r, .nadd (r + 15) (r + 3) (r + 10),
      .nadd (r + 16) (r + 4) (r + 10), .nsub (r + 18) (r + 18) (r + 18), .nadd (r + 20) (r + 9) (r + 10)])
    (.seq
      (.whileN (r + 18) (r + 2)
        (.seq (prims [.rconst (r + 7) 0, .nsub (r + 19) (r + 19) (r + 19)])
          (.seq
            (.whileN (r + 19) (r + 1)
              (prims [.nadd (r + 12) (r + 15) (r + 19), .nadd (r + 13) (r + 17) (r + 19),
                .op2 .mul (r + 8) (r + 12) (r + 13), .op2 .add (r + 7) (r + 7) (r + 8),
                .nadd (r + 19) (r + 19) (r + 9)]))
            (.ifR (r + 16) (r + 7)
              (prims [.nsub (r + 20) (r + 20) (r + 20), .nadd (r + 18) (r + 2) (r + 10)])
              (prims [.nadd (r + 15) (r + 15) (r + 1), .nadd (r + 15) (r + 15) (r + 9),
                .nadd (r + 16) (r + 16) (r + 9), .nadd (r + 18) (r + 18) (r + 9)])))))
      (.ifN (r + 10) (r + 20) (.prim (.rconst (r + 11) 1)) (.prim (.rconst (r + 11) 0))))

/-- The block of `ins` at the address `st`, jumps relocated by `τ`. Real operands are shifted by `OFF` (register
`r`) into the registers `r + 11, ...`; natural instructions are kept. -/
def blockCode (r st : ℕ) (τ : ℕ → ℕ) : Instr → List Instr
  | .rconst dst q => [.nadd (r + 11) dst r, .rconst (r + 11) q]
  | .op2 o dst a b => [.nadd (r + 11) a r, .nadd (r + 12) b r, .nadd (r + 13) dst r, .op2 o (r + 13) (r + 11) (r + 12)]
  | .op1 o dst a => [.nadd (r + 11) a r, .nadd (r + 12) dst r, .op1 o (r + 12) (r + 11)]
  | .rjlt a b t => [.nadd (r + 11) a r, .nadd (r + 12) b r, .rjlt (r + 11) (r + 12) (τ t)]
  | .nconst dst c => [.nconst dst c]
  | .nadd dst a b => [.nadd dst a b]
  | .nsub dst a b => [.nsub dst a b]
  | .njlt a b t => [.njlt a b (τ t)]
  | .ncast dst a => [.nadd (r + 11) dst r, .ncast (r + 11) a]
  | .jmp t => [.jmp (τ t)]
  | .spec s dst src a b =>
    [.nadd (r + 11) dst r, .nadd (r + 12) src r, .nadd (r + 13) a r, .nadd (r + 14) b r,
      .spec s (r + 11) (r + 12) (r + 13) (r + 14)]
  | .gauss dst => [.nadd (r + 11) dst r, .gauss (r + 11)]
  | .query dst src => (queryCmd r dst src).compile st
  | .play dst src => (playCmd r dst src).compile st

/-- The length of a block, which depends on the kind of the instruction only. -/
def blockLen (ins : Instr) : ℕ := (blockCode 0 0 id ins).length

theorem queryCmd_len (r dst src : ℕ) : (queryCmd r dst src).len = (queryCmd 0 dst src).len := by
  unfold queryCmd
  simp [Cmd.len, prims]

theorem playCmd_len (r dst src : ℕ) : (playCmd r dst src).len = (playCmd 0 dst src).len := by
  unfold playCmd
  simp [Cmd.len, prims]

theorem blockCode_length (r st : ℕ) (τ : ℕ → ℕ) (ins : Instr) : (blockCode r st τ ins).length = blockLen ins := by
  cases ins
  case rconst => simp [blockCode, blockLen]
  case op2 => simp [blockCode, blockLen]
  case op1 => simp [blockCode, blockLen]
  case rjlt => simp [blockCode, blockLen]
  case nconst => simp [blockCode, blockLen]
  case nadd => simp [blockCode, blockLen]
  case nsub => simp [blockCode, blockLen]
  case njlt => simp [blockCode, blockLen]
  case ncast => simp [blockCode, blockLen]
  case jmp => simp [blockCode, blockLen]
  case spec => simp [blockCode, blockLen]
  case gauss => simp [blockCode, blockLen]
  case query =>
    simp [blockCode, blockLen]
    exact queryCmd_len r _ _
  case play =>
    simp [blockCode, blockLen]
    exact playCmd_len r _ _

/-- The address of the block of the instruction `p` when `S(P)` starts at `o` (the end of the code for `p ≥ |P|`). -/
def blockStart (o : ℕ) (P : List Instr) (p : ℕ) : ℕ := o + ((P.take p).map blockLen).sum

/-- The blocks of the instructions `ins :: rest`, the first at `st`. -/
def simCodeFrom (r : ℕ) (τ : ℕ → ℕ) : ℕ → List Instr → List Instr
  | _, [] => []
  | st, ins :: rest => blockCode r st τ ins ++ simCodeFrom r τ (st + blockLen ins) rest

/-- `S(P)` placed at the address `o`. -/
def simCode (r o : ℕ) (P : List Instr) : List Instr := simCodeFrom r (blockStart o P) o P

/-- `P_pol = PRE ++ S(P)`. -/
def polyProg (pre P : List Instr) : List Instr := pre ++ simCode (regBound P) pre.length P

theorem simCodeFrom_length (r : ℕ) (τ : ℕ → ℕ) : ∀ (st : ℕ) (L : List Instr),
    (simCodeFrom r τ st L).length = (L.map blockLen).sum
  | _, [] => rfl
  | st, ins :: rest => by
    simp only [simCodeFrom, List.length_append, blockCode_length, simCodeFrom_length r τ _ rest, List.map_cons,
      List.sum_cons]

theorem codeAt_append_left {l1 l2 l : List Instr} {o : ℕ} (h : CodeAt l2 o l) : CodeAt (l1 ++ l2) (l1.length + o) l :=
  fun i hi => by
  rw [Nat.add_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact h i hi

theorem simCodeFrom_codeAt (r : ℕ) (τ : ℕ → ℕ) : ∀ (st : ℕ) (L : List Instr) {p : ℕ} {ins : Instr},
    L[p]? = some ins →
      CodeAt (simCodeFrom r τ st L) ((L.take p).map blockLen).sum
        (blockCode r (st + ((L.take p).map blockLen).sum) τ ins)
  | _, [], _, _, h => by simp at h
  | st, a :: rest, 0, ins, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    intro i hi
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero, Nat.zero_add, simCodeFrom] at hi ⊢
    exact List.getElem?_append_left hi
  | st, a :: rest, p + 1, ins, h => by
    simp only [List.getElem?_cons_succ] at h
    have ih := simCodeFrom_codeAt r τ (st + blockLen a) rest h
    have h2 := codeAt_append_left (l1 := blockCode r st τ a) ih
    rw [blockCode_length] at h2
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, simCodeFrom]
    rw [← Nat.add_assoc st]
    exact h2

theorem queryCmd_no_query (r dst src a b st : ℕ) : Instr.query a b ∉ (queryCmd r dst src).compile st := by
  unfold queryCmd
  simp [Cmd.compile, prims, Prim.toInstr]

theorem playCmd_no_query (r dst src a b st : ℕ) : Instr.query a b ∉ (playCmd r dst src).compile st := by
  unfold playCmd
  simp [Cmd.compile, prims, Prim.toInstr]

theorem blockCode_no_query (r st : ℕ) (τ : ℕ → ℕ) (ins : Instr) (a b : ℕ) : Instr.query a b ∉ blockCode r st τ ins := by
  cases ins <;> simp [blockCode, queryCmd_no_query, playCmd_no_query]

theorem simCodeFrom_no_query (r : ℕ) (τ : ℕ → ℕ) : ∀ (st : ℕ) (L : List Instr) (a b : ℕ),
    Instr.query a b ∉ simCodeFrom r τ st L
  | _, [], _, _ => by simp [simCodeFrom]
  | st, ins :: rest, a, b => by
    simp only [simCodeFrom, List.mem_append, not_or]
    exact ⟨blockCode_no_query r st τ ins a b, simCodeFrom_no_query r τ _ rest a b⟩

theorem simCode_length (r o : ℕ) (P : List Instr) : (simCode r o P).length = (P.map blockLen).sum := by
  exact simCodeFrom_length r _ o P

theorem blockStart_succ (o : ℕ) (P : List Instr) {p : ℕ} {ins : Instr} (h : P[p]? = some ins) :
    blockStart o P (p + 1) = blockStart o P p + blockLen ins := by
  unfold blockStart
  rw [List.take_add_one, h, Option.toList_some]
  simp [List.map_append, List.sum_append]
  omega

theorem blockStart_ge (o : ℕ) (P : List Instr) {p : ℕ} (h : P.length ≤ p) :
    blockStart o P p = o + (P.map blockLen).sum := by
  unfold blockStart
  rw [List.take_of_length_le h]

/-- The block of the instruction `p` sits at `blockStart`. -/
theorem polyProg_codeAt (pre P : List Instr) {p : ℕ} {ins : Instr} (h : P[p]? = some ins) :
    CodeAt (polyProg pre P) (blockStart pre.length P p)
      (blockCode (regBound P) (blockStart pre.length P p) (blockStart pre.length P) ins) := by
  unfold polyProg simCode
  have := simCodeFrom_codeAt (regBound P) (blockStart pre.length P) pre.length P h
  have h2 := codeAt_append_left (l1 := pre) this
  simpa [blockStart] using h2

theorem polyProg_length (pre P : List Instr) :
    (polyProg pre P).length = pre.length + (P.map blockLen).sum := by
  unfold polyProg
  rw [List.length_append]
  rw [simCode_length]

/-- `S(P)` has no query. -/
theorem polyProg_queryFree {pre : List Instr} (hpre : QueryFree pre) (P : List Instr) :
    QueryFree (polyProg pre P) := by
  unfold polyProg simCode
  intro dst src hmem
  rcases List.mem_append.1 hmem with h | h
  · exact hpre dst src h
  · exact simCodeFrom_no_query _ _ _ _ dst src h

/-! ## The relation -/

/-- (R6): the state is framed at `a₀` for the data `(Am, bv)`. -/
structure Framed (r : ℕ) (a0 : E d) (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ) (s : State d) : Prop where
  dd : s.nreg (r + 1) = d
  mm : s.nreg (r + 2) = m
  rows : s.nreg (r + 3) = 3
  acc : s.nreg (r + 7) = s.nreg (r + 6) + d
  tmp : s.nreg (r + 8) = s.nreg (r + 6) + d + 1
  one : s.nreg (r + 9) = 1
  zero : s.nreg (r + 10) = 0
  lay1 : 3 + (d + 1) * m ≤ s.nreg (r + 4)
  lay2 : s.nreg (r + 4) + m ≤ s.nreg (r + 5)
  lay3 : s.nreg (r + 5) + d ≤ s.nreg (r + 6)
  lay4 : s.nreg (r + 6) + d + 2 ≤ s.nreg r
  cellA : ∀ (i : Fin m) (j : Fin d), s.mem (3 + (d + 1) * i + j) = (Am i j : ℝ)
  cellB : ∀ i : Fin m, s.mem (s.nreg (r + 4) + i) = (bv i : ℝ) - ∑ j, (Am i j : ℝ) * a0 j
  cellA0 : ∀ j : Fin d, s.mem (s.nreg (r + 5) + j) = a0 j

/-- The relation between a state `s` of `P` and a state `s'` of `S(P)`, (R1) to (R6)
of the proof of Lemma 8.14. -/
structure SimRel (r : ℕ) (τ : ℕ → ℕ) (a0 : E d) (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ)
    (s s' : State d) : Prop where
  nreg : ∀ i < r, s'.nreg i = s.nreg i
  mem : ∀ c, s'.mem (s'.nreg r + c) = s.mem c
  draws : s'.draws = s.draws
  rounds : s'.rounds = s.rounds
  pts : ∀ u < s.rounds, s'.pts u = s.pts u + a0
  pc : s'.pc = τ s.pc
  framed : Framed r a0 Am bv s'

/-- The bound on the steps of a block. -/
def blockSteps (d m : ℕ) : ℕ := 7 * d * m + 12 * m + 7 * d + 12

/-- The conclusion of Lemma 8.14 for one block: from `s'`, at most `blockSteps d m` steps of `Q` in the world `w'`
reach a state related to `step P w s`, the rounds and the points of `s'` kept before the last of them. -/
def BlockOK (r : ℕ) (τ : ℕ → ℕ) (a0 : E d) (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ) (P Q : List Instr)
    (w w' : World d) (s s' : State d) : Prop :=
  ∃ k, 1 ≤ k ∧ k ≤ blockSteps d m ∧ SimRel r τ a0 Am bv (step P w s) (run Q w' s' k) ∧
    ∀ k' < k, (run Q w' s' k').rounds = s'.rounds ∧ (run Q w' s' k').pts = s'.pts

/-- A `whileN` loop under an invariant `I t` after `t` turns: while the test holds, `t < N`, and the body keeps the
invariant within `Kb` steps. -/
theorem exec_whileN_inv {w : World d} {a b : ℕ} {c : Cmd} (I : ℕ → State d → Prop) (N Kb : ℕ)
    (hbound : ∀ t s, I t s → condN s a b → t < N)
    (hbody : ∀ t s, I t s → condN s a b → ∃ k s', k ≤ Kb ∧ Exec w c s k s' ∧ I (t + 1) s') :
    ∀ t s, I t s → ∃ k s' t', k ≤ (N - t) * (Kb + 2) + 2 ∧ Exec w (.whileN a b c) s k s' ∧ I t' s' ∧
      ¬ condN s' a b := by
  suffices H : ∀ n t s, N - t = n → I t s → ∃ k s' t', k ≤ (N - t) * (Kb + 2) + 2 ∧
      Exec w (.whileN a b c) s k s' ∧ I t' s' ∧ ¬ condN s' a b from fun t s h => H _ t s rfl h
  intro n
  induction n with
  | zero =>
    intro t s hn hI
    by_cases hc : condN s a b
    · have := hbound t s hI hc; omega
    · exact ⟨2, s, t, by omega, Exec.whileN_f hc, hI, hc⟩
  | succ n ih =>
    intro t s hn hI
    by_cases hc : condN s a b
    · obtain ⟨k, s1, hk, he, hI1⟩ := hbody t s hI hc
      obtain ⟨k', s2, t', hk', he', hI2, hc2⟩ := ih (t + 1) s1 (by omega) hI1
      refine ⟨k + 2 + k', s2, t', ?_, Exec.whileN_t hc he he', hI2, hc2⟩
      have : N - t = (N - (t + 1)) + 1 := by omega
      rw [this, Nat.add_mul, one_mul]
      omega
    · exact ⟨2, s, t, by omega, Exec.whileN_f hc, hI, hc⟩

/-- A step that keeps the rounds keeps the points. -/
theorem step_pts_of_rounds (P : List Instr) (w : World d) (s : State d) (h : (step P w s).rounds = s.rounds) :
    (step P w s).pts = s.pts := by
  unfold step at h ⊢
  rcases hP : P[s.pc]? with _ | ins
  · rfl
  · rw [hP] at h
    cases ins <;> simp_all <;> split_ifs <;> rfl

/-- If the rounds after `K` steps are those at the start, the rounds and the points are kept at every step up to
`K`. -/
theorem kept_of_rounds (P : List Instr) (w : World d) (s : State d) {K : ℕ} (h : (run P w s K).rounds = s.rounds) :
    ∀ k ≤ K, (run P w s k).rounds = s.rounds ∧ (run P w s k).pts = s.pts := by
  have hr : ∀ k ≤ K, (run P w s k).rounds = s.rounds := fun k hk =>
    le_antisymm ((run_rounds_mono P w s hk).trans h.le) (run_rounds_mono P w s (Nat.zero_le k))
  intro k hk
  refine ⟨hr k hk, ?_⟩
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 := hr (k + 1) hk
    have h0 := hr k (by omega)
    have e : run P w s (k + 1) = step P w (run P w s k) := by
      simp only [run]; rw [Function.iterate_succ_apply']
    rw [e] at h1 ⊢
    rw [step_pts_of_rounds P w _ (h1.trans h0.symm), ih (by omega)]


/-- A state related to `t` from the frame of `s'`: the registers below `r` those of `t`, the frame registers and the
cells below `F_z` those of `s'`, the shifted memory that of `t`. -/
theorem SimRel.of_frame {r : ℕ} {τ : ℕ → ℕ} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {s s' t t' : State d} (hrel : SimRel r τ a0 Am bv s s')
    (hn : ∀ i < r, t'.nreg i = t.nreg i) (hfr : ∀ i, r ≤ i → i ≤ r + 10 → t'.nreg i = s'.nreg i)
    (hm : ∀ c, t'.mem (s'.nreg r + c) = t.mem c) (hlow : ∀ c < s'.nreg (r + 6), t'.mem c = s'.mem c)
    (hd : t'.draws = t.draws) (hr : t'.rounds = t.rounds) (hp : ∀ u < t.rounds, t'.pts u = t.pts u + a0)
    (hpc : t'.pc = τ t.pc) : SimRel r τ a0 Am bv t t' := by
  have fr := hrel.framed
  have e : ∀ k, k ≤ 10 → t'.nreg (r + k) = s'.nreg (r + k) := fun k hk => hfr (r + k) (by omega) (by omega)
  have e0 : t'.nreg r = s'.nreg r := hfr r le_rfl (by omega)
  have l1 := fr.lay1; have l2 := fr.lay2; have l3 := fr.lay3; have l4 := fr.lay4
  refine ⟨hn, fun c => by rw [e0]; exact hm c, hd, hr, hp, hpc, ?_⟩
  refine ⟨by rw [e 1 (by omega)]; exact fr.dd, by rw [e 2 (by omega)]; exact fr.mm,
    by rw [e 3 (by omega)]; exact fr.rows, by rw [e 7 (by omega), e 6 (by omega)]; exact fr.acc,
    by rw [e 8 (by omega), e 6 (by omega)]; exact fr.tmp, by rw [e 9 (by omega)]; exact fr.one,
    by rw [e 10 (by omega)]; exact fr.zero, by rw [e 4 (by omega)]; exact fr.lay1,
    by rw [e 4 (by omega), e 5 (by omega)]; exact fr.lay2, by rw [e 5 (by omega), e 6 (by omega)]; exact fr.lay3,
    by rw [e 6 (by omega), e0]; exact fr.lay4, fun i j => ?_, fun i => ?_, fun j => ?_⟩
  · have hij : (d + 1) * (i : ℕ) + j < (d + 1) * m := by
      have := Nat.mul_le_mul_left (d + 1) (Nat.succ_le_of_lt i.2)
      rw [Nat.mul_succ] at this
      omega
    rw [hlow _ (by omega)]
    exact fr.cellA i j
  · rw [e 4 (by omega), hlow _ (by omega)]
    exact fr.cellB i
  · rw [e 5 (by omega), hlow _ (by omega)]
    exact fr.cellA0 j


/-! ## The query block -/

/-- What every state of the query block keeps of `s'`: the registers up to `r + 10`, the point and answer addresses
`yA`, `DA` in `r + 17`, `r + 11`, the memory outside the accumulator and product cells, the draws, rounds, points. -/
def QBase (r : ℕ) (s' S : State d) (yA DA : ℕ) : Prop :=
  (∀ i ≤ r + 10, S.nreg i = s'.nreg i) ∧ S.nreg (r + 17) = yA ∧ S.nreg (r + 11) = DA ∧
    (∀ c, c ≠ s'.nreg (r + 6) + d → c ≠ s'.nreg (r + 6) + d + 1 → S.mem c = s'.mem c) ∧
    S.draws = s'.draws ∧ S.rounds = s'.rounds ∧ S.pts = s'.pts

/-- `⟨a_t, y⟩` over the first `j` coordinates, read in the memory of `s'`. -/
noncomputable def qRow (s' : State d) (yA t j : ℕ) : ℝ :=
  ∑ j' ∈ Finset.range j, s'.mem (3 + (d + 1) * t + j') * s'.mem (yA + j')

/-- The state of the inner loop of the query block at row `t` after `j` turns. -/
def QInner (r : ℕ) (s' S : State d) (yA DA t j : ℕ) : Prop :=
  QBase r s' S yA DA ∧ S.nreg (r + 20) = 1 ∧ S.nreg (r + 18) = t ∧ S.nreg (r + 15) = 3 + (d + 1) * t ∧
    S.nreg (r + 16) = s'.nreg (r + 4) + t ∧ S.nreg (r + 19) = j ∧ j ≤ d ∧
    S.mem (s'.nreg (r + 6) + d) = qRow s' yA t j

theorem row_cell_lt {d m t j : ℕ} (ht : t < m) (hj : j < d) : (d + 1) * t + j < (d + 1) * m := by
  have := Nat.mul_le_mul_left (d + 1) (Nat.succ_le_of_lt ht)
  rw [Nat.mul_succ] at this
  omega

theorem qInner_body {r yA DA t j : ℕ} {w : World d} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {s' S : State d} (fr : Framed r a0 Am bv s') (ht : t < m) (hyA : s'.nreg r ≤ yA)
    (hI : QInner r s' S yA DA t j) (hj : j < d) :
    ∃ S1, Exec w (prims [.nadd (r + 12) (r + 15) (r + 19), .nadd (r + 13) (r + 17) (r + 19),
      .op2 .mul (r + 8) (r + 12) (r + 13), .op2 .add (r + 7) (r + 7) (r + 8), .nadd (r + 19) (r + 19) (r + 9)])
      S 5 S1 ∧ QInner r s' S1 yA DA t (j + 1) := by
  refine ⟨_, exec_prims w _ S, ?_⟩
  obtain ⟨⟨hn, hy, hD, hm, hdr, hro, hpt⟩, h20, h18, h15, h16, h19, hjd, hacc⟩ := hI
  have l1 := fr.lay1; have l2 := fr.lay2; have l3 := fr.lay3; have l4 := fr.lay4
  have hrc := row_cell_lt ht hj
  have n7 := hn (r + 7) (by omega); have n8 := hn (r + 8) (by omega); have n9 := hn (r + 9) (by omega)
  rw [fr.acc] at n7; rw [fr.tmp] at n8; rw [fr.one] at n9
  simp only [List.foldl, Prim.exec, Op2.eval]
  refine ⟨⟨fun i hi => ?_, ?_, ?_, fun c h1 h2 => ?_, hdr, hro, hpt⟩, ?_, ?_, ?_, ?_, ?_, by omega, ?_⟩
  · simp only [Function.update_apply]
    split_ifs <;> first | omega | exact hn i hi
  · simp [hy]
  · simp [hD]
  · simp [Function.update_apply, h15, h19, hy, n7, n8]
    simp only [h1, h2, ↓reduceIte]
    exact hm c h1 h2
  · simp [h20]
  · simp [h18]
  · simp [h15]
  · simp [h16]
  · simp [h19, n9]
  · simp [h15, h19, hy, n7, n8]
    rw [hacc, hm _ (by omega) (by omega), hm _ (by omega) (by omega)]
    simp [qRow, Finset.sum_range_succ]


/-- The row `i` fails at the point: `b'_i < ⟨a_i, y⟩`. -/
def QFail (r : ℕ) (s' : State d) (yA i : ℕ) : Prop := s'.mem (s'.nreg (r + 4) + i) < qRow s' yA i d

/-- The state of the outer loop of the query block after `t` turns. -/
def QOuter (r : ℕ) (s' S : State d) (yA DA t : ℕ) : Prop :=
  QBase r s' S yA DA ∧
    ((S.nreg (r + 20) = 1 ∧ S.nreg (r + 18) = t ∧ S.nreg (r + 15) = 3 + (d + 1) * t ∧
        S.nreg (r + 16) = s'.nreg (r + 4) + t ∧ t ≤ s'.nreg (r + 2) ∧ ∀ i < t, ¬ QFail r s' yA i) ∨
      (S.nreg (r + 20) = 0 ∧ S.nreg (r + 18) = s'.nreg (r + 2) ∧ ∃ i < s'.nreg (r + 2), QFail r s' yA i))

/-- The inner loop of the query block. -/
def qInnerCmd (r : ℕ) : Cmd :=
  .whileN (r + 19) (r + 1)
    (prims [.nadd (r + 12) (r + 15) (r + 19), .nadd (r + 13) (r + 17) (r + 19),
      .op2 .mul (r + 8) (r + 12) (r + 13), .op2 .add (r + 7) (r + 7) (r + 8), .nadd (r + 19) (r + 19) (r + 9)])

/-- The body of the outer loop of the query block. -/
def qOuterBody (r : ℕ) : Cmd :=
  .seq (prims [.rconst (r + 7) 0, .nsub (r + 19) (r + 19) (r + 19)])
    (.seq (qInnerCmd r)
      (.ifR (r + 16) (r + 7)
        (prims [.nsub (r + 20) (r + 20) (r + 20), .nadd (r + 18) (r + 2) (r + 10)])
        (prims [.nadd (r + 15) (r + 15) (r + 1), .nadd (r + 15) (r + 15) (r + 9),
          .nadd (r + 16) (r + 16) (r + 9), .nadd (r + 18) (r + 18) (r + 9)])))

theorem qOuter_body {r yA DA t : ℕ} {w : World d} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {s' S : State d} (fr : Framed r a0 Am bv s') (hyA : s'.nreg r ≤ yA)
    (hI : QOuter r s' S yA DA t) (hc : condN S (r + 18) (r + 2)) :
    ∃ k S1, k ≤ 7 * d + 10 ∧ Exec w (qOuterBody r) S k S1 ∧ QOuter r s' S1 yA DA (t + 1) := by
  obtain ⟨⟨hn, hy, hD, hm, hdr, hro, hpt⟩, hI⟩ := hI
  have l1 := fr.lay1; have l2 := fr.lay2; have l3 := fr.lay3; have l4 := fr.lay4
  have n1 := hn (r + 1) (by omega); have n2 := hn (r + 2) (by omega); have n7 := hn (r + 7) (by omega)
  have n8 := hn (r + 8) (by omega); have n9 := hn (r + 9) (by omega); have n10 := hn (r + 10) (by omega)
  rw [fr.dd] at n1; rw [fr.mm] at n2; rw [fr.acc] at n7; rw [fr.tmp] at n8; rw [fr.one] at n9
  rw [fr.zero] at n10
  unfold condN at hc
  rw [n2] at hc
  rcases hI with ⟨h20, h18, h15, h16, htm, hpass⟩ | ⟨h20, h18, hfail⟩
  swap
  · rw [h18, fr.mm] at hc; exact absurd hc (lt_irrefl _)
  rw [h18] at hc
  -- the two primitives: the accumulator to `0`, `j` to `0`
  have e0 := exec_prims w [.rconst (r + 7) 0, .nsub (r + 19) (r + 19) (r + 19)] S
  set S0 := [Prim.rconst (r + 7) 0, .nsub (r + 19) (r + 19) (r + 19)].foldl (fun s p => p.exec w s) S with hS0
  have hI0 : QInner r s' S0 yA DA t 0 := by
    simp only [hS0, List.foldl, Prim.exec]
    refine ⟨⟨fun i hi => ?_, ?_, ?_, fun c h1 h2 => ?_, hdr, hro, hpt⟩, ?_, ?_, ?_, ?_, ?_, by omega, ?_⟩
    · simp only [Function.update_apply]
      split_ifs <;> first | omega | exact hn i hi
    · simp [hy]
    · simp [hD]
    · simp [n7, h1]
      exact hm c h1 h2
    · simp [h20]
    · simp [h18]
    · simp [h15]
    · simp [h16]
    · simp
    · simp [n7, qRow]
  -- the inner loop
  obtain ⟨k1, S2, j', hk1, e1, hI2, hc2⟩ := exec_whileN_inv (w := w) (a := r + 19) (b := r + 1)
    (c := prims [.nadd (r + 12) (r + 15) (r + 19), .nadd (r + 13) (r + 17) (r + 19),
      .op2 .mul (r + 8) (r + 12) (r + 13), .op2 .add (r + 7) (r + 7) (r + 8), .nadd (r + 19) (r + 19) (r + 9)])
    (fun j S => QInner r s' S yA DA t j) d 5
    (fun j S hI hc => by
      obtain ⟨⟨hn', -⟩, -, -, -, -, h19, -⟩ := hI
      unfold condN at hc
      rwa [h19, hn' (r + 1) (by omega), fr.dd] at hc)
    (fun j S hI hc' => by
      have hj : j < d := by
        obtain ⟨⟨hn', -⟩, -, -, -, -, h19, -⟩ := hI
        unfold condN at hc'
        rwa [h19, hn' (r + 1) (by omega), fr.dd] at hc'
      obtain ⟨S1, he, hI1⟩ := qInner_body fr hc hyA hI hj
      exact ⟨5, S1, le_rfl, he, hI1⟩) 0 S0 hI0
  obtain ⟨⟨hn2, hy2, hD2, hm2, hdr2, hro2, hpt2⟩, h20', h18', h15', h16', h19', hj', hacc'⟩ := hI2
  have hjd : j' = d := by
    unfold condN at hc2
    rw [h19', hn2 (r + 1) (by omega), fr.dd] at hc2
    omega
  rw [hjd] at hacc'
  have n7' := hn2 (r + 7) (by omega); rw [fr.acc] at n7'
  have n9' := hn2 (r + 9) (by omega); rw [fr.one] at n9'
  have n1' := hn2 (r + 1) (by omega); rw [fr.dd] at n1'
  have n2' := hn2 (r + 2) (by omega); rw [fr.mm] at n2'
  have n10' := hn2 (r + 10) (by omega); rw [fr.zero] at n10'
  have hcell : S2.mem (s'.nreg (r + 4) + t) = s'.mem (s'.nreg (r + 4) + t) := hm2 _ (by omega) (by omega)
  by_cases hf : QFail r s' yA t
  · -- the row fails
    have hcR : condR S2 (r + 16) (r + 7) := by
      unfold condR; rw [h16', n7', hacc', hcell]; exact hf
    have e2 := exec_prims w [.nsub (r + 20) (r + 20) (r + 20), .nadd (r + 18) (r + 2) (r + 10)] S2
    refine ⟨2 + (k1 + (2 + 1)), _, by omega,
      Exec.seq e0 (Exec.seq e1 (Exec.ifR_t hcR e2)), ?_⟩
    simp only [List.foldl, Prim.exec]
    refine ⟨⟨fun i hi => ?_, ?_, ?_, fun c h1 h2 => ?_, hdr2, hro2, hpt2⟩, Or.inr ⟨?_, ?_, t, ?_, hf⟩⟩
    · simp only [Function.update_apply]
      split_ifs <;> first | omega | exact hn2 i hi
    · simp [hy2]
    · simp [hD2]
    · exact hm2 c h1 h2
    · simp
    · simp [n2', n10', fr.mm]
    · rw [fr.mm]; exact hc
  · -- the row passes
    have hcR : ¬ condR S2 (r + 16) (r + 7) := by
      unfold condR; rw [h16', n7', hacc', hcell]; exact hf
    have e2 := exec_prims w [.nadd (r + 15) (r + 15) (r + 1), .nadd (r + 15) (r + 15) (r + 9),
      .nadd (r + 16) (r + 16) (r + 9), .nadd (r + 18) (r + 18) (r + 9)] S2
    refine ⟨2 + (k1 + (4 + 2)), _, by omega,
      Exec.seq e0 (Exec.seq e1 (Exec.ifR_f hcR e2)), ?_⟩
    simp only [List.foldl, Prim.exec]
    refine ⟨⟨fun i hi => ?_, ?_, ?_, fun c h1 h2 => ?_, hdr2, hro2, hpt2⟩, Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simp only [Function.update_apply]
      split_ifs <;> first | omega | exact hn2 i hi
    · simp [hy2]
    · simp [hD2]
    · exact hm2 c h1 h2
    · simp [h20']
    · simp [h18', n9']
    · simp [h15', n1', n9']; ring
    · simp [h16', n9']; ring
    · rw [fr.mm]; omega
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact hpass i hi
      · exact hf


theorem queryCmd_eq (r dst src : ℕ) :
    queryCmd r dst src =
      .seq (prims [.nadd (r + 17) src r, .nadd (r + 11) dst r, .nadd (r + 15) (r + 3) (r + 10),
          .nadd (r + 16) (r + 4) (r + 10), .nsub (r + 18) (r + 18) (r + 18), .nadd (r + 20) (r + 9) (r + 10)])
        (.seq (.whileN (r + 18) (r + 2) (qOuterBody r))
          (.ifN (r + 10) (r + 20) (.prim (.rconst (r + 11) 1)) (.prim (.rconst (r + 11) 0)))) := rfl

open Classical in
/-- The query block from a framed state: the answer `1` if no row fails, else `0`, at `DA`; nothing else changed but
the accumulator and product cells and the working registers. -/
theorem query_exec {r dst src : ℕ} {w : World d} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {s' : State d} (fr : Framed r a0 Am bv s') (hdst : dst < r) :
    ∃ k S', 6 ≤ k ∧ k ≤ 7 * d * m + 12 * m + 11 ∧ Exec w (queryCmd r dst src) s' k S' ∧
      (∀ i ≤ r + 10, S'.nreg i = s'.nreg i) ∧
      (∀ c, c ≠ s'.nreg (r + 6) + d → c ≠ s'.nreg (r + 6) + d + 1 → c ≠ s'.nreg dst + s'.nreg r →
        S'.mem c = s'.mem c) ∧
      S'.mem (s'.nreg dst + s'.nreg r) =
        (if ∀ i < m, ¬ QFail r s' (s'.nreg src + s'.nreg r) i then 1 else 0) ∧
      S'.draws = s'.draws ∧ S'.rounds = s'.rounds ∧ S'.pts = s'.pts := by
  have l1 := fr.lay1; have l2 := fr.lay2; have l3 := fr.lay3; have l4 := fr.lay4
  rw [queryCmd_eq]
  have e0 := exec_prims w [.nadd (r + 17) src r, .nadd (r + 11) dst r, .nadd (r + 15) (r + 3) (r + 10),
    .nadd (r + 16) (r + 4) (r + 10), .nsub (r + 18) (r + 18) (r + 18), .nadd (r + 20) (r + 9) (r + 10)] s'
  set S0 := [Prim.nadd (r + 17) src r, .nadd (r + 11) dst r, .nadd (r + 15) (r + 3) (r + 10),
    .nadd (r + 16) (r + 4) (r + 10), .nsub (r + 18) (r + 18) (r + 18), .nadd (r + 20) (r + 9) (r + 10)].foldl
      (fun s p => p.exec w s) s' with hS0
  have hI0 : QOuter r s' S0 (s'.nreg src + s'.nreg r) (s'.nreg dst + s'.nreg r) 0 := by
    simp only [hS0, List.foldl, Prim.exec]
    refine ⟨⟨fun i hi => ?_, ?_, ?_, fun c _ _ => rfl, rfl, rfl, rfl⟩, Or.inl ⟨?_, ?_, ?_, ?_, by omega, by simp⟩⟩
    · dsimp only
      rw [Function.update_of_ne (show i ≠ r + 20 by omega), Function.update_of_ne (show i ≠ r + 18 by omega),
        Function.update_of_ne (show i ≠ r + 16 by omega), Function.update_of_ne (show i ≠ r + 15 by omega),
        Function.update_of_ne (show i ≠ r + 11 by omega), Function.update_of_ne (show i ≠ r + 17 by omega)]
    · simp [Function.update_apply]
    · simp [show dst ≠ r + 17 by omega]
    · simp [fr.one, fr.zero]
    · simp
    · simp [fr.rows, fr.zero]
    · simp [fr.zero]
  obtain ⟨k2, S2, t', hk2, e2, hI2, hc2⟩ := exec_whileN_inv (w := w) (a := r + 18) (b := r + 2) (c := qOuterBody r)
    (fun t S => QOuter r s' S (s'.nreg src + s'.nreg r) (s'.nreg dst + s'.nreg r) t) m (7 * d + 10)
    (fun t S hI hc => by
      obtain ⟨⟨hn', -⟩, ⟨-, h18, -⟩ | ⟨-, h18, -⟩⟩ := hI <;> unfold condN at hc <;>
        rw [h18, hn' (r + 2) (by omega), fr.mm] at hc
      · exact hc
      · exact absurd hc (lt_irrefl _))
    (fun t S hI hc => qOuter_body fr (by omega) hI hc) 0 S0 hI0
  obtain ⟨⟨hn2, hy2, hD2, hm2, hdr2, hro2, hpt2⟩, hI2⟩ := hI2
  have n10 := hn2 (r + 10) (by omega); rw [fr.zero] at n10
  have hcost : (m - 0) * (7 * d + 10 + 2) + 2 = 7 * d * m + 12 * m + 2 := by rw [Nat.sub_zero]; ring
  rcases hI2 with ⟨h20, h18, -, -, htm, hpass⟩ | ⟨h20, h18, hfail⟩
  · -- every row passed
    have ht : t' = m := by
      unfold condN at hc2; rw [h18, hn2 (r + 2) (by omega), fr.mm] at hc2; rw [fr.mm] at htm; omega
    subst ht
    have hcN : condN S2 (r + 10) (r + 20) := by unfold condN; rw [n10, h20]; omega
    refine ⟨6 + (k2 + (1 + 1)), _, by omega, by omega, Exec.seq e0 (Exec.seq e2 (Exec.ifN_t hcN (Exec.prim _ S2))),
      fun i hi => hn2 i hi, fun c h1 h2 h3 => ?_, ?_, hdr2, hro2, hpt2⟩
    · simp only [Prim.exec, Function.update_apply, hD2, h3, ↓reduceIte]
      exact hm2 c h1 h2
    · simp only [Prim.exec, Function.update_apply, hD2, ↓reduceIte]
      split_ifs
      norm_num
  · -- a row failed
    have hcN : ¬ condN S2 (r + 10) (r + 20) := by unfold condN; rw [n10, h20]; omega
    refine ⟨6 + (k2 + (1 + 2)), _, by omega, by omega, Exec.seq e0 (Exec.seq e2 (Exec.ifN_f hcN (Exec.prim _ S2))),
      fun i hi => hn2 i hi, fun c h1 h2 h3 => ?_, ?_, hdr2, hro2, hpt2⟩
    · simp only [Prim.exec, Function.update_apply, hD2, h3, ↓reduceIte]
      exact hm2 c h1 h2
    · simp only [Prim.exec, Function.update_apply, hD2, ↓reduceIte]
      obtain ⟨i, hi, hf⟩ := hfail
      rw [fr.mm] at hi
      split_ifs with h
      · exact absurd hf (h i hi)
      · norm_num

/-! ## The play block -/

/-- The state of the loop of the play block after `j` turns: the scratch cells `F_z + j'`, `j' < j`, hold
`y_{j'} + a₀_{j'}`, nothing else changed but the working registers. -/
def PInv (r : ℕ) (s' S : State d) (yA DA j : ℕ) : Prop :=
  (∀ i ≤ r + 10, S.nreg i = s'.nreg i) ∧ S.nreg (r + 17) = yA ∧ S.nreg (r + 11) = DA ∧ S.nreg (r + 19) = j ∧
    j ≤ d ∧ (∀ c, (c < s'.nreg (r + 6) ∨ s'.nreg (r + 6) + j ≤ c) → S.mem c = s'.mem c) ∧
    (∀ j' < j, S.mem (s'.nreg (r + 6) + j') = s'.mem (yA + j') + s'.mem (s'.nreg (r + 5) + j')) ∧
    S.draws = s'.draws ∧ S.rounds = s'.rounds ∧ S.pts = s'.pts

theorem pInv_body {r yA DA j : ℕ} {w : World d} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {s' S : State d} (fr : Framed r a0 Am bv s') (hyA : s'.nreg r ≤ yA)
    (hI : PInv r s' S yA DA j) (hj : j < d) :
    ∃ S1, Exec w (prims [.nadd (r + 15) (r + 17) (r + 19), .nadd (r + 16) (r + 5) (r + 19),
      .nadd (r + 12) (r + 6) (r + 19), .op2 .add (r + 12) (r + 15) (r + 16), .nadd (r + 19) (r + 19) (r + 9)])
      S 5 S1 ∧ PInv r s' S1 yA DA (j + 1) := by
  refine ⟨_, exec_prims w _ S, ?_⟩
  obtain ⟨hn, hy, hD, h19, hjd, hm, hz, hdr, hro, hpt⟩ := hI
  have l3 := fr.lay3; have l4 := fr.lay4
  have n5 := hn (r + 5) (by omega); have n6 := hn (r + 6) (by omega); have n9 := hn (r + 9) (by omega)
  rw [fr.one] at n9
  simp only [List.foldl, Prim.exec, Op2.eval]
  refine ⟨fun i hi => ?_, ?_, ?_, ?_, by omega, fun c hc => ?_, fun j' hj' => ?_, hdr, hro, hpt⟩
  · simp only [Function.update_apply]
    split_ifs <;> first | omega | exact hn i hi
  · simp [hy]
  · simp [hD]
  · simp [h19, n9]
  · simp only [Function.update_apply]
    simp [n6, h19]
    split_ifs with h
    · exact absurd h (by omega)
    · exact hm c (by omega)
  · simp [Function.update_apply, n6, n5, h19, hy]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
    · split_ifs with h
      · exact absurd h (by omega)
      · exact hz j' hj'
    · rw [hm _ (by omega), hm _ (by omega)]
      simp

/-! ## Lemma 8.14, one lemma per kind of instruction

Common hypotheses: the instruction `ins` of `P` at `s.pc` names registers below `r`; its block sits at `τ s.pc` in
`Q`, and the next block at `τ (s.pc + 1)`; `s` and `s'` are related. -/

/-- A block of primitives from related states (the straight-line blocks): it runs in `l.length` steps, and the
rounds and the points are kept before the last of them. -/
theorem sim_rconst_aux {r : ℕ} {τ : ℕ → ℕ} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {P Q : List Instr} {w w' : World d} {s s' : State d} (l : List Prim) (hl1 : 1 ≤ l.length)
    (hl : l.length ≤ blockSteps d m) (hQ : CodeAt Q s'.pc ((prims l).compile s'.pc))
    (hrnd : (l.foldl (fun s p => p.exec w' s) s').rounds = s'.rounds)
    (hrel : SimRel r τ a0 Am bv (step P w s) (atPc (l.foldl (fun s p => p.exec w' s) s') (s'.pc + l.length))) :
    BlockOK r τ a0 Am bv P Q w w' s s' := by
  have hlen : ∀ l : List Prim, (prims l).len = l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons p l ih => simp only [prims, Cmd.len, ih, List.length_cons]; omega
  have hrun : run Q w' s' l.length = atPc (l.foldl (fun s p => p.exec w' s) s') (s'.pc + l.length) := by
    have := exec_sim (exec_prims w' l s') s'.pc hQ
    rw [atPc_self, hlen] at this
    exact this
  refine ⟨l.length, hl1, hl, by rw [hrun]; exact hrel, fun k' hk' =>
    kept_of_rounds Q w' s' (K := l.length) (by rw [hrun]; exact hrnd) k' hk'.le⟩

theorem sim_rconst {r : ℕ} {τ : ℕ → ℕ} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {P Q : List Instr} {w w' : World d} {s s' : State d} {dst : ℕ} {q : ℚ} (hreg : dst < r)
    (hP : P[s.pc]? = some (.rconst dst q)) (hQ : CodeAt Q (τ s.pc) (blockCode r (τ s.pc) τ (.rconst dst q)))
    (hnext : τ (s.pc + 1) = τ s.pc + blockLen (.rconst dst q)) (hrel : SimRel r τ a0 Am bv s s') :
    BlockOK r τ a0 Am bv P Q w w' s s' := by
  have fr := hrel.framed
  have l3 := fr.lay3; have l4 := fr.lay4
  have hdst' := hrel.nreg dst hreg
  have hQ' : CodeAt Q s'.pc ((prims [.nadd (r + 11) dst r, .rconst (r + 11) q]).compile s'.pc) := by
    rw [hrel.pc]; exact hQ
  have hstep : step P w s = { s with pc := s.pc + 1, mem := Function.update s.mem (s.nreg dst) q } := by
    unfold step; rw [hP]
  refine sim_rconst_aux _ (by simp) (by simp only [List.length_cons, List.length_nil, blockSteps]; omega) hQ' (by simp [List.foldl, Prim.exec]) ?_
  rw [hstep]
  refine SimRel.of_frame hrel (fun i hi => ?_) (fun i h1 h2 => ?_) (fun c => ?_) (fun c hc => ?_) ?_ ?_
    (fun u hu => ?_) ?_
  · simp only [List.foldl, Prim.exec, atPc, Function.update_apply]
    split_ifs <;> first | omega | exact hrel.nreg i hi
  · simp only [List.foldl, Prim.exec, atPc, Function.update_apply]
    split_ifs <;> omega
  · simp only [List.foldl, Prim.exec, atPc, Function.update_self]
    rw [hdst']
    by_cases hc : c = s.nreg dst
    · subst hc; rw [add_comm, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne hc]; exact hrel.mem c
  · simp only [List.foldl, Prim.exec, atPc, Function.update_self]
    rw [Function.update_of_ne (by omega)]
  · exact hrel.draws
  · show s'.rounds = s.rounds; exact hrel.rounds
  · exact hrel.pts u hu
  · show s'.pc + 2 = τ (s.pc + 1)
    rw [hnext, hrel.pc]; rfl

theorem sim_op2 {r : ℕ} {τ : ℕ → ℕ} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {P Q : List Instr} {w w' : World d} {s s' : State d} {o : Op2} {dst a b : ℕ} (hreg : dst < r ∧ a < r ∧ b < r)
    (hP : P[s.pc]? = some (.op2 o dst a b)) (hQ : CodeAt Q (τ s.pc) (blockCode r (τ s.pc) τ (.op2 o dst a b)))
    (hnext : τ (s.pc + 1) = τ s.pc + blockLen (.op2 o dst a b)) (hrel : SimRel r τ a0 Am bv s s') :
    BlockOK r τ a0 Am bv P Q w w' s s' := by
  obtain ⟨hdst, ha, hb⟩ := hreg
  have fr := hrel.framed
  have l3 := fr.lay3; have l4 := fr.lay4
  have hdst' := hrel.nreg dst hdst
  have ha' := hrel.nreg a ha
  have hb' := hrel.nreg b hb
  have nd : ∀ k, dst ≠ r + k := fun k => by omega
  have na : ∀ k, a ≠ r + k := fun k => by omega
  have nb : ∀ k, b ≠ r + k := fun k => by omega
  have hQ' : CodeAt Q s'.pc ((prims [.nadd (r + 11) a r, .nadd (r + 12) b r, .nadd (r + 13) dst r,
      .op2 o (r + 13) (r + 11) (r + 12)]).compile s'.pc) := by
    rw [hrel.pc]; exact hQ
  have hstep : step P w s = { s with pc := s.pc + 1, mem := Function.update s.mem (s.nreg dst) (o.eval (s.mem (s.nreg a)) (s.mem (s.nreg b))) } := by
    unfold step; rw [hP]
  refine sim_rconst_aux _ (by simp only [List.length_cons, List.length_nil]; omega) (by simp only [List.length_cons, List.length_nil, blockSteps]; omega) hQ' (by simp [List.foldl, Prim.exec]) ?_
  rw [hstep]
  refine SimRel.of_frame hrel (fun i hi => ?_) (fun i h1 h2 => ?_) (fun c => ?_) (fun c hc => ?_) ?_ ?_
    (fun u hu => ?_) ?_
  · have ni : ∀ k, i ≠ r + k := fun k => by omega
    simp [List.foldl, Prim.exec, atPc, Function.update_apply, ni, hrel.nreg i hi]
  · simp only [List.foldl, Prim.exec, atPc, Function.update_apply]
    split_ifs <;> omega
  · simp [List.foldl, Prim.exec, atPc, Function.update_apply, nd, nb, ha', hb', hdst']
    rw [add_comm (s.nreg a), add_comm (s.nreg b), hrel.mem, hrel.mem]
    by_cases hc : c = s.nreg dst
    · simp [hc, add_comm]
    · rw [ite_eq_right (by omega), ite_eq_right hc]; exact hrel.mem c
  · simp [List.foldl, Prim.exec, atPc, Function.update_apply, nd, nb, ha', hb', hdst']
    intro h; omega
  · exact hrel.draws
  · exact hrel.rounds
  · exact hrel.pts u hu
  · show s'.pc + 4 = τ (s.pc + 1)
    rw [hnext, hrel.pc]; rfl

theorem sim_op1 {r : ℕ} {τ : ℕ → ℕ} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {P Q : List Instr} {w w' : World d} {s s' : State d} {o : Op1} {dst a : ℕ} (hreg : dst < r ∧ a < r)
    (hP : P[s.pc]? = some (.op1 o dst a)) (hQ : CodeAt Q (τ s.pc) (blockCode r (τ s.pc) τ (.op1 o dst a)))
    (hnext : τ (s.pc + 1) = τ s.pc + blockLen (.op1 o dst a)) (hrel : SimRel r τ a0 Am bv s s') :
    BlockOK r τ a0 Am bv P Q w w' s s' := by
  obtain ⟨hdst, ha⟩ := hreg
  have fr := hrel.framed
  have l3 := fr.lay3; have l4 := fr.lay4
  have hdst' := hrel.nreg dst hdst
  have ha' := hrel.nreg a ha
  have nd : ∀ k, dst ≠ r + k := fun k => by omega
  have na : ∀ k, a ≠ r + k := fun k => by omega
  have hQ' : CodeAt Q s'.pc ((prims [.nadd (r + 11) a r, .nadd (r + 12) dst r, .op1 o (r + 12) (r + 11)]).compile
      s'.pc) := by
    rw [hrel.pc]; exact hQ
  have hstep : step P w s =
      { s with pc := s.pc + 1, mem := Function.update s.mem (s.nreg dst) (o.eval (s.mem (s.nreg a))) } := by
    unfold step; rw [hP]
  refine sim_rconst_aux _ (by simp only [List.length_cons, List.length_nil]; omega)
    (by simp only [List.length_cons, List.length_nil, blockSteps]; omega) hQ' (by simp [List.foldl, Prim.exec]) ?_
  rw [hstep]
  refine SimRel.of_frame hrel (fun i hi => ?_) (fun i h1 h2 => ?_) (fun c => ?_) (fun c hc => ?_) ?_ ?_
    (fun u hu => ?_) ?_
  · have ni : ∀ k, i ≠ r + k := fun k => by omega
    simp [List.foldl, Prim.exec, atPc, Function.update_apply, ni, hrel.nreg i hi]
  · simp only [List.foldl, Prim.exec, atPc, Function.update_apply]
    split_ifs <;> omega
  · simp [List.foldl, Prim.exec, atPc, Function.update_apply, nd, na, ha', hdst']
    rw [add_comm (s.nreg a), hrel.mem]
    by_cases hc : c = s.nreg dst
    · simp [hc, add_comm]
    · rw [ite_eq_right (by omega), ite_eq_right hc]; exact hrel.mem c
  · simp [List.foldl, Prim.exec, atPc, Function.update_apply, nd, na, ha', hdst']
    intro h; omega
  · exact hrel.draws
  · exact hrel.rounds
  · exact hrel.pts u hu
  · show s'.pc + 3 = τ (s.pc + 1)
    rw [hnext, hrel.pc]; rfl

/-- A jump of the simulation: the states with their counters moved, `p` to `τ p`, stay related. -/
theorem sim_rjlt_aux {r : ℕ} {τ : ℕ → ℕ} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {s s' : State d} (hrel : SimRel r τ a0 Am bv s s') (p : ℕ) :
    SimRel r τ a0 Am bv (atPc s p) (atPc s' (τ p)) :=
  ⟨hrel.nreg, hrel.mem, hrel.draws, hrel.rounds, hrel.pts, rfl,
    ⟨hrel.framed.dd, hrel.framed.mm, hrel.framed.rows, hrel.framed.acc, hrel.framed.tmp, hrel.framed.one,
      hrel.framed.zero, hrel.framed.lay1, hrel.framed.lay2, hrel.framed.lay3, hrel.framed.lay4, hrel.framed.cellA,
      hrel.framed.cellB, hrel.framed.cellA0⟩⟩

theorem sim_rjlt {r : ℕ} {τ : ℕ → ℕ} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {P Q : List Instr} {w w' : World d} {s s' : State d} {a b t : ℕ} (hreg : a < r ∧ b < r)
    (hP : P[s.pc]? = some (.rjlt a b t)) (hQ : CodeAt Q (τ s.pc) (blockCode r (τ s.pc) τ (.rjlt a b t)))
    (hnext : τ (s.pc + 1) = τ s.pc + blockLen (.rjlt a b t)) (hrel : SimRel r τ a0 Am bv s s') :
    BlockOK r τ a0 Am bv P Q w w' s s' := by
  obtain ⟨ha, hb⟩ := hreg
  have fr := hrel.framed
  have l3 := fr.lay3; have l4 := fr.lay4
  have ha' := hrel.nreg a ha
  have hb' := hrel.nreg b hb
  have na : ∀ k, a ≠ r + k := fun k => by omega
  have nb : ∀ k, b ≠ r + k := fun k => by omega
  have hQ2 : CodeAt Q s'.pc ((prims [.nadd (r + 11) a r, .nadd (r + 12) b r]).compile s'.pc) := by
    rw [hrel.pc]; exact CodeAt.append_left (l₂ := [.rjlt (r + 11) (r + 12) (τ t)]) hQ
  have hQ3 : Q[s'.pc + 2]? = some (.rjlt (r + 11) (r + 12) (τ t)) := by
    rw [hrel.pc]; exact hQ 2 (by simp [blockCode])
  set S2 := [Prim.nadd (r + 11) a r, .nadd (r + 12) b r].foldl (fun s p => p.exec w' s) s' with hS2
  have hr2 : run Q w' s' 2 = atPc S2 (s'.pc + 2) := by
    have := exec_sim (exec_prims w' [.nadd (r + 11) a r, .nadd (r + 12) b r] s') s'.pc hQ2
    rw [atPc_self] at this
    exact this
  have h11 : S2.nreg (r + 11) = s.nreg a + s'.nreg r := by simp [hS2, List.foldl, Prim.exec, na, nb, ha']
  have h12 : S2.nreg (r + 12) = s.nreg b + s'.nreg r := by simp [hS2, List.foldl, Prim.exec, na, nb, hb']
  have hm2 : S2.mem = s'.mem := rfl
  have hc : condR (atPc S2 (s'.pc + 2)) (r + 11) (r + 12) ↔ condR s a b := by
    unfold condR
    simp only [atPc_nreg, atPc_mem, h11, h12, hm2]
    rw [add_comm (s.nreg a), add_comm (s.nreg b), hrel.mem, hrel.mem]
  have hfr : ∀ p, SimRel r τ a0 Am bv (atPc s p) (atPc S2 (τ p)) := by
    intro p
    refine SimRel.of_frame hrel (fun i hi => ?_) (fun i h1 h2 => ?_) (fun c => hrel.mem c) (fun c _ => rfl)
      hrel.draws hrel.rounds hrel.pts rfl
    · have ni : ∀ k, i ≠ r + k := fun k => by omega
      simp [hS2, List.foldl, Prim.exec, atPc, Function.update_apply, ni, hrel.nreg i hi]
    · simp only [hS2, List.foldl, Prim.exec, atPc, Function.update_apply]
      split_ifs <;> omega
  refine ⟨3, by omega, by unfold blockSteps; omega, ?_, fun k' hk' => ?_⟩
  · rw [show (3 : ℕ) = 2 + 1 from rfl, run_add, hr2, run_one,
      step_rjlt Q w' _ _ _ _ (by simpa using hQ3), step_rjlt P w s a b _ hP]
    split_ifs with h1 h2 h2
    · simpa using hfr t
    · exact absurd (hc.2 h1) h2
    · exact absurd (hc.1 h2) h1
    · have := hfr (s.pc + 1)
      rwa [hnext, show blockLen (.rjlt a b t) = 3 from rfl, ← hrel.pc] at this
  · refine kept_of_rounds Q w' s' (K := 2) ?_ k' (by omega)
    rw [hr2]; rfl

theorem sim_nconst {r : ℕ} {τ : ℕ → ℕ} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {P Q : List Instr} {w w' : World d} {s s' : State d} {dst c : ℕ} (hreg : dst < r)
    (hP : P[s.pc]? = some (.nconst dst c)) (hQ : CodeAt Q (τ s.pc) (blockCode r (τ s.pc) τ (.nconst dst c)))
    (hnext : τ (s.pc + 1) = τ s.pc + blockLen (.nconst dst c)) (hrel : SimRel r τ a0 Am bv s s') :
    BlockOK r τ a0 Am bv P Q w w' s s' := by
  have hQ' : CodeAt Q s'.pc ((prims [.nconst dst c]).compile s'.pc) := by
    rw [hrel.pc]; exact hQ
  have hstep : step P w s = { s with pc := s.pc + 1, nreg := Function.update s.nreg dst c } := by
    unfold step; rw [hP]
  refine sim_rconst_aux _ (by simp only [List.length_cons, List.length_nil]; omega)
    (by simp only [List.length_cons, List.length_nil, blockSteps]; omega) hQ' (by simp [List.foldl, Prim.exec]) ?_
  rw [hstep]
  refine SimRel.of_frame hrel (fun i hi => ?_) (fun i h1 h2 => ?_) (fun c => ?_) (fun c hc => rfl) ?_ ?_
    (fun u hu => ?_) ?_
  · simp only [List.foldl, Prim.exec, atPc, Function.update_apply]
    split_ifs
    · rfl
    · exact hrel.nreg i hi
  · simp only [List.foldl, Prim.exec, atPc, Function.update_apply]
    rw [ite_eq_right (by omega)]
  · exact hrel.mem c
  · exact hrel.draws
  · exact hrel.rounds
  · exact hrel.pts u hu
  · show s'.pc + 1 = τ (s.pc + 1)
    rw [hnext, hrel.pc]; rfl

theorem sim_nadd {r : ℕ} {τ : ℕ → ℕ} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {P Q : List Instr} {w w' : World d} {s s' : State d} {dst a b : ℕ} (hreg : dst < r ∧ a < r ∧ b < r)
    (hP : P[s.pc]? = some (.nadd dst a b)) (hQ : CodeAt Q (τ s.pc) (blockCode r (τ s.pc) τ (.nadd dst a b)))
    (hnext : τ (s.pc + 1) = τ s.pc + blockLen (.nadd dst a b)) (hrel : SimRel r τ a0 Am bv s s') :
    BlockOK r τ a0 Am bv P Q w w' s s' := by
  obtain ⟨hdst, ha, hb⟩ := hreg
  have hQ' : CodeAt Q s'.pc ((prims [.nadd dst a b]).compile s'.pc) := by
    rw [hrel.pc]; exact hQ
  have hstep : step P w s = { s with pc := s.pc + 1, nreg := Function.update s.nreg dst (s.nreg a + s.nreg b) } := by
    unfold step; rw [hP]
  refine sim_rconst_aux _ (by simp only [List.length_cons, List.length_nil]; omega)
    (by simp only [List.length_cons, List.length_nil, blockSteps]; omega) hQ' (by simp [List.foldl, Prim.exec]) ?_
  rw [hstep]
  refine SimRel.of_frame hrel (fun i hi => ?_) (fun i h1 h2 => ?_) (fun c => ?_) (fun c hc => rfl) ?_ ?_
    (fun u hu => ?_) ?_
  · simp only [List.foldl, Prim.exec, atPc, Function.update_apply]
    split_ifs
    · rw [hrel.nreg a ha, hrel.nreg b hb]
    · exact hrel.nreg i hi
  · simp only [List.foldl, Prim.exec, atPc, Function.update_apply]
    rw [ite_eq_right (by omega)]
  · exact hrel.mem c
  · exact hrel.draws
  · exact hrel.rounds
  · exact hrel.pts u hu
  · show s'.pc + 1 = τ (s.pc + 1)
    rw [hnext, hrel.pc]; rfl

theorem sim_nsub {r : ℕ} {τ : ℕ → ℕ} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {P Q : List Instr} {w w' : World d} {s s' : State d} {dst a b : ℕ} (hreg : dst < r ∧ a < r ∧ b < r)
    (hP : P[s.pc]? = some (.nsub dst a b)) (hQ : CodeAt Q (τ s.pc) (blockCode r (τ s.pc) τ (.nsub dst a b)))
    (hnext : τ (s.pc + 1) = τ s.pc + blockLen (.nsub dst a b)) (hrel : SimRel r τ a0 Am bv s s') :
    BlockOK r τ a0 Am bv P Q w w' s s' := by
  obtain ⟨hdst, ha, hb⟩ := hreg
  have hQ' : CodeAt Q s'.pc ((prims [.nsub dst a b]).compile s'.pc) := by
    rw [hrel.pc]; exact hQ
  have hstep : step P w s = { s with pc := s.pc + 1, nreg := Function.update s.nreg dst (s.nreg a - s.nreg b) } := by
    unfold step; rw [hP]
  refine sim_rconst_aux _ (by simp only [List.length_cons, List.length_nil]; omega)
    (by simp only [List.length_cons, List.length_nil, blockSteps]; omega) hQ' (by simp [List.foldl, Prim.exec]) ?_
  rw [hstep]
  refine SimRel.of_frame hrel (fun i hi => ?_) (fun i h1 h2 => ?_) (fun c => ?_) (fun c hc => rfl) ?_ ?_
    (fun u hu => ?_) ?_
  · simp only [List.foldl, Prim.exec, atPc, Function.update_apply]
    split_ifs
    · rw [hrel.nreg a ha, hrel.nreg b hb]
    · exact hrel.nreg i hi
  · simp only [List.foldl, Prim.exec, atPc, Function.update_apply]
    rw [ite_eq_right (by omega)]
  · exact hrel.mem c
  · exact hrel.draws
  · exact hrel.rounds
  · exact hrel.pts u hu
  · show s'.pc + 1 = τ (s.pc + 1)
    rw [hnext, hrel.pc]; rfl

theorem sim_njlt {r : ℕ} {τ : ℕ → ℕ} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {P Q : List Instr} {w w' : World d} {s s' : State d} {a b t : ℕ} (hreg : a < r ∧ b < r)
    (hP : P[s.pc]? = some (.njlt a b t)) (hQ : CodeAt Q (τ s.pc) (blockCode r (τ s.pc) τ (.njlt a b t)))
    (hnext : τ (s.pc + 1) = τ s.pc + blockLen (.njlt a b t)) (hrel : SimRel r τ a0 Am bv s s') :
    BlockOK r τ a0 Am bv P Q w w' s s' := by
  obtain ⟨ha, hb⟩ := hreg
  have hQ0 : Q[s'.pc]? = some (.njlt a b (τ t)) := by rw [hrel.pc]; exact hQ.cons_head
  have hc : condN s' a b ↔ condN s a b := by
    unfold condN; rw [hrel.nreg a ha, hrel.nreg b hb]
  have hs : s = atPc s s.pc := rfl
  have hs' : s' = atPc s' s'.pc := rfl
  refine ⟨1, le_rfl, by unfold blockSteps; omega, ?_, fun k' hk' => ?_⟩
  · rw [run_one, step_njlt Q w' s' a b _ hQ0, step_njlt P w s a b _ hP]
    split_ifs with h1 h2 h2
    · exact sim_rjlt_aux hrel t
    · exact absurd (hc.2 h1) h2
    · exact absurd (hc.1 h2) h1
    · have := sim_rjlt_aux hrel (s.pc + 1)
      rwa [hnext, show blockLen (.njlt a b t) = 1 from rfl, ← hrel.pc] at this
  · obtain rfl : k' = 0 := by omega
    exact ⟨rfl, rfl⟩

theorem sim_ncast {r : ℕ} {τ : ℕ → ℕ} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {P Q : List Instr} {w w' : World d} {s s' : State d} {dst a : ℕ} (hreg : dst < r ∧ a < r)
    (hP : P[s.pc]? = some (.ncast dst a)) (hQ : CodeAt Q (τ s.pc) (blockCode r (τ s.pc) τ (.ncast dst a)))
    (hnext : τ (s.pc + 1) = τ s.pc + blockLen (.ncast dst a)) (hrel : SimRel r τ a0 Am bv s s') :
    BlockOK r τ a0 Am bv P Q w w' s s' := by
  obtain ⟨hdst, ha⟩ := hreg
  have fr := hrel.framed
  have l3 := fr.lay3; have l4 := fr.lay4
  have hdst' := hrel.nreg dst hdst
  have ha' := hrel.nreg a ha
  have nd : ∀ k, dst ≠ r + k := fun k => by omega
  have na : ∀ k, a ≠ r + k := fun k => by omega
  have hQ' : CodeAt Q s'.pc ((prims [.nadd (r + 11) dst r, .ncast (r + 11) a]).compile s'.pc) := by
    rw [hrel.pc]; exact hQ
  have hstep : step P w s =
      { s with pc := s.pc + 1, mem := Function.update s.mem (s.nreg dst) (s.nreg a : ℝ) } := by
    unfold step; rw [hP]
  refine sim_rconst_aux _ (by simp only [List.length_cons, List.length_nil]; omega)
    (by simp only [List.length_cons, List.length_nil, blockSteps]; omega) hQ' (by simp [List.foldl, Prim.exec]) ?_
  rw [hstep]
  refine SimRel.of_frame hrel (fun i hi => ?_) (fun i h1 h2 => ?_) (fun c => ?_) (fun c hc => ?_) ?_ ?_
    (fun u hu => ?_) ?_
  · have ni : ∀ k, i ≠ r + k := fun k => by omega
    simp [List.foldl, Prim.exec, atPc, Function.update_apply, ni, hrel.nreg i hi]
  · simp only [List.foldl, Prim.exec, atPc, Function.update_apply]
    split_ifs <;> omega
  · simp [List.foldl, Prim.exec, atPc, Function.update_apply, nd, na, ha', hdst']
    by_cases hc : c = s.nreg dst
    · simp [hc, add_comm]
    · rw [ite_eq_right (by omega), ite_eq_right hc]; exact hrel.mem c
  · simp [List.foldl, Prim.exec, atPc, Function.update_apply, nd, na, ha', hdst']
    intro h; omega
  · exact hrel.draws
  · exact hrel.rounds
  · exact hrel.pts u hu
  · show s'.pc + 2 = τ (s.pc + 1)
    rw [hnext, hrel.pc]; rfl

theorem sim_jmp {r : ℕ} {τ : ℕ → ℕ} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {P Q : List Instr} {w w' : World d} {s s' : State d} {t : ℕ}
    (hP : P[s.pc]? = some (.jmp t)) (hQ : CodeAt Q (τ s.pc) (blockCode r (τ s.pc) τ (.jmp t)))
    (hrel : SimRel r τ a0 Am bv s s') :
    BlockOK r τ a0 Am bv P Q w w' s s' := by
  have hQ0 : Q[s'.pc]? = some (.jmp (τ t)) := by rw [hrel.pc]; exact hQ.cons_head
  refine ⟨1, le_rfl, by unfold blockSteps; omega, ?_, fun k' hk' => ?_⟩
  · rw [run_one, step_jmp Q w' s' _ hQ0, step_jmp P w s _ hP]
    exact sim_rjlt_aux hrel t
  · obtain rfl : k' = 0 := by omega
    exact ⟨rfl, rfl⟩

theorem sim_spec {r : ℕ} {τ : ℕ → ℕ} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {P Q : List Instr} {w w' : World d} {s s' : State d} {sp : Spec} {dst src a b : ℕ}
    (hreg : dst < r ∧ src < r ∧ a < r ∧ b < r)
    (hP : P[s.pc]? = some (.spec sp dst src a b))
    (hQ : CodeAt Q (τ s.pc) (blockCode r (τ s.pc) τ (.spec sp dst src a b)))
    (hnext : τ (s.pc + 1) = τ s.pc + blockLen (.spec sp dst src a b)) (hrel : SimRel r τ a0 Am bv s s') :
    BlockOK r τ a0 Am bv P Q w w' s s' := by
  obtain ⟨hdst, hsrc, ha, hb⟩ := hreg
  have fr := hrel.framed
  have l3 := fr.lay3; have l4 := fr.lay4
  have hdst' := hrel.nreg dst hdst
  have hsrc' := hrel.nreg src hsrc
  have ha' := hrel.nreg a ha
  have hb' := hrel.nreg b hb
  have nd : ∀ k, dst ≠ r + k := fun k => by omega
  have ns : ∀ k, src ≠ r + k := fun k => by omega
  have na : ∀ k, a ≠ r + k := fun k => by omega
  have nb : ∀ k, b ≠ r + k := fun k => by omega
  have hQ' : CodeAt Q s'.pc ((prims [.nadd (r + 11) dst r, .nadd (r + 12) src r, .nadd (r + 13) a r,
      .nadd (r + 14) b r, .spec sp (r + 11) (r + 12) (r + 13) (r + 14)]).compile s'.pc) := by
    rw [hrel.pc]; exact hQ
  have hstep : step P w s =
      { s with
        pc := s.pc + 1
        mem := writeMat s.mem (s.nreg dst)
          (cfc (sp.fn (s.mem (s.nreg a)) (s.mem (s.nreg b))) (symPart (matAt d s.mem (s.nreg src)))) } := by
    unfold step; rw [hP]
  have hmat : matAt d s'.mem (s.nreg src + s'.nreg r) = matAt d s.mem (s.nreg src) := by
    funext i j
    unfold matAt
    rw [show s.nreg src + s'.nreg r + d * i + j = s'.nreg r + (s.nreg src + d * i + j) by ring, hrel.mem]
  refine sim_rconst_aux _ (by simp only [List.length_cons, List.length_nil]; omega)
    (by simp only [List.length_cons, List.length_nil, blockSteps]; omega) hQ' (by simp [List.foldl, Prim.exec]) ?_
  rw [hstep]
  refine SimRel.of_frame hrel (fun i hi => ?_) (fun i h1 h2 => ?_) (fun c => ?_) (fun c hc => ?_) ?_ ?_
    (fun u hu => ?_) ?_
  · have ni : ∀ k, i ≠ r + k := fun k => by omega
    simp [List.foldl, Prim.exec, atPc, Function.update_apply, ni, hrel.nreg i hi]
  · simp only [List.foldl, Prim.exec, atPc, Function.update_apply]
    split_ifs <;> omega
  · simp [List.foldl, Prim.exec, atPc, Function.update_apply, nd, ns, na, nb, ha', hb', hdst', hsrc', hmat]
    rw [add_comm (s.nreg a), add_comm (s.nreg b), hrel.mem, hrel.mem]
    unfold writeMat
    generalize d * d = N
    have e : s'.nreg r + c - (s.nreg dst + s'.nreg r) = c - s.nreg dst := by omega
    rw [e]
    by_cases h : s.nreg dst ≤ c ∧ c < s.nreg dst + N
    · rw [ite_eq_left (by omega), ite_eq_left h]
    · rw [ite_eq_right (by omega), ite_eq_right h]; exact hrel.mem c
  · simp [List.foldl, Prim.exec, atPc, Function.update_apply, nd, ns, na, nb, ha', hb', hdst', hsrc', hmat]
    unfold writeMat
    rw [ite_eq_right (by omega)]
  · exact hrel.draws
  · exact hrel.rounds
  · exact hrel.pts u hu
  · show s'.pc + 5 = τ (s.pc + 1)
    rw [hnext, hrel.pc]; rfl

theorem sim_gauss {r : ℕ} {τ : ℕ → ℕ} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {P Q : List Instr} {w w' : World d} {s s' : State d} {dst : ℕ} (hreg : dst < r)
    (hP : P[s.pc]? = some (.gauss dst)) (hQ : CodeAt Q (τ s.pc) (blockCode r (τ s.pc) τ (.gauss dst)))
    (hnext : τ (s.pc + 1) = τ s.pc + blockLen (.gauss dst)) (hrel : SimRel r τ a0 Am bv s s')
    (hg : w.gs s.draws = w'.gs s.draws) :
    BlockOK r τ a0 Am bv P Q w w' s s' := by
  have fr := hrel.framed
  have l3 := fr.lay3; have l4 := fr.lay4
  have hdst' := hrel.nreg dst hreg
  have nd : ∀ k, dst ≠ r + k := fun k => by omega
  have hQ' : CodeAt Q s'.pc ((prims [.nadd (r + 11) dst r, .gauss (r + 11)]).compile s'.pc) := by
    rw [hrel.pc]; exact hQ
  have hstep : step P w s =
      { s with pc := s.pc + 1, mem := Function.update s.mem (s.nreg dst) (w.gs s.draws), draws := s.draws + 1 } := by
    unfold step; rw [hP]
  refine sim_rconst_aux _ (by simp only [List.length_cons, List.length_nil]; omega)
    (by simp only [List.length_cons, List.length_nil, blockSteps]; omega) hQ' (by simp [List.foldl, Prim.exec]) ?_
  rw [hstep]
  refine SimRel.of_frame hrel (fun i hi => ?_) (fun i h1 h2 => ?_) (fun c => ?_) (fun c hc => ?_) ?_ ?_
    (fun u hu => ?_) ?_
  · have ni : ∀ k, i ≠ r + k := fun k => by omega
    simp [List.foldl, Prim.exec, atPc, Function.update_apply, ni, hrel.nreg i hi]
  · simp only [List.foldl, Prim.exec, atPc, Function.update_apply]
    split_ifs <;> omega
  · simp [List.foldl, Prim.exec, atPc, Function.update_apply, nd, hdst']
    by_cases hc : c = s.nreg dst
    · simp [hc, add_comm, hg, hrel.draws]
    · rw [ite_eq_right (by omega), ite_eq_right hc]; exact hrel.mem c
  · simp [List.foldl, Prim.exec, atPc, Function.update_apply, nd, hdst']
    intro h; omega
  · show s'.draws + 1 = s.draws + 1
    rw [hrel.draws]
  · exact hrel.rounds
  · exact hrel.pts u hu
  · show s'.pc + 2 = τ (s.pc + 1)
    rw [hnext, hrel.pc]; rfl

theorem sim_play {r : ℕ} {τ : ℕ → ℕ} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {P Q : List Instr} {w w' : World d} {s s' : State d} {dst src : ℕ} (hreg : dst < r ∧ src < r)
    (hP : P[s.pc]? = some (.play dst src)) (hQ : CodeAt Q (τ s.pc) (blockCode r (τ s.pc) τ (.play dst src)))
    (hnext : τ (s.pc + 1) = τ s.pc + blockLen (.play dst src)) (hrel : SimRel r τ a0 Am bv s s')
    (hf : ∀ y, w.f s.rounds y = w'.f s.rounds (y + a0)) (hn : w.noise s.rounds = w'.noise s.rounds) :
    BlockOK r τ a0 Am bv P Q w w' s s' := by
  classical
  obtain ⟨hdst, hsrc⟩ := hreg
  have fr := hrel.framed
  have l3 := fr.lay3; have l4 := fr.lay4
  have hsrc' := hrel.nreg src hsrc
  have hdst' := hrel.nreg dst hdst
  -- the three primitives
  have e0 := exec_prims w' [.nadd (r + 17) src r, .nadd (r + 11) dst r, .nsub (r + 19) (r + 19) (r + 19)] s'
  obtain ⟨S0, hS0⟩ : ∃ S0, S0 = [Prim.nadd (r + 17) src r, .nadd (r + 11) dst r,
      .nsub (r + 19) (r + 19) (r + 19)].foldl (fun s p => p.exec w' s) s' := ⟨_, rfl⟩
  rw [← hS0] at e0
  have hI0 : PInv r s' S0 (s'.nreg src + s'.nreg r) (s'.nreg dst + s'.nreg r) 0 := by
    subst hS0
    simp only [List.foldl, Prim.exec]
    refine ⟨fun i hi => ?_, ?_, ?_, ?_, by omega, fun c _ => rfl, fun j' hj' => absurd hj' (by omega), rfl, rfl, rfl⟩
    · dsimp only
      rw [Function.update_of_ne (show i ≠ r + 19 by omega), Function.update_of_ne (show i ≠ r + 11 by omega),
        Function.update_of_ne (show i ≠ r + 17 by omega)]
    · simp [Function.update_apply]
    · simp [show dst ≠ r + 17 by omega]
    · simp
  -- the loop
  obtain ⟨k1, S2, j', hk1, e1, hI2, hc2⟩ := exec_whileN_inv (w := w') (a := r + 19) (b := r + 1)
    (c := prims [.nadd (r + 15) (r + 17) (r + 19), .nadd (r + 16) (r + 5) (r + 19),
      .nadd (r + 12) (r + 6) (r + 19), .op2 .add (r + 12) (r + 15) (r + 16), .nadd (r + 19) (r + 19) (r + 9)])
    (fun j S => PInv r s' S (s'.nreg src + s'.nreg r) (s'.nreg dst + s'.nreg r) j) d 5
    (fun j S hI hc => by
      obtain ⟨hn', -, -, h19, -⟩ := hI
      unfold condN at hc
      rwa [h19, hn' (r + 1) (by omega), fr.dd] at hc)
    (fun j S hI hc => by
      have hj : j < d := by
        obtain ⟨hn', -, -, h19, -⟩ := hI
        unfold condN at hc
        rwa [h19, hn' (r + 1) (by omega), fr.dd] at hc
      obtain ⟨S1, he, hI1⟩ := pInv_body fr (by omega) hI hj
      exact ⟨5, S1, le_rfl, he, hI1⟩) 0 S0 hI0
  obtain ⟨hn2, hy2, hD2, h19', hj', hm2, hz2, hdr2, hro2, hpt2⟩ := hI2
  have hjd : j' = d := by
    unfold condN at hc2
    rw [h19', hn2 (r + 1) (by omega), fr.dd] at hc2
    omega
  rw [hjd] at hz2 hm2
  have n6 := hn2 (r + 6) (by omega)
  -- the runs
  have hQc : CodeAt Q (τ s.pc) ((playCmd r dst src).compile (τ s.pc)) := hQ
  have hs' : atPc s' (τ s.pc) = s' := by rw [← hrel.pc]; rfl
  have hr3 : run Q w' s' 3 = atPc S0 (τ s.pc + 3) := by
    have := run_seq_left hQc e0
    rw [hs'] at this
    exact this
  have hQ2 := hQc.seq_right
  have hrk : run Q w' s' (3 + k1) = atPc S2 (τ s.pc + 3 + 8) := by
    rw [run_add, hr3]
    exact run_seq_left hQ2 e1
  have hQ3 := hQ2.seq_right
  have hpl := hQ3.prim_head
  have hrK : run Q w' s' (3 + k1 + 1) =
      atPc (Prim.exec w' S2 (.play (r + 11) (r + 6))) (τ s.pc + 3 + 8 + 1) := by
    rw [run_add, hrk, run_one, step_prim Q w' _ _ hpl, Prim.exec_setPc]
    rfl
  -- the step of `P`
  have hstep : step P w s = (⟨s.pc + 1, s.nreg,
      Function.update s.mem (s.nreg dst) (w.f s.rounds (vecAt s.mem (s.nreg src)) + w.noise s.rounds), s.draws,
      s.rounds + 1, Function.update s.pts s.rounds (vecAt s.mem (s.nreg src))⟩ : State d) := by
    unfold step; rw [hP]
  -- the point played
  have hpt : (vecAt S2.mem (S2.nreg (r + 6)) : E d) = vecAt s.mem (s.nreg src) + a0 := by
    ext j
    simp only [vecAt, n6, PiLp.add_apply]
    rw [hz2 j j.2, fr.cellA0 j, show s'.nreg src + s'.nreg r + j = s'.nreg r + (s.nreg src + j) by
      rw [hsrc']; ring, hrel.mem]
  refine ⟨3 + k1 + 1, by omega, by unfold blockSteps; omega, ?_, fun k' hk' =>
    kept_of_rounds Q w' s' (K := 3 + k1) (by rw [hrk]; exact hro2) k' (by omega)⟩
  rw [hrK, hstep]
  refine SimRel.of_frame hrel (fun i hi => ?_) (fun i _ hi => hn2 i hi) (fun c => ?_) (fun c hc => ?_)
    (by show S2.draws = s.draws; rw [hdr2, hrel.draws])
    (by show S2.rounds + 1 = s.rounds + 1; rw [hro2, hrel.rounds]) (fun u hu => ?_) ?_
  · show S2.nreg i = s.nreg i
    rw [hn2 i (by omega), hrel.nreg i hi]
  · show Function.update S2.mem (S2.nreg (r + 11)) _ (s'.nreg r + c) = Function.update s.mem (s.nreg dst) _ c
    rw [hD2]
    by_cases hc : c = s.nreg dst
    · subst hc
      rw [Function.update_self, show s'.nreg r + s.nreg dst = s'.nreg dst + s'.nreg r by rw [hdst']; ring,
        Function.update_self, hpt, hro2, hrel.rounds, hf, hn]
    · rw [Function.update_of_ne hc, Function.update_of_ne (by omega), hm2 _ (by omega)]
      exact hrel.mem c
  · show Function.update S2.mem (S2.nreg (r + 11)) _ c = s'.mem c
    rw [hD2, Function.update_of_ne (by omega), hm2 _ (by omega)]
  · show Function.update S2.pts S2.rounds (vecAt S2.mem (S2.nreg (r + 6))) u =
      Function.update s.pts s.rounds (vecAt s.mem (s.nreg src)) u + a0
    rw [hro2, hpt2, hrel.rounds, hpt]
    by_cases hu' : u = s.rounds
    · subst hu'; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hu', Function.update_of_ne hu']
      exact hrel.pts u (by have : u < s.rounds + 1 := hu; omega)
  · show τ s.pc + 3 + 8 + 1 = τ (s.pc + 1)
    rw [hnext]; rfl

theorem sim_query {r : ℕ} {τ : ℕ → ℕ} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {P Q : List Instr} {w w' : World d} {s s' : State d} {dst src : ℕ} (hreg : dst < r ∧ src < r)
    (hP : P[s.pc]? = some (.query dst src)) (hQ : CodeAt Q (τ s.pc) (blockCode r (τ s.pc) τ (.query dst src)))
    (hnext : τ (s.pc + 1) = τ s.pc + blockLen (.query dst src)) (hrel : SimRel r τ a0 Am bv s s')
    (hK : ∀ y, y ∈ w.K ↔ y + a0 ∈ polytope Am bv) :
    BlockOK r τ a0 Am bv P Q w w' s s' := by
  classical
  obtain ⟨hdst, hsrc⟩ := hreg
  have fr := hrel.framed
  have l4 := fr.lay4
  obtain ⟨k, S', hk1, hk, he, hn', hm', hans, hdr', hro', hpt'⟩ := query_exec (w := w') (src := src) fr hdst
  have hlen : (queryCmd r dst src).len = blockLen (.query dst src) := rfl
  have hrun : run Q w' s' k = atPc S' (τ s.pc + (queryCmd r dst src).len) := by
    have := exec_sim he (τ s.pc) hQ
    rw [← hrel.pc, atPc_self] at this
    rw [this, hrel.pc]
  have hstep : step P w s = (⟨s.pc + 1, s.nreg,
      Function.update s.mem (s.nreg dst) (if vecAt s.mem (s.nreg src) ∈ w.K then 1 else 0), s.draws, s.rounds,
      s.pts⟩ : State d) := by
    unfold step; rw [hP]
  have hsrc' := hrel.nreg src hsrc
  have hdst' := hrel.nreg dst hdst
  have hrow : ∀ i : Fin m, qRow s' (s'.nreg src + s'.nreg r) i d =
      ∑ j : Fin d, (Am i j : ℝ) * s.mem (s.nreg src + j) := by
    intro i
    unfold qRow
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [fr.cellA i j, show s'.nreg src + s'.nreg r + j = s'.nreg r + (s.nreg src + j) by rw [hsrc']; ring,
      hrel.mem]
  have hiff : (∀ i < m, ¬ QFail r s' (s'.nreg src + s'.nreg r) i) ↔ vecAt s.mem (s.nreg src) ∈ w.K := by
    rw [hK]
    unfold polytope QFail
    simp only [Set.mem_ofPred_eq, vecAt, PiLp.add_apply, mul_add, Finset.sum_add_distrib, not_lt]
    constructor
    · intro h i
      have := h i i.2
      rw [fr.cellB i, hrow i] at this
      linarith
    · intro h i hi
      have := h ⟨i, hi⟩
      have hb := fr.cellB ⟨i, hi⟩
      have hr := hrow ⟨i, hi⟩
      change qRow s' _ ((⟨i, hi⟩ : Fin m) : ℕ) d ≤ s'.mem (s'.nreg (r + 4) + ((⟨i, hi⟩ : Fin m) : ℕ))
      rw [hb, hr]
      linarith
  refine ⟨k, by omega, by unfold blockSteps; omega, ?_, fun k' hk' =>
    kept_of_rounds Q w' s' (K := k) (by rw [hrun]; exact hro') k' hk'.le⟩
  rw [hrun, hstep]
  refine SimRel.of_frame hrel (fun i hi => ?_) (fun i _ hi => hn' i hi) (fun c => ?_)
    (fun c hc => hm' c (by omega) (by omega) (by omega)) (by show S'.draws = s.draws; rw [hdr', hrel.draws])
    (by show S'.rounds = s.rounds; rw [hro', hrel.rounds]) (fun u hu => ?_) ?_
  · show S'.nreg i = s.nreg i
    rw [hn' i (by omega), hrel.nreg i hi]
  · show S'.mem (s'.nreg r + c) = Function.update s.mem (s.nreg dst) _ c
    by_cases hc : c = s.nreg dst
    · subst hc
      rw [Function.update_self, show s'.nreg r + s.nreg dst = s'.nreg dst + s'.nreg r by rw [hdst']; ring, hans]
      simp only [hiff]
    · rw [Function.update_of_ne hc, hm' _ (by omega) (by omega) (by omega)]
      exact hrel.mem c
  · show S'.pts u = s.pts u + a0
    rw [hpt']; exact hrel.pts u hu
  · show τ s.pc + (queryCmd r dst src).len = τ (s.pc + 1)
    rw [hnext, hlen]


/-- Lemma 8.14: every block, from related states, under the hypotheses on the worlds at the current round. -/
theorem sim_step {r : ℕ} {τ : ℕ → ℕ} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {P Q : List Instr} (hregs : ∀ ins ∈ P, ∀ x ∈ Instr.regs ins, x < r)
    (hcode : ∀ p ins, P[p]? = some ins → CodeAt Q (τ p) (blockCode r (τ p) τ ins) ∧ τ (p + 1) = τ p + blockLen ins)
    {w w' : World d} {s s' : State d} (hpc : s.pc < P.length) (hrel : SimRel r τ a0 Am bv s s')
    (hK : ∀ y, y ∈ w.K ↔ y + a0 ∈ polytope Am bv) (hf : ∀ y, w.f s.rounds y = w'.f s.rounds (y + a0))
    (hn : w.noise s.rounds = w'.noise s.rounds) (hg : w.gs s.draws = w'.gs s.draws) :
    BlockOK r τ a0 Am bv P Q w w' s s' := by
  obtain ⟨ins, hins⟩ : ∃ ins, P[s.pc]? = some ins := ⟨P[s.pc], List.getElem?_eq_getElem hpc⟩
  have hr := hregs ins (List.mem_of_getElem? hins)
  obtain ⟨hQ, hnext⟩ := hcode s.pc ins hins
  cases ins with
  | rconst dst q => exact sim_rconst (hr dst (by simp [Instr.regs])) hins hQ hnext hrel
  | op2 o dst a b =>
    exact sim_op2 ⟨hr dst (by simp [Instr.regs]), hr a (by simp [Instr.regs]), hr b (by simp [Instr.regs])⟩
      hins hQ hnext hrel
  | op1 o dst a => exact sim_op1 ⟨hr dst (by simp [Instr.regs]), hr a (by simp [Instr.regs])⟩ hins hQ hnext hrel
  | rjlt a b t => exact sim_rjlt ⟨hr a (by simp [Instr.regs]), hr b (by simp [Instr.regs])⟩ hins hQ hnext hrel
  | nconst dst c => exact sim_nconst (hr dst (by simp [Instr.regs])) hins hQ hnext hrel
  | nadd dst a b =>
    exact sim_nadd ⟨hr dst (by simp [Instr.regs]), hr a (by simp [Instr.regs]), hr b (by simp [Instr.regs])⟩
      hins hQ hnext hrel
  | nsub dst a b =>
    exact sim_nsub ⟨hr dst (by simp [Instr.regs]), hr a (by simp [Instr.regs]), hr b (by simp [Instr.regs])⟩
      hins hQ hnext hrel
  | njlt a b t => exact sim_njlt ⟨hr a (by simp [Instr.regs]), hr b (by simp [Instr.regs])⟩ hins hQ hnext hrel
  | ncast dst a => exact sim_ncast ⟨hr dst (by simp [Instr.regs]), hr a (by simp [Instr.regs])⟩ hins hQ hnext hrel
  | jmp t => exact sim_jmp hins hQ hrel
  | spec sp dst src a b =>
    exact sim_spec ⟨hr dst (by simp [Instr.regs]), hr src (by simp [Instr.regs]), hr a (by simp [Instr.regs]),
      hr b (by simp [Instr.regs])⟩ hins hQ hnext hrel
  | query dst src => exact sim_query ⟨hr dst (by simp [Instr.regs]), hr src (by simp [Instr.regs])⟩ hins hQ hnext hrel hK
  | gauss dst => exact sim_gauss (hr dst (by simp [Instr.regs])) hins hQ hnext hrel hg
  | play dst src =>
    exact sim_play ⟨hr dst (by simp [Instr.regs]), hr src (by simp [Instr.regs])⟩ hins hQ hnext hrel hf hn

/-! ## Corollary SIM-run -/

/-- While the points do not change, the run against a strategy is the run in the world of those points. -/
theorem runAd_eq_run_of_pts {P : List Instr} {g : GameAd d} {s0 : State d} {k : ℕ}
    (h : ∀ k' < k, (run P (g.world s0.pts) s0 k').pts = s0.pts) :
    runAd P g s0 k = run P (g.world s0.pts) s0 k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk : k < k.succ := Nat.lt_succ_self k
    have h_restrict : ∀ k' < k, (run P (g.world s0.pts) s0 k').pts = s0.pts := by
      intro k' hk'
      exact h k' (Nat.lt_of_lt_of_le hk' (Nat.le_succ k))
    have hpts : (run P (g.world s0.pts) s0 k).pts = s0.pts := h k hk
    have h_eq : runAd P g s0 k = run P (g.world s0.pts) s0 k := ih h_restrict
    have h_eq_pts : (runAd P g s0 k).pts = s0.pts := by
      rw [h_eq, hpts]
    calc
      runAd P g s0 (k.succ) = (stepAd P g)^[k.succ] s0 := rfl
      _ = stepAd P g ((stepAd P g)^[k] s0) := by rw [Function.iterate_succ_apply']
      _ = stepAd P g (runAd P g s0 k) := rfl
      _ = step P (g.world (runAd P g s0 k).pts) (runAd P g s0 k) := rfl
      _ = step P (g.world s0.pts) (runAd P g s0 k) := by rw [h_eq_pts]
      _ = step P (g.world s0.pts) (run P (g.world s0.pts) s0 k) := by rw [h_eq]
      _ = run P (g.world s0.pts) s0 (k.succ) := by
        simp [run, Function.iterate_succ_apply']

/-- The observations of the rounds before `t` read the points of those rounds only. -/
theorem lockstep_aux_obs (σ : Strategy d) (ε : ℕ → ℝ) {x y : ℕ → E d} :
    ∀ t, (∀ i < t, x i = y i) → obsAd σ ε x t = obsAd σ ε y t
  | 0, _ => rfl
  | t + 1, h => by
    have ih := lockstep_aux_obs σ ε t fun i hi => h i (by omega)
    have hx : (fun i : Fin t => x i) = fun i : Fin t => y i := funext fun i => h i (by omega)
    simp only [obsAd, ih, hx, h t (by omega)]

/-- The loss of round `t` reads the points of the rounds before `t` only. -/
theorem lockstep_aux_loss (σ : Strategy d) (ε : ℕ → ℝ) {x y : ℕ → E d} (t : ℕ) (h : ∀ i < t, x i = y i) :
    lossAd σ ε x t = lossAd σ ε y t := by
  have hx : (fun i : Fin t => x i) = fun i : Fin t => y i := funext fun i => h i i.2
  simp only [lossAd, lockstep_aux_obs σ ε t h, hx]

/-- One block against the strategies: from related states, `S(P)` against `σ` reaches in at most `blockSteps d m`
steps a state related to the step of `P` against `transStrat σ a₀`, the rounds kept before. -/
theorem lockstep_aux_blk {r : ℕ} {τ : ℕ → ℕ} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {P Q : List Instr} (hregs : ∀ ins ∈ P, ∀ x ∈ Instr.regs ins, x < r)
    (hcode : ∀ p ins, P[p]? = some ins → CodeAt Q (τ p) (blockCode r (τ p) τ ins) ∧ τ (p + 1) = τ p + blockLen ins)
    (hhalt : ∀ p, P.length ≤ p → Q.length ≤ τ p) (σ : Strategy d) (ε gs : ℕ → ℝ) (K' K : Set (E d))
    (hK : ∀ y, y ∈ K' ↔ y + a0 ∈ polytope Am bv) {s s' : State d} (hrel : SimRel r τ a0 Am bv s s') :
    ∃ k, 1 ≤ k ∧ k ≤ blockSteps d m ∧
      SimRel r τ a0 Am bv (stepAd P ⟨K', transStrat σ a0, ε, gs⟩ s) (runAd Q ⟨K, σ, ε, gs⟩ s' k) ∧
      ∀ k' < k, (runAd Q ⟨K, σ, ε, gs⟩ s' k').rounds = s.rounds := by
  by_cases hpc : s.pc < P.length
  · obtain ⟨k, hk1, hk, hr, hkept⟩ := sim_step (w := (⟨K', transStrat σ a0, ε, gs⟩ : GameAd d).world s.pts)
      (w' := (⟨K, σ, ε, gs⟩ : GameAd d).world s'.pts) hregs hcode hpc hrel hK
      (fun y => by
        show lossAd (transStrat σ a0) ε s.pts s.rounds y = lossAd σ ε s'.pts s.rounds (y + a0)
        rw [lossAd_trans]
        exact congrFun (lockstep_aux_loss σ ε s.rounds fun i hi => (hrel.pts i hi).symm) (y + a0))
      rfl rfl
    have hrun : ∀ k'' ≤ k, runAd Q ⟨K, σ, ε, gs⟩ s' k'' = run Q ((⟨K, σ, ε, gs⟩ : GameAd d).world s'.pts) s' k'' :=
      fun k'' hk'' => runAd_eq_run_of_pts fun k' hk' => (hkept k' (by omega)).2
    refine ⟨k, hk1, hk, ?_, fun k' hk' => ?_⟩
    · rw [hrun k le_rfl]; exact hr
    · rw [hrun k' hk'.le, (hkept k' hk').1, hrel.rounds]
  · have hQ : Q.length ≤ s'.pc := by rw [hrel.pc]; exact hhalt _ (by omega)
    refine ⟨1, le_rfl, by unfold blockSteps; omega, ?_, fun k' hk' => ?_⟩
    · show SimRel r τ a0 Am bv (step P _ s) (step Q _ s')
      rw [step_halt P _ s (by omega), step_halt Q _ s' hQ]
      exact hrel
    · obtain rfl : k' = 0 := by omega
      exact hrel.rounds

/-- Corollary SIM-run: the run of `Q` against `σ` from `s₀'` follows, block by block, the run of `P` against
`transStrat σ a₀` on `K'` from `s₀`, with `K' = K - a₀` as far as the queries see it. -/
theorem lockstep {r : ℕ} {τ : ℕ → ℕ} {a0 : E d} {Am : Matrix (Fin m) (Fin d) ℚ} {bv : Fin m → ℚ}
    {P Q : List Instr} (hregs : ∀ ins ∈ P, ∀ x ∈ Instr.regs ins, x < r)
    (hcode : ∀ p ins, P[p]? = some ins → CodeAt Q (τ p) (blockCode r (τ p) τ ins) ∧ τ (p + 1) = τ p + blockLen ins)
    (hhalt : ∀ p, P.length ≤ p → Q.length ≤ τ p) (σ : Strategy d) (ε gs : ℕ → ℝ) (K' K : Set (E d))
    (hK : ∀ y, y ∈ K' ↔ y + a0 ∈ polytope Am bv) {s0 s0' : State d} (h0 : SimRel r τ a0 Am bv s0 s0') :
    ∃ κ : ℕ → ℕ, κ 0 = 0 ∧ (∀ j, κ j < κ (j + 1) ∧ κ (j + 1) ≤ κ j + blockSteps d m) ∧
      (∀ j, SimRel r τ a0 Am bv (runAd P ⟨K', transStrat σ a0, ε, gs⟩ s0 j)
        (runAd Q ⟨K, σ, ε, gs⟩ s0' (κ j))) ∧
      ∀ j k, κ j ≤ k → k < κ (j + 1) →
        (runAd Q ⟨K, σ, ε, gs⟩ s0' k).rounds = (runAd P ⟨K', transStrat σ a0, ε, gs⟩ s0 j).rounds := by
  classical
  set gP : GameAd d := ⟨K', transStrat σ a0, ε, gs⟩ with hgP
  set gQ : GameAd d := ⟨K, σ, ε, gs⟩ with hgQ
  have blk := fun (s s' : State d) (h : SimRel r τ a0 Am bv s s') =>
    lockstep_aux_blk hregs hcode hhalt σ ε gs K' K hK h
  let Kb : State d → State d → ℕ := fun s s' =>
    if h : SimRel r τ a0 Am bv s s' then Classical.choose (blk s s' h) else 1
  let κ : ℕ → ℕ := fun j => Nat.rec 0 (fun j kj => kj + Kb (runAd P gP s0 j) (runAd Q gQ s0' kj)) j
  have hκ : ∀ j, κ (j + 1) = κ j + Kb (runAd P gP s0 j) (runAd Q gQ s0' (κ j)) := fun j => rfl
  have hP1 : ∀ j, runAd P gP s0 (j + 1) = stepAd P gP (runAd P gP s0 j) := fun j => by
    simp only [runAd]; rw [Function.iterate_succ_apply']
  have hQadd : ∀ a b, runAd Q gQ s0' (a + b) = runAd Q gQ (runAd Q gQ s0' a) b := fun a b => by
    simp only [runAd]; rw [add_comm, Function.iterate_add_apply]
  have hspec : ∀ s s', SimRel r τ a0 Am bv s s' →
      1 ≤ Kb s s' ∧ Kb s s' ≤ blockSteps d m ∧ SimRel r τ a0 Am bv (stepAd P gP s) (runAd Q gQ s' (Kb s s')) ∧
        ∀ k' < Kb s s', (runAd Q gQ s' k').rounds = s.rounds := by
    intro s s' h
    have e : Kb s s' = Classical.choose (blk s s' h) := dite_eq_left h
    rw [e]
    exact Classical.choose_spec (blk s s' h)
  have hrel : ∀ j, SimRel r τ a0 Am bv (runAd P gP s0 j) (runAd Q gQ s0' (κ j)) := by
    intro j
    induction j with
    | zero => exact h0
    | succ j ih =>
      rw [hP1, hκ, hQadd]
      exact (hspec _ _ ih).2.2.1
  refine ⟨κ, rfl, fun j => ?_, hrel, fun j k hk1 hk2 => ?_⟩
  · have := hspec _ _ (hrel j)
    rw [hκ]; omega
  · obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hk1
    rw [hκ] at hk2
    rw [hQadd]
    exact (hspec _ _ (hrel j)).2.2.2 k' (by omega)

end AdversarialBco.Conj1Poly
