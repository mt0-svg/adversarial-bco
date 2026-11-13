/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XRuns
public import AdversarialBco.Bit.Transfer.XSpace
public import AdversarialBco.Conj1Bit.Sanity

@[expose] public section

/-!
# The compiler, part 5: the driver, from rounds to the clauses of the frozen statement

* `space_run_le`: along a run, the space grows at most by the cost spent (`space_step_le`).
* `driver`: a run in a fixed world that reaches a checkpoint within cost `Bp`, and from every checkpoint before round
  `n` reaches the next checkpoint within cost `Bc` with one more round played, meets the cost clause with
  `Bp + 2 Bc` and the space clause with `max S0 Sc + Bp + Bc` (`S0` the space of the start, `Sc` that of a checkpoint).
* `driver_bit`: the same for `runBit` against a strategy, as `CostOKBit` and `SpaceOKBit`, through
  `Conj1BitSanity.runBit_eq_run`.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco BitRAM
open Function

variable {d : ℕ}

/-! ## Monotonicity and space along runs -/

theorem step_cost_le (P : List Instr) (w : World d) (s : State d) : s.cost ≤ (step P w s).cost := by
  unfold step
  split
  · exact le_rfl
  · split <;> simp only <;> omega

theorem step_rounds_le (P : List Instr) (w : World d) (s : State d) : s.rounds ≤ (step P w s).rounds :=
  (Conj1BitSanity.step_rounds_pts P w s).1

theorem run_mono (P : List Instr) (w : World d) (s : State d) {i j : ℕ} (h : i ≤ j) :
    (run P w s i).cost ≤ (run P w s j).cost ∧ (run P w s i).rounds ≤ (run P w s j).rounds := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [B.run_add]
  generalize run P w s i = t; clear h
  induction k with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ k ih =>
    rw [B.run_add, B.run_one]
    exact ⟨ih.1.trans (step_cost_le P w _), ih.2.trans (step_rounds_le P w _)⟩

theorem space_run_le {P : List Instr} {w : World d} {s : State d} {S : ℝ} (h : SpaceLE s S) (k : ℕ) :
    SpaceLE (run P w s k) (S + ((run P w s k).cost - s.cost : ℝ)) := by
  induction k with
  | zero => simpa [B.run_zero] using h
  | succ k ih =>
    rw [B.run_add, B.run_one]
    refine spaceLE_mono (space_step_le P w _ _ ih) (le_of_eq ?_)
    ring

/-! ## The driver -/

/-- The driver, in a fixed world. -/
theorem driver {P : List Instr} {w : World d} {a0 : State d} {n Bp Bc : ℕ} {S0 Sc : ℝ}
    (Start : State d → Prop) (hsp0 : SpaceLE a0 S0) (j0 : ℕ) (h0 : Start (run P w a0 j0))
    (hc0 : (run P w a0 j0).cost ≤ a0.cost + Bp) (hS : ∀ a, Start a → SpaceLE a Sc)
    (hseg : ∀ a, Start a → a.rounds < n → ∃ j, Start (run P w a j) ∧ a.rounds < (run P w a j).rounds ∧
      (run P w a j).cost ≤ a.cost + Bc) :
    (∀ k, (run P w a0 k).rounds < n → ∃ j, (run P w a0 k).rounds < (run P w a0 (k + j)).rounds ∧
        ((run P w a0 (k + j)).cost : ℝ) ≤ (run P w a0 k).cost + ((Bp + 2 * Bc : ℕ) : ℝ)) ∧
      ∀ k, (run P w a0 k).rounds < n → SpaceLE (run P w a0 k) (max S0 Sc + ((Bp + Bc : ℕ) : ℝ)) := by
  set Sp : State d → Prop := fun a => SpaceLE a (max S0 Sc + ((Bp + Bc : ℕ) : ℝ))
  have hmono : ∀ a, a.rounds ≤ (step P w a).rounds ∧ a.cost ≤ (step P w a).cost :=
    fun a => ⟨step_rounds_le P w a, step_cost_le P w a⟩
  have hsp0' : ∀ i ≤ j0, Sp ((step P w)^[i] a0) := fun i hi => by
    have h1 := space_run_le (P := P) (w := w) hsp0 i
    have h2 := (run_mono P w a0 hi).1
    refine spaceLE_mono h1 ?_
    have h3 : ((run P w a0 i).cost : ℝ) ≤ a0.cost + Bp := by exact_mod_cast h2.trans hc0
    have h4 : S0 ≤ max S0 Sc := le_max_left _ _
    push_cast
    have : (0 : ℝ) ≤ Bc := Nat.cast_nonneg _
    linarith
  have hseg' : ∀ a, Start a → a.rounds < n → ∃ j, Start ((step P w)^[j] a) ∧ a.rounds < ((step P w)^[j] a).rounds ∧
      ((step P w)^[j] a).cost ≤ a.cost + Bc ∧ ∀ i ≤ j, Sp ((step P w)^[i] a) := fun a ha hn => by
    obtain ⟨j, hj, hr, hc⟩ := hseg a ha hn
    refine ⟨j, hj, hr, hc, fun i hi => ?_⟩
    have h1 := space_run_le (P := P) (w := w) (hS a ha) i
    have h2 := (run_mono P w a hi).1
    refine spaceLE_mono h1 ?_
    have h3 : ((run P w a i).cost : ℝ) ≤ a.cost + Bc := by exact_mod_cast h2.trans hc
    have h4 : Sc ≤ max S0 Sc := le_max_right _ _
    push_cast
    have : (0 : ℝ) ≤ Bp := Nat.cast_nonneg _
    linarith
  obtain ⟨hc, hs⟩ := seg_driver (step P w) State.rounds State.cost Sp Start n Bp Bc hmono a0 j0 h0 hc0 hsp0' hseg'
  refine ⟨fun k hk => ?_, fun k hk => hs k hk⟩
  obtain ⟨j, hj1, hj2⟩ := hc k hk
  exact ⟨j, hj1, by exact_mod_cast hj2⟩

/-- The driver against a strategy: the cost clause and the space clause of the frozen statement. -/
theorem driver_bit {P : List Instr} (g : GameBit d) {s0 : State d} {n Bp Bc : ℕ} {S0 Sc : ℝ} {w : World d}
    (hw : w = ⟨RealRAM.lossAd g.σ 0 (playedBit P g s0), g.cs⟩)
    (Start : State d → Prop) (hsp0 : SpaceLE s0 S0) (j0 : ℕ) (h0 : Start (run P w s0 j0))
    (hc0 : (run P w s0 j0).cost ≤ s0.cost + Bp) (hS : ∀ a, Start a → SpaceLE a Sc)
    (hseg : ∀ a, Start a → a.rounds < n →
      ∃ j, Start (run P w a j) ∧ a.rounds < (run P w a j).rounds ∧ (run P w a j).cost ≤ a.cost + Bc) :
    CostOKBit P g s0 n ((Bp + 2 * Bc : ℕ) : ℝ) ∧ SpaceOKBit P g s0 n (max S0 Sc + ((Bp + Bc : ℕ) : ℝ)) := by
  obtain ⟨hc, hs⟩ := driver Start hsp0 j0 h0 hc0 hS hseg
  have e : ∀ k, runBit P g s0 k = run P w s0 k := fun k => by
    rw [hw]; cases g; exact Conj1BitSanity.runBit_eq_run P _ _ s0 k
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · rw [e] at hk ⊢
    obtain ⟨j, h1, h2⟩ := hc k hk
    exact ⟨j, by rw [e]; exact h1, by rw [e]; exact h2⟩
  · rw [e] at hk ⊢
    exact hs k hk

/-! ## The program: a prologue, a setup, then the rounds -/

/-- The offset of the real cells on the input `d, n, m, A, b`: the input occupies the cells `0, ..., 2 + 2 (d + 1) m`. -/
def offOf (d m : ℕ) : ℕ := 3 + 2 * (d + 1) * m

/-- The prologue: `TO := 3 + 2 (d + 1) m`, from the input cells `0` (`d`) and `2` (`m`). -/
def prologue : List Instr :=
  [.const T1 1, .add T2 0 T1, .mul T2 T2 2, .add T2 T2 T2, .const T1 3, .add TO T2 T1]

/-- The program: the prologue, the code of `setup`, then forever: zero the scratch cells and run `round`. -/
def prog (setup round : XCmd) : List Instr :=
  prologue ++ (xtr setup 6 ++ (Instr.const T1 0 :: Instr.const T2 0 ::
    (xtr round (6 + xtlen setup + 2) ++ [Instr.jmp (6 + xtlen setup)])))

/-- The real state the run starts from: no register, no cell, no draw, no round. -/
def zeroState : RealRAM.State d where
  pc := 0
  nreg := fun _ => 0
  mem := fun _ => 0
  draws := 0
  rounds := 0
  pts := fun _ => 0

/-- The context of the run on the input `d, n, m, A, b` in the world `w`. -/
def ctxOf (w : World d) (n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : XCtx d :=
  ⟨w, fun j => inputMem d n m A b j, offOf d m⟩

theorem toE_zero : toE (fun _ : Fin d => (0 : ℚ)) = 0 := by
  ext i; simp [toE]

section Prog

variable {setup round : XCmd}

theorem prog_code (setup round : XCmd) :
    B.CodeAt (prog setup round) 0 prologue ∧ B.CodeAt (prog setup round) 6 (xtr setup 6) ∧
      (prog setup round)[6 + xtlen setup]? = some (.const T1 0) ∧
      (prog setup round)[6 + xtlen setup + 1]? = some (.const T2 0) ∧
      B.CodeAt (prog setup round) (6 + xtlen setup + 2) (xtr round (6 + xtlen setup + 2)) ∧
      (prog setup round)[6 + xtlen setup + 2 + xtlen round]? = some (.jmp (6 + xtlen setup)) := by
  have hfull : B.CodeAt (prog setup round) 0 (prog setup round) := fun i _ => by rw [Nat.zero_add]
  have r1 : B.CodeAt (prog setup round) 6 _ := hfull.append_right
  have r2 := r1.append_right
  rw [length_xtr] at r2
  have r3 := r2.cons_tail.cons_tail
  have r4 := r3.append_right
  rw [length_xtr] at r4
  exact ⟨hfull.append_left, r1.append_left, r2.cons_head, r2.cons_tail.cons_head, r3.append_left, r4.cons_head⟩

/-- Zeroing the scratch cells keeps the simulation, in two steps of cost `5`. -/
theorem zero_scratch {P : List Instr} {X : XCtx d} {s : RealRAM.State d} {t : State d} {o : ℕ}
    (h1 : P[o]? = some (.const T1 0)) (h2 : P[o + 1]? = some (.const T2 0)) (hpc : t.pc = o) (hs : XSim X s t) :
    ∃ t', run P X.wb t 2 = t' ∧ t'.pc = o + 2 ∧ XSim X s t' ∧ t'.mem T1 = 0 ∧ t'.mem T2 = 0 ∧
      t'.cost = t.cost + 5 := by
  obtain ⟨t1, e1, p1, m1, c1, s1⟩ := B.const_spec (w := X.wb) h1 hpc
  obtain ⟨t2, e2, p2, m2, c2, s2⟩ := B.const_spec (w := X.wb) h2 p1
  refine ⟨t2, by rw [show (2 : ℕ) = 1 + 1 from rfl, B.run_add, B.run_one, B.run_one, e1, e2], p2, ?_, ?_, ?_, ?_⟩
  · refine hs.scratch (fun c hc1 hc2 => ?_) (s1.trans s2).1 (s1.trans s2).2.1 (s1.trans s2).2.2
    rw [m2, update_of_ne hc2, m1, update_of_ne hc1]
  · rw [m2, update_of_ne T1_ne_T2, m1, update_self]
  · rw [m2, update_self]
  · rw [c2, c1, len_T1, len_T2, show len (0 : ℤ) = 0 from rfl]

/-- The prologue: from the initial state, six steps set `TO` to the offset and simulate the zero state, at cost at most
`xstepCost ℓa ℓ`. -/
theorem prologue_run {P : List Instr} {w : World d} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    {ℓa ℓ : ℕ} (hP : B.CodeAt P 0 prologue) (hoff : offOf d m < 2 ^ ℓa) (hd : d + 1 < 2 ^ ℓa) :
    ∃ t, run P w (initBit d n m A b) 6 = t ∧ t.pc = 6 ∧ XSim (ctxOf w n m A b) zeroState t ∧
      t.cost ≤ xstepCost ℓa ℓ := by
  obtain ⟨i0, -, i2⟩ := Conj1BitSanity.inputMem_small (n := n) A b
  simp only [prologue] at hP
  obtain ⟨t1, e1, p1, m1, c1, s1⟩ := B.const_spec (w := w) hP.cons_head (t := initBit d n m A b) rfl
  obtain ⟨t2, e2, p2, m2, c2, s2⟩ := B.add_spec (w := w) hP.cons_tail.cons_head p1
  obtain ⟨t3, e3, p3, m3, c3, s3⟩ := B.opI_spec' (o := .mul) (w := w) hP.cons_tail.cons_tail.cons_head p2
  obtain ⟨t4, e4, p4, m4, c4, s4⟩ := B.add_spec (w := w) hP.cons_tail.cons_tail.cons_tail.cons_head p3
  obtain ⟨t5, e5, p5, m5, c5, s5⟩ := B.const_spec (w := w) hP.cons_tail.cons_tail.cons_tail.cons_tail.cons_head p4
  obtain ⟨t6, e6, p6, m6, c6, s6⟩ :=
    B.add_spec (w := w) hP.cons_tail.cons_tail.cons_tail.cons_tail.cons_tail.cons_head p5
  have q0 : (initBit d n m A b).mem = inputMem d n m A b := rfl
  -- the values of the scratch cells along the prologue
  have v1 : t1.mem T1 = 1 := by rw [m1, update_self]
  have v1' : t1.mem 0 = d := by rw [m1, update_of_ne (by unfold T1; omega), q0, i0]
  have v1'' : t1.mem 2 = m := by rw [m1, update_of_ne (by unfold T1; omega), q0, i2]
  have v2 : t2.mem T2 = d + 1 := by rw [m2, update_self, v1', v1]
  have v2' : t2.mem 2 = m := by rw [m2, update_of_ne (by unfold T2; omega), v1'']
  have v3 : t3.mem T2 = (d + 1) * m := by rw [m3, update_self, v2, v2']; rfl
  have v4 : t4.mem T2 = 2 * ((d + 1) * m) := by rw [m4, update_self, v3]; ring
  have v5 : t5.mem T2 = 2 * ((d + 1) * m) := by rw [m5, update_of_ne T2_ne_T1, v4]
  have v5' : t5.mem T1 = 3 := by rw [m5, update_self]
  have v6 : t6.mem TO = offOf d m := by rw [m6, update_self, v5, v5']; unfold offOf; push_cast; ring
  have hm : ∀ c, c ≠ T1 → c ≠ T2 → c ≠ TO → t6.mem c = inputMem d n m A b c := fun c h1 h2 h3 => by
    rw [m6, update_of_ne h3, m5, update_of_ne h1, m4, update_of_ne h2, m3, update_of_ne h2, m2, update_of_ne h2,
      m1, update_of_ne h1, q0]
  have sS := s1.trans (s2.trans (s3.trans (s4.trans (s5.trans s6))))
  refine ⟨t6, ?_, p6, ?_, ?_⟩
  · simp only [show (6 : ℕ) = 1 + 1 + 1 + 1 + 1 + 1 from rfl, B.run_add, B.run_one, e1, e2, e3, e4, e5, e6]
  · refine ⟨fun i => ?_, fun j => ?_, v6, fun j hj => ?_, ?_, ?_, fun r => ?_⟩
    · rw [hm _ (rg_ne_T1 i) (rg_ne_T2 i) (rg_ne_TO i), Conj1BitSanity.inputMem_neg A b _ (by unfold rg; omega)]; rfl
    · rw [hm _ (cl_ne_T1 _ _) (cl_ne_T2 _ _) (cl_ne_TO _ _),
        Conj1BitSanity.inputMem_high A b _ (by simp only [ctxOf, offOf]; push_cast; omega)]
      simp [zeroState]
    · rw [hm _ (by unfold T1; omega) (by unfold T2; omega) (by unfold TO; omega)]; rfl
    · rw [sS.1]; rfl
    · rw [sS.2.1]; rfl
    · rw [sS.2.2]; exact toE_zero
  · -- the cost of the six instructions
    have hoff' : 3 + 2 * ((d + 1) * m) < 2 ^ ℓa := by
      have := hoff; unfold offOf at this; rw [Nat.mul_assoc] at this; exact this
    have hm1 : m < 2 ^ ℓa := by
      have : m ≤ (d + 1) * m := Nat.le_mul_of_pos_left m (by omega)
      omega
    have hdm : (d + 1) * m < 2 ^ ℓa := by omega
    have h2dm : 2 * ((d + 1) * m) < 2 ^ ℓa := by omega
    have l1 : len ((d : ℤ)) ≤ ℓa := len_nat (by omega)
    have l2 : len ((d : ℤ) + 1) ≤ ℓa := by
      have := len_nat (ℓa := ℓa) (n := d + 1) hd; push_cast at this; exact this
    have l3 : len (m : ℤ) ≤ ℓa := len_nat hm1
    have l4 : len (((d : ℤ) + 1) * m) ≤ ℓa := by
      have := len_nat (ℓa := ℓa) (n := (d + 1) * m) hdm; push_cast at this; exact this
    have l5 : len (2 * (((d : ℤ) + 1) * m)) ≤ ℓa := by
      have := len_nat (ℓa := ℓa) (n := 2 * ((d + 1) * m)) h2dm; push_cast at this; exact this
    have w1 : t1.mem T1 = 1 := v1
    have w3 : t3.mem T2 = ((d : ℤ) + 1) * m := v3
    rw [c6, c5, c4, c3, c2, c1, v5, v5', w3, v2, v2', v1', v1]
    simp only [opC, len_T1, len_T2, len_TO]
    have e0 : len (0 : ℤ) = 0 := rfl
    have e1' : len (1 : ℤ) = 1 := rfl
    have e2' : len (2 : ℤ) = 2 := rfl
    have e3' : len (3 : ℤ) = 2 := rfl
    have e4' : (initBit d n m A b).cost = 0 := rfl
    rw [e0, e1', e2', e3', e4']
    have hsq : (len ((d : ℤ) + 1) + 1) * (len (m : ℤ) + 1) ≤ (ℓa + ℓ + 1) ^ 2 :=
      calc (len ((d : ℤ) + 1) + 1) * (len (m : ℤ) + 1) ≤ (ℓa + ℓ + 1) * (ℓa + ℓ + 1) :=
            Nat.mul_le_mul (by omega) (by omega)
        _ = (ℓa + ℓ + 1) ^ 2 := (sq _).symm
    unfold xstepCost
    omega

/-- The space of the input. -/
def inSpace (d n m M : ℕ) : ℕ := offOf d m * (len (offOf d m : ℤ) + (len d + len n + len m + len M))

/-- The cost of the prologue, of a setup of at most `Ks` units and of the first zeroing. -/
def costP (ℓa ℓ Ks : ℕ) : ℕ := xstepCost ℓa ℓ + Ks * xstepCost ℓa ℓ + 5

/-- The cost of a round of at most `Kr` units, with the jump back and the zeroing. -/
def costR (ℓa ℓ Kr : ℕ) : ℕ := Kr * xstepCost ℓa ℓ + 6

/-- The space of a checkpoint. -/
def ckSpace (d n m M ℓa ℓ : ℕ) : ℕ :=
  (offOf d m + 2 * 2 ^ ℓa) * (2 * ℓa + ℓ + (len d + len n + len m + len M) + 3)

theorem input_spaceLE {n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} (hH : RealRAM.HeightLE A b M) :
    SpaceLE (initBit d n m A b) (inSpace d n m M : ℝ) := fun F hF => by
  have := Conj1BitSanity.input_space_nat hH F hF
  exact_mod_cast this

/-- The world of the game `g` played by the program `P` from `s0`: the losses of `g` on the bits played, the coins of
`g` (the world of `driver_bit`). -/
noncomputable def gameWorld (P : List Instr) (g : GameBit d) (s0 : State d) : World d :=
  ⟨RealRAM.lossAd g.σ 0 (playedBit P g s0), g.cs⟩


theorem costOKBit_mono {P : List Instr} {g : GameBit d} {s0 : State d} {n : ℕ} {B B' : ℝ}
    (h : CostOKBit P g s0 n B) (hB : B ≤ B') : CostOKBit P g s0 n B' := fun k hk => by
  obtain ⟨j, h1, h2⟩ := h k hk
  exact ⟨j, h1, h2.trans (by linarith)⟩

theorem spaceOKBit_mono {P : List Instr} {g : GameBit d} {s0 : State d} {n : ℕ} {B B' : ℝ}
    (h : SpaceOKBit P g s0 n B) (hB : B ≤ B') : SpaceOKBit P g s0 n B' := fun k hk =>
  spaceLE_mono (h k hk) hB

end Prog

end AdversarialBco.Bit.Transfer
