/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.XTransO
public import AdversarialBco.Unified.RunFacts
public import AdversarialBco.Bit.Transfer.XDriver

@[expose] public section

/-!
# The driver of a program on the oracle machine (UNI-PROG, UNI-MACH)

The machine layer of Bit/Transfer/XDriver.lean on the oracle machine of StatementBitRAMO.lean, with
the input `initU` of StatementUnified.lean and the coin clause `CoinWindowsOK`.

* The input: `inputU` occupies the cells `0, ..., 7 + 2 d` (`offU d = 8 + 2 d`), every cell has length at most
  `len d + len n + S` (`S = sizeN`, the input size whose cast is `sizeU`), and the input state has space at most
  `inSpaceU`.
* `progO setup rA rM rB`: the prologue (`TO := 8 + 2 d`, three instructions), the code of `setup`, then forever: zero
  the scratch cells, run the round in three segments `rA`, `rM`, `rB`, jump back.
* `progO_ok`: from a bounded run of `setup` from the zero state to an environment with `Inv 0`, and the three segment
  contracts of every round `t < n` (`Inv t` to `IA t` to `IM t` to `Inv (t + 1)`; `IA t` at `t` rounds and `D' t`
  coins, `IM t` at `t + 1` rounds and `D' t` coins; `D' t ≤ D (t + 1)`), the program meets the cost clause, the
  space clause and the coin clause with the windows `D`, `D'`, and the point of every round `t < n` is that of an
  environment with `IM t`. The coin clause needs only the two inner checkpoints of each round and the monotonicity
  of the rounds and the coins along `runO` (`runO_mono`).
-/

namespace AdversarialBco.Unified.ProgO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer
open AdversarialBco.Uni
open BitRAM BitRAMO
open Function

variable {d : ℕ}

/-! ## The input -/

/-- The offset of the real cells: the input occupies the cells `0, ..., 7 + 2 d`. -/
def offU (d : ℕ) : ℕ := 8 + 2 * d

/-- The input size in `ℕ`; `sizeU` is its cast. -/
def sizeN (δ r0 R0 : ℚ) (a : Fin d → ℚ) : ℕ :=
  len δ.num + len δ.den + len r0.num + len r0.den + len R0.num + len R0.den + ∑ i, (len (a i).num + len (a i).den)

theorem sizeU_eq (δ r0 R0 : ℚ) (a : Fin d → ℚ) : sizeU δ r0 R0 a = (sizeN δ r0 R0 a : ℝ) := rfl

/-- The bit length bound of an input cell. -/
def lenIn (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) : ℕ := len d + len n + sizeN δ r0 R0 a

section Input

variable {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ}

theorem inputU_zero : inputU d n δ r0 R0 a 0 = d := by simp [inputU]

theorem inputU_neg {c : ℤ} (hc : c < 0) : inputU d n δ r0 R0 a c = 0 := by
  unfold inputU
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), dite_eq_right (by omega)]

theorem inputU_high {c : ℤ} (hc : (offU d : ℤ) ≤ c) : inputU d n δ r0 R0 a c = 0 := by
  unfold inputU offU at *
  push_cast at hc
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), dite_eq_right]
  rintro ⟨-, h⟩
  omega

theorem len_inputU_le (c : ℤ) : len (inputU d n δ r0 R0 a c) ≤ lenIn d n δ r0 R0 a := by
  unfold inputU lenIn sizeN
  split_ifs with h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · have := Finset.single_le_sum (f := fun i : Fin d => len (a i).num + len (a i).den)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨(c - 8).toNat / 2, h8.2⟩)
    omega
  · have := Finset.single_le_sum (f := fun i : Fin d => len (a i).num + len (a i).den)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨(c - 8).toNat / 2, h8.2⟩)
    omega
  · simp [len]

theorem inputU_support (c : ℤ) (hc : inputU d n δ r0 R0 a c ≠ 0) : c ∈ Finset.Ico (0 : ℤ) (offU d) := by
  rw [Finset.mem_Ico]
  constructor
  · by_contra h; exact hc (inputU_neg (by omega))
  · by_contra h; exact hc (inputU_high (by omega))

/-- The space of the input. -/
def inSpaceU (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) : ℕ := offU d * (len (offU d : ℤ) + lenIn d n δ r0 R0 a)

theorem input_spaceU : SpaceLE (initU d n δ r0 R0 a) (inSpaceU d n δ r0 R0 a : ℝ) := fun F hF => by
  have hsub : F ⊆ Finset.Ico (0 : ℤ) (offU d) := fun c hc => inputU_support c (hF c hc)
  have h : ∑ c ∈ F, (len c + len (inputU d n δ r0 R0 a c)) ≤ inSpaceU d n δ r0 R0 a :=
    calc ∑ c ∈ F, (len c + len (inputU d n δ r0 R0 a c))
        ≤ ∑ c ∈ Finset.Ico (0 : ℤ) (offU d), (len c + len (inputU d n δ r0 R0 a c)) :=
          Finset.sum_le_sum_of_subset hsub
      _ ≤ (Finset.Ico (0 : ℤ) (offU d)).card * (len (offU d : ℤ) + lenIn d n δ r0 R0 a) := by
          refine Finset.sum_le_card_nsmul _ _ _ fun c hc => ?_
          rw [Finset.mem_Ico] at hc
          have h1 : len c ≤ len (offU d : ℤ) := Conj1BitSanity.len_mono (by omega)
          have h2 := len_inputU_le (n := n) (δ := δ) (r0 := r0) (R0 := R0) (a := a) c
          omega
      _ = inSpaceU d n δ r0 R0 a := by rw [Int.card_Ico]; rfl
  exact_mod_cast h

end Input

/-! ## The program -/

/-- The prologue: `TO := 8 + 2 d` from the input cell `0`. -/
def prologueU : List Instr := [.const T1 8, .add T2 0 0, .add TO T2 T1]

/-- The address of the zeroing that starts every round. -/
def oZ (setup : XCmdO) : ℕ := 3 + xtlenO setup

/-- The address of the first segment. -/
def oA (setup : XCmdO) : ℕ := oZ setup + 2

/-- The address of the second segment. -/
def oM (setup rA : XCmdO) : ℕ := oA setup + xtlenO rA

/-- The address of the third segment. -/
def oB (setup rA rM : XCmdO) : ℕ := oM setup rA + xtlenO rM

/-- The address of the jump back. -/
def oJ (setup rA rM rB : XCmdO) : ℕ := oB setup rA rM + xtlenO rB

/-- The program: the prologue, the code of `setup`, then forever: zero the scratch cells, run the round's segments
`rA`, `rM`, `rB`, jump back. -/
def progO (setup rA rM rB : XCmdO) : List InstrO :=
  bL prologueU ++ (xtrO setup 3 ++ (.base (.const T1 0) :: .base (.const T2 0) ::
    (xtrO rA (oA setup) ++ (xtrO rM (oM setup rA) ++ (xtrO rB (oB setup rA rM) ++ [.base (.jmp (oZ setup))])))))

/-- The real state the run starts from: no register, no cell, no draw, no round. -/
def zeroState : RealRAM.State d where
  pc := 0
  nreg := fun _ => 0
  mem := fun _ => 0
  draws := 0
  rounds := 0
  pts := fun _ => 0

/-- The context of the run on the input `d, n, δ, r0, R0, a` in the world `w`. -/
def ctxU (w : WorldO d) (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) : XCtxO d :=
  ⟨w, fun j => inputU d n δ r0 R0 a j, offU d⟩

theorem progO_length (setup rA rM rB : XCmdO) : (progO setup rA rM rB).length = oJ setup rA rM rB + 1 := by
  simp [progO, prologueU, oJ, oB, oM, oA, oZ]
  omega

theorem progO_code (setup rA rM rB : XCmdO) :
    CodeAtO (progO setup rA rM rB) 0 (bL prologueU) ∧ CodeAtO (progO setup rA rM rB) 3 (xtrO setup 3) ∧
      (progO setup rA rM rB)[oZ setup]? = some (.base (.const T1 0)) ∧
      (progO setup rA rM rB)[oZ setup + 1]? = some (.base (.const T2 0)) ∧
      CodeAtO (progO setup rA rM rB) (oA setup) (xtrO rA (oA setup)) ∧
      CodeAtO (progO setup rA rM rB) (oM setup rA) (xtrO rM (oM setup rA)) ∧
      CodeAtO (progO setup rA rM rB) (oB setup rA rM) (xtrO rB (oB setup rA rM)) ∧
      (progO setup rA rM rB)[oJ setup rA rM rB]? = some (.base (.jmp (oZ setup))) := by
  have hfull : CodeAtO (progO setup rA rM rB) 0 (progO setup rA rM rB) := fun i _ => by rw [Nat.zero_add]
  have r1 := hfull.append_right
  simp only [length_bL, prologueU, List.length_cons, List.length_nil] at r1
  have r2 := r1.append_right
  rw [length_xtrO] at r2
  have r3 := r2.cons_tail.cons_tail
  have r4 := r3.append_right
  rw [length_xtrO] at r4
  have r5 := r4.append_right
  rw [length_xtrO] at r5
  have r6 := r5.append_right
  rw [length_xtrO] at r6
  refine ⟨hfull.append_left, r1.append_left, r2.cons_head, r2.cons_tail.cons_head, r3.append_left, ?_, ?_, ?_⟩
  · exact r4.append_left
  · exact r5.append_left
  · exact r6.cons_head

/-! ## Base steps on the oracle machine -/

section Steps

variable {P : List InstrO} {w : WorldO d}

/-- A run of base instructions of the lowered program that stays inside the program is a run of `P`. -/
theorem runO_of_run {t : State d} {k : ℕ} (h : (run (lowerP P) w.toW t k).pc < P.length) :
    runO P w t k = run (lowerP P) w.toW t k := uni_liftO P w t k h

/-- Zeroing the scratch cells keeps the simulation, in two steps of cost `5`. -/
theorem zero_scratchO {XO : XCtxO d} (_hw : XO.w = w) {s : RealRAM.State d} {t : State d} {o : ℕ}
    (h1 : P[o]? = some (.base (.const T1 0))) (h2 : P[o + 1]? = some (.base (.const T2 0)))
    (hlen : o + 2 < P.length) (hpc : t.pc = o) (hs : XSim XO.X s t) :
    ∃ t', runO P w t 2 = t' ∧ t'.pc = o + 2 ∧ XSim XO.X s t' ∧ t'.mem T1 = 0 ∧ t'.mem T2 = 0 ∧
      t'.cost = t.cost + 5 := by
  obtain ⟨t1, e1, p1, m1, c1, s1⟩ := B.const_spec (w := w.toW) (lowerP_get h1) hpc
  obtain ⟨t2, e2, p2, m2, c2, s2⟩ := B.const_spec (w := w.toW) (lowerP_get h2) p1
  have er : run (lowerP P) w.toW t 2 = t2 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, B.run_add, B.run_one, B.run_one, e1, e2]
  refine ⟨t2, by rw [runO_of_run (by rw [er, p2]; exact hlen), er], p2, ?_, ?_, ?_, ?_⟩
  · refine hs.scratch (fun c hc1 hc2 => ?_) (s1.trans s2).1 (s1.trans s2).2.1 (s1.trans s2).2.2
    rw [m2, update_of_ne hc2, m1, update_of_ne hc1]
  · rw [m2, update_of_ne T1_ne_T2, m1, update_self]
  · rw [m2, update_self]
  · rw [c2, c1, len_T1, len_T2, show len (0 : ℤ) = 0 from rfl]

/-- A jump on the oracle machine keeps the simulation, in one step of cost `1`. -/
theorem xsimO_jmp {XO : XCtxO d} (_hw : XO.w = w) {s : RealRAM.State d} {t : State d} {o tg : ℕ}
    (h0 : P[o]? = some (.base (.jmp tg))) (htg : tg < P.length) (hpc : t.pc = o) (hs : XSim XO.X s t) :
    ∃ t', runO P w t 1 = t' ∧ t'.pc = tg ∧ XSim XO.X s t' ∧ t'.cost = t.cost + 1 := by
  obtain ⟨t1, e1, p1, m1, c1, s1⟩ := B.jmp_spec (w := w.toW) (lowerP_get h0) hpc
  have er : run (lowerP P) w.toW t 1 = t1 := by rw [B.run_one, e1]
  exact ⟨t1, by rw [runO_of_run (by rw [er, p1]; exact htg), er], p1,
    hs.scratch (fun c _ _ => by rw [m1]) s1.1 s1.2.1 s1.2.2, c1⟩

/-- The prologue: from the initial state, three steps set `TO` to the offset and simulate the zero state, at cost at
most `xstepCost ℓa ℓ`. -/
theorem prologueU_run {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ} {ℓa ℓ : ℕ} (hP : CodeAtO P 0 (bL prologueU))
    (hlen : 3 < P.length) (hoff : offU d < 2 ^ ℓa) :
    ∃ t, runO P w (initU d n δ r0 R0 a) 3 = t ∧ t.pc = 3 ∧ XSim (ctxU w n δ r0 R0 a).X zeroState t ∧
      t.cost ≤ xstepCost ℓa ℓ := by
  have hL := hP.lower
  simp only [prologueU] at hL
  obtain ⟨t1, e1, p1, m1, c1, s1⟩ := B.const_spec (w := w.toW) hL.cons_head (t := initU d n δ r0 R0 a) rfl
  obtain ⟨t2, e2, p2, m2, c2, s2⟩ := B.add_spec (w := w.toW) hL.cons_tail.cons_head p1
  obtain ⟨t3, e3, p3, m3, c3, s3⟩ := B.add_spec (w := w.toW) hL.cons_tail.cons_tail.cons_head p2
  have q0 : (initU d n δ r0 R0 a).mem = inputU d n δ r0 R0 a := rfl
  have er : run (lowerP P) w.toW (initU d n δ r0 R0 a) 3 = t3 := by
    simp only [show (3 : ℕ) = 1 + 1 + 1 from rfl, B.run_add, B.run_one, e1, e2, e3]
  have v1 : t1.mem T1 = 8 := by rw [m1, update_self]
  have v1' : t1.mem 0 = d := by rw [m1, update_of_ne (by unfold T1; omega), q0, inputU_zero]
  have v2 : t2.mem T2 = 2 * d := by rw [m2, update_self, v1']; ring
  have v2' : t2.mem T1 = 8 := by rw [m2, update_of_ne T1_ne_T2, v1]
  have v3 : t3.mem TO = offU d := by rw [m3, update_self, v2, v2']; unfold offU; push_cast; ring
  have hm : ∀ c, c ≠ T1 → c ≠ T2 → c ≠ TO → t3.mem c = inputU d n δ r0 R0 a c := fun c h1 h2 h3 => by
    rw [m3, update_of_ne h3, m2, update_of_ne h2, m1, update_of_ne h1, q0]
  have sS := s1.trans (s2.trans s3)
  refine ⟨t3, by rw [runO_of_run (by rw [er, p3]; exact hlen), er], p3, ?_, ?_⟩
  · refine ⟨fun i => ?_, fun j => ?_, v3, fun j hj => ?_, ?_, ?_, fun r => ?_⟩
    · rw [hm _ (rg_ne_T1 i) (rg_ne_T2 i) (rg_ne_TO i), inputU_neg (by unfold rg; omega)]; rfl
    · rw [hm _ (cl_ne_T1 _ _) (cl_ne_T2 _ _) (cl_ne_TO _ _), inputU_high (by simp [ctxU, XCtxO.X])]; simp [zeroState]
    · rw [hm _ (by unfold T1; omega) (by unfold T2; omega) (by unfold TO; omega)]; rfl
    · rw [sS.1]; rfl
    · rw [sS.2.1]; rfl
    · rw [sS.2.2]; exact toE_zero
  · have hd2 : 2 * d < 2 ^ ℓa := by unfold offU at hoff; omega
    have hd1 : d < 2 ^ ℓa := by omega
    have l1 : len ((d : ℤ)) ≤ ℓa := len_nat hd1
    have l2 : len (2 * (d : ℤ)) ≤ ℓa := by
      have := len_nat (ℓa := ℓa) (n := 2 * d) hd2; push_cast at this; exact this
    rw [c3, c2, c1, v2, v2', v1']
    simp only [len_T1, len_T2, len_TO]
    have e0 : len (0 : ℤ) = 0 := rfl
    have e8 : len (8 : ℤ) = 4 := rfl
    have e4' : (initU d n δ r0 R0 a).cost = 0 := rfl
    rw [e0, e8, e4']
    unfold xstepCost
    nlinarith

end Steps

/-! ## Space along runs of the oracle machine -/

theorem spaceO_step_le (P : List InstrO) (w : WorldO d) (s : State d) (B : ℝ) (h : SpaceLE s B) :
    SpaceLE (stepO P w s) (B + ((stepO P w s).cost - s.cost : ℝ)) := by
  have hup : ∀ (s' : State d) (c v : ℤ) (k : ℕ), s'.mem = Function.update s.mem c v → s'.cost = s.cost + k →
      len c + len v ≤ k → SpaceLE s' (B + ((s'.cost : ℝ) - s.cost)) := fun s' c v k hm hc hk => by
    have h1 := spaceLE_update s s' c v B hm h
    have h2 : ((len c + len v : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    intro F hF
    refine (h1 F hF).trans ?_
    rw [hc]; push_cast at h1 h2 ⊢; linarith
  unfold stepO
  rcases hP : P[s.pc]? with _ | ins
  · simp only
    intro F hF
    have := h F hF
    simp only [sub_self, add_zero]
    exact this
  · rcases ins with i | ⟨dst, src, prec⟩ | ⟨dst, prec, rng⟩
    · exact space_step_le (lowerP P) w.toW s B h
    · refine hup _ _ _ _ rfl rfl ?_
      have : len (if w.orc (ptAt d s.mem (s.mem src)) (s.mem prec).toNat then (1 : ℤ) else 0) ≤ 1 := by
        split_ifs <;> decide
      omega
    · refine hup _ _ _ _ rfl rfl ?_
      have := uni_clip_lenO (reading w.toW s (s.mem prec).toNat) (s.mem rng).toNat
      omega

theorem space_runO_le {P : List InstrO} {w : WorldO d} {s : State d} {S : ℝ} (h : SpaceLE s S) (k : ℕ) :
    SpaceLE (runO P w s k) (S + ((runO P w s k).cost - s.cost : ℝ)) := by
  induction k with
  | zero => simpa [RunFacts.runO_zero] using h
  | succ k ih =>
    rw [RunFacts.runO_succ]
    refine spaceLE_mono (spaceO_step_le P w _ _ ih) (le_of_eq ?_)
    ring

theorem stepO_cost_le (P : List InstrO) (w : WorldO d) (s : State d) : s.cost ≤ (stepO P w s).cost := by
  unfold stepO
  rcases hP : P[s.pc]? with _ | ins
  · exact le_rfl
  · rcases ins with i | ⟨dst, src, prec⟩ | ⟨dst, prec, rng⟩
    · exact step_cost_le (lowerP P) w.toW s
    · simp only; omega
    · simp only; omega

theorem runO_cost_mono (P : List InstrO) (w : WorldO d) (s : State d) {i j : ℕ} (h : i ≤ j) :
    (runO P w s i).cost ≤ (runO P w s j).cost := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [runO_add]
  generalize runO P w s i = t; clear h
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [runO_add, runO_one]
    exact ih.trans (stepO_cost_le P w _)

/-! ## The oracle language keeps the real state clean -/

theorem clean_leafO {XO : XCtxO d} {ℓa ℓ : ℕ} {s : RealRAM.State d} {l : LeafO} (h : Clean ℓa ℓ s)
    (hl : l.OK ℓa ℓ s) : Clean ℓa ℓ (l.exec XO s) := by
  cases l with
  | orc dst src prec =>
    obtain ⟨hd, -⟩ := hl
    refine h.setReg hd ?_
    have : (2 : ℕ) ≤ 2 ^ (ℓa + 1) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (ℓa + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    split_ifs <;> omega
  | obsR dst prec rng =>
    obtain ⟨⟨-, hd⟩, -, -, -, hq⟩ := hl
    refine h.setMem hd ?_
    have e : ∀ (q : ℕ) (z : ℤ), |BitRAMO.clip q z| ≤ (2 : ℤ) ^ q := fun q z => by
      unfold BitRAMO.clip
      have h0 : (0 : ℤ) ≤ 2 ^ q := by positivity
      rw [abs_le]
      exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
    have hc : |((BitRAMO.clip (s.nreg rng) ⌊(2 : ℝ) ^ (s.nreg prec) * fbR XO.X s⌋ : ℤ) : ℝ)| ≤
        2 ^ (s.nreg rng) := by
      rw [← Int.cast_abs]
      exact_mod_cast e _ _
    exact hc.trans ((pow_le_pow_right₀ (by norm_num) hq.le).trans (pow_le_pow_add ℓa ℓ))

/-- A bounded run of the oracle language keeps the real state clean. -/
theorem execBO_clean {XO : XCtxO d} {ℓa ℓ : ℕ} {c : XCmdO} {s s' : RealRAM.State d} {k : ℕ}
    (he : XExecBO XO ℓa ℓ c s k s') (h : Clean ℓa ℓ s) : Clean ℓa ℓ s' := by
  induction he with
  | base hex => exact hex.clean h
  | leaf l s hl => exact clean_leafO h hl
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ h)
  | ifR_t _ _ _ ih => exact ih h
  | ifR_f _ _ _ ih => exact ih h
  | ifN_t _ _ _ ih => exact ih h
  | ifN_f _ _ _ ih => exact ih h
  | whileR_t _ _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ h)
  | whileR_f => exact h
  | whileN_t _ _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ h)
  | whileN_f => exact h

/-! ## The driver on the oracle machine -/

/-- The driver of Bit/Transfer/XDriver.lean on `runO`, in a fixed world: a run that reaches a checkpoint within cost
`Bp`, and from every checkpoint before round `n` reaches the next checkpoint within cost `Bc` with one more round
played, meets the cost clause with `Bp + 2 Bc` and the space clause with `max S0 Sc + Bp + Bc`. -/
theorem driverO {P : List InstrO} {w : WorldO d} {a0 : State d} {n Bp Bc : ℕ} {S0 Sc : ℝ}
    (Start : State d → Prop) (hsp0 : SpaceLE a0 S0) (j0 : ℕ) (h0 : Start (runO P w a0 j0))
    (hc0 : (runO P w a0 j0).cost ≤ a0.cost + Bp) (hS : ∀ a, Start a → SpaceLE a Sc)
    (hseg : ∀ a, Start a → a.rounds < n → ∃ j, Start (runO P w a j) ∧ a.rounds < (runO P w a j).rounds ∧
      (runO P w a j).cost ≤ a.cost + Bc) :
    CostOKO P w a0 n ((Bp + 2 * Bc : ℕ) : ℝ) ∧ SpaceOKO P w a0 n (max S0 Sc + ((Bp + Bc : ℕ) : ℝ)) := by
  set Sp : State d → Prop := fun a => SpaceLE a (max S0 Sc + ((Bp + Bc : ℕ) : ℝ))
  have hmono : ∀ a, a.rounds ≤ (stepO P w a).rounds ∧ a.cost ≤ (stepO P w a).cost :=
    fun a => ⟨(RunFacts.stepO_facts P w a).1, stepO_cost_le P w a⟩
  have hsp0' : ∀ i ≤ j0, Sp ((stepO P w)^[i] a0) := fun i hi => by
    have h1 := space_runO_le (P := P) (w := w) hsp0 i
    have h2 := runO_cost_mono P w a0 hi
    refine spaceLE_mono h1 ?_
    have h3 : ((runO P w a0 i).cost : ℝ) ≤ a0.cost + Bp := by exact_mod_cast h2.trans hc0
    have h4 : S0 ≤ max S0 Sc := le_max_left _ _
    push_cast
    have : (0 : ℝ) ≤ Bc := Nat.cast_nonneg _
    linarith
  have hseg' : ∀ a, Start a → a.rounds < n → ∃ j, Start ((stepO P w)^[j] a) ∧
      a.rounds < ((stepO P w)^[j] a).rounds ∧ ((stepO P w)^[j] a).cost ≤ a.cost + Bc ∧
      ∀ i ≤ j, Sp ((stepO P w)^[i] a) := fun a ha hn => by
    obtain ⟨j, hj, hr, hc⟩ := hseg a ha hn
    refine ⟨j, hj, hr, hc, fun i hi => ?_⟩
    have h1 := space_runO_le (P := P) (w := w) (hS a ha) i
    have h2 := runO_cost_mono P w a hi
    refine spaceLE_mono h1 ?_
    have h3 : ((runO P w a i).cost : ℝ) ≤ a.cost + Bc := by exact_mod_cast h2.trans hc
    have h4 : Sc ≤ max S0 Sc := le_max_right _ _
    push_cast
    have : (0 : ℝ) ≤ Bp := Nat.cast_nonneg _
    linarith
  obtain ⟨hc, hs⟩ := seg_driver (stepO P w) State.rounds State.cost Sp Start n Bp Bc hmono a0 j0 h0 hc0 hsp0'
    hseg'
  refine ⟨fun k hk => ?_, fun k hk => hs k hk⟩
  obtain ⟨j, hj1, hj2⟩ := hc k hk
  exact ⟨j, hj1, by exact_mod_cast hj2⟩

/-- The space of a checkpoint on the input `d, n, δ, r0, R0, a`. -/
def ckSpaceU (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (ℓa ℓ : ℕ) : ℕ :=
  (offU d + 2 * 2 ^ ℓa) * (2 * ℓa + ℓ + lenIn d n δ r0 R0 a + 3)

section Prog

variable {L : Layout} {ℓa ℓ : ℕ} {setup rA rM rB : XCmdO} {Inv IA IM : ℕ → Env d → Prop}
  {n : ℕ} {δ r0 R0 : ℚ} {a : Fin d → ℚ}

/-- **The driver of `progO`.** From a bounded run of `setup` from the zero state to an environment with `Inv 0`
within `Ks` units, and in every round `t < n` the three segments `rA` (from `Inv t` to `IA t`, within `KA` units),
`rM` (from `IA t` to `IM t`, within `KM`) and `rB` (from `IM t` to `Inv (t + 1)`, within `KB`), where `Inv t` is at
`t` rounds, `IA t` at `t` rounds and `D' t` draws, `IM t` at `t + 1` rounds and `D' t` draws, and `D' t ≤ D (t + 1)`:
the cost clause, the space clause, the coin clause with the windows `D`, `D'`, and the point of every round `t < n`
is the point of round `t` of an environment with `IM t`. -/
theorem progO_ok (w : WorldO d) (Ks KA KM KB : ℕ) (D D' : ℕ → ℕ) (hoff : offU d < 2 ^ ℓa) (h4 : 4 ≤ 2 ^ ℓa)
    (hsetup : ∃ k s1 σ1, k ≤ Ks ∧ XExecBO (ctxU w n δ r0 R0 a) ℓa ℓ setup zeroState k s1 ∧ Rep L σ1 s1 ∧
      Inv 0 σ1)
    (hA : ∀ t < n, ∀ σ, Inv t σ → XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ rA σ KA (IA t))
    (hM : ∀ t < n, ∀ σ, IA t σ → XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ rM σ KM (IM t))
    (hB : ∀ t < n, ∀ σ, IM t σ → XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ rB σ KB (Inv (t + 1)))
    (hIr : ∀ t σ, Inv t σ → σ.rounds = t)
    (hIA : ∀ t σ, IA t σ → σ.rounds = t ∧ σ.draws = D' t)
    (hIM : ∀ t σ, IM t σ → σ.rounds = t + 1 ∧ σ.draws = D' t)
    (hDD : ∀ t, D' t ≤ D (t + 1)) :
    CostOKO (progO setup rA rM rB) w (initU d n δ r0 R0 a) n
        ((costP ℓa ℓ Ks + 2 * costR ℓa ℓ (KA + KM + KB) : ℕ) : ℝ) ∧
      SpaceOKO (progO setup rA rM rB) w (initU d n δ r0 R0 a) n
        (max (inSpaceU d n δ r0 R0 a : ℝ) (ckSpaceU d n δ r0 R0 a ℓa ℓ : ℝ) +
          ((costP ℓa ℓ Ks + costR ℓa ℓ (KA + KM + KB) : ℕ) : ℝ)) ∧
      CoinWindowsOK (progO setup rA rM rB) w (initU d n δ r0 R0 a) n D D' ∧
      ∀ t < n, ∃ σ, IM t σ ∧ playedO (progO setup rA rM rB) w (initU d n δ r0 R0 a) t = σ.pts t := by
  obtain ⟨cP, cS, cZ1, cZ2, cA, cM, cB, cJ⟩ := progO_code setup rA rM rB
  have hlen := progO_length setup rA rM rB
  generalize hP : progO setup rA rM rB = P at cP cS cZ1 cZ2 cA cM cB cJ hlen
  set XO := ctxU w n δ r0 R0 a with hXO
  set s0 := initU d n δ r0 R0 a with hs0
  have hoffX : XO.off < 2 ^ ℓa := hoff
  have hoA : oA setup = oZ setup + 2 := rfl
  have hoM : oM setup rA = oA setup + xtlenO rA := rfl
  have hoB : oB setup rA rM = oM setup rA + xtlenO rM := rfl
  have hoJ : oJ setup rA rM rB = oB setup rA rM + xtlenO rB := rfl
  have hoZ : oZ setup = 3 + xtlenO setup := rfl
  -- the checkpoints: at the head of the round loop, with the invariant of round `t`
  let StartT : ℕ → State d → Prop := fun t b => (b.pc = oA setup ∧ b.mem T1 = 0 ∧ b.mem T2 = 0 ∧
    ∃ s σ, XSim XO.X s b ∧ Rep L σ s ∧ Inv t σ ∧ Clean ℓa ℓ s) ∧ ∃ k, b = runO P w s0 k
  -- the prologue, the setup and the first zeroing
  obtain ⟨t3, e3, p3, hs3, c3⟩ := prologueU_run (w := w) (n := n) (δ := δ) (r0 := r0) (R0 := R0) (a := a)
    (ℓ := ℓ) cP (by omega) hoff
  obtain ⟨k, s1, σ1, hk, he, hr, hinv⟩ := hsetup
  obtain ⟨n1, -, t7, e7, p7, hs7, c7⟩ := xtransferO hoffX he 3 t3 cS (by omega) p3 hs3
  obtain ⟨t8, e8, p8, hs8, z1, z2, c8⟩ := zero_scratchO (P := P) (w := w) (XO := XO) rfl cZ1 cZ2 (by omega)
    p7 hs7
  have hj0 : runO P w s0 (3 + n1 + 2) = t8 := by
    rw [runO_add, runO_add, e3]
    exact (congrArg (fun t => runO P w t 2) e7).trans e8
  have hst : StartT 0 (runO P w s0 (3 + n1 + 2)) := by
    refine ⟨?_, _, rfl⟩
    rw [hj0]
    exact ⟨p8, z1, z2, s1, σ1, hs8, hr, hinv, execBO_clean he (clean_zero (fun _ => rfl) (fun _ => rfl))⟩
  have hc0 : (runO P w s0 (3 + n1 + 2)).cost ≤ s0.cost + costP ℓa ℓ Ks := by
    rw [hj0]
    have : k * xstepCost ℓa ℓ ≤ Ks * xstepCost ℓa ℓ := Nat.mul_le_mul_right _ hk
    show t8.cost ≤ 0 + costP ℓa ℓ Ks
    unfold costP; omega
  -- the space of a checkpoint
  have hS : ∀ b, (∃ t, StartT t b) → SpaceLE b (ckSpaceU d n δ r0 R0 a ℓa ℓ : ℝ) := by
    rintro b ⟨t, ⟨-, h1, h2, s, σ, hs, -, -, hcl⟩, -⟩
    have := space_checkpoint (ℓi := lenIn d n δ r0 R0 a) hs hcl h1 h2
      (fun j _ => len_inputU_le (n := n) (δ := δ) (r0 := r0) (R0 := R0) (a := a) j) hoffX h4
    unfold ckSpaceU
    exact this
  -- a round, with its two inner checkpoints
  have hseg : ∀ t b, StartT t b → t < n → ∃ j, StartT (t + 1) (runO P w b j) ∧ b.rounds = t ∧
      (runO P w b j).rounds = t + 1 ∧ (runO P w b j).cost ≤ b.cost + costR ℓa ℓ (KA + KM + KB) ∧
      (∃ jA, (runO P w b jA).rounds = t ∧ (runO P w b jA).coins = D' t) ∧
      (∃ jM σ, IM t σ ∧ (runO P w b jM).rounds = t + 1 ∧ (runO P w b jM).coins = D' t ∧
        toE ((runO P w b jM).pts t) = σ.pts t) := by
    rintro t b ⟨⟨hpc, -, -, s, σ, hs, hr, hinv, hcl⟩, kb, rfl⟩ ht
    obtain ⟨kA, sA, σA, hkA, heA, hrA, hqA⟩ := hA t ht σ hinv s hr
    obtain ⟨nA, -, tA, eA, pA, hsA, cA'⟩ := xtransferO hoffX heA _ _ cA (by omega) hpc hs
    obtain ⟨kM, sM, σM, hkM, heM, hrM, hqM⟩ := hM t ht σA hqA sA hrA
    obtain ⟨nM, -, tM, eM, pM, hsM, cM'⟩ := xtransferO hoffX heM _ _ cM (by omega) pA hsA
    obtain ⟨kB, sB, σB, hkB, heB, hrB, hqB⟩ := hB t ht σM hqM sM hrM
    obtain ⟨nB, -, tB, eB, pB, hsB, cB'⟩ := xtransferO hoffX heB _ _ cB (by omega) pM hsM
    obtain ⟨tJ, eJ, pJ, hsJ, cJ'⟩ := xsimO_jmp (P := P) (w := w) (XO := XO) rfl cJ (by omega) pB hsB
    obtain ⟨tZ, eZ, pZ, hsZ, z1, z2, cZ⟩ := zero_scratchO (P := P) (w := w) (XO := XO) rfl cZ1 cZ2 (by omega) pJ hsJ
    have eA' : runO P w (runO P w s0 kb) nA = tA := eA
    have eM' : runO P w (runO P w s0 kb) (nA + nM) = tM := by rw [runO_add, eA']; exact eM
    have eB' : runO P w (runO P w s0 kb) (nA + nM + nB) = tB := by rw [runO_add, eM']; exact eB
    have eZ' : runO P w (runO P w s0 kb) (nA + nM + nB + 1 + 2) = tZ := by
      rw [runO_add, runO_add, eB', eJ, eZ]
    have rA' := hIA t σA hqA
    have rM' := hIM t σM hqM
    refine ⟨nA + nM + nB + 1 + 2, ?_, ?_, ?_, ?_, ⟨nA, ?_, ?_⟩, ⟨nA + nM, σM, hqM, ?_, ?_, ?_⟩⟩
    · refine ⟨?_, kb + (nA + nM + nB + 1 + 2), (runO_add P w s0 kb _).symm⟩
      rw [eZ']
      exact ⟨pZ, z1, z2, sB, σB, hsZ, hrB, hqB, execBO_clean heB (execBO_clean heM (execBO_clean heA hcl))⟩
    · rw [hs.rounds, hr.rounds, hIr t σ hinv]
    · rw [eZ', hsZ.rounds, hrB.rounds, hIr (t + 1) σB hqB]
    · rw [eZ', cZ, cJ']
      have h1 : kA * xstepCost ℓa ℓ ≤ KA * xstepCost ℓa ℓ := Nat.mul_le_mul_right _ hkA
      have h2 : kM * xstepCost ℓa ℓ ≤ KM * xstepCost ℓa ℓ := Nat.mul_le_mul_right _ hkM
      have h3 : kB * xstepCost ℓa ℓ ≤ KB * xstepCost ℓa ℓ := Nat.mul_le_mul_right _ hkB
      have e : (KA + KM + KB) * xstepCost ℓa ℓ = KA * xstepCost ℓa ℓ + KM * xstepCost ℓa ℓ +
        KB * xstepCost ℓa ℓ := by ring
      unfold costR; omega
    · rw [eA', hsA.rounds, hrA.rounds, rA'.1]
    · rw [eA', hsA.coins, hrA.draws, rA'.2]
    · rw [eM', hsM.rounds, hrM.rounds, rM'.1]
    · rw [eM', hsM.coins, hrM.draws, rM'.2]
    · rw [eM', hsM.pts, hrM.pts]
  -- every round `t ≤ n` has a checkpoint
  have hall : ∀ t ≤ n, ∃ b, StartT t b := by
    intro t
    induction t with
    | zero => exact fun _ => ⟨_, hst⟩
    | succ t ih =>
      intro ht
      obtain ⟨b, hb⟩ := ih (by omega)
      obtain ⟨j, hj, -⟩ := hseg t b hb (by omega)
      exact ⟨_, hj⟩
  -- the cost and space clauses
  have hsegD : ∀ b : State d, (∃ t, StartT t b) → b.rounds < n → ∃ j, (∃ t, StartT t (runO P w b j)) ∧
      b.rounds < (runO P w b j).rounds ∧ (runO P w b j).cost ≤ b.cost + costR ℓa ℓ (KA + KM + KB) := by
    rintro b ⟨t, hb⟩ hlt
    have hbr : b.rounds = t := by
      obtain ⟨⟨-, -, -, s, σ, hs, hr, hinv, -⟩, -⟩ := hb
      rw [hs.rounds, hr.rounds, hIr t σ hinv]
    obtain ⟨j, hj, -, h2, h3, -⟩ := hseg t b hb (by omega)
    exact ⟨j, ⟨t + 1, hj⟩, by omega, h3⟩
  obtain ⟨hC, hSp⟩ := driverO (P := P) (w := w) (fun b => ∃ t, StartT t b) input_spaceU (3 + n1 + 2) ⟨0, hst⟩
    hc0 hS hsegD
  -- the inner checkpoints of every round `t < n`, as steps of the run
  have hck : ∀ t < n, (∃ kA, (runO P w s0 kA).rounds = t ∧ (runO P w s0 kA).coins = D' t) ∧
      ∃ kM σ, IM t σ ∧ (runO P w s0 kM).rounds = t + 1 ∧ (runO P w s0 kM).coins = D' t ∧
        toE ((runO P w s0 kM).pts t) = σ.pts t := by
    intro t ht
    obtain ⟨b, hb⟩ := hall t ht.le
    obtain ⟨kb, rfl⟩ := hb.2
    obtain ⟨j, -, -, -, -, ⟨jA, hA1, hA2⟩, ⟨jM, σ, hσ, hM1, hM2, hM3⟩⟩ := hseg t _ hb ht
    rw [← runO_add] at hA1 hA2 hM1 hM2 hM3
    exact ⟨⟨_, hA1, hA2⟩, _, σ, hσ, hM1, hM2, hM3⟩
  refine ⟨hP ▸ hC, hP ▸ hSp, ?_, ?_⟩
  · -- the coin clause
    subst hP
    intro t ht k
    obtain ⟨⟨kA, hA1, hA2⟩, kM, -, -, hM1, hM2, -⟩ := hck t ht
    refine ⟨fun hk => ?_, fun hk => ?_, fun hk => ?_⟩
    · rcases le_or_gt k kM with h | h
      · exact hM2 ▸ (RunFacts.runO_mono (progO setup rA rM rB) w s0 h).2.1
      · have := (RunFacts.runO_mono (progO setup rA rM rB) w s0 h.le).1
        omega
    · rcases le_or_gt kA k with h | h
      · exact hA2 ▸ (RunFacts.runO_mono (progO setup rA rM rB) w s0 h).2.1
      · have := (RunFacts.runO_mono (progO setup rA rM rB) w s0 h.le).1
        omega
    · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      obtain ⟨-, kM', -, -, hM1', hM2', -⟩ := hck t' (by omega)
      rcases le_or_gt k kM' with h | h
      · exact ((RunFacts.runO_mono (progO setup rA rM rB) w s0 h).2.1.trans hM2'.le).trans (hDD t')
      · have := (RunFacts.runO_mono (progO setup rA rM rB) w s0 h.le).1
        omega
  · -- the points
    subst hP
    intro t ht
    obtain ⟨-, kM, σ, hσ, hM1, -, hM3⟩ := hck t ht
    exact ⟨σ, hσ, by rw [RunFacts.playedO_eq_pts (progO setup rA rM rB) w s0 (by omega : t < (runO (progO setup rA rM rB) w s0 kM).rounds), hM3]⟩

end Prog

end AdversarialBco.Unified.ProgO
