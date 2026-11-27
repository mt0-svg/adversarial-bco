/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PolyCode
public import AdversarialBco.Unified.PolyRS
public import AdversarialBco.StatementConj1Bit

@[expose] public section

/-!
# UNI-POLY, part 11: one instruction of `P`, one block of the compiled program

* `blk_step`: a block that runs within the bound `L` in at most `nb` steps to a state related to the next state of `P`
  takes the compiled program there, at a cost of at most `nb · U d L`.
* `Rel.upd`: the relation after a write to a cell of `P`.
* `cost_poly`: `nb · U d (c + Kd) ≤ Kc0 · c^3` for a block of at most `N1 + 4 c` steps.
* the simple instructions (`const`, `add`, `sub`, `mul`, `div`, `coins`, `obs`), `load`, `store` and the jumps.
-/

namespace AdversarialBco.UniPoly

open AdversarialBco BitRAM BitRAMO RCmd
open AdversarialBco.Bit.Transfer (B.CodeAt B.step_const B.step_add B.step_sub B.step_load B.step_store B.step_jlt
  B.step_jmp B.run_one)

variable {d : ℕ}

/-! ## The oracle machine on a base instruction -/

theorem stepO_base {P : List InstrO} {wO : WorldO d} {s : State d} {i : Instr} (h : P[s.pc]? = some (.base i)) :
    stepO P wO s = step (lowerP P) wO.toW s := by simp [stepO, h]

theorem lowerP_base {P : List InstrO} {k : ℕ} {i : Instr} (h : P[k]? = some (.base i)) :
    (lowerP P)[k]? = some i := by
  simp [lowerP, h, lowerI]

/-! ## The relation -/

/-- The relation after a block that writes `v` into the cell of `P`'s `x` and touches nothing else of `P`. -/
theorem Rel.upd {F : ℕ → ℕ} {Fix : ℤ → ℤ} {s t s' t' : State d} (hR : Rel F Fix s t) (x v : ℤ)
    (hpc : t'.pc = F s'.pc) (hm : t'.mem = Function.update t.mem (φ x) v) (hs : s'.mem = Function.update s.mem x v)
    (hco : t'.coins = s'.coins) (hro : t'.rounds = s'.rounds) (hpt : t'.pts = s'.pts) : Rel F Fix s' t' where
  pc := hpc
  z y := by
    rw [hm, hs]
    by_cases hy : y = x
    · subst hy; simp
    · rw [Function.update_of_ne (φ_ne hy), Function.update_of_ne hy, hR.z]
  fix c hc := by rw [hm, Function.update_of_ne (φ_ne_of_gt hc).symm, hR.fix c hc]
  coins := hco
  rounds := hro
  pts := hpt

/-! ## A block -/

variable {pro : List Instr} {P : List InstrO} {Fix : ℤ → ℤ} {s s' t : State d} {w : World d}

/-- A block that runs to a state related to the next state of `P`. -/
theorem blk_step {L nb : ℕ} (hR : Rel (Fa P pro.length) Fix s t) (hk : s.pc < P.length)
    (hcode : code (Fa P pro.length) P[s.pc] (Fa P pro.length s.pc) = rtr (blk P[s.pc]) (Fa P pro.length s.pc))
    (hlen : blen P[s.pc] = rlen (blk P[s.pc])) (hpc : s'.pc = s.pc + 1)
    (hRS : RS w L (blk P[s.pc]) t
      (fun n t' => n ≤ nb ∧ Rel (Fa P pro.length) Fix s' { t' with pc := Fa P pro.length s'.pc })) :
    ∃ j, Rel (Fa P pro.length) Fix s' (run (compP pro P) w t j) ∧
      (run (compP pro P) w t j).cost ≤ t.cost + nb * U d L := by
  obtain ⟨n, t', hx, hn, hrel⟩ := hRS
  have hc := codeAt_blk pro P hk
  rw [hcode] at hc
  have hrun := rtr_run hx _ hc
  have ht : ({ t with pc := Fa P pro.length s.pc } : State d) = t := by rw [← hR.pc]
  rw [ht] at hrun
  have hF : Fa P pro.length s.pc + rlen (blk P[s.pc]) = Fa P pro.length s'.pc := by
    rw [hpc, Fa_succ, blenAt_of P hk, hlen]
  refine ⟨n, ?_, ?_⟩
  · rw [hrun, hF]; exact hrel
  · rw [hrun]
    have h1 := RX.cost_le hx
    have h2 : n * U d L ≤ nb * U d L := Nat.mul_le_mul_right _ hn
    dsimp only; omega

/-- A block of one instruction. -/
theorem ins_step {L : ℕ} {j : Instr} (hR : Rel (Fa P pro.length) Fix s t) (hk : s.pc < P.length)
    (hb : blk P[s.pc] = .ins j) (hcode : code (Fa P pro.length) P[s.pc] (Fa P pro.length s.pc) =
      rtr (blk P[s.pc]) (Fa P pro.length s.pc)) (hlen : blen P[s.pc] = rlen (blk P[s.pc])) (hpc : s'.pc = s.pc + 1)
    (hok : InsOK w L t j) (hrel : Rel (Fa P pro.length) Fix s' { stepI w j t with pc := Fa P pro.length s'.pc }) :
    ∃ j, Rel (Fa P pro.length) Fix s' (run (compP pro P) w t j) ∧
      (run (compP pro P) w t j).cost ≤ t.cost + 1 * U d L :=
  blk_step hR hk hcode hlen hpc (by rw [hb]; exact RS.ins hok ⟨le_rfl, hrel⟩)

/-! ## The cost of a block -/

/-- The bound added to the cost of an instruction of `P`. -/
def Kd (d m Ms LY : ℕ) : ℕ := 20 + (d + 1) * (Ms + 2) + LY + m

/-- The steps of a block, but for the `4 c` of `obsR`. -/
def N1 (d m : ℕ) : ℕ := (d + 1) * 25 + m * (d * 19 + 29) + 100

/-- The constant of the cubic bound on the cost of a block. -/
def Kc0 (d m Ms LY : ℕ) : ℕ := (N1 d m + 4) * U d (1 + Kd d m Ms LY)

theorem U_mono {L L' : ℕ} (h : L ≤ L') : U d L ≤ U d L' := by
  unfold U
  have : (L + 1) ^ 2 ≤ (L' + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have : (d + 1) * (1 + 2 * L) ≤ (d + 1) * (1 + 2 * L') := Nat.mul_le_mul_left _ (by omega)
  omega

theorem U_scale {c K : ℕ} (hc : 1 ≤ c) : U d (c + K) ≤ c ^ 2 * U d (1 + K) := by
  unfold U
  have h1 : c + K ≤ c * (1 + K) := by nlinarith
  have h2 : (c + K + 1) ^ 2 ≤ c ^ 2 * (1 + K + 1) ^ 2 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by nlinarith) 2
  have h3 : 1 ≤ c ^ 2 := Nat.one_le_pow _ _ hc
  have h4 : c ≤ c ^ 2 := by nlinarith
  have h5 : (d + 1) * (1 + 2 * (c + K)) ≤ c ^ 2 * ((d + 1) * (1 + 2 * (1 + K))) := by
    have : 1 + 2 * (c + K) ≤ c ^ 2 * (1 + 2 * (1 + K)) := by nlinarith
    calc (d + 1) * (1 + 2 * (c + K)) ≤ (d + 1) * (c ^ 2 * (1 + 2 * (1 + K))) := Nat.mul_le_mul_left _ this
      _ = c ^ 2 * ((d + 1) * (1 + 2 * (1 + K))) := by ring
  have h6 : 6 * (c + K) ≤ c ^ 2 * (6 * (1 + K)) := by nlinarith
  nlinarith

theorem cost_poly {m Ms LY c nb : ℕ} (hc : 1 ≤ c) (hnb : nb ≤ N1 d m + 4 * c) :
    nb * U d (c + Kd d m Ms LY) ≤ Kc0 d m Ms LY * c ^ 3 := by
  have h1 := U_scale (d := d) (K := Kd d m Ms LY) hc
  have h2 : nb ≤ (N1 d m + 4) * c := by nlinarith
  unfold Kc0
  calc nb * U d (c + Kd d m Ms LY) ≤ ((N1 d m + 4) * c) * (c ^ 2 * U d (1 + Kd d m Ms LY)) :=
        Nat.mul_le_mul h2 h1
    _ = (N1 d m + 4) * U d (1 + Kd d m Ms LY) * c ^ 3 := by ring

/-! ## The cells the blocks need -/

/-- The cells above `-N0` at every block boundary: the scratch cells at `0`, the buffer address in `cYB`, the buffer at
`0` above the input, `d` and `m` in the cells `0` and `2`, the rows of the input. -/
structure FixOK (d m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (YB : ℤ) (Fix : ℤ → ℤ) : Prop where
  scr : ∀ c, IsScr c → Fix c = 0
  yb : Fix cYB = YB
  ybm : 3 + 2 * (((d : ℤ) + 1) * m) ≤ YB
  ybz : ∀ c, YB ≤ c → c ≤ YB + d → Fix c = 0
  d0 : Fix 0 = d
  m2 : Fix 2 = m
  row : ∀ i (hi : i < m), ∀ j ≤ d, Fix (3 + 2 * (((d : ℤ) + 1) * i + j)) = (entry A b ⟨i, hi⟩ j).num ∧
    Fix (3 + 2 * (((d : ℤ) + 1) * i + j) + 1) = (entry A b ⟨i, hi⟩ j).den

theorem isScr_of {c : ℤ} (h1 : -627 ≤ c) (h2 : c ≤ -602) : IsScr c := Or.inr ⟨h1, h2⟩

theorem Rel.scr {F : ℕ → ℕ} {Fix : ℤ → ℤ} {s t : State d} {m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    {YB : ℤ} (hR : Rel F Fix s t) (hF : FixOK d m A b YB Fix) {c : ℤ} (hc : IsScr c) : t.mem c = 0 := by
  rw [hR.fix c (by rcases hc with h | h <;> simp only [N0] <;> omega), hF.scr c hc]

theorem reading_congr {w : World d} {s t : State d} (hr : t.rounds = s.rounds) (hp : t.pts = s.pts) (p : ℕ) :
    reading w t p = reading w s p := by
  simp only [reading, feedback, hr, hp]

/-! ## The simple instructions -/

theorem getElem?_of {k : ℕ} {i : InstrO} (hk : k < P.length) (hP : P[k] = i) : P[k]? = some i := by
  rw [List.getElem?_eq_getElem hk, hP]

/-- A block of one instruction that writes `v` into the cell of `x`. -/
theorem upd_case {L : ℕ} {wO : WorldO d} {j : Instr} {x v : ℤ} {k : ℕ} (hR : Rel (Fa P pro.length) Fix s t)
    (hk : s.pc < P.length) (hb : blk P[s.pc] = .ins j)
    (hcode : code (Fa P pro.length) P[s.pc] (Fa P pro.length s.pc) = rtr (blk P[s.pc]) (Fa P pro.length s.pc))
    (hlen : blen P[s.pc] = rlen (blk P[s.pc])) (hpl : Plain j) (hnj : NJ j)
    (hs' : stepO P wO s = { s with pc := s.pc + 1, mem := Function.update s.mem x v, cost := s.cost + k })
    (hm : (stepI w j t).mem = Function.update t.mem (φ x) v) (hok : InsOK w L t j) :
    ∃ n, Rel (Fa P pro.length) Fix (stepO P wO s) (run (compP pro P) w t n) ∧
      (run (compP pro P) w t n).cost ≤ t.cost + 1 * U d L := by
  rw [hs']
  have hS := stepI_same (w := w) (t := t) hpl hnj
  exact ins_step hR hk hb hcode hlen rfl hok
    (hR.upd x v rfl hm rfl (hS.1.trans hR.coins) (hS.2.1.trans hR.rounds) (hS.2.2.trans hR.pts))

/-- The cost increment of the step of `P`. -/
noncomputable def dC (P : List InstrO) (wO : WorldO d) (s : State d) : ℕ := (stepO P wO s).cost - s.cost

/-- One step of `P` at a base instruction other than `play`, `load`, `store` and the jumps: the block is that instruction
on the cells `φ`. -/
theorem sim_simple {wO : WorldO d} (hW : wO.toW = w) (hR : Rel (Fa P pro.length) Fix s t)
    (hk : s.pc < P.length) {i : Instr} (hP : P[s.pc] = .base i)
    (hi : ∀ tg a b src, i ≠ .jlt a b tg ∧ i ≠ .jmp tg ∧ i ≠ .play src ∧ i ≠ .load a b ∧ i ≠ .store a b) :
    ∃ n, Rel (Fa P pro.length) Fix (stepO P wO s) (run (compP pro P) w t n) ∧
      (run (compP pro P) w t n).cost ≤ t.cost + 1 * U d (dC P wO s + 11) := by
  have h? := getElem?_of hk hP
  have hs0 := stepO_base (wO := wO) h?
  have hl := lowerP_base h?
  rw [hW] at hs0
  have hz := hR.z
  cases i with
  | const dst v =>
    have hs' := hs0.trans (B.step_const hl)
    have hc : dC P wO s = 1 + len dst + len v := by simp only [dC, hs']; omega
    rw [hc]
    refine upd_case (j := .const (φ dst) v) hR hk (by rw [hP]; rfl) (by rw [hP]; rfl) (by rw [hP]; rfl) trivial
      trivial hs' (stepI_const_mem _ _) ⟨(len_φ _).trans (by omega), by omega⟩
  | add dst a b =>
    have hs' := hs0.trans (B.step_add hl)
    have hc : dC P wO s = 1 + len dst + len a + len b + len (s.mem a) + len (s.mem b) := by
      simp only [dC, hs']; omega
    rw [hc]
    refine upd_case (j := .add (φ dst) (φ a) (φ b)) hR hk (by rw [hP]; rfl) (by rw [hP]; rfl) (by rw [hP]; rfl)
      trivial trivial hs' (by rw [stepI_add_mem, hz, hz]) ⟨(len_φ _).trans (by omega), (len_φ _).trans (by omega),
        (len_φ _).trans (by omega), by rw [hz]; omega, by rw [hz]; omega⟩
  | sub dst a b =>
    have hs' := hs0.trans (B.step_sub hl)
    have hc : dC P wO s = 1 + len dst + len a + len b + len (s.mem a) + len (s.mem b) := by
      simp only [dC, hs']; omega
    rw [hc]
    refine upd_case (j := .sub (φ dst) (φ a) (φ b)) hR hk (by rw [hP]; rfl) (by rw [hP]; rfl) (by rw [hP]; rfl)
      trivial trivial hs' (by rw [stepI_sub_mem, hz, hz]) ⟨(len_φ _).trans (by omega), (len_φ _).trans (by omega),
        (len_φ _).trans (by omega), by rw [hz]; omega, by rw [hz]; omega⟩
  | mul dst a b =>
    have hs' : stepO P wO s =
        { s with pc := s.pc + 1, mem := Function.update s.mem dst (s.mem a * s.mem b),
                 cost := s.cost + (1 + len dst + len a + len b + (len (s.mem a) + 1) * (len (s.mem b) + 1)) } := by
      rw [hs0]; simp [step, hl]
    have hc : dC P wO s = 1 + len dst + len a + len b + (len (s.mem a) + 1) * (len (s.mem b) + 1) := by
      simp only [dC, hs']; omega
    rw [hc]
    have h1 : len (s.mem a) ≤ (len (s.mem a) + 1) * (len (s.mem b) + 1) := by nlinarith
    have h2 : len (s.mem b) ≤ (len (s.mem a) + 1) * (len (s.mem b) + 1) := by nlinarith
    refine upd_case (j := .mul (φ dst) (φ a) (φ b)) hR hk (by rw [hP]; rfl) (by rw [hP]; rfl) (by rw [hP]; rfl)
      trivial trivial hs' (by rw [stepI_mul_mem, hz, hz]) ⟨(len_φ _).trans (by omega), (len_φ _).trans (by omega),
        (len_φ _).trans (by omega), by rw [hz]; omega, by rw [hz]; omega⟩
  | div dst a b =>
    have hs' : stepO P wO s =
        { s with pc := s.pc + 1, mem := Function.update s.mem dst (s.mem a / s.mem b),
                 cost := s.cost + (1 + len dst + len a + len b + (len (s.mem a) + 1) * (len (s.mem b) + 1)) } := by
      rw [hs0]; simp [step, hl]
    have hc : dC P wO s = 1 + len dst + len a + len b + (len (s.mem a) + 1) * (len (s.mem b) + 1) := by
      simp only [dC, hs']; omega
    rw [hc]
    have h1 : len (s.mem a) ≤ (len (s.mem a) + 1) * (len (s.mem b) + 1) := by nlinarith
    have h2 : len (s.mem b) ≤ (len (s.mem a) + 1) * (len (s.mem b) + 1) := by nlinarith
    refine upd_case (j := .div (φ dst) (φ a) (φ b)) hR hk (by rw [hP]; rfl) (by rw [hP]; rfl) (by rw [hP]; rfl)
      trivial trivial hs' (by rw [stepI_div_mem, hz, hz]) ⟨(len_φ _).trans (by omega), (len_φ _).trans (by omega),
        (len_φ _).trans (by omega), by rw [hz]; omega, by rw [hz]; omega⟩
  | obs dst prec =>
    have hs' : stepO P wO s =
        { s with pc := s.pc + 1,
                 mem := Function.update s.mem dst (reading w s (s.mem prec).toNat),
                 cost := s.cost + (1 + len dst + len prec + len (s.mem prec) + (s.mem prec).toNat +
                   len (reading w s (s.mem prec).toNat)) } := by
      rw [hs0]; simp [step, hl]
    have hc : dC P wO s = 1 + len dst + len prec + len (s.mem prec) + (s.mem prec).toNat +
        len (reading w s (s.mem prec).toNat) := by
      simp only [dC, hs']; omega
    rw [hc]
    have hrd := reading_congr (w := w) hR.rounds hR.pts (s.mem prec).toNat
    refine upd_case (j := .obs (φ dst) (φ prec)) hR hk (by rw [hP]; rfl) (by rw [hP]; rfl) (by rw [hP]; rfl)
      trivial trivial hs' (by rw [stepI_obs_mem, hz, hrd]) ⟨(len_φ _).trans (by omega), (len_φ _).trans (by omega),
        by rw [hz]; omega, by rw [hz]; omega, by rw [hz, hrd]; omega⟩
  | coins dst cnt =>
    have hs' : stepO P wO s =
        { s with pc := s.pc + 1,
                 mem := Function.update s.mem dst (readCoins w.cs s.coins (s.mem cnt).toNat),
                 coins := s.coins + (s.mem cnt).toNat,
                 cost := s.cost + (1 + len dst + len cnt + len (s.mem cnt) + (s.mem cnt).toNat) } := by
      rw [hs0]; simp [step, hl]
    have hc : dC P wO s = 1 + len dst + len cnt + len (s.mem cnt) + (s.mem cnt).toNat := by
      simp only [dC, hs']; omega
    rw [hc, hs']
    refine ins_step (j := .coins (φ dst) (φ cnt)) hR hk (by rw [hP]; rfl) (by rw [hP]; rfl) (by rw [hP]; rfl) rfl
      ⟨(len_φ _).trans (by omega), (len_φ _).trans (by omega), by rw [hz]; omega, by rw [hz]; omega⟩
      (hR.upd dst _ rfl (by rw [stepI_coins_mem, hz, hR.coins]) rfl
        (by rw [stepI_coins_coins, hz, hR.coins]) (by simp [stepI, step, hR.rounds]) (by simp [stepI, step, hR.pts]))
  | load a b => exact absurd rfl (hi 0 a b 0).2.2.2.1
  | store a b => exact absurd rfl (hi 0 a b 0).2.2.2.2
  | jlt a b tg => exact absurd rfl (hi tg a b 0).1
  | jmp tg => exact absurd rfl (hi tg 0 0 0).2.1
  | play src => exact absurd rfl (hi 0 0 0 src).2.2.1

/-! ## `load`, `store` -/

theorem sim_load {wO : WorldO d} {m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {YB : ℤ}
    (hW : wO.toW = w) (hF : FixOK d m A b YB Fix) (hR : Rel (Fa P pro.length) Fix s t)
    (hk : s.pc < P.length) {dst src : ℤ} (hP : P[s.pc] = .base (.load dst src)) :
    ∃ n, Rel (Fa P pro.length) Fix (stepO P wO s) (run (compP pro P) w t n) ∧
      (run (compP pro P) w t n).cost ≤ t.cost + 9 * U d (dC P wO s + 11) := by
  have h? := getElem?_of hk hP
  have hs0 := stepO_base (wO := wO) h?
  rw [hW] at hs0
  have hs' := hs0.trans (B.step_load (lowerP_base h?))
  have hc : dC P wO s = 1 + len dst + len src + len (s.mem src) + len (s.mem (s.mem src)) := by
    simp only [dC, hs']; omega
  rw [hc, hs']
  have hz := hR.z
  refine blk_step hR hk (by rw [hP]; rfl) (by rw [hP]; rfl) rfl ?_
  rw [hP]
  refine (rs_LOADB (hR.scr hF (Or.inl rfl)) (hR.scr hF (isScr_of (by norm_num) (by norm_num)))
    (hR.scr hF (isScr_of (by norm_num) (by norm_num))) (by rw [hz]; omega) (by omega) (by omega)
    (by rw [hz, hz]; omega)).mono ?_
  rintro n t' ⟨hn, hm, hS⟩
  exact ⟨hn, hR.upd dst _ rfl (by rw [hm, hz, hz]) rfl (hS.1.trans hR.coins) (hS.2.1.trans hR.rounds)
    (hS.2.2.trans hR.pts)⟩

theorem sim_store {wO : WorldO d} {m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {YB : ℤ}
    (hW : wO.toW = w) (hF : FixOK d m A b YB Fix) (hR : Rel (Fa P pro.length) Fix s t)
    (hk : s.pc < P.length) {dst src : ℤ} (hP : P[s.pc] = .base (.store dst src)) :
    ∃ n, Rel (Fa P pro.length) Fix (stepO P wO s) (run (compP pro P) w t n) ∧
      (run (compP pro P) w t n).cost ≤ t.cost + 9 * U d (dC P wO s + 11) := by
  have h? := getElem?_of hk hP
  have hs0 := stepO_base (wO := wO) h?
  rw [hW] at hs0
  have hs' := hs0.trans (B.step_store (lowerP_base h?))
  have hc : dC P wO s = 1 + len dst + len src + len (s.mem dst) + len (s.mem src) := by
    simp only [dC, hs']; omega
  rw [hc, hs']
  have hz := hR.z
  refine blk_step hR hk (by rw [hP]; rfl) (by rw [hP]; rfl) rfl ?_
  rw [hP]
  refine (rs_STOREB (hR.scr hF (Or.inl rfl)) (hR.scr hF (isScr_of (by norm_num) (by norm_num)))
    (hR.scr hF (isScr_of (by norm_num) (by norm_num))) (by rw [hz]; omega) (by omega) (by omega)
    (by rw [hz]; omega)).mono ?_
  rintro n t' ⟨hn, hm, hS⟩
  exact ⟨hn, hR.upd (s.mem dst) _ rfl (by rw [hm, hz, hz]) rfl (hS.1.trans hR.coins) (hS.2.1.trans hR.rounds)
    (hS.2.2.trans hR.pts)⟩

/-! ## The jumps -/

theorem sim_jlt {wO : WorldO d} (hW : wO.toW = w) (hR : Rel (Fa P pro.length) Fix s t)
    (hk : s.pc < P.length) {a b : ℤ} {tg : ℕ} (hP : P[s.pc] = .base (.jlt a b tg)) :
    ∃ n, Rel (Fa P pro.length) Fix (stepO P wO s) (run (compP pro P) w t n) ∧
      (run (compP pro P) w t n).cost ≤ t.cost + 1 * U d (dC P wO s + 11) := by
  have h? := getElem?_of hk hP
  have hs0 := stepO_base (wO := wO) h?
  rw [hW] at hs0
  have hs' := hs0.trans (B.step_jlt (lowerP_base h?))
  have hc : dC P wO s = 1 + len a + len b + len (s.mem a) + len (s.mem b) := by
    simp only [dC, hs']; omega
  rw [hc, hs']
  have hz := hR.z
  have hcd := codeAt_blk pro P hk
  rw [hP] at hcd
  have hj : (compP pro P)[Fa P pro.length s.pc]? = some (.jlt (φ a) (φ b) (Fa P pro.length tg)) := hcd.cons_head
  have ht : ({ t with pc := Fa P pro.length s.pc } : State d) = t := by rw [← hR.pc]
  have hrun := run_jlt (w := w) (t := t) hj
  rw [ht] at hrun
  have hT : TestOK (1 + len a + len b + len (s.mem a) + len (s.mem b) + 11) (φ a) (φ b) t :=
    ⟨(len_φ _).trans (by omega), (len_φ _).trans (by omega), by rw [hz]; omega, by rw [hz]; omega⟩
  refine ⟨1, ?_, ?_⟩
  · rw [hrun]
    have hF1 : Fa P pro.length (s.pc + 1) = Fa P pro.length s.pc + 1 := by
      rw [Fa_succ, blenAt_of P hk, hP]; rfl
    refine ⟨?_, fun x => hR.z x, fun c hc => hR.fix c hc, hR.coins, hR.rounds, hR.pts⟩
    simp only [hz]
    split_ifs <;> simp [hF1]
  · rw [hrun]
    have := tcost_le_U1 (d := d) hT
    simp only [addC]; omega

theorem sim_jmp {wO : WorldO d} (hW : wO.toW = w) (hR : Rel (Fa P pro.length) Fix s t)
    (hk : s.pc < P.length) {tg : ℕ} (hP : P[s.pc] = .base (.jmp tg)) :
    ∃ n, Rel (Fa P pro.length) Fix (stepO P wO s) (run (compP pro P) w t n) ∧
      (run (compP pro P) w t n).cost ≤ t.cost + 1 * U d (dC P wO s + 11) := by
  have h? := getElem?_of hk hP
  have hs0 := stepO_base (wO := wO) h?
  rw [hW] at hs0
  have hs' := hs0.trans (B.step_jmp (lowerP_base h?))
  rw [hs']
  have hcd := codeAt_blk pro P hk
  rw [hP] at hcd
  have hj : (compP pro P)[Fa P pro.length s.pc]? = some (.jmp (Fa P pro.length tg)) := hcd.cons_head
  have ht : ({ t with pc := Fa P pro.length s.pc } : State d) = t := by rw [← hR.pc]
  have hrun := run_jmp (w := w) (t := t) hj
  rw [ht] at hrun
  refine ⟨1, ?_, ?_⟩
  · rw [hrun]
    exact ⟨rfl, fun x => hR.z x, fun c hc => hR.fix c hc, hR.coins, hR.rounds, hR.pts⟩
  · rw [hrun]; simp only [addC]; unfold U; omega

end AdversarialBco.UniPoly
