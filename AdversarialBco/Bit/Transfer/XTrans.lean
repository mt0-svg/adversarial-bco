/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XLang

@[expose] public section

/-!
# The compiler, part 2: the extended language compiled to the bit machine, with the real cells at an offset

* `xtr c o`: the code of `c : XCmd` for the frozen bit machine, placed at address `o`. Natural register `i` is the
  cell `rg i = -(i + 4)` as in Trans.lean; the real cell `j` is the cell `j + off`, `off` held in the cell `TO = -3`;
  the cells `0, ..., off - 1` hold the input and are never written; `T1 = -1`, `T2 = -2` are scratch. An access to a
  real cell adds the offset (`add T1 (rg a) TO; load T1 T1`), so the layout of `Poly/MachVL.lean` is unchanged.
* `XSim X s t`: the bit state `t` holds the registers, the real cells (at the offset), the offset, the input, the
  coins used, the rounds and the points played of the real state `s`.
* `xtransfer`: if `XExecB X ℓa ℓ c s k s'` and `t` simulates `s`, the code `xtr c o` runs from `t` within `7 k` steps
  of the bit machine in the world `X.wb` to a state simulating `s'`, at cost at most `k * xstepCost ℓa ℓ`,
  `xstepCost ℓa ℓ = 40 + 12 ℓa + 4 ℓ + (ℓa + ℓ + 1)²`, when `off < 2 ^ ℓa`.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco
open AdversarialBco.Poly.Mach (Prim Cmd condR condN)
open Function

variable {d : ℕ}

/-! ## Cells -/

/-- The cell holding the offset of the real cells. -/
def TO : ℤ := -3

@[simp] theorem TO_ne_T1 : TO ≠ T1 := by unfold TO T1; omega
@[simp] theorem TO_ne_T2 : TO ≠ T2 := by unfold TO T2; omega
@[simp] theorem rg_ne_TO (i : ℕ) : rg i ≠ TO := by unfold rg TO; omega
@[simp] theorem TO_ne_rg (i : ℕ) : TO ≠ rg i := by unfold rg TO; omega
@[simp] theorem cl_ne_T1 (j o : ℕ) : (j : ℤ) + (o : ℤ) ≠ T1 := by unfold T1; omega
@[simp] theorem cl_ne_T2 (j o : ℕ) : (j : ℤ) + (o : ℤ) ≠ T2 := by unfold T2; omega
@[simp] theorem cl_ne_TO (j o : ℕ) : (j : ℤ) + (o : ℤ) ≠ TO := by unfold TO; omega
@[simp] theorem cl_ne_rg (j o i : ℕ) : (j : ℤ) + (o : ℤ) ≠ rg i := by unfold rg; omega
@[simp] theorem TO_ne_cl (j o : ℕ) : TO ≠ (j : ℤ) + (o : ℤ) := by unfold TO; omega
@[simp] theorem rg_ne_cl (j o i : ℕ) : rg i ≠ (j : ℤ) + (o : ℤ) := by unfold rg; omega
@[simp] theorem nat_ne_rg (i j : ℕ) : (j : ℤ) ≠ rg i := by unfold rg; omega

theorem nat_ne_cl {j k o : ℕ} (h : j < o) : (j : ℤ) ≠ (k : ℤ) + (o : ℤ) := by omega

theorem len_TO : BitRAM.len TO = 2 := rfl

theorem len_cl {ℓa j o : ℕ} (hj : j < 2 ^ ℓa) (ho : o < 2 ^ ℓa) : BitRAM.len ((j : ℤ) + (o : ℤ)) ≤ ℓa + 1 := by
  have : ((j : ℤ) + (o : ℤ)) = ((j + o : ℕ) : ℤ) := by push_cast; ring
  rw [this]
  exact len_nat (by rw [pow_succ]; omega)

/-! ## The simulation -/

/-- The bit state `t` holds the registers, the real cells at the offset `X.off`, the offset in `TO`, the input in
the cells below the offset, the coins used, the rounds and the points played of the real state `s`. -/
structure XSim (X : XCtx d) (s : RealRAM.State d) (t : BitRAM.State d) : Prop where
  nreg : ∀ i, t.mem (rg i) = s.nreg i
  mem : ∀ j : ℕ, (t.mem ((j : ℤ) + X.off) : ℝ) = s.mem j
  off : t.mem TO = X.off
  inp : ∀ j : ℕ, j < X.off → t.mem j = X.inp j
  coins : t.coins = s.draws
  rounds : t.rounds = s.rounds
  pts : ∀ r, BitRAM.toE (t.pts r) = s.pts r

/-- The simulation survives a change of the scratch cells. -/
theorem XSim.scratch {X : XCtx d} {s : RealRAM.State d} {t t' : BitRAM.State d} (hs : XSim X s t)
    (hm : ∀ c, c ≠ T1 → c ≠ T2 → t'.mem c = t.mem c) (hc : t'.coins = t.coins) (hr : t'.rounds = t.rounds)
    (hp : t'.pts = t.pts) : XSim X s t' where
  nreg i := by rw [hm _ (rg_ne_T1 i) (rg_ne_T2 i)]; exact hs.nreg i
  mem j := by rw [hm _ (cl_ne_T1 _ _) (cl_ne_T2 _ _)]; exact hs.mem j
  off := by rw [hm _ TO_ne_T1 TO_ne_T2]; exact hs.off
  inp j hj := by rw [hm _ (by simp) (by simp)]; exact hs.inp j hj
  coins := by rw [hc]; exact hs.coins
  rounds := by rw [hr]; exact hs.rounds
  pts r := by rw [hp]; exact hs.pts r

/-- The simulation survives a change of the scratch cells, with the coins, rounds and points of the real state given. -/
theorem XSim.scratch' {X : XCtx d} {s s' : RealRAM.State d} {t t' : BitRAM.State d} (hs : XSim X s t)
    (hm : ∀ c, c ≠ T1 → c ≠ T2 → t'.mem c = t.mem c) (hn : s'.nreg = s.nreg) (hme : s'.mem = s.mem)
    (hc : t'.coins = s'.draws) (hr : t'.rounds = s'.rounds) (hp : ∀ r, BitRAM.toE (t'.pts r) = s'.pts r) :
    XSim X s' t' where
  nreg i := by rw [hm _ (rg_ne_T1 i) (rg_ne_T2 i), hn]; exact hs.nreg i
  mem j := by rw [hm _ (cl_ne_T1 _ _) (cl_ne_T2 _ _), hme]; exact hs.mem j
  off := by rw [hm _ TO_ne_T1 TO_ne_T2]; exact hs.off
  inp j hj := by rw [hm _ (by simp) (by simp)]; exact hs.inp j hj
  coins := hc
  rounds := hr
  pts := hp

/-- One real cell written (and the scratch cells), with the coins, rounds and points of the real state given. -/
theorem XSim.write' {X : XCtx d} {s s' : RealRAM.State d} {t t' : BitRAM.State d} (hs : XSim X s t) (j : ℕ)
    (z : ℤ) (v : ℝ) (hzv : (z : ℝ) = v) (hm : ∀ c, c ≠ T1 → c ≠ T2 → t'.mem c = update t.mem ((j : ℤ) + X.off) z c)
    (hn : s'.nreg = s.nreg) (hme : s'.mem = update s.mem j v) (hc : t'.coins = s'.draws)
    (hr : t'.rounds = s'.rounds) (hp : ∀ r, BitRAM.toE (t'.pts r) = s'.pts r) : XSim X s' t' where
  nreg i := by rw [hm _ (rg_ne_T1 i) (rg_ne_T2 i), update_of_ne (rg_ne_cl _ _ _), hn]; exact hs.nreg i
  mem k := by
    rw [hm _ (cl_ne_T1 _ _) (cl_ne_T2 _ _), hme]
    by_cases hk : k = j
    · subst hk; simp [hzv]
    · have : (k : ℤ) + X.off ≠ (j : ℤ) + X.off := by omega
      rw [update_of_ne this]; simp [update_of_ne hk, hs.mem k]
  off := by rw [hm _ TO_ne_T1 TO_ne_T2, update_of_ne (TO_ne_cl _ _)]; exact hs.off
  inp k hk := by rw [hm _ (by simp) (by simp), update_of_ne (nat_ne_cl hk)]; exact hs.inp k hk
  coins := hc
  rounds := hr
  pts := hp

/-- One real cell written (and the scratch cells). -/
theorem XSim.write {X : XCtx d} {s : RealRAM.State d} {t t' : BitRAM.State d} (hs : XSim X s t) (j : ℕ) (z : ℤ)
    (v : ℝ) (hzv : (z : ℝ) = v) (hm : ∀ c, c ≠ T1 → c ≠ T2 → t'.mem c = update t.mem ((j : ℤ) + X.off) z c)
    (hc : t'.coins = t.coins) (hr : t'.rounds = t.rounds) (hp : t'.pts = t.pts) :
    XSim X { s with mem := update s.mem j v } t' where
  nreg i := by rw [hm _ (rg_ne_T1 i) (rg_ne_T2 i), update_of_ne (rg_ne_cl _ _ _)]; exact hs.nreg i
  mem k := by
    rw [hm _ (cl_ne_T1 _ _) (cl_ne_T2 _ _)]
    by_cases hk : k = j
    · subst hk; simp [hzv]
    · have : (k : ℤ) + X.off ≠ (j : ℤ) + X.off := by omega
      rw [update_of_ne this]; simp [update_of_ne hk, hs.mem k]
  off := by rw [hm _ TO_ne_T1 TO_ne_T2, update_of_ne (TO_ne_cl _ _)]; exact hs.off
  inp k hk := by rw [hm _ (by simp) (by simp), update_of_ne (nat_ne_cl hk)]; exact hs.inp k hk
  coins := by rw [hc]; exact hs.coins
  rounds := by rw [hr]; exact hs.rounds
  pts r := by rw [hp]; exact hs.pts r

/-- One register written (and the scratch cells). -/
theorem XSim.writeReg {X : XCtx d} {s : RealRAM.State d} {t t' : BitRAM.State d} (hs : XSim X s t) (i v : ℕ)
    (hm : ∀ c, c ≠ T1 → c ≠ T2 → t'.mem c = update t.mem (rg i) (v : ℤ) c)
    (hc : t'.coins = t.coins) (hr : t'.rounds = t.rounds) (hp : t'.pts = t.pts) :
    XSim X { s with nreg := update s.nreg i v } t' where
  nreg k := by
    rw [hm _ (rg_ne_T1 k) (rg_ne_T2 k)]
    by_cases hk : k = i
    · subst hk; simp
    · rw [update_of_ne (by simpa using hk)]; simp [update_of_ne hk, hs.nreg k]
  mem k := by rw [hm _ (cl_ne_T1 _ _) (cl_ne_T2 _ _), update_of_ne (cl_ne_rg _ _ _)]; exact hs.mem k
  off := by rw [hm _ TO_ne_T1 TO_ne_T2, update_of_ne (TO_ne_rg _)]; exact hs.off
  inp k hk := by rw [hm _ (by simp) (by simp), update_of_ne (nat_ne_rg _ _)]; exact hs.inp k hk
  coins := by rw [hc]; exact hs.coins
  rounds := by rw [hr]; exact hs.rounds
  pts r := by rw [hp]; exact hs.pts r

/-! ## Blocks -/

/-- From `t`, `n` steps of `P` in the world `X.wb` reach a state at `q` simulating `s'`, at cost at most `C`. -/
def XBlock (X : XCtx d) (P : List BitRAM.Instr) (t : BitRAM.State d) (n q : ℕ) (s' : RealRAM.State d) (C : ℕ) :
    Prop :=
  ∃ t', BitRAM.run P X.wb t n = t' ∧ t'.pc = q ∧ XSim X s' t' ∧ t'.cost ≤ t.cost + C

/-- Within `N` steps. -/
def XBlockLE (X : XCtx d) (P : List BitRAM.Instr) (t : BitRAM.State d) (N q : ℕ) (s' : RealRAM.State d) (C : ℕ) :
    Prop :=
  ∃ n ≤ N, XBlock X P t n q s' C

section Blocks

variable {X : XCtx d} {P : List BitRAM.Instr}

theorem XBlock.le {t : BitRAM.State d} {n N q C : ℕ} {s : RealRAM.State d} (h : XBlock X P t n q s C) (hn : n ≤ N) :
    XBlockLE X P t N q s C := ⟨n, hn, h⟩

theorem XBlock.zero (t : BitRAM.State d) (s : RealRAM.State d) (hs : XSim X s t) : XBlock X P t 0 t.pc s 0 :=
  ⟨t, rfl, rfl, hs, by simp⟩

theorem XBlockLE.bind {t : BitRAM.State d} {N₁ N₂ q₁ q₂ C₁ C₂ : ℕ} {s₁ s₂ : RealRAM.State d}
    (h₁ : XBlockLE X P t N₁ q₁ s₁ C₁)
    (h₂ : ∀ t₁ : BitRAM.State d, t₁.pc = q₁ → XSim X s₁ t₁ → XBlockLE X P t₁ N₂ q₂ s₂ C₂) :
    XBlockLE X P t (N₁ + N₂) q₂ s₂ (C₁ + C₂) := by
  obtain ⟨n₁, hn₁, t₁, e₁, p₁, hs₁, c₁⟩ := h₁
  obtain ⟨n₂, hn₂, t₂, e₂, p₂, hs₂, c₂⟩ := h₂ t₁ p₁ hs₁
  exact ⟨n₁ + n₂, by omega, t₂, by rw [B.run_add, e₁, e₂], p₂, hs₂, by omega⟩

theorem XBlockLE.mono {t : BitRAM.State d} {N N' q q' C C' : ℕ} {s : RealRAM.State d}
    (h : XBlockLE X P t N q s C) (hN : N ≤ N') (hq : q = q') (hC : C ≤ C') : XBlockLE X P t N' q' s C' := by
  obtain ⟨n, hn, t', e, p, hs, c⟩ := h
  exact ⟨n, by omega, t', e, hq ▸ p, hs, by omega⟩

end Blocks

/-! ## The instructions that the fragment did not use -/

namespace B

open BitRAM

variable {P : List Instr} {w : World d} {t : State d} {q : ℕ}

theorem opI_spec' {o : RealRAM.Op2} {x a b : ℤ} (h : P[q]? = some (opI o x a b)) (hpc : t.pc = q) :
    ∃ t', step P w t = t' ∧ t'.pc = q + 1 ∧ t'.mem = update t.mem x (opZ o (t.mem a) (t.mem b)) ∧
      t'.cost = t.cost + (1 + len x + len a + len b + opC o (len (t.mem a)) (len (t.mem b))) ∧ Same t t' := by
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩ <;> cases o <;> simp [step, hpc ▸ h, opI, opZ, opC, Same] <;> omega

theorem coins_spec {dst cnt : ℤ} (h : P[q]? = some (.coins dst cnt)) (hpc : t.pc = q) :
    ∃ t', step P w t = t' ∧ t'.pc = q + 1 ∧
      t'.mem = update t.mem dst (readCoins w.cs t.coins (t.mem cnt).toNat) ∧
      t'.cost = t.cost + (1 + len dst + len cnt + len (t.mem cnt) + (t.mem cnt).toNat) ∧
      t'.coins = t.coins + (t.mem cnt).toNat ∧ t'.rounds = t.rounds ∧ t'.pts = t.pts := by
  subst hpc; exact ⟨_, rfl, by simp [step, h], by simp [step, h], by simp [step, h], by simp [step, h],
    by simp [step, h], by simp [step, h]⟩

theorem obs_spec {dst prec : ℤ} (h : P[q]? = some (.obs dst prec)) (hpc : t.pc = q) :
    ∃ t', step P w t = t' ∧ t'.pc = q + 1 ∧
      t'.mem = update t.mem dst (reading w t (t.mem prec).toNat) ∧
      t'.cost = t.cost + (1 + len dst + len prec + len (t.mem prec) + (t.mem prec).toNat +
        len (reading w t (t.mem prec).toNat)) ∧ Same t t' := by
  subst hpc; exact ⟨_, rfl, by simp [step, h], by simp [step, h], by simp [step, h], by simp [step, h, Same]⟩

theorem play_spec {src : ℤ} (h : P[q]? = some (.play src)) (hpc : t.pc = q) :
    ∃ t', step P w t = t' ∧ t'.pc = q + 1 ∧ t'.mem = t.mem ∧
      t'.cost = t.cost + (1 + len src + len (t.mem src) + playCost d t.mem (t.mem src)) ∧
      t'.coins = t.coins ∧ t'.rounds = t.rounds + 1 ∧
      t'.pts = update t.pts t.rounds (ptAt d t.mem (t.mem src)) := by
  subst hpc; exact ⟨_, rfl, by simp [step, h], by simp [step, h], by simp [step, h], by simp [step, h],
    by simp [step, h], by simp [step, h]⟩

end B

/-! ## The code -/

/-- The bit cost charged per unit of the extended language. -/
def xstepCost (ℓa ℓ : ℕ) : ℕ := 40 + 12 * ℓa + 4 * ℓ + (ℓa + ℓ + 1) ^ 2

/-- The code of a binary operation on two real cells into a third, through the offset. -/
def binCode (o : RealRAM.Op2) (dst a b : ℕ) : List BitRAM.Instr :=
  [.add T1 (rg a) TO, .load T1 T1, .add T2 (rg b) TO, .load T2 T2, opI o T1 T1 T2, .add T2 (rg dst) TO,
    .store T2 T1]

/-- The code of a fragment primitive (empty outside the fragment). -/
def xtrFrag : Prim → List BitRAM.Instr
  | .rconst dst q => [.const T1 q.num, .add T2 (rg dst) TO, .store T2 T1]
  | .op2 o dst a b => binCode o dst a b
  | .nconst dst c => [.const (rg dst) c]
  | .nadd dst a b => [.add (rg dst) (rg a) (rg b)]
  | .nsub dst a b => [.sub (rg dst) (rg a) (rg b)]
  | .ncast dst a => [.add T2 (rg dst) TO, .store T2 (rg a)]
  | _ => []

/-- The code of a leaf. -/
def xtrLeaf : Leaf → List BitRAM.Instr
  | .idiv dst a b => binCode .div dst a b
  | .coins dst cnt => [.coins T1 (rg cnt), .add T2 (rg dst) TO, .store T2 T1]
  | .obs dst prec => [.obs T1 (rg prec), .add T2 (rg dst) TO, .store T2 T1]
  | .play src => [.add T1 (rg src) TO, .play T1]
  | .rtoN dst a => [.add T1 (rg a) TO, .load (rg dst) T1]
  | .nmul dst a b => [.mul (rg dst) (rg a) (rg b)]
  | .rdIn dst e => [.load T1 (rg e), .add T2 (rg dst) TO, .store T2 T1]

/-- The code of a primitive. -/
def xtrPrim : XPrim → List BitRAM.Instr
  | .frag p => xtrFrag p
  | .leaf l => xtrLeaf l

/-- The code of the test `M (N a) < M (N b)`, jumping to `tg`. -/
def testRCode (a b tg : ℕ) : List BitRAM.Instr :=
  [.add T1 (rg a) TO, .load T1 T1, .add T2 (rg b) TO, .load T2 T2, .jlt T1 T2 tg]

/-- The length of the code of a command. -/
def xtlen : XCmd → ℕ
  | .skip => 0
  | .prim p => (xtrPrim p).length
  | .seq c₁ c₂ => xtlen c₁ + xtlen c₂
  | .ifR _ _ c₁ c₂ => xtlen c₁ + xtlen c₂ + 6
  | .ifN _ _ c₁ c₂ => xtlen c₁ + xtlen c₂ + 2
  | .whileR _ _ c => xtlen c + 7
  | .whileN _ _ c => xtlen c + 3

/-- The code of a command placed at address `o` (absolute jumps). -/
def xtr : XCmd → ℕ → List BitRAM.Instr
  | .skip, _ => []
  | .prim p, _ => xtrPrim p
  | .seq c₁ c₂, o => xtr c₁ o ++ xtr c₂ (o + xtlen c₁)
  | .ifR a b c₁ c₂, o =>
    testRCode a b (o + xtlen c₂ + 6) ++ (xtr c₂ (o + 5) ++ .jmp (o + xtlen c₂ + 6 + xtlen c₁) ::
      xtr c₁ (o + xtlen c₂ + 6))
  | .ifN a b c₁ c₂, o =>
    .jlt (rg a) (rg b) (o + xtlen c₂ + 2) ::
      (xtr c₂ (o + 1) ++ .jmp (o + xtlen c₂ + 2 + xtlen c₁) :: xtr c₁ (o + xtlen c₂ + 2))
  | .whileR a b c, o => testRCode a b (o + 6) ++ (.jmp (o + xtlen c + 7) :: (xtr c (o + 6) ++ [.jmp o]))
  | .whileN a b c, o => .jlt (rg a) (rg b) (o + 2) :: .jmp (o + xtlen c + 3) :: (xtr c (o + 2) ++ [.jmp o])

@[simp] theorem length_xtr (c : XCmd) (o : ℕ) : (xtr c o).length = xtlen c := by
  induction c generalizing o <;> simp [xtr, xtlen, testRCode, *] <;> omega

/-! ## The primitives -/

section Prims

variable {X : XCtx d} {P : List BitRAM.Instr} {ℓa ℓ : ℕ}

theorem len_le_of_cast {ℓ : ℕ} {z : ℤ} {x : ℝ} (hz : (z : ℝ) = x) (h : |x| < 2 ^ ℓ) : BitRAM.len z ≤ ℓ :=
  len_val hz h

/-- The block of a binary operation `M (N dst) := v`, `v` the value of the instruction on the two operands. -/
theorem xsim_bin {s : RealRAM.State d} {t : BitRAM.State d} {o : ℕ} {op : RealRAM.Op2} {dst a b : ℕ} {v : ℝ}
    (hP : B.CodeAt P o (binCode op dst a b)) (hpc : t.pc = o) (hs : XSim X s t) (hoff : X.off < 2 ^ ℓa)
    (hd : RegOK ℓa s dst) (ha : RegOK ℓa s a) (hb : RegOK ℓa s b)
    (hx : |s.mem (s.nreg a)| < 2 ^ ℓ) (hy : |s.mem (s.nreg b)| < 2 ^ ℓ)
    (hv : ∀ x y : ℤ, (x : ℝ) = s.mem (s.nreg a) → (y : ℝ) = s.mem (s.nreg b) → ((opZ op x y : ℤ) : ℝ) = v)
    (hz : |v| < 2 ^ ℓ) :
    XBlock X P t 7 (o + 7) { s with mem := update s.mem (s.nreg dst) v } (xstepCost ℓa ℓ) := by
  obtain ⟨hd1, hd2⟩ := hd
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  simp only [binCode] at hP
  have ea := hs.nreg a
  have eb := hs.nreg b
  have ed := hs.nreg dst
  have eo := hs.off
  set xa := t.mem ((s.nreg a : ℤ) + X.off) with hxa
  set xb := t.mem ((s.nreg b : ℤ) + X.off) with hxb
  have hxa' : (xa : ℝ) = s.mem (s.nreg a) := hs.mem _
  have hxb' : (xb : ℝ) = s.mem (s.nreg b) := hs.mem _
  obtain ⟨t1, e1, p1, m1, c1, s1⟩ := B.add_spec (w := X.wb) hP.cons_head hpc
  obtain ⟨t2, e2, p2, m2, c2, s2⟩ := B.load_spec (w := X.wb) hP.cons_tail.cons_head p1
  obtain ⟨t3, e3, p3, m3, c3, s3⟩ := B.add_spec (w := X.wb) hP.cons_tail.cons_tail.cons_head p2
  obtain ⟨t4, e4, p4, m4, c4, s4⟩ := B.load_spec (w := X.wb) hP.cons_tail.cons_tail.cons_tail.cons_head p3
  obtain ⟨t5, e5, p5, m5, c5, s5⟩ :=
    B.opI_spec' (w := X.wb) hP.cons_tail.cons_tail.cons_tail.cons_tail.cons_head p4
  obtain ⟨t6, e6, p6, m6, c6, s6⟩ :=
    B.add_spec (w := X.wb) hP.cons_tail.cons_tail.cons_tail.cons_tail.cons_tail.cons_head p5
  obtain ⟨t7, e7, p7, m7, c7, s7⟩ :=
    B.store_spec (w := X.wb) hP.cons_tail.cons_tail.cons_tail.cons_tail.cons_tail.cons_tail.cons_head p6
  have v1 : t1.mem T1 = (s.nreg a : ℤ) + X.off := by rw [m1]; simp [ea, eo]
  have v2 : t2.mem T1 = xa := by rw [m2, v1, m1]; simp [hxa]
  have v3 : t3.mem T2 = (s.nreg b : ℤ) + X.off := by rw [m3]; simp [m2, m1, eb, eo]
  have v4 : t4.mem T2 = xb := by rw [m4, v3, m3]; simp [m2, m1, hxb]
  have v4' : t4.mem T1 = xa := by rw [m4, m3]; simp [v2]
  have v5 : t5.mem T1 = opZ op xa xb := by rw [m5, v4, v4']; simp
  have v6 : t6.mem T2 = (s.nreg dst : ℤ) + X.off := by rw [m6]; simp [m5, m4, m3, m2, m1, ed, eo]
  have v6' : t6.mem T1 = opZ op xa xb := by rw [m6]; simp [v5]
  have f5 : ∀ c, c ≠ T1 → c ≠ T2 → t6.mem c = t.mem c := fun c h1 h2 => by
    rw [m6, m5, m4, m3, m2, m1]; simp [h1, h2]
  refine ⟨t7, ?_, by rw [p7], ?_, ?_⟩
  · simp only [show (7 : ℕ) = 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl, B.run_add, B.run_one, e1, e2, e3, e4, e5, e6, e7]
  · refine hs.write (s.nreg dst) (opZ op xa xb) v (hv xa xb hxa' hxb') (fun c h1 h2 => ?_) ?_ ?_ ?_
    · rw [m7, v6, v6']
      by_cases hc : c = (s.nreg dst : ℤ) + X.off
      · subst hc; simp
      · rw [update_of_ne hc, update_of_ne hc, f5 c h1 h2]
    · exact (s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans s7)))))).1
    · exact (s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans s7)))))).2.1
    · exact (s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans s7)))))).2.2
  · have l1 : BitRAM.len ((s.nreg a : ℤ) + X.off) ≤ ℓa + 1 := len_cl ha2 hoff
    have l2 : BitRAM.len ((s.nreg b : ℤ) + X.off) ≤ ℓa + 1 := len_cl hb2 hoff
    have l3 : BitRAM.len ((s.nreg dst : ℤ) + X.off) ≤ ℓa + 1 := len_cl hd2 hoff
    have lxa : BitRAM.len xa ≤ ℓ := len_le_of_cast hxa' hx
    have lxb : BitRAM.len xb ≤ ℓ := len_le_of_cast hxb' hy
    have lz : BitRAM.len (opZ op xa xb) ≤ ℓ := len_le_of_cast (hv xa xb hxa' hxb') hz
    have lo : BitRAM.len (X.off : ℤ) ≤ ℓa := len_nat hoff
    have lra := len_rg ha1
    have lrb := len_rg hb1
    have lrd := len_rg hd1
    have lna := len_nat ha2
    have lnb := len_nat hb2
    have lnd := len_nat hd2
    have hc := opC_le op (BitRAM.len xa) (BitRAM.len xb)
    have hq : (BitRAM.len xa + 1) * (BitRAM.len xb + 1) ≤ (ℓa + ℓ + 1) ^ 2 := by
      rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
    rw [c7, c6, c5, c4, c3, c2, c1]
    have w1 : t1.mem (rg b) = s.nreg b := by rw [m1]; simp [eb]
    have w2 : t2.mem (rg b) = s.nreg b := by rw [m2]; simp [w1]
    have w3 : t3.mem TO = X.off := by rw [m3]; simp [m2, m1, eo]
    have w5 : t5.mem (rg dst) = s.nreg dst := by rw [m5]; simp [m4, m3, m2, m1, ed]
    have w5' : t5.mem TO = X.off := by rw [m5]; simp [m4, w3]
    have w3' : t3.mem ((s.nreg b : ℤ) + X.off) = xb := by rw [m3]; simp [m2, m1, hxb]
    have w1' : t1.mem ((s.nreg a : ℤ) + X.off) = xa := by rw [m1]; simp [hxa]
    have w2o : t2.mem TO = X.off := by rw [m2]; simp [m1, eo]
    rw [ea, eo, v1, w1', w2, w2o, v3, w3', v4', v4, w5, w5', v6, v6']
    simp only [len_T1, len_T2, len_TO]
    unfold xstepCost
    omega

theorem xsim_op2 {s : RealRAM.State d} {t : BitRAM.State d} {o : ℕ} {op : RealRAM.Op2} {dst a b : ℕ}
    (hP : B.CodeAt P o (xtrFrag (.op2 op dst a b))) (hpc : t.pc = o) (hs : XSim X s t) (hoff : X.off < 2 ^ ℓa)
    (hok : PrimOK ℓa ℓ s (.op2 op dst a b)) :
    XBlock X P t 7 (o + 7) ((Prim.op2 op dst a b).exec X.rw s) (xstepCost ℓa ℓ) := by
  obtain ⟨hdiv, hd, ha, hb, hx, hy, hz⟩ := hok
  exact xsim_bin hP hpc hs hoff hd ha hb hx hy (fun x y hx' hy' => by rw [opZ_cast op hdiv, hx', hy']) hz

theorem abs_ediv_cast_lt {x y : ℤ} {ℓ : ℕ} (h : |(x : ℝ)| < 2 ^ ℓ) : |((x / y : ℤ) : ℝ)| < 2 ^ ℓ := by
  have h1 : (x / y).natAbs ≤ x.natAbs := Int.natAbs_ediv_le_natAbs x y
  have h2 : |((x / y : ℤ) : ℝ)| ≤ |(x : ℝ)| := by
    rw [← Int.cast_abs, ← Int.cast_abs, Int.abs_eq_natAbs, Int.abs_eq_natAbs]
    exact_mod_cast h1
  linarith

theorem xsim_idiv {s : RealRAM.State d} {t : BitRAM.State d} {o : ℕ} {dst a b : ℕ}
    (hP : B.CodeAt P o (xtrLeaf (.idiv dst a b))) (hpc : t.pc = o) (hs : XSim X s t) (hoff : X.off < 2 ^ ℓa)
    (hok : LeafOK X ℓa ℓ s (.idiv dst a b)) :
    XBlock X P t 7 (o + 7) ((Leaf.idiv dst a b).exec X s) (xstepCost ℓa ℓ) := by
  obtain ⟨hd, ha, hb, hx, hy⟩ := hok
  have hxa := hs.mem (s.nreg a)
  have hxb := hs.mem (s.nreg b)
  refine xsim_bin hP hpc hs hoff hd ha hb hx hy (fun x y hx' hy' => ?_) ?_
  · rw [← hx', ← hy', Int.floor_intCast, Int.floor_intCast]; rfl
  · rw [← hxa, ← hxb, Int.floor_intCast, Int.floor_intCast]
    exact abs_ediv_cast_lt (by rw [hxa]; exact hx)

theorem xsim_rconst {s : RealRAM.State d} {t : BitRAM.State d} {o : ℕ} {dst : ℕ} {qv : ℚ}
    (hP : B.CodeAt P o (xtrFrag (.rconst dst qv))) (hpc : t.pc = o) (hs : XSim X s t) (hoff : X.off < 2 ^ ℓa)
    (hok : PrimOK ℓa ℓ s (.rconst dst qv)) :
    XBlock X P t 3 (o + 3) ((Prim.rconst dst qv).exec X.rw s) (xstepCost ℓa ℓ) := by
  obtain ⟨⟨hd1, hd2⟩, hden, hq⟩ := hok
  simp only [xtrFrag] at hP
  have ed := hs.nreg dst
  have eo := hs.off
  have hqz : ((qv.num : ℤ) : ℝ) = (qv : ℝ) := by
    rw [← Rat.cast_intCast, Rat.coe_int_num_of_den_eq_one hden]
  obtain ⟨t1, e1, p1, m1, c1, s1⟩ := B.const_spec (w := X.wb) hP.cons_head hpc
  obtain ⟨t2, e2, p2, m2, c2, s2⟩ := B.add_spec (w := X.wb) hP.cons_tail.cons_head p1
  obtain ⟨t3, e3, p3, m3, c3, s3⟩ := B.store_spec (w := X.wb) hP.cons_tail.cons_tail.cons_head p2
  have v2 : t2.mem T2 = (s.nreg dst : ℤ) + X.off := by rw [m2]; simp [m1, ed, eo]
  have v2' : t2.mem T1 = qv.num := by rw [m2]; simp [m1]
  refine ⟨t3, ?_, by rw [p3], ?_, ?_⟩
  · simp only [show (3 : ℕ) = 1 + 1 + 1 from rfl, B.run_add, B.run_one, e1, e2, e3]
  · refine hs.write (s.nreg dst) qv.num qv hqz (fun c h1 h2 => ?_) (s1.trans (s2.trans s3)).1
      (s1.trans (s2.trans s3)).2.1 (s1.trans (s2.trans s3)).2.2
    rw [m3, v2, v2']
    by_cases hc : c = (s.nreg dst : ℤ) + X.off
    · subst hc; simp
    · rw [update_of_ne hc, update_of_ne hc, m2, m1]; simp [h1, h2]
  · have l3 : BitRAM.len ((s.nreg dst : ℤ) + X.off) ≤ ℓa + 1 := len_cl hd2 hoff
    have lq : BitRAM.len qv.num ≤ ℓ := len_le_of_cast hqz hq
    have lo : BitRAM.len (X.off : ℤ) ≤ ℓa := len_nat hoff
    have lrd := len_rg hd1
    have lnd := len_nat hd2
    have w1 : t1.mem (rg dst) = s.nreg dst := by rw [m1]; simp [ed]
    have w1o : t1.mem TO = X.off := by rw [m1]; simp [eo]
    rw [c3, c2, c1, w1, w1o, v2, v2']
    simp only [len_T1, len_T2, len_TO]
    unfold xstepCost
    have := Nat.zero_le ((ℓa + ℓ + 1) ^ 2); omega

theorem xsim_ncast {s : RealRAM.State d} {t : BitRAM.State d} {o : ℕ} {dst a : ℕ}
    (hP : B.CodeAt P o (xtrFrag (.ncast dst a))) (hpc : t.pc = o) (hs : XSim X s t) (hoff : X.off < 2 ^ ℓa)
    (hok : PrimOK ℓa ℓ s (.ncast dst a)) :
    XBlock X P t 2 (o + 2) ((Prim.ncast dst a).exec X.rw s) (xstepCost ℓa ℓ) := by
  obtain ⟨⟨hd1, hd2⟩, ⟨ha1, ha2⟩⟩ := hok
  simp only [xtrFrag] at hP
  have ed := hs.nreg dst
  have ea := hs.nreg a
  have eo := hs.off
  obtain ⟨t1, e1, p1, m1, c1, s1⟩ := B.add_spec (w := X.wb) hP.cons_head hpc
  obtain ⟨t2, e2, p2, m2, c2, s2⟩ := B.store_spec (w := X.wb) hP.cons_tail.cons_head p1
  have v1 : t1.mem T2 = (s.nreg dst : ℤ) + X.off := by rw [m1]; simp [ed, eo]
  have v1' : t1.mem (rg a) = s.nreg a := by rw [m1]; simp [ea]
  refine ⟨t2, ?_, by rw [p2], ?_, ?_⟩
  · simp only [show (2 : ℕ) = 1 + 1 from rfl, B.run_add, B.run_one, e1, e2]
  · refine hs.write (s.nreg dst) (s.nreg a) (s.nreg a : ℝ) (by simp) (fun c h1 h2 => ?_) (s1.trans s2).1
      (s1.trans s2).2.1 (s1.trans s2).2.2
    rw [m2, v1, v1']
    by_cases hc : c = (s.nreg dst : ℤ) + X.off
    · subst hc; simp
    · rw [update_of_ne hc, update_of_ne hc, m1]; simp [h2]
  · have l3 : BitRAM.len ((s.nreg dst : ℤ) + X.off) ≤ ℓa + 1 := len_cl hd2 hoff
    have lo : BitRAM.len (X.off : ℤ) ≤ ℓa := len_nat hoff
    have lrd := len_rg hd1
    have lra := len_rg ha1
    have lnd := len_nat hd2
    have lna := len_nat ha2
    rw [c2, c1, v1, v1', ed, eo]
    simp only [len_T2, len_TO]
    unfold xstepCost
    have := Nat.zero_le ((ℓa + ℓ + 1) ^ 2); omega

theorem xsim_nconst {s : RealRAM.State d} {t : BitRAM.State d} {o : ℕ} {dst c : ℕ}
    (hP : B.CodeAt P o (xtrFrag (.nconst dst c))) (hpc : t.pc = o) (hs : XSim X s t)
    (hok : PrimOK ℓa ℓ s (.nconst dst c)) :
    XBlock X P t 1 (o + 1) ((Prim.nconst dst c).exec X.rw s) (xstepCost ℓa ℓ) := by
  obtain ⟨hd1, hc⟩ := hok
  simp only [xtrFrag] at hP
  obtain ⟨t1, e1, p1, m1, c1, s1⟩ := B.const_spec (w := X.wb) hP.cons_head hpc
  refine ⟨t1, by rw [B.run_one, e1], p1, hs.writeReg dst c (fun x _ _ => by rw [m1]) s1.1 s1.2.1 s1.2.2, ?_⟩
  rw [c1]
  have := len_rg hd1
  have := len_nat hc
  unfold xstepCost
  have := Nat.zero_le ((ℓa + ℓ + 1) ^ 2); omega

theorem xsim_nadd {s : RealRAM.State d} {t : BitRAM.State d} {o : ℕ} {dst a b : ℕ}
    (hP : B.CodeAt P o (xtrFrag (.nadd dst a b))) (hpc : t.pc = o) (hs : XSim X s t)
    (hok : PrimOK ℓa ℓ s (.nadd dst a b)) :
    XBlock X P t 1 (o + 1) ((Prim.nadd dst a b).exec X.rw s) (xstepCost ℓa ℓ) := by
  obtain ⟨hd1, ⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩ := hok
  simp only [xtrFrag] at hP
  obtain ⟨t1, e1, p1, m1, c1, s1⟩ := B.add_spec (w := X.wb) hP.cons_head hpc
  refine ⟨t1, by rw [B.run_one, e1], p1,
    hs.writeReg dst (s.nreg a + s.nreg b) (fun x _ _ => by rw [m1, hs.nreg a, hs.nreg b]; push_cast; rfl) s1.1
      s1.2.1 s1.2.2, ?_⟩
  rw [c1, hs.nreg a, hs.nreg b]
  have := len_rg hd1
  have := len_rg ha1
  have := len_rg hb1
  have := len_nat ha2
  have := len_nat hb2
  unfold xstepCost
  have := Nat.zero_le ((ℓa + ℓ + 1) ^ 2); omega

theorem xsim_nsub {s : RealRAM.State d} {t : BitRAM.State d} {o : ℕ} {dst a b : ℕ}
    (hP : B.CodeAt P o (xtrFrag (.nsub dst a b))) (hpc : t.pc = o) (hs : XSim X s t)
    (hok : PrimOK ℓa ℓ s (.nsub dst a b)) :
    XBlock X P t 1 (o + 1) ((Prim.nsub dst a b).exec X.rw s) (xstepCost ℓa ℓ) := by
  obtain ⟨hd1, ⟨ha1, ha2⟩, ⟨hb1, hb2⟩, hba⟩ := hok
  simp only [xtrFrag] at hP
  obtain ⟨t1, e1, p1, m1, c1, s1⟩ := B.sub_spec (w := X.wb) hP.cons_head hpc
  refine ⟨t1, by rw [B.run_one, e1], p1,
    hs.writeReg dst (s.nreg a - s.nreg b)
      (fun x _ _ => by rw [m1, hs.nreg a, hs.nreg b, Nat.cast_sub hba]) s1.1 s1.2.1 s1.2.2, ?_⟩
  rw [c1, hs.nreg a, hs.nreg b]
  have := len_rg hd1
  have := len_rg ha1
  have := len_rg hb1
  have := len_nat ha2
  have := len_nat hb2
  unfold xstepCost
  have := Nat.zero_le ((ℓa + ℓ + 1) ^ 2); omega

theorem xsim_nmul {s : RealRAM.State d} {t : BitRAM.State d} {o : ℕ} {dst a b : ℕ}
    (hP : B.CodeAt P o (xtrLeaf (.nmul dst a b))) (hpc : t.pc = o) (hs : XSim X s t)
    (hok : LeafOK X ℓa ℓ s (.nmul dst a b)) :
    XBlock X P t 1 (o + 1) ((Leaf.nmul dst a b).exec X s) (xstepCost ℓa ℓ) := by
  obtain ⟨hd1, ⟨ha1, ha2⟩, ⟨hb1, hb2⟩, -⟩ := hok
  simp only [xtrLeaf] at hP
  obtain ⟨t1, e1, p1, m1, c1, s1⟩ :=
    B.opI_spec' (w := X.wb) (o := .mul) (x := rg dst) (a := rg a) (b := rg b) hP.cons_head hpc
  refine ⟨t1, by rw [B.run_one, e1], p1,
    hs.writeReg dst (s.nreg a * s.nreg b) (fun x _ _ => by rw [m1, hs.nreg a, hs.nreg b]; push_cast; rfl) s1.1
      s1.2.1 s1.2.2, ?_⟩
  rw [c1, hs.nreg a, hs.nreg b]
  have := len_rg hd1
  have := len_rg ha1
  have := len_rg hb1
  have la := len_nat ha2
  have lb := len_nat hb2
  have hq : (BitRAM.len (s.nreg a : ℤ) + 1) * (BitRAM.len (s.nreg b : ℤ) + 1) ≤ (ℓa + ℓ + 1) ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  simp only [opC]
  unfold xstepCost
  omega

theorem readCoins_bounds (cs : ℕ → Bool) (c k : ℕ) :
    0 ≤ BitRAM.readCoins cs c k ∧ BitRAM.readCoins cs c k < 2 ^ k := by
  induction k with
  | zero => simp [BitRAM.readCoins]
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    simp only [BitRAM.readCoins, pow_succ]
    split_ifs <;> constructor <;> omega

theorem feedback_eq {s : RealRAM.State d} {t : BitRAM.State d} (hs : XSim X s t) :
    BitRAM.feedback X.wb t = fbR X s := by
  unfold BitRAM.feedback fbR
  rw [hs.rounds]
  split
  · rfl
  · rw [hs.pts]

theorem xsim_coins {s : RealRAM.State d} {t : BitRAM.State d} {o : ℕ} {dst cnt : ℕ}
    (hP : B.CodeAt P o (xtrLeaf (.coins dst cnt))) (hpc : t.pc = o) (hs : XSim X s t) (hoff : X.off < 2 ^ ℓa)
    (hok : LeafOK X ℓa ℓ s (.coins dst cnt)) :
    XBlock X P t 3 (o + 3) ((Leaf.coins dst cnt).exec X s) (xstepCost ℓa ℓ) := by
  obtain ⟨⟨hd1, hd2⟩, ⟨hc1, hc2⟩, hk⟩ := hok
  simp only [xtrLeaf] at hP
  have ed := hs.nreg dst
  have ec := hs.nreg cnt
  have eo := hs.off
  obtain ⟨t1, e1, p1, m1, c1, k1, r1, q1⟩ := B.coins_spec (w := X.wb) hP.cons_head hpc
  obtain ⟨t2, e2, p2, m2, c2, s2⟩ := B.add_spec (w := X.wb) hP.cons_tail.cons_head p1
  obtain ⟨t3, e3, p3, m3, c3, s3⟩ := B.store_spec (w := X.wb) hP.cons_tail.cons_tail.cons_head p2
  have hcnt : (t.mem (rg cnt)).toNat = s.nreg cnt := by rw [ec]; simp
  set r := BitRAM.readCoins X.wb.cs s.draws (s.nreg cnt) with hr
  have v1 : t1.mem T1 = r := by rw [m1, hcnt, hs.coins]; simp [hr]
  have v2 : t2.mem T2 = (s.nreg dst : ℤ) + X.off := by rw [m2]; simp [m1, ed, eo]
  have v2' : t2.mem T1 = r := by rw [m2]; simp [v1]
  have hS := s2.trans s3
  refine ⟨t3, ?_, by rw [p3], ?_, ?_⟩
  · simp only [show (3 : ℕ) = 1 + 1 + 1 from rfl, B.run_add, B.run_one, e1, e2, e3]
  · refine hs.write' (j := s.nreg dst) (z := r) (v := (r : ℝ)) rfl (fun c h1 h2 => ?_) rfl rfl ?_ ?_ ?_
    · rw [m3, v2, v2']
      by_cases hc : c = (s.nreg dst : ℤ) + X.off
      · subst hc; simp
      · rw [update_of_ne hc, update_of_ne hc, m2, m1]; simp [h1, h2]
    · rw [hS.1, k1, hcnt, hs.coins]; rfl
    · rw [hS.2.1, r1]; exact hs.rounds
    · rw [hS.2.2, q1]; exact hs.pts
  · have l3 : BitRAM.len ((s.nreg dst : ℤ) + X.off) ≤ ℓa + 1 := len_cl hd2 hoff
    have lo : BitRAM.len (X.off : ℤ) ≤ ℓa := len_nat hoff
    have lrd := len_rg hd1
    have lrc := len_rg hc1
    have lnd := len_nat hd2
    have lnc := len_nat hc2
    have lr : BitRAM.len r ≤ s.nreg cnt := by
      obtain ⟨h0, h1⟩ := readCoins_bounds X.wb.cs s.draws (s.nreg cnt)
      unfold BitRAM.len; rw [Nat.size_le]
      have h2 : ((r.natAbs : ℕ) : ℤ) < ((2 ^ s.nreg cnt : ℕ) : ℤ) := by
        rw [Int.natCast_natAbs, abs_of_nonneg h0]; push_cast; exact h1
      exact_mod_cast h2
    have w1 : t1.mem (rg dst) = s.nreg dst := by rw [m1]; simp [ed]
    have w1o : t1.mem TO = X.off := by rw [m1]; simp [eo]
    rw [c3, c2, c1, w1, w1o, v2, v2', hcnt, ec]
    simp only [len_T1, len_T2, len_TO]
    unfold xstepCost
    have := Nat.zero_le ((ℓa + ℓ + 1) ^ 2); omega

theorem xsim_obs {s : RealRAM.State d} {t : BitRAM.State d} {o : ℕ} {dst prec : ℕ}
    (hP : B.CodeAt P o (xtrLeaf (.obs dst prec))) (hpc : t.pc = o) (hs : XSim X s t) (hoff : X.off < 2 ^ ℓa)
    (hok : LeafOK X ℓa ℓ s (.obs dst prec)) :
    XBlock X P t 3 (o + 3) ((Leaf.obs dst prec).exec X s) (xstepCost ℓa ℓ) := by
  obtain ⟨⟨hd1, hd2⟩, ⟨hp1, hp2⟩, hk, hz⟩ := hok
  simp only [xtrLeaf] at hP
  have ed := hs.nreg dst
  have ep := hs.nreg prec
  have eo := hs.off
  obtain ⟨t1, e1, p1, m1, c1, s1⟩ := B.obs_spec (w := X.wb) hP.cons_head hpc
  obtain ⟨t2, e2, p2, m2, c2, s2⟩ := B.add_spec (w := X.wb) hP.cons_tail.cons_head p1
  obtain ⟨t3, e3, p3, m3, c3, s3⟩ := B.store_spec (w := X.wb) hP.cons_tail.cons_tail.cons_head p2
  have hp : (t.mem (rg prec)).toNat = s.nreg prec := by rw [ep]; simp
  set r := ⌊(2 : ℝ) ^ (s.nreg prec) * fbR X s⌋ with hr
  have hrd : BitRAM.reading X.wb t (t.mem (rg prec)).toNat = r := by
    rw [hp, hr, BitRAM.reading, feedback_eq hs]
  have v1 : t1.mem T1 = r := by rw [m1, hrd]; simp
  have v2 : t2.mem T2 = (s.nreg dst : ℤ) + X.off := by rw [m2]; simp [m1, ed, eo]
  have v2' : t2.mem T1 = r := by rw [m2]; simp [v1]
  have hS := s1.trans (s2.trans s3)
  refine ⟨t3, ?_, by rw [p3], ?_, ?_⟩
  · simp only [show (3 : ℕ) = 1 + 1 + 1 from rfl, B.run_add, B.run_one, e1, e2, e3]
  · refine hs.write (s.nreg dst) r (r : ℝ) rfl (fun c h1 h2 => ?_) hS.1 hS.2.1 hS.2.2
    rw [m3, v2, v2']
    by_cases hc : c = (s.nreg dst : ℤ) + X.off
    · subst hc; simp
    · rw [update_of_ne hc, update_of_ne hc, m2, m1]; simp [h1, h2]
  · have l3 : BitRAM.len ((s.nreg dst : ℤ) + X.off) ≤ ℓa + 1 := len_cl hd2 hoff
    have lo : BitRAM.len (X.off : ℤ) ≤ ℓa := len_nat hoff
    have lrd := len_rg hd1
    have lrp := len_rg hp1
    have lnd := len_nat hd2
    have lnp := len_nat hp2
    have lr : BitRAM.len r ≤ ℓ := len_le_of_cast rfl hz
    have w1 : t1.mem (rg dst) = s.nreg dst := by rw [m1]; simp [ed]
    have w1o : t1.mem TO = X.off := by rw [m1]; simp [eo]
    rw [c3, c2, c1, w1, w1o, v2, v2', hrd, hp, ep]
    simp only [len_T1, len_T2, len_TO]
    unfold xstepCost
    have := Nat.zero_le ((ℓa + ℓ + 1) ^ 2); omega

theorem xsim_rdIn {s : RealRAM.State d} {t : BitRAM.State d} {o : ℕ} {dst e : ℕ}
    (hP : B.CodeAt P o (xtrLeaf (.rdIn dst e))) (hpc : t.pc = o) (hs : XSim X s t) (hoff : X.off < 2 ^ ℓa)
    (hok : LeafOK X ℓa ℓ s (.rdIn dst e)) :
    XBlock X P t 3 (o + 3) ((Leaf.rdIn dst e).exec X s) (xstepCost ℓa ℓ) := by
  obtain ⟨⟨hd1, hd2⟩, ⟨he1, he2⟩, hin, hz⟩ := hok
  simp only [xtrLeaf] at hP
  have ed := hs.nreg dst
  have ee := hs.nreg e
  have eo := hs.off
  obtain ⟨t1, e1, p1, m1, c1, s1⟩ := B.load_spec (w := X.wb) hP.cons_head hpc
  obtain ⟨t2, e2, p2, m2, c2, s2⟩ := B.add_spec (w := X.wb) hP.cons_tail.cons_head p1
  obtain ⟨t3, e3, p3, m3, c3, s3⟩ := B.store_spec (w := X.wb) hP.cons_tail.cons_tail.cons_head p2
  have hi : t.mem (t.mem (rg e)) = X.inp (s.nreg e) := by rw [ee]; exact hs.inp _ hin
  have v1 : t1.mem T1 = X.inp (s.nreg e) := by rw [m1, hi]; simp
  have v2 : t2.mem T2 = (s.nreg dst : ℤ) + X.off := by rw [m2]; simp [m1, ed, eo]
  have v2' : t2.mem T1 = X.inp (s.nreg e) := by rw [m2]; simp [v1]
  have hS := s1.trans (s2.trans s3)
  refine ⟨t3, ?_, by rw [p3], ?_, ?_⟩
  · simp only [show (3 : ℕ) = 1 + 1 + 1 from rfl, B.run_add, B.run_one, e1, e2, e3]
  · refine hs.write (s.nreg dst) (X.inp (s.nreg e)) _ rfl (fun c h1 h2 => ?_) hS.1 hS.2.1 hS.2.2
    rw [m3, v2, v2']
    by_cases hc : c = (s.nreg dst : ℤ) + X.off
    · subst hc; simp
    · rw [update_of_ne hc, update_of_ne hc, m2, m1]; simp [h1, h2]
  · have l3 : BitRAM.len ((s.nreg dst : ℤ) + X.off) ≤ ℓa + 1 := len_cl hd2 hoff
    have lo : BitRAM.len (X.off : ℤ) ≤ ℓa := len_nat hoff
    have lrd := len_rg hd1
    have lre := len_rg he1
    have lnd := len_nat hd2
    have lne := len_nat he2
    have lr : BitRAM.len (X.inp (s.nreg e)) ≤ ℓ := len_le_of_cast rfl hz
    have w1 : t1.mem (rg dst) = s.nreg dst := by rw [m1]; simp [ed]
    have w1o : t1.mem TO = X.off := by rw [m1]; simp [eo]
    rw [c3, c2, c1, w1, w1o, v2, v2', hi, ee]
    simp only [len_T1, len_T2, len_TO]
    unfold xstepCost
    have := Nat.zero_le ((ℓa + ℓ + 1) ^ 2); omega

theorem xsim_rtoN {s : RealRAM.State d} {t : BitRAM.State d} {o : ℕ} {dst a : ℕ}
    (hP : B.CodeAt P o (xtrLeaf (.rtoN dst a))) (hpc : t.pc = o) (hs : XSim X s t) (hoff : X.off < 2 ^ ℓa)
    (hok : LeafOK X ℓa ℓ s (.rtoN dst a)) :
    XBlock X P t 2 (o + 2) ((Leaf.rtoN dst a).exec X s) (xstepCost ℓa ℓ) := by
  obtain ⟨hd1, ⟨ha1, ha2⟩, h0, hlt, hz⟩ := hok
  simp only [xtrLeaf] at hP
  have ea := hs.nreg a
  have eo := hs.off
  set z := t.mem ((s.nreg a : ℤ) + X.off) with hzd
  have hz' : (z : ℝ) = s.mem (s.nreg a) := hs.mem _
  have hz0 : 0 ≤ z := by exact_mod_cast hz' ▸ h0
  have hfl : (⌊s.mem (s.nreg a)⌋).toNat = z.toNat := by rw [← hz', Int.floor_intCast]
  obtain ⟨t1, e1, p1, m1, c1, s1⟩ := B.add_spec (w := X.wb) hP.cons_head hpc
  obtain ⟨t2, e2, p2, m2, c2, s2⟩ := B.load_spec (w := X.wb) hP.cons_tail.cons_head p1
  have v1 : t1.mem T1 = (s.nreg a : ℤ) + X.off := by rw [m1]; simp [ea, eo]
  have v1' : t1.mem ((s.nreg a : ℤ) + X.off) = z := by rw [m1]; simp [hzd]
  have hS := s1.trans s2
  refine ⟨t2, ?_, by rw [p2], ?_, ?_⟩
  · simp only [show (2 : ℕ) = 1 + 1 from rfl, B.run_add, B.run_one, e1, e2]
  · show XSim X { s with nreg := update s.nreg dst (⌊s.mem (s.nreg a)⌋).toNat } t2
    rw [hfl]
    refine hs.writeReg dst z.toNat (fun c h1 h2 => ?_) hS.1 hS.2.1 hS.2.2
    rw [m2, v1, v1', Int.toNat_of_nonneg hz0]
    by_cases hc : c = rg dst
    · subst hc; simp
    · rw [update_of_ne hc, update_of_ne hc, m1]; simp [h1]
  · have l1 : BitRAM.len ((s.nreg a : ℤ) + X.off) ≤ ℓa + 1 := len_cl ha2 hoff
    have lo : BitRAM.len (X.off : ℤ) ≤ ℓa := len_nat hoff
    have lrd := len_rg hd1
    have lra := len_rg ha1
    have lna := len_nat ha2
    have lz : BitRAM.len z ≤ ℓ := len_le_of_cast hz' hz
    rw [c2, c1, v1, v1', ea, eo]
    simp only [len_T1, len_TO]
    unfold xstepCost
    have := Nat.zero_le ((ℓa + ℓ + 1) ^ 2); omega
theorem xsim_play {s : RealRAM.State d} {t : BitRAM.State d} {o : ℕ} {src : ℕ}
    (hP : B.CodeAt P o (xtrLeaf (.play src))) (hpc : t.pc = o) (hs : XSim X s t) (hoff : X.off < 2 ^ ℓa)
    (hok : LeafOK X ℓa ℓ s (.play src)) :
    XBlock X P t 2 (o + 2) ((Leaf.play src).exec X s) ((d + 2) * xstepCost ℓa ℓ) := by
  obtain ⟨⟨hs1, hs2⟩, hsd, hv⟩ := hok
  simp only [xtrLeaf] at hP
  have es := hs.nreg src
  have eo := hs.off
  obtain ⟨t1, e1, p1, m1, c1, s1⟩ := B.add_spec (w := X.wb) hP.cons_head hpc
  obtain ⟨t2, e2, p2, m2, c2, k2, r2, q2⟩ := B.play_spec (w := X.wb) hP.cons_tail.cons_head p1
  have v1 : t1.mem T1 = (s.nreg src : ℤ) + X.off := by rw [m1]; simp [es, eo]
  have f1 : ∀ c, c ≠ T1 → t1.mem c = t.mem c := fun c hc => by rw [m1, update_of_ne hc]
  have hcell : ∀ i : ℕ, t1.mem ((s.nreg src : ℤ) + X.off + i) = t.mem (((s.nreg src + i : ℕ) : ℤ) + X.off) :=
    fun i => by rw [f1 _ (by unfold T1; omega)]; congr 1; push_cast; ring
  have hpt : BitRAM.toE (BitRAM.ptAt d t1.mem (t1.mem T1)) = ptR d s.mem (s.nreg src) := by
    rw [v1]
    unfold BitRAM.toE BitRAM.ptAt ptR
    congr 1
    funext i
    have h1 : t1.mem ((s.nreg src : ℤ) + X.off + 1 + (i : ℕ)) =
        t.mem (((s.nreg src + 1 + (i : ℕ) : ℕ) : ℤ) + X.off) := by
      rw [f1 _ (by unfold T1; omega)]; congr 1; push_cast; ring
    have h0 : t1.mem ((s.nreg src : ℤ) + X.off) = t.mem (((s.nreg src : ℕ) : ℤ) + X.off) := by
      rw [f1 _ (by unfold T1; omega)]
    rw [h1, h0, Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast, hs.mem, hs.mem]
  refine ⟨t2, ?_, by rw [p2], ?_, ?_⟩
  · simp only [show (2 : ℕ) = 1 + 1 from rfl, B.run_add, B.run_one, e1, e2]
  · refine hs.scratch' (fun c h1 _ => by rw [m2, f1 c h1]) rfl rfl ?_ ?_ ?_
    · rw [k2, s1.1]; exact hs.coins
    · rw [r2, s1.2.1, hs.rounds]; rfl
    · intro r
      rw [q2, s1.2.1, hs.rounds]
      show _ = update s.pts s.rounds (ptR d s.mem (s.nreg src)) r
      by_cases hr : r = s.rounds
      · subst hr; rw [update_self, update_self, hpt]
      · rw [update_of_ne hr, update_of_ne hr, s1.2.2]; exact hs.pts r
  · have lo : BitRAM.len (X.off : ℤ) ≤ ℓa := len_nat hoff
    have lrs := len_rg hs1
    have lns := len_nat hs2
    have l1 : BitRAM.len ((s.nreg src : ℤ) + X.off) ≤ ℓa + 1 := len_cl hs2 hoff
    have hpc' : BitRAM.playCost d t1.mem ((s.nreg src : ℤ) + X.off) ≤ (d + 1) * (1 + (ℓa + 1) + ℓ) := by
      unfold BitRAM.playCost
      refine (Finset.sum_le_card_nsmul _ _ (1 + (ℓa + 1) + ℓ) fun i hi => ?_).trans (by simp)
      rw [Finset.mem_range] at hi
      have hi' : s.nreg src + i < 2 ^ ℓa := by omega
      have la : BitRAM.len ((s.nreg src : ℤ) + X.off + i) ≤ ℓa + 1 := by
        have : (s.nreg src : ℤ) + X.off + i = ((s.nreg src + i : ℕ) : ℤ) + X.off := by push_cast; ring
        rw [this]; exact len_cl hi' hoff
      have lv : BitRAM.len (t1.mem ((s.nreg src : ℤ) + X.off + i)) ≤ ℓ := by
        rw [hcell i]
        exact len_le_of_cast (hs.mem _) (hv i (by omega))
      omega
    rw [c2, c1, v1, es, eo]
    simp only [len_T1, len_TO]
    have hX : 1 + (ℓa + 1) + ℓ ≤ xstepCost ℓa ℓ := by
      unfold xstepCost; have := Nat.zero_le ((ℓa + ℓ + 1) ^ 2); omega
    have hX2 : 7 + 4 * ℓa ≤ xstepCost ℓa ℓ := by
      unfold xstepCost; have := Nat.zero_le ((ℓa + ℓ + 1) ^ 2); omega
    have h1 := Nat.mul_le_mul_left (d + 1) hX
    have h2 : (d + 2) * xstepCost ℓa ℓ = (d + 1) * xstepCost ℓa ℓ + xstepCost ℓa ℓ := by ring
    rw [h2]
    omega

/-! ## Tests and jumps -/

/-- The cost of the test `M (N a) < M (N b)` through the offset. -/
def xtestRCost (ℓa ℓ : ℕ) : ℕ := 23 + 8 * ℓa + 4 * ℓ

theorem xsim_testR {s : RealRAM.State d} {t : BitRAM.State d} {o a b tg : ℕ}
    (hP : B.CodeAt P o (testRCode a b tg)) (hpc : t.pc = o) (hs : XSim X s t) (hoff : X.off < 2 ^ ℓa)
    (hok : TestR ℓa ℓ s a b) :
    XBlock X P t 5 (if condR s a b then tg else o + 5) s (xtestRCost ℓa ℓ) := by
  obtain ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩, hx, hy⟩ := hok
  simp only [testRCode] at hP
  have ea := hs.nreg a
  have eb := hs.nreg b
  have eo := hs.off
  set xa := t.mem ((s.nreg a : ℤ) + X.off) with hxa
  set xb := t.mem ((s.nreg b : ℤ) + X.off) with hxb
  have hxa' : (xa : ℝ) = s.mem (s.nreg a) := hs.mem _
  have hxb' : (xb : ℝ) = s.mem (s.nreg b) := hs.mem _
  obtain ⟨t1, e1, p1, m1, c1, s1⟩ := B.add_spec (w := X.wb) hP.cons_head hpc
  obtain ⟨t2, e2, p2, m2, c2, s2⟩ := B.load_spec (w := X.wb) hP.cons_tail.cons_head p1
  obtain ⟨t3, e3, p3, m3, c3, s3⟩ := B.add_spec (w := X.wb) hP.cons_tail.cons_tail.cons_head p2
  obtain ⟨t4, e4, p4, m4, c4, s4⟩ := B.load_spec (w := X.wb) hP.cons_tail.cons_tail.cons_tail.cons_head p3
  obtain ⟨t5, e5, p5, m5, c5, s5⟩ :=
    B.jlt_spec (w := X.wb) hP.cons_tail.cons_tail.cons_tail.cons_tail.cons_head p4
  have v1 : t1.mem T1 = (s.nreg a : ℤ) + X.off := by rw [m1]; simp [ea, eo]
  have w1' : t1.mem ((s.nreg a : ℤ) + X.off) = xa := by rw [m1]; simp [hxa]
  have v2 : t2.mem T1 = xa := by rw [m2, v1, w1']; simp
  have w2 : t2.mem (rg b) = s.nreg b := by rw [m2]; simp [m1, eb]
  have w2o : t2.mem TO = X.off := by rw [m2]; simp [m1, eo]
  have v3 : t3.mem T2 = (s.nreg b : ℤ) + X.off := by rw [m3, w2, w2o]; simp
  have w3' : t3.mem ((s.nreg b : ℤ) + X.off) = xb := by rw [m3]; simp [m2, m1, hxb]
  have v4 : t4.mem T2 = xb := by rw [m4, v3, w3']; simp
  have v4' : t4.mem T1 = xa := by rw [m4, m3]; simp [v2]
  have hS := s1.trans (s2.trans (s3.trans (s4.trans s5)))
  refine ⟨t5, ?_, ?_, ?_, ?_⟩
  · simp only [show (5 : ℕ) = 1 + 1 + 1 + 1 + 1 from rfl, B.run_add, B.run_one, e1, e2, e3, e4, e5]
  · rw [p5, v4, v4']
    by_cases hc : condR s a b
    · have : xa < xb := by
        have : (xa : ℝ) < xb := by rw [hxa', hxb']; exact hc
        exact_mod_cast this
      simp [hc, this]
    · have : ¬ xa < xb := fun h => hc (by
        show s.mem (s.nreg a) < s.mem (s.nreg b)
        rw [← hxa', ← hxb']; exact_mod_cast h)
      simp [hc, this]
  · refine hs.scratch (fun c h1 h2 => ?_) hS.1 hS.2.1 hS.2.2
    rw [m5, m4, m3, m2, m1]; simp [h1, h2]
  · have l1 : BitRAM.len ((s.nreg a : ℤ) + X.off) ≤ ℓa + 1 := len_cl ha2 hoff
    have l2 : BitRAM.len ((s.nreg b : ℤ) + X.off) ≤ ℓa + 1 := len_cl hb2 hoff
    have lxa : BitRAM.len xa ≤ ℓ := len_le_of_cast hxa' hx
    have lxb : BitRAM.len xb ≤ ℓ := len_le_of_cast hxb' hy
    have lo : BitRAM.len (X.off : ℤ) ≤ ℓa := len_nat hoff
    have lra := len_rg ha1
    have lrb := len_rg hb1
    have lna := len_nat ha2
    have lnb := len_nat hb2
    rw [c5, c4, c3, c2, c1, ea, eo, v1, w1', w2, w2o, v3, w3', v4, v4']
    simp only [len_T1, len_T2, len_TO]
    unfold xtestRCost
    omega

theorem xsim_testN {s : RealRAM.State d} {t : BitRAM.State d} {o a b tg : ℕ}
    (h0 : P[o]? = some (.jlt (rg a) (rg b) tg)) (hpc : t.pc = o) (hs : XSim X s t) (hok : TestN ℓa s a b) :
    XBlock X P t 1 (if condN s a b then tg else o + 1) s (testNCost ℓa) := by
  obtain ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩ := hok
  obtain ⟨t1, e1, p1, m1, c1, s1⟩ := B.jlt_spec (w := X.wb) h0 hpc
  refine ⟨t1, by rw [B.run_one, e1], ?_, hs.scratch (fun c _ _ => by rw [m1]) s1.1 s1.2.1 s1.2.2, ?_⟩
  · rw [p1, hs.nreg a, hs.nreg b]; simp [condN]
  · rw [c1, hs.nreg a, hs.nreg b]
    have := len_rg ha1
    have := len_rg hb1
    have := len_nat ha2
    have := len_nat hb2
    unfold testNCost
    omega

theorem xsim_jmp {s : RealRAM.State d} {t : BitRAM.State d} {o tg : ℕ} (h0 : P[o]? = some (.jmp tg))
    (hpc : t.pc = o) (hs : XSim X s t) : XBlock X P t 1 tg s 1 := by
  obtain ⟨t1, e1, p1, m1, c1, s1⟩ := B.jmp_spec (w := X.wb) h0 hpc
  exact ⟨t1, by rw [B.run_one, e1], p1, hs.scratch (fun c _ _ => by rw [m1]) s1.1 s1.2.1 s1.2.2, by rw [c1]⟩
/-! ## Dispatch -/

theorem xsim_frag {p : Prim} {s : RealRAM.State d} {t : BitRAM.State d} {o : ℕ}
    (hP : B.CodeAt P o (xtrFrag p)) (hpc : t.pc = o) (hs : XSim X s t) (hoff : X.off < 2 ^ ℓa)
    (hok : PrimOK ℓa ℓ s p) :
    (xtrFrag p).length ≤ 7 ∧
      XBlock X P t (xtrFrag p).length (o + (xtrFrag p).length) (p.exec X.rw s) (xstepCost ℓa ℓ) := by
  cases p with
  | rconst dst q => exact ⟨by simp [xtrFrag], xsim_rconst hP hpc hs hoff hok⟩
  | op2 op dst a b => exact ⟨by simp [xtrFrag, binCode], xsim_op2 hP hpc hs hoff hok⟩
  | nconst dst c => exact ⟨by simp [xtrFrag], xsim_nconst hP hpc hs hok⟩
  | nadd dst a b => exact ⟨by simp [xtrFrag], xsim_nadd hP hpc hs hok⟩
  | nsub dst a b => exact ⟨by simp [xtrFrag], xsim_nsub hP hpc hs hok⟩
  | ncast dst a => exact ⟨by simp [xtrFrag], xsim_ncast hP hpc hs hoff hok⟩
  | op1 => exact hok.elim
  | spec => exact hok.elim
  | query => exact hok.elim
  | gauss => exact hok.elim
  | play => exact hok.elim

theorem xsim_leaf {l : Leaf} {s : RealRAM.State d} {t : BitRAM.State d} {o : ℕ}
    (hP : B.CodeAt P o (xtrLeaf l)) (hpc : t.pc = o) (hs : XSim X s t) (hoff : X.off < 2 ^ ℓa)
    (hok : LeafOK X ℓa ℓ s l) :
    (xtrLeaf l).length ≤ 7 * leafUnits d l ∧
      XBlock X P t (xtrLeaf l).length (o + (xtrLeaf l).length) (l.exec X s) (leafUnits d l * xstepCost ℓa ℓ) := by
  cases l with
  | idiv dst a b =>
    exact ⟨by simp [xtrLeaf, binCode, leafUnits], by
      rw [show leafUnits d (.idiv dst a b) = 1 from rfl, one_mul]; exact xsim_idiv hP hpc hs hoff hok⟩
  | coins dst cnt =>
    exact ⟨by simp [xtrLeaf, leafUnits], by
      rw [show leafUnits d (.coins dst cnt) = 1 from rfl, one_mul]; exact xsim_coins hP hpc hs hoff hok⟩
  | obs dst prec =>
    exact ⟨by simp [xtrLeaf, leafUnits], by
      rw [show leafUnits d (.obs dst prec) = 1 from rfl, one_mul]; exact xsim_obs hP hpc hs hoff hok⟩
  | play src => exact ⟨by simp [xtrLeaf, leafUnits]; omega, xsim_play hP hpc hs hoff hok⟩
  | rtoN dst a =>
    exact ⟨by simp [xtrLeaf, leafUnits], by
      rw [show leafUnits d (.rtoN dst a) = 1 from rfl, one_mul]; exact xsim_rtoN hP hpc hs hoff hok⟩
  | nmul dst a b =>
    exact ⟨by simp [xtrLeaf, leafUnits], by
      rw [show leafUnits d (.nmul dst a b) = 1 from rfl, one_mul]; exact xsim_nmul hP hpc hs hok⟩
  | rdIn dst e =>
    exact ⟨by simp [xtrLeaf, leafUnits], by
      rw [show leafUnits d (.rdIn dst e) = 1 from rfl, one_mul]; exact xsim_rdIn hP hpc hs hoff hok⟩

theorem xtestR_le (ℓa ℓ : ℕ) : xtestRCost ℓa ℓ + 1 ≤ xstepCost ℓa ℓ := by
  unfold xtestRCost xstepCost; have := Nat.zero_le ((ℓa + ℓ + 1) ^ 2); omega

theorem xtestN_le (ℓa ℓ : ℕ) : testNCost ℓa + 1 ≤ xstepCost ℓa ℓ := by
  unfold testNCost xstepCost; have := Nat.zero_le ((ℓa + ℓ + 1) ^ 2); omega

end Prims

/-! ## The transfer theorem -/

/-- The transfer with leaves: a bounded run of the extended language on the real state is a run of the compiled code on
the bit machine, in the world of the context, within `7 k` steps and at cost at most `k * xstepCost ℓa ℓ`. -/
theorem xtransfer {X : XCtx d} {P : List BitRAM.Instr} {ℓa ℓ : ℕ} (hoff : X.off < 2 ^ ℓa) {c : XCmd}
    {s s' : RealRAM.State d} {k : ℕ} (h : XExecB X ℓa ℓ c s k s') :
    ∀ (o : ℕ) (t : BitRAM.State d), B.CodeAt P o (xtr c o) → t.pc = o → XSim X s t →
      XBlockLE X P t (7 * k) (o + xtlen c) s' (k * xstepCost ℓa ℓ) := by
  induction h with
  | skip s =>
    intro o t _ hpc hs
    exact ((XBlock.zero t s hs).le (Nat.zero_le _)).mono le_rfl (by simp [hpc, xtlen]) (Nat.zero_le _)
  | frag p s hok =>
    intro o t hP hpc hs
    obtain ⟨hl, hb⟩ := xsim_frag hP hpc hs hoff hok
    exact (hb.le (by omega)).mono le_rfl (by simp [xtlen, xtrPrim]) (by simp)
  | leaf l s hok =>
    intro o t hP hpc hs
    obtain ⟨hl, hb⟩ := xsim_leaf hP hpc hs hoff hok
    exact (hb.le hl).mono le_rfl (by simp [xtlen, xtrPrim]) le_rfl
  | @seq c₁ c₂ s s₁ s₂ k₁ k₂ _ _ ih₁ ih₂ =>
    intro o t hP hpc hs
    simp only [xtr] at hP
    refine ((ih₁ o t hP.append_left hpc hs).bind
      (fun t₁ p₁ hs₁ => ih₂ (o + xtlen c₁) t₁ (by simpa using hP.append_right) p₁ hs₁)).mono
      (by omega) (by simp [xtlen]; omega) (by rw [add_mul])
  | @ifR_t a b c₁ c₂ s s' k hok hc _ ih =>
    intro o t hP hpc hs
    simp only [xtr] at hP
    have hT := xsim_testR hP.append_left hpc hs hoff hok
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at hT
    have hc₁ : B.CodeAt P (o + xtlen c₂ + 6) (xtr c₁ (o + xtlen c₂ + 6)) :=
      hP.append_right.append_right.cons_tail.cast (by simp [testRCode]; omega)
    refine ((hT.le le_rfl).bind (fun t₁ p₁ hs₁ => ih _ t₁ hc₁ p₁ hs₁)).mono (by omega) (by simp [xtlen]; omega) ?_
    have := xtestR_le ℓa ℓ
    nlinarith
  | @ifR_f a b c₁ c₂ s s' k hok hc _ ih =>
    intro o t hP hpc hs
    simp only [xtr] at hP
    have hT := xsim_testR hP.append_left hpc hs hoff hok
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at hT
    have hc₂ : B.CodeAt P (o + 5) (xtr c₂ (o + 5)) := hP.append_right.append_left.cast (by simp [testRCode])
    have hj := hP.append_right.append_right.head_at (o' := o + 5 + xtlen c₂) (by simp [testRCode])
    refine (((hT.le le_rfl).bind (fun t₁ p₁ hs₁ => ih _ t₁ hc₂ p₁ hs₁)).bind
      (fun t₂ p₂ hs₂ => (xsim_jmp hj p₂ hs₂).le le_rfl)).mono (by omega) (by simp [xtlen]; omega) ?_
    have := xtestR_le ℓa ℓ
    nlinarith
  | @ifN_t a b c₁ c₂ s s' k hok hc _ ih =>
    intro o t hP hpc hs
    simp only [xtr] at hP
    have hT := xsim_testN (X := X) hP.cons_head hpc hs hok
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at hT
    have hc₁ : B.CodeAt P (o + xtlen c₂ + 2) (xtr c₁ (o + xtlen c₂ + 2)) :=
      hP.cons_tail.append_right.cons_tail.cast (by simp; omega)
    refine ((hT.le le_rfl).bind (fun t₁ p₁ hs₁ => ih _ t₁ hc₁ p₁ hs₁)).mono (by omega) (by simp [xtlen]; omega) ?_
    have := xtestN_le ℓa ℓ
    nlinarith
  | @ifN_f a b c₁ c₂ s s' k hok hc _ ih =>
    intro o t hP hpc hs
    simp only [xtr] at hP
    have hT := xsim_testN (X := X) hP.cons_head hpc hs hok
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at hT
    have hc₂ : B.CodeAt P (o + 1) (xtr c₂ (o + 1)) := hP.cons_tail.append_left
    have hj := hP.cons_tail.append_right.head_at (o' := o + 1 + xtlen c₂) (by simp)
    refine (((hT.le le_rfl).bind (fun t₁ p₁ hs₁ => ih _ t₁ hc₂ p₁ hs₁)).bind
      (fun t₂ p₂ hs₂ => (xsim_jmp hj p₂ hs₂).le le_rfl)).mono (by omega) (by simp [xtlen]; omega) ?_
    have := xtestN_le ℓa ℓ
    nlinarith
  | @whileR_t a b c s s₁ s₂ k k' hok hc _ _ ih₁ ih₂ =>
    intro o t hP hpc hs
    have hP0 := hP
    simp only [xtr] at hP
    have hT := xsim_testR hP.append_left hpc hs hoff hok
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at hT
    have hcb : B.CodeAt P (o + 6) (xtr c (o + 6)) :=
      hP.append_right.cons_tail.append_left.cast (by simp [testRCode])
    have hj := hP.append_right.cons_tail.append_right.head_at (o' := o + 6 + xtlen c) (by simp [testRCode])
    refine ((((hT.le le_rfl).bind (fun t₁ p₁ hs₁ => ih₁ _ t₁ hcb p₁ hs₁)).bind
      (fun t₂ p₂ hs₂ => (xsim_jmp hj p₂ hs₂).le le_rfl)).bind
      (fun t₃ p₃ hs₃ => ih₂ o t₃ hP0 p₃ hs₃)).mono (by omega) rfl ?_
    have := xtestR_le ℓa ℓ
    nlinarith
  | @whileR_f a b c s hok hc =>
    intro o t hP hpc hs
    simp only [xtr] at hP
    have hT := xsim_testR hP.append_left hpc hs hoff hok
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at hT
    have hj := hP.append_right.head_at (o' := o + 5) (by simp [testRCode])
    refine ((hT.le le_rfl).bind (fun t₁ p₁ hs₁ => (xsim_jmp hj p₁ hs₁).le le_rfl)).mono (by omega)
      (by simp [xtlen]; omega) ?_
    have := xtestR_le ℓa ℓ
    nlinarith
  | @whileN_t a b c s s₁ s₂ k k' hok hc _ _ ih₁ ih₂ =>
    intro o t hP hpc hs
    have hP0 := hP
    simp only [xtr] at hP
    have hT := xsim_testN (X := X) hP.cons_head hpc hs hok
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at hT
    have hcb : B.CodeAt P (o + 2) (xtr c (o + 2)) := hP.cons_tail.cons_tail.append_left.cast (by omega)
    have hj := hP.cons_tail.cons_tail.append_right.head_at (o' := o + 2 + xtlen c) (by simp)
    refine ((((hT.le le_rfl).bind (fun t₁ p₁ hs₁ => ih₁ _ t₁ hcb p₁ hs₁)).bind
      (fun t₂ p₂ hs₂ => (xsim_jmp hj p₂ hs₂).le le_rfl)).bind
      (fun t₃ p₃ hs₃ => ih₂ o t₃ hP0 p₃ hs₃)).mono (by omega) rfl ?_
    have := xtestN_le ℓa ℓ
    nlinarith
  | @whileN_f a b c s hok hc =>
    intro o t hP hpc hs
    simp only [xtr] at hP
    have hT := xsim_testN (X := X) hP.cons_head hpc hs hok
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at hT
    have hj := hP.cons_tail.head_at (o' := o + 1) rfl
    refine ((hT.le le_rfl).bind (fun t₁ p₁ hs₁ => (xsim_jmp hj p₁ hs₁).le le_rfl)).mono (by omega)
      (by simp [xtlen]; omega) ?_
    have := xtestN_le ℓa ℓ
    nlinarith

end AdversarialBco.Bit.Transfer
