/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTrans
public import AdversarialBco.Bit.Transfer.XArith

@[expose] public section

/-!
# The compiler, part 4: space

* `Clean ℓa ℓ s`: the real state uses only the registers `i` with `i + 4 < 2 ^ ℓa` and the cells below `2 ^ ℓa`, its
  registers are below `2 ^ (ℓa + 1)` and its cells at most `2 ^ ℓ + 2 ^ ℓa` in absolute value. The zero state is
  clean (`clean_zero`) and every bounded run keeps it clean (`XExecB.clean`): each primitive and leaf writes at an
  address below `2 ^ ℓa` (its bounds `PrimOK`, `LeafOK`) a value within these bounds. No routine has to zero
  anything: the bounds of the run are the invariant.
* `space_checkpoint`: a bit state that simulates a clean real state, with its two scratch cells at `0`, has space at
  most `(off + 2 ^ (ℓa + 1)) (2 ℓa + ℓ + ℓi + 3)`, `ℓi` a bound on the bit length of the input cells.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco
open AdversarialBco.Poly.Mach (Prim)
open Function

variable {d : ℕ}

/-- The real state touches only the registers `i` with `i + 4 < 2 ^ ℓa` and the cells below `2 ^ ℓa`, with
registers below `2 ^ (ℓa + 1)` and cells at most `2 ^ ℓ + 2 ^ ℓa` in absolute value. -/
structure Clean (ℓa ℓ : ℕ) (s : RealRAM.State d) : Prop where
  reg0 : ∀ i, 2 ^ ℓa ≤ i + 4 → s.nreg i = 0
  regv : ∀ i, s.nreg i < 2 ^ (ℓa + 1)
  mem0 : ∀ j, 2 ^ ℓa ≤ j → s.mem j = 0
  memv : ∀ j, |s.mem j| ≤ 2 ^ ℓ + 2 ^ ℓa

namespace Clean

variable {ℓa ℓ : ℕ} {s : RealRAM.State d}

theorem of_eq {s' : RealRAM.State d} (h : Clean ℓa ℓ s) (hn : s'.nreg = s.nreg) (hm : s'.mem = s.mem) :
    Clean ℓa ℓ s' where
  reg0 i hi := by rw [hn]; exact h.reg0 i hi
  regv i := by rw [hn]; exact h.regv i
  mem0 j hj := by rw [hm]; exact h.mem0 j hj
  memv j := by rw [hm]; exact h.memv j

theorem setMem (h : Clean ℓa ℓ s) {j : ℕ} (hj : j < 2 ^ ℓa) {v : ℝ} (hv : |v| ≤ 2 ^ ℓ + 2 ^ ℓa) :
    Clean ℓa ℓ { s with mem := update s.mem j v } where
  reg0 := h.reg0
  regv := h.regv
  mem0 k hk := by
    have : k ≠ j := by omega
    simp only [update_of_ne this]; exact h.mem0 k hk
  memv k := by
    by_cases hk : k = j
    · subst hk; simpa using hv
    · simp only [update_of_ne hk]; exact h.memv k

theorem setReg (h : Clean ℓa ℓ s) {i : ℕ} (hi : i + 4 < 2 ^ ℓa) {v : ℕ} (hv : v < 2 ^ (ℓa + 1)) :
    Clean ℓa ℓ { s with nreg := update s.nreg i v } where
  reg0 k hk := by
    have : k ≠ i := by omega
    simp only [update_of_ne this]; exact h.reg0 k hk
  regv k := by
    by_cases hk : k = i
    · subst hk; simpa using hv
    · simp only [update_of_ne hk]; exact h.regv k
  mem0 := h.mem0
  memv := h.memv

end Clean

theorem pow_le_pow_add (ℓa ℓ : ℕ) : (2 : ℝ) ^ ℓ ≤ 2 ^ ℓ + 2 ^ ℓa := le_add_of_nonneg_right (by positivity)

theorem pow_le_pow_add' (ℓa ℓ : ℕ) : (2 : ℝ) ^ ℓa ≤ 2 ^ ℓ + 2 ^ ℓa := le_add_of_nonneg_left (by positivity)

theorem abs_floor_le {x : ℝ} {ℓ : ℕ} (h : |x| < 2 ^ ℓ) : |((⌊x⌋ : ℤ) : ℝ)| ≤ 2 ^ ℓ := by
  rw [abs_lt] at h
  have h1 : (-(2 ^ ℓ : ℤ) : ℤ) ≤ ⌊x⌋ := Int.le_floor.2 (by push_cast; linarith)
  have h2 : ((-(2 ^ ℓ : ℤ) : ℤ) : ℝ) ≤ (⌊x⌋ : ℝ) := by exact_mod_cast h1
  push_cast at h2
  rw [abs_le]
  exact ⟨h2, (Int.floor_le x).trans h.2.le⟩

theorem abs_ediv_floor_le {x y : ℝ} {ℓ : ℕ} (h : |x| < 2 ^ ℓ) : |((⌊x⌋ / ⌊y⌋ : ℤ) : ℝ)| ≤ 2 ^ ℓ := by
  have h1 : (⌊x⌋ / ⌊y⌋).natAbs ≤ (⌊x⌋).natAbs := Int.natAbs_ediv_le_natAbs _ _
  have h2 : |((⌊x⌋ / ⌊y⌋ : ℤ) : ℝ)| ≤ |((⌊x⌋ : ℤ) : ℝ)| := by
    rw [← Int.cast_abs, ← Int.cast_abs, Int.abs_eq_natAbs, Int.abs_eq_natAbs]
    exact_mod_cast h1
  exact h2.trans (abs_floor_le h)

theorem clean_prim {w : RealRAM.World d} {ℓa ℓ : ℕ} {s : RealRAM.State d} {p : Prim} (h : Clean ℓa ℓ s)
    (hp : PrimOK ℓa ℓ s p) : Clean ℓa ℓ (p.exec w s) := by
  cases p with
  | rconst dst q =>
    obtain ⟨⟨-, hd⟩, -, hq⟩ := hp
    exact h.setMem hd (hq.le.trans (pow_le_pow_add ℓa ℓ))
  | op2 o dst a b =>
    obtain ⟨-, ⟨-, hd⟩, -, -, -, -, hv⟩ := hp
    exact h.setMem hd (hv.le.trans (pow_le_pow_add ℓa ℓ))
  | nconst dst c =>
    obtain ⟨hd, hc⟩ := hp
    exact h.setReg hd (hc.trans (Nat.pow_lt_pow_right (by norm_num) (by omega)))
  | nadd dst a b =>
    obtain ⟨hd, ⟨-, ha⟩, ⟨-, hb⟩⟩ := hp
    exact h.setReg hd (by rw [pow_succ]; omega)
  | nsub dst a b =>
    obtain ⟨hd, ⟨-, ha⟩, -, -⟩ := hp
    exact h.setReg hd (by rw [pow_succ]; omega)
  | ncast dst a =>
    obtain ⟨⟨-, hd⟩, ⟨-, ha⟩⟩ := hp
    refine h.setMem hd ?_
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact le_trans (by exact_mod_cast ha.le) (pow_le_pow_add' ℓa ℓ)
  | op1 => exact hp.elim
  | spec => exact hp.elim
  | query => exact hp.elim
  | gauss => exact hp.elim
  | play => exact hp.elim

theorem clean_leaf {X : XCtx d} {ℓa ℓ : ℕ} {s : RealRAM.State d} {l : Leaf} (h : Clean ℓa ℓ s)
    (hl : LeafOK X ℓa ℓ s l) : Clean ℓa ℓ (l.exec X s) := by
  cases l with
  | idiv dst a b =>
    obtain ⟨⟨-, hd⟩, -, -, ha, -⟩ := hl
    exact h.setMem hd ((abs_ediv_floor_le ha).trans (pow_le_pow_add ℓa ℓ))
  | coins dst cnt =>
    obtain ⟨⟨-, hd⟩, -, hk⟩ := hl
    obtain ⟨h0, h1⟩ := readCoins_bounds X.wb.cs s.draws (s.nreg cnt)
    have h2 : (BitRAM.readCoins X.wb.cs s.draws (s.nreg cnt) : ℝ) < 2 ^ ℓ := by
      have h3 : BitRAM.readCoins X.wb.cs s.draws (s.nreg cnt) < 2 ^ ℓ :=
        h1.trans_le (pow_le_pow_right₀ (by norm_num) hk)
      exact_mod_cast h3
    have h4 : (0 : ℝ) ≤ (BitRAM.readCoins X.wb.cs s.draws (s.nreg cnt) : ℝ) := by exact_mod_cast h0
    exact (h.setMem hd (v := (BitRAM.readCoins X.wb.cs s.draws (s.nreg cnt) : ℝ))
      (by rw [abs_of_nonneg h4]; exact h2.le.trans (pow_le_pow_add ℓa ℓ))).of_eq rfl rfl
  | obs dst prec =>
    obtain ⟨⟨-, hd⟩, -, -, hz⟩ := hl
    exact h.setMem hd (hz.le.trans (pow_le_pow_add ℓa ℓ))
  | play src => exact h.of_eq rfl rfl
  | rtoN dst a =>
    obtain ⟨hd, -, h0, hlt, -⟩ := hl
    refine h.setReg hd ?_
    have h1 : (⌊s.mem (s.nreg a)⌋).toNat < 2 ^ ℓa := by
      have h2 : ⌊s.mem (s.nreg a)⌋ < 2 ^ ℓa := Int.floor_lt.2 (by push_cast; exact hlt)
      have h3 : 0 ≤ ⌊s.mem (s.nreg a)⌋ := Int.floor_nonneg.2 h0
      have h4 : ((⌊s.mem (s.nreg a)⌋).toNat : ℤ) < ((2 ^ ℓa : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg h3]; push_cast; exact h2
      exact_mod_cast h4
    exact h1.trans (Nat.pow_lt_pow_right (by norm_num) (by omega))
  | nmul dst a b =>
    obtain ⟨hd, -, -, hab⟩ := hl
    exact h.setReg hd (hab.trans (Nat.pow_lt_pow_right (by norm_num) (by omega)))
  | rdIn dst e =>
    obtain ⟨⟨-, hd⟩, -, -, hv⟩ := hl
    exact h.setMem hd (hv.le.trans (pow_le_pow_add ℓa ℓ))

/-- A bounded run keeps the real state clean. -/
theorem XExecB.clean {X : XCtx d} {ℓa ℓ : ℕ} {c : XCmd} {s s' : RealRAM.State d} {k : ℕ}
    (he : XExecB X ℓa ℓ c s k s') (h : Clean ℓa ℓ s) : Clean ℓa ℓ s' := by
  induction he with
  | skip => exact h
  | frag p s hp => exact clean_prim h hp
  | leaf l s hl => exact clean_leaf h hl
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ h)
  | ifR_t _ _ _ ih => exact ih h
  | ifR_f _ _ _ ih => exact ih h
  | ifN_t _ _ _ ih => exact ih h
  | ifN_f _ _ _ ih => exact ih h
  | whileR_t _ _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ h)
  | whileR_f => exact h
  | whileN_t _ _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ h)
  | whileN_f => exact h

/-- A real state with zero registers and cells is clean. -/
theorem clean_zero {ℓa ℓ : ℕ} {s : RealRAM.State d} (hn : ∀ i, s.nreg i = 0) (hm : ∀ j, s.mem j = 0) :
    Clean ℓa ℓ s where
  reg0 i _ := hn i
  regv i := by rw [hn i]; positivity
  mem0 j _ := hm j
  memv j := by rw [hm j, abs_zero]; positivity

/-! ## The space of a checkpoint -/

theorem two_pow_add_lt (ℓa ℓ : ℕ) : (2 : ℝ) ^ ℓ + 2 ^ ℓa < 2 ^ (ℓ + ℓa + 2) := by
  have h1 : (2 : ℝ) ^ ℓ ≤ 2 ^ (ℓ + ℓa) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (2 : ℝ) ^ ℓa ≤ 2 ^ (ℓ + ℓa) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : (2 : ℝ) ^ (ℓ + ℓa + 2) = 4 * 2 ^ (ℓ + ℓa) := by ring
  have h4 : (0 : ℝ) < 2 ^ (ℓ + ℓa) := by positivity
  linarith

theorem spaceLE_mono {t : BitRAM.State d} {B B' : ℝ} (h : BitRAM.SpaceLE t B) (hB : B ≤ B') :
    BitRAM.SpaceLE t B' := fun F hF => (h F hF).trans hB

/-- The space of a checkpoint: a bit state simulating a clean real state, with its scratch cells at `0`. -/
theorem space_checkpoint {X : XCtx d} {s : RealRAM.State d} {t : BitRAM.State d} {ℓa ℓ ℓi : ℕ}
    (hs : XSim X s t) (hc : Clean ℓa ℓ s) (h1 : t.mem T1 = 0) (h2 : t.mem T2 = 0)
    (hinp : ∀ j < X.off, BitRAM.len (X.inp j) ≤ ℓi) (hoff : X.off < 2 ^ ℓa) (h4 : 4 ≤ 2 ^ ℓa) :
    BitRAM.SpaceLE t (((X.off + 2 * 2 ^ ℓa) * (2 * ℓa + ℓ + ℓi + 3) : ℕ) : ℝ) := by
  set b := 2 * ℓa + ℓ + ℓi + 3
  set S : Finset ℤ := Finset.Ico (-((2 ^ ℓa : ℕ) : ℤ)) ((X.off : ℤ) + ((2 ^ ℓa : ℕ) : ℤ))
  have hP : (2 : ℕ) ≤ 2 ^ (ℓa + 1) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (ℓa + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have key : ∀ c, t.mem c ≠ 0 → c ∈ S ∧ BitRAM.len c + BitRAM.len (t.mem c) ≤ b := by
    intro c hne
    rcases (show c ≤ -4 ∨ c = TO ∨ c = T2 ∨ c = T1 ∨ (0 ≤ c ∧ c < X.off) ∨ (X.off : ℤ) ≤ c by
      unfold TO T1 T2; omega) with hc4 | hcT | hcT | hcT | ⟨hc0, hcI⟩ | hcR
    · obtain ⟨i, rfl⟩ : ∃ i : ℕ, c = rg i := ⟨(-c - 4).toNat, by unfold rg; omega⟩
      rw [hs.nreg] at hne ⊢
      have hi : i + 4 < 2 ^ ℓa := by
        by_contra hi
        exact hne (by rw [hc.reg0 i (by omega)]; rfl)
      refine ⟨?_, ?_⟩
      · simp only [S, Finset.mem_Ico, rg]; omega
      · have e1 : BitRAM.len (rg i) ≤ ℓa := size_rg i ℓa hi
        have e2 : BitRAM.len (s.nreg i : ℤ) ≤ ℓa + 1 := len_nat (hc.regv i)
        omega
    · subst hcT
      rw [hs.off]
      refine ⟨?_, ?_⟩
      · simp only [S, Finset.mem_Ico, TO]; omega
      · have e2 : BitRAM.len (X.off : ℤ) ≤ ℓa := len_nat hoff
        rw [len_TO]; omega
    · exact absurd (hcT ▸ h2) hne
    · exact absurd (hcT ▸ h1) hne
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, c = j := ⟨c.toNat, by omega⟩
      have hj : j < X.off := by omega
      rw [hs.inp j hj] at hne ⊢
      refine ⟨?_, ?_⟩
      · simp only [S, Finset.mem_Ico]; omega
      · have e1 : BitRAM.len (j : ℤ) ≤ ℓa := len_nat (hj.trans hoff)
        have e2 := hinp j hj
        omega
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, c = (j : ℤ) + X.off := ⟨(c - X.off).toNat, by omega⟩
      have hj : j < 2 ^ ℓa := by
        by_contra hj
        apply hne
        have e := hs.mem j
        rw [hc.mem0 j (by omega)] at e
        exact_mod_cast e
      refine ⟨?_, ?_⟩
      · simp only [S, Finset.mem_Ico]; omega
      · have e1 : BitRAM.len ((j : ℤ) + X.off) ≤ ℓa + 1 := len_cl hj hoff
        have e2 : BitRAM.len (t.mem ((j : ℤ) + X.off)) ≤ ℓ + ℓa + 2 :=
          len_val (hs.mem j) ((hc.memv j).trans_lt (two_pow_add_lt ℓa ℓ))
        omega
  have hsp := spaceLE_of_support t S (fun _ => b) key
  refine spaceLE_mono hsp (le_of_eq ?_)
  rw [Finset.sum_const, smul_eq_mul, Int.card_Ico]
  have e : ((X.off : ℤ) + ((2 ^ ℓa : ℕ) : ℤ) - -((2 ^ ℓa : ℕ) : ℤ)) = ((X.off + 2 * 2 ^ ℓa : ℕ) : ℤ) := by
    push_cast; ring
  rw [e, Int.toNat_natCast]

end AdversarialBco.Bit.Transfer
