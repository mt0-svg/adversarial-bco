/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PolyMap

@[expose] public section

/-!
# UNI-POLY, part 3: rules for `RCmd`, and the address block `PHI`

* `RS w L c t Q`: from `t`, `c` runs within the bound `L` to some `t'` in some `n` steps with `Q n t'`.
* The rules of `skip`, an instruction, sequence, both branches of `ifLt`; the effect of each instruction on the
  memory, the coins, the rounds and the points (`stepI_*`).
* `rs_PHI`: `PHI src dst` sets `dst` to `φ (M src)` and `cC` to `0` in at most `7` steps.
-/

namespace AdversarialBco.UniPoly

open AdversarialBco BitRAM BitRAMO

variable {d : ℕ}

/-! ## Specifications -/

/-- From `t`, `c` runs within the bound `L` to a state `t'` in `n` steps with `Q n t'`. -/
def RS (w : World d) (L : ℕ) (c : RCmd) (t : State d) (Q : ℕ → State d → Prop) : Prop :=
  ∃ n t', RX w L c t n t' ∧ Q n t'

variable {w : World d} {L : ℕ} {t : State d} {Q : ℕ → State d → Prop}

theorem RS.mono {c : RCmd} {Q' : ℕ → State d → Prop} (h : RS w L c t Q) (hQ : ∀ n t', Q n t' → Q' n t') :
    RS w L c t Q' := by
  obtain ⟨n, t', hx, hq⟩ := h; exact ⟨n, t', hx, hQ n t' hq⟩

theorem RS.skip (hQ : Q 0 t) : RS w L .skip t Q := ⟨0, t, .skip t, hQ⟩

theorem RS.ins {i : Instr} (h : InsOK w L t i) (hQ : Q 1 (stepI w i t)) : RS w L (.ins i) t Q :=
  ⟨1, _, .ins i t h, hQ⟩

theorem RS.seq {c₁ c₂ : RCmd} {Q₁ : ℕ → State d → Prop} (h₁ : RS w L c₁ t Q₁)
    (h₂ : ∀ n₁ t₁, Q₁ n₁ t₁ → RS w L c₂ t₁ (fun n₂ t₂ => Q (n₁ + n₂) t₂)) : RS w L (.seq c₁ c₂) t Q := by
  obtain ⟨n₁, t₁, hx₁, hq₁⟩ := h₁
  obtain ⟨n₂, t₂, hx₂, hq₂⟩ := h₂ n₁ t₁ hq₁
  exact ⟨n₁ + n₂, t₂, .seq hx₁ hx₂, hq₂⟩

theorem RS.ifT {a b : ℤ} {c₁ c₂ : RCmd} (ht : TestOK L a b t) (hc : t.mem a < t.mem b)
    (h : RS w L c₁ (addC t (tcost a b t)) (fun n t' => Q (n + 1) t')) : RS w L (.ifLt a b c₁ c₂) t Q := by
  obtain ⟨n, t', hx, hq⟩ := h; exact ⟨n + 1, t', .ifT ht hc hx, hq⟩

theorem RS.ifF {a b : ℤ} {c₁ c₂ : RCmd} (ht : TestOK L a b t) (hc : ¬ t.mem a < t.mem b)
    (h : RS w L c₂ (addC t (tcost a b t)) (fun n t' => Q (n + 2) (addC t' 1))) : RS w L (.ifLt a b c₁ c₂) t Q := by
  obtain ⟨n, t', hx, hq⟩ := h; exact ⟨n + 2, addC t' 1, .ifF ht hc hx, hq⟩

/-- The rule of a loop from an invariant: `I k u` holds after `k` turns, the loop runs while `k < K`, a turn takes at
most `nb` steps. -/
theorem RS.loop {a b : ℤ} {c : RCmd} (I : ℕ → State d → Prop) (K nb : ℕ) (h0 : I 0 t)
    (htest : ∀ k u, I k u → TestOK L a b u ∧ (u.mem a < u.mem b ↔ k < K))
    (hbody : ∀ k u, I k u → k < K →
      RS w L c (addC u (tcost a b u)) (fun n u' => n ≤ nb ∧ I (k + 1) (addC u' 1)))
    (hQ : ∀ n u, I K u → n ≤ K * (nb + 2) + 2 → Q n (addC u (tcost a b u + 1))) :
    RS w L (.whileLt a b c) t Q := by
  have key : ∀ j k u, k + j = K → I k u →
      ∃ n u', RX w L (.whileLt a b c) u n u' ∧ n ≤ j * (nb + 2) + 2 ∧ ∃ v, I K v ∧ u' = addC v (tcost a b v + 1) := by
    intro j
    induction j with
    | zero =>
      intro k u hk hI
      obtain ⟨ht, hiff⟩ := htest k u hI
      have hn : ¬ u.mem a < u.mem b := fun h => by have := hiff.1 h; omega
      exact ⟨2, _, .whF ht hn, by omega, u, by rwa [show k = K by omega] at hI, rfl⟩
    | succ j ih =>
      intro k u hk hI
      obtain ⟨ht, hiff⟩ := htest k u hI
      have hlt : u.mem a < u.mem b := hiff.2 (by omega)
      obtain ⟨n₁, u₁, hx₁, hn₁, hI₁⟩ := hbody k u hI (by omega)
      obtain ⟨n₂, u₂, hx₂, hn₂, v, hv, hu₂⟩ := ih (k + 1) (addC u₁ 1) (by omega) hI₁
      refine ⟨n₁ + n₂ + 2, u₂, .whT ht hlt hx₁ hx₂, ?_, v, hv, hu₂⟩
      rw [Nat.succ_mul]; omega
  obtain ⟨n, u', hx, hn, v, hv, rfl⟩ := key K 0 t (by omega) h0
  exact ⟨n, _, hx, hQ n v hv hn⟩

/-! ## The effect of the instructions -/

/-- The counter, the coins, the rounds and the points unchanged. -/
def Same' (t t' : State d) : Prop := t'.coins = t.coins ∧ t'.rounds = t.rounds ∧ t'.pts = t.pts

theorem Same'.refl (t : State d) : Same' t t := ⟨rfl, rfl, rfl⟩

theorem Same'.trans {t₁ t₂ t₃ : State d} (h₁ : Same' t₁ t₂) (h₂ : Same' t₂ t₃) : Same' t₁ t₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

@[simp] theorem addC_mem (t : State d) (k : ℕ) : (addC t k).mem = t.mem := rfl

theorem Same'.addC (t : State d) (k : ℕ) : Same' t (addC t k) := ⟨rfl, rfl, rfl⟩

/-- An instruction that is neither `coins` nor `play`. -/
def Plain : Instr → Prop
  | .coins .. => False
  | .play _ => False
  | _ => True

theorem stepI_same {i : Instr} (h : Plain i) (hj : NJ i) : Same' t (stepI w i t) := by
  cases i <;> simp_all [Plain, NJ, Same', stepI, step]

@[simp] theorem stepI_const_mem (dst c : ℤ) : (stepI w (.const dst c) t).mem = Function.update t.mem dst c := by
  simp [stepI, step]

@[simp] theorem stepI_add_mem (dst a b : ℤ) :
    (stepI w (.add dst a b) t).mem = Function.update t.mem dst (t.mem a + t.mem b) := by simp [stepI, step]

@[simp] theorem stepI_sub_mem (dst a b : ℤ) :
    (stepI w (.sub dst a b) t).mem = Function.update t.mem dst (t.mem a - t.mem b) := by simp [stepI, step]

@[simp] theorem stepI_mul_mem (dst a b : ℤ) :
    (stepI w (.mul dst a b) t).mem = Function.update t.mem dst (t.mem a * t.mem b) := by simp [stepI, step]

@[simp] theorem stepI_div_mem (dst a b : ℤ) :
    (stepI w (.div dst a b) t).mem = Function.update t.mem dst (t.mem a / t.mem b) := by simp [stepI, step]

@[simp] theorem stepI_load_mem (dst src : ℤ) :
    (stepI w (.load dst src) t).mem = Function.update t.mem dst (t.mem (t.mem src)) := by simp [stepI, step]

@[simp] theorem stepI_store_mem (dst src : ℤ) :
    (stepI w (.store dst src) t).mem = Function.update t.mem (t.mem dst) (t.mem src) := by simp [stepI, step]

@[simp] theorem stepI_obs_mem (dst prec : ℤ) :
    (stepI w (.obs dst prec) t).mem = Function.update t.mem dst (reading w t (t.mem prec).toNat) := by
  simp [stepI, step]; rfl

@[simp] theorem stepI_coins_mem (dst cnt : ℤ) :
    (stepI w (.coins dst cnt) t).mem = Function.update t.mem dst (readCoins w.cs t.coins (t.mem cnt).toNat) := by
  simp [stepI, step]

@[simp] theorem stepI_coins_coins (dst cnt : ℤ) :
    (stepI w (.coins dst cnt) t).coins = t.coins + (t.mem cnt).toNat := by simp [stepI, step]

@[simp] theorem stepI_play_mem (src : ℤ) : (stepI w (.play src) t).mem = t.mem := by simp [stepI, step]

@[simp] theorem stepI_play_coins (src : ℤ) : (stepI w (.play src) t).coins = t.coins := by simp [stepI, step]

@[simp] theorem stepI_play_rounds (src : ℤ) : (stepI w (.play src) t).rounds = t.rounds + 1 := by
  simp [stepI, step]

@[simp] theorem stepI_play_pts (src : ℤ) :
    (stepI w (.play src) t).pts = Function.update t.pts t.rounds (ptAt d t.mem (t.mem src)) := by
  simp [stepI, step]

/-! ## Lengths of small integers -/

theorem len_small {c : ℤ} (h1 : -1024 < c) (h2 : c < 1024) : len c ≤ 10 :=
  len_le_of_natAbs_lt (by have : (2 : ℕ) ^ 10 = 1024 := rfl; rw [this]; omega)

theorem len_two_mul (v : ℤ) : len (2 * v) ≤ len v + 1 := by
  rw [len_le_iff, Int.natAbs_mul, pow_succ]
  have := Nat.lt_size_self v.natAbs
  unfold len; simp; omega

theorem len_le_of_natAbs_le {a b : ℤ} (h : a.natAbs ≤ b.natAbs) : len a ≤ len b := Nat.size_le_size h

/-! ## `PHI` -/

/-- `PHI src dst`: `dst := φ (M src)`, `cC := 0`, in at most `7` steps, when `M cZ = 0`. -/
theorem rs_PHI {src dst : ℤ} (hdC : dst ≠ cC)
    (hz : t.mem cZ = 0) (hL : len (t.mem src) + 11 ≤ L) (hLs : len src ≤ L) (hLd : len dst ≤ L) (h10 : 10 ≤ L) :
    RS w L (PHI src dst) t (fun n t' => n ≤ 7 ∧
      t'.mem = Function.update (Function.update t.mem dst (φ (t.mem src))) cC 0 ∧ Same' t t') := by
  generalize hv : t.mem src = v at hL ⊢
  have hcC : len cC ≤ L := (len_small (by decide) (by decide)).trans h10
  have hcZ : len cZ ≤ L := (len_small (by decide) (by decide)).trans h10
  have h2v : len (v + v) ≤ L := by rw [← two_mul]; have := len_two_mul v; omega
  have hN : len (1 - N0) ≤ L := (len_small (by decide) (by decide)).trans h10
  have hN' : len (-N0) ≤ L := (len_small (by decide) (by decide)).trans h10
  have hφ : len (φ v) ≤ L := (len_φ v).trans hL
  unfold PHI
  simp only [seqL]
  by_cases hneg : v < 0
  · -- `v < 0`: `φ v = 2v + 1 - N0`
    refine RS.seq (Q₁ := fun n t₁ => n ≤ 6 ∧ t₁.mem = Function.update (Function.update t.mem dst (φ v)) cC (1 - N0) ∧
      Same' t t₁) ?_ ?_
    · refine RS.ifT ⟨hLs, hcZ, by rw [hv]; omega, by rw [hz]; simp [len_zero]⟩ (by rw [hz, hv]; exact hneg) ?_
      refine RS.seq (RS.ins ⟨hLd, hLs, hLs, by simp [hv]; omega, by simp [hv]; omega⟩ (Q := fun n t₁ => n = 1 ∧ t₁ =
        stepI w (.add dst src src) (addC t (tcost src cZ t))) ⟨rfl, rfl⟩) ?_
      rintro n₁ t₁ ⟨rfl, rfl⟩
      refine RS.seq (RS.ins ⟨hcC, hN⟩ (Q := fun n t₂ => n = 1 ∧ t₂ = stepI w (.const cC (1 - N0)) _) ⟨rfl, rfl⟩) ?_
      rintro n₂ t₂ ⟨rfl, rfl⟩
      have e1 : (stepI w (.const cC (1 - N0)) (stepI w (.add dst src src) (addC t (tcost src cZ t)))).mem dst =
          v + v := by simp [Function.update_of_ne hdC, hv]
      have e2 : (stepI w (.const cC (1 - N0)) (stepI w (.add dst src src) (addC t (tcost src cZ t)))).mem cC =
          1 - N0 := by simp
      refine RS.ins ⟨hLd, hLd, hcC, by rw [e1]; exact h2v, by rw [e2]; exact hN⟩ ⟨by omega, ?_, ?_⟩
      · rw [stepI_add_mem, e1, e2]
        have hφv : v + v + (1 - N0) = φ v := by unfold φ; simp only [show ¬ (0 : ℤ) ≤ v by omega, ↓reduceIte]; ring
        rw [hφv]
        simp only [stepI_const_mem, stepI_add_mem, addC_mem]
        rw [Function.update_comm hdC, Function.update_idem, Function.update_comm hdC.symm]
      · refine (Same'.addC t _).trans ((stepI_same (by simp [Plain]) (by simp [NJ])).trans
          ((stepI_same (by simp [Plain]) (by simp [NJ])).trans (stepI_same (by simp [Plain]) (by simp [NJ]))))
    · rintro n₁ t₁ ⟨hn₁, hm₁, hs₁⟩
      refine RS.ins ⟨hcC, by simp [len_zero]⟩ ⟨by omega, ?_, hs₁.trans (stepI_same (by simp [Plain]) (by simp [NJ]))⟩
      rw [stepI_const_mem, hm₁, Function.update_idem]
  · -- `v ≥ 0`: `φ v = -N0 - 2v`
    refine RS.seq (Q₁ := fun n t₁ => n ≤ 6 ∧ t₁.mem = Function.update (Function.update t.mem dst (φ v)) cC (-N0) ∧
      Same' t t₁) ?_ ?_
    · refine RS.ifF ⟨hLs, hcZ, by rw [hv]; omega, by rw [hz]; simp [len_zero]⟩ (by rw [hz, hv]; exact hneg) ?_
      refine RS.seq (RS.ins ⟨hLd, hLs, hLs, by simp [hv]; omega, by simp [hv]; omega⟩ (Q := fun n t₁ => n = 1 ∧ t₁ =
        stepI w (.add dst src src) (addC t (tcost src cZ t))) ⟨rfl, rfl⟩) ?_
      rintro n₁ t₁ ⟨rfl, rfl⟩
      refine RS.seq (RS.ins ⟨hcC, hN'⟩ (Q := fun n t₂ => n = 1 ∧ t₂ = stepI w (.const cC (-N0)) _) ⟨rfl, rfl⟩) ?_
      rintro n₂ t₂ ⟨rfl, rfl⟩
      have e1 : (stepI w (.const cC (-N0)) (stepI w (.add dst src src) (addC t (tcost src cZ t)))).mem dst =
          v + v := by simp [Function.update_of_ne hdC, hv]
      have e2 : (stepI w (.const cC (-N0)) (stepI w (.add dst src src) (addC t (tcost src cZ t)))).mem cC =
          -N0 := by simp
      refine RS.ins ⟨hLd, hcC, hLd, by rw [e2]; exact hN', by rw [e1]; exact h2v⟩ ⟨by omega, ?_, ?_⟩
      · rw [addC_mem, stepI_sub_mem, e1, e2]
        have hφv : -N0 - (v + v) = φ v := by unfold φ; simp only [show (0 : ℤ) ≤ v by omega, ↓reduceIte]; ring
        rw [hφv]
        simp only [stepI_const_mem, stepI_add_mem, addC_mem]
        rw [Function.update_comm hdC, Function.update_idem, Function.update_comm hdC.symm]
      · refine (Same'.addC t _).trans ((stepI_same (by simp [Plain]) (by simp [NJ])).trans
          ((stepI_same (by simp [Plain]) (by simp [NJ])).trans ((stepI_same (by simp [Plain]) (by simp [NJ])).trans
            (Same'.addC _ 1))))
    · rintro n₁ t₁ ⟨hn₁, hm₁, hs₁⟩
      refine RS.ins ⟨hcC, by simp [len_zero]⟩ ⟨by omega, ?_, hs₁.trans (stepI_same (by simp [Plain]) (by simp [NJ]))⟩
      rw [stepI_const_mem, hm₁, Function.update_idem]

/-! ## Straight lines -/

/-- The state after a straight line of instructions. -/
noncomputable def runI (w : World d) : List Instr → State d → State d
  | [], t => t
  | i :: is, t => runI w is (stepI w i t)

/-- Every instruction of a straight line within the bound `L`, each at the state it runs from. -/
def OKI (w : World d) (L : ℕ) : List Instr → State d → Prop
  | [], _ => True
  | i :: is, t => InsOK w L t i ∧ OKI w L is (stepI w i t)

theorem rs_seqI {is : List Instr} (h : OKI w L is t) :
    RS w L (seqI is) t (fun n t' => n = is.length ∧ t' = runI w is t) := by
  induction is generalizing t with
  | nil => exact RS.skip ⟨rfl, rfl⟩
  | cons i is ih =>
    obtain ⟨h1, h2⟩ := h
    cases is with
    | nil => exact RS.ins h1 ⟨rfl, rfl⟩
    | cons j js =>
      refine RS.seq (RS.ins h1 (Q := fun n t₁ => n = 1 ∧ t₁ = stepI w i t) ⟨rfl, rfl⟩) ?_
      rintro n₁ t₁ ⟨rfl, rfl⟩
      exact (ih h2).mono fun n t' ⟨hn, ht⟩ => ⟨by simp [hn]; omega, ht⟩

/-- A straight line of plain instructions keeps the coins, the rounds and the points. -/
theorem runI_same {is : List Instr} (h : ∀ i ∈ is, Plain i ∧ NJ i) : Same' t (runI w is t) := by
  induction is generalizing t with
  | nil => exact Same'.refl t
  | cons i is ih =>
    exact (stepI_same (h i (by simp)).1 (h i (by simp)).2).trans
      (ih fun j hj => h j (List.mem_cons_of_mem i hj))

/-! ## `load` and `store` -/

/-- `LOADB dst src`: the cell `φ dst` gets `M (φ (M (φ src)))`; the scratch cells `cA`, `cC` stay `0`. -/
theorem rs_LOADB {dst src : ℤ} (hz : t.mem cZ = 0) (hA : t.mem cA = 0) (hC : t.mem cC = 0)
    (hL : len (t.mem (φ src)) + 11 ≤ L) (hLs : len src + 11 ≤ L) (hLd : len dst + 11 ≤ L)
    (hLv : len (t.mem (φ (t.mem (φ src)))) ≤ L) :
    RS w L (LOADB dst src) t (fun n t' => n ≤ 9 ∧
      t'.mem = Function.update t.mem (φ dst) (t.mem (φ (t.mem (φ src)))) ∧ Same' t t') := by
  have h10 : 10 ≤ L := by omega
  have hcA : len cA ≤ L := (len_small (by decide) (by decide)).trans h10
  have hfA : φ (t.mem (φ src)) ≠ cA := φ_ne_of_gt (by decide)
  have hfC : φ (t.mem (φ src)) ≠ cC := φ_ne_of_gt (by decide)
  have hdA : φ dst ≠ cA := φ_ne_of_gt (by decide)
  have hdC : φ dst ≠ cC := φ_ne_of_gt (by decide)
  unfold LOADB; simp only [seqL]
  refine RS.seq (rs_PHI (by decide) hz hL ((len_φ src).trans hLs) hcA h10) ?_
  rintro n₁ t₁ ⟨hn₁, hm₁, hs₁⟩
  have e1 : t₁.mem cA = φ (t.mem (φ src)) := by rw [hm₁]; simp
  have e2 : t₁.mem (φ (t.mem (φ src))) = t.mem (φ (t.mem (φ src))) := by
    rw [hm₁, Function.update_of_ne hfC, Function.update_of_ne hfA]
  refine (rs_seqI (is := [.load (φ dst) cA, .const cA 0]) (t := t₁) ⟨⟨(len_φ dst).trans hLd, hcA, by rw [e1]; exact (len_φ _).trans hL, by rw [e1, e2]; exact hLv⟩,
    ⟨hcA, by simp [len_zero]⟩, trivial⟩).mono ?_
  rintro n t' ⟨hn, rfl⟩
  refine ⟨by simp at hn; omega, ?_, hs₁.trans (runI_same (by simp [Plain, NJ]))⟩
  simp only [runI, stepI_const_mem, stepI_load_mem, e1, e2]
  rw [hm₁]
  funext c
  simp only [Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

/-- `STOREB dst src`: the cell `φ (M (φ dst))` gets `M (φ src)`; the scratch cells `cA`, `cC` stay `0`. -/
theorem rs_STOREB {dst src : ℤ} (hz : t.mem cZ = 0) (hA : t.mem cA = 0) (hC : t.mem cC = 0)
    (hL : len (t.mem (φ dst)) + 11 ≤ L) (hLs : len src + 11 ≤ L) (hLd : len dst + 11 ≤ L)
    (hLv : len (t.mem (φ src)) ≤ L) :
    RS w L (STOREB dst src) t (fun n t' => n ≤ 9 ∧
      t'.mem = Function.update t.mem (φ (t.mem (φ dst))) (t.mem (φ src)) ∧ Same' t t') := by
  have h10 : 10 ≤ L := by omega
  have hcA : len cA ≤ L := (len_small (by decide) (by decide)).trans h10
  have hfA : φ (t.mem (φ dst)) ≠ cA := φ_ne_of_gt (by decide)
  have hfC : φ (t.mem (φ dst)) ≠ cC := φ_ne_of_gt (by decide)
  have hsA : φ src ≠ cA := φ_ne_of_gt (by decide)
  have hsC : φ src ≠ cC := φ_ne_of_gt (by decide)
  unfold STOREB; simp only [seqL]
  refine RS.seq (rs_PHI (by decide) hz hL ((len_φ dst).trans hLd) hcA h10) ?_
  rintro n₁ t₁ ⟨hn₁, hm₁, hs₁⟩
  have e1 : t₁.mem cA = φ (t.mem (φ dst)) := by rw [hm₁]; simp
  have e2 : t₁.mem (φ src) = t.mem (φ src) := by
    rw [hm₁, Function.update_of_ne hsC, Function.update_of_ne hsA]
  refine (rs_seqI (is := [.store cA (φ src), .const cA 0]) (t := t₁) ⟨⟨hcA, (len_φ src).trans hLs, by rw [e1]; exact (len_φ _).trans hL, by rw [e2]; exact hLv⟩,
    ⟨hcA, by simp [len_zero]⟩, trivial⟩).mono ?_
  rintro n t' ⟨hn, rfl⟩
  refine ⟨by simp at hn; omega, ?_, hs₁.trans (runI_same (by simp [Plain, NJ]))⟩
  simp only [runI, stepI_const_mem, stepI_store_mem, e1, e2]
  rw [hm₁]
  funext c
  simp only [Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

end AdversarialBco.UniPoly
