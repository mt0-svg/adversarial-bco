/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PolyRS

@[expose] public section

/-!
# UNI-POLY, part 4: the buffer blocks `CLEARY`, `COPYN`, `PLAYB`

* `rs_CLEARY`: `Y := 0` on the `d + 1` cells of the buffer from `YB`, the scratch cells back at `0`.
* `rs_COPYN`: the point of `P` at `a = M src` into the buffer, normalised (`Y_0 > 0`, the same point).
* `rs_PLAYB`: `play src` of `P`.
-/

namespace AdversarialBco.UniPoly

open AdversarialBco BitRAM BitRAMO RCmd

variable {d : ℕ} {w : World d} {L : ℕ} {t : State d}

/-- Lengths of nonnegative integers grow with the value. -/
theorem len_mono {a b : ℤ} (ha : 0 ≤ a) (hab : a ≤ b) : len a ≤ len b :=
  len_le_of_natAbs_le (by omega)

/-- Evaluate the cells at known addresses after a straight line: the updates and the branches whose conditions
`omega` decides. -/
macro "evl" : tactic => `(tactic| simp (disch := omega) only [runI, addC_mem, stepI_const_mem, stepI_add_mem,
  stepI_sub_mem, stepI_mul_mem, stepI_div_mem, stepI_store_mem, stepI_load_mem, stepI_obs_mem, stepI_coins_mem,
  stepI_play_mem, Function.update_self, Function.update_of_ne,
  ite_eq_left, ite_eq_right, ↓reduceIte, ite_true, ite_false])

/-- Close a goal by cases on the remaining updates and branches. -/
macro "cases_omega" : tactic => `(tactic| (simp only [Function.update_apply]; split_ifs <;> (try subst_vars) <;>
  (try simp only [add_sub_cancel_left, add_sub_cancel_right, sub_self, add_zero]) <;> first | rfl | omega))

theorem len_scr {c : ℤ} (h1 : -1024 < c) (h2 : c < 1024) (h10 : 10 ≤ L) : len c ≤ L := (len_small h1 h2).trans h10

/-- `CLEARY`: the buffer `Y` of `d + 1` cells from `YB` back at `0`, from `cOne = cD1 = cI = cB = 0`. -/
theorem rs_CLEARY {YB : ℤ} (hz : t.mem cZ = 0) (hd : t.mem 0 = d) (hYB : t.mem cYB = YB) (hYB0 : 0 ≤ YB)
    (hOne : t.mem cOne = 0) (hD1 : t.mem cD1 = 0) (hI : t.mem cI = 0) (hB : t.mem cB = 0)
    (hLY : len (YB + d) ≤ L) (hLd : len ((d : ℤ) + 1) ≤ L) (h10 : 10 ≤ L) :
    RS w L CLEARY t (fun n t' => n ≤ 6 * d + 16 ∧
      t'.mem = (fun c => if YB ≤ c ∧ c ≤ YB + d then 0 else t.mem c) ∧ Same' t t') := by
  unfold CLEARY; simp only [seqL, seqI]
  set G : ℕ → ℤ → ℤ := fun k c => if YB ≤ c ∧ c < YB + k then 0 else if c = cI then (k : ℤ) else
    if c = cOne then 1 else if c = cD1 then (d : ℤ) + 1 else t.mem c with hG
  have hk : ∀ k : ℕ, k ≤ d + 1 → len (k : ℤ) ≤ L := fun k hk =>
    (len_mono (by omega) (by omega : (k : ℤ) ≤ d + 1)).trans hLd
  have hd0 : len (d : ℤ) ≤ L := (len_mono (by omega) (by omega)).trans hLd
  have h1 : len (1 : ℤ) ≤ L := by rw [len_one]; omega
  have hY0 : len YB ≤ L := (len_mono hYB0 (by omega)).trans hLY
  have l0 : len (0 : ℤ) ≤ L := by rw [len_zero]; omega
  refine RS.seq (rs_seqI (is := [.const cOne 1, .add cD1 0 cOne]) (t := t)
    ⟨⟨len_scr (by decide) (by decide) h10, h1⟩,
     ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      len_scr (by decide) (by decide) h10, by evl; rw [hd]; exact hd0, by evl; exact h1⟩, trivial⟩) ?_
  rintro n₁ t₁ ⟨hn₁, rfl⟩
  have hs₁ : Same' t (runI w [.const cOne 1, .add cD1 0 cOne] t) := runI_same (by simp [Plain, NJ])
  have hm₁ : (runI w [.const cOne 1, .add cD1 0 cOne] t).mem = G 0 := by
    funext c; evl; rw [hd]; simp only [hG]; cases_omega
  refine RS.seq (Q₁ := fun n u => n ≤ (d + 1) * 6 + 2 ∧ u.mem = G (d + 1) ∧ Same' t u)
    (RS.loop (fun k u => k ≤ d + 1 ∧ u.mem = G k ∧ Same' t u) (d + 1) 4 ⟨by omega, hm₁, hs₁⟩ ?_ ?_ ?_) ?_
  · rintro k u ⟨hk1, hu, -⟩
    have e1 : u.mem cI = k := by rw [hu, hG]; evl
    have e2 : u.mem cD1 = (d : ℤ) + 1 := by rw [hu, hG]; evl
    refine ⟨⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, by rw [e1]; exact hk k hk1,
      by rw [e2]; exact hLd⟩, by rw [e1, e2]; omega⟩
  · rintro k u ⟨hk1, hu, hsu⟩ hkK
    have hkL := hk k hk1
    have hYk : len (YB + k) ≤ L := (len_mono (by omega) (by omega)).trans hLY
    have e1 : u.mem cI = k := by rw [hu, hG]; evl
    have e3 : u.mem cYB = YB := by rw [hu, hG]; evl; exact hYB
    have e4 : u.mem cOne = 1 := by rw [hu, hG]; evl
    have e5 : u.mem cZ = 0 := by rw [hu, hG]; evl; exact hz
    refine (rs_seqI (is := [.add cB cYB cI, .store cB cZ, .add cI cI cOne, .const cB 0]) (t := addC u _)
      ⟨⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        len_scr (by decide) (by decide) h10, by evl; rw [e3]; exact hY0, by evl; rw [e1]; exact hkL⟩,
       ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, by evl; rw [e3, e1]; exact hYk,
        by evl; rw [e5]; exact l0⟩,
       ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        len_scr (by decide) (by decide) h10, by evl; rw [e1]; exact hkL, by evl; rw [e4]; exact h1⟩,
       ⟨len_scr (by decide) (by decide) h10, l0⟩, trivial⟩).mono ?_
    rintro n u' ⟨hn, rfl⟩
    refine ⟨by simp at hn; omega, by omega, ?_, (hsu.trans ((Same'.addC _ _).trans
      (runI_same (by simp [Plain, NJ])))).trans (Same'.addC _ 1)⟩
    funext c; evl; rw [e3, e1, e5, e4, hu]; simp only [hG]; cases_omega
  · rintro n u ⟨hk1, hu, hsu⟩ hn
    exact ⟨hn, hu, hsu.trans (Same'.addC _ _)⟩
  · rintro n₂ t₂ ⟨hn₂, hm₂, hs₂⟩
    refine (rs_seqI (is := [.const cOne 0, .const cD1 0, .const cI 0, .const cB 0]) (t := t₂)
      ⟨⟨len_scr (by decide) (by decide) h10, l0⟩, ⟨len_scr (by decide) (by decide) h10, l0⟩,
        ⟨len_scr (by decide) (by decide) h10, l0⟩, ⟨len_scr (by decide) (by decide) h10, l0⟩, trivial⟩).mono ?_
    rintro n u' ⟨hn, rfl⟩
    refine ⟨by simp only [List.length_cons, List.length_nil] at hn₁ hn; omega, ?_,
      hs₂.trans (runI_same (by simp [Plain, NJ]))⟩
    funext c; evl; rw [hm₂]; simp only [hG]; cases_omega

/-! ## The copy loop -/

/-- The copy loop: `Y_i := sg · y_i` for `i ≤ d`, `y_i = M (φ (a + i))`. -/
theorem rs_COPYLOOP {u0 : State d} {a YB sg : ℤ} (hsg : sg = 1 ∨ sg = -1) (hYB0 : 0 ≤ YB)
    (hI : u0.mem cI = 0) (hD1 : u0.mem cD1 = (d : ℤ) + 1) (hOne : u0.mem cOne = 1) (hAa : u0.mem cAa = a)
    (hSg : u0.mem cSg = sg) (hYB : u0.mem cYB = YB) (hz : u0.mem cZ = 0) (hX : u0.mem cX = 0)
    (hA : u0.mem cA = 0) (hV : u0.mem cV = 0) (hB : u0.mem cB = 0) (hC : u0.mem cC = 0)
    (hLa : ∀ j : ℕ, j ≤ d → len (a + j) + 11 ≤ L) (hLy : ∀ j : ℕ, j ≤ d → len (u0.mem (φ (a + j))) ≤ L)
    (hLY : len (YB + d) ≤ L) (hLd : len ((d : ℤ) + 1) ≤ L) (h10 : 10 ≤ L) :
    RS w L COPYLOOP u0 (fun n u' => n ≤ (d + 1) * 19 + 2 ∧
      u'.mem = (fun c => if YB ≤ c ∧ c < YB + (d + 1) then sg * u0.mem (φ (a + (c - YB))) else
        if c = cI then (d : ℤ) + 1 else u0.mem c) ∧ Same' u0 u') := by
  unfold COPYLOOP
  set H : ℕ → ℤ → ℤ := fun k c => if YB ≤ c ∧ c < YB + k then sg * u0.mem (φ (a + (c - YB))) else
    if c = cI then (k : ℤ) else u0.mem c with hH
  have hk : ∀ k : ℕ, k ≤ d + 1 → len (k : ℤ) ≤ L := fun k hk =>
    (len_mono (by omega) (by omega : (k : ℤ) ≤ d + 1)).trans hLd
  have h1 : len (1 : ℤ) ≤ L := by rw [len_one]; omega
  have hY0 : len YB ≤ L := (len_mono hYB0 (by omega)).trans hLY
  have l0 : len (0 : ℤ) ≤ L := by rw [len_zero]; omega
  have hsgL : len sg ≤ L := by
    rcases hsg with rfl | rfl
    · rw [len_one]; omega
    · have : len (-1 : ℤ) = 1 := rfl
      omega
  have ha0 : len a ≤ L := by have := hLa 0 (by omega); simp only [Nat.cast_zero, add_zero] at this; omega
  have hm0 : u0.mem = H 0 := by
    funext c; simp only [hH]; split_ifs <;> (try subst_vars) <;> first | rfl | omega
  refine RS.loop (fun k u => k ≤ d + 1 ∧ u.mem = H k ∧ Same' u0 u) (d + 1) 17 ⟨by omega, hm0, Same'.refl _⟩
    ?_ ?_ ?_
  · rintro k u ⟨hk1, hu, -⟩
    have e1 : u.mem cI = k := by rw [hu, hH]; evl
    have e2 : u.mem cD1 = (d : ℤ) + 1 := by rw [hu, hH]; evl; exact hD1
    refine ⟨⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, by rw [e1]; exact hk k hk1,
      by rw [e2]; exact hLd⟩, by rw [e1, e2]; omega⟩
  · rintro k u ⟨hk1, hu, hsu⟩ hkK
    have hkL := hk k hk1
    have hYk : len (YB + k) ≤ L := (len_mono (by omega) (by omega)).trans hLY
    have hφk : φ (a + k) ≤ -1000 := φ_le _
    have hak := hLa k (by omega)
    have hyk := hLy k (by omega)
    have e1 : u.mem cI = k := by rw [hu, hH]; evl
    have eAa : u.mem cAa = a := by rw [hu, hH]; evl; exact hAa
    have eZ : u.mem cZ = 0 := by rw [hu, hH]; evl; exact hz
    have eYB : u.mem cYB = YB := by rw [hu, hH]; evl; exact hYB
    have eSg : u.mem cSg = sg := by rw [hu, hH]; evl; exact hSg
    have eOne : u.mem cOne = 1 := by rw [hu, hH]; evl; exact hOne
    have eφ : u.mem (φ (a + k)) = u0.mem (φ (a + k)) := by rw [hu, hH]; evl
    simp only [seqL]
    refine RS.seq (RS.ins (Q := fun n s => n = 1 ∧ s = stepI w (.add cX cAa cI) (addC u (tcost cI cD1 u)))
      ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        len_scr (by decide) (by decide) h10, by rw [addC_mem, eAa]; exact ha0, by rw [addC_mem, e1]; exact hkL⟩
      ⟨rfl, rfl⟩) ?_
    rintro n₁ s₁ ⟨rfl, rfl⟩
    have f1 : (stepI w (.add cX cAa cI) (addC u (tcost cI cD1 u))).mem cX = a + k := by evl; rw [eAa, e1]
    have f2 : (stepI w (.add cX cAa cI) (addC u (tcost cI cD1 u))).mem cZ = 0 := by evl; exact eZ
    refine RS.seq (rs_PHI (by decide) f2 (by rw [f1]; exact hak) (len_scr (by decide) (by decide) h10)
      (len_scr (by decide) (by decide) h10) h10) ?_
    rintro n₂ s₂ ⟨hn₂, hm₂, hs₂⟩
    rw [f1] at hm₂
    have g1 : s₂.mem cA = φ (a + k) := by rw [hm₂]; evl
    have g2 : s₂.mem (φ (a + k)) = u0.mem (φ (a + k)) := by rw [hm₂]; evl; exact eφ
    have g3 : s₂.mem cSg = sg := by rw [hm₂]; evl; exact eSg
    have g4 : s₂.mem cYB = YB := by rw [hm₂]; evl; exact eYB
    have g5 : s₂.mem cI = k := by rw [hm₂]; evl; exact e1
    have g6 : s₂.mem cOne = 1 := by rw [hm₂]; evl; exact eOne
    have hmy : len (u0.mem (φ (a + k)) * sg) ≤ L := by
      rcases hsg with rfl | rfl
      · rw [mul_one]; exact hyk
      · rw [mul_neg_one]; unfold len; rw [Int.natAbs_neg]; exact hyk
    refine (rs_seqI (is := [.load cV cA, .mul cV cV cSg, .add cB cYB cI, .store cB cV, .add cI cI cOne,
      .const cX 0, .const cA 0, .const cV 0, .const cB 0]) (t := s₂)
      ⟨⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by rw [g1]; exact (len_φ _).trans hak, by rw [g1, g2]; exact hyk⟩,
       ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        len_scr (by decide) (by decide) h10, by evl; rw [g1, g2]; exact hyk, by evl; rw [g3]; exact hsgL⟩,
       ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        len_scr (by decide) (by decide) h10, by evl; rw [g4]; exact hY0, by evl; rw [g5]; exact hkL⟩,
       ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by evl; rw [g4, g5]; exact hYk, by evl; rw [g1, g2, g3]; exact hmy⟩,
       ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        len_scr (by decide) (by decide) h10, by evl; rw [g5]; exact hkL, by evl; rw [g6]; exact h1⟩,
       ⟨len_scr (by decide) (by decide) h10, l0⟩, ⟨len_scr (by decide) (by decide) h10, l0⟩,
       ⟨len_scr (by decide) (by decide) h10, l0⟩, ⟨len_scr (by decide) (by decide) h10, l0⟩, trivial⟩).mono ?_
    rintro n u' ⟨hn, rfl⟩
    refine ⟨by simp at hn; omega, by omega, ?_, (hsu.trans ((Same'.addC _ _).trans ((stepI_same (by simp [Plain])
      (by simp [NJ])).trans (hs₂.trans (runI_same (by simp [Plain, NJ])))))).trans (Same'.addC _ 1)⟩
    funext c; evl; rw [g1, g2, g3, g4, g5, g6, hm₂]; evl; rw [hu]; simp only [hH]
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> (try simp only [add_sub_cancel_left, mul_comm]) <;> first | rfl | omega
  · rintro n u ⟨hk1, hu, hsu⟩ hn
    exact ⟨by nlinarith, hu, hsu.trans (Same'.addC _ _)⟩

/-! ## `COPYN` -/

/-- The buffer entry `j` for the point with denominator `y0` and entry `yj` at `j`: `yj` times the sign of `y0`, or the
point `(1, 0, ..., 0)` when `y0 = 0`. -/
def nrm (y0 yj j : ℤ) : ℤ := if y0 = 0 then (if j = 0 then 1 else 0) else if y0 < 0 then -yj else yj

set_option maxHeartbeats 4000000 in
/-- `COPYN src`: the point of `P` at `a = M (φ src)` into the buffer, normalised; the scratch cells back at `0`. -/
theorem rs_COPYN {src a YB : ℤ} (ha : t.mem (φ src) = a) (hYB0 : 0 ≤ YB) (hYB : t.mem cYB = YB)
    (hd : t.mem 0 = d) (hz : t.mem cZ = 0) (hAa : t.mem cAa = 0) (hOne : t.mem cOne = 0) (hD1 : t.mem cD1 = 0)
    (hA : t.mem cA = 0) (hC : t.mem cC = 0) (hY0 : t.mem cY0 = 0) (hSg : t.mem cSg = 0) (hI : t.mem cI = 0)
    (hX : t.mem cX = 0) (hV : t.mem cV = 0) (hB : t.mem cB = 0)
    (hYz : ∀ c, YB ≤ c → c ≤ YB + d → t.mem c = 0)
    (hLs : len src + 11 ≤ L) (hLa : ∀ j : ℕ, j ≤ d → len (a + j) + 11 ≤ L)
    (hLy : ∀ j : ℕ, j ≤ d → len (t.mem (φ (a + j))) ≤ L)
    (hLY : len (YB + d) ≤ L) (hLd : len ((d : ℤ) + 1) ≤ L) (h10 : 10 ≤ L) :
    RS w L (COPYN src) t (fun n t' => n ≤ (d + 1) * 19 + 40 ∧
      t'.mem = (fun c => if YB ≤ c ∧ c ≤ YB + d then nrm (t.mem (φ a)) (t.mem (φ (a + (c - YB)))) (c - YB)
        else t.mem c) ∧ Same' t t') := by
  have h1 : len (1 : ℤ) ≤ L := by rw [len_one]; omega
  have l0 : len (0 : ℤ) ≤ L := by rw [len_zero]; omega
  have hd0 : len (d : ℤ) ≤ L := (len_mono (by omega) (by omega)).trans hLd
  have hY0L : len YB ≤ L := (len_mono hYB0 (by omega)).trans hLY
  have ha0 : len a + 11 ≤ L := by have := hLa 0 (by omega); simp only [Nat.cast_zero, add_zero] at this; omega
  have hy0 : len (t.mem (φ a)) ≤ L := by have := hLy 0 (by omega); simp only [Nat.cast_zero, add_zero] at this; omega
  have hφa : φ a ≤ -1000 := φ_le _
  have hφs : φ src ≤ -1000 := φ_le _
  set y0 := t.mem (φ a) with hy0d
  unfold COPYN; simp only [seqL]
  -- the address and the two constants
  refine RS.seq (rs_seqI (is := [.add cAa (φ src) cZ, .const cOne 1, .add cD1 0 cOne]) (t := t)
    ⟨⟨len_scr (by decide) (by decide) h10, (len_φ _).trans hLs, len_scr (by decide) (by decide) h10,
      by rw [ha]; omega, by rw [hz]; exact l0⟩,
     ⟨len_scr (by decide) (by decide) h10, h1⟩,
     ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      len_scr (by decide) (by decide) h10, by evl; rw [hd]; exact hd0, by evl; exact h1⟩, trivial⟩) ?_
  rintro n₁ t₁ ⟨hn₁, rfl⟩
  have m1 : (runI w [.add cAa (φ src) cZ, .const cOne 1, .add cD1 0 cOne] t).mem =
      Function.update (Function.update (Function.update t.mem cAa a) cOne 1) cD1 ((d : ℤ) + 1) := by
    simp only [runI, stepI_add_mem, stepI_const_mem]; evl; simp only [ha, hz, hd, add_zero]
  have s1 : Same' t (runI w [.add cAa (φ src) cZ, .const cOne 1, .add cD1 0 cOne] t) :=
    runI_same (by simp [Plain, NJ])
  set t₁ := runI w [.add cAa (φ src) cZ, .const cOne 1, .add cD1 0 cOne] t with ht₁
  -- `cA := φ a`
  refine RS.seq (rs_PHI (src := cAa) (dst := cA) (by decide) (by rw [m1]; evl; exact hz)
    (by rw [m1]; evl; exact ha0) (len_scr (by decide) (by decide) h10) (len_scr (by decide) (by decide) h10) h10) ?_
  rintro n₂ t₂ ⟨hn₂, hm₂, hs₂⟩
  have m2 : t₂.mem = Function.update (Function.update (Function.update (Function.update (Function.update t.mem cAa a)
      cOne 1) cD1 ((d : ℤ) + 1)) cA (φ a)) cC 0 := by
    rw [hm₂, m1]; congr 2; try evl
  -- `cY0 := y0`, `cSg := 1`, `cA := 0`
  refine RS.seq (rs_seqI (is := [.load cY0 cA, .const cSg 1, .const cA 0]) (t := t₂)
    ⟨⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      by rw [m2]; evl; exact (len_φ _).trans (by omega), by rw [m2]; evl; exact hy0⟩,
     ⟨len_scr (by decide) (by decide) h10, h1⟩, ⟨len_scr (by decide) (by decide) h10, l0⟩, trivial⟩) ?_
  rintro n₃ t₃ ⟨hn₃, rfl⟩
  set F3 : ℤ → ℤ := Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update t.mem cAa a) cOne 1) cD1 ((d : ℤ) + 1)) cA (φ a)) cC 0) cY0 y0)
    cSg 1) cA 0 with hF3
  have m3 : (runI w [.load cY0 cA, .const cSg 1, .const cA 0] t₂).mem = F3 := by
    simp only [runI, stepI_load_mem, stepI_const_mem]; rw [m2]; congr 3; evl; try rfl
  have s3 : Same' t₂ (runI w [.load cY0 cA, .const cSg 1, .const cA 0] t₂) := runI_same (by simp [Plain, NJ])
  set t₃ := runI w [.load cY0 cA, .const cSg 1, .const cA 0] t₂ with ht₃
  have e3Y0 : t₃.mem cY0 = y0 := by rw [m3, hF3]; evl
  have e3Z : t₃.mem cZ = 0 := by rw [m3, hF3]; evl; exact hz
  -- the sign
  set sg : ℤ := if y0 < 0 then -1 else 1 with hsg
  refine RS.seq (Q₁ := fun n t₄ => n ≤ 2 ∧ t₄.mem = Function.update F3 cSg sg ∧ Same' t₃ t₄) ?_ ?_
  · by_cases hneg : y0 < 0
    · refine RS.ifT ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by rw [e3Y0]; exact hy0, by rw [e3Z]; exact l0⟩ (by rw [e3Y0, e3Z]; exact hneg) ?_
      refine RS.ins ⟨len_scr (by decide) (by decide) h10, by have : len (-1 : ℤ) = 1 := rfl; omega⟩
        ⟨by omega, ?_, (Same'.addC _ _).trans (stepI_same (by simp [Plain]) (by simp [NJ]))⟩
      rw [stepI_const_mem, addC_mem, m3, hsg, ite_eq_left hneg]
    · refine RS.ifF ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by rw [e3Y0]; exact hy0, by rw [e3Z]; exact l0⟩ (by rw [e3Y0, e3Z]; exact hneg) (RS.skip ?_)
      refine ⟨by omega, ?_, (Same'.addC _ _).trans (Same'.addC _ 1)⟩
      rw [addC_mem, addC_mem, m3, hsg, ite_eq_right hneg]
      funext c; simp only [hF3, Function.update_apply]; split_ifs <;> (try subst_vars) <;> first | rfl | omega
  rintro n₄ t₄ ⟨hn₄, m4, hs₄⟩
  have hφ4 : ∀ x, t₄.mem (φ x) = t.mem (φ x) := fun x => by
    have : φ x ≤ -1000 := φ_le x
    rw [m4, hF3]; evl
  have e4I : t₄.mem cI = 0 := by rw [m4, hF3]; evl; exact hI
  have e4D1 : t₄.mem cD1 = (d : ℤ) + 1 := by rw [m4, hF3]; evl
  have e4One : t₄.mem cOne = 1 := by rw [m4, hF3]; evl
  have e4Aa : t₄.mem cAa = a := by rw [m4, hF3]; evl
  have e4Sg : t₄.mem cSg = sg := by rw [m4, Function.update_self]
  have e4YB : t₄.mem cYB = YB := by rw [m4, hF3]; evl; exact hYB
  have e4Z : t₄.mem cZ = 0 := by rw [m4, hF3]; evl; exact hz
  have e4X : t₄.mem cX = 0 := by rw [m4, hF3]; evl; exact hX
  have e4A : t₄.mem cA = 0 := by rw [m4, hF3]; evl
  have e4V : t₄.mem cV = 0 := by rw [m4, hF3]; evl; exact hV
  have e4B : t₄.mem cB = 0 := by rw [m4, hF3]; evl; exact hB
  have e4C : t₄.mem cC = 0 := by rw [m4, hF3]; evl
  have e4Y0 : t₄.mem cY0 = y0 := by rw [m4, hF3]; evl
  have hLy4 : ∀ j : ℕ, j ≤ d → len ((addC (addC t₄ 0) 0).mem (φ (a + j))) ≤ L := fun j hj => by
    rw [addC_mem, addC_mem, hφ4]; exact hLy j hj
  have hT : TestOK L cZ cY0 t₄ := ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
    by rw [e4Z]; exact l0, by rw [e4Y0]; exact hy0⟩
  have hT' : TestOK L cY0 cZ (addC t₄ (tcost cZ cY0 t₄)) := ⟨len_scr (by decide) (by decide) h10,
    len_scr (by decide) (by decide) h10, by rw [addC_mem, e4Y0]; exact hy0, by rw [addC_mem, e4Z]; exact l0⟩
  set M5 : ℤ → ℤ := fun c => if YB ≤ c ∧ c ≤ YB + d then nrm y0 (t.mem (φ (a + (c - YB)))) (c - YB) else
    if c = cI then (if y0 = 0 then 0 else (d : ℤ) + 1) else t₄.mem c with hM5
  refine RS.seq (Q₁ := fun n t₅ => n ≤ (d + 1) * 19 + 6 ∧ t₅.mem = M5 ∧ Same' t₄ t₅) ?_ ?_
  · rcases lt_trichotomy y0 0 with hneg | h0 | hpos
    · -- `y0 < 0`: the copy with the sign `-1`
      have hsg' : sg = -1 := by rw [hsg, ite_eq_left hneg]
      refine RS.ifF hT (by rw [e4Z, e4Y0]; omega) (RS.ifT hT' (by simp only [addC_mem, e4Y0, e4Z]; exact hneg) ?_)
      refine (rs_COPYLOOP (Or.inr hsg') hYB0 (by simp [e4I]) (by simp [e4D1]) (by simp [e4One]) (by simp [e4Aa])
        (by simp [e4Sg, hsg']) (by simp [e4YB]) (by simp [e4Z]) (by simp [e4X]) (by simp [e4A]) (by simp [e4V])
        (by simp [e4B]) (by simp [e4C]) hLa (fun j hj => by simpa using hLy4 j hj) hLY hLd h10).mono ?_
      rintro n u' ⟨hn, hu', hsu'⟩
      refine ⟨by omega, ?_, ((Same'.addC _ _).trans ((Same'.addC _ _).trans hsu')).trans (Same'.addC _ 1)⟩
      rw [addC_mem, hu', hM5]
      funext c
      simp only [addC_mem]
      have : φ (a + (c - YB)) ≤ -1000 := φ_le _
      by_cases hc : YB ≤ c ∧ c ≤ YB + d
      · rw [ite_eq_left (by omega), ite_eq_left hc, hφ4, hsg']
        simp only [nrm, ite_eq_right (show ¬ y0 = 0 by omega), ite_eq_left hneg]; ring
      · rw [ite_eq_right (by omega), ite_eq_right hc]
        split_ifs <;> first | rfl | omega
    · -- `y0 = 0`: the point `(1, 0, ..., 0)`
      refine RS.ifF hT (by rw [e4Z, e4Y0]; omega) (RS.ifF hT' (by simp only [addC_mem, e4Y0, e4Z]; omega) ?_)
      refine RS.ins ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by simp [e4YB]; exact hY0L, by simp [e4One]; exact h1⟩ ⟨by omega, ?_, ?_⟩
      · simp only [addC_mem, stepI_store_mem, e4YB, e4One, hM5]
        funext c
        have : φ (a + (c - YB)) ≤ -1000 := φ_le _
        rw [Function.update_apply]
        by_cases hc : YB ≤ c ∧ c ≤ YB + d
        · rw [ite_eq_left hc]
          simp only [nrm, ite_eq_left h0]
          split_ifs <;> (try subst_vars) <;> first | rfl | omega | (rw [m4, hF3]; evl; exact hYz _ hc.1 hc.2)
        · rw [ite_eq_right hc]
          split_ifs <;> (try subst_vars) <;> first | rfl | omega | (simp only [h0, if_true]; exact e4I)
      · exact (((Same'.addC _ _).trans ((Same'.addC _ _).trans (stepI_same (by simp [Plain]) (by simp [NJ])))).trans
          (Same'.addC _ 1)).trans (Same'.addC _ 1)
    · -- `0 < y0`: the copy with the sign `1`
      have hsg' : sg = 1 := by rw [hsg, ite_eq_right (by omega)]
      refine RS.ifT hT (by rw [e4Z, e4Y0]; exact hpos) ?_
      refine (rs_COPYLOOP (Or.inl hsg') hYB0 (by simp [e4I]) (by simp [e4D1]) (by simp [e4One]) (by simp [e4Aa])
        (by simp [e4Sg, hsg']) (by simp [e4YB]) (by simp [e4Z]) (by simp [e4X]) (by simp [e4A]) (by simp [e4V])
        (by simp [e4B]) (by simp [e4C]) hLa (fun j hj => by simpa using hLy4 j hj) hLY hLd h10).mono ?_
      rintro n u' ⟨hn, hu', hsu'⟩
      refine ⟨by omega, ?_, (Same'.addC _ _).trans hsu'⟩
      rw [hu', hM5]
      funext c
      simp only [addC_mem]
      have : φ (a + (c - YB)) ≤ -1000 := φ_le _
      by_cases hc : YB ≤ c ∧ c ≤ YB + d
      · rw [ite_eq_left (by omega), ite_eq_left hc, hφ4, hsg']
        simp only [nrm, ite_eq_right (show ¬ y0 = 0 by omega), ite_eq_right (show ¬ y0 < 0 by omega)]; ring
      · rw [ite_eq_right (by omega), ite_eq_right hc]
        split_ifs <;> first | rfl | omega
  rintro n₅ t₅ ⟨hn₅, m5, hs₅⟩
  refine (rs_seqI (is := copyClr) (t := t₅) ⟨⟨len_scr (by decide) (by decide) h10, l0⟩,
    ⟨len_scr (by decide) (by decide) h10, l0⟩, ⟨len_scr (by decide) (by decide) h10, l0⟩,
    ⟨len_scr (by decide) (by decide) h10, l0⟩, ⟨len_scr (by decide) (by decide) h10, l0⟩,
    ⟨len_scr (by decide) (by decide) h10, l0⟩, ⟨len_scr (by decide) (by decide) h10, l0⟩,
    ⟨len_scr (by decide) (by decide) h10, l0⟩, ⟨len_scr (by decide) (by decide) h10, l0⟩,
    ⟨len_scr (by decide) (by decide) h10, l0⟩, trivial⟩).mono ?_
  rintro n t' ⟨hn, rfl⟩
  refine ⟨by simp only [copyClr, List.length_cons, List.length_nil] at hn hn₁ hn₃ ⊢; omega, ?_,
    s1.trans (hs₂.trans (s3.trans (hs₄.trans (hs₅.trans (runI_same (by simp [copyClr, Plain, NJ]))))))⟩
  funext c
  simp only [copyClr, runI, stepI_const_mem, m5, hM5]
  have : φ (a + (c - YB)) ≤ -1000 := φ_le _
  by_cases hc : YB ≤ c ∧ c ≤ YB + d
  · simp only [Function.update_apply]
    rw [ite_eq_left hc]
    split_ifs <;> first | rfl | omega
  · simp only [Function.update_apply, ite_eq_right hc]
    rw [m4, hF3]
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> first | rfl | omega

end AdversarialBco.UniPoly
