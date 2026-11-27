/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PolyBlk

@[expose] public section

/-!
# UNI-POLY, part 6: `OBSRB`, the clipped reading of `P`

`rs_OBSRB`: `obsR dst prec rng` of `P`: the cell `φ dst` gets `clip q v`, `v` the reading of `p` digits of the
feedback, `p`, `q` the contents of `φ prec`, `φ rng`; the scratch cells back at `0`.
-/

namespace AdversarialBco.UniPoly

open AdversarialBco BitRAM BitRAMO RCmd

variable {d : ℕ} {w : World d} {L : ℕ} {t : State d}

theorem len_two_pow (k : ℕ) : len ((2 : ℤ) ^ k) = k + 1 := by
  unfold len
  rw [Int.natAbs_pow]
  exact Nat.size_pow

set_option maxHeartbeats 4000000 in
/-- `OBSRB dst prec rng`: the cell `φ dst` gets the clipped reading. -/
theorem rs_OBSRB {dst prec rng : ℤ} (hz : t.mem cZ = 0) (hV : t.mem cV = 0) (hOne : t.mem cOne = 0)
    (hP : t.mem cP = 0) (hQ : t.mem cQ = 0) (hI : t.mem cI = 0) (hNP : t.mem cNP = 0)
    (hLd : len dst + 11 ≤ L) (hLp : len prec + 11 ≤ L) (hLr : len rng + 11 ≤ L)
    (hLpv : len (t.mem (φ prec)) ≤ L) (hLrv : len (t.mem (φ rng)) ≤ L)
    (hp : (t.mem (φ prec)).toNat ≤ L) (hq : (t.mem (φ rng)).toNat + 1 ≤ L)
    (hv : len (reading w t (t.mem (φ prec)).toNat) ≤ L) (h10 : 10 ≤ L) :
    RS w L (OBSRB dst prec rng) t (fun n t' => n ≤ 4 * (t.mem (φ rng)).toNat + 24 ∧
      t'.mem = Function.update t.mem (φ dst)
        (clip (t.mem (φ rng)).toNat (reading w t (t.mem (φ prec)).toNat)) ∧ Same' t t') := by
  have h1 : len (1 : ℤ) ≤ L := by rw [len_one]; omega
  have l0 : len (0 : ℤ) ≤ L := by rw [len_zero]; omega
  have hφd : φ dst ≤ -1000 := φ_le _
  have hφp : φ prec ≤ -1000 := φ_le _
  have hφr : φ rng ≤ -1000 := φ_le _
  set r := t.mem (φ rng) with hr
  set q := r.toNat with hqd
  set v := reading w t (t.mem (φ prec)).toNat with hvd
  have hpow : ∀ k ≤ q, len ((2 : ℤ) ^ k) ≤ L := fun k hk => by rw [len_two_pow]; omega
  have hkL : ∀ k ≤ q, len (k : ℤ) ≤ L := fun k hk => by
    have : len (k : ℤ) ≤ len ((2 : ℤ) ^ k) := len_le_of_natAbs_le (by
      rw [Int.natAbs_pow]; simpa using (Nat.lt_two_pow_self (n := k)).le)
    exact this.trans (hpow k hk)
  unfold OBSRB; simp only [seqL]
  -- the reading, `1`, `1`, `r`
  refine RS.seq (rs_seqI (is := [.obs cV (φ prec), .const cOne 1, .const cP 1, .add cQ (φ rng) cZ]) (t := t)
    ⟨⟨len_scr (by decide) (by decide) h10, (len_φ _).trans hLp, hLpv, hp, hv⟩,
     ⟨len_scr (by decide) (by decide) h10, h1⟩, ⟨len_scr (by decide) (by decide) h10, h1⟩,
     ⟨len_scr (by decide) (by decide) h10, (len_φ _).trans hLr, len_scr (by decide) (by decide) h10,
      by evl; exact hLrv, by evl; rw [hz]; exact l0⟩, trivial⟩) ?_
  rintro n₁ t₁ ⟨hn₁, rfl⟩
  set F1 : ℤ → ℤ := Function.update (Function.update (Function.update (Function.update t.mem cV v) cOne 1) cP 1)
    cQ r with hF1
  have m1 : (runI w [.obs cV (φ prec), .const cOne 1, .const cP 1, .add cQ (φ rng) cZ] t).mem = F1 := by
    simp only [runI, stepI_add_mem, stepI_const_mem, stepI_obs_mem]; evl; rw [hz, add_zero]
  have s1 : Same' t (runI w [.obs cV (φ prec), .const cOne 1, .const cP 1, .add cQ (φ rng) cZ] t) :=
    runI_same (by simp [Plain, NJ])
  set G : ℕ → ℤ → ℤ := fun k c => if c = cP then (2 : ℤ) ^ k else if c = cI then (k : ℤ) else F1 c with hG
  have hm0 : (runI w [.obs cV (φ prec), .const cOne 1, .const cP 1, .add cQ (φ rng) cZ] t).mem = G 0 := by
    rw [m1]; funext c; simp only [hG, hF1, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> first | rfl | omega
  -- `2^q` by doubling
  refine RS.seq (Q₁ := fun n u => n ≤ q * 4 + 2 ∧ u.mem = G q ∧ Same' t u)
    (RS.loop (fun k u => k ≤ q ∧ u.mem = G k ∧ Same' t u) q 2 ⟨by omega, hm0, s1⟩ ?_ ?_ ?_) ?_
  · rintro k u ⟨hk, hu, -⟩
    have e1 : u.mem cI = k := by rw [hu, hG]; evl
    have e2 : u.mem cQ = r := by rw [hu, hG, hF1]; evl
    refine ⟨⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, by rw [e1]; exact hkL k hk,
      by rw [e2]; exact hLrv⟩, by rw [e1, e2]; omega⟩
  · rintro k u ⟨hk, hu, hsu⟩ hkq
    have e1 : u.mem cI = k := by rw [hu, hG]; evl
    have e3 : u.mem cP = (2 : ℤ) ^ k := by rw [hu, hG]; evl
    have e4 : u.mem cOne = 1 := by rw [hu, hG, hF1]; evl
    refine (rs_seqI (is := [.add cP cP cP, .add cI cI cOne]) (t := addC u _)
      ⟨⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        len_scr (by decide) (by decide) h10, by rw [addC_mem, e3]; exact hpow k (by omega),
        by rw [addC_mem, e3]; exact hpow k (by omega)⟩,
       ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        len_scr (by decide) (by decide) h10, by evl; rw [e1]; exact hkL k (by omega),
        by evl; rw [e4]; exact h1⟩, trivial⟩).mono ?_
    rintro n u' ⟨hn, rfl⟩
    refine ⟨by simp at hn; omega, by omega, ?_, (hsu.trans ((Same'.addC _ _).trans
      (runI_same (by simp [Plain, NJ])))).trans (Same'.addC _ 1)⟩
    funext c; evl; rw [e3, e1, e4, hu]; simp only [hG, Function.update_apply]
    split_ifs <;> (try subst_vars) <;> first | rfl | omega | (rw [pow_succ]; ring)
  · rintro n u ⟨hk, hu, hsu⟩ hn
    exact ⟨by nlinarith, hu, hsu.trans (Same'.addC _ _)⟩
  rintro n₂ t₂ ⟨hn₂, m2, s2⟩
  have e2P : t₂.mem cP = (2 : ℤ) ^ q := by rw [m2, hG]; evl
  have e2V : t₂.mem cV = v := by rw [m2, hG, hF1]; evl
  have e2Z : t₂.mem cZ = 0 := by rw [m2, hG, hF1]; evl; exact hz
  have hvq : len (min v ((2 : ℤ) ^ q)) ≤ L := by
    rcases min_choice v ((2 : ℤ) ^ q) with h | h <;> rw [h]
    · exact hv
    · exact hpow q le_rfl
  -- `v := min v 2^q`
  refine RS.seq (Q₁ := fun n t₃ => n ≤ 2 ∧ t₃.mem = Function.update (G q) cV (min v ((2 : ℤ) ^ q)) ∧
    Same' t₂ t₃) ?_ ?_
  · have hT : TestOK L cP cV t₂ := ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      by rw [e2P]; exact hpow q le_rfl, by rw [e2V]; exact hv⟩
    by_cases hlt : (2 : ℤ) ^ q < v
    · refine RS.ifT hT (by rw [e2P, e2V]; exact hlt) (RS.ins ⟨len_scr (by decide) (by decide) h10,
        len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by rw [addC_mem, e2P]; exact hpow q le_rfl, by rw [addC_mem, e2Z]; exact l0⟩ ⟨by omega, ?_, ?_⟩)
      · rw [stepI_add_mem, addC_mem, e2P, e2Z, add_zero, m2, min_eq_right hlt.le]
      · exact (Same'.addC _ _).trans (stepI_same (by simp [Plain]) (by simp [NJ]))
    · refine RS.ifF hT (by rw [e2P, e2V]; exact hlt) (RS.skip ⟨by omega, ?_, (Same'.addC _ _).trans
        (Same'.addC _ 1)⟩)
      rw [addC_mem, addC_mem, m2, min_eq_left (by omega)]
      funext c; simp only [Function.update_apply]; split_ifs <;> (try subst_vars) <;> first | rfl | (rw [← m2]; exact e2V.symm)
  rintro n₃ t₃ ⟨hn₃, m3, s3⟩
  have e3P : t₃.mem cP = (2 : ℤ) ^ q := by rw [m3, hG]; evl
  have e3Z : t₃.mem cZ = 0 := by rw [m3, hG, hF1]; evl; exact hz
  -- `NP := -2^q`
  refine RS.seq (RS.ins (Q := fun n t₄ => n = 1 ∧ t₄ = stepI w (.sub cNP cZ cP) t₃)
    ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      len_scr (by decide) (by decide) h10, by rw [e3Z]; exact l0, by rw [e3P]; exact hpow q le_rfl⟩ ⟨rfl, rfl⟩) ?_
  rintro n₄ t₄ ⟨rfl, rfl⟩
  have e4V : (stepI w (.sub cNP cZ cP) t₃).mem cV = min v ((2 : ℤ) ^ q) := by rw [stepI_sub_mem, m3]; evl
  have e4N : (stepI w (.sub cNP cZ cP) t₃).mem cNP = -(2 : ℤ) ^ q := by
    rw [stepI_sub_mem, Function.update_self, e3Z, e3P, zero_sub]
  have e4Z : (stepI w (.sub cNP cZ cP) t₃).mem cZ = 0 := by rw [stepI_sub_mem]; evl; exact e3Z
  set t₄ := stepI w (.sub cNP cZ cP) t₃ with ht₄
  have hLN : len (-(2 : ℤ) ^ q) ≤ L := by rw [len_neg]; exact hpow q le_rfl
  -- `v := max (-2^q) v`
  refine RS.seq (Q₁ := fun n t₅ => n ≤ 2 ∧ t₅.mem = Function.update t₄.mem cV (clip q v) ∧ Same' t₄ t₅) ?_ ?_
  · have hT : TestOK L cV cNP t₄ := ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      by rw [e4V]; exact hvq, by rw [e4N]; exact hLN⟩
    by_cases hlt : min v ((2 : ℤ) ^ q) < -(2 : ℤ) ^ q
    · refine RS.ifT hT (by rw [e4V, e4N]; exact hlt) (RS.ins ⟨len_scr (by decide) (by decide) h10,
        len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
        by rw [addC_mem, e4N]; exact hLN, by rw [addC_mem, e4Z]; exact l0⟩ ⟨by omega, ?_, ?_⟩)
      · rw [stepI_add_mem, addC_mem, e4N, e4Z, add_zero, clip, max_eq_left hlt.le]
      · exact (Same'.addC _ _).trans (stepI_same (by simp [Plain]) (by simp [NJ]))
    · refine RS.ifF hT (by rw [e4V, e4N]; exact hlt) (RS.skip ⟨by omega, ?_, (Same'.addC _ _).trans
        (Same'.addC _ 1)⟩)
      rw [addC_mem, addC_mem, clip, max_eq_right (by omega), ← e4V, Function.update_eq_self]
  rintro n₅ t₅ ⟨hn₅, m5, s5⟩
  have e5V : t₅.mem cV = clip q v := by rw [m5, Function.update_self]
  have e5Z : t₅.mem cZ = 0 := by rw [m5]; evl; exact e4Z
  have hclip : len (clip q v) ≤ L := by
    unfold clip
    rcases max_choice (-(2 : ℤ) ^ q) (min v ((2 : ℤ) ^ q)) with h | h <;> rw [h]
    · exact hLN
    · exact hvq
  refine (rs_seqI (is := [.add (φ dst) cV cZ, .const cV 0, .const cOne 0, .const cP 0, .const cQ 0, .const cI 0,
    .const cNP 0]) (t := t₅)
    ⟨⟨(len_φ _).trans hLd, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
      by rw [e5V]; exact hclip, by rw [e5Z]; exact l0⟩,
     ⟨len_scr (by decide) (by decide) h10, l0⟩, ⟨len_scr (by decide) (by decide) h10, l0⟩,
     ⟨len_scr (by decide) (by decide) h10, l0⟩, ⟨len_scr (by decide) (by decide) h10, l0⟩,
     ⟨len_scr (by decide) (by decide) h10, l0⟩, ⟨len_scr (by decide) (by decide) h10, l0⟩, trivial⟩).mono ?_
  rintro n t' ⟨hn, rfl⟩
  refine ⟨by simp only [List.length_cons, List.length_nil] at hn hn₁; omega, ?_,
    s1.trans (s2.trans (s3.trans ((stepI_same (by simp [Plain]) (by simp [NJ])).trans (s5.trans
      (runI_same (by simp [Plain, NJ])))))).symm.symm⟩
  simp only [runI, stepI_add_mem, stepI_const_mem]
  rw [e5V, e5Z, add_zero, m5, ht₄, stepI_sub_mem, m3, hG, hF1]
  funext c; simp only [Function.update_apply]
  split_ifs <;> (try subst_vars) <;> first | rfl | omega

end AdversarialBco.UniPoly
