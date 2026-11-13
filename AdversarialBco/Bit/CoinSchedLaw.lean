/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.CoinSched
public import AdversarialBco.Bit.BoxMuller
public import AdversarialBco.Bit.GsM
public import AdversarialBco.Bit.Transfer.XCoins
public import AdversarialBco.Conj1Bit.Sanity

@[expose] public section

/-!
# The schedule of Bit/CoinSched.lean meets (W0)

* `w0Law_beta`: for `0 < B`, the digit map `beta d K0 B` is measurable and carries the Gaussian stream to the fair
  coins (`W0Law`, the digit-map lemma).
* `grp_odd`: the groups `grp d K0 B` of the prologue coins lie in the odd terms of the stream.
* `readCoins_blk_u`, `readCoins_blk_w`: the integers BL reads off block `q` of round `t` are the cells
  `⌈2^B u⌉ - 1`, `⌈2^B w⌉ - 1` of the exact pair `(u, w) = bmInv` of the block's two terms of the stream.

Proof of the law: the pairs of the stream of distinct blocks are disjoint (`pairIdx_injective`), so the blocks' pairs
are independent standard Gaussian pairs; on one block `bmInv` carries the pair to two independent uniforms on `(0, 1]`
(`map_bmInv`, from `boxMuller_law2` and `bmInv_bm`), whose `B` digits each are fair independent coins (`dig_cell`,
from `dyadic_cell`); the coins are distinct slots of distinct blocks (`coinIdx_injective`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AdversarialBco.Bit.Sched

open AdversarialBco.Bit.Cpl AdversarialBco.BitRAM AdversarialBco.RealRAM AdversarialBco.Poly.Layer2

/-! ## The schedule -/

theorem posOf_lt {K0 B : ℕ} (hB : 0 < B) (j : ℕ) : posOf K0 B j < 2 * B := by
  unfold posOf
  split_ifs with h
  · exact Nat.mod_lt _ (by omega)
  · exact Nat.mod_lt _ (by omega)

/-- The term of the stream under slot `i` of block `a`. -/
def pairIdx (d : ℕ) (p : (ℕ ⊕ ℕ) × Fin 2) : ℕ := if p.2 = 0 then (pairOf d p.1).1 else (pairOf d p.1).2

theorem pairIdx_injective (d : ℕ) : Function.Injective (pairIdx d) := by
  have hnb : nBlk d = (d + 1) / 2 + 1 := rfl
  have key : ∀ {t t' r r' : ℕ}, r < d + 5 → r' < d + 5 → t * (d + 5) + r = t' * (d + 5) + r' → t = t' ∧ r = r' := by
    intro t t' r r' hr hr' h
    have ht : t = t' := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have : (t + 1) * (d + 5) ≤ t' * (d + 5) := Nat.mul_le_mul_right _ hlt
        nlinarith
      · have : (t' + 1) * (d + 5) ≤ t * (d + 5) := Nat.mul_le_mul_right _ hlt
        nlinarith
    subst ht
    exact ⟨rfl, by omega⟩
  have hinl : ∀ (k : ℕ) (i : Fin 2), pairIdx d (.inl k, i) = 4 * k + 1 + 2 * (i : ℕ) := by
    intro k i
    fin_cases i <;> simp [pairIdx, pairOf]
  have hinr : ∀ (k : ℕ) (i : Fin 2), pairIdx d (.inr k, i) =
      2 * ((k / nBlk d) * (d + 5) +
        (if k % nBlk d + 1 = nBlk d then d + 1 + (i : ℕ) else 2 * (k % nBlk d) + (i : ℕ))) := by
    intro k i
    fin_cases i <;> by_cases hk : k % nBlk d + 1 = nBlk d <;> simp [pairIdx, pairOf, cIdx, hk]
  have hrole : ∀ k (i : Fin 2),
      (if k % nBlk d + 1 = nBlk d then d + 1 + (i : ℕ) else 2 * (k % nBlk d) + (i : ℕ)) < d + 5 := by
    intro k i
    have hq : k % nBlk d < nBlk d := Nat.mod_lt _ (by omega)
    have hi := i.2
    split_ifs <;> omega
  rintro ⟨a, i⟩ ⟨a', i'⟩ h
  have hi := i.2
  have hi' := i'.2
  rcases a with k | k <;> rcases a' with k' | k'
  · rw [hinl, hinl] at h
    have hk : k = k' := by omega
    have hii : (i : ℕ) = i' := by omega
    subst hk
    exact Prod.ext rfl (Fin.ext hii)
  · rw [hinl, hinr] at h
    omega
  · rw [hinr, hinl] at h
    omega
  · rw [hinr, hinr] at h
    obtain ⟨ht, hr⟩ := key (t := k / nBlk d) (t' := k' / nBlk d) (hrole k i) (hrole k' i') (by omega)
    have hq : k % nBlk d < nBlk d := Nat.mod_lt _ (by omega)
    have hq' : k' % nBlk d < nBlk d := Nat.mod_lt _ (by omega)
    have hqq : k % nBlk d = k' % nBlk d ∧ (i : ℕ) = i' := by
      split_ifs at hr with h1 h2 h2 <;> omega
    have hk : k = k' := by
      rw [← Nat.div_add_mod k (nBlk d), ← Nat.div_add_mod k' (nBlk d), ht, hqq.1]
    subst hk
    exact Prod.ext rfl (Fin.ext hqq.2)

/-- The slot of coin `j`: its block and its position in the block. -/
def coinIdx (K0 B : ℕ) (hB : 0 < B) (j : ℕ) : (ℕ ⊕ ℕ) × Fin (2 * B) :=
  (blkOf K0 B j, ⟨posOf K0 B j, posOf_lt hB j⟩)

theorem coinIdx_injective {K0 B : ℕ} (hB : 0 < B) : Function.Injective (coinIdx K0 B hB) := by
  intro x y h
  unfold coinIdx at h
  rcases Prod.ext_iff.mp h with ⟨h_blk, h_fin⟩
  have h_pos : posOf K0 B x = posOf K0 B y := by
    simpa [Fin.ext_iff] using h_fin
  by_cases hx : x < K0
  · by_cases hy : y < K0
    · -- both < K0
      simp [blkOf, hx, hy] at h_blk
      have h_div : x / (2 * B) = y / (2 * B) := by simpa using h_blk
      simp [posOf, hx, hy] at h_pos
      calc
        x = 2 * B * (x / (2 * B)) + x % (2 * B) := (Nat.div_add_mod x (2 * B)).symm
        _ = 2 * B * (y / (2 * B)) + y % (2 * B) := by rw [h_div, h_pos]
        _ = y := Nat.div_add_mod y (2 * B)
    · -- x < K0, y ≥ K0
      simp [blkOf, hx, hy] at h_blk
  · by_cases hy : y < K0
    · -- x ≥ K0, y < K0
      simp [blkOf, hx, hy] at h_blk
    · -- both ≥ K0
      simp [blkOf, posOf, hx, hy] at h_blk h_pos
      have h_div : (x - K0) / (2 * B) = (y - K0) / (2 * B) := by simpa using h_blk
      have hx_sub : x = K0 + (x - K0) := by omega
      have hy_sub : y = K0 + (y - K0) := by omega
      have h_eq : x - K0 = y - K0 := by
        calc
          x - K0 = 2 * B * ((x - K0) / (2 * B)) + (x - K0) % (2 * B) := (Nat.div_add_mod (x - K0) (2 * B)).symm
          _ = 2 * B * ((y - K0) / (2 * B)) + (y - K0) % (2 * B) := by rw [h_div, h_pos]
          _ = y - K0 := Nat.div_add_mod (y - K0) (2 * B)
      rw [hx_sub, hy_sub, h_eq]

theorem beta_local (d K0 B j : ℕ) (x y : ℕ → ℝ) (h : ∀ i ∈ grp d K0 B j, x i = y i) :
    beta d K0 B x j = beta d K0 B y j := by
  unfold beta
  have ha : (pairOf d (blkOf K0 B j)).1 ∈ grp d K0 B j := by
    simp [grp]
  have hb : (pairOf d (blkOf K0 B j)).2 ∈ grp d K0 B j := by
    simp [grp]
  simp [h _ ha, h _ hb]

theorem grp_past (d K0 B t : ℕ) : ∀ j ∈ rdBefore d K0 B t, grp d K0 B j ⊆ idxC d t := by
  intro j hj
  rw [rdBefore, Set.mem_setOf_eq] at hj
  rw [blkStart] at hj
  simp at hj
  -- hj : j < K0 + 2 * B * (t * nBlk d)
  rw [grp]
  intro x hx
  simp [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with (hx | hx)
  · -- hx : x = (pairOf d (blkOf K0 B j)).1
    rw [hx]
    by_cases hjk : j < K0
    · -- j < K0: odd terms from prologue blocks
      rw [blkOf, if_pos hjk]
      rw [pairOf]
      simp
      rw [idxC, Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
      left
      omega
    · -- K0 ≤ j: round blocks
      have hK0j : K0 ≤ j := Nat.le_of_not_lt hjk
      rw [blkOf, if_neg (by omega)]
      set k := (j - K0) / (2 * B) with hkdef
      have hsub : j - K0 < 2 * B * (t * nBlk d) := by omega
      have hpos2B : 0 < 2 * B := by
        by_contra! h
        have hB0 : 2 * B = 0 := by omega
        have hB0' : B = 0 := by omega
        subst hB0'
        simp at hj
        omega
      have hk_lt : k < t * nBlk d := by
        rw [hkdef]
        rw [Nat.div_lt_iff_lt_mul hpos2B]
        -- need: j - K0 < (t * nBlk d) * (2 * B)
        -- which is the same as hsub (up to commutativity)
        simpa [mul_comm, mul_left_comm, mul_assoc] using hsub
      have hnBlk_pos : 0 < nBlk d := by
        dsimp [nBlk]
        omega
      set t' := k / nBlk d with ht'def
      have ht'_lt_t : t' < t := by
        rw [ht'def]
        rw [Nat.div_lt_iff_lt_mul hnBlk_pos]
        exact hk_lt
      rw [pairOf]
      split
      · -- case: k % nBlk d + 1 = nBlk d
        -- goal: (cIdx d (k / nBlk d) (d + 1), cIdx d (k / nBlk d) (d + 2)).1 ∈ idxC d t
        simp
        -- goal: cIdx d (k / nBlk d) (d + 1) ∈ idxC d t
        rw [idxC, Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
        right
        dsimp [cIdx]
        have hc : d + 1 < d + 5 := by omega
        nlinarith
      · -- case: k % nBlk d + 1 ≠ nBlk d
        -- goal: (cIdx d (k / nBlk d) (2 * (k % nBlk d)), cIdx d (k / nBlk d) (2 * (k % nBlk d) + 1)).1 ∈ idxC d t
        simp
        -- goal: cIdx d (k / nBlk d) (2 * (k % nBlk d)) ∈ idxC d t
        rw [idxC, Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
        right
        dsimp [cIdx]
        -- need: 2 * ((k / nBlk d) * (d + 5) + 2 * (k % nBlk d)) < 2 * (t * (d + 5))
        -- We know k % nBlk d < nBlk d
        have hmod : k % nBlk d < nBlk d := Nat.mod_lt _ hnBlk_pos
        -- So 2*(k%nBlk d) + 1 ≤ 2*nBlk d - 1 < d + 5
        have hc : 2 * (k % nBlk d) < d + 5 := by
          dsimp [nBlk] at hmod ⊢
          omega
        nlinarith
  · -- hx : x = (pairOf d (blkOf K0 B j)).2
    rw [hx]
    by_cases hjk : j < K0
    · -- j < K0: odd terms from prologue blocks
      rw [blkOf, if_pos hjk]
      rw [pairOf]
      simp
      rw [idxC, Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
      left
      omega
    · -- K0 ≤ j: round blocks
      have hK0j : K0 ≤ j := Nat.le_of_not_lt hjk
      rw [blkOf, if_neg (by omega)]
      set k := (j - K0) / (2 * B) with hkdef
      have hsub : j - K0 < 2 * B * (t * nBlk d) := by omega
      have hpos2B : 0 < 2 * B := by
        by_contra! h
        have hB0 : 2 * B = 0 := by omega
        have hB0' : B = 0 := by omega
        subst hB0'
        simp at hj
        omega
      have hk_lt : k < t * nBlk d := by
        rw [hkdef]
        rw [Nat.div_lt_iff_lt_mul hpos2B]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hsub
      have hnBlk_pos : 0 < nBlk d := by
        dsimp [nBlk]
        omega
      set t' := k / nBlk d with ht'def
      have ht'_lt_t : t' < t := by
        rw [ht'def]
        rw [Nat.div_lt_iff_lt_mul hnBlk_pos]
        exact hk_lt
      rw [pairOf]
      split
      · -- case: k % nBlk d + 1 = nBlk d
        -- goal: (cIdx d (k / nBlk d) (d + 1), cIdx d (k / nBlk d) (d + 2)).2 ∈ idxC d t
        simp
        -- goal: cIdx d (k / nBlk d) (d + 2) ∈ idxC d t
        rw [idxC, Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
        right
        dsimp [cIdx]
        have hc : d + 2 < d + 5 := by omega
        nlinarith
      · -- case: k % nBlk d + 1 ≠ nBlk d
        -- goal: (cIdx d (k / nBlk d) (2 * (k % nBlk d)), cIdx d (k / nBlk d) (2 * (k % nBlk d) + 1)).2 ∈ idxC d t
        simp
        -- goal: cIdx d (k / nBlk d) (2 * (k % nBlk d) + 1) ∈ idxC d t
        rw [idxC, Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
        right
        dsimp [cIdx]
        have hmod : k % nBlk d < nBlk d := Nat.mod_lt _ hnBlk_pos
        have hc : 2 * (k % nBlk d) + 1 < d + 5 := by
          dsimp [nBlk] at hmod ⊢
          omega
        nlinarith

/-- The coins of the prologue read odd terms of the stream only. -/
theorem grp_odd {d K0 B j : ℕ} (hj : j < K0) : grp d K0 B j ⊆ {i | i % 2 = 1} := by
  have hblk : blkOf K0 B j = .inl (j / (2 * B)) := by
    simp [blkOf, hj]
  rw [grp, hblk]
  simp [pairOf, Set.insert_subset_iff, Set.singleton_subset_iff]
  have h_even : ∀ k : ℕ, (4 * k) % 2 = 0 := by
    intro k
    rw [Nat.mul_mod]
    norm_num
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mod, h_even (j / (2 * B))]
  · rw [Nat.add_mod, h_even (j / (2 * B))]

/-! ## The integers read off a block -/

theorem cellIdx_lt {B : ℕ} {v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1) : cellIdx B v < 2 ^ B := by
  have h2pos : 0 < (2 : ℝ) ^ B := pow_pos (by norm_num) B
  have hpos : 0 < (2 : ℝ) ^ B * v := mul_pos h2pos hv0
  have hle : (2 : ℝ) ^ B * v ≤ (2 : ℝ) ^ B := by
    nlinarith
  have hceil_le : (⌈(2 : ℝ) ^ B * v⌉ : ℤ) ≤ (2 ^ B : ℤ) := by
    rw [Int.ceil_le]
    push_cast
    exact hle
  have hceil_pos : 0 < ⌈(2 : ℝ) ^ B * v⌉ := by
    rw [Int.ceil_pos]
    exact hpos
  have h_sub_nonneg : 0 ≤ ⌈(2 : ℝ) ^ B * v⌉ - 1 := by
    omega
  have h_sub_lt : ⌈(2 : ℝ) ^ B * v⌉ - 1 < (2 ^ B : ℤ) := by
    omega
  rw [cellIdx]
  rw [Int.toNat_lt h_sub_nonneg]
  exact h_sub_lt

theorem bmInv_fst_mem (p : ℝ × ℝ) : (bmInv p).1 ∈ Set.Ioc 0 1 := by
  dsimp [bmInv]
  have hpos : 0 < Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) := Real.exp_pos _
  have hle : Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg p.1, sq_nonneg p.2]
  exact ⟨hpos, hle⟩

theorem bmInv_snd_mem (p : ℝ × ℝ) : (bmInv p).2 ∈ Set.Ioc 0 1 := by
  have ha_low : -Real.pi < Complex.arg ⟨p.1, p.2⟩ := Complex.neg_pi_lt_arg _
  have ha_high : Complex.arg ⟨p.1, p.2⟩ ≤ Real.pi := Complex.arg_le_pi _
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h2pi_pos : 0 < 2 * Real.pi := by nlinarith
  dsimp [bmInv, bmW]
  split
  · rename_i h
    have ha_pos : 0 < Complex.arg ⟨p.1, p.2⟩ := h
    refine ⟨div_pos ha_pos h2pi_pos, ?_⟩
    have hdiv_le : Complex.arg ⟨p.1, p.2⟩ / (2 * Real.pi) ≤ Real.pi / (2 * Real.pi) :=
      div_le_div_of_nonneg_right ha_high (by nlinarith)
    have hhalf : Real.pi / (2 * Real.pi) = (1 : ℝ)/2 := by
      field_simp [ne_of_gt Real.pi_pos]
    have hhalf_le_one : (1 : ℝ)/2 ≤ 1 := by norm_num
    linarith
  · rename_i h
    have ha_nonpos : Complex.arg ⟨p.1, p.2⟩ ≤ 0 := by linarith
    refine ⟨?_, ?_⟩
    · have hdiv_gt : -1 < Complex.arg ⟨p.1, p.2⟩ / (2 * Real.pi) := by
        apply (lt_div_iff₀ h2pi_pos).mpr
        nlinarith
      linarith
    · have hdiv_nonpos : Complex.arg ⟨p.1, p.2⟩ / (2 * Real.pi) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg ha_nonpos (by nlinarith)
      linarith

theorem blkOf_posOf_blkStart {d K0 B t q s : ℕ} (hs : s < 2 * B) :
    blkOf K0 B (blkStart d K0 B t q + s) = .inr (t * nBlk d + q) ∧ posOf K0 B (blkStart d K0 B t q + s) = s := by
  unfold blkStart blkOf posOf
  have hle : ¬ (K0 + 2 * B * (t * nBlk d + q) + s < K0) := by omega
  have hsub : (K0 + 2 * B * (t * nBlk d + q) + s) - K0 = 2 * B * (t * nBlk d + q) + s := by omega
  have hpos : 0 < 2 * B := by omega
  have hdiv : (2 * B * (t * nBlk d + q) + s) / (2 * B) = t * nBlk d + q := by
    calc
      (2 * B * (t * nBlk d + q) + s) / (2 * B) = (s + (t * nBlk d + q) * (2 * B)) / (2 * B) := by ring
      _ = s / (2 * B) + (t * nBlk d + q) := by rw [Nat.add_mul_div_right _ _ hpos]
      _ = 0 + (t * nBlk d + q) := by rw [Nat.div_eq_of_lt hs]
      _ = t * nBlk d + q := by simp
  have hmod : (2 * B * (t * nBlk d + q) + s) % (2 * B) = s := by
    calc
      (2 * B * (t * nBlk d + q) + s) % (2 * B) = ((2 * B * (t * nBlk d + q)) % (2 * B) + s % (2 * B)) % (2 * B) := by rw [Nat.add_mod]
      _ = (0 + s % (2 * B)) % (2 * B) := by rw [Nat.mul_mod_right]
      _ = (s % (2 * B)) % (2 * B) := by simp
      _ = s % (2 * B) := by rw [Nat.mod_mod]
      _ = s := by rw [Nat.mod_eq_of_lt hs]
  simp [hle, hsub, hdiv, hmod]

/-- The pair of terms of the stream of the round block `k` (block `q` of round `t` is `k = t * nBlk d + q`). -/
def blkPair (d : ℕ) (x : ℕ → ℝ) (k : ℕ) : ℝ × ℝ := (x (pairOf d (.inr k)).1, x (pairOf d (.inr k)).2)

/-- The first `B` coins of block `q` of round `t` read the cell `⌈2^B u⌉ - 1` of `u`. -/
theorem readCoins_blk_u (d K0 B t q : ℕ) (x : ℕ → ℝ) :
    readCoins (beta d K0 B x) (blkStart d K0 B t q) B = (cellIdx B (bmInv (blkPair d x (t * nBlk d + q))).1 : ℤ) := by
  set k := t * nBlk d + q with hk
  set v := cellIdx B (bmInv (blkPair d x k)).1 with hv
  have hv_lt : v < 2 ^ B := by
    have hmem := bmInv_fst_mem (blkPair d x k)
    exact cellIdx_lt hmem.1 hmem.2
  have h := (AdversarialBco.Bit.Transfer.readCoins_eq_iff (beta d K0 B x) (blkStart d K0 B t q) B v hv_lt).mpr ?_
  · simpa [hk, hv] using h
  · intro i hi
    have hi2 : i < 2 * B := by
      have : B ≤ 2 * B := by omega
      exact Nat.lt_of_lt_of_le hi this
    rcases blkOf_posOf_blkStart hi2 with ⟨hblk, hpos⟩
    unfold beta
    rw [hblk, hpos, ← hk]
    unfold blkCoin
    simp [hi, dig, v, blkPair]

/-- The last `B` coins of block `q` of round `t` read the cell `⌈2^B w⌉ - 1` of `w`. -/
theorem readCoins_blk_w (d K0 B t q : ℕ) (x : ℕ → ℝ) :
    readCoins (beta d K0 B x) (blkStart d K0 B t q + B) B =
      (cellIdx B (bmInv (blkPair d x (t * nBlk d + q))).2 : ℤ) := by
  set k := t * nBlk d + q with hk
  have hcell_lt : cellIdx B (bmInv (blkPair d x k)).2 < 2 ^ B := by
    apply cellIdx_lt
    · have hmem := bmInv_snd_mem (blkPair d x k)
      exact hmem.1
    · have hmem := bmInv_snd_mem (blkPair d x k)
      exact hmem.2
  rw [Bit.Transfer.readCoins_eq_iff (beta d K0 B x) (blkStart d K0 B t q + B) B
    (cellIdx B (bmInv (blkPair d x k)).2) hcell_lt]
  intro i hi
  have hsum_lt : B + i < 2 * B := by omega
  have hblk := blkOf_posOf_blkStart (d := d) (K0 := K0) (B := B) (t := t) (q := q) (s := B + i) hsum_lt
  rcases hblk with ⟨hblk_of, hpos_of⟩
  have hadd : blkStart d K0 B t q + B + i = blkStart d K0 B t q + (B + i) := by omega
  rw [hadd]
  unfold beta
  rw [hblk_of, hpos_of]
  unfold blkCoin
  have h_not_lt : ¬ (B + i < B) := by omega
  simp [h_not_lt]
  rw [← hk]
  unfold dig blkPair
  rfl

/-- The cell index as an integer: `⌈2^B v⌉ - 1` for `v ∈ (0, 1]`. -/
theorem cellIdx_eq {B : ℕ} {v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1) : (cellIdx B v : ℤ) = ⌈(2 : ℝ) ^ B * v⌉ - 1 := by
  unfold cellIdx
  have hpos : 0 < (2 : ℝ) ^ B * v := by
    have hpow : 0 < (2 : ℝ) ^ B := pow_pos (by norm_num) B
    exact mul_pos hpow hv0
  have hceil : 1 ≤ ⌈(2 : ℝ) ^ B * v⌉ := by
    rw [Int.one_le_ceil_iff]
    exact hpos
  have h_nonneg : 0 ≤ ⌈(2 : ℝ) ^ B * v⌉ - 1 := by
    linarith
  rw [Int.toNat_of_nonneg h_nonneg]

/-! ## Measurability -/

theorem measurable_cellIdx (B : ℕ) : Measurable (cellIdx B) := by
  have h_ceil : Measurable (fun (v : ℝ) => (⌈(2 : ℝ) ^ B * v⌉ : ℤ)) :=
    Measurable.ceil (measurable_const.mul measurable_id)
  have h_sub : Measurable (fun (z : ℤ) => ((z - 1).toNat : ℕ)) :=
    measurable_of_countable _
  have h_comp : Measurable (fun (v : ℝ) => ((⌈(2 : ℝ) ^ B * v⌉ : ℤ) - 1).toNat) :=
    h_sub.comp h_ceil
  exact h_comp

theorem measurable_bmInv : Measurable bmInv := by
  unfold bmInv
  refine Measurable.prodMk ?_ ?_
  · -- first component: Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2)
    refine Real.measurable_exp.comp ?_
    refine (((measurable_fst.pow (measurable_const (a := (2 : ℕ)))).add
      (measurable_snd.pow (measurable_const (a := (2 : ℕ))))).neg.div_const (2 : ℝ))
  · -- second component: bmW p.1 p.2
    dsimp [bmW]
    refine Measurable.ite ?_ ?_ ?_
    · -- the condition 0 < Complex.arg ⟨p.1, p.2⟩
      refine measurableSet_lt measurable_const
        (Complex.measurable_arg.comp Complex.measurableEquivRealProd.symm.measurable)
    · -- then branch: Complex.arg ⟨p.1, p.2⟩ / (2 * Real.pi)
      refine (Complex.measurable_arg.comp Complex.measurableEquivRealProd.symm.measurable).div_const (2 * Real.pi)
    · -- else branch: Complex.arg ⟨p.1, p.2⟩ / (2 * Real.pi) + 1
      refine ((Complex.measurable_arg.comp Complex.measurableEquivRealProd.symm.measurable).div_const (2 * Real.pi)).add_const 1

theorem measurable_blkCoin (B s : ℕ) : Measurable fun p : ℝ × ℝ => blkCoin B p s := by
  by_cases hs : s < B
  · simp [blkCoin, hs]
    have h_fst_bmInv : Measurable (fun p : ℝ × ℝ => (bmInv p).1) :=
      measurable_fst.comp measurable_bmInv
    have h_cellIdx_fst : Measurable (cellIdx B ∘ (fun p : ℝ × ℝ => (bmInv p).1)) :=
      (measurable_cellIdx B).comp h_fst_bmInv
    have h_testBit : Measurable (fun n : ℕ => n.testBit (B - 1 - s)) :=
      Measurable.of_discrete
    exact h_testBit.comp h_cellIdx_fst
  · simp [blkCoin, hs]
    have h_snd_bmInv : Measurable (fun p : ℝ × ℝ => (bmInv p).2) :=
      measurable_snd.comp measurable_bmInv
    have h_cellIdx_snd : Measurable (cellIdx B ∘ (fun p : ℝ × ℝ => (bmInv p).2)) :=
      (measurable_cellIdx B).comp h_snd_bmInv
    have h_testBit : Measurable (fun n : ℕ => n.testBit (B - 1 - (s - B))) :=
      Measurable.of_discrete
    exact h_testBit.comp h_cellIdx_snd

theorem measurable_beta (d K0 B : ℕ) : Measurable (beta d K0 B) := by
  refine measurable_pi_iff.mpr fun j => ?_
  unfold beta
  have h_inner : Measurable (fun x : ℕ → ℝ => (x (pairOf d (blkOf K0 B j)).1, x (pairOf d (blkOf K0 B j)).2)) :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have h_outer : Measurable (fun p : ℝ × ℝ => blkCoin B p (posOf K0 B j)) :=
    measurable_blkCoin B (posOf K0 B j)
  exact h_outer.comp h_inner

/-! ## The law of one block -/

theorem bmInv_fst_bm {u : ℝ} (w : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) : (bmInv (bm (u, w))).1 = u := by
  simp [bmInv, bm]
  have hlog : Real.log u ≤ 0 := Real.log_nonpos hu0.le hu1
  have hnonneg : 0 ≤ -(2 * Real.log u) := by linarith
  have hsq : (Real.sqrt (-(2 * Real.log u))) ^ 2 = -(2 * Real.log u) := Real.sq_sqrt hnonneg
  calc
    Real.exp ((-(Real.sqrt (-(2 * Real.log u)) * Real.sin (2 * Real.pi * w)) ^ 2 +
      -(Real.sqrt (-(2 * Real.log u)) * Real.cos (2 * Real.pi * w)) ^ 2) / 2)
        = Real.exp ((-(Real.sqrt (-(2 * Real.log u))) ^ 2 * ((Real.sin (2 * Real.pi * w)) ^ 2 + (Real.cos (2 * Real.pi * w)) ^ 2)) / 2) := by
      ring
    _ = Real.exp ((-(Real.sqrt (-(2 * Real.log u))) ^ 2 * 1) / 2) := by simp [Real.sin_sq_add_cos_sq]
    _ = Real.exp ((-(Real.sqrt (-(2 * Real.log u))) ^ 2) / 2) := by ring
    _ = Real.exp ((-(-(2 * Real.log u))) / 2) := by rw [hsq]
    _ = Real.exp (Real.log u) := by ring
    _ = u := Real.exp_log hu0

theorem bmW_polar {r θ : ℝ} (hr : 0 < r) (hθ0 : 0 < θ) (hθ1 : θ ≤ 2 * Real.pi) :
    bmW (r * Real.cos θ) (r * Real.sin θ) = θ / (2 * Real.pi) := by
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  rw [bmW]
  -- Complex.arg ⟨r cos θ, r sin θ⟩ = Complex.arg ⟨cos θ, sin θ⟩ by arg_real_mul
  have h_arg_mul : Complex.arg ⟨r * Real.cos θ, r * Real.sin θ⟩ = Complex.arg ⟨Real.cos θ, Real.sin θ⟩ := by
    have htemp : (⟨r * Real.cos θ, r * Real.sin θ⟩ : ℂ) = (r : ℂ) * ⟨Real.cos θ, Real.sin θ⟩ := by
      apply Complex.ext <;> simp
    simpa [htemp] using Complex.arg_real_mul ⟨Real.cos θ, Real.sin θ⟩ hr
  rw [h_arg_mul]
  -- Complex.arg ⟨cos θ, sin θ⟩ = toIocMod (2π) (-π) θ
  have h_arg_cos_sin : Complex.arg ⟨Real.cos θ, Real.sin θ⟩ = toIocMod Real.two_pi_pos (-Real.pi) θ := by
    have htemp : (⟨Real.cos θ, Real.sin θ⟩ : ℂ) = Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re]
    simpa [htemp] using Complex.arg_cos_add_sin_mul_I_eq_toIocMod θ
  rw [h_arg_cos_sin]
  by_cases hθπ : θ ≤ Real.pi
  · -- Case θ ≤ π: then θ ∈ Ioc (-π) π, so toIocMod = θ > 0
    have h_toIocMod : toIocMod Real.two_pi_pos (-Real.pi) θ = θ := by
      apply (toIocMod_eq_self Real.two_pi_pos).mpr
      constructor <;> linarith
    rw [h_toIocMod]
    simp [hθ0]
  · -- Case π < θ ≤ 2π: then θ - 2π ∈ Ioc (-π) 0, so toIocMod = θ - 2π ≤ 0
    have hθ_gt_pi : Real.pi < θ := by linarith
    have h_toIocMod : toIocMod Real.two_pi_pos (-Real.pi) θ = θ - 2 * Real.pi := by
      apply (toIocMod_eq_iff Real.two_pi_pos).mpr
      constructor
      · -- θ - 2π ∈ Ioc (-π) π
        constructor <;> linarith
      · -- ∃ z, θ = (θ - 2π) + z • (2π)
        use 1
        ring
    rw [h_toIocMod]
    have h_nonpos : ¬ 0 < θ - 2 * Real.pi := by linarith
    simp [h_nonpos]
    field_simp [hπ_pos.ne']
    ring

theorem bmInv_bm {u w : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (hw0 : 0 < w) (hw1 : w ≤ 1) : bmInv (bm (u, w)) = (u, w) := by
  ext
  · exact bmInv_fst_bm w hu0 hu1.le
  · have hr : 0 < Real.sqrt (-2 * Real.log u) := by
      refine Real.sqrt_pos.mpr ?_
      have hlog : Real.log u < 0 := Real.log_neg hu0 hu1
      nlinarith
    have hθ0 : 0 < 2 * Real.pi * w := by
      positivity
    have hθ1 : 2 * Real.pi * w ≤ 2 * Real.pi := by
      have := mul_le_mul_of_nonneg_left hw1 (by positivity : 0 ≤ 2 * Real.pi)
      simpa [mul_comm] using this
    calc
      (bmInv (bm (u, w))).2 = bmW (Real.sqrt (-2 * Real.log u) * Real.cos (2 * Real.pi * w))
          (Real.sqrt (-2 * Real.log u) * Real.sin (2 * Real.pi * w)) := by
        simp [bmInv, bm]
      _ = (2 * Real.pi * w) / (2 * Real.pi) := bmW_polar hr hθ0 hθ1
      _ = w := by field_simp

/-- LAW-4: `bmInv` carries a pair of independent standard Gaussians to two independent uniforms
on `(0, 1]`. -/
theorem map_bmInv :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map bmInv =
      (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  set U := volume.restrict (Set.Ioc (0 : ℝ) 1) with hU
  have h_box : (U.prod U).map bm = (gaussianReal 0 1).prod (gaussianReal 0 1) := by
    unfold bm
    simpa [U] using Bit.boxMuller_law2
  have h_meas_bm : Measurable bm := by
    unfold bm
    measurability
  have h_meas_bmInv : Measurable bmInv := measurable_bmInv
  have h_ae : bmInv ∘ bm =ᵐ[U.prod U] id := by
    have h_mem1 : ∀ᵐ x ∂U, x ∈ Set.Ioc (0 : ℝ) 1 :=
      MeasureTheory.ae_restrict_mem measurableSet_Ioc
    have h_mem2 : ∀ᵐ x ∂U, x ∈ Set.Ioc (0 : ℝ) 1 :=
      MeasureTheory.ae_restrict_mem measurableSet_Ioc
    have h_ne_one : ∀ᵐ x ∂U, x ≠ (1 : ℝ) := by
      have : MeasureTheory.NullSingletonClass U := by infer_instance
      exact MeasureTheory.Measure.ae_ne U (1 : ℝ)
    have h_ioo : ∀ᵐ x ∂U, x ∈ Set.Ioo (0 : ℝ) 1 := by
      filter_upwards [h_mem1, h_ne_one] with x hx hx_ne
      exact ⟨hx.1, lt_of_le_of_ne hx.2 hx_ne⟩
    have h_meas_ioo : MeasurableSet {p : ℝ × ℝ | p.1 ∈ Set.Ioo (0 : ℝ) 1} :=
      measurable_fst measurableSet_Ioo
    have h_meas_ioc : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Set.Ioc (0 : ℝ) 1} :=
      measurable_snd measurableSet_Ioc
    have h1 : ∀ᵐ p ∂(U.prod U), p.1 ∈ Set.Ioo (0 : ℝ) 1 := by
      rw [MeasureTheory.Measure.ae_prod_iff_ae_ae h_meas_ioo]
      refine h_ioo.mono (fun x hx => ?_)
      exact MeasureTheory.ae_of_all U (fun _ => hx)
    have h2 : ∀ᵐ p ∂(U.prod U), p.2 ∈ Set.Ioc (0 : ℝ) 1 := by
      rw [MeasureTheory.Measure.ae_prod_iff_ae_ae h_meas_ioc]
      exact MeasureTheory.ae_of_all U (fun x => h_mem2)
    filter_upwards [h1, h2] with p hp1 hp2
    exact bmInv_bm hp1.1 hp1.2 hp2.1 hp2.2
  calc
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map bmInv
        = ((U.prod U).map bm).map bmInv := by rw [← h_box]
    _ = (U.prod U).map (bmInv ∘ bm) := by rw [MeasureTheory.Measure.map_map h_meas_bmInv h_meas_bm]
    _ = (U.prod U).map id := by rw [MeasureTheory.Measure.map_congr h_ae]
    _ = U.prod U := by rw [MeasureTheory.Measure.map_id]
    _ = (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1)) := rfl

/-- The first `B` digits of a uniform on `(0, 1]` take any given values with probability `2^{-B}`. -/
theorem dig_cell (B : ℕ) (c : ℕ → Bool) :
    volume.restrict (Set.Ioc (0 : ℝ) 1) {u | ∀ i < B, dig B u i = c i} = ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ))) := by
  -- Get n0 < 2^B such that n0.testBit k = c (B - 1 - k) for all k < B
  obtain ⟨n0, hn0_lt, hn0_bits⟩ := Bit.Aux_gsm_digits_law.exists_nat_with_bits B (fun k => c (B - 1 - k))
  have hn0_le : (n0 : ℤ) + 1 ≤ (2 : ℤ) ^ B := by
    have h : (n0 : ℤ) < (2 : ℤ) ^ B := by
      have htemp : (n0 : ℤ) < ((2 ^ B : ℕ) : ℤ) := Nat.cast_lt.mpr hn0_lt
      simpa [Nat.cast_pow] using htemp
    omega
  have h1_le : (1 : ℤ) ≤ (n0 : ℤ) + 1 := by omega
  have h_set_eq : {u | ∀ i < B, dig B u i = c i} ∩ Set.Ioc (0 : ℝ) 1 =
      {u | u ∈ Set.Ioc (0 : ℝ) 1 ∧ ⌈(2 : ℝ) ^ B * u⌉ = (n0 : ℤ) + 1} := by
    ext u
    constructor
    · intro ⟨h_dig, h_mem⟩
      have hu_pos : 0 < u := (Set.mem_Ioc.mp h_mem).1
      have hu_le_one : u ≤ 1 := (Set.mem_Ioc.mp h_mem).2
      have h_cell_lt : cellIdx B u < 2 ^ B := cellIdx_lt hu_pos hu_le_one
      -- For each i < B, dig B u i = (cellIdx B u).testBit (B - 1 - i)
      have h_dig_eq : ∀ i < B, (cellIdx B u).testBit (B - 1 - i) = c i := by
        intro i hi
        simpa [dig] using h_dig i hi
      -- Convert to: for all k < B, (cellIdx B u).testBit k = n0.testBit k
      have h_bits_eq : ∀ k < B, (cellIdx B u).testBit k = n0.testBit k := by
        intro k hk
        -- Set i = B - 1 - k, then B - 1 - i = k (since k < B)
        have hk_le : k ≤ B - 1 := by omega
        have hi : B - 1 - k < B := by omega
        have h_eq : B - 1 - (B - 1 - k) = k := by omega
        -- From hn0_bits: n0.testBit k = c (B - 1 - k)
        -- From h_dig_eq: (cellIdx B u).testBit (B - 1 - (B - 1 - k)) = c (B - 1 - k)
        -- i.e., (cellIdx B u).testBit k = c (B - 1 - k)
        calc
          (cellIdx B u).testBit k = (cellIdx B u).testBit (B - 1 - (B - 1 - k)) := by rw [h_eq]
          _ = c (B - 1 - k) := h_dig_eq (B - 1 - k) hi
          _ = n0.testBit k := (hn0_bits k hk).symm
      have h_cell_eq_n0 : cellIdx B u = n0 :=
        Bit.Aux_gsm_digits_law.eq_of_testBit_eq_of_lt_two_pow h_cell_lt hn0_lt h_bits_eq
      have h_cellIdx_eq : (cellIdx B u : ℤ) = ⌈(2 : ℝ) ^ B * u⌉ - 1 := cellIdx_eq hu_pos hu_le_one
      have h_ceil_eq : ⌈(2 : ℝ) ^ B * u⌉ = (n0 : ℤ) + 1 := by
        have h_temp : ⌈(2 : ℝ) ^ B * u⌉ = (cellIdx B u : ℤ) + 1 := by
          linarith
        rw [h_temp, h_cell_eq_n0]
      exact ⟨h_mem, h_ceil_eq⟩
    · intro ⟨h_mem, h_ceil⟩
      have hu_pos : 0 < u := (Set.mem_Ioc.mp h_mem).1
      have hu_le_one : u ≤ 1 := (Set.mem_Ioc.mp h_mem).2
      have h_cellIdx_eq : (cellIdx B u : ℤ) = ⌈(2 : ℝ) ^ B * u⌉ - 1 := cellIdx_eq hu_pos hu_le_one
      have h_cell_eq_n0 : (cellIdx B u : ℤ) = (n0 : ℤ) := by
        rw [h_cellIdx_eq, h_ceil]
        omega
      -- Since both are < 2^B, we can lift to ℕ
      have h_cell_lt : cellIdx B u < 2 ^ B := cellIdx_lt hu_pos hu_le_one
      have h_cell_eq_n0_nat : cellIdx B u = n0 :=
        Nat.cast_inj.mp h_cell_eq_n0
      have h_dig : ∀ i < B, dig B u i = c i := by
        intro i hi
        rw [dig, h_cell_eq_n0_nat]
        -- Need: n0.testBit (B - 1 - i) = c i
        -- From hn0_bits: n0.testBit k = c (B - 1 - k) for k < B
        -- Set k = B - 1 - i. Need to show k < B and B - 1 - k = i.
        have hk_lt : B - 1 - i < B := by omega
        have h_eq : B - 1 - (B - 1 - i) = i := by omega
        calc
          n0.testBit (B - 1 - i) = c (B - 1 - (B - 1 - i)) := hn0_bits (B - 1 - i) hk_lt
          _ = c i := by rw [h_eq]
      exact ⟨h_dig, h_mem⟩
  calc
    volume.restrict (Set.Ioc (0 : ℝ) 1) {u | ∀ i < B, dig B u i = c i}
        = volume ({u | ∀ i < B, dig B u i = c i} ∩ Set.Ioc (0 : ℝ) 1) := by
      rw [Measure.restrict_apply' measurableSet_Ioc]
    _ = volume {u | u ∈ Set.Ioc (0 : ℝ) 1 ∧ ⌈(2 : ℝ) ^ B * u⌉ = (n0 : ℤ) + 1} := by rw [h_set_eq]
    _ = ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ))) := by
      rw [Bit.dyadic_cell B ((n0 : ℤ) + 1) h1_le hn0_le]

theorem uw_law (B : ℕ) :
    ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))).map
        (fun p (s : Fin (2 * B)) => if (s : ℕ) < B then dig B p.1 s else dig B p.2 (s - B)) =
      Measure.pi fun _ : Fin (2 * B) => coinLaw := by
  apply MeasureTheory.Measure.ext_of_singleton; intro c
  -- Right side: Measure.pi (fun _ => coinLaw) {c} = ∏ i, coinLaw {c i} = (2⁻¹)^(2B)
  rw [MeasureTheory.Measure.pi_singleton]
  -- Now: ∏ i : Fin (2*B), coinLaw {c i} = Measure.map ... {c}
  -- coinLaw {c i} = 2⁻¹
  have h_coin_singleton : ∀ (b : Bool), coinLaw {b} = (2⁻¹ : ENNReal) := by
    intro b; cases b <;> simp [coinLaw]
  simp_rw [h_coin_singleton]
  -- Now: ∏ i : Fin (2*B), (2⁻¹ : ENNReal) = Measure.map ... {c}
  -- ∏ i : Fin (2*B), (2⁻¹ : ENNReal) = (2⁻¹)^(2B)
  rw [Finset.prod_const, Finset.card_fin]
  -- Now: (2⁻¹ : ENNReal)^(2*B) = Measure.map ... {c}
  -- Left side: compute Measure.map_apply
  -- Need measurability of the map and that {c} is measurable
  have h_meas : Measurable (fun (p : ℝ × ℝ) (s : Fin (2 * B)) =>
    if (s : ℕ) < B then dig B p.1 s else dig B p.2 (s - B)) := by
    rw [measurable_pi_iff]
    intro s
    -- For each s, we need measurability of fun p => ...
    refine Measurable.ite ?_ ?_ ?_
    · -- The set {p | (s:ℕ) < B} is either whole space or empty, both measurable
      by_cases h : (s : ℕ) < B
      · -- then the set is the whole space
        have : {p : ℝ × ℝ | (s : ℕ) < B} = Set.univ := by
          ext p; simp [h]
        rw [this]
        exact MeasurableSet.univ
      · -- then the set is empty
        have : {p : ℝ × ℝ | (s : ℕ) < B} = ∅ := by
          ext p; simp [h]
        rw [this]
        exact MeasurableSet.empty
    · -- dig B p.1 s is measurable in p
      -- (fun n : ℕ => n.testBit (B - 1 - s)) is measurable (discrete sigma-algebra)
      -- cellIdx B is measurable, composed with fst
      have h_testbit : Measurable (fun (n : ℕ) => n.testBit (B - 1 - s)) :=
        Measurable.of_discrete (f := fun (n : ℕ) => n.testBit (B - 1 - s))
      exact h_testbit.comp ((measurable_cellIdx B).comp measurable_fst)
    · -- dig B p.2 (s - B) is measurable in p
      have h_testbit : Measurable (fun (n : ℕ) => n.testBit (B - 1 - (s - B))) :=
        Measurable.of_discrete (f := fun (n : ℕ) => n.testBit (B - 1 - (s - B)))
      exact h_testbit.comp ((measurable_cellIdx B).comp measurable_snd)
  -- Measurability of {c}
  have h_singleton_meas : MeasurableSet ({c} : Set (Fin (2 * B) → Bool)) :=
    MeasurableSet.singleton c
  -- Apply map_apply
  rw [Measure.map_apply h_meas h_singleton_meas]
  -- Now: ((ℙ.restrict (Set.Ioc 0 1)).prod (ℙ.restrict (Set.Ioc 0 1))) (f⁻¹' {c}) = 2⁻¹ ^ (2 * B)
  let μ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  -- Helper: embed Fin B into Fin (2*B) in two ways
  let fL (i : Fin B) : Fin (2 * B) := ⟨i.val, Nat.lt_of_lt_of_le i.isLt (by omega)⟩
  let fR (i : Fin B) : Fin (2 * B) := ⟨B + i.val, by
    have hi := i.isLt
    omega⟩
  have h_fL_val (i : Fin B) : ((fL i : Fin (2 * B)) : ℕ) = (i : ℕ) := rfl
  have h_fR_val (i : Fin B) : ((fR i : Fin (2 * B)) : ℕ) = B + (i : ℕ) := rfl
  -- The preimage is a product of two sets
  have h_preimage_eq : (fun (p : ℝ × ℝ) (s : Fin (2 * B)) =>
      if (s : ℕ) < B then dig B p.1 s else dig B p.2 (s - B)) ⁻¹' {c} =
      {u : ℝ | ∀ (i : Fin B), dig B u i = c (fL i)} ×ˢ
      {w : ℝ | ∀ (i : Fin B), dig B w i = c (fR i)} := by
    ext ⟨u, w⟩
    constructor
    · intro h
      have h_eq : (fun (p : ℝ × ℝ) (s : Fin (2 * B)) =>
          if (s : ℕ) < B then dig B p.1 s else dig B p.2 (s - B)) (u, w) = c := by
        simpa using h
      constructor
      · intro i
        have h_i := congrFun h_eq (fL i)
        -- fL i has value < B, so the condition is (fL i : ℕ) < B
        have h_lt : ((fL i : Fin (2 * B)) : ℕ) < B := by
          simpa [h_fL_val] using i.isLt
        simp [h_lt] at h_i
        simpa [h_fL_val] using h_i
      · intro i
        have h_i := congrFun h_eq (fR i)
        have h_ge : ¬ ((fR i : Fin (2 * B)) : ℕ) < B := by
          simpa [h_fR_val] using Nat.not_lt.mpr (Nat.le_add_right B (i : ℕ))
        simp [h_ge] at h_i
        -- Need to relate (fR i - B) to i
        -- fR i = B + i, so fR i - B = i
        have h_sub : ((fR i : Fin (2 * B)) : ℕ) - B = (i : ℕ) := by
          simpa [h_fR_val] using Nat.add_sub_cancel_left (i : ℕ) B
        simp [h_sub] at h_i
        simpa [h_fR_val] using h_i
    · intro h
      rcases h with ⟨hu, hw⟩
      have hu' : ∀ (i : Fin B), dig B u i = c (fL i) := hu
      have hw' : ∀ (i : Fin B), dig B w i = c (fR i) := hw
      show (fun (p : ℝ × ℝ) (s : Fin (2 * B)) =>
        if (s : ℕ) < B then dig B p.1 s else dig B p.2 (s - B)) (u, w) = c
      ext s
      by_cases hs : (s : ℕ) < B
      · -- s < B, so s = fL i for some i
        let i : Fin B := ⟨s, hs⟩
        have h_s_eq_fL : (s : Fin (2 * B)) = fL i := by
          ext; simp [fL, i]
        have h_val : ((fL i : Fin (2 * B)) : ℕ) < B := by
          simpa [fL] using i.isLt
        rw [h_s_eq_fL]
        simpa [fL] using hu' i
      · -- s ≥ B, so s = fR i for some i
        have h_lt : (s : ℕ) - B < B := by
          have h_s_lt : (s : ℕ) < 2 * B := s.isLt
          omega
        let i : Fin B := ⟨(s : ℕ) - B, h_lt⟩
        have h_s_eq_fR : (s : Fin (2 * B)) = fR i := by
          ext; simp [fR, i]
          omega
        have h_val : ¬ ((fR i : Fin (2 * B)) : ℕ) < B := by
          simpa [fR] using Nat.not_lt.mpr (Nat.le_add_right B (i : ℕ))
        rw [h_s_eq_fR]
        simpa [fR] using hw' i
  -- Now compute using Measure.prod_prod
  rw [h_preimage_eq]
  -- Need measurability of the two sets for prod_prod
  have hA_meas : MeasurableSet {u : ℝ | ∀ (i : Fin B), dig B u i = c (fL i)} := by
    -- This is a finite intersection of measurable sets
    have h_eq : {u : ℝ | ∀ (i : Fin B), dig B u i = c (fL i)} = ⋂ i : Fin B, {u : ℝ | dig B u i = c (fL i)} := by
      ext u; simp
    rw [h_eq]
    refine MeasurableSet.iInter (fun i => ?_)
    have h_dig_meas : Measurable (fun (u : ℝ) => dig B u i) := by
      have h_cell_meas : Measurable (cellIdx B) := measurable_cellIdx B
      have h_testbit_meas : Measurable (fun (n : ℕ) => n.testBit (B - 1 - i)) :=
        Measurable.of_discrete (f := fun (n : ℕ) => n.testBit (B - 1 - i))
      exact h_testbit_meas.comp h_cell_meas
    have h_singleton_meas : MeasurableSet ({c (fL i)} : Set Bool) :=
      MeasurableSet.singleton (c (fL i))
    exact h_dig_meas h_singleton_meas
  have hB_meas : MeasurableSet {w : ℝ | ∀ (i : Fin B), dig B w i = c (fR i)} := by
    have h_eq : {w : ℝ | ∀ (i : Fin B), dig B w i = c (fR i)} = ⋂ i : Fin B, {w : ℝ | dig B w i = c (fR i)} := by
      ext w; simp
    rw [h_eq]
    refine MeasurableSet.iInter (fun i => ?_)
    have h_dig_meas : Measurable (fun (w : ℝ) => dig B w i) := by
      have h_cell_meas : Measurable (cellIdx B) := measurable_cellIdx B
      have h_testbit_meas : Measurable (fun (n : ℕ) => n.testBit (B - 1 - i)) :=
        Measurable.of_discrete (f := fun (n : ℕ) => n.testBit (B - 1 - i))
      exact h_testbit_meas.comp h_cell_meas
    have h_singleton_meas : MeasurableSet ({c (fR i)} : Set Bool) :=
      MeasurableSet.singleton (c (fR i))
    exact h_dig_meas h_singleton_meas
  rw [MeasureTheory.Measure.prod_prod _ _]
  -- Now: μ {u | ∀ i, dig B u i = c (fL i)} * μ {w | ∀ i, dig B w i = c (fR i)} = 2⁻¹ ^ (2 * B)
  -- Use dig_cell to compute each factor
  -- Define cL : ℕ → Bool corresponding to c ∘ fL (first B coordinates)
  let cL : ℕ → Bool := fun i => if h : i < 2 * B then c ⟨i, h⟩ else false
  have h_cL_fin (i : Fin B) : cL (i : ℕ) = c (fL i) := by
    dsimp [cL, fL]
    have hi : (i : ℕ) < 2 * B := by
      have h := i.isLt
      omega
    simp [hi]
  -- The set for the first factor equals the set in dig_cell for cL
  have h_setL : {u : ℝ | ∀ (i : Fin B), dig B u i = c (fL i)} = {u : ℝ | ∀ i < B, dig B u i = cL i} := by
    ext u; constructor
    · intro h i hi
      let fi : Fin B := ⟨i, hi⟩
      have hfi := h fi
      -- hfi : dig B u ↑fi = c (fL fi)
      -- ↑fi = i, so we can simplify
      simpa [fi, h_cL_fin fi] using hfi
    · intro h i
      -- i : Fin B, so i.val < B
      have hi_val := i.isLt
      have h_i := h i.val hi_val
      -- h_i : dig B u i.val = cL i.val
      -- We need: dig B u i = c (fL i)
      simpa [h_cL_fin i] using h_i
  -- Similarly for the second factor
  let cR : ℕ → Bool := fun i => cL (B + i)
  have h_cR_fin (i : Fin B) : cR (i : ℕ) = c (fR i) := by
    dsimp [cR, cL, fR]
    have hi : (i : ℕ) < 2 * B := by
      have h := i.isLt
      omega
    have hsum : B + (i : ℕ) < 2 * B := by omega
    -- Both sides equal c ⟨B+i, hsum⟩
    -- cR i = cL (B + i) = (if h : B + i < 2*B then c ⟨B+i, h⟩ else false) = c ⟨B+i, hsum⟩
    -- c (fR i) = c ⟨B + i, ...⟩ = c ⟨B+i, hsum⟩
    -- So they're equal
    simp [hsum]
  have h_setR : {w : ℝ | ∀ (i : Fin B), dig B w i = c (fR i)} = {w : ℝ | ∀ i < B, dig B w i = cR i} := by
    ext w; constructor
    · intro h i hi
      let fi : Fin B := ⟨i, hi⟩
      have hfi := h fi
      simpa [fi, h_cR_fin fi] using hfi
    · intro h i
      have hi_val := i.isLt
      have h_i := h i.val hi_val
      simpa [h_cR_fin i] using h_i
  rw [h_setL, h_setR]
  -- Now use dig_cell
  rw [dig_cell B cL, dig_cell B cR]
  -- Goal: ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ))) * ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ))) = 2⁻¹ ^ (2 * B)
  -- Compute the product
  have h_ofReal : ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ))) = (2⁻¹ : ENNReal) ^ B := by
    calc
      ENNReal.ofReal ((2 : ℝ) ^ (-(B : ℝ))) = ENNReal.ofReal (((2 : ℝ)⁻¹) ^ (B : ℝ)) := by
        rw [Real.rpow_neg_eq_inv_rpow]
      _ = ENNReal.ofReal (((2 : ℝ)⁻¹) ^ B) := by rw [Real.rpow_natCast]
      _ = (ENNReal.ofReal ((2 : ℝ)⁻¹)) ^ B := by
        rw [ENNReal.ofReal_pow (by norm_num : 0 ≤ (2 : ℝ)⁻¹)]
      _ = ((ENNReal.ofReal (2⁻¹ : ℝ))) ^ B := by norm_num
      _ = ((2⁻¹ : ENNReal)) ^ B := by
        rw [ENNReal.ofReal_inv_of_pos (by norm_num : 0 < (2 : ℝ))]
        -- Goal: (ENNReal.ofReal 2)⁻¹ ^ B = (2⁻¹ : ENNReal) ^ B
        -- ENNReal.ofReal 2 = (2 : ENNReal) by norm_num
        -- (2 : ENNReal)⁻¹ = 2⁻¹ by simp
        norm_num
  rw [h_ofReal]
  -- Goal: (2⁻¹ : ENNReal) ^ B * (2⁻¹ : ENNReal) ^ B = 2⁻¹ ^ (2 * B)
  calc
    (2⁻¹ : ENNReal) ^ B * (2⁻¹ : ENNReal) ^ B = (2⁻¹ : ENNReal) ^ (B + B) := by rw [pow_add]
    _ = (2⁻¹ : ENNReal) ^ (2 * B) := by rw [show B + B = 2 * B by omega]

/-- The `2B` coins of one block, on a pair of independent standard Gaussians, are fair independent coins. -/
theorem blk_law (B : ℕ) :
    (Measure.pi fun _ : Fin 2 => gaussianReal 0 1).map (fun v (s : Fin (2 * B)) => blkCoin B (v 0, v 1) s) =
      Measure.pi fun _ : Fin (2 * B) => coinLaw := by
  let γ := gaussianReal 0 1
  let g (p : ℝ × ℝ) (s : Fin (2 * B)) : Bool :=
    if (s : ℕ) < B then dig B p.1 s else dig B p.2 (s - B)
  have h_eq : (fun (v : Fin 2 → ℝ) (s : Fin (2 * B)) => blkCoin B (v 0, v 1) s) =
      g ∘ bmInv ∘ MeasurableEquiv.finTwoArrow := by
    ext v s
    simp [g, blkCoin, MeasurableEquiv.finTwoArrow_apply]
  have h_meas_finTwoArrow : Measurable (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) → ℝ × ℝ) :=
    MeasurableEquiv.finTwoArrow.measurable
  have h_meas_bmInv : Measurable (bmInv : ℝ × ℝ → ℝ × ℝ) := measurable_bmInv
  have h_meas_dig_bit (k : ℕ) : Measurable (fun (v : ℝ) => dig B v k) := by
    have h_cell : Measurable (cellIdx B) := measurable_cellIdx B
    have h_testBit : Measurable (fun (n : ℕ) => n.testBit (B - 1 - k)) := measurable_from_nat
    have h_eq' : (fun (v : ℝ) => dig B v k) = (fun (n : ℕ) => n.testBit (B - 1 - k)) ∘ (cellIdx B) := by
      ext v; simp [dig]
    rw [h_eq']
    exact h_testBit.comp h_cell
  have h_meas_comp (s : Fin (2 * B)) : Measurable (fun (p : ℝ × ℝ) => g p s) := by
    dsimp [g]
    split
    · exact (h_meas_dig_bit (s : ℕ)).comp measurable_fst
    · exact (h_meas_dig_bit ((s : ℕ) - B)).comp measurable_snd
  have h_meas_g : Measurable (g : ℝ × ℝ → Fin (2 * B) → Bool) := by
    rw [measurable_pi_iff]
    intro s
    exact h_meas_comp s
  calc
    (Measure.pi fun _ : Fin 2 => γ).map (fun v (s : Fin (2 * B)) => blkCoin B (v 0, v 1) s)
        = (Measure.pi fun _ : Fin 2 => γ).map (g ∘ bmInv ∘ MeasurableEquiv.finTwoArrow) := by
      rw [h_eq]
    _ = Measure.map g (Measure.map (bmInv ∘ MeasurableEquiv.finTwoArrow) (Measure.pi fun _ : Fin 2 => γ)) := by
      rw [Measure.map_map h_meas_g (h_meas_bmInv.comp h_meas_finTwoArrow)]
    _ = Measure.map g (Measure.map bmInv (Measure.map MeasurableEquiv.finTwoArrow (Measure.pi fun _ : Fin 2 => γ))) := by
      rw [Measure.map_map h_meas_bmInv h_meas_finTwoArrow]
    _ = Measure.map g (Measure.map bmInv (γ.prod γ)) := by
      rw [(measurePreserving_finTwoArrow γ).map_eq]
    _ = Measure.map g ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
      rw [map_bmInv]
    _ = Measure.pi fun _ : Fin (2 * B) => coinLaw := by
      rw [uw_law]

/-! ## The law of the stream -/

theorem infinitePi_map_comp_injective {α ι X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {e : α → ι} (he : Function.Injective e) :
    (Measure.infinitePi fun _ : ι => μ).map (fun x a => x (e a)) = Measure.infinitePi fun _ : α => μ := by
  exact Measure.map_infinitePi_infinitePi_of_inj he

/-- The block map: the `2B` coins of a block from its pair of terms of the stream. -/
noncomputable def blkMap (B : ℕ) (v : Fin 2 → ℝ) (s : Fin (2 * B)) : Bool := blkCoin B (v 0, v 1) s

theorem measurable_blkMap (B : ℕ) : Measurable (blkMap B) :=
  measurable_pi_iff.mpr fun s =>
    (measurable_blkCoin B s).comp ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))

/-- The digit map in five steps: the pairs of the blocks, curried; the block map on each block; uncurried; the slots
of the coins. -/
theorem beta_eq_comp (d K0 B : ℕ) (hB : 0 < B) :
    beta d K0 B =
      ((((fun z : (ℕ ⊕ ℕ) × Fin (2 * B) → Bool => fun j => z (coinIdx K0 B hB j)) ∘
        (MeasurableEquiv.curry (ℕ ⊕ ℕ) (Fin (2 * B)) Bool).symm) ∘
        (fun y : (ℕ ⊕ ℕ) → Fin 2 → ℝ => fun a => blkMap B (y a))) ∘
        (MeasurableEquiv.curry (ℕ ⊕ ℕ) (Fin 2) ℝ)) ∘
        (fun x : ℕ → ℝ => fun p => x (pairIdx d p)) := by
  funext x j
  simp [beta, coinIdx, blkMap, pairIdx, MeasurableEquiv.coe_curry, MeasurableEquiv.coe_curry_symm]

/-- (W0-LEAN): the digit map of the schedule meets `W0Law`. -/
theorem w0Law_beta (d K0 B : ℕ) (hB : 0 < B) : W0Law (beta d K0 B) := by
  refine ⟨measurable_beta d K0 B, ?_⟩
  have hF1 : Measurable fun x : ℕ → ℝ => fun p => x (pairIdx d p) :=
    measurable_pi_iff.mpr fun p => measurable_pi_apply _
  have hF2 := (MeasurableEquiv.curry (ℕ ⊕ ℕ) (Fin 2) ℝ).measurable
  have hF3 : Measurable fun y : (ℕ ⊕ ℕ) → Fin 2 → ℝ => fun a => blkMap B (y a) :=
    measurable_pi_iff.mpr fun a => (measurable_blkMap B).comp (measurable_pi_apply a)
  have hF4 := (MeasurableEquiv.curry (ℕ ⊕ ℕ) (Fin (2 * B)) Bool).symm.measurable
  have hF5 : Measurable fun z : (ℕ ⊕ ℕ) × Fin (2 * B) → Bool => fun j => z (coinIdx K0 B hB j) :=
    measurable_pi_iff.mpr fun j => measurable_pi_apply _
  have h1 : gaussStream.map (fun x : ℕ → ℝ => fun p => x (pairIdx d p)) =
      Measure.infinitePi fun _ : (ℕ ⊕ ℕ) × Fin 2 => gaussianReal 0 1 :=
    infinitePi_map_comp_injective (gaussianReal 0 1) (pairIdx_injective d)
  have h2 : (Measure.infinitePi fun _ : (ℕ ⊕ ℕ) × Fin 2 => gaussianReal 0 1).map
      (MeasurableEquiv.curry (ℕ ⊕ ℕ) (Fin 2) ℝ) =
      Measure.infinitePi fun _ : ℕ ⊕ ℕ => Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1 :=
    Measure.infinitePi_map_curry (fun _ _ => gaussianReal 0 1)
  have h3 : (Measure.infinitePi fun _ : ℕ ⊕ ℕ => Measure.infinitePi fun _ : Fin 2 => gaussianReal 0 1).map
      (fun y : (ℕ ⊕ ℕ) → Fin 2 → ℝ => fun a => blkMap B (y a)) =
      Measure.infinitePi fun _ : ℕ ⊕ ℕ => Measure.infinitePi fun _ : Fin (2 * B) => coinLaw := by
    rw [Measure.infinitePi_map_pi _ (f := fun _ => blkMap B) fun _ => measurable_blkMap B]
    congr 1
    funext a
    rw [Measure.infinitePi_eq_pi, Measure.infinitePi_eq_pi]
    exact blk_law B
  have h4 : (Measure.infinitePi fun _ : ℕ ⊕ ℕ => Measure.infinitePi fun _ : Fin (2 * B) => coinLaw).map
      (MeasurableEquiv.curry (ℕ ⊕ ℕ) (Fin (2 * B)) Bool).symm =
      Measure.infinitePi fun _ : (ℕ ⊕ ℕ) × Fin (2 * B) => coinLaw :=
    Measure.infinitePi_map_curry_symm (fun _ _ => coinLaw)
  have h5 : (Measure.infinitePi fun _ : (ℕ ⊕ ℕ) × Fin (2 * B) => coinLaw).map
      (fun z : (ℕ ⊕ ℕ) × Fin (2 * B) → Bool => fun j => z (coinIdx K0 B hB j)) = coinStream :=
    infinitePi_map_comp_injective coinLaw (coinIdx_injective hB)
  rw [beta_eq_comp d K0 B hB, ← Measure.map_map (((hF5.comp hF4).comp hF3).comp hF2) hF1, h1,
    ← Measure.map_map ((hF5.comp hF4).comp hF3) hF2, h2, ← Measure.map_map (hF5.comp hF4) hF3, h3,
    ← Measure.map_map hF5 hF4, h4, h5]

/-! ## The coins read before round `t` are known before round `t` -/

/-- A coin read before round `t` is measurable in the coupled filtration at `t`. -/
theorem meas_beta_c (d K0 B t j : ℕ) (hj : j < blkStart d K0 B t 0) :
    Measurable[cσ d t] fun ω : WΩ => beta d K0 B ω.1 j := by
  have hg := grp_past d K0 B t j hj
  have hc : ∀ i ∈ grp d K0 B j, Measurable[cσ d t] fun ω : WΩ => ω.1 i := fun i hi =>
    meas_coord i ((le_iSup₂ (f := fun i (_ : i ∈ idxC d t) => gσ i) i (hg hi)).trans le_sup_left)
  have ha := hc (pairOf d (blkOf K0 B j)).1 (by simp [grp])
  have hb := hc (pairOf d (blkOf K0 B j)).2 (by simp [grp])
  exact (measurable_blkCoin B (posOf K0 B j)).comp (ha.prodMk hb)

/-- A map of the coins that reads only the coins `j < N`, all read before round `t`, is measurable in the coupled
filtration at `t`, for any codomain. -/
theorem meas_comp_beta {Y : Type*} [MeasurableSpace Y] (d K0 B t N : ℕ) (hN : N ≤ blkStart d K0 B t 0)
    (f : (ℕ → Bool) → Y) (hf : ∀ cs cs' : ℕ → Bool, (∀ j < N, cs j = cs' j) → f cs = f cs') :
    Measurable[cσ d t] fun ω : WΩ => f (beta d K0 B ω.1) := by
  let g : (Fin N → Bool) → Y := fun c => f fun j => if h : j < N then c ⟨j, h⟩ else false
  have hg : Measurable g := measurable_of_countable g
  have hc : Measurable[cσ d t] fun ω : WΩ => fun j : Fin N => beta d K0 B ω.1 j :=
    (@measurable_pi_iff WΩ (Fin N) (fun _ => Bool) (cσ d t) _ _).mpr fun j =>
      meas_beta_c d K0 B t j (lt_of_lt_of_le j.2 hN)
  have heq : (fun ω : WΩ => f (beta d K0 B ω.1)) = g ∘ fun ω : WΩ => fun j : Fin N => beta d K0 B ω.1 j := by
    funext ω
    exact hf _ _ fun j hj => by simp [hj]
  rw [heq]
  exact hg.comp hc
end AdversarialBco.Bit.Sched
