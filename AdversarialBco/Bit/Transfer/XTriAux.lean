/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriCore

@[expose] public section

/-!
# TRI-M, auxiliary lemmas

The coins of a stage (`readCoins_congr`, `tzY_shift`, `tzIter_congr`, `tzSum_congr`, `stage_coins`), the constants
from the slot `n` and the register `d` (`clog4_eq`, `mst_eq`, `ellPos_eq`, `triSQ_eq_of`), the constants of a draw
(`tzDC_ok`), and the row bounds (`tzRowA_abs_le`, `tzRowB_abs_le`).
-/

open AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.Transfer AdversarialBco.Bit.TriM Matrix

theorem AdversarialBco.Bit.TriM.readCoins_congr (x cs : ℕ → Bool) (a c B : ℕ)
    (h : ∀ j < B, x (a + j) = cs (c + j)) : BitRAM.readCoins x a B = BitRAM.readCoins cs c B := by
  induction' B with B ih
  · rfl
  · simp only [BitRAM.readCoins]
    rw [ih (fun j hj => h j (Nat.lt_of_lt_of_le hj (Nat.le_succ _)))]
    have hB := h B (by omega)
    simp [hB]

theorem AdversarialBco.Bit.TriM.tzY_shift {d : ℕ} (B c0 t : ℕ) (cs x : ℕ → Bool)
    (hx : ∀ k < 2 * B * d * (t + 1), x k = cs (c0 + k)) : tzY d B x t = tzYc (d := d) cs B c0 t := by
  funext i
  unfold tzY tzYc gsAt
  have hi : (i : ℕ) < d := i.2
  have h1 : BitRAM.readCoins x (2 * ((t : ℕ) * d + (i : ℕ)) * B) B =
      BitRAM.readCoins cs (c0 + 2 * ((t : ℕ) * d + (i : ℕ)) * B) B := by
    apply readCoins_congr x cs (2 * ((t : ℕ) * d + (i : ℕ)) * B) (c0 + 2 * ((t : ℕ) * d + (i : ℕ)) * B) B
    intro j hj
    have hk : 2 * ((t : ℕ) * d + (i : ℕ)) * B + j < 2 * B * d * (t + 1) := by nlinarith
    simpa [add_assoc] using hx (2 * ((t : ℕ) * d + (i : ℕ)) * B + j) hk
  have h2 : BitRAM.readCoins x ((2 * ((t : ℕ) * d + (i : ℕ)) + 1) * B) B =
      BitRAM.readCoins cs (c0 + (2 * ((t : ℕ) * d + (i : ℕ)) + 1) * B) B := by
    apply readCoins_congr x cs ((2 * ((t : ℕ) * d + (i : ℕ)) + 1) * B) (c0 + (2 * ((t : ℕ) * d + (i : ℕ)) + 1) * B) B
    intro j hj
    have hk : (2 * ((t : ℕ) * d + (i : ℕ)) + 1) * B + j < 2 * B * d * (t + 1) := by nlinarith
    simpa [add_assoc] using hx ((2 * ((t : ℕ) * d + (i : ℕ)) + 1) * B + j) hk
  have hleft1 : c0 + 2 * ((t : ℕ) * d + (i : ℕ)) * B = c0 + 2 * B * d * t + 2 * B * (i : ℕ) := by ring
  have hleft2 : c0 + (2 * ((t : ℕ) * d + (i : ℕ)) + 1) * B = c0 + 2 * B * d * t + 2 * B * (i : ℕ) + B := by ring
  simp [h1, h2, hleft1, hleft2]

theorem AdversarialBco.Bit.TriM.tzIter_congr {d M : ℕ} (c : DC) (T : Matrix (Fin d) (Fin d) ℤ)
    (mu : Fin d → ℤ) (ra : ℕ → Fin d → ℤ) (rb : ℕ → ℤ) (Y Y' : ℕ → Fin d → ℤ) (N : ℕ)
    (h : ∀ t < N, Y t = Y' t) : ∀ t ≤ N, tzIter c T mu ra rb M Y t = tzIter c T mu ra rb M Y' t := by
  intro t ht
  induction' t with t IH
  · rfl
  · have ht' : t ≤ N := by omega
    have hY : Y t = Y' t := h t (by omega)
    rw [tzIter, tzIter, IH ht', hY]

theorem AdversarialBco.Bit.TriM.tzSum_congr {d M : ℕ} (c : DC) (T : Matrix (Fin d) (Fin d) ℤ)
    (mu : Fin d → ℤ) (ra : ℕ → Fin d → ℤ) (rb : ℕ → ℤ) (Y Y' : ℕ → Fin d → ℤ) (N : ℕ)
    (h : ∀ t < N, Y t = Y' t) : tzSum c T mu ra rb M Y N = tzSum c T mu ra rb M Y' N := by
  dsimp [tzSum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' : t < N := Finset.mem_range.mp ht
  exact tzIter_congr c T mu ra rb Y Y' N h t (le_of_lt ht')

theorem AdversarialBco.Bit.TriM.clog4_eq (x : ℕ) : Nat.clog 4 x = (Nat.clog 2 x + 1) / 2 := by
  calc
    Nat.clog 4 x = Nat.clog (2 ^ 2) x := by norm_num
    _ = (Nat.clog 2 x + (2 - 1)) / 2 := by rw [Nat.clog_pow_left]
    _ = (Nat.clog 2 x + 1) / 2 := by norm_num

theorem AdversarialBco.Bit.TriM.mst_eq (n : ℕ) (hn : 1 ≤ n) : triMstQ (1 / 2) n = Nat.clog 2 (2 * n) := by
  unfold triMstQ
  have h2pos : 1 < (2 : ℕ) := by norm_num
  have h2npos : 1 < 2 * n := by
    have : 1 ≤ n := hn
    omega
  have hceil : ⌈(n : ℚ) / ((1 : ℚ) / 2)⌉₊ = 2 * n := by
    calc
      ⌈(n : ℚ) / ((1 : ℚ) / 2)⌉₊ = ⌈(n : ℚ) * (2 : ℚ)⌉₊ := by ring
      _ = ⌈((2 * n : ℕ) : ℚ)⌉₊ := by push_cast; ring
      _ = 2 * n := Nat.ceil_natCast _
  have hclogpos : 0 < Nat.clog 2 (2 * n) := Nat.clog_pos h2pos h2npos
  have hmax : max 1 (Nat.clog 2 (2 * n)) = Nat.clog 2 (2 * n) := by
    apply max_eq_right
    omega
  rw [hceil, hmax]

theorem AdversarialBco.Bit.TriM.ellPos_eq (d n : ℕ) (hn : 1 ≤ n) :
    ellPos d n = Nat.clog 2 (3 * 2 ^ 19 * (d * n) ^ 3 * Nat.clog 2 (2 * n)) := by
  unfold ellPos
  rw [AdversarialBco.Bit.TriM.mst_eq n hn]

theorem AdversarialBco.Bit.TriM.triSQ_eq_of (d s : ℕ) (hs : 4 ≤ s)
    (ht : 2086812 * d ^ 2 * triLh s ≤ 125 * (2 ^ triLa s - 1) ^ 2)
    (hmin : ∀ s', 4 ≤ s' → s' < s → 125 * (2 ^ triLa s' - 1) ^ 2 < 2086812 * d ^ 2 * triLh s') :
    triSQ d = s := by
  rw [triSQ]
  apply (Nat.find_eq_iff (pg_par_exists d)).mpr
  have hP : (4 ≤ s ∧ 2086812 * d ^ 2 * ((50 * s ^ 2 + 68) / 69) ≤ 125 * (2 ^ (5 * s ^ 2 / 7) - 1) ^ 2) := by
    simpa [triLh, triLa] using And.intro hs ht
  refine ⟨hP, ?_⟩
  intro s' hs'_lt_s
  by_cases hs'4 : 4 ≤ s'
  · have hstrict := hmin s' hs'4 hs'_lt_s
    intro h
    have hineq : 2086812 * d ^ 2 * triLh s' ≤ 125 * (2 ^ triLa s' - 1) ^ 2 := by
      simpa [triLh, triLa] using h.2
    exact (Nat.lt_irrefl _) (Nat.lt_of_lt_of_le hstrict hineq)
  · intro h
    exact hs'4 h.1

theorem AdversarialBco.Bit.TriM.tzRowA_abs_le {d m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (k : Fin (m + (d + d))) (l : Fin d) : |tzRowA A b k l| ≤ (frMhat A b : ℤ) ^ (d + 1) := by
  have h_one_pow : (1 : ℤ) ≤ (frMhat A b : ℤ) ^ (d + 1) := by
    have hfr : 1 ≤ frMhat A b := le_max_left _ _
    have hfr_pos : 0 < frMhat A b := by omega
    have h_nat : 1 ≤ frMhat A b ^ (d + 1) := Nat.one_le_pow (d + 1) (frMhat A b) hfr_pos
    exact_mod_cast h_nat
  unfold tzRowA
  refine Fin.addCases ?_ ?_ k
  · intro k'
    simpa using (frAl_le A b k').2.1 l
  · intro k'
    refine Fin.addCases ?_ ?_ k'
    · intro i
      rw [Fin.append_right, Fin.append_left]
      have h_single : |(Pi.single (M := fun (_ : Fin d) => ℤ) i 1 l : ℤ)| ≤ (1 : ℤ) := by
        by_cases h_eq : i = l
        · subst h_eq; simp
        · simp [h_eq]
      exact le_trans h_single h_one_pow
    · intro i
      rw [Fin.append_right, Fin.append_right]
      have h_single : |(-Pi.single (M := fun (_ : Fin d) => ℤ) i 1 l : ℤ)| ≤ (1 : ℤ) := by
        by_cases h_eq : i = l
        · subst h_eq; simp
        · simp [h_eq]
      exact le_trans h_single h_one_pow

theorem AdversarialBco.Bit.TriM.tzRowB_abs_le {d m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (ch : Fin d → ℤ) (e j : ℕ) (D H : ℤ) (hD : 0 ≤ D) (hH : 0 ≤ H) (hch : ∀ i, |ch i| ≤ H)
    (k : Fin (m + (d + d))) :
    |tzRowB A b ch e j D k| ≤ (frMhat A b : ℤ) ^ (d + 1) * D + H * 2 ^ e + 2 ^ j * D := by
  have hM : (0 : ℤ) ≤ (frMhat A b : ℤ) ^ (d + 1) * D := by positivity
  have h2e : (0 : ℤ) ≤ 2 ^ e := by positivity
  have h2j : (0 : ℤ) ≤ 2 ^ j * D := by positivity
  have hHe : (0 : ℤ) ≤ H * 2 ^ e := mul_nonneg hH h2e
  have hbox : ∀ i, |ch i * 2 ^ e| ≤ H * 2 ^ e := fun i => by
    rw [abs_mul, abs_of_nonneg h2e]; exact mul_le_mul_of_nonneg_right (hch i) h2e
  unfold tzRowB
  refine Fin.addCases (fun k' => ?_) (fun k' => ?_) k
  · rw [Fin.append_left, abs_mul, abs_of_nonneg hD]
    have := mul_le_mul_of_nonneg_right (frAl_le A b k').2.2 hD
    linarith
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) k'
    · rw [Fin.append_right, Fin.append_left]
      have := abs_add_le (ch i * 2 ^ e) (2 ^ j * D)
      rw [abs_of_nonneg h2j] at this
      linarith [hbox i]
    · rw [Fin.append_right, Fin.append_right]
      have := abs_sub (2 ^ j * D) (ch i * 2 ^ e)
      rw [abs_of_nonneg h2j] at this
      linarith [hbox i]

theorem AdversarialBco.Bit.TriM.stage_coins {d : ℕ} (B N mst Lc j c0 : ℕ) (cs : ℕ → Bool) (hj : j < mst)
    (hL : 2 * B * d * N ≤ Lc) (t : ℕ) (ht : t < N) :
    tzY d B (fun k => cs (c0 + triLay mst Lc (j, k))) t = tzYc (d := d) cs B (c0 + j * Lc) t := by
  refine tzY_shift B (c0 + j * Lc) t cs _ (fun k hk => ?_)
  have hkL : k < Lc := by
    have : 2 * B * d * (t + 1) ≤ 2 * B * d * N := Nat.mul_le_mul_left _ ht
    omega
  simp only [triLay, if_pos (show j < mst ∧ k < Lc from ⟨hj, hkL⟩)]
  congr 1
  ring

theorem AdversarialBco.Bit.TriM.triLa_ge (d : ℕ) : 10 ≤ triLa (triSQ d) := by
  have h4 := (triSQ_bounds d).1
  unfold triLa
  have : 5 * 4 ^ 2 ≤ 5 * triSQ d ^ 2 := Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left h4 2)
  have h7 : 5 * 4 ^ 2 / 7 ≤ 5 * triSQ d ^ 2 / 7 := Nat.div_le_div_right this
  norm_num at h7
  omega

theorem AdversarialBco.Bit.TriM.tzDC_ok (d ℓ : ℕ) :
    0 ≤ (tzDC d ℓ).R ∧ (tzDC d ℓ).R ≤ (tzDC d ℓ).Bh ∧ 0 < (tzDC d ℓ).Al ∧ (tzDC d ℓ).Al ≤ (tzDC d ℓ).Bh ∧
      0 ≤ (tzDC d ℓ).PG ∧ (tzDC d ℓ).PG ≤ (tzDC d ℓ).Bh := by
  have hLa := triLa_ge d
  set La := triLa (triSQ d)
  have hG : tzG d ℓ = triBvQ d + triJsQ d ℓ + triJaQ d := rfl
  have key : ∀ x : ℕ, x ≤ La - 10 + tzG d ℓ → (2 : ℤ) ^ x ≤ 161 * 2 ^ (La - 10 + tzG d ℓ) := fun x hx => by
    calc (2 : ℤ) ^ x ≤ 2 ^ (La - 10 + tzG d ℓ) := pow_le_pow_right₀ (by norm_num) hx
      _ ≤ 161 * 2 ^ (La - 10 + tzG d ℓ) := le_mul_of_one_le_left (by positivity) (by norm_num)
  simp only [tzDC]
  refine ⟨by positivity, ?_, by positivity, key _ (by omega), by positivity, key _ (by omega)⟩
  rw [show La - 3 + tzG d ℓ = (La - 10 + tzG d ℓ) + 7 by omega, pow_add, mul_comm]
  exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
