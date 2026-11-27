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

The coins of a stage (`readCoins_congr`, `tzY_shift`) and the constants from the slot `n` and the register `d`
(`clog4_eq`, `triSQ_eq_of`, `triLa_ge`).
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

theorem AdversarialBco.Bit.TriM.clog4_eq (x : ℕ) : Nat.clog 4 x = (Nat.clog 2 x + 1) / 2 := by
  calc
    Nat.clog 4 x = Nat.clog (2 ^ 2) x := by norm_num
    _ = (Nat.clog 2 x + (2 - 1)) / 2 := by rw [Nat.clog_pow_left]
    _ = (Nat.clog 2 x + 1) / 2 := by norm_num

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

theorem AdversarialBco.Bit.TriM.triLa_ge (d : ℕ) : 10 ≤ triLa (triSQ d) := by
  have h4 := (triSQ_bounds d).1
  unfold triLa
  have : 5 * 4 ^ 2 ≤ 5 * triSQ d ^ 2 := Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left h4 2)
  have h7 : 5 * 4 ^ 2 / 7 ≤ 5 * triSQ d ^ 2 / 7 := Nat.div_le_div_right this
  norm_num at h7
  omega

