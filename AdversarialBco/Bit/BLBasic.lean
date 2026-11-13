/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.BLLink

@[expose] public section

/-!
# Basic lemmas on BL's pure function

The rounding primitives of Bit/BLPure.lean against the exact values (`rnd`, `dn`, `up`, `sqrtDn`, `sqrtUp`), and the
coin locality of the run: the draw of round `t` reads the coins of its blocks, and the run before round `t` reads the
coins before round `t`'s first block (given `PosLocal`).
-/
namespace AdversarialBco.Bit.BLP

theorem rnd_err (k : ℕ) (x : ℚ) : |rnd k x - x| ≤ 1 / 2 ^ (k + 1) := by
  have h2 : (0:ℚ) < 2 ^ k := by positivity
  have e : rnd k x - x = ((⌊x * 2 ^ k + 1 / 2⌋ : ℚ) - x * 2 ^ k) / 2 ^ k := by
    unfold rnd; field_simp
  have hf := Int.floor_le (x * 2 ^ k + 1 / 2)
  have hl := Int.lt_floor_add_one (x * 2 ^ k + 1 / 2)
  have e2 : (1:ℚ) / 2 ^ (k + 1) = (1 / 2) / 2 ^ k := by rw [pow_succ]; field_simp
  rw [e, e2, abs_div, abs_of_pos h2]
  gcongr
  rw [abs_le]; constructor <;> linarith

theorem dn_le (k : ℕ) (x : ℚ) : dn k x ≤ x := by
  unfold dn
  rw [div_le_iff₀ (by positivity)]; exact Int.floor_le _

theorem sub_lt_dn (k : ℕ) (x : ℚ) : x - 1 / 2 ^ k < dn k x := by
  have h2 : (0:ℚ) < 2 ^ k := by positivity
  have e : dn k x - (x - 1 / 2 ^ k) = ((⌊x * 2 ^ k⌋ : ℚ) - x * 2 ^ k + 1) / 2 ^ k := by
    unfold dn; field_simp; ring
  have := Int.lt_floor_add_one (x * 2 ^ k)
  have : 0 < dn k x - (x - 1 / 2 ^ k) := by rw [e]; apply div_pos _ h2; linarith
  linarith

theorem le_up (k : ℕ) (x : ℚ) : x ≤ up k x := by
  unfold up
  rw [le_div_iff₀ (by positivity)]; exact Int.le_ceil _

theorem up_lt (k : ℕ) (x : ℚ) : up k x < x + 1 / 2 ^ k := by
  have h2 : (0:ℚ) < 2 ^ k := by positivity
  have e : x + 1 / 2 ^ k - up k x = (x * 2 ^ k + 1 - (⌈x * 2 ^ k⌉ : ℚ)) / 2 ^ k := by
    unfold up; field_simp
  have := Int.ceil_lt_add_one (x * 2 ^ k)
  have : 0 < x + 1 / 2 ^ k - up k x := by rw [e]; apply div_pos _ h2; linarith
  linarith

theorem sqrtDn_nonneg (k : ℕ) (x : ℚ) : 0 ≤ sqrtDn k x := by unfold sqrtDn; positivity

theorem sqrtDn_sq_le (k : ℕ) {x : ℚ} (hx : 0 ≤ x) : sqrtDn k x ^ 2 ≤ x := by
  unfold sqrtDn
  have h4 : (4:ℚ) ^ k = (2 ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [div_pow, div_le_iff₀ (by positivity)]
  have hs := Nat.sqrt_le' ⌊x * 4 ^ k⌋₊
  have hf := Nat.floor_le (a := x * 4 ^ k) (by positivity)
  have : ((Nat.sqrt ⌊x * 4 ^ k⌋₊ : ℕ) : ℚ) ^ 2 ≤ (⌊x * 4 ^ k⌋₊ : ℚ) := by exact_mod_cast hs
  rw [← h4]; linarith

theorem lt_sqrtDn_succ_sq (k : ℕ) (x : ℚ) : x < (sqrtDn k x + 1 / 2 ^ k) ^ 2 := by
  unfold sqrtDn
  have h4 : (4:ℚ) ^ k = (2 ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h2 : (0:ℚ) < 2 ^ k := by positivity
  have he : (Nat.sqrt ⌊x * 4 ^ k⌋₊ : ℚ) / 2 ^ k + 1 / 2 ^ k
      = ((Nat.sqrt ⌊x * 4 ^ k⌋₊ : ℚ) + 1) / 2 ^ k := by ring
  rw [he, div_pow, lt_div_iff₀ (by positivity)]
  have hs := Nat.lt_succ_sqrt' ⌊x * 4 ^ k⌋₊
  have hf := Nat.lt_floor_add_one (x * 4 ^ k)
  have : (⌊x * 4 ^ k⌋₊ : ℚ) + 1 ≤ ((Nat.sqrt ⌊x * 4 ^ k⌋₊ + 1 : ℕ) : ℚ) ^ 2 := by exact_mod_cast hs
  push_cast at this
  rw [← h4]; linarith

theorem le_sqrtUp_sq (k : ℕ) (x : ℚ) : x ≤ sqrtUp k x ^ 2 := by
  unfold sqrtUp
  have h4 : (4:ℚ) ^ k = (2 ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [div_pow, le_div_iff₀ (by positivity)]
  have hs := Nat.lt_succ_sqrt' ⌈x * 4 ^ k⌉₊
  have hf := Nat.le_ceil (x * 4 ^ k)
  have : (⌈x * 4 ^ k⌉₊ : ℚ) + 1 ≤ ((Nat.sqrt ⌈x * 4 ^ k⌉₊ + 1 : ℕ) : ℚ) ^ 2 := by exact_mod_cast hs
  push_cast at this
  rw [← h4]; linarith

open AdversarialBco.BitRAM

theorem readCoins_congr (cs cs' : ℕ → Bool) (c k : ℕ) (h : ∀ j, c ≤ j → j < c + k → cs j = cs' j) :
    readCoins cs c k = readCoins cs' c k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [readCoins]
    rw [ih (fun j h1 h2 => h j h1 (by omega)), h (c + k) (by omega) (by omega)]

theorem blkStart_succ_le (d K0 B t q : ℕ) (hq : q < Sched.nBlk d) :
    Sched.blkStart d K0 B t q + 2 * B ≤ Sched.blkStart d K0 B (t + 1) 0 := by
  unfold Sched.blkStart
  have : t * Sched.nBlk d + q + 1 ≤ (t + 1) * Sched.nBlk d + 0 := by rw [add_mul]; omega
  nlinarith

theorem blkUW_congr (cs cs' : ℕ → Bool) (K0 B d t q : ℕ) (hq : q < Sched.nBlk d)
    (h : ∀ j, j < Sched.blkStart d K0 B (t + 1) 0 → cs j = cs' j) :
    blkUW cs K0 B d t q = blkUW cs' K0 B d t q := by
  have hle := blkStart_succ_le d K0 B t q hq
  unfold blkUW
  rw [readCoins_congr cs cs' _ B (fun j _ h2 => h j (by omega)),
    readCoins_congr cs cs' _ B (fun j _ h2 => h j (by omega))]

theorem draw_congr (cs cs' : ℕ → Bool) (K0 B d t : ℕ)
    (h : ∀ j, j < Sched.blkStart d K0 B (t + 1) 0 → cs j = cs' j) :
    draw cs K0 B d t = draw cs' K0 B d t := by
  have hb : ∀ q, q < Sched.nBlk d → blkUW cs K0 B d t q = blkUW cs' K0 B d t q :=
    fun q hq => blkUW_congr cs cs' K0 B d t q hq h
  refine Prod.ext ?_ ?_
  · funext i
    show (if (i : ℕ) % 2 = 0 then _ else _) = (if (i : ℕ) % 2 = 0 then _ else _)
    rw [hb ((i : ℕ) / 2) (by unfold Sched.nBlk; omega)]
  · show (gOut B (blkUW cs K0 B d t ((d + 1) / 2))).1 / 2 = (gOut B (blkUW cs' K0 B d t ((d + 1) / 2))).1 / 2
    rw [hb _ (by unfold Sched.nBlk; omega)]

theorem K0_le_blkStart (d K0 B t q : ℕ) : K0 ≤ Sched.blkStart d K0 B t q := by
  unfold Sched.blkStart; omega

theorem blkStart_mono (d K0 B : ℕ) {t t' : ℕ} (h : t ≤ t') :
    Sched.blkStart d K0 B t 0 ≤ Sched.blkStart d K0 B t' 0 := by
  unfold Sched.blkStart; gcongr

/-- The run before round `t` reads only the coins before round `t`'s first block. -/
theorem traj_congr (R : Routines) (hR : PosLocal R) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (σ : RealRAM.Strategy d) (cs cs' : ℕ → Bool) (t : ℕ)
    (h : ∀ j, j < Sched.blkStart d (R.K0 d n) (par d n).B t 0 → cs j = cs' j) :
    traj R d n m A b σ cs t = traj R d n m A b σ cs' t := by
  have hcfg : cfgOf R d n m A b cs = cfgOf R d n m A b cs' := by
    unfold cfgOf
    rw [hR d n m A b cs cs' (fun j hj => h j (lt_of_lt_of_le hj (K0_le_blkStart _ _ _ _ _)))]
  induction t with
  | zero => simp only [traj, hcfg]
  | succ t ih =>
    have ih' := ih (fun j hj => h j (lt_of_lt_of_le hj (blkStart_mono _ _ _ (Nat.le_succ t))))
    have hdr : drawAt R d n cs t = drawAt R d n cs' t := draw_congr cs cs' _ _ d t h
    simp only [traj]
    rw [hcfg, ih', hdr]

end AdversarialBco.Bit.BLP
