/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PolyInst
public import AdversarialBco.Bit.Transfer.XFrameE
public import AdversarialBco.Bit.Transfer.XFrameW
public import AdversarialBco.Bit.Transfer.XFrameLem
public import AdversarialBco.Bit.Transfer.XBLSetupFacts
public import AdversarialBco.Bit.Transfer.XArith
public import AdversarialBco.Bit.Transfer.XDrvPoly

@[expose] public section

/-!
# UNI-POLY: the polynomial bound of the machine clauses (`bound_mach_gen`)

For a compiler whose block constant `Kc` and prologue cost `Cpro` are polynomial in the size of the instance, the bound
`Bmach` of the machine clauses at Theorem U's bound `B_U = C_U (d log(2dn/δ) S)^{k_U}` (`δ = 1/(n+1)`, `S` the size of
Theorem U's input) is at most `C' (d m log(2dn) log(2M))^{k'}`. The load-bearing step is the size `S` of the frame
centre `frameQ`: its coordinates are `â_i / 2^p` with `|â_i|` below ELL-F's cap for `d ≥ 2` (`ellUpd` refuses a centre
above it), and `(β_i α_j + β_j α_i) / (2 α_i α_j)` for `d = 1`, with `|α|, |β| ≤ M̂^2`.
-/

namespace AdversarialBco.UniPoly

open BitRAM

variable {d : ℕ}

/-! ## The heights of the frame centre -/

/-- `x / D` in lowest terms: numerator at most `|x|`, denominator at most `|D|`. -/
theorem pb_div_height (x D : ℤ) (hD : D ≠ 0) :
    ((x : ℚ) / D).num.natAbs ≤ x.natAbs ∧ ((x : ℚ) / D).den ≤ D.natAbs := by
  rw [← Rat.divInt_eq_div]
  constructor
  · by_cases hx : x = 0
    · subst hx; simp
    · exact Int.natAbs_le_of_dvd_ne_zero (Rat.num_dvd x hD) hx
  · have h := Int.natAbs_dvd_natAbs.2 (Rat.den_dvd x D)
    rw [Int.natAbs_natCast] at h
    exact Nat.le_of_dvd (Int.natAbs_pos.2 hD) h

/-- FRAME's read-off for `d = 1` is the midpoint of two quotients `β_i / α_i`, `β_j / α_j` with `α_i, α_j ≠ 0`. -/
theorem pb_frame1_some {m : ℕ} (al be : Fin m → ℤ) {c : ℚ} (h : Bit.RQ.frame1 al be = some c) :
    ∃ i j, al i ≠ 0 ∧ al j ≠ 0 ∧ c = ((be i : ℚ) / al i + (be j : ℚ) / al j) / 2 := by
  unfold Bit.RQ.frame1 at h
  split_ifs at h with h0
  split at h
  · rename_i lo hi hlo hhi
    split_ifs at h with hw
    obtain rfl := (Option.some.inj h).symm
    obtain ⟨i, -, hi'⟩ := List.mem_filterMap.1 (List.max?_mem hlo)
    obtain ⟨j, -, hj'⟩ := List.mem_filterMap.1 (List.min?_mem hhi)
    split_ifs at hi' with hai
    split_ifs at hj' with haj
    refine ⟨i, j, by omega, by omega, ?_⟩
    rw [← Option.some.inj hi', ← Option.some.inj hj']
  · exact absurd h (by simp)

/-- ELL-F's update refuses a centre above the cap `capa`. -/
theorem pb_ellUpd_bound {p q j : ℕ} {capA capa : ℤ} {A : Matrix (Fin d) (Fin d) ℤ} {a c : Fin d → ℤ}
    {A' : Matrix (Fin d) (Fin d) ℤ} {a' : Fin d → ℤ} (h : Bit.RQ.ellUpd p q j capA capa A a c = some (A', a')) :
    ∀ i, |a' i| ≤ capa := by
  unfold Bit.RQ.ellUpd at h
  simp only at h
  split_ifs at h with h1 h2
  have e := (Prod.mk.inj (Option.some.inj h)).2
  intro i
  rw [← e, Bit.RQ.Arr.get_ofFn']
  push_neg at h2
  exact h2.2 i

/-- ELL-F's loop returns a centre below the cap. -/
theorem pb_frLoop_bound {m : ℕ} (p q : ℕ) (capA capa : ℤ) (al : Fin m → Fin d → ℤ) (B nn : Fin m → ℤ) :
    ∀ (k : ℕ) (A : Matrix (Fin d) (Fin d) ℤ) (a r : Fin d → ℤ), (∀ i, |a i| ≤ capa) →
      Bit.RQ.frLoop p q capA capa al B nn k A a = some r → ∀ i, |r i| ≤ capa := by
  intro k
  induction k with
  | zero => intro A a r _ h; simp [Bit.RQ.frLoop] at h
  | succ k ih =>
    intro A a r ha h
    simp only [Bit.RQ.frLoop] at h
    split at h
    · exact (Option.some.inj h) ▸ ha
    · rename_i i hi
      by_cases hn : nn i = 0
      · simp [hn] at h
      · rw [if_neg hn] at h
        split at h
        · exact absurd h (by simp)
        · rename_i A' a' hu
          exact ih A' a' r (pb_ellUpd_bound hu) h

/-- ELL-F's centre is below its cap `2^p (2^{e_R} + 2^{4 e_R + 4})`. -/
theorem pb_frEll_bound {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) {a : Fin d → ℤ}
    (h : Bit.RQ.frEll A b = some a) (i : Fin d) :
    |a i| ≤ 2 ^ Bit.RQ.frP d * (2 ^ Bit.RQ.frER d m (Bit.RQ.frMhat A b) +
      2 ^ (Bit.RQ.frER d m (Bit.RQ.frMhat A b) + 3 * (Bit.RQ.frER d m (Bit.RQ.frMhat A b) + 1) + 1)) := by
  simp only [Bit.RQ.frEll] at h
  exact pb_frLoop_bound _ _ _ _ _ _ _ _ _ _ _ (fun i => by simp only [Pi.zero_apply, abs_zero]; positivity) h i

/-- The frame centre for `d ≥ 2`: numerators below `2^{p + 4 e_R + 5}`, denominators below `2^p`. -/
theorem pb_frameQ_ge2 {n m : ℕ} (hd : 2 ≤ d) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (i : Fin d) :
    (Bit.RQ.frameQ d n m A b i).num.natAbs ≤ 2 ^ (Bit.RQ.frP d + 4 * Bit.RQ.frER d m (Bit.RQ.frMhat A b) + 5) ∧
      (Bit.RQ.frameQ d n m A b i).den ≤ 2 ^ Bit.RQ.frP d := by
  rw [Bit.Transfer.frameQ_ge2 hd]
  set P := Bit.RQ.frP d with hP
  set e := Bit.RQ.frER d m (Bit.RQ.frMhat A b) with he
  cases hE : Bit.RQ.frEll A b with
  | none =>
    simp only [Bit.Transfer.frOutQ, Pi.zero_apply, Rat.num_zero, Int.natAbs_zero, Rat.den_zero]
    exact ⟨Nat.zero_le _, Nat.one_le_two_pow⟩
  | some a =>
    simp only [Bit.Transfer.frOutQ]
    have hc := pb_frEll_bound A b hE i
    rw [← hP, ← he] at hc
    have e1 : ((a i : ℤ) : ℚ) / 2 ^ P = ((a i : ℤ) : ℚ) / ((2 ^ P : ℤ) : ℚ) := by push_cast; rfl
    rw [e1]
    obtain ⟨h1, h2⟩ := pb_div_height (a i) (2 ^ P) (by positivity)
    refine ⟨h1.trans ?_, h2.trans (by rw [Int.natAbs_pow]; rfl)⟩
    have hb : |a i| ≤ 2 ^ (P + 4 * e + 5) := by
      refine hc.trans ?_
      have q1 : (2 : ℤ) ^ e ≤ 2 ^ (4 * e + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
      have q2 : e + 3 * (e + 1) + 1 = 4 * e + 4 := by ring
      have q3 : (2 : ℤ) ^ (P + 4 * e + 5) = 2 ^ P * (2 * 2 ^ (4 * e + 4)) := by ring
      rw [q2, q3]
      have h0 : (0 : ℤ) ≤ 2 ^ P := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) h0
    have : ((a i).natAbs : ℤ) ≤ ((2 ^ (P + 4 * e + 5) : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]; push_cast; exact hb
    exact_mod_cast this

/-- The frame centre for `d = 1`: numerator and denominator at most `2 M^4`. -/
theorem pb_frameQ_one {n m M : ℕ} (A : Matrix (Fin m) (Fin 1) ℚ) (b : Fin m → ℚ) (hM : Bit.RQ.frMhat A b ≤ M)
    (h1 : 1 ≤ M) (i : Fin 1) :
    (Bit.RQ.frameQ 1 n m A b i).num.natAbs ≤ 2 * M ^ 4 ∧ (Bit.RQ.frameQ 1 n m A b i).den ≤ 2 * M ^ 4 := by
  have hM4 : 1 ≤ M ^ 4 := Nat.one_le_pow _ _ h1
  unfold Bit.RQ.frameQ
  simp only [↓reduceDIte]
  generalize hf : Bit.RQ.frame1 (fun k => Bit.RQ.frAl A b k ⟨0, Nat.one_pos⟩) (Bit.RQ.frBe A b) = o
  cases o with
  | some c =>
    obtain ⟨i', j', hi, hj, rfl⟩ := pb_frame1_some _ _ hf
    dsimp only
    have bA := fun k => (Bit.Transfer.frAl_le A b k).2.1 ⟨0, Nat.one_pos⟩
    have bB := fun k => (Bit.Transfer.frAl_le A b k).2.2
    set al := fun k => Bit.RQ.frAl A b k ⟨0, Nat.one_pos⟩ with hal
    set be := Bit.RQ.frBe A b with hbe
    have hMz : (Bit.RQ.frMhat A b : ℤ) ≤ M := by exact_mod_cast hM
    have hM0 : (0 : ℤ) ≤ Bit.RQ.frMhat A b := by positivity
    have q : ∀ k, |al k| ≤ (M : ℤ) ^ 2 ∧ |be k| ≤ (M : ℤ) ^ 2 := fun k =>
      ⟨(bA k).trans (pow_le_pow_left₀ hM0 hMz 2), (bB k).trans (pow_le_pow_left₀ hM0 hMz 2)⟩
    have e : ((be i' : ℚ) / al i' + (be j' : ℚ) / al j') / 2 =
        (((be i' * al j' + be j' * al i' : ℤ) : ℚ) / ((2 * al i' * al j' : ℤ) : ℚ)) := by
      have hi' : (al i' : ℚ) ≠ 0 := by exact_mod_cast hi
      have hj' : (al j' : ℚ) ≠ 0 := by exact_mod_cast hj
      push_cast; field_simp
    rw [e]
    have hD : 2 * al i' * al j' ≠ 0 := by
      have := mul_ne_zero hi hj; intro h0; apply this; linarith
    obtain ⟨h1', h2'⟩ := pb_div_height _ _ hD
    obtain ⟨a1, b1⟩ := q i'
    obtain ⟨a2, b2⟩ := q j'
    have hM2 : (0 : ℤ) ≤ (M : ℤ) ^ 2 := by positivity
    have n1 : |be i' * al j' + be j' * al i'| ≤ 2 * (M : ℤ) ^ 4 := by
      calc |be i' * al j' + be j' * al i'| ≤ |be i'| * |al j'| + |be j'| * |al i'| := by
            rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
        _ ≤ (M : ℤ) ^ 2 * (M : ℤ) ^ 2 + (M : ℤ) ^ 2 * (M : ℤ) ^ 2 := by
            gcongr
        _ = 2 * (M : ℤ) ^ 4 := by ring
    have n2 : |2 * al i' * al j'| ≤ 2 * (M : ℤ) ^ 4 := by
      rw [abs_mul, abs_mul, abs_two]
      calc 2 * |al i'| * |al j'| ≤ 2 * (M : ℤ) ^ 2 * (M : ℤ) ^ 2 := by gcongr
        _ = 2 * (M : ℤ) ^ 4 := by ring
    refine ⟨h1'.trans ?_, h2'.trans ?_⟩
    · have : ((be i' * al j' + be j' * al i').natAbs : ℤ) ≤ ((2 * M ^ 4 : ℕ) : ℤ) := by
        rw [Int.natCast_natAbs]; push_cast; exact n1
      exact_mod_cast this
    · have : ((2 * al i' * al j').natAbs : ℤ) ≤ ((2 * M ^ 4 : ℕ) : ℤ) := by
        rw [Int.natCast_natAbs]; push_cast; exact n2
      exact_mod_cast this
  | none =>
    dsimp only
    simp only [Pi.zero_apply, Rat.num_zero, Int.natAbs_zero, Rat.den_zero]
    exact ⟨Nat.zero_le _, by omega⟩

/-- The height exponent of the frame centre. -/
def pbHB (d m M : ℕ) : ℕ := Bit.RQ.frP d + 4 * Bit.Transfer.frG d m M + 4 * M.size + 6

/-- The frame centre of an instance: numerators and denominators below `2^{pbHB d m M}`. -/
theorem pb_frameQ_height {n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    (hI : Bit.Asm.InputOK d n m M A b) (i : Fin d) :
    (Bit.RQ.frameQ d n m A b i).num.natAbs ≤ 2 ^ pbHB d m M ∧
      (Bit.RQ.frameQ d n m A b i).den ≤ 2 ^ pbHB d m M := by
  have hd := hI.hd
  obtain ⟨z, hz⟩ := hI.ball
  have hm := Bit.ApQ.m_pos_of_diam hd n A b hI.diam ⟨z, hz (Metric.mem_closedBall_self zero_le_one)⟩
  have hM1 : 1 ≤ M := le_trans (b ⟨0, hm⟩).den_pos (hI.height.2 ⟨0, hm⟩).2
  have hMh := Bit.Transfer.BLM.frMhat_le_M A b hI.height hM1
  have hpow : ∀ k k' : ℕ, k ≤ k' → (2 : ℕ) ^ k ≤ 2 ^ k' := fun k k' h => Nat.pow_le_pow_right (by norm_num) h
  rcases Nat.lt_or_ge d 2 with h1 | h2
  · obtain rfl : d = 1 := by omega
    obtain ⟨a1, a2⟩ := pb_frameQ_one (n := n) A b hMh hM1 i
    have hM4 : 2 * M ^ 4 ≤ 2 ^ pbHB 1 m M := by
      have q1 : M ^ 4 ≤ (2 ^ M.size) ^ 4 := Nat.pow_le_pow_left (Nat.lt_size_self M).le 4
      calc 2 * M ^ 4 ≤ 2 * (2 ^ M.size) ^ 4 := Nat.mul_le_mul_left _ q1
        _ = 2 ^ (4 * M.size + 1) := by ring
        _ ≤ 2 ^ pbHB 1 m M := hpow _ _ (by unfold pbHB; omega)
    exact ⟨a1.trans hM4, a2.trans hM4⟩
  · obtain ⟨a1, a2⟩ := pb_frameQ_ge2 (n := n) h2 A b i
    have heR : Bit.RQ.frER d m (Bit.RQ.frMhat A b) ≤ Bit.Transfer.frG d m M := by
      have q1 : Bit.RQ.frER d m (Bit.RQ.frMhat A b) ≤ Bit.Transfer.frG d m (Bit.RQ.frMhat A b) :=
        Nat.clog_le_of_le_pow (Bit.Transfer.frArg_le d m _)
      have q2 : Bit.Transfer.frG d m (Bit.RQ.frMhat A b) ≤ Bit.Transfer.frG d m M := by
        unfold Bit.Transfer.frG
        have hs := Nat.size_le_size hMh
        have : 2 * (d + 1) * Nat.size (Bit.RQ.frMhat A b) ≤ 2 * (d + 1) * Nat.size M := Nat.mul_le_mul_left _ hs
        exact Nat.mul_le_mul_left _ (by omega)
      exact q1.trans q2
    exact ⟨a1.trans (hpow _ _ (by unfold pbHB; omega)), a2.trans (hpow _ _ (by unfold pbHB; omega))⟩

/-! ## The size of Theorem U's input -/

theorem pb_len_le {z : ℤ} {N : ℕ} (h : z.natAbs ≤ N) : len z ≤ N.size := Nat.size_le_size h

theorem pb_size_succ (n : ℕ) : (n + 1).size ≤ n.size + 1 :=
  Nat.size_le.2 (by have := Nat.lt_size_self n; rw [pow_succ]; omega)

theorem pb_frP_le (d : ℕ) : Bit.RQ.frP d ≤ 3 * d + 8 := by
  unfold Bit.RQ.frP
  have h : d ^ 2 * (d + 1) ≤ 2 ^ (3 * d) := by
    have h1 : d < 2 ^ d := Nat.lt_two_pow_self
    have h2 : d ^ 2 ≤ (2 ^ d) ^ 2 := Nat.pow_le_pow_left h1.le 2
    calc d ^ 2 * (d + 1) ≤ (2 ^ d) ^ 2 * 2 ^ d := Nat.mul_le_mul h2 h1
      _ = 2 ^ (3 * d) := by ring
  have := Nat.clog_le_of_le_pow h
  omega

theorem pb_HB_le (d m M : ℕ) : pbHB d m M ≤ 33 * (d + m + M.size + 1) ^ 3 := by
  set V := d + m + M.size + 1 with hV
  have h1 := pb_frP_le d
  have h2 := Bit.Transfer.frG_le_W d m M
  rw [← hV] at h2
  have hV1 : V ≤ V ^ 3 := Nat.le_self_pow (by norm_num) V
  unfold pbHB
  omega

/-- The size of Theorem U's input `(δ, r₀, R₀, a) = (1/(n+1), 1/2, n, frameQ)`. -/
theorem pb_sizeU_le {n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} (hI : Bit.Asm.InputOK d n m M A b) :
    Unified.sizeU (δK n) (1 / 2) (n : ℚ) (Bit.RQ.frameQ d n m A b) ≤
      ((2 * n.size + 8 + d * (2 * pbHB d m M + 2) : ℕ) : ℝ) := by
  unfold Unified.sizeU
  apply Nat.cast_le.2
  have eδ : δK n = ((1 : ℤ) : ℚ) / (((n + 1 : ℕ) : ℤ) : ℚ) := by unfold δK; push_cast; ring
  have e2 : (1 / 2 : ℚ) = ((1 : ℤ) : ℚ) / ((2 : ℤ) : ℚ) := by norm_num
  obtain ⟨δ1, δ2⟩ := pb_div_height 1 ((n + 1 : ℕ) : ℤ) (by positivity)
  obtain ⟨h1, h2⟩ := pb_div_height 1 2 (by norm_num)
  rw [← eδ] at δ1 δ2
  rw [← e2] at h1 h2
  have l1 : len (δK n).num ≤ 1 := (pb_len_le δ1).trans (by simp)
  rw [Int.natAbs_natCast] at δ2
  have h2' : (1 / 2 : ℚ).den ≤ 2 := h2.trans (by norm_num)
  have l2 : len ((δK n).den : ℤ) ≤ n.size + 1 :=
    (pb_len_le (N := n + 1) (by rw [Int.natAbs_natCast]; exact δ2)).trans (pb_size_succ n)
  have l3 : len (1 / 2 : ℚ).num ≤ 1 := (pb_len_le h1).trans (by simp)
  have l4 : len ((1 / 2 : ℚ).den : ℤ) ≤ 2 :=
    (pb_len_le (N := 2) (by rw [Int.natAbs_natCast]; exact h2')).trans (Nat.size_le.2 (by norm_num))
  have l5 : len (n : ℚ).num ≤ n.size := by rw [Rat.num_natCast]; unfold len; simp
  have l6 : len ((n : ℚ).den : ℤ) ≤ 1 := by rw [Rat.den_natCast]; unfold len; simp
  have l7 : ∑ i, (len (Bit.RQ.frameQ d n m A b i).num + len ((Bit.RQ.frameQ d n m A b i).den : ℤ)) ≤
      d * (2 * pbHB d m M + 2) := by
    have hs : (2 ^ pbHB d m M).size = pbHB d m M + 1 := Nat.size_pow
    calc ∑ i, (len (Bit.RQ.frameQ d n m A b i).num + len ((Bit.RQ.frameQ d n m A b i).den : ℤ))
        ≤ ∑ _i : Fin d, (2 * pbHB d m M + 2) := Finset.sum_le_sum fun i _ => by
          obtain ⟨a1, a2⟩ := pb_frameQ_height hI i
          have q1 := pb_len_le a1
          have q2 := pb_len_le (z := ((Bit.RQ.frameQ d n m A b i).den : ℤ)) (N := 2 ^ pbHB d m M)
            (by rw [Int.natAbs_natCast]; exact a2)
          omega
      _ = d * (2 * pbHB d m M + 2) := by simp
  omega

/-- `log(2dn/δ)` at `δ = 1/(n+1)` lies in `[0, 3(d + size n + 1)]`. -/
theorem pb_log_le {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    0 ≤ Real.log (2 * d * n / ((δK n : ℚ) : ℝ)) ∧
      Real.log (2 * d * n / ((δK n : ℚ) : ℝ)) ≤ 3 * ((d + n.size + 1 : ℕ) : ℝ) := by
  have e : 2 * (d : ℝ) * n / ((δK n : ℚ) : ℝ) = ((2 * d * n * (n + 1) : ℕ) : ℝ) := by
    unfold δK; push_cast; field_simp
  rw [e]
  have h1 : 1 ≤ 2 * d * n * (n + 1) := by
    have : 1 ≤ d * n := Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith
  have hle : 2 * d * n * (n + 1) ≤ 2 ^ (3 * (d + n.size + 1)) := by
    have a1 : d ≤ 2 ^ d := Nat.lt_two_pow_self.le
    have a2 : n ≤ 2 ^ n.size := (Nat.lt_size_self n).le
    have a3 : n + 1 ≤ 2 ^ n.size := Nat.lt_size_self n
    calc 2 * d * n * (n + 1) ≤ 2 * 2 ^ d * 2 ^ n.size * 2 ^ n.size := by gcongr
      _ = 2 ^ (d + 2 * n.size + 1) := by ring
      _ ≤ 2 ^ (3 * (d + n.size + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨Real.log_nonneg (by exact_mod_cast h1), ?_⟩
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc Real.log ((2 * d * n * (n + 1) : ℕ) : ℝ) ≤ Real.log ((2 : ℝ) ^ (3 * (d + n.size + 1))) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < 2 * d * n * (n + 1))) (by exact_mod_cast hle)
    _ = ((3 * (d + n.size + 1) : ℕ) : ℝ) * Real.log 2 := by rw [Real.log_pow]
    _ ≤ ((3 * (d + n.size + 1) : ℕ) : ℝ) := by
        have : (0 : ℝ) ≤ ((3 * (d + n.size + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
        nlinarith
    _ = 3 * ((d + n.size + 1 : ℕ) : ℝ) := by push_cast; ring

/-! ## The bound -/

theorem pb_inSpace_le {n m M W : ℕ} (hW : d + m + n.size + M.size + 1 ≤ W) :
    Bit.Transfer.inSpace d n m M ≤ 45 * W ^ 4 := by
  unfold Bit.Transfer.inSpace Bit.Transfer.offOf
  have l1 := Bit.Transfer.BLM.len_natCast_le (3 + 2 * (d + 1) * m)
  have l2 := Bit.Transfer.BLM.len_natCast_le d
  have l3 : len (n : ℤ) = n.size := by unfold len; simp
  have l4 := Bit.Transfer.BLM.len_natCast_le m
  have l5 : len (M : ℤ) = M.size := by unfold len; simp
  have hW2 : W ≤ W ^ 2 := Nat.le_self_pow (by norm_num) W
  have hO : 3 + 2 * (d + 1) * m ≤ 5 * W ^ 2 := by
    have h1 : (d + 1) * m ≤ W * W := Nat.mul_le_mul (by omega) (by omega)
    have h2 : W * W = W ^ 2 := (sq W).symm
    have h3 : 1 ≤ W := by omega
    have h4 : 2 * (d + 1) * m = 2 * ((d + 1) * m) := by ring
    omega
  have hS : len ((3 + 2 * (d + 1) * m : ℕ) : ℤ) + (len (d : ℤ) + len (n : ℤ) + len (m : ℤ) + len (M : ℤ)) ≤
      9 * W ^ 2 := by omega
  calc (3 + 2 * (d + 1) * m) * (len ((3 + 2 * (d + 1) * m : ℕ) : ℤ) +
        (len (d : ℤ) + len (n : ℤ) + len (m : ℤ) + len (M : ℤ))) ≤ (5 * W ^ 2) * (9 * W ^ 2) := Nat.mul_le_mul hO hS
    _ = 45 * W ^ 4 := by ring

/-- `d + m + size n + size M + 1 ≤ 4 d m (size n + 1)(size M + 1)` for `d, m ≥ 1`. -/
theorem pb_sum_le_prod {n m M : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) :
    d + m + n.size + M.size + 1 ≤ 4 * (d * m * (n.size + 1) * (M.size + 1)) := by
  have p1 : d ≤ d * m := Nat.le_mul_of_pos_right d (by omega)
  have p2 : m ≤ d * m := Nat.le_mul_of_pos_left m (by omega)
  have p3 : d * m ≤ d * m * (n.size + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have p4 : n.size + 1 ≤ d * m * (n.size + 1) := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega))
  have p5 : d * m * (n.size + 1) ≤ d * m * (n.size + 1) * (M.size + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have p6 : M.size + 1 ≤ d * m * (n.size + 1) * (M.size + 1) :=
    Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
  omega

/-- **The bound of the machine clauses** for a compiler whose block constant `Kc` and prologue cost `Cpro` are
polynomial in the size of the instance: `Bmach` (inlined) at Theorem U's bound is at most
`C' (d m log(2dn) log(2M))^{k'}`. -/
theorem bound_mach_gen (Kc : ℕ → ℕ → ℕ → ℕ) (Cpro : ℕ → ℕ → ℕ → ℕ → ℕ) (K0 e : ℕ)
    (hK : ∀ d m M, Kc d m M ≤ K0 * (d + m + M.size + 1) ^ e)
    (hC : ∀ d n m M, Cpro d n m M ≤ K0 * (d + m + n.size + M.size + 1) ^ e)
    (CU' : ℝ) (kU : ℕ) : ∃ (C' : ℝ) (k' : ℕ), ∀ (d n m M : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ),
    Bit.Asm.InputOK d n m M A b →
    0 ≤ CU' * ((d : ℝ) * Real.log (2 * d * n / ((δK n : ℚ) : ℝ)) *
      Unified.sizeU (δK n) (1 / 2) (n : ℚ) (Bit.RQ.frameQ d n m A b)) ^ kU →
    ((2 * Cpro d n m M + 2 * (Kc d m M * ⌊CU' * ((d : ℝ) * Real.log (2 * d * n / ((δK n : ℚ) : ℝ)) *
      Unified.sizeU (δK n) (1 / 2) (n : ℚ) (Bit.RQ.frameQ d n m A b)) ^ kU⌋₊ ^ 3) : ℕ) : ℝ) +
      2 * (Bit.Transfer.inSpace d n m M : ℝ) +
      12 * (CU' * ((d : ℝ) * Real.log (2 * d * n / ((δK n : ℚ) : ℝ)) *
        Unified.sizeU (δK n) (1 / 2) (n : ℚ) (Bit.RQ.frameQ d n m A b)) ^ kU) ≤
      C' * ((d : ℝ) * m * Real.log (2 * d * n) * Real.log (2 * M)) ^ k' := by
  set c : ℝ := |CU'| * 240 ^ kU with hc
  set K : ℕ := e + 18 * kU + 4 with hKdef
  set C1 : ℝ := 2 * K0 + 2 * K0 * c ^ 3 + 90 + 12 * c with hC1
  refine ⟨C1 * 4 ^ K * (4 / Real.log 2 ^ 2) ^ K, K, ?_⟩
  intro d n m M A b hI hX0
  have hd := hI.hd
  have hn := hI.hn
  obtain ⟨z, hz⟩ := hI.ball
  have hm := Bit.ApQ.m_pos_of_diam hd n A b hI.diam ⟨z, hz (Metric.mem_closedBall_self zero_le_one)⟩
  have hM1 : 1 ≤ M := le_trans (b ⟨0, hm⟩).den_pos (hI.height.2 ⟨0, hm⟩).2
  have hF := Bit.Transfer.frozen_form d m n M K (C1 * 4 ^ K) (by positivity) hd hn hm hM1
  have hN := pb_sum_le_prod (n := n) (M := M) hd hm
  have hS := pb_sizeU_le hI
  have hHB := pb_HB_le d m M
  have hIn' := pb_inSpace_le (d := d) (n := n) (m := m) (M := M) (W := d + m + n.size + M.size + 1) le_rfl
  have hKc' := hK d m M
  have hCp' := hC d n m M
  obtain ⟨hL0, hL⟩ := pb_log_le (n := n) hd hn
  set W : ℕ := d + m + n.size + M.size + 1 with hW
  have hW1 : 1 ≤ W := by omega
  have hSW : 2 * n.size + 8 + d * (2 * pbHB d m M + 2) ≤ 80 * W ^ 4 := by
    have h1 : d + m + M.size + 1 ≤ W := by omega
    have h2 : (d + m + M.size + 1) ^ 3 ≤ W ^ 3 := Nat.pow_le_pow_left h1 3
    have h3 : d * (2 * pbHB d m M + 2) ≤ W * (66 * W ^ 3 + 2) := Nat.mul_le_mul (by omega) (by omega)
    have h4 : W * (66 * W ^ 3 + 2) = 66 * W ^ 4 + 2 * W := by ring
    have h5 : W ≤ W ^ 4 := Nat.le_self_pow (by norm_num) W
    omega
  set L := Real.log (2 * d * n / ((δK n : ℚ) : ℝ)) with hLdef
  set S := Unified.sizeU (δK n) (1 / 2) (n : ℚ) (Bit.RQ.frameQ d n m A b) with hSdef
  set X := CU' * ((d : ℝ) * L * S) ^ kU with hXdef
  set w : ℝ := (W : ℝ) with hw
  have hw1 : (1 : ℝ) ≤ w := by rw [hw]; exact_mod_cast hW1
  have hw0 : (0 : ℝ) ≤ w := by linarith
  have hS0 : 0 ≤ S := by simp only [hSdef, Unified.sizeU]; positivity
  have hSw : S ≤ 80 * w ^ 4 := hS.trans (by rw [hw]; exact_mod_cast hSW)
  have hLw : L ≤ 3 * w := by
    refine hL.trans ?_
    have : ((d + n.size + 1 : ℕ) : ℝ) ≤ w := by rw [hw]; exact_mod_cast (show d + n.size + 1 ≤ W by omega)
    linarith
  have hdw : (d : ℝ) ≤ w := by rw [hw]; exact_mod_cast (show d ≤ W by omega)
  have hY0 : 0 ≤ (d : ℝ) * L * S := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hL0) hS0
  have hY : (d : ℝ) * L * S ≤ 240 * w ^ 6 := by
    calc (d : ℝ) * L * S ≤ (w * (3 * w)) * (80 * w ^ 4) :=
          mul_le_mul (mul_le_mul hdw hLw hL0 hw0) hSw hS0 (mul_nonneg hw0 (by linarith))
      _ = 240 * w ^ 6 := by ring
  have hc0 : 0 ≤ c := by positivity
  have hX : X ≤ c * w ^ (6 * kU) := by
    calc X ≤ |CU'| * ((d : ℝ) * L * S) ^ kU := mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hY0 _)
      _ ≤ |CU'| * (240 * w ^ 6) ^ kU := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hY0 hY kU) (abs_nonneg _)
      _ = c * w ^ (6 * kU) := by rw [hc]; ring
  have hfl : (⌊X⌋₊ : ℝ) ≤ c * w ^ (6 * kU) := (Nat.floor_le hX0).trans hX
  have hfl3 : (⌊X⌋₊ : ℝ) ^ 3 ≤ c ^ 3 * w ^ (18 * kU) := by
    calc (⌊X⌋₊ : ℝ) ^ 3 ≤ (c * w ^ (6 * kU)) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hfl 3
      _ = c ^ 3 * w ^ (18 * kU) := by ring
  have hK0 : (0 : ℝ) ≤ K0 := Nat.cast_nonneg _
  have hKc : (Kc d m M : ℝ) ≤ K0 * w ^ e := by
    have h2 : (d + m + M.size + 1) ^ e ≤ W ^ e := Nat.pow_le_pow_left (by omega) e
    have : Kc d m M ≤ K0 * W ^ e := hKc'.trans (Nat.mul_le_mul_left _ h2)
    rw [hw]; exact_mod_cast this
  have hCp : (Cpro d n m M : ℝ) ≤ K0 * w ^ e := by rw [hw]; exact_mod_cast hCp'
  have hIn : (Bit.Transfer.inSpace d n m M : ℝ) ≤ 45 * w ^ 4 := by rw [hw]; exact_mod_cast hIn'
  have hp : ∀ j, j ≤ K → w ^ j ≤ w ^ K := fun j hj => pow_le_pow_right₀ hw1 hj
  have hLHS : ((2 * Cpro d n m M + 2 * (Kc d m M * ⌊X⌋₊ ^ 3) : ℕ) : ℝ) + 2 * (Bit.Transfer.inSpace d n m M : ℝ) +
      12 * X ≤ C1 * w ^ K := by
    push_cast
    have t1 : (Kc d m M : ℝ) * (⌊X⌋₊ : ℝ) ^ 3 ≤ K0 * c ^ 3 * w ^ (e + 18 * kU) := by
      calc (Kc d m M : ℝ) * (⌊X⌋₊ : ℝ) ^ 3 ≤ (K0 * w ^ e) * (c ^ 3 * w ^ (18 * kU)) :=
            mul_le_mul hKc hfl3 (by positivity) (by positivity)
        _ = K0 * c ^ 3 * w ^ (e + 18 * kU) := by ring
    have a1 : (Cpro d n m M : ℝ) ≤ K0 * w ^ K := hCp.trans (mul_le_mul_of_nonneg_left (hp e (by omega)) hK0)
    have a2 : (Kc d m M : ℝ) * (⌊X⌋₊ : ℝ) ^ 3 ≤ K0 * c ^ 3 * w ^ K :=
      t1.trans (mul_le_mul_of_nonneg_left (hp _ (by omega)) (by positivity))
    have a3 : (Bit.Transfer.inSpace d n m M : ℝ) ≤ 45 * w ^ K := hIn.trans (by linarith [hp 4 (by omega)])
    have a4 : X ≤ c * w ^ K := hX.trans (mul_le_mul_of_nonneg_left (hp _ (by omega)) hc0)
    rw [hC1]
    linarith
  refine hLHS.trans ?_
  have hC10 : 0 ≤ C1 := by positivity
  have hwp : w ≤ 4 * ((d : ℝ) * m * ((n.size : ℝ) + 1) * ((M.size : ℝ) + 1)) := by rw [hw]; exact_mod_cast hN
  have hpow : w ^ K ≤ 4 ^ K * ((d : ℝ) * m * ((n.size : ℝ) + 1) * ((M.size : ℝ) + 1)) ^ K := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hw0 hwp K
  calc C1 * w ^ K ≤ C1 * (4 ^ K * ((d : ℝ) * m * ((n.size : ℝ) + 1) * ((M.size : ℝ) + 1)) ^ K) :=
        mul_le_mul_of_nonneg_left hpow hC10
    _ = C1 * 4 ^ K * ((d : ℝ) * m * ((n.size : ℝ) + 1) * ((M.size : ℝ) + 1)) ^ K := by ring
    _ ≤ _ := hF

end AdversarialBco.UniPoly
