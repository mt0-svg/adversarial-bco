/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XVec

@[expose] public section

/-!
# Euclid's algorithm on the machine

`xgcd L z sa sb st`: `while 0 < sb: st := sa / sb; st := st * sb; st := sa - st; sa := sb; sb := st` (the Euclidean
quotient of the leaf `idiv`, so `st` ends as `sa % sb`), with `z` a slot holding `0`. From `sa = a`, `sb = b > 0` it
ends with `sa = gcd(a, b)` (`Int.gcd`) and `sb = 0`, after at most `2 s + 1` turns when `b ≤ 2^s`.

* `euStep`, `euIt`: the pure iteration, `(a, b) ↦ (b, a % b)`, `(a, 0)` kept.
* `euIt_gcd`, `euIt_nonneg`, `euIt_le`, `euIt_turns`, `euIt_fin`: the gcd is kept, the pairs are nonnegative and at
  most `b` after the first turn, a positive `b` after `t` turns forces `t ≤ 2 s`, the last pair is `(gcd, 0)`.
* `XV.gcd`: the rule, within `gcdUnits s = (2 s + 1) 7 + 2` units, every value below `2^(s + 1)`.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach

variable {d : ℕ}

/-! ## The pure iteration -/

/-- One step of Euclid's algorithm: `(a, b) ↦ (b, a % b)`, the pair `(a, 0)` kept. -/
def euStep (p : ℤ × ℤ) : ℤ × ℤ := if p.2 = 0 then p else (p.2, p.1 % p.2)

/-- `t` steps of Euclid's algorithm from `p`. -/
def euIt (p : ℤ × ℤ) : ℕ → ℤ × ℤ
  | 0 => p
  | t + 1 => euStep (euIt p t)

theorem euIt_one {p : ℤ × ℤ} (hb : p.2 ≠ 0) : euIt p 1 = (p.2, p.1 % p.2) := by
  show euStep p = _
  unfold euStep
  rw [ite_eq_right_iff.mpr (fun h => absurd h hb)]

theorem euStep_gcd (p : ℤ × ℤ) : Int.gcd (euStep p).1 (euStep p).2 = Int.gcd p.1 p.2 := by
  unfold euStep
  split_ifs with h
  · rfl
  · simp only
    rw [Int.gcd_comm, Int.gcd_emod]

/-- The gcd is kept along the iteration. -/
theorem euIt_gcd (p : ℤ × ℤ) : ∀ t, Int.gcd (euIt p t).1 (euIt p t).2 = Int.gcd p.1 p.2
  | 0 => rfl
  | t + 1 => by rw [euIt, euStep_gcd, euIt_gcd p t]

/-- Once `b = 0` the pair stays. -/
theorem euIt_zero {p : ℤ × ℤ} {t : ℕ} (h : (euIt p t).2 = 0) : ∀ u, euIt p (t + u) = euIt p t
  | 0 => rfl
  | u + 1 => by
    rw [← Nat.add_assoc, euIt, euIt_zero h u]
    unfold euStep
    rw [ite_eq_left_iff.mpr (fun h' => absurd h h')]

/-- A positive `b` after `t` steps was positive at every earlier step. -/
theorem euIt_pos_of_le {p : ℤ × ℤ} {t u : ℕ} (hu : u ≤ t) (h : (euIt p t).2 ≠ 0) : (euIt p u).2 ≠ 0 := by
  intro h0
  have := euIt_zero h0 (t - u)
  rw [Nat.add_sub_cancel' hu] at this
  rw [this] at h
  exact h h0

/-- After the first step, with `b > 0` at the start: `0 ≤ b_t ≤ a_t ≤ b`, and `b_t < a_t` when `b_t > 0`. -/
theorem euIt_le {p : ℤ × ℤ} (hb : 0 < p.2) :
    ∀ t, 1 ≤ t → 0 ≤ (euIt p t).2 ∧ (euIt p t).2 ≤ (euIt p t).1 ∧ (euIt p t).1 ≤ p.2 ∧
      ((euIt p t).2 ≠ 0 → (euIt p t).2 < (euIt p t).1)
  | 0, h => absurd h (by norm_num)
  | 1, _ => by
    rw [euIt_one hb.ne']
    refine ⟨Int.emod_nonneg _ hb.ne', (Int.emod_lt_of_pos _ hb).le, le_rfl, fun _ => Int.emod_lt_of_pos _ hb⟩
  | t + 2, _ => by
    obtain ⟨h1, h2, h3, h4⟩ := euIt_le hb (t + 1) (by omega)
    rw [euIt]
    unfold euStep
    split_ifs with h0
    · exact ⟨h1, h2, h3, h4⟩
    · have hp : 0 < (euIt p (t + 1)).2 := lt_of_le_of_ne h1 (Ne.symm h0)
      simp only
      exact ⟨Int.emod_nonneg _ h0, (Int.emod_lt_of_pos _ hp).le, by linarith [h4 h0],
        fun _ => Int.emod_lt_of_pos _ hp⟩

theorem euIt_nonneg {p : ℤ × ℤ} (hb : 0 < p.2) {t : ℕ} (ht : 1 ≤ t) : 0 ≤ (euIt p t).1 ∧ 0 ≤ (euIt p t).2 := by
  obtain ⟨h1, h2, -, -⟩ := euIt_le hb t ht
  exact ⟨by linarith, h1⟩

/-- The potential: `3 (a' + b') ≤ 2 (a + b)` at a step from `b ≤ a`, `b > 0`. -/
theorem euStep_pot {a b : ℤ} (hb : 0 < b) (hba : b ≤ a) : 3 * (b + a % b) ≤ 2 * (a + b) := by
  have e := Int.emod_def a b
  have hq : 1 ≤ a / b := by
    rw [Int.le_ediv_iff_mul_le hb]; linarith
  have hr := Int.emod_nonneg a hb.ne'
  have hr' := Int.emod_lt_of_pos a hb
  nlinarith

/-- The potential after `t ≥ 1` steps: `3^(t-1) (a_t + b_t) ≤ 2^(t-1) (a_1 + b_1)` while `b` stays positive. -/
theorem euIt_pot {p : ℤ × ℤ} (hb : 0 < p.2) :
    ∀ t, (euIt p (t + 1)).2 ≠ 0 →
      3 ^ t * ((euIt p (t + 1)).1 + (euIt p (t + 1)).2) ≤ 2 ^ t * ((euIt p 1).1 + (euIt p 1).2)
  | 0, _ => by simp
  | t + 1, h => by
    have h' : (euIt p (t + 1)).2 ≠ 0 := euIt_pos_of_le (by omega) h
    have ih := euIt_pot hb t h'
    obtain ⟨g1, g2, -, g4⟩ := euIt_le hb (t + 1) (by omega)
    have hp : 0 < (euIt p (t + 1)).2 := lt_of_le_of_ne g1 (Ne.symm h')
    have key := euStep_pot hp g2
    have e : euIt p (t + 1 + 1) = ((euIt p (t + 1)).2, (euIt p (t + 1)).1 % (euIt p (t + 1)).2) := by
      rw [euIt]; unfold euStep; simp only [h', ↓reduceIte]
    rw [e]
    simp only
    have h3 : (0 : ℤ) ≤ 3 ^ t := by positivity
    calc 3 ^ (t + 1) * ((euIt p (t + 1)).2 + (euIt p (t + 1)).1 % (euIt p (t + 1)).2)
        = 3 ^ t * (3 * ((euIt p (t + 1)).2 + (euIt p (t + 1)).1 % (euIt p (t + 1)).2)) := by ring
      _ ≤ 3 ^ t * (2 * ((euIt p (t + 1)).1 + (euIt p (t + 1)).2)) := mul_le_mul_of_nonneg_left key h3
      _ = 2 * (3 ^ t * ((euIt p (t + 1)).1 + (euIt p (t + 1)).2)) := by ring
      _ ≤ 2 * (2 ^ t * ((euIt p 1).1 + (euIt p 1).2)) := by linarith
      _ = 2 ^ (t + 1) * ((euIt p 1).1 + (euIt p 1).2) := by ring

/-- `(3/2)^(2s+1) > 2^s`, in integers. -/
theorem three_pow_gt (s : ℕ) : (2 : ℤ) ^ (2 * s + 1) * 2 ^ s < 3 ^ (2 * s + 1) := by
  have h : (8 : ℤ) ^ s ≤ 9 ^ s := pow_le_pow_left₀ (by norm_num) (by norm_num) s
  have e1 : (2 : ℤ) ^ (2 * s + 1) * 2 ^ s = 2 * 8 ^ s := by
    rw [show (8 : ℤ) = 2 ^ 3 by norm_num, ← pow_mul]; ring
  have e2 : (3 : ℤ) ^ (2 * s + 1) = 3 * 9 ^ s := by
    rw [show (9 : ℤ) = 3 ^ 2 by norm_num, ← pow_mul]; ring
  rw [e1, e2]
  have : (0 : ℤ) < 8 ^ s := by positivity
  linarith

/-- **The number of turns**: from `b ≤ 2^s`, `b > 0`, a positive `b` after `t` steps forces `t ≤ 2 s`. -/
theorem euIt_turns {p : ℤ × ℤ} {s : ℕ} (hb : 0 < p.2) (hs : p.2 ≤ 2 ^ s) {t : ℕ} (h : 0 < (euIt p t).2) :
    t ≤ 2 * s := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  have hpot := euIt_pot hb u h.ne'
  obtain ⟨g1, g2, -, g4⟩ := euIt_le hb (u + 1) (by omega)
  have g5 := g4 h.ne'
  -- `a_1 + b_1 < 2 b ≤ 2^(s+1)`
  have h1 : (euIt p 1).1 + (euIt p 1).2 < 2 ^ (s + 1) := by
    rw [euIt_one hb.ne']
    have := Int.emod_lt_of_pos p.1 hb
    rw [pow_succ]; linarith
  -- `a_t + b_t ≥ 3`
  have h3 : 3 ≤ (euIt p (u + 1)).1 + (euIt p (u + 1)).2 := by linarith
  have hu : 2 * s ≤ u := by omega
  have A : (3 : ℤ) ^ u * 3 ≤ 2 ^ u * 2 ^ (s + 1) := by
    have h2u : (0 : ℤ) ≤ 2 ^ u := by positivity
    have h3u : (0 : ℤ) ≤ 3 ^ u := by positivity
    nlinarith
  -- `3^(u+1) ≤ 2^(u+s+1)`, against `three_pow_gt`
  obtain ⟨v, rfl⟩ : ∃ v, u = 2 * s + v := ⟨u - 2 * s, by omega⟩
  have B := three_pow_gt s
  have C : (2 : ℤ) ^ v ≤ 3 ^ v := pow_le_pow_left₀ (by norm_num) (by norm_num) v
  have e1 : (3 : ℤ) ^ (2 * s + v) * 3 = 3 ^ (2 * s + 1) * 3 ^ v := by ring
  have e2 : (2 : ℤ) ^ (2 * s + v) * 2 ^ (s + 1) = (2 ^ (2 * s + 1) * 2 ^ s) * 2 ^ v := by ring
  rw [e1, e2] at A
  have hv : (0 : ℤ) < 2 ^ v := by positivity
  have : (2 : ℤ) ^ (2 * s + 1) * 2 ^ s * 2 ^ v < 3 ^ (2 * s + 1) * 3 ^ v :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_right B hv) (mul_le_mul_of_nonneg_left C (by positivity))
  linarith

/-- **The end**: from `b > 0`, a pair `(a_t, 0)` has `a_t = gcd(a, b)`. -/
theorem euIt_fin {p : ℤ × ℤ} (hb : 0 < p.2) {t : ℕ} (h : (euIt p t).2 = 0) : (euIt p t).1 = Int.gcd p.1 p.2 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact absurd h hb.ne'
  have hg := euIt_gcd p t
  rw [h, Int.gcd_zero_right] at hg
  rw [← hg, Int.natAbs_of_nonneg (euIt_nonneg hb ht).1]

/-! ## The machine -/

/-- One turn of Euclid's algorithm: `st := sa / sb; st := st * sb; st := sa - st; sa := sb + z; sb := st + z`. -/
def xgcdBody (L : Layout) (z sa sb st : ℕ) : XCmd :=
  .seq (xsidiv L st sa sb) (.seq (toX (VL.sop2 L .mul st st sb))
    (.seq (toX (VL.sop2 L .sub st sa st)) (.seq (toX (VL.sop2 L .add sa sb z)) (toX (VL.sop2 L .add sb st z)))))

/-- Euclid's algorithm: `while 0 < sb` do the turn. -/
def xgcd (L : Layout) (z sa sb st : ℕ) : XCmd := xwhileS L z sb (xgcdBody L z sa sb st)

/-- The units of `xgcd` from `b ≤ 2^s`. -/
def gcdUnits (s : ℕ) : ℕ := (2 * s + 1) * (1 + (1 + (1 + (1 + 1))) + 2) + 2

theorem absI_le_pow {x : ℤ} {s ℓ : ℕ} (h : |x| ≤ 2 ^ s) (hs : s < ℓ) : |x| < 2 ^ ℓ :=
  lt_of_le_of_lt h (pow_lt_pow_right₀ (by norm_num) hs)

set_option maxHeartbeats 1000000 in
/-- **The rule of `xgcd`**: from `sa = a`, `sb = b`, `0 < b ≤ 2^s`, `|a| ≤ 2^s`, `s + 1 < ℓ`, the slot `sa` ends as
`gcd(a, b)` and `sb` as `0`; only `sa`, `sb`, `st` change. -/
theorem XV.gcd {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {z sa sb st : ℕ}
    (hz : z < L.NS) (ha : sa < L.NS) (hb : sb < L.NS) (ht : st < L.NS) (hne : [z, sa, sb, st].Nodup)
    {a b : ℤ} {s : ℕ} (hz0 : σ.sc z = 0) (hσa : σ.sc sa = a) (hσb : σ.sc sb = b) (hb0 : 0 < b)
    (ba : |a| ≤ 2 ^ s) (bb : b ≤ 2 ^ s) (hs : s + 1 < ℓ) :
    XRunsB L X ℓa ℓ (xgcd L z sa sb st) σ (gcdUnits s) (fun σ' =>
      σ'.sc sa = ((Int.gcd a b : ℤ) : ℝ) ∧ σ'.sc sb = 0 ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = sa ∨ y = sb ∨ y = st) (fun _ => False) (fun _ _ => False) σ σ') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne
  obtain ⟨⟨za, zb, zt⟩, ⟨ab, at'⟩, bt⟩ := hne
  have bt : sb ≠ st := bt.1
  set p : ℤ × ℤ := (a, b) with hp
  have hpb : 0 < p.2 := hb0
  -- the values stay below `2^s`
  have bnd : ∀ t, |(euIt p t).1| ≤ 2 ^ s ∧ |(euIt p t).2| ≤ 2 ^ s := by
    intro t
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · exact ⟨ba, show |b| ≤ 2 ^ s by rw [abs_of_pos hb0]; exact bb⟩
    · obtain ⟨h1, h2, h3, -⟩ := euIt_le hpb t ht
      exact ⟨by rw [abs_of_nonneg (by linarith)]; exact h3.trans bb, by rw [abs_of_nonneg h1]; linarith⟩
  have hs' : s < ℓ := by omega
  let I : ℕ → Env d → Prop := fun t σ' => σ'.sc sa = (euIt p t).1 ∧ σ'.sc sb = (euIt p t).2 ∧
    σ'.draws = σ.draws ∧ FrameA (fun y => y = sa ∨ y = sb ∨ y = st) (fun _ => False) (fun _ _ => False) σ σ'
  have hloop := XV.whileS (L := L) (X := X) (ℓa := ℓa) (ℓ := ℓ) (x := z) (y := sb) (c := xgcdBody L z sa sb st) hL hz hb I (2 * s + 1)
    (1 + (1 + (1 + (1 + 1))))
    (fun t σ' hI => by
      obtain ⟨-, h2, -, hF⟩ := hI
      refine ⟨?_, ?_⟩
      · rw [hF.2.1 z (by omega), hz0, abs_zero]; positivity
      · rw [h2]; exact XV.abs_int_lt (absI_le_pow (bnd t).2 hs'))
    (fun t σ' hI hc => by
      obtain ⟨-, h2, -, hF⟩ := hI
      rw [hF.2.1 z (by omega), hz0, h2] at hc
      have := euIt_turns hpb bb (t := t) (by exact_mod_cast hc)
      omega)
    (fun t σ' hI hc => by
      obtain ⟨h1, h2, h3, hF⟩ := hI
      have hz' : σ'.sc z = 0 := by rw [hF.2.1 z (by omega), hz0]
      rw [hz', h2] at hc
      have hbt : 0 < (euIt p t).2 := by exact_mod_cast hc
      set u := (euIt p t).1 with hu
      set v := (euIt p t).2 with hv
      have bu := absI_le_pow (bnd t).1 hs'
      have bv := absI_le_pow (bnd t).2 hs'
      -- st := u / v
      refine XV.seq (XV.divI hL ht ha hb h1 h2 bu bv) fun σ1 e1 => ?_
      subst e1
      have bq : |u / v| ≤ 2 ^ s := (absI_ediv_le u v).trans (bnd t).1
      -- st := (u / v) * v
      have bqv : |u / v * v| ≤ 2 ^ (s + 1) := by
        have e : u / v * v = u - u % v := by rw [Int.emod_def]; ring
        rw [e]
        have r0 := Int.emod_nonneg u hbt.ne'
        have r1 := Int.emod_lt_of_pos u hbt
        have := (bnd t).1
        have := (bnd t).2
        rw [abs_le] at *
        rw [pow_succ]
        constructor <;> linarith
      refine XV.seq (XV.mulI hL ht ht hb (u := u / v) (v := v) (by simp) (by simp [bt, h2])
        (absI_le_pow bq hs') bv (absI_le_pow bqv (by omega))) fun σ2 e2 => ?_
      subst e2
      -- st := u - (u / v) * v = u % v
      have er : u - u / v * v = u % v := by rw [Int.emod_def]; ring
      have br : |u % v| ≤ 2 ^ s := by
        rw [abs_of_nonneg (Int.emod_nonneg u hbt.ne')]
        have := Int.emod_lt_of_pos u hbt
        have := (bnd t).2
        rw [abs_of_pos hbt] at this
        linarith
      refine XV.seq (XV.subI hL ht ha ht (u := u) (v := u / v * v) (by simp [at', h1]) (by simp)
        bu (absI_le_pow bqv (by omega)) (by rw [er]; exact absI_le_pow br hs')) fun σ3 e3 => ?_
      subst e3
      -- sa := v
      refine XV.seq (XV.addI hL ha hb hz (u := v) (v := 0) (by simp [bt, h2]) (by simp [zt, hz'])
        bv (by simp) (by simpa using bv)) fun σ4 e4 => ?_
      subst e4
      -- sb := u % v
      refine XV.mono (XV.addI hL hb ht hz (u := u % v) (v := 0) (by simp [Ne.symm at', er]) (by simp [zt, za, hz'])
        (absI_le_pow br hs') (by simp) (by simpa using absI_le_pow br hs')) le_rfl fun σ5 e5 => ?_
      subst e5
      have estep : euIt p (t + 1) = (v, u % v) := by
        rw [euIt]; unfold euStep; rw [ite_eq_right_of_eq_false _ _ (eq_false hbt.ne')]
      refine ⟨?_, ?_, by simp [h3], ?_⟩
      · simp [ab, estep]
      · simp [estep]
      · exact (((hF.setSc (Or.inr (Or.inr rfl)) _).setSc (Or.inr (Or.inr rfl)) _ |>.setSc (Or.inr (Or.inr rfl)) _
          |>.setSc (Or.inl rfl) _).setSc (Or.inr (Or.inl rfl)) _))
  refine XV.mono (hloop 0 σ ⟨by rw [hσa]; rfl, by rw [hσb]; rfl, rfl, FrameA.refl _ _ _ σ⟩) (by unfold gcdUnits; omega)
    fun σ' ⟨t', ⟨h1, h2, h3, hF⟩, hc⟩ => ?_
  rw [hF.2.1 z (by omega), hz0, h2] at hc
  have h0 : (euIt p t').2 = 0 := by
    rcases Nat.eq_zero_or_pos t' with rfl | ht'
    · exact absurd (by exact_mod_cast hb0) hc
    · have := (euIt_nonneg hpb ht').2
      have : ¬ (0 : ℤ) < (euIt p t').2 := fun h => hc (by exact_mod_cast h)
      omega
  refine ⟨by rw [h1, euIt_fin hpb h0], by rw [h2, h0]; simp, h3, hF⟩

/-! ## The reduced form of a fraction -/

/-- Reads registers and slots of an environment built by `setNat`, `setSc`, `setArr`; disequalities by `omega`. -/
macro "rpenv" : tactic =>
  `(tactic| (simp (disch := omega) only [nat_setNat_ne, nat_setNat_eq, sc_setSc_ne, sc_setSc_eq,
    Env.setNat_sc, Env.setSc_nat, Env.setArr_nat, Env.setArr_sc, Env.setNat_arr, Env.setSc_arr, Env.setNat_draws,
    Env.setSc_draws, Env.setArr_draws]))

/-- `sa := sN; sb := sD; xgcd; snum := sN / sa; sden := sD / sa`: the numerator and the denominator of `N / D` divided
by `gcd(N, D)`. -/
def xred (L : Layout) (z sN sD sa sb st snum sden : ℕ) : XCmd :=
  .seq (toX (VL.sop2 L .add sa sN z)) (.seq (toX (VL.sop2 L .add sb sD z)) (.seq (xgcd L z sa sb st)
    (.seq (xsidiv L snum sN sa) (xsidiv L sden sD sa))))

/-- The units of `xred`. -/
def redUnits (s : ℕ) : ℕ := 1 + (1 + (gcdUnits s + (1 + 1)))

set_option maxHeartbeats 1000000 in
/-- **The rule of `xred`**: from `sN = N`, `sD = D`, `0 < D ≤ 2^s`, `|N| ≤ 2^s`, `s + 1 < ℓ`, the slots `snum`, `sden`
end as `N / gcd(N, D)` and `D / gcd(N, D)`; only `sa`, `sb`, `st`, `snum`, `sden` change. -/
theorem XV.red {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {z sN sD sa sb st snum sden : ℕ} (hz : z < L.NS) (hN : sN < L.NS) (hD : sD < L.NS) (ha : sa < L.NS)
    (hb : sb < L.NS) (ht : st < L.NS) (hn : snum < L.NS) (hd : sden < L.NS)
    (hne : [z, sN, sD, sa, sb, st, snum, sden].Nodup) {N D : ℤ} {s : ℕ} (hz0 : σ.sc z = 0) (hσN : σ.sc sN = N)
    (hσD : σ.sc sD = D) (hD0 : 0 < D) (bN : |N| ≤ 2 ^ s) (bD : D ≤ 2 ^ s) (hs : s + 1 < ℓ) :
    XRunsB L X ℓa ℓ (xred L z sN sD sa sb st snum sden) σ (redUnits s) (fun σ' =>
      σ'.sc snum = ((N / (Int.gcd N D : ℤ) : ℤ) : ℝ) ∧ σ'.sc sden = ((D / (Int.gcd N D : ℤ) : ℤ) : ℝ) ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => y = sa ∨ y = sb ∨ y = st ∨ y = snum ∨ y = sden) (fun _ => False) (fun _ _ => False) σ σ') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne
  obtain ⟨⟨zN, zD, za, zb, zt, zn, zd⟩, ⟨ND, Na, Nb, Nt, Nn, Nd⟩, ⟨Da, Db, Dt, Dn, Dd⟩, ⟨ab, at', an, ad⟩,
    ⟨bt, bn, bd⟩, ⟨tn, td⟩, nd⟩ := hne
  have hs' : s < ℓ := by omega
  have bN' := absI_le_pow bN hs'
  have bD' : |D| < 2 ^ ℓ := absI_le_pow (by rw [abs_of_pos hD0]; exact bD) hs'
  refine XV.seq (XV.addI hL ha hN hz (u := N) (v := 0) hσN (by rw [hz0]; simp) bN' (by simp)
    (by simpa using bN')) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.addI hL hb hD hz (u := D) (v := 0) (by rpenv; rw [hσD])
    (by rpenv; rw [hz0]; simp) bD' (by simp) (by simpa using bD')) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.gcd hL hz ha hb ht (by simp [za, zb, zt, ab, at', bt]) (a := N) (b := D) (s := s)
    (by rpenv; exact hz0) (by rpenv; simp) (by rpenv; simp) hD0 bN bD (by omega)) fun σ3 ⟨g1, g2, g3, g4⟩ => ?_
  have e3N : σ3.sc sN = N := by rw [g4.2.1 sN (by omega)]; rpenv; exact hσN
  have e3D : σ3.sc sD = D := by rw [g4.2.1 sD (by omega)]; rpenv; exact hσD
  have hg : (1 : ℤ) ≤ (Int.gcd N D : ℤ) := by
    have := Int.gcd_pos_of_ne_zero_right N hD0.ne'
    omega
  have bg : |(Int.gcd N D : ℤ)| < 2 ^ ℓ := by
    rw [abs_of_pos (by omega)]
    have := Int.le_of_dvd hD0 (Int.gcd_dvd_right N D)
    have : |D| < 2 ^ ℓ := bD'
    rw [abs_of_pos hD0] at this
    omega
  refine XV.seq (XV.divI hL hn hN ha (u := N) (v := (Int.gcd N D : ℤ)) e3N g1 bN' bg) fun σ4 e4 => ?_
  subst e4
  refine XV.mono (XV.divI hL hd hD ha (u := D) (v := (Int.gcd N D : ℤ)) (by rpenv; exact e3D)
    (by rpenv; exact g1) bD' bg) le_rfl fun σ5 e5 => ?_
  subst e5
  refine ⟨by rpenv, by rpenv, by rpenv; exact g3, ?_⟩
  have hF : FrameA (fun y => y = sa ∨ y = sb ∨ y = st ∨ y = snum ∨ y = sden) (fun _ => False) (fun _ _ => False)
      σ σ3 :=
    ((FrameA.refl _ _ _ σ).setSc (Or.inl rfl) _ |>.setSc (Or.inr (Or.inl rfl)) _).trans
      (g4.mono (fun y h => by rcases h with h | h | h <;> simp [h]) (fun _ h => h) (fun _ _ h => h))
  exact (hF.setSc (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _).setSc (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) _

end AdversarialBco.Bit.Transfer
