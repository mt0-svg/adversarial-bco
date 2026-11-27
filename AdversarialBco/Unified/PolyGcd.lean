/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PolyBlk4
public import AdversarialBco.Bit.Transfer.XGcd

@[expose] public section

/-!
# UNI-POLY, part 13: Euclid's algorithm for the setup of `P`'s input

The setup writes `P`'s input, the frame centre among it, with every coordinate in lowest terms; the reduction is
Euclid's algorithm on the cells `zA`, `zB` (`zQ` the remainder), at most `2 s + 1` turns for a denominator below `2^s`
(`euIt_turns`, XGcd.lean).

* `GCD`: `while 0 < zB: zQ := zA / zB; zQ := zQ zB; zQ := zA - zQ; zA := zB; zB := zQ; zQ := 0`.
* `rs_GCD`: from `zA = a`, `zB = b > 0`, `zQ = 0`, it ends with `zA = gcd(a, b)`, `zB = 0`.
-/

namespace AdversarialBco.UniPoly

open AdversarialBco BitRAM RCmd
open AdversarialBco.Bit.Transfer (euIt euStep euIt_le euIt_nonneg euIt_turns euIt_fin)

/-! ## The cells of the setup (above `-N0`, below the scratch cells of the blocks) -/

scoped notation "zOne" => (-700 : ℤ)
scoped notation "zFB" => (-701 : ℤ)
scoped notation "zD" => (-702 : ℤ)
scoped notation "zJ" => (-703 : ℤ)
scoped notation "zX" => (-704 : ℤ)
scoped notation "zA" => (-705 : ℤ)
scoped notation "zB" => (-706 : ℤ)
scoped notation "zQ" => (-707 : ℤ)
scoped notation "zN" => (-708 : ℤ)
scoped notation "zDn" => (-709 : ℤ)
scoped notation "zP" => (-710 : ℤ)
scoped notation "zFour" => (-711 : ℤ)
scoped notation "zP0" => (-712 : ℤ)
scoped notation "zTwo" => (-713 : ℤ)
scoped notation "zT" => (-714 : ℤ)

/-- Euclid's algorithm on `zA`, `zB`. -/
def GCD : RCmd :=
  .whileLt cZ zB (seqI [.div zQ zA zB, .mul zQ zQ zB, .sub zQ zA zQ, .add zA zB cZ, .add zB zQ cZ, .const zQ 0])

variable {d : ℕ} {w : World d} {L : ℕ}

theorem euIt_bounds {a b : ℤ} {s : ℕ} (hb : 0 < b) (ha : |a| < 2 ^ s) (hbs : b < 2 ^ s) (k : ℕ) :
    |(euIt (a, b) k).1| < 2 ^ s ∧ 0 ≤ (euIt (a, b) k).2 ∧ (euIt (a, b) k).2 < 2 ^ s := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨ha, hb.le, hbs⟩
  · obtain ⟨h1, h2, h3, -⟩ := euIt_le (p := (a, b)) hb k hk
    have h0 := (euIt_nonneg (p := (a, b)) hb hk).1
    refine ⟨?_, h1, by simp only at h3; omega⟩
    rw [abs_of_nonneg h0]; simp only at h3; omega

theorem euIt_stop {a b : ℤ} {s : ℕ} (hb : 0 < b) (hbs : b ≤ 2 ^ s) : (euIt (a, b) (2 * s + 1)).2 = 0 := by
  by_contra h
  have h0 := (euIt_nonneg (p := (a, b)) hb (t := 2 * s + 1) (by omega)).2
  have := euIt_turns (p := (a, b)) (s := s) hb hbs (t := 2 * s + 1) (lt_of_le_of_ne h0 (Ne.symm h))
  omega

set_option maxHeartbeats 1000000 in
/-- **Euclid's algorithm**: `zA := gcd(a, b)`, `zB := 0`. -/
theorem rs_GCD {u0 : State d} {a b : ℤ} {s : ℕ} (hA : u0.mem zA = a) (hB : u0.mem zB = b) (hQ : u0.mem zQ = 0)
    (hz : u0.mem cZ = 0) (hb : 0 < b) (has : |a| < 2 ^ s) (hbs : b < 2 ^ s) (hL : s + 2 ≤ L) (h10 : 10 ≤ L) :
    RS w L GCD u0 (fun n u => n ≤ (2 * s + 1) * 8 + 2 ∧
      u.mem = Function.update (Function.update u0.mem zA (Int.gcd a b)) zB 0 ∧ Same' u0 u) := by
  have hex : ∃ k, (euIt (a, b) k).2 = 0 := ⟨_, euIt_stop (s := s) hb hbs.le⟩
  classical
  set K := Nat.find hex with hK
  have hKs : K ≤ 2 * s + 1 := Nat.find_min' hex (euIt_stop (s := s) hb hbs.le)
  have hKz : (euIt (a, b) K).2 = 0 := Nat.find_spec hex
  have hpos : ∀ k < K, 0 < (euIt (a, b) k).2 := fun k hk => by
    have h1 := Nat.find_min hex hk
    have h2 := (euIt_bounds (s := s) hb has hbs k).2.1
    omega
  have l0 : len (0 : ℤ) ≤ L := by rw [len_zero]; omega
  have lS : ∀ x : ℤ, |x| < 2 ^ (s + 1) → len x ≤ L := fun x hx =>
    len_of_abs le_rfl (hx.trans_le (pow_le_pow_right₀ (by norm_num) (by omega)))
  have hs1 : (2 : ℤ) ^ s < 2 ^ (s + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  unfold GCD
  refine RS.loop (fun k u => k ≤ K ∧ u.mem = Function.update (Function.update u0.mem zA (euIt (a, b) k).1) zB
      (euIt (a, b) k).2 ∧ Same' u0 u) K 6 ⟨Nat.zero_le K, ?_, Same'.refl _⟩ ?_ ?_ ?_
  · show u0.mem = Function.update (Function.update u0.mem zA a) zB b
    rw [← hA, ← hB, Function.update_eq_self, Function.update_eq_self]
  · rintro k u ⟨hk, hu, -⟩
    obtain ⟨e1, e2, e3⟩ := euIt_bounds (s := s) hb has hbs k
    have fz : u.mem cZ = 0 := by rw [hu]; evl; exact hz
    have fB : u.mem zB = (euIt (a, b) k).2 := by rw [hu]; evl
    refine ⟨⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, by rw [fz]; exact l0,
      by rw [fB]; exact lS _ (by rw [abs_of_nonneg e2]; omega)⟩, ?_⟩
    rw [fz, fB]
    constructor
    · intro h; by_contra hkK
      have : k = K := by omega
      rw [this, hKz] at h; exact lt_irrefl _ h
    · intro h; exact hpos k h
  · rintro k u ⟨hk, hu, hsu⟩ hkK
    obtain ⟨e1, e2, e3⟩ := euIt_bounds (s := s) hb has hbs k
    have hB0 := hpos k hkK
    set A := (euIt (a, b) k).1 with hAd
    set B := (euIt (a, b) k).2 with hBd
    set v := addC u (tcost cZ zB u) with hv
    have hvm : v.mem = Function.update (Function.update u0.mem zA A) zB B := by rw [hv, addC_mem, hu]
    have fA : v.mem zA = A := by rw [hvm]; evl
    have fB : v.mem zB = B := by rw [hvm]; evl
    have fQ : v.mem zQ = 0 := by rw [hvm]; evl; exact hQ
    have fz : v.mem cZ = 0 := by rw [hvm]; evl; exact hz
    have hq : |A / B| ≤ |A| := by
      rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]; exact_mod_cast Int.natAbs_ediv_le_natAbs A B
    have hr0 : 0 ≤ A % B := Int.emod_nonneg A hB0.ne'
    have hr1 : A % B < B := Int.emod_lt_of_pos A hB0
    have hm : A / B * B = A - A % B := by rw [Int.emod_def]; ring
    have hqb : |A / B * B| < 2 ^ (s + 1) := by
      rw [hm]; rw [abs_lt] at e1 ⊢; constructor <;> omega
    -- `zQ := A % B`
    have ok1 : OKI w L [.div zQ zA zB, .mul zQ zQ zB, .sub zQ zA zQ] v ∧
        (runI w [.div zQ zA zB, .mul zQ zQ zB, .sub zQ zA zQ] v).mem =
          Function.update (Function.update (Function.update v.mem zQ (A / B)) zQ (A / B * B)) zQ (A - A / B * B) := by
      refine ⟨⟨⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
          len_scr (by decide) (by decide) h10, by rw [fA]; exact lS _ (by omega), by
            rw [fB]; exact lS _ (by rw [abs_of_nonneg e2]; omega)⟩,
        ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
          by evl; rw [fA, fB]; exact lS _ (by omega), by evl; rw [fB]; exact lS _ (by rw [abs_of_nonneg e2]; omega)⟩,
        ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
          by evl; rw [fA]; exact lS _ (by omega), by evl; rw [fA, fB]; exact lS _ hqb⟩, trivial⟩, ?_⟩
      simp only [runI, stepI_div_mem, stepI_mul_mem, stepI_sub_mem]
      evl
      simp only [fA, fB]
    obtain ⟨okA, mA⟩ := ok1
    set v1 := runI w [.div zQ zA zB, .mul zQ zQ zB, .sub zQ zA zQ] v with hv1
    have gA : v1.mem zA = A := by rw [mA]; evl; exact fA
    have gB : v1.mem zB = B := by rw [mA]; evl; exact fB
    have gQ : v1.mem zQ = A % B := by rw [mA]; evl; rw [hm]; ring
    have gz : v1.mem cZ = 0 := by rw [mA]; evl; exact fz
    have ok2 : OKI w L [.add zA zB cZ, .add zB zQ cZ, .const zQ 0] v1 ∧
        (runI w [.add zA zB cZ, .add zB zQ cZ, .const zQ 0] v1).mem =
          Function.update (Function.update (Function.update v1.mem zA B) zB (A % B)) zQ 0 := by
      refine ⟨⟨⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
          len_scr (by decide) (by decide) h10, by rw [gB]; exact lS _ (by rw [abs_of_nonneg e2]; omega),
          by rw [gz]; exact l0⟩,
        ⟨len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10, len_scr (by decide) (by decide) h10,
          by evl; rw [gQ]; exact lS _ (by rw [abs_of_nonneg hr0]; omega), by evl; rw [gz]; exact l0⟩,
        ⟨len_scr (by decide) (by decide) h10, l0⟩, trivial⟩, ?_⟩
      simp only [runI, stepI_add_mem, stepI_const_mem]
      evl
      simp only [gB, gQ, gz, add_zero]
    obtain ⟨okB, mB⟩ := ok2
    refine (rs_seqI (OKI_append okA okB)).mono ?_
    rintro n v' ⟨hn, rfl⟩
    have hstep : euIt (a, b) (k + 1) = (B, A % B) := by
      show euStep (euIt (a, b) k) = _
      unfold euStep; rw [ite_eq_right_iff.mpr (fun h => absurd h hB0.ne')]
    refine ⟨by simp at hn; omega, by omega, ?_, (hsu.trans ((Same'.addC _ _).trans
      (runI_same (by simp [Plain, NJ])))).trans (Same'.addC _ 1)⟩
    rw [addC_mem, runI_append, ← hv1, mB, mA, hvm, hstep]
    funext c
    simp only [Function.update_apply]
    split_ifs <;> (try subst_vars) <;> first | rfl | omega
  · rintro n u ⟨-, hu, hsu⟩ hn
    refine ⟨by omega, ?_, hsu.trans (Same'.addC _ _)⟩
    rw [addC_mem, hu, hKz, euIt_fin hb hKz]

end AdversarialBco.UniPoly
