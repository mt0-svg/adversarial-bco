/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.PolyStep
public import AdversarialBco.Unified.PolyOrc
public import AdversarialBco.Unified.PolyBlk3
public import AdversarialBco.StatementConj1Poly

@[expose] public section

/-!
# UNI-POLY, part 12: `play`, `orc`, `obsR`, and one step of `P`

* `sim_play`, `sim_orc`, `sim_obsR`: the three long blocks against the step of `P`.
* `step_sim`: from related states, the compiled program reaches the state related to the next state of `P`; when the
  feedback is in `[0, 1]`, at a cost of at most `Kc0 · c^3`, `c` the cost of the step of `P`.
-/

namespace AdversarialBco.UniPoly

open AdversarialBco BitRAM BitRAMO RCmd
open AdversarialBco.Bit.Transfer (B.CodeAt B.run_zero)
open AdversarialBco.RealRAM (polytope HeightLE)

variable {d : ℕ} {pro : List Instr} {P : List InstrO} {Fix : ℤ → ℤ} {s t : State d} {w : World d}

/-! ## Arithmetic facts -/

theorem playCost_ge (mm : ℤ → ℤ) (a : ℤ) {j : ℕ} (hj : j ≤ d) :
    1 + len (a + j) + len (mm (a + j)) ≤ playCost d mm a := by
  unfold playCost
  exact Finset.single_le_sum (f := fun i : ℕ => 1 + len (a + i) + len (mm (a + i))) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.2 (by omega))

theorem abs_lt_two_pow_len (x : ℤ) : |x| < 2 ^ len x := by
  have h := natAbs_lt_of_len_le (le_refl (len x))
  rw [Int.abs_eq_natAbs]; exact_mod_cast h

theorem len_le_self_add (x : ℕ) : len (x : ℤ) ≤ x := by
  rw [len_le_iff]; simpa using Nat.lt_two_pow_self

/-- The feedback in `[0, 1]`: a reading of precision `p` has at most `p + 1` bits. -/
theorem len_reading_le {w : World d} {t : State d} (h0 : 0 ≤ feedback w t) (h1 : feedback w t ≤ 1) (p : ℕ) :
    len (reading w t p) ≤ p + 1 := by
  rw [len_le_iff]
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have a0 : 0 ≤ reading w t p := Int.floor_nonneg.2 (mul_nonneg hp.le h0)
  have a1 : reading w t p ≤ 2 ^ p := by
    unfold reading
    have : (2 : ℝ) ^ p * feedback w t ≤ ((2 ^ p : ℤ) : ℝ) := by push_cast; nlinarith
    exact (Int.floor_le_floor this).trans (by rw [Int.floor_intCast])
  have e : ((2 ^ p : ℕ) : ℤ) = (2 : ℤ) ^ p := by norm_num
  have : (reading w t p).natAbs ≤ 2 ^ p := by omega
  calc (reading w t p).natAbs ≤ 2 ^ p := this
    _ < 2 ^ (p + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- `(d + 1) M^(d + 1) 2^c < 2^(c + Kd)`. -/
theorem lv_bound {m Ms LY c : ℕ} {M : ℤ} (hM1 : 1 ≤ M) (hM : M < 2 ^ (Ms + 1)) :
    ((d : ℤ) + 1) * M ^ (d + 1) * 2 ^ c < 2 ^ (c + Kd d m Ms LY) := by
  have h1 : ((d : ℤ) + 1) < 2 ^ (d + 1) := by exact_mod_cast Nat.lt_two_pow_self
  have h2 : M ^ (d + 1) ≤ (2 ^ (Ms + 1)) ^ (d + 1) := pow_le_pow_left₀ (by omega) hM.le _
  have h3 : ((d : ℤ) + 1) * M ^ (d + 1) < 2 ^ (d + 1) * (2 ^ (Ms + 1)) ^ (d + 1) := by
    calc ((d : ℤ) + 1) * M ^ (d + 1) ≤ ((d : ℤ) + 1) * (2 ^ (Ms + 1)) ^ (d + 1) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ < 2 ^ (d + 1) * (2 ^ (Ms + 1)) ^ (d + 1) := mul_lt_mul_of_pos_right h1 (by positivity)
  have e : (2 : ℤ) ^ (d + 1) * (2 ^ (Ms + 1)) ^ (d + 1) = 2 ^ ((d + 1) * (Ms + 2)) := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  have h4 : (2 : ℤ) ^ ((d + 1) * (Ms + 2)) ≤ 2 ^ Kd d m Ms LY :=
    pow_le_pow_right₀ (by norm_num) (by unfold Kd; omega)
  have h5 : ((d : ℤ) + 1) * M ^ (d + 1) < 2 ^ Kd d m Ms LY := by rw [e] at h3; exact h3.trans_le h4
  have : (0 : ℤ) < 2 ^ c := by positivity
  rw [pow_add (2 : ℤ) c, mul_comm ((2 : ℤ) ^ c)]
  exact mul_lt_mul_of_pos_right h5 this

/-- From a block cost to the cubic bound. -/
theorem fin_cost {m Ms LY c nb L : ℕ} (hc : 1 ≤ c) (hnb : nb ≤ N1 d m + 4 * c) (hL : L ≤ c + Kd d m Ms LY) :
    nb * U d L ≤ Kc0 d m Ms LY * c ^ 3 :=
  (Nat.mul_le_mul_left _ (U_mono hL)).trans (cost_poly hc hnb)

/-! ## The input rows -/

/-- The numerator of the entry `(i, j)` (`0` past the rows). -/
def nmA {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (i j : ℕ) : ℤ :=
  if h : i < m then (entry A b ⟨i, h⟩ j).num else 0

/-- The denominator of the entry `(i, j)` (`1` past the rows). -/
def dnA {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (i j : ℕ) : ℤ :=
  if h : i < m then ((entry A b ⟨i, h⟩ j).den : ℤ) else 1

theorem entry_height {m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} (hH : HeightLE A b M) (i : Fin m)
    (j : ℕ) : (entry A b i j).num.natAbs ≤ M ∧ (entry A b i j).den ≤ M := by
  unfold entry
  split_ifs with hj
  · exact hH.1 i ⟨j, hj⟩
  · exact hH.2 i

/-! ## `play` -/

theorem sim_play {wO : WorldO d} {m LY : ℕ} {Ms : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {YB : ℤ}
    (hW : wO.toW = w) (hF : FixOK d m A b YB Fix) (hLYB : len (YB + d + 1) ≤ LY)
    (hR : Rel (Fa P pro.length) Fix s t) (hk : s.pc < P.length) {src : ℤ} (hP : P[s.pc] = .base (.play src)) :
    ∃ n, Rel (Fa P pro.length) Fix (stepO P wO s) (run (compP pro P) w t n) ∧
      (run (compP pro P) w t n).cost ≤ t.cost + ((d + 1) * 25 + 60) * U d (dC P wO s + Kd d m Ms LY) := by
  have h? := getElem?_of hk hP
  have hs0 := stepO_base (wO := wO) h?
  rw [hW] at hs0
  have hs' : stepO P wO s =
      { s with pc := s.pc + 1, rounds := s.rounds + 1,
               pts := Function.update s.pts s.rounds (ptAt d s.mem (s.mem src)),
               cost := s.cost + (1 + len src + len (s.mem src) + playCost d s.mem (s.mem src)) } := by
    rw [hs0]; simp [step, lowerP_base h?]
  have hc : dC P wO s = 1 + len src + len (s.mem src) + playCost d s.mem (s.mem src) := by
    simp only [dC, hs']; omega
  rw [hc, hs']
  have hz := hR.z
  have fx : ∀ c, -999 ≤ c → t.mem c = Fix c := fun c hc => hR.fix c (by simp only [N0]; omega)
  have hYB3 : 3 ≤ YB := by
    have := hF.ybm; have : (0 : ℤ) ≤ ((d : ℤ) + 1) * m := by positivity
    omega
  have hpc := fun j (hj : j ≤ d) => playCost_ge (d := d) s.mem (s.mem src) hj
  have hKd : LY + (d + 1) ≤ Kd d m Ms LY := by unfold Kd; nlinarith
  have hLY' : len (YB + d) ≤ LY := (len_mono (by omega) (by omega)).trans hLYB
  have hLd : len ((d : ℤ) + 1) ≤ d + 1 := by exact_mod_cast len_le_self_add (d + 1)
  refine blk_step hR hk (by rw [hP]; rfl) (by rw [hP]; rfl) rfl ?_
  rw [hP]
  refine (rs_PLAYB (a := s.mem src) (YB := YB) (hz src) (by omega) (by rw [fx _ (by norm_num), hF.yb])
    (by rw [fx _ (by norm_num), hF.d0]) (hR.scr hF (Or.inl rfl)) (hR.scr hF (isScr_of (by norm_num) (by norm_num)))
    (hR.scr hF (isScr_of (by norm_num) (by norm_num))) (hR.scr hF (isScr_of (by norm_num) (by norm_num)))
    (hR.scr hF (isScr_of (by norm_num) (by norm_num))) (hR.scr hF (isScr_of (by norm_num) (by norm_num)))
    (hR.scr hF (isScr_of (by norm_num) (by norm_num))) (hR.scr hF (isScr_of (by norm_num) (by norm_num)))
    (hR.scr hF (isScr_of (by norm_num) (by norm_num))) (hR.scr hF (isScr_of (by norm_num) (by norm_num)))
    (hR.scr hF (isScr_of (by norm_num) (by norm_num))) (hR.scr hF (isScr_of (by norm_num) (by norm_num)))
    (fun c h1 h2 => by rw [fx c (by omega), hF.ybz c h1 h2]) (by unfold Kd; omega)
    (fun j hj => by have := hpc j hj; unfold Kd; omega) (fun j hj => by rw [hz]; have := hpc j hj; unfold Kd; omega)
    (by omega) (by omega) (by unfold Kd; omega)).mono ?_
  rintro n t' ⟨hn, hm, hco, hro, hpt⟩
  refine ⟨hn, rfl, fun x => ?_, fun c hc => ?_, ?_, ?_, ?_⟩
  · show t'.mem (φ x) = s.mem x
    rw [hm]; exact hz x
  · show t'.mem c = Fix c
    rw [hm]; exact hR.fix c hc
  · show t'.coins = s.coins
    rw [hco]; exact hR.coins
  · show t'.rounds = s.rounds + 1
    rw [hro, hR.rounds]
  · show t'.pts = Function.update s.pts s.rounds (ptAt d s.mem (s.mem src))
    rw [hpt, hR.pts, hR.rounds, show (fun x => t.mem (φ x)) = s.mem from funext hz]

/-! ## `orc` -/

theorem sim_orc {wO : WorldO d} {m M LY : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {YB : ℤ}
    (hO : ∀ y k, wO.orc y k = @decide (toE y ∈ polytope A b) (Classical.dec _)) (hH : HeightLE A b M)
    (hF : FixOK d m A b YB Fix) (hLYB : len (YB + d + 1) ≤ LY)
    (hR : Rel (Fa P pro.length) Fix s t) (hk : s.pc < P.length) {dst src prec : ℤ}
    (hP : P[s.pc] = .orc dst src prec) :
    ∃ n, Rel (Fa P pro.length) Fix (stepO P wO s) (run (compP pro P) w t n) ∧
      (run (compP pro P) w t n).cost ≤ t.cost + N1 d m * U d (dC P wO s + Kd d m M.size LY) := by
  have h? := getElem?_of hk hP
  set a := s.mem src with ha
  set c := 1 + len dst + len src + len prec + len (s.mem prec) + len a + playCost d s.mem a + (s.mem prec).toNat
    with hcd
  have hs' : stepO P wO s =
      { s with pc := s.pc + 1,
               mem := Function.update s.mem dst (if wO.orc (ptAt d s.mem a) (s.mem prec).toNat then 1 else 0),
               cost := s.cost + c } := by
    simp [stepO, h?, hcd, ha]
  have hc : dC P wO s = c := by simp only [dC, hs']; omega
  rw [hc, hs']
  have hz := hR.z
  have fx : ∀ c, -999 ≤ c → t.mem c = Fix c := fun c hc => hR.fix c (by simp only [N0]; omega)
  have hYB3 : 3 ≤ YB := by
    have := hF.ybm; have : (0 : ℤ) ≤ ((d : ℤ) + 1) * m := by positivity
    omega
  have hpc := fun j (hj : j ≤ d) => playCost_ge (d := d) s.mem a hj
  have hKd : LY + (d + 1) + m + 20 ≤ Kd d m M.size LY := by unfold Kd; nlinarith
  set L := c + Kd d m M.size LY with hL
  set M' : ℤ := max (M : ℤ) 1 with hM'
  have hM1 : 1 ≤ M' := le_max_right _ _
  have hMs : M' < 2 ^ (M.size + 1) := by
    have h1 : (M : ℤ) < 2 ^ M.size := by exact_mod_cast Nat.lt_size_self M
    have h2 : (2 : ℤ) ^ M.size < 2 ^ (M.size + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
    have h3 : (1 : ℤ) < 2 ^ (M.size + 1) := one_lt_pow₀ (by norm_num) (by omega)
    rw [hM']; exact max_lt (h1.trans h2) h3
  have hMb : ∀ i < m, ∀ j : ℕ, j ≤ d → |nmA A b i j| ≤ M' ∧ 0 < dnA A b i j ∧ dnA A b i j ≤ M' := by
    intro i hi j _
    obtain ⟨e1, e2⟩ := entry_height hH ⟨i, hi⟩ j
    simp only [nmA, dnA, hi, ↓reduceDIte]
    refine ⟨?_, by exact_mod_cast (entry A b ⟨i, hi⟩ j).den_pos, ?_⟩
    · rw [Int.abs_eq_natAbs]; exact (by exact_mod_cast e1 : ((entry A b ⟨i, hi⟩ j).num.natAbs : ℤ) ≤ M).trans
        (le_max_left _ _)
    · exact (by exact_mod_cast e2 : ((entry A b ⟨i, hi⟩ j).den : ℤ) ≤ M).trans (le_max_left _ _)
  have hrow : ∀ i < m, ∀ j : ℕ, j ≤ d → 0 ≤ ((d : ℤ) + 1) * i + j := fun i _ j _ => by positivity
  have hyb : ∀ j : ℕ, j ≤ d → |t.mem (φ (a + j))| ≤ 2 ^ c := fun j hj => by
    rw [hz]
    have h1 := abs_lt_two_pow_len (s.mem (a + j))
    have h2 : (2 : ℤ) ^ len (s.mem (a + j)) ≤ 2 ^ c :=
      pow_le_pow_right₀ (by norm_num) (by have := hpc j hj; omega)
    exact (h1.trans_le h2).le
  have hLV : ((d : ℤ) + 1) * M' ^ (d + 1) * 2 ^ c < 2 ^ L := lv_bound hM1 hMs
  have hLY : YB + d + 1 < 2 ^ L := by
    have h1 := natAbs_lt_of_len_le hLYB
    have h2 : (2 : ℕ) ^ LY ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : ((YB + d + 1).natAbs : ℤ) = YB + d + 1 := Int.natAbs_of_nonneg (by omega)
    have h3 : ((YB + d + 1).natAbs : ℤ) < 2 ^ L := by exact_mod_cast h1.trans_le h2
    omega
  have hLm : (m : ℤ) + 1 < 2 ^ L := by
    have h1 : m + 1 < 2 ^ (m + 1) := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ (m + 1) ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast h1.trans_le h2
  refine blk_step hR hk (by rw [hP]; rfl) (by rw [hP]; rfl) rfl ?_
  rw [hP]
  refine (rs_ORCB (L := L) (dst := dst) (src := src) (a := a) (YB := YB) (M := M') (B := 2 ^ c) (m := m)
    (nm := nmA A b) (dn := dnA A b) (hz src) (by omega) (by rw [fx _ (by norm_num), hF.yb])
    (by rw [fx _ (by norm_num), hF.d0]) (by rw [fx _ (by norm_num), hF.m2])
    (hR.scr hF (Or.inl rfl)) (hR.scr hF (isScr_of (by norm_num) (by norm_num)))
    (hR.scr hF (isScr_of (by norm_num) (by norm_num))) (hR.scr hF (isScr_of (by norm_num) (by norm_num)))
    (hR.scr hF (isScr_of (by norm_num) (by norm_num))) (hR.scr hF (isScr_of (by norm_num) (by norm_num)))
    (hR.scr hF (isScr_of (by norm_num) (by norm_num))) (hR.scr hF (isScr_of (by norm_num) (by norm_num)))
    (hR.scr hF (isScr_of (by norm_num) (by norm_num))) (hR.scr hF (isScr_of (by norm_num) (by norm_num)))
    (hR.scr hF (isScr_of (by norm_num) (by norm_num))) (hR.scr hF (isScr_of (by norm_num) (by norm_num)))
    (hR.scr hF (isScr_of (by norm_num) (by norm_num))) (hR.scr hF (isScr_of (by norm_num) (by norm_num)))
    (hR.scr hF (isScr_of (by norm_num) (by norm_num))) (hR.scr hF (isScr_of (by norm_num) (by norm_num)))
    (hR.scr hF (isScr_of (by norm_num) (by norm_num))) (hR.scr hF (isScr_of (by norm_num) (by norm_num)))
    (hR.scr hF (isScr_of (by norm_num) (by norm_num))) (hR.scr hF (isScr_of (by norm_num) (by norm_num)))
    (hR.scr hF (isScr_of (by norm_num) (by norm_num))) (hR.scr hF (isScr_of (by norm_num) (by norm_num)))
    (hR.scr hF (isScr_of (by norm_num) (by norm_num)))
    (hR.scr hF (isScr_of (by norm_num) (by norm_num))) (hR.scr hF (isScr_of (by norm_num) (by norm_num)))
    (fun c h1 h2 => by rw [fx c (by omega), hF.ybz c h1 h2]) hF.ybm
    (fun i hi j hj => by
      have := hrow i hi j hj
      rw [fx _ (by omega), (hF.row i hi j hj).1]; simp [nmA, hi])
    (fun i hi j hj => by
      have := hrow i hi j hj
      rw [fx _ (by omega), (hF.row i hi j hj).2]; simp [dnA, hi])
    hM1 hMb (one_le_pow₀ (by norm_num)) hyb (by unfold Kd at hL; omega) (by unfold Kd at hL; omega)
    (fun j hj => by have := hpc j hj; unfold Kd at hL; omega) hLV hLY hLm (by omega)).mono ?_
  rintro n t' ⟨hn, hm, hS⟩
  refine ⟨by unfold N1; omega, hR.upd dst _ rfl hm ?_ (hS.1.trans hR.coins) (hS.2.1.trans hR.rounds)
    (hS.2.2.trans hR.pts)⟩
  -- the answer
  have e : (fun j : ℕ => nrm (t.mem (φ a)) (t.mem (φ (a + j))) j) = fun j : ℕ => nrm (s.mem a) (s.mem (a + j)) j :=
    funext fun j => by rw [hz, hz]
  rw [e, rowR_nrm A b s.mem a (fun i hi j hj => by simp [nmA, dnA, hi, Rat.num_div_den])
    (fun i hi j hj => by simp [dnA, hi, (entry A b ⟨i, hi⟩ j).den_pos]), hO]
  by_cases hK : toE (ptAt d s.mem a) ∈ polytope A b
  · simp [hK]
  · simp [hK]

/-! ## `obsR` -/

theorem sim_obsR {wO : WorldO d} {m Ms LY : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {YB : ℤ}
    (hW : wO.toW = w) (hF : FixOK d m A b YB Fix)
    (hR : Rel (Fa P pro.length) Fix s t) (hk : s.pc < P.length) {dst prec rng : ℤ}
    (hP : P[s.pc] = .obsR dst prec rng) :
    ∃ n, Rel (Fa P pro.length) Fix (stepO P wO s) (run (compP pro P) w t n) ∧
      (0 ≤ feedback w t → feedback w t ≤ 1 →
        (run (compP pro P) w t n).cost ≤ t.cost + (N1 d m + 4 * dC P wO s) * U d (dC P wO s + Kd d m Ms LY)) := by
  have h? := getElem?_of hk hP
  set c := 1 + len dst + len prec + len rng + len (s.mem prec) + len (s.mem rng) + (s.mem prec).toNat +
    (s.mem rng).toNat with hcd
  have hs' : stepO P wO s =
      { s with pc := s.pc + 1,
               mem := Function.update s.mem dst (clip (s.mem rng).toNat (reading w s (s.mem prec).toNat)),
               cost := s.cost + c } := by
    simp [stepO, h?, hcd, hW]
  have hc : dC P wO s = c := by simp only [dC, hs']; omega
  rw [hc, hs']
  have hz := hR.z
  have hrd := reading_congr (w := w) hR.rounds hR.pts (s.mem prec).toNat
  -- the block within the bound `L`
  have key : ∀ L : ℕ, c + 11 ≤ L → len (reading w t (s.mem prec).toNat) ≤ L →
      ∃ n, Rel (Fa P pro.length) Fix
        { s with pc := s.pc + 1,
                 mem := Function.update s.mem dst (clip (s.mem rng).toNat (reading w s (s.mem prec).toNat)),
                 cost := s.cost + c } (run (compP pro P) w t n) ∧
        (run (compP pro P) w t n).cost ≤ t.cost + (4 * c + 24) * U d L := fun L hL hv => by
    refine blk_step hR hk (by rw [hP]; rfl) (by rw [hP]; rfl) rfl ?_
    rw [hP]
    refine (rs_OBSRB (L := L) (hR.scr hF (Or.inl rfl)) (hR.scr hF (isScr_of (by norm_num) (by norm_num)))
      (hR.scr hF (isScr_of (by norm_num) (by norm_num))) (hR.scr hF (isScr_of (by norm_num) (by norm_num)))
      (hR.scr hF (isScr_of (by norm_num) (by norm_num))) (hR.scr hF (isScr_of (by norm_num) (by norm_num)))
      (hR.scr hF (isScr_of (by norm_num) (by norm_num))) (by omega) (by omega) (by omega)
      (by rw [hz]; omega) (by rw [hz]; omega) (by rw [hz]; omega) (by rw [hz]; omega) (by rw [hz]; exact hv)
      (by omega)).mono ?_
    rintro n t' ⟨hn, hm, hS⟩
    refine ⟨by rw [hz] at hn; omega, hR.upd dst _ rfl (by rw [hm, hz, hz, hrd]) rfl (hS.1.trans hR.coins)
      (hS.2.1.trans hR.rounds) (hS.2.2.trans hR.pts)⟩
  by_cases hfb : 0 ≤ feedback w t ∧ feedback w t ≤ 1
  · have hv := len_reading_le (w := w) (t := t) hfb.1 hfb.2 (s.mem prec).toNat
    obtain ⟨n, h1, h2⟩ := key (c + Kd d m Ms LY) (by unfold Kd; omega) (by unfold Kd; omega)
    refine ⟨n, h1, fun _ _ => h2.trans ?_⟩
    have : 4 * c + 24 ≤ N1 d m + 4 * c := by unfold N1; omega
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ this) _
  · obtain ⟨n, h1, -⟩ := key (c + 11 + len (reading w t (s.mem prec).toNat)) (by omega) (by omega)
    exact ⟨n, h1, fun h0 h1 => absurd ⟨h0, h1⟩ hfb⟩

/-! ## One step -/

theorem dC_pos {wO : WorldO d} {i : InstrO} (h : P[s.pc]? = some i) : 1 ≤ dC P wO s := by
  unfold dC
  rcases i with i | ⟨dst, src, prec⟩ | ⟨dst, prec, rng⟩
  · rw [stepO_base h]
    cases i <;> simp [step, lowerP_base h] <;> omega
  · simp [stepO, h]; omega
  · simp [stepO, h]; omega

/-- **One step of `P`.** -/
theorem step_sim {wO : WorldO d} {m M LY : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {YB : ℤ}
    (hW : wO.toW = w) (hO : ∀ y k, wO.orc y k = @decide (toE y ∈ polytope A b) (Classical.dec _))
    (hH : HeightLE A b M) (hF : FixOK d m A b YB Fix) (hLYB : len (YB + d + 1) ≤ LY)
    (hR : Rel (Fa P pro.length) Fix s t) :
    ∃ n, Rel (Fa P pro.length) Fix (stepO P wO s) (run (compP pro P) w t n) ∧
      (0 ≤ feedback w t → feedback w t ≤ 1 →
        (run (compP pro P) w t n).cost ≤ t.cost + Kc0 d m M.size LY * dC P wO s ^ 3) := by
  rcases hget : P[s.pc]? with _ | i
  · have e : stepO P wO s = s := by simp [stepO, hget]
    refine ⟨0, ?_, fun _ _ => ?_⟩
    · rw [e, B.run_zero]; exact hR
    · rw [B.run_zero]; omega
  have hk : s.pc < P.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hget
    exact absurd hget (by simp)
  have hPi : P[s.pc] = i := by
    rw [List.getElem?_eq_getElem hk] at hget; exact Option.some.inj hget
  have hc1 := dC_pos (wO := wO) hget
  have hKd : 11 ≤ Kd d m M.size LY := by unfold Kd; omega
  have conv : ∀ {nb L : ℕ}, nb ≤ N1 d m + 4 * dC P wO s → L ≤ dC P wO s + Kd d m M.size LY →
      ∀ n, (run (compP pro P) w t n).cost ≤ t.cost + nb * U d L →
        (run (compP pro P) w t n).cost ≤ t.cost + Kc0 d m M.size LY * dC P wO s ^ 3 :=
    fun hnb hL n h => h.trans (Nat.add_le_add_left (fin_cost hc1 hnb hL) _)
  have hN1 : 100 ≤ N1 d m := by unfold N1; omega
  rcases i with i | ⟨dst, src, prec⟩ | ⟨dst, prec, rng⟩
  · cases i with
    | load dst src =>
      obtain ⟨n, h1, h2⟩ := sim_load hW hF hR hk hPi
      exact ⟨n, h1, fun _ _ => conv (by omega) (by omega) n h2⟩
    | store dst src =>
      obtain ⟨n, h1, h2⟩ := sim_store hW hF hR hk hPi
      exact ⟨n, h1, fun _ _ => conv (by omega) (by omega) n h2⟩
    | jlt a b' tg =>
      obtain ⟨n, h1, h2⟩ := sim_jlt hW hR hk hPi
      exact ⟨n, h1, fun _ _ => conv (by omega) (by omega) n h2⟩
    | jmp tg =>
      obtain ⟨n, h1, h2⟩ := sim_jmp hW hR hk hPi
      exact ⟨n, h1, fun _ _ => conv (by omega) (by omega) n h2⟩
    | play src =>
      obtain ⟨n, h1, h2⟩ := sim_play (Ms := M.size) hW hF hLYB hR hk hPi
      exact ⟨n, h1, fun _ _ => conv (by unfold N1; omega) le_rfl n h2⟩
    | _ =>
      obtain ⟨n, h1, h2⟩ := sim_simple hW hR hk hPi (by intros; simp)
      exact ⟨n, h1, fun _ _ => conv (by omega) (by omega) n h2⟩
  · obtain ⟨n, h1, h2⟩ := sim_orc hO hH hF hLYB hR hk hPi
    exact ⟨n, h1, fun _ _ => conv (by omega) le_rfl n h2⟩
  · obtain ⟨n, h1, h2⟩ := sim_obsR (Ms := M.size) (LY := LY) hW hF hR hk hPi
    exact ⟨n, h1, fun a b => conv le_rfl le_rfl n (h2 a b)⟩

end AdversarialBco.UniPoly
