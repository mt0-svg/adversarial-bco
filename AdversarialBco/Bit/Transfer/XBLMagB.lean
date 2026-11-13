/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLMagA
public import AdversarialBco.Bit.Transfer.XBLMagLem

@[expose] public section

/-!
# The magnitudes of BL's state, part B: the draws, the mode, the play

The draws of BM-INT are at most `B` (`draw_abs`); a run in mode `run` started in mode `run` (`modeAt_run`), so
`ε' ≤ 1/2` and every kept `β̃_i` is positive (`mode0_run`); `0 ≤ ε'` (`eps_nonneg`); the play of mode `run` lies in
the polytope (`play_mem`), so the reading of an admissible loss is in `[0, 2^p]` (`obs_bnd`).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ AdversarialBco.Bit.Asm Matrix
open AdversarialBco.BitRAM (toE)

variable {d : ℕ}

/-! ## The draws -/

theorem gOut_abs (B U W : ℕ) (hB : 8 ≤ B) (hU : U < 2 ^ B) (hW : W < 2 ^ B) :
    |(gOut B (U, W)).1| ≤ B ∧ |(gOut B (U, W)).2| ≤ B := by
  obtain ⟨-, -, h1, h2⟩ := gsSpec_err B U W hB hU hW
  have hs := sqrt_two_mul_le B (by omega)
  have e : gOut B (U, W) = (((gsSpec B U W).1 : ℚ) / 2 ^ (2 * gsm_prec B),
      ((gsSpec B U W).2 : ℚ) / 2 ^ (2 * gsm_prec B)) := rfl
  rw [e]
  generalize gsSpec B U W = g at h1 h2
  generalize 2 * gsm_prec B = q at h1 h2
  have key : ∀ z : ℤ, |(z : ℝ) / 2 ^ q| ≤ Real.sqrt (2 * B) → |(z : ℚ) / 2 ^ q| ≤ B := fun z hz => by
    have h : ((|(z : ℚ) / 2 ^ q| : ℚ) : ℝ) ≤ ((B : ℚ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h
  exact ⟨key _ h1, key _ h2⟩

theorem blkUW_lt2 (cs : ℕ → Bool) (K0 B d t j : ℕ) :
    (blkUW cs K0 B d t j).1 < 2 ^ B ∧ (blkUW cs K0 B d t j).2 < 2 ^ B := by
  unfold blkUW
  obtain ⟨a0, a1⟩ := readCoins_bounds cs (Sched.blkStart d K0 B t j) B
  obtain ⟨b0, b1⟩ := readCoins_bounds cs (Sched.blkStart d K0 B t j + B) B
  have e1 := Int.toNat_of_nonneg a0
  have e2 := Int.toNat_of_nonneg b0
  constructor
  · have : (((BitRAM.readCoins cs (Sched.blkStart d K0 B t j) B).toNat : ℕ) : ℤ) < 2 ^ B := by rw [e1]; exact a1
    exact_mod_cast this
  · have : (((BitRAM.readCoins cs (Sched.blkStart d K0 B t j + B) B).toNat : ℕ) : ℤ) < 2 ^ B := by rw [e2]; exact b1
    exact_mod_cast this

/-- **The draws are at most `B`.** -/
theorem draw_abs (cs : ℕ → Bool) (K0 B t : ℕ) (hB : 8 ≤ B) :
    (∀ i, |(draw cs K0 B d t).1 i| ≤ B) ∧ |(draw cs K0 B d t).2| ≤ B := by
  have hg : ∀ j, |(gOut B (blkUW cs K0 B d t j)).1| ≤ B ∧ |(gOut B (blkUW cs K0 B d t j)).2| ≤ B := fun j => by
    obtain ⟨h1, h2⟩ := blkUW_lt2 cs K0 B d t j
    exact gOut_abs B _ _ hB h1 h2
  refine ⟨fun i => ?_, ?_⟩
  · unfold draw
    dsimp only
    split_ifs
    · exact (hg _).1
    · exact (hg _).2
  · unfold draw
    dsimp only
    rw [abs_div, abs_two]
    have := (hg ((d + 1) / 2)).1
    have hB0 : (0 : ℚ) ≤ B := by positivity
    linarith

/-! ## The mode -/

/-- **A run in mode `run` started in mode `run`.** -/
theorem modeAt_run (R : Routines) (n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (σ : RealRAM.Strategy d) (cs : ℕ → Bool) :
    ∀ (t : ℕ) (st : St d), modeAt R d n m A b σ cs t = .run st → ∃ st0, mode0 (cfgOf R d n m A b cs) = .run st0
  | 0, st, h => ⟨st, h⟩
  | t + 1, st, h => by
    unfold modeAt at h
    simp only [traj] at h
    rcases hm : (traj R d n m A b σ cs t).1 with _ | _ | st1
    · rw [hm] at h; cases h
    · rw [hm] at h; cases h
    · exact modeAt_run R n m A b σ cs t st1 hm

/-- Mode `run` at the start: `ε' ≤ 1/2`, every kept `β̃_i` positive, the state the epoch start. -/
theorem mode0_run {cfg : Cfg d} {st0 : St d} (h : mode0 cfg = .run st0) :
    cfg.par.eps ≤ 1 / 2 ∧ (∀ i, 0 < cfg.β i) ∧ st0 = init cfg.par d := by
  unfold mode0 at h
  split_ifs at h with hc
  push_neg at hc
  cases h
  exact ⟨hc.1, hc.2, rfl⟩

theorem eps_nonneg {n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 ≤ (par d n).eps := by
  have hLe := Le_ge_one hd hn
  rw [PieceA.par_Le] at hLe
  have hee : 0 ≤ PieceA.ee d n := by unfold PieceA.ee lnErr; positivity
  have hL : 0 ≤ 36 * (PieceA.L0 d n + PieceA.ee d n) := by linarith
  have hrn : 0 ≤ sqrtDn (par d n).q n := by unfold sqrtDn; positivity
  have hx : 0 ≤ 14500 * (d : ℚ) * (sqrtDn (par d n).q d + 1 / 2 ^ (par d n).q) *
      (36 * (PieceA.L0 d n + PieceA.ee d n)) ^ 5 / sqrtDn (par d n).q n := by
    apply div_nonneg _ hrn
    have hrd : 0 ≤ sqrtDn (par d n).q d := by unfold sqrtDn; positivity
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (pow_nonneg hL 5)
  rw [PieceA.par_eps]
  unfold up
  apply div_nonneg _ (by positivity)
  exact_mod_cast Int.ceil_nonneg (mul_nonneg hx (by positivity))

/-! ## The play -/

/-- The gauge is nonnegative and at least each of its terms. -/
theorem gauge_spec (cfg : Cfg d) (X : Fin d → ℚ) :
    0 ≤ gaugeQ cfg X ∧ ∀ i, cfg.α i ⬝ᵥ X / cfg.β i ≤ gaugeQ cfg X := by
  obtain ⟨h0, h1, -⟩ := foldlMax_spec (List.ofFn fun i => cfg.α i ⬝ᵥ X / cfg.β i)
  exact ⟨h0, fun i => h1 _ (List.mem_ofFn.2 ⟨i, rfl⟩)⟩

/-- The gauge is at most any common bound of its terms. -/
theorem gauge_le (cfg : Cfg d) (X : Fin d → ℚ) (S : ℚ) (hS : 0 ≤ S) (h : ∀ i, cfg.α i ⬝ᵥ X / cfg.β i ≤ S) :
    gaugeQ cfg X ≤ S := by
  obtain ⟨-, -, h2⟩ := foldlMax_spec (List.ofFn fun i => cfg.α i ⬝ᵥ X / cfg.β i)
  refine h2 S hS fun x hx => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  exact h i

/-- `1 ≤ pt'` and `π(X') ≤ pt'` for `0 ≤ ε' < 1`. -/
theorem ptQ_ge (cfg : Cfg d) (X : Fin d → ℚ) (h0 : 0 ≤ cfg.par.eps) (h1 : cfg.par.eps < 1) :
    1 ≤ ptQ cfg X ∧ gaugeQ cfg X ≤ ptQ cfg X := by
  have hg := (gauge_spec cfg X).1
  refine ⟨le_max_left _ _, le_trans ?_ (le_max_right _ _)⟩
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- The kept rows: a nonzero row of `A` is a row of the list `keptIdx A`. -/
theorem kept_get {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (i : Fin m) (hA : A i ≠ 0) :
    ∃ k : Fin (keptIdx A).length, (keptIdx A).get k = i := by
  have : i ∈ keptIdx A := by
    unfold keptIdx
    exact List.mem_filter.2 ⟨List.mem_finRange i, by simpa using hA⟩
  exact List.mem_iff_get.1 this

/-- **The play of mode `run` is in the polytope.** -/
theorem play_mem {n m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ)
    (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ) (st : St d) (ξ : Fin d → ℚ) (hzero : ∀ i, A i = 0 → 0 ≤ b i)
    (heps : (par d n).eps ≤ 1 / 2) (heps0 : 0 ≤ (par d n).eps) (hβ : ∀ i, 0 < (mkCfg d n m A b c S).β i) :
    toE (playPt (mkCfg d n m A b c S) (.run st) ξ) ∈ RealRAM.polytope A b := by
  set cfg := mkCfg d n m A b c S with hcfg
  set X := XQ cfg st ξ
  set pt := ptQ cfg X
  have key : ∀ i, A i ⬝ᵥ playPt cfg (.run st) ξ ≤ b i := by
    intro i
    by_cases hA : A i = 0
    · rw [hA, zero_dotProduct]; exact hzero i hA
    obtain ⟨k, hk⟩ := kept_get A i hA
    have hβk := hβ k
    have hαk : cfg.α k = S.2ᵀ *ᵥ A i := by rw [← hk]; rfl
    have hβe : cfg.β k = b i - A i ⬝ᵥ S.1 := by rw [← hk]; rfl
    have heps1 : cfg.par.eps < 1 := by show (par d n).eps < 1; linarith
    obtain ⟨hpt1, hptg⟩ := ptQ_ge cfg X heps0 heps1
    have hg := (gauge_spec cfg X).2 k
    have hpt0 : (0 : ℚ) < pt := by linarith
    have h1 : cfg.α k ⬝ᵥ X ≤ pt * cfg.β k := by
      have := hg.trans hptg
      rwa [div_le_iff₀ hβk] at this
    show A i ⬝ᵥ (S.1 + S.2 *ᵥ (pt⁻¹ • X)) ≤ b i
    rw [dotProduct_add, dotProduct_mulVec, ← mulVec_transpose, ← hαk, dotProduct_smul, smul_eq_mul]
    have h2 : pt⁻¹ * (cfg.α k ⬝ᵥ X) ≤ cfg.β k := by
      rw [inv_mul_le_iff₀ hpt0]; exact h1
    rw [hβe] at h2
    linarith
  intro i
  have := key i
  have e : ∑ j, (A i j : ℝ) * (toE (playPt cfg (.run st) ξ)) j = ((A i ⬝ᵥ playPt cfg (.run st) ξ : ℚ) : ℝ) := by
    simp [dotProduct, toE]
  rw [e]
  exact_mod_cast this

/-- **The reading of an admissible loss at a point of the body is in `[0, 2^p]`.** -/
theorem obs_bnd {K : Set (E d)} {n : ℕ} {σ : RealRAM.Strategy d} (hσ : AdmStrat K n σ) (t : ℕ) (ht : t < n)
    (h : ℕ → Fin d → ℚ) (x : Fin d → ℚ) (hx : toE x ∈ K) (p : ℕ) :
    0 ≤ ⌊(2 : ℝ) ^ p * RealRAM.lossAd σ 0 (fun i => toE (h i)) t (toE x)⌋ ∧
      ⌊(2 : ℝ) ^ p * RealRAM.lossAd σ 0 (fun i => toE (h i)) t (toE x)⌋ ≤ 2 ^ p := by
  obtain ⟨-, hf⟩ := hσ t ht h
  obtain ⟨f0, f1⟩ := hf _ hx
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  constructor
  · exact Int.floor_nonneg.2 (mul_nonneg hp.le f0)
  · have h1 : ((⌊(2 : ℝ) ^ p * RealRAM.lossAd σ 0 (fun i => toE (h i)) t (toE x)⌋ : ℤ) : ℝ) ≤ ((2 ^ p : ℤ) : ℝ) := by
      push_cast
      exact (Int.floor_le _).trans (by nlinarith)
    exact_mod_cast h1

end AdversarialBco.Bit.Transfer.BLM
