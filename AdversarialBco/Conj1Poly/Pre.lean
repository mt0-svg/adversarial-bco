/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Poly.PreProof

@[expose] public section

/-!
# Theorem 1.3, the prefix PRE^b (Section 8.6 of the paper)

`PreOK r pre cpre kpre` is what the composition needs of the prefix: it has no query; run from `initPoly` inside any
program that holds it at address `0`, under the hypotheses of `TheoremConj1UpperPoly` and in any world, it plays
nothing, and after `T ≤ cpre (d m log (2 M))^kpre` steps it reaches a state related by `SimRel` (with `pc` the start of
`S(P)`) to the initial state `init d n (1/2) n δ` of `TheoremConj1Upper`, at a centre `a₀` with `B(a₀, 1/2) ⊆ K`.

`exists_pre` (C2) is the code of PRE^b with its proof: the layout of the frame above
the rows, the products `ρ |a_i|`, the stages `R_j = 2^{2^j}` of CENTRE-cap at the margin `1/2` (`stageRes`), whose
number of tests `stages_count` bounds through `polytope_sub_ball` (Lemma 8.12), the cells `b'_i`, the three cells
`1/2`, `n`, `δ` at `OFF`, the reset of the register `2`, and the jump to `S(P)`. It is the coupled part of the proof,
composed here from the runs of PreProof.lean (`setup_exec`, `outer_exec`, `frame_exec`) with `exec_sim` and
`kept_of_rounds`.
-/

open MeasureTheory Matrix

namespace AdversarialBco.Conj1Poly

open AdversarialBco.RealRAM AdversarialBco.Poly.Mach

/-- What the prefix achieves, for the frame based at the register `r`. The number of steps `T` and the centre `a₀`
depend on the instance only, not on the world: the prefix reads neither the body, nor the losses, nor the Gaussian
stream. -/
def PreOK (r : ℕ) (pre : List Instr) (cpre : ℝ) (kpre : ℕ) : Prop :=
  QueryFree pre ∧
    ∀ Q : List Instr, CodeAt Q 0 pre → ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 1 ≤ n → ∀ m M : ℕ, ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ (Am : Matrix (Fin m) (Fin d) ℚ) (bv : Fin m → ℚ), HeightLE Am bv M →
      (∃ c : E d, Metric.closedBall c 1 ⊆ polytope Am bv) →
      (∀ x ∈ polytope Am bv, ∀ y ∈ polytope Am bv, dist x y ≤ n) →
    ∃ (T : ℕ) (a0 : E d),
      (T : ℝ) ≤ cpre * ((d : ℝ) * m * Real.log (2 * M)) ^ kpre ∧
      Metric.closedBall a0 (1 / 2) ⊆ polytope Am bv ∧
      ∀ w : World d, (∀ k ≤ T, (run Q w (initPoly d n m δ Am bv) k).rounds = 0 ∧
        (run Q w (initPoly d n m δ Am bv) k).pts = (initPoly d n m δ Am bv).pts) ∧
      ∀ τ : ℕ → ℕ, τ 0 = pre.length →
        SimRel r τ a0 Am bv (init d n (1 / 2) n δ) (run Q w (initPoly d n m δ Am bv) T)

/-- The steps of PRE^b: the set-up, the stages up to `jStarOf (Rloc d m M)`, the frame. -/
noncomputable def preK (d m M : ℕ) : ℕ :=
  (4 * m + 4 * d + 60) +
    (((jStarOf (Rloc d m M) + 1) * (stageK d m (jStarOf (Rloc d m M)) + 2) + 2) + (10 * (d + 1) * (m + 1) + 10))

/-- The steps of PRE^b are polynomial in `d`, `m` and `log (2 M)`. -/
theorem preK_le : ∃ (cpre : ℝ) (kpre : ℕ), ∀ d m M : ℕ, 1 ≤ d → 1 ≤ m → 1 ≤ M →
    (preK d m M : ℝ) ≤ cpre * ((d : ℝ) * m * Real.log (2 * M)) ^ kpre := by
  refine ⟨10 ^ 9 / Real.log 2 ^ 13, 13, fun d m M hd hm hM => ?_⟩
  have hℓ0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hℓ1 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hD : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hMm : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hvℓ : Real.log 2 ≤ Real.log (2 * M) := Real.log_le_log (by norm_num) (by linarith)
  -- `u = log (2 M) / log 2 ≥ 1` and `Z = d m u ≥ 1`
  obtain ⟨u, hu⟩ : ∃ u, u = Real.log (2 * M) / Real.log 2 := ⟨_, rfl⟩
  have hu1 : 1 ≤ u := by rw [hu]; exact (one_le_div hℓ0).2 hvℓ
  have hvu : Real.log (2 * M) = Real.log 2 * u := by rw [hu]; field_simp
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = (d : ℝ) * m * u := ⟨_, rfl⟩
  have hmu : 1 ≤ (m : ℝ) * u := one_le_mul_of_one_le_of_one_le hMm hu1
  have hdu : 1 ≤ (d : ℝ) * u := one_le_mul_of_one_le_of_one_le hD hu1
  have hdm : 1 ≤ (d : ℝ) * m := one_le_mul_of_one_le_of_one_le hD hMm
  have hZd : (d : ℝ) ≤ Z := by
    rw [hZ, mul_assoc]; exact le_mul_of_one_le_right (by linarith) hmu
  have hZm : (m : ℝ) ≤ Z := by
    rw [hZ, mul_comm (d : ℝ) m, mul_assoc]; exact le_mul_of_one_le_right (by linarith) hdu
  have hZu : u ≤ Z := by
    rw [hZ]; exact le_mul_of_one_le_left (by linarith) hdm
  have hZ1 : 1 ≤ Z := hD.trans hZd
  have hZp : ∀ a ≤ 13, Z ^ a ≤ Z ^ 13 := fun a ha => pow_le_pow_right₀ hZ1 ha
  -- `log (2 R) ≤ 13 Z ^ 3`
  have hR := one_le_Rloc hd hm hM
  have hd0 : (0 : ℝ) < d := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hM0 : (0 : ℝ) < M := by linarith
  have hlog2R : Real.log (2 * Rloc d m M) =
      Real.log 2 + ((d : ℝ) + 1) * (Real.log d + Real.log m + 2 * ((d : ℝ) + 1) * Real.log M) := by
    unfold Rloc
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  have l1 : Real.log d ≤ Z := (Real.log_le_sub_one_of_pos hd0).trans (by linarith)
  have l2 : Real.log m ≤ Z := (Real.log_le_sub_one_of_pos hm0).trans (by linarith)
  have l3 : Real.log M ≤ Z := by
    have h1 : Real.log M ≤ Real.log (2 * M) := Real.log_le_log hM0 (by linarith)
    have h2 : Real.log 2 * u ≤ u := by nlinarith
    linarith
  have l1' : 0 ≤ Real.log d := Real.log_nonneg hD
  have l2' : 0 ≤ Real.log m := Real.log_nonneg hMm
  have l3' : 0 ≤ Real.log M := Real.log_nonneg hMr
  have hd1 : (d : ℝ) + 1 ≤ 2 * Z := by linarith
  have hlogR : Real.log (2 * Rloc d m M) ≤ 13 * Z ^ 3 := by
    rw [hlog2R]
    have h1 : Real.log d + Real.log m + 2 * ((d : ℝ) + 1) * Real.log M ≤ Z + Z + 2 * (2 * Z) * Z := by
      gcongr
    have h2 : ((d : ℝ) + 1) * (Real.log d + Real.log m + 2 * ((d : ℝ) + 1) * Real.log M) ≤
        (2 * Z) * (Z + Z + 2 * (2 * Z) * Z) := by
      gcongr
    have h3 : Z ^ 2 ≤ Z ^ 3 := pow_le_pow_right₀ hZ1 (by norm_num)
    have h4 : 1 ≤ Z ^ 3 := one_le_pow₀ hZ1
    nlinarith
  -- the stages
  have hsum := stages_count hd hR
  have hX : 40 * (d : ℝ) ^ 2 * (Real.log (2 * Rloc d m M) + 1) ≤ 560 * Z ^ 5 := by
    have h4 : 1 ≤ Z ^ 3 := one_le_pow₀ hZ1
    have h5 : (d : ℝ) ^ 2 ≤ Z ^ 2 := by gcongr
    calc 40 * (d : ℝ) ^ 2 * (Real.log (2 * Rloc d m M) + 1) ≤ 40 * Z ^ 2 * (13 * Z ^ 3 + Z ^ 3) := by
          gcongr
          have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * Rloc d m M); linarith
      _ = 560 * Z ^ 5 := by ring
  unfold preK stageK
  generalize jStarOf (Rloc d m M) = J at hsum ⊢
  have hJ1 : ((J : ℝ) + 1) ≤ 560 * Z ^ 5 := by
    have h : ∑ j ∈ Finset.range (J + 1), (1 : ℝ) ≤ ∑ j ∈ Finset.range (J + 1), (stageN d j : ℝ) :=
      Finset.sum_le_sum fun j _ => Nat.one_le_cast.mpr (by unfold stageN; omega)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h
    push_cast at h
    linarith
  have hN1 : (stageN d J : ℝ) + 1 ≤ 561 * Z ^ 5 := by
    have h : (stageN d J : ℝ) ≤ ∑ j ∈ Finset.range (J + 1), (stageN d j : ℝ) :=
      Finset.single_le_sum (f := fun j => (stageN d j : ℝ)) (fun j _ => Nat.cast_nonneg _)
        (Finset.self_mem_range_succ J)
    have : 1 ≤ Z ^ 5 := one_le_pow₀ hZ1
    linarith
  have hB : 100 * ((d : ℝ) + 1) * ((d : ℝ) + 1) * ((m : ℝ) + 1) ≤ 800 * Z ^ 3 := by
    have h2 : (m : ℝ) + 1 ≤ 2 * Z := by linarith
    calc 100 * ((d : ℝ) + 1) * ((d : ℝ) + 1) * ((m : ℝ) + 1) ≤ 100 * (2 * Z) * (2 * Z) * (2 * Z) := by gcongr
      _ = 800 * Z ^ 3 := by ring
  have hmain : ((J : ℝ) + 1) * (((stageN d J : ℝ) + 1) * (100 * ((d : ℝ) + 1) * ((d : ℝ) + 1) * ((m : ℝ) + 1)) + 2) ≤
      560 * Z ^ 5 * (561 * Z ^ 5 * (800 * Z ^ 3) + 2) := by
    gcongr
  have key : (((4 * m + 4 * d + 60) + (((J + 1) * ((stageN d J + 1) * (100 * (d + 1) * (d + 1) * (m + 1)) + 2) + 2) +
      (10 * (d + 1) * (m + 1) + 10)) : ℕ) : ℝ) ≤ 10 ^ 9 * Z ^ 13 := by
    push_cast
    have e1 : 560 * Z ^ 5 * (561 * Z ^ 5 * (800 * Z ^ 3) + 2) = 251328000 * Z ^ 13 + 1120 * Z ^ 5 := by ring
    have h5 := hZp 5 (by norm_num)
    have h2 := hZp 2 (by norm_num)
    have h1 := hZp 1 (by norm_num)
    have h0 : 1 ≤ Z ^ 13 := one_le_pow₀ hZ1
    have hdm2 : ((d : ℝ) + 1) * ((m : ℝ) + 1) ≤ 4 * Z ^ 2 := by
      have h2 : (m : ℝ) + 1 ≤ 2 * Z := by linarith
      calc ((d : ℝ) + 1) * ((m : ℝ) + 1) ≤ (2 * Z) * (2 * Z) := by gcongr
        _ = 4 * Z ^ 2 := by ring
    rw [pow_one] at h1
    nlinarith
  refine key.trans (le_of_eq ?_)
  rw [hZ, hvu]
  field_simp

/-- The world with an empty body, no loss, no noise and no draw: the prefix runs the same in every world. -/
def world0 (d : ℕ) : World d := ⟨∅, fun _ _ => 0, fun _ => 0, fun _ => 0⟩

/-- C2: the code of PRE^b and its proof. -/
theorem exists_pre (r : ℕ) (hr : 4 ≤ r) : ∃ (pre : List Instr) (cpre : ℝ) (kpre : ℕ), PreOK r pre cpre kpre := by
  obtain ⟨cpre, kpre, hK⟩ := preK_le
  refine ⟨(preCmd r).compile 0, cpre, kpre, fun dst src => cmdPure_noQuery (preCmd_pure r) 0 dst src, ?_⟩
  intro Q hQ d hd n hn m M δ hδ0 hδ1 Am bv hH hball hdiam
  have hm := Conj1PolySanity.one_le_m hd Am bv hdiam
  have hM := Conj1PolySanity.one_le_M hm Am bv hH
  have hloc := polytope_sub_ball Am bv hd hm hM hH (isCompact_polytope Am bv n hdiam)
  obtain ⟨z, hz⟩ := hball
  obtain ⟨s1, e1, hc1, hR1, hf1⟩ := setup_exec (w := world0 d) (n := n) (δ := δ) Am bv hr
  obtain ⟨k2, s2, hk2, e2, hc2, j, hj⟩ := outer_exec (w := world0 d) hd hc1 hloc z hz hR1 hf1
  set a0 : E d := WithLp.toLp 2 (rdVec s2 (lFa d m)) with ha0
  obtain ⟨k3, s3, hk3, e3, hro3, hsim⟩ :=
    frame_exec (w := world0 d) hd hr hc2 a0 rfl ((preCmd r).compile 0).length
  have e : Exec (world0 d) (preCmd r) (initPoly d n m δ Am bv) ((4 * m + 4 * d + 60) + (k2 + k3)) s3 :=
    Exec.seq e1 (Exec.seq e2 e3)
  refine ⟨(4 * m + 4 * d + 60) + (k2 + k3), a0, ?_, ?_, fun w => ?_⟩
  · refine le_trans ?_ (hK d m M hd hm hM)
    have : (4 * m + 4 * d + 60) + (k2 + k3) ≤ preK d m M := by unfold preK; omega
    exact_mod_cast this
  · have hs : centreRun Am bv (1 / 2) (stageN d j) (((stageR j) ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) 0 =
        some (rdVec s2 (lFa d m)) := hj
    exact rowOK_ball Am bv (by norm_num) (centreRun_sound Am bv (1 / 2) _ _ _ _ hs)
  · have ew := cmdPure_exec_world (preCmd_pure r) e w
    have hrun := exec_sim (P := Q) ew 0 hQ
    have h0 : atPc (initPoly d n m δ Am bv) 0 = initPoly d n m δ Am bv := atPc_self _
    rw [h0, Nat.zero_add] at hrun
    have hro : (run Q w (initPoly d n m δ Am bv) ((4 * m + 4 * d + 60) + (k2 + k3))).rounds =
        (initPoly d n m δ Am bv).rounds := by
      rw [hrun]; exact hro3
    refine ⟨fun k hk => kept_of_rounds Q w _ hro k hk, fun τ hτ => ?_⟩
    rw [hrun, ← Cmd.length_compile (preCmd r) 0]
    exact hsim τ hτ

end AdversarialBco.Conj1Poly
