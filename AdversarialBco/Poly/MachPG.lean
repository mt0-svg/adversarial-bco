/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachPGStage
public import AdversarialBco.Poly.Df2Run

@[expose] public section

/-!
# Procedure PG in VL: the rule of the code

`runs_pgCode`: from `draws = 0`, with `r₀`, `R₀`, `δ₁` in scalars, the code `pgCode` of MachPGCode.lean reads exactly
`df2oN0` terms of the stream, in the order of `df2oIdxA` and `df2oIdxT`, and ends with `ok = 0` if
`pg d w.K r₀ R₀ δ₁ (df2oOmega ..) = none`, with `ok = 1`, `μ = pgMu P`, `A = pgMat P` if it returns `some P`, in
`kPG d r₀ R₀ δ₁` steps. The leaves of the stage (the descent step, the sample, the verdict, the matrix product) enter
through the hypothesis `PgLeaves` of MachPGLoops.lean.
-/

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL
  Matrix

namespace AdversarialBco.Poly.PG

variable {d : ℕ}

/-! ## The procedure reads only the samples in range -/

theorem pgDescent_congr {K' : Set (EuclideanSpace ℝ (Fin d))} {ρ : ℝ} {a b : ℕ → EuclideanSpace ℝ (Fin d)}
    (h : ∀ k < pgNs d ρ, a k = b k) : pgDescent K' ρ a = pgDescent K' ρ b :=
  sgdAvg_congr _ _ _ _ _ a b h

theorem pgVerdict_congr {K' : Set (EuclideanSpace ℝ (Fin d))} {ρ : ℝ} {x : PgSp d}
    {u u' : ℕ → EuclideanSpace ℝ (Fin d)} (h : ∀ k < pgNT d ρ, u k = u' k) :
    pgVerdict K' ρ x u ↔ pgVerdict K' ρ x u' := by
  have e1 : ∑ i ∈ Finset.range (pgNT d ρ), pgFt K' ρ x (u i) = ∑ i ∈ Finset.range (pgNT d ρ), pgFt K' ρ x (u' i) :=
    Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]
  have e2 : ∑ i ∈ Finset.range (pgNT d ρ), pgFt K' ρ x (u i) • u i =
      ∑ i ∈ Finset.range (pgNT d ρ), pgFt K' ρ x (u' i) • u' i :=
    Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]
  have e3 : ∑ i ∈ Finset.range (pgNT d ρ), pgFt K' ρ x (u i) • pgGG (u i) =
      ∑ i ∈ Finset.range (pgNT d ρ), pgFt K' ρ x (u' i) • pgGG (u' i) :=
    Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]
  simp only [pgVerdict, e1, e2, e3]

open Classical in
theorem pgTest_congr {K' : Set (EuclideanSpace ℝ (Fin d))} {ρ δ : ℝ} {x : PgSp d}
    {u u' : ℕ → ℕ → EuclideanSpace ℝ (Fin d)} (h : ∀ v < pgMT δ, ∀ k < pgNT d ρ, u v k = u' v k) :
    pgTest K' ρ δ x u ↔ pgTest K' ρ δ x u' := by
  unfold pgTest
  have e : ∀ v ∈ Finset.range (pgMT δ), pgVerdict K' ρ x (u v) ↔ pgVerdict K' ρ x (u' v) :=
    fun v hv => pgVerdict_congr (h v (Finset.mem_range.1 hv))
  rw [Finset.filter_congr e]

theorem pgCore_congr {K' : Set (EuclideanSpace ℝ (Fin d))} {ρ δ : ℝ} {ω ω' : ℕ → PgRound d}
    (h1 : ∀ r < pgJr δ, ∀ k < pgNs d ρ, (ω r).1 k = (ω' r).1 k)
    (h2 : ∀ r < pgJr δ, ∀ v < pgMT δ, ∀ k < pgNT d ρ, (ω r).2 v k = (ω' r).2 v k) :
    pgCore d K' ρ δ ω = pgCore d K' ρ δ ω' := by
  have hD : ∀ r < pgJr δ, pgRepD K' ρ ω r = pgRepD K' ρ ω' r := fun r hr => pgDescent_congr (h1 r hr)
  have hT : ∀ r < pgJr δ, pgRepT K' ρ δ ω r ↔ pgRepT K' ρ δ ω' r := fun r hr => by
    unfold pgRepT; rw [hD r hr]; exact pgTest_congr (h2 r hr)
  by_cases hex : ∃ r < pgJr δ, pgRepT K' ρ δ ω r
  · have hex' : ∃ r < pgJr δ, pgRepT K' ρ δ ω' r := let ⟨r, hr, h⟩ := hex; ⟨r, hr, (hT r hr).1 h⟩
    obtain ⟨r, hr, hTr, hmin, hc⟩ := pgCore_some hex
    obtain ⟨r', hr', hTr', hmin', hc'⟩ := pgCore_some hex'
    have e : r = r' := by
      rcases lt_trichotomy r r' with h | h | h
      · exact absurd ((hT r hr).1 hTr) (hmin' r h)
      · exact h
      · exact absurd ((hT r' hr').2 hTr') (hmin r' h)
    subst e
    rw [hc, hc', hD r hr]
  · have hex' : ¬∃ r < pgJr δ, pgRepT K' ρ δ ω' r := fun ⟨r, hr, h⟩ => hex ⟨r, hr, (hT r hr).2 h⟩
    rw [pgCore_none hex, pgCore_none hex']

/-- Stage `i < m` of the stream of `pg` is the stream of the code from the first term of the stage. -/
theorem pgCore_df2oOmega (w : World d) (n : ℕ) {r0 R0 δ1 : ℝ} (K' : Set (EuclideanSpace ℝ (Fin d))) {i : ℕ}
    (hi : i < pgStages r0 R0) :
    pgCore d K' (pgRhoStage d i) (df2oPgDelta r0 R0 δ1) (df2oOmega d n r0 R0 δ1 w.gs i) =
      pgCore d K' (pgRhoStage d i) (df2oPgDelta r0 R0 δ1)
        (pgOmegaAt w (pgRhoStage d i) (df2oPgDelta r0 R0 δ1) (df2oPgOff d (df2oPgDelta r0 R0 δ1) i)) := by
  apply pgCore_congr
  · intro r hr k hk
    simp only [df2oOmega, pgOmegaAt]
    congr 1; funext c
    simp only [df2oIdxA]
    rw [if_pos (show i < pgStages r0 R0 ∧ r < pgJr (df2oPgDelta r0 R0 δ1) ∧ k < pgNs d (pgRhoStage d i) from ⟨hi, hr, hk⟩)]
    congr 1; simp only [pgW, df2oPgW]; ring
  · intro r hr v hv k hk
    simp only [df2oOmega, pgOmegaAt]
    congr 1; funext c
    simp only [df2oIdxT]
    rw [if_pos ⟨hi, hr, hv, hk⟩]
    congr 1; simp only [pgW, df2oPgW]; ring

theorem one_le_pgRhoStage (hd : 1 ≤ d) : ∀ i, 1 ≤ pgRhoStage d i
  | 0 => by simp [pgRhoStage]
  | i + 1 => by
    have ih := one_le_pgRhoStage hd i
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hlog : (1 / 4 : ℝ) ≤ Real.log (1 + pgRhoStage d i) := by
      have h2 : Real.log 2 ≤ Real.log (1 + pgRhoStage d i) := Real.log_le_log (by norm_num) (by linarith)
      have := Real.log_two_gt_d9
      linarith
    have hs : (1 / 2 : ℝ) ≤ Real.sqrt (Real.log (1 + pgRhoStage d i)) := by
      rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hlog
    simp only [pgRhoStage]
    nlinarith

/-! ## A stage followed by the next ratio and radius -/

/-- The flag and the position against the value of `pgStage`. -/
def PgPos (σ : Env d) (okv muv Av : ℕ) (o : Option (PgSp d)) : Prop :=
  (o = none ∧ σ.sc okv = 0) ∨ (∃ P, o = some P ∧ σ.sc okv = 1 ∧ PgAt σ muv Av P)

/-- The scalars a stage and the next ratio write (besides `ok`). -/
def pgBodyS (s0 : ℕ) : List ℕ := pgStageS s0 ++ [s0 + 19, s0 + 42]

theorem pgBodyS_not_mem {s0 x : ℕ} (h : x < s0 ∨ s0 + 64 ≤ x) : x ∉ pgBodyS s0 := by
  simp only [pgBodyS, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨pgStageS_not_mem h, by omega, by omega⟩

theorem df2oPgOff_succ (d : ℕ) (δ' : ℝ) (t : ℕ) :
    df2oPgOff d δ' (t + 1) = df2oPgOff d δ' t + pgJr δ' * (pgW d (pgRhoStage d t) δ' * d) := by
  simp only [df2oPgOff, Finset.sum_range_succ, df2oPgBlock, df2oPgW, pgW]; ring

theorem pgStage_succ_some {K : Set (EuclideanSpace ℝ (Fin d))} {r0 δ' : ℝ} {Ω : ℕ → ℕ → PgRound d} {t : ℕ}
    {P : PgSp d} (h : pgStage d K r0 δ' Ω t = some P) :
    pgStage d K r0 δ' Ω (t + 1) = (pgCore d (pgKi K (2 ^ (t + 1) * r0) P) (pgRhoStage d t) δ' (Ω t)).map (pgComp P) := by
  rw [pgStage, h]; rfl

theorem pgStage_succ_none {K : Set (EuclideanSpace ℝ (Fin d))} {r0 δ' : ℝ} {Ω : ℕ → ℕ → PgRound d} {t : ℕ}
    (h : pgStage d K r0 δ' Ω t = none) : pgStage d K r0 δ' Ω (t + 1) = none := by
  rw [pgStage, h]; rfl

theorem pgS19 (s0 : ℕ) : s0 + 19 ∉ pgStageS s0 := by simp [pgStageS, pgTmpS]
theorem pgS42 (s0 : ℕ) : s0 + 42 ∉ pgStageS s0 := by simp [pgStageS, pgTmpS]
theorem pgS48 (s0 : ℕ) : s0 + 48 ∉ pgStageS s0 := by simp [pgStageS, pgTmpS]

set_option maxHeartbeats 1000000 in
theorem runs_pgStageBody (hL : PgLeaves) {L : Layout} {w : World d} {dv one okv muv Av n0 s0 a0 : ℕ} {r0 δ' : ℝ}
    {Ω : ℕ → ℕ → PgRound d} {t : ℕ} (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS)
    (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv)
    (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) (hmuv : muv < L.NA)
    (hAv : Av < L.NA) (hmub : muv < a0 ∨ a0 + 32 ≤ muv) (hAb : Av < a0 ∨ a0 + 32 ≤ Av) (hmuA : muv ≠ Av)
    (hokv : okv < L.NS) (hokb : okv < s0 ∨ s0 + 64 ≤ okv) (hd1 : 1 ≤ d)
    (hΩ : ∀ K', pgCore d K' (pgRhoStage d t) δ' (Ω t) =
      pgCore d K' (pgRhoStage d t) δ' (pgOmegaAt w (pgRhoStage d t) δ' σ.draws))
    (hρ : σ.sc (s0 + 19) = pgRhoStage d t) (hR : σ.sc (s0 + 42) = 2 ^ (t + 1) * r0)
    (hdR : σ.sc (s0 + 48) = d) (hdd : σ.nat (n0 + 9) = d * d) (hJ : σ.nat (n0 + 16) = pgJr δ')
    (hmT : σ.nat (n0 + 14) = pgMT δ') (hPos : PgPos σ okv muv Av (pgStage d w.K r0 δ' Ω t)) :
    Runs L w (.seq (pgStageC L dv one okv muv Av n0 s0 a0) (pgRho L s0)) σ
      (kStage d (pgJb d (pgRhoStage d t)) (pgNs d (pgRhoStage d t)) (pgNT d (pgRhoStage d t)) (pgJr δ')
        (pgMT δ') + 8)
      (fun σ' => σ'.sc (s0 + 19) = pgRhoStage d (t + 1) ∧ σ'.sc (s0 + 42) = 2 ^ (t + 2) * r0 ∧
        σ'.draws = σ.draws + pgJr δ' * (pgW d (pgRhoStage d t) δ' * d) ∧
        PgPos σ' okv muv Av (pgStage d w.K r0 δ' Ω (t + 1)) ∧
        Env.Frame σ { σ' with draws := σ.draws } (pgStageN n0) (okv :: pgBodyS s0) (muv :: Av :: pgStageA a0)) := by
  obtain ⟨P0, hP0, hP0e⟩ : ∃ P0, PgAt σ muv Av P0 ∧ ∀ P, pgStage d w.K r0 δ' Ω t = some P → P0 = P := by
    rcases hPos with ⟨ho, -⟩ | ⟨P, ho, -, hP⟩
    · refine ⟨pgPack (WithLp.toLp 2 (σ.vec muv)) (σ.mat Av), ⟨?_, (pgMat_pgPack _ _).symm⟩, fun P h => by
        rw [ho] at h; cases h⟩
      rw [pgMu_pgPack]
    · exact ⟨P, hP, fun P' h => by rw [ho] at h; exact Option.some_inj.1 h⟩
  have hokS : okv ∉ [s0 + 2, s0 + 19, s0 + 42, s0 + 45, s0 + 46] := by simp; omega
  refine runs_seq (runs_pgStageC hL σ hn0 hs0 ha0 hdv hone hdvb honeb hd h1 hmuv hAv hmub hAb hmuA hokv hokb hd1
    (one_le_pgRhoStage hd1 t) hρ hdR hdd hJ hmT hP0) fun σ1 h => ?_
  obtain ⟨hS, hN, hD1, hF1⟩ := h
  rw [hR, ← hΩ] at hS hN
  have h19 : σ1.sc (s0 + 19) = σ.sc (s0 + 19) := hF1.2.1 _ (by simp only [List.mem_cons, not_or]; exact ⟨by omega, pgS19 s0⟩)
  have h42 : σ1.sc (s0 + 42) = σ.sc (s0 + 42) := hF1.2.1 _ (by simp only [List.mem_cons, not_or]; exact ⟨by omega, pgS42 s0⟩)
  have h48 : σ1.sc (s0 + 48) = d := (hF1.2.1 _ (by simp only [List.mem_cons, not_or]; exact ⟨by omega, pgS48 s0⟩)).trans hdR
  refine runs_mono (runs_pgRho σ1 hs0 h48) le_rfl fun σ2 h2 => ?_
  obtain ⟨h219, h242, hF2⟩ := h2
  have hok2 : σ2.sc okv = σ1.sc okv := hF2.2.1 _ hokS
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h219, h19, hρ]; rfl
  · rw [h242, h42, hR]; ring
  · rw [hF2.2.2.2.1, hD1]
  · rcases hPos with ⟨ho, hok⟩ | ⟨P, ho, hok, hP⟩
    · refine Or.inl ⟨pgStage_succ_none ho, ?_⟩
      rw [hok2]
      cases hc : pgCore d (pgKi w.K (2 ^ (t + 1) * r0) P0) (pgRhoStage d t) δ' (Ω t) with
      | none => exact (hN hc).1
      | some X => rw [(hS X hc).1, hok]
    · obtain rfl := hP0e P ho
      rw [pgStage_succ_some ho]
      cases hc : pgCore d (pgKi w.K (2 ^ (t + 1) * r0) P0) (pgRhoStage d t) δ' (Ω t) with
      | none => exact Or.inl ⟨rfl, by rw [hok2]; exact (hN hc).1⟩
      | some X =>
        exact Or.inr ⟨pgComp P0 X, rfl, by rw [hok2, (hS X hc).1, hok],
          (hS X hc).2.of_frame hF2 (by simp) (by simp)⟩
  · refine frameD_trans (Env.Frame.mono hF1 (fun _ h => h) (fun _ h => ?_) (fun _ h => h))
      (frameD_of_frame (Env.Frame.mono hF2 (by simp) (fun x hx => ?_) (by simp)))
    · simp only [List.mem_cons] at h ⊢
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_append_left _ h)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp only [pgBodyS, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
      rcases hx with h | h | h | h | h <;> subst h <;> simp [pgStageS, pgTmpS]

/-! ## The stages -/

/-- The naturals the stages and the stage counter write. -/
def pgLoopN (n0 : ℕ) : List ℕ := pgStageN n0 ++ [n0 + 19]

set_option maxHeartbeats 1000000 in
theorem runs_pgLoop (hL : PgLeaves) {L : Layout} {w : World d} {dv one okv muv Av n0 s0 a0 : ℕ} {r0 δ' : ℝ}
    {Ω : ℕ → ℕ → PgRound d} {m kB : ℕ} (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS)
    (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv)
    (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) (hmuv : muv < L.NA)
    (hAv : Av < L.NA) (hmub : muv < a0 ∨ a0 + 32 ≤ muv) (hAb : Av < a0 ∨ a0 + 32 ≤ Av) (hmuA : muv ≠ Av)
    (hokv : okv < L.NS) (hokb : okv < s0 ∨ s0 + 64 ≤ okv) (hd1 : 1 ≤ d) (hm : σ.nat (n0 + 18) = m)
    (hΩ : ∀ t < m, ∀ K', pgCore d K' (pgRhoStage d t) δ' (Ω t) =
      pgCore d K' (pgRhoStage d t) δ' (pgOmegaAt w (pgRhoStage d t) δ' (df2oPgOff d δ' t)))
    (hkB : ∀ t < m, kStage d (pgJb d (pgRhoStage d t)) (pgNs d (pgRhoStage d t)) (pgNT d (pgRhoStage d t))
      (pgJr δ') (pgMT δ') + 8 ≤ kB)
    (hρ : σ.sc (s0 + 19) = 2) (hR : σ.sc (s0 + 42) = 2 * r0) (hdR : σ.sc (s0 + 48) = d)
    (hdd : σ.nat (n0 + 9) = d * d) (hJ : σ.nat (n0 + 16) = pgJr δ') (hmT : σ.nat (n0 + 14) = pgMT δ')
    (hdr : σ.draws = 0) (hPos : PgPos σ okv muv Av (pgStage d w.K r0 δ' Ω 0)) :
    Runs L w (forN (n0 + 19) (n0 + 18) one (.seq (pgStageC L dv one okv muv Av n0 s0 a0) (pgRho L s0))) σ
      (m * (kB + 3) + 3)
      (fun σ' => σ'.draws = df2oPgOff d δ' m ∧ PgPos σ' okv muv Av (pgStage d w.K r0 δ' Ω m) ∧
        Env.Frame σ { σ' with draws := σ.draws } (pgLoopN n0) (okv :: pgBodyS s0) (muv :: Av :: pgStageA a0)) := by
  have nD : dv ∉ pgLoopN n0 := by simp [pgLoopN, pgStageN, pgTmpN]; omega
  have nO : one ∉ pgLoopN n0 := by simp [pgLoopN, pgStageN, pgTmpN]; omega
  have n9 : n0 + 9 ∉ pgLoopN n0 := by simp [pgLoopN, pgStageN, pgTmpN]
  have n14 : n0 + 14 ∉ pgLoopN n0 := by simp [pgLoopN, pgStageN, pgTmpN]
  have n16 : n0 + 16 ∉ pgLoopN n0 := by simp [pgLoopN, pgStageN, pgTmpN]
  have n18 : n0 + 18 ∉ pgStageN n0 := by simp [pgStageN, pgTmpN]
  have n19 : n0 + 19 ∉ pgStageN n0 := by simp [pgStageN, pgTmpN]
  have nOs : one ∉ pgStageN n0 := fun h => nO (List.mem_append_left _ h)
  have s48 : s0 + 48 ∉ okv :: pgBodyS s0 := by
    simp only [List.mem_cons, not_or]; exact ⟨by omega, by simp [pgBodyS, pgStageS, pgTmpS]⟩
  let J : ℕ → Env d → Prop := fun t σ' => σ'.sc (s0 + 19) = pgRhoStage d t ∧ σ'.sc (s0 + 42) = 2 ^ (t + 1) * r0 ∧
    σ'.draws = df2oPgOff d δ' t ∧ PgPos σ' okv muv Av (pgStage d w.K r0 δ' Ω t) ∧
    Env.Frame σ { σ' with draws := σ.draws } (pgLoopN n0) (okv :: pgBodyS s0) (muv :: Av :: pgStageA a0)
  have h0 : J 0 (σ.setNat (n0 + 19) 0) :=
    ⟨hρ, by rw [Env.setNat_sc, hR]; ring, by rw [Env.setNat_draws, hdr]; rfl, hPos,
      Env.Frame.setNat (Env.Frame.refl _ _ _ _) (by simp [pgLoopN]) 0⟩
  refine runs_mono (runs_forN (L := L) (w := w) (by omega) (by omega) hone (by omega) (by omega) m kB J σ hm h1 h0
    ?_) le_rfl fun σ' h => ⟨h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2⟩
  intro t ht σ' hJt hi hn h1'
  obtain ⟨j19, j42, jdr, jpos, jF⟩ := hJt
  refine runs_mono (runs_pgStageBody hL σ' hn0 hs0 ha0 hdv hone hdvb honeb ((jF.1 dv nD).trans hd) h1' hmuv hAv
    hmub hAb hmuA hokv hokb hd1 (by rw [jdr]; exact hΩ t ht) j19 j42 ((jF.2.1 _ s48).trans hdR)
    ((jF.1 _ n9).trans hdd) ((jF.1 _ n16).trans hJ) ((jF.1 _ n14).trans hmT) jpos) (hkB t ht) fun σ'' h => ?_
  obtain ⟨k19, k42, kdr, kpos, kF⟩ := h
  refine ⟨(kF.1 _ n19).trans hi, (kF.1 _ n18).trans hn, (kF.1 _ nOs).trans h1', k19, ?_, ?_, kpos, ?_⟩
  · show σ''.sc (s0 + 42) = _
    rw [k42]
  · show σ''.draws = _
    rw [kdr, jdr, df2oPgOff_succ]
  · exact Env.Frame.setNat (frameD_trans jF (Env.Frame.mono kF (fun _ h => List.mem_append_left _ h)
      (fun _ h => h) (fun _ h => h))) (by simp [pgLoopN]) (t + 1)

/-! ## The code of PG -/

/-- The step count of one stage and the next ratio, the largest over the stages. -/
noncomputable def kPGStage (d : ℕ) (r0 R0 δ₁ : ℝ) : ℕ :=
  (Finset.range (pgStages r0 R0)).sup fun i => kStage d (pgJb d (pgRhoStage d i)) (pgNs d (pgRhoStage d i))
    (pgNT d (pgRhoStage d i)) (pgJr (δ₁ / pgStages r0 R0)) (pgMT (δ₁ / pgStages r0 R0)) + 8

/-- The step count of the code of PG. -/
noncomputable def kPG (d : ℕ) (r0 R0 δ₁ : ℝ) : ℕ :=
  kCaps d ⌈Real.logb 2 (R0 / r0)⌉₊ (pgJr (δ₁ / pgStages r0 R0)) (pgMT (δ₁ / pgStages r0 R0)) +
    (1 + (1 + (d * 5 + 3 + (d * d * 5 + 3 + (d * 7 + 4 +
      (1 + (1 + (pgStages r0 R0 * (kPGStage d r0 R0 δ₁ + 3) + 3))))))))

/-- The naturals the code of PG writes. -/
def pgCodeN (n0 : ℕ) : List ℕ := pgLoopN n0 ++ [n0 + 9, n0 + 14, n0 + 16, n0 + 18]

/-- The scalars the code of PG writes (besides `ok`). -/
def pgCodeS (s0 : ℕ) : List ℕ := pgBodyS s0 ++ [s0 + 43, s0 + 48]

theorem pgPack_zero_smul_one (r0 : ℝ) :
    Matrix.of (fun a b : Fin d => if a = b then r0 else (0 : ℝ)) = pgMat (pgPack 0 (r0 • (1 : Matrix (Fin d) (Fin d) ℝ))) := by
  rw [pgMat_pgPack]; ext a b; simp [Matrix.one_apply]

set_option maxHeartbeats 1000000 in
theorem runs_pgCode (hL : PgLeaves) {L : Layout} {w : World d} {dv one r0v R0v δv okv muv Av n0 s0 a0 n : ℕ}
    {r0 R0 δ₁ : ℝ} (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA)
    (hdv : dv < L.NN) (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one)
    (hr0v : r0v < L.NS) (hR0v : R0v < L.NS) (hδv : δv < L.NS) (hr0b : r0v < s0 ∨ s0 + 64 ≤ r0v)
    (hR0b : R0v < s0 ∨ s0 + 64 ≤ R0v) (hδb : δv < s0 ∨ s0 + 64 ≤ δv) (hmuv : muv < L.NA) (hAv : Av < L.NA)
    (hmub : muv < a0 ∨ a0 + 32 ≤ muv) (hAb : Av < a0 ∨ a0 + 32 ≤ Av) (hmuA : muv ≠ Av) (hokv : okv < L.NS)
    (hokb : okv < s0 ∨ s0 + 64 ≤ okv) (hokr : okv ≠ r0v) (hd1 : 1 ≤ d) (hd : σ.nat dv = d) (h1 : σ.nat one = 1)
    (hr0 : σ.sc r0v = r0) (hR0 : σ.sc R0v = R0) (hδ : σ.sc δv = δ₁) (hdr : σ.draws = 0) :
    Runs L w (pgCode L dv one r0v R0v δv okv muv Av n0 s0 a0) σ (kPG d r0 R0 δ₁)
      (fun σ' => σ'.draws = df2oN0 d r0 R0 δ₁ ∧
        (pg d w.K r0 R0 δ₁ (df2oOmega d n r0 R0 δ₁ w.gs) = none → σ'.sc okv = 0) ∧
        (∀ P, pg d w.K r0 R0 δ₁ (df2oOmega d n r0 R0 δ₁ w.gs) = some P →
          σ'.sc okv = 1 ∧ σ'.vec muv = (fun i => pgMu P i) ∧ σ'.mat Av = pgMat P) ∧
        Env.Frame σ { σ' with draws := σ.draws } (pgCodeN n0) (okv :: pgCodeS s0) (muv :: Av :: pgStageA a0)) := by
  have hS0 : s0 < L.NS := by omega
  unfold pgCode kPG
  refine runs_seq (runs_pgCaps σ hn0 hs0 hdv hone hdvb honeb hr0v hR0v hδv hr0b hR0b hδb hd h1 hr0 hR0 hδ)
    fun σC hC => ?_
  obtain ⟨c9, c48, -, c18, -, c16, c14, hFC⟩ := hC
  have cd : σC.nat dv = d := (hFC.1 _ (by simp; omega)).trans hd
  have c1 : σC.nat one = 1 := (hFC.1 _ (by simp; omega)).trans h1
  have cr0 : σC.sc r0v = r0 := (hFC.2.1 _ (by simp; omega)).trans hr0
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := σC) (x := okv) hokv 1) ?_
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := σC.setSc okv ((1 : ℚ) : ℝ)) (x := s0) hS0 0) ?_
  set σ2 := (σC.setSc okv ((1 : ℚ) : ℝ)).setSc s0 ((0 : ℚ) : ℝ) with hσ2
  have F2 : Env.Frame σC σ2 [] [okv, s0] [] :=
    Env.Frame.setSc (Env.Frame.setSc (Env.Frame.refl σC [] [okv, s0] []) (by simp) _) (by simp) _
  have e2s0 : σ2.sc s0 = 0 := by simp [hσ2]
  have e2ok : σ2.sc okv = 1 := by simp [hσ2]; omega
  refine runs_seq (runs_vfill σ2 hdv hone (by omega) hmuv hS0 (by omega) (by omega) cd c1) fun σ3 h3 => ?_
  obtain ⟨v3, F3, -⟩ := h3
  have d3 : σ3.nat dv = d := (F3.1 _ (by simp; omega)).trans cd
  have o3 : σ3.nat one = 1 := (F3.1 _ (by simp; omega)).trans c1
  refine runs_seq (runs_mfill σ3 (by omega) hone (by omega) hAv hS0 (by omega) (by omega)
    ((F3.1 _ (by simp)).trans c9) o3) fun σ4 h4 => ?_
  obtain ⟨m4, F4, -⟩ := h4
  have d4 : σ4.nat dv = d := (F4.1 _ (by simp; omega)).trans d3
  have o4 : σ4.nat one = 1 := (F4.1 _ (by simp; omega)).trans o3
  refine runs_seq (runs_mdiag σ4 hdv hone (by omega) (by omega) hAv hr0v (by omega) (by omega) (by omega)
    (by omega) (by omega) d4 o4) fun σ5 h5 => ?_
  obtain ⟨m5, F5, -⟩ := h5
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := σ5) (x := s0 + 19) (by omega) 2) ?_
  refine runs_seq_eq (runs_sop2 (L := L) (w := w) (σ := σ5.setSc (s0 + 19) ((2 : ℚ) : ℝ)) (x := s0 + 42)
    (by omega) hr0v hr0v .add) ?_
  set σ7 := (σ5.setSc (s0 + 19) ((2 : ℚ) : ℝ)).setSc (s0 + 42)
    (Op2.add.eval ((σ5.setSc (s0 + 19) ((2 : ℚ) : ℝ)).sc r0v) ((σ5.setSc (s0 + 19) ((2 : ℚ) : ℝ)).sc r0v)) with hσ7
  have F25 : Env.Frame σ2 σ5 [n0, n0 + 2] [] [muv, Av] :=
    Env.Frame.trans (Env.Frame.mono F3 (by simp) (by simp) (by simp))
      (Env.Frame.trans (Env.Frame.mono F4 (by simp) (by simp) (by simp))
        (Env.Frame.mono F5 (by simp) (by simp) (by simp)))
  have F7a : Env.Frame σC σ5 [n0, n0 + 2] [okv, s0, s0 + 19, s0 + 42] [muv, Av] :=
    Env.Frame.trans (Env.Frame.mono F2 (by simp) (by simp) (by simp)) (Env.Frame.mono F25 (by simp) (by simp) (by simp))
  have F7 : Env.Frame σC σ7 [n0, n0 + 2] [okv, s0, s0 + 19, s0 + 42] [muv, Av] :=
    Env.Frame.setSc (Env.Frame.setSc F7a (by simp) _) (by simp) _
  have e5r0 : σ5.sc r0v = r0 := by
    rw [F25.2.1 _ (by simp), F2.2.1 _ (by simp; omega)]; exact cr0
  have e7r0 : (σ5.setSc (s0 + 19) ((2 : ℚ) : ℝ)).sc r0v = r0 := by
    rw [Env.setSc_sc, if_neg (by omega)]; exact e5r0
  have Fi : Env.Frame σ σ7 [n0, n0 + 2, n0 + 9, n0 + 14, n0 + 16, n0 + 18]
      [okv, s0, s0 + 2, s0 + 19, s0 + 42, s0 + 43, s0 + 45, s0 + 46, s0 + 48] [muv, Av] :=
    Env.Frame.trans (Env.Frame.mono hFC (by simp) (by simp) (by simp)) (Env.Frame.mono F7 (by simp) (by simp) (by simp))
  have hPos : PgPos σ7 okv muv Av (pgStage d w.K r0 (δ₁ / pgStages r0 R0) (df2oOmega d n r0 R0 δ₁ w.gs) 0) := by
    refine Or.inr ⟨_, rfl, ?_, ?_, ?_⟩
    · rw [hσ7, Env.setSc_sc, if_neg (by omega), Env.setSc_sc, if_neg (by omega), F25.2.1 _ (by simp)]
      exact e2ok
    · show σ5.vec muv = _
      rw [Env.vec_of_arr (F5.2.2.1 muv (by simp; exact hmuA)), Env.vec_of_arr (F4.2.2.1 muv (by simp; exact hmuA)), v3,
        e2s0, pgMu_pgPack]
      rfl
    · show σ5.mat Av = _
      rw [m5, m4, ← pgPack_zero_smul_one]
      have e3 : σ3.sc s0 = 0 := (F3.2.1 _ (by simp)).trans e2s0
      have e4 : σ4.sc r0v = r0 := by
        rw [F4.2.1 _ (by simp), F3.2.1 _ (by simp), F2.2.1 _ (by simp; omega)]; exact cr0
      ext a b; simp only [Matrix.of_apply, e3, e4]
  refine runs_mono (runs_pgLoop (Ω := df2oOmega d n r0 R0 δ₁ w.gs) hL σ7 hn0 hs0 ha0 hdv hone hdvb honeb
    ((Fi.1 _ (by simp; omega)).trans hd) ((Fi.1 _ (by simp; omega)).trans h1) hmuv hAv hmub hAb hmuA hokv hokb hd1
    ((F7.1 _ (by simp)).trans c18) (fun t ht K' => pgCore_df2oOmega w n K' ht)
    (fun t ht => Finset.le_sup (f := fun i => kStage d (pgJb d (pgRhoStage d i)) (pgNs d (pgRhoStage d i))
      (pgNT d (pgRhoStage d i)) (pgJr (δ₁ / pgStages r0 R0)) (pgMT (δ₁ / pgStages r0 R0)) + 8)
      (Finset.mem_range.2 ht))
    (by rw [hσ7, Env.setSc_sc, if_neg (by omega), Env.setSc_sc, if_pos rfl]; norm_num)
    (by rw [hσ7, Env.setSc_sc, if_pos rfl, e7r0]; simp [Op2.eval]; ring)
    ((F7.2.1 _ (by simp; omega)).trans c48) ((F7.1 _ (by simp)).trans c9) ((F7.1 _ (by simp)).trans c16)
    ((F7.1 _ (by simp)).trans c14) (Fi.2.2.2.1.trans hdr) hPos) le_rfl fun σ' h => ?_
  obtain ⟨hdr', hpos', hF'⟩ := h
  refine ⟨hdr', fun hn => ?_, fun P hP => ?_, frameD_trans (frameD_of_frame (Env.Frame.mono Fi
    (by simp [pgCodeN, pgLoopN, pgStageN, pgTmpN]) (by simp [pgCodeS, pgBodyS, pgStageS, pgTmpS]) (by simp)))
    (Env.Frame.mono hF' (fun _ h => List.mem_append_left _ h)
      (fun _ h => by
        simp only [List.mem_cons] at h ⊢
        exact h.imp_right fun h => List.mem_append_left _ h) (fun _ h => h))⟩
  · rcases hpos' with ⟨-, hok⟩ | ⟨P, hP, -⟩
    · exact hok
    · exact absurd (hP.symm.trans hn) (by simp)
  · rcases hpos' with ⟨hP', -⟩ | ⟨P', hP', hok, hA⟩
    · exact absurd (hP'.symm.trans hP) (by simp)
    · obtain rfl : P' = P := Option.some_inj.1 (hP'.symm.trans hP)
      exact ⟨hok, hA.1, hA.2⟩

end AdversarialBco.Poly.PG
