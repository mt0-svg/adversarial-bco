/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Conj1Arith.MachN.Stage
public import AdversarialBco.Poly.MachPG

@[expose] public section

/-!
# The rule of the code of PG-N with CLAMP-NS

`runs_pgCodeNS`: from `draws = 0`, with `r₀`, `R₀`, `δ₁` in scalars, the code `pgCodeNS` of MachN/Code.lean reads
exactly `df2oN0` terms of the stream and ends with `ok = 0` if `pgN clampNSRoutine d w.K r₀ R₀ δ₁ (df2oOmega ..)` is
`none`, with `ok = 1`, `μ = pgMu P`, `A = pgMat P` if it is `some P`, in `kPGNS d r₀ R₀ δ₁` steps. The rules of a
stage followed by the next ratio and radius (`runs_pgStageBodyNS`) and of the loop over the stages (`runs_pgLoopNS`)
run the stage `pgStageCNS` with the semantics of PG-N; the variable lists are those of PG (`pgStageN`, `pgLoopN`,
`pgCodeN`, `pgBodyS`, `pgCodeS`, Poly/MachPGStage.lean and Poly/MachPG.lean).
-/

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL
  AdversarialBco.Poly.PG Matrix

namespace AdversarialBco.Conj1Arith

variable {d : ℕ}

/-! ## PG-N reads only the samples in range -/

theorem pgDescentN_congr {K' : Set (EuclideanSpace ℝ (Fin d))} {ρ : ℝ} {a b : ℕ → EuclideanSpace ℝ (Fin d)}
    (h : ∀ k < pgNs d ρ, a k = b k) : pgDescentN clampNSRoutine K' ρ a = pgDescentN clampNSRoutine K' ρ b :=
  sgdAvg_congr _ _ _ _ _ a b h

theorem pgVerdictS_congr {K' : Set (EuclideanSpace ℝ (Fin d))} {ρ : ℝ} {x : PgSp d}
    {u u' : ℕ → EuclideanSpace ℝ (Fin d)} (h : ∀ k < pgNT d ρ, u k = u' k) :
    pgVerdictS K' ρ x u ↔ pgVerdictS K' ρ x u' := by
  have e1 : ∑ i ∈ Finset.range (pgNT d ρ), pgFt K' ρ x (u i) = ∑ i ∈ Finset.range (pgNT d ρ), pgFt K' ρ x (u' i) :=
    Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]
  have e2 : ∑ i ∈ Finset.range (pgNT d ρ), pgFt K' ρ x (u i) • u i =
      ∑ i ∈ Finset.range (pgNT d ρ), pgFt K' ρ x (u' i) • u' i :=
    Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]
  have e3 : ∑ i ∈ Finset.range (pgNT d ρ), pgFt K' ρ x (u i) • pgGG (u i) =
      ∑ i ∈ Finset.range (pgNT d ρ), pgFt K' ρ x (u' i) • pgGG (u' i) :=
    Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]
  simp only [pgVerdictS, pgKh, pgBh, pgQh, e1, e2, e3]

open Classical in
theorem pgTestS_congr {K' : Set (EuclideanSpace ℝ (Fin d))} {ρ δ : ℝ} {x : PgSp d}
    {u u' : ℕ → ℕ → EuclideanSpace ℝ (Fin d)} (h : ∀ v < pgMT δ, ∀ k < pgNT d ρ, u v k = u' v k) :
    pgTestS K' ρ δ x u ↔ pgTestS K' ρ δ x u' := by
  unfold pgTestS
  have e : ∀ v ∈ Finset.range (pgMT δ), pgVerdictS K' ρ x (u v) ↔ pgVerdictS K' ρ x (u' v) :=
    fun v hv => pgVerdictS_congr (h v (Finset.mem_range.1 hv))
  rw [Finset.filter_congr e]

theorem pgCoreN_congr {K' : Set (EuclideanSpace ℝ (Fin d))} {ρ δ : ℝ} {ω ω' : ℕ → PgRound d}
    (h1 : ∀ r < pgJr δ, ∀ k < pgNs d ρ, (ω r).1 k = (ω' r).1 k)
    (h2 : ∀ r < pgJr δ, ∀ v < pgMT δ, ∀ k < pgNT d ρ, (ω r).2 v k = (ω' r).2 v k) :
    pgCoreN clampNSRoutine d K' ρ δ ω = pgCoreN clampNSRoutine d K' ρ δ ω' := by
  have hD : ∀ r < pgJr δ, pgRepDN K' ρ ω r = pgRepDN K' ρ ω' r := fun r hr => pgDescentN_congr (h1 r hr)
  have hT : ∀ r < pgJr δ, pgRepTN K' ρ δ ω r ↔ pgRepTN K' ρ δ ω' r := fun r hr => by
    unfold pgRepTN; rw [hD r hr]; exact pgTestS_congr (h2 r hr)
  by_cases hex : ∃ r < pgJr δ, pgRepTN K' ρ δ ω r
  · have hex' : ∃ r < pgJr δ, pgRepTN K' ρ δ ω' r := let ⟨r, hr, h⟩ := hex; ⟨r, hr, (hT r hr).1 h⟩
    obtain ⟨r, hr, hTr, hmin, hc⟩ := pgCoreN_some hex
    obtain ⟨r', hr', hTr', hmin', hc'⟩ := pgCoreN_some hex'
    have e : r = r' := by
      rcases lt_trichotomy r r' with h | h | h
      · exact absurd ((hT r hr).1 hTr) (hmin' r h)
      · exact h
      · exact absurd ((hT r' hr').2 hTr') (hmin r' h)
    subst e
    rw [hc, hc', hD r hr]
  · have hex' : ¬∃ r < pgJr δ, pgRepTN K' ρ δ ω' r := fun ⟨r, hr, h⟩ => hex ⟨r, hr, (hT r hr).2 h⟩
    rw [pgCoreN_none hex, pgCoreN_none hex']

/-- Stage `i < m` of the stream `df2oOmega` of PG-N is the stream of the code from the first term of the stage. -/
theorem pgCoreN_df2oOmega (w : World d) (n : ℕ) {r0 R0 δ1 : ℝ} (K' : Set (EuclideanSpace ℝ (Fin d))) {i : ℕ}
    (hi : i < pgStages r0 R0) :
    pgCoreN clampNSRoutine d K' (pgRhoStage d i) (df2oPgDelta r0 R0 δ1) (df2oOmega d n r0 R0 δ1 w.gs i) =
      pgCoreN clampNSRoutine d K' (pgRhoStage d i) (df2oPgDelta r0 R0 δ1)
        (pgOmegaAt w (pgRhoStage d i) (df2oPgDelta r0 R0 δ1) (df2oPgOff d (df2oPgDelta r0 R0 δ1) i)) := by
  apply pgCoreN_congr
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

/-! ## A stage of PG-N followed by the next ratio and radius -/

theorem pgStageN_succ_some {K : Set (EuclideanSpace ℝ (Fin d))} {r0 δ' : ℝ} {Ω : ℕ → ℕ → PgRound d} {t : ℕ}
    {P : PgSp d} (h : pgStageN clampNSRoutine d K r0 δ' Ω t = some P) :
    pgStageN clampNSRoutine d K r0 δ' Ω (t + 1) =
      (pgCoreN clampNSRoutine d (pgKi K (2 ^ (t + 1) * r0) P) (pgRhoStage d t) δ' (Ω t)).map (pgComp P) := by
  rw [pgStageN, h]; rfl

theorem pgStageN_succ_none {K : Set (EuclideanSpace ℝ (Fin d))} {r0 δ' : ℝ} {Ω : ℕ → ℕ → PgRound d} {t : ℕ}
    (h : pgStageN clampNSRoutine d K r0 δ' Ω t = none) : pgStageN clampNSRoutine d K r0 δ' Ω (t + 1) = none := by
  rw [pgStageN, h]; rfl

set_option maxHeartbeats 1000000 in
theorem runs_pgStageBodyNS {L : Layout} {w : World d} {dv one okv muv Av n0 s0 a0 : ℕ} {r0 δ' : ℝ}
    {Ω : ℕ → ℕ → PgRound d} {t : ℕ} (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS)
    (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv)
    (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) (hmuv : muv < L.NA)
    (hAv : Av < L.NA) (hmub : muv < a0 ∨ a0 + 32 ≤ muv) (hAb : Av < a0 ∨ a0 + 32 ≤ Av) (hmuA : muv ≠ Av)
    (hokv : okv < L.NS) (hokb : okv < s0 ∨ s0 + 64 ≤ okv) (hd1 : 1 ≤ d)
    (hΩ : ∀ K', pgCoreN clampNSRoutine d K' (pgRhoStage d t) δ' (Ω t) =
      pgCoreN clampNSRoutine d K' (pgRhoStage d t) δ' (pgOmegaAt w (pgRhoStage d t) δ' σ.draws))
    (hρ : σ.sc (s0 + 19) = pgRhoStage d t) (hR : σ.sc (s0 + 42) = 2 ^ (t + 1) * r0)
    (hdR : σ.sc (s0 + 48) = d) (hdd : σ.nat (n0 + 9) = d * d) (hJ : σ.nat (n0 + 16) = pgJr δ')
    (hmT : σ.nat (n0 + 14) = pgMT δ') (hPos : PgPos σ okv muv Av (pgStageN clampNSRoutine d w.K r0 δ' Ω t)) :
    Runs L w (.seq (pgStageCNS L dv one okv muv Av n0 s0 a0) (pgRho L s0)) σ
      (kStageAt d (pgRhoStage d t) δ' + 8)
      (fun σ' => σ'.sc (s0 + 19) = pgRhoStage d (t + 1) ∧ σ'.sc (s0 + 42) = 2 ^ (t + 2) * r0 ∧
        σ'.draws = σ.draws + pgJr δ' * (pgW d (pgRhoStage d t) δ' * d) ∧
        PgPos σ' okv muv Av (pgStageN clampNSRoutine d w.K r0 δ' Ω (t + 1)) ∧
        Env.Frame σ { σ' with draws := σ.draws } (PG.pgStageN n0) (okv :: pgBodyS s0) (muv :: Av :: pgStageA a0)) := by
  obtain ⟨P0, hP0, hP0e⟩ : ∃ P0, PgAt σ muv Av P0 ∧ ∀ P, pgStageN clampNSRoutine d w.K r0 δ' Ω t = some P → P0 = P := by
    rcases hPos with ⟨ho, -⟩ | ⟨P, ho, -, hP⟩
    · refine ⟨pgPack (WithLp.toLp 2 (σ.vec muv)) (σ.mat Av), ⟨?_, (pgMat_pgPack _ _).symm⟩, fun P h => by
        rw [ho] at h; cases h⟩
      rw [pgMu_pgPack]
    · exact ⟨P, hP, fun P' h => by rw [ho] at h; exact Option.some_inj.1 h⟩
  have hokS : okv ∉ [s0 + 2, s0 + 19, s0 + 42, s0 + 45, s0 + 46] := by simp; omega
  refine runs_seq (runs_pgStageCNS σ hn0 hs0 ha0 hdv hone hdvb honeb hd h1 hmuv hAv hmub hAb hmuA hokv hokb hd1
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
    · refine Or.inl ⟨pgStageN_succ_none ho, ?_⟩
      rw [hok2]
      cases hc : pgCoreN clampNSRoutine d (pgKi w.K (2 ^ (t + 1) * r0) P0) (pgRhoStage d t) δ' (Ω t) with
      | none => exact (hN hc).1
      | some X => rw [(hS X hc).1, hok]
    · obtain rfl := hP0e P ho
      rw [pgStageN_succ_some ho]
      cases hc : pgCoreN clampNSRoutine d (pgKi w.K (2 ^ (t + 1) * r0) P0) (pgRhoStage d t) δ' (Ω t) with
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

set_option maxHeartbeats 1000000 in
theorem runs_pgLoopNS {L : Layout} {w : World d} {dv one okv muv Av n0 s0 a0 : ℕ} {r0 δ' : ℝ}
    {Ω : ℕ → ℕ → PgRound d} {m kB : ℕ} (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS)
    (ha0 : a0 + 32 ≤ L.NA) (hdv : dv < L.NN) (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv)
    (honeb : one < n0 ∨ n0 + 20 ≤ one) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) (hmuv : muv < L.NA)
    (hAv : Av < L.NA) (hmub : muv < a0 ∨ a0 + 32 ≤ muv) (hAb : Av < a0 ∨ a0 + 32 ≤ Av) (hmuA : muv ≠ Av)
    (hokv : okv < L.NS) (hokb : okv < s0 ∨ s0 + 64 ≤ okv) (hd1 : 1 ≤ d) (hm : σ.nat (n0 + 18) = m)
    (hΩ : ∀ t < m, ∀ K', pgCoreN clampNSRoutine d K' (pgRhoStage d t) δ' (Ω t) =
      pgCoreN clampNSRoutine d K' (pgRhoStage d t) δ' (pgOmegaAt w (pgRhoStage d t) δ' (df2oPgOff d δ' t)))
    (hkB : ∀ t < m, kStageAt d (pgRhoStage d t) δ' + 8 ≤ kB)
    (hρ : σ.sc (s0 + 19) = 2) (hR : σ.sc (s0 + 42) = 2 * r0) (hdR : σ.sc (s0 + 48) = d)
    (hdd : σ.nat (n0 + 9) = d * d) (hJ : σ.nat (n0 + 16) = pgJr δ') (hmT : σ.nat (n0 + 14) = pgMT δ')
    (hdr : σ.draws = 0) (hPos : PgPos σ okv muv Av (pgStageN clampNSRoutine d w.K r0 δ' Ω 0)) :
    Runs L w (forN (n0 + 19) (n0 + 18) one (.seq (pgStageCNS L dv one okv muv Av n0 s0 a0) (pgRho L s0))) σ
      (m * (kB + 3) + 3)
      (fun σ' => σ'.draws = df2oPgOff d δ' m ∧ PgPos σ' okv muv Av (pgStageN clampNSRoutine d w.K r0 δ' Ω m) ∧
        Env.Frame σ { σ' with draws := σ.draws } (PG.pgLoopN n0) (okv :: pgBodyS s0) (muv :: Av :: pgStageA a0)) := by
  have nD : dv ∉ PG.pgLoopN n0 := by simp [PG.pgLoopN, PG.pgStageN, pgTmpN]; omega
  have nO : one ∉ PG.pgLoopN n0 := by simp [PG.pgLoopN, PG.pgStageN, pgTmpN]; omega
  have n9 : n0 + 9 ∉ PG.pgLoopN n0 := by simp [PG.pgLoopN, PG.pgStageN, pgTmpN]
  have n14 : n0 + 14 ∉ PG.pgLoopN n0 := by simp [PG.pgLoopN, PG.pgStageN, pgTmpN]
  have n16 : n0 + 16 ∉ PG.pgLoopN n0 := by simp [PG.pgLoopN, PG.pgStageN, pgTmpN]
  have n18 : n0 + 18 ∉ PG.pgStageN n0 := by simp [PG.pgStageN, pgTmpN]
  have n19 : n0 + 19 ∉ PG.pgStageN n0 := by simp [PG.pgStageN, pgTmpN]
  have nOs : one ∉ PG.pgStageN n0 := fun h => nO (List.mem_append_left _ h)
  have s48 : s0 + 48 ∉ okv :: pgBodyS s0 := by
    simp only [List.mem_cons, not_or]; exact ⟨by omega, by simp [pgBodyS, pgStageS, pgTmpS]⟩
  let J : ℕ → Env d → Prop := fun t σ' => σ'.sc (s0 + 19) = pgRhoStage d t ∧ σ'.sc (s0 + 42) = 2 ^ (t + 1) * r0 ∧
    σ'.draws = df2oPgOff d δ' t ∧ PgPos σ' okv muv Av (pgStageN clampNSRoutine d w.K r0 δ' Ω t) ∧
    Env.Frame σ { σ' with draws := σ.draws } (PG.pgLoopN n0) (okv :: pgBodyS s0) (muv :: Av :: pgStageA a0)
  have h0 : J 0 (σ.setNat (n0 + 19) 0) :=
    ⟨hρ, by rw [Env.setNat_sc, hR]; ring, by rw [Env.setNat_draws, hdr]; rfl, hPos,
      Env.Frame.setNat (Env.Frame.refl _ _ _ _) (by simp [PG.pgLoopN]) 0⟩
  refine runs_mono (runs_forN (L := L) (w := w) (by omega) (by omega) hone (by omega) (by omega) m kB J σ hm h1 h0
    ?_) le_rfl fun σ' h => ⟨h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2⟩
  intro t ht σ' hJt hi hn h1'
  obtain ⟨j19, j42, jdr, jpos, jF⟩ := hJt
  refine runs_mono (runs_pgStageBodyNS σ' hn0 hs0 ha0 hdv hone hdvb honeb ((jF.1 dv nD).trans hd) h1' hmuv hAv
    hmub hAb hmuA hokv hokb hd1 (by rw [jdr]; exact hΩ t ht) j19 j42 ((jF.2.1 _ s48).trans hdR)
    ((jF.1 _ n9).trans hdd) ((jF.1 _ n16).trans hJ) ((jF.1 _ n14).trans hmT) jpos) (hkB t ht) fun σ'' h => ?_
  obtain ⟨k19, k42, kdr, kpos, kF⟩ := h
  refine ⟨(kF.1 _ n19).trans hi, (kF.1 _ n18).trans hn, (kF.1 _ nOs).trans h1', k19, ?_, ?_, kpos, ?_⟩
  · show σ''.sc (s0 + 42) = _
    rw [k42]
  · show σ''.draws = _
    rw [kdr, jdr, df2oPgOff_succ]
  · exact Env.Frame.setNat (frameD_trans jF (Env.Frame.mono kF (fun _ h => List.mem_append_left _ h)
      (fun _ h => h) (fun _ h => h))) (by simp [PG.pgLoopN]) (t + 1)

/-! ## The code of PG-N -/

set_option maxHeartbeats 1000000 in
theorem runs_pgCodeNS {L : Layout} {w : World d} {dv one r0v R0v δv okv muv Av n0 s0 a0 n : ℕ}
    {r0 R0 δ₁ : ℝ} (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA)
    (hdv : dv < L.NN) (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one)
    (hr0v : r0v < L.NS) (hR0v : R0v < L.NS) (hδv : δv < L.NS) (hr0b : r0v < s0 ∨ s0 + 64 ≤ r0v)
    (hR0b : R0v < s0 ∨ s0 + 64 ≤ R0v) (hδb : δv < s0 ∨ s0 + 64 ≤ δv) (hmuv : muv < L.NA) (hAv : Av < L.NA)
    (hmub : muv < a0 ∨ a0 + 32 ≤ muv) (hAb : Av < a0 ∨ a0 + 32 ≤ Av) (hmuA : muv ≠ Av) (hokv : okv < L.NS)
    (hokb : okv < s0 ∨ s0 + 64 ≤ okv) (hokr : okv ≠ r0v) (hd1 : 1 ≤ d) (hd : σ.nat dv = d) (h1 : σ.nat one = 1)
    (hr0 : σ.sc r0v = r0) (hR0 : σ.sc R0v = R0) (hδ : σ.sc δv = δ₁) (hdr : σ.draws = 0) :
    Runs L w (pgCodeNS L dv one r0v R0v δv okv muv Av n0 s0 a0) σ (kPGNS d r0 R0 δ₁)
      (fun σ' => σ'.draws = df2oN0 d r0 R0 δ₁ ∧
        (pgN clampNSRoutine d w.K r0 R0 δ₁ (df2oOmega d n r0 R0 δ₁ w.gs) = none → σ'.sc okv = 0) ∧
        (∀ P, pgN clampNSRoutine d w.K r0 R0 δ₁ (df2oOmega d n r0 R0 δ₁ w.gs) = some P →
          σ'.sc okv = 1 ∧ σ'.vec muv = (fun i => pgMu P i) ∧ σ'.mat Av = pgMat P) ∧
        Env.Frame σ { σ' with draws := σ.draws } (PG.pgCodeN n0) (okv :: pgCodeS s0) (muv :: Av :: pgStageA a0)) := by
  have hS0 : s0 < L.NS := by omega
  unfold pgCodeNS kPGNS
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
  have hPos : PgPos σ7 okv muv Av (pgStageN clampNSRoutine d w.K r0 (δ₁ / pgStages r0 R0) (df2oOmega d n r0 R0 δ₁ w.gs) 0) := by
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
  refine runs_mono (runs_pgLoopNS (Ω := df2oOmega d n r0 R0 δ₁ w.gs) σ7 hn0 hs0 ha0 hdv hone hdvb honeb
    ((Fi.1 _ (by simp; omega)).trans hd) ((Fi.1 _ (by simp; omega)).trans h1) hmuv hAv hmub hAb hmuA hokv hokb hd1
    ((F7.1 _ (by simp)).trans c18) (fun t ht K' => pgCoreN_df2oOmega w n K' ht)
    (fun t ht => Finset.le_sup (f := fun i => kStageAt d (pgRhoStage d i) (δ₁ / pgStages r0 R0) + 8)
      (Finset.mem_range.2 ht))
    (by rw [hσ7, Env.setSc_sc, if_neg (by omega), Env.setSc_sc, if_pos rfl]; norm_num)
    (by rw [hσ7, Env.setSc_sc, if_pos rfl, e7r0]; simp [Op2.eval]; ring)
    ((F7.2.1 _ (by simp; omega)).trans c48) ((F7.1 _ (by simp)).trans c9) ((F7.1 _ (by simp)).trans c16)
    ((F7.1 _ (by simp)).trans c14) (Fi.2.2.2.1.trans hdr) hPos) le_rfl fun σ' h => ?_
  obtain ⟨hdr', hpos', hF'⟩ := h
  refine ⟨hdr', fun hn => ?_, fun P hP => ?_, frameD_trans (frameD_of_frame (Env.Frame.mono Fi
    (by simp [PG.pgCodeN, PG.pgLoopN, PG.pgStageN, pgTmpN]) (by simp [pgCodeS, pgBodyS, pgStageS, pgTmpS]) (by simp)))
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

end AdversarialBco.Conj1Arith
