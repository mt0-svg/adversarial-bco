/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachPGPar
public import AdversarialBco.Poly.MachPGLoops

@[expose] public section

/-!
# Procedure PG in VL: the rule of one stage

`runs_pgStageC`: the parameters of the stage from `ρ`, the `J` repeats, each a descent and an amplified test on the
stream `pgOmegaAt` (repeat `r` reads `W d` draws from `b + r W d`), the first accepted average kept, then the
composition with the current position, or `ok := 0` when no repeat is accepted: the stage computes `pgCore`
(`pgCore_some`, `pgCore_none`).
-/

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL
  Matrix

namespace AdversarialBco.Poly.PG

variable {d : ℕ}

/-- The samples of one repeat of a stage: the `N` steps of the descent, then the `m_T` blocks of `n_T` samples of the
amplified test. -/
noncomputable def pgW (d : ℕ) (ρ δ : ℝ) : ℕ := pgNs d ρ + pgMT δ * pgNT d ρ

/-- The stream of the repeats of a stage that starts at the draw `b`: repeat `r` reads the `W d` draws from
`b + r W d`, the `N` samples of the descent first, then the `m_T` blocks of `n_T` samples of the test. -/
noncomputable def pgOmegaAt (w : World d) (ρ δ : ℝ) (b : ℕ) : ℕ → PgRound d := fun r =>
  (fun k => WithLp.toLp 2 fun c => w.gs (b + r * (pgW d ρ δ * d) + k * d + c),
    fun v k => WithLp.toLp 2 fun c => w.gs (b + r * (pgW d ρ δ * d) + pgNs d ρ * d + (v * pgNT d ρ + k) * d + c))

/-- The average point of the descent of repeat `r`. -/
noncomputable def pgRepD (K' : Set (EuclideanSpace ℝ (Fin d))) (ρ : ℝ) (ω : ℕ → PgRound d) (r : ℕ) : PgSp d :=
  pgDescent K' ρ (ω r).1

/-- The amplified test of repeat `r` accepts. -/
def pgRepT (K' : Set (EuclideanSpace ℝ (Fin d))) (ρ δ : ℝ) (ω : ℕ → PgRound d) (r : ℕ) : Prop :=
  pgTest K' ρ δ (pgRepD K' ρ ω r) (ω r).2

open Classical in
theorem pgCore_eq (K' : Set (EuclideanSpace ℝ (Fin d))) (ρ δ : ℝ) (ω : ℕ → PgRound d) :
    pgCore d K' ρ δ ω = if h : ∃ r < pgJr δ, pgRepT K' ρ δ ω r then
      some (pgOut (pgRepD K' ρ ω (Nat.find h))) else none := rfl

open Classical in
theorem pgCore_some {K' : Set (EuclideanSpace ℝ (Fin d))} {ρ δ : ℝ} {ω : ℕ → PgRound d}
    (h : ∃ r < pgJr δ, pgRepT K' ρ δ ω r) :
    ∃ r < pgJr δ, pgRepT K' ρ δ ω r ∧ (∀ r' < r, ¬pgRepT K' ρ δ ω r') ∧
      pgCore d K' ρ δ ω = some (pgOut (pgRepD K' ρ ω r)) := by
  rw [pgCore_eq, dif_pos h]
  exact ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2,
    fun r' hr' h' => Nat.find_min h hr' ⟨lt_trans hr' (Nat.find_spec h).1, h'⟩, rfl⟩

open Classical in
theorem pgCore_none {K' : Set (EuclideanSpace ℝ (Fin d))} {ρ δ : ℝ} {ω : ℕ → PgRound d}
    (h : ¬∃ r < pgJr δ, pgRepT K' ρ δ ω r) : pgCore d K' ρ δ ω = none := by
  rw [pgCore_eq, dif_neg h]

/-- The natural variables a stage writes. -/
def pgStageN (n0 : ℕ) : List ℕ := pgTmpN n0 ++ [n0 + 10, n0 + 11, n0 + 12, n0 + 13, n0 + 15, n0 + 17]

/-- The scalars a stage writes (besides `ok`). -/
def pgStageS (s0 : ℕ) : List ℕ :=
  pgTmpS s0 ++ [s0 + 20, s0 + 21, s0 + 22, s0 + 23, s0 + 24, s0 + 25, s0 + 26, s0 + 27, s0 + 28, s0 + 29, s0 + 30,
    s0 + 31, s0 + 32, s0 + 33, s0 + 34, s0 + 35, s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 41, s0 + 44,
    s0 + 45, s0 + 46, s0 + 47, s0 + 49, s0 + 50, s0 + 51]

/-- The arrays a repeat writes. -/
def pgRepA (a0 : ℕ) : List ℕ :=
  [a0, a0 + 1, a0 + 2, a0 + 3, a0 + 4, a0 + 5, a0 + 6, a0 + 7, a0 + 8, a0 + 9, a0 + 10, a0 + 11, a0 + 12, a0 + 13,
    a0 + 14, a0 + 15, a0 + 16, a0 + 17, a0 + 18, a0 + 19, a0 + 20]

/-- The arrays a stage writes (besides `μ` and `A`). -/
def pgStageA (a0 : ℕ) : List ℕ := pgRepA a0 ++ [a0 + 21, a0 + 22]

theorem pgStageN_compC (n0 : ℕ) : ∀ i ∈ [n0, n0 + 1, n0 + 2, n0 + 3, n0 + 4, n0 + 5, n0 + 6], i ∈ pgStageN n0 := by
  simp [pgStageN, pgTmpN]

theorem pgStageS_compC (s0 : ℕ) : ∀ x ∈ [s0 + 2, s0 + 8, s0 + 9, s0 + 11], x ∈ pgStageS s0 := by
  simp [pgStageS, pgTmpS]

theorem pgStageS_not_mem {x s0 : ℕ} (h : x < s0 ∨ s0 + 64 ≤ x) : x ∉ pgStageS s0 := by
  simp [pgStageS, pgTmpS]; omega

theorem kCompC_ge (d : ℕ) : 1 + 2 ≤ kCompC d + 1 := by unfold kCompC; omega

/-- The composition `μ := μ + A μ'`, `A := A T'` puts `μ`, `A` at the composed position. -/
theorem PgAt.comp {σ σ' : Env d} {muv Av a b : ℕ} {P X : PgSp d} (hP : PgAt σ muv Av P) (hX : PgAt σ a b X)
    (hv : σ'.vec muv = σ.vec muv + σ.mat Av *ᵥ σ.vec a) (hm : σ'.mat Av = σ.mat Av * σ.mat b) :
    PgAt σ' muv Av (pgComp P (pgOut X)) := by
  refine ⟨?_, ?_⟩
  · rw [hv, hP.1, hP.2, hX.1]
    funext i
    simp [pgComp, pgOut, pgMu_pgPack, pgOp_apply]
  · rw [hm, hP.2, hX.2]
    simp [pgComp, pgOut, pgMat_pgPack, pgA]

set_option maxHeartbeats 1000000 in
theorem runs_pgStageC (hL : PgLeaves) {L : Layout} {w : World d} {dv one okv muv Av n0 s0 a0 : ℕ} {ρ δ : ℝ}
    {P : PgSp d} (σ : Env d) (hn0 : n0 + 20 ≤ L.NN) (hs0 : s0 + 64 ≤ L.NS) (ha0 : a0 + 32 ≤ L.NA)
    (hdv : dv < L.NN) (hone : one < L.NN) (hdvb : dv < n0 ∨ n0 + 20 ≤ dv) (honeb : one < n0 ∨ n0 + 20 ≤ one)
    (hd : σ.nat dv = d) (h1 : σ.nat one = 1) (hmuv : muv < L.NA) (hAv : Av < L.NA)
    (hmub : muv < a0 ∨ a0 + 32 ≤ muv) (hAb : Av < a0 ∨ a0 + 32 ≤ Av) (hmuA : muv ≠ Av) (hokv : okv < L.NS)
    (hokb : okv < s0 ∨ s0 + 64 ≤ okv) (hd1 : 1 ≤ d) (hρ1 : 1 ≤ ρ) (hρ : σ.sc (s0 + 19) = ρ)
    (hdR : σ.sc (s0 + 48) = d) (hdd : σ.nat (n0 + 9) = d * d) (hJ : σ.nat (n0 + 16) = pgJr δ)
    (hmT : σ.nat (n0 + 14) = pgMT δ) (hP : PgAt σ muv Av P) :
    Runs L w (pgStageC L dv one okv muv Av n0 s0 a0) σ
      (kStage d (pgJb d ρ) (pgNs d ρ) (pgNT d ρ) (pgJr δ) (pgMT δ))
      (fun σ' => (∀ X, pgCore d (pgKi w.K (σ.sc (s0 + 42)) P) ρ δ (pgOmegaAt w ρ δ σ.draws) = some X →
          σ'.sc okv = σ.sc okv ∧ PgAt σ' muv Av (pgComp P X)) ∧
        (pgCore d (pgKi w.K (σ.sc (s0 + 42)) P) ρ δ (pgOmegaAt w ρ δ σ.draws) = none →
          σ'.sc okv = 0 ∧ PgAt σ' muv Av P) ∧
        σ'.draws = σ.draws + pgJr δ * (pgW d ρ δ * d) ∧
        Env.Frame σ { σ' with draws := σ.draws } (pgStageN n0) (okv :: pgStageS s0) (muv :: Av :: pgStageA a0)) := by
  have hS0 : s0 < L.NS := by omega
  have hS41 : s0 + 41 < L.NS := by omega
  have nO : one ∉ pgTmpN n0 ++ [n0 + 13, n0 + 15] := by simp [pgTmpN] <;> omega
  have nD : dv ∉ pgTmpN n0 ++ [n0 + 13, n0 + 15, n0 + 17] := by simp [pgTmpN] <;> omega
  have nM : muv ∉ (pgRepA a0) := by
    simp [pgRepA] <;> omega
  have nA : Av ∉ (pgRepA a0) := by
    simp [pgRepA] <;> omega
  set R := σ.sc (s0 + 42) with hR
  set K' := pgKi w.K R P with hK'
  set ω := pgOmegaAt w ρ δ σ.draws with hω
  unfold pgStageC kStage
  -- the parameters
  refine runs_seq (runs_pgParA σ hn0 hs0 hρ hdR) fun σA hA => ?_
  obtain ⟨hA2, hA20, hA21, hA22, hA23, hA24, hA32, hFA⟩ := hA
  have sA : ∀ x, x ∉ [s0 + 2, s0 + 20, s0 + 21, s0 + 22, s0 + 23, s0 + 24, s0 + 32, s0 + 45, s0 + 46] →
      σA.sc x = σ.sc x := hFA.2.1
  refine runs_seq (runs_pgParB σA hn0 hs0 (by rw [sA _ (by simp)]; exact hdR) hA2 hA20 hA21 hA22 hA24)
    fun σB hB => ?_
  obtain ⟨hB25, hB26, hB27, hB28, hFB⟩ := hB
  have sB : ∀ x, x ∉ [s0 + 25, s0 + 26, s0 + 27, s0 + 28, s0 + 45, s0 + 46, s0 + 47] → σB.sc x = σA.sc x :=
    hFB.2.1
  have hB1 : σB.nat one = 1 := by rw [hFB.1 _ (by simp), hFA.1 _ (by simp)]; exact h1
  refine runs_seq (runs_pgParC1 σB hn0 hs0 hone honeb hB1 (by rw [sB _ (by simp), sA _ (by simp)]; exact hdR)
    (by rw [sB _ (by simp)]; exact hA2) (by rw [sB _ (by simp)]; exact hA20) (by rw [sB _ (by simp)]; exact hA22))
    fun σC hC => ?_
  obtain ⟨hC12, hFC⟩ := hC
  have sC : ∀ x, x ∉ [s0 + 45, s0 + 46, s0 + 47, s0 + 50] → σC.sc x = σB.sc x := hFC.2.1
  have hC1 : σC.nat one = 1 := by rw [hFC.1 _ (by simp <;> omega)]; exact hB1
  refine runs_seq (runs_pgParC2 σC hn0 hs0 hone honeb hC1
    (by rw [sC _ (by simp), sB _ (by simp), sA _ (by simp)]; exact hρ)
    (by rw [sC _ (by simp), sB _ (by simp)]; exact hA24) (by rw [sC _ (by simp)]; exact hB25)
    (by rw [sC _ (by simp)]; exact hB26) (by rw [sC _ (by simp)]; exact hB27)) fun σD hD => ?_
  obtain ⟨hD11, hD10, hD29, hD30, hFD⟩ := hD
  have sD : ∀ x, x ∉ [s0, s0 + 29, s0 + 30, s0 + 45, s0 + 46] → σD.sc x = σC.sc x := hFD.2.1
  have hFP : Env.Frame σ σD [n0 + 10, n0 + 11, n0 + 12] [s0, s0 + 2, s0 + 20, s0 + 21, s0 + 22, s0 + 23, s0 + 24,
      s0 + 25, s0 + 26, s0 + 27, s0 + 28, s0 + 29, s0 + 30, s0 + 32, s0 + 45, s0 + 46, s0 + 47, s0 + 50] [] :=
    Env.Frame.trans (Env.Frame.mono hFA (by simp) (by simp) (by simp))
      (Env.Frame.trans (Env.Frame.mono hFB (by simp) (by simp) (by simp))
        (Env.Frame.trans (Env.Frame.mono hFC (by simp) (by simp) (by simp))
          (Env.Frame.mono hFD (by simp) (by simp) (by simp))))
  have hVD : PgStageVars σD n0 s0 ρ :=
    ⟨by rw [hFP.1 _ (by simp)]; exact hdd, hD10, hD11, by rw [hFD.1 _ (by simp)]; exact hC12,
      by rw [hFP.2.1 _ (by simp)]; exact hρ, by rw [sD _ (by simp), sC _ (by simp), sB _ (by simp)]; exact hA21,
      by rw [sD _ (by simp), sC _ (by simp), sB _ (by simp)]; exact hA22,
      by rw [sD _ (by simp), sC _ (by simp), sB _ (by simp)]; exact hA23,
      by rw [sD _ (by simp), sC _ (by simp)]; exact hB28, hD30,
      by rw [sD _ (by simp), sC _ (by simp), sB _ (by simp)]; exact hA32, by rw [hFP.2.1 _ (by simp)]; exact hdR⟩
  have hdD : σD.nat dv = d := by rw [hFP.1 _ (by simp <;> omega)]; exact hd
  have h1D : σD.nat one = 1 := by rw [hFP.1 _ (by simp <;> omega)]; exact h1
  have hJD : σD.nat (n0 + 16) = pgJr δ := by rw [hFP.1 _ (by simp)]; exact hJ
  have hmTD : σD.nat (n0 + 14) = pgMT δ := by rw [hFP.1 _ (by simp)]; exact hmT
  have hRD : σD.sc (s0 + 42) = R := hFP.2.1 _ (by simp)
  have hPD : PgAt σD muv Av P := hP.of_frame hFP (by simp) (by simp)
  -- `found := 0`, then the repeats
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := σD) (x := s0 + 41) (by omega) 0) ?_
  set σE := σD.setSc (s0 + 41) ((0 : ℚ) : ℝ) with hσE
  have hFE : Env.Frame σD σE [n0 + 17] [s0 + 41] [] := Env.Frame.setSc (Env.Frame.refl σD _ _ _) (by simp) _
  refine runs_seq (runs_forN (L := L) (w := w) (i := n0 + 17) (n := n0 + 16) (one := one)
      (body := pgRep L dv one n0 s0 a0 muv Av) (by omega) (by omega) hone (by omega) (by omega) (pgJr δ)
      (kRep d (pgJb d ρ) (pgNs d ρ) (pgNT d ρ) (pgMT δ))
      (fun t σ' => PgStageVars σ' n0 s0 ρ ∧ PgAt σ' muv Av P ∧ σ'.sc (s0 + 42) = R ∧ σ'.nat dv = d ∧
        σ'.nat (n0 + 14) = pgMT δ ∧ σ'.draws = σ.draws + t * (pgW d ρ δ * d) ∧
        ((∃ r < t, pgRepT K' ρ δ ω r) → σ'.sc (s0 + 41) = 1) ∧
        ((¬∃ r < t, pgRepT K' ρ δ ω r) → σ'.sc (s0 + 41) = 0) ∧
        (∀ r < t, pgRepT K' ρ δ ω r → (∀ r' < r, ¬pgRepT K' ρ δ ω r') →
          PgAt σ' (a0 + 19) (a0 + 20) (pgRepD K' ρ ω r)) ∧
        Env.Frame σE { σ' with draws := σE.draws } (pgTmpN n0 ++ [n0 + 13, n0 + 15, n0 + 17])
          (pgTmpS s0 ++ [s0 + 31, s0 + 33, s0 + 34, s0 + 35, s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 41,
            s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 49, s0 + 51])
          (pgRepA a0))
      σE (by rw [hσE, Env.setSc_nat]; exact hJD) (by rw [hσE, Env.setSc_nat]; exact h1D) ?_ ?_) fun σL hL' => ?_
  · -- the invariant at the start
    have F0 : Env.Frame σD (σE.setNat (n0 + 17) 0) [n0 + 17] [s0 + 41] [] := Env.Frame.setNat hFE (by simp) 0
    refine ⟨hVD.of_frame F0 (by simp) (by simp), hPD.of_frame F0 (by simp) (by simp),
      (F0.2.1 _ (by simp)).trans hRD, (F0.1 _ (by simp <;> omega)).trans hdD, (F0.1 _ (by simp)).trans hmTD,
      by rw [F0.2.2.2.1, hFP.2.2.2.1]; simp, fun ⟨_, hr, _⟩ => absurd hr (Nat.not_lt_zero _),
      fun _ => by simp [hσE], fun r hr => absurd hr (Nat.not_lt_zero _),
      frameD_of_frame (Env.Frame.setNat (Env.Frame.refl σE _ _ _) (by simp) 0)⟩
  · -- one repeat
    intro t ht σ' hJt hit hnt hot
    obtain ⟨hV', hP', hR', hd', hmT', hdr', hf1, hf0, hkept, hF'⟩ := hJt
    have hf : σ'.sc (s0 + 41) = 0 ∨ σ'.sc (s0 + 41) = 1 := by
      by_cases hex : ∃ r < t, pgRepT K' ρ δ ω r
      · exact Or.inr (hf1 hex)
      · exact Or.inl (hf0 hex)
    refine runs_mono (runs_pgRep hL σ' hn0 hs0 ha0 hdv hone hdvb honeb hd' hot hmuv hAv hmub hAb hd1 hρ1 hV' hP'
      hmT' hf) le_rfl ?_
    rintro σ'' ⟨hfound, hkeep, hdr'', hF''⟩
    rw [hR', hdr'] at hfound hkeep
    have hFn : Env.Frame σ' { σ''.setNat (n0 + 17) (t + 1) with draws := σ'.draws }
        (pgTmpN n0 ++ [n0 + 13, n0 + 15, n0 + 17])
        (pgTmpS s0 ++ [s0 + 31, s0 + 33, s0 + 34, s0 + 35, s0 + 36, s0 + 37, s0 + 38, s0 + 39, s0 + 40, s0 + 41,
          s0 + 44, s0 + 45, s0 + 46, s0 + 47, s0 + 49, s0 + 51])
        (pgRepA a0) :=
      Env.Frame.setNat (Env.Frame.mono hF'' (by simp [pgTmpN]) (by simp) (fun _ h => h)) (by simp) (t + 1)
    refine ⟨(hF''.1 (n0 + 17) (by simp [pgTmpN])).trans hit, (hF''.1 (n0 + 16) (by simp [pgTmpN])).trans hnt,
      (hF''.1 one nO).trans hot, ?_⟩
    have hs41 : (σ''.setNat (n0 + 17) (t + 1)).sc (s0 + 41) = σ''.sc (s0 + 41) := rfl
    have hV1 := hV'.of_frame hFn (by simp [pgTmpN]) (by simp [pgTmpS])
    have hP1 := hP'.of_frame hFn nM nA
    refine ⟨hV1, hP1, (hFn.2.1 (s0 + 42) (by simp [pgTmpS])).trans hR',
      (hFn.1 dv nD).trans hd', (hFn.1 (n0 + 14) (by simp [pgTmpN])).trans hmT', ?_, ?_, ?_,
      ?_, frameD_trans hF' hFn⟩
    · show σ''.draws = _
      rw [hdr'', hdr', pgW]; ring
    · intro hex
      rw [hs41]
      by_cases hc : σ'.sc (s0 + 41) = 0 ∧ pgRepT K' ρ δ ω t
      · exact (hfound hc.1 hc.2).1
      · rw [(hkeep hc).1]
        by_cases hex' : ∃ r < t, pgRepT K' ρ δ ω r
        · exact hf1 hex'
        · obtain ⟨r, hr, hTr⟩ := hex
          have hrt : r = t := by
            by_contra hne; exact hex' ⟨r, by omega, hTr⟩
          subst hrt
          exact absurd ⟨hf0 hex', hTr⟩ hc
    · intro hne
      have hex' : ¬∃ r < t, pgRepT K' ρ δ ω r := fun ⟨r, hr, h⟩ => hne ⟨r, by omega, h⟩
      rw [hs41]
      by_cases hc : σ'.sc (s0 + 41) = 0 ∧ pgRepT K' ρ δ ω t
      · exact absurd ⟨t, by omega, hc.2⟩ hne
      · rw [(hkeep hc).1]; exact hf0 hex'
    · intro r hr hTr hmin
      by_cases hc : σ'.sc (s0 + 41) = 0 ∧ pgRepT K' ρ δ ω t
      · have hrt : r = t := by
          by_contra hne
          have h1' := hf1 ⟨r, by omega, hTr⟩
          rw [hc.1] at h1'; norm_num at h1'
        subst hrt
        exact (hfound hc.1 hc.2).2
      · obtain ⟨-, h19, h20⟩ := hkeep hc
        by_cases hrt : r < t
        · have hk := hkept r hrt hTr hmin
          exact ⟨(Env.vec_of_arr (σ' := σ''.setNat (n0 + 17) (t + 1)) h19).trans hk.1,
            (Env.mat_of_arr (σ' := σ''.setNat (n0 + 17) (t + 1)) h20).trans hk.2⟩
        · have hrt' : r = t := by omega
          subst hrt'
          exact absurd ⟨hf0 fun ⟨r', hr', h⟩ => hmin r' hr' h, hTr⟩ hc
  -- after the repeats
  obtain ⟨⟨hVL, hPL, hRL, hdL, hmTL, hdrL, hf1L, hf0L, hkL, hFL⟩, -, -, h1L⟩ := hL'
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := σL) (x := s0) (by omega) 0) ?_
  have hFM : Env.Frame σL (σL.setSc s0 ((0 : ℚ) : ℝ)) [] [s0] [] := Env.Frame.setSc (Env.Frame.refl σL _ _ _) (by simp) _
  have hFLs : Env.Frame σ { σL with draws := σ.draws } (pgStageN n0) (pgStageS s0) (pgStageA a0) := by
    have h0 : Env.Frame σ σE (pgStageN n0) (pgStageS s0) (pgStageA a0) :=
      Env.Frame.trans (Env.Frame.mono hFP (by simp [pgStageN]) (by simp [pgStageS, pgTmpS]) (by simp))
        (Env.Frame.mono hFE (by simp [pgStageN]) (by simp [pgStageS]) (by simp))
    exact frameD_trans (frameD_of_frame h0)
      (Env.Frame.mono hFL (by simp [pgStageN, pgTmpN]) (by simp [pgStageS, pgTmpS]) (fun _ h => List.mem_append_left _ h))
  have hPM : PgAt (σL.setSc s0 ((0 : ℚ) : ℝ)) muv Av P := hPL.of_frame hFM (by simp) (by simp)
  by_cases hex : ∃ r < pgJr δ, pgRepT K' ρ δ ω r
  · have hlt : (σL.setSc s0 ((0 : ℚ) : ℝ)).sc s0 < (σL.setSc s0 ((0 : ℚ) : ℝ)).sc (s0 + 41) := by
      simp [hf1L hex]
    refine runs_ifS_t hS0 hS41 hlt (runs_mono (runs_pgCompC hL _ hn0 hs0 ha0 hdv hone hdvb honeb
      (by simp [hdL]) (by simp [h1L]) hmuv hAv hmub hAb hmuA (by simp [hVL.1])) le_rfl ?_)
    rintro σ' ⟨hv', hm', hF'⟩
    have hF1 : Env.Frame σL σ' (pgStageN n0) (pgStageS s0) (muv :: Av :: pgStageA a0) :=
      Env.Frame.trans (Env.Frame.mono hFM (by simp) (by simp [pgStageS, pgTmpS]) (by simp))
        (Env.Frame.mono hF' (pgStageN_compC n0) (pgStageS_compC s0) (by simp [pgStageA]))
    have hFs : Env.Frame σ { σ' with draws := σ.draws } (pgStageN n0) (pgStageS s0) (muv :: Av :: pgStageA a0) :=
      frameD_trans (Env.Frame.mono hFLs (fun _ h => h) (fun _ h => h)
        (fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))) (frameD_of_frame hF1)
    have hokv' : σ'.sc okv = σ.sc okv := hFs.2.1 okv (pgStageS_not_mem hokb)
    have hdr' : σ'.draws = σL.draws := hF'.2.2.2.1
    refine ⟨fun X hX => ?_, fun hX => ?_, by rw [hdr', hdrL], Env.Frame.mono hFs (fun _ h => h)
      (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h)⟩
    · obtain ⟨r, hrJ, hTr, hmin, hcr⟩ := pgCore_some hex
      rw [hcr, Option.some_inj] at hX
      subst hX
      exact ⟨hokv', PgAt.comp hPM ((hkL r hrJ hTr hmin).of_frame hFM (by simp) (by simp)) hv' hm'⟩
    · obtain ⟨r, -, -, -, hcr⟩ := pgCore_some hex
      rw [hcr] at hX; exact absurd hX (Option.some_ne_none _)
  · have hnlt : ¬(σL.setSc s0 ((0 : ℚ) : ℝ)).sc s0 < (σL.setSc s0 ((0 : ℚ) : ℝ)).sc (s0 + 41) := by
      simp [hf0L hex]
    refine runs_mono (runs_ifS_f hS0 hS41 hnlt (runs_sconst (L := L) (w := w) hokv 0))
      (kCompC_ge d) ?_
    rintro σ' rfl
    have hFo : Env.Frame σL ((σL.setSc s0 ((0 : ℚ) : ℝ)).setSc okv ((0 : ℚ) : ℝ)) [] [s0, okv] [] :=
      Env.Frame.setSc (Env.Frame.mono hFM (by simp) (by simp) (by simp)) (by simp) _
    refine ⟨fun X hX => ?_, fun _ => ⟨by simp, hPL.of_frame hFo (by simp) (by simp)⟩, ?_,
      frameD_trans (Env.Frame.mono hFLs (fun _ h => h) (fun _ h => List.mem_cons_of_mem _ h)
        (fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))
        (frameD_of_frame (Env.Frame.mono hFo (by simp) (by simp [pgStageS, pgTmpS]) (by simp)))⟩
    · rw [pgCore_none hex] at hX; exact absurd hX.symm (Option.some_ne_none _)
    · show σL.draws = _; exact hdrL

end AdversarialBco.Poly.PG
