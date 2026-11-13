/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriUpdEq
public import AdversarialBco.Bit.Transfer.XTriAux

@[expose] public section

/-!
# TRI-M, the integer model of a stage against the rational one

* `triDrawQ_eq`: a draw of BM-INT as `tzY` over `2^{2 p}`;
* `stage_u_eq`: the update direction of a stage from the integer rows `tzRowA`, `tzRowB` and the stage's `(μ, T)`;
* `tzUpd_step`, `tzIter_eq`, `core_out_eq`: one draw, the iterates and the core output at the grid;
* `tzStage_eq`, `tzPos_eq`: the stages and the position of TRI-M as `tzStage`, `tzPos` over their denominators.
-/

open AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.Transfer AdversarialBco.Bit.TriM Matrix

theorem AdversarialBco.Bit.TriM.triDrawQ_eq (d B : ℕ) (x : ℕ → Bool) (t : ℕ) :
    triDrawQ d B x t = fun i => (tzY d B x t i : ℚ) / 2 ^ (2 * gsm_prec B) := by
  funext i
  simp [triDrawQ, tzY]

theorem AdversarialBco.Bit.TriM.stage_u_eq {d m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (ch : Fin d → ℤ)
    (Dc : ℤ) (hDc : 0 < Dc) (e j : ℕ) (mu : Fin d → ℤ) (T : Matrix (Fin d) (Fin d) ℤ) (z : Fin d → ℚ) :
    triUQ (triStAQ (fun k => A k) (fun i => (mu i : ℚ) / (Dc * 2 ^ e), fun i l => (T i l : ℚ) / (Dc * 2 ^ e)))
        (triStBQ (fun k => A k) b (fun i => (ch i : ℚ) / Dc) (2 ^ j)
          (fun i => (mu i : ℚ) / (Dc * 2 ^ e), fun i l => (T i l : ℚ) / (Dc * 2 ^ e))) z =
      triUQ (fun k : Fin (m + (d + d)) => (T.map (Int.cast : ℤ → ℚ))ᵀ *ᵥ fun i => (onN (tzRowA A b) k i : ℚ))
        (fun k : Fin (m + (d + d)) =>
          ((onN (tzRowB A b ch e j (Dc * 2 ^ e)) k - onN (tzRowA A b) k ⬝ᵥ mu : ℤ) : ℚ)) z := by
  choose sk hsk using fun k => stage_rows_scale A b ch Dc hDc e j mu T k
  have hA : ∀ k : Fin (m + (d + d)), onN (tzRowA A b) (k : ℕ) = tzRowA A b k := fun k => by
    unfold onN; simp [k.2]
  have hB : ∀ k : Fin (m + (d + d)),
      onN (tzRowB A b ch e j (Dc * 2 ^ e)) (k : ℕ) = tzRowB A b ch e j (Dc * 2 ^ e) k := fun k => by
    unfold onN; simp [k.2]
  refine (triUQ_smul_rows _ _ sk (fun k => (hsk k).1) z).symm.trans ?_
  congr 1
  · funext k; rw [hA k]; exact (hsk k).2.1.symm
  · funext k; rw [hB k, hA k]; exact (hsk k).2.2.symm

theorem AdversarialBco.Bit.TriM.tzUpd_step {d : ℕ} (hd : 1 ≤ d) (Bv Js ja p La G : ℕ) (hG : G = Bv + Js + ja)
    (hLa : 10 ≤ La) (X : PosZ d) (hdiag : ∀ i, 0 < X.2 i i) (A Y : Fin d → ℤ) (Bb : ℤ) (hBb : 0 < Bb)
    (x : PosQ d) (hx : x = (fun i => (X.1 i : ℚ) / 2 ^ G, fun i l => (X.2 i l : ℚ) / 2 ^ G))
    (y : Fin d → ℚ) (hy : y = fun i => (Y i : ℚ) / 2 ^ (2 * p))
    (u : (Fin d → ℚ) → Fin d → ℚ) (hu : u (x.1 + x.2 *ᵥ y) = fun i => (A i : ℚ) / Bb)
    (c : DC) (hc : c = ⟨2 ^ Bv, 2 ^ (2 * p), 2 ^ G, 2 ^ ja, 2 ^ (La - 3 + G), 2 ^ (Bv + Js),
      161 * 2 ^ (La - 10 + G), d⟩) :
    triClipQ (2 ^ (La - 3)) (1 / 2 ^ ja) (161 * 2 ^ (La - 10)) (x - (1 / 2 ^ Js : ℚ) • triRoundQ Bv (triVQ u x y)) =
      (fun i => ((tzUpd c X A Y Bb).1 i : ℚ) / 2 ^ G, fun i l => ((tzUpd c X A Y Bb).2 i l : ℚ) / 2 ^ G) := by
  unfold triVQ
  rw [hu]
  subst hx hy hc hG
  refine Prod.ext (funext fun i => ?_) (funext fun i => funext fun l => ?_)
  · have e1 : ∀ (z w : PosQ d) (s : ℚ), (z - s • w).1 i = z.1 i - s * w.1 i := fun _ _ _ => rfl
    simp only [triClipQ]
    refine (congrArg₂ max rfl (congrArg₂ min rfl (e1 _ _ _))).trans ?_
    simp only [triLoQ, triHiQ, triRoundQ, tzUpd, tzRMu]
    exact upd_mu Bv Js ja La hLa (X.1 i) (A i) Bb hBb
  · have e2 : ∀ (z w : PosQ d) (s : ℚ), (z - s • w).2 i l = z.2 i l - s * w.2 i l := fun _ _ _ => rfl
    simp only [triClipQ]
    refine (congrArg₂ max rfl (congrArg₂ min rfl (e2 _ _ _))).trans ?_
    simp only [triLoQ, triHiQ, triRoundQ, tzUpd, tzRLow, tzRDiag]
    rcases lt_trichotomy l i with hl | rfl | hl
    · simp only [hl, hl.le, ne_of_gt hl, ↓reduceIte, sub_zero]
      exact upd_low Bv Js ja La p hLa (X.2 i l) (A i) (Y l) Bb hBb
    · simp only [lt_irrefl, le_refl, ↓reduceIte]
      exact upd_diag d hd Bv Js ja La p hLa (X.2 l l) (A l) (Y l) Bb hBb (hdiag l)
    · have h1 : ¬ l < i := not_lt.mpr hl.le
      have h2 : ¬ l ≤ i := not_le.mpr hl
      have h3 : i ≠ l := ne_of_lt hl
      have h4 : l ≠ i := (ne_of_lt hl).symm
      simp only [h1, h2, h3, h4, ↓reduceIte, Int.cast_zero, zero_div]
      exact max_eq_left (min_le_left _ _)

theorem AdversarialBco.Bit.TriM.tzIter_eq {d m : ℕ} (hd : 1 ≤ d) (Bv Js ja p La G : ℕ) (hG : G = Bv + Js + ja)
    (hLa : 10 ≤ La) (c : DC) (hc : c = ⟨2 ^ Bv, 2 ^ (2 * p), 2 ^ G, 2 ^ ja, 2 ^ (La - 3 + G), 2 ^ (Bv + Js),
      161 * 2 ^ (La - 10 + G), d⟩)
    (T : Matrix (Fin d) (Fin d) ℤ) (mu : Fin d → ℤ) (ra : ℕ → Fin d → ℤ) (rb : ℕ → ℤ)
    (α : Fin m → Fin d → ℚ) (β : Fin m → ℚ)
    (hαβ : ∀ z, triUQ α β z = triUQ (fun k : Fin m => (T.map (Int.cast : ℤ → ℚ))ᵀ *ᵥ fun i => (ra k i : ℚ))
        (fun k : Fin m => ((rb k - ra k ⬝ᵥ mu : ℤ) : ℚ)) z)
    (Y : ℕ → Fin d → ℤ) (y : ℕ → Fin d → ℚ) (hy : ∀ t, y t = fun i => (Y t i : ℚ) / 2 ^ (2 * p)) (t : ℕ) :
    triIterQ (2 ^ (La - 3)) (1 / 2 ^ ja) (161 * 2 ^ (La - 10)) (1 / 2 ^ Js)
        (fun x w => triRoundQ Bv (triVQ (triUQ α β) x w)) y t =
      (fun i => ((tzIter c T mu ra rb m Y t).1 i : ℚ) / 2 ^ G,
       fun i l => ((tzIter c T mu ra rb m Y t).2 i l : ℚ) / 2 ^ G) := by
  set emb := fun (X : PosZ d) => (fun i => (X.1 i : ℚ) / 2 ^ G, fun i l => (X.2 i l : ℚ) / 2 ^ G) with hemb
  have h_main : ∀ t, triIterQ (2 ^ (La - 3)) (1 / 2 ^ ja) (161 * 2 ^ (La - 10)) (1 / 2 ^ Js)
      (fun x w => triRoundQ Bv (triVQ (triUQ α β) x w)) y t = emb (tzIter c T mu ra rb m Y t) ∧
      ∀ i, 0 < (tzIter c T mu ra rb m Y t).2 i i := by
    intro t
    induction' t with t ih
    · refine ⟨?_, ?_⟩
      · dsimp [triIterQ, tzIter, emb]
        have hPG : c.PG = 2 ^ G := by
          rw [hc]
        rw [hPG]
        refine Prod.ext ?_ ?_
        · ext i; simp
        · ext i j; simp [Matrix.one_apply]; split <;> simp
      · intro i
        dsimp [tzIter]
        have hPG : c.PG = 2 ^ G := by
          rw [hc]
        rw [hPG]
        have hpos : 0 < (2 : ℚ) ^ G := pow_pos (by norm_num) G
        simp
    · rcases ih with ⟨ih_eq, ih_pos⟩
      set X := tzIter c T mu ra rb m Y t with hX
      have hXpos : ∀ i, 0 < X.2 i i := ih_pos
      have h_emb_eq : triIterQ (2 ^ (La - 3)) (1 / 2 ^ ja) (161 * 2 ^ (La - 10)) (1 / 2 ^ Js)
          (fun x w => triRoundQ Bv (triVQ (triUQ α β) x w)) y t = emb X := ih_eq
      dsimp [triIterQ]
      rw [h_emb_eq]
      set st := tzKeep T mu ra rb m (tzZ X (Y t) c.P2) with hst
      set A := Tᵀ *ᵥ st.row with hA
      set Bb := st.bb with hBb
      have hBb_pos : 0 < Bb := by
        rw [hBb]
        exact (tzKeep_triU T mu ra rb (tzZ X (Y t) c.P2)).1
      have hP2 : c.P2 = 2 ^ (2 * p) := by
        rw [hc]
      have h_sum_eq : (emb X).1 + (emb X).2 *ᵥ y t =
          ((1 : ℚ) / ((2 : ℚ) ^ (G + 2 * p))) • (fun i => (tzZ X (Y t) c.P2 i : ℚ)) := by
        ext i
        dsimp [emb, tzZ, Matrix.mulVec]
        rw [hy t, hP2]
        push_cast
        simp only [dotProduct]
        set A := (X.1 i : ℚ) with hA
        set B := (∑ j : Fin d, (X.2 i j : ℚ) * (Y t j : ℚ)) with hB
        have h_denom : A / (2 : ℚ) ^ G + B / ((2 : ℚ) ^ G * (2 : ℚ) ^ (2 * p)) =
            ((1 : ℚ) / (2 : ℚ) ^ (G + 2 * p)) * (A * (2 : ℚ) ^ (2 * p) + B) := by
          have h2G : (2 : ℚ) ^ G ≠ 0 := pow_ne_zero _ (by norm_num)
          have h2p : (2 : ℚ) ^ (2 * p) ≠ 0 := pow_ne_zero _ (by norm_num)
          field_simp [h2G, h2p]
          rw [pow_add]
          ring
        simpa [hA, hB, Finset.sum_mul, Finset.mul_sum, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h_denom
      have h_sum_pos : 0 < (1 : ℚ) / ((2 : ℚ) ^ (G + 2 * p)) := by
        refine div_pos (by norm_num) (pow_pos (by norm_num) (G + 2 * p))
      have hu_eq : triUQ α β ((emb X).1 + (emb X).2 *ᵥ y t) = fun i => (A i : ℚ) / Bb := by
        rw [h_sum_eq]
        rw [triUQ_smul_pt α β ((1 : ℚ) / ((2 : ℚ) ^ (G + 2 * p))) h_sum_pos
          (fun i => (tzZ X (Y t) c.P2 i : ℚ))]
        rw [hαβ (fun i => (tzZ X (Y t) c.P2 i : ℚ))]
        have h_keep := tzKeep_triU (M := m) T mu ra rb (tzZ X (Y t) c.P2)
        rcases h_keep with ⟨_, h_eq⟩
        rw [h_eq]
      have h_step := tzUpd_step hd Bv Js ja p La G hG hLa X hXpos A (Y t) Bb hBb_pos (emb X) rfl (y t)
          (hy t) (triUQ α β) hu_eq c hc
      have h_tzIter_succ : tzIter c T mu ra rb m Y (t + 1) = tzUpd c X A (Y t) Bb := by
        dsimp [tzIter, tzStep1, X, A, Bb, st]
      have h_pos_next : ∀ i, 0 < (tzUpd c X A (Y t) Bb).2 i i := by
        intro i
        have hR_val : c.R = 2 ^ (La - 3 + G) := by
          rw [hc]
        have hAl_val : c.Al = 2 ^ (Bv + Js) := by
          rw [hc]
        have hBh_val : c.Bh = 161 * 2 ^ (La - 10 + G) := by
          rw [hc]
        have hR : 0 ≤ c.R := by
          rw [hR_val]
          positivity
        have hRB : c.R ≤ c.Bh := by
          rw [hR_val, hBh_val]
          have h_exp : La - 3 + G = (La - 10 + G) + 7 := by omega
          rw [h_exp, pow_add]
          have hpos' : 0 < (2 : ℤ) ^ (La - 10 + G) := pow_pos (by norm_num) _
          nlinarith
        have hAl : 0 < c.Al := by
          rw [hAl_val]
          positivity
        have hAB : c.Al ≤ c.Bh := by
          rw [hAl_val, hBh_val]
          have hG_le : Bv + Js ≤ G := by omega
          have hG_le' : G ≤ La - 10 + G := by omega
          have h_pow1 : (2 : ℤ) ^ (Bv + Js) ≤ (2 : ℤ) ^ G := by
            have h_nat : (2 : ℕ) ^ (Bv + Js) ≤ (2 : ℕ) ^ G :=
              Nat.pow_le_pow_right (by norm_num) hG_le
            exact_mod_cast h_nat
          have h_pow2 : (2 : ℤ) ^ G ≤ (2 : ℤ) ^ (La - 10 + G) := by
            have h_nat : (2 : ℕ) ^ G ≤ (2 : ℕ) ^ (La - 10 + G) :=
              Nat.pow_le_pow_right (by norm_num) hG_le'
            exact_mod_cast h_nat
          have h_pow3 : (2 : ℤ) ^ (La - 10 + G) ≤ 161 * (2 : ℤ) ^ (La - 10 + G) := by
            nlinarith [pow_pos (by norm_num : 0 < (2 : ℤ)) (La - 10 + G)]
          exact le_trans h_pow1 (le_trans h_pow2 h_pow3)
        have h_bound := tzUpd_bound c X A (Y t) Bb hR hRB hAl hAB
        have h_le : c.Al ≤ (tzUpd c X A (Y t) Bb).2 i i := h_bound.2.2 i
        linarith
      rw [h_tzIter_succ]
      exact ⟨h_step, h_pos_next⟩
  exact (h_main t).1

theorem AdversarialBco.Bit.TriM.core_out_eq {d m : ℕ} (hd : 1 ≤ d) (ℓ : ℕ) (α : Fin m → Fin d → ℚ) (β : Fin m → ℚ)
    (T : Matrix (Fin d) (Fin d) ℤ) (mu : Fin d → ℤ) (ra : ℕ → Fin d → ℤ) (rb : ℕ → ℤ)
    (hαβ : ∀ z, triUQ α β z = triUQ (fun k : Fin m => (T.map (Int.cast : ℤ → ℚ))ᵀ *ᵥ fun i => (ra k i : ℚ))
        (fun k : Fin m => ((rb k - ra k ⬝ᵥ mu : ℤ) : ℚ)) z)
    (x : ℕ → Bool) :
    triCoreOutQ d α β ℓ (fun t => triDrawQ d (triBgQ d) x t) =
      (fun i => ((tzSum (tzDC d ℓ) T mu ra rb m (tzY d (triBgQ d) x) (2 ^ triNeQ d ℓ)).1 i : ℚ) / 2 ^ tzGc d ℓ,
       fun i l => ((tzSum (tzDC d ℓ) T mu ra rb m (tzY d (triBgQ d) x) (2 ^ triNeQ d ℓ)).2 i l : ℚ) /
        2 ^ tzGc d ℓ) := by
  set Bv := triBvQ d with hBv_def
  set Js := triJsQ d ℓ with hJs_def
  set ja := triJaQ d with hja_def
  set p := tzP d with hp_def
  set G := tzG d ℓ with hG_def
  set Ne := triNeQ d ℓ with hNe_def
  have hG_eq : G = Bv + Js + ja := by
    dsimp [G, Bv, Js, ja, tzG, triBvQ, triJsQ, triJaQ]
  have hLa : 10 ≤ triLa (triSQ d) := by
    have h4 : triLa 4 = 11 := by
      unfold triLa; norm_num
    have h4le : 4 ≤ triSQ d := (triSQ_bounds d).1
    have h_sq : 4 ^ 2 ≤ (triSQ d) ^ 2 := Nat.pow_le_pow_left h4le 2
    have h_mul : 5 * 4 ^ 2 ≤ 5 * (triSQ d) ^ 2 := Nat.mul_le_mul_left 5 h_sq
    have h_le : triLa 4 ≤ triLa (triSQ d) := by
      unfold triLa
      exact Nat.div_le_div_right h_mul
    omega
  have hc : tzDC d ℓ = ⟨2 ^ Bv, 2 ^ (2 * p), 2 ^ G, 2 ^ ja, 2 ^ (triLa (triSQ d) - 3 + G), 2 ^ (Bv + Js),
      161 * 2 ^ (triLa (triSQ d) - 10 + G), d⟩ := by
    dsimp [tzDC, Bv, Js, ja, p, G, tzG, triBvQ, triJsQ, triJaQ, tzP, gsm_prec]
  have hy : ∀ t, (fun t => triDrawQ d (triBgQ d) x t) t = fun i => ((tzY d (triBgQ d) x t i : ℚ) / 2 ^ (2 * p)) := by
    intro t
    have h := triDrawQ_eq d (triBgQ d) x t
    simpa [hp_def, tzP] using h
  have h_iter_eq : ∀ t, triIterQ (2 ^ (triLa (triSQ d) - 3)) (1 / 2 ^ ja) (161 * 2 ^ (triLa (triSQ d) - 10))
      (1 / 2 ^ Js)
      (fun x w => triRoundQ Bv (triVQ (triUQ α β) x w)) (fun t => triDrawQ d (triBgQ d) x t) t =
      (fun i => ((tzIter (tzDC d ℓ) T mu ra rb m (tzY d (triBgQ d) x) t).1 i : ℚ) / 2 ^ G,
       fun i l => ((tzIter (tzDC d ℓ) T mu ra rb m (tzY d (triBgQ d) x) t).2 i l : ℚ) / 2 ^ G) := by
    intro t
    apply tzIter_eq hd Bv Js ja p (triLa (triSQ d)) G hG_eq hLa (tzDC d ℓ) hc T mu ra rb α β hαβ
      (tzY d (triBgQ d) x) (fun t => triDrawQ d (triBgQ d) x t) hy t
  rw [triCoreOutQ]
  have h_avg := avg_eq (2 ^ (triLa (triSQ d) - 3)) (1 / 2 ^ ja) (161 * 2 ^ (triLa (triSQ d) - 10)) (1 / 2 ^ Js)
    (fun x w => triRoundQ Bv (triVQ (triUQ α β) x w)) (fun t => triDrawQ d (triBgQ d) x t)
    (tzIter (tzDC d ℓ) T mu ra rb m (tzY d (triBgQ d) x)) G Ne h_iter_eq
  have hGc : tzGc d ℓ = G + Ne := by
    dsimp [tzGc, G, Ne, triNeQ, tzG]
  simpa [Bv, Js, ja, Ne, triRQ, triAQ, triBQ, triJsQ, triBvQ, triJaQ, triNeQ, tzSum, hGc] using h_avg

theorem AdversarialBco.Bit.TriM.tzStage_eq {d m : ℕ} (hd : 1 ≤ d) (n : ℕ) (A : Matrix (Fin m) (Fin d) ℚ)
    (b : Fin m → ℚ) (Dc : ℤ) (hDc : 0 < Dc) (ch : Fin d → ℤ) (ω : ℕ → ℕ → Bool) (j : ℕ) :
    triStageNQ (fun k => A k) b (fun i => (ch i : ℚ) / Dc) (1 / 2) (ellPos d n) ω j =
      (fun i => ((tzStage n A b Dc ch ω j).mu i : ℚ) / (tzStage n A b Dc ch ω j).D,
       fun i l => ((tzStage n A b Dc ch ω j).T i l : ℚ) / (tzStage n A b Dc ch ω j).D) := by
  have hD0 : (Dc : ℚ) ≠ 0 := by exact_mod_cast hDc.ne'
  induction j with
  | zero =>
    refine Prod.ext (funext fun i => ?_) (funext fun i => funext fun l => ?_)
    · simp only [triStageNQ, tzStage]
      push_cast
      field_simp
    · simp only [triStageNQ, tzStage, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> push_cast <;> field_simp
  | succ j ih =>
    set ℓ := ellPos d n with hℓ
    set P := tzStage n A b Dc ch ω j with hP
    set e := 1 + j * tzGc d ℓ with he
    have hD : P.D = Dc * 2 ^ e := tzStage_D n A b Dc ch ω j
    have hPD : 0 < P.D := by rw [hD]; positivity
    have hemb : (fun i => (P.mu i : ℚ) / P.D, fun i l => (P.T i l : ℚ) / P.D) =
        ((fun i => (P.mu i : ℚ) / (Dc * 2 ^ e), fun i l => (P.T i l : ℚ) / (Dc * 2 ^ e)) : PosQ d) := by
      rw [hD]; push_cast; rfl
    have hr : (2 : ℚ) ^ (j + 1) * (1 / 2) = 2 ^ j := by rw [pow_succ]; ring
    have hstep : triStageNQ (fun k => A k) b (fun i => (ch i : ℚ) / Dc) (1 / 2) ℓ ω (j + 1) =
        triStepQ (fun k => A k) b (fun i => (ch i : ℚ) / Dc) (1 / 2) ℓ j
          (triStageNQ (fun k => A k) b (fun i => (ch i : ℚ) / Dc) (1 / 2) ℓ ω j) (ω j) := rfl
    rw [hstep, ih]
    unfold triStepQ
    rw [hr, hemb, core_out_eq hd ℓ _ _ P.T P.mu (onN (tzRowA A b)) (onN (tzRowB A b ch e j (Dc * 2 ^ e)))
      (fun z => stage_u_eq A b ch Dc hDc e j P.mu P.T z) (ω j), ← hemb]
    refine (comp_eq P _ (tzGc d ℓ) hPD).trans ?_
    have hS : tzStage n A b Dc ch ω (j + 1) = tzComp P
        (tzSum (tzDC d ℓ) P.T P.mu (onN (tzRowA A b)) (onN (tzRowB A b ch e j (Dc * 2 ^ e))) (m + (d + d))
          (tzY d (triBgQ d) (ω j)) (2 ^ triNeQ d ℓ)) (tzGc d ℓ) := by
      rw [← hD]; rfl
    exact congrArg (fun Q : StZ d => ((fun i => (Q.mu i : ℚ) / Q.D, fun i l => (Q.T i l : ℚ) / Q.D) : PosQ d))
      hS.symm

theorem AdversarialBco.Bit.TriM.tzPos_eq {d m : ℕ} (hd : 1 ≤ d) (n : ℕ) (A : Matrix (Fin m) (Fin d) ℚ)
    (b : Fin m → ℚ) (Dc : ℤ) (hDc : 0 < Dc) (ch : Fin d → ℤ) (c : Fin d → ℚ) (hc : c = fun i => (ch i : ℚ) / Dc)
    (cs : ℕ → Bool) :
    triPosQ (fun k => A k) b c (1 / 2) n (ellPos d n) cs =
      (fun i => ((tzPos n A b Dc ch cs).mu i : ℚ) / (tzPos n A b Dc ch cs).D,
       fun i l => ((tzPos n A b Dc ch cs).T i l : ℚ) / (tzPos n A b Dc ch cs).D) := by
  subst hc
  unfold triPosQ tzPos
  exact tzStage_eq hd n A b Dc hDc ch _ _
