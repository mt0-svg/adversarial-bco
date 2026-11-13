/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XEllOut

@[expose] public section

/-!
# ELL-R and BIS-R on the machine: the projection routine

The two branches after the constants up to `λ` (`XV.ellJ`): ELL-R for `d ≥ 2` (`XV.ellBr`) and BIS-R for `d = 1`
(`XV.bisBr`), each from its constants through its loop to the output.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## Arithmetic -/

/-- The register needs from `1000 W^3 < A`, `W = d + m + s + 1`. -/
theorem ell_regs {d m s lam A : ℕ} (hlam : lam ≤ 7 * s + d + 3) (h : 1000 * (d + m + s + 1) ^ 3 < A) :
    2 * d * (d + 1) * lam + 1 < A ∧ 1000 * (d + m + s + 1) < A ∧ d * d + d < A ∧
      (d * (d + 1) + d * (d + 1)) * lam + 1 < A ∧ d * (d + 1) + d * (d + 1) < A := by
  have hW : 1 ≤ d + m + s + 1 := by omega
  have h2 : (d + m + s + 1) ^ 2 ≤ (d + m + s + 1) ^ 3 := Nat.pow_le_pow_right hW (by norm_num)
  have h1 : d + m + s + 1 ≤ (d + m + s + 1) ^ 2 := by
    calc d + m + s + 1 = (d + m + s + 1) ^ 1 := (pow_one _).symm
      _ ≤ (d + m + s + 1) ^ 2 := Nat.pow_le_pow_right hW (by norm_num)
  have hdd : d * (d + 1) ≤ (d + m + s + 1) ^ 2 := by nlinarith
  have hdd' : d * d + d ≤ (d + m + s + 1) ^ 2 := by nlinarith
  have hl : lam ≤ 7 * (d + m + s + 1) := by omega
  have hN : 2 * d * (d + 1) * lam ≤ 14 * (d + m + s + 1) ^ 3 := by
    calc 2 * d * (d + 1) * lam = 2 * (d * (d + 1)) * lam := by ring
      _ ≤ 2 * (d + m + s + 1) ^ 2 * (7 * (d + m + s + 1)) := by gcongr
      _ = 14 * (d + m + s + 1) ^ 3 := by ring
  have hN' : (d * (d + 1) + d * (d + 1)) * lam = 2 * d * (d + 1) * lam := by ring
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem abs_le_of_le {x : ℤ} {a E : ℕ} (h0 : 0 ≤ x) (h : x ≤ 2 ^ a) (ha : a ≤ E) : |x| ≤ 2 ^ E := by
  rw [abs_of_nonneg h0]; exact h.trans (pow_le_pow_right₀ (by norm_num) ha)

/-- The products of ELL-R's constants below powers of `2`, from `R̄ ≤ 2^s`. -/
theorem ell_pows {s lam p : ℕ} {Rb : ℤ} (hR0 : 0 ≤ Rb) (hR : Rb ≤ 2 ^ s) :
    Rb * Rb ≤ 2 ^ (2 * s) ∧ Rb * Rb * 2 ^ (6 * lam + 2) ≤ 2 ^ (2 * s + (6 * lam + 2)) ∧
      Rb * 2 ^ (3 * lam + 1) ≤ 2 ^ (s + (3 * lam + 1)) ∧
      Rb + Rb * 2 ^ (3 * lam + 1) ≤ 2 ^ (s + (3 * lam + 1) + 1) ∧
      (2 : ℤ) ^ p * (Rb * Rb) ≤ 2 ^ (p + 2 * s) ∧
      (2 : ℤ) ^ p * (Rb * Rb * 2 ^ (6 * lam + 2)) ≤ 2 ^ (p + (2 * s + (6 * lam + 2))) ∧
      (2 : ℤ) ^ p * (Rb + Rb * 2 ^ (3 * lam + 1)) ≤ 2 ^ (p + (s + (3 * lam + 1) + 1)) := by
  have hRR : Rb * Rb ≤ 2 ^ (2 * s) := by rw [two_mul, pow_add]; exact mul_le_mul hR hR hR0 (by positivity)
  have hL : Rb * Rb * 2 ^ (6 * lam + 2) ≤ 2 ^ (2 * s + (6 * lam + 2)) := by
    rw [pow_add (2 : ℤ) (2 * s) (6 * lam + 2)]; exact mul_le_mul_of_nonneg_right hRR (by positivity)
  have hLH : Rb * 2 ^ (3 * lam + 1) ≤ 2 ^ (s + (3 * lam + 1)) := by
    rw [pow_add (2 : ℤ) s (3 * lam + 1)]; exact mul_le_mul_of_nonneg_right hR (by positivity)
  have hRL : Rb + Rb * 2 ^ (3 * lam + 1) ≤ 2 ^ (s + (3 * lam + 1) + 1) := by
    have : Rb ≤ 2 ^ (s + (3 * lam + 1)) := hR.trans (pow_le_pow_right₀ (by norm_num) (by omega))
    rw [pow_succ (2 : ℤ) (s + (3 * lam + 1))]; linarith
  refine ⟨hRR, hL, hLH, hRL, ?_, ?_, ?_⟩
  · rw [pow_add (2 : ℤ) p (2 * s)]; exact mul_le_mul_of_nonneg_left hRR (by positivity)
  · rw [pow_add (2 : ℤ) p (2 * s + (6 * lam + 2))]; exact mul_le_mul_of_nonneg_left hL (by positivity)
  · rw [pow_add (2 : ℤ) p (s + (3 * lam + 1) + 1)]; exact mul_le_mul_of_nonneg_left hRL (by positivity)

/-- The inputs survive a change above the bases. -/
theorem EllIn.frame {B : EllBlk} {I : EllI d} {L : Layout} {nS nN nA : ℕ} {S N : ℕ → Prop}
    {Ar : ℕ → ℕ → Prop} {σ σ' : Env d} (hB : B.OK L nS nN nA) (h : EllIn B I σ) (hF : FrameA S N Ar σ σ')
    (hS : ∀ y, S y → B.o ≤ y) (hN : ∀ j, N j → B.rE ≤ j) (hA : ∀ b k, Ar b k → B.aW ≤ b) : EllIn B I σ' := by
  obtain ⟨-, -, -, hrd, hrm, hsl, hsDf, hsRn, hsRd, hsrn, hsrd, hsen, hsed, haH, hag, haP, haf⟩ := hB
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14⟩ := h
  have nS : ∀ y, y < B.o → σ'.sc y = σ.sc y := fun y hy => hF.2.1 y (fun h => by have := hS y h; omega)
  have nN : ∀ j, j < B.rE → σ'.nat j = σ.nat j := fun j hj => hF.1 j (fun h => by have := hN j h; omega)
  have nA : ∀ b k, b < B.aW → σ'.arr b k = σ.arr b k := fun b k hb =>
    hF.2.2.1 b k (fun h => by have := hA b k h; omega)
  exact ⟨by rw [nN _ hrd, e1], by rw [nN _ hrm, e2], by rw [nS _ hsl, e3], by rw [nS _ hsDf, e4],
    by rw [nS _ hsRn, e5], by rw [nS _ hsRd, e6], by rw [nS _ hsrn, e7], by rw [nS _ hsrd, e8],
    by rw [nS _ hsen, e9], by rw [nS _ hsed, e10], fun i j => by rw [nA _ _ haH, e11 i j],
    fun j => by rw [nA _ _ hag, e12 j], fun i j => by rw [nA _ _ haP, e13 i j], fun j => by rw [nA _ _ haf, e14 j]⟩

/-! ## ELL-R -/

/-- The exponent bound of ELL-R's matrix, `70 s + 30 d + 80`. -/
def ellE (d s : ℕ) : ℕ := 70 * s + 30 * d + 80

/-- The exponent bound of ELL-R's point, `40 s + 20 d + 60`. -/
def ellF (d s : ℕ) : ℕ := 40 * s + 20 * d + 60

/-- The units of the ELL-R branch. -/
def ellBrU (d m s Kr : ℕ) : ℕ :=
  (24 * d + 16) + (30 + ((32 * (12 * s + 5 * d + 12) + 12 * (34 * s + 6 * d + 24) + 36 * (7 * s + d + 3) + 111) +
    ((7 * (d * d) + 14 * d + 13) + (((2 * d * (d + 1) * (7 * s + d + 3) + 1) * (ellKb d m Kr (ellE d s) + 2) + 4) +
      (8 * d + 8)))))

/-- The ELL-R branch: `d`, the registers, the slots, the start state, the loop and the output. -/
def xellBr (L : Layout) (B : EllBlk) (rowc : XCmd) (P u c a0 n0 : ℕ) : XCmd :=
  .seq (xellS0 L B u c n0)
  (.seq (xellSetR B n0)
  (.seq (xellSlots L B P u c n0)
  (.seq (xellArr L B P u c a0 n0)
  (.seq (xellLoop L B rowc P u a0 (a0 + 6) n0)
    (xellOut L B P u a0 n0)))))

theorem ellN_le {I : EllI d} (h : I.lam ≤ 7 * ellSz I + d + 3) :
    I.N ≤ 2 * d * (d + 1) * (7 * ellSz I + d + 3) + 1 := by
  unfold EllI.N; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ h) 1

set_option maxHeartbeats 16000000 in
/-- **The ELL-R branch on the machine** (`d ≥ 2`), from the constants up to `λ` (`XV.ellJ`): the result `ellR I`
over `2^p`. -/
theorem XV.ellBr {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk} {I : EllI d}
    {nS nN nA P u c a0 n0 Kr : ℕ} {rowc : XCmd} {Ctx : Env d → Prop} {SR NR AR : ℕ → Prop}
    (hB : B.OK L nS nN nA) (hav : B.Avoid SR NR AR) (hrow : RowProv L X ℓa ℓ I B rowc Ctx SR NR AR Kr)
    (hctx : CtxOK B Ctx SR NR AR) (hP : P = B.o + 3) (hu : u = P + 12) (hc : c = u + 60) (hn : n0 = B.rE + 1)
    (ha : a0 = B.aW + 2) (hS : c + 60 ≤ L.NS) (hNN : n0 + 47 ≤ L.NN) (hNA : a0 + 7 ≤ L.NA)
    (hin : EllIn B I σ) (hC : Ctx σ) (hz : σ.sc u = 0) (h1 : σ.sc (u + 1) = 1) (hone : σ.nat (n0 + 4) = 1)
    (hRb : σ.sc c = ((I.Rb : ℤ) : ℝ)) (hj : σ.nat (n0 + 8) = I.j) (hcR : σ.nat (n0 + 9) = Nat.clog 2 I.Rb)
    (hl : σ.nat (n0 + 10) = I.lam) (hd : 2 ≤ d) (hr : 0 < I.r) (he : 0 < I.e)
    (hℓ : 4500 * (ellSz I + d + 2) ≤ ℓ) (hℓa : 1000 * (d + I.m + ellSz I + 1) ^ 3 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xellBr L B rowc P u c a0 n0) σ (ellBrU d I.m (ellSz I) Kr) (fun σ' =>
      EllOut B (ellR I) I.p σ' ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => B.o ≤ y ∨ SR y) (fun j => B.rE ≤ j ∨ NR j) (fun b _ => B.aW ≤ b ∨ AR b) σ σ') := by
  have hB' := hB
  obtain ⟨hoS, hrN, haA, hrd, hrm, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hB'
  have hrow' := hrow
  obtain ⟨hsr, hnr, har, -⟩ := hrow'
  have hd1 : 1 ≤ d := by omega
  obtain ⟨blam, bp, bq, bcR⟩ := ellLam_le I hd1 hr he
  have bj := ellJ_le I hd1 hr he
  obtain ⟨rN, rW, rdd, rA2, rA2'⟩ := ell_regs (m := I.m) blam hℓa
  have hdd1 : d * (d + 1) = d * d + d := by ring
  have hRb0 : (0 : ℤ) ≤ I.Rb := by positivity
  have hRbs : (I.Rb : ℤ) ≤ 2 ^ ellSz I := by exact_mod_cast (ellRb_lt I).le
  obtain ⟨pRR, pL, pLH, pRL, ppRR, pcA, pca⟩ := ell_pows (lam := I.lam) (p := I.p) hRb0 hRbs
  have ep : I.p = 6 + Nat.clog 2 (d ^ 2 * (d + 1)) + 2 * I.j := rfl
  have eq : I.q = 9 + Nat.clog 2 d + Nat.clog 2 I.Rb + 3 * I.lam + 2 * I.j := rfl
  have eN : I.N = 2 * d * (d + 1) * I.lam + 1 := rfl
  have hin' := hin
  obtain ⟨e_rd, -⟩ := hin'
  refine XV.mono (K := (24 * d + 16) + (30 + ((32 * I.p + 12 * I.q + 36 * I.lam + 111) +
    ((7 * (d * d) + 14 * d + 13) + ((I.N * (ellKb d I.m Kr (ellE d (ellSz I)) + 2) + 4) + (8 * d + 8)))))) ?_
    ?_ (fun _ h => h)
  swap
  · unfold ellBrU
    have := Nat.mul_le_mul_right (ellKb d I.m Kr (ellE d (ellSz I)) + 2) (ellN_le blam)
    omega
  -- `d`, `d²(d + 1)`, their logarithms
  refine XV.seq (XV.ellS0 hL (B := B) (u := u) (c := c) (n0 := n0) (by omega) (by omega) (by omega) (by omega)
    e_rd hz h1 hone (by omega) (by omega)) fun σ1 ⟨d13, c1v, cdv, d1, F1⟩ => ?_
  have n1 : ∀ j, j ≠ n0 + 17 → j ≠ n0 + 18 → σ1.nat j = σ.nat j := fun j h h' => F1.1 j (by omega)
  -- the registers
  refine XV.seq (XV.ellSetR hL (B := B) (n0 := n0) (j := I.j) (cR := Nat.clog 2 I.Rb) (lam := I.lam)
    (c1 := Nat.clog 2 (d ^ 2 * (d + 1))) (cd := Nat.clog 2 d) (by omega) (by omega) hd1
    (by rw [n1 _ (by omega) (by omega), hone]) (by rw [n1 _ (by omega) (by omega), e_rd])
    (by rw [n1 _ (by omega) (by omega), hj]) (by rw [n1 _ (by omega) (by omega), hcR])
    (by rw [n1 _ (by omega) (by omega), hl]) c1v cdv rfl (by omega) rA2 rA2' (by omega))
    fun σ2 ⟨r4, rdv, _, _, r14, r15, r22, r30, r7, r34, r35, r36, r38, r39, r42, r45, d2, F2⟩ => ?_
  have s2 : ∀ y, ¬ (y = c + 12 ∨ y = c + 13 ∨ c + 21 ≤ y) → σ2.sc y = σ.sc y := fun y h => by
    rw [F2.2.1 _ id, F1.2.1 _ h]
  -- the slots
  have hE : ellSz I + 6 * I.lam + 2 + I.p + ellSz I ≤ ellE d (ellSz I) := by unfold ellE; omega
  refine XV.seq (XV.ellSlots hL (B := B) (P := P) (u := u) (c := c) (n0 := n0) (p := I.p) (q := I.q) (j := I.j)
    (lam := I.lam) (E := ellE d (ellSz I)) (Rb := I.Rb) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [s2 _ (by omega), hz]) (by rw [s2 _ (by omega), h1]) (by rw [s2 _ (by omega), hRb])
    (by rw [F2.2.1 _ id, d13]) r4 r14 (by rw [r22, ep]) (by rw [r30, eq]) (by rw [r34, ep]) (by rw [r35, ep])
    (by rw [r36, ep]) (by rw [r38, ep]) (by rw [r39, eq]) r42 r45
    (abs_le_of_le hRb0 hRbs (by omega)) (abs_le_of_le (mul_nonneg hRb0 hRb0) pRR (by omega))
    (abs_le_of_le (by positivity) le_rfl (by omega)) (abs_le_of_le (by positivity) pL (by omega))
    (abs_le_of_le (by positivity) le_rfl (by omega)) (abs_le_of_le (by positivity) le_rfl (by omega))
    (abs_le_of_le (by positivity) pLH (by omega)) (abs_le_of_le (by positivity) pRL (by omega))
    (by omega) (by omega) (by unfold ellE at hE ⊢; omega) (by omega))
    fun σ3 ⟨o3v, t3, t4, t5, t6, hU, c20, z3, o3, d3, F3⟩ => ?_
  have n3 : ∀ j, j ≠ n0 + 46 → σ3.nat j = σ2.nat j := fun j h => F3.1 j h
  -- the start state
  refine XV.seq (XV.ellArr hL (B := B) (P := P) (u := u) (c := c) (a0 := a0) (n0 := n0)
    (E := ellE d (ellSz I)) (D := 2 ^ I.p * (I.Rb * I.Rb)) hd1 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) z3 c20 (abs_le_of_le (by positivity) ppRR (by omega)) (by unfold ellE at hE ⊢; omega)
    (by rw [n3 _ (by omega), r4]) (by rw [n3 _ (by omega), r14]) (by rw [n3 _ (by omega), r15])
    (by rw [n3 _ (by omega), rdv])) fun σ4 ⟨A4, a4, k4, d4, F4⟩ => ?_
  -- the frame so far
  have G4 : FrameA (fun y => B.o ≤ y) (fun j => B.rE ≤ j) (fun b _ => B.aW ≤ b) σ σ4 :=
    (((F1.mono (fun y h => by omega) (fun j h => by omega) (fun _ _ h => h.elim)).trans
      (F2.mono (fun y h => h.elim) (fun j h => by omega) (fun _ _ h => h.elim))).trans
      (F3.mono (fun y h => by omega) (fun j h => by omega) (fun _ _ h => h.elim))).trans
      (F4.mono (fun y h => by omega) (fun j h => by omega) (fun b _ h => by omega))
  have D4 : σ4.draws = σ.draws := by rw [d4, d3, d2, d1]
  have hin4 : EllIn B I σ4 := EllIn.frame hB hin G4 (fun _ h => h) (fun _ h => h) (fun _ _ h => h)
  have hC4 : Ctx σ4 := hctx σ σ4 hC D4 (G4.mono (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ _ h => Or.inl h))
  have s4 : ∀ y, ¬ (y = P + 1 ∨ c + 24 ≤ y) → σ4.sc y = σ3.sc y := fun y h => F4.2.1 y h
  have n4 : ∀ j, j ≠ n0 + 11 → j ≠ n0 + 13 → j ≠ n0 + 46 → σ4.nat j = σ2.nat j := fun j h h' h'' => by
    rw [F4.1 _ (by omega), n3 _ h'']
  -- the loop
  have eA : (2 : ℤ) ^ I.p * (I.Rb * I.Rb * 2 ^ (6 * I.lam + 2)) = 2 ^ I.p * (I.Lam : ℤ) := by
    unfold EllI.Lam; push_cast; ring
  have ea : (2 : ℤ) ^ I.p * (I.Rb + I.Rb * 2 ^ (3 * I.lam + 1)) = 2 ^ I.p * ((I.Rb : ℤ) + (I.LamH : ℤ)) := by
    unfold EllI.LamH; push_cast; ring
  rw [eA, ea] at hU
  have hU4 : UpdEnv u I.p I.q I.j ((2 : ℤ) ^ I.p * I.Lam) ((2 : ℤ) ^ I.p * (I.Rb + I.LamH)) σ4 :=
    hU.frame F4 (fun y h => by omega)
  have hT4 : TestEnv B I I.p P u (n0 + 4) σ4 :=
    ⟨hin4, by rw [s4 _ (by omega), z3], by rw [s4 _ (by omega), o3], by rw [n4 _ (by omega) (by omega) (by omega), r4],
      by rw [s4 _ (by omega), t3], by rw [s4 _ (by omega), t4], by rw [s4 _ (by omega), t5],
      by rw [s4 _ (by omega), t6]⟩
  have bA : ∀ i k, |(((2 : ℤ) ^ I.p * (I.Rb : ℤ) ^ 2) • (1 : Matrix (Fin d) (Fin d) ℤ)) i k| ≤
      (2 : ℤ) ^ I.p * I.Lam := by
    intro i k
    have h0 : (0 : ℤ) ≤ (2 : ℤ) ^ I.p * (I.Rb : ℤ) ^ 2 := by positivity
    have hle : (2 : ℤ) ^ I.p * (I.Rb : ℤ) ^ 2 ≤ (2 : ℤ) ^ I.p * I.Lam := by
      unfold EllI.Lam; push_cast
      exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num)))
        (by positivity)
    rw [Matrix.smul_apply, Matrix.one_apply]
    split_ifs
    · rw [smul_eq_mul, mul_one, abs_of_nonneg h0]; exact hle
    · rw [smul_eq_mul, mul_zero, abs_zero]; exact h0.trans hle
  have eD : (2 : ℤ) ^ I.p * (I.Rb * I.Rb) = 2 ^ I.p * (I.Rb : ℤ) ^ 2 := by ring
  have hS4 : LoopSt P a0 (a0 + 6) ((2 : ℤ) ^ I.p * I.Lam) ((2 : ℤ) ^ I.p * (I.Rb + I.LamH)) (ellF d (ellSz I))
      (⟨((2 : ℤ) ^ I.p * I.Rb ^ 2) • (1 : Matrix (Fin d) (Fin d) ℤ), 0, none⟩ : ESt d) σ4 :=
    ⟨fun i k => (A4 i k).trans (by rw [eD]), a4, k4, bA, fun k => by simp only [Pi.zero_apply, abs_zero]; positivity,
      fun b W h => by cases h⟩
  have bcA : (2 : ℤ) ^ I.p * I.Lam ≤ 2 ^ ellE d (ellSz I) := by
    rw [← eA]; exact pcA.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have bca : (2 : ℤ) ^ I.p * (I.Rb + I.LamH) ≤ 2 ^ ellF d (ellSz I) := by
    rw [← ea]; exact pca.trans (pow_le_pow_right₀ (by norm_num) (by unfold ellF; omega))
  have bkE : 3 * d + 2 ≤ ellE d (ellSz I) := by unfold ellE; omega
  have cA0 : (0 : ℤ) ≤ 2 ^ I.p * (I.Lam : ℤ) := mul_nonneg (pow_nonneg (by norm_num) _) (Nat.cast_nonneg _)
  have ca0 : (0 : ℤ) ≤ 2 ^ I.p * ((I.Rb : ℤ) + (I.LamH : ℤ)) :=
    mul_nonneg (pow_nonneg (by norm_num) _) (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  refine XV.seq (XV.ellLoop hL hB hav hrow hctx (P := P) (u := u) (a0 := a0) (kb := a0 + 6) (n0 := n0)
    (F := ellF d (ellSz I)) (E := ellE d (ellSz I)) (N := I.N)
    ⟨⟨by omega, by omega, by omega, by omega, rfl, by omega, by omega, rfl, rfl, by omega⟩, by omega, by omega⟩
    hT4 hU4 hC4 hS4 (by rw [n4 _ (by omega) (by omega) (by omega), r7, eN]) rN rfl rfl cA0 ca0 bcA bca
    (by unfold ellF; omega) (by unfold ellF; omega) (by unfold ellF; omega)
    (by unfold ellF ellE; omega) (by unfold ellE; omega)
    ((kapN_le hd1).trans (pow_le_pow_right₀ (by norm_num) bkE))
    ((kapD_le hd1).trans (pow_le_pow_right₀ (by norm_num) bkE)) (by omega) (by unfold ellE; omega))
    fun σ5 ⟨o5, d5, F5⟩ => ?_
  -- the output
  have rd5 : σ5.nat B.rd = σ4.nat B.rd := F5.1 _ (by
    rintro (h | h)
    · omega
    · exact hav.1 h)
  have nn5 : σ5.nat (n0 + 4) = σ4.nat (n0 + 4) := F5.1 _ (by
    rintro (h | h)
    · omega
    · have := hnr _ h; omega)
  have ss5 : ∀ y, B.o ≤ y → ¬ (y = P ∨ y = P + 1 ∨ y = P + 2 ∨ y = P + 7 ∨ y = P + 8 ∨ u + 13 ≤ y ∨ y = B.o + 2) →
      σ5.sc y = σ4.sc y := fun y hy h' => F5.2.1 y (by
    rintro (h | h)
    · exact h' h
    · have := hsr _ h; omega)
  refine XV.mono (XV.ellOut hL (B := B) (P := P) (u := u) (a0 := a0) (n0 := n0) (F := ellF d (ellSz I))
    (e := I.p) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [rd5]; exact hin4.1) (by rw [nn5, n4 _ (by omega) (by omega) (by omega), r4])
    (by rw [ss5 _ (by omega) (by omega), s4 _ (by omega), z3])
    (by rw [ss5 _ (by omega) (by omega), s4 _ (by omega), o3])
    (by rw [ss5 _ (by omega) (by omega), s4 _ (by omega), o3v, Int.cast_natCast]) o5 bca (by unfold ellF; omega))
    le_rfl fun σ6 ⟨o6, d6, F6⟩ => ?_
  refine ⟨o6, by rw [d6, d5, D4], ?_⟩
  exact ((G4.mono (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ _ h => Or.inl h)).trans
    (F5.mono (fun y h => h.elim (fun h => Or.inl (by omega)) Or.inr)
      (fun j h => h.elim (fun h => Or.inl (by omega)) Or.inr)
      (fun b _ h => h.elim (fun h => Or.inl (by omega)) Or.inr))).trans
    (F6.mono (fun y h => by left; omega) (fun j h => by left; omega) (fun b _ h => by left; omega))

/-! ## BIS-R -/

/-- The units of the BIS-R branch. -/
def bisBrU (d m s Kr : ℕ) : ℕ :=
  (24 * (7 * s + d + 3) + 57) + (((7 * s + d + 3 + 1) * (bisKb d m Kr + 2) + 4) + (8 * d + 8))

/-- The BIS-R branch: the constants, the loop and the output. -/
def xbisBr (L : Layout) (B : EllBlk) (rowc : XCmd) (P u c a0 n0 : ℕ) : XCmd :=
  .seq (xbisSet L B P u c n0)
  (.seq (xbisLoop L B rowc P u a0 (a0 + 6) n0)
    (xellOut L B P u a0 n0))

set_option maxHeartbeats 16000000 in
/-- **The BIS-R branch on the machine** (`d = 1`), from the constants up to `λ` (`XV.ellJ`): the result `bisR I`
over `2^{λ+1}`. -/
theorem XV.bisBr {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk} {I : EllI d}
    {nS nN nA P u c a0 n0 Kr : ℕ} {rowc : XCmd} {Ctx : Env d → Prop} {SR NR AR : ℕ → Prop}
    (hB : B.OK L nS nN nA) (hav : B.Avoid SR NR AR) (hrow : RowProv L X ℓa ℓ I B rowc Ctx SR NR AR Kr)
    (hctx : CtxOK B Ctx SR NR AR) (hP : P = B.o + 3) (hu : u = P + 12) (hc : c = u + 60) (hn : n0 = B.rE + 1)
    (ha : a0 = B.aW + 2) (hS : c + 60 ≤ L.NS) (hNN : n0 + 47 ≤ L.NN) (hNA : a0 + 7 ≤ L.NA)
    (hin : EllIn B I σ) (hC : Ctx σ) (hz : σ.sc u = 0) (h1 : σ.sc (u + 1) = 1) (hone : σ.nat (n0 + 4) = 1)
    (hRb : σ.sc c = ((I.Rb : ℤ) : ℝ)) (hl : σ.nat (n0 + 10) = I.lam) (hd : d = 1) (hr : 0 < I.r)
    (he : 0 < I.e) (hℓ : 4500 * (ellSz I + d + 2) ≤ ℓ) (hℓa : 1000 * (d + I.m + ellSz I + 1) ^ 3 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xbisBr L B rowc P u c a0 n0) σ (bisBrU d I.m (ellSz I) Kr) (fun σ' =>
      EllOut B (bisR I) (I.lam + 1) σ' ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => B.o ≤ y ∨ SR y) (fun j => B.rE ≤ j ∨ NR j) (fun b _ => B.aW ≤ b ∨ AR b) σ σ') := by
  have hB' := hB
  obtain ⟨hoS, hrN, haA, hrd, hrm, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hB'
  have hrow' := hrow
  obtain ⟨hsr, hnr, har, -⟩ := hrow'
  have hd1 : 1 ≤ d := by omega
  obtain ⟨blam, -, -, bcR⟩ := ellLam_le I hd1 hr he
  obtain ⟨-, rW, -, -, -⟩ := ell_regs (m := I.m) blam hℓa
  have hRb0 : (0 : ℤ) ≤ I.Rb := by positivity
  have hRbs : (I.Rb : ℤ) ≤ 2 ^ ellSz I := by exact_mod_cast (ellRb_lt I).le
  refine XV.mono (K := (24 * I.lam + 57) + (((I.lam + 1) * (bisKb d I.m Kr + 2) + 4) + (8 * d + 8))) ?_ ?_
    (fun _ h => h)
  swap
  · unfold bisBrU
    have := Nat.mul_le_mul_right (bisKb d I.m Kr + 2) (show I.lam + 1 ≤ 7 * ellSz I + d + 3 + 1 by omega)
    omega
  -- the constants
  refine XV.seq (XV.bisSet hL (B := B) (P := P) (u := u) (c := c) (n0 := n0) (lam := I.lam) (E := ellSz I)
    (Rb := I.Rb) (by omega) (by omega) (by omega) (by omega) (by omega) hz hl hone hRb hRb0 hRbs (by omega)
    (by omega)) fun σ1 ⟨n7, o1, t3, t4, t5, t6, u2, lo1, hi1, k1, d1, F1⟩ => ?_
  have G1 : FrameA (fun y => B.o ≤ y) (fun j => B.rE ≤ j) (fun b _ => B.aW ≤ b) σ σ1 :=
    F1.mono (fun y h => by simp only [bisSetS] at h; omega) (fun j h => by omega) (fun _ _ h => h.elim)
  have hin1 : EllIn B I σ1 := EllIn.frame hB hin G1 (fun _ h => h) (fun _ h => h) (fun _ _ h => h)
  have hC1 : Ctx σ1 := hctx σ σ1 hC d1 (G1.mono (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ _ h => Or.inl h))
  have s1 : ∀ y, ¬ bisSetS B P u y → σ1.sc y = σ.sc y := fun y h => F1.2.1 y h
  have hT1 : TestEnv B I (I.lam + 1) P u (n0 + 4) σ1 :=
    ⟨hin1, by rw [s1 _ (by simp only [bisSetS]; omega), hz], by rw [s1 _ (by simp only [bisSetS]; omega), h1],
      by rw [F1.1 _ (by omega), hone], t3, t4, t5, t6⟩
  have hM0 : (0 : ℤ) ≤ I.Rb * 2 ^ (I.lam + 1) := by positivity
  have bM : (I.Rb : ℤ) * 2 ^ (I.lam + 1) ≤ 2 ^ ellF d (ellSz I) := by
    have : (I.Rb : ℤ) * 2 ^ (I.lam + 1) ≤ 2 ^ (ellSz I + (I.lam + 1)) := by
      rw [pow_add (2 : ℤ) (ellSz I) (I.lam + 1)]; exact mul_le_mul_of_nonneg_right hRbs (by positivity)
    exact this.trans (pow_le_pow_right₀ (by norm_num) (by unfold ellF; omega))
  -- the loop
  refine XV.seq (XV.bisLoop hL hB hav hrow hctx (P := P) (u := u) (a0 := a0) (kb := a0 + 6) (n0 := n0)
    (F := ellF d (ellSz I)) (G := ellE d (ellSz I)) (N := I.lam + 1) (M := I.Rb * 2 ^ (I.lam + 1)) (kept0 := none)
    ⟨⟨⟨by omega, by omega, by omega, by omega, rfl, by omega, by omega, rfl, rfl, by omega⟩, by omega, by omega⟩,
      by omega⟩ hd hT1 u2 hC1 lo1 hi1 (by rw [abs_neg, abs_of_nonneg hM0]) (by rw [abs_of_nonneg hM0]) k1
    (fun b W h => by cases h) n7 (by omega) bM (by unfold ellF; omega) (by unfold ellF; omega)
    (by unfold ellF; omega) (by unfold ellF ellE; omega) (by omega) (by unfold ellE; omega))
    fun σ2 ⟨o2, d2, F2⟩ => ?_
  -- the output
  have rd2 : σ2.nat B.rd = σ1.nat B.rd := F2.1 _ (by
    rintro (h | h)
    · omega
    · exact hav.1 h)
  have nn2 : σ2.nat (n0 + 4) = σ1.nat (n0 + 4) := F2.1 _ (by
    rintro (h | h)
    · omega
    · have := hnr _ h; omega)
  have ss2 : ∀ y, B.o ≤ y → ¬ ((P ≤ y ∧ y ≤ P + 11 ∧ (y < P + 3 ∨ P + 6 < y)) ∨ u + 13 ≤ y ∨ y = B.o + 2) →
      σ2.sc y = σ1.sc y := fun y hy h' => F2.2.1 y (by
    rintro (h | h)
    · exact h' h
    · have := hsr _ h; omega)
  refine XV.mono (XV.ellOut hL (B := B) (P := P) (u := u) (a0 := a0) (n0 := n0) (F := ellF d (ellSz I))
    (e := I.lam + 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [rd2]; exact hin1.1) (by rw [nn2, F1.1 _ (by omega), hone])
    (by rw [ss2 _ (by omega) (by omega), s1 _ (by simp only [bisSetS]; omega), hz])
    (by rw [ss2 _ (by omega) (by omega), s1 _ (by simp only [bisSetS]; omega), h1])
    (by rw [ss2 _ (by omega) (by omega), o1]) o2 bM (by unfold ellF; omega))
    le_rfl fun σ3 ⟨o3, d3, F3⟩ => ?_
  refine ⟨o3, by rw [d3, d2, d1], ?_⟩
  exact ((G1.mono (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ _ h => Or.inl h)).trans
    (F2.mono (fun y h => h.elim (fun h => Or.inl (by omega)) Or.inr)
      (fun j h => h.elim (fun h => Or.inl (by omega)) Or.inr)
      (fun b _ h => h.elim (fun h => Or.inl (by omega)) Or.inr))).trans
    (F3.mono (fun y h => by left; omega) (fun j h => by left; omega) (fun b _ h => by left; omega))

end AdversarialBco.Bit.Transfer
