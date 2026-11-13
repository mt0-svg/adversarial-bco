/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XCallSz
public import AdversarialBco.Bit.Transfer.XVec

@[expose] public section

/-!
# One call of BL's projection routine

`callBL_of : EllRule → CallPrepBL → RowBL → CallBL`: the command `xprep L; xell L blkBL (xrow L)`. The preparation
writes the inputs of the block; `RowCtx` survives it and every change of the routine (`CtxOK`), since it reads only the
registers below `6`, the slots below `23` and the arrays `0`, `1`; the routine runs on the cleared call, whose bit
length is at most `callSzB d E s (size M)` (`ellSz_call`, Bit/Transfer/XCallSz.lean). Work term
`(C₂ + C₃ + C₁ (8 + C₃)^{k₁}) W^{k₂ + k₃ + (3 + k₃) k₁}`, `W = d + m + size M + E + s + 1`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-- `RowCtx` reads the registers below `6`, the slots below `23` and the arrays `0`, `1` only. -/
theorem rowCtx_of_agree {L : Layout} {m E : ℕ} {cfg : Cfg d} {σ σ' : Env d} (h : RowCtx L m E cfg σ)
    (hN : ∀ j < 6, σ'.nat j = σ.nat j) (hS : ∀ y < 23, σ'.sc y = σ.sc y)
    (hA : ∀ a < 2, ∀ k, σ'.arr a k = σ.arr a k) : RowCtx L m E cfg σ' := by
  obtain ⟨lay, ⟨r1, r2, r3, r4, r5⟩, ⟨c1, c2, c3⟩, ⟨DS, hDS, eDS, hmu, hAS⟩, ⟨bS, bA⟩⟩ := h
  refine ⟨lay, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨DS, hDS, ?_, fun j => ?_, fun i j => ?_⟩, ⟨fun y hy => ?_,
    fun a ha k hk => ?_⟩⟩
  · rw [hN rD (by decide)]; exact r1
  · rw [hN rM (by decide)]; exact r2
  · rw [hN rMk (by decide)]; exact r3
  · rw [hN rOne (by decide)]; exact r4
  · rw [hN rPF (by decide)]; exact r5
  · rw [hS sZ (by decide)]; exact c1
  · rw [hS s2pF (by decide)]; exact c2
  · rw [hS sEps (by decide)]; exact c3
  · rw [hS sDS (by decide)]; exact eDS
  · obtain ⟨x, ex, hx⟩ := hmu j
    exact ⟨x, by rw [hA aMuS (by decide)]; exact ex, hx⟩
  · obtain ⟨x, ex, hx⟩ := hAS i j
    exact ⟨x, by rw [hA aAS (by decide)]; exact ex, hx⟩
  · obtain ⟨z, ez, bz⟩ := bS y hy
    have : y < 23 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, s2pF, sEps, sDS] at hy; omega
    exact ⟨z, by rw [hS y this]; exact ez, bz⟩
  · obtain ⟨z, ez, bz⟩ := bA a ha k hk
    have : a < 2 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false, aMuS, aAS] at ha; omega
    exact ⟨z, by rw [hA a this]; exact ez, bz⟩

/-- `RowCtx` survives the preparation. -/
theorem rowCtx_prep {L : Layout} {m E : ℕ} {cfg : Cfg d} {σ σ' : Env d} (h : RowCtx L m E cfg σ)
    (F : FrameA SPrep NPrep (fun a _ => APrep a) σ σ') : RowCtx L m E cfg σ' :=
  rowCtx_of_agree h (fun j hj => F.1 j (by simp only [NPrep, NRow]; omega))
    (fun y hy => F.2.1 y (by simp only [SPrep, SRow, sEl]; omega))
    (fun a ha k => F.2.2.1 a k (by simp only [APrep, ARow, aEH, aEf]; omega))

/-- `RowCtx` survives the routine and the row command (`CtxOK`). -/
theorem rowCtx_ok {L : Layout} {m E : ℕ} {cfg : Cfg d} : CtxOK blkBL (RowCtx L m E cfg) SRow NRow ARow :=
  fun _ _ h _ F => rowCtx_of_agree h (fun j hj => F.1 j (by simp only [blkBL, rEE, NRow]; omega))
    (fun y hy => F.2.1 y (by simp only [blkBL, oE, SRow]; omega))
    (fun a ha k => F.2.2.1 a k (by simp only [blkBL, aWE, ARow]; omega))

/-- The kept rows are at most `m`. -/
theorem keptIdx_length_le {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) : (keptIdx A).length ≤ m :=
  (List.length_filter_le _ _).trans (List.length_finRange).le

/-- The size of the routine's work term against `W`. -/
theorem callW_le {C1 k1 C3 k3 W x Kr : ℕ} (hW : 1 ≤ W) (hx : x + 1 ≤ 8 * W ^ 3) (hKr : Kr ≤ C3 * W ^ k3) :
    C1 * (x + Kr + 1) ^ k1 ≤ C1 * (8 + C3) ^ k1 * W ^ ((3 + k3) * k1) := by
  have h3 : W ^ 3 ≤ W ^ (3 + k3) := Nat.pow_le_pow_right hW (by omega)
  have hk : W ^ k3 ≤ W ^ (3 + k3) := Nat.pow_le_pow_right hW (by omega)
  have hs : x + Kr + 1 ≤ (8 + C3) * W ^ (3 + k3) := by
    have := Nat.mul_le_mul_left 8 h3
    have := Nat.mul_le_mul_left C3 hk
    nlinarith
  calc C1 * (x + Kr + 1) ^ k1 ≤ C1 * ((8 + C3) * W ^ (3 + k3)) ^ k1 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs _)
    _ = C1 * (8 + C3) ^ k1 * W ^ ((3 + k3) * k1) := by rw [mul_pow, ← pow_mul, mul_assoc]

/-- `c x^a ≤ C W^K` from `x ≤ W`, `c ≤ C`, `a ≤ K`. -/
theorem pw_up {W C K c a x : ℕ} (hW : 1 ≤ W) (hx : x ≤ W) (hc : c ≤ C) (ha : a ≤ K) : c * x ^ a ≤ C * W ^ K :=
  Nat.mul_le_mul hc ((Nat.pow_le_pow_left hx a).trans (Nat.pow_le_pow_right hW ha))

set_option maxHeartbeats 1000000 in
/-- **One call of BL's projection routine** from the routine, the preparation and the row command. -/
theorem callBL_of (hE : EllRule) (hP : CallPrepBL) (hR : RowBL) : CallBL := by
  obtain ⟨xell, C1, k1, nS, nN, nA, H1⟩ := hE
  obtain ⟨xprep, C2, k2, H2⟩ := hP
  obtain ⟨xrow, C3, k3, H3⟩ := hR
  refine ⟨fun L => .seq (xprep L) (xell L blkBL (xrow L)), C2 + C3 + C1 * (8 + C3) ^ k1,
    k2 + k3 + (3 + k3) * k1, nS, nN, nA, ?_⟩
  intro d L w n m M E ℓa ℓ s A b c S H g ℓq r P f e σ hd hL hB hM hOn he0 he1 hC hI hℓ hℓa
  obtain ⟨W, hW⟩ : ∃ W, W = d + m + M.size + E + s + 1 := ⟨_, rfl⟩
  rw [← hW] at hℓ hℓa ⊢
  have hW1 : 1 ≤ W := by omega
  -- the bit length of the call
  have hsz := ellSz_call hM hOn he0 he1 hC hI
  have hkm := keptIdx_length_le A
  have hx : d + (clearQ (callOf (mkCfg d n m A b c S) H g ℓq r P f e)).m +
      ellSz (clearQ (callOf (mkCfg d n m A b c S) H g ℓq r P f e)) + 1 ≤ 8 * W ^ 3 := by
    have h1 : (d + 1) ^ 2 * (E + s + M.size + 1) ≤ W ^ 3 := by
      rw [pow_succ W 2]; exact Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) (by omega)
    have h2 : W ≤ W ^ 3 := Nat.le_self_pow (by norm_num) W
    have h3 : (clearQ (callOf (mkCfg d n m A b c S) H g ℓq r P f e)).m = (keptIdx A).length := rfl
    unfold callSzB at hsz
    rw [h3]
    nlinarith
  have hKr : C3 * (d + m + M.size + E + 1) ^ k3 ≤ C3 * W ^ k3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hEW := callW_le (C1 := C1) (k1 := k1) hW1 hx hKr
  have hEW0 := callW_le (C1 := C1) (k1 := k1) (C3 := C3) (k3 := k3) (Kr := 0) hW1 hx (Nat.zero_le _)
  rw [add_zero] at hEW0
  have hKK : ∀ {a : ℕ}, a ≤ k2 + k3 + (3 + k3) * k1 → W ^ a ≤ W ^ (k2 + k3 + (3 + k3) * k1) :=
    fun h => Nat.pow_le_pow_right hW1 h
  have up1 : C1 * (8 + C3) ^ k1 * W ^ ((3 + k3) * k1) ≤
      (C2 + C3 + C1 * (8 + C3) ^ k1) * W ^ (k2 + k3 + (3 + k3) * k1) :=
    Nat.mul_le_mul (by omega) (hKK (by omega))
  have up2 : C2 * (d + s + 1) ^ k2 ≤ (C2 + C3 + C1 * (8 + C3) ^ k1) * W ^ (k2 + k3 + (3 + k3) * k1) :=
    pw_up hW1 (by omega) (by omega) (by omega)
  have up3 : C3 * (d + m + M.size + E + 1) ^ k3 ≤ (C2 + C3 + C1 * (8 + C3) ^ k1) * W ^ (k2 + k3 + (3 + k3) * k1) :=
    pw_up hW1 (by omega) (by omega) (by omega)
  have hRP := H3 d L w n m M E ℓa ℓ A b c S H g ℓq r P f e hd hL hM hOn he0 he1 (up3.trans hℓ)
    (lt_of_le_of_lt up3 hℓa)
  refine XV.mono (K := C2 * (d + s + 1) ^ k2 + C1 * (d + (clearQ (callOf (mkCfg d n m A b c S) H g ℓq r P f e)).m +
      ellSz (clearQ (callOf (mkCfg d n m A b c S) H g ℓq r P f e)) + C3 * (d + m + M.size + E + 1) ^ k3 + 1) ^ k1)
    ?_ ?_ (fun _ h => h)
  · refine XV.seq (H2 d L (ctxOf w n m A b) ℓa ℓ s (mkCfg d n m A b c S) H g ℓq r P f e σ hd hL hC.lay hI
      (up2.trans hℓ) (lt_of_le_of_lt up2 hℓa)) fun σ1 h1 => ?_
    have F1 : FrameA SPrep NPrep (fun a _ => APrep a) σ σ1 := h1.2.2
    refine XV.mono (H1 d L (ctxOf w n m A b) ℓa ℓ blkBL _ (xrow L) _ SRow NRow ARow _ σ1 hd hL hB blkBL_avoid hRP
      rowCtx_ok h1.1 (rowCtx_prep hC F1) ((hEW0.trans up1).trans hℓ) (lt_of_le_of_lt (hEW0.trans up1) hℓa)) le_rfl ?_
    intro σ' h2
    have F : FrameA (fun y => blkBL.o ≤ y ∨ SRow y) (fun j => blkBL.rE ≤ j ∨ NRow j)
        (fun b _ => blkBL.aW ≤ b ∨ ARow b) σ1 σ' := h2.2.2
    refine ⟨h2.1, h2.2.1.trans h1.2.1, ?_⟩
    exact (F1.mono (fun _ h => Or.inr h) (fun _ h => Or.inr h) (fun _ _ h => Or.inr h)).trans
      (F.mono (fun _ h => h.elim Or.inl fun h => Or.inr (Or.inr h)) (fun _ h => h.elim Or.inl Or.inr)
        (fun _ _ h => h.elim Or.inl fun h => Or.inr (Or.inr h)))
  · have ha := pw_up (C := C2) (K := k2 + k3 + (3 + k3) * k1) hW1 (show d + s + 1 ≤ W by omega) le_rfl
      (by omega : k2 ≤ _)
    have hb := hEW.trans (Nat.mul_le_mul_left (C1 * (8 + C3) ^ k1) (hKK (by omega : (3 + k3) * k1 ≤ _)))
    calc _ ≤ C2 * W ^ (k2 + k3 + (3 + k3) * k1) + C1 * (8 + C3) ^ k1 * W ^ (k2 + k3 + (3 + k3) * k1) :=
          Nat.add_le_add ha hb
      _ = (C2 + C1 * (8 + C3) ^ k1) * W ^ (k2 + k3 + (3 + k3) * k1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

end AdversarialBco.Bit.Transfer.BLM
