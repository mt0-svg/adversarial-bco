/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.BLOParam
public import AdversarialBco.Bit.BLBasic

@[expose] public section

/-!
# BL-O: the coins each piece reads

* `posLocalO : PosLocalO`: the position (TRI-OGD-O in rationals) reads the coins below `m_st L' = LposO ≤ K0O` only;
* `drawLocalO : DrawLocalO` (UNI-ORDER): the draw `ξ'_t` reads the coins in `[winL t, winN t)`, the dither `ζ'_t`
  those in `[winN t, winL (t + 1))`.
-/

namespace AdversarialBco.Unified.BLO

open AdversarialBco AdversarialBco.Bit.RQ
open AdversarialBco.Bit.BLP (draw blkUW gOut readCoins_congr blkStart_succ_le)
open AdversarialBco.BitRAM (readCoins)
open AdversarialBco.Bit (triLay)

variable {d : ℕ}

/-! ## The position -/

theorem triIterQ_congr (r a b s : ℚ) (Vt : PosQ d → (Fin d → ℚ) → PosQ d) (y y' : ℕ → Fin d → ℚ) :
    ∀ t, (∀ u < t, y u = y' u) → triIterQ r a b s Vt y t = triIterQ r a b s Vt y' t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro h
    simp only [triIterQ]
    rw [ih fun u hu => h u (by omega), h t (by omega)]

theorem triAvgQ_congr (r a b s : ℚ) (Vt : PosQ d → (Fin d → ℚ) → PosQ d) (y y' : ℕ → Fin d → ℚ) (N : ℕ)
    (h : ∀ u < N, y u = y' u) : triAvgQ r a b s Vt y N = triAvgQ r a b s Vt y' N := by
  unfold triAvgQ
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  exact triIterQ_congr r a b s Vt y y' t fun u hu => h u (by omega)

theorem triDrawQ_congr (B : ℕ) (x x' : ℕ → Bool) (t : ℕ) (h : ∀ k < (t + 1) * (2 * d * B), x k = x' k) :
    triDrawQ d B x t = triDrawQ d B x' t := by
  funext i
  have hi := i.isLt
  have hb : (2 * (t * d + i) + 1) * B + B ≤ (t + 1) * (2 * d * B) := by
    have e : (2 * (t * d + i) + 1) * B + B = (2 * (t * d + i) + 2) * B := by ring
    rw [e]
    have : 2 * (t * d + i) + 2 ≤ (t + 1) * (2 * d) := by
      have : (i : ℕ) + 1 ≤ d := hi
      nlinarith
    calc (2 * (t * d + i) + 2) * B ≤ (t + 1) * (2 * d) * B := Nat.mul_le_mul_right _ this
      _ = (t + 1) * (2 * d * B) := by ring
  have hb0 : 2 * (t * d + i) * B + B ≤ (2 * (t * d + i) + 1) * B := by
    have e : (2 * (t * d + i) + 1) * B = 2 * (t * d + i) * B + B := by ring
    omega
  unfold triDrawQ
  rw [readCoins_congr x x' _ B (fun j _ hj => h j (by omega)),
    readCoins_congr x x' _ B (fun j _ hj => h j (by omega))]

theorem triStepOQ_congr (gs : ℕ → PosQ d → (Fin d → ℚ) → Fin d → ℚ) (ℓ j : ℕ) (P : PosQ d) (x x' : ℕ → Bool)
    (h : ∀ k < triLTQ d ℓ, x k = x' k) : triStepOQ gs ℓ j P x = triStepOQ gs ℓ j P x' := by
  have hc : triCoreOutOQ d ℓ (gs j P) (fun t => triDrawQ d (triBgQ d) x t) =
      triCoreOutOQ d ℓ (gs j P) (fun t => triDrawQ d (triBgQ d) x' t) := by
    unfold triCoreOutOQ
    apply triAvgQ_congr
    intro u hu
    apply triDrawQ_congr
    intro k hk
    apply h k
    have h1 : (u + 1) * (2 * d * triBgQ d) ≤ 2 ^ triNeTQ d ℓ * (2 * d * triBgQ d) :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hu)
    unfold triLTQ
    omega
  unfold triStepOQ
  rw [hc]

theorem triStageNOQ_congr (gs : ℕ → PosQ d → (Fin d → ℚ) → Fin d → ℚ) (c : Fin d → ℚ) (r0 : ℚ) (ℓ : ℕ)
    (ω ω' : ℕ → ℕ → Bool) : ∀ J, (∀ j < J, ∀ k < triLTQ d ℓ, ω j k = ω' j k) →
      triStageNOQ gs c r0 ℓ ω J = triStageNOQ gs c r0 ℓ ω' J := by
  intro J
  induction J with
  | zero => intro _; rfl
  | succ J ih =>
    intro h
    simp only [triStageNOQ]
    rw [ih fun j hj k hk => h j (by omega) k hk]
    exact triStepOQ_congr gs ℓ J _ _ _ fun k hk => h J (by omega) k hk

theorem posO_congr (d n : ℕ) (orc : (Fin d → ℚ) → ℕ → Bool) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (cs cs' : ℕ → Bool)
    (h : ∀ i < LposO d n δ r0 R0, cs i = cs' i) : posO d n orc δ r0 R0 a cs = posO d n orc δ r0 R0 a cs' := by
  unfold posO triPosOQ
  refine triStageNOQ_congr _ _ _ _ _ _ _ fun j hj k hk => h _ ?_
  rw [triLay, if_pos ⟨hj, hk⟩]
  unfold LposO
  calc j * triLTQ d (ellPosO d n (kDel δ) r0 R0) + k <
        j * triLTQ d (ellPosO d n (kDel δ) r0 R0) + triLTQ d (ellPosO d n (kDel δ) r0 R0) := by omega
    _ = (j + 1) * triLTQ d (ellPosO d n (kDel δ) r0 R0) := by ring
    _ ≤ triMstQ r0 R0 * triLTQ d (ellPosO d n (kDel δ) r0 R0) := Nat.mul_le_mul_right _ hj

theorem posLocalO : PosLocalO := by
  intro d n orc δ r0 R0 a cs cs' _ h
  have hL := LposO_le_K0O d n δ r0 R0
  exact ⟨hL, posO_congr d n orc δ r0 R0 a cs cs' fun i hi => h i (by omega)⟩

/-! ## The draws -/

theorem blkStart_lt (d K0 B t q q' : ℕ) (hq : q < q') :
    Bit.Sched.blkStart d K0 B t q + 2 * B ≤ Bit.Sched.blkStart d K0 B t q' := by
  unfold Bit.Sched.blkStart
  have h2 : 2 * B * (t * Bit.Sched.nBlk d + q + 1) ≤ 2 * B * (t * Bit.Sched.nBlk d + q') :=
    Nat.mul_le_mul_left _ (by omega)
  have e : 2 * B * (t * Bit.Sched.nBlk d + q + 1) = 2 * B * (t * Bit.Sched.nBlk d + q) + 2 * B := by ring
  omega

theorem blkStart_le (d K0 B t q q' : ℕ) (hq : q ≤ q') : Bit.Sched.blkStart d K0 B t q ≤ Bit.Sched.blkStart d K0 B t q' := by
  unfold Bit.Sched.blkStart
  have : 2 * B * (t * Bit.Sched.nBlk d + q) ≤ 2 * B * (t * Bit.Sched.nBlk d + q') := Nat.mul_le_mul_left _ (by omega)
  omega

/-- A block reads only its own `2B` coins. -/
theorem blkUW_congr_win (cs cs' : ℕ → Bool) (K0 B d t q lo hi : ℕ) (hlo : lo ≤ Bit.Sched.blkStart d K0 B t q)
    (hhi : Bit.Sched.blkStart d K0 B t q + 2 * B ≤ hi) (h : ∀ j, lo ≤ j → j < hi → cs j = cs' j) :
    blkUW cs K0 B d t q = blkUW cs' K0 B d t q := by
  unfold blkUW
  rw [readCoins_congr cs cs' _ B (fun j h1 h2 => h j (by omega) (by omega)),
    readCoins_congr cs cs' _ B (fun j h1 h2 => h j (by omega) (by omega))]

theorem drawLocalO : DrawLocalO := by
  intro d n δ r0 R0 a cs cs' t
  set K0 := K0O d n δ r0 R0
  set B := (parO d n δ).B
  have hlast : (d + 1) / 2 = Bit.Sched.nBlk d - 1 := by unfold Bit.Sched.nBlk; omega
  refine ⟨fun h => ?_, fun h => ?_⟩
  · funext i
    have hq : (i : ℕ) / 2 < Bit.Sched.nBlk d - 1 := by
      have := i.isLt
      unfold Bit.Sched.nBlk
      omega
    have hb : blkUW cs K0 B d t ((i : ℕ) / 2) = blkUW cs' K0 B d t ((i : ℕ) / 2) :=
      blkUW_congr_win cs cs' K0 B d t _ _ _ (blkStart_le d K0 B t 0 _ (Nat.zero_le _))
        (blkStart_lt d K0 B t _ _ hq) h
    show (if (i : ℕ) % 2 = 0 then _ else _) = (if (i : ℕ) % 2 = 0 then _ else _)
    rw [hb]
  · show (gOut B (blkUW cs K0 B d t ((d + 1) / 2))).1 / 2 = (gOut B (blkUW cs' K0 B d t ((d + 1) / 2))).1 / 2
    have hq : (d + 1) / 2 < Bit.Sched.nBlk d := by unfold Bit.Sched.nBlk; omega
    have hb : blkUW cs K0 B d t ((d + 1) / 2) = blkUW cs' K0 B d t ((d + 1) / 2) :=
      blkUW_congr_win cs cs' K0 B d t _ _ _ (by rw [hlast]; exact le_refl _) (blkStart_succ_le d K0 B t _ hq) h
    rw [hb]

end AdversarialBco.Unified.BLO
