/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.BLOSpec
public import AdversarialBco.Bit.Transfer.XTriChain

@[expose] public section

/-!
# TRI-OGD-O in integers

The integers that the program of `TriSpecO` (Unified/ProgOSetup.lean) computes, as pure functions mirroring its
loops, and `tzPosO_eq`: the position they give is `posO` (Unified/BLOSpec.lean). The integer model of v2.1's TRI-M
(Bit/Transfer/XTriZ.lean) with the row scan replaced by the SEP field of the stages:

* the grid of the iterates `2^{-G'}`, `G' = B_v + j_s' + j_a` (`tGT`), the grid of the core output `G_c' = G' + n_e'`
  (`tGcT`), the scale `2^{G' + 2p}` of the base point `ẑ = X̂_μ 2^{2p} + X̂_T Y` (`tKZ`); the constants of a draw
  `tzDCO` (at the step `2^{-j_s'}`);
* the base point rounded to SEP's grid `2^{-stE}` in integers (`rndZ`, `rndZ_eq`: it is `rndPt`), SEP's vector `G` of
  the stage (`sepGZ`, `0` on failure), read as `G / 2^{stEu + 1}` (`tBb`, `stSep_eq`: it is `stSep`);
* one draw is v2.1's update `tzUpd` with `A = G`, `|β̃| = 2^{stEu + 1}`; the iterates and their sum (`tzIterO`,
  `tzSumO`, `stSumO`), the composition (v2.1's `tzComp`), the stages (`tzStageO`) from the first position
  `(a, r₀ I)` in integers (`tzP0`), the position on the coins (`tzPosO`).

The chain: `tzIterO_eq` (one draw is v2.1's `tzUpd_step`), `core_outO_eq`, `tzStageO_eq`, `tzPosO_eq`.
-/

namespace AdversarialBco.Unified.ProgO.TriO

open AdversarialBco AdversarialBco.Uni AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM
open AdversarialBco.Unified.BLO Matrix

variable {d : ℕ}

/-! ## Constants -/

/-- `G' = B_v + j_s' + j_a`, the grid `2^{-G'}` of the iterates. -/
def tGT (d ℓ : ℕ) : ℕ := triBvQ d + triJsTQ d ℓ + triJaQ d

/-- `G_c' = G' + n_e'`, the grid of the core output (the average of `2^{n_e'}` iterates). -/
def tGcT (d ℓ : ℕ) : ℕ := tGT d ℓ + triNeTQ d ℓ

/-- The scale of the base point `ẑ`: `2^{G' + 2p}`. -/
def tKZ (d ℓ : ℕ) : ℕ := tGT d ℓ + 2 * tzP d

/-- The constants of one draw of TRI-OGD-O at the step `2^{-j_s'}`. -/
def tzDCO (d ℓ : ℕ) : DC where
  PB := 2 ^ triBvQ d
  P2 := 2 ^ (2 * tzP d)
  PG := 2 ^ tGT d ℓ
  Pj := 2 ^ triJaQ d
  R := 2 ^ (triLa (triSQ d) - 3 + tGT d ℓ)
  Al := 2 ^ (triBvQ d + triJsTQ d ℓ)
  Bh := 161 * 2 ^ (triLa (triSQ d) - 10 + tGT d ℓ)
  dd := d

/-- The divisor of SEP's vector: `g = G / 2^{stEu + 1}`. -/
def tBb (d : ℕ) : ℤ := 2 ^ (stEu d + 1)

/-! ## The SEP field in integers -/

/-- The nearest point of the grid `2^{-E}` to `z / 2^K`, as numerators. -/
def rndZ (E K : ℕ) (z : Fin d → ℤ) : Fin d → ℤ := fun i => (2 * z i * 2 ^ E + 2 ^ K) / (2 * 2 ^ K)

/-- SEP's vector of stage `j` at the position `P` and the base point `z / 2^K`: SEP's `G`, `0` when SEP fails. -/
def sepGZ (orc : (Fin d → ℚ) → ℕ → Bool) (a : Fin d → ℚ) (r0 R0 : ℚ) (j : ℕ) (P : PosQ d) (K : ℕ)
    (z : Fin d → ℤ) : Fin d → ℤ :=
  match sepE (stEv orc a r0 R0 j P) (rndZ (stE d) K z) (stE d) (stE1 d) (triETauQ d) 0 (stEu d) with
  | none => 0
  | some (_, G) => G

/-! ## The core and the stages -/

/-- The iterates at the grid with the field `gv` over `Bb`: `X̂_0 = (0, P_G I)`, then v2.1's update with `A = gv ẑ`. -/
def tzIterO (c : DC) (gv : (Fin d → ℤ) → Fin d → ℤ) (Bb : ℤ) (Y : ℕ → Fin d → ℤ) : ℕ → PosZ d
  | 0 => (0, c.PG • 1)
  | t + 1 => tzUpd c (tzIterO c gv Bb Y t) (gv (tzZ (tzIterO c gv Bb Y t) (Y t) c.P2)) (Y t) Bb

/-- The sum of the first `N` iterates. -/
def tzSumO (c : DC) (gv : (Fin d → ℤ) → Fin d → ℤ) (Bb : ℤ) (Y : ℕ → Fin d → ℤ) (N : ℕ) : PosZ d :=
  ∑ t ∈ Finset.range N, tzIterO c gv Bb Y t

/-- A stage position in integers read as a rational position. -/
def posZ (P : StZ d) : PosQ d := (fun i => (P.mu i : ℚ) / P.D, fun i l => (P.T i l : ℚ) / P.D)

/-- The field of stage `j` at the integer position `P`, on the base points at the scale `2^{tKZ}`. -/
def gvO (orc : (Fin d → ℚ) → ℕ → Bool) (a : Fin d → ℚ) (r0 R0 : ℚ) (ℓ j : ℕ) (P : StZ d) :
    (Fin d → ℤ) → Fin d → ℤ :=
  sepGZ orc a r0 R0 j (posZ P) (tKZ d ℓ)

/-- The core output of stage `j` at the integer position `P` on the draws `Y`. -/
def stSumY (orc : (Fin d → ℚ) → ℕ → Bool) (a : Fin d → ℚ) (r0 R0 : ℚ) (ℓ j : ℕ) (P : StZ d)
    (Y : ℕ → Fin d → ℤ) : PosZ d :=
  tzSumO (tzDCO d ℓ) (gvO orc a r0 R0 ℓ j P) (tBb d) Y (2 ^ triNeTQ d ℓ)

/-- The core output of stage `j` at the integer position `P` on the stage coins `x`. -/
def stSumO (orc : (Fin d → ℚ) → ℕ → Bool) (a : Fin d → ℚ) (r0 R0 : ℚ) (ℓ j : ℕ) (P : StZ d) (x : ℕ → Bool) :
    PosZ d :=
  stSumY orc a r0 R0 ℓ j P (tzY d (triBgQ d) x)

/-- The stages from the first position `P0` on the stage coins `ω`. -/
def tzStageO (orc : (Fin d → ℚ) → ℕ → Bool) (a : Fin d → ℚ) (r0 R0 : ℚ) (ℓ : ℕ) (P0 : StZ d)
    (ω : ℕ → ℕ → Bool) : ℕ → StZ d
  | 0 => P0
  | j + 1 => tzComp (tzStageO orc a r0 R0 ℓ P0 ω j) (stSumO orc a r0 R0 ℓ j (tzStageO orc a r0 R0 ℓ P0 ω j) (ω j))
      (tGcT d ℓ)

/-- The first position `(a, r₀ I)` with `a = N_a / D_a`, `r₀ = r_n / r_d`: `(N_a r_d, D_a r_n I) / (D_a r_d)`. -/
def tzP0 (Da : ℤ) (Na : Fin d → ℤ) (rn rd : ℤ) : StZ d := ⟨Da * rd, fun i => Na i * rd, (Da * rn) • 1⟩

/-- The coins of the stages: stage `j` reads `cs (triLay m_st L' (j, k))`. -/
def omO (mst LT : ℕ) (cs : ℕ → Bool) : ℕ → ℕ → Bool := fun j k => cs (triLay mst LT (j, k))

/-- The confidence integer of the position at the input. -/
abbrev ellO (d n : ℕ) (δ r0 R0 : ℚ) : ℕ := ellPosO d n (kDel δ) r0 R0

/-- The position of the program on the coins `cs` from the first position `P0`. -/
def tzPosO (d n : ℕ) (orc : (Fin d → ℚ) → ℕ → Bool) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (P0 : StZ d) (cs : ℕ → Bool) :
    StZ d :=
  tzStageO orc a r0 R0 (ellO d n δ r0 R0) P0 (omO (triMstQ r0 R0) (triLTQ d (ellO d n δ r0 R0)) cs)
    (triMstQ r0 R0)

/-! ## The chain -/

theorem rndZ_eq (E K : ℕ) (z : Fin d → ℤ) : rndPt E (fun i => (z i : ℚ) / 2 ^ K) = rndZ E K z := by
  funext i
  unfold rndPt rndZ
  have hK : (0 : ℤ) < 2 * 2 ^ K := by positivity
  rw [← floor_div_int _ _ hK]
  congr 1
  push_cast
  have h2 : (2 : ℚ) ^ K ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

theorem stSep_eq (orc : (Fin d → ℚ) → ℕ → Bool) (a : Fin d → ℚ) (r0 R0 : ℚ) (j : ℕ) (P : PosQ d) (K : ℕ)
    (z : Fin d → ℤ) :
    stSep orc a r0 R0 j P (fun i => (z i : ℚ) / 2 ^ K) = fun i => (sepGZ orc a r0 R0 j P K z i : ℚ) / tBb d := by
  unfold stSep sepGZ tBb
  rw [rndZ_eq]
  rcases sepE (stEv orc a r0 R0 j P) (rndZ (stE d) K z) (stE d) (stE1 d) (triETauQ d) 0 (stEu d) with _ | ⟨Y, G⟩
  · funext i; simp
  · funext i; push_cast; rfl

/-- The base point of a draw at the grid: `μ + T y = ẑ / 2^{G + 2p}`. -/
theorem base_eq (G p : ℕ) (X : PosZ d) (Y : Fin d → ℤ) (x : PosQ d)
    (hx : x = (fun i => (X.1 i : ℚ) / 2 ^ G, fun i l => (X.2 i l : ℚ) / 2 ^ G)) :
    x.1 + x.2 *ᵥ (fun i => (Y i : ℚ) / 2 ^ (2 * p)) =
      fun i => (tzZ X Y (2 ^ (2 * p)) i : ℚ) / 2 ^ (G + 2 * p) := by
  subst hx
  funext i
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct, tzZ]
  push_cast
  have h2G : (2 : ℚ) ^ G ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2p : (2 : ℚ) ^ (2 * p) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [pow_add, add_div, Finset.sum_div]
  congr 1
  · field_simp
  · refine Finset.sum_congr rfl fun l _ => ?_
    field_simp

/-- The iterates of the core with a field given at the grid points of the base points. -/
theorem tzIterO_eq {d : ℕ} (hd : 1 ≤ d) (Bv Js ja p La G : ℕ) (hG : G = Bv + Js + ja) (hLa : 10 ≤ La) (c : DC)
    (hc : c = ⟨2 ^ Bv, 2 ^ (2 * p), 2 ^ G, 2 ^ ja, 2 ^ (La - 3 + G), 2 ^ (Bv + Js), 161 * 2 ^ (La - 10 + G), d⟩)
    (u : (Fin d → ℚ) → Fin d → ℚ) (gv : (Fin d → ℤ) → Fin d → ℤ) (Bb : ℤ) (hBb : 0 < Bb)
    (hu : ∀ z : Fin d → ℤ, u (fun i => (z i : ℚ) / 2 ^ (G + 2 * p)) = fun i => (gv z i : ℚ) / Bb)
    (Y : ℕ → Fin d → ℤ) (y : ℕ → Fin d → ℚ) (hy : ∀ t, y t = fun i => (Y t i : ℚ) / 2 ^ (2 * p)) (t : ℕ) :
    triIterQ (2 ^ (La - 3)) (1 / 2 ^ ja) (161 * 2 ^ (La - 10)) (1 / 2 ^ Js)
        (fun x w => triRoundQ Bv (triVQ u x w)) y t =
      (fun i => ((tzIterO c gv Bb Y t).1 i : ℚ) / 2 ^ G, fun i l => ((tzIterO c gv Bb Y t).2 i l : ℚ) / 2 ^ G) := by
  have hR : 0 ≤ c.R := by rw [hc]; positivity
  have hRB : c.R ≤ c.Bh := by
    rw [hc]
    show (2 : ℤ) ^ (La - 3 + G) ≤ 161 * 2 ^ (La - 10 + G)
    rw [show La - 3 + G = (La - 10 + G) + 7 by omega, pow_add, mul_comm]
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hAl : 0 < c.Al := by rw [hc]; positivity
  have hAB : c.Al ≤ c.Bh := by
    rw [hc]
    show (2 : ℤ) ^ (Bv + Js) ≤ 161 * 2 ^ (La - 10 + G)
    calc (2 : ℤ) ^ (Bv + Js) ≤ 2 ^ (La - 10 + G) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ 161 * 2 ^ (La - 10 + G) := le_mul_of_one_le_left (by positivity) (by norm_num)
  have hP2 : c.P2 = 2 ^ (2 * p) := by rw [hc]
  have main : ∀ t, triIterQ (2 ^ (La - 3)) (1 / 2 ^ ja) (161 * 2 ^ (La - 10)) (1 / 2 ^ Js)
      (fun x w => triRoundQ Bv (triVQ u x w)) y t =
      (fun i => ((tzIterO c gv Bb Y t).1 i : ℚ) / 2 ^ G, fun i l => ((tzIterO c gv Bb Y t).2 i l : ℚ) / 2 ^ G) ∧
      ∀ i, 0 < (tzIterO c gv Bb Y t).2 i i := by
    intro t
    induction t with
    | zero =>
      have hPG : c.PG = 2 ^ G := by rw [hc]
      refine ⟨?_, fun i => ?_⟩
      · simp only [triIterQ, tzIterO, hPG]
        refine Prod.ext (funext fun i => by simp) (funext fun i => funext fun l => ?_)
        simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
        split_ifs <;> simp
      · simp only [tzIterO, hPG, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
        positivity
    | succ t ih =>
      obtain ⟨ih1, ih2⟩ := ih
      set X := tzIterO c gv Bb Y t with hX
      have hu' : u ((((fun i => (X.1 i : ℚ) / 2 ^ G, fun i l => (X.2 i l : ℚ) / 2 ^ G) : PosQ d)).1 +
          (((fun i => (X.1 i : ℚ) / 2 ^ G, fun i l => (X.2 i l : ℚ) / 2 ^ G) : PosQ d)).2 *ᵥ y t) =
          fun i => (gv (tzZ X (Y t) c.P2) i : ℚ) / Bb := by
        rw [hy t, base_eq G p X (Y t) _ rfl, ← hP2]
        exact hu _
      have hstep := tzUpd_step hd Bv Js ja p La G hG hLa X ih2 (gv (tzZ X (Y t) c.P2)) (Y t) Bb hBb _ rfl (y t)
        (hy t) u hu' c hc
      refine ⟨?_, fun i => ?_⟩
      · show triClipQ _ _ _ (triIterQ _ _ _ _ _ y t - _ • _) = _
        rw [ih1]
        exact hstep
      · exact lt_of_lt_of_le hAl ((tzUpd_bound c X _ (Y t) Bb hR hRB hAl hAB).2.2 i)
  exact (main t).1

theorem triLa_ge10 (d : ℕ) : 10 ≤ triLa (triSQ d) := triLa_ge d

/-- **The core of TRI-OGD-O at the grid**: the core output on the draws of the stage coins `x`, with the SEP field of
stage `j` at the position `posZ P`, is the integer sum over `2^{G_c'}`. -/
theorem core_outO_eq (hd : 1 ≤ d) (orc : (Fin d → ℚ) → ℕ → Bool) (a : Fin d → ℚ) (r0 R0 : ℚ) (ℓ j : ℕ)
    (P : StZ d) (x : ℕ → Bool) :
    triCoreOutOQ d ℓ (stSep orc a r0 R0 j (posZ P)) (fun t => triDrawQ d (triBgQ d) x t) =
      (fun i => ((stSumO orc a r0 R0 ℓ j P x).1 i : ℚ) / 2 ^ tGcT d ℓ,
       fun i l => ((stSumO orc a r0 R0 ℓ j P x).2 i l : ℚ) / 2 ^ tGcT d ℓ) := by
  have hc : tzDCO d ℓ = ⟨2 ^ triBvQ d, 2 ^ (2 * tzP d), 2 ^ tGT d ℓ, 2 ^ triJaQ d,
      2 ^ (triLa (triSQ d) - 3 + tGT d ℓ), 2 ^ (triBvQ d + triJsTQ d ℓ), 161 * 2 ^ (triLa (triSQ d) - 10 + tGT d ℓ),
      d⟩ := rfl
  have hy : ∀ t, (fun t => triDrawQ d (triBgQ d) x t) t =
      fun i => ((tzY d (triBgQ d) x t i : ℚ) / 2 ^ (2 * tzP d)) := fun t => by
    simpa [tzP] using triDrawQ_eq d (triBgQ d) x t
  have hu : ∀ z : Fin d → ℤ, stSep orc a r0 R0 j (posZ P) (fun i => (z i : ℚ) / 2 ^ (tGT d ℓ + 2 * tzP d)) =
      fun i => (gvO orc a r0 R0 ℓ j P z i : ℚ) / tBb d := fun z => stSep_eq orc a r0 R0 j (posZ P) _ z
  have hit := tzIterO_eq hd (triBvQ d) (triJsTQ d ℓ) (triJaQ d) (tzP d) (triLa (triSQ d)) (tGT d ℓ) rfl
    (triLa_ge10 d) (tzDCO d ℓ) hc (stSep orc a r0 R0 j (posZ P)) (gvO orc a r0 R0 ℓ j P) (tBb d)
    (by unfold tBb; positivity) hu (tzY d (triBgQ d) x) (fun t => triDrawQ d (triBgQ d) x t) hy
  have havg := avg_eq (2 ^ (triLa (triSQ d) - 3)) (1 / 2 ^ triJaQ d) (161 * 2 ^ (triLa (triSQ d) - 10))
    (1 / 2 ^ triJsTQ d ℓ) (fun x w => triRoundQ (triBvQ d) (triVQ (stSep orc a r0 R0 j (posZ P)) x w))
    (fun t => triDrawQ d (triBgQ d) x t) (tzIterO (tzDCO d ℓ) (gvO orc a r0 R0 ℓ j P) (tBb d) (tzY d (triBgQ d) x))
    (tGT d ℓ) (triNeTQ d ℓ) hit
  unfold triCoreOutOQ
  simpa [triRQ, triAQ, triBQ, stSumO, stSumY, tzSumO, tGcT] using havg

theorem tzStageO_D_pos (orc : (Fin d → ℚ) → ℕ → Bool) (a : Fin d → ℚ) (r0 R0 : ℚ) (ℓ : ℕ) (P0 : StZ d)
    (ω : ℕ → ℕ → Bool) (h0 : 0 < P0.D) : ∀ j, 0 < (tzStageO orc a r0 R0 ℓ P0 ω j).D
  | 0 => h0
  | j + 1 => by
    show 0 < (tzStageO orc a r0 R0 ℓ P0 ω j).D * 2 ^ tGcT d ℓ
    exact mul_pos (tzStageO_D_pos orc a r0 R0 ℓ P0 ω h0 j) (by positivity)

/-- **The stages in integers**: from a first position whose rational reading is `(a, r₀ I)`, stage `j` of TRI-OGD-O in
rationals is the rational reading of `tzStageO`. -/
theorem tzStageO_eq (hd : 1 ≤ d) (orc : (Fin d → ℚ) → ℕ → Bool) (a : Fin d → ℚ) (r0 R0 : ℚ) (ℓ : ℕ)
    (P0 : StZ d) (h0 : 0 < P0.D) (hP0 : posZ P0 = (a, r0 • (1 : Matrix (Fin d) (Fin d) ℚ))) (ω : ℕ → ℕ → Bool) :
    ∀ j, triStageNOQ (stSep orc a r0 R0) a r0 ℓ ω j = posZ (tzStageO orc a r0 R0 ℓ P0 ω j)
  | 0 => hP0.symm
  | j + 1 => by
    show pgCompQ (triStageNOQ (stSep orc a r0 R0) a r0 ℓ ω j)
        (triCoreOutOQ d ℓ (stSep orc a r0 R0 j (triStageNOQ (stSep orc a r0 R0) a r0 ℓ ω j))
          fun t => triDrawQ d (triBgQ d) (ω j) t) = _
    rw [tzStageO_eq hd orc a r0 R0 ℓ P0 h0 hP0 ω j, core_outO_eq hd]
    exact comp_eq _ _ _ (tzStageO_D_pos orc a r0 R0 ℓ P0 ω h0 j)

/-- The first position in integers reads as `(a, r₀ I)`. -/
theorem posZ_tzP0 {Da : ℤ} {Na : Fin d → ℤ} {rn rd : ℤ} {a : Fin d → ℚ} {r0 : ℚ} (hDa : 0 < Da) (hrd : 0 < rd)
    (ha : ∀ i, (Na i : ℚ) / Da = a i) (hr : (rn : ℚ) / rd = r0) :
    posZ (tzP0 Da Na rn rd) = (a, r0 • (1 : Matrix (Fin d) (Fin d) ℚ)) := by
  have hD : (Da : ℚ) ≠ 0 := by exact_mod_cast hDa.ne'
  have hd' : (rd : ℚ) ≠ 0 := by exact_mod_cast hrd.ne'
  refine Prod.ext (funext fun i => ?_) (funext fun i => funext fun l => ?_)
  · simp only [posZ, tzP0]
    rw [← ha i]; push_cast; field_simp
  · simp only [posZ, tzP0, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    rw [← hr]
    split_ifs <;> push_cast <;> field_simp

/-- **TRI-OGD-O in integers**: `posO` is the rational reading of `tzPosO` from the first position in integers. -/
theorem tzPosO_eq (hd : 1 ≤ d) (n : ℕ) (orc : (Fin d → ℚ) → ℕ → Bool) (δ r0 R0 : ℚ) (a : Fin d → ℚ)
    {Da : ℤ} {Na : Fin d → ℤ} {rn rd : ℤ} (hDa : 0 < Da) (hrd : 0 < rd) (ha : ∀ i, (Na i : ℚ) / Da = a i)
    (hr : (rn : ℚ) / rd = r0) (cs : ℕ → Bool) :
    posO d n orc δ r0 R0 a cs = posZ (tzPosO d n orc δ r0 R0 a (tzP0 Da Na rn rd) cs) := by
  unfold posO triPosOQ tzPosO
  exact tzStageO_eq hd orc a r0 R0 _ _ (mul_pos hDa hrd) (posZ_tzP0 hDa hrd ha hr) _ _

/-! ## The coins of a stage -/

theorem tzIterO_congr (c : DC) (gv : (Fin d → ℤ) → Fin d → ℤ) (Bb : ℤ) (Y Y' : ℕ → Fin d → ℤ) (N : ℕ)
    (h : ∀ t < N, Y t = Y' t) : ∀ t ≤ N, tzIterO c gv Bb Y t = tzIterO c gv Bb Y' t
  | 0, _ => rfl
  | t + 1, ht => by
    show tzUpd c (tzIterO c gv Bb Y t) (gv (tzZ (tzIterO c gv Bb Y t) (Y t) c.P2)) (Y t) Bb =
      tzUpd c (tzIterO c gv Bb Y' t) (gv (tzZ (tzIterO c gv Bb Y' t) (Y' t) c.P2)) (Y' t) Bb
    rw [tzIterO_congr c gv Bb Y Y' N h t (by omega), h t (by omega)]

/-- The core output of a stage reads only the first `triLT` coins of the stage. -/
theorem stSumO_congr (orc : (Fin d → ℚ) → ℕ → Bool) (a : Fin d → ℚ) (r0 R0 : ℚ) (ℓ j : ℕ) (P : StZ d)
    (x x' : ℕ → Bool) (h : ∀ k < triLTQ d ℓ, x k = x' k) :
    stSumO orc a r0 R0 ℓ j P x = stSumO orc a r0 R0 ℓ j P x' := by
  unfold stSumO stSumY tzSumO
  refine Finset.sum_congr rfl fun t ht => tzIterO_congr _ _ _ _ _ (2 ^ triNeTQ d ℓ) (fun u hu => ?_) t
    (Finset.mem_range.1 ht).le
  have hL : 2 * triBgQ d * d * (u + 1) ≤ triLTQ d ℓ := by
    unfold triLTQ
    calc 2 * triBgQ d * d * (u + 1) ≤ 2 * triBgQ d * d * 2 ^ triNeTQ d ℓ := Nat.mul_le_mul_left _ hu
      _ = 2 ^ triNeTQ d ℓ * (2 * d * triBgQ d) := by ring
  rw [tzY_shift (triBgQ d) 0 u x' x (fun k hk => by rw [zero_add]; exact h k (by omega)),
    tzY_shift (triBgQ d) 0 u x' x' (fun k _ => by rw [zero_add])]

end AdversarialBco.Unified.ProgO.TriO
