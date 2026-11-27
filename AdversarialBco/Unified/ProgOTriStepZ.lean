/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOTriKX

@[expose] public section

/-!
# TRI-OGD-O on the oracle machine: the base point and its rounding

The first part of the core step `xstepO`: the base point `ẑ = tzZ X̂ Y P₂` into `aT + 7` (with `ieZ`,
Bit/Transfer/XTriStep.lean), then its rounding to SEP's grid `Y₀ = rndZ E K ẑ` into `aT + 18` (one `xmapE`
with an integer division, `2^E` from `sCE`, `2^K` from `sC2K`). Rule `XV.zO`.
-/

namespace AdversarialBco.Unified.ProgO.TriO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM
open AdversarialBco.Unified.ProgO Matrix

variable {d : ℕ}

/-- `(2 ẑ_i 2^E + 2^K) / (2^K + 2^K)`, `ẑ_i = aZ[nr]`, `2^E` in `sE`, `2^K` in `sK`. -/
def ieRnd (aZ sE sK nr : ℕ) : IE :=
  .ediv (.op .add (.op .mul (.op .add (.arr aZ nr) (.arr aZ nr)) (.sc sE)) (.sc sK)) (.op .add (.sc sK) (.sc sK))

/-- The base point `ẑ = X̂_μ P₂ + X̂_T Y` into `aT + 7` and its rounding `rndZ E K ẑ` into `aT + 18`. -/
def xzO (L : Layout) : XCmd :=
  .seq (xmatvec L (oT + 1) (oT + 20) (oT + 40) (aT + 3) (aT + 6) (aT + 7) (rT + 7) (rT + 4) (rT + 5) rD rT)
  (.seq (.prim (.frag (.nconst (rT + 4) 0)))
  (.seq (xmapE L (oT + 1) (oT + 40) (ieZ (aT + 2) (aT + 7) (oT + 5) (rT + 4)) (aT + 7) (rT + 4) rT (rT + 5) rD rT)
  (.seq (.prim (.frag (.nconst (rT + 4) 0)))
    (xmapE L (oT + 1) (oT + 40) (ieRnd (aT + 7) sCE sC2K (rT + 4)) (aT + 18) (rT + 4) rT (rT + 5) rD rT))))

/-- The units of `xzO`. -/
abbrev zOK (d : ℕ) : ℕ :=
  d * (d * 10 + 9) + 4 + (1 + (d * (7 + 6) + 3 + (1 + (d * (13 + 6) + 3))))

/-- The slots `xzO` writes. -/
abbrev zS (y : ℕ) : Prop := (oT + 16 ≤ y ∧ y < oT + 35) ∨ oT + 40 ≤ y

/-- The registers `xzO` writes. -/
abbrev zN (j : ℕ) : Prop := rT + 3 ≤ j ∧ j < rT + 11

/-- The array cells `xzO` writes. -/
abbrev zA (d : ℕ) (b k : ℕ) : Prop := (b = aT + 7 ∨ b = aT + 18) ∧ k < d

theorem abs_rndZ_le {E K F : ℕ} {z : Fin d → ℤ} (bz : ∀ i, |z i| ≤ 2 ^ F) (i : Fin d) :
    |rndZ E K z i| ≤ 2 ^ (F + E + 1) + 2 ^ K := by
  unfold rndZ
  refine (Int.abs_ediv_le_abs _ _).trans ((abs_add_le _ _).trans (add_le_add ?_ ?_))
  · rw [abs_mul, abs_mul, abs_two, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ E), pow_add, pow_add, pow_one]
    have := bz i
    have h2E : (0 : ℤ) < 2 ^ E := by positivity
    nlinarith
  · rw [abs_of_pos (by positivity)]

set_option maxHeartbeats 4000000 in
/-- The rule of `xzO`: `ẑ = tzZ X̂ Y P₂` in `aT + 7`, `rndZ E K ẑ` in `aT + 18`. -/
theorem XV.zO {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {E F Es K : ℕ} {P2 : ℤ} {Xp : PosZ d} {Y : Fin d → ℤ}
    (hS : oT + 70 ≤ L.NS) (hN : rT + 11 ≤ L.NN) (hA : aT + 19 ≤ L.NA)
    (hσd : σ.nat rD = d) (hσ1 : σ.nat rT = 1) (hda : d * d + d < 2 ^ ℓa)
    (eZ : σ.sc (oT + 1) = 0) (eP2 : σ.sc (oT + 5) = P2) (eCE : σ.sc sCE = ((2 ^ Es : ℤ) : ℝ))
    (eCK : σ.sc sC2K = ((2 ^ K : ℤ) : ℝ))
    (eXm : ∀ l : Fin d, σ.arr (aT + 2) l = Xp.1 l) (eXt : ∀ i l : Fin d, σ.arr (aT + 3) (d * i + l) = Xp.2 i l)
    (eY : ∀ l : Fin d, σ.arr (aT + 6) l = Y l)
    (bX1 : ∀ i, |Xp.1 i| ≤ 2 ^ E) (bX2 : ∀ i l, |Xp.2 i l| ≤ 2 ^ E) (bY : ∀ l, |Y l| ≤ 2 ^ E)
    (bP2 : |P2| ≤ 2 ^ E) (hF : 2 * E + d + 1 ≤ F) (hEs : Es ≤ F) (hK : K ≤ F) (hℓ : 4 * F + 4 < ℓ) :
    XRunsB L X ℓa ℓ (xzO L) σ (zOK d)
      (fun σ' => (∀ l : Fin d, σ'.arr (aT + 7) l = tzZ Xp Y P2 l) ∧
        (∀ l : Fin d, σ'.arr (aT + 18) l = rndZ Es K (tzZ Xp Y P2) l) ∧ σ'.draws = σ.draws ∧
        FrameA zS zN (zA d) σ σ') := by
  have hNS : ∀ k, k < 70 → oT + k < L.NS := fun k h => by omega
  have hNN : ∀ k, k < 11 → rT + k < L.NN := fun k h => by omega
  have hNA : ∀ k, k < 19 → aT + k < L.NA := fun k h => by omega
  have hndN : rD < L.NN := by simp only [rD]; omega
  have hcell : ∀ k < d, k < asz d := fun k hk => by unfold asz; nlinarith
  have hdl : d * 2 ^ (2 * E) < 2 ^ ℓ := by
    have h2 : d < 2 ^ d := Nat.lt_two_pow_self
    calc d * 2 ^ (2 * E) ≤ 2 ^ d * 2 ^ (2 * E) := Nat.mul_le_mul_right _ h2.le
      _ = 2 ^ (2 * E + d) := by rw [← pow_add]; ring_nf
      _ < 2 ^ ℓ := Nat.pow_lt_pow_right (by norm_num) (by omega)
  -- `X̂_T Y`
  refine XV.seq (XV.matvec hL (z := oT + 1) (r := oT + 20) (t := oT + 40) (aM := aT + 3) (ax := aT + 6)
    (ay := aT + 7) (ni := rT + 7) (nr := rT + 4) (nk := rT + 5) (nd := rD) (none := rT) (E := E) (M := Xp.2) (x := Y)
    (by omega) (by omega) (by omega) (by omega) eZ (hNA 3 (by norm_num)) (hNA 6 (by norm_num)) (hNA 7 (by norm_num))
    (by omega) (by omega) (hNN 7 (by norm_num)) (hNN 4 (by norm_num)) (hNN 5 (by norm_num)) hndN
    (hNN 0 (by norm_num)) (by simp only [rD, rT]; decide) hσd hσ1 eXt eY bX2 bY (by omega) hdl)
    fun σ1 ⟨z1, dr1, F1⟩ => ?_
  have G1 : FrameA zS zN (zA d) σ σ1 := F1.mono (fun y h => by simp only [zS]; omega)
    (fun j h => by simp only [zN]; omega) (fun b k h => by simp only [zA]; omega)
  refine XV.seq (XV.nconst hL (hNN 4 (by norm_num)) 0 (by positivity)) fun σ2 e2 => ?_
  subst e2
  have G2 : FrameA zS zN (zA d) σ (σ1.setNat (rT + 4) 0) := G1.setNat (by simp only [zN]; omega) _
  -- `ẑ`
  have F2 : ∀ k (hk : k < d), ∀ σ' : Env d, FrameA (fun y => oT + 40 ≤ y) (fun j => j = rT + 5 ∨ j = rT + 4)
      (fun b c' => b = aT + 7 ∧ 0 ≤ c' ∧ c' < 0 + 1 * k) (σ1.setNat (rT + 4) 0) σ' →
      σ'.draws = (σ1.setNat (rT + 4) 0).draws → σ'.nat (rT + 5) = k → σ'.nat (rT + 4) = 0 + 1 * k →
      (ieZ (aT + 2) (aT + 7) (oT + 5) (rT + 4)).Leaves (2 * E + d) σ' ∧
        (ieZ (aT + 2) (aT + 7) (oT + 5) (rT + 4)).eval σ' = ((tzZ Xp Y P2) ⟨k, hk⟩ : ℤ) := by
    intro k hk σ' F' _ _ hr
    have Fσ := G2.trans (F'.mono (fun y h => by simp only [zS]; omega) (fun j h => by simp only [zN]; omega)
      (fun b k' h => by simp only [zA]; omega))
    have hr' : σ'.nat (rT + 4) = k := by omega
    have xm : σ'.arr (aT + 2) k = Xp.1 ⟨k, hk⟩ := by
      rw [F'.2.2.1 _ _ (by omega), Env.setNat_arr, F1.2.2.1 _ _ (by omega), eXm ⟨k, hk⟩]
    have p2 : σ'.sc (oT + 5) = P2 := by rw [Fσ.2.1 _ (by simp only [zS]; omega), eP2]
    have zk : σ'.arr (aT + 7) k = (Xp.2 *ᵥ Y) ⟨k, hk⟩ := by
      rw [F'.2.2.1 _ _ (by omega), Env.setNat_arr, z1 ⟨k, hk⟩]
    have hE1 : E ≤ 2 * E + d := by omega
    refine ⟨?_, ?_⟩
    · simp only [ieZ, IE.Leaves]
      exact ⟨⟨⟨by rw [hr']; exact hcell k hk, Xp.1 ⟨k, hk⟩, by rw [hr', xm], abs_le_mono (bX1 _) hE1⟩,
        ⟨P2, p2, abs_le_mono bP2 hE1⟩⟩,
        ⟨by rw [hr']; exact hcell k hk, (Xp.2 *ᵥ Y) ⟨k, hk⟩, by rw [hr', zk], abs_mulVec_le bX2 bY _⟩⟩
    · simp only [ieZ, IE.eval, RealRAM.Op2.eval, hr', xm, p2, zk, tzZ, Matrix.mulVec, dotProduct]
      push_cast; ring
  refine XV.seq (XV.mono (K := d * (7 + 6) + 3) (XV.mapE hL (z := oT + 1) (t := oT + 40)
    (e := ieZ (aT + 2) (aT + 7) (oT + 5) (rT + 4)) (aB := aT + 7) (nr := rT + 4) (nst := rT) (nk := rT + 5) (nn := rD)
    (none := rT) (E := 2 * E + d) (N := d) (base := 0) (st := 1) (F := fun k => vext (tzZ Xp Y P2) k)
    (by simp only [ieZ, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega) (by omega)
    (by simp only [ieZ, IE.scr]; omega) (by rw [Env.setNat_sc, F1.2.1 _ (by omega), eZ]) (hNA 7 (by norm_num))
    (hNN 4 (by norm_num)) (hNN 0 (by norm_num)) (hNN 5 (by norm_num)) hndN (hNN 0 (by norm_num))
    (by simp only [rD, rT]; decide) (by omega) (by omega)
    (by rw [nat_setNat_ne _ (by simp only [rD, rT]; omega), F1.1 _ (by simp only [rD, rT]; omega), hσd])
    (by rw [nat_setNat_ne _ (by omega), F1.1 _ (by omega), hσ1]) (by rw [nat_setNat_eq])
    (by rw [nat_setNat_ne _ (by omega), F1.1 _ (by omega), hσ1]) one_pos (fun k hk => by simpa using hcell k hk)
    (by omega) (by omega) (by have := hL.1; omega)
    (by simp only [ieZ, IE.top, IE.mag]; omega)
    (fun k hk σ' F' d' hk' hr => by rw [vext_lt _ hk]; exact F2 k hk σ' F' d' hk' hr)) (by simp)
    (fun _ h => h)) fun σ3 ⟨z3, _, dr3, F3⟩ => ?_
  have G3 : FrameA zS zN (zA d) σ σ3 := G2.trans (F3.mono (fun y h => by simp only [zS]; omega)
    (fun j h => by simp only [zN]; omega) (fun b k h => by simp only [zA]; omega))
  have zz : ∀ l : Fin d, σ3.arr (aT + 7) l = tzZ Xp Y P2 l := fun l => by
    have := z3 l l.2; simp only [zero_add, one_mul] at this; rw [this, vext_lt _ l.2]
  -- the rounding
  refine XV.seq (XV.nconst hL (hNN 4 (by norm_num)) 0 (by positivity)) fun σ4 e4 => ?_
  subst e4
  have G4 : FrameA zS zN (zA d) σ (σ3.setNat (rT + 4) 0) := G3.setNat (by simp only [zN]; omega) _
  have bz : ∀ i, |tzZ Xp Y P2 i| ≤ 2 ^ (2 * E + d + 1) := abs_tzZ_le bX1 bX2 bY bP2
  have F4 : ∀ k (hk : k < d), ∀ σ' : Env d, FrameA (fun y => oT + 40 ≤ y) (fun j => j = rT + 5 ∨ j = rT + 4)
      (fun b c' => b = aT + 18 ∧ 0 ≤ c' ∧ c' < 0 + 1 * k) (σ3.setNat (rT + 4) 0) σ' →
      σ'.draws = (σ3.setNat (rT + 4) 0).draws → σ'.nat (rT + 5) = k → σ'.nat (rT + 4) = 0 + 1 * k →
      (ieRnd (aT + 7) sCE sC2K (rT + 4)).Leaves F σ' ∧
        (ieRnd (aT + 7) sCE sC2K (rT + 4)).eval σ' = ((rndZ Es K (tzZ Xp Y P2)) ⟨k, hk⟩ : ℤ) := by
    intro k hk σ' F' _ _ hr
    have Fσ := G4.trans (F'.mono (fun y h => by simp only [zS]; omega) (fun j h => by simp only [zN]; omega)
      (fun b k' h => by simp only [zA]; omega))
    have hr' : σ'.nat (rT + 4) = k := by omega
    have zk : σ'.arr (aT + 7) k = tzZ Xp Y P2 ⟨k, hk⟩ := by
      rw [F'.2.2.1 _ _ (by omega), Env.setNat_arr, zz ⟨k, hk⟩]
    have ce : σ'.sc sCE = ((2 ^ Es : ℤ) : ℝ) := by rw [Fσ.2.1 _ (by simp only [zS, sCE, oT]; omega), eCE]
    have ck : σ'.sc sC2K = ((2 ^ K : ℤ) : ℝ) := by rw [Fσ.2.1 _ (by simp only [zS, sC2K, oT]; omega), eCK]
    have bzk : |tzZ Xp Y P2 ⟨k, hk⟩| ≤ 2 ^ F := abs_le_mono (bz _) hF
    refine ⟨?_, ?_⟩
    · simp only [ieRnd, IE.Leaves]
      have lz : σ'.nat (rT + 4) < asz d ∧ ∃ v : ℤ, σ'.arr (aT + 7) (σ'.nat (rT + 4)) = v ∧ |v| ≤ 2 ^ F :=
        ⟨by rw [hr']; exact hcell k hk, _, by rw [hr', zk], bzk⟩
      have lE : ∃ v : ℤ, σ'.sc sCE = v ∧ |v| ≤ 2 ^ F :=
        ⟨_, ce, by rw [abs_of_pos (by positivity)]; exact pow_le_pow_right₀ (by norm_num) hEs⟩
      have lK : ∃ v : ℤ, σ'.sc sC2K = v ∧ |v| ≤ 2 ^ F :=
        ⟨_, ck, by rw [abs_of_pos (by positivity)]; exact pow_le_pow_right₀ (by norm_num) hK⟩
      exact ⟨⟨⟨⟨lz, lz⟩, lE⟩, lK⟩, lK, lK⟩
    · have ha : (IE.op .add (.op .mul (.op .add (.arr (aT + 7) (rT + 4)) (.arr (aT + 7) (rT + 4))) (.sc sCE))
          (.sc sC2K)).eval σ' = ((2 * tzZ Xp Y P2 ⟨k, hk⟩ * 2 ^ Es + 2 ^ K : ℤ) : ℝ) := by
        simp only [IE.eval, RealRAM.Op2.eval, hr', zk, ce, ck]; push_cast; ring
      have hb : (IE.op .add (.sc sC2K) (.sc sC2K)).eval σ' = ((2 * 2 ^ K : ℤ) : ℝ) := by
        simp only [IE.eval, RealRAM.Op2.eval, ck]; push_cast; ring
      simp only [ieRnd]
      rw [IE.eval, ha, hb, Int.floor_intCast, Int.floor_intCast]
      rfl
  refine XV.mono (K := d * (13 + 6) + 3) (XV.mapE hL (z := oT + 1) (t := oT + 40)
    (e := ieRnd (aT + 7) sCE sC2K (rT + 4)) (aB := aT + 18) (nr := rT + 4) (nst := rT) (nk := rT + 5) (nn := rD)
    (none := rT) (E := F) (N := d) (base := 0) (st := 1) (F := fun k => vext (rndZ Es K (tzZ Xp Y P2)) k)
    (by simp only [ieRnd, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and, sCE, sC2K, oT]; omega)
    (by omega) (by simp only [ieRnd, IE.scr]; omega)
    (by rw [Env.setNat_sc, G3.2.1 _ (by simp only [zS]; omega), eZ]) (hNA 18 (by norm_num))
    (hNN 4 (by norm_num)) (hNN 0 (by norm_num)) (hNN 5 (by norm_num)) hndN (hNN 0 (by norm_num))
    (by simp only [rD, rT]; decide) (by omega) (by omega)
    (by rw [nat_setNat_ne _ (by simp only [rD, rT]; omega), G3.1 _ (by simp only [zN, rD, rT]; omega), hσd])
    (by rw [nat_setNat_ne _ (by omega), G3.1 _ (by simp only [zN]; omega), hσ1]) (by rw [nat_setNat_eq])
    (by rw [nat_setNat_ne _ (by omega), G3.1 _ (by simp only [zN]; omega), hσ1]) one_pos
    (fun k hk => by simpa using hcell k hk) (by omega) (by omega) (by have := hL.1; omega)
    (by simp only [ieRnd, IE.top, IE.mag]; omega)
    (fun k hk σ' F' d' hk' hr => by rw [vext_lt _ hk]; exact F4 k hk σ' F' d' hk' hr)) (by simp)
    fun σ5 ⟨z5, _, dr5, F5⟩ => ⟨fun l => by
      rw [F5.2.2.1 _ _ (by omega), Env.setNat_arr, zz l], fun l => by
      have := z5 l l.2; simp only [zero_add, one_mul] at this; rw [this, vext_lt _ l.2],
      by rw [dr5, Env.setNat_draws, dr3, Env.setNat_draws, dr1],
      G4.trans (F5.mono (fun y h => by simp only [zS]; omega) (fun j h => by simp only [zN]; omega)
        (fun b k h => by simp only [zA]; omega))⟩

end AdversarialBco.Unified.ProgO.TriO
