/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLR1
public import AdversarialBco.Bit.Transfer.XTriRow
public import AdversarialBco.Bit.Transfer.XBLR5

@[expose] public section

/-!
# BL's round on the machine, R2 PLAYPT in mode `run`, the point `X'`

In mode `run` with the state `st` (`StRep`: `μ' = μ̂/D_μ`, `A' = Â/2^p`, `λ' = λ̂/2^pF`) and the draw `ξ = Γ/G`
(`G = 2^(2 p_B)`, R1), the round computes, over the integers,

* `w = Â Γ` (`A' ξ = w/(2^p G)`, kept for R8 and R13), in the array `aWv`;
* `X̂_j = μ̂_j 2^pF 2^p G + (2^pF - λ̂) w_j D_μ` and `D_X = D_μ 2^pF 2^p G`, so that `X' = X̂/D_X` (`XQ`), in the
  array `aXh` and the slot `sDX`;
* `y = Â_S X̂` (`A_S X' = y/(D_S D_X)`), in the array `aYv`, read by the gauge and the play.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

/-! ## The round's cells for R2 -/

abbrev rD1 : ℕ := 22
abbrev rK : ℕ := 23
abbrev rI : ℕ := 24
abbrev rTT : ℕ := 25
abbrev rjj : ℕ := 26
abbrev ri : ℕ := 27
abbrev rr : ℕ := 28
abbrev rk : ℕ := 29

abbrev sDX : ℕ := 27
abbrev sPtN : ℕ := 28
abbrev sPtD : ℕ := 29
abbrev sBN : ℕ := 30
abbrev sBD : ℕ := 31
abbrev sGN : ℕ := 32
abbrev sGD : ℕ := 33
abbrev sC1 : ℕ := 34
abbrev sC2 : ℕ := 35
abbrev sTa : ℕ := 36
abbrev sRB : ℕ := 37
abbrev sRD : ℕ := 38
abbrev sRT : ℕ := 39
abbrev sRN : ℕ := 40
abbrev sRQ : ℕ := 41
abbrev sAcc : ℕ := 43
/-- The scratch of the round's expressions. -/
abbrev tR : ℕ := 256

abbrev aWv : ℕ := 25
abbrev aXh : ℕ := 26
abbrev aYv : ℕ := 27
abbrev aPl : ℕ := 28
abbrev aRw : ℕ := 29

/-- The cells R2 changes. -/
def SR2 (y : ℕ) : Prop := (sZeta < y ∧ y < 64) ∨ tR ≤ y
def NR2 (j : ℕ) : Prop := rD2 < j ∧ j < 32
def AR2 (a _k : ℕ) : Prop := aGam < a ∧ a < 32

/-- `omega` after unfolding the names of BL's cells and the round's. -/
macro "romega" : tactic => `(tactic| ((try simp only [rD, rM, rMk, rOne, rP, rPF, rNb, rB, nN0, sZ, sMode, sFirst,
  sN, s2p, s2pF, s2g, sNe, sLam, sRint, s2eh, sEps, sLamb, sEta, sRho, sKapc, sNu, sR, sSb, sW, sA0, sB0, sDS, sDmu,
  sK, sL, nSP, nS0, aMuS, aAS, aC, aMu, aA, aB, ab, aG, nAP, nA0, sEl, aEH, aEg, aEP, aEf, oE, rEE, aWE, rJ, rT, rD2,
  sZeta, aGam, oBM, rD1, rK, rI, rTT, rjj, ri, rr, rk, sDX, sPtN, sPtD, sBN, sBD, sGN, sGD, sC1, sC2, sTa, sRB, sRD,
  sRT, sRN, sRQ, sAcc, tR, aWv, aXh, aYv, aPl, aRw, SR2, NR2, AR2] at *) <;> omega))

/-! ## Bounds -/

theorem dot_abs_le {x y : Fin d → ℤ} {a b c : ℕ} (bx : ∀ k, |x k| ≤ 2 ^ a) (by' : ∀ k, |y k| ≤ 2 ^ b)
    (hd : d ≤ 2 ^ c) : |x ⬝ᵥ y| ≤ 2 ^ (a + b + c) := by
  unfold dotProduct
  calc |∑ k, x k * y k| ≤ ∑ k, |x k * y k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin d, (2 ^ a * 2 ^ b : ℤ) := Finset.sum_le_sum fun k _ => by
        rw [abs_mul]; exact mul_le_mul (bx k) (by' k) (abs_nonneg _) (by positivity)
    _ = d * (2 ^ a * 2 ^ b) := by simp
    _ ≤ 2 ^ c * (2 ^ a * 2 ^ b) := by gcongr; exact_mod_cast hd
    _ = 2 ^ (a + b + c) := by ring

theorem mulVec_abs_le {M : Matrix (Fin d) (Fin d) ℤ} {x : Fin d → ℤ} {a b c : ℕ} (bM : ∀ i k, |M i k| ≤ 2 ^ a)
    (bx : ∀ k, |x k| ≤ 2 ^ b) (hd : d ≤ 2 ^ c) (i : Fin d) : |(M *ᵥ x) i| ≤ 2 ^ (a + b + c) :=
  dot_abs_le (fun k => bM i k) bx hd

theorem abs_le_pow_mono {x : ℤ} {a b : ℕ} (h : |x| ≤ 2 ^ a) (hab : a ≤ b) : |x| ≤ 2 ^ b :=
  h.trans (pow_le_pow_right₀ (by norm_num) hab)

/-! ## The point `X'` over the integers -/

/-- `X̂_j = μ̂_j 2^pF 2^p G + (2^pF - λ̂) (Â Γ)_j D_μ`. -/
def xhI (mh : Fin d → ℤ) (Ah : Matrix (Fin d) (Fin d) ℤ) (Γ : Fin d → ℤ) (Dm PF P G lh : ℤ) : Fin d → ℤ :=
  fun j => mh j * PF * P * G + (PF - lh) * (Ah *ᵥ Γ) j * Dm

theorem xhI_abs {mh : Fin d → ℤ} {Ah : Matrix (Fin d) (Fin d) ℤ} {Γ : Fin d → ℤ} {Dm PF P G lh : ℤ} {E : ℕ}
    (bA : ∀ i k, |Ah i k| ≤ 2 ^ E) (bG : ∀ k, |Γ k| ≤ 2 ^ E) (bmu : ∀ k, |mh k| ≤ 2 ^ E) (bDm : |Dm| ≤ 2 ^ E)
    (bPF : |PF| ≤ 2 ^ E) (bP : |P| ≤ 2 ^ E) (bGs : |G| ≤ 2 ^ E) (blh : |lh| ≤ 2 ^ E) (hdE : d ≤ 2 ^ E)
    (j : Fin d) : |xhI mh Ah Γ Dm PF P G lh j| ≤ 2 ^ (5 * E + 2) := by
  have hw := mulVec_abs_le bA bG hdE j
  have h1 : |mh j * PF * P * G| ≤ 2 ^ (4 * E) := by
    rw [abs_mul, abs_mul, abs_mul]
    calc |mh j| * |PF| * |P| * |G| ≤ 2 ^ E * 2 ^ E * 2 ^ E * 2 ^ E := by gcongr; exact bmu j
      _ = 2 ^ (4 * E) := by ring
  have h2 : |(PF - lh) * (Ah *ᵥ Γ) j * Dm| ≤ 2 ^ (5 * E + 1) := by
    rw [abs_mul, abs_mul]
    have hs : |PF - lh| ≤ 2 ^ (E + 1) := (abs_sub _ _).trans (by rw [pow_succ]; linarith)
    calc |PF - lh| * |(Ah *ᵥ Γ) j| * |Dm| ≤ 2 ^ (E + 1) * 2 ^ (E + E + E) * 2 ^ E := by gcongr
      _ = 2 ^ (5 * E + 1) := by ring
  unfold xhI
  calc |mh j * PF * P * G + (PF - lh) * (Ah *ᵥ Γ) j * Dm|
      ≤ |mh j * PF * P * G| + |(PF - lh) * (Ah *ᵥ Γ) j * Dm| := abs_add_le _ _
    _ ≤ 2 ^ (5 * E + 1) + 2 ^ (5 * E + 1) := by
        gcongr
        exact h1.trans (pow_le_pow_right₀ (by norm_num) (by omega))
    _ = 2 ^ (5 * E + 2) := by ring

/-! ## The code -/

/-- `D_X = D_μ 2^pF 2^p G`. -/
def ieDX : IE := .op .mul (.op .mul (.op .mul (.sc sDmu) (.sc s2pF)) (.sc s2p)) (.sc s2g)

/-- `X̂_k`, `k` in the register `rk`. -/
def ieXh : IE := .op .add (.op .mul (.op .mul (.op .mul (.arr aMu rk) (.sc s2pF)) (.sc s2p)) (.sc s2g))
  (.op .mul (.op .mul (.op .sub (.sc s2pF) (.sc sLamb)) (.arr aWv rk)) (.sc sDmu))

theorem ieDX_facts : ieDX.units = 7 ∧ ieDX.scr = 6 ∧ topL ieDX = (4, 0) := ⟨rfl, rfl, by
  simp [ieDX, topL, magL]⟩

theorem ieXh_facts : ieXh.units = 17 ∧ ieXh.scr = 14 ∧ topL ieXh = (4, 2) := ⟨rfl, rfl, by
  simp [ieXh, topL, magL]⟩

/-- R2, the point: `w := Â Γ`, `D_X`, `X̂`, `y := Â_S X̂`. -/
def xR2x (L : Layout) : XCmd :=
  .seq (xmatvec L sZ sAcc tR aA aGam aWv ri rr rk rD rOne)
  (.seq (ieDX.code L sZ sDX tR)
  (.seq (.prim (.frag (.nconst rr 0)))
  (.seq (xmapE L sZ tR ieXh aXh rr rOne rk rD rOne)
    (xmatvec L sZ sAcc tR aAS aXh aYv ri rr rk rD rOne))))

/-- The units of `xR2x`. -/
def r2xUnits (d : ℕ) : ℕ := (d * (d * 10 + 9) + 4) + (7 + (1 + ((d * (17 + 6) + 3) + (d * (d * 10 + 9) + 4))))

set_option maxHeartbeats 2000000 in
/-- **R2, the point `X'`**: `w = Â Γ`, `D_X`, `X̂`, `y = Â_S X̂`, every input below `2^E`, `d ≤ 2^E`. -/
theorem XV.r2x {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {σ : Env d} {E : ℕ}
    {Ah ASh : Matrix (Fin d) (Fin d) ℤ} {Γ mh : Fin d → ℤ} {Dm PF P G lh : ℤ}
    (hD : σ.nat rD = d) (h1 : σ.nat rOne = 1) (hz : σ.sc sZ = 0)
    (hA : ∀ i k : Fin d, σ.arr aA (d * i + k) = Ah i k) (hAS : ∀ i k : Fin d, σ.arr aAS (d * i + k) = ASh i k)
    (hG : ∀ k : Fin d, σ.arr aGam k = Γ k) (hmu : ∀ k : Fin d, σ.arr aMu k = mh k)
    (hDm : σ.sc sDmu = Dm) (hPF : σ.sc s2pF = PF) (hP : σ.sc s2p = P) (hGs : σ.sc s2g = G)
    (hlh : σ.sc sLamb = lh)
    (bA : ∀ i k, |Ah i k| ≤ 2 ^ E) (bAS : ∀ i k, |ASh i k| ≤ 2 ^ E) (bG : ∀ k, |Γ k| ≤ 2 ^ E)
    (bmu : ∀ k, |mh k| ≤ 2 ^ E) (bDm : |Dm| ≤ 2 ^ E) (bPF : |PF| ≤ 2 ^ E) (bP : |P| ≤ 2 ^ E)
    (bGs : |G| ≤ 2 ^ E) (blh : |lh| ≤ 2 ^ E) (hdE : d ≤ 2 ^ E) (hℓ : 12 * E + 6 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xR2x L) σ (r2xUnits d) (fun σ' =>
      (∀ i : Fin d, σ'.arr aWv i = (Ah *ᵥ Γ) i) ∧ σ'.sc sDX = ((Dm * PF * P * G : ℤ) : ℝ) ∧
      (∀ k : Fin d, σ'.arr aXh k = xhI mh Ah Γ Dm PF P G lh k) ∧
      (∀ i : Fin d, σ'.arr aYv i = (ASh *ᵥ xhI mh Ah Γ Dm PF P G lh) i) ∧ σ'.draws = σ.draws ∧
      FrameA SR2 NR2 AR2 σ σ') := by
  obtain ⟨hS, hN, hAr⟩ := hlay
  have hda := asz_lt hL (a := 0) (by romega)
  have hdl : ∀ k < d, k < asz d := fun k hk => by unfold asz; nlinarith
  have hdℓ : (d : ℤ) ≤ 2 ^ E := by exact_mod_cast hdE
  have p2 : ∀ {a b : ℕ}, a ≤ b → (2 : ℤ) ^ a ≤ 2 ^ b := fun h => pow_le_pow_right₀ (by norm_num) h
  have hdm : ∀ a : ℕ, (d : ℤ) * 2 ^ a ≤ 2 ^ (E + a) := fun a => by
    rw [pow_add]; exact mul_le_mul_of_nonneg_right hdℓ (by positivity)
  have hlt : ∀ {a : ℕ}, a < ℓ → (d : ℤ) * 2 ^ (2 * a) < 2 ^ ℓ → (d : ℕ) * 2 ^ (2 * a) < 2 ^ ℓ := fun _ h => by
    exact_mod_cast h
  -- step 1: `w := Â Γ`
  refine XV.seq (XV.matvec (E := E) (M := Ah) (x := Γ) hL (z := sZ) (r := sAcc) (t := tR) (aM := aA) (ax := aGam)
    (ay := aWv) (ni := ri) (nr := rr) (nk := rk) (nd := rD) (none := rOne) (by romega) (by romega) (by romega)
    (by romega) hz (by romega) (by romega) (by romega) (by romega) (by romega) (by romega) (by romega) (by romega)
    (by romega) (by romega) (by decide) hD h1 hA hG bA bG (by omega) ?_) fun σ1 ⟨w1, d1, F1⟩ => ?_
  · refine hlt (a := E) (by omega) (lt_of_le_of_lt (hdm _) ?_)
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  -- step 2: `D_X`
  have q1 : ∀ y, ¬ (y = sAcc ∨ tR ≤ y) → σ1.sc y = σ.sc y := F1.2.1
  have a1 : ∀ b k, b ≠ aWv → σ1.arr b k = σ.arr b k := fun b k h => F1.2.2.1 b k fun h' => h h'.1
  refine XV.seq (XV.ieRun (E := E) (v := Dm * PF * P * G) hL (z := sZ) (x := sDX) (t := tR) (e := ieDX)
    (by simp [ieDX, IE.WF]; romega) (by romega) (by romega) (by rw [ieDX_facts.2.1]; romega)
    (by rw [q1 _ (by romega), hz])
    ⟨⟨⟨⟨Dm, by rw [q1 _ (by romega), hDm], bDm⟩, ⟨PF, by rw [q1 _ (by romega), hPF], bPF⟩⟩,
      ⟨P, by rw [q1 _ (by romega), hP], bP⟩⟩, ⟨G, by rw [q1 _ (by romega), hGs], bGs⟩⟩
    (top_lt ieDX_facts.2.2 (by omega))
    (by simp only [ieDX, IE.eval, RealRAM.Op2.eval, q1 _ (by romega : ¬ (sDmu = sAcc ∨ tR ≤ sDmu)),
      q1 _ (by romega : ¬ (s2pF = sAcc ∨ tR ≤ s2pF)), q1 _ (by romega : ¬ (s2p = sAcc ∨ tR ≤ s2p)),
      q1 _ (by romega : ¬ (s2g = sAcc ∨ tR ≤ s2g)), hDm, hPF, hP, hGs]; push_cast; ring))
    fun σ2 ⟨v2, _, d2, P2⟩ => ?_
  have q2 : ∀ y, ¬ (y = sDX ∨ tR ≤ y) → σ2.sc y = σ1.sc y := P2.2.1
  -- step 3: `rr := 0`
  refine XV.seq (XV.nconst hL (σ := σ2) (i := rr) (by romega) 0 (by positivity)) fun σ3 e3 => ?_
  subst e3
  -- step 4: `X̂`
  set xh := xhI mh Ah Γ Dm PF P G lh with hxh
  have bxh : ∀ k, |xh k| ≤ 2 ^ (5 * E + 2) := xhI_abs bA bG bmu bDm bPF bP bGs blh hdE
  have s3 : ∀ y, ¬ (y = sAcc ∨ tR ≤ y) → ¬ (y = sDX ∨ tR ≤ y) → (σ2.setNat rr 0).sc y = σ.sc y :=
    fun y h h' => by rw [Env.setNat_sc, q2 y h', q1 y h]
  have a3 : ∀ b k, b ≠ aWv → (σ2.setNat rr 0).arr b k = σ.arr b k := fun b k h => by
    rw [Env.setNat_arr, P2.2.2.1, a1 b k h]
  have w3 : ∀ k : Fin d, (σ2.setNat rr 0).arr aWv k = (Ah *ᵥ Γ) k := fun k => by
    rw [Env.setNat_arr, P2.2.2.1, w1 k]
  refine XV.seq (XV.mapE (E := 3 * E) (N := d) (base := 0) (st := 1) (F := vext xh) hL (z := sZ) (t := tR)
    (aB := aXh) (nr := rr) (nst := rOne) (nk := rk) (nn := rD) (none := rOne) (e := ieXh)
    (by simp [ieXh, IE.WF]; romega) (by romega) (by rw [ieXh_facts.2.1]; romega)
    (by rw [s3 _ (by romega) (by romega), hz]) (by romega) (by romega) (by romega) (by romega) (by romega)
    (by romega) (by decide) (by decide) (by decide)
    (by rw [Env.setNat_nat, ite_eq_right (by romega), P2.1 _ (by simp), F1.1 _ (by romega), hD])
    (by rw [Env.setNat_nat, ite_eq_right (by romega), P2.1 _ (by simp), F1.1 _ (by romega), h1])
    (by simp) (by rw [Env.setNat_nat, ite_eq_right (by romega), P2.1 _ (by simp), F1.1 _ (by romega), h1]) one_pos
    (fun k hk => by simpa using hdl k hk) (by unfold asz at hda; nlinarith) (by unfold asz at hda; nlinarith)
    (by have := hL.1; omega) (top_lt ieXh_facts.2.2 (by omega)) ?_) fun σ4 ⟨x4, r4, d4, F4⟩ => ?_
  · intro k hk σ' F' d' hk' hr'
    have sc' : ∀ y, ¬ (y = sAcc ∨ tR ≤ y) → ¬ (y = sDX ∨ tR ≤ y) → σ'.sc y = σ.sc y :=
      fun y h h' => by rw [F'.2.1 y (by romega), s3 y h h']
    have ar' : ∀ b, b ≠ aWv → b ≠ aXh → σ'.arr b k = σ.arr b k := fun b h h' => by
      rw [F'.2.2.1 b k fun h'' => h' h''.1, a3 b k h]
    have wv' : σ'.arr aWv k = (Ah *ᵥ Γ) ⟨k, hk⟩ := by
      rw [F'.2.2.1 aWv k fun h'' => absurd h''.1 (by romega)]; exact w3 ⟨k, hk⟩
    have mu' : σ'.arr aMu k = mh ⟨k, hk⟩ := by rw [ar' aMu (by romega) (by romega)]; exact hmu ⟨k, hk⟩
    have e3 : ∀ {x : ℤ}, |x| ≤ 2 ^ E → |x| ≤ 2 ^ (3 * E) := fun h => abs_le_pow_mono h (by omega)
    refine ⟨⟨⟨⟨⟨⟨by rw [hk']; exact hdl k hk, mh ⟨k, hk⟩, by rw [hk', mu'], e3 (bmu _)⟩,
      PF, by rw [sc' _ (by romega) (by romega), hPF], e3 bPF⟩, P, by rw [sc' _ (by romega) (by romega), hP], e3 bP⟩,
      G, by rw [sc' _ (by romega) (by romega), hGs], e3 bGs⟩,
      ⟨⟨⟨PF, by rw [sc' _ (by romega) (by romega), hPF], e3 bPF⟩, lh, by rw [sc' _ (by romega) (by romega), hlh],
        e3 blh⟩, by rw [hk']; exact hdl k hk, (Ah *ᵥ Γ) ⟨k, hk⟩, by rw [hk', wv'],
        abs_le_pow_mono (mulVec_abs_le bA bG hdE _) (by omega)⟩,
      Dm, by rw [sc' _ (by romega) (by romega), hDm], e3 bDm⟩, ?_⟩
    simp only [ieXh, IE.eval, RealRAM.Op2.eval, hk', mu', wv', sc' _ (by romega : ¬ (s2pF = sAcc ∨ tR ≤ s2pF))
      (by romega), sc' _ (by romega : ¬ (s2p = sAcc ∨ tR ≤ s2p)) (by romega),
      sc' _ (by romega : ¬ (s2g = sAcc ∨ tR ≤ s2g)) (by romega),
      sc' _ (by romega : ¬ (sLamb = sAcc ∨ tR ≤ sLamb)) (by romega),
      sc' _ (by romega : ¬ (sDmu = sAcc ∨ tR ≤ sDmu)) (by romega), hPF, hP, hGs, hlh, hDm]
    rw [vext_lt _ hk, hxh]; simp only [xhI]
    push_cast; ring
  -- step 5: `y := Â_S X̂`
  have s4 : ∀ y, ¬ (y = sAcc ∨ tR ≤ y) → ¬ (y = sDX ∨ tR ≤ y) → σ4.sc y = σ.sc y :=
    fun y h h' => by rw [F4.2.1 y (by romega), s3 y h h']
  have n4 : ∀ j, j ≠ rk → j ≠ rr → j ≠ ri → σ4.nat j = σ.nat j := fun j h h' h'' => by
    rw [F4.1 j (by tauto), Env.setNat_nat, ite_eq_right h', P2.1 j (by simp), F1.1 j (by tauto)]
  have xh4 : ∀ k : Fin d, σ4.arr aXh k = xh k := fun k => by
    have := x4 k k.2
    rw [zero_add, one_mul, vext_lt _ k.2] at this
    exact this
  refine XV.mono (XV.matvec (X := X) (ℓa := ℓa) (ℓ := ℓ) (σ := σ4) (E := 5 * E + 2) (M := ASh) (x := xh) hL (z := sZ) (r := sAcc) (t := tR) (aM := aAS)
    (ax := aXh) (ay := aYv) (ni := ri) (nr := rr) (nk := rk) (nd := rD) (none := rOne) (by romega) (by romega)
    (by romega) (by romega) (by rw [s4 _ (by romega) (by romega), hz]) (by romega) (by romega) (by romega)
    (by romega) (by romega) (by romega) (by romega) (by romega) (by romega) (by romega) (by decide)
    (by rw [n4 _ (by romega) (by romega) (by romega), hD]) (by rw [n4 _ (by romega) (by romega) (by romega), h1])
    (fun i k => by
      rw [F4.2.2.1 _ _ (fun h => absurd h.1 (by romega)), Env.setNat_arr, P2.2.2.1, a1 _ _ (by romega)]
      exact hAS i k)
    xh4 (fun i k => abs_le_pow_mono (bAS i k) (by omega)) bxh (by omega) ?_) le_rfl fun σ5 ⟨y5, d5, F5⟩ => ?_
  · refine hlt (a := 5 * E + 2) (by omega) (lt_of_le_of_lt (hdm _) ?_)
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  have s5 : ∀ y, ¬ (y = sAcc ∨ tR ≤ y) → σ5.sc y = σ4.sc y := F5.2.1
  refine ⟨fun i => ?_, ?_, fun k => ?_, y5, ?_, ?_⟩
  · rw [F5.2.2.1 _ _ (fun h => absurd h.1 (by romega)), F4.2.2.1 _ _ (fun h => absurd h.1 (by romega)),
      Env.setNat_arr, P2.2.2.1, w1 i]
  · rw [s5 _ (by romega), F4.2.1 _ (by romega), Env.setNat_sc, v2]
  · rw [F5.2.2.1 _ _ (fun h => absurd h.1 (by romega)), xh4 k]
  · rw [d5, d4, Env.setNat_draws, d2, d1]
  · have G1 : FrameA SR2 NR2 AR2 σ σ1 := F1.mono (fun y h => by romega) (fun j h => by romega)
      (fun b k h => by romega)
    have G2 : FrameA SR2 NR2 AR2 σ1 σ2 :=
      (FrameA.ofP P2).mono (fun y h => by romega) (fun j h => h.elim) (fun b k h => h)
    have G3 : FrameA SR2 NR2 AR2 σ2 (σ2.setNat rr 0) := (FrameA.refl _ _ _ σ2).setNat (by romega) 0
    have G4 : FrameA SR2 NR2 AR2 (σ2.setNat rr 0) σ4 := F4.mono (fun y h => by romega) (fun j h => by romega)
      (fun b k h => by romega)
    have G5 : FrameA SR2 NR2 AR2 σ4 σ5 := F5.mono (fun y h => by romega) (fun j h => by romega)
      (fun b k h => by romega)
    exact (((G1.trans G2).trans G3).trans G4).trans G5

end AdversarialBco.Bit.Transfer.BLM
