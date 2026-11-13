/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLCall
public import AdversarialBco.Bit.Transfer.XBmRun
public import AdversarialBco.Bit.Transfer.XVec

@[expose] public section

/-!
# BL's round on the machine, R1 DRAW

Every round, in every mode, runs Procedure BM-INT (`xbmint`) on the `nBlk d` blocks of `2B` coins of the round
(`Sched.blkStart`): block `j` gives the two integers `Γ_{2j}`, `Γ_{2j+1}` (`gsSpec`), kept in the array `aGam` for the
coordinates below `d`, and block `(d + 1)/2` gives `Γ_ζ`, its first integer, kept in the slot `sZeta`. Then
`draw = (Γ/2^(2 p_B), Γ_ζ/2^(2 p_B)/2)` (`draw_eq`), and the count of draws is the start of the next round. Running the
draws in every mode keeps the count of draws on the schedule without a case on the mode.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP

variable {d : ℕ}

/-! ## The round's cells for R1 -/

/-- The block counter, an index, `d + 2`. -/
abbrev rJ : ℕ := 19
abbrev rT : ℕ := 20
abbrev rD2 : ℕ := 21

/-- `Γ_ζ`. -/
abbrev sZeta : ℕ := 26

/-- `Γ`, coordinates `0, ..., d - 1`. -/
abbrev aGam : ℕ := 24

/-- The slots of `xbmint`: `oBM, ..., oBM + 42`. -/
abbrev oBM : ℕ := 704

/-! ## The integers of the draw -/

/-- `Γ_i`: coordinate `i` of the draw times `2^(2 p_B)`. -/
def gamI (cs : ℕ → Bool) (K0 B d t i : ℕ) : ℤ :=
  if i % 2 = 0 then (gsSpec B (blkUW cs K0 B d t (i / 2)).1 (blkUW cs K0 B d t (i / 2)).2).1
  else (gsSpec B (blkUW cs K0 B d t (i / 2)).1 (blkUW cs K0 B d t (i / 2)).2).2

/-- `Γ_ζ`: the dither times `2^(2 p_B + 1)`. -/
def zetI (cs : ℕ → Bool) (K0 B d t : ℕ) : ℤ :=
  (gsSpec B (blkUW cs K0 B d t ((d + 1) / 2)).1 (blkUW cs K0 B d t ((d + 1) / 2)).2).1

theorem draw_eq (cs : ℕ → Bool) (K0 B t : ℕ) :
    draw cs K0 B d t = (fun i : Fin d => (gamI cs K0 B d t i : ℚ) / 2 ^ (2 * gsm_prec B),
      (zetI cs K0 B d t : ℚ) / 2 ^ (2 * gsm_prec B) / 2) := by
  unfold draw gamI zetI gOut
  congr 1
  funext i
  split_ifs <;> rfl

/-- The integers of BM-INT are below `2^(4 p_B)`. -/
theorem gsSpec_abs_le (B U W : ℕ) (hU : U < 2 ^ B) :
    |(gsSpec B U W).1| ≤ 2 ^ (4 * gsm_prec B) ∧ |(gsSpec B U W).2| ≤ 2 ^ (4 * gsm_prec B) := by
  obtain ⟨hp4, hpB⟩ := bm_prec B
  obtain ⟨hLL0, hLLb⟩ := bm_LLq_bounds B (2 * gsm_prec B) U hU (by omega)
  set LL := (gsm_LLq B (2 * gsm_prec B) U).toNat with hLLn
  have hLLz : ((LL : ℕ) : ℤ) = gsm_LLq B (2 * gsm_prec B) U := Int.toNat_of_nonneg hLL0
  have hLL3 : LL ≤ 2 ^ (3 * gsm_prec B) := by
    have h1 : LL ≤ B * (2 * gsm_prec B) * 2 ^ (2 * gsm_prec B) := by
      have : ((LL : ℕ) : ℤ) ≤ ((B * (2 * gsm_prec B) * 2 ^ (2 * gsm_prec B) : ℕ) : ℤ) := by
        rw [hLLz]; push_cast; exact hLLb
      exact_mod_cast this
    have h2 : B * (2 * gsm_prec B) ≤ 2 ^ gsm_prec B := by
      have : B * (2 * gsm_prec B) ≤ 2 * B * (2 * gsm_prec B) := Nat.mul_le_mul_right _ (by omega)
      omega
    calc LL ≤ B * (2 * gsm_prec B) * 2 ^ (2 * gsm_prec B) := h1
      _ ≤ 2 ^ gsm_prec B * 2 ^ (2 * gsm_prec B) := Nat.mul_le_mul_right _ h2
      _ = 2 ^ (3 * gsm_prec B) := by rw [← pow_add]; congr 1; omega
  have hR : Nat.sqrt (2 * LL) ≤ 2 ^ (2 * gsm_prec B) := bm_sqrt_le _ _ (by
    calc 2 * LL ≤ 2 * 2 ^ (3 * gsm_prec B) := by omega
      _ = 2 ^ (3 * gsm_prec B + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (2 * (2 * gsm_prec B)) := Nat.pow_le_pow_right (by norm_num) (by omega))
  have hRb : |((Nat.sqrt (2 * LL) : ℕ) : ℤ)| ≤ 2 ^ (2 * gsm_prec B) := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast hR
  obtain ⟨hZ1, hZ2⟩ := bm_prodq_le (gsm_prec B) B ((W + 1) % 2 ^ B)
    (fun k => bm_chainq_le (gsm_prec B) k (by omega)) (B - 1)
  have hpp : (2 : ℤ) ^ (gsm_prec B + (B - 1) + 1) ≤ 2 ^ (2 * gsm_prec B) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have e4 : (2 : ℤ) ^ (4 * gsm_prec B) = 2 ^ (2 * gsm_prec B) * 2 ^ (2 * gsm_prec B) := by
    rw [← pow_add]; congr 1; omega
  unfold gsSpec
  rw [← hLLn, abs_mul, abs_mul, e4]
  exact ⟨mul_le_mul hRb (hZ1.le.trans hpp) (abs_nonneg _) (by positivity),
    mul_le_mul hRb (hZ2.le.trans hpp) (abs_nonneg _) (by positivity)⟩

theorem blkUW_lt (cs : ℕ → Bool) (K0 B d t j : ℕ) : (blkUW cs K0 B d t j).1 < 2 ^ B := by
  obtain ⟨h0, h1⟩ := readCoins_bounds cs (Sched.blkStart d K0 B t j) B
  have : (((BitRAM.readCoins cs (Sched.blkStart d K0 B t j) B).toNat : ℕ) : ℤ) < ((2 ^ B : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg h0]; push_cast; exact h1
  exact_mod_cast this

theorem gamI_abs_le (cs : ℕ → Bool) (K0 B d t i : ℕ) : |gamI cs K0 B d t i| ≤ 2 ^ (4 * gsm_prec B) := by
  have h := gsSpec_abs_le B _ (blkUW cs K0 B d t (i / 2)).2 (blkUW_lt cs K0 B d t (i / 2))
  unfold gamI; split_ifs
  · exact h.1
  · exact h.2

theorem zetI_abs_le (cs : ℕ → Bool) (K0 B d t : ℕ) : |zetI cs K0 B d t| ≤ 2 ^ (4 * gsm_prec B) :=
  (gsSpec_abs_le B _ (blkUW cs K0 B d t ((d + 1) / 2)).2 (blkUW_lt cs K0 B d t _)).1

/-! ## The command -/

/-- One block: BM-INT, then `Γ_{2j}`, `Γ_{2j+1}` into `aGam` (below `d`), `Γ_ζ` into `sZeta` at the block
`(d + 1)/2` (`d ≤ 2j ≤ d + 1`). -/
def xR1body (L : Layout) : XCmd :=
  .seq (xbmint L oBM rB)
  (.seq (.prim (.frag (.nadd rT rJ rJ)))
  (.seq (.ifN rT rD (toX (VL.aset L aGam rT (oBM + 40))) .skip)
  (.seq (.ifN rT rD .skip (.ifN rT rD2 (toX (VL.sop2 L .add sZeta (oBM + 40) sZ)) .skip))
  (.seq (.prim (.frag (.nadd rT rT rOne)))
  (.ifN rT rD (toX (VL.aset L aGam rT (oBM + 41))) .skip)))))

/-- R1: `d + 2` into `rD2`, then the `nBlk d` blocks. -/
def xR1 (L : Layout) : XCmd :=
  .seq (.prim (.frag (.nadd rD2 rD rOne))) (.seq (.prim (.frag (.nadd rD2 rD2 rOne))) (xforN rJ rNb rOne (xR1body L)))

/-- The units of R1. -/
def r1Units (d B : ℕ) : ℕ := Sched.nBlk d * (bmUnits B + 18) + 5

/-- The cells R1 changes. -/
def SR1 (y : ℕ) : Prop := y = sZeta ∨ (oBM ≤ y ∧ y < oBM + 43)
def NR1 (j : ℕ) : Prop := j = rJ ∨ j = rT ∨ j = rD2 ∨ (rB < j ∧ j < rB + 12)
def AR1 (d a k : ℕ) : Prop := a = aGam ∧ k < d

/-! ## Conditionals with one empty branch -/

section Rules

variable {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ}

theorem XV.ifN_skip (hL : LayOK L d ℓa) {i j : ℕ} {c : XCmd} {σ : Env d} {K : ℕ} {P : Env d → Prop}
    (hi : i < L.NN) (hj : j < L.NN) (hvi : σ.nat i < 2 ^ ℓa) (hvj : σ.nat j < 2 ^ ℓa)
    (ht : σ.nat i < σ.nat j → XRunsB L X ℓa ℓ c σ K P) (hf : ¬ σ.nat i < σ.nat j → P σ) :
    XRunsB L X ℓa ℓ (.ifN i j c .skip) σ (K + 2) P := by
  by_cases h : σ.nat i < σ.nat j
  · exact XV.mono (XV.ifN_t hL hi hj hvi hvj h (ht h)) (by omega) fun _ h => h
  · exact XV.mono (XV.ifN_f hL hi hj hvi hvj h (XV.skip σ)) (by omega) fun σ' e => e ▸ hf h

theorem XV.ifN_skipT (hL : LayOK L d ℓa) {i j : ℕ} {c : XCmd} {σ : Env d} {K : ℕ} {P : Env d → Prop}
    (hi : i < L.NN) (hj : j < L.NN) (hvi : σ.nat i < 2 ^ ℓa) (hvj : σ.nat j < 2 ^ ℓa)
    (ht : σ.nat i < σ.nat j → P σ) (hf : ¬ σ.nat i < σ.nat j → XRunsB L X ℓa ℓ c σ K P) :
    XRunsB L X ℓa ℓ (.ifN i j .skip c) σ (K + 2) P := by
  by_cases h : σ.nat i < σ.nat j
  · exact XV.mono (XV.ifN_t hL hi hj hvi hvj h (XV.skip σ)) (by omega) fun σ' e => e ▸ ht h
  · exact XV.mono (XV.ifN_f hL hi hj hvi hvj h (hf h)) (by omega) fun _ h => h

end Rules

/-! ## `omega` on BL's cells -/

/-- `omega` after unfolding the names of BL's cells. -/
macro "lomega" : tactic => `(tactic| ((try simp only [rD, rM, rMk, rOne, rP, rPF, rNb, rB, nN0, sZ, sMode, sFirst, sN,
  s2p, s2pF, s2g, sNe, sLam, sRint, s2eh, sEps, sLamb, sEta, sRho, sKapc, sNu, sR, sSb, sW, sA0, sB0, sDS, sDmu, sK,
  sL, nSP, nS0, aMuS, aAS, aC, aMu, aA, aB, ab, aG, nAP, nA0, sEl, aEH, aEg, aEP, aEf, oE, rEE, aWE, rJ, rT, rD2,
  sZeta, aGam, oBM] at *) <;> omega))

/-! ## One block -/

theorem blkStart_succ (d K0 B t j : ℕ) : Sched.blkStart d K0 B t (j + 1) = Sched.blkStart d K0 B t j + 2 * B := by
  unfold Sched.blkStart; ring

/-- The cells one block changes. -/
def SB1 (d j y : ℕ) : Prop := (y = sZeta ∧ (d + 1) / 2 = j) ∨ (oBM ≤ y ∧ y < oBM + 43)
def NB1 (i : ℕ) : Prop := i = rT ∨ (rB < i ∧ i < rB + 12)
def AB1 (d j a k : ℕ) : Prop := a = aGam ∧ k < d ∧ (k = 2 * j ∨ k = 2 * j + 1)

set_option maxHeartbeats 1000000 in
theorem XV.r1body {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {cs : ℕ → Bool}
    (hX : X.wb.cs = cs) {K0 B t j : ℕ} {σ : Env d} (hB1 : 1 ≤ B) (hB : σ.nat rB = B) (hD : σ.nat rD = d)
    (h1 : σ.nat rOne = 1) (hD2 : σ.nat rD2 = d + 2) (hj : σ.nat rJ = j) (hz : σ.sc sZ = 0)
    (hdr : σ.draws = Sched.blkStart d K0 B t j) (hℓa : 4 * gsm_prec B + 2 < 2 ^ ℓa) (hℓ : 4 * gsm_prec B + 4 ≤ ℓ)
    (hja : 2 * j + 1 < 2 ^ ℓa) (hda : d + 2 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xR1body L) σ (bmUnits B + 15) (fun σ' =>
      σ'.draws = Sched.blkStart d K0 B t (j + 1) ∧
      (∀ i, i < d → (i = 2 * j ∨ i = 2 * j + 1) → σ'.arr aGam i = gamI cs K0 B d t i) ∧
      ((d + 1) / 2 = j → σ'.sc sZeta = zetI cs K0 B d t) ∧
      FrameA (SB1 d j) NB1 (AB1 d j) σ σ') := by
  obtain ⟨hS, hN, hA⟩ := hlay
  have hdl : ∀ k < d, k < asz d := fun k hk => by unfold asz; nlinarith
  set out1 := (gsSpec B (blkUW cs K0 B d t j).1 (blkUW cs K0 B d t j).2).1 with hout1
  set out2 := (gsSpec B (blkUW cs K0 B d t j).1 (blkUW cs K0 B d t j).2).2 with hout2
  have b1 : |out1| ≤ 2 ^ (4 * gsm_prec B) := (gsSpec_abs_le B _ _ (blkUW_lt cs K0 B d t j)).1
  have b2 : |out2| ≤ 2 ^ (4 * gsm_prec B) := (gsSpec_abs_le B _ _ (blkUW_lt cs K0 B d t j)).2
  have hpl : (2 : ℤ) ^ (4 * gsm_prec B) < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) (by omega)
  have bo1 : |(out1 : ℝ)| < 2 ^ ℓ := XV.abs_int_lt (lt_of_le_of_lt b1 hpl)
  have bo2 : |(out2 : ℝ)| < 2 ^ ℓ := XV.abs_int_lt (lt_of_le_of_lt b2 hpl)
  have g1 : gamI cs K0 B d t (2 * j) = out1 := by
    unfold gamI; rw [if_pos (by omega : 2 * j % 2 = 0), show 2 * j / 2 = j by omega]
  have g2 : gamI cs K0 B d t (2 * j + 1) = out2 := by
    unfold gamI; rw [if_neg (by omega), show (2 * j + 1) / 2 = j by omega]
  refine XV.mono (K := bmUnits B + (1 + ((2 + 2) + (((1 + 2) + 2) + (1 + (2 + 2)))))) ?_ (by omega) fun _ h => h
  -- BM-INT
  refine XV.seq (XV.bmint hL (σ := σ) (o := oBM) (on := rB) (by lomega) (by lomega) hB1 hB hℓa hℓ)
    fun σ1 ⟨e40, e41, hd1, F1⟩ => ?_
  have c40 : σ1.sc (oBM + 40) = out1 := by
    rw [e40, hX, hdr]; rfl
  have c41 : σ1.sc (oBM + 41) = out2 := by
    rw [e41, hX, hdr]; rfl
  have FA1 : FrameA (SB1 d j) NB1 (AB1 d j) σ σ1 :=
    FrameA.ofP (F1.mono (fun y hy => Or.inr hy) (fun i hi => Or.inr hi))
  have n1 : ∀ i, ¬ NB1 i → σ1.nat i = σ.nat i := FA1.1
  have j1 : σ1.nat rJ = j := by rw [n1 rJ (by simp only [NB1]; lomega), hj]
  have d1 : σ1.nat rD = d := by rw [n1 rD (by simp only [NB1]; lomega), hD]
  have o1 : σ1.nat rOne = 1 := by rw [n1 rOne (by simp only [NB1]; lomega), h1]
  have dd1 : σ1.nat rD2 = d + 2 := by rw [n1 rD2 (by simp only [NB1]; lomega), hD2]
  have z1 : σ1.sc sZ = 0 := by rw [F1.2.1 sZ (by lomega), hz]
  -- `rT := 2 j`
  refine XV.seq (XV.nadd hL (σ := σ1) (i := rT) (a := rJ) (b := rJ) (by lomega) (by lomega) (by lomega)
    (by rw [j1]; omega) (by rw [j1]; omega)) fun σ2 e2 => ?_
  subst e2
  have FA2 : FrameA (SB1 d j) NB1 (AB1 d j) σ (σ1.setNat rT (σ1.nat rJ + σ1.nat rJ)) := FA1.setNat (Or.inl rfl) _
  have t2 : (σ1.setNat rT (σ1.nat rJ + σ1.nat rJ)).nat rT = 2 * j := by simp [j1]; omega
  have d2 : (σ1.setNat rT (σ1.nat rJ + σ1.nat rJ)).nat rD = d := by simp [d1]
  have dd2 : (σ1.setNat rT (σ1.nat rJ + σ1.nat rJ)).nat rD2 = d + 2 := by simp [dd1]
  have o2 : (σ1.setNat rT (σ1.nat rJ + σ1.nat rJ)).nat rOne = 1 := by simp [o1]
  have c40' : (σ1.setNat rT (σ1.nat rJ + σ1.nat rJ)).sc (oBM + 40) = out1 := by simp [c40]
  have c41' : (σ1.setNat rT (σ1.nat rJ + σ1.nat rJ)).sc (oBM + 41) = out2 := by simp [c41]
  have z2 : (σ1.setNat rT (σ1.nat rJ + σ1.nat rJ)).sc sZ = 0 := by simp [z1]
  have dr2 : (σ1.setNat rT (σ1.nat rJ + σ1.nat rJ)).draws = Sched.blkStart d K0 B t (j + 1) := by
    simp only [Env.setNat_draws]; rw [hd1, hdr, blkStart_succ]
  generalize σ1.setNat rT (σ1.nat rJ + σ1.nat rJ) = σ2 at FA2 t2 d2 dd2 o2 c40' c41' z2 dr2
  -- `Γ_{2j}`
  refine XV.seq (Q₁ := fun σ3 => FrameA (SB1 d j) NB1 (AB1 d j) σ σ3 ∧ σ3.nat = σ2.nat ∧ σ3.sc = σ2.sc ∧
      σ3.draws = σ2.draws ∧ (∀ k, k ≠ 2 * j → σ3.arr aGam k = σ2.arr aGam k) ∧
      (2 * j < d → σ3.arr aGam (2 * j) = out1))
    (XV.ifN_skip hL (σ := σ2) (by lomega) (by lomega) (by rw [t2]; omega) (by rw [d2]; omega)
      (fun hc => ?_) (fun hc => ⟨FA2, rfl, rfl, rfl, fun _ _ => rfl, fun h => absurd (by rw [t2, d2]; exact h) hc⟩))
    fun σ3 ⟨FA3, n3, s3, d3, a3, a3'⟩ => ?_
  · rw [t2, d2] at hc
    refine XV.mono (XV.aset hL (σ := σ2) (a := aGam) (i := rT) (x := oBM + 40) (by lomega) (by lomega) (by lomega)
      (by rw [t2]; exact hdl _ hc) (by rw [c40']; exact bo1)) le_rfl fun σ' e => ?_
    subst e
    refine ⟨FA2.setArr ⟨rfl, by rw [t2]; exact hc, Or.inl t2⟩ _, rfl, rfl, rfl, fun k hk => ?_, fun _ => ?_⟩
    · simp only [Env.setArr_arr, t2]; rw [if_neg (by omega)]
    · simp only [Env.setArr_arr, t2, and_self, ite_true, c40']
  -- `Γ_ζ`
  have t3 : σ3.nat rT = 2 * j := by rw [n3, t2]
  have d3' : σ3.nat rD = d := by rw [n3, d2]
  have dd3 : σ3.nat rD2 = d + 2 := by rw [n3, dd2]
  have z3 : σ3.sc sZ = 0 := by rw [s3, z2]
  have v40 : σ3.sc (oBM + 40) = out1 := by rw [s3, c40']
  refine XV.seq (Q₁ := fun σ4 => FrameA (SB1 d j) NB1 (AB1 d j) σ σ4 ∧ σ4.nat = σ3.nat ∧ σ4.arr = σ3.arr ∧
      σ4.draws = σ3.draws ∧ ((d + 1) / 2 = j → σ4.sc sZeta = zetI cs K0 B d t) ∧
      (∀ y, y ≠ sZeta → σ4.sc y = σ3.sc y))
    (XV.ifN_skipT hL (σ := σ3) (by lomega) (by lomega) (by rw [t3]; omega) (by rw [d3']; omega)
      (fun hc => ⟨FA3, rfl, rfl, rfl, fun h => by rw [t3, d3'] at hc; omega, fun _ _ => rfl⟩)
      (fun hc => ?_)) fun σ4 ⟨FA4, n4, a4, d4, z4, s4⟩ => ?_
  · rw [t3, d3'] at hc
    refine XV.ifN_skip hL (σ := σ3) (by lomega) (by lomega) (by rw [t3]; omega) (by rw [dd3]; omega)
      (fun hc2 => ?_) (fun hc2 => ?_)
    · rw [t3, dd3] at hc2
      have hzj : (d + 1) / 2 = j := by omega
      refine XV.mono (XV.sop2 hL (σ := σ3) (x := sZeta) (a := oBM + 40) (b := sZ) (by lomega) (by lomega)
        (by lomega) .add (by intro h; cases h) (by rw [v40]; exact bo1) (by rw [z3]; simp)
        (by simp only [RealRAM.Op2.eval, v40, z3, add_zero]; exact bo1)) le_rfl fun σ' e => ?_
      subst e
      refine ⟨FA3.setSc (Or.inl ⟨rfl, hzj⟩) _, rfl, rfl, rfl, fun _ => ?_, fun y hy => by simp [hy]⟩
      simp only [Env.setSc_sc, ite_true, RealRAM.Op2.eval, v40, z3, add_zero, zetI, hzj, hout1]
    · rw [t3, dd3] at hc2
      exact ⟨FA3, rfl, rfl, rfl, fun h => by omega, fun _ _ => rfl⟩
  -- `rT := 2 j + 1`
  have t4 : σ4.nat rT = 2 * j := by rw [n4, t3]
  have o4 : σ4.nat rOne = 1 := by rw [n4, n3, o2]
  have d4' : σ4.nat rD = d := by rw [n4, d3']
  have v41 : σ4.sc (oBM + 41) = out2 := by rw [s4 _ (by lomega), s3, c41']
  refine XV.seq (XV.nadd hL (σ := σ4) (i := rT) (a := rT) (b := rOne) (by lomega) (by lomega) (by lomega)
    (by rw [t4]; omega) (by rw [o4]; omega)) fun σ5 e5 => ?_
  subst e5
  have FA5 : FrameA (SB1 d j) NB1 (AB1 d j) σ (σ4.setNat rT (σ4.nat rT + σ4.nat rOne)) := FA4.setNat (Or.inl rfl) _
  have t5 : (σ4.setNat rT (σ4.nat rT + σ4.nat rOne)).nat rT = 2 * j + 1 := by simp [t4, o4]
  have d5 : (σ4.setNat rT (σ4.nat rT + σ4.nat rOne)).nat rD = d := by simp [d4']
  have v41' : (σ4.setNat rT (σ4.nat rT + σ4.nat rOne)).sc (oBM + 41) = out2 := by simp [v41]
  have a5 : (σ4.setNat rT (σ4.nat rT + σ4.nat rOne)).arr = σ4.arr := rfl
  have s5 : (σ4.setNat rT (σ4.nat rT + σ4.nat rOne)).sc = σ4.sc := rfl
  have dr5 : (σ4.setNat rT (σ4.nat rT + σ4.nat rOne)).draws = σ4.draws := rfl
  generalize σ4.setNat rT (σ4.nat rT + σ4.nat rOne) = σ5 at FA5 t5 d5 v41' a5 s5 dr5
  -- `Γ_{2j+1}`
  refine XV.mono (XV.ifN_skip (P := fun σ6 => FrameA (SB1 d j) NB1 (AB1 d j) σ σ6 ∧
      σ6.sc = σ5.sc ∧ σ6.draws = σ5.draws ∧ (∀ k, k ≠ 2 * j + 1 → σ6.arr aGam k = σ5.arr aGam k) ∧
      (2 * j + 1 < d → σ6.arr aGam (2 * j + 1) = out2)) hL (σ := σ5) (by lomega) (by lomega) (by rw [t5]; omega)
      (by rw [d5]; omega) (fun hc => ?_) (fun hc => ⟨FA5, rfl, rfl, fun _ _ => rfl, fun h => by
        rw [t5, d5] at hc; omega⟩)) le_rfl fun σ6 ⟨FA6, s6, d6, a6, a6'⟩ => ?_
  · rw [t5, d5] at hc
    refine XV.mono (XV.aset hL (σ := σ5) (a := aGam) (i := rT) (x := oBM + 41) (by lomega) (by lomega) (by lomega)
      (by rw [t5]; exact hdl _ hc) (by rw [v41']; exact bo2)) le_rfl fun σ' e => ?_
    subst e
    refine ⟨FA5.setArr ⟨rfl, by rw [t5]; exact hc, Or.inr t5⟩ _, rfl, rfl, fun k hk => ?_, fun _ => ?_⟩
    · simp only [Env.setArr_arr, t5]; rw [if_neg (by omega)]
    · simp only [Env.setArr_arr, t5, and_self, ite_true, v41']
  refine ⟨?_, ?_, ?_, FA6⟩
  · rw [d6, dr5, d4, d3, dr2]
  · intro i hi hij
    rcases hij with rfl | rfl
    · rw [a6 _ (by omega), a5, a4, a3', g1]; exact hi
    · rw [a6' hi, g2]
  · intro h
    rw [s6, s5]
    exact z4 h

/-! ## The blocks of a round -/

theorem blkStart_next (d K0 B t : ℕ) :
    Sched.blkStart d K0 B t (Sched.nBlk d) = Sched.blkStart d K0 B (t + 1) 0 := by
  unfold Sched.blkStart; ring

set_option maxHeartbeats 1000000 in
/-- **R1 DRAW**: from the start of round `t` on the schedule, the integers `Γ_i` (`i < d`) and `Γ_ζ` of the draw of
round `t`, the count of draws at the start of round `t + 1`. -/
theorem XV.r1 {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) (hlay : BLLay L) {cs : ℕ → Bool}
    (hX : X.wb.cs = cs) {K0 B t : ℕ} {σ : Env d} (hB1 : 1 ≤ B) (hB : σ.nat rB = B) (hD : σ.nat rD = d)
    (h1 : σ.nat rOne = 1) (hNb : σ.nat rNb = Sched.nBlk d) (hz : σ.sc sZ = 0)
    (hdr : σ.draws = Sched.blkStart d K0 B t 0) (hℓa : 4 * gsm_prec B + 2 < 2 ^ ℓa) (hℓ : 4 * gsm_prec B + 4 ≤ ℓ)
    (hda : d + 2 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xR1 L) σ (r1Units d B) (fun σ' =>
      (∀ i : Fin d, σ'.arr aGam i = gamI cs K0 B d t i) ∧ σ'.sc sZeta = zetI cs K0 B d t ∧
      σ'.draws = Sched.blkStart d K0 B (t + 1) 0 ∧ FrameA SR1 NR1 (AR1 d) σ σ') := by
  have hlay' := hlay
  obtain ⟨hS, hN, hA⟩ := hlay'
  have hnb : 2 * Sched.nBlk d ≤ d + 3 := by unfold Sched.nBlk; omega
  have hnb' : d < 2 * Sched.nBlk d := by unfold Sched.nBlk; omega
  have hzn : (d + 1) / 2 < Sched.nBlk d := by unfold Sched.nBlk; omega
  -- `rD2 := d + 2`
  refine XV.mono (K := 1 + (1 + (Sched.nBlk d * (bmUnits B + 15 + 3) + 3))) ?_ (by unfold r1Units; ring_nf; omega)
    fun _ h => h
  refine XV.seq (XV.nadd hL (σ := σ) (i := rD2) (a := rD) (b := rOne) (by lomega) (by lomega) (by lomega)
    (by rw [hD]; omega) (by rw [h1]; omega)) fun σ0 e0 => ?_
  subst e0
  refine XV.seq (XV.nadd hL (i := rD2) (a := rD2) (b := rOne) (by lomega) (by lomega) (by lomega)
    (by simp [hD]; omega) (by rw [Env.setNat_nat, if_neg (by lomega), h1]; omega)) fun σ0 e0 => ?_
  subst e0
  set σ0 := (σ.setNat rD2 (σ.nat rD + σ.nat rOne)).setNat rD2
    ((σ.setNat rD2 (σ.nat rD + σ.nat rOne)).nat rD2 + (σ.setNat rD2 (σ.nat rD + σ.nat rOne)).nat rOne) with hσ0
  have F0 : FrameA SR1 NR1 (AR1 d) σ σ0 :=
    ((FrameA.refl _ _ _ σ).setNat (Or.inr (Or.inr (Or.inl rfl))) _).setNat (Or.inr (Or.inr (Or.inl rfl))) _
  have dd0 : σ0.nat rD2 = d + 2 := by simp [hσ0, hD, h1]
  let J : ℕ → Env d → Prop := fun j σ' => σ'.draws = Sched.blkStart d K0 B t j ∧ σ'.nat rD2 = d + 2 ∧
    (∀ i, i < d → i < 2 * j → σ'.arr aGam i = gamI cs K0 B d t i) ∧
    ((d + 1) / 2 < j → σ'.sc sZeta = zetI cs K0 B d t) ∧ FrameA SR1 NR1 (AR1 d) σ σ'
  refine XV.mono (XV.forN hL (i := rJ) (n := rNb) (one := rOne) (body := xR1body L) (by lomega) (by lomega)
    (by lomega) (by lomega) (by lomega) (Sched.nBlk d) (bmUnits B + 15) (by omega) J σ0
    (by simp [hσ0, hNb]) (by simp [hσ0, h1])
    ⟨by simp [hσ0, hdr], by simp [dd0], fun i _ h => absurd h (by omega), fun h => absurd h (by omega),
      F0.setNat (Or.inl rfl) 0⟩ ?_) le_rfl fun σ' ⟨⟨hd', _, ha', hz', F'⟩, _⟩ =>
      ⟨fun i => ha' i i.2 (by omega), hz' hzn, by rw [hd', blkStart_next], F'⟩
  intro j hj σ' ⟨hd', hdd', ha', hz', F'⟩ hjj hjn hj1
  have nB : σ'.nat rB = B := by rw [F'.1 rB (by simp only [NR1]; lomega), hB]
  have nD : σ'.nat rD = d := by rw [F'.1 rD (by simp only [NR1]; lomega), hD]
  have zz : σ'.sc sZ = 0 := by rw [F'.2.1 sZ (by simp only [SR1]; lomega), hz]
  refine XV.mono (XV.r1body hL hlay hX hB1 nB nD hj1 hdd' hjj zz hd' hℓa hℓ (by omega) hda) le_rfl
    fun σ'' ⟨hd'', ha'', hz'', F''⟩ => ?_
  have nJ : σ''.nat rJ = j := by rw [F''.1 rJ (by simp only [NB1]; lomega), hjj]
  have nN : σ''.nat rNb = Sched.nBlk d := by rw [F''.1 rNb (by simp only [NB1]; lomega), hjn]
  have nO : σ''.nat rOne = 1 := by rw [F''.1 rOne (by simp only [NB1]; lomega), hj1]
  have nD2 : σ''.nat rD2 = d + 2 := by rw [F''.1 rD2 (by simp only [NB1]; lomega), hdd']
  refine ⟨nJ, nN, nO, by simp [hd''], by simp [nD2], fun i hi hi2 => ?_, fun h => ?_, ?_⟩
  · simp only [Env.setNat_arr]
    by_cases hij : i = 2 * j ∨ i = 2 * j + 1
    · exact ha'' i hi hij
    · rw [F''.2.2.1 aGam i (fun h => hij h.2.2)]
      exact ha' i hi (by omega)
  · simp only [Env.setNat_sc]
    by_cases hzj : (d + 1) / 2 = j
    · exact hz'' hzj
    · rw [F''.2.1 sZeta (fun h => by rcases h with h | h <;> [exact hzj h.2; (simp only [oBM, sZeta] at h; omega)])]
      exact hz' (by omega)
  · refine (F'.trans (F''.mono (fun y hy => ?_) (fun i hi => ?_) (fun a k hk => ⟨hk.1, hk.2.1⟩))).setNat
      (Or.inl rfl) _
    · rcases hy with h | h
      · exact Or.inl h.1
      · exact Or.inr h
    · rcases hi with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))

end AdversarialBco.Bit.Transfer.BLM
