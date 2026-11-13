/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLRowT
public import AdversarialBco.Bit.Transfer.XBLRowP
public import AdversarialBco.Bit.Transfer.XTriRow
public import AdversarialBco.Bit.Transfer.XBLCall

@[expose] public section

/-!
# The row provider of BL, part 2: the scan for the `i`-th kept row

The row command's own cells (`SRow`, `NRow`, `ARow` of XBLCall.lean: slots `96..255`, registers `32..63`, arrays
`12..15`) are used as follows, all phases together:

* registers: `32` the row counter `k` of the scan, `33` the inner counter, `34` the count `c` of kept rows, `35` the
  row found `kk`, `36` an input address, `37` scratch of the addresses, `38` holds `0`, `39` holds `d + 1`, `40` the
  position of the strided dot product, `41` the column counter, `42` the output counter;
* slots: `96` the sum of squares `f`, `97` its scratch; `100..104` the row reading (`104`: `b̂ D_S`); `105`, `106`
  the product `P` of the row's denominators; `107` `D₀ = D_S P`; `108..115` a column (`108` `N_j`, `111..113` Euclid,
  `114`, `115` the reduced pair); `116` `rowDen`; `117..123` the right-hand side; `124`, `125` the outputs;
* arrays: `12` the cleared row `â`, `13` the reduced numerators, `14` the reduced denominators.

This file: `xscan`, the scan of the input rows `k < m` (`f = ∑_j Nm(k, j)²`; when `f > 0` the row is kept, and it
is the row `kk` sought when the count `c` equals `i`, read in register `64`), and its rule `XV.scan`:
`kk = (scanK keep i m).2`.
-/

namespace AdversarialBco.Bit.Transfer.BLM.RowM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer.RowP

variable {d : ℕ}

/-- Side conditions on the named cells of XBLInv.lean: `omega`, after unfolding the names. -/
macro "rwgo" : tactic => `(tactic| first | omega | decide |
  ((simp only [rD, rM, rMk, rOne, rPF, sZ, s2pF, sEps, sDS, aMuS, aAS, rEE, oE, aWE] at *) <;> omega) | fail "rwgo")

/-- `rpenv` with the names of XBLInv.lean unfolded in its side conditions. -/
macro "rwenv" : tactic =>
  `(tactic| (simp (disch := rwgo) only [nat_setNat_ne, nat_setNat_eq, sc_setSc_ne, sc_setSc_eq,
    Env.setNat_sc, Env.setSc_nat, Env.setArr_nat, Env.setArr_sc, Env.setNat_arr, Env.setSc_arr, Env.setNat_draws,
    Env.setSc_draws, Env.setArr_draws]))

theorem abs_sum_mul_lt {Xv Yv : ℕ → ℤ} {N E ℓ : ℕ} (bX : ∀ k < N, |Xv k| ≤ 2 ^ E) (bY : ∀ k < N, |Yv k| ≤ 2 ^ E)
    (hℓ : N * 2 ^ (2 * E) < 2 ^ ℓ) : ∀ k ≤ N, |∑ j ∈ Finset.range k, Xv j * Yv j| < 2 ^ ℓ := fun k hk => by
  have bXY : ∀ k < N, |Xv k * Yv k| ≤ ((2 ^ (2 * E) : ℕ) : ℤ) := fun k hk => by
    rw [abs_mul]; push_cast
    calc |Xv k| * |Yv k| ≤ 2 ^ E * 2 ^ E := mul_le_mul (bX k hk) (bY k hk) (abs_nonneg _) (by positivity)
      _ = 2 ^ (2 * E) := by ring
  have h1 : |∑ j ∈ Finset.range k, Xv j * Yv j| ≤ k * ((2 ^ (2 * E) : ℕ) : ℤ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have := Finset.sum_le_card_nsmul (Finset.range k) (fun j => |Xv j * Yv j|) ((2 ^ (2 * E) : ℕ) : ℤ)
      (fun j hj => bXY j (by rw [Finset.mem_range] at hj; omega))
    simpa using this
  have h2 : (k : ℤ) * ((2 ^ (2 * E) : ℕ) : ℤ) ≤ N * 2 ^ (2 * E) := by
    push_cast; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) (by positivity)
  have h3 : (N : ℤ) * 2 ^ (2 * E) < 2 ^ ℓ := by exact_mod_cast hℓ
  linarith

theorem scanK_le (keep : ℕ → Bool) (i : ℕ) : ∀ k, (scanK keep i k).1 ≤ k ∧ (scanK keep i k).2 ≤ k
  | 0 => by simp [scanK]
  | k + 1 => by
    obtain ⟨h1, h2⟩ := scanK_le keep i k
    rw [scanK_succ]
    split_ifs <;> refine ⟨?_, ?_⟩ <;> (try dsimp only) <;> omega

/-- What is kept: the rows with a positive sum of squares of the numerators. -/
def keepOf (d : ℕ) (Nm : ℕ → ℕ → ℤ) (k : ℕ) : Bool := decide (0 < ∑ j ∈ Finset.range d, Nm k j * Nm k j)

/-- The scan's work on a hit: `kk := k` if `c = i`, then `c := c + 1`. -/
def xscanHit : XCmd :=
  .seq (.ifN 34 64 .skip (.ifN 64 34 .skip (.prim (.frag (.nadd 35 32 38))))) (.prim (.frag (.nadd 34 34 rOne)))

/-- One row `k` of the scan: the address of its first numerator, the sum of squares, the hit. -/
def xscanBody (L : Layout) : XCmd :=
  .seq (xaddr 36 39 32 37 3) (.seq (xsqsum L sZ 96 97 33 36 rD rOne) (xifS L sZ 96 xscanHit .skip))

/-- The scan: `0`, `c`, `kk` to `0`, `d + 1` in `39`, then the rows `k < m`. -/
def xscan (L : Layout) : XCmd :=
  .seq (.prim (.frag (.nconst 38 0))) (.seq (.prim (.frag (.nconst 34 0))) (.seq (.prim (.frag (.nconst 35 0)))
    (.seq (.prim (.frag (.nadd 39 rD rOne))) (xforN 32 rM rOne (xscanBody L)))))

/-- The units of one row of the scan. -/
def scanKb (d : ℕ) : ℕ := 1 + (1 + (1 + 1)) + (sqUnits d + 7)

/-- The units of the scan. -/
def scanUnits (d m : ℕ) : ℕ := 1 + (1 + (1 + (1 + (m * (scanKb d + 3) + 3))))

/-- The registers of the row command. -/
def NR (j : ℕ) : Prop := 32 ≤ j ∧ j < 64

set_option maxHeartbeats 4000000 in
/-- **The scan**: register `35` ends as the row `(scanK keep i m).2`, with `keep k` the sign of the sum of the squares
of the numerators of row `k`; `38` holds `0` and `39` holds `d + 1`; only the slots `96`, `97` and the registers
`32..63` change. -/
theorem XV.scan {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) (hNS : 128 ≤ L.NS)
    (hNN : 64 < L.NN) {m i E : ℕ} {Nm : ℕ → ℕ → ℤ} (hD : σ.nat rD = d) (hM : σ.nat rM = m)
    (h1 : σ.nat rOne = 1) (hi : σ.nat 64 = i) (hz : σ.sc sZ = 0) (hoff : 3 + 2 * (d + 1) * m ≤ X.off)
    (hinp : ∀ k < m, ∀ j < d, X.inp (3 + 2 * ((d + 1) * k + j)) = Nm k j) (bN : ∀ k < m, ∀ j < d, |Nm k j| ≤ 2 ^ E)
    (hE : 2 * E < ℓ) (hℓ : d * 2 ^ (2 * E) < 2 ^ ℓ) (hma : 4 + 2 * (d + 1) * (m + 1) < 2 ^ ℓa) (hia : i < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xscan L) σ (scanUnits d m) (fun σ' =>
      σ'.nat 35 = (scanK (keepOf d Nm) i m).2 ∧ σ'.nat 38 = 0 ∧ σ'.nat 39 = d + 1 ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = 96 ∨ y = 97) NR (fun _ _ => False) σ σ') := by
  have hla := hL.1
  have hd1 : d + 1 < 2 ^ ℓa := by nlinarith
  have hm1 : m + 1 < 2 ^ ℓa := by nlinarith
  refine XV.seq (XV.nconst hL (i := 38) (by omega) 0 (by omega)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.nconst hL (i := 34) (by omega) 0 (by omega)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.nconst hL (i := 35) (by omega) 0 (by omega)) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.nadd hL (i := 39) (a := rD) (b := rOne) (by omega) (by rwgo)
    (by rwgo) (by rwenv; rw [hD]; omega) (by rwenv; rw [h1]; omega)) fun σ4 e4 => ?_
  subst e4
  set σ4 := (((σ.setNat 38 0).setNat 34 0).setNat 35 0).setNat 39
    ((((σ.setNat 38 0).setNat 34 0).setNat 35 0).nat rD + (((σ.setNat 38 0).setNat 34 0).setNat 35 0).nat rOne)
    with hσ4
  have g4D : σ4.nat rD = d := by rw [hσ4]; rwenv; exact hD
  have g4M : σ4.nat rM = m := by rw [hσ4]; rwenv; exact hM
  have g41 : σ4.nat rOne = 1 := by rw [hσ4]; rwenv; exact h1
  have g4i : σ4.nat 64 = i := by rw [hσ4]; rwenv; exact hi
  have g4c : σ4.nat 34 = 0 := by rw [hσ4]; rwenv
  have g4k : σ4.nat 35 = 0 := by rw [hσ4]; rwenv
  have g4z : σ4.nat 38 = 0 := by rw [hσ4]; rwenv
  have g4d : σ4.nat 39 = d + 1 := by rw [hσ4]; rwenv; rw [hD, h1]
  have F4 : FrameA (fun y => y = 96 ∨ y = 97) NR (fun _ _ => False) σ σ4 := by
    rw [hσ4]
    exact ((((FrameA.refl _ _ _ σ).setNat (by simp [NR]) _).setNat (by simp [NR]) _).setNat (by simp [NR]) _).setNat
      (by simp [NR]) _
  let J : ℕ → Env d → Prop := fun t σ' => σ'.nat 34 = (scanK (keepOf d Nm) i t).1 ∧
    σ'.nat 35 = (scanK (keepOf d Nm) i t).2 ∧ σ'.nat 38 = 0 ∧ σ'.nat 39 = d + 1 ∧ σ'.draws = σ.draws ∧
    FrameA (fun y => y = 96 ∨ y = 97) NR (fun _ _ => False) σ σ'
  refine XV.mono (XV.forN hL (i := 32) (n := rM) (one := rOne) (body := xscanBody L) (by omega)
    (by rwgo) (by rwgo) (by simp [rM]) (by simp [rOne]) m (scanKb d)
    (by omega) J σ4 g4M g41 ⟨by rwenv; rw [g4c]; rfl, by rwenv; rw [g4k]; rfl, by rwenv; exact g4z,
      by rwenv; exact g4d, by rwenv; rw [hσ4]; rwenv, F4.setNat (by simp [NR]) _⟩ ?_) le_rfl
    fun σ' ⟨⟨c1, c2, c3, c4, c5, c6⟩, _⟩ => ⟨c2, c3, c4, c5, c6⟩
  intro t ht σ' ⟨hc, hkk, hz', hd', hdr, hF⟩ hkt hkm hk1
  -- the cells that the frame keeps
  have eD : σ'.nat rD = d := by rw [hF.1 rD (by simp [NR, rD]), hD]
  have ei : σ'.nat 64 = i := by rw [hF.1 64 (by simp [NR]), hi]
  have ez : σ'.sc sZ = 0 := by rw [hF.2.1 sZ (by simp [sZ]), hz]
  obtain ⟨sc1, sc2⟩ := scanK_le (keepOf d Nm) i t
  have htm : (d + 1) * t ≤ (d + 1) * m := Nat.mul_le_mul_left _ ht.le
  have htm' : (d + 1) * (t + 1) ≤ (d + 1) * m := Nat.mul_le_mul_left _ ht
  -- the address of the first numerator of row `t`
  refine XV.seq (XV.addr hL (nI := 36) (nd1 := 39) (nk := 32) (nT := 37) (c0 := 3) (by omega) (by omega)
    (by omega) (by omega) (by decide) hd' hkt (by nlinarith) hd1 (by omega)) fun σ1 ⟨a1, a2, a3⟩ => ?_
  have e1 : ∀ j, ¬ (j = 36 ∨ j = 37) → σ1.nat j = σ'.nat j := a3.1
  -- the sum of squares
  have hinpt : ∀ j < d, X.inp (3 + 2 * ((d + 1) * t) + 2 * j) = Nm t j := fun j hj => by
    rw [show 3 + 2 * ((d + 1) * t) + 2 * j = 3 + 2 * ((d + 1) * t + j) by ring]; exact hinp t ht j hj
  refine XV.seq (XV.sqSum hL (z := sZ) (f := 96) (t := 97) (nj := 33) (nI := 36) (nn := rD) (none := rOne)
    (c := 3 + 2 * ((d + 1) * t)) (N := d) (E := E) (Nm := Nm t) (by rwgo) (by omega) (by omega)
    (by decide) (by omega) (by omega) (by rwgo) (by rwgo) (by decide)
    (by rw [a3.2.1 sZ (by simp), ez]) a1 (by rw [e1 rD (by simp [rD]), eD])
    (by rw [e1 rOne (by simp [rOne]), hk1]) (by nlinarith) (by nlinarith) hinpt (bN t ht) hE hℓ)
    fun σ2 ⟨s1, s2, s3, s4⟩ => ?_
  have hf : |(∑ j ∈ Finset.range d, Nm t j * Nm t j : ℤ)| < 2 ^ ℓ :=
    abs_sum_mul_lt (bN t ht) (bN t ht) hℓ d le_rfl
  have e2 : ∀ j, ¬ (j = 36 ∨ j = 37) → ¬ (j = 33 ∨ j = 36) → σ2.nat j = σ'.nat j := fun j h h' => by
    rw [s4.1 j h', e1 j h]
  have z2 : σ2.sc sZ = 0 := by rw [s4.2.1 sZ (by simp [sZ]), a3.2.1 sZ (by simp), ez]
  have F2 : FrameA (fun y => y = 96 ∨ y = 97) NR (fun _ _ => False) σ σ2 :=
    hF.trans ((a3.mono (fun _ h => h.elim) (fun j h => by rcases h with h | h <;> simp [NR, h])
      (fun _ _ h => h)).trans (s4.mono (fun _ h => h) (fun j h => by rcases h with h | h <;> simp [NR, h])
      (fun _ _ h => h)))
  have c2 : σ2.nat 34 = (scanK (keepOf d Nm) i t).1 := by rw [e2 34 (by simp) (by simp), hc]
  have k2 : σ2.nat 35 = (scanK (keepOf d Nm) i t).2 := by rw [e2 35 (by simp) (by simp), hkk]
  have i2 : σ2.nat 64 = i := by rw [e2 64 (by simp) (by simp), ei]
  have t2 : σ2.nat 32 = t := by rw [e2 32 (by simp) (by simp), hkt]
  have z2' : σ2.nat 38 = 0 := by rw [e2 38 (by simp) (by simp), hz']
  have d2 : σ2.nat 39 = d + 1 := by rw [e2 39 (by simp) (by simp), hd']
  have m2 : σ2.nat rM = m := by rw [e2 rM (by simp [rM]) (by simp [rM]), hkm]
  have o2 : σ2.nat rOne = 1 := by rw [e2 rOne (by simp [rOne]) (by simp [rOne]), hk1]
  have hS : scanK (keepOf d Nm) i (t + 1) = if keepOf d Nm t then
      (if (scanK (keepOf d Nm) i t).1 = i then ((scanK (keepOf d Nm) i t).1 + 1, t)
        else ((scanK (keepOf d Nm) i t).1 + 1, (scanK (keepOf d Nm) i t).2)) else scanK (keepOf d Nm) i t :=
    scanK_succ _ _ _
  set c := (scanK (keepOf d Nm) i t).1 with hcdef
  set kk := (scanK (keepOf d Nm) i t).2 with hkkdef
  -- the post of the turn, from the registers `34`, `35` after it
  have post : ∀ σ5 : Env d, FrameA (fun _ => False) (fun j => j = 34 ∨ j = 35) (fun _ _ => False) σ2 σ5 →
      σ5.draws = σ2.draws → σ5.nat 34 = (scanK (keepOf d Nm) i (t + 1)).1 →
      σ5.nat 35 = (scanK (keepOf d Nm) i (t + 1)).2 →
      σ5.nat 32 = t ∧ σ5.nat rM = m ∧ σ5.nat rOne = 1 ∧ J (t + 1) (σ5.setNat 32 (t + 1)) := by
    intro σ5 F5 d5 c5 k5
    refine ⟨by rw [F5.1 32 (by simp), t2], by rw [F5.1 rM (by simp [rM]), m2], by rw [F5.1 rOne (by simp [rOne]), o2],
      by rwenv; exact c5, by rwenv; exact k5, by rwenv; rw [F5.1 38 (by simp), z2'],
      by rwenv; rw [F5.1 39 (by simp), d2], by rwenv; rw [d5, s3, a2, hdr], ?_⟩
    exact (F2.trans (F5.mono (fun _ h => h.elim) (fun j h => by rcases h with h | h <;> simp [NR, h])
      (fun _ _ h => h))).setNat (by simp [NR]) _
  -- the test `0 < f`
  by_cases hkeep : (0 : ℤ) < ∑ j ∈ Finset.range d, Nm t j * Nm t j
  · have hkp : keepOf d Nm t = true := by simp [keepOf, hkeep]
    refine XV.mono (XV.ifS_t hL (by rwgo) (by omega) (by rw [z2]; simp)
      (by rw [s1]; exact XV.abs_int_lt hf) (by rw [z2, s1]; exact_mod_cast hkeep) ?_) (K := 6 + 1)
      (by omega) fun σ' h => h
    have hca : c < 2 ^ ℓa := by omega
    -- `kk := t` when `c = i`, then `c := c + 1`
    have hstep : ∀ σ3 : Env d, FrameA (fun _ => False) (fun j => j = 35) (fun _ _ => False) σ2 σ3 →
        σ3.draws = σ2.draws → σ3.nat 35 = (scanK (keepOf d Nm) i (t + 1)).2 →
        XRunsB L X ℓa ℓ (.prim (.frag (.nadd 34 34 rOne))) σ3 1 (fun σ5 =>
          σ5.nat 32 = t ∧ σ5.nat rM = m ∧ σ5.nat rOne = 1 ∧ J (t + 1) (σ5.setNat 32 (t + 1))) := by
      intro σ3 F3 d3 k3
      have c3 : σ3.nat 34 = c := by rw [F3.1 34 (by simp), c2]
      have o3 : σ3.nat rOne = 1 := by rw [F3.1 rOne (by simp [rOne]), o2]
      refine XV.mono (XV.nadd hL (i := 34) (a := 34) (b := rOne) (by omega) (by omega)
        (by rwgo) (by rw [c3]; exact hca) (by rw [o3]; omega)) le_rfl fun σ5 e5 => ?_
      subst e5
      refine post _ ((F3.mono (N' := fun j => j = 34 ∨ j = 35) (fun _ h => h) (fun j h => Or.inr h) (fun _ _ h => h)).setNat (Or.inl rfl) _)
        (by simp [d3]) (by rw [nat_setNat_eq, c3, o3, hS, hkp]; simp only [↓reduceIte]; split_ifs <;> rfl) ?_
      rw [nat_setNat_ne _ (by decide), k3]
    refine XV.seq (K₂ := 1) (Q₁ := fun σ3 => FrameA (fun _ => False) (fun j => j = 35) (fun _ _ => False) σ2 σ3 ∧
      σ3.draws = σ2.draws ∧ σ3.nat 35 = (scanK (keepOf d Nm) i (t + 1)).2) ?_ fun σ3 ⟨F3, d3, k3⟩ => hstep σ3 F3 d3 k3
    by_cases hci : c < i
    · refine XV.mono (XV.ifN_t hL (i := 34) (j := 64) (by omega) (by omega) (by rw [c2]; exact hca)
        (by rw [i2]; exact hia) (by rw [c2, i2]; exact hci) (XV.skip σ2)) (by omega) fun σ3 e3 => ?_
      subst e3
      refine ⟨FrameA.refl _ _ _ _, rfl, ?_⟩
      rw [k2, hS, hkp]; simp [show c ≠ i by omega]
    · refine XV.mono (XV.ifN_f hL (i := 34) (j := 64) (by omega) (by omega) (by rw [c2]; exact hca)
        (by rw [i2]; exact hia) (by rw [c2, i2]; exact hci) ?_) (K := 3 + 2) (by omega) fun σ3 h => h
      by_cases hic : i < c
      · refine XV.mono (XV.ifN_t hL (i := 64) (j := 34) (by omega) (by omega) (by rw [i2]; exact hia)
          (by rw [c2]; exact hca) (by rw [c2, i2]; exact hic) (XV.skip σ2)) (by omega) fun σ3 e3 => ?_
        subst e3
        refine ⟨FrameA.refl _ _ _ _, rfl, ?_⟩
        rw [k2, hS, hkp]; simp [show c ≠ i by omega]
      · have hce : c = i := by omega
        refine XV.mono (XV.ifN_f hL (i := 64) (j := 34) (by omega) (by omega) (by rw [i2]; exact hia)
          (by rw [c2]; exact hca) (by rw [c2, i2]; exact hic) (XV.nadd hL (i := 35) (a := 32) (b := 38)
            (by omega) (by omega) (by omega) (by rw [t2]; omega) (by rw [z2']; omega))) le_rfl fun σ3 e3 => ?_
        subst e3
        refine ⟨(FrameA.refl (fun _ => False) (fun j => j = 35) (fun _ _ => False) σ2).setNat rfl _, rfl, ?_⟩
        rw [nat_setNat_eq, t2, z2', hS, hkp]; simp [hce]
  · have hkp : keepOf d Nm t = false := by simp [keepOf, hkeep]
    refine XV.mono (XV.ifS_f hL (by rwgo) (by omega) (by rw [z2]; simp)
      (by rw [s1]; exact XV.abs_int_lt hf) (by rw [z2, s1]; exact_mod_cast hkeep) (XV.skip σ2)) (K := 0 + 2)
      (by omega) fun σ5 e5 => ?_
    subst e5
    exact post _ (FrameA.refl _ _ _ _) rfl (by rw [c2, hS, hkp]; simp only [Bool.false_eq_true, ↓reduceIte]; exact hcdef)
      (by rw [k2, hS, hkp]; simp only [Bool.false_eq_true, ↓reduceIte]; exact hkkdef)

end AdversarialBco.Bit.Transfer.BLM.RowM
