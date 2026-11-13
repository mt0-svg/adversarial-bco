/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriCore

@[expose] public section

/-!
# TRI-M, a stage on the machine

* `xmmRow`, `XV.mmRow`: row `i` of `T S` as `Sᵀ (Tᵀ e_i)`, scattered into the cells `d i + l`; `xmatmul`,
  `XV.matmul`: the product `T S` row by row into a third array.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM Matrix

variable {d : ℕ}

theorem row_mul_eq' (T S : Matrix (Fin d) (Fin d) ℤ) (i : Fin d) :
    Sᵀ *ᵥ (Tᵀ *ᵥ Pi.single i 1) = fun l => (T * S) i l := by
  have h1 : Tᵀ *ᵥ Pi.single i 1 = fun k => T i k := by
    funext k; simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.single_apply]
  funext l
  rw [h1]; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_comm]

/-! ## The product of two matrices -/

/-- Row `i` (in `nri`) of `T S`: `e := e_i`, `u := Tᵀ e`, `v := Sᵀ u`, then `P[nb + k] := v[k]`. -/
def xmmRow (L : Layout) (z r t s1 aT aS aE aU aV aP nri nb ni nr nk nd none : ℕ) : XCmd :=
  .seq (xfill L z t z aE nr none nk nd none)
  (.seq (toX (VL.aset L aE nri s1))
  (.seq (xmatvecT L z r t aT aE aU ni nr nk nd none)
  (.seq (xmatvecT L z r t aS aU aV ni nr nk nd none)
  (xmapE L z t (.arr aV nk) aP nb none nk nd none))))

/-- The units of `xmmRow`. -/
abbrev mmRowK (d : ℕ) : ℕ :=
  1 + (d * (1 + 6) + 3) + (2 + (d * (1 + (1 + (d * 10 + 4 + 2)) + 3) + 3 +
    (d * (1 + (1 + (d * 10 + 4 + 2)) + 3) + 3 + (d * (2 + 6) + 3))))

set_option maxHeartbeats 4000000 in
theorem XV.mmRow {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {z r t s1 aT aS aE aU aV aP nri nb ni nr nk nd none E i : ℕ} {T S : Matrix (Fin d) (Fin d) ℤ}
    (hi : i < d) (hz : z < t) (hs1 : s1 < t) (hrt : r < t) (hrz : r ≠ z) (hS : t + 3 ≤ L.NS) (hz0 : σ.sc z = 0)
    (h1 : σ.sc s1 = 1) (haT : aT < L.NA) (haS : aS < L.NA) (haE : aE < L.NA) (haU : aU < L.NA) (haV : aV < L.NA)
    (haP : aP < L.NA) (hA : aT < aS ∧ aS < aE ∧ aE < aU ∧ aU < aV ∧ aV < aP)
    (hnri : nri < L.NN) (hnb : nb < L.NN) (hni : ni < L.NN) (hnr : nr < L.NN) (hnk : nk < L.NN)
    (hnd : nd < L.NN) (hno : none < L.NN) (hne : nd < none ∧ none < nr ∧ nr < nk ∧ nk < ni ∧ ni < nri ∧ nri < nb)
    (hσd : σ.nat nd = d) (hσ1 : σ.nat none = 1) (hσi : σ.nat nri = i) (hσb : σ.nat nb = d * i)
    (hda : d * d + d < 2 ^ ℓa)
    (hT : ∀ i l : Fin d, σ.arr aT (d * i + l) = T i l) (hSS : ∀ i l : Fin d, σ.arr aS (d * i + l) = S i l)
    (bT : ∀ i l, |T i l| ≤ 2 ^ E) (bS : ∀ i l, |S i l| ≤ 2 ^ E) (hE : 4 * E + 3 * d + 2 < ℓ) :
    XRunsB L X ℓa ℓ (xmmRow L z r t s1 aT aS aE aU aV aP nri nb ni nr nk nd none) σ (mmRowK d) (fun σ' =>
      (∀ l : Fin d, σ'.arr aP (d * i + l) = (T * S) ⟨i, hi⟩ l) ∧ σ'.nat nb = d * (i + 1) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = r ∨ t ≤ y) (fun j => j = ni ∨ j = nk ∨ j = nr ∨ j = nb)
        (fun b c => (b = aE ∨ b = aU ∨ b = aV) ∧ c < d ∨ b = aP ∧ d * i ≤ c ∧ c < d * i + d) σ σ') := by
  obtain ⟨TS, SE, EU, UV, VP⟩ := hA
  obtain ⟨dO, oR, rk, ki, iI, Ib⟩ := hne
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  have hcd : ∀ k < d, k < asz d := fun k hk => by unfold asz; nlinarith
  have hdl : ∀ F, 2 * F + d < ℓ → d * 2 ^ (2 * F) < 2 ^ ℓ := fun F hF => by
    have h2 : d < 2 ^ d := Nat.lt_two_pow_self
    calc d * 2 ^ (2 * F) ≤ 2 ^ d * 2 ^ (2 * F) := Nat.mul_le_mul_right _ h2.le
      _ = 2 ^ (2 * F + d) := by rw [← pow_add]; ring_nf
      _ < 2 ^ ℓ := Nat.pow_lt_pow_right (by norm_num) hF
  have E2 : E ≤ 2 * E + d := by omega
  -- `e := 0`
  refine XV.seq (XV.fill hL (z := z) (t := t) (s := z) (aB := aE) (nr := nr) (nst := none) (nk := nk) (nn := nd)
    (none := none) (N := d) (st := 1) (E := 0) (v := 0) hz hz (by omega) hz0 haE hnr hno hnk hnd hno
    (by simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
      and_true, not_false_eq_true]; omega) (by omega) (by omega) hσd hσ1 hσ1 one_pos
    (fun k hk => by rw [one_mul]; exact hcd k hk) (by omega) (by omega) hsa (by rw [hz0]; simp) (by simp)
    (by omega)) fun σ1 ⟨e1, d1, F1⟩ => ?_
  -- `e[i] := 1`
  have n1 : ∀ j, j ≠ nk → j ≠ nr → σ1.nat j = σ.nat j := fun j h h' => F1.1 _ (by omega)
  have s1' : σ1.sc s1 = 1 := by rw [F1.2.1 _ (by omega), h1]
  refine XV.seq (XV.aset hL (a := aE) (i := nri) (x := s1) haE hnri (by omega)
    (by rw [n1 _ (by omega) (by omega), hσi]; exact hcd i hi) (by rw [s1']; simp only [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)))
    fun σ2 e2 => ?_
  subst e2
  set σ2 := σ1.setArr aE (σ1.nat nri) (σ1.sc s1) with hσ2
  have eE : ∀ k : Fin d, σ2.arr aE k = (Pi.single (⟨i, hi⟩ : Fin d) (1 : ℤ) : Fin d → ℤ) k := fun k => by
    rw [hσ2, Env.setArr_arr, n1 _ (by omega) (by omega), hσi, s1']
    by_cases hk : (k : ℕ) = i
    · have : k = ⟨i, hi⟩ := Fin.ext hk
      subst this; simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hk h.2)]
      have := e1 k k.2; rw [one_mul] at this; rw [this]
      rw [Pi.single_eq_of_ne (fun h => hk (by rw [h]))]
  have bE : ∀ k, |(Pi.single (⟨i, hi⟩ : Fin d) (1 : ℤ) : Fin d → ℤ) k| ≤ 2 ^ E := fun k => by
    by_cases hk : k = ⟨i, hi⟩
    · subst hk; rw [Pi.single_eq_same, abs_one]; exact one_le_pow₀ (by norm_num)
    · rw [Pi.single_eq_of_ne hk]; simp
  have G2 : FrameA (fun y => t ≤ y) (fun j => j = nk ∨ j = nr) (fun b c => b = aE ∧ c < d) σ σ2 :=
    (F1.mono (fun _ h => h) (fun _ h => h) (fun b c h => ⟨h.1, by rw [one_mul] at h; exact h.2⟩)).setArr
      ⟨rfl, by rw [n1 _ (by omega) (by omega), hσi]; exact hi⟩ _
  -- `u := Tᵀ e`
  refine XV.seq (XV.matvecT hL (z := z) (r := r) (t := t) (aM := aT) (ax := aE) (ay := aU) (ni := ni) (nr := nr)
    (nk := nk) (nd := nd) (none := none) (E := E) (M := T) (x := Pi.single (⟨i, hi⟩ : Fin d) (1 : ℤ)) hz hrt hrz hS
    (by rw [G2.2.1 _ (by omega), hz0]) haT haE haU (by omega) (by omega) hni hnr hnk hnd hno
    (by simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
      and_true, not_false_eq_true]; omega) (by rw [G2.1 _ (by omega), hσd]) (by rw [G2.1 _ (by omega), hσ1])
    (fun i' l => by rw [G2.2.2.1 aT (d * i' + l) (fun h => by omega), hT]) eE bT bE (by omega) (hdl E (by omega)))
    fun σ3 ⟨u3, d3, F3⟩ => ?_
  -- `v := Sᵀ u`
  refine XV.seq (XV.matvecT hL (z := z) (r := r) (t := t) (aM := aS) (ax := aU) (ay := aV) (ni := ni) (nr := nr)
    (nk := nk) (nd := nd) (none := none) (E := 2 * E + d) (M := S)
    (x := Tᵀ *ᵥ Pi.single (⟨i, hi⟩ : Fin d) (1 : ℤ)) hz hrt hrz hS
    (by rw [F3.2.1 _ (by omega), G2.2.1 _ (by omega), hz0]) haS haU haV (by omega) (by omega) hni hnr hnk hnd hno
    (by simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
      and_true, not_false_eq_true]; omega) (by rw [F3.1 _ (by omega), G2.1 _ (by omega), hσd])
    (by rw [F3.1 _ (by omega), G2.1 _ (by omega), hσ1])
    (fun i' l => by rw [F3.2.2.1 aS (d * i' + l) (fun h => by omega), G2.2.2.1 aS (d * i' + l) (fun h => by omega), hSS]) u3
    (fun i' l => abs_le_mono (bS i' l) E2) (abs_mulVec_le (fun a b => bT b a) bE) (by omega)
    (hdl _ (by omega))) fun σ4 ⟨v4, d4, F4⟩ => ?_
  -- scatter `v` into row `i` of `P`
  have hv : ∀ k : Fin d, σ4.arr aV k = (T * S) ⟨i, hi⟩ k := fun k => by
    rw [v4 k, row_mul_eq']
  have bV : ∀ k, |(T * S) ⟨i, hi⟩ k| ≤ 2 ^ (2 * (2 * E + d) + d) := fun k => by
    rw [show (T * S) ⟨i, hi⟩ k = (Sᵀ *ᵥ (Tᵀ *ᵥ Pi.single (⟨i, hi⟩ : Fin d) (1 : ℤ))) k by rw [row_mul_eq']]
    exact abs_mulVec_le (fun a b => abs_le_mono (bS b a) E2) (abs_mulVec_le (fun a b => bT b a) bE) k
  have n4 : ∀ j, j ≠ ni → j ≠ nk → j ≠ nr → σ4.nat j = σ.nat j := fun j h h' h'' => by
    rw [F4.1 _ (by omega), F3.1 _ (by omega), G2.1 _ (by omega)]
  refine XV.mono (XV.mapE hL (z := z) (t := t) (e := .arr aV nk) (aB := aP) (nr := nb) (nst := none) (nk := nk)
    (nn := nd) (none := none) (E := 2 * (2 * E + d) + d) (N := d) (base := d * i) (st := 1)
    (F := fun k => vext (fun l => (T * S) ⟨i, hi⟩ l) k) (by simp only [IE.WF]; exact ⟨haV, hnk⟩) hz
    (by simp only [IE.scr]; omega) (by rw [F4.2.1 _ (by omega), F3.2.1 _ (by omega), G2.2.1 _ (by omega), hz0]) haP
    hnb hno hnk hnd hno
    (by simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
      and_true, not_false_eq_true]; omega) (by omega) (by omega) (by rw [n4 _ (by omega) (by omega) (by omega), hσd])
    (by rw [n4 _ (by omega) (by omega) (by omega), hσ1]) (by rw [n4 _ (by omega) (by omega) (by omega), hσb])
    (by rw [n4 _ (by omega) (by omega) (by omega), hσ1]) one_pos
    (fun k hk => by unfold asz; nlinarith [Nat.mul_le_mul_left d (show i + 1 ≤ d by omega)]) (by omega)
    (by nlinarith [Nat.mul_le_mul_left d (show i + 1 ≤ d by omega)]) hsa (by simp only [IE.top]; omega)
    (fun k hk σ' F' _ hk' _ => ?_)) (by simp only [IE.units]; omega) ?_
  · have va : σ'.arr aV k = (T * S) ⟨i, hi⟩ ⟨k, hk⟩ := by
      rw [F'.2.2.1 _ _ (by omega)]; exact hv ⟨k, hk⟩
    refine ⟨⟨by rw [hk']; exact hcd k hk, (T * S) ⟨i, hi⟩ ⟨k, hk⟩, by rw [hk', va], bV _⟩, ?_⟩
    simp only [IE.eval, hk', va, vext_lt _ hk]
  · rintro σ5 ⟨p5, b5, d5, F5⟩
    refine ⟨fun l => by have := p5 l l.2; rw [one_mul, vext_lt _ l.2] at this; exact this,
      by rw [b5]; ring, by rw [d5, d4, d3, hσ2, Env.setArr_draws, d1], ?_⟩
    exact (((G2.mono (fun y h => Or.inr h) (fun j h => by omega) (fun b c h => Or.inl ⟨Or.inl h.1, h.2⟩)).trans
      (F3.mono (fun y h => h) (fun j h => by omega) (fun b c h => Or.inl ⟨Or.inr (Or.inl h.1), h.2⟩))).trans
      (F4.mono (fun y h => h) (fun j h => by omega) (fun b c h => Or.inl ⟨Or.inr (Or.inr h.1), h.2⟩))).trans
      (F5.mono (fun y h => Or.inr h) (fun j h => by omega) (fun b c h => Or.inr ⟨h.1, h.2.1, by omega⟩))

/-- `P := T S` into the `d²` cells of `aP`, row by row (`nri` the row, `nb = d nri`). -/
def xmatmul (L : Layout) (z r t s1 aT aS aE aU aV aP nri nb ni nr nk nd none : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst nb 0)))
  (xforN nri nd none (xmmRow L z r t s1 aT aS aE aU aV aP nri nb ni nr nk nd none))

/-- The units of `xmatmul`. -/
abbrev matmulK (d : ℕ) : ℕ := 1 + (d * (mmRowK d + 3) + 3)

set_option maxHeartbeats 4000000 in
theorem XV.matmul {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {z r t s1 aT aS aE aU aV aP nri nb ni nr nk nd none E : ℕ} {T S : Matrix (Fin d) (Fin d) ℤ}
    (hz : z < t) (hs1 : s1 < t) (hrt : r < t) (hrz : r ≠ z) (hs1r : s1 ≠ r) (hS : t + 3 ≤ L.NS) (hz0 : σ.sc z = 0)
    (h1 : σ.sc s1 = 1) (haT : aT < L.NA) (haS : aS < L.NA) (haE : aE < L.NA) (haU : aU < L.NA) (haV : aV < L.NA)
    (haP : aP < L.NA) (hA : aT < aS ∧ aS < aE ∧ aE < aU ∧ aU < aV ∧ aV < aP)
    (hnri : nri < L.NN) (hnb : nb < L.NN) (hni : ni < L.NN) (hnr : nr < L.NN) (hnk : nk < L.NN)
    (hnd : nd < L.NN) (hno : none < L.NN) (hne : nd < none ∧ none < nr ∧ nr < nk ∧ nk < ni ∧ ni < nri ∧ nri < nb)
    (hσd : σ.nat nd = d) (hσ1 : σ.nat none = 1) (hda : d * d + d < 2 ^ ℓa)
    (hT : ∀ i l : Fin d, σ.arr aT (d * i + l) = T i l) (hSS : ∀ i l : Fin d, σ.arr aS (d * i + l) = S i l)
    (bT : ∀ i l, |T i l| ≤ 2 ^ E) (bS : ∀ i l, |S i l| ≤ 2 ^ E) (hE : 4 * E + 3 * d + 2 < ℓ) :
    XRunsB L X ℓa ℓ (xmatmul L z r t s1 aT aS aE aU aV aP nri nb ni nr nk nd none) σ (matmulK d) (fun σ' =>
      (∀ i l : Fin d, σ'.arr aP (d * i + l) = (T * S) i l) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = r ∨ t ≤ y) (fun j => j = ni ∨ j = nk ∨ j = nr ∨ j = nb ∨ j = nri)
        (fun b c => (b = aE ∨ b = aU ∨ b = aV) ∧ c < d ∨ b = aP ∧ c < d * d) σ σ') := by
  have hA' := hA
  have hne' := hne
  obtain ⟨TS, SE, EU, UV, VP⟩ := hA'
  obtain ⟨dO, oR, rk, ki, iI, Ib⟩ := hne'
  refine XV.seq (XV.nconst hL hnb 0 (by positivity)) fun σ0 e0 => ?_
  subst e0
  let J : ℕ → Env d → Prop := fun i σ' =>
    (∀ i' (_ : i' < i) (hd : i' < d), ∀ l : Fin d, σ'.arr aP (d * i' + l) = (T * S) ⟨i', hd⟩ l) ∧
    σ'.nat nb = d * i ∧ σ'.draws = σ.draws ∧
    FrameA (fun y => y = r ∨ t ≤ y) (fun j => j = ni ∨ j = nk ∨ j = nr ∨ j = nb ∨ j = nri)
      (fun b c => (b = aE ∨ b = aU ∨ b = aV) ∧ c < d ∨ b = aP ∧ c < d * i) σ σ'
  have hdN : d < 2 ^ ℓa := by nlinarith
  refine XV.mono (XV.forN (L := L) (X := X) (ℓ := ℓ) (i := nri) (n := nd) (one := none) hL hnri hnd hno
    (by omega) (by omega) d (mmRowK d) hdN J (σ.setNat nb 0)
    (by rw [nat_setNat_ne _ (by omega), hσd]) (by rw [nat_setNat_ne _ (by omega), hσ1])
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), by rw [nat_setNat_ne _ (by omega), nat_setNat_eq, mul_zero],
      by rw [Env.setNat_draws, Env.setNat_draws],
      (((FrameA.refl (fun y => y = r ∨ t ≤ y) (fun j => j = ni ∨ j = nk ∨ j = nr ∨ j = nb ∨ j = nri)
        (fun b c => (b = aE ∨ b = aU ∨ b = aV) ∧ c < d ∨ b = aP ∧ c < d * 0) σ).setNat
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) 0).setNat (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) 0)⟩ ?_)
    le_rfl ?_
  · intro i hi σ' ⟨jP, jb, jd, jG⟩ hki hkn hk1
    refine XV.mono (XV.mmRow hL (z := z) (r := r) (t := t) (s1 := s1) (aT := aT) (aS := aS) (aE := aE) (aU := aU)
      (aV := aV) (aP := aP) (nri := nri) (nb := nb) (ni := ni) (nr := nr) (nk := nk) (nd := nd) (none := none)
      (E := E) (i := i) (T := T) (S := S) hi hz hs1 hrt hrz hS (by rw [jG.2.1 z (by omega), hz0])
      (by rw [jG.2.1 s1 (by omega), h1]) haT haS haE haU haV haP hA hnri hnb hni hnr hnk hnd hno hne hkn hk1 hki jb hda
      (fun i' l => by rw [jG.2.2.1 aT (d * i' + l) (by omega), hT])
      (fun i' l => by rw [jG.2.2.1 aS (d * i' + l) (by omega), hSS]) bT bS hE)
      le_rfl ?_
    rintro σ'' ⟨p'', b'', d'', F''⟩
    have hdi : d * (i + 1) = d * i + d := Nat.mul_succ d i
    refine ⟨by rw [F''.1 nri (by omega), hki], by rw [F''.1 nd (by omega), hkn], by rw [F''.1 none (by omega), hk1],
      fun i' hi' hd l => ?_, by rw [nat_setNat_ne _ (by omega), b''], by rw [Env.setNat_draws, d'', jd], ?_⟩
    · rw [Env.setNat_arr]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hlt | rfl
      · have hc : d * i' + l < d * i := by
          have : d * (i' + 1) ≤ d * i := Nat.mul_le_mul_left _ hlt
          rw [Nat.mul_succ] at this; have := l.2; omega
        rw [F''.2.2.1 aP (d * i' + l) (by omega)]
        exact jP i' hlt hd l
      · exact p'' l
    · exact ((jG.mono (fun _ h => h) (fun _ h => h) (fun b c h => by
        rcases h with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, by omega⟩)).trans (F''.mono (fun _ h => h) (fun j h => by omega) (fun b c h => by
        rcases h with h | ⟨h1, -, h3⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, by omega⟩))).setNat (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) _
  · rintro σ' ⟨⟨jP, -, jd, jG⟩, -, -, -⟩
    exact ⟨fun i l => jP i i.2 i.2 l, jd, jG⟩

theorem abs_matmul_le {T S : Matrix (Fin d) (Fin d) ℤ} {E : ℕ} (bT : ∀ i l, |T i l| ≤ 2 ^ E)
    (bS : ∀ i l, |S i l| ≤ 2 ^ E) (i l : Fin d) : |(T * S) i l| ≤ 2 ^ (2 * E + d) := by
  rw [Matrix.mul_apply]
  exact dot_abs_le (x := fun k => T i k) (y := fun k => S k l) (fun k => bT i k) (fun k => bS k l)

theorem tabsR_lt {v : ℤ} {F ℓ : ℕ} (h : |v| ≤ 2 ^ F) (hF : F < ℓ) : |(v : ℝ)| < 2 ^ ℓ := by
  have h2 : (2 : ℤ) ^ F < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) hF
  have : |v| < 2 ^ ℓ := lt_of_le_of_lt h h2
  rw [← Int.cast_abs]; exact_mod_cast this

theorem abs_two_pow_le {G E : ℕ} (h : G ≤ E) : |(2 : ℤ) ^ G| ≤ 2 ^ E := by
  rw [abs_of_pos (by positivity)]; exact pow_le_pow_right₀ (by norm_num) h

/-! ## The composition of a stage -/

/-- `μ̂_k 2^{G_c} + w_k`. -/
def ieMuC (aMu aW sP nr : ℕ) : IE := .op .add (.op .mul (.arr aMu nr) (.sc sP)) (.arr aW nr)

/-- The composition after the core: `μ̂ := μ̂ 2^{G_c} + T̂ Ŝ_μ`, `T̂ := T̂ Ŝ_T`, `D := D 2^{G_c}`, and the slots
`2^e := 2^e 2^{G_c}`, `2^j D := 2 (2^j D) 2^{G_c}` of the next stage (`2^{G_c}` in `o + 35`). -/
def xstageC (L : Layout) (o r a nd : ℕ) : XCmd :=
  .seq (xmatvec L (o + 1) (o + 20) (o + 40) (a + 1) (a + 4) (a + 12) (r + 7) (r + 4) (r + 5) nd r)
  (.seq (.prim (.frag (.nconst (r + 4) 0)))
  (.seq (xmapE L (o + 1) (o + 40) (ieMuC a (a + 12) (o + 35) (r + 4)) a (r + 4) r (r + 5) nd r)
  (.seq (xmatmul L (o + 1) (o + 20) (o + 40) (o + 2) (a + 1) (a + 5) (a + 12) (a + 13) (a + 14) (a + 15)
      (r + 11) (r + 16) (r + 7) (r + 4) (r + 5) nd r)
  (.seq (.prim (.frag (.nconst (r + 4) 0)))
  (.seq (xmapE L (o + 1) (o + 40) (.arr (a + 15) (r + 4)) (a + 1) (r + 4) r (r + 5) (r + 25) r)
  (.seq (toX (VL.sop2 L .mul o o (o + 35)))
  (.seq (toX (VL.sop2 L .mul (o + 14) (o + 14) (o + 35)))
  (.seq (toX (VL.sop2 L .mul (o + 15) (o + 15) (o + 35)))
  (toX (VL.sop2 L .add (o + 15) (o + 15) (o + 15)))))))))))

/-- The units of `xstageC`. -/
abbrev stageCK (d : ℕ) : ℕ :=
  d * (d * 10 + 9) + 4 + (1 + (d * (7 + 6) + 3 + (matmulK d + (1 + (d * d * (2 + 6) + 3 + (1 + (1 + (1 + 1))))))))

/-- The slots `xstageC` may change. -/
abbrev stcS (o : ℕ) (y : ℕ) : Prop := y = o ∨ y = o + 14 ∨ y = o + 15 ∨ y = o + 20 ∨ o + 40 ≤ y

/-- The registers `xstageC` may change. -/
abbrev stcN (r : ℕ) (j : ℕ) : Prop := j = r + 4 ∨ j = r + 5 ∨ j = r + 7 ∨ j = r + 11 ∨ j = r + 16

/-- The cells `xstageC` may change. -/
abbrev stcA (d a : ℕ) (b c : ℕ) : Prop :=
  (b = a ∨ a + 12 ≤ b ∧ b < a + 15) ∧ c < d ∨ (b = a + 1 ∨ b = a + 15) ∧ c < d * d

set_option maxHeartbeats 4000000 in
theorem XV.stageC {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {o r a nd Gc e E : ℕ} {P : StZ d} {S : PosZ d} {Q : ℤ}
    (hS : o + 45 ≤ L.NS) (hN : r + 26 ≤ L.NN) (hA : a + 16 ≤ L.NA) (hnd : nd < r)
    (hσd : σ.nat nd = d) (hσ1 : σ.nat r = 1) (hσdd : σ.nat (r + 25) = d * d)
    (eZ : σ.sc (o + 1) = 0) (eO : σ.sc (o + 2) = 1) (eD : σ.sc o = P.D) (eP : σ.sc (o + 14) = ((2 ^ e : ℤ) : ℝ))
    (eQ : σ.sc (o + 15) = Q) (eG : σ.sc (o + 35) = ((2 ^ Gc : ℤ) : ℝ))
    (eMu : ∀ l : Fin d, σ.arr a l = P.mu l) (eT : ∀ i l : Fin d, σ.arr (a + 1) (d * i + l) = P.T i l)
    (eS1 : ∀ l : Fin d, σ.arr (a + 4) l = S.1 l) (eS2 : ∀ i l : Fin d, σ.arr (a + 5) (d * i + l) = S.2 i l)
    (bMu : ∀ l, |P.mu l| ≤ 2 ^ E) (bT : ∀ i l, |P.T i l| ≤ 2 ^ E) (bS1 : ∀ l, |S.1 l| ≤ 2 ^ E)
    (bS2 : ∀ i l, |S.2 i l| ≤ 2 ^ E) (bD : |P.D| ≤ 2 ^ E) (bP : e ≤ E) (bQ : |Q| ≤ 2 ^ E) (bG : Gc ≤ E)
    (hE : 4 * E + 3 * d + 4 < ℓ) :
    XRunsB L X ℓa ℓ (xstageC L o r a nd) σ (stageCK d) (fun σ' =>
      (∀ l : Fin d, σ'.arr a l = (tzComp P S Gc).mu l) ∧
      (∀ i l : Fin d, σ'.arr (a + 1) (d * i + l) = (tzComp P S Gc).T i l) ∧
      σ'.sc o = (tzComp P S Gc).D ∧ σ'.sc (o + 14) = ((2 ^ (e + Gc) : ℤ) : ℝ) ∧
      σ'.sc (o + 15) = ((2 * (Q * 2 ^ Gc) : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (stcS o) (stcN r) (stcA d a) σ σ') := by
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  have hda : d * d + d < 2 ^ ℓa := asz_lt hL (show a < L.NA by omega)
  have hcd : ∀ k < d, k < asz d := fun k hk => by unfold asz; nlinarith
  have hdl : ∀ F, 2 * F + d < ℓ → d * 2 ^ (2 * F) < 2 ^ ℓ := fun F hF => by
    have h2 : d < 2 ^ d := Nat.lt_two_pow_self
    calc d * 2 ^ (2 * F) ≤ 2 ^ d * 2 ^ (2 * F) := Nat.mul_le_mul_right _ h2.le
      _ = 2 ^ (2 * F + d) := by rw [← pow_add]; ring_nf
      _ < 2 ^ ℓ := Nat.pow_lt_pow_right (by norm_num) hF
  have bW : ∀ l, |(P.T *ᵥ S.1) l| ≤ 2 ^ (2 * E + d) := abs_mulVec_le bT bS1
  have bTS : ∀ i l, |(P.T * S.2) i l| ≤ 2 ^ (2 * E + d) := abs_matmul_le bT bS2
  have bGE : |(2 : ℤ) ^ Gc| ≤ 2 ^ E := abs_two_pow_le bG
  -- `w := T̂ Ŝ_μ` into `a + 12`
  refine XV.seq (XV.matvec hL (z := o + 1) (r := o + 20) (t := o + 40) (aM := a + 1) (ax := a + 4) (ay := a + 12)
    (ni := r + 7) (nr := r + 4) (nk := r + 5) (nd := nd) (none := r) (E := E) (M := P.T) (x := S.1) (by omega)
    (by omega) (by omega) (by omega) eZ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
    (by simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
      and_true, not_false_eq_true]; omega) hσd hσ1 eT eS1 bT bS1 (by omega) (hdl E (by omega)))
    fun σ1 ⟨w1, d1, F1⟩ => ?_
  have n1 : ∀ j, j ≠ r + 7 → j ≠ r + 5 → j ≠ r + 4 → σ1.nat j = σ.nat j := fun j h h' h'' => F1.1 j (by omega)
  -- `μ̂ := μ̂ 2^{G_c} + w`
  refine XV.seq (XV.nconst hL (show r + 4 < L.NN by omega) 0 (by positivity)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.mapE hL (z := o + 1) (t := o + 40) (e := ieMuC a (a + 12) (o + 35) (r + 4)) (aB := a)
    (nr := r + 4) (nst := r) (nk := r + 5) (nn := nd) (none := r) (E := 2 * E + d) (N := d) (base := 0) (st := 1)
    (F := fun k => vext (tzComp P S Gc).mu k)
    (by simp only [ieMuC, IE.WF, ne_eq, reduceCtorEq, not_false_eq_true, true_and]; omega)
    (by omega) (by simp only [ieMuC, IE.scr]; omega)
    (by rw [Env.setNat_sc, F1.2.1 (o + 1) (by omega), eZ]) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)
    (by simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
      and_true, not_false_eq_true]; omega) (by omega) (by omega)
    (by rw [nat_setNat_ne _ (by omega), n1 nd (by omega) (by omega) (by omega), hσd])
    (by rw [nat_setNat_ne _ (by omega), n1 r (by omega) (by omega) (by omega), hσ1])
    (by rw [nat_setNat_eq])
    (by rw [nat_setNat_ne _ (by omega), n1 r (by omega) (by omega) (by omega), hσ1]) one_pos
    (fun k hk => by rw [zero_add, one_mul]; exact hcd k hk) (by omega) (by omega) hsa
    (by simp only [ieMuC, IE.top, IE.mag]; omega) (fun k hk σ' F' _ _ hr' => ?_))
    fun σ3 ⟨m3, _, d3, F3⟩ => ?_
  · have hk'' : σ'.nat (r + 4) = k := by rw [hr']; ring
    have va : σ'.arr a k = P.mu ⟨k, hk⟩ := by
      rw [F'.2.2.1 a k (by omega), Env.setNat_arr, F1.2.2.1 a k (by omega)]; exact eMu ⟨k, hk⟩
    have vg : σ'.sc (o + 35) = ((2 ^ Gc : ℤ) : ℝ) := by
      rw [F'.2.1 (o + 35) (by omega), Env.setNat_sc, F1.2.1 (o + 35) (by omega), eG]
    have vw : σ'.arr (a + 12) k = (P.T *ᵥ S.1) ⟨k, hk⟩ := by
      rw [F'.2.2.1 (a + 12) k (by omega), Env.setNat_arr]; exact w1 ⟨k, hk⟩
    refine ⟨⟨⟨⟨by rw [hk'']; exact hcd k hk, P.mu ⟨k, hk⟩, by rw [hk'', va], abs_le_mono (bMu _) (by omega)⟩,
      2 ^ Gc, vg, abs_le_mono bGE (by omega)⟩, by rw [hk'']; exact hcd k hk, _, by rw [hk'', vw], bW _⟩, ?_⟩
    simp only [ieMuC, IE.eval, RealRAM.Op2.eval, hk'', va, vg, vw, vext_lt _ hk, tzComp]
    push_cast; ring
  have n3 : ∀ j, j ≠ r + 7 → j ≠ r + 5 → j ≠ r + 4 → σ3.nat j = σ.nat j := fun j h h' h'' => by
    rw [F3.1 j (by omega), nat_setNat_ne _ h'', n1 j h h' h'']
  have s3 : ∀ y, y ≠ o + 20 → y < o + 40 → σ3.sc y = σ.sc y := fun y h h' => by
    rw [F3.2.1 y (by omega), Env.setNat_sc, F1.2.1 y (by omega)]
  have a3 : ∀ b c, b ≠ a → b ≠ a + 12 → σ3.arr b c = σ.arr b c := fun b c h h' => by
    rw [F3.2.2.1 b c (by omega), Env.setNat_arr, F1.2.2.1 b c (by omega)]
  -- `T̂ := T̂ Ŝ_T` into `a + 15`
  refine XV.seq (XV.matmul hL (z := o + 1) (r := o + 20) (t := o + 40) (s1 := o + 2) (aT := a + 1) (aS := a + 5)
    (aE := a + 12) (aU := a + 13) (aV := a + 14) (aP := a + 15) (nri := r + 11) (nb := r + 16) (ni := r + 7)
    (nr := r + 4) (nk := r + 5) (nd := nd) (none := r) (E := E) (T := P.T) (S := S.2) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by rw [s3 (o + 1) (by omega) (by omega), eZ])
    (by rw [s3 (o + 2) (by omega) (by omega), eO])
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [n3 nd (by omega) (by omega) (by omega), hσd]) (by rw [n3 r (by omega) (by omega) (by omega), hσ1]) hda
    (fun i l => by rw [a3 (a + 1) (d * i + l) (by omega) (by omega), eT])
    (fun i l => by rw [a3 (a + 5) (d * i + l) (by omega) (by omega), eS2]) bT bS2 (by omega))
    fun σ4 ⟨p4, d4, F4⟩ => ?_
  have n4 : ∀ j, ¬ stcN r j → σ4.nat j = σ.nat j := fun j h => by
    simp only [stcN] at h
    rw [F4.1 j (by omega), n3 j (by omega) (by omega) (by omega)]
  -- copy `a + 15` into `a + 1`
  refine XV.seq (XV.nconst hL (show r + 4 < L.NN by omega) 0 (by positivity)) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.mapE hL (z := o + 1) (t := o + 40) (e := .arr (a + 15) (r + 4)) (aB := a + 1) (nr := r + 4)
    (nst := r) (nk := r + 5) (nn := r + 25) (none := r) (E := 2 * E + d) (N := d * d) (base := 0) (st := 1)
    (F := tmext (P.T * S.2)) (by simp only [IE.WF]; omega) (by omega) (by simp only [IE.scr]; omega)
    (by rw [Env.setNat_sc, F4.2.1 (o + 1) (by omega), s3 (o + 1) (by omega) (by omega), eZ]) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
    (by simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
      and_true, not_false_eq_true]; omega) (by omega) (by omega)
    (by rw [nat_setNat_ne _ (by omega), n4 (r + 25) (by simp only [stcN]; omega), hσdd])
    (by rw [nat_setNat_ne _ (by omega), n4 r (by simp only [stcN]; omega), hσ1])
    (by rw [nat_setNat_eq])
    (by rw [nat_setNat_ne _ (by omega), n4 r (by simp only [stcN]; omega), hσ1]) one_pos
    (fun k hk => by unfold asz; omega) (by omega) (by omega) hsa (by simp only [IE.top]; omega)
    (fun k hk σ' F' _ _ hr' => ?_)) fun σ6 ⟨m6, _, d6, F6⟩ => ?_
  · have hk'' : σ'.nat (r + 4) = k := by rw [hr']; ring
    have vp : σ'.arr (a + 15) k = tmext (P.T * S.2) k := by
      rw [F'.2.2.1 (a + 15) k (by omega), Env.setNat_arr]
      exact mat_cells p4 k hk
    exact ⟨⟨by rw [hk'']; unfold asz; omega, _, by rw [hk'', vp], tmext_abs_le (by positivity) bTS k⟩,
      by simp only [IE.eval, hk'', vp]⟩
  have s6 : ∀ y, y ≠ o + 20 → y < o + 40 → σ6.sc y = σ.sc y := fun y h h' => by
    rw [F6.2.1 y (by omega), Env.setNat_sc, F4.2.1 y (by omega), s3 y h h']
  -- the slots
  have vD : σ6.sc o = P.D := by rw [s6 o (by omega) (by omega), eD]
  have vG : σ6.sc (o + 35) = ((2 ^ Gc : ℤ) : ℝ) := by rw [s6 (o + 35) (by omega) (by omega), eG]
  have vP : σ6.sc (o + 14) = ((2 ^ e : ℤ) : ℝ) := by rw [s6 (o + 14) (by omega) (by omega), eP]
  have vQ : σ6.sc (o + 15) = Q := by rw [s6 (o + 15) (by omega) (by omega), eQ]
  refine XV.seq (XV.sop2 hL (x := o) (a := o) (b := o + 35) (by omega) (by omega) (by omega) .mul
    (by intro h; cases h) (by rw [vD]; exact tabsR_lt bD (by omega)) (by rw [vG]; exact tabsR_lt bGE (by omega))
    (by rw [vD, vG]; simp only [RealRAM.Op2.eval]; rw [← Int.cast_mul]
        exact tabsR_lt (absI_mul_le bD bGE) (by omega))) fun σ7 e7 => ?_
  have s7 : ∀ y, y ≠ o → σ7.sc y = σ6.sc y := fun y h => by rw [e7, sc_setSc_ne _ h]
  have v7 : σ7.sc o = ((P.D * 2 ^ Gc : ℤ) : ℝ) := by
    rw [e7, sc_setSc_eq, vD, vG]; simp only [RealRAM.Op2.eval]; push_cast; ring
  refine XV.seq (XV.sop2 hL (x := o + 14) (a := o + 14) (b := o + 35) (by omega) (by omega) (by omega) .mul
    (by intro h; cases h) (by rw [s7 (o + 14) (by omega), vP]; exact tabsR_lt (abs_two_pow_le bP) (by omega))
    (by rw [s7 (o + 35) (by omega), vG]; exact tabsR_lt bGE (by omega))
    (by rw [s7 (o + 14) (by omega), s7 (o + 35) (by omega), vP, vG]; simp only [RealRAM.Op2.eval]
        rw [← Int.cast_mul]; exact tabsR_lt (absI_mul_le (abs_two_pow_le bP) bGE) (by omega))) fun σ8 e8 => ?_
  have s8 : ∀ y, y ≠ o + 14 → σ8.sc y = σ7.sc y := fun y h => by rw [e8, sc_setSc_ne _ h]
  have v8 : σ8.sc (o + 14) = ((2 ^ (e + Gc) : ℤ) : ℝ) := by
    rw [e8, sc_setSc_eq, s7 (o + 14) (by omega), s7 (o + 35) (by omega), vP, vG]
    simp only [RealRAM.Op2.eval]; push_cast; ring
  refine XV.seq (XV.sop2 hL (x := o + 15) (a := o + 15) (b := o + 35) (by omega) (by omega) (by omega) .mul
    (by intro h; cases h)
    (by rw [s8 (o + 15) (by omega), s7 (o + 15) (by omega), vQ]; exact tabsR_lt bQ (by omega))
    (by rw [s8 (o + 35) (by omega), s7 (o + 35) (by omega), vG]; exact tabsR_lt bGE (by omega))
    (by rw [s8 (o + 15) (by omega), s7 (o + 15) (by omega), s8 (o + 35) (by omega), s7 (o + 35) (by omega), vQ, vG]
        simp only [RealRAM.Op2.eval]
        rw [← Int.cast_mul]; exact tabsR_lt (absI_mul_le bQ bGE) (by omega))) fun σ9 e9 => ?_
  have s9 : ∀ y, y ≠ o + 15 → σ9.sc y = σ8.sc y := fun y h => by rw [e9, sc_setSc_ne _ h]
  have v9 : σ9.sc (o + 15) = ((Q * 2 ^ Gc : ℤ) : ℝ) := by
    rw [e9, sc_setSc_eq, s8 (o + 15) (by omega), s7 (o + 15) (by omega), s8 (o + 35) (by omega),
      s7 (o + 35) (by omega), vQ, vG]
    simp only [RealRAM.Op2.eval]; push_cast; ring
  have hA9 : σ9.arr = σ6.arr := by rw [e9, e8, e7]; rfl
  have hD9 : σ9.draws = σ6.draws := by rw [e9, e8, e7]; rfl
  have G6 : FrameA (stcS o) (stcN r) (stcA d a) σ σ6 :=
    ((((F1.mono (fun y h => by simp only [stcS]; omega) (fun j h => by simp only [stcN]; omega)
      (fun b c h => by simp only [stcA]; omega)).setNat (Or.inl rfl) 0).trans
      (F3.mono (fun y h => by simp only [stcS]; omega) (fun j h => by simp only [stcN]; omega)
        (fun b c h => by simp only [stcA]; omega))).trans
      (F4.mono (fun y h => by simp only [stcS]; omega) (fun j h => by simp only [stcN]; omega)
        (fun b c h => by simp only [stcA]; omega))).setNat (Or.inl rfl) 0 |>.trans
      (F6.mono (fun y h => by simp only [stcS]; omega) (fun j h => by simp only [stcN]; omega)
        (fun b c h => by simp only [stcA]; omega))
  have G9 : FrameA (stcS o) (stcN r) (stcA d a) σ σ9 := by
    rw [e9, e8, e7]
    exact ((G6.setSc (Or.inl rfl) _).setSc
      (Or.inr (Or.inl rfl)) _).setSc (Or.inr (Or.inr (Or.inl rfl))) _
  have a6 : ∀ b c, b ≠ a + 1 → σ6.arr b c = σ4.arr b c := fun b c h => by
    rw [F6.2.2.1 b c (by omega), Env.setNat_arr]
  refine XV.mono (XV.sop2 hL (x := o + 15) (a := o + 15) (b := o + 15) (by omega) (by omega) (by omega) .add
    (by intro h; cases h) (by rw [v9]; exact tabsR_lt (absI_mul_le bQ bGE) (by omega))
    (by rw [v9]; exact tabsR_lt (absI_mul_le bQ bGE) (by omega))
    (by rw [v9]; simp only [RealRAM.Op2.eval]; rw [← Int.cast_add]
        exact tabsR_lt (absI_add_le (absI_mul_le bQ bGE) (absI_mul_le bQ bGE)) (by omega))) le_rfl ?_
  rintro σ' rfl
  refine ⟨fun l => ?_, fun i l => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := m3 l l.2; rw [zero_add, one_mul] at this
    rw [Env.setSc_arr, hA9, a6 a l (by omega), F4.2.2.1 a l (by omega), this]
    rw [vext_lt _ l.2]
  · rw [Env.setSc_arr, hA9]
    have := m6 (d * i + l) (cell_dil i l)
    rw [zero_add, one_mul] at this
    rw [this, tmext_cell]; rfl
  · rw [sc_setSc_ne _ (by omega), s9 o (by omega), s8 o (by omega), v7]; rfl
  · rw [sc_setSc_ne _ (by omega), s9 (o + 14) (by omega), v8]
  · rw [sc_setSc_eq, v9]; simp only [RealRAM.Op2.eval]; push_cast; ring
  · rw [Env.setSc_draws, hD9, d6, Env.setNat_draws, d4, d3, Env.setNat_draws, d1]
  · exact G9.setSc (Or.inr (Or.inr (Or.inl rfl))) _

/-! ## One stage -/

/-- The row command at the layout of the core: row `k` (in `r + 3`) into `a + 9` and `o + 19`, read in the position of
denominator `D` (slot `o`), with `2^e` in `o + 14`, `2^j D` in `o + 15` and `m` in `r + 26`. -/
def xrowAt (L : Layout) (o r a nd aC : ℕ) : XCmd :=
  xrowK L (o + 29) (o + 30) (o + 31) (o + 32) (o + 19) o (a + 9) aC (o + 1) (o + 33) (o + 14) (o + 15)
    (r + 8) (r + 9) (r + 10) nd (r + 1) (r + 3) (r + 26) (r + 7) (r + 6) r

/-- One stage: the core on the rows read in the position, then the composition. -/
def xstage (L : Layout) (o r a nd aC : ℕ) : XCmd :=
  .seq (xcore L (xrowAt L o r a nd aC) o r a nd) (xstageC L o r a nd)

/-- The units of a stage. -/
abbrev stageK (d M N B : ℕ) : ℕ := coreK d M N B + stageCK d

/-- The slots a stage may change. -/
abbrev sgS (o : ℕ) (y : ℕ) : Prop := y = o ∨ y = o + 14 ∨ y = o + 15 ∨ o + 16 ≤ y ∧ y < o + 35 ∨ o + 40 ≤ y

/-- The registers a stage may change. -/
abbrev sgN (r : ℕ) (j : ℕ) : Prop := r + 3 ≤ j ∧ j < r + 12 ∨ r + 13 ≤ j ∧ j < r + 24

/-- The cells a stage may change. -/
abbrev sgA (d a : ℕ) (b k : ℕ) : Prop := a ≤ b ∧ b < a + 16 ∧ k < d * d + d

/-- The core output of a stage at the position `P`, with `2^e = D/D_c` and the half-width `2^j`. -/
def stSum {m : ℕ} (c : DC) (P : StZ d) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (ch : Fin d → ℤ)
    (e j B N : ℕ) (cs : ℕ → Bool) (c0 : ℕ) : PosZ d :=
  tzSum c P.T P.mu (onN (tzRowA A b)) (onN (tzRowB A b ch e j P.D)) (m + (d + d)) (tzYc cs B c0) N

set_option maxHeartbeats 4000000 in
theorem XV.stage {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa)
    {o r a nd aC n m N B E e j Gc : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} {ch : Fin d → ℤ}
    {c : DC} {P : StZ d}
    (hXi : ∀ k : ℕ, X.inp k = BitRAM.inputMem d n m A b k) (hXo : X.off = 3 + 2 * (d + 1) * m)
    (hS : o + 113 ≤ L.NS) (hN : r + 27 ≤ L.NN) (hA : a + 16 ≤ L.NA) (hnd : nd < r) (haC : aC < a)
    (hσd : σ.nat nd = d) (hσ1 : σ.nat r = 1) (hσd1 : σ.nat (r + 1) = d + 1) (hσM : σ.nat (r + 2) = m + (d + d))
    (hσB : σ.nat (r + 12) = B) (hσN : σ.nat (r + 24) = N) (hσdd : σ.nat (r + 25) = d * d)
    (hσm : σ.nat (r + 26) = m)
    (hka : 4 + 2 * ((d + 1) * (m + 1)) < 2 ^ ℓa) (hMa : m + (d + d) < 2 ^ ℓa) (hNa : N < 2 ^ ℓa)
    (hB1 : 1 ≤ B) (hBa : 4 * gsm_prec B + 2 < 2 ^ ℓa)
    (eZ : σ.sc (o + 1) = 0) (eO : σ.sc (o + 2) = 1) (eM : σ.sc (o + 3) = -1)
    (ePB : σ.sc (o + 4) = c.PB) (eP2 : σ.sc (o + 5) = c.P2) (ePG : σ.sc (o + 6) = c.PG)
    (ePj : σ.sc (o + 7) = c.Pj) (eR : σ.sc (o + 8) = c.R) (eMR : σ.sc (o + 9) = -c.R)
    (eAl : σ.sc (o + 10) = c.Al) (eBh : σ.sc (o + 11) = c.Bh) (eMB : σ.sc (o + 12) = ((-c.Bh : ℤ) : ℝ))
    (eD8 : σ.sc (o + 13) = ((8 * c.dd : ℤ) : ℝ))
    (eD : σ.sc o = P.D) (eP : σ.sc (o + 14) = ((2 ^ e : ℤ) : ℝ)) (eQ : σ.sc (o + 15) = ((2 ^ j * P.D : ℤ) : ℝ))
    (eG : σ.sc (o + 35) = ((2 ^ Gc : ℤ) : ℝ))
    (eMu : ∀ l : Fin d, σ.arr a l = P.mu l) (eT : ∀ i l : Fin d, σ.arr (a + 1) (d * i + l) = P.T i l)
    (eC : ∀ i : Fin d, σ.arr aC (i + 1) = ch i)
    (hR : 0 ≤ c.R) (hRB : c.R ≤ c.Bh) (hAl : 0 < c.Al) (hAB : c.Al ≤ c.Bh) (hPG : 0 ≤ c.PG)
    (hPGB : c.PG ≤ c.Bh) (hD1 : 1 ≤ P.D)
    (bT : ∀ i l, |P.T i l| ≤ 2 ^ E) (bMu : ∀ l, |P.mu l| ≤ 2 ^ E) (bC : ∀ i, |ch i| ≤ 2 ^ E)
    (bD : |P.D| ≤ 2 ^ E) (bP : e ≤ E) (bQ : |2 ^ j * P.D| ≤ 2 ^ E) (bG : Gc ≤ E)
    (bRA : ∀ k l, |onN (tzRowA A b) k l| ≤ 2 ^ E) (bRB : ∀ k, |onN (tzRowB A b ch e j P.D) k| ≤ 2 ^ E)
    (bPB : |c.PB| ≤ 2 ^ E) (bP2 : |c.P2| ≤ 2 ^ E) (bPj : |c.Pj| ≤ 2 ^ E)
    (bBh : c.Bh ≤ 2 ^ E) (bD8 : |8 * c.dd| ≤ 2 ^ E) (b4p : 4 * gsm_prec B ≤ E) (bN : N ≤ 2 ^ E)
    (bNB : (N : ℤ) * c.Bh ≤ 2 ^ E) (hb : (frMhat A b : ℤ) ^ (d + 2) * P.D < 2 ^ ℓ)
    (hE : 48 * E + 42 * d + 32 < ℓ) :
    XRunsB L X ℓa ℓ (xstage L o r a nd aC) σ (stageK d (m + (d + d)) N B) (fun σ' =>
      (∀ l : Fin d, σ'.arr a l = (tzComp P (stSum c P A b ch e j B N X.wb.cs σ.draws) Gc).mu l) ∧
      (∀ i l : Fin d, σ'.arr (a + 1) (d * i + l) = (tzComp P (stSum c P A b ch e j B N X.wb.cs σ.draws) Gc).T i l) ∧
      σ'.sc o = (tzComp P (stSum c P A b ch e j B N X.wb.cs σ.draws) Gc).D ∧
      σ'.sc (o + 14) = ((2 ^ (e + Gc) : ℤ) : ℝ) ∧
      σ'.sc (o + 15) = ((2 ^ (j + 1) * (tzComp P (stSum c P A b ch e j B N X.wb.cs σ.draws) Gc).D : ℤ) : ℝ) ∧
      σ'.draws = σ.draws + 2 * B * d * N ∧ FrameA (sgS o) (sgN r) (sgA d a) σ σ') := by
  have hda : d * d + d < 2 ^ ℓa := asz_lt hL (show a < L.NA by omega)
  have hBh0 : 0 ≤ c.Bh := hR.trans hRB
  -- the core
  refine XV.seq (XV.core hL (row := xrowAt L o r a nd aC) (o := o) (r := r) (a := a) (nd := nd)
    (M := m + (d + d)) (N := N) (B := B) (E := E) (c := c) (T := P.T) (mu := P.mu) (ra := onN (tzRowA A b))
    (rb := onN (tzRowB A b ch e j P.D)) hS (by omega) (by omega) hnd hσd hσ1 hσd1 hσM hσB hσN hσdd hda hMa hNa
    hB1 hBa eZ eO eM ePB eP2 ePG ePj eR eMR eAl eBh eMB eD8 eMu eT ?_ hR hRB hAl hAB hPG hPGB bT bMu
    (fun k _ l => bRA k l) (fun k _ => bRB k) bPB bP2 bPj bBh bD8 b4p bN hE) fun σ1 ⟨s1, s2, d1, F1⟩ => ?_
  · intro k hk σ' F' hk'
    have n' : ∀ q, ¬ coN r q → σ'.nat q = σ.nat q := fun q h => F'.1 q h
    have s' : ∀ y, ¬ coS o y → σ'.sc y = σ.sc y := fun y h => F'.2.1 y h
    refine XV.mono (XV.rowK hL (k := k) (e := e) (js := j) (E := E) (n := n) (m := m) (A := A) (b := b) (ch := ch)
      (D := P.D) hXi hXo hk (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
      (by simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
        and_true, not_false_eq_true]; omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
        and_true, not_false_eq_true]; omega)
      (by rw [n' nd (by simp only [coN]; omega), hσd]) (by rw [n' (r + 1) (by simp only [coN]; omega), hσd1]) hk'
      (by rw [n' (r + 26) (by simp only [coN]; omega), hσm]) (by rw [n' r (by simp only [coN]; omega), hσ1])
      (by rw [s' o (by simp only [coS]; omega), eD]) (by rw [s' (o + 1) (by simp only [coS]; omega), eZ])
      (by rw [s' (o + 14) (by simp only [coS]; omega), eP]) (by rw [s' (o + 15) (by simp only [coS]; omega), eQ])
      (fun i => by rw [F'.2.2.1 aC (i + 1) (by simp only [coA]; omega), eC]) hka hda (by omega) hD1 bC
      (pow_le_pow_right₀ (by norm_num) bP) bQ (by omega) hb)
      le_rfl ?_
    rintro σ'' ⟨h1, h2, h3, h4⟩
    exact ⟨fun l => by rw [h1 l]; simp [onN, hk], by rw [h2]; simp [onN, hk], h3, h4⟩
  -- the composition
  have n1 : ∀ q, ¬ coN r q → σ1.nat q = σ.nat q := fun q h => F1.1 q h
  have s1' : ∀ y, ¬ coS o y → σ1.sc y = σ.sc y := fun y h => F1.2.1 y h
  have bS := tzSum_bound (M := m + (d + d)) c P.T P.mu (onN (tzRowA A b)) (onN (tzRowB A b ch e j P.D))
    (tzYc X.wb.cs B σ.draws) hR hRB hAl hAB hPG hPGB N
  refine XV.mono (XV.stageC hL (o := o) (r := r) (a := a) (nd := nd) (Gc := Gc) (e := e) (E := E) (P := P)
    (S := stSum c P A b ch e j B N X.wb.cs σ.draws) (Q := 2 ^ j * P.D) (by omega) (by omega) hA hnd
    (by rw [n1 nd (by simp only [coN]; omega), hσd]) (by rw [n1 r (by simp only [coN]; omega), hσ1])
    (by rw [n1 (r + 25) (by simp only [coN]; omega), hσdd])
    (by rw [s1' (o + 1) (by simp only [coS]; omega), eZ]) (by rw [s1' (o + 2) (by simp only [coS]; omega), eO])
    (by rw [s1' o (by simp only [coS]; omega), eD]) (by rw [s1' (o + 14) (by simp only [coS]; omega), eP])
    (by rw [s1' (o + 15) (by simp only [coS]; omega), eQ]) (by rw [s1' (o + 35) (by simp only [coS]; omega), eG])
    (fun l => by rw [F1.2.2.1 a l (by simp only [coA]; omega), eMu])
    (fun i l => by rw [F1.2.2.1 (a + 1) _ (by simp only [coA]; omega), eT]) s1 s2 bMu bT
    (fun l => (bS.1 l).trans bNB) (fun i l => (bS.2 i l).trans bNB) bD bP bQ bG (by omega)) le_rfl ?_
  rintro σ2 ⟨m2, t2, D2, P2, Q2, d2, F2⟩
  refine ⟨m2, t2, D2, P2, by rw [Q2]; simp only [tzComp]; push_cast; ring, by rw [d2, d1], ?_⟩
  exact (F1.mono (fun y h => by simp only [coS] at h; simp only [sgS]; omega)
    (fun q h => by simp only [coN] at h; simp only [sgN]; omega)
    (fun b k h => by simp only [coA] at h; simp only [sgA]; omega)).trans
    (F2.mono (fun y h => by simp only [stcS] at h; simp only [sgS]; omega)
      (fun q h => by simp only [stcN] at h; simp only [sgN]; omega)
      (fun b k h => by simp only [stcA] at h; simp only [sgA]; omega))

end AdversarialBco.Bit.Transfer
