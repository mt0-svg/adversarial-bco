/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XEllConst

@[expose] public section

/-!
# Straight-line code with tables of values

The constants of ELL-R take some seventy steps of straight-line code, each writing one fresh register or slot. The
tables `RegsAre σ l` and `ScAre σ l` record the values of the registers and slots written so far (pairs of an index and
a value); each step adds its pair in front, the others survive because the index is fresh. The step rules below read
their arguments from the tables.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach

variable {d : ℕ}

/-- The registers of the table hold their values. -/
def RegsAre (σ : Env d) (l : List (ℕ × ℕ)) : Prop := ∀ p ∈ l, σ.nat p.1 = p.2

/-- The slots of the table hold their values. -/
def ScAre (σ : Env d) (l : List (ℕ × ℝ)) : Prop := ∀ p ∈ l, σ.sc p.1 = p.2

theorem RegsAre.get {σ : Env d} {l : List (ℕ × ℕ)} (h : RegsAre σ l) {i v : ℕ} (hm : (i, v) ∈ l) : σ.nat i = v :=
  h _ hm

theorem ScAre.get {σ : Env d} {l : List (ℕ × ℝ)} (h : ScAre σ l) {i : ℕ} {v : ℝ} (hm : (i, v) ∈ l) : σ.sc i = v :=
  h _ hm

theorem RegsAre.frame {σ σ' : Env d} {l : List (ℕ × ℕ)} {S N : ℕ → Prop} {Ar : ℕ → ℕ → Prop} (h : RegsAre σ l)
    (hF : FrameA S N Ar σ σ') (hl : ∀ p ∈ l, ¬ N p.1) : RegsAre σ' l := fun p hp => by
  rw [hF.1 _ (hl p hp), h p hp]

theorem RegsAre.cons {σ σ' : Env d} {l : List (ℕ × ℕ)} {S : ℕ → Prop} {Ar : ℕ → ℕ → Prop} {i v : ℕ}
    (h : RegsAre σ l) (hF : FrameA S (fun j => j = i) Ar σ σ') (hl : ∀ p ∈ l, p.1 ≠ i) (hv : σ'.nat i = v) :
    RegsAre σ' ((i, v) :: l) := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact hv
  · rw [hF.1 _ (hl p hp), h p hp]

namespace XV

variable {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d}

/-! ## Register steps -/

theorem nconstA (hL : LayOK L d ℓa) {i : ℕ} (hi : i < L.NN) (c : ℕ) (hc : c < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (.prim (.frag (.nconst i c))) σ 1 (fun σ' => σ'.nat i = c ∧ σ'.draws = σ.draws ∧
      FrameA (fun _ => False) (fun j => j = i) (fun _ _ => False) σ σ') :=
  mono (nconst hL hi c hc) le_rfl fun _ e => by
    subst e; exact ⟨by simp, rfl, (FrameA.refl (fun _ => False) (fun j => j = i) (fun _ _ => False) σ).setNat rfl _⟩

theorem naddA (hL : LayOK L d ℓa) {i a b : ℕ} (hi : i < L.NN) (ha : a < L.NN) (hb : b < L.NN) {va vb : ℕ}
    (hva : σ.nat a = va) (hvb : σ.nat b = vb) (hab : va + vb < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (.prim (.frag (.nadd i a b))) σ 1 (fun σ' => σ'.nat i = va + vb ∧ σ'.draws = σ.draws ∧
      FrameA (fun _ => False) (fun j => j = i) (fun _ _ => False) σ σ') :=
  mono (nadd hL hi ha hb (by omega) (by omega)) le_rfl fun _ e => by
    subst e; exact ⟨by simp [hva, hvb], rfl, (FrameA.refl (fun _ => False) (fun j => j = i) (fun _ _ => False) σ).setNat rfl _⟩

theorem nmulA (hL : LayOK L d ℓa) {i a b : ℕ} (hi : i < L.NN) (ha : a < L.NN) (hb : b < L.NN) {va vb : ℕ}
    (hva : σ.nat a = va) (hvb : σ.nat b = vb) (hva' : va < 2 ^ ℓa) (hvb' : vb < 2 ^ ℓa) (hab : va * vb < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xnmul i a b) σ 1 (fun σ' => σ'.nat i = va * vb ∧ σ'.draws = σ.draws ∧
      FrameA (fun _ => False) (fun j => j = i) (fun _ _ => False) σ σ') :=
  mono (nmul hL hi ha hb (by rw [hva]; exact hva') (by rw [hvb]; exact hvb') (by rw [hva, hvb]; exact hab)) le_rfl
    fun _ e => by subst e; exact ⟨by simp [hva, hvb], rfl, (FrameA.refl (fun _ => False) (fun j => j = i) (fun _ _ => False) σ).setNat rfl _⟩

theorem nsubA (hL : LayOK L d ℓa) {i a b : ℕ} (hi : i < L.NN) (ha : a < L.NN) (hb : b < L.NN) {va vb : ℕ}
    (hva : σ.nat a = va) (hvb : σ.nat b = vb) (hva' : va < 2 ^ ℓa) (hba : vb ≤ va) :
    XRunsB L X ℓa ℓ (.prim (.frag (.nsub i a b))) σ 1 (fun σ' => σ'.nat i = va - vb ∧ σ'.draws = σ.draws ∧
      FrameA (fun _ => False) (fun j => j = i) (fun _ _ => False) σ σ') :=
  mono (nsub hL hi ha hb (by omega) (by omega) (by omega)) le_rfl fun _ e => by
    subst e; exact ⟨by simp [hva, hvb], rfl, (FrameA.refl (fun _ => False) (fun j => j = i) (fun _ _ => False) σ).setNat rfl _⟩

/-! ## Slot steps -/

theorem ncastA (hL : LayOK L d ℓa) {x i : ℕ} (hx : x < L.NS) (hi : i < L.NN) {v : ℕ} (hv : σ.nat i = v)
    (hva : v < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (toX (VL.ncast L x i)) σ 1 (fun σ' => σ'.sc x = ((v : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = x) (fun _ => False) (fun _ _ => False) σ σ') :=
  mono (ncastI hL hx hi (by rw [hv]; exact hva)) le_rfl fun _ e => by
    subst e; exact ⟨by simp [hv], rfl, (FrameA.refl (fun y => y = x) (fun _ => False) (fun _ _ => False) σ).setSc rfl _⟩

theorem sconstA (hL : LayOK L d ℓa) {x : ℕ} (hx : x < L.NS) (v : ℤ) (hv : |v| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (toX (VL.sconst L x (v : ℚ))) σ 1 (fun σ' => σ'.sc x = ((v : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => y = x) (fun _ => False) (fun _ _ => False) σ σ') :=
  mono (sconst hL hx (v : ℚ) (by simp) (by rw [Rat.cast_intCast]; exact abs_int_lt hv)) le_rfl fun _ e => by
    subst e; exact ⟨by simp, rfl, (FrameA.refl (fun y => y = x) (fun _ => False) (fun _ _ => False) σ).setSc rfl _⟩

end XV


/-! ## The registers of ELL-R's constants -/

/-- The registers of ELL-R's constants, each written once: `d + 1` (`n0 + 14`), `d²` (`n0 + 15`),
`p = 6 + c₁ + 2j` (`n0 + 22`), `q = 9 + c_d + lg R̄ + 3λ + 2j` (`n0 + 30`), `N = 2d(d + 1)λ + 1` (`n0 + 7`), the
exponents `p + 1, 2p, 2p + 1` (`n0 + 34, 35, 36`), `p - 2j` (`n0 + 38`), `2q` (`n0 + 39`), `3λ + 1` (`n0 + 42`),
`6λ + 2` (`n0 + 45`); from `j, lg R̄, λ` in `n0 + 8, 9, 10`, `c₁ = lg(d²(d + 1))`, `c_d = lg d` in `n0 + 17, 18`. -/
def xellSetR (B : EllBlk) (n0 : ℕ) : XCmd :=
  (.seq (.prim (.frag (.nadd (n0 + 14) (B.rd) (n0 + 4))))
  (.seq (xnmul (n0 + 15) (B.rd) (B.rd))
  (.seq (.prim (.frag (.nconst (n0 + 19) 6)))
  (.seq (.prim (.frag (.nadd (n0 + 20) (n0 + 19) (n0 + 17))))
  (.seq (.prim (.frag (.nadd (n0 + 21) (n0 + 20) (n0 + 8))))
  (.seq (.prim (.frag (.nadd (n0 + 22) (n0 + 21) (n0 + 8))))
  (.seq (.prim (.frag (.nconst (n0 + 23) 9)))
  (.seq (.prim (.frag (.nadd (n0 + 24) (n0 + 23) (n0 + 18))))
  (.seq (.prim (.frag (.nadd (n0 + 25) (n0 + 24) (n0 + 9))))
  (.seq (.prim (.frag (.nadd (n0 + 26) (n0 + 25) (n0 + 10))))
  (.seq (.prim (.frag (.nadd (n0 + 27) (n0 + 26) (n0 + 10))))
  (.seq (.prim (.frag (.nadd (n0 + 28) (n0 + 27) (n0 + 10))))
  (.seq (.prim (.frag (.nadd (n0 + 29) (n0 + 28) (n0 + 8))))
  (.seq (.prim (.frag (.nadd (n0 + 30) (n0 + 29) (n0 + 8))))
  (.seq (xnmul (n0 + 31) (B.rd) (n0 + 14))
  (.seq (.prim (.frag (.nadd (n0 + 32) (n0 + 31) (n0 + 31))))
  (.seq (xnmul (n0 + 33) (n0 + 32) (n0 + 10))
  (.seq (.prim (.frag (.nadd (n0 + 7) (n0 + 33) (n0 + 4))))
  (.seq (.prim (.frag (.nadd (n0 + 34) (n0 + 22) (n0 + 4))))
  (.seq (.prim (.frag (.nadd (n0 + 35) (n0 + 22) (n0 + 22))))
  (.seq (.prim (.frag (.nadd (n0 + 36) (n0 + 35) (n0 + 4))))
  (.seq (.prim (.frag (.nadd (n0 + 37) (n0 + 8) (n0 + 8))))
  (.seq (.prim (.frag (.nsub (n0 + 38) (n0 + 22) (n0 + 37))))
  (.seq (.prim (.frag (.nadd (n0 + 39) (n0 + 30) (n0 + 30))))
  (.seq (.prim (.frag (.nadd (n0 + 40) (n0 + 10) (n0 + 10))))
  (.seq (.prim (.frag (.nadd (n0 + 41) (n0 + 40) (n0 + 10))))
  (.seq (.prim (.frag (.nadd (n0 + 42) (n0 + 41) (n0 + 4))))
  (.seq (.prim (.frag (.nadd (n0 + 43) (n0 + 41) (n0 + 41))))
  (.seq (.prim (.frag (.nadd (n0 + 44) (n0 + 43) (n0 + 4))))
  (.prim (.frag (.nadd (n0 + 45) (n0 + 44) (n0 + 4)))))))))))))))))))))))))))))))))

set_option maxHeartbeats 8000000 in
/-- The rule of `xellSetR`. -/
theorem XV.ellSetR {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : EllBlk}
    {n0 j cR lam c1 cd : ℕ} (hrd : B.rd < n0) (hN : n0 + 46 ≤ L.NN) (hd : 1 ≤ d) (h1 : σ.nat (n0 + 4) = 1)
    (hdv : σ.nat B.rd = d) (hj : σ.nat (n0 + 8) = j) (hcR : σ.nat (n0 + 9) = cR) (hl : σ.nat (n0 + 10) = lam)
    (hc1 : σ.nat (n0 + 17) = c1) (hcd : σ.nat (n0 + 18) = cd) (hlam : lam = cR + j)
    (hA1 : d * d < 2 ^ ℓa) (hA2 : (d * (d + 1) + d * (d + 1)) * lam + 1 < 2 ^ ℓa)
    (hA2' : d * (d + 1) + d * (d + 1) < 2 ^ ℓa)
    (hA3 : 2 * (9 + cd + cR + 3 * lam + 2 * j) + 6 * lam + 2 * (6 + c1 + 2 * j) + 20 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xellSetR B n0) σ 30 (fun σ' =>
      σ'.nat (n0 + 4) = 1 ∧ σ'.nat B.rd = d ∧ σ'.nat (n0 + 8) = j ∧ σ'.nat (n0 + 10) = lam ∧
      σ'.nat (n0 + 14) = d + 1 ∧ σ'.nat (n0 + 15) = d * d ∧ σ'.nat (n0 + 22) = 6 + c1 + 2 * j ∧
      σ'.nat (n0 + 30) = 9 + cd + cR + 3 * lam + 2 * j ∧ σ'.nat (n0 + 7) = 2 * d * (d + 1) * lam + 1 ∧
      σ'.nat (n0 + 34) = 6 + c1 + 2 * j + 1 ∧ σ'.nat (n0 + 35) = 2 * (6 + c1 + 2 * j) ∧
      σ'.nat (n0 + 36) = 2 * (6 + c1 + 2 * j) + 1 ∧ σ'.nat (n0 + 38) = 6 + c1 + 2 * j - 2 * j ∧
      σ'.nat (n0 + 39) = 2 * (9 + cd + cR + 3 * lam + 2 * j) ∧ σ'.nat (n0 + 42) = 3 * lam + 1 ∧
      σ'.nat (n0 + 45) = 6 * lam + 2 ∧ σ'.draws = σ.draws ∧
      FrameA (fun _ => False) (fun i => i = n0 + 7 ∨ (n0 + 14 ≤ i ∧ i ≤ n0 + 45)) (fun _ _ => False) σ σ') := by
  have hdd : d ≤ d * d := Nat.le_mul_of_pos_left d hd
  have hd1 : d + 1 ≤ d * (d + 1) := Nat.le_mul_of_pos_left (d + 1) hd
  have R0 : RegsAre σ [(n0 + 4, 1), (B.rd, d), (n0 + 8, j), (n0 + 9, cR), (n0 + 10, lam), (n0 + 17, c1),
      (n0 + 18, cd)] := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have H0 := FrameA.refl (fun _ => False) (fun i => i = n0 + 7 ∨ (n0 + 14 ≤ i ∧ i ≤ n0 + 45)) (fun _ _ => False) σ
  refine XV.mono (K := 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1)))))))))))))))))))))))))))))) ?_ (by norm_num) (fun _ h => h)
  refine XV.seq (XV.naddA hL (i := n0 + 14) (a := B.rd) (b := n0 + 4) (va := d) (vb := 1) (by omega)
    (by omega) (by omega) (R0.get (by simp)) (R0.get (by simp)) (by omega)) fun σ1 ⟨v1, d1, G1⟩ => ?_
  have R1 := R0.cons G1 (by simp <;> omega) v1
  have H1 := H0.trans (G1.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.nmulA hL (i := n0 + 15) (a := B.rd) (b := B.rd) (va := d) (vb := d) (by omega)
    (by omega) (by omega) (R1.get (by simp)) (R1.get (by simp)) (by omega) (by omega) (by omega))
    fun σ2 ⟨v2, d2, G2⟩ => ?_
  have R2 := R1.cons G2 (by simp <;> omega) v2
  have H2 := H1.trans (G2.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.nconstA hL (i := n0 + 19) (by omega) 6 (by omega)) fun σ3 ⟨v3, d3, G3⟩ => ?_
  have R3 := R2.cons G3 (by simp <;> omega) v3
  have H3 := H2.trans (G3.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.naddA hL (i := n0 + 20) (a := n0 + 19) (b := n0 + 17) (va := 6) (vb := c1) (by omega)
    (by omega) (by omega) (R3.get (by simp)) (R3.get (by simp)) (by omega)) fun σ4 ⟨v4, d4, G4⟩ => ?_
  have R4 := R3.cons G4 (by simp <;> omega) v4
  have H4 := H3.trans (G4.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.naddA hL (i := n0 + 21) (a := n0 + 20) (b := n0 + 8) (va := 6 + c1) (vb := j) (by omega)
    (by omega) (by omega) (R4.get (by simp)) (R4.get (by simp)) (by omega)) fun σ5 ⟨v5, d5, G5⟩ => ?_
  have R5 := R4.cons G5 (by simp <;> omega) v5
  have H5 := H4.trans (G5.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.naddA hL (i := n0 + 22) (a := n0 + 21) (b := n0 + 8) (va := 6 + c1 + j) (vb := j) (by omega)
    (by omega) (by omega) (R5.get (by simp)) (R5.get (by simp)) (by omega)) fun σ6 ⟨v6, d6, G6⟩ => ?_
  have R6 := R5.cons G6 (by simp <;> omega) v6
  have H6 := H5.trans (G6.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.nconstA hL (i := n0 + 23) (by omega) 9 (by omega)) fun σ7 ⟨v7, d7, G7⟩ => ?_
  have R7 := R6.cons G7 (by simp <;> omega) v7
  have H7 := H6.trans (G7.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.naddA hL (i := n0 + 24) (a := n0 + 23) (b := n0 + 18) (va := 9) (vb := cd) (by omega)
    (by omega) (by omega) (R7.get (by simp)) (R7.get (by simp)) (by omega)) fun σ8 ⟨v8, d8, G8⟩ => ?_
  have R8 := R7.cons G8 (by simp <;> omega) v8
  have H8 := H7.trans (G8.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.naddA hL (i := n0 + 25) (a := n0 + 24) (b := n0 + 9) (va := 9 + cd) (vb := cR) (by omega)
    (by omega) (by omega) (R8.get (by simp)) (R8.get (by simp)) (by omega)) fun σ9 ⟨v9, d9, G9⟩ => ?_
  have R9 := R8.cons G9 (by simp <;> omega) v9
  have H9 := H8.trans (G9.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.naddA hL (i := n0 + 26) (a := n0 + 25) (b := n0 + 10) (va := 9 + cd + cR) (vb := lam) (by omega)
    (by omega) (by omega) (R9.get (by simp)) (R9.get (by simp)) (by omega)) fun σ10 ⟨v10, d10, G10⟩ => ?_
  have R10 := R9.cons G10 (by simp <;> omega) v10
  have H10 := H9.trans (G10.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.naddA hL (i := n0 + 27) (a := n0 + 26) (b := n0 + 10) (va := 9 + cd + cR + lam) (vb := lam) (by omega)
    (by omega) (by omega) (R10.get (by simp)) (R10.get (by simp)) (by omega)) fun σ11 ⟨v11, d11, G11⟩ => ?_
  have R11 := R10.cons G11 (by simp <;> omega) v11
  have H11 := H10.trans (G11.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.naddA hL (i := n0 + 28) (a := n0 + 27) (b := n0 + 10) (va := 9 + cd + cR + lam + lam) (vb := lam) (by omega)
    (by omega) (by omega) (R11.get (by simp)) (R11.get (by simp)) (by omega)) fun σ12 ⟨v12, d12, G12⟩ => ?_
  have R12 := R11.cons G12 (by simp <;> omega) v12
  have H12 := H11.trans (G12.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.naddA hL (i := n0 + 29) (a := n0 + 28) (b := n0 + 8) (va := 9 + cd + cR + lam + lam + lam) (vb := j) (by omega)
    (by omega) (by omega) (R12.get (by simp)) (R12.get (by simp)) (by omega)) fun σ13 ⟨v13, d13, G13⟩ => ?_
  have R13 := R12.cons G13 (by simp <;> omega) v13
  have H13 := H12.trans (G13.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.naddA hL (i := n0 + 30) (a := n0 + 29) (b := n0 + 8) (va := 9 + cd + cR + lam + lam + lam + j) (vb := j) (by omega)
    (by omega) (by omega) (R13.get (by simp)) (R13.get (by simp)) (by omega)) fun σ14 ⟨v14, d14, G14⟩ => ?_
  have R14 := R13.cons G14 (by simp <;> omega) v14
  have H14 := H13.trans (G14.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.nmulA hL (i := n0 + 31) (a := B.rd) (b := n0 + 14) (va := d) (vb := d + 1) (by omega)
    (by omega) (by omega) (R14.get (by simp)) (R14.get (by simp)) (by omega) (by omega) (by omega))
    fun σ15 ⟨v15, d15, G15⟩ => ?_
  have R15 := R14.cons G15 (by simp <;> omega) v15
  have H15 := H14.trans (G15.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.naddA hL (i := n0 + 32) (a := n0 + 31) (b := n0 + 31) (va := d * (d + 1)) (vb := d * (d + 1)) (by omega)
    (by omega) (by omega) (R15.get (by simp)) (R15.get (by simp)) (by omega)) fun σ16 ⟨v16, d16, G16⟩ => ?_
  have R16 := R15.cons G16 (by simp <;> omega) v16
  have H16 := H15.trans (G16.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.nmulA hL (i := n0 + 33) (a := n0 + 32) (b := n0 + 10) (va := d * (d + 1) + d * (d + 1)) (vb := lam) (by omega)
    (by omega) (by omega) (R16.get (by simp)) (R16.get (by simp)) (by omega) (by omega) (by omega))
    fun σ17 ⟨v17, d17, G17⟩ => ?_
  have R17 := R16.cons G17 (by simp <;> omega) v17
  have H17 := H16.trans (G17.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.naddA hL (i := n0 + 7) (a := n0 + 33) (b := n0 + 4) (va := (d * (d + 1) + d * (d + 1)) * lam) (vb := 1) (by omega)
    (by omega) (by omega) (R17.get (by simp)) (R17.get (by simp)) (by omega)) fun σ18 ⟨v18, d18, G18⟩ => ?_
  have R18 := R17.cons G18 (by simp <;> omega) v18
  have H18 := H17.trans (G18.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.naddA hL (i := n0 + 34) (a := n0 + 22) (b := n0 + 4) (va := 6 + c1 + j + j) (vb := 1) (by omega)
    (by omega) (by omega) (R18.get (by simp)) (R18.get (by simp)) (by omega)) fun σ19 ⟨v19, d19, G19⟩ => ?_
  have R19 := R18.cons G19 (by simp <;> omega) v19
  have H19 := H18.trans (G19.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.naddA hL (i := n0 + 35) (a := n0 + 22) (b := n0 + 22) (va := 6 + c1 + j + j) (vb := 6 + c1 + j + j) (by omega)
    (by omega) (by omega) (R19.get (by simp)) (R19.get (by simp)) (by omega)) fun σ20 ⟨v20, d20, G20⟩ => ?_
  have R20 := R19.cons G20 (by simp <;> omega) v20
  have H20 := H19.trans (G20.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.naddA hL (i := n0 + 36) (a := n0 + 35) (b := n0 + 4) (va := 6 + c1 + j + j + (6 + c1 + j + j)) (vb := 1) (by omega)
    (by omega) (by omega) (R20.get (by simp)) (R20.get (by simp)) (by omega)) fun σ21 ⟨v21, d21, G21⟩ => ?_
  have R21 := R20.cons G21 (by simp <;> omega) v21
  have H21 := H20.trans (G21.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.naddA hL (i := n0 + 37) (a := n0 + 8) (b := n0 + 8) (va := j) (vb := j) (by omega)
    (by omega) (by omega) (R21.get (by simp)) (R21.get (by simp)) (by omega)) fun σ22 ⟨v22, d22, G22⟩ => ?_
  have R22 := R21.cons G22 (by simp <;> omega) v22
  have H22 := H21.trans (G22.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.nsubA hL (i := n0 + 38) (a := n0 + 22) (b := n0 + 37) (va := 6 + c1 + j + j) (vb := j + j) (by omega)
    (by omega) (by omega) (R22.get (by simp)) (R22.get (by simp)) (by omega) (by omega))
    fun σ23 ⟨v23, d23, G23⟩ => ?_
  have R23 := R22.cons G23 (by simp <;> omega) v23
  have H23 := H22.trans (G23.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.naddA hL (i := n0 + 39) (a := n0 + 30) (b := n0 + 30) (va := 9 + cd + cR + lam + lam + lam + j + j) (vb := 9 + cd + cR + lam + lam + lam + j + j) (by omega)
    (by omega) (by omega) (R23.get (by simp)) (R23.get (by simp)) (by omega)) fun σ24 ⟨v24, d24, G24⟩ => ?_
  have R24 := R23.cons G24 (by simp <;> omega) v24
  have H24 := H23.trans (G24.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.naddA hL (i := n0 + 40) (a := n0 + 10) (b := n0 + 10) (va := lam) (vb := lam) (by omega)
    (by omega) (by omega) (R24.get (by simp)) (R24.get (by simp)) (by omega)) fun σ25 ⟨v25, d25, G25⟩ => ?_
  have R25 := R24.cons G25 (by simp <;> omega) v25
  have H25 := H24.trans (G25.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.naddA hL (i := n0 + 41) (a := n0 + 40) (b := n0 + 10) (va := lam + lam) (vb := lam) (by omega)
    (by omega) (by omega) (R25.get (by simp)) (R25.get (by simp)) (by omega)) fun σ26 ⟨v26, d26, G26⟩ => ?_
  have R26 := R25.cons G26 (by simp <;> omega) v26
  have H26 := H25.trans (G26.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.naddA hL (i := n0 + 42) (a := n0 + 41) (b := n0 + 4) (va := lam + lam + lam) (vb := 1) (by omega)
    (by omega) (by omega) (R26.get (by simp)) (R26.get (by simp)) (by omega)) fun σ27 ⟨v27, d27, G27⟩ => ?_
  have R27 := R26.cons G27 (by simp <;> omega) v27
  have H27 := H26.trans (G27.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.naddA hL (i := n0 + 43) (a := n0 + 41) (b := n0 + 41) (va := lam + lam + lam) (vb := lam + lam + lam) (by omega)
    (by omega) (by omega) (R27.get (by simp)) (R27.get (by simp)) (by omega)) fun σ28 ⟨v28, d28, G28⟩ => ?_
  have R28 := R27.cons G28 (by simp <;> omega) v28
  have H28 := H27.trans (G28.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.seq (XV.naddA hL (i := n0 + 44) (a := n0 + 43) (b := n0 + 4) (va := lam + lam + lam + (lam + lam + lam)) (vb := 1) (by omega)
    (by omega) (by omega) (R28.get (by simp)) (R28.get (by simp)) (by omega)) fun σ29 ⟨v29, d29, G29⟩ => ?_
  have R29 := R28.cons G29 (by simp <;> omega) v29
  have H29 := H28.trans (G29.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine XV.mono (XV.naddA hL (i := n0 + 45) (a := n0 + 44) (b := n0 + 4) (va := lam + lam + lam + (lam + lam + lam) + 1) (vb := 1) (by omega)
    (by omega) (by omega) (R29.get (by simp)) (R29.get (by simp)) (by omega)) le_rfl fun σ30 ⟨v30, d30, G30⟩ => ?_
  have R30 := R29.cons G30 (by simp <;> omega) v30
  have H30 := H29.trans (G30.mono (fun _ h => h) (fun _ h => by omega) (fun _ _ h => h))
  refine ⟨R30.get (by simp), R30.get (by simp), R30.get (by simp), R30.get (by simp), R30.get (by simp),
    R30.get (by simp), by rw [R30.get (i := n0 + 22) (v := 6 + c1 + j + j) (by simp)]; ring,
    by rw [R30.get (i := n0 + 30) (v := 9 + cd + cR + lam + lam + lam + j + j) (by simp)]; ring,
    by rw [R30.get (i := n0 + 7) (v := (d * (d + 1) + d * (d + 1)) * lam + 1) (by simp)]; ring,
    by rw [R30.get (i := n0 + 34) (v := 6 + c1 + j + j + 1) (by simp)]; ring,
    by rw [R30.get (i := n0 + 35) (v := 6 + c1 + j + j + (6 + c1 + j + j)) (by simp)]; ring,
    by rw [R30.get (i := n0 + 36) (v := 6 + c1 + j + j + (6 + c1 + j + j) + 1) (by simp)]; ring,
    by rw [R30.get (i := n0 + 38) (v := 6 + c1 + j + j - (j + j)) (by simp)]; omega,
    by rw [R30.get (i := n0 + 39) (v := 9 + cd + cR + lam + lam + lam + j + j + (9 + cd + cR + lam + lam + lam + j + j))
      (by simp)]; ring,
    by rw [R30.get (i := n0 + 42) (v := lam + lam + lam + 1) (by simp)]; ring,
    by rw [R30.get (i := n0 + 45) (v := lam + lam + lam + (lam + lam + lam) + 1 + 1) (by simp)]; ring,
    by rw [d30, d29, d28, d27, d26, d25, d24, d23, d22, d21, d20, d19, d18, d17, d16, d15, d14, d13, d12, d11, d10, d9,
      d8, d7, d6, d5, d4, d3, d2, d1], H30⟩

end AdversarialBco.Bit.Transfer
