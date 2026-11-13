/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.BLPure
public import AdversarialBco.Bit.TriSamp

@[expose] public section

/-!
# Interface I: BL's routines as computable pure functions

The functions that BL's machine program computes for the routines that Bit/BLPure.lean leaves open (`Routines`):

* `ellRI` on the integer problem `EllI d`: Procedure ELL-R for `d ≥ 2` (`ellR`),
  Procedure BIS-R for `d = 1` (`bisR`), the point `x / 2^(ellExp I)`; `clearQ : CallQ d → EllI d` clears the
  denominators of a call; `apQ` is the projection routine on BL's call data.
* `frameQ`: Procedure FRAME: F0 the height, F1 the cleared rows, F2 the read-off for `d = 1`,
  F3 the constants and F4 Procedure ELL-F for `d ≥ 2`, F5 the centre (`0` on fail).
* `triPosQ`: TRI-OGD staged (`triPos` of Bit/TriStage.lean) in rational arithmetic, line by line; `K0Q`, the coins of
  the prologue; `posQ`, P2 POS on the frame `B̄(c, 1/2) ⊆ K ⊆ B̄(c, n)` with `c = frameQ`.
* `RoutinesQ : Routines`.

Choices against the procedures of the paper, none of which changes the statement of a theorem:

* `EllI` keeps the radius `R` of the region and the two scalars `r₀`, `e` as rationals: the test of step 1 of ELL-R
  compares `|â|² R.den²` with `2^{2p} R.num²`; the constants use `R̄ = ⌈R⌉₊` in the place of an integer `R`
  (`L_G`, `θ`, `λ`, `Λ`, `q`, the start `Â = 2^p R̄² I`, BIS-R's start interval `[-R̄, R̄]`). At BL's calls
  `R = R_int` is an integer and `R̄ = R`. BIS-R makes the test of step 1, which never acts when `R` is an integer.
* The matrix step computes every entry `Â'_{ik}` (not only `i ≤ k`, then the mirror); the two agree as long as `Â`
  is symmetric, which the start is and every step keeps.
* `ellLoop` returns `a` when `ĝ = 0` (the kept point would have the same value of `G`).
* The rows of `clearQ`: `D_i` the product of the `d + 1` denominators of `(α_i, β_i)` (FRAME's F1); the quadratic
  constraint is multiplied by the product `D_H` of the denominators of `H`, `g`, `ℓ`; the objective by the product
  `D_P` of the denominators of `P`, with `f̂ = D_f D_P f`, `D_f` the product of the denominators of `f`, and the
  accuracy `e` by `D_P`.
* `triPosQ` mirrors `triU` (Bit/TriLeaves.lean) on every row: the quotient `α_k·z/β_k` with Lean's `x/0 = 0`, so a row
  with `β_k = 0` never makes `u` nonzero (the rows lemma of BL (ii)), and the position agrees with
  `triPos` on every coin sequence. Rows with `β_k < 0` (a stage position outside `K`, on a bad coin sequence) take
  part as in `triU`: the program's search must keep them to compute `triPosQ`.
* ELL-R and ELL-F store each new state in arrays (`Arr`, equal to the functions by `Arr.get_ofFn'`), so that they
  evaluate in time linear in the iterations.
* The prologue's confidence: `ℓ_pos = clog₂(3 · 2^{19} (d n)³ m_st)`, so `ℓ_pos ≥ log(m_st/δ₁)` at BL's
  `δ₁ = δ/3`, `δ = 2^{-19}/(d n)³`.
-/

namespace AdversarialBco.Bit.RQ

open AdversarialBco.Bit.BLP (CallQ Routines)
open AdversarialBco.BitRAM (readCoins)
open Matrix

variable {d : ℕ}

/-! ## Integer primitives -/

/-- `rnd(u/v) = ⌊(2u + v)/(2v)⌋`, the Euclidean quotient of the machine (Grid). -/
def rndI (u v : ℤ) : ℤ := (2 * u + v) / (2 * v)

/-- `lg(x)`: the least `c ≥ 0` with `2^c ≥ x`, for a rational `x` (`0` for `x ≤ 1`). -/
def lgQ (x : ℚ) : ℕ := Nat.clog 2 ⌈x⌉₊

/-- `κ_N = d (2d + 1)²`. -/
def kapN (d : ℕ) : ℤ := d * (2 * d + 1) ^ 2

/-- `κ_D = 4 (d + 1)² (d - 1)`. -/
def kapD (d : ℕ) : ℤ := 4 * (d + 1) ^ 2 * ((d : ℤ) - 1)

/-- A vector stored in an array. The routines store each new state in arrays (`Arr.ofFn'`, read back by `Arr.get`,
`Arr.get_ofFn'`), so that evaluating `n` iterations takes time linear in `n`: a state kept as a closure would be
recomputed from the start at every read. -/
structure Arr (d : ℕ) (α : Type*) where
  /-- The entries. -/
  a : Array α
  /-- The length. -/
  h : a.size = d

/-- The array of the values of `f`. -/
def Arr.ofFn' {α : Type*} (f : Fin d → α) : Arr d α := ⟨Array.ofFn f, Array.size_ofFn⟩

/-- Entry `i`. -/
def Arr.get {α : Type*} (x : Arr d α) (i : Fin d) : α := x.a[i.1]'(by rw [x.h]; exact i.2)

/-- Entry `(i, k)` of an array of rows. -/
def Arr.get2 {α : Type*} (x : Arr d (Arr d α)) (i k : Fin d) : α := (x.get i).get k

@[simp] theorem Arr.get_ofFn' {α : Type*} (f : Fin d → α) : (Arr.ofFn' f).get = f := by
  funext i
  simp only [Arr.get, Arr.ofFn', Array.getElem_ofFn]

@[simp] theorem Arr.get2_ofFn' {α : Type*} (A : Fin d → Fin d → α) :
    Arr.get2 (Arr.ofFn' fun i => Arr.ofFn' (A i)) = A := by
  funext i k
  simp only [Arr.get2, Arr.get_ofFn']

/-- Steps 6 to 8 of ELL-R (steps 3 to 5 of ELL-F) on `(Â, â)` and the cut `c`, at the grid `2^{-p}`, the root bits `q`,
the threshold `ρ = 2^{-j}` of (K1) and the caps `capA`, `capa` of (K2): the next state, or `none` when (K1) or (K2)
acts. -/
def ellUpd (p q j : ℕ) (capA capa : ℤ) (A : Matrix (Fin d) (Fin d) ℤ) (a c : Fin d → ℤ) :
    Option (Matrix (Fin d) (Fin d) ℤ × (Fin d → ℤ)) :=
  let v := A *ᵥ c
  let s := c ⬝ᵥ v
  if s < 2 ^ (p - 2 * j) * (c ⬝ᵥ c) then none else
  let X := s * 2 ^ (2 * q) / 2 ^ p
  let t : ℤ := (Nat.sqrt X.toNat : ℤ)
  let a' : Fin d → ℤ := fun i => a i - rndI (v i * 2 ^ q) ((d + 1) * t)
  let A' : Matrix (Fin d) (Fin d) ℤ := fun i k =>
    rndI (kapN d * ((d + 1) * s * A i k - 2 * v i * v k)) (kapD d * (d + 1) * s)
  if (∃ i k, capA < |A' i k|) ∨ (∃ i, capa < |a' i|) then none else
  some (Arr.get2 (Arr.ofFn' fun i => Arr.ofFn' (A' i)), (Arr.ofFn' a').get)

/-! ## The integer problem PROJ and Procedures ELL-R, BIS-R -/

/-- The integer problem PROJ: rows `α_i·y ≤ β_i`, the quadratic constraint `yᵀHy/2 - g·y ≤ ℓ`, the objective
`yᵀPy/2 - (f/D_f)·y`, the radius `R` (`|y| ≤ R`), the radius `r₀` of a ball in the region, the accuracy `e`. -/
structure EllI (d : ℕ) where
  m : ℕ
  α : Fin m → Fin d → ℤ
  β : Fin m → ℤ
  H : Matrix (Fin d) (Fin d) ℤ
  g : Fin d → ℤ
  ℓ : ℤ
  P : Matrix (Fin d) (Fin d) ℤ
  f : Fin d → ℤ
  Df : ℕ
  R : ℚ
  r : ℚ
  e : ℚ

namespace EllI

variable (I : EllI d)

/-- `R̄ = ⌈R⌉₊`. -/
def Rb : ℕ := ⌈I.R⌉₊

/-- `L_G = tr(P) R̄ + |f|₁/D_f`. -/
def LG : ℚ := (I.P.trace : ℚ) * I.Rb + (∑ i, |(I.f i : ℚ)|) / I.Df

/-- `θ = 1` if `3 L_G R̄ ≤ e`, else `e/(3 L_G R̄)`. -/
def θ : ℚ := if 3 * I.LG * I.Rb ≤ I.e then 1 else I.e / (3 * I.LG * I.Rb)

/-- `j = lg(1/(θ min(r₀, 1)))`, `ρ = 2^{-j}`. -/
def j : ℕ := lgQ (1 / (I.θ * min I.r 1))

/-- `λ = lg(R̄) + j`. -/
def lam : ℕ := Nat.clog 2 I.Rb + I.j

/-- `N = 2d(d + 1)λ + 1`, the iterations of ELL-R. -/
def N : ℕ := 2 * d * (d + 1) * I.lam + 1

/-- `p = 6 + lg(d²(d + 1)) + 2j`, the fractional bits. -/
def p : ℕ := 6 + Nat.clog 2 (d ^ 2 * (d + 1)) + 2 * I.j

/-- `q = 9 + lg(d) + lg(R̄) + 3λ + 2j`, the bits of the square root. -/
def q : ℕ := 9 + Nat.clog 2 d + Nat.clog 2 I.Rb + 3 * I.lam + 2 * I.j

/-- `Λ = R̄² 2^{6λ+2}`, the cap on the matrix. -/
def Lam : ℕ := I.Rb ^ 2 * 2 ^ (6 * I.lam + 2)

/-- `Λ^{1/2} = R̄ 2^{3λ+1}`. -/
def LamH : ℕ := I.Rb * 2 ^ (3 * I.lam + 1)

end EllI

/-- The outcome of the tests of one iteration: return a point, or cut with `c`, the kept point updated. -/
inductive Cut (d : ℕ) where
  | ret (x : Fin d → ℤ)
  | cut (c : Fin d → ℤ) (kept : Option ((Fin d → ℤ) × ℤ))

/-- Steps 1 to 4 of ELL-R at the scale `2^s` (`s = p` for ELL-R, `s = N₁` for BIS-R): the point `â/2^s`, the kept
point with its value `V`. -/
def ellTest (I : EllI d) (s : ℕ) (a : Fin d → ℤ) (kept : Option ((Fin d → ℤ) × ℤ)) : Cut d :=
  if 2 ^ (2 * s) * I.R.num ^ 2 < (a ⬝ᵥ a) * (I.R.den : ℤ) ^ 2 then .cut a kept else
  match (List.finRange I.m).find? (fun i => decide (2 ^ s * I.β i < I.α i ⬝ᵥ a)) with
  | some i => .cut (I.α i) kept
  | none =>
    if 2 ^ (2 * s + 1) * I.ℓ < a ⬝ᵥ (I.H *ᵥ a) - 2 ^ (s + 1) * (I.g ⬝ᵥ a) then
      .cut (I.H *ᵥ a - (2 ^ s : ℤ) • I.g) kept
    else
      let gh := I.P *ᵥ ((I.Df : ℤ) • a) - (2 ^ s : ℤ) • I.f
      let V := (I.Df : ℤ) * (a ⬝ᵥ (I.P *ᵥ a)) - 2 ^ (s + 1) * (I.f ⬝ᵥ a)
      let kept' : Option ((Fin d → ℤ) × ℤ) :=
        match kept with
        | none => some (a, V)
        | some (b, W) => if V < W then some (a, V) else some (b, W)
      if gh = 0 then .ret a else .cut gh kept'

/-- The state of ELL-R: `Â`, `â`, the kept point with its value. -/
structure ESt (d : ℕ) where
  A : Matrix (Fin d) (Fin d) ℤ
  a : Fin d → ℤ
  kept : Option ((Fin d → ℤ) × ℤ)

/-- The iterations of ELL-R, `k` of them left. -/
def ellLoop (I : EllI d) : ℕ → ESt d → Option (Fin d → ℤ)
  | 0, st => st.kept.map Prod.fst
  | k + 1, st =>
    match ellTest I I.p st.a st.kept with
    | .ret x => some x
    | .cut c kept =>
      if c = 0 then kept.map Prod.fst else
      match ellUpd I.p I.q I.j ((2 : ℤ) ^ I.p * I.Lam) ((2 : ℤ) ^ I.p * (I.Rb + I.LamH)) st.A st.a c with
      | none => kept.map Prod.fst
      | some (A', a') => ellLoop I k ⟨A', a', kept⟩

/-- Procedure ELL-R (`d ≥ 2`): from `Â = 2^p R̄² I`, `â = 0`, `N` iterations; the point `â/2^p`. -/
def ellR (I : EllI d) : Option (Fin d → ℤ) :=
  ellLoop I I.N ⟨((2 : ℤ) ^ I.p * I.Rb ^ 2) • (1 : Matrix (Fin d) (Fin d) ℤ), 0, none⟩

/-- The iterations of BIS-R on the interval `[lo, hi]` (integers over `2^{N₁}`), `k` of them left. -/
def bisLoop (I : EllI d) : ℕ → ℤ → ℤ → Option ((Fin d → ℤ) × ℤ) → Option (Fin d → ℤ)
  | 0, _, _, kept => kept.map Prod.fst
  | k + 1, lo, hi, kept =>
    let a : ℤ := (lo + hi) / 2
    match ellTest I (I.lam + 1) (fun _ => a) kept with
    | .ret x => some x
    | .cut c kept' =>
      if c = 0 then kept'.map Prod.fst else
      if 0 < ∑ i, c i then bisLoop I k lo a kept' else bisLoop I k a hi kept'

/-- Procedure BIS-R (`d = 1`): `N₁ = λ + 1` halvings of `[-R̄, R̄]`; the point over `2^{N₁}`. -/
def bisR (I : EllI d) : Option (Fin d → ℤ) :=
  bisLoop I (I.lam + 1) (-((I.Rb : ℤ) * 2 ^ (I.lam + 1))) ((I.Rb : ℤ) * 2 ^ (I.lam + 1)) none

/-- The exponent of the denominator of the returned point: `N₁ = λ + 1` for `d = 1`, `p` otherwise. -/
def ellExp (I : EllI d) : ℕ := if d = 1 then I.lam + 1 else I.p

/-- The projection routine on the integer problem: fail at once if `R < 1`, `r₀ ≤ 0` or `e ≤ 0`; `0` for `d = 0`;
BIS-R for `d = 1`; ELL-R for `d ≥ 2`. The point is `x / 2^(ellExp I)`. -/
def ellRI (I : EllI d) : Option (Fin d → ℤ) :=
  if I.R < 1 ∨ I.r ≤ 0 ∨ I.e ≤ 0 then none else
  if d = 0 then some 0 else
  if d = 1 then bisR I else ellR I

/-! ## Clearing the denominators of a call -/

/-- `num(x) (D / den(x))`: the integer `D x` when `den(x)` divides `D`. -/
def clr (D : ℕ) (x : ℚ) : ℤ := x.num * ((D / x.den : ℕ) : ℤ)

/-- The product of the `d + 1` denominators of row `i` of a call. -/
def rowDen (D : CallQ d) (i : Fin D.m) : ℕ := (∏ j, (D.α i j).den) * (D.β i).den

/-- `D_H`, the product of the denominators of `H`, `g`, `ℓ`. -/
def quadDen (D : CallQ d) : ℕ := (∏ i, ∏ j, (D.H i j).den) * (∏ j, (D.g j).den) * D.ℓ.den

/-- `D_P`, the product of the denominators of `P`. -/
def objDen (D : CallQ d) : ℕ := ∏ i, ∏ j, (D.P i j).den

/-- `D_f`, the product of the denominators of `f`. -/
def linDen (D : CallQ d) : ℕ := ∏ j, (D.f j).den

/-- The integer problem of a call: each row times `D_i`, the quadratic constraint times `D_H`, the objective and the
accuracy times `D_P` (`f̂ = D_f D_P f`). -/
def clearQ (D : CallQ d) : EllI d where
  m := D.m
  α i j := clr (rowDen D i) (D.α i j)
  β i := clr (rowDen D i) (D.β i)
  H i j := clr (quadDen D) (D.H i j)
  g j := clr (quadDen D) (D.g j)
  ℓ := clr (quadDen D) D.ℓ
  P i j := clr (objDen D) (D.P i j)
  f j := clr (linDen D) (D.f j) * objDen D
  Df := linDen D
  R := D.R
  r := D.r
  e := objDen D * D.e

/-- The projection routine of BL (`Routines.ap`): ELL-R or BIS-R on the cleared call. -/
def apQ {d : ℕ} (D : CallQ d) : Option (Fin d → ℚ) :=
  (ellRI (clearQ D)).map fun x i => (x i : ℚ) / 2 ^ ellExp (clearQ D)

/-! ## Procedure FRAME -/

section Frame

variable {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)

/-- F0: `M̂`, the largest `|numerator|` and denominator of the entries of `(A, b)`, at least `1`. -/
def frMhat : ℕ :=
  max 1 (Finset.univ.sup fun i =>
    max (Finset.univ.sup fun j => max (A i j).num.natAbs (A i j).den) (max (b i).num.natAbs (b i).den))

/-- F1: the product `D_i` of the `d + 1` denominators of row `i`. -/
def frDen (i : Fin m) : ℕ := (∏ j, (A i j).den) * (b i).den

/-- F1: the cleared row `α_i = D_i A_i`. -/
def frAl (i : Fin m) (j : Fin d) : ℤ := clr (frDen A b i) (A i j)

/-- F1: the cleared right-hand side `β_i = D_i b_i`. -/
def frBe (i : Fin m) : ℤ := clr (frDen A b i) (b i)

/-- F2 (`d = 1`), the read-off on the cleared rows `α_i x ≤ β_i`: fail if a zero row has `β_i < 0`; `lo` the largest
`β_i/α_i` over `α_i < 0`, `hi` the least over `α_i > 0`; fail if one is missing or `hi - lo < 1`; else `(lo + hi)/2`. -/
def frame1 (al be : Fin m → ℤ) : Option ℚ :=
  if ∃ i, al i = 0 ∧ be i < 0 then none else
  match ((List.finRange m).filterMap fun i => if al i < 0 then some ((be i : ℚ) / al i) else none).max?,
    ((List.finRange m).filterMap fun i => if 0 < al i then some ((be i : ℚ) / al i) else none).min? with
  | some lo, some hi => if hi - lo < 1 then none else some ((lo + hi) / 2)
  | _, _ => none

/-- F3: `e_R = lg(R_loc + 1)`, `R_loc = (d m M̂^{2(d+1)})^{d+1}` (the localisation lemma). -/
def frER (d m Mh : ℕ) : ℕ := Nat.clog 2 ((d * m * Mh ^ (2 * (d + 1))) ^ (d + 1) + 1)

/-- F3: `p = 8 + lg(d²(d + 1))`. -/
def frP (d : ℕ) : ℕ := 8 + Nat.clog 2 (d ^ 2 * (d + 1))

/-- F3: `q = 14 + lg(d) + 4 e_R`. -/
def frQ (d eR : ℕ) : ℕ := 14 + Nat.clog 2 d + 4 * eR

/-- F3: `N = 2d(d + 1)λ_e + 1`, `λ_e = e_R + 1`. -/
def frN (d eR : ℕ) : ℕ := 2 * d * (d + 1) * (eR + 1) + 1

/-- F4, Procedure ELL-F on the margin rows (`B_i = 2^{p+1} β_i`, `nn_i = 2^{2p} |α_i|²`), `k` iterations left: return
`â` when every row passes (`D = B_i - 2 α_i·â ≥ 0` and `D² ≥ nn_i`), else cut with the first failing row; fail on
(K0), (K1) (`ρ = 1/2`: `ŝ < 2^{p-2} |c|²`, which is `4 ŝ < 2^p |c|²`), (K2), or after the last iteration. -/
def frLoop (p q : ℕ) (capA capa : ℤ) (al : Fin m → Fin d → ℤ) (B nn : Fin m → ℤ) :
    ℕ → Matrix (Fin d) (Fin d) ℤ → (Fin d → ℤ) → Option (Fin d → ℤ)
  | 0, _, _ => none
  | k + 1, A, a =>
    match (List.finRange m).find? (fun i =>
        decide (B i - 2 * (al i ⬝ᵥ a) < 0 ∨ (B i - 2 * (al i ⬝ᵥ a)) ^ 2 < nn i)) with
    | none => some a
    | some i =>
      if nn i = 0 then none else
      match ellUpd p q 1 capA capa A a (al i) with
      | none => none
      | some (A', a') => frLoop p q capA capa al B nn k A' a'

/-- F3 and F4 (`d ≥ 2`): ELL-F from `Â = 2^{p + 2 e_R} I`, `â = 0`, with the caps `2^p Λ = 2^{p + 2e_R + 6λ_e + 2}` and
`2^p (R + Λ^{1/2}) = 2^p (2^{e_R} + 2^{e_R + 3λ_e + 1})`; the point `â/2^p`. -/
def frEll : Option (Fin d → ℤ) :=
  let eR := frER d m (frMhat A b)
  let p := frP d
  frLoop p (frQ d eR) (2 ^ (p + 2 * eR + 6 * (eR + 1) + 2)) (2 ^ p * (2 ^ eR + 2 ^ (eR + 3 * (eR + 1) + 1)))
    (frAl A b) (fun i => 2 ^ (p + 1) * frBe A b i) (fun i => 2 ^ (2 * p) * (frAl A b i ⬝ᵥ frAl A b i))
    (frN d eR) ((2 : ℤ) ^ (p + 2 * eR) • (1 : Matrix (Fin d) (Fin d) ℤ)) 0

end Frame

/-- Procedure FRAME (`Routines.ctr`): the frame centre `c`, `0` on fail. `d = 1`: the read-off F2; `d ≥ 2`: ELL-F,
`c = â/2^p`. -/
def frameQ (d _n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : Fin d → ℚ :=
  if h : d = 1 then
    match frame1 (fun i => frAl A b i ⟨0, by omega⟩) (frBe A b) with
    | some c => fun _ => c
    | none => 0
  else if d = 0 then 0 else
    match frEll A b with
    | some a => fun i => (a i : ℚ) / 2 ^ frP d
    | none => 0

/-! ## TRI-OGD staged in rationals (`triPos`, Bit/TriStage.lean) -/

/-- A position `(μ, T)`, the rational form of `PgSp d` (`pgMu`, `pgMat`). -/
abbrev PosQ (d : ℕ) := (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ

/-- `triS`: the parameter lemma's length `s`. -/
def triSQ (d : ℕ) : ℕ := Nat.find (pg_par_exists d)

/-- `triR = 2^{L-3}`. -/
def triRQ (d : ℕ) : ℚ := 2 ^ (triLa (triSQ d) - 3)

/-- `triJa`: the least `j` with `9 d s ≤ 2^j`. -/
def triJaQ (d : ℕ) : ℕ := Nat.clog 2 (9 * d * triSQ d)

/-- `triA = 2^{-j_a}`. -/
def triAQ (d : ℕ) : ℚ := 1 / 2 ^ triJaQ d

/-- `triB = 161 · 2^{L-10}`. -/
def triBQ (d : ℕ) : ℚ := 161 * 2 ^ (triLa (triSQ d) - 10)

/-- `triRh = 2^{L_h} - 1`. -/
def triRhQ (d : ℕ) : ℚ := 2 ^ triLh (triSQ d) - 1

/-- `triD2`, the squared diameter of the box. -/
def triD2Q (d : ℕ) : ℚ :=
  4 * d * triRQ d ^ 2 + d * (triBQ d - triAQ d) ^ 2 + 2 * d * (d - 1) * triBQ d ^ 2

/-- `triElo`, with `pgKappa = 1/8`. -/
def triEloQ (d : ℕ) : ℚ :=
  (1 / 8) ^ 2 / (922 * (d : ℚ) ^ 2 * (7 / 5 * triLh (triSQ d)) * (627 / 4000 * triRhQ d))

/-- `triKg`. -/
def triKgQ (d : ℕ) : ℕ :=
  max 2 (Nat.clog 2 ⌈16 * triBQ d * (d + 1) * d * (8 * d + 2) / triEloQ d⌉₊)

/-- `triGu`. -/
def triGuQ (d : ℕ) : ℚ := (Nat.sqrt (8 * d * triKgQ d) : ℚ) + 2 + 2 ^ triJaQ d / 8

/-- `triBv`. -/
def triBvQ (d : ℕ) : ℕ := Nat.clog 4 ⌈64 * (d + 1) ^ 2 * triD2Q d / triEloQ d ^ 2⌉₊

/-- `triBu`. -/
def triBuQ (d : ℕ) : ℚ := (d + 1) / 2 ^ triBvQ d

/-- `triNe`, the horizon `N' = 2^n`. -/
def triNeQ (d ℓ : ℕ) : ℕ :=
  Nat.clog 2 ⌈16 * triD2Q d * (2 * (3 / 2 * (triGuQ d + triBuQ d)) ^ 2 + 4 * triGuQ d ^ 2 * ℓ) /
    (9 * triEloQ d ^ 2)⌉₊

/-- `triJs`, the step `2^{-j_s}`. -/
def triJsQ (d ℓ : ℕ) : ℕ := Nat.clog 4 ⌈(triGuQ d + triBuQ d) ^ 2 * 2 ^ triNeQ d ℓ / triD2Q d⌉₊

/-- `triBg = 4 k_g`. -/
def triBgQ (d : ℕ) : ℕ := 4 * triKgQ d

/-- `triL`, the coins of one stage. -/
def triLQ (d ℓ : ℕ) : ℕ := 2 ^ triNeQ d ℓ * (2 * d * triBgQ d)

/-- `triMst`, the number of stages `max 1 ⌈log₂ ⌈R0/r0⌉⌉`. -/
def triMstQ (r0 R0 : ℚ) : ℕ := max 1 (Nat.clog 2 ⌈R0 / r0⌉₊)

/-- `triLo`: `-r` on `μ`; on the matrix `-b` below the diagonal, `a` on it, `0` above it. -/
def triLoQ (r a b : ℚ) : PosQ d :=
  (fun _ => -r, fun i j => if j < i then -b else if i = j then a else 0)

/-- `triHi`: `r` on `μ`; on the matrix `b` on and below the diagonal, `0` above it. -/
def triHiQ (r b : ℚ) : PosQ d := (fun _ => r, fun i j => if j ≤ i then b else 0)

/-- `triClip`, the coordinate clip onto the box. -/
def triClipQ (r a b : ℚ) (x : PosQ d) : PosQ d :=
  (fun i => max ((triLoQ r a b : PosQ d).1 i) (min ((triHiQ r b : PosQ d).1 i) (x.1 i)),
   fun i j => max ((triLoQ r a b : PosQ d).2 i j) (min ((triHiQ r b : PosQ d).2 i j) (x.2 i j)))

/-- `triRound`: every coordinate down to the grid `2^{-B_v}`. -/
def triRoundQ (Bv : ℕ) (x : PosQ d) : PosQ d :=
  (fun i => (⌊x.1 i * 2 ^ Bv⌋ : ℚ) / 2 ^ Bv, fun i j => (⌊x.2 i j * 2 ^ Bv⌋ : ℚ) / 2 ^ Bv)

/-- `triQ`, the quotient `α_k·z/β_k` of row `k`. -/
def triQQ {m : ℕ} (α : Fin m → Fin d → ℚ) (β : Fin m → ℚ) (k : Fin m) (z : Fin d → ℚ) : ℚ := α k ⬝ᵥ z / β k

/-- `triU`, the subgradient of the gauge: `α_k/β_k` for the least `k` at which the quotient is largest, when that
quotient is positive, else `0`. -/
def triUQ {m : ℕ} (α : Fin m → Fin d → ℚ) (β : Fin m → ℚ) (z : Fin d → ℚ) : Fin d → ℚ :=
  ∑ k, if 0 < triQQ α β k z ∧ (∀ k', triQQ α β k' z ≤ triQQ α β k z) ∧
      (∀ k', k' < k → triQQ α β k' z < triQQ α β k z)
    then (β k)⁻¹ • α k else 0

/-- `triV`, the subgradient `(u, tril(u yᵀ) - (κ/d) diag(1/T_ii))`, `u = u(μ + T y)`, `κ = 1/8`. -/
def triVQ (u : (Fin d → ℚ) → Fin d → ℚ) (x : PosQ d) (y : Fin d → ℚ) : PosQ d :=
  (fun i => u (x.1 + x.2 *ᵥ y) i,
   fun i j => (if j ≤ i then u (x.1 + x.2 *ᵥ y) i * y j else 0) - (if i = j then 1 / 8 / d / x.2 i i else 0))

/-- `triIter`: `x_0 = (0, I)`, `x_{t+1} = clip(x_t - s Ṽ(x_t; y_t))`. -/
def triIterQ (r a b s : ℚ) (Vt : PosQ d → (Fin d → ℚ) → PosQ d) (y : ℕ → Fin d → ℚ) : ℕ → PosQ d
  | 0 => (0, 1)
  | t + 1 => triClipQ r a b (triIterQ r a b s Vt y t - s • Vt (triIterQ r a b s Vt y t) (y t))

/-- `triAvg`: the average of the first `N` iterates. -/
def triAvgQ (r a b s : ℚ) (Vt : PosQ d → (Fin d → ℚ) → PosQ d) (y : ℕ → Fin d → ℚ) (N : ℕ) : PosQ d :=
  (N : ℚ)⁻¹ • ∑ t ∈ Finset.range N, triIterQ r a b s Vt y t

/-- `triDraw`: coordinate `i` of draw `t` is the cosine output of BM-INT on the blocks `2 (t d + i)` and
`2 (t d + i) + 1` of `B` coins. -/
def triDrawQ (d B : ℕ) (x : ℕ → Bool) (t : ℕ) : Fin d → ℚ := fun i =>
  ((gsSpec B (readCoins x (2 * (t * d + i) * B) B).toNat (readCoins x ((2 * (t * d + i) + 1) * B) B).toNat).1 : ℚ) /
    2 ^ (2 * gsm_prec B)

/-- `triCoreOut`: the core on the rows `(α, β)` at the integer `ℓ`, on the draws `y`. -/
def triCoreOutQ (d : ℕ) {m : ℕ} (α : Fin m → Fin d → ℚ) (β : Fin m → ℚ) (ℓ : ℕ) (y : ℕ → Fin d → ℚ) : PosQ d :=
  triAvgQ (triRQ d) (triAQ d) (triBQ d) (1 / 2 ^ triJsQ d ℓ)
    (fun x w => triRoundQ (triBvQ d) (triVQ (triUQ α β) x w)) y (2 ^ triNeQ d ℓ)

/-- `triRowsA`: the rows `A`, then `e_i` and `-e_i`. -/
def triRowsAQ {m : ℕ} (A : Fin m → Fin d → ℚ) : Fin (m + (d + d)) → Fin d → ℚ :=
  Fin.append A (Fin.append (fun i => Pi.single i 1) (fun i => -Pi.single i 1))

/-- `triRowsB`: `b`, then `c_i + s` and `s - c_i`. -/
def triRowsBQ {m : ℕ} (b : Fin m → ℚ) (c : Fin d → ℚ) (s : ℚ) : Fin (m + (d + d)) → ℚ :=
  Fin.append b (Fin.append (fun i => c i + s) (fun i => s - c i))

/-- `triStA`: the rows of a stage read in the position `P`, `Tᵀ a_k`. -/
def triStAQ {m : ℕ} (A : Fin m → Fin d → ℚ) (P : PosQ d) : Fin (m + (d + d)) → Fin d → ℚ :=
  fun k => P.2ᵀ *ᵥ triRowsAQ A k

/-- `triStB`: the right-hand sides of a stage read in `P`, `b_k - a_k·μ`. -/
def triStBQ {m : ℕ} (A : Fin m → Fin d → ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ) (s : ℚ) (P : PosQ d) :
    Fin (m + (d + d)) → ℚ :=
  fun k => triRowsBQ b c s k - triRowsAQ A k ⬝ᵥ P.1

/-- `pgComp`: `(μ + T μ', T T')`. -/
def pgCompQ (P P' : PosQ d) : PosQ d := (P.1 + P.2 *ᵥ P'.1, P.2 * P'.2)

/-- `triStep`: stage `j` from the position `P` on the coins `x` of the stage. -/
def triStepQ {m : ℕ} (A : Fin m → Fin d → ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ) (r0 : ℚ) (ℓ j : ℕ) (P : PosQ d)
    (x : ℕ → Bool) : PosQ d :=
  pgCompQ P (triCoreOutQ d (triStAQ A P) (triStBQ A b c (2 ^ (j + 1) * r0) P) ℓ fun t => triDrawQ d (triBgQ d) x t)

/-- `triStageN`: the position after the stages `0, ..., j - 1`, from `(c, r0 I)`. -/
def triStageNQ {m : ℕ} (A : Fin m → Fin d → ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ) (r0 : ℚ) (ℓ : ℕ)
    (ω : ℕ → ℕ → Bool) : ℕ → PosQ d
  | 0 => (c, r0 • 1)
  | j + 1 => triStepQ A b c r0 ℓ j (triStageNQ A b c r0 ℓ ω j) (ω j)

/-- `triPos`: stage `j` reads the coins `j L, ..., j L + L - 1` of `cs`. -/
def triPosQ {m : ℕ} (A : Fin m → Fin d → ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ) (r0 R0 : ℚ) (ℓ : ℕ) (cs : ℕ → Bool) :
    PosQ d :=
  triStageNQ A b c r0 ℓ (fun j k => cs (triLay (triMstQ r0 R0) (triLQ d ℓ) (j, k))) (triMstQ r0 R0)

/-! ## The prologue and the routines -/

/-- The integer `ℓ_pos = clog₂(3 · 2^{19} (d n)³ m_st) ≥ log(m_st/δ₁)`, `δ₁ = 2^{-19}/(3 (d n)³)`. -/
def ellPos (d n : ℕ) : ℕ := Nat.clog 2 (3 * 2 ^ 19 * (d * n) ^ 3 * triMstQ (1 / 2) n)

/-- The coins of the prologue: `m_st L` (`Routines.K0`). -/
def K0Q (d n : ℕ) : ℕ := triMstQ (1 / 2) n * triLQ d (ellPos d n)

/-- P2 POS (`Routines.pos`): TRI-OGD staged on the rows of `K`, on the frame `B̄(c, 1/2) ⊆ K ⊆ B̄(c, n)`,
`c = frameQ`. -/
def posQ (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (cs : ℕ → Bool) : PosQ d :=
  triPosQ (fun k => A k) b (frameQ d n m A b) (1 / 2) n (ellPos d n) cs

/-- BL's routines as computed by its program. -/
def RoutinesQ : Routines where
  ap := apQ
  K0 := K0Q
  ctr := frameQ
  pos := posQ

end AdversarialBco.Bit.RQ
