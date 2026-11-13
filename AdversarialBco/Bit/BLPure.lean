/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.GsSpec
public import AdversarialBco.Bit.CoinSched
public import AdversarialBco.StatementConj1Bit

@[expose] public section

/-!
# BL as a pure function

The bit learner BL in exact rational and integer arithmetic: the parameters of Procedure PARAM, the prologue P3 to P5
(rows, mode), the draws of R1 (coins read through `readCoins`, Procedure BM-INT as `gsSpec`), the play of R2 and the
round R5 to R15. This file is the interface between the analysis (the record `Run` and `EngineHyp`)
and the machine program: the program must compute these values.

What BL calls and does not define here:

* the projection routine of R11 and R14 (ELL-R for `d ≥ 2`, BIS-R for `d = 1`), any function
  `CallQ d → Option (Fin d → ℚ)` of the call data (`Routines.ap`);
* the prologue routines P1 FRAME (the frame centre `c`) and P2 POS (TRI-OGD staged: the position `(μ_S, A_S)` from the
  first `K0 d n` coins of the stream) (`Routines.ctr`, `Routines.pos`, `Routines.K0`).

Choices made against Algorithm BL, none of which changes a bound of the lemma of the errors of a round or the precision
theorem:

* the rows of P3 are the rational rows `α̃_i = A_Sᵀ a_i`, `β̃_i = b_i - a_i·μ_S` over the kept rows `a_i ≠ 0`; the paper
  scales them to integers by `D_i 2^{k_S} > 0`, which changes no sign test, no gauge and no region;
* PARAM computes the fields to the absolute precision `2^{-pF}`, `pF = p + 2ℓe + 4ℓd + 40`, in the place of a
  relative precision: every field below `1` is at least `2^{-2ℓe - 4ℓd - 30}` (Lemma FB), so the relative
  error stays below `2^{-p-4}`;
* the logarithm `LOGINT` of PARAM is `lnQ`, two calls of the logarithm `gsm_LLq` of Procedure BM-INT (Lemma LOG,
  `gsm_LLq_err`): `ln N = size(N) ln 2 - (-ln (N/2^{size N}))`, error at most `2 size(N)(4q + 1)/2^q`, at
  `q = p + 2 len(ℓe) + 24`;
* the test call of R11 passes the objective `yᵀP'_+y/2 - w'_+·y` (side route R9) as the linear
  part `f = w'_+`; line μ passes `f = P'_+ wmu'`. The call data `CallQ` carry this linear part.

The coins are read on the schedule of Bit/CoinSched.lean (`Sched.nBlk`, `Sched.blkStart`), in every
mode: the prologue reads the coins `0, ..., K0 - 1`, round `t` reads `nBlk d = ⌈d/2⌉ + 1` blocks of `2B` coins.
Block `j < ⌈d/2⌉` gives the draws `ξ'_{2j}, ξ'_{2j+1}` (the second dropped when `2j + 1 = d`), the last block gives
`ζ'`, half its first output.
-/

namespace AdversarialBco.Bit.BLP

open AdversarialBco.BitRAM (readCoins toE)
open AdversarialBco.RealRAM (Strategy lossAd)
open Matrix

variable {d : ℕ}

/-! ## Arithmetic primitives -/

/-- `rnd_k x`: the nearest point of `2^{-k} ℤ`, ties up. -/
def rnd (k : ℕ) (x : ℚ) : ℚ := (⌊x * 2 ^ k + 1 / 2⌋ : ℚ) / 2 ^ k

/-- `x` rounded up to `2^{-k} ℤ`. -/
def up (k : ℕ) (x : ℚ) : ℚ := (⌈x * 2 ^ k⌉ : ℚ) / 2 ^ k

/-- `x` rounded down to `2^{-k} ℤ`. -/
def dn (k : ℕ) (x : ℚ) : ℚ := (⌊x * 2 ^ k⌋ : ℚ) / 2 ^ k

/-- `ISQRT(⌊4^k x⌋)/2^k`: below `x^{1/2}` by less than `2^{-k}` for `x ≥ 0`. -/
def sqrtDn (k : ℕ) (x : ℚ) : ℚ := (Nat.sqrt ⌊x * 4 ^ k⌋₊ : ℚ) / 2 ^ k

/-- `(ISQRT(⌈4^k x⌉) + 1)/2^k`: at least `x^{1/2}` for `x ≥ 0`. -/
def sqrtUp (k : ℕ) (x : ℚ) : ℚ := ((Nat.sqrt ⌈x * 4 ^ k⌉₊ : ℚ) + 1) / 2 ^ k

/-- `rnd_k` entrywise on a vector. -/
def rndV (k : ℕ) (v : Fin d → ℚ) : Fin d → ℚ := fun i => rnd k (v i)

/-- `rnd_k` entrywise on a matrix. -/
def rndM (k : ℕ) (M : Matrix (Fin d) (Fin d) ℚ) : Matrix (Fin d) (Fin d) ℚ := fun i j => rnd k (M i j)

/-- The squared Frobenius norm. -/
def frob2 (M : Matrix (Fin d) (Fin d) ℚ) : ℚ := ∑ i, ∑ j, M i j ^ 2

/-- `LOGINT_q(N)`: `ln N ≈ (size(N) LL(1, q, 0) - LL(size N, q, N - 1))/2^q` with the logarithm `gsm_LLq` of
Procedure BM-INT (`-ln((U + 1)/2^B)` at scale `2^q`). -/
def lnQ (q N : ℕ) : ℚ := (((N.size : ℤ) * gsm_LLq 1 q 0 - gsm_LLq N.size q (N - 1) : ℤ) : ℚ) / 2 ^ q

/-- The error bound of `lnQ q N`: `2 size(N) (4q + 1)/2^q` (twice Lemma LOG, `gsm_LLq_err`). -/
def lnErr (q N : ℕ) : ℚ := 2 * N.size * (4 * q + 1) / 2 ^ q

/-! ## Procedure PARAM -/

/-- `N_e = 15 · 2^17 d^3 n^4 = 1/δe` at BL's confidence `δ = 2^{-19}/(d n)^3`. -/
def Ne (d n : ℕ) : ℕ := 15 * 2 ^ 17 * d ^ 3 * n ^ 4

/-- BL's parameters: the precisions and every rational field of the table. -/
structure Par where
  /-- BL's precision `p = 10 ℓe + 16 ℓd + 160`. -/
  p : ℕ
  /-- The working bits of the logarithms and roots. -/
  q : ℕ
  /-- The precision of the fields. -/
  pF : ℕ
  /-- The coins per uniform of a draw, `B = 2 (p + len(n (d + 2)) + 2)`. -/
  B : ℕ
  /-- `N_e = 1/δe`. -/
  Ne : ℕ
  /-- `Λ = d N_e`. -/
  Lam : ℕ
  /-- `Le' ≤ Le`. -/
  Le : ℚ
  /-- `ε' ≥ ε`. -/
  eps : ℚ
  /-- `λ'`. -/
  lam : ℚ
  /-- `η'`. -/
  eta : ℚ
  /-- `sig2'`. -/
  sig2 : ℚ
  /-- `ρ' ≤ ρ`. -/
  rho : ℚ
  /-- `κ_c'`, the coefficient of `c = κ_c Y`. -/
  kapc : ℚ
  /-- `ν' ≈ 1/(1 - λ)`. -/
  nu : ℚ
  /-- `R' ≥ R`. -/
  R : ℚ
  /-- `s'_b ≤ s_b`. -/
  sb : ℚ
  /-- `W' ≥ W`. -/
  W : ℚ
  /-- `A_0 ≈ σ`. -/
  A0 : ℚ
  /-- `B_0 ≈ 1/σ`. -/
  B0 : ℚ
  /-- The outer radius `R_int = ⌈R'⌉`. -/
  Rint : ℕ
  /-- The slack `ê = 2^{-p + 3ℓe + 6ℓd + 64}`. -/
  eHat : ℚ

/-- Procedure PARAM at `(d, n)`. -/
def par (d n : ℕ) : Par :=
  let ne := Ne d n
  let le := ne.size
  let ld := d.size
  let p := 10 * le + 16 * ld + 160
  let q := p + 2 * le.size + 24
  let pF := p + 2 * le + 4 * ld + 40
  let L0 := lnQ q ne
  let ηe := lnErr q ne
  let L1 := lnQ q (2 * d + 2)
  let η1 := lnErr q (2 * d + 2)
  let rn := sqrtDn q n
  let rd := sqrtDn q d
  let Le := 36 * (L0 - ηe)
  let Lehi := 36 * (L0 + ηe)
  let lam := rnd pF (1 / (725 * d * Le ^ 2))
  let eta := rnd pF (rd / (Le * rn))
  let R := up pF (134 * d * sqrtUp q (L1 + η1))
  let s := sqrtUp q (rnd pF (1 / (8 * Le)))
  { p := p
    q := q
    pF := pF
    B := 2 * (p + (n * (d + 2)).size + 2)
    Ne := ne
    Lam := d * ne
    Le := Le
    eps := up pF (14500 * d * (rd + 1 / 2 ^ q) * Lehi ^ 5 / rn)
    lam := lam
    eta := eta
    sig2 := rnd pF (1 / (8 * Le))
    rho := dn pF (1450 * d ^ 2 * Le ^ 3)
    kapc := rnd pF (eta * lam / (4 * (1 - lam) ^ 2))
    nu := rnd pF (1 / (1 - lam))
    R := R
    sb := dn pF (1 / ((ne : ℚ) ^ 2 * R * (R + 1)))
    W := up pF (R + 4 * d * sqrtUp q (ne / Le))
    A0 := rnd p s
    B0 := rnd p (1 / s)
    Rint := ⌈R⌉₊
    eHat := 1 / 2 ^ (p - 3 * le - 6 * ld - 64) }

/-! ## The state, the modes, the configuration -/

/-- BL's state in mode `run`: the mean, the pair `(A, B)` (`P = B Bᵀ`, `S = A Aᵀ` never
stored), `b`, `G`, `k`, `l`, and whether the round is the first of an epoch. -/
structure St (d : ℕ) where
  first : Bool
  mu : Fin d → ℚ
  A : Matrix (Fin d) (Fin d) ℚ
  B : Matrix (Fin d) (Fin d) ℚ
  b : Fin d → ℚ
  k : ℚ
  G : Fin d → ℚ
  l : ℚ

/-- BL's mode: `off` plays the frame centre `c`, `guard` plays `μ_S`, `run` a round of the learner. -/
inductive Mode (d : ℕ)
  | off
  | guard
  | run (st : St d)

/-- The epoch start (`df2Init` at BL's parameters): `μ' = 0`, `A' = A_0 I`, `B' = B_0 I`, `b' = G' = 0`,
`k' = l' = 0`. -/
def init (P : Par) (d : ℕ) : St d := ⟨true, 0, P.A0 • 1, P.B0 • 1, 0, 0, 0, 0⟩

/-- What BL reads after its prologue: the parameters, the kept rows of `K~` (P3), the position, the frame centre. -/
structure Cfg (d : ℕ) where
  par : Par
  /-- The number of kept rows. -/
  m : ℕ
  /-- `α̃_i = A_Sᵀ a_i` over the kept rows. -/
  α : Fin m → Fin d → ℚ
  /-- `β̃_i = b_i - a_i·μ_S` over the kept rows. -/
  β : Fin m → ℚ
  /-- The position centre `μ_S`. -/
  μS : Fin d → ℚ
  /-- The position matrix `A_S`. -/
  AS : Matrix (Fin d) (Fin d) ℚ
  /-- The frame centre `c` of P1. -/
  c : Fin d → ℚ

/-- The kept rows of the input (P3): the indices `i` with `a_i ≠ 0`. -/
def keptIdx {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) : List (Fin m) := (List.finRange m).filter fun i => A i ≠ 0

/-- P3 ROWS: the rows of `K~ = posBody K S'` over the kept rows, from the input and the position. -/
def mkCfg (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ)
    (S : (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ) : Cfg d where
  par := par d n
  m := (keptIdx A).length
  α := fun i => S.2ᵀ *ᵥ A ((keptIdx A).get i)
  β := fun i => b ((keptIdx A).get i) - A ((keptIdx A).get i) ⬝ᵥ S.1
  μS := S.1
  AS := S.2
  c := c

/-- P5 MODE: `off` if `ε' > 1/2` or some kept `β̃_i ≤ 0`, else `run` at the epoch start. -/
def mode0 (cfg : Cfg d) : Mode d :=
  if 1 / 2 < cfg.par.eps ∨ ∃ i, cfg.β i ≤ 0 then .off else .run (init cfg.par d)

/-- The gauge of `K~` at `X` from the kept rows: `max(0, max_i α̃_i·X/β̃_i)` (the rows lemma of BL (c)). -/
def gaugeQ (cfg : Cfg d) (X : Fin d → ℚ) : ℚ := (List.ofFn fun i => cfg.α i ⬝ᵥ X / cfg.β i).foldl max 0

/-- `pt' = max(1, π(X')/(1 - ε'))`. -/
def ptQ (cfg : Cfg d) (X : Fin d → ℚ) : ℚ := max 1 (gaugeQ cfg X / (1 - cfg.par.eps))

/-- `X' = μ' + (1 - λ') A'ξ'`. -/
def XQ (cfg : Cfg d) (st : St d) (ξ : Fin d → ℚ) : Fin d → ℚ := st.mu + (1 - cfg.par.lam) • (st.A *ᵥ ξ)

/-- R2 PLAYPT: the play `x' = μ_S + A_S (X'/pt')` in mode `run`, `μ_S` in mode `guard`, `c` in mode `off`. -/
def playPt (cfg : Cfg d) (mo : Mode d) (ξ : Fin d → ℚ) : Fin d → ℚ :=
  match mo with
  | .off => cfg.c
  | .guard => cfg.μS
  | .run st => cfg.μS + cfg.AS *ᵥ ((ptQ cfg (XQ cfg st ξ))⁻¹ • XQ cfg st ξ)

/-! ## The projection calls -/

/-- The data of one call of BL's projection routine (BL's call class): the region
`{y | α_i·y ≤ β_i (i < m), yᵀHy/2 - g·y ≤ ℓ, |y| ≤ R}`, the objective `yᵀPy/2 - f·y`, the
radius `r` of a ball the region holds (its centre is not passed), the accuracy `e`. -/
structure CallQ (d : ℕ) where
  m : ℕ
  α : Fin m → Fin d → ℚ
  β : Fin m → ℚ
  H : Matrix (Fin d) (Fin d) ℚ
  g : Fin d → ℚ
  ℓ : ℚ
  R : ℚ
  r : ℚ
  P : Matrix (Fin d) (Fin d) ℚ
  f : Fin d → ℚ
  e : ℚ

/-- BL's routines that this file does not define (label R): the projection routine and the
prologue routines FRAME and TRI-OGD staged. `pos d n m A b cs` reads the coins `cs 0, ..., cs (K0 d n - 1)`. -/
structure Routines where
  /-- ELL-R (`d ≥ 2`) or BIS-R (`d = 1`). -/
  ap : ∀ {d : ℕ}, CallQ d → Option (Fin d → ℚ)
  /-- The coins read by the prologue. -/
  K0 : ℕ → ℕ → ℕ
  /-- P1 FRAME: the frame centre. -/
  ctr : (d n m : ℕ) → Matrix (Fin m) (Fin d) ℚ → (Fin m → ℚ) → Fin d → ℚ
  /-- P2 POS: the position `(μ_S, A_S)` from the coin stream. -/
  pos : (d n m : ℕ) → Matrix (Fin m) (Fin d) ℚ → (Fin m → ℚ) → (ℕ → Bool) → (Fin d → ℚ) × Matrix (Fin d) (Fin d) ℚ

/-- The region `K_ε' = {y | α̃_i·y ≤ (1 - ε') β̃_i}` with the quadratic `yᵀHy/2 - g·y ≤ ℓ`, the outer radius `R_int`,
radius `r`, objective `(P, f)`, accuracy `e`. -/
def callOf (cfg : Cfg d) (H : Matrix (Fin d) (Fin d) ℚ) (g : Fin d → ℚ) (ℓ r : ℚ) (P : Matrix (Fin d) (Fin d) ℚ)
    (f : Fin d → ℚ) (e : ℚ) : CallQ d :=
  ⟨cfg.m, cfg.α, fun i => (1 - cfg.par.eps) * cfg.β i, H, g, ℓ, cfg.par.Rint, r, P, f, e⟩

/-! ## The draws (R1) -/

/-- The two `B`-coin integers `(U, W)` of block `j` of round `t`, on the schedule `Sched.blkStart`. -/
def blkUW (cs : ℕ → Bool) (K0 B d t j : ℕ) : ℕ × ℕ :=
  ((readCoins cs (Sched.blkStart d K0 B t j) B).toNat, (readCoins cs (Sched.blkStart d K0 B t j + B) B).toNat)

/-- The two outputs of BM-INT on a block, `Γ/2^{2 p_B}`. -/
def gOut (B : ℕ) (UW : ℕ × ℕ) : ℚ × ℚ :=
  (((gsSpec B UW.1 UW.2).1 : ℚ) / 2 ^ (2 * gsm_prec B), ((gsSpec B UW.1 UW.2).2 : ℚ) / 2 ^ (2 * gsm_prec B))

/-- R1 DRAW: the draw `ξ'_t` (coordinate `i` from block `i/2`, first output for even `i`) and the dither `ζ'_t` (half
the first output of the last block). -/
def draw (cs : ℕ → Bool) (K0 B d t : ℕ) : (Fin d → ℚ) × ℚ :=
  (fun i => if (i : ℕ) % 2 = 0 then (gOut B (blkUW cs K0 B d t ((i : ℕ) / 2))).1
    else (gOut B (blkUW cs K0 B d t ((i : ℕ) / 2))).2,
   (gOut B (blkUW cs K0 B d t ((d + 1) / 2))).1 / 2)

/-! ## One round (R5 to R15) -/

/-- The levels and accuracies of Procedure PARAM. -/
def LT (P : Par) : ℚ := 799 / 100 * P.rho - P.eHat

/-- The level of line μ. -/
def Lmu (P : Par) : ℚ := 8 * P.rho - P.eHat

/-- BL's radius `r' = s'_b (1 - ε')`. -/
def rB (P : Par) : ℚ := P.sb * (1 - P.eps)

/-- The accuracy of line μ, `e_BL = δe/(128 n² R'² d)`. -/
def eBL (P : Par) (d n : ℕ) : ℚ := 1 / (P.Ne * (128 * (n : ℚ) ^ 2 * P.R ^ 2 * d))

/-- The round after the play, from the mode before the round, the draw `ξ'`, the dither `ζ'` and the reading
`obs = ⌊2^p f_t(x'_t)⌋` (R4): R5 YOBS to R15 COMMIT. The mode after the round. -/
def step (ap : CallQ d → Option (Fin d → ℚ)) (cfg : Cfg d) (n : ℕ) (mo : Mode d) (ξ : Fin d → ℚ) (ζ : ℚ)
    (obs : ℤ) : Mode d :=
  match mo with
  | .off => .off
  | .guard => .guard
  | .run st =>
    let P := cfg.par
    let w := st.A *ᵥ ξ
    let X := XQ cfg st ξ
    let pt := ptQ cfg X
    -- R5 YOBS
    let Y := rnd P.p (pt * ((obs : ℚ) / 2 ^ P.p + ζ) / 2 + 2 * (pt - 1) / P.eps)
    -- R7 FACTOR
    let c := P.kapc * Y
    let a := 1 - c
    let q := a + c * (ξ ⬝ᵥ ξ)
    if a < 1 / 2 ∨ q < 1 / 2 then .guard else
    let s1 := sqrtDn P.p (1 / a)
    let s3 := sqrtDn P.p a
    let rq := sqrtDn P.p q
    let s2 := rnd P.p (c / (s3 * rq * (s3 + rq)))
    let s4 := rnd P.p (c / (s3 + rq))
    -- R8 PAIR
    let A' := rndM P.p (s1 • st.A - s2 • vecMulVec w ξ)
    let B' := rndM P.p (s3 • st.B + s4 • vecMulVec (st.B *ᵥ ξ) ξ)
    -- R9 INCR
    let u := st.B *ᵥ ξ
    let v := st.Bᵀ *ᵥ st.mu
    let b' := st.b + rndV P.p (c • ((u ⬝ᵥ st.mu) • u - st.B *ᵥ v))
    let k' := st.k + rnd P.p (c / 2 * ((u ⬝ᵥ st.mu) ^ 2 - v ⬝ᵥ v))
    let g := rndV P.p ((Y * P.nu) • u)
    let G' := st.G + g
    let l' := st.l + rnd P.p (g ⬝ᵥ st.mu)
    -- R10 TRACE
    if 2 * (P.Lam : ℚ) < frob2 B' ∨ 2 * (P.Lam : ℚ) < frob2 A' then .guard else
    let Pp := B' * B'ᵀ
    let wp := b' - (P.eta / 2) • G'
    -- R11 TEST (first round of an epoch: the region `K_ε'`, the ball radius `1 - ε'`)
    let callT : CallQ d :=
      if st.first then callOf cfg 0 0 0 (1 - P.eps) Pp wp ((1 - P.eps) ^ 2 / (P.Ne * d * 8))
      else callOf cfg (st.B * st.Bᵀ) st.b (LT P - st.k) (rB P / 2) Pp wp (rB P ^ 2 / (P.Ne * d * 8))
    match ap callT with
    | none => .guard
    | some p' =>
      -- R12 FIRE
      if P.eta * (l' - G' ⬝ᵥ p') - 2 * (p' ⬝ᵥ (Pp *ᵥ p') / 2 - b' ⬝ᵥ p' + k') ≤ -P.rho + P.eHat then
        .run (init P d)
      else
      -- R13 WMU
      let s5 := rnd P.p (P.eta * Y * P.nu / q)
      let wmu := st.mu - s5 • w
      if (2 * P.W) ^ 2 < wmu ⬝ᵥ wmu then .guard else
      -- R14 LINE
      match ap (callOf cfg Pp b' (Lmu P - k') (rB P / 2) Pp (Pp *ᵥ wmu) (eBL P d n)) with
      | none => .guard
      -- R15 COMMIT
      | some mu' => .run ⟨false, mu', A', B', b', k', G', l'⟩

/-! ## The run against a strategy -/

/-- BL's configuration on the input `(d, n, m, A, b)` on the coin stream `cs`: P1, P2, P3, P4. -/
def cfgOf (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (cs : ℕ → Bool) : Cfg d :=
  mkCfg d n m A b (R.ctr d n m A b) (R.pos d n m A b cs)

/-- The draw of round `t`. -/
def drawAt (R : Routines) (d n : ℕ) (cs : ℕ → Bool) (t : ℕ) : (Fin d → ℚ) × ℚ :=
  draw cs (R.K0 d n) (par d n).B d t

/-- BL's run against the strategy `σ` on the coins `cs`: the mode before round `t` and the points played in the
rounds `< t` (`0` from round `t` on). The reading of round `t` is `⌊2^p f_t(x'_t)⌋` with the loss
`f_t = lossAd σ 0 x t` of the frozen statement (the game has no noise). -/
noncomputable def traj (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d)
    (cs : ℕ → Bool) : ℕ → Mode d × (ℕ → Fin d → ℚ)
  | 0 => (mode0 (cfgOf R d n m A b cs), fun _ => 0)
  | t + 1 =>
    let cfg := cfgOf R d n m A b cs
    let prev := traj R d n m A b σ cs t
    let dr := drawAt R d n cs t
    let x := playPt cfg prev.1 dr.1
    let h := Function.update prev.2 t x
    let o : ℤ := ⌊(2 : ℝ) ^ cfg.par.p * lossAd σ 0 (fun i => toE (h i)) t (toE x)⌋
    (step R.ap cfg n prev.1 dr.1 dr.2 o, h)

/-- BL's mode before round `t`. -/
noncomputable def modeAt (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (σ : Strategy d) (cs : ℕ → Bool) (t : ℕ) : Mode d :=
  (traj R d n m A b σ cs t).1

/-- BL's play of round `t`, a rational point. -/
noncomputable def play (R : Routines) (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (σ : Strategy d)
    (cs : ℕ → Bool) (t : ℕ) : Fin d → ℚ :=
  playPt (cfgOf R d n m A b cs) (modeAt R d n m A b σ cs t) (drawAt R d n cs t).1

end AdversarialBco.Bit.BLP
