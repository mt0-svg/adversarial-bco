/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.RoutQ
public import AdversarialBco.Bit.Transfer.XTriEnt

@[expose] public section

/-!
# TRI-M in integers

The integers that the program of `TriRule` (Bit/RoutM.lean) computes, as pure functions mirroring its loops: the
machine rules state their invariants on these, and `tzPos_eq` (XTriChain.lean) relates the result to `posQ`
(Bit/RoutQ.lean).

* The grid of the iterates `2^{-G}`, `G = B_v + j_s + j_a` (`tzG`); the stage position `(μ̂, T̂) / D`.
* The rows of stage `j`, each scaled by its own positive factor: `tzRowA` (the cleared input rows `frAl`, then `e_i`,
  `-e_i`), `tzRowB` (`β'`: `frBe D`, then `ĉ_i 2^e + 2^j D`, `2^j D - ĉ_i 2^e`); `β̃ = β' - a'·μ̂`.
* The scan of the rows (`qn`, `scanStep`, `scan`): the quotient `N/β̃` sign-normalised, kept when strictly above the
  best so far; the kept row `sgn(β̃) a'` and `|β̃|`, else `0` and `1`.
* One draw (`tzZ`, `tzRMu`, `tzRLow`, `tzRDiag`, `tzUpd`), the iterates and their sum (`tzIter`, `tzSum`), the
  composition (`tzComp`), the stages (`tzStage`).
-/

namespace AdversarialBco.Bit.TriM

open AdversarialBco.Bit.RQ AdversarialBco.Bit.Transfer Matrix

variable {d : ℕ}

/-- A position in integers: `(μ̂, T̂)`. -/
abbrev PosZ (d : ℕ) := (Fin d → ℤ) × Matrix (Fin d) (Fin d) ℤ

/-! ## Constants -/

/-- `G = B_v + j_s + j_a`, the grid `2^{-G}` of the iterates. -/
def tzG (d ℓ : ℕ) : ℕ := triBvQ d + triJsQ d ℓ + triJaQ d

/-- `G_c = G + n_e`, the grid of the core output (the average of `2^{n_e}` iterates). -/
def tzGc (d ℓ : ℕ) : ℕ := tzG d ℓ + triNeQ d ℓ

/-- `p`, the precision of BM-INT at `B_g` bits: the draws are integers over `2^{2p}`. -/
def tzP (d : ℕ) : ℕ := gsm_prec (triBgQ d)

/-- The constants of one draw: `P_B = 2^{B_v}`, `P_2 = 2^{2p}`, `P_G = 2^G`, `P_j = 2^{j_a}`, the box bounds at the
grid (`r 2^G`, `a 2^G`, `b 2^G`), and `d`. -/
structure DC where
  PB : ℤ
  P2 : ℤ
  PG : ℤ
  Pj : ℤ
  R : ℤ
  Al : ℤ
  Bh : ℤ
  dd : ℤ

/-- The constants of one draw at `(d, ℓ)`. -/
def tzDC (d ℓ : ℕ) : DC where
  PB := 2 ^ triBvQ d
  P2 := 2 ^ (2 * tzP d)
  PG := 2 ^ tzG d ℓ
  Pj := 2 ^ triJaQ d
  R := 2 ^ (triLa (triSQ d) - 3 + tzG d ℓ)
  Al := 2 ^ (triBvQ d + triJsQ d ℓ)
  Bh := 161 * 2 ^ (triLa (triSQ d) - 10 + tzG d ℓ)
  dd := d

/-! ## The scan of the rows -/

/-- The quotient `N / B` as a pair with a positive second entry: `(N, B)`, `(-N, -B)`, or `(0, 1)` for `B = 0`
(Lean's `x / 0 = 0`). -/
def qn (N B : ℤ) : ℤ × ℤ := if 0 < B then (N, B) else if B < 0 then (-N, -B) else (0, 1)

/-- The state of the scan: the best quotient `bn / bd`, the kept row and its `|β̃|`. -/
structure Scan (d : ℕ) where
  bn : ℤ
  bd : ℤ
  row : Fin d → ℤ
  bb : ℤ

/-- The start of the scan: quotient `0`, no row (`0`, `1`). -/
def scan0 : Scan d := ⟨0, 1, 0, 1⟩

/-- One row of the scan: kept when its normalised quotient is strictly above the best. -/
def scanStep (st : Scan d) (N B : ℤ) (a : Fin d → ℤ) : Scan d :=
  if st.bn * (qn N B).2 < (qn N B).1 * st.bd then ⟨(qn N B).1, (qn N B).2, Int.sign B • a, (qn N B).2⟩ else st

/-- The scan of the rows `0, ..., k - 1`. -/
def scan (N B : ℕ → ℤ) (a : ℕ → Fin d → ℤ) : ℕ → Scan d
  | 0 => scan0
  | k + 1 => scanStep (scan N B a k) (N k) (B k) (a k)

/-! ## The rows of a stage -/

/-- `a'`: the cleared input rows, then `e_i` and `-e_i`. -/
def tzRowA {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : Fin (m + (d + d)) → Fin d → ℤ :=
  Fin.append (frAl A b) (Fin.append (fun i => Pi.single i 1) (fun i => -Pi.single i 1))

/-- `β'` at the stage position of denominator `D = D_c 2^e` and the half-width `2^j`: `frBe D`, then `ĉ_i 2^e + 2^j D`
and `2^j D - ĉ_i 2^e`. -/
def tzRowB {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (ch : Fin d → ℤ) (e j : ℕ) (D : ℤ) :
    Fin (m + (d + d)) → ℤ :=
  Fin.append (fun k => frBe A b k * D)
    (Fin.append (fun i => ch i * 2 ^ e + 2 ^ j * D) (fun i => 2 ^ j * D - ch i * 2 ^ e))

/-- A row family on `Fin M` read on `ℕ` (`0` past `M`). -/
def onN {M : ℕ} {α : Type*} [Zero α] (f : Fin M → α) (k : ℕ) : α := if h : k < M then f ⟨k, h⟩ else 0

/-! ## One draw -/

/-- `ẑ = X̂_μ 2^{2p} + X̂_T Y`, `μ + T y` at the grid `2^{-(G + 2p)}`. -/
def tzZ (X : PosZ d) (Y : Fin d → ℤ) (P2 : ℤ) : Fin d → ℤ := fun i => X.1 i * P2 + ∑ l, X.2 i l * Y l

/-- The entry `μ_i` of the rounded subgradient at the grid `2^{-B_v}`. -/
def tzRMu (A : Fin d → ℤ) (Bb PB : ℤ) (i : Fin d) : ℤ := A i * PB / Bb

/-- The entry `(i, l)`, `l < i`, of the rounded subgradient. -/
def tzRLow (A Y : Fin d → ℤ) (Bb PB P2 : ℤ) (i l : Fin d) : ℤ := A i * Y l * PB / (Bb * P2)

/-- The entry `(i, i)` of the rounded subgradient: `⌊(A_i Y_i / (|β̃| P_2) - P_G / (8 d T̂_ii)) P_B⌋`. -/
def tzRDiag (A Y : Fin d → ℤ) (Bb PB P2 PG dd Tii : ℤ) (i : Fin d) : ℤ :=
  (A i * Y i * (8 * dd * Tii) - PG * Bb * P2) * PB / (Bb * P2 * (8 * dd * Tii))

/-- The next iterate at the grid, from the kept row read in the stage position (`A = T̂ᵀ row`), its `|β̃|` and the draw
`Y`. -/
def tzUpd (c : DC) (X : PosZ d) (A Y : Fin d → ℤ) (Bb : ℤ) : PosZ d :=
  (fun i => clipZ (-c.R) c.R (X.1 i - tzRMu A Bb c.PB i * c.Pj),
   fun i l => if l < i then clipZ (-c.Bh) c.Bh (X.2 i l - tzRLow A Y Bb c.PB c.P2 i l * c.Pj)
     else if l = i then clipZ c.Al c.Bh (X.2 i i - tzRDiag A Y Bb c.PB c.P2 c.PG c.dd (X.2 i i) i * c.Pj)
     else 0)

/-! ## The core of a stage -/

/-- The scan at the point `ẑ`: `ŵ = T̂ ẑ`, `N_k = a'_k · ŵ`, `β̃_k = β'_k - a'_k · μ̂`, over the rows `k < M`. -/
def tzKeep (T : Matrix (Fin d) (Fin d) ℤ) (mu : Fin d → ℤ) (ra : ℕ → Fin d → ℤ) (rb : ℕ → ℤ) (M : ℕ)
    (z : Fin d → ℤ) : Scan d :=
  scan (fun k => ra k ⬝ᵥ (T *ᵥ z)) (fun k => rb k - ra k ⬝ᵥ mu) ra M

/-- One draw of the core: the scan at `ẑ`, `A = T̂ᵀ row`, the update. -/
def tzStep1 (c : DC) (T : Matrix (Fin d) (Fin d) ℤ) (mu : Fin d → ℤ) (ra : ℕ → Fin d → ℤ) (rb : ℕ → ℤ) (M : ℕ)
    (X : PosZ d) (Y : Fin d → ℤ) : PosZ d :=
  tzUpd c X (Tᵀ *ᵥ (tzKeep T mu ra rb M (tzZ X Y c.P2)).row) Y (tzKeep T mu ra rb M (tzZ X Y c.P2)).bb

/-- The iterates at the grid: `X̂_0 = (0, P_G I)`. -/
def tzIter (c : DC) (T : Matrix (Fin d) (Fin d) ℤ) (mu : Fin d → ℤ) (ra : ℕ → Fin d → ℤ) (rb : ℕ → ℤ) (M : ℕ)
    (Y : ℕ → Fin d → ℤ) : ℕ → PosZ d
  | 0 => (0, c.PG • 1)
  | t + 1 => tzStep1 c T mu ra rb M (tzIter c T mu ra rb M Y t) (Y t)

/-- The sum of the first `N` iterates. -/
def tzSum (c : DC) (T : Matrix (Fin d) (Fin d) ℤ) (mu : Fin d → ℤ) (ra : ℕ → Fin d → ℤ) (rb : ℕ → ℤ) (M : ℕ)
    (Y : ℕ → Fin d → ℤ) (N : ℕ) : PosZ d :=
  ∑ t ∈ Finset.range N, tzIter c T mu ra rb M Y t

/-- Draw `t` of the stage coins `x`: the numerators of `triDrawQ d B x t` over `2^{2 gsm_prec B}`. -/
def tzY (d B : ℕ) (x : ℕ → Bool) (t : ℕ) : Fin d → ℤ := fun i =>
  (gsSpec B (BitRAM.readCoins x (2 * (t * d + i) * B) B).toNat
    (BitRAM.readCoins x ((2 * (t * d + i) + 1) * B) B).toNat).1

/-! ## The stages -/

/-- A stage position in integers: `(μ̂, T̂) / D`. -/
structure StZ (d : ℕ) where
  D : ℤ
  mu : Fin d → ℤ
  T : Matrix (Fin d) (Fin d) ℤ

/-- `pgComp` at the grids: `P = (μ̂, T̂)/D` and the core output `S/2^{G_c}` give `(μ̂ 2^{G_c} + T̂ Ŝ_μ, T̂ Ŝ_T)/(D 2^{G_c})`. -/
def tzComp (P : StZ d) (S : PosZ d) (Gc : ℕ) : StZ d :=
  ⟨P.D * 2 ^ Gc, fun i => P.mu i * 2 ^ Gc + (P.T *ᵥ S.1) i, P.T * S.2⟩

/-- The stages on the input `(A, b)`, the frame centre `ĉ / D_c` and the stage coins `ω`: `P_0 = (2ĉ, D_c I)/(2D_c)`;
stage `j` runs the core on the rows of `K ∩ triCube c 2^j` read in `P_j`, whose denominator is `D_c 2^{1 + j G_c}`. -/
def tzStage (n : ℕ) {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (Dc : ℤ) (ch : Fin d → ℤ)
    (ω : ℕ → ℕ → Bool) : ℕ → StZ d
  | 0 => ⟨2 * Dc, fun i => 2 * ch i, Dc • 1⟩
  | j + 1 =>
    tzComp (tzStage n A b Dc ch ω j)
      (tzSum (tzDC d (ellPos d n)) (tzStage n A b Dc ch ω j).T (tzStage n A b Dc ch ω j).mu (onN (tzRowA A b))
        (onN (tzRowB A b ch (1 + j * tzGc d (ellPos d n)) j (tzStage n A b Dc ch ω j).D)) (m + (d + d))
        (tzY d (triBgQ d) (ω j)) (2 ^ triNeQ d (ellPos d n)))
      (tzGc d (ellPos d n))

/-- The position of the program on the coins `cs`: stage `j` reads `cs (j L + k)`. -/
def tzPos (n : ℕ) {m : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (Dc : ℤ) (ch : Fin d → ℤ)
    (cs : ℕ → Bool) : StZ d :=
  tzStage n A b Dc ch (fun j k => cs (triLay (triMstQ (1 / 2) n) (triLQ d (ellPos d n)) (j, k)))
    (triMstQ (1 / 2) n)

end AdversarialBco.Bit.TriM
