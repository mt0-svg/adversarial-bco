/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Statement

@[expose] public section

/-!
# Frozen statements: Theorem 1.1, Lemma 7.13 and Corollary 1.2 of the paper with explicit constants

The statements of the paper: Theorem 1.1, Lemma 7.13 and Corollary 1.2 in the policy class of Section 1.
The definitions `E`, `AdmLoss` and `Advs` are those of `AdversarialBco/Statement.lean` (the losses of `G(K)` are the
functions convex on `K` with values in `[0, 1]` on `K`; a sequence fixed in advance is an element of `Advs K n`).
Rounds are indexed from `0`: the paper's round `t` is round `t - 1` here.

## Algorithm 7.1

* The net. `h = ε / (2 d^{1/2} (D + 1))` (`mesh`). The scanned points are the points `h k`, `k ∈ ℤ^d`
  (`latticePt`), in the cube `x0 + [-D, D]^d` and in the inner body `J = {x : B(x, 1/n) ⊆ K}` (`scanSet`,
  `innerBody`). The paper scans them "in a fixed order"; the theorem holds for every order, given as a list of the
  scanned points without repetition (`IsScanOrder`), and states that one exists. A point is kept if its distance
  to every point kept so far is at least `ε/2` (`greedyKeep`); the net `C` is the set kept (`net`), `m = |C|`.
* A round. For the weights `q`, `S_q` (`SetS`, display (7.1)), `P_L` (`PL`), `R(p, g; f, y)` (`roundR`,
  display (7.2)). Step 1 asks for `(P_t, G_t) ∈ S_{q_t}` with `Rbar(P_t, G_t) ≤ inf_{S_{q_t}} Rbar + tol`, where
  `Rbar(p, g) = max_{y ∈ C} max_{f ∈ P_L} R(p, g; f, y)` (`IsStep1`). It is written without the infimum and the
  maximum: whenever a number `c` bounds `R(p', g'; f, y)` for some `(p', g') ∈ S_q` and all `y`, `f ∈ P_L`, the
  number `c + tol` bounds `R(p, g; f, y)` for all `y`, `f ∈ P_L`. This is `Rbar(p, g) ≤ Rbar(p', g') + tol` for
  every `(p', g') ∈ S_q`, that is `Rbar(p, g) ≤ inf Rbar + tol`. The deterministic procedure of step 1 is a map
  `sol` from weights to pairs, any map with this property at every positive probability vector (`IsSolver`); the
  theorem holds for every such map, and states that one exists.
* Steps 2 to 5. `X_t` is drawn from `P_t`, the coin `B_t` from `Bern(f_t(X_t))` (`bern`), the estimate is
  `lhat_t = G_t(X_t, B_t) / P_t(X_t)` and `q_{t+1}(y) ∝ q_t(y) exp(-η lhat_t(y))`, `q_0` uniform (`weights`); `P_t`
  is `exoKernel`, a function of the earlier actions and coins.
* The probability space. As in the proof of Theorem 7.2, the history `(X_0, B_0, ..., X_{n-1}, B_{n-1})` takes
  finitely many values, with the product law `coinLaw`: the mass of a history is the product over the rounds of
  `P_t(x_t)` and `Bern(f_t(x_t))(b_t)`, where `f_t` is the loss of round `t`, `A t` of the earlier actions and coins
  for an adaptive adversary (`AdaptAdv`), `f t` for a sequence fixed in advance. The regret against a sequence
  fixed in advance is `E Σ_t f_t(X_t) - inf_K Σ_t f_t` (`coinReg`); against an adaptive adversary the theorem bounds
  `E Σ_t (f_t(X_t) - f_t(x))` for every `x ∈ K` (`pseudoReg`), that is its supremum over `x ∈ K`.

## Policies (Section 1)

A `C`-policy maps each history `(x_0, o_0, ..., x_{t-1}, o_{t-1}) ∈ (K × [0, 1])^t` to a probability law on the
finite set `C ⊆ K`, given by its vector of masses (`IsCPolicy`); its values on other histories play no role, and no
measurability is asked. Its law of play against `f` is the product (1.2) (`playLaw`), its regret `policyReg`, and
`minimaxRegretC` is the infimum over finite `C ⊆ K` and `C`-policies of the supremum over `Advs K n` of the regret.
The policy of Lemma 7.13 is `margPolicy`, written as in the paper, for any learner with coins whose laws `P_t` are
probability vectors on `C` (the lemma is stated for every such learner, the learner of Algorithm 7.1 among them).

## Junk values

* `β > 0`, since `d ≥ 1`, `n ≥ 2` and `D ≥ diam K ≥ 2`; so `ε`, `h` and `√(2 β)` are positive. The theorem states
  `m ≥ 2`, so `log m > 0` and `η > 0`.
* `lhat_t` divides by `P_t(X_t)`; on a history where `P_t(x_t) = 0` the weights of the later rounds take a junk
  value, but the mass of every such history is `0`, so neither the law nor the regret sees it.
* The `sInf` in `coinReg` and `policyReg` is over the nonempty set of values of `Σ_t f_t` on `K`, bounded below
  by `0`. In `minimaxRegretC`, the `sSup` is over a nonempty set (the zero sequence) bounded above by `n`, and it
  is at least the regret `0` of the zero sequence; the `sInf` is over a nonempty set (a constant policy) bounded
  below by `0`. In the bounds of `TheoremExplicit`, `log (n D) ≥ log 4 > 0`, and in `CorollaryExplicit`,
  `log (n diam K) ≥ log 2 > 0` (`diam K ≥ 2`, and `n = 1` is allowed), so the real powers are the ordinary ones.
-/

open Real

namespace AdversarialBco.Explicit

/-- The probability vectors on the finite set `C`: nonnegative masses summing to `1`. -/
def probVecs (C : Type*) [Fintype C] : Set (C → ℝ) :=
  {p | (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1}

/-- The inner body `J = {x : B(x, 1/n) ⊆ K}` of Section 2. -/
def innerBody {d : ℕ} (K : Set (E d)) (n : ℕ) : Set (E d) :=
  {y | Metric.closedBall y (1 / (n : ℝ)) ⊆ K}

/-- The mesh `h = ε / (2 d^{1/2} (D + 1))` of the net of Algorithm 7.1. -/
noncomputable def mesh (d : ℕ) (ε D : ℝ) : ℝ :=
  ε / (2 * √(d : ℝ) * (D + 1))

/-- The point `h k` of the lattice `h ℤ^d`. -/
noncomputable def latticePt {d : ℕ} (h : ℝ) (k : Fin d → ℤ) : E d :=
  WithLp.toLp 2 fun i => h * (k i : ℝ)

/-- The scanned points of Algorithm 7.1: the `k ∈ ℤ^d` with `h k` in the cube `x0 + [-D, D]^d` and in `J`. -/
def scanSet {d : ℕ} (J : Set (E d)) (x0 : E d) (D h : ℝ) : Set (Fin d → ℤ) :=
  {k | (∀ i, |h * (k i : ℝ) - x0 i| ≤ D) ∧ latticePt h k ∈ J}

/-- A scan order: a list of the scanned points, each once. -/
def IsScanOrder {d : ℕ} (J : Set (E d)) (x0 : E d) (D h : ℝ) (ord : List (Fin d → ℤ)) : Prop :=
  ord.Nodup ∧ ∀ k, k ∈ ord ↔ k ∈ scanSet J x0 D h

open Classical in
/-- The greedy rule: scan `pts` in order and keep a point if its distance to every point kept so far is at
least `r`. -/
noncomputable def greedyKeep {d : ℕ} (r : ℝ) (pts : List (E d)) : List (E d) :=
  pts.foldl (fun kept z => if ∀ y ∈ kept, r ≤ dist z y then kept ++ [z] else kept) []

open Classical in
/-- The net `C` of Algorithm 7.1 for the scan order `ord`: the points `h k`, `k` along `ord`, kept by the greedy
rule with the radius `ε/2`. -/
noncomputable def net {d : ℕ} (ε D : ℝ) (ord : List (Fin d → ℤ)) : Finset (E d) :=
  (greedyKeep (ε / 2) (ord.map (latticePt (mesh d ε D)))).toFinset

/-- The set `S_q` of display (7.1): `p` a probability vector, and for every `(x, b)`,
`Σ_z q(z) exp(-η g(x, b)(z) / p(x)) ≤ 1` if `p(x) > 0`, `g(x, b) ≥ 0` if `p(x) = 0`. -/
def SetS {C : Type*} [Fintype C] (η : ℝ) (q : C → ℝ) : Set ((C → ℝ) × (C → Bool → C → ℝ)) :=
  {pg | pg.1 ∈ probVecs C ∧ ∀ x b,
    (0 < pg.1 x → ∑ z, q z * Real.exp (-η * (pg.2 x b z / pg.1 x)) ≤ 1) ∧ (pg.1 x = 0 → ∀ z, 0 ≤ pg.2 x b z)}

/-- The set `P_L`: the `v ∈ [0, 1]^C` with witnesses `s_x`, `|s_x| ≤ L`, such that
`v(z) ≥ v(x) + ⟨s_x, z - x⟩` for all `x, z ∈ C` (the points of `C` are `pt x`). -/
def PL {d : ℕ} {C : Type*} (pt : C → E d) (L : ℝ) : Set (C → ℝ) :=
  {v | (∀ x, v x ∈ Set.Icc (0 : ℝ) 1) ∧
    ∃ s : C → E d, (∀ x, ‖s x‖ ≤ L) ∧ ∀ x z, v x + inner ℝ (s x) (pt z - pt x) ≤ v z}

/-- `R(p, g; f, y)` of display (7.2). -/
def roundR {C : Type*} [Fintype C] (pg : (C → ℝ) × (C → Bool → C → ℝ)) (f : C → ℝ) (y : C) : ℝ :=
  ∑ x, pg.1 x * f x - f y + ∑ x, ((1 - f x) * pg.2 x false y + f x * pg.2 x true y)

/-- Step 1 of Algorithm 7.1 at the weights `q`: `(p, g) ∈ S_q` and `Rbar(p, g) ≤ inf_{S_q} Rbar + tol`, written
as: whenever `c` bounds `R(p', g'; f, y)` for some `(p', g') ∈ S_q` and all `y`, `f ∈ P_L`, `c + tol` bounds
`R(p, g; f, y)` for all `y`, `f ∈ P_L`. -/
def IsStep1 {d : ℕ} {C : Type*} [Fintype C] (pt : C → E d) (L η tol : ℝ) (q : C → ℝ)
    (pg : (C → ℝ) × (C → Bool → C → ℝ)) : Prop :=
  pg ∈ SetS η q ∧ ∀ pg' ∈ SetS η q, ∀ c : ℝ, (∀ y, ∀ f ∈ PL pt L, roundR pg' f y ≤ c) →
    ∀ y, ∀ f ∈ PL pt L, roundR pg f y ≤ c + tol

/-- A deterministic procedure for step 1: a map from weights to pairs that meets step 1 at every positive
probability vector. The paper applies the procedure only to the weights `q_t` the run meets; asking for step 1 at
every `q` loses nothing. A procedure that meets step 1 at the weights reached on the histories of positive mass can
be changed at the other weights into one that meets it everywhere (one exists), and the change alters no factor of
`coinLaw` at a history of positive mass; a history of mass `0` keeps mass `0`, since its first zero factor sits at
a prefix of positive mass, where `P_s` is unchanged. So the law and the regret stay the same. -/
def IsSolver {d : ℕ} {C : Type*} [Fintype C] (pt : C → E d) (L η tol : ℝ)
    (sol : (C → ℝ) → (C → ℝ) × (C → Bool → C → ℝ)) : Prop :=
  ∀ q : C → ℝ, (∀ z, 0 < q z) → ∑ z, q z = 1 → IsStep1 pt L η tol q (sol q)

/-- The weights `q_t` of Algorithm 7.1 after the actions and coins `h` of rounds `0, ..., t - 1`: `q_0` uniform,
`q_{t+1}(y) = q_t(y) exp(-η lhat_t(y)) / Σ_z q_t(z) exp(-η lhat_t(z))` with `lhat_t = G_t(X_t, B_t) / P_t(X_t)` and
`(P_t, G_t) = sol q_t`. -/
noncomputable def weights {C : Type*} [Fintype C] (η : ℝ) (sol : (C → ℝ) → (C → ℝ) × (C → Bool → C → ℝ)) :
    (t : ℕ) → (Fin t → C × Bool) → C → ℝ
  | 0 => fun _ _ => 1 / (Fintype.card C : ℝ)
  | t + 1 => fun h y =>
    weights η sol t (Fin.init h) y *
        Real.exp (-η * ((sol (weights η sol t (Fin.init h))).2 (h (Fin.last t)).1 (h (Fin.last t)).2 y /
          (sol (weights η sol t (Fin.init h))).1 (h (Fin.last t)).1)) /
      ∑ z, weights η sol t (Fin.init h) z *
        Real.exp (-η * ((sol (weights η sol t (Fin.init h))).2 (h (Fin.last t)).1 (h (Fin.last t)).2 z /
          (sol (weights η sol t (Fin.init h))).1 (h (Fin.last t)).1))

/-- The law `P_t` of the action of round `t` of Algorithm 7.1, after the actions and coins `h` of the earlier
rounds. -/
noncomputable def exoKernel {C : Type*} [Fintype C] (η : ℝ) (sol : (C → ℝ) → (C → ℝ) × (C → Bool → C → ℝ))
    (t : ℕ) (h : Fin t → C × Bool) : C → ℝ :=
  (sol (weights η sol t h)).1

/-- The mass of `b` under `Bern(o)`, `true` standing for `1`. -/
def bern (o : ℝ) (b : Bool) : ℝ :=
  if b then o else 1 - o

/-- The actions, as points, and the coins of the rounds before `s` in the history `h`. -/
def ptHist {d : ℕ} {C : Type*} (pt : C → E d) {n : ℕ} (h : Fin n → C × Bool) (s : Fin n) : Fin s → E d × Bool :=
  fun i => (pt (h (Fin.castLE s.2.le i)).1, (h (Fin.castLE s.2.le i)).2)

/-- The law of the history `(X_0, B_0, ..., X_{n-1}, B_{n-1})` of a learner that draws `X_s` from
`P s (X_0, B_0, ..., X_{s-1}, B_{s-1})` and then a coin `B_s` of mean `f_s(X_s)`, where the loss of round `s` is
`f_s = A s` of the earlier actions and coins: the mass of the history `h`. -/
noncomputable def coinLaw {d : ℕ} {C : Type*} (pt : C → E d) (P : (t : ℕ) → (Fin t → C × Bool) → C → ℝ)
    (A : (t : ℕ) → (Fin t → E d × Bool) → E d → ℝ) (n : ℕ) (h : Fin n → C × Bool) : ℝ :=
  ∏ s : Fin n, P s (fun i : Fin s => h (Fin.castLE s.2.le i)) (h s).1 *
    bern (A s (ptHist pt h s) (pt (h s).1)) (h s).2

/-- The adaptive adversaries over `n` rounds: in each round `t < n` the loss is a function of the earlier actions
and coins, with values in `G(K)`. The loss is asked to be in `G(K)` at every history in `(E d × Bool)^t`, while the
learner only produces histories of points of `C`; an adversary given on those histories only extends by the loss
`0 ∈ G(K)` to the others, which changes no regret. -/
def AdaptAdv {d : ℕ} (K : Set (E d)) (n : ℕ) : Set ((t : ℕ) → (Fin t → E d × Bool) → E d → ℝ) :=
  {A | ∀ t < n, ∀ χ, AdmLoss K (A t χ)}

/-- `E Σ_{t < n} (f_t(X_t) - f_t(x))` for the learner with coins `P` against the adaptive adversary `A`. -/
noncomputable def pseudoReg {d : ℕ} {C : Type*} [Fintype C] (pt : C → E d)
    (P : (t : ℕ) → (Fin t → C × Bool) → C → ℝ) (A : (t : ℕ) → (Fin t → E d × Bool) → E d → ℝ) (n : ℕ)
    (x : E d) : ℝ :=
  ∑ h : Fin n → C × Bool, coinLaw pt P A n h *
    ∑ t : Fin n, (A t (ptHist pt h t) (pt (h t).1) - A t (ptHist pt h t) x)

/-- The regret `E Σ_{t < n} f_t(X_t) - inf_K Σ_{t < n} f_t` of the learner with coins `P` against the sequence `f`
fixed in advance. -/
noncomputable def coinReg {d : ℕ} {C : Type*} [Fintype C] (K : Set (E d)) (pt : C → E d)
    (P : (t : ℕ) → (Fin t → C × Bool) → C → ℝ) (f : ℕ → E d → ℝ) (n : ℕ) : ℝ :=
  ∑ h : Fin n → C × Bool, coinLaw pt P (fun t _ => f t) n h * ∑ t : Fin n, f t (pt (h t).1) -
    sInf ((fun x => ∑ t ∈ Finset.range n, f t x) '' K)

/-- The three bounds of Theorem 1.1 on a quantity `r`, for the net size `m`. -/
def Bounds (d n : ℕ) (β D : ℝ) (m : ℕ) (r : ℝ) : Prop :=
  r ≤ 671 / 100 + √(β * n * Real.log m / 2) ∧
    r ≤ 671 / 100 + √(β * n * d * Real.log (5 * n ^ 2 * √(2 * β) * D) / 2) ∧
    r ≤ 190000 * (d : ℝ) ^ (3 / 2 : ℝ) * √(n : ℝ) * Real.log (n * D) ^ (3 / 2 : ℝ)

/-- Theorem 1.1. Let `d ≥ 1`, `n ≥ 2`, `K` a convex body containing `B(x0, 1)`, `D ≥ diam K`,
`β = 1.2 · 10^9 d^2 ln(n d D) ln(2n)` and `ε = 1/(n^2 (2β)^{1/2})`. For every scan order (one exists) the net of
Algorithm 7.1 has `2 ≤ m ≤ (5 n^2 (2β)^{1/2} D)^d`; with `η = (8 ln m/(n β))^{1/2}`, `tol = 1/n` and `L = n`, step 1
can be carried out, and for every procedure that carries it out the learner has, against every sequence fixed in
advance, regret at most `6.71 + (β n ln m / 2)^{1/2}`, at most `6.71 + (β n d ln(5 n^2 (2β)^{1/2} D) / 2)^{1/2}` and
at most `C_X d^{3/2} n^{1/2} ln^{3/2}(n D)` with `C_X = 1.9 · 10^5`; and the same three bounds hold for
`E Σ_t (f_t(X_t) - f_t(x))`, for every `x ∈ K`, when each `f_t` is a function of the earlier actions and coins. -/
def TheoremExplicit : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ n : ℕ, 2 ≤ n → ∀ K : Set (E d), IsCompact K → Convex ℝ K → ∀ x0 : E d,
    Metric.closedBall x0 1 ⊆ K → ∀ D : ℝ, Metric.diam K ≤ D →
    ∀ β ε : ℝ, β = 1200000000 * d ^ 2 * Real.log (n * d * D) * Real.log (2 * n) → ε = 1 / (n ^ 2 * √(2 * β)) →
      (∃ ord, IsScanOrder (innerBody K n) x0 D (mesh d ε D) ord) ∧
      ∀ ord, IsScanOrder (innerBody K n) x0 D (mesh d ε D) ord → ∀ C : Finset (E d), C = net ε D ord →
        2 ≤ C.card ∧ (C.card : ℝ) ≤ (5 * n ^ 2 * √(2 * β) * D) ^ d ∧
        ∀ η : ℝ, η = √(8 * Real.log C.card / (n * β)) →
          (∃ sol, IsSolver (Subtype.val : C → E d) n η (1 / n) sol) ∧
          ∀ sol, IsSolver (Subtype.val : C → E d) n η (1 / n) sol →
            (∀ f ∈ Advs K n, Bounds d n β D C.card (coinReg K Subtype.val (exoKernel η sol) f n)) ∧
            ∀ A ∈ AdaptAdv K n, ∀ x ∈ K,
              Bounds d n β D C.card (pseudoReg Subtype.val (exoKernel η sol) A n x)

/-- A `C`-policy on `K`: `C ⊆ K` is finite, and for every round `t` and every history
`(x_0, o_0, ..., x_{t-1}, o_{t-1}) ∈ (K × [0, 1])^t`, `pol t` of the history is a probability vector on `C`. -/
def IsCPolicy {d : ℕ} (K : Set (E d)) (C : Finset (E d)) (pol : (t : ℕ) → (Fin t → E d × ℝ) → C → ℝ) : Prop :=
  ↑C ⊆ K ∧ ∀ t (χ : Fin t → E d × ℝ), (∀ i, (χ i).1 ∈ K ∧ (χ i).2 ∈ Set.Icc (0 : ℝ) 1) →
    pol t χ ∈ probVecs C

/-- The law of play (1.2) of the policy `pol` against `f`: the mass of the actions `y ∈ C^n`. -/
noncomputable def playLaw {d : ℕ} {C : Finset (E d)} (pol : (t : ℕ) → (Fin t → E d × ℝ) → C → ℝ)
    (f : ℕ → E d → ℝ) (n : ℕ) (y : Fin n → C) : ℝ :=
  ∏ t : Fin n, pol t (fun i : Fin t => ((y (Fin.castLE t.2.le i) : E d), f i (y (Fin.castLE t.2.le i)))) (y t)

/-- The regret `E Σ_{t < n} f_t(x_t) - inf_K Σ_{t < n} f_t` of the policy `pol` under its law of play against `f`. -/
noncomputable def policyReg {d : ℕ} (K : Set (E d)) (C : Finset (E d))
    (pol : (t : ℕ) → (Fin t → E d × ℝ) → C → ℝ) (f : ℕ → E d → ℝ) (n : ℕ) : ℝ :=
  ∑ y : Fin n → C, playLaw pol f n y * ∑ t : Fin n, f t (y t) - sInf ((fun x => ∑ t ∈ Finset.range n, f t x) '' K)

/-- The minimax regret `Reg_n^⋆(G(K))` of Section 1: the infimum over finite sets `C ⊆ K` and `C`-policies of the
supremum over `G(K)^n` of the regret. -/
noncomputable def minimaxRegretC {d : ℕ} (K : Set (E d)) (n : ℕ) : ℝ :=
  sInf {r | ∃ (C : Finset (E d)) (pol : (t : ℕ) → (Fin t → E d × ℝ) → C → ℝ), IsCPolicy K C pol ∧
    r = sSup ((fun f => policyReg K C pol f n) '' Advs K n)}

open Classical in
/-- The policy `ϖ` of Lemma 7.13 for the learner with coins `P`. On a history `χ = (x_{<t}, o_{<t})` whose actions lie
in `C`, `φ_t(b | χ) ∝ Π_{s<t} P_s(x_s | x_{<s}, b_{<s}) Bern(o_s)(b_s)` and `ϖ_t(x | χ) = Σ_b φ_t(b | χ) P_t(x | x_{<t}, b)`
when the normalising sum is positive; `ϖ_t(· | χ)` is uniform on `C` otherwise, and when an action lies outside `C`. -/
noncomputable def margPolicy {d : ℕ} (C : Finset (E d)) (P : (t : ℕ) → (Fin t → C × Bool) → C → ℝ) (t : ℕ)
    (χ : Fin t → E d × ℝ) : C → ℝ :=
  if hχ : ∀ i, (χ i).1 ∈ C then
    if 0 < ∑ b : Fin t → Bool, ∏ s : Fin t,
        P s (fun i : Fin s => (⟨(χ (Fin.castLE s.2.le i)).1, hχ _⟩, b (Fin.castLE s.2.le i))) ⟨(χ s).1, hχ s⟩ *
          bern (χ s).2 (b s) then
      fun y => ∑ b : Fin t → Bool,
        (∏ s : Fin t,
            P s (fun i : Fin s => (⟨(χ (Fin.castLE s.2.le i)).1, hχ _⟩, b (Fin.castLE s.2.le i))) ⟨(χ s).1, hχ s⟩ *
              bern (χ s).2 (b s)) /
          (∑ b' : Fin t → Bool, ∏ s : Fin t,
            P s (fun i : Fin s => (⟨(χ (Fin.castLE s.2.le i)).1, hχ _⟩, b' (Fin.castLE s.2.le i))) ⟨(χ s).1, hχ s⟩ *
              bern (χ s).2 (b' s)) *
          P t (fun i => (⟨(χ i).1, hχ i⟩, b i)) y
    else fun _ => 1 / (C.card : ℝ)
  else fun _ => 1 / (C.card : ℝ)

/-- Lemma 7.13, for every learner with coins whose laws `P_t` are probability vectors on a finite
nonempty `C ⊆ K`: `ϖ` is a `C`-policy and a Borel function of the history, and against every `f ∈ G(K)^n` the
actions have the same law under `ϖ` as under the learner (the mass of `x ∈ C^n` under the learner is the sum over
the coins `b` of the mass of the history `(x, b)`); in particular the two have the same regret. -/
def LemmaMarg : Prop :=
  ∀ d : ℕ, ∀ K : Set (E d), ∀ C : Finset (E d), ↑C ⊆ K → C.Nonempty →
    ∀ P : (t : ℕ) → (Fin t → C × Bool) → C → ℝ, (∀ t h, P t h ∈ probVecs C) →
      IsCPolicy K C (margPolicy C P) ∧ (∀ t, Measurable (margPolicy C P t)) ∧
      ∀ n : ℕ, ∀ f ∈ Advs K n,
        (∀ x : Fin n → C, playLaw (margPolicy C P) f n x =
          ∑ b : Fin n → Bool, coinLaw Subtype.val P (fun t _ => f t) n fun t => (x t, b t)) ∧
        policyReg K C (margPolicy C P) f n = coinReg K Subtype.val P f n

/-- Corollary 1.2 for the policies of Section 1: for a convex body `K ⊆ ℝ^d` containing a ball of
radius `1` and every `n ≥ 1`, `Reg_n^⋆(G(K)) ≤ C_X d^{3/2} n^{1/2} ln^{3/2}(n diam K)` with `C_X = 1.9 · 10^5`. -/
def CorollaryExplicit : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∀ K : Set (E d), IsCompact K → Convex ℝ K → (∃ c : E d, Metric.closedBall c 1 ⊆ K) →
    ∀ n : ℕ, 1 ≤ n →
      minimaxRegretC K n ≤
        190000 * (d : ℝ) ^ (3 / 2 : ℝ) * √(n : ℝ) * Real.log (n * Metric.diam K) ^ (3 / 2 : ℝ)

end AdversarialBco.Explicit
