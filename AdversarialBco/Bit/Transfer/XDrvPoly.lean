/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XDrvBL
public import AdversarialBco.Bit.Transfer.XBLSetupPos
public import AdversarialBco.Bit.Transfer.XBLSetupKs

@[expose] public section

/-!
# BL's program driver: the parameters and their polynomial bounds

* `PolyB S X f`: `f ≤ c X^k` on the inputs `S`, with `c` and `k` uniform; closed under sums, products, powers,
  bit lengths and `2^size`;
* `DrvK`: the constants of the round, of FRAME and of TRI; the layout `DrvK.L`; for an input, the exponent `E` of BL's
  invariant, the bits `ℓ` of the magnitudes and `ℓa` of the registers, the units of the setup and of a round, and the
  totals `cost`, `space` of `prog_ok_frozenR`;
* `drv_poly`: `cost` and `space` at most `c (d m (size n + 1)(size M + 1))^k` on every input of the frozen statement.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ
  AdversarialBco.Bit.Asm
open AdversarialBco.RealRAM (Strategy polytope HeightLE)

/-! ## Polynomial bounds, uniformly over the inputs -/

/-- `f ≤ c X^k` on `S`, for some `c`, `k` that do not depend on the input. -/
def PolyB {ι : Type*} (S : ι → Prop) (X f : ι → ℕ) : Prop := ∃ c k : ℕ, ∀ i, S i → f i ≤ c * X i ^ k

namespace PolyB

variable {ι : Type*} {S : ι → Prop} {X f g : ι → ℕ}

theorem mono (h : PolyB S X g) (hfg : ∀ i, S i → f i ≤ g i) : PolyB S X f := by
  obtain ⟨c, k, h⟩ := h
  exact ⟨c, k, fun i hi => (hfg i hi).trans (h i hi)⟩

theorem const (c : ℕ) : PolyB S X (fun _ => c) := ⟨c, 0, fun i _ => by simp⟩

theorem self : PolyB S X X := ⟨1, 1, fun i _ => by simp⟩

theorem le_X (h : ∀ i, S i → f i ≤ X i) : PolyB S X f := self.mono h

theorem add (hX : ∀ i, S i → 1 ≤ X i) (hf : PolyB S X f) (hg : PolyB S X g) :
    PolyB S X (fun i => f i + g i) := by
  obtain ⟨c1, k1, h1⟩ := hf
  obtain ⟨c2, k2, h2⟩ := hg
  refine ⟨c1 + c2, k1 + k2, fun i hi => ?_⟩
  have e1 : X i ^ k1 ≤ X i ^ (k1 + k2) := Nat.pow_le_pow_right (hX i hi) (by omega)
  have e2 : X i ^ k2 ≤ X i ^ (k1 + k2) := Nat.pow_le_pow_right (hX i hi) (by omega)
  calc f i + g i ≤ c1 * X i ^ k1 + c2 * X i ^ k2 := Nat.add_le_add (h1 i hi) (h2 i hi)
    _ ≤ c1 * X i ^ (k1 + k2) + c2 * X i ^ (k1 + k2) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ e1) (Nat.mul_le_mul_left _ e2)
    _ = (c1 + c2) * X i ^ (k1 + k2) := (add_mul _ _ _).symm

theorem mul (hf : PolyB S X f) (hg : PolyB S X g) : PolyB S X (fun i => f i * g i) := by
  obtain ⟨c1, k1, h1⟩ := hf
  obtain ⟨c2, k2, h2⟩ := hg
  refine ⟨c1 * c2, k1 + k2, fun i hi => ?_⟩
  calc f i * g i ≤ (c1 * X i ^ k1) * (c2 * X i ^ k2) := Nat.mul_le_mul (h1 i hi) (h2 i hi)
    _ = c1 * c2 * X i ^ (k1 + k2) := by rw [pow_add]; ring

theorem pow (hf : PolyB S X f) (j : ℕ) : PolyB S X (fun i => f i ^ j) := by
  obtain ⟨c, k, h⟩ := hf
  refine ⟨c ^ j, k * j, fun i hi => ?_⟩
  calc f i ^ j ≤ (c * X i ^ k) ^ j := Nat.pow_le_pow_left (h i hi) j
    _ = c ^ j * X i ^ (k * j) := by rw [mul_pow, ← pow_mul]

theorem size (hf : PolyB S X f) : PolyB S X (fun i => (f i).size) :=
  hf.mono fun _ _ => Nat.size_le.2 Nat.lt_two_pow_self

theorem two_pow_size_le (x : ℕ) : 2 ^ x.size ≤ 2 * x + 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  have hs : 0 < x.size := Nat.size_pos.2 hx
  have h2 : 2 ^ (x.size - 1) ≤ x := Nat.lt_size.1 (by omega)
  have e : 2 ^ x.size = 2 * 2 ^ (x.size - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

theorem two_pow_size (hX : ∀ i, S i → 1 ≤ X i) (hf : PolyB S X f) : PolyB S X (fun i => 2 ^ (f i).size) :=
  (((const 2).mul hf).add hX (const 1)).mono fun i _ => two_pow_size_le (f i)

end PolyB

/-! ## The inputs -/

/-- An input of the frozen statement, its integers and its polytope. -/
structure DInp where
  d : ℕ
  n : ℕ
  m : ℕ
  M : ℕ
  A : Matrix (Fin m) (Fin d) ℚ
  b : Fin m → ℚ

/-- The inputs of the frozen statement. -/
def DInp.OK (i : DInp) : Prop := InputOK i.d i.n i.m i.M i.A i.b

/-- The size of an input, `d m (size n + 1)(size M + 1)`. -/
def DInp.X (i : DInp) : ℕ := i.d * i.m * (i.n.size + 1) * (i.M.size + 1)

variable {d : ℕ}

/-- An input of the frozen statement has a row: with no row the polytope is the whole space, of infinite diameter. -/
theorem inputOK_m_pos {n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} (hI : InputOK d n m M A b) :
    1 ≤ m := by
  by_contra hm
  obtain rfl : m = 0 := by omega
  obtain ⟨c, -⟩ := hI.ball
  have hK : ∀ x : E d, x ∈ polytope A b := fun x i => i.elim0
  let e : E d := EuclideanSpace.single ⟨0, hI.hd⟩ 1
  have h := hI.diam c (hK c) (c + ((n : ℝ) + 1) • e) (hK _)
  rw [dist_self_add_right, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)] at h
  linarith

/-- On an input of the frozen statement, `M ≥ 1`: the denominators are at least `1`. -/
theorem inputOK_M_pos {n m M : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} (hI : InputOK d n m M A b) :
    1 ≤ M := by
  have hm := inputOK_m_pos hI
  have h := (hI.height.2 ⟨0, hm⟩).2
  have := (b ⟨0, hm⟩).pos
  omega

theorem DInp.X_ge {i : DInp} (h : i.OK) :
    i.d ≤ i.X ∧ i.m ≤ i.X ∧ i.n.size + 1 ≤ i.X ∧ i.M.size + 1 ≤ i.X ∧ 1 ≤ i.X := by
  have hd : 1 ≤ i.d := h.hd
  have hm : 1 ≤ i.m := inputOK_m_pos h
  unfold DInp.X
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc i.d = i.d * 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr <;> omega
  · calc i.m = 1 * i.m * 1 * 1 := by ring
      _ ≤ _ := by gcongr <;> omega
  · calc i.n.size + 1 = 1 * 1 * (i.n.size + 1) * 1 := by ring
      _ ≤ _ := by gcongr; omega
  · calc i.M.size + 1 = 1 * 1 * 1 * (i.M.size + 1) := by ring
      _ ≤ _ := by gcongr; omega
  · calc 1 = 1 * 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr <;> omega

/-! ## The constants and the parameters of the driver -/

/-- The constants of the round (`RoundSpec`), of FRAME (`FrameSpec`) and of TRI (`TriSpec`). -/
structure DrvK where
  C : ℕ
  k : ℕ
  Cn : ℕ
  kn : ℕ
  nS : ℕ
  nN : ℕ
  nA : ℕ
  Cf : ℕ
  kf : ℕ
  nSf : ℕ
  nNf : ℕ
  nAf : ℕ
  Ct : ℕ
  kt : ℕ
  nSt : ℕ
  nNt : ℕ
  nAt : ℕ

namespace DrvK

variable (K : DrvK)

/-- The layout of BL's program: room for BL's cells (`BLLay`), the round's block, FRAME's and TRI's blocks. -/
def L : Layout :=
  { NN := 65 + K.nN + K.nNf + K.nNt, NS := 771 + K.nS + K.nSf + K.nSt, NA := 34 + K.nA + K.nAf + K.nAt }

/-- The bound of the position, the bits of TRI's integers. -/
def E0 (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : ℕ :=
  sT K.Ct K.kt d n m (sF K.Cf K.kf d m A b) A b

/-- What the setup asks of `E`. -/
def ES (d n m M : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : ℕ :=
  75 * parG d n + 343 + sF K.Cf K.kf d m A b + sT K.Ct K.kt d n m (sF K.Cf K.kf d m A b) A b + M.size + m

/-- The exponent of BL's invariant: what the setup asks, and what the round asks at the bound `E0` of the position. -/
def E (d n m M : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : ℕ :=
  K.ES d n m M A b + K.Cn * (d + m + M.size + n.size + K.E0 d n m A b + 1) ^ K.kn

/-- The units of a round. -/
def Kr (d n m M : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : ℕ :=
  K.C * (d + m + M.size + n.size + K.E d n m M A b + 1) ^ K.k

/-- The bits of the magnitudes. -/
def ell (d n m M : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : ℕ :=
  3 * (K.E d n m M A b * d) + 10 * K.E d n m M A b + 5 + K.Kr d n m M A b

/-- Every count that a register must hold. -/
def Q (d n m M : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : ℕ :=
  K.E d n m M A b + 2 * ((d + 1) * m) + 4 + K.Kr d n m M A b + (K.L.NN + K.L.NS + K.L.NA + 8) +
    K.L.base d K.L.NA + offOf d m + d + 4

/-- The bits of the registers. -/
def ella (d n m M : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : ℕ := (K.Q d n m M A b).size

/-- The units of the setup. -/
def Ks (d n m : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : ℕ :=
  K.L.NS + 2 * K.L.NA + 7 + initUnits d n m (sF K.Cf K.kf d m A b) (sT K.Ct K.kt d n m (sF K.Cf K.kf d m A b) A b)

/-- The cost bound of `prog_ok_frozenR`. -/
def cost (d n m M : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : ℕ :=
  costP (K.ella d n m M A b) (K.ell d n m M A b) (K.Ks d n m A b) +
    2 * costR (K.ella d n m M A b) (K.ell d n m M A b) (K.Kr d n m M A b)

/-- The space bound of `prog_ok_frozenR`, in `ℕ`. -/
def space (d n m M : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) : ℕ :=
  max (inSpace d n m M) (ckSpace d n m M (K.ella d n m M A b) (K.ell d n m M A b)) +
    (costP (K.ella d n m M A b) (K.ell d n m M A b) (K.Ks d n m A b) +
      costR (K.ella d n m M A b) (K.ell d n m M A b) (K.Kr d n m M A b))

theorem Q_lt (d n m M : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) :
    K.Q d n m M A b < 2 ^ K.ella d n m M A b := Nat.lt_size_self _

end DrvK

/-! ## The polynomial bounds -/

theorem len_natCast_le (x : ℕ) : BitRAM.len (x : ℤ) ≤ x := by
  unfold BitRAM.len
  rw [Int.natAbs_natCast]
  exact Nat.size_le.2 Nat.lt_two_pow_self

/-- **The totals of the driver are polynomial** in `d m (size n + 1)(size M + 1)` on the inputs of the frozen
statement. -/
theorem drv_poly (K : DrvK) : ∃ c k : ℕ, ∀ (d n m M : ℕ) (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ),
    InputOK d n m M A b →
      K.cost d n m M A b ≤ c * (d * m * (n.size + 1) * (M.size + 1)) ^ k ∧
      K.space d n m M A b ≤ c * (d * m * (n.size + 1) * (M.size + 1)) ^ k := by
  have hX : ∀ i : DInp, i.OK → 1 ≤ i.X := fun i h => (DInp.X_ge h).2.2.2.2
  have pd : PolyB DInp.OK DInp.X (fun i => i.d) := PolyB.le_X fun i h => (DInp.X_ge h).1
  have pm : PolyB DInp.OK DInp.X (fun i => i.m) := PolyB.le_X fun i h => (DInp.X_ge h).2.1
  have pns : PolyB DInp.OK DInp.X (fun i => i.n.size) := PolyB.le_X fun i h => by
    have := (DInp.X_ge h).2.2.1; omega
  have pMs : PolyB DInp.OK DInp.X (fun i => i.M.size) := PolyB.le_X fun i h => by
    have := (DInp.X_ge h).2.2.2.1; omega
  have pc : ∀ c : ℕ, PolyB DInp.OK DInp.X (fun _ => c) := PolyB.const
  have pES : PolyB DInp.OK DInp.X (fun i => K.ES i.d i.n i.m i.M i.A i.b) :=
    ⟨_, _, fun i h => setupE_le K.Cf K.kf K.Ct K.kt i.A i.b h.hd h.hn (inputOK_m_pos h) h.height (inputOK_M_pos h)⟩
  have pE0 : PolyB DInp.OK DInp.X (fun i => K.E0 i.d i.n i.m i.A i.b) :=
    pES.mono fun i _ => by unfold DrvK.E0 DrvK.ES; omega
  have pE : PolyB DInp.OK DInp.X (fun i => K.E i.d i.n i.m i.M i.A i.b) :=
    (pES.add hX ((pc K.Cn).mul (((((((pd.add hX pm).add hX pMs).add hX pns).add hX pE0).add hX
      (pc 1)).pow K.kn)))).mono fun i _ => le_rfl
  have pKr : PolyB DInp.OK DInp.X (fun i => K.Kr i.d i.n i.m i.M i.A i.b) :=
    ((pc K.C).mul ((((((pd.add hX pm).add hX pMs).add hX pns).add hX pE).add hX (pc 1)).pow K.k)).mono
      fun i _ => le_rfl
  have pell : PolyB DInp.OK DInp.X (fun i => K.ell i.d i.n i.m i.M i.A i.b) :=
    ((((pc 3).mul (pE.mul pd)).add hX ((pc 10).mul pE)).add hX (pc 5) |>.add hX pKr).mono fun i _ => le_rfl
  have pQ : PolyB DInp.OK DInp.X (fun i => K.Q i.d i.n i.m i.M i.A i.b) := by
    have p1 := ((((((((pE.add hX ((pc 2).mul ((pd.add hX (pc 1)).mul pm))).add hX (pc 4)).add hX pKr).add hX
      (pc (K.L.NN + K.L.NS + K.L.NA + 8))).add hX ((pc (K.L.NS + 1)).add hX ((pc K.L.NA).mul
      ((pd.mul pd).add hX pd)))).add hX ((pc 3).add hX ((pc 2).mul ((pd.add hX (pc 1)).mul pm)))).add hX pd).add hX
      (pc 4))
    refine p1.mono fun i _ => le_of_eq ?_
    simp only [DrvK.Q, Layout.base, asz, offOf]
    ring
  have pella : PolyB DInp.OK DInp.X (fun i => K.ella i.d i.n i.m i.M i.A i.b) := pQ.size
  have p2a : PolyB DInp.OK DInp.X (fun i => 2 ^ K.ella i.d i.n i.m i.M i.A i.b) := PolyB.two_pow_size hX pQ
  have pKs : PolyB DInp.OK DInp.X (fun i => K.Ks i.d i.n i.m i.A i.b) :=
    ((pc (K.L.NS + 2 * K.L.NA + 7)).add hX ⟨_, _, fun i h => initUnits_le K.Cf K.kf K.Ct K.kt i.A i.b h.hd h.hn
      (inputOK_m_pos h) h.height (inputOK_M_pos h)⟩).mono fun i _ => le_rfl
  have pxs : PolyB DInp.OK DInp.X (fun i => xstepCost (K.ella i.d i.n i.m i.M i.A i.b) (K.ell i.d i.n i.m i.M i.A i.b)) :=
    ((((pc 40).add hX ((pc 12).mul pella)).add hX ((pc 4).mul pell)).add hX
      (((pella.add hX pell).add hX (pc 1)).pow 2)).mono fun i _ => le_rfl
  have pcP : PolyB DInp.OK DInp.X (fun i => costP (K.ella i.d i.n i.m i.M i.A i.b) (K.ell i.d i.n i.m i.M i.A i.b)
      (K.Ks i.d i.n i.m i.A i.b)) :=
    ((pxs.add hX (pKs.mul pxs)).add hX (pc 5)).mono fun i _ => le_rfl
  have pcR : PolyB DInp.OK DInp.X (fun i => costR (K.ella i.d i.n i.m i.M i.A i.b) (K.ell i.d i.n i.m i.M i.A i.b)
      (K.Kr i.d i.n i.m i.M i.A i.b)) :=
    ((pKr.mul pxs).add hX (pc 6)).mono fun i _ => le_rfl
  have pcost : PolyB DInp.OK DInp.X (fun i => K.cost i.d i.n i.m i.M i.A i.b) :=
    (pcP.add hX ((pc 2).mul pcR)).mono fun i _ => le_rfl
  have poff : PolyB DInp.OK DInp.X (fun i => offOf i.d i.m) :=
    ((pc 3).add hX ((pc 2).mul ((pd.add hX (pc 1)).mul pm))).mono fun i _ => le_of_eq (by unfold offOf; ring)
  have plens : PolyB DInp.OK DInp.X (fun i => BitRAM.len (i.d : ℤ) + BitRAM.len (i.n : ℤ) + BitRAM.len (i.m : ℤ) +
      BitRAM.len (i.M : ℤ)) :=
    (((pd.add hX pns).add hX pm).add hX pMs).mono fun i _ => by
      have h1 := len_natCast_le i.d
      have h3 := len_natCast_le i.m
      have h2 : BitRAM.len (i.n : ℤ) = i.n.size := by unfold BitRAM.len; rw [Int.natAbs_natCast]
      have h4 : BitRAM.len (i.M : ℤ) = i.M.size := by unfold BitRAM.len; rw [Int.natAbs_natCast]
      omega
  have pin : PolyB DInp.OK DInp.X (fun i => inSpace i.d i.n i.m i.M) :=
    (poff.mul (poff.add hX plens)).mono fun i _ => by
      unfold inSpace
      have := len_natCast_le (offOf i.d i.m)
      gcongr
  have pck : PolyB DInp.OK DInp.X (fun i => ckSpace i.d i.n i.m i.M (K.ella i.d i.n i.m i.M i.A i.b)
      (K.ell i.d i.n i.m i.M i.A i.b)) :=
    ((poff.add hX ((pc 2).mul p2a)).mul ((((pc 2).mul pella).add hX pell).add hX plens |>.add hX (pc 3))).mono
      fun i _ => le_rfl
  have pspace : PolyB DInp.OK DInp.X (fun i => K.space i.d i.n i.m i.M i.A i.b) :=
    ((pin.add hX pck).add hX (pcP.add hX pcR)).mono fun i _ => by
      unfold DrvK.space
      have := max_le_add_of_nonneg (Nat.zero_le (inSpace i.d i.n i.m i.M))
        (Nat.zero_le (ckSpace i.d i.n i.m i.M (K.ella i.d i.n i.m i.M i.A i.b) (K.ell i.d i.n i.m i.M i.A i.b)))
      omega
  obtain ⟨c, k, h⟩ := pcost.add hX pspace
  refine ⟨c, k, fun d n m M A b hI => ?_⟩
  have := h ⟨d, n, m, M, A, b⟩ hI
  simp only [DInp.X] at this
  constructor <;> omega

end AdversarialBco.Bit.Transfer.BLM
