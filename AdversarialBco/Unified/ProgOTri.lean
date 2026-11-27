/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.ProgOSetup
public import AdversarialBco.Unified.ProgOTriZ

@[expose] public section

/-!
# TRI-OGD-O on the oracle machine: the sub-block contracts and their assembly

The contract `TriSpecO xtri C k nS nN nA` of Unified/ProgOSetup.lean split into named sub-blocks,
and `triSpecO_of`, which assembles it from them. The program `xtriO xpre xst xout L`:

1. **The prologue of TRI** (`TriPreSpec`): from `BasO` and `k_δ` in `sKd`, the constants of the block (a predicate
   `KE` on the cells, left to the prologue and kept by every stage), `1` in `rT`, `m_st` in `rT + 28`, and the first
   position `(a, r₀ I)` in integers (`tzP0`, from a representation `a = N_a/D_a`, `r₀ = r_n/r_d` of the input,
   `P0OK`) in the stage cells (`StAtO`).
2. **The stage loop**: `for j < m_st` (`j` in `rT + 27`) one stage (`TriStageSpec`): from `StAtO σ j P`, the stage
   reads its `triLT` coins and leaves `StAtO σ' (j + 1) (tzComp P (stSumO .. j P coins) G_c')`, the integer stage of
   ProgOTriZ.lean; it keeps `KE`, the counter, `m_st` and `1`.
3. **The output** (`TriOutSpec`): from `StAtO σ m_st P`, `P` into `sDS`, `aMuS`, `aAS` and `LposO` into `sLp`.

The magnitudes of the integer stages are a property of the model (`TriMagO`: every stage `j ≤ m_st` has a positive
denominator and entries at most `2^{C_m (W + 1)^{k_m}}`); every sub-block runs within `C (W + B + 1)^k` units under
`C (W + B + 1)^k ≤ ℓ` for a bound `2^B` of the stage it reads (the prologue within `C (W + 1)^k`). The rational
position is `posO` by `tzPosO_eq` (ProgOTriZ.lean).

The cells: the stage position `μ̂`, `T̂`, `D` in the array `aT`, the array `aT + 1` (cells `d i + l`) and the slot
`oT`, with `2^{j+1}` (the half-width of the stage cube over `r₀`) in the slot `oT + 36`; every block writes only
`sDS`, the slots above `29`, the registers from `8` on and `ATri d` (the frame of `TriSpecO`).
-/

namespace AdversarialBco.Unified.ProgO.TriO

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM
open AdversarialBco.Unified.ProgO
open BitRAM BitRAMO

variable {d : ℕ}

/-! ## The cells of the block -/

/-- The slot base of the block. -/
abbrev oT : ℕ := 130

/-- The register base of the block. -/
abbrev rT : ℕ := 8

/-- The array base of the block. -/
abbrev aT : ℕ := 8

/-- **The stage position in the cells**: `μ̂` in `aT`, `T̂` in `aT + 1` (cells `d i + l`), `D` in `oT`, and `2^{j+1}`
in `oT + 36`. -/
def StAtO (σ : Env d) (j : ℕ) (P : StZ d) : Prop :=
  (∀ l : Fin d, σ.arr aT l = P.mu l) ∧ (∀ i l : Fin d, σ.arr (aT + 1) (d * i + l) = P.T i l) ∧ σ.sc oT = P.D ∧
    σ.sc (oT + 36) = ((2 ^ (j + 1) : ℤ) : ℝ)

/-- A stage position with a positive denominator and entries at most `2^B`. -/
def StBnd (P : StZ d) (B : ℕ) : Prop :=
  0 < P.D ∧ P.D ≤ 2 ^ B ∧ (∀ l, |P.mu l| ≤ 2 ^ B) ∧ ∀ i l, |P.T i l| ≤ 2 ^ B

/-- A representation `a = N_a / D_a`, `r₀ = r_n / r_d` of the input, integers below `2^W`. -/
def P0OK (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (Da : ℤ) (Na : Fin d → ℤ) (rn rd : ℤ) : Prop :=
  0 < Da ∧ Da < 2 ^ wU d n δ r0 R0 a ∧ (∀ i, |Na i| < 2 ^ wU d n δ r0 R0 a) ∧ (∀ i, (Na i : ℚ) / Da = a i) ∧
    0 < rn ∧ rn < 2 ^ wU d n δ r0 R0 a ∧ 0 < rd ∧ rd < 2 ^ wU d n δ r0 R0 a ∧ (rn : ℚ) / rd = r0

/-- The slots of the frame of `TriSpecO`. -/
abbrev TriS (y : ℕ) : Prop := y = sDS ∨ 29 < y

/-- The registers of the frame of `TriSpecO`. -/
abbrev TriN (j : ℕ) : Prop := 8 ≤ j

/-- A predicate on the cells at an input (the constants of the block). -/
abbrev KPred : Type := ∀ d : ℕ, ℕ → ℚ → ℚ → ℚ → (Fin d → ℚ) → Env d → Prop

/-- The work term of an input. -/
abbrev WT (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) : ℕ := wU d n δ r0 R0 a

/-! ## The sub-block contracts -/

/-- **The prologue of TRI**: from `BasO` and `k_δ` in `sKd`, `xpre L` writes the constants `KE`, `1` in `rT`, `m_st`
in `rT + 28` and the first position `(a, r₀ I)` in integers into the stage cells, within `C (W + 1)^k` units; it
reads no coin. -/
def TriPreSpec (xpre : Layout → XCmdO) (KE : KPred) (C k nS nN nA : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (w : WorldO d) (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (ℓa ℓ : ℕ) (σ : Env d),
    InU d n δ r0 R0 → LayOK L d ℓa → RoomO L nS nN nA → BasO n σ → σ.sc sKd = kDel δ →
    C * (WT d n δ r0 R0 a + 1) ^ k ≤ ℓ → C * (WT d n δ r0 R0 a + 1) ^ k < 2 ^ ℓa →
    XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ (xpre L) σ (C * (WT d n δ r0 R0 a + 1) ^ k) (fun σ' =>
      KE d n δ r0 R0 a σ' ∧ σ'.nat rT = 1 ∧ σ'.nat (rT + 28) = triMstQ r0 R0 ∧
      (∃ (Da : ℤ) (Na : Fin d → ℤ) (rn rd : ℤ), P0OK d n δ r0 R0 a Da Na rn rd ∧
        StAtO σ' 0 (tzP0 Da Na rn rd)) ∧
      σ'.draws = σ.draws ∧ FrameA TriS TriN (ATri d) σ σ')

/-- **One stage**: from the constants `KE`, the stage `j < m_st` at the position `P` (entries at most `2^B`) and the
counter `j` in `rT + 27`, `xst L` runs the core of TRI-OGD-O on the next `triLT` coins with the SEP field of the stage
and composes: `StAtO σ' (j + 1) (tzComp P (stSumO .. j P coins) G_c')`, within `C (W + B + 1)^k` units. It keeps
`KE`, the counter, `m_st` in `rT + 28` and `1` in `rT`. -/
def TriStageSpec (xst : Layout → XCmdO) (KE : KPred) (C k nS nN nA : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (w : WorldO d) (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (ℓa ℓ : ℕ) (σ : Env d) (j B : ℕ)
    (P : StZ d),
    InU d n δ r0 R0 → LayOK L d ℓa → RoomO L nS nN nA → KE d n δ r0 R0 a σ → StAtO σ j P → StBnd P B →
    j < triMstQ r0 R0 → σ.nat rT = 1 → σ.nat (rT + 27) = j → σ.nat (rT + 28) = triMstQ r0 R0 →
    C * (WT d n δ r0 R0 a + B + 1) ^ k ≤ ℓ → C * (WT d n δ r0 R0 a + B + 1) ^ k < 2 ^ ℓa →
    XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ (xst L) σ (C * (WT d n δ r0 R0 a + B + 1) ^ k) (fun σ' =>
      KE d n δ r0 R0 a σ' ∧
      StAtO σ' (j + 1) (tzComp P (stSumO w.orc a r0 R0 (ellO d n δ r0 R0) j P fun k => w.cs (σ.draws + k))
        (tGcT d (ellO d n δ r0 R0))) ∧
      σ'.nat rT = 1 ∧ σ'.nat (rT + 27) = j ∧ σ'.nat (rT + 28) = triMstQ r0 R0 ∧
      σ'.draws = σ.draws + triLTQ d (ellO d n δ r0 R0) ∧ FrameA TriS TriN (ATri d) σ σ')

/-- **The output**: from the last stage `P` in the stage cells, `xout L` writes `P` into `sDS`, `aMuS`, `aAS` (the
form of `PosIn`) and `LposO` into `sLp`, within `C (W + B + 1)^k` units; it reads no coin. -/
def TriOutSpec (xout : Layout → XCmdO) (KE : KPred) (C k nS nN nA : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (w : WorldO d) (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (ℓa ℓ : ℕ) (σ : Env d) (B : ℕ)
    (P : StZ d),
    InU d n δ r0 R0 → LayOK L d ℓa → RoomO L nS nN nA → KE d n δ r0 R0 a σ → StAtO σ (triMstQ r0 R0) P →
    StBnd P B → σ.nat rT = 1 → σ.nat (rT + 28) = triMstQ r0 R0 →
    C * (WT d n δ r0 R0 a + B + 1) ^ k ≤ ℓ → C * (WT d n δ r0 R0 a + B + 1) ^ k < 2 ^ ℓa →
    XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ (xout L) σ (C * (WT d n δ r0 R0 a + B + 1) ^ k) (fun σ' =>
      σ'.sc sDS = P.D ∧ (∀ l : Fin d, σ'.arr aMuS l = P.mu l) ∧
      (∀ i l : Fin d, σ'.arr aAS (d * i + l) = P.T i l) ∧ σ'.sc sLp = LposO d n δ r0 R0 ∧
      σ'.draws = σ.draws ∧ FrameA TriS TriN (ATri d) σ σ')

/-- **The magnitudes of the integer stages**: from a representation of the input below `2^W`, every stage
`j ≤ m_st` has a positive denominator and entries at most `2^{C (W + 1)^k}`, on every coins. -/
def TriMagO (C k : ℕ) : Prop :=
  ∀ (d n : ℕ) (orc : (Fin d → ℚ) → ℕ → Bool) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (Da : ℤ) (Na : Fin d → ℤ)
    (rn rd : ℤ) (ω : ℕ → ℕ → Bool) (j : ℕ),
    InU d n δ r0 R0 → P0OK d n δ r0 R0 a Da Na rn rd → j ≤ triMstQ r0 R0 →
    StBnd (tzStageO orc a r0 R0 (ellO d n δ r0 R0) (tzP0 Da Na rn rd) ω j) (C * (WT d n δ r0 R0 a + 1) ^ k)

/-- The constants of the block survive the step of the stage counter. -/
def KCtr (KE : KPred) : Prop :=
  ∀ (d n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (σ : Env d) (v : ℕ), KE d n δ r0 R0 a σ →
    KE d n δ r0 R0 a (σ.setNat (rT + 27) v)

/-! ## The program -/

/-- **TRI-OGD-O on the oracle machine**: the prologue, `for j < m_st` one stage, the output. -/
def xtriO (xpre xst xout : Layout → XCmdO) (L : Layout) : XCmdO :=
  .seq (xpre L) (.seq (xforNO (rT + 27) (rT + 28) rT (xst L)) (xout L))

/-! ## The arithmetic of the constants -/

/-- The constant of the assembly. -/
def triCA (Cp kp Cs ks Co ko Cm : ℕ) : ℕ := (Cp + Cs + Co + 7) * (Cm + 2) ^ (kp + ks + ko + 1)

/-- The exponent of the assembly. -/
def triKA (kp ks ko km : ℕ) : ℕ := (km + 1) * (kp + ks + ko + 1)

theorem lenT_natCast (m : ℕ) : len (m : ℤ) = m.size := by
  simp [len]

/-- The number of stages is below the work term. -/
theorem mst_le_wU {n : ℕ} {δ r0 R0 : ℚ} (a : Fin d → ℚ) (hI : InU d n δ r0 R0) :
    triMstQ r0 R0 ≤ wU d n δ r0 R0 a := by
  have hR : 0 < R0 := lt_of_lt_of_le hI.hr0 hI.hR0
  unfold triMstQ
  refine max_le (by unfold wU; omega) ?_
  have hRn : (0 : ℚ) < R0.num := by exact_mod_cast Rat.num_pos.2 hR
  have hrn1 : (1 : ℚ) ≤ r0.num := by exact_mod_cast Rat.num_pos.2 hI.hr0
  have e1 : (R0.num : ℚ) = R0 * R0.den := (Rat.mul_den_eq_num R0).symm
  have e2 : (r0.num : ℚ) = r0 * r0.den := (Rat.mul_den_eq_num r0).symm
  have hRd : (1 : ℚ) ≤ R0.den := by exact_mod_cast R0.den_pos
  have hq : R0 / r0 ≤ ((R0.num.natAbs * r0.den : ℕ) : ℚ) := by
    have hnat : ((R0.num.natAbs : ℕ) : ℚ) = R0.num := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos hRn]
    push_cast
    rw [hnat, div_le_iff₀ hI.hr0]
    have e3 : (R0.num : ℚ) * r0.den * r0 = R0.num * r0.num := by rw [e2]; ring
    rw [e3]
    have h3 : R0 ≤ (R0.num : ℚ) := by rw [e1]; nlinarith
    have h4 : (R0.num : ℚ) ≤ R0.num * r0.num := by nlinarith
    linarith
  have hS : len R0.num + len (r0.den : ℤ) ≤ sizeN δ r0 R0 a := by unfold sizeN; omega
  apply Nat.clog_le_of_le_pow
  have a1 : R0.num.natAbs < 2 ^ len R0.num := Nat.lt_size_self _
  have a2 : r0.den < 2 ^ len (r0.den : ℤ) := by rw [lenT_natCast]; exact Nat.lt_size_self _
  have hc : ⌈R0 / r0⌉₊ ≤ R0.num.natAbs * r0.den := Nat.ceil_le.2 hq
  calc ⌈R0 / r0⌉₊ ≤ R0.num.natAbs * r0.den := hc
    _ ≤ 2 ^ len R0.num * 2 ^ len (r0.den : ℤ) := Nat.mul_le_mul a1.le a2.le
    _ = 2 ^ (len R0.num + len (r0.den : ℤ)) := (pow_add _ _ _).symm
    _ ≤ 2 ^ wU d n δ r0 R0 a := Nat.pow_le_pow_right (by norm_num) (by unfold wU; omega)

/-- The arithmetic of the assembly: with `V = W + 1`, `B = C_m V^{k_m}` and `m ≤ W`, every bound of a sub-block and
the bound of the output are at most `triCA V^{triKA}`. -/
theorem tri_arith (Cp kp Cs ks Co ko Cm km W mst : ℕ) (hm : mst ≤ W) :
    Cp * (W + 1) ^ kp ≤ triCA Cp kp Cs ks Co ko Cm * (W + 1) ^ triKA kp ks ko km ∧
    Cs * (W + Cm * (W + 1) ^ km + 1) ^ ks ≤ triCA Cp kp Cs ks Co ko Cm * (W + 1) ^ triKA kp ks ko km ∧
    Co * (W + Cm * (W + 1) ^ km + 1) ^ ko ≤ triCA Cp kp Cs ks Co ko Cm * (W + 1) ^ triKA kp ks ko km ∧
    Cm * (W + 1) ^ km + 1 ≤ triCA Cp kp Cs ks Co ko Cm * (W + 1) ^ triKA kp ks ko km ∧
    Cp * (W + 1) ^ kp + (mst * (Cs * (W + Cm * (W + 1) ^ km + 1) ^ ks + 3) + 3 +
      Co * (W + Cm * (W + 1) ^ km + 1) ^ ko) ≤ triCA Cp kp Cs ks Co ko Cm * (W + 1) ^ triKA kp ks ko km := by
  set V := W + 1 with hV
  have hV1 : 1 ≤ V := by omega
  set X := (Cm + 2) * V ^ (km + 1) with hX
  set e := kp + ks + ko + 1 with he
  have hVk : V ^ km ≤ V ^ (km + 1) := Nat.pow_le_pow_right hV1 (by omega)
  have hVV : V ≤ V ^ (km + 1) := by
    calc V = V ^ 1 := (pow_one V).symm
      _ ≤ V ^ (km + 1) := Nat.pow_le_pow_right hV1 (by omega)
  have hX1 : 1 ≤ X := by
    have : 1 ≤ V ^ (km + 1) := Nat.one_le_pow _ _ hV1
    calc 1 ≤ 1 * 1 := le_rfl
      _ ≤ (Cm + 2) * V ^ (km + 1) := Nat.mul_le_mul (by omega) this
  have hVX : V ≤ X := by
    calc V ≤ V ^ (km + 1) := hVV
      _ = 1 * V ^ (km + 1) := (one_mul _).symm
      _ ≤ (Cm + 2) * V ^ (km + 1) := Nat.mul_le_mul_right _ (by omega)
  have hWB : W + Cm * V ^ km + 1 ≤ X := by
    calc W + Cm * V ^ km + 1 = V + Cm * V ^ km := by omega
      _ ≤ V ^ (km + 1) + Cm * V ^ (km + 1) := Nat.add_le_add hVV (Nat.mul_le_mul_left _ hVk)
      _ ≤ (Cm + 2) * V ^ (km + 1) := by nlinarith
  have hpow : ∀ m, m ≤ e → X ^ m ≤ X ^ e := fun m hm => Nat.pow_le_pow_right hX1 hm
  have hXe : X ^ e = (Cm + 2) ^ e * V ^ triKA kp ks ko km := by
    rw [hX, mul_pow, ← pow_mul]
    unfold triKA
    rw [← he]
  have hCA : triCA Cp kp Cs ks Co ko Cm * V ^ triKA kp ks ko km = (Cp + Cs + Co + 7) * X ^ e := by
    unfold triCA; rw [← he, hXe]; ring
  rw [hCA]
  have t1 : V ^ kp ≤ X ^ e := (Nat.pow_le_pow_left hVX kp).trans (hpow kp (by omega))
  have t2 : (W + Cm * V ^ km + 1) ^ ks ≤ X ^ ks := Nat.pow_le_pow_left hWB ks
  have t2' : (W + Cm * V ^ km + 1) ^ ks ≤ X ^ e := t2.trans (hpow ks (by omega))
  have t3 : (W + Cm * V ^ km + 1) ^ ko ≤ X ^ e := (Nat.pow_le_pow_left hWB ko).trans (hpow ko (by omega))
  have t4 : Cm * V ^ km + 1 ≤ X ^ e := by
    calc Cm * V ^ km + 1 ≤ W + Cm * V ^ km + 1 := by omega
      _ ≤ X := hWB
      _ = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ e := hpow 1 (by omega)
  have t5 : mst * (W + Cm * V ^ km + 1) ^ ks ≤ X ^ e := by
    calc mst * (W + Cm * V ^ km + 1) ^ ks ≤ X * X ^ ks := Nat.mul_le_mul (by omega) t2
      _ = X ^ (ks + 1) := by ring
      _ ≤ X ^ e := hpow _ (by omega)
  have t6 : mst ≤ X ^ e := by
    calc mst ≤ X := by omega
      _ = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ e := hpow 1 (by omega)
  have hc : ∀ c, c ≤ Cp + Cs + Co + 7 → ∀ x, x ≤ X ^ e → c * x ≤ (Cp + Cs + Co + 7) * X ^ e :=
    fun c hc x hx => Nat.mul_le_mul hc hx
  refine ⟨hc _ (by omega) _ t1, hc _ (by omega) _ t2', hc _ (by omega) _ t3, ?_, ?_⟩
  · calc Cm * V ^ km + 1 ≤ X ^ e := t4
      _ = 1 * X ^ e := (one_mul _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  · have e5 : Cp * V ^ kp + (mst * (Cs * (W + Cm * V ^ km + 1) ^ ks + 3) + 3 + Co * (W + Cm * V ^ km + 1) ^ ko) =
        Cp * V ^ kp + Cs * (mst * (W + Cm * V ^ km + 1) ^ ks) + 3 * mst + 3 + Co * (W + Cm * V ^ km + 1) ^ ko := by
      ring
    have g4 : (Cp + Cs + Co + 7) * X ^ e = Cp * X ^ e + Cs * X ^ e + Co * X ^ e + 7 * X ^ e := by ring
    rw [e5, g4]
    have g1 : Cp * V ^ kp ≤ Cp * X ^ e := Nat.mul_le_mul_left _ t1
    have g2 : Cs * (mst * (W + Cm * V ^ km + 1) ^ ks) ≤ Cs * X ^ e := Nat.mul_le_mul_left _ t5
    have g3 : Co * (W + Cm * V ^ km + 1) ^ ko ≤ Co * X ^ e := Nat.mul_le_mul_left _ t3
    have hE1 : 1 ≤ X ^ e := Nat.one_le_pow _ _ hX1
    generalize Cp * V ^ kp = u1 at g1 ⊢
    generalize Cs * (mst * (W + Cm * V ^ km + 1) ^ ks) = u2 at g2 ⊢
    generalize Co * (W + Cm * V ^ km + 1) ^ ko = u3 at g3 ⊢
    generalize Cp * X ^ e = v1 at g1 ⊢
    generalize Cs * X ^ e = v2 at g2 ⊢
    generalize Co * X ^ e = v3 at g3 ⊢
    generalize X ^ e = x at t6 hE1 ⊢
    omega

/-! ## The assembly -/

theorem tzStageO_succ (orc : (Fin d → ℚ) → ℕ → Bool) (a : Fin d → ℚ) (r0 R0 : ℚ) (ℓ : ℕ) (P0 : StZ d)
    (ω : ℕ → ℕ → Bool) (j : ℕ) :
    tzStageO orc a r0 R0 ℓ P0 ω (j + 1) =
      tzComp (tzStageO orc a r0 R0 ℓ P0 ω j) (stSumO orc a r0 R0 ℓ j (tzStageO orc a r0 R0 ℓ P0 ω j) (ω j))
        (tGcT d ℓ) := rfl

/-- The stage position survives a change of a register. -/
theorem StAtO.setNat {σ : Env d} {j : ℕ} {P : StZ d} (h : StAtO σ j P) (i v : ℕ) : StAtO (σ.setNat i v) j P := by
  obtain ⟨e1, e2, e3, e4⟩ := h
  exact ⟨fun l => by rw [Env.setNat_arr, e1], fun i l => by rw [Env.setNat_arr, e2], by rw [Env.setNat_sc, e3],
    by rw [Env.setNat_sc, e4]⟩

/-- The coins of stage `t` read from the draws after the stages before it. -/
theorem stage_coinsO (cs : ℕ → Bool) (c0 mst LT t : ℕ) (ht : t < mst) :
    ∀ k < LT, cs (c0 + t * LT + k) = omO mst LT (fun j => cs (c0 + j)) t k := by
  intro k hk
  simp only [omO, triLay, ht, hk, and_self, ↓reduceIte]
  congr 1
  ring

/-- The arithmetic of the assembly at the input. -/
theorem tri_arithU {n : ℕ} {δ r0 R0 : ℚ} (a : Fin d → ℚ) (hI : InU d n δ r0 R0) (Cp kp Cs ks Co ko Cm km : ℕ) :
    Cp * (wU d n δ r0 R0 a + 1) ^ kp ≤ triCA Cp kp Cs ks Co ko Cm * (wU d n δ r0 R0 a + 1) ^ triKA kp ks ko km ∧
    Cs * (wU d n δ r0 R0 a + Cm * (wU d n δ r0 R0 a + 1) ^ km + 1) ^ ks ≤
      triCA Cp kp Cs ks Co ko Cm * (wU d n δ r0 R0 a + 1) ^ triKA kp ks ko km ∧
    Co * (wU d n δ r0 R0 a + Cm * (wU d n δ r0 R0 a + 1) ^ km + 1) ^ ko ≤
      triCA Cp kp Cs ks Co ko Cm * (wU d n δ r0 R0 a + 1) ^ triKA kp ks ko km ∧
    Cm * (wU d n δ r0 R0 a + 1) ^ km + 1 ≤ triCA Cp kp Cs ks Co ko Cm * (wU d n δ r0 R0 a + 1) ^ triKA kp ks ko km ∧
    Cp * (wU d n δ r0 R0 a + 1) ^ kp + (triMstQ r0 R0 *
      (Cs * (wU d n δ r0 R0 a + Cm * (wU d n δ r0 R0 a + 1) ^ km + 1) ^ ks + 3) + 3 +
      Co * (wU d n δ r0 R0 a + Cm * (wU d n δ r0 R0 a + 1) ^ km + 1) ^ ko) ≤
        triCA Cp kp Cs ks Co ko Cm * (wU d n δ r0 R0 a + 1) ^ triKA kp ks ko km ∧
    triMstQ r0 R0 < triCA Cp kp Cs ks Co ko Cm * (wU d n δ r0 R0 a + 1) ^ triKA kp ks ko km := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := tri_arith Cp kp Cs ks Co ko Cm km (wU d n δ r0 R0 a) (triMstQ r0 R0) (mst_le_wU a hI)
  refine ⟨a1, a2, a3, a4, a5, ?_⟩
  have hQ : triMstQ r0 R0 ≤ triMstQ r0 R0 * (Cs * (wU d n δ r0 R0 a + Cm * (wU d n δ r0 R0 a + 1) ^ km + 1) ^ ks + 3) :=
    Nat.le_mul_of_pos_right _ (by omega)
  generalize triMstQ r0 R0 * (Cs * (wU d n δ r0 R0 a + Cm * (wU d n δ r0 R0 a + 1) ^ km + 1) ^ ks + 3) = q at hQ a5
  generalize triCA Cp kp Cs ks Co ko Cm * (wU d n δ r0 R0 a + 1) ^ triKA kp ks ko km = M at a5 ⊢
  omega

set_option maxHeartbeats 4000000 in
/-- **`TriSpecO` from the sub-block contracts**: the prologue, one stage and the output with their constants, the
magnitudes of the integer stages, and the constants kept by the counter step give `TriSpecO` for `xtriO`. -/
theorem triSpecO_of {KE : KPred} {xpre xst xout : Layout → XCmdO} {Cp kp Cs ks Co ko Cm km nS nN nA : ℕ}
    (hp : TriPreSpec xpre KE Cp kp nS nN nA) (hs : TriStageSpec xst KE Cs ks nS nN nA)
    (ho : TriOutSpec xout KE Co ko nS nN nA) (hm : TriMagO Cm km) (hK : KCtr KE) (hN : rT + 29 ≤ nN) :
    TriSpecO (xtriO xpre xst xout) (triCA Cp kp Cs ks Co ko Cm) (triKA kp ks ko km) nS nN nA := by
  intro d L w n δ r0 R0 a ℓa ℓ σ hI hL hR hB hkd hℓ hℓa
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := tri_arithU a hI Cp kp Cs ks Co ko Cm km
  have hNN : rT + 28 < L.NN := lt_of_lt_of_le (by omega) hR.2.1
  have hmst_lt : triMstQ r0 R0 < 2 ^ ℓa := lt_trans a6 hℓa
  refine XVO.mono (XVO.seq (hp d L w n δ r0 R0 a ℓa ℓ σ hI hL hR hB hkd (a1.trans hℓ) (lt_of_le_of_lt a1 hℓa))
    fun σ1 ⟨k1, o1, m1, ⟨Da, Na, rn, rd, hP0, s1⟩, d1, F1⟩ => ?_) a5 fun σ' h => h
  have bP : ∀ t, t ≤ triMstQ r0 R0 → StBnd (tzStageO w.orc a r0 R0 (ellO d n δ r0 R0) (tzP0 Da Na rn rd)
      (omO (triMstQ r0 R0) (triLTQ d (ellO d n δ r0 R0)) fun j => w.cs (σ.draws + j)) t)
      (Cm * (wU d n δ r0 R0 a + 1) ^ km) := fun t ht =>
    hm d n w.orc δ r0 R0 a Da Na rn rd _ t hI hP0 ht
  let J : ℕ → Env d → Prop := fun t σ' =>
    KE d n δ r0 R0 a σ' ∧ StAtO σ' t (tzStageO w.orc a r0 R0 (ellO d n δ r0 R0) (tzP0 Da Na rn rd)
      (omO (triMstQ r0 R0) (triLTQ d (ellO d n δ r0 R0)) fun j => w.cs (σ.draws + j)) t) ∧
      σ'.draws = σ1.draws + t * triLTQ d (ellO d n δ r0 R0) ∧ FrameA TriS TriN (ATri d) σ1 σ'
  have hJ0 : J 0 (σ1.setNat (rT + 27) 0) :=
    ⟨hK _ _ _ _ _ _ _ _ k1, s1.setNat _ _, by rw [Env.setNat_draws]; ring,
      (FrameA.refl _ _ _ σ1).setNat (show TriN (rT + 27) by omega) 0⟩
  have hloop := XVO.forN (L := L) (XO := ctxU w n δ r0 R0 a) (ℓ := ℓ) (i := rT + 27) (n := rT + 28) (one := rT)
    (body := xst L) hL (by omega) hNN (by omega) (by omega) (by omega) (triMstQ r0 R0)
    (Cs * (wU d n δ r0 R0 a + Cm * (wU d n δ r0 R0 a + 1) ^ km + 1) ^ ks) hmst_lt J σ1 m1 o1 hJ0 ?_
  · refine XVO.seq hloop fun σ2 ⟨⟨k2, s2, d2, F2⟩, _, n2, o2⟩ => ?_
    refine XVO.mono (ho d L w n δ r0 R0 a ℓa ℓ σ2 _ _ hI hL hR k2 s2 (bP _ le_rfl) o2 n2 (a3.trans hℓ)
      (lt_of_le_of_lt a3 hℓa)) le_rfl ?_
    rintro σ3 ⟨e1, e2, e3, e4, d3, F3⟩
    obtain ⟨h1, -, -, h4, -, -, h7, -, h9⟩ := hP0
    have hpos := tzPosO_eq hI.hd n w.orc δ r0 R0 a h1 h7 h4 h9 fun j => w.cs (σ.draws + j)
    obtain ⟨b1, b2, b3, b4⟩ := bP _ le_rfl
    have hlt : ∀ x : ℤ, |x| ≤ 2 ^ (Cm * (wU d n δ r0 R0 a + 1) ^ km) →
        |x| < 2 ^ (triCA Cp kp Cs ks Co ko Cm * (wU d n δ r0 R0 a + 1) ^ triKA kp ks ko km) := fun x hx =>
      lt_of_le_of_lt hx (pow_lt_pow_right₀ (by norm_num) (by omega))
    refine ⟨⟨_, b1, lt_of_le_of_lt b2 (pow_lt_pow_right₀ (by norm_num) (by omega)), e1,
      fun l => ⟨_, hlt _ (b3 l), e2 l, ?_⟩, fun i l => ⟨_, hlt _ (b4 i l), e3 i l, ?_⟩⟩, e4, ?_, ?_⟩
    · rw [hpos]; rfl
    · rw [hpos]; rfl
    · rw [d3, d2, d1]; unfold LposO; ring
    · exact (F1.trans F2).trans F3
  · intro t ht σ' ⟨kt, st, dt, Ft⟩ it nt ot
    refine XVO.mono (hs d L w n δ r0 R0 a ℓa ℓ σ' t _ _ hI hL hR kt st (bP t ht.le) ht ot it nt
      (a2.trans hℓ) (lt_of_le_of_lt a2 hℓa)) le_rfl ?_
    rintro σ'' ⟨k'', s'', o'', i'', n'', d'', F''⟩
    have hc : stSumO w.orc a r0 R0 (ellO d n δ r0 R0) t (tzStageO w.orc a r0 R0 (ellO d n δ r0 R0)
        (tzP0 Da Na rn rd) (omO (triMstQ r0 R0) (triLTQ d (ellO d n δ r0 R0)) fun j => w.cs (σ.draws + j)) t)
        (fun k => w.cs (σ'.draws + k)) =
        stSumO w.orc a r0 R0 (ellO d n δ r0 R0) t (tzStageO w.orc a r0 R0 (ellO d n δ r0 R0)
        (tzP0 Da Na rn rd) (omO (triMstQ r0 R0) (triLTQ d (ellO d n δ r0 R0)) fun j => w.cs (σ.draws + j)) t)
        (omO (triMstQ r0 R0) (triLTQ d (ellO d n δ r0 R0)) (fun j => w.cs (σ.draws + j)) t) :=
      stSumO_congr _ _ _ _ _ _ _ _ _ fun k hk => by
        rw [dt, d1]; exact stage_coinsO w.cs σ.draws _ _ t ht k hk
    rw [hc, ← tzStageO_succ] at s''
    exact ⟨i'', n'', o'', hK _ _ _ _ _ _ _ _ k'', s''.setNat _ _, by rw [Env.setNat_draws, d'', dt]; ring,
      (Ft.trans F'').setNat (show TriN (rT + 27) by omega) _⟩

end AdversarialBco.Unified.ProgO.TriO
