/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.UW.ProgMachSplit
public import AdversarialBco.Unified.TailOPar
public import AdversarialBco.Unified.TailOData
public import AdversarialBco.Unified.MagField

@[expose] public section

/-!
# The tail's sub-block contracts at BL-OW's PARAM

BL-O's tail contracts (Unified/TailOSpec.lean) fix PARAM by `cfg.par = parN ne d n`; their proofs read only a list of
facts of it. `ParT ne d n P` is that list: `ê` as at `parN ne d n`, `Λ = d N_e`, `N_e ≥ 1`, `p ≥ 1`, the fields `ε'`,
`η'`, `ρ'`, `κ_c'`, `ν'`, `s'_b`, `R'`, `W'` on the grid `2^{-pF}`, `A_0`, `B_0` on the grid `2^{-p}`, `ε' > 0`,
`R' > 0`. PARAM-W meets it (`parOW_parT`).

* `DTSpecW`, `DLSpecW`, `FireSpecW`: BL-O's contracts for the data of R11 and R14 and for R12's new epoch under
  `ParT ne d n cfg.par`;
* `CallSpecW`: BL-O's call contract at BL-OW's configuration `cfgWW`.
-/

namespace AdversarialBco.UW.ProgW

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Uni
open AdversarialBco.Unified.BLO
open AdversarialBco.Unified.ProgO
open AdversarialBco.Unified.ProgO.TailD (parN_onG_sb parN_onG_R parN_R_pos)
open AdversarialBco.UW.BLOW (parOW cfgWW lf1 n0O ruOW parOW_eps ruOW_nonneg parOW_p parOW_pF parOW_Ne parOW_Lam parOW_R
  parOW_sb parOW_W parOW_eHat)
open AdversarialBco.Bit.BLP (Par Cfg Mode St CallQ init LT Lmu eBL sqrtDn up le_up)
open BitRAM BitRAMO Matrix

variable {d : ℕ}

/-! ## The facts of PARAM that the tail reads -/

/-- **The facts of PARAM that BL-O's tail reads**, at the number of epochs `ne`. -/
structure ParT (ne d n : ℕ) (P : Par) : Prop where
  eHat : P.eHat = (parN ne d n).eHat
  Lam : P.Lam = d * P.Ne
  Ne : 1 ≤ P.Ne
  p1 : 1 ≤ P.p
  eps : OnG P.pF P.eps
  eta : OnG P.pF P.eta
  rho : OnG P.pF P.rho
  kapc : OnG P.pF P.kapc
  nu : OnG P.pF P.nu
  sb : OnG P.pF P.sb
  R : OnG P.pF P.R
  W : OnG P.pF P.W
  A0 : OnG P.p P.A0
  B0 : OnG P.p P.B0
  eps0 : 0 < P.eps
  R0 : 0 < P.R

/-- `L_01 > 0`: `lnQ_q(N_0) + lnErr_q(N_0) ≥ ln N_0 > 0`. -/
theorem lf1_pos (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 < lf1 d n δ := by
  have hne : 2 ≤ n0O d n := by
    unfold n0O NeO
    have h1 : 1 ≤ d ^ 3 := Nat.one_le_pow _ _ hd
    have h2 : 1 ≤ n ^ 4 := Nat.one_le_pow _ _ hn
    have : 2 ≤ 15 * 2 ^ (17 + 0) * d ^ 3 * n ^ 4 := by
      have : 2 ≤ 15 * 2 ^ (17 + 0) := by norm_num
      calc 2 ≤ 15 * 2 ^ (17 + 0) * 1 * 1 := by omega
        _ ≤ 15 * 2 ^ (17 + 0) * d ^ 3 * n ^ 4 := by gcongr
    omega
  have hq : 1 ≤ (parO d n δ).q := by rw [parO_q]; omega
  have hL := Bit.PieceA.lnQ_err (parO d n δ).q (n0O d n) hq (by omega)
  have hlog : 0 < Real.log (n0O d n) := Real.log_pos (by exact_mod_cast (show 1 < n0O d n by omega))
  have h : (0 : ℝ) < ((lf1 d n δ : ℚ) : ℝ) := by
    unfold lf1; push_cast
    linarith [(abs_le.1 hL).1]
  exact_mod_cast h

/-- `ε' > 0` at PARAM-W. -/
theorem parOW_eps_pos (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) : 0 < (parOW d n δ).eps := by
  rw [parOW_eps]
  refine lt_of_lt_of_le ?_ (le_up _ _)
  have h1 : (0 : ℚ) < 36 * lf1 d n δ := by have := lf1_pos d n δ hd hn; linarith
  have hru := ruOW_nonneg d n δ
  have hrn : (1 : ℚ) ≤ sqrtDn (parO d n δ).q n := Unified.MagO.rn_ge d n (kDel δ) hn
  have hrd : (0 : ℚ) ≤ sqrtDn (parO d n δ).q d := by unfold sqrtDn; positivity
  have hq : (0 : ℚ) < 1 / 2 ^ (parO d n δ).q := by positivity
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  refine div_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hd') ?_) (pow_pos h1 5)) ?_) (by linarith)
  · linarith
  · linarith

set_option maxHeartbeats 1000000 in
/-- **PARAM-W meets `ParT`** at `N_e = NeO d n (kDel δ)`. -/
theorem parOW_parT (d n : ℕ) (δ : ℚ) (hd : 1 ≤ d) (hn : 1 ≤ n) : ParT (NeO d n (kDel δ)) d n (parOW d n δ) where
  eHat := by rw [parOW_eHat]; rfl
  Lam := by rw [parOW_Lam, parOW_Ne]; rfl
  Ne := by rw [parOW_Ne]; exact NeO_pos _ hd hn
  p1 := by rw [parOW_p]; show 1 ≤ 10 * (NeO d n (kDel δ)).size + 16 * d.size + 160; omega
  eps := onG_up _ _
  eta := onG_rnd_s _ _
  rho := onG_dn _ _
  kapc := onG_rnd_s _ _
  nu := onG_rnd_s _ _
  sb := by rw [parOW_pF, parOW_sb]; exact parN_onG_sb (NeO d n (kDel δ)) d n
  R := by rw [parOW_pF, parOW_R]; exact parN_onG_R (NeO d n (kDel δ)) d n
  W := by rw [parOW_pF, parOW_W]; exact tlN_onG_W (NeO d n (kDel δ)) d n
  A0 := onG_rnd_s _ _
  B0 := onG_rnd_s _ _
  eps0 := parOW_eps_pos d n δ hd hn
  R0 := by rw [parOW_R]; exact parN_R_pos (NeO d n (kDel δ)) d n hd

/-! ## The sub-block contracts -/

/-- **The data of R11 TEST** under `ParT`: BL-O's contract with `ParT ne d n cfg.par` for `cfg.par = parN ne d n`. -/
def DTSpecW (xdt : Layout → XCmd) (C k : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (X : XCtx d) (ℓa ℓ n m K0 E t ne : ℕ) (cfg : Cfg d) (st : St d)
    (Bp : Matrix (Fin d) (Fin d) ℚ) (bp Gp : Fin d → ℚ) (σ : Env d),
    1 ≤ d → 1 ≤ n → 1 ≤ ne → ParT ne d n cfg.par → LayOK L d ℓa → BLLay L →
    BLInv L n m K0 E cfg (.run st) t σ →
    (∀ i j : Fin d, σ.arr 27 (d * i + j) = qn cfg.par.p (Bp i j) ∧ OnG cfg.par.p (Bp i j) ∧
      |qn cfg.par.p (Bp i j)| ≤ 2 ^ E) →
    (∀ j : Fin d, σ.arr 28 j = qn cfg.par.p (bp j) ∧ OnG cfg.par.p (bp j) ∧ |qn cfg.par.p (bp j)| ≤ 2 ^ E) →
    (∀ j : Fin d, σ.arr 29 j = qn cfg.par.p (Gp j) ∧ OnG cfg.par.p (Gp j) ∧ |qn cfg.par.p (Gp j)| ≤ 2 ^ E) →
    C * (d + E + 1) ^ k ≤ ℓ → C * (d + E + 1) ^ k < 2 ^ ℓa →
    XRunsB L X ℓa ℓ (xdt L) σ (C * (d + E + 1) ^ k) (fun σ' =>
      PrepIn σ' cfg (C * (d + E + 1) ^ k) (if st.first then 0 else st.B * st.Bᵀ) (if st.first then 0 else st.b)
        (if st.first then 0 else LT cfg.par - st.k) (if st.first then 1 - cfg.par.eps else Bit.BLP.rB cfg.par / 2)
        (Bp * Bpᵀ) (bp - (cfg.par.eta / 2) • Gp)
        (if st.first then (1 - cfg.par.eps) ^ 2 / (cfg.par.Ne * d * 8)
          else Bit.BLP.rB cfg.par ^ 2 / (cfg.par.Ne * d * 8)) ∧
      σ'.draws = σ.draws ∧ FrameA SDat NDat ADat σ σ')

/-- **The data of R14 LINE** under `ParT`: BL-O's contract with `ParT ne d n cfg.par`. -/
def DLSpecW (xdl : Layout → XCmd) (C k : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (X : XCtx d) (ℓa ℓ n m K0 E t ne : ℕ) (cfg : Cfg d) (st : St d)
    (Bp : Matrix (Fin d) (Fin d) ℚ) (bp : Fin d → ℚ) (kp : ℚ) (wh : Fin d → ℤ) (Dw : ℤ) (σ : Env d),
    1 ≤ d → 1 ≤ n → 1 ≤ ne → ParT ne d n cfg.par → LayOK L d ℓa → BLLay L →
    BLInv L n m K0 E cfg (.run st) t σ →
    (∀ i j : Fin d, σ.arr 27 (d * i + j) = qn cfg.par.p (Bp i j) ∧ OnG cfg.par.p (Bp i j) ∧
      |qn cfg.par.p (Bp i j)| ≤ 2 ^ E) →
    (∀ j : Fin d, σ.arr 28 j = qn cfg.par.p (bp j) ∧ OnG cfg.par.p (bp j) ∧ |qn cfg.par.p (bp j)| ≤ 2 ^ E) →
    σ.sc 59 = qn cfg.par.p kp → OnG cfg.par.p kp → |qn cfg.par.p kp| ≤ 2 ^ E →
    0 < Dw → Dw ≤ 2 ^ E → σ.sc 91 = Dw → (∀ j : Fin d, σ.arr 31 j = wh j ∧ |wh j| ≤ 2 ^ E) →
    C * (d + E + 1) ^ k ≤ ℓ → C * (d + E + 1) ^ k < 2 ^ ℓa →
    XRunsB L X ℓa ℓ (xdl L) σ (C * (d + E + 1) ^ k) (fun σ' =>
      PrepIn σ' cfg (C * (d + E + 1) ^ k) (Bp * Bpᵀ) bp (Lmu cfg.par - kp) (Bit.BLP.rB cfg.par / 2) (Bp * Bpᵀ)
        ((Bp * Bpᵀ) *ᵥ fun j => (wh j : ℚ) / Dw) (eBL cfg.par d n) ∧
      σ'.draws = σ.draws ∧ FrameA SDat NDat ADat σ σ')

/-- **R12's new epoch** under `ParT`: BL-O's contract with `ParT ne d n cfg.par`. -/
def FireSpecW (xfire : Layout → XCmd) (C k : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (X : XCtx d) (ℓa ℓ n m K0 E t ne : ℕ) (cfg : Cfg d) (st : St d) (σ : Env d),
    1 ≤ d → 1 ≤ n → 1 ≤ ne → ParT ne d n cfg.par → LayOK L d ℓa → BLLay L →
    BLInv L n m K0 E cfg (.run st) t σ →
    C * (d + E + 1) ^ k ≤ ℓ → C * (d + E + 1) ^ k < 2 ^ ℓa →
    XRunsB L X ℓa ℓ (xfire L) σ (C * (d + E + 1) ^ k) (fun σ' =>
      BLInv L n m K0 E cfg (.run (init cfg.par d)) t σ' ∧ σ'.draws = σ.draws ∧ FrameA SEnd NEnd AEnd σ σ')

/-- **One ELL-O call of BL-OW**: BL-O's call contract at BL-OW's configuration `cfgWW`. -/
def CallSpecW (xcall : Layout → XCmdO) (C k nS nN nA : ℕ) : Prop :=
  ∀ (d : ℕ) (L : Layout) (w : WorldO d) (n : ℕ) (δ r0 R0 : ℚ) (a : Fin d → ℚ) (K0 E ℓa ℓ s t : ℕ) (mo : Mode d)
    (H : Matrix (Fin d) (Fin d) ℚ) (g : Fin d → ℚ) (ℓq r : ℚ) (P : Matrix (Fin d) (Fin d) ℚ) (f : Fin d → ℚ) (e : ℚ)
    (σ : Env d),
    InU d n δ r0 R0 → LayOK L d ℓa → RoomO L nS nN nA →
    BLOInv L n K0 E (cfgWW d n δ r0 R0 a w) mo t σ → PrepIn σ (cfgV (cfgWW d n δ r0 R0 a w)) s H g ℓq r P f e →
    C * (wU d n δ r0 R0 a + E + s + 1) ^ k ≤ ℓ → C * (wU d n δ r0 R0 a + E + s + 1) ^ k < 2 ^ ℓa →
    XRunsBO L (ctxU w n δ r0 R0 a) ℓa ℓ (xcall L) σ (C * (wU d n δ r0 R0 a + E + s + 1) ^ k) (fun σ' =>
      EllOut blkBL (apI w.orc (cfgWW d n δ r0 R0 a w) (callO (cfgWW d n δ r0 R0 a w) H g ℓq r P f e))
        (ellExpO (clearO (callO (cfgWW d n δ r0 R0 a w) H g ℓq r P f e))) σ' ∧ σ'.draws = σ.draws ∧
      FrameA SCall NCall ACall σ σ')

/-- The block statements. -/
def DataTW : Prop := ∃ (xdt : Layout → XCmd) (C k : ℕ), DTSpecW xdt C k
def DataLW : Prop := ∃ (xdl : Layout → XCmd) (C k : ℕ), DLSpecW xdl C k
def FireW : Prop := ∃ (xfire : Layout → XCmd) (C k : ℕ), FireSpecW xfire C k
def CallW : Prop := ∃ (xcall : Layout → XCmdO) (C k nS nN nA : ℕ), CallSpecW xcall C k nS nN nA

end AdversarialBco.UW.ProgW
