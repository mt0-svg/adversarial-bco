/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBmInt

@[expose] public section

/-!
# Procedure BM-INT from the coins to `gsSpec` (GS-RUN)

* `XV.noDraws`: a routine with no `coins` leaf keeps the count of draws.
* `xbmint`, `XV.bmint`: the whole procedure, from two blocks of `B` coins to `gsSpec B U W`, within `bmUnits B` units.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach

variable {d : ℕ}

/-! ## The draws

A command with no `coins` leaf leaves the count of draws where it was. -/

/-- A leaf other than `coins`. -/
def Leaf.noCoins : Leaf → Bool
  | .idiv _ _ _ => true
  | .coins _ _ => false
  | .obs _ _ => true
  | .play _ => true
  | .rtoN _ _ => true
  | .nmul _ _ _ => true
  | .rdIn _ _ => true

/-- A primitive other than `coins`. -/
def XPrim.noCoins : XPrim → Bool
  | .frag _ => true
  | .leaf l => l.noCoins

/-- No `coins` leaf in the command. -/
def XCmd.noCoins : XCmd → Bool
  | .skip => true
  | .prim p => p.noCoins
  | .seq c₁ c₂ => c₁.noCoins && c₂.noCoins
  | .ifR _ _ c₁ c₂ => c₁.noCoins && c₂.noCoins
  | .ifN _ _ c₁ c₂ => c₁.noCoins && c₂.noCoins
  | .whileR _ _ c => c.noCoins
  | .whileN _ _ c => c.noCoins

theorem noCoins_toX (c : Cmd) : (toX c).noCoins = true := by
  induction c <;> simp_all [toX, XCmd.noCoins, XPrim.noCoins]

/-- Unfolds the commands of BM-INT and checks that they have no `coins` leaf. -/
macro "nocoins" : tactic =>
  `(tactic| simp [XCmd.noCoins, XPrim.noCoins, Leaf.noCoins, noCoins_toX, xbmPrec, xsize, xbmConst, xbmX, xbmMerc,
    xbmLL, xbmR, xbmJ, xbmCmul, xbmChain, xbmTurn, xbmAngle, xsidiv, xforN, xwhileS, xifS, xisqrt, xisqrtPass,
    xpow2, xrtoN, xnmul])

theorem XExecB.draws_eq {X : XCtx d} {ℓa ℓ : ℕ} {c : XCmd} {s s' : RealRAM.State d} {k : ℕ}
    (h : XExecB X ℓa ℓ c s k s') (hc : c.noCoins = true) : s'.draws = s.draws := by
  induction h with
  | skip => rfl
  | frag p s hok => cases p <;> first | rfl | exact hok.elim
  | leaf l s _ => cases l <;> first | rfl | simp [XCmd.noCoins, XPrim.noCoins, Leaf.noCoins] at hc
  | seq _ _ ih₁ ih₂ =>
    simp only [XCmd.noCoins, Bool.and_eq_true] at hc
    rw [ih₂ hc.2, ih₁ hc.1]
  | ifR_t _ _ _ ih => simp only [XCmd.noCoins, Bool.and_eq_true] at hc; exact ih hc.1
  | ifR_f _ _ _ ih => simp only [XCmd.noCoins, Bool.and_eq_true] at hc; exact ih hc.2
  | ifN_t _ _ _ ih => simp only [XCmd.noCoins, Bool.and_eq_true] at hc; exact ih hc.1
  | ifN_f _ _ _ ih => simp only [XCmd.noCoins, Bool.and_eq_true] at hc; exact ih hc.2
  | whileR_t _ _ _ _ ih₁ ih₂ => rw [ih₂ hc, ih₁ hc]
  | whileR_f => rfl
  | whileN_t _ _ _ _ ih₁ ih₂ => rw [ih₂ hc, ih₁ hc]
  | whileN_f => rfl

/-- A routine with no `coins` leaf keeps the count of draws. -/
theorem XV.noDraws {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {c : XCmd} {σ : Env d} {K : ℕ} {Q : Env d → Prop}
    (h : XRunsB L X ℓa ℓ c σ K Q) (hc : c.noCoins = true) :
    XRunsB L X ℓa ℓ c σ K (fun σ' => Q σ' ∧ σ'.draws = σ.draws) := fun s hs => by
  obtain ⟨k, s', σ', hk, he, hr, hq⟩ := h s hs
  exact ⟨k, s', σ', hk, he, hr, hq, by rw [← hr.draws, ← hs.draws, he.draws_eq hc]⟩

/-! ## Procedure BM-INT -/

/-- Procedure BM-INT on the natural `B` at `on`: the precision and the constants, the coin blocks `U`, `W`, the
logarithm `e` of `U + 1`, `X`, the two Mercator sums, `LL`, `R = ⌊√(2 LL)⌋`, `J = (W + 1) mod 2^B`, the product loop
to `Z`, then `R Z` at `o + 40`, `o + 41`. -/
def xbmint (L : Layout) (o on : ℕ) : XCmd :=
  .seq (xbmPrec on) (.seq (xbmConst L o on) (.seq (xbmLog L o on) (.seq (xbmX L o)
  (.seq (xbmMerc L o on (o + 17) (o + 16)) (.seq (xbmMerc L o on (o + 21) (o + 7)) (.seq (xbmLL L o on)
  (.seq (xbmR L o) (.seq (xbmJ L o) (.seq (xbmAngle L o on)
  (.seq (toX (VL.sop2 L .mul (o + 40) (o + 25) (o + 34))) (toX (VL.sop2 L .mul (o + 41) (o + 25) (o + 35)))))))))))))

/-- The units of cost of `xbmint`. -/
def bmUnits (B : ℕ) : ℕ :=
  4 * Nat.size B + 9 * B + 92 * gsm_prec B + 110 + (B - 1) * (24 * gsm_prec B + 41)

theorem bm_mul_lt {u v : ℤ} {k ℓ : ℕ} (hu : |u| ≤ 2 ^ k) (hv : |v| ≤ 2 ^ k) (hk : 2 * k < ℓ) :
    |u * v| < 2 ^ ℓ := by
  rw [abs_mul]
  calc |u| * |v| ≤ 2 ^ k * 2 ^ k := mul_le_mul hu hv (abs_nonneg _) (pow_nonneg (by norm_num) _)
    _ = 2 ^ (2 * k) := by rw [← pow_add, two_mul]
    _ < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) hk

set_option maxHeartbeats 1000000 in
theorem XV.bmint {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {o on B : ℕ}
    (hS : o + 43 ≤ L.NS) (hN : on + 12 ≤ L.NN) (hB : 1 ≤ B) (hσB : σ.nat on = B)
    (hℓa : 4 * gsm_prec B + 2 < 2 ^ ℓa) (hℓ : 4 * gsm_prec B + 4 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xbmint L o on) σ (bmUnits B) (fun σ' =>
      σ'.sc (o + 40) = ((gsSpec B (BitRAM.readCoins X.wb.cs σ.draws B).toNat
        (BitRAM.readCoins X.wb.cs (σ.draws + B) B).toNat).1 : ℝ) ∧
      σ'.sc (o + 41) = ((gsSpec B (BitRAM.readCoins X.wb.cs σ.draws B).toNat
        (BitRAM.readCoins X.wb.cs (σ.draws + B) B).toNat).2 : ℝ) ∧
      σ'.draws = σ.draws + 2 * B ∧
      FrameP (fun y => o ≤ y ∧ y < o + 43) (fun j => on < j ∧ j < on + 12) σ σ') := by
  obtain ⟨hp4, hpB⟩ := bm_prec B
  have hK : (4 * Nat.size B + 14) + ((4 * B + 24 * gsm_prec B + 16) + ((5 * B + 9) + (3 + ((16 * gsm_prec B + 6) +
      ((16 * gsm_prec B + 6) + (6 + ((36 * gsm_prec B + 33) + (4 + ((8 + ((B - 1) * (24 * gsm_prec B + 38 + 3) + 3))
      + (1 + 1)))))))))) ≤ bmUnits B := by
    have e : 24 * gsm_prec B + 38 + 3 = 24 * gsm_prec B + 41 := by omega
    rw [e]; unfold bmUnits
    generalize (B - 1) * (24 * gsm_prec B + 41) = t
    omega
  refine XV.mono ?_ hK (fun _ h => h)
  refine XV.seq (XV.noDraws (XV.bmPrec hL hN hB hσB hℓa) (by nocoins))
    fun σ1 ⟨⟨h10, h14, h16, h17, h18, h19, h111, hF1⟩, hd1⟩ => ?_
  refine XV.seq (XV.noDraws (XV.bmConst hL (o := o) (by omega) hN h10 h14 h16 h17 h18 h19 h111 hℓa (by omega))
    (by nocoins)) fun σ2 ⟨⟨hC2, hF2⟩, hd2⟩ => ?_
  refine XV.seq (XV.bmLog hL (by omega) hN hC2 hℓa hℓ) fun σ3 ⟨h39, h310, h311, h312, h315, hd3, hF3⟩ => ?_
  have hC3 := hC2.frame hF3 (fun y hy => hy.1) (fun j hj => hj.elim)
  rw [hd2, hd1] at h39 h310 h311 h312 h315 hd3
  obtain ⟨hU0, hUlt⟩ := readCoins_bounds X.wb.cs σ.draws B
  obtain ⟨hW0, hWlt⟩ := readCoins_bounds X.wb.cs (σ.draws + B) B
  set U := BitRAM.readCoins X.wb.cs σ.draws B with hUdef
  set W := BitRAM.readCoins X.wb.cs (σ.draws + B) B with hWdef
  have hUn : ((U.toNat : ℕ) : ℤ) = U := Int.toNat_of_nonneg hU0
  have hWn : ((W.toNat : ℕ) : ℤ) = W := Int.toNat_of_nonneg hW0
  have hUB : U.toNat < 2 ^ B := by
    have : ((U.toNat : ℕ) : ℤ) < ((2 ^ B : ℕ) : ℤ) := by rw [hUn]; push_cast; exact hUlt
    exact_mod_cast this
  have hWB : W.toNat < 2 ^ B := by
    have : ((W.toNat : ℕ) : ℤ) < ((2 ^ B : ℕ) : ℤ) := by rw [hWn]; push_cast; exact hWlt
    exact_mod_cast this
  set e := Nat.log 2 (U.toNat + 1) with he
  have h2e : 2 ^ e ≤ U.toNat + 1 := Nat.pow_log_le_self 2 (by omega)
  have heB : e ≤ B := by
    by_contra hc
    have : 2 ^ B < 2 ^ e := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  refine XV.seq (XV.noDraws (XV.bmX hL (on := on) (by omega) hC3 (Un := U.toNat) (e := e)
    (by rw [h311]; congr 1; omega) (by rw [h312]; norm_cast) h2e (by omega) hℓ) (by nocoins))
    fun σ4 ⟨⟨h416, hF4⟩, hd4⟩ => ?_
  have hC4 := hC3.frame hF4 (fun y hy => by omega) (fun j hj => hj.elim)
  set Xv := (U.toNat + 1 - 2 ^ e) * 2 ^ (2 * gsm_prec B) / (U.toNat + 1) with hXv
  have hXq : Xv ≤ 2 ^ (2 * gsm_prec B) := bm_X_le (U.toNat + 1) e (2 * gsm_prec B) h2e
  refine XV.seq (XV.noDraws (XV.bmMerc hL (S := o + 17) (Xin := o + 16) (by omega) hN hC4 (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) h416 hXq hℓa hℓ) (by nocoins)) fun σ5 ⟨⟨h517, hF5⟩, hd5⟩ => ?_
  have hC5 := hC4.frame hF5 (fun y hy => by omega) (fun j hj => hj)
  have hq1 : 2 ^ (2 * gsm_prec B - 1) ≤ 2 ^ (2 * gsm_prec B) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine XV.seq (XV.noDraws (XV.bmMerc hL (S := o + 21) (Xin := o + 7) (Xv := 2 ^ (2 * gsm_prec B - 1)) (by omega)
    hN hC5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [hC5.sq1, Nat.cast_pow, Nat.cast_ofNat]) hq1 hℓa hℓ) (by nocoins)) fun σ6 ⟨⟨h621, hF6⟩, hd6⟩ => ?_
  have hC6 := hC5.frame hF6 (fun y hy => by omega) (fun j hj => hj)
  set Lam := gsm_mercq (2 * gsm_prec B) (2 ^ (2 * gsm_prec B - 1)) (2 * gsm_prec B) with hLam
  set Sm := gsm_mercq (2 * gsm_prec B) Xv (2 * gsm_prec B) with hSm
  have hLb : Lam ≤ 2 * gsm_prec B * 2 ^ (2 * gsm_prec B) :=
    (bm_mercq_le _ _ _ hq1).trans (Nat.mul_le_mul_left _ hq1)
  have hSb : Sm ≤ 2 * gsm_prec B * 2 ^ (2 * gsm_prec B) :=
    (bm_mercq_le _ _ _ hXq).trans (Nat.mul_le_mul_left _ hXq)
  refine XV.seq (XV.noDraws (XV.bmLL hL (by omega) hN hC6 (e := e) (Lam := Lam) (Sm := Sm)
    (by rw [hF6.2.1 _ (by omega), hF5.2.1 _ (by omega), hF4.2.1 _ (by omega), h315]) heB h621
    (by rw [hF6.2.1 _ (by omega), h517]) hLb hSb hℓa hℓ) (by nocoins)) fun σ7 ⟨⟨h723, hF7⟩, hd7⟩ => ?_
  have hC7 := hC6.frame hF7 (fun y hy => by omega) (fun j hj => hj.elim)
  obtain ⟨hLL0, hLLb⟩ := bm_LLq_bounds B (2 * gsm_prec B) U.toNat hUB (by omega)
  have hLLdef : max (((B : ℤ) - (e : ℕ)) * (Lam : ℕ) - (Sm : ℕ)) 0 = gsm_LLq B (2 * gsm_prec B) U.toNat := rfl
  set LL := (gsm_LLq B (2 * gsm_prec B) U.toNat).toNat with hLLn
  have hLLz : ((LL : ℕ) : ℤ) = gsm_LLq B (2 * gsm_prec B) U.toNat := Int.toNat_of_nonneg hLL0
  have hLL3 : LL ≤ 2 ^ (3 * gsm_prec B) := by
    have h1 : LL ≤ B * (2 * gsm_prec B) * 2 ^ (2 * gsm_prec B) := by
      have : ((LL : ℕ) : ℤ) ≤ ((B * (2 * gsm_prec B) * 2 ^ (2 * gsm_prec B) : ℕ) : ℤ) := by
        rw [hLLz]; push_cast; exact hLLb
      exact_mod_cast this
    have h2 : B * (2 * gsm_prec B) ≤ 2 ^ gsm_prec B := by
      have : B * (2 * gsm_prec B) ≤ 2 * B * (2 * gsm_prec B) := Nat.mul_le_mul_right _ (by omega)
      omega
    calc LL ≤ B * (2 * gsm_prec B) * 2 ^ (2 * gsm_prec B) := h1
      _ ≤ 2 ^ gsm_prec B * 2 ^ (2 * gsm_prec B) := Nat.mul_le_mul_right _ h2
      _ = 2 ^ (3 * gsm_prec B) := by rw [← pow_add]; congr 1; omega
  clear_value LL Sm Lam Xv e
  refine XV.seq (XV.noDraws (XV.bmR hL (on := on) (by omega) hC7 (LL := LL)
    (by rw [h723, hLLdef, ← hLLz]) hLL3 hℓ) (by nocoins)) fun σ8 ⟨⟨h825, hF8⟩, hd8⟩ => ?_
  have hC8 := hC7.frame hF8 (fun y hy => by omega) (fun j hj => hj.elim)
  refine XV.seq (XV.noDraws (XV.bmJ hL (on := on) (by omega) hC8 (Wn := W.toNat)
    (by rw [hF8.2.1 _ (by omega), hF7.2.1 _ (by omega), hF6.2.1 _ (by omega), hF5.2.1 _ (by omega),
      hF4.2.1 _ (by omega), h310, hWn]) hWB hℓ) (by nocoins)) fun σ9 ⟨⟨h929, hF9⟩, hd9⟩ => ?_
  have hC9 := hC8.frame hF9 (fun y hy => by omega) (fun j hj => hj.elim)
  have hJ : (W.toNat + 1) % 2 ^ B < 2 ^ B := Nat.mod_lt _ (by positivity)
  refine XV.seq (XV.noDraws (XV.bmAngle hL hS hN hC9 hB h929 hJ hℓa hℓ) (by nocoins))
    fun σ10 ⟨⟨h1034, h1035, hF10⟩, hd10⟩ => ?_
  set R := Nat.sqrt (2 * LL) with hR
  set Z := gsm_prodq (gsm_prec B) B ((W.toNat + 1) % 2 ^ B) (B - 1) with hZ
  have hR25 : σ10.sc (o + 25) = ((R : ℕ) : ℤ) := by
    rw [hF10.2.1 _ (by omega), hF9.2.1 _ (by omega), h825]
  have hRb : |((R : ℕ) : ℤ)| ≤ 2 ^ (2 * gsm_prec B) := by
    have : R ≤ 2 ^ (2 * gsm_prec B) := bm_sqrt_le _ _ (by
      calc 2 * LL ≤ 2 * 2 ^ (3 * gsm_prec B) := by omega
        _ = 2 ^ (3 * gsm_prec B + 1) := by rw [pow_succ]; ring
        _ ≤ 2 ^ (2 * (2 * gsm_prec B)) := Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast this
  obtain ⟨hZ1, hZ2⟩ := bm_prodq_le (gsm_prec B) B ((W.toNat + 1) % 2 ^ B)
    (fun k => bm_chainq_le (gsm_prec B) k (by omega)) (B - 1)
  have hpp : (2 : ℤ) ^ (gsm_prec B + (B - 1) + 1) ≤ 2 ^ (2 * gsm_prec B) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  refine XV.seq (XV.mulI hL (x := o + 40) (a := o + 25) (b := o + 34) (u := ((R : ℕ) : ℤ)) (v := Z.1) (by omega)
    (by omega) (by omega) hR25 h1034 (lt_of_le_of_lt hRb (pow_lt_pow_right₀ (by norm_num) (by omega)))
    (lt_of_lt_of_le hZ1 (hpp.trans (pow_le_pow_right₀ (by norm_num) (by omega))))
    (bm_mul_lt hRb (hZ1.le.trans hpp) (by omega))) fun σ11 e11 => ?_
  subst e11
  refine XV.mono (XV.mulI hL (x := o + 41) (a := o + 25) (b := o + 35) (u := ((R : ℕ) : ℤ)) (v := Z.2) (by omega)
    (by omega) (by omega) (by slot) (by slot) (lt_of_le_of_lt hRb (pow_lt_pow_right₀ (by norm_num) (by omega)))
    (lt_of_lt_of_le hZ2 (hpp.trans (pow_le_pow_right₀ (by norm_num) (by omega))))
    (bm_mul_lt hRb (hZ2.le.trans hpp) (by omega))) le_rfl fun σ' e' => ?_
  subst e'
  have F : FrameP (fun y => o ≤ y ∧ y < o + 43) (fun j => on < j ∧ j < on + 12) σ σ10 :=
    ((((((((((hF1.mono (fun y hy => hy.elim) (fun j hj => hj)).trans
      (hF2.mono (fun y hy => by omega) (fun j hj => by omega))).trans
      (hF3.mono (fun y hy => by omega) (fun j hj => hj.elim))).trans
      (hF4.mono (fun y hy => by omega) (fun j hj => hj.elim))).trans
      (hF5.mono (fun y hy => by omega) (fun j hj => by omega))).trans
      (hF6.mono (fun y hy => by omega) (fun j hj => by omega))).trans
      (hF7.mono (fun y hy => by omega) (fun j hj => hj.elim))).trans
      (hF8.mono (fun y hy => by omega) (fun j hj => hj.elim))).trans
      (hF9.mono (fun y hy => by omega) (fun j hj => hj.elim))).trans
      (hF10.mono (fun y hy => by omega) (fun j hj => by omega)))
  have hG : gsSpec B U.toNat W.toNat = (((R : ℕ) : ℤ) * Z.1, ((R : ℕ) : ℤ) * Z.2) := by
    simp only [gsSpec, ← hLLn, hR, hZ]
  refine ⟨?_, ?_, ?_, (F.setSc ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _⟩
  · slot
    rw [hG]
  · slot
    rw [hG]
  · show σ10.draws = _
    rw [hd10, hd9, hd8, hd7, hd6, hd5, hd4, hd3]

/-! ## The cost -/

/-- At most `24 p^2` units, `p = gsm_prec B`. -/
theorem bmUnits_le {B : ℕ} (hB : 1 ≤ B) : bmUnits B ≤ 24 * gsm_prec B ^ 2 := by
  have hs : 1 ≤ Nat.size B := Nat.size_pos.2 (by omega)
  have hp : gsm_prec B = B + 2 * Nat.size B + 4 := rfl
  obtain ⟨r, hr⟩ : ∃ r, gsm_prec B = r + 7 := ⟨gsm_prec B - 7, by omega⟩
  have h1 : (B - 1) * (24 * gsm_prec B + 41) ≤ r * (24 * gsm_prec B + 41) := Nat.mul_le_mul_right _ (by omega)
  unfold bmUnits
  rw [hr] at h1 hp ⊢
  have h2 : r * (24 * (r + 7) + 41) = 24 * r ^ 2 + 209 * r := by ring
  have h3 : 24 * (r + 7) ^ 2 = 24 * r ^ 2 + 336 * r + 1176 := by ring
  rw [h2] at h1
  rw [h3]
  generalize (B - 1) * (24 * (r + 7) + 41) = t at h1 ⊢
  generalize r ^ 2 = s at h1 ⊢
  omega

end AdversarialBco.Bit.Transfer
