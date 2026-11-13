/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XStep
public import AdversarialBco.Bit.Transfer.XBmArith

@[expose] public section

/-!
# The pieces of Procedure BM-INT as programs of the extended language (GS-RUN)

The pieces of Procedure BM-INT (the theorem BM-INT and the paper's appendix on Gaussian draws from coins), each with its
rule; the composition is in XBmRun.lean.

* `xsize`: `l = size B` on the naturals, by doubling (`XV.size`);
* `xbmPrec`: `p = B + 2 l + 4`, `q = 2 p`, `p - 1`, `q - 1`, `B - 1` on the naturals (`XV.bmPrec`);
* `xbmConst`: `0, 1, 2, 4, 2^p, 2^q, 2^(p-1), 2^(q-1), 2^B` on the scalars (`XV.bmConst`, the invariant `BmC`);
* `xbmLog`: the coin blocks `U`, `W`, `N = U + 1`, `e = log₂ N` and `2^e`, by doubling (`XV.bmLog`);
* `xbmX`: `X = (N - 2^e) 2^q / N` (`XV.bmX`);
* `xbmMerc`: the fixed-point Mercator sum `gsm_mercq q X q` (`XV.bmMerc`);
* `xbmLL`: `LL = max ((B - e) Λ - S) 0` (`XV.bmLL`);
* `xbmR`: `R = ⌊√(2 LL)⌋` (`XV.bmR`);
* `xbmJ`: `J = (W + 1) mod 2^B` (`XV.bmJ`);
* `xbmCmul`, `xbmChain`, `xbmTurn`, `xbmAngle`: the rounded complex product, the half-angle chain, one turn of
  the product loop and the loop, to `gsm_prodq p B J (B - 1)` (`XV.bmCmul`, `XV.bmChain`, `XV.bmTurn`,
  `XV.bmAngle`).
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach

variable {d : ℕ}

/-! ## `l = size B` -/

/-- `l := 0`, `w := 1`, `one := 1`, `B1 := B + one`; while `w < B1`: `w := w + w`, `l := l + one`. -/
def xsize (nl nw nB nB1 none : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst nl 0)))
  (.seq (.prim (.frag (.nconst nw 1)))
  (.seq (.prim (.frag (.nconst none 1)))
  (.seq (.prim (.frag (.nadd nB1 nB none)))
  (.whileN nw nB1 (.seq (.prim (.frag (.nadd nw nw nw))) (.prim (.frag (.nadd nl nl none))))))))

theorem nat_setNat_ne {σ : Env d} {i j : ℕ} (v : ℕ) (h : j ≠ i) : (σ.setNat i v).nat j = σ.nat j := by simp [h]

theorem nat_setNat_eq (σ : Env d) (i v : ℕ) : (σ.setNat i v).nat i = v := by simp

theorem sc_setSc_ne {σ : Env d} {x y : ℕ} (v : ℝ) (h : y ≠ x) : (σ.setSc x v).sc y = σ.sc y := by simp [h]

theorem sc_setSc_eq (σ : Env d) (x : ℕ) (v : ℝ) : (σ.setSc x v).sc x = v := by simp

/-- Reads a slot of an environment built by `setNat` and `setSc`, the disequalities of indices by `omega`. -/
macro "slot" : tactic =>
  `(tactic| ((try simp (disch := omega) only [nat_setNat_ne, nat_setNat_eq, sc_setSc_ne, sc_setSc_eq,
    Env.setNat_sc, Env.setSc_nat]) <;> try (first | assumption | omega | with_reducible rfl)))

theorem XV.size {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {nl nw nB nB1 none : ℕ}
    (hl : nl < L.NN) (hw : nw < L.NN) (hB : nB < L.NN) (hB1 : nB1 < L.NN) (ho : none < L.NN)
    (hne : [nl, nw, nB, nB1, none].Nodup) {B : ℕ} (hσB : σ.nat nB = B) (hBa : 2 * B + 2 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xsize nl nw nB nB1 none) σ (4 * Nat.size B + 6)
      (fun σ' => σ'.nat nl = Nat.size B ∧ σ'.nat none = 1 ∧
        FrameP (fun _ => False) (fun j => j = nl ∨ j = nw ∨ j = nB1 ∨ j = none) σ σ') := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil, and_true] at hne
  obtain ⟨⟨lw, lB, lB1, lo⟩, ⟨wB, wB1, wo⟩, ⟨BB1, Bo⟩, B1o⟩ := hne
  have h2 : 2 < 2 ^ ℓa := by omega
  refine XV.mono (K := 1 + (1 + (1 + (1 + ((Nat.size B - 0) * (2 + 2) + 2))))) ?_ (by omega) (fun _ h => h)
  refine XV.seq (XV.nconst hL hl 0 (by omega)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.nconst hL hw 1 (by omega)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.nconst hL ho 1 (by omega)) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.nadd hL hB1 hB ho (by slot) (by slot)) fun σ4 e4 => ?_
  subst e4
  refine XV.mono (XV.whileN (X := X) (ℓ := ℓ) hL hw hB1
    (fun t σ' => σ'.nat nw = 2 ^ t ∧ σ'.nat nl = t ∧ σ'.nat nB1 = B + 1 ∧ σ'.nat none = 1 ∧
      (t = 0 ∨ 2 ^ (t - 1) ≤ B) ∧ FrameP (fun _ => False) (fun j => j = nl ∨ j = nw ∨ j = nB1 ∨ j = none) σ σ')
    (Nat.size B) 2
    (fun t σ' ⟨h1, _, h3, _, h5, _⟩ => by
      have : 2 ^ t ≤ 2 * B + 1 := by
        rcases h5 with rfl | h5
        · simp
        · cases t with
          | zero => simp
          | succ s => rw [pow_succ]; simp only [Nat.add_sub_cancel] at h5; omega
      exact ⟨by rw [h1]; omega, by rw [h3]; omega⟩)
    (fun t σ' ⟨h1, _, h3, _, _, _⟩ hc => by
      rw [h1, h3] at hc
      exact Nat.lt_size.2 (by omega))
    (fun t σ' ⟨h1, h2', h3, h4, h5, hF⟩ hc => by
      rw [h1, h3] at hc
      have ht : t < 2 ^ t := Nat.lt_two_pow_self
      refine XV.seq (K₂ := 1) (XV.nadd hL hw hw hw (by rw [h1]; omega) (by rw [h1]; omega)) fun σ5 e5 => ?_
      subst e5
      refine XV.mono (XV.nadd hL hl hl ho (by slot) (by slot)) le_rfl (fun σ6 e6 => ?_)
      subst e6
      refine ⟨by slot, by slot, by slot, by slot,
        Or.inr (by simp; omega),
        (hF.setNat (Or.inr (Or.inl rfl)) _).setNat (Or.inl rfl) _⟩)
    0 _ ⟨by slot, by slot, by slot, by slot, Or.inl rfl,
      ((((FrameP.refl _ _ σ).setNat (Or.inl rfl) _).setNat (Or.inr (Or.inl rfl)) _).setNat
        (Or.inr (Or.inr (Or.inr rfl))) _).setNat (Or.inr (Or.inr (Or.inl rfl))) _⟩) le_rfl
    (fun σ' ⟨t, ⟨h1', h2', h3, h4, h5, hF⟩, hx⟩ => ?_)
  rw [h3] at hx
  exact ⟨by rw [h2', bm_size_eq B t h5 (by rw [h1'] at hx; omega)], h4, hF⟩


/-! ## The setup: the precision and the constants

The slots of BM-INT sit at the scalar base `o` and the natural base `on`. Naturals: `on` holds `B`, `on + 1` to
`on + 3` serve `xsize`, `on + 4` holds `1`, `on + 5` holds `4`, `on + 6, ..., on + 9` hold `p, q, p - 1, q - 1`,
`on + 10` is the loop counter, `on + 11` holds `B - 1`. Scalars `o, ..., o + 8` hold `0, 1, 2, 4, 2^p, 2^q, 2^(p-1),
2^(q-1), 2^B`. -/

/-- `l = size B`, then `p = B + 2 l + 4`, `q = 2 p`, `p - 1`, `q - 1`, `B - 1` on the naturals. -/
def xbmPrec (on : ℕ) : XCmd :=
  .seq (xsize (on + 1) (on + 2) on (on + 3) (on + 4))
  (.seq (.prim (.frag (.nconst (on + 5) 4)))
  (.seq (.prim (.frag (.nadd (on + 6) on (on + 1))))
  (.seq (.prim (.frag (.nadd (on + 6) (on + 6) (on + 1))))
  (.seq (.prim (.frag (.nadd (on + 6) (on + 6) (on + 5))))
  (.seq (.prim (.frag (.nadd (on + 7) (on + 6) (on + 6))))
  (.seq (.prim (.frag (.nsub (on + 8) (on + 6) (on + 4))))
  (.seq (.prim (.frag (.nsub (on + 9) (on + 7) (on + 4))))
  (.prim (.frag (.nsub (on + 11) on (on + 4)))))))))))

theorem XV.bmPrec {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {on : ℕ}
    (hN : on + 12 ≤ L.NN) {B : ℕ} (hB : 1 ≤ B) (hσB : σ.nat on = B) (hℓa : 4 * gsm_prec B + 2 < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xbmPrec on) σ (4 * Nat.size B + 14)
      (fun σ' => σ'.nat on = B ∧ σ'.nat (on + 4) = 1 ∧ σ'.nat (on + 6) = gsm_prec B ∧
        σ'.nat (on + 7) = 2 * gsm_prec B ∧ σ'.nat (on + 8) = gsm_prec B - 1 ∧
        σ'.nat (on + 9) = 2 * gsm_prec B - 1 ∧ σ'.nat (on + 11) = B - 1 ∧
        FrameP (fun _ => False) (fun j => on < j ∧ j < on + 12) σ σ') := by
  have hpd : gsm_prec B = B + 2 * Nat.size B + 4 := rfl
  have hlB : Nat.size B ≤ B := Nat.size_le.2 Nat.lt_two_pow_self
  have hBa : 2 * B + 2 < 2 ^ ℓa := by omega
  refine XV.mono (K := (4 * Nat.size B + 6) + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))))
    ?_ (by omega) (fun _ h => h)
  refine XV.seq (XV.size hL (by omega) (by omega) (by omega) (by omega) (by omega) (by simp) hσB hBa)
    fun σ1 ⟨hl1, ho1, hF1⟩ => ?_
  have hB1 : σ1.nat on = B := by rw [hF1.1 on (by omega), hσB]
  refine XV.seq (XV.nconst hL (i := on + 5) (by omega) 4 (by omega)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.nadd hL (i := on + 6) (a := on) (b := on + 1) (by omega) (by omega) (by omega) (by slot)
    (by slot)) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.nadd hL (i := on + 6) (a := on + 6) (b := on + 1) (by omega) (by omega) (by omega) (by slot)
    (by slot)) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.nadd hL (i := on + 6) (a := on + 6) (b := on + 5) (by omega) (by omega) (by omega) (by slot)
    (by slot)) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.nadd hL (i := on + 7) (a := on + 6) (b := on + 6) (by omega) (by omega) (by omega) (by slot)
    (by slot)) fun σ6 e6 => ?_
  subst e6
  refine XV.seq (XV.nsub hL (i := on + 8) (a := on + 6) (b := on + 4) (by omega) (by omega) (by omega) (by slot)
    (by slot) (by slot)) fun σ7 e7 => ?_
  subst e7
  refine XV.seq (XV.nsub hL (i := on + 9) (a := on + 7) (b := on + 4) (by omega) (by omega) (by omega) (by slot)
    (by slot) (by slot)) fun σ8 e8 => ?_
  subst e8
  refine XV.mono (XV.nsub hL (i := on + 11) (a := on) (b := on + 4) (by omega) (by omega) (by omega) (by slot)
    (by slot) (by slot)) le_rfl fun σ9 e9 => ?_
  subst e9
  have hF := hF1.mono (S' := fun _ => False) (N' := fun j => on < j ∧ j < on + 12) (fun _ h => h)
    (fun j h => by omega)
  refine ⟨by slot, by slot, by slot, by slot, by slot, by slot, by slot, ?_⟩
  exact (((((((hF.setNat ⟨by omega, by omega⟩ _).setNat ⟨by omega, by omega⟩ _).setNat ⟨by omega, by omega⟩ _).setNat
    ⟨by omega, by omega⟩ _).setNat ⟨by omega, by omega⟩ _).setNat ⟨by omega, by omega⟩ _).setNat
    ⟨by omega, by omega⟩ _).setNat ⟨by omega, by omega⟩ _

/-- The rule of `xpow2` with the value as an integer and the frame as predicates. -/
theorem XV.pow2P {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {p i n one : ℕ}
    (hp : p < L.NS) (hi : i < L.NN) (hn : n < L.NN) (ho : one < L.NN) (hin : i ≠ n) (hio : i ≠ one)
    {W : ℕ} (hW : σ.nat n = W) (h1 : σ.nat one = 1) (hWa : W < 2 ^ ℓa) (hWl : W < ℓ) :
    XRunsB L X ℓa ℓ (xpow2 L p i n one) σ (4 * W + 4)
      (fun σ' => σ'.sc p = ((2 ^ W : ℤ) : ℝ) ∧ FrameP (fun y => y = p) (fun j => j = i) σ σ') :=
  XV.mono (XV.pow2 hL hp hi hn ho hin hio hW h1 hWa hWl) le_rfl fun _ ⟨h1, _, hF⟩ =>
    ⟨by rw [h1]; push_cast; ring, FrameP.of_frame (S := fun y => y = p) (N := fun j => j = i) hF (by simp)
      (by simp)⟩

/-- The constants of BM-INT after its setup. -/
structure BmC (o on B : ℕ) (σ : Env d) : Prop where
  nB : σ.nat on = B
  n1 : σ.nat (on + 4) = 1
  np : σ.nat (on + 6) = gsm_prec B
  nq : σ.nat (on + 7) = 2 * gsm_prec B
  nBm : σ.nat (on + 11) = B - 1
  s0 : σ.sc o = ((0 : ℤ) : ℝ)
  s1 : σ.sc (o + 1) = ((1 : ℤ) : ℝ)
  s2 : σ.sc (o + 2) = ((2 : ℤ) : ℝ)
  s4 : σ.sc (o + 3) = ((4 : ℤ) : ℝ)
  sp : σ.sc (o + 4) = ((2 ^ gsm_prec B : ℤ) : ℝ)
  sq : σ.sc (o + 5) = ((2 ^ (2 * gsm_prec B) : ℤ) : ℝ)
  sp1 : σ.sc (o + 6) = ((2 ^ (gsm_prec B - 1) : ℤ) : ℝ)
  sq1 : σ.sc (o + 7) = ((2 ^ (2 * gsm_prec B - 1) : ℤ) : ℝ)
  sB : σ.sc (o + 8) = ((2 ^ B : ℤ) : ℝ)

theorem BmC.frame {o on B : ℕ} {σ σ' : Env d} {S N : ℕ → Prop} (h : BmC o on B σ) (hF : FrameP S N σ σ')
    (hS : ∀ y, S y → o + 9 ≤ y) (hN : ∀ j, N j → j = on + 10) : BmC o on B σ' := by
  have hs : ∀ y, y < o + 9 → σ'.sc y = σ.sc y := fun y hy => hF.2.1 y (fun h' => by have := hS y h'; omega)
  have hn : ∀ j, j ≠ on + 10 → σ'.nat j = σ.nat j := fun j hj => hF.1 j (fun h' => hj (hN j h'))
  exact ⟨by rw [hn _ (by omega), h.nB], by rw [hn _ (by omega), h.n1], by rw [hn _ (by omega), h.np],
    by rw [hn _ (by omega), h.nq], by rw [hn _ (by omega), h.nBm], by rw [hs _ (by omega), h.s0],
    by rw [hs _ (by omega), h.s1], by rw [hs _ (by omega), h.s2], by rw [hs _ (by omega), h.s4],
    by rw [hs _ (by omega), h.sp], by rw [hs _ (by omega), h.sq], by rw [hs _ (by omega), h.sp1],
    by rw [hs _ (by omega), h.sq1], by rw [hs _ (by omega), h.sB]⟩

/-- `0, 1, 2, 4`, then `2^p, 2^q, 2^(p-1), 2^(q-1), 2^B` on the scalars. -/
def xbmConst (L : Layout) (o on : ℕ) : XCmd :=
  .seq (toX (VL.sconst L o ((0 : ℤ) : ℚ)))
  (.seq (toX (VL.sconst L (o + 1) ((1 : ℤ) : ℚ)))
  (.seq (toX (VL.sconst L (o + 2) ((2 : ℤ) : ℚ)))
  (.seq (toX (VL.sconst L (o + 3) ((4 : ℤ) : ℚ)))
  (.seq (xpow2 L (o + 4) (on + 10) (on + 6) (on + 4))
  (.seq (xpow2 L (o + 5) (on + 10) (on + 7) (on + 4))
  (.seq (xpow2 L (o + 6) (on + 10) (on + 8) (on + 4))
  (.seq (xpow2 L (o + 7) (on + 10) (on + 9) (on + 4))
  (xpow2 L (o + 8) (on + 10) on (on + 4)))))))))

theorem XV.bmConst {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {o on : ℕ}
    (hS : o + 9 ≤ L.NS) (hN : on + 12 ≤ L.NN) {B : ℕ} (h0 : σ.nat on = B) (h1 : σ.nat (on + 4) = 1)
    (h2 : σ.nat (on + 6) = gsm_prec B) (h3 : σ.nat (on + 7) = 2 * gsm_prec B)
    (h4 : σ.nat (on + 8) = gsm_prec B - 1) (h5 : σ.nat (on + 9) = 2 * gsm_prec B - 1)
    (h6 : σ.nat (on + 11) = B - 1) (hℓa : 4 * gsm_prec B + 2 < 2 ^ ℓa) (hℓ : 2 * gsm_prec B < ℓ) :
    XRunsB L X ℓa ℓ (xbmConst L o on) σ (4 * B + 24 * gsm_prec B + 16)
      (fun σ' => BmC o on B σ' ∧ FrameP (fun y => o ≤ y ∧ y < o + 9) (fun j => j = on + 10) σ σ') := by
  obtain ⟨hp4, -⟩ := bm_prec B
  set p := gsm_prec B with hpdef
  have h4l : (4 : ℤ) < 2 ^ ℓ := by
    have : (2 : ℤ) ^ 2 < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) (by omega)
    norm_num at this; exact this
  have hc : ∀ c : ℤ, 0 ≤ c → c ≤ 4 → |c| < 2 ^ ℓ := fun c h0 h4 => by rw [abs_of_nonneg h0]; omega
  refine XV.mono (K := 1 + (1 + (1 + (1 + ((4 * p + 4) + ((4 * (2 * p) + 4) + ((4 * (p - 1) + 4) +
    ((4 * (2 * p - 1) + 4) + (4 * B + 4))))))))) ?_ (by omega) (fun _ h => h)
  refine XV.seq (XV.constI hL (x := o) (by omega) 0 (hc 0 le_rfl (by norm_num))) fun σ1 e1 => ?_
  refine XV.seq (XV.constI hL (x := o + 1) (by omega) 1 (hc 1 (by norm_num) (by norm_num))) fun σ2 e2 => ?_
  refine XV.seq (XV.constI hL (x := o + 2) (by omega) 2 (hc 2 (by norm_num) (by norm_num))) fun σ3 e3 => ?_
  refine XV.seq (XV.constI hL (x := o + 3) (by omega) 4 (hc 4 (by norm_num) (by norm_num))) fun σ4 e4 => ?_
  have F4 : FrameP (fun y => o ≤ y ∧ y < o + 9) (fun j => j = on + 10) σ σ4 := by
    rw [e4, e3, e2, e1]
    exact ((((FrameP.refl _ _ σ).setSc ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _).setSc
      ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _
  have n4 : ∀ j, σ4.nat j = σ.nat j := fun j => by rw [e4, e3, e2, e1]; rfl
  refine XV.seq (XV.pow2P hL (p := o + 4) (i := on + 10) (n := on + 6) (one := on + 4) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (W := p) (by rw [n4, h2]) (by rw [n4, h1]) (by omega) (by omega))
    fun σ5 ⟨g5, f5⟩ => ?_
  refine XV.seq (XV.pow2P hL (p := o + 5) (i := on + 10) (n := on + 7) (one := on + 4) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (W := 2 * p) (by rw [f5.1 _ (by omega), n4, h3])
    (by rw [f5.1 _ (by omega), n4, h1]) (by omega) (by omega)) fun σ6 ⟨g6, f6⟩ => ?_
  refine XV.seq (XV.pow2P hL (p := o + 6) (i := on + 10) (n := on + 8) (one := on + 4) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (W := p - 1) (by rw [f6.1 _ (by omega), f5.1 _ (by omega), n4, h4])
    (by rw [f6.1 _ (by omega), f5.1 _ (by omega), n4, h1]) (by omega) (by omega)) fun σ7 ⟨g7, f7⟩ => ?_
  refine XV.seq (XV.pow2P hL (p := o + 7) (i := on + 10) (n := on + 9) (one := on + 4) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (W := 2 * p - 1)
    (by rw [f7.1 _ (by omega), f6.1 _ (by omega), f5.1 _ (by omega), n4, h5])
    (by rw [f7.1 _ (by omega), f6.1 _ (by omega), f5.1 _ (by omega), n4, h1]) (by omega) (by omega))
    fun σ8 ⟨g8, f8⟩ => ?_
  refine XV.mono (XV.pow2P hL (p := o + 8) (i := on + 10) (n := on) (one := on + 4) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (W := B)
    (by rw [f8.1 _ (by omega), f7.1 _ (by omega), f6.1 _ (by omega), f5.1 _ (by omega), n4, h0])
    (by rw [f8.1 _ (by omega), f7.1 _ (by omega), f6.1 _ (by omega), f5.1 _ (by omega), n4, h1]) (by omega)
    (by omega)) le_rfl fun σ9 ⟨g9, f9⟩ => ?_
  have mS : ∀ k, k < 9 → ∀ y, y = o + k → o ≤ y ∧ y < o + 9 := fun k hk y h => ⟨by omega, by omega⟩
  have F := ((((F4.trans (f5.mono (mS 4 (by omega)) (fun _ h => h))).trans (f6.mono (mS 5 (by omega))
    (fun _ h => h))).trans (f7.mono (mS 6 (by omega)) (fun _ h => h))).trans (f8.mono (mS 7 (by omega))
    (fun _ h => h))).trans (f9.mono (mS 8 (by omega)) (fun _ h => h))
  have hn : ∀ j, j ≠ on + 10 → σ9.nat j = σ.nat j := fun j hj => F.1 j hj
  have s4 : ∀ y, y < o + 4 → σ9.sc y = σ4.sc y := fun y hy => by
    rw [f9.2.1 _ (by omega), f8.2.1 _ (by omega), f7.2.1 _ (by omega), f6.2.1 _ (by omega), f5.2.1 _ (by omega)]
  refine ⟨⟨by rw [hn _ (by omega), h0], by rw [hn _ (by omega), h1], by rw [hn _ (by omega), h2],
    by rw [hn _ (by omega), h3], by rw [hn _ (by omega), h6], by rw [s4 _ (by omega), e4, e3, e2, e1]; slot,
    by rw [s4 _ (by omega), e4, e3, e2]; slot, by rw [s4 _ (by omega), e4, e3]; slot,
    by rw [s4 _ (by omega), e4]; slot,
    by rw [f9.2.1 _ (by omega), f8.2.1 _ (by omega), f7.2.1 _ (by omega), f6.2.1 _ (by omega), g5],
    by rw [f9.2.1 _ (by omega), f8.2.1 _ (by omega), f7.2.1 _ (by omega), g6],
    by rw [f9.2.1 _ (by omega), f8.2.1 _ (by omega), g7], by rw [f9.2.1 _ (by omega), g8], g9⟩, F⟩


/-- Nonnegativity of the integer values of BM-INT (casts of naturals, powers of two, their products, sums and
quotients), without unfolding the precision. -/
syntax "nn" : tactic
macro_rules
  | `(tactic| nn) => `(tactic| first
      | exact Nat.cast_nonneg _
      | exact pow_nonneg (by norm_num) _
      | exact le_refl _
      | (apply mul_nonneg <;> nn)
      | (apply add_nonneg <;> nn)
      | (apply Int.ediv_nonneg <;> nn)
      | norm_num)

theorem absI_lt {z : ℤ} {k ℓ : ℕ} (h0 : 0 ≤ z) (h : z ≤ 2 ^ k) (hk : k < ℓ) : |z| < 2 ^ ℓ := by
  rw [abs_of_nonneg h0]; exact lt_of_le_of_lt h (pow_lt_pow_right₀ (by norm_num) hk)

/-! ## The coins and the logarithm -/

/-- `U`, `W` from two blocks of `B` coins at `o + 9`, `o + 10`; `N = U + 1` at `o + 11`, `N + 1` at `o + 14`; then
`2^e` at `o + 12`, `2^(e+1)` at `o + 13` and `e` at `o + 15` by doubling while `2^(e+1) ≤ N`. -/
def xbmLog (L : Layout) (o on : ℕ) : XCmd :=
  .seq (xcoins L (o + 9) on)
  (.seq (xcoins L (o + 10) on)
  (.seq (toX (VL.sop2 L .add (o + 11) (o + 9) (o + 1)))
  (.seq (toX (VL.sop2 L .add (o + 14) (o + 11) (o + 1)))
  (.seq (toX (VL.sop2 L .add (o + 12) (o + 1) o))
  (.seq (toX (VL.sop2 L .add (o + 13) (o + 2) o))
  (.seq (toX (VL.sop2 L .add (o + 15) o o))
  (xwhileS L (o + 13) (o + 14)
    (.seq (toX (VL.sop2 L .add (o + 12) (o + 13) o))
    (.seq (toX (VL.sop2 L .add (o + 13) (o + 13) (o + 13)))
    (toX (VL.sop2 L .add (o + 15) (o + 15) (o + 1))))))))))))

theorem XV.bmLog {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {o on B : ℕ}
    (hS : o + 16 ≤ L.NS) (hN : on + 12 ≤ L.NN) (hC : BmC o on B σ)
    (hℓa : 4 * gsm_prec B + 2 < 2 ^ ℓa) (hℓ : 4 * gsm_prec B + 4 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xbmLog L o on) σ (5 * B + 9) (fun σ' =>
      σ'.sc (o + 9) = (BitRAM.readCoins X.wb.cs σ.draws B : ℝ) ∧
      σ'.sc (o + 10) = (BitRAM.readCoins X.wb.cs (σ.draws + B) B : ℝ) ∧
      σ'.sc (o + 11) = ((BitRAM.readCoins X.wb.cs σ.draws B + 1 : ℤ) : ℝ) ∧
      σ'.sc (o + 12) = ((2 ^ Nat.log 2 ((BitRAM.readCoins X.wb.cs σ.draws B).toNat + 1) : ℤ) : ℝ) ∧
      σ'.sc (o + 15) = ((Nat.log 2 ((BitRAM.readCoins X.wb.cs σ.draws B).toNat + 1) : ℕ) : ℤ) ∧
      σ'.draws = σ.draws + 2 * B ∧
      FrameP (fun y => o + 9 ≤ y ∧ y < o + 16) (fun _ => False) σ σ') := by
  obtain ⟨hp4, -⟩ := bm_prec B
  obtain ⟨hU0, hU1⟩ := readCoins_bounds X.wb.cs σ.draws B
  set U := BitRAM.readCoins X.wb.cs σ.draws B with hU
  set Un := U.toNat with hUndef
  have hUn : (Un : ℤ) = U := Int.toNat_of_nonneg hU0
  have hUnB : Un + 1 ≤ 2 ^ B := by
    have : (Un : ℤ) + 1 ≤ 2 ^ B := by rw [hUn]; omega
    exact_mod_cast this
  have bB : ∀ z : ℤ, 0 ≤ z → z ≤ 2 ^ (B + 1) → |z| < 2 ^ ℓ := fun z h0 h1 => absI_lt h0 h1 (by omega)
  have h2B : (2 : ℤ) ^ (B + 1) = 2 * 2 ^ B := by ring
  have hpB : (1 : ℤ) ≤ 2 ^ B := one_le_pow₀ (by norm_num)
  refine XV.mono (K := 1 + (1 + (1 + (1 + (1 + (1 + (1 + ((B - 0) * (3 + 2) + 2)))))))) ?_ (by omega)
    (fun _ h => h)
  refine XV.seq (XV.coins hL (x := o + 9) (i := on) (by omega) (by omega) (by rw [hC.nB]; omega)
    (by rw [hC.nB]; omega)) fun σ1 e1 => ?_
  rw [hC.nB] at e1
  subst e1
  refine XV.seq (XV.coins hL (x := o + 10) (i := on) (by omega) (by omega) (by simp [hC.nB]; omega)
    (by simp [hC.nB]; omega)) fun σ2 e2 => ?_
  simp only at e2
  subst e2
  refine XV.seq (XV.addI hL (x := o + 11) (a := o + 9) (b := o + 1) (u := U) (v := 1) (by omega) (by omega)
    (by omega) (by slot) (by slot; exact hC.s1) (bB _ hU0 (by omega)) (bB _ (by norm_num) (by omega))
    (bB _ (by omega) (by omega))) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.addI hL (x := o + 14) (a := o + 11) (b := o + 1) (u := U + 1) (v := 1) (by omega) (by omega)
    (by omega) (by slot) (by slot; exact hC.s1) (bB _ (by omega) (by omega)) (bB _ (by norm_num) (by omega))
    (bB _ (by omega) (by omega))) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.addI hL (x := o + 12) (a := o + 1) (b := o) (u := 1) (v := 0) (by omega) (by omega)
    (by omega) (by slot; exact hC.s1) (by slot; exact hC.s0) (bB _ (by norm_num) (by omega))
    (bB _ (by norm_num) (by omega)) (bB _ (by norm_num) (by omega))) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.addI hL (x := o + 13) (a := o + 2) (b := o) (u := 2) (v := 0) (by omega) (by omega)
    (by omega) (by slot; exact hC.s2) (by slot; exact hC.s0) (bB _ (by norm_num) (by omega))
    (bB _ (by norm_num) (by omega)) (bB _ (by norm_num) (by omega))) fun σ6 e6 => ?_
  subst e6
  refine XV.seq (XV.addI hL (x := o + 15) (a := o) (b := o) (u := 0) (v := 0) (by omega) (by omega)
    (by omega) (by slot; exact hC.s0) (by slot; exact hC.s0) (bB _ (by norm_num) (by omega))
    (bB _ (by norm_num) (by omega)) (bB _ (by norm_num) (by omega))) fun σ7 e7 => ?_
  subst e7
  have hW2 : σ.draws + B + B = σ.draws + 2 * B := by ring
  refine XV.mono (XV.whileS hL (x := o + 13) (y := o + 14) (by omega) (by omega)
    (fun t σ' => σ'.sc (o + 9) = (U : ℝ) ∧
      σ'.sc (o + 10) = (BitRAM.readCoins X.wb.cs (σ.draws + B) B : ℝ) ∧
      σ'.sc (o + 11) = ((U + 1 : ℤ) : ℝ) ∧ σ'.sc (o + 14) = ((U + 1 + 1 : ℤ) : ℝ) ∧
      σ'.sc (o + 12) = ((2 ^ t : ℤ) : ℝ) ∧ σ'.sc (o + 13) = ((2 ^ (t + 1) : ℤ) : ℝ) ∧
      σ'.sc (o + 15) = ((t : ℕ) : ℤ) ∧ 2 ^ t ≤ Un + 1 ∧ σ'.draws = σ.draws + 2 * B ∧
      FrameP (fun y => o + 9 ≤ y ∧ y < o + 16) (fun _ => False) σ σ')
    B 3 ?_ ?_ ?_ 0 _ ?_) le_rfl ?_
  · intro t σ' ⟨_, _, _, i14, _, i13, _, ile, _⟩
    have : (2 : ℤ) ^ t ≤ U + 1 := by rw [← hUn]; exact_mod_cast ile
    refine ⟨by rw [i13]; exact XV.abs_int_lt (bB _ (by positivity) (by rw [pow_succ, h2B]; omega)),
      by rw [i14]; exact XV.abs_int_lt (bB _ (by omega) (by omega))⟩
  · intro t σ' ⟨_, _, _, i14, _, i13, _, ile, _⟩ hc
    rw [i13, i14, Int.cast_lt] at hc
    have : (2 : ℤ) ^ (t + 1) ≤ 2 ^ B := by omega
    have := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℤ) < 2)).1 this
    omega
  · intro t σ' ⟨i9, i10, i11, i14, i12, i13, i15, ile, idr, iF⟩ hc
    rw [i13, i14, Int.cast_lt] at hc
    have hcN : 2 ^ (t + 1) ≤ Un + 1 := by
      have : (2 : ℤ) ^ (t + 1) ≤ Un + 1 := by rw [hUn]; omega
      exact_mod_cast this
    have htB : t + 1 ≤ B := by
      have : 2 ^ (t + 1) ≤ 2 ^ B := by omega
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
    have z0 : σ'.sc o = ((0 : ℤ) : ℝ) := by rw [iF.2.1 o (by omega), hC.s0]
    have z1 : σ'.sc (o + 1) = ((1 : ℤ) : ℝ) := by rw [iF.2.1 (o + 1) (by omega), hC.s1]
    have ht2 : (2 : ℤ) ^ (t + 1 + 1) ≤ 2 ^ (B + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have ht1 : (2 : ℤ) ^ (t + 1) ≤ 2 ^ (B + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    refine XV.seq (K₂ := 2) (XV.addI hL (x := o + 12) (a := o + 13) (b := o) (u := 2 ^ (t + 1)) (v := 0) (by omega)
      (by omega) (by omega) i13 z0 (bB _ (by positivity) ht1) (bB _ le_rfl (by positivity))
      (bB _ (by positivity) (by simpa using ht1))) fun σa ea => ?_
    subst ea
    refine XV.seq (K₂ := 1) (XV.addI hL (x := o + 13) (a := o + 13) (b := o + 13) (u := 2 ^ (t + 1)) (v := 2 ^ (t + 1))
      (by omega) (by omega) (by omega) (by slot) (by slot) (bB _ (by positivity) ht1) (bB _ (by positivity) ht1)
      (bB _ (by positivity) (by rw [← two_mul, ← pow_succ']; exact ht2))) fun σb eb => ?_
    subst eb
    refine XV.mono (XV.addI hL (x := o + 15) (a := o + 15) (b := o + 1) (u := ((t : ℕ) : ℤ)) (v := 1) (by omega)
      (by omega) (by omega) (by slot) (by slot) (bB _ (by positivity) ?_) (bB _ (by norm_num) (by omega))
      (bB _ (by positivity) ?_)) le_rfl fun σc ec => ?_
    · have : (t : ℤ) < 2 ^ t := by exact_mod_cast Nat.lt_two_pow_self
      have : (2 : ℤ) ^ t ≤ 2 ^ (B + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      omega
    · have : ((t + 1 : ℕ) : ℤ) < 2 ^ (t + 1) := by exact_mod_cast Nat.lt_two_pow_self
      push_cast at this
      omega
    subst ec
    refine ⟨by slot, by slot, by slot, by slot, by slot <;> simp, by slot <;> (push_cast; ring),
      by slot <;> (push_cast; ring), hcN, by simpa using idr, ?_⟩
    exact ((iF.setSc ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _
  · refine ⟨by slot, by slot <;> simp [hC.nB], by slot, by slot, by slot <;> simp, by slot <;> simp, by slot <;> simp,
      by simp, by simp [hC.nB]; ring, ?_⟩
    exact (((((((FrameP.refl _ _ σ).setSc ⟨by omega, by omega⟩ _).draws _).setSc ⟨by omega, by omega⟩ _).draws
      _).setSc ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _
      |>.setSc ⟨by omega, by omega⟩ _ |>.setSc ⟨by omega, by omega⟩ _
  · intro σ' ⟨t, ⟨i9, i10, i11, i14, i12, i13, i15, ile, idr, iF⟩, hx⟩
    rw [i13, i14, Int.cast_lt] at hx
    have hlt : Un + 1 < 2 ^ (t + 1) := by
      have : (Un : ℤ) + 1 < 2 ^ (t + 1) := by rw [hUn]; omega
      exact_mod_cast this
    have he : Nat.log 2 (Un + 1) = t := bm_log_eq (Un + 1) t ile hlt
    exact ⟨i9, i10, i11, by rw [he, i12], by rw [he, i15], idr, iF⟩


/-! ## The argument of Mercator's series -/

/-- `X = ((N - 2^e) 2^q) div N` at `o + 16`, through the temporary `o + 20`. -/
def xbmX (L : Layout) (o : ℕ) : XCmd :=
  .seq (toX (VL.sop2 L .sub (o + 20) (o + 11) (o + 12)))
  (.seq (toX (VL.sop2 L .mul (o + 20) (o + 20) (o + 5)))
  (xsidiv L (o + 16) (o + 20) (o + 11)))

theorem XV.bmX {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {o on B : ℕ}
    (hS : o + 21 ≤ L.NS) (hC : BmC o on B σ) {Un e : ℕ} (hN1 : σ.sc (o + 11) = (((Un + 1 : ℕ) : ℤ) : ℝ))
    (he : σ.sc (o + 12) = (((2 ^ e : ℕ) : ℤ) : ℝ)) (h2e : 2 ^ e ≤ Un + 1) (hUn : Un + 1 ≤ 2 ^ B)
    (hℓ : 4 * gsm_prec B + 4 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xbmX L o) σ 3 (fun σ' =>
      σ'.sc (o + 16) = ((((Un + 1 - 2 ^ e) * 2 ^ (2 * gsm_prec B) / (Un + 1) : ℕ) : ℤ) : ℝ) ∧
      FrameP (fun y => y = o + 16 ∨ y = o + 20) (fun _ => False) σ σ') := by
  obtain ⟨hp4, -⟩ := bm_prec B
  set p := gsm_prec B
  have bb : ∀ z : ℤ, 0 ≤ z → z ≤ 2 ^ (B + 2 * p) → |z| < 2 ^ ℓ := fun z h0 h1 => absI_lt h0 h1 (by omega)
  have hBe : ((Un + 1 : ℕ) : ℤ) - ((2 ^ e : ℕ) : ℤ) = ((Un + 1 - 2 ^ e : ℕ) : ℤ) := by push_cast [Nat.cast_sub h2e]; ring
  have hB1 : ((Un + 1 : ℕ) : ℤ) ≤ 2 ^ B := by exact_mod_cast hUn
  have hB2 : (2 : ℤ) ^ B ≤ 2 ^ (B + 2 * p) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hq2 : (2 : ℤ) ^ (2 * p) ≤ 2 ^ (B + 2 * p) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hd : ((Un + 1 - 2 ^ e : ℕ) : ℤ) ≤ 2 ^ B := by
    have : Un + 1 - 2 ^ e ≤ 2 ^ B := le_trans (Nat.sub_le _ _) hUn
    exact_mod_cast this
  have hd0 : (0 : ℤ) ≤ ((Un + 1 - 2 ^ e : ℕ) : ℤ) := Nat.cast_nonneg _
  have h2eZ : ((2 ^ e : ℕ) : ℤ) ≤ 2 ^ B := by exact_mod_cast h2e.trans hUn
  have hpr : ((Un + 1 - 2 ^ e : ℕ) : ℤ) * 2 ^ (2 * p) ≤ 2 ^ (B + 2 * p) := by
    rw [pow_add]; exact mul_le_mul_of_nonneg_right hd (by nn)
  refine XV.seq (K₂ := 2) (XV.subI hL (x := o + 20) (a := o + 11) (b := o + 12) (by omega) (by omega) (by omega) hN1 he
    (bb _ (by nn) (by omega)) (bb _ (by nn) (le_trans h2eZ hB2))
    (by rw [hBe]; exact bb _ hd0 (by omega))) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (K₂ := 1) (XV.mulI hL (x := o + 20) (a := o + 20) (b := o + 5) (u := ((Un + 1 - 2 ^ e : ℕ) : ℤ))
    (v := 2 ^ (2 * p)) (by omega) (by omega) (by omega) (by slot <;> rw [hBe]) (by slot; exact hC.sq)
    (bb _ hd0 (by omega)) (bb _ (by nn) hq2) (bb _ (by nn) hpr)) fun σ2 e2 => ?_
  subst e2
  refine XV.mono (XV.divI hL (x := o + 16) (a := o + 20) (b := o + 11)
    (u := ((Un + 1 - 2 ^ e : ℕ) : ℤ) * 2 ^ (2 * p)) (v := ((Un + 1 : ℕ) : ℤ)) (by omega) (by omega) (by omega)
    (by slot) (by slot) (bb _ (by nn) hpr) (bb _ (by nn) (by omega))) le_rfl fun σ3 e3 => ?_
  subst e3
  refine ⟨by slot <;> (push_cast; ring_nf), ?_⟩
  exact ((FrameP.refl _ _ σ).setSc (Or.inr rfl) _ |>.setSc (Or.inr rfl) _).setSc (Or.inl rfl) _

/-! ## Mercator's fixed-point sum -/

/-- `S := Σ_{i < q} P_i div (i + 1)` with `P_0 = X`, `P_{i+1} = (P_i X) div 2^q` (`gsm_mercq q X q`), `X` read at `Xin`,
the sum written at `S`; `P_i` at `o + 18`, `i + 1` at `o + 19`, a temporary at `o + 20`, the counter `on + 10`. -/
def xbmMerc (L : Layout) (o on S Xin : ℕ) : XCmd :=
  .seq (toX (VL.sop2 L .add S o o))
  (.seq (toX (VL.sop2 L .add (o + 18) Xin o))
  (.seq (toX (VL.sop2 L .add (o + 19) (o + 1) o))
  (xforN (on + 10) (on + 7) (on + 4)
    (.seq (xsidiv L (o + 20) (o + 18) (o + 19))
    (.seq (toX (VL.sop2 L .add S S (o + 20)))
    (.seq (toX (VL.sop2 L .mul (o + 20) (o + 18) Xin))
    (.seq (xsidiv L (o + 18) (o + 20) (o + 5))
    (toX (VL.sop2 L .add (o + 19) (o + 19) (o + 1))))))))))

theorem XV.bmMerc {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {o on B S Xin : ℕ}
    (hS : o + 21 ≤ L.NS) (hN : on + 12 ≤ L.NN) (hC : BmC o on B σ) (hSl : S < L.NS) (hXl : Xin < L.NS)
    (hS9 : o + 9 ≤ S) (hSo : S < o + 18 ∨ o + 20 < S) (hX9 : Xin < o + 18 ∨ o + 20 < Xin) (hSX : S ≠ Xin)
    {Xv : ℕ} (hXv : σ.sc Xin = ((Xv : ℤ) : ℝ)) (hXq : Xv ≤ 2 ^ (2 * gsm_prec B))
    (hℓa : 4 * gsm_prec B + 2 < 2 ^ ℓa) (hℓ : 4 * gsm_prec B + 4 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xbmMerc L o on S Xin) σ (16 * gsm_prec B + 6) (fun σ' =>
      σ'.sc S = ((gsm_mercq (2 * gsm_prec B) Xv (2 * gsm_prec B) : ℕ) : ℤ) ∧
      FrameP (fun y => y = S ∨ (o + 18 ≤ y ∧ y ≤ o + 20)) (fun j => j = on + 10) σ σ') := by
  obtain ⟨hp4, -⟩ := bm_prec B
  set p := gsm_prec B
  set q := 2 * p with hqdef
  have bq : ∀ z : ℤ, 0 ≤ z → z ≤ 2 ^ (2 * q) → |z| < 2 ^ ℓ := fun z h0 h1 => absI_lt h0 h1 (by omega)
  have hXz : (Xv : ℤ) ≤ 2 ^ q := by exact_mod_cast hXq
  have hqq : (2 : ℤ) ^ q ≤ 2 ^ (2 * q) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hq2 : (2 : ℤ) ^ (2 * q) = 2 ^ q * 2 ^ q := by rw [two_mul, pow_add]
  have hqlt : (q : ℤ) + 1 ≤ 2 ^ q := by
    have : q + 1 ≤ 2 ^ q := Nat.lt_two_pow_self
    exact_mod_cast this
  have hmq : ∀ t ≤ q, ((gsm_mercq q Xv t : ℕ) : ℤ) ≤ 2 ^ (2 * q) := fun t ht => by
    have h1 : gsm_mercq q Xv t ≤ t * Xv := bm_mercq_le q Xv t hXq
    have h3 : t * Xv ≤ 2 ^ q * 2 ^ q := Nat.mul_le_mul (le_trans ht Nat.lt_two_pow_self.le) hXq
    have h4 : gsm_mercq q Xv t ≤ 2 ^ (2 * q) := by rw [two_mul, pow_add]; exact le_trans h1 h3
    exact_mod_cast h4
  have hpw : ∀ t, ((gsm_powq q Xv t : ℕ) : ℤ) ≤ 2 ^ q := fun t => by
    have : gsm_powq q Xv t ≤ Xv := bm_powq_le q Xv hXq t
    have : ((gsm_powq q Xv t : ℕ) : ℤ) ≤ Xv := by exact_mod_cast this
    omega
  have hm : ∀ t, ((gsm_mercq q Xv (t + 1) : ℕ) : ℤ) =
      ((gsm_mercq q Xv t : ℕ) : ℤ) + ((gsm_powq q Xv t : ℕ) : ℤ) / ((t + 1 : ℕ) : ℤ) := fun t => by
    unfold gsm_mercq; rw [Finset.sum_range_succ]; push_cast; ring
  have hp : ∀ t, ((gsm_powq q Xv (t + 1) : ℕ) : ℤ) = ((gsm_powq q Xv t : ℕ) : ℤ) * (Xv : ℤ) / 2 ^ q := fun t => by
    rw [gsm_powq]; push_cast; ring
  have z0 : ∀ σ', FrameP (fun y => y = S ∨ (o + 18 ≤ y ∧ y ≤ o + 20)) (fun j => j = on + 10) σ σ' →
      σ'.sc o = ((0 : ℤ) : ℝ) ∧ σ'.sc (o + 1) = ((1 : ℤ) : ℝ) ∧ σ'.sc (o + 5) = ((2 ^ q : ℤ) : ℝ) ∧
      σ'.sc Xin = ((Xv : ℤ) : ℝ) ∧ σ'.nat (on + 7) = q ∧ σ'.nat (on + 4) = 1 := fun σ' hF =>
    ⟨by rw [hF.2.1 o (by omega), hC.s0], by rw [hF.2.1 (o + 1) (by omega), hC.s1],
     by rw [hF.2.1 (o + 5) (by omega), hC.sq], by rw [hF.2.1 Xin (by omega), hXv],
     by rw [hF.1 (on + 7) (by omega), hC.nq], by rw [hF.1 (on + 4) (by omega), hC.n1]⟩
  refine XV.mono (K := 1 + (1 + (1 + (q * (5 + 3) + 3)))) ?_ (by omega) (fun _ h => h)
  refine XV.seq (XV.addI hL (x := S) (a := o) (b := o) (u := 0) (v := 0) hSl (by omega) (by omega) hC.s0 hC.s0
    (bq _ le_rfl (by nn)) (bq _ le_rfl (by nn)) (bq _ le_rfl (by nn))) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.addI hL (x := o + 18) (a := Xin) (b := o) (u := Xv) (v := 0) (by omega) hXl (by omega)
    (by slot) (by slot; exact hC.s0) (bq _ (by nn) (by omega)) (bq _ le_rfl (by nn))
    (bq _ (by nn) (by omega))) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.addI hL (x := o + 19) (a := o + 1) (b := o) (u := 1) (v := 0) (by omega) (by omega)
    (by omega) (by slot; exact hC.s1) (by slot; exact hC.s0) (bq _ (by norm_num) (by omega))
    (bq _ le_rfl (by nn)) (bq _ (by norm_num) (by omega))) fun σ3 e3 => ?_
  subst e3
  refine XV.mono (XV.forN hL (i := on + 10) (n := on + 7) (one := on + 4) (by omega) (by omega) (by omega)
    (by omega) (by omega) q 5 (by omega)
    (fun t σ' => σ'.sc S = ((gsm_mercq q Xv t : ℕ) : ℤ) ∧ σ'.sc (o + 18) = ((gsm_powq q Xv t : ℕ) : ℤ) ∧
      σ'.sc (o + 19) = ((t + 1 : ℕ) : ℤ) ∧
      FrameP (fun y => y = S ∨ (o + 18 ≤ y ∧ y ≤ o + 20)) (fun j => j = on + 10) σ σ') _
    (by slot <;> rw [hC.nq]) (by slot <;> rw [hC.n1]) ?_ ?_) le_rfl (fun σ' ⟨⟨h1, _, _, hF⟩, _⟩ => ⟨h1, hF⟩)
  · refine ⟨by slot <;> simp [gsm_mercq], by slot <;> simp [gsm_powq], by slot <;> simp, ?_⟩
    exact ((((FrameP.refl (fun y => y = S ∨ (o + 18 ≤ y ∧ y ≤ o + 20)) (fun j => j = on + 10) σ).setSc
      (Or.inl rfl) _).setSc (Or.inr ⟨le_rfl, by omega⟩) _).setSc
      (Or.inr ⟨by omega, by omega⟩) _).setNat rfl _
  intro t ht σ' ⟨iS, iP, iI, iF⟩ hi hn h1
  obtain ⟨c0, c1, c5, cX, -, -⟩ := z0 σ' iF
  have hPt := hpw t
  have hP0 : (0 : ℤ) ≤ ((gsm_powq q Xv t : ℕ) : ℤ) := Nat.cast_nonneg _
  have hdiv : ((gsm_powq q Xv t : ℕ) : ℤ) / ((t + 1 : ℕ) : ℤ) ≤ 2 ^ q :=
    le_trans (Int.ediv_le_self _ hP0) hPt
  refine XV.seq (K₂ := 4) (XV.divI hL (x := o + 20) (a := o + 18) (b := o + 19) (by omega) (by omega) (by omega) iP iI
    (bq _ hP0 (by omega)) (bq _ (by nn) (by push_cast; omega))) fun σa ea => ?_
  subst ea
  refine XV.seq (K₂ := 3) (XV.addI hL (x := S) (a := S) (b := o + 20) (u := ((gsm_mercq q Xv t : ℕ) : ℤ))
    (v := ((gsm_powq q Xv t : ℕ) : ℤ) / ((t + 1 : ℕ) : ℤ)) hSl hSl (by omega) (by slot) (by slot)
    (bq _ (by nn) (hmq t ht.le)) (bq _ (Int.ediv_nonneg hP0 (by nn)) (by omega))
    (bq _ (by nn) (by rw [← hm]; exact hmq (t + 1) ht))) fun σb eb => ?_
  subst eb
  refine XV.seq (K₂ := 2) (XV.mulI hL (x := o + 20) (a := o + 18) (b := Xin) (u := ((gsm_powq q Xv t : ℕ) : ℤ))
    (v := Xv) (by omega) (by omega) hXl (by slot) (by slot) (bq _ hP0 (by omega)) (bq _ (by nn)
    (by omega)) (bq _ (by nn) (by rw [hq2]; exact mul_le_mul hPt hXz (by nn) (by nn))))
    fun σc ec => ?_
  subst ec
  refine XV.seq (K₂ := 1) (XV.divI hL (x := o + 18) (a := o + 20) (b := o + 5)
    (u := ((gsm_powq q Xv t : ℕ) : ℤ) * Xv) (v := 2 ^ q) (by omega) (by omega) (by omega) (by slot) (by slot)
    (bq _ (by nn) (by rw [hq2]; exact mul_le_mul hPt hXz (by nn) (by nn)))
    (bq _ (by nn) hqq)) fun σd ed => ?_
  subst ed
  refine XV.mono (XV.addI hL (x := o + 19) (a := o + 19) (b := o + 1) (u := ((t + 1 : ℕ) : ℤ)) (v := 1)
    (by omega) (by omega) (by omega) (by slot) (by slot) (bq _ (by nn) (by push_cast; omega))
    (bq _ (by norm_num) (by omega)) (bq _ (by nn) (by push_cast; omega))) le_rfl fun σe ee => ?_
  subst ee
  refine ⟨by slot, by slot, by slot, ⟨by slot <;> rw [hm], by slot <;> rw [hp], by slot <;> (push_cast; ring), ?_⟩⟩
  exact (((((iF.setSc (Or.inr ⟨by omega, by omega⟩) _).setSc (Or.inl rfl) _).setSc (Or.inr ⟨by omega, by omega⟩) _).setSc
    (Or.inr ⟨by omega, by omega⟩) _).setSc (Or.inr ⟨by omega, by omega⟩) _).setNat rfl _


theorem absI_lt' {z : ℤ} {k ℓ : ℕ} (h1 : -2 ^ k ≤ z) (h2 : z ≤ 2 ^ k) (hk : k < ℓ) : |z| < 2 ^ ℓ := by
  have : (2 : ℤ) ^ k < 2 ^ ℓ := pow_lt_pow_right₀ (by norm_num) hk
  rw [abs_lt]; constructor <;> omega

/-! ## The scaled logarithm, its square root, the angle index -/

/-- `LL = max ((B - e) Lam - S, 0)` at `o + 23`, from `e` at `o + 15`, `Lam` at `o + 21`, `S` at `o + 17`; `B` cast at
`o + 22`, a temporary at `o + 20`. -/
def xbmLL (L : Layout) (o on : ℕ) : XCmd :=
  .seq (toX (VL.ncast L (o + 22) on))
  (.seq (toX (VL.sop2 L .sub (o + 20) (o + 22) (o + 15)))
  (.seq (toX (VL.sop2 L .mul (o + 20) (o + 20) (o + 21)))
  (.seq (toX (VL.sop2 L .sub (o + 23) (o + 20) (o + 17)))
  (xifS L (o + 23) o (toX (VL.sop2 L .add (o + 23) o o)) .skip))))

theorem XV.bmLL {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {o on B : ℕ}
    (hS : o + 24 ≤ L.NS) (hN : on + 12 ≤ L.NN) (hC : BmC o on B σ) {e Lam Sm : ℕ}
    (he : σ.sc (o + 15) = ((e : ℕ) : ℤ)) (heB : e ≤ B) (hLam : σ.sc (o + 21) = ((Lam : ℕ) : ℤ))
    (hSm : σ.sc (o + 17) = ((Sm : ℕ) : ℤ)) (hLb : Lam ≤ 2 * gsm_prec B * 2 ^ (2 * gsm_prec B))
    (hSb : Sm ≤ 2 * gsm_prec B * 2 ^ (2 * gsm_prec B)) (hℓa : 4 * gsm_prec B + 2 < 2 ^ ℓa)
    (hℓ : 4 * gsm_prec B + 4 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xbmLL L o on) σ 6 (fun σ' =>
      σ'.sc (o + 23) = ((max (((B : ℤ) - e) * Lam - Sm) 0 : ℤ) : ℝ) ∧
      FrameP (fun y => y = o + 20 ∨ y = o + 22 ∨ y = o + 23) (fun _ => False) σ σ') := by
  obtain ⟨hp4, hpb⟩ := bm_prec B
  set p := gsm_prec B
  have hBq : B * (2 * p) ≤ 2 ^ p := le_trans (Nat.mul_le_mul_right _ (by omega)) ((Nat.le_add_right _ 2).trans hpb)
  have hq3 : 2 ^ p * 2 ^ (2 * p) = 2 ^ (3 * p) := by rw [← pow_add]; ring_nf
  have hLB : B * Lam ≤ 2 ^ (3 * p) := by
    rw [← hq3]; calc B * Lam ≤ B * (2 * p * 2 ^ (2 * p)) := Nat.mul_le_mul_left _ hLb
      _ = B * (2 * p) * 2 ^ (2 * p) := by ring
      _ ≤ 2 ^ p * 2 ^ (2 * p) := Nat.mul_le_mul_right _ hBq
  have h2p : 2 * p ≤ 2 ^ p := by
    have h1 : p - 1 < 2 ^ (p - 1) := Nat.lt_two_pow_self
    have h2 : 2 ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ']; congr 1
    omega
  have hSB : Sm ≤ 2 ^ (3 * p) := by rw [← hq3]; exact le_trans hSb (Nat.mul_le_mul_right _ h2p)
  have hLam3 : Lam ≤ 2 ^ (3 * p) := by rw [← hq3]; exact le_trans hLb (Nat.mul_le_mul_right _ h2p)
  have hLam3z : (Lam : ℤ) ≤ 2 ^ (3 * p) := by exact_mod_cast hLam3
  have hLBz : ((B : ℤ) - e) * Lam ≤ 2 ^ (3 * p) := by
    have h1 : ((B : ℤ) - e) * Lam ≤ (B : ℤ) * Lam :=
      mul_le_mul_of_nonneg_right (by omega) (Nat.cast_nonneg _)
    have h2 : ((B * Lam : ℕ) : ℤ) ≤ 2 ^ (3 * p) := by exact_mod_cast hLB
    push_cast at h2; omega
  have hLB0 : 0 ≤ ((B : ℤ) - e) * Lam := mul_nonneg (by omega) (Nat.cast_nonneg _)
  have hSBz : (Sm : ℤ) ≤ 2 ^ (3 * p) := by exact_mod_cast hSB
  have hB3 : (B : ℤ) ≤ 2 ^ (3 * p) := by
    have : B < 2 ^ (3 * p) := lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact_mod_cast this.le
  have h3p : (0 : ℤ) ≤ 2 ^ (3 * p) := pow_nonneg (by norm_num) _
  have b3 : ∀ z : ℤ, -2 ^ (3 * p + 1) ≤ z → z ≤ 2 ^ (3 * p + 1) → |z| < 2 ^ ℓ := fun z h1 h2 =>
    absI_lt' h1 h2 (by omega)
  have h31 : (2 : ℤ) ^ (3 * p + 1) = 2 * 2 ^ (3 * p) := by ring
  refine XV.seq (K₂ := 5) (XV.ncastI hL (x := o + 22) (i := on) (by omega) (by omega) (by rw [hC.nB]; omega))
    fun σ1 e1 => ?_
  subst e1
  rw [hC.nB]
  refine XV.seq (K₂ := 4) (XV.subI hL (x := o + 20) (a := o + 22) (b := o + 15) (u := B) (v := e) (by omega)
    (by omega) (by omega) (by slot) (by slot) (b3 _ (by omega) (by omega)) (b3 _ (by omega) (by omega))
    (b3 _ (by omega) (by omega))) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (K₂ := 3) (XV.mulI hL (x := o + 20) (a := o + 20) (b := o + 21) (u := (B : ℤ) - e) (v := Lam)
    (by omega) (by omega) (by omega) (by slot) (by slot) (b3 _ (by omega) (by omega))
    (b3 _ (by omega) (by omega)) (b3 _ (by omega) (by omega))) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (K₂ := 2) (XV.subI hL (x := o + 23) (a := o + 20) (b := o + 17) (u := ((B : ℤ) - e) * Lam)
    (v := Sm) (by omega) (by omega) (by omega) (by slot) (by slot) (b3 _ (by omega) (by omega))
    (b3 _ (by omega) (by omega)) (b3 _ (by omega) (by omega))) fun σ4 e4 => ?_
  subst e4
  have F4 : FrameP (fun y => y = o + 20 ∨ y = o + 22 ∨ y = o + 23) (fun _ => False) σ
      ((((σ.setSc (o + 22) ((B : ℤ) : ℝ)).setSc (o + 20) (((B : ℤ) - e : ℤ) : ℝ)).setSc (o + 20)
        ((((B : ℤ) - e) * Lam : ℤ) : ℝ)).setSc (o + 23) ((((B : ℤ) - e) * Lam - Sm : ℤ) : ℝ)) :=
    ((((FrameP.refl _ _ σ).setSc (Or.inr (Or.inl rfl)) _).setSc (Or.inl rfl) _).setSc (Or.inl rfl) _).setSc
      (Or.inr (Or.inr rfl)) _
  have v23 := sc_setSc_eq (((σ.setSc (o + 22) ((B : ℤ) : ℝ)).setSc (o + 20) (((B : ℤ) - e : ℤ) : ℝ)).setSc
    (o + 20) ((((B : ℤ) - e) * Lam : ℤ) : ℝ)) (o + 23) ((((B : ℤ) - e) * Lam - Sm : ℤ) : ℝ)
  have v0 : ((((σ.setSc (o + 22) ((B : ℤ) : ℝ)).setSc (o + 20) (((B : ℤ) - e : ℤ) : ℝ)).setSc (o + 20)
      ((((B : ℤ) - e) * Lam : ℤ) : ℝ)).setSc (o + 23) ((((B : ℤ) - e) * Lam - Sm : ℤ) : ℝ)).sc o = ((0 : ℤ) : ℝ) := by
    rw [F4.2.1 o (by omega)]; exact hC.s0
  have bL : |((((((B : ℤ) - e) * Lam - Sm : ℤ)) : ℝ))| < 2 ^ ℓ := XV.abs_int_lt (b3 _ (by omega) (by omega))
  by_cases hneg : ((B : ℤ) - e) * Lam - Sm < 0
  · refine XV.ifS_t hL (by omega) (by omega) (by rw [v23]; exact bL) (by rw [v0]; simp) (by rw [v23, v0]; exact_mod_cast hneg) ?_
    refine XV.mono (XV.addI hL (x := o + 23) (a := o) (b := o) (u := 0) (v := 0) (by omega) (by omega) (by omega)
      v0 v0 (b3 _ (by omega) (by omega)) (b3 _ (by omega) (by omega)) (b3 _ (by omega) (by omega))) le_rfl
      fun σ5 e5 => ?_
    subst e5
    exact ⟨by rw [sc_setSc_eq, max_eq_right hneg.le]; simp, F4.setSc (Or.inr (Or.inr rfl)) _⟩
  · refine XV.ifS_f hL (by omega) (by omega) (by rw [v23]; exact bL) (by rw [v0]; simp) (by rw [v23, v0]; exact_mod_cast hneg) ?_
    refine XV.mono (XV.skip _) le_rfl fun σ5 e5 => ?_
    subst e5
    exact ⟨by rw [v23, max_eq_left (by omega)], F4⟩

/-- `R = isqrt (2 LL)` at `o + 25`, through `o + 24, ..., o + 28`. -/
def xbmR (L : Layout) (o : ℕ) : XCmd :=
  .seq (toX (VL.sop2 L .add (o + 24) (o + 23) (o + 23)))
  (xisqrt L (o + 24) (o + 25) (o + 26) (o + 27) (o + 28) o (o + 1) (o + 2) (o + 3))

theorem XV.bmR {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {o on B : ℕ}
    (hS : o + 29 ≤ L.NS) (hC : BmC o on B σ) {LL : ℕ} (hLL : σ.sc (o + 23) = ((LL : ℕ) : ℤ))
    (hLb : LL ≤ 2 ^ (3 * gsm_prec B)) (hℓ : 4 * gsm_prec B + 4 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xbmR L o) σ (36 * gsm_prec B + 33) (fun σ' =>
      σ'.sc (o + 25) = (((Nat.sqrt (2 * LL) : ℕ) : ℤ) : ℝ) ∧
      FrameP (fun y => o + 24 ≤ y ∧ y ≤ o + 28) (fun _ => False) σ σ') := by
  obtain ⟨hp4, -⟩ := bm_prec B
  set p := gsm_prec B
  have h2L : 2 * LL < 2 ^ (3 * p + 2) := by
    have h0 : 0 < 2 ^ (3 * p) := Nat.pos_of_ne_zero (by simp)
    rw [pow_add]; norm_num; omega
  have hL2 : LL ≤ 2 ^ (3 * p + 2) := le_trans hLb (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hz : ∀ k ≤ 3 * p + 2, |((2 ^ k : ℕ) : ℤ)| < 2 ^ ℓ := fun k hk =>
    absI_lt (Nat.cast_nonneg _) (by push_cast; exact pow_le_pow_right₀ (by norm_num) hk) (by omega)
  have hb : ∀ v : ℕ, v ≤ 2 ^ (3 * p + 2) → |((v : ℕ) : ℤ)| < 2 ^ ℓ := fun v hv =>
    absI_lt (Nat.cast_nonneg _) (by exact_mod_cast hv) (by omega)
  have hsz : (2 * LL).size ≤ 3 * p + 2 := Nat.size_le.2 h2L
  refine XV.mono (K := 1 + (12 * (3 * p + 2) + 8)) ?_ (by omega) (fun _ h => h)
  refine XV.seq (XV.addI hL (x := o + 24) (a := o + 23) (b := o + 23) (u := LL) (v := LL)
    (by omega) (by omega) (by omega) hLL hLL (hb _ hL2) (hb _ hL2) ?_) fun σ1 e1 => ?_
  · have := hb (2 * LL) h2L.le; push_cast at this; rwa [two_mul] at this
  subst e1
  refine XV.mono (XV.isqrt hL (r := o + 24) (dd := o + 25) (q := o + 26) (t := o + 27) (n1 := o + 28) (z := o)
    (one := o + 1) (two := o + 2) (four := o + 3) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by simp) (n := 2 * LL) (by slot <;> (push_cast; ring))
    (by slot; rw [hC.s0]; simp) (by slot; rw [hC.s1]; simp) (by slot; rw [hC.s2]; simp)
    (by slot; rw [hC.s4]; simp) ?_) (by omega) fun σ2 ⟨h1, _, hF⟩ => ⟨by rw [h1]; simp, ?_⟩
  · have : 4 * (2 * LL) + 4 < 2 ^ ℓ := by
      have : 2 ^ (3 * p + 2) * 8 ≤ 2 ^ ℓ := by
        rw [show 8 = 2 ^ 3 by norm_num, ← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact this
  · exact FrameP.trans ((FrameP.refl (fun y => o + 24 ≤ y ∧ y ≤ o + 28) (fun _ => False) σ).setSc
      ⟨le_rfl, by omega⟩ _) (FrameP.of_frame hF (fun y hy => by simp at hy; omega) (by simp))

/-- `J = (W + 1) mod 2^B` at `o + 29`, from `W` at `o + 10` and `2^B` at `o + 8`. -/
def xbmJ (L : Layout) (o : ℕ) : XCmd :=
  .seq (toX (VL.sop2 L .add (o + 29) (o + 10) (o + 1)))
  (xifS L (o + 29) (o + 8) .skip (toX (VL.sop2 L .sub (o + 29) (o + 29) (o + 8))))

theorem XV.bmJ {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {o on B : ℕ}
    (hS : o + 30 ≤ L.NS) (hC : BmC o on B σ) {Wn : ℕ} (hW : σ.sc (o + 10) = ((Wn : ℕ) : ℤ)) (hWB : Wn < 2 ^ B)
    (hℓ : 4 * gsm_prec B + 4 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xbmJ L o) σ 4 (fun σ' =>
      σ'.sc (o + 29) = ((((Wn + 1) % 2 ^ B : ℕ) : ℤ) : ℝ) ∧
      FrameP (fun y => y = o + 29) (fun _ => False) σ σ') := by
  obtain ⟨hp4, -⟩ := bm_prec B
  have hb : ∀ z : ℤ, 0 ≤ z → z ≤ 2 ^ B → |z| < 2 ^ ℓ := fun z h0 h1 => absI_lt h0 h1 (by omega)
  have hWz : (Wn : ℤ) + 1 ≤ 2 ^ B := by exact_mod_cast hWB
  refine XV.seq (K₂ := 3) (XV.addI hL (x := o + 29) (a := o + 10) (b := o + 1) (u := Wn) (v := 1) (by omega)
    (by omega) (by omega) hW hC.s1 (hb _ (Nat.cast_nonneg _) (by omega)) (hb _ (by norm_num) (by omega))
    (hb _ (by omega) hWz)) fun σ1 e1 => ?_
  subst e1
  have v29 := sc_setSc_eq σ (o + 29) ((((Wn : ℤ) + 1 : ℤ)) : ℝ)
  have v8 : (σ.setSc (o + 29) ((((Wn : ℤ) + 1 : ℤ)) : ℝ)).sc (o + 8) = ((2 ^ B : ℤ) : ℝ) := by slot; exact hC.sB
  have F : FrameP (fun y => y = o + 29) (fun _ => False) σ (σ.setSc (o + 29) ((((Wn : ℤ) + 1 : ℤ)) : ℝ)) :=
    (FrameP.refl (fun y => y = o + 29) (fun _ => False) σ).setSc rfl _
  by_cases hlt : Wn + 1 < 2 ^ B
  · refine XV.mono (XV.ifS_t hL (by omega) (by omega) (by rw [v29]; exact XV.abs_int_lt (hb _ (by omega) hWz))
      (by rw [v8]; exact XV.abs_int_lt (hb _ (pow_nonneg (by norm_num) _) le_rfl)) (by rw [v29, v8]; exact_mod_cast hlt) (XV.skip _)) (by omega) fun σ2 e2 => ?_
    subst e2
    exact ⟨by rw [v29, Nat.mod_eq_of_lt hlt]; push_cast; ring, F⟩
  · have heq : Wn + 1 = 2 ^ B := by omega
    have hz : (Wn : ℤ) + 1 = 2 ^ B := by exact_mod_cast heq
    refine XV.ifS_f hL (by omega) (by omega) (by rw [v29]; exact XV.abs_int_lt (hb _ (by omega) hWz))
      (by rw [v8]; exact XV.abs_int_lt (hb _ (pow_nonneg (by norm_num) _) le_rfl)) (by rw [v29, v8]; exact_mod_cast hlt) ?_
    refine XV.mono (XV.subI hL (x := o + 29) (a := o + 29) (b := o + 8) (u := (Wn : ℤ) + 1) (v := 2 ^ B) (by omega)
      (by omega) (by omega) v29 v8 (hb _ (by omega) hWz) (hb _ (pow_nonneg (by norm_num) _) le_rfl)
      (hb _ (by omega) (by omega))) le_rfl fun σ2 e2 => ?_
    subst e2
    refine ⟨by rw [sc_setSc_eq, heq, Nat.mod_self, hz]; simp, F.setSc rfl _⟩


/-! ## The product loop: one rounded complex product, one step of the half-angle chain -/

/-- `(ZX, ZY) := ((ZX C - ZY Sn) div 2^p, (ZX Sn + ZY C) div 2^p)`, the pair at `o + 34, o + 35`, the factor at
`o + 36, o + 37`, temporaries `o + 20, o + 38, o + 39`. -/
def xbmCmul (L : Layout) (o : ℕ) : XCmd :=
  .seq (toX (VL.sop2 L .mul (o + 38) (o + 34) (o + 36)))
  (.seq (toX (VL.sop2 L .mul (o + 39) (o + 35) (o + 37)))
  (.seq (toX (VL.sop2 L .sub (o + 38) (o + 38) (o + 39)))
  (.seq (toX (VL.sop2 L .mul (o + 39) (o + 34) (o + 37)))
  (.seq (toX (VL.sop2 L .mul (o + 20) (o + 35) (o + 36)))
  (.seq (toX (VL.sop2 L .add (o + 39) (o + 39) (o + 20)))
  (.seq (xsidiv L (o + 34) (o + 38) (o + 4))
  (xsidiv L (o + 35) (o + 39) (o + 4))))))))

theorem XV.bmCmul {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {o on B : ℕ}
    (hS : o + 43 ≤ L.NS) (hC : BmC o on B σ) {zx zy : ℤ} {c s : ℕ} (hzx : σ.sc (o + 34) = zx)
    (hzy : σ.sc (o + 35) = zy) (hc : σ.sc (o + 36) = ((c : ℕ) : ℤ)) (hs : σ.sc (o + 37) = ((s : ℕ) : ℤ))
    (bzx : |zx| ≤ 2 ^ (2 * gsm_prec B)) (bzy : |zy| ≤ 2 ^ (2 * gsm_prec B)) (bc : c ≤ 2 ^ gsm_prec B)
    (bs : s ≤ 2 ^ gsm_prec B) (hℓ : 4 * gsm_prec B + 4 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xbmCmul L o) σ 8 (fun σ' =>
      σ'.sc (o + 34) = ((gsm_cmulq (gsm_prec B) (zx, zy) ((c : ℤ), (s : ℤ))).1 : ℝ) ∧
      σ'.sc (o + 35) = ((gsm_cmulq (gsm_prec B) (zx, zy) ((c : ℤ), (s : ℤ))).2 : ℝ) ∧
      FrameP (fun y => y = o + 20 ∨ y = o + 34 ∨ y = o + 35 ∨ y = o + 38 ∨ y = o + 39) (fun _ => False) σ σ') := by
  obtain ⟨hp4, -⟩ := bm_prec B
  set p := gsm_prec B
  have b4 : ∀ z : ℤ, -2 ^ (4 * p) ≤ z → z ≤ 2 ^ (4 * p) → |z| < 2 ^ ℓ := fun z h1 h2 => absI_lt' h1 h2 (by omega)
  have hcz : (c : ℤ) ≤ 2 ^ p := by exact_mod_cast bc
  have hsz : (s : ℤ) ≤ 2 ^ p := by exact_mod_cast bs
  have h0p : (0 : ℤ) ≤ 2 ^ p := pow_nonneg (by norm_num) _
  have h3 : (2 : ℤ) ^ (2 * p) * 2 ^ p = 2 ^ (3 * p) := by rw [← pow_add]; ring_nf
  have h34 : (2 : ℤ) ^ (3 * p) ≤ 2 ^ (4 * p) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3p : (2 : ℤ) ^ (3 * p + 1) ≤ 2 ^ (4 * p) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h31 : (2 : ℤ) ^ (3 * p + 1) = 2 * 2 ^ (3 * p) := by ring
  have h2p : (2 : ℤ) ^ p ≤ 2 ^ (4 * p) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h22 : (2 : ℤ) ^ (2 * p) ≤ 2 ^ (4 * p) := pow_le_pow_right₀ (by norm_num) (by omega)
  have mb : ∀ a b : ℤ, |a| ≤ 2 ^ (2 * p) → 0 ≤ b → b ≤ 2 ^ p → |a * b| ≤ 2 ^ (3 * p) := fun a b ha hb0 hb => by
    rw [abs_mul, abs_of_nonneg hb0, ← h3]; exact mul_le_mul ha hb hb0 (pow_nonneg (by norm_num) _)
  have h30 : (0 : ℤ) ≤ 2 ^ (3 * p) := pow_nonneg (by norm_num) _
  have ab : ∀ z : ℤ, |z| ≤ 2 ^ (3 * p + 1) → |z| < 2 ^ ℓ := fun z hz =>
    b4 _ (by have := neg_abs_le z; omega) (by have := le_abs_self z; omega)
  have a3 : ∀ z : ℤ, |z| ≤ 2 ^ (3 * p) → |z| < 2 ^ ℓ := fun z hz => ab z (by omega)
  have a2 : ∀ z : ℤ, |z| ≤ 2 ^ (2 * p) → |z| < 2 ^ ℓ := fun z hz => ab z (by
    have : (2 : ℤ) ^ (2 * p) ≤ 2 ^ (3 * p + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    omega)
  have ac : |(c : ℤ)| ≤ 2 ^ (2 * p) := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact hcz.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have as' : |(s : ℤ)| ≤ 2 ^ (2 * p) := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact hsz.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have m1 := mb zx c bzx (Nat.cast_nonneg _) hcz
  have m2 := mb zy s bzy (Nat.cast_nonneg _) hsz
  have m3 := mb zx s bzx (Nat.cast_nonneg _) hsz
  have m4 := mb zy c bzy (Nat.cast_nonneg _) hcz
  have d1 : |zx * c - zy * s| ≤ 2 ^ (3 * p + 1) := by
    have := abs_sub (zx * c) (zy * s); omega
  have d2 : |zx * s + zy * c| ≤ 2 ^ (3 * p + 1) := by
    have := abs_add_le (zx * s) (zy * c); omega
  have ap : |(2 : ℤ) ^ p| ≤ 2 ^ (2 * p) := by
    rw [abs_of_nonneg h0p]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  refine XV.mono (K := 1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))) ?_ (by omega) (fun _ h => h)
  refine XV.seq (XV.mulI hL (x := o + 38) (a := o + 34) (b := o + 36) (u := zx) (v := c) (by omega) (by omega)
    (by omega) hzx hc (a2 _ bzx) (a2 _ ac) (a3 _ m1)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.mulI hL (x := o + 39) (a := o + 35) (b := o + 37) (u := zy) (v := s) (by omega) (by omega)
    (by omega) (by slot) (by slot) (a2 _ bzy) (a2 _ as') (a3 _ m2)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.subI hL (x := o + 38) (a := o + 38) (b := o + 39) (u := zx * c) (v := zy * s) (by omega)
    (by omega) (by omega) (by slot) (by slot) (a3 _ m1) (a3 _ m2) (ab _ d1)) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.mulI hL (x := o + 39) (a := o + 34) (b := o + 37) (u := zx) (v := s) (by omega) (by omega)
    (by omega) (by slot) (by slot) (a2 _ bzx) (a2 _ as') (a3 _ m3)) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.mulI hL (x := o + 20) (a := o + 35) (b := o + 36) (u := zy) (v := c) (by omega) (by omega)
    (by omega) (by slot) (by slot) (a2 _ bzy) (a2 _ ac) (a3 _ m4)) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.addI hL (x := o + 39) (a := o + 39) (b := o + 20) (u := zx * s) (v := zy * c) (by omega)
    (by omega) (by omega) (by slot) (by slot) (a3 _ m3) (a3 _ m4) (ab _ d2)) fun σ6 e6 => ?_
  subst e6
  have v4 : ∀ σ' : Env d, FrameP (fun y => y = o + 20 ∨ y = o + 34 ∨ y = o + 35 ∨ y = o + 38 ∨ y = o + 39)
      (fun _ => False) σ σ' → σ'.sc (o + 4) = ((2 ^ p : ℤ) : ℝ) := fun σ' hF => by
    rw [hF.2.1 (o + 4) (by omega)]; exact hC.sp
  have F6 : FrameP (fun y => y = o + 20 ∨ y = o + 34 ∨ y = o + 35 ∨ y = o + 38 ∨ y = o + 39) (fun _ => False) σ
      ((((((σ.setSc (o + 38) ((zx * c : ℤ) : ℝ)).setSc (o + 39) ((zy * s : ℤ) : ℝ)).setSc (o + 38)
        ((zx * c - zy * s : ℤ) : ℝ)).setSc (o + 39) ((zx * s : ℤ) : ℝ)).setSc (o + 20) ((zy * c : ℤ) : ℝ)).setSc
        (o + 39) ((zx * s + zy * c : ℤ) : ℝ)) :=
    (((((((FrameP.refl _ _ σ).setSc (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _).setSc
      (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) _).setSc (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _).setSc
      (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) _).setSc (Or.inl rfl) _).setSc (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) _)
  refine XV.seq (XV.divI hL (x := o + 34) (a := o + 38) (b := o + 4) (u := zx * c - zy * s) (v := 2 ^ p)
    (by omega) (by omega) (by omega) (by slot) (v4 _ F6) (ab _ d1) (a2 _ ap)) fun σ7 e7 => ?_
  subst e7
  refine XV.mono (XV.divI hL (x := o + 35) (a := o + 39) (b := o + 4) (u := zx * s + zy * c) (v := 2 ^ p)
    (by omega) (by omega) (by omega) (by slot) (v4 _ (F6.setSc (Or.inr (Or.inl rfl)) _)) (ab _ d2) (a2 _ ap)) le_rfl
    fun σ8 e8 => ?_
  subst e8
  exact ⟨by slot <;> rfl, by slot <;> rfl, (F6.setSc (Or.inr (Or.inl rfl)) _).setSc (Or.inr (Or.inr (Or.inl rfl))) _⟩

/-- One step of the half-angle chain: `C := isqrt ((2^p + C) 2^(p-1))`, `Sn := (Sn 2^(p-1)) div C`, the chain at
`o + 36, o + 37`, through `o + 42`, `o + 26, o + 27, o + 28` and `o + 20`. -/
def xbmChain (L : Layout) (o : ℕ) : XCmd :=
  .seq (toX (VL.sop2 L .add (o + 42) (o + 4) (o + 36)))
  (.seq (toX (VL.sop2 L .mul (o + 42) (o + 42) (o + 6)))
  (.seq (xisqrt L (o + 42) (o + 36) (o + 26) (o + 27) (o + 28) o (o + 1) (o + 2) (o + 3))
  (.seq (toX (VL.sop2 L .mul (o + 20) (o + 37) (o + 6)))
  (xsidiv L (o + 37) (o + 20) (o + 36)))))

theorem XV.bmChain {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {o on B : ℕ}
    (hS : o + 43 ≤ L.NS) (hC : BmC o on B σ) {k : ℕ}
    (hc : σ.sc (o + 36) = (((gsm_chainq (gsm_prec B) k).1 : ℕ) : ℤ))
    (hs : σ.sc (o + 37) = (((gsm_chainq (gsm_prec B) k).2 : ℕ) : ℤ)) (hℓ : 4 * gsm_prec B + 4 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xbmChain L o) σ (24 * gsm_prec B + 24) (fun σ' =>
      σ'.sc (o + 36) = (((gsm_chainq (gsm_prec B) (k + 1)).1 : ℕ) : ℤ) ∧
      σ'.sc (o + 37) = (((gsm_chainq (gsm_prec B) (k + 1)).2 : ℕ) : ℤ) ∧
      FrameP (fun y => y = o + 20 ∨ (o + 26 ≤ y ∧ y ≤ o + 28) ∨ y = o + 36 ∨ y = o + 37 ∨ y = o + 42) (fun _ => False)
        σ σ') := by
  obtain ⟨hp4, -⟩ := bm_prec B
  set p := gsm_prec B
  obtain ⟨bc, bs⟩ := bm_chainq_le p k (by omega)
  set c := (gsm_chainq p k).1
  set s := (gsm_chainq p k).2
  have hpp : 2 ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ']; congr 1
  have h2p : 2 ^ p * 2 ^ p = 2 ^ (2 * p) := by rw [← pow_add]; ring_nf
  have hn : (2 ^ p + c) * 2 ^ (p - 1) ≤ 2 ^ (2 * p) := by
    rw [← h2p, hpp]; nlinarith
  have hsn : s * 2 ^ (p - 1) ≤ 2 ^ (2 * p) := by rw [← h2p]; nlinarith
  have bN : ∀ v : ℕ, v ≤ 2 ^ (2 * p) → |((v : ℕ) : ℤ)| < 2 ^ ℓ := fun v hv =>
    absI_lt (Nat.cast_nonneg _) (by exact_mod_cast hv) (by omega)
  have hle : ∀ v : ℕ, v ≤ 2 ^ p → v ≤ 2 ^ (2 * p) := fun v hv => le_trans hv (Nat.pow_le_pow_right (by norm_num)
    (by omega))
  have hle1 : 2 ^ (p - 1) ≤ 2 ^ (2 * p) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsz : ((2 ^ p + c) * 2 ^ (p - 1)).size ≤ 2 * p + 1 := Nat.size_le.2 (lt_of_le_of_lt hn
    (Nat.pow_lt_pow_right (by norm_num) (by omega)))
  have hr4 : 4 * ((2 ^ p + c) * 2 ^ (p - 1)) + 4 < 2 ^ ℓ := by
    have : 2 ^ (2 * p) * 8 ≤ 2 ^ ℓ := by
      rw [show 8 = 2 ^ 3 by norm_num, ← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ 1 ≤ 2 ^ (2 * p) := Nat.pow_le_pow_right (by norm_num) (by omega)
    generalize (2 ^ p + c) * 2 ^ (p - 1) = n at hn ⊢
    omega
  have b1 : |((2 ^ p : ℕ) : ℤ) + (c : ℤ)| < 2 ^ ℓ := by
    have := bN (2 ^ p + c) (le_trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) hn)
    push_cast at this ⊢; exact this
  have b2 : |(((2 ^ p : ℕ) : ℤ) + (c : ℤ)) * ((2 ^ (p - 1) : ℕ) : ℤ)| < 2 ^ ℓ := by
    have := bN _ hn; push_cast at this ⊢; exact this
  have b3 : |(s : ℤ) * ((2 ^ (p - 1) : ℕ) : ℤ)| < 2 ^ ℓ := by
    have := bN _ hsn; push_cast at this ⊢; exact this
  refine XV.mono (K := 1 + (1 + ((12 * (2 * p + 1) + 8) + (1 + 1)))) ?_ (by omega) (fun _ h => h)
  refine XV.seq (XV.addI hL (x := o + 42) (a := o + 4) (b := o + 36) (u := ((2 ^ p : ℕ) : ℤ)) (v := c) (by omega)
    (by omega) (by omega) (by rw [hC.sp]; push_cast; ring) hc (bN _ (hle _ le_rfl)) (bN _ (hle _ bc)) b1) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.mulI hL (x := o + 42) (a := o + 42) (b := o + 6) (u := ((2 ^ p : ℕ) : ℤ) + c)
    (v := ((2 ^ (p - 1) : ℕ) : ℤ)) (by omega) (by omega) (by omega) (by slot) (by slot; rw [hC.sp1]; push_cast; ring)
    b1 (bN _ hle1) b2) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.mono (XV.isqrt hL (r := o + 42) (dd := o + 36) (q := o + 26) (t := o + 27) (n1 := o + 28)
    (z := o) (one := o + 1) (two := o + 2) (four := o + 3) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by simp) (n := (2 ^ p + c) * 2 ^ (p - 1))
    (by slot <;> (push_cast; ring)) (by slot; rw [hC.s0]; simp) (by slot; rw [hC.s1]; simp)
    (by slot; rw [hC.s2]; simp) (by slot; rw [hC.s4]; simp) hr4) (by omega) (fun σ' h => h)) fun σ3 ⟨h3, _, hF3⟩ => ?_
  have hcp : Nat.sqrt ((2 ^ p + c) * 2 ^ (p - 1)) = (gsm_chainq p (k + 1)).1 := by
    simp only [gsm_chainq]; rw [mul_comm]
  have hsp : s * 2 ^ (p - 1) / Nat.sqrt ((2 ^ p + c) * 2 ^ (p - 1)) = (gsm_chainq p (k + 1)).2 := by
    simp only [gsm_chainq]; rw [mul_comm (2 ^ (p - 1))]
  have F3 := FrameP.trans (((FrameP.refl (fun y => y = o + 20 ∨ (o + 26 ≤ y ∧ y ≤ o + 28) ∨ y = o + 36 ∨
      y = o + 37 ∨ y = o + 42) (fun _ => False) σ).setSc (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) _).setSc
      (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) _)
    (FrameP.of_frame hF3 (fun y hy => by simp at hy; omega) (by simp))
  have g37 : σ3.sc (o + 37) = ((s : ℕ) : ℤ) := by
    rw [hF3.2.1 (o + 37) (by simp), sc_setSc_ne _ (by omega), sc_setSc_ne _ (by omega)]; exact hs
  have g6 : σ3.sc (o + 6) = (((2 ^ (p - 1) : ℕ) : ℤ) : ℝ) := by
    rw [hF3.2.1 (o + 6) (by simp), sc_setSc_ne _ (by omega), sc_setSc_ne _ (by omega), hC.sp1]; push_cast; ring
  have g36 : σ3.sc (o + 36) = (((Nat.sqrt ((2 ^ p + c) * 2 ^ (p - 1)) : ℕ) : ℤ) : ℝ) := by
    rw [h3, Int.cast_natCast]
  refine XV.seq (XV.mulI hL (x := o + 20) (a := o + 37) (b := o + 6) (u := s) (v := ((2 ^ (p - 1) : ℕ) : ℤ))
    (by omega) (by omega) (by omega) g37 g6 (bN _ (hle _ bs)) (bN _ hle1) b3) fun σ4 e4 => ?_
  subst e4
  refine XV.mono (XV.divI hL (x := o + 37) (a := o + 20) (b := o + 36) (u := (s : ℤ) * ((2 ^ (p - 1) : ℕ) : ℤ))
    (v := ((Nat.sqrt ((2 ^ p + c) * 2 ^ (p - 1)) : ℕ) : ℤ)) (by omega) (by omega) (by omega) (by slot)
    (by slot) b3
    (bN _ (le_trans (Nat.sqrt_le_self _) hn))) le_rfl fun σ5 e5 => ?_
  subst e5
  refine ⟨by rw [sc_setSc_ne _ (by omega), sc_setSc_ne _ (by omega), g36, hcp],
    by rw [sc_setSc_eq, ← hsp]; push_cast; ring, ?_⟩
  exact (F3.setSc (Or.inl rfl) _).setSc (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) _


/-! ## The product loop: one turn, the loop -/

/-- The state of the product loop after `t` turns: `J`, `2^(B-1-t)`, `J div 2^(B-1-t)`, the pair, the chain. -/
def BmAng (o B Jn t : ℕ) (σ : Env d) : Prop :=
  σ.sc (o + 29) = ((Jn : ℕ) : ℤ) ∧ σ.sc (o + 30) = ((2 ^ (B - 1 - t) : ℕ) : ℤ) ∧
  σ.sc (o + 32) = ((Jn / 2 ^ (B - 1 - t) : ℕ) : ℤ) ∧
  σ.sc (o + 34) = ((gsm_prodq (gsm_prec B) B Jn t).1 : ℝ) ∧
  σ.sc (o + 35) = ((gsm_prodq (gsm_prec B) B Jn t).2 : ℝ) ∧
  σ.sc (o + 36) = (((gsm_chainq (gsm_prec B) t).1 : ℕ) : ℤ) ∧
  σ.sc (o + 37) = (((gsm_chainq (gsm_prec B) t).2 : ℕ) : ℤ)

/-- One turn of the product loop: the next digit of `J` (by halving `D`), the product with the factor of the chain
when the digit is `1`, the next factor of the chain. -/
def xbmTurn (L : Layout) (o : ℕ) : XCmd :=
  .seq (xsidiv L (o + 30) (o + 30) (o + 2))
  (.seq (xsidiv L (o + 31) (o + 29) (o + 30))
  (.seq (toX (VL.sop2 L .sub (o + 33) (o + 31) (o + 32)))
  (.seq (toX (VL.sop2 L .sub (o + 33) (o + 33) (o + 32)))
  (.seq (toX (VL.sop2 L .add (o + 32) (o + 31) o))
  (.seq (xifS L o (o + 33) (xbmCmul L o) .skip)
  (xbmChain L o))))))

theorem bm_digitZ (Jn k : ℕ) :
    ((Jn / 2 ^ k : ℕ) : ℤ) - ((Jn / 2 ^ (k + 1) : ℕ) : ℤ) - ((Jn / 2 ^ (k + 1) : ℕ) : ℤ) =
      ((if Jn.testBit k then 1 else 0 : ℕ) : ℤ) := by
  have h1 := bm_digit Jn k
  have h2 : 2 * (Jn / 2 ^ (k + 1)) ≤ Jn / 2 ^ k := by
    rw [pow_succ, ← Nat.div_div_eq_div_mul]; exact Nat.mul_div_le _ _
  split_ifs at h1 ⊢ <;> omega

theorem XV.bmTurn {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {o on B : ℕ}
    (hS : o + 43 ≤ L.NS) (hC : BmC o on B σ) {Jn t : ℕ} (hJ : Jn < 2 ^ B) (ht : t + 1 < B)
    (hA : BmAng o B Jn t σ) (hℓ : 4 * gsm_prec B + 4 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xbmTurn L o) σ (24 * gsm_prec B + 38) (fun σ' => BmAng o B Jn (t + 1) σ' ∧
      FrameP (fun y => y = o + 20 ∨ (o + 26 ≤ y ∧ y ≤ o + 28) ∨ (o + 30 ≤ y ∧ y ≤ o + 39) ∨ y = o + 42)
        (fun _ => False) σ σ') := by
  obtain ⟨hp4, -⟩ := bm_prec B
  obtain ⟨a29, a30, a32, a34, a35, a36, a37⟩ := hA
  set p := gsm_prec B
  obtain ⟨k, hk⟩ : ∃ k, B - 1 - t = k + 1 := ⟨B - 2 - t, by omega⟩
  have hk' : B - 1 - (t + 1) = k := by omega
  rw [hk] at a30 a32
  have hkB : k + 1 ≤ B := by omega
  have hpB : (2 : ℤ) ^ B ≤ 2 ^ (2 * p) := pow_le_pow_right₀ (by norm_num) (by omega)
  have bb : ∀ z : ℤ, 0 ≤ z → z ≤ 2 ^ B → |z| < 2 ^ ℓ := fun z h0 h1 => absI_lt h0 h1 (by omega)
  have hk1 : ((2 ^ (k + 1) : ℕ) : ℤ) ≤ 2 ^ B := by
    have : 2 ^ (k + 1) ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) hkB
    exact_mod_cast this
  have hk0 : ((2 ^ k : ℕ) : ℤ) ≤ 2 ^ B := by
    have : 2 ^ k ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast this
  have hJz : ((Jn : ℕ) : ℤ) ≤ 2 ^ B := by exact_mod_cast hJ.le
  have hdv : ∀ m, ((Jn / 2 ^ m : ℕ) : ℤ) ≤ 2 ^ B := fun m => by
    have : Jn / 2 ^ m ≤ 2 ^ B := le_trans (Nat.div_le_self _ _) hJ.le
    exact_mod_cast this
  have hD : (((2 ^ (k + 1) : ℕ) : ℤ) / 2) = ((2 ^ k : ℕ) : ℤ) := by push_cast; rw [pow_succ]; simp
  have hA2 : (((Jn : ℕ) : ℤ) / ((2 ^ k : ℕ) : ℤ)) = ((Jn / 2 ^ k : ℕ) : ℤ) := by push_cast; rfl
  set dg : ℕ := if Jn.testBit k then 1 else 0 with hdg
  have hdg1 : dg ≤ 1 := by rw [hdg]; split_ifs <;> omega
  have hdig : ((Jn / 2 ^ k : ℕ) : ℤ) - ((Jn / 2 ^ (k + 1) : ℕ) : ℤ) - ((Jn / 2 ^ (k + 1) : ℕ) : ℤ) = ((dg : ℕ) : ℤ) :=
    bm_digitZ Jn k
  have hz1 : 0 ≤ ((Jn / 2 ^ k : ℕ) : ℤ) - ((Jn / 2 ^ (k + 1) : ℕ) : ℤ) := by
    linarith [Nat.cast_nonneg (α := ℤ) dg, Nat.cast_nonneg (α := ℤ) (Jn / 2 ^ (k + 1))]
  have hz2 : ((Jn / 2 ^ k : ℕ) : ℤ) - ((Jn / 2 ^ (k + 1) : ℕ) : ℤ) ≤ 2 ^ B := by
    linarith [hdv k, Nat.cast_nonneg (α := ℤ) (Jn / 2 ^ (k + 1))]
  have h2B : (2 : ℤ) ≤ 2 ^ B := by
    have : (2 : ℤ) ^ 1 ≤ 2 ^ B := pow_le_pow_right₀ (by norm_num) (by omega)
    simpa using this
  refine XV.mono (K := 1 + (1 + (1 + (1 + (1 + (9 + (24 * p + 24))))))) ?_ (by omega) (fun _ h => h)
  refine XV.seq (XV.divI hL (x := o + 30) (a := o + 30) (b := o + 2) (u := ((2 ^ (k + 1) : ℕ) : ℤ)) (v := 2)
    (by omega) (by omega) (by omega) a30 hC.s2 (bb _ (Nat.cast_nonneg _) hk1) (bb _ (by norm_num) h2B)) fun σ1 e1 => ?_
  subst e1
  rw [hD]
  refine XV.seq (XV.divI hL (x := o + 31) (a := o + 29) (b := o + 30) (u := ((Jn : ℕ) : ℤ))
    (v := ((2 ^ k : ℕ) : ℤ)) (by omega) (by omega) (by omega) (by slot) (by slot) (bb _ (Nat.cast_nonneg _) hJz)
    (bb _ (Nat.cast_nonneg _) hk0)) fun σ2 e2 => ?_
  subst e2
  rw [hA2]
  refine XV.seq (XV.subI hL (x := o + 33) (a := o + 31) (b := o + 32) (u := ((Jn / 2 ^ k : ℕ) : ℤ))
    (v := ((Jn / 2 ^ (k + 1) : ℕ) : ℤ)) (by omega) (by omega) (by omega) (by slot) (by slot)
    (bb _ (Nat.cast_nonneg _) (hdv _)) (bb _ (Nat.cast_nonneg _) (hdv _))
    (bb _ hz1 hz2)) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.subI hL (x := o + 33) (a := o + 33) (b := o + 32)
    (u := ((Jn / 2 ^ k : ℕ) : ℤ) - ((Jn / 2 ^ (k + 1) : ℕ) : ℤ)) (v := ((Jn / 2 ^ (k + 1) : ℕ) : ℤ)) (by omega)
    (by omega) (by omega) (by slot) (by slot) (bb _ hz1 hz2)
    (bb _ (Nat.cast_nonneg _) (hdv _)) (by rw [hdig]; exact bb _ (Nat.cast_nonneg _) (by
      have : (1 : ℤ) ≤ 2 ^ B := one_le_pow₀ (by norm_num)
      have : (dg : ℤ) ≤ 1 := by exact_mod_cast hdg1
      omega))) fun σ4 e4 => ?_
  subst e4
  rw [hdig]
  refine XV.seq (XV.addI hL (x := o + 32) (a := o + 31) (b := o) (u := ((Jn / 2 ^ k : ℕ) : ℤ)) (v := 0) (by omega)
    (by omega) (by omega) (by slot) (by slot; exact hC.s0) (bb _ (Nat.cast_nonneg _) (hdv _))
    (bb _ le_rfl (pow_nonneg (by norm_num) _)) (bb _ (by rw [add_zero]; exact Nat.cast_nonneg _) (by rw [add_zero]; exact hdv k))) fun σ5 e5 => ?_
  have F5 : FrameP (fun y => o + 30 ≤ y ∧ y ≤ o + 33) (fun _ => False) σ σ5 := by
    rw [e5]
    exact (((((FrameP.refl _ _ σ).setSc ⟨le_rfl, by omega⟩ _).setSc ⟨by omega, by omega⟩ _).setSc
      ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _).setSc ⟨by omega, by omega⟩ _
  have f30 : σ5.sc (o + 30) = ((2 ^ k : ℕ) : ℤ) := by rw [e5]; slot
  have f32 : σ5.sc (o + 32) = ((Jn / 2 ^ k : ℕ) : ℤ) := by rw [e5]; slot <;> simp
  have f33 : σ5.sc (o + 33) = ((dg : ℕ) : ℤ) := by rw [e5]; slot
  have f0 : σ5.sc o = ((0 : ℤ) : ℝ) := by rw [F5.2.1 o (by omega)]; exact hC.s0
  clear e5
  have C5 := hC.frame F5 (fun y hy => by omega) (fun _ h => h.elim)
  have hcb := fun j => bm_chainq_le p j (by omega)
  obtain ⟨bc, bs⟩ := hcb t
  have hpq : gsm_prodq p B Jn (t + 1) = if Jn.testBit k then gsm_cmulq p (gsm_prodq p B Jn t)
      (((gsm_chainq p t).1 : ℤ), ((gsm_chainq p t).2 : ℤ)) else gsm_prodq p B Jn t := by
    rw [gsm_prodq, hk']
  obtain ⟨bz1, bz2⟩ := bm_prodq_le p B Jn hcb t
  have hz2 : (2 : ℤ) ^ (p + t + 1) ≤ 2 ^ (2 * p) := pow_le_pow_right₀ (by norm_num) (by omega)
  have b0 : |((0 : ℤ) : ℝ)| < 2 ^ ℓ := by simp
  have bdg : |(((dg : ℕ) : ℤ) : ℝ)| < 2 ^ ℓ := XV.abs_int_lt (bb _ (Nat.cast_nonneg _) (by
    have : (1 : ℤ) ≤ 2 ^ B := one_le_pow₀ (by norm_num)
    have : (dg : ℤ) ≤ 1 := by exact_mod_cast hdg1
    omega))
  refine XV.seq (Q₁ := fun σ' => σ'.sc (o + 34) = ((gsm_prodq p B Jn (t + 1)).1 : ℝ) ∧
      σ'.sc (o + 35) = ((gsm_prodq p B Jn (t + 1)).2 : ℝ) ∧
      FrameP (fun y => y = o + 20 ∨ y = o + 34 ∨ y = o + 35 ∨ y = o + 38 ∨ y = o + 39) (fun _ => False) σ5 σ')
    ?_ fun σ6 ⟨g34, g35, F6⟩ => ?_
  · by_cases hb : Jn.testBit k
    · have hd1 : dg = 1 := by rw [hdg, if_pos hb]
      refine XV.mono (XV.ifS_t hL (by omega) (by omega) (by rw [f0]; exact b0) (by rw [f33]; exact bdg)
        (by rw [f0, f33, hd1]; norm_num) (XV.bmCmul hL hS C5 (zx := (gsm_prodq p B Jn t).1)
        (zy := (gsm_prodq p B Jn t).2) (by rw [F5.2.1 _ (by omega), a34]) (by rw [F5.2.1 _ (by omega), a35])
        (by rw [F5.2.1 _ (by omega), a36]) (by rw [F5.2.1 _ (by omega), a37]) (by show _ ≤ (2 : ℤ) ^ (2 * p); omega) (by show _ ≤ (2 : ℤ) ^ (2 * p); omega) bc bs hℓ))
        (by omega) fun σ' ⟨h1, h2, h3⟩ => ⟨by rw [h1, hpq, if_pos hb], by rw [h2, hpq, if_pos hb], h3⟩
    · have hd0 : dg = 0 := by rw [hdg, if_neg hb]
      refine XV.mono (XV.ifS_f hL (by omega) (by omega) (by rw [f0]; exact b0) (by rw [f33]; exact bdg)
        (by rw [f0, f33, hd0]; norm_num) (XV.skip _)) (by omega) fun σ' e => ?_
      subst e
      exact ⟨by rw [F5.2.1 _ (by omega), a34, hpq, if_neg hb], by rw [F5.2.1 _ (by omega), a35, hpq, if_neg hb],
        FrameP.refl _ _ _⟩
  have C6 := C5.frame F6 (fun y hy => by omega) (fun _ h => h.elim)
  refine XV.mono (XV.bmChain hL hS C6 (k := t) (by rw [F6.2.1 _ (by omega), F5.2.1 _ (by omega), a36])
    (by rw [F6.2.1 _ (by omega), F5.2.1 _ (by omega), a37]) hℓ) le_rfl fun σ7 ⟨h36, h37, F7⟩ => ?_
  have F := (F5.mono (S' := fun y => y = o + 20 ∨ (o + 26 ≤ y ∧ y ≤ o + 28) ∨ (o + 30 ≤ y ∧ y ≤ o + 39) ∨
    y = o + 42) (N' := fun _ => False) (fun y hy => by omega) (fun _ h => h)).trans
    ((F6.mono (fun y hy => by omega) (fun _ h => h)).trans (F7.mono (fun y hy => by omega) (fun _ h => h)))
  refine ⟨⟨by rw [F.2.1 _ (by omega), a29], ?_, ?_, ?_, ?_, h36, h37⟩, F⟩
  · rw [F7.2.1 _ (by omega), F6.2.1 _ (by omega), f30, hk']
  · rw [F7.2.1 _ (by omega), F6.2.1 _ (by omega), f32, hk']
  · rw [F7.2.1 _ (by omega), g34]
  · rw [F7.2.1 _ (by omega), g35]


/-- The product loop: `D = 2^(B-1)`, the top digit of `J`, `Z = (±2^p, 0)`, the chain at `(0, 2^p)`, then `B - 1`
turns, the counter at `on + 10`. -/
def xbmAngle (L : Layout) (o on : ℕ) : XCmd :=
  .seq (xsidiv L (o + 30) (o + 8) (o + 2))
  (.seq (xsidiv L (o + 32) (o + 29) (o + 30))
  (.seq (toX (VL.sop2 L .add (o + 38) (o + 32) (o + 32)))
  (.seq (toX (VL.sop2 L .sub (o + 38) (o + 1) (o + 38)))
  (.seq (toX (VL.sop2 L .mul (o + 34) (o + 4) (o + 38)))
  (.seq (toX (VL.sop2 L .add (o + 35) o o))
  (.seq (toX (VL.sop2 L .add (o + 36) o o))
  (.seq (toX (VL.sop2 L .add (o + 37) (o + 4) o))
  (xforN (on + 10) (on + 11) (on + 4) (xbmTurn L o)))))))))

theorem XV.bmAngle {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {o on B : ℕ}
    (hS : o + 43 ≤ L.NS) (hN : on + 12 ≤ L.NN) (hC : BmC o on B σ) (hB : 1 ≤ B) {Jn : ℕ}
    (hJv : σ.sc (o + 29) = ((Jn : ℕ) : ℤ)) (hJ : Jn < 2 ^ B) (hℓa : 4 * gsm_prec B + 2 < 2 ^ ℓa)
    (hℓ : 4 * gsm_prec B + 4 ≤ ℓ) :
    XRunsB L X ℓa ℓ (xbmAngle L o on) σ (8 + ((B - 1) * (24 * gsm_prec B + 38 + 3) + 3)) (fun σ' =>
      σ'.sc (o + 34) = ((gsm_prodq (gsm_prec B) B Jn (B - 1)).1 : ℝ) ∧
      σ'.sc (o + 35) = ((gsm_prodq (gsm_prec B) B Jn (B - 1)).2 : ℝ) ∧
      FrameP (fun y => y = o + 20 ∨ (o + 26 ≤ y ∧ y ≤ o + 28) ∨ (o + 30 ≤ y ∧ y ≤ o + 39) ∨ y = o + 42)
        (fun j => j = on + 10) σ σ') := by
  obtain ⟨hp4, -⟩ := bm_prec B
  set p := gsm_prec B
  have hpB : (2 : ℤ) ^ B ≤ 2 ^ (2 * p) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hpp : (2 : ℤ) ^ p ≤ 2 ^ (2 * p) := pow_le_pow_right₀ (by norm_num) (by omega)
  have bb : ∀ z : ℤ, -2 ^ (2 * p) ≤ z → z ≤ 2 ^ (2 * p) → |z| < 2 ^ ℓ := fun z h0 h1 => absI_lt' h0 h1 (by omega)
  have h0p : (0 : ℤ) ≤ 2 ^ p := pow_nonneg (by norm_num) _
  have h0B : (0 : ℤ) ≤ 2 ^ B := pow_nonneg (by norm_num) _
  have h02 : (0 : ℤ) ≤ 2 ^ (2 * p) := pow_nonneg (by norm_num) _
  have h1B : (2 : ℤ) ≤ 2 ^ B := by
    have : (2 : ℤ) ^ 1 ≤ 2 ^ B := pow_le_pow_right₀ (by norm_num) hB
    simpa using this
  have hD0 : (2 : ℤ) ^ B / 2 = ((2 ^ (B - 1) : ℕ) : ℤ) := by
    obtain ⟨b, rfl⟩ : ∃ b, B = b + 1 := ⟨B - 1, by omega⟩
    push_cast; rw [pow_succ]; simp
  have hJz : ((Jn : ℕ) : ℤ) ≤ 2 ^ B := by exact_mod_cast hJ.le
  have hA0 : (((Jn : ℕ) : ℤ) / ((2 ^ (B - 1) : ℕ) : ℤ)) = ((Jn / 2 ^ (B - 1) : ℕ) : ℤ) := by push_cast; rfl
  have htop := bm_top_digit B Jn hB hJ
  set a0 := Jn / 2 ^ (B - 1) with ha0
  have ha01 : a0 ≤ 1 := by rw [htop]; split_ifs <;> omega
  have ha0z : ((a0 : ℕ) : ℤ) ≤ 1 := by exact_mod_cast ha01
  have ha00 : (0 : ℤ) ≤ ((a0 : ℕ) : ℤ) := Nat.cast_nonneg _
  have hD1 : ((2 ^ (B - 1) : ℕ) : ℤ) ≤ 2 ^ B := by
    have : 2 ^ (B - 1) ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast this
  have hZ0 : (2 : ℤ) ^ p * (1 - ((a0 : ℕ) + (a0 : ℕ) : ℤ)) = (gsm_prodq p B Jn 0).1 := by
    simp only [gsm_prodq]
    rw [htop]; split_ifs <;> push_cast <;> ring
  refine XV.mono (K := 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + ((B - 1) * (24 * p + 38 + 3) + 3))))))))) ?_
    (by omega) (fun _ h => h)
  refine XV.seq (XV.divI hL (x := o + 30) (a := o + 8) (b := o + 2) (u := 2 ^ B) (v := 2) (by omega) (by omega)
    (by omega) hC.sB hC.s2 (bb _ (by omega) (by omega)) (bb _ (by omega) (by omega))) fun σ1 e1 => ?_
  subst e1
  rw [hD0]
  refine XV.seq (XV.divI hL (x := o + 32) (a := o + 29) (b := o + 30) (u := ((Jn : ℕ) : ℤ))
    (v := ((2 ^ (B - 1) : ℕ) : ℤ)) (by omega) (by omega) (by omega) (by slot) (by slot) (bb _ (by omega) (by omega))
    (bb _ (by omega) (by omega))) fun σ2 e2 => ?_
  subst e2
  rw [hA0]
  refine XV.seq (XV.addI hL (x := o + 38) (a := o + 32) (b := o + 32) (u := ((a0 : ℕ) : ℤ)) (v := ((a0 : ℕ) : ℤ))
    (by omega) (by omega) (by omega) (by slot) (by slot) (bb _ (by omega) (by omega)) (bb _ (by omega) (by omega))
    (bb _ (by omega) (by omega))) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.subI hL (x := o + 38) (a := o + 1) (b := o + 38) (u := 1) (v := ((a0 : ℕ) : ℤ) + (a0 : ℕ))
    (by omega) (by omega) (by omega) (by slot; exact hC.s1) (by slot) (bb _ (by omega) (by omega))
    (bb _ (by omega) (by omega)) (bb _ (by omega) (by omega))) fun σ4 e4 => ?_
  subst e4
  have hm : |(2 : ℤ) ^ p * (1 - ((a0 : ℕ) + (a0 : ℕ) : ℤ))| ≤ 2 ^ p := by
    rw [abs_mul, abs_of_nonneg h0p]
    have : |(1 - ((a0 : ℕ) + (a0 : ℕ) : ℤ))| ≤ 1 := by rw [abs_le]; constructor <;> omega
    exact (mul_le_mul_of_nonneg_left this h0p).trans (le_of_eq (mul_one _))
  refine XV.seq (XV.mulI hL (x := o + 34) (a := o + 4) (b := o + 38) (u := 2 ^ p)
    (v := 1 - ((a0 : ℕ) + (a0 : ℕ) : ℤ)) (by omega) (by omega) (by omega) (by slot; exact hC.sp) (by slot)
    (bb _ (by omega) (by omega)) (bb _ (by omega) (by omega))
    (bb _ (by have := neg_abs_le ((2 : ℤ) ^ p * (1 - ((a0 : ℕ) + (a0 : ℕ) : ℤ))); omega)
      (by have := le_abs_self ((2 : ℤ) ^ p * (1 - ((a0 : ℕ) + (a0 : ℕ) : ℤ))); omega))) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.addI hL (x := o + 35) (a := o) (b := o) (u := 0) (v := 0) (by omega) (by omega) (by omega)
    (by slot; exact hC.s0) (by slot; exact hC.s0) (bb _ (by omega) (by omega)) (bb _ (by omega) (by omega))
    (bb _ (by omega) (by omega))) fun σ6 e6 => ?_
  subst e6
  refine XV.seq (XV.addI hL (x := o + 36) (a := o) (b := o) (u := 0) (v := 0) (by omega) (by omega) (by omega)
    (by slot; exact hC.s0) (by slot; exact hC.s0) (bb _ (by omega) (by omega)) (bb _ (by omega) (by omega))
    (bb _ (by omega) (by omega))) fun σ7 e7 => ?_
  subst e7
  refine XV.seq (XV.addI hL (x := o + 37) (a := o + 4) (b := o) (u := 2 ^ p) (v := 0) (by omega) (by omega)
    (by omega) (by slot; exact hC.sp) (by slot; exact hC.s0) (bb _ (by omega) (by omega))
    (bb _ (by omega) (by omega)) (bb _ (by omega) (by omega))) fun σ8 e8 => ?_
  have F8 : FrameP (fun y => y = o + 20 ∨ (o + 26 ≤ y ∧ y ≤ o + 28) ∨ (o + 30 ≤ y ∧ y ≤ o + 39) ∨ y = o + 42)
      (fun j => j = on + 10) σ σ8 := by
    rw [e8]
    exact ((((((((FrameP.refl _ _ σ).setSc (Or.inr (Or.inr (Or.inl ⟨le_rfl, by omega⟩))) _).setSc
      (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))) _).setSc (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))) _).setSc
      (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))) _).setSc (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))) _).setSc
      (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))) _).setSc (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))) _).setSc
      (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))) _
  have A8 : BmAng o B Jn 0 σ8 := by
    rw [e8]
    refine ⟨by slot, by slot <;> rw [Nat.sub_zero], by slot <;> rw [Nat.sub_zero], by slot <;> rw [← hZ0],
      by slot <;> simp [gsm_prodq],
      by slot <;> simp [gsm_chainq], by slot <;> simp [gsm_chainq] <;> rfl⟩
  have n8 : ∀ j, σ8.nat j = σ.nat j := fun j => by rw [e8]; rfl
  clear e8
  refine XV.forN hL (i := on + 10) (n := on + 11) (one := on + 4) (by omega) (by omega) (by omega) (by omega)
    (by omega) (B - 1) (24 * p + 38) (by omega)
    (fun t σ' => BmAng o B Jn t σ' ∧
      FrameP (fun y => y = o + 20 ∨ (o + 26 ≤ y ∧ y ≤ o + 28) ∨ (o + 30 ≤ y ∧ y ≤ o + 39) ∨ y = o + 42)
        (fun j => j = on + 10) σ σ') σ8 (by rw [n8, hC.nBm]) (by rw [n8, hC.n1]) ⟨A8, F8.setNat rfl _⟩ ?_
    |> fun h => XV.mono h le_rfl fun σ' ⟨⟨hA, hF⟩, _⟩ => ⟨hA.2.2.2.1, hA.2.2.2.2.1, hF⟩
  intro t ht σ' ⟨hA, hF⟩ hi hn h1
  have C' := hC.frame hF (fun y hy => by omega) (fun _ h => h)
  refine XV.mono (XV.bmTurn hL hS C' hJ (by omega) hA hℓ) le_rfl fun σ'' ⟨hA', hF'⟩ => ?_
  refine ⟨by rw [hF'.1 _ id, hi], by rw [hF'.1 _ id, hn], by rw [hF'.1 _ id, h1], hA', ?_⟩
  exact (hF.trans (hF'.mono (fun y hy => hy) (fun _ h => h.elim))).setNat rfl _

end AdversarialBco.Bit.Transfer
