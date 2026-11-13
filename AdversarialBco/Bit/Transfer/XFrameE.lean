/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XFrameEL
public import AdversarialBco.Bit.Transfer.XEllRoute

@[expose] public section

/-!
# Procedure FRAME for `d ≥ 2` on the machine

ELL-F (`frEll`, Bit/RoutQ.lean) on the machine, with the setup of ELL-R at `j = 1`: `M̂` and `e_R` (`XV.frE0`),
`R̄ = 2^{e_R}` into the slot `c`, then ELL-R's constants with `lg R̄ = e_R` and `λ = e_R + 1` (`XV.ellS0`,
`XV.ellSetR`, `XV.ellSlots`), so that `p = frP d`, `q = frQ d e_R`, `N = frN d e_R` and the caps are those of `frEll`;
the start state `Â = 2^{p + 2 e_R} I`, `â = 0` (`XV.ellArr`); the loop (`XV.frEllLoop`); the output into the array
`aW` in the form of the play leaf. The layout of ELL-R: `P = o + 3`, `u = o + 15`, `c = o + 75`, `n0 = rE + 1`,
`a0 = aW + 2`.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.RQ Matrix

variable {d : ℕ}

/-! ## The output -/

/-- The point of a result of the loop: `â / 2^p`, or `0`. -/
def frOutQ (p : ℕ) : Option (Fin d → ℤ) → Fin d → ℚ
  | some a => fun i => (a i : ℚ) / 2 ^ p
  | none => 0

/-- The output into the array `aW`: on a returned point (`2` in `P + 8`) `2^p` (slot `P + 3`) into the cell `0` and `â`
(array `a0 + 1`) into the cells `1, ..., d`; else `1` and zeros. The register `n0 + 11` walks the cells, `n0 + 13`
counts. -/
def xfrOut (L : Layout) (B : PrBlk) (P u a0 n0 : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst (n0 + 11) 0)))
  (xifS L (u + 1) (P + 8)
    (.seq (toX (VL.aset L B.aW (n0 + 11) (P + 3)))
      (.seq (.prim (.frag (.nconst (n0 + 11) 1)))
        (xmapE L u (u + 13) (.arr (a0 + 1) (n0 + 13)) B.aW (n0 + 11) (n0 + 4) (n0 + 13) B.rd (n0 + 4))))
    (.seq (toX (VL.aset L B.aW (n0 + 11) (u + 1)))
      (.seq (.prim (.frag (.nconst (n0 + 11) 1)))
        (xmapE L u (u + 13) (.sc u) B.aW (n0 + 11) (n0 + 4) (n0 + 13) B.rd (n0 + 4)))))

theorem vextZ_lt {x : Fin d → ℤ} {k : ℕ} (hk : k < d) : vextZ x k = x ⟨k, hk⟩ := by simp [vextZ, hk]

/-- The units of `xfrOut`. -/
def frOutU (d : ℕ) : ℕ := 1 + ((2 + (1 + (d * (2 + 6) + 3))) + 2)

set_option maxHeartbeats 4000000 in
/-- The rule of `xfrOut`. -/
theorem XV.frOut {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : PrBlk}
    {P u a0 n0 F p s : ℕ} {capa : ℤ} {r : Option (Fin d → ℤ)} (hd : 1 ≤ d) (hPu : P + 9 ≤ u)
    (hS : u + 14 ≤ L.NS) (hwa : B.aW + 2 ≤ a0) (hA : a0 + 2 ≤ L.NA) (hrd : B.rd < n0) (hN : n0 + 14 ≤ L.NN)
    (hdv : σ.nat B.rd = d) (hone : σ.nat (n0 + 4) = 1) (hz : σ.sc u = 0) (h1 : σ.sc (u + 1) = 1)
    (hp : σ.sc (P + 3) = ((2 ^ p : ℤ) : ℝ)) (hout : FrLoopOut P a0 capa r σ) (bca : capa ≤ 2 ^ F)
    (hF : F + 2 < ℓ) (hpl : p < ℓ) (hFs : F < s) (hps : p < s) :
    XRunsB L X ℓa ℓ (xfrOut L B P u a0 n0) σ (frOutU d) (fun σ' =>
      PtIn σ' B.aW s (frOutQ p r) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => u + 13 ≤ y) (fun j => j = n0 + 11 ∨ j = n0 + 13) (fun b _ => b = B.aW) σ σ') := by
  have h0 : |(0 : ℝ)| < 2 ^ ℓ := by simp only [abs_zero]; positivity
  have h1' : |(1 : ℝ)| < 2 ^ ℓ := by rw [abs_one]; exact one_lt_pow₀ (by norm_num) (by omega)
  have h2' : |(2 : ℝ)| < 2 ^ ℓ := by
    rw [abs_two]
    have := pow_lt_pow_right₀ (show (1 : ℝ) < 2 by norm_num) (show 1 < ℓ by omega)
    simpa using this
  have hsa : 1 < 2 ^ ℓa := by have := hL.1; omega
  have hda := asz_lt hL (show B.aW < L.NA by omega)
  unfold asz at hda
  have hdd : d + 1 ≤ d * d + d := by nlinarith
  have hne : [n0 + 11, n0 + 13, B.rd, n0 + 4].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil, and_true,
      not_false_eq_true]; omega
  unfold frOutU
  refine XV.seq (XV.nconstA hL (i := n0 + 11) (by omega) 0 (by positivity)) fun σ1 ⟨v1, d1, G1⟩ => ?_
  have e1 : ∀ j, j ≠ n0 + 11 → σ1.nat j = σ.nat j := fun j h => G1.1 j h
  have s1 : ∀ y, σ1.sc y = σ.sc y := fun y => G1.2.1 y id
  have a1 : ∀ b k, σ1.arr b k = σ.arr b k := fun b k => G1.2.2.1 b k id
  -- the cells `1, ..., d` from an expression, after the cell `0`
  have tail : ∀ (σ2 : Env d) (D : ℤ) (e : IE) (x : Fin d → ℤ) (K : ℕ), e.units = K →
      σ2.arr B.aW 0 = D → σ2.nat (n0 + 4) = 1 → σ2.nat B.rd = d → σ2.sc u = 0 → σ2.draws = σ.draws →
      FrameA (fun y => u + 13 ≤ y) (fun j => j = n0 + 11 ∨ j = n0 + 13) (fun b _ => b = B.aW) σ σ2 →
      e.WF L (u + 13) → e.scr = 0 → e.top F < ℓ →
      (∀ k < d, ∀ σ' : Env d, FrameA (fun y => u + 13 ≤ y) (fun j => j = n0 + 13 ∨ j = n0 + 11)
        (fun b c => b = B.aW ∧ ∃ k' < k, c = 1 + 1 * k') σ2 σ' → σ'.nat (n0 + 13) = k →
        e.Leaves F σ' ∧ e.eval σ' = vextZ x k) →
      XRunsB L X ℓa ℓ (.seq (.prim (.frag (.nconst (n0 + 11) 1)))
        (xmapE L u (u + 13) e B.aW (n0 + 11) (n0 + 4) (n0 + 13) B.rd (n0 + 4))) σ2 (1 + (d * (K + 6) + 3))
        (fun σ' => (σ'.arr B.aW 0 = D ∧ ∀ j : Fin d, σ'.arr B.aW (j + 1) = x j) ∧ σ'.draws = σ.draws ∧
          FrameA (fun y => u + 13 ≤ y) (fun j => j = n0 + 11 ∨ j = n0 + 13) (fun b _ => b = B.aW) σ σ') := by
    intro σ2 D e x K hK hD2 o2 r2 z2 d2 G2 hw hsc htop hFe
    refine XV.seq (XV.nconstA hL (i := n0 + 11) (by omega) 1 hsa) fun σ3 ⟨v3, d3, G3⟩ => ?_
    have e3 : ∀ j, j ≠ n0 + 11 → σ3.nat j = σ2.nat j := fun j h => G3.1 j h
    rw [← hK]
    refine XV.mono (XV.mapEx (E := F) (N := d) (base := 1) (st := 1) (F := vextZ x) hL (z := u) (t := u + 13)
      (e := e) (aB := B.aW) (nr := n0 + 11) (nst := n0 + 4) (nk := n0 + 13) (nn := B.rd) (none := n0 + 4)
      hw (by omega) (by rw [hsc]; omega) (by rw [G3.2.1 _ id, z2]) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) hne (by omega) (by omega) (by rw [e3 _ (by omega), r2])
      (by rw [e3 _ (by omega), o2]) v3 (by rw [e3 _ (by omega), o2]) one_pos (fun k hk => by unfold asz; omega)
      (by omega) (by omega) hsa htop (fun k hk σ' hF _ hk' _ => hFe k hk σ' ?_ hk')) le_rfl
      fun σ4 ⟨z4, _, d4, F4⟩ => ?_
    · exact (G3.mono (S' := fun y => u + 13 ≤ y) (N' := fun j => j = n0 + 13 ∨ j = n0 + 11)
        (Ar' := fun b c => b = B.aW ∧ ∃ k' < k, c = 1 + 1 * k') (fun _ h => h.elim) (fun j h => Or.inr h)
        (fun _ _ h => h.elim)).trans hF
    · refine ⟨⟨?_, fun j => ?_⟩, by rw [d4, d3, d2], ?_⟩
      · rw [F4.2.2.1 _ _ (fun ⟨_, k', _, h⟩ => by omega), G3.2.2.1 _ _ id, hD2]
      · have := z4 j j.isLt
        rw [show 1 + 1 * (j : ℕ) = j + 1 by ring] at this
        rw [this, vextZ_lt j.isLt]
      · exact (G2.trans (G3.mono (fun _ h => h.elim) (fun j h => Or.inl h) (fun _ _ h => h.elim))).trans
          (F4.mono (fun y h => h) (fun j h => by rcases h with h | h <;> simp [h]) (fun b c h => h.1))
  have bxs : ∀ x : Fin d → ℤ, (∀ k, |x k| ≤ capa) → ∀ k, |x k| < 2 ^ s := fun x bx k =>
    (bx k).trans_lt (bca.trans_lt (pow_lt_pow_right₀ (by norm_num) hFs))
  rcases hout with ⟨h8, x, hr, hx, bx⟩ | ⟨h8, hr⟩
  · -- a returned point
    subst hr
    have b8 : |σ1.sc (P + 8)| < 2 ^ ℓ := by rw [s1, h8]; exact h2'
    have bp : |σ1.sc (P + 3)| < 2 ^ ℓ := by
      rw [s1, hp]; exact abs_cast_lt (by rw [abs_of_pos (by positivity)]) hpl
    refine XV.mono (XV.ifS_t (K := 2 + (1 + (d * (2 + 6) + 3))) hL (by omega) (by omega)
      (by rw [s1, h1]; exact h1') b8 (by rw [s1, s1, h1, h8]; norm_num) ?_) (by omega) (fun _ h => h)
    refine XV.seq (XV.aset hL (a := B.aW) (i := n0 + 11) (x := P + 3) (by omega) (by omega) (by omega)
      (by rw [v1]; unfold asz; omega) bp) fun σ2 e2 => ?_
    subst e2
    have hD2 : (σ1.setArr B.aW (σ1.nat (n0 + 11)) (σ1.sc (P + 3))).arr B.aW 0 = ((2 ^ p : ℤ) : ℝ) := by
      simp [v1, s1, hp]
    refine XV.mono (tail _ (2 ^ p) (.arr (a0 + 1) (n0 + 13)) x 2 rfl hD2 (by simp [e1 (n0 + 4) (by omega), hone])
      (by simp [e1 B.rd (by omega), hdv]) (by simp [s1, hz]) (by simp [d1])
      ((G1.mono (S' := fun y => u + 13 ≤ y) (N' := fun j => j = n0 + 11 ∨ j = n0 + 13)
        (Ar' := fun b _ => b = B.aW) (fun _ h => h.elim) (fun j h => Or.inl h) (fun _ _ h => h.elim)).setArr
        (b := B.aW) rfl _)
      (by simp only [IE.WF]; omega) rfl (by simp only [IE.top]; omega) fun k hk σ' hF hk' => ?_) le_rfl ?_
    · have ha : σ'.arr (a0 + 1) k = ((vextZ x k : ℤ) : ℝ) := by
        rw [hF.2.2.1 _ _ (fun h => by omega)]
        simp only [Env.setArr_arr, show a0 + 1 ≠ B.aW by omega, false_and, ite_false]
        rw [a1]
        have := hx ⟨k, hk⟩
        simp only at this
        rw [this, vextZ_lt hk]
      refine ⟨⟨by rw [hk']; unfold asz; omega, vextZ x k, by rw [hk', ha], ?_⟩, by simp only [IE.eval]; rw [hk', ha]⟩
      rw [vextZ_lt hk]; exact (bx _).trans bca
    · rintro σ' ⟨⟨hD, hj⟩, d', F'⟩
      exact ⟨⟨2 ^ p, by positivity, pow_lt_pow_right₀ (by norm_num) hps, hD,
        fun j => ⟨x j, bxs x bx j, hj j, by simp [frOutQ]⟩⟩, d', F'⟩
  · -- no point
    subst hr
    have b8 : |σ1.sc (P + 8)| < 2 ^ ℓ := by rw [s1]; rcases h8 with h | h <;> rw [h] <;> assumption
    have h8' : ¬ σ1.sc (u + 1) < σ1.sc (P + 8) := by
      rw [s1, s1, h1]; rcases h8 with h | h <;> rw [h] <;> norm_num
    refine XV.mono (XV.ifS_f (K := 2 + (1 + (d * (1 + 6) + 3))) hL (by omega) (by omega)
      (by rw [s1, h1]; exact h1') b8 h8' ?_) (by nlinarith) (fun _ h => h)
    refine XV.seq (XV.aset hL (a := B.aW) (i := n0 + 11) (x := u + 1) (by omega) (by omega) (by omega)
      (by rw [v1]; unfold asz; omega) (by rw [s1, h1]; exact h1')) fun σ2 e2 => ?_
    subst e2
    have hD2 : (σ1.setArr B.aW (σ1.nat (n0 + 11)) (σ1.sc (u + 1))).arr B.aW 0 = ((1 : ℤ) : ℝ) := by
      simp [v1, s1, h1]
    refine XV.mono (tail _ 1 (.sc u) 0 1 rfl hD2 (by simp [e1 (n0 + 4) (by omega), hone])
      (by simp [e1 B.rd (by omega), hdv]) (by simp [s1, hz]) (by simp [d1])
      ((G1.mono (S' := fun y => u + 13 ≤ y) (N' := fun j => j = n0 + 11 ∨ j = n0 + 13)
        (Ar' := fun b _ => b = B.aW) (fun _ h => h.elim) (fun j h => Or.inl h) (fun _ _ h => h.elim)).setArr
        (b := B.aW) rfl _)
      (by simp only [IE.WF]; omega) rfl (by simp only [IE.top]; omega) fun k hk σ' hF hk' => ?_) le_rfl ?_
    · have hz' : σ'.sc u = 0 := by rw [hF.2.1 _ (by omega)]; simp [s1, hz]
      refine ⟨⟨0, by rw [hz']; simp, by simp⟩, by simp only [IE.eval]; rw [hz']; simp [vextZ]⟩
    · rintro σ' ⟨⟨hD, hj⟩, d', F'⟩
      exact ⟨⟨1, one_pos, one_lt_pow₀ (by norm_num) (by omega), hD,
        fun j => ⟨0, by simp, by rw [hj j]; simp, by simp [frOutQ]⟩⟩, d', F'⟩

/-! ## The bounds of the branch -/

/-- The exponent bound of ELL-F: `8 G + 4 d + (d + 1) size M̂ + 40`, `G = frG d m M̂ ≥ e_R`. -/
def frEx (d m Mh : ℕ) : ℕ := 8 * frG d m Mh + 4 * d + (d + 1) * Nat.size Mh + 40

/-- The register bound of the branch. -/
def frRegB (d m Mh : ℕ) : ℕ := 100 * (d + m + frG d m Mh + 1) ^ 3

/-- The units of the branch. -/
def frBrU (d m Mh : ℕ) : ℕ :=
  frE0U d m Mh + ((4 * frER d m Mh + 4) + ((24 * d + 16) + (30 + ((32 * frP d + 12 * frQ d (frER d m Mh) +
    36 * (frER d m Mh + 1) + 111) + ((7 * (d * d) + 14 * d + 13) +
    ((frN d (frER d m Mh) * (frKb d m (frEx d m Mh) + 2) + 4) + frOutU d))))))

theorem fr_regs {d m M A : ℕ} (hd : 1 ≤ d) (h : frRegB d m M < A) :
    3 + 2 * ((d + 1) * m) + 1 < A ∧ 2 * (d + 1) + frG d m M + 1 < A ∧ frER d m M < A ∧ 3 * d < A ∧ d * d < A ∧
      (d * (d + 1) + d * (d + 1)) * (frER d m M + 1) + 1 < A ∧ d * (d + 1) + d * (d + 1) < A ∧
      2 * (9 + Nat.clog 2 d + frER d m M + 3 * (frER d m M + 1) + 2 * 1) + 6 * (frER d m M + 1) +
        2 * (6 + Nat.clog 2 (d ^ 2 * (d + 1)) + 2 * 1) + 20 < A ∧
      2 * frQ d (frER d m M) + 2 * frP d + 6 * (frER d m M + 1) + d + 3 < A ∧ frN d (frER d m M) < A ∧ m < A ∧
      4 + 2 * ((d + 1) * (m + 1)) < A ∧ d * d + d < A ∧ d + 1 < A := by
  have he := frER_leG d m M
  obtain ⟨-, c2, c3⟩ := clog_bounds
  have hcd := c2 d
  have hcq := c3 d hd
  unfold frRegB at h
  unfold frQ frP frN
  generalize frER d m M = e at he ⊢
  generalize frG d m M = G at he h ⊢
  generalize hV : d + m + G + 1 = V at h
  have hV1 : 1 ≤ V := by omega
  have hA : 100 * (V * V * V) < A := by rw [show V * V * V = V ^ 3 by ring]; exact h
  have k1 : V ≤ V * V := by nlinarith
  have k2 : V * V ≤ V * V * V := by nlinarith
  have b1 : (d + 1) * m ≤ V * V := Nat.mul_le_mul (by omega) (by omega)
  have b2 : d * d ≤ V * V := Nat.mul_le_mul (by omega) (by omega)
  have b3 : d * (d + 1) ≤ V * V := Nat.mul_le_mul (by omega) (by omega)
  have b4 : (d * (d + 1) + d * (d + 1)) * (e + 1) ≤ (V * V + V * V) * V :=
    Nat.mul_le_mul (by omega) (by omega)
  have b5 : (d + 1) * (m + 1) ≤ V * V := Nat.mul_le_mul (by omega) (by omega)
  have b6 : 2 * d * (d + 1) * (e + 1) ≤ 2 * V * V * V :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl (by omega)) (by omega)) (by omega)
  have k3 : (V * V + V * V) * V = 2 * (V * V * V) := by ring
  have k4 : 2 * V * V * V = 2 * (V * V * V) := by ring
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega⟩

/-! ## The branch -/

/-- Procedure FRAME for `d ≥ 2`: `M̂` and `e_R`, `R̄ = 2^{e_R}` into the slot `c`, the constants of ELL-R at `j = 1`,
the start state, the loop of ELL-F, the output. -/
def xframeBr (L : Layout) (B : PrBlk) (P u c a0 n0 : ℕ) : XCmd :=
  .seq (xfrE0 L B u c n0)
  (.seq (xpow2 L c (n0 + 46) (n0 + 9) (n0 + 4))
  (.seq (xellS0 L (frEB B) u c n0)
  (.seq (xellSetR (frEB B) n0)
  (.seq (xellSlots L (frEB B) P u c n0)
  (.seq (xellArr L (frEB B) P u c a0 n0)
  (.seq (xfrLoop L B P u a0 n0)
    (xfrOut L B P u a0 n0)))))))

theorem frameQ_ge2 {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ} (hd : 2 ≤ d) :
    frameQ d n m A b = frOutQ (frP d) (frEll A b) := by
  unfold frameQ
  split_ifs with h1 h0
  · omega
  · omega
  · cases frEll A b <;> rfl

set_option maxHeartbeats 32000000 in
/-- **Procedure FRAME on the machine for `d ≥ 2`**: the frame centre `frameQ` in the array `aW` in the form of the
play leaf, from the input rows of `ctxOf`. -/
theorem XV.frameBr {L : Layout} {w : BitRAM.World d} {n m : ℕ} {A : Matrix (Fin m) (Fin d) ℚ} {b : Fin m → ℚ}
    {ℓa ℓ s : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {B : PrBlk} {P u c a0 n0 : ℕ} (hd : 2 ≤ d)
    (hP : P = B.o + 3) (hu : u = P + 12) (hc : c = u + 60) (hn : n0 = B.rE + 1) (ha : a0 = B.aW + 2)
    (hS : c + 60 ≤ L.NS) (hNN : n0 + 50 ≤ L.NN) (hNA : a0 + 6 ≤ L.NA) (hrd : B.rd < B.rE) (hrm : B.rm < B.rE)
    (e_d : σ.nat B.rd = d) (e_m : σ.nat B.rm = m) (hz : σ.sc u = 0) (h1 : σ.sc (u + 1) = 1)
    (hone : σ.nat (n0 + 4) = 1) (hℓ : 64 * frEx d m (frMhat A b) + 16 < ℓ) (hs : frEx d m (frMhat A b) < s)
    (hℓa : frRegB d m (frMhat A b) < 2 ^ ℓa) :
    XRunsB L (ctxOf w n m A b) ℓa ℓ (xframeBr L B P u c a0 n0) σ (frBrU d m (frMhat A b)) (fun σ' =>
      PtIn σ' B.aW s (frameQ d n m A b) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => B.o ≤ y) (fun j => B.rE ≤ j) (fun b _ => B.aW ≤ b) σ σ') := by
  have hd1 : 1 ≤ d := by omega
  set M := frMhat A b with hMdef
  set G := frG d m M with hGdef
  set eR := frER d m M with heRdef
  set E := frEx d m M with hEdef
  set p := frP d with hpdef
  set q := frQ d eR with hqdef
  set N := frN d eR with hNdef
  obtain ⟨-, hcd, hc1⟩ := clog_bounds
  have hcd' : Nat.clog 2 d ≤ d := hcd d
  have hc1' : Nat.clog 2 (d ^ 2 * (d + 1)) ≤ 3 * d := hc1 d hd1
  have heG : eR ≤ G := frER_leG d m M
  have hp8 : p = 8 + Nat.clog 2 (d ^ 2 * (d + 1)) := rfl
  have hq14 : q = 14 + Nat.clog 2 d + 4 * eR := rfl
  have hE' : E = 8 * G + 4 * d + (d + 1) * Nat.size M + 40 := rfl
  generalize hSM : (d + 1) * Nat.size M = SM at hE'
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14⟩ := fr_regs hd1 hℓa
  -- the powers of `2`
  set Rb : ℤ := 2 ^ eR with hRb
  have hRb0 : (0 : ℤ) ≤ Rb := by positivity
  obtain ⟨pRR, pL, pLH, pRL, ppRR, pcA, pca⟩ := ell_pows (s := eR) (lam := eR + 1) (p := p) hRb0 le_rfl
  have hMF : (M : ℤ) ^ (d + 1) ≤ 2 ^ E := by
    have hM : (M : ℤ) ≤ 2 ^ Nat.size M := by exact_mod_cast (Nat.lt_size_self M).le
    calc (M : ℤ) ^ (d + 1) ≤ (2 ^ Nat.size M) ^ (d + 1) := pow_le_pow_left₀ (by positivity) hM _
      _ = 2 ^ ((d + 1) * Nat.size M) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ E := pow_le_pow_right₀ (by norm_num) (by omega)
  -- `M̂`, `e_R`
  refine XV.seq (XV.frE0 hL (B := B) (u := u) (c := c) (n0 := n0) (by omega) (by omega) (by omega) (by omega)
    (by omega) hz h1 hone e_d e_m r1 r2 (show G + 1 < ℓ by omega)) fun σ1 ⟨n81, n91, n101, d1, F1⟩ => ?_
  have k1 : ∀ j, j < n0 + 8 ∨ (n0 + 10 < j ∧ j < n0 + 19) ∨ n0 + 21 < j → σ1.nat j = σ.nat j := fun j h =>
    F1.1 j (by simp only [fr0N]; omega)
  have s1 : ∀ y, y < c + 30 → σ1.sc y = σ.sc y := fun y h => F1.2.1 y (by simp only [fr0S]; omega)
  -- `R̄ = 2^{e_R}`
  refine XV.seq (XV.pow2A hL (p := c) (i := n0 + 46) (n := n0 + 9) (one := n0 + 4) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) n91 (by rw [k1 _ (by omega), hone]) r3 (by omega))
    fun σ2 ⟨c2, d2, F2⟩ => ?_
  have k2 : ∀ j, j ≠ n0 + 46 → σ2.nat j = σ1.nat j := fun j h => F2.1 j h
  have s2 : ∀ y, y ≠ c → σ2.sc y = σ1.sc y := fun y h => F2.2.1 y h
  -- `d`, the logarithms
  refine XV.seq (XV.ellS0 hL (B := frEB B) (u := u) (c := c) (n0 := n0) (by simp only [frEB]; omega) (by omega)
    (by omega) (by omega) (by simp only [frEB]; rw [k2 _ (by omega), k1 _ (by omega), e_d])
    (by rw [s2 _ (by omega), s1 _ (by omega), hz]) (by rw [s2 _ (by omega), s1 _ (by omega), h1])
    (by rw [k2 _ (by omega), k1 _ (by omega), hone]) r4 (by omega)) fun σ3 ⟨d13, c1v, cdv, d3, F3⟩ => ?_
  have k3 : ∀ j, j ≠ n0 + 17 → j ≠ n0 + 18 → σ3.nat j = σ2.nat j := fun j h h' => F3.1 j (by omega)
  -- the registers
  refine XV.seq (XV.ellSetR hL (B := frEB B) (n0 := n0) (j := 1) (cR := eR) (lam := eR + 1)
    (c1 := Nat.clog 2 (d ^ 2 * (d + 1))) (cd := Nat.clog 2 d) (by simp only [frEB]; omega) (by omega) hd1
    (by rw [k3 _ (by omega) (by omega), k2 _ (by omega), k1 _ (by omega), hone])
    (by simp only [frEB]; rw [k3 _ (by omega) (by omega), k2 _ (by omega), k1 _ (by omega), e_d])
    (by rw [k3 _ (by omega) (by omega), k2 _ (by omega), n81])
    (by rw [k3 _ (by omega) (by omega), k2 _ (by omega), n91])
    (by rw [k3 _ (by omega) (by omega), k2 _ (by omega), n101]) c1v cdv rfl r5 r6 r7 r8)
    fun σ4 ⟨r4', rdv, _, _, r14', r15, r22, r30, r7', r34, r35, r36, r38, r39, r42, r45, d4, F4⟩ => ?_
  have s4 : ∀ y, σ4.sc y = σ3.sc y := fun y => F4.2.1 y id
  -- the slots
  refine XV.seq (XV.ellSlots hL (B := frEB B) (P := P) (u := u) (c := c) (n0 := n0) (p := p) (q := q) (j := 1)
    (lam := eR + 1) (E := E) (Rb := Rb) (by simp only [frEB]; omega) (by omega) (by omega) hS (by omega)
    (by rw [s4, F3.2.1 _ (by omega), s2 _ (by omega), s1 _ (by omega), hz])
    (by rw [s4, F3.2.1 _ (by omega), s2 _ (by omega), s1 _ (by omega), h1])
    (by rw [s4, F3.2.1 _ (by omega), c2])
    (by rw [s4, d13]) r4' r14' (by rw [r22, hp8]; omega) (by rw [r30, hq14]; omega) (by rw [r34, hp8]; omega)
    (by rw [r35, hp8]; omega) (by rw [r36, hp8]; omega) (by rw [r38, hp8]; omega) (by rw [r39, hq14]; omega) r42 r45
    (abs_le_of_le hRb0 le_rfl (by omega)) (abs_le_of_le (mul_nonneg hRb0 hRb0) pRR (by omega))
    (abs_le_of_le (by positivity) le_rfl (by omega)) (abs_le_of_le (by positivity) pL (by omega))
    (abs_le_of_le (by positivity) le_rfl (by omega)) (abs_le_of_le (by positivity) le_rfl (by omega))
    (abs_le_of_le (by positivity) pLH (by omega)) (abs_le_of_le (by positivity) pRL (by omega))
    r9 (by omega) (by omega) (by omega))
    fun σ5 ⟨o5v, t3, t4, t5, t6, hU, c20, z5, o5, d5, F5⟩ => ?_
  have k5 : ∀ j, j ≠ n0 + 46 → σ5.nat j = σ4.nat j := fun j h => F5.1 j h
  -- the start state
  set D : ℤ := 2 ^ p * (Rb * Rb) with hD
  refine XV.seq (XV.ellArr hL (B := frEB B) (P := P) (u := u) (c := c) (a0 := a0) (n0 := n0) (E := E) (D := D)
    hd1 (by omega) (by omega) (by omega) (by omega) (by simp only [frEB]; omega) (by omega) z5 c20
    (abs_le_of_le (by positivity) ppRR (by omega)) (by omega) (by rw [k5 _ (by omega), r4'])
    (by rw [k5 _ (by omega), r14']) (by rw [k5 _ (by omega), r15]) ((k5 B.rd (by omega)).trans rdv))
    fun σ6 ⟨A6, a6, _, d6, F6⟩ => ?_
  have k6 : ∀ j, j ≠ n0 + 11 → j ≠ n0 + 13 → σ6.nat j = σ5.nat j := fun j h h' => F6.1 j (by omega)
  have s6 : ∀ y, y ≠ P + 1 → y < c + 24 → σ6.sc y = σ5.sc y := fun y h h' => F6.2.1 y (by omega)
  -- the frame so far
  have G6 : FrameA (fun y => B.o ≤ y) (fun j => B.rE ≤ j) (fun b _ => B.aW ≤ b) σ σ6 :=
    ((((F1.mono (fun y h => by simp only [fr0S] at h; omega) (fun j h => by simp only [fr0N] at h; omega)
      (fun _ _ h => h.elim)).trans (F2.mono (fun y h => by omega) (fun j h => by omega) (fun _ _ h => h.elim))).trans
      ((F3.mono (fun y h => by omega) (fun j h => by omega) (fun _ _ h => h.elim)).trans
      (F4.mono (fun y h => h.elim) (fun j h => by omega) (fun _ _ h => h.elim)))).trans
      (F5.mono (fun y h => by simp only [frEB] at h; omega) (fun j h => by omega) (fun _ _ h => h.elim))).trans
      (F6.mono (fun y h => by omega) (fun j h => by omega) (fun b _ h => by omega))
  have D6 : σ6.draws = σ.draws := by rw [d6, d5, d4, d3, d2, d1]
  -- the loop
  set capA : ℤ := 2 ^ p * (Rb * Rb * 2 ^ (6 * (eR + 1) + 2)) with hcapA
  set capa : ℤ := 2 ^ p * (Rb + Rb * 2 ^ (3 * (eR + 1) + 1)) with hcapa
  have hE6 : FrEnv B m p P u n0 σ6 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [k6 _ (by omega) (by omega), k5 _ (by omega)]; exact rdv
    · rw [G6.1 _ (by omega), e_m]
    · rw [k6 _ (by omega) (by omega), k5 _ (by omega)]; exact r14'
    · rw [k6 _ (by omega) (by omega), k5 _ (by omega)]; exact r4'
    · rw [s6 _ (by omega) (by omega)]; exact z5
    · rw [s6 _ (by omega) (by omega)]; exact o5
    · rw [s6 _ (by omega) (by omega)]; exact t4
    · rw [s6 _ (by omega) (by omega)]; exact t5
  have hU6 : UpdEnv u p q 1 capA capa σ6 := hU.frame F6 (fun y h => by omega)
  have bA0 : ∀ i k, |(D • (1 : Matrix (Fin d) (Fin d) ℤ)) i k| ≤ capA := by
    intro i k
    have h0 : (0 : ℤ) ≤ D := by positivity
    have hle : D ≤ capA := by
      simp only [hD, hcapA]
      exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num)))
        (by positivity)
    rw [Matrix.smul_apply, Matrix.one_apply]
    split_ifs
    · rw [smul_eq_mul, mul_one, abs_of_nonneg h0]; exact hle
    · rw [smul_eq_mul, mul_zero, abs_zero]; exact h0.trans hle
  have hS6 : FrLSt a0 capA capa (D • (1 : Matrix (Fin d) (Fin d) ℤ)) 0 σ6 :=
    ⟨A6, a6, bA0, fun k => by simp only [Pi.zero_apply, abs_zero]; positivity⟩
  have bcA : capA ≤ 2 ^ E := pcA.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have bca : capa ≤ 2 ^ E := pca.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have bkE : 3 * d + 2 ≤ E := by omega
  refine XV.seq (XV.frEllLoop hL (B := B) (p := p) (q := q) (P := P) (u := u) (a0 := a0) (n0 := n0) (E := E)
    (N := N) (by omega) (by omega) (by omega) (by omega) (by omega) hNN hrd hrm hE6 hU6 hS6
    (by rw [k6 _ (by omega) (by omega), k5 _ (by omega)]; exact r7') r10 hMF (by omega) (by omega) (by omega)
    (by omega) ((kapN_le hd1).trans (pow_le_pow_right₀ (by norm_num) bkE))
    ((kapD_le hd1).trans (pow_le_pow_right₀ (by norm_num) bkE)) (by positivity) (by positivity) bcA bca r11 r12
    r13 hℓ) fun σ7 ⟨o7, d7, F7⟩ => ?_
  -- the output
  have k7 : ∀ j, ¬ frlN B n0 j → σ7.nat j = σ6.nat j := fun j h => F7.1 j h
  have s7 : ∀ y, ¬ frlS P u y → σ7.sc y = σ6.sc y := fun y h => F7.2.1 y h
  refine XV.mono (XV.frOut hL (B := B) (P := P) (u := u) (a0 := a0) (n0 := n0) (F := E) (p := p) (s := s)
    hd1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rw [k7 _ (by simp only [frlN]; omega)]; exact hE6.1)
    (by rw [k7 _ (by simp only [frlN]; omega)]; exact hE6.2.2.2.1)
    (by rw [s7 _ (by simp only [frlS]; omega)]; exact hE6.2.2.2.2.1)
    (by rw [s7 _ (by simp only [frlS]; omega)]; exact hE6.2.2.2.2.2.1)
    (by rw [s7 _ (by simp only [frlS]; omega), s6 _ (by omega) (by omega)]; exact t3) o7 bca (by omega) (by omega)
    hs (by omega)) le_rfl fun σ8 ⟨o8, d8, F8⟩ => ?_
  -- the result
  have eA : (2 : ℤ) ^ (p + 2 * eR + 6 * (eR + 1) + 2) = capA := by simp only [hcapA, hRb]; ring
  have ea : (2 : ℤ) ^ p * (2 ^ eR + 2 ^ (eR + 3 * (eR + 1) + 1)) = capa := by simp only [hcapa, hRb]; ring
  have eD : (2 : ℤ) ^ (p + 2 * eR) = D := by simp only [hD, hRb]; ring
  have hEll : frEll A b = frLoop p q capA capa (frAl A b) (fun i => 2 ^ (p + 1) * frBe A b i)
      (fun i => 2 ^ (2 * p) * (frAl A b i ⬝ᵥ frAl A b i)) N (D • (1 : Matrix (Fin d) (Fin d) ℤ)) 0 := by
    rw [← eA, ← ea, ← eD]; rfl
  refine ⟨?_, by rw [d8, d7, D6], ?_⟩
  · rw [frameQ_ge2 hd, hEll]; exact o8
  · exact (G6.trans (F7.mono (fun y h => by simp only [frlS] at h; omega)
      (fun j h => by simp only [frlN] at h; omega) (fun b _ h => by simp only [frlA] at h; omega))).trans
      (F8.mono (fun y h => by omega) (fun j h => by omega) (fun b _ h => by omega))

end AdversarialBco.Bit.Transfer
