/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTriConstRun
public import AdversarialBco.Bit.Transfer.XBLSetupPrm

@[expose] public section

/-!
# TRI-M, the constants block

* `xtcPro`, `XV.tcPro`: the registers `1, d + 1, m + (d + d), d d, m` and the slots `0, 1, -1, 2, 4`, `s = 4`, `d`, `n`;
* `xconsts`, `XV.consts`: the prologue, the search of `triSQ d`, the straight line `tcSt`, the copies of the constants
  of a draw into `o + 4, ..., o + 13` and `2^{G_c}` into `o + 35`, then `B_g`, `2^{n_e}`, `m_st` into the registers
  `r + 12`, `r + 24`, `r + 28`: every constant `XV.init` and `XV.stages` read.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.RQ AdversarialBco.Bit.TriM
  AdversarialBco.Bit.Transfer.BLM

variable {d : ℕ}

/-! ## The prologue -/

/-- The prologue: `r := 1`, `r + 1 := d + 1`, `r + 25 := d d`, `r + 26 := m`, `r + 2 := m + (d + d)`; the slots
`o + 1, o + 2, o + 3 := 0, 1, -1`, `o + 116, o + 117 := 2, 4`, `o + 115 := 4`, `o + 113 := d`, `o + 114 := n`. -/
def xtcPro (L : Layout) (nd rm sn o r : ℕ) : XCmd :=
  .seq (.prim (.frag (.nconst r 1)))
  (.seq (.prim (.frag (.nadd (r + 1) nd r)))
  (.seq (xnmul (r + 25) nd nd)
  (.seq (.prim (.frag (.nconst (r + 26) 0)))
  (.seq (.prim (.frag (.nadd (r + 26) (r + 26) rm)))
  (.seq (.prim (.frag (.nadd (r + 2) nd nd)))
  (.seq (.prim (.frag (.nadd (r + 2) (r + 26) (r + 2))))
  (.seq (toX (VL.sconst L (o + 1) 0))
  (.seq (toX (VL.sconst L (o + 2) 1))
  (.seq (toX (VL.sconst L (o + 3) (-1)))
  (.seq (toX (VL.sconst L (o + 116) 2))
  (.seq (toX (VL.sconst L (o + 117) 4))
  (.seq (toX (VL.sconst L (o + 115) 4))
  (.seq (toX (VL.ncast L (o + 113) nd))
  (toX (VL.sop2 L .add (o + 114) sn (o + 1))))))))))))))))

set_option maxHeartbeats 4000000 in
theorem XV.tcPro {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {nd rm sn o r m n : ℕ}
    (hS : o + 245 ≤ L.NS) (hN : r + 31 ≤ L.NN) (hnd : nd < r) (hrm : rm < r) (hsn : sn < o)
    (hσd : σ.nat nd = d) (hσm : σ.nat rm = m) (hσn : σ.sc sn = n)
    (hda : d * d + m + (d + d) + 2 < 2 ^ ℓa) (hdl : d + 4 < 2 ^ ℓ) (hnl : n + 4 < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xtcPro L nd rm sn o r) σ 15 (fun σ' =>
      σ'.nat r = 1 ∧ σ'.nat (r + 1) = d + 1 ∧ σ'.nat (r + 2) = m + (d + d) ∧ σ'.nat (r + 25) = d * d ∧
      σ'.nat (r + 26) = m ∧ σ'.sc (o + 1) = 0 ∧ σ'.sc (o + 2) = 1 ∧ σ'.sc (o + 3) = -1 ∧ σ'.sc (o + 116) = 2 ∧
      σ'.sc (o + 117) = 4 ∧ σ'.sc (o + 115) = (((4 : ℕ) : ℤ) : ℝ) ∧ σ'.sc (o + 113) = ((d : ℤ) : ℝ) ∧
      σ'.sc (o + 114) = ((n : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => o ≤ y) (fun j => r ≤ j) (fun _ _ => False) σ σ') := by
  have n0 : nd ≠ r := by omega
  have n1 : nd ≠ r + 1 := by omega
  have n2 : nd ≠ r + 2 := by omega
  have n25 : nd ≠ r + 25 := by omega
  have n26 : nd ≠ r + 26 := by omega
  have m0 : rm ≠ r := by omega
  have m1 : rm ≠ r + 1 := by omega
  have m25 : rm ≠ r + 25 := by omega
  have m26 : rm ≠ r + 26 := by omega
  have s1 : sn ≠ o + 1 := by omega
  have s2 : sn ≠ o + 2 := by omega
  have s3 : sn ≠ o + 3 := by omega
  have s113 : sn ≠ o + 113 := by omega
  have s115 : sn ≠ o + 115 := by omega
  have s116 : sn ≠ o + 116 := by omega
  have s117 : sn ≠ o + 117 := by omega
  have hc : ∀ c : ℕ, c ≤ 4 → |((c : ℚ) : ℝ)| < 2 ^ ℓ := fun c hc => by
    rw [Rat.cast_natCast]; exact XV.abs_nat_lt (by omega)
  have h1 : (1 : ℕ) < 2 ^ ℓa := by omega
  refine XV.mono (K := 1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1))))))))))))))
    ?_ (by norm_num) (fun _ h => h)
  unfold xtcPro
  refine XV.seq (XV.nconst hL (i := r) (by omega) 1 h1) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.nadd hL (i := r + 1) (a := nd) (b := r) (by omega) (by omega) (by omega)
    (by simp [n0, hσd]; omega) (by simpa using h1)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.nmul hL (i := r + 25) (a := nd) (b := nd) (by omega) (by omega) (by omega)
    (by simp [n0, n1, hσd]; nlinarith) (by simp [n0, n1, hσd]; nlinarith) (by simp [n0, n1, hσd]; omega))
    fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.nconst hL (i := r + 26) (by omega) 0 (by omega)) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.nadd hL (i := r + 26) (a := r + 26) (b := rm) (by omega) (by omega) (by omega)
    (by simp) (by simp [m0, m1, m25, m26, hσm]; omega)) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.nadd hL (i := r + 2) (a := nd) (b := nd) (by omega) (by omega) (by omega)
    (by simp [n0, n1, n25, n26, hσd]; nlinarith) (by simp [n0, n1, n25, n26, hσd]; nlinarith)) fun σ6 e6 => ?_
  subst e6
  refine XV.seq (XV.nadd hL (i := r + 2) (a := r + 26) (b := r + 2) (by omega) (by omega) (by omega)
    (by simp [m0, m1, m25, m26, hσm]; omega) (by simp [n0, n1, n25, n26, hσd]; omega)) fun σ7 e7 => ?_
  subst e7
  refine XV.seq (XV.sconst hL (x := o + 1) (by omega) 0 rfl (by simp)) fun σ8 e8 => ?_
  subst e8
  refine XV.seq (XV.sconst hL (x := o + 2) (by omega) 1 rfl (by simpa using hc 1 (by omega))) fun σ9 e9 => ?_
  subst e9
  refine XV.seq (XV.sconst hL (x := o + 3) (by omega) (-1) rfl (by
    rw [show ((-1 : ℚ) : ℝ) = -((1 : ℕ) : ℚ) by push_cast; ring, abs_neg]; exact hc 1 (by omega)))
    fun σ10 e10 => ?_
  subst e10
  refine XV.seq (XV.sconst hL (x := o + 116) (by omega) 2 rfl (by simpa using hc 2 (by omega))) fun σ11 e11 => ?_
  subst e11
  refine XV.seq (XV.sconst hL (x := o + 117) (by omega) 4 rfl (by simpa using hc 4 (by omega))) fun σ12 e12 => ?_
  subst e12
  refine XV.seq (XV.sconst hL (x := o + 115) (by omega) 4 rfl (by simpa using hc 4 (by omega))) fun σ13 e13 => ?_
  subst e13
  refine XV.seq (XV.ncastI hL (x := o + 113) (i := nd) (by omega) (by omega)
    (by simp [n0, n1, n2, n25, n26, hσd]; omega))
    fun σ14 e14 => ?_
  subst e14
  have hn0 : |((n : ℕ) : ℝ)| < 2 ^ ℓ := XV.abs_nat_lt (by omega)
  refine XV.mono (XV.sop2 hL (x := o + 114) (a := sn) (b := o + 1) (by omega) (by omega) (by omega) .add
    (by intro h; cases h) (by simp [s1, s2, s3, s113, s115, s116, s117, hσn]; exact_mod_cast (show n < 2 ^ ℓ by omega))
    (by simp)
    (by simp [s1, s2, s3, s113, s115, s116, s117, hσn, RealRAM.Op2.eval]; exact_mod_cast (show n < 2 ^ ℓ by omega)))
    le_rfl ?_
  rintro σ' rfl
  refine ⟨by simp, by simp [n0, hσd], by simp [m0, m1, m25, m26, hσm, n0, n1, n25, n26, hσd],
    by simp [n0, n1, hσd], by simp [m0, m1, m25, m26, hσm], by simp, by simp, by simp, by simp, by simp,
    by simp, by simp [n0, n1, n2, n25, n26, hσd], by simp [s1, s2, s3, s113, s115, s116, s117, hσn, RealRAM.Op2.eval],
    by simp, ?_⟩
  refine ⟨fun j hj => ?_, fun y hy => ?_, fun b k _ => by simp, by simp, by simp⟩
  · simp only [not_le] at hj
    simp [show j ≠ r by omega, show j ≠ r + 1 by omega, show j ≠ r + 2 by omega, show j ≠ r + 25 by omega,
      show j ≠ r + 26 by omega]
  · simp only [not_le] at hy
    simp [show y ≠ o + 1 by omega, show y ≠ o + 2 by omega, show y ≠ o + 3 by omega, show y ≠ o + 113 by omega,
      show y ≠ o + 114 by omega, show y ≠ o + 115 by omega, show y ≠ o + 116 by omega, show y ≠ o + 117 by omega]

/-! ## The constants block -/

/-- The copies of the constants of a draw (`P_B, P_2, P_G, P_j, R, -R, A_l, B_h, -B_h, 8 d`) into `o + 4, ..., o + 13`
and of `2^{G_c}` into `o + 35`, from the region of `tcSt`. -/
def tcCp (o : ℕ) : List (ℕ × ℕ) :=
  [(o + 4, o + 120 + 49), (o + 5, o + 120 + 72), (o + 6, o + 120 + 73), (o + 7, o + 120 + 32), (o + 8, o + 120 + 75),
   (o + 9, o + 120 + 76), (o + 10, o + 120 + 78), (o + 11, o + 120 + 81), (o + 12, o + 120 + 82),
   (o + 13, o + 120 + 83), (o + 35, o + 120 + 84)]

/-- The constants block of TRI-M: the prologue, the search of `triSQ d`, the line `tcSt`, the copies, then
`B_g`, `2^{n_e}`, `m_st` into the registers `r + 12`, `r + 24`, `r + 28`. -/
def xconsts (L : Layout) (nd rm sn o r : ℕ) : XCmd :=
  .seq (xtcPro L nd rm sn o r)
  (.seq (xsearch L o r)
  (.seq (SL.code L (SLC.atB o r tcC) (tcSt.map (SStep.shS o)))
  (.seq (xcopyS L (o + 1) (tcCp o))
  (.seq (xrtoN L (r + 12) (o + 120 + 39))
  (.seq (xrtoN L (r + 24) (o + 120 + 64)) (xrtoN L (r + 28) (o + 120 + 57)))))))

/-- The units of the constants block. -/
abbrev constsK (d n : ℕ) : ℕ := 15 + (srchK d n + (ev (tcG d n) (636, 3897) + (11 + (1 + (1 + 1)))))

set_option maxHeartbeats 8000000 in
/-- **The constants block**: from `d`, `m` in the registers `nd`, `rm` and `n` in the slot `sn`, every constant the
initial position and the stages read, within `constsK d n` units, changing only the slots from `o` and the registers
from `r`. -/
theorem XV.consts {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} {σ : Env d} (hL : LayOK L d ℓa) {nd rm sn o r m n : ℕ}
    (hd : 1 ≤ d) (hn : 1 ≤ n) (hS : o + 245 ≤ L.NS) (hN : r + 31 ≤ L.NN) (hnd : nd < r) (hrm : rm < r)
    (hsn : sn < o) (hσd : σ.nat nd = d) (hσm : σ.nat rm = m) (hσn : σ.sc sn = n)
    (hda : d * d + m + (d + d) + 2 < 2 ^ ℓa) (hNa : 2 ^ triNeQ d (ellPos d n) < 2 ^ ℓa)
    (hTl : ev (tcG d n) tcT < ℓ) (hTa : ev (tcG d n) tcT < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xconsts L nd rm sn o r) σ (constsK d n) (fun σ' =>
      σ'.nat r = 1 ∧ σ'.nat (r + 1) = d + 1 ∧ σ'.nat (r + 2) = m + (d + d) ∧ σ'.nat (r + 12) = triBgQ d ∧
      σ'.nat (r + 24) = 2 ^ triNeQ d (ellPos d n) ∧ σ'.nat (r + 25) = d * d ∧ σ'.nat (r + 26) = m ∧
      σ'.nat (r + 28) = triMstQ (1 / 2) n ∧
      σ'.sc (o + 1) = 0 ∧ σ'.sc (o + 2) = 1 ∧ σ'.sc (o + 3) = -1 ∧
      σ'.sc (o + 4) = (tzDC d (ellPos d n)).PB ∧ σ'.sc (o + 5) = (tzDC d (ellPos d n)).P2 ∧
      σ'.sc (o + 6) = (tzDC d (ellPos d n)).PG ∧ σ'.sc (o + 7) = (tzDC d (ellPos d n)).Pj ∧
      σ'.sc (o + 8) = (tzDC d (ellPos d n)).R ∧ σ'.sc (o + 9) = -(tzDC d (ellPos d n)).R ∧
      σ'.sc (o + 10) = (tzDC d (ellPos d n)).Al ∧ σ'.sc (o + 11) = (tzDC d (ellPos d n)).Bh ∧
      σ'.sc (o + 12) = ((-(tzDC d (ellPos d n)).Bh : ℤ) : ℝ) ∧
      σ'.sc (o + 13) = ((8 * (tzDC d (ellPos d n)).dd : ℤ) : ℝ) ∧
      σ'.sc (o + 35) = ((2 ^ tzGc d (ellPos d n) : ℤ) : ℝ) ∧ σ'.draws = σ.draws ∧
      FrameA (fun y => o ≤ y) (fun j => r ≤ j) (fun _ _ => False) σ σ') := by
  have hΓl : tcG d n + 1 < ℓ := by have := hTl; simp only [ev, tcT] at this; omega
  have hΓa : tcG d n + 1 < 2 ^ ℓa := by have := hTa; simp only [ev, tcT] at this; omega
  have hsΓ : triSQ d ≤ tcG d n := by unfold tcG; omega
  have hsz : n.size ≤ tcG d n := by unfold tcG; omega
  have hs4 := (triSQ_bounds d).1
  have hp : ∀ k : ℕ, k ≤ tcG d n + 1 → k + 4 < 2 ^ ℓ := fun k hk => by
    have h1 : 2 ^ (tcG d n + 2) ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hΓl
    have h2 : tcG d n + 1 < 2 ^ (tcG d n + 1) := Nat.lt_two_pow_self
    rw [pow_succ] at h1; omega
  have hnG : n < 2 ^ tcG d n := (Nat.lt_size_self n).trans_le (Nat.pow_le_pow_right (by norm_num) hsz)
  have hn4 : n + 4 < 2 ^ ℓ := by
    have h1 : 2 ^ (tcG d n + 2) ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hΓl
    have h2 : 2 ^ 2 ≤ 2 ^ tcG d n := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ, pow_succ] at h1; omega
  have nS : ∀ y, y < o + 115 ∨ (o + 115 < y ∧ y < o + 120) → ¬ srS o y := fun y hy h => by
    rcases h with h | h <;> omega
  have nN : ∀ j, j < r + 29 → ¬ srN r j := fun j hj h => by rcases h with h | h <;> omega
  have nF : ∀ y, y < o + 4 ∨ (o + 13 < y ∧ y ≠ o + 35) → y ∉ (tcCp o).map Prod.fst := fun y hy h => by
    simp only [tcCp, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at h; omega
  have hC := tcC_ok (o := o) (r := r) hS hN
  unfold xconsts
  refine XV.seq (XV.tcPro hL hS hN hnd hrm hsn hσd hσm hσn hda (hp d (by unfold tcG; omega)) hn4)
    fun σ1 ⟨a1, a2, a3, a25, a26, c1, c2, c3, c116, c117, c115, c113, c114, d1, F1⟩ => ?_
  refine XV.seq (XV.search (n := n) hL hS hN hTl hTa c113 c115 c1 c2 c116 c117 a1)
    fun σ2 ⟨s2, d2, F2⟩ => ?_
  have k2 : ∀ y, ¬ srS o y → σ2.sc y = σ1.sc y := fun y h => F2.2.1 y h
  have j2 : ∀ j, ¬ srN r j → σ2.nat j = σ1.nat j := fun j h => F2.1 j h
  -- the line `tcSt`
  have h := XV.slAt (X := X) (σ := σ2) (G := tcG d n) (et := tcEt) (T := tcT) (ι := tcIn d n)
    (ins := [113, 114, 115]) (eIn := tcInP) (st := tcSt) hL hC tcSt_chk (fun k hk => tcSt_sem hd hn k hk)
    (by rw [tcSt_length]; show 120 + 85 ≤ 205; norm_num) hTl hTa tcIn_bound
    (fun y hy => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with rfl | rfl | rfl
      · rw [Nat.add_comm, k2 _ (nS _ (by omega)), c113]; simp [tcIn]
      · rw [Nat.add_comm, k2 _ (nS _ (by omega)), c114]; simp [tcIn]
      · rw [Nat.add_comm, s2]; simp [tcIn])
    (by show σ2.sc (1 + o) = 0; rw [Nat.add_comm, k2 _ (nS _ (by omega)), c1])
    (by show σ2.sc (2 + o) = 1; rw [Nat.add_comm, k2 _ (nS _ (by omega)), c2])
    (by show σ2.sc (116 + o) = 2; rw [Nat.add_comm, k2 _ (nS _ (by omega)), c116])
    (by show σ2.sc (117 + o) = 4; rw [Nat.add_comm, k2 _ (nS _ (by omega)), c117])
    (by show σ2.nat (0 + r) = 1; rw [Nat.zero_add, j2 _ (nN _ (by omega)), a1])
  rw [tcSt_units] at h
  refine XV.seq h fun σ3 ⟨v3, d3, F3⟩ => ?_
  have vS : ∀ k < 85, σ3.sc (o + 120 + k) = ((tcV d n k : ℤ) : ℝ) := fun k hk => by
    have h := v3 k (by rw [tcSt_length]; exact hk)
    rw [show tcC.b + o + k = o + 120 + k by show 120 + o + k = o + 120 + k; omega] at h
    exact h
  have k3 : ∀ y, y < o + 120 → σ3.sc y = σ2.sc y := fun y hy =>
    F3.2.1 y (by show ¬ ((120 + o ≤ y ∧ y < 120 + o + tcSt.length) ∨ 205 + o ≤ y); omega)
  have j3 : ∀ j, j < r + 29 → σ3.nat j = σ2.nat j := fun j hj =>
    F3.1 j (by show ¬ (j = 29 + r ∨ j = 30 + r); omega)
  have hbv := SL.val_bound tcSt 120 (tcIn d n) [113, 114, 115] tcInP tcEt tcT 40 (tcG d n)
    (SL.chk_get tcSt_chk).2 (fun k hk => tcSt_sem hd hn k hk) tcIn_bound
  have bS : ∀ k < 85, ple (tcEt k) tcT = true → ∀ y, y = o + 120 + k → |σ3.sc y| < 2 ^ ℓ := fun k hk hpl y hy => by
    rw [hy, vS k hk]; exact absZ_lt (hbv k (by rw [tcSt_length]; exact hk)) ((ev_mono hpl).trans_lt hTl)
  -- the copies
  refine XV.seq (XV.copyS hL (z := o + 1) (by omega) (tcCp o) σ3
    (by rw [k3 _ (by omega), k2 _ (nS _ (by omega)), c1])
    (by
      intro p hp
      simp only [tcCp, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        refine ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, ?_⟩
      · exact bS 49 (by norm_num) (by decide) _ rfl
      · exact bS 72 (by norm_num) (by decide) _ rfl
      · exact bS 73 (by norm_num) (by decide) _ rfl
      · exact bS 32 (by norm_num) (by decide) _ rfl
      · exact bS 75 (by norm_num) (by decide) _ rfl
      · exact bS 76 (by norm_num) (by decide) _ rfl
      · exact bS 78 (by norm_num) (by decide) _ rfl
      · exact bS 81 (by norm_num) (by decide) _ rfl
      · exact bS 82 (by norm_num) (by decide) _ rfl
      · exact bS 83 (by norm_num) (by decide) _ rfl
      · exact bS 84 (by norm_num) (by decide) _ rfl)
    (by
      show ([4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 35].map (fun x => o + x)).Nodup
      exact List.Nodup.map (fun a b h => by simpa using h) (by decide))
    (by
      have e1 : ∀ p ∈ tcCp o, p.1 < o + 120 := by
        intro p hp
        simp only [tcCp, List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; omega)
      have e2 : ∀ p ∈ tcCp o, o + 120 ≤ p.2 := by
        intro p hp
        simp only [tcCp, List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; omega)
      exact fun p hp q hq => by have := e1 p hp; have := e2 q hq; omega)) fun σ4 ⟨v4, d4, F4⟩ => ?_
  have k4 : ∀ y, y ∉ (tcCp o).map Prod.fst → σ4.sc y = σ3.sc y := fun y h => F4.2.1 y h
  have cpv : ∀ x k, (x, o + 120 + k) ∈ tcCp o → k < 85 → σ4.sc x = ((tcV d n k : ℤ) : ℝ) :=
    fun x k hm hk => (v4 _ hm).trans (vS k hk)
  have e4 : σ4.sc (o + 4) = (tzDC d (ellPos d n)).PB := by
    rw [cpv _ 49 (by simp [tcCp]) (by norm_num), tcV_49 d n hd]; simp [tzDC]
  have e5 : σ4.sc (o + 5) = (tzDC d (ellPos d n)).P2 := by
    rw [cpv _ 72 (by simp [tcCp]) (by norm_num), tcV_72 d n hd]
  have e6 : σ4.sc (o + 6) = (tzDC d (ellPos d n)).PG := by
    rw [cpv _ 73 (by simp [tcCp]) (by norm_num), tcV_73 d n hd hn]
  have e7 : σ4.sc (o + 7) = (tzDC d (ellPos d n)).Pj := by
    rw [cpv _ 32 (by simp [tcCp]) (by norm_num), tcV_32 d n]; simp [tzDC]
  have e8 : σ4.sc (o + 8) = (tzDC d (ellPos d n)).R := by
    rw [cpv _ 75 (by simp [tcCp]) (by norm_num), tcV_75 d n hd hn]
  have e9 : σ4.sc (o + 9) = -(tzDC d (ellPos d n)).R := by
    rw [cpv _ 76 (by simp [tcCp]) (by norm_num), tcV_76 d n hd hn, Int.cast_neg]
  have e10 : σ4.sc (o + 10) = (tzDC d (ellPos d n)).Al := by
    rw [cpv _ 78 (by simp [tcCp]) (by norm_num), tcV_78 d n hd hn]
  have e11 : σ4.sc (o + 11) = (tzDC d (ellPos d n)).Bh := by
    rw [cpv _ 81 (by simp [tcCp]) (by norm_num), tcV_81 d n hd hn]
  have e12 : σ4.sc (o + 12) = ((-(tzDC d (ellPos d n)).Bh : ℤ) : ℝ) := by
    rw [cpv _ 82 (by simp [tcCp]) (by norm_num), tcV_82 d n hd hn]
  have e13 : σ4.sc (o + 13) = ((8 * (tzDC d (ellPos d n)).dd : ℤ) : ℝ) := by
    rw [cpv _ 83 (by simp [tcCp]) (by norm_num), tcV_83 d n]
  have e35 : σ4.sc (o + 35) = ((2 ^ tzGc d (ellPos d n) : ℤ) : ℝ) := by
    rw [cpv _ 84 (by simp [tcCp]) (by norm_num), tcV_84 d n hd hn]
  -- the registers
  have hBg : triBgQ d ≤ tcG d n := by unfold tcG tzP gsm_prec; omega
  refine XV.seq (XV.rtoNat hL (i := r + 12) (x := o + 120 + 39) (v := triBgQ d) (by omega) (by omega)
    (by rw [k4 _ (nF _ (by omega)), vS 39 (by norm_num), tcV_39 d n hd]) (by omega)
    (by have := hp _ (by omega : triBgQ d ≤ tcG d n + 1); omega)) fun σ5 e5' => ?_
  subst e5'
  have hN2 : 2 ^ triNeQ d (ellPos d n) < 2 ^ ℓ := by
    have h := bS 64 (by norm_num) (by decide) _ rfl
    rw [vS 64 (by norm_num), tcV_64 d n hd hn] at h
    exact_mod_cast (abs_lt.mp h).2
  refine XV.seq (XV.rtoNat hL (i := r + 24) (x := o + 120 + 64) (v := 2 ^ triNeQ d (ellPos d n)) (by omega)
    (by omega) (by rw [Env.setNat_sc, k4 _ (nF _ (by omega)), vS 64 (by norm_num), tcV_64 d n hd hn]) hNa hN2)
    fun σ6 e6' => ?_
  subst e6'
  have hcl : Nat.clog 2 (2 * n) ≤ n.size + 1 := by
    refine Nat.clog_le_of_le_pow ?_
    rw [pow_succ]; have := Nat.lt_size_self n; omega
  refine XV.mono (XV.rtoNat hL (i := r + 28) (x := o + 120 + 57) (v := Nat.clog 2 (2 * n)) (by omega) (by omega)
    (by rw [Env.setNat_sc, Env.setNat_sc, k4 _ (nF _ (by omega)), vS 57 (by norm_num), tcV_57 d n]) (by omega)
    (by have := hp _ (by omega : Nat.clog 2 (2 * n) ≤ tcG d n + 1); omega)) le_rfl ?_
  rintro σ' rfl
  have R : ∀ j, j < r + 29 → σ4.nat j = σ1.nat j := fun j hj => by
    rw [F4.1 j id, j3 j hj, j2 j (nN j hj)]
  have nat7 : ∀ j, j ≠ r + 12 → j ≠ r + 24 → j ≠ r + 28 →
      (((σ4.setNat (r + 12) (triBgQ d)).setNat (r + 24) (2 ^ triNeQ d (ellPos d n))).setNat (r + 28)
        (Nat.clog 2 (2 * n))).nat j = σ4.nat j := fun j h1 h2 h3 => by simp [Env.setNat_nat, h1, h2, h3]
  have lo : ∀ y, y < o + 4 → σ4.sc y = σ1.sc y := fun y hy => by
    rw [k4 _ (nF _ (Or.inl hy)), k3 _ (by omega), k2 _ (nS _ (by omega))]
  have G2 : FrameA (fun y => o ≤ y) (fun j => r ≤ j) (fun _ _ => False) σ1 σ2 :=
    (FrameA.ofP (Ar := fun _ _ => False) F2).mono (fun y h => by rcases h with h | h <;> omega)
      (fun j h => by rcases h with h | h <;> omega) (fun _ _ h => h)
  have G3 : FrameA (fun y => o ≤ y) (fun j => r ≤ j) (fun _ _ => False) σ2 σ3 :=
    (FrameA.ofP (Ar := fun _ _ => False) F3).mono
      (fun y (h : (120 + o ≤ y ∧ y < 120 + o + tcSt.length) ∨ 205 + o ≤ y) => by omega)
      (fun j (h : j = 29 + r ∨ j = 30 + r) => by omega) (fun _ _ h => h)
  have G4 : FrameA (fun y => o ≤ y) (fun j => r ≤ j) (fun _ _ => False) σ3 σ4 :=
    F4.mono (fun y h => by
      simp only [tcCp, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at h; omega)
      (fun _ h => h.elim) (fun _ _ h => h)
  refine ⟨by rw [nat7 r (by omega) (by omega) (by omega), R r (by omega), a1],
    by rw [nat7 (r + 1) (by omega) (by omega) (by omega), R _ (by omega), a2],
    by rw [nat7 (r + 2) (by omega) (by omega) (by omega), R _ (by omega), a3],
    by simp [Env.setNat_nat], by simp [Env.setNat_nat],
    by rw [nat7 (r + 25) (by omega) (by omega) (by omega), R _ (by omega), a25],
    by rw [nat7 (r + 26) (by omega) (by omega) (by omega), R _ (by omega), a26],
    by rw [mst_eq n hn]; simp [Env.setNat_nat],
    by simp only [Env.setNat_sc]; rw [lo _ (by omega), c1],
    by simp only [Env.setNat_sc]; rw [lo _ (by omega), c2],
    by simp only [Env.setNat_sc]; rw [lo _ (by omega), c3],
    by simp only [Env.setNat_sc]; exact e4, by simp only [Env.setNat_sc]; exact e5,
    by simp only [Env.setNat_sc]; exact e6, by simp only [Env.setNat_sc]; exact e7,
    by simp only [Env.setNat_sc]; exact e8, by simp only [Env.setNat_sc]; exact e9,
    by simp only [Env.setNat_sc]; exact e10, by simp only [Env.setNat_sc]; exact e11,
    by simp only [Env.setNat_sc]; exact e12, by simp only [Env.setNat_sc]; exact e13,
    by simp only [Env.setNat_sc]; exact e35,
    by simp [d4, d3, d2, d1], ?_⟩
  exact (((F1.trans (G2.trans (G3.trans G4))).setNat (Nat.le_add_right r 12) _).setNat
    (Nat.le_add_right r 24) _).setNat (Nat.le_add_right r 28) _

end AdversarialBco.Bit.Transfer
