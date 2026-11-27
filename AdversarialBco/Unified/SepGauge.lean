/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.SepCM
public import AdversarialBco.Unified.SepMath

@[expose] public section

/-!
# UNI-GAUGE on the oracle machine

The gauge block `xgauge d L g TB` and its contract `gaugeBlockOK : GaugeBlockOK L XO ℓa ℓ g (xgauge d L g)`. The
bisection of `gaugeIt` in counters `l < u` (scalars `u`, `u + 1`), `j` turns: the midpoint `m = (l + u)/2` into
`u + 2`, the ray point `gaugePt a₀ x H j m` into array `atp` as `(D'; N')` with

* `D' = D Da (Hn m)`,
* `N'_i = Na_i α + N_i β`, `α = (Hn m - 2^j Hd) D`, `β = 2^j Hd Da`

(`gPt_runs`), the test block, then `l := m` on a reject and `u := m` on an accept. At the end `gout := u`.
-/

namespace AdversarialBco.Uni

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer

variable {d : ℕ}

/-! ## The ray point -/

/-- The ray point of the gauge as `N'/D'`. -/
theorem gaugePt_eq (Hn Hd D Da : ℤ) (j : ℕ) (m : ℕ) (N Na : Fin d → ℤ) (hHn : 0 < Hn) (hHd : 0 < Hd) (hD : 0 < D)
    (hDa : 0 < Da) (hm : 0 < m) (i : Fin d) :
    gaugePt (ptDN Da Na) (ptDN D N) ((Hn : ℚ) / Hd) j m i =
      ((Na i * ((Hn * m - 2 ^ j * Hd) * D) + N i * (2 ^ j * Hd * Da) : ℤ) : ℚ) / ((D * Da * (Hn * m) : ℤ) : ℚ) := by
  have h1 : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have h2 : (Da : ℚ) ≠ 0 := by exact_mod_cast hDa.ne'
  have h3 : (Hn : ℚ) ≠ 0 := by exact_mod_cast hHn.ne'
  have h4 : (Hd : ℚ) ≠ 0 := by exact_mod_cast hHd.ne'
  have h5 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [gaugePt, ptDN]
  push_cast
  field_simp
  ring

/-- The code of the ray point at the counter `m` in `u + 2`, from `D`, `Da`, `B = 2^j Hd`, `β` in `u + 4`, `u + 5`,
`u + 7`, `u + 9`: `A = Hn m` into `u + 6`, `α` into `u + 8`, `D'` into `u + 10` and `atp[0]`, then the numerators. -/
def xgPt (L : Layout) (g : GaugeLay) : XCmd :=
  .seq (toX (VL.sop2 L .mul (g.u + 6) g.cHn (g.u + 2)))
  (.seq (toX (VL.sop2 L .sub (g.u + 8) (g.u + 6) (g.u + 7)))
  (.seq (toX (VL.sop2 L .mul (g.u + 8) (g.u + 8) (g.u + 4)))
  (.seq (toX (VL.sop2 L .mul (g.u + 10) (g.u + 4) (g.u + 5)))
  (.seq (toX (VL.sop2 L .mul (g.u + 10) (g.u + 10) (g.u + 6)))
  (.seq (.prim (.frag (.nconst (g.n0 + 2) 0)))
  (.seq (toX (VL.aset L g.atp (g.n0 + 2) (g.u + 10)))
  (.seq (.prim (.frag (.nconst (g.n0 + 2) 1)))
    (.whileN (g.n0 + 2) (g.n0 + 3)
      (.seq (toX (VL.aget L (g.u + 11) g.aa (g.n0 + 2)))
      (.seq (toX (VL.sop2 L .mul (g.u + 11) (g.u + 11) (g.u + 8)))
      (.seq (toX (VL.aget L (g.u + 12) g.ax (g.n0 + 2)))
      (.seq (toX (VL.sop2 L .mul (g.u + 12) (g.u + 12) (g.u + 9)))
      (.seq (toX (VL.sop2 L .add (g.u + 11) (g.u + 11) (g.u + 12)))
      (.seq (toX (VL.aset L g.atp (g.n0 + 2) (g.u + 11)))
        (.prim (.frag (.nadd (g.n0 + 2) (g.n0 + 2) (g.n0 + 1))))))))))))))))))

/-- The scalars the code of the ray point writes. -/
def gPtS (g : GaugeLay) (y : ℕ) : Prop := y = g.u + 6 ∨ y = g.u + 8 ∨ y = g.u + 10 ∨ y = g.u + 11 ∨ y = g.u + 12

set_option maxHeartbeats 4000000 in
theorem gPt_runs {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ} (hL : LayOK L d ℓa) {g : GaugeLay} (hg : GaugeLay.OK L g)
    (hd : 1 ≤ d) {σ : Env d} {m Hn D Da B β : ℤ} {N Na : Fin d → ℤ} {E : ℕ}
    (hm : σ.sc (g.u + 2) = m) (hHn : σ.sc g.cHn = Hn) (hD : σ.sc (g.u + 4) = D) (hDa : σ.sc (g.u + 5) = Da)
    (hB : σ.sc (g.u + 7) = B) (hβ : σ.sc (g.u + 9) = β) (h1 : σ.nat (g.n0 + 1) = 1)
    (hd1 : σ.nat (g.n0 + 3) = d + 1)
    (hN : ∀ i : Fin d, σ.arr g.ax (1 + (i : ℕ)) = N i) (hNa : ∀ i : Fin d, σ.arr g.aa (1 + (i : ℕ)) = Na i)
    (b1 : |m| ≤ 2 ^ E) (b2 : |Hn| ≤ 2 ^ E) (b3 : |D| ≤ 2 ^ E) (b4 : |Da| ≤ 2 ^ E) (b5 : |B| ≤ 2 ^ E)
    (b6 : |β| ≤ 2 ^ E) (b7 : |Hn * m| ≤ 2 ^ E) (b8 : |Hn * m - B| ≤ 2 ^ E) (b9 : |(Hn * m - B) * D| ≤ 2 ^ E)
    (b10 : |D * Da| ≤ 2 ^ E) (b11 : |D * Da * (Hn * m)| ≤ 2 ^ E) (b12 : ∀ i, |Na i| ≤ 2 ^ E)
    (b13 : ∀ i, |N i| ≤ 2 ^ E) (b14 : ∀ i, |Na i * ((Hn * m - B) * D)| ≤ 2 ^ E) (b15 : ∀ i, |N i * β| ≤ 2 ^ E)
    (hE : E + 1 < ℓ) :
    XRunsB L X ℓa ℓ (xgPt L g) σ (9 + (d * (10 + 2) + 2)) (fun σ' =>
      σ'.arr g.atp 0 = ((D * Da * (Hn * m) : ℤ) : ℝ) ∧
      (∀ i : Fin d, σ'.arr g.atp (1 + (i : ℕ)) = ((Na i * ((Hn * m - B) * D) + N i * β : ℤ) : ℝ)) ∧
      σ'.draws = σ.draws ∧
      FrameA (gPtS g) (fun j => j = g.n0 + 2) (fun b _ => b = g.atp) σ σ') := by
  obtain ⟨⟨hax, haa, hatp⟩, ⟨htx, hta⟩, ⟨hs1, hs2, hs3, hs4, hs5⟩, ⟨hu1, hu2, hu3, hu4, -, -, -⟩,
    ⟨hn1, hn2, hn3⟩, ⟨hn4, hn5, hn6⟩⟩ := hg
  have bb : ∀ z : ℤ, |z| ≤ 2 ^ (E + 1) → |z| < 2 ^ ℓ := fun z hz =>
    lt_of_le_of_lt hz (pow_lt_pow_right₀ (by norm_num) hE)
  have bb' : ∀ z : ℤ, |z| ≤ 2 ^ E → |z| < 2 ^ ℓ := fun z hz => bb z (absI_mono hz (by omega))
  have hasz := asz_lt hL hax
  have h1a : 1 < 2 ^ ℓa := lt_of_le_of_lt (by unfold asz; nlinarith) hasz
  have hda : d + 1 < 2 ^ ℓa := lt_of_le_of_lt (by unfold asz; nlinarith) hasz
  refine XV.mono (K := 1 + (1 + (1 + (1 + (1 + (1 + (2 + (1 + ((d - 0) * (10 + 2) + 2))))))))) ?_ (by omega)
    (fun _ h => h)
  refine XV.seq (XV.mulI hL (x := g.u + 6) (a := g.cHn) (b := g.u + 2) (u := Hn) (v := m) (by omega) (by omega)
    (by omega) hHn hm (bb' _ b2) (bb' _ b1) (bb' _ b7)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.subI hL (x := g.u + 8) (a := g.u + 6) (b := g.u + 7) (u := Hn * m) (v := B) (by omega)
    (by omega) (by omega) (by simp) (by simp [hB]) (bb' _ b7) (bb' _ b5) (bb' _ b8)) fun σ2 e2 => ?_
  subst e2
  refine XV.seq (XV.mulI hL (x := g.u + 8) (a := g.u + 8) (b := g.u + 4) (u := Hn * m - B) (v := D) (by omega)
    (by omega) (by omega) (by simp) (by simp [hD]) (bb' _ b8) (bb' _ b3) (bb' _ b9)) fun σ3 e3 => ?_
  subst e3
  refine XV.seq (XV.mulI hL (x := g.u + 10) (a := g.u + 4) (b := g.u + 5) (u := D) (v := Da) (by omega)
    (by omega) (by omega) (by simp [hD]) (by simp [hDa]) (bb' _ b3) (bb' _ b4) (bb' _ b10)) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.mulI hL (x := g.u + 10) (a := g.u + 10) (b := g.u + 6) (u := D * Da) (v := Hn * m)
    (by omega) (by omega) (by omega) (by simp) (by simp) (bb' _ b10) (bb' _ b7) (bb' _ b11)) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.nconst hL (i := g.n0 + 2) (by omega) 0 (by omega)) fun σ6 e6 => ?_
  subst e6
  refine XV.seq (XV.aset hL (a := g.atp) (i := g.n0 + 2) (x := g.u + 10) hatp (by omega) (by omega)
    (by rw [Env.setNat_nat, ite_eq_left rfl]; unfold asz; nlinarith)
    (by rw [Env.setNat_sc, Env.setSc_sc, ite_eq_left rfl]; exact XV.abs_int_lt (bb' _ b11))) fun σ7 e7 => ?_
  subst e7
  refine XV.seq (XV.nconst hL (i := g.n0 + 2) (by omega) 1 h1a) fun σ8 e8 => ?_
  -- the state before the loop
  have f0 : σ8.arr g.atp 0 = ((D * Da * (Hn * m) : ℤ) : ℝ) := by rw [e8]; simp
  have f1 : σ8.nat (g.n0 + 2) = 1 := by rw [e8]; simp
  have f2 : σ8.nat (g.n0 + 1) = 1 := by rw [e8]; simp [h1]
  have f3 : σ8.nat (g.n0 + 3) = d + 1 := by rw [e8]; simp [hd1]
  have f4 : σ8.sc (g.u + 8) = (Hn * m - B) * D := by rw [e8]; simp
  have f5 : σ8.sc (g.u + 9) = β := by rw [e8]; simp [hβ]
  have f6 : ∀ i : Fin d, σ8.arr g.ax (1 + (i : ℕ)) = N i := fun i => by
    rw [e8]; simp [Ne.symm htx, hN i]
  have f7 : ∀ i : Fin d, σ8.arr g.aa (1 + (i : ℕ)) = Na i := fun i => by
    rw [e8]; simp [Ne.symm hta, hNa i]
  have f8 : σ8.draws = σ.draws := by rw [e8]; simp
  have F8 : FrameA (gPtS g) (fun j => j = g.n0 + 2) (fun b _ => b = g.atp) σ σ8 := by
    rw [e8]
    exact (FrameA.refl (gPtS g) (fun j => j = g.n0 + 2) (fun b _ => b = g.atp) σ).setSc
      (by simp [gPtS]) _ |>.setSc (by simp [gPtS]) _
      |>.setSc (by simp [gPtS]) _ |>.setSc (by simp [gPtS]) _ |>.setSc (by simp [gPtS]) _
      |>.setNat rfl _ |>.setArr rfl _ |>.setNat rfl _
  clear e8
  refine XV.mono (XV.whileN hL (i := g.n0 + 2) (j := g.n0 + 3) (by omega) (by omega)
    (fun t σ' => σ'.nat (g.n0 + 2) = 1 + t ∧ t ≤ d ∧ σ'.nat (g.n0 + 1) = 1 ∧ σ'.nat (g.n0 + 3) = d + 1 ∧
      (∀ i : Fin d, (i : ℕ) < t → σ'.arr g.atp (1 + (i : ℕ)) = ((Na i * ((Hn * m - B) * D) + N i * β : ℤ) : ℝ)) ∧
      σ'.draws = σ.draws ∧
      FrameA (fun y => y = g.u + 11 ∨ y = g.u + 12) (fun j => j = g.n0 + 2) (fun b k => b = g.atp ∧ 1 ≤ k) σ8 σ')
    d 10 (fun t σ' hI => by rw [hI.1, hI.2.2.2.1]; constructor <;> omega)
    (fun t σ' hI hc => by rw [hI.1, hI.2.2.2.1] at hc; omega) ?_ 0 σ8
    ⟨by rw [f1], Nat.zero_le _, f2, f3, fun i hi => absurd hi (Nat.not_lt_zero _), f8, FrameA.refl _ _ _ σ8⟩)
    le_rfl ?_
  · intro t σ' ⟨hr', htd, h1', hd1', hk', hd', hF'⟩ hc
    rw [hr', hd1'] at hc
    have ht : t < d := by omega
    have hidx : 1 + t < asz d := by unfold asz; nlinarith
    have hta' : 1 + t < 2 ^ ℓa := lt_trans hidx hasz
    have eα : σ'.sc (g.u + 8) = (Hn * m - B) * D := by rw [hF'.2.1 _ (by omega), f4]
    have eβ : σ'.sc (g.u + 9) = β := by rw [hF'.2.1 _ (by omega), f5]
    have eN : σ'.arr g.ax (1 + t) = N ⟨t, ht⟩ := by
      rw [hF'.2.2.1 _ _ (fun h => htx h.1.symm)]; exact f6 ⟨t, ht⟩
    have eNa : σ'.arr g.aa (1 + t) = Na ⟨t, ht⟩ := by
      rw [hF'.2.2.1 _ _ (fun h => hta h.1.symm)]; exact f7 ⟨t, ht⟩
    have bS := absI_add_le (b14 ⟨t, ht⟩) (b15 ⟨t, ht⟩)
    refine XV.mono (K := 2 + (1 + (2 + (1 + (1 + (2 + 1)))))) ?_ le_rfl (fun _ h => h)
    refine XV.seq (XV.aget hL (x := g.u + 11) (a := g.aa) (i := g.n0 + 2) (by omega) haa (by omega)
      (by rw [hr']; exact hidx) (by rw [hr', eNa]; exact XV.abs_int_lt (bb' _ (b12 _)))) fun σ1 e1 => ?_
    subst e1
    rw [hr', eNa]
    refine XV.seq (XV.mulI hL (x := g.u + 11) (a := g.u + 11) (b := g.u + 8) (u := Na ⟨t, ht⟩)
      (v := (Hn * m - B) * D) (by omega) (by omega) (by omega) (by simp) (by simp [eα]) (bb' _ (b12 _))
      (bb' _ b9) (bb' _ (b14 _))) fun σ2 e2 => ?_
    subst e2
    refine XV.seq (XV.aget hL (x := g.u + 12) (a := g.ax) (i := g.n0 + 2) (by omega) hax (by omega)
      (by simp only [Env.setSc_nat, hr']; exact hidx)
      (by simp only [Env.setSc_nat, Env.setSc_arr, hr', eN]; exact XV.abs_int_lt (bb' _ (b13 _)))) fun σ3 e3 => ?_
    subst e3
    simp only [Env.setSc_nat, Env.setSc_arr, hr', eN]
    refine XV.seq (XV.mulI hL (x := g.u + 12) (a := g.u + 12) (b := g.u + 9) (u := N ⟨t, ht⟩) (v := β)
      (by omega) (by omega) (by omega) (by simp) (by simp [eβ]) (bb' _ (b13 _)) (bb' _ b6) (bb' _ (b15 _)))
      fun σ4 e4 => ?_
    subst e4
    refine XV.seq (XV.addI hL (x := g.u + 11) (a := g.u + 11) (b := g.u + 12)
      (u := Na ⟨t, ht⟩ * ((Hn * m - B) * D)) (v := N ⟨t, ht⟩ * β) (by omega) (by omega) (by omega) (by simp)
      (by simp) (bb' _ (b14 _)) (bb' _ (b15 _)) (bb _ bS)) fun σ5 e5 => ?_
    subst e5
    refine XV.seq (XV.aset hL (a := g.atp) (i := g.n0 + 2) (x := g.u + 11) hatp (by omega) (by omega)
      (by simp only [Env.setSc_nat, hr']; exact hidx)
      (by rw [Env.setSc_sc, ite_eq_left rfl]; exact XV.abs_int_lt (bb _ bS))) fun σ6 e6 => ?_
    subst e6
    simp only [Env.setSc_nat, hr']
    refine XV.mono (XV.nadd hL (i := g.n0 + 2) (a := g.n0 + 2) (b := g.n0 + 1) (by omega) (by omega) (by omega)
      (by simp only [Env.setArr_nat, Env.setSc_nat, hr']; exact hta')
      (by simp only [Env.setArr_nat, Env.setSc_nat, h1']; omega)) le_rfl fun σ7 e7 => ?_
    subst e7
    refine ⟨by simp [hr', h1']; omega, by omega, by simp [h1'], by simp [hd1'], ?_, by simp [hd'], ?_⟩
    · intro i hi
      simp only [Env.setNat_arr, Env.setArr_arr]
      by_cases hit : (i : ℕ) = t
      · have hi' : i = ⟨t, ht⟩ := Fin.ext hit
        subst hi'
        simp
      · rw [ite_eq_right (by omega)]
        exact hk' i (by omega)
    · exact hF'.setSc (Or.inl rfl) _ |>.setSc (Or.inl rfl) _ |>.setSc (Or.inr rfl) _ |>.setSc (Or.inr rfl) _
        |>.setSc (Or.inl rfl) _ |>.setArr ⟨rfl, by omega⟩ _ |>.setNat rfl _
  · rintro σ' ⟨t', ⟨hr', htd, -, hd1', hk', hd', hF'⟩, hc⟩
    rw [hr', hd1'] at hc
    have ht : t' = d := by omega
    subst ht
    refine ⟨by rw [hF'.2.2.1 _ _ (fun h => by omega), f0], fun i => hk' i i.2, by rw [hd', ← f8], ?_⟩
    exact F8.trans (hF'.mono (fun y hy => by rcases hy with rfl | rfl <;> simp [gPtS]) (fun j hj => hj)
      (fun b k h => h.1))

/-! ## The bisection -/

theorem gaugeIt_succ (T : (Fin d → ℚ) → Bool) (a0 x : Fin d → ℚ) (H : ℚ) (j k : ℕ) :
    gaugeIt T a0 x H j (k + 1) =
      if T (gaugePt a0 x H j (((gaugeIt T a0 x H j k).1 + (gaugeIt T a0 x H j k).2) / 2)) then
        ((gaugeIt T a0 x H j k).1, ((gaugeIt T a0 x H j k).1 + (gaugeIt T a0 x H j k).2) / 2)
      else (((gaugeIt T a0 x H j k).1 + (gaugeIt T a0 x H j k).2) / 2, (gaugeIt T a0 x H j k).2) := rfl

theorem gaugeIt_le (T : (Fin d → ℚ) → Bool) (a0 x : Fin d → ℚ) (H : ℚ) (j : ℕ) :
    ∀ k ≤ j, (gaugeIt T a0 x H j k).1 ≤ (gaugeIt T a0 x H j k).2 ∧ (gaugeIt T a0 x H j k).2 ≤ 2 ^ j := by
  intro k
  induction k with
  | zero => intro _; simp [gaugeIt]
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [gaugeIt_succ]
    split_ifs <;> simp only <;> omega

/-! ## The code -/

/-- One turn: `m = (l + u)/2`, the ray point, the test, then `l := m` on a reject (`nt < 1`), `u := m` otherwise. -/
def xgBody (L : Layout) (g : GaugeLay) (TB : XCmdO) : XCmdO :=
  .seq (.base (.seq (toX (VL.sop2 L .add (g.u + 2) g.u (g.u + 1)))
    (.seq (xsidiv L (g.u + 2) (g.u + 2) (g.u + 3)) (xgPt L g))))
  (.seq TB
    (.ifN g.nt (g.n0 + 1)
      (.base (.seq (toX (VL.sop2 L .add g.u g.u (g.u + 1))) (xsidiv L g.u g.u (g.u + 3))))
      (.base (.seq (toX (VL.sop2 L .add (g.u + 1) g.u (g.u + 1))) (xsidiv L (g.u + 1) (g.u + 1) (g.u + 3))))))

end AdversarialBco.Uni
