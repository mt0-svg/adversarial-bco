/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.SepRun

@[expose] public section

/-!
# The SEP block, uniform in `d`

The block `xsepU L s EV` reads the dimension `d` from the natural register `0` (the register `rD` of the machine, which
holds `d` throughout) to bound its coordinate loops, in place of a constant `d` written into the text: one program text
for every `d`. Its contract `SepBlockOKU` is `SepBlockOK` with `σ.nat 0 = d`
in the data. The register `0` is read once, by the third instruction, before SEP writes any natural; the frame is that
of `SepBlockOK`, so a caller whose layout keeps `s.nok` and `s.n0, ..., s.n0 + 15` away from `0` keeps `d` there. The
units are those of SEP with a constant `d`: the load of `d` takes the place of the constant.
-/

namespace AdversarialBco.Uni

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer

variable {d : ℕ}

/-- The contract of a SEP block uniform in `d`: `SepBlockOK` with `d` in the register `0` at the start. -/
def SepBlockOKU (L : Layout) (XO : XCtxO d) (ℓa ℓ : ℕ) (s : SepLay) (sepc : XCmdO → XCmdO) : Prop :=
  ∀ (EV : XCmdO) (Dat : Env d → Prop) (evN : (Fin d → ℤ) → ℤ) (Kev bv : ℕ) (Sev Nev : ℕ → Prop)
    (Arev : ℕ → ℕ → Prop) (σ : Env d) (Y0 : Fin d → ℤ) (E e1 eτ eL eu bY : ℕ),
    LayOK L d ℓa → SepLay.OK L s → 1 ≤ d →
    EvalOK L XO ℓa ℓ EV Dat s.aev s.vout E (SepDom Y0 E e1) evN Kev Sev Nev Arev →
    (∀ X, SepDom Y0 E e1 X → |evN X| < 2 ^ bv) → SepDisj s Sev Nev Arev →
    Stable Dat (fun y => sepS s y ∨ Sev y) (fun j => sepN s j ∨ Nev j) (fun b k => sepAr s b k ∨ Arev b k) →
    Dat σ → σ.nat 0 = d →
    (∀ i : Fin d, σ.arr s.ay0 i = Y0 i) → (∀ i, |Y0 i| < 2 ^ bY) →
    σ.sc s.cE = 2 ^ E → σ.sc s.cL1 = 2 ^ (E - e1) → σ.sc s.cSh = 2 ^ (eτ + 4 + eL) →
    σ.sc s.cA = 2 ^ (E + eτ + 1) → σ.sc s.cB = 2 ^ eu → σ.nat s.nJ = eL + eτ + 3 →
    e1 + d * (2 * (eL + eτ + 3) + 6 + eτ + eL) ≤ E → E + eτ + eu + bY + bv + 8 ≤ ℓ → E + eτ + 8 < 2 ^ ℓa →
    XRunsBO L XO ℓa ℓ (sepc EV) σ (sepK d (eL + eτ + 3) Kev) (fun σ' =>
      SepOut s (sepE evN Y0 E e1 eτ eL eu) σ' ∧
        FrameA (fun y => sepS s y ∨ Sev y) (fun j => sepN s j ∨ Nev j) (fun b k => sepAr s b k ∨ Arev b k) σ σ' ∧
        σ'.draws = σ.draws)

/-- SEP's initialisation, the bound `d` of the loops loaded from the register `0`: `1`, `0`, then `d := r₀ + 0`, the
flag, `4`, `0`, `len`, `ay := ay0`, `i := 0`. -/
def xsInitU (L : Layout) (s : SepLay) : XCmd :=
  .seq (.prim (.frag (.nconst (s.n0 + 1) 1)))
  (.seq (.prim (.frag (.nconst (s.n0 + 8) 0)))
  (.seq (.prim (.frag (.nadd (s.n0 + 2) 0 (s.n0 + 8))))
  (.seq (.prim (.frag (.nconst s.nok 1)))
  (.seq (toX (VL.sconst L (s.u + 15) ((4 : ℤ) : ℚ)))
  (.seq (toX (VL.sconst L (s.u + 16) ((0 : ℤ) : ℚ)))
  (.seq (toX (VL.sop2 L .add s.u s.cL1 (s.u + 16)))
  (.seq (xforN s.n0 (s.n0 + 2) (s.n0 + 1)
      (.seq (toX (VL.aget L (s.u + 26) s.ay0 s.n0)) (toX (VL.aset L s.ay s.n0 (s.u + 26)))))
    (.prim (.frag (.nconst s.n0 0))))))))))

/-- The SEP block uniform in `d`, with the initialisation `xsInitU`. -/
def xsepU (L : Layout) (s : SepLay) (EV : XCmdO) : XCmdO :=
  .seq (.base (xsInitU L s))
  (.seq (.whileN s.n0 (s.n0 + 2) (xsCoord L s EV))
    (.ifN (s.n0 + 8) s.nok (xforNO s.n0 (s.n0 + 2) (s.n0 + 1) (xsGrad L s EV)) (.base .skip)))

variable {L : Layout} {s : SepLay} {Sev Nev : ℕ → Prop} {Arev : ℕ → ℕ → Prop} {σ0 : Env d}

set_option maxHeartbeats 16000000 in
theorem sInitU_runs {XO : XCtxO d} {ℓa ℓ : ℕ} {EV : XCmdO} {Dat : Env d → Prop} {evN : (Fin d → ℤ) → ℤ}
    {Kev bv : ℕ} {Y0 : Fin d → ℤ} {E e1 eτ eL eu bY : ℕ}
    (H : SEvH L XO ℓa ℓ s EV Dat evN Kev bv Sev Nev Arev Y0 E e1 σ0)
    (P : SepHyp s σ0 Y0 E e1 eτ eL eu bY bv ℓa ℓ) (h0 : σ0.nat 0 = d) (hay0 : ∀ i : Fin d, σ0.arr s.ay0 i = Y0 i) :
    XRunsB L XO.X ℓa ℓ (xsInitU L s) σ0 (1 + (1 + (1 + (1 + (1 + (1 + (1 + ((d * ((2 + 2) + 3) + 3) + 1))))))))
      (CInv s Sev Nev Arev σ0 evN Y0 E e1 eτ eL eu 0) := by
  obtain ⟨⟨h0a, hya, hga, hla, hea⟩, hne, ⟨hvo, hcEs, hL1s, hShs, hcAs, hcBs, hus⟩,
    ⟨-, hvu, hEu, hLu, hSu, hAu, hBu⟩, ⟨hnJs, hnoks, hn0s⟩, ⟨hJok, hJn, hokn⟩⟩ := H.hs
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne
  obtain ⟨⟨h0y, h0g, h0l, h0e⟩, ⟨hyg, hyl, hye⟩, ⟨hgl, hge⟩, hle⟩ := hne
  obtain ⟨dE, dJ⟩ := P.dE H.hd
  have hℓ := P.hℓ
  have hℓa := P.hℓa
  have hlt : ∀ t, t < d → t < asz d := fun t h => Nat.lt_of_lt_of_le h (Nat.le_add_left d (d * d))
  have bb : ∀ z : ℤ, ∀ e, |z| ≤ 2 ^ e → e ≤ E + eτ + eu + bY + bv + 7 → |z| < 2 ^ ℓ := fun z e hz he =>
    lt_of_le_of_lt (absI_mono hz he) (pow_lt_pow_right₀ (by norm_num) (by omega))
  have bY0 : ∀ m, |Y0 m| < 2 ^ ℓ := fun m => bb _ _ (P.Y0b m).le (by omega)
  refine XV.seq (XV.nconst H.hL (i := s.n0 + 1) (by omega) 1 (by omega)) fun σ1 e1 => ?_
  subst e1
  refine XV.seq (XV.nconst H.hL (i := s.n0 + 8) (by omega) 0 (by omega)) fun σ2 e2 => ?_
  subst e2
  have v3 : ((σ0.setNat (s.n0 + 1) 1).setNat (s.n0 + 8) 0).nat 0 +
      ((σ0.setNat (s.n0 + 1) 1).setNat (s.n0 + 8) 0).nat (s.n0 + 8) = d := by
    simp only [Env.setNat_nat, ↓reduceIte, show ¬ (0 : ℕ) = s.n0 + 8 by omega, show ¬ (0 : ℕ) = s.n0 + 1 by omega,
      h0, add_zero]
  refine XV.seq (XV.nadd H.hL (i := s.n0 + 2) (a := 0) (b := s.n0 + 8) (by omega) (by omega) (by omega)
    (by simp only [Env.setNat_nat, ↓reduceIte, show ¬ (0 : ℕ) = s.n0 + 8 by omega,
      show ¬ (0 : ℕ) = s.n0 + 1 by omega, h0]; omega) (by simp)) fun σ3 e3 => ?_
  rw [v3] at e3
  subst e3
  refine XV.seq (XV.nconst H.hL (i := s.nok) (by omega) 1 (by omega)) fun σ4 e4 => ?_
  subst e4
  refine XV.seq (XV.constI H.hL (x := s.u + 15) (by omega) 4 (bb _ 2 (by norm_num) (by omega))) fun σ5 e5 => ?_
  subst e5
  refine XV.seq (XV.constI H.hL (x := s.u + 16) (by omega) 0 (by simp)) fun σ6 e6 => ?_
  subst e6
  have b1 : |(2 : ℤ) ^ (E - e1)| ≤ 2 ^ (E - e1) := bound_two_pow _
  refine XV.seq (XV.addI H.hL (x := s.u) (a := s.cL1) (b := s.u + 16) (u := 2 ^ (E - e1)) (v := 0) (by omega)
    hL1s (by omega) (by simp [show s.cL1 ≠ s.u + 15 by omega, show s.cL1 ≠ s.u + 16 by omega, P.cL1]) (by simp)
    (bb _ _ b1 (by omega)) (by simp) (by simpa using bb _ _ b1 (by omega))) fun σ7 e7 => ?_
  subst e7
  have U7 : SepU s Sev Nev Arev σ0 _ := ((((((((FrameA.refl (fun y => sepS s y ∨ Sev y)
    (fun j => sepN s j ∨ Nev j) (fun b k => sepAr s b k ∨ Arev b k) σ0).setNat
    (i := s.n0 + 1) (Or.inl (Or.inr ⟨by omega, by omega⟩)) 1).setNat (i := s.n0 + 8) (Or.inl (Or.inr ⟨by omega, by omega⟩)) 0).setNat
    (i := s.n0 + 2) (Or.inl (Or.inr ⟨by omega, by omega⟩)) d).setNat (i := s.nok) (Or.inl (Or.inl rfl)) 1).setSc
    (x := s.u + 15) (Or.inl (Or.inr ⟨by omega, by omega⟩)) (((4 : ℤ) : ℝ))).setSc (x := s.u + 16) (Or.inl (Or.inr ⟨by omega, by omega⟩))
    (((0 : ℤ) : ℝ))).setSc (x := s.u) (Or.inl (Or.inr ⟨le_rfl, by omega⟩)) (((2 ^ (E - e1) + 0 : ℤ) : ℝ)))
  have SE7 : SEnv s Sev Nev Arev σ0 _ := ⟨by simp [show s.n0 + 1 ≠ s.nok by omega],
    by simp [show s.n0 + 2 ≠ s.nok by omega], by simp [show s.n0 + 8 ≠ s.nok by omega], by simp, by simp, U7,
    by simp⟩
  refine XV.seq (XV.forN H.hL (i := s.n0) (n := s.n0 + 2) (one := s.n0 + 1) (by omega) (by omega) (by omega)
    (by omega) (by omega) d (2 + 2) (by omega)
    (fun t σ' => SEnv s Sev Nev Arev σ0 σ' ∧ σ'.nat s.nok = 1 ∧ σ'.sc s.u = ((2 ^ (E - e1) : ℤ) : ℝ) ∧
      ∀ m : Fin d, (m : ℕ) < t → σ'.arr s.ay m = Y0 m) _ (by simp [show s.n0 + 2 ≠ s.nok by omega])
    (by simp [show s.n0 + 1 ≠ s.nok by omega]) ⟨SE7.setNat (Or.inr ⟨le_rfl, by omega⟩) (by omega) (by omega)
      (by omega) _, by simp [show s.nok ≠ s.n0 by omega], by simp, fun m hm => absurd hm (Nat.not_lt_zero _)⟩ ?_)
    fun σ8 ⟨⟨SE8, nok8, u8, ay8⟩, _, _, _⟩ => ?_
  · intro t ht σ' ⟨SE, nok1, hu, hay⟩ n0e n2e n1e
    have a0 : σ'.arr s.ay0 t = Y0 ⟨t, ht⟩ := by
      rw [(SE.U.keep H.hs H.hDisj).2.2.2.2.2.2 t]; exact hay0 ⟨t, ht⟩
    refine XV.seq (XV.aget H.hL (x := s.u + 26) (a := s.ay0) (i := s.n0) (by omega) h0a (by omega)
      (by rw [n0e]; exact hlt t ht) (by rw [n0e, a0]; exact XV.abs_int_lt (bY0 _))) fun σa ea => ?_
    subst ea
    refine XV.mono (XV.aset H.hL (a := s.ay) (i := s.n0) (x := s.u + 26) hya (by omega) (by omega)
      (by rw [Env.setSc_nat, n0e]; exact hlt t ht)
      (by rw [Env.setSc_sc, ite_eq_left rfl, n0e, a0]; exact XV.abs_int_lt (bY0 _))) le_rfl fun σb eb => ?_
    subst eb
    refine ⟨by simp [n0e], by simp [n2e], by simp [n1e], ?_⟩
    refine ⟨((SE.setSc (x := s.u + 26) (by omega) (by omega) (by omega) (by omega) _).setArr (Or.inl rfl) _).setNat
      (Or.inr ⟨le_rfl, by omega⟩) (by omega) (by omega) (by omega) _, by simp [show s.nok ≠ s.n0 by omega, nok1],
      by simp [hu], fun m hm => ?_⟩
    by_cases hmt : (m : ℕ) = t
    · have : m = ⟨t, ht⟩ := Fin.ext hmt
      subst this
      simp [n0e, a0]
    · simp [n0e, hmt, hay m (by omega)]
  refine XV.mono (XV.nconst H.hL (i := s.n0) (by omega) 0 (by omega)) le_rfl fun σ9 e9 => ?_
  subst e9
  refine ⟨SE8.setNat (Or.inr ⟨le_rfl, by omega⟩) (by omega) (by omega) (by omega) _, Or.inl ⟨by simp, Nat.zero_le _,
    by simp [show s.nok ≠ s.n0 by omega, nok8], (Y0, 2 ^ (E - e1), 0), rfl, sepDomInv_zero Y0 (by positivity),
    fun m => by simp [ay8 m m.2], by simp [u8], fun m hm => absurd hm (Nat.not_lt_zero _)⟩⟩
set_option maxHeartbeats 8000000 in
/-- The SEP block uniform in `d` meets its contract. -/
theorem sepBlockOKU (L : Layout) (XO : XCtxO d) (ℓa ℓ : ℕ) (s : SepLay) : SepBlockOKU L XO ℓa ℓ s (xsepU L s) := by
  intro EV Dat evN Kev bv Sev Nev Arev σ Y0 E e1 eτ eL eu bY hL hs hd hEV hbv hDisj hStab hD h0 hay0 hY0 hcE hcL1 hcSh
    hcA hcB hnJ hE hℓ hℓa
  have H : SEvH L XO ℓa ℓ s EV Dat evN Kev bv Sev Nev Arev Y0 E e1 σ := ⟨hL, hs, hd, hEV, hbv, hDisj, hStab, hD⟩
  have P : SepHyp s σ Y0 E e1 eτ eL eu bY bv ℓa ℓ := ⟨hY0, hcE, hcL1, hcSh, hcA, hcB, hnJ, hE, hℓ, hℓa⟩
  have hn := hs.nats
  have hnn := hs.nats_ne
  obtain ⟨dE, -⟩ := P.dE hd
  refine XVO.mono ?_ (sep_cost d (eL + eτ + 3) Kev) (fun _ h => h)
  refine XVO.seq (XVO.ofX (sInitU_runs H P h0 hay0)) fun σ1 hI1 => ?_
  refine XVO.seq (XVO.whileN hL (i := s.n0) (j := s.n0 + 2) (by omega) (by omega)
    (CInv s Sev Nev Arev σ evN Y0 E e1 eτ eL eu) d _ ?_ ?_ (fun t σ' hI hc => sCoord_runs H P hI hc) 0 σ1 hI1)
    fun σ2 ⟨t', ⟨SE2, hR2⟩, hc2⟩ => ?_
  · rintro t σ' ⟨SE, hR⟩
    rcases hR with ⟨n0e, htd, -⟩ | ⟨n0e, -⟩
    · rw [n0e, SE.nd]; omega
    · rw [n0e, SE.nd]; omega
  · rintro t σ' ⟨SE, hR⟩ hc
    rcases hR with ⟨n0e, htd, -⟩ | ⟨n0e, -⟩
    · rw [n0e, SE.nd] at hc; exact hc
    · rw [n0e, SE.nd] at hc; omega
  rcases hR2 with ⟨n0e, htd, nok1, st, hst, hDI, hay, hu, hadl⟩ | ⟨n0e, nok0, hnone⟩
  · have ht : t' = d := by rw [n0e, SE2.nd] at hc2; omega
    subst ht
    refine XVO.mono (XVO.ifN_t hL (i := s.n0 + 8) (j := s.nok) (by omega) (by omega) (by rw [SE2.nz]; omega)
      (by rw [nok1]; omega) (by rw [SE2.nz, nok1]; omega)
      (sGrads_runs H P hDI ⟨SE2, nok1, hay, hu, fun m => hadl m m.2, fun m hm => absurd hm (Nat.not_lt_zero _)⟩))
      (by omega) fun σ' ⟨SE', nok', hay', _, _, hag'⟩ => ⟨?_, SE'.U, SE'.dr⟩
    rw [sepE_eq, hst]
    exact ⟨nok', fun i => ⟨hay' i, hag' i i.2⟩⟩
  · refine XVO.mono (XVO.ifN_f hL (i := s.n0 + 8) (j := s.nok) (by omega) (by omega) (by rw [SE2.nz]; omega)
      (by rw [nok0]; omega) (by rw [SE2.nz, nok0]; omega) (XVO.ofX (XV.skip σ2))) (by omega)
      fun σ' e => ?_
    subst e
    refine ⟨?_, SE2.U, SE2.dr⟩
    rw [sepE_eq, hnone]
    exact nok0

end AdversarialBco.Uni
