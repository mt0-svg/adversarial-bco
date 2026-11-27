/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.SepBlock

@[expose] public section

/-!
# UNI-SEP on the oracle machine: the searches along the coordinates, the differences, the block

The SEP block `xsep d L s EV`: the constants and `Y := Y₀`, the searches of LINE along the coordinates `0, ..., d - 1`
(`sepCoordsZ`), then on success the differences `G_i` (`sepZ`); its contract `sepBlockOK : SepBlockOK L XO ℓa ℓ s
(xsep d L s)`.

The registers beyond those of LINE (SepBlock.lean): `nok` the flag of SEP, `u + 26`, `u + 27`, `u + 28` the scratch of
the update and of the differences.
-/

namespace AdversarialBco.Uni

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer

variable {d : ℕ}

/-! ## The domain of the searches -/

/-- The searches after `k` coordinates: the point moved along the first `k` coordinates only, each by at most `L₁`, the
length in `[0, L₁]`, the scales of the first `k` coordinates in `[0, L₁/4]`. -/
def SepDomInv (Y0 : Fin d → ℤ) (L1 : ℤ) (k : ℕ) (st : SepStZ d) : Prop :=
  (∀ m : Fin d, |st.1 m - Y0 m| ≤ L1) ∧ (∀ m : Fin d, k ≤ (m : ℕ) → st.1 m = Y0 m) ∧ 0 ≤ st.2.1 ∧ st.2.1 ≤ L1 ∧
    ∀ m : Fin d, (m : ℕ) < k → 0 ≤ st.2.2 m ∧ 4 * st.2.2 m ≤ L1

theorem sepDomInv_zero (Y0 : Fin d → ℤ) {L1 : ℤ} (h : 0 ≤ L1) : SepDomInv Y0 L1 0 (Y0, L1, 0) :=
  ⟨fun m => by simp [h], fun _ _ => rfl, h, le_rfl, fun _ hm => absurd hm (Nat.not_lt_zero _)⟩

theorem sepDom_line {Y0 : Fin d → ℤ} {E e1 k : ℕ} {st : SepStZ d} (hI : SepDomInv Y0 (2 ^ (E - e1)) k st)
    (i : Fin d) (hik : (i : ℕ) = k) (t : ℤ) (h0 : 0 ≤ t) (h1 : t ≤ st.2.1) : SepDom Y0 E e1 (st.1 + t • eZ i) := by
  obtain ⟨hY, hY0, -, hl1, -⟩ := hI
  intro m
  rw [eZ_apply]
  have hp : (0 : ℤ) ≤ 2 ^ (E - e1) := by positivity
  split_ifs with hm
  · subst hm
    rw [hY0 m (by omega), show Y0 m + t - Y0 m = t by ring, abs_of_nonneg h0]
    linarith
  · linarith [hY m]

theorem sepDom_grad {Y0 : Fin d → ℤ} {E e1 k : ℕ} {st : SepStZ d} (hI : SepDomInv Y0 (2 ^ (E - e1)) k st)
    (i : Fin d) (c : ℤ) (hc : |c| ≤ 2 ^ (E - e1)) : SepDom Y0 E e1 (st.1 + c • eZ i) := by
  obtain ⟨hY, -, -, -, -⟩ := hI
  intro m
  rw [eZ_apply]
  have hp : (0 : ℤ) ≤ 2 ^ (E - e1) := by positivity
  split_ifs with hm
  · rw [show st.1 m + c - Y0 m = (st.1 m - Y0 m) + c by ring]
    linarith [abs_add_le (st.1 m - Y0 m) c, hY m]
  · linarith [hY m]

theorem sepCoordZ_eq (evN : (Fin d → ℤ) → ℤ) (sh cA cB : ℤ) (J : ℕ) (i : Fin d) (st : SepStZ d) :
    sepCoordZ evN sh cA cB J i st = lineZ (fun t => evN (st.1 + t • eZ i)) st.2.1 cA cB J >>= fun r =>
      some (st.1 + r.1 • eZ i, r.2 / sh, Function.update st.2.2 i r.2) := rfl

theorem sepDomInv_step {evN : (Fin d → ℤ) → ℤ} {Y0 : Fin d → ℤ} {E e1 k bv : ℕ} {sh cA cB : ℤ} {J : ℕ}
    (hsh : 1 ≤ sh) (hbv : ∀ X, SepDom Y0 E e1 X → |evN X| < 2 ^ bv) {st st' : SepStZ d}
    (hI : SepDomInv Y0 (2 ^ (E - e1)) k st) (i : Fin d) (hik : (i : ℕ) = k)
    (h : sepCoordZ evN sh cA cB J i st = some st') : SepDomInv Y0 (2 ^ (E - e1)) (k + 1) st' := by
  rw [sepCoordZ_eq] at h
  cases hr : lineZ (fun t => evN (st.1 + t • eZ i)) st.2.1 cA cB J with
  | none => rw [hr] at h; simp at h
  | some r =>
    rw [hr] at h
    simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
    subst h
    have hI' := hI
    obtain ⟨hY, hY0, hl0, hl1, hΔ⟩ := hI'
    obtain ⟨r1, r2, r3, r4⟩ := lineZ_bound (fun t h0 h1 => hbv _ (sepDom_line hI i hik t h0 h1)) hl0 cA cB J r hr
    refine ⟨fun m => ?_, fun m hm => ?_, ?_, ?_, fun m hm => ?_⟩
    · simp only
      rw [eZ_apply]
      split_ifs with hmi
      · subst hmi
        rw [hY0 m (by omega), show Y0 m + r.1 - Y0 m = r.1 by ring, abs_of_nonneg r1]
        linarith
      · exact hY m
    · simp only
      rw [eZ_apply, ite_eq_right (fun e => by subst e; omega)]
      exact hY0 m (by omega)
    · exact Int.ediv_nonneg r3 (by omega)
    · simp only
      have : r.2 / sh ≤ r.2 := Int.ediv_le_self _ r3
      linarith
    · simp only [Function.update_apply]
      split_ifs with hmi
      · exact ⟨r3, by linarith⟩
      · exact hΔ m (by have : (m : ℕ) ≠ k := fun e => hmi (Fin.ext (e.trans hik.symm)); omega)

theorem sepCoordsZ_none {evN : (Fin d → ℤ) → ℤ} {Y0 : Fin d → ℤ} {len1 sh cA cB : ℤ} {J k : ℕ}
    (h : sepCoordsZ evN Y0 len1 sh cA cB J k = none) : ∀ k', k ≤ k' → sepCoordsZ evN Y0 len1 sh cA cB J k' = none := by
  intro k' hk
  induction k' with
  | zero => have : k = 0 := by omega
            subst this; exact h
  | succ k' ih =>
    rcases Nat.lt_or_ge k (k' + 1) with hlt | hge
    · rw [sepCoordsZ, ih (by omega)]; rfl
    · have : k = k' + 1 := by omega
      subst this; exact h

theorem sepCoordsZ_succ {evN : (Fin d → ℤ) → ℤ} {Y0 : Fin d → ℤ} {len1 sh cA cB : ℤ} {J k : ℕ} (hk : k < d)
    {st : SepStZ d} (h : sepCoordsZ evN Y0 len1 sh cA cB J k = some st) :
    sepCoordsZ evN Y0 len1 sh cA cB J (k + 1) = sepCoordZ evN sh cA cB J ⟨k, hk⟩ st := by
  rw [sepCoordsZ, h, Option.bind_eq_bind, Option.bind_some, dite_eq_left hk]

/-! ## What SEP reads and never writes -/

/-- The constants of SEP in its registers, its frame and the draws. -/
structure SEnv (s : SepLay) (Sev Nev : ℕ → Prop) (Arev : ℕ → ℕ → Prop) (σ0 σ : Env d) : Prop where
  n1 : σ.nat (s.n0 + 1) = 1
  nd : σ.nat (s.n0 + 2) = d
  nz : σ.nat (s.n0 + 8) = 0
  four : σ.sc (s.u + 15) = 4
  zero : σ.sc (s.u + 16) = 0
  U : SepU s Sev Nev Arev σ0 σ
  dr : σ.draws = σ0.draws

variable {L : Layout} {s : SepLay} {Sev Nev : ℕ → Prop} {Arev : ℕ → ℕ → Prop} {σ0 : Env d}

theorem SEnv.ofL {i : Fin d} {J E eτ eu : ℕ} {len : ℤ} {Y : Fin d → ℤ} {σ : Env d}
    (h : LEnv s Sev Nev Arev σ0 i J E eτ eu len Y σ) : SEnv s Sev Nev Arev σ0 σ :=
  ⟨h.n1, h.nd, h.nz, h.four, h.zero, h.U, h.dr⟩

theorem SEnv.setSc {σ : Env d} (h : SEnv s Sev Nev Arev σ0 σ) {x : ℕ} (hx1 : s.u ≤ x) (hx2 : x < s.u + 48)
    (hx3 : x ≠ s.u + 15) (hx4 : x ≠ s.u + 16) (v : ℝ) : SEnv s Sev Nev Arev σ0 (σ.setSc x v) :=
  ⟨by simp [h.n1], by simp [h.nd], by simp [h.nz], by simp [Ne.symm hx3, h.four], by simp [Ne.symm hx4, h.zero],
    h.U.setSc (Or.inl (Or.inr ⟨hx1, hx2⟩)) v, by simp [h.dr]⟩

theorem SEnv.setNat {σ : Env d} (h : SEnv s Sev Nev Arev σ0 σ) {j : ℕ} (hj : j = s.nok ∨ (s.n0 ≤ j ∧ j < s.n0 + 16))
    (hj1 : j ≠ s.n0 + 1) (hj2 : j ≠ s.n0 + 2) (hj8 : j ≠ s.n0 + 8) (v : ℕ) :
    SEnv s Sev Nev Arev σ0 (σ.setNat j v) :=
  ⟨by simp [Ne.symm hj1, h.n1], by simp [Ne.symm hj2, h.nd], by simp [Ne.symm hj8, h.nz], by simp [h.four],
    by simp [h.zero], h.U.setNat (Or.inl hj) v, by simp [h.dr]⟩

theorem SEnv.setArr {σ : Env d} (h : SEnv s Sev Nev Arev σ0 σ) {b k : ℕ} (hb : sepAr s b k) (v : ℝ) :
    SEnv s Sev Nev Arev σ0 (σ.setArr b k v) :=
  ⟨by simp [h.n1], by simp [h.nd], by simp [h.nz], by simp [h.four], by simp [h.zero], h.U.setArr (Or.inl hb) v,
    by simp [h.dr]⟩

/-- The cells SEP reads and never writes, kept by its frame. -/
theorem SepU.keep (hs : SepLay.OK L s) (hD : SepDisj s Sev Nev Arev) {σ : Env d}
    (hU : SepU s Sev Nev Arev σ0 σ) :
    σ.sc s.cE = σ0.sc s.cE ∧ σ.sc s.cL1 = σ0.sc s.cL1 ∧ σ.sc s.cSh = σ0.sc s.cSh ∧ σ.sc s.cA = σ0.sc s.cA ∧
      σ.sc s.cB = σ0.sc s.cB ∧ σ.nat s.nJ = σ0.nat s.nJ ∧ ∀ k, σ.arr s.ay0 k = σ0.arr s.ay0 k := by
  obtain ⟨dS, dN, dA⟩ := hD
  obtain ⟨-, hne, -, ⟨hsne, hvu, hEu, hLu, hSu, hAu, hBu⟩, -, ⟨hJok, hJn, -⟩⟩ := hs
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne hsne
  obtain ⟨⟨h0y, h0g, h0l, h0e⟩, -⟩ := hne
  obtain ⟨⟨hvE, hvL, hvS, hvA, hvB⟩, -⟩ := hsne
  have kS : ∀ y, y ≠ s.vout → y < s.u → ¬ Sev y → σ.sc y = σ0.sc y := fun y h1 h2 h3 =>
    hU.2.1 y (fun h => by
      rcases h with (h | h) | h
      · exact h1 h
      · omega
      · exact h3 h)
  refine ⟨kS _ (Ne.symm hvE) hEu (fun h => (dS _ h).1 rfl), kS _ (Ne.symm hvL) hLu (fun h => (dS _ h).2.1 rfl),
    kS _ (Ne.symm hvS) hSu (fun h => (dS _ h).2.2.1 rfl), kS _ (Ne.symm hvA) hAu (fun h => (dS _ h).2.2.2.1 rfl),
    kS _ (Ne.symm hvB) hBu (fun h => (dS _ h).2.2.2.2.1 rfl), ?_, fun k => ?_⟩
  · refine hU.1 _ (fun h => ?_)
    rcases h with (h | h) | h
    · exact hJok h
    · omega
    · exact (dN _ h).1 rfl
  · refine hU.2.2.1 _ _ (fun h => ?_)
    rcases h with (h | h | h | h) | h
    · exact h0y h
    · exact h0g h
    · exact h0l h
    · exact h0e h
    · exact (dA _ _ h).1 rfl

/-! ## One coordinate -/

/-- On success of LINE: `ay[i] += s`, `adl[i] := δ`, `len := δ / cSh`, `i := i + 1`. -/
def xsUpd (L : Layout) (s : SepLay) : XCmd :=
  .seq (toX (VL.aget L (s.u + 26) s.ay s.n0))
  (.seq (toX (VL.sop2 L .add (s.u + 26) (s.u + 26) (s.u + 19)))
  (.seq (toX (VL.aset L s.ay s.n0 (s.u + 26)))
  (.seq (toX (VL.aset L s.adl s.n0 (s.u + 20)))
  (.seq (xsidiv L s.u (s.u + 20) s.cSh)
    (.prim (.frag (.nadd s.n0 s.n0 (s.n0 + 1))))))))

/-- On failure of LINE: the flag `nok := 0`, `i := d`. -/
def xsFailC (L : Layout) (s : SepLay) : XCmd :=
  .seq (.prim (.frag (.nconst s.nok 0))) (.prim (.frag (.nadd s.n0 (s.n0 + 2) (s.n0 + 8))))

/-- The search along the coordinate `i` (in `n0`). -/
def xsCoord (L : Layout) (s : SepLay) (EV : XCmdO) : XCmdO :=
  .seq (xsLine L s EV) (.ifN (s.n0 + 8) (s.n0 + 7) (.base (xsUpd L s)) (.base (xsFailC L s)))

/-- The searches after `t` turns: running at the coordinate `t` with the state of `sepCoordsZ` in the registers, or
stopped at a failure. -/
def CInv (s : SepLay) (Sev Nev : ℕ → Prop) (Arev : ℕ → ℕ → Prop) (σ0 : Env d) (evN : (Fin d → ℤ) → ℤ)
    (Y0 : Fin d → ℤ) (E e1 eτ eL eu : ℕ) (t : ℕ) (σ : Env d) : Prop :=
  SEnv s Sev Nev Arev σ0 σ ∧
    ((σ.nat s.n0 = t ∧ t ≤ d ∧ σ.nat s.nok = 1 ∧ ∃ st,
      sepCoordsZ evN Y0 (2 ^ (E - e1)) (2 ^ (eτ + 4 + eL)) (2 ^ (E + eτ + 1)) (2 ^ eu) (eL + eτ + 3) t = some st ∧
      SepDomInv Y0 (2 ^ (E - e1)) t st ∧ (∀ m : Fin d, σ.arr s.ay m = st.1 m) ∧ σ.sc s.u = st.2.1 ∧
      ∀ m : Fin d, (m : ℕ) < t → σ.arr s.adl m = st.2.2 m) ∨
     (σ.nat s.n0 = d ∧ σ.nat s.nok = 0 ∧
      sepCoordsZ evN Y0 (2 ^ (E - e1)) (2 ^ (eτ + 4 + eL)) (2 ^ (E + eτ + 1)) (2 ^ eu) (eL + eτ + 3) d = none))

/-- The hypotheses of the SEP contract on the exponents and the constants. -/
structure SepHyp (s : SepLay) (σ0 : Env d) (Y0 : Fin d → ℤ) (E e1 eτ eL eu bY bv ℓa ℓ : ℕ) : Prop where
  Y0b : ∀ i, |Y0 i| < 2 ^ bY
  cE : σ0.sc s.cE = 2 ^ E
  cL1 : σ0.sc s.cL1 = 2 ^ (E - e1)
  cSh : σ0.sc s.cSh = 2 ^ (eτ + 4 + eL)
  cA : σ0.sc s.cA = 2 ^ (E + eτ + 1)
  cB : σ0.sc s.cB = 2 ^ eu
  nJ : σ0.nat s.nJ = eL + eτ + 3
  hE : e1 + d * (2 * (eL + eτ + 3) + 6 + eτ + eL) ≤ E
  hℓ : E + eτ + eu + bY + bv + 8 ≤ ℓ
  hℓa : E + eτ + 8 < 2 ^ ℓa

theorem SepHyp.dE {Y0 : Fin d → ℤ} {σ : Env d} {E e1 eτ eL eu bY bv ℓa ℓ : ℕ}
    (h : SepHyp s σ Y0 E e1 eτ eL eu bY bv ℓa ℓ) (hd : 1 ≤ d) : d ≤ E ∧ eL + eτ + 3 + 1 ≤ E := by
  have h1 := h.hE
  have h2 : d * 1 ≤ d * (2 * (eL + eτ + 3) + 6 + eτ + eL) := Nat.mul_le_mul_left _ (by omega)
  have h3 : 1 * (2 * (eL + eτ + 3) + 6 + eτ + eL) ≤ d * (2 * (eL + eτ + 3) + 6 + eτ + eL) :=
    Nat.mul_le_mul_right _ hd
  omega

theorem sepDomInv_bound {Y0 : Fin d → ℤ} {E e1 k bY Bm : ℕ} {st : SepStZ d} (hI : SepDomInv Y0 (2 ^ (E - e1)) k st)
    (hY0 : ∀ i, |Y0 i| < 2 ^ bY) (h1 : bY ≤ Bm) (h2 : E ≤ Bm) : ∀ m, |st.1 m| ≤ 2 ^ (Bm + 1) := fun m => by
  have a := absI_add_le (absI_mono (hY0 m).le h1) (absI_mono (hI.1 m) (by omega : E - e1 ≤ Bm))
  rwa [show Y0 m + (st.1 m - Y0 m) = st.1 m by ring] at a

theorem sepCoordsZ_succ' {evN : (Fin d → ℤ) → ℤ} {Y0 : Fin d → ℤ} {len1 sh cA cB : ℤ} {J k : ℕ} (i : Fin d)
    (hik : (i : ℕ) = k) {st : SepStZ d} (h : sepCoordsZ evN Y0 len1 sh cA cB J k = some st) :
    sepCoordsZ evN Y0 len1 sh cA cB J (k + 1) = sepCoordZ evN sh cA cB J i st := by
  subst hik
  exact sepCoordsZ_succ i.2 h

set_option maxHeartbeats 16000000 in
theorem sCoord_runs {XO : XCtxO d} {ℓa ℓ : ℕ} {EV : XCmdO} {Dat : Env d → Prop} {evN : (Fin d → ℤ) → ℤ}
    {Kev bv : ℕ} {Y0 : Fin d → ℤ} {E e1 eτ eL eu bY : ℕ}
    (H : SEvH L XO ℓa ℓ s EV Dat evN Kev bv Sev Nev Arev Y0 E e1 σ0)
    (P : SepHyp s σ0 Y0 E e1 eτ eL eu bY bv ℓa ℓ) {t : ℕ} {σ : Env d}
    (hI : CInv s Sev Nev Arev σ0 evN Y0 E e1 eτ eL eu t σ) (hc : σ.nat s.n0 < σ.nat (s.n0 + 2)) :
    XRunsBO L XO ℓa ℓ (xsCoord L s EV) σ (sLK d (eL + eτ + 3) Kev + (9 + 2))
      (CInv s Sev Nev Arev σ0 evN Y0 E e1 eτ eL eu (t + 1)) := by
  obtain ⟨⟨h0a, hya, hga, hla, hea⟩, hne, ⟨hvo, hcEs, hL1s, hShs, hcAs, hcBs, hus⟩,
    ⟨-, hvu, hEu, hLu, hSu, hAu, hBu⟩, ⟨hnJs, hnoks, hn0s⟩, ⟨hJok, hJn, hokn⟩⟩ := H.hs
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne
  obtain ⟨⟨h0y, h0g, h0l, h0e⟩, ⟨hyg, hyl, hye⟩, ⟨hgl, hge⟩, hle⟩ := hne
  obtain ⟨dE, dJ⟩ := P.dE H.hd
  have hℓ := P.hℓ
  have hℓa := P.hℓa
  obtain ⟨SE, hR⟩ := hI
  rcases hR with ⟨n0e, htd, nok1, st, hst, hDI, hay, hu, hadl⟩ | ⟨n0e, -, -⟩
  swap
  · rw [n0e, SE.nd] at hc; omega
  rw [n0e, SE.nd] at hc
  obtain ⟨i, hi⟩ : ∃ i : Fin d, (i : ℕ) = t := ⟨⟨t, hc⟩, rfl⟩
  obtain ⟨kE, -, -, kA, kB, kJ, -⟩ := SE.U.keep H.hs H.hDisj
  have LE : LEnv s Sev Nev Arev σ0 i (eL + eτ + 3) E eτ eu st.2.1 st.1 σ :=
    ⟨n0e.trans hi.symm, SE.n1, SE.nd, SE.nz, by rw [kJ, P.nJ], by rw [kE, P.cE], by rw [kA, P.cA],
      by rw [kB, P.cB], hu, SE.four, SE.zero, hay, SE.U, SE.dr⟩
  have bY' := sepDomInv_bound (Bm := E + eτ + eu + bY + bv + 4) hDI P.Y0b (by omega) (by omega)
  have hl0 := hDI.2.2.1
  have hlE : st.2.1 ≤ 2 ^ E := hDI.2.2.2.1.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have bb : ∀ z : ℤ, |z| ≤ 2 ^ (E + eτ + eu + bY + bv + 4 + 1) → |z| < 2 ^ ℓ := fun z hz =>
    lt_of_le_of_lt hz (pow_lt_pow_right₀ (by norm_num) (by omega))
  have bt : ∀ z : ℤ, 0 ≤ z → z ≤ st.2.1 → |z| ≤ 2 ^ (E + eτ + eu + bY + bv + 4 + 1) := fun z h0 h1 =>
    bound_of_le h0 h1 hlE (by omega)
  have hlt : t < asz d := Nat.lt_of_lt_of_le hc (Nat.le_add_left d (d * d))
  refine XVO.seq (sLine_runs H LE hl0 hlE (sepDom_line hDI i hi) bY' (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)) fun σ1 ⟨hO, E1, kA1⟩ => ?_
  have n01 : σ1.nat s.n0 = t := E1.ni.trans hi
  have nok1' : σ1.nat s.nok = 1 := by rw [kA1.1, nok1]
  have SE1 := SEnv.ofL E1
  have hcSh1 : σ1.sc s.cSh = ((2 ^ (eτ + 4 + eL) : ℤ) : ℝ) := by
    rw [(E1.U.keep H.hs H.hDisj).2.2.1, P.cSh]; norm_num
  cases hR : lineZ (fun t => evN (st.1 + t • eZ i)) st.2.1 (2 ^ (E + eτ + 1)) (2 ^ eu) (eL + eτ + 3) with
  | none =>
    have f0 := hO.1 hR
    refine XVO.ifN H.hL (i := s.n0 + 8) (j := s.n0 + 7) (K := 9) (by omega) (by omega) (by rw [E1.nz]; omega)
      (by rw [f0]; omega) (fun hc' => by rw [E1.nz, f0] at hc'; omega) (fun _ => ?_)
    refine XVO.mono (K := 1 + 1) (XVO.ofX ?_) (by omega) (fun _ h => h)
    refine XV.seq (XV.nconst H.hL (i := s.nok) (by omega) 0 (by omega)) fun σ2 e2 => ?_
    subst e2
    refine XV.mono (XV.nadd H.hL (i := s.n0) (a := s.n0 + 2) (b := s.n0 + 8) (by omega) (by omega) (by omega)
      (lt_of_eq_of_lt (by simp [show s.n0 + 2 ≠ s.nok by omega, E1.nd]) (show d < 2 ^ ℓa by omega))
      (lt_of_eq_of_lt (by simp [show s.n0 + 8 ≠ s.nok by omega, E1.nz]) (show 0 < 2 ^ ℓa by omega))) le_rfl
      fun σ3 e3 => ?_
    subst e3
    have hnone : sepCoordsZ evN Y0 (2 ^ (E - e1)) (2 ^ (eτ + 4 + eL)) (2 ^ (E + eτ + 1)) (2 ^ eu) (eL + eτ + 3)
        (t + 1) = none := by
      rw [sepCoordsZ_succ' i hi hst, sepCoordZ_eq, hR]; rfl
    refine ⟨(SE1.setNat (Or.inl rfl) (by omega) (by omega) (by omega) _).setNat (Or.inr ⟨le_rfl, by omega⟩)
      (by omega) (by omega) (by omega) _, Or.inr ⟨?_, by simp [show s.nok ≠ s.n0 by omega], sepCoordsZ_none hnone d
      (by omega)⟩⟩
    simp [show s.n0 + 2 ≠ s.nok by omega, show s.n0 + 8 ≠ s.nok by omega, E1.nd, E1.nz]
  | some r =>
    obtain ⟨f1, f19, f20⟩ := hO.2 r hR
    obtain ⟨r1, r2, r3, r4⟩ :=
      lineZ_bound (fun t h0 h1 => H.hbv _ (sepDom_line hDI i hi t h0 h1)) hl0 _ _ _ r hR
    have hst' : sepCoordZ evN (2 ^ (eτ + 4 + eL)) (2 ^ (E + eτ + 1)) (2 ^ eu) (eL + eτ + 3) i st =
        some (st.1 + r.1 • eZ i, r.2 / 2 ^ (eτ + 4 + eL), Function.update st.2.2 i r.2) := by
      rw [sepCoordZ_eq, hR]; rfl
    have hDI' := sepDomInv_step (one_le_pow₀ (by norm_num)) H.hbv hDI i hi hst'
    have bnew : |st.1 i + r.1| ≤ 2 ^ (E + eτ + eu + bY + bv + 4 + 1) := by
      have := sepDomInv_bound (Bm := E + eτ + eu + bY + bv + 4) hDI' P.Y0b (by omega) (by omega) i
      simp only at this
      rwa [eZ_apply, ite_eq_left rfl] at this
    have ay1 : σ1.arr s.ay t = st.1 i := by rw [← hi]; exact E1.ay i
    refine XVO.ifN H.hL (i := s.n0 + 8) (j := s.n0 + 7) (K := 9) (by omega) (by omega) (by rw [E1.nz]; omega)
      (by rw [f1]; omega) (fun _ => ?_) (fun hc' => absurd (by rw [E1.nz, f1]; omega) hc')
    refine XVO.mono (K := 2 + (1 + (2 + (2 + (1 + 1))))) (XVO.ofX ?_) (by omega) (fun _ h => h)
    refine XV.seq (XV.aget H.hL (x := s.u + 26) (a := s.ay) (i := s.n0) (by omega) hya (by omega)
      (by rw [n01]; exact hlt) (by rw [n01, ay1]; exact XV.abs_int_lt (bb _ (bY' i)))) fun σ2 e2 => ?_
    subst e2
    refine XV.seq (XV.addI H.hL (x := s.u + 26) (a := s.u + 26) (b := s.u + 19) (u := st.1 i) (v := r.1)
      (by omega) (by omega) (by omega) (by simp [n01, ay1]) (by simp [f19]) (bb _ (bY' i))
      (bb _ (bt _ r1 r2)) (bb _ bnew)) fun σ3 e3 => ?_
    subst e3
    refine XV.seq (XV.aset H.hL (a := s.ay) (i := s.n0) (x := s.u + 26) hya (by omega) (by omega)
      (by rw [Env.setSc_nat, Env.setSc_nat, n01]; exact hlt)
      (by rw [Env.setSc_sc, ite_eq_left rfl]; exact XV.abs_int_lt (bb _ bnew))) fun σ4 e4 => ?_
    subst e4
    refine XV.seq (XV.aset H.hL (a := s.adl) (i := s.n0) (x := s.u + 20) hla (by omega) (by omega)
      (by simp only [Env.setArr_nat, Env.setSc_nat, n01]; exact hlt)
      (by simpa [f20] using XV.abs_int_lt (bb _ (bt _ r3 (by omega))))) fun σ5 e5 => ?_
    subst e5
    have bsh : |(2 : ℤ) ^ (eτ + 4 + eL)| ≤ 2 ^ (E + eτ + eu + bY + bv + 4 + 1) :=
      absI_mono (bound_two_pow _) (by omega)
    refine XV.seq (XV.divI H.hL (x := s.u) (a := s.u + 20) (b := s.cSh) (u := r.2) (v := 2 ^ (eτ + 4 + eL))
      (by omega) (by omega) hShs (by simp [f20]) (by simp [show s.cSh ≠ s.u + 26 by omega, hcSh1])
      (bb _ (bt _ r3 (by omega))) (bb _ bsh)) fun σ6 e6 => ?_
    subst e6
    refine XV.mono (XV.nadd H.hL (i := s.n0) (a := s.n0) (b := s.n0 + 1) (by omega) (by omega) (by omega)
      (lt_of_eq_of_lt (by simp [n01]) (show t < 2 ^ ℓa by omega))
      (lt_of_eq_of_lt (by simp [E1.n1]) (show 1 < 2 ^ ℓa by omega))) le_rfl fun σ7 e7 => ?_
    subst e7
    refine ⟨((((((SE1.setSc (x := s.u + 26) (by omega) (by omega) (by omega) (by omega) _).setSc (x := s.u + 26)
      (by omega) (by omega) (by omega) (by omega) _).setArr (Or.inl rfl) _).setArr
      (Or.inr (Or.inr (Or.inl rfl))) _).setSc (x := s.u) (by omega) (by omega) (by omega) (by omega) _).setNat
      (Or.inr ⟨le_rfl, by omega⟩) (by omega) (by omega) (by omega) _),
      Or.inl ⟨by simp [n01, E1.n1], by omega, by simp [show s.nok ≠ s.n0 by omega, nok1'], _,
        (sepCoordsZ_succ' i hi hst).trans hst', hDI', fun m => ?_, by simp, fun m hm => ?_⟩⟩
    · show _ = (((st.1 + r.1 • eZ i) m : ℤ) : ℝ)
      by_cases hm : m = i
      · rw [eZ_apply, ite_eq_left hm]
        simp [hyl, n01, hm, hi]
      · have hmt : (m : ℕ) ≠ t := fun e => hm (Fin.ext (e.trans hi.symm))
        rw [eZ_apply, ite_eq_right hm]
        simp [hyl, n01, hmt, E1.ay m]
    · by_cases hmi : m = i
      · subst hmi
        simp [Ne.symm hyl, n01, hi, f20]
      · have hmt : (m : ℕ) ≠ t := fun e => hmi (Fin.ext (e.trans hi.symm))
        simp [Ne.symm hyl, n01, hmt, hmi, kA1.2 s.adl m (Or.inr (Or.inr rfl)), hadl m (by omega)]

/-! ## The differences -/

/-- `G_i := (evN (Y + Δ_i e_i) - evN (Y - Δ_i e_i)) (cE / Δ_i)` into `ag[i]`, `i` in `n0`. -/
def xsGrad (L : Layout) (s : SepLay) (EV : XCmdO) : XCmdO :=
  .seq (.base (.seq (toX (VL.aget L (s.u + 28) s.adl s.n0)) (toX (VL.sop2 L .add (s.u + 8) (s.u + 28) (s.u + 16)))))
  (.seq (xsEval L s EV (s.u + 26))
  (.seq (.base (toX (VL.sop2 L .sub (s.u + 8) (s.u + 16) (s.u + 28))))
  (.seq (xsEval L s EV (s.u + 27))
  (.base (.seq (toX (VL.sop2 L .sub (s.u + 26) (s.u + 26) (s.u + 27)))
    (.seq (xsidiv L (s.u + 27) s.cE (s.u + 28))
    (.seq (toX (VL.sop2 L .mul (s.u + 26) (s.u + 26) (s.u + 27)))
      (toX (VL.aset L s.ag s.n0 (s.u + 26))))))))))

/-- The difference of SEP at the coordinate `i` from the state `st`. -/
def gradZ (evN : (Fin d → ℤ) → ℤ) (E : ℕ) (st : SepStZ d) (i : Fin d) : ℤ :=
  (evN (st.1 + st.2.2 i • eZ i) - evN (st.1 - st.2.2 i • eZ i)) * (2 ^ E / st.2.2 i)

/-- The differences after `t` coordinates. -/
def GInv (s : SepLay) (Sev Nev : ℕ → Prop) (Arev : ℕ → ℕ → Prop) (σ0 : Env d) (evN : (Fin d → ℤ) → ℤ) (E : ℕ)
    (st : SepStZ d) (t : ℕ) (σ : Env d) : Prop :=
  SEnv s Sev Nev Arev σ0 σ ∧ σ.nat s.nok = 1 ∧ (∀ m : Fin d, σ.arr s.ay m = st.1 m) ∧ σ.sc s.u = st.2.1 ∧
    (∀ m : Fin d, σ.arr s.adl m = st.2.2 m) ∧ ∀ m : Fin d, (m : ℕ) < t → σ.arr s.ag m = gradZ evN E st m

set_option maxHeartbeats 16000000 in
theorem sGrads_runs {XO : XCtxO d} {ℓa ℓ : ℕ} {EV : XCmdO} {Dat : Env d → Prop} {evN : (Fin d → ℤ) → ℤ}
    {Kev bv : ℕ} {Y0 : Fin d → ℤ} {E e1 eτ eL eu bY : ℕ}
    (H : SEvH L XO ℓa ℓ s EV Dat evN Kev bv Sev Nev Arev Y0 E e1 σ0)
    (P : SepHyp s σ0 Y0 E e1 eτ eL eu bY bv ℓa ℓ) {st : SepStZ d} (hDI : SepDomInv Y0 (2 ^ (E - e1)) d st)
    {σ : Env d} (hG : GInv s Sev Nev Arev σ0 evN E st 0 σ) :
    XRunsBO L XO ℓa ℓ (xforNO s.n0 (s.n0 + 2) (s.n0 + 1) (xsGrad L s EV)) σ
      (d * (((2 + 1) + (sKE d Kev + (1 + (sKE d Kev + (1 + (1 + (1 + 2))))))) + 3) + 3)
      (fun σ' => GInv s Sev Nev Arev σ0 evN E st d σ') := by
  obtain ⟨⟨h0a, hya, hga, hla, hea⟩, hne, ⟨hvo, hcEs, hL1s, hShs, hcAs, hcBs, hus⟩,
    ⟨-, hvu, hEu, hLu, hSu, hAu, hBu⟩, ⟨hnJs, hnoks, hn0s⟩, ⟨hJok, hJn, hokn⟩⟩ := H.hs
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or, List.nodup_nil,
    and_true] at hne
  obtain ⟨⟨h0y, h0g, h0l, h0e⟩, ⟨hyg, hyl, hye⟩, ⟨hgl, hge⟩, hle⟩ := hne
  obtain ⟨dE, dJ⟩ := P.dE H.hd
  have hℓ := P.hℓ
  have hℓa := P.hℓa
  have bY' := sepDomInv_bound (Bm := E + eτ + eu + bY + bv + 4) hDI P.Y0b (by omega) (by omega)
  have hL1 : (2 : ℤ) ^ (E - e1) ≤ 2 ^ (E + eτ + eu + bY + bv + 4 + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hlt : ∀ t, t < d → t < asz d := fun t h => Nat.lt_of_lt_of_le h (Nat.le_add_left d (d * d))
  have bb : ∀ z : ℤ, ∀ e, |z| ≤ 2 ^ e → e ≤ E + eτ + eu + bY + bv + 7 → |z| < 2 ^ ℓ := fun z e hz he =>
    lt_of_le_of_lt (absI_mono hz he) (pow_lt_pow_right₀ (by norm_num) (by omega))
  refine XVO.mono (XVO.forN H.hL (i := s.n0) (n := s.n0 + 2) (one := s.n0 + 1) (by omega) (by omega) (by omega)
    (by omega) (by omega) d _ (by omega) (GInv s Sev Nev Arev σ0 evN E st) σ hG.1.nd hG.1.n1 ?_ ?_) le_rfl
    fun σ' h => h.1
  · obtain ⟨SE, n1, ay, u, adl, -⟩ := hG
    exact ⟨SE.setNat (Or.inr ⟨le_rfl, by omega⟩) (by omega) (by omega) (by omega) _,
      by simp [show s.nok ≠ s.n0 by omega, n1], fun m => by simp [ay m], by simp [u], fun m => by simp [adl m],
      fun m hm => absurd hm (Nat.not_lt_zero _)⟩
  intro t ht σ1 ⟨SE, nok1, hay, hu, hadl, hag⟩ n0e n2e n1e
  obtain ⟨i, hi⟩ : ∃ i : Fin d, (i : ℕ) = t := ⟨⟨t, ht⟩, rfl⟩
  obtain ⟨kE, -, -, kA, kB, kJ, -⟩ := SE.U.keep H.hs H.hDisj
  have LE : LEnv s Sev Nev Arev σ0 i (eL + eτ + 3) E eτ eu st.2.1 st.1 σ1 :=
    ⟨n0e.trans hi.symm, SE.n1, SE.nd, SE.nz, by rw [kJ, P.nJ], by rw [kE, P.cE], by rw [kA, P.cA],
      by rw [kB, P.cB], hu, SE.four, SE.zero, hay, SE.U, SE.dr⟩
  have hΔ := hDI.2.2.2.2 i (by omega)
  have bΔ : |st.2.2 i| ≤ 2 ^ (E - e1) := by rw [abs_of_nonneg hΔ.1]; linarith
  have adl1 : σ1.arr s.adl t = st.2.2 i := by rw [← hi]; exact hadl i
  -- `u + 28 := Δ`, `off := Δ`
  have hb : XRunsB L XO.X ℓa ℓ (.seq (toX (VL.aget L (s.u + 28) s.adl s.n0))
      (toX (VL.sop2 L .add (s.u + 8) (s.u + 28) (s.u + 16)))) σ1 (2 + 1) (fun σ' =>
      σ' = (σ1.setSc (s.u + 28) ((st.2.2 i : ℤ) : ℝ)).setSc (s.u + 8) (((st.2.2 i + 0 : ℤ) : ℝ))) := by
    refine XV.seq (XV.aget H.hL (x := s.u + 28) (a := s.adl) (i := s.n0) (by omega) hla (by omega)
      (by rw [n0e]; exact hlt t ht) (by rw [n0e, adl1]; exact XV.abs_int_lt (bb _ _ bΔ (by omega)))) fun σa ea => ?_
    rw [n0e, adl1] at ea
    subst ea
    exact XV.mono (XV.addI H.hL (x := s.u + 8) (a := s.u + 28) (b := s.u + 16) (u := st.2.2 i) (v := 0) (by omega)
      (by omega) (by omega) (by simp) (by simp [SE.zero]) (bb _ _ bΔ (by omega)) (by simp)
      (by simpa using bb _ _ bΔ (by omega))) le_rfl (fun σb eb => eb)
  refine XVO.seq (XVO.ofX hb) fun σ2 h2 => ?_
  subst h2
  have E2 := (LE.setSc H.hs (x := s.u + 28) (by omega) (by omega) (by omega) (by omega) ((st.2.2 i : ℤ) : ℝ)).setSc H.hs
    (x := s.u + 8) (by omega) (by omega) (by omega) (by omega) (((st.2.2 i + 0 : ℤ) : ℝ))
  refine XVO.seq (sLEval_runs H.hL H.hs H.hd H.hEV H.hbv H.hDisj H.hStab H.hD0 E2 (off := st.2.2 i + 0) (by simp)
    (sepDom_grad hDI i _ (by simpa using bΔ)) bY' (by simpa using absI_mono bΔ (by omega)) (by omega) (by omega)
    (by omega) (x := s.u + 26) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    fun σ3 ⟨v3, _, E3, k3⟩ => ?_
  have d3 : σ3.sc (s.u + 28) = st.2.2 i :=
    SKeep.sc' k3 (by simp) (by omega) (by omega) (by omega) (by omega) (by omega)
  refine XVO.seq (XVO.ofX (XV.subI H.hL (x := s.u + 8) (a := s.u + 16) (b := s.u + 28) (u := 0) (v := st.2.2 i)
    (by omega) (by omega) (by omega) (by simp [E3.zero]) d3 (by simp) (bb _ _ bΔ (by omega))
    (by simpa using bb _ _ bΔ (by omega)))) fun σ4 e4 => ?_
  subst e4
  have E4 := E3.setSc H.hs (x := s.u + 8) (by omega) (by omega) (by omega) (by omega) (((0 - st.2.2 i : ℤ) : ℝ))
  have hneg : st.1 + (0 - st.2.2 i) • eZ i = st.1 - st.2.2 i • eZ i := by
    rw [zero_sub, neg_smul, ← sub_eq_add_neg]
  refine XVO.seq (sLEval_runs H.hL H.hs H.hd H.hEV H.hbv H.hDisj H.hStab H.hD0 E4 (off := 0 - st.2.2 i) (by simp)
    (by rw [hneg, sub_eq_add_neg, ← neg_smul]; exact sepDom_grad hDI i _ (by simpa using bΔ)) bY'
    (by simpa using absI_mono bΔ (by omega)) (by omega) (by omega) (by omega) (x := s.u + 27) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)) fun σ5 ⟨v5, _, E5, k5⟩ => ?_
  rw [hneg] at v5
  have v35 : σ5.sc (s.u + 26) = evN (st.1 + (st.2.2 i + 0) • eZ i) :=
    SKeep.sc' k5 (by simpa using v3) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [add_zero] at v35
  have d5 : σ5.sc (s.u + 28) = st.2.2 i :=
    SKeep.sc' k5 (by simp [d3]) (by omega) (by omega) (by omega) (by omega) (by omega)
  have bp := H.hbv _ (sepDom_grad hDI i _ bΔ)
  have bm := H.hbv _ (by rw [sub_eq_add_neg, ← neg_smul]; exact sepDom_grad hDI i _ (by simpa using bΔ) :
    SepDom Y0 E e1 (st.1 - st.2.2 i • eZ i))
  have bdiff := absI_sub_le bp.le bm.le
  have bq : |(2 : ℤ) ^ E / st.2.2 i| ≤ 2 ^ E := (absI_ediv_le _ _).trans (bound_two_pow E)
  have bprod := absI_mul_le bdiff bq
  have cE5 : σ5.sc s.cE = ((2 ^ E : ℤ) : ℝ) := by rw [E5.cE]; norm_num
  refine XVO.ofX (XV.seq (XV.subI H.hL (x := s.u + 26) (a := s.u + 26) (b := s.u + 27)
    (u := evN (st.1 + st.2.2 i • eZ i)) (v := evN (st.1 - st.2.2 i • eZ i)) (by omega) (by omega) (by omega) v35 v5
    (bb _ _ bp.le (by omega)) (bb _ _ bm.le (by omega)) (bb _ _ bdiff (by omega))) fun σ6 e6 => ?_)
  subst e6
  refine XV.seq (XV.divI H.hL (x := s.u + 27) (a := s.cE) (b := s.u + 28) (u := 2 ^ E) (v := st.2.2 i)
    (by omega) hcEs (by omega) (by simp [show s.cE ≠ s.u + 26 by omega, cE5]) (by simp [d5])
    (bb _ _ (bound_two_pow E) (by omega)) (bb _ _ bΔ (by omega))) fun σ7 e7 => ?_
  subst e7
  refine XV.seq (XV.mulI H.hL (x := s.u + 26) (a := s.u + 26) (b := s.u + 27)
    (u := evN (st.1 + st.2.2 i • eZ i) - evN (st.1 - st.2.2 i • eZ i)) (v := 2 ^ E / st.2.2 i) (by omega) (by omega)
    (by omega) (by simp) (by simp) (bb _ _ bdiff (by omega)) (bb _ _ bq (by omega)) (bb _ _ bprod (by omega)))
    fun σ8 e8 => ?_
  subst e8
  have n05 : σ5.nat s.n0 = t := by rw [E5.ni, hi]
  refine XV.mono (XV.aset H.hL (a := s.ag) (i := s.n0) (x := s.u + 26) hga (by omega) (by omega)
    (by simp [n05]; exact hlt t ht) (by rw [Env.setSc_sc, ite_eq_left rfl]; exact XV.abs_int_lt (bb _ _ bprod
    (by omega)))) le_rfl fun σ9 e9 => ?_
  subst e9
  have SE5 := SEnv.ofL E5
  have nk3 := k3.2.1 s.nok (Or.inr rfl)
  have nk5 := k5.2.1 s.nok (Or.inr rfl)
  refine ⟨by simp [n05], by simp [E5.nd], by simp [E5.n1], ?_⟩
  refine ⟨((((SE5.setSc (x := s.u + 26) (by omega) (by omega) (by omega) (by omega) _).setSc (x := s.u + 27)
    (by omega) (by omega) (by omega) (by omega) _).setSc (x := s.u + 26) (by omega) (by omega) (by omega)
    (by omega) _).setArr (Or.inr (Or.inl rfl)) _).setNat (Or.inr ⟨le_rfl, by omega⟩) (by omega) (by omega)
    (by omega) _, ?_, fun m => ?_, by simp [E5.len], fun m => ?_, fun m hm => ?_⟩
  · simp [show s.nok ≠ s.n0 by omega, nk5, nk3, nok1]
  · simp [hyg, E5.ay m]
  · simp [Ne.symm hgl, k5.2.2 s.adl m (Or.inr (Or.inr rfl)), k3.2.2 s.adl m (Or.inr (Or.inr rfl)), hadl m]
  · by_cases hmi : m = i
    · simp [hmi, n05, hi, gradZ]
    · have hmt : (m : ℕ) ≠ t := fun e => hmi (Fin.ext (e.trans hi.symm))
      simp [hmt, n05, k5.2.2 s.ag m (Or.inr (Or.inl rfl)), k3.2.2 s.ag m (Or.inr (Or.inl rfl)),
        hag m (by omega)]

/-! ## The block -/

theorem sep_cost (d J Kev : ℕ) :
    (1 + (1 + (1 + (1 + (1 + (1 + (1 + ((d * ((2 + 2) + 3) + 3) + 1)))))))) +
      ((d - 0) * ((sLK d J Kev + (9 + 2)) + 2) + 2 +
        ((d * (((2 + 1) + (sKE d Kev + (1 + (sKE d Kev + (1 + (1 + (1 + 2))))))) + 3) + 3) + 2)) ≤
      sepK d J Kev := by
  simp only [sLK, sLB, sKE, sepK, Nat.sub_zero]
  ring_nf
  nlinarith [Nat.zero_le (d * J * Kev), Nat.zero_le (d * d * J), Nat.zero_le (d * J), Nat.zero_le (d * Kev),
    Nat.zero_le (d * d), Nat.zero_le (J * Kev), Nat.zero_le (d ^ 2 * J), Nat.zero_le (d ^ 2)]

theorem sepE_eq (evN : (Fin d → ℤ) → ℤ) (Y0 : Fin d → ℤ) (E e1 eτ eL eu : ℕ) :
    sepE evN Y0 E e1 eτ eL eu =
      sepCoordsZ evN Y0 (2 ^ (E - e1)) (2 ^ (eτ + 4 + eL)) (2 ^ (E + eτ + 1)) (2 ^ eu) (eL + eτ + 3) d >>= fun st =>
        some (st.1, fun i => gradZ evN E st i) := rfl

end AdversarialBco.Uni
