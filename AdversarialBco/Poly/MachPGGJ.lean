/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachPGLoops

@[expose] public section

/-! # The rules of the Gauss-Jordan code of PG

`runs_gjCode`: the code `gjCode` (`MachPGCode.lean`) leaves `(A, B) = gjRun T d`, the Gauss-Jordan elimination without
pivoting of `(T, 1)`, in `d (21 d² + 31 d + 17) + 12 d² + 7 d + 16` steps. Built from the column loops `runs_gjScale`
(row `k` times `ip`) and `runs_gjElimRow` (row `i` minus `f` times row `k`), the row loop `runs_gjElimAll`, one pivot
`runs_gjPivot` and the pivot loop `runs_gjLoop`. Proofs through the rules of `Runs` only. -/

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL
  Matrix

namespace AdversarialBco.Poly.PG

theorem idx_eq_iff {d a a' b b' : ℕ} (hb : b < d) (hb' : b' < d) :
    d * a + b = d * a' + b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    have hd : 0 < d := by omega
    have h1 : (d * a + b) / d = (d * a' + b') / d := by rw [h]
    have h2 : (d * a + b) % d = (d * a' + b') % d := by rw [h]
    rw [Nat.mul_add_div hd, Nat.mul_add_div hd, Nat.div_eq_of_lt hb, Nat.div_eq_of_lt hb'] at h1
    rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb'] at h2
    exact ⟨by omega, h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem mat_setArr_self {d : ℕ} (σ : Env d) (A : ℕ) (a b : Fin d) (v : ℝ) :
    (σ.setArr A (d * a + b) v).mat A =
      Matrix.of (fun a' b' => if a' = a ∧ b' = b then v else σ.mat A a' b') := by
  ext a' b'
  show (σ.setArr A (d * a + b) v).arr A (d * a' + b') = _
  rw [Env.setArr_arr, Matrix.of_apply]
  have e : (A = A ∧ d * a' + b' = d * a + b) ↔ (a' = a ∧ b' = b) := by
    rw [idx_eq_iff b'.2 b.2]; simp [Fin.ext_iff]
  by_cases h : a' = a ∧ b' = b
  · rw [if_pos (e.2 h), if_pos h]
  · rw [if_neg (fun h' => h (e.1 h')), if_neg h]; rfl

theorem mat_setArr_ne {d : ℕ} (σ : Env d) {A B : ℕ} (h : B ≠ A) (m : ℕ) (v : ℝ) :
    (σ.setArr A m v).mat B = σ.mat B := by
  ext a' b'
  show (σ.setArr A m v).arr B (d * a' + b') = σ.arr B (d * a' + b')
  simp [h]

theorem frame_setArr' {d : ℕ} {σ σ' : Env d} {ns ss as : List ℕ} (h : Env.Frame σ σ' ns ss as) {a : ℕ}
    (ha : a ∈ as) (k : ℕ) (v : ℝ) : Env.Frame σ (σ'.setArr a k v) ns ss as :=
  ⟨h.1, h.2.1, fun b hb => by
    have hba : b ≠ a := fun e => hb (e ▸ ha)
    funext m; simp [hba]; exact congrFun (h.2.2.1 b hb) m, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- Row `i` of `X0` replaced by `g` on the columns `< c`. -/
def rowPart {d : ℕ} (X0 : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) (g : Fin d → ℝ) (c : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun a b => if a = i ∧ (b : ℕ) < c then g b else X0 a b

theorem rowPart_zero {d : ℕ} (X0 : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) (g : Fin d → ℝ) :
    rowPart X0 i g 0 = X0 := by
  ext a b; simp [rowPart]

theorem rowPart_full {d : ℕ} (X0 : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) (g : Fin d → ℝ) :
    rowPart X0 i g d = Matrix.updateRow X0 i g := by
  ext a b
  by_cases ha : a = i
  · subst ha; simp [rowPart, b.2]
  · simp [rowPart, ha, Matrix.updateRow_apply]

theorem rowPart_of_not {d : ℕ} (X0 : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) (g : Fin d → ℝ) {c : ℕ} {a b : Fin d}
    (h : ¬ (a = i ∧ (b : ℕ) < c)) : rowPart X0 i g c a b = X0 a b := by
  simp only [rowPart, Matrix.of_apply, if_neg h]

theorem rowPart_set {d : ℕ} (X0 : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) (g : Fin d → ℝ) {c : ℕ} (hc : c < d) :
    Matrix.of (fun a' b' => if a' = i ∧ b' = (⟨c, hc⟩ : Fin d) then g ⟨c, hc⟩ else rowPart X0 i g c a' b') =
      rowPart X0 i g (c + 1) := by
  ext a b
  simp only [rowPart, Matrix.of_apply]
  by_cases ha : a = i
  · subst ha
    by_cases hb : (b : ℕ) = c
    · have e : b = ⟨c, hc⟩ := Fin.ext hb
      subst e; simp
    · have hb' : b ≠ ⟨c, hc⟩ := fun h => hb (by rw [h])
      rw [if_neg (fun h => hb' h.2)]
      by_cases h' : (b : ℕ) < c
      · rw [if_pos ⟨rfl, h'⟩, if_pos ⟨rfl, by omega⟩]
      · rw [if_neg (fun h => h' h.2), if_neg (fun h => by omega)]
  · simp [ha]

theorem runs_gjScale {d : ℕ} {L : AdversarialBco.Poly.Mach.Layout}
    {w : AdversarialBco.RealRAM.World d} {dv one j kj A B ip t : ℕ} (σ : Env d)
    (k : Fin d) (hdv : dv < L.NN) (hone : one < L.NN) (hj : j < L.NN) (hkj : kj < L.NN) (hA : A < L.NA)
    (hB : B < L.NA) (hip : ip < L.NS) (ht : t < L.NS) (hjdv : j ≠ dv) (hjone : j ≠ one) (hjkj : j ≠ kj)
    (hkjdv : kj ≠ dv) (hkjone : kj ≠ one) (hAB : A ≠ B) (hipt : ip ≠ t) (hd : σ.nat dv = d)
    (h1 : σ.nat one = 1) (hkv : σ.nat kj = d * k) :
    AdversarialBco.Poly.Mach.Runs L w (gjScale L dv one j kj A B ip t) σ (d * 14 + 3)
      (fun σ' => σ'.mat A = Matrix.updateRow (σ.mat A) k (fun c => σ.mat A k c * σ.sc ip) ∧
        σ'.mat B = Matrix.updateRow (σ.mat B) k (fun c => σ.mat B k c * σ.sc ip) ∧ σ'.nat kj = d * k + d ∧
        Env.Frame σ σ' [j, kj] [t] [A, B]) := by
  have hk' : (k : ℕ) < d := k.2
  set A0 := σ.mat A with hA0
  set B0 := σ.mat B with hB0
  set φ := σ.sc ip with hφ
  let J : ℕ → Env d → Prop := fun c σ' => σ'.nat kj = d * k + c ∧
    σ'.mat A = rowPart A0 k (fun b => A0 k b * φ) c ∧ σ'.mat B = rowPart B0 k (fun b => B0 k b * φ) c ∧
    Env.Frame σ σ' [j, kj] [t] [A, B]
  refine runs_mono (runs_forN (L := L) (w := w) hj hdv hone hjdv hjone d 11 J σ hd h1 ?_ ?_)
    (le_of_eq (by ring)) (fun σ' h => ?_)
  · exact ⟨by simp [Ne.symm hjkj, hkv], (rowPart_zero _ _ _).symm, (rowPart_zero _ _ _).symm,
      Env.Frame.setNat (Env.Frame.refl σ _ _ _) (by simp) 0⟩
  · intro c hc σ' hJ ej ed e1
    obtain ⟨ekj, mA, mB, F'⟩ := hJ
    set cf : Fin d := ⟨c, hc⟩ with hcf
    have hφ' : σ'.sc ip = φ := F'.2.1 ip (by simp [hipt])
    have hkj' : σ'.nat kj < asz d := by rw [ekj, asz]; nlinarith
    have vA : σ'.arr A (σ'.nat kj) = A0 k cf := by
      rw [ekj]; show σ'.mat A k cf = _; rw [mA, rowPart_of_not _ _ _ (by simp [hcf])]
    have vB : σ'.arr B (σ'.nat kj) = B0 k cf := by
      rw [ekj]; show σ'.mat B k cf = _; rw [mB, rowPart_of_not _ _ _ (by simp [hcf])]
    refine runs_mono (K := 2 + (1 + (2 + (2 + (1 + (2 + 1)))))) ?_ (by norm_num) (fun _ h => h)
    refine runs_seq_eq (runs_aget (L := L) (w := w) (σ := σ') (x := t) (a := A) (i := kj) ht hA hkj hkj') ?_
    set σ1 := σ'.setSc t (σ'.arr A (σ'.nat kj)) with hσ1
    refine runs_seq_eq (runs_sop2 (L := L) (w := w) (σ := σ1) (x := t) (a := t) (b := ip) ht ht hip .mul) ?_
    set σ2 := σ1.setSc t (Op2.eval .mul (σ1.sc t) (σ1.sc ip)) with hσ2
    refine runs_seq_eq (runs_aset (L := L) (w := w) (σ := σ2) (a := A) (i := kj) (x := t) hA hkj ht hkj') ?_
    set σ3 := σ2.setArr A (σ2.nat kj) (σ2.sc t) with hσ3
    have v2 : σ2.sc t = A0 k cf * φ := by simp [hσ2, hσ1, Op2.eval, hipt, vA, hφ']
    refine runs_seq_eq (runs_aget (L := L) (w := w) (σ := σ3) (x := t) (a := B) (i := kj) ht hB hkj hkj') ?_
    set σ4 := σ3.setSc t (σ3.arr B (σ3.nat kj)) with hσ4
    refine runs_seq_eq (runs_sop2 (L := L) (w := w) (σ := σ4) (x := t) (a := t) (b := ip) ht ht hip .mul) ?_
    set σ5 := σ4.setSc t (Op2.eval .mul (σ4.sc t) (σ4.sc ip)) with hσ5
    refine runs_seq_eq (runs_aset (L := L) (w := w) (σ := σ5) (a := B) (i := kj) (x := t) hB hkj ht hkj') ?_
    set σ6 := σ5.setArr B (σ5.nat kj) (σ5.sc t) with hσ6
    have v5 : σ5.sc t = B0 k cf * φ := by
      simp [hσ5, hσ4, hσ3, hσ2, hσ1, Op2.eval, hipt, Ne.symm hAB, hφ', vB]
    refine runs_mono (runs_nadd (L := L) (w := w) (σ := σ6) (i := kj) (a := kj) (b := one) hkj hkj hone) le_rfl
      (fun σ7 e7 => ?_)
    subst e7
    have n6 : σ6.nat = σ'.nat := rfl
    have mA3 : σ3.mat A = rowPart A0 k (fun b => A0 k b * φ) (c + 1) := by
      rw [hσ3, show σ2.nat kj = d * k + cf from ekj, mat_setArr_self, v2, show σ2.mat A = σ'.mat A from rfl, mA]
      exact rowPart_set A0 k (fun b => A0 k b * φ) hc
    have mB6 : σ6.mat B = rowPart B0 k (fun b => B0 k b * φ) (c + 1) := by
      rw [hσ6, show σ5.nat kj = d * k + cf from ekj, mat_setArr_self, v5, show σ5.mat B = σ3.mat B from rfl, hσ3,
        mat_setArr_ne _ (Ne.symm hAB), show σ2.mat B = σ'.mat B from rfl, mB]
      exact rowPart_set B0 k (fun b => B0 k b * φ) hc
    refine ⟨by simp [n6, hjkj, ej], by simp [n6, Ne.symm hkjdv, ed], by simp [n6, Ne.symm hkjone, e1], ?_, ?_, ?_, ?_⟩
    · simp [n6, Ne.symm hjkj, ekj, hkjone, e1]; ring
    · show σ6.mat A = _
      rw [hσ6, mat_setArr_ne _ hAB, show σ5.mat A = σ3.mat A from rfl, mA3]
    · exact mB6
    · refine Env.Frame.setNat (Env.Frame.setNat ?_ (by simp) _) (by simp) _
      refine frame_setArr' ?_ (by simp) _ _
      refine Env.Frame.setSc ?_ (by simp) _
      refine Env.Frame.setSc ?_ (by simp) _
      refine frame_setArr' ?_ (by simp) _ _
      refine Env.Frame.setSc ?_ (by simp) _
      refine Env.Frame.setSc F' (by simp) _
  · obtain ⟨⟨ekj, mA, mB, F'⟩, -⟩ := h
    exact ⟨mA.trans (rowPart_full _ _ _), mB.trans (rowPart_full _ _ _), ekj, F'⟩

theorem runs_gjElimRow {d : ℕ} {L : AdversarialBco.Poly.Mach.Layout}
    {w : AdversarialBco.RealRAM.World d} {dv one j ij kj A B f t1 t2 : ℕ} (σ : Env d)
    (i k : Fin d) (hik : i ≠ k) (hdv : dv < L.NN) (hone : one < L.NN) (hj : j < L.NN) (hij : ij < L.NN)
    (hkj : kj < L.NN) (hA : A < L.NA) (hB : B < L.NA) (hf : f < L.NS) (ht1 : t1 < L.NS) (ht2 : t2 < L.NS)
    (hjdv : j ≠ dv) (hjone : j ≠ one) (hjij : j ≠ ij) (hjkj : j ≠ kj) (hijkj : ij ≠ kj) (hijdv : ij ≠ dv)
    (hijone : ij ≠ one) (hkjdv : kj ≠ dv) (hkjone : kj ≠ one) (hAB : A ≠ B) (hf1 : f ≠ t1) (hf2 : f ≠ t2)
    (h12 : t1 ≠ t2) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) (hiv : σ.nat ij = d * i)
    (hkv : σ.nat kj = d * k) :
    AdversarialBco.Poly.Mach.Runs L w (gjElimRow L dv one j ij kj A B f t1 t2) σ (d * 21 + 3)
      (fun σ' => σ'.mat A = Matrix.updateRow (σ.mat A) i (fun c => σ.mat A i c - σ.sc f * σ.mat A k c) ∧
        σ'.mat B = Matrix.updateRow (σ.mat B) i (fun c => σ.mat B i c - σ.sc f * σ.mat B k c) ∧
        σ'.nat ij = d * i + d ∧ σ'.nat kj = d * k + d ∧
        Env.Frame σ σ' [j, ij, kj] [t1, t2] [A, B]) := by
  have hi' : (i : ℕ) < d := i.2
  have hk' : (k : ℕ) < d := k.2
  set A0 := σ.mat A with hA0
  set B0 := σ.mat B with hB0
  set φ := σ.sc f with hφ
  let J : ℕ → Env d → Prop := fun c σ' => σ'.nat ij = d * i + c ∧ σ'.nat kj = d * k + c ∧
    σ'.mat A = rowPart A0 i (fun b => A0 i b - φ * A0 k b) c ∧
    σ'.mat B = rowPart B0 i (fun b => B0 i b - φ * B0 k b) c ∧
    Env.Frame σ σ' [j, ij, kj] [t1, t2] [A, B]
  refine runs_mono (runs_forN (L := L) (w := w) hj hdv hone hjdv hjone d 18 J σ hd h1 ?_ ?_)
    (le_of_eq (by ring)) (fun σ' h => ?_)
  · exact ⟨by simp [Ne.symm hjij, hiv], by simp [Ne.symm hjkj, hkv], (rowPart_zero _ _ _).symm,
      (rowPart_zero _ _ _).symm, Env.Frame.setNat (Env.Frame.refl σ _ _ _) (by simp) 0⟩
  · intro c hc σ' hJ ej ed e1
    obtain ⟨eij, ekj, mA, mB, F'⟩ := hJ
    set cf : Fin d := ⟨c, hc⟩ with hcf
    have hf' : σ'.sc f = φ := F'.2.1 f (by simp [hf1, hf2])
    have hkj' : σ'.nat kj < asz d := by rw [ekj, asz]; nlinarith
    have hij' : σ'.nat ij < asz d := by rw [eij, asz]; nlinarith
    have nk : ¬ (k = i ∧ (cf : ℕ) < c) := fun h => hik h.1.symm
    have ni : ¬ (i = i ∧ (cf : ℕ) < c) := fun h => lt_irrefl c h.2
    have vAk : σ'.arr A (σ'.nat kj) = A0 k cf := by
      rw [ekj]; show σ'.mat A k cf = _; rw [mA, rowPart_of_not _ _ _ nk]
    have vAi : σ'.arr A (σ'.nat ij) = A0 i cf := by
      rw [eij]; show σ'.mat A i cf = _; rw [mA, rowPart_of_not _ _ _ ni]
    have vBk : σ'.arr B (σ'.nat kj) = B0 k cf := by
      rw [ekj]; show σ'.mat B k cf = _; rw [mB, rowPart_of_not _ _ _ nk]
    have vBi : σ'.arr B (σ'.nat ij) = B0 i cf := by
      rw [eij]; show σ'.mat B i cf = _; rw [mB, rowPart_of_not _ _ _ ni]
    refine runs_mono (K := 2 + (1 + (2 + (1 + (2 + (2 + (1 + (2 + (1 + (2 + (1 + 1))))))))))) ?_ (by norm_num)
      (fun _ h => h)
    refine runs_seq_eq (runs_aget (L := L) (w := w) (σ := σ') (x := t1) (a := A) (i := kj) ht1 hA hkj hkj') ?_
    set σ1 := σ'.setSc t1 (σ'.arr A (σ'.nat kj)) with hσ1
    refine runs_seq_eq (runs_sop2 (L := L) (w := w) (σ := σ1) (x := t1) (a := f) (b := t1) ht1 hf ht1 .mul) ?_
    set σ2 := σ1.setSc t1 (Op2.eval .mul (σ1.sc f) (σ1.sc t1)) with hσ2
    refine runs_seq_eq (runs_aget (L := L) (w := w) (σ := σ2) (x := t2) (a := A) (i := ij) ht2 hA hij hij') ?_
    set σ3 := σ2.setSc t2 (σ2.arr A (σ2.nat ij)) with hσ3
    refine runs_seq_eq (runs_sop2 (L := L) (w := w) (σ := σ3) (x := t2) (a := t2) (b := t1) ht2 ht2 ht1 .sub) ?_
    set σ4 := σ3.setSc t2 (Op2.eval .sub (σ3.sc t2) (σ3.sc t1)) with hσ4
    refine runs_seq_eq (runs_aset (L := L) (w := w) (σ := σ4) (a := A) (i := ij) (x := t2) hA hij ht2 hij') ?_
    set σ5 := σ4.setArr A (σ4.nat ij) (σ4.sc t2) with hσ5
    have v4 : σ4.sc t2 = A0 i cf - φ * A0 k cf := by
      simp [hσ4, hσ3, hσ2, hσ1, Op2.eval, h12, Ne.symm h12, hf1, hf2, vAk, vAi, hf']
    refine runs_seq_eq (runs_aget (L := L) (w := w) (σ := σ5) (x := t1) (a := B) (i := kj) ht1 hB hkj hkj') ?_
    set σ6 := σ5.setSc t1 (σ5.arr B (σ5.nat kj)) with hσ6
    refine runs_seq_eq (runs_sop2 (L := L) (w := w) (σ := σ6) (x := t1) (a := f) (b := t1) ht1 hf ht1 .mul) ?_
    set σ7 := σ6.setSc t1 (Op2.eval .mul (σ6.sc f) (σ6.sc t1)) with hσ7
    refine runs_seq_eq (runs_aget (L := L) (w := w) (σ := σ7) (x := t2) (a := B) (i := ij) ht2 hB hij hij') ?_
    set σ8 := σ7.setSc t2 (σ7.arr B (σ7.nat ij)) with hσ8
    refine runs_seq_eq (runs_sop2 (L := L) (w := w) (σ := σ8) (x := t2) (a := t2) (b := t1) ht2 ht2 ht1 .sub) ?_
    set σ9 := σ8.setSc t2 (Op2.eval .sub (σ8.sc t2) (σ8.sc t1)) with hσ9
    refine runs_seq_eq (runs_aset (L := L) (w := w) (σ := σ9) (a := B) (i := ij) (x := t2) hB hij ht2 hij') ?_
    set σ10 := σ9.setArr B (σ9.nat ij) (σ9.sc t2) with hσ10
    have v9 : σ9.sc t2 = B0 i cf - φ * B0 k cf := by
      simp [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Op2.eval, h12, Ne.symm h12, hf1, hf2, Ne.symm hAB, vBk,
        vBi, hf']
    refine runs_seq_eq (runs_nadd (L := L) (w := w) (σ := σ10) (i := ij) (a := ij) (b := one) hij hij hone) ?_
    set σ11 := σ10.setNat ij (σ10.nat ij + σ10.nat one) with hσ11
    refine runs_mono (runs_nadd (L := L) (w := w) (σ := σ11) (i := kj) (a := kj) (b := one) hkj hkj hone) le_rfl
      (fun σ12 e12 => ?_)
    subst e12
    have n10 : σ10.nat = σ'.nat := rfl
    have mA5 : σ5.mat A = rowPart A0 i (fun b => A0 i b - φ * A0 k b) (c + 1) := by
      rw [hσ5, show σ4.nat ij = d * i + cf from eij, mat_setArr_self, v4, show σ4.mat A = σ'.mat A from rfl, mA]
      exact rowPart_set A0 i (fun b => A0 i b - φ * A0 k b) hc
    have mB10 : σ10.mat B = rowPart B0 i (fun b => B0 i b - φ * B0 k b) (c + 1) := by
      rw [hσ10, show σ9.nat ij = d * i + cf from eij, mat_setArr_self, v9, show σ9.mat B = σ5.mat B from rfl, hσ5,
        mat_setArr_ne _ (Ne.symm hAB), show σ4.mat B = σ'.mat B from rfl, mB]
      exact rowPart_set B0 i (fun b => B0 i b - φ * B0 k b) hc
    refine ⟨by simp [hσ11, n10, hjkj, hjij, ej], by simp [hσ11, n10, Ne.symm hkjdv, Ne.symm hijdv, ed],
      by simp [hσ11, n10, Ne.symm hkjone, Ne.symm hijone, e1], ?_, ?_, ?_, ?_, ?_⟩
    · simp [hσ11, n10, Ne.symm hjij, hijkj, eij, Ne.symm hijone, e1]; ring
    · simp [hσ11, n10, Ne.symm hjkj, Ne.symm hijkj, ekj, Ne.symm hkjone, Ne.symm hijone, e1]; ring
    · show σ10.mat A = _
      rw [hσ10, mat_setArr_ne _ hAB, show σ9.mat A = σ5.mat A from rfl, mA5]
    · exact mB10
    · refine Env.Frame.setNat (Env.Frame.setNat (Env.Frame.setNat ?_ (by simp) _) (by simp) _) (by simp) _
      refine frame_setArr' ?_ (by simp) _ _
      refine Env.Frame.setSc ?_ (by simp) _
      refine Env.Frame.setSc ?_ (by simp) _
      refine Env.Frame.setSc ?_ (by simp) _
      refine Env.Frame.setSc ?_ (by simp) _
      refine frame_setArr' ?_ (by simp) _ _
      refine Env.Frame.setSc ?_ (by simp) _
      refine Env.Frame.setSc ?_ (by simp) _
      refine Env.Frame.setSc ?_ (by simp) _
      refine Env.Frame.setSc F' (by simp) _
  · obtain ⟨⟨eij, ekj, mA, mB, F'⟩, -⟩ := h
    exact ⟨mA.trans (rowPart_full _ _ _), mB.trans (rowPart_full _ _ _), eij, ekj, F'⟩


theorem runs_gjElim {d : ℕ} {L : AdversarialBco.Poly.Mach.Layout}
    {w : AdversarialBco.RealRAM.World d} {dv one j ri rk kk ij kj A B f t1 t2 : ℕ}
    (σ : Env d) (i k : Fin d) (hik : i ≠ k) (hdv : dv < L.NN) (hone : one < L.NN)
    (hj : j < L.NN) (hri : ri < L.NN) (hrk : rk < L.NN) (hkk : kk < L.NN) (hij : ij < L.NN) (hkj : kj < L.NN)
    (hA : A < L.NA) (hB : B < L.NA) (hf : f < L.NS) (ht1 : t1 < L.NS) (ht2 : t2 < L.NS)
    (hN : [j, ij, kj].Nodup) (hjN : j ∉ [dv, one, ri, rk, kk]) (hijN : ij ∉ [dv, one, ri, rk, kk])
    (hkjN : kj ∉ [dv, one, ri, rk, kk]) (hAB : A ≠ B) (hS : [f, t1, t2].Nodup) (hd : σ.nat dv = d)
    (h1 : σ.nat one = 1) (hriv : σ.nat ri = d * i) (hrkv : σ.nat rk = d * k) (hkkv : σ.nat kk = k) :
    AdversarialBco.Poly.Mach.Runs L w (gjElim L dv one j ri rk kk ij kj A B f t1 t2) σ (d * 21 + 10)
      (fun σ' => σ'.mat A = Matrix.updateRow (σ.mat A) i (fun c => σ.mat A i c - σ.mat A i k * σ.mat A k c) ∧
        σ'.mat B = Matrix.updateRow (σ.mat B) i (fun c => σ.mat B i c - σ.mat A i k * σ.mat B k c) ∧
        Env.Frame σ σ' [j, ij, kj] [f, t1, t2] [A, B]) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    at hN hjN hijN hkjN hS
  obtain ⟨⟨hjij, hjkj⟩, hijkj, -⟩ := hN
  obtain ⟨hijdv, hijone, hijri, hijrk, hijkk⟩ := hijN
  obtain ⟨hkjdv, hkjone, hkjri, hkjrk, hkjkk⟩ := hkjN
  obtain ⟨hjdv, hjone, -, -, -⟩ := hjN
  obtain ⟨⟨hf1, hf2⟩, h12, -⟩ := hS
  have hik' : (i : ℕ) < d := i.2
  have hk' : (k : ℕ) < d := k.2
  refine runs_mono (K := 1 + (2 + (1 + (1 + (1 + (1 + (d * 21 + 3))))))) ?_ (by omega) (fun σ' h => h)
  unfold gjElim
  refine runs_seq_eq (runs_nadd (L := L) (w := w) (σ := σ) (i := ij) (a := ri) (b := kk) hij hri hkk) ?_
  set σ1 := σ.setNat ij (σ.nat ri + σ.nat kk) with hσ1
  have e1 : σ1.nat ij = d * i + k := by simp [hσ1, hriv, hkkv]
  have hi1 : σ1.nat ij < asz d := by
    rw [e1, asz]; nlinarith
  refine runs_seq_eq (runs_aget (L := L) (w := w) (σ := σ1) (x := f) (a := A) (i := ij) hf hA hij hi1) ?_
  set σ2 := σ1.setSc f (σ1.arr A (σ1.nat ij)) with hσ2
  refine runs_seq_eq (runs_nconst (L := L) (w := w) (σ := σ2) hij 0) ?_
  refine runs_seq_eq (runs_nadd (L := L) (w := w) (σ := σ2.setNat ij 0) (i := ij) (a := ij) (b := ri) hij hij hri) ?_
  set σ3 := (σ2.setNat ij 0).setNat ij ((σ2.setNat ij 0).nat ij + (σ2.setNat ij 0).nat ri) with hσ3
  refine runs_seq_eq (runs_nconst (L := L) (w := w) (σ := σ3) hkj 0) ?_
  refine runs_seq_eq (runs_nadd (L := L) (w := w) (σ := σ3.setNat kj 0) (i := kj) (a := kj) (b := rk) hkj hkj hrk) ?_
  set σ4 := (σ3.setNat kj 0).setNat kj ((σ3.setNat kj 0).nat kj + (σ3.setNat kj 0).nat rk) with hσ4
  have n4 : ∀ x, x ≠ ij → x ≠ kj → σ4.nat x = σ.nat x := fun x h1 h2 => by simp [hσ4, hσ3, hσ2, hσ1, h1, h2]
  have e4i : σ4.nat ij = d * i := by simp [hσ4, hσ3, hσ2, hσ1, hijkj, Ne.symm hijri, hriv]
  have e4k : σ4.nat kj = d * k := by simp [hσ4, hσ3, hσ2, hσ1, Ne.symm hkjrk, Ne.symm hijrk, hrkv]
  have a4 : σ4.arr = σ.arr := rfl
  have s4f : σ4.sc f = σ.mat A i k := by
    simp only [hσ4, hσ3, hσ2, Env.setNat_sc, Env.setSc_sc, if_pos rfl, e1]; rfl
  have F04 : Env.Frame σ σ4 [ij, kj] [f] [] := by
    refine ⟨fun x hx => n4 x (by simp at hx; exact hx.1) (by simp at hx; exact hx.2), fun x hx => ?_,
      fun _ _ => rfl, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at hx
    simp [hσ4, hσ3, hσ2, hσ1, hx]
  refine runs_mono (runs_gjElimRow σ4 i k hik hdv hone hj hij hkj hA hB hf ht1 ht2 hjdv hjone hjij hjkj hijkj hijdv
    hijone hkjdv hkjone hAB hf1 hf2 h12 ((n4 _ (Ne.symm hijdv) (Ne.symm hkjdv)).trans hd)
    ((n4 _ (Ne.symm hijone) (Ne.symm hkjone)).trans h1) e4i e4k) le_rfl fun σ5 h5 => ?_
  obtain ⟨mA, mB, -, -, F5⟩ := h5
  refine ⟨?_, ?_, Env.Frame.trans (Env.Frame.mono F04 (by simp) (by simp) (by simp))
    (Env.Frame.mono F5 (by simp) (by simp) (by simp))⟩
  · rw [mA, s4f]; rfl
  · rw [mB, s4f]; rfl

/-- The rows `< t` other than `k` eliminated at the pivot `k`, in `X` with the factors of `A`. -/
def gjPart {d : ℕ} (A0 X0 : Matrix (Fin d) (Fin d) ℝ) (k : Fin d) (t : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun a b => if (a : ℕ) < t ∧ a ≠ k then X0 a b - A0 a k * X0 k b else X0 a b

theorem gjPart_zero {d : ℕ} (A0 X0 : Matrix (Fin d) (Fin d) ℝ) (k : Fin d) : gjPart A0 X0 k 0 = X0 := by
  ext a b; simp [gjPart]

theorem gjPart_step {d : ℕ} (A0 X0 : Matrix (Fin d) (Fin d) ℝ) (k : Fin d) {t : ℕ} (ht : t < d)
    (htk : (⟨t, ht⟩ : Fin d) ≠ k) :
    Matrix.updateRow (gjPart A0 X0 k t) ⟨t, ht⟩
        (fun c => gjPart A0 X0 k t ⟨t, ht⟩ c - gjPart A0 A0 k t ⟨t, ht⟩ k * gjPart A0 X0 k t k c) =
      gjPart A0 X0 k (t + 1) := by
  ext a b
  by_cases ha : a = ⟨t, ht⟩
  · subst ha
    simp [gjPart, Matrix.updateRow_apply, htk]
  · have hat : (a : ℕ) ≠ t := fun h => ha (Fin.ext h)
    have e : ((a : ℕ) < t ∧ a ≠ k) ↔ ((a : ℕ) < t + 1 ∧ a ≠ k) := by omega
    simp only [gjPart, Matrix.updateRow_apply, ha, if_false, Matrix.of_apply]
    by_cases h : (a : ℕ) < t ∧ a ≠ k
    · rw [if_pos h, if_pos (e.1 h)]
    · rw [if_neg h, if_neg (fun h' => h (e.2 h'))]

theorem gjPart_skip {d : ℕ} (A0 X0 : Matrix (Fin d) (Fin d) ℝ) (k : Fin d) {t : ℕ} (htk : t = k) :
    gjPart A0 X0 k t = gjPart A0 X0 k (t + 1) := by
  ext a b
  have e : ((a : ℕ) < t ∧ a ≠ k) ↔ ((a : ℕ) < t + 1 ∧ a ≠ k) := by
    constructor
    · exact fun h => ⟨by omega, h.2⟩
    · intro h; refine ⟨?_, h.2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h.1 with h' | h'
      · exact h'
      · exact absurd (Fin.ext (h'.trans htk)) h.2
  simp only [gjPart, Matrix.of_apply]
  by_cases h : (a : ℕ) < t ∧ a ≠ k
  · rw [if_pos h, if_pos (e.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (e.2 h'))]

theorem gjPart_full {d : ℕ} (A0 X0 : Matrix (Fin d) (Fin d) ℝ) (k : Fin d) :
    gjPart A0 X0 k d = Matrix.of (fun a b => if a = k then X0 k b else X0 a b - A0 a k * X0 k b) := by
  ext a b
  by_cases h : a = k
  · subst h; simp [gjPart]
  · simp [gjPart, h, a.2]

theorem runs_gjElimAll {d : ℕ} {L : AdversarialBco.Poly.Mach.Layout}
    {w : AdversarialBco.RealRAM.World d} {dv one i j kk ri rk ij kj A B f t1 t2 : ℕ}
    (σ : Env d) (k : Fin d) (hdv : dv < L.NN) (hone : one < L.NN) (hi : i < L.NN)
    (hj : j < L.NN) (hri : ri < L.NN) (hrk : rk < L.NN) (hkk : kk < L.NN) (hij : ij < L.NN) (hkj : kj < L.NN)
    (hA : A < L.NA) (hB : B < L.NA) (hf : f < L.NS) (ht1 : t1 < L.NS) (ht2 : t2 < L.NS)
    (hN : [i, j, ri, ij, kj].Nodup) (hNo : ∀ q ∈ [i, j, ri, ij, kj], q ∉ [dv, one, rk, kk]) (hAB : A ≠ B)
    (hS : [f, t1, t2].Nodup) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) (hrkv : σ.nat rk = d * k)
    (hkkv : σ.nat kk = k) :
    AdversarialBco.Poly.Mach.Runs L w (gjElimAll L dv one i j kk ri rk ij kj A B f t1 t2) σ
      (d * (d * 21 + 17) + 4)
      (fun σ' => σ'.mat A = Matrix.of (fun a b => if a = k then σ.mat A k b else
            σ.mat A a b - σ.mat A a k * σ.mat A k b) ∧
        σ'.mat B = Matrix.of (fun a b => if a = k then σ.mat B k b else
            σ.mat B a b - σ.mat A a k * σ.mat B k b) ∧
        Env.Frame σ σ' [i, j, ri, ij, kj] [f, t1, t2] [A, B]) := by
  have hS' := hS
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    forall_eq_or_imp, forall_eq] at hN hNo hS
  obtain ⟨⟨hij_, hiri, hiij, hikj⟩, ⟨hjri, hjij, hjkj⟩, ⟨hriij, hrikj⟩, hijkj⟩ := hN
  obtain ⟨⟨hidv, hione, hirk, hikk⟩, ⟨hjdv, hjone, hjrk, hjkk⟩, ⟨hridv, hrione, hrirk, hrikk⟩,
    ⟨hijdv, hijone, hijrk, hijkk⟩, ⟨hkjdv, hkjone, hkjrk, hkjkk⟩⟩ := hNo
  have nkk : kk ∉ [i, j, ri, ij, kj] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm hikk, Ne.symm hjkk, Ne.symm hrikk, Ne.symm hijkk, Ne.symm hkjkk⟩
  have nrk : rk ∉ [i, j, ri, ij, kj] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm hirk, Ne.symm hjrk, Ne.symm hrirk, Ne.symm hijrk, Ne.symm hkjrk⟩
  have hk' : (k : ℕ) < d := k.2
  set A0 := σ.mat A with hA0
  set B0 := σ.mat B with hB0
  refine runs_mono (K := 1 + (d * (d * 21 + 14 + 3) + 3)) ?_ (le_of_eq (by ring)) (fun _ h => h)
  unfold gjElimAll
  refine runs_seq_eq (runs_nconst (L := L) (w := w) (σ := σ) hri 0) ?_
  set σ0 := σ.setNat ri 0 with hσ0
  have F0 : Env.Frame σ σ0 [i, j, ri, ij, kj] [f, t1, t2] [A, B] :=
    Env.Frame.setNat (Env.Frame.refl σ _ _ _) (by simp) 0
  let J : ℕ → Env d → Prop := fun t σ' => σ'.mat A = gjPart A0 A0 k t ∧ σ'.mat B = gjPart A0 B0 k t ∧
    σ'.nat ri = d * t ∧ Env.Frame σ σ' [i, j, ri, ij, kj] [f, t1, t2] [A, B]
  have hd0 : σ0.nat dv = d := by simp [hσ0, Ne.symm hridv, hd]
  have h10 : σ0.nat one = 1 := by simp [hσ0, Ne.symm hrione, h1]
  refine runs_mono (runs_forN (L := L) (w := w) hi hdv hone hidv hione d (d * 21 + 14) J σ0 hd0 h10 ?_ ?_)
    le_rfl (fun σ' h => ?_)
  · refine ⟨by rw [gjPart_zero]; rfl, by rw [gjPart_zero]; rfl, by simp [hσ0, Ne.symm hiri],
      Env.Frame.setNat F0 (by simp) 0⟩
  · intro t ht σ' hJ ei ed e1
    obtain ⟨mA, mB, eri, F'⟩ := hJ
    have ekk : σ'.nat kk = k := (F'.1 kk nkk).trans hkkv
    have erk : σ'.nat rk = d * k := (F'.1 rk nrk).trans hrkv
    have post : ∀ σ'', σ''.mat A = gjPart A0 A0 k (t + 1) → σ''.mat B = gjPart A0 B0 k (t + 1) →
        Env.Frame σ' σ'' [j, ij, kj] [f, t1, t2] [A, B] →
        Runs L w (nadd ri ri dv) σ'' 1 (fun σ3 => σ3.nat i = t ∧ σ3.nat dv = d ∧ σ3.nat one = 1 ∧
          J (t + 1) (σ3.setNat i (t + 1))) := by
      intro σ'' mA'' mB'' F''
      refine runs_mono (runs_nadd hri hri hdv) le_rfl (fun σ3 e3 => ?_)
      subst e3
      have n'' : ∀ x, x ≠ j → x ≠ ij → x ≠ kj → σ''.nat x = σ'.nat x := fun x h1 h2 h3 =>
        F''.1 x (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2, h3⟩)
      refine ⟨?_, ?_, ?_, mA'', mB'', ?_, ?_⟩
      · simp [hiri, n'' i hij_ hiij hikj, ei]
      · simp [Ne.symm hridv, n'' dv (Ne.symm hjdv) (Ne.symm hijdv) (Ne.symm hkjdv), ed]
      · simp [Ne.symm hrione, n'' one (Ne.symm hjone) (Ne.symm hijone) (Ne.symm hkjone), e1]
      · simp [Ne.symm hiri, n'' ri (Ne.symm hjri) hriij hrikj, eri,
          n'' dv (Ne.symm hjdv) (Ne.symm hijdv) (Ne.symm hkjdv), ed]
        ring
      · refine Env.Frame.setNat (Env.Frame.setNat (Env.Frame.trans F' (Env.Frame.mono F'' (by simp) (by simp) (by simp)))
          (by simp) _) (by simp) _
    have elim : (⟨t, ht⟩ : Fin d) ≠ k →
        Runs L w (gjElim L dv one j ri rk kk ij kj A B f t1 t2) σ' (d * 21 + 10) (fun σ'' =>
          σ''.mat A = gjPart A0 A0 k (t + 1) ∧ σ''.mat B = gjPart A0 B0 k (t + 1) ∧
          Env.Frame σ' σ'' [j, ij, kj] [f, t1, t2] [A, B]) := by
      intro htk
      refine runs_mono (runs_gjElim σ' ⟨t, ht⟩ k htk hdv hone hj hri hrk hkk hij hkj hA hB hf ht1 ht2
        (by simp [hjij, hjkj, hijkj]) (by simp [hjdv, hjone, hjri, hjrk, hjkk])
        (by simp [hijdv, hijone, Ne.symm hriij, hijrk, hijkk])
        (by simp [hkjdv, hkjone, Ne.symm hrikj, hkjrk, hkjkk]) hAB hS' ed e1 eri erk ekk) le_rfl
        (fun σ'' h => ?_)
      obtain ⟨hA'', hB'', F''⟩ := h
      refine ⟨?_, ?_, F''⟩
      · rw [hA'', mA]; exact gjPart_step A0 A0 k ht htk
      · rw [hB'', mA, mB]; exact gjPart_step A0 B0 k ht htk
    rcases lt_trichotomy t k with h | h | h
    · have htk : (⟨t, ht⟩ : Fin d) ≠ k := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      refine runs_mono (K := (d * 21 + 10 + 1) + 1) (runs_seq (runs_ifN_t hi hkk (by rw [ei, ekk]; exact h)
        (elim htk)) fun σ'' h'' => post σ'' h''.1 h''.2.1 h''.2.2) (by omega) (fun _ h => h)
    · have hkt : (k : ℕ) = t := h.symm
      refine runs_mono (K := (0 + 2 + 2) + 1) (runs_seq (runs_ifN_f hi hkk (by rw [ei, ekk]; omega)
        (runs_ifN_f hkk hi (by rw [ei, ekk]; omega) (runs_skip σ'))) fun σ'' h'' => ?_) (by omega)
        (fun _ h => h)
      subst σ''
      exact post σ' (by rw [mA, gjPart_skip A0 A0 k h]) (by rw [mB, gjPart_skip A0 B0 k h])
        (Env.Frame.refl σ' _ _ _)
    · have htk : (⟨t, ht⟩ : Fin d) ≠ k := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      refine runs_mono (K := (d * 21 + 10 + 1 + 2) + 1) (runs_seq (runs_ifN_f hi hkk (by rw [ei, ekk]; omega)
        (runs_ifN_t hkk hi (by rw [ei, ekk]; exact h) (elim htk))) fun σ'' h'' =>
        post σ'' h''.1 h''.2.1 h''.2.2) (by omega) (fun _ h => h)
  · obtain ⟨⟨mA, mB, -, F'⟩, -⟩ := h
    exact ⟨mA.trans (gjPart_full A0 A0 k), mB.trans (gjPart_full A0 B0 k), Env.Frame.mono F' (by simp) (by simp) (by simp)⟩

theorem runs_gjPivot {d : ℕ} {L : AdversarialBco.Poly.Mach.Layout}
    {w : AdversarialBco.RealRAM.World d} {dv one i j kk ri rk ij kj A B p ip o f t1 t2 : ℕ}
    (σ : Env d) (k : Fin d) (hdv : dv < L.NN) (hone : one < L.NN) (hi : i < L.NN)
    (hj : j < L.NN) (hri : ri < L.NN) (hrk : rk < L.NN) (hkk : kk < L.NN) (hij : ij < L.NN) (hkj : kj < L.NN)
    (hA : A < L.NA) (hB : B < L.NA) (hp : p < L.NS) (hip : ip < L.NS) (ho : o < L.NS) (hf : f < L.NS)
    (ht1 : t1 < L.NS) (ht2 : t2 < L.NS) (hN : [i, j, ri, rk, ij, kj].Nodup)
    (hNo : ∀ q ∈ [i, j, ri, rk, ij, kj], q ∉ [dv, one, kk]) (hAB : A ≠ B) (hS : [p, ip, o, f, t1, t2].Nodup)
    (hd : σ.nat dv = d) (h1 : σ.nat one = 1) (hrkv : σ.nat rk = d * k) (hkkv : σ.nat kk = k)
    (hov : σ.sc o = 1) :
    AdversarialBco.Poly.Mach.Runs L w (gjPivot L dv one i j kk ri rk ij kj A B p ip o f t1 t2) σ
      (d * d * 21 + d * 31 + 14)
      (fun σ' => (σ'.mat A, σ'.mat B) = gjStep k (σ.mat A, σ.mat B) ∧ σ'.nat rk = d * k + d ∧
        Env.Frame σ σ' [i, j, ri, rk, ij, kj] [p, ip, f, t1, t2] [A, B]) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    forall_eq_or_imp, forall_eq] at hN hNo hS
  obtain ⟨⟨hij_, hiri, hirk, hiij, hikj⟩, ⟨hjri, hjrk, hjij, hjkj⟩, ⟨hrirk, hriij, hrikj⟩, ⟨hrkij, hrkkj⟩,
    hijkj⟩ := hN
  obtain ⟨⟨hidv, hione, hikk⟩, ⟨hjdv, hjone, hjkk⟩, ⟨hridv, hrione, hrikk⟩, ⟨hrkdv, hrkone, hrkkk⟩,
    ⟨hijdv, hijone, hijkk⟩, ⟨hkjdv, hkjone, hkjkk⟩⟩ := hNo
  obtain ⟨⟨hpip, hpo, hpf, hpt1, hpt2⟩, ⟨hipo, hipf, hipt1, hipt2⟩, ⟨hof, hot1, hot2⟩, ⟨hf1, hf2⟩, h12⟩ := hS
  have hk' : (k : ℕ) < d := k.2
  set A0 := σ.mat A with hA0
  set B0 := σ.mat B with hB0
  refine runs_mono (K := 1 + (2 + (1 + (1 + (1 + ((d * 14 + 3) + ((d * (d * 21 + 17) + 4) + 1))))))) ?_
    (le_of_eq (by ring)) (fun _ h => h)
  unfold gjPivot
  refine runs_seq_eq (runs_nadd (L := L) (w := w) (σ := σ) (i := ij) (a := rk) (b := kk) hij hrk hkk) ?_
  set σ1 := σ.setNat ij (σ.nat rk + σ.nat kk) with hσ1
  have e1 : σ1.nat ij = d * k + k := by simp [hσ1, hrkv, hkkv]
  have hi1 : σ1.nat ij < asz d := by rw [e1, asz]; nlinarith
  refine runs_seq_eq (runs_aget (L := L) (w := w) (σ := σ1) (x := p) (a := A) (i := ij) hp hA hij hi1) ?_
  set σ2 := σ1.setSc p (σ1.arr A (σ1.nat ij)) with hσ2
  have s2p : σ2.sc p = A0 k k := by simp only [hσ2, Env.setSc_sc, if_pos rfl, e1]; rfl
  have s2o : σ2.sc o = 1 := by simp [hσ2, Ne.symm hpo, hσ1, hov]
  refine runs_seq_eq (runs_sop2 (L := L) (w := w) (σ := σ2) hip ho hp .div) ?_
  set σ3 := σ2.setSc ip (Op2.eval .div (σ2.sc o) (σ2.sc p)) with hσ3
  refine runs_seq_eq (runs_nconst (L := L) (w := w) (σ := σ3) hkj 0) ?_
  refine runs_seq_eq (runs_nadd (L := L) (w := w) (σ := σ3.setNat kj 0) (i := kj) (a := kj) (b := rk) hkj hkj hrk) ?_
  set σ4 := (σ3.setNat kj 0).setNat kj ((σ3.setNat kj 0).nat kj + (σ3.setNat kj 0).nat rk) with hσ4
  have n4 : ∀ x, x ≠ ij → x ≠ kj → σ4.nat x = σ.nat x := fun x h1 h2 => by simp [hσ4, hσ3, hσ2, hσ1, h1, h2]
  have e4k : σ4.nat kj = d * k := by simp [hσ4, hσ3, hσ2, hσ1, hrkkj, hrkij, hrkv]
  have s4ip : σ4.sc ip = 1 / A0 k k := by
    have : σ4.sc ip = σ3.sc ip := rfl
    rw [this, hσ3, Env.setSc_sc, if_pos rfl, s2o, s2p]; rfl
  have F04 : Env.Frame σ σ4 [ij, kj] [p, ip] [] := by
    refine ⟨fun x hx => n4 x (by simp at hx; exact hx.1) (by simp at hx; exact hx.2), fun x hx => ?_,
      fun _ _ => rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp [hσ4, hσ3, hσ2, hσ1, hx.1, hx.2]
  refine runs_seq (runs_gjScale σ4 k hdv hone hj hkj hA hB hip ht1 hjdv hjone hjkj hkjdv hkjone hAB hipt1
    ((n4 _ (Ne.symm hijdv) (Ne.symm hkjdv)).trans hd) ((n4 _ (Ne.symm hijone) (Ne.symm hkjone)).trans h1) e4k)
    fun σ5 h5 => ?_
  obtain ⟨m5A, m5B, -, F45⟩ := h5
  have n5 : ∀ x, x ≠ j → x ≠ ij → x ≠ kj → σ5.nat x = σ.nat x := fun x h1 h2 h3 =>
    (F45.1 x (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h3⟩)).trans (n4 x h2 h3)
  have e4A : σ4.mat A = A0 := rfl
  have e4B : σ4.mat B = B0 := rfl
  rw [s4ip] at m5A m5B
  rw [e4A] at m5A
  rw [e4B] at m5B
  refine runs_seq (runs_gjElimAll σ5 k hdv hone hi hj hri hrk hkk hij hkj hA hB hf ht1 ht2
    (by simp [hij_, hiri, hiij, hikj, hjri, hjij, hjkj, hriij, hrikj, hijkj])
    (by simp [hidv, hione, hirk, hikk, hjdv, hjone, hjrk, hjkk, hridv, hrione, hrirk, hrikk, hijdv, hijone,
      Ne.symm hrkij, hijkk, hkjdv, hkjone, Ne.symm hrkkj, hkjkk]) hAB (by simp [hf1, hf2, h12])
    ((n5 _ (Ne.symm hjdv) (Ne.symm hijdv) (Ne.symm hkjdv)).trans hd)
    ((n5 _ (Ne.symm hjone) (Ne.symm hijone) (Ne.symm hkjone)).trans h1)
    ((n5 _ (Ne.symm hjrk) hrkij hrkkj).trans hrkv)
    ((n5 _ (Ne.symm hjkk) (Ne.symm hijkk) (Ne.symm hkjkk)).trans hkkv)) fun σ6 h6 => ?_
  obtain ⟨m6A, m6B, F56⟩ := h6
  refine runs_mono (runs_nadd hrk hrk hdv) le_rfl (fun σ7 e7 => ?_)
  subst e7
  have n6 : ∀ x ∉ [i, j, ri, ij, kj], σ6.nat x = σ5.nat x := F56.1
  have r6 : σ6.nat rk = d * k :=
    (n6 rk (by simp [Ne.symm hirk, Ne.symm hjrk, Ne.symm hrirk, hrkij, hrkkj])).trans
      ((n5 _ (Ne.symm hjrk) hrkij hrkkj).trans hrkv)
  have d6 : σ6.nat dv = d :=
    (n6 dv (by simp [Ne.symm hidv, Ne.symm hjdv, Ne.symm hridv, Ne.symm hijdv, Ne.symm hkjdv])).trans
      ((n5 _ (Ne.symm hjdv) (Ne.symm hijdv) (Ne.symm hkjdv)).trans hd)
  refine ⟨?_, ?_, ?_⟩
  · show (σ6.mat A, σ6.mat B) = _
    rw [m6A, m6B, m5A, m5B]
    simp only [gjStep, Prod.mk.injEq]
    constructor <;> ext a b <;> by_cases ha : a = k <;> simp [ha, Matrix.updateRow_apply]
  · simp [r6, d6]
  · refine Env.Frame.setNat (Env.Frame.trans (Env.Frame.mono F04 (by simp) (by simp) (by simp))
      (Env.Frame.trans (Env.Frame.mono F45 (by simp) (by simp) (by simp))
        (Env.Frame.mono F56 (by simp) (by simp) (by simp)))) (by simp) _

theorem runs_gjLoop {d : ℕ} {L : AdversarialBco.Poly.Mach.Layout}
    {w : AdversarialBco.RealRAM.World d} {dv one i j kk ri rk ij kj A B p ip o f t1 t2 : ℕ}
    (σ : Env d) (T : Matrix (Fin d) (Fin d) ℝ) (hdv : dv < L.NN) (hone : one < L.NN)
    (hi : i < L.NN) (hj : j < L.NN) (hri : ri < L.NN) (hrk : rk < L.NN) (hkk : kk < L.NN) (hij : ij < L.NN)
    (hkj : kj < L.NN) (hA : A < L.NA) (hB : B < L.NA) (hp : p < L.NS) (hip : ip < L.NS) (ho : o < L.NS)
    (hf : f < L.NS) (ht1 : t1 < L.NS) (ht2 : t2 < L.NS) (hN : [i, j, kk, ri, rk, ij, kj].Nodup)
    (hNo : ∀ q ∈ [i, j, kk, ri, rk, ij, kj], q ∉ [dv, one]) (hAB : A ≠ B) (hS : [p, ip, o, f, t1, t2].Nodup)
    (hd : σ.nat dv = d) (h1 : σ.nat one = 1) (hA0 : σ.mat A = T) (hB0 : σ.mat B = 1) (hrk0 : σ.nat rk = 0)
    (hov : σ.sc o = 1) :
    AdversarialBco.Poly.Mach.Runs L w
      (AdversarialBco.Poly.Mach.VL.forN kk dv one (gjPivot L dv one i j kk ri rk ij kj A B p ip o f t1 t2)) σ
      (d * (d * d * 21 + d * 31 + 17) + 3)
      (fun σ' => (σ'.mat A, σ'.mat B) = gjRun T d ∧
        Env.Frame σ σ' [i, j, kk, ri, rk, ij, kj] [p, ip, f, t1, t2] [A, B]) := by
  have hS' := hS
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    forall_eq_or_imp, forall_eq] at hN hNo hS
  obtain ⟨⟨hij_, hikk, hiri, hirk, hiij, hikj⟩, ⟨hjkk, hjri, hjrk, hjij, hjkj⟩, ⟨hkkri, hkkrk, hkkij, hkkkj⟩,
    ⟨hrirk, hriij, hrikj⟩, ⟨hrkij, hrkkj⟩, hijkj⟩ := hN
  obtain ⟨⟨hidv, hione⟩, ⟨hjdv, hjone⟩, ⟨hkkdv, hkkone⟩, ⟨hridv, hrione⟩, ⟨hrkdv, hrkone⟩,
    ⟨hijdv, hijone⟩, ⟨hkjdv, hkjone⟩⟩ := hNo
  obtain ⟨⟨hpip, hpo, hpf, hpt1, hpt2⟩, ⟨hipo, hipf, hipt1, hipt2⟩, ⟨hof, hot1, hot2⟩, ⟨hf1, hf2⟩, h12⟩ := hS
  let J : ℕ → Env d → Prop := fun t σ' => (σ'.mat A, σ'.mat B) = gjRun T t ∧ σ'.nat rk = d * t ∧
    Env.Frame σ σ' [i, j, kk, ri, rk, ij, kj] [p, ip, f, t1, t2] [A, B]
  refine runs_mono (runs_forN (L := L) (w := w) hkk hdv hone hkkdv hkkone d (d * d * 21 + d * 31 + 14) J σ hd h1
    ?_ ?_) (le_of_eq (by ring)) (fun σ' h => ⟨h.1.1, h.1.2.2⟩)
  · refine ⟨?_, by simp [Ne.symm hkkrk, hrk0], Env.Frame.setNat (Env.Frame.refl σ _ _ _) (by simp) 0⟩
    show (σ.mat A, σ.mat B) = gjRun T 0
    rw [hA0, hB0]; rfl
  · intro t ht σ' hJ ekk ed e1
    obtain ⟨mAB, erk, F'⟩ := hJ
    have eo : σ'.sc o = 1 := (F'.2.1 o (by simp [Ne.symm hpo, Ne.symm hipo, hof, hot1, hot2])).trans hov
    refine runs_mono (runs_gjPivot σ' ⟨t, ht⟩ hdv hone hi hj hri hrk hkk hij hkj hA hB hp hip ho hf ht1 ht2
      (by simp [hij_, hiri, hirk, hiij, hikj, hjri, hjrk, hjij, hjkj, hrirk, hriij, hrikj, hrkij, hrkkj, hijkj])
      (by simp [hidv, hione, hikk, hjdv, hjone, hjkk, hridv, hrione, Ne.symm hkkri, hrkdv, hrkone,
        Ne.symm hkkrk, hijdv, hijone, Ne.symm hkkij, hkjdv, hkjone, Ne.symm hkkkj]) hAB hS' ed e1 erk ekk eo)
      le_rfl (fun σ'' h => ?_)
    obtain ⟨mAB'', erk'', F''⟩ := h
    have n'' : ∀ x ∉ [i, j, ri, rk, ij, kj], σ''.nat x = σ'.nat x := F''.1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [n'' kk (by simp [Ne.symm hikk, Ne.symm hjkk, hkkri, hkkrk, hkkij, hkkkj]), ekk]
    · rw [n'' dv (by simp [Ne.symm hidv, Ne.symm hjdv, Ne.symm hridv, Ne.symm hrkdv, Ne.symm hijdv,
        Ne.symm hkjdv]), ed]
    · rw [n'' one (by simp [Ne.symm hione, Ne.symm hjone, Ne.symm hrione, Ne.symm hrkone, Ne.symm hijone,
        Ne.symm hkjone]), e1]
    · show (σ''.mat A, σ''.mat B) = gjRun T (t + 1)
      rw [mAB'', mAB, gjRun, dif_pos ht]
    · simp [Ne.symm hkkrk, erk'']; ring
    · exact Env.Frame.setNat (Env.Frame.trans F' (Env.Frame.mono F'' (by simp) (by simp) (by simp))) (by simp) _

theorem runs_gjCode {d : ℕ} {L : AdversarialBco.Poly.Mach.Layout}
    {w : AdversarialBco.RealRAM.World d} {dv one dd i j kk ri rk ij kj T A B p ip o z f t1 t2 : ℕ}
    (σ : Env d) (hdv : dv < L.NN) (hone : one < L.NN) (hdd : dd < L.NN)
    (hi : i < L.NN) (hj : j < L.NN) (hkk : kk < L.NN) (hri : ri < L.NN) (hrk : rk < L.NN) (hij : ij < L.NN)
    (hkj : kj < L.NN) (hT : T < L.NA) (hA : A < L.NA) (hB : B < L.NA) (hp : p < L.NS) (hip : ip < L.NS)
    (ho : o < L.NS) (hz : z < L.NS) (hf : f < L.NS) (ht1 : t1 < L.NS) (ht2 : t2 < L.NS)
    (hN : [i, j, kk, ri, rk, ij, kj].Nodup) (hNo : ∀ q ∈ [i, j, kk, ri, rk, ij, kj], q ∉ [dv, one, dd])
    (hAr : [T, A, B].Nodup) (hS : [p, ip, o, z, f, t1, t2].Nodup) (hd : σ.nat dv = d) (h1 : σ.nat one = 1)
    (hddv : σ.nat dd = d * d) :
    AdversarialBco.Poly.Mach.Runs L w (gjCode L dv one dd i j kk ri rk ij kj T A B p ip o z f t1 t2) σ
      (d * (d * d * 21 + d * 31 + 17) + d * d * 12 + d * 7 + 16)
      (fun σ' => (σ'.mat A, σ'.mat B) = gjRun (σ.mat T) d ∧
        Env.Frame σ σ' [i, j, kk, ri, rk, ij, kj] [p, ip, o, z, f, t1, t2] [A, B]) := by
  have hN' := hN
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    forall_eq_or_imp, forall_eq] at hN hNo hS hAr
  obtain ⟨⟨hij_, hikk, hiri, hirk, hiij, hikj⟩, ⟨hjkk, hjri, hjrk, hjij, hjkj⟩, ⟨hkkri, hkkrk, hkkij, hkkkj⟩,
    ⟨hrirk, hriij, hrikj⟩, ⟨hrkij, hrkkj⟩, hijkj⟩ := hN
  obtain ⟨⟨hidv, hione, hidd⟩, ⟨hjdv, hjone, hjdd⟩, ⟨hkkdv, hkkone, hkkdd⟩, ⟨hridv, hrione, hridd⟩,
    ⟨hrkdv, hrkone, hrkdd⟩, ⟨hijdv, hijone, hijdd⟩, ⟨hkjdv, hkjone, hkjdd⟩⟩ := hNo
  obtain ⟨⟨hpip, hpo, hpz, hpf, hpt1, hpt2⟩, ⟨hipo, hipz, hipf, hipt1, hipt2⟩, ⟨hoz, hof, hot1, hot2⟩,
    ⟨hzf, hzt1, hzt2⟩, ⟨hf1, hf2⟩, h12⟩ := hS
  obtain ⟨⟨hTA, hTB⟩, hAB, -⟩ := hAr
  refine runs_mono (K := 1 + (1 + ((d * d * 7 + 3) + ((d * d * 5 + 3) + ((d * 7 + 4) + (1 +
    (d * (d * d * 21 + d * 31 + 17) + 3))))))) ?_ (le_of_eq (by ring)) (fun _ h => h)
  unfold gjCode
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := σ) ho 1) ?_
  refine runs_seq_eq (runs_sconst (L := L) (w := w) (σ := σ.setSc o ((1 : ℚ) : ℝ)) hz 0) ?_
  set σ2 := (σ.setSc o ((1 : ℚ) : ℝ)).setSc z ((0 : ℚ) : ℝ) with hσ2
  have F02 : Env.Frame σ σ2 [] [o, z] [] :=
    Env.Frame.setSc (Env.Frame.setSc (Env.Frame.refl σ _ _ _) (by simp) _) (by simp) _
  have n2 : ∀ x, σ2.nat x = σ.nat x := fun _ => rfl
  have o2 : σ2.sc o = 1 := by simp [hσ2, hoz]
  have z2 : σ2.sc z = 0 := by simp [hσ2]
  refine runs_seq (runs_mcopy σ2 hdd hone hj hA hT ht1 hjdd hjone (by rw [n2]; exact hddv) (by rw [n2]; exact h1))
    fun σ3 h3 => ?_
  obtain ⟨m3A, F23, -⟩ := h3
  have n3 : ∀ x, x ≠ j → σ3.nat x = σ.nat x := fun x hx =>
    (F23.1 x (by simp [hx])).trans (n2 x)
  have o3 : σ3.sc o = 1 := (F23.2.1 o (by simp [hot1])).trans o2
  have z3 : σ3.sc z = 0 := (F23.2.1 z (by simp [hzt1])).trans z2
  refine runs_seq (runs_mfill σ3 hdd hone hj hB hz hjdd hjone ((n3 _ (Ne.symm hjdd)).trans hddv)
    ((n3 _ (Ne.symm hjone)).trans h1)) fun σ4 h4 => ?_
  obtain ⟨m4B, F34, -⟩ := h4
  have n4 : ∀ x, x ≠ j → σ4.nat x = σ.nat x := fun x hx =>
    (F34.1 x (by simp [hx])).trans (n3 x hx)
  have m4A : σ4.mat A = σ.mat T := (Env.mat_of_arr (F34.2.2.1 A (by simp [hAB]))).trans (m3A.trans (rfl : σ2.mat T = σ.mat T))
  have o4 : σ4.sc o = 1 := (F34.2.1 o (by simp)).trans o3
  refine runs_seq (runs_mdiag σ4 hdv hone hi hkj hB ho hidv hione (Ne.symm hikj) hkjdv hkjone
    ((n4 _ (Ne.symm hjdv)).trans hd) ((n4 _ (Ne.symm hjone)).trans h1)) fun σ5 h5 => ?_
  obtain ⟨m5B, F45, -⟩ := h5
  have n5 : ∀ x, x ≠ j → x ≠ i → x ≠ kj → σ5.nat x = σ.nat x := fun x hx hi' hkj' =>
    (F45.1 x (by simp [hi', hkj'])).trans (n4 x hx)
  have m5A : σ5.mat A = σ.mat T := (Env.mat_of_arr (F45.2.2.1 A (by simp [hAB]))).trans m4A
  have m5B' : σ5.mat B = 1 := by
    rw [m5B, m4B, o4, z3]
    ext a b
    simp [Matrix.one_apply]
  have o5 : σ5.sc o = 1 := (F45.2.1 o (by simp)).trans o4
  refine runs_seq_eq (runs_nconst (L := L) (w := w) (σ := σ5) hrk 0) ?_
  refine runs_mono (runs_gjLoop (σ5.setNat rk 0) (σ.mat T) hdv hone hi hj hri hrk hkk hij hkj hA hB hp hip ho hf
    ht1 ht2 hN' (by simp [hidv, hione, hjdv, hjone, hkkdv, hkkone, hridv, hrione, hrkdv, hrkone, hijdv, hijone,
      hkjdv, hkjone]) hAB (by simp [hpip, hpo, hpf, hpt1, hpt2, hipo, hipf, hipt1, hipt2, hof, hot1, hot2, hf1, hf2,
      h12])
    (by simp [Ne.symm hrkdv, n5 _ (Ne.symm hjdv) (Ne.symm hidv) (Ne.symm hkjdv), hd])
    (by simp [Ne.symm hrkone, n5 _ (Ne.symm hjone) (Ne.symm hione) (Ne.symm hkjone), h1])
    m5A m5B' (by simp) o5) le_rfl (fun σ6 h6 => ⟨h6.1, ?_⟩)
  exact Env.Frame.trans (Env.Frame.mono F02 (by simp) (by simp) (by simp))
    (Env.Frame.trans (Env.Frame.mono F23 (by simp) (by simp) (by simp))
      (Env.Frame.trans (Env.Frame.mono F34 (by simp) (by simp) (by simp))
        (Env.Frame.trans (Env.Frame.mono F45 (by simp) (by simp) (by simp))
          (Env.Frame.trans (Env.Frame.setNat (Env.Frame.refl σ5 [i, j, kk, ri, rk, ij, kj] _ _) (by simp) 0)
            (Env.Frame.mono h6.2 (by simp) (by simp) (by simp))))))

end AdversarialBco.Poly.PG
