/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachVec

@[expose] public section

/-! # Rules of the matrix codes

The rules of the matrix codes of MachVec.lean that are not proved there: `mdiag`, which sets the diagonal, `mlin`,
the linear combination of two matrices, `mmul`, the product, and `mtransp`, the transpose. -/

namespace AdversarialBco.Poly.Mach.VL

open AdversarialBco AdversarialBco.RealRAM Matrix

variable {d : ℕ} {L : Layout} {w : World d}

/-- `mdiag` writes `z` on the diagonal of the matrix `A` and keeps the rest. -/
theorem runs_mdiag {dv one i k A z : ℕ}
    (σ : Env d) (hdv : dv < L.NN) (hone : one < L.NN) (hi : i < L.NN) (hk : k < L.NN) (hA : A < L.NA)
    (hz : z < L.NS) (hidv : i ≠ dv) (hione : i ≠ one) (hki : k ≠ i) (hkdv : k ≠ dv) (hkone : k ≠ one)
    (hd : σ.nat dv = d) (h1 : σ.nat one = 1) :
    Runs L w (mdiag L dv one i k A z) σ (d * 7 + 4)
      (fun σ' => σ'.mat A = Matrix.of (fun a b => if a = b then σ.sc z else σ.mat A a b) ∧
        Env.Frame σ σ' [i, k] [] [A] ∧ ∀ q, d * d ≤ q → σ'.arr A q = σ.arr A q) := by
  let body : Cmd := .seq (aset L A k z) (.seq (nadd k k dv) (nadd k k one))
  let J : ℕ → Env d → Prop := fun t σ' =>
    σ'.nat k = d * t + t ∧
    (∀ q, σ'.arr A q = if (∃ c, c < t ∧ q = d * c + c) then σ.sc z else σ.arr A q) ∧
    (∀ a, a ≠ A → σ'.arr a = σ.arr a) ∧
    (∀ x, σ'.sc x = σ.sc x) ∧
    (∀ i', i' ≠ i → i' ≠ k → σ'.nat i' = σ.nat i') ∧
    σ'.draws = σ.draws ∧ σ'.rounds = σ.rounds ∧ σ'.pts = σ.pts
  have h0 : J 0 ((σ.setNat k 0).setNat i 0) := by
    refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro q; simp
    · intro a ha; simp
    · intro x; simp [Env.setNat_sc]
    · intro i' hi' hk'
      simp [hi', hk']
    · simp
    · simp
    · simp
  have hbody : ∀ t < d, ∀ σ', J t σ' → σ'.nat i = t → σ'.nat dv = d → σ'.nat one = 1 →
      Runs L w body σ' 4 (fun σ'' => σ''.nat i = t ∧ σ''.nat dv = d ∧ σ''.nat one = 1 ∧
        J (t + 1) (σ''.setNat i (t + 1))) := by
    intro t ht σ' hJ hit hdv' hone'
    obtain ⟨hJk, hJA, hJotherA, hJsc, hJn, hJd, hJr, hJp⟩ := hJ
    have hk_asz : σ'.nat k < asz d := by
      rw [hJk]
      have : d * t + t < d * d := idx_lt_sq (r := t) (t := t) ht ht
      unfold asz; omega
    have hrun := runs_seq_eq (runs_aset (w := w) (σ := σ') hA hk hz hk_asz)
      (runs_seq_eq (runs_nadd (w := w) hk hk hdv)
        (runs_nadd (w := w) hk hk hone))
    refine runs_mono hrun (by norm_num) (fun σ5 e5 => ?_)
    subst e5
    simp only [Env.setArr_nat]
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- nat i = t
      simp [hit, hki.symm]
    · -- nat dv = d
      simp [hdv', hkdv.symm]
    · -- nat one = 1
      simp [hone', hkone.symm]
    · -- J (t+1) (big_term.setNat i (t+1))
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- nat k = d*(t+1) + (t+1)
        simp [hJk, hdv', hone', hki, hkone.symm]
        ring
      · -- arr A condition
        intro q
        simp only [Env.setNat_arr, Env.setArr_arr, true_and, hJk]
        rw [hJA q, hJsc z]
        by_cases hq : q = d * t + t
        · subst hq
          have hex : ∃ c, c < t + 1 ∧ d * t + t = d * c + c := ⟨t, by omega, rfl⟩
          simp only [hex, ↓reduceIte]
        · have hiff : (∃ c, c < t + 1 ∧ q = d * c + c) ↔ (∃ c, c < t ∧ q = d * c + c) := by
            constructor
            · rintro ⟨c, hc, hq'⟩
              refine ⟨c, ?_, hq'⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp hc with h | h
              · exact h
              · subst h; exact absurd hq' hq
            · rintro ⟨c, hc, hq'⟩; exact ⟨c, by omega, hq'⟩
          simp only [hq, ↓reduceIte]
          exact if_congr hiff.symm rfl rfl
      · -- other arrays unchanged
        intro a ha
        have ha_ne_A : a ≠ A := by intro heq; apply ha; simp [heq]
        ext q; simpa [Env.setArr_arr, ha_ne_A] using congrFun (hJotherA a ha_ne_A) q
      · -- all scalars unchanged
        intro x; simpa using hJsc x
      · -- other naturals unchanged
        intro i' hi'i hi'k; simpa [hi'i, hi'k] using hJn i' hi'i hi'k
      · -- draws
        simpa using hJd
      · -- rounds
        simpa using hJr
      · -- pts
        simpa using hJp
  have hfor := runs_forN (L := L) (w := w) (body := body) (i := i) (n := dv) (one := one)
    hi hdv hone hidv hione d 4 J (σ.setNat k 0) (by simpa [Env.setNat_nat, hkdv.symm] using hd)
    (by simpa [Env.setNat_nat, hkone.symm] using h1) h0 hbody
  have hseq := runs_seq_eq (runs_nconst (L := L) (w := w) (σ := σ) hk 0) hfor
  refine runs_mono hseq (by ring_nf; omega) (fun σ' h => ?_)
  obtain ⟨hJ, h_nat_i, h_nat_dv, h_nat_one⟩ := h
  obtain ⟨hJk, hJA, hJotherA, hJsc, hJn, hJd, hJr, hJp⟩ := hJ
  have h_frame : Env.Frame σ σ' [i, k] [] [A] := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i' hi'
      have hi'_not_i : i' ≠ i := by
        intro heq; apply hi'; simp [heq]
      have hi'_not_k : i' ≠ k := by
        intro heq; apply hi'; simp [heq]
      exact hJn i' hi'_not_i hi'_not_k
    · intro x hx; exact hJsc x
    · intro a ha; apply hJotherA a; intro heq; apply ha; simp [heq]
    · exact hJd
    · exact hJr
    · exact hJp
  have h_tail : ∀ q, d * d ≤ q → σ'.arr A q = σ.arr A q := by
    intro q hq
    rw [hJA q]
    by_cases h_exists : ∃ c, c < d ∧ q = d * c + c
    · rcases h_exists with ⟨c, hc, hq'⟩
      have h_lt : d * c + c < d * d := idx_lt_sq hc hc
      rw [hq'] at hq
      omega
    · simp [h_exists]
  have h_mat : σ'.mat A = Matrix.of (fun a b => if a = b then σ.sc z else σ.mat A a b) := by
    ext a b
    show σ'.arr A (d * (a : ℕ) + (b : ℕ)) = (if a = b then σ.sc z else σ.arr A (d * (a : ℕ) + (b : ℕ)))
    rw [hJA (d * (a : ℕ) + (b : ℕ))]
    by_cases h_exists : ∃ c, c < d ∧ d * (a : ℕ) + (b : ℕ) = d * c + c
    · obtain ⟨c, hc, h_eq⟩ := id h_exists
      have ha_val_lt_d : (a : ℕ) < d := a.2
      have hb_val_lt_d : (b : ℕ) < d := b.2
      have hpos : 0 < d := by omega
      have key : ∀ x y : ℕ, y < d → (d * x + y) / d = x ∧ (d * x + y) % d = y := fun x y hy =>
        ⟨by rw [Nat.add_comm, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hy, Nat.zero_add],
         by rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy]⟩
      have e1 := key a b hb_val_lt_d
      have e2 := key c c hc
      rw [h_eq, e2.1, e2.2] at e1
      have ha_eq_b : a = b := Fin.ext (e1.1.symm.trans e1.2)
      simp only [h_exists, ↓reduceIte]
      exact (ite_eq_left_iff.mpr fun h => absurd ha_eq_b h).symm
    · by_cases h_ab : a = b
      · subst h_ab
        have ha_lt_d : (a : ℕ) < d := a.2
        have h_contra : ∃ c, c < d ∧ d * (a : ℕ) + (a : ℕ) = d * c + c := by
          refine ⟨(a : ℕ), ha_lt_d, ?_⟩
          ring
        exact absurd h_contra h_exists
      · simp [h_exists, h_ab]
  exact ⟨h_mat, h_frame, h_tail⟩

/-- `mlin` writes `α A + β B` into `C` (which may be `A` or `B`), entry by entry. -/
theorem runs_mlin {dd one m C A B α β t1 t2 : ℕ}
    (σ : Env d) (hdd : dd < L.NN) (hone : one < L.NN) (hm : m < L.NN) (hC : C < L.NA) (hA : A < L.NA)
    (hB : B < L.NA) (hα : α < L.NS) (hβ : β < L.NS) (ht1 : t1 < L.NS) (ht2 : t2 < L.NS) (hmdd : m ≠ dd)
    (hmone : m ≠ one) (h12 : t1 ≠ t2) (hα1 : α ≠ t1) (hα2 : α ≠ t2) (hβ1 : β ≠ t1) (hβ2 : β ≠ t2)
    (hd : σ.nat dd = d * d) (h1 : σ.nat one = 1) :
    Runs L w (mlin L dd one m C A B α β t1 t2) σ (d * d * 12 + 3)
      (fun σ' => σ'.mat C = σ.sc α • σ.mat A + σ.sc β • σ.mat B ∧ Env.Frame σ σ' [m] [t1, t2] [C] ∧
        ∀ q, d * d ≤ q → σ'.arr C q = σ.arr C q) := by
  let J : ℕ → Env d → Prop := fun s σ' =>
    (∀ k, σ'.arr C k = if k < s then σ.sc α * σ.arr A k + σ.sc β * σ.arr B k else σ.arr C k) ∧
    (∀ a, a ≠ C → σ'.arr a = σ.arr a) ∧
    (∀ z, z ≠ t1 → z ≠ t2 → σ'.sc z = σ.sc z) ∧
    (∀ j, j ≠ m → σ'.nat j = σ.nat j) ∧ σ'.draws = σ.draws ∧ σ'.rounds = σ.rounds ∧ σ'.pts = σ.pts
  have h0 : J 0 (σ.setNat m 0) := by
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · intro k; simp [Env.setNat_arr]
    · intro a ha; simp [Env.setNat_arr]
    · intro z hz1 hz2; simp [Env.setNat_sc]
    · intro j hj; simp [Env.setNat_nat, hj]
  have hbody : ∀ t < d * d, ∀ σ', J t σ' → σ'.nat m = t → σ'.nat dd = d * d → σ'.nat one = 1 →
      Runs L w (.seq (aget L t1 A m) (.seq (sop2 L .mul t1 α t1) (.seq (aget L t2 B m) (.seq (sop2 L .mul t2 β t2)
        (.seq (sop2 L .add t1 t1 t2) (aset L C m t1)))))) σ' 9 (fun σ'' => σ''.nat m = t ∧
          σ''.nat dd = d * d ∧ σ''.nat one = 1 ∧
        J (t + 1) (σ''.setNat m (t + 1))) := by
    intro s hs σ' hJ hits hds hots
    obtain ⟨Jarr, Jab, Js, Jn, Jd, Jr, Jp⟩ := hJ
    have hk : σ'.nat m < asz d := by
      rw [hits]
      have : s < d * d := hs
      unfold asz
      omega
    have hAt : σ'.arr A (σ'.nat m) = σ.arr A (σ'.nat m) := by
      by_cases hCA : C = A
      · subst hCA
        rw [hits]
        have h := Jarr s
        simpa using h
      · have h := Jab A (Ne.symm hCA)
        rw [hits]
        simpa using congrFun h s
    have hBt : σ'.arr B (σ'.nat m) = σ.arr B (σ'.nat m) := by
      by_cases hCB : C = B
      · subst hCB
        rw [hits]
        have h := Jarr s
        simpa using h
      · have h := Jab B (Ne.symm hCB)
        rw [hits]
        simpa using congrFun h s
    have hchain := runs_seq_eq (runs_aget (w := w) (σ := σ') ht1 hA hm hk) <|
      runs_seq_eq (runs_sop2 ht1 hα ht1 .mul) <|
      runs_seq_eq (runs_aget (w := w) ht2 hB hm hk) <|
      runs_seq_eq (runs_sop2 ht2 hβ ht2 .mul) <|
      runs_seq_eq (runs_sop2 ht1 ht1 ht2 .add) <|
      runs_aset (w := w) hC hm ht1 hk
    refine runs_mono hchain (by norm_num) (fun σ5 e5 => ?_)
    subst e5
    simp only [Env.setArr_nat, Env.setSc_nat, hits, hds, hots, true_and]
    have hxt : σ'.arr A s = σ.arr A s := by
      simpa [hits] using hAt
    have hyt : σ'.arr B s = σ.arr B s := by
      simpa [hits] using hBt
    refine ⟨fun k => ?_, fun a ha => ?_, fun z hz1 hz2 => ?_, fun j hj => ?_, Jd, Jr, Jp⟩
    · simp only [Env.setNat_arr, Env.setArr_arr, Env.setSc_arr, Env.setSc_sc, hxt, hyt]
      by_cases hks : k = s
      · subst hks
        simp [Op2.eval, h12, hα1, hβ1, hβ2, Js α hα1 hα2, Js β hβ1 hβ2]
      · rw [Jarr k]
        by_cases hk' : k < s
        · simp [hks, hk', show k < s + 1 by omega]
        · simp [hks, hk', show ¬ k < s + 1 by omega]
    · funext k; simp [ha, Jab a ha]
    · simp [hz1, hz2, Js z hz1 hz2]
    · simp [hj, Jn j hj]
  have hfor := runs_forN (w := w) (i := m) (n := dd) (one := one) (body := .seq (aget L t1 A m)
    (.seq (sop2 L .mul t1 α t1) (.seq (aget L t2 B m) (.seq (sop2 L .mul t2 β t2)
    (.seq (sop2 L .add t1 t1 t2) (aset L C m t1)))))) hm hdd hone hmdd hmone
    (d * d) 9 J σ hd h1 h0 hbody
  refine runs_mono hfor le_rfl (fun σ' h => ?_)
  obtain ⟨⟨Jarr, Jab, Js, Jn, Jd, Jr, Jp⟩, -, -, -⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · -- σ'.mat C = σ.sc α • σ.mat A + σ.sc β • σ.mat B
    ext i j
    simp [Env.mat, Jarr (d * i + j), show d * i + j < d * d by
      have hi : (i : ℕ) < d := i.2
      have hj : (j : ℕ) < d := j.2
      nlinarith]
  · -- Env.Frame σ σ' [m] [t1, t2] [C]
    refine ⟨?_, ?_, ?_, Jd, Jr, Jp⟩
    · intro i hi
      simp at hi
      have hi' : i ≠ m := by
        intro heq; subst heq; exact hi rfl
      simp [Jn i hi']
    · intro x hx
      simp at hx
      rcases hx with ⟨hx1, hx2⟩
      simp [Js x hx1 hx2]
    · intro a ha
      simp at ha
      simp [Jab a ha]
  · -- ∀ q, d * d ≤ q → σ'.arr C q = σ.arr C q
    intro q hq
    have hq' : ¬ q < d * d := by omega
    simp [hq', Jarr q]

/-- One row `r` of `mmul`: row `r` of `C` becomes row `r` of `A B`, the index `kC` running along it. -/
theorem runs_mmulRow {dv one j l kA kB kC C A B s t1 t2 : ℕ} (σ : Env d) (r : Fin d) (hdv : dv < L.NN) (hone : one < L.NN)
    (hj : j < L.NN) (hl : l < L.NN) (hkA : kA < L.NN) (hkB : kB < L.NN) (hkC : kC < L.NN)
    (hC : C < L.NA) (hA : A < L.NA) (hB : B < L.NA) (hs : s < L.NS) (ht1 : t1 < L.NS) (ht2 : t2 < L.NS)
    (hN : [j, l, kA, kB, kC].Nodup) (hdvN : dv ∉ [j, l, kA, kB, kC]) (honeN : one ∉ [j, l, kA, kB, kC])
    (hCA : C ≠ A) (hCB : C ≠ B) (hs1 : s ≠ t1) (hs2 : s ≠ t2) (h12 : t1 ≠ t2) (hd : σ.nat dv = d)
    (h1 : σ.nat one = 1) (hkC0 : σ.nat kC = d * r) :
    Runs L w (forN j dv one (.seq (sconst L s 0) (.seq (nsub kA kC j) (.seq (nsub kB kC kA) (.seq (forN l dv one
      (.seq (aget L t1 A kA) (.seq (aget L t2 B kB) (.seq (sop2 L .mul t1 t1 t2) (.seq (sop2 L .add s s t1)
        (.seq (nadd kA kA one) (nadd kB kB dv)))))))
      (.seq (aset L C kC s) (nadd kC kC one))))))) σ (d * (d * 11 + 12) + 3)
      (fun σ' => (∀ c : Fin d, σ'.arr C (d * r + c) = (σ.mat A * σ.mat B) r c) ∧
        (∀ m, (m < d * r ∨ d * r + d ≤ m) → σ'.arr C m = σ.arr C m) ∧ σ'.nat kC = d * r + d ∧
        Env.Frame σ σ' [j, l, kA, kB, kC] [s, t1, t2] [C]) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    at hN hdvN honeN
  obtain ⟨⟨hjl, hjkA, hjkB, hjkC⟩, ⟨hlkA, hlkB, hlkC⟩, ⟨hkAkB, hkAkC⟩, hkBkC, -⟩ := hN
  obtain ⟨hdvj, hdvl, hdvkA, hdvkB, hdvkC⟩ := hdvN
  obtain ⟨honej, honel, honekA, honekB, honekC⟩ := honeN
  let J : ℕ → Env d → Prop := fun t σ' =>
    σ'.nat kC = d * r + t ∧ (∀ c : Fin d, (c : ℕ) < t → σ'.arr C (d * r + c) = (σ.mat A * σ.mat B) r c) ∧
      (∀ m, (m < d * r ∨ d * r + t ≤ m) → σ'.arr C m = σ.arr C m) ∧ (∀ b, b ≠ C → σ'.arr b = σ.arr b) ∧
      (∀ z, z ≠ s → z ≠ t1 → z ≠ t2 → σ'.sc z = σ.sc z) ∧
      (∀ q, q ≠ j → q ≠ l → q ≠ kA → q ≠ kB → q ≠ kC → σ'.nat q = σ.nat q) ∧ σ'.draws = σ.draws ∧
      σ'.rounds = σ.rounds ∧ σ'.pts = σ.pts
  have hfor := runs_forN (L := L) (w := w) (body := .seq (sconst L s 0) (.seq (nsub kA kC j)
      (.seq (nsub kB kC kA) (.seq (forN l dv one (.seq (aget L t1 A kA) (.seq (aget L t2 B kB)
        (.seq (sop2 L .mul t1 t1 t2) (.seq (sop2 L .add s s t1) (.seq (nadd kA kA one) (nadd kB kB dv)))))))
      (.seq (aset L C kC s) (nadd kC kC one)))))) hj hdv hone (Ne.symm hdvj) (Ne.symm honej) d (d * 11 + 9) J σ
      hd h1
    ⟨by simp [Ne.symm hjkC, hkC0], fun c hc => absurd hc (Nat.not_lt_zero _), fun m _ => by simp,
      fun b _ => by simp, fun z _ _ _ => by simp, fun q hqj _ _ _ _ => by simp [hqj], by simp, by simp, by simp⟩
    (fun t ht σ' hJ hjt hdt hot => by
      obtain ⟨Jk, JC, Jhi, Jb, Js, Jn, Jd, Jr, Jp⟩ := hJ
      have eA : σ'.arr A = σ.arr A := Jb A (Ne.symm hCA)
      have eB : σ'.arr B = σ.arr B := Jb B (Ne.symm hCB)
      refine runs_mono (K := 1 + (1 + (1 + ((d * 11 + 3) + (2 + 1))))) ?_ (le_of_eq (by ring)) (fun σ'' h => h)
      refine runs_seq_eq (runs_sconst hs 0) (runs_seq_eq (runs_nsub hkA hkC hj) (runs_seq_eq (runs_nsub hkB hkC hkA)
        (runs_seq (runs_mmulDot (w := w) _ r ⟨t, ht⟩ hdv hone hl hkA hkB hA hB hs ht1 ht2 (Ne.symm hdvl)
          (Ne.symm honel) hlkA hlkB hkAkB (Ne.symm hdvkA) (Ne.symm honekA) (Ne.symm hdvkB) (Ne.symm honekB) hs1 hs2
          h12 ?_ ?_ ?_ ?_) (fun σ4 h4 => ?_))))
      · simp [hdvkA, hdvkB, hdt]
      · simp [honekA, honekB, hot]
      · simp [Ne.symm hkAkC, Jk, hjt, hkAkB]
      · simp [Ne.symm hkAkC, Jk, hjt]
      obtain ⟨S4, -, -, F4n, F4s, F4a, F4d, F4r, F4p⟩ := h4
      have n4 : ∀ q, q ≠ l → q ≠ kA → q ≠ kB → σ4.nat q = σ'.nat q := fun q h1 h2 h3 => by
        rw [F4n q (by simp [h1, h2, h3])]; simp [h2, h3]
      have k4 : σ4.nat kC = d * r + t := by rw [n4 kC (Ne.symm hlkC) (Ne.symm hkAkC) (Ne.symm hkBkC), Jk]
      have a4 : ∀ a, σ4.arr a = σ'.arr a := fun a => by rw [F4a a (by simp)]; simp
      refine runs_seq_eq (runs_aset hC hkC hs (by rw [k4]; exact idx_lt_asz r.2 ht))
        (runs_mono (runs_nadd hkC hkC hone) le_rfl (fun σ6 e6 => ?_))
      subst e6
      have o4 : σ4.nat one = 1 := by rw [n4 one honel honekA honekB, hot]
      have mA : ∀ (v : ℝ) (u u2 : ℕ), (((σ'.setSc s v).setNat kA u).setNat kB u2).mat A = σ.mat A := fun _ _ _ => by
        unfold Env.mat; simp only [Env.setNat_arr, Env.setSc_arr, eA]; rfl
      have mB : ∀ (v : ℝ) (u u2 : ℕ), (((σ'.setSc s v).setNat kA u).setNat kB u2).mat B = σ.mat B := fun _ _ _ => by
        unfold Env.mat; simp only [Env.setNat_arr, Env.setSc_arr, eB]; rfl
      refine ⟨by simp [hjkC, n4 j hjl hjkA hjkB, hjt], by simp [hdvkC, n4 dv hdvl hdvkA hdvkB, hdt],
        by simp [honekC, o4], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [Ne.symm hjkC, k4, o4]; ring
      · intro c hc
        simp only [Env.setNat_arr, Env.setArr_arr, true_and, k4, a4]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc' | hc'
        · have hne : d * (r : ℕ) + c ≠ d * r + t := by omega
          simp only [hne, ↓reduceIte]; exact JC c hc'
        · have hc2 : c = (⟨t, ht⟩ : Fin d) := Fin.ext hc'
          subst hc2
          simp only [↓reduceIte, S4, mA, mB, Env.setNat_sc, Env.setSc_sc, Rat.cast_zero, zero_add]
      · intro m hm
        have hne : m ≠ d * r + t := by omega
        simp only [Env.setNat_arr, Env.setArr_arr, true_and, k4, a4, hne, ↓reduceIte]
        exact Jhi m (by omega)
      · intro b hb
        funext m
        simp only [Env.setNat_arr, Env.setArr_arr, hb, false_and, ite_false, a4, Jb b hb]
      · intro z hz1 hz2 hz3
        simp only [Env.setNat_sc, Env.setArr_sc]
        rw [F4s z (by simp [hz1, hz2, hz3])]; simp [hz1, Js z hz1 hz2 hz3]
      · intro q hqj hql hqA hqB hqC
        simp [hqj, hqC, n4 q hql hqA hqB, Jn q hqj hql hqA hqB hqC]
      · simp [F4d, Jd]
      · simp [F4r, Jr]
      · simp [F4p, Jp])
  refine runs_mono hfor (le_of_eq (by ring)) (fun σ' h => ?_)
  obtain ⟨⟨Jk, JC, Jhi, Jb, Js, Jn, Jd, Jr, Jp⟩, -, -, -⟩ := h
  refine ⟨fun c => JC c c.2, Jhi, Jk, ⟨fun q hq => ?_, fun z hz => ?_, fun b hb => Jb b (by simpa using hb), Jd, Jr, Jp⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    exact Jn q hq.1 hq.2.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    exact Js z hz.1 hz.2.1 hz.2.2

/-- The rule of `mmul`: `C := A B` (`C ≠ A`, `C ≠ B`). -/
theorem runs_mmul {dv one i j l kA kB kC C A B s t1 t2 : ℕ} (σ : Env d) (hdv : dv < L.NN) (hone : one < L.NN)
    (hi : i < L.NN) (hj : j < L.NN) (hl : l < L.NN) (hkA : kA < L.NN) (hkB : kB < L.NN) (hkC : kC < L.NN)
    (hC : C < L.NA) (hA : A < L.NA) (hB : B < L.NA) (hs : s < L.NS) (ht1 : t1 < L.NS) (ht2 : t2 < L.NS)
    (hN : [i, j, l, kA, kB, kC].Nodup) (hdvN : dv ∉ [i, j, l, kA, kB, kC]) (honeN : one ∉ [i, j, l, kA, kB, kC])
    (hCA : C ≠ A) (hCB : C ≠ B) (hs1 : s ≠ t1) (hs2 : s ≠ t2) (h12 : t1 ≠ t2) (hd : σ.nat dv = d)
    (h1 : σ.nat one = 1) :
    Runs L w (mmul L dv one i j l kA kB kC C A B s t1 t2) σ (d * (d * (d * 11 + 12) + 6) + 4)
      (fun σ' => σ'.mat C = σ.mat A * σ.mat B ∧ Env.Frame σ σ' [i, j, l, kA, kB, kC] [s, t1, t2] [C] ∧
        ∀ m, d * d ≤ m → σ'.arr C m = σ.arr C m) := by
  have hN' : [j, l, kA, kB, kC].Nodup := (List.nodup_cons.1 hN).2
  have hiN : i ∉ [j, l, kA, kB, kC] := (List.nodup_cons.1 hN).1
  have hidv : i ≠ dv := fun e => hdvN (by simp [e])
  have hione : i ≠ one := fun e => honeN (by simp [e])
  have hdvN' : dv ∉ [j, l, kA, kB, kC] := fun h' => hdvN (List.mem_cons_of_mem _ h')
  have honeN' : one ∉ [j, l, kA, kB, kC] := fun h' => honeN (List.mem_cons_of_mem _ h')
  have hkCi : kC ≠ i := fun e => hiN (by simp [e])
  have hkCdv : kC ≠ dv := fun e => hdvN (by simp [e])
  have hkCone : kC ≠ one := fun e => honeN (by simp [e])
  let J : ℕ → Env d → Prop := fun t σ' =>
    σ'.nat kC = d * t ∧ (∀ (r c : Fin d), (r : ℕ) < t → σ'.arr C (d * r + c) = (σ.mat A * σ.mat B) r c) ∧
      (∀ m, d * t ≤ m → σ'.arr C m = σ.arr C m) ∧ (∀ b, b ≠ C → σ'.arr b = σ.arr b) ∧
      (∀ z, z ∉ [s, t1, t2] → σ'.sc z = σ.sc z) ∧
      (∀ q, q ≠ i → q ∉ [j, l, kA, kB, kC] → σ'.nat q = σ.nat q) ∧ σ'.draws = σ.draws ∧ σ'.rounds = σ.rounds ∧
      σ'.pts = σ.pts
  have hd0 : (σ.setNat kC 0).nat dv = d := by simp [Ne.symm hkCdv, hd]
  have h10 : (σ.setNat kC 0).nat one = 1 := by simp [Ne.symm hkCone, h1]
  have hfor := runs_forN (L := L) (w := w) (body := forN j dv one (.seq (sconst L s 0) (.seq (nsub kA kC j)
      (.seq (nsub kB kC kA) (.seq (forN l dv one (.seq (aget L t1 A kA) (.seq (aget L t2 B kB)
        (.seq (sop2 L .mul t1 t1 t2) (.seq (sop2 L .add s s t1) (.seq (nadd kA kA one) (nadd kB kB dv)))))))
      (.seq (aset L C kC s) (nadd kC kC one))))))) hi hdv hone hidv hione d (d * (d * 11 + 12) + 3) J
      (σ.setNat kC 0) hd0 h10
    ⟨by simp [hkCi], fun r c h => absurd h (Nat.not_lt_zero _), fun m _ => by simp, fun b _ => by simp,
      fun z _ => by simp, fun q hqi hq => by simp [hqi]; intro e; exact absurd (by simp [e]) hq, rfl, rfl, rfl⟩
    (fun t ht σ' hJ hit hdt hot => by
      obtain ⟨Jk, JC, Jhi, Jb, Js, Jn, Jd, Jr, Jp⟩ := hJ
      refine runs_mono (runs_mmulRow (w := w) σ' ⟨t, ht⟩ hdv hone hj hl hkA hkB hkC hC hA hB hs ht1 ht2 hN' hdvN'
        honeN' hCA hCB hs1 hs2 h12 hdt hot Jk) le_rfl (fun σ2 h2 => ?_)
      obtain ⟨R2, O2, K2, F2n, F2s, F2a, F2d, F2r, F2p⟩ := h2
      have eA : σ'.mat A = σ.mat A := by unfold Env.mat; rw [Jb A (Ne.symm hCA)]
      have eB : σ'.mat B = σ.mat B := by unfold Env.mat; rw [Jb B (Ne.symm hCB)]
      refine ⟨by rw [F2n i hiN, hit], by rw [F2n dv hdvN', hdt], by rw [F2n one honeN', hot], ?_⟩
      refine ⟨by simp [hkCi, K2]; ring, fun r c hr => ?_, fun m hm => ?_, fun b hb => ?_, fun z hz => ?_,
        fun q hqi hq => ?_, by simp [F2d, Jd], by simp [F2r, Jr], by simp [F2p, Jp]⟩
      · simp only [Env.setNat_arr]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr' | hr'
        · have hlt : d * r + c < d * t := by
            have := c.2
            calc d * (r : ℕ) + c < d * r + d := by omega
              _ = d * (r + 1) := by ring
              _ ≤ d * t := Nat.mul_le_mul_left _ hr'
          rw [O2 _ (Or.inl hlt), JC r c hr']
        · have hr2 : r = (⟨t, ht⟩ : Fin d) := Fin.ext hr'
          rw [hr2, R2 c, eA, eB]
      · simp only [Env.setNat_arr]
        rw [O2 m (Or.inr (by rw [Nat.mul_succ] at hm; exact hm)), Jhi m (by rw [Nat.mul_succ] at hm; omega)]
      · simp only [Env.setNat_arr]; rw [F2a b (by simpa using hb), Jb b hb]
      · simp only [Env.setNat_sc]; rw [F2s z hz, Js z hz]
      · simp only [Env.setNat_nat, hqi, ite_false]; rw [F2n q hq, Jn q hqi hq])
  refine runs_mono (K := 1 + (d * ((d * (d * 11 + 12) + 3) + 3) + 3)) (runs_seq_eq (runs_nconst hkC 0) hfor)
    (le_of_eq (by ring)) (fun σ' h => ?_)
  obtain ⟨⟨Jk, JC, Jhi, Jb, Js, Jn, Jd, Jr, Jp⟩, -, -, -⟩ := h
  refine ⟨?_, ⟨fun q hq => ?_, fun z hz => Js z hz, fun b hb => Jb b (by simpa using hb), Jd, Jr, Jp⟩, Jhi⟩
  · ext r c
    exact JC r c r.2
  · have hqi : q ≠ i := fun e => hq (by simp [e])
    have hq' : q ∉ [j, l, kA, kB, kC] := fun h' => hq (List.mem_cons_of_mem _ h')
    rw [Jn q hqi hq']

/-- The rule of `mtransp`: `B := Aᵀ` (`B ≠ A`). -/
theorem runs_mtransp {dv one i j kA kB B A t : ℕ} (σ : Env d) (hdv : dv < L.NN) (hone : one < L.NN)
    (hi : i < L.NN) (hj : j < L.NN) (hkA : kA < L.NN) (hkB : kB < L.NN) (hB : B < L.NA) (hA : A < L.NA)
    (ht : t < L.NS) (hBA : B ≠ A) (hN : [i, j, kA, kB].Nodup) (hdvN : dv ∉ [i, j, kA, kB])
    (honeN : one ∉ [i, j, kA, kB]) (hd : σ.nat dv = d) (h1 : σ.nat one = 1) :
    Runs L w (mtransp L dv one i j kA kB B A t) σ (d * (d * 9 + 8) + 4)
      (fun σ' => σ'.mat B = (σ.mat A)ᵀ ∧ Env.Frame σ σ' [i, j, kA, kB] [t] [B] ∧
        ∀ m, d * d ≤ m → σ'.arr B m = σ.arr B m) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
    at hN hdvN honeN
  obtain ⟨⟨hij, hikA, hikB⟩, ⟨hjkA, hjkB⟩, hkAkB, -⟩ := hN
  obtain ⟨hdvi, hdvj, hdvkA, hdvkB⟩ := hdvN
  obtain ⟨honei, honej, honekA, honekB⟩ := honeN
  let g : ℕ → ℝ := fun m => σ.arr A (d * (m % d) + m / d)
  let J : ℕ → Env d → Prop := fun u σ' =>
    σ'.nat kB = d * u ∧ (∀ m, σ'.arr B m = if m < d * u then g m else σ.arr B m) ∧
      (∀ b, b ≠ B → σ'.arr b = σ.arr b) ∧ (∀ z, z ≠ t → σ'.sc z = σ.sc z) ∧
      (∀ q, q ≠ i → q ≠ j → q ≠ kA → q ≠ kB → σ'.nat q = σ.nat q) ∧ σ'.draws = σ.draws ∧
      σ'.rounds = σ.rounds ∧ σ'.pts = σ.pts
  have hdk : (σ.setNat kB 0).nat dv = d := by simp [hdvkB, hd]
  have h1k : (σ.setNat kB 0).nat one = 1 := by simp [honekB, h1]
  have hfor := runs_forN (L := L) (w := w) (body := .seq (nconst kA 0) (.seq (nadd kA kA i) (forN j dv one
      (.seq (aget L t A kA) (.seq (aset L B kB t) (.seq (nadd kA kA dv) (nadd kB kB one))))))) hi hdv hone
      (Ne.symm hdvi) (Ne.symm honei) d (d * 9 + 5) J (σ.setNat kB 0) hdk h1k
    ⟨by simp [Ne.symm hikB], fun m => by simp, fun b _ => rfl, fun z _ => rfl,
      fun q hqi _ _ hqB => by simp [hqi, hqB], rfl, rfl, rfl⟩
    (fun u hu σ' hJ hiu hdu hou => by
      obtain ⟨Jk, JB, Jb, Js, Jn, Jd, Jr, Jp⟩ := hJ
      refine runs_mono (K := 1 + (1 + (d * 9 + 3))) ?_ (le_of_eq (by ring)) (fun σ'' h => h)
      refine runs_seq_eq (runs_nconst hkA 0) (runs_seq_eq (runs_nadd hkA hkA hi)
        (runs_mono (runs_mtranspRow (w := w) _ ⟨u, hu⟩ hdv hone hj hkA hkB hB hA ht hBA (Ne.symm hdvj)
          (Ne.symm honej) hjkA hjkB hkAkB (Ne.symm hdvkA) (Ne.symm honekA) (Ne.symm hdvkB) (Ne.symm honekB)
          ?_ ?_ ?_ ?_) le_rfl (fun σ4 h4 => ?_)))
      · simp [hdvkA, hdu]
      · simp [honekA, hou]
      · simp [hiu, hikA]
      · simp [Ne.symm hkAkB, Jk]
      obtain ⟨R4, -, K4, F4n, F4s, F4a, F4d, F4r, F4p⟩ := h4
      have n4 : ∀ q, q ≠ j → q ≠ kA → q ≠ kB → σ4.nat q = σ'.nat q := fun q h1 h2 h3 => by
        rw [F4n q (by simp [h1, h2, h3])]; simp [h2]
      have eA : σ'.arr A = σ.arr A := Jb A (Ne.symm hBA)
      refine ⟨by rw [n4 i hij hikA hikB, hiu], by rw [n4 dv hdvj hdvkA hdvkB, hdu],
        by rw [n4 one honej honekA honekB, hou], ?_⟩
      refine ⟨by simp [Ne.symm hikB, K4]; ring, fun m => ?_, fun b hb => ?_, fun z hz => ?_,
        fun q hqi hqj hqA hqB => ?_, by simp [F4d, Jd], by simp [F4r, Jr], by simp [F4p, Jp]⟩
      · simp only [Env.setNat_arr]
        rw [R4 m]
        simp only [Env.setNat_arr, eA, JB m]
        by_cases hm1 : m < d * u
        · have : m < d * (u + 1) := by rw [Nat.mul_succ]; omega
          simp [hm1, this, show ¬ d * u ≤ m by omega]
        · by_cases hm2 : m < d * u + d
          · have hq : m / d = u :=
              Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; omega) (by rw [Nat.add_mul, one_mul, Nat.mul_comm]; omega)
            have hr : m % d = m - d * u := by rw [Nat.mod_eq_sub_mul_div, hq, Nat.mul_comm]
            simp only [hm1, ite_false, show d * u ≤ m by omega, hm2, and_self, ite_true,
              show m < d * (u + 1) by rw [Nat.mul_succ]; omega, g, hq, hr]
          · simp [hm1, hm2, show ¬ m < d * (u + 1) by rw [Nat.mul_succ]; omega]
      · simp only [Env.setNat_arr]; rw [F4a b (by simpa using hb)]; simp [Jb b hb]
      · simp only [Env.setNat_sc]; rw [F4s z (by simpa using hz)]; simp [Js z hz]
      · simp [hqi, n4 q hqj hqA hqB, Jn q hqi hqj hqA hqB])
  refine runs_mono (K := 1 + (d * ((d * 9 + 5) + 3) + 3)) (runs_seq_eq (runs_nconst hkB 0) hfor)
    (le_of_eq (by ring)) (fun σ' h => ?_)
  obtain ⟨⟨Jk, JB, Jb, Js, Jn, Jd, Jr, Jp⟩, -, -, -⟩ := h
  refine ⟨?_, ⟨fun q hq => ?_, fun z hz => Js z (by simpa using hz), fun b hb => Jb b (by simpa using hb), Jd, Jr,
    Jp⟩, fun m hm => by rw [JB]; simp; omega⟩
  · funext a b
    have hab : d * (a : ℕ) + b < d * d := idx_lt_sq a.2 b.2
    have hpos : 0 < d := Nat.pos_of_ne_zero (fun h => by subst h; exact a.elim0)
    have hq : (d * (a : ℕ) + b) / d = a := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt b.2, Nat.zero_add]
    have hr : (d * (a : ℕ) + b) % d = b := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.2]
    simp only [Env.mat, JB, hab, ite_true, g, hq, hr, Matrix.transpose_apply]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    rw [Jn q hq.1 hq.2.1 hq.2.2.1 hq.2.2.2]

end AdversarialBco.Poly.Mach.VL
