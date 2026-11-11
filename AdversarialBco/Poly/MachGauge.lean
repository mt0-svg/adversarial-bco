/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachVec
public import AdversarialBco.Poly.PgLemmas

@[expose] public section

/-!
# The machine layer: the gauge by bisection

`runs_gaugeBis`: the code `gaugeBis` of `MachVec.lean` computes `piTilde Q ρ j x` of `PgLemmas.lean` for any set `Q`
whose membership a code `memQ` decides (the answer `1` or `0` in a scalar), within
`j (15 d + Kq + 16) + 9 d + 15` steps, `Kq` the steps of one call of `memQ`. The positioned bodies of PG and DF2 are
instances (`memQ` built from `memAff`).
-/

namespace AdversarialBco.Poly.Mach.VL

open AdversarialBco AdversarialBco.RealRAM Matrix

variable {d : ℕ} {L : Layout} {w : World d}

theorem bisect_succ_pos {P : ℝ → Prop} {lo hi a b : ℝ} {j : ℕ} (hB : bisect P lo hi j = (a, b))
    (hP : P ((a + b) / 2)) : bisect P lo hi (j + 1) = (a, (a + b) / 2) := by
  simp only [bisect, hB, hP, ite_true]

theorem bisect_succ_neg {P : ℝ → Prop} {lo hi a b : ℝ} {j : ℕ} (hB : bisect P lo hi j = (a, b))
    (hP : ¬ P ((a + b) / 2)) : bisect P lo hi (j + 1) = ((a + b) / 2, b) := by
  simp only [bisect, hB, hP, ite_false]

open Classical in
theorem runs_gaugeBis {memQ : Cmd} {dv one i jj jv x yv ρ qo pv nx sl su mid inv z h o t1 t2 : ℕ}
    (Q : Set (E d)) (Iq : Env d → Prop) (Kq : ℕ) (nsQ ssQ asQ : List ℕ) (σ : Env d)
    (hdv : dv < L.NN) (hone : one < L.NN) (hi : i < L.NN) (hjj : jj < L.NN) (hjv : jv < L.NN)
    (hx : x < L.NA) (hyv : yv < L.NA) (hρ : ρ < L.NS) (hpv : pv < L.NS) (hnx : nx < L.NS)
    (hsl : sl < L.NS) (hsu : su < L.NS) (hmid : mid < L.NS) (hinv : inv < L.NS) (hz : z < L.NS) (hh : h < L.NS)
    (ho : o < L.NS) (ht1 : t1 < L.NS) (ht2 : t2 < L.NS) (hqo : qo < L.NS)
    (hidv : i ≠ dv) (hione : i ≠ one) (hjjdv : jj ≠ dv) (hjjone : jj ≠ one) (hjjjv : jj ≠ jv) (hijj : i ≠ jj)
    (hijv : i ≠ jv) (hyx : yv ≠ x)
    (hS : [nx, sl, su, mid, inv, z, h, o, t1, t2].Nodup) (hρS : ρ ∉ [nx, z, h, o, t1, t2])
    (hnQ : ∀ q ∈ [dv, one, jj, jv], q ∉ nsQ) (hsQ : ∀ s ∈ [sl, su, mid, z, h, o], s ∉ ssQ) (hxQ : x ∉ asQ)
    (hd : σ.nat dv = d) (h1 : σ.nat one = 1) (hI : Iq σ)
    (hmem : ∀ σ', Iq σ' → σ'.nat dv = d → σ'.nat one = 1 → Runs L w memQ σ' Kq (fun σ'' =>
      σ''.sc qo = (if WithLp.toLp 2 (σ'.vec yv) ∈ Q then 1 else 0) ∧ Env.Frame σ' σ'' nsQ ssQ asQ ∧ Iq σ''))
    (hIq : ∀ σ' σ'', Iq σ' → Env.Frame σ' σ'' [i, jj] [nx, sl, su, mid, inv, z, h, o, t1, t2, pv] [yv] →
      Iq σ'') :
    Runs L w (gaugeBis L memQ dv one i jj jv x yv ρ qo pv nx sl su mid inv z h o t1 t2) σ
      (σ.nat jv * (d * 15 + Kq + 16) + d * 9 + 15)
      (fun σ' => σ'.sc pv = piTilde Q (σ.sc ρ) (σ.nat jv) (WithLp.toLp 2 (σ.vec x)) ∧
        Env.Frame σ σ' (i :: jj :: nsQ) ([nx, sl, su, mid, inv, z, h, o, t1, t2, pv] ++ ssQ) (yv :: asQ) ∧
        Iq σ') := by
  -- distinctness
  have hS' := hS
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, List.nodup_nil, and_true, or_false] at hS'
  obtain ⟨⟨nsl, -, -, -, nz, nh, no, nt1, nt2⟩, ⟨slsu, slmid, slinv, slz, slh, slo, slt1, -⟩,
    ⟨sumid, suinv, suz, suh, suo, sut1, -⟩, ⟨midinv, midz, midh, mido, midt1, -⟩,
    ⟨invz, invh, invo, invt1, -⟩, ⟨zh, zo, zt1, -⟩, ⟨ho', ht1', -⟩, ⟨ot1, -⟩, t1t2, -⟩ := hS'
  have hρnx : ρ ≠ nx := fun e => hρS (by simp [e])
  have hρz : ρ ≠ z := fun e => hρS (by simp [e])
  have hρh : ρ ≠ h := fun e => hρS (by simp [e])
  have hρo : ρ ≠ o := fun e => hρS (by simp [e])
  have hρ1 : ρ ≠ t1 := fun e => hρS (by simp [e])
  have hρ2 : ρ ≠ t2 := fun e => hρS (by simp [e])
  set X := σ.vec x with hX
  set N := σ.nat jv with hN
  set ρ0 := σ.sc ρ with hρ0
  set nX := Real.sqrt (X ⬝ᵥ X) with hnX
  let oN : List ℕ := [i, jj]
  let oS : List ℕ := [nx, sl, su, mid, inv, z, h, o, t1, t2, pv]
  let oA : List ℕ := [yv]
  -- the facts kept along the run
  let G : Env d → Prop := fun σ' => Iq σ' ∧ σ'.arr x = σ.arr x ∧ σ'.nat dv = d ∧ σ'.nat one = 1 ∧ σ'.nat jv = N ∧
    Env.Frame σ σ' (i :: jj :: nsQ) (oS ++ ssQ) (yv :: asQ)
  have hown : ∀ σa σb, G σa → Env.Frame σa σb oN oS oA → G σb := by
    intro σa σb ⟨ga1, ga2, ga3, ga4, ga5, ga6⟩ hf
    refine ⟨hIq σa σb ga1 hf, ?_, ?_, ?_, ?_, Env.Frame.trans ga6 (Env.Frame.mono hf ?_ ?_ ?_)⟩
    · rw [hf.2.2.1 x (by simp [oA, Ne.symm hyx])]; exact ga2
    · rw [hf.1 dv (by simp [oN, Ne.symm hidv, Ne.symm hjjdv])]; exact ga3
    · rw [hf.1 one (by simp [oN, Ne.symm hione, Ne.symm hjjone])]; exact ga4
    · rw [hf.1 jv (by simp [oN, Ne.symm hijv, Ne.symm hjjjv])]; exact ga5
    · intro q hq; simp [oN] at hq ⊢; tauto
    · intro q hq; simp only [List.mem_append]; exact Or.inl hq
    · intro q hq; simp [oA] at hq ⊢; tauto
  have hG0 : G σ := ⟨hI, rfl, hd, h1, rfl, Env.Frame.refl _ _ _ _⟩
  have hmemG : ∀ σa σb, G σa → Env.Frame σa σb nsQ ssQ asQ → Iq σb → G σb := by
    intro σa σb ⟨_, ga2, ga3, ga4, ga5, ga6⟩ hf hIb
    refine ⟨hIb, ?_, ?_, ?_, ?_, Env.Frame.trans ga6 (Env.Frame.mono hf ?_ ?_ ?_)⟩
    · rw [hf.2.2.1 x hxQ]; exact ga2
    · rw [hf.1 dv (hnQ dv (by simp))]; exact ga3
    · rw [hf.1 one (hnQ one (by simp))]; exact ga4
    · rw [hf.1 jv (hnQ jv (by simp))]; exact ga5
    · intro q hq; simp [hq]
    · intro q hq; simp [hq]
    · intro q hq; simp [hq]
  have hsc : ∀ σa (q : ℕ) (v : ℝ), q ∈ oS → G σa → G (σa.setSc q v) := fun σa q v hq ga =>
    hown σa _ ga (Env.Frame.setSc (Env.Frame.refl _ _ _ _) hq v)
  have hvx : ∀ σa, G σa → σa.vec x = X := fun σa ga => by
    funext k; simp only [Env.vec, ga.2.1, hX]
  -- the norm
  have hvn : Runs L w (vnorm L dv one i nx x t1 t2) σ (d * 9 + 4 + 1)
      (fun σ1 => σ1.sc nx = nX ∧ σ1.sc ρ = ρ0 ∧ G σ1) :=
    runs_seq (runs_vdot (L := L) (w := w) σ hdv hone hi hnx hx hx ht1 ht2 hidv hione nt1 nt2 t1t2 hd h1)
      (fun σa ha => runs_mono (runs_sop1 (σ := σa) hnx hnx .sqrt) le_rfl (fun σb e => by
        subst e
        refine ⟨by simp [ha.1, Op1.eval, hnX, hX], ?_, hown σ _ hG0 ?_⟩
        · simp only [Env.setSc_sc, hρnx, ite_false]; exact ha.2.2.1 ρ (by simp [hρnx, hρ1, hρ2])
        · exact Env.Frame.setSc (Env.Frame.mono (ns' := oN) (ss' := oS) (as' := oA) ha.2 (by simp [oN])
            (by simp [oS]) (by simp)) (by simp [oS]) _))
  -- the bisection
  let P : ℝ → Prop := fun s => 0 < s ∧ s⁻¹ • WithLp.toLp 2 X ∈ Q
  let JG : ℕ → Env d → Prop := fun t σ' => G σ' ∧ σ'.sc sl = (bisect P (nX / ρ0) nX t).1 ∧
    σ'.sc su = (bisect P (nX / ρ0) nX t).2 ∧ σ'.sc z = 0 ∧ σ'.sc h = 1 / 2 ∧ σ'.sc o = 1
  have hbody : ∀ t < N, ∀ σ', JG t σ' → σ'.nat jj = t → σ'.nat jv = N → σ'.nat one = 1 →
      Runs L w (.seq (sop2 L .add mid sl su) (.seq (sop2 L .mul mid mid h)
        (ifS L z mid
          (.seq (sop2 L .div inv o mid) (.seq (vcopy L dv one i yv x t1) (.seq (vscale L dv one i yv inv t1)
            (.seq memQ (ifS L z qo (smov L su mid) (smov L sl mid))))))
          (smov L sl mid)))) σ' (d * 15 + Kq + 13)
        (fun σ'' => σ''.nat jj = t ∧ σ''.nat jv = N ∧ σ''.nat one = 1 ∧ JG (t + 1) (σ''.setNat jj (t + 1))) := by
    intro t _ σ' hJ hjt _ _
    obtain ⟨g', esl, esu, ez, eh, eo⟩ := hJ
    obtain ⟨bl, bu, hB⟩ : ∃ bl bu, bisect P (nX / ρ0) nX t = (bl, bu) := ⟨_, _, rfl⟩
    rw [hB] at esl esu
    have post : ∀ σ'', JG (t + 1) σ'' → σ''.nat jj = t →
        σ''.nat jj = t ∧ σ''.nat jv = N ∧ σ''.nat one = 1 ∧ JG (t + 1) (σ''.setNat jj (t + 1)) := by
      intro σ'' hJ' hj
      obtain ⟨g'', e1, e2, e3, e4, e5⟩ := hJ'
      exact ⟨hj, g''.2.2.2.2.1, g''.2.2.2.1,
        hown σ'' _ g'' (Env.Frame.setNat (Env.Frame.refl _ _ _ _) (by simp [oN]) _),
        by simpa using e1, by simpa using e2, by simpa using e3, by simpa using e4, by simpa using e5⟩
    refine runs_mono (K := 1 + (1 + (d * 15 + Kq + 11))) (Q := fun σ'' => JG (t + 1) σ'' ∧ σ''.nat jj = t) ?_
      (by omega) (fun σ'' h => post σ'' h.1 h.2)
    refine runs_seq (runs_sop2 hmid hsl hsu .add) (fun σa ea => runs_seq (runs_sop2 hmid hmid hh .mul)
      (fun σb eb => ?_))
    have gb : G σb := by rw [eb, ea]; exact hsc _ _ _ (by simp [oS]) (hsc _ _ _ (by simp [oS]) g')
    have kb : ∀ q, q ≠ mid → σb.sc q = σ'.sc q := fun q hq => by rw [eb, ea]; simp [hq]
    have bjj : σb.nat jj = t := by rw [eb, ea]; simpa using hjt
    have bmid : σb.sc mid = (bl + bu) / 2 := by
      rw [eb, ea]; simp only [Env.setSc_sc, ite_true, Op2.eval, Ne.symm midh, ite_false, esl, esu, eh]; ring
    have bz : σb.sc z = 0 := by rw [kb z (Ne.symm midz), ez]
    by_cases hm : 0 < (bl + bu) / 2
    · refine runs_mono (K := (1 + ((d * 7 + 3) + ((d * 8 + 3) + (Kq + 3)))) + 1)
        (runs_ifS_t hz hmid (by rw [bz, bmid]; exact hm) ?_) (by omega) (fun _ h => h)
      refine runs_seq (runs_sop2 hinv ho hmid .div) (fun σc ec => ?_)
      have gc : G σc := by rw [ec]; exact hsc _ _ _ (by simp [oS]) gb
      have cinv : σc.sc inv = ((bl + bu) / 2)⁻¹ := by
        rw [ec]; simp only [Env.setSc_sc, ite_true, Op2.eval, kb o (Ne.symm mido), eo, bmid, one_div]
      have kc : ∀ q, q ≠ inv → σc.sc q = σb.sc q := fun q hq => by rw [ec]; simp [hq]
      have cjj : σc.nat jj = t := by rw [ec]; simpa using bjj
      refine runs_seq (runs_vcopy σc hdv hone hi hyv hx ht1 hidv hione gc.2.2.1 gc.2.2.2.1) (fun σd hd' => ?_)
      obtain ⟨ed, fd, -⟩ := hd'
      have gd : G σd := hown σc σd gc (Env.Frame.mono fd (by simp [oN]) (by simp [oS]) (by simp [oA]))
      refine runs_seq (runs_vscale σd hdv hone hi hyv hinv ht1 hidv hione invt1 gd.2.2.1 gd.2.2.2.1)
        (fun σe he => ?_)
      obtain ⟨ee, fe, -⟩ := he
      have ge : G σe := hown σd σe gd (Env.Frame.mono fe (by simp [oN]) (by simp [oS]) (by simp [oA]))
      have eye : WithLp.toLp 2 (σe.vec yv) = ((bl + bu) / 2)⁻¹ • WithLp.toLp 2 X := by
        rw [ee, fd.2.1 inv (by simpa using invt1), cinv, ed, hvx σc gc, WithLp.toLp_smul]
      refine runs_seq (hmem σe ge.1 ge.2.2.1 ge.2.2.2.1) (fun σf hf => ?_)
      obtain ⟨eqo, ff, Iqf⟩ := hf
      have gf : G σf := hmemG σe σf ge ff Iqf
      have kf : ∀ q, q ≠ t1 → q ≠ inv → q ∉ ssQ → σf.sc q = σb.sc q := fun q h1' h2' h3' => by
        rw [ff.2.1 q h3', fe.2.1 q (by simpa using h1'), fd.2.1 q (by simpa using h1'), kc q h2']
      have fjj : σf.nat jj = t := by
        rw [ff.1 jj (hnQ jj (by simp)), fe.1 jj (by simpa using Ne.symm hijj), fd.1 jj (by simpa using Ne.symm hijj),
          cjj]
      have fz : σf.sc z = 0 := by rw [kf z zt1 (Ne.symm invz) (hsQ z (by simp)), bz]
      have fmid : σf.sc mid = (bl + bu) / 2 := by rw [kf mid midt1 midinv (hsQ mid (by simp)), bmid]
      have fsl : σf.sc sl = bl := by rw [kf sl slt1 slinv (hsQ sl (by simp)), kb sl slmid, esl]
      have fsu : σf.sc su = bu := by rw [kf su sut1 suinv (hsQ su (by simp)), kb su sumid, esu]
      have fh : σf.sc h = 1 / 2 := by rw [kf h ht1' (Ne.symm invh) (hsQ h (by simp)), kb h (Ne.symm midh), eh]
      have fo : σf.sc o = 1 := by rw [kf o ot1 (Ne.symm invo) (hsQ o (by simp)), kb o (Ne.symm mido), eo]
      by_cases hq : WithLp.toLp 2 (σe.vec yv) ∈ Q
      · have hP : P ((bl + bu) / 2) := by
          show 0 < _ ∧ _
          exact ⟨hm, by rw [← eye]; exact hq⟩
        refine runs_mono (K := 1 + 1) (runs_ifS_t hz hqo (by simp only [fz, eqo, hq, ite_true]; norm_num)
          (runs_smov hsu hmid)) (by omega) (fun σg eg => ?_)
        rw [eg]
        refine ⟨⟨hsc _ _ _ (by simp [oS]) gf, ?_, ?_, ?_, ?_, ?_⟩, by simpa using fjj⟩ <;>
          (try rw [bisect_succ_pos hB hP]) <;> simp [slsu, Ne.symm suz, Ne.symm suh, Ne.symm suo, fsl, fmid, fz, fh, fo]
      · have hP : ¬ P ((bl + bu) / 2) := by
          rintro ⟨-, h'⟩
          exact hq (by rw [eye]; exact h')
        refine runs_mono (K := 1 + 2) (runs_ifS_f hz hqo (by simp only [fz, eqo, hq, ite_false]; norm_num)
          (runs_smov hsl hmid)) (by omega) (fun σg eg => ?_)
        rw [eg]
        refine ⟨⟨hsc _ _ _ (by simp [oS]) gf, ?_, ?_, ?_, ?_, ?_⟩, by simpa using fjj⟩ <;>
          (try rw [bisect_succ_neg hB hP]) <;>
          simp [Ne.symm slsu, Ne.symm slz, Ne.symm slh, Ne.symm slo, fsu, fmid, fz, fh, fo]
    · have hP : ¬ P ((bl + bu) / 2) := fun h' => hm h'.1
      refine runs_mono (K := 1 + 2) (runs_ifS_f hz hmid (by rw [bz, bmid]; exact hm) (runs_smov hsl hmid))
        (by omega) (fun σg eg => ?_)
      rw [eg]
      refine ⟨⟨hsc _ _ _ (by simp [oS]) gb, ?_, ?_, ?_, ?_, ?_⟩, by simpa using bjj⟩ <;>
        (try rw [bisect_succ_neg hB hP]) <;>
        simp [Ne.symm slsu, Ne.symm slz, Ne.symm slh, Ne.symm slo, bmid, kb su sumid, esu, bz,
          kb h (Ne.symm midh), eh, kb o (Ne.symm mido), eo]
  -- the constants, then the two branches
  refine runs_mono (K := (d * 9 + 4 + 1) + (1 + (1 + (1 + (N * (d * 15 + Kq + 16) + 7)))))
    (runs_seq hvn (fun σ1 hσ1 => ?_)) (le_of_eq (by ring)) (fun _ h => h)
  obtain ⟨e1n, e1ρ, g1⟩ := hσ1
  refine runs_seq (runs_sconst hz 0) (fun σa ea => runs_seq (runs_sconst hh (1 / 2)) (fun σb eb =>
    runs_seq (runs_sconst ho 1) (fun σ2 e2 => ?_)))
  have g2 : G σ2 := by
    rw [e2, eb, ea]; exact hsc _ _ _ (by simp [oS]) (hsc _ _ _ (by simp [oS]) (hsc _ _ _ (by simp [oS]) g1))
  have k2 : ∀ q, q ≠ z → q ≠ h → q ≠ o → σ2.sc q = σ1.sc q := fun q q1 q2 q3 => by
    rw [e2, eb, ea]; simp [q1, q2, q3]
  have e2z : σ2.sc z = 0 := by rw [e2, eb, ea]; simp [zh, zo]
  have e2h : σ2.sc h = 1 / 2 := by rw [e2, eb, ea]; norm_num [ho']
  have e2o : σ2.sc o = 1 := by rw [e2]; simp
  have e2n : σ2.sc nx = nX := by rw [k2 nx nz nh no, e1n]
  have e2ρ : σ2.sc ρ = ρ0 := by rw [k2 ρ hρz hρh hρo, e1ρ]
  by_cases hpos : 0 < nX
  · refine runs_mono (K := (1 + (1 + ((N * (d * 15 + Kq + 13 + 3) + 3) + 1))) + 1)
      (runs_ifS_t hz hnx (by rw [e2z, e2n]; exact hpos) ?_) (le_of_eq (by ring)) (fun _ h => h)
    refine runs_seq (runs_sop2 hsl hnx hρ .div) (fun σ3 e3 => runs_seq (runs_smov hsu hnx) (fun σ4 e4 => ?_))
    have g4 : G σ4 := by rw [e4, e3]; exact hsc _ _ _ (by simp [oS]) (hsc _ _ _ (by simp [oS]) g2)
    have k4 : ∀ q, q ≠ sl → q ≠ su → σ4.sc q = σ2.sc q := fun q q1 q2 => by rw [e4, e3]; simp [q1, q2]
    have e4sl : σ4.sc sl = nX / ρ0 := by rw [e4, e3]; simp [slsu, Op2.eval, e2n, e2ρ]
    have e4su : σ4.sc su = nX := by rw [e4, e3]; simp [nsl, e2n]
    have hJ0 : JG 0 (σ4.setNat jj 0) :=
      ⟨hown σ4 _ g4 (Env.Frame.setNat (Env.Frame.refl _ _ _ _) (by simp [oN]) _), by simpa [bisect] using e4sl,
        by simpa [bisect] using e4su, by simp [k4 z (Ne.symm slz) (Ne.symm suz), e2z],
        by simp [k4 h (Ne.symm slh) (Ne.symm suh), e2h], by simp [k4 o (Ne.symm slo) (Ne.symm suo), e2o]⟩
    refine runs_seq (runs_forN hjj hjv hone hjjjv hjjone N (d * 15 + Kq + 13) JG σ4 g4.2.2.2.2.1 g4.2.2.2.1 hJ0 hbody)
      (fun σ5 h5 => runs_mono (runs_smov hpv hsu) le_rfl (fun σ6 e6 => ?_))
    obtain ⟨⟨g5, -, e5su, -⟩, -⟩ := h5
    have g6 : G σ6 := by rw [e6]; exact hsc _ _ _ (by simp [oS]) g5
    refine ⟨?_, g6.2.2.2.2.2, g6.1⟩
    have hX0 : WithLp.toLp 2 X ≠ 0 := fun h0 => by
      have h0' : ‖WithLp.toLp 2 X‖ = 0 := by rw [h0, norm_zero]
      rw [norm_toLp_eq, ← hnX] at h0'; linarith
    rw [e6]; simp only [Env.setSc_sc, ite_true]; rw [e5su]
    unfold piTilde; simp only [hX0, ite_false]; rw [norm_toLp_eq]
  · refine runs_mono (K := 1 + 2) (runs_ifS_f hz hnx (by rw [e2z, e2n]; exact hpos) (runs_smov hpv hz))
      (by omega) (fun σ6 e6 => ?_)
    have g6 : G σ6 := by rw [e6]; exact hsc _ _ _ (by simp [oS]) g2
    refine ⟨?_, g6.2.2.2.2.2, g6.1⟩
    have hX0 : WithLp.toLp 2 X = 0 := by
      rw [← norm_eq_zero, norm_toLp_eq, ← hnX]; exact le_antisymm (not_lt.mp hpos) (Real.sqrt_nonneg _)
    rw [e6]; simp [e2z, piTilde, hX0]

end AdversarialBco.Poly.Mach.VL
