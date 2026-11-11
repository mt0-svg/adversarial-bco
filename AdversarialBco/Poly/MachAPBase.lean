/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachAPCode
public import AdversarialBco.Poly.APMath

@[expose] public section

/-!
# The subroutine AP in VL: frames, the gauge value and one value on a line

The layout `APVars.Ok`, the rule `MemRule` of the membership code, the frames `KP` of the pieces, then the rules of
`gvCode` (the gauge value with the stop (c2)) and `ev1Code` (that value at `y + s e_i`). The rule of the whole code,
`runs_apCode`, is in `MachAP.lean`.
-/

namespace AdversarialBco.Poly.AP

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL Matrix

variable {d : ℕ} {L : Layout} {w : World d} {memQ : Cmd} {V : APVars}

/-! ## Layout and frames -/

/-- The natural variables, scalars and arrays that AP writes, besides those of `memQ`. -/
def apN (V : APVars) : List ℕ := List.range' V.nB 16
/-- The scalars that AP writes. -/
def apS (V : APVars) : List ℕ := V.ok :: List.range' V.sB 128
/-- The arrays that AP writes. -/
def apA (V : APVars) : List ℕ := V.out :: V.qv :: List.range' V.aB 14

/-- The layout of AP: the blocks fit, the caller's variables lie outside them, and `memQ` writes none of the variables
that AP reads. -/
structure APVars.Ok (V : APVars) (L : Layout) (nsQ ssQ asQ : List ℕ) : Prop where
  nN : V.nB + 16 ≤ L.NN
  nS : V.sB + 128 ≤ L.NS
  nA : V.aB + 14 ≤ L.NA
  dv : V.dv < L.NN
  one : V.one < L.NN
  dvB : V.dv < V.nB ∨ V.nB + 16 ≤ V.dv
  oneB : V.one < V.nB ∨ V.nB + 16 ≤ V.one
  a0 : V.a0 < L.NA
  a0B : V.a0 < V.aB ∨ V.aB + 14 ≤ V.a0
  P : V.P < L.NA
  PB : V.P < V.aB ∨ V.aB + 14 ≤ V.P
  w : V.w < L.NA
  wB : V.w < V.aB ∨ V.aB + 14 ≤ V.w
  out : V.out < L.NA
  qv : V.qv < L.NA
  qvB : V.qv < V.aB ∨ V.aB + 14 ≤ V.qv
  qva0 : V.qv ≠ V.a0
  qvP : V.qv ≠ V.P
  qvw : V.qv ≠ V.w
  r : V.r < L.NS
  rB : V.r < V.sB ∨ V.sB + 128 ≤ V.r
  R : V.R < L.NS
  RB : V.R < V.sB ∨ V.sB + 128 ≤ V.R
  e : V.e < L.NS
  eB : V.e < V.sB ∨ V.sB + 128 ≤ V.e
  ok : V.ok < L.NS
  qo : V.qo < L.NS
  qoB : V.qo < V.sB ∨ V.sB + 128 ≤ V.qo
  qN : ∀ q ∈ nsQ, q ≠ V.dv ∧ q ≠ V.one ∧ (q < V.nB ∨ V.nB + 16 ≤ q)
  qS : ∀ q ∈ ssQ, q ≠ V.r ∧ q ≠ V.R ∧ q ≠ V.e ∧ (q < V.sB ∨ V.sB + 128 ≤ q)
  qA : ∀ q ∈ asQ, q ≠ V.a0 ∧ q ≠ V.P ∧ q ≠ V.w ∧ (q < V.aB ∨ V.aB + 14 ≤ q)

open Classical in
/-- The rule of the membership code: from any environment with `Iq`, it answers whether the array `qv` is in `Q`,
within `Kq` steps, writes only `nsQ`, `ssQ`, `asQ` and keeps `Iq`. -/
def MemRule (L : Layout) (w : World d) (memQ : Cmd) (V : APVars) (Q : Set (Fin d → ℝ)) (Iq : Env d → Prop)
    (Kq : ℕ) (nsQ ssQ asQ : List ℕ) : Prop :=
  ∀ σ, Iq σ → σ.nat V.dv = d → σ.nat V.one = 1 → Runs L w memQ σ Kq (fun σ' =>
    σ'.sc V.qo = (if σ.vec V.qv ∈ Q then 1 else 0) ∧ Env.Frame σ σ' nsQ ssQ asQ ∧ Iq σ')

/-- `Iq` is kept by every change of AP's own variables. -/
def IqRule (V : APVars) (Iq : Env d → Prop) : Prop :=
  ∀ σ σ', Iq σ → Env.Frame σ σ' (apN V) (apS V) (apA V) → Iq σ'

/-- `Iq` holds and `σ` agrees with `σ₀` outside the lists `ON`, `OS`, `OA` of a piece and those of `memQ`. -/
def KP (Iq : Env d → Prop) (nsQ ssQ asQ ON OS OA : List ℕ) (σ0 σ : Env d) : Prop :=
  Iq σ ∧ Env.Frame σ0 σ (ON ++ nsQ) (OS ++ ssQ) (OA ++ asQ)

/-- An option of reals as a flag (`0` for `none`, `1` for `some`) and a value. -/
def OptRel : Option ℝ → ℝ → ℝ → Prop
  | none, f, _ => f = 0
  | some x, f, v => f = 1 ∧ v = x

section Keep

variable {Iq : Env d → Prop} {nsQ ssQ asQ ON OS OA : List ℕ}

theorem keep_refl {σ : Env d} (h : Iq σ) : KP Iq nsQ ssQ asQ ON OS OA σ σ := ⟨h, Env.Frame.refl _ _ _ _⟩

theorem keep_own (hIq : IqRule V Iq) (hON : ∀ i ∈ ON, i ∈ apN V) (hOS : ∀ i ∈ OS, i ∈ apS V)
    (hOA : ∀ i ∈ OA, i ∈ apA V) {σ0 σa σb : Env d} {ns ss as : List ℕ}
    (h : KP Iq nsQ ssQ asQ ON OS OA σ0 σa) (hf : Env.Frame σa σb ns ss as) (hn : ∀ i ∈ ns, i ∈ ON)
    (hs : ∀ i ∈ ss, i ∈ OS) (ha : ∀ i ∈ as, i ∈ OA) : KP Iq nsQ ssQ asQ ON OS OA σ0 σb :=
  ⟨hIq σa σb h.1 (Env.Frame.mono hf (fun i hi => hON i (hn i hi)) (fun i hi => hOS i (hs i hi))
      (fun i hi => hOA i (ha i hi))),
    Env.Frame.trans h.2 (Env.Frame.mono hf (fun i hi => List.mem_append_left _ (hn i hi))
      (fun i hi => List.mem_append_left _ (hs i hi)) (fun i hi => List.mem_append_left _ (ha i hi)))⟩

theorem keep_mem {σ0 σa σb : Env d} (h : KP Iq nsQ ssQ asQ ON OS OA σ0 σa) (hf : Env.Frame σa σb nsQ ssQ asQ)
    (hI : Iq σb) : KP Iq nsQ ssQ asQ ON OS OA σ0 σb :=
  ⟨hI, Env.Frame.trans h.2 (Env.Frame.mono hf (fun _ hi => List.mem_append_right _ hi)
    (fun _ hi => List.mem_append_right _ hi) (fun _ hi => List.mem_append_right _ hi))⟩

theorem keep_trans {σ0 σa σb : Env d} (h : KP Iq nsQ ssQ asQ ON OS OA σ0 σa)
    (h' : KP Iq nsQ ssQ asQ ON OS OA σa σb) : KP Iq nsQ ssQ asQ ON OS OA σ0 σb :=
  ⟨h'.1, Env.Frame.trans h.2 h'.2⟩

theorem keep_mono {ON' OS' OA' : List ℕ} {σ0 σ : Env d} (h : KP Iq nsQ ssQ asQ ON OS OA σ0 σ)
    (hn : ∀ i ∈ ON, i ∈ ON') (hs : ∀ i ∈ OS, i ∈ OS') (ha : ∀ i ∈ OA, i ∈ OA') :
    KP Iq nsQ ssQ asQ ON' OS' OA' σ0 σ :=
  ⟨h.1, Env.Frame.mono h.2 (fun i hi => by
      rcases List.mem_append.1 hi with h' | h'
      · exact List.mem_append_left _ (hn i h')
      · exact List.mem_append_right _ h')
    (fun i hi => by
      rcases List.mem_append.1 hi with h' | h'
      · exact List.mem_append_left _ (hs i h')
      · exact List.mem_append_right _ h')
    (fun i hi => by
      rcases List.mem_append.1 hi with h' | h'
      · exact List.mem_append_left _ (ha i h')
      · exact List.mem_append_right _ h')⟩

theorem KP.nat {σ0 σ : Env d} (h : KP Iq nsQ ssQ asQ ON OS OA σ0 σ) {i : ℕ} (h1 : i ∉ ON) (h2 : i ∉ nsQ) :
    σ.nat i = σ0.nat i :=
  h.2.1 i (fun h' => (List.mem_append.1 h').elim h1 h2)

theorem KP.sc {σ0 σ : Env d} (h : KP Iq nsQ ssQ asQ ON OS OA σ0 σ) {x : ℕ} (h1 : x ∉ OS) (h2 : x ∉ ssQ) :
    σ.sc x = σ0.sc x :=
  h.2.2.1 x (fun h' => (List.mem_append.1 h').elim h1 h2)

theorem KP.arr {σ0 σ : Env d} (h : KP Iq nsQ ssQ asQ ON OS OA σ0 σ) {a : ℕ} (h1 : a ∉ OA) (h2 : a ∉ asQ) :
    σ.arr a = σ0.arr a :=
  h.2.2.2.1 a (fun h' => (List.mem_append.1 h').elim h1 h2)

theorem KP.vec {σ0 σ : Env d} (h : KP Iq nsQ ssQ asQ ON OS OA σ0 σ) {a : ℕ} (h1 : a ∉ OA) (h2 : a ∉ asQ) :
    σ.vec a = σ0.vec a := by
  funext k; simp only [Env.vec, h.arr h1 h2]

theorem KP.mat {σ0 σ : Env d} (h : KP Iq nsQ ssQ asQ ON OS OA σ0 σ) {a : ℕ} (h1 : a ∉ OA) (h2 : a ∉ asQ) :
    σ.mat a = σ0.mat a := by
  funext k l; simp only [Env.mat, h.arr h1 h2]

end Keep

theorem frame_setSc (σ : Env d) (x : ℕ) (v : ℝ) : Env.Frame σ (σ.setSc x v) [] [x] [] :=
  Env.Frame.setSc (Env.Frame.refl _ _ _ _) (List.mem_singleton_self x) v

theorem frame_setNat (σ : Env d) (i v : ℕ) : Env.Frame σ (σ.setNat i v) [i] [] [] :=
  Env.Frame.setNat (Env.Frame.refl _ _ _ _) (List.mem_singleton_self i) v

/-- Membership of offsets in the lists of a piece. -/
macro "mem_tac" : tactic =>
  `(tactic| (intro i hi; simp only [apN, apS, apA, List.mem_cons, List.mem_append, List.mem_range'_1,
    List.not_mem_nil, or_false] at hi ⊢; all_goals (clear * - hi; omega)))


section Ok

variable {nsQ ssQ asQ : List ℕ}

theorem APVars.Ok.nN_nQ (hp : V.Ok L nsQ ssQ asQ) {i : ℕ} (h1 : V.nB ≤ i) (h2 : i < V.nB + 16) : i ∉ nsQ :=
  fun h => by have := (hp.qN i h).2.2; omega

theorem APVars.Ok.dv_nQ (hp : V.Ok L nsQ ssQ asQ) : V.dv ∉ nsQ := fun h => (hp.qN _ h).1 rfl

theorem APVars.Ok.one_nQ (hp : V.Ok L nsQ ssQ asQ) : V.one ∉ nsQ := fun h => (hp.qN _ h).2.1 rfl

theorem APVars.Ok.sB_sQ (hp : V.Ok L nsQ ssQ asQ) {x : ℕ} (h1 : V.sB ≤ x) (h2 : x < V.sB + 128) : x ∉ ssQ :=
  fun h => by have := (hp.qS x h).2.2.2; omega

theorem APVars.Ok.r_sQ (hp : V.Ok L nsQ ssQ asQ) : V.r ∉ ssQ := fun h => (hp.qS _ h).1 rfl
theorem APVars.Ok.R_sQ (hp : V.Ok L nsQ ssQ asQ) : V.R ∉ ssQ := fun h => (hp.qS _ h).2.1 rfl
theorem APVars.Ok.e_sQ (hp : V.Ok L nsQ ssQ asQ) : V.e ∉ ssQ := fun h => (hp.qS _ h).2.2.1 rfl

theorem APVars.Ok.aB_aQ (hp : V.Ok L nsQ ssQ asQ) {a : ℕ} (h1 : V.aB ≤ a) (h2 : a < V.aB + 14) : a ∉ asQ :=
  fun h => by have := (hp.qA a h).2.2.2; omega

theorem APVars.Ok.a0_aQ (hp : V.Ok L nsQ ssQ asQ) : V.a0 ∉ asQ := fun h => (hp.qA _ h).1 rfl
theorem APVars.Ok.P_aQ (hp : V.Ok L nsQ ssQ asQ) : V.P ∉ asQ := fun h => (hp.qA _ h).2.1 rfl
theorem APVars.Ok.w_aQ (hp : V.Ok L nsQ ssQ asQ) : V.w ∉ asQ := fun h => (hp.qA _ h).2.2.1 rfl

end Ok

set_option hygiene false in
/-- The facts of the layout `hp` in the context, for `omega`. -/
macro "layout_facts" : tactic =>
  `(tactic| (
    have _hnN := hp.nN
    have _hnS := hp.nS
    have _hnA := hp.nA
    have _hdv := hp.dv
    have _hone := hp.one
    have _ha0 := hp.a0
    have _hP := hp.P
    have _hw := hp.w
    have _hout := hp.out
    have _hqv := hp.qv
    have _hr := hp.r
    have _hR := hp.R
    have _he := hp.e
    have _hok := hp.ok
    have _hqo := hp.qo))

set_option hygiene false in
/-- Arithmetic on the layout: `omega` with at most one disjunctive fact of `hp`. -/
macro "lay" : tactic => `(tactic| first
  | omega
  | (have := hp.dvB; omega) | (have := hp.oneB; omega) | (have := hp.a0B; omega) | (have := hp.PB; omega)
  | (have := hp.wB; omega) | (have := hp.qvB; omega) | (have := hp.rB; omega) | (have := hp.RB; omega)
  | (have := hp.eB; omega) | (have := hp.qva0; omega) | (have := hp.qvP; omega) | (have := hp.qvw; omega)
  | (have := hp.qoB; omega))

/-- An offset outside the lists of a piece. -/
macro "nmem_tac" : tactic =>
  `(tactic| (simp only [List.mem_cons, List.mem_append, List.mem_range'_1, List.not_mem_nil, or_false, not_or,
    not_and, not_lt]; (repeat' apply And.intro); all_goals lay))

@[simp] theorem Env.setSc_vec (σ : Env d) (x : ℕ) (v : ℝ) (a : ℕ) : (σ.setSc x v).vec a = σ.vec a := rfl
@[simp] theorem Env.setNat_vec (σ : Env d) (i v a : ℕ) : (σ.setNat i v).vec a = σ.vec a := rfl
@[simp] theorem Env.setSc_mat (σ : Env d) (x : ℕ) (v : ℝ) (a : ℕ) : (σ.setSc x v).mat a = σ.mat a := rfl
@[simp] theorem Env.setNat_mat (σ : Env d) (i v a : ℕ) : (σ.setNat i v).mat a = σ.mat a := rfl

theorem Env.vec_of_arr {σ σ' : Env d} (h : σ'.arr = σ.arr) {a : ℕ} : σ'.vec a = σ.vec a := by
  funext k; simp only [Env.vec, h]

theorem Env.mat_of_arr {σ σ' : Env d} (h : σ'.arr = σ.arr) {a : ℕ} : σ'.mat a = σ.mat a := by
  funext k l; simp only [Env.mat, h]

theorem Env.Frame.vec {σ σ' : Env d} {ns ss as : List ℕ} (h : Env.Frame σ σ' ns ss as) {a : ℕ} (ha : a ∉ as) :
    σ'.vec a = σ.vec a := by
  funext k; simp only [Env.vec, h.2.2.1 a ha]

theorem Env.Frame.mat {σ σ' : Env d} {ns ss as : List ℕ} (h : Env.Frame σ σ' ns ss as) {a : ℕ} (ha : a ∉ as) :
    σ'.mat a = σ.mat a := by
  funext k l; simp only [Env.mat, h.2.2.1 a ha]

/-! ## The gauge value -/

open Classical in
set_option maxHeartbeats 2000000 in
/-- The rule of one halving of the gauge value. -/
theorem runs_gvTurn {Q : Set (Fin d → ℝ)} {Iq : Env d → Prop} {Kq : ℕ} {nsQ ssQ asQ : List ℕ}
    (hp : V.Ok L nsQ ssQ asQ) (hmem : MemRule L w memQ V Q Iq Kq nsQ ssQ asQ) (hIq : IqRule V Iq)
    (σ : Env d) (hI : Iq σ) (hdv : σ.nat V.dv = d) (hone : σ.nat V.one = 1)
    (hz : σ.sc (V.sB + 7) = 0) (hh : σ.sc (V.sB + 10) = 1 / 2) (ho : σ.sc (V.sB + 11) = 1) :
    Runs L w (gvTurn L memQ V) σ (d * 18 + Kq + 13) (fun σ' =>
      (σ'.sc (V.sB + 8), σ'.sc (V.sB + 9)) =
        (if 0 < (σ.sc (V.sB + 8) + σ.sc (V.sB + 9)) / 2 ∧
            σ.vec V.a0 + ((σ.sc (V.sB + 8) + σ.sc (V.sB + 9)) / 2)⁻¹ • σ.vec V.aB ∈ Q
          then (σ.sc (V.sB + 8), (σ.sc (V.sB + 8) + σ.sc (V.sB + 9)) / 2)
          else ((σ.sc (V.sB + 8) + σ.sc (V.sB + 9)) / 2, σ.sc (V.sB + 9))) ∧
      KP Iq nsQ ssQ asQ [V.nB] [V.sB + 8, V.sB + 9, V.sB + 12, V.sB + 13, V.sB + 15, V.sB + 16] [V.qv] σ σ') := by
  layout_facts
  have hON : ∀ i ∈ [V.nB], i ∈ apN V := by mem_tac
  have hOS : ∀ i ∈ [V.sB + 8, V.sB + 9, V.sB + 12, V.sB + 13, V.sB + 15, V.sB + 16], i ∈ apS V := by mem_tac
  have hOA : ∀ i ∈ [V.qv], i ∈ apA V := by mem_tac
  let G : Env d → Prop := KP Iq nsQ ssQ asQ [V.nB] [V.sB + 8, V.sB + 9, V.sB + 12, V.sB + 13, V.sB + 15, V.sB + 16] [V.qv] σ
  have own : ∀ σa (q : ℕ) (v : ℝ), q ∈ [V.sB + 8, V.sB + 9, V.sB + 12, V.sB + 13, V.sB + 15, V.sB + 16] →
      G σa → G (σa.setSc q v) :=
    fun σa q v hq g => keep_own hIq hON hOS hOA g (frame_setSc _ _ _) (by simp) (by simpa using hq) (by simp)
  unfold gvTurn
  refine runs_mono (K := 1 + (1 + (d * 18 + Kq + 11))) ?_ (by lay) (fun _ h => h)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .add) (fun σa ea => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .mul) (fun σb eb => ?_)
  have gb : G σb := by
    rw [eb, ea]; exact own _ _ _ (by simp) (own _ _ _ (by simp) (keep_refl hI))
  have kb : ∀ q, q ≠ V.sB + 12 → σb.sc q = σ.sc q := fun q hq => by rw [eb, ea]; simp [hq]
  have bmid : σb.sc (V.sB + 12) = (σ.sc (V.sB + 8) + σ.sc (V.sB + 9)) / 2 := by
    rw [eb, ea]; simp [Op2.eval, hh]; ring
  have bnat : σb.nat = σ.nat := by rw [eb, ea]; rfl
  have barr : σb.arr = σ.arr := by rw [eb, ea]; rfl
  by_cases hm : 0 < (σ.sc (V.sB + 8) + σ.sc (V.sB + 9)) / 2
  · refine runs_mono (K := (1 + ((d * 7 + 3) + ((d * 11 + 3) + (Kq + 3)))) + 1)
      (runs_ifS_t (by lay) (by lay) (by rw [kb _ (by lay), hz, bmid]; exact hm) ?_) (by lay) (fun _ h => h)
    refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .div) (fun σc ec => ?_)
    have gc : G σc := by rw [ec]; exact own _ _ _ (by simp) gb
    have cinv : σc.sc (V.sB + 13) = ((σ.sc (V.sB + 8) + σ.sc (V.sB + 9)) / 2)⁻¹ := by
      rw [ec]; simp [Op2.eval, kb (V.sB + 11) (by lay), ho, bmid]
    have cnat : σc.nat = σ.nat := by rw [ec]; exact bnat
    have carr : σc.arr = σ.arr := by rw [ec]; exact barr
    have kc : ∀ q, q ≠ V.sB + 12 → q ≠ V.sB + 13 → σc.sc q = σ.sc q := fun q h1 h2 => by
      rw [ec]; simp [h2, kb q h1]
    refine runs_seq (runs_vcopy σc hp.dv hp.one (by lay) hp.qv hp.a0 (by lay) (by lay) (by lay)
      (by rw [cnat]; exact hdv) (by rw [cnat]; exact hone)) (fun σd hd' => ?_)
    obtain ⟨ed, fd, -⟩ := hd'
    have gd := keep_own hIq hON hOS hOA gc fd (by mem_tac) (by mem_tac) (by mem_tac)
    have ddv : σd.nat V.dv = d := by rw [fd.1 V.dv (by nmem_tac), cnat]; exact hdv
    have eone0 : σd.nat V.one = 1 := by rw [fd.1 V.one (by nmem_tac), cnat]; exact hone
    refine runs_seq (runs_vaxpy σd hp.dv hp.one (by lay) hp.qv (by lay) (by lay) (by lay) (by lay)
      (by lay) (by lay) (by lay) (by lay) (by lay) ddv eone0) (fun σe he => ?_)
    obtain ⟨ee, fe, -⟩ := he
    have ge := keep_own hIq hON hOS hOA gd fe (by mem_tac) (by mem_tac) (by mem_tac)
    have edv : σe.nat V.dv = d := by rw [fe.1 V.dv (by nmem_tac)]; exact ddv
    have eone : σe.nat V.one = 1 := by rw [fe.1 V.one (by nmem_tac)]; exact eone0
    have eqv : σe.vec V.qv = σ.vec V.a0 + ((σ.sc (V.sB + 8) + σ.sc (V.sB + 9)) / 2)⁻¹ • σ.vec V.aB := by
      rw [ee, ed, fd.2.1 (V.sB + 13) (by nmem_tac), cinv, Env.Frame.vec fd (a := V.aB) (by nmem_tac)]
      rw [Env.vec_of_arr carr, Env.vec_of_arr carr]
    refine runs_seq (hmem σe ge.1 edv eone) (fun σf hf => ?_)
    obtain ⟨eqo, ff, If⟩ := hf
    have gf := keep_mem ge ff If
    have kf : ∀ q, q ≠ V.sB + 12 → q ≠ V.sB + 13 → q ≠ V.sB + 15 → q ≠ V.sB + 16 → q ∉ ssQ →
        σf.sc q = σ.sc q := fun q h1 h2 h3 h4 h5 => by
      rw [ff.2.1 q h5, fe.2.1 q (by simp [h3, h4]), fd.2.1 q (by simp [h3]), kc q h1 h2]
    have fz : σf.sc (V.sB + 7) = 0 := by
      rw [kf _ (by lay) (by lay) (by lay) (by lay) (hp.sB_sQ (by lay) (by lay)), hz]
    have fmid : σf.sc (V.sB + 12) = (σ.sc (V.sB + 8) + σ.sc (V.sB + 9)) / 2 := by
      rw [ff.2.1 (V.sB + 12) (hp.sB_sQ (by lay) (by lay)), fe.2.1 (V.sB + 12) (by nmem_tac), fd.2.1 (V.sB + 12) (by nmem_tac), ec]
      simp [bmid]
    have flo : σf.sc (V.sB + 8) = σ.sc (V.sB + 8) :=
      kf _ (by lay) (by lay) (by lay) (by lay) (hp.sB_sQ (by lay) (by lay))
    have fhi : σf.sc (V.sB + 9) = σ.sc (V.sB + 9) :=
      kf _ (by lay) (by lay) (by lay) (by lay) (hp.sB_sQ (by lay) (by lay))
    by_cases hq : σe.vec V.qv ∈ Q
    · have hP : 0 < (σ.sc (V.sB + 8) + σ.sc (V.sB + 9)) / 2 ∧
          σ.vec V.a0 + ((σ.sc (V.sB + 8) + σ.sc (V.sB + 9)) / 2)⁻¹ • σ.vec V.aB ∈ Q := ⟨hm, eqv ▸ hq⟩
      refine runs_mono (K := 1 + 1) (runs_ifS_t (by lay) hp.qo (by rw [fz, eqo]; simp [hq])
        (runs_smov (by lay) (by lay))) (by lay) (fun σg eg => ?_)
      rw [eg]
      refine ⟨?_, own _ _ _ (by simp) gf⟩
      simp only [hP]; simp [fmid, flo]
    · have hP : ¬ (0 < (σ.sc (V.sB + 8) + σ.sc (V.sB + 9)) / 2 ∧
          σ.vec V.a0 + ((σ.sc (V.sB + 8) + σ.sc (V.sB + 9)) / 2)⁻¹ • σ.vec V.aB ∈ Q) :=
        fun h' => hq (eqv ▸ h'.2)
      refine runs_mono (K := 1 + 2) (runs_ifS_f (by lay) hp.qo (by rw [fz, eqo]; simp [hq])
        (runs_smov (by lay) (by lay))) (by lay) (fun σg eg => ?_)
      rw [eg]
      refine ⟨?_, own _ _ _ (by simp) gf⟩
      simp only [hP, ite_false]; simp [fmid, fhi]
  · have hP : ¬ (0 < (σ.sc (V.sB + 8) + σ.sc (V.sB + 9)) / 2 ∧
        σ.vec V.a0 + ((σ.sc (V.sB + 8) + σ.sc (V.sB + 9)) / 2)⁻¹ • σ.vec V.aB ∈ Q) := fun h' => hm h'.1
    refine runs_mono (K := 1 + 2) (runs_ifS_f (by lay) (by lay)
      (by rw [kb _ (by lay), hz, bmid]; exact hm) (runs_smov (by lay) (by lay))) (by lay)
      (fun σg eg => ?_)
    rw [eg]
    refine ⟨?_, own _ _ _ (by simp) gb⟩
    simp only [hP, ite_false]; simp [bmid, kb (V.sB + 9) (by lay)]

/-- The step bound of the gauge value with the cap `B`. -/
def kGV (d Kq B : ℕ) : ℕ := B * (d * 18 + Kq + 20) + d * 27 + 37

theorem oNorm_eq_zero_iff {x : Fin d → ℝ} : oNorm x = 0 ↔ x = 0 := by
  have hnn : (0 : ℝ) ≤ x ⬝ᵥ x := by
    unfold dotProduct; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  unfold oNorm; rw [Real.sqrt_eq_zero hnn, dotProduct_self_eq_zero]

set_option maxHeartbeats 2000000 in
open Classical in
/-- The rule of the gauge value: `oGaugeValCap Q a₀ r R B x η` as a flag (`sB + 17`) and a value (`sB + 18`). -/
theorem runs_gvCode {Q : Set (Fin d → ℝ)} {Iq : Env d → Prop} {Kq : ℕ} {nsQ ssQ asQ : List ℕ}
    (hp : V.Ok L nsQ ssQ asQ) (hmem : MemRule L w memQ V Q Iq Kq nsQ ssQ asQ) (hIq : IqRule V Iq)
    {x η : ℕ} (hx : x < L.NA) (_hxB : x ≠ V.aB) (hη : η < L.NS) (hηB : η < V.sB ∨ V.sB + 20 ≤ η)
    (σ : Env d) (hd : σ.nat V.dv = d) (h1 : σ.nat V.one = 1) (hI : Iq σ) :
    Runs L w (gvCode L memQ V x η) σ (kGV d Kq (σ.nat (V.nB + 11)))
      (fun σ' => OptRel (oGaugeValCap Q (σ.vec V.a0) (σ.sc V.r) (σ.sc V.R) (σ.nat (V.nB + 11)) (σ.vec x)
          (σ.sc η)) (σ'.sc (V.sB + 17)) (σ'.sc (V.sB + 18)) ∧
        KP Iq nsQ ssQ asQ (List.range' V.nB 5) (List.range' V.sB 20) [V.aB, V.qv] σ σ') := by
  layout_facts
  have hON : ∀ i ∈ List.range' V.nB 5, i ∈ apN V := by mem_tac
  have hOS : ∀ i ∈ List.range' V.sB 20, i ∈ apS V := by mem_tac
  have hOA : ∀ i ∈ [V.aB, V.qv], i ∈ apA V := by mem_tac
  let G : Env d → Prop := KP Iq nsQ ssQ asQ (List.range' V.nB 5) (List.range' V.sB 20) [V.aB, V.qv] σ
  have own : ∀ σa (q : ℕ) (v : ℝ), V.sB ≤ q → q < V.sB + 20 → G σa → G (σa.setSc q v) :=
    fun σa q v h1 h2 g => keep_own hIq hON hOS hOA g (frame_setSc _ _ _) (by simp)
      (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; simp only [List.mem_range'_1]; omega) (by simp)
  have ownN : ∀ σa (i v : ℕ), V.nB ≤ i → i < V.nB + 5 → G σa → G (σa.setNat i v) :=
    fun σa i v h1 h2 g => keep_own hIq hON hOS hOA g (frame_setNat _ _ _)
      (by intro j hj; simp only [List.mem_singleton] at hj; subst hj; simp only [List.mem_range'_1]; omega)
      (by simp) (by simp)
  have Gdv : ∀ σa, G σa → σa.nat V.dv = d := fun σa g => by
    rw [g.nat (by nmem_tac) hp.dv_nQ]; exact hd
  have Gone : ∀ σa, G σa → σa.nat V.one = 1 := fun σa g => by
    rw [g.nat (by nmem_tac) hp.one_nQ]; exact h1
  have GB : ∀ σa, G σa → σa.nat (V.nB + 11) = σ.nat (V.nB + 11) := fun σa g =>
    g.nat (by nmem_tac) (hp.nN_nQ (by lay) (by lay))
  have Ga0 : ∀ σa, G σa → σa.vec V.a0 = σ.vec V.a0 := fun σa g => g.vec (by nmem_tac) hp.a0_aQ
  have Gr : ∀ σa, G σa → σa.sc V.r = σ.sc V.r := fun σa g => g.sc (by nmem_tac) hp.r_sQ
  have GR : ∀ σa, G σa → σa.sc V.R = σ.sc V.R := fun σa g => g.sc (by nmem_tac) hp.R_sQ
  -- the names of the mathematical objects
  obtain ⟨X, hX⟩ : ∃ X, σ.vec x = X := ⟨_, rfl⟩
  obtain ⟨A0, hA0⟩ : ∃ A0, σ.vec V.a0 = A0 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, σ.nat (V.nB + 11) = B := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, σ.sc V.r = r := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, σ.sc V.R = R := ⟨_, rfl⟩
  obtain ⟨η0, hη0⟩ : ∃ η0, σ.sc η = η0 := ⟨_, rfl⟩
  rw [hX, hA0, hB, hr, hR, hη0]
  rw [hA0] at Ga0; rw [hB] at GB; rw [hr] at Gr; rw [hR] at GR
  unfold gvCode
  refine runs_mono (K := (d * 7 + 3) + (1 + ((d * 11 + 3) + ((d * 9 + 5) + (1 + (1 + (1 + (1 + (1 + (1 + (1 +
    ((1 + (1 + ((B * 4 + 4) + (1 + (1 + (1 + (1 + (1 + ((B * (d * 18 + Kq + 13 + 3) + 3) + 1)))))) + 1))) +
      2)))))))))))) ?_ (le_of_eq (by unfold kGV; ring)) (fun _ h => h)
  -- the difference and its norm
  refine runs_seq (runs_vcopy σ hp.dv hp.one (by lay) (by lay) hx (by lay) (by lay) (by lay) hd h1)
    (fun σ1 hσ1 => ?_)
  obtain ⟨e1, f1, -⟩ := hσ1
  have g1 : G σ1 := keep_own hIq hON hOS hOA (keep_refl hI) f1 (by mem_tac) (by mem_tac) (by mem_tac)
  refine runs_seq (runs_sconst (by lay) (-1)) (fun σ2 e2 => ?_)
  have g2 : G σ2 := by rw [e2]; exact own _ _ _ (by lay) (by lay) g1
  refine runs_seq (runs_vaxpy σ2 hp.dv hp.one (by lay) (by lay) hp.a0 (by lay) (by lay) (by lay) (by lay)
    (by lay) (by lay) (by lay) (by lay) (Gdv _ g2) (Gone _ g2)) (fun σ3 hσ3 => ?_)
  obtain ⟨e3, f3, -⟩ := hσ3
  have g3 : G σ3 := keep_own hIq hON hOS hOA g2 f3 (by mem_tac) (by mem_tac) (by mem_tac)
  have hD : σ3.vec V.aB = X - A0 := by
    rw [e3, e2]
    simp only [Env.setSc_vec, Env.setSc_sc, ite_true, e1, Ga0 _ g1, ← hX]
    push_cast; rw [neg_one_smul, sub_eq_add_neg]
  refine runs_seq (runs_vnorm σ3 hp.dv hp.one (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) (by lay)
    (by lay) (by lay) (by lay) (Gdv _ g3) (Gone _ g3)) (fun σ4 hσ4 => ?_)
  obtain ⟨e4, f4⟩ := hσ4
  have g4 : G σ4 := keep_own hIq hON hOS hOA g3 f4 (by mem_tac) (by mem_tac) (by mem_tac)
  have hnx : σ4.sc (V.sB + 1) = oNorm (X - A0) := by rw [e4, hD]; rfl
  have hη4 : σ4.sc η = η0 := by
    rw [f4.2.1 η (by nmem_tac), f3.2.1 η (by nmem_tac), e2, Env.setSc_sc, ite_eq_right (by lay),
      f1.2.1 η (by nmem_tac), hη0]
  have hD4 : σ4.vec V.aB = X - A0 := by rw [Env.Frame.vec f4 (by simp)]; exact hD
  -- the exponent and the cap
  refine runs_seq (runs_sop2 (by lay) hp.r hη .mul) (fun σ5 e5 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .div) (fun σ6 e6 => ?_)
  refine runs_seq (runs_sop1 (by lay) (by lay) .log) (fun σ7 e7 => ?_)
  refine runs_seq (runs_sconst (by lay) 2) (fun σ8 e8 => ?_)
  refine runs_seq (runs_sop1 (by lay) (by lay) .log) (fun σ9 e9 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .div) (fun σ10 e10 => ?_)
  refine runs_seq (runs_ncast (by lay) (by lay)) (fun σ11 e11 => ?_)
  have g11 : G σ11 := by
    rw [e11, e10, e9, e8, e7, e6, e5]
    exact own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay)
      (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay)
      (own _ _ _ (by lay) (by lay) g4))))))
  have v11 : σ11.sc (V.sB + 5) = Real.logb 2 (oNorm (X - A0) / (r * η0)) := by
    rw [e11, e10, e9, e8, e7, e6, e5]
    simp [Op2.eval, Op1.eval, Real.logb, hnx, hη4, Gr _ g4]
  have b11 : σ11.sc (V.sB + 6) = (B : ℝ) := by
    rw [e11]; simp [e10, e9, e8, e7, e6, e5, GB _ g4]
  have n11 : σ11.sc (V.sB + 1) = oNorm (X - A0) := by
    rw [e11, e10, e9, e8, e7, e6, e5]; simp [hnx]
  have t11 : σ11.sc (V.sB + 3) = 2 := by
    rw [e11, e10, e9, e8, e7, e6, e5]; simp
  have D11 : σ11.vec V.aB = X - A0 := by
    rw [e11, e10, e9, e8, e7, e6, e5]; simp [hD4]
  have nat11 : σ11.nat = σ4.nat := by rw [e11, e10, e9, e8, e7, e6, e5]; rfl
  by_cases hcap : (B : ℝ) < Real.logb 2 (oNorm (X - A0) / (r * η0))
  · -- the stop (c2)
    have hnone : oGaugeValCap Q A0 r R B X η0 = none := by
      unfold oGaugeValCap oValSteps; rw [ite_eq_left (Nat.lt_ceil.2 hcap)]
    refine runs_mono (runs_ifS_t (by lay) (by lay) (by rw [b11, v11]; exact hcap)
      (runs_sconst (σ := σ11) (by lay) 0)) (by omega) (fun σ' e' => ?_)
    rw [e', hnone]
    exact ⟨by simp [OptRel], own _ _ _ (by lay) (by lay) g11⟩
  · have hsteps : oValSteps A0 r X η0 ≤ B := Nat.ceil_le.2 (not_lt.1 hcap)
    refine runs_ifS_f (by lay) (by lay) (by rw [b11, v11]; exact hcap) ?_
    refine runs_seq (runs_sconst (by lay) 1) (fun σ12 e12 => ?_)
    refine runs_seq (runs_sconst (by lay) 0) (fun σ13 e13 => ?_)
    have g13 : G σ13 := by rw [e13, e12]; exact own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) g11)
    have k13 : ∀ q, q ≠ V.sB + 7 → q ≠ V.sB + 17 → σ13.sc q = σ11.sc q := fun q h1 h2 => by
      rw [e13, e12]; simp [h1, h2]
    have z13 : σ13.sc (V.sB + 7) = 0 := by rw [e13]; simp
    have ok13 : σ13.sc (V.sB + 17) = 1 := by rw [e13, e12]; simp
    have nat13 : σ13.nat = σ4.nat := by rw [e13, e12]; exact nat11
    have D13 : σ13.vec V.aB = X - A0 := by rw [e13, e12]; simp [D11]
    by_cases hpos : 0 < oNorm (X - A0)
    · have hXA : X ≠ A0 := fun h => by rw [h, sub_self] at hpos; simp [oNorm] at hpos
      refine runs_mono (runs_ifS_t (by lay) (by lay) (by rw [z13, k13 (V.sB + 1) (by lay) (by lay), n11]; exact hpos) ?_)
        le_rfl (fun _ h => h)
      -- the number of steps
      have hS13 : ⌈σ13.sc (V.sB + 5)⌉₊ = oValSteps A0 r X η0 := by
        rw [k13 (V.sB + 5) (by lay) (by lay), v11]; rfl
      refine runs_mono (K := (oValSteps A0 r X η0 * 4 + 4) + (1 + (1 + (1 + (1 + (1 +
        ((oValSteps A0 r X η0 * (d * 18 + Kq + 13 + 3) + 3) + 1)))))))
        ?_ (by have := Nat.mul_le_mul_right (d * 18 + Kq + 13 + 3) hsteps; omega) (fun _ h => h)
      refine runs_seq (runs_mono (runs_nceil σ13 (by lay) (by lay) (by lay) (by lay) (by lay) (by lay)
        (by rw [nat13]; exact Gone _ g4)) (by rw [hS13]) (fun σ' h => h)) (fun σ14 e14 => ?_)
      have g14 : G σ14 := by
        rw [e14]; exact own _ _ _ (by lay) (by lay) (ownN _ _ _ (by lay) (by lay) g13)
      have s14 : σ14.nat (V.nB + 4) = oValSteps A0 r X η0 := by rw [e14]; simp [hS13]
      have n14 : σ14.sc (V.sB + 1) = oNorm (X - A0) := by
        rw [e14]; simp [k13 (V.sB + 1) (by lay) (by lay), n11]
      have t14 : σ14.sc (V.sB + 3) = 2 := by
        rw [e14]; simp [k13 (V.sB + 3) (by lay) (by lay), t11]
      have z14 : σ14.sc (V.sB + 7) = 0 := by rw [e14]; simp [z13]
      have ok14 : σ14.sc (V.sB + 17) = 1 := by rw [e14]; simp [ok13]
      have D14 : σ14.vec V.aB = X - A0 := by rw [e14]; simp [D13]
      refine runs_seq (runs_sop2 (by lay) (by lay) hp.R .mul) (fun σ15 e15 => ?_)
      refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .div) (fun σ16 e16 => ?_)
      have g16 : G σ16 := by
        rw [e16, e15]; exact own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) g14)
      have lo16 : σ16.sc (V.sB + 8) = oNorm (X - A0) / (2 * R) := by
        rw [e16, e15]; simp [Op2.eval, n14, t14, GR _ g14]
      have n16 : σ16.sc (V.sB + 1) = oNorm (X - A0) := by rw [e16, e15]; simp [n14]
      refine runs_seq (runs_sop2 (by lay) (by lay) hp.r .div) (fun σ17 e17 => ?_)
      have hi17 : σ17.sc (V.sB + 9) = oNorm (X - A0) / r := by
        rw [e17]; simp [Op2.eval, n16, Gr _ g16]
      have lo17 : σ17.sc (V.sB + 8) = oNorm (X - A0) / (2 * R) := by rw [e17]; simp [lo16]
      refine runs_seq (runs_sconst (by lay) (1 / 2)) (fun σ18 e18 => ?_)
      refine runs_seq (runs_sconst (by lay) 1) (fun σ19 e19 => ?_)
      have g19 : G σ19 := by
        rw [e19, e18, e17]
        exact own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) (own _ _ _ (by lay) (by lay) g16))
      have k19 : ∀ q, q ≠ V.sB + 2 → q ≠ V.sB + 8 → q ≠ V.sB + 9 → q ≠ V.sB + 10 → q ≠ V.sB + 11 →
          σ19.sc q = σ14.sc q := fun q h1 h2 h3 h4 h5 => by
        rw [e19, e18, e17, e16, e15]; simp [h1, h2, h3, h4, h5]
      have lo19 : σ19.sc (V.sB + 8) = oNorm (X - A0) / (2 * R) := by rw [e19, e18]; simp [lo17]
      have hi19 : σ19.sc (V.sB + 9) = oNorm (X - A0) / r := by rw [e19, e18]; simp [hi17]
      have D19 : σ19.vec V.aB = X - A0 := by rw [e19, e18, e17, e16, e15]; simp [D14]
      -- the bisection
      let Pr : ℝ → Prop := fun t => 0 < t ∧ A0 + t⁻¹ • (X - A0) ∈ Q
      let JG : ℕ → Env d → Prop := fun t σ' => G σ' ∧
        (σ'.sc (V.sB + 8), σ'.sc (V.sB + 9)) = oBisect Pr (oNorm (X - A0) / (2 * R)) (oNorm (X - A0) / r) t ∧
        σ'.vec V.aB = X - A0 ∧
        σ'.sc (V.sB + 7) = 0 ∧ σ'.sc (V.sB + 10) = 1 / 2 ∧ σ'.sc (V.sB + 11) = 1 ∧ σ'.sc (V.sB + 17) = 1
      have hJ0 : JG 0 (σ19.setNat (V.nB + 3) 0) := by
        refine ⟨ownN _ _ _ (by lay) (by lay) g19, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [oBisect, lo19, hi19]
        · simp [D19]
        · simp only [Env.setNat_sc]; rw [k19 (V.sB + 7) (by lay) (by lay) (by lay) (by lay) (by lay)]; exact z14
        · rw [e19, e18]; simp
        · rw [e19]; simp
        · simp only [Env.setNat_sc]; rw [k19 (V.sB + 17) (by lay) (by lay) (by lay) (by lay) (by lay)]; exact ok14
      refine runs_seq (runs_forN (by lay) (by lay) hp.one (by lay) (by lay) (oValSteps A0 r X η0)
        (d * 18 + Kq + 13) JG σ19 (by rw [e19, e18, e17, e16, e15]; exact s14) (Gone _ g19) hJ0 ?_)
        (fun σ20 h20 => ?_)
      · intro t _ σ' hJ hit hNt h1t
        obtain ⟨g', hB', eD, ez, eh, eo, eok⟩ := hJ
        obtain ⟨a, b, hab⟩ : ∃ a b, oBisect Pr (oNorm (X - A0) / (2 * R)) (oNorm (X - A0) / r) t = (a, b) :=
          ⟨_, _, rfl⟩
        rw [hab, Prod.mk.injEq] at hB'
        refine runs_mono (runs_gvTurn hp hmem hIq σ' g'.1 (Gdv _ g') (Gone _ g') ez eh eo) le_rfl
          (fun σ'' h => ?_)
        obtain ⟨hpair, k''⟩ := h
        have g'' : G σ'' := keep_trans g' (keep_mono k'' (by mem_tac) (by mem_tac) (by mem_tac))
        have kk : ∀ q, q ∉ [V.sB + 8, V.sB + 9, V.sB + 12, V.sB + 13, V.sB + 15, V.sB + 16] → q ∉ ssQ →
            σ''.sc q = σ'.sc q := fun q h1 h2 => k''.sc h1 h2
        refine ⟨by rw [k''.nat (by nmem_tac) (hp.nN_nQ (by lay) (by lay))]; exact hit,
          by rw [k''.nat (by nmem_tac) (hp.nN_nQ (by lay) (by lay))]; exact hNt,
          by rw [k''.nat (by nmem_tac) hp.one_nQ]; exact h1t,
          ownN _ _ _ (by lay) (by lay) g'', ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [Env.setNat_sc]
          rw [hpair, hB'.1, hB'.2, Ga0 _ g', eD]
          simp only [oBisect, hab, Pr]
        · simp only [Env.setNat_vec]
          rw [k''.vec (a := V.aB) (by nmem_tac) (hp.aB_aQ (by lay) (by lay))]; exact eD
        · simp only [Env.setNat_sc]; rw [kk (V.sB + 7) (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact ez
        · simp only [Env.setNat_sc]; rw [kk (V.sB + 10) (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact eh
        · simp only [Env.setNat_sc]; rw [kk (V.sB + 11) (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact eo
        · simp only [Env.setNat_sc]; rw [kk (V.sB + 17) (by nmem_tac) (hp.sB_sQ (by lay) (by lay))]; exact eok
      · obtain ⟨⟨g20, hB20, -, -, -, -, eok20⟩, -⟩ := h20
        refine runs_mono (runs_smov (by lay) (by lay)) le_rfl (fun σ21 e21 => ?_)
        have hval : oGaugeValCap Q A0 r R B X η0 =
            some (oBisect Pr (oNorm (X - A0) / (2 * R)) (oNorm (X - A0) / r) (oValSteps A0 r X η0)).2 := by
          unfold oGaugeValCap oGaugeVal; rw [ite_eq_right (not_lt.2 hsteps), ite_eq_right hXA]
        rw [e21, hval]
        refine ⟨⟨by simp [eok20], ?_⟩, own _ _ _ (by lay) (by lay) g20⟩
        simp only [Env.setSc_sc, ite_true]
        exact congrArg Prod.snd hB20
    · have hXA : X = A0 := by
        have h0 : oNorm (X - A0) = 0 := le_antisymm (not_lt.1 hpos) (Real.sqrt_nonneg _)
        exact sub_eq_zero.1 (oNorm_eq_zero_iff.1 h0)
      refine runs_mono (runs_ifS_f (by lay) (by lay)
        (by rw [z13, k13 (V.sB + 1) (by lay) (by lay), n11]; exact hpos) (runs_smov (by lay) (by lay)))
        (by omega) (fun σ21 e21 => ?_)
      have hval : oGaugeValCap Q A0 r R B X η0 = some 0 := by
        unfold oGaugeValCap oGaugeVal; rw [ite_eq_right (not_lt.2 hsteps), ite_eq_left hXA]
      rw [e21, hval]
      refine ⟨⟨by simp [ok13], ?_⟩, own _ _ _ (by lay) (by lay) g13⟩
      simp [z13]

/-! ## One value on a coordinate line -/

theorem Env.setArr_vec_self (σ : Env d) (a : ℕ) (i : Fin d) (v : ℝ) :
    (σ.setArr a i v).vec a = Function.update (σ.vec a) i v := by
  funext j
  simp only [Env.vec, Env.setArr_arr, true_and, Function.update_apply, Fin.val_inj]

theorem Env.setArr_vec_ne (σ : Env d) {a b : ℕ} (h : b ≠ a) (k : ℕ) (v : ℝ) : (σ.setArr a k v).vec b = σ.vec b := by
  funext j; simp [Env.vec, h]

theorem frame_setArr (σ : Env d) (a k : ℕ) (v : ℝ) : Env.Frame σ (σ.setArr a k v) [] [] [a] :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun b hb => by
    funext j; simp only [List.mem_singleton] at hb; simp [hb], rfl, rfl, rfl⟩

/-- The step bound of one value on a coordinate line. -/
def kEV (d Kq B : ℕ) : ℕ := kGV d Kq B + d * 7 + 8

set_option maxHeartbeats 1000000 in
open Classical in
/-- The rule of `ev1Code`: the gauge value at `y + s e_i` (`y` the array `aB + 2`, `i` the natural variable `idx`). -/
theorem runs_ev1Code {Q : Set (Fin d → ℝ)} {Iq : Env d → Prop} {Kq : ℕ} {nsQ ssQ asQ : List ℕ}
    (hp : V.Ok L nsQ ssQ asQ) (hmem : MemRule L w memQ V Q Iq Kq nsQ ssQ asQ) (hIq : IqRule V Iq)
    {idx s η : ℕ} (hidx : V.nB + 5 ≤ idx ∧ idx < V.nB + 16) (hs : V.sB + 21 ≤ s ∧ s < V.sB + 128)
    (hη : V.sB + 21 ≤ η ∧ η < V.sB + 128)
    (σ : Env d) (hd : σ.nat V.dv = d) (h1 : σ.nat V.one = 1) (hI : Iq σ) (i : Fin d) (hi : σ.nat idx = i) :
    Runs L w (ev1Code L memQ V idx s η) σ (kEV d Kq (σ.nat (V.nB + 11)))
      (fun σ' => OptRel (oGaugeValCap Q (σ.vec V.a0) (σ.sc V.r) (σ.sc V.R) (σ.nat (V.nB + 11))
          (σ.vec (V.aB + 2) + σ.sc s • oUnit i) (σ.sc η)) (σ'.sc (V.sB + 17)) (σ'.sc (V.sB + 18)) ∧
        KP Iq nsQ ssQ asQ (List.range' V.nB 5) (List.range' V.sB 21) [V.aB, V.aB + 1, V.qv] σ σ') := by
  layout_facts
  have hON : ∀ i ∈ List.range' V.nB 5, i ∈ apN V := by mem_tac
  have hOS : ∀ i ∈ List.range' V.sB 21, i ∈ apS V := by mem_tac
  have hOA : ∀ i ∈ [V.aB, V.aB + 1, V.qv], i ∈ apA V := by mem_tac
  let G : Env d → Prop := KP Iq nsQ ssQ asQ (List.range' V.nB 5) (List.range' V.sB 21) [V.aB, V.aB + 1, V.qv] σ
  obtain ⟨B, hB⟩ : ∃ B, σ.nat (V.nB + 11) = B := ⟨_, rfl⟩
  rw [hB]
  unfold ev1Code
  refine runs_mono (K := (d * 7 + 3) + (2 + (1 + (2 + kGV d Kq B)))) ?_ (by unfold kEV; omega) (fun _ h => h)
  refine runs_seq (runs_vcopy σ hp.dv hp.one (by lay) (by lay) (by lay) (by lay) (by lay) (by lay) hd h1)
    (fun σ1 hσ1 => ?_)
  obtain ⟨e1, f1, -⟩ := hσ1
  have g1 : G σ1 := keep_own hIq hON hOS hOA (keep_refl hI) f1 (by mem_tac) (by mem_tac) (by mem_tac)
  have n1 : σ1.nat idx = i := by rw [f1.1 idx (by nmem_tac)]; exact hi
  have hk1 : σ1.nat idx < asz d := by rw [n1]; exact lt_asz i.2
  refine runs_seq (runs_aget (by lay) (by lay) (by lay) hk1) (fun σ2 e2 => ?_)
  refine runs_seq (runs_sop2 (by lay) (by lay) (by lay) .add) (fun σ3 e3 => ?_)
  have n3 : σ3.nat idx = i := by rw [e3, e2]; exact n1
  refine runs_seq (runs_aset (by lay) (by lay) (by lay) (by rw [n3]; exact lt_asz i.2)) (fun σ4 e4 => ?_)
  have g4 : G σ4 := by
    rw [e4, e3, e2]
    refine keep_own hIq hON hOS hOA ?_ (frame_setArr _ _ _ _) (by simp) (by simp) (by mem_tac)
    refine keep_own hIq hON hOS hOA ?_ (frame_setSc _ _ _) (by simp) (by mem_tac) (by simp)
    exact keep_own hIq hON hOS hOA g1 (frame_setSc _ _ _) (by simp) (by mem_tac) (by simp)
  have hv4 : σ4.vec (V.aB + 1) = σ.vec (V.aB + 2) + σ.sc s • oUnit i := by
    rw [e4, n3, Env.setArr_vec_self, ← update_add_eq_oUnit]
    have hy : σ3.vec (V.aB + 1) = σ.vec (V.aB + 2) := by rw [e3, e2]; exact e1
    have hs3 : σ1.sc s = σ.sc s := by rw [f1.2.1 s (by nmem_tac)]
    rw [hy, e3, e2]
    simp only [Env.setSc_sc, ite_true, Op2.eval, n1]
    rw [ite_eq_right (by lay), hs3]
    congr 1
    rw [← e1]; rfl
  refine runs_mono (runs_gvCode hp hmem hIq (x := V.aB + 1) (η := η) (by lay) (by lay) (by lay) (by lay) σ4
    (by rw [g4.nat (by nmem_tac) hp.dv_nQ]; exact hd) (by rw [g4.nat (by nmem_tac) hp.one_nQ]; exact h1) g4.1)
    (by rw [g4.nat (by nmem_tac) (hp.nN_nQ (by lay) (by lay)), hB]) (fun σ' h => ?_)
  obtain ⟨hrel, k'⟩ := h
  refine ⟨?_, keep_trans g4 (keep_mono k' (by mem_tac) (by mem_tac) (by mem_tac))⟩
  rw [g4.vec (a := V.a0) (by nmem_tac) hp.a0_aQ, g4.sc (x := V.r) (by nmem_tac) hp.r_sQ,
    g4.sc (x := V.R) (by nmem_tac) hp.R_sQ, g4.nat (by nmem_tac) (hp.nN_nQ (by lay) (by lay)), hv4,
    g4.sc (x := η) (by nmem_tac) (hp.sB_sQ (by lay) (by lay)), hB] at hrel
  exact hrel
