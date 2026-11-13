/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XTrans
public import AdversarialBco.Bit.Transfer.RunsB

@[expose] public section

/-!
# The compiler, part 3: the typed-variable rules of the extended language

`XRunsB L X ℓa ℓ c σ K Q` is `RunsB` (RunsB.lean) for `XCmd` and `XExecB`: from every real state representing `σ`
in the layout `L` (`Rep`, Poly/MachVL.lean), the command runs in the bounded semantics within `K` units to a state
representing an environment that satisfies `Q`.

* `RunsB.toX`: a routine of the fragment proved with `RunsB` is a routine of the extended language.
* The control rules: sequence, both conditionals, both loops, `xforN`.
* The leaves on variables: `xsidiv` (Euclidean quotient of two scalars), `xcoins` (a block of coins into a scalar),
  `xobs` (digits of the feedback into a scalar), `xplay` (play the point stored in an array, denominator first),
  `xrtoN` (a scalar to a natural variable), `xnmul` (product of naturals), `xrdIn` (an input cell into a scalar).
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach

variable {d : ℕ}

/-- `RunsB` for the extended language. -/
def XRunsB (L : Layout) (X : XCtx d) (ℓa ℓ : ℕ) (c : XCmd) (σ : Env d) (K : ℕ) (Q : Env d → Prop) : Prop :=
  ∀ s, Rep L σ s → ∃ k s' σ', k ≤ K ∧ XExecB X ℓa ℓ c s k s' ∧ Rep L σ' s' ∧ Q σ'

/-- A routine of the fragment is a routine of the extended language. -/
theorem RunsB.toX {L : Layout} {ℓa ℓ : ℕ} {w : RealRAM.World d} {c : Cmd} {σ : Env d} {K : ℕ}
    {Q : Env d → Prop} (h : RunsB L ℓa ℓ w c σ K Q) (X : XCtx d) : XRunsB L X ℓa ℓ (toX c) σ K Q := fun s hs => by
  obtain ⟨k, s', σ', hk, he, hr, hq⟩ := h s hs
  exact ⟨k, s', σ', hk, he.toX X, hr, hq⟩

/-- `if sc x < sc y then c₁ else c₂`. -/
def xifS (L : Layout) (x y : ℕ) (c₁ c₂ : XCmd) : XCmd := .ifR (L.rS x) (L.rS y) c₁ c₂

/-- `while sc x < sc y do c`. -/
def xwhileS (L : Layout) (x y : ℕ) (c : XCmd) : XCmd := .whileR (L.rS x) (L.rS y) c

/-- `for i < n do body` (`one` holds `1`), as `VL.forN`. -/
def xforN (i n one : ℕ) (body : XCmd) : XCmd :=
  .seq (.prim (.frag (.nconst i 0))) (.whileN i n (.seq body (.prim (.frag (.nadd i i one)))))

/-- `x := ⌊sc a⌋ / ⌊sc b⌋`, the Euclidean quotient. -/
def xsidiv (L : Layout) (x a b : ℕ) : XCmd := .prim (.leaf (.idiv (L.rS x) (L.rS a) (L.rS b)))

/-- `x :=` the integer of the next `nat i` coins. -/
def xcoins (L : Layout) (x i : ℕ) : XCmd := .prim (.leaf (.coins (L.rS x) i))

/-- `x := ⌊2^(nat i) o⌋`, `o` the feedback of the last round played. -/
def xobs (L : Layout) (x i : ℕ) : XCmd := .prim (.leaf (.obs (L.rS x) i))

/-- Play the point `(arr v (1 + j) / arr v 0)_{j < d}`. -/
def xplay (L : Layout) (v : ℕ) : XCmd := .prim (.leaf (.play (L.rA v)))

/-- `nat i := sc x`, for a nonnegative integer `sc x`. -/
def xrtoN (L : Layout) (i x : ℕ) : XCmd := .prim (.leaf (.rtoN i (L.rS x)))

/-- `nat i := nat a * nat b`. -/
def xnmul (i a b : ℕ) : XCmd := .prim (.leaf (.nmul i a b))

/-- `x :=` the input cell `nat i`. -/
def xrdIn (L : Layout) (x i : ℕ) : XCmd := .prim (.leaf (.rdIn (L.rS x) i))

/-- The feedback of the last round played, read on the environment. -/
noncomputable def fbE (X : XCtx d) (σ : Env d) : ℝ :=
  if σ.rounds = 0 then 0 else X.wb.f (σ.rounds - 1) (σ.pts (σ.rounds - 1))

/-- The point stored in array `v`: denominator in entry `0`, numerators in entries `1, ..., d`. -/
noncomputable def ptE (σ : Env d) (v : ℕ) : E d := WithLp.toLp 2 fun j : Fin d => σ.arr v (1 + (j : ℕ)) / σ.arr v 0

namespace XV

variable {L : Layout} {X : XCtx d} {ℓa ℓ : ℕ}

/-! ## Control -/

theorem mono {c : XCmd} {σ : Env d} {K K' : ℕ} {Q Q' : Env d → Prop} (h : XRunsB L X ℓa ℓ c σ K Q)
    (hK : K ≤ K') (hQ : ∀ σ', Q σ' → Q' σ') : XRunsB L X ℓa ℓ c σ K' Q' := fun s hs => by
  obtain ⟨k, s', σ', hk, he, hr, hq⟩ := h s hs
  exact ⟨k, s', σ', hk.trans hK, he, hr, hQ σ' hq⟩

theorem seq {c₁ c₂ : XCmd} {σ : Env d} {K₁ K₂ : ℕ} {Q₁ Q : Env d → Prop} (h₁ : XRunsB L X ℓa ℓ c₁ σ K₁ Q₁)
    (h₂ : ∀ σ₁, Q₁ σ₁ → XRunsB L X ℓa ℓ c₂ σ₁ K₂ Q) : XRunsB L X ℓa ℓ (.seq c₁ c₂) σ (K₁ + K₂) Q := fun s hs => by
  obtain ⟨k₁, s₁, σ₁, hk₁, he₁, hr₁, hq₁⟩ := h₁ s hs
  obtain ⟨k₂, s₂, σ₂, hk₂, he₂, hr₂, hq₂⟩ := h₂ σ₁ hq₁ s₁ hr₁
  exact ⟨k₁ + k₂, s₂, σ₂, by omega, XExecB.seq he₁ he₂, hr₂, hq₂⟩

theorem skip (σ : Env d) : XRunsB L X ℓa ℓ .skip σ 0 (· = σ) := fun s hs => ⟨0, s, σ, le_rfl, .skip s, hs, rfl⟩

theorem ifS_t {x y : ℕ} {c₁ c₂ : XCmd} {σ : Env d} {K : ℕ} {Q : Env d → Prop} (hL : LayOK L d ℓa)
    (hx : x < L.NS) (hy : y < L.NS) (hvx : |σ.sc x| < 2 ^ ℓ) (hvy : |σ.sc y| < 2 ^ ℓ) (hc : σ.sc x < σ.sc y)
    (h : XRunsB L X ℓa ℓ c₁ σ K Q) : XRunsB L X ℓa ℓ (xifS L x y c₁ c₂) σ (K + 1) Q := fun s hs => by
  obtain ⟨k, s', σ', hk, he, hr, hq⟩ := h s hs
  exact ⟨k + 1, s', σ', by omega,
    XExecB.ifR_t (VB.testR_of hL hs hx hy hvx hvy) ((VL.condR_iff hs hx hy).2 hc) he, hr, hq⟩

theorem ifS_f {x y : ℕ} {c₁ c₂ : XCmd} {σ : Env d} {K : ℕ} {Q : Env d → Prop} (hL : LayOK L d ℓa)
    (hx : x < L.NS) (hy : y < L.NS) (hvx : |σ.sc x| < 2 ^ ℓ) (hvy : |σ.sc y| < 2 ^ ℓ) (hc : ¬ σ.sc x < σ.sc y)
    (h : XRunsB L X ℓa ℓ c₂ σ K Q) : XRunsB L X ℓa ℓ (xifS L x y c₁ c₂) σ (K + 2) Q := fun s hs => by
  obtain ⟨k, s', σ', hk, he, hr, hq⟩ := h s hs
  exact ⟨k + 2, s', σ', by omega,
    XExecB.ifR_f (VB.testR_of hL hs hx hy hvx hvy) (fun h' => hc ((VL.condR_iff hs hx hy).1 h')) he, hr, hq⟩

theorem testN_of {σ : Env d} {s : RealRAM.State d} (hL : LayOK L d ℓa) (hs : Rep L σ s) {i j : ℕ} (hi : i < L.NN)
    (hj : j < L.NN) (hvi : σ.nat i < 2 ^ ℓa) (hvj : σ.nat j < 2 ^ ℓa) : TestN ℓa s i j :=
  ⟨VB.regOK_nat hL hi (by rw [hs.nat i hi]; exact hvi), VB.regOK_nat hL hj (by rw [hs.nat j hj]; exact hvj)⟩

theorem ifN_t {i j : ℕ} {c₁ c₂ : XCmd} {σ : Env d} {K : ℕ} {Q : Env d → Prop} (hL : LayOK L d ℓa)
    (hi : i < L.NN) (hj : j < L.NN) (hvi : σ.nat i < 2 ^ ℓa) (hvj : σ.nat j < 2 ^ ℓa) (hc : σ.nat i < σ.nat j)
    (h : XRunsB L X ℓa ℓ c₁ σ K Q) : XRunsB L X ℓa ℓ (.ifN i j c₁ c₂) σ (K + 1) Q := fun s hs => by
  obtain ⟨k, s', σ', hk, he, hr, hq⟩ := h s hs
  exact ⟨k + 1, s', σ', by omega,
    XExecB.ifN_t (testN_of hL hs hi hj hvi hvj) ((VL.condN_iff hs hi hj).2 hc) he, hr, hq⟩

theorem ifN_f {i j : ℕ} {c₁ c₂ : XCmd} {σ : Env d} {K : ℕ} {Q : Env d → Prop} (hL : LayOK L d ℓa)
    (hi : i < L.NN) (hj : j < L.NN) (hvi : σ.nat i < 2 ^ ℓa) (hvj : σ.nat j < 2 ^ ℓa) (hc : ¬ σ.nat i < σ.nat j)
    (h : XRunsB L X ℓa ℓ c₂ σ K Q) : XRunsB L X ℓa ℓ (.ifN i j c₁ c₂) σ (K + 2) Q := fun s hs => by
  obtain ⟨k, s', σ', hk, he, hr, hq⟩ := h s hs
  exact ⟨k + 2, s', σ', by omega,
    XExecB.ifN_f (testN_of hL hs hi hj hvi hvj) (fun h' => hc ((VL.condN_iff hs hi hj).1 h')) he, hr, hq⟩

/-- A `whileN` loop with an invariant `I t` after `t` turns (which bounds the two compared naturals), at most `N`
turns, each within `Kb` units. -/
theorem whileN {i j : ℕ} {c : XCmd} (hL : LayOK L d ℓa) (hi : i < L.NN) (hj : j < L.NN) (I : ℕ → Env d → Prop)
    (N Kb : ℕ) (hb : ∀ t σ, I t σ → σ.nat i < 2 ^ ℓa ∧ σ.nat j < 2 ^ ℓa)
    (hlt : ∀ t σ, I t σ → σ.nat i < σ.nat j → t < N)
    (hbody : ∀ t σ, I t σ → σ.nat i < σ.nat j → XRunsB L X ℓa ℓ c σ Kb (I (t + 1))) :
    ∀ t σ, I t σ → XRunsB L X ℓa ℓ (.whileN i j c) σ ((N - t) * (Kb + 2) + 2)
      (fun σ' => ∃ t', I t' σ' ∧ ¬ σ'.nat i < σ'.nat j) := by
  suffices H : ∀ m t σ, N - t = m → I t σ → XRunsB L X ℓa ℓ (.whileN i j c) σ ((N - t) * (Kb + 2) + 2)
      (fun σ' => ∃ t', I t' σ' ∧ ¬ σ'.nat i < σ'.nat j) from fun t σ hI => H _ t σ rfl hI
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro t σ hm hI s hs
    have hT : TestN ℓa s i j := testN_of hL hs hi hj (hb t σ hI).1 (hb t σ hI).2
    by_cases hc : σ.nat i < σ.nat j
    · have htN := hlt t σ hI hc
      obtain ⟨k₁, s₁, σ₁, hk₁, he₁, hr₁, hq₁⟩ := hbody t σ hI hc s hs
      obtain ⟨k₂, s₂, σ₂, hk₂, he₂, hr₂, hq₂⟩ := ih (N - (t + 1)) (by omega) (t + 1) σ₁ rfl hq₁ s₁ hr₁
      refine ⟨k₁ + 2 + k₂, s₂, σ₂, ?_, XExecB.whileN_t hT ((VL.condN_iff hs hi hj).2 hc) he₁ he₂, hr₂, hq₂⟩
      have e : N - t = (N - (t + 1)) + 1 := by omega
      rw [e, Nat.succ_mul]
      omega
    · exact ⟨2, s, σ, by omega, XExecB.whileN_f hT (fun h' => hc ((VL.condN_iff hs hi hj).1 h')), hs, t, hI, hc⟩

/-- A `whileS` loop with an invariant `I t` after `t` turns (which bounds the two compared scalars), at most `N`
turns, each within `Kb` units. -/
theorem whileS {x y : ℕ} {c : XCmd} (hL : LayOK L d ℓa) (hx : x < L.NS) (hy : y < L.NS) (I : ℕ → Env d → Prop)
    (N Kb : ℕ) (hb : ∀ t σ, I t σ → |σ.sc x| < 2 ^ ℓ ∧ |σ.sc y| < 2 ^ ℓ)
    (hlt : ∀ t σ, I t σ → σ.sc x < σ.sc y → t < N)
    (hbody : ∀ t σ, I t σ → σ.sc x < σ.sc y → XRunsB L X ℓa ℓ c σ Kb (I (t + 1))) :
    ∀ t σ, I t σ → XRunsB L X ℓa ℓ (xwhileS L x y c) σ ((N - t) * (Kb + 2) + 2)
      (fun σ' => ∃ t', I t' σ' ∧ ¬ σ'.sc x < σ'.sc y) := by
  suffices H : ∀ m t σ, N - t = m → I t σ → XRunsB L X ℓa ℓ (xwhileS L x y c) σ ((N - t) * (Kb + 2) + 2)
      (fun σ' => ∃ t', I t' σ' ∧ ¬ σ'.sc x < σ'.sc y) from fun t σ hI => H _ t σ rfl hI
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro t σ hm hI s hs
    have hT : TestR ℓa ℓ s (L.rS x) (L.rS y) := VB.testR_of hL hs hx hy (hb t σ hI).1 (hb t σ hI).2
    by_cases hc : σ.sc x < σ.sc y
    · have htN := hlt t σ hI hc
      obtain ⟨k₁, s₁, σ₁, hk₁, he₁, hr₁, hq₁⟩ := hbody t σ hI hc s hs
      obtain ⟨k₂, s₂, σ₂, hk₂, he₂, hr₂, hq₂⟩ := ih (N - (t + 1)) (by omega) (t + 1) σ₁ rfl hq₁ s₁ hr₁
      refine ⟨k₁ + 2 + k₂, s₂, σ₂, ?_, XExecB.whileR_t hT ((VL.condR_iff hs hx hy).2 hc) he₁ he₂, hr₂, hq₂⟩
      have e : N - t = (N - (t + 1)) + 1 := by omega
      rw [e, Nat.succ_mul]
      omega
    · exact ⟨2, s, σ, by omega, XExecB.whileR_f hT (fun h' => hc ((VL.condR_iff hs hx hy).1 h')), hs, t, hI, hc⟩

theorem nconst (hL : LayOK L d ℓa) {σ : Env d} {i : ℕ} (hi : i < L.NN) (c : ℕ) (hc : c < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (.prim (.frag (.nconst i c))) σ 1 (· = σ.setNat i c) :=
  (VB.runsB_nconst (w := X.rw) (ℓ := ℓ) (σ := σ) hL hi c hc).toX X

theorem nadd (hL : LayOK L d ℓa) {σ : Env d} {i a b : ℕ} (hi : i < L.NN) (ha : a < L.NN) (hb : b < L.NN)
    (hva : σ.nat a < 2 ^ ℓa) (hvb : σ.nat b < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (.prim (.frag (.nadd i a b))) σ 1 (· = σ.setNat i (σ.nat a + σ.nat b)) :=
  (VB.runsB_nadd (w := X.rw) (ℓ := ℓ) (σ := σ) hL hi ha hb hva hvb).toX X

/-- The rule of `xforN`. -/
theorem forN (hL : LayOK L d ℓa) {i n one : ℕ} {body : XCmd} (hi : i < L.NN) (hn : n < L.NN) (ho : one < L.NN)
    (hin : i ≠ n) (hio : i ≠ one) (N Kb : ℕ) (hNb : N < 2 ^ ℓa) (J : ℕ → Env d → Prop) (σ : Env d)
    (hN : σ.nat n = N) (h1 : σ.nat one = 1) (h0 : J 0 (σ.setNat i 0))
    (hbody : ∀ t < N, ∀ σ', J t σ' → σ'.nat i = t → σ'.nat n = N → σ'.nat one = 1 →
      XRunsB L X ℓa ℓ body σ' Kb (fun σ'' => σ''.nat i = t ∧ σ''.nat n = N ∧ σ''.nat one = 1 ∧
        J (t + 1) (σ''.setNat i (t + 1)))) :
    XRunsB L X ℓa ℓ (xforN i n one body) σ (N * (Kb + 3) + 3)
      (fun σ' => J N σ' ∧ σ'.nat i = N ∧ σ'.nat n = N ∧ σ'.nat one = 1) := by
  have h1b : 1 < 2 ^ ℓa := by have := hL.1; omega
  let I : ℕ → Env d → Prop := fun t σ' => J t σ' ∧ σ'.nat i = t ∧ σ'.nat n = N ∧ σ'.nat one = 1 ∧ t ≤ N
  have hloop := whileN (L := L) (X := X) (ℓ := ℓ) (c := .seq body (.prim (.frag (.nadd i i one)))) hL hi hn I N
    (Kb + 1)
    (fun t σ' hI => by obtain ⟨-, h2, h3, -, h5⟩ := hI; omega)
    (fun t σ' hI hc => by obtain ⟨-, h2, h3, -, h5⟩ := hI; omega)
    (fun t σ' hI hc => by
      obtain ⟨hJ, h2, h3, h4, h5⟩ := hI
      have ht : t < N := by omega
      refine seq (hbody t ht σ' hJ h2 h3 h4) (fun σ'' h => ?_)
      obtain ⟨g2, g3, g4, g5⟩ := h
      refine mono (nadd hL hi hi ho (by omega) (by omega)) le_rfl (fun σ3 e => ?_)
      subst e
      rw [g2, g4]
      exact ⟨g5, by simp, by simp [Ne.symm hin, g3], by simp [Ne.symm hio, g4], by omega⟩)
  have hs := seq (nconst (L := L) (X := X) (ℓ := ℓ) (σ := σ) hL hi 0 (by omega))
    (fun σ1 e => e ▸ hloop 0 (σ.setNat i 0) ⟨h0, by simp, by simp [Ne.symm hin, hN], by simp [Ne.symm hio, h1],
      Nat.zero_le _⟩)
  refine mono hs (by rw [Nat.sub_zero]; ring_nf; omega) (fun σ' h => ?_)
  obtain ⟨t', ⟨hJ, h2, h3, h4, h5⟩, hc⟩ := h
  have : t' = N := by omega
  subst this
  exact ⟨hJ, h2, h3, h4⟩

/-! ## The leaves on variables -/

/-- The rule of a leaf from its bound and the representation of its effect. -/
theorem leaf {l : Leaf} {σ σ' : Env d} (h : ∀ s, Rep L σ s → LeafOK X ℓa ℓ s l ∧ Rep L σ' (l.exec X s)) :
    XRunsB L X ℓa ℓ (.prim (.leaf l)) σ (leafUnits d l) (· = σ') := fun s hs =>
  ⟨_, _, σ', le_rfl, XExecB.leaf l s (h s hs).1, (h s hs).2, rfl⟩

theorem rep_draws {σ : Env d} {s : RealRAM.State d} (h : Rep L σ s) (k : ℕ) :
    Rep L { σ with draws := k } { s with draws := k } :=
  ⟨h.nat, h.rZ, h.rS, h.rA, h.sc, h.zero, h.arr, rfl, h.rounds, h.pts⟩

theorem fbR_eq {σ : Env d} {s : RealRAM.State d} (h : Rep L σ s) : fbR X s = fbE X σ := by
  unfold fbR fbE; rw [h.rounds, h.pts]

variable {σ : Env d}

theorem sidiv (hL : LayOK L d ℓa) {x a b : ℕ} (hx : x < L.NS) (ha : a < L.NS) (hb : b < L.NS)
    (hva : |σ.sc a| < 2 ^ ℓ) (hvb : |σ.sc b| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xsidiv L x a b) σ 1 (· = σ.setSc x ((⌊σ.sc a⌋ / ⌊σ.sc b⌋ : ℤ) : ℝ)) :=
  leaf fun s hs => by
    refine ⟨⟨VB.regOK_rS hL hs hx, VB.regOK_rS hL hs ha, VB.regOK_rS hL hs hb, ?_, ?_⟩, ?_⟩
    · rw [hs.rS a ha, hs.sc a ha]; exact hva
    · rw [hs.rS b hb, hs.sc b hb]; exact hvb
    · dsimp only [Leaf.exec]
      rw [hs.rS x hx, hs.rS a ha, hs.rS b hb, hs.sc a ha, hs.sc b hb]
      exact hs.setSc hx _

theorem coins (hL : LayOK L d ℓa) {x i : ℕ} (hx : x < L.NS) (hi : i < L.NN) (hk : σ.nat i ≤ ℓ)
    (hka : σ.nat i < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xcoins L x i) σ 1
      (· = { σ.setSc x (BitRAM.readCoins X.wb.cs σ.draws (σ.nat i) : ℝ) with draws := σ.draws + σ.nat i }) :=
  leaf fun s hs => by
    refine ⟨⟨VB.regOK_rS hL hs hx, VB.regOK_nat hL hi (by rw [hs.nat i hi]; exact hka), by
      rw [hs.nat i hi]; exact hk⟩, ?_⟩
    dsimp only [Leaf.exec]
    rw [hs.rS x hx, hs.nat i hi, hs.draws]
    exact rep_draws (hs.setSc hx _) _

theorem obs (hL : LayOK L d ℓa) {x i : ℕ} (hx : x < L.NS) (hi : i < L.NN) (hp : σ.nat i ≤ ℓ)
    (hpa : σ.nat i < 2 ^ ℓa) (hz : |((⌊(2 : ℝ) ^ (σ.nat i) * fbE X σ⌋ : ℤ) : ℝ)| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xobs L x i) σ 1 (· = σ.setSc x (⌊(2 : ℝ) ^ (σ.nat i) * fbE X σ⌋ : ℝ)) :=
  leaf fun s hs => by
    refine ⟨⟨VB.regOK_rS hL hs hx, VB.regOK_nat hL hi (by rw [hs.nat i hi]; exact hpa), by
      rw [hs.nat i hi]; exact hp, by rw [hs.nat i hi, fbR_eq hs]; exact hz⟩, ?_⟩
    dsimp only [Leaf.exec]
    rw [hs.rS x hx, hs.nat i hi, fbR_eq hs]
    exact hs.setSc hx _

theorem play (hL : LayOK L d ℓa) (hd : 1 ≤ d) {v : ℕ} (hv : v < L.NA) (hb : ∀ j ≤ d, |σ.arr v j| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xplay L v) σ (d + 2)
      (· = { σ with rounds := σ.rounds + 1, pts := Function.update σ.pts σ.rounds (ptE σ v) }) :=
  leaf fun s hs => by
    have hlt : ∀ j ≤ d, j < asz d := fun j hj => by unfold asz; nlinarith
    refine ⟨⟨VB.regOK_rA hL hs hv, ?_, fun j hj => ?_⟩, ?_⟩
    · rw [hs.rA v hv]; exact VB.cell_lt' hL hv (by unfold asz; nlinarith)
    · rw [hs.rA v hv, hs.arr v hv j (hlt j hj)]; exact hb j hj
    · have e0 : s.mem (L.base d v) = σ.arr v 0 := by
        simpa using hs.arr v hv 0 (hlt 0 (Nat.zero_le _))
      have hpt : ptR d s.mem (s.nreg (L.rA v)) = ptE σ v := by
        unfold ptR ptE
        congr 1
        funext j
        rw [hs.rA v hv, Nat.add_assoc, hs.arr v hv _ (hlt _ (by have := j.isLt; omega)), e0]
      dsimp only [Leaf.exec]
      rw [hpt, hs.rounds, hs.pts]
      exact ⟨hs.nat, hs.rZ, hs.rS, hs.rA, hs.sc, hs.zero, hs.arr, hs.draws, rfl, rfl⟩

theorem rtoN (hL : LayOK L d ℓa) {i x : ℕ} (hi : i < L.NN) (hx : x < L.NS) (h0 : 0 ≤ σ.sc x)
    (hva : σ.sc x < 2 ^ ℓa) (hv : |σ.sc x| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xrtoN L i x) σ 1 (· = σ.setNat i (⌊σ.sc x⌋).toNat) :=
  leaf fun s hs => by
    refine ⟨⟨by have := hL.1; omega, VB.regOK_rS hL hs hx, ?_, ?_, ?_⟩, ?_⟩
    · rw [hs.rS x hx, hs.sc x hx]; exact h0
    · rw [hs.rS x hx, hs.sc x hx]; exact hva
    · rw [hs.rS x hx, hs.sc x hx]; exact hv
    · dsimp only [Leaf.exec]
      rw [hs.rS x hx, hs.sc x hx]
      exact hs.setNat hi _

theorem nmul (hL : LayOK L d ℓa) {i a b : ℕ} (hi : i < L.NN) (ha : a < L.NN) (hb : b < L.NN)
    (hva : σ.nat a < 2 ^ ℓa) (hvb : σ.nat b < 2 ^ ℓa) (hab : σ.nat a * σ.nat b < 2 ^ ℓa) :
    XRunsB L X ℓa ℓ (xnmul i a b) σ 1 (· = σ.setNat i (σ.nat a * σ.nat b)) :=
  leaf fun s hs => by
    refine ⟨⟨by have := hL.1; omega, VB.regOK_nat hL ha (by rw [hs.nat a ha]; exact hva),
      VB.regOK_nat hL hb (by rw [hs.nat b hb]; exact hvb), by rw [hs.nat a ha, hs.nat b hb]; exact hab⟩, ?_⟩
    dsimp only [Leaf.exec]
    rw [hs.nat a ha, hs.nat b hb]
    exact hs.setNat hi _

theorem rdIn (hL : LayOK L d ℓa) {x i : ℕ} (hx : x < L.NS) (hi : i < L.NN) (hin : σ.nat i < X.off)
    (hia : σ.nat i < 2 ^ ℓa) (hv : |(X.inp (σ.nat i) : ℝ)| < 2 ^ ℓ) :
    XRunsB L X ℓa ℓ (xrdIn L x i) σ 1 (· = σ.setSc x (X.inp (σ.nat i) : ℝ)) :=
  leaf fun s hs => by
    refine ⟨⟨VB.regOK_rS hL hs hx, VB.regOK_nat hL hi (by rw [hs.nat i hi]; exact hia), by
      rw [hs.nat i hi]; exact hin, by rw [hs.nat i hi]; exact hv⟩, ?_⟩
    dsimp only [Leaf.exec]
    rw [hs.rS x hx, hs.nat i hi]
    exact hs.setSc hx _

end XV

end AdversarialBco.Bit.Transfer
