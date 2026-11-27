/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.XTransO

@[expose] public section

/-!
# The rules of `XRunsBO` (UNI-MACH)

The contract `XRunsBO` of XLangO.lean: a routine of the bit machine's language is a routine of the oracle language
(`XVO.ofX`, so every rule `XV.*` of Bit/Transfer applies under `base`); the control rules (sequence, both
conditionals, both loops, `xforNO`), as `XV.*` of XRuns.lean; the two new leaves on variables (`XVO.orc`: a query at
the point of an array; `XVO.obsR`: a clipped reading into a scalar).
-/

namespace AdversarialBco.Uni

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer

variable {d : ℕ}

namespace XVO

variable {L : Layout} {XO : XCtxO d} {ℓa ℓ : ℕ}

/-! ## Control -/

/-- A routine of the bit machine's language is a routine of the oracle language. -/
theorem ofX {c : XCmd} {σ : Env d} {K : ℕ} {Q : Env d → Prop} (h : XRunsB L XO.X ℓa ℓ c σ K Q) :
    XRunsBO L XO ℓa ℓ (.base c) σ K Q := fun s hs => by
  obtain ⟨k, s', σ', hk, he, hr, hq⟩ := h s hs
  exact ⟨k, s', σ', hk, .base he, hr, hq⟩

theorem mono {c : XCmdO} {σ : Env d} {K K' : ℕ} {Q Q' : Env d → Prop} (h : XRunsBO L XO ℓa ℓ c σ K Q)
    (hK : K ≤ K') (hQ : ∀ σ', Q σ' → Q' σ') : XRunsBO L XO ℓa ℓ c σ K' Q' := fun s hs => by
  obtain ⟨k, s', σ', hk, he, hr, hq⟩ := h s hs
  exact ⟨k, s', σ', hk.trans hK, he, hr, hQ σ' hq⟩

theorem seq {c₁ c₂ : XCmdO} {σ : Env d} {K₁ K₂ : ℕ} {Q₁ Q : Env d → Prop} (h₁ : XRunsBO L XO ℓa ℓ c₁ σ K₁ Q₁)
    (h₂ : ∀ σ₁, Q₁ σ₁ → XRunsBO L XO ℓa ℓ c₂ σ₁ K₂ Q) : XRunsBO L XO ℓa ℓ (.seq c₁ c₂) σ (K₁ + K₂) Q :=
  fun s hs => by
  obtain ⟨k₁, s₁, σ₁, hk₁, he₁, hr₁, hq₁⟩ := h₁ s hs
  obtain ⟨k₂, s₂, σ₂, hk₂, he₂, hr₂, hq₂⟩ := h₂ σ₁ hq₁ s₁ hr₁
  exact ⟨k₁ + k₂, s₂, σ₂, by omega, XExecBO.seq he₁ he₂, hr₂, hq₂⟩

theorem ifS_t {x y : ℕ} {c₁ c₂ : XCmdO} {σ : Env d} {K : ℕ} {Q : Env d → Prop} (hL : LayOK L d ℓa)
    (hx : x < L.NS) (hy : y < L.NS) (hvx : |σ.sc x| < 2 ^ ℓ) (hvy : |σ.sc y| < 2 ^ ℓ) (hc : σ.sc x < σ.sc y)
    (h : XRunsBO L XO ℓa ℓ c₁ σ K Q) : XRunsBO L XO ℓa ℓ (xifSO L x y c₁ c₂) σ (K + 1) Q := fun s hs => by
  obtain ⟨k, s', σ', hk, he, hr, hq⟩ := h s hs
  exact ⟨k + 1, s', σ', by omega,
    XExecBO.ifR_t (VB.testR_of hL hs hx hy hvx hvy) ((VL.condR_iff hs hx hy).2 hc) he, hr, hq⟩

theorem ifS_f {x y : ℕ} {c₁ c₂ : XCmdO} {σ : Env d} {K : ℕ} {Q : Env d → Prop} (hL : LayOK L d ℓa)
    (hx : x < L.NS) (hy : y < L.NS) (hvx : |σ.sc x| < 2 ^ ℓ) (hvy : |σ.sc y| < 2 ^ ℓ) (hc : ¬ σ.sc x < σ.sc y)
    (h : XRunsBO L XO ℓa ℓ c₂ σ K Q) : XRunsBO L XO ℓa ℓ (xifSO L x y c₁ c₂) σ (K + 2) Q := fun s hs => by
  obtain ⟨k, s', σ', hk, he, hr, hq⟩ := h s hs
  exact ⟨k + 2, s', σ', by omega,
    XExecBO.ifR_f (VB.testR_of hL hs hx hy hvx hvy) (fun h' => hc ((VL.condR_iff hs hx hy).1 h')) he, hr, hq⟩

/-- Both branches of a scalar test, each within its own bound. -/
theorem ifS {x y : ℕ} {c₁ c₂ : XCmdO} {σ : Env d} {K : ℕ} {Q : Env d → Prop} (hL : LayOK L d ℓa)
    (hx : x < L.NS) (hy : y < L.NS) (hvx : |σ.sc x| < 2 ^ ℓ) (hvy : |σ.sc y| < 2 ^ ℓ)
    (h₁ : σ.sc x < σ.sc y → XRunsBO L XO ℓa ℓ c₁ σ K Q) (h₂ : ¬ σ.sc x < σ.sc y → XRunsBO L XO ℓa ℓ c₂ σ K Q) :
    XRunsBO L XO ℓa ℓ (xifSO L x y c₁ c₂) σ (K + 2) Q := by
  by_cases hc : σ.sc x < σ.sc y
  · exact mono (ifS_t hL hx hy hvx hvy hc (h₁ hc)) (by omega) fun _ h => h
  · exact ifS_f hL hx hy hvx hvy hc (h₂ hc)

theorem ifN_t {i j : ℕ} {c₁ c₂ : XCmdO} {σ : Env d} {K : ℕ} {Q : Env d → Prop} (hL : LayOK L d ℓa)
    (hi : i < L.NN) (hj : j < L.NN) (hvi : σ.nat i < 2 ^ ℓa) (hvj : σ.nat j < 2 ^ ℓa) (hc : σ.nat i < σ.nat j)
    (h : XRunsBO L XO ℓa ℓ c₁ σ K Q) : XRunsBO L XO ℓa ℓ (.ifN i j c₁ c₂) σ (K + 1) Q := fun s hs => by
  obtain ⟨k, s', σ', hk, he, hr, hq⟩ := h s hs
  exact ⟨k + 1, s', σ', by omega,
    XExecBO.ifN_t (XV.testN_of hL hs hi hj hvi hvj) ((VL.condN_iff hs hi hj).2 hc) he, hr, hq⟩

theorem ifN_f {i j : ℕ} {c₁ c₂ : XCmdO} {σ : Env d} {K : ℕ} {Q : Env d → Prop} (hL : LayOK L d ℓa)
    (hi : i < L.NN) (hj : j < L.NN) (hvi : σ.nat i < 2 ^ ℓa) (hvj : σ.nat j < 2 ^ ℓa) (hc : ¬ σ.nat i < σ.nat j)
    (h : XRunsBO L XO ℓa ℓ c₂ σ K Q) : XRunsBO L XO ℓa ℓ (.ifN i j c₁ c₂) σ (K + 2) Q := fun s hs => by
  obtain ⟨k, s', σ', hk, he, hr, hq⟩ := h s hs
  exact ⟨k + 2, s', σ', by omega,
    XExecBO.ifN_f (XV.testN_of hL hs hi hj hvi hvj) (fun h' => hc ((VL.condN_iff hs hi hj).1 h')) he, hr, hq⟩

/-- Both branches of a natural test, each within its own bound. -/
theorem ifN {i j : ℕ} {c₁ c₂ : XCmdO} {σ : Env d} {K : ℕ} {Q : Env d → Prop} (hL : LayOK L d ℓa)
    (hi : i < L.NN) (hj : j < L.NN) (hvi : σ.nat i < 2 ^ ℓa) (hvj : σ.nat j < 2 ^ ℓa)
    (h₁ : σ.nat i < σ.nat j → XRunsBO L XO ℓa ℓ c₁ σ K Q) (h₂ : ¬ σ.nat i < σ.nat j → XRunsBO L XO ℓa ℓ c₂ σ K Q) :
    XRunsBO L XO ℓa ℓ (.ifN i j c₁ c₂) σ (K + 2) Q := by
  by_cases hc : σ.nat i < σ.nat j
  · exact mono (ifN_t hL hi hj hvi hvj hc (h₁ hc)) (by omega) fun _ h => h
  · exact ifN_f hL hi hj hvi hvj hc (h₂ hc)

/-- A `whileN` loop with an invariant `I t` after `t` turns (which bounds the two compared naturals), at most `N`
turns, each within `Kb` units. -/
theorem whileN {i j : ℕ} {c : XCmdO} (hL : LayOK L d ℓa) (hi : i < L.NN) (hj : j < L.NN) (I : ℕ → Env d → Prop)
    (N Kb : ℕ) (hb : ∀ t σ, I t σ → σ.nat i < 2 ^ ℓa ∧ σ.nat j < 2 ^ ℓa)
    (hlt : ∀ t σ, I t σ → σ.nat i < σ.nat j → t < N)
    (hbody : ∀ t σ, I t σ → σ.nat i < σ.nat j → XRunsBO L XO ℓa ℓ c σ Kb (I (t + 1))) :
    ∀ t σ, I t σ → XRunsBO L XO ℓa ℓ (.whileN i j c) σ ((N - t) * (Kb + 2) + 2)
      (fun σ' => ∃ t', I t' σ' ∧ ¬ σ'.nat i < σ'.nat j) := by
  suffices H : ∀ m t σ, N - t = m → I t σ → XRunsBO L XO ℓa ℓ (.whileN i j c) σ ((N - t) * (Kb + 2) + 2)
      (fun σ' => ∃ t', I t' σ' ∧ ¬ σ'.nat i < σ'.nat j) from fun t σ hI => H _ t σ rfl hI
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro t σ hm hI s hs
    have hT : TestN ℓa s i j := XV.testN_of hL hs hi hj (hb t σ hI).1 (hb t σ hI).2
    by_cases hc : σ.nat i < σ.nat j
    · have htN := hlt t σ hI hc
      obtain ⟨k₁, s₁, σ₁, hk₁, he₁, hr₁, hq₁⟩ := hbody t σ hI hc s hs
      obtain ⟨k₂, s₂, σ₂, hk₂, he₂, hr₂, hq₂⟩ := ih (N - (t + 1)) (by omega) (t + 1) σ₁ rfl hq₁ s₁ hr₁
      refine ⟨k₁ + 2 + k₂, s₂, σ₂, ?_, XExecBO.whileN_t hT ((VL.condN_iff hs hi hj).2 hc) he₁ he₂, hr₂, hq₂⟩
      have e : N - t = (N - (t + 1)) + 1 := by omega
      rw [e, Nat.succ_mul]
      omega
    · exact ⟨2, s, σ, by omega, XExecBO.whileN_f hT (fun h' => hc ((VL.condN_iff hs hi hj).1 h')), hs, t, hI, hc⟩

theorem nconst (hL : LayOK L d ℓa) {σ : Env d} {i : ℕ} (hi : i < L.NN) (c : ℕ) (hc : c < 2 ^ ℓa) :
    XRunsBO L XO ℓa ℓ (.base (.prim (.frag (.nconst i c)))) σ 1 (· = σ.setNat i c) :=
  ofX (XV.nconst hL hi c hc)

theorem nadd (hL : LayOK L d ℓa) {σ : Env d} {i a b : ℕ} (hi : i < L.NN) (ha : a < L.NN) (hb : b < L.NN)
    (hva : σ.nat a < 2 ^ ℓa) (hvb : σ.nat b < 2 ^ ℓa) :
    XRunsBO L XO ℓa ℓ (.base (.prim (.frag (.nadd i a b)))) σ 1 (· = σ.setNat i (σ.nat a + σ.nat b)) :=
  ofX (XV.nadd hL hi ha hb hva hvb)

/-- The rule of `xforNO`, as `XV.forN`. -/
theorem forN (hL : LayOK L d ℓa) {i n one : ℕ} {body : XCmdO} (hi : i < L.NN) (hn : n < L.NN) (ho : one < L.NN)
    (hin : i ≠ n) (hio : i ≠ one) (N Kb : ℕ) (hNb : N < 2 ^ ℓa) (J : ℕ → Env d → Prop) (σ : Env d)
    (hN : σ.nat n = N) (h1 : σ.nat one = 1) (h0 : J 0 (σ.setNat i 0))
    (hbody : ∀ t < N, ∀ σ', J t σ' → σ'.nat i = t → σ'.nat n = N → σ'.nat one = 1 →
      XRunsBO L XO ℓa ℓ body σ' Kb (fun σ'' => σ''.nat i = t ∧ σ''.nat n = N ∧ σ''.nat one = 1 ∧
        J (t + 1) (σ''.setNat i (t + 1)))) :
    XRunsBO L XO ℓa ℓ (xforNO i n one body) σ (N * (Kb + 3) + 3)
      (fun σ' => J N σ' ∧ σ'.nat i = N ∧ σ'.nat n = N ∧ σ'.nat one = 1) := by
  have h1b : 1 < 2 ^ ℓa := by have := hL.1; omega
  let I : ℕ → Env d → Prop := fun t σ' => J t σ' ∧ σ'.nat i = t ∧ σ'.nat n = N ∧ σ'.nat one = 1 ∧ t ≤ N
  have hloop := whileN (L := L) (XO := XO) (ℓ := ℓ) (c := .seq body (.base (.prim (.frag (.nadd i i one))))) hL hi
    hn I N (Kb + 1)
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
  have hs := seq (nconst (L := L) (XO := XO) (ℓ := ℓ) (σ := σ) hL hi 0 (by omega))
    (fun σ1 e => e ▸ hloop 0 (σ.setNat i 0) ⟨h0, by simp, by simp [Ne.symm hin, hN], by simp [Ne.symm hio, h1],
      Nat.zero_le _⟩)
  refine mono hs (by rw [Nat.sub_zero]; ring_nf; omega) (fun σ' h => ?_)
  obtain ⟨t', ⟨hJ, h2, h3, h4, h5⟩, hc⟩ := h
  have : t' = N := by omega
  subst this
  exact ⟨hJ, h2, h3, h4⟩

/-! ## The new leaves on variables -/

/-- The rule of a new leaf from its bound and the representation of its effect. -/
theorem leaf {l : LeafO} {σ σ' : Env d} (h : ∀ s, Rep L σ s → l.OK ℓa ℓ s ∧ Rep L σ' (l.exec XO s)) :
    XRunsBO L XO ℓa ℓ (.leaf l) σ (l.units d) (· = σ') := fun s hs =>
  ⟨_, _, σ', le_rfl, XExecBO.leaf l s (h s hs).1, (h s hs).2, rfl⟩

/-- The query at the point of array `v` (entries `0, ..., d`, below `2^ℓ`) and the precision `nat p ≤ ℓ`: the
answer into the natural `i`. -/
theorem orc (hL : LayOK L d ℓa) (hd : 1 ≤ d) {σ : Env d} {i v p : ℕ} (hi : i < L.NN) (hv : v < L.NA)
    (hp : p < L.NN) (hpℓ : σ.nat p ≤ ℓ) (hpa : σ.nat p < 2 ^ ℓa) (hb : ∀ j ≤ d, |σ.arr v j| < 2 ^ ℓ) :
    XRunsBO L XO ℓa ℓ (xorcO L i v p) σ (d + 3)
      (· = σ.setNat i (if XO.w.orc (ptArr σ v) (σ.nat p) then 1 else 0)) :=
  leaf fun s hs => by
    have hlt : ∀ j ≤ d, j < asz d := fun j hj => by unfold asz; nlinarith
    refine ⟨⟨by have := hL.1; omega, VB.regOK_rA hL hs hv, VB.regOK_nat hL hp (by rw [hs.nat p hp]; exact hpa), ?_,
      fun j hj => ?_, by rw [hs.nat p hp]; exact hpℓ⟩, ?_⟩
    · rw [hs.rA v hv]; exact VB.cell_lt' hL hv (hlt d le_rfl)
    · rw [hs.rA v hv, hs.arr v hv j (hlt j hj)]; exact hb j hj
    · have hpt : ptQ d s.mem (s.nreg (L.rA v)) = ptArr σ v := by
        funext j
        unfold ptQ ptArr
        have e0 : s.mem (L.base d v) = σ.arr v 0 := by simpa using hs.arr v hv 0 (hlt 0 (Nat.zero_le _))
        rw [hs.rA v hv, Nat.add_assoc, hs.arr v hv _ (hlt _ (by have := j.isLt; omega)), e0]
      dsimp only [LeafO.exec]
      rw [hpt, hs.nat p hp]
      exact hs.setNat hi _

/-- The clipped reading into the scalar `x`, at the precision `nat p ≤ ℓ` and the range `nat q < ℓ`. -/
theorem obsR (hL : LayOK L d ℓa) {σ : Env d} {x p q : ℕ} (hx : x < L.NS) (hp : p < L.NN) (hq : q < L.NN)
    (hpℓ : σ.nat p ≤ ℓ) (hqℓ : σ.nat q < ℓ) (hpa : σ.nat p < 2 ^ ℓa) (hqa : σ.nat q < 2 ^ ℓa) :
    XRunsBO L XO ℓa ℓ (xobsRO L x p q) σ 1
      (· = σ.setSc x (BitRAMO.clip (σ.nat q) ⌊(2 : ℝ) ^ (σ.nat p) * fbE XO.X σ⌋ : ℝ)) :=
  leaf fun s hs => by
    refine ⟨⟨VB.regOK_rS hL hs hx, VB.regOK_nat hL hp (by rw [hs.nat p hp]; exact hpa),
      VB.regOK_nat hL hq (by rw [hs.nat q hq]; exact hqa), by rw [hs.nat p hp]; exact hpℓ,
      by rw [hs.nat q hq]; exact hqℓ⟩, ?_⟩
    dsimp only [LeafO.exec]
    rw [hs.rS x hx, hs.nat p hp, hs.nat q hq, XV.fbR_eq hs]
    exact hs.setSc hx _

end XVO

end AdversarialBco.Uni
