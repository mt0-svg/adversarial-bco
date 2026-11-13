/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.Trans
public import AdversarialBco.Poly.MachVL

@[expose] public section

/-!
# The integer fragment compiled, part 2: the typed-variable rules with magnitudes

`RunsB L ℓa ℓ w c σ K Q` is `Runs L w c σ K Q` (`Poly/MachVL.lean`) with the bounded fragment run `ExecB ℓa ℓ` in
place of `Exec`. The rules of the primitives on variables are lifted from the proved `Runs` rules (the same commands,
the bounds added as hypotheses on the environment). `LayOK L d ℓa`: every register index and every address of the
layout fits in `ℓa` bits.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco AdversarialBco.Poly.Mach

variable {d : ℕ}

/-- Every register index of the layout and every address of its cells is below `2 ^ ℓa`. -/
def LayOK (L : Layout) (d ℓa : ℕ) : Prop := L.NN + L.NS + L.NA + 8 ≤ 2 ^ ℓa ∧ L.base d L.NA < 2 ^ ℓa

/-- `Runs` with the bounded fragment run. -/
def RunsB (L : Layout) (ℓa ℓ : ℕ) (w : RealRAM.World d) (c : Cmd) (σ : Env d) (K : ℕ) (Q : Env d → Prop) : Prop :=
  ∀ s, Rep L σ s → ∃ k s' σ', k ≤ K ∧ ExecB ℓa ℓ w c s k s' ∧ Rep L σ' s' ∧ Q σ'

namespace VB

variable {L : Layout} {ℓa ℓ : ℕ} {w : RealRAM.World d}

/-! ## Layout facts -/

theorem regOK_nat {s : RealRAM.State d} (hL : LayOK L d ℓa) {i : ℕ} (hi : i < L.NN) (hv : s.nreg i < 2 ^ ℓa) :
    RegOK ℓa s i := ⟨by have := hL.1; omega, hv⟩

theorem adr_rP (hL : LayOK L d ℓa) : L.rP + 4 < 2 ^ ℓa := by
  have := hL.1; unfold Layout.rP; omega

theorem regOK_rZ {σ : Env d} {s : RealRAM.State d} (hL : LayOK L d ℓa) (hs : Rep L σ s) : RegOK ℓa s L.rZ := by
  refine ⟨by have := hL.1; unfold Layout.rZ; omega, ?_⟩
  rw [hs.rZ]; have := hL.2; unfold Layout.base at this; omega

theorem regOK_rS {σ : Env d} {s : RealRAM.State d} (hL : LayOK L d ℓa) (hs : Rep L σ s) {x : ℕ} (hx : x < L.NS) :
    RegOK ℓa s (L.rS x) := by
  refine ⟨by have := hL.1; unfold Layout.rS; omega, ?_⟩
  rw [hs.rS x hx]; have := hL.2; unfold Layout.base at this; omega

theorem regOK_rA {σ : Env d} {s : RealRAM.State d} (hL : LayOK L d ℓa) (hs : Rep L σ s) {a : ℕ} (ha : a < L.NA) :
    RegOK ℓa s (L.rA a) := by
  refine ⟨by have := hL.1; unfold Layout.rA; omega, ?_⟩
  rw [hs.rA a ha]
  have h2 := hL.2
  have : L.base d a ≤ L.base d L.NA := by unfold Layout.base; have := Nat.mul_le_mul_right (asz d) ha.le; omega
  omega

theorem cell_lt' (hL : LayOK L d ℓa) {a k : ℕ} (ha : a < L.NA) (hk : k < asz d) : L.base d a + k < 2 ^ ℓa := by
  unfold Layout.base
  exact cell_lt L.NS L.NA (asz d) a k (2 ^ ℓa) ha hk (by have := hL.2; unfold Layout.base at this; omega)

/-! ## Control -/

theorem testR_of {σ : Env d} {s : RealRAM.State d} (hL : LayOK L d ℓa) (hs : Rep L σ s) {x y : ℕ} (hx : x < L.NS)
    (hy : y < L.NS) (hvx : |σ.sc x| < 2 ^ ℓ) (hvy : |σ.sc y| < 2 ^ ℓ) : TestR ℓa ℓ s (L.rS x) (L.rS y) :=
  ⟨regOK_rS hL hs hx, regOK_rS hL hs hy, by rw [hs.rS x hx, hs.sc x hx]; exact hvx,
    by rw [hs.rS y hy, hs.sc y hy]; exact hvy⟩

/-! ## Primitives, lifted from the `Runs` rules -/

theorem runsB_prim {p : Prim} {σ : Env d} {K : ℕ} {Q : Env d → Prop} (h : Runs L w (.prim p) σ K Q)
    (hok : ∀ s, Rep L σ s → PrimOK ℓa ℓ s p) : RunsB L ℓa ℓ w (.prim p) σ K Q := fun s hs => by
  obtain ⟨k, s', σ', hk, he, hr, hq⟩ := h s hs
  cases he
  exact ⟨1, _, σ', hk, ExecB.prim p s (hok s hs), hr, hq⟩

theorem runsB_prim2 {p₁ p₂ : Prim} {σ : Env d} {K : ℕ} {Q : Env d → Prop}
    (h : Runs L w (.seq (.prim p₁) (.prim p₂)) σ K Q) (hok₁ : ∀ s, Rep L σ s → PrimOK ℓa ℓ s p₁)
    (hok₂ : ∀ s, Rep L σ s → PrimOK ℓa ℓ (p₁.exec w s) p₂) :
    RunsB L ℓa ℓ w (.seq (.prim p₁) (.prim p₂)) σ K Q := fun s hs => by
  obtain ⟨k, s', σ', hk, he, hr, hq⟩ := h s hs
  cases he with
  | seq h₁ h₂ =>
    cases h₁
    cases h₂
    exact ⟨_, _, σ', hk, ExecB.seq (ExecB.prim p₁ s (hok₁ s hs)) (ExecB.prim p₂ _ (hok₂ s hs)), hr, hq⟩

variable {σ : Env d}

theorem runsB_sconst (hL : LayOK L d ℓa) {x : ℕ} (hx : x < L.NS) (q : ℚ) (hq : q.den = 1) (hv : |(q : ℝ)| < 2 ^ ℓ) :
    RunsB L ℓa ℓ w (VL.sconst L x q) σ 1 (· = σ.setSc x q) :=
  runsB_prim (VL.runs_sconst hx q) fun _ hs => ⟨regOK_rS hL hs hx, hq, hv⟩

theorem runsB_sop2 (hL : LayOK L d ℓa) {x a b : ℕ} (hx : x < L.NS) (ha : a < L.NS) (hb : b < L.NS)
    (o : RealRAM.Op2) (ho : o ≠ .div) (hva : |σ.sc a| < 2 ^ ℓ) (hvb : |σ.sc b| < 2 ^ ℓ)
    (hvr : |o.eval (σ.sc a) (σ.sc b)| < 2 ^ ℓ) :
    RunsB L ℓa ℓ w (VL.sop2 L o x a b) σ 1 (· = σ.setSc x (o.eval (σ.sc a) (σ.sc b))) :=
  runsB_prim (VL.runs_sop2 hx ha hb o) fun s hs => by
    refine ⟨ho, regOK_rS hL hs hx, regOK_rS hL hs ha, regOK_rS hL hs hb, ?_, ?_, ?_⟩ <;>
      simp only [hs.rS a ha, hs.rS b hb, hs.sc a ha, hs.sc b hb] <;> assumption

theorem runsB_nconst (hL : LayOK L d ℓa) {i : ℕ} (hi : i < L.NN) (c : ℕ) (hc : c < 2 ^ ℓa) :
    RunsB L ℓa ℓ w (VL.nconst i c) σ 1 (· = σ.setNat i c) :=
  runsB_prim (VL.runs_nconst hi c) fun _ _ => ⟨by have := hL.1; omega, hc⟩

theorem runsB_nadd (hL : LayOK L d ℓa) {i a b : ℕ} (hi : i < L.NN) (ha : a < L.NN) (hb : b < L.NN)
    (hva : σ.nat a < 2 ^ ℓa) (hvb : σ.nat b < 2 ^ ℓa) :
    RunsB L ℓa ℓ w (VL.nadd i a b) σ 1 (· = σ.setNat i (σ.nat a + σ.nat b)) :=
  runsB_prim (VL.runs_nadd hi ha hb) fun _ hs =>
    ⟨by have := hL.1; omega, regOK_nat hL ha (by rw [hs.nat a ha]; exact hva),
      regOK_nat hL hb (by rw [hs.nat b hb]; exact hvb)⟩

theorem runsB_nsub (hL : LayOK L d ℓa) {i a b : ℕ} (hi : i < L.NN) (ha : a < L.NN) (hb : b < L.NN)
    (hva : σ.nat a < 2 ^ ℓa) (hvb : σ.nat b < 2 ^ ℓa) (hba : σ.nat b ≤ σ.nat a) :
    RunsB L ℓa ℓ w (VL.nsub i a b) σ 1 (· = σ.setNat i (σ.nat a - σ.nat b)) :=
  runsB_prim (VL.runs_nsub hi ha hb) fun _ hs =>
    ⟨by have := hL.1; omega, regOK_nat hL ha (by rw [hs.nat a ha]; exact hva),
      regOK_nat hL hb (by rw [hs.nat b hb]; exact hvb), by rw [hs.nat a ha, hs.nat b hb]; exact hba⟩

theorem runsB_aget (hL : LayOK L d ℓa) {x a i : ℕ} (hx : x < L.NS) (ha : a < L.NA) (hi : i < L.NN)
    (hk : σ.nat i < asz d) (hv : |σ.arr a (σ.nat i)| < 2 ^ ℓ) :
    RunsB L ℓa ℓ w (VL.aget L x a i) σ 2 (· = σ.setSc x (σ.arr a (σ.nat i))) := by
  have hiv : σ.nat i < 2 ^ ℓa := by have := cell_lt' hL ha hk; omega
  refine runsB_prim2 (VL.runs_aget hx ha hi hk) (fun s hs => ⟨adr_rP hL, regOK_rA hL hs ha,
    regOK_nat hL hi (by rw [hs.nat i hi]; exact hiv)⟩) (fun s hs => ?_)
  have hrP : L.rZ ≠ L.rP := L.rZ_ne_rP
  have hrS : L.rS x ≠ L.rP := L.rS_ne_rP x
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨(regOK_rS hL hs hx).1, by simpa [Prim.exec, Function.update_of_ne hrS] using (regOK_rS hL hs hx).2⟩
  · exact ⟨adr_rP hL, by
      simpa [Prim.exec, hs.rA a ha, hs.nat i hi] using cell_lt' hL ha hk⟩
  · exact ⟨(regOK_rZ hL hs).1, by simpa [Prim.exec, Function.update_of_ne hrP] using (regOK_rZ hL hs).2⟩
  · simpa [Prim.exec, hs.rA a ha, hs.nat i hi, hs.arr a ha _ hk] using hv
  · simp [Prim.exec, Function.update_of_ne hrP, hs.rZ, hs.zero]
  · simpa [Prim.exec, RealRAM.Op2.eval, Function.update_of_ne hrP, hs.rZ, hs.zero, hs.rA a ha, hs.nat i hi,
      hs.arr a ha _ hk] using hv

theorem runsB_aset (hL : LayOK L d ℓa) {a i x : ℕ} (ha : a < L.NA) (hi : i < L.NN) (hx : x < L.NS)
    (hk : σ.nat i < asz d) (hv : |σ.sc x| < 2 ^ ℓ) :
    RunsB L ℓa ℓ w (VL.aset L a i x) σ 2 (· = σ.setArr a (σ.nat i) (σ.sc x)) := by
  have hiv : σ.nat i < 2 ^ ℓa := by have := cell_lt' hL ha hk; omega
  refine runsB_prim2 (VL.runs_aset ha hi hx hk) (fun s hs => ⟨adr_rP hL, regOK_rA hL hs ha,
    regOK_nat hL hi (by rw [hs.nat i hi]; exact hiv)⟩) (fun s hs => ?_)
  have hrP : L.rZ ≠ L.rP := L.rZ_ne_rP
  have hrS : L.rS x ≠ L.rP := L.rS_ne_rP x
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨adr_rP hL, by simpa [Prim.exec, hs.rA a ha, hs.nat i hi] using cell_lt' hL ha hk⟩
  · exact ⟨(regOK_rS hL hs hx).1, by simpa [Prim.exec, Function.update_of_ne hrS] using (regOK_rS hL hs hx).2⟩
  · exact ⟨(regOK_rZ hL hs).1, by simpa [Prim.exec, Function.update_of_ne hrP] using (regOK_rZ hL hs).2⟩
  · simpa [Prim.exec, Function.update_of_ne hrS, hs.rS x hx, hs.sc x hx] using hv
  · simp [Prim.exec, Function.update_of_ne hrP, hs.rZ, hs.zero]
  · simpa [Prim.exec, RealRAM.Op2.eval, Function.update_of_ne hrP, Function.update_of_ne hrS, hs.rZ, hs.zero,
      hs.rS x hx, hs.sc x hx] using hv

end VB

end AdversarialBco.Bit.Transfer
