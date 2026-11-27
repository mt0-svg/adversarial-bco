/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.XLangO

@[expose] public section

/-!
# The transfer of the oracle language to the oracle machine (UNI-MACH)

`xtransferO`: a bounded run `XExecBO XO ℓa ℓ c s k s'` and a state `t` of the oracle machine that simulates `s`
(`XSim` of Bit/Transfer/XTrans.lean, in the bit context `XO.X`) give a run of the code `xtrO c o` on `runO` within
`7 k` steps, at cost at most `k * xstepCost ℓa ℓ`, to a state simulating `s'`, when the code sits at `o` in the
program and is followed by at least one instruction.

A base block is run by `xtransfer` on the lowered program `lowerP P` and lifted by `uni_liftO` (LeafFrozen.lean): its
lowered run ends inside the program, so it made no query and no clipped reading. The tests and jumps of the control
are lifted the same way; the two new leaves step `stepO` directly (`xsimO_orc`, `xsimO_obsR`).
-/

namespace AdversarialBco.Uni

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer Function

variable {d : ℕ}

/-! ## The bit context of an oracle context -/

@[simp] theorem XCtxO.X_off (XO : XCtxO d) : XO.X.off = XO.off := rfl

/-! ## Runs of the oracle machine -/

theorem runO_add (P : List BitRAMO.InstrO) (w : BitRAMO.WorldO d) (s : BitRAM.State d) (k j : ℕ) :
    BitRAMO.runO P w s (k + j) = BitRAMO.runO P w (BitRAMO.runO P w s k) j := by
  simp only [BitRAMO.runO]; rw [add_comm, Function.iterate_add_apply]

theorem runO_one (P : List BitRAMO.InstrO) (w : BitRAMO.WorldO d) (s : BitRAM.State d) :
    BitRAMO.runO P w s 1 = BitRAMO.stepO P w s := rfl

/-- The lowered program at a base instruction. -/
theorem lowerP_get {P : List BitRAMO.InstrO} {q : ℕ} {i : BitRAM.Instr} (h : P[q]? = some (.base i)) :
    (BitRAMO.lowerP P)[q]? = some i := by
  simp [BitRAMO.lowerP, List.getElem?_map, h, BitRAMO.lowerI]

/-- At a base instruction the oracle machine steps as the bit machine on the lowered program. -/
theorem stepO_base {P : List BitRAMO.InstrO} {w : BitRAMO.WorldO d} {t : BitRAM.State d} {i : BitRAM.Instr}
    (h : P[t.pc]? = some (.base i)) : BitRAMO.stepO P w t = BitRAM.step (BitRAMO.lowerP P) w.toW t := by
  unfold BitRAMO.stepO; rw [h]

/-- The step of a query. -/
theorem orcO_spec {P : List BitRAMO.InstrO} {w : BitRAMO.WorldO d} {t : BitRAM.State d} {q : ℕ} {dst src prec : ℤ}
    (h : P[q]? = some (.orc dst src prec)) (hpc : t.pc = q) :
    ∃ t', BitRAMO.stepO P w t = t' ∧ t'.pc = q + 1 ∧
      t'.mem = update t.mem dst (if w.orc (BitRAM.ptAt d t.mem (t.mem src)) (t.mem prec).toNat then 1 else 0) ∧
      t'.cost = t.cost + (1 + BitRAM.len dst + BitRAM.len src + BitRAM.len prec + BitRAM.len (t.mem prec) +
        BitRAM.len (t.mem src) + BitRAM.playCost d t.mem (t.mem src) + (t.mem prec).toNat) ∧ B.Same t t' := by
  subst hpc
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩ <;> simp [BitRAMO.stepO, h, B.Same]

/-- The step of a clipped reading. -/
theorem obsRO_spec {P : List BitRAMO.InstrO} {w : BitRAMO.WorldO d} {t : BitRAM.State d} {q : ℕ}
    {dst prec rng : ℤ} (h : P[q]? = some (.obsR dst prec rng)) (hpc : t.pc = q) :
    ∃ t', BitRAMO.stepO P w t = t' ∧ t'.pc = q + 1 ∧
      t'.mem = update t.mem dst (BitRAMO.clip (t.mem rng).toNat (BitRAM.reading w.toW t (t.mem prec).toNat)) ∧
      t'.cost = t.cost + (1 + BitRAM.len dst + BitRAM.len prec + BitRAM.len rng + BitRAM.len (t.mem prec) +
        BitRAM.len (t.mem rng) + (t.mem prec).toNat + (t.mem rng).toNat) ∧ B.Same t t' := by
  subst hpc
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩ <;> simp [BitRAMO.stepO, h, B.Same]

/-! ## Code placement -/

/-- The list `l` sits at address `o` of the program `P` of the oracle machine. -/
def CodeAtO (P : List BitRAMO.InstrO) (o : ℕ) (l : List BitRAMO.InstrO) : Prop := ∀ i < l.length, P[o + i]? = l[i]?

namespace CodeAtO

variable {P : List BitRAMO.InstrO} {o : ℕ}

theorem append_left {l₁ l₂ : List BitRAMO.InstrO} (h : CodeAtO P o (l₁ ++ l₂)) : CodeAtO P o l₁ := fun i hi => by
  rw [h i (by simp; omega), List.getElem?_append_left hi]

theorem append_right {l₁ l₂ : List BitRAMO.InstrO} (h : CodeAtO P o (l₁ ++ l₂)) :
    CodeAtO P (o + l₁.length) l₂ := fun i hi => by
  have := h (l₁.length + i) (by simp; omega)
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at this
  rw [← this, Nat.add_assoc]

theorem cons_head {x : BitRAMO.InstrO} {l : List BitRAMO.InstrO} (h : CodeAtO P o (x :: l)) : P[o]? = some x := by
  simpa using h 0 (by simp)

theorem cons_tail {x : BitRAMO.InstrO} {l : List BitRAMO.InstrO} (h : CodeAtO P o (x :: l)) :
    CodeAtO P (o + 1) l := fun i hi => by
  have := h (i + 1) (by simp; omega)
  rw [← Nat.add_assoc, Nat.add_right_comm] at this
  simpa using this

theorem cast {o' : ℕ} {l : List BitRAMO.InstrO} (h : CodeAtO P o l) (e : o = o') : CodeAtO P o' l := e ▸ h

theorem head_at {o' : ℕ} {x : BitRAMO.InstrO} {l : List BitRAMO.InstrO} (h : CodeAtO P o (x :: l)) (e : o = o') :
    P[o']? = some x := e ▸ h.cons_head

/-- Base code of the oracle program is code of the lowered program. -/
theorem lower {l : List BitRAM.Instr} (h : CodeAtO P o (bL l)) : B.CodeAt (BitRAMO.lowerP P) o l := fun i hi => by
  have := h i (by simpa using hi)
  simp only [bL, List.getElem?_map] at this
  simp only [BitRAMO.lowerP, List.getElem?_map, this, Option.map_map]
  cases l[i]? <;> rfl

end CodeAtO

/-! ## Blocks on the oracle machine -/

/-- From `t`, `n` steps of the oracle machine reach a state at `q` simulating `s'`, at cost at most `C`. -/
def XBlockO (XO : XCtxO d) (P : List BitRAMO.InstrO) (t : BitRAM.State d) (n q : ℕ) (s' : RealRAM.State d)
    (C : ℕ) : Prop :=
  ∃ t', BitRAMO.runO P XO.w t n = t' ∧ t'.pc = q ∧ XSim XO.X s' t' ∧ t'.cost ≤ t.cost + C

/-- Within `N` steps. -/
def XBlockLEO (XO : XCtxO d) (P : List BitRAMO.InstrO) (t : BitRAM.State d) (N q : ℕ) (s' : RealRAM.State d)
    (C : ℕ) : Prop :=
  ∃ n ≤ N, XBlockO XO P t n q s' C

section Blocks

variable {XO : XCtxO d} {P : List BitRAMO.InstrO}

theorem XBlockO.le {t : BitRAM.State d} {n N q C : ℕ} {s : RealRAM.State d} (h : XBlockO XO P t n q s C)
    (hn : n ≤ N) : XBlockLEO XO P t N q s C := ⟨n, hn, h⟩

theorem XBlockLEO.bind {t : BitRAM.State d} {N₁ N₂ q₁ q₂ C₁ C₂ : ℕ} {s₁ s₂ : RealRAM.State d}
    (h₁ : XBlockLEO XO P t N₁ q₁ s₁ C₁)
    (h₂ : ∀ t₁ : BitRAM.State d, t₁.pc = q₁ → XSim XO.X s₁ t₁ → XBlockLEO XO P t₁ N₂ q₂ s₂ C₂) :
    XBlockLEO XO P t (N₁ + N₂) q₂ s₂ (C₁ + C₂) := by
  obtain ⟨n₁, hn₁, t₁, e₁, p₁, hs₁, c₁⟩ := h₁
  obtain ⟨n₂, hn₂, t₂, e₂, p₂, hs₂, c₂⟩ := h₂ t₁ p₁ hs₁
  exact ⟨n₁ + n₂, by omega, t₂, by rw [runO_add, e₁, e₂], p₂, hs₂, by omega⟩

theorem XBlockLEO.mono {t : BitRAM.State d} {N N' q q' C C' : ℕ} {s : RealRAM.State d}
    (h : XBlockLEO XO P t N q s C) (hN : N ≤ N') (hq : q = q') (hC : C ≤ C') : XBlockLEO XO P t N' q' s C' := by
  obtain ⟨n, hn, t', e, p, hs, c⟩ := h
  exact ⟨n, by omega, t', e, hq ▸ p, hs, by omega⟩

/-- UNI-MACH for a block: a block of the lowered program that ends inside the program is a block of the oracle
machine (`uni_liftO`). -/
theorem XBlock.liftO {t : BitRAM.State d} {n q C : ℕ} {s : RealRAM.State d}
    (h : XBlock XO.X (BitRAMO.lowerP P) t n q s C) (hq : q < P.length) : XBlockO XO P t n q s C := by
  obtain ⟨t', e, p, hs, c⟩ := h
  have e' : BitRAM.run (BitRAMO.lowerP P) XO.w.toW t n = t' := e
  refine ⟨t', ?_, p, hs, c⟩
  rw [uni_liftO P XO.w t n (by rw [e', p]; exact hq), e']

theorem XBlockLE.liftO {t : BitRAM.State d} {N q C : ℕ} {s : RealRAM.State d}
    (h : XBlockLE XO.X (BitRAMO.lowerP P) t N q s C) (hq : q < P.length) : XBlockLEO XO P t N q s C := by
  obtain ⟨n, hn, hb⟩ := h
  exact ⟨n, hn, XBlock.liftO hb hq⟩

end Blocks

/-! ## The new leaves -/

section Leaves

variable {XO : XCtxO d} {P : List BitRAMO.InstrO} {ℓa ℓ : ℕ}

theorem xsimO_orc {s : RealRAM.State d} {t : BitRAM.State d} {o dst src prec : ℕ}
    (hP : CodeAtO P o (xtrLeafO (.orc dst src prec))) (hpc : t.pc = o) (hs : XSim XO.X s t)
    (hoff : XO.off < 2 ^ ℓa) (hok : (LeafO.orc dst src prec).OK (d := d) ℓa ℓ s) :
    XBlockO XO P t 2 (o + 2) ((LeafO.orc dst src prec).exec XO s) ((d + 3) * xstepCost ℓa ℓ) := by
  obtain ⟨hd1, ⟨hs1, hs2⟩, ⟨hp1, hp2⟩, hsd, hv, hk⟩ := hok
  simp only [xtrLeafO] at hP
  have es := hs.nreg src
  have ep := hs.nreg prec
  have eo : t.mem TO = XO.off := hs.off
  have h0 : P[t.pc]? = some (.base (.add T1 (rg src) TO)) := by rw [hpc]; exact hP.cons_head
  obtain ⟨t1, e1, p1, m1, c1, s1⟩ := B.add_spec (w := XO.w.toW) (lowerP_get hP.cons_head) hpc
  obtain ⟨t2, e2, p2, m2, c2, s2⟩ := orcO_spec (w := XO.w) hP.cons_tail.cons_head p1
  have v1 : t1.mem T1 = (s.nreg src : ℤ) + XO.off := by rw [m1]; simp [es, eo]
  have f1 : ∀ c, c ≠ T1 → t1.mem c = t.mem c := fun c hc => by rw [m1, update_of_ne hc]
  have hfl : ∀ j : ℕ, ⌊s.mem j⌋ = t.mem ((j : ℤ) + XO.off) := fun j => by
    rw [← hs.mem j, Int.floor_intCast]; rfl
  have hcell : ∀ i : ℕ, t1.mem ((s.nreg src : ℤ) + XO.off + i) = t.mem (((s.nreg src + i : ℕ) : ℤ) + XO.off) :=
    fun i => by rw [f1 _ (by unfold T1; omega)]; congr 1; push_cast; ring
  have hpt : BitRAM.ptAt d t1.mem (t1.mem T1) = ptQ d s.mem (s.nreg src) := by
    rw [v1]
    funext i
    unfold BitRAM.ptAt ptQ
    have h1 : t1.mem ((s.nreg src : ℤ) + XO.off + 1 + (i : ℕ)) =
        t.mem (((s.nreg src + 1 + (i : ℕ) : ℕ) : ℤ) + XO.off) := by
      rw [f1 _ (by unfold T1; omega)]; congr 1; push_cast; ring
    have h0' : t1.mem ((s.nreg src : ℤ) + XO.off) = t.mem (((s.nreg src : ℕ) : ℤ) + XO.off) := by
      rw [f1 _ (by unfold T1; omega)]
    rw [h1, h0', hfl, hfl]
  have hk' : (t1.mem (rg prec)).toNat = s.nreg prec := by rw [f1 _ (by simp), ep]; simp
  set b := XO.w.orc (ptQ d s.mem (s.nreg src)) (s.nreg prec) with hb
  have hans : (if XO.w.orc (BitRAM.ptAt d t1.mem (t1.mem T1)) (t1.mem (rg prec)).toNat then (1 : ℤ) else 0) =
      (((if b then 1 else 0 : ℕ)) : ℤ) := by
    rw [hpt, hk', ← hb]; split_ifs <;> rfl
  refine ⟨t2, ?_, by rw [p2], ?_, ?_⟩
  · rw [show (2 : ℕ) = 1 + 1 from rfl, runO_add, runO_one, runO_one, stepO_base h0, e1, e2]
  · refine hs.writeReg dst (if b then 1 else 0) (fun c h1 _ => ?_) ?_ ?_ ?_
    · rw [m2, hans]
      by_cases hc : c = rg dst
      · subst hc; simp
      · rw [update_of_ne hc, update_of_ne hc, f1 c h1]
    · rw [s2.1, s1.1]
    · rw [s2.2.1, s1.2.1]
    · rw [s2.2.2, s1.2.2]
  · have lo : BitRAM.len (XO.off : ℤ) ≤ ℓa := len_nat hoff
    have lrs := len_rg hs1
    have lrp := len_rg hp1
    have lrd := len_rg hd1
    have lns := len_nat hs2
    have lnp := len_nat hp2
    have l1 : BitRAM.len ((s.nreg src : ℤ) + XO.off) ≤ ℓa + 1 := len_cl hs2 hoff
    have hpc' : BitRAM.playCost d t1.mem ((s.nreg src : ℤ) + XO.off) ≤ (d + 1) * (1 + (ℓa + 1) + ℓ) := by
      unfold BitRAM.playCost
      refine (Finset.sum_le_card_nsmul _ _ (1 + (ℓa + 1) + ℓ) fun i hi => ?_).trans (by simp)
      rw [Finset.mem_range] at hi
      have hi' : s.nreg src + i < 2 ^ ℓa := by omega
      have la : BitRAM.len ((s.nreg src : ℤ) + XO.off + i) ≤ ℓa + 1 := by
        have : (s.nreg src : ℤ) + XO.off + i = ((s.nreg src + i : ℕ) : ℤ) + XO.off := by push_cast; ring
        rw [this]; exact len_cl hi' hoff
      have lv : BitRAM.len (t1.mem ((s.nreg src : ℤ) + XO.off + i)) ≤ ℓ := by
        rw [hcell i]
        exact len_le_of_cast (hs.mem _) (hv i (by omega))
      omega
    have w1p : t1.mem (rg prec) = s.nreg prec := by rw [f1 _ (by simp), ep]
    rw [c2, c1, v1, es, eo, w1p]
    simp only [len_T1, len_TO]
    have hpn : ((s.nreg prec : ℤ)).toNat = s.nreg prec := by simp
    rw [hpn]
    have hX : 1 + (ℓa + 1) + ℓ ≤ xstepCost ℓa ℓ := by
      unfold xstepCost; have := Nat.zero_le ((ℓa + ℓ + 1) ^ 2); omega
    have hX2 : 8 + 5 * ℓa + ℓ ≤ xstepCost ℓa ℓ := by
      unfold xstepCost; have := Nat.zero_le ((ℓa + ℓ + 1) ^ 2); omega
    have h1 := Nat.mul_le_mul_left (d + 1) hX
    have h2 : (d + 3) * xstepCost ℓa ℓ = (d + 1) * xstepCost ℓa ℓ + 2 * xstepCost ℓa ℓ := by ring
    rw [h2]
    omega

theorem xsimO_obsR {s : RealRAM.State d} {t : BitRAM.State d} {o dst prec rng : ℕ}
    (hP : CodeAtO P o (xtrLeafO (.obsR dst prec rng))) (hpc : t.pc = o) (hs : XSim XO.X s t)
    (hoff : XO.off < 2 ^ ℓa) (hok : (LeafO.obsR dst prec rng).OK (d := d) ℓa ℓ s) :
    XBlockO XO P t 3 (o + 3) ((LeafO.obsR dst prec rng).exec XO s) (xstepCost ℓa ℓ) := by
  obtain ⟨⟨hd1, hd2⟩, ⟨hp1, hp2⟩, ⟨hr1, hr2⟩, hk, hq⟩ := hok
  simp only [xtrLeafO] at hP
  have ed := hs.nreg dst
  have ep := hs.nreg prec
  have er := hs.nreg rng
  have eo : t.mem TO = XO.off := hs.off
  obtain ⟨t1, e1, p1, m1, c1, s1⟩ := obsRO_spec (w := XO.w) hP.cons_head hpc
  have h1 : P[t1.pc]? = some (.base (.add T2 (rg dst) TO)) := by rw [p1]; exact hP.cons_tail.cons_head
  have h2 : P[o + 1 + 1]? = some (.base (.store T2 T1)) := hP.cons_tail.cons_tail.cons_head
  obtain ⟨t2, e2, p2, m2, c2, s2⟩ := B.add_spec (w := XO.w.toW) (lowerP_get hP.cons_tail.cons_head) p1
  have h2' : P[t2.pc]? = some (.base (.store T2 T1)) := by rw [p2]; exact h2
  obtain ⟨t3, e3, p3, m3, c3, s3⟩ := B.store_spec (w := XO.w.toW) (lowerP_get h2) p2
  have hp : (t.mem (rg prec)).toNat = s.nreg prec := by rw [ep]; simp
  have hrn : (t.mem (rg rng)).toNat = s.nreg rng := by rw [er]; simp
  set r := BitRAMO.clip (s.nreg rng) ⌊(2 : ℝ) ^ (s.nreg prec) * fbR XO.X s⌋ with hr
  have hrd : BitRAMO.clip (t.mem (rg rng)).toNat (BitRAM.reading XO.w.toW t (t.mem (rg prec)).toNat) = r := by
    rw [hp, hrn, hr, BitRAM.reading]
    have := feedback_eq (X := XO.X) hs
    rw [← this]; rfl
  have v1 : t1.mem T1 = r := by rw [m1, hrd]; simp
  have v2 : t2.mem T2 = (s.nreg dst : ℤ) + XO.off := by rw [m2]; simp [m1, ed, eo]
  have v2' : t2.mem T1 = r := by rw [m2]; simp [v1]
  have hS := s1.trans (s2.trans s3)
  refine ⟨t3, ?_, by rw [p3], ?_, ?_⟩
  · rw [show (3 : ℕ) = 1 + 1 + 1 from rfl, runO_add, runO_add, runO_one, runO_one, runO_one, e1, stepO_base h1, e2,
      stepO_base h2', e3]
  · refine hs.write (s.nreg dst) r (r : ℝ) rfl (fun c h1 h2 => ?_) hS.1 hS.2.1 hS.2.2
    rw [m3, v2, v2']
    simp only [XCtxO.X_off]
    by_cases hc : c = (s.nreg dst : ℤ) + XO.off
    · subst hc; simp
    · rw [update_of_ne hc, update_of_ne hc, m2, m1]; simp [h1, h2]
  · have l3 : BitRAM.len ((s.nreg dst : ℤ) + XO.off) ≤ ℓa + 1 := len_cl hd2 hoff
    have lo : BitRAM.len (XO.off : ℤ) ≤ ℓa := len_nat hoff
    have lrd := len_rg hd1
    have lrp := len_rg hp1
    have lrr := len_rg hr1
    have lnd := len_nat hd2
    have lnp := len_nat hp2
    have lnr := len_nat hr2
    have lr : BitRAM.len r ≤ ℓ := (uni_clip_lenO _ _).trans (by omega)
    have w1 : t1.mem (rg dst) = s.nreg dst := by rw [m1]; simp [ed]
    have w1o : t1.mem TO = XO.off := by rw [m1]; simp [eo]
    rw [c3, c2, c1, w1, w1o, v2, v2', hp, hrn, ep, er]
    simp only [len_T1, len_T2, len_TO]
    unfold xstepCost
    have := Nat.zero_le ((ℓa + ℓ + 1) ^ 2); omega

theorem xsimO_leaf {l : LeafO} {s : RealRAM.State d} {t : BitRAM.State d} {o : ℕ}
    (hP : CodeAtO P o (xtrLeafO l)) (hpc : t.pc = o) (hs : XSim XO.X s t) (hoff : XO.off < 2 ^ ℓa)
    (hok : l.OK (d := d) ℓa ℓ s) :
    (xtrLeafO l).length ≤ 7 * l.units d ∧
      XBlockO XO P t (xtrLeafO l).length (o + (xtrLeafO l).length) (l.exec XO s) (l.units d * xstepCost ℓa ℓ) := by
  cases l with
  | orc dst src prec => exact ⟨by simp [xtrLeafO, LeafO.units]; omega, xsimO_orc hP hpc hs hoff hok⟩
  | obsR dst prec rng =>
    exact ⟨by simp [xtrLeafO, LeafO.units], by
      rw [show LeafO.units d (.obsR dst prec rng) = 1 from rfl, one_mul]; exact xsimO_obsR hP hpc hs hoff hok⟩

end Leaves

/-! ## The transfer theorem -/

/-- TRANSFER on the oracle machine: a bounded run of the oracle language on the real state is a run of the compiled
code on the oracle machine, in the world of the context, within `7 k` steps and at cost at most
`k * xstepCost ℓa ℓ`, when the code is followed by at least one instruction of the program. -/
theorem xtransferO {XO : XCtxO d} {P : List BitRAMO.InstrO} {ℓa ℓ : ℕ} (hoff : XO.off < 2 ^ ℓa) {c : XCmdO}
    {s s' : RealRAM.State d} {k : ℕ} (h : XExecBO XO ℓa ℓ c s k s') :
    ∀ (o : ℕ) (t : BitRAM.State d), CodeAtO P o (xtrO c o) → o + xtlenO c < P.length → t.pc = o → XSim XO.X s t →
      XBlockLEO XO P t (7 * k) (o + xtlenO c) s' (k * xstepCost ℓa ℓ) := by
  have hoff' : XO.X.off < 2 ^ ℓa := hoff
  induction h with
  | @base c s s' k hex =>
    intro o t hP hend hpc hs
    exact XBlockLE.liftO (xtransfer (P := BitRAMO.lowerP P) hoff' hex o t hP.lower hpc hs) hend
  | leaf l s hok =>
    intro o t hP _ hpc hs
    obtain ⟨hl, hb⟩ := xsimO_leaf hP hpc hs hoff hok
    exact (hb.le hl).mono le_rfl (by simp [xtlenO]) le_rfl
  | @seq c₁ c₂ s s₁ s₂ k₁ k₂ _ _ ih₁ ih₂ =>
    intro o t hP hend hpc hs
    simp only [xtrO] at hP
    simp only [xtlenO] at hend
    refine ((ih₁ o t hP.append_left (by omega) hpc hs).bind
      (fun t₁ p₁ hs₁ => ih₂ (o + xtlenO c₁) t₁ (by simpa using hP.append_right) (by omega) p₁ hs₁)).mono
      (by omega) (by simp [xtlenO]; omega) (by rw [add_mul])
  | @ifR_t a b c₁ c₂ s s' k hok hc _ ih =>
    intro o t hP hend hpc hs
    simp only [xtrO] at hP
    simp only [xtlenO] at hend
    have hT := xsim_testR (P := BitRAMO.lowerP P) hP.append_left.lower hpc hs hoff' hok
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at hT
    have hc₁ : CodeAtO P (o + xtlenO c₂ + 6) (xtrO c₁ (o + xtlenO c₂ + 6)) :=
      hP.append_right.append_right.cons_tail.cast (by simp [testRCode]; omega)
    refine (((XBlock.liftO hT (by omega)).le le_rfl).bind (fun t₁ p₁ hs₁ => ih _ t₁ hc₁ (by omega) p₁ hs₁)).mono
      (by omega) (by simp [xtlenO]; omega) ?_
    have := xtestR_le ℓa ℓ
    nlinarith
  | @ifR_f a b c₁ c₂ s s' k hok hc _ ih =>
    intro o t hP hend hpc hs
    simp only [xtrO] at hP
    simp only [xtlenO] at hend
    have hT := xsim_testR (P := BitRAMO.lowerP P) hP.append_left.lower hpc hs hoff' hok
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at hT
    have hc₂ : CodeAtO P (o + 5) (xtrO c₂ (o + 5)) := hP.append_right.append_left.cast (by simp [testRCode])
    have hj := hP.append_right.append_right.head_at (o' := o + 5 + xtlenO c₂) (by simp [testRCode])
    refine ((((XBlock.liftO hT (by omega)).le le_rfl).bind (fun t₁ p₁ hs₁ => ih _ t₁ hc₂ (by omega) p₁ hs₁)).bind
      (fun t₂ p₂ hs₂ => (XBlock.liftO (xsim_jmp (lowerP_get hj) p₂ hs₂) (by omega)).le le_rfl)).mono (by omega)
      (by simp [xtlenO]; omega) ?_
    have := xtestR_le ℓa ℓ
    nlinarith
  | @ifN_t a b c₁ c₂ s s' k hok hc _ ih =>
    intro o t hP hend hpc hs
    simp only [xtrO] at hP
    simp only [xtlenO] at hend
    have hT := xsim_testN (X := XO.X) (lowerP_get hP.cons_head) hpc hs hok
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at hT
    have hc₁ : CodeAtO P (o + xtlenO c₂ + 2) (xtrO c₁ (o + xtlenO c₂ + 2)) :=
      hP.cons_tail.append_right.cons_tail.cast (by simp; omega)
    refine (((XBlock.liftO hT (by omega)).le le_rfl).bind (fun t₁ p₁ hs₁ => ih _ t₁ hc₁ (by omega) p₁ hs₁)).mono
      (by omega) (by simp [xtlenO]; omega) ?_
    have := xtestN_le ℓa ℓ
    nlinarith
  | @ifN_f a b c₁ c₂ s s' k hok hc _ ih =>
    intro o t hP hend hpc hs
    simp only [xtrO] at hP
    simp only [xtlenO] at hend
    have hT := xsim_testN (X := XO.X) (lowerP_get hP.cons_head) hpc hs hok
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at hT
    have hc₂ : CodeAtO P (o + 1) (xtrO c₂ (o + 1)) := hP.cons_tail.append_left
    have hj := hP.cons_tail.append_right.head_at (o' := o + 1 + xtlenO c₂) (by simp)
    refine ((((XBlock.liftO hT (by omega)).le le_rfl).bind (fun t₁ p₁ hs₁ => ih _ t₁ hc₂ (by omega) p₁ hs₁)).bind
      (fun t₂ p₂ hs₂ => (XBlock.liftO (xsim_jmp (lowerP_get hj) p₂ hs₂) (by omega)).le le_rfl)).mono (by omega)
      (by simp [xtlenO]; omega) ?_
    have := xtestN_le ℓa ℓ
    nlinarith
  | @whileR_t a b c s s₁ s₂ k k' hok hc _ _ ih₁ ih₂ =>
    intro o t hP hend hpc hs
    have hP0 := hP
    have hend0 := hend
    simp only [xtrO] at hP
    simp only [xtlenO] at hend
    have hT := xsim_testR (P := BitRAMO.lowerP P) hP.append_left.lower hpc hs hoff' hok
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at hT
    have hcb : CodeAtO P (o + 6) (xtrO c (o + 6)) :=
      hP.append_right.cons_tail.append_left.cast (by simp [testRCode])
    have hj := hP.append_right.cons_tail.append_right.head_at (o' := o + 6 + xtlenO c) (by simp [testRCode])
    refine (((((XBlock.liftO hT (by omega)).le le_rfl).bind (fun t₁ p₁ hs₁ => ih₁ _ t₁ hcb (by omega) p₁ hs₁)).bind
      (fun t₂ p₂ hs₂ => (XBlock.liftO (xsim_jmp (lowerP_get hj) p₂ hs₂) (by omega)).le le_rfl)).bind
      (fun t₃ p₃ hs₃ => ih₂ o t₃ hP0 hend0 p₃ hs₃)).mono (by omega) rfl ?_
    have := xtestR_le ℓa ℓ
    nlinarith
  | @whileR_f a b c s hok hc =>
    intro o t hP hend hpc hs
    simp only [xtrO] at hP
    simp only [xtlenO] at hend
    have hT := xsim_testR (P := BitRAMO.lowerP P) hP.append_left.lower hpc hs hoff' hok
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at hT
    have hj := hP.append_right.head_at (o' := o + 5) (by simp [testRCode])
    refine (((XBlock.liftO hT (by omega)).le le_rfl).bind
      (fun t₁ p₁ hs₁ => (XBlock.liftO (xsim_jmp (lowerP_get hj) p₁ hs₁) (by omega)).le le_rfl)).mono (by omega)
      (by simp [xtlenO]; omega) ?_
    have := xtestR_le ℓa ℓ
    nlinarith
  | @whileN_t a b c s s₁ s₂ k k' hok hc _ _ ih₁ ih₂ =>
    intro o t hP hend hpc hs
    have hP0 := hP
    have hend0 := hend
    simp only [xtrO] at hP
    simp only [xtlenO] at hend
    have hT := xsim_testN (X := XO.X) (lowerP_get hP.cons_head) hpc hs hok
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at hT
    have hcb : CodeAtO P (o + 2) (xtrO c (o + 2)) := hP.cons_tail.cons_tail.append_left.cast (by omega)
    have hj := hP.cons_tail.cons_tail.append_right.head_at (o' := o + 2 + xtlenO c) (by simp)
    refine (((((XBlock.liftO hT (by omega)).le le_rfl).bind (fun t₁ p₁ hs₁ => ih₁ _ t₁ hcb (by omega) p₁ hs₁)).bind
      (fun t₂ p₂ hs₂ => (XBlock.liftO (xsim_jmp (lowerP_get hj) p₂ hs₂) (by omega)).le le_rfl)).bind
      (fun t₃ p₃ hs₃ => ih₂ o t₃ hP0 hend0 p₃ hs₃)).mono (by omega) rfl ?_
    have := xtestN_le ℓa ℓ
    nlinarith
  | @whileN_f a b c s hok hc =>
    intro o t hP hend hpc hs
    simp only [xtrO] at hP
    simp only [xtlenO] at hend
    have hT := xsim_testN (X := XO.X) (lowerP_get hP.cons_head) hpc hs hok
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at hT
    have hj := hP.cons_tail.head_at (o' := o + 1) rfl
    refine (((XBlock.liftO hT (by omega)).le le_rfl).bind
      (fun t₁ p₁ hs₁ => (XBlock.liftO (xsim_jmp (lowerP_get hj) p₁ hs₁) (by omega)).le le_rfl)).mono (by omega)
      (by simp [xtlenO]; omega) ?_
    have := xtestN_le ℓa ℓ
    nlinarith

end AdversarialBco.Uni
