/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.StatementBitRAMO
public import AdversarialBco.Bit.Transfer.XRuns
public import AdversarialBco.Bit.Transfer.XEllRow
public import AdversarialBco.Unified.LeafFrozen

@[expose] public section

/-!
# The extended language over the oracle machine (UNI-MACH, the leaf layer)

The structured language of Bit/Transfer (`XCmd`, its bounded semantics `XExecB` on real states and its compiler
`xtr` to the bit machine) lifted to the oracle machine of StatementBitRAMO.lean:

* `XCtxO`: the context of a run, the world of the oracle machine (losses, noise, coins, oracle), the input cells and
  the offset of the real cells; `XCtxO.X` is the bit context that the base instructions see (`WorldO.toW`).
* `LeafO`: the two new leaves. `orc dst src prec`: the natural register `dst` receives `1` if the oracle accepts the
  rational point stored at the real cells `N src, ..., N src + d` (denominator first) at the precision `N prec`, and
  `0` otherwise. `obsR dst prec rng`: `M (N dst) := clip (N rng) ⌊2^(N prec) o⌋`, `o` the noisy feedback of the last
  round played.
* `XCmdO`: a command of `XCmd` (`base`, run as the bit machine), a new leaf, and the control of `XCmd` over them;
  `XExecBO` its bounded semantics, `xtrO` its code for the oracle machine (a base block is the code of `xtr` with every
  instruction wrapped in `InstrO.base`, so its jumps keep their absolute targets).
* `XRunsBO`: the contract of a routine on typed variables (`XRunsB` with `XExecBO`).

The transfer to `runO` (through `uni_liftO` for the base blocks) is in XTransO.lean; the rules of `XRunsBO` in
XRunsO.lean.
-/

namespace AdversarialBco.Uni

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.Transfer

variable {d : ℕ}

/-- The context of a run on the oracle machine: its world, the input cells and the offset of the real cells. -/
structure XCtxO (d : ℕ) where
  /-- The world of the oracle machine: losses, noise, coins and the oracle. -/
  w : BitRAMO.WorldO d
  /-- The input cells. -/
  inp : ℕ → ℤ
  /-- The offset of the real cells in the bit memory. -/
  off : ℕ

/-- The bit context that the base instructions see: the coins and the noisy feedback. -/
def XCtxO.X (XO : XCtxO d) : XCtx d := ⟨XO.w.toW, XO.inp, XO.off⟩

/-- The rational point with its denominator in the real cell `a` and its numerators in `a + 1, ..., a + d`, read through
floors (the cells of a bounded run hold integers). -/
noncomputable def ptQ (d : ℕ) (m : ℕ → ℝ) (a : ℕ) : Fin d → ℚ :=
  fun i => (⌊m (a + 1 + (i : ℕ))⌋ : ℚ) / (⌊m a⌋ : ℚ)

/-- The leaves of the oracle machine. -/
inductive LeafO
  /-- `N dst :=` the answer (`1` or `0`) of the oracle at the point of the cells `N src, ..., N src + d` and the
  precision `N prec`. -/
  | orc (dst src prec : ℕ)
  /-- `M (N dst) := clip (N rng) ⌊2^(N prec) o⌋`, `o` the feedback of the last round played. -/
  | obsR (dst prec rng : ℕ)

/-- The effect of a new leaf on the real state. -/
noncomputable def LeafO.exec (XO : XCtxO d) (s : RealRAM.State d) : LeafO → RealRAM.State d
  | .orc dst src prec =>
    { s with
        nreg := Function.update s.nreg dst (if XO.w.orc (ptQ d s.mem (s.nreg src)) (s.nreg prec) then 1 else 0) }
  | .obsR dst prec rng =>
    { s with
        mem := Function.update s.mem (s.nreg dst)
          (BitRAMO.clip (s.nreg rng) ⌊(2 : ℝ) ^ (s.nreg prec) * fbR XO.X s⌋ : ℝ) }

/-- A new leaf within the bounds: registers within `ℓa` bits, the cells of the point within `ℓ` bits and their addresses
within `ℓa` bits, the precision at most `ℓ`, the range below `ℓ`. -/
def LeafO.OK (ℓa ℓ : ℕ) (s : RealRAM.State d) : LeafO → Prop
  | .orc dst src prec => dst + 4 < 2 ^ ℓa ∧ RegOK ℓa s src ∧ RegOK ℓa s prec ∧ s.nreg src + d < 2 ^ ℓa ∧
      (∀ i ≤ d, |s.mem (s.nreg src + i)| < 2 ^ ℓ) ∧ s.nreg prec ≤ ℓ
  | .obsR dst prec rng => RegOK ℓa s dst ∧ RegOK ℓa s prec ∧ RegOK ℓa s rng ∧ s.nreg prec ≤ ℓ ∧ s.nreg rng < ℓ

/-- The units of cost of a new leaf: a query reads `d + 1` cells and its precision, a clipped reading is one unit. -/
def LeafO.units (d : ℕ) : LeafO → ℕ
  | .orc .. => d + 3
  | .obsR .. => 1

/-- The commands of the oracle machine: a command of the bit machine's language, a new leaf, and the control. -/
inductive XCmdO
  | base (c : XCmd)
  | leaf (l : LeafO)
  | seq (c₁ c₂ : XCmdO)
  /-- `if M (N a) < M (N b) then c₁ else c₂`. -/
  | ifR (a b : ℕ) (c₁ c₂ : XCmdO)
  /-- `if N a < N b then c₁ else c₂`. -/
  | ifN (a b : ℕ) (c₁ c₂ : XCmdO)
  /-- `while M (N a) < M (N b) do c`. -/
  | whileR (a b : ℕ) (c : XCmdO)
  /-- `while N a < N b do c`. -/
  | whileN (a b : ℕ) (c : XCmdO)

/-- The bounded semantics of `XCmdO` on real states, in units of cost (`XExecB` with the new leaves). -/
inductive XExecBO (XO : XCtxO d) (ℓa ℓ : ℕ) : XCmdO → RealRAM.State d → ℕ → RealRAM.State d → Prop
  | base {c : XCmd} {s s' : RealRAM.State d} {k : ℕ} :
      XExecB XO.X ℓa ℓ c s k s' → XExecBO XO ℓa ℓ (.base c) s k s'
  | leaf (l : LeafO) (s : RealRAM.State d) : l.OK ℓa ℓ s → XExecBO XO ℓa ℓ (.leaf l) s (l.units d) (l.exec XO s)
  | seq {c₁ c₂ : XCmdO} {s s₁ s₂ : RealRAM.State d} {k₁ k₂ : ℕ} :
      XExecBO XO ℓa ℓ c₁ s k₁ s₁ → XExecBO XO ℓa ℓ c₂ s₁ k₂ s₂ → XExecBO XO ℓa ℓ (.seq c₁ c₂) s (k₁ + k₂) s₂
  | ifR_t {a b : ℕ} {c₁ c₂ : XCmdO} {s s' : RealRAM.State d} {k : ℕ} :
      TestR ℓa ℓ s a b → condR s a b → XExecBO XO ℓa ℓ c₁ s k s' → XExecBO XO ℓa ℓ (.ifR a b c₁ c₂) s (k + 1) s'
  | ifR_f {a b : ℕ} {c₁ c₂ : XCmdO} {s s' : RealRAM.State d} {k : ℕ} :
      TestR ℓa ℓ s a b → ¬ condR s a b → XExecBO XO ℓa ℓ c₂ s k s' → XExecBO XO ℓa ℓ (.ifR a b c₁ c₂) s (k + 2) s'
  | ifN_t {a b : ℕ} {c₁ c₂ : XCmdO} {s s' : RealRAM.State d} {k : ℕ} :
      TestN ℓa s a b → condN s a b → XExecBO XO ℓa ℓ c₁ s k s' → XExecBO XO ℓa ℓ (.ifN a b c₁ c₂) s (k + 1) s'
  | ifN_f {a b : ℕ} {c₁ c₂ : XCmdO} {s s' : RealRAM.State d} {k : ℕ} :
      TestN ℓa s a b → ¬ condN s a b → XExecBO XO ℓa ℓ c₂ s k s' → XExecBO XO ℓa ℓ (.ifN a b c₁ c₂) s (k + 2) s'
  | whileR_t {a b : ℕ} {c : XCmdO} {s s₁ s₂ : RealRAM.State d} {k k' : ℕ} :
      TestR ℓa ℓ s a b → condR s a b → XExecBO XO ℓa ℓ c s k s₁ → XExecBO XO ℓa ℓ (.whileR a b c) s₁ k' s₂ →
        XExecBO XO ℓa ℓ (.whileR a b c) s (k + 2 + k') s₂
  | whileR_f {a b : ℕ} {c : XCmdO} {s : RealRAM.State d} :
      TestR ℓa ℓ s a b → ¬ condR s a b → XExecBO XO ℓa ℓ (.whileR a b c) s 2 s
  | whileN_t {a b : ℕ} {c : XCmdO} {s s₁ s₂ : RealRAM.State d} {k k' : ℕ} :
      TestN ℓa s a b → condN s a b → XExecBO XO ℓa ℓ c s k s₁ → XExecBO XO ℓa ℓ (.whileN a b c) s₁ k' s₂ →
        XExecBO XO ℓa ℓ (.whileN a b c) s (k + 2 + k') s₂
  | whileN_f {a b : ℕ} {c : XCmdO} {s : RealRAM.State d} :
      TestN ℓa s a b → ¬ condN s a b → XExecBO XO ℓa ℓ (.whileN a b c) s 2 s

/-! ## The code -/

/-- Instructions of the bit machine as base instructions of the oracle machine. -/
def bL (l : List BitRAM.Instr) : List BitRAMO.InstrO := l.map .base

/-- The code of a new leaf: the address of the point through the offset, then the query; the clipped reading into `T1`,
then stored through the offset. -/
def xtrLeafO : LeafO → List BitRAMO.InstrO
  | .orc dst src prec => [.base (.add T1 (rg src) TO), .orc (rg dst) T1 (rg prec)]
  | .obsR dst prec rng => [.obsR T1 (rg prec) (rg rng), .base (.add T2 (rg dst) TO), .base (.store T2 T1)]

/-- The length of the code of a command. -/
def xtlenO : XCmdO → ℕ
  | .base c => xtlen c
  | .leaf l => (xtrLeafO l).length
  | .seq c₁ c₂ => xtlenO c₁ + xtlenO c₂
  | .ifR _ _ c₁ c₂ => xtlenO c₁ + xtlenO c₂ + 6
  | .ifN _ _ c₁ c₂ => xtlenO c₁ + xtlenO c₂ + 2
  | .whileR _ _ c => xtlenO c + 7
  | .whileN _ _ c => xtlenO c + 3

/-- The code of a command for the oracle machine, placed at address `o` (absolute jumps, as `xtr`). -/
def xtrO : XCmdO → ℕ → List BitRAMO.InstrO
  | .base c, o => bL (xtr c o)
  | .leaf l, _ => xtrLeafO l
  | .seq c₁ c₂, o => xtrO c₁ o ++ xtrO c₂ (o + xtlenO c₁)
  | .ifR a b c₁ c₂, o =>
    bL (testRCode a b (o + xtlenO c₂ + 6)) ++
      (xtrO c₂ (o + 5) ++ .base (.jmp (o + xtlenO c₂ + 6 + xtlenO c₁)) :: xtrO c₁ (o + xtlenO c₂ + 6))
  | .ifN a b c₁ c₂, o =>
    .base (.jlt (rg a) (rg b) (o + xtlenO c₂ + 2)) ::
      (xtrO c₂ (o + 1) ++ .base (.jmp (o + xtlenO c₂ + 2 + xtlenO c₁)) :: xtrO c₁ (o + xtlenO c₂ + 2))
  | .whileR a b c, o =>
    bL (testRCode a b (o + 6)) ++ (.base (.jmp (o + xtlenO c + 7)) :: (xtrO c (o + 6) ++ [.base (.jmp o)]))
  | .whileN a b c, o =>
    .base (.jlt (rg a) (rg b) (o + 2)) :: .base (.jmp (o + xtlenO c + 3)) :: (xtrO c (o + 2) ++ [.base (.jmp o)])

@[simp] theorem length_bL (l : List BitRAM.Instr) : (bL l).length = l.length := List.length_map _

@[simp] theorem length_xtrO (c : XCmdO) (o : ℕ) : (xtrO c o).length = xtlenO c := by
  induction c generalizing o <;> simp [xtrO, xtlenO, testRCode, *] <;> omega

/-! ## Routines on typed variables -/

/-- From every real state that represents `σ` in the layout `L`, the command `c` runs in the bounded semantics within
`K` units to a state representing an environment that satisfies `Q` (`XRunsB` on the oracle machine). -/
def XRunsBO (L : Layout) (XO : XCtxO d) (ℓa ℓ : ℕ) (c : XCmdO) (σ : Env d) (K : ℕ) (Q : Env d → Prop) : Prop :=
  ∀ s, Rep L σ s → ∃ k s' σ', k ≤ K ∧ XExecBO XO ℓa ℓ c s k s' ∧ Rep L σ' s' ∧ Q σ'

/-- The rational point stored in array `v`: denominator in entry `0`, numerators in entries `1, ..., d`, through
floors. -/
noncomputable def ptArr (σ : Env d) (v : ℕ) : Fin d → ℚ :=
  fun i => (⌊σ.arr v (1 + (i : ℕ))⌋ : ℚ) / (⌊σ.arr v 0⌋ : ℚ)

/-- `nat i :=` the answer of the oracle at the point stored in array `v` and the precision `nat p`. -/
def xorcO (L : Layout) (i v p : ℕ) : XCmdO := .leaf (.orc i (L.rA v) p)

/-- `sc x := clip (nat q) ⌊2^(nat p) o⌋`, `o` the noisy feedback of the last round played. -/
def xobsRO (L : Layout) (x p q : ℕ) : XCmdO := .leaf (.obsR (L.rS x) p q)

/-- `if sc x < sc y then c₁ else c₂`. -/
def xifSO (L : Layout) (x y : ℕ) (c₁ c₂ : XCmdO) : XCmdO := .ifR (L.rS x) (L.rS y) c₁ c₂

/-- `for i < n do body` (`one` holds `1`), as `xforN`. -/
def xforNO (i n one : ℕ) (body : XCmdO) : XCmdO :=
  .seq (.base (.prim (.frag (.nconst i 0)))) (.whileN i n (.seq body (.base (.prim (.frag (.nadd i i one))))))

end AdversarialBco.Uni
