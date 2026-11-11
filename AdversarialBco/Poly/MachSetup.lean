/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachProg

@[expose] public section

/-! # The setup of the registers

The rules of the parts of `setup` (MachVL.lean): `setRS` points the scalar registers at their cells, `setRA`
the array registers at their bases, the loop that computes `d²`; `setup_rep`: the setup represents the initial
environment. -/

open AdversarialBco AdversarialBco.RealRAM AdversarialBco.Poly.Mach AdversarialBco.Poly.Mach.VL

/-- `setRS L k` points the registers of the scalars `x < k` at the cells `x`, in `k` steps. -/
theorem AdversarialBco.Poly.Mach.exec_setRS {d : ℕ} (L : Layout) (w : World d) (k : ℕ) (s : State d) :
    ∃ s', Exec w (setRS L k) s k s' ∧ s'.pc = s.pc ∧ s'.mem = s.mem ∧ s'.draws = s.draws ∧
      s'.rounds = s.rounds ∧ s'.pts = s.pts ∧ (∀ x < k, s'.nreg (L.rS x) = x) ∧
      (∀ r, (∀ x < k, r ≠ L.rS x) → s'.nreg r = s.nreg r) := by
  induction k with
  | zero =>
    refine ⟨s, Exec.skip s, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · intro x hx; exfalso; exact Nat.not_lt_zero _ hx
    · intro r hr; rfl
  | succ k ih =>
    rcases ih with ⟨s₁, hExec₁, hpc₁, hmem₁, hdraws₁, hrounds₁, hpts₁, hnreg₁, hnreg_other₁⟩
    have hPrim : Exec w (.prim (.nconst (L.rS k) k)) s₁ 1 (Prim.exec w s₁ (.nconst (L.rS k) k)) :=
      Exec.prim (.nconst (L.rS k) k) s₁
    let s₂ : State d := { s₁ with nreg := Function.update s₁.nreg (L.rS k) k }
    have hExec_seq : Exec w (setRS L (k + 1)) s (k + 1) s₂ := by
      simp [setRS, s₂]
      exact Exec.seq hExec₁ hPrim
    have hpc₂ : s₂.pc = s.pc := by dsimp [s₂]; rw [hpc₁]
    have hmem₂ : s₂.mem = s.mem := by dsimp [s₂]; rw [hmem₁]
    have hdraws₂ : s₂.draws = s.draws := by dsimp [s₂]; rw [hdraws₁]
    have hrounds₂ : s₂.rounds = s.rounds := by dsimp [s₂]; rw [hrounds₁]
    have hpts₂ : s₂.pts = s.pts := by dsimp [s₂]; rw [hpts₁]
    have hnreg₂ : ∀ x < k + 1, s₂.nreg (L.rS x) = x := by
      intro x hx
      have hx' : x ≤ k := by omega
      rcases Nat.le_iff_lt_or_eq.mp hx' with (hx_lt_k | rfl)
      · have hne : L.rS x ≠ L.rS k := by
          unfold Layout.rS; omega
        dsimp [s₂]
        simp [hne, hnreg₁ x hx_lt_k]
      · dsimp [s₂]
        simp
    have hnreg_other₂ : ∀ r, (∀ x < k + 1, r ≠ L.rS x) → s₂.nreg r = s.nreg r := by
      intro r hr
      have hr' : ∀ x < k, r ≠ L.rS x := by
        intro x hx
        apply hr x
        omega
      have hne : r ≠ L.rS k := hr k (Nat.lt_succ_self k)
      dsimp [s₂]
      simp [hnreg_other₁ r hr', hne]
    exact ⟨s₂, hExec_seq, hpc₂, hmem₂, hdraws₂, hrounds₂, hpts₂, hnreg₂, hnreg_other₂⟩

/-- `setRA L k` points the registers of the arrays `a < k` at their bases, in `2 k` steps. -/
theorem AdversarialBco.Poly.Mach.exec_setRA {d : ℕ} (L : Layout) (w : World d) (hNS : 1 ≤ L.NS) (k : ℕ)
    (s : State d) (hSZ : s.nreg L.rSZ = asz d) (hS0 : s.nreg (L.rS 0) = 0) (hT : s.nreg L.rT = L.NS + 1) :
    ∃ s', Exec w (setRA L k) s (2 * k) s' ∧ s'.pc = s.pc ∧ s'.mem = s.mem ∧ s'.draws = s.draws ∧
      s'.rounds = s.rounds ∧ s'.pts = s.pts ∧ (∀ a < k, s'.nreg (L.rA a) = L.base d a) ∧
      s'.nreg L.rT = L.base d k ∧ (∀ r, r ≠ L.rT → (∀ a < k, r ≠ L.rA a) → s'.nreg r = s.nreg r) := by
  -- Use a helper lemma with different binder names to avoid shadowing
  have h_main : ∀ (n : ℕ) (s' : State d), s'.nreg L.rSZ = asz d → s'.nreg (L.rS 0) = 0 → s'.nreg L.rT = L.NS + 1 →
      ∃ s'', Exec w (setRA L n) s' (2 * n) s'' ∧ s''.pc = s'.pc ∧ s''.mem = s'.mem ∧ s''.draws = s'.draws ∧
      s''.rounds = s'.rounds ∧ s''.pts = s'.pts ∧ (∀ (x : ℕ), x < n → s''.nreg (L.rA x) = L.base d x) ∧
      s''.nreg L.rT = L.base d n ∧
        (∀ (r : ℕ), r ≠ L.rT → (∀ (x : ℕ), x < n → r ≠ L.rA x) → s''.nreg r = s'.nreg r) := by
    intro n
    induction n with
    | zero =>
      intro s' hSZ' hS0' hT'
      refine ⟨s', Exec.skip s', rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
      · intro x hx; exact (Nat.not_lt_zero _ hx).elim
      · rw [hT']; unfold Layout.base; simp
      · intro r hr hra; rfl
    | succ n ih =>
      intro s' hSZ' hS0' hT'
      rcases ih s' hSZ' hS0' hT' with ⟨s₁, h_exec₁, h_pc₁, h_mem₁, h_draws₁, h_rounds₁, h_pts₁, h_rA₁, h_rT₁, h_other₁⟩
      have h_ne_rS0_rT : L.rS 0 ≠ L.rT := by
        unfold Layout.rS Layout.rT; omega
      have h_ne_rS0_rA : ∀ x < n, L.rS 0 ≠ L.rA x := by
        intro x hx; unfold Layout.rS Layout.rA; omega
      have h_nreg_rS0 : s₁.nreg (L.rS 0) = s'.nreg (L.rS 0) :=
        h_other₁ (L.rS 0) h_ne_rS0_rT h_ne_rS0_rA
      have h_ne_rSZ_rT : L.rSZ ≠ L.rT := by
        unfold Layout.rSZ Layout.rT; omega
      have h_ne_rSZ_rA : ∀ x < n, L.rSZ ≠ L.rA x := by
        intro x hx; unfold Layout.rSZ Layout.rA; omega
      have h_nreg_rSZ : s₁.nreg L.rSZ = s'.nreg L.rSZ :=
        h_other₁ L.rSZ h_ne_rSZ_rT h_ne_rSZ_rA
      have h_nadd1_exec : Exec w (.prim (.nadd (L.rA n) L.rT (L.rS 0))) s₁ 1
        (Prim.exec w s₁ (.nadd (L.rA n) L.rT (L.rS 0))) :=
        Exec.prim _ _
      set s₂ := Prim.exec w s₁ (.nadd (L.rA n) L.rT (L.rS 0)) with hs₂_def
      have h_nadd2_exec : Exec w (.prim (.nadd L.rT L.rT L.rSZ)) s₂ 1
        (Prim.exec w s₂ (.nadd L.rT L.rT L.rSZ)) :=
        Exec.prim _ _
      set s₃ := Prim.exec w s₂ (.nadd L.rT L.rT L.rSZ) with hs₃_def
      have h_seq2_exec : Exec w (.seq (.prim (.nadd (L.rA n) L.rT (L.rS 0))) (.prim (.nadd L.rT L.rT L.rSZ))) s₁ 2 s₃ :=
        Exec.seq h_nadd1_exec h_nadd2_exec
      have h_total : Exec w (setRA L (n + 1)) s' (2 * (n + 1)) s₃ := by
        rw [setRA]
        have h := Exec.seq h_exec₁ h_seq2_exec
        exact h.cost (by omega)
      have h_pc₃ : s₃.pc = s'.pc := by
        rw [hs₃_def, hs₂_def]; simp [Prim.exec, h_pc₁]
      have h_mem₃ : s₃.mem = s'.mem := by
        rw [hs₃_def, hs₂_def]; simp [Prim.exec, h_mem₁]
      have h_draws₃ : s₃.draws = s'.draws := by
        rw [hs₃_def, hs₂_def]; simp [Prim.exec, h_draws₁]
      have h_rounds₃ : s₃.rounds = s'.rounds := by
        rw [hs₃_def, hs₂_def]; simp [Prim.exec, h_rounds₁]
      have h_pts₃ : s₃.pts = s'.pts := by
        rw [hs₃_def, hs₂_def]; simp [Prim.exec, h_pts₁]
      have h_nreg_unch (dst a b r : ℕ) (hr : r ≠ dst) (t : State d) :
          (Prim.exec w t (.nadd dst a b)).nreg r = t.nreg r := by
        simp [Prim.exec, hr]
      have h_rA₃ : ∀ x < n + 1, s₃.nreg (L.rA x) = L.base d x := by
        intro x hx
        have hx_le : x ≤ n := Nat.le_of_lt_succ hx
        by_cases h_eq : x = n
        · -- x = n case: use x instead of n to avoid substitution issues
          rw [h_eq]
          have h_ne_rT : L.rA n ≠ L.rT := by
            unfold Layout.rA Layout.rT; omega
          calc
            s₃.nreg (L.rA n) = s₂.nreg (L.rA n) := h_nreg_unch L.rT L.rT L.rSZ (L.rA n) h_ne_rT s₂
            _ = s₁.nreg L.rT + s₁.nreg (L.rS 0) := by
              rw [hs₂_def]; simp [Prim.exec]
            _ = L.base d n + 0 := by rw [h_rT₁, h_nreg_rS0, hS0']
            _ = L.base d n := by simp
        · have hx_lt_n : x < n := Nat.lt_of_le_of_ne hx_le h_eq
          have h_ne : L.rA x ≠ L.rA n := by
            unfold Layout.rA; omega
          have h_ne_rA_rT : L.rA x ≠ L.rT := by
            unfold Layout.rA Layout.rT; omega
          calc
            s₃.nreg (L.rA x) = s₂.nreg (L.rA x) := h_nreg_unch L.rT L.rT L.rSZ (L.rA x) h_ne_rA_rT s₂
            _ = s₁.nreg (L.rA x) := h_nreg_unch (L.rA n) L.rT (L.rS 0) (L.rA x) h_ne s₁
            _ = L.base d x := h_rA₁ x hx_lt_n
      have h_rT₃ : s₃.nreg L.rT = L.base d (n + 1) := by
        have h_ne_rT_rA : L.rT ≠ L.rA n := by
          unfold Layout.rT Layout.rA; omega
        have h_ne_rA_rSZ : L.rA n ≠ L.rSZ := by
          unfold Layout.rA Layout.rSZ; omega
        calc
          s₃.nreg L.rT = s₂.nreg L.rT + s₂.nreg L.rSZ := by
            rw [hs₃_def]; simp [Prim.exec]
          _ = s₁.nreg L.rT + s₁.nreg L.rSZ := by
            rw [hs₂_def, Prim.exec]
            simp [h_ne_rT_rA]
            exact Function.update_of_ne h_ne_rA_rSZ.symm (s₁.nreg L.rT + s₁.nreg (L.rS 0)) s₁.nreg
          _ = L.base d n + s'.nreg L.rSZ := by rw [h_rT₁, h_nreg_rSZ]
          _ = L.base d n + asz d := by rw [hSZ']
          _ = (L.NS + 1 + n * asz d) + asz d := rfl
          _ = L.NS + 1 + (n + 1) * asz d := by ring
          _ = L.base d (n + 1) := rfl
      have h_other₃ : ∀ r, r ≠ L.rT → (∀ x < n + 1, r ≠ L.rA x) → s₃.nreg r = s'.nreg r := by
        intro r hr_ne_rT hr_ne_rA
        have hr_ne_rA_n : r ≠ L.rA n := by
          intro heq; apply hr_ne_rA n (by omega); exact heq
        have h_r_eq_s : s₁.nreg r = s'.nreg r := by
          apply h_other₁ r hr_ne_rT
          intro a ha
          apply hr_ne_rA a
          omega
        calc
          s₃.nreg r = s₂.nreg r := h_nreg_unch L.rT L.rT L.rSZ r hr_ne_rT s₂
          _ = s₁.nreg r := h_nreg_unch (L.rA n) L.rT (L.rS 0) r hr_ne_rA_n s₁
          _ = s'.nreg r := h_r_eq_s
      refine ⟨s₃, h_total, h_pc₃, h_mem₃, h_draws₃, h_rounds₃, h_pts₃, h_rA₃, h_rT₃, h_other₃⟩
  exact h_main k s hSZ hS0 hT

/-- The loop of `setup` from the count `d - m`: `m` more rounds bring `SZ` to `d²` and `T` to `d`. -/
theorem AdversarialBco.Poly.Mach.exec_setupLoop_aux {d m : ℕ} (L : Layout) (w : World d) (s : State d)
    (h0 : s.nreg 0 = d) (h1 : s.nreg (L.rS 1) = 1) (hSZ : s.nreg L.rSZ = (d - m) * d) (hT : s.nreg L.rT = d - m)
    (hm : m ≤ d) :
    ∃ s', Exec w (.whileN L.rT 0 (.seq (.prim (.nadd L.rSZ L.rSZ 0)) (.prim (.nadd L.rT L.rT (L.rS 1))))) s
        (4 * m + 2) s' ∧ s'.pc = s.pc ∧ s'.mem = s.mem ∧ s'.draws = s.draws ∧ s'.rounds = s.rounds ∧
      s'.pts = s.pts ∧ s'.nreg L.rSZ = d * d ∧ s'.nreg L.rT = d ∧
      (∀ r, r ≠ L.rSZ → r ≠ L.rT → s'.nreg r = s.nreg r) := by
  induction m generalizing d L w s with
  | zero =>
    have hcond : ¬ condN s L.rT 0 := by
      unfold condN
      rw [hT, h0]
      have : d - 0 = d := Nat.sub_zero d
      rw [this]
      exact Nat.not_lt.mpr (le_refl d)
    refine ⟨s, Exec.whileN_f hcond, rfl, rfl, rfl, rfl, rfl, ?_, ?_, fun r hr1 hr2 => rfl⟩
    · rw [hSZ]; simp
    · rw [hT]; simp
  | succ m ih =>
    have hm' : m ≤ d := by omega
    have hcond : condN s L.rT 0 := by
      unfold condN
      rw [hT, h0]
      have hpos : 0 < d - m := Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hm)
      omega
    have hne_rT_rSZ : L.rT ≠ L.rSZ := by
      unfold Layout.rT Layout.rSZ; omega
    have hne_rS1_rSZ : L.rS 1 ≠ L.rSZ := by
      unfold Layout.rS Layout.rSZ; omega
    have hne_rS1_rT : L.rS 1 ≠ L.rT := by
      unfold Layout.rS Layout.rT; omega
    set s1 := Prim.exec w s (.nadd L.rSZ L.rSZ 0) with hs1
    set s2 := Prim.exec w s1 (.nadd L.rT L.rT (L.rS 1)) with hs2
    have hbody : Exec w (.seq (.prim (.nadd L.rSZ L.rSZ 0)) (.prim (.nadd L.rT L.rT (L.rS 1)))) s 2 s2 := by
      refine Exec.seq (Exec.prim _ _) (Exec.prim _ _)
    have hs1_nreg_rSZ : s1.nreg L.rSZ = (d - m) * d := by
      rw [hs1, Prim.exec]
      simp
      rw [hSZ, h0]
      have hle : m + 1 ≤ d := hm
      have : (d - (m + 1)) * d + d = (d - m) * d := by
        calc
          (d - (m + 1)) * d + d = ((d - (m + 1)) + 1) * d := by ring
          _ = (d - m) * d := by
            have h : d - (m + 1) + 1 = d - m := by omega
            rw [h]
      rw [this]
    have hs1_nreg_rT : s1.nreg L.rT = d - (m + 1) := by
      rw [hs1, Prim.exec]
      simp [hne_rT_rSZ, hT]
    have hs2_nreg_rSZ : s2.nreg L.rSZ = (d - m) * d := by
      rw [hs2, Prim.exec]
      simp [hne_rT_rSZ.symm]
      rw [hs1_nreg_rSZ]
    have hs2_nreg_rT : s2.nreg L.rT = d - m := by
      rw [hs2, Prim.exec]
      simp
      rw [hs1_nreg_rT]
      have h1_s1 : s1.nreg (L.rS 1) = 1 := by
        rw [hs1, Prim.exec]
        simp [hne_rS1_rSZ, h1]
      rw [h1_s1]
      omega
    have h1_s2 : s2.nreg (L.rS 1) = 1 := by
      have h_rest_s2 : ∀ r, r ≠ L.rT → s2.nreg r = s1.nreg r := by
        intro r hr
        rw [hs2, Prim.exec]
        simp [hr]
      rw [h_rest_s2 (L.rS 1) hne_rS1_rT]
      rw [hs1, Prim.exec]
      simp [hne_rS1_rSZ, h1]
    have h_rest_s1 : ∀ r, r ≠ L.rSZ → s1.nreg r = s.nreg r := by
      intro r hr
      rw [hs1, Prim.exec]
      simp [hr]
    have h_rest_s2 : ∀ r, r ≠ L.rT → s2.nreg r = s1.nreg r := by
      intro r hr
      rw [hs2, Prim.exec]
      simp [hr]
    have h_rest : ∀ r, r ≠ L.rSZ → r ≠ L.rT → s2.nreg r = s.nreg r := by
      intro r hr1 hr2
      rw [h_rest_s2 r hr2, h_rest_s1 r hr1]
    obtain ⟨s', hExec, hpc, hmem, hdraws, hrounds, hpts, hSZ', hT', hRest'⟩ :=
      ih L w s2 h0 h1_s2 hs2_nreg_rSZ hs2_nreg_rT hm'
    have htotal : 2 + 2 + (4 * m + 2) = 4 * (m + 1) + 2 := by ring
    have hExec_total : Exec w (.whileN L.rT 0 (.seq (.prim (.nadd L.rSZ L.rSZ 0)) (.prim (.nadd L.rT L.rT (L.rS 1)))))
        s (4 * (m + 1) + 2) s' := by
      rw [← htotal]
      exact Exec.whileN_t hcond hbody hExec
    have hpc' : s'.pc = s.pc := by
      rw [hpc, hs2, hs1]
      simp [Prim.exec]
    have hmem' : s'.mem = s.mem := by
      rw [hmem, hs2, hs1]
      simp [Prim.exec]
    have hdraws' : s'.draws = s.draws := by
      rw [hdraws, hs2, hs1]
      simp [Prim.exec]
    have hrounds' : s'.rounds = s.rounds := by
      rw [hrounds, hs2, hs1]
      simp [Prim.exec]
    have hpts' : s'.pts = s.pts := by
      rw [hpts, hs2, hs1]
      simp [Prim.exec]
    refine ⟨s', hExec_total, hpc', hmem', hdraws', hrounds', hpts', hSZ', hT', ?_⟩
    intro r hr1 hr2
    rw [hRest' r hr1 hr2, h_rest r hr1 hr2]

/-- The loop of `setup` that computes `SZ = d²`, in `4 d + 2` steps. -/
theorem AdversarialBco.Poly.Mach.exec_setupLoop {d : ℕ} (L : Layout) (w : World d) (s : State d)
    (h0 : s.nreg 0 = d) (h1 : s.nreg (L.rS 1) = 1) (hSZ : s.nreg L.rSZ = 0) (hT : s.nreg L.rT = 0) :
    ∃ s', Exec w (.whileN L.rT 0 (.seq (.prim (.nadd L.rSZ L.rSZ 0)) (.prim (.nadd L.rT L.rT (L.rS 1))))) s
        (4 * d + 2) s' ∧ s'.pc = s.pc ∧ s'.mem = s.mem ∧ s'.draws = s.draws ∧ s'.rounds = s.rounds ∧
      s'.pts = s.pts ∧ s'.nreg L.rSZ = d * d ∧ s'.nreg L.rT = d ∧
      (∀ r, r ≠ L.rSZ → r ≠ L.rT → s'.nreg r = s.nreg r) := by
  have hm : d ≤ d := le_refl d
  have hSZ' : s.nreg L.rSZ = (d - d) * d := by
    rw [hSZ]; simp
  have hT' : s.nreg L.rT = d - d := by
    rw [hT]; simp
  exact exec_setupLoop_aux L w s h0 h1 hSZ' hT' hm

/-- The setup represents the initial environment, in `NS + 2 NA + 4 d + 7` steps. -/
theorem AdversarialBco.Poly.Mach.setup_rep {d : ℕ} (L : Layout) (hNN : 2 ≤ L.NN) (hNS : 3 ≤ L.NS)
    (w : World d) (n : ℕ) (r0 R0 δ : ℝ) :
    ∃ s, Exec w (setup L) (init d n r0 R0 δ) (L.NS + 2 * L.NA + 4 * d + 7) s ∧ Rep L (Env.init d n r0 R0 δ) s := by
  set s0 := init d n r0 R0 δ with hs0
  let s1 : State d := { s0 with nreg := Function.update s0.nreg L.rZ L.NS }
  obtain ⟨s2, e2, -, m2, dr2, ro2, pt2, rs2, oth2⟩ := exec_setRS L w L.NS s1
  let s3 : State d := { s2 with nreg := Function.update s2.nreg L.rSZ 0 }
  let s4 : State d := { s3 with nreg := Function.update s3.nreg L.rT 0 }
  have n42 : ∀ r, r ≠ L.rSZ → r ≠ L.rT → s4.nreg r = s2.nreg r := fun r h1 h2 => by
    show Function.update (Function.update s2.nreg L.rSZ 0) L.rT 0 r = _
    rw [Function.update_of_ne h2, Function.update_of_ne h1]
  have n4 : ∀ r, r < L.NN → s4.nreg r = s0.nreg r := fun r hr => by
    rw [n42 r (by unfold Layout.rSZ; omega) (by unfold Layout.rT; omega),
      oth2 r (fun x _ => by unfold Layout.rS; omega)]
    show Function.update s0.nreg L.rZ L.NS r = s0.nreg r
    rw [Function.update_of_ne (by unfold Layout.rZ; omega)]
  have nS : ∀ x < L.NS, s4.nreg (L.rS x) = x := fun x hx => by
    rw [n42 _ (by unfold Layout.rS Layout.rSZ; omega) (by unfold Layout.rS Layout.rT; omega)]; exact rs2 x hx
  have a0 : s4.nreg 0 = d := by rw [n4 0 (by omega)]; rfl
  obtain ⟨s5, e5, -, m5, dr5, ro5, pt5, sz5, t5, oth5⟩ :=
    exec_setupLoop L w s4 a0 (nS 1 (by omega)) (by simp [s4, s3, Layout.rT, Layout.rSZ]) (by simp [s4])
  let s6 : State d := { s5 with nreg := Function.update s5.nreg L.rSZ (s5.nreg L.rSZ + s5.nreg 0) }
  let s7 : State d := { s6 with nreg := Function.update s6.nreg L.rT (L.NS + 1) }
  have b0 : s5.nreg 0 = d := by
    rw [oth5 0 (by unfold Layout.rSZ; omega) (by unfold Layout.rT; omega), a0]
  have c7 : ∀ r, r ≠ L.rSZ → r ≠ L.rT → s7.nreg r = s4.nreg r := fun r h1 h2 => by
    show Function.update (Function.update s5.nreg L.rSZ (s5.nreg L.rSZ + s5.nreg 0)) L.rT (L.NS + 1) r = _
    rw [Function.update_of_ne h2, Function.update_of_ne h1]; exact oth5 r h1 h2
  have hTSZ : L.rT ≠ L.rSZ := by unfold Layout.rT Layout.rSZ; omega
  obtain ⟨s8, e8, -, m8, dr8, ro8, pt8, ra8, -, oth8⟩ := exec_setRA L w (by omega) L.NA s7
    (by
      show Function.update (Function.update s5.nreg L.rSZ (s5.nreg L.rSZ + s5.nreg 0)) L.rT (L.NS + 1) L.rSZ = _
      rw [Function.update_of_ne hTSZ.symm, Function.update_self, sz5, b0]; rfl)
    (by
      rw [c7 _ (by unfold Layout.rS Layout.rSZ; omega) (by unfold Layout.rS Layout.rT; omega)]
      exact nS 0 (by omega))
    (by show Function.update (Function.update s5.nreg L.rSZ (s5.nreg L.rSZ + s5.nreg 0)) L.rT (L.NS + 1) L.rT = _
        rw [Function.update_self])
  refine ⟨s8, ?_, ?_⟩
  · have h := Exec.seq (Exec.prim (w := w) (.nconst L.rZ L.NS) s0) (Exec.seq e2 (Exec.seq
      (Exec.prim (w := w) (.nconst L.rSZ 0) s2) (Exec.seq (Exec.prim (w := w) (.nconst L.rT 0) s3)
        (Exec.seq e5 (Exec.seq (Exec.prim (w := w) (.nadd L.rSZ L.rSZ 0) s5)
          (Exec.seq (Exec.prim (w := w) (.nconst L.rT (L.NS + 1)) s6) e8))))))
    have hk : 1 + (L.NS + (1 + (1 + (4 * d + 2 + (1 + (1 + 2 * L.NA)))))) = L.NS + 2 * L.NA + 4 * d + 7 := by
      ring
    rw [hk] at h
    exact h
  · have mem8 : s8.mem = s0.mem := by rw [m8]; show s5.mem = _; rw [m5]; show s2.mem = _; rw [m2]
    have n8 : ∀ r, r ≠ L.rSZ → r ≠ L.rT → (∀ a < L.NA, r ≠ L.rA a) → s8.nreg r = s4.nreg r :=
      fun r h1 h2 h3 => by rw [oth8 r h2 h3, c7 r h1 h2]
    refine ⟨fun i hi => ?_, ?_, fun x hx => ?_, fun a ha => ra8 a ha, fun x hx => ?_, ?_, fun a _ k _ => ?_, ?_, ?_,
      ?_⟩
    · rw [n8 i (by unfold Layout.rSZ; omega) (by unfold Layout.rT; omega)
        (fun a _ => by unfold Layout.rA; omega), n4 i hi]; rfl
    · rw [n8 _ (by unfold Layout.rZ Layout.rSZ; omega) (by unfold Layout.rZ Layout.rT; omega)
        (fun a _ => by unfold Layout.rZ Layout.rA; omega),
        n42 _ (by unfold Layout.rZ Layout.rSZ; omega) (by unfold Layout.rZ Layout.rT; omega),
        oth2 _ (fun x _ => by unfold Layout.rS Layout.rZ; omega)]
      show Function.update s0.nreg L.rZ L.NS L.rZ = _
      rw [Function.update_self]
    · rw [n8 _ (by unfold Layout.rS Layout.rSZ; omega) (by unfold Layout.rS Layout.rT; omega)
        (fun a _ => by unfold Layout.rS Layout.rA; omega)]
      exact nS x hx
    · rw [mem8]; rfl
    · rw [mem8]; simp only [s0, init]; simp [show L.NS ≠ 0 by omega, show L.NS ≠ 1 by omega,
        show L.NS ≠ 2 by omega]
    · rw [mem8]; simp only [s0, init, Env.init, Layout.base]
      simp [show L.NS + 1 + a * asz d + k ≠ 1 by omega,
        show L.NS + 1 + a * asz d + k ≠ 2 by omega]
    · rw [dr8]; show s5.draws = _; rw [dr5]; show s2.draws = _; rw [dr2]; rfl
    · rw [ro8]; show s5.rounds = _; rw [ro5]; show s2.rounds = _; rw [ro2]; rfl
    · rw [pt8]; show s5.pts = _; rw [pt5]; show s2.pts = _; rw [pt2]; rfl
