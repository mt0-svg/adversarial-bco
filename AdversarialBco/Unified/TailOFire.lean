/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Unified.TailOPar
public import AdversarialBco.Bit.Transfer.XBLFire

@[expose] public section

/-!
# R12's new epoch at BL-O's PARAM

The command `xfire` of R12's new epoch (Bit/Transfer/XBLFire.lean) at `cfg.par = parN ne d n`, `1 ≤ ne`, with the
constants `64`, `2`. The proof reads PARAM only through `A₀'`, `B₀'` on the grid `2^{-p}` (PARAM rounds them there),
which holds at `parN` as at `par d n = parN (Ne d n) d n`.
-/

namespace AdversarialBco.Unified.ProgO.TailD

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP AdversarialBco.Bit.RQ Matrix
open AdversarialBco.Bit AdversarialBco.Bit.Transfer AdversarialBco.Bit.Transfer.BLM
open AdversarialBco.Unified.BLO (parN)

variable {d : ℕ}

theorem parN_onG_A0 (ne d n : ℕ) : OnG (parN ne d n).p (parN ne d n).A0 := onG_rnd_s _ _

theorem parN_onG_B0 (ne d n : ℕ) : OnG (parN ne d n).p (parN ne d n).B0 := onG_rnd_s _ _

set_option maxHeartbeats 4000000 in
/-- **`FireO` holds**: R12's new epoch at `parN ne d n`. -/
theorem fireO_holds : FireO := by
  refine ⟨xfire, 64, 2, ?_⟩
  intro d L X ℓa ℓ n m K0 E t ne cfg st σ hd hn _ hpar hL hlay hI hCl hCa
  have hsq : d * d + d + E + 1 ≤ (d + E + 1) ^ 2 := by
    have h2 : (d + E + 1) ^ 2 = d * d + (2 * d * E + E * E + 2 * d + 2 * E + 1) := by ring
    omega
  have hE : E < ℓ := by omega
  have hdd : d * d < 2 ^ ℓa := by omega
  obtain ⟨hS, hN, hAr⟩ := id hlay
  simp only [oE, rEE, aWE] at hS hN hAr
  obtain ⟨r0, -, -, r3, -, -, -, -⟩ := hI.regs
  have c0 : σ.sc sZ = 0 := hI.consts.1
  have p9 : σ.sc sA0 = qn cfg.par.p cfg.par.A0 := hI.par.2.2.2.2.2.2.2.2.2.1
  have p10 : σ.sc sB0 = qn cfg.par.p cfg.par.B0 := hI.par.2.2.2.2.2.2.2.2.2.2
  have hE0 : (0 : ℤ) ≤ 2 ^ E := by positivity
  have ba : |qn cfg.par.p cfg.par.A0| ≤ 2 ^ E := by
    obtain ⟨z, hz, hzE⟩ := hI.bnd.1 sA0 (by decide)
    have : z = qn cfg.par.p cfg.par.A0 := by exact_mod_cast hz.symm.trans p9
    rwa [← this]
  have bb : |qn cfg.par.p cfg.par.B0| ≤ 2 ^ E := by
    obtain ⟨z, hz, hzE⟩ := hI.bnd.1 sB0 (by decide)
    have : z = qn cfg.par.p cfg.par.B0 := by exact_mod_cast hz.symm.trans p10
    rwa [← this]
  refine XV.mono (K := (14 * (d * d) + 21 * d + 23) + epochUnits d)
    (XV.seq (XV.fireZ hL hlay r0 r3 c0 hE hdd) fun σ1 ⟨z1, k1, l1, d1, F1⟩ => ?_) (by unfold epochUnits; omega)
    fun _ h => h
  have n1 : ∀ j < 8, σ1.nat j = σ.nat j := fun j hj => F1.1 j fun h => by simp only [NCom] at h; omega
  have s1 : ∀ y < 128, y ≠ sK → y ≠ sL → σ1.sc y = σ.sc y := fun y hy h h' => F1.2.1 y (not_sCom hy h h')
  refine XV.mono (XV.epoch (a0 := qn cfg.par.p cfg.par.A0) (b0 := qn cfg.par.p cfg.par.B0) (E := E) hL (by omega)
    (by omega) (by omega) (by rw [n1 _ (by decide), r0]) (by rw [n1 _ (by decide), r3])
    (by rw [s1 _ (by decide) (by decide) (by decide), c0]) (by rw [s1 _ (by decide) (by decide) (by decide), p9])
    (by rw [s1 _ (by decide) (by decide) (by decide), p10]) ba bb hE) le_rfl
    fun σ2 ⟨f2, m2, dA, dB, d2, F2⟩ => ?_
  have s2 : ∀ y < 128, y ≠ sFirst → y ≠ sDmu → σ2.sc y = σ1.sc y := fun y hy h h' =>
    F2.2.1 y fun e => by rcases e with e | e | e <;> [exact h e; exact h' e; omega]
  have a2 : ∀ b k, ¬ AE (d := d) b k → σ2.arr b k = σ1.arr b k := fun b k h => F2.2.2.1 b k h
  have hF : FrameA SEnd NEnd AEnd σ σ2 := by
    refine (F1.mono (fun y h => ?_) (fun j h => h.1) (fun b c h => ?_)).trans
      (F2.mono (fun y h => ?_) (fun j h => ?_) (fun b c h => ?_))
    · rcases h with h | h | h
      exacts [Or.inr (Or.inr (Or.inl h)), Or.inr (Or.inr (Or.inr (Or.inl h))),
        Or.inr (Or.inr (Or.inr (Or.inr (by simp only [nSP]; omega))))]
    · show aMu ≤ b
      rcases h with ⟨h, -⟩ | ⟨h | h, -⟩ | ⟨h | h, -⟩ <;> subst h <;> decide
    · rcases h with h | h | h
      exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inr (Or.inr (by simp only [nSP]; omega))))]
    · show 8 ≤ j
      rcases h with h | h | h <;> omega
    · show aMu ≤ b
      rcases h with ⟨h | h, -⟩ <;> subst h <;> decide
  have hA0 : OnG cfg.par.p cfg.par.A0 := by rw [hpar]; exact parN_onG_A0 ne d n
  have hB0 : OnG cfg.par.p cfg.par.B0 := by rw [hpar]; exact parN_onG_B0 ne d n
  obtain ⟨g0, q0⟩ := onG_zero cfg.par.p
  have nAE : ∀ b k, b ≠ aA → b ≠ aB → ¬ AE (d := d) b k := fun b k h h' e => by
    rcases e.1 with e | e
    exacts [h e, h' e]
  have hst : StRep σ2 cfg.par.p (init cfg.par d) := by
    refine ⟨by rw [f2]; simp [init], ⟨1, one_pos,
      by rw [m2]; simp, fun j => ⟨0, ?_, by simp [init]⟩⟩, fun i j => ?_, fun i j => ?_, fun j => ?_, ?_,
      fun j => ?_, ?_⟩
    · rw [a2 _ _ (nAE _ _ (by decide) (by decide)), z1 aMu j (Or.inl ⟨rfl, j.2⟩)]; simp
    · show σ2.arr aA (d * i + j) = qn cfg.par.p ((cfg.par.A0 • 1 : Matrix (Fin d) (Fin d) ℚ) i j) ∧ _
      refine ⟨?_, onG_smul_one _ _ hA0 i j⟩
      rw [qn_smul_one]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        have := dA i i.2
        rwa [show 0 + (d + 1) * (i : ℕ) = d * i + i by ring] at this
      · rw [if_neg hij, a2 _ _ (fun h => hij ((diag_iff i j).1 h.2)),
          z1 aA _ (Or.inr (Or.inl ⟨Or.inl rfl, cell_lt i j⟩))]
        simp
    · show σ2.arr aB (d * i + j) = qn cfg.par.p ((cfg.par.B0 • 1 : Matrix (Fin d) (Fin d) ℚ) i j) ∧ _
      refine ⟨?_, onG_smul_one _ _ hB0 i j⟩
      rw [qn_smul_one]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        have := dB i i.2
        rwa [show 0 + (d + 1) * (i : ℕ) = d * i + i by ring] at this
      · rw [if_neg hij, a2 _ _ (fun h => hij ((diag_iff i j).1 h.2)),
          z1 aB _ (Or.inr (Or.inl ⟨Or.inr rfl, cell_lt i j⟩))]
        simp
    · show σ2.arr ab j = qn cfg.par.p ((0 : Fin d → ℚ) j) ∧ OnG cfg.par.p ((0 : Fin d → ℚ) j)
      rw [Pi.zero_apply, q0, a2 _ _ (nAE _ _ (by decide) (by decide)), z1 ab j (Or.inr (Or.inr ⟨Or.inl rfl, j.2⟩))]
      exact ⟨by simp, g0⟩
    · show σ2.sc sK = qn cfg.par.p 0 ∧ OnG cfg.par.p 0
      rw [q0, s2 _ (by decide) (by decide) (by decide), k1]
      exact ⟨by simp, g0⟩
    · show σ2.arr aG j = qn cfg.par.p ((0 : Fin d → ℚ) j) ∧ OnG cfg.par.p ((0 : Fin d → ℚ) j)
      rw [Pi.zero_apply, q0, a2 _ _ (nAE _ _ (by decide) (by decide)), z1 aG j (Or.inr (Or.inr ⟨Or.inr rfl, j.2⟩))]
      exact ⟨by simp, g0⟩
    · show σ2.sc sL = qn cfg.par.p 0 ∧ OnG cfg.par.p 0
      rw [q0, s2 _ (by decide) (by decide) (by decide), l1]
      exact ⟨by simp, g0⟩
  refine ⟨BLInv.setSt hI hF (by rw [d2, d1]) hst (fun y hy => ?_) (fun a ha k hk => ?_), by rw [d2, d1], hF⟩
  · simp only [nSP] at hy
    by_cases e1 : y = sFirst
    · subst e1
      exact Or.inr ⟨1, by rw [f2]; simp, one_le_two_pow E⟩
    by_cases e2 : y = sDmu
    · subst e2
      exact Or.inr ⟨1, by rw [m2]; simp, one_le_two_pow E⟩
    by_cases e3 : y = sK
    · subst e3
      exact Or.inr ⟨0, by rw [s2 _ (by decide) (by decide) (by decide), k1]; simp, by simp⟩
    by_cases e4 : y = sL
    · subst e4
      exact Or.inr ⟨0, by rw [s2 _ (by decide) (by decide) (by decide), l1]; simp, by simp⟩
    exact Or.inl (by rw [s2 y (by omega) e1 e2, s1 y (by omega) e3 e4])
  · by_cases hAE : AE (d := d) a k
    · obtain ⟨ha' | ha', j, hj, rfl⟩ := hAE
      · subst ha'; exact Or.inr ⟨_, dA j hj, ba⟩
      · subst ha'; exact Or.inr ⟨_, dB j hj, bb⟩
    rw [a2 _ _ hAE]
    by_cases hZ : AFz d a k
    · exact Or.inr ⟨0, by rw [z1 a k hZ]; simp, by simp⟩
    · exact Or.inl (F1.2.2.1 a k hZ)

end AdversarialBco.Unified.ProgO.TailD
