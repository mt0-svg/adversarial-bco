/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLRt
public import AdversarialBco.Bit.Transfer.XBLR9b
public import AdversarialBco.Bit.Transfer.XBLTailSpec

@[expose] public section

/-!
# The head of BL's round in BL's terms

The values of R5 to R9 of `step` in mode `run` (Bit/Transfer/XBLStep.lean) as the integers the machine computes, once
the state and the draw are fractions of integers (`Q = 2^p`, `F = 2^pF`, `G = 2^(2 p_B)`, `μ' = μ̂/D_μ`): the numerators
of `A'`, `B'`, `s5` (`head_r8`), of `b'`, `k'`, `G'`, `l'` (`head_r9`). The point `w_μ` is `head_wmuO`
(Unified/TailOFld.lean).
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit.BLP Matrix

variable {d : ℕ}

/-- A point on the grid is its numerator over `2^k`. -/
theorem eq_of_onG {k : ℕ} {x : ℚ} {z : ℤ} (hx : OnG k x) (hz : qn k x = z) : x = (z : ℚ) / ((2 ^ k : ℤ) : ℚ) := by
  unfold OnG at hx
  rw [hz] at hx
  push_cast
  rw [hx]
  field_simp

section Head8

variable (cfg : Cfg d) (st : St d) (ζ : ℚ) (obs : ℤ)

/-- R8 and R13's `s5` in the integers of the second line. -/
theorem head_r8 (Q F G kN yh eh nh : ℤ) (Γ : Fin d → ℤ) (v : ℕ → ℤ) (Ah Bh : Matrix (Fin d) (Fin d) ℤ)
    (hp : 1 ≤ cfg.par.p) (hQ : Q = 2 ^ cfg.par.p) (hF : 0 < F) (hG : 0 < G)
    (h0 : v 0 = yh) (h1 : v 1 = kN * yh) (h2 : v 2 = F * Q) (h3 : v 3 = F * Q - kN * yh) (h4 : v 4 = G * G)
    (h5 : v 5 = (F * Q - kN * yh) * (G * G) + kN * yh * (Γ ⬝ᵥ Γ)) (h7 : v 7 = F * Q * (G * G))
    (hY : rY cfg st (fun i => (Γ i : ℚ) / G) ζ obs = (yh : ℚ) / Q)
    (hc : rc cfg st (fun i => (Γ i : ℚ) / G) ζ obs = (kN : ℚ) / F * ((yh : ℚ) / Q))
    (hη : cfg.par.eta = (eh : ℚ) / F) (hν : cfg.par.nu = (nh : ℚ) / F)
    (hA : st.A = Matrix.of fun a b => (Ah a b : ℚ) / Q) (hB : st.B = Matrix.of fun a b => (Bh a b : ℚ) / Q)
    (ha : ¬ ra cfg st (fun i => (Γ i : ℚ) / G) ζ obs < 1 / 2)
    (hq : ¬ rq cfg st (fun i => (Γ i : ℚ) / G) ζ obs < 1 / 2) :
    (∀ i j, OnG cfg.par.p (rA' cfg st (fun i => (Γ i : ℚ) / G) ζ obs i j) ∧
      qn cfg.par.p (rA' cfg st (fun i => (Γ i : ℚ) / G) ζ obs i j) =
        rndZ (w2 Q F eh nh v 4 * Ah i j * (G * G) - w2 Q F eh nh v 11 * (Ah *ᵥ Γ) i * Γ j) (Q * Q * (G * G)) Q) ∧
    (∀ i j, OnG cfg.par.p (rB' cfg st (fun i => (Γ i : ℚ) / G) ζ obs i j) ∧
      qn cfg.par.p (rB' cfg st (fun i => (Γ i : ℚ) / G) ζ obs i j) =
        rndZ (w2 Q F eh nh v 6 * Bh i j * (G * G) + w2 Q F eh nh v 13 * (Bh *ᵥ Γ) i * Γ j) (Q * Q * (G * G)) Q) ∧
    rs5 cfg st (fun i => (Γ i : ℚ) / G) ζ obs = (w2 Q F eh nh v 2 : ℚ) / ((2 ^ cfg.par.p : ℤ) : ℚ) ∧
    0 < w2 Q F eh nh v 6 ∧ 0 < w2 Q F eh nh v 8 ∧ v 2 ≤ 2 * v 3 ∧ v 7 ≤ 2 * v 5 := by
  obtain ⟨⟨o1, q1⟩, ⟨o3, q3⟩, ⟨o8, q8⟩, f11, f13, f2, p6, p8, hv23, hv75⟩ :=
    r8s_pure cfg.par.p hp Q F G kN yh eh nh Γ v hQ hF hG h0 h1 h2 h3 h4 h5 h7 hc rfl rfl ha hq
  have hQ' : ((2 ^ cfg.par.p : ℤ) : ℚ) = (Q : ℚ) := by rw [hQ]
  set ξ : Fin d → ℚ := fun i => (Γ i : ℚ) / G with hξ
  have e1 : rs1 cfg st ξ ζ obs = (w2 Q F eh nh v 4 : ℚ) / Q := by rw [← hQ']; exact eq_of_onG o1 q1
  have e3 : rs3 cfg st ξ ζ obs = (w2 Q F eh nh v 6 : ℚ) / Q := by rw [← hQ']; exact eq_of_onG o3 q3
  have e2 : rs2 cfg st ξ ζ obs = (w2 Q F eh nh v 11 : ℚ) / Q := by
    rw [← hQ']; exact eq_of_onG (onG_rnd_s _ _) f11
  have e4 : rs4 cfg st ξ ζ obs = (w2 Q F eh nh v 13 : ℚ) / Q := by
    rw [← hQ']; exact eq_of_onG (onG_rnd_s _ _) f13
  refine ⟨fun i j => ?_, fun i j => ?_, ?_, p6, p8, hv23, hv75⟩
  · have := r8_Aq cfg.par.p Q G (w2 Q F eh nh v 4) (w2 Q F eh nh v 11) Ah Γ hQ hG i j
    rw [rA', e1, e2, hA]
    exact this
  · have := r8_Bq cfg.par.p Q G (w2 Q F eh nh v 6) (w2 Q F eh nh v 13) Bh Γ hQ hG i j
    rw [rB', e3, e4, hB]
    exact this
  · have e5 : rs5 cfg st ξ ζ obs =
        rnd cfg.par.p ((eh : ℚ) / F * ((yh : ℚ) / Q) * ((nh : ℚ) / F) / rq cfg st ξ ζ obs) := by
      rw [rs5, hY, hη, hν]
    rw [e5]
    exact eq_of_onG (onG_rnd_s _ _) f2

end Head8

section Head9

variable (cfg : Cfg d) (st : St d) (ζ : ℚ) (obs : ℤ)

/-- R9 in the integers of the machine. -/
theorem head_r9 (Q F G D kN yh nh kh lh : ℤ) (Γ mu bh Gh : Fin d → ℤ) (Bh : Matrix (Fin d) (Fin d) ℤ)
    (hQ : Q = 2 ^ cfg.par.p) (hF : 0 < F) (hG : 0 < G) (hD : 0 < D)
    (hY : rY cfg st (fun i => (Γ i : ℚ) / G) ζ obs = (yh : ℚ) / Q)
    (hc : rc cfg st (fun i => (Γ i : ℚ) / G) ζ obs = (kN : ℚ) / F * ((yh : ℚ) / Q))
    (hν : cfg.par.nu = (nh : ℚ) / F) (hB : st.B = Matrix.of fun a b => (Bh a b : ℚ) / Q)
    (hb : st.b = fun k => (bh k : ℚ) / Q) (hk : st.k = (kh : ℚ) / Q) (hGo : ∀ j, OnG cfg.par.p (st.G j))
    (hGq : ∀ j, qn cfg.par.p (st.G j) = Gh j) (hl : st.l = (lh : ℚ) / Q)
    (hmu : st.mu = fun k => (mu k : ℚ) / D) :
    (∀ j, OnG cfg.par.p (rb' cfg st (fun i => (Γ i : ℚ) / G) ζ obs j) ∧
      qn cfg.par.p (rb' cfg st (fun i => (Γ i : ℚ) / G) ζ obs j) =
        bh j + rndZ (kN * yh * (((Bh *ᵥ Γ) ⬝ᵥ mu) * (Bh *ᵥ Γ) j - G * G * (Bh *ᵥ (Bhᵀ *ᵥ mu)) j))
          (F * Q * Q * Q * (G * G) * D) Q) ∧
    (OnG cfg.par.p (rk' cfg st (fun i => (Γ i : ℚ) / G) ζ obs) ∧
      qn cfg.par.p (rk' cfg st (fun i => (Γ i : ℚ) / G) ζ obs) =
        kh + rndZ (kN * yh * (((Bh *ᵥ Γ) ⬝ᵥ mu) * ((Bh *ᵥ Γ) ⬝ᵥ mu) - G * G * ((Bhᵀ *ᵥ mu) ⬝ᵥ (Bhᵀ *ᵥ mu))))
          (2 * (F * Q * Q * Q * (G * G) * D * D)) Q) ∧
    (∀ j, OnG cfg.par.p (rG' cfg st (fun i => (Γ i : ℚ) / G) ζ obs j) ∧
      qn cfg.par.p (rG' cfg st (fun i => (Γ i : ℚ) / G) ζ obs j) =
        Gh j + rndZ (yh * nh * (Bh *ᵥ Γ) j) (F * Q * Q * G) Q) ∧
    (OnG cfg.par.p (rl' cfg st (fun i => (Γ i : ℚ) / G) ζ obs) ∧
      qn cfg.par.p (rl' cfg st (fun i => (Γ i : ℚ) / G) ζ obs) =
        lh + rndZ ((fun j => rndZ (yh * nh * (Bh *ᵥ Γ) j) (F * Q * Q * G) Q) ⬝ᵥ mu) (Q * D) Q) := by
  have hQ' : ((2 ^ cfg.par.p : ℤ) : ℚ) = (Q : ℚ) := by rw [hQ]
  set ξ : Fin d → ℚ := fun i => (Γ i : ℚ) / G with hξ
  have hg : ∀ j, OnG cfg.par.p (rg cfg st ξ ζ obs j) ∧
      qn cfg.par.p (rg cfg st ξ ζ obs j) = rndZ (yh * nh * (Bh *ᵥ Γ) j) (F * Q * Q * G) Q := fun j => by
    have := r9_gq cfg.par.p F Q G yh nh Bh Γ hQ hF hG j
    rw [rg, hY, hν, hB]
    exact ⟨this.1, by rw [this.2, rndZ]⟩
  have eg : rg cfg st ξ ζ obs = fun j => (rndZ (yh * nh * (Bh *ᵥ Γ) j) (F * Q * Q * G) Q : ℚ) / Q := by
    funext j; rw [← hQ']; exact eq_of_onG (hg j).1 (hg j).2
  refine ⟨fun j => ?_, ?_, fun j => ?_, ?_⟩
  · have := r9_bq cfg.par.p F Q G D kN yh Bh Γ mu bh hQ hF hG hD j
    rw [rb', hb, hc, hB, hmu]
    exact ⟨this.1, by rw [this.2, rndZ]⟩
  · have := r9_kq cfg.par.p F Q G D kN yh kh Bh Γ mu hQ hF hG hD
    have hV : 2 * F * Q * Q * Q * (G * G) * (D * D) = 2 * (F * Q * Q * Q * (G * G) * D * D) := by ring
    rw [hV] at this
    rw [rk', hk, hc, hB, hmu]
    exact ⟨this.1, by rw [this.2, rndZ]⟩
  · have h2 := qn_add_onG cfg.par.p (st.G j) (rg cfg st ξ ζ obs j) (hGo j) (hg j).1
    rw [rG', Pi.add_apply]
    exact ⟨h2.1, by rw [h2.2, hGq j, (hg j).2]⟩
  · have := r9_lq cfg.par.p Q D lh (fun j => rndZ (yh * nh * (Bh *ᵥ Γ) j) (F * Q * Q * G) Q) mu hQ hD
    rw [rl', hl, eg, hmu]
    exact ⟨this.1, by rw [this.2, rndZ]⟩

end Head9

end AdversarialBco.Bit.Transfer.BLM
