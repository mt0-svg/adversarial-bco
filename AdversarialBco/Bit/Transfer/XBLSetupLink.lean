/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.Transfer.XBLSetupParRun

@[expose] public section

/-!
# BL's setup on the machine: PARAM's values are the numerators of `BLInv`

The generic identities (one per rounded field: `qn` of the rounded rational is the integer formula of the program)
are proved generically; the second part instantiates them at `par d n`.
-/

namespace AdversarialBco.Bit.Transfer.BLM

open AdversarialBco AdversarialBco.Poly.Mach AdversarialBco.Bit AdversarialBco.Bit.BLP

/-! ## The generic identities -/

theorem qn_lam_gen (d q pF : ℕ) (hd : 1 ≤ d) (LeN : ℤ) (hL : LeN ≠ 0) :
    qn pF (rnd pF (1 / (725 * (d : ℚ) * ((LeN : ℚ) / 2 ^ q) ^ 2))) = lamI d LeN (2 ^ pF) (2 ^ q) := by
  set U := (2 ^ q * 2 ^ q : ℤ) with hU
  set V := (725 * (d : ℤ) * LeN ^ 2 : ℤ) with hVdef
  have hVpos : 0 < V := by
    rw [hVdef]
    have hd' : 0 < (d : ℤ) := by exact_mod_cast (Nat.one_pos.trans_le hd)
    have hsq : 0 < LeN ^ 2 := sq_pos_iff.mpr hL
    positivity
  have hx : 1 / (725 * (d : ℚ) * ((LeN : ℚ) / 2 ^ q) ^ 2) = ((U : ℤ) : ℚ) / ((V : ℤ) : ℚ) := by
    rw [hU, hVdef]
    push_cast
    have h2 : (2 ^ q : ℚ) ≠ 0 := by positivity
    have h725 : (725 : ℚ) ≠ 0 := by norm_num
    have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.one_pos.trans_le hd).ne'
    have hLeN : (LeN : ℚ) ≠ 0 := by exact_mod_cast hL
    field_simp [h2, h725, hd', hLeN]
  rw [hx]
  rw [qn_rnd_div pF U V hVpos]
  unfold lamI
  rw [hU, hVdef]
  congr 1
  ring

theorem qn_eta_gen (d n q pF : ℕ) (hn : 1 ≤ n) (LeN : ℤ) (hL : 0 < LeN) :
    qn pF (rnd pF (sqrtDn q d / ((LeN : ℚ) / 2 ^ q * sqrtDn q n))) =
      etaI (Nat.sqrt (d * 4 ^ q)) (Nat.sqrt (n * 4 ^ q)) LeN (2 ^ pF) (2 ^ q) := by
  set RD := Nat.sqrt (d * 4 ^ q) with hRD
  set RN := Nat.sqrt (n * 4 ^ q) with hRN
  have hRnpos : 0 < (RN : ℚ) := by
    have hpos : 0 < n * 4 ^ q := by
      have hnpos : 0 < n := by omega
      have h4pos : 0 < 4 ^ q := by positivity
      exact mul_pos hnpos h4pos
    have hsqrtpos : 0 < RN := by
      rw [hRN]
      exact (Nat.sqrt_pos.mpr hpos)
    exact_mod_cast hsqrtpos
  have hqpos : (2 ^ q : ℚ) ≠ 0 := by positivity
  have hVpos' : (LeN : ℚ) * (RN : ℚ) ≠ 0 := by
    have hL' : (0 : ℚ) < LeN := by exact_mod_cast hL
    positivity
  have hV : 0 < (LeN : ℤ) * (RN : ℤ) := by
    have hRnpos_int : 0 < (RN : ℤ) := by exact_mod_cast hRnpos
    nlinarith
  calc
    qn pF (rnd pF (sqrtDn q d / ((LeN : ℚ) / 2 ^ q * sqrtDn q n)))
        = qn pF (rnd pF (((RD : ℚ) / 2 ^ q) / (((LeN : ℚ) / 2 ^ q) * ((RN : ℚ) / 2 ^ q)))) := by
      simp [sqrtDn_nat, hRD, hRN]
    _ = qn pF (rnd pF (((RD : ℚ) / 2 ^ q) * ((2 ^ q : ℚ) ^ 2 / ((LeN : ℚ) * (RN : ℚ))))) := by
      field_simp [hVpos', hqpos]
    _ = qn pF (rnd pF (((RD : ℚ) * (2 ^ q : ℚ)) / ((LeN : ℚ) * (RN : ℚ)))) := by
      field_simp [hqpos]
    _ = qn pF (rnd pF (((RD * 2 ^ q : ℤ) : ℚ) / ((LeN * RN : ℤ) : ℚ))) := by
      push_cast
      ring
    _ = (2 * (RD * 2 ^ q : ℤ) * 2 ^ pF + LeN * RN) / (2 * (LeN * RN)) := by
      rw [qn_rnd_div pF (RD * 2 ^ q : ℤ) (LeN * RN : ℤ) hV]
    _ = etaI (Nat.sqrt (d * 4 ^ q)) (Nat.sqrt (n * 4 ^ q)) LeN (2 ^ pF) (2 ^ q) := by
      unfold etaI
      simp [hRD, hRN]

theorem qn_sig_gen (q pF : ℕ) (LeN : ℤ) (hL : 0 < LeN) :
    qn pF (rnd pF (1 / (8 * ((LeN : ℚ) / 2 ^ q)))) = sigI LeN (2 ^ pF) (2 ^ q) := by
  have hV : 0 < (8 * LeN : ℤ) := by
    nlinarith
  have h_eq : (1 : ℚ) / (8 * ((LeN : ℚ) / ((2 : ℚ) ^ q))) = ((2 ^ q : ℤ) : ℚ) / (8 * LeN : ℤ) := by
    push_cast
    field_simp
  rw [h_eq]
  rw [qn_rnd_div pF (2 ^ q : ℤ) (8 * LeN : ℤ) hV]
  unfold sigI
  ring

theorem qn_rho_gen (d q pF : ℕ) (LeN : ℤ) :
    qn pF (dn pF (1450 * (d : ℚ) ^ 2 * ((LeN : ℚ) / 2 ^ q) ^ 3)) = rhoI d LeN (2 ^ pF) (2 ^ q) := by
  have hV : 0 < ((2 : ℤ) ^ q) ^ 3 := by
    have h2 : 0 < (2 : ℤ) ^ q := pow_pos (by norm_num) q
    exact pow_pos h2 3
  have h_inner : 1450 * (d : ℚ) ^ 2 * ((LeN : ℚ) / 2 ^ q) ^ 3 = ((1450 * (d : ℤ) ^ 2 * LeN ^ 3 : ℤ) : ℚ) / ((2 : ℤ) ^ q) ^ 3 := by
    push_cast
    rw [div_pow, mul_div_assoc]
  rw [h_inner]
  have hqn := qn_dn_div pF (1450 * (d : ℤ) ^ 2 * LeN ^ 3) (((2 : ℤ) ^ q) ^ 3) hV
  have hLHS : qn pF (dn pF (((1450 * (d : ℤ) ^ 2 * LeN ^ 3 : ℤ) : ℚ) / (((2 : ℤ) ^ q) ^ 3 : ℚ))) = (1450 * (d : ℤ) ^ 2 * LeN ^ 3) * 2 ^ pF / ((2 : ℤ) ^ q) ^ 3 := by
    simpa using hqn
  rw [hLHS]
  unfold rhoI
  rfl

theorem qn_kapc_gen (pF : ℕ) (EN LN : ℤ) :
    qn pF (rnd pF ((EN : ℚ) / 2 ^ pF * ((LN : ℚ) / 2 ^ pF) / (4 * (1 - (LN : ℚ) / 2 ^ pF) ^ 2))) =
      kapI EN LN (2 ^ pF) := by
  let PF := (2 : ℤ) ^ pF
  have hPF_ne_zero : (PF : ℚ) ≠ 0 := by
    norm_cast
    exact pow_ne_zero pF (by norm_num : (2 : ℤ) ≠ 0)
  have hPF_eq : (PF : ℚ) = (2 : ℚ) ^ pF := by simp [PF]
  by_cases h : LN = PF
  · subst h
    have hzero : ((EN : ℚ) / (2 : ℚ) ^ pF * ((PF : ℚ) / (2 : ℚ) ^ pF) / (4 * (1 - (PF : ℚ) / (2 : ℚ) ^ pF) ^ 2)) = (0 : ℚ) := by
      rw [hPF_eq]
      have h2 : (2 : ℚ) ^ pF ≠ 0 := pow_ne_zero pF (by norm_num)
      field_simp [h2]
      ring
    rw [hzero]
    rw [qn_rnd]
    norm_num
    unfold kapI PF
    simp
  · have hV : 0 < 4 * (PF - LN) ^ 2 := by
      have hsq : 0 < (PF - LN) ^ 2 := sq_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm h))
      positivity
    have h_expr : ((EN : ℚ) / (2 : ℚ) ^ pF * ((LN : ℚ) / (2 : ℚ) ^ pF) / (4 * (1 - (LN : ℚ) / (2 : ℚ) ^ pF) ^ 2)) =
                 ((EN * LN : ℚ) / (4 * ((PF : ℚ) - (LN : ℚ)) ^ 2)) := by
      rw [hPF_eq]
      field_simp [hPF_ne_zero]
    have h_qn := qn_rnd_div pF (EN * LN) (4 * (PF - LN) ^ 2) hV
    -- h_qn: qn pF (rnd pF (↑(EN * LN) / ↑(4 * (PF - LN) ^ 2))) = (2 * (EN * LN) * 2 ^ pF + (4 * (PF - LN) ^ 2)) / (2 * (4 * (PF - LN) ^ 2))
    calc
      qn pF (rnd pF ((EN : ℚ) / 2 ^ pF * ((LN : ℚ) / 2 ^ pF) / (4 * (1 - (LN : ℚ) / 2 ^ pF) ^ 2))) =
          qn pF (rnd pF (((EN * LN : ℚ) / (4 * ((PF : ℚ) - (LN : ℚ)) ^ 2)))) := by rw [h_expr]
      _ = qn pF (rnd pF (((EN * LN : ℤ) : ℚ) / ((4 * (PF - LN) ^ 2 : ℤ) : ℚ))) := by push_cast; ring
      _ = (2 * (EN * LN) * 2 ^ pF + (4 * (PF - LN) ^ 2)) / (2 * (4 * (PF - LN) ^ 2)) := by rw [h_qn]
      _ = kapI EN LN (2 ^ pF) := by
        unfold kapI
        rfl

theorem qn_nu_gen (pF : ℕ) (LN : ℤ) (h : LN < 2 ^ pF) :
    qn pF (rnd pF (1 / (1 - (LN : ℚ) / 2 ^ pF))) = nuI LN (2 ^ pF) := by
  have hV : 0 < (2 ^ pF : ℤ) - LN := by
    omega
  have h2 : (2 ^ pF : ℚ) ≠ 0 := by positivity
  have hden : (2 ^ pF : ℚ) - (LN : ℚ) ≠ 0 := by
    intro hzero
    have hzero' : (2 ^ pF : ℤ) - LN = 0 := by exact_mod_cast hzero
    omega
  have h_eq : (1 : ℚ) / (1 - (LN : ℚ) / (2 ^ pF : ℚ)) = ((2 ^ pF : ℤ) : ℚ) / (((2 ^ pF : ℤ) - LN : ℤ) : ℚ) := by
    field_simp [h2, hden]
    push_cast
    ring
  rw [h_eq]
  rw [qn_rnd_div pF (2 ^ pF) ((2 ^ pF : ℤ) - LN) hV]
  unfold nuI
  rfl

theorem qn_sb_gen (pF Ne : ℕ) (RNp : ℤ) (h : 0 ≤ RNp) :
    qn pF (dn pF (1 / ((Ne : ℚ) ^ 2 * ((RNp : ℚ) / 2 ^ pF) * ((RNp : ℚ) / 2 ^ pF + 1)))) =
      sbI Ne RNp (2 ^ pF) := by
  rw [qn_dn]
  have hP_ne_zero : (2 ^ pF : ℚ) ≠ 0 := by positivity
  have h_expr : (1 / ((Ne : ℚ) ^ 2 * ((RNp : ℚ) / 2 ^ pF) * ((RNp : ℚ) / 2 ^ pF + 1))) * (2 ^ pF : ℚ) =
      ((2 ^ pF : ℚ) ^ 3) / (((Ne : ℚ) ^ 2 * (RNp : ℚ) * ((RNp : ℚ) + (2 ^ pF : ℚ)))) := by
    field_simp [hP_ne_zero]
  rw [h_expr]
  unfold sbI
  let U : ℤ := (2 ^ pF) ^ 3
  let V : ℤ := (Ne : ℤ) ^ 2 * RNp * (RNp + (2 ^ pF : ℤ))
  have hV_nonneg : 0 ≤ V := by
    have hNe2 : 0 ≤ (Ne : ℤ) ^ 2 := pow_two_nonneg _
    have hP : 0 < (2 ^ pF : ℤ) := pow_pos (by norm_num) pF
    have hSum : 0 ≤ RNp + (2 ^ pF : ℤ) := add_nonneg h hP.le
    exact mul_nonneg (mul_nonneg hNe2 h) hSum
  by_cases hV0 : V = 0
  · have hV0' : (V : ℚ) = 0 := by exact_mod_cast hV0
    have h_denom : (Ne : ℚ) ^ 2 * (RNp : ℚ) * ((RNp : ℚ) + (2 ^ pF : ℚ)) = 0 := by
      simpa [V] using hV0'
    rw [h_denom]
    have h_rhs_denom : (Ne : ℤ) ^ 2 * RNp * (RNp + (2 ^ pF : ℤ)) = V := rfl
    rw [h_rhs_denom, hV0, Int.ediv_zero]
    simp
  · have hV_pos : 0 < V := by
      omega
    simpa [U, V] using floor_div_int U V hV_pos

theorem qn_W_gen (d q pF Ne : ℕ) (RNp LeN : ℤ) (hL : 0 < LeN) :
    qn pF (up pF ((RNp : ℚ) / 2 ^ pF + 4 * (d : ℚ) * sqrtUp q ((Ne : ℚ) / ((LeN : ℚ) / 2 ^ q)))) =
      WI d RNp ((Nat.sqrt ((Ne * (2 ^ q) ^ 3 + LeN - 1) / LeN).toNat : ℤ) + 1) (2 ^ pF) (2 ^ q) := by
  set SW := (Nat.sqrt ((Ne * (2 ^ q) ^ 3 + LeN - 1) / LeN).toNat : ℤ) + 1 with hSW
  have h2qpos : 0 < (2 : ℤ) ^ q := by
    exact pow_pos (by norm_num) q
  have h_sqrtUp : sqrtUp q ((Ne : ℚ) / ((LeN : ℚ) / 2 ^ q)) = ((SW : ℚ) / 2 ^ q) := by
    unfold sqrtUp SW
    have h_inner : ((Ne : ℚ) / ((LeN : ℚ) / 2 ^ q)) * 4 ^ q = ((Ne : ℤ) * ((2 : ℤ) ^ q) ^ 3 : ℤ) / (LeN : ℚ) := by
      field_simp [show (LeN : ℚ) ≠ 0 from by exact_mod_cast hL.ne']
      push_cast
      have h_pow_eq : (4 : ℚ) ^ q = ((2 : ℚ) ^ q) ^ 2 := by
        calc
          (4 : ℚ) ^ q = ((2 : ℚ) ^ 2) ^ q := by norm_num
          _ = (2 : ℚ) ^ (2 * q) := by rw [pow_mul]
          _ = (2 : ℚ) ^ (q * 2) := by rw [mul_comm]
          _ = ((2 : ℚ) ^ q) ^ 2 := by rw [pow_mul]
      rw [h_pow_eq]
      ring
    have h_ceil : ⌈((Ne : ℚ) / ((LeN : ℚ) / 2 ^ q)) * 4 ^ q⌉ = ((Ne : ℤ) * ((2 : ℤ) ^ q) ^ 3 + LeN - 1) / LeN := by
      rw [h_inner]
      exact ceil_div_int ((Ne : ℤ) * ((2 : ℤ) ^ q) ^ 3) LeN hL
    rw [← Int.ceil_toNat]
    rw [h_ceil]
    push_cast
    ring
  rw [h_sqrtUp]
  have hx : ((RNp : ℚ) / 2 ^ pF + 4 * (d : ℚ) * ((SW : ℚ) / 2 ^ q)) * 2 ^ pF =
      ((RNp : ℤ) * ((2 : ℤ) ^ q) + 4 * (d : ℤ) * SW * ((2 : ℤ) ^ pF) : ℤ) / ((2 : ℤ) ^ q) := by
    field_simp [show ((2 : ℤ) ^ q : ℚ) ≠ 0 from by
      intro hzero
      have : (2 : ℤ) ^ q = 0 := by exact_mod_cast hzero
      exact pow_ne_zero q (by norm_num) this]
    push_cast
    ring
  rw [qn_up]
  rw [hx]
  have h_cast_denom : ((2 : ℤ) ^ q : ℚ) = ((2 : ℚ) ^ q) := by simp
  have h_ceil2_raw := ceil_div_int ((RNp : ℤ) * ((2 : ℤ) ^ q) + 4 * (d : ℤ) * SW * ((2 : ℤ) ^ pF)) ((2 : ℤ) ^ q) h2qpos
  have h_ceil2 : ⌈(↑(RNp * 2 ^ q + 4 * (d : ℤ) * SW * 2 ^ pF) : ℚ) / ((2 : ℚ) ^ q)⌉ =
      (((RNp : ℤ) * ((2 : ℤ) ^ q) + 4 * (d : ℤ) * SW * ((2 : ℤ) ^ pF) + (2 : ℤ) ^ q - 1) / ((2 : ℤ) ^ q) : ℤ) := by
    simpa [h_cast_denom] using h_ceil2_raw
  calc
    ⌈(↑(RNp * 2 ^ q + 4 * (d : ℤ) * SW * 2 ^ pF) : ℚ) / ((2 : ℚ) ^ q)⌉
        = (((RNp : ℤ) * ((2 : ℤ) ^ q) + 4 * (d : ℤ) * SW * ((2 : ℤ) ^ pF) + (2 : ℤ) ^ q - 1) / ((2 : ℤ) ^ q) : ℤ) := h_ceil2
    _ = WI d RNp SW (2 ^ pF) (2 ^ q) := by
      unfold WI
      ring

theorem qn_A0_gen (p q pF : ℕ) (SG : ℤ) :
    qn p (rnd p (sqrtUp q ((SG : ℚ) / 2 ^ pF))) =
      A0I ((Nat.sqrt ((SG * (2 ^ q) ^ 2 + 2 ^ pF - 1) / 2 ^ pF).toNat : ℤ) + 1) (2 ^ p) (2 ^ q) := by
  set S1 := (Nat.sqrt ((SG * (2 ^ q) ^ 2 + 2 ^ pF - 1) / 2 ^ pF).toNat : ℤ) + 1 with hS1
  have hpFpos : 0 < (2 : ℤ) ^ pF := pow_pos (by norm_num) pF
  have hqpos : 0 < (2 : ℤ) ^ q := pow_pos (by norm_num) q
  have h_sqrtUp : sqrtUp q ((SG : ℚ) / 2 ^ pF) = (S1 : ℚ) / ((2 ^ q : ℤ) : ℚ) := by
    unfold sqrtUp S1
    have h_mul : ((SG : ℚ) / 2 ^ pF) * (4 : ℚ) ^ q = ((SG * ((2 : ℤ) ^ q) ^ 2 : ℤ) : ℚ) / ((2 ^ pF : ℤ) : ℚ) := by
      have h4q : (4 : ℚ) ^ q = ((2 : ℚ) ^ q) ^ 2 := by
        calc
          (4 : ℚ) ^ q = ((2 : ℚ) ^ 2) ^ q := by norm_num
          _ = (2 : ℚ) ^ (2 * q) := by rw [pow_mul]
          _ = (2 : ℚ) ^ (q * 2) := by rw [mul_comm]
          _ = ((2 : ℚ) ^ q) ^ 2 := by rw [pow_mul]
      rw [h4q]
      push_cast
      ring
    rw [h_mul]
    rw [← Int.ceil_toNat]
    rw [ceil_div_int (SG * ((2 : ℤ) ^ q) ^ 2) ((2 : ℤ) ^ pF) hpFpos]
    push_cast
    simp
  rw [h_sqrtUp]
  rw [qn_rnd_div p S1 (2 ^ q : ℤ) hqpos]
  unfold A0I
  ring

theorem rint_gen (pF : ℕ) (RNp : ℤ) (h : 0 ≤ RNp) :
    ((⌈(RNp : ℚ) / 2 ^ pF⌉₊ : ℕ) : ℤ) = (RNp + 2 ^ pF - 1) / 2 ^ pF := by
  have hpFpos : 0 < (2 ^ pF : ℤ) := by
    have hpos : 0 < 2 ^ pF := pow_pos (by norm_num) pF
    exact_mod_cast hpos
  have hdiv_nonneg : 0 ≤ (RNp : ℚ) / (2 ^ pF : ℚ) :=
    div_nonneg (by exact_mod_cast h) (by positivity)
  have hceil_eq : ((⌈(RNp : ℚ) / (2 ^ pF : ℚ)⌉₊ : ℕ) : ℤ) = ⌈(RNp : ℚ) / (2 ^ pF : ℚ)⌉ := by
    exact_mod_cast natCast_ceil_eq_intCast_ceil hdiv_nonneg
  rw [hceil_eq]
  simpa using ceil_div_int RNp (2 ^ pF) hpFpos

theorem qn_R_gen (d q pF : ℕ) (T : ℤ) :
    qn pF (up pF (134 * (d : ℚ) * sqrtUp q ((T : ℚ) / 2 ^ q))) =
      RI d ((Nat.sqrt (T * 2 ^ q).toNat : ℤ) + 1) (2 ^ pF) (2 ^ q) := by
  set RS := (Nat.sqrt ((T * 2 ^ q).toNat) : ℤ) + 1 with hRS
  have h4q_eq : (4 ^ q : ℚ) = (2 ^ q : ℚ) * (2 ^ q : ℚ) := by
    have h_nat : (4 : ℕ) ^ q = (2 ^ q) * (2 ^ q) := by
      calc
        (4 : ℕ) ^ q = ((2 : ℕ) ^ 2) ^ q := by norm_num
        _ = ((2 : ℕ) ^ q) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]
        _ = (2 ^ q) * (2 ^ q) := by ring
    exact_mod_cast h_nat
  have h_sqrtUp : sqrtUp q ((T : ℚ) / 2 ^ q) = (RS : ℚ) / (2 ^ q : ℚ) := by
    unfold sqrtUp
    have h_inner : ((T : ℚ) / (2 ^ q : ℚ)) * (4 ^ q : ℚ) = (T : ℚ) * (2 ^ q : ℚ) := by
      field_simp [show (2 ^ q : ℚ) ≠ 0 from by positivity]
      rw [h4q_eq]
      ring
    rw [h_inner]
    have h_ceil : ⌈(T : ℚ) * (2 ^ q : ℚ)⌉₊ = (T * 2 ^ q).toNat := by
      have h_arg : (T : ℚ) * (2 ^ q : ℚ) = ((T * 2 ^ q : ℤ) : ℚ) := by simp
      rw [h_arg]
      rw [Nat.ceil_intCast]
    rw [h_ceil]
    unfold RS
    push_cast
    ring
  have h_arg : 134 * (d : ℚ) * sqrtUp q ((T : ℚ) / 2 ^ q) = ((134 * d * RS : ℤ) : ℚ) / (2 ^ q : ℚ) := by
    rw [h_sqrtUp]
    push_cast
    ring
  rw [h_arg]
  simpa [RI] using qn_up_div pF (134 * d * RS) (2 ^ q) (by positivity)

theorem neg_neg_ediv_eq_add_pred_ediv {N : ℤ} {D : ℕ} (hD : 0 < D) : -(-N / (D : ℤ)) = (N + (D : ℤ) - 1) / (D : ℤ) := by
  have hD' : (0 : ℤ) < D := by exact_mod_cast hD
  have hceil : ⌈(N : ℚ) / (D : ℚ)⌉ = -(-N / (D : ℤ)) := Rat.ceil_intCast_div_natCast N D
  have hceil2 : ⌈(N : ℚ) / (D : ℚ)⌉ = (N + (D : ℤ) - 1) / (D : ℤ) := by
    rw [Int.ceil_eq_iff]
    have hD'' : (0 : ℚ) < D := by exact_mod_cast hD
    set z := (N + (D : ℤ) - 1) / (D : ℤ) with hz
    have hz_mul_le : z * (D : ℤ) ≤ N + (D : ℤ) - 1 := Int.ediv_mul_le (N + (D : ℤ) - 1) hD'.ne'
    have hz_lt : N + (D : ℤ) - 1 < (z + 1) * (D : ℤ) := Int.lt_ediv_add_one_mul_self (N + (D : ℤ) - 1) hD'
    have hz1_lt_N : (z - 1) * (D : ℤ) < N := by
      have hineq : (z - 1) * (D : ℤ) + 1 ≤ N := by
        linarith
      omega
    have hN_le_zD : N ≤ z * (D : ℤ) := by
      have hineq : N < z * (D : ℤ) + 1 := by
        linarith
      omega
    constructor
    · have hq : ((z - 1 : ℤ) : ℚ) * (D : ℚ) < (N : ℚ) := by exact_mod_cast hz1_lt_N
      field_simp [hD''.ne']
      simpa [sub_mul] using hq
    · have hq : (N : ℚ) ≤ (z : ℚ) * (D : ℚ) := by exact_mod_cast hN_le_zD
      field_simp [hD''.ne']
      nlinarith
  rw [← hceil, hceil2]

theorem qn_B0_gen (p q pF : ℕ) (SG : ℤ) :
    qn p (rnd p (1 / sqrtUp q ((SG : ℚ) / 2 ^ pF))) =
      B0I ((Nat.sqrt ((SG * (2 ^ q) ^ 2 + 2 ^ pF - 1) / 2 ^ pF).toNat : ℤ) + 1) (2 ^ p) (2 ^ q) := by
  set S1 : ℤ := (Nat.sqrt ((SG * (2 ^ q) ^ 2 + 2 ^ pF - 1) / 2 ^ pF).toNat : ℤ) + 1 with hS1
  have hS1pos : 0 < S1 := by
    rw [hS1]
    have : 0 ≤ (Nat.sqrt ((SG * (2 ^ q) ^ 2 + 2 ^ pF - 1) / 2 ^ pF).toNat : ℤ) := by
      exact_mod_cast Nat.zero_le _
    omega
  have h_sqrtUp : sqrtUp q ((SG : ℚ) / 2 ^ pF) = (S1 : ℚ) / 2 ^ q := by
    unfold sqrtUp
    have h_mul : ((SG : ℚ) / 2 ^ pF) * 4 ^ q = (SG : ℚ) * ((2 ^ q) ^ 2) / (2 ^ pF : ℚ) := by
      have h : (4 : ℚ) ^ q = ((2 : ℚ) ^ q) ^ 2 := by
        calc
          (4 : ℚ) ^ q = ((2 : ℚ) ^ 2) ^ q := by norm_num
          _ = ((2 : ℚ) ^ q) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]
      rw [h]
      ring
    rw [h_mul]
    set N := SG * ((2 ^ q) ^ 2) with hN
    set D := 2 ^ pF with hD
    have hDpos : 0 < D := by
      apply pow_pos (by norm_num) pF
    congr 1
    rw [hS1]
    have hgoal : (Nat.sqrt ⌈(SG : ℚ) * ((2 ^ q) ^ 2 : ℕ) / ((2 ^ pF : ℕ) : ℚ)⌉₊ : ℚ) + 1 =
                ((Nat.sqrt ((N + (D : ℤ) - 1) / (D : ℤ)).toNat : ℤ) + 1 : ℚ) := by
      have hLHS : (Nat.sqrt ⌈(SG : ℚ) * ((2 ^ q) ^ 2 : ℕ) / ((2 ^ pF : ℕ) : ℚ)⌉₊ : ℚ) = (Nat.sqrt ⌈(N : ℚ) / (D : ℚ)⌉₊ : ℚ) := by
        simp [hN, hD]
      rw [hLHS]
      congr 1
      have hceil_eq : ⌈(N : ℚ) / (D : ℚ)⌉₊ = (((N + (D : ℤ) - 1) / (D : ℤ)).toNat : ℕ) := by
        calc
          ⌈(N : ℚ) / (D : ℚ)⌉₊ = Int.toNat (Int.ceil ((N : ℚ) / (D : ℚ))) := rfl
          _ = Int.toNat (-(-N / (D : ℤ))) := by rw [Rat.ceil_intCast_div_natCast N D]
          _ = Int.toNat ((N + (D : ℤ) - 1) / (D : ℤ)) := by rw [neg_neg_ediv_eq_add_pred_ediv hDpos]
          _ = (((N + (D : ℤ) - 1) / (D : ℤ)).toNat : ℕ) := rfl
      rw [hceil_eq]
      simp
    simpa [hN, hD] using hgoal
  have h_recip : 1 / sqrtUp q ((SG : ℚ) / 2 ^ pF) = (2 ^ q : ℚ) / (S1 : ℚ) := by
    rw [h_sqrtUp]
    field_simp [show (S1 : ℚ) ≠ 0 from by exact_mod_cast hS1pos.ne']
  rw [h_recip]
  have htemp := qn_rnd_div p (2 ^ q) S1 hS1pos
  have htemp' : qn p (rnd p (2 ^ q / (S1 : ℚ))) = (2 * (2 ^ q) * 2 ^ p + S1) / (2 * S1) := by
    simpa [Nat.cast_pow] using htemp
  rw [htemp']
  unfold B0I
  congr 1

/-! ## At `par d n` -/

theorem rnd_eq_qn (k : ℕ) (x : ℚ) : rnd k x = (qn k (rnd k x) : ℚ) / 2 ^ k := by rw [qn_rnd]; rfl

theorem up_eq_qn (k : ℕ) (x : ℚ) : up k x = (qn k (up k x) : ℚ) / 2 ^ k := by rw [qn_up]; rfl

theorem par_Ne (d n : ℕ) : (par d n).Ne = BLP.Ne d n := rfl

theorem par_Lam (d n : ℕ) : (par d n).Lam = d * BLP.Ne d n := rfl

theorem par_Rint (d n : ℕ) : (par d n).Rint = ⌈(par d n).R⌉₊ := rfl

theorem par_eHat (d n : ℕ) :
    (par d n).eHat = 1 / 2 ^ ((par d n).p - 3 * (BLP.Ne d n).size - 6 * d.size - 64) := rfl

theorem par_eHat_inv (d n : ℕ) :
    (par d n).eHat⁻¹ = 2 ^ ((par d n).p - 3 * (BLP.Ne d n).size - 6 * d.size - 64) := by
  rw [par_eHat, one_div, inv_inv]

section Par

variable {d n : ℕ}

theorem par_Le_eq (hd : 1 ≤ d) (hn : 1 ≤ n) : (par d n).Le = (LeN d n : ℚ) / 2 ^ (par d n).q :=
  (LeN_div hd hn).symm

theorem par_Lh (hd : 1 ≤ d) (hn : 1 ≤ n) :
    36 * (PieceA.L0 d n + PieceA.ee d n) = (LhN d n : ℚ) / 2 ^ (par d n).q := by
  rw [PieceA.L0, PieceA.ee, lnQ_eq _ _ (Ne_pos hd hn), LhN, L0N, EN, lnErr]
  push_cast; field_simp

theorem Le_ge_one (hd : 1 ≤ d) (hn : 1 ≤ n) : 1 ≤ (par d n).Le := by
  have hq1 : 1 ≤ (par d n).q := by have := q_ge d n; omega
  have hL0 := PieceA.lnQ_err (par d n).q (BLP.Ne d n) hq1 (Ne_pos hd hn)
  have hee := PieceA.lnErr_le d n (BLP.Ne d n) hd hn le_rfl
  have hu : PieceA.u d n ≤ 1 := by
    unfold PieceA.u; rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hN20 : (2 : ℝ) ^ 20 ≤ (BLP.Ne d n : ℝ) := by
    have h1 := (PieceA.NeN_ge d n hd hn).1
    have h3 : 1 ≤ d ^ 3 := Nat.one_le_pow _ _ hd
    have h2 : 2 ^ 20 ≤ BLP.Ne d n := le_trans (by nlinarith) h1
    exact_mod_cast h2
  have hlog : 20 * Real.log 2 ≤ Real.log (BLP.Ne d n) := by
    have h20 : Real.log ((2 : ℝ) ^ 20) = 20 * Real.log 2 := by rw [Real.log_pow]; norm_num
    linarith [Real.log_le_log (by positivity) hN20]
  have h2 := Real.log_two_gt_d9
  obtain ⟨hA, -⟩ := abs_le.mp hL0
  have hLe : (((par d n).Le : ℚ) : ℝ) = 36 * (((lnQ (par d n).q (BLP.Ne d n) : ℚ) : ℝ) -
      ((lnErr (par d n).q (BLP.Ne d n) : ℚ) : ℝ)) := by
    rw [PieceA.par_Le, PieceA.L0, PieceA.ee]; push_cast; ring
  have hpos : (1 : ℝ) ≤ (((par d n).Le : ℚ) : ℝ) := by
    rw [hLe]
    have : (PieceA.u d n) / 2 ^ 16 ≤ 1 := by linarith
    linarith
  exact_mod_cast hpos

theorem qn_par_eps (hd : 1 ≤ d) (hn : 1 ≤ n) : qn (par d n).pF (par d n).eps = epsZ d n := by
  rw [qn_eps_eq d n hn (LhN d n) (par_Lh hd hn)]; rfl

theorem qn_par_lam (hd : 1 ≤ d) (hn : 1 ≤ n) : qn (par d n).pF (par d n).lam = lamZ d n := by
  rw [PieceA.par_lam, par_Le_eq hd hn]
  exact qn_lam_gen d _ _ hd (LeN d n) (LeN_pos hd hn).ne'

theorem qn_par_eta (hd : 1 ≤ d) (hn : 1 ≤ n) : qn (par d n).pF (par d n).eta = etaZ d n := by
  rw [PieceA.par_eta, par_Le_eq hd hn]
  exact qn_eta_gen d n _ _ hn (LeN d n) (LeN_pos hd hn)

theorem qn_par_sig (hd : 1 ≤ d) (hn : 1 ≤ n) : qn (par d n).pF (par d n).sig2 = sigZ d n := by
  rw [PieceA.par_sig2, par_Le_eq hd hn]
  exact qn_sig_gen _ _ (LeN d n) (LeN_pos hd hn)

theorem qn_par_rho (hd : 1 ≤ d) (hn : 1 ≤ n) : qn (par d n).pF (par d n).rho = rhoZ d n := by
  rw [PieceA.par_rho, par_Le_eq hd hn]
  exact qn_rho_gen d _ _ (LeN d n)

theorem par_lam_eq (hd : 1 ≤ d) (hn : 1 ≤ n) : (par d n).lam = (lamZ d n : ℚ) / 2 ^ (par d n).pF := by
  rw [← qn_par_lam hd hn, PieceA.par_lam]; exact rnd_eq_qn _ _

theorem par_eta_eq (hd : 1 ≤ d) (hn : 1 ≤ n) : (par d n).eta = (etaZ d n : ℚ) / 2 ^ (par d n).pF := by
  rw [← qn_par_eta hd hn, PieceA.par_eta]; exact rnd_eq_qn _ _

theorem par_sig_eq (hd : 1 ≤ d) (hn : 1 ≤ n) : (par d n).sig2 = (sigZ d n : ℚ) / 2 ^ (par d n).pF := by
  rw [← qn_par_sig hd hn, PieceA.par_sig2]; exact rnd_eq_qn _ _

theorem qn_par_kapc (hd : 1 ≤ d) (hn : 1 ≤ n) : qn (par d n).pF (par d n).kapc = kapZ d n := by
  rw [PieceA.par_kapc, par_eta_eq hd hn, par_lam_eq hd hn]
  exact qn_kapc_gen _ (etaZ d n) (lamZ d n)

/-- `λ' < 1`: `qn pF λ' < 2^pF`. -/
theorem lamZ_lt (hd : 1 ≤ d) (hn : 1 ≤ n) : lamZ d n < 2 ^ (par d n).pF := by
  have hL := Le_ge_one hd hn
  have hd' : (1 : ℚ) ≤ d := by exact_mod_cast hd
  have hP : (1 : ℚ) ≤ 2 ^ (par d n).pF := one_le_pow₀ (by norm_num)
  have h1 : (1 : ℚ) ≤ d * (par d n).Le ^ 2 := one_le_mul_of_one_le_of_one_le hd' (one_le_pow₀ hL)
  have hx : 1 / (725 * (d : ℚ) * (par d n).Le ^ 2) ≤ 1 / 725 :=
    one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have hx2 := mul_le_mul_of_nonneg_right hx (by positivity : (0 : ℚ) ≤ 2 ^ (par d n).pF)
  rw [← qn_par_lam hd hn, PieceA.par_lam, qn_rnd, Int.floor_lt]
  push_cast
  linarith

theorem qn_par_nu (hd : 1 ≤ d) (hn : 1 ≤ n) : qn (par d n).pF (par d n).nu = nuZ d n := by
  rw [PieceA.par_nu, par_lam_eq hd hn]
  exact qn_nu_gen _ (lamZ d n) (lamZ_lt hd hn)

theorem qn_par_A0 (hd : 1 ≤ d) (hn : 1 ≤ n) : qn (par d n).p (par d n).A0 = A0Z d n := by
  rw [PieceA.par_A0, par_sig_eq hd hn]
  exact qn_A0_gen _ _ _ (sigZ d n)


theorem l1Q_eq : PieceA.l1Q d n = ((L1N d n + E1N d n : ℤ) : ℚ) / 2 ^ (par d n).q := by
  rw [PieceA.l1Q, lnQ_eq _ _ (by omega : 1 ≤ 2 * d + 2), L1N, E1N, lnErr]
  push_cast; field_simp

theorem qn_par_R : qn (par d n).pF (par d n).R = RZ d n := by
  rw [PieceA.par_R, l1Q_eq]
  unfold RZ RSZ PFZ QZ
  exact qn_R_gen d _ _ _

theorem par_R_eq : (par d n).R = (RZ d n : ℚ) / 2 ^ (par d n).pF := by
  rw [← qn_par_R, PieceA.par_R]; exact up_eq_qn _ _

theorem RI_nonneg (d : ℕ) (T : ℤ) (pF q : ℕ) :
    0 ≤ RI d ((Nat.sqrt T.toNat : ℤ) + 1) (2 ^ pF) (2 ^ q) := by
  unfold RI
  have h0 : 0 ≤ (Nat.sqrt T.toNat : ℤ) := Int.natCast_nonneg _
  have h1 : (1 : ℤ) ≤ 2 ^ q := one_le_pow₀ (by norm_num)
  have h2 : 0 ≤ 134 * (d : ℤ) * ((Nat.sqrt T.toNat : ℤ) + 1) * 2 ^ pF := by positivity
  exact Int.ediv_nonneg (by linarith) (by linarith)

theorem RZ_nonneg : 0 ≤ RZ d n := RI_nonneg d _ _ _

theorem qn_par_sb : qn (par d n).pF (par d n).sb = sbZ d n := by
  rw [PieceA.par_sb, par_R_eq]
  unfold sbZ PFZ
  exact qn_sb_gen _ _ _ RZ_nonneg

theorem qn_par_W (hd : 1 ≤ d) (hn : 1 ≤ n) : qn (par d n).pF (par d n).W = WZ d n := by
  rw [PieceA.par_W, par_R_eq, par_Le_eq hd hn]
  unfold WZ SWZ PFZ QZ
  exact qn_W_gen d _ _ _ (RZ d n) (LeN d n) (LeN_pos hd hn)

theorem qn_par_B0 (hd : 1 ≤ d) (hn : 1 ≤ n) : qn (par d n).p (par d n).B0 = B0Z d n := by
  rw [PieceA.par_B0, par_sig_eq hd hn]
  unfold B0Z S1Z PZ QZ PFZ
  exact qn_B0_gen _ _ _ (sigZ d n)

theorem Rint_eq : ((par d n).Rint : ℤ) = RintZ d n := by
  rw [par_Rint, par_R_eq]
  unfold RintZ rintI PFZ
  exact rint_gen _ _ RZ_nonneg
end Par

end AdversarialBco.Bit.Transfer.BLM
