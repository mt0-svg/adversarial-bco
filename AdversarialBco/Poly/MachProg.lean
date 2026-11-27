/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Poly.MachVL

@[expose] public section

/-!
# The machine layer, part 4: the program of a learner and the clauses of the frozen statement

A learner is the program `prog L pre A B rt rn one x v`: the setup of the registers (`setup`), a preparation `pre`,
then the rounds `t < n` of a counted loop, each made of a part `A` that leaves the point to play in the array `v`, the
play (`play L x v`, the observation lands in the scalar `x`) and a part `B`. `prog_spec` turns rules for `pre`, `A` and
`B` in the language of `MachVL.lean` (invariants `I t` at the start of round `t` and `J t` before its play, step bounds
`K0`, `KA`, `KB`) into the two clauses that the frozen statement asks of a program on one run: `CostOK` with the bounds
`Ks + K0 + KA + 3` and `KA + KB + 4`, and the point played in round `t < n` equal to the point `pt t` that the rule of
`A` names. `CostOK.mono` loosens the bounds.
-/

namespace AdversarialBco.Poly.Mach

open AdversarialBco AdversarialBco.RealRAM VL

variable {d : ℕ}

/-- The environment after `play L x v`: the observation in the scalar `x`, one more round, the point recorded. -/
noncomputable def Env.afterPlay (w : World d) (x v : ℕ) (σ : Env d) : Env d :=
  { σ.setSc x (w.f σ.rounds (WithLp.toLp 2 (σ.vec v)) + w.noise σ.rounds) with
    rounds := σ.rounds + 1
    pts := Function.update σ.pts σ.rounds (WithLp.toLp 2 (σ.vec v)) }

/-- The program of a learner. -/
def prog (L : Layout) (pre A B : Cmd) (rt rn one x v : ℕ) : Cmd :=
  .seq (setup L) (.seq pre (forN rt rn one (.seq A (.seq (play L x v) B))))

theorem Exec.prim_inv {w : World d} {p : Prim} {s s' : State d} {k : ℕ} (h : Exec w (.prim p) s k s') :
    k = 1 ∧ s' = p.exec w s := by
  cases h; exact ⟨rfl, rfl⟩

/-- The cost clause from the plays: the first within `B0` steps, and for each later round `t < n` a step `p` at which
round `t - 1` is not played yet and a step `p'`, within `B` steps of `p`, after which round `t` is played. -/
theorem costOK_of_plays (P : List Instr) (w : World d) (s : State d) (n : ℕ) (B0 B : ℝ)
    (h0 : ∃ p, (run P w s (p + 1)).rounds = 1 ∧ p + 1 ≤ ⌈B0⌉₊)
    (hstep : ∀ t, 1 ≤ t → t < n → ∃ p p', (run P w s p).rounds = t - 1 ∧ (run P w s (p' + 1)).rounds = t + 1 ∧
      p' ≤ p + ⌈B⌉₊) :
    CostOK P w s n B0 B := by
  refine ⟨?_, fun k t ht1 htn hk => ?_⟩
  · obtain ⟨p, hp, hpB⟩ := h0
    have := run_rounds_mono P w s hpB
    rw [hp] at this
    exact this
  · obtain ⟨p, p', hp, hp', hpp⟩ := hstep t ht1 htn
    have hkp : p + 1 ≤ k := by
      by_contra hlt
      have := run_rounds_mono P w s (show k ≤ p by omega)
      rw [hp, hk] at this
      omega
    have := run_rounds_mono P w s (show p' + 1 ≤ k + ⌈B⌉₊ by omega)
    rw [hp'] at this
    exact this

/-- `CostOK` with looser bounds. -/
theorem CostOK.mono {P : List Instr} {w : World d} {s : State d} {n : ℕ} {B0 B B0' B' : ℝ}
    (h : CostOK P w s n B0 B) (h0 : B0 ≤ B0') (h1 : B ≤ B') : CostOK P w s n B0' B' := by
  refine ⟨(h.1.trans (run_rounds_mono P w s (Nat.ceil_mono h0))), fun k t ht1 htn hk => ?_⟩
  exact (h.2 k t ht1 htn hk).trans (run_rounds_mono P w s (by have := Nat.ceil_mono h1; omega))

/-- The program lemma. -/
theorem prog_spec (L : Layout) {pre A B : Cmd} {rt rn one x v : ℕ} (hrt : rt < L.NN) (hrn : rn < L.NN)
    (hone : one < L.NN) (hrtn : rt ≠ rn) (hrto : rt ≠ one) (hx : x < L.NS) (hv : v < L.NA)
    (w : World d) (n : ℕ) (hn : 1 ≤ n) (r0 R0 δ : ℝ) (Ks K0 KA KB : ℕ)
    (I J : ℕ → Env d → Prop) (pt : ℕ → E d)
    (hsetup : ∃ s, Exec w (setup L) (init d n r0 R0 δ) Ks s ∧ Rep L (Env.init d n r0 R0 δ) s)
    (hpre : Runs L w pre (Env.init d n r0 R0 δ) K0
      (fun σ => I 0 (σ.setNat rt 0) ∧ σ.nat rn = n ∧ σ.nat one = 1 ∧ σ.rounds = 0))
    (hA : ∀ t < n, ∀ σ, I t σ → σ.nat rt = t → σ.nat rn = n → σ.nat one = 1 → σ.rounds = t →
      Runs L w A σ KA (fun σ' => J t σ' ∧ σ'.nat rt = t ∧ σ'.nat rn = n ∧ σ'.nat one = 1 ∧ σ'.rounds = t ∧
        WithLp.toLp 2 (σ'.vec v) = pt t))
    (hB : ∀ t < n, ∀ σ, J t σ → σ.nat rt = t → σ.nat rn = n → σ.nat one = 1 → σ.rounds = t →
      Runs L w B (σ.afterPlay w x v) KB (fun σ' => I (t + 1) (σ'.setNat rt (t + 1)) ∧ σ'.nat rt = t ∧
        σ'.nat rn = n ∧ σ'.nat one = 1 ∧ σ'.rounds = t + 1)) :
    CostOK ((prog L pre A B rt rn one x v).compile 0) w (init d n r0 R0 δ) n ((Ks + K0 + KA + 3 : ℕ) : ℝ)
        ((KA + KB + 4 : ℕ) : ℝ) ∧
      ∀ t < n, played ((prog L pre A B rt rn one x v).compile 0) w (init d n r0 R0 δ) t = pt t := by
  set P := (prog L pre A B rt rn one x v).compile 0 with hP
  set S0 := init d n r0 R0 δ
  -- the code of the parts
  have hc : CodeAt P 0 ((prog L pre A B rt rn one x v).compile 0) := fun i _ => by rw [Nat.zero_add]
  have hset : CodeAt P 0 ((setup L).compile 0) := CodeAt.seq_left hc
  have hrest := CodeAt.seq_right hc
  have hpreC := CodeAt.seq_left hrest
  have hfor : CodeAt P (0 + (setup L).len + pre.len)
      ((Cmd.seq (nconst rt 0) (.whileN rt rn (.seq (.seq A (.seq (play L x v) B)) (nadd rt rt one)))).compile
        (0 + (setup L).len + pre.len)) := CodeAt.seq_right hrest
  have hnc := CodeAt.seq_left hfor
  set oL := 0 + (setup L).len + pre.len + (nconst rt 0).len with hoL
  have hloop : CodeAt P oL
      ((Cmd.whileN rt rn (.seq (.seq A (.seq (play L x v) B)) (nadd rt rt one))).compile oL) :=
    CodeAt.seq_right hfor
  have hbody := CodeAt.whileN_body hloop
  have hAB := CodeAt.seq_left hbody
  have hAc := CodeAt.seq_left hAB
  have hPB := CodeAt.seq_right hAB
  have hPc := CodeAt.seq_left hPB
  -- the claims
  let Claim : ℕ → ℕ → Prop := fun t q => ∃ s σ, run P w S0 q = atPc s oL ∧ Rep L σ s ∧ I t σ ∧ σ.nat rt = t ∧
    σ.nat rn = n ∧ σ.nat one = 1 ∧ σ.rounds = t
  let PlayAt : ℕ → ℕ → Prop := fun t p => (run P w S0 p).rounds = t ∧ (run P w S0 (p + 1)).rounds = t + 1 ∧
    (run P w S0 (p + 1)).pts t = pt t
  have hinit : ∃ q, Claim 0 q ∧ q ≤ Ks + K0 + 1 := by
    obtain ⟨s1, hex1, hrep1⟩ := hsetup
    have hr1 : run P w S0 Ks = atPc s1 (0 + (setup L).len) := exec_sim hex1 0 hset
    obtain ⟨k0, s2, σ2, hk0, hex2, hrep2, hI0, hn2, ho2, hr2⟩ := hpre s1 hrep1
    have hr2' := exec_sim hex2 _ hpreC
    obtain ⟨k1, s3, σ3, hk1, hex3, hrep3, e3⟩ := runs_nconst (L := L) (w := w) (σ := σ2) hrt 0 s2 hrep2
    have hr3 := exec_sim hex3 _ hnc
    subst e3
    refine ⟨Ks + k0 + k1, ⟨s3, σ2.setNat rt 0, ?_, hrep3, hI0, by simp, by simp [Ne.symm hrtn, hn2],
      by simp [Ne.symm hrto, ho2], hr2⟩, by omega⟩
    rw [run_add, run_add, hr1, hr2', hr3]
  have hstep : ∀ t < n, ∀ q, Claim t q → ∃ p, PlayAt t p ∧ p ≤ q + 1 + KA ∧
      ∃ q', Claim (t + 1) q' ∧ q' ≤ p + KB + 3 := by
    intro t ht q ⟨s, σ, hq, hs, hI, hσt, hσn, hσo, hσr⟩
    have hcond : condN s rt rn := (condN_iff hs hrt hrn).2 (by rw [hσt, hσn]; exact ht)
    obtain ⟨kA, sA, σA, hkA, hexA, hrepA, hJ, hAt, hAn, hAo, hAr, hAv⟩ := hA t ht σ hI hσt hσn hσo hσr s hs
    obtain ⟨k2, sP, σP, -, hexP, hrepP, eP⟩ := runs_play (L := L) (w := w) (σ := σA) hx hv sA hrepA
    obtain ⟨rfl, -⟩ := Exec.prim_inv hexP
    subst eP
    obtain ⟨kB, sB, σB, hkB, hexB, hrepB, hI1, hBt, hBn, hBo, hBr⟩ := hB t ht σA hJ hAt hAn hAo hAr sP hrepP
    obtain ⟨k4, s4, σ4, hk4, hex4, hrep4, e4⟩ := runs_nadd (L := L) (w := w) (σ := σB) hrt hrt hone sB hrepB
    have hexBody := Exec.seq (Exec.seq hexA (Exec.seq hexP hexB)) hex4
    have hturn := run_whileN_turn hloop hcond hexBody
    have hpA : run P w S0 (q + 1 + kA) = atPc sA (oL + 2 + A.len) := by
      rw [run_add, run_add, hq, run_whileN_enter hloop hcond, exec_sim hexA _ hAc]
    have hpP : run P w S0 (q + 1 + kA + 1) = atPc sP (oL + 2 + A.len + (play L x v).len) := by
      rw [run_add, hpA, exec_sim hexP _ hPc]
    refine ⟨q + 1 + kA, ⟨?_, ?_, ?_⟩, by omega, q + (1 + (kA + (1 + kB) + k4 + 1)),
      ⟨s4, σ4, ?_, hrep4, ?_, ?_, ?_, ?_, ?_⟩,
      by omega⟩
    · rw [hpA, atPc_rounds, hrepA.rounds, hAr]
    · rw [hpP, atPc_rounds, hrepP.rounds, hAr]
    · rw [hpP, atPc_pts, hrepP.pts]
      show Function.update σA.pts σA.rounds (WithLp.toLp 2 (σA.vec v)) t = pt t
      rw [hAr, Function.update_self, hAv]
    · rw [run_add, hq, hturn]
    · subst e4; rw [hBt, hBo]; exact hI1
    · subst e4; simp [hBt, hBo]
    · subst e4; simp [Ne.symm hrtn, hBn]
    · subst e4; simp [Ne.symm hrto, hBo]
    · subst e4; exact hBr
  have hq : ∀ t < n, ∃ q, Claim t q ∧ (t = 0 → q ≤ Ks + K0 + 1) ∧
      (∀ u, t = u + 1 → ∃ p, PlayAt u p ∧ q ≤ p + KB + 3) := by
    intro t
    induction t with
    | zero =>
      intro _
      obtain ⟨q, hq0, hqb⟩ := hinit
      exact ⟨q, hq0, fun _ => hqb, fun u hu => absurd hu (by omega)⟩
    | succ t ih =>
      intro ht
      obtain ⟨q, hqc, -, -⟩ := ih (by omega)
      obtain ⟨p, hp, -, q', hq', hq'b⟩ := hstep t (by omega) q hqc
      refine ⟨q', hq', fun h => absurd h (by omega), fun u hu => ?_⟩
      obtain rfl : u = t := by omega
      exact ⟨p, hp, hq'b⟩
  have hplay : ∀ t < n, ∃ q p, PlayAt t p ∧ p ≤ q + 1 + KA ∧ (t = 0 → q ≤ Ks + K0 + 1) ∧
      (∀ u, t = u + 1 → ∃ p', PlayAt u p' ∧ q ≤ p' + KB + 3) := by
    intro t ht
    obtain ⟨q, hqc, h0, h1⟩ := hq t ht
    obtain ⟨p, hp, hpq, -⟩ := hstep t ht q hqc
    exact ⟨q, p, hp, hpq, h0, h1⟩
  refine ⟨costOK_of_plays P w S0 n _ _ ?_ ?_, fun t ht => ?_⟩
  · obtain ⟨q, p, ⟨-, hp1, -⟩, hpq, h0, -⟩ := hplay 0 hn
    refine ⟨p, hp1, ?_⟩
    rw [Nat.ceil_natCast]
    have := h0 rfl
    omega
  · intro t ht1 htn
    obtain ⟨q, p, ⟨-, hp1, -⟩, hpq, -, h1⟩ := hplay t htn
    obtain ⟨p', ⟨hp'0, -, -⟩, hqp'⟩ := h1 (t - 1) (by omega)
    refine ⟨p', p, hp'0, hp1, ?_⟩
    rw [Nat.ceil_natCast]
    omega
  · obtain ⟨q, p, ⟨-, hp1, hpts⟩, -⟩ := hplay t ht
    rw [played_eq P w S0 (p + 1) t (by rw [hp1]; omega), hpts]

end AdversarialBco.Poly.Mach
