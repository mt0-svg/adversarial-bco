/-
Copyright (c) 2026 mt0-svg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mt0-svg
-/
module

public import AdversarialBco.Bit.RoutM

@[expose] public section

/-!
# Facts on the integer problem of ELL-R and FRAME

Pure facts used by the machine version of ELL-R, BIS-R and FRAME: the size of the integers of the problem, the constants
`R̄`, `j`, `λ` as integer computations, and small lemmas on lists and sums.
-/

namespace AdversarialBco.Bit.Transfer

open AdversarialBco.Bit.RQ Matrix

theorem ellMx_le {d : ℕ} (I : EllI d) :
    (∀ i j, (I.α i j).natAbs ≤ ellMx I) ∧ (∀ i, (I.β i).natAbs ≤ ellMx I) ∧
    (∀ i j, (I.H i j).natAbs ≤ ellMx I) ∧ (∀ i j, (I.P i j).natAbs ≤ ellMx I) ∧
    (∀ j, (I.g j).natAbs ≤ ellMx I) ∧ (∀ j, (I.f j).natAbs ≤ ellMx I) ∧ I.ℓ.natAbs ≤ ellMx I ∧
    I.Df ≤ ellMx I ∧ I.R.num.natAbs ≤ ellMx I ∧ I.R.den ≤ ellMx I ∧ I.r.num.natAbs ≤ ellMx I ∧
    I.r.den ≤ ellMx I ∧ I.e.num.natAbs ≤ ellMx I ∧ I.e.den ≤ ellMx I := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    have h1 : (I.α i j).natAbs ≤ (Finset.univ.sup fun j => (I.α i j).natAbs) :=
      Finset.le_sup (f := fun j => (I.α i j).natAbs) (Finset.mem_univ j)
    have h2 : (Finset.univ.sup fun j => (I.α i j).natAbs) ≤
      max (Finset.univ.sup fun j => (I.α i j).natAbs) (I.β i).natAbs :=
      le_max_left _ _
    have h3 : max (Finset.univ.sup fun j => (I.α i j).natAbs) (I.β i).natAbs ≤
      (Finset.univ.sup fun i => max (Finset.univ.sup fun j => (I.α i j).natAbs) (I.β i).natAbs) :=
      Finset.le_sup (f := fun i => max (Finset.univ.sup fun j => (I.α i j).natAbs) (I.β i).natAbs)
        (Finset.mem_univ i)
    have h4 : (Finset.univ.sup fun i => max (Finset.univ.sup fun j => (I.α i j).natAbs) (I.β i).natAbs) ≤ ellMx I := by
      unfold ellMx; exact le_max_left _ _
    exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 h4))
  · intro i
    have h1 : (I.β i).natAbs ≤ max (Finset.univ.sup fun j => (I.α i j).natAbs) (I.β i).natAbs :=
      le_max_right _ _
    have h2 : max (Finset.univ.sup fun j => (I.α i j).natAbs) (I.β i).natAbs ≤
      (Finset.univ.sup fun i => max (Finset.univ.sup fun j => (I.α i j).natAbs) (I.β i).natAbs) :=
      Finset.le_sup (f := fun i => max (Finset.univ.sup fun j => (I.α i j).natAbs) (I.β i).natAbs)
        (Finset.mem_univ i)
    have h3 : (Finset.univ.sup fun i => max (Finset.univ.sup fun j => (I.α i j).natAbs) (I.β i).natAbs) ≤ ellMx I := by
      unfold ellMx; exact le_max_left _ _
    exact Nat.le_trans h1 (Nat.le_trans h2 h3)
  · intro i j
    have h1 : (I.H i j).natAbs ≤ max (I.H i j).natAbs (I.P i j).natAbs :=
      le_max_left _ _
    have h2 : max (I.H i j).natAbs (I.P i j).natAbs ≤
      (Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs) :=
      Finset.le_sup (f := fun j => max (I.H i j).natAbs (I.P i j).natAbs) (Finset.mem_univ j)
    have h3 : (Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs) ≤
      (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs) :=
      Finset.le_sup (f := fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs)
        (Finset.mem_univ i)
    have h4 : (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs) ≤ ellMx I := by
      unfold ellMx
      -- goal: B ≤ max A (max B (max C D))
      -- B ≤ max B (max C D) by le_max_left, then max B (max C D) ≤ max A (max B (max C D)) by le_max_right
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 h4))
  · intro i j
    have h1 : (I.P i j).natAbs ≤ max (I.H i j).natAbs (I.P i j).natAbs :=
      le_max_right _ _
    have h2 : max (I.H i j).natAbs (I.P i j).natAbs ≤
      (Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs) :=
      Finset.le_sup (f := fun j => max (I.H i j).natAbs (I.P i j).natAbs) (Finset.mem_univ j)
    have h3 : (Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs) ≤
      (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs) :=
      Finset.le_sup (f := fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs)
        (Finset.mem_univ i)
    have h4 : (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs) ≤ ellMx I := by
      unfold ellMx
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 h4))
  · intro j
    have h1 : (I.g j).natAbs ≤ max (I.g j).natAbs (I.f j).natAbs :=
      le_max_left _ _
    have h2 : max (I.g j).natAbs (I.f j).natAbs ≤
      (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs) :=
      Finset.le_sup (f := fun j => max (I.g j).natAbs (I.f j).natAbs) (Finset.mem_univ j)
    have h3 : (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs) ≤ ellMx I := by
      unfold ellMx
      -- goal: C ≤ max A (max B (max C D))
      -- C ≤ max C D by le_max_left, max C D ≤ max B (max C D) by le_max_right, max B (max C D) ≤ ellMx I by le_max_right
      exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    exact Nat.le_trans h1 (Nat.le_trans h2 h3)
  · intro j
    have h1 : (I.f j).natAbs ≤ max (I.g j).natAbs (I.f j).natAbs :=
      le_max_right _ _
    have h2 : max (I.g j).natAbs (I.f j).natAbs ≤
      (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs) :=
      Finset.le_sup (f := fun j => max (I.g j).natAbs (I.f j).natAbs) (Finset.mem_univ j)
    have h3 : (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs) ≤ ellMx I := by
      unfold ellMx
      exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    exact Nat.le_trans h1 (Nat.le_trans h2 h3)
  · have h1 : I.ℓ.natAbs ≤ max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
      (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))) :=
      le_max_left _ _
    have h2 : max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
      (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))) ≤
      max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
        (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
          (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))))) :=
      le_max_right _ _
    have h3 : max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
        (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
          (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))))) ≤
      max (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs)
        (max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
          (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
            (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))))) :=
      le_max_right _ _
    have h4 : max (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs)
        (max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
          (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
            (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))))) ≤
      ellMx I := by
      unfold ellMx; exact le_max_right _ _
    exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 h4))
  · have h1 : I.Df ≤ max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
      (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))) := by
      -- I.Df ≤ max I.Df ... ≤ max I.ℓ.natAbs (max I.Df ...)
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have h2 : max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
      (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))) ≤
      max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
        (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
          (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))))) :=
      le_max_right _ _
    have h3 : max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
        (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
          (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))))) ≤
      max (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs)
        (max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
          (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
            (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))))) :=
      le_max_right _ _
    have h4 : max (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs)
        (max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
          (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
            (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))))) ≤
      ellMx I := by
      unfold ellMx; exact le_max_right _ _
    exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 h4))
  · have h1 : I.R.num.natAbs ≤ max I.R.num.natAbs I.R.den :=
      le_max_left _ _
    have h2 : max I.R.num.natAbs I.R.den ≤
      max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)) :=
      le_max_left _ _
    have h3 : max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)) ≤
      max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))) :=
      le_max_right _ _
    have h4 : max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))) ≤
      max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))) :=
      le_max_right _ _
    have h5 : max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
      (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))) ≤
      max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
        (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
          (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))))) :=
      le_max_right _ _
    have h6 : max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
        (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
          (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))))) ≤
      max (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs)
        (max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
          (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
            (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))))) :=
      le_max_right _ _
    have h7 : max (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs)
        (max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
          (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
            (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))))) ≤
      ellMx I := by
      unfold ellMx; exact le_max_right _ _
    exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 (Nat.le_trans h4 (Nat.le_trans h5 (Nat.le_trans h6 h7)))))
  · have h1 : I.R.den ≤ max I.R.num.natAbs I.R.den :=
      le_max_right _ _
    have h2 : max I.R.num.natAbs I.R.den ≤
      max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)) :=
      le_max_left _ _
    have h3 : max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)) ≤
      max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))) :=
      le_max_right _ _
    have h4 : max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))) ≤
      max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))) :=
      le_max_right _ _
    have h5 : max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
      (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))) ≤
      max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
        (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
          (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))))) :=
      le_max_right _ _
    have h6 : max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
        (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
          (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))))) ≤
      max (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs)
        (max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
          (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
            (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))))) :=
      le_max_right _ _
    have h7 : max (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs)
        (max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
          (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
            (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))))) ≤
      ellMx I := by
      unfold ellMx; exact le_max_right _ _
    exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 (Nat.le_trans h4 (Nat.le_trans h5 (Nat.le_trans h6 h7)))))
  · have h1 : I.r.num.natAbs ≤ max I.r.num.natAbs I.r.den :=
      le_max_left _ _
    have h2 : max I.r.num.natAbs I.r.den ≤
      max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den) :=
      le_max_left _ _
    have h3 : max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den) ≤
      max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)) :=
      le_max_right _ _
    have h4 : max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)) ≤
      max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))) :=
      le_max_right _ _
    have h5 : max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))) ≤
      max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))) :=
      le_max_right _ _
    have h6 : max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
      (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))) ≤
      max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
        (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
          (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))))) :=
      le_max_right _ _
    have h7 : max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
        (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
          (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))))) ≤
      max (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs)
        (max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
          (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
            (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))))) :=
      le_max_right _ _
    have h8 : max (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs)
        (max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
          (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
            (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))))) ≤
      ellMx I := by
      unfold ellMx; exact le_max_right _ _
    exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 (Nat.le_trans h4 (Nat.le_trans h5 (Nat.le_trans h6 (Nat.le_trans h7 h8))))))
  · have h1 : I.r.den ≤ max I.r.num.natAbs I.r.den :=
      le_max_right _ _
    have h2 : max I.r.num.natAbs I.r.den ≤
      max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den) :=
      le_max_left _ _
    have h3 : max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den) ≤
      max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)) :=
      le_max_right _ _
    have h4 : max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)) ≤
      max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))) :=
      le_max_right _ _
    have h5 : max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))) ≤
      max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))) :=
      le_max_right _ _
    have h6 : max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
      (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))) ≤
      max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
        (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
          (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))))) :=
      le_max_right _ _
    have h7 : max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
        (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
          (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))))) ≤
      max (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs)
        (max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
          (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
            (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))))) :=
      le_max_right _ _
    have h8 : max (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs)
        (max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
          (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
            (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))))) ≤
      ellMx I := by
      unfold ellMx; exact le_max_right _ _
    exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 (Nat.le_trans h4 (Nat.le_trans h5 (Nat.le_trans h6 (Nat.le_trans h7 h8))))))
  · have h1 : I.e.num.natAbs ≤ max I.e.num.natAbs I.e.den :=
      le_max_left _ _
    have h2 : max I.e.num.natAbs I.e.den ≤
      max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den) :=
      le_max_right _ _
    have h3 : max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den) ≤
      max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)) :=
      le_max_right _ _
    have h4 : max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)) ≤
      max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))) :=
      le_max_right _ _
    have h5 : max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))) ≤
      max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))) :=
      le_max_right _ _
    have h6 : max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
      (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))) ≤
      max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
        (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
          (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))))) :=
      le_max_right _ _
    have h7 : max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
        (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
          (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))))) ≤
      max (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs)
        (max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
          (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
            (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))))) :=
      le_max_right _ _
    have h8 : max (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs)
        (max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
          (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
            (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))))) ≤
      ellMx I := by
      unfold ellMx; exact le_max_right _ _
    exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 (Nat.le_trans h4 (Nat.le_trans h5 (Nat.le_trans h6 (Nat.le_trans h7 h8))))))
  · have h1 : I.e.den ≤ max I.e.num.natAbs I.e.den :=
      le_max_right _ _
    have h2 : max I.e.num.natAbs I.e.den ≤
      max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den) :=
      le_max_right _ _
    have h3 : max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den) ≤
      max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)) :=
      le_max_right _ _
    have h4 : max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)) ≤
      max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))) :=
      le_max_right _ _
    have h5 : max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))) ≤
      max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))) :=
      le_max_right _ _
    have h6 : max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
      (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))) ≤
      max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
        (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
          (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))))) :=
      le_max_right _ _
    have h7 : max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
        (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
          (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))))) ≤
      max (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs)
        (max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
          (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
            (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))))) :=
      le_max_right _ _
    have h8 : max (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs)
        (max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
          (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den)
            (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))))) ≤
      ellMx I := by
      unfold ellMx; exact le_max_right _ _
    exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 (Nat.le_trans h4 (Nat.le_trans h5 (Nat.le_trans h6 (Nat.le_trans h7 h8))))))

theorem ellRb_lt {d : ℕ} (I : EllI d) : I.Rb < 2 ^ ellSz I := by
  -- I.Rb = ⌈I.R⌉₊, ellSz I = (ellMx I).size
  -- Goal: ⌈I.R⌉₊ < 2 ^ (ellMx I).size
  have hRb_le_num_natAbs : I.Rb ≤ I.R.num.natAbs := by
    rw [EllI.Rb]
    rw [Nat.ceil_le]
    -- Goal: I.R ≤ (I.R.num.natAbs : ℚ)
    -- Use the identity I.R = (I.R.num : ℚ) / (I.R.den : ℚ)
    have h_eq := Rat.num_div_den I.R
    -- h_eq : (I.R.num : ℚ) / (I.R.den : ℚ) = I.R
    -- We need to show I.R ≤ (I.R.num.natAbs : ℚ)
    -- First prove the inequality for the expanded form, then use h_eq to relate back
    have h_ineq : (I.R.num : ℚ) / (I.R.den : ℚ) ≤ (I.R.num.natAbs : ℚ) := by
      by_cases hRnonpos : I.R ≤ 0
      · -- I.R ≤ 0: numerator ≤ 0, so the fraction ≤ 0 ≤ natAbs
        have hnum_nonpos : I.R.num ≤ 0 := (Rat.num_nonpos.mpr hRnonpos)
        have hdiv_nonpos : (I.R.num : ℚ) / (I.R.den : ℚ) ≤ 0 := by
          have hnum' : (I.R.num : ℚ) ≤ 0 := by exact_mod_cast hnum_nonpos
          have hden_pos : 0 < (I.R.den : ℚ) := by exact_mod_cast Rat.pos I.R
          exact div_nonpos_of_nonpos_of_nonneg hnum' (by linarith)
        have hnatAbs_nonneg : 0 ≤ (I.R.num.natAbs : ℚ) := by exact_mod_cast Nat.zero_le _
        linarith
      · -- I.R > 0: numerator ≥ 0, and natAbs = num
        have hnum_nonneg : 0 ≤ I.R.num := (Rat.num_nonneg.mpr (by linarith))
        have hnum_nonneg' : 0 ≤ (I.R.num : ℚ) := by exact_mod_cast hnum_nonneg
        have hnatAbs_eq : (I.R.num.natAbs : ℚ) = (I.R.num : ℚ) := by
          have h := Int.natAbs_of_nonneg hnum_nonneg
          -- h : (I.R.num.natAbs : ℤ) = I.R.num
          -- Cast to ℚ
          simpa using congrArg (fun (x : ℤ) => (x : ℚ)) h
        rw [hnatAbs_eq]
        exact div_nat_le_self_of_nonnneg hnum_nonneg' I.R.den
    -- Now use h_eq to rewrite the goal
    -- Goal: I.R ≤ (I.R.num.natAbs : ℚ)
    -- h_eq: (I.R.num : ℚ) / (I.R.den : ℚ) = I.R
    -- So h_eq.symm: I.R = (I.R.num : ℚ) / (I.R.den : ℚ)
    -- We can rewrite the goal using h_eq.symm only on the LHS
    -- Using `conv` to target only the left-hand side
    conv =>
      lhs
      rw [← h_eq]
    -- Goal: (I.R.num : ℚ) / (I.R.den : ℚ) ≤ (I.R.num.natAbs : ℚ)
    exact h_ineq
  have hnum_natAbs_le_ellMx : I.R.num.natAbs ≤ ellMx I := by
    unfold ellMx
    -- Build the chain of inequalities through the max hierarchy
    -- F = max I.R.num.natAbs I.R.den
    -- G = max I.r.num.natAbs I.r.den
    -- H = max I.e.num.natAbs I.e.den
    -- Chain: F ≤ max F (max G H) ≤ max E (max F (max G H)) ≤ ... ≤ ellMx I
    have h1 : I.R.num.natAbs ≤ max I.R.num.natAbs I.R.den := le_max_left _ _
    have h2 : max I.R.num.natAbs I.R.den ≤
             max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)) := le_max_left _ _
    have h3 : max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)) ≤
             max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))) := le_max_right _ _
    have h4 : max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))) ≤
             max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))) := le_max_right _ _
    have h5 : max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))) ≤
             max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
               (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))))) := le_max_right _ _
    have h6 : max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
               (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))))) ≤
             max (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs)
               (max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
                 (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))))) := le_max_right _ _
    have h7 : max (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs)
               (max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
                 (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den)))))) ≤
             max (Finset.univ.sup fun i => max (Finset.univ.sup fun j => (I.α i j).natAbs) (I.β i).natAbs)
               (max (Finset.univ.sup fun i => Finset.univ.sup fun j => max (I.H i j).natAbs (I.P i j).natAbs)
                 (max (Finset.univ.sup fun j => max (I.g j).natAbs (I.f j).natAbs)
                   (max I.ℓ.natAbs (max I.Df (max (max I.R.num.natAbs I.R.den) (max (max I.r.num.natAbs I.r.den) (max I.e.num.natAbs I.e.den))))))) := le_max_right _ _
    exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 (Nat.le_trans h4 (Nat.le_trans h5 (Nat.le_trans h6 h7)))))
  -- Now we have: I.Rb ≤ I.R.num.natAbs ≤ ellMx I
  -- And ellMx I < 2 ^ (ellMx I).size = 2 ^ ellSz I
  have h_ellMx_lt : ellMx I < 2 ^ (ellMx I).size := Nat.lt_size_self _
  have h_ellSz : ellSz I = (ellMx I).size := rfl
  rw [h_ellSz]
  -- Goal: I.Rb < 2 ^ (ellMx I).size
  -- Chain: I.Rb ≤ I.R.num.natAbs ≤ ellMx I < 2 ^ (ellMx I).size
  exact Nat.lt_of_le_of_lt (Nat.le_trans hRb_le_num_natAbs hnum_natAbs_le_ellMx) h_ellMx_lt

theorem natCeil_div_eq (n k : ℤ) (hk : 0 < k) :
    ⌈(n : ℚ) / k⌉₊ = ((n + k - 1) / k).toNat := by
  by_cases hn : n ≤ 0
  · -- Case n ≤ 0
    have hdiv : (n : ℚ) / k ≤ 0 := by
      have hn' : (n : ℚ) ≤ 0 := by exact mod_cast hn
      have hk' : (0 : ℚ) ≤ k := by exact mod_cast hk.le
      exact div_nonpos_of_nonpos_of_nonneg hn' hk'
    have hceil : ⌈(n : ℚ) / k⌉₊ = 0 := by
      rw [Nat.ceil_eq_zero]
      exact hdiv
    have hdiv_int : (n + k - 1) / k ≤ 0 := by
      have hlt : n + k - 1 < 1 * k := by
        -- n + k - 1 < k = 1 * k because n ≤ 0
        have : n + k - 1 ≤ k - 1 := by omega
        omega
      have h := Int.ediv_lt_of_lt_mul hk hlt
      -- h : (n + k - 1) / k < 1
      -- Since integer division, this implies ≤ 0
      omega
    have htoNat : ((n + k - 1) / k).toNat = 0 := by
      rw [Int.toNat_eq_zero]
      exact hdiv_int
    rw [hceil, htoNat]
  · -- Case 0 < n
    have hnpos : 0 < n := by omega
    set c := (n + k - 1) / k with hc_def
    have hc_nonneg : 0 ≤ c := by
      have hsum : 0 ≤ n + k - 1 := by omega
      exact Int.ediv_nonneg hsum hk.le
    -- c * k ≤ n + k - 1
    have hle : c * k ≤ n + k - 1 := by
      rw [hc_def]
      exact Int.ediv_mul_le (n + k - 1) (by omega : k ≠ 0)
    -- n + k - 1 < (c + 1) * k
    have hlt : n + k - 1 < (c + 1) * k := by
      rw [hc_def]
      exact Int.lt_ediv_add_one_mul_self (n + k - 1) hk
    -- From hle: c * k ≤ n + k - 1, so (c - 1) * k = c * k - k ≤ n - 1 < n
    have h_ineq1 : (c - 1) * k < n := by
      have : c * k - k ≤ n - 1 := by omega
      have hpos : c * k - k = (c - 1) * k := by ring
      rw [hpos] at this
      omega
    -- From hlt: n + k - 1 < (c + 1) * k = c * k + k, so n < c * k + 1, hence n ≤ c * k
    have h_ineq2 : n ≤ c * k := by
      have : n < c * k + 1 := by
        -- (c + 1) * k = c * k + k
        have h_expand : (c + 1) * k = c * k + k := by ring
        rw [h_expand] at hlt
        omega
      omega
    -- Convert to ℚ inequalities
    have hk_rat_pos : (0 : ℚ) < k := by exact mod_cast hk
    have h_rat_le : (n : ℚ) / (k : ℚ) ≤ (c : ℚ) := by
      have hcast : (n : ℚ) ≤ (c : ℚ) * (k : ℚ) := by exact mod_cast h_ineq2
      -- n/k ≤ c  ↔  n ≤ c * k (since k > 0)
      rw [div_le_iff₀ hk_rat_pos]
      exact hcast
    have h_rat_lt : (c - 1 : ℚ) < (n : ℚ) / (k : ℚ) := by
      have hcast : (c - 1 : ℚ) * (k : ℚ) < (n : ℚ) := by exact mod_cast h_ineq1
      -- c-1 < n/k  ↔  (c-1)*k < n (since k > 0)
      rw [lt_div_iff₀ hk_rat_pos]
      exact hcast
    -- Now use Int.ceil_eq_iff
    have hceil_int : ⌈(n : ℚ) / (k : ℚ)⌉ = c := by
      rw [Int.ceil_eq_iff]
      constructor
      · -- c - 1 < n/k
        -- We have (c - 1 : ℚ) < n/k, but we need (c : ℤ) - 1 < n/k in ℚ
        -- Int.ceil_eq_iff expects: (z : ℤ), and gives condition with (z : ℝ) - 1 < a ∧ a ≤ (z : ℝ)
        -- Here z = c, a = (n : ℚ) / (k : ℚ)
        -- So we need: (c : ℚ) - 1 < (n : ℚ) / (k : ℚ) ∧ (n : ℚ) / (k : ℚ) ≤ (c : ℚ)
        -- We have h_rat_lt: (c - 1 : ℚ) < n/k
        -- But we need (c : ℚ) - 1 < n/k, which is the same as (c - 1 : ℚ) < n/k
        simpa using h_rat_lt
      · -- n/k ≤ c
        simpa using h_rat_le
    -- Now use Int.ceil_toNat to relate to Nat.ceil
    calc
      ⌈(n : ℚ) / k⌉₊ = (⌈(n : ℚ) / (k : ℚ)⌉).toNat := by rw [Int.ceil_toNat]
      _ = c.toNat := by rw [hceil_int]
      _ = ((n + k - 1) / k).toNat := by rw [hc_def]

theorem ellJ_frac (trP F1 rn en : ℤ) (Rb Df rd ed : ℕ) (hF1 : 0 ≤ F1) (hrn : 0 < rn)
    (hen : 0 < en) (hrd : 0 < rd) (hed : 0 < ed) :
    let LG : ℚ := (trP : ℚ) * Rb + (F1 : ℚ) / Df
    let θ : ℚ := if 3 * LG * Rb ≤ (en : ℚ) / ed then 1 else (en : ℚ) / ed / (3 * LG * Rb)
    let LGn : ℤ := if Df = 0 then trP * Rb else trP * Rb * Df + F1
    let LGd : ℤ := if Df = 0 then 1 else Df
    let Nx : ℤ := (if 3 * LGn * Rb * ed ≤ en * LGd then 1 else 3 * LGn * Rb * ed) * (if rn ≤ rd then rd else 1)
    let Dx : ℤ := (if 3 * LGn * Rb * ed ≤ en * LGd then 1 else LGd * en) * (if rn ≤ rd then rn else 1)
    0 < Nx ∧ 0 < Dx ∧ 1 / (θ * min ((rn : ℚ) / rd) 1) = (Nx : ℚ) / Dx := by
  intro LG θ LGn LGd Nx Dx
  have hpos_rn : (0 : ℚ) < (rn : ℚ) := by exact_mod_cast hrn
  have hpos_rd : (0 : ℚ) < (rd : ℚ) := by exact_mod_cast hrd
  have hpos_en : (0 : ℚ) < (en : ℚ) := by exact_mod_cast hen
  have hpos_ed : (0 : ℚ) < (ed : ℚ) := by exact_mod_cast hed
  -- LG = LGn / LGd in ℚ
  have hLG_eq : LG = (LGn : ℚ) / (LGd : ℚ) := by
    dsimp [LG, LGn, LGd]
    by_cases hDf : Df = 0
    · simp [hDf]
    · simp [hDf]
      have hDf_ne : (Df : ℚ) ≠ 0 := by exact_mod_cast hDf
      field_simp [hDf_ne]
  -- LGd > 0 in ℚ
  have hLGd_pos : 0 < (LGd : ℚ) := by
    dsimp [LGd]
    by_cases hDf : Df = 0
    · simp [hDf]
    · simp [hDf]
      have hpos_Df_nat : 0 < Df := Nat.pos_of_ne_zero hDf
      exact_mod_cast hpos_Df_nat
  -- Equivalence: 3 * LG * Rb ≤ en/ed ↔ 3 * LGn * Rb * ed ≤ en * LGd
  have h_equiv : (3 * LG * (Rb : ℚ) ≤ (en : ℚ) / (ed : ℚ)) ↔
      (3 * LGn * (Rb : ℤ) * (ed : ℤ) ≤ (en : ℤ) * (LGd : ℤ)) := by
    rw [hLG_eq]
    constructor
    · intro h
      have h' : ((3 : ℚ) * (LGn : ℚ) * (Rb : ℚ)) / (LGd : ℚ) ≤ (en : ℚ) / (ed : ℚ) := by
        calc
          ((3 : ℚ) * (LGn : ℚ) * (Rb : ℚ)) / (LGd : ℚ) = 3 * ((LGn : ℚ) / (LGd : ℚ)) * (Rb : ℚ) := by
            field_simp [ne_of_gt hLGd_pos]
          _ ≤ (en : ℚ) / (ed : ℚ) := h
      have hdiv := (div_le_div_iff₀ hLGd_pos hpos_ed).mp h'
      exact_mod_cast hdiv
    · intro h
      have h' : ((3 : ℚ) * (LGn : ℚ) * (Rb : ℚ) * (ed : ℚ)) ≤ (en : ℚ) * (LGd : ℚ) := by exact_mod_cast h
      have h'' : ((3 : ℚ) * (LGn : ℚ) * (Rb : ℚ)) / (LGd : ℚ) ≤ (en : ℚ) / (ed : ℚ) :=
        (div_le_div_iff₀ hLGd_pos hpos_ed).mpr h'
      calc
        3 * ((LGn : ℚ) / (LGd : ℚ)) * (Rb : ℚ) = ((3 : ℚ) * (LGn : ℚ) * (Rb : ℚ)) / (LGd : ℚ) := by
          field_simp [ne_of_gt hLGd_pos]
        _ ≤ (en : ℚ) / (ed : ℚ) := h''
  -- Case split on the test condition
  by_cases htest : 3 * LG * (Rb : ℚ) ≤ (en : ℚ) / (ed : ℚ)
  · -- Test true: θ = 1, Nx and Dx use the first branch
    have htest_int : 3 * LGn * (Rb : ℤ) * (ed : ℤ) ≤ (en : ℤ) * (LGd : ℤ) := h_equiv.mp htest
    have hθ : θ = 1 := by dsimp [θ]; simp [htest]
    have hNx_expr : Nx = (if (rn : ℤ) ≤ (rd : ℤ) then (rd : ℤ) else 1) := by
      dsimp [Nx]; simp [htest_int]
    have hDx_expr : Dx = (if (rn : ℤ) ≤ (rd : ℤ) then (rn : ℤ) else 1) := by
      dsimp [Dx]; simp [htest_int]
    have hNx_pos : 0 < Nx := by
      rw [hNx_expr]
      by_cases hrnrd : (rn : ℤ) ≤ (rd : ℤ)
      · simp [hrnrd]; exact_mod_cast hrd
      · simp [hrnrd]
    have hDx_pos : 0 < Dx := by
      rw [hDx_expr]
      by_cases hrnrd : (rn : ℤ) ≤ (rd : ℤ)
      · simp [hrnrd]; exact_mod_cast hrn
      · simp [hrnrd]
    have h_eq : 1 / (θ * min ((rn : ℚ) / (rd : ℚ)) 1) = (Nx : ℚ) / (Dx : ℚ) := by
      rw [hθ, hNx_expr, hDx_expr]
      by_cases hrnrd : (rn : ℚ) ≤ (rd : ℚ)
      · have hmin : min ((rn : ℚ) / (rd : ℚ)) 1 = (rn : ℚ) / (rd : ℚ) :=
          min_eq_left ((div_le_one hpos_rd).mpr hrnrd)
        have hrnrd_ℤ : (rn : ℤ) ≤ (rd : ℤ) := by exact_mod_cast hrnrd
        simp [hmin, hrnrd_ℤ]
      · have hrd_lt_rn : (rd : ℚ) < (rn : ℚ) := by
          exact_mod_cast (not_le.mp hrnrd)
        have hmin : min ((rn : ℚ) / (rd : ℚ)) 1 = 1 :=
          min_eq_right ((one_le_div hpos_rd).mpr (le_of_lt hrd_lt_rn))
        have h_not_rnrd_ℤ : ¬ (rn : ℤ) ≤ (rd : ℤ) := by exact_mod_cast hrnrd
        simp [hmin, h_not_rnrd_ℤ]
    exact And.intro hNx_pos (And.intro hDx_pos h_eq)
  · -- Test false: θ = (en/ed)/(3*LG*Rb), Nx and Dx use the else branch
    have htest_int : ¬ (3 * LGn * (Rb : ℤ) * (ed : ℤ) ≤ (en : ℤ) * (LGd : ℤ)) := mt h_equiv.mpr htest
    -- 3 * LG * Rb > 0 in ℚ
    have hpos_3LG_Rb : 0 < 3 * LG * (Rb : ℚ) := by
      have hpos_en_div_ed : 0 < (en : ℚ) / (ed : ℚ) := div_pos hpos_en hpos_ed
      have hlt : (en : ℚ) / (ed : ℚ) < 3 * LG * (Rb : ℚ) := not_le.mp htest
      exact lt_trans hpos_en_div_ed hlt
    have hθ : θ = ((en : ℚ) / (ed : ℚ)) / (3 * LG * (Rb : ℚ)) := by
      dsimp [θ]; simp [htest]
    -- 3 * LGn * Rb * ed > 0 in ℤ
    have hpos_3LGn_Rb_ed : 0 < 3 * LGn * (Rb : ℤ) * (ed : ℤ) := by
      have hpos_LGd_int : 0 < (LGd : ℤ) := by exact_mod_cast hLGd_pos
      have hpos_en_LGd : 0 < (en : ℤ) * (LGd : ℤ) := mul_pos hen hpos_LGd_int
      have hlt : (en : ℤ) * (LGd : ℤ) < 3 * LGn * (Rb : ℤ) * (ed : ℤ) := not_le.mp htest_int
      exact lt_trans hpos_en_LGd hlt
    have hNx_expr : Nx = (3 * LGn * (Rb : ℤ) * (ed : ℤ)) *
        (if (rn : ℤ) ≤ (rd : ℤ) then (rd : ℤ) else 1) := by
      dsimp [Nx]; simp [htest_int]
    have hDx_expr : Dx = ((LGd : ℤ) * (en : ℤ)) *
        (if (rn : ℤ) ≤ (rd : ℤ) then (rn : ℤ) else 1) := by
      dsimp [Dx]; simp [htest_int]
    have hNx_pos : 0 < Nx := by
      rw [hNx_expr]
      by_cases hrnrd : (rn : ℤ) ≤ (rd : ℤ)
      · simp [hrnrd]
        have hpos_rd_int : 0 < (rd : ℤ) := by exact_mod_cast hrd
        exact mul_pos hpos_3LGn_Rb_ed hpos_rd_int
      · simp [hrnrd]; exact hpos_3LGn_Rb_ed
    have hDx_pos : 0 < Dx := by
      rw [hDx_expr]
      by_cases hrnrd : (rn : ℤ) ≤ (rd : ℤ)
      · simp [hrnrd]
        have hpos_rn_int : 0 < (rn : ℤ) := by exact_mod_cast hrn
        have hpos_LGd_int : 0 < (LGd : ℤ) := by exact_mod_cast hLGd_pos
        exact mul_pos (mul_pos hpos_LGd_int hen) hpos_rn_int
      · simp [hrnrd]
        have hpos_LGd_int : 0 < (LGd : ℤ) := by exact_mod_cast hLGd_pos
        exact mul_pos hpos_LGd_int hen
    have h_eq : 1 / (θ * min ((rn : ℚ) / (rd : ℚ)) 1) = (Nx : ℚ) / (Dx : ℚ) := by
      rw [hθ, hNx_expr, hDx_expr]
      by_cases hrnrd_ℤ : (rn : ℤ) ≤ (rd : ℤ)
      · have hrnrd_ℚ : (rn : ℚ) ≤ (rd : ℚ) := by exact_mod_cast hrnrd_ℤ
        have hmin : min ((rn : ℚ) / (rd : ℚ)) 1 = (rn : ℚ) / (rd : ℚ) :=
          min_eq_left ((div_le_one hpos_rd).mpr hrnrd_ℚ)
        simp [hmin, hrnrd_ℤ]
        rw [hLG_eq]
        field_simp [ne_of_gt hpos_rn, ne_of_gt hpos_rd, ne_of_gt hpos_ed, ne_of_gt hLGd_pos,
          ne_of_gt hpos_3LG_Rb]
      · have hrd_lt_rn_ℚ : (rd : ℚ) < (rn : ℚ) := by
          have h := not_le.mp hrnrd_ℤ
          exact_mod_cast h
        have hmin : min ((rn : ℚ) / (rd : ℚ)) 1 = 1 :=
          min_eq_right ((one_le_div hpos_rd).mpr (le_of_lt hrd_lt_rn_ℚ))
        simp [hmin, hrnrd_ℤ]
        rw [hLG_eq]
        field_simp [ne_of_gt hpos_en, ne_of_gt hpos_ed, ne_of_gt hLGd_pos, ne_of_gt hpos_3LG_Rb]
    exact And.intro hNx_pos (And.intro hDx_pos h_eq)

theorem clog_bounds :
    (∀ n : ℕ, Nat.clog 2 n ≤ n.size) ∧ (∀ n : ℕ, Nat.clog 2 n ≤ n) ∧
    ∀ d : ℕ, 1 ≤ d → Nat.clog 2 (d ^ 2 * (d + 1)) ≤ 3 * d := by
  have h2pos : 1 < 2 := by norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rw [Nat.clog_le_iff_le_pow h2pos]
    exact (Nat.lt_size_self n).le
  · intro n
    rw [Nat.clog_le_iff_le_pow h2pos]
    exact (Nat.lt_two_pow_self (n := n)).le
  · intro d hd
    rw [Nat.clog_le_iff_le_pow h2pos]
    have h_pow_eq : (2 : ℕ) ^ (3 * d) = (8 : ℕ) ^ d := by
      calc
        (2 : ℕ) ^ (3 * d) = ((2 : ℕ) ^ 3) ^ d := by rw [Nat.pow_mul]
        _ = (8 : ℕ) ^ d := by norm_num
    rw [h_pow_eq]
    have hineq : ∀ d : ℕ, 1 ≤ d → d ^ 2 * (d + 1) ≤ (8 : ℕ) ^ d := by
      refine Nat.le_induction ?base ?step
      · norm_num
      · intro m hm ih
        have hcalc : (m + 1) ^ 2 * (m + 2) ≤ 8 * (m ^ 2 * (m + 1)) := by
          nlinarith
        calc
          (m + 1) ^ 2 * (m + 2) ≤ 8 * (m ^ 2 * (m + 1)) := hcalc
          _ ≤ 8 * ((8 : ℕ) ^ m) := by
            nlinarith
          _ = (8 : ℕ) ^ (m + 1) := by ring
    exact hineq d hd

theorem find_finRange_some {m : ℕ} (p : Fin m → Bool) (i : Fin m) (hi : p i = true)
    (hlt : ∀ j : Fin m, j < i → p j = false) : (List.finRange m).find? p = some i := by
  rw [← List.ofFn_id m]
  apply (List.find?_ofFn_eq_some (f := id) (p := p) (b := i)).mpr
  refine ⟨hi, i, rfl, ?_⟩
  intro j hj
  have hfalse := hlt j hj
  simp [hfalse]


theorem clog_spec (n c : ℕ) (h1 : n ≤ 2 ^ c) (h2 : c = 0 ∨ 2 ^ (c - 1) < n) :
    Nat.clog 2 n = c := by
  have hb : 1 < 2 := by norm_num
  have hle : Nat.clog 2 n ≤ c := by
    rw [Nat.clog_le_iff_le_pow hb]
    exact h1
  rcases h2 with (hc | hlt)
  · subst hc; omega
  · have h_lt : c - 1 < Nat.clog 2 n :=
      (Nat.lt_clog_iff_pow_lt hb).mpr hlt
    omega

theorem ellRb_eq {d : ℕ} (I : EllI d) :
    I.Rb = ((I.R.num + (I.R.den : ℤ) - 1) / (I.R.den : ℤ)).toNat := by
  have hden_pos : 0 < (I.R.den : ℤ) := by
    have h := Rat.den_pos I.R
    exact Int.natCast_pos.mpr h
  calc
    I.Rb = ⌈I.R⌉₊ := rfl
    _ = ⌈(I.R.num : ℚ) / (I.R.den : ℚ)⌉₊ := by rw [Rat.num_div_den I.R]
    _ = ⌈(I.R.num : ℚ) / (I.R.den : ℤ)⌉₊ := by simp
    _ = ((I.R.num + (I.R.den : ℤ) - 1) / (I.R.den : ℤ)).toNat := by
      rw [natCeil_div_eq I.R.num I.R.den hden_pos]

theorem ellTest_ret {d : ℕ} (I : EllI d) (s : ℕ) (a x : Fin d → ℤ)
    (kept : Option ((Fin d → ℤ) × ℤ)) (h : ellTest I s a kept = .ret x) : x = a := by
  unfold ellTest at h
  split at h
  · injection h
  · split at h
    · injection h
    · split at h
      · injection h
      · dsimp at h
        split at h
        · injection h with ha_eq_x
          exact ha_eq_x.symm
        · injection h

theorem mulVec_smul_int {d : ℕ} (P : Matrix (Fin d) (Fin d) ℤ) (D : ℤ) (a : Fin d → ℤ)
    (i : Fin d) : (P *ᵥ (D • a)) i = D * (P *ᵥ a) i := by
  calc
    (P *ᵥ (D • a)) i = (D • (P *ᵥ a)) i := by rw [Matrix.mulVec_smul]
    _ = D * (P *ᵥ a) i := by rw [Pi.smul_apply, smul_eq_mul]

theorem ellTest_cut {d : ℕ} (I : EllI d) (s : ℕ) (a c : Fin d → ℤ)
    (kept kept' : Option ((Fin d → ℤ) × ℤ)) (h : ellTest I s a kept = .cut c kept') :
    (c = a ∨ (∃ i, c = I.α i) ∨ c = I.H *ᵥ a - (2 ^ s : ℤ) • I.g ∨
        c = I.P *ᵥ ((I.Df : ℤ) • a) - (2 ^ s : ℤ) • I.f) ∧
      (kept' = kept ∨ kept' = some (a, (I.Df : ℤ) * (a ⬝ᵥ (I.P *ᵥ a)) - 2 ^ (s + 1) * (I.f ⬝ᵥ a))) := by
  unfold ellTest at h
  split at h
  · -- h : .cut a kept = .cut c kept'
    have h_inj := Cut.cut.inj h
    rcases h_inj with ⟨hc, hk⟩
    exact ⟨Or.inl hc.symm, Or.inl hk.symm⟩
  · -- h : (match (List.finRange I.m).find? (fun i => decide (2 ^ s * I.β i < I.α i ⬝ᵥ a)) with ...) = .cut c kept'
    split at h
    · -- h : .cut (I.α i) kept = .cut c kept' for some i
      have h_inj := Cut.cut.inj h
      rcases h_inj with ⟨hc, hk⟩
      exact ⟨Or.inr (Or.inl ⟨_, hc.symm⟩), Or.inl hk.symm⟩
    · -- h : (if 2 ^ (2 * s + 1) * I.ℓ < a ⬝ᵥ (I.H *ᵥ a) - 2 ^ (s + 1) * (I.g ⬝ᵥ a) then ... else ...) = .cut c kept'
      split at h
      · -- h : .cut (I.H *ᵥ a - (2 ^ s : ℤ) • I.g) kept = .cut c kept'
        have h_inj := Cut.cut.inj h
        rcases h_inj with ⟨hc, hk⟩
        exact ⟨Or.inr (Or.inr (Or.inl hc.symm)), Or.inl hk.symm⟩
      · -- h : (let gh := ...; let V := ...; let kept' := ...; if gh = 0 then .ret a else .cut gh kept') = .cut c kept'
        dsimp at h
        -- h : (if (I.P *ᵥ ((I.Df : ℤ) • a) - (2 ^ s : ℤ) • I.f) = 0 then .ret a
        --            else .cut (I.P *ᵥ ((I.Df : ℤ) • a) - (2 ^ s : ℤ) • I.f)
        --              (match kept with
        --              | none => some (a, V_expr)
        --              | some (b, W) => if V_expr < W then some (a, V_expr) else some (b, W))) = .cut c kept'
        split at h
        · -- h : .ret a = .cut c kept' → contradiction
          cases h
        · -- h : .cut gh (match kept with ...) = .cut c kept'
          have h_inj := Cut.cut.inj h
          rcases h_inj with ⟨hc, hk⟩
          -- hc : I.P *ᵥ ((I.Df : ℤ) • a) - (2 ^ s : ℤ) • I.f = c
          -- hk : (match kept with ...) = kept'
          have hc' : c = I.P *ᵥ ((I.Df : ℤ) • a) - (2 ^ s : ℤ) • I.f := Eq.symm hc
          constructor
          · -- prove c = a ∨ (∃ i, c = I.α i) ∨ c = I.H *ᵥ a - ... ∨ c = I.P *ᵥ ...
            right; right; right; exact hc'
          · -- prove kept' = kept ∨ kept' = some (a, V_expr)
            rw [hk.symm]
            -- Goal: (match kept with ...) = kept ∨ (match kept with ...) = some (a, V_expr)
            cases kept with
            | none =>
              simp
            | some b =>
              dsimp
              split_ifs with hlt
              · right; rfl
              · left; rfl

theorem ellJ_eq {d : ℕ} (I : EllI d) (hr : 0 < I.r) (he : 0 < I.e) :
    let trP : ℤ := I.P.trace
    let F1 : ℤ := ∑ i, |I.f i|
    let rn : ℤ := I.r.num
    let rd : ℤ := I.r.den
    let en : ℤ := I.e.num
    let ed : ℤ := I.e.den
    let LGn : ℤ := if I.Df = 0 then trP * I.Rb else trP * I.Rb * I.Df + F1
    let LGd : ℤ := if I.Df = 0 then 1 else I.Df
    let Nx : ℤ := (if 3 * LGn * I.Rb * ed ≤ en * LGd then 1 else 3 * LGn * I.Rb * ed) * (if rn ≤ rd then rd else 1)
    let Dx : ℤ := (if 3 * LGn * I.Rb * ed ≤ en * LGd then 1 else LGd * en) * (if rn ≤ rd then rn else 1)
    0 < Nx ∧ 0 < Dx ∧ I.j = Nat.clog 2 ((Nx + Dx - 1) / Dx).toNat := by
  intro trP F1 rn rd en ed LGn LGd Nx Dx
  have hF1 : 0 ≤ F1 := by
    dsimp [F1]
    refine Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hrn : 0 < I.r.num := Rat.num_pos.mpr hr
  have hen : 0 < I.e.num := Rat.num_pos.mpr he
  have hrd : 0 < I.r.den := Rat.den_pos _
  have hed : 0 < I.e.den := Rat.den_pos _
  have h_ellJ := ellJ_frac I.P.trace (∑ i, |I.f i|) I.r.num I.e.num I.Rb I.Df I.r.den I.e.den hF1 hrn hen hrd hed
  dsimp at h_ellJ
  rcases h_ellJ with ⟨hNx_raw, hDx_raw, h_eq_raw⟩
  have hsum : ((∑ i, |I.f i|) : ℚ) = ∑ i, |(I.f i : ℚ)| := by
    simpa using (map_sum (Int.castRingHom ℚ) (fun i => |I.f i|) Finset.univ).symm
  have hIe_eq : I.e = (I.e.num : ℚ) / (I.e.den : ℚ) := (Rat.num_div_den _).symm
  have hIr_eq : I.r = (I.r.num : ℚ) / (I.r.den : ℚ) := (Rat.num_div_den _).symm
  have hNx : 0 < Nx := by
    simpa [Nx, LGn, LGd, trP, F1, rn, rd, en, ed] using hNx_raw
  have hDx : 0 < Dx := by
    simpa [Dx, LGn, LGd, trP, F1, rn, rd, en, ed] using hDx_raw
  have h_main : 1 / (I.θ * min I.r 1) = (Nx : ℚ) / (Dx : ℚ) := by
    rw [EllI.θ, EllI.LG, hIe_eq, hIr_eq, ← hsum]
    simpa [Nx, Dx, LGn, LGd, trP, F1, rn, rd, en, ed] using h_eq_raw
  have h_ceil_eq : ⌈(Nx : ℚ) / (Dx : ℚ)⌉₊ = ((Nx + Dx - 1) / Dx).toNat :=
    natCeil_div_eq Nx Dx hDx
  have h_j_eq : I.j = Nat.clog 2 ((Nx + Dx - 1) / Dx).toNat := by
    dsimp [EllI.j, lgQ]
    rw [h_main, h_ceil_eq]
  exact ⟨hNx, hDx, h_j_eq⟩

theorem ellUpd_caps {d : ℕ} {p q j : ℕ} {capA capa : ℤ}
    {A A' : Matrix (Fin d) (Fin d) ℤ} {a a' c : Fin d → ℤ} (h : ellUpd p q j capA capa A a c = some (A', a')) :
    (∀ i k, |A' i k| ≤ capA) ∧ ∀ i, |a' i| ≤ capa := by
  simp [ellUpd] at h
  rcases h with ⟨h1, ⟨hA_bound, ha_bound⟩, h_eq⟩
  have h_eq' := Prod.mk.inj h_eq
  rcases h_eq' with ⟨hA', ha'⟩
  have hA_caps : ∀ i1 i2, |A' i1 i2| ≤ capA := by
    intro i1 i2
    rw [← hA']
    beta_reduce
    exact hA_bound i1 i2
  have ha_caps : ∀ i3, |a' i3| ≤ capa := by
    intro i3
    rw [← ha']
    beta_reduce
    exact ha_bound i3
  exact And.intro hA_caps ha_caps

open Finset in
theorem ellCut_le {d : ℕ} (I : EllI d) (s E0 : ℕ) (a c : Fin d → ℤ)
    (kept kept' : Option ((Fin d → ℤ) × ℤ)) (ha : ∀ i, |a i| ≤ 2 ^ E0) (h : ellTest I s a kept = .cut c kept')
    (i : Fin d) : |c i| ≤ 2 ^ (E0 + 2 * ellSz I + d + s + 2) := by
  have h_two_pos : 0 < (2 : ℕ) := by norm_num
  rcases ellTest_cut I s a c kept kept' h with ⟨h_cases, h_kept⟩
  rcases h_cases with (hc | hc | hc | hc)
  · -- c = a
    rw [hc]
    refine (ha i).trans ?_
    refine Nat.cast_le.mpr (Nat.pow_le_pow_right h_two_pos ?_)
    omega
  · -- c = I.α i₀ for some i₀
    rcases hc with ⟨i₀, hc⟩
    rw [hc]
    rcases ellMx_le I with ⟨h_α, h_β, h_H, h_P, h_g, h_f, h_ℓ, h_Df, h_Rnum, h_Rden, h_rnum, h_rden, h_en, h_eden⟩
    have h_bound_nat : (I.α i₀ i).natAbs < 2 ^ ellSz I :=
      lt_of_le_of_lt (h_α i₀ i) (Nat.lt_size_self _)
    have h_abs_lt : |I.α i₀ i| < (2 : ℤ) ^ ellSz I := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast h_bound_nat
    refine h_abs_lt.le.trans ?_
    refine Nat.cast_le.mpr (Nat.pow_le_pow_right h_two_pos ?_)
    omega
  · -- c = I.H *ᵥ a - (2 ^ s : ℤ) • I.g
    rw [hc]
    rcases ellMx_le I with ⟨h_α, h_β, h_H, h_P, h_g, h_f, h_ℓ, h_Df, h_Rnum, h_Rden, h_rnum, h_rden, h_en, h_eden⟩
    have h_ellMx_lt : (ellMx I : ℤ) < (2 : ℤ) ^ ellSz I := by
      have h_nat : ellMx I < 2 ^ ellSz I := Nat.lt_size_self _
      exact_mod_cast h_nat
    have h_H_bound (i j : Fin d) : |I.H i j| ≤ (2 : ℤ) ^ ellSz I := by
      rw [Int.abs_eq_natAbs]
      exact (Nat.cast_le.mpr (h_H i j)).trans h_ellMx_lt.le
    have h_g_bound (j : Fin d) : |I.g j| ≤ (2 : ℤ) ^ ellSz I := by
      rw [Int.abs_eq_natAbs]
      exact (Nat.cast_le.mpr (h_g j)).trans h_ellMx_lt.le
    have ha_bound (i : Fin d) : |a i| ≤ (2 : ℤ) ^ E0 := ha i
    have h_pow_nonneg (n : ℕ) : 0 ≤ (2 : ℤ) ^ n := pow_nonneg (by norm_num) _
    have h_sum_H : |(I.H *ᵥ a) i| ≤ (d : ℤ) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ E0) := by
      calc
        |(I.H *ᵥ a) i| = |∑ j, I.H i j * a j| := rfl
        _ ≤ ∑ j, |I.H i j * a j| := Finset.abs_sum_le_sum_abs (fun j => I.H i j * a j) univ
        _ = ∑ j, |I.H i j| * |a j| := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [abs_mul]
        _ ≤ ∑ j, ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ E0) := by
          refine Finset.sum_le_sum fun j hj => ?_
          exact mul_le_mul (h_H_bound i j) (ha_bound j) (abs_nonneg _) (h_pow_nonneg _)
        _ = (d : ℤ) * (((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ E0)) := by
          simp [Finset.sum_const]
        _ = (d : ℤ) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ E0) := by ring
    have h_bound_g : |((2 ^ s : ℤ) • I.g) i| ≤ (2 : ℤ) ^ s * ((2 : ℤ) ^ ellSz I) := by
      calc
        |((2 ^ s : ℤ) • I.g) i| = |(2 ^ s : ℤ) * I.g i| := rfl
        _ = |(2 : ℤ) ^ s| * |I.g i| := abs_mul _ _
        _ = (2 : ℤ) ^ s * |I.g i| := by rw [abs_of_nonneg (h_pow_nonneg s)]
        _ ≤ (2 : ℤ) ^ s * ((2 : ℤ) ^ ellSz I) :=
          mul_le_mul_of_nonneg_left (h_g_bound i) (h_pow_nonneg s)
    have h_total : |(I.H *ᵥ a - (2 ^ s : ℤ) • I.g) i| ≤
        (d : ℤ) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ E0) + (2 : ℤ) ^ s * ((2 : ℤ) ^ ellSz I) := by
      calc
        |(I.H *ᵥ a - (2 ^ s : ℤ) • I.g) i| = |(I.H *ᵥ a) i - ((2 ^ s : ℤ) • I.g) i| := rfl
        _ ≤ |(I.H *ᵥ a) i| + |((2 ^ s : ℤ) • I.g) i| := abs_sub _ _
        _ ≤ ((d : ℤ) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ E0)) +
            ((2 : ℤ) ^ s * ((2 : ℤ) ^ ellSz I)) := add_le_add h_sum_H h_bound_g
    have h_d_lt : (d : ℤ) < (2 : ℤ) ^ d := by
      have h_nat : d < 2 ^ d := Nat.lt_two_pow_self (n := d)
      exact_mod_cast h_nat
    have h_term1 : (d : ℤ) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ E0) ≤
        (2 : ℤ) ^ (ellSz I + E0 + d) := by
      calc
        (d : ℤ) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ E0) ≤
            ((2 : ℤ) ^ d) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ E0) := by
          have h_nonneg : 0 ≤ ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ E0) :=
            mul_nonneg (h_pow_nonneg _) (h_pow_nonneg _)
          have h_mul : (d : ℤ) * (((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ E0)) ≤
              ((2 : ℤ) ^ d) * (((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ E0)) :=
            mul_le_mul_of_nonneg_right h_d_lt.le h_nonneg
          simpa [mul_assoc] using h_mul
        _ = ((2 : ℤ) ^ d * (2 : ℤ) ^ ellSz I) * (2 : ℤ) ^ E0 := by ring
        _ = (2 : ℤ) ^ (d + ellSz I) * (2 : ℤ) ^ E0 := by rw [← pow_add]
        _ = (2 : ℤ) ^ ((d + ellSz I) + E0) := by rw [← pow_add]
        _ = (2 : ℤ) ^ (ellSz I + E0 + d) := by ring
    have h_term2 : (2 : ℤ) ^ s * ((2 : ℤ) ^ ellSz I) ≤ (2 : ℤ) ^ (ellSz I + s) := by
      rw [← pow_add, add_comm]
    have h_sum_le : (d : ℤ) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ E0) + (2 : ℤ) ^ s * ((2 : ℤ) ^ ellSz I) ≤
        (2 : ℤ) ^ (ellSz I + E0 + d) + (2 : ℤ) ^ (ellSz I + s) :=
      add_le_add h_term1 h_term2
    have h_both_le : (2 : ℤ) ^ (ellSz I + E0 + d) + (2 : ℤ) ^ (ellSz I + s) ≤
        2 * (2 : ℤ) ^ (E0 + ellSz I + d + s) := by
      have h1 : (2 : ℤ) ^ (ellSz I + E0 + d) ≤ (2 : ℤ) ^ (E0 + ellSz I + d + s) :=
        Nat.cast_le.mpr (Nat.pow_le_pow_right h_two_pos (by omega))
      have h2 : (2 : ℤ) ^ (ellSz I + s) ≤ (2 : ℤ) ^ (E0 + ellSz I + d + s) :=
        Nat.cast_le.mpr (Nat.pow_le_pow_right h_two_pos (by omega))
      calc
        (2 : ℤ) ^ (ellSz I + E0 + d) + (2 : ℤ) ^ (ellSz I + s) ≤
            (2 : ℤ) ^ (E0 + ellSz I + d + s) + (2 : ℤ) ^ (E0 + ellSz I + d + s) := add_le_add h1 h2
        _ = 2 * (2 : ℤ) ^ (E0 + ellSz I + d + s) := by ring
    have h_pow_succ : 2 * (2 : ℤ) ^ (E0 + ellSz I + d + s) = (2 : ℤ) ^ (E0 + ellSz I + d + s + 1) := by
      rw [pow_succ, mul_comm]
    have h_final : (2 : ℤ) ^ (E0 + ellSz I + d + s + 1) ≤
        (2 : ℤ) ^ (E0 + 2 * ellSz I + d + s + 2) :=
      Nat.cast_le.mpr (Nat.pow_le_pow_right h_two_pos (by omega))
    refine h_total.trans ?_
    refine h_sum_le.trans ?_
    refine h_both_le.trans ?_
    rw [h_pow_succ]
    exact h_final
  · -- c = I.P *ᵥ ((I.Df : ℤ) • a) - (2 ^ s : ℤ) • I.f
    rw [hc]
    rcases ellMx_le I with ⟨h_α, h_β, h_H, h_P, h_g, h_f, h_ℓ, h_Df, h_Rnum, h_Rden, h_rnum, h_rden, h_en, h_eden⟩
    have h_ellMx_lt : (ellMx I : ℤ) < (2 : ℤ) ^ ellSz I := by
      have h_nat : ellMx I < 2 ^ ellSz I := Nat.lt_size_self _
      exact_mod_cast h_nat
    have h_P_bound (i j : Fin d) : |I.P i j| ≤ (2 : ℤ) ^ ellSz I := by
      rw [Int.abs_eq_natAbs]
      exact (Nat.cast_le.mpr (h_P i j)).trans h_ellMx_lt.le
    have h_f_bound (j : Fin d) : |I.f j| ≤ (2 : ℤ) ^ ellSz I := by
      rw [Int.abs_eq_natAbs]
      exact (Nat.cast_le.mpr (h_f j)).trans h_ellMx_lt.le
    have ha_bound (i : Fin d) : |a i| ≤ (2 : ℤ) ^ E0 := ha i
    have h_Df_bound : |(I.Df : ℤ)| ≤ (2 : ℤ) ^ ellSz I := by
      have h_nonneg : 0 ≤ (I.Df : ℤ) := by exact mod_cast (Nat.zero_le I.Df)
      rw [abs_of_nonneg h_nonneg]
      exact (Nat.cast_le.mpr h_Df).trans_lt h_ellMx_lt |>.le
    have h_pow_nonneg (n : ℕ) : 0 ≤ (2 : ℤ) ^ n := pow_nonneg (by norm_num) _
    have h_sum_P : |(I.P *ᵥ ((I.Df : ℤ) • a)) i| ≤ (d : ℤ) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ E0) := by
      calc
        |(I.P *ᵥ ((I.Df : ℤ) • a)) i| = |∑ j, I.P i j * ((I.Df : ℤ) • a) j| := rfl
        _ = |∑ j, I.P i j * ((I.Df : ℤ) * a j)| := rfl
        _ = |∑ j, (I.P i j * (I.Df : ℤ)) * a j| := by
          refine congrArg (fun x => |x|) (Finset.sum_congr rfl fun j hj => ?_)
          ring
        _ ≤ ∑ j, |(I.P i j * (I.Df : ℤ)) * a j| :=
          Finset.abs_sum_le_sum_abs (fun j => (I.P i j * (I.Df : ℤ)) * a j) univ
        _ = ∑ j, |I.P i j * (I.Df : ℤ)| * |a j| := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [abs_mul]
        _ = ∑ j, (|I.P i j| * |(I.Df : ℤ)|) * |a j| := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [abs_mul]
        _ ≤ ∑ j, (((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ ellSz I)) * ((2 : ℤ) ^ E0) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have h_inner : |I.P i j| * |(I.Df : ℤ)| ≤ ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ ellSz I) :=
            mul_le_mul (h_P_bound i j) h_Df_bound (abs_nonneg _) (h_pow_nonneg _)
          have h_nonneg_inner : 0 ≤ |I.P i j| * |(I.Df : ℤ)| :=
            mul_nonneg (abs_nonneg _) (abs_nonneg _)
          have h_nonneg_outer : 0 ≤ ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ ellSz I) :=
            mul_nonneg (h_pow_nonneg _) (h_pow_nonneg _)
          exact mul_le_mul h_inner (ha_bound j) (abs_nonneg _) h_nonneg_outer
        _ = (d : ℤ) * ((((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ ellSz I)) * ((2 : ℤ) ^ E0)) := by
          simp [Finset.sum_const]
        _ = (d : ℤ) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ E0) := by ring
    have h_bound_f : |((2 ^ s : ℤ) • I.f) i| ≤ (2 : ℤ) ^ s * ((2 : ℤ) ^ ellSz I) := by
      calc
        |((2 ^ s : ℤ) • I.f) i| = |(2 ^ s : ℤ) * I.f i| := rfl
        _ = |(2 : ℤ) ^ s| * |I.f i| := abs_mul _ _
        _ = (2 : ℤ) ^ s * |I.f i| := by rw [abs_of_nonneg (h_pow_nonneg s)]
        _ ≤ (2 : ℤ) ^ s * ((2 : ℤ) ^ ellSz I) :=
          mul_le_mul_of_nonneg_left (h_f_bound i) (h_pow_nonneg s)
    have h_total : |(I.P *ᵥ ((I.Df : ℤ) • a) - (2 ^ s : ℤ) • I.f) i| ≤
        (d : ℤ) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ E0) +
        (2 : ℤ) ^ s * ((2 : ℤ) ^ ellSz I) := by
      calc
        |(I.P *ᵥ ((I.Df : ℤ) • a) - (2 ^ s : ℤ) • I.f) i| =
            |(I.P *ᵥ ((I.Df : ℤ) • a)) i - ((2 ^ s : ℤ) • I.f) i| := rfl
        _ ≤ |(I.P *ᵥ ((I.Df : ℤ) • a)) i| + |((2 ^ s : ℤ) • I.f) i| := abs_sub _ _
        _ ≤ ((d : ℤ) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ E0)) +
            ((2 : ℤ) ^ s * ((2 : ℤ) ^ ellSz I)) := add_le_add h_sum_P h_bound_f
    have h_d_lt : (d : ℤ) < (2 : ℤ) ^ d := by
      have h_nat : d < 2 ^ d := Nat.lt_two_pow_self (n := d)
      exact_mod_cast h_nat
    have h_term1 : (d : ℤ) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ E0) ≤
        (2 : ℤ) ^ (2 * ellSz I + E0 + d) := by
      calc
        (d : ℤ) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ E0) =
            (d : ℤ) * (((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ ellSz I)) * ((2 : ℤ) ^ E0) := by ring
        _ ≤ ((2 : ℤ) ^ d) * (((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ ellSz I)) * ((2 : ℤ) ^ E0) := by
          have h_nonneg : 0 ≤ ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ E0) :=
            mul_nonneg (mul_nonneg (h_pow_nonneg _) (h_pow_nonneg _)) (h_pow_nonneg _)
          have h_mul : (d : ℤ) * (((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ E0)) ≤
              ((2 : ℤ) ^ d) * (((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ E0)) :=
            mul_le_mul_of_nonneg_right h_d_lt.le h_nonneg
          simpa [mul_assoc] using h_mul
        _ = ((2 : ℤ) ^ d * ((2 : ℤ) ^ ellSz I * (2 : ℤ) ^ ellSz I)) * (2 : ℤ) ^ E0 := by ring
        _ = ((2 : ℤ) ^ d * (2 : ℤ) ^ (ellSz I + ellSz I)) * (2 : ℤ) ^ E0 := by rw [← pow_add]
        _ = ((2 : ℤ) ^ (d + (ellSz I + ellSz I))) * (2 : ℤ) ^ E0 := by rw [← pow_add]
        _ = (2 : ℤ) ^ ((d + (ellSz I + ellSz I)) + E0) := by rw [← pow_add]
        _ = (2 : ℤ) ^ (2 * ellSz I + E0 + d) := by ring
    have h_term2 : (2 : ℤ) ^ s * ((2 : ℤ) ^ ellSz I) ≤ (2 : ℤ) ^ (ellSz I + s) := by
      rw [← pow_add, add_comm]
    have h_sum_le : (d : ℤ) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ ellSz I) * ((2 : ℤ) ^ E0) +
        (2 : ℤ) ^ s * ((2 : ℤ) ^ ellSz I) ≤
        (2 : ℤ) ^ (2 * ellSz I + E0 + d) + (2 : ℤ) ^ (ellSz I + s) :=
      add_le_add h_term1 h_term2
    have h_both_le : (2 : ℤ) ^ (2 * ellSz I + E0 + d) + (2 : ℤ) ^ (ellSz I + s) ≤
        2 * (2 : ℤ) ^ (E0 + 2 * ellSz I + d + s) := by
      have h1 : (2 : ℤ) ^ (2 * ellSz I + E0 + d) ≤ (2 : ℤ) ^ (E0 + 2 * ellSz I + d + s) :=
        Nat.cast_le.mpr (Nat.pow_le_pow_right h_two_pos (by omega))
      have h2 : (2 : ℤ) ^ (ellSz I + s) ≤ (2 : ℤ) ^ (E0 + 2 * ellSz I + d + s) :=
        Nat.cast_le.mpr (Nat.pow_le_pow_right h_two_pos (by omega))
      calc
        (2 : ℤ) ^ (2 * ellSz I + E0 + d) + (2 : ℤ) ^ (ellSz I + s) ≤
            (2 : ℤ) ^ (E0 + 2 * ellSz I + d + s) + (2 : ℤ) ^ (E0 + 2 * ellSz I + d + s) :=
          add_le_add h1 h2
        _ = 2 * (2 : ℤ) ^ (E0 + 2 * ellSz I + d + s) := by ring
    have h_pow_succ : 2 * (2 : ℤ) ^ (E0 + 2 * ellSz I + d + s) = (2 : ℤ) ^ (E0 + 2 * ellSz I + d + s + 1) := by
      rw [pow_succ, mul_comm]
    have h_final : (2 : ℤ) ^ (E0 + 2 * ellSz I + d + s + 1) ≤
        (2 : ℤ) ^ (E0 + 2 * ellSz I + d + s + 2) :=
      Nat.cast_le.mpr (Nat.pow_le_pow_right h_two_pos (by omega))
    refine h_total.trans ?_
    refine h_sum_le.trans ?_
    refine h_both_le.trans ?_
    rw [h_pow_succ]
    exact h_final

/-- The early exits of ELL-R in integers: `R < 1`, `r ≤ 0`, `e ≤ 0` by numerator and denominator. -/
theorem ellRI_cond {d : ℕ} (I : EllI d) :
    (I.R < 1 ↔ I.R.num < I.R.den) ∧ (I.r ≤ 0 ↔ I.r.num ≤ 0) ∧ (I.e ≤ 0 ↔ I.e.num ≤ 0) := by
  have hR : I.R < 1 ↔ I.R.num < I.R.den := by
    have hpos : 0 < (I.R.den : ℚ) := by exact_mod_cast Rat.pos I.R
    constructor
    · intro h
      rw [← Rat.num_div_den I.R] at h
      have hdiv := (div_lt_one (a := (I.R.num : ℚ)) hpos).mp h
      simpa using (Int.cast_lt (R := ℚ) (m := I.R.num) (n := (I.R.den : ℤ))).mp hdiv
    · intro h
      have hdiv : (I.R.num : ℚ) < (I.R.den : ℚ) :=
        (Int.cast_lt (R := ℚ) (m := I.R.num) (n := (I.R.den : ℤ))).mpr h
      have hq' : (I.R.num : ℚ) / (I.R.den : ℚ) < 1 :=
        (div_lt_one (a := (I.R.num : ℚ)) hpos).mpr hdiv
      rw [← Rat.num_div_den I.R]
      exact hq'
  have hr : I.r ≤ 0 ↔ I.r.num ≤ 0 := Rat.num_nonpos.symm
  have he : I.e ≤ 0 ↔ I.e.num ≤ 0 := Rat.num_nonpos.symm
  exact And.intro hR (And.intro hr he)

end AdversarialBco.Bit.Transfer
