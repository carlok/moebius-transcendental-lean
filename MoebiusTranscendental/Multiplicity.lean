/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
import Mathlib

/-!
# Multiplicity of a point on a plane curve

The multiplicity of `p` on the curve `P = 0` is the degree of the lowest non-zero
homogeneous component of `P` translated so that `p` becomes the origin.

Mathlib has no notion of multiplicity of a point on a variety, but it has every
ingredient: `MvPolynomial.homogeneousComponent`, `sum_homogeneousComponent`, and
`aeval`. This file assembles them.

`shiftTo` is named to avoid `Function.translate`, which Mathlib already uses.

## Main declarations

* `MoebiusTranscendental.shiftTo` — translation of a polynomial
* `MoebiusTranscendental.mult` — multiplicity of a point on a plane curve
-/

open MvPolynomial

namespace MoebiusTranscendental

noncomputable section
variable {K : Type*} [Field K]

/-- Translate a polynomial so that `p` becomes the origin. -/
def shiftTo (p : Fin 2 → K) (P : MvPolynomial (Fin 2) K) : MvPolynomial (Fin 2) K :=
  aeval (fun i => X i + C (p i)) P

/-- The multiplicity of the point `p` on the curve `P = 0`: the degree of the
lowest non-zero homogeneous component of `P` translated to the origin. -/
def mult (P : MvPolynomial (Fin 2) K) (p : Fin 2 → K) : ℕ :=
  sInf {n | homogeneousComponent n (shiftTo p P) ≠ 0}

/-- A non-zero polynomial has a non-zero homogeneous component, so the set
defining `mult` is non-empty. -/
theorem nonempty_of_ne_zero {Q : MvPolynomial (Fin 2) K} (h : Q ≠ 0) :
    {n | homogeneousComponent n Q ≠ 0}.Nonempty := by
  by_contra hc
  rw [Set.not_nonempty_iff_eq_empty] at hc
  apply h
  have hall : ∀ n, homogeneousComponent n Q = 0 := by
    intro n
    by_contra hn
    have : n ∈ {n | homogeneousComponent n Q ≠ 0} := hn
    rw [hc] at this; exact this
  calc Q = ∑ i ∈ Finset.range (Q.totalDegree + 1), homogeneousComponent i Q :=
        (sum_homogeneousComponent Q).symm
    _ = 0 := by simp [hall]

/-- Translation is invertible, so it preserves non-vanishing. -/
theorem shiftTo_ne_zero {P : MvPolynomial (Fin 2) K} {p : Fin 2 → K} (h : P ≠ 0) :
    shiftTo p P ≠ 0 := by
  intro hzero
  apply h
  have : shiftTo (fun i => -p i) (shiftTo p P) = P := by
    simp only [shiftTo, ← AlgHom.comp_apply]
    rw [show (aeval fun i => X i + C (-p i)).comp (aeval fun i => X i + C (p i))
        = AlgHom.id K (MvPolynomial (Fin 2) K) by ext i; simp]
    simp
  rw [hzero] at this
  rw [← this]
  simp [shiftTo]

end

end MoebiusTranscendental
