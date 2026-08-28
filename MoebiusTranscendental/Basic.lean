/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
import Mathlib

/-!
# The transcendental locus and the conjugation degree

The setting of `p19.tex`: the algebraic numbers `Q̄` as a subfield of `ℂ`, the
transcendental locus `𝒯 = ℂ ∖ Q̄`, and the conjugation degree

  `δ(z) = [Q̄(z, conj z) : Q̄(z)]`

which organises the paper. `δ(z) = 1` is exactly the condition that conjugation
is already determined by the field structure on `Q̄(z)`; that stratum is the one
formalised in `carlok/diaz-modulus-lean`.

`δ` is defined through the degree of the minimal polynomial rather than
`Module.finrank`, for two reasons: it avoids the `IntermediateField` tower
instances, and `⊤` is a genuine value rather than `finrank`'s junk `0`.

## Main declarations

* `MoebiusTranscendental.Qbar` — the algebraic numbers as a subfield of `ℂ`
* `MoebiusTranscendental.Transcendentals` — the locus `𝒯`
* `MoebiusTranscendental.conjDegree` — the invariant `δ`
* `MoebiusTranscendental.stratum` — the level sets of `δ`
-/

open ComplexConjugate IntermediateField
open scoped Classical

namespace MoebiusTranscendental

noncomputable section

/-- The algebraic numbers, as a subfield of `ℂ`. -/
def Qbar : Subfield ℂ := (algebraicClosure ℚ ℂ).toSubfield

theorem mem_Qbar_iff {a : ℂ} : a ∈ Qbar ↔ IsAlgebraic ℚ a := by
  simp only [Qbar, IntermediateField.mem_toSubfield]
  exact mem_algebraicClosure_iff

/-- The transcendental locus `𝒯 = ℂ ∖ Q̄`. -/
def Transcendentals : Set ℂ := {z | ¬ IsAlgebraic ℚ z}

/-- The field `Q̄(z)` generated over the algebraic numbers by `z`. -/
abbrev gen (z : ℂ) : IntermediateField ↥Qbar ℂ := IntermediateField.adjoin ↥Qbar {z}

/-- The conjugation degree `δ(z) = [Q̄(z, conj z) : Q̄(z)]`, as the degree of the
minimal polynomial of `conj z` over `Q̄(z)`, and `⊤` when there is none. -/
def conjDegree (z : ℂ) : ℕ∞ :=
  if IsIntegral (gen z) (conj z) then ((minpoly (gen z) (conj z)).natDegree : ℕ∞) else ⊤

/-- The stratum of transcendental points of conjugation degree `n`. -/
def stratum (n : ℕ∞) : Set ℂ := {z ∈ Transcendentals | conjDegree z = n}

end

end MoebiusTranscendental
