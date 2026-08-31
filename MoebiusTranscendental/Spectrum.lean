/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
import MoebiusTranscendental.Basic

/-!
# The conjugation-degree spectrum

Every stratum of `conjDegree` is inhabited except the zeroth, which is empty:

  `∀ n : ℕ∞, n ≠ 0 → ∃ z ∈ Transcendentals, conjDegree z = n`

This is the first result attached to `stratum`, and it is a complete
classification — `δ` takes every value in `ℕ∞ ∖ {0}` on `𝒯` and no other.

The two halves are proved differently. The finite values `n ≥ 1` have the
uniform explicit witness

  `zₙ = sⁿ + i·s`,   `s = liouvilleNumber 2`,

whose degree is computed by transporting `RatFunc.finrank_eq_max_natDegree`
along `Q̄(zₙ, conj zₙ) = Q̄(s)`: conjugation recovers `s` from `zₙ`, so the pair
generates `Q̄(s)`, and `zₙ` sits inside it as a rational function of degree `n`.
The `⊤` stratum is not explicit — it takes an algebraically independent pair of
reals over `Q̄`, chosen by cardinality, so `conj z` is integral over `Q̄(z)` for
no reason at all.

`ENat.recTopCoe` glues the two.

## Main declarations

* `MoebiusTranscendental.conjDegree_ne_zero` — `0` is not a value of `δ`
* `MoebiusTranscendental.finite_spectrum` — every `n ≥ 1` is attained
* `MoebiusTranscendental.top_witness_exists` — `⊤` is attained
* `MoebiusTranscendental.spectrum_statement_compiles` — the classification
* `MoebiusTranscendental.stratum_nonempty` — restated on `stratum`

## Provenance

Produced 2026-08-28 by `gpt-5.6-sol` under direction, as corner 4 of the probe
recorded in `carlok/palomar-tries`; adapted here to the definitions in
`Basic.lean` and rechecked 2026-08-31. The finite half is an elementary
transport and is not claimed as new; the statement as a whole is what the
`stratum` definition was waiting for.
-/

open ComplexConjugate IntermediateField
open scoped Classical

namespace MoebiusTranscendental

noncomputable section

local instance : Algebra.IsAlgebraic ℤ ℚ :=
  ⟨fun x ↦ (IsFractionRing.isAlgebraic_iff ℤ ℚ ℚ).2 (isAlgebraic_algebraMap x)⟩

local instance qbarAlgebra : Algebra ℚ Qbar :=
  IntermediateField.algebra' (algebraicClosure ℚ ℂ)

local instance : Algebra.IsAlgebraic ℚ Qbar :=
  ⟨fun x ↦ (IntermediateField.isAlgebraic_iff
    (S := algebraicClosure ℚ ℂ)).mpr (mem_Qbar_iff.mp x.property)⟩


def finiteWitness (n : ℕ) : ℂ :=
  ((liouvilleNumber 2 : ℝ) : ℂ) ^ n + Complex.I * (liouvilleNumber 2 : ℝ)

def qbarI : Qbar :=
  ⟨Complex.I, mem_Qbar_iff.mpr Complex.isIntegral_rat_I.isAlgebraic⟩

def witnessPoly (n : ℕ) : Polynomial Qbar :=
  Polynomial.X ^ n + Polynomial.C qbarI * Polynomial.X

theorem liouville_two_transcendental_Qbar :
    Transcendental Qbar (((liouvilleNumber 2 : ℝ) : ℂ)) := by
  have hZ : Transcendental ℤ (liouvilleNumber (2 : ℕ)) :=
    transcendental_liouvilleNumber (by norm_num)
  have hQ : Transcendental ℚ (liouvilleNumber (2 : ℕ)) :=
    hZ.extendScalars ℚ
  have hQC : Transcendental ℚ (((liouvilleNumber 2 : ℝ) : ℂ)) := by
    change Transcendental ℚ (algebraMap ℝ ℂ (liouvilleNumber 2))
    exact (transcendental_algebraMap_iff (algebraMap ℝ ℂ).injective).2 hQ
  exact hQC.extendScalars Qbar

theorem finiteWitness_one_conj :
    conj (finiteWitness 1) = -Complex.I * finiteWitness 1 := by
  simp [finiteWitness, Complex.conj_ofReal, Complex.conj_I, mul_add, ← mul_assoc,
    Complex.I_mul_I, add_comm]

theorem finiteWitness_one_degree : conjDegree (finiteWitness 1) = 1 := by
  let z := finiteWitness 1
  have hi : ((-qbarI : Qbar) : ℂ) ∈ (gen z : Set ℂ) :=
    IntermediateField.algebraMap_mem (gen z) (-qbarI)
  have hz : z ∈ gen z := IntermediateField.subset_adjoin ↥Qbar {z} (by simp)
  have hc : conj z ∈ gen z := by
    rw [show conj z = -Complex.I * z by exact finiteWitness_one_conj]
    exact (gen z).mul_mem hi hz
  let c : gen z := ⟨conj z, hc⟩
  have hc_eq : algebraMap (gen z) ℂ c = conj z := rfl
  have hint : IsIntegral (gen z) (conj z) := by
    rw [← hc_eq]
    exact isIntegral_algebraMap
  rw [conjDegree, if_pos hint, ← hc_eq, minpoly.eq_X_sub_C]
  simp

theorem finiteWitness_one_mem_transcendentals : finiteWitness 1 ∈ Transcendentals := by
  let s : ℂ := ((liouvilleNumber 2 : ℝ) : ℂ)
  have hs : Transcendental ℚ s :=
    liouville_two_transcendental_Qbar.restrictScalars (algebraMap ℚ Qbar).injective
  have hyalg : IsAlgebraic ℚ ((1 : ℂ) + Complex.I) :=
    isAlgebraic_one.add Complex.isIntegral_rat_I.isAlgebraic
  have hy0 : (1 : ℂ) + Complex.I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
  intro hz
  have hprod : IsAlgebraic ℚ (((1 : ℂ) + Complex.I) * s) := by
    simpa [finiteWitness, s, add_mul] using hz
  exact hs (IsAlgebraic.of_mul (mem_nonZeroDivisors_iff_ne_zero.mpr hy0) hyalg hprod)

theorem witnessPoly_natDegree {n : ℕ} (hn : 2 ≤ n) :
    (witnessPoly n).natDegree = n := by
  have hi : qbarI ≠ 0 := by
    intro h
    have hv := congrArg Subtype.val h
    simp [qbarI] at hv
  rw [witnessPoly]
  calc
    (Polynomial.X ^ n + Polynomial.C qbarI * Polynomial.X).natDegree =
        (Polynomial.X ^ n : Polynomial Qbar).natDegree := by
      apply Polynomial.natDegree_add_eq_left_of_natDegree_lt
      rw [Polynomial.natDegree_C_mul_X qbarI hi, Polynomial.natDegree_X_pow]
      omega
    _ = n := Polynomial.natDegree_X_pow n

theorem aeval_witnessPoly (n : ℕ) :
    Polynomial.aeval (((liouvilleNumber 2 : ℝ) : ℂ)) (witnessPoly n) = finiteWitness n := by
  rw [witnessPoly]
  simp only [map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_mul,
    Polynomial.aeval_C]
  rw [show algebraMap Qbar ℂ qbarI = Complex.I by rfl]
  rfl

theorem finiteWitness_transcendental_Qbar {n : ℕ} (hn : 2 ≤ n) :
    Transcendental Qbar (finiteWitness n) := by
  let s : ℂ := ((liouvilleNumber 2 : ℝ) : ℂ)
  have hs : Transcendental Qbar s := liouville_two_transcendental_Qbar
  have hpdeg : (witnessPoly n).natDegree = n := witnessPoly_natDegree hn
  have hp0 : witnessPoly n ≠ 0 := by
    intro hp
    have := congrArg Polynomial.natDegree hp
    rw [hpdeg] at this
    simp at this
    omega
  have ht := hs.aeval (witnessPoly n) (by omega)
    (mem_nonZeroDivisors_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp0))
  rw [aeval_witnessPoly] at ht
  exact ht

theorem finiteWitness_mem_transcendentals {n : ℕ} (hn : 2 ≤ n) :
    finiteWitness n ∈ Transcendentals := by
  exact (finiteWitness_transcendental_Qbar hn).restrictScalars
    (algebraMap ℚ Qbar).injective

theorem finiteWitness_conj (n : ℕ) :
    conj (finiteWitness n) =
      (((liouvilleNumber 2 : ℝ) : ℂ)) ^ n -
        Complex.I * ((liouvilleNumber 2 : ℝ) : ℂ) := by
  simp [finiteWitness, Complex.conj_ofReal, Complex.conj_I]
  rfl

theorem finiteWitness_recover (n : ℕ) :
    (finiteWitness n - conj (finiteWitness n)) / ((2 : ℂ) * Complex.I) =
      ((liouvilleNumber 2 : ℝ) : ℂ) := by
  rw [finiteWitness_conj, finiteWitness]
  field_simp [Complex.I_ne_zero]
  ring

theorem finiteWitness_adjoin_pair {n : ℕ} (_hn : 2 ≤ n) :
    IntermediateField.adjoin Qbar {finiteWitness n, conj (finiteWitness n)} =
      gen (((liouvilleNumber 2 : ℝ) : ℂ)) := by
  let s : ℂ := ((liouvilleNumber 2 : ℝ) : ℂ)
  let z : ℂ := finiteWitness n
  let L : IntermediateField Qbar ℂ := IntermediateField.adjoin Qbar {z, conj z}
  let S : IntermediateField Qbar ℂ := gen s
  have hsS : s ∈ S := IntermediateField.subset_adjoin Qbar {s} (by simp)
  have hiS : Complex.I ∈ S := IntermediateField.algebraMap_mem S qbarI
  have hzS : z ∈ S := by
    change s ^ n + Complex.I * s ∈ S
    exact S.add_mem (S.pow_mem hsS n) (S.mul_mem hiS hsS)
  have hcS : conj z ∈ S := by
    rw [show conj z = s ^ n - Complex.I * s by exact finiteWitness_conj n]
    exact S.sub_mem (S.pow_mem hsS n) (S.mul_mem hiS hsS)
  have hLS : L ≤ S := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with (rfl | rfl)
    · exact hzS
    · exact hcS
  have hzL : z ∈ L := IntermediateField.subset_adjoin Qbar {z, conj z} (by simp)
  have hcL : conj z ∈ L := IntermediateField.subset_adjoin Qbar {z, conj z} (by simp)
  have hiL : Complex.I ∈ L := IntermediateField.algebraMap_mem L qbarI
  have htwoL : (2 : ℂ) ∈ L := by
    exact IntermediateField.algebraMap_mem L (2 : Qbar)
  have hsL : s ∈ L := by
    change ((liouvilleNumber 2 : ℝ) : ℂ) ∈ L
    rw [← finiteWitness_recover n]
    exact L.div_mem (L.sub_mem hzL hcL) (L.mul_mem htwoL hiL)
  have hSL : S ≤ L := IntermediateField.adjoin_le_iff.mpr (by simpa using hsL)
  exact le_antisymm hLS hSL

theorem relfinrank_adjoin_aeval_eq_natDegree
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (s : E) (hs : Transcendental K s) (p : Polynomial K)
    (_hp : 0 < p.natDegree) :
    IntermediateField.relfinrank (IntermediateField.adjoin K {Polynomial.aeval s p})
      (IntermediateField.adjoin K {s}) = p.natDegree := by
  let r : RatFunc K := algebraMap (Polynomial K) (RatFunc K) p
  let A : IntermediateField K (RatFunc K) := IntermediateField.adjoin K {r}
  let B : IntermediateField K (RatFunc K) := ⊤
  have hrat : Module.finrank A (RatFunc K) = p.natDegree := by
    change Module.finrank (IntermediateField.adjoin K {r}) (RatFunc K) = p.natDegree
    rw [RatFunc.finrank_eq_max_natDegree]
    simp [r]
  have hrel : IntermediateField.relfinrank A B = p.natDegree := by
    rw [show B = ⊤ by rfl, IntermediateField.relfinrank_top_right]
    exact hrat
  let S : IntermediateField K E := IntermediateField.adjoin K {s}
  let e : RatFunc K ≃ₐ[K] S := RatFunc.algEquivOfTranscendental s hs
  let inc : S →ₐ[K] E := S.val
  have hmap₁ := (IntermediateField.relfinrank_map_map A B e.toAlgHom).trans hrel
  have hmap₂ := (IntermediateField.relfinrank_map_map (A.map e.toAlgHom)
    (B.map e.toAlgHom) inc).trans hmap₁
  have hBe : B.map e.toAlgHom = ⊤ := by
    change (IntermediateField.map e.toAlgHom ⊤) = ⊤
    rw [← e.toAlgHom.fieldRange_eq_map, e.fieldRange_eq_top]
  have htop : (B.map e.toAlgHom).map inc = S := by
    rw [hBe]
    rw [← inc.fieldRange_eq_map]
    change S.val.fieldRange = S
    exact S.fieldRange_val
  rw [htop] at hmap₂
  simpa [A, B, S, e, inc, r, IntermediateField.adjoin_map,
    RatFunc.algEquivOfTranscendental_algebraMap] using hmap₂

theorem finiteWitness_degree {n : ℕ} (hn : 2 ≤ n) :
    conjDegree (finiteWitness n) = n := by
  let s : ℂ := ((liouvilleNumber 2 : ℝ) : ℂ)
  let z : ℂ := finiteWitness n
  let S : IntermediateField Qbar ℂ := gen s
  let A : IntermediateField (gen z) ℂ := IntermediateField.adjoin (gen z) {conj z}
  have hdeg : (witnessPoly n).natDegree = n := witnessPoly_natDegree hn
  have hrel : IntermediateField.relfinrank (gen z) S = n := by
    have h := relfinrank_adjoin_aeval_eq_natDegree s
      liouville_two_transcendental_Qbar (witnessPoly n) (by omega)
    rw [aeval_witnessPoly] at h
    simpa [z, S, s, gen, hdeg] using h
  have hpair : IntermediateField.adjoin Qbar {z, conj z} = S := by
    exact finiteWitness_adjoin_pair hn
  have hle : gen z ≤ S := by
    rw [← hpair]
    exact IntermediateField.adjoin.mono Qbar {z} {z, conj z} (by simp)
  let T : IntermediateField (gen z) ℂ := IntermediateField.extendScalars hle
  have hfinT : Module.finrank (gen z) T = n := by
    rw [← IntermediateField.relfinrank_eq_finrank_of_le hle]
    exact hrel
  letI : Module.Finite (gen z) T := Module.finite_of_finrank_pos (by
    rw [hfinT]
    omega)
  have hcS : conj z ∈ S := by
    rw [← hpair]
    exact IntermediateField.subset_adjoin Qbar {z, conj z} (by simp)
  let c : T := ⟨conj z, hcS⟩
  have hcintT : IsIntegral (gen z) c := IsIntegral.of_finite (gen z) c
  have hint : IsIntegral (gen z) (conj z) := by
    exact (isIntegral_algHom_iff T.val T.val.injective).mpr hcintT
  have hAT : A = T := by
    apply IntermediateField.restrictScalars_injective Qbar
    change (IntermediateField.adjoin (IntermediateField.adjoin Qbar {z})
      {conj z}).restrictScalars Qbar = S
    rw [IntermediateField.adjoin_adjoin_left]
    simpa only [Set.singleton_union] using hpair
  have hmin : (minpoly (gen z) (conj z)).natDegree = n := by
    have hfinA : Module.finrank (gen z) A = n := by rw [hAT, hfinT]
    change Module.finrank (gen z) (IntermediateField.adjoin (gen z) {conj z}) = n at hfinA
    rw [IntermediateField.adjoin.finrank hint] at hfinA
    exact hfinA
  rw [conjDegree, if_pos hint, hmin]

theorem degree_two_smoke :
    finiteWitness 2 ∈ Transcendentals ∧ conjDegree (finiteWitness 2) = 2 := by
  exact ⟨finiteWitness_mem_transcendentals (by norm_num),
    finiteWitness_degree (by norm_num)⟩

theorem finite_spectrum (n : ℕ) (hn : n ≠ 0) :
    ∃ z ∈ Transcendentals, conjDegree z = (n : ℕ∞) := by
  rcases n with _ | n
  · exact (hn rfl).elim
  · rcases n with _ | n
    · exact ⟨finiteWitness 1, finiteWitness_one_mem_transcendentals,
        finiteWitness_one_degree⟩
    · exact ⟨finiteWitness (n + 2), finiteWitness_mem_transcendentals (by omega),
        finiteWitness_degree (by omega)⟩

theorem conjDegree_ne_zero (z : ℂ) : conjDegree z ≠ 0 := by
  rw [conjDegree]
  split
  · exact_mod_cast (minpoly.natDegree_pos (by assumption)).ne'
  · simp

theorem exists_large_real_transcendence_basis :
    ∃ s : Set ℝ, IsTranscendenceBasis ℚ ((↑) : s → ℝ) ∧ 2 ≤ Cardinal.mk s := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ ℝ
  have hQ : Transcendental ℚ (liouvilleNumber (2 : ℕ)) :=
    (transcendental_liouvilleNumber (m := 2) (by norm_num)).extendScalars ℚ
  letI : Algebra.Transcendental ℚ ℝ := ⟨⟨liouvilleNumber 2, hQ⟩⟩
  haveI : Nonempty s := hs.nonempty_iff_transcendental.mpr inferInstance
  have hc := hs.lift_cardinalMk_eq_max_lift
  simp only [Cardinal.lift_id, Cardinal.mk_real, Cardinal.mkRat] at hc
  refine ⟨s, hs, ?_⟩
  by_contra h
  have hs_lt : Cardinal.mk s < 2 := lt_of_not_ge h
  have hs_le : Cardinal.mk s ≤ Cardinal.aleph0 := hs_lt.le.trans (by simp)
  have hbad : Cardinal.continuum = Cardinal.aleph0 := by
    simpa [max_eq_left hs_le] using hc
  exact Cardinal.aleph0_lt_continuum.ne hbad.symm

theorem exists_qbar_algebraicallyIndependent_real_pair :
    ∃ e : Fin 2 → ℝ,
      AlgebraicIndependent Qbar (fun j ↦ ((e j : ℝ) : ℂ)) := by
  obtain ⟨s, hs, htwo⟩ := exists_large_real_transcendence_basis
  have he : Nonempty (Fin 2 ↪ s) := by
    rw [← Cardinal.le_def, Cardinal.mk_fin]
    exact htwo
  let e : Fin 2 ↪ s := Classical.choice he
  have hR : AlgebraicIndependent ℚ (fun j : Fin 2 ↦ ((e j : s) : ℝ)) :=
    hs.1.comp e e.injective
  let f : ℝ →ₐ[ℚ] ℂ := IsScalarTower.toAlgHom ℚ ℝ ℂ
  have hC : AlgebraicIndependent ℚ (f ∘ fun j : Fin 2 ↦ ((e j : s) : ℝ)) :=
    hR.map' f.injective
  have hCQ : AlgebraicIndependent Qbar
      (f ∘ fun j : Fin 2 ↦ ((e j : s) : ℝ)) := hC.extendScalars Qbar
  refine ⟨fun j ↦ ((e j : s) : ℝ), ?_⟩
  simpa [f, Function.comp_def] using hCQ

def optionFinTwo : Option Unit → Fin 2
  | none => 1
  | some _ => 0

theorem optionFinTwo_injective : Function.Injective optionFinTwo := by
  intro a b h
  rcases a with _ | ⟨⟩ <;> rcases b with _ | ⟨⟩ <;> simp [optionFinTwo] at h ⊢

def optionSwapUnit : Option Unit → Option Unit
  | none => some ()
  | some _ => none

theorem optionSwapUnit_injective : Function.Injective optionSwapUnit := by
  intro a b h
  rcases a with _ | ⟨⟩ <;> rcases b with _ | ⟨⟩ <;> simp [optionSwapUnit] at h ⊢

theorem top_witness_exists :
    ∃ z ∈ Transcendentals, conjDegree z = ⊤ := by
  obtain ⟨e, he⟩ := exists_qbar_algebraicallyIndependent_real_pair
  let x : ℂ := ((e 0 : ℝ) : ℂ)
  let y : ℂ := ((e 1 : ℝ) : ℂ)
  have hopt : AlgebraicIndependent Qbar
      (fun o : Option Unit ↦ o.elim y (fun _ ↦ x)) := by
    convert he.comp optionFinTwo optionFinTwo_injective using 1
    ext o
    rcases o with _ | ⟨⟩ <;> rfl
  have hsplit := (AlgebraicIndependent.option_iff (R := Qbar)
    (x := fun _ : Unit ↦ x) (a := y)).mp hopt
  have hySub : Transcendental (Algebra.adjoin Qbar (Set.range fun _ : Unit ↦ x)) y :=
    hsplit.2
  have hy : Transcendental (gen x) y := by
    have hrange : Set.range (fun _ : Unit ↦ x) = {x} := by
      ext a
      simp
    rw [hrange] at hySub
    change Transcendental (IntermediateField.adjoin Qbar {x}) y
    rw [IntermediateField.transcendental_adjoin_iff]
    exact hySub
  let z : ℂ := x + Complex.I * y
  have hzBase : Transcendental (gen x) z := by
    let bx : gen x := ⟨x, IntermediateField.subset_adjoin Qbar {x} (by simp)⟩
    let bi : gen x := ⟨Complex.I, IntermediateField.algebraMap_mem (gen x) qbarI⟩
    let p : Polynomial (gen x) := Polynomial.C bx + Polynomial.C bi * Polynomial.X
    have hbi : bi ≠ 0 := by
      intro h
      have hv := congrArg Subtype.val h
      exact Complex.I_ne_zero hv
    have hpdeg : p.natDegree = 1 := by
      change (Polynomial.C bx + Polynomial.C bi * Polynomial.X).natDegree = 1
      calc
        (Polynomial.C bx + Polynomial.C bi * Polynomial.X).natDegree =
            (Polynomial.C bi * Polynomial.X).natDegree := by
          apply Polynomial.natDegree_add_eq_right_of_natDegree_lt
          rw [Polynomial.natDegree_C_mul_X bi hbi]
          simp
        _ = 1 := Polynomial.natDegree_C_mul_X bi hbi
    have hp0 : p ≠ 0 := by
      intro hp
      have := congrArg Polynomial.natDegree hp
      rw [hpdeg] at this
      simp at this
    have hz := hy.aeval p (by simp [hpdeg])
      (mem_nonZeroDivisors_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp0))
    change Transcendental (gen x) (x + Complex.I * y)
    convert hz using 1
    simp [p, bx, bi]
  have hzQbar : Transcendental Qbar z :=
    hzBase.restrictScalars (algebraMap Qbar (gen x)).injective
  have hzQ : Transcendental ℚ z := hzQbar.restrictScalars (algebraMap ℚ Qbar).injective
  have hzSub : Transcendental (Algebra.adjoin Qbar (Set.range fun _ : Unit ↦ x)) z := by
    have hrange : Set.range (fun _ : Unit ↦ x) = {x} := by
      ext a
      simp
    rw [hrange]
    rw [← IntermediateField.transcendental_adjoin_iff]
    exact hzBase
  have hxz : AlgebraicIndependent Qbar
      (fun o : Option Unit ↦ o.elim z (fun _ ↦ x)) :=
    (AlgebraicIndependent.option_iff (R := Qbar)).mpr ⟨hsplit.1, hzSub⟩
  have hzx : AlgebraicIndependent Qbar
      (fun o : Option Unit ↦ o.elim x (fun _ ↦ z)) := by
    convert hxz.comp optionSwapUnit optionSwapUnit_injective using 1
    ext o
    rcases o with _ | ⟨⟩ <;> rfl
  have hxSub : Transcendental (Algebra.adjoin Qbar (Set.range fun _ : Unit ↦ z)) x :=
    ((AlgebraicIndependent.option_iff (R := Qbar)
      (x := fun _ : Unit ↦ z) (a := x)).mp hzx).2
  have hxBase : Transcendental (gen z) x := by
    have hrange : Set.range (fun _ : Unit ↦ z) = {z} := by
      ext a
      simp
    rw [hrange] at hxSub
    change Transcendental (IntermediateField.adjoin Qbar {z}) x
    rw [IntermediateField.transcendental_adjoin_iff]
    exact hxSub
  have hconjFormula : conj z = (2 : ℂ) * x - z := by
    simp [z, x, y, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hconj : Transcendental (gen z) (conj z) := by
    let bz : gen z := ⟨z, IntermediateField.subset_adjoin Qbar {z} (by simp)⟩
    let btwo : gen z := ⟨(2 : ℂ), IntermediateField.algebraMap_mem (gen z) (2 : Qbar)⟩
    let p : Polynomial (gen z) := Polynomial.C (-bz) + Polynomial.C btwo * Polynomial.X
    have htwo : btwo ≠ 0 := by
      intro h
      have hv := congrArg Subtype.val h
      norm_num at hv
    have hpdeg : p.natDegree = 1 := by
      change (Polynomial.C (-bz) + Polynomial.C btwo * Polynomial.X).natDegree = 1
      calc
        (Polynomial.C (-bz) + Polynomial.C btwo * Polynomial.X).natDegree =
            (Polynomial.C btwo * Polynomial.X).natDegree := by
          apply Polynomial.natDegree_add_eq_right_of_natDegree_lt
          rw [Polynomial.natDegree_C_mul_X btwo htwo]
          simp
        _ = 1 := Polynomial.natDegree_C_mul_X btwo htwo
    have hp0 : p ≠ 0 := by
      intro hp
      have := congrArg Polynomial.natDegree hp
      rw [hpdeg] at this
      simp at this
    have ht := hxBase.aeval p (by simp [hpdeg])
      (mem_nonZeroDivisors_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp0))
    rw [hconjFormula]
    convert ht using 1
    simp [p, bz, btwo]
    ring
  refine ⟨z, hzQ, ?_⟩
  rw [conjDegree, if_neg]
  exact fun hint ↦ hconj hint.isAlgebraic

theorem spectrum_statement_compiles :
    ∀ n : ℕ∞, n ≠ 0 → ∃ z ∈ Transcendentals, conjDegree z = n := by
  intro n hn
  exact ENat.recTopCoe
    (C := fun m : ℕ∞ ↦ m ≠ 0 → ∃ z ∈ Transcendentals, conjDegree z = m)
    (fun _ ↦ top_witness_exists)
    (fun m hm ↦ finite_spectrum m (by exact_mod_cast hm)) n hn

#print axioms conjDegree_ne_zero
#print axioms finiteWitness_one_degree
#print axioms relfinrank_adjoin_aeval_eq_natDegree
#print axioms degree_two_smoke
#print axioms finiteWitness_degree
#print axioms finite_spectrum
#print axioms top_witness_exists
#print axioms spectrum_statement_compiles

/-- Every stratum but the zeroth is inhabited. -/
theorem stratum_nonempty {n : ℕ∞} (hn : n ≠ 0) : (stratum n).Nonempty := by
  obtain ⟨z, hz, hd⟩ := spectrum_statement_compiles n hn
  exact ⟨z, hz, hd⟩

/-- The zeroth stratum is empty. -/
theorem stratum_zero : stratum 0 = ∅ := by
  ext z
  simp only [stratum, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun _ ↦ conjDegree_ne_zero z

end

end MoebiusTranscendental
