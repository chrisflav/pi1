/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Tower
import Pi1.RingTheory.RingOfDefinition.Utils

/-!
# Descent of finitely presented algebras
If `A` is a finitely presented `R`-algebra, there exists a subring `R₀` of `R` of finite type
over `ℤ` and a finitely presented `R₀`-algebra `A₀` such that `A` is `R`-isomorphic to
`R ⊗[R₀] A₀`.
`R₀` is obtained by choosing a presentation for `A` and adjoining the finitely-many defining
coefficients of `A` to `R`. More generally we show, that `R ⊗[R₀] A₀` is `R`-isomorphic to `A`
whenever `R₀` contains all defining coefficients of `A`.
-/

universe u v w t

open TensorProduct

namespace Algebra

variable {R : Type u} [CommRing R] {ι : Type v}
variable {S : Type w} [CommRing S] [Algebra R S]

section

variable {T : Type t} [CommRing T] [Algebra S T] {T' : Type v} [CommRing T'] [Algebra R T']
variable {I : Ideal (MvPolynomial ι R)}

variable [Algebra R T] [IsScalarTower R S T]

lemma baseChange_MvPolynomialQuot_ext {f g : S ⊗[R] (MvPolynomial ι R ⧸ I) →ₐ[S] T}
    (h : ∀ (i : ι), f (1 ⊗ₜ (Ideal.Quotient.mk I <| MvPolynomial.X i))
      = g (1 ⊗ₜ (Ideal.Quotient.mk I <| MvPolynomial.X i))) : f = g := by
  apply TensorProduct.ext (by ext)
  apply AlgHom.cancel_surjective (Ideal.Quotient.mkₐ R I)
  · exact Ideal.Quotient.mkₐ_surjective R I
  · apply MvPolynomial.algHom_ext
    exact h

end

namespace RingOfDefinition

variable (I : Ideal (MvPolynomial ι S))
variable (J : Ideal (MvPolynomial ι R))
  (hJ : J ≤ Ideal.comap (MvPolynomial.map <| algebraMap R S) I)

noncomputable def baseChangeHom (hJ : J ≤ Ideal.comap (MvPolynomial.map <| algebraMap R S) I) :
    S ⊗[R] (MvPolynomial ι R ⧸ J) →ₐ[S] MvPolynomial ι S ⧸ I := by
  fapply Algebra.TensorProduct.lift
  · exact Algebra.ofId _ _
  · let f : MvPolynomial ι R →ₐ[R] MvPolynomial ι S :=
      MvPolynomial.aeval MvPolynomial.X
    let g : MvPolynomial ι S →ₐ[R] MvPolynomial ι S ⧸ I :=
      Ideal.Quotient.mkₐ R I
    fapply Ideal.Quotient.liftₐ
    exact g.comp f
    intro x hx
    simp only [AlgHom.comp_apply]
    rw [← RingHom.mem_ker]
    change f x ∈ RingHom.ker (Ideal.Quotient.mkₐ R I)
    erw [Ideal.Quotient.mkₐ_ker R I]
    exact (hJ hx)
  · intro s p
    apply mul_comm

@[simp]
lemma baseChangeHom_mk_X (hJ : J ≤ Ideal.comap (MvPolynomial.map <| algebraMap R S) I) (i : ι) :
    (baseChangeHom I J hJ) (1 ⊗ₜ[R] (Ideal.Quotient.mk J) (MvPolynomial.X i))
      = Ideal.Quotient.mk I (MvPolynomial.X i) := by
  simp [baseChangeHom]

omit [Algebra R S] in
lemma exists_preimage_of_coefficients' (f : R →+* S) (t : MvPolynomial ι S)
    (hc : MvPolynomial.coefficients t ⊆ Set.range f) :
    ∃ (p : MvPolynomial ι R), MvPolynomial.map f p = t := by
  have (m : ι →₀ ℕ) : ∃ (r : R), f r = t.coeff m ∧ (t.coeff m = 0 → r = 0) := by
    by_cases h : m ∈ t.support
    · obtain ⟨r, hr⟩ := hc (MvPolynomial.coefficients_mem m h)
      use r
      simp_all
    · simp at h
      use 0
      simp only [map_zero, implies_true, and_true]
      exact h.symm
  choose c h1 h2 using this
  let p : (ι →₀ ℕ) →₀ R := Finsupp.ofSupportFinite c <| by
    apply Set.Finite.subset
    · exact Finsupp.finite_support t
    · intro m minc h
      exact minc (h2 m h)
  use p
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_map]
  exact h1 m

-- TODO: add choose def also for ring hom instead of algebraMap

lemma exists_preimage_of_coefficients (t : MvPolynomial ι S)
    (hc : MvPolynomial.coefficients t ⊆ Set.range (algebraMap R S)) :
    ∃ (p : MvPolynomial ι R), MvPolynomial.map (algebraMap R S) p = t := by
  have (m : ι →₀ ℕ) : ∃ (r : R), algebraMap R S r = t.coeff m ∧ (t.coeff m = 0 → r = 0) := by
    by_cases h : m ∈ t.support
    · obtain ⟨r, hr⟩ := hc (MvPolynomial.coefficients_mem m h)
      use r
      simp_all
    · simp at h
      use 0
      simp only [map_zero, implies_true, and_true]
      exact h.symm
  choose c h1 h2 using this
  let p : (ι →₀ ℕ) →₀ R := Finsupp.ofSupportFinite c <| by
    apply Set.Finite.subset
    · exact Finsupp.finite_support t
    · intro m minc h
      exact minc (h2 m h)
  use p
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_map]
  exact h1 m

noncomputable def MvPolynomial.choosePreimageOfCoeffs (t : MvPolynomial ι S)
    (h : MvPolynomial.coefficients t ⊆ Set.range (algebraMap R S)) :
    MvPolynomial ι R :=
  (exists_preimage_of_coefficients t h).choose

@[simp]
lemma MvPolynomial.choosePreimageOfCoeffs_map (t : MvPolynomial ι S)
    (h : MvPolynomial.coefficients t ⊆ Set.range (algebraMap R S)) :
    MvPolynomial.map (algebraMap R S) (MvPolynomial.choosePreimageOfCoeffs t h) = t :=
  (exists_preimage_of_coefficients t h).choose_spec

noncomputable def MvPolynomial.Set.choosePreimageOfCoeffs (T : Set (MvPolynomial ι S))
    (h : MvPolynomial.Set.coefficients T ⊆ Set.range (algebraMap R S))
    (t : T) : MvPolynomial ι R := by
  apply MvPolynomial.choosePreimageOfCoeffs t.val
  apply Set.Subset.trans
  exact MvPolynomial.Set.coefficients_in T t.val t.property
  exact h

end RingOfDefinition
