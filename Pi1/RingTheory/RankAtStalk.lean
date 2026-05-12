import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Flat.Rank
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Pi1.Mathlib.RingTheory.RingHom.Integral

universe u

open TensorProduct

section rankAtStalk

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

attribute [local instance] Module.free_of_flat_of_isLocalRing

namespace Module

open LocalizedModule Localization

instance {R : Type*} [CommSemiring R] (S : Submonoid R)
    (M : Type*) [AddCommMonoid M] [Module R M] [Module.Finite R M] :
    Module.Finite (Localization S) (LocalizedModule S M) :=
  Module.Finite.of_isLocalizedModule S (LocalizedModule.mkLinearMap S M)

variable [Flat R M] [Module.Finite R M]

end Module

variable {S : Type*} [CommRing S] [Algebra R S] [Module.Flat R S] [Module.Finite R S]

set_option synthInstance.maxHeartbeats 0 in
lemma Algebra.rankAtStalk_pos_iff_mem_range_specComap (p : PrimeSpectrum R) :
    0 < Module.rankAtStalk (R := R) S p ↔
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap R S)) := by
  rw [Module.rankAtStalk_eq, Module.finrank_pos_iff, p.nontrivial_iff_mem_rangeComap]

/-- The rank is positive at all stalks if and only if the induced map on prime spectra is
surjective. -/
lemma Algebra.rankAtStalk_pos_iff_specComap_surjective :
    (∀ p, 0 < Module.rankAtStalk (R := R) S p) ↔
      Function.Surjective (PrimeSpectrum.comap (algebraMap R S)) := by
  simp_rw [rankAtStalk_pos_iff_mem_range_specComap, ← Set.range_eq_univ,
    Set.eq_univ_iff_forall]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
instance (Rₚ : Type*) [CommSemiring Rₚ] [Algebra R Rₚ] (p : Ideal R) [p.IsPrime]
    [IsLocalization.AtPrime Rₚ p] :
    IsLocalizedModule.AtPrime p (IsScalarTower.toAlgHom R S (Rₚ ⊗[R] S) : S →ₗ[R] Rₚ ⊗[R] S) := by
  rw [IsLocalizedModule.AtPrime, isLocalizedModule_iff_isBaseChange (S := p.primeCompl) (A := Rₚ)]
  exact TensorProduct.isBaseChange _ _ _

attribute [local instance] Algebra.TensorProduct.rightAlgebra

end rankAtStalk
