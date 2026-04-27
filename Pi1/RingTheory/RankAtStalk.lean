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

lemma Algebra.comap_surjective_iff_injective_of_finite :
    (PrimeSpectrum.comap (algebraMap R S)).Surjective ↔ Function.Injective (algebraMap R S) := by
  refine ⟨fun h ↦ ?_, fun h ↦
    have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr h
    Algebra.IsIntegral.specComap_surjective⟩
  apply injective_of_isLocalization_isMaximal (fun P _ ↦ Localization.AtPrime P)
    (fun P _ ↦ Localization.AtPrime P ⊗[R] S)
  intro p _
  apply (faithfulSMul_iff_algebraMap_injective _ _).mp
  obtain ⟨⟨Q, _⟩, hQ⟩ := h ⟨p, inferInstance⟩
  have : Q.LiesOver p := ⟨(congr($(hQ).asIdeal)).symm⟩
  have : Nontrivial (Localization.AtPrime p ⊗[R] S) := by
    let f : Localization.AtPrime p ⊗[R] S →ₐ[R] Localization.AtPrime Q :=
      Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R _ _)
        (IsScalarTower.toAlgHom R S _) (fun _ _ ↦ Commute.all _ _)
    exact f.domain_nontrivial
  infer_instance

lemma Algebra.rankAtStalk_pos_iff_injective :
    (∀ p, 0 < Module.rankAtStalk (R := R) S p) ↔ Function.Injective (algebraMap R S) := by
  rw [← comap_surjective_iff_injective_of_finite, rankAtStalk_pos_iff_specComap_surjective]

lemma Algebra.bijective_algebraMap_of_free [Nontrivial R] [Module.Free R S]
    (h : Module.finrank R S = 1) :
    Function.Bijective (algebraMap R S) := by
  refine ⟨Algebra.rankAtStalk_pos_iff_injective.mp
      (fun p ↦ by simp [Module.rankAtStalk_eq_finrank_of_free, h]), ?_⟩
  have : Module.Free R (Module.End R S) := .of_equiv (dualTensorHomEquiv R S S)
  let f : S →ₗ[R] (S →ₗ[R] S) := LinearMap.mul R S
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro s hs
    rw [show s = f s 1 by simp [f], hs, LinearMap.zero_apply]
  have : (LinearMap.mul R S) 1 = 1 := by
    ext
    simp
  have h1 : LinearMap.trace R S ∘ₗ (f ∘ₗ Algebra.linearMap R S) = LinearMap.id := by
    ext
    simp [f, this, h]
  let e := dualTensorHomEquiv R S S
  let b : Module.Basis (Unit × Unit) R (Module.End R S) :=
    Module.Basis.map (Module.Basis.tensorProduct
      (Module.Basis.dualBasis <| Module.basisUnique Unit h) <| Module.basisUnique Unit h) e
  have h2 : (f ∘ₗ Algebra.linearMap R S) ∘ₗ LinearMap.trace R S = LinearMap.id := by
    apply b.ext
    intro i
    apply (Module.basisUnique Unit h).ext
    intro j
    simp [f, b, e, Module.Basis.tensorProduct]
  let eq : R ≃ₗ[R] Module.End R S := .ofLinear (f ∘ₗ Algebra.linearMap R S) (.trace R S) h2 h1
  have : Function.Bijective (f ∘ₗ Algebra.linearMap R S) := eq.bijective
  have hf : Function.Bijective f := ⟨hinj, .of_comp this.2⟩
  exact (Function.Bijective.of_comp_iff' hf _).mp this |>.2

lemma Algebra.surjective_algebraMap_of_rankAtStalk_le_one
      (h : ∀ p, Module.rankAtStalk (R := R) S p ≤ 1) : Function.Surjective (algebraMap R S) := by
  apply surjective_of_isLocalization_isMaximal (fun P _ ↦ Localization.AtPrime P)
    (fun P _ ↦ Localization.AtPrime P ⊗[R] S)
  intro p _
  have := h ⟨p, inferInstance⟩
  by_cases h : Module.rankAtStalk S ⟨p, inferInstance⟩ = 0
  · have : Subsingleton (Localization.AtPrime p ⊗[R] S) := by
      apply Module.subsingleton_of_rank_zero (R := Localization.AtPrime p)
      simp [← Module.finrank_eq_rank,
        ← Module.rankAtStalk_eq_finrank_tensorProduct ⟨p, inferInstance⟩, h]
    exact Function.surjective_to_subsingleton _
  · refine (Algebra.bijective_algebraMap_of_free ?_).2
    rw [← Module.rankAtStalk_eq_finrank_tensorProduct ⟨p, inferInstance⟩]
    omega

lemma Algebra.rankAtStalk_le_one_iff_surjective :
    (∀ p, Module.rankAtStalk (R := R) S p ≤ 1) ↔ Function.Surjective (algebraMap R S) :=
  (Module.Flat.tfae_algebraMap_surjective R S).out 2 0

/-- If `S` is a finite, flat `R`-algebra of constant rank `1`, `S` is isomorphic to `R`.-/
lemma Algebra.bijective_of_rankAtStalk {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S] (h : Module.rankAtStalk (R := R) S = 1) :
    Function.Bijective (algebraMap R S) :=
  ⟨rankAtStalk_pos_iff_injective.mp (by simp [h]),
    rankAtStalk_le_one_iff_surjective.mp (by simp [h])⟩

end rankAtStalk
