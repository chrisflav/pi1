import Mathlib
import Pi1.RingTheory.CotangentBaseChange
import Pi1.RingTheory.KaehlerBaseChange

universe u

open TensorProduct

namespace Module

variable {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable (M : Type*) [AddCommGroup M] [Module R M]

-- #22565
/-- Flat descends along faithfully flat ring maps. -/
lemma Flat.of_flat_tensorProduct [Module.FaithfullyFlat R S] [Module.Flat S (S ⊗[R] M)] :
    Module.Flat R M := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  have : Flat R (S ⊗[R] M) := Flat.trans _ S _
  rw [← FaithfullyFlat.lTensor_injective_iff_injective R S]
  have : LinearMap.lTensor S (LinearMap.lTensor M f) =
      (TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ LinearMap.lTensor (S ⊗[R] M) f ∘ₗ
        (TensorProduct.assoc _ _ _ _).symm.toLinearMap := by
    ext
    simp
  simpa [this] using lTensor_preserves_injective_linearMap f hf

-- #22565
/-- Faithful flatness is preserved by arbitrary base change. -/
instance [Module.FaithfullyFlat R M] : Module.FaithfullyFlat S (S ⊗[R] M) := by
  rw [Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality]
  refine ⟨inferInstance, fun N _ _ hN ↦ ?_⟩
  let _ : Module R N := Module.compHom N (algebraMap R S)
  have : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun r ↦ congrFun rfl
  have := (AlgebraTensorModule.cancelBaseChange R S S N M).symm.subsingleton
  exact FaithfullyFlat.rTensor_reflects_triviality R M N

end Module

namespace LinearMap

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable (M N : Type*) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
  [Module S N] [IsScalarTower R S N]

lemma liftBaseChange_surjective {f : M →ₗ[R] N} (hf : Function.Surjective f) :
    Function.Surjective (f.liftBaseChange S) := by
  intro n
  obtain ⟨m, rfl⟩ := hf n
  use 1 ⊗ₜ m
  simp

end LinearMap

namespace Algebra

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

lemma FormallySmooth.of_formallySmooth_tensorProduct
    [Algebra.FinitePresentation R S]
    (T : Type u) [CommRing T] [Algebra R T]
    [FormallySmooth T (T ⊗[R] S)] [Module.FaithfullyFlat R T] :
    FormallySmooth R S := by
  rw [FormallySmooth.iff_subsingleton_and_projective]
  constructor
  · have : Subsingleton (T ⊗[R] H1Cotangent R S) := (tensorH1CotangentOfFlat R S T).subsingleton
    exact Module.FaithfullyFlat.lTensor_reflects_triviality R T (H1Cotangent R S)
  · let _ : Algebra T (S ⊗[R] T) := TensorProduct.includeRight.toRingHom.toAlgebra
    let e : S ⊗[R] T ≃ₐ[T] T ⊗[R] S :=
      AlgEquiv.ofRingEquiv (f := TensorProduct.comm R S T) <| by simp [RingHom.algebraMap_toAlgebra]
    have : FormallySmooth T (S ⊗[R] T) := FormallySmooth.of_equiv e.symm
    let e' : (S ⊗[R] T) ⊗[S] Ω[S⁄R] ≃ₗ[S ⊗[R] T] Ω[S ⊗[R] T⁄T] :=
      KaehlerDifferential.tensorKaehlerEquiv' R T S (S ⊗[R] T)
    have : Module.Flat (S ⊗[R] T) ((S ⊗[R] T) ⊗[S] Ω[S⁄R]) := .of_linearEquiv e'
    have : Module.Flat S (Ω[S⁄R]) := Module.Flat.of_flat_tensorProduct (S ⊗[R] T) _
    exact Module.Flat.projective_of_finitePresentation

end Algebra
