import Mathlib.RingTheory.LocalProperties.Exactness

open Ideal

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
variable
  (Rₚ : ∀ (p : Ideal R) [p.IsMaximal], Type*)
  [∀ (p : Ideal R) [p.IsMaximal], CommSemiring (Rₚ p)]
  [∀ (p : Ideal R) [p.IsMaximal], Algebra R (Rₚ p)]
  (Sₚ : ∀ (p : Ideal R) [p.IsMaximal], Type*)
  [∀ (p : Ideal R) [p.IsMaximal], CommSemiring (Sₚ p)]
  [∀ (p : Ideal R) [p.IsMaximal], Algebra S (Sₚ p)]
  [∀ (p : Ideal R) [p.IsMaximal], Algebra (Rₚ p) (Sₚ p)]
  [∀ (p : Ideal R) [p.IsMaximal], Algebra R (Sₚ p)]
  [∀ (p : Ideal R) [p.IsMaximal], IsScalarTower R (Rₚ p) (Sₚ p)]
  [∀ (p : Ideal R) [p.IsMaximal], IsScalarTower R S (Sₚ p)]
  [∀ (p : Ideal R) [p.IsMaximal], IsLocalization.AtPrime (Rₚ p) p]
  [∀ (p : Ideal R) [p.IsMaximal],
    IsLocalizedModule.AtPrime p (IsScalarTower.toAlgHom R S (Sₚ p) : S →ₗ[R] (Sₚ p))]

open TensorProduct

lemma IsLocalizedModule.map_linearMap_of_isLocalization (Rₚ Sₚ : Type*) [CommSemiring Rₚ]
    [Algebra R Rₚ] [CommSemiring Sₚ] [Algebra S Sₚ] [Algebra R Sₚ] [IsScalarTower R S Sₚ]
    [Algebra Rₚ Sₚ] [IsScalarTower R Rₚ Sₚ] (p : Ideal R) [p.IsPrime]
    [IsLocalization.AtPrime Rₚ p]
    [IsLocalizedModule.AtPrime p (IsScalarTower.toAlgHom R S Sₚ : S →ₗ[R] Sₚ)] :
    IsLocalizedModule.map p.primeCompl (Algebra.linearMap R Rₚ)
        (IsScalarTower.toAlgHom R S Sₚ : S →ₗ[R] Sₚ) (Algebra.linearMap R S) =
    (Algebra.linearMap Rₚ Sₚ).restrictScalars R := by
  apply IsLocalizedModule.linearMap_ext p.primeCompl (Algebra.linearMap _ _)
    (IsScalarTower.toAlgHom R S Sₚ : S →ₗ[R] Sₚ)
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply, map_one,
    LinearMap.coe_restrictScalars]
  rw [show 1 = Algebra.linearMap R Rₚ 1 by simp, IsLocalizedModule.map_apply]
  simp

lemma injective_of_isLocalization_isMaximal
    (H : ∀ (p : Ideal R) [p.IsMaximal], Function.Injective (algebraMap (Rₚ p) (Sₚ p))) :
    Function.Injective (algebraMap R S) := by
  apply injective_of_isLocalized_maximal (fun P _ ↦ Rₚ P) (fun P _ ↦ Algebra.linearMap _ _)
    (fun P _ ↦ Sₚ P) (fun P _ ↦ IsScalarTower.toAlgHom R S (Sₚ P)) (Algebra.linearMap R S) _
  intro p hp
  convert_to Function.Injective ((Algebra.linearMap (Rₚ p) (Sₚ p)).restrictScalars R)
  · rw [DFunLike.coe_fn_eq]
    apply IsLocalizedModule.map_linearMap_of_isLocalization
  · exact H p

lemma surjective_of_isLocalization_isMaximal
    (H : ∀ (p : Ideal R) [p.IsMaximal], Function.Surjective (algebraMap (Rₚ p) (Sₚ p))) :
    Function.Surjective (algebraMap R S) := by
  apply surjective_of_isLocalized_maximal (fun P _ ↦ Rₚ P) (fun P _ ↦ Algebra.linearMap _ _)
    (fun P _ ↦ Sₚ P) (fun P _ ↦ IsScalarTower.toAlgHom R S (Sₚ P)) (Algebra.linearMap R S) _
  intro p hp
  convert_to Function.Surjective ((Algebra.linearMap (Rₚ p) (Sₚ p)).restrictScalars R)
  · rw [DFunLike.coe_fn_eq]
    apply IsLocalizedModule.map_linearMap_of_isLocalization
  · exact H p

lemma bijective_of_isLocalization_isMaximal
    (H : ∀ (p : Ideal R) [p.IsMaximal], Function.Bijective (algebraMap (Rₚ p) (Sₚ p))) :
    Function.Bijective (algebraMap R S) :=
  ⟨injective_of_isLocalization_isMaximal _ _ (fun p _ ↦ (H p).1),
    surjective_of_isLocalization_isMaximal _ _ (fun p _ ↦ (H p).2)⟩
