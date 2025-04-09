import Mathlib.RingTheory.IsTensorProduct

open TensorProduct

namespace Algebra

lemma IsPushout.of_equiv {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    {R' S' : Type*} [CommSemiring R'] [CommSemiring S'] [Algebra R R']
    [Algebra S S'] [Algebra R' S'] [Algebra R S'] [IsScalarTower R R' S']
    [IsScalarTower R S S'] [IsPushout R R' S S']
    (T : Type*) [CommSemiring T] [Algebra R' T] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [IsScalarTower R R' T] (e : S' ≃ₐ[R'] T)
    (he : e.toRingHom.comp (algebraMap S S') = algebraMap S T) :
    IsPushout R R' S T := by
  rw [isPushout_iff]
  have h : IsPushout R R' S S' := inferInstance
  rw [isPushout_iff] at h
  let e1 := h.equiv
  apply IsBaseChange.of_equiv (e1 ≪≫ₗ e.toLinearEquiv)
  intro x
  simpa [e1, h.equiv_tmul] using DFunLike.congr_fun he x

variable (R S T : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

noncomputable def commTensorProd : S ⊗[R] T ≃ₐ[T] T ⊗[R] S :=
  AlgEquiv.ofRingEquiv (f := (TensorProduct.comm R S T).toRingEquiv) <| by
    intro x
    simp [RingHom.algebraMap_toAlgebra]

@[simp]
lemma commTensorProd_tmul (s : S) (t : T) : commTensorProd R S T (s ⊗ₜ[R] t) = t ⊗ₜ s :=
  rfl

@[simp]
lemma commTensorProd_symm_tmul (s : S) (t : T) : (commTensorProd R S T).symm (t ⊗ₜ[R] s) = s ⊗ₜ t :=
  rfl


instance _root_.TensorProduct.isPushout_rightAlgebra : IsPushout R T S (T ⊗[R] S) := by
  apply IsPushout.of_equiv (T ⊗[R] S) (commTensorProd R S T)
  ext x
  simp [RingHom.algebraMap_toAlgebra]

instance _root_.TensorProduct.isPushout_rightAlgebra' : IsPushout R S T (T ⊗[R] S) := by
  rw [IsPushout.comm]
  infer_instance

end Algebra
