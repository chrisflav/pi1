import Mathlib.RingTheory.IsTensorProduct

open TensorProduct

namespace Algebra

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
  apply IsPushout.of_equiv (commTensorProd R S T)
  ext x
  simp [RingHom.algebraMap_toAlgebra]

instance _root_.TensorProduct.isPushout_rightAlgebra' : IsPushout R S T (T ⊗[R] S) := by
  rw [IsPushout.comm]
  infer_instance

end Algebra
