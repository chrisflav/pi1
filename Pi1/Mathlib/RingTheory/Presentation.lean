import Mathlib.RingTheory.Extension.Presentation.Basic

noncomputable section

universe t₁ t₂

open TensorProduct MvPolynomial

variable {R : Type*} [CommRing R]

namespace Algebra

lemma aeval_mk_X_eq_mk {σ : Type*} (I : Ideal (MvPolynomial σ R)) :
    aeval (fun i ↦ Ideal.Quotient.mk I (X i)) = Ideal.Quotient.mkₐ _ I := by
  rw [aeval_unique (Ideal.Quotient.mkₐ _ I)]
  rfl

end Algebra
