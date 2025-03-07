import Mathlib

universe u

open TensorProduct

namespace Algebra

namespace Extension

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (P : Extension.{u, u, u} R S)
variable (T : Type u) [CommRing T] [Algebra R T]

lemma exact_hCotangentι_cotangentComplex :
    Function.Exact h1Cotangentι P.cotangentComplex := by
  sorry

attribute [local instance] Algebra.TensorProduct.rightAlgebra

noncomputable
def toBaseChange : P.Hom (P.baseChange (T := T)) where
  toRingHom := TensorProduct.includeRight.toRingHom
  toRingHom_algebraMap x := by simp [baseChange]
  algebraMap_toRingHom x := rfl

end Extension

end Algebra
