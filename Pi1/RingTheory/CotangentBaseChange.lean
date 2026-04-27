import Mathlib
import Pi1.RingTheory.KaehlerBaseChange
import Pi1.RingTheory.FiveLemma
import Pi1.Mathlib.RingTheory.TensorProduct.Basic

noncomputable section

universe u

open TensorProduct

namespace TensorProduct.AlgebraTensorModule

variable {R : Type*} (A B : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable {N : Type*} [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]

end TensorProduct.AlgebraTensorModule

namespace Algebra.TensorProduct

variable {R : Type*} (S T A : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T]
  [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

lemma map_includeRight_eq (I : Ideal T) :
    (I.map (includeRight (A := A) (R := R))).restrictScalars S =
      LinearMap.range ((AlgebraTensorModule.lTensor S A) (I.subtype.restrictScalars R)) := by
  have := I.map_includeRight_eq (R := R) (A := A)
  rwa [Submodule.ext_iff] at this ⊢

end Algebra.TensorProduct
