import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Prod

open TensorProduct

-- #24380
noncomputable
nonrec def Algebra.TensorProduct.prodRight (R S T A B : Type*) [CommRing R] [CommRing A]
    [CommRing B] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [Algebra R A] [Algebra R B] :
    T ⊗[R] (A × B) ≃ₐ[S] T ⊗[R] A × T ⊗[R] B :=
  .ofLinearEquiv (TensorProduct.prodRight R S T A B) (by simp [Algebra.TensorProduct.one_def])
    (LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ ↦ by simp))

