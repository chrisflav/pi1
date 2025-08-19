import Mathlib.RingTheory.TensorProduct.Basic

open TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
noncomputable def Algebra.TensorProduct.comm' {R S T : Type*} [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    S ⊗[R] T ≃ₗ[S] T ⊗[R] S :=
  (_root_.TensorProduct.comm ..).toAddEquiv.toLinearEquiv <| by
    intro c x
    induction x with
    | zero => simp
    | add x y hx hy =>
      simp only [LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply] at hx hy
      simp [hx, hy]
    | tmul s t =>
      simp only [LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply]
      show (_root_.TensorProduct.comm R S T) ((c • s) ⊗ₜ[R] t) = c • t ⊗ₜ[R] s
      simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra]

section

variable (R S A B C : Type*) [CommSemiring R] [Semiring A] [Semiring B]
  [Semiring C] [Algebra R A] [CommSemiring S] [Algebra R S] [Algebra S A]
  [IsScalarTower R S A] [Algebra R B] [Algebra R C]

noncomputable
def Algebra.TensorProduct.assoc' : A ⊗[R] B ⊗[R] C ≃ₐ[S] A ⊗[R] (B ⊗[R] C) where
  toRingEquiv := Algebra.TensorProduct.assoc R R A B C
  commutes' r := by simp [one_def]

@[simp]
lemma Algebra.TensorProduct.assoc'_tmul (a : A) (b : B) (c : C) :
    TensorProduct.assoc' R S A B C (a ⊗ₜ b ⊗ₜ c) = a ⊗ₜ (b ⊗ₜ c) :=
  rfl

@[simp]
lemma Algebra.TensorProduct.assoc'_symm_tmul (a : A) (b : B) (c : C) :
    (TensorProduct.assoc' R S A B C).symm (a ⊗ₜ (b ⊗ₜ c)) = a ⊗ₜ b ⊗ₜ c :=
  rfl

end
