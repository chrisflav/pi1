import Mathlib.RingTheory.TensorProduct.Basic

open TensorProduct

lemma Algebra.TensorProduct.tmul_comm {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (r : R) :
    algebraMap R S r ⊗ₜ[R] 1 = 1 ⊗ₜ algebraMap R T r := by
  rw [algebraMap_eq_smul_one, algebraMap_eq_smul_one, smul_tmul]

lemma Algebra.TensorProduct.map_mul_of_map_mul_tmul {R S A B C : Type*} [CommRing R]
    [CommRing S] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R S] [Algebra R A] [Algebra R B]
    [Algebra S A] [IsScalarTower R S A] [Algebra S C]
    {f : A ⊗[R] B →ₗ[S] C}
    (hf : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f (a₁ ⊗ₜ b₁ * a₂ ⊗ₜ b₂) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
    (x y : A ⊗[R] B) :
    f (x * y) = f x * f y := by
  induction x with
  | zero => simp
  | add a b ha hb => simp [ha, hb, add_mul]
  | tmul a b =>
      induction y with
      | zero => simp
      | add c d hc hd => simp [hc, hd, mul_add]
      | tmul => apply hf

noncomputable
def Algebra.TensorProduct.cancelBaseChange (R S T A B : Type*)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R T] [Algebra R A] [Algebra R B]
    [Algebra T A] [IsScalarTower R T A] [Algebra S A]
    [IsScalarTower R S A] [Algebra S T] [IsScalarTower S T A] :
    A ⊗[S] (S ⊗[R] B) ≃ₐ[T] A ⊗[R] B :=
  AlgEquiv.symm <| AlgEquiv.ofLinearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T A B).symm
    (by simp [Algebra.TensorProduct.one_def]) <|
      map_mul_of_map_mul_tmul (fun _ _ _ _ ↦ by simp)

@[simp]
lemma Algebra.TensorProduct.cancelBaseChange_tmul (R S T A B : Type*)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R T] [Algebra R A] [Algebra R B]
    [Algebra T A] [IsScalarTower R T A] [Algebra S A]
    [IsScalarTower R S A] [Algebra S T] [IsScalarTower S T A]
    (a : A) (s : S) (b : B) :
    Algebra.TensorProduct.cancelBaseChange R S T A B (a ⊗ₜ (s ⊗ₜ b)) = (s • a) ⊗ₜ b :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul R S T a b s

@[simp]
lemma Algebra.TensorProduct.cancelBaseChange_symm_tmul (R S T A B : Type*)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R T] [Algebra R A] [Algebra R B]
    [Algebra T A] [IsScalarTower R T A] [Algebra S A]
    [IsScalarTower R S A] [Algebra S T] [IsScalarTower S T A]
    (a : A) (b : B) :
    (Algebra.TensorProduct.cancelBaseChange R S T A B).symm (a ⊗ₜ b) = a ⊗ₜ (1 ⊗ₜ b) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul R S T a b
