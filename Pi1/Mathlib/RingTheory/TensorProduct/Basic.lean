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
