import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Prod

open TensorProduct

section
-- #22339

section

variable {R A M M' : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (S : Submonoid R)
  [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  [IsLocalization S A]

noncomputable
def IsLocalizedModule.module (f : M →ₗ[R] M') [IsLocalizedModule S f] : Module A M' :=
  (IsLocalizedModule.iso S f).symm.toAddEquiv.module A

instance IsLocalizedModule.module_isScalarTower (f : M →ₗ[R] M') [IsLocalizedModule S f] :
    letI : Module A M' := IsLocalizedModule.module S f
    IsScalarTower R A M' :=
  (IsLocalizedModule.iso S f).symm.isScalarTower A

end

lemma IsBaseChange.pi {R S ι : Type*} [Finite ι] [CommSemiring R] [CommSemiring S]
    [Algebra R S]
    {M M' : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (M' i)]
    [∀ i, Module R (M i)] [∀ i, Module R (M' i)] [∀ i, Module S (M' i)]
    [∀ i, IsScalarTower R S (M' i)]
    (f : ∀ i, M i →ₗ[R] M' i) (hf : ∀ i, IsBaseChange S (f i)) :
    IsBaseChange S (.pi fun i ↦ f i ∘ₗ .proj i) := by
  classical
  cases nonempty_fintype ι
  apply IsBaseChange.of_equiv <| TensorProduct.piRight R S _ M ≪≫ₗ
    .piCongrRight fun i ↦ (hf i).equiv
  intro x
  ext i
  simp [IsBaseChange.equiv_tmul]

instance IsLocalizedModule.pi {R ι : Type*} [Finite ι] [CommSemiring R] (S : Submonoid R)
    {M M' : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (M' i)]
    [∀ i, Module R (M i)] [∀ i, Module R (M' i)]
    (f : ∀ i, M i →ₗ[R] M' i) [∀ i, IsLocalizedModule S (f i)] :
    IsLocalizedModule S (.pi fun i ↦ f i ∘ₗ .proj i) := by
  letI (i : ι) : Module (Localization S) (M' i) := IsLocalizedModule.module S (f i)
  rw [isLocalizedModule_iff_isBaseChange S (Localization S)]
  apply IsBaseChange.pi
  intro i
  rw [← isLocalizedModule_iff_isBaseChange S]
  infer_instance

lemma IsBaseChange.prodMap {R S M N M' N' : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [AddCommMonoid M'] [AddCommMonoid N'] [Module R M'] [Module R N']
    [Module S M'] [Module S N'] [IsScalarTower R S M'] [IsScalarTower R S N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    (hf : IsBaseChange S f) (hg : IsBaseChange S g) :
    IsBaseChange S (f.prodMap g) := by
  apply IsBaseChange.of_equiv (TensorProduct.prodRight R _ S M N ≪≫ₗ hf.equiv.prod hg.equiv)
  intro p
  simp [hf.equiv_tmul, hg.equiv_tmul]

instance IsLocalizedModule.prodMap {R M N M' N' : Type*} [CommSemiring R] (S : Submonoid R)
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [AddCommMonoid M'] [AddCommMonoid N'] [Module R M'] [Module R N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    [IsLocalizedModule S f] [IsLocalizedModule S g] :
    IsLocalizedModule S (f.prodMap g) := by
  letI : Module (Localization S) M' := IsLocalizedModule.module S f
  letI : Module (Localization S) N' := IsLocalizedModule.module S g
  rw [isLocalizedModule_iff_isBaseChange S (Localization S)]
  apply IsBaseChange.prodMap
  · rw [← isLocalizedModule_iff_isBaseChange S]
    infer_instance
  · rw [← isLocalizedModule_iff_isBaseChange S]
    infer_instance

end
