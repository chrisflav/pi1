import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Prod

open TensorProduct

section

lemma Module.FinitePresentation.of_equiv {R M N : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) [Module.FinitePresentation R M] :
    Module.FinitePresentation R N := by
  simp [← Module.FinitePresentation.fg_ker_iff e.toLinearMap e.surjective, Submodule.fg_bot]

end

instance {R : Type*} [CommRing R] (S : Submonoid R) (M : Type*) [AddCommMonoid M] [Module R M]
    [Subsingleton M] : Subsingleton (LocalizedModule S M) := by
  rw [LocalizedModule.subsingleton_iff]
  intro m
  use 1, S.one_mem, Subsingleton.elim _ _

instance IsLocalizedModule.pi {R ι : Type*} [Finite ι] [CommSemiring R] (S : Submonoid R)
    {M M' : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (M' i)]
    [∀ i, Module R (M i)] [∀ i, Module R (M' i)]
    (f : ∀ i, M i →ₗ[R] M' i) [∀ i, IsLocalizedModule S (f i)] :
    IsLocalizedModule S (LinearMap.pi fun i ↦ f i ∘ₗ LinearMap.proj i) := by
  classical
  cases nonempty_fintype ι
  let e₃ : Localization S ⊗[R] (Π i, M i) ≃ₗ[R] Π i, M' i :=
    TensorProduct.piRight R R _ M ≪≫ₗ LinearEquiv.piCongrRight
      (fun i ↦ (isBaseChange S (Localization S)
        (LocalizedModule.mkLinearMap S _)).equiv.restrictScalars R ≪≫ₗ iso S (f i))
  have : ((LinearMap.pi fun i ↦ f i ∘ₗ LinearMap.proj i)) =
      e₃ ∘ₗ (TensorProduct.mk R (Localization S) (Π i, M i) 1) := by
    ext x
    simp [e₃, IsBaseChange.equiv_tmul]
  rw [this]
  infer_instance

instance IsLocalizedModule.prodMap {R M N M' N' : Type*} [CommSemiring R] (S : Submonoid R)
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [AddCommMonoid M'] [AddCommMonoid N'] [Module R M'] [Module R N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    [IsLocalizedModule S f] [IsLocalizedModule S g] :
    IsLocalizedModule S (f.prodMap g) := by
  let e₃ : Localization S ⊗[R] (M × N) ≃ₗ[R] M' × N' :=
    TensorProduct.prodRight R _ (Localization S) M N ≪≫ₗ
        ((isBaseChange S (Localization S)
            (LocalizedModule.mkLinearMap S M)).equiv.restrictScalars R ≪≫ₗ iso S f).prod
        ((isBaseChange S (Localization S)
            (LocalizedModule.mkLinearMap S N)).equiv.restrictScalars R ≪≫ₗ iso S g)
  have : (f.prodMap g) = e₃ ∘ₗ (TensorProduct.mk R (Localization S) (M × N) 1) := by
    ext x : 2 <;> simp [e₃, IsBaseChange.equiv_tmul]
  rw [this]
  infer_instance

@[simps!]
def LinearEquiv.extendScalarsOfIsLocalization
    {R : Type*} [CommSemiring R] (S : Submonoid R) (A : Type*)
    [CommSemiring A] [Algebra R A] [IsLocalization S A] {M N : Type*} [AddCommMonoid M] [Module R M]
    [Module A M] [IsScalarTower R A M] [AddCommMonoid N] [Module R N] [Module A N]
    [IsScalarTower R A N] (f : M ≃ₗ[R] N) :
    M ≃ₗ[A] N :=
  .ofLinear (LinearMap.extendScalarsOfIsLocalization S A f)
    (LinearMap.extendScalarsOfIsLocalization S A f.symm)
    (by ext; simp) (by ext; simp)

@[simps]
def LinearEquiv.extendScalarsOfIsLocalizationEquiv
    {R : Type*} [CommSemiring R] (S : Submonoid R) (A : Type*)
    [CommSemiring A] [Algebra R A] [IsLocalization S A] {M N : Type*} [AddCommMonoid M] [Module R M]
    [Module A M] [IsScalarTower R A M] [AddCommMonoid N] [Module R N] [Module A N]
    [IsScalarTower R A N] :
    (M ≃ₗ[R] N) ≃ M ≃ₗ[A] N where
  toFun e := e.extendScalarsOfIsLocalization S A
  invFun e := e.restrictScalars R
  left_inv e := by ext; simp
  right_inv e := by ext; simp

/-- -/
noncomputable
def IsLocalizedModule.mapEquiv {R : Type*} [CommSemiring R] (S : Submonoid R)
    (A : Type*) {M N M' N' : Type*} [CommSemiring A] [Algebra R A] [IsLocalization S A]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid M'] [AddCommMonoid N']
    [Module R M] [Module R N] [Module R M'] [Module R N']
    [Module A M'] [Module A N'] [IsScalarTower R A M'] [IsScalarTower R A N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N') [IsLocalizedModule S f] [IsLocalizedModule S g]
    (e : M ≃ₗ[R] N) :
    M' ≃ₗ[A] N' :=
  LinearEquiv.ofLinear
    (IsLocalizedModule.mapExtendScalars S f g A e)
    (IsLocalizedModule.mapExtendScalars S g f A e.symm)
    (by
      apply LinearMap.restrictScalars_injective R
      apply IsLocalizedModule.linearMap_ext S g g
      ext
      simp)
    (by
      apply LinearMap.restrictScalars_injective R
      apply IsLocalizedModule.linearMap_ext S f f
      ext
      simp)


/-- The localization of an `R`-module `M` at a submonoid `S` is isomorphic to `S⁻¹R ⊗[R] M` as
an `S⁻¹R`-module. -/
noncomputable def LocalizedModule.equivTensorProduct {R : Type*} [CommSemiring R] (S : Submonoid R)
    (M : Type*) [AddCommMonoid M] [Module R M] :
    LocalizedModule S M ≃ₗ[Localization S] Localization S ⊗[R] M :=
  IsLocalizedModule.isBaseChange S (Localization S)
    (LocalizedModule.mkLinearMap S M) |>.equiv.symm

@[simp]
lemma LocalizedModule.equivTensorProduct_symm_apply_tmul {R : Type*} [CommSemiring R] (S : Submonoid R)
    (M : Type*) [AddCommMonoid M] [Module R M] (x : M) (r : R)(s : S) :
    (equivTensorProduct S M).symm (Localization.mk r s ⊗ₜ[R] x) = r • mk x s := by
  simp [equivTensorProduct, IsBaseChange.equiv_tmul, mk_smul_mk, smul'_mk]

@[simp]
lemma LocalizedModule.equivTensorProduct_symm_apply_tmul_one {R : Type*} [CommSemiring R] (S : Submonoid R)
    (M : Type*) [AddCommMonoid M] [Module R M] (x : M) :
    (equivTensorProduct S M).symm (1 ⊗ₜ[R] x) = mk x 1 := by
  simp [← Localization.mk_one]

@[simp]
lemma LocalizedModule.equivTensorProduct_apply_mk {R : Type*} [CommSemiring R] (S : Submonoid R)
    (M : Type*) [AddCommMonoid M] [Module R M] (x : M) (s : S) :
    equivTensorProduct S M (mk x s) = Localization.mk 1 s ⊗ₜ[R] x := by
  apply (equivTensorProduct S M).symm.injective
  simp
