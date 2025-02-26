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

section
-- #22328

variable {R : Type*} [CommSemiring R] (S : Submonoid R)

/-- The localization of an `R`-module `M` at a submonoid `S` is isomorphic to `S⁻¹R ⊗[R] M` as
an `S⁻¹R`-module. -/
noncomputable def LocalizedModule.equivTensorProduct (M : Type*) [AddCommMonoid M] [Module R M] :
    LocalizedModule S M ≃ₗ[Localization S] Localization S ⊗[R] M :=
  IsLocalizedModule.isBaseChange S (Localization S)
    (LocalizedModule.mkLinearMap S M) |>.equiv.symm

@[simp]
lemma LocalizedModule.equivTensorProduct_symm_apply_tmul
    (M : Type*) [AddCommMonoid M] [Module R M] (x : M) (r : R)(s : S) :
    (equivTensorProduct S M).symm (Localization.mk r s ⊗ₜ[R] x) = r • mk x s := by
  simp [equivTensorProduct, IsBaseChange.equiv_tmul, mk_smul_mk, smul'_mk]

@[simp]
lemma LocalizedModule.equivTensorProduct_symm_apply_tmul_one
    (M : Type*) [AddCommMonoid M] [Module R M] (x : M) :
    (equivTensorProduct S M).symm (1 ⊗ₜ[R] x) = mk x 1 := by
  simp [← Localization.mk_one]

@[simp]
lemma LocalizedModule.equivTensorProduct_apply_mk
    (M : Type*) [AddCommMonoid M] [Module R M] (x : M) (s : S) :
    equivTensorProduct S M (mk x s) = Localization.mk 1 s ⊗ₜ[R] x := by
  apply (equivTensorProduct S M).symm.injective
  simp

end

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

section
-- #22336

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

@[simps!]
noncomputable def IsLocalizedModule.mapEquiv {R : Type*} [CommSemiring R] (S : Submonoid R)
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

end
