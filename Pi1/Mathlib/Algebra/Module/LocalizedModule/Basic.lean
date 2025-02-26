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

variable {R : Type*} [CommSemiring R] (S : Submonoid R) {M M' M'' : Type*}
  [AddCommMonoid M] [AddCommMonoid M']
  [AddCommMonoid M''] [Module R M] [Module R M'] [Module R M'']
  (f : M →ₗ[R] M') (g : M →ₗ[R] M'') [IsLocalizedModule S f]

@[simp]
lemma IsLocalizedModule.iso_symm_apply'' (x) : (iso S f).symm (f x) = LocalizedModule.mk x 1 := by
  show ((iso S f).symm.toLinearMap.comp f) x = _
  --have := iso_symm_comp S f
  rw [iso_symm_comp]
  simp

@[simp]
lemma IsLocalizedModule.iso_mk_one (x) : (iso S f) (LocalizedModule.mk x 1) = f x := by
  simp
  --show ((iso S f).symm.toLinearMap.comp f) x = _
  ----have := iso_symm_comp S f
  --rw [iso_symm_comp]
  --simp

@[simp]
lemma LocalizedModule.lift_mk_one (h : ∀ (x : S), IsUnit ((algebraMap R (Module.End R M'')) x))
    (m : M) :
    (lift S g h) (mk m 1) = g m := by
  conv_rhs => rw [← LocalizedModule.lift_comp S g h]
  simp

@[simp]
lemma IsLocalizedModule.lift_comp_iso
    (h : ∀ (x : S), IsUnit ((algebraMap R (Module.End R M'')) x)) :
    IsLocalizedModule.lift S f g h ∘ₗ iso S f = LocalizedModule.lift S g h := by
  apply IsLocalizedModule.ext S (LocalizedModule.mkLinearMap S M) h
  ext x
  simp

@[simp]
lemma IsLocalizedModule.lift_iso (h : ∀ (x : S), IsUnit ((algebraMap R (Module.End R M'')) x)) (x) :
    IsLocalizedModule.lift S f g h ((iso S f) x) =
      LocalizedModule.lift _ g h x := by
  rw [← IsLocalizedModule.lift_comp_iso S f]
  dsimp

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
    ext x : 2 <;> simp [e₃, -IsLocalizedModule.iso_apply, IsBaseChange.equiv_tmul]
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
