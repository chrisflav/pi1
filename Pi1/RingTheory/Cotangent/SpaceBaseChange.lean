import Mathlib
import Pi1.RingTheory.Cotangent.Basic
import Pi1.RingTheory.KaehlerBaseChange
import Pi1.Mathlib.RingTheory.IsTensorProduct

suppress_compilation

universe u

open TensorProduct

namespace Algebra

namespace Extension

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (P : Extension.{u, u, u} R S)
variable (T : Type u) [CommRing T] [Algebra R T]

attribute [local instance] SMulCommClass.of_commMonoid
attribute [local instance] KaehlerDifferential.moduleBaseChange'

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance : Algebra P.Ring (T ⊗[R] S) :=
  (algebraMap _ _).comp (algebraMap P.Ring S) |>.toAlgebra

def commTensorProd : S ⊗[R] T ≃ₗ[P.Ring] T ⊗[R] S :=
  (_root_.TensorProduct.comm ..).toAddEquiv.toLinearEquiv <| by
    intro c x
    induction x with
    | zero => simp
    | add x y hx hy =>
        simp only [LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply] at hx hy
        simp [hx, hy]
    | tmul s t =>
        simp only [LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply, comm_tmul]
        show (_root_.TensorProduct.comm R S T) ((c • s) ⊗ₜ[R] t) = c • t ⊗ₜ[R] s
        simp [comm_tmul, Algebra.smul_def, RingHom.algebraMap_toAlgebra]

instance : IsScalarTower P.Ring S (T ⊗[R] S) :=
  IsScalarTower.of_algebraMap_eq' rfl

instance : IsScalarTower R P.Ring (T ⊗[R] S) :=
  IsScalarTower.of_algebraMap_eq <| fun x ↦ by
    simp only [TensorProduct.algebraMap_apply, RingHom.algebraMap_toAlgebra]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      TensorProduct.includeRight_apply]
    rw [← IsScalarTower.algebraMap_apply, ← mul_one (algebraMap R T x), ← smul_eq_mul, ← smul_tmul']
    conv_rhs => rw [← mul_one (algebraMap R S x), ← Algebra.smul_def]
    simp

def myAssoc : T ⊗[R] (S ⊗[P.Ring] Ω[P.Ring⁄R]) ≃ₗ[R] (T ⊗[R] S) ⊗[P.Ring] Ω[P.Ring⁄R] :=
  let e₁ : T ⊗[R] (S ⊗[P.Ring] Ω[P.Ring⁄R]) ≃ₗ[R] (S ⊗[P.Ring] Ω[P.Ring⁄R]) ⊗[R] T :=
    _root_.TensorProduct.comm ..
  let e₂ : (S ⊗[P.Ring] Ω[P.Ring⁄R]) ⊗[R] T ≃ₗ[R] (Ω[P.Ring⁄R] ⊗[P.Ring] S) ⊗[R] T :=
    AlgebraTensorModule.congr
      ((_root_.TensorProduct.comm ..).restrictScalars R) (LinearEquiv.refl R T)
  let e₃ : (Ω[P.Ring⁄R] ⊗[P.Ring] S) ⊗[R] T ≃ₗ[P.Ring] Ω[P.Ring⁄R] ⊗[P.Ring] (S ⊗[R] T) :=
    AlgebraTensorModule.assoc ..
  let e₄ : Ω[P.Ring⁄R] ⊗[P.Ring] (S ⊗[R] T) ≃ₗ[R] (S ⊗[R] T) ⊗[P.Ring] Ω[P.Ring⁄R] :=
    (_root_.TensorProduct.comm ..).restrictScalars R
  let eaux : S ⊗[R] T ≃ₗ[P.Ring] T ⊗[R] S := commTensorProd ..
  let e₅ : (S ⊗[R] T) ⊗[P.Ring] Ω[P.Ring⁄R] ≃ₗ[P.Ring] (T ⊗[R] S) ⊗[P.Ring] Ω[P.Ring⁄R] :=
    AlgebraTensorModule.congr eaux (LinearEquiv.refl _ _)
  e₁ ≪≫ₗ e₂ ≪≫ₗ e₃.restrictScalars R ≪≫ₗ e₄ ≪≫ₗ e₅.restrictScalars R

lemma myAssoc_tmul (t : T) (s : S) (x : Ω[P.Ring⁄R]) :
    P.myAssoc T (t ⊗ₜ (s ⊗ₜ x)) = (t ⊗ₜ s) ⊗ₜ x :=
  rfl

def myAssocE : T ⊗[R] (S ⊗[P.Ring] Ω[P.Ring⁄R]) ≃ₗ[T] (T ⊗[R] S) ⊗[P.Ring] Ω[P.Ring⁄R] :=
  (myAssoc ..).toAddEquiv.toLinearEquiv <| fun c x ↦ by
    induction x with
    | zero => rw [smul_zero, AddEquiv.map_zero, smul_zero]
    | add x y hx hy =>
    dsimp only [LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply] at hx hy ⊢
    rw [smul_add, LinearEquiv.map_add, LinearEquiv.map_add, hx, hy, smul_add]
    | tmul t x =>
    induction x with
    | zero => rw [tmul_zero, smul_zero, AddEquiv.map_zero, smul_zero]
    | add x y hx hy =>
    dsimp only [LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply] at hx hy ⊢
    rw [tmul_add, smul_add, LinearEquiv.map_add, hx, hy, LinearEquiv.map_add, smul_add]
    | tmul s x =>
    dsimp only [LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply]
    have : c • t ⊗ₜ[R] (s ⊗ₜ[P.Ring] x) = (c • t) ⊗ₜ[R] (s ⊗ₜ[P.Ring] x) := rfl
    rw [this, myAssoc_tmul, myAssoc_tmul]
    rfl

@[simp]
lemma myAssocE_tmul (t : T) (s : S) (x : Ω[P.Ring⁄R]) :
    P.myAssocE T (t ⊗ₜ (s ⊗ₜ x)) = (t ⊗ₜ s) ⊗ₜ x :=
  rfl

set_option maxHeartbeats 0 in
noncomputable
def tensorCotangentSpace' :
    T ⊗[R] P.CotangentSpace ≃ₗ[T] (P.baseChange (T := T)).CotangentSpace := by
  let PT : Extension T (T ⊗[R] S) := P.baseChange
  let _ : Algebra P.Ring PT.Ring :=
    inferInstanceAs <| Algebra P.Ring (T ⊗[R] P.Ring)
  have : IsScalarTower R P.Ring PT.Ring :=
    IsScalarTower.of_algebraMap_eq <| fun x ↦ by
      simp only [baseChange, RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        AlgHom.commutes, TensorProduct.algebraMap_apply, PT]
      rfl
  have : IsPushout R T P.Ring PT.Ring := by
    rw [IsPushout.comm]
    dsimp [PT, baseChange]
    convert _root_.TensorProduct.isPushout_rightAlgebra' R P.Ring T
    ext x (y : T ⊗[R] P.Ring)
    rw [Algebra.smul_def]
    simp only [TensorProduct.algebraMap_apply]
    rw [Algebra.compHom_smul_def]
    rw [Algebra.smul_def]
    simp
  have : IsScalarTower P.Ring PT.Ring (T ⊗[R] S) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower T PT.Ring (T ⊗[R] S) :=
    IsScalarTower.of_algebraMap_eq <| fun x ↦ by
      simp [PT, baseChange, RingHom.algebraMap_toAlgebra]
  let e : PT.Ring ⊗[P.Ring] Ω[P.Ring⁄R] ≃ₗ[PT.Ring] Ω[PT.Ring⁄T] :=
    KaehlerDifferential.tensorKaehlerEquiv' _ _ _ _
  dsimp only [CotangentSpace]
  let e' :
      (T ⊗[R] S) ⊗[PT.Ring] (PT.Ring ⊗[P.Ring] Ω[P.Ring⁄R]) ≃ₗ[PT.Ring]
      (T ⊗[R] S) ⊗[PT.Ring] Ω[PT.Ring⁄T] :=
    AlgebraTensorModule.congr (LinearEquiv.refl _ _) e
  let e₂ : T ⊗[R] (S ⊗[P.Ring] Ω[P.Ring⁄R]) ≃ₗ[T] (T ⊗[R] S) ⊗[P.Ring] Ω[P.Ring⁄R] :=
    myAssocE ..
  let e₃ : (T ⊗[R] S) ⊗[P.Ring] Ω[P.Ring⁄R] ≃ₗ[T]
      (T ⊗[R] S) ⊗[PT.Ring] (PT.Ring ⊗[P.Ring] Ω[P.Ring⁄R]) :=
    (AlgebraTensorModule.cancelBaseChange _ PT.Ring PT.Ring _ _).symm.restrictScalars T
  let e'' : T ⊗[R] (S ⊗[P.Ring] Ω[P.Ring⁄R]) ≃ₗ[T]
      (T ⊗[R] S) ⊗[PT.Ring] (PT.Ring ⊗[P.Ring] Ω[P.Ring⁄R]) :=
    e₂ ≪≫ₗ e₃
  exact e'' ≪≫ₗ e'.restrictScalars T

noncomputable local instance : Algebra P.Ring (P.baseChange (T := T)).Ring :=
  TensorProduct.includeRight.toRingHom.toAlgebra

set_option maxHeartbeats 0 in
@[simp]
lemma tensorCotangentSpace'_tmul (t : T) (x : P.CotangentSpace) :
    P.tensorCotangentSpace' T (t ⊗ₜ x) = t • CotangentSpace.map (P.toBaseChange T) x := by
  dsimp only [CotangentSpace] at x
  induction (x : S ⊗[P.Ring] Ω[P.Ring⁄R]) with
  | zero => rw [tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero, smul_zero]
  | add x y hx hy => rw [tmul_add, LinearEquiv.map_add, LinearMap.map_add, smul_add, hx, hy]
  | tmul s y =>
  simp [tensorCotangentSpace']
  have : y ∈ Submodule.span P.Ring (Set.range (KaehlerDifferential.D R P.Ring)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction this using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨y, rfl⟩ := hy
    rw [CotangentSpace.map_tmul, KaehlerDifferential.tensorKaehlerEquiv'_tmul]
    rw [one_smul, smul_tmul', Algebra.smul_def, RingHom.algebraMap_toAlgebra,
      RingHom.algebraMap_toAlgebra]
    simp
    rfl
  | smul a x _ hx =>
    have h1 : a • (1 : (P.baseChange (T := T)).Ring) ⊗ₜ[P.Ring] x =
        algebraMap P.Ring (P.baseChange (T := T)).Ring a • 1 ⊗ₜ x :=
      rfl
    have h2 : a • s ⊗ₜ[P.Ring] x = algebraMap P.Ring S a • s ⊗ₜ x := by
      rw [smul_tmul', Algebra.smul_def, ← smul_eq_mul, smul_tmul']
    rw [tmul_smul, tmul_smul, h1, LinearEquiv.map_smul, tmul_smul, hx, h2, LinearMap.map_smul,
      smul_comm]
    rfl
  | add x y _ _ hx hy =>
    rw [tmul_add, LinearEquiv.map_add, tmul_add, tmul_add, LinearMap.map_add, smul_add, hx, hy]
  | zero =>
    rw [tmul_zero, tmul_zero, LinearEquiv.map_zero, tmul_zero, LinearMap.map_zero, smul_zero]

end Extension

end Algebra
