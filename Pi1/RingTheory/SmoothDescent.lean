import Mathlib

universe u

open TensorProduct

namespace Module

variable {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable (M : Type*) [AddCommGroup M] [Module R M]

/-- Flat descends along faithfully flat ring maps. -/
lemma Flat.of_flat_tensorProduct [Module.FaithfullyFlat R S] [Module.Flat S (S ⊗[R] M)] :
    Module.Flat R M :=
  sorry

instance [Module.FaithfullyFlat R M] : Module.FaithfullyFlat S (S ⊗[R] M) := sorry

end Module

namespace Algebra

section

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- Flat base change commutes with `H1Cotangent`. -/
def tensorH1CotangentOfFlat (T : Type*) [CommRing T] [Algebra R T] [Module.Flat R T] :
    T ⊗[R] H1Cotangent R S ≃ₗ[T] H1Cotangent T (T ⊗[R] S) :=
  sorry

end

section

variable (R S A B : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [IsPushout R S A B]

section

variable (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- (Implementation) If `B = S ⊗[R] A`, this is the canonical `R`-isomorphism:
`B ⊗[A] M ≃ₗ[S] S ⊗[R] M`. See `IsPushout.cancelBaseChange` for the `S`-linear version. -/
noncomputable
def IsPushout.cancelBaseChange_aux : B ⊗[A] M ≃ₗ[R] S ⊗[R] M :=
  have : IsPushout R A S B := IsPushout.symm inferInstance
  (AlgebraTensorModule.congr ((IsPushout.equiv R A S B).toLinearEquiv).symm
      (LinearEquiv.refl _ _)).restrictScalars R ≪≫ₗ
    (_root_.TensorProduct.comm _ _ _).restrictScalars R ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange _ _ A _ _).restrictScalars R ≪≫ₗ
    (_root_.TensorProduct.comm _ _ _).restrictScalars R

@[simp]
lemma IsPushout.cancelBaseChange_aux_symm_tmul (s : S) (m : M) :
    (IsPushout.cancelBaseChange_aux R S A B M).symm (s ⊗ₜ m) = algebraMap S B s ⊗ₜ m := by
  simp [IsPushout.cancelBaseChange_aux, IsPushout.equiv_tmul]

/-- If `B = S ⊗[R] A`, this is the canonical `S`-isomorphism: `B ⊗[A] M ≃ₗ[S] S ⊗[R] M`.
This is the cancelling on the left version of
`TensorProduct.AlgebraTensorModule.cancelBaseChange`. -/
noncomputable
def IsPushout.cancelBaseChange [SMulCommClass A S B] : B ⊗[A] M ≃ₗ[S] S ⊗[R] M :=
  LinearEquiv.symm <|
  AddEquiv.toLinearEquiv (IsPushout.cancelBaseChange_aux R S A B M).symm <| by
    intro s x
    induction x with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul s' m => simp [Algebra.smul_def, TensorProduct.smul_tmul']

@[simp]
lemma IsPushout.cancelBaseChange_symm_tmul [SMulCommClass A S B] (s : S) (m : M) :
    (IsPushout.cancelBaseChange R S A B M).symm (s ⊗ₜ m) = algebraMap S B s ⊗ₜ m :=
  IsPushout.cancelBaseChange_aux_symm_tmul R S A B M s m

end

attribute [local instance] KaehlerDifferential.moduleBaseChange
attribute [local instance] KaehlerDifferential.moduleBaseChange'

/-- If `S ⊗[R] Ω[A⁄R]` is equipped with its canonical `B`-module structure
from `KaehlerDifferential.moduleBaseChange'`, it is `B`-isomorphic to `B ⊗[A] Ω[A⁄R]`. -/
noncomputable
def _root_.KaehlerDifferential.tensorKaehlerCancelBase : B ⊗[A] Ω[A⁄R] ≃ₗ[B] S ⊗[R] Ω[A⁄R] :=
  LinearEquiv.symm <|
  have : SMulCommClass A S B := SMulCommClass.of_commMonoid A S B
  let f : B ⊗[A] Ω[A⁄R] ≃ₗ[S] S ⊗[R] Ω[A⁄R] :=
    IsPushout.cancelBaseChange _ _ _ _ _
  have h : IsPushout R S A B := inferInstance
  AddEquiv.toLinearEquiv f.symm <| by
    intro b x
    dsimp
    induction b using h.1.inductionOn with
    | h₁ => rw [zero_smul, LinearEquiv.map_zero, zero_smul]
    | h₂ a =>
      simp only [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom', algebraMap_smul]
      induction x with
      | zero => rw [smul_zero, LinearEquiv.map_zero, smul_zero]
      | add x y hx hy => rw [smul_add, LinearEquiv.map_add, hx, hy, LinearEquiv.map_add, smul_add]
      | tmul s x =>
      show f.symm (s ⊗ₜ[R] (a • x)) = a • f.symm (s ⊗ₜ[R] x)
      simp only [f, IsPushout.cancelBaseChange_symm_tmul, tmul_smul]
    | h₃ s b h => rw [smul_assoc, map_smul, h, smul_assoc]
    | h₄ b₁ b₂ h1 h2 => rw [add_smul, add_smul, map_add, h1, h2]

/-- A `B`-linear version of `KaehlerDifferential.tensorKaehlerEquiv` depending on
`KaehlerDifferential.moduleBaseChange'`. -/
noncomputable
def _root_.KaehlerDifferential.tensorKaehlerEquivExtend : S ⊗[R] Ω[A⁄R] ≃ₗ[B] Ω[B⁄S] :=
  LinearEquiv.symm <| (KaehlerDifferential.tensorKaehlerEquiv R S A B).symm.toLinearEquiv <|
    (KaehlerDifferential.derivationTensorProduct R S A B).liftKaehlerDifferential.map_smul

/-- A `B`-linear version of `KaehlerDifferential.tensorKaehlerEquiv`. -/
noncomputable
def _root_.KaehlerDifferential.tensorKaehlerEquiv' : B ⊗[A] Ω[A⁄R] ≃ₗ[B] Ω[B⁄S] :=
  KaehlerDifferential.tensorKaehlerCancelBase R S A B ≪≫ₗ
    KaehlerDifferential.tensorKaehlerEquivExtend R S A B

end

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

lemma FormallySmooth.of_formallySmooth_tensorProduct
    [Algebra.FinitePresentation R S]
    (T : Type u) [CommRing T] [Algebra R T]
    [FormallySmooth T (T ⊗[R] S)] [Module.FaithfullyFlat R T] :
    FormallySmooth R S := by
  rw [FormallySmooth.iff_subsingleton_and_projective]
  constructor
  · have : Subsingleton (T ⊗[R] H1Cotangent R S) := (tensorH1CotangentOfFlat R S T).subsingleton
    exact Module.FaithfullyFlat.lTensor_reflects_triviality R T (H1Cotangent R S)
  · let _ : Algebra T (S ⊗[R] T) := TensorProduct.includeRight.toRingHom.toAlgebra
    let e : S ⊗[R] T ≃ₐ[T] T ⊗[R] S :=
      AlgEquiv.ofRingEquiv (f := TensorProduct.comm R S T) <| by simp [RingHom.algebraMap_toAlgebra]
    have : FormallySmooth T (S ⊗[R] T) := FormallySmooth.of_equiv e.symm
    let e' : (S ⊗[R] T) ⊗[S] Ω[S⁄R] ≃ₗ[S ⊗[R] T] Ω[S ⊗[R] T⁄T] :=
      KaehlerDifferential.tensorKaehlerEquiv' R T S (S ⊗[R] T)
    have : Module.Flat (S ⊗[R] T) ((S ⊗[R] T) ⊗[S] Ω[S⁄R]) := .of_linearEquiv e'
    have : Module.Flat S (Ω[S⁄R]) := Module.Flat.of_flat_tensorProduct (S ⊗[R] T) _
    exact Module.Flat.projective_of_finitePresentation

end Algebra
