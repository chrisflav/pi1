import Mathlib
import Pi1.RingTheory.KaehlerBaseChange
import Pi1.RingTheory.FiveLemma

universe u

open TensorProduct

namespace Module

namespace Foo

variable (R S : Type*)
  [CommRing R]
  [CommRing S] [Algebra R S]

variable (M : Type*) [AddCommGroup M] [Module R M]
variable (N : Type*) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
variable (P : Type*) [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]

def assoc [Module S (M ⊗[R] N)] [IsScalarTower R S (M ⊗[R] N)]
    [Module S (M ⊗[R] N ⊗[S] P)] [IsScalarTower R S (M ⊗[R] N ⊗[S] P)] :
    (M ⊗[R] N) ⊗[S] P ≃ₗ[S] M ⊗[R] N ⊗[S] P :=
  let fbil : M ⊗[R] N →ₗ[S] P →ₗ[S] M ⊗[R] N ⊗[S] P :=
    sorry
  let f : (M ⊗[R] N) ⊗[S] P →ₗ[S] M ⊗[R] (N ⊗[S] P) :=
    TensorProduct.lift fbil
  let g : M ⊗[R] (N ⊗[S] P) →ₗ[S] (M ⊗[R] N) ⊗[S] P :=
    sorry
  sorry

noncomputable
def assoc2 :
     P ⊗[S] (N ⊗[R] M) ≃ₗ[S] (P ⊗[S] N) ⊗[R] M :=
  (AlgebraTensorModule.assoc _ _ _ _ _ _).symm

variable (MN : Type*) [AddCommGroup MN] [Module R MN] [Module S MN] [IsScalarTower R S MN]
  (fMN : M →ₗ[R] N →ₗ[R] MN) (hfMN : IsTensorProduct fMN)

include hfMN

def assoc1 :
    MN ⊗[S] P ≃ₗ[S] (N ⊗[S] P) ⊗[R] M :=
  sorry

end Foo

section

variable (R S T : Type*)
  [CommRing R]
  [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

variable (M : Type*) [AddCommGroup M] [Module R M]
variable (MT : Type*) [AddCommGroup MT] [Module R MT] [Module S MT] [IsScalarTower R S MT]
  [Module T MT] [IsScalarTower R T MT] [IsScalarTower S T MT]
  (fM : M →ₗ[R] MT) (hfM : IsBaseChange T fM)
  -- MT = T ⊗[R] M
variable (N : Type*) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
variable (NT : Type*) [AddCommGroup NT] [Module R NT] [Module S NT] [IsScalarTower R S NT]
  [Module T NT] [IsScalarTower R T NT] [IsScalarTower S T NT]
  (fN : N →ₗ[S] NT) (hfN : IsBaseChange T fN)
  -- NT = T ⊗[S] N

variable (P : Type*) [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]
  [Module T P] [IsScalarTower S T P] [IsScalarTower R T P]
  (fP : M →ₗ[R] NT →ₗ[R] P) (hfP : IsTensorProduct fP)

noncomputable
def associator : MT →ₗ[S] N →ₗ[S] P :=
  let fbil : M →ₗ[R] N →ₗ[S] P :=
    sorry
  (hfM.lift fbil).restrictScalars S

noncomputable
def assoc00 : MT ⊗[S] N ≃ₗ[S] P :=
  let fbil00 (m : M) : N →ₗ[S] P :=
    { toFun n := fP m (fN n)
      map_add' x y := by simp
      map_smul' s n := by sorry
      }
  let fbil0 : M →ₗ[R] N →ₗ[S] P :=
    { toFun := fbil00
      map_add' := sorry
      map_smul' := sorry }
  let fbil : MT →ₗ[S] N →ₗ[S] P :=
    (hfM.lift fbil0).restrictScalars S
  let f : MT ⊗[S] N →ₗ[S] P :=
    TensorProduct.lift fbil
  let g : P →ₗ[S] MT ⊗[S] N := sorry
  { __ := f
    invFun := g
    left_inv := sorry
    right_inv := sorry }

--variable (Q : Type*) [AddCommGroup Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]
--  (fQ : MT →ₗ[S] N →ₗ[S] Q) (hfQ : IsTensorProduct fQ)

--def assoc00 : P ≃ₗ[R] Q :=
--  sorry

noncomputable
def assoc0 :
    M ⊗[R] NT ≃ₗ[R] MT ⊗[S] N :=
  let f0 (m : M) : NT →ₗ[T] MT ⊗[S] N :=
    hfN.lift (TensorProduct.mk _ _ _ (fM m))
  let fbil : M →ₗ[R] NT →ₗ[R] MT ⊗[S] N :=
    { toFun m := f0 m
      map_add' x y := by
        dsimp only
        rw [← LinearMap.restrictScalars_add]
        congr
        apply hfN.algHom_ext
        intro n
        simp [f0, hfN.lift_eq]
      map_smul' r x := by
        dsimp only
        rw [← LinearMap.restrictScalars_smul]
        congr
        apply hfN.algHom_ext
        intro n
        simp [f0, hfN.lift_eq]
    }
  let f : M ⊗[R] NT →ₗ[R] MT ⊗[S] N :=
    TensorProduct.lift fbil
  let _ : Module S (M ⊗[R] NT) := sorry
  have : LinearMap.CompatibleSMul (MT ⊗[S] N) (M ⊗[R] NT) R S := sorry
  let gbil : MT →ₗ[S] N →ₗ[S] M ⊗[R] NT :=
    (hfM.lift _).restrictScalars S
  let g : MT ⊗[S] N →ₗ[R] M ⊗[R] NT :=
    (TensorProduct.lift gbil).restrictScalars R
  { __ := f
    invFun := g
    left_inv := sorry
    right_inv := sorry
  }

end

variable (R S T A M : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [CommRing A] [Algebra R A] [Algebra A S] [IsScalarTower R A S]
  [AddCommGroup M] [Module R M] [Module A M]
  [CommRing T] [Algebra R T]

variable (B : Type*) [CommRing B] [Algebra T B] [Algebra R B] [Algebra S B]
  [IsScalarTower R T B] [IsScalarTower R S B]
  [Algebra.IsPushout R S T B]
  [Algebra A B] [SMulCommClass A T B]
  [IsScalarTower A S B]

variable (N : Type*) [AddCommGroup N] [Module R N]

def assoc' :
    T ⊗[R] N ≃ₗ[T] B ⊗[A] M :=
  sorry

def assoc :
    T ⊗[R] N ≃ₗ[T] B ⊗[A] M :=
  sorry

def assoc'' :
    T ⊗[R] (S ⊗[A] M) ≃ₗ[T] B ⊗[A] M := sorry
    --((IsScalarTower.toAlgHom A S B).toLinearMap.rTensor M).liftBaseChange T

-- T ⊗[R] (S ⊗[P.Ring] Ω[P.Ring⁄R]) ≃ₗ[T] (T ⊗[R] S) ⊗[P.Ring] Ω[P.Ring⁄R]
-- M ⊗[R] (T ⊗[S] N) ≃ₗ[R] (M ⊗[R] T) ⊗[S] N
-- M ⊗[R] NT ≃ₗ[R] MT ⊗[S] N

end Module

namespace Algebra

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (P : Extension.{u, u, u} R S)
variable (T : Type u) [CommRing T] [Algebra R T]

namespace Extension

lemma exact_hCotangentι_cotangentComplex :
    Function.Exact h1Cotangentι P.cotangentComplex := by
  sorry

attribute [local instance] KaehlerDifferential.moduleBaseChange'
set_option maxHeartbeats 0 in
noncomputable
def tensorCotangentSpace' :
    T ⊗[R] P.CotangentSpace ≃ₗ[T] (P.baseChange (T := T)).CotangentSpace := by
  let PT : Extension T (T ⊗[R] S) := P.baseChange
  let _ : Algebra P.Ring PT.Ring :=
    TensorProduct.includeRight.toRingHom.toAlgebra
  have : IsScalarTower R P.Ring PT.Ring := sorry
  have : IsPushout R T P.Ring PT.Ring := sorry
  let e : PT.Ring ⊗[P.Ring] Ω[P.Ring⁄R] ≃ₗ[PT.Ring] Ω[PT.Ring⁄T] :=
    KaehlerDifferential.tensorKaehlerEquiv' _ _ _ _
  dsimp only [CotangentSpace]
  let e' :
      (T ⊗[R] S) ⊗[PT.Ring] (PT.Ring ⊗[P.Ring] Ω[P.Ring⁄R]) ≃ₗ[PT.Ring]
      (T ⊗[R] S) ⊗[PT.Ring] Ω[PT.Ring⁄T] :=
    AlgebraTensorModule.congr (LinearEquiv.refl _ _) e
  let _ : Algebra S (T ⊗[R] S) := TensorProduct.includeRight.toRingHom.toAlgebra
  let _ : Algebra P.Ring (T ⊗[R] S) := (algebraMap _ _).comp (algebraMap P.Ring S) |>.toAlgebra
  have : IsScalarTower P.Ring S (T ⊗[R] S) := sorry
  have : SMulCommClass P.Ring T (T ⊗[R] S) := sorry
  have : IsScalarTower P.Ring PT.Ring (T ⊗[R] S) := sorry
  let e₂ : T ⊗[R] (S ⊗[P.Ring] Ω[P.Ring⁄R]) ≃ₗ[T] (T ⊗[R] S) ⊗[P.Ring] Ω[P.Ring⁄R] :=
    sorry
  have : LinearMap.CompatibleSMul ((T ⊗[R] S) ⊗[P.Ring] Ω[P.Ring⁄R])
      ((T ⊗[R] S) ⊗[PT.Ring] PT.Ring ⊗[P.Ring] Ω[P.Ring⁄R]) T
      PT.Ring :=
    sorry
  let e₃ : (T ⊗[R] S) ⊗[P.Ring] Ω[P.Ring⁄R] ≃ₗ[T]
      (T ⊗[R] S) ⊗[PT.Ring] PT.Ring ⊗[P.Ring] Ω[P.Ring⁄R] :=
    (AlgebraTensorModule.cancelBaseChange _ PT.Ring PT.Ring _ _).symm.restrictScalars T
  let e'' : T ⊗[R] S ⊗[P.Ring] Ω[P.Ring⁄R] ≃ₗ[T]
      (T ⊗[R] S) ⊗[PT.Ring] PT.Ring ⊗[P.Ring] Ω[P.Ring⁄R] :=
    e₂ ≪≫ₗ e₃
  -- (T ⊗[R] S) ⊗[P.baseChange.Ring] P.baseChange.Ring ⊗[P.Ring] Ω[P.Ring⁄R]
  exact e'' ≪≫ₗ e'.restrictScalars T
  --let e' := TensorProduct.congr (LinearEquiv.refl _ (T ⊗[R] S)) e
  --exact _ ≪≫ₗ TensorProduct.congr (LinearEquiv.refl _ (T ⊗[R] S)) e
  --exact (AlgebraTensorModule.assoc _ _ _ _ _ _).symm ≪≫ₗ _

def tensorCotangent' :
    T ⊗[R] P.Cotangent ≃ₗ[T] (P.baseChange (T := T)).Cotangent :=
  sorry

noncomputable
def tensorToH1Cotangent :
    T ⊗[R] P.H1Cotangent →ₗ[T] (P.baseChange (T := T)).H1Cotangent := by
  let _ : Algebra S (T ⊗[R] S) := TensorProduct.includeRight.toRingHom.toAlgebra
  apply LinearMap.liftBaseChange T
  let f : P.Hom (P.baseChange (T := T)) :=
    sorry
  apply (Extension.H1Cotangent.map f).restrictScalars R

lemma tensorToH1Cotangent_bijective_of_flat [Module.Flat R T] :
    Function.Bijective (P.tensorToH1Cotangent T) := by
  apply LinearMap.bijective_of (M₁ := Unit) (N₁ := Unit) (M₂ := Unit) (N₂ := Unit)
      (M₄ := T ⊗[R] P.Cotangent) (N₄ := (P.baseChange (T := T)).Cotangent)
      (M₅ := T ⊗[R] P.CotangentSpace) (N₅ := (P.baseChange (T := T)).CotangentSpace)
    0
    0
    (((h1Cotangentι (P := P)).restrictScalars R).lTensor T)
    ((P.cotangentComplex.restrictScalars R).lTensor T)
    0
    0
    (h1Cotangentι.restrictScalars R)
    ((P.baseChange (T := T)).cotangentComplex.restrictScalars R)
    0
    0
    _
    ((P.tensorCotangent' T).restrictScalars R)
    ((P.tensorCotangentSpace' T).restrictScalars R)
  · simp
  · simp
  · ext
    sorry
  · ext
    simp
    sorry
  · tauto
  · simp
    apply Module.Flat.lTensor_preserves_injective_linearMap
    simp only [LinearMap.coe_restrictScalars]
    exact h1Cotangentι_injective
  · apply Module.Flat.lTensor_exact
    simp only [LinearMap.coe_restrictScalars]
    exact P.exact_hCotangentι_cotangentComplex
  · tauto
  · rw [LinearMap.exact_zero_iff_injective]
    simp only [LinearMap.coe_restrictScalars]
    exact h1Cotangentι_injective
  · simp only [LinearMap.coe_restrictScalars]
    apply exact_hCotangentι_cotangentComplex
  · tauto
  · simp
  · exact (P.tensorCotangent' T).bijective
  · exact (P.tensorCotangentSpace' T).injective

end Extension

end

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- Flat base change commutes with `H1Cotangent`. -/
def tensorH1CotangentOfFlat (T : Type*) [CommRing T] [Algebra R T] [Module.Flat R T] :
    T ⊗[R] H1Cotangent R S ≃ₗ[T] H1Cotangent T (T ⊗[R] S) :=
  let _ : Algebra S (T ⊗[R] S) := TensorProduct.includeRight.toRingHom.toAlgebra
  let f := H1Cotangent.map R T S (T ⊗[R] S)
  let f' := (f.restrictScalars R).liftBaseChange T
  sorry

end Algebra
