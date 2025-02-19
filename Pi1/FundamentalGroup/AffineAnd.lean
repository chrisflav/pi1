/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Pi1.Mathlib.CategoryTheory.MorphismProperty.Composition
import Pi1.Mathlib.CategoryTheory.MorphismProperty.UnderAdjunction
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.Etale
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.Finite
import Pi1.FundamentalGroup.AffineColimits
import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!
# Limit properties of subcategories of `P.Over ⊤ X` for `P = affineAnd`
-/

universe u

open CategoryTheory Limits

section

variable {R : CommRingCat.{u}} {ι : Type} (P : ι → Under R)

namespace CommRingCat

variable {ι : Type} (R : ι → CommRingCat.{u})

/--
The categorical product of rings is the cartesian product of rings. This is its `Fan`.
-/
@[simps! pt]
def piFan' : Fan R :=
  Fan.mk (CommRingCat.of ((i : ι) → R i)) (fun i ↦ ofHom <| Pi.evalRingHom _ i)

/--
The categorical product of rings is the cartesian product of rings.
-/
def piFanIsLimit' : IsLimit (piFan' R) where
  lift s := ofHom <| Pi.ringHom fun i ↦ (s.π.1 ⟨i⟩).hom
  fac s i := by rfl
  uniq _ _ h := hom_ext <| DFunLike.ext _ _ fun x ↦ funext fun i ↦
    DFunLike.congr_fun (congrArg Hom.hom <| h ⟨i⟩) x

end CommRingCat

namespace CommRingCat.Under

/-- The canonical fan on `P : ι → Under R` given by `∀ i, P i`. -/
def piFan' : Fan P :=
  Fan.mk (Under.mk <| ofHom <| Pi.ringHom (fun i ↦ (P i).hom.hom))
    (fun i ↦ Under.homMk (ofHom <| Pi.evalRingHom _ i))

/-- The canonical fan is limiting. -/
noncomputable def piFanIsLimit' : IsLimit (piFan' P) :=
  isLimitOfReflects (Under.forget R) <|
    (isLimitMapConeFanMkEquiv (Under.forget R) P _).symm <|
      CommRingCat.piFanIsLimit' (fun i ↦ (P i).right)

end CommRingCat.Under

end

namespace RingHom

variable {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}

-- TODO: reformulate these with ringhoms?

/-- A property of ring homomorphisms `Q` is said to have equalizers, if the equalizer of algebra maps
between algebras satisfiying `Q` also satisfies `Q`. -/
def HasEqualizers (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop) : Prop :=
  ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f g : S →ₐ[R] T), Q (algebraMap R S) → Q (algebraMap R T) →
      Q (algebraMap R (AlgHom.equalizer f g))

def HasFiniteProducts (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop) : Prop :=
  ∀ {R : Type u} [CommRing R] {ι : Type} [_root_.Finite ι] (S : ι → Type u) [∀ i, CommRing (S i)]
    [∀ i, Algebra R (S i)],
    (∀ i, Q (algebraMap R (S i))) → Q (algebraMap R (Π i, S i))

end RingHom

namespace CategoryTheory.MorphismProperty.Over

noncomputable
instance {C : Type*} [Category C] (P : MorphismProperty C) (X : C)
    [HasPullbacks C] [P.IsStableUnderComposition] [P.ContainsIdentities]
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    CreatesFiniteLimits (Over.forget P ⊤ X) :=
  createsFiniteLimitsOfCreatesTerminalAndPullbacks _

instance {C : Type*} [Category C] (P : MorphismProperty C) (X : C)
    [HasPullbacks C] [P.IsStableUnderComposition] [P.ContainsIdentities]
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    PreservesFiniteLimits (Over.forget P ⊤ X) :=
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks (Over.forget P ⊤ X)

end CategoryTheory.MorphismProperty.Over

namespace AlgebraicGeometry

variable {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
variable (P : MorphismProperty Scheme.{u}) [HasAffineProperty P (affineAnd Q)]

namespace AffineAnd

open MorphismProperty

variable {X : Scheme.{u}}

instance (f : P.Over ⊤ X) : IsAffineHom f.hom :=
  HasAffineProperty.affineAnd_le_isAffineHom P inferInstance _ f.2

def toAffine (X : Scheme.{u}) : P.Over ⊤ X ⥤ Affine X where
  obj f := ⟨f.toComma, inferInstance⟩
  map f := ⟨f.toCommaMorphism, trivial, trivial⟩

def toAffineFullyFaithful (X : Scheme.{u}) : (toAffine P X).FullyFaithful where
  preimage f := ⟨f.toCommaMorphism, trivial, trivial⟩

instance : (toAffine P X).Faithful := (toAffineFullyFaithful P X).faithful
instance : (toAffine P X).Full := (toAffineFullyFaithful P X).full

variable [P.IsStableUnderBaseChange]

variable (J : Type) [SmallCategory J] [FinCategory J]

noncomputable
def _root_.CommRingCat.Under.createsFiniteProductsForget (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) (R : CommRingCat.{u}) :
    CreatesFiniteProducts (MorphismProperty.Under.forget (RingHom.toMorphismProperty Q) ⊤ R) := by
  refine ⟨fun J _ ↦ Comma.forgetCreatesLimitsOfShapeOfClosed _ <| ?_⟩
  intro (D : Discrete J ⥤ Under R) c hc hD
  let e : c.pt ≅ CommRingCat.mkUnder R (Π i, D.obj ⟨i⟩) :=
    (limit.isoLimitCone ⟨c, hc⟩).symm ≪≫
      HasLimit.isoOfNatIso (Discrete.natIso fun i ↦ eqToIso <| by simp) ≪≫
      limit.isoLimitCone ⟨CommRingCat.Under.piFan' <| fun i ↦ (D.obj ⟨i⟩),
        CommRingCat.Under.piFanIsLimit' <| fun i ↦ (D.obj ⟨i⟩)⟩
  have := Under.w e.inv
  rw [← this]
  have : (RingHom.toMorphismProperty Q).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp hQi
  rw [MorphismProperty.cancel_right_of_respectsIso (P := RingHom.toMorphismProperty Q)]
  exact hQp _ fun i ↦ hD ⟨i⟩

lemma _root_.CommRingCat.Under.hasFiniteProducts (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) (R : CommRingCat.{u}) :
    HasFiniteProducts ((RingHom.toMorphismProperty Q).Under ⊤ R) := by
  refine ⟨fun n ↦ ⟨fun D ↦ ?_⟩⟩
  have := CommRingCat.Under.createsFiniteProductsForget hQi hQp R
  exact CategoryTheory.hasLimit_of_created D (Under.forget _ _ R)

noncomputable
def _root_.CommRingCat.Under.createsEqualizersForget (hQi : RingHom.RespectsIso Q)
    (hQe : RingHom.HasEqualizers Q) (R : CommRingCat.{u}) :
    CreatesLimitsOfShape WalkingParallelPair
      (MorphismProperty.Under.forget (RingHom.toMorphismProperty Q) ⊤ R) := by
  apply Comma.forgetCreatesLimitsOfShapeOfClosed
  intro (D : WalkingParallelPair ⥤ Under R) c hc hD
  let e : c.pt ≅
      CommRingCat.mkUnder R
        (AlgHom.equalizer (R := R)
          (CommRingCat.toAlgHom (D.map .left))
          (CommRingCat.toAlgHom (D.map .right))) :=
    (limit.isoLimitCone ⟨c, hc⟩).symm ≪≫
      HasLimit.isoOfNatIso (diagramIsoParallelPair _) ≪≫ limit.isoLimitCone
        ⟨CommRingCat.Under.equalizerFork (D.map .left) (D.map .right),
          CommRingCat.Under.equalizerForkIsLimit
            (D.map .left) (D.map .right)⟩
  have := Under.w e.inv
  rw [← this]
  have : (RingHom.toMorphismProperty Q).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp hQi
  rw [MorphismProperty.cancel_right_of_respectsIso (P := RingHom.toMorphismProperty Q)]
  exact hQe _ _ (hD .zero) (hD .one)

noncomputable
def _root_.CommRingCat.Under.createsFiniteLimitsForget (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) (hQe : RingHom.HasEqualizers Q) (R : CommRingCat.{u}) :
    CreatesFiniteLimits (Under.forget (RingHom.toMorphismProperty Q) ⊤ R) := by
  have := CommRingCat.Under.createsFiniteProductsForget hQi hQp
  have := CommRingCat.Under.createsEqualizersForget hQi hQe
  apply createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts

lemma _root_.CommRingCat.Under.hasEqualizers (hQi : RingHom.RespectsIso Q)
    (hQe : RingHom.HasEqualizers Q) (R : CommRingCat.{u}) :
    HasEqualizers ((RingHom.toMorphismProperty Q).Under ⊤ R) := by
  refine ⟨fun D ↦ ?_⟩
  have := CommRingCat.Under.createsEqualizersForget hQi hQe R
  exact CategoryTheory.hasLimit_of_created D (Under.forget _ _ R)

lemma _root_.CommRingCat.Under.hasFiniteLimits (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) (hQe : RingHom.HasEqualizers Q) (R : CommRingCat.{u}) :
    HasFiniteLimits ((RingHom.toMorphismProperty Q).Under ⊤ R) :=
  have := CommRingCat.Under.hasFiniteProducts hQi hQp
  have := CommRingCat.Under.hasEqualizers hQi hQe
  hasFiniteLimits_of_hasEqualizers_and_finite_products

lemma _root_.CommRingCat.Under.property_limit_of_hasFiniteProducts_of_hasEqualizers
    (hQi : RingHom.RespectsIso Q) (hQp : RingHom.HasFiniteProducts Q)
    (hQe : RingHom.HasEqualizers Q)
    {R : CommRingCat.{u}} (D : J ⥤ Under R) (h : ∀ j, Q (D.obj j).hom.hom) :
    Q (limit D).hom.hom := by
  have := CommRingCat.Under.hasFiniteLimits hQi hQp hQe
  let D' : J ⥤ (RingHom.toMorphismProperty Q).Under ⊤ R :=
    MorphismProperty.Comma.lift D h (by simp) (by simp)
  let A := limit D'
  have : CreatesFiniteLimits (Under.forget (RingHom.toMorphismProperty Q) ⊤ R) :=
    CommRingCat.Under.createsFiniteLimitsForget hQi hQp hQe R
  let e : (Under.forget _ _ R).obj A ≅ limit D :=
    preservesLimitIso (Under.forget (RingHom.toMorphismProperty Q) ⊤ R) D'
  have := CategoryTheory.Under.w e.hom
  rw [← this, CommRingCat.hom_comp, hQi.cancel_right_isIso]
  exact A.prop

noncomputable
def createsFiniteColimits (hQi : RingHom.RespectsIso Q) (hQp : RingHom.HasFiniteProducts Q)
    (hQe : RingHom.HasEqualizers Q) :
    CreatesFiniteColimits (toAffine P X) := by
  constructor
  intro J _ _
  constructor
  intro D
  let D' : J ⥤ Affine X := D ⋙ toAffine P X
  have : HasColimit D' := inferInstance
  have : P (colimit D').hom := by
    rw [IsLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
    dsimp
    intro U
    simp only [morphismRestrict]
    rw [P.cancel_left_of_respectsIso]
    show P <| ((Affine.pullback U.1.ι).obj (colimit D')).hom
    let i : (Affine.pullback U.1.ι).obj (colimit D') ≅
        colimit (D' ⋙ Affine.pullback U.1.ι) :=
      preservesColimitIso (Affine.pullback U.1.ι) D'
    erw [P.over_iso_iff ((MorphismProperty.Comma.forget _ _ _ _ _).mapIso i)]
    simp only [Comma.forget_obj, Functor.id_obj, Functor.const_obj_obj]
    let i₂ : (Affine.Γ U.1).rightOp.obj (colimit (D' ⋙ Affine.pullback U.1.ι)) ≅
        colimit (D' ⋙ Affine.pullback U.1.ι ⋙ (Affine.Γ U.1).rightOp) :=
      preservesColimitIso (Affine.Γ U.1).rightOp (D' ⋙ Affine.pullback U.1.ι)
    let i₃ : ((Affine.Γ U.1).rightOp.obj (colimit (D' ⋙ Affine.pullback U.1.ι))).unop ≅
        (colimit (D' ⋙ Affine.pullback U.1.ι ⋙ (Affine.Γ U.1).rightOp)).unop :=
      i₂.symm.unop
    let i₄ : ((Affine.Γ U.1).rightOp.obj (colimit (D' ⋙ Affine.pullback U.1.ι))).unop ≅
        limit (D' ⋙ Affine.pullback U.1.ι ⋙ (Affine.Γ U.1).rightOp).leftOp :=
      i₃ ≪≫ (limitLeftOpIsoUnopColimit
        (D' ⋙ Affine.pullback U.1.ι ⋙ (Affine.Γ ↑↑U).rightOp)).symm
    have := CategoryTheory.Under.w i₄.inv
    rw [HasAffineProperty.iff_of_isAffine (P := P)]
    simp
    constructor
    · infer_instance
    have heq : (colimit (D' ⋙ Affine.pullback U.1.ι)).hom.appTop =
        ((Affine.Γ U.1).rightOp.obj (colimit (D' ⋙ Affine.pullback U.1.ι))).unop.hom := rfl
    rw [heq, ← this, CommRingCat.hom_comp]
    simp only [Functor.id_obj, Functor.rightOp_obj]
    rw [hQi.cancel_right_isIso]
    apply _root_.CommRingCat.Under.property_limit_of_hasFiniteProducts_of_hasEqualizers
    · exact hQi
    · exact hQp
    · exact hQe
    · intro ⟨j⟩
      have : P (pullback.snd (D'.obj j).hom U.1.ι) := P.pullback_snd _ _ (D.obj j).prop
      rw [HasAffineProperty.iff_of_isAffine (P := P)] at this
      exact this.2
  exact CategoryTheory.createsColimitOfFullyFaithfulOfIso
    ⟨(colimit D').toComma, this⟩ (eqToIso rfl)

lemma hasFiniteColimits (hQi : RingHom.RespectsIso Q) (hQp : RingHom.HasFiniteProducts Q)
    (hQe : RingHom.HasEqualizers Q) :
    HasFiniteColimits (P.Over ⊤ X) := by
  constructor
  intro J _ _
  constructor
  intro D
  have := createsFiniteColimits (X := X) P hQi hQp hQe
  apply CategoryTheory.hasColimit_of_created D (toAffine P X)

lemma preservesFiniteColimits_toAffine (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) (hQe : RingHom.HasEqualizers Q) :
    PreservesFiniteColimits (toAffine P X) := by
  have := hasFiniteColimits (X := X) P hQi hQp hQe
  have := createsFiniteColimits (X := X) P hQi hQp hQe
  infer_instance

theorem preservesFiniteLimits_pullback
    [P.IsStableUnderComposition] [P.ContainsIdentities]
    [P.HasOfPostcompProperty P] {Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (MorphismProperty.Over.pullback P ⊤ f) := by
  constructor
  intro J _ _
  have heq : MorphismProperty.Over.pullback P ⊤ f ⋙ MorphismProperty.Over.forget _ _ _ =
      MorphismProperty.Over.forget _ _ _ ⋙ Over.pullback f :=
    rfl
  have : PreservesLimitsOfShape J
      (MorphismProperty.Over.pullback P ⊤ f ⋙ MorphismProperty.Over.forget _ _ _) := by
    rw [heq]
    infer_instance
  apply preservesLimitsOfShape_of_reflects_of_preserves
    (MorphismProperty.Over.pullback P ⊤ f) (MorphismProperty.Over.forget _ _ _)

theorem preservesFiniteColimits_pullback' (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) (hQe : RingHom.HasEqualizers Q)
    [(RingHom.toMorphismProperty Q).IsStableUnderCobaseChange]
    [∀ (R S : CommRingCat.{u}) (f : R ⟶ S), PreservesFiniteLimits
      (Under.pushout (RingHom.toMorphismProperty Q) ⊤ f)]
    {Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (Over.pullback P ⊤ f) := by
  constructor
  intro J _ _
  sorry

theorem preservesFiniteColimits_pullback (hQi : RingHom.RespectsIso Q) (hQp : RingHom.HasFiniteProducts Q)
    (hQe : RingHom.HasEqualizers Q)
    [P.IsStableUnderComposition] [P.ContainsIdentities]
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    {Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (MorphismProperty.Over.pullback P ⊤ f) := by
  constructor
  intro J _ _
  have heq : MorphismProperty.Over.pullback P ⊤ f ⋙ toAffine P X =
      toAffine P Y ⋙ Affine.pullback f :=
    rfl
  have : PreservesFiniteColimits (toAffine P Y) :=
    preservesFiniteColimits_toAffine P (X := Y) hQi hQp hQe
  -- this is wrong (!), since `f` is not necessarily flat
  have : PreservesFiniteColimits (Affine.pullback f) :=
    sorry
  have : PreservesColimitsOfShape J (MorphismProperty.Over.pullback P ⊤ f ⋙ toAffine P X) := by
    rw [heq]
    infer_instance
  apply preservesColimitsOfShape_of_reflects_of_preserves
    (MorphismProperty.Over.pullback P ⊤ f) (toAffine P X)

end AffineAnd

end AlgebraicGeometry
