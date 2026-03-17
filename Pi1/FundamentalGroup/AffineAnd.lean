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
import Pi1.Mathlib.CategoryTheory.Limits.MorphismProperty
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.Etale
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.Finite
import Pi1.FundamentalGroup.AffineColimits
import Pi1.Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!
# Limit properties of subcategories of `P.Over ⊤ X` for `P = affineAnd`
-/

universe u

open CategoryTheory Limits

namespace CategoryTheory.MorphismProperty

variable {A : Type*} [Category A]
  {B : Type*} [Category B] {T : Type*} [Category T] {L L₁ L₂ L₃ : A ⥤ T} {P : MorphismProperty T}
  {Q : MorphismProperty A} {W : MorphismProperty B} [Q.IsMultiplicative] [W.IsMultiplicative]
  {R R₁ R₂ R₃ : B ⥤ T}

variable (L)

variable {L} (R)

variable {C : Type*} [Category C] (P Q : MorphismProperty C) [Q.IsMultiplicative]

def Over.congr [P.RespectsIso] [Q.RespectsIso] {X Y : C} (e : X ≅ Y) :
    P.Over Q X ≌ P.Over Q Y :=
  Comma.mapRightIso _ (Discrete.natIso fun _ ↦ e)

@[simps!]
def Under.congr [P.RespectsIso] [Q.RespectsIso] {X Y : C} (e : X ≅ Y) :
    P.Under Q X ≌ P.Under Q Y :=
  Comma.mapLeftIso _ (Discrete.natIso fun _ ↦ e)

@[simps]
noncomputable def pushoutIsoOfIso [HasPushouts C] {X Y X' Y' Z : C} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk f') (g : X ⟶ Z) :
    pushout g f ≅ pushout (e.inv.left ≫ g) f' where
  hom := pushout.map _ _ _ _ (𝟙 Z) e.hom.right e.hom.left (by simp) (by simp)
  inv := pushout.map _ _ _ _ (𝟙 Z) e.inv.right e.inv.left (by simp) (by simp)

noncomputable
def Under.congrPushoutIso [HasPushouts C] [P.IsStableUnderCobaseChange]
    [Q.IsStableUnderCobaseChange] [Q.RespectsIso]
    {X X' Y Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') (eX : X ≅ X') (eY : Y ≅ Y')
    (h : f ≫ eY.hom = eX.hom ≫ f') :
    (Under.congr P Q eX).functor ⋙ Under.pushout P Q f' ≅
      Under.pushout P Q f ⋙ (Under.congr P Q eY).functor :=
  NatIso.ofComponents
    (fun A ↦ Under.isoMk ((pushoutIsoOfIso (Arrow.isoMk eX eY h.symm) A.hom).symm)) <|
    fun {A B} g ↦ by
      ext
      apply pushout.hom_ext <;> simp [Under.pushout]

end CategoryTheory.MorphismProperty

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

/-- A property of ring homomorphisms `Q` is said to have equalizers, if the equalizer of algebra
maps between algebras satisfiying `Q` also satisfies `Q`. -/
def HasEqualizers (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop) : Prop :=
  ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f g : S →ₐ[R] T), Q (algebraMap R S) → Q (algebraMap R T) →
      Q (algebraMap R (AlgHom.equalizer f g))

def HasFiniteProducts (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop) : Prop :=
  ∀ {R : Type u} [CommRing R] {ι : Type} [_root_.Finite ι] (S : ι → Type u) [∀ i, CommRing (S i)]
    [∀ i, Algebra R (S i)],
    (∀ i, Q (algebraMap R (S i))) → Q (algebraMap R (Π i, S i))

end RingHom

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

@[implicit_reducible]
noncomputable
def _root_.CommRingCat.Under.createsFiniteProductsForget (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) (R : CommRingCat.{u}) :
    CreatesFiniteProducts (MorphismProperty.Under.forget (RingHom.toMorphismProperty Q) ⊤ R) := by
  refine ⟨fun J _ ↦ ?_⟩
  have : (commaObj (Functor.fromPUnit R) (𝟭 _)
      (RingHom.toMorphismProperty Q)).IsClosedUnderLimitsOfShape (Discrete J) := by
    constructor
    intro (A : Under R) ⟨(pres : LimitPresentation _ A), hpres⟩
    -- intro (D : Discrete J ⥤ Under R) c hc hD
    let e : A ≅ CommRingCat.mkUnder R (Π i, pres.diag.obj ⟨i⟩) :=
      (limit.isoLimitCone ⟨_, pres.isLimit⟩).symm ≪≫
        HasLimit.isoOfNatIso (Discrete.natIso fun i ↦ eqToIso <| by simp) ≪≫
        limit.isoLimitCone ⟨CommRingCat.Under.piFan' <| fun i ↦ (pres.diag.obj ⟨i⟩),
          CommRingCat.Under.piFanIsLimit' <| fun i ↦ (pres.diag.obj ⟨i⟩)⟩
    have := Under.w e.inv
    simp only [commaObj_iff, Functor.const_obj_obj, Functor.id_obj]
    rw [← this]
    have : (RingHom.toMorphismProperty Q).RespectsIso :=
      RingHom.toMorphismProperty_respectsIso_iff.mp hQi
    rw [MorphismProperty.cancel_right_of_respectsIso (P := RingHom.toMorphismProperty Q)]
    exact hQp _ fun i ↦ hpres ⟨i⟩
  apply +allowSynthFailures (Comma.forgetCreatesLimitsOfShapeOfClosed _)

lemma _root_.CommRingCat.Under.hasFiniteProducts (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) (R : CommRingCat.{u}) :
    HasFiniteProducts ((RingHom.toMorphismProperty Q).Under ⊤ R) := by
  refine ⟨fun n ↦ ⟨fun D ↦ ?_⟩⟩
  have := CommRingCat.Under.createsFiniteProductsForget hQi hQp R
  exact CategoryTheory.hasLimit_of_created D (Under.forget _ _ R)

@[implicit_reducible]
noncomputable
def _root_.CommRingCat.Under.createsEqualizersForget (hQi : RingHom.RespectsIso Q)
    (hQe : RingHom.HasEqualizers Q) (R : CommRingCat.{u}) :
    CreatesLimitsOfShape WalkingParallelPair
      (MorphismProperty.Under.forget (RingHom.toMorphismProperty Q) ⊤ R) := by
  have :
      (commaObj (Functor.fromPUnit R) (𝟭 _)
        (RingHom.toMorphismProperty Q)).IsClosedUnderLimitsOfShape
      WalkingParallelPair := by
    constructor
    intro (A : Under R) ⟨(pres : LimitPresentation _ A), hpres⟩
    let e : A ≅
        CommRingCat.mkUnder R
          (AlgHom.equalizer (R := R)
            (CommRingCat.toAlgHom (pres.diag.map .left))
            (CommRingCat.toAlgHom (pres.diag.map .right))) :=
      (limit.isoLimitCone ⟨_, pres.isLimit⟩).symm ≪≫
        HasLimit.isoOfNatIso (diagramIsoParallelPair _) ≪≫ limit.isoLimitCone
          ⟨CommRingCat.Under.equalizerFork (pres.diag.map .left) (pres.diag.map .right),
            CommRingCat.Under.equalizerForkIsLimit
              (pres.diag.map .left) (pres.diag.map .right)⟩
    have := Under.w e.inv
    simp only [commaObj_iff, Functor.const_obj_obj, Functor.id_obj]
    rw [← this]
    have : (RingHom.toMorphismProperty Q).RespectsIso :=
      RingHom.toMorphismProperty_respectsIso_iff.mp hQi
    rw [MorphismProperty.cancel_right_of_respectsIso (P := RingHom.toMorphismProperty Q)]
    exact hQe _ _ (hpres .zero) (hpres .one)
  apply Comma.forgetCreatesLimitsOfShapeOfClosed

@[implicit_reducible]
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

@[implicit_reducible]
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
    rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
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
  infer_instance

@[simps!]
def _root_.AlgebraicGeometry.IsAffineOpen.ΓProp
    (hQi : RingHom.RespectsIso Q)
    {S : Scheme.{u}} {U : S.Opens} (hU : IsAffineOpen U) :
    (P.Over ⊤ S)ᵒᵖ ⥤ (RingHom.toMorphismProperty Q).Under ⊤ Γ(S, U) where
  obj X := MorphismProperty.Under.mk _ (X.unop.hom.app U) <| by
    have : targetAffineLocally (affineAnd Q) X.unop.hom := by
      rw [← HasAffineProperty.eq_targetAffineLocally P]
      exact X.unop.prop
    rw [targetAffineLocally_affineAnd_iff hQi] at this
    exact (this U hU).2
  map {X Y} f := MorphismProperty.Under.homMk
      (f.unop.left.appLE (X.unop.hom ⁻¹ᵁ U) (Y.unop.hom ⁻¹ᵁ U)
      (by rw [← Scheme.Hom.comp_preimage, CategoryTheory.Over.w])) <| by
    simp [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  map_id X := by
    ext : 1
    simp only [Functor.id_obj, Functor.const_obj_obj,
      Scheme.Hom.appLE,
      homOfLE_leOfHom, homOfLE_refl, op_id, unop_id, Comma.id_hom,
      CategoryTheory.Comma.id_left, Scheme.Hom.id_app, Category.id_comp,
      Under.homMk_hom, Under.homMk_right, CategoryTheory.Comma.id_right]
    apply CategoryTheory.Functor.map_id
  map_comp {X Y Z} f g := by
    ext : 1
    show Scheme.Hom.appLE (g.unop.left ≫ f.unop.left) _ _ _ =
      Scheme.Hom.appLE _ _ _ _ ≫ Scheme.Hom.appLE _ _ _ _
    rw [Scheme.Hom.appLE_comp_appLE]

@[simps! obj_hom]
def ΓProp (hQi : RingHom.RespectsIso Q) (S : Scheme.{u}) [IsAffine S] :
    (P.Over ⊤ S)ᵒᵖ ⥤ (RingHom.toMorphismProperty Q).Under ⊤ Γ(S, ⊤) :=
  (isAffineOpen_top S).ΓProp P hQi

omit [P.IsStableUnderBaseChange] in
-- `simps` generates this with `appLE` on the RHS
@[simp]
lemma ΓProp_map_right (hQi : RingHom.RespectsIso Q) (S : Scheme.{u}) [IsAffine S]
    {X Y : (P.Over ⊤ S)ᵒᵖ} (f : X ⟶ Y) :
    ((ΓProp P hQi S).map f).right = f.unop.left.appTop := by
  simpa [ΓProp, IsAffineOpen.ΓProp, Scheme.Hom.appTop] using
    (Scheme.Hom.app_eq_appLE ..).symm

lemma _root_.AlgebraicGeometry.Scheme.Hom.appTop_bijective_of_isAffine
      {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] :
    Function.Bijective (fun (f : X ⟶ Y) ↦ f.appTop) := by
  refine ⟨fun f g (hfg : f.appTop = g.appTop) ↦ ?_, fun f ↦ ?_⟩
  · have (f : X ⟶ Y) : f = X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.inv := by
      simp [Scheme.isoSpec_hom_naturality_assoc]
    rw [this f, this g, hfg]
  · use X.isoSpec.hom ≫ Spec.map f ≫ Y.isoSpec.inv
    simp [Scheme.isoSpec]

omit [P.IsStableUnderBaseChange] in
lemma faithful_ΓProp (hQi : RingHom.RespectsIso Q) {S : Scheme.{u}} [IsAffine S] :
    (ΓProp P hQi S).Faithful where
  map_injective := by
    intro ⟨X⟩ ⟨Y⟩ ⟨f⟩ ⟨g⟩ hfg
    have : f = g := by
      ext : 1
      have : IsAffine X.left := isAffine_of_isAffineHom (Y := S) X.hom
      have : IsAffine Y.left := isAffine_of_isAffineHom (Y := S) Y.hom
      apply AlgebraicGeometry.Scheme.Hom.appTop_bijective_of_isAffine.injective
      simpa using congr($(hfg).right)
    rw [this]

omit [P.IsStableUnderBaseChange] in
lemma full_ΓProp (hQi : RingHom.RespectsIso Q) {S : Scheme.{u}} [IsAffine S] :
    (ΓProp P hQi S).Full where
  map_surjective := by
    intro ⟨X⟩ ⟨Y⟩ f
    have : IsAffine ((𝟭 Scheme).obj X.left) := isAffine_of_isAffineHom (Y := S) X.hom
    have : IsAffine ((𝟭 Scheme).obj Y.left) := isAffine_of_isAffineHom (Y := S) Y.hom
    have : IsAffine ((Functor.fromPUnit S).obj X.right) := inferInstanceAs <| IsAffine S
    have : IsAffine Y.left := isAffine_of_isAffineHom (Y := S) Y.hom
    obtain ⟨f', h⟩ := AlgebraicGeometry.Scheme.Hom.appTop_bijective_of_isAffine.surjective f.right
    use (MorphismProperty.Over.homMk f' <| by
      apply AlgebraicGeometry.Scheme.Hom.appTop_bijective_of_isAffine.injective
      simpa [h] using f.w.symm).op
    ext : 1
    simpa using h

omit [P.IsStableUnderBaseChange] in
lemma essSurj_ΓProp (hQi : RingHom.RespectsIso Q) {S : Scheme.{u}} [IsAffine S] :
    (ΓProp P hQi S).EssSurj where
  mem_essImage R := by
    let X : P.Over ⊤ S := MorphismProperty.Over.mk ⊤ (Spec.map R.hom ≫ S.isoSpec.inv) <| by
      rw [P.cancel_right_of_respectsIso, HasAffineProperty.SpecMap_iff_of_affineAnd (P := P) _ hQi]
      exact R.prop
      infer_instance
    refine ⟨⟨X⟩, ⟨Under.isoMk (Scheme.ΓSpecIso _) ?_⟩⟩
    simp [X, Scheme.isoSpec]

omit [P.IsStableUnderBaseChange] in
lemma isEquivalence_ΓProp (hQi : RingHom.RespectsIso Q) {S : Scheme.{u}} [IsAffine S] :
    (ΓProp P hQi S).IsEquivalence where
  faithful := faithful_ΓProp ..
  full := full_ΓProp ..
  essSurj := essSurj_ΓProp ..

attribute [reassoc (attr := simp)] Scheme.appLE_comp_appLE

noncomputable
def pullbackΓPropIso [(RingHom.toMorphismProperty Q).IsStableUnderCobaseChange]
    (hQi : RingHom.RespectsIso Q) {S T : Scheme.{u}} [IsAffine S]
    [IsAffine T] (f : S ⟶ T) :
    (Over.pullback P ⊤ f).op ⋙ ΓProp P hQi S ≅
      ΓProp P hQi T ⋙ Under.pushout _ ⊤ f.appTop :=
  NatIso.ofComponents
    (fun X ↦
      haveI : IsAffine X.unop.left := isAffine_of_isAffineHom (Y := T) X.unop.hom
      Under.isoMk (ΓpullbackIsoPushout (X := X.unop.left) (Y := S) (S := T)
        (X.unop.hom : X.unop.left ⟶ T) f) <| by simp) <| fun {X Y} g ↦ by
    ext : 1
    dsimp [MorphismProperty.Under.pushout]
    have : IsAffine ((𝟭 Scheme).obj (Opposite.unop X).left) :=
      isAffine_of_isAffineHom (Y := T) X.unop.hom
    have : IsAffine ((Functor.fromPUnit T).obj (Opposite.unop X).right) :=
      inferInstanceAs <| IsAffine T
    rw [← cancel_epi (ΓpullbackIsoPushout (X.unop).hom f).inv]
    apply pushout.hom_ext
    · simp [← Scheme.Hom.comp_appTop_assoc]
    · simp [← Scheme.Hom.comp_appTop_assoc]

@[simps!]
noncomputable
def overSpecEquivUnder (hQi : RingHom.RespectsIso Q) (R : CommRingCat.{u}) :
    (P.Over ⊤ (Spec R))ᵒᵖ ≌ (RingHom.toMorphismProperty Q).Under ⊤ R :=
  have : (RingHom.toMorphismProperty Q).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp hQi
  have : (ΓProp P hQi (Spec R)).IsEquivalence :=
    isEquivalence_ΓProp P hQi
  (ΓProp P hQi (Spec R)).asEquivalence.trans <| Under.congr _ ⊤ (Scheme.ΓSpecIso R)

noncomputable
def overSpecEquivUnderCompPushoutIso (hQi : RingHom.RespectsIso Q) {R S : CommRingCat.{u}}
    (f : R ⟶ S)
    [(RingHom.toMorphismProperty Q).IsStableUnderCobaseChange] :
    (overSpecEquivUnder P hQi R).functor ⋙
      (MorphismProperty.Under.pushout (RingHom.toMorphismProperty Q) ⊤ f) ≅
      (Over.pullback P ⊤ (Spec.map f)).op ⋙ (overSpecEquivUnder P hQi S).functor :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Under.congrPushoutIso _ ⊤
      (Spec.map f).appTop f (Scheme.ΓSpecIso R) (Scheme.ΓSpecIso S) (by simp)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pullbackΓPropIso P hQi _).symm _ ≪≫
      Functor.associator _ _ _

lemma preservesColimitsOfShape_pullback_iff_preservesLimitsOfShape (hQi : RingHom.RespectsIso Q)
    {R S : CommRingCat.{u}} (f : R ⟶ S) {J : Type*} [Category J]
    [(RingHom.toMorphismProperty Q).IsStableUnderCobaseChange] :
    PreservesColimitsOfShape J (Over.pullback P ⊤ (Spec.map f)) ↔
      PreservesLimitsOfShape Jᵒᵖ
        (MorphismProperty.Under.pushout (RingHom.toMorphismProperty Q) ⊤ f) := by
  let iso : (overSpecEquivUnder P hQi R).functor ⋙
      (Under.pushout (RingHom.toMorphismProperty Q) ⊤ f) ⋙
      (overSpecEquivUnder P hQi S).inverse ≅ (Over.pullback P ⊤ (Spec.map f)).op :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (overSpecEquivUnderCompPushoutIso P hQi f) _ ≪≫
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (overSpecEquivUnder P hQi S).unitIso.symm ≪≫
      Functor.rightUnitor _
  let iso' : ((overSpecEquivUnder P hQi R).functor.rightOp ⋙
      (Under.pushout (RingHom.toMorphismProperty Q) ⊤ f).op ⋙
      (overSpecEquivUnder P hQi S).inverse.leftOp).op ≅ (Over.pullback P ⊤ (Spec.map f)).op :=
    iso
  let foo := NatIso.removeOp iso'
  let e' : _ ≅ (overSpecEquivUnder P (Q := Q) hQi R).inverse.leftOp ⋙
      (overSpecEquivUnder P (Q := Q) hQi R).functor.rightOp :=
   (NatIso.op <| (overSpecEquivUnder P (Q := Q) hQi R).counitIso)
  let e'' : _ ≅ (overSpecEquivUnder P hQi S).inverse.leftOp ⋙
      (overSpecEquivUnder P hQi S).functor.rightOp :=
   (NatIso.op <| (overSpecEquivUnder P hQi S).counitIso)
  let iso2 : (Under.pushout (RingHom.toMorphismProperty Q) ⊤ f).op ≅
      (overSpecEquivUnder P hQi R).inverse.leftOp ⋙ Over.pullback P ⊤ (Spec.map f) ⋙
      (overSpecEquivUnder P hQi S).functor.rightOp :=
    (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft _ e'' ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.leftUnitor _).symm _ ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerRight e' _) _ ≪≫
      Functor.isoWhiskerRight (Functor.associator _ _ _) _ ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft _ foo.symm) _ ≪≫ Functor.associator _ _ _
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · convert preservesLimitsOfShape_of_op _ _
    convert preservesColimitsOfShape_of_natIso iso2.symm
    exact preservesColimitsOfShape_of_equiv (opOpEquivalence J).symm _
  · convert preservesColimitsOfShape_of_op _ _
    exact preservesLimitsOfShape_of_natIso iso

instance preservesColimitsOfShape_pullback_of_toAffine {J : Type*} [Category J]
      {Y : Scheme.{u}} (f : X ⟶ Y)
      [PreservesColimitsOfShape J (toAffine P Y)]
      [PreservesColimitsOfShape J (Affine.pullback f)] :
    PreservesColimitsOfShape J (Over.pullback P ⊤ f) := by
  have heq : MorphismProperty.Over.pullback P ⊤ f ⋙ toAffine P X =
      toAffine P Y ⋙ Affine.pullback f :=
    rfl
  have : PreservesColimitsOfShape J (MorphismProperty.Over.pullback P ⊤ f ⋙ toAffine P X) := by
    rw [heq]
    infer_instance
  apply preservesColimitsOfShape_of_reflects_of_preserves
    (MorphismProperty.Over.pullback P ⊤ f) (toAffine P X)

lemma isPullback_openCoverOfBase_map {X Y Z T : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : T ⟶ pullback f g) (𝒰 : Z.OpenCover) (i : 𝒰.I₀) :
    IsPullback (pullback.fst (h ≫ pullback.fst _ _) (pullback.fst f (𝒰.f i)))
      (pullback.lift
        (pullback.map _ _ _ _ (h ≫ pullback.fst _ _) (pullback.snd _ _) f
          (by simp) pullback.condition)
        (pullback.map _ _ _ _ (h ≫ pullback.snd _ _) (pullback.snd _ _) f
          (by simp [pullback.condition]) pullback.condition)
        (by simp))
      h ((Scheme.Pullback.openCoverOfBase 𝒰 f g).f i) := by
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · apply pullback.hom_ext <;> simp
  · intro c
    refine pullback.lift c.fst
      (pullback.lift (c.snd ≫ pullback.fst _ _ ≫ pullback.fst _ _)
        (c.snd ≫ pullback.fst _ _ ≫ pullback.snd _ _)
        (by simp; rw [pullback.condition]))
        (by rw [pullback.lift_fst, c.condition_assoc]; simp)
  · intro c
    rw [pullback.lift_fst]
  · intro c
    refine pullback.hom_ext ?_ ?_
    · simp only [Scheme.Pullback.openCoverOfBase_f, PullbackCone.π_app_left,
      PullbackCone.π_app_right, Category.assoc, limit.lift_π, PullbackCone.mk_pt,
      PullbackCone.mk_π_app]
      apply pullback.hom_ext
      · simp only [pullback.map]
        simp_rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, c.condition_assoc]
        simp
      · simp_rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd]
    · apply pullback.hom_ext
      · simp_rw [Category.assoc, pullback.lift_snd_assoc, pullback.lift_fst,
          pullback.lift_fst_assoc]
        simp [c.condition_assoc]
      · simp_rw [Category.assoc, pullback.lift_snd_assoc, pullback.lift_snd,
          pullback.lift_snd_assoc, pullback.lift_snd, pullback.condition]
  · intro c m hfst hsnd
    apply pullback.hom_ext
    rw [hfst, pullback.lift_fst]
    apply pullback.hom_ext
    rw [pullback.lift_snd, pullback.lift_fst, ← hsnd]
    simp [pullback.condition]
    rw [pullback.lift_snd, pullback.lift_snd, ← hsnd]
    simp

section

variable {T : Type*} [Category T] (P Q : MorphismProperty T) [Q.IsMultiplicative] [Q.RespectsIso]
variable {X Y Z : T} (f : X ⟶ Z) (g : Y ⟶ Z)
variable [HasPullbacks T] [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]

noncomputable
def _root_.CategoryTheory.IsPullback.arrowMkSndIso
    {C : Type*} [Category C] {P X Y Z : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {P' : C} {fst' : P' ⟶ X} {snd' : P' ⟶ Y} (h : IsPullback fst snd f g)
    (h' : IsPullback fst' snd' f g) :
    Arrow.mk snd ≅ Arrow.mk snd' :=
  Arrow.isoMk (h.isoIsPullback _ _ h') (Iso.refl _) (by simp)

noncomputable
def _root_.CategoryTheory.IsPullback.arrowMkFstIso
    {C : Type*} [Category C] {P X Y Z : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {P' : C} {fst' : P' ⟶ X} {snd' : P' ⟶ Y} (h : IsPullback fst snd f g)
    (h' : IsPullback fst' snd' f g) :
    Arrow.mk fst ≅ Arrow.mk fst' :=
  Arrow.isoMk (h.isoIsPullback _ _ h') (Iso.refl _) (by simp)

noncomputable
def _root_.CategoryTheory.MorphismProperty.Over.pullbackCondition :
    Over.pullback P Q f ⋙ Over.pullback P Q (pullback.fst f g) ≅
        Over.pullback P Q g ⋙ Over.pullback P Q (pullback.snd f g) :=
  (MorphismProperty.Over.pullbackComp _ _).symm ≪≫
    MorphismProperty.Over.pullbackCongr pullback.condition ≪≫
    MorphismProperty.Over.pullbackComp _ _

lemma _root_.CategoryTheory.MorphismProperty.Over.colimit_post_pullback
  {J : Type*} [Category J] (D : J ⥤ P.Over Q Z) [HasColimit D]
  [HasColimit (D ⋙ Over.pullback P Q f)]
  [HasColimit ((D ⋙ Over.pullback P Q f) ⋙ Over.pullback P Q (pullback.fst f g))]
  [HasColimit (D ⋙ MorphismProperty.Over.pullback P Q g)]
  [HasColimit ((D ⋙ MorphismProperty.Over.pullback P Q g) ⋙
    MorphismProperty.Over.pullback P Q (pullback.snd f g))]
  [HasColimit (D ⋙ MorphismProperty.Over.pullback P Q f ⋙
    MorphismProperty.Over.pullback P Q (pullback.fst f g))] :
    colimit.post (D ⋙ Over.pullback P Q f) (Over.pullback P Q (pullback.fst f g)) ≫
    (Over.pullback P Q (pullback.fst f g)).map (colimit.post D (Over.pullback P Q f)) =
    (HasColimit.isoOfNatIso
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft D (Over.pullbackCondition P Q f g) ≪≫
        (Functor.associator _ _ _).symm)).hom ≫
      colimit.post (D ⋙ Over.pullback P Q g) _ ≫
      (MorphismProperty.Over.pullback P Q (pullback.snd f g)).map
        (colimit.post D (MorphismProperty.Over.pullback P Q g)) ≫
      ((Over.pullbackCondition P Q f g).app (colimit D)).inv := by
  simp only [colimit.post_post, Functor.comp_obj, Iso.app_inv]
  apply colimit.hom_ext
  intro j
  simp only [Functor.comp_obj, colimit.ι_post, Functor.comp_map, HasColimit.isoOfNatIso_ι_hom_assoc,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Category.comp_id, Category.id_comp, colimit.ι_post_assoc]
  rw [← Functor.map_comp_assoc, colimit.ι_post, ← Functor.comp_map, ← Functor.comp_map]
  rw [NatTrans.naturality]
  simp

/-- If `F` is naturally isomorphic to `F'` they induce isomorphic `colimit.post` maps. -/
noncomputable
def _root_.CategoryTheory.Limits.colimit.arrowMkPostIsoOfIso {J C D : Type*} [Category J]
    [Category C] [Category D] (K : J ⥤ C) (F F' : C ⥤ D)
    (e : F ≅ F') [HasColimit K] [HasColimit (K ⋙ F)] [HasColimit (K ⋙ F')] :
    Arrow.mk (colimit.post K F) ≅ Arrow.mk (colimit.post K F') :=
  Arrow.isoMk (HasColimit.isoOfNatIso <| Functor.isoWhiskerLeft K e) (e.app _)
    (by apply colimit.hom_ext; simp)

end

section

variable (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]

lemma _root_.AlgebraicGeometry.IsLocalAtTarget.iff_of_openCover_of_over
    {X Y S : Scheme.{u}} [X.Over S] [Y.Over S]
    (f : X ⟶ Y) [f.IsOver S] (𝒰 : S.OpenCover) :
    P f ↔ ∀ i : 𝒰.I₀,
      P (pullback.map (X ↘ S) (𝒰.f i) (Y ↘ S) (𝒰.f i) f (𝟙 _) (𝟙 _) (by simp) (by simp)) := by
  have heq (i : 𝒰.I₀) :
      dsimp% pullback.snd f ((𝒰.pullback₁ (Y ↘ S)).f i) =
      (pullbackRightPullbackFstIso _ _ _).hom ≫ (pullback.congrHom (by simp) rfl).hom ≫
      pullback.map (X ↘ S) (𝒰.f i) (Y ↘ S) (𝒰.f i) f (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [pullback.condition]
  refine ⟨fun hf i ↦ ?_, fun H ↦ ?_⟩
  · have : P (pullback.snd f ((𝒰.pullback₁ (Y ↘ S)).f i)) :=
      IsZariskiLocalAtTarget.of_isPullback (.of_hasPullback _ _) hf
    dsimp at this
    rwa [heq, P.cancel_left_of_respectsIso, P.cancel_left_of_respectsIso] at this
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := P) (𝒰.pullback₁ (Y ↘ S))]
    intro i
    dsimp [Scheme.Cover.pullbackHom]
    rw [heq, P.cancel_left_of_respectsIso, P.cancel_left_of_respectsIso]
    exact H i

variable {W Q : MorphismProperty Scheme.{u}} [Q.IsMultiplicative]
variable [W.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]

variable {P} in
lemma _root_.AlgebraicGeometry.IsLocalAtTarget.left_iff_of_openCover
    {S : Scheme.{u}} {X Y : W.Over Q S} {f : X ⟶ Y} (𝒰 : S.OpenCover) :
    P f.left ↔ ∀ i : 𝒰.I₀,
      P ((MorphismProperty.Over.pullback W Q (𝒰.f i)).map f).left :=
  AlgebraicGeometry.IsLocalAtTarget.iff_of_openCover_of_over ..

end

nonrec theorem preservesFiniteColimits_pullback (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) (hQe : RingHom.HasEqualizers Q)
    [(RingHom.toMorphismProperty Q).IsStableUnderCobaseChange]
    [∀ (R S : CommRingCat.{u}) (f : R ⟶ S), PreservesFiniteLimits
      (Under.pushout (RingHom.toMorphismProperty Q) ⊤ f)]
    {Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (Over.pullback P ⊤ f) := by
  have (S : Scheme.{u}) : HasFiniteColimits (P.Over ⊤ S) := hasFiniteColimits P hQi hQp hQe
  constructor
  intro J _ _
  constructor
  intro D
  suffices h : IsIso (colimit.post D (MorphismProperty.Over.pullback P ⊤ f)).left by
    have : IsIso (colimit.post D (MorphismProperty.Over.pullback P ⊤ f)) := by
      convert isIso_of_reflects_iso _ (Over.forget P ⊤ X ⋙ Over.forget X)
      exact h
    apply preservesColimit_of_isIso_post
  show isomorphisms Scheme.{u} _
  wlog H : (∃ R, Y = Spec R) ∧ ∃ S, X = Spec S generalizing X Y D f
  · let 𝒰X : X.OpenCover :=
      (Scheme.OpenCover.affineRefinement (Y.affineCover.pullback₁ f)).openCover
    rw [IsLocalAtTarget.left_iff_of_openCover (P := isomorphisms Scheme) 𝒰X]
    intro i
    let uᵢ : Y.affineCover.X i.1 ⟶ Y := Y.affineCover.f i.1
    have _ : PreservesFiniteColimits (toAffine P X) :=
      preservesFiniteColimits_toAffine P hQi hQp hQe
    have _ : PreservesFiniteColimits (toAffine P Y) :=
      preservesFiniteColimits_toAffine P hQi hQp hQe
    rw [← cancel_left_of_respectsIso (isomorphisms Scheme)
      (colimit.post (D ⋙ Over.pullback P ⊤ f) (Over.pullback P ⊤ (𝒰X.f i))).left]
    erw [← MorphismProperty.Comma.comp_left]
    simp only [MorphismProperty.Over.pullback_obj_left, MorphismProperty.Over.pullback_obj_hom,
      colimit.post_post]
    have heq : 𝒰X.f i = (Scheme.OpenCover.fromAffineRefinement _).h₀ i ≫ pullback.fst f uᵢ := by
      convert (Scheme.OpenCover.fromAffineRefinement (Y.affineCover.pullback₁ f)).w₀ i
    let aux : 𝒰X.X i ⟶ Y.affineCover.X i.fst :=
      (Scheme.OpenCover.fromAffineRefinement _).h₀ i ≫ pullback.snd f uᵢ
    let natiso :
        Over.pullback P ⊤ f ⋙ Over.pullback P ⊤ (𝒰X.f i) ≅
          Over.pullback P ⊤ uᵢ ⋙
            MorphismProperty.Over.pullback P ⊤
              aux :=
              -- ((Scheme.OpenCover.fromAffineRefinement _).h₀ i ≫ pullback.snd f uᵢ) :=
      (MorphismProperty.Over.pullbackComp _ _).symm ≪≫
        MorphismProperty.Over.pullbackCongr
        (by rw [Category.assoc, ← pullback.condition, heq, Category.assoc]) ≪≫
        (MorphismProperty.Over.pullbackComp _ _)
    let e := colimit.arrowMkPostIsoOfIso D _ _ natiso
    have : IsIso ((colimit.post D
        (Over.pullback P ⊤ f ⋙ MorphismProperty.Over.pullback P ⊤ (𝒰X.f i)))) := by
      show isomorphisms _ _
      rw [(isomorphisms _).arrow_mk_iso_iff e, ← colimit.post_post,
        (isomorphisms _).cancel_right_of_respectsIso]
      convert isIso_of_reflects_iso _ (Over.forget P ⊤ _ ⋙ Over.forget _)
      exact this _ ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
    simp only [isomorphisms.iff]
    infer_instance
  obtain ⟨⟨R, rfl⟩, ⟨S, rfl⟩⟩ := H
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have : PreservesColimitsOfShape J (MorphismProperty.Over.pullback P ⊤ (Spec.map φ)) := by
    rw [preservesColimitsOfShape_pullback_iff_preservesLimitsOfShape _ hQi]
    infer_instance
  simp only [isomorphisms.iff]
  infer_instance

end AffineAnd

end AlgebraicGeometry
