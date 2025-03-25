/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Category.Ring.Under.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Pi1.Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Category of schemes affine over an affine base

-/

universe t u

noncomputable section

open CategoryTheory Limits Opposite TensorProduct

section

def CategoryTheory.Limits.coneToFan {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {ι : Type*} (f : ι → C) :
    Cone (Discrete.functor f ⋙ F) ⥤ Fan (fun i ↦ F.obj (f i)) where
  obj c := Fan.mk c.pt (fun i ↦ c.π.app ⟨i⟩)
  map {c d} f := { hom := f.hom }

def CategoryTheory.Limits.coneEquivFan {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {ι : Type*} (f : ι → C) :
    Cone (Discrete.functor f ⋙ F) ≌ Fan (fun i ↦ F.obj (f i)) where
  functor := {
    obj := fun c ↦ Fan.mk c.pt (fun i ↦ c.π.app ⟨i⟩)
    map := fun f ↦ { hom := f.hom }
  }
  inverse := {
    obj := fun c ↦ {
        pt := c.pt
        π := Discrete.natTrans c.π.app
      }
    map := fun f ↦ { hom := f.hom }
  }
  unitIso := eqToIso rfl
  counitIso := eqToIso rfl

def CategoryTheory.Limits.preservesLimitsOfShapeDiscrete {C D J : Type*} [Category C] [Category D]
    (F : C ⥤ D) [∀ (f : J → C), PreservesLimit (Discrete.functor f) F] :
    PreservesLimitsOfShape (Discrete J) F where
  preservesLimit :=
      preservesLimit_of_iso_diagram F (Discrete.natIsoFunctor).symm

end

section

variable {C : Type*} [Category C]

instance MorphismProperty.top_isStableUnderBaseChange :
    (⊤ : MorphismProperty C).IsStableUnderBaseChange where
  of_isPullback _ _ := trivial

instance (P : MorphismProperty C) : (⊤ : MorphismProperty C).HasOfPostcompProperty P where
  of_postcomp _ _ _ _ := trivial

end

section

variable {C : Type*} [Category C] (X : C)

def Over.opToUnderOp : Over (op X) ⥤ (Under X)ᵒᵖ where
  obj Y := ⟨Under.mk Y.hom.unop⟩
  map {Z Y} f := ⟨Under.homMk (f.left.unop) (by dsimp; rw [← unop_comp, Over.w])⟩

def Under.opToOverOp : (Under X)ᵒᵖ ⥤ Over (op X) where
  obj Y := Over.mk (Y.unop.hom.op)
  map {Z Y} f := Over.homMk f.unop.right.op <| by
    dsimp
    rw [← Under.w f.unop, op_comp]

def Over.equivUnderOp : Over (op X) ≌ (Under X)ᵒᵖ where
  functor := Over.opToUnderOp X
  inverse := Under.opToOverOp X
  unitIso := eqToIso rfl
  counitIso := eqToIso rfl

end

section

namespace CategoryTheory.Limits

variable {C D J : Type*} [Category C] [Category D] [Category J] (F : C ⥤ D)
  (K : J ⥤ C)

variable {K} in
def coconeHomOp {c c' : Cocone K} (f : c ⟶ c') : c'.op ⟶ c.op where
  hom := (f.hom).op
  w j := by simp [← op_comp]

variable {K} in
def coneHomOp {c c' : Cone K} (f : c ⟶ c') : c'.op ⟶ c.op where
  hom := f.hom.op
  w j := by simp [← op_comp]

variable {K} in
def coconeHomUnop {c c' : Cocone K} (f : c.op ⟶ c'.op) : c' ⟶ c where
  hom := f.hom.unop
  w j := by simpa using congrArg Quiver.Hom.unop (f.w ⟨j⟩)

variable {K} in
def coneHomUnop {c c' : Cone K} (f : c.op ⟶ c'.op) : c' ⟶ c where
  hom := f.hom.unop
  w j := by simpa using congrArg Quiver.Hom.unop (f.w ⟨j⟩)

def opOpCoconeEquiv : Cocone K ≌ Cocone K.op.op where
  functor := {
      obj := fun c ↦ c.op.op
      map := fun {c c'} f ↦ coneHomOp (coconeHomOp f)
    }
  inverse := {
      obj := fun c ↦ c.unop.unop
      map := fun {c c'} f ↦ coconeHomUnop (coneHomUnop f)
    }
  unitIso := eqToIso rfl
  counitIso := eqToIso rfl

variable {K F} in
def isColimitOfIsLimitMapOp {c : Cocone K} (h : IsLimit (F.op.mapCone c.op)) :
    IsColimit (F.mapCocone c) :=
  IsColimit.ofCoconeEquiv (opOpCoconeEquiv (K ⋙ F)) h.op

def preservesColimitOfOp [PreservesLimit K.op F.op] :
    PreservesColimit K F where
  preserves {_} hc := ⟨isColimitOfIsLimitMapOp (isLimitOfPreserves F.op hc.op)⟩

def preservesColimitsOfShapeOfOp [PreservesLimitsOfShape Jᵒᵖ F.op] :
    PreservesColimitsOfShape J F where
  preservesColimit {K} := preservesColimitOfOp F K

end CategoryTheory.Limits

end

namespace AlgebraicGeometry

section

@[reassoc]
lemma Scheme.comp_app_top {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).app ⊤ = g.app ⊤ ≫ f.app ⊤ :=
  rfl

end

section

variable {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine S] {f : X ⟶ S} {g : Y ⟶ S}

lemma Γ_isPushout {P : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} (h : IsPullback fst snd f g) :
    IsPushout (f.app ⊤) (g.app ⊤) (fst.app ⊤) (snd.app ⊤) := by
  haveI : IsAffine (pullback f g) := inferInstance
  let iso : P ≅ pullback f g := h.isoPullback
  haveI : IsAffine P := isAffine_of_isIso iso.hom
  let h' : IsPullback (AffineScheme.ofHom fst) (AffineScheme.ofHom snd)
      (AffineScheme.ofHom f) (AffineScheme.ofHom g) := by
    apply IsPullback.of_map (F := AffineScheme.forgetToScheme) h.w
    exact h
  have h'' := AffineScheme.Γ.rightOp.map_isPullback h'
  have h2 := h''.unop
  exact h2.flip

variable (f g)

def ΓpullbackIsoPushout : Γ(pullback f g, ⊤) ≅ pushout (f.app ⊤) (g.app ⊤) :=
  IsPushout.isoPushout (Γ_isPushout (f := f) (g := g) <| IsPullback.of_hasPullback f g)

@[reassoc (attr := simp)]
def inl_ΓpullbackIsoPushout_inv :
    pushout.inl (f.app ⊤) (g.app ⊤) ≫ (ΓpullbackIsoPushout f g).inv = (pullback.fst f g).app ⊤ := by
  simp [ΓpullbackIsoPushout]

@[reassoc (attr := simp)]
def inr_ΓpullbackIsoPushout_inv :
    pushout.inr (f.app ⊤) (g.app ⊤) ≫ (ΓpullbackIsoPushout f g).inv = (pullback.snd f g).app ⊤ := by
  simp [ΓpullbackIsoPushout]

@[reassoc (attr := simp)]
def app_fst_ΓpullbackIsoPushout_hom :
     (pullback.fst f g).app ⊤ ≫ (ΓpullbackIsoPushout f g).hom =
        pushout.inl (f.app ⊤) (g.app ⊤) := by
  simp [ΓpullbackIsoPushout]

@[reassoc (attr := simp)]
def app_snd_ΓpullbackIsoPushout_hom :
     (pullback.snd f g).app ⊤ ≫ (ΓpullbackIsoPushout f g).hom =
        pushout.inr (f.app ⊤) (g.app ⊤) := by
  simp [ΓpullbackIsoPushout]

end

variable (S : Scheme.{u}) (A : CommRingCat.{u})

section General

def Over.Spec : Over (op A) ⥤ Over (Spec A) :=
  Over.post Scheme.Spec

def Over.Γ : (Over S)ᵒᵖ ⥤ Under Γ(S, ⊤) where
  obj X := Under.mk (X.unop.hom.app ⊤)
  map {X Y} f :=
    Under.homMk (f.unop.left.app ⊤) <| by
      dsimp
      erw [← Scheme.comp_app]
      rw [Over.w]

end General

/-- The category of affine morphisms with target `S`. -/
def Affine : Type _ := MorphismProperty.Over @IsAffineHom ⊤ S

variable {S} in
abbrev Affine.mk {X : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] : Affine S :=
  MorphismProperty.Over.mk ⊤ f inferInstance

instance : Category (Affine S) :=
  inferInstanceAs <| Category (MorphismProperty.Over @IsAffineHom ⊤ S)

instance (X : Affine S) : IsAffineHom X.hom := X.prop

namespace Affine

@[simps! map_right obj_hom]
def Γ : (Affine S)ᵒᵖ ⥤ Under Γ(S, ⊤) :=
  (MorphismProperty.Over.forget @IsAffineHom ⊤ S).op ⋙ Over.Γ S

section

variable {S} {T : Scheme.{u}} (f : T ⟶ S)

abbrev pullback : Affine S ⥤ Affine T :=
  MorphismProperty.Over.pullback _ _ f

abbrev map [IsAffineHom f] : Affine T ⥤ Affine S :=
  MorphismProperty.Over.map ⊤ ‹IsAffineHom f›

abbrev mapPullbackAdjunction [IsAffineHom f] : map f ⊣ pullback f :=
  MorphismProperty.Over.mapPullbackAdj _ _ f _ trivial

instance [IsAffineHom f] : (map f).IsLeftAdjoint :=
  ⟨pullback f, ⟨mapPullbackAdjunction f⟩⟩

instance [IsAffineHom f] : (pullback f).IsRightAdjoint :=
  ⟨map f, ⟨mapPullbackAdjunction f⟩⟩

end

section AffineBase

variable [IsAffine S]

instance (X : Affine S) : IsAffine ((Functor.fromPUnit S).obj X.right) := ‹IsAffine S›

instance (X : Affine S) : IsAffine X.left := isAffine_of_isAffineHom X.hom

instance (X : Affine S) : IsAffine ((𝟭 Scheme).obj X.left) := inferInstanceAs <| IsAffine X.left

def toAffine : Affine S ⥤ Over (AffineScheme.mk S inferInstance) where
  obj X := Over.mk (AffineScheme.ofHom X.hom)
  map {X Y} f := Over.homMk (AffineScheme.ofHom f.left) (Over.w f.1)

def fromAffine : Over (AffineScheme.mk S inferInstance) ⥤ Affine S where
  obj X := Affine.mk X.hom
  map {X Y} f := MorphismProperty.Over.homMk f.left (Over.w f)

lemma toAffine_fromAffine : toAffine S ⋙ fromAffine S = 𝟭 _ := rfl
lemma fromAffine_toAffine : fromAffine S ⋙ toAffine S = 𝟭 _ := rfl

/-- If `S` is affine, the category of affine morphisms with target `S` is equivalent
to the over category of `S` viewed as affine scheme. -/
def toAffineEquiv : Affine S ≌ Over (AffineScheme.mk S inferInstance) where
  functor := toAffine S
  inverse := fromAffine S
  unitIso := eqToIso _
  counitIso := eqToIso _

instance : (toAffine S).IsEquivalence := (toAffineEquiv S).isEquivalence_functor
instance : (fromAffine S).IsEquivalence := (toAffineEquiv S).isEquivalence_inverse

def Over.AffineΓ : Over (AffineScheme.mk S inferInstance) ⥤ (Under Γ(S, ⊤))ᵒᵖ :=
  Over.post AffineScheme.Γ.rightOp ⋙ (Over.equivUnderOp _).functor

instance : (Over.AffineΓ S).IsEquivalence := inferInstanceAs <|
  (Over.post AffineScheme.Γ.rightOp ⋙ (Over.equivUnderOp _).functor).IsEquivalence

lemma Γ_eq : Γ S = (toAffine S ⋙ Over.AffineΓ S).leftOp := rfl

instance : (Γ S).IsEquivalence :=
  inferInstanceAs <| (toAffine S ⋙ Over.AffineΓ S).leftOp.IsEquivalence

section

variable {T : Scheme.{u}} (f : T ⟶ S) [IsAffine T]

variable {S}

@[simps! hom_right]
def pullbackIsoPushout (X : (Affine S)ᵒᵖ) :
    (Γ T).obj (op ((pullback f).obj X.unop)) ≅
      Under.mk (pushout.inr ((Γ S).obj X).hom (f.app ⊤)) :=
  Under.isoMk (ΓpullbackIsoPushout X.unop.hom f) <| by simp

def pullbackΓIso : (pullback f).op ⋙ Γ T ≅ Γ S ⋙ Under.pushout (f.app ⊤) :=
  NatIso.ofComponents (pullbackIsoPushout f) <| by
    intro X Y g
    ext : 1
    dsimp
    rw [← cancel_epi (ΓpullbackIsoPushout (unop X).hom f).inv]
    simp only [Functor.const_obj_obj, Functor.id_obj, TopologicalSpace.Opens.map_top,
      Iso.inv_hom_id_assoc]
    apply pushout.hom_ext
    · rw [pushout.inl_desc]
      simp only [inl_ΓpullbackIsoPushout_inv_assoc, TopologicalSpace.Opens.map_top]
      rw [← Scheme.comp_app_top_assoc]
      rw [pullback.lift_fst]
      simp
    · simp only [inr_ΓpullbackIsoPushout_inv_assoc, TopologicalSpace.Opens.map_top, colimit.ι_desc,
        Functor.id_obj, Functor.const_obj_obj, Γ_obj_hom, Under.mk_right, Γ_map_right, id_eq,
        PushoutCocone.mk_pt, PushoutCocone.mk_ι_app]
      rw [← Scheme.comp_app_top_assoc]
      rw [pullback.lift_snd]
      simp

end

variable {J : Type t} [Category J] [UnivLE.{t, u}]

instance [IsAffine S] : HasLimitsOfShape J (Affine S)ᵒᵖ :=
  Adjunction.hasLimitsOfShape_of_equivalence (Γ S)

instance hasColimitsOfShape_of_isAffine : HasColimitsOfShape J (Affine S) :=
  Limits.hasColimitsOfShape_of_hasLimitsOfShape_op

variable (T : Scheme.{u}) [IsAffine T] (f : T ⟶ S)

instance [Flat f] : PreservesFiniteLimits (Under.pushout (f.app ⊤)) := by
  apply CommRingCat.Under.preservesFiniteLimits_of_flat (Scheme.Hom.app f ⊤)
  apply HasRingHomProperty.appTop (P := @Flat)
  infer_instance

instance preservesColimitsOfShapePullback [PreservesLimitsOfShape Jᵒᵖ (Under.pushout (f.app ⊤))] :
    PreservesColimitsOfShape J (pullback f) :=
  have : PreservesLimitsOfShape Jᵒᵖ ((pullback f).op ⋙ Γ T) :=
    preservesLimitsOfShape_of_natIso (pullbackΓIso f).symm
  have : PreservesLimitsOfShape Jᵒᵖ (pullback f).op :=
    preservesLimitsOfShape_of_reflects_of_preserves _ (Γ T)
  preservesColimitsOfShapeOfOp (pullback f)

instance [Flat f] : PreservesFiniteColimits (pullback f) where
  preservesFiniteColimits _ := inferInstance

end AffineBase

instance (X : Scheme.{u}) : HasFiniteColimits (Affine X) :=
  sorry

instance {X U : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] [IsAffine U] :
    PreservesFiniteColimits (pullback f) :=
  sorry

instance {X U : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] [IsAffine U] :
    PreservesFiniteColimits (pullback f) :=
  sorry

end Affine

end AlgebraicGeometry
