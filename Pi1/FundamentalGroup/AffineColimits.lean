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
import Pi1.FundamentalGroup.Colimits.Gluing

/-!
# Category of schemes affine over an affine base

-/

universe t u

noncomputable section

open CategoryTheory Limits Opposite TensorProduct

section

namespace CategoryTheory

variable {C : Type*} [Category C] (P Q : MorphismProperty C) [Q.IsMultiplicative]
  [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]

@[simp]
lemma Over.pullbackId_hom_app_left [HasPullbacks C] {X : C} (A : Over X) :
    (CategoryTheory.Over.pullbackId.hom.app A).left = pullback.fst _ _ := by
  simp [Over.pullbackId, Adjunction.id]

@[simp]
lemma Over.pullbackId_inv_app_left [HasPullbacks C] {X : C} (A : Over X) :
    (CategoryTheory.Over.pullbackId.inv.app A).left = pullback.lift (𝟙 _) A.hom (by simp) := by
  apply pullback.hom_ext <;> simp [Over.pullbackId, Adjunction.id]

@[simps!]
def MorphismProperty.Over.pullbackId [HasPullbacks C] (X : C) :
    MorphismProperty.Over.pullback P Q (𝟙 X) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun A ↦ MorphismProperty.Over.isoMk
      (Comma.leftIso (CategoryTheory.Over.pullbackId.app <| A.toComma))
      (by simp [pullback.condition]))

@[reassoc (attr := simp)]
lemma MorphismProperty.Over.pullbackCongr_hom_app_left_snd [HasPullbacks C]
    {X Y : C} {f g : X ⟶ Y} (h : f = g) (A : P.Over Q Y) :
    ((pullbackCongr h).hom.app A).left ≫ pullback.snd _ _ = pullback.snd _ _ := by
  subst h
  simp [pullbackCongr]

def MorphismProperty.Over.pullbackIso [HasPullbacks C] {X Y : C} (e : X ≅ Y) :
    P.Over Q X ≌ P.Over Q Y where
  functor := MorphismProperty.Over.pullback P Q e.inv
  inverse := MorphismProperty.Over.pullback P Q e.hom
  unitIso := (MorphismProperty.Over.pullbackId P Q _).symm ≪≫
    MorphismProperty.Over.pullbackCongr e.hom_inv_id.symm ≪≫
    MorphismProperty.Over.pullbackComp e.hom e.inv
  counitIso :=
    (MorphismProperty.Over.pullbackComp e.inv e.hom).symm ≪≫
    MorphismProperty.Over.pullbackCongr e.inv_hom_id ≪≫
    (MorphismProperty.Over.pullbackId P Q _)
  functor_unitIso_comp A := by
    ext
    simp only [Functor.id_obj, pullback_obj_left, Functor.comp_obj, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.map_comp, Category.assoc, Comma.comp_hom,
      CategoryTheory.Comma.comp_left, pullback_obj_hom, pullback_map_left, pullbackId_inv_app_left,
      pullbackComp_hom_app_left, pullbackComp_inv_app_left, pullbackId_hom_app_left, Comma.id_hom,
      CategoryTheory.Comma.id_left]
    apply pullback.hom_ext
    · simp_rw [← Over.pullback_obj_hom, MorphismProperty.Over.pullbackCongr_hom_app_left_fst]
      simp
    · simp_rw [← Over.pullback_obj_hom, MorphismProperty.Over.pullbackCongr_hom_app_left_fst]
      simp [pullback.condition_assoc]

end CategoryTheory

end

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

variable {P Q : MorphismProperty Scheme.{u}} [Q.IsMultiplicative] [P.IsStableUnderBaseChange]
  [Q.IsStableUnderBaseChange] [P.IsStableUnderComposition]
  [Q.IsStableUnderComposition]
variable {S : Scheme.{u}} {J : Type t} [UnivLE.{t, u}] [Category J] (D : J ⥤ P.Over Q S)
variable (d : ColimitGluingData D)
variable [∀ {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j),
  PreservesColimitsOfShape J (MorphismProperty.Over.map Q (d.hPhom hij))]
variable [∀ (i j : d.ι) (hij : d.ℬ i ≤ d.ℬ j),
  PreservesColimitsOfShape J (MorphismProperty.Over.pullback P Q (S.homOfLE hij))]
variable [IsLocalAtTarget P]

def ColimitGluingData.mapCoconePullback (i : d.ι) :
    (MorphismProperty.Over.pullback P Q (d.ℬ i).ι).mapCocone d.gluedCocone ≅ d.c i := by
  refine Cocones.ext ?_ ?_
  · exact MorphismProperty.Comma.isoFromComma (d.gluingData.glued.isoPullback i)
  · intro j
    ext : 1
    rw [← cancel_mono (d.gluingData.glued.ι i)]
    simp only [Functor.comp_obj, MorphismProperty.Over.pullback_obj_left, Functor.mapCocone_pt,
      Functor.const_obj_obj, Functor.mapCocone_ι_app, RelativeGluingData.Glued.isoPullback,
      gluingData_f, Over.pullback_obj_left, Over.mk_left, Over.mk_hom,
      MorphismProperty.Comma.isoFromComma_hom, MorphismProperty.Comma.comp_hom,
      MorphismProperty.Comma.homFromCommaOfIsIso_hom, Comma.comp_left,
      MorphismProperty.Over.pullback_map_left, Over.isoMk_hom_left, Iso.trans_hom, Category.assoc]
    conv_lhs => rw [← RelativeGluingData.Glued.iso_inv_ι]
    rw [Iso.hom_inv_id_assoc]
    simp only [pullbackRestrictIsoRestrict_hom_ι]
    erw [pullback.lift_fst]
    apply componentOpenCover_map_gluedCoconeι

end

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
  haveI : IsAffine P := .of_isIso iso.hom
  let h' : IsPullback (AffineScheme.ofHom fst) (AffineScheme.ofHom snd)
      (AffineScheme.ofHom f) (AffineScheme.ofHom g) := by
    apply IsPullback.of_map (F := AffineScheme.forgetToScheme) h.w
    exact h
  have h'' := AffineScheme.Γ.rightOp.map_isPullback h'
  have h2 := h''.unop
  exact h2.flip

variable (f g)

def ΓpullbackIsoPushout : Γ(pullback f g, ⊤) ≅ pushout f.appTop g.appTop :=
  IsPushout.isoPushout (Γ_isPushout (f := f) (g := g) <| IsPullback.of_hasPullback f g)

@[reassoc (attr := simp)]
def inl_ΓpullbackIsoPushout_inv :
    pushout.inl f.appTop g.appTop ≫ (ΓpullbackIsoPushout f g).inv = (pullback.fst f g).appTop := by
  simp [ΓpullbackIsoPushout]

@[reassoc (attr := simp)]
def inr_ΓpullbackIsoPushout_inv :
    pushout.inr f.appTop g.appTop ≫ (ΓpullbackIsoPushout f g).inv = (pullback.snd f g).appTop := by
  simp [ΓpullbackIsoPushout]

@[reassoc (attr := simp)]
def app_fst_ΓpullbackIsoPushout_hom :
     (pullback.fst f g).appTop ≫ (ΓpullbackIsoPushout f g).hom =
        pushout.inl f.appTop g.appTop := by
  simp [ΓpullbackIsoPushout]

@[reassoc (attr := simp)]
def app_snd_ΓpullbackIsoPushout_hom :
     (pullback.snd f g).appTop ≫ (ΓpullbackIsoPushout f g).hom =
        pushout.inr f.appTop g.appTop := by
  simp [ΓpullbackIsoPushout]

end

variable (S : Scheme.{u})

section General

variable (A : CommRingCat.{u})

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
  unitIso := Iso.refl _
  counitIso := Iso.refl _

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

section

variable {J : Type t} [UnivLE.{t, u}] [SmallCategory J] [FinCategory J] (D : J ⥤ Affine S)

variable {S} in
def colimitGluingData : ColimitGluingData D where
  ι := S.affineOpens
  ℬ := fun U ↦ U.1
  hℬ := by simpa using isBasis_affine_open S
  hP := inferInstance
  hQ := inferInstance
  c := fun U ↦
    let K : J ⥤ Affine U.1.toScheme :=
      Scheme.Opens.diagram D U.1
    colimit.cocone K
  hc := fun U ↦
    let K : J ⥤ Affine U.1.toScheme :=
      Scheme.Opens.diagram D U.1
    colimit.isColimit K
  hPhom := fun _ ↦ inferInstance
  hQhom := fun _ ↦ trivial
  hQ_trivial := by simp

instance : HasColimit D where
  exists_colimit := by
    haveI {U V : S.affineOpens} (hUV : U.1 ≤ V.1) :
        PreservesColimitsOfShape J (map (S.homOfLE hUV)) :=
      inferInstance
    haveI {U V : S.affineOpens} (hUV : U.1 ≤ V.1) :
        PreservesColimitsOfShape J (pullback (S.homOfLE hUV)) :=
      inferInstance
    use (colimitGluingData D).gluedCocone
    exact (colimitGluingData D).gluedIsColimit

end

instance : HasFiniteColimits (Affine S) where
  out J _ _ := { }

instance {U : Scheme.{u}} (f : U ⟶ S) [IsOpenImmersion f] [IsAffine U] :
    PreservesFiniteColimits (pullback f) := by
  wlog h : ∃ (V : S.Opens) (h : U = V), IsAffineOpen V ∧ h ▸ f = V.ι
  · let V : S.Opens := f.opensRange
    have _ : IsAffineOpen V := isAffineOpen_opensRange f
    let e : U ≅ V := f.isoOpensRange
    have heq : f = e.hom ≫ V.ι := by simp [e, V]
    rw [heq]
    let iso := MorphismProperty.Over.pullbackComp (P := @IsAffineHom) (Q := ⊤) e.hom V.ι
    constructor
    intro J _ _
    let eq : Affine U ≌ Affine V := MorphismProperty.Over.pullbackIso _ _ e
    have heq : pullback e.hom = eq.inverse := rfl
    have _ : PreservesColimitsOfShape J (pullback e.hom) := by
      rw [heq]
      infer_instance
    have _ : IsAffine V := ‹_›
    have _ : PreservesFiniteColimits (pullback V.ι) :=
      this _ _ ⟨_, rfl, isAffineOpen_opensRange f, rfl⟩
    exact preservesColimitsOfShape_of_natIso iso.symm
  obtain ⟨V, rfl, hV, rfl⟩ := h
  constructor
  intro J _ _
  constructor
  intro D
  haveI {U V : S.affineOpens} (hUV : U.1 ≤ V.1) :
      PreservesColimitsOfShape J (map (S.homOfLE hUV)) :=
    inferInstance
  haveI {U V : S.affineOpens} (hUV : U.1 ≤ V.1) :
      PreservesColimitsOfShape J (pullback (S.homOfLE hUV)) :=
    inferInstance
  have hc := (colimitGluingData D).gluedIsColimit
  apply CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone hc
  let iso := (colimitGluingData D).mapCoconePullback D ⟨V, hV⟩
  exact ((colimitGluingData D).hc ⟨V, hV⟩).ofIsoColimit iso.symm

end Affine

end AlgebraicGeometry
