/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Pi1.Mathlib.AlgebraicGeometry.RelativeGluing
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Gluing colimits

-/

suppress_compilation

universe u v

open CategoryTheory Limits MulAction

section

variable {C: Type*} [Category C] [HasPullbacks C]

def Over.pullbackCongr {X Y : C} {f g : X ⟶ Y} (h : f = g) :
    Over.pullback f ≅ Over.pullback g :=
  NatIso.ofComponents (fun A ↦ eqToIso (by rw [h]))

@[reassoc (attr := simp)]
lemma Over.pullbackCongr_fst {X Y : C} {f g : X ⟶ Y} (h : f = g) (A : Over Y) :
    ((Over.pullbackCongr h).hom.app A).left ≫ pullback.fst A.hom g = pullback.fst A.hom f := by
  subst h
  simp [pullbackCongr]

@[reassoc (attr := simp)]
lemma Over.pullbackComp_fst_fst {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (A : Over Z) :
    ((Over.pullbackComp f g).hom.app A).left ≫
      pullback.fst (pullback.snd A.hom g) f ≫ pullback.fst A.hom g =
        pullback.fst A.hom (f ≫ g) := by
  simp only [Over.pullback_obj_left, Functor.id_obj, Functor.comp_obj, Over.pullback_obj_hom,
    Over.pullbackComp, Over.mapComp, conjugateIsoEquiv_apply_hom, Iso.symm_hom, eqToIso.inv,
    conjugateEquiv_apply_app, Adjunction.comp_unit_app, Over.mapPullbackAdj_unit_app,
    Over.map_obj_left, Over.map_obj_hom, Functor.const_obj_obj, eqToHom_app, Functor.comp_map,
    Over.mapPullbackAdj_counit_app, Category.assoc, Over.comp_left, Over.homMk_left,
    Over.pullback_map_left, Over.eqToHom_left, eqToHom_refl, Category.comp_id, limit.lift_π_assoc,
    id_eq, PullbackCone.mk_pt, cospan_left, PullbackCone.mk_π_app, limit.lift_π, Category.id_comp]

end

namespace AlgebraicGeometry

section

lemma _root_.AlgebraicGeometry.opensRange_homOfLE {X : Scheme.{u}} {U U' : X.Opens}
    (hUU' : U ≤ U') :
    (X.homOfLE hUU').opensRange = U'.ι ⁻¹ᵁ U := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe]
    show ((X.homOfLE hUU').base y).val ∈ U
    simp
  · intro hx
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe] at hx
    simp only [Scheme.Hom.coe_opensRange, Set.mem_range]
    use ⟨x.val, hx⟩
    apply Subtype.ext
    simp

/-- -/
def _root_.AlgebraicGeometry.pullbackHomOfLEIso' {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsOpenImmersion g] :
    (f ⁻¹ᵁ g.opensRange).toScheme ≅ pullback f g :=
  ((Comma.fst _ _).mapIso (morphismRestrictOpensRange f g))

@[reassoc (attr := simp)]
lemma _root_.AlgebraicGeometry.pullbackHomOfLEIso'_hom_fst {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsOpenImmersion g] :
    (pullbackHomOfLEIso' f g).hom ≫ pullback.fst _ _ = (f ⁻¹ᵁ Scheme.Hom.opensRange g).ι := by
  simp only [pullbackHomOfLEIso', morphismRestrictOpensRange]
  rw [← cancel_epi (pullbackRestrictIsoRestrict f (Scheme.Hom.opensRange g)).hom]
  simp

def _root_.AlgebraicGeometry.pullbackHomOfLEIso {X Y : Scheme.{u}} {U U' : Y.Opens}
    (hUU' : U ≤ U') (f : X ⟶ U') :
    (f ⁻¹ᵁ U'.ι ⁻¹ᵁ U).toScheme ≅ pullback f (Y.homOfLE hUU') :=
  X.isoOfEq (by rw [opensRange_homOfLE]) ≪≫ pullbackHomOfLEIso' f (Y.homOfLE hUU')

end

section

variable {X : Scheme.{u}}

/-- A directed open cover. -/
structure Scheme.DirectedOpenCover extends X.OpenCover where
  preorder : LE J := by infer_instance
  trans {i j : J} (hij : i ≤ j) : obj i ⟶ obj j
  w {i j : J} (hij : i ≤ j) : trans hij ≫ map j = map i
  directed {i j : J} (x : (pullback (map i) (map j)).carrier) :
    ∃ (k : J) (hki : k ≤ i) (hkj : k ≤ j) (y : obj k),
      (pullback.lift (trans hki) (trans hkj) (by simp [w])).base y = x
  trans_isOpenImmersion {i j : J} (hij : i ≤ j) : IsOpenImmersion (trans hij) :=
    by infer_instance

attribute [instance] Scheme.DirectedOpenCover.preorder
  Scheme.DirectedOpenCover.trans_isOpenImmersion

attribute [reassoc (attr := simp)] Scheme.DirectedOpenCover.w

def Scheme.DirectedOpenCover.pullbackCover (𝒰 : X.DirectedOpenCover) {Y : Scheme.{u}} (f : Y ⟶ X) :
    Y.DirectedOpenCover where
  __ := 𝒰.toCover.pullbackCover f
  preorder := inferInstanceAs <| LE 𝒰.J
  trans {i j} hij := pullback.map f (𝒰.map i) f (𝒰.map j) (𝟙 _) (𝒰.trans hij) (𝟙 _)
    (by simp) (by simp)
  w {i j} hij := by simp
  directed {i j} x := by
    dsimp at i j x ⊢
    let zl := (pullback.fst (pullback.fst f (𝒰.map i))
      (pullback.fst f (𝒰.map j))).base x
    let y : Y := (pullback.fst f (𝒰.map i)).base zl
    let o : X := f.base y
    let a : pullback (pullback.fst f (𝒰.map i)) (pullback.fst f (𝒰.map j)) ⟶
        pullback (𝒰.map i) (𝒰.map j) :=
      pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _ ≫ pullback.snd _ _)
        (by
          rw [Category.assoc, Category.assoc]
          rw [← pullback.condition, pullback.condition_assoc, pullback.condition])
    let z : (pullback (𝒰.map i) (𝒰.map j)).carrier := a.base x
    obtain ⟨k, hki, hkj, yk, hyk⟩ := 𝒰.directed z
    use k, hki, hkj
    have ho : o ∈ (𝒰.map k).opensRange := by
      use yk
      apply_fun (pullback.fst (𝒰.map i) (𝒰.map j)).base at hyk
      rw [← Scheme.comp_base_apply, pullback.lift_fst] at hyk
      apply_fun (𝒰.map i).base at hyk
      rw [← Scheme.comp_base_apply, 𝒰.w] at hyk
      rw [hyk]
      simp only [z, a]
      rw [← Scheme.comp_base_apply]
      rw [← Scheme.comp_base_apply, pullback.lift_fst_assoc]
      simp only [o, y, zl]
      rw [Category.assoc, ← pullback.condition, Scheme.comp_base_apply, Scheme.comp_base_apply]
    have hy : y ∈ f ⁻¹ᵁ (𝒰.map k).opensRange := ho
    let iso := pullbackHomOfLEIso' f (𝒰.map k)
    use iso.hom.base ⟨y, hy⟩
    have hinj : Function.Injective
        (pullback.fst (pullback.fst f (𝒰.map i)) (pullback.fst f (𝒰.map j))).base :=
      (Scheme.Hom.isOpenEmbedding _).injective
    apply hinj
    rw [← Scheme.comp_base_apply, pullback.lift_fst]
    have hinj : Function.Injective ((pullback.fst f (𝒰.map i))).base :=
      (Scheme.Hom.isOpenEmbedding _).injective
    apply hinj
    rw [← Scheme.comp_base_apply, pullback.lift_fst]
    dsimp
    rw [← Scheme.comp_base_apply]
    simp only [iso, pullbackHomOfLEIso'_hom_fst]
    rfl

@[simps map]
def Scheme.DirectedOpenCover.intersection (𝒰 : X.DirectedOpenCover) (i j : 𝒰.J) :
    (pullback (𝒰.map i) (𝒰.map j)).OpenCover where
  J := { k : 𝒰.J | k ≤ i ∧ k ≤ j }
  obj k := 𝒰.obj k
  map k := pullback.lift (𝒰.trans k.2.1) (𝒰.trans k.2.2) (by simp)
  f x := ⟨(𝒰.directed x).choose, (𝒰.directed x).choose_spec.choose,
    (𝒰.directed x).choose_spec.choose_spec.choose⟩
  covers x := (𝒰.directed x).choose_spec.choose_spec.choose_spec
  map_prop k := by
    apply @IsOpenImmersion.of_comp _ _ _ _ (pullback.fst _ _) ?_ ?_
    · apply IsOpenImmersion.pullback_fst_of_right
    · simp only [Set.coe_setOf, Set.mem_setOf_eq, limit.lift_π, PullbackCone.mk_pt,
        PullbackCone.mk_π_app]
      infer_instance

/-- -/
def Scheme.DirectedOpenCover.glueMorphisms (𝒰 : X.DirectedOpenCover) {Y : Scheme.{u}}
    (g : ∀ i, 𝒰.obj i ⟶ Y) (h : ∀ {i j : 𝒰.J} (hij : i ≤ j), 𝒰.trans hij ≫ g j = g i) :
    X ⟶ Y :=
  𝒰.toCover.glueMorphisms g <| by
    intro i j
    apply (𝒰.intersection i j).hom_ext
    intro k
    simp [h]

@[reassoc (attr := simp)]
lemma Scheme.DirectedOpenCover.map_glueMorphisms (𝒰 : X.DirectedOpenCover) {Y : Scheme.{u}}
    (g : ∀ i, 𝒰.obj i ⟶ Y) (h : ∀ {i j : 𝒰.J} (hij : i ≤ j), 𝒰.trans hij ≫ g j = g i) (i : 𝒰.J) :
    𝒰.map i ≫ 𝒰.glueMorphisms g h = g i := by
  simp [glueMorphisms]

def Scheme.DirectedOpenCover.glueMorphismsOver {S : Scheme.{u}} {X : Over S}
    (𝒰 : X.left.DirectedOpenCover) {Y : Over S}
    (g : ∀ i, 𝒰.obj i ⟶ Y.left)
    (h : ∀ {i j : 𝒰.J} (hij : i ≤ j), 𝒰.trans hij ≫ g j = g i)
    (w : ∀ i, g i ≫ Y.hom = 𝒰.map i ≫ X.hom) :
    X ⟶ Y :=
  Over.homMk (𝒰.glueMorphisms g h) <| by
    apply 𝒰.hom_ext
    intro i
    simp [w]

@[reassoc (attr := simp)]
lemma Scheme.DirectedOpenCover.map_glueMorphismsOver_left {S : Scheme.{u}} {X : Over S}
    (𝒰 : X.left.DirectedOpenCover) {Y : Over S}
    (g : ∀ i, 𝒰.obj i ⟶ Y.left)
    (h : ∀ {i j : 𝒰.J} (hij : i ≤ j), 𝒰.trans hij ≫ g j = g i)
    (w : ∀ i, g i ≫ Y.hom = 𝒰.map i ≫ X.hom) (i : 𝒰.J) :
    𝒰.map i ≫ (𝒰.glueMorphismsOver g h w).left = g i := by
  simp [glueMorphismsOver]

end

section

variable {S : Scheme.{u}} (d : PreRelativeGluingData S)

namespace PreRelativeGluingData

/-- An alternative definition of `ρres`. -/
def ρres' {i j : d.ι} (hij : d.U i ≤ d.U j) : d.X i ⟶ pullback (d.f j) (S.homOfLE hij) :=
  pullback.lift (d.ρ hij) (d.f i) (d.w hij)

lemma ρres_pullbackHomOfLEIso_hom {i j : d.ι} (hij : d.U i ≤ d.U j) :
    d.ρres hij ≫ (pullbackHomOfLEIso hij _).hom = d.ρres' hij := by
  rw [← cancel_mono (pullback.fst _ _)]
  simp [ρres', pullbackHomOfLEIso]

/-- -/
def ρresIsoρres' {i j : d.ι} (hij : d.U i ≤ d.U j) :
    Arrow.mk (d.ρres hij) ≅ Arrow.mk (d.ρres' hij) :=
  Arrow.isoMk (Iso.refl _) (pullbackHomOfLEIso hij _) (by simp [ρres_pullbackHomOfLEIso_hom])

lemma ρres_isIso_iff_ρres'_isIso {i j : d.ι} (hij : d.U i ≤ d.U j) :
    IsIso (d.ρres hij) ↔ IsIso (d.ρres' hij) := by
  rw [← ρres_pullbackHomOfLEIso_hom]
  refine ⟨fun h ↦ inferInstance,
    fun h ↦ IsIso.of_isIso_comp_right _ (pullbackHomOfLEIso hij (d.f j)).hom⟩

end PreRelativeGluingData

end

section Colimits

open TopologicalSpace

variable {P Q : MorphismProperty Scheme.{u}} [Q.IsMultiplicative]
variable [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]
variable {S : Scheme.{u}}
variable {J : Type*} [Category J] (D : J ⥤ P.Over Q S)

def pullbackDiagram {S' : Scheme.{u}} (f : S' ⟶ S) : J ⥤ P.Over Q S' :=
  D ⋙ MorphismProperty.Over.pullback P Q f

variable {S' : Scheme.{u}} (f : S' ⟶ S)

def Scheme.Opens.diagram (U : S.Opens) : J ⥤ P.Over Q U.toScheme :=
  pullbackDiagram D U.ι

@[simp]
lemma Scheme.Opens.diagram_hom (U : S.Opens) (k : J) :
    ((U.diagram D).obj k).hom = pullback.snd (D.obj k).hom U.ι :=
  rfl

variable [P.IsStableUnderComposition]

def Scheme.diagramo {U U' : S.Opens} (hUU' : U ≤ U') (hPhom : P (S.homOfLE hUU')) :
    J ⥤ P.Over Q U'.toScheme :=
  U.diagram D ⋙ MorphismProperty.Over.map Q hPhom

@[simp]
lemma Scheme.diagramo_hom {U U' : S.Opens} (hUU' : U ≤ U') (hPhom : P (S.homOfLE hUU')) (k : J) :
    ((S.diagramo D hUU' hPhom).obj k).hom = pullback.snd (D.obj k).hom U.ι ≫ S.homOfLE hUU' :=
  rfl

lemma Scheme.diagramo_map_left {U U' : S.Opens} (hUU' : U ≤ U') (hPhom : P (S.homOfLE hUU'))
    {k l : J} (f : k ⟶ l) :
    ((S.diagramo D hUU' hPhom).map f).left =
      pullback.map _ _ _ _ (D.map f).left (𝟙 _) (𝟙 _) (by simp) (by simp) :=
  rfl

structure ColimitGluingData where
  ι : Type u
  ℬ : ι → S.Opens
  hℬ : Opens.IsBasis <| Set.range ℬ
  hP : P.IsStableUnderBaseChange
  hQ : Q.IsStableUnderBaseChange
  c (i : ι) : Cocone ((ℬ i).diagram D)
  hc (i : ι) : IsColimit (c i)
  hPhom {i j : ι} (hij : ℬ i ≤ ℬ j) : P (S.homOfLE hij)
  hQhom {i j : ι} (hij : ℬ i ≤ ℬ j) : Q (S.homOfLE hij)
  hQ_trivial {X Y : Scheme.{u}} (f : X ⟶ Y) : Q f

instance (U : S.Opens) : PreservesColimits (Over.forget U.toScheme) := inferInstance

namespace ColimitGluingData

variable {D} (d : ColimitGluingData D)

def pullbackMap {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j) (T : P.Over Q S) :
    (MorphismProperty.Over.map _ (d.hPhom hij)).obj
        ((MorphismProperty.Over.pullback P Q (d.ℬ i).ι).obj T) ⟶
      (MorphismProperty.Over.pullback P Q (d.ℬ j).ι).obj T :=
  MorphismProperty.Over.homMk
    (pullback.map _ _ _ _ (𝟙 _) (S.homOfLE hij) (𝟙 _) (by simp) (by simp))
    (by simp)
    (d.hQ_trivial _)

@[reassoc (attr := simp)]
lemma pullbackMap_left_fst (s : Cocone D) {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j) :
    (d.pullbackMap hij s.pt).left ≫ pullback.fst s.pt.hom (d.ℬ j).ι =
      pullback.fst s.pt.hom (d.ℬ i).ι := by
  simp [pullbackMap]

def cfo {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j) : Cocone (S.diagramo D hij (d.hPhom hij)) :=
  (MorphismProperty.Over.map _ (d.hPhom hij)).mapCocone (d.c i)

@[simp]
lemma cfo_ι_app_left {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j) (k : J) :
    ((d.cfo hij).ι.app k).left = ((d.c i).ι.app k).left :=
  rfl

def trans {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j) (k : J) :
    (S.diagramo D hij (d.hPhom hij)).obj k ⟶ ((d.ℬ j).diagram D).obj k :=
  MorphismProperty.Over.homMk (pullback.map (D.obj k).hom (d.ℬ i).ι (D.obj k).hom (d.ℬ j).ι (𝟙 _)
      (S.homOfLE hij) (𝟙 _) rfl (by simp)) (by simp)
      (d.hQ_trivial _)

@[reassoc (attr := simp)]
lemma trans_fst {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j) (k : J) :
    (d.trans hij k).left ≫ pullback.fst (D.obj k).hom (d.ℬ j).ι =
      pullback.fst (D.obj k).hom (d.ℬ i).ι := by
  simp [trans]

@[reassoc]
lemma trans_trans {i j k : d.ι} (hij : d.ℬ i ≤ d.ℬ j) (hjk : d.ℬ j ≤ d.ℬ k) (l : J) :
    (d.trans hij l).left ≫ (d.trans hjk l).left = (d.trans (hij.trans hjk) l).left := by
  simp [trans, pullback.map_comp]

@[reassoc (attr := simp)]
lemma diagramo_map_trans_left {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j) {k l : J} (f : k ⟶ l) :
    ((S.diagramo D hij (d.hPhom hij)).map f).left ≫ (d.trans hij l).left =
        (d.trans hij k).left ≫ (((d.ℬ j).diagram D).map f).left := by
  rw [← cancel_mono (pullback.fst (D.obj l).hom (d.ℬ j).ι)]
  simp [Scheme.diagramo_map_left, Scheme.Opens.diagram, pullbackDiagram]

def restrictRestrictIso {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j) :
    (d.ℬ i).diagram D ≅ (d.ℬ j).diagram D ⋙
      MorphismProperty.Over.pullback P Q (S.homOfLE hij) :=
  let iso0 :=
    MorphismProperty.Over.pullbackComp (S.homOfLE hij) (d.ℬ j).ι
  have heq : (d.ℬ i).ι = (S.homOfLE hij) ≫ (d.ℬ j).ι := by rw [Scheme.homOfLE_ι]
  let iso1 : MorphismProperty.Over.pullback P Q (d.ℬ i).ι ≅
      MorphismProperty.Over.pullback P Q (d.ℬ j).ι ⋙
        MorphismProperty.Over.pullback P Q (S.homOfLE hij) :=
    MorphismProperty.Over.pullbackCongr heq ≪≫ iso0
  let iso2 := isoWhiskerLeft D iso1
  let iso3 := Functor.associator D
    (MorphismProperty.Over.pullback P Q (d.ℬ j).ι)
      (MorphismProperty.Over.pullback P Q (S.homOfLE hij))
  iso2 ≪≫ iso3.symm

@[reassoc]
lemma restrictRestrictIso_hom_app_left_fst {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j) (k : J) :
    ((d.restrictRestrictIso hij).hom.app k).left ≫
    pullback.fst (((d.ℬ j).diagram D).obj k).hom (S.homOfLE hij) = (d.trans hij k).left := by
  rw [← cancel_mono (pullback.fst _ _)]
  simp [restrictRestrictIso, Scheme.Opens.diagram, pullbackDiagram]

/-
This is evil!

def hcf (i : d.ι) : IsColimit (d.cf i) :=
  isColimitOfPreserves (Over.forget (d.ℬ i).toScheme) (d.hc i)
-/

variable [∀ {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j),
  PreservesColimitsOfShape J (MorphismProperty.Over.map Q (d.hPhom hij))]

def hcfo {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j) : IsColimit (d.cfo hij) :=
  isColimitOfPreserves (MorphismProperty.Over.map Q (d.hPhom hij)) (d.hc i)

lemma hcfo_desc {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j)
    (s : Cocone ((d.ℬ i).diagram D)) :
    (d.hcfo hij).desc ((MorphismProperty.Over.map Q (d.hPhom hij)).mapCocone s) =
      (MorphismProperty.Over.map Q (d.hPhom hij)).map ((d.hc i).desc s) :=
  preserves_desc_mapCocone _ _ _ _ _

/-
(d.hcfo hij).desc ((Over.map (S.homOfLE hij)).mapCocone
    ((Over.pullback (d.ℬ i).ι).mapCocone s))).left ≫
    (d.pullbackMap hij s.pt).left =
  ((d.hc i).desc ((Over.pullback (d.ℬ i).ι).mapCocone s)).left ≫ (d.pullbackMap hij s.pt).left
-/

--lemma hcfo_hom_ext {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j)

@[reassoc (attr := simp)]
def trans_hom {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j) (k : J) :
    (d.trans hij k).left ≫ (((d.ℬ j).diagram D).obj k).hom =
      (((d.ℬ i).diagram D).obj k).hom ≫ S.homOfLE hij := by
  simp [trans, Scheme.Opens.diagram, pullbackDiagram]

/-
@[reassoc (attr := simp)]
lemma diagramf_map_trans {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j) {k l : J} (f : k ⟶ l) :
    ((d.ℬ i).diagramf D).map f ≫ d.trans hij l = d.trans hij k ≫ ((d.ℬ j).diagramf D).map f := by
  rw [← cancel_mono (pullback.fst (D.obj l).hom (d.ℬ j).ι)]
  simp [Scheme.Opens.diagramf, Scheme.Opens.diagram, pullbackDiagram]
-/

def transitionCocone {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j) :
    Cocone (S.diagramo D hij (d.hPhom hij)) where
  pt := (d.c j).pt
  ι := {
      app := fun k ↦ d.trans hij k ≫ (d.c j).ι.app k
      naturality := fun k l f ↦ by
        simp
        ext : 1
        simp only [MorphismProperty.Comma.comp_hom, Comma.comp_left,
          MorphismProperty.Comma.Hom.hom_left, diagramo_map_trans_left_assoc]
        rw [← MorphismProperty.Comma.comp_left, NatTrans.naturality]
        simp
    }

def transition {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j) :
    (d.cfo hij).pt ⟶ (d.c j).pt :=
  (d.hcfo hij).desc (d.transitionCocone hij)

lemma ι_transition_aux {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j) (k : J) :
    (d.cfo hij).ι.app k ≫ d.transition hij = d.trans hij k ≫ (d.c j).ι.app k :=
  (d.hcfo hij).fac (d.transitionCocone hij) k

/-
TODO: this lemma is extremely slow!
-/
lemma ι_transition {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j) (k : J) :
    ((d.c i).ι.app k).left ≫ (d.transition hij).left =
      (d.trans hij k).left ≫ ((d.c j).ι.app k).left := by
  have : ((d.c i).ι.app k).left = ((d.cfo hij).ι.app k).left := rfl
  rw [this, ← MorphismProperty.Comma.comp_left, ← MorphismProperty.Comma.comp_left,
    ι_transition_aux]

attribute [reassoc] ι_transition

def transitionTransitionAux {i j k : d.ι} (hij : d.ℬ i ≤ d.ℬ j) (hjk : d.ℬ j ≤ d.ℬ k) :
    (MorphismProperty.Over.map Q (d.hPhom hjk)).obj (d.cfo hij).pt ≅
      (d.cfo <| hij.trans hjk).pt :=
  eqToIso <| by
    simp only [cfo, Functor.mapCocone_pt]
    conv_rhs => simp only [← S.homOfLE_homOfLE hij hjk]
    rw [← Functor.comp_obj, ← MorphismProperty.Over.map_comp Q]
    simp

lemma transition_transition {i j k : d.ι} (hij : d.ℬ i ≤ d.ℬ j) (hjk : d.ℬ j ≤ d.ℬ k) :
    (d.transitionTransitionAux hij hjk).inv ≫
      (MorphismProperty.Over.map Q (d.hPhom hjk)).map (d.transition hij) ≫ d.transition hjk =
        d.transition (hij.trans hjk) := by
  apply (d.hcfo (hij.trans hjk)).hom_ext
  intro a
  ext : 1
  simp only [Functor.const_obj_obj, transitionTransitionAux, eqToIso.inv, Over.comp_left,
    cfo_ι_app_left, Over.map_obj_left, Over.eqToHom_left, eqToHom_refl, Over.map_map_left,
    Category.id_comp, ι_transition_assoc, ι_transition, trans_trans_assoc]
  simp [ι_transition, ι_transition_assoc, trans_trans_assoc]

lemma preGluingData_comp_aux {i j k : d.ι} (hij : d.ℬ i ≤ d.ℬ j) (hjk : d.ℬ j ≤ d.ℬ k) :
    (d.transition hij).left ≫ (d.transition hjk).left = (d.transition <| hij.trans hjk).left := by
  rw [← d.transition_transition hij hjk]
  simp [transitionTransitionAux]

@[simps -isSimp]
def preGluingData : PreRelativeGluingData S where
  ι := d.ι
  U := d.ℬ
  hU := d.hℬ
  X i := (d.c i).pt.left
  f i := (d.c i).pt.hom
  ρ hij := (d.transition hij).left
  w hij := (d.transition hij).w
  comp hij hjk := d.preGluingData_comp_aux hij hjk

def ρwQ {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j) :
    (MorphismProperty.Over.map Q (d.hPhom hij)).obj (d.c i).pt ⟶ (d.c j).pt :=
  ⟨d.preGluingData.ρw hij, d.hQ_trivial _, trivial⟩

lemma ρres_isIso_aux {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j) :
    ((d.hc i).map ((MorphismProperty.Over.pullback P Q (S.homOfLE hij)).mapCocone (d.c j))
      (d.restrictRestrictIso hij).hom).left ≫
      pullback.fst (d.c j).pt.hom (S.homOfLE hij) = (d.preGluingData.ρw hij).left := by
  let a := (d.hc i).map
      ((MorphismProperty.Over.pullback P Q (S.homOfLE hij)).mapCocone (d.c j))
    (d.restrictRestrictIso hij).hom
  let a' := (MorphismProperty.Over.map Q (d.hPhom hij)).map a
  have : a'.left = a.left := rfl
  rw [← this]
  let b : (MorphismProperty.Over.map Q (d.hPhom hij)).obj
      ((MorphismProperty.Over.pullback P Q (S.homOfLE hij)).mapCocone (d.c j)).pt ⟶
        (d.c j).pt :=
    MorphismProperty.Over.homMk (pullback.fst (d.c j).pt.hom (S.homOfLE hij))
      (by simp [pullback.condition])
      (by apply Q.pullback_fst; exact d.hQhom hij)
  have : pullback.fst (d.c j).pt.hom (S.homOfLE hij) = b.left := rfl
  rw [this, ← MorphismProperty.Comma.comp_left]
  have : a' ≫ b = d.ρwQ hij := by
    apply (d.hcfo hij).hom_ext
    intro k
    ext : 1
    simp [a', b, a, ρwQ]
    rw [← MorphismProperty.Comma.comp_left_assoc, IsColimit.ι_map]
    simp only [MorphismProperty.Over.pullback_obj_left, Functor.comp_obj, Functor.mapCocone_pt,
      Functor.const_obj_obj, Functor.mapCocone_ι_app, MorphismProperty.Comma.comp_hom,
      Comma.comp_left, Scheme.Opens.diagram_hom, Functor.id_obj,
      MorphismProperty.Comma.Hom.hom_left, MorphismProperty.Over.pullback_map_left, Category.assoc,
      limit.lift_π, id_eq, PullbackCone.mk_pt, PullbackCone.mk_π_app]
    erw [restrictRestrictIso_hom_app_left_fst_assoc]
    rw [← ι_transition]
    rfl
  rw [this]
  rfl

/- This seems to be necessary. -/
variable [∀ (i j : d.ι) (hij : d.ℬ i ≤ d.ℬ j),
  PreservesColimitsOfShape J (MorphismProperty.Over.pullback P Q (S.homOfLE hij))]

instance ρres_isIso {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j) : IsIso (d.preGluingData.ρres hij) := by
  rw [d.preGluingData.ρres_isIso_iff_ρres'_isIso]
  let foo := isColimitOfPreserves
    (MorphismProperty.Over.pullback P Q (S.homOfLE hij)) (d.hc j)
  let bar : (d.c i).pt ≅ _ := (d.hc i).coconePointsIsoOfNatIso foo (d.restrictRestrictIso hij)
  let bar' : (d.c i).pt.left ≅ pullback (d.c j).pt.hom (S.homOfLE hij) :=
    (MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _).mapIso bar
  have : bar'.hom = d.preGluingData.ρres' hij := by
    rw [← cancel_mono (pullback.fst _ _)]
    simp only [Functor.id_obj, Functor.const_obj_obj, PreRelativeGluingData.ρres']
    simp only [Functor.mapCocone_pt, Functor.mapIso_hom, IsColimit.coconePointsIsoOfNatIso_hom,
      Over.forget_map, bar', bar]
    erw [pullback.lift_fst]
    erw [← PreRelativeGluingData.ρw_left, ρres_isIso_aux]
  rw [← this]
  infer_instance

@[simps! -isSimp ρ U]
def gluingData : RelativeGluingData S where
  __ := d.preGluingData
  ρIso := d.ρres_isIso

@[reassoc]
lemma ρwQ_left {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j) :
    (d.ρwQ hij).left = d.gluingData.ρ hij :=
  rfl

@[simp]
lemma gluingData_f (i : d.ι) : d.gluingData.f i = (d.c i).pt.hom := rfl

instance {S : Scheme.{u}} (d : RelativeGluingData S) : LE d.ι where
  le i j := d.U i ≤ d.U j

def _root_.AlgebraicGeometry.RelativeGluingData.directedOpenCover {S : Scheme.{u}}
    (d : RelativeGluingData S) : S.DirectedOpenCover where
  __ := Scheme.OpenCover.mkOfCovers d.ι (fun i ↦ d.U i) (fun i ↦ (d.U i).ι)
    (fun x ↦ by
      obtain ⟨i, hx⟩ := d.exists_mem x
      use i, ⟨x, hx⟩
      rfl)
  preorder := inferInstanceAs <| LE d.ι
  trans {i j} hij := S.homOfLE hij
  w {i j} hij := by erw [S.homOfLE_ι]; rfl
  directed {i j} x := by
    let s : S := (pullback.fst (d.U i).ι (d.U j).ι ≫ (d.U i).ι).base x
    have hsi : s ∈ d.U i := Subtype.property _
    have hsj : s ∈ d.U j := by
      simp only [s]
      rw [pullback.condition]
      apply Subtype.property
    obtain ⟨-, ⟨a, rfl⟩, hz, hle⟩ := Opens.isBasis_iff_nbhd.mp (U := d.U i ⊓ d.U j) d.hU ⟨hsi, hsj⟩
    use a, hle.trans inf_le_left, hle.trans inf_le_right
    use ⟨s, hz⟩
    have : Function.Injective (pullback.fst (d.U i).ι (d.U j).ι).base :=
      (Scheme.Hom.isOpenEmbedding _).injective
    apply this
    erw [← Scheme.comp_base_apply]
    erw [pullback.lift_fst]
    have : Function.Injective (d.U i).ι.base := (Scheme.Hom.isOpenEmbedding _).injective
    apply this
    rw [← Scheme.comp_base_apply]
    simp only [Scheme.homOfLE_ι]
    rfl

def componentOpenCover (k : J) : (D.obj k).left.DirectedOpenCover :=
  d.gluingData.directedOpenCover.pullbackCover (D.obj k).hom

@[simp]
lemma componentOpenCover_trans_ι (i j : d.ι) (hij : d.ℬ i ≤ d.ℬ j) (k) :
    (d.componentOpenCover k).trans hij = (d.trans hij k).left :=
  rfl

variable [IsLocalAtTarget P]

lemma P_gluingData_glued_f : P d.gluingData.glued.f := by
  apply d.gluingData.glued.f_prop
  intro i
  exact (d.c i).pt.prop

def gluedCoconeι (k : J) :
    D.obj k ⟶ MorphismProperty.Over.mk Q d.gluingData.glued.f d.P_gluingData_glued_f where
  toCommaMorphism := (d.componentOpenCover k).glueMorphismsOver
    (fun i ↦ ((d.c i).ι.app k).left ≫ d.gluingData.glued.ι i)
    (by
      intro i j hij
      simp only [Over.mk_left, componentOpenCover_trans_ι, Functor.const_obj_obj]
      rw [← ι_transition_assoc]
      show _ ≫ d.gluingData.ρ hij ≫ _ = _
      simp only [Functor.const_obj_obj, RelativeGluingData.Glued.openCover_ρ_map])
    (by
      intro i
      simp only [Functor.const_obj_obj, MorphismProperty.Over.mk_left, MorphismProperty.Over.mk_hom,
        Category.assoc]
      rw [← d.gluingData.glued.f_ι]
      simp only [gluingData_f]
      simp only [gluingData_U, Over.w_assoc, Functor.const_obj_obj, Scheme.Opens.diagram_hom,
        Functor.id_obj]
      rw [← pullback.condition]
      rfl)
  prop_hom_left := d.hQ_trivial _
  prop_hom_right := trivial

@[reassoc (attr := simp)]
lemma componentOpenCover_map_gluedCoconeι (k : J) (i : d.ι) :
    (d.componentOpenCover k).map i ≫ (d.gluedCoconeι k).left =
      ((d.c i).ι.app k).left ≫ d.gluingData.glued.ι i := by
  simp only [Over.mk_left, gluedCoconeι, Functor.const_obj_obj]
  rw [Scheme.DirectedOpenCover.map_glueMorphismsOver_left]
  -- TODO: why do we have to give the proof again?!
  simp
  intro i j hij
  rw [← ι_transition_assoc]
  show _ ≫ d.gluingData.ρ hij ≫ _ = _
  simp only [Functor.const_obj_obj, RelativeGluingData.Glued.openCover_ρ_map]

def gluedCocone : Cocone D where
  pt := MorphismProperty.Over.mk Q d.gluingData.glued.f d.P_gluingData_glued_f
  ι := {
    app := fun k ↦ d.gluedCoconeι k
    naturality := fun k l f ↦ by
      simp
      ext : 1
      apply (d.componentOpenCover k).hom_ext
      intro (i : d.ι)
      have : (d.componentOpenCover k).map i ≫ (D.map f).left =
          (((d.ℬ i).diagram D).map f).left ≫ (d.componentOpenCover l).map i := by
        simp only [componentOpenCover, Scheme.DirectedOpenCover.pullbackCover,
          Scheme.Cover.pullbackCover_J, Scheme.Cover.pullbackCover_obj,
          Scheme.Cover.pullbackCover_map, Scheme.Opens.diagram, pullbackDiagram,
          Functor.comp_obj, Over.pullback_obj_left, Functor.comp_map, Over.pullback_map_left]
        erw [pullback.lift_fst]
        rfl
      simp
      rw [reassoc_of% this]
      simp
      rw [← MorphismProperty.Comma.comp_left_assoc, (d.c i).w]
  }

@[reassoc (attr := simp)]
lemma componentOpenCover_map_gluedCocone_ι_app (k : J) (i : d.ι) :
    (d.componentOpenCover k).map i ≫ (d.gluedCocone.ι.app k).left =
      ((d.c i).ι.app k).left ≫ d.gluingData.glued.ι i :=
  d.componentOpenCover_map_gluedCoconeι k i

omit [IsLocalAtTarget P] in
lemma aux2 (s : Cocone D) {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j) :
    d.gluingData.ρ hij ≫
    ((d.hc j).desc ((MorphismProperty.Over.pullback P Q (d.ℬ j).ι).mapCocone s)).left =
    ((d.hc i).desc ((MorphismProperty.Over.pullback P Q (d.ℬ i).ι).mapCocone s)).left ≫
      (d.pullbackMap hij s.pt).left := by
  rw [← d.ρwQ_left]
  rw [← MorphismProperty.Comma.comp_left]
  have : d.ρwQ hij ≫
      (d.hc j).desc ((MorphismProperty.Over.pullback P Q (d.ℬ j).ι).mapCocone s) =
        ((d.hcfo hij).desc ((MorphismProperty.Over.map Q (d.hPhom hij)).mapCocone
          ((MorphismProperty.Over.pullback P Q (d.ℬ i).ι).mapCocone s))) ≫
          d.pullbackMap hij s.pt := by
    apply (d.hcfo hij).hom_ext
    intro k
    simp only [Functor.mapCocone_pt, Functor.const_obj_obj, IsColimit.fac_assoc,
      Functor.mapCocone_ι_app]
    ext : 1
    simp only [MorphismProperty.Over.pullback_obj_left, MorphismProperty.Comma.comp_hom,
      Comma.comp_left, MorphismProperty.Comma.Hom.hom_left, cfo_ι_app_left, Functor.const_obj_obj,
      MorphismProperty.Over.map_obj_left, MorphismProperty.Over.map_map_left,
      MorphismProperty.Over.pullback_map_left]
    rw [← cancel_mono (pullback.fst _ _)]
    simp only [ρwQ, MorphismProperty.Comma.Hom.hom_mk, PreRelativeGluingData.ρw_left,
      Category.assoc, pullbackMap_left_fst, Functor.id_obj, Functor.const_obj_obj, limit.lift_π,
      PullbackCone.mk_pt, PullbackCone.mk_π_app]
    erw [gluingData_ρ]
    rw [ι_transition_assoc]
    nth_rw 2 [← MorphismProperty.Comma.comp_left_assoc]
    rw [IsColimit.fac]
    simp
  rw [this]
  simp [hcfo_desc]

omit [IsLocalAtTarget P] in
lemma aux1 (s : Cocone D) {i j : d.ι} (hij : d.ℬ i ≤ d.ℬ j) :
    d.gluingData.ρ hij ≫
      ((d.hc j).desc ((MorphismProperty.Over.pullback P Q (d.ℬ j).ι).mapCocone s)).left ≫
      pullback.fst s.pt.hom (d.ℬ j).ι =
    ((d.hc i).desc ((MorphismProperty.Over.pullback P Q (d.ℬ i).ι).mapCocone s)).left ≫
      pullback.fst s.pt.hom (d.ℬ i).ι := by
  rw [← d.pullbackMap_left_fst _ hij]
  rw [reassoc_of% aux2]

lemma aux3 (i : d.ι) (s : Cocone D)
    (m : d.gluedCocone.pt ⟶ s.pt)
    (hm : ∀ (j : J), d.gluedCocone.ι.app j ≫ m = s.ι.app j) :
    d.gluingData.glued.ι i ≫ m.left =
      ((d.hc i).desc ((MorphismProperty.Over.pullback P Q (d.ℬ i).ι).mapCocone s)).left ≫
        pullback.fst s.pt.hom (d.ℬ i).ι := by
  let mᵢ : (d.c i).pt ⟶
    (MorphismProperty.Over.pullback P Q (d.ℬ i).ι).obj s.pt :=
      (MorphismProperty.Comma.isoFromComma (d.gluingData.glued.isoPullback i)).inv ≫
        (MorphismProperty.Over.pullback P Q (d.ℬ i).ι).map m
  have comp : d.gluingData.glued.ι i ≫ m.left = mᵢ.left ≫ pullback.fst s.pt.hom (d.ℬ i).ι := by
    simp only [Over.pullback_obj_left, Functor.id_obj, gluingData_f, Over.comp_left, Over.mk_left,
      Over.mk_hom, Over.pullback_map_left, Functor.const_obj_obj, Category.assoc, limit.lift_π,
      id_eq, PullbackCone.mk_pt, PullbackCone.mk_π_app, mᵢ]
    simp [MorphismProperty.Comma.isoFromComma]
    erw [d.gluingData.glued.isoPullback_inv_left_fst_assoc i]
  rw [comp]
  have : mᵢ = (d.hc i).desc
      ((MorphismProperty.Over.pullback P Q (d.ℬ i).ι).mapCocone s) := by
    apply (d.hc i).hom_ext
    intro k
    ext : 1
    rw [← cancel_mono (pullback.fst _ _)]
    simp only [Functor.id_obj, Functor.const_obj_obj, MorphismProperty.Comma.comp_hom,
      Comma.comp_left, MorphismProperty.Over.pullback_obj_left, MorphismProperty.Comma.Hom.hom_left,
      Category.assoc, IsColimit.fac, Functor.mapCocone_pt, Functor.mapCocone_ι_app,
      MorphismProperty.Over.pullback_map_left, limit.lift_π, PullbackCone.mk_pt,
      PullbackCone.mk_π_app]
    have hm : (d.gluedCocone.ι.app k ≫ m).left = (s.ι.app k).left := by
      rw [hm k]
    simp only [Functor.const_obj_obj, MorphismProperty.Comma.comp_left] at hm
    rw [← comp, ← hm, ← componentOpenCover_map_gluedCocone_ι_app_assoc]
    rfl
  rw [this]

/-- The glued cocone is indeed colimiting. -/
def gluedIsColimit : IsColimit d.gluedCocone where
  desc s := {
    toCommaMorphism := d.gluingData.glued.glueHomsOver
      (fun i ↦ ((d.hc i).desc <|
          (MorphismProperty.Over.pullback P Q (d.ℬ i).ι).mapCocone s).left ≫
        pullback.fst s.pt.hom (d.ℬ i).ι)
      (fun {i j} hij ↦ by apply aux1)
      (fun i ↦ by
        simp only [Functor.const_obj_obj, Functor.mapCocone_pt, Over.pullback_obj_left,
          Functor.id_obj, Category.assoc, gluingData_f]
        have : pullback.snd s.pt.hom (d.ℬ i).ι =
          ((MorphismProperty.Over.pullback P Q (d.ℬ i).ι).mapCocone s).pt.hom := rfl
        rw [pullback.condition, this]
        erw [Over.w_assoc]
        rfl)
    prop_hom_left := d.hQ_trivial _
    prop_hom_right := trivial }
  fac s k := by
    dsimp
    ext : 1
    apply (d.componentOpenCover k).hom_ext
    intro i
    simp only [MorphismProperty.Comma.comp_hom, MorphismProperty.Comma.Hom.hom_mk, Comma.comp_left,
      MorphismProperty.Comma.Hom.hom_left, RelativeGluingData.Glued.ι_glueHomsOver,
      componentOpenCover_map_gluedCocone_ι_app_assoc, Functor.const_obj_obj,
      RelativeGluingData.glueHoms_ι]
    rw [← MorphismProperty.Comma.comp_left_assoc, IsColimit.fac]
    simp only [MorphismProperty.Over.pullback_obj_left, Functor.mapCocone_pt,
      Functor.mapCocone_ι_app, MorphismProperty.Over.pullback_map_left, limit.lift_π,
      PullbackCone.mk_pt, PullbackCone.mk_π_app]
    rfl
  uniq s m hm := by
    ext : 1
    apply d.gluingData.glued.hom_ext
    intro i
    simp only [Functor.mapCocone_pt, MorphismProperty.Over.pullback_obj_left, Functor.id_obj,
      Functor.const_obj_obj, RelativeGluingData.Glued.ι_glueHomsOver, RelativeGluingData.glueHoms_ι]
    apply d.aux3 i s m hm

end ColimitGluingData

end Colimits

end AlgebraicGeometry
