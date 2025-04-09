import Mathlib
import Pi1.RingTheory.RankAtStalk
import Pi1.RingTheory.FinitePresentation
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.Flat
import Pi1.Mathlib.RingTheory.RingHom.Finite

open CategoryTheory Limits TopologicalSpace TensorProduct

universe u

noncomputable def RingHom.finrank {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : PrimeSpectrum R) : ℕ :=
  letI : Algebra R S := f.toAlgebra
  Module.rankAtStalk S x

@[simp]
lemma finrank_algebraMap {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    (algebraMap R S).finrank = Module.rankAtStalk (R := R) S := by
  ext
  dsimp only [RingHom.finrank]
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

lemma RingHom.finrank_comp_left_of_bijective {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (hf : Function.Bijective g) (x : PrimeSpectrum R) :
    (g.comp f).finrank x = f.finrank x := by
  sorry

lemma RingHom.finrank_comp_right_of_bijective {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (hg : Function.Bijective f) (x : PrimeSpectrum S) :
    (g.comp f).finrank (f.specComap x) = g.finrank x := by
  sorry

lemma Algebra.rankAtStalk_eq_of_isPushout (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (R' S' : Type*) [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S'] [Algebra R' S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    [Algebra.IsPushout R S R' S'] [Module.Flat R S] [Module.Finite R S] (x : PrimeSpectrum R') :
    Module.rankAtStalk S' x = Module.rankAtStalk S (PrimeSpectrum.comap (algebraMap R R') x) := by
  have : IsPushout R R' S S' := Algebra.IsPushout.symm inferInstance
  have := Module.rankAtStalk_eq_of_equiv (Algebra.IsPushout.equiv R R' S S').symm.toLinearEquiv
  rw [Module.rankAtStalk_eq_of_equiv (Algebra.IsPushout.equiv R R' S S').symm.toLinearEquiv,
    Module.rankAtStalk_tensorProduct]
  rfl

lemma CommRingCat.isPushout_iff_isPushout {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {R' S' : Type u} [CommRing R'] [CommRing S'] [Algebra R R'] [Algebra S S'] [Algebra R' S']
    [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] :
    IsPushout (ofHom <| algebraMap R R') (ofHom <| algebraMap R S)
      (ofHom <| algebraMap R' S') (ofHom <| algebraMap S S') ↔ Algebra.IsPushout R R' S S' := by
  refine ⟨?_, fun h ↦ isPushout_of_isPushout ..⟩
  --refine Algebra.IsPushout.of_equiv ?_ -- does not exist :(
  sorry

lemma CommRingCat.finrank_eq_of_isPushout {R S T P : CommRingCat.{u}} {f : R ⟶ S} {g : R ⟶ T}
    {inl : S ⟶ P} {inr : T ⟶ P} (h : IsPushout f g inl inr) (hf : f.hom.Flat) (hfin : f.hom.Finite)
    (x : PrimeSpectrum T) : inr.hom.finrank x = f.hom.finrank (PrimeSpectrum.comap g.hom x) := by
  algebraize [f.hom, g.hom, inl.hom, inr.hom, inl.hom.comp f.hom]
  have : IsScalarTower R T P := .of_algebraMap_eq' <| congr($(h.1.1).hom)
  have : Algebra.IsPushout R S T P := CommRingCat.isPushout_iff_isPushout.mp h
  exact Algebra.rankAtStalk_eq_of_isPushout R S T P x

namespace AlgebraicGeometry

noncomputable section

section

variable {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

lemma IsAffine.of_isPullback [IsAffine X] [IsAffine Y] [IsAffine Z]
    (h : IsPullback fst snd f g) : IsAffine P :=
  .of_isIso h.isoPullback.hom

lemma isPushout_appTop_of_isPullback [IsAffine X] [IsAffine Y] [IsAffine Z]
    (h : IsPullback fst snd f g) :
    IsPushout f.appTop g.appTop fst.appTop snd.appTop := by
  have : IsAffine P := .of_isPullback h
  have : IsPullback (AffineScheme.ofHom fst) (AffineScheme.ofHom snd) (AffineScheme.ofHom f)
      (AffineScheme.ofHom g) :=
    IsPullback.of_map_of_faithful AffineScheme.forgetToScheme.{u} h
  exact (IsPullback.map AffineScheme.Γ.rightOp this).unop.flip

end

variable {X S : Scheme.{u}} (f : X ⟶ S)

def IsAffine.finrank [IsAffine S] (f : X ⟶ S) (s : S) : ℕ :=
  (f.appTop).hom.finrank (S.isoSpec.hom.base s)

lemma IsAffine.finrank_of_isPullback {Y T : Scheme.{u}} [IsAffine S] [IsAffine T]
    (f' : Y ⟶ T) (g' : Y ⟶ X) (g : T ⟶ S) (h : IsPullback g' f' f g) [Flat f] [IsFinite f]
    (s : S) (t : T) (hs : g.base t = s) :
    IsAffine.finrank f' t = IsAffine.finrank f s := by
  subst hs
  dsimp [finrank]
  have : IsAffine X := isAffine_of_isAffineHom f
  have : IsPushout f.appTop g.appTop g'.appTop f'.appTop := isPushout_appTop_of_isPullback h
  convert CommRingCat.finrank_eq_of_isPushout this
    (HasRingHomProperty.appTop (P := @Flat) _ inferInstance)
    ((HasAffineProperty.iff_of_isAffine (P := @IsFinite).mp inferInstance).2) (T.isoSpec.hom.base t)
  rw [← Scheme.comp_base_apply, ← Scheme.isoSpec_hom_naturality]
  rfl

lemma IsAffine.finrank_snd {T : Scheme.{u}} [IsAffine S] [IsAffine T]
    (g : T ⟶ S) [Flat f] [IsFinite f] (x : T) :
    IsAffine.finrank (pullback.snd f g) x = IsAffine.finrank f (g.base x) := by
  dsimp [finrank]
  apply finrank_of_isPullback f
  apply IsPullback.of_hasPullback
  rfl

lemma IsAffine.finrank_comp_left_of_isIso {X Y Z : Scheme.{u}} [IsAffine Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsFinite g] [Flat g] :
    IsAffine.finrank (f ≫ g) = IsAffine.finrank g := by
  ext z
  apply finrank_of_isPullback g (f ≫ g) f (𝟙 _) _ _ _ rfl
  exact IsPullback.of_horiz_isIso (by simp)

def finrank {X S : Scheme.{u}} (f : X ⟶ S) (s : S) : ℕ :=
  IsAffine.finrank (pullback.snd f (S.affineOpenCover.map s)) (S.affineOpenCover.covers s).choose

lemma finrank_eq_finrank_snd_of_isAffine {T : Scheme.{u}} (g : T ⟶ S) [IsAffine T] (t : T) [Flat f]
    [IsFinite f] : finrank f (g.base t) = IsAffine.finrank (pullback.snd f g) t := by
  let i := S.affineOpenCover.map (g.base t)
  dsimp only [finrank]
  let Y := pullback i g
  obtain ⟨y, hyl, hyr⟩ := Scheme.Pullback.exists_preimage_pullback
    (S.affineOpenCover.covers <| g.base t).choose t
    ((S.affineOpenCover.covers <| g.base t).choose_spec)
  let U := Spec (Y.affineOpenCover.obj y)
  let z : U := (Y.affineOpenCover.covers y).choose
  have : IsFinite (pullback.snd f g) := MorphismProperty.pullback_snd _ _ inferInstance
  have : IsFinite (pullback.snd f (S.affineOpenCover.map ((ConcreteCategory.hom g.base) t))) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  trans IsAffine.finrank
      (pullback.snd (pullback.snd f g) (Y.affineOpenCover.map y ≫ pullback.snd _ _)) z
  · symm
    refine IsAffine.finrank_of_isPullback _ _ ?_ ?_ ?_ _ _ ?_
    · exact pullback.map _ _ _ _ (pullback.fst f g) (Y.affineOpenCover.map y ≫ pullback.fst _ _) g
        pullback.condition.symm (by simp [← pullback.condition]; rfl)
    · exact Y.affineOpenCover.map y ≫ pullback.fst _ _
    · apply isPullback_map_fst_fst
    · rw [← hyl]
      simp only [Scheme.affineOpenCover_obj, Spec.toLocallyRingedSpace_obj,
        Scheme.affineOpenCover_map, Scheme.comp_coeBase, TopCat.hom_comp, ContinuousMap.comp_apply,
        Scheme.affineOpenCover_f]
      congr
      exact (Y.affineOpenCover.covers y).choose_spec
  · convert IsAffine.finrank_snd (pullback.snd f g) (Y.affineOpenCover.map y ≫ pullback.snd _ _) z
    simp only [← hyr, Scheme.affineOpenCover_f, Scheme.affineOpenCover_obj, TopCat.hom_comp,
      Spec.toLocallyRingedSpace_obj, Scheme.affineOpenCover_map, Scheme.comp_coeBase,
      ContinuousMap.comp_apply]
    congr
    exact (Y.affineOpenCover.covers y).choose_spec.symm

lemma finrank_eq_of_isAffine [IsAffine S] [Flat f] [IsFinite f] (s : S) :
    finrank f s = IsAffine.finrank f s := by
  rw [show s = (𝟙 S : S ⟶ S).base s from rfl, finrank_eq_finrank_snd_of_isAffine,
    IsAffine.finrank_snd]

@[simp]
lemma finrank_SpecMap_eq_finrank {R S : CommRingCat.{u}} (f : R ⟶ S) [IsFinite (Spec.map f)]
    [Flat (Spec.map f)] :
    finrank (Spec.map f) = f.hom.finrank := by
  ext x
  rw [finrank_eq_of_isAffine]
  dsimp only [IsAffine.finrank]
  have : f = (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop ≫ (Scheme.ΓSpecIso S).hom := by simp
  conv_rhs => rw [this]
  rw [← Category.assoc]
  have : Function.Bijective (Scheme.ΓSpecIso S).hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).hom
  rw [← RingHom.finrank_comp_right_of_bijective (Scheme.ΓSpecIso R).inv.hom _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv)]
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.finrank_comp_left_of_bijective _ _ this]
  congr
  simp only [Scheme.isoSpec_Spec_hom]
  show (Spec.map _).base _ = _
  rw [← Scheme.comp_base_apply, ← Spec.map_comp]
  simp

lemma rank_SpecMap_algebraMap (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S] (x : PrimeSpectrum R) :
    finrank (Spec.map (CommRingCat.ofHom <| algebraMap R S)) x =
      Module.rankAtStalk S x := by
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    rw [HasAffineProperty.SpecMap_iff_of_affineAnd (P := @IsFinite) (Q := RingHom.Finite)]
    simp only [CommRingCat.hom_ofHom, RingHom.finite_algebraMap_iff]
    infer_instance
    infer_instance
    exact RingHom.finite_respectsIso
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    simpa [HasRingHomProperty.Spec_iff (P := @Flat), RingHom.flat_algebraMap_iff]
  simp [finrank_SpecMap_eq_finrank]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsFinite f]
    [LocallyOfFinitePresentation f]

instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsFinite f] :
    IsFinite (pullback.snd f g) := MorphismProperty.pullback_snd _ _ ‹_›

instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsFinite g] :
    IsFinite (pullback.fst f g) := MorphismProperty.pullback_fst _ _ ‹_›

@[simp]
lemma finrank_comp_left_of_isIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [Flat g]
    [IsFinite g] [LocallyOfFinitePresentation g] : finrank (f ≫ g) = finrank g := by
  ext z
  rw [finrank, finrank]
  let e : pullback (f ≫ g) (Z.affineOpenCover.map z) ≅ pullback g (Z.affineOpenCover.map z) :=
    (pullbackRightPullbackFstIso g (Z.affineOpenCover.map z) f).symm ≪≫
      asIso (pullback.snd f (pullback.fst g (Z.affineOpenCover.map z)))
  have : e.hom ≫ pullback.snd _ _ = pullback.snd _ _ := by simp [e]
  rw [← this, IsAffine.finrank_comp_left_of_isIso]

lemma finrank_pullback_snd {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Flat f] [IsFinite f] [LocallyOfFinitePresentation f] (y : Y) :
    finrank (pullback.snd f g) y = finrank f (g.base y) := by
  let R := Y.affineOpenCover.obj y
  let i : Spec R ⟶ Y := Y.affineOpenCover.map y
  let y' : Spec R := Y.affineOpenCover.covers y |>.choose
  have h1 : i.base y' = y := Y.affineOpenCover.covers y |>.choose_spec
  have h2 : (i ≫ g).base y' = g.base y := by simp [h1]
  rw [← h2, ← h1, finrank_eq_finrank_snd_of_isAffine, finrank_eq_finrank_snd_of_isAffine,
    ← pullbackLeftPullbackSndIso_hom_snd f g i, ← finrank_eq_of_isAffine,
    ← finrank_eq_of_isAffine, finrank_comp_left_of_isIso]

nonrec lemma finrank_of_isPullback {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : IsPullback fst snd f g)
    [Flat f] [IsFinite f] [LocallyOfFinitePresentation f] (y : Y) :
    finrank snd y = finrank f (g.base y) := by
  rw [← h.isoPullback_hom_snd, finrank_comp_left_of_isIso, finrank_pullback_snd]

nonrec lemma one_le_finrank_map [Flat f] [IsFinite f] [LocallyOfFinitePresentation f] (x : X) :
    1 ≤ finrank f (f.base x) := by
  wlog hY : ∃ R, Y = Spec R
  · let g : Spec (Y.affineOpenCover.obj _) ⟶ Y := Y.affineOpenCover.map (f.base x)
    let y' := Y.affineOpenCover.covers (f.base x) |>.choose
    have heq : g.base y' = f.base x := Y.affineOpenCover.covers (f.base x) |>.choose_spec
    rw [← heq, ← finrank_pullback_snd]
    obtain ⟨z, hzl, hzr⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x y' (by simp [← heq])
    have heq : y' = (pullback.snd f g).base z := hzr.symm
    rw [heq]
    refine this _ _ ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have _ : IsAffine X := isAffine_of_isAffineHom f
    have heq : f.base x = (X.isoSpec.inv ≫ f).base (X.isoSpec.hom.base x) := by simp
    rw [← finrank_comp_left_of_isIso X.isoSpec.inv, heq]
    exact this _ _ _ ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  rw [finrank_SpecMap_eq_finrank]
  algebraize [φ.hom]
  rw [← RingHom.algebraMap_toAlgebra φ.hom, finrank_algebraMap]
  show 0 < _
  have : Module.Flat R S := (HasRingHomProperty.Spec_iff (P := @Flat)).mp ‹_›
  have : Module.Finite R S := (HasAffineProperty.SpecMap_iff_of_affineAnd
    (P := @IsFinite) (Q := RingHom.Finite) inferInstance RingHom.finite_respectsIso _).mp ‹_›
  rw [Algebra.rankAtStalk_pos_iff_mem_range_specComap]
  use x
  rfl

nonrec lemma one_le_finrank_iff_surjective [Flat f] [IsFinite f] [LocallyOfFinitePresentation f] :
    1 ≤ finrank f ↔ Surjective f := by
  refine ⟨fun h ↦ ?_, fun _ ↦ ?_⟩
  · wlog hY : ∃ R, Y = Spec R
    · rw [IsLocalAtTarget.iff_of_openCover (P := @Surjective) Y.affineCover]
      intro i
      dsimp only [Scheme.Cover.pullbackHom]
      refine this _ (fun y ↦ ?_) ⟨_, rfl⟩
      rw [finrank_pullback_snd]
      exact h _
    obtain ⟨R, rfl⟩ := hY
    wlog hX : ∃ S, X = Spec S
    · have _ : IsAffine X := isAffine_of_isAffineHom f
      rw [← MorphismProperty.cancel_left_of_respectsIso @Surjective X.isoSpec.inv]
      refine this _ _ (fun x ↦ ?_) ⟨_, rfl⟩
      rw [finrank_comp_left_of_isIso]
      exact h x
    obtain ⟨S, rfl⟩ := hX
    obtain ⟨φ, rfl⟩ := Spec.map_surjective f
    constructor
    intro x
    specialize h x
    rw [finrank_SpecMap_eq_finrank] at h
    algebraize [φ.hom]
    have : Module.Flat R S := (HasRingHomProperty.Spec_iff (P := @Flat)).mp ‹_›
    have : Module.Finite R S := (HasAffineProperty.SpecMap_iff_of_affineAnd
      (P := @IsFinite) (Q := RingHom.Finite) inferInstance RingHom.finite_respectsIso _).mp ‹_›
    exact (Algebra.rankAtStalk_pos_iff_mem_range_specComap _).mp h
  · intro y
    obtain ⟨x, rfl⟩ := f.surjective y
    exact one_le_finrank_map f x

lemma Scheme.exists_Spec_base_eq {X : Scheme.{u}} (x : X) :
    ∃ (R : CommRingCat.{u}) (f : Spec R ⟶ X) (_ : IsOpenImmersion f) (y : Spec R),
    f.base y = x :=
  ⟨X.affineOpenCover.obj x, X.affineOpenCover.map x, inferInstance, X.affineOpenCover.covers x⟩

nonrec lemma isLocallyConstant_finrank : IsLocallyConstant (finrank f) := by
  wlog hY : ∃ R, Y = Spec R
  · rw [IsLocallyConstant.iff_exists_open]
    intro y
    obtain ⟨R, g, _, x, rfl⟩ := Y.exists_Spec_base_eq y
    have := this (pullback.snd f g) ⟨_, rfl⟩
    rw [IsLocallyConstant.iff_exists_open] at this
    obtain ⟨U, hU, hxU, H⟩ := this x
    refine ⟨g ''ᵁ ⟨U, hU⟩, (g ''ᵁ ⟨U, hU⟩).2, ⟨x, hxU, rfl⟩, fun y ↦ ?_⟩
    rintro ⟨y, (hyU : y ∈ U), rfl⟩
    have := H y hyU
    rwa [finrank_pullback_snd, finrank_pullback_snd] at this
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have _ : IsAffine X := isAffine_of_isAffineHom f
    rw [← finrank_comp_left_of_isIso X.isoSpec.inv]
    exact this _ _ ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  rw [finrank_SpecMap_eq_finrank]
  algebraize [φ.hom]
  have : Module.Flat R S := (HasRingHomProperty.Spec_iff (P := @Flat)).mp ‹_›
  have : Module.Finite R S := (HasAffineProperty.SpecMap_iff_of_affineAnd
    (P := @IsFinite) (Q := RingHom.Finite) inferInstance RingHom.finite_respectsIso _).mp ‹_›
  have : Algebra.FinitePresentation R S :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp ‹_›
  exact Module.isLocallyConstant_rankAtStalk

lemma continuous_finrank : Continuous (finrank f) :=
  (isLocallyConstant_finrank f).continuous

lemma finrank_eq_one_of_isIso [IsIso f] : finrank f = 1 := by
  ext y
  obtain ⟨R, g, _, y, rfl⟩ := Y.exists_Spec_base_eq y
  have : Nontrivial R := y.nontrivial
  rw [← finrank_pullback_snd, ← Category.comp_id (pullback.snd f g), finrank_comp_left_of_isIso,
    ← Spec.map_id, finrank_SpecMap_eq_finrank, CommRingCat.hom_id, Pi.one_apply,
    ← Algebra.id.map_eq_id, finrank_algebraMap]
  simp

nonrec lemma isIso_iff_rank_eq [Flat f] [IsFinite f] [LocallyOfFinitePresentation f] :
    CategoryTheory.IsIso f ↔ finrank f = 1 := by
  refine ⟨fun h ↦ finrank_eq_one_of_isIso f, fun h ↦ ?_⟩
  wlog hY : ∃ R, Y = Spec R
  · show MorphismProperty.isomorphisms _ _
    rw [IsLocalAtTarget.iff_of_openCover (P := MorphismProperty.isomorphisms Scheme) Y.affineCover]
    intro i
    dsimp [Scheme.Cover.pullbackHom]
    refine this _ ?_ ⟨_, rfl⟩
    ext y
    rw [finrank_pullback_snd, h, Pi.one_apply, Pi.one_apply]
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have _ : IsAffine X := isAffine_of_isAffineHom f
    show MorphismProperty.isomorphisms _ _
    rw [← MorphismProperty.cancel_left_of_respectsIso (MorphismProperty.isomorphisms Scheme)
      X.isoSpec.inv]
    refine this _ _ ?_ ⟨_, rfl⟩
    rw [finrank_comp_left_of_isIso, h]
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  algebraize [φ.hom]
  have : Module.Flat R S := (HasRingHomProperty.Spec_iff (P := @Flat)).mp ‹_›
  have : Module.Finite R S := (HasAffineProperty.SpecMap_iff_of_affineAnd
    (P := @IsFinite) (Q := RingHom.Finite) inferInstance RingHom.finite_respectsIso _).mp ‹_›
  have : IsIso φ := by
    apply (ConcreteCategory.isIso_iff_bijective φ).mpr
    apply Algebra.bijective_of_rankAtStalk
    rwa [finrank_SpecMap_eq_finrank] at h
  infer_instance

lemma finrank_eq_const_of_preconnectedSpace [PreconnectedSpace Y] (y y' : Y) :
    finrank f y = finrank f y' := by
  apply IsLocallyConstant.apply_eq_of_preconnectedSpace
  rw [IsLocallyConstant.iff_continuous]
  exact continuous_finrank f

end

end AlgebraicGeometry
