import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Pi1.Mathlib.CategoryTheory.MorphismProperty.Limits
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Pi1.Mathlib.RingTheory.RingHom.Flat
import Pi1.Mathlib.RingTheory.Spectrum.Prime.Topology

universe u v

open TensorProduct

section

@[algebraize Module.FaithfullyFlat]
def RingHom.FaithfullyFlat {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  Module.FaithfullyFlat R S

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

lemma RingHom.faithfullyFlat_algebraMap_iff [Algebra R S] :
    (algebraMap R S).FaithfullyFlat ↔ Module.FaithfullyFlat R S := by
  simp only [RingHom.FaithfullyFlat]
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

lemma RingHom.FaithfullyFlat.flat (hf : f.FaithfullyFlat) : f.Flat := by
  algebraize [f]
  exact inferInstanceAs <| Module.Flat R S

lemma RingHom.FaithfullyFlat.iff_flat_and_comap_surjective :
    f.FaithfullyFlat ↔ f.Flat ∧ Function.Surjective f.specComap := by
  algebraize [f]
  show (algebraMap R S).FaithfullyFlat ↔ (algebraMap R S).Flat ∧
    Function.Surjective (algebraMap R S).specComap
  rw [RingHom.faithfullyFlat_algebraMap_iff, RingHom.flat_algebraMap_iff]
  exact ⟨fun h ↦ ⟨inferInstance, PrimeSpectrum.specComap_surjective_of_faithfullyFlat⟩,
    fun ⟨h, hf⟩ ↦ .of_specComap_surjective hf⟩

lemma Module.FaithfullyFlat.bijective_of_tensorProduct [Algebra R S]
    {T : Type*} [CommRing T] [Algebra R T] [Module.FaithfullyFlat R S]
    (H : Function.Bijective (algebraMap S (S ⊗[R] T))) :
    Function.Bijective (algebraMap R T) := by
  refine ⟨?_, ?_⟩
  · apply (Module.FaithfullyFlat.lTensor_injective_iff_injective R S (Algebra.linearMap R T)).mp
    have : LinearMap.lTensor S (Algebra.linearMap R T) =
        Algebra.linearMap S (S ⊗[R] T) ∘ₗ (AlgebraTensorModule.rid R S S).toLinearMap := by
      ext; simp
    simpa [this] using H.1
  · apply (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S (Algebra.linearMap R T)).mp
    have : LinearMap.lTensor S (Algebra.linearMap R T) =
        Algebra.linearMap S (S ⊗[R] T) ∘ₗ (AlgebraTensorModule.rid R S S).toLinearMap := by
      ext; simp
    simpa [this] using H.2

lemma RingHom.Bijective.stableUnderComposition :
    RingHom.StableUnderComposition (fun f ↦ Function.Bijective f) :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ hg.comp hf

lemma RingHom.Bijective.respectsIso :
    RingHom.RespectsIso (fun f ↦ Function.Bijective f) :=
  RingHom.Bijective.stableUnderComposition.respectsIso fun e ↦ e.bijective

lemma RingHom.FaithfullyFlat.bijective_codescendsAlong :
    RingHom.CodescendsAlong (fun f ↦ Function.Bijective f) RingHom.FaithfullyFlat := by
  apply RingHom.CodescendsAlong.mk
  · exact RingHom.Bijective.respectsIso
  · introv h H
    rw [RingHom.faithfullyFlat_algebraMap_iff] at h
    exact h.bijective_of_tensorProduct H

end

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

lemma exists_preimage_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (x : X) (y : Y)
    (hxy : f.base x = g.base y) :
    ∃ (p : P), fst.base p = x ∧ snd.base p = y := by
  let e := h.isoPullback
  obtain ⟨z, hzl, hzr⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback x y hxy
  use h.isoPullback.inv.base z
  simp [← Scheme.comp_base_apply, hzl, hzr]

lemma image_preimage_eq_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (s : Set X) :
    snd.base '' (fst.base ⁻¹' s) = g.base ⁻¹' (f.base '' s) := by
  refine subset_antisymm ?_ (fun x hx ↦ ?_)
  · rw [Set.image_subset_iff, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.comp_base, ← h.1.1]
    rw [Scheme.comp_base, TopCat.coe_comp, ← Set.image_subset_iff, Set.image_comp]
    exact Set.image_mono (Set.image_preimage_subset _ _)
  · obtain ⟨y, hy, heq⟩ := hx
    obtain ⟨o, hl, hr⟩ := exists_preimage_of_isPullback h y x heq
    use o
    simpa [hl, hr]

instance : IsStableUnderComposition @Surjective where
  comp_mem _ _ hf hg := ⟨hg.1.comp hf.1⟩

instance Flat.surjective_descendsAlong_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @Surjective (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have : RespectsRight (@Surjective) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
    constructor
    introv hi hf
    exact MorphismProperty.comp_mem _ _ _ hf hi.1.1
  have : HasOfPrecompProperty (@Surjective) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
    constructor
    introv hf hcomp
    exact Surjective.of_comp f g
  infer_instance

instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [Flat g] : Flat (pullback.fst f g) :=
  pullback_fst _ _ inferInstance

instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [Flat f] : Flat (pullback.snd f g) :=
  pullback_snd _ _ inferInstance

instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [Surjective g] :
    Surjective (pullback.fst f g) :=
  pullback_fst _ _ inferInstance

instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [Surjective f] :
    Surjective (pullback.snd f g) :=
  pullback_snd _ _ inferInstance

lemma QuasiCompact.compactSpace_of_compactSpace {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
      [CompactSpace Y] : CompactSpace X := by
  constructor
  rw [← Set.preimage_univ (f := f.base)]
  exact QuasiCompact.isCompact_preimage _ isOpen_univ CompactSpace.isCompact_univ

@[stacks 02JY]
lemma Flat.isQuotientMap_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [QuasiCompact f]
    [Surjective f] : Topology.IsQuotientMap f.base := by
  rw [Topology.isQuotientMap_iff]
  refine ⟨f.surjective, fun s ↦ ⟨fun hs ↦ hs.preimage f.continuous, fun hs ↦ ?_⟩⟩
  wlog hY : ∃ R, Y = Spec R
  · let 𝒰 := Y.affineCover
    rw [𝒰.isOpenCover_opensRange.isOpen_iff_inter]
    intro i
    rw [Scheme.Hom.coe_opensRange, ← Set.image_preimage_eq_inter_range]
    apply (𝒰.map i).isOpenMap
    refine this (f := pullback.fst (𝒰.map i) f) _ ?_ ⟨_, rfl⟩
    rw [← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.comp_base, pullback.condition,
      Scheme.comp_base, TopCat.coe_comp, Set.preimage_comp]
    exact hs.preimage (Scheme.Hom.continuous _)
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    let 𝒰 := X.affineCover.finiteSubcover
    let T := ∐ (fun i : 𝒰.J ↦ 𝒰.obj i)
    let p : ∐ (fun i : 𝒰.J ↦ 𝒰.obj i) ⟶ X := Sigma.desc (fun i ↦ 𝒰.map i)
    have _ (i : 𝒰.J) : IsAffine (𝒰.obj i) := inferInstanceAs <| IsAffine (X.affineCover.obj _)
    have _ : Flat p := by
      rw [IsLocalAtSource.iff_of_openCover (P := @Flat) (sigmaOpenCover _)]
      exact fun i ↦ by simpa [p] using IsLocalAtSource.of_isOpenImmersion _
    have _ : Surjective p := ⟨fun x ↦ by
      obtain ⟨i, x, rfl⟩ := X.affineCover.finiteSubcover.exists_eq x
      use (Sigma.ι (fun i ↦ X.affineCover.finiteSubcover.obj i) i).base x
      rw [← Scheme.comp_base_apply, Sigma.ι_desc]⟩
    refine this (f := T.isoSpec.inv ≫ p ≫ f) _ _ ?_ ⟨_, rfl⟩
    rw [← Category.assoc, Scheme.comp_base, TopCat.coe_comp, Set.preimage_comp]
    exact hs.preimage (T.isoSpec.inv ≫ p).continuous
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  refine ((PrimeSpectrum.isQuotientMap_of_generalizingMap ?_ ?_).isOpen_preimage).mp hs
  exact (surjective_iff (Spec.map φ)).mp inferInstance
  apply RingHom.Flat.generalizingMap_comap
  rwa [← HasRingHomProperty.Spec_iff (P := @Flat)]

lemma _root_.CategoryTheory.Limits.isPullback_map_snd_snd {C : Type*} [Category C] [HasPullbacks C]
    {X Y Z S : C} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) :
    IsPullback (pullback.map _ _ _ _ (pullback.snd f g) (pullback.snd f h) f
        pullback.condition pullback.condition)
      (pullback.fst (pullback.fst f g) (pullback.fst f h))
      (pullback.fst g h) (pullback.snd f g) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro c
    refine pullback.lift c.snd
        (pullback.lift (c.snd ≫ pullback.fst _ _) (c.fst ≫ pullback.snd _ _) ?_) ?_
    · simp [pullback.condition, ← c.condition_assoc]
    · simp
  · intro c
    apply pullback.hom_ext <;> simp [c.condition]
  · intro c
    apply pullback.hom_ext <;> simp [c.condition]
  · intro c m hfst hsnd
    apply pullback.hom_ext
    · simpa
    · apply pullback.hom_ext <;> simp [← hsnd, pullback.condition, ← hfst]

lemma _root_.CategoryTheory.Limits.isPullback_map_fst_fst {C : Type*} [Category C] [HasPullbacks C]
    {X Y Z U S : C} (f : X ⟶ S) (g : Y ⟶ S) (i : Z ⟶ S) (h : U ⟶ pullback i g) :
    IsPullback
      (pullback.map (pullback.snd f g) (h ≫ pullback.snd i g) f i
        (pullback.fst f g) (h ≫ pullback.fst i g) g
        pullback.condition.symm (by simp [pullback.condition]))
      (pullback.snd (pullback.snd f g) (h ≫ pullback.snd i g))
      (pullback.snd f i)
      (h ≫ pullback.fst i g) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro c
    exact pullback.lift (pullback.lift (c.fst ≫ pullback.fst _ _) (c.snd ≫ h ≫ pullback.snd _ _)
          (by simp [pullback.condition, c.condition_assoc])) c.snd (by simp)
  · intro c
    apply pullback.hom_ext <;> simp [c.condition]
  · intro c
    simp
  · intro c m hfst hsnd
    apply pullback.hom_ext
    · apply pullback.hom_ext
      simp [← hfst]
      simp [← hsnd, pullback.condition]
    · simpa

/-- Universally closed satisfies fpqc descent. -/
@[stacks 02KS]
instance Flat.universallyClosed_descendsAlong_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @UniversallyClosed (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine IsLocalAtTarget.descendsAlong_inf_quasiCompact _ _ ?_ ?_
  · exact fun {X} _ ↦ X.exists_hom_isAffine_of_isLocalAtSource _ @Flat le_rfl
  refine fun {R} S Y φ g ⟨_, _⟩ hfst ↦ ⟨universally_mk' _ _ fun {T} f _ s hs ↦ ?_⟩
  let p := pullback.fst (pullback.fst (Spec.map φ) f) (pullback.fst (Spec.map φ) g)
  let r : pullback (pullback.fst (Spec.map φ) f) (pullback.fst (Spec.map φ) g) ⟶ pullback f g :=
    pullback.map _ _ _ _ (pullback.snd _ _) (pullback.snd _ _) (Spec.map φ) (pullback.condition ..)
      (pullback.condition ..)
  have : IsClosed ((pullback.snd (Spec.map φ) f).base ⁻¹' ((pullback.fst f g).base '' s)) := by
    rw [← image_preimage_eq_of_isPullback (isPullback_map_snd_snd ..)]
    exact p.isClosedMap _ (hs.preimage r.continuous)
  rwa [(Flat.isQuotientMap_of_surjective _).isClosed_preimage] at this

/-- Universally open satisfies fpqc descent. -/
@[stacks 02KT]
instance Flat.universallyOpen_descendsAlong_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @UniversallyOpen
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  refine IsLocalAtTarget.descendsAlong_inf_quasiCompact _ _ ?_ ?_
  · exact fun {X} _ ↦ X.exists_hom_isAffine_of_isLocalAtSource _ @Flat le_rfl
  refine fun {R} S Y φ g ⟨_, _⟩ hfst ↦ ⟨universally_mk' _ _ fun {T} f _ s hs ↦ ?_⟩
  let p := pullback.fst (pullback.fst (Spec.map φ) f) (pullback.fst (Spec.map φ) g)
  let r : pullback (pullback.fst (Spec.map φ) f) (pullback.fst (Spec.map φ) g) ⟶ pullback f g :=
    pullback.map _ _ _ _ (pullback.snd _ _) (pullback.snd _ _) (Spec.map φ) (pullback.condition ..)
      (pullback.condition ..)
  have : IsOpen ((pullback.snd (Spec.map φ) f).base ⁻¹' ((pullback.fst f g).base '' s)) := by
    rw [← image_preimage_eq_of_isPullback (isPullback_map_snd_snd ..)]
    exact p.isOpenMap _ (hs.preimage r.continuous)
  rwa [(Flat.isQuotientMap_of_surjective _).isOpen_preimage] at this

lemma flat_and_surjective_SpecMap_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Flat (Spec.map f) ∧ Surjective (Spec.map f) ↔ f.hom.FaithfullyFlat := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective, surjective_iff]
  rfl

lemma isIso_SpecMap_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsIso (Spec.map f) ↔ Function.Bijective f.hom := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : IsIso (Spec.map f).appTop := inferInstance
    rw [← ConcreteCategory.isIso_iff_bijective]
    show isomorphisms _ _
    rwa [(isomorphisms _).arrow_mk_iso_iff (arrowIsoΓSpecOfIsAffine f)]
  · have : IsIso f := by rwa [ConcreteCategory.isIso_iff_bijective]
    infer_instance

instance Flat.universallyInjective_descendsAlong_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @UniversallyInjective (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  apply DescendsAlong.mk'
  introv hf hfst
  rw [UniversallyInjective.iff_diagonal] at hfst ⊢
  have heq : pullback.fst (pullback.fst (pullback.snd g g ≫ g) f) (pullback.diagonal g) =
      (pullbackSymmetry _ _).hom ≫
      (pullbackRightPullbackFstIso _ _ _).hom ≫
      (pullback.congrHom (by simp) rfl).hom ≫
      (pullbackSymmetry _ _).hom ≫
      pullback.diagonal (pullback.fst f g) ≫
      (diagonalObjPullbackFstIso f g).hom := by
    apply pullback.hom_ext
    apply pullback.hom_ext <;> simp [pullback.condition]
    simp [pullback.condition]
  apply MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := @Surjective) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (f := pullback.fst (pullback.snd g g ≫ g) f)
  · exact MorphismProperty.pullback_fst _ _ hf
  · rw [heq]
    iterate 4 rw [cancel_left_of_respectsIso (P := @Surjective)]
    rwa [cancel_right_of_respectsIso (P := @Surjective)]

instance Flat.isomorphisms_descendsAlong_surjective_inf_flat_inf_quasicompact :
    (isomorphisms Scheme.{u}).DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  apply IsLocalAtTarget.descendsAlong_inf_quasiCompact
  · intro X _
    exact X.exists_hom_isAffine_of_isLocalAtSource _ @Flat le_rfl
  · intro R S Y φ g h (hfst : IsIso _)
    have : IsAffine Y :=
      have : IsIso (pullback.fst (Spec.map φ) g) := ‹_›
      have : UniversallyInjective g := by
        apply MorphismProperty.of_pullback_fst_of_descendsAlong
          (P := @UniversallyInjective) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := Spec.map φ)
        exact ⟨h, inferInstance⟩
        infer_instance
      have : Surjective g := by
        apply MorphismProperty.of_pullback_fst_of_descendsAlong
          (P := @Surjective) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := Spec.map φ)
        exact ⟨h, inferInstance⟩
        infer_instance
      have hopen' : UniversallyOpen g :=
        MorphismProperty.of_pullback_fst_of_descendsAlong
          (P := @UniversallyOpen) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := Spec.map φ)
          ⟨h, inferInstance⟩ inferInstance
      have : IsHomeomorph g.base :=
        ⟨g.continuous, g.isOpenMap, g.injective, g.surjective⟩
      have : IsAffineHom g :=
        AlgebraicGeometry.isAffineHom_of_isInducing g this.isInducing
          this.isClosedEmbedding.isClosed_range
      isAffine_of_isAffineHom g
    wlog hY : ∃ T, Y = Spec T generalizing Y
    · rw [← (isomorphisms Scheme).cancel_left_of_respectsIso Y.isoSpec.inv]
      have heq : pullback.fst (Spec.map φ) (Y.isoSpec.inv ≫ g) =
          pullback.map _ _ _ _ (𝟙 _) (Y.isoSpec.inv) (𝟙 _) (by simp) (by simp) ≫
            pullback.fst (Spec.map φ) g := (pullback.lift_fst _ _ _).symm
      refine this _ ?_ ?_ ⟨_, rfl⟩
      · show isomorphisms Scheme _
        rwa [heq, (isomorphisms Scheme).cancel_left_of_respectsIso]
      · infer_instance
    obtain ⟨T, rfl⟩ := hY
    obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
    apply of_pullback_fst_Spec_of_codescendsAlong (P := isomorphisms Scheme.{u})
      (Q' := RingHom.FaithfullyFlat) (Q := fun f ↦ Function.Bijective f) (P' := @Surjective ⊓ @Flat)
    · exact RingHom.FaithfullyFlat.bijective_codescendsAlong
    · intro _ _ f hf
      rwa [← flat_and_surjective_SpecMap_iff, and_comm]
    · simp_rw [← isIso_SpecMap_iff]
      rfl
    · exact h
    · exact hfst

lemma _root_.RingHom.Flat.isOpenMap_comap_of_finitePresentation
    {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} (hf : f.Flat)
    (hfin : f.FinitePresentation) :
    IsOpenMap (PrimeSpectrum.comap f) := by
  algebraize [f]
  exact PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation

lemma of_generalizingMap {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (hf : GeneralizingMap f.base) : IsOpenMap f.base := by
  show topologically IsOpenMap f
  wlog hY : ∃ R, Y = Spec R
  · rw [IsLocalAtTarget.iff_of_openCover (P := topologically IsOpenMap) Y.affineCover]
    intro i
    dsimp only [Scheme.Cover.pullbackHom]
    refine this _ ?_ ⟨_, rfl⟩
    exact IsLocalAtTarget.of_isPullback (P := topologically GeneralizingMap)
      (iY := Y.affineCover.map i) (IsPullback.of_hasPullback ..) hf
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · rw [IsLocalAtSource.iff_of_openCover (P := topologically IsOpenMap) X.affineCover]
    intro i
    refine this _ _ ?_ ⟨_, rfl⟩
    exact IsLocalAtSource.comp (P := topologically GeneralizingMap) hf _
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  algebraize [φ.hom]
  convert PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
  · rwa [Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap]
  · apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp inferInstance

lemma Flat.generalizingMap {X Y : Scheme.{u}} (f : X ⟶ Y) [hf : Flat f] :
    GeneralizingMap f.base := by
  have := HasRingHomProperty.of_isLocalAtSource_of_isLocalAtTarget.{u}
    (topologically GeneralizingMap)
  show topologically GeneralizingMap f
  rw [HasRingHomProperty.iff_appLE (P := topologically GeneralizingMap)]
  intro U V e
  algebraize [(f.appLE U V e).hom]
  apply Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp
  convert Algebra.HasGoingDown.of_flat
  exact hf.1 U V e

instance (priority := low) Flat.universallyOpen {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [LocallyOfFinitePresentation f] : UniversallyOpen f :=
  ⟨universally_mk' _ _ fun _ _ ↦ of_generalizingMap _ (Flat.generalizingMap _)⟩

instance (priority := low) Flat.isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [QuasiCompact f] [Surjective f] [Mono f] : IsIso f := by
  apply MorphismProperty.of_pullback_fst_of_descendsAlong
    (P := isomorphisms Scheme.{u}) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := f) (g := f)
  · tauto
  · exact inferInstanceAs <| IsIso (pullback.fst f f)

instance (priority := low) Flat.isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [LocallyOfFinitePresentation f] [Mono f] : IsOpenImmersion f := by
  wlog hf : Surjective f
  · let U : Y.Opens := ⟨Set.range f.base, f.isOpenMap.isOpen_range⟩
    have hU : IsOpenImmersion U.ι := U.instIsOpenImmersionι
    let f' : X ⟶ U := AlgebraicGeometry.IsOpenImmersion.lift U.ι f (by simp [U])
    have heq : f = f' ≫ U.ι := by simp [f']
    have hflat : Flat f' := by
      refine of_postcomp (W := @Flat) (W' := @IsOpenImmersion) f' U.ι ?_ ?_
      · infer_instance
      · rwa [← heq]
    have hfinpres : LocallyOfFinitePresentation f' := by
      refine of_postcomp (W := @LocallyOfFinitePresentation) (W' := @IsOpenImmersion) f' U.ι ?_ ?_
      · infer_instance
      · rwa [← heq]
    have hmono : Mono f' := by
      convert mono_of_mono f' U.ι
      rwa [← heq]
    rw [heq]
    have := this f' ⟨fun x : U ↦ by
      obtain ⟨a, ha⟩ := x.2
      use a
      apply Subtype.ext
      rw [← ha]
      simp only [f']
      conv_rhs => rw [heq]
      simp only [Scheme.comp_coeBase, TopCat.hom_comp, ContinuousMap.comp_apply,
        Scheme.Opens.ι_base_apply, SetLike.coe_eq_coe, f']⟩
    apply IsOpenImmersion.comp
  have hhomeo : IsHomeomorph f.base :=
    ⟨f.continuous, f.isOpenMap, f.injective, f.surjective⟩
  have : QuasiCompact f := ⟨fun U hU hc ↦ (hhomeo.homeomorph).isCompact_preimage.mpr hc⟩
  infer_instance

end AlgebraicGeometry
