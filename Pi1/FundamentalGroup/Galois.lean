/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.Etale
import Pi1.FundamentalGroup.FiniteEtale
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

universe u w

open CategoryTheory Limits

instance {C : Type*} [Category C] {G : Type*} [Group G] [Finite G] [HasFiniteColimits C] :
    HasColimitsOfShape (SingleObj G) C := by
  obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  exact Limits.hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm

namespace AlgebraicGeometry

section General

lemma isClosedImmersion_of_isPreimmersion_of_isClosed
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsPreimmersion f] (hf : IsClosed (Set.range f.base)) :
    IsClosedImmersion f where
  base_closed := ⟨Scheme.Hom.isEmbedding f, hf⟩

lemma isClosedImmersion_iff_isClosed_range_of_isPreimmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsPreimmersion f] :
    IsClosedImmersion f ↔ IsClosed (Set.range f.base) :=
  ⟨fun _ ↦ f.isClosedEmbedding.isClosed_range,
    fun h ↦ isClosedImmersion_of_isPreimmersion_of_isClosed f h⟩

lemma isIso_of_isOpenImmersion_of_opensRange_eq_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (hf : f.opensRange = ⊤) :
    IsIso f := by
  rw [isIso_iff_isOpenImmersion]
  refine ⟨inferInstance, ?_⟩
  rw [TopCat.epi_iff_surjective, ← Set.range_eq_univ]
  exact TopologicalSpace.Opens.ext_iff.mp hf

lemma SurjectiveOnStalks.mono_of_injective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [SurjectiveOnStalks f] (hf : Function.Injective f.base) : Mono f := by
  refine (Scheme.forgetToLocallyRingedSpace ⋙
    LocallyRingedSpace.forgetToSheafedSpace).mono_of_mono_map ?_
  apply SheafedSpace.mono_of_base_injective_of_stalk_epi
  · exact hf
  · exact fun x ↦ ConcreteCategory.epi_of_surjective _ (f.stalkMap_surjective x)

lemma nonempty_isColimit_cofanMk_of_aux {ι : Type u} {X : ι → Scheme.{u}}
    {S : Scheme.{u}}
    (f : ∀ i, X i ⟶ S) [∀ i, IsOpenImmersion (f i)]
    (hcov : ⨆ i, (f i).opensRange = ⊤)
    (hdisj : ∀ i j : ι, i ≠ j → Disjoint (f i).opensRange (f j).opensRange) :
    Nonempty (IsColimit <| Cofan.mk S f) := by
  let 𝒰 : S.OpenCover := by
    refine .mkOfCovers ι X f (fun x ↦ ?_)
    have : x ∈ ⨆ i, (f i).opensRange := by rw [hcov]; trivial
    simpa using this
  have : SurjectiveOnStalks (Sigma.desc f) := by
    rw [IsLocalAtSource.iff_of_openCover (P := @SurjectiveOnStalks) (sigmaOpenCover X)]
    intro i
    simp
    infer_instance
  let 𝒱 : (∐ X).OpenCover := sigmaOpenCover X
  have : Mono (Sigma.desc f) := by
    apply this.mono_of_injective
    intro x y hxy
    obtain ⟨i, a, rfl⟩ := 𝒱.exists_eq x
    obtain ⟨j, b, rfl⟩ := 𝒱.exists_eq y
    rw [← Scheme.comp_base_apply, ← Scheme.comp_base_apply] at hxy
    simp [𝒱] at hxy
    by_cases h : i = j
    · subst h
      congr
      apply (f i).injective
      exact hxy
    · simp [𝒱]
      have hdisj : (f i).opensRange ⊓ (f j).opensRange = ⊥ := by
        rw [← disjoint_iff]
        exact hdisj i j h
      have : (f i).base a ∈ (f i).opensRange ⊓ (f j).opensRange := by
        constructor
        · use a
        · rw [hxy]
          use b
      simp [hdisj] at this
  have : IsOpenImmersion (Sigma.desc f) := by
    rw [IsLocalAtTarget.iff_of_openCover (P := @IsOpenImmersion) 𝒰]
    · intro i
      have : pullback.snd (Sigma.desc f) (𝒰.map i) ≫ Sigma.ι X i =
          pullback.fst (Sigma.desc f) (𝒰.map i) := by
        simp [𝒰, ← cancel_mono (Sigma.desc f), pullback.condition]
      have : IsOpenImmersion (Scheme.Cover.pullbackHom 𝒰 (Sigma.desc f) i ≫ Sigma.ι X i) := by
        simp only [Scheme.Cover.pullbackCover_obj, Scheme.Cover.pullbackHom, this]
        infer_instance
      exact IsOpenImmersion.of_comp _ (Sigma.ι X i)
  rw [← Cofan.isColimit_iff_isIso_sigmaDesc (Cofan.mk S f)]
  show IsIso (Sigma.desc f)
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  · rw [eq_top_iff]
    rintro x hx
    have : x ∈ ⨆ i, (f i).opensRange := by rwa [hcov]
    simp only [TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.mem_mk,
      Set.mem_iUnion] at this
    obtain ⟨i, y, rfl⟩ := this
    use (Sigma.ι X i).base y
    simp [← Scheme.comp_base_apply]

lemma nonempty_isColimit_cofanMk_of {ι : Type w} [UnivLE.{w, u}] {X : ι → Scheme.{u}}
    {S : Scheme.{u}}
    (f : ∀ i, X i ⟶ S) [∀ i, IsOpenImmersion (f i)]
    (hcov : ⨆ i, (f i).opensRange = ⊤)
    (hdisj : ∀ i j : ι, i ≠ j → Disjoint (f i).opensRange (f j).opensRange) :
    Nonempty (IsColimit <| Cofan.mk S f) := by
  obtain ⟨κ, ⟨e⟩⟩ := Small.equiv_small (α := ι)
  constructor
  apply IsColimit.ofWhiskerEquivalence (Discrete.equivalence e).symm
  apply Nonempty.some
  apply nonempty_isColimit_cofanMk_of_aux (fun k ↦ f (e.symm k))
  · rw [← hcov]
    apply Equiv.iSup_congr
    intro
    rfl
  · exact fun _ _ hij ↦ hdisj _ _ fun h ↦ hij <| e.symm.injective h

lemma nonempty_isColimit_binaryCofanMk_of_isCompl {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) [IsOpenImmersion f] [IsOpenImmersion g]
    (hf : IsCompl f.opensRange g.opensRange) :
    Nonempty (IsColimit <| BinaryCofan.mk f g) := by
  have := pair X Y
  let c : Cofan _ := BinaryCofan.mk f g
  let c' : Cofan (fun j ↦ (WalkingPair.casesOn j X Y : Scheme.{u})) :=
    Cofan.mk S (fun j ↦ WalkingPair.casesOn j f g)
  let i : c ≅ c' := by
    refine Cofan.ext (eqToIso rfl) ?_
    rintro (b|b) <;> rfl
  constructor
  refine IsColimit.ofIsoColimit ?_ i.symm
  apply Nonempty.some
  let fi (j : WalkingPair) : WalkingPair.casesOn j X Y ⟶ S := WalkingPair.casesOn j f g
  convert nonempty_isColimit_cofanMk_of fi _ _
  · intro i
    cases i <;> (simp [fi]; infer_instance)
  · rw [← WalkingPair.equivBool.symm.iSup_comp]
    rw [iSup_bool_eq]
    simp only [WalkingPair.equivBool_symm_apply_true, WalkingPair.equivBool_symm_apply_false, fi]
    rw [← codisjoint_iff]
    exact hf.2
  · intro i j hij
    match i, j with
    | .left, .right => simpa [fi] using hf.1
    | .right, .left => simpa [fi] using hf.1.symm

end General

namespace FiniteEtale

variable (X : Scheme.{u})

/-- The category of finite étale morphisms is a pre-galois category. -/
instance (X : Scheme.{u}) : PreGaloisCategory (FiniteEtale X) where
  hasQuotientsByFiniteGroups G := inferInstance
  monoInducesIsoOnDirectSummand {f g} i hi := by
    rw [FiniteEtale.mono_iff] at hi
    obtain ⟨ho, hc⟩ := hi
    let A : Set g.left := Set.range i.hom.left.base
    have hA : IsClosed A := i.hom.left.isClosedEmbedding.isClosed_range
    let U : g.left.Opens := ⟨Aᶜ, hA.isOpen_compl⟩
    have : IsClosedImmersion U.ι := by
      apply isClosedImmersion_of_isPreimmersion_of_isClosed
      simp only [Scheme.Opens.range_ι, TopologicalSpace.Opens.coe_mk, isClosed_compl_iff, U, A]
      apply IsOpenImmersion.isOpen_range
    let u : FiniteEtale X := ⟨Over.mk (U.ι ≫ g.hom), by simpa using ⟨⟩⟩
    refine ⟨u, MorphismProperty.Over.homMk U.ι, ⟨?_⟩⟩
    apply isColimitOfReflects (MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _)
    apply (isColimitMapCoconeBinaryCofanEquiv _ _ _).invFun
    simp only [Functor.comp_obj, MorphismProperty.Comma.forget_obj, Over.forget_obj,
      Functor.comp_map, MorphismProperty.Comma.forget_map, Over.forget_map,
      MorphismProperty.Over.homMk_hom, Over.homMk_left]
    apply Nonempty.some
    apply nonempty_isColimit_binaryCofanMk_of_isCompl
    constructor
    · rw [disjoint_iff]
      ext : 1
      simp [U, A]
    · rw [codisjoint_iff]
      ext : 1
      simp [U, A]

noncomputable
def fiber {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ X) (f : FiniteEtale X) : Scheme.{u} :=
  pullback x f.hom

end AlgebraicGeometry.FiniteEtale
