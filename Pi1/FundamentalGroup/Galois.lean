/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.Etale
import Pi1.FundamentalGroup.FiniteEtale
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

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

-- TODO: these are wrong, need covering and disjointness conditions

lemma Scheme.isColimit_cofanMk_iff_of_finite {S : Scheme.{u}}
    {ι : Type*} [Finite ι] {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S) :
    Nonempty (IsColimit <| Cofan.mk S f) ↔
      ∀ i, IsOpenImmersion (f i) ∧ IsClosedImmersion (f i) :=
  sorry

end General

namespace FiniteEtale

variable (X : Scheme.{u})

lemma isColimit_cofanMk_iff_of_finite {S : Scheme.{u}} {Y : FiniteEtale S}
    {ι : Type*} [Finite ι] {X : ι → FiniteEtale S} (f : ∀ i, X i ⟶ Y) :
    Nonempty (IsColimit (Cofan.mk Y f)) ↔
      ∀ i, IsOpenImmersion (f i).hom.left ∧ IsClosedImmersion (f i).hom.left :=
  sorry

lemma isColimit_binaryCofanMk_iff {S : Scheme.{u}}
    {X Y Z : FiniteEtale S} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Nonempty (IsColimit (BinaryCofan.mk f g)) ↔ IsOpenImmersion f.hom.left ∧
      IsOpenImmersion g.hom.left ∧
      IsClosedImmersion f.hom.left ∧
      IsClosedImmersion g.hom.left :=
  sorry

instance (X : Scheme.{u}) : PreGaloisCategory (FiniteEtale X) where
  hasQuotientsByFiniteGroups G := inferInstance
  monoInducesIsoOnDirectSummand {f g} i hi := by
    rw [FiniteEtale.mono_iff] at hi
    obtain ⟨ho, hc⟩ := hi
    let A : Set g.left := Set.range i.hom.left.base
    have hA : IsClosed A := i.hom.left.isClosedEmbedding.isClosed_range
    let U : g.left.Opens := ⟨Aᶜ, hA.isOpen_compl⟩
    have : IsClosedImmersion U.ι := by
      apply isClosedImmersion_of_isOpenImmersion_of_isClosed
      simp only [Scheme.Opens.range_ι, TopologicalSpace.Opens.coe_mk, isClosed_compl_iff, U, A]
      apply IsOpenImmersion.isOpen_range
    let u : FiniteEtale X := ⟨Over.mk (U.ι ≫ g.hom), by simpa using ⟨⟩⟩
    refine ⟨u, MorphismProperty.Over.homMk U.ι, ?_⟩
    rw [isColimit_binaryCofanMk_iff]
    refine ⟨inferInstance, ?_, inferInstance, ?_⟩
    · dsimp
      infer_instance
    · dsimp
      infer_instance

noncomputable
def fiber {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ X) (f : FiniteEtale X) : Scheme.{u} :=
  pullback x f.hom

end AlgebraicGeometry.FiniteEtale
