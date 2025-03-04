/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.Etale
import Pi1.Mathlib.AlgebraicGeometry.Limits
import Pi1.FundamentalGroup.FiniteEtale
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-!
# The category of finite étale morphisms over a connected base is a Galois category

Let `S` be a scheme and denote by `FEt S` the category of finite étale schemes over `S`. Then
`FEt S` is a `PreGaloisCategory`.
-/

universe u w

open CategoryTheory Limits

instance {C : Type*} [Category C] {G : Type*} [Group G] [Finite G] [HasFiniteColimits C] :
    HasColimitsOfShape (SingleObj G) C := by
  obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  exact Limits.hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm

namespace AlgebraicGeometry

section General

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
