/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.Etale
import Pi1.FundamentalGroup.FiniteEtale
import Mathlib.CategoryTheory.Galois.Basic

universe u w

open CategoryTheory Limits

instance {C : Type*} [Category C] {G : Type*} [Group G] [Finite G] [HasFiniteColimits C] :
    HasColimitsOfShape (SingleObj G) C := by
  obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  exact Limits.hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm

namespace AlgebraicGeometry.FiniteEtale

variable (X : Scheme.{u})

instance (X : Scheme.{u}) : PreGaloisCategory (FiniteEtale X) where
  hasQuotientsByFiniteGroups G := inferInstance
  monoInducesIsoOnDirectSummand {f g} i hi := sorry

noncomputable
def fiber {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ X) (f : FiniteEtale X) : Scheme.{u} :=
  pullback x f.hom

end AlgebraicGeometry.FiniteEtale
