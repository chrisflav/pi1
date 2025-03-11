import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

universe u w

open CategoryTheory Limits

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

end General
