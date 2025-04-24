import Mathlib.AlgebraicGeometry.Morphisms.Constructors
import Pi1.Mathlib.CategoryTheory.MorphismProperty.Limits

universe u

open TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry

variable (P : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β], (α → β) → Prop)

end AlgebraicGeometry
