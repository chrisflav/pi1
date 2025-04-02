import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [LocallyOfFinitePresentation g] :
    LocallyOfFinitePresentation (pullback.fst f g) :=
  pullback_fst _ _ inferInstance

instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation (pullback.snd f g) :=
  pullback_snd _ _ inferInstance

end AlgebraicGeometry
