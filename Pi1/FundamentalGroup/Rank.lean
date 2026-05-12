import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

open CategoryTheory Limits TopologicalSpace TensorProduct

universe u

namespace AlgebraicGeometry

noncomputable section

variable {X S : Scheme.{u}} (f : X ⟶ S)

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsFinite f]
    [LocallyOfFinitePresentation f]

lemma finrank_eq_const_of_preconnectedSpace [PreconnectedSpace Y] (y y' : Y) :
    f.finrank y = f.finrank y' := by
  apply IsLocallyConstant.apply_eq_of_preconnectedSpace
  apply f.isLocallyConstant_finrank

end

end AlgebraicGeometry
