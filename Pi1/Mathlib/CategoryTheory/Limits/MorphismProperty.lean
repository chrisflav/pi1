import Mathlib.CategoryTheory.Limits.MorphismProperty
import Pi1.FundamentalGroup.AffineColimits

open CategoryTheory Limits

namespace CategoryTheory.MorphismProperty.Over

noncomputable
instance {C : Type*} [Category C] (P : MorphismProperty C) (X : C)
    [HasPullbacks C] [P.IsStableUnderComposition] [P.ContainsIdentities]
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    CreatesFiniteLimits (Over.forget P ⊤ X) :=
  createsFiniteLimitsOfCreatesTerminalAndPullbacks _

instance {C : Type*} [Category C] (P : MorphismProperty C) (X : C)
    [HasPullbacks C] [P.IsStableUnderComposition] [P.ContainsIdentities]
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    PreservesFiniteLimits (Over.forget P ⊤ X) :=
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks (Over.forget P ⊤ X)

variable {C : Type*} [Category C] (P Q : MorphismProperty C)
variable [HasPullbacks C] [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]
  [Q.IsMultiplicative]

instance {X Y : C} (f : X ⟶ Y) [P.HasOfPostcompProperty P]
    [P.IsStableUnderComposition] [P.ContainsIdentities] :
    PreservesFiniteLimits (MorphismProperty.Over.pullback P ⊤ f) := by
  constructor
  intro J _ _
  have heq : MorphismProperty.Over.pullback P ⊤ f ⋙ MorphismProperty.Over.forget _ _ _ =
      MorphismProperty.Over.forget _ _ _ ⋙ CategoryTheory.Over.pullback f :=
    rfl
  have : PreservesLimitsOfShape J
      (MorphismProperty.Over.pullback P ⊤ f ⋙ MorphismProperty.Over.forget _ _ _) := by
    rw [heq]
    infer_instance
  apply preservesLimitsOfShape_of_reflects_of_preserves
    (MorphismProperty.Over.pullback P ⊤ f) (MorphismProperty.Over.forget _ _ _)

end CategoryTheory.MorphismProperty.Over
