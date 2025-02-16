import Mathlib.CategoryTheory.MorphismProperty.Composition

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category C] (P Q W : MorphismProperty C)

instance HasOfPostcompProperty.inf [P.HasOfPostcompProperty W]
    [Q.HasOfPostcompProperty W] :
    (P ⊓ Q).HasOfPostcompProperty W where
  of_postcomp f g hg hfg := ⟨P.of_postcomp f g hg hfg.1, Q.of_postcomp f g hg hfg.2⟩

end CategoryTheory.MorphismProperty
