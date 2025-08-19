/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

instance : HasOfPostcompProperty @IsProper @IsSeparated where
  of_postcomp f g _ _ := IsProper.of_comp_of_isSeparated f g


namespace IsFinite

lemma of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite (f ≫ g)] [IsAffineHom g] : IsFinite f := by
  rw [IsFinite.iff_isProper_and_isAffineHom]
  exact ⟨IsProper.of_comp_of_isSeparated f g, IsAffineHom.of_comp f g⟩

instance : HasOfPostcompProperty @IsFinite @IsFinite where
  of_postcomp f g _ _ := .of_comp f g

end IsFinite

end AlgebraicGeometry
