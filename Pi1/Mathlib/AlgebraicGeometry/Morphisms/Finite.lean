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

namespace IsFinite

instance : HasOfPostcompProperty @IsFinite @IsFinite where
  of_postcomp f g _ _ := .of_comp f g

end IsFinite

end AlgebraicGeometry
