/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.Flat
import Pi1.Mathlib.RingTheory.RingHom.Etale

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace IsEtale

variable (X : Scheme.{u})

instance : MorphismProperty.HasOfPostcompProperty @Etale @Etale := by
  apply MorphismProperty.HasOfPostcompProperty.of_le (W := @Etale)
    (Q := (@LocallyOfFiniteType ⊓ @FormallyUnramified))
  intro X Y f hf
  constructor <;> infer_instance

end IsEtale

end AlgebraicGeometry
