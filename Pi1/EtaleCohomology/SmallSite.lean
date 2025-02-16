/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Sites.Small

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

def smallEtaleTopology (X : Scheme.{u}) : GrothendieckTopology (Etale X) :=
  X.smallGrothendieckTopology

end AlgebraicGeometry
