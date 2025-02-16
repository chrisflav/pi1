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

/-- The small étale site of a scheme is the Grothendieck topology on the
category of schemes étale over `X` induced from the étale topology on `Scheme.{u}`. -/
def smallEtaleTopology (X : Scheme.{u}) : GrothendieckTopology (Etale X) :=
  X.smallGrothendieckTopology (P := @IsEtale)

/-- The pretopology generating the small étale site. -/
def smallEtalePretopology (X : Scheme.{u}) : Pretopology (Etale X) :=
  X.smallPretopology (Q := @IsEtale) (P := @IsEtale)

end AlgebraicGeometry
