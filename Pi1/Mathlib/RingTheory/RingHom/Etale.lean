import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.RingHom.Locally
import Mathlib.RingTheory.RingHom.StandardSmooth

universe u

namespace RingHom

def Etale {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.Etale R S

-- this follows from the analogous statement for smoothness and is done in a branch of mathlib
-- TODO: integrate that branch into pi1 or mathlib
theorem Etale.iff_locally_isStandardSmoothOfRelativeDimension
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    f.Etale ↔ Locally (IsStandardSmoothOfRelativeDimension 0) f :=
  sorry
