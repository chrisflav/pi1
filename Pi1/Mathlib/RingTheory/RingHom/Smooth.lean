/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

open TensorProduct

universe u

namespace RingHom

lemma Smooth.respectsIso : RespectsIso Smooth := by
  apply Smooth.stableUnderComposition.respectsIso
  introv
  algebraize [e.toRingHom]
  rw [Smooth]
  have : IsLocalization.Away (1 : R) S := by
    apply IsLocalization.away_of_isUnit_of_bijective
    simp only [isUnit_one]
    exact e.bijective
  exact Algebra.Smooth.of_isLocalization_Away 1

lemma Smooth.ofLocalizationSpan : OfLocalizationSpan Smooth := by
  apply ofLocalizationSpanTarget.ofLocalizationSpan
  exact (stableUnderComposition.stableUnderCompositionWithLocalizationAway
    holdsForLocalizationAway).left

end RingHom

lemma Algebra.FormallySmooth.of_bijective_algebraMap {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (h : Function.Bijective (algebraMap R S)) :
    Algebra.FormallySmooth R S :=
  Algebra.FormallySmooth.of_equiv
    { __ := RingEquiv.ofBijective (algebraMap R S) h, commutes' := by simp }

namespace Algebra

instance {k ι : Type u} [Field k] : FormallySmooth k (FractionRing (MvPolynomial ι k)) :=
  have : FormallySmooth k (MvPolynomial ι k) := inferInstance
  have : FormallySmooth (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) :=
    .of_isLocalization (nonZeroDivisors _)
  .comp k (MvPolynomial ι k) (FractionRing (MvPolynomial ι k))

end Algebra
