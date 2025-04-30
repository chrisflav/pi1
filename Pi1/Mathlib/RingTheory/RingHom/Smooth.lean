/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

open TensorProduct

universe u

namespace RingHom

/-- A ring hom `R →+* S` is smooth, if `S` is a smooth `R`-algebra. -/
def Smooth {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  @Algebra.Smooth R _ S _ f.toAlgebra

lemma smooth_algebraMap_iff {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    (algebraMap R S).Smooth ↔ Algebra.Smooth R S := by
  simp only [RingHom.Smooth]
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

lemma Smooth.stableUnderComposition : StableUnderComposition Smooth := by
  introv R hf hg
  algebraize [f, g, g.comp f]
  have : Algebra.Smooth R S := hf
  have : Algebra.Smooth S T := hg
  rw [Smooth]
  exact Algebra.Smooth.comp R S T

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

lemma Smooth.isStableUnderBaseChange : IsStableUnderBaseChange Smooth := by
  apply IsStableUnderBaseChange.mk _ respectsIso
  introv h
  show (algebraMap S (S ⊗[R] T)).Smooth
  rw [smooth_algebraMap_iff] at h ⊢
  infer_instance

lemma Smooth.ofLocalizationSpanTarget : OfLocalizationSpanTarget Smooth := by
  introv R hs hf
  have hfin : f.FinitePresentation := by
    apply finitePresentation_ofLocalizationSpanTarget _ s hs
    intro r
    apply (hf r).finitePresentation
  algebraize [f]
  rw [Smooth]
  refine ⟨?_, hfin⟩
  rw [← Algebra.smoothLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  intro x
  obtain ⟨r, hr, hrx⟩ : ∃ r ∈ s, x ∈ PrimeSpectrum.basicOpen r := by
    simpa using (PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr hs).ge
      (TopologicalSpace.Opens.mem_top x)
  refine Algebra.basicOpen_subset_smoothLocus_iff.mpr ?_ hrx
  convert (hf ⟨r, hr⟩).1
  dsimp
  ext
  dsimp
  rw [Algebra.smul_def]
  rfl

lemma Smooth.holdsForLocalizationAway : HoldsForLocalizationAway Smooth := by
  introv R h
  rw [smooth_algebraMap_iff]
  exact Algebra.Smooth.of_isLocalization_Away r

lemma Smooth.ofLocalizationSpan : OfLocalizationSpan Smooth := by
  apply ofLocalizationSpanTarget.ofLocalizationSpan
  exact (stableUnderComposition.stableUnderCompositionWithLocalizationAway
    holdsForLocalizationAway).left

lemma Smooth.propertyIsLocal : PropertyIsLocal Smooth where
  localizationAwayPreserves := isStableUnderBaseChange.localizationPreserves.away
  ofLocalizationSpanTarget := ofLocalizationSpanTarget
  ofLocalizationSpan := ofLocalizationSpan
  StableUnderCompositionWithLocalizationAwayTarget :=
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).right

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
