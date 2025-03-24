import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.RingHom.Locally
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.RingHom.Unramified
import Pi1.Mathlib.RingTheory.RingHom.Smooth
import Pi1.Mathlib.RingTheory.RingHom.And

universe u

namespace RingHom

/-- A ring hom `R →+* S` is etale, if `S` is an etale `R`-algebra. -/
def Etale {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.Etale R S

lemma etale_algebraMap_iff {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    (algebraMap R S).Etale ↔ Algebra.Etale R S := by
  simp only [RingHom.Etale]
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

lemma etale_iff_formallyUnramified_and_smooth {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    f.Etale ↔ f.FormallyUnramified ∧ f.Smooth := by
  algebraize [f]
  simp only [Etale, Smooth, FormallyUnramified]
  constructor
  · intro h
    constructor
    · infer_instance
    · constructor <;> infer_instance
  · intro ⟨h1, h2⟩
    constructor
    · rw [Algebra.FormallyEtale.iff_unramified_and_smooth]
      constructor <;> infer_instance
    · infer_instance

lemma Etale.eq_and :
    @Etale = fun R S (_ : CommRing R) (_ : CommRing S) f ↦ f.FormallyUnramified ∧ f.Smooth := by
  ext
  rw [etale_iff_formallyUnramified_and_smooth]

lemma Etale.isStableUnderBaseChange : IsStableUnderBaseChange Etale := by
  rw [eq_and]
  apply IsStableUnderBaseChange.and
  · exact FormallyUnramified.isStableUnderBaseChange
  · exact Smooth.isStableUnderBaseChange

lemma Etale.propertyIsLocal : PropertyIsLocal Etale := by
  rw [eq_and]
  apply PropertyIsLocal.and
  · exact FormallyUnramified.propertyIsLocal
  · exact Smooth.propertyIsLocal

lemma Etale.respectsIso : RespectsIso Etale :=
  propertyIsLocal.respectsIso

lemma Etale.ofLocalizationSpanTarget : OfLocalizationSpanTarget Etale :=
  propertyIsLocal.ofLocalizationSpanTarget

lemma Etale.ofLocalizationSpan : OfLocalizationSpan Etale :=
  propertyIsLocal.ofLocalizationSpan

lemma Etale.stableUnderComposition : StableUnderComposition Etale := by
  rw [eq_and]
  apply StableUnderComposition.and
  · exact FormallyUnramified.stableUnderComposition
  · exact Smooth.stableUnderComposition

-- this follows from the analogous statement for smoothness and is done in a branch of mathlib
-- TODO: integrate that branch into pi1 or mathlib
theorem Etale.iff_locally_isStandardSmoothOfRelativeDimension
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    f.Etale ↔ Locally (IsStandardSmoothOfRelativeDimension 0) f :=
  sorry

end RingHom
