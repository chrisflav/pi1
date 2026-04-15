import Pi1.Mathlib.RingTheory.RingHom.Etale
import Pi1.FundamentalGroup.AffineAnd
import Pi1.RingTheory.StableProperties
import Pi1.RingTheory.FiniteEtale.Equalizer
import Pi1.RingTheory.KerTensor

universe u

/-!
# Finite étale ring homomorphisms
-/

namespace RingHom

/-- A ring homomorphism is finite étale if the induced algebra is finite étale. -/
def FiniteEtale {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.FiniteEtale R S

lemma finiteEtale_algebraMap_iff {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    (algebraMap R S).FiniteEtale ↔ Algebra.FiniteEtale R S := by
  simp only [RingHom.FiniteEtale]
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

namespace FiniteEtale

lemma iff_finite_and_etale
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    f.FiniteEtale ↔ f.Etale ∧ f.Finite := by
  rw [FiniteEtale, Finite, Etale]
  rw [Algebra.finiteEtale_iff]

lemma eq_and :
    @FiniteEtale = (fun R S (_ : CommRing R) (_ : CommRing S) f ↦ f.Etale ∧ f.Finite) := by
  ext
  rw [iff_finite_and_etale]

lemma isStableUnderBaseChange : IsStableUnderBaseChange FiniteEtale := by
  rw [eq_and]
  exact Etale.isStableUnderBaseChange.and finite_isStableUnderBaseChange

lemma respectsIso : RespectsIso FiniteEtale := by
  rw [eq_and]
  apply Etale.respectsIso.and finite_respectsIso

lemma hasFiniteProducts : HasFiniteProducts FiniteEtale := by
  introv R _ hf
  simp_rw [finiteEtale_algebraMap_iff] at hf ⊢
  constructor

lemma hasEqualizers : HasEqualizers FiniteEtale := by
  introv R hS hT
  rw [finiteEtale_algebraMap_iff] at hS hT ⊢
  apply Algebra.Etale.equalizer

lemma hasStableEqualizers : HasStableEqualizers FiniteEtale := by
  introv R hA hB
  rw [finiteEtale_algebraMap_iff] at hA hB
  exact Algebra.tensorEqualizer_bijective_of_finite_of_etale f g

instance : (toMorphismProperty RingHom.FiniteEtale).IsStableUnderCobaseChange := by
  rw [isStableUnderCobaseChange_toMorphismProperty_iff]
  exact isStableUnderBaseChange

end FiniteEtale

end RingHom
