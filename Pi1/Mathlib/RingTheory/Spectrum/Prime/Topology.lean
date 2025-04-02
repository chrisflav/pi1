import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.RingHom.Flat

section

namespace PrimeSpectrum

variable {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} (h₁ : Function.Surjective (comap f))

include h₁

/-- If `f : Spec S → Spec R` is specializing and surjective, the topology on `Spec R` is the
quotient topology induced by `f`. -/
lemma isQuotientMap_of_specializingMap (h₂ : SpecializingMap (comap f)) :
    Topology.IsQuotientMap (comap f) := by
  rw [Topology.isQuotientMap_iff_isClosed]
  exact ⟨h₁, fun s ↦ ⟨fun hs ↦ hs.preimage (comap f).continuous,
    fun hsc ↦ Set.image_preimage_eq s h₁ ▸ isClosed_image_of_stableUnderSpecialization _ _ hsc
      (h₂.stableUnderSpecialization_image hsc.stableUnderSpecialization)⟩⟩

/-- If `f : Spec S → Spec R` is generalizing and surjective, the topology on `Spec R` is the
quotient topology induced by `f`. -/
lemma isQuotientMap_of_generalizingMap (h₂ : GeneralizingMap (comap f)) :
    Topology.IsQuotientMap (comap f) := by
  rw [Topology.isQuotientMap_iff_isClosed]
  refine ⟨h₁, fun s ↦ ⟨fun hs ↦ hs.preimage (comap f).continuous,
    fun hsc ↦ Set.image_preimage_eq s h₁ ▸ ?_⟩⟩
  apply isClosed_image_of_stableUnderSpecialization _ _ hsc
  rw [Set.image_preimage_eq s h₁, ← stableUnderGeneralization_compl_iff]
  convert h₂.stableUnderGeneralization_image hsc.isOpen_compl.stableUnderGeneralization
  rw [← Set.preimage_compl, Set.image_preimage_eq _ h₁]

end PrimeSpectrum
