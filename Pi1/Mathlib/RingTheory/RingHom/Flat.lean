import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Ideal.GoingDown

open PrimeSpectrum

namespace RingHom

lemma flat_algebraMap_iff {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    (algebraMap R S).Flat ↔ Module.Flat R S := by
  simp only [RingHom.Flat]
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

variable {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} (h₁ : Function.Surjective (comap f))

lemma Flat.generalizingMap_comap (hf : f.Flat) : GeneralizingMap (comap f) := by
  algebraize [f]
  show GeneralizingMap (comap (algebraMap R S))
  rw [← Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap]
  infer_instance

end RingHom
