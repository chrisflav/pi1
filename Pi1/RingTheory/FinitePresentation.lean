import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.FinitePresentation

instance (priority := 900) {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FinitePresentation R S] : Algebra.FinitePresentation R S := by
  sorry

instance (priority := 900) {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S] : Module.FinitePresentation R S :=
  sorry
