import Mathlib.RingTheory.RingHom.Finite

universe u

lemma RingHom.finite_algebraMap_iff {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] : (algebraMap R S).Finite ↔ Module.Finite R S := by
  simp only [RingHom.Finite]
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

