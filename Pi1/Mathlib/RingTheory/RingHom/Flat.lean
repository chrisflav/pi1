import Mathlib.RingTheory.RingHom.Flat

namespace RingHom

lemma flat_algebraMap_iff {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    (algebraMap R S).Flat ↔ Module.Flat R S := by
  simp only [RingHom.Flat]
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

end RingHom
