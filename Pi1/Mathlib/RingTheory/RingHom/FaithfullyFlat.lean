import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Pi1.Mathlib.RingTheory.RingHom.Bijective

open TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}

lemma Module.FaithfullyFlat.bijective_of_tensorProduct [Algebra R S]
    {T : Type*} [CommRing T] [Algebra R T] [Module.FaithfullyFlat R S]
    (H : Function.Bijective (algebraMap S (S ⊗[R] T))) :
    Function.Bijective (algebraMap R T) := by
  have : LinearMap.lTensor S (Algebra.linearMap R T) =
      Algebra.linearMap S (S ⊗[R] T) ∘ₗ (AlgebraTensorModule.rid R S S).toLinearMap := by
    ext; simp
  refine ⟨?_, ?_⟩
  · apply (Module.FaithfullyFlat.lTensor_injective_iff_injective R S (Algebra.linearMap R T)).mp
    simpa [this] using H.1
  · apply (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S (Algebra.linearMap R T)).mp
    simpa [this] using H.2

lemma RingHom.FaithfullyFlat.codescendsAlong_bijective :
    RingHom.CodescendsAlong (fun f ↦ Function.Bijective f) RingHom.FaithfullyFlat := by
  apply RingHom.CodescendsAlong.mk
  · exact RingHom.Bijective.respectsIso
  · introv h H
    rw [RingHom.faithfullyFlat_algebraMap_iff] at h
    exact h.bijective_of_tensorProduct H
