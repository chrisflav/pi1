import Pi1.Mathlib.RingTheory.RingHomProperties
import Pi1.Mathlib.RingTheory.RingHom.Flat
import Pi1.Mathlib.RingTheory.RingHom.Bijective
import Pi1.Mathlib.RingTheory.RingHom.And

open TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}

namespace RingHom

/-- A ring map is faithfully flat if `S` is faithfully flat as an `R`-algebra. -/
@[algebraize Module.FaithfullyFlat]
def FaithfullyFlat {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  Module.FaithfullyFlat R S

lemma faithfullyFlat_algebraMap_iff [Algebra R S] :
    (algebraMap R S).FaithfullyFlat ↔ Module.FaithfullyFlat R S := by
  simp only [RingHom.FaithfullyFlat]
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

namespace FaithfullyFlat

lemma flat (hf : f.FaithfullyFlat) : f.Flat := by
  algebraize [f]
  exact inferInstanceAs <| Module.Flat R S

lemma iff_flat_and_comap_surjective :
    f.FaithfullyFlat ↔ f.Flat ∧ Function.Surjective f.specComap := by
  algebraize [f]
  show (algebraMap R S).FaithfullyFlat ↔ (algebraMap R S).Flat ∧
    Function.Surjective (algebraMap R S).specComap
  rw [RingHom.faithfullyFlat_algebraMap_iff, RingHom.flat_algebraMap_iff]
  exact ⟨fun h ↦ ⟨inferInstance, PrimeSpectrum.specComap_surjective_of_faithfullyFlat⟩,
    fun ⟨h, hf⟩ ↦ .of_specComap_surjective hf⟩

lemma eq_and : @FaithfullyFlat =
      fun R S (_ : CommRing R) (_ : CommRing S) f ↦ f.Flat ∧ Function.Surjective f.specComap := by
  ext
  rw [iff_flat_and_comap_surjective]

lemma stableUnderComposition : StableUnderComposition FaithfullyFlat := by
  rw [eq_and]
  refine Flat.stableUnderComposition.and ?_
  introv R hf hg
  rw [PrimeSpectrum.specComap_comp]
  exact hf.comp hg

lemma of_bijective (hf : Function.Bijective f) : f.FaithfullyFlat := by
  rw [iff_flat_and_comap_surjective]
  refine ⟨.of_bijective hf, fun p ↦ ?_⟩
  use (RingEquiv.ofBijective f hf).symm.toRingHom.specComap p
  have : (RingEquiv.ofBijective f hf).symm.toRingHom.comp f = RingHom.id R := by
    ext
    exact (RingEquiv.ofBijective f hf).injective (by simp)
  rw [← PrimeSpectrum.specComap_comp_apply, this, PrimeSpectrum.specComap_id]

lemma respectsIso : RespectsIso FaithfullyFlat :=
  stableUnderComposition.respectsIso (fun e ↦ .of_bijective e.bijective)

lemma isStableUnderBaseChange : IsStableUnderBaseChange FaithfullyFlat := by
  refine .mk _ respectsIso (fun R S T _ _ _ _ _ _ ↦ show (algebraMap _ _).FaithfullyFlat from ?_)
  rw [faithfullyFlat_algebraMap_iff] at *
  infer_instance

end RingHom.FaithfullyFlat

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

lemma RingHom.FaithfullyFlat.bijective_codescendsAlong :
    RingHom.CodescendsAlong (fun f ↦ Function.Bijective f) RingHom.FaithfullyFlat := by
  apply RingHom.CodescendsAlong.mk
  · exact RingHom.Bijective.respectsIso
  · introv h H
    rw [RingHom.faithfullyFlat_algebraMap_iff] at h
    exact h.bijective_of_tensorProduct H
