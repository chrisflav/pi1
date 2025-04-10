import Mathlib.RingTheory.RingHom.Integral
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Ideal.GoingUp

lemma Algebra.IsIntegral.specComap_surjective_of_injective {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) :
    Function.Surjective (algebraMap R S).specComap := by
  intro ⟨p, hp⟩
  obtain ⟨Q, _, hQ, rfl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal S)
    (by simp [Ideal.comap_bot_of_injective (algebraMap R S) hinj])
  exact ⟨⟨Q, hQ⟩, rfl⟩

lemma RingHom.IsIntegral.specComap_surjective {R S : Type*} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : f.IsIntegral) (hinj : Function.Injective f) :
    Function.Surjective f.specComap := by
  algebraize [f]
  exact Algebra.IsIntegral.specComap_surjective_of_injective hinj
