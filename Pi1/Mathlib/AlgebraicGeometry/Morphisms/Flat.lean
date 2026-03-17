import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Morphisms.Descent
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Pi1.Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import Pi1.Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

universe u v

open TensorProduct

open CategoryTheory Limits MorphismProperty

lemma RingHom.Flat.isOpenMap_comap_of_finitePresentation
    {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} (hf : f.Flat)
    (hfin : f.FinitePresentation) :
    IsOpenMap (PrimeSpectrum.comap f) := by
  algebraize [f]
  exact PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation

namespace AlgebraicGeometry

instance (priority := low) Flat.isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [QuasiCompact f] [Surjective f] [Mono f] : IsIso f :=
  isIso_of_surjective_of_mono f

instance (priority := low) Flat.isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [LocallyOfFinitePresentation f] [Mono f] : IsOpenImmersion f :=
  IsOpenImmersion.of_flat_of_mono f

end AlgebraicGeometry
