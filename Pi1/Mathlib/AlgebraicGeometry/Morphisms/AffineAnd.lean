import Mathlib.AlgebraicGeometry.Morphisms.AffineAnd

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {P : MorphismProperty Scheme.{u}}
variable {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}

lemma HasAffineProperty.SpecMap_iff_of_affineAnd (hP : HasAffineProperty P (affineAnd Q))
    (hQi : RingHom.RespectsIso Q) {R S : CommRingCat.{u}} (f : R ⟶ S) :
    P (Spec.map f) ↔ Q f.hom := by
  have := RingHom.toMorphismProperty_respectsIso_iff.mp hQi
  rw [HasAffineProperty.iff_of_isAffine (P := P), affineAnd, and_iff_right]
  exacts [MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty Q)
    (arrowIsoΓSpecOfIsAffine f).symm, inferInstance]

end AlgebraicGeometry
