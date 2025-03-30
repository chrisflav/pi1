import Mathlib
import Pi1.Mathlib.RingTheory.RingHomProperties
import Pi1.Mathlib.CategoryTheory.MorphismProperty.Limits

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable (P P' : MorphismProperty Scheme.{u})
variable (Q Q' : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

lemma HasRingHomProperty.descendsAlong [IsLocalAtTarget P] (hQQ' : RingHom.DescendsAlong Q Q') :
    P.DescendsAlong P' := by
  constructor
  introv h hf hfst
  wlog hZ : ∃ R, Z = Spec R
  · rw [IsLocalAtTarget.iff_of_openCover (P := P) Z.affineCover]
    intro i
    apply this P P' Q Q' hQQ' <;> sorry
  sorry

end AlgebraicGeometry
