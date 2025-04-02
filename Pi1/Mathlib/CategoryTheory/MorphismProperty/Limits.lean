import Mathlib.CategoryTheory.MorphismProperty.Limits

namespace CategoryTheory

open Limits

lemma MorphismProperty.universally_mk' {C : Type*} [Category C]
    (P : MorphismProperty C) [P.RespectsIso] {X Y : C} (g : X ⟶ Y)
    (H : ∀ {T : C} (f : T ⟶ Y) [HasPullback f g], P (pullback.fst f g)) :
    universally P g := by
  introv X' h
  have := h.hasPullback
  rw [← h.isoPullback_hom_fst, P.cancel_left_of_respectsIso]
  exact H ..

end CategoryTheory
