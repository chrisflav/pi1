import Mathlib.CategoryTheory.MorphismProperty.Limits

namespace CategoryTheory.MorphismProperty

open Limits

variable {T : Type*} [Category T] (P : MorphismProperty T)
variable [HasPushouts T] [P.IsStableUnderCobaseChange]

lemma pushout_map {S S' : T} (f : S ⟶ S') {X Y : Under S} (g : X ⟶ Y)
    (H : P g.right) : P ((CategoryTheory.Under.pushout f).map g).right := by
  have : pushout.inr g.right (pushout.inl X.hom f) ≫
        (pushoutRightPushoutInlIso _ _ _ ≪≫ pushout.congrHom (by simp) rfl).hom =
      ((CategoryTheory.Under.pushout f).map g).right := by
    ext <;> simp
  rw [← this, P.cancel_right_of_respectsIso]
  exact pushout_inr _ _ H

instance : (⊤ : MorphismProperty T).IsStableUnderCobaseChange where
  of_isPushout _ _ := trivial

end CategoryTheory.MorphismProperty
