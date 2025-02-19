/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Adjunction of pushforward and pullback in `P.Under Q X`

-/

namespace CategoryTheory.MorphismProperty

open Limits

variable {T : Type*} [Category T] (P Q : MorphismProperty T) [Q.IsMultiplicative]
variable {X Y : T} (f : X ⟶ Y)

section Map

variable {P} [P.IsStableUnderComposition] (hPf : P f)

variable {f}

/-- If `P` is stable under composition and `f : X ⟶ Y` satisfies `P`,
this is the functor `P.Over Q X ⥤ P.Over Q Y` given by composing with `f`. -/
@[simps! obj_left obj_hom map_left]
def Under.map : P.Under Q Y ⥤ P.Under Q X :=
  Comma.mapLeft _ (Discrete.natTrans fun _ ↦ f) <| fun X ↦ P.comp_mem _ _ hPf X.prop

end Map

variable [HasPushouts T] [P.IsStableUnderCobaseChange] [Q.IsStableUnderCobaseChange]

/-- If `P` and `Q` are stable under base change and pullbacks exist in `T`,
this is the functor `P.Over Q Y ⥤ P.Over Q X` given by base change along `f`. -/
@[simps! obj_left obj_hom map_left]
noncomputable def Under.pushout : P.Under Q X ⥤ P.Under Q Y where
  obj A :=
    { __ := (CategoryTheory.Under.pushout f).obj A.toComma
      prop := P.pushout_inr _ _ A.prop }
  map {A B} g :=
    { __ := (CategoryTheory.Under.pushout f).map g.toCommaMorphism
      prop_hom_left := trivial
      -- the proof for `Over.pullback` is `Q.baseChange_map f g.toCommaMorphism g.prop_hom_left`
      prop_hom_right := sorry }

end CategoryTheory.MorphismProperty
