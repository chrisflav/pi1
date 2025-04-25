/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Pi1.Mathlib.CategoryTheory.MorphismProperty.Limits
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

/-- If `P` and `Q` are stable under cobase change and pushouts exist in `T`,
this is the functor `P.Over Q X ⥤ P.Over Q Y` given by cobase change along `f`. -/
@[simps! obj_left obj_hom map_left]
noncomputable def Under.pushout : P.Under Q X ⥤ P.Under Q Y where
  obj A :=
    { __ := (CategoryTheory.Under.pushout f).obj A.toComma
      prop := P.pushout_inr _ _ A.prop }
  map {A B} g :=
    { __ := (CategoryTheory.Under.pushout f).map g.toCommaMorphism
      prop_hom_left := trivial
      prop_hom_right := Q.pushout_map f _ g.prop_hom_right }

end CategoryTheory.MorphismProperty
