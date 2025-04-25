/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

instance : HasOfPostcompProperty @IsProper @IsSeparated where
  of_postcomp f g _ _ := IsProper.of_comp_of_isSeparated f g

lemma IsAffineHom.of_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsAffineHom g] [IsAffineHom (f ≫ g)] :
    IsAffineHom f := by
  wlog hZ : IsAffine Z
  · rw [IsLocalAtTarget.iff_of_openCover (P := @IsAffineHom) (Z.affineCover.pullbackCover g)]
    intro i
    dsimp [Scheme.Cover.pullbackHom]
    have _ : IsAffineHom
        (pullback.snd f (pullback.fst g (Z.affineCover.map i)) ≫ pullback.snd _ _) := by
      rw [← pullbackRightPullbackFstIso_hom_snd, cancel_left_of_respectsIso (P := @IsAffineHom)]
      exact MorphismProperty.pullback_snd _ _ ‹_›
    have _ : IsAffineHom (pullback.snd g (Z.affineCover.map i)) :=
      MorphismProperty.pullback_snd _ _ ‹_›
    apply this _ (pullback.snd _ _)
    exact Scheme.isAffine_affineCover Z i
  have : IsAffine Y := isAffine_of_isAffineHom g
  have : IsAffine X := isAffine_of_isAffineHom (f ≫ g)
  infer_instance

namespace IsFinite

lemma of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite (f ≫ g)] [IsAffineHom g] : IsFinite f := by
  rw [IsFinite.iff_isProper_and_isAffineHom]
  exact ⟨IsProper.of_comp_of_isSeparated f g, IsAffineHom.of_comp f g⟩

instance : HasOfPostcompProperty @IsFinite @IsFinite where
  of_postcomp f g _ _ := .of_comp f g

end IsFinite

end AlgebraicGeometry
