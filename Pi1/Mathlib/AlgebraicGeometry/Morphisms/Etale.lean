/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Pi1.Mathlib.RingTheory.RingHom.Etale

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace IsEtale

instance (priority := 900) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsEtale f] :
    FormallyUnramified f where
  formallyUnramified_of_affine_subset U V e := by
    have : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 0)
        (f.appLE (↑U) (↑V) e).hom := by
      apply HasRingHomProperty.appLE (P := @IsSmoothOfRelativeDimension 0)
      infer_instance
    have : RingHom.Locally RingHom.FormallyUnramified (f.appLE U V e).hom := by
      apply RingHom.locally_of_locally _ this
      intro R S _ _ f hf
      algebraize [f]
      rw [RingHom.FormallyUnramified]
      have : Algebra.IsStandardSmoothOfRelativeDimension 0 R S := hf
      infer_instance
    rwa [← RingHom.locally_iff_of_localizationSpanTarget
      RingHom.FormallyUnramified.respectsIso
      RingHom.FormallyUnramified.ofLocalizationSpanTarget]

variable (X : Scheme.{u})

instance : MorphismProperty.HasOfPostcompProperty
    @IsEtale (@LocallyOfFiniteType ⊓ @FormallyUnramified) := by
  rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
  rintro X Y f ⟨hft, hfu⟩
  have : IsOpenImmersion (pullback.diagonal f) := by
    apply FormallyUnramified.AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal
  show IsEtale (pullback.diagonal f)
  infer_instance

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsEtale f] :
    IsSmooth f := by
  have : IsSmoothOfRelativeDimension 0 f := inferInstance
  exact this.isSmooth

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [hf : LocallyOfFinitePresentation f] :
    LocallyOfFiniteType f := by
  rw [HasRingHomProperty.eq_affineLocally @LocallyOfFinitePresentation] at hf
  rw [HasRingHomProperty.eq_affineLocally @LocallyOfFiniteType]
  refine affineLocally_le (fun hf ↦ ?_) f hf
  exact RingHom.FiniteType.of_finitePresentation hf

instance : MorphismProperty.HasOfPostcompProperty @IsEtale @IsEtale := by
  apply MorphismProperty.HasOfPostcompProperty.of_le (W := @IsEtale)
    (Q := (@LocallyOfFiniteType ⊓ @FormallyUnramified))
  intro X Y f hf
  constructor <;> infer_instance

instance : HasPullbacks (Etale X) := by
  unfold Etale
  infer_instance

instance : HasRingHomProperty @IsEtale RingHom.Etale :=
  sorry

instance isOpenImmersion_of_mono {X Y : Scheme.{u}} (f : X ⟶ Y) [IsEtale f] [Mono f] :
    IsOpenImmersion f :=
  sorry

end IsEtale

end AlgebraicGeometry
