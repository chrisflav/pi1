import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.Constructors

universe u

open CategoryTheory

namespace AlgebraicGeometry

instance : (topologically IsOpenMap).RespectsIso :=
  topologically_respectsIso _ (fun f ↦ f.isOpenMap) (fun _ _ hf hg ↦ hg.comp hf)

instance : IsLocalAtSource (topologically IsOpenMap) :=
  topologically_isLocalAtSource' (fun _ ↦ _) fun _ _ _ hU _ ↦ hU.isOpenMap_iff_comp

instance : (topologically GeneralizingMap).RespectsIso :=
  topologically_respectsIso _ (fun f ↦ f.isOpenEmbedding.generalizingMap
    f.isOpenEmbedding.isOpen_range.stableUnderGeneralization) (fun _ _ hf hg ↦ hf.comp hg)

instance : IsLocalAtSource (topologically GeneralizingMap) :=
  topologically_isLocalAtSource' (fun _ ↦ _) fun _ _ _ hU _ ↦ hU.generalizingMap_iff_comp

instance : IsLocalAtTarget (topologically GeneralizingMap) :=
  topologically_isLocalAtTarget' (fun _ ↦ _) fun _ _ _ hU _ ↦
    hU.generalizingMap_iff_restrictPreimage

section Surjective

instance : MorphismProperty.IsStableUnderComposition @Surjective.{u} where
  comp_mem _ _ hf hg := ⟨hg.1.comp hf.1⟩

end Surjective

end AlgebraicGeometry
