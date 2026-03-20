import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.Constructors

universe u

open CategoryTheory

namespace AlgebraicGeometry

instance : (topologically IsOpenMap).RespectsIso :=
  topologically_respectsIso _ (fun f ↦ f.isOpenMap) (fun _ _ hf hg ↦ hg.comp hf)

instance : IsZariskiLocalAtSource (topologically IsOpenMap) :=
  topologically_isZariskiLocalAtSource' (fun _ ↦ _) fun _ _ _ hU _ ↦ hU.isOpenMap_iff_comp

instance : (topologically GeneralizingMap).RespectsIso :=
  topologically_respectsIso _ (fun f ↦ f.isOpenEmbedding.generalizingMap
    f.isOpenEmbedding.isOpen_range.stableUnderGeneralization) (fun _ _ hf hg ↦ hf.comp hg)

instance : IsZariskiLocalAtSource (topologically GeneralizingMap) :=
  topologically_isZariskiLocalAtSource' (fun _ ↦ _) fun _ _ _ hU _ ↦ hU.generalizingMap_iff_comp

instance : IsZariskiLocalAtTarget (topologically GeneralizingMap) :=
  topologically_isZariskiLocalAtTarget' (fun _ ↦ _) fun _ _ _ hU _ ↦
    hU.generalizingMap_iff_restrictPreimage

section Surjective

instance : MorphismProperty.IsStableUnderComposition @Surjective.{u} where
  comp_mem _ _ hf hg := ⟨hg.1.comp hf.1⟩

end Surjective

end AlgebraicGeometry
