import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.Constructors

section

-- TODO: move me
lemma TopologicalSpace.IsOpenCover.isOpenMap_iff_comp {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} {ι : Type*} {U : ι → Opens X} (hU : IsOpenCover U) :
    IsOpenMap f ↔ ∀ i, IsOpenMap (f ∘ ((↑) : U i → X)) := by
  refine ⟨fun hf ↦ fun i ↦ hf.comp (U i).isOpenEmbedding'.isOpenMap, fun hf ↦ ?_⟩
  intro V hV
  have : f '' V = ⋃ i, (f ∘ ((↑) : U i → X)) '' ((↑) ⁻¹' V) := by
    simp_rw [Set.image_comp, Set.image_preimage_eq_inter_range, ← Set.image_iUnion,
      Subtype.range_coe_subtype, SetLike.setOf_mem_eq, hU.iUnion_inter]
  rw [this]
  apply isOpen_iUnion
  intro i
  apply hf i
  exact isOpen_induced hV

end

namespace AlgebraicGeometry

instance : (topologically IsOpenMap).RespectsIso :=
  topologically_respectsIso _ (fun f ↦ f.isOpenMap) (fun _ _ hf hg ↦ hg.comp hf)

instance : IsLocalAtSource (topologically IsOpenMap) :=
  topologically_isLocalAtSource' (fun _ ↦ _) fun _ _ _ hU _ ↦ hU.isOpenMap_iff_comp

end AlgebraicGeometry
