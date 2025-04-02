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

-- TODO: move me
lemma TopologicalSpace.IsOpenCover.generalizingMap_iff_comp {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} {ι : Type*} {U : ι → Opens X} (hU : IsOpenCover U) :
    GeneralizingMap f ↔ ∀ i, GeneralizingMap (f ∘ ((↑) : U i → X)) := by
  refine ⟨fun hf ↦ fun i ↦
      ((U i).isOpenEmbedding'.generalizingMap
        (U i).isOpenEmbedding'.isOpen_range.stableUnderGeneralization).comp hf,
    fun hf ↦ fun x y h ↦ ?_⟩
  obtain ⟨i, hi⟩ := hU.exists_mem x
  replace h : y ⤳ (f ∘ ((↑) : U i → X)) ⟨x, hi⟩ := h
  obtain ⟨a, ha, rfl⟩ := hf i h
  use a.val
  simp [ha.map (U i).isOpenEmbedding'.continuous]

lemma GeneralizingMap.restrictPreimage {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y}
    (hf : GeneralizingMap f) (s : Set Y) :
    GeneralizingMap (s.restrictPreimage f) := by
  intro x y h
  obtain ⟨a, ha, hy⟩ := hf (h.map <| continuous_subtype_val (p := s))
  use ⟨a, by simp [hy]⟩
  simp [hy, subtype_specializes_iff, ha]

lemma TopologicalSpace.IsOpenCover.generalizingMap_iff_restrictPreimage
    {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} {ι : Type*} {U : ι → Opens Y} (hU : IsOpenCover U) :
    GeneralizingMap f ↔ ∀ i, GeneralizingMap ((U i).1.restrictPreimage f) := by
  refine ⟨fun hf ↦ fun i ↦ hf.restrictPreimage _, fun hf ↦ fun x y h ↦ ?_⟩
  obtain ⟨i, hx⟩ := hU.exists_mem (f x)
  have h : (⟨y, (U i).2.stableUnderGeneralization h hx⟩ : U i) ⤳
    (U i).1.restrictPreimage f ⟨x, hx⟩ := by rwa [subtype_specializes_iff]
  obtain ⟨a, ha, heq⟩ := hf i h
  refine ⟨a, ?_, congr(($heq).val)⟩
  rwa [subtype_specializes_iff] at ha

end

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

end AlgebraicGeometry
