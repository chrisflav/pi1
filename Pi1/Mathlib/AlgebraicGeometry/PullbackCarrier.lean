import Mathlib.AlgebraicGeometry.PullbackCarrier

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

lemma exists_preimage_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (x : X) (y : Y)
    (hxy : f.base x = g.base y) :
    ∃ (p : P), fst.base p = x ∧ snd.base p = y := by
  let e := h.isoPullback
  obtain ⟨z, hzl, hzr⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback x y hxy
  use h.isoPullback.inv.base z
  simp [← Scheme.comp_base_apply, hzl, hzr]

lemma image_preimage_eq_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (s : Set X) :
    snd.base '' (fst.base ⁻¹' s) = g.base ⁻¹' (f.base '' s) := by
  refine subset_antisymm ?_ (fun x hx ↦ ?_)
  · rw [Set.image_subset_iff, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.comp_base, ← h.1.1]
    rw [Scheme.comp_base, TopCat.coe_comp, ← Set.image_subset_iff, Set.image_comp]
    exact Set.image_mono (Set.image_preimage_subset _ _)
  · obtain ⟨y, hy, heq⟩ := hx
    obtain ⟨o, hl, hr⟩ := exists_preimage_of_isPullback h y x heq
    use o
    simpa [hl, hr]

instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [Surjective g] :
    Surjective (pullback.fst f g) :=
  MorphismProperty.pullback_fst _ _ inferInstance

instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [Surjective f] :
    Surjective (pullback.snd f g) :=
  MorphismProperty.pullback_snd _ _ inferInstance

end AlgebraicGeometry
