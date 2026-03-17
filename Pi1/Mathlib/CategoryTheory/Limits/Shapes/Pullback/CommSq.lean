import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

namespace CategoryTheory

open Limits

lemma Limits.isPullback_map_fst_fst {C : Type*} [Category C] [HasPullbacks C]
    {X Y Z U S : C} (f : X ⟶ S) (g : Y ⟶ S) (i : Z ⟶ S) (h : U ⟶ pullback i g) :
    IsPullback
      (pullback.map (pullback.snd f g) (h ≫ pullback.snd i g) f i
        (pullback.fst f g) (h ≫ pullback.fst i g) g
        pullback.condition.symm (by simp [pullback.condition]))
      (pullback.snd (pullback.snd f g) (h ≫ pullback.snd i g))
      (pullback.snd f i)
      (h ≫ pullback.fst i g) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro c
    exact pullback.lift (pullback.lift (c.fst ≫ pullback.fst _ _) (c.snd ≫ h ≫ pullback.snd _ _)
          (by simp [pullback.condition, c.condition_assoc])) c.snd (by simp)
  · intro c
    apply pullback.hom_ext <;> simp [c.condition]
  · intro c
    simp
  · intro c m hfst hsnd
    apply pullback.hom_ext
    · apply pullback.hom_ext
      simp [← hfst]
      simp [← hsnd, pullback.condition]
    · simpa

end CategoryTheory
