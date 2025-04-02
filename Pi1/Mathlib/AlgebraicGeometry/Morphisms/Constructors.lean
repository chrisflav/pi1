import Mathlib.AlgebraicGeometry.Morphisms.Constructors
import Pi1.Mathlib.CategoryTheory.MorphismProperty.Limits

universe u

open TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry

variable (P : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β], (α → β) → Prop)

lemma topologically_isLocalAtSource [(topologically P).RespectsIso]
    (hP₁ : ∀ {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
      (_ : Continuous f) (U : Opens X), P f → P (f ∘ ((↑) : U → X)))
    (hP₂ : ∀ {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
      (_ : Continuous f) {ι : Type u} (U : ι → Opens X),
      IsOpenCover U → (∀ i, P (f ∘ ((↑) : U i → X))) → P f) :
    IsLocalAtSource (topologically P) := by
  apply IsLocalAtSource.mk'
  · introv hf
    exact hP₁ f.base f.continuous _ hf
  · introv hU hf
    exact hP₂ f.base f.continuous _ hU hf

/-- A variant of `topologically_isLocalAtSource`
that takes one iff statement instead of two implications. -/
lemma topologically_isLocalAtSource' [(topologically P).RespectsIso]
    (hP : ∀ {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) {ι : Type u}
      (U : ι → Opens X) (_ : IsOpenCover U) (_ : Continuous f),
      P f ↔ (∀ i, P (f ∘ ((↑) : U i → X)))) :
    IsLocalAtSource (topologically P) := by
  refine topologically_isLocalAtSource P ?_ (fun f hf _ U hU hf' ↦ (hP f U hU hf).mpr hf')
  introv hf hs
  refine (hP f (![⊤, U] ∘ Equiv.ulift) ?_ hf).mp hs ⟨1⟩
  rw [IsOpenCover, ← top_le_iff]
  exact le_iSup (![⊤, U] ∘ Equiv.ulift) ⟨0⟩

theorem universally_isLocalAtSource (P : MorphismProperty Scheme)
    [IsLocalAtSource P] : IsLocalAtSource P.universally := by
  refine ⟨inferInstance, ?_⟩
  intro X Y f 𝒰
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · intro i 
    apply MorphismProperty.universally_mk'
    intro T g _
    rw [← P.cancel_left_of_respectsIso (pullbackLeftPullbackSndIso g f _).hom,
      pullbackLeftPullbackSndIso_hom_fst]
    exact IsLocalAtSource.comp (hf _ _ _ (IsPullback.of_hasPullback ..)) _
  · apply MorphismProperty.universally_mk'
    intro T g _
    rw [IsLocalAtSource.iff_of_openCover (P := P) (𝒰.pullbackCover <| pullback.snd g f)]
    intro i
    rw [𝒰.pullbackCover_map, ← pullbackLeftPullbackSndIso_hom_fst, P.cancel_left_of_respectsIso]
    exact hf i _ _ _ (IsPullback.of_hasPullback ..)


end AlgebraicGeometry
