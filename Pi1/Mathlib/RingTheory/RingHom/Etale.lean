import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.RingHom.Locally
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.RingHom.Unramified
import Pi1.Mathlib.RingTheory.RingHom.Smooth
import Pi1.Mathlib.RingTheory.RingHom.And

universe u

namespace Algebra

@[nontriviality]
instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Subsingleton S]
    (n : ℕ) : IsStandardSmoothOfRelativeDimension n R S := by
  let P' : Generators R S := .ofSurjective (fun _ : Fin (n + 1) ↦ 0) <| by
    intro s
    exact ⟨0, Subsingleton.elim _ _⟩
  have hker : P'.ker = ⊤ := le_antisymm le_top (fun x _ ↦ Subsingleton.elim _ _)
  let P : SubmersivePresentation R S :=
    { __ := P'
      rels := Unit
      relation _ := 1
      span_range_relation_eq_ker := by simp [hker]
      map _ := (0 : Fin (n + 1))
      map_inj _ _ _ := rfl
      relations_finite := inferInstance
      jacobian_isUnit := isUnit_of_subsingleton _
      isFinite := ⟨inferInstanceAs <| Finite (Fin (n + 1)), inferInstance⟩ }
  refine ⟨⟨P, ?_⟩⟩
  simp [P, P', Presentation.dimension, Generators.ofSurjective_vars]

instance (priority := low) {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsStandardSmooth R S] [FormallyUnramified R S] :
    IsStandardSmoothOfRelativeDimension 0 R S := by
  nontriviality S
  obtain ⟨P⟩ := IsStandardSmooth.out (R := R) (S := S)
  have : Module.rank S (Ω[S⁄R]) = P.dimension := P.rank_kaehlerDifferential
  have : Subsingleton (Ω[S⁄R]) := inferInstance
  refine ⟨P, ?_⟩
  apply Nat.cast_injective (R := Cardinal)
  rw [← P.rank_kaehlerDifferential, rank_subsingleton', CharP.cast_eq_zero]

end Algebra

namespace RingHom

/-- A ring hom `R →+* S` is etale, if `S` is an etale `R`-algebra. -/
def Etale {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.Etale R S

lemma etale_algebraMap_iff {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    (algebraMap R S).Etale ↔ Algebra.Etale R S := by
  simp only [RingHom.Etale]
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

lemma etale_iff_formallyUnramified_and_smooth {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    f.Etale ↔ f.FormallyUnramified ∧ f.Smooth := by
  algebraize [f]
  simp only [Etale, Smooth, FormallyUnramified]
  constructor
  · intro h
    constructor
    · infer_instance
    · constructor <;> infer_instance
  · intro ⟨h1, h2⟩
    constructor
    · rw [Algebra.FormallyEtale.iff_unramified_and_smooth]
      constructor <;> infer_instance
    · infer_instance

lemma Etale.eq_and :
    @Etale = fun R S (_ : CommRing R) (_ : CommRing S) f ↦ f.FormallyUnramified ∧ f.Smooth := by
  ext
  rw [etale_iff_formallyUnramified_and_smooth]

lemma Etale.isStableUnderBaseChange : IsStableUnderBaseChange Etale := by
  rw [eq_and]
  apply IsStableUnderBaseChange.and
  · exact FormallyUnramified.isStableUnderBaseChange
  · exact Smooth.isStableUnderBaseChange

lemma Etale.propertyIsLocal : PropertyIsLocal Etale := by
  rw [eq_and]
  apply PropertyIsLocal.and
  · exact FormallyUnramified.propertyIsLocal
  · exact Smooth.propertyIsLocal

lemma Etale.respectsIso : RespectsIso Etale :=
  propertyIsLocal.respectsIso

lemma Etale.ofLocalizationSpanTarget : OfLocalizationSpanTarget Etale :=
  propertyIsLocal.ofLocalizationSpanTarget

lemma Etale.ofLocalizationSpan : OfLocalizationSpan Etale :=
  propertyIsLocal.ofLocalizationSpan

lemma Etale.stableUnderComposition : StableUnderComposition Etale := by
  rw [eq_and]
  apply StableUnderComposition.and
  · exact FormallyUnramified.stableUnderComposition
  · exact Smooth.stableUnderComposition

theorem Etale.iff_locally_isStandardSmoothOfRelativeDimension
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    f.Etale ↔ Locally (IsStandardSmoothOfRelativeDimension 0) f := by
  rw [etale_iff_formallyUnramified_and_smooth, ← locally_isStandardSmooth_iff_smooth]
  refine ⟨fun ⟨hr, hs⟩ ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩
  · have : Locally (fun f ↦ f.FormallyUnramified ∧ f.IsStandardSmooth) f := by
      obtain ⟨s, hs, H⟩ := hs
      refine ⟨s, hs, fun t ht ↦ ⟨?_, H t ht⟩⟩
      exact
        FormallyUnramified.propertyIsLocal.StableUnderCompositionWithLocalizationAwayTarget _ t _ hr
    refine locally_of_locally ?_ this
    intro R S _ _ f hf
    algebraize [f]
    have : Algebra.FormallyUnramified R S := hf.1
    have : Algebra.IsStandardSmooth R S := hf.2
    show Algebra.IsStandardSmoothOfRelativeDimension 0 R S
    infer_instance
  · rw [← locally_iff_of_localizationSpanTarget FormallyUnramified.respectsIso
      FormallyUnramified.ofLocalizationSpanTarget]
    refine locally_of_locally ?_ h
    intro R S _ _ f hf
    algebraize [f]
    have : Algebra.IsStandardSmoothOfRelativeDimension 0 R S := hf
    show Algebra.FormallyUnramified R S
    infer_instance
  · refine locally_of_locally ?_ h
    intro R S _ _ f hf
    exact hf.isStandardSmooth

end RingHom
