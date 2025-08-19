import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.RingHom.Locally
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.RingHom.Unramified
import Pi1.Mathlib.RingTheory.RingHom.Smooth
import Pi1.RingTheory.Smooth.StandardSmoothSmooth

universe u

namespace Algebra

variable {ι : Type*}

@[nontriviality]
instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Subsingleton S]
    (n : ℕ) : IsStandardSmoothOfRelativeDimension n R S := by
  let P' : Generators R S (Fin (n + 1)) := .ofSurjective (fun _ : Fin (n + 1) ↦ 0) <| by
    intro s
    exact ⟨0, Subsingleton.elim _ _⟩
  have hker : P'.ker = ⊤ := le_antisymm le_top (fun x _ ↦ Subsingleton.elim _ _)
  let P : SubmersivePresentation R S (Fin (n + 1)) Unit :=
    { __ := P'
      relation _ := 1
      span_range_relation_eq_ker := by simp [hker]
      map _ := (0 : Fin (n + 1))
      map_inj _ _ _ := rfl
      jacobian_isUnit := isUnit_of_subsingleton _ }
  refine ⟨Fin (n + 1), Unit, inferInstance, inferInstance, P, ?_⟩
  simp [Presentation.dimension]

instance (priority := low) {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsStandardSmooth R S] [FormallyUnramified R S] :
    IsStandardSmoothOfRelativeDimension 0 R S := by
  nontriviality S
  obtain ⟨α, β, _, _, ⟨P⟩⟩ := IsStandardSmooth.out (R := R) (S := S)
  have : Module.rank S (Ω[S⁄R]) = P.dimension := P.rank_kaehlerDifferential
  have : Subsingleton (Ω[S⁄R]) := inferInstance
  refine ⟨α, β, inferInstance, inferInstance, P, ?_⟩
  apply Nat.cast_injective (R := Cardinal)
  rw [← P.rank_kaehlerDifferential, rank_subsingleton', CharP.cast_eq_zero]

end Algebra

namespace RingHom

lemma Etale.eq_and :
    @Etale = fun R S (_ : CommRing R) (_ : CommRing S) f ↦ f.FormallyUnramified ∧ f.Smooth := by
  ext
  rw [etale_iff_formallyUnramified_and_smooth]

theorem Etale.iff_locally_isStandardSmoothOfRelativeDimension
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    f.Etale ↔ Locally (IsStandardSmoothOfRelativeDimension 0) f := by
  rw [etale_iff_formallyUnramified_and_smooth, smooth_iff_locally_isStandardSmooth]
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
