import Mathlib
import Pi1.RingTheory.TotallySplit

open TensorProduct

universe u

class Algebra.FiniteEtale (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  extends Algebra.Etale R S, Module.Finite R S : Prop

lemma Algebra.FiniteEtale.of_equiv {R S S' : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteEtale R S] [CommRing S'] [Algebra R S'] (e : S ≃ₐ[R] S') :
    Algebra.FiniteEtale R S' := by
  have := Algebra.Etale.of_equiv e
  have := Module.Finite.equiv e.toLinearEquiv
  constructor

instance (n : ℕ) (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsSplitOfRank n R S] : Algebra.FiniteEtale R S := by
  obtain ⟨e⟩ := Algebra.IsSplitOfRank.nonempty_algEquiv_fun n R S
  have : Algebra.FiniteEtale R (Fin n → R) := by constructor
  exact Algebra.FiniteEtale.of_equiv e.symm

section

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

lemma RingHom.OfLocalizationSpan.of_exists_of_isPrime
    (hP : RingHom.OfLocalizationSpan P)
    {R S : Type u}
    [CommRing R] [CommRing S] (f : R →+* S)
    (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p, P (Localization.awayMap f r)) :
    P f := by
  have := H
  choose u hu₁ hu₂ using this
  apply hP f (Set.range (fun p : PrimeSpectrum R ↦ u p.asIdeal))
  · rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
    rw [_root_.eq_top_iff]
    rintro p -
    simp only [TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.carrier_eq_coe,
      PrimeSpectrum.basicOpen_eq_zeroLocus_compl, TopologicalSpace.Opens.coe_mk, Set.mem_iUnion,
      Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]
    use p
    apply hu₁
  · simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    rintro ⟨p, ⟨p, rfl⟩⟩
    apply hu₂


section Etale

def RingHom.Etale {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  Algebra.Etale R S

lemma RingHom.etale_algebraMap_iff {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    (algebraMap R S).Etale ↔ Algebra.Etale R S := by
  simp only [RingHom.Etale]
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

lemma RingHom.FormallyEtale.of_localRingHom {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
      (hf : f.FinitePresentation)
      (H : ∀ (p : Ideal S) [p.IsPrime], (Localization.localRingHom _ p f rfl).FormallyEtale) :
    f.FormallyEtale :=
  sorry

lemma RingHom.Etale.ofLocalizationSpan :
    RingHom.OfLocalizationSpan RingHom.Etale :=
  sorry

lemma RingHom.FormallyEtale.ofLocalizationSpan :
    RingHom.OfLocalizationSpan RingHom.FormallyEtale :=
  sorry

lemma RingHom.FormallyEtale.of_exists_of_prime {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FinitePresentation)
    (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p,
      (Localization.awayMap f r).FormallyEtale) :
    f.FormallyEtale :=
  sorry

lemma RingHom.FormallyEtale.respectsIso :
    RingHom.RespectsIso RingHom.FormallyEtale :=
  sorry

lemma Algebra.finite_etale_of_exists_cover' {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S]
    (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p,
      Algebra.FiniteEtale (Localization.Away r) (Localization.Away r ⊗[R] S)) :
    Algebra.FiniteEtale R S :=
  sorry

def AlgHom.extendScalarsOfIsLocalization {R S T A : Type*}
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra R A]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra S A] [IsScalarTower R S A]
    (M : Submonoid R) [IsLocalization M S]
    (P : Submonoid S) [IsLocalization P T]
    (f : T →ₐ[R] A) : T →ₐ[S] A where
  __ := f
  commutes' s := by
    simp
    sorry

@[simp]
lemma AlgHom.extendScalarsOfIsLocalization_apply {R S T A : Type*}
    [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra R A]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra S A] [IsScalarTower R S A]
    (M : Submonoid R) [IsLocalization M S]
    (P : Submonoid S) [IsLocalization P T]
    (f : T →ₐ[R] A) (t : T) :
    f.extendScalarsOfIsLocalization M P t = f t :=
  rfl

--lemma Algebra.TensorProduct.isUnit_tmul {R S T : Type*} [CommRing R] [CommRing S]
--    [CommRing T]

lemma Algebra.etale_of_exists_cover' {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S]
    (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p,
      Algebra.Etale (Localization.Away r) (Localization.Away r ⊗[R] S)) : Algebra.Etale R S := by
  rw [← RingHom.etale_algebraMap_iff]
  apply RingHom.Etale.ofLocalizationSpan.of_exists_of_isPrime
  intro p hp
  obtain ⟨r, hr, h⟩ := H p
  refine ⟨r, hr, ?_⟩
  algebraize [Localization.awayMap (algebraMap R S) r]
  have : IsScalarTower R (Localization.Away r) (Localization.Away ((algebraMap R S) r)) := sorry
  let e : Localization.Away r ⊗[R] S ≃ₐ[Localization.Away r]
      Localization.Away ((algebraMap R S) r) :=
    AlgEquiv.ofAlgHom
      (Algebra.TensorProduct.lift (Algebra.ofId _ _) (IsScalarTower.toAlgHom _ _ _)
        fun _ _ ↦ Commute.all _ _)
      --((IsLocalization.liftAlgHom _).extendScalarsOfIsLocalization (.powers r)
      --  (.powers (algebraMap R S r)))
      ⟨IsLocalization.Away.lift (algebraMap R S r) (g := TensorProduct.includeRight.toRingHom)
        (by simp; sorry), sorry⟩
      (by
        apply AlgHom.coe_ringHom_injective
        apply IsLocalization.ringHom_ext (M := .powers (algebraMap R S r))
        ext x
        simp)
      (by ext; simp;)
  rw [RingHom.Etale]
  apply Algebra.Etale.of_equiv e

end Etale
