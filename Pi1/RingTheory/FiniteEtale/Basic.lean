import Mathlib
import Pi1.RingTheory.TotallySplit
import Pi1.Mathlib.RingTheory.RingHom.Etale

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

lemma IsUnit.tmul {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R T] [Algebra R S] {s : S} {t : T} (hs : IsUnit s) (ht : IsUnit t) :
    IsUnit (s ⊗ₜ[R] t) :=
  sorry

lemma RingHom.OfLocalizationSpan.of_exists_of_isPrime'
    {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hP : RingHom.OfLocalizationSpan P)
    (hPi : RingHom.RespectsIso P)
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p,
      P (algebraMap (Localization.Away r) (Localization.Away r ⊗[R] S))) :
    P (algebraMap R S) := by
  apply hP.of_exists_of_isPrime
  intro p hp
  obtain ⟨r, hr, hf⟩ := H p
  refine ⟨r, hr, ?_⟩
  have : IsLocalization.Away ((Algebra.ofId R S) r) (Localization.Away ((algebraMap R S) r)) :=
    inferInstanceAs <| IsLocalization.Away (algebraMap R S r) _
  let u : Localization.Away r →ₐ[R] Localization.Away ((algebraMap R S) r) :=
    Localization.awayMapₐ (Algebra.ofId R S) r
  let v : S →ₐ[R] Localization.Away ((algebraMap R S) r) :=
    IsScalarTower.toAlgHom R S (Localization.Away ((algebraMap R S) r))
  let e : Localization.Away r ⊗[R] S ≃+* Localization.Away (algebraMap R S r) :=
    RingEquiv.ofRingHom
      (Algebra.TensorProduct.lift (R := R) (S := R) u v fun _ _ ↦ Commute.all _ _).toRingHom
      (IsLocalization.Away.lift (algebraMap R S r)
        (g := Algebra.TensorProduct.includeRight.toRingHom) (by
          simp only [AlgHom.toRingHom_eq_coe, coe_coe, AlgHom.commutes,
            Algebra.TensorProduct.algebraMap_apply]
          exact (IsLocalization.Away.algebraMap_isUnit r).tmul isUnit_one))
      (by
        apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R S r))
        ext x
        simp [v])
      (by
        ext x
        simp only [AlgHom.toRingHom_eq_coe, coe_comp, coe_coe, Function.comp_apply, id_apply, v]
        induction x with
        | zero => simp
        | add x y hx hy => simp [hx, hy]
        | tmul x y =>
        simp [u, v, Localization.awayMapₐ, IsLocalization.Away.mapₐ, IsLocalization.Away.map]
        sorry)
  have : Localization.awayMap (algebraMap R S) r =
      e.toRingHom.comp (algebraMap (Localization.Away r) (Localization.Away r ⊗[R] S)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext x
    simp [e, Localization.awayMap, IsLocalization.Away.map, ← IsScalarTower.algebraMap_apply]
  rw [this]
  exact hPi.left _ _ hf

lemma Algebra.etale_of_exists_cover' {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S]
    (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p,
      Algebra.Etale (Localization.Away r) (Localization.Away r ⊗[R] S)) : Algebra.Etale R S := by
  rw [← RingHom.etale_algebraMap_iff]
  apply RingHom.Etale.ofLocalizationSpan.of_exists_of_isPrime'
  · exact RingHom.Etale.respectsIso
  · intro p hp
    obtain ⟨r, hr, hf⟩ := H p
    use r, hr
    rwa [RingHom.etale_algebraMap_iff]

lemma Algebra.finite_etale_of_exists_cover' {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S]
    (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p,
      Algebra.FiniteEtale (Localization.Away r) (Localization.Away r ⊗[R] S)) :
    Algebra.FiniteEtale R S :=
  sorry

end Etale
