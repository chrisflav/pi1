import Mathlib
import Pi1.RingTheory.TotallySplit
import Pi1.Mathlib.RingTheory.RingHom.Etale
import Pi1.Mathlib.RingTheory.RingHom.Finite

open TensorProduct

universe u

@[mk_iff]
class Algebra.FiniteEtale (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop
  extends Algebra.Etale R S, Module.Finite R S

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

lemma IsUnit.tmul {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R T] [Algebra R S] {s : S} {t : T} (hs : IsUnit s) (ht : IsUnit t) :
    IsUnit (s ⊗ₜ[R] t) := by
  obtain ⟨s, rfl⟩ := hs
  obtain ⟨t, rfl⟩ := ht
  rw [isUnit_iff_exists_inv]
  use s⁻¹.val ⊗ₜ t⁻¹.val
  simp [Algebra.TensorProduct.one_def]

lemma Algebra.isLocalization_iff_isPushout {R : Type*} [CommSemiring R]
    {S : Type*} (A : Type*) {B : Type*} [CommSemiring S] [Algebra R S]
    [CommSemiring A] [CommSemiring B] [Algebra R A] [Algebra R B]
    [Algebra S B] [Algebra A B] [IsScalarTower R A B] [IsScalarTower R S B]
    (M : Submonoid R) [IsLocalization M A] :
    IsLocalization (Algebra.algebraMapSubmonoid S M) B ↔ IsPushout R S A B := by
  rw [Algebra.IsPushout.comm, Algebra.isPushout_iff, ← isLocalizedModule_iff_isLocalization]
  rw [← isLocalizedModule_iff_isBaseChange (S := M)]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
instance IsLocalization.Away.tensor {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (r : R) (A : Type*) [CommRing A] [Algebra R A] [IsLocalization.Away r A] :
    IsLocalization.Away (algebraMap R S r) (S ⊗[R] A) := by
  simp only [IsLocalization.Away]
  have : Submonoid.powers (algebraMap R S r) = Algebra.algebraMapSubmonoid S (.powers r) := by
    simp [Algebra.algebraMapSubmonoid]
  rw [this, Algebra.isLocalization_iff_isPushout A]
  infer_instance

noncomputable
def IsLocalization.Away.tensorEquiv {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (r : R) (A : Type*) [CommRing A] [Algebra R A] [IsLocalization.Away r A] :
    S ⊗[R] A ≃ₐ[S] Localization.Away (algebraMap R S r) :=
  IsLocalization.algEquiv (Submonoid.powers <| algebraMap R S r) _ _

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
  let e₀ : S ⊗[R] Localization.Away r ≃ₐ[R] Localization.Away (algebraMap R S r) :=
    (IsLocalization.Away.tensorEquiv r (Localization.Away r)).restrictScalars R
  let e : Localization.Away r ⊗[R] S ≃+* Localization.Away (algebraMap R S r) :=
    (Algebra.TensorProduct.comm R _ _).trans e₀
  have : Localization.awayMap (algebraMap R S) r =
      e.toRingHom.comp (algebraMap (Localization.Away r) (Localization.Away r ⊗[R] S)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext x
    simp [e, Localization.awayMap, IsLocalization.Away.map, ← IsScalarTower.algebraMap_apply,
      Algebra.TensorProduct.tmul_one_eq_one_tmul]
  rw [this]
  exact hPi.left _ _ hf

lemma Algebra.Etale.of_exists_of_isPrime {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p,
      Algebra.Etale (Localization.Away r) (Localization.Away r ⊗[R] S)) : Algebra.Etale R S := by
  simp_rw [← RingHom.etale_algebraMap_iff] at H ⊢
  apply RingHom.Etale.ofLocalizationSpan.of_exists_of_isPrime'
  · exact RingHom.Etale.respectsIso
  · intro p hp
    obtain ⟨r, hr, hf⟩ := H p
    use r, hr

lemma Module.Finite.of_exists_of_isPrime {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p,
      Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] S)) : Module.Finite R S := by
  simp_rw [← RingHom.finite_algebraMap_iff] at H ⊢
  apply RingHom.finite_ofLocalizationSpan.of_exists_of_isPrime'
  · exact RingHom.finite_respectsIso
  · intro p hp
    obtain ⟨r, hr, h⟩ := H p
    use r, hr

lemma Algebra.FiniteEtale.of_exists_of_isPrime {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p,
      Algebra.FiniteEtale (Localization.Away r) (Localization.Away r ⊗[R] S)) :
    Algebra.FiniteEtale R S := by
  simp_rw [Algebra.finiteEtale_iff] at H ⊢
  refine ⟨.of_exists_of_isPrime fun p hp ↦ ?_, .of_exists_of_isPrime fun p hp ↦ ?_⟩
  · obtain ⟨r, hr, hf⟩ := H p
    exact ⟨r, hr, hf.1⟩
  · obtain ⟨r, hr, hf⟩ := H p
    exact ⟨r, hr, hf.2⟩
