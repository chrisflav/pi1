import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Support
import Pi1.Mathlib.Algebra.Module.LocalizedModule.Basic

universe u

open TensorProduct

section rankAtStalk

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

lemma PrimeSpectrum.nontrivial (p : PrimeSpectrum R) : Nontrivial R := by
  refine ⟨0, 1, fun h ↦ p.2.ne_top ?_⟩
  simp [Ideal.eq_top_iff_one p.asIdeal, ← h]

/-- A prime `p` is in the range of `Spec S → Spec R` if the fiber over `p` is nontrivial. -/
lemma PrimeSpectrum.mem_rangeComap_iff_nontrivial {S : Type*} [CommRing S]
    [Algebra R S] (p : PrimeSpectrum R) :
    Nontrivial (p.asIdeal.ResidueField ⊗[R] S) ↔ p ∈ Set.range (algebraMap R S).specComap := by
  let k := p.asIdeal.ResidueField
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal (k ⊗[R] S)
    use (Algebra.TensorProduct.includeRight).specComap ⟨m, hm.isPrime⟩
    ext : 1
    rw [← PrimeSpectrum.specComap_comp_apply,
      ← Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap, specComap_comp_apply]
    simp [Ideal.eq_bot_of_prime, k, ← RingHom.ker_eq_comap_bot]
  · obtain ⟨q, rfl⟩ := h
    let f : k ⊗[R] S →ₐ[R] q.asIdeal.ResidueField :=
      Algebra.TensorProduct.lift (Ideal.ResidueField.mapₐ _ _ rfl)
        (IsScalarTower.toAlgHom _ _ _) (fun _ _ ↦ Commute.all ..)
    exact RingHom.domain_nontrivial f.toRingHom

namespace Module

@[simp]
lemma rankAtStalk_eq_zero_of_subsingleton [Subsingleton M] :
    rankAtStalk (R := R) M = 0 := by
  ext p
  exact Module.finrank_zero_of_subsingleton

lemma nontrivial_of_rankAtStalk_pos (p : PrimeSpectrum R) (h : 0 < rankAtStalk (R := R) M) :
    Nontrivial M := by
  by_contra! hn
  have : Subsingleton M := not_nontrivial_iff_subsingleton.mp hn
  have := finrank_zero_of_subsingleton (R := Localization.AtPrime p.asIdeal)
    (M := LocalizedModule p.asIdeal.primeCompl M)
  simp [rankAtStalk, this] at h

lemma rankAtStalk_eq_of_equiv {N : Type*} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    rankAtStalk (R := R) M = rankAtStalk N := by
  ext p
  exact IsLocalizedModule.mapEquiv p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N)
    (Localization.AtPrime p.asIdeal) e |>.finrank_eq

/-- If `M` is `R`-free, its rank at stalks is constant and agrees with the `R`-rank of `M`. -/
@[simp]
lemma rankAtStalk_eq_finrank_of_free [Module.Free R M] :
    rankAtStalk (R := R) M = Module.finrank R M := by
  ext p
  simp [rankAtStalk, finrank_of_isLocalizedModule_of_free _ p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)]

@[simp]
lemma rankAtStalk_self [Nontrivial R] : rankAtStalk (R := R) R = 1 := by
  simp [rankAtStalk_eq_finrank_of_free]

open LocalizedModule Localization

instance {R : Type*} [CommSemiring R] (S : Submonoid R)
    (M : Type*) [AddCommMonoid M] [Module R M] [Module.Finite R M] :
    Module.Finite (Localization S) (LocalizedModule S M) :=
  Module.Finite.of_isLocalizedModule S (LocalizedModule.mkLinearMap S M)

/-- The rank of `Π i, M i` at a prime `p` is the sum of the ranks of `M i` at `p`. -/
lemma rankAtStalk_pi {ι : Type*} [Finite ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Flat R (M i)]
    [∀ i, Module.Finite R (M i)] (p : PrimeSpectrum R) :
    rankAtStalk (Π i, M i) p = ∑ᶠ i, rankAtStalk (M i) p := by
  cases nonempty_fintype ι
  let f : (Π i, M i) →ₗ[R] Π i, LocalizedModule p.asIdeal.primeCompl (M i) :=
    .pi (fun i ↦ mkLinearMap p.asIdeal.primeCompl (M i) ∘ₗ LinearMap.proj i)
  let e : LocalizedModule p.asIdeal.primeCompl (Π i, M i) ≃ₗ[Localization.AtPrime p.asIdeal]
      Π i, LocalizedModule p.asIdeal.primeCompl (M i) :=
    IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
      (mkLinearMap _ _) f |>.extendScalarsOfIsLocalization p.asIdeal.primeCompl _
  have (i : ι) : Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl (M i)) :=
    free_of_flat_of_isLocalRing
  simp_rw [rankAtStalk, e.finrank_eq, Module.finrank_pi_fintype, finsum_eq_sum_of_fintype]

variable [Flat R M] [Module.Finite R M]

lemma rankAtStalk_eq_zero_iff_subsingleton :
    rankAtStalk (R := R) M = 0 ↔ Subsingleton M := by
  refine ⟨fun h ↦ ?_, fun _ ↦ rankAtStalk_eq_zero_of_subsingleton⟩
  simp_rw [← support_eq_empty_iff (R := R), Set.eq_empty_iff_forall_not_mem, not_mem_support_iff]
  intro p
  have : Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) :=
    free_of_flat_of_isLocalRing
  apply subsingleton_of_rank_zero (R := Localization.AtPrime p.asIdeal)
  have hr : finrank (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) = 0 :=
    funext_iff.mp h p
  simp [← finrank_eq_rank, hr]

variable (M) in
/-- The rank of `M × N` at `p` is equal to the sum of the ranks. -/
lemma rankAtStalk_prod (N : Type*) [AddCommGroup N] [Module R N]
    [Module.Flat R N] [Module.Finite R N] (p : PrimeSpectrum R) :
    rankAtStalk (M × N) p = rankAtStalk M p + rankAtStalk N p := by
  let e : LocalizedModule p.asIdeal.primeCompl (M × N) ≃ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule p.asIdeal.primeCompl M × LocalizedModule p.asIdeal.primeCompl N :=
    IsLocalizedModule.linearEquiv p.asIdeal.primeCompl (mkLinearMap _ _)
      (.prodMap (mkLinearMap _ M) (mkLinearMap _ N)) |>.extendScalarsOfIsLocalization
      p.asIdeal.primeCompl _
  have : Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl N) :=
    free_of_flat_of_isLocalRing
  have : Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) :=
    free_of_flat_of_isLocalRing
  simp [rankAtStalk, e.finrank_eq]

lemma rankAtStalk_tensorProduct {S : Type*} [CommRing S] [Algebra R S] (p : PrimeSpectrum S) :
    rankAtStalk (S ⊗[R] M) p = rankAtStalk M ((algebraMap R S).specComap p) := by
  let q : PrimeSpectrum R := (algebraMap R S).specComap p
  letI : Algebra (Localization.AtPrime q.asIdeal) (Localization.AtPrime p.asIdeal) :=
    localRingHom q.asIdeal p.asIdeal (algebraMap R S) rfl |>.toAlgebra
  have : IsScalarTower R (Localization.AtPrime q.asIdeal) (Localization.AtPrime p.asIdeal) := by
    refine IsScalarTower.of_algebraMap_eq (fun x ↦ ?_)
    simp [RingHom.algebraMap_toAlgebra, localRingHom_to_map,
      IsScalarTower.algebraMap_apply R S (Localization.AtPrime p.asIdeal)]
  let e : LocalizedModule p.asIdeal.primeCompl (S ⊗[R] M) ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal ⊗[Localization.AtPrime q.asIdeal]
        LocalizedModule q.asIdeal.primeCompl M :=
    LocalizedModule.equivTensorProduct _ _ ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange R S _ _ M) ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange R _ _ _ M).symm ≪≫ₗ
      (AlgebraTensorModule.congr (LinearEquiv.refl _ _)
        (LocalizedModule.equivTensorProduct _ M).symm)
  rw [rankAtStalk, e.finrank_eq]
  have : Free (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl M) :=
    free_of_flat_of_isLocalRing
  apply Module.finrank_baseChange

/-- The rank of a module `M` at a prime `p` is equal to the dimension
of `κ(p) ⊗[R] M` as a `κ(p)`-module. -/
lemma rankAtStalk_eq (p : PrimeSpectrum R) :
    rankAtStalk M p = finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) := by
  let k := p.asIdeal.ResidueField
  have : Free (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⊗[R] M) :=
    free_of_flat_of_isLocalRing
  let e₁ : LocalizedModule p.asIdeal.primeCompl M ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal ⊗[R] M :=
    LocalizedModule.equivTensorProduct p.asIdeal.primeCompl M
  let e₂ : k ⊗[Localization.AtPrime p.asIdeal] (Localization.AtPrime p.asIdeal ⊗[R] M) ≃ₗ[k]
      k ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange _ _ _ _ _
  rw [rankAtStalk, ← e₂.finrank_eq, finrank_baseChange, e₁.finrank_eq]

/-- `M` has positive rank at `p` if the "fiber" over `p` is non-trivial. -/
lemma rankAtStalk_pos_iff_nontrivial (p : PrimeSpectrum R) :
    0 < rankAtStalk M p ↔ Nontrivial (p.asIdeal.ResidueField ⊗[R] M) := by
  rw [rankAtStalk_eq, finrank_pos_iff]

end Module

variable {S : Type*} [CommRing S] [Algebra R S] [Module.Flat R S] [Module.Finite R S]

lemma Algebra.rankAtStalk_pos_iff_mem_range_specComap (p : PrimeSpectrum R) :
    0 < Module.rankAtStalk (R := R) S p ↔ p ∈ Set.range (algebraMap R S).specComap := by
  rw [Module.rankAtStalk_pos_iff_nontrivial, p.mem_rangeComap_iff_nontrivial]

/-- The rank is positive at all stalks if and only if the induced map on prime spectra is
surjective. -/
lemma Algebra.rankAtStalk_pos_iff_specComap_surjective :
    (∀ p, 0 < Module.rankAtStalk (R := R) S p) ↔
      Function.Surjective (algebraMap R S).specComap := by
  simp_rw [rankAtStalk_pos_iff_mem_range_specComap, ← Set.range_eq_univ,
    Set.eq_univ_iff_forall]

end rankAtStalk
