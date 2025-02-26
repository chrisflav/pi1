import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Support
import Pi1.Mathlib.Algebra.Module.LocalizedModule.Basic

universe u

open TensorProduct

section rankAtStalk

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

lemma Module.rankAtStalk_eq_zero_of_subsingleton [Subsingleton M] :
    rankAtStalk (R := R) M = 0 := by
  ext p
  exact Module.finrank_zero_of_subsingleton

lemma Module.rankAtStalk_eq_zero_iff_subsingleton [Module.Flat R M]
      [Module.FinitePresentation R M] :
    rankAtStalk (R := R) M = 0 ↔ Subsingleton M := by
  refine ⟨fun h ↦ ?_, fun _ ↦ rankAtStalk_eq_zero_of_subsingleton⟩
  simp_rw [← Module.support_eq_empty_iff (R := R), Set.eq_empty_iff_forall_not_mem,
    Module.not_mem_support_iff]
  intro p
  have : Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) :=
    free_of_flat_of_isLocalRing
  apply Module.subsingleton_of_rank_zero (R := (Localization.AtPrime p.asIdeal))
  have hr : finrank (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) = 0 :=
    (funext_iff.mp h) p
  simp [← Module.finrank_eq_rank, hr]

lemma Module.rankAtStalk_pi {ι : Type*} [Finite ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Flat R (M i)]
    [∀ i, Module.FinitePresentation R (M i)] (p : PrimeSpectrum R) :
    rankAtStalk (∀ i, M i) p = ∑ᶠ i, rankAtStalk (M i) p := by
  cases nonempty_fintype ι
  let f : (Π i, M i) →ₗ[R] Π i, LocalizedModule p.asIdeal.primeCompl (M i) :=
    LinearMap.pi
      (fun i ↦ LocalizedModule.mkLinearMap p.asIdeal.primeCompl (M i) ∘ₗ LinearMap.proj i)
  let e : LocalizedModule p.asIdeal.primeCompl (Π i, M i) ≃ₗ[Localization.AtPrime p.asIdeal]
      (Π i, LocalizedModule p.asIdeal.primeCompl (M i)) :=
    (IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl _) f).extendScalarsOfIsLocalization
      p.asIdeal.primeCompl _
  dsimp [rankAtStalk]
  rw [e.finrank_eq]
  have (i : ι) : Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl (M i)) :=
    free_of_flat_of_isLocalRing
  rw [Module.finrank_pi_fintype, finsum_eq_sum_of_fintype]

lemma Module.rankAtStalk_prod (M N : Type*) [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N]
    [Module.Flat R M] [Module.Flat R N]
    [Module.FinitePresentation R M] [Module.FinitePresentation R N]
    (p : PrimeSpectrum R) :
    rankAtStalk (M × N) p = rankAtStalk M p + rankAtStalk N p := by
  let e : (LocalizedModule p.asIdeal.primeCompl (M × N)) ≃ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule p.asIdeal.primeCompl M × LocalizedModule p.asIdeal.primeCompl N :=
    (IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl _)
      (LinearMap.prodMap (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N))).extendScalarsOfIsLocalization
      p.asIdeal.primeCompl _
  dsimp [rankAtStalk]
  have : Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl N) :=
    free_of_flat_of_isLocalRing
  have : Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) :=
    free_of_flat_of_isLocalRing
  simp [e.finrank_eq]

lemma Module.rankAtStalk_tensorProduct {S : Type*} [CommRing S] [Algebra R S]
    [Module.Flat R M] [Module.FinitePresentation R M]
    (p : PrimeSpectrum S) :
    rankAtStalk (S ⊗[R] M) p = rankAtStalk M ((algebraMap R S).specComap p) := by
  dsimp [rankAtStalk]
  let q : PrimeSpectrum R := ((algebraMap R S).specComap p)
  letI : Algebra (Localization.AtPrime q.asIdeal) (Localization.AtPrime p.asIdeal) :=
    (Localization.localRingHom q.asIdeal p.asIdeal (algebraMap R S) rfl).toAlgebra
  have : IsScalarTower R (Localization.AtPrime q.asIdeal) (Localization.AtPrime p.asIdeal) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    simp [RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map,
      IsScalarTower.algebraMap_apply R S (Localization.AtPrime p.asIdeal)]
  let e₁ : (LocalizedModule p.asIdeal.primeCompl (S ⊗[R] M)) ≃ₗ[Localization.AtPrime p.asIdeal]
      (Localization.AtPrime p.asIdeal) ⊗[S] (S ⊗[R] M) := by
    refine (IsBaseChange.equiv (f := ?_) ?_).symm
    · exact LocalizedModule.mkLinearMap p.asIdeal.primeCompl (S ⊗[R] M)
    · apply IsLocalizedModule.isBaseChange p.asIdeal.primeCompl
  let e₂ : (LocalizedModule q.asIdeal.primeCompl M) ≃ₗ[Localization.AtPrime q.asIdeal]
      (Localization.AtPrime q.asIdeal) ⊗[R] M := by
    refine (IsBaseChange.equiv (f := ?_) ?_).symm
    · exact LocalizedModule.mkLinearMap q.asIdeal.primeCompl M
    · apply IsLocalizedModule.isBaseChange q.asIdeal.primeCompl
  let e : (LocalizedModule p.asIdeal.primeCompl (S ⊗[R] M)) ≃ₗ[Localization.AtPrime p.asIdeal]
      (Localization.AtPrime p.asIdeal) ⊗[Localization.AtPrime q.asIdeal]
        (LocalizedModule q.asIdeal.primeCompl M) :=
    e₁ ≪≫ₗ (TensorProduct.AlgebraTensorModule.cancelBaseChange
        R S _ (Localization.AtPrime p.asIdeal) M) ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange
        R (Localization.AtPrime q.asIdeal) _ _ M).symm ≪≫ₗ
        (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) e₂.symm)
  rw [e.finrank_eq]
  have : Free (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl M) :=
    free_of_flat_of_isLocalRing
  apply Module.finrank_baseChange

noncomputable
def IsLocalizedModule.mapEquiv {R : Type*} [CommSemiring R] (S : Submonoid R)
    (A : Type*) {M N M' N' : Type*} [CommSemiring A] [Algebra R A] [IsLocalization S A]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid M'] [AddCommMonoid N']
    [Module R M] [Module R N] [Module R M'] [Module R N']
    [Module A M'] [Module A N'] [IsScalarTower R A M'] [IsScalarTower R A N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N') [IsLocalizedModule S f] [IsLocalizedModule S g]
    (e : M ≃ₗ[R] N) :
    M' ≃ₗ[A] N' :=
  LinearEquiv.ofLinear
    (IsLocalizedModule.mapExtendScalars S f g A e)
    (IsLocalizedModule.mapExtendScalars S g f A e.symm)
    (by
      apply LinearMap.restrictScalars_injective R
      apply IsLocalizedModule.linearMap_ext S g g
      ext
      simp)
    (by
      apply LinearMap.restrictScalars_injective R
      apply IsLocalizedModule.linearMap_ext S f f
      ext
      simp)

lemma Module.rankAtStalk_eq_of_equiv {N : Type*} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    rankAtStalk (R := R) M = rankAtStalk N := by
  ext p
  dsimp [rankAtStalk]
  exact IsLocalizedModule.mapEquiv p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl N) e |>.finrank_eq

lemma Module.rankAtStalk_eq_finrank_of_free [Module.Free R M] :
    rankAtStalk (R := R) M = Module.finrank R M := by
  ext p
  simp [rankAtStalk, Module.finrank_of_isLocalizedModule_of_free _ p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)]

lemma Module.nontrivial_of_rankAtStalk_gt_zero (p : PrimeSpectrum R)
    (h : rankAtStalk (R := R) M p > 0) :
    Nontrivial M := by
  by_contra! hn
  have : Subsingleton M := not_nontrivial_iff_subsingleton.mp hn
  have := Module.finrank_zero_of_subsingleton (R := Localization.AtPrime p.asIdeal)
    (M := LocalizedModule p.asIdeal.primeCompl M)
  simp [rankAtStalk, this] at h

@[simp]
lemma Module.rankAtStalk_self [Nontrivial R] : rankAtStalk (R := R) R = 1 := by
  simp [rankAtStalk_eq_finrank_of_free]

end rankAtStalk

open IsLocalRing

lemma Module.rankAtStalk_eq {R M : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [Module.Flat R M] (p : PrimeSpectrum R) :
    Module.rankAtStalk M p = Module.finrank p.asIdeal.ResidueField
        (p.asIdeal.ResidueField ⊗[R] M) := by
  let k := p.asIdeal.ResidueField
  have : Free (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⊗[R] M) :=
    free_of_flat_of_isLocalRing
  let e₁ : LocalizedModule p.asIdeal.primeCompl M ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal ⊗[R] M :=
    (IsLocalizedModule.isBaseChange p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)).equiv.symm
  let e₂ : k ⊗[Localization.AtPrime p.asIdeal] (Localization.AtPrime p.asIdeal ⊗[R] M) ≃ₗ[k]
      k ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange _ _ _ _ _
  simp only [rankAtStalk]
  rw [← e₂.finrank_eq, finrank_baseChange, e₁.finrank_eq]

lemma Algebra.specComap_surjective_of_rankAtStalk_pos {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] [Module.FinitePresentation R S]
    (h : ∀ p, 0 < Module.rankAtStalk (R := R) S p) :
    Function.Surjective (algebraMap R S).specComap := by
  intro p
  let k := p.asIdeal.ResidueField
  have : Nontrivial R := by
    refine ⟨0, 1, fun h ↦ p.2.ne_top ?_⟩
    simp [Ideal.eq_top_iff_one p.asIdeal, ← h]
  have : Nontrivial (k ⊗[R] S) := by
    apply Module.nontrivial_of_finrank_pos (R := k)
    rw [← Module.rankAtStalk_eq]
    apply h
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (k ⊗[R] S)
  use (TensorProduct.includeRight).specComap ⟨m, hm.isPrime⟩
  rw [← PrimeSpectrum.specComap_comp_apply, ← TensorProduct.includeLeftRingHom_comp_algebraMap,
    PrimeSpectrum.specComap_comp_apply]
  ext : 1
  simp [Ideal.eq_bot_of_prime, k, ← RingHom.ker_eq_comap_bot]

-- in PR
lemma Module.FaithfullyFlat.of_flat_of_specComap_surjective {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [Module.Flat R S]
    (h : Function.Surjective (algebraMap R S).specComap) :
    Module.FaithfullyFlat R S :=
  sorry
