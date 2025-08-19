import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Pi1.Mathlib.RingTheory.RingHom.Integral

universe u

open TensorProduct

section

/-- If `R → S` is surjective, the multiplication map `S ⊗[R] S → S` is an isomorphism, this
is the algebraic version of closed immersions are monomorphisms. -/
lemma LinearMap.mul'_bijective_of_surjective {R S : Type*} [CommRing R] [CommRing S]
      [Algebra R S] (H : Function.Surjective (algebraMap R S)) :
    Function.Bijective (LinearMap.mul' R S) :=
  have : TensorProduct.CompatibleSMul R S S S := by
    refine ⟨fun r m n ↦ ?_⟩
    obtain ⟨r, rfl⟩ := H r
    obtain ⟨m, rfl⟩ := H m
    obtain ⟨n, rfl⟩ := H n
    rw [smul_eq_mul, smul_eq_mul, ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def]
  (Algebra.TensorProduct.lmulEquiv R S).bijective

end

section rankAtStalk

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

attribute [local instance] Module.free_of_flat_of_isLocalRing

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






open LocalizedModule Localization

instance {R : Type*} [CommSemiring R] (S : Submonoid R)
    (M : Type*) [AddCommMonoid M] [Module R M] [Module.Finite R M] :
    Module.Finite (Localization S) (LocalizedModule S M) :=
  Module.Finite.of_isLocalizedModule S (LocalizedModule.mkLinearMap S M)

variable [Flat R M] [Module.Finite R M]

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

lemma Algebra.comap_surjective_iff_injective_of_finite :
    Function.Surjective (algebraMap R S).specComap ↔ Function.Injective (algebraMap R S) := by
  refine ⟨fun h ↦ ?_, fun h ↦ Algebra.IsIntegral.specComap_surjective_of_injective h⟩
  have (P : Ideal R) [P.IsPrime] : IsLocalizedModule P.primeCompl
      (TensorProduct.includeRight : S →ₐ[R] Localization.AtPrime P ⊗[R] S).toLinearMap := by
    rw [isLocalizedModule_iff_isBaseChange (S := P.primeCompl) (A := Localization.AtPrime P)]
    exact TensorProduct.isBaseChange _ _ _
  apply injective_of_isLocalized_maximal (fun P _ ↦ Localization.AtPrime P)
    (fun P _ ↦ Algebra.linearMap _ _) (fun P _ ↦ Localization.AtPrime P ⊗[R] S)
    (fun P _ ↦ Algebra.TensorProduct.includeRight.toLinearMap)
    (Algebra.linearMap R S) _
  intro P _
  convert_to Function.Injective
    ((Algebra.linearMap (Localization.AtPrime P) (Localization.AtPrime P ⊗[R] S)).restrictScalars R)
  rw [DFunLike.coe_fn_eq]
  apply IsLocalizedModule.linearMap_ext P.primeCompl (Algebra.linearMap _ _)
    (Algebra.TensorProduct.includeRight.toLinearMap)
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, linearMap_apply, map_one,
    LinearMap.coe_restrictScalars]
  have : Algebra.linearMap R (Localization.AtPrime P) 1 = 1 := by simp
  rw [← this, IsLocalizedModule.map_apply]
  simp only [linearMap_apply, map_one, AlgHom.toLinearMap_apply]
  apply (faithfulSMul_iff_algebraMap_injective _ _).mp
  obtain ⟨⟨Q, _⟩, hQ⟩ := h ⟨P, inferInstance⟩
  have : Q.LiesOver P := ⟨(congr($(hQ).asIdeal)).symm⟩
  have : Nontrivial (Localization.AtPrime P ⊗[R] S) := by
    let f : Localization.AtPrime P ⊗[R] S →ₐ[R] Localization.AtPrime Q :=
      Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R _ _)
        (IsScalarTower.toAlgHom R S _) (fun _ _ ↦ Commute.all _ _)
    exact f.domain_nontrivial
  infer_instance

lemma Algebra.rankAtStalk_pos_iff_injective :
    (∀ p, 0 < Module.rankAtStalk (R := R) S p) ↔ Function.Injective (algebraMap R S) := by
  rw [← comap_surjective_iff_injective_of_finite, rankAtStalk_pos_iff_specComap_surjective]

lemma Algebra.bijective_algebraMap_of_free [Nontrivial R] [Module.Free R S]
    (h : Module.finrank R S = 1) :
    Function.Bijective (algebraMap R S) := by
  refine ⟨Algebra.rankAtStalk_pos_iff_injective.mp
      (fun p ↦ by simp [Module.rankAtStalk_eq_finrank_of_free, h]), ?_⟩
  have : Module.Free R (Module.End R S) := .of_equiv (dualTensorHomEquiv R S S)
  let f : S →ₗ[R] (S →ₗ[R] S) := LinearMap.mul R S
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro s hs
    rw [show s = f s 1 by simp [f], hs, LinearMap.zero_apply]
  have : (LinearMap.mul R S) 1 = 1 := by
    ext
    simp
  have h1 : LinearMap.trace R S ∘ₗ (f ∘ₗ Algebra.linearMap R S) = LinearMap.id := by
    ext
    simp [f, this, h]
  let e := dualTensorHomEquiv R S S
  let b : Module.Basis (Unit × Unit) R (Module.End R S) :=
    Module.Basis.map (Module.Basis.tensorProduct
      (Module.Basis.dualBasis <| Module.basisUnique Unit h) <| Module.basisUnique Unit h) e
  have h2 : (f ∘ₗ Algebra.linearMap R S) ∘ₗ LinearMap.trace R S = LinearMap.id := by
    apply b.ext
    intro i
    apply (Module.basisUnique Unit h).ext
    intro j
    simp [f, b, e, Module.Basis.tensorProduct]
  let eq : R ≃ₗ[R] Module.End R S := .ofLinear (f ∘ₗ Algebra.linearMap R S) (.trace R S) h2 h1
  have : Function.Bijective (f ∘ₗ Algebra.linearMap R S) := eq.bijective
  have hf : Function.Bijective f := ⟨hinj, .of_comp this.2⟩
  exact (Function.Bijective.of_comp_iff' hf _).mp this |>.2

lemma Algebra.surjective_algebraMap_of_rankAtStalk_le_one
      (h : ∀ p, Module.rankAtStalk (R := R) S p ≤ 1) : Function.Surjective (algebraMap R S) := by
  have (P : Ideal R) [P.IsPrime] : IsLocalizedModule P.primeCompl
      (TensorProduct.includeRight : S →ₐ[R] Localization.AtPrime P ⊗[R] S).toLinearMap := by
    rw [isLocalizedModule_iff_isBaseChange (S := P.primeCompl) (A := Localization.AtPrime P)]
    exact TensorProduct.isBaseChange _ _ _
  apply surjective_of_isLocalized_maximal (fun P _ ↦ Localization.AtPrime P)
    (fun P _ ↦ Algebra.linearMap _ _) (fun P _ ↦ Localization.AtPrime P ⊗[R] S)
    (fun P _ ↦ Algebra.TensorProduct.includeRight.toLinearMap)
    (Algebra.linearMap R S) _
  intro P _
  convert_to Function.Surjective
    ((Algebra.linearMap (Localization.AtPrime P) (Localization.AtPrime P ⊗[R] S)).restrictScalars R)
  rw [DFunLike.coe_fn_eq]
  apply IsLocalizedModule.linearMap_ext P.primeCompl (Algebra.linearMap _ _)
    (Algebra.TensorProduct.includeRight.toLinearMap)
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, linearMap_apply, map_one,
    LinearMap.coe_restrictScalars]
  have : Algebra.linearMap R (Localization.AtPrime P) 1 = 1 := by simp
  rw [← this, IsLocalizedModule.map_apply]
  simp only [linearMap_apply, map_one, AlgHom.toLinearMap_apply]
  have := h ⟨P, inferInstance⟩
  by_cases h : Module.rankAtStalk S ⟨P, inferInstance⟩ = 0
  · have : Subsingleton (Localization.AtPrime P ⊗[R] S) := by
      apply Module.subsingleton_of_rank_zero (R := Localization.AtPrime P)
      simp [← Module.finrank_eq_rank,
        ← Module.rankAtStalk_eq_finrank_tensorProduct ⟨P, inferInstance⟩, h]
    exact Function.surjective_to_subsingleton _
  · refine (Algebra.bijective_algebraMap_of_free ?_).2
    rw [← Module.rankAtStalk_eq_finrank_tensorProduct ⟨P, inferInstance⟩]
    omega

variable (R) (S) in
/-- If `S` is a finite and flat `R`-algebra, `R → S` is surjective iff `S ⊗[R] S → S` is an
isomorphism iff the rank of `S` is at most `1` at all primes. -/
lemma Module.Flat.tfae_algebraMap_surjective :
    [Function.Surjective (algebraMap R S),
      Function.Bijective (LinearMap.mul' R S),
      (∀ p, Module.rankAtStalk (R := R) S p ≤ 1)].TFAE := by
  tfae_have 1 → 2 := LinearMap.mul'_bijective_of_surjective
  tfae_have 2 → 3 := fun H ↦ by
    intro p
    have h : Module.rankAtStalk (S ⊗[R] S) p = Module.rankAtStalk S p ^ 2 := by
      simp [Module.rankAtStalk_tensorProduct, sq]
    by_contra! hc
    apply Nat.succ_succ_ne_one 0
    rw [← Nat.pow_eq_self_iff hc, ← h, Module.rankAtStalk_eq_of_equiv
      (AlgEquiv.ofBijective (Algebra.TensorProduct.lmul' R (S := S)) H).toLinearEquiv]
  tfae_have 3 → 1 := Algebra.surjective_algebraMap_of_rankAtStalk_le_one
  tfae_finish

lemma Algebra.rankAtStalk_le_one_iff_surjective :
    (∀ p, Module.rankAtStalk (R := R) S p ≤ 1) ↔ Function.Surjective (algebraMap R S) :=
  (Module.Flat.tfae_algebraMap_surjective R S).out 2 0

lemma Algebra.bijective_of_rankAtStalk {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S] (h : Module.rankAtStalk (R := R) S = 1) :
    Function.Bijective (algebraMap R S) :=
  ⟨rankAtStalk_pos_iff_injective.mp (by simp [h]),
    rankAtStalk_le_one_iff_surjective.mp (by simp [h])⟩

end rankAtStalk
