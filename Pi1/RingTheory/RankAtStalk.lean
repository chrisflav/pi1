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
  simp_rw [rankAtStalk, e.finrank_eq, Module.finrank_pi_fintype, finsum_eq_sum_of_fintype]

lemma rankAtStalk_eq_finrank_tensorProduct (p : PrimeSpectrum R):
    rankAtStalk M p =
      finrank (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal ⊗[R] M) := by
  let e : LocalizedModule p.asIdeal.primeCompl M ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal ⊗[R] M :=
    LocalizedModule.equivTensorProduct p.asIdeal.primeCompl M
  rw [rankAtStalk, e.finrank_eq]

variable [Flat R M] [Module.Finite R M]

lemma rankAtStalk_eq_zero_iff_subsingleton :
    rankAtStalk (R := R) M = 0 ↔ Subsingleton M := by
  refine ⟨fun h ↦ ?_, fun _ ↦ rankAtStalk_eq_zero_of_subsingleton⟩
  simp_rw [← support_eq_empty_iff (R := R), Set.eq_empty_iff_forall_not_mem, not_mem_support_iff]
  intro p
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
  apply Module.finrank_baseChange

lemma rankAtStalk_tensorProduct' (N : Type*) [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Module.Flat R N] : rankAtStalk (M ⊗[R] N) = rankAtStalk M * rankAtStalk (R := R) N := by
  ext p
  let e : Localization.AtPrime p.asIdeal ⊗[R] M ⊗[R] N ≃ₗ[Localization.AtPrime p.asIdeal]
      (Localization.AtPrime p.asIdeal ⊗[R] M) ⊗[Localization.AtPrime p.asIdeal]
        (Localization.AtPrime p.asIdeal ⊗[R] N) :=
    (AlgebraTensorModule.assoc _ _ _ _ _ _).symm ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange _ _ _ _ _).symm
  rw [rankAtStalk_eq_finrank_tensorProduct, e.finrank_eq, finrank_tensorProduct,
    ← rankAtStalk_eq_finrank_tensorProduct, ← rankAtStalk_eq_finrank_tensorProduct, Pi.mul_apply]

/-- The rank of a module `M` at a prime `p` is equal to the dimension
of `κ(p) ⊗[R] M` as a `κ(p)`-module. -/
lemma rankAtStalk_eq (p : PrimeSpectrum R) :
    rankAtStalk M p = finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) := by
  let k := p.asIdeal.ResidueField
  let e : k ⊗[Localization.AtPrime p.asIdeal] (Localization.AtPrime p.asIdeal ⊗[R] M) ≃ₗ[k]
      k ⊗[R] M :=
    AlgebraTensorModule.cancelBaseChange _ _ _ _ _
  rw [← e.finrank_eq, finrank_baseChange, rankAtStalk_eq_finrank_tensorProduct]

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
    LinearMap.coe_restrictScalars, TensorProduct.algebraMap_apply, id.map_eq_id, RingHom.id_apply]
  have : Algebra.linearMap R (Localization.AtPrime P) 1 = 1 := by simp
  rw [← this, IsLocalizedModule.map_apply]
  simp only [linearMap_apply, map_one, AlgHom.toLinearMap_apply, TensorProduct.includeRight_apply]
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
  let b : Basis (Unit × Unit) R (Module.End R S) :=
    Basis.map (Basis.tensorProduct
      (Basis.dualBasis <| Module.basisUnique Unit h) <| Module.basisUnique Unit h) e
  have h2 : (f ∘ₗ Algebra.linearMap R S) ∘ₗ LinearMap.trace R S = LinearMap.id := by
    apply b.ext
    intro i
    apply (Module.basisUnique Unit h).ext
    intro j
    simp [f, b, e, Basis.tensorProduct]
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
    LinearMap.coe_restrictScalars, TensorProduct.algebraMap_apply, id.map_eq_id, RingHom.id_apply]
  have : Algebra.linearMap R (Localization.AtPrime P) 1 = 1 := by simp
  rw [← this, IsLocalizedModule.map_apply]
  simp only [linearMap_apply, map_one, AlgHom.toLinearMap_apply, TensorProduct.includeRight_apply]
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
      simp [Module.rankAtStalk_tensorProduct', sq]
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
