import Pi1.RingTheory.SmoothDescent
import Pi1.RingTheory.FiniteEtale.Basic

universe u v w

open TensorProduct

lemma TensorProduct.exists_sum_tmul_eq {R M N : Type*}
    [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (x : M ⊗[R] N) :
    ∃ (k : ℕ) (m : Fin k → M) (n : Fin k → N),
      x = ∑ j, m j ⊗ₜ n j := by
  suffices h : ∃ (ι : Type _) (_ : Fintype ι) (m : ι → M) (n : ι → N),
      x = ∑ j, m j ⊗ₜ n j by
    obtain ⟨ι, _, m, n, h⟩ := h
    use Fintype.card ι, m ∘ (Fintype.equivFin ι).symm, n ∘ (Fintype.equivFin ι).symm
    simp [h, ← Equiv.sum_comp (Fintype.equivFin ι).symm]
  have := Submodule.eq_top_iff'.mp (TensorProduct.span_tmul_eq_top R M N) x
  rw [Submodule.mem_span_iff_exists_finset_subset] at this
  obtain ⟨u, v, hsub, hsup, heq⟩ := this
  choose t m h using hsub
  refine ⟨v, inferInstance, fun j ↦ u j • t j.2, fun j ↦ m j.2, ?_⟩
  simp_rw [← heq]
  rw [← Finset.sum_attach, Finset.univ_eq_attach]
  congr
  ext j
  rw [← smul_tmul']
  congr
  exact (h j.2).symm

lemma Module.Finite.of_finite_tensorProduct_of_faithfullyFlat
    {R : Type*} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (T : Type u) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [Module.Finite T (T ⊗[R] M)] : Module.Finite R M := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := T) (M := T ⊗[R] M)
  have (i : Fin n) : ∃ (k : ℕ) (t : Fin k → T) (m : Fin k → M),
      s i = ∑ j, t j ⊗ₜ m j := TensorProduct.exists_sum_tmul_eq (s i)
  choose k t m h using this
  let f₀ : ((Σ i, Fin (k i)) → R) →ₗ[R] M :=
    (Pi.basisFun R _).constr R fun ⟨i, j⟩ ↦ m i j
  apply of_surjective f₀
  rw [← Module.FaithfullyFlat.lTensor_surjective_iff_surjective _ T]
  intro x
  have hx : x ∈ Submodule.span T (Set.range s) := by rw [hs]; trivial
  induction hx using Submodule.span_induction with
  | zero => use 0; simp
  | smul a _ _ hx =>
    obtain ⟨x, rfl⟩ := hx
    use a • x
    exact (TensorProduct.AlgebraTensorModule.lTensor T T f₀).map_smul a x
  | add _ _ _ _ hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    use x + y
    simp
  | mem _ hx =>
    obtain ⟨i, rfl⟩ := hx
    use ∑ (j : Fin (k i)), t i j ⊗ₜ Pi.basisFun R _ ⟨i, j⟩
    simp [f₀, -Pi.basisFun_equivFun, -Pi.basisFun_apply, h i]

lemma Algebra.FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (T : Type u) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [Algebra.FormallyUnramified T (T ⊗[R] S)] :
    Algebra.FormallyUnramified R S := by
  constructor
  let _ : Algebra S (T ⊗[R] S) := TensorProduct.rightAlgebra
  have : Subsingleton (T ⊗[R] Ω[S⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquiv R T S (T ⊗[R] S)).subsingleton
  exact Module.FaithfullyFlat.lTensor_reflects_triviality R T _

lemma Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (T : Type*) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [Algebra.FiniteType T (T ⊗[R] S)] :
    Algebra.FiniteType R S := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := T) (A := T ⊗[R] S)
  have (x : s) := TensorProduct.exists_sum_tmul_eq x.1
  choose k t m h using this
  let f : MvPolynomial (Σ x : s, Fin (k x)) R →ₐ[R] S := MvPolynomial.aeval (fun ⟨x, i⟩ ↦ m x i)
  apply Algebra.FiniteType.of_surjective inferInstance f
  have hf : Function.Surjective (Algebra.TensorProduct.map (.id T T) f) := by
    intro x
    have hx : x ∈ adjoin T s := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | algebraMap t => use algebraMap _ _ t; simp
    | mul _ _ _ _ hx hy =>
      obtain ⟨x, _, rfl⟩ := hx
      obtain ⟨y, _, rfl⟩ := hy
      use x * y
      simp
    | add _ _ _ _ hx hy =>
      obtain ⟨x, _, rfl⟩ := hx
      obtain ⟨y, _, rfl⟩ := hy
      use x + y
      simp
    | mem x hx =>
      let i : s := ⟨x, hx⟩
      use ∑ (j : Fin (k i)), t i j ⊗ₜ MvPolynomial.X ⟨i, j⟩
      simp [f, ← h, i]
  exact (Module.FaithfullyFlat.lTensor_surjective_iff_surjective _ T _).mp hf

lemma Ideal.FG.of_FG_map_of_faithfullyFlat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] {I : Ideal R} (hI : (I.map (algebraMap R S)).FG) :
    I.FG := by
  show Submodule.FG I
  rw [← Module.Finite.iff_fg]
  let f : S ⊗[R] I →ₗ[S] S :=
    (AlgebraTensorModule.rid _ _ _).toLinearMap ∘ₗ
      AlgebraTensorModule.lTensor S S I.subtype
  have hf : Function.Injective f := by simp [f]
  have : I.map (algebraMap R S) = LinearMap.range f := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      use 1 ⊗ₜ ⟨x, hx⟩
      simp [f, Algebra.smul_def]
    · rintro - ⟨x, rfl⟩
      induction x with
      | zero => simp
      | add _ _ hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
      | tmul s x =>
        have : f (s ⊗ₜ[R] x) = s • f (1 ⊗ₜ x) := by
          rw [← map_smul, smul_tmul', smul_eq_mul, mul_one]
        rw [this]
        apply Ideal.mul_mem_left
        simpa [f, Algebra.smul_def] using Ideal.mem_map_of_mem _ x.2
  let e : S ⊗[R] I ≃ₗ[S] I.map (algebraMap R S) :=
    LinearEquiv.ofInjective _ hf ≪≫ₗ .ofEq _ _ this.symm
  have : Module.Finite S (S ⊗[R] ↥I) := by
    rwa [Module.Finite.equiv_iff e, Module.Finite.iff_fg]
  apply Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
lemma Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (T : Type*) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [Algebra.FinitePresentation T (T ⊗[R] S)] :
    Algebra.FinitePresentation R S := by
  have : Algebra.FiniteType R S := .of_finiteType_tensorProduct_of_faithfullyFlat T
  rw [Algebra.FiniteType.iff_quotient_mvPolynomial''] at this
  obtain ⟨n, f, hf⟩ := this
  have : Module.FaithfullyFlat (MvPolynomial (Fin n) R) (T ⊗[R] MvPolynomial (Fin n) R) :=
    .of_linearEquiv _ _ Algebra.TensorProduct.comm'.symm
  let fT := Algebra.TensorProduct.map (.id T T) f
  refine .of_surjective hf (.of_FG_map_of_faithfullyFlat (S := T ⊗[R] MvPolynomial (Fin n) R) ?_)
  have : (RingHom.ker f.toRingHom).map
      (algebraMap (MvPolynomial (Fin n) R) (T ⊗[R] MvPolynomial (Fin n) R)) = RingHom.ker fT :=
    (Algebra.TensorProduct.lTensor_ker f hf).symm
  rw [this]
  apply ker_fG_of_surjective
  exact FiniteType.baseChangeAux_surj T hf

lemma Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S]
    (T : Type u) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [Algebra.Etale T (T ⊗[R] S)] :
    Algebra.Etale R S := by
  have : Algebra.FinitePresentation R S := .of_finitePresentation_tensorProduct_of_faithfullyFlat T
  refine ⟨?_, .of_finitePresentation_tensorProduct_of_faithfullyFlat T⟩
  rw [FormallyEtale.iff_unramified_and_smooth]
  exact ⟨.of_formallyUnramified_tensorProduct_of_faithfullyFlat T,
    .of_formallySmooth_tensorProduct T⟩

lemma Algebra.FiniteEtale.of_finiteEtale_tensorProduct_of_faithfullyFlat {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S]
    (T : Type u) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [Algebra.FiniteEtale T (T ⊗[R] S)] :
    Algebra.FiniteEtale R S := by
  have : Algebra.Etale R S :=
    .of_etale_tensorProduct_of_faithfullyFlat T
  have : Module.Finite R S :=
    .of_finite_tensorProduct_of_faithfullyFlat T
  constructor
