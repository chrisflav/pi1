import Pi1.RingTheory.SmoothDescent
import Pi1.RingTheory.FiniteEtale.Basic

universe u v

open TensorProduct

lemma Module.Finite.of_finite_tensorProduct_of_faithfullyFlat
    {R : Type*} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (T : Type u) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [Module.Finite T (T ⊗[R] M)] : Module.Finite R M := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := T) (M := T ⊗[R] M)
  have (i : Fin n) : ∃ (ι : Type (max u v)) (_ : Fintype ι) (t : ι → T) (m : ι → M),
      s i = ∑ j, t j ⊗ₜ m j := by
    have := Submodule.eq_top_iff'.mp (TensorProduct.span_tmul_eq_top R T M) (s i)
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
  choose ι hι t m h using this
  let f₀ : ((Σ i, ι i) → R) →ₗ[R] M :=
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
    use ∑ (j : ι i), t i j ⊗ₜ Pi.basisFun R _ ⟨i, j⟩
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

lemma Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (T : Type u) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [Algebra.FinitePresentation T (T ⊗[R] S)] :
    Algebra.FinitePresentation R S :=
  sorry

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
