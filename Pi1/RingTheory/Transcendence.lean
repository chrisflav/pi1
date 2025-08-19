import Mathlib

universe u

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

lemma Algebra.finite_of_intermediateFieldFG_of_isAlgebraic
    (h : IntermediateField.FG (⊤ : IntermediateField k K)) [Algebra.IsAlgebraic k K] :
    Module.Finite k K := by
  obtain ⟨s, hs⟩ := h
  have : Algebra.FiniteType k K := by
    use s
    rw [← IntermediateField.adjoin_algebraic_toSubalgebra
      (fun x hx ↦ Algebra.IsAlgebraic.isAlgebraic x)]
    simpa [← IntermediateField.toSubalgebra_inj] using hs
  exact Algebra.IsIntegral.finite

instance Algebra.formallySmooth_fractionRing_mvPolynomial {k ι : Type u} [Field k] :
    FormallySmooth k (FractionRing (MvPolynomial ι k)) :=
  have : FormallySmooth k (MvPolynomial ι k) := inferInstance
  have : FormallySmooth (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) :=
    .of_isLocalization (nonZeroDivisors _)
  .comp k (MvPolynomial ι k) (FractionRing (MvPolynomial ι k))

open AlgebraicGeometry CategoryTheory

/-- If `S` is of finite type over `R` and `K` the fraction field of `S`,
then `K` is finitely generated over `R` as a field. -/
lemma Algebra.FiniteType.FG_top_of_isFractionRing {R S K : Type*} [Field R]
    [CommRing S] [Field K] [Algebra R S] [Algebra R K]
    [Algebra S K] [IsScalarTower R S K] [IsFractionRing S K]
    [h : Algebra.FiniteType R S] :
    (⊤ : IntermediateField R K).FG := by
  classical
  obtain ⟨s, hs⟩ := h.1
  use Finset.image (algebraMap S K) s
  let g : S →ₐ[R] K := IsScalarTower.toAlgHom R S K
  have hg : Function.Injective g := FaithfulSMul.algebraMap_injective S K
  rw [← IsFractionRing.liftAlgHom_fieldRange_eq_of_range_eq hg (L := K) (K := K)]
  let u := IsFractionRing.liftAlgHom hg (K := K)
  have : (IsFractionRing.liftAlgHom hg).toRingHom = (AlgHom.id R K).toRingHom := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors S)
    ext
    simp [g]
  have : IsFractionRing.liftAlgHom hg = AlgHom.id R K := by
    ext
    apply DFunLike.congr_fun this _
  rw [this]
  ext
  simp only [AlgHom.mem_fieldRange, AlgHom.coe_id, id_eq, exists_eq, IntermediateField.mem_top]
  rw [← Algebra.map_top, ← hs, AlgHom.map_adjoin]
  simp [g]
