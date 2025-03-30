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

lemma Algebra.exists_isTranscendenceBasis_and_isSeparable (p : ℕ) [ExpChar k p]
      (hp : Nat.Prime p) (H : ∀ (s : Finset K),
      LinearIndepOn k _root_.id (s : Set K) → LinearIndepOn k (fun x ↦ x ^ p) (s : Set K))
      (Hfg : (⊤ : IntermediateField k K).FG) :
    ∃ s : Finset K,
      IsTranscendenceBasis k (Subtype.val : s → K) ∧
      Algebra.IsSeparable ((IntermediateField.adjoin k (s : Set K))) K :=
  sorry

lemma sum_pow_expChar {R : Type*} [CommSemiring R] (p : ℕ) [ExpChar R p]
    {ι : Type*} (s : Finset ι) (f : ι → R) :
    (∑ x ∈ s, f x) ^ p = ∑ x ∈ s, f x ^ p :=
  map_sum (frobenius R p) ..

lemma foobar' [PerfectField k] (Hfg : (⊤ : IntermediateField k K).FG) :
    ∃ (s : Finset K),
      IsTranscendenceBasis k (Subtype.val : s → K) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (s : Set K)) K := by
  let p := ringExpChar k
  have : ExpChar K p := expChar_of_injective_ringHom (algebraMap k K).injective p
  obtain (hp|h) := expChar_is_prime_or_one k p
  · refine Algebra.exists_isTranscendenceBasis_and_isSeparable k K p hp (fun s hs ↦ ?_) Hfg
    simp only [LinearIndepOn, Finset.coe_sort_coe, Fintype.linearIndependent_iff]
    intro g hg
    have (x : s) : ∃ (a : k), a ^ p = g x := surjective_frobenius k p (g x)
    choose a ha using this
    simp_rw [← ha, Algebra.smul_def, map_pow, ← mul_pow, ← sum_pow_expChar, ← frobenius_def,
      ← Algebra.smul_def] at hg
    have := frobenius_inj K p
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero] at this
    rw [LinearIndepOn, Fintype.linearIndependent_iff] at hs
    simp_rw [← ha, hs _ (this _ hg)]
    intro i
    simp
    exact Nat.Prime.ne_zero hp
  · have : ExpChar k 1 := ringExpChar.of_eq h
    have : CharZero k := charZero_of_expChar_one' k
    obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k (algebraMap k K).injective
    -- will follow from a PR by Junyan
    have hfin : s.Finite := sorry
    refine ⟨hfin.toFinset, ?_, ?_⟩
    · convert hs <;> ext <;> simp
    · have : Algebra.IsAlgebraic (IntermediateField.adjoin k (hfin.toFinset : Set K)) K := by
        convert hs.isAlgebraic_field <;> simp
      infer_instance

instance Algebra.formallySmooth_fractionRing_mvPolynomial {k ι : Type u} [Field k] :
    FormallySmooth k (FractionRing (MvPolynomial ι k)) :=
  have : FormallySmooth k (MvPolynomial ι k) := inferInstance
  have : FormallySmooth (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) :=
    .of_isLocalization (nonZeroDivisors _)
  .comp k (MvPolynomial ι k) (FractionRing (MvPolynomial ι k))

lemma formallySmooth_of_perfectField_of_FG [PerfectField k] (Hfg : (⊤ : IntermediateField k K).FG) :
    Algebra.FormallySmooth k K := by
  obtain ⟨s, hb, hs⟩ := foobar' k K Hfg
  have : Algebra.FormallySmooth k ↥(IntermediateField.adjoin k (s : Set K)) :=
    let e : FractionRing (MvPolynomial s k) ≃ₐ[k] IntermediateField.adjoin k (s : Set K) :=
      (hb.1.aevalEquivField).trans (IntermediateField.equivOfEq (by simp))
    .of_equiv e
  have : Algebra.FormallyEtale (IntermediateField.adjoin k (s : Set K)) K :=
    Algebra.FormallyEtale.of_isSeparable _ _
  apply Algebra.FormallySmooth.comp k (IntermediateField.adjoin k (s : Set K)) K

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
  simp only [AlgHom.mem_fieldRange, AlgHom.coe_id, id_eq, exists_eq, IntermediateField.mem_top, g]
  rw [← Algebra.map_top, ← hs, AlgHom.map_adjoin]
  simp [g]
