import Mathlib
import Pi1.Mathlib.RingTheory.Presentation

open TensorProduct

section

lemma _root_.AlgHom.cancel_right {R S T A : Type*} [CommSemiring R] [Semiring S] [Semiring T]
    [Semiring A] [Algebra R S] [Algebra R T] [Algebra R A]
    {g₁ g₂ : S →ₐ[R] T} {f : A →ₐ[R] S} (hf : Function.Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => AlgHom.ext <| hf.forall.2 (AlgHom.ext_iff.1 h), fun h => h ▸ rfl⟩

lemma _root_.AlgHom.cancel_left {R S T A : Type*} [CommSemiring R] [Semiring S] [Semiring T]
    [Semiring A] [Algebra R S] [Algebra R T] [Algebra R A]
    {g₁ g₂ : S →ₐ[R] T} {f : T →ₐ[R] A} (hf : Function.Injective f) :
    f.comp g₁ = f.comp g₂ ↔ g₁ = g₂ :=
  ⟨fun h => AlgHom.ext <| fun _ ↦ hf.eq_iff.mp <| AlgHom.ext_iff.mp h _, fun h => h ▸ rfl⟩

@[simp]
lemma _root_.AlgEquiv.restrictScalars_symm_apply (R : Type*) {S A B : Type*}
    [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B] [Algebra R S]
    [Algebra S A] [Algebra S B] [Algebra R A] [Algebra R B]
    [IsScalarTower R S A] [IsScalarTower R S B] (e : A ≃ₐ[S] B) (b : B) :
    (e.restrictScalars R).symm b = e.symm b := rfl

@[simp]
lemma _root_.MvPolynomial.algebraTensorAlgEquiv_symm_comp_aeval (R : Type*) [CommSemiring R]
    {σ : Type*} (A : Type*) [CommSemiring A] [Algebra R A] :
    (((MvPolynomial.algebraTensorAlgEquiv (σ := σ) R A).symm.restrictScalars R) :
        MvPolynomial σ A →ₐ[R] A ⊗[R] MvPolynomial σ R).comp
      (MvPolynomial.mapAlgHom (R := R) (S₁ := R) (S₂ := A) (Algebra.ofId R A)) =
      MvPolynomial.aeval fun i ↦ 1 ⊗ₜ MvPolynomial.X i := by
  ext
  simp

@[simp]
lemma _root_.MvPolynomial.algebraTensorAlgEquiv_symm_map (R : Type*) [CommSemiring R]
    {σ : Type*} (A : Type*) [CommSemiring A] [Algebra R A] (x : MvPolynomial σ R) :
    (MvPolynomial.algebraTensorAlgEquiv R A).symm
      (MvPolynomial.map (algebraMap R A) x) = 1 ⊗ₜ x := by
  have : (MvPolynomial.aeval fun i ↦ 1 ⊗ₜ[R] MvPolynomial.X i) x = (1 : A) ⊗ₜ x := by
    induction x using MvPolynomial.induction_on
    · simp [Algebra.TensorProduct.tmul_one_eq_one_tmul]
    · simp_all [TensorProduct.tmul_add]
    · simp_all
  rw [← this]
  exact DFunLike.congr_fun (MvPolynomial.algebraTensorAlgEquiv_symm_comp_aeval R A) x

lemma MvPolynomial.coeffs_C {R σ : Type*} [CommSemiring R] [DecidableEq R] (r : R) :
    (C (σ := σ) r).coeffs = if r = 0 then ∅ else {r} := by
  classical
  aesop (add simp mem_coeffs_iff)

lemma MvPolynomial.coeffs_C_subset {R σ : Type*} [CommSemiring R] (r : R) :
    (C (σ := σ) r).coeffs ⊆ {r} := by
  classical
  rw [coeffs_C]
  split <;> simp

@[simp]
lemma MvPolynomial.coeffs_mul_X {R σ : Type*} [CommSemiring R] (p : MvPolynomial σ R) (n : σ) :
    (p * X n).coeffs = p.coeffs := by
  classical
  aesop (add simp mem_coeffs_iff)

@[simp]
lemma MvPolynomial.coeffs_X_mul {R σ : Type*} [CommSemiring R] (p : MvPolynomial σ R) (n : σ) :
    (X n * p).coeffs = p.coeffs := by
  classical
  aesop (add simp mem_coeffs_iff)

lemma MvPolynomial.coeffs_add {R σ : Type*} [CommSemiring R] [DecidableEq R]
    {p q : MvPolynomial σ R} (h : Disjoint p.support q.support) :
    (p + q).coeffs = p.coeffs ∪ q.coeffs := by
  ext r
  simp only [mem_coeffs_iff, mem_support_iff, coeff_add, ne_eq, Finset.mem_union]
  have hl (n : σ →₀ ℕ) (hne : p.coeff n ≠ 0) : q.coeff n = 0 :=
    not_mem_support_iff.mp <| h.not_mem_of_mem_left_finset (mem_support_iff.mpr hne)
  have hr (n : σ →₀ ℕ) (hne : q.coeff n ≠ 0) : p.coeff n = 0 :=
    not_mem_support_iff.mp <| h.not_mem_of_mem_right_finset (mem_support_iff.mpr hne)
  have hor (n) (h : ¬coeff n p + coeff n q = 0) : coeff n p ≠ 0 ∨ coeff n q ≠ 0 := by
    by_cases hp : coeff n p = 0 <;> aesop
  refine ⟨fun ⟨n, hn1, hn2⟩ ↦ ?_, ?_⟩
  · obtain (h|h) := hor n hn1
    · exact Or.inl ⟨n, by simp [h, hn2, hl n h]⟩
    · exact Or.inr ⟨n, by simp [h, hn2, hr n h]⟩
  · rintro (⟨n, hn, rfl⟩|⟨n, hn, rfl⟩)
    · exact ⟨n, by simp [hl n hn, hn]⟩
    · exact ⟨n, by simp [hr n hn, hn]⟩

lemma MvPolynomial.mem_range_map_of_coeffs_subset {R S σ : Type*} [CommSemiring R]
    [CommSemiring S] {f : R →+* S} {x : MvPolynomial σ S} (hx : (x.coeffs : Set _) ⊆ Set.range f) :
    x ∈ Set.range (MvPolynomial.map f) := by
  classical
  induction x using MvPolynomial.induction_on'' with
  | C a =>
    by_cases h : a = 0
    · subst h
      exact ⟨0, by simp⟩
    · simp only [coeffs_C, h, reduceIte, Finset.coe_singleton, Set.singleton_subset_iff] at hx
      obtain ⟨b, rfl⟩ := hx
      exact ⟨C b, by simp⟩
  | mul_X p n ih =>
    rw [coeffs_mul_X] at hx
    obtain ⟨q, rfl⟩ := ih hx
    exact ⟨q * X n, by simp⟩
  | monomial_add a s p ha hs hp ih =>
    rw [coeffs_add] at hx
    · simp only [Finset.coe_union, Set.union_subset_iff] at hx
      obtain ⟨q, hq⟩ := ih hx.1
      obtain ⟨u, hu⟩ := hp hx.2
      exact ⟨q + u, by simp [hq, hu]⟩
    · simpa [support_monomial, hs] using not_mem_support_iff.mp ha

end

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

variable {P : Algebra.Presentation R S}

namespace Algebra.Presentation

variable (P) in
/-- The coefficients of a presentation are the coefficients of the relations. -/
def coeffs : Set R := ⋃ (i : P.rels), (P.relation i).coeffs

lemma coeffs_relation_subset_coeffs (x : P.rels) :
    ((P.relation x).coeffs : Set R) ⊆ P.coeffs :=
  Set.subset_iUnion_of_subset x (by simp)

variable (P) in
/-- The core of a presentation is the subalgebra generated by the coefficients of the relations. -/
def core : Subalgebra ℤ R := Algebra.adjoin _ P.coeffs

variable (P) in
lemma coeffs_subset_core : P.coeffs ⊆ P.core := Algebra.subset_adjoin

lemma coeffs_relation_subset_core (x : P.rels) :
    ((P.relation x).coeffs : Set R) ⊆ P.core :=
  subset_trans (P.coeffs_relation_subset_coeffs x) P.coeffs_subset_core

variable (P) in
/-- The core coerced to a type for performance reasons. -/
def Core : Type _ := P.core

instance : CommRing P.Core := fast_instance% (inferInstanceAs <| CommRing P.core)
instance : Algebra P.Core R := fast_instance% (inferInstanceAs <| Algebra P.core R)
instance : FaithfulSMul P.Core R := inferInstanceAs <| FaithfulSMul P.core R
instance : Algebra P.Core S := fast_instance% (inferInstanceAs <| Algebra P.core S)
instance : IsScalarTower P.Core R S := inferInstanceAs <| IsScalarTower P.core R S

variable (P) in
/--
A ring `R₀` is a core for the presentation `P` if the coefficients of the relations of `P`
lie in the image of `R₀` in `R`.
The smallest subring of `R` satisfying this is given by `Algebra.Presentation.Core P`.
-/
class IsCore (R₀ : Type*) [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S] where
  coeffs_subset_range : P.coeffs ⊆ Set.range (algebraMap R₀ R)

instance : P.IsCore P.Core where
  coeffs_subset_range := by
    refine subset_trans P.coeffs_subset_core ?_
    simp [Core, Subalgebra.algebraMap_eq]

variable (R₀ : Type*) [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S]

lemma aeval_map_core (x : MvPolynomial P.vars R₀) :
    MvPolynomial.aeval P.val (MvPolynomial.map (algebraMap R₀ R) x) =
      MvPolynomial.aeval P.val x := by
  induction x using MvPolynomial.induction_on
  · simp [IsScalarTower.algebraMap_apply R₀ R S]
  · simp_all
  · simp_all

variable [P.IsCore R₀]

lemma IsCore.coeffs_relation_mem_range (x : P.rels) :
    ((P.relation x).coeffs : Set R) ⊆ Set.range (algebraMap R₀ R) :=
  subset_trans (P.coeffs_relation_subset_coeffs x) IsCore.coeffs_subset_range

lemma IsCore.mem_range_map_core (x : P.rels) :
    P.relation x ∈ Set.range (MvPolynomial.map (algebraMap R₀ R)) :=
  MvPolynomial.mem_range_map_of_coeffs_subset <| IsCore.coeffs_relation_mem_range R₀ x

/-- The `r`-th relation of `P` as a polynomial in `R₀`. This is the (arbitrary) choice of a
pre-image under the map `R₀[X] → R[X]`. -/
noncomputable def coreRelation (r : P.rels) : MvPolynomial P.vars R₀ :=
  (IsCore.mem_range_map_core R₀ r).choose

lemma map_coreRelation (r : P.rels) :
    MvPolynomial.map (algebraMap R₀ R) (P.coreRelation R₀ r) = P.relation r :=
  (IsCore.mem_range_map_core R₀ r).choose_spec

@[simp]
lemma aeval_val_coreRelation (r : P.rels) :
    (MvPolynomial.aeval P.val) (coreRelation R₀ r) = 0 := by
  rw [← aeval_map_core, map_coreRelation, aeval_val_relation]

@[simp]
lemma algebraTensorAlgEquiv_symm_relation (r : P.rels) :
    (MvPolynomial.algebraTensorAlgEquiv R₀ R).symm (P.relation r) =
      1 ⊗ₜ P.coreRelation R₀ r := by
  rw [← map_coreRelation R₀, MvPolynomial.algebraTensorAlgEquiv_symm_map]

@[simp]
lemma _root_.Ideal.Quotient.mk_span_range {R : Type*} [CommRing R]
    {ι : Type*} (f : ι → R) (i : ι) :
    Ideal.Quotient.mk (Ideal.span (Set.range f)) (f i) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  apply Ideal.subset_span
  use i

/-- The model of `S` over a core `R₀` is `R₀[X]` quotiented by the same relations. -/
abbrev CoreModel : Type _ :=
  MvPolynomial P.vars R₀ ⧸ (Ideal.span <| Set.range (P.coreRelation R₀))

variable (P) in
/-- (Implementation detail): The underlying `AlgHom` of `tensorCoreModelEquiv`. -/
noncomputable def tensorCoreModelHom : R ⊗[R₀] P.CoreModel R₀ →ₐ[R] S :=
  Algebra.TensorProduct.lift (Algebra.ofId R S)
    (Ideal.Quotient.liftₐ _ (MvPolynomial.aeval P.val) <| by
      simp_rw [← RingHom.mem_ker, ← SetLike.le_def, Ideal.span_le]
      rintro a ⟨i, rfl⟩
      simp)
    fun _ _ ↦ Commute.all _ _

@[simp]
lemma tensorCoreModelHom_tmul (x : R) (y : MvPolynomial P.vars R₀) :
    P.tensorCoreModelHom R₀ (x ⊗ₜ y) = algebraMap R S x * MvPolynomial.aeval P.val y :=
  rfl

variable (P) in
/-- (Implementation detail): The inverse of `tensorCoreModelHom`. -/
noncomputable def tensorCoreModelInv : S →ₐ[R] R ⊗[R₀] P.CoreModel R₀ :=
  (Ideal.Quotient.liftₐ _
    ((Algebra.TensorProduct.map (.id R R) (Ideal.Quotient.mkₐ _ _)).comp
      (MvPolynomial.algebraTensorAlgEquiv R₀ R).symm.toAlgHom) <| by
    simp_rw [← RingHom.mem_ker, ← SetLike.le_def]
    rw [← P.span_range_relation_eq_ker, Ideal.span_le]
    rintro a ⟨i, rfl⟩
    simp only [AlgEquiv.toAlgHom_eq_coe, SetLike.mem_coe, RingHom.mem_ker, AlgHom.coe_comp,
      AlgHom.coe_coe, Function.comp_apply, algebraTensorAlgEquiv_symm_relation]
    simp only [TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.mk_span_range, tmul_zero]).comp
    (P.quotientEquiv.restrictScalars R).symm.toAlgHom

@[simp]
lemma tensorCoreModelInv_aeval_val (x : MvPolynomial P.vars R₀) :
    P.tensorCoreModelInv R₀ (MvPolynomial.aeval P.val x) = 1 ⊗ₜ[R₀] (Ideal.Quotient.mk _ x) := by
  rw [← aeval_map_core, ← Generators.algebraMap_apply, ← quotientEquiv_mk]
  simp [tensorCoreModelInv, -quotientEquiv_symm, -quotientEquiv_mk]

private lemma hom_comp_inv :
    (P.tensorCoreModelHom R₀).comp (P.tensorCoreModelInv R₀) = AlgHom.id R S := by
  have h : Function.Surjective
      ((P.quotientEquiv.restrictScalars R).toAlgHom.comp (Ideal.Quotient.mkₐ _ _)) :=
    (P.quotientEquiv.restrictScalars R).surjective.comp Ideal.Quotient.mk_surjective
  simp only [← AlgHom.cancel_right h, tensorCoreModelInv, AlgEquiv.toAlgHom_eq_coe, AlgHom.id_comp]
  rw [AlgHom.comp_assoc, AlgHom.comp_assoc, ← AlgHom.comp_assoc _ _ (Ideal.Quotient.mkₐ R P.ker),
    AlgEquiv.symm_comp, AlgHom.id_comp]
  ext x
  simp

private lemma inv_comp_hom :
    (P.tensorCoreModelInv R₀).comp (P.tensorCoreModelHom R₀) = AlgHom.id R _ := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

/-- The natural isomorphism `R ⊗[R₀] S₀ ≃ₐ[R] S`. -/
noncomputable def tensorCoreModelEquiv : R ⊗[R₀] P.CoreModel R₀ ≃ₐ[R] S :=
  AlgEquiv.ofAlgHom (P.tensorCoreModelHom R₀) (P.tensorCoreModelInv R₀)
    (P.hom_comp_inv R₀) (P.inv_comp_hom R₀)

end Algebra.Presentation
