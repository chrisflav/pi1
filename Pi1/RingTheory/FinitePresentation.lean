import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.RingHom.FinitePresentation

universe u

-- this is in Mathlib (on a newer version), but non dependent
lemma Pi.single_induction' {ι : Type*} [DecidableEq ι] [Finite ι] {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] (p : (Π i, M i) → Prop) (f : Π i, M i)
    (zero : p 0) (add : ∀ f g, p f → p g → p (f + g))
    (single : ∀ i m, p (Pi.single i m)) : p f := by
  cases nonempty_fintype ι
  rw [← Finset.univ_sum_single f]
  exact Finset.sum_induction _ _ add zero (by simp [single])

lemma Pi.ker_algHom {I : Type*} (R : Type*) (f : I → Type*) [CommSemiring R] [∀ i, Semiring (f i)]
    [∀ i, Algebra R (f i)] {A : Type*} [Semiring A] [Algebra R A]
    (g : ∀ i, A →ₐ[R] f i) : RingHom.ker (Pi.algHom R f g) = ⨅ i, RingHom.ker (g i) :=
  Pi.ker_ringHom _

@[simp]
lemma RingHom.finitePresentation_algebraMap {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] :
    (algebraMap R S).FinitePresentation ↔ Algebra.FinitePresentation R S := by
  dsimp only [FinitePresentation]
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

-- TODO: generalize to arbitrary universes
lemma Algebra.FinitePresentation.of_cover_target {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] {ι : Type*} (A : ι → Type u) (s : ι → S) (hs : Ideal.span (Set.range s) = ⊤)
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, Algebra S (A i)]
    [∀ i, IsScalarTower R S (A i)] [∀ i, IsLocalization.Away (s i) (A i)]
    (h : ∀ i, Algebra.FinitePresentation R (A i)) :
    Algebra.FinitePresentation R S := by
  rw [← RingHom.finitePresentation_algebraMap]
  apply RingHom.finitePresentation_ofLocalizationSpanTarget.ofIsLocalization
  exact RingHom.finitePresentation_respectsIso
  exact hs
  rintro ⟨-, ⟨i, rfl⟩⟩
  use A i, inferInstance, inferInstance, inferInstance
  rw [← IsScalarTower.algebraMap_eq, RingHom.finitePresentation_algebraMap]
  infer_instance

lemma RingHom.ker_evalRingHom {ι : Type*} [DecidableEq ι] (R : ι → Type*)
    [∀ i, CommRing (R i)] (i : ι) :
    RingHom.ker (Pi.evalRingHom R i) = Ideal.span {1 - Pi.single i 1} := by
  apply le_antisymm
  · intro x hx
    simp only [mem_ker, Pi.evalRingHom_apply] at hx
    rw [Ideal.mem_span_singleton]
    use x + Pi.single i 1
    simp [mul_add, sub_mul, one_mul, ← Pi.single_mul_left, hx]
  · simp [Ideal.span_le]

lemma Ideal.span_single_eq_top {ι : Type*} [DecidableEq ι] [Finite ι] (R : ι → Type*)
    [∀ i, Ring (R i)] : Ideal.span (Set.range fun i ↦ (Pi.single i 1 : Π i, R i)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using Pi.single_induction' with
  | zero => simp
  | add f g hf hg => exact Ideal.add_mem _ hf hg
  | single i r =>
      have : Pi.single i r = Pi.single i r * Pi.single i 1 := by simp [← Pi.single_mul_left]
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

instance Algebra.FinitePresentation.pi (A : Type u) {α : Type} [Finite α] (B : α → Type u)
    [CommRing A] [∀ a, CommRing (B a)] [∀ a, Algebra A (B a)]
    [∀ a, Algebra.FinitePresentation A (B a)] :
    Algebra.FinitePresentation A (∀ a, B a) := by
  classical
  let _ (i : α) : Algebra (Π a, B a) (B i) := (Pi.evalAlgHom A B i).toAlgebra
  have (i : α) : IsLocalization.Away (Pi.single i 1 : ∀ a, B a) (B i) := by
    refine IsLocalization.away_of_isIdempotentElem ?_ (RingHom.ker_evalRingHom _ _)
      ((Pi.evalRingHom B i).surjective)
    simp [IsIdempotentElem, ← Pi.single_mul_left]
  exact Algebra.FinitePresentation.of_cover_target (fun i ↦ B i) (fun i : α ↦ Pi.single i 1)
    (Ideal.span_single_eq_top B) fun i ↦ inferInstance

instance Algebra.Etale.pi (A : Type u) {α : Type} [Finite α] (B : α → Type u)
    [CommRing A] [∀ a, CommRing (B a)] [∀ a, Algebra A (B a)]
    [hf : ∀ a, Algebra.Etale A (B a)] :
    Algebra.Etale A (∀ a, B a) where

open TensorProduct

instance (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FinitePresentation R A] [Algebra.FinitePresentation R B] :
    Algebra.FinitePresentation R (A ⊗[R] B) :=
  Algebra.FinitePresentation.trans R A (A ⊗[R] B)

instance (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FormallyEtale R A] [Algebra.FormallyEtale R B] :
    Algebra.FormallyEtale R (A ⊗[R] B) :=
  Algebra.FormallyEtale.comp R A (A ⊗[R] B)

proof_wanted Algebra.FinitePresentation.of_finitePresentation {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [Module.FinitePresentation R S] : Algebra.FinitePresentation R S

lemma Module.FinitePresentation.of_equiv {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.FinitePresentation R M] (e : M ≃ₗ[R] N) :
    Module.FinitePresentation R N :=
  sorry

instance (priority := 900) Module.FinitePresentation.of_subsingleton
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Subsingleton M] :
    Module.FinitePresentation R M :=
  sorry

private lemma Module.FinitePresentation.pi_aux {ι : Type*} [Fintype ι] (R : Type*) (M : ι → Type*)
    [CommRing R] [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.FinitePresentation R (M i)] : Module.FinitePresentation R (∀ i, M i) := by
  revert R M
  refine Fintype.induction_empty_option ?_ ?_ ?_ ι
  · intro α β _ e h R M _ _ _ _
    let eq : (∀ i, M i) ≃ₗ[R] ∀ j, M (e j) :=
      sorry
    apply Module.FinitePresentation.of_equiv eq.symm
  · intro R M _ _ _ _
    infer_instance
  · intro α _ h R M _ _ _ _
    let f : (∀ i, M i) →ₗ[R] ∀ i, M (some i) := .pi (fun i ↦ .proj (some i))
    let g : M none →ₗ[R] ∀ i, M i :=
      sorry
    let eq : LinearMap.ker f ≃ₗ[R] M none :=
      sorry
    have hf : Function.Surjective f := by
      intro x
      use fun i ↦ i.recOn 0 (fun a ↦ x a)
      ext
      simp [f]
    have : FinitePresentation R (LinearMap.ker f) := .of_equiv eq.symm
    apply Module.finitePresentation_of_ker f hf

instance Module.FinitePresentation.pi {R ι : Type*} (M : ι → Type*) [CommRing R]
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.FinitePresentation R (M i)]
    [Finite ι] :
    Module.FinitePresentation R (∀ i, M i) := by
  cases nonempty_fintype ι
  apply Module.FinitePresentation.pi_aux

lemma Module.FinitePresentation.trans {R : Type*} (S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.FinitePresentation R S] [Module.FinitePresentation S M] :
    Module.FinitePresentation R M := by
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin S M
  let f : (Fin n → S) →ₗ[R] M := (e.symm ∘ₗ K.mkQ).restrictScalars R
  apply Module.finitePresentation_of_surjective f
  · intro m
    obtain ⟨a, ha⟩ := K.mkQ_surjective (e m)
    use a
    simp [f, ha]
  · simp only [f, LinearMap.ker_restrictScalars, ← Module.Finite.iff_fg]
    have : Module.Finite S
        (Submodule.restrictScalars R (LinearMap.ker (e.symm.toLinearMap ∘ₗ K.mkQ))) := by
      show Module.Finite S (LinearMap.ker (e.symm.toLinearMap ∘ₗ K.mkQ))
      simpa [Module.Finite.iff_fg]
    apply Module.Finite.trans S

open Polynomial

@[simp]
lemma MvPolynomial.aeval_polynomialEval₂_C {R S : Type*} [CommSemiring R]
      [CommSemiring S] [Algebra R S] (f : PUnit → S) (p : R[X]) :
    MvPolynomial.aeval f (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X ()) p) =
      Polynomial.eval₂ (algebraMap R S) (f ()) p := by
  induction p using Polynomial.induction_on with
  | h_C => simp
  | h_monomial => simp
  | h_add p q hp hq => simp [hp, hq]

instance (priority := 900) {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S] : Module.FinitePresentation R S := by
  have : (⊤ : Submodule R S).FG := Module.finite_def.mp inferInstance
  obtain ⟨s, hs⟩ := this
  have (s : S) : IsIntegral R s := Algebra.IsIntegral.isIntegral s
  choose p hm hp using this
  let q (x : s) : MvPolynomial s R :=
    MvPolynomial.rename (fun _ : Unit ↦ x) (MvPolynomial.pUnitAlgEquiv R |>.symm <| p x)
  let S' : Type _ := MvPolynomial s R ⧸ (Ideal.span <| Set.range fun x ↦ q x)
  let f : S' →ₐ[R] S := Ideal.Quotient.liftₐ _ (MvPolynomial.aeval Subtype.val) <| by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem _ h =>
        obtain ⟨x, rfl⟩ := h
        simp [q, MvPolynomial.aeval_rename, hp]
    | add _ _ _ _ h1 h2 => simp [h1, h2]
    | smul _ _ _ h => simp [h]
    | zero => simp
  have hf : Function.Surjective f := by
    apply Ideal.Quotient.lift_surjective_of_surjective
    simp
    intro x
    have hx : x ∈ Submodule.span R s := by rw [hs]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      use .X ⟨x, hx⟩
      simp
    | smul r _ _ hx =>
      obtain ⟨x, rfl⟩ := hx
      use r • x
      simp
    | add x y _ _ hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      use x + y
      simp
    | zero =>
      use 0; simp
  let _ : Algebra S' S := f.toRingHom.toAlgebra
  have : Algebra.FinitePresentation S' S :=
    .of_restrict_scalars_finitePresentation R _ _
  have hker : (RingHom.ker f).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId S' S) hf
  have : Module.FinitePresentation S' S :=
    Module.finitePresentation_of_surjective (Algebra.linearMap S' S) hf hker
  have : IsScalarTower R S' S := .of_algHom f
  have : Module.Finite R S' := by
    sorry
  have : Module.Free R S' :=
    sorry
  have : Module.FinitePresentation R S' :=
    Module.finitePresentation_of_projective R S'
  apply Module.FinitePresentation.trans S'
