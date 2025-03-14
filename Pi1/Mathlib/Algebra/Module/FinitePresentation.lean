import Mathlib.Algebra.Module.FinitePresentation

--#22918
section

universe u v

lemma Module.FinitePresentation.of_equiv {R M N : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) [Module.FinitePresentation R M] :
    Module.FinitePresentation R N := by
  simp [← Module.FinitePresentation.fg_ker_iff e.toLinearMap e.surjective, Submodule.fg_bot]

instance (priority := 900) Module.FinitePresentation.of_subsingleton
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Subsingleton M] :
    Module.FinitePresentation R M :=
  .of_equiv (default : (Fin 0 → R) ≃ₗ[R] M)

@[elab_as_elim]
lemma Module.pi_induction {ι : Type} [Finite ι] (R : Type*) [Semiring R]
    (motive : ∀ (N : Type u) [AddCommMonoid N] [Module R N], Prop)
    (equiv : ∀ {N N' : Type u} [AddCommMonoid N] [AddCommMonoid N']
      [Module R N] [Module R N'], (N ≃ₗ[R] N') → motive N → motive N')
    (unit : motive PUnit)
    (prod : ∀ {N N' : Type u} [AddCommMonoid N] [AddCommMonoid N']
      [Module R N] [Module R N'], motive N → motive N' → motive (N × N'))
    (M : ι → Type u) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (h : ∀ i, motive (M i)) :
    motive (∀ i, M i) := by
  classical
  cases nonempty_fintype ι
  revert M
  refine Fintype.induction_empty_option ?_ ?_ ?_ ι
  · intro α β _ e h M _ _ hM
    apply equiv (LinearEquiv.piCongrLeft R M e) <| h _ fun i ↦ hM _
  · intro M _ _ _
    exact equiv default unit
  · intro α _ h M _ _ hn
    exact equiv (LinearEquiv.piOptionEquivProd R).symm <| prod (hn _) (h _ fun i ↦ hn i)

@[elab_as_elim]
lemma Module.pi_induction' {ι : Type} [Finite ι] (R : Type*) [Ring R]
    (motive : ∀ (N : Type u) [AddCommGroup N] [Module R N], Prop)
    (equiv : ∀ {N N' : Type u} [AddCommGroup N] [AddCommGroup N']
      [Module R N] [Module R N'], (N ≃ₗ[R] N') → motive N → motive N')
    (unit : motive PUnit)
    (prod : ∀ {N N' : Type u} [AddCommGroup N] [AddCommGroup N']
      [Module R N] [Module R N'], motive N → motive N' → motive (N × N'))
    (M : ι → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (h : ∀ i, motive (M i)) :
    motive (∀ i, M i) := by
  classical
  cases nonempty_fintype ι
  revert M
  refine Fintype.induction_empty_option ?_ ?_ ?_ ι
  · intro α β _ e h M _ _ hM
    apply equiv (LinearEquiv.piCongrLeft R M e) <| h _ fun i ↦ hM _
  · intro M _ _ _
    exact equiv default unit
  · intro α _ h M _ _ hn
    exact equiv (LinearEquiv.piOptionEquivProd R).symm <| prod (hn _) (h _ fun i ↦ hn i)

instance Module.FinitePresentation.prod (R : Type*) (M N : Type*)
    [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.FinitePresentation R M] [Module.FinitePresentation R N] :
    Module.FinitePresentation R (M × N) := by
  have hf : Function.Surjective (LinearMap.fst R M N) := LinearMap.fst_surjective
  have : FinitePresentation R ↥(LinearMap.ker (LinearMap.fst R M N)) := by
    rw [LinearMap.ker_fst]
    exact .of_equiv (LinearEquiv.ofInjective (LinearMap.inr R M N) LinearMap.inr_injective)
  apply Module.finitePresentation_of_ker (.fst R M N) hf

private lemma Module.FinitePresentation.pi_aux {ι : Type} [Finite ι] (R : Type*) (M : ι → Type*)
    [CommRing R] [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.FinitePresentation R (M i)] : Module.FinitePresentation R (∀ i, M i) := by
  refine Module.pi_induction' (motive := fun N _ _ ↦ Module.FinitePresentation R N) R ?_ ?_ ?_ M
      inferInstance
  · intro N N' _ _ _ _ e hN
    exact Module.FinitePresentation.of_equiv e
  · infer_instance
  · introv hN hN'
    infer_instance

instance Module.FinitePresentation.pi {R ι : Type*} [CommRing R] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.FinitePresentation R (M i)]
    [Finite ι] : Module.FinitePresentation R (∀ i, M i) := by
  cases nonempty_fintype ι
  convert Module.FinitePresentation.of_equiv (LinearEquiv.piCongrLeft R M (Fintype.equivFin ι).symm)
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

end
