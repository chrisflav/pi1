import Mathlib.RingTheory.IsAdjoinRoot
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

lemma Module.FinitePresentation.of_equiv {R M N : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) [Module.FinitePresentation R M] :
    Module.FinitePresentation R N := by
  simp [← Module.FinitePresentation.fg_ker_iff e.toLinearMap e.surjective, Submodule.fg_bot]

instance (priority := 900) Module.FinitePresentation.of_subsingleton
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Subsingleton M] :
    Module.FinitePresentation R M :=
  .of_equiv (default : (Fin 0 → R) ≃ₗ[R] M)

universe v

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
lemma Module.pi_induction' {ι : Type} [Finite ι] (R : Type*) [CommRing R]
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

noncomputable
def Polynomial.toMvPolynomial {R ι : Type*} [CommSemiring R]
    (i : ι) (p : R[X]) : MvPolynomial ι R :=
  MvPolynomial.rename (fun _ : Unit ↦ i) (MvPolynomial.pUnitAlgEquiv R |>.symm <| p)

lemma Module.Free.trans (R S M : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Free R S] [Module.Free S M] :
    Module.Free R M :=
  sorry

lemma AdjoinRoot.free_of_monic {R : Type*} [CommRing R] {f : R[X]} (hf : f.Monic) :
    Module.Free R (AdjoinRoot f) :=
  .of_basis (AdjoinRoot.powerBasis' hf).basis

lemma Polynomial.free_quotient_of_monic {R : Type*} [CommRing R] {p : R[X]} (hp : p.Monic) :
    Module.Free R (R[X] ⧸ Ideal.span {p}) :=
  AdjoinRoot.free_of_monic hp

--def fooEquiv {R ι : Type*} [CommRing R] (p : Option ι → R[X]) :
--    AdjoinRoot

lemma AdjoinRoot.lift_algebraMap {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (f : Polynomial R) (x : S) (hfx : Polynomial.aeval x f = 0) (r : R) :
    AdjoinRoot.lift (algebraMap R S) x hfx (algebraMap R (AdjoinRoot f) r) =
      algebraMap R S r := by
  simp

set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
lemma MvPolynomial.freeQuotientOfMonic {R ι : Type*} [Finite ι] [CommRing R] (p : ι → R[X])
    (hp : ∀ i, (p i).Monic) :
    Module.Free R
      (MvPolynomial ι R ⧸ (Ideal.span <| Set.range fun i ↦ (p i).toMvPolynomial i)) := by
  cases nonempty_fintype ι
  revert p
  refine Fintype.induction_empty_option ?_ ?_ ?_ ι
  · sorry
  · intro p _
    let e :
        (MvPolynomial PEmpty R ⧸ Ideal.span (Set.range fun i : PEmpty ↦ (p i).toMvPolynomial i))
          ≃ₐ[R] R :=
      sorry
    apply Module.Free.of_equiv e.toLinearEquiv.symm
  · intro α _ hp q hq
    let A :=
      MvPolynomial α R ⧸ (Ideal.span <| Set.range fun i : α ↦ (q i).toMvPolynomial i)
    let B := MvPolynomial (Option α) R ⧸ (Ideal.span <| Set.range fun i ↦ (q i).toMvPolynomial i)
    let f : A →ₐ[R] B :=
      Ideal.Quotient.liftₐ _ (MvPolynomial.aeval fun x ↦ Ideal.Quotient.mk _ <| X (some x)) sorry
    have : Module.Free R A := by
      apply hp
      intro i
      exact hq i
    let _ : Algebra A B := f.toRingHom.toAlgebra
    let P : A[X] := (q none).map (algebraMap R A)
    let u : AdjoinRoot P →ₐ[A] B :=
      AdjoinRoot.liftHom _
        (Ideal.Quotient.mk _ (toMvPolynomial none (q none)))
        sorry
    let v' : B →ₐ[R] AdjoinRoot P :=
      Ideal.Quotient.liftₐ _
        (MvPolynomial.aeval (fun x ↦ x.elim (AdjoinRoot.root P)
          (fun i ↦ AdjoinRoot.mk _ (Polynomial.C <| Ideal.Quotient.mk _ (X i)))))
        sorry
    let v : B →ₐ[A] AdjoinRoot P :=
      { __ := v'.toRingHom
        commutes' := sorry }
    have h1 : v.comp u = AlgHom.id A (AdjoinRoot P) := by
      apply AdjoinRoot.algHom_ext
      simp [u, v, v']
      rw [Ideal.Quotient.liftₐ_apply]
      have : Polynomial.eval₂ (algebraMap R (AdjoinRoot P)) (AdjoinRoot.root P) (q none) = AdjoinRoot.root P := sorry
      simp [toMvPolynomial, MvPolynomial.aeval_rename, this]
    have h2 : ((u.comp v).restrictScalars R) =
        ((AlgHom.id A B).restrictScalars R) := by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      simp [u, v, v']
      rw [Ideal.Quotient.liftₐ_apply]
      simp [Ideal.Quotient.mkₐ]
      cases i
      · simp [P]
        simp [toMvPolynomial]
        sorry
      · simp [RingHom.algebraMap_toAlgebra, f]
        rw [Ideal.Quotient.liftₐ_apply]
        rw [Ideal.Quotient.lift_mk]
        simp
        rfl
    /-
    let h : IsAdjoinRoot B P :=
      { map := (Polynomial.aeval <| Ideal.Quotient.mk _ (toMvPolynomial none (q none))).toRingHom
        map_surjective x := by
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
          induction x using MvPolynomial.induction_on with
          | h_C r =>
            use Polynomial.C (algebraMap R A r)
            simp
            erw [Polynomial.aeval_C]
            rw [RingHom.algebraMap_toAlgebra]
            simp
            rfl
          | h_X => sorry
          | h_add p q hp hq =>
            obtain ⟨a, ha⟩ := hp
            obtain ⟨b, hb⟩ := hq
            use a + b
            simp at ha hb
            simp [ha, hb]
        ker_map := sorry
        algebraMap_eq := by
          ext
          simp
          sorry
          sorry
      }
    #exit
    -/
    let e : AdjoinRoot P ≃ₐ[A] B :=
      sorry
      /-
      { __ := u
        invFun := v
        left_inv x := by
          induction' x using AdjoinRoot.induction_on with p
          simp [u, v]
          induction p using Polynomial.induction_on with
          | h_C a =>
            obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
            simp [RingHom.algebraMap_toAlgebra, f, AdjoinRoot.mk, AdjoinRoot]
            nth_rw 2 [Ideal.Quotient.liftₐ_apply]
            simp
            induction a using MvPolynomial.induction_on with
            | h_C r =>
              have : IsScalarTower R A (A[X] ⧸ Ideal.span {P}) := sorry
              simp
              rw [IsScalarTower.algebraMap_apply R A]
              simp [A]
              rfl
            | h_X p i hp =>
              simp [hp]
              rw [Ideal.Quotient.liftₐ_apply]
              have : (Ideal.Quotient.mk (Ideal.span {P}))
                  (Polynomial.C
                    ((Ideal.Quotient.mk
                      (Ideal.span (Set.range fun i ↦ toMvPolynomial i (q (some i))))) p)) = 0 :=
                sorry
              simp [this]
            | h_add p q hp hq =>
              simp_rw [map_add, hp, hq]
          | h_add p q hp hq =>
            simp [hp, hq]
          | h_monomial n a hn =>
            simp at hn
            simp [pow_add, hn]
            rw [← mul_assoc, hn]
            rw [Ideal.Quotient.liftₐ_apply]
            simp [Polynomial.toMvPolynomial, MvPolynomial.aeval_rename]
            have : (algebraMap R (AdjoinRoot P)) ((q none).coeff 0) = AdjoinRoot.root P := sorry
            rw [← mul_assoc, this]
        right_inv x := by
          simp [u, v]
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
          rw [Ideal.Quotient.liftₐ_apply]
          simp
          induction x using MvPolynomial.induction_on with
          | h_C r =>
              simp
              rw [IsScalarTower.algebraMap_apply R A]
              simp
              rw [IsScalarTower.algebraMap_apply R (MvPolynomial α R) A]
              simp [RingHom.algebraMap_toAlgebra, f]
              rw [Ideal.Quotient.liftₐ_apply]
              rw [Ideal.Quotient.lift_mk]
              simp
              rfl
          | h_add p q hp hq =>
              simp [hp, hq]
          | h_X p n hp =>
              simp at hp
              simp [hp]
              congr
              cases n
              · simp [P]
                sorry
              · simp
                sorry
        }
      -/
    have : Module.Free A (AdjoinRoot P) := by
      apply AdjoinRoot.free_of_monic
      exact (hq none).map _
    have : Module.Free A B := Module.Free.of_equiv e.toLinearEquiv
    apply Module.Free.trans R A B

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
