import Mathlib
import Pi1.RingTheory.FiniteEtale.Equalizer
import Pi1.Mathlib.AlgebraicGeometry.Morphisms.Flat
import Pi1.Mathlib.RingTheory.Flat.Equalizer

set_option linter.unusedTactic false

open TensorProduct

universe u

@[simp]
lemma AlgHom.equalizerCompRightEquiv_symm_apply (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] {E F : Type*} (σ τ : E → F) (x : Function.Coequalizer σ τ → S) (i : F) :
    ((equalizerCompRightEquiv R S σ τ).symm x).val i = x (.mk _ _ i) :=
  rfl

@[simp]
lemma AlgHom.equalizerCompRightEquiv_apply (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] {E F : Type*} (σ τ : E → F) (x : equalizer (compRight R S σ) (compRight R S τ))
    (i : F) :
    (AlgHom.equalizerCompRightEquiv R S σ τ) x (Function.Coequalizer.mk σ τ i) =
      x.val i :=
  rfl

namespace RingHom

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

variable {P} in
lemma OfLocalizationSpan.pi (hP : OfLocalizationSpan P)
    (hPi : RespectsIso P)
    {ι : Type u} [_root_.Finite ι]
    (R : ι → Type u) (S : ι → Type u) [∀ i, CommRing (R i)]
    [∀ i, CommRing (S i)] (f : ∀ i, R i →+* S i)
    (hf : ∀ i, P (f i)) :
    P (Pi.ringHom <| fun i ↦ (f i).comp <| Pi.evalRingHom R i) := by
  classical
  have := Ideal.span_single_eq_top R
  apply hP.ofIsLocalization hPi _ _ this
  rintro ⟨r, i, rfl⟩
  let i₁ : Algebra (∀ i, R i) (R i) := (Pi.evalRingHom R i).toAlgebra
  let i₂ : Algebra (∀ i, S i) (S i) := (Pi.evalRingHom S i).toAlgebra
  refine ⟨R i, S i, inferInstance, inferInstance, i₁, i₂, ?_, ?_, f i, ?_, hf i⟩
  · refine IsLocalization.away_of_isIdempotentElem ?_ (RingHom.ker_evalRingHom _ _)
      ((Pi.evalRingHom R i).surjective)
    simp [IsIdempotentElem, ← Pi.single_mul_left]
  · have : (Pi.ringHom fun i ↦ (f i).comp <| Pi.evalRingHom R i)
        (Pi.single i 1) = Pi.single i 1 := by
      ext j
      simp only [Pi.single, Pi.ringHom_apply, coe_comp, Function.comp_apply, Pi.evalRingHom_apply,
        Function.update, Pi.zero_apply]
      by_cases h : j = i
      · subst h
        simp
      · simp [h]
    simp [this]
    refine IsLocalization.away_of_isIdempotentElem ?_ (RingHom.ker_evalRingHom _ _)
      ((Pi.evalRingHom S i).surjective)
    simp [IsIdempotentElem, ← Pi.single_mul_left]
  · ext j x
    simp [RingHom.algebraMap_toAlgebra]

lemma _root_.Pi.algebraMap_instAlgebraForall_apply {ι : Type*} (A : ι → Type*)
    [∀ i, Semiring (A i)] (S : ι → Type*) [∀ i, CommSemiring (S i)]
    [∀ i, Algebra (S i) (A i)] (x : ∀ i, S i) :
    algebraMap (∀ i, S i) (∀ i, A i) x = fun i ↦ algebraMap (S i) (A i) (x i) :=
  rfl

instance (R M N : Type*) [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Flat R M] [Module.Flat R N] :
    Module.Flat R (M × N) := by
  refine ⟨fun P _ _ _ Q _ ↦ ?_⟩
  have heq :
      LinearMap.rTensor (M × N) Q.subtype =
        (TensorProduct.prodRight _ _ _ _ _).symm.toLinearMap ∘ₗ
          LinearMap.prodMap (Q.subtype.rTensor M) (Q.subtype.rTensor N) ∘ₗ
          (TensorProduct.prodRight _ _ _ _ _).toLinearMap := by
    ext <;>
    · apply (TensorProduct.prodRight R R P M N).injective
      simp
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective,
    EquivLike.injective_comp, heq]
  apply Function.Injective.prodMap <;>
    exact Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective

instance {ι : Type*} (R : Type*) [CommRing R] [_root_.Finite ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Flat R (M i)] :
    Module.Flat R (∀ i, M i) := by
  refine Module.pi_induction' (ι := ι) R (motive := fun N _ _ ↦ Module.Flat R N)
    (motive' := fun N _ _ ↦ Module.Flat R N)
      ?_ ?_ ?_ ?_ M inferInstance
  · intro N N' _ _ _ _ e _
    exact Module.Flat.of_linearEquiv e.symm
  · intro N N' _ _ _ _ e _
    exact Module.Flat.of_linearEquiv e.symm
  · infer_instance
  · intros
    infer_instance

lemma CodescendsAlong.of_forall_flat {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hPi : RespectsIso P) (hPl : OfLocalizationSpan P) (hP : CodescendsAlong P FaithfullyFlat)
    {ι : Type u} (T : ι → Type u) [∀ i, CommRing (T i)]
    [∀ i, Algebra R (T i)] [∀ i, Module.Flat R (T i)]
    (ho : ∀ i, IsOpen <| Set.range (algebraMap R (T i)).specComap)
    (hunion : ⋃ i, Set.range (algebraMap R (T i)).specComap = Set.univ)
    (H : ∀ i, P (algebraMap (T i) (T i ⊗[R] S))) :
    P (algebraMap R S) := by
  classical
  let U (i : ι) : Set (PrimeSpectrum R) :=
    Set.range <| (algebraMap R (T i)).specComap
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U (fun p ↦ ho _) (hunion ▸ le_rfl)
  let A : Type u := ∀ (p : t), T p.1
  have : Module.FaithfullyFlat R A := by
    apply Module.FaithfullyFlat.of_specComap_surjective
    intro p
    obtain ⟨i, hi, q, rfl⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ p))
    use (Pi.evalRingHom (fun p : t ↦ T p.1) ⟨i, hi⟩).specComap q
    rfl
  apply hP.algebraMap_tensorProduct (R := R) (S := A) (T := S)
  rwa [faithfullyFlat_algebraMap_iff]
  let e : A ⊗[R] S ≃ₐ[R] ∀ i : t, T i.val ⊗[R] S :=
    (Algebra.TensorProduct.comm ..).trans <|
      (Algebra.TensorProduct.piRight R R S (fun i : t ↦ T i)).trans <|
        .piCongrRight fun i ↦ Algebra.TensorProduct.comm ..
  have : algebraMap A (A ⊗[R] S) = e.symm.toRingHom.comp
      (algebraMap A <| ∀ p : t, T p.1 ⊗[R] S) := by
    ext i x
    simp [e, A, Pi.algebraMap_instAlgebraForall_apply, ← AlgEquiv.symm_toRingEquiv,
      AlgEquiv.piCongrRight, Algebra.TensorProduct.piRight]
  rw [this]
  apply hPi.1
  exact hPl.pi hPi _ _ _ (fun i ↦ H i.1)

lemma CodescendsAlong.of_forall_exists_flat {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hPi : RespectsIso P) (hPl : OfLocalizationSpan P)
    (hP : CodescendsAlong P FaithfullyFlat)
    (H : ∀ (p : PrimeSpectrum R), ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T),
      p ∈ Set.range (algebraMap R T).specComap ∧ Module.Flat R T ∧
      IsOpen (Set.range <| (algebraMap R T).specComap) ∧
      P (algebraMap T (T ⊗[R] S))) :
    P (algebraMap R S) := by
  choose T h1 h2 hmem _ ho hT using H
  exact hP.of_forall_flat _ hPi hPl T ho (Set.iUnion_eq_univ_iff.mpr fun p ↦ ⟨p, hmem p⟩) hT

open AlgebraicGeometry CategoryTheory Limits in
lemma PrimeSpectrum.range_comap_tensorProduct (R S T : Type u) [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    Set.range (PrimeSpectrum.comap <| algebraMap S (S ⊗[R] T)) =
      (PrimeSpectrum.comap (algebraMap R S)) ⁻¹'
        (Set.range <| PrimeSpectrum.comap (algebraMap R T)) := by
  ext p
  refine ⟨?_, ?_⟩
  · rintro ⟨p, rfl⟩
    use PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom p
    have : (algebraMap S (S ⊗[R] T)).comp (algebraMap R S) =
        Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap R T) := by ext; simp
    exact congr(PrimeSpectrum.comap $(this) p).symm
  · rintro ⟨q, hp⟩
    obtain ⟨z, hz⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
      (X := Spec <| .of S) (Y := Spec <| .of T) (S := Spec <| .of R)
        (f := Spec.map <| CommRingCat.ofHom (algebraMap R S))
        (g := Spec.map <| CommRingCat.ofHom (algebraMap R T)) p q hp.symm
    let e : pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (Spec.map (CommRingCat.ofHom (algebraMap R T))) ≅ Spec (.of <| S ⊗[R] T) :=
      pullbackSpecIso R S T
    use e.hom.base z
    rw [← hz.1, ← pullbackSpecIso_hom_fst]
    rfl

set_option maxHeartbeats 0 in
lemma CodescendsAlong.algHom_of_forall_exists_flat {R A B : Type u} [CommRing R]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (hPi : RespectsIso P) (hPl : OfLocalizationSpan P)
    (hP : CodescendsAlong P FaithfullyFlat)
    (f : A →ₐ[R] B)
    (H : ∀ (p : PrimeSpectrum R), ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T),
      p ∈ Set.range (algebraMap R T).specComap ∧ Module.Flat R T ∧
      IsOpen (Set.range <| (algebraMap R T).specComap) ∧
      P (Algebra.TensorProduct.map (.id T T) f).toRingHom) :
    P f.toRingHom := by
  algebraize [f.toRingHom]
  apply hP.of_forall_exists_flat _ hPi hPl
  intro p
  obtain ⟨T, _, _, ⟨q, hq⟩, hflat, ho, hp⟩ := H ((algebraMap R A).specComap p)
  have heq : Set.range (algebraMap A (A ⊗[R] T)).specComap =
      (PrimeSpectrum.comap (algebraMap R A)) ⁻¹'
        (Set.range <| PrimeSpectrum.comap (algebraMap R T)) :=
    PrimeSpectrum.range_comap_tensorProduct R A T
  let e : T ⊗[R] B ≃ₐ[R] (A ⊗[R] T) ⊗[A] B :=
    .trans ((Algebra.TensorProduct.comm _ _ _).restrictScalars R)
      (.trans
        ((Algebra.TensorProduct.cancelBaseChange R A A B T).symm.restrictScalars R)
        ((Algebra.TensorProduct.comm _ _ _).restrictScalars R))
  have hdiag' :
    IsScalarTower.toAlgHom R (A ⊗[R] T) ((A ⊗[R] T) ⊗[A] B) =
      (AlgHom.comp e.toAlgHom
        ((Algebra.TensorProduct.map (AlgHom.id T T) f).restrictScalars R)).comp
        (Algebra.TensorProduct.comm _ _ _).toAlgHom := by
    ext a
    · suffices h : (a ⊗ₜ[R] (1 : T)) ⊗ₜ[A] (1 : B) = (1 ⊗ₜ[R] 1) ⊗ₜ[A] f a by
        simp [e, h]
      rw [← mul_one a, ← smul_eq_mul, ← TensorProduct.smul_tmul', TensorProduct.smul_tmul,
        Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra, smul_eq_mul, mul_one,
        AlgHom.toRingHom_eq_coe, coe_coe]
    · simp [e]
  replace hdiag' := congr($(hdiag').toRingHom)
  simp only [AlgHom.toRingHom_eq_coe, IsScalarTower.coe_toAlgHom,
    AlgEquiv.toAlgHom_eq_coe, AlgHom.comp_toRingHom] at hdiag'
  refine ⟨A ⊗[R] T, inferInstance, inferInstance, ?_, inferInstance, ?_, ?_⟩
  · rw [heq]
    use q
    exact hq
  · rw [heq]
    exact ho.preimage (PrimeSpectrum.comap (algebraMap R A)).2
  · rw [hdiag']
    exact hPi.2 _ (Algebra.TensorProduct.comm R A T).toRingEquiv
      (hPi.1 _ e.toRingEquiv hp)

end RingHom

section

variable {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R S] [Algebra R B]

/--
A property `P` of ring homomorphisms is said to have stable equalizers, if the equalizer
of algebra maps between algebras with structure morphisms satisfying `P`, is preserved by
arbitrary base change.
-/
def HasStableEqualizers (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop) : Prop :=
  ∀ {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R S] [Algebra R B]
    (f g : A →ₐ[R] B), P (algebraMap R A) → P (algebraMap R B) →
    Function.Bijective (f.tensorEqualizer R S g)

def AlgHom.IsSplit (f : A →ₐ[R] B) : Prop :=
  ∃ (n m : ℕ) (eA : A ≃ₐ[R] (Fin n → R)) (eB : B ≃ₐ[R] (Fin m → R))
    (σ : Fin m → Fin n),
    f = eB.symm.toAlgHom.comp ((AlgHom.compRight R R σ).comp eA)

lemma AlgHom.IsSplit.mk (f : A →ₐ[R] B) {E F : Type*} [_root_.Finite E] [_root_.Finite F]
    (eA : A ≃ₐ[R] (E → R)) (eB : B ≃ₐ[R] (F → R)) (σ : F → E)
    (h : eB.toAlgHom.comp f = (AlgHom.compRight R R σ).comp eA.toAlgHom) :
    f.IsSplit := by
  cases nonempty_fintype E
  cases nonempty_fintype F
  let eE := Fintype.equivFin E
  let eF := Fintype.equivFin F
  refine ⟨Fintype.card E, Fintype.card F, eA.trans ?_, eB.trans ?_, eE ∘ σ ∘ eF.symm, ?_⟩
  · exact AlgEquiv.piCongrLeft R (fun _ ↦ R) eE
  · exact AlgEquiv.piCongrLeft R (fun _ ↦ R) eF
  · ext x
    apply eB.injective
    have := DFunLike.congr_fun h x
    simp only [AlgEquiv.toAlgHom_eq_coe, coe_comp, AlgHom.coe_coe, Function.comp_apply] at this
    ext i
    simp [this, AlgHom.compRight, AlgEquiv.piCongrLeft, AlgEquiv.piCongrLeft']

noncomputable
def Algebra.TensorProduct.piScalarRight (R S A : Type*) [CommSemiring R] [CommSemiring S]
    [Algebra R S] [CommSemiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    A ⊗[R] (ι → R) ≃ₐ[S] ι → A :=
  (Algebra.TensorProduct.piRight R S A (fun _ : ι ↦ R)).trans <|
    AlgEquiv.piCongrRight (fun _ ↦ Algebra.TensorProduct.rid R S A)

@[simp]
lemma Algebra.TensorProduct.piScalarRight_tmul (R S A : Type*) [CommSemiring R] [CommSemiring S]
    [Algebra R S] [CommSemiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (x : A) (y : ι → R) :
    piScalarRight R S A ι (x ⊗ₜ y) = fun i ↦ y i • x :=
  rfl

lemma AlgHom.compRight_apply' {E F : Type*} (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (σ : E → F) (x : F → S) :
    AlgHom.compRight R S σ x = fun i ↦ x (σ i) :=
  rfl

variable (S) in
lemma AlgHom.IsSplit.tensorProductMap {f : A →ₐ[R] B} (hf : f.IsSplit) :
    (Algebra.TensorProduct.map (.id S S) f).IsSplit := by
  obtain ⟨n, m, eA, eB, σ, hf⟩ := hf
  refine AlgHom.IsSplit.mk (E := Fin n) (F := Fin m) _
    ((Algebra.TensorProduct.congr .refl eA).trans (Algebra.TensorProduct.piScalarRight ..))
    ((Algebra.TensorProduct.congr .refl eB).trans (Algebra.TensorProduct.piScalarRight ..)) σ ?_
  ext a
  simp [hf]

variable (S) in
lemma AlgHom.IsSplit.iff_of_isScalarTower
    (T : Type u) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] (f : A →ₐ[R] B) :
    (Algebra.TensorProduct.map (.id T T) f).IsSplit ↔
      (Algebra.TensorProduct.map (.id T T)
        (Algebra.TensorProduct.map (.id S S) f)).IsSplit := by
  refine ⟨?_, ?_⟩
  · rintro ⟨n, m, eA, eB, σ, hf⟩
    refine AlgHom.IsSplit.mk (E := Fin n) (F := Fin m) _ ?_ ?_ σ ?_
    exact (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans eA
    exact (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans eB
    ext a i
    have := DFunLike.congr_fun hf (1 ⊗ₜ a)
    simp only [Algebra.TensorProduct.map_tmul, coe_id, id_eq, AlgEquiv.toAlgHom_eq_coe, coe_comp,
      AlgHom.coe_coe, Function.comp_apply] at this
    simp [this]
  · rintro ⟨n, m, eA, eB, σ, hf⟩
    refine AlgHom.IsSplit.mk (E := Fin n) (F := Fin m) _ ?_ ?_ σ ?_
    exact (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm.trans eA
    exact (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm.trans eB
    ext a i
    have := DFunLike.congr_fun hf (1 ⊗ₜ (1 ⊗ₜ a))
    simp only [Algebra.TensorProduct.map_tmul, coe_id, id_eq, AlgEquiv.toAlgHom_eq_coe, coe_comp,
      AlgHom.coe_coe, Function.comp_apply] at this
    simp [this]

lemma RingHom.Bijective.ofLocalizationSpan :
    RingHom.OfLocalizationSpan (fun f ↦ Function.Bijective f) := by
  introv R hs hf
  algebraize [f]
  let f' (r : s) :=
    (IsScalarTower.toAlgHom R S (Localization.Away (Algebra.ofId R S <| r.val))).toLinearMap
  have (r : s) : IsLocalizedModule (Submonoid.powers r.val) (f' r) := by
    rw [isLocalizedModule_iff_isLocalization]
    have : Algebra.algebraMapSubmonoid S (.powers r.val) = .powers (Algebra.ofId R S <| r.val) :=
      Submonoid.map_powers _ r.val
    rw [this]
    infer_instance
  apply bijective_of_isLocalized_span s hs (F := Algebra.linearMap R S)
    (fun x : s ↦ Localization.Away x.val) (fun x : s ↦ Algebra.linearMap _ _) _ f'
  intro r
  let fr := (Localization.awayMapₐ (Algebra.ofId R S) r.val).toLinearMap
  have heq :
      (IsLocalizedModule.map (.powers r.val) (Algebra.linearMap R (Localization.Away r.val))
      (f' r))
        (Algebra.linearMap R S) =
        (Localization.awayMapₐ (Algebra.ofId R S) r.val).toLinearMap := by
    apply IsLocalizedModule.linearMap_ext (.powers r.val)
      (f := (Algebra.linearMap R (Localization.Away r.val)))
      (f' := f' r)
    rw [IsLocalizedModule.map_comp]
    ext
    simp [f']
  rw [heq]
  exact hf r

namespace Algebra

lemma exists_isSplitOfRank [Module.Finite R A] [Algebra.Etale R A]
    (p : PrimeSpectrum R) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (n : ℕ),
      Module.Flat R S ∧
      IsOpenMap (PrimeSpectrum.comap (algebraMap R S)) ∧
      p ∈ Set.range (algebraMap R S).specComap ∧
      Algebra.IsSplitOfRank n S (S ⊗[R] A) := by
  wlog h : ∃ (n : ℕ), Module.rankAtStalk (R := R) A = n
  · obtain ⟨r, hr, hn⟩ := Algebra.exists_cover_rankAtStalk_eq A p.asIdeal
    obtain ⟨p', rfl⟩ : p ∈ Set.range
        (PrimeSpectrum.comap <| algebraMap R (Localization.Away r)) := by
      rwa [PrimeSpectrum.localization_away_comap_range _ r]
    obtain ⟨S, _, _, n, _, ho, ⟨q, rfl⟩, h⟩ := this p' ⟨_, hn⟩
    let _ : Algebra R S := Algebra.compHom S (algebraMap R (Localization.Away r))
    have : IsScalarTower R (Localization.Away r) S := IsScalarTower.of_algebraMap_eq' rfl
    let e : S ⊗[Localization.Away r] Localization.Away r ⊗[R] A ≃ₐ[S] S ⊗[R] A :=
      TensorProduct.cancelBaseChange ..
    refine ⟨S, inferInstance, inferInstance, n, ?_, ?_, ⟨q, rfl⟩, ?_⟩
    · exact Module.Flat.trans R (Localization.Away r) S
    · rw [IsScalarTower.algebraMap_eq R (Localization.Away r) S, PrimeSpectrum.comap_comp,
        ContinuousMap.coe_comp]
      exact (PrimeSpectrum.localization_away_isOpenEmbedding _ r).isOpenMap.comp ho
    · exact IsSplitOfRank.of_equiv (S := S ⊗[Localization.Away r] Localization.Away r ⊗[R] A) e
  obtain ⟨n, hn⟩ := h
  obtain ⟨S, _, _, _, _, hS⟩ := Algebra.IsSplitOfRank.exists_isSplitOfRank_tensorProduct hn
  obtain ⟨p, rfl⟩ := PrimeSpectrum.specComap_surjective_of_faithfullyFlat (B := S) p
  have homap : IsOpenMap (PrimeSpectrum.comap (algebraMap R S)) :=
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
  refine ⟨S, inferInstance, inferInstance, n, ?_, homap, ⟨p, rfl⟩, hS⟩
  exact Module.Flat.trans _ S _

lemma exists_isSplit [Module.Finite R A] [Algebra.Etale R A]
    [Module.Finite R B] [Algebra.Etale R B] (f : A →ₐ[R] B)
    (p : PrimeSpectrum R) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Module.Flat R S ∧
      IsOpenMap (PrimeSpectrum.comap (algebraMap R S)) ∧
      p ∈ Set.range (algebraMap R S).specComap ∧
      (TensorProduct.map (AlgHom.id S S) f).IsSplit := by
  classical
  wlog h : ∃ (n : ℕ), IsSplitOfRank n R A
  · obtain ⟨S, _, _, n, _, ho₁, ⟨p, rfl⟩, hS⟩ := exists_isSplitOfRank p (A := A)
    obtain ⟨S', _, _, _, ho₂, ⟨q, rfl⟩, hS'⟩ := this (TensorProduct.map (.id S S) f) p ⟨n, hS⟩
    let _ : Algebra R S' := Algebra.compHom S' (algebraMap R S)
    have : IsScalarTower R S S' := .of_algebraMap_eq' rfl
    refine ⟨S', inferInstance, inferInstance, Module.Flat.trans R S S', ?_, ⟨q, rfl⟩, ?_⟩
    · rw [IsScalarTower.algebraMap_eq R S S', PrimeSpectrum.comap_comp, ContinuousMap.coe_comp]
      exact ho₁.comp ho₂
    · rwa [AlgHom.IsSplit.iff_of_isScalarTower S]
  obtain ⟨n, hn⟩ := h
  wlog h : ∃ (m : ℕ), IsSplitOfRank m R B
  · obtain ⟨S, _, _, m, _, ho₁, ⟨p, rfl⟩, hS⟩ := exists_isSplitOfRank p (A := B)
    obtain ⟨S', _, _, _, ho₂, ⟨q, rfl⟩, hS'⟩ := this
      (A := S ⊗[R] A) (B := S ⊗[R] B) (R := S)
      (TensorProduct.map (.id S S) f) p n inferInstance ⟨m, hS⟩
    let _ : Algebra R S' := Algebra.compHom S' (algebraMap R S)
    have : IsScalarTower R S S' := .of_algebraMap_eq' rfl
    refine ⟨S', inferInstance, inferInstance, Module.Flat.trans R S S', ?_, ⟨q, rfl⟩, ?_⟩
    · rw [IsScalarTower.algebraMap_eq R S S', PrimeSpectrum.comap_comp, ContinuousMap.coe_comp]
      exact ho₁.comp ho₂
    · rwa [AlgHom.IsSplit.iff_of_isScalarTower S]
  obtain ⟨⟨eA⟩⟩ := hn
  obtain ⟨m, ⟨⟨eB⟩⟩⟩ := h
  let f' : (Fin n → R) →ₐ[R] Fin m → R := eB.toAlgHom.comp (f.comp eA.symm.toAlgHom)
  obtain ⟨r, hr, σ, hσ⟩ := AlgHom.exists_cover_eq_compRight'' f' p.asIdeal
  refine ⟨Localization.Away r, inferInstance, inferInstance, inferInstance,
      ?_, ?_, ?_⟩
  · exact (PrimeSpectrum.localization_away_isOpenEmbedding _ r).isOpenMap
  · show p ∈ Set.range (PrimeSpectrum.comap <| algebraMap R (Localization.Away r))
    rwa [PrimeSpectrum.localization_away_comap_range _ r]
  · let e := TensorProduct.piScalarRight R (Localization.Away r) (Localization.Away r) (Fin m)
    apply AlgHom.IsSplit.mk (E := Fin n) (F := Fin m) _
      (TensorProduct.congr .refl eA |>.trans (TensorProduct.piScalarRight ..))
      (TensorProduct.congr .refl eB |>.trans (TensorProduct.piScalarRight ..)) σ
    ext a : 2
    simpa [f', e] using congr(e ($(hσ) (1 ⊗ₜ eA a)))

local notation f " ≟ₐ " g => AlgHom.equalizer f g
local notation S " ⊗ₘ " f => Algebra.TensorProduct.map (AlgHom.id S S) f

lemma tensorEqualizer_compRight_bijective {E F : Type*} [Finite E] [Finite F]
    (σ τ : E → F) :
    Function.Bijective ((AlgHom.compRight R R σ).tensorEqualizer S S (.compRight R R τ)) := by
  classical
  cases nonempty_fintype E
  cases nonempty_fintype F
  cases nonempty_fintype (Function.Coequalizer σ τ)
  set f : (F → R) →ₐ[R] E → R := AlgHom.compRight R R σ
  set g : (F → R) →ₐ[R] E → R := AlgHom.compRight R R τ
  let eL : S ⊗[R] (F → R) ≃ₐ[S] F → S :=
    Algebra.TensorProduct.piScalarRight R S S F
  let eR : S ⊗[R] (E → R) ≃ₐ[S] E → S :=
    Algebra.TensorProduct.piScalarRight R S S E
  let eq₂ : S ⊗[R] (Function.Coequalizer σ τ → R) ≃ₐ[S] Function.Coequalizer σ τ → S :=
    Algebra.TensorProduct.piScalarRight R S S (Function.Coequalizer σ τ)
  let e₁ := AlgHom.equalizerCompRightEquiv R R σ τ
  let e₂ := AlgHom.equalizerCompRightEquiv S S σ τ
  let _ : AddCommMonoid ↥(f ≟ₐ g) := AddCommGroup.toAddCommMonoid
  let eq₁ : S ⊗[R] (f ≟ₐ g) ≃ₐ[S] S ⊗[R] (Function.Coequalizer σ τ → R) :=
    TensorProduct.congr AlgEquiv.refl e₁
  let eq₃ : ↥(TensorProduct.map (AlgHom.id S S) f ≟ₐ TensorProduct.map (AlgHom.id S S) g) ≃ₐ[S]
      (AlgHom.compRight S S σ) ≟ₐ (AlgHom.compRight S S τ) :=
    AlgHom.equalizerCongr eL eR (by ext; simp [eL, eR, f]) (by ext; simp [eL, eR, g])
  have : AlgHom.tensorEqualizer S S f g =
      AlgHom.comp (.comp (.comp eq₃.symm.toAlgHom e₂.symm.toAlgHom)
        eq₂.toAlgHom) eq₁.toAlgHom := by
    ext x
    apply (TensorProduct.piScalarRight R S S F).injective
    simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
      TensorProduct.includeRight_apply, AlgHom.coe_tensorEqualizer, TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq, Subalgebra.coe_val, TensorProduct.piScalarRight_tmul, smul_def, mul_one,
      AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom,
      AlgHom.equalizerCongr_symm_apply, AlgEquiv.apply_symm_apply, eq₁, eq₂, e₁, e₂, eq₃, eL]
    ext i
    rw [AlgHom.equalizerCompRightEquiv_symm_apply, AlgHom.equalizerCompRightEquiv_apply]
  rw [this]
  dsimp
  exact eq₃.symm.bijective.comp (e₂.symm.bijective.comp <| eq₂.bijective.comp eq₁.bijective)

lemma TensorProduct.map_bijective_of_bijective {R S A B C D : Type*} [CommSemiring R]
    [CommSemiring S] [Algebra R S]
    [Semiring A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C] [Algebra S C]
    [IsScalarTower R S C] [Semiring D] [Algebra R D] {f : A →ₐ[S] C} {g : B →ₐ[R] D}
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (TensorProduct.map f g) :=
  TensorProduct.congr (.ofBijective f hf) (.ofBijective g hg) |>.bijective

lemma tensorEqualizer_comp_comp {R : Type*} (S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    {A A' : Type*} {B B' : Type*} [CommRing A] [CommRing A']
    [CommRing B] [CommRing B'] [Algebra R A] [Algebra R A']
    [Algebra R B] [Algebra R B'] (f g : A' →ₐ[R] B')
    (eA : A ≃ₐ[R] A') (eB : B ≃ₐ[R] B') :
    AlgHom.tensorEqualizer S T
      (eB.symm.toAlgHom.comp (f.comp eA.toAlgHom))
      (eB.symm.toAlgHom.comp (g.comp eA.toAlgHom)) =
        AlgHom.comp
          (AlgHom.equalizerCongr
            (TensorProduct.congr .refl eA.symm)
            (TensorProduct.congr .refl eB.symm)
            (by ext <;> simp) (by ext <;> simp)).toAlgHom
          (AlgHom.comp (AlgHom.tensorEqualizer S T f g)
          (TensorProduct.congr .refl
            (AlgHom.equalizerCongr eA eB (by ext; simp) (by ext; simp))).toAlgHom) := by
  ext t
  simp [AlgHom.tensorEqualizer_tmul_one', AlgHom.equalizerCongr_apply]
  simp [AlgHom.tensorEqualizer_one_tmul, AlgHom.equalizerCongr_apply]

set_option maxHeartbeats 0 in
/-- The natural map `S ⊗[R] eq(f, g) →ₐ[S] eq(S ⊗ f, S ⊗ g)` is an isomorphism for
arbitrary `S` if `A` and `B` are finite étale over `R`. -/
nonrec theorem tensorEqualizer_bijective_of_finite_of_etale (f g : A →ₐ[R] B)
    [Module.Finite R A] [Algebra.Etale R A] [Module.Finite R B] [Algebra.Etale R B] :
    Function.Bijective (f.tensorEqualizer R S g) := by
  wlog hf : f.IsSplit
  · apply RingHom.FaithfullyFlat.bijective_codescendsAlong.algHom_of_forall_exists_flat
    · exact RingHom.Bijective.respectsIso
    · exact RingHom.Bijective.ofLocalizationSpan
    · intro p
      obtain ⟨T, _, _, _, ho, hmem, hf⟩ := exists_isSplit f p
      refine ⟨T, inferInstance, inferInstance, hmem, inferInstance, ho.isOpen_range, ?_⟩
      apply (TensorProduct.map_tensorEqualizer_bijective_iff_tensorEqualizer_map_bijective ..).mpr
      apply this
      exact hf
  obtain ⟨n, m, eA, eB, σ, rfl⟩ := hf
  let g' : (Fin n → R) →ₐ[R] (Fin m → R) :=
    eB.toAlgHom.comp (g.comp eA.symm.toAlgHom)
  have : g = eB.symm.toAlgHom.comp (g'.comp eA.toAlgHom) := by ext; simp [g']
  rw [this]
  have : Function.Bijective (AlgHom.tensorEqualizer R S (.compRight R R σ) g') := by
    let _ : AddCommMonoid ↥(AlgHom.compRight R R σ ≟ₐ g') := AddCommGroup.toAddCommMonoid
    let _ : CommRing (S ⊗[R] ↥(AlgHom.compRight R R σ ≟ₐ g')) := inferInstance
    apply RingHom.FaithfullyFlat.bijective_codescendsAlong.algHom_of_forall_exists_flat
      (B := TensorProduct.map (AlgHom.id R S) (.compRight R R σ) ≟ₐ TensorProduct.map (.id R S) g')
    · exact RingHom.Bijective.respectsIso
    · exact RingHom.Bijective.ofLocalizationSpan
    · intro p
      obtain ⟨r, hr, τ, h⟩ := AlgHom.exists_cover_eq_compRight'' g' p.asIdeal
      refine ⟨Localization.Away r, inferInstance, inferInstance, ?_, inferInstance, ?_, ?_⟩
      · show p ∈ Set.range (PrimeSpectrum.comap <| algebraMap R (Localization.Away r))
        rw [PrimeSpectrum.localization_away_comap_range _ r]
        exact hr
      · show IsOpen <| Set.range (PrimeSpectrum.comap <| algebraMap R (Localization.Away r))
        rw [PrimeSpectrum.localization_away_comap_range _ r]
        exact PrimeSpectrum.isOpen_basicOpen
      · apply (TensorProduct.map_tensorEqualizer_bijective_iff_tensorEqualizer_map_bijective ..).mpr
        rw [h]
        apply (TensorProduct.map_tensorEqualizer_bijective_iff_tensorEqualizer_map_bijective ..).mp
        apply TensorProduct.map_bijective_of_bijective
        exact Function.bijective_id
        apply tensorEqualizer_compRight_bijective
  erw [tensorEqualizer_comp_comp]
  dsimp
  apply Function.Bijective.comp
  apply AlgEquiv.bijective
  apply Function.Bijective.comp
  exact this
  apply AlgEquiv.bijective

end Algebra

end
