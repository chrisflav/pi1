import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Separation.Connected

-- PR #23835

universe u w

--
lemma Set.iUnion_sumElim {α ι σ : Type*} (s : ι → Set α) (t : σ → Set α) :
    ⋃ x, Sum.elim s t x = (⋃ x, s x) ∪ ⋃ x, t x := by
  ext
  simp

--
lemma ENat.card_lt_top_iff_finite {α : Type*} :
    ENat.card α < ⊤ ↔ Finite α := by
  simp [← not_iff_not]

section

variable {X : Type u} {ι : Type w} [TopologicalSpace X]
    {U : ι → Set X} (hclopen : ∀ i, IsClopen (U i)) (hdisj : Pairwise (Function.onFun Disjoint U))
    (hunion : ⋃ i, U i = Set.univ) (hconn : ∀ i, IsPreconnected (U i))

--
lemma IsClopen.connectedComponentIn_eq {U : Set X} (hU : IsClopen U) {x : X} (hx : x ∈ U) :
    connectedComponentIn U x = connectedComponent x :=
  subset_antisymm ((isPreconnected_connectedComponentIn).subset_connectedComponent
    (mem_connectedComponentIn hx)) <|
    (isPreconnected_connectedComponent).subset_connectedComponentIn (mem_connectedComponent)
    (hU.connectedComponent_subset hx)

--
noncomputable
def ConnectedComponents.equivOfIsClopen {X ι : Type*} [TopologicalSpace X] {U : ι → Set X}
    (hU₁ : ∀ i, IsClopen (U i)) (hU₂ : Pairwise (Function.onFun Disjoint U))
    (hU₃ : ⋃ i, U i = Set.univ) :
    ConnectedComponents X ≃ Σ i, ConnectedComponents (U i) := by
  have heq {x : X} {i} (hx : x ∈ U i) :
      Subtype.val '' connectedComponent ⟨x, hx⟩ = connectedComponent x := by
    rw [← connectedComponentIn_eq_image hx, (hU₁ i).connectedComponentIn_eq hx]
  refine .symm <| .ofBijective
    (fun ⟨i, x⟩ ↦
      Quotient.lift (ConnectedComponents.mk ∘ Subtype.val)
        (fun x y (hxy : connectedComponent x = connectedComponent y) ↦ by
          simp [← heq x.2, ← heq y.2, hxy])
        x)
    ⟨fun ⟨i, x⟩ ⟨j, y⟩ hxy ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
    obtain ⟨i, hi⟩ := Set.iUnion_eq_univ_iff.mp hU₃ x
    simp only [Sigma.exists]
    use i, .mk ⟨x, hi⟩
    rfl
  · obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe y
    replace hxy : ConnectedComponents.mk x.val = ConnectedComponents.mk y.val := hxy
    rw [ConnectedComponents.coe_eq_coe] at hxy
    have : i = j := by
      apply hU₂.eq
      rw [Set.not_disjoint_iff]
      exact ⟨x, x.2, (hU₁ j).connectedComponent_subset y.2 (hxy ▸ mem_connectedComponent)⟩
    subst this
    simp [← Set.image_val_inj, heq, hxy]

--
lemma ConnectedComponents.nonempty_iff_nonempty :
    Nonempty (ConnectedComponents X) ↔ Nonempty X :=
  ⟨fun _ ↦ ConnectedComponents.surjective_coe.nonempty, fun h ↦ h.map ConnectedComponents.mk⟩

--
lemma ConnectedComponents.isEmpty_iff_isEmpty :
    IsEmpty (ConnectedComponents X) ↔ IsEmpty X := by
  rw [← not_iff_not, not_isEmpty_iff, not_isEmpty_iff, nonempty_iff_nonempty]

--
instance ConnectedComponents.subsingleton [PreconnectedSpace X] :
    Subsingleton (ConnectedComponents X) := by
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := surjective_coe x
  obtain ⟨y, rfl⟩ := surjective_coe y
  simp_rw [coe_eq_coe, PreconnectedSpace.connectedComponent_eq_univ, ]

--
instance [Nonempty X] : Nonempty (ConnectedComponents X) := by
  rwa [ConnectedComponents.nonempty_iff_nonempty]

--
include hclopen hdisj hunion in
noncomputable
def ConnectedComponents.equivOfIsClopenOfIsConnected (hconn : ∀ i, IsConnected (U i))  :
    ConnectedComponents X ≃ ι :=
  have _ (i) : ConnectedSpace (U i) := isConnected_iff_connectedSpace.mp (hconn i)
  have _ (i) : Unique (ConnectedComponents <| U i) := (nonempty_unique _).some
  (equivOfIsClopen hclopen hdisj hunion).trans (.sigmaUnique _ _)

open Set in
/-- Variant of `isClopen_inter_of_disjoint_cover_clopen` with weaker disjointness condition. -/
lemma isClopen_inter_of_disjoint_cover_clopen' {s a b : Set X} (h : IsClopen s) (cover : s ⊆ a ∪ b)
    (ha : IsOpen a) (hb : IsOpen b) (hab : s ∩ a ∩ b = ∅) : IsClopen (s ∩ a) := by
  rw [show s ∩ a = s ∩ (s ∩ a) by simp]
  refine isClopen_inter_of_disjoint_cover_clopen h ?_ (h.2.inter ha) (h.2.inter hb) ?_
  · rw [← inter_union_distrib_left]
    exact subset_inter .rfl cover
  · rw [disjoint_iff_inter_eq_empty, inter_comm s b, ← inter_assoc, hab, empty_inter]

end

--
open Set in
/-- If `X` has infinitely many connected components, it admits disjoint union decompositions with
arbitrarily many summands. -/
lemma ConnectedComponents.exists_fun_isClopen_of_infinite (X : Type*) [TopologicalSpace X]
    [Infinite (ConnectedComponents X)] (n : ℕ) (hn : 0 < n) :
    ∃ (U : Fin n → Set X), (∀ i, IsClopen (U i)) ∧ (∀ i, (U i).Nonempty) ∧
      Pairwise (Function.onFun Disjoint U) ∧ ⋃ i, U i = Set.univ :=
  suffices h : ∃ (ι : Type) (e : ι ≃ Fin n) (U : ι → Set X), (∀ i, IsClopen (U i)) ∧
      (∀ i, (U i).Nonempty) ∧ Pairwise (Function.onFun Disjoint U) ∧ ⋃ i, U i = Set.univ by
    obtain ⟨ι, e, U, hU1, hU2, hU3, hU4⟩ := h
    refine ⟨U ∘ e.symm, fun i ↦ hU1 _, fun i ↦ hU2 _,
      fun i j h ↦ hU3 <| e.symm.injective.ne_iff.mpr h, iUnion_eq_univ_iff.mpr fun x ↦ ?_⟩
    obtain ⟨i, hi⟩ := Set.iUnion_eq_univ_iff.mp hU4 x
    exact ⟨e i, by simp [hi]⟩
  have : Nonempty X := ConnectedComponents.nonempty_iff_nonempty.mp inferInstance
  match n with
  | 1 => ⟨Unit, Fintype.equivFinOfCardEq rfl, fun _ ↦ Set.univ, by simp [isClopen_univ],
    by simp, Subsingleton.pairwise, by simp [Set.iUnion_const]⟩
  | n + 2 => by
    obtain ⟨U, hU₁, hU₂, hU₃, hU₄⟩ := exists_fun_isClopen_of_infinite X (n + 1) (by simp)
    obtain ⟨i, hi⟩ : ∃ (i : Fin (n + 1)), ¬ IsPreconnected (U i) := by
      by_contra! h
      exact Infinite.not_finite <|
        .of_equiv _ (equivOfIsClopenOfIsConnected hU₁ hU₃ hU₄ fun i ↦ ⟨hU₂ i, h i⟩).symm
    simp only [IsPreconnected, not_forall] at hi
    obtain ⟨V, W, hV, hW, hle, hVU, hWU, h⟩ := hi
    rw [Set.not_nonempty_iff_eq_empty, ← Set.inter_assoc] at h
    have hunion : V ∩ U i ∪ W ∩ U i = U i := by rwa [← union_inter_distrib_right, inter_eq_right]
    refine ⟨{ x : Fin (n + 1) // x ≠ i } ⊕ Unit ⊕ Unit, Fintype.equivFinOfCardEq (by simp),
        Sum.elim (fun j ↦ U j) (Sum.elim (fun _ ↦ V ∩ U i) fun _ ↦ W ∩ U i), ?_, ?_, ?_, ?_⟩
    · rintro (x|-|-)
      apply hU₁
      all_goals simp only [ne_eq, Sum.elim_inr, Sum.elim_inl]; rw [Set.inter_comm]
      · exact isClopen_inter_of_disjoint_cover_clopen' (hU₁ _) hle hV hW h
      · refine isClopen_inter_of_disjoint_cover_clopen' (hU₁ _) (union_comm _ _ ▸ hle) hW hV ?_
        rwa [Set.inter_assoc, Set.inter_comm W V, ← Set.inter_assoc]
    · rintro (x|x|x)
      · exact hU₂ _
      · rwa [Sum.elim_inr, Sum.elim_inl, Set.inter_comm]
      · rwa [Sum.elim_inr, Sum.elim_inr, Set.inter_comm]
    · rintro (x|x|x) (y|y|y) hxy
      · exact hU₃ fun hxy' ↦ hxy (congrArg Sum.inl <| Subtype.ext_iff.mpr hxy')
      · exact Disjoint.inter_right' _ (hU₃ x.2)
      · exact Disjoint.inter_right' _ (hU₃ x.2)
      · exact Disjoint.inter_left' _ (hU₃ <| Ne.symm y.2)
      · contradiction
      · exact Disjoint.inter_right _ (disjoint_iff_inter_eq_empty.mpr <| inter_comm V (U i) ▸ h)
      · exact Disjoint.inter_left' _ (hU₃ <| Ne.symm y.2)
      · apply Disjoint.inter_right _ (disjoint_iff_inter_eq_empty.mpr ?_)
        rwa [Sum.elim_inr, Sum.elim_inr, inter_comm W, inter_assoc, inter_comm W V, ← inter_assoc]
      · contradiction
    · simp only [iUnion_sumElim, iUnion_const, hunion, eq_univ_iff_forall, mem_union, mem_iUnion]
      intro x
      obtain ⟨j, hj⟩ := (Set.iUnion_eq_univ_iff.mp hU₄) x
      by_cases h : j = i
      · exact h ▸ Or.inr hj
      · exact Or.inl ⟨⟨j, h⟩, hj⟩

--
lemma ConnectedComponents.discreteTopology_iff (X : Type*) [TopologicalSpace X] :
    DiscreteTopology (ConnectedComponents X) ↔ ∀ x : X, IsOpen (connectedComponent x) := by
  simp_rw [← singletons_open_iff_discrete, ← connectedComponents_preimage_singleton,
    isQuotientMap_coe.isOpen_preimage, surjective_coe.forall]

/-- If `f : X → Y` is an open and closed map to and `Y` is connected, the number of connected
components of `X` is bounded by the cardinality of the fiber of any point. -/
@[stacks 07VB]
lemma ConnectedComponents.enatCard_le_encard_preimage_singleton {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [ConnectedSpace Y]
    {f : X → Y} (hf₁ : IsOpenMap f) (hf₂ : IsClosedMap f) (y : Y) :
    ENat.card (ConnectedComponents X) ≤ (f ⁻¹' {y}).encard := by
  suffices h : ∀ {n : ℕ} (U : Fin n → Set X) (hU₁ : ∀ i, IsClopen (U i)) (hU₂ : ∀ i, (U i).Nonempty)
      (hU₃ : Pairwise <| Function.onFun Disjoint U) (hU₄ : ⋃ i, U i = Set.univ),
      n ≤ (f ⁻¹' {y}).encard by
    obtain (hy|hy) := finite_or_infinite (ConnectedComponents X)
    · cases nonempty_fintype (ConnectedComponents X)
      simp only [ENat.card_eq_coe_fintype_card]
      refine h (fun i ↦ ConnectedComponents.mk ⁻¹' {(Fintype.equivFin _).symm i}) (fun i ↦ ?_)
          (fun i ↦ ?_) (fun i j hij ↦ Disjoint.preimage _ (by simp [hij])) ?_
      · exact (isClopen_discrete _).preimage continuous_coe
      · exact (Set.singleton_nonempty _).preimage surjective_coe
      · simp [← Set.preimage_iUnion]
    · simp only [ENat.card_eq_top_of_infinite, top_le_iff, ENat.eq_top_iff_forall_ge]
      intro m
      obtain ⟨U, hU1, hU2, hU3, hU4⟩ := exists_fun_isClopen_of_infinite X (m + 1) (by simp)
      exact le_trans (by simp) (h U hU1 hU2 hU3 hU4)
  intro n U hU1 hU2 hU3 hU4
  have heq : f ⁻¹' {y} = ⋃ i, (U i ∩ f ⁻¹' {y}) := by
    conv_lhs => rw [← Set.univ_inter (f ⁻¹' {y}), ← hU4, Set.iUnion_inter]
  rw [heq, Set.encard_iUnion_of_finite fun i j hij ↦ .inter_left _ (.inter_right _ <| hU3 hij),
    finsum_eq_sum_of_fintype]
  trans ∑ i : Fin n, 1
  · simp
  · refine Fintype.sum_mono fun i ↦ Set.one_le_encard_iff_nonempty.mpr (show y ∈ f '' (U i) from ?_)
    convert Set.mem_univ y
    exact IsClopen.eq_univ ⟨hf₂ _ (hU1 i).1, hf₁ _ (hU1 i).2⟩ ((hU2 i).image f)

@[stacks 07VB]
lemma IsOpenMap.finite_connectedComponents_of_finite_preimage_singleton_of_connectedSpace
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [ConnectedSpace Y] {f : X → Y}
    (hf₁ : IsOpenMap f) (hf₂ : IsClosedMap f) {y : Y} (hy : (f ⁻¹' {y}).Finite) :
    Finite (ConnectedComponents X) := by
  rw [← ENat.card_lt_top_iff_finite]
  exact lt_of_le_of_lt (ConnectedComponents.enatCard_le_encard_preimage_singleton hf₁ hf₂ y)
    hy.encard_lt_top

open ConnectedComponents in
/-- If `f : X → Y` is open and closed with finite fibers and `Y` has finitely many connected
components, so does `X`. -/
@[stacks 07VB]
lemma IsOpenMap.finite_connectedComponents_of_finite_preimage_singleton {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Finite (ConnectedComponents Y)] {f : X → Y}
    (hfc : Continuous f) (hf₁ : IsOpenMap f) (hf₂ : IsClosedMap f) (h : ∀ y, (f ⁻¹' {y}).Finite) :
    Finite (ConnectedComponents X) := by
  suffices h : ∀ (y : ConnectedComponents Y), Finite (ConnectedComponents (f ⁻¹' (mk ⁻¹' {y}))) by
    refine .of_equiv _ (equivOfIsClopen (U := fun y ↦ f ⁻¹' (mk ⁻¹' {y})) ?_ ?_ ?_).symm
    · exact fun y ↦ (isClopen_discrete {y}).preimage (continuous_coe.comp hfc)
    · exact fun i j hij ↦ (Disjoint.preimage mk (by simpa)).preimage f
    · rw [Set.iUnion_eq_univ_iff]
      exact fun x ↦ ⟨mk (f x), rfl⟩
  intro y
  obtain ⟨y, rfl⟩ := surjective_coe y
  have := isConnected_iff_connectedSpace.mp (isConnected_connectedComponent (x := y))
  rw [connectedComponents_preimage_singleton]
  refine IsOpenMap.finite_connectedComponents_of_finite_preimage_singleton_of_connectedSpace
    (hf₁.restrictPreimage (connectedComponent y)) (hf₂.restrictPreimage (connectedComponent y))
    (y := ⟨y, mem_connectedComponent⟩) ?_
  rw [← Set.finite_image_iff Subtype.val_injective.injOn]
  convert h y
  aesop (add safe mem_connectedComponent)

instance (X : Type*) [TopologicalSpace X] [LocallyConnectedSpace X] :
    DiscreteTopology (ConnectedComponents X) := by
  rw [ConnectedComponents.discreteTopology_iff]
  exact fun x ↦ isOpen_connectedComponent
