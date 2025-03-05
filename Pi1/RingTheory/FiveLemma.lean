import Mathlib

/-!
# The five lemma in terms of modules
-/

namespace LinearMap

variable {R : Type*} [CommRing R]
variable {M₁ M₂ M₃ M₄ M₅ N₁ N₂ N₃ N₄ N₅ : Type*}
variable [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup M₄] [AddCommGroup M₅]
variable [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄] [Module R M₅]
variable [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [AddCommGroup N₄] [AddCommGroup N₅]
variable [Module R N₁] [Module R N₂] [Module R N₃] [Module R N₄] [Module R N₅]
variable (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃) (f₃ : M₃ →ₗ[R] M₄) (f₄ : M₄ →ₗ[R] M₅)
variable (g₁ : N₁ →ₗ[R] N₂) (g₂ : N₂ →ₗ[R] N₃) (g₃ : N₃ →ₗ[R] N₄) (g₄ : N₄ →ₗ[R] N₅)
variable (i₁ : M₁ →ₗ[R] N₁) (i₂ : M₂ →ₗ[R] N₂) (i₃ : M₃ →ₗ[R] N₃) (i₄ : M₄ →ₗ[R] N₄)
  (i₅ : M₅ →ₗ[R] N₅)
variable (hc₁ : g₁.comp i₁ = i₂.comp f₁) (hc₂ : g₂.comp i₂ = i₃.comp f₂)
  (hc₃ : g₃.comp i₃ = i₄.comp f₃) (hc₄ : g₄.comp i₄ = i₅.comp f₄)
variable (hf₁ : Function.Exact f₁ f₂) (hf₂ : Function.Exact f₂ f₃) (hf₃ : Function.Exact f₃ f₄)
variable (hg₁ : Function.Exact g₁ g₂) (hg₂ : Function.Exact g₂ g₃) (hg₃ : Function.Exact g₃ g₄)

include hf₂ hg₁ hg₂ hc₁ hc₂ hc₃ in
/-- One four lemma in terms of modules. -/
lemma surjective_of (hi₁ : Function.Surjective i₁)
    (hi₃ : Function.Surjective i₃) (hi₄ : Function.Injective i₄) :
    Function.Surjective i₂ := by
  intro x
  obtain ⟨y, hy⟩ := hi₃ (g₂ x)
  have := (DFunLike.congr_fun hc₃ y).symm
  simp only [coe_comp, Function.comp_apply] at this
  rw [hy, hg₂.apply_apply_eq_zero] at this
  rw [map_eq_zero_iff _ hi₄] at this
  obtain ⟨a, rfl⟩ := (hf₂ _).mp this
  have : g₂ (x - i₂ a) = 0 := by
    have := DFunLike.congr_fun hc₂ a
    simp only [coe_comp, Function.comp_apply] at this
    simp [← hy, this]
  obtain ⟨b, hb⟩ := (hg₁ _).mp this
  obtain ⟨o, rfl⟩ := hi₁ b
  use f₁ o + a
  have := DFunLike.congr_fun hc₁ o
  simp only [coe_comp, Function.comp_apply] at this
  simp [← this, hb]

include hf₁ hf₂ hg₁ hc₁ hc₂ hc₃ in
/-- One four lemma in terms of modules. -/
lemma injective_of (hi₁ : Function.Surjective i₁) (hi₂ : Function.Injective i₂)
    (hi₄ : Function.Injective i₄) :
    Function.Injective i₃ := by
  rw [← ker_eq_bot, ker_eq_bot']
  intro m hm
  have : f₃ m = 0 := by
    suffices h : i₄ (f₃ m) = 0 by
      rwa [map_eq_zero_iff _ hi₄] at h
    have := DFunLike.congr_fun hc₃ m
    simp only [coe_comp, Function.comp_apply] at this
    rw [← this, hm]
    simp
  obtain ⟨x, rfl⟩ := (hf₂ m).mp this
  have : g₂ (i₂ x) = 0 := by
    have := DFunLike.congr_fun hc₂ x
    simp only [coe_comp, Function.comp_apply] at this
    rwa [this]
  obtain ⟨y, hy⟩ := (hg₁ _).mp this
  obtain ⟨a, rfl⟩ := hi₁ y
  have := DFunLike.congr_fun hc₁ a
  simp only [coe_comp, Function.comp_apply] at this
  rw [this] at hy
  apply hi₂ at hy
  subst hy
  rw [hf₁.apply_apply_eq_zero]

include hf₁ hf₂ hf₃ hg₁ hg₂ hg₃ hc₁ hc₂ hc₃ hc₄ in
/-- The five lemma in terms of modules. -/
lemma bijective_of (hi₁ : Function.Surjective i₁) (hi₂ : Function.Bijective i₂)
    (hi₄ : Function.Bijective i₄) (hi₅ : Function.Injective i₅) :
    Function.Bijective i₃ :=
  ⟨injective_of f₁ f₂ f₃ g₁ g₂ g₃ i₁ i₂ i₃ i₄ hc₁ hc₂ hc₃ hf₁ hf₂ hg₁ hi₁ hi₂.1 hi₄.1,
    surjective_of f₂ f₃ f₄ g₂ g₃ g₄ i₂ i₃ i₄ i₅ hc₂ hc₃ hc₄ hf₃ hg₂ hg₃ hi₂.2 hi₄.2 hi₅⟩

end LinearMap

variable {M₁ M₂ M₃ M₄ M₅ N₁ N₂ N₃ N₄ N₅ : Type*}
variable [AddGroup M₁] [AddGroup M₂] [AddGroup M₃] [AddGroup M₄] [AddGroup M₅]
variable [AddGroup N₁] [AddGroup N₂] [AddGroup N₃] [AddGroup N₄] [AddGroup N₅]
variable (f₁ : M₁ →+ M₂) (f₂ : M₂ →+ M₃) (f₃ : M₃ →+ M₄) (f₄ : M₄ →+ M₅)
variable (g₁ : N₁ →+ N₂) (g₂ : N₂ →+ N₃) (g₃ : N₃ →+ N₄) (g₄ : N₄ →+ N₅)
variable (i₁ : M₁ →+ N₁) (i₂ : M₂ →+ N₂) (i₃ : M₃ →+ N₃) (i₄ : M₄ →+ N₄)
  (i₅ : M₅ →+ N₅)
variable (hc₁ : g₁.comp i₁ = i₂.comp f₁) (hc₂ : g₂.comp i₂ = i₃.comp f₂)
  (hc₃ : g₃.comp i₃ = i₄.comp f₃) (hc₄ : g₄.comp i₄ = i₅.comp f₄)
variable (hf₁ : Function.Exact f₁ f₂) (hf₂ : Function.Exact f₂ f₃) (hf₃ : Function.Exact f₃ f₄)
variable (hg₁ : Function.Exact g₁ g₂) (hg₂ : Function.Exact g₂ g₃) (hg₃ : Function.Exact g₃ g₄)

include hf₂ hg₁ hg₂ hc₁ hc₂ hc₃ in
/-- One four lemma in terms of modules. -/
lemma surjective_of (hi₁ : Function.Surjective i₁)
    (hi₃ : Function.Surjective i₃) (hi₄ : Function.Injective i₄) :
    Function.Surjective i₂ := by
  intro x
  obtain ⟨y, hy⟩ := hi₃ (g₂ x)
  have := (DFunLike.congr_fun hc₃ y).symm
  simp at this
  rw [hy, hg₂.apply_apply_eq_zero] at this
  rw [map_eq_zero_iff _ hi₄] at this
  obtain ⟨a, rfl⟩ := (hf₂ _).mp this
  have : g₂ (x - i₂ a) = 0 := by
    have := DFunLike.congr_fun hc₂ a
    simp at this
    simp [← hy, this]
  obtain ⟨b, hb⟩ := (hg₁ _).mp this
  obtain ⟨o, rfl⟩ := hi₁ b
  use f₁ o + a
  have := DFunLike.congr_fun hc₁ o
  simp at this
  simp [← this, hb]

include hf₁ hf₂ hg₁ hc₁ hc₂ hc₃ in
/-- One four lemma in terms of modules. -/
lemma injective_of (hi₁ : Function.Surjective i₁) (hi₂ : Function.Injective i₂)
    (hi₄ : Function.Injective i₄) :
    Function.Injective i₃ := by
  rw [injective_iff_map_eq_zero]
  intro m hm
  have : f₃ m = 0 := by
    suffices h : i₄ (f₃ m) = 0 by
      rwa [map_eq_zero_iff _ hi₄] at h
    have := DFunLike.congr_fun hc₃ m
    simp at this
    rw [← this, hm]
    simp
  obtain ⟨x, rfl⟩ := (hf₂ m).mp this
  have : g₂ (i₂ x) = 0 := by
    have := DFunLike.congr_fun hc₂ x
    simp at this
    rwa [this]
  obtain ⟨y, hy⟩ := (hg₁ _).mp this
  obtain ⟨a, rfl⟩ := hi₁ y
  have := DFunLike.congr_fun hc₁ a
  simp at this
  rw [this] at hy
  apply hi₂ at hy
  subst hy
  rw [hf₁.apply_apply_eq_zero]

include hf₁ hf₂ hf₃ hg₁ hg₂ hg₃ hc₁ hc₂ hc₃ hc₄ in
/-- The five lemma in terms of modules. -/
lemma bijective_of (hi₁ : Function.Surjective i₁) (hi₂ : Function.Bijective i₂)
    (hi₄ : Function.Bijective i₄) (hi₅ : Function.Injective i₅) :
    Function.Bijective i₃ :=
  ⟨injective_of f₁ f₂ f₃ g₁ g₂ g₃ i₁ i₂ i₃ i₄ hc₁ hc₂ hc₃ hf₁ hf₂ hg₁ hi₁ hi₂.1 hi₄.1,
    surjective_of f₂ f₃ f₄ g₂ g₃ g₄ i₂ i₃ i₄ i₅ hc₂ hc₃ hc₄ hf₃ hg₂ hg₃ hi₂.2 hi₄.2 hi₅⟩
