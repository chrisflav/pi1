import Mathlib.Algebra.Module.LocalizedModule.Basic

section
-- #22339

section

variable {R A M M' : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (S : Submonoid R)
  [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  [IsLocalization S A]

instance IsLocalizedModule.module_isScalarTower (f : M →ₗ[R] M') [IsLocalizedModule S f] :
    letI : Module A M' := IsLocalizedModule.module S f
    IsScalarTower R A M' :=
  (IsLocalizedModule.iso S f).symm.isScalarTower A

end

end
