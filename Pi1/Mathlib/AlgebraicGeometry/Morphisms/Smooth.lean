import Pi1.Mathlib.RingTheory.RingHom.Smooth
import Pi1.RingTheory.SmoothFlat

universe u

namespace AlgebraicGeometry

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSmooth f] : Flat f := by
  rw [HasRingHomProperty.iff_appLE (P := @Flat)]
  intro U V e
  have := HasRingHomProperty.appLE @IsSmooth f inferInstance U V e
  rw [RingHom.locally_isStandardSmooth_iff_smooth] at this
  algebraize [(Scheme.Hom.appLE f U V e).hom]
  have : Algebra.Smooth Γ(Y, U) Γ(X, V) := this
  show Module.Flat _ _
  infer_instance

end AlgebraicGeometry
