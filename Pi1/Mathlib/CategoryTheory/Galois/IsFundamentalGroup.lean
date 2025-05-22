import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

open CategoryTheory

@[simp]
lemma CategoryTheory.Aut.one_hom {C : Type*} [Category C] (X : C) :
    (1 : Aut X).hom = (1 : End X) := rfl

namespace CategoryTheory.PreGaloisCategory

variable {C : Type*} [Category C] (F : C ⥤ FintypeCat)

variable (G : Type*) [Group G] [∀ X, MulAction G (F.obj X)][IsNaturalSMul F G]

lemma ker_toAut : (toAut F G).ker = ⨅ (X : C) (x : F.obj X), MulAction.stabilizer G x := by
  ext g : 1
  simp [MonoidHom.mem_ker, Subgroup.mem_iInf, Aut.ext_iff, NatTrans.ext'_iff, funext_iff,
    FintypeCat.hom_ext_iff]

variable  [GaloisCategory C] [FiberFunctor F]
variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ X, ContinuousSMul G (F.obj X)]

end CategoryTheory.PreGaloisCategory
