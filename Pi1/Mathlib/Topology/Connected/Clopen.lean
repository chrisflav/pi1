import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Connected.CardComponents
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Separation.Connected

universe u w

--
instance {X : Type u} [TopologicalSpace X] [Nonempty X] : Nonempty (ConnectedComponents X) := by
  rwa [ConnectedComponents.nonempty_iff_nonempty]
