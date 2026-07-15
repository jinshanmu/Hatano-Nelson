import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Topology of components of bounded open sets

These general lemmas isolate the component topology used in
`lem:component`: components of an open set in a locally connected space are
open, their frontiers lie outside the ambient open set, and bounded metric
components have compact closure in a proper space.
-/

namespace ConnectedPseudospectrum

open Set Filter

/-- A connected component of an open set is relatively closed in that open
set: every closure point which remains in the ambient set already belongs to
the component. -/
theorem closure_connectedComponentIn_inter_subset
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {Ω : Set X} (hΩ : IsOpen Ω) (z : X) :
    closure (connectedComponentIn Ω z) ∩ Ω ⊆
      connectedComponentIn Ω z := by
  rintro p ⟨hpclosure, hpΩ⟩
  let C := connectedComponentIn Ω z
  let D := connectedComponentIn Ω p
  have hDopen : IsOpen D := hΩ.connectedComponentIn
  have hpD : p ∈ D := mem_connectedComponentIn hpΩ
  have hinter : (D ∩ C).Nonempty :=
    (mem_closure_iff_nhds.mp hpclosure) D (hDopen.mem_nhds hpD)
  obtain ⟨q, hqD, hqC⟩ := hinter
  have hDC : D = C := by
    calc
      D = connectedComponentIn Ω q := connectedComponentIn_eq hqD
      _ = C := (connectedComponentIn_eq hqC).symm
  change p ∈ C
  exact hDC ▸ hpD

/-- The frontier of a connected component of an open set cannot remain in
that open set. -/
theorem frontier_connectedComponentIn_subset_compl
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {Ω : Set X} (hΩ : IsOpen Ω) (z : X) :
    frontier (connectedComponentIn Ω z) ⊆ Ωᶜ := by
  intro p hpfront hpΩ
  let C := connectedComponentIn Ω z
  let D := connectedComponentIn Ω p
  have hCopen : IsOpen C := hΩ.connectedComponentIn
  have hDopen : IsOpen D := hΩ.connectedComponentIn
  have hpD : p ∈ D := mem_connectedComponentIn hpΩ
  have hpclosure : p ∈ closure C :=
    frontier_subset_closure hpfront
  have hinter : (D ∩ C).Nonempty :=
    (mem_closure_iff_nhds.mp hpclosure) D (hDopen.mem_nhds hpD)
  obtain ⟨q, hqD, hqC⟩ := hinter
  have hDC : D = C := by
    calc
      D = connectedComponentIn Ω q := connectedComponentIn_eq hqD
      _ = C := (connectedComponentIn_eq hqC).symm
  have hpC : p ∈ C := by
    rw [← hDC]
    exact hpD
  have hpInterior : p ∈ interior C := by
    rw [hCopen.interior_eq]
    exact hpC
  exact hpfront.2 hpInterior

/-- In a proper metric space, the closure of a component of a bounded set is
compact. -/
theorem isCompact_closure_connectedComponentIn
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    {Ω : Set X} (hΩ : Bornology.IsBounded Ω) (z : X) :
    IsCompact (closure (connectedComponentIn Ω z)) := by
  exact (hΩ.subset (connectedComponentIn_subset Ω z)).isCompact_closure

end ConnectedPseudospectrum
