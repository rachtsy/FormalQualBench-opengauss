import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.HausdorffDimension

namespace KakeyaTheorem3D

open Set

abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The closed line segment from `x` to `x + v`. -/
def segmentAlong (x v : R3) : Set R3 := (fun t : ℝ => x + t • v) '' Set.Icc (0 : ℝ) 1

/-- A Kakeya set in `R^3` contains a line segment of length `1` in every direction. -/
def IsKakeyaSet (K : Set R3) : Prop :=
  ∀ v : R3, ‖v‖ = 1 → ∃ x : R3, segmentAlong x v ⊆ K

/-- The three-dimensional Kakeya theorem: every Kakeya set in `R^3` has Hausdorff dimension `3`. -/
theorem MainTheorem :
    ∀ K : Set R3, IsKakeyaSet K → dimH K = (3 : ENNReal) := by
  intro K hK
  apply le_antisymm
  · calc dimH K ≤ dimH (Set.univ : Set R3) := dimH_mono (subset_univ _)
      _ = ↑(Module.finrank ℝ R3) := Real.dimH_univ_eq_finrank R3
      _ = 3 := by simp
  · sorry

end KakeyaTheorem3D
