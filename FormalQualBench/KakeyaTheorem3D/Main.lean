import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

namespace KakeyaTheorem3D

open Set MeasureTheory

abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The closed line segment from `x` to `x + v`. -/
def segmentAlong (x v : R3) : Set R3 := (fun t : ℝ => x + t • v) '' Set.Icc (0 : ℝ) 1

/-- A Kakeya set in `R^3` contains a line segment of length `1` in every direction. -/
def IsKakeyaSet (K : Set R3) : Prop :=
  ∀ v : R3, ‖v‖ = 1 → ∃ x : R3, segmentAlong x v ⊆ K

lemma segmentAlong_eq_segment (x v : R3) :
    segmentAlong x v = segment ℝ x (x + v) := by
  simp only [segmentAlong, segment_eq_image']
  congr 1; ext t; simp [add_sub_cancel_left]

lemma dimH_segmentAlong_unit (x v : R3) (hv : ‖v‖ = 1) :
    dimH (segmentAlong x v) = 1 := by
  rw [segmentAlong_eq_segment]
  apply dimH_of_hausdorffMeasure_ne_zero_ne_top
  · rw [show ((1 : NNReal) : ℝ) = (1 : ℝ) from by norm_cast, hausdorffMeasure_segment]
    rw [Ne, edist_eq_zero]; intro h
    have : v = 0 := by
      have := sub_eq_zero.mpr h
      simp only [sub_add_cancel_left, neg_eq_zero] at this
      exact this
    norm_num [this] at hv
  · rw [show ((1 : NNReal) : ℝ) = (1 : ℝ) from by norm_cast, hausdorffMeasure_segment]
    exact edist_ne_top x (x + v)

/-- Wang–Zahl (2025): for any Kakeya set K in R^3 and any d < 3, the
    d-dimensional Hausdorff measure of K is infinite.  This is the hard
    analytic core of the 3-dimensional Kakeya conjecture. -/
lemma kakeya_hausdorffMeasure_eq_top (K : Set R3) (hK : IsKakeyaSet K)
    (d : NNReal) (hd : (d : ENNReal) < 3) :
    Measure.hausdorffMeasure (↑d : ℝ) K = ⊤ := by
  by_cases hd1 : (d : ENNReal) < 1
  · -- d < 1: K ⊇ segment with dimH = 1, so μH[d] = ⊤ by monotonicity
    let e₁ : R3 := EuclideanSpace.single (0 : Fin 3) 1
    obtain ⟨x, hx⟩ := hK e₁ (by simp [e₁, EuclideanSpace.norm_single])
    have := dimH_segmentAlong_unit x e₁ (by simp [e₁, EuclideanSpace.norm_single])
    exact top_unique (hausdorffMeasure_of_lt_dimH (this ▸ hd1) ▸ measure_mono hx)
  · -- 1 ≤ d < 3: the hard analytic core (Wang–Zahl 2025)
    sorry

/-- The three-dimensional Kakeya theorem: every Kakeya set in `R^3` has Hausdorff dimension `3`. -/
theorem MainTheorem :
    ∀ K : Set R3, IsKakeyaSet K → dimH K = (3 : ENNReal) := by
  intro K hK
  apply le_antisymm
  · calc dimH K ≤ dimH (Set.univ : Set R3) := dimH_mono (subset_univ _)
      _ = ↑(Module.finrank ℝ R3) := Real.dimH_univ_eq_finrank R3
      _ = 3 := by simp
  · apply le_of_forall_lt
    intro c hc
    obtain ⟨e, hce, he3⟩ := exists_between hc
    have he_ne : e ≠ ⊤ := ne_top_of_lt he3
    have he3' : (e.toNNReal : ENNReal) < 3 := by rwa [ENNReal.coe_toNNReal he_ne]
    exact lt_of_lt_of_le hce
      ((ENNReal.coe_toNNReal he_ne).symm ▸
        le_dimH_of_hausdorffMeasure_eq_top (kakeya_hausdorffMeasure_eq_top K hK e.toNNReal he3'))

end KakeyaTheorem3D
