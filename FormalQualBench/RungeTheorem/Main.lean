import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.Basic

namespace RungeTheorem

open scoped Topology
open Complex Polynomial Finset Filter MeasureTheory

private lemma pole_approx_far {R : ℝ} (hR : 0 ≤ R) {a : ℂ} (ha : R < ‖a‖) :
    ∀ ε > 0, ∃ p : Polynomial ℂ,
      ∀ z : ℂ, ‖z‖ ≤ R → ‖Polynomial.eval z p - (a - z)⁻¹‖ < ε := by
  intro ε hε
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha; linarith
  have ha_pos : (0 : ℝ) < ‖a‖ := by linarith
  have hdiff : (0 : ℝ) < ‖a‖ - R := by linarith
  have hr_lt : R / ‖a‖ < 1 := by rwa [div_lt_one ha_pos]
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (mul_pos hε hdiff) hr_lt
  refine ⟨C a⁻¹ * ∑ i ∈ range N, (C a⁻¹ * X) ^ i, fun z hz => ?_⟩
  simp only [eval_mul, eval_C, eval_finset_sum, eval_pow, eval_X]
  set w := z * a⁻¹
  simp_rw [show a⁻¹ * z = w from by ring]
  have haz : (a - z)⁻¹ = a⁻¹ * (1 - w)⁻¹ := by
    have : a - z = a * (1 - w) := by
      simp only [w, mul_sub, mul_one, mul_comm z, ← mul_assoc,
        mul_inv_cancel₀ ha0, one_mul]
    rw [this, mul_inv, mul_comm]
  rw [haz, ← mul_sub, norm_mul, norm_inv]
  have hw_bound : ‖w‖ ≤ R / ‖a‖ := by
    simp only [w, norm_mul, norm_inv]
    exact div_le_div_of_nonneg_right hz ha_pos.le
  have hw_lt_one : ‖w‖ < 1 := hw_bound.trans_lt hr_lt
  have hw1 : w ≠ 1 := by intro h; simp [h] at hw_lt_one
  have hkey : ∑ k ∈ range N, w ^ k - (1 - w)⁻¹ =
      -(w ^ N * (1 - w)⁻¹) := by
    rw [geom_sum_eq hw1 N, div_eq_mul_inv, ← neg_sub w 1, inv_neg]; ring
  rw [hkey, norm_neg, norm_mul, norm_inv, norm_pow]
  have h1w_pos : (0 : ℝ) < ‖(1 : ℂ) - w‖ := by
    rw [norm_pos_iff]; exact sub_ne_zero.mpr (Ne.symm hw1)
  have h1r_pos : (0 : ℝ) < 1 - R / ‖a‖ := by linarith
  have h1w_bound : 1 - R / ‖a‖ ≤ ‖(1 : ℂ) - w‖ := by
    have h1 : ‖(1 : ℂ)‖ = 1 := norm_one
    linarith [norm_sub_norm_le (1 : ℂ) w, hw_bound]
  calc ‖a‖⁻¹ * (‖w‖ ^ N * ‖(1 : ℂ) - w‖⁻¹)
      ≤ ‖a‖⁻¹ * ((R / ‖a‖) ^ N * (1 - R / ‖a‖)⁻¹) := by gcongr
      _ = (R / ‖a‖) ^ N / (‖a‖ - R) := by
          have : ‖a‖ ≠ 0 := ha_pos.ne'
          have : ‖a‖ - R ≠ 0 := hdiff.ne'
          field_simp
      _ < ε := by rw [div_lt_iff₀ hdiff]; linarith

/-- **Pole pushing**: If `Kᶜ` is connected and `a ∉ K`, then `z ↦ (a - z)⁻¹` can be uniformly
approximated by polynomials on `K`. Uses connectedness to "move" the pole to infinity, then
applies `pole_approx_far`. -/
private lemma pole_push {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected Kᶜ)
    {a : ℂ} (ha : a ∉ K) :
    ∀ ε > 0, ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖Polynomial.eval z p - (a - z)⁻¹‖ < ε := by
  sorry

/-- **Runge's theorem**: A holomorphic function on an open set can be uniformly approximated on a
compact subset (with connected complement) by polynomials. -/
theorem MainTheorem {U K : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hKc : IsConnected (Kᶜ)) (hf : DifferentiableOn ℂ f U) :
    ∀ ε > 0, ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖Polynomial.eval z p - f z‖ < ε := by
  sorry

end RungeTheorem
