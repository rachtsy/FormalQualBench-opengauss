import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Topology.Sequences

namespace SchauderFixedPointTheorem

open scoped Topology
open Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Schauder fixed point theorem (statement)**: a continuous self-map of a nonempty compact
convex subset of a Banach space has a fixed point. -/
theorem MainTheorem {s : Set E} (hs_nonempty : s.Nonempty) (hs_compact : IsCompact s)
    (hs_convex : Convex ℝ s) {f : E → E} (hf_cont : ContinuousOn f s)
    (hf_maps : Set.MapsTo f s s) :
    ∃ x ∈ s, f x = x := by
  have h_approx : ∀ n : ℕ, ∃ x ∈ s, ‖x - f x‖ ≤ 1 / (↑n + 1) := by
    sorry
  choose x hx_mem hx_bound using h_approx
  obtain ⟨y, hy_mem, φ, hφ_mono, hφ_tendsto⟩ := hs_compact.tendsto_subseq hx_mem
  refine ⟨y, hy_mem, ?_⟩
  have hdiff_zero : Tendsto (fun n => x (φ n) - f (x (φ n))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => hx_bound (φ n))
    have h1 : Tendsto (fun n => (↑(φ n) : ℝ) + 1) atTop atTop := by
      apply Filter.Tendsto.atTop_add _ tendsto_const_nhds
      exact tendsto_natCast_atTop_atTop.comp hφ_mono.tendsto_atTop
    exact tendsto_const_nhds.div_atTop h1
  have hfconv' : Tendsto (f ∘ x ∘ φ) atTop (𝓝 y) := by
    have h3 := hφ_tendsto.sub hdiff_zero
    simp only [sub_zero] at h3
    convert h3 using 1
    ext n; simp [Function.comp, sub_sub_cancel]
  have hxφ_within : Tendsto (x ∘ φ) atTop (nhdsWithin y s) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hφ_tendsto
      (Filter.Eventually.of_forall fun n => hx_mem (φ n))
  exact tendsto_nhds_unique
    ((hf_cont.continuousWithinAt hy_mem).tendsto.comp hxφ_within) hfconv'

end SchauderFixedPointTheorem
