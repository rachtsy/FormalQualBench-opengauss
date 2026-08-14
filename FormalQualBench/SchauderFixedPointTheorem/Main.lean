import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.Set.Operations
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Sequences

namespace SchauderFixedPointTheorem

open scoped Topology
open Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ### Bump function helpers for the Schauder projection -/

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The bump function `x ↦ max(0, ε − ‖x − y‖)` is continuous. -/
lemma bump_continuous (y : E) (ε : ℝ) :
    Continuous (fun x : E => max (0 : ℝ) (ε - ‖x - y‖)) :=
  continuous_const.max
    (continuous_const.sub (continuous_norm.comp (continuous_id.sub continuous_const)))

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The sum of bump functions `∑ max(0, ε − ‖x − yᵢ‖)` is positive when `x` is covered
by at least one `ε`-ball centered at a point in `F`. -/
lemma sum_bump_pos (F : Finset E) (ε : ℝ) (x : E)
    (hcover : x ∈ ⋃ y ∈ (F : Set E), Metric.ball y ε) :
    0 < ∑ y ∈ F, max (0 : ℝ) (ε - ‖x - y‖) := by
  rw [Set.mem_iUnion₂] at hcover
  obtain ⟨y, hy_mem, hy_ball⟩ := hcover
  apply Finset.sum_pos'
  · intro i _; exact le_max_left 0 _
  · exact ⟨y, hy_mem, lt_max_of_lt_right (by
      rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hy_ball
      linarith [norm_sub_rev x y])⟩

omit [CompleteSpace E] in
/-- The center of mass with bump weights approximates `x` to within `ε`:
the center of mass is a convex combination of centers `yᵢ` with `‖x − yᵢ‖ < ε`,
hence lies in the convex (and thus open) ball `B(x, ε)`. -/
lemma centerMass_approx (F : Finset E) (x : E) (ε : ℝ)
    (hW : 0 < ∑ y ∈ F, max (0 : ℝ) (ε - ‖x - y‖)) :
    ‖F.centerMass (fun y => max (0 : ℝ) (ε - ‖x - y‖)) id - x‖ < ε := by
  set w : E → ℝ := fun y => max (0 : ℝ) (ε - ‖x - y‖)
  let F' := F.filter (fun y => 0 < w y)
  have hF'_sub : F' ⊆ F := Finset.filter_subset _ _
  have h_zero : ∀ i ∈ F, i ∉ F' → w i = 0 := by
    intro i hi hi'
    simp only [F', Finset.mem_filter, not_and, not_lt] at hi'
    exact le_antisymm (hi' hi) (le_max_left 0 _)
  rw [← Finset.centerMass_subset id hF'_sub h_zero]
  have hW' : 0 < ∑ y ∈ F', w y := by rwa [Finset.sum_subset hF'_sub h_zero]
  have h_ball : ∀ i ∈ F', id i ∈ Metric.ball x ε := by
    intro i hi
    simp only [F', Finset.mem_filter] at hi
    simp only [id, Metric.mem_ball, dist_comm, dist_eq_norm]
    have h1 : 0 < ε - ‖x - i‖ := by
      have := hi.2; simp only [w, max_def] at this
      split_ifs at this with h <;> linarith
    linarith
  have h_in_ball : F'.centerMass w id ∈ Metric.ball x ε :=
    (convex_ball x ε).centerMass_mem (fun i _ => le_max_left 0 _) hW' h_ball
  simp only [Metric.mem_ball, dist_comm, dist_eq_norm] at h_in_ball
  rwa [norm_sub_rev]

/-! ### Schauder projection -/

omit [CompleteSpace E] in
/-- **Schauder projection**: given a compact set `s` and `ε > 0`, there exists a finite set
`F ⊆ s` and a continuous projection `p : s → convexHull ℝ F` approximating the identity
within `ε`. The map `p` is defined as the center of mass with bump-function weights
`max(0, ε − ‖x − yᵢ‖)`. -/
theorem schauder_projection_exists
    {s : Set E} (hs_compact : IsCompact s) (hs_nonempty : s.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : Finset E) (p : E → E),
      ↑F ⊆ s ∧
      (↑F : Set E).Nonempty ∧
      ContinuousOn p s ∧
      Set.MapsTo p s (convexHull ℝ (↑F : Set E)) ∧
      ∀ x ∈ s, ‖p x - x‖ < ε := by
  obtain ⟨t, ht_sub, ht_fin, ht_cover⟩ := hs_compact.finite_cover_balls hε
  set F := ht_fin.toFinset
  have hF_coe : (F : Set E) = t := ht_fin.coe_toFinset
  have hF_sub : ↑F ⊆ s := hF_coe ▸ ht_sub
  have hcover : s ⊆ ⋃ y ∈ (F : Set E), Metric.ball y ε := hF_coe ▸ ht_cover
  have hF_ne : (↑F : Set E).Nonempty := by
    obtain ⟨x, hx⟩ := hs_nonempty
    have hx_cover := hcover hx
    rw [Set.mem_iUnion₂] at hx_cover
    obtain ⟨y, hy_mem, _⟩ := hx_cover
    exact ⟨y, hy_mem⟩
  let p : E → E := fun x => F.centerMass (fun y => max (0 : ℝ) (ε - ‖x - y‖)) id
  refine ⟨F, p, hF_sub, hF_ne, ?_, ?_, ?_⟩
  · -- ContinuousOn: centerMass is (∑ wᵢ)⁻¹ • ∑ wᵢ • yᵢ, both parts continuous
    change ContinuousOn (fun x => F.centerMass (fun y => max 0 (ε - ‖x - y‖)) id) s
    simp only [Finset.centerMass, id]
    apply ContinuousOn.smul
    · apply ContinuousOn.inv₀
      · exact (continuous_finset_sum F fun y _ => bump_continuous y ε).continuousOn
      · intro x hx; exact ne_of_gt (sum_bump_pos F ε x (hcover hx))
    · exact (continuous_finset_sum F fun y _ =>
        (bump_continuous y ε).smul continuous_const).continuousOn
  · -- MapsTo: centerMass lies in convexHull F
    intro x hx
    exact Finset.centerMass_mem_convexHull F (fun i _ => le_max_left 0 _)
      (sum_bump_pos F ε x (hcover hx)) (fun i hi => hi)
  · -- Approximation: ‖p(x) - x‖ < ε
    intro x hx
    exact centerMass_approx F x ε (sum_bump_pos F ε x (hcover hx))

/-! ### Brouwer fixed point theorem (sorry) -/

/-- **Brouwer fixed point theorem** for convex hulls of finite sets in normed spaces.
The convex hull of a finite set is compact (`Set.Finite.isCompact_convexHull`), convex
(`convex_convexHull`), nonempty, and finite-dimensional (contained in the span of finitely
many vectors). Thus any continuous self-map has a fixed point by the Brouwer FPT.

This result is not currently in Mathlib; a proof requires algebraic topology
(e.g., degree theory, the no-retraction theorem, or simplicial approximation). -/
theorem brouwer_fixed_point_convexHull_finite
    {F : Finset E} (hF : (F : Set E).Nonempty)
    {g : E → E} (hg_cont : ContinuousOn g (convexHull ℝ (F : Set E)))
    (hg_maps : Set.MapsTo g (convexHull ℝ (F : Set E)) (convexHull ℝ (F : Set E))) :
    ∃ x ∈ convexHull ℝ (F : Set E), g x = x := by
  sorry

/-! ### Main theorem -/

/-- **Schauder fixed point theorem**: a continuous self-map of a nonempty compact
convex subset of a Banach space has a fixed point. -/
theorem MainTheorem {s : Set E} (hs_nonempty : s.Nonempty) (hs_compact : IsCompact s)
    (hs_convex : Convex ℝ s) {f : E → E} (hf_cont : ContinuousOn f s)
    (hf_maps : Set.MapsTo f s s) :
    ∃ x ∈ s, f x = x := by
  have h_approx : ∀ n : ℕ, ∃ x ∈ s, ‖x - f x‖ ≤ 1 / (↑n + 1) := by
    intro n
    have hε : (0 : ℝ) < 1 / (↑n + 1) := by positivity
    obtain ⟨F, p, hF_sub, hF_ne, hp_cont, hp_maps, hp_approx⟩ :=
      schauder_projection_exists hs_compact hs_nonempty hε
    -- The convex hull of F is contained in s (since F ⊆ s and s is convex)
    have hK_sub : convexHull ℝ (↑F : Set E) ⊆ s := convexHull_min hF_sub hs_convex
    -- f maps convexHull F into s
    have hf_maps' : Set.MapsTo f (convexHull ℝ (↑F : Set E)) s :=
      hf_maps.mono hK_sub (fun _ h => h)
    -- p ∘ f maps convexHull F into convexHull F
    have hpf_maps :
        Set.MapsTo (p ∘ f) (convexHull ℝ (↑F : Set E)) (convexHull ℝ (↑F : Set E)) :=
      hp_maps.comp hf_maps'
    -- p ∘ f is continuous on convexHull F
    have hpf_cont : ContinuousOn (p ∘ f) (convexHull ℝ (↑F : Set E)) :=
      hp_cont.comp (hf_cont.mono hK_sub) hf_maps'
    -- By Brouwer FPT, p ∘ f has a fixed point z in convexHull F
    obtain ⟨z, hz_mem, hz_fp⟩ :=
      brouwer_fixed_point_convexHull_finite hF_ne hpf_cont hpf_maps
    refine ⟨z, hK_sub hz_mem, ?_⟩
    -- z = p(f(z)), so ‖z - f(z)‖ = ‖p(f(z)) - f(z)‖ < ε = 1/(n+1)
    have hz_eq : p (f z) = z := hz_fp
    suffices h : ‖p (f z) - f z‖ ≤ 1 / (↑n + 1) by rwa [hz_eq] at h
    exact le_of_lt (hp_approx (f z) (hf_maps (hK_sub hz_mem)))
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
