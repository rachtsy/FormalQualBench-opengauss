import Mathlib

namespace ColorfulCaratheodoryTheorem

noncomputable section

open Finset BigOperators Set
open scoped InnerProductSpace

variable {d : ℕ}

/-- If 0 ∈ convexHull ℝ S and v ≠ 0, then some point in S has ⟪v, ·⟫ ≤ 0. -/
lemma exists_inner_nonpos {S : Set (EuclideanSpace ℝ (Fin d))}
    (hS : (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ S)
    {v : EuclideanSpace ℝ (Fin d)} (hv : v ≠ 0) :
    ∃ s ∈ S, ⟪v, s⟫_ℝ ≤ 0 := by
  by_contra hall
  push_neg at hall
  obtain ⟨ι, _, w, z, hw_nn, hw_sum, hz_mem, hz_eq⟩ := mem_convexHull_iff_exists_fintype.mp hS
  have hzpos : ∀ i, 0 < ⟪v, z i⟫_ℝ := fun i => hall _ (hz_mem i)
  have ⟨i₀, hi₀⟩ : ∃ i : ι, 0 < w i := by
    by_contra h; push_neg at h
    have : ∀ i, w i = 0 := fun i => le_antisymm (h i) (hw_nn i)
    simp [this] at hw_sum
  have h0 : (0 : ℝ) = ∑ i, w i * ⟪v, z i⟫_ℝ := by
    have h1 : ⟪v, ∑ i, w i • z i⟫_ℝ = ∑ i, w i * ⟪v, z i⟫_ℝ := by
      simp only [← innerSL_apply_apply (𝕜 := ℝ)]
      rw [map_sum]
      simp only [innerSL_apply_apply, inner_smul_right]
    rw [show (0 : ℝ) = ⟪v, (0 : EuclideanSpace ℝ (Fin d))⟫_ℝ from (inner_zero_right v).symm,
        ← hz_eq, h1]
  have hpos : 0 < ∑ i, w i * ⟪v, z i⟫_ℝ := by
    have : (∑ _ : ι, (0 : ℝ)) < ∑ i, w i * ⟪v, z i⟫_ℝ :=
      Finset.sum_lt_sum (fun i _ => mul_nonneg (hw_nn i) (le_of_lt (hzpos i)))
        ⟨i₀, mem_univ i₀, mul_pos hi₀ (hzpos i₀)⟩
    simpa using this
  linarith

/-- d + 1 points in ℝ^d with z ≠ 0, z = ∑ αᵢ pᵢ, and ⟪z, pᵢ⟫ ≥ ‖z‖² ∀ i:
    z has an alternative convex representation with some coefficient zero.
    (Uses: d+1 points on a hyperplane in ℝ^d are affinely dependent.) -/
lemma exists_zero_coeff
    (p : Fin (d + 1) → EuclideanSpace ℝ (Fin d))
    (z : EuclideanSpace ℝ (Fin d)) (hz : z ≠ 0)
    (α : Fin (d + 1) → ℝ) (hα_nn : ∀ i, 0 ≤ α i)
    (hα_sum : ∑ i, α i = 1) (hα_eq : ∑ i, α i • p i = z)
    (hinner : ∀ i, ⟪z, p i⟫_ℝ ≥ ‖z‖ ^ 2) :
    ∃ j : Fin (d + 1), ∃ β : Fin (d + 1) → ℝ,
      (∀ i, 0 ≤ β i) ∧ ∑ i, β i = 1 ∧ ∑ i, β i • p i = z ∧ β j = 0 := by
  -- Case 1: Some αⱼ is already zero
  by_cases hα_zero : ∃ j, α j = 0
  · obtain ⟨j, hj⟩ := hα_zero
    exact ⟨j, α, hα_nn, hα_sum, hα_eq, hj⟩
  -- All αᵢ are positive
  push_neg at hα_zero
  have hα_pos : ∀ i, 0 < α i :=
    fun i => lt_of_le_of_ne (hα_nn i) (Ne.symm (hα_zero i))
  -- Handle d = 0 (vacuous: EuclideanSpace ℝ (Fin 0) is trivial)
  rcases Nat.eq_zero_or_pos d with rfl | hd_pos
  · exact absurd (Subsingleton.elim z 0) hz
  -- d ≥ 1 from now on
  -- Step 1: All inner products equal ‖z‖²
  have hinner_eq : ∀ i, ⟪z, p i⟫_ℝ = ‖z‖ ^ 2 := by
    have h_sum_eq : ∑ i, α i * ⟪z, p i⟫_ℝ = ‖z‖ ^ 2 := by
      have h1 : ⟪z, ∑ i, α i • p i⟫_ℝ = ∑ i, α i * ⟪z, p i⟫_ℝ := by
        rw [inner_sum]; congr 1; ext i; rw [real_inner_smul_right]
      rw [hα_eq, real_inner_self_eq_norm_sq] at h1; linarith
    have h_sum_eq' : ∑ i, α i * ‖z‖ ^ 2 = ‖z‖ ^ 2 := by
      rw [← Finset.sum_mul, hα_sum, one_mul]
    have hterms_nn : 0 ≤ fun i => α i * (⟪z, p i⟫_ℝ - ‖z‖ ^ 2) :=
      fun i => mul_nonneg (hα_nn i) (sub_nonneg.mpr (hinner i))
    have hterms_sum : ∑ i, α i * (⟪z, p i⟫_ℝ - ‖z‖ ^ 2) = 0 := by
      simp_rw [mul_sub]; rw [Finset.sum_sub_distrib]; linarith
    have hterms_zero :=
      (Fintype.sum_eq_zero_iff_of_nonneg hterms_nn).mp hterms_sum
    intro i
    have h := congr_fun hterms_zero i
    change α i * (⟪z, p i⟫_ℝ - ‖z‖ ^ 2) = 0 at h
    rcases mul_eq_zero.mp h with h | h
    · linarith [hα_pos i]
    · linarith
  -- Step 2: Points are not affinely independent
  have hnotai : ¬ AffineIndependent ℝ p := by
    have hcard : Fintype.card (Fin (d + 1)) = (d - 1) + 2 := by
      rw [Fintype.card_fin]; omega
    rw [← finrank_vectorSpan_le_iff_not_affineIndependent ℝ p hcard]
    set f := (innerSL ℝ z).toLinearMap with hf_def
    have hf_ne : f ≠ 0 := by
      intro hf; apply hz
      have : f z = 0 := by rw [hf]; simp
      change (innerSL ℝ z) z = 0 at this
      rw [innerSL_apply_apply] at this
      exact inner_self_eq_zero.mp this
    have hker_finrank : Module.finrank ℝ (LinearMap.ker f) = d - 1 := by
      have := Module.Dual.finrank_ker_add_one_of_ne_zero hf_ne
      rw [finrank_euclideanSpace_fin] at this; omega
    have hvs_le : vectorSpan ℝ (Set.range p) ≤ LinearMap.ker f := by
      rw [vectorSpan_range_eq_span_range_vsub_right ℝ p 0, Submodule.span_le]
      rintro v ⟨i, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker]
      change (innerSL ℝ z) (p i -ᵥ p 0) = 0
      simp only [vsub_eq_sub, map_sub, innerSL_apply_apply, hinner_eq, sub_self]
    calc Module.finrank ℝ (vectorSpan ℝ (Set.range p))
        ≤ Module.finrank ℝ (LinearMap.ker f) := Submodule.finrank_mono hvs_le
      _ = d - 1 := hker_finrank
  -- Step 3: Extract dependence relation
  rw [affineIndependent_iff_of_fintype] at hnotai
  push_neg at hnotai
  obtain ⟨w, hw_sum, hw_vsub, j₀, hj₀⟩ := hnotai
  have hw_eq : ∑ i, w i • p i = 0 := by
    have := Finset.weightedVSub_eq_linear_combination Finset.univ hw_sum (p := p)
    rw [← this]; exact hw_vsub
  -- There exists some index with w > 0
  have hw_pos : ∃ i, 0 < w i := by
    by_contra h; push_neg at h
    have : w j₀ < 0 := lt_of_le_of_ne (h j₀) hj₀
    have : ∑ i, w i < 0 := by
      calc ∑ i, w i
          = w j₀ + ∑ i ∈ Finset.univ.erase j₀, w i := by
            rw [Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
        _ ≤ w j₀ + 0 := by
            gcongr; exact Finset.sum_nonpos (fun k _ => h k)
        _ < 0 := by linarith
    linarith
  -- Step 4: Find minimizing index and construct β
  set S := Finset.univ.filter (fun i => 0 < w i) with hS_def
  have hS_ne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hw_pos
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨j, hjS, hj_min⟩ :=
    S.exists_min_image (fun i => α i / w i) hS_ne
  have hjw_pos : 0 < w j := (Finset.mem_filter.mp hjS).2
  set t := -(α j / w j) with ht_def
  set β := fun i => α i + t * w i with hβ_def
  refine ⟨j, β, ?_, ?_, ?_, ?_⟩
  · -- ∀ i, 0 ≤ β i
    intro i
    simp only [hβ_def, ht_def]
    by_cases hiS : i ∈ S
    · have hi_pos : 0 < w i := (Finset.mem_filter.mp hiS).2
      have hmin := hj_min i hiS
      rw [div_le_div_iff₀ hjw_pos hi_pos] at hmin
      have : α j / w j * w i ≤ α i := by
        rwa [div_mul_eq_mul_div, div_le_iff₀ hjw_pos]
      linarith
    · simp only [hS_def, Finset.mem_filter, Finset.mem_univ,
        true_and, not_lt] at hiS
      have h1 : α j / w j * w i ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos
          (le_of_lt (div_pos (hα_pos j) hjw_pos)) hiS
      linarith [hα_pos i]
  · -- ∑ β = 1
    simp_rw [hβ_def, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hα_sum, hw_sum, mul_zero, add_zero]
  · -- ∑ β_i • p_i = z
    simp_rw [hβ_def, add_smul, mul_smul]
    rw [Finset.sum_add_distrib, hα_eq, ← Finset.smul_sum, hw_eq,
      smul_zero, add_zero]
  · -- β j = 0
    simp only [hβ_def, ht_def]
    field_simp; ring

lemma norm_sq_convex_comb (z c : EuclideanSpace ℝ (Fin d)) (ε : ℝ) :
    ‖(1 - ε) • z + ε • c‖ ^ 2 =
    (1 - ε) ^ 2 * ‖z‖ ^ 2 + 2 * ε * (1 - ε) * ⟪z, c⟫_ℝ + ε ^ 2 * ‖c‖ ^ 2 := by
  rw [← @real_inner_self_eq_norm_sq (EuclideanSpace ℝ (Fin d)) _ _ ((1 - ε) • z + ε • c)]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm c z, RCLike.conj_to_real]
  ring

lemma alg_identity (A B C D : ℝ) (hD : D ≠ 0) :
    let ε := (A - B) / (2 * D)
    (1 - ε) ^ 2 * A + 2 * ε * (1 - ε) * B + ε ^ 2 * C - A =
    -(3 * (A - B) ^ 2 / (4 * D)) +
      (A - 2 * B + C - D) * (A - B) ^ 2 / (4 * D ^ 2) := by
  simp only; field_simp; ring

lemma norm_convex_lt (z c : EuclideanSpace ℝ (Fin d))
    (hz : z ≠ 0) (hc : ⟪z, c⟫_ℝ ≤ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ‖(1 - ε) • z + ε • c‖ ^ 2 < ‖z‖ ^ 2 := by
  have hzn2 : 0 < ‖z‖ ^ 2 := by positivity
  have hzc : z ≠ c := by intro h; subst h; nlinarith [real_inner_self_eq_norm_sq z]
  have hzc_norm : (0 : ℝ) < ‖z - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzc)
  have hD : 0 < ‖z - c‖ ^ 2 := by positivity
  have hD_ne : ‖z - c‖ ^ 2 ≠ 0 := ne_of_gt hD
  have ha : 0 < ‖z‖ ^ 2 - ⟪z, c⟫_ℝ := by linarith
  have hD_exp : ‖z - c‖ ^ 2 = ‖z‖ ^ 2 - 2 * ⟪z, c⟫_ℝ + ‖c‖ ^ 2 := norm_sub_sq_real z c
  use (‖z‖ ^ 2 - ⟪z, c⟫_ℝ) / (2 * ‖z - c‖ ^ 2)
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_lt_one (by positivity : (0 : ℝ) < 2 * ‖z - c‖ ^ 2)]
    nlinarith [sq_nonneg (‖c‖)]
  · rw [norm_sq_convex_comb]
    have key := alg_identity (‖z‖ ^ 2) (⟪z, c⟫_ℝ) (‖c‖ ^ 2) (‖z - c‖ ^ 2) hD_ne
    simp only at key
    have hcancel : ‖z‖ ^ 2 - 2 * ⟪z, c⟫_ℝ + ‖c‖ ^ 2 - ‖z - c‖ ^ 2 = 0 := by linarith
    have h2 : (‖z‖ ^ 2 - 2 * ⟪z, c⟫_ℝ + ‖c‖ ^ 2 - ‖z - c‖ ^ 2) *
        (‖z‖ ^ 2 - ⟪z, c⟫_ℝ) ^ 2 / (4 * (‖z - c‖ ^ 2) ^ 2) = 0 := by
      rw [hcancel, zero_mul, zero_div]
    have h3 : 0 < 3 * (‖z‖ ^ 2 - ⟪z, c⟫_ℝ) ^ 2 / (4 * ‖z - c‖ ^ 2) := by positivity
    linarith

/-- The colorful Carathéodory theorem (statement): if each of `d+1` sets of points in `ℝ^d`
contains the origin in its convex hull, then one can pick one point from each set so that the
origin lies in the convex hull of the chosen points. -/
theorem MainTheorem (d : ℕ)
    (C : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)))
    (hC : ∀ i, (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (C i)) :
    ∃ p : Fin (d + 1) → EuclideanSpace ℝ (Fin d),
      (∀ i, p i ∈ C i) ∧ (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (Set.range p) := by
  -- Step 1: Extract finite witnesses using Carathéodory's theorem
  have hFin : ∀ i, ∃ (F : Finset (EuclideanSpace ℝ (Fin d))),
      F.Nonempty ∧ (↑F : Set _) ⊆ C i ∧
      (0 : EuclideanSpace ℝ (Fin d)) ∈ convexHull ℝ (↑F : Set _) := by
    intro i
    exact ⟨Caratheodory.minCardFinsetOfMemConvexHull (hC i),
      Caratheodory.minCardFinsetOfMemConvexHull_nonempty (hC i),
      Caratheodory.minCardFinsetOfMemConvexHull_subseteq (hC i),
      Caratheodory.mem_minCardFinsetOfMemConvexHull (hC i)⟩
  choose F hF_ne hF_sub hF_conv using hFin
  -- Step 2: Suffices to find tuple from F
  suffices ∃ p : Fin (d + 1) → EuclideanSpace ℝ (Fin d),
      (∀ i, p i ∈ (F i : Set _)) ∧ (0 : _) ∈ convexHull ℝ (Set.range p) by
    obtain ⟨p, hp, h0⟩ := this; exact ⟨p, fun i => hF_sub i (hp i), h0⟩
  -- Step 3: By contradiction
  by_contra h_bad; push_neg at h_bad
  -- Step 4: Finite type setup
  haveI : ∀ i, Fintype ↥(F i : Set (EuclideanSpace ℝ (Fin d))) :=
    fun i => (F i).fintypeCoeSort
  haveI : ∀ i, Nonempty ↥(F i : Set (EuclideanSpace ℝ (Fin d))) :=
    fun i => Set.Nonempty.to_subtype (Finset.coe_nonempty.mpr (hF_ne i))
  let val : (∀ i, ↥(F i : Set (EuclideanSpace ℝ (Fin d)))) →
      Fin (d + 1) → EuclideanSpace ℝ (Fin d) := fun t i => (t i).val
  -- Step 5: Minimize infDist over all colorful tuples
  let D := fun t => Metric.infDist 0 (convexHull ℝ (Set.range (val t)))
  obtain ⟨t₀, ht₀⟩ := Finite.exists_min D
  -- Step 6: Properties of the optimal tuple
  set K := convexHull ℝ (Set.range (val t₀)) with hK_def
  have hK_ne : K.Nonempty := ⟨val t₀ 0, subset_convexHull _ _ ⟨0, rfl⟩⟩
  have hK_compact : IsCompact K := (Set.finite_range _).isCompact_convexHull
  have hK_cvx : Convex ℝ K := convex_convexHull ℝ _
  have h0K : (0 : EuclideanSpace ℝ (Fin d)) ∉ K := h_bad _ (fun i => (t₀ i).prop)
  -- Step 7: Closest point z and inner product characterization
  obtain ⟨z, hz_mem, hz_norm⟩ := exists_norm_eq_iInf_of_complete_convex hK_ne
    hK_compact.isClosed.isComplete hK_cvx 0
  have hz_ne : z ≠ 0 := fun h => h0K (h ▸ hz_mem)
  have hDt₀ : D t₀ = ‖z‖ := by
    show Metric.infDist 0 K = ‖z‖
    rw [Metric.infDist_eq_iInf]
    simp_rw [dist_eq_norm]
    rw [show ‖z‖ = ‖(0 : EuclideanSpace ℝ (Fin d)) - z‖ by rw [zero_sub, norm_neg]]
    exact hz_norm.symm
  have hz_inner : ∀ w ∈ K, ⟪z, w⟫_ℝ ≥ ‖z‖ ^ 2 := by
    intro w hw
    have h1 := ((norm_eq_iInf_iff_real_inner_le_zero hK_cvx hz_mem).mp hz_norm) w hw
    rw [zero_sub, inner_neg_left] at h1
    have h2 : ⟪z, w - z⟫_ℝ = ⟪z, w⟫_ℝ - ⟪z, z⟫_ℝ := by rw [inner_sub_right]
    have h3 : ⟪z, z⟫_ℝ = ‖z‖ ^ 2 := real_inner_self_eq_norm_sq z
    linarith
  -- Step 8: Extract convex combination of z
  have hz_comb : z ∈ convexHull ℝ (Set.range (val t₀)) := hK_def ▸ hz_mem
  rw [convexHull_range_eq_exists_affineCombination] at hz_comb
  obtain ⟨s, w, hw_nn, hw_sum, hw_eq⟩ := hz_comb
  set α : Fin (d + 1) → ℝ := fun i => if i ∈ s then w i else 0 with hα_def
  have hα_nn : ∀ i, 0 ≤ α i := by
    intro i; simp only [hα_def]; split_ifs with h; exact hw_nn i h; exact le_refl 0
  have hα_sum : ∑ i, α i = 1 := by
    simp only [hα_def, Finset.sum_ite_mem, Finset.univ_inter]; exact hw_sum
  have hα_eq : ∑ i, α i • val t₀ i = z := by
    simp only [hα_def, ite_smul, zero_smul, Finset.sum_ite_mem, Finset.univ_inter]
    rwa [Finset.affineCombination_eq_linear_combination _ _ _ hw_sum] at hw_eq
  -- Step 9: Apply exists_zero_coeff
  obtain ⟨j, β, hβ_nn, hβ_sum, hβ_eq, hβ_zero⟩ :=
    exists_zero_coeff (val t₀) z hz_ne α hα_nn hα_sum hα_eq
      (fun i => hz_inner _ (subset_convexHull _ _ ⟨i, rfl⟩))
  -- Step 10: Find replacement c from F_j with ⟪z, c⟫ ≤ 0
  obtain ⟨c, hc_mem, hc_inner⟩ := exists_inner_nonpos (hF_conv j) hz_ne
  -- Step 11: Exchange argument — define new tuple t'
  let t' : ∀ i, ↥(F i : Set (EuclideanSpace ℝ (Fin d))) :=
    fun i => if h : i = j then h ▸ ⟨c, hc_mem⟩ else t₀ i
  -- z ∈ conv(range(val t')) since β_j = 0
  have hz_in_K' : z ∈ convexHull ℝ (Set.range (val t')) := by
    have h_sum_eq : ∑ i, β i • (val t') i = z := by
      have h_eq : ∀ i, β i • (val t') i = β i • val t₀ i := by
        intro i; by_cases h : i = j
        · subst h; simp [val, t', hβ_zero]
        · congr 1; show (t' i).val = (t₀ i).val; simp [t', dif_neg h]
      simp_rw [h_eq]; exact hβ_eq
    rw [← h_sum_eq]
    have h := affineCombination_mem_convexHull (s := Finset.univ) (v := val t') (w := β)
      (fun i _ => hβ_nn i) (by simpa using hβ_sum)
    rwa [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hβ_sum)] at h
  -- c ∈ conv(range(val t'))
  have hc_in_K' : c ∈ convexHull ℝ (Set.range (val t')) :=
    subset_convexHull _ _ ⟨j, by simp [val, t']⟩
  -- Step 12: Use norm_convex_lt to find ε with ‖(1-ε)z + εc‖² < ‖z‖²
  obtain ⟨ε, hε_pos, hε_lt, hε_sq⟩ := norm_convex_lt z c hz_ne hc_inner
  -- (1-ε)z + εc ∈ conv(range(val t')) by convexity
  have hpt_mem : (1 - ε) • z + ε • c ∈ convexHull ℝ (Set.range (val t')) :=
    (convex_convexHull ℝ _) hz_in_K' hc_in_K' (by linarith) (le_of_lt hε_pos)
      (by linarith)
  -- Step 13: Contradiction — D(t') < D(t₀) contradicts minimality
  have hDt'_le : D t' ≤ ‖(1 - ε) • z + ε • c‖ :=
    (Metric.infDist_le_dist_of_mem hpt_mem).trans (by rw [dist_zero_left])
  have hnorm_lt : ‖(1 - ε) • z + ε • c‖ < ‖z‖ := by
    by_contra h; push_neg at h
    have := pow_le_pow_left₀ (norm_nonneg z) h 2
    linarith
  exact absurd (show D t' < D t₀ by linarith) (not_lt.mpr (ht₀ t'))

end

end ColorfulCaratheodoryTheorem
