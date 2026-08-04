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

-- Helper: ‖a^n - b^n‖ ≤ n * M^(n-1) * ‖a - b‖ where M = max ‖a‖ ‖b‖
private lemma norm_pow_sub_pow_le (a b : ℂ) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ ↑n * (max ‖a‖ ‖b‖) ^ (n - 1) * ‖a - b‖ := by
  rw [← geom_sum₂_mul]
  calc ‖(∑ i ∈ range n, a ^ i * b ^ (n - 1 - i)) * (a - b)‖
      ≤ ‖∑ i ∈ range n, a ^ i * b ^ (n - 1 - i)‖ * ‖a - b‖ := norm_mul_le _ _
    _ ≤ (∑ i ∈ range n, ‖a ^ i * b ^ (n - 1 - i)‖) * ‖a - b‖ := by
        gcongr; exact norm_sum_le _ _
    _ ≤ (∑ _i ∈ range n, (max ‖a‖ ‖b‖) ^ (n - 1)) * ‖a - b‖ := by
        gcongr with i hi
        have hi' : i < n := mem_range.mp hi
        simp only [norm_mul, norm_pow]
        calc ‖a‖ ^ i * ‖b‖ ^ (n - 1 - i)
            ≤ (max ‖a‖ ‖b‖) ^ i * ‖b‖ ^ (n - 1 - i) := by
              gcongr; exact le_max_left _ _
          _ ≤ (max ‖a‖ ‖b‖) ^ i * (max ‖a‖ ‖b‖) ^ (n - 1 - i) := by
              gcongr; exact le_max_right _ _
          _ = (max ‖a‖ ‖b‖) ^ (n - 1) := by rw [← pow_add]; congr 1; omega
    _ = ↑n * (max ‖a‖ ‖b‖) ^ (n - 1) * ‖a - b‖ := by
        rw [sum_const, card_range, nsmul_eq_mul]

-- Helper: pole transfer using geometric series.
-- If (b-·)⁻¹ is poly-approx on K and dist(c,b) < infDist(b,K), then (c-·)⁻¹ is poly-approx on K.
private lemma pole_transfer {K : Set ℂ} (hK : IsCompact K) (hKne : K.Nonempty) {b : ℂ}
    (hb : b ∉ K) (hbapprox : ∀ ε > 0, ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖eval z p - (b - z)⁻¹‖ < ε)
    {c : ℂ} (hcb : dist c b < Metric.infDist b K) :
    ∀ ε > 0, ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖eval z p - (c - z)⁻¹‖ < ε := by
  intro ε hε
  set d := Metric.infDist b K
  have hd : 0 < d := (Metric.infDist_pos_iff_notMem_closure hKne).mp
    (hK.isClosed.closure_eq.symm ▸ hb)
  have hcbn : ‖c - b‖ < d := by rwa [← dist_eq_norm]
  set ρ := ‖c - b‖ / d
  have hρ1 : ρ < 1 := (div_lt_one hd).mpr hcbn
  have hρ0 : 0 ≤ ρ := div_nonneg (norm_nonneg _) hd.le
  have h1ρ : 0 < 1 - ρ := sub_pos.mpr hρ1
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (mul_pos (half_pos hε) (mul_pos hd h1ρ)) hρ1
  set M := 2 * d⁻¹
  have hM0 : 0 < M := by positivity
  let Cf := ∑ k ∈ range N, ((↑(k + 1) : ℝ) * (‖c - b‖ * M) ^ k)
  have hCf0 : 0 ≤ Cf := sum_nonneg fun k _ =>
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (mul_nonneg (norm_nonneg _) hM0.le) _)
  set δ : ℝ := min d⁻¹ (ε / (2 * (Cf + 1)))
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδCf : δ * Cf ≤ ε / 2 :=
    calc δ * Cf ≤ δ * (Cf + 1) := by gcongr; linarith
      _ ≤ ε / (2 * (Cf + 1)) * (Cf + 1) := by gcongr; exact min_le_right _ _
      _ = ε / 2 := by field_simp
  obtain ⟨p, hp⟩ := hbapprox δ hδ0
  refine ⟨p * ∑ k ∈ range N, (C (b - c) * p) ^ k, fun z hz => ?_⟩
  simp only [eval_mul, eval_finset_sum, eval_pow, eval_C]
  set A := eval z p; set B := (b - z)⁻¹; set w := (b - c) * B
  have hdz : d ≤ ‖b - z‖ := dist_eq_norm b z ▸ Metric.infDist_le_dist_of_mem hz
  have hbzn : b - z ≠ 0 := norm_pos_iff.mp (hd.trans_le hdz)
  have hczn : c - z ≠ 0 := by
    intro h; linarith [sub_eq_zero.mp h ▸ Metric.infDist_le_dist_of_mem (x := b) hz, dist_comm b c]
  have hAB : ‖A - B‖ < δ := hp z hz
  have hBb : ‖B‖ ≤ d⁻¹ := by simp only [B, norm_inv]; exact inv_anti₀ hd hdz
  have hMb : max ‖A‖ ‖B‖ ≤ M := by
    apply max_le
    · linarith [norm_le_insert' A B, hAB.trans_le (min_le_left d⁻¹ _)]
    · linarith [inv_nonneg.mpr hd.le]
  have hwρ : ‖w‖ ≤ ρ := by
    simp only [w, B, norm_mul, norm_inv]; rw [norm_sub_rev b c]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hd hdz) (norm_nonneg _)
  have hw1 : ‖w‖ < 1 := hwρ.trans_lt hρ1
  have hwn1 : w ≠ 1 := by intro h; simp [h] at hw1
  rw [show (c - z)⁻¹ = B * (1 - w)⁻¹ from by
        simp only [B, w]
        rw [show c-z = (b-z)*(1-(b-c)*(b-z)⁻¹) from by field_simp; ring, mul_inv, mul_comm],
    show A * ∑ k ∈ range N, ((b-c)*A)^k = ∑ k ∈ range N, (b-c)^k * A^(k+1) from by
        rw [Finset.mul_sum]; congr 1; ext k; rw [mul_pow]; ring,
    show ∑ k ∈ range N, (b-c)^k*A^(k+1) - B*(1-w)⁻¹ =
        (∑ k ∈ range N, (b-c)^k*(A^(k+1)-B^(k+1))) + B*(∑ k ∈ range N, w^k - (1-w)⁻¹) from by
      rw [show ∀ a b c : ℂ, a-c = (a-b)+(b-c) from fun a b c => by ring,
        show ∑ k ∈ range N, (b-c)^k*A^(k+1) - ∑ k ∈ range N, (b-c)^k*B^(k+1) =
          ∑ k ∈ range N, (b-c)^k*(A^(k+1)-B^(k+1)) from by
            rw [← Finset.sum_sub_distrib]; congr 1; ext k; ring]
      congr 1; rw [show ∑ k ∈ range N, (b-c)^k*B^(k+1) = B*∑ k ∈ range N, w^k from by
        simp only [w]; rw [Finset.mul_sum]; congr 1; ext k; rw [mul_pow]; ring, ← mul_sub]]
  calc ‖(∑ k ∈ range N, (b-c)^k*(A^(k+1)-B^(k+1))) + B*(∑ k ∈ range N, w^k-(1-w)⁻¹)‖
      ≤ ‖∑ k ∈ range N, (b-c)^k*(A^(k+1)-B^(k+1))‖ + ‖B*(∑ k ∈ range N, w^k-(1-w)⁻¹)‖ :=
        norm_add_le _ _
    _ ≤ (δ * Cf) + d⁻¹ * (ρ^N / (1-ρ)) := by
        apply add_le_add
        · calc ‖∑ k ∈ range N, (b-c)^k*(A^(k+1)-B^(k+1))‖
              ≤ ∑ k ∈ range N, ‖(b-c)^k*(A^(k+1)-B^(k+1))‖ := norm_sum_le _ _
            _ ≤ ∑ k ∈ range N, (‖b-c‖^k * (↑(k+1) * (max ‖A‖ ‖B‖)^k * ‖A-B‖)) := by
                apply sum_le_sum; intro k _; rw [norm_mul, norm_pow]; gcongr
                exact norm_pow_sub_pow_le A B (k+1)
            _ ≤ ∑ k ∈ range N, (δ * (↑(k+1) * (‖c-b‖ * M) ^ k)) := by
                apply sum_le_sum; intro k _; rw [norm_sub_rev b c]
                calc ‖c-b‖^k * (↑(k+1) * (max ‖A‖ ‖B‖)^k * ‖A-B‖)
                    ≤ ‖c-b‖^k * (↑(k+1) * M^k * δ) := by gcongr
                  _ = δ * (↑(k+1) * (‖c-b‖ * M)^k) := by rw [mul_pow]; ring
            _ = δ * Cf := by rw [← Finset.mul_sum]
        · have hgeom : ∑ k ∈ range N, w^k - (1-w)⁻¹ = -(w^N * (1-w)⁻¹) := by
            rw [geom_sum_eq hwn1 N, div_eq_mul_inv, ← neg_sub w 1, inv_neg]; ring
          rw [hgeom, mul_neg, norm_neg]
          have h1wb : (1-ρ) ≤ ‖(1:ℂ)-w‖ := by
            linarith [norm_sub_norm_le (1:ℂ) w, norm_one (α := ℂ), hwρ]
          calc ‖B * (w^N * (1-w)⁻¹)‖
              = ‖B‖ * (‖w‖^N * ‖(1-w)⁻¹‖) := by rw [norm_mul, norm_mul, norm_pow]
            _ = ‖B‖ * (‖w‖^N * ‖(1:ℂ)-w‖⁻¹) := by rw [norm_inv (1-w)]
            _ ≤ d⁻¹ * (ρ^N * (1-ρ)⁻¹) := by
                apply mul_le_mul hBb _ (by positivity) (by positivity)
                apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hwρ _)
                  (inv_anti₀ h1ρ h1wb) (by positivity) (by positivity)
            _ = d⁻¹ * (ρ^N / (1-ρ)) := by rw [div_eq_mul_inv]
    _ < ε := by
        have hρN : 0 ≤ ρ ^ N := pow_nonneg hρ0 _
        linarith [calc d⁻¹ * (ρ^N / (1-ρ)) < d⁻¹ * (ε/2*(d*(1-ρ)) / (1-ρ)) := by gcongr
          _ = ε / 2 := by field_simp]

/-- **Pole pushing**: If `Kᶜ` is connected and `a ∉ K`, then `z ↦ (a - z)⁻¹` can be uniformly
approximated by polynomials on `K`. Uses connectedness to "move" the pole to infinity, then
applies `pole_approx_far`. -/
private lemma pole_push {K : Set ℂ} (hK : IsCompact K) (hKc : IsConnected Kᶜ)
    {a : ℂ} (ha : a ∉ K) :
    ∀ ε > 0, ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖Polynomial.eval z p - (a - z)⁻¹‖ < ε := by
  -- Trivial case: K is empty
  by_cases hKne : K.Nonempty
  swap
  · intro ε _; exact ⟨0, fun z hz => absurd ⟨z, hz⟩ hKne⟩
  -- K is compact → bounded → K ⊆ closedBall 0 R with R > 0
  obtain ⟨R, hR0, hKR⟩ := hK.isBounded.subset_closedBall_lt 0 0
  have hKcl : IsClosed K := hK.isClosed
  -- Define the "good" set: points outside K whose Cauchy kernel is poly-approx on K
  let S : Set ℂ := {b | b ∉ K ∧
    ∀ ε > 0, ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖eval z p - (b - z)⁻¹‖ < ε}
  -- It suffices to show a ∈ S
  suffices haS : a ∈ S from haS.2
  -- We use connectedness: show S and Kᶜ \ S are both open, S nonempty, they cover Kᶜ
  have hSKc : S ⊆ Kᶜ := fun b hb => hb.1
  -- Step 1: S is nonempty (pick a point far from K, use pole_approx_far)
  have hSne : S.Nonempty := by
    refine ⟨(↑(R + 1) : ℂ), ?_, fun ε hε => ?_⟩
    · intro hbK
      have hle := mem_closedBall_zero_iff.mp (hKR hbK)
      have : ‖(↑(R + 1) : ℂ)‖ = R + 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · have hRnorm : R < ‖(↑(R + 1) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
      obtain ⟨p, hp⟩ := pole_approx_far hR0.le hRnorm ε hε
      exact ⟨p, fun z hz => hp z (mem_closedBall_zero_iff.mp (hKR hz))⟩
  -- Step 2: S is open (using pole_transfer)
  have hS_open : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    intro b ⟨hbK, hbapprox⟩
    have hd_pos : 0 < Metric.infDist b K :=
      (Metric.infDist_pos_iff_notMem_closure hKne).mp (hKcl.closure_eq.symm ▸ hbK)
    refine ⟨Metric.ball b (Metric.infDist b K), fun c hc => ?_,
      Metric.isOpen_ball, Metric.mem_ball_self hd_pos⟩
    constructor
    · intro hcK
      exact absurd (Metric.mem_ball.mp hc)
        (not_lt.mpr ((dist_comm b c ▸ Metric.infDist_le_dist_of_mem hcK)))
    · exact pole_transfer hK hKne hbK hbapprox (Metric.mem_ball.mp hc)
  -- Step 3: Kᶜ \ S is open (using pole_transfer by contradiction)
  have hT_open : IsOpen (Kᶜ \ S) := by
    rw [isOpen_iff_forall_mem_open]
    intro c ⟨hcKc, hcS⟩
    have hd_pos : 0 < Metric.infDist c K :=
      (Metric.infDist_pos_iff_notMem_closure hKne).mp (hKcl.closure_eq.symm ▸ hcKc)
    refine ⟨Metric.ball c (Metric.infDist c K / 2),
      fun b hb => ?_, Metric.isOpen_ball, Metric.mem_ball_self (half_pos hd_pos)⟩
    have hbc : dist b c < Metric.infDist c K / 2 := Metric.mem_ball.mp hb
    constructor
    · intro hbK
      linarith [dist_comm c b ▸ Metric.infDist_le_dist_of_mem (s := K) hbK]
    · intro ⟨hbK, hbapprox⟩
      apply hcS; constructor; exact hcKc
      have hcb_lt : dist c b < Metric.infDist b K := by
        have := Metric.infDist_le_infDist_add_dist (x := c) (y := b) (s := K)
        rw [dist_comm] at hbc; linarith
      exact pole_transfer hK hKne hbK hbapprox hcb_lt
  -- Step 4: Apply connectedness of Kᶜ
  have hDisj : Disjoint S (Kᶜ \ S) := Set.disjoint_sdiff_right
  have hCover : Kᶜ ⊆ S ∪ (Kᶜ \ S) := fun x hx => by
    by_cases hxS : x ∈ S
    · exact Or.inl hxS
    · exact Or.inr ⟨hx, hxS⟩
  have hKcS : (Kᶜ ∩ S).Nonempty := hSne.mono (fun s hs => ⟨hSKc hs, hs⟩)
  exact hKc.isPreconnected.subset_left_of_subset_union hS_open hT_open hDisj hCover hKcS ha

-- Rational approximation via Cauchy integral formula: f can be approximated by rational functions
-- with poles outside K. This is the analytic core of Runge's theorem.
private lemma rational_approx {U K : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) (hf : DifferentiableOn ℂ f U) :
    ∀ ε > 0, ∃ (n : ℕ) (a : Fin n → ℂ) (c : Fin n → ℂ),
      (∀ i, a i ∉ K) ∧
      ∀ z ∈ K, ‖(∑ i, c i * (a i - z)⁻¹) - f z‖ < ε := by
  sorry

/-- **Runge's theorem**: A holomorphic function on an open set can be uniformly approximated on a
compact subset (with connected complement) by polynomials. -/
theorem MainTheorem {U K : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hKc : IsConnected (Kᶜ)) (hf : DifferentiableOn ℂ f U) :
    ∀ ε > 0, ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖Polynomial.eval z p - f z‖ < ε := by
  intro ε hε
  obtain ⟨n, a, c, ha, hrat⟩ := rational_approx hU hK hKU hf (ε / 2) (half_pos hε)
  set S := ∑ i : Fin n, ‖c i‖
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => norm_nonneg _
  set M := S + 1
  have hM : 0 < M := by linarith
  have : ∀ i : Fin n, ∃ q : Polynomial ℂ, ∀ z ∈ K,
      ‖eval z q - (a i - z)⁻¹‖ < ε / (2 * M) :=
    fun i => pole_push hK hKc (ha i) (ε / (2 * M)) (by positivity)
  choose q hq using this
  refine ⟨∑ i : Fin n, C (c i) * q i, fun z hz => ?_⟩
  simp only [eval_finset_sum, eval_mul, eval_C]
  have hsplit : ∑ i : Fin n, c i * eval z (q i) - f z =
      (∑ i, c i * (eval z (q i) - (a i - z)⁻¹)) + (∑ i, c i * (a i - z)⁻¹ - f z) := by
    rw [show ∑ i, c i * (eval z (q i) - (a i - z)⁻¹) =
        ∑ i, c i * eval z (q i) - ∑ i, c i * (a i - z)⁻¹ from by
      rw [← Finset.sum_sub_distrib]; congr 1; ext i; ring]; ring
  rw [hsplit]
  have h1 : ‖∑ i, c i * (eval z (q i) - (a i - z)⁻¹)‖ ≤ ε / 2 :=
    calc ‖∑ i, c i * (eval z (q i) - (a i - z)⁻¹)‖
        ≤ ∑ i, ‖c i * (eval z (q i) - (a i - z)⁻¹)‖ := norm_sum_le _ _
      _ = ∑ i, ‖c i‖ * ‖eval z (q i) - (a i - z)⁻¹‖ := by
          congr 1; ext i; exact norm_mul _ _
      _ ≤ ∑ i, ‖c i‖ * (ε / (2 * M)) := by
          apply Finset.sum_le_sum; intro i _
          exact mul_le_mul_of_nonneg_left (hq i z hz).le (norm_nonneg _)
      _ = S * (ε / (2 * M)) := by rw [← Finset.sum_mul]
      _ ≤ M * (ε / (2 * M)) := by gcongr; linarith
      _ = ε / 2 := by field_simp
  linarith [norm_add_le (∑ i, c i * (eval z (q i) - (a i - z)⁻¹))
    (∑ i, c i * (a i - z)⁻¹ - f z), hrat z hz]

end RungeTheorem
