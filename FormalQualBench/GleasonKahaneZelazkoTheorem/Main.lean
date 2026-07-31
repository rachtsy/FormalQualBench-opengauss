import Mathlib

namespace GleasonKahaneZelazkoTheorem

/-- Gleason-Kahane-Zelazko theorem for complex Banach algebras: a normalized complex-linear
functional on a complex Banach algebra that does not vanish on invertible elements is an algebra
homomorphism. -/
theorem MainTheorem (A : Type*) [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] :
    ∀ φ : A →ₗ[ℂ] ℂ, φ 1 = 1 →
      (∀ a : A, IsUnit a → φ a ≠ 0) →
      ∃ ψ : A →ₐ[ℂ] ℂ, ψ.toLinearMap = φ := by
  intro φ hφ1 hφ_inv
  -- Reduce to multiplicativity
  suffices hmul : ∀ x y : A, φ (x * y) = φ x * φ y by
    exact ⟨AlgHom.ofLinearMap φ hφ1 hmul, AlgHom.toLinearMap_ofLinearMap φ hφ1 hmul⟩
  -- Helper: φ on scalars
  have hφ_alg : ∀ c : ℂ, φ ((algebraMap ℂ A) c) = c := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hφ1, smul_eq_mul, mul_one]
  -- Helper: φ(a) ∈ spectrum(a)
  have hφ_spec : ∀ a : A, φ a ∈ spectrum ℂ a := by
    intro a
    rw [spectrum.mem_iff]
    intro h_unit
    have h0 : φ ((algebraMap ℂ A) (φ a) - a) = 0 := by
      simp [map_sub, hφ_alg]
    exact absurd h0 (hφ_inv _ h_unit)
  -- Helper: left multiplication by algebraMap
  have hφ_alg_mul_left : ∀ (c : ℂ) (a : A), φ ((algebraMap ℂ A) c * a) = c * φ a := by
    intro c a
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]
  -- Helper: right multiplication by algebraMap
  have hφ_alg_mul_right : ∀ (a : A) (c : ℂ), φ (a * (algebraMap ℂ A) c) = φ a * c := by
    intro a c
    rw [← Algebra.commutes, hφ_alg_mul_left, mul_comm]
  -- Reduce multiplicativity to: ker(φ) closed under multiplication
  suffices hker_mul : ∀ a b : A, φ a = 0 → φ b = 0 → φ (a * b) = 0 by
    intro x y
    have hx' : φ (x - (algebraMap ℂ A) (φ x)) = 0 := by simp [map_sub, hφ_alg]
    have hy' : φ (y - (algebraMap ℂ A) (φ y)) = 0 := by simp [map_sub, hφ_alg]
    -- Decompose: x*y = algebraMap(φx)*y + (x - algebraMap(φx))*y
    have decomp : x * y = (algebraMap ℂ A) (φ x) * y + (x - (algebraMap ℂ A) (φ x)) * y := by
      rw [← add_mul, add_sub_cancel]
    rw [decomp, map_add, hφ_alg_mul_left]
    -- Now need: φ((x - algebraMap(φ x)) * y) = 0
    have decomp2 : (x - (algebraMap ℂ A) (φ x)) * y =
        (x - (algebraMap ℂ A) (φ x)) * (algebraMap ℂ A) (φ y) +
        (x - (algebraMap ℂ A) (φ x)) * (y - (algebraMap ℂ A) (φ y)) := by
      rw [← mul_add, add_sub_cancel]
    rw [decomp2, map_add, hφ_alg_mul_right, hx', zero_mul, zero_add]
    rw [hker_mul _ _ hx' hy', add_zero]
  -- The hard part: ker(φ) is closed under multiplication
  intro a b ha hb
  -- Infrastructure: make φ continuous via spectrum bound
  have hφ_cont : ∀ x : A, ‖φ x‖ ≤ ‖x‖ * ‖(1 : A)‖ :=
    fun x => spectrum.norm_le_norm_mul_of_mem (hφ_spec x)
  let φ_clm : A →L[ℂ] ℂ :=
    φ.mkContinuous ‖(1 : A)‖ (fun x => by rw [mul_comm]; exact hφ_cont x)
  have hφ_clm_eq : ∀ x, φ_clm x = φ x := fun x => LinearMap.mkContinuous_apply ..
  -- Step 0 (sorry): φ(exp(w•c)) = 1 for c ∈ ker(φ)
  -- Provable via holomorphic logarithm + Liouville on log(φ(exp(λc)))/λ ↦ σ(c)
  have hφ_exp_ker : ∀ c : A, φ c = 0 → ∀ w : ℂ, φ (NormedSpace.exp (w • c)) = 1 := by
    intro c hc
    -- G(w) = φ(exp(w•c)) never vanishes since exp is always invertible
    have hG_ne : ∀ w : ℂ, φ (NormedSpace.exp (w • c)) ≠ 0 := fun w =>
      hφ_inv _ (NormedSpace.isUnit_exp_of_mem_ball (𝕂 := ℂ)
        (by simp [NormedSpace.expSeries_radius_eq_top]))
    -- The ratio φ(c·exp(w•c))/φ(exp(w•c)) lies in σ(c) for all w
    -- Proof: if z ∉ σ(c), then (algebraMap z - c)·exp(w•c) is invertible,
    -- so φ of it is nonzero, but φ of it equals z·G(w) - G'(w).
    -- Taking z = G'(w)/G(w) gives 0 ≠ 0, contradiction.
    have hRatio_spec : ∀ w : ℂ,
        φ (c * NormedSpace.exp (w • c)) / φ (NormedSpace.exp (w • c)) ∈ spectrum ℂ c := by
      intro w
      rw [spectrum.mem_iff]
      intro h_unit
      set z := φ (c * NormedSpace.exp (w • c)) / φ (NormedSpace.exp (w • c))
      have h_prod_unit : IsUnit (((algebraMap ℂ A) z - c) * NormedSpace.exp (w • c)) :=
        h_unit.mul (NormedSpace.isUnit_exp_of_mem_ball (𝕂 := ℂ)
          (by simp [NormedSpace.expSeries_radius_eq_top]))
      have h_eq : φ (((algebraMap ℂ A) z - c) * NormedSpace.exp (w • c)) = 0 := by
        simp only [sub_mul, map_sub, hφ_alg_mul_left, z]
        rw [div_mul_cancel₀ _ (hG_ne w)]; exact sub_self _
      exact absurd h_eq (hφ_inv _ h_prod_unit)
    -- Differentiability of w ↦ exp(w•c)
    have hexp_diff : Differentiable ℂ (fun t : ℂ => NormedSpace.exp (t • c)) :=
      fun w => (hasDerivAt_exp_smul_const' c w).differentiableAt
    -- Convert nonvanishing to φ_clm
    have hG_ne_clm : ∀ w : ℂ, φ_clm (NormedSpace.exp (w • c)) ≠ 0 := by
      intro w; rw [hφ_clm_eq]; exact hG_ne w
    -- The ratio is differentiable (entire)
    have hRatio_diff : Differentiable ℂ (fun w : ℂ =>
        φ_clm (c * NormedSpace.exp (w • c)) / φ_clm (NormedSpace.exp (w • c))) :=
      Differentiable.fun_div
        (φ_clm.differentiable.comp ((ContinuousLinearMap.mul ℂ A c).differentiable.comp hexp_diff))
        (φ_clm.differentiable.comp hexp_diff)
        hG_ne_clm
    -- Range of ratio is bounded (contained in σ(c) which is bounded)
    have hRatio_bdd : Bornology.IsBounded (Set.range (fun w : ℂ =>
        φ_clm (c * NormedSpace.exp (w • c)) / φ_clm (NormedSpace.exp (w • c)))) :=
      (spectrum.isBounded c).subset (Set.range_subset_iff.mpr
        (fun w => by simp only [hφ_clm_eq]; exact hRatio_spec w))
    -- By Liouville: ratio is constant. At w=0 it equals φ(c)/φ(1) = 0/1 = 0.
    have hRatio_const := hRatio_diff.apply_eq_apply_of_bounded hRatio_bdd
    have hRatio_zero : φ_clm (c * NormedSpace.exp ((0 : ℂ) • c)) /
        φ_clm (NormedSpace.exp ((0 : ℂ) • c)) = 0 := by
      simp [zero_smul, NormedSpace.exp_zero, mul_one, hφ_clm_eq, hc, hφ1]
    -- Therefore φ(c·exp(w•c)) = 0 for all w
    have hG'_zero : ∀ w : ℂ, φ_clm (c * NormedSpace.exp (w • c)) = 0 := by
      intro w
      have h := hRatio_const w 0
      rw [hRatio_zero, div_eq_zero_iff] at h
      exact h.elim id (absurd · (hG_ne_clm w))
    -- Since deriv G = G' = 0, G is constant by is_const_of_deriv_eq_zero
    have hG_diff : Differentiable ℂ (fun t : ℂ => φ_clm (NormedSpace.exp (t • c))) :=
      φ_clm.differentiable.comp hexp_diff
    have hG_deriv_zero : ∀ w : ℂ,
        deriv (fun t : ℂ => φ_clm (NormedSpace.exp (t • c))) w = 0 := by
      intro w
      have h_hd : HasDerivAt (fun t : ℂ => φ_clm (NormedSpace.exp (t • c)))
          (φ_clm (c * NormedSpace.exp (w • c))) w :=
        (φ_clm.hasFDerivAt).comp_hasDerivAt w (hasDerivAt_exp_smul_const' c w)
      rw [h_hd.deriv]
      exact hG'_zero w
    -- G(w) = G(0) = φ(exp(0)) = φ(1) = 1
    intro w
    have := is_const_of_deriv_eq_zero hG_diff hG_deriv_zero w 0
    simp only [hφ_clm_eq] at this
    rw [this, zero_smul, NormedSpace.exp_zero, hφ1]
  -- Step 1: φ(c * c) = 0 for c ∈ ker(φ) via differentiating exp twice
  have hφ_sq_ker : ∀ c : A, φ c = 0 → φ (c * c) = 0 := by
    intro c hc
    -- First derivative: w ↦ φ(exp(w•c)) is constant 1, so its derivative is 0
    -- Derivative equals φ(c * exp(w•c)), hence φ(c * exp(w•c)) = 0 for all w
    have h_cmul_exp : ∀ w : ℂ, φ (c * NormedSpace.exp (w • c)) = 0 := by
      intro w
      have h_deriv : HasDerivAt (fun t => φ_clm (NormedSpace.exp (t • c)))
          (φ_clm (c * NormedSpace.exp (w • c))) w :=
        (φ_clm.hasFDerivAt).comp_hasDerivAt w (hasDerivAt_exp_smul_const' c w)
      have h_eq : (fun t => φ_clm (NormedSpace.exp (t • c))) = fun _ => (1 : ℂ) :=
        funext fun t => by rw [hφ_clm_eq]; exact hφ_exp_ker c hc t
      rw [h_eq] at h_deriv
      have := h_deriv.unique (hasDerivAt_const w 1)
      rwa [hφ_clm_eq] at this
    -- Second derivative at w = 0: w ↦ φ(c * exp(w•c)) is constant 0
    -- Derivative at 0 equals φ(c * c * exp(0)) = φ(c * c), which must be 0
    have h_deriv2 : HasDerivAt (fun t => φ_clm (c * NormedSpace.exp (t • c)))
        (φ_clm (c * (c * NormedSpace.exp ((0 : ℂ) • c)))) (0 : ℂ) :=
      (φ_clm.hasFDerivAt).comp_hasDerivAt 0
        (((ContinuousLinearMap.mul ℂ A c).hasFDerivAt).comp_hasDerivAt 0
          (hasDerivAt_exp_smul_const' c 0))
    have h_eq2 : (fun t => φ_clm (c * NormedSpace.exp (t • c))) = fun _ => (0 : ℂ) :=
      funext fun t => by rw [hφ_clm_eq]; exact h_cmul_exp t
    rw [h_eq2] at h_deriv2
    have h_final := h_deriv2.unique (hasDerivAt_const 0 0)
    rw [hφ_clm_eq, zero_smul, NormedSpace.exp_zero, mul_one] at h_final
    exact h_final
  -- Step 2: φ(x * x) = φ(x) * φ(x) for all x (shift by algebraMap)
  have hφ_sq : ∀ x : A, φ (x * x) = φ x * φ x := by
    intro x
    have hc : φ (x - (algebraMap ℂ A) (φ x)) = 0 := by simp [map_sub, hφ_alg]
    have h := hφ_sq_ker _ hc
    have key : φ ((x - (algebraMap ℂ A) (φ x)) * (x - (algebraMap ℂ A) (φ x))) =
        φ (x * x) - φ x * φ x := by
      have expand : (x - (algebraMap ℂ A) (φ x)) * (x - (algebraMap ℂ A) (φ x)) =
          x * x - x * (algebraMap ℂ A) (φ x) - (algebraMap ℂ A) (φ x) * x +
          (algebraMap ℂ A) (φ x) * (algebraMap ℂ A) (φ x) := by noncomm_ring
      rw [expand, map_add, map_sub, map_sub, hφ_alg_mul_right, hφ_alg_mul_left,
          hφ_alg_mul_left, hφ_alg]
      ring
    rw [key] at h; exact sub_eq_zero.mp h
  -- Step 3: Jordan identity: φ(x*y + y*x) = 2 * φ(x) * φ(y)
  have hφ_jordan : ∀ x y : A, φ (x * y + y * x) = 2 * φ x * φ y := by
    intro x y
    have h1 := hφ_sq (x + y)
    rw [map_add] at h1
    have h_expand : (x + y) * (x + y) = x * x + (x * y + y * x) + y * y := by noncomm_ring
    rw [h_expand, map_add, map_add, hφ_sq x, hφ_sq y] at h1
    linear_combination h1
  -- Step 4: Quadratic argument showing φ(a*b) = 0
  -- From Jordan(a, b): φ(ab + ba) = 0, so φ(ba) = -φ(ab)
  have hab_ba : φ (a * b + b * a) = 0 := by rw [hφ_jordan]; simp [ha]
  have hab_neg : φ (b * a) = -φ (a * b) := by
    have h1 : φ (a * b) + φ (b * a) = 0 := by rw [← map_add]; exact hab_ba
    linear_combination h1
  -- From Jordan(a, b*a*b): φ(a*b*a*b + b*a*b*a) = 0
  have h_sum : φ (a * (b * a * b) + b * a * b * a) = 0 := by
    rw [hφ_jordan]; simp [ha]
  -- Rewrite: a*(b*a*b) = (ab)² and (b*a*b)*a = (ba)²
  rw [map_add, show a * (b * a * b) = a * b * (a * b) from by noncomm_ring,
    show b * a * b * a = b * a * (b * a) from by noncomm_ring,
    hφ_sq (a * b), hφ_sq (b * a), hab_neg] at h_sum
  -- h_sum : φ(ab)² + (-φ(ab))² = 0, i.e., 2 * φ(ab)² = 0
  have h2 : φ (a * b) * φ (a * b) = 0 := by
    have : (2 : ℂ) * (φ (a * b) * φ (a * b)) = 0 := by linear_combination h_sum
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (by norm_num : (2 : ℂ) ≠ 0)
    · exact h
  exact mul_self_eq_zero.mp h2

end GleasonKahaneZelazkoTheorem
