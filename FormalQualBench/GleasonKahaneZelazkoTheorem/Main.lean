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
    -- Decompose: x*y = algebraMap(φx) * algebraMap(φy) + algebraMap(φx) * (y - algebraMap(φy))
    --                  + (x - algebraMap(φx)) * algebraMap(φy) + (x-algebraMap(φx))*(y-algebraMap(φy))
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
  haveI : NormedAlgebra ℝ A := NormedAlgebra.restrictScalars ℝ ℂ A
  haveI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hφ_cont : ∀ x : A, ‖φ x‖ ≤ ‖x‖ * ‖(1 : A)‖ :=
    fun x => spectrum.norm_le_norm_mul_of_mem (hφ_spec x)
  let φ_clm : A →L[ℂ] ℂ :=
    φ.mkContinuous ‖(1 : A)‖ (fun x => by rw [mul_comm]; exact hφ_cont x)
  -- Key: φ(a * exp(w•b)) = 0 for all w (Liouville + two-variable argument)
  have hφ_clm_eq : ∀ x, φ_clm x = φ x :=
    fun x => LinearMap.mkContinuous_apply ..
  have hc_zero : ∀ w : ℂ, φ (a * NormedSpace.exp (w • b)) = 0 := by
    have hg_bounded : Bornology.IsBounded
        (Set.range (fun w : ℂ =>
          φ_clm (a * NormedSpace.exp (w • b)))) := by
      sorry
    have hg_diff : Differentiable ℂ
        (fun w : ℂ => φ_clm (a * NormedSpace.exp (w • b))) :=
      φ_clm.differentiable.comp
        (((ContinuousLinearMap.mul ℂ A) a).differentiable.comp
          (fun t => (hasDerivAt_exp_smul_const b t).differentiableAt))
    have hg_const := hg_diff.apply_eq_apply_of_bounded hg_bounded
    intro w
    rw [← hφ_clm_eq, hg_const w 0]
    simp [zero_smul, NormedSpace.exp_zero, mul_one, hφ_clm_eq, ha]
  -- Extract φ(ab) = 0 by differentiating at w = 0
  have h_deriv : HasDerivAt (fun w : ℂ => φ (a * NormedSpace.exp (w • b)))
      (φ (a * b)) (0 : ℂ) := by
    have h_exp := hasDerivAt_exp_smul_const b (0 : ℂ)
    simp [zero_smul, NormedSpace.exp_zero, one_mul] at h_exp
    have h_amul := (ContinuousLinearMap.mul ℂ A a).hasFDerivAt
      (x := NormedSpace.exp ((0 : ℂ) • b))
    have h1 := h_amul.comp_hasDerivAt (0 : ℂ) h_exp
    simp at h1
    have h_phi := φ_clm.hasFDerivAt
      (x := a * NormedSpace.exp ((0 : ℂ) • b))
    have h2 := h_phi.comp_hasDerivAt (0 : ℂ) h1
    simp at h2
    rwa [LinearMap.mkContinuous_apply] at h2
  rw [(funext hc_zero : (fun w : ℂ => φ (a * NormedSpace.exp (w • b))) =
    fun _ => (0 : ℂ))] at h_deriv
  exact h_deriv.unique (hasDerivAt_const 0 0)

end GleasonKahaneZelazkoTheorem
