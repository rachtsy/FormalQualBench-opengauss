import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.ContinuousMap.Ideals
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Topology.UrysohnsLemma

namespace BanachStoneTheorem

open WeakDual

/-! ## Extreme point lemmas -/

set_option maxHeartbeats 800000 in
/-- Extreme points of the closed unit ball of `C(Y, ℝ)` satisfy `|f(y)| = 1` everywhere.
The proof uses the Urysohn bump argument. -/
lemma extremePoint_abs_eq_one {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [T2Space Y] (f : C(Y, ℝ))
    (hf : f ∈ Set.extremePoints ℝ (Metric.closedBall (0 : C(Y, ℝ)) 1)) :
    ∀ y, |f y| = 1 := by
  have hf_norm : ‖f‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hf.1
  by_contra h; push_neg at h
  obtain ⟨y₀, hy₀⟩ := h
  have hy₀_lt : |f y₀| < 1 := lt_of_le_of_ne
    ((Real.norm_eq_abs (f y₀) ▸ ContinuousMap.norm_coe_le_norm f y₀).trans hf_norm) hy₀
  set ε := (1 - |f y₀|) / 2
  have hε_pos : (0 : ℝ) < ε := by simp only [ε]; linarith
  set s : Set Y := {y | 1 - ε ≤ |f y|}
  have hs_closed : IsClosed s := isClosed_le continuous_const (Continuous.abs f.continuous)
  have hy₀_notin : y₀ ∉ s := by simp only [s, Set.mem_setOf_eq, not_le, ε]; linarith
  obtain ⟨φ, hφ_s, hφ_t, hφ_range⟩ := exists_continuous_zero_one_of_isClosed hs_closed
    isClosed_singleton (Set.disjoint_singleton_right.mpr hy₀_notin)
  set ψ : C(Y, ℝ) := (ε / 2) • φ
  have hψ_y₀ : ψ y₀ = ε / 2 := by
    change ε / 2 * φ y₀ = ε / 2
    have : φ y₀ = 1 := by have := hφ_t rfl; simpa using this
    rw [this, mul_one]
  have hψ_on_s : ∀ y ∈ s, ψ y = 0 := fun y hy => by
    change ε / 2 * φ y = 0
    have : φ y = 0 := by have := hφ_s hy; simpa using this
    rw [this, mul_zero]
  have hψ_nonneg : ∀ y, 0 ≤ ψ y := fun y =>
    show 0 ≤ ε / 2 * φ y from mul_nonneg (le_of_lt (by linarith)) (hφ_range y).1
  have hψ_le : ∀ y, ψ y ≤ ε / 2 := fun y =>
    show ε / 2 * φ y ≤ ε / 2 from
      mul_le_of_le_one_right (le_of_lt (by linarith)) (hφ_range y).2
  have norm_bound : ∀ (g : C(Y, ℝ)), (∀ y, ‖g y‖ ≤ 1) → ‖g‖ ≤ 1 := fun g hg =>
    (ContinuousMap.norm_le _ zero_le_one).mpr hg
  have h_add : f + ψ ∈ Metric.closedBall (0 : C(Y, ℝ)) 1 := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    apply norm_bound; intro y; rw [ContinuousMap.add_apply, Real.norm_eq_abs]
    by_cases hy : y ∈ s
    · rw [hψ_on_s y hy, add_zero]
      exact (Real.norm_eq_abs _ ▸ ContinuousMap.norm_coe_le_norm f y).trans hf_norm
    · simp only [s, Set.mem_setOf_eq, not_le] at hy
      have h1 := abs_add_le (f y) (ψ y)
      rw [abs_of_nonneg (hψ_nonneg y)] at h1; linarith [hψ_le y]
  have h_sub : f - ψ ∈ Metric.closedBall (0 : C(Y, ℝ)) 1 := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    apply norm_bound; intro y; rw [ContinuousMap.sub_apply, Real.norm_eq_abs]
    by_cases hy : y ∈ s
    · rw [hψ_on_s y hy, sub_zero]
      exact (Real.norm_eq_abs _ ▸ ContinuousMap.norm_coe_le_norm f y).trans hf_norm
    · simp only [s, Set.mem_setOf_eq, not_le] at hy
      have h1 : |f y - ψ y| ≤ |f y| + |ψ y| := by
        have := abs_add_le (f y) (-(ψ y))
        rwa [abs_neg, ← sub_eq_add_neg] at this
      rw [abs_of_nonneg (hψ_nonneg y)] at h1; linarith [hψ_le y]
  have hf_seg : f ∈ openSegment ℝ (f + ψ) (f - ψ) :=
    ⟨1/2, 1/2, by linarith, by linarith, by ring, by
      ext y; simp [ContinuousMap.add_apply, ContinuousMap.sub_apply,
        ContinuousMap.smul_apply]; ring⟩
  have heq := hf.2 h_add h_sub hf_seg
  have : ψ y₀ = 0 := by
    have : (f + ψ) y₀ = f y₀ := congr_fun (congr_arg DFunLike.coe heq) y₀
    simp [ContinuousMap.add_apply] at this; linarith
  linarith [hψ_y₀]

/-- The constant function `1` is an extreme point of the unit ball of `C(X, ℝ)`. -/
lemma one_mem_extremePoints {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [Nonempty X] :
    (1 : C(X, ℝ)) ∈ Set.extremePoints ℝ (Metric.closedBall 0 1) := by
  refine ⟨by simp [Metric.mem_closedBall], ?_⟩
  intro g₁ hg₁ g₂ hg₂ ⟨a, b, ha, hb, hab, hconv⟩
  simp only [Metric.mem_closedBall, dist_zero_right] at hg₁ hg₂
  ext x
  have hpw : a * g₁ x + b * g₂ x = 1 := by
    have := congr_fun (congr_arg DFunLike.coe hconv) x
    simp [ContinuousMap.add_apply, ContinuousMap.smul_apply] at this; linarith
  have hg1_le := le_of_abs_le
    (Real.norm_eq_abs _ ▸ (ContinuousMap.norm_coe_le_norm g₁ x).trans hg₁)
  have hg2_le := le_of_abs_le
    (Real.norm_eq_abs _ ▸ (ContinuousMap.norm_coe_le_norm g₂ x).trans hg₂)
  simp [ContinuousMap.one_apply]; nlinarith [hpw]

/-- The image of `1` under a linear isometry is an extreme point, hence `|e(1)(y)| = 1`. -/
lemma linearIsometryEquiv_one_abs_eq_one {X Y : Type*}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (e : C(X, ℝ) ≃ₗᵢ[ℝ] C(Y, ℝ)) : ∀ y, |(e 1 : C(Y, ℝ)) y| = 1 := by
  apply extremePoint_abs_eq_one
  have : e 1 ∈ e '' Set.extremePoints ℝ (Metric.closedBall 0 1) :=
    Set.mem_image_of_mem _ one_mem_extremePoints
  rw [show (⇑e : C(X, ℝ) → C(Y, ℝ)) = ⇑e.toLinearEquiv from rfl,
      image_extremePoints e.toLinearEquiv,
      show (⇑e.toLinearEquiv : C(X, ℝ) → C(Y, ℝ)) = ⇑e from rfl,
      LinearIsometryEquiv.image_closedBall, map_zero] at this
  exact this

/-! ## Helper lemmas for multiplicativity -/

private lemma nonneg_iff_norm_sub {A : Type*} [TopologicalSpace A] [CompactSpace A]
    [T2Space A] (f : C(A, ℝ)) :
    0 ≤ f ↔ ‖f - ‖f‖ • (1 : C(A, ℝ))‖ ≤ ‖f‖ := by
  constructor
  · intro hf
    apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
    intro x
    simp only [ContinuousMap.coe_sub, ContinuousMap.coe_smul, Pi.sub_apply,
      Pi.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one,
      Real.norm_eq_abs, abs_le]
    have hfx : (0 : ℝ) ≤ f x := hf x
    have hfn : f x ≤ ‖f‖ :=
      le_of_abs_le (Real.norm_eq_abs (f x) ▸ ContinuousMap.norm_coe_le_norm f x)
    exact ⟨by linarith, by linarith⟩
  · intro hle x
    have h1 := ContinuousMap.norm_coe_le_norm (f - ‖f‖ • (1 : C(A, ℝ))) x
    simp only [ContinuousMap.coe_sub, ContinuousMap.coe_smul, Pi.sub_apply,
      Pi.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one,
      Real.norm_eq_abs] at h1
    have h2 : |f x - ‖f‖| ≤ ‖f‖ := le_trans h1 hle
    change (0 : C(A, ℝ)) x ≤ f x
    simp only [ContinuousMap.zero_apply]; linarith [(abs_le.mp h2).1]

set_option maxHeartbeats 400000 in
private lemma sq_le_of_pos_unital
    {A B : Type*} [TopologicalSpace A] [CompactSpace A] [T2Space A]
    [TopologicalSpace B] [CompactSpace B] [T2Space B]
    (S : C(A, ℝ) →ₗ[ℝ] C(B, ℝ)) (hunit : S 1 = 1)
    (hpos : ∀ f : C(A, ℝ), 0 ≤ f → 0 ≤ S f)
    (f : C(A, ℝ)) (y : B) : (S f y) ^ 2 ≤ S (f ^ 2) y := by
  suffices ∀ c : ℝ, 0 ≤ S (f ^ 2) y - 2 * c * S f y + c ^ 2 by
    have := this (S f y); nlinarith
  intro c
  have h0 : (0 : C(A, ℝ)) ≤ (f - c • 1) ^ 2 :=
    fun x => by simp only [sq]; exact mul_self_nonneg _
  have expand : (f - c • (1 : C(A, ℝ))) ^ 2 =
      f ^ 2 + (-2 * c) • f + c ^ 2 • (1 : C(A, ℝ)) := by
    ext x; simp [sq]; ring
  have eval_eq : S ((f - c • 1) ^ 2) y = S (f ^ 2) y + (-2 * c) * S f y + c ^ 2 := by
    rw [expand]; simp only [map_add, map_smul, hunit]
    simp [ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
      smul_eq_mul, mul_one]
  have h1 : (0 : ℝ) ≤ S ((f - c • 1) ^ 2) y := hpos _ h0 y
  nlinarith

/-! ## Key lemma: linear isometry equiv → star algebra equiv -/

set_option maxHeartbeats 800000 in
lemma mul_image_mul_of_linearIsometryEquiv {X Y : Type*}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (e : C(X, ℝ) ≃ₗᵢ[ℝ] C(Y, ℝ))
    (h_sq : (e 1 : C(Y, ℝ)) * e 1 = 1) :
    ∀ f g : C(X, ℝ), e 1 * e (f * g) = (e 1 * e f) * (e 1 * e g) := by
  intro f₁ f₂
  set h := (e 1 : C(Y, ℝ)) with hdef
  have habs : ∀ y, |h y| = 1 := linearIsometryEquiv_one_abs_eq_one e
  have hmul := h_sq
  let S : C(X, ℝ) →ₗ[ℝ] C(Y, ℝ) :=
    { toFun := fun f => h * e f
      map_add' := fun a b => by simp [mul_add, map_add]
      map_smul' := fun r f => by
        change h * e (r • f) = r • (h * e f); rw [map_smul, mul_smul_comm] }
  let T : C(Y, ℝ) →ₗ[ℝ] C(X, ℝ) :=
    { toFun := fun g => e.symm (h * g)
      map_add' := fun a b => by simp [mul_add, map_add]
      map_smul' := fun r g => by
        change e.symm (h * (r • g)) = r • e.symm (h * g)
        rw [mul_smul_comm, map_smul] }
  have ST : ∀ g, S (T g) = g := fun g => by
    change h * e (e.symm (h * g)) = g
    rw [LinearIsometryEquiv.apply_symm_apply, ← mul_assoc, hmul, one_mul]
  have TS : ∀ f, T (S f) = f := fun f => by
    change e.symm (h * (h * e f)) = f
    rw [← mul_assoc, hmul, one_mul, LinearIsometryEquiv.symm_apply_apply]
  have S_one : S 1 = 1 := show h * e 1 = 1 by rw [← hdef]; exact hmul
  have T_one : T 1 = 1 := by
    change e.symm (h * 1) = 1
    rw [mul_one, hdef]; exact e.symm_apply_apply 1
  have norm_h_mul : ∀ g : C(Y, ℝ), ‖h * g‖ = ‖g‖ := by
    intro g; apply le_antisymm
    · apply (ContinuousMap.norm_le _ (norm_nonneg g)).mpr; intro y
      simp only [ContinuousMap.mul_apply, Real.norm_eq_abs, abs_mul, habs, one_mul]
      rw [← Real.norm_eq_abs]; exact ContinuousMap.norm_coe_le_norm g y
    · apply (ContinuousMap.norm_le _ (norm_nonneg (h * g))).mpr; intro y
      rw [Real.norm_eq_abs]
      have := ContinuousMap.norm_coe_le_norm (h * g) y
      rw [Real.norm_eq_abs, ContinuousMap.mul_apply, abs_mul, habs, one_mul] at this
      exact this
  have S_norm : ∀ f, ‖S f‖ = ‖f‖ := fun f => by
    change ‖h * e f‖ = ‖f‖; rw [norm_h_mul, e.norm_map]
  have T_norm : ∀ g, ‖T g‖ = ‖g‖ := fun g => by
    change ‖e.symm (h * g)‖ = ‖g‖; rw [e.symm.norm_map, norm_h_mul]
  have S_pos : ∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ S f := by
    intro f hf; rw [nonneg_iff_norm_sub]
    calc ‖S f - ‖S f‖ • 1‖ = ‖S f - ‖f‖ • S 1‖ := by rw [S_one, S_norm]
      _ = ‖S (f - ‖f‖ • 1)‖ := by rw [map_sub, map_smul]
      _ = ‖f - ‖f‖ • 1‖ := S_norm _
      _ ≤ ‖f‖ := (nonneg_iff_norm_sub f).mp hf
      _ = ‖S f‖ := (S_norm _).symm
  have T_pos : ∀ g : C(Y, ℝ), 0 ≤ g → 0 ≤ T g := by
    intro g hg; rw [nonneg_iff_norm_sub]
    calc ‖T g - ‖T g‖ • 1‖ = ‖T g - ‖g‖ • T 1‖ := by rw [T_one, T_norm]
      _ = ‖T (g - ‖g‖ • 1)‖ := by rw [map_sub, map_smul]
      _ = ‖g - ‖g‖ • 1‖ := T_norm _
      _ ≤ ‖g‖ := (nonneg_iff_norm_sub g).mp hg
      _ = ‖T g‖ := (T_norm _).symm
  have S_mono : ∀ a b : C(X, ℝ), a ≤ b → S a ≤ S b := by
    intro a b hab; have := S_pos _ (sub_nonneg.mpr hab); rwa [map_sub, sub_nonneg] at this
  have S_sq : ∀ f, S (f ^ 2) = (S f) ^ 2 := by
    intro f; apply le_antisymm
    · have jensen_T := sq_le_of_pos_unital T T_one T_pos (S f)
      have hord : f ^ 2 ≤ T ((S f) ^ 2) := by
        intro x; have := jensen_T x; rwa [TS] at this
      have hSord := S_mono _ _ hord; rwa [ST] at hSord
    · exact sq_le_of_pos_unital S S_one S_pos f
  have key : (4 : ℝ) • S (f₁ * f₂) = (4 : ℝ) • (S f₁ * S f₂) := by
    have four_mul : (4 : ℝ) • (f₁ * f₂) = (f₁ + f₂) ^ 2 - (f₁ - f₂) ^ 2 := by
      ext x; simp [sq, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
        ContinuousMap.add_apply, ContinuousMap.sub_apply, smul_eq_mul]; ring
    have four_mul' : ∀ a b : C(Y, ℝ),
        (a + b) ^ 2 - (a - b) ^ 2 = (4 : ℝ) • (a * b) := by
      intro a b; ext y; simp [sq, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
        ContinuousMap.add_apply, ContinuousMap.sub_apply, smul_eq_mul]; ring
    calc (4 : ℝ) • S (f₁ * f₂)
        = S ((4 : ℝ) • (f₁ * f₂)) := (map_smul S _ _).symm
      _ = S ((f₁ + f₂) ^ 2 - (f₁ - f₂) ^ 2) := by rw [four_mul]
      _ = S ((f₁ + f₂) ^ 2) - S ((f₁ - f₂) ^ 2) := map_sub S _ _
      _ = (S (f₁ + f₂)) ^ 2 - (S (f₁ - f₂)) ^ 2 := by rw [S_sq, S_sq]
      _ = (S f₁ + S f₂) ^ 2 - (S f₁ - S f₂) ^ 2 := by
          rw [show S (f₁ + f₂) = S f₁ + S f₂ from map_add S f₁ f₂,
              show S (f₁ - f₂) = S f₁ - S f₂ from map_sub S f₁ f₂]
      _ = (4 : ℝ) • (S f₁ * S f₂) := four_mul' (S f₁) (S f₂)
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  calc S (f₁ * f₂)
      = (4 : ℝ)⁻¹ • ((4 : ℝ) • S (f₁ * f₂)) := (inv_smul_smul₀ h4 _).symm
    _ = (4 : ℝ)⁻¹ • ((4 : ℝ) • (S f₁ * S f₂)) := by rw [key]
    _ = S f₁ * S f₂ := inv_smul_smul₀ h4 _

set_option maxHeartbeats 400000 in
/-- A linear isometry equivalence between `C(X,ℝ)` and `C(Y,ℝ)` induces a star algebra
equivalence. This is the core of the Banach-Stone theorem. -/
noncomputable def starAlgEquivOfLinearIsometryEquiv
    (X Y : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (e : C(X, ℝ) ≃ₗᵢ[ℝ] C(Y, ℝ)) :
    C(X, ℝ) ≃⋆ₐ[ℝ] C(Y, ℝ) := by
  set h : C(Y, ℝ) := e 1
  have h_sq : h * h = 1 := by
    ext y; simp only [ContinuousMap.mul_apply, ContinuousMap.one_apply, h]
    have hab := linearIsometryEquiv_one_abs_eq_one e y
    have : (e 1 : C(Y, ℝ)) y * (e 1 : C(Y, ℝ)) y = |(e 1 : C(Y, ℝ)) y| ^ 2 := by
      rw [sq_abs]; ring
    rw [this, hab]; norm_num
  have S_mul := mul_image_mul_of_linearIsometryEquiv e h_sq
  let S : C(X, ℝ) →ₐ[ℝ] C(Y, ℝ) :=
  { toFun := fun f => h * e f
    map_one' := by change h * e 1 = 1; change h * h = 1; exact h_sq
    map_mul' := S_mul
    map_zero' := by simp
    map_add' := fun f g => by simp [mul_add, map_add]
    commutes' := fun r => by
      change h * e ((algebraMap ℝ C(X, ℝ)) r) = (algebraMap ℝ C(Y, ℝ)) r
      simp [Algebra.algebraMap_eq_smul_one, map_smul]
      change r • (h * h) = r • 1; rw [h_sq] }
  have S_bij : Function.Bijective S := by
    constructor
    · intro f1 f2 (hf : h * e f1 = h * e f2)
      have : e f1 = e f2 := by
        have := congr_arg (h * ·) hf
        simp only [← mul_assoc, h_sq, one_mul] at this; exact this
      exact e.injective this
    · intro g
      exact ⟨e.symm (h * g), show h * e (e.symm (h * g)) = g by
        rw [LinearIsometryEquiv.apply_symm_apply, ← mul_assoc, h_sq, one_mul]⟩
  exact StarAlgEquiv.ofAlgEquiv (AlgEquiv.ofBijective S S_bij)
    (fun f => by ext x; simp [star_trivial])

/-! ## From star algebra equiv to homeomorphism via character spaces -/

/-- A star algebra equivalence induces a homeomorphism on character spaces. -/
noncomputable def charSpaceHomeoOfStarAlgEquiv
    {A B : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [StarRing A]
    [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B] [StarRing B]
    (φ : A ≃⋆ₐ[ℝ] B) :
    characterSpace ℝ B ≃ₜ characterSpace ℝ A := by
  let fwd := CharacterSpace.compContinuousMap (φ : A →⋆ₐ[ℝ] B)
  let bwd := CharacterSpace.compContinuousMap (φ.symm : B →⋆ₐ[ℝ] A)
  have key1 : (φ : A →⋆ₐ[ℝ] B).comp (φ.symm : B →⋆ₐ[ℝ] A) = StarAlgHom.id ℝ B := by
    ext b; simp [StarAlgHom.comp_apply, StarAlgEquiv.apply_symm_apply]
  have key2 : (φ.symm : B →⋆ₐ[ℝ] A).comp (φ : A →⋆ₐ[ℝ] B) = StarAlgHom.id ℝ A := by
    ext a; simp [StarAlgHom.comp_apply, StarAlgEquiv.symm_apply_apply]
  have hleft : bwd.comp fwd = ContinuousMap.id _ := by
    rw [← CharacterSpace.compContinuousMap_comp, key1,
      CharacterSpace.compContinuousMap_id]
  have hright : fwd.comp bwd = ContinuousMap.id _ := by
    rw [← CharacterSpace.compContinuousMap_comp, key2,
      CharacterSpace.compContinuousMap_id]
  exact ⟨⟨fwd, bwd,
    fun x => congr_fun (congr_arg DFunLike.coe hleft) x,
    fun x => congr_fun (congr_arg DFunLike.coe hright) x⟩,
    fwd.continuous, bwd.continuous⟩

/-! ## Main theorem -/

/-- Banach-Stone theorem for real-valued continuous functions on compact Hausdorff spaces:
if `C(X, ℝ) ≃ₗᵢ[ℝ] C(Y, ℝ)`, then `X ≃ₜ Y`. The proof constructs a star algebra
equivalence from the linear isometry (via the `S(f) = e(1) · e(f)` trick), then uses
Gelfand duality (character space identification) to obtain the homeomorphism. -/
theorem MainTheorem (X Y : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (e : C(X, ℝ) ≃ₗᵢ[ℝ] C(Y, ℝ)) :
    Nonempty (X ≃ₜ Y) := by
  -- Handle the empty case: if X is empty, Y must be empty, and both are homeomorphic
  by_cases hX : Nonempty X
  · haveI := hX
    haveI : Nonempty Y := by
      by_contra hY; rw [not_nonempty_iff] at hY; haveI := hY
      have : ‖(e 1 : C(Y, ℝ))‖ = 0 := norm_of_subsingleton _
      rw [e.norm_map] at this; simp at this
    let φ := starAlgEquivOfLinearIsometryEquiv X Y e
    let eX := CharacterSpace.homeoEval X ℝ
    let eY := CharacterSpace.homeoEval Y ℝ
    let charHomeo := charSpaceHomeoOfStarAlgEquiv φ
    exact ⟨eX.trans (charHomeo.symm.trans eY.symm)⟩
  · rw [not_nonempty_iff] at hX; haveI := hX
    haveI : IsEmpty Y := by
      by_contra hY; rw [not_isEmpty_iff] at hY; haveI := hY
      have : ‖(e.symm 1 : C(X, ℝ))‖ = 0 := norm_of_subsingleton _
      rw [e.symm.norm_map] at this; simp at this
    exact ⟨{
      toEquiv := Equiv.equivOfIsEmpty X Y
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology
    }⟩

end BanachStoneTheorem
