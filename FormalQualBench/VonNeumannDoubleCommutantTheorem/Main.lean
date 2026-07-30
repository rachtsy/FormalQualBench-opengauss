import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace VonNeumannDoubleCommutantTheorem

set_option linter.unusedSectionVars false
set_option linter.style.show false
set_option linter.style.maxHeartbeats false
set_option linter.style.longLine false
open scoped Topology InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private noncomputable def diagCLM (n : ℕ) (s : H →L[ℂ] H) :
    PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => s.comp (PiLp.proj 2 _ i)))

private lemma diagCLM_single (n : ℕ) (s : H →L[ℂ] H) (k : Fin n) (w : H) :
    diagCLM n s (WithLp.toLp 2 (Pi.single k w)) = WithLp.toLp 2 (Pi.single k (s w)) := by
  ext j; simp [diagCLM, Pi.single, Function.update, PiLp.proj]; split <;> simp

private lemma adjoint_diagCLM (n : ℕ) (s : H →L[ℂ] H) :
    ContinuousLinearMap.adjoint (diagCLM n s) = diagCLM n (ContinuousLinearMap.adjoint s) := by
  rw [eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro v w; simp only [PiLp.inner_apply]; congr 1; ext i
  exact ContinuousLinearMap.adjoint_inner_left s (w.ofLp i) (v.ofLp i)

private lemma ofLp_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → PiLp 2 (fun _ : Fin n => H)) (j : Fin n) :
    (∑ k ∈ s, f k).ofLp j = ∑ k ∈ s, (f k).ofLp j := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => simp [Finset.sum_cons, ih]

set_option maxHeartbeats 400000 in
private lemma diagCLM_bicommutant (n : ℕ) (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer)
    (M : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H))
    (hM : ∀ s ∈ (S : Set (H →L[ℂ] H)), diagCLM n s * M = M * diagCLM n s) :
    diagCLM n T * M = M * diagCLM n T := by
  have hentry : ∀ j k : Fin n,
      (PiLp.proj 2 _ j).comp (M.comp
        ((PiLp.continuousLinearEquiv 2 ℂ _).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.single ℂ _ k))) ∈
        (S : Set (H →L[ℂ] H)).centralizer := by
    intro j k s hs; ext w
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
      PiLp.proj_apply, ContinuousLinearMap.single_apply, ContinuousLinearEquiv.coe_coe]
    have h := congr_arg (fun v => v.ofLp j)
      (ContinuousLinearMap.ext_iff.mp (hM s hs) (WithLp.toLp 2 (Pi.single k w)))
    simpa [ContinuousLinearMap.mul_apply, diagCLM_single] using h
  have hTentry : ∀ j k : Fin n, ∀ w : H,
      T ((M (WithLp.toLp 2 (Pi.single k w))).ofLp j) =
        (M (WithLp.toLp 2 (Pi.single k (T w)))).ofLp j := by
    intro j k w
    have h := ContinuousLinearMap.ext_iff.mp (hT _ (hentry j k)) w
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
      PiLp.proj_apply, ContinuousLinearMap.single_apply, ContinuousLinearEquiv.coe_coe] at h
    exact h.symm
  ext v j; simp only [ContinuousLinearMap.mul_apply]
  have hv : v = ∑ k, WithLp.toLp 2 (Pi.single k (v.ofLp k)) := by
    ext i
    simp [Finset.sum_apply, Pi.single, Function.update, Finset.sum_ite_eq, Finset.mem_univ]
  conv_lhs => rw [hv]
  conv_rhs => rw [hv]
  simp only [map_sum, diagCLM_single]
  rw [ofLp_sum, ofLp_sum]
  exact Finset.sum_congr rfl (fun k _ => hTentry j k (v.ofLp k))

private noncomputable def diagApply (n : ℕ) (v : PiLp 2 (fun _ : Fin n => H)) :
    (H →L[ℂ] H) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => H) where
  toFun s := diagCLM n s v
  map_add' s t := by ext j; simp [diagCLM]
  map_smul' c s := by ext j; simp [diagCLM]

set_option maxHeartbeats 800000 in
private lemma mem_closure_piLp (n : ℕ) (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ (S : Set (H →L[ℂ] H)).centralizer.centralizer)
    (v : PiLp 2 (fun _ : Fin n => H)) :
    diagCLM n T v ∈ closure ((fun s => diagCLM n s v) '' (S : Set (H →L[ℂ] H))) := by
  set V := S.toSubalgebra.toSubmodule.map (diagApply n v)
  have hV_eq : (V : Set _) = (fun s => diagCLM n s v) '' (S : Set (H →L[ℂ] H)) := by
    ext y; exact ⟨fun ⟨s, hs, h⟩ => ⟨s, hs, h⟩, fun ⟨s, hs, h⟩ => ⟨s, hs, h⟩⟩
  rw [← hV_eq]
  set K := V.topologicalClosure
  haveI : K.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace K
  have hv_V : v ∈ V :=
    Submodule.mem_map.mpr ⟨1, Subalgebra.one_mem _, by ext j; simp [diagApply, diagCLM]⟩
  have hS_V : ∀ s ∈ (S : Set (H →L[ℂ] H)), ∀ w ∈ V, diagCLM n s w ∈ V := by
    intro s hs w hw
    obtain ⟨t, ht, htw⟩ := Submodule.mem_map.mp hw
    exact Submodule.mem_map.mpr ⟨s * t, S.toSubalgebra.mul_mem hs ht,
      by ext j; simp [diagApply, diagCLM, ContinuousLinearMap.mul_apply, ← htw]⟩
  have hS_K : ∀ s ∈ (S : Set (H →L[ℂ] H)), ∀ w ∈ K, diagCLM n s w ∈ K := by
    intro s hs w hw
    have hsub : (V : Set _) ⊆ (diagCLM n s) ⁻¹' closure (V : Set _) :=
      fun u hu => subset_closure (hS_V s hs u hu)
    exact closure_minimal hsub (isClosed_closure.preimage (diagCLM n s).cont) hw
  have hS_Ko : ∀ s ∈ (S : Set (H →L[ℂ] H)), ∀ w ∈ Kᗮ, diagCLM n s w ∈ Kᗮ := by
    intro s hs w hw
    rw [Submodule.mem_orthogonal'] at hw ⊢; intro u hu
    rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_diagCLM]
    exact hw _ (hS_K _ (star_mem hs) u hu)
  have hP_comm : ∀ s ∈ (S : Set (H →L[ℂ] H)),
      K.starProjection * diagCLM n s = diagCLM n s * K.starProjection := by
    intro s hs; ext w; simp only [ContinuousLinearMap.mul_apply]
    rw [show diagCLM n s w = diagCLM n s (K.starProjection w) +
        diagCLM n s (w - K.starProjection w) from by rw [map_sub, add_sub_cancel],
      map_add,
      Submodule.starProjection_eq_self_iff.mpr
        (hS_K s hs _ (K.starProjection_apply_mem w)),
      (Submodule.starProjection_apply_eq_zero_iff K).mpr
        (hS_Ko s hs _ (K.sub_starProjection_mem_orthogonal w)),
      add_zero]
  have hPv : K.starProjection v = v :=
    Submodule.starProjection_eq_self_iff.mpr (Submodule.le_topologicalClosure V hv_V)
  have h := ContinuousLinearMap.ext_iff.mp
    (diagCLM_bicommutant n S T hT K.starProjection
      (fun s hs => (hP_comm s hs).symm)) v
  simp only [ContinuousLinearMap.mul_apply] at h
  rw [hPv] at h
  exact Submodule.starProjection_eq_self_iff.mp h.symm

set_option maxHeartbeats 600000 in
private lemma mem_closure_wot (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (happrox : ∀ (n : ℕ) (x : Fin n → H) (ε : ℝ), ε > 0 →
      ∃ s ∈ (S : Set (H →L[ℂ] H)), ∀ i, ‖s (x i) - T (x i)‖ < ε) :
    ContinuousLinearMap.toWOT (RingHom.id ℂ) H H T ∈
      closure (ContinuousLinearMap.toWOT (RingHom.id ℂ) H H '' (S : Set (H →L[ℂ] H))) := by
  set toWOT := ContinuousLinearMap.toWOT (RingHom.id ℂ) H H
  set g := ContinuousLinearMapWOT.inducingFn (RingHom.id ℂ) H H
  rw [ContinuousLinearMapWOT.isInducing_inducingFn.closure_eq_preimage_closure_image]
  simp only [Set.mem_preimage]
  rw [mem_closure_iff_nhds]
  intro U hU
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, t, ht, htU⟩ := hU
  choose ε hε_pos hε_sub using fun i => Metric.mem_nhds_iff.mp (ht i)
  by_cases hI : I.Nonempty
  case neg =>
    push_neg at hI; simp only [hI, Finset.coe_empty, Set.empty_pi] at htU
    exact ⟨g (toWOT 1), htU (Set.mem_univ _), toWOT 1, ⟨1, Subalgebra.one_mem _, rfl⟩, rfl⟩
  case pos =>
    set e := I.equivFin
    set x : Fin I.card → H := fun j => ((e.symm j : H × StrongDual ℂ H)).1
    set δ := I.inf' hI (fun i => ε i / (‖i.2‖ + 1))
    have hδ_pos : δ > 0 := by
      simp only [δ, gt_iff_lt, Finset.lt_inf'_iff]
      exact fun i _ => div_pos (hε_pos i) (by linarith [norm_nonneg i.2])
    obtain ⟨s, hs, happr⟩ := happrox I.card x δ hδ_pos
    refine ⟨g (toWOT s), htU (fun i hi => hε_sub i ?_), toWOT s, ⟨s, hs, rfl⟩, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have hyi : (0 : ℝ) < ‖i.2‖ + 1 := by linarith [norm_nonneg i.2]
    have hx_eq : x (e ⟨i, hi⟩) = i.1 := by simp [x, Equiv.symm_apply_apply]
    show ‖g (toWOT s) i - g (toWOT T) i‖ < ε i
    calc ‖g (toWOT s) i - g (toWOT T) i‖
        = ‖i.2 (s i.1 - T i.1)‖ := by
            show ‖i.2 (s i.1) - i.2 (T i.1)‖ = _; rw [← map_sub]
      _ ≤ ‖i.2‖ * ‖s i.1 - T i.1‖ := i.2.le_opNorm _
      _ = ‖i.2‖ * ‖s (x (e ⟨i, hi⟩)) - T (x (e ⟨i, hi⟩))‖ := by rw [hx_eq]
      _ ≤ ‖i.2‖ * δ := by gcongr; exact (happr _).le
      _ ≤ ‖i.2‖ * (ε i / (‖i.2‖ + 1)) := by gcongr; exact Finset.inf'_le _ hi
      _ < ε i := by
          calc ‖i.2‖ * (ε i / (‖i.2‖ + 1)) = ε i * (‖i.2‖ / (‖i.2‖ + 1)) := by ring
            _ < ε i * 1 := mul_lt_mul_of_pos_left
                ((div_lt_one hyi).mpr (by linarith)) (hε_pos i)
            _ = ε i := mul_one _

private lemma isClosed_wot_centralizer (A : Set (H →L[ℂ] H)) :
    IsClosed (ContinuousLinearMap.toWOT (RingHom.id ℂ) H H '' A.centralizer) := by
  set toWOT := ContinuousLinearMap.toWOT (RingHom.id ℂ) H H
  suffices h_eq : toWOT '' A.centralizer =
      ⋂ (a : H →L[ℂ] H) (_ : a ∈ A) (x : H) (y : StrongDual ℂ H),
        {T : ContinuousLinearMapWOT (RingHom.id ℂ) H H |
          y (T (a x)) = (y.comp a) (T x)} by
    rw [h_eq]
    apply isClosed_iInter; intro a; apply isClosed_iInter; intro _
    apply isClosed_iInter; intro x; apply isClosed_iInter; intro y
    exact isClosed_eq (ContinuousLinearMapWOT.continuous_dual_apply (a x) y)
      (ContinuousLinearMapWOT.continuous_dual_apply x (y.comp a))
  ext T; simp only [Set.mem_image, Set.mem_iInter, Set.mem_setOf_eq]
  constructor
  · rintro ⟨S, hS, rfl⟩ a ha x y
    exact congr_arg y (ContinuousLinearMap.ext_iff.mp
      (Set.mem_centralizer_iff.mp hS a ha) x).symm
  · intro h
    refine ⟨toWOT.symm T, ?_, LinearEquiv.apply_symm_apply toWOT T⟩
    rw [Set.mem_centralizer_iff]; intro a ha; ext x
    have h' : ∀ y : StrongDual ℂ H, y (T (a x)) = y (a (T x)) := by
      intro y; have := h a ha x y
      simp only [ContinuousLinearMap.comp_apply] at this; exact this
    have h0 : T (a x) - a (T x) = 0 := by
      by_contra hne
      obtain ⟨f, hf⟩ := (inferInstance : SeparatingDual ℂ H).exists_ne_zero'
        (T (a x) - a (T x)) hne
      exact hf (by simp [map_sub, h' f])
    exact (sub_eq_zero.mp h0).symm

set_option maxHeartbeats 400000 in
/-- **von Neumann double commutant theorem (statement)**:
for a unital *-subalgebra `S ⊆ B(H)`, being closed in the weak operator topology is equivalent to
being equal to its bicommutant. -/
theorem MainTheorem (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    IsClosed ((ContinuousLinearMap.toWOT (RingHom.id ℂ) H H) '' (S : Set (H →L[ℂ] H))) ↔
      Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) = (S : Set (H →L[ℂ] H)) := by
  set toWOT := ContinuousLinearMap.toWOT (RingHom.id ℂ) H H
  constructor
  · intro hclosed
    apply Set.Subset.antisymm
    · intro T hT
      have happrox : ∀ (m : ℕ) (x : Fin m → H) (ε : ℝ), ε > 0 →
          ∃ s ∈ (S : Set (H →L[ℂ] H)), ∀ i, ‖s (x i) - T (x i)‖ < ε := by
        intro m x ε hε
        have hcl := mem_closure_piLp m S T hT (WithLp.toLp 2 x)
        rw [Metric.mem_closure_iff] at hcl
        obtain ⟨w, ⟨s, hs, hw⟩, hdist⟩ := hcl ε hε
        exact ⟨s, hs, fun i => calc
          ‖s (x i) - T (x i)‖
              = ‖(diagCLM m s (WithLp.toLp 2 x) -
                  diagCLM m T (WithLp.toLp 2 x)).ofLp i‖ := by simp [diagCLM]
            _ ≤ ‖diagCLM m s (WithLp.toLp 2 x) -
                  diagCLM m T (WithLp.toLp 2 x)‖ := PiLp.norm_apply_le _ i
            _ = dist (diagCLM m T (WithLp.toLp 2 x)) w := by
                rw [← hw, dist_comm, dist_eq_norm]
            _ < ε := hdist⟩
      have hwot := mem_closure_wot S T happrox
      rw [hclosed.closure_eq] at hwot
      obtain ⟨s, hs, hTs⟩ := hwot
      have := toWOT.injective hTs; subst this; exact hs
    · exact Set.subset_centralizer_centralizer
  · intro heq; rw [heq.symm]; exact isClosed_wot_centralizer _

end VonNeumannDoubleCommutantTheorem
