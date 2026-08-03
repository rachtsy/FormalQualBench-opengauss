import Mathlib.Topology.Algebra.PontryaginDual

namespace PontryaginDuality

open scoped Topology

/-- A topological-group isomorphism `e : A ≃ₜ* PontryaginDual (PontryaginDual A)` realizes
Pontryagin biduality if it agrees pointwise with the canonical evaluation map
`a ↦ (fun χ ↦ χ a)`. -/
def IsEvaluationIso (A : Type*) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    (e : A ≃ₜ* PontryaginDual (PontryaginDual A)) : Prop :=
  ∀ a (χ : PontryaginDual A), e a χ = χ a

private noncomputable def evalAt (A : Type*) [CommGroup A] [TopologicalSpace A]
    (a : A) : PontryaginDual (PontryaginDual A) where
  toFun := fun χ => χ a
  map_one' := map_one (M := A) (N := Circle) (1 : A →ₜ* Circle)
  map_mul' := fun _ _ => rfl
  continuous_toFun :=
    (inferInstance : ContinuousEvalConst (A →ₜ* Circle) A Circle).continuous_eval_const a

private noncomputable def evalCMH (A : Type*) [CommGroup A] [TopologicalSpace A]
    [LocallyCompactSpace A] : A →ₜ* PontryaginDual (PontryaginDual A) where
  toFun := evalAt A
  map_one' := by
    apply DFunLike.ext; intro χ; change χ 1 = 1; exact map_one χ
  map_mul' := fun a b => by
    apply DFunLike.ext; intro χ; change χ (a * b) = _; rw [map_mul χ a b]; rfl
  continuous_toFun := by
    apply ContinuousMonoidHom.continuous_of_continuous_uncurry
    change Continuous fun (p : A × PontryaginDual A) => (p.2 : A →ₜ* Circle) p.1
    exact (continuous_eval (F := A →ₜ* Circle)).comp continuous_swap

private theorem evalCMH_isHomeomorph (A : Type*) [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [LocallyCompactSpace A] [T2Space A] :
    IsHomeomorph (evalCMH A) := by
  sorry

/-- **Pontryagin duality (canonical formulation)**: every locally compact Hausdorff abelian
topological group is canonically topologically isomorphic to its double Pontryagin dual, via the
evaluation map `a ↦ (χ ↦ χ a)`. -/
theorem MainTheorem (A : Type*) [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A]
    [LocallyCompactSpace A] [T2Space A] :
    ∃ e : A ≃ₜ* PontryaginDual (PontryaginDual A), IsEvaluationIso A e :=
  ⟨ContinuousMulEquiv.mk' ((evalCMH_isHomeomorph A).homeomorph _) (map_mul (evalCMH A)),
    fun _ _ => rfl⟩

end PontryaginDuality
