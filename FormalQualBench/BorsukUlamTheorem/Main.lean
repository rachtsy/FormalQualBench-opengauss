import Mathlib

namespace BorsukUlamTheorem

noncomputable section

/-- The unit sphere `S^n` as a subtype of `ℝ^{n+1}`. -/
abbrev UnitSphere (n : ℕ) : Type :=
  {x : EuclideanSpace ℝ (Fin (n + 1)) // ‖x‖ = 1}

/-- The antipodal map `x ↦ -x` on the unit sphere. -/
def antipode {n : ℕ} : UnitSphere n → UnitSphere n :=
  fun x => ⟨-x.1, by simpa [norm_neg] using x.2⟩

private lemma continuous_antipode {n : ℕ} : Continuous (@antipode n) :=
  Continuous.subtype_mk continuous_subtype_val.neg _

private lemma antipode_antipode {n : ℕ} (x : UnitSphere n) : antipode (antipode x) = x := by
  ext i; simp [antipode]

private instance unitSphereConnected (n : ℕ) : ConnectedSpace (UnitSphere (n + 1)) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 2))) := by
    calc (1 : Cardinal) < ↑(n + 2 : ℕ) := by exact_mod_cast Nat.one_lt_succ_succ n
      _ = ↑(Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 2)))) := by
          rw [finrank_euclideanSpace, Fintype.card_fin]
      _ = Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 2))) := Module.finrank_eq_rank ..
  have hconn := isConnected_sphere hrank (0 : EuclideanSpace ℝ (Fin (n + 2)))
    (show (0 : ℝ) ≤ 1 by norm_num)
  rw [isConnected_iff_connectedSpace] at hconn
  let e : UnitSphere (n + 1) ≃ₜ ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
    (Homeomorph.refl _).subtype fun x => by simp
  exact
    { isPreconnected_univ := by
        apply e.isInducing.isPreconnected_image.mp
        simp only [Set.image_univ, EquivLike.range_eq_univ]
        exact hconn.isPreconnected_univ
      toNonempty := e.surjective.nonempty }

private lemma odd_map_zero_of_connected {n : ℕ} (g : UnitSphere (n + 1) → ℝ)
    (hg : Continuous g) (hodd : ∀ x, g (antipode x) = -g x) :
    ∃ x : UnitSphere (n + 1), g x = 0 := by
  obtain ⟨a⟩ : Nonempty (UnitSphere (n + 1)) := inferInstance
  rcases le_total 0 (g a) with h | h
  · have ha : g (antipode a) ≤ 0 := by rw [hodd]; linarith
    obtain ⟨x, _, hx⟩ := IsPreconnected.intermediate_value₂
      isPreconnected_univ (Set.mem_univ (antipode a)) (Set.mem_univ a)
      hg.continuousOn continuous_const.continuousOn ha h
    exact ⟨x, hx⟩
  · have ha : 0 ≤ g (antipode a) := by rw [hodd]; linarith
    obtain ⟨x, _, hx⟩ := IsPreconnected.intermediate_value₂
      isPreconnected_univ (Set.mem_univ a) (Set.mem_univ (antipode a))
      hg.continuousOn continuous_const.continuousOn h ha
    exact ⟨x, hx⟩

/-- Borsuk–Ulam theorem (statement): any continuous map `S^n → ℝ^n` identifies a pair of antipodal
points. -/
theorem MainTheorem (n : ℕ) :
    ∀ f : UnitSphere n → EuclideanSpace ℝ (Fin n),
      Continuous f → ∃ x : UnitSphere n, f x = f (antipode x) := by
  intro f hf
  cases n with
  | zero =>
    exact ⟨⟨EuclideanSpace.single 0 1, by simp [EuclideanSpace.norm_single]⟩,
      Subsingleton.elim _ _⟩
  | succ n =>
    cases n with
    | zero =>
      set F : UnitSphere 1 → ℝ := fun x => (f x) 0
      set G : UnitSphere 1 → ℝ := fun x => (f (antipode x)) 0
      have hcF : Continuous F := (EuclideanSpace.proj (0 : Fin 1)).continuous.comp hf
      have hcG : Continuous G :=
        (EuclideanSpace.proj (0 : Fin 1)).continuous.comp (hf.comp continuous_antipode)
      obtain ⟨a⟩ : Nonempty (UnitSphere 1) := inferInstance
      have hswap1 : F (antipode a) = G a := rfl
      have hswap2 : G (antipode a) = F a := by
        change (f (antipode (antipode a))) 0 = (f a) 0; rw [antipode_antipode]
      rcases le_total (F a) (G a) with h | h
      · obtain ⟨x, _, hx⟩ := IsPreconnected.intermediate_value₂
          isPreconnected_univ (Set.mem_univ a) (Set.mem_univ (antipode a))
          hcF.continuousOn hcG.continuousOn h (by rw [hswap2, hswap1]; exact h)
        exact ⟨x, by ext i; fin_cases i; exact hx⟩
      · obtain ⟨x, _, hx⟩ := IsPreconnected.intermediate_value₂
          isPreconnected_univ (Set.mem_univ a) (Set.mem_univ (antipode a))
          hcG.continuousOn hcF.continuousOn h (by rw [hswap2, hswap1]; exact h)
        exact ⟨x, by ext i; fin_cases i; exact hx.symm⟩
    | succ n => sorry

end

end BorsukUlamTheorem

