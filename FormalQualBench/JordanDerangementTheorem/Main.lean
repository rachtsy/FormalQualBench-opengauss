import Mathlib.Combinatorics.Derangements.Basic
import Mathlib.GroupTheory.GroupAction.Jordan

namespace JordanDerangementTheorem

open MulAction Finset

/-- Jordan's derangement theorem: a finite transitive permutation group on a nontrivial set contains
a derangement (equivalently, a fixed-point-free element). -/
theorem MainTheorem {α : Type*} [Finite α] [Nontrivial α]
    {G : Subgroup (Equiv.Perm α)} (hG : IsPretransitive G α) :
    ∃ g : Equiv.Perm α, g ∈ G ∧ g ∈ derangements α := by
  classical
  cases nonempty_fintype α
  by_contra hall
  push_neg at hall
  haveI : Nonempty α := Nontrivial.to_nonempty
  haveI : Unique (orbitRel.Quotient (↥G) α) :=
    ((pretransitive_iff_unique_quotient_of_nonempty (↥G) α).mp hG).some
  have hb := sum_card_fixedBy_eq_card_orbits_mul_card_group (↥G) α
  rw [Fintype.card_unique, one_mul] at hb
  have hlt : ∑ _ : ↥G, (1 : ℕ) < ∑ g : ↥G, Fintype.card ↑(fixedBy α g) := by
    apply sum_lt_sum
    · intro ⟨g, hg⟩ _
      have := hall g hg
      simp only [derangements, Set.mem_setOf_eq, ne_eq, not_forall, not_not] at this
      obtain ⟨a, ha⟩ := this
      exact Fintype.card_pos_iff.mpr ⟨⟨a, ha⟩⟩
    · refine ⟨1, mem_univ _, ?_⟩
      have : Fintype.card ↑(fixedBy α (1 : ↥G)) = Fintype.card α :=
        Fintype.card_congr
          ((Equiv.setCongr (fixedBy_one_eq_univ α ↥G)).trans (Equiv.Set.univ α))
      rw [this]
      exact Fintype.one_lt_card
  simp only [sum_const, card_univ, smul_eq_mul, mul_one] at hlt
  omega

end JordanDerangementTheorem
