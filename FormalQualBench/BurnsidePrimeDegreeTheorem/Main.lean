import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.GroupAction.Jordan

namespace BurnsidePrimeDegreeTheorem

open MulAction

/--
**Burnside's theorem on transitive permutation groups of prime degree (statement)**.

A transitive permutation group of prime degree is either 2-transitive or has a normal regular
subgroup.
-/
theorem MainTheorem
    {α : Type*} [Fintype α]
    {G : Subgroup (Equiv.Perm α)}
    (htrans : IsPretransitive G α)
    (hp : (Fintype.card α).Prime) :
    IsMultiplyPretransitive G α 2 ∨
      ∃ N : Subgroup G, N.Normal ∧ IsPretransitive N α ∧
        ∀ a : α, MulAction.stabilizer N a = ⊥ := by
  haveI : Fact (Nat.Prime (Fintype.card α)) := ⟨hp⟩
  classical
  set p := Fintype.card α with hp_def
  -- Choose a Sylow p-subgroup P of G
  let P : Sylow p ↥G := default
  by_cases hN : (P : Subgroup ↥G).Normal
  · -- Case: P is normal in G → right disjunct (normal regular subgroup)
    right
    have hp' : Nat.Prime (Nat.card α) := by rwa [Nat.card_eq_fintype_card]
    haveI : IsPreprimitive (↥G) α := IsPreprimitive.of_prime_card hp'
    haveI := hN
    have hp_dvd : p ∣ Nat.card ↥G := by
      have ⟨a⟩ : Nonempty α := Fintype.card_pos_iff.mp (hp_def ▸ hp.pos)
      have h := Subgroup.index_dvd_card (stabilizer (↥G) a)
      rwa [index_stabilizer_of_transitive, Nat.card_eq_fintype_card] at h
    have hPne : (↑P : Subgroup ↥G) ≠ ⊥ := Sylow.ne_bot_of_dvd_card P hp_dvd
    -- P acts transitively via quasiprimitivity
    have hPtrans : IsPretransitive (↥(P : Subgroup ↥G)) α := by
      apply IsPreprimitive.isQuasiPreprimitive.isPretransitive_of_normal
      intro hfix
      apply hPne
      rw [eq_bot_iff]
      intro g hg
      rw [Subgroup.mem_bot]
      have hfixed : ∀ a : α, (g : Equiv.Perm α) a = a := by
        intro a
        exact (hfix ▸ Set.mem_univ a : a ∈ fixedPoints (↥(↑P : Subgroup ↥G)) α) ⟨g, hg⟩
      exact Subtype.ext (Equiv.ext hfixed)
    refine ⟨P.toSubgroup, hN, hPtrans, ?_⟩
    -- P has trivial point stabilizers (acts freely)
    intro a
    -- The stabilizer of a in P is a p-group
    set PP : Subgroup ↥G := P.toSubgroup with hPP
    have stab_pg : IsPGroup p (stabilizer (↥PP) a) := P.isPGroup'.to_subgroup _
    -- Fixed points of stabilizer ≡ |α| (mod p)
    have hmod := stab_pg.card_modEq_card_fixedPoints α
    have hcard : Nat.card α = p := by rw [Nat.card_eq_fintype_card, hp_def]
    -- p divides |fixedPoints|
    have hdvd : p ∣ Nat.card (fixedPoints (↥(stabilizer (↥PP) a)) α) := by
      rw [hcard] at hmod
      have h : p % p = Nat.card _ % p := hmod
      rw [Nat.mod_self] at h
      exact Nat.dvd_of_mod_eq_zero h.symm
    -- |fixedPoints| ≤ p
    have hle : Nat.card (fixedPoints (↥(stabilizer (↥PP) a)) α) ≤ p := by
      calc Nat.card (fixedPoints _ α) ≤ Nat.card α := Finite.card_subtype_le _
        _ = p := hcard
    -- a is a fixed point, so |fixedPoints| ≥ 1
    have hge : 1 ≤ Nat.card (fixedPoints (↥(stabilizer (↥PP) a)) α) := by
      have ha : a ∈ fixedPoints (↥(stabilizer (↥PP) a)) α := by
        rw [mem_fixedPoints]; intro ⟨m, hm⟩; exact mem_stabilizer_iff.mp hm
      haveI : Nonempty (fixedPoints (↥(stabilizer (↥PP) a)) α) := ⟨⟨a, ha⟩⟩
      exact Nat.card_pos
    -- Therefore |fixedPoints| = p
    have hfp_card : Nat.card (fixedPoints (↥(stabilizer (↥PP) a)) α) = p := by
      obtain ⟨k, hk⟩ := hdvd
      have hk1 : k ≤ 1 := by
        by_contra h; push_neg at h
        have : p * k ≥ p * 2 := Nat.mul_le_mul_left p h; omega
      interval_cases k <;> omega
    -- So fixedPoints = Set.univ (stabilizer fixes all points)
    have hfp_univ : fixedPoints (↥(stabilizer (↥PP) a)) α = Set.univ := by
      rw [← set_fintype_card_eq_univ_iff, ← Nat.card_eq_fintype_card,
        ← Nat.card_eq_fintype_card, hfp_card, hcard]
    -- By faithfulness of the permutation action, stabilizer = ⊥
    rw [hPP, eq_bot_iff]; intro g hg; rw [Subgroup.mem_bot]
    apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro x
    have : x ∈ fixedPoints (↥(stabilizer (↥PP) a)) α := hfp_univ ▸ Set.mem_univ x
    exact (mem_fixedPoints.mp this) ⟨g, hg⟩
  · -- Case: P is not normal → G is 2-transitive
    left
    -- G contains a cycle of intermediate length (2 ≤ support < p)
    have hp' : Nat.Prime (Nat.card α) := by rwa [Nat.card_eq_fintype_card]
    haveI hprim : IsPreprimitive (↥G) α := IsPreprimitive.of_prime_card hp'
    have h_cycle : ∃ g : Equiv.Perm α, g.IsCycle ∧ g ∈ G ∧
        2 ≤ g.support.card ∧ g.support.card < Fintype.card α := by
      sorry
    -- Apply Jordan's criterion for 2-pretransitivity
    obtain ⟨g, hgc, hgG, h2, hlt⟩ := h_cycle
    have htrans' := Equiv.Perm.isPretransitive_of_isCycle_mem hgc hgG
    set s := (g.support : Set α)ᶜ with hs_def
    have hs_ncard : s.ncard = Fintype.card α - g.support.card := by
      rw [hs_def, Set.ncard_compl (s := (↑g.support : Set α)),
        Nat.card_eq_fintype_card, Set.ncard_coe_finset]
    set n := s.ncard - 1 with hn_def
    have hsn : s.ncard = n + 1 := by rw [hs_ncard]; omega
    have hsn' : n + 2 < Nat.card α := by
      rw [Nat.card_eq_fintype_card, hn_def, hs_ncard]; omega
    exact hprim.is_two_pretransitive hsn hsn' htrans'

end BurnsidePrimeDegreeTheorem
