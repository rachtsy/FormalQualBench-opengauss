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
    have hp' : Nat.Prime (Nat.card α) := by rwa [Nat.card_eq_fintype_card]
    haveI hprim : IsPreprimitive (↥G) α := IsPreprimitive.of_prime_card hp'
    haveI := htrans
    by_cases h_cycle : ∃ g : Equiv.Perm α, g.IsCycle ∧ g ∈ G ∧
        2 ≤ g.support.card ∧ g.support.card < Fintype.card α
    · obtain ⟨g, hgc, hgG, h2, hlt⟩ := h_cycle
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
    · -- No intermediate cycle exists.
      -- For p ≥ 7, proving 2-transitivity requires character-theoretic methods.
      -- For p ∈ {2, 3, 5}, the no-intermediate-cycle hypothesis is vacuous.
      by_cases hp7 : 7 ≤ p
      · -- p ≥ 7: 2-transitivity via character theory (not available in Mathlib)
        sorry
      · -- p ∈ {2, 3, 5}: derive contradiction
        push_neg at hp7
        exfalso
        have hp235 : p = 2 ∨ p = 3 ∨ p = 5 := by
          have := hp.two_le
          rcases show p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 from by omega
            with h | h | h | h | h
          · left; exact h
          · right; left; exact h
          · exfalso; rw [h] at hp; revert hp; decide
          · right; right; exact h
          · exfalso; rw [h] at hp; revert hp; decide
        -- |G| divides p! (G ≤ S_p, Lagrange)
        have hGdvd : Nat.card ↥G ∣ p.factorial := by
          have h := Subgroup.card_subgroup_dvd_card G
          rw [Nat.card_perm] at h
          rwa [show Nat.card α = p from Nat.card_eq_fintype_card] at h
        -- p | |G| (transitive action on p points)
        have hp_dvd : p ∣ Nat.card ↥G := by
          have ⟨a⟩ : Nonempty α := Fintype.card_pos_iff.mp (hp_def ▸ hp.pos)
          have h := Subgroup.index_dvd_card (stabilizer (↥G) a)
          rwa [index_stabilizer_of_transitive, Nat.card_eq_fintype_card] at h
        -- p! = p * (p-1)!
        have hfact : p.factorial = p * (p - 1).factorial := by
          cases hp_eq : p with
          | zero => exact absurd (hp_eq ▸ hp) (by omega)
          | succ n => simp [Nat.factorial_succ]
        -- |P| = p (coprimality: |P| is a p-power dividing p!, gcd(p,(p-1)!) = 1)
        have hPcard : Nat.card ↥(P : Subgroup ↥G) = p := by
          apply Nat.dvd_antisymm
          · obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
            rw [hk]
            have : p ^ k ∣ p.factorial :=
              hk ▸ (Subgroup.card_subgroup_dvd_card (P : Subgroup ↥G)).trans hGdvd
            rw [hfact] at this
            exact ((hp.coprime_factorial_of_lt
              (Nat.sub_lt hp.pos Nat.one_pos)).pow_left k).dvd_of_dvd_mul_right this
          · exact P.dvd_card_of_dvd_card hp_dvd
        -- P.index | (p-1)! and n_p | (p-1)!
        have hIdxdvd : (P : Subgroup ↥G).index ∣ (p - 1).factorial := by
          have h1 : p * (P : Subgroup ↥G).index = Nat.card ↥G := by
            have := Subgroup.card_mul_index (P : Subgroup ↥G)
            rwa [hPcard] at this
          exact (Nat.mul_dvd_mul_iff_left hp.pos).mp (by rw [h1, ← hfact]; exact hGdvd)
        have h_np_dvd : Nat.card (Sylow p ↥G) ∣ (p - 1).factorial :=
          dvd_trans (Sylow.card_dvd_index P) hIdxdvd
        have h_mod := card_sylow_modEq_one p ↥G
        -- Case split on p ∈ {2, 3, 5}
        rcases hp235 with h | h | h
        · -- p = 2: n_2 | 1! = 1 → P normal → contradiction with hN
          exact hN (by
            haveI : Subsingleton (Sylow p ↥G) := Finite.card_le_one_iff_subsingleton.mp
              (Nat.le_of_dvd (by norm_num)
                (show Nat.card (Sylow p ↥G) ∣ 1 from by
                  rwa [show (p - 1).factorial = 1 from by rw [h]; norm_num [Nat.factorial]]
                    at h_np_dvd))
            exact Sylow.normal_of_subsingleton P)
        · -- p = 3: n_3 | 2! = 2, n_3 ≡ 1 mod 3 → n_3 = 1 → P normal
          exact hN (by
            haveI : Subsingleton (Sylow p ↥G) := by
              rw [← Finite.card_le_one_iff_subsingleton]
              have hle : Nat.card (Sylow p ↥G) ≤ 2 := Nat.le_of_dvd (by norm_num)
                (show Nat.card (Sylow p ↥G) ∣ 2 from by
                  rwa [show (p - 1).factorial = 2 from by rw [h]; norm_num [Nat.factorial]]
                    at h_np_dvd)
              rw [Nat.ModEq, Nat.mod_eq_of_lt (show 1 < p from by rw [h]; omega)] at h_mod
              suffices ∀ n, n ≤ 2 → n % 3 = 1 → n ≤ 1 by
                exact this _ hle (by rw [show (3 : ℕ) = p from h.symm]; exact h_mod)
              intro n; omega
            exact Sylow.normal_of_subsingleton P)
        · -- p = 5: Cauchy gives a 3-cycle, contradicting h_cycle
          -- Show 3 | |G| via Sylow counting: n_5 = 6
          have h3dvd : 3 ∣ Nat.card ↥G := by
            have hgt1 : 1 < Nat.card (Sylow p ↥G) := by
              by_contra hle; push_neg at hle; exact hN (by
                haveI := Finite.card_le_one_iff_subsingleton.mp hle
                exact Sylow.normal_of_subsingleton P)
            have h_np_dvd' : Nat.card (Sylow p ↥G) ∣ 24 := by
              rwa [show (p - 1).factorial = 24 from by rw [h]; norm_num [Nat.factorial]]
                at h_np_dvd
            have hle : Nat.card (Sylow p ↥G) ≤ 24 :=
              Nat.le_of_dvd (by norm_num) h_np_dvd'
            rw [Nat.ModEq, Nat.mod_eq_of_lt (show 1 < p from by rw [h]; omega)] at h_mod
            have h5 : Nat.card (Sylow p ↥G) % 5 = 1 := by
              rw [show (5 : ℕ) = p from h.symm]; exact h_mod
            have hn6 : Nat.card (Sylow p ↥G) = 6 := by
              clear h_mod h_np_dvd hIdxdvd hGdvd hfact hPcard hp_dvd
              interval_cases (Nat.card (Sylow p ↥G)) <;> omega
            exact dvd_trans (show (3 : ℕ) ∣ 6 from by norm_num)
              (dvd_trans (hn6 ▸ Sylow.card_dvd_index P) (Subgroup.index_dvd_card _))
          -- Cauchy: ∃ element of order 3 in G
          haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
          obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥G) 3 h3dvd
          -- Order preserved by subgroup inclusion
          have hord : orderOf (x : Equiv.Perm α) = 3 :=
            (Subgroup.orderOf_coe x).trans hx
          -- Element is a cycle (|α| = 5 < 6 = 2·3)
          have hcyc : (x : Equiv.Perm α).IsCycle :=
            Equiv.Perm.isCycle_of_prime_order'
              (by rw [hord]; exact Fact.out)
              (by rw [hord, ← hp_def, h]; norm_num)
          -- support = orderOf = 3, giving a 3-cycle with 2 ≤ 3 < 5
          have hsupp : (x : Equiv.Perm α).support.card = 3 :=
            hcyc.orderOf.symm.trans hord
          exact h_cycle ⟨_, hcyc, x.property,
            by rw [hsupp]; norm_num,
            by rw [hsupp, ← hp_def, h]; norm_num⟩

end BurnsidePrimeDegreeTheorem
