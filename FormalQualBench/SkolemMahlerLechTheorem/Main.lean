import Mathlib.Algebra.LinearRecurrence
import Mathlib.Data.Finset.Basic

namespace SkolemMahlerLechTheorem

/-- The arithmetic progression `{a + d * n | n : ℕ}`. -/
def arithProg (a d : ℕ) : Set ℕ :=
  Set.range fun n : ℕ => a + d * n

/-- The p-adic dichotomy for linear recurrences (Skolem–Mahler–Lech, core analytic step):
for a linear recurrence of positive order over a characteristic-zero field, there exists a
modulus `d > 0` such that on each residue class modulo `d`, the solution is either eventually
identically zero or eventually never zero. This combines: (1) expressing the solution as an
exponential polynomial via roots of the characteristic polynomial, (2) embedding into a p-adic
field and choosing `d` so that root ratios become trivial on each residue class, and
(3) Strassman's theorem bounding the p-adic zeros of the resulting power series. -/
lemma padic_zero_set_dichotomy (K : Type*) [Field K] [CharZero K]
    (E : LinearRecurrence K) (u : ℕ → K) (hu : E.IsSolution u) (hord : E.order ≠ 0) :
    ∃ d : ℕ, 0 < d ∧ ∀ r : Fin d,
      (∃ N, ∀ n, N ≤ n → u (↑r + d * n) = 0) ∨
      (∃ N, ∀ n, N ≤ n → u (↑r + d * n) ≠ 0) := by
  sorry

/-- The zero set of a linear recurrence over a characteristic-zero field is eventually periodic:
there exist `N` and `d > 0` such that for all `n ≥ N`, `u n = 0 ↔ u (n + d) = 0`.
This is the core analytic content of the Skolem–Mahler–Lech theorem, requiring p-adic methods. -/
theorem zeroSet_eventuallyPeriodic (K : Type*) [Field K] [CharZero K]
    (E : LinearRecurrence K) (u : ℕ → K) (hu : E.IsSolution u) :
    ∃ (N d : ℕ), 0 < d ∧ ∀ n, N ≤ n → (u n = 0 ↔ u (n + d) = 0) := by
  by_cases hord : E.order = 0
  · refine ⟨0, 1, one_pos, fun n _ => ?_⟩
    have hzero : ∀ m, u m = 0 := by
      intro m
      have h := hu m
      rw [show m + E.order = m from by omega] at h
      haveI : IsEmpty (Fin E.order) := by rw [hord]; exact Fin.isEmpty
      rwa [Finset.sum_eq_zero (fun i _ => (IsEmpty.false i).elim)] at h
    simp [hzero]
  · by_cases hord1 : E.order = 1
    · -- Order 1: u(n+1) = c*u(n), so u(n) = c^n * u(0)
      have hrec : ∀ n, u (n + 1) = E.coeffs ⟨0, by omega⟩ * u n := by
        intro n
        have h := hu n
        rw [show n + E.order = n + 1 from by omega] at h
        rw [Finset.sum_eq_single_of_mem ⟨0, by omega⟩ (Finset.mem_univ _)
          (fun b _ hb => absurd (Fin.ext (by omega)) hb)] at h
        simpa using h
      set c := E.coeffs ⟨0, by omega⟩
      have hpow : ∀ n, u n = c ^ n * u 0 := by
        intro n; induction n with
        | zero => rw [pow_zero, one_mul]
        | succ n ih => rw [hrec, ih]; ring
      refine ⟨1, 1, one_pos, fun n hn => ?_⟩
      rw [hpow n, hpow (n + 1), mul_eq_zero, mul_eq_zero,
        pow_eq_zero_iff (show n ≠ 0 by omega),
        pow_eq_zero_iff (show n + 1 ≠ 0 by omega)]
    · -- Order ≥ 2: apply the p-adic dichotomy
      obtain ⟨d, hd, hdic⟩ := padic_zero_set_dichotomy K E u hu hord
      -- Convert dichotomy to stabilization on each residue class
      have hstab : ∀ r : Fin d, ∃ N, ∀ n, N ≤ n →
          (u (↑r + d * n) = 0 ↔ u (↑r + d * (n + 1)) = 0) := by
        intro r; rcases hdic r with ⟨N, hN⟩ | ⟨N, hN⟩
        · exact ⟨N, fun n hn => ⟨fun _ => hN (n + 1) (by omega), fun _ => hN n hn⟩⟩
        · exact ⟨N, fun n hn => iff_of_false (hN n hn) (hN (n + 1) (by omega))⟩
      choose N_r hN_r using hstab
      -- Global threshold ensuring all residue classes have stabilized
      refine ⟨d * (Finset.univ.sup N_r + 1), d, hd, fun n hn => ?_⟩
      have hmod : n % d < d := Nat.mod_lt n hd
      have hdiv_eq : n % d + d * (n / d) = n := Nat.mod_add_div n d
      have hq : N_r ⟨n % d, hmod⟩ ≤ n / d := by
        have hsup : N_r ⟨n % d, hmod⟩ ≤ Finset.univ.sup N_r :=
          Finset.le_sup (f := N_r) (Finset.mem_univ (⟨n % d, hmod⟩ : Fin d))
        have hge : Finset.univ.sup N_r + 1 ≤ n / d :=
          (Nat.le_div_iff_mul_le hd).mpr (mul_comm d _ ▸ hn)
        omega
      have h1 : u n = u (↑(⟨n % d, hmod⟩ : Fin d) + d * (n / d)) := by
        congr 1; change n = n % d + d * (n / d); omega
      have h2 : u (n + d) = u (↑(⟨n % d, hmod⟩ : Fin d) + d * (n / d + 1)) := by
        congr 1; change n + d = n % d + d * (n / d + 1); rw [mul_add, mul_one]; omega
      rw [h1, h2]; exact hN_r ⟨n % d, hmod⟩ (n / d) hq

/-- An eventually periodic subset of `ℕ` decomposes as a finite set plus a finite union of
arithmetic progressions. -/
theorem eventuallyPeriodic_decomp (S : Set ℕ)
    (N d : ℕ) (hd : 0 < d) (hper : ∀ n, N ≤ n → (n ∈ S ↔ n + d ∈ S)) :
    ∃ (s : Finset ℕ) (t : Finset (ℕ × ℕ)),
      S = (s : Set ℕ) ∪ ⋃ p ∈ (t : Set (ℕ × ℕ)), arithProg p.1 p.2 := by
  classical
  have hper_add : ∀ n, N ≤ n → ∀ k, (n ∈ S ↔ n + d * k ∈ S) := by
    intro n hn k; induction k with
    | zero => simp
    | succ k ih =>
      rw [ih]; constructor
      · intro h; rw [Nat.mul_succ, ← Nat.add_assoc]
        exact (hper _ (le_trans hn (Nat.le_add_right _ _))).mp h
      · intro h; rw [Nat.mul_succ, ← Nat.add_assoc] at h
        exact (hper _ (le_trans hn (Nat.le_add_right _ _))).mpr h
  refine ⟨(Finset.range N).filter (· ∈ S),
          ((Finset.Ico N (N + d)).filter (· ∈ S)).image (fun a => (a, d)), ?_⟩
  apply Set.eq_of_subset_of_subset
  · intro n hn_S
    by_cases h : n < N
    · exact Set.mem_union_left _ (Finset.mem_coe.mpr (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr h, hn_S⟩))
    · push_neg at h
      apply Set.mem_union_right
      simp only [Set.mem_iUnion]
      have hm_ge : N ≤ N + (n - N) % d := Nat.le_add_right N _
      have hm_lt : N + (n - N) % d < N + d :=
        Nat.add_lt_add_left (Nat.mod_lt _ hd) N
      have hm_S : N + (n - N) % d ∈ S := by
        rw [hper_add _ hm_ge ((n - N) / d)]
        convert hn_S using 1
        have := Nat.div_add_mod (n - N) d; omega
      refine ⟨(N + (n - N) % d, d), ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_filter, Finset.mem_Ico]
        exact ⟨N + (n - N) % d, ⟨⟨hm_ge, hm_lt⟩, hm_S⟩, rfl⟩
      · rw [show (N + (n - N) % d, d).1 = N + (n - N) % d from rfl,
             show (N + (n - N) % d, d).2 = d from rfl, arithProg, Set.mem_range]
        exact ⟨(n - N) / d, by have := Nat.div_add_mod (n - N) d; omega⟩
  · intro n hn
    rcases hn with h | h
    · exact (Finset.mem_filter.mp (Finset.mem_coe.mp h)).2
    · simp only [Set.mem_iUnion] at h
      obtain ⟨p, hp_mem, hp_ap⟩ := h
      simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_filter,
        Finset.mem_Ico] at hp_mem
      obtain ⟨a, ⟨⟨ha_ge, _⟩, ha_S⟩, ha_eq⟩ := hp_mem
      rw [← ha_eq] at hp_ap
      rw [show (a, d).1 = a from rfl, show (a, d).2 = d from rfl,
          arithProg, Set.mem_range] at hp_ap
      obtain ⟨k, hk⟩ := hp_ap
      have : n = a + d * k := by omega
      rw [this]; exact (hper_add a ha_ge k).mp ha_S

/-- Skolem-Mahler-Lech theorem: the zero set of a linear recurrence sequence over a characteristic
zero field is a finite union of arithmetic progressions plus a finite exceptional set. -/
theorem MainTheorem (K : Type*) [Field K] [CharZero K] (E : LinearRecurrence K) (u : ℕ → K)
    (hu : E.IsSolution u) :
    ∃ s : Finset ℕ, ∃ t : Finset (ℕ × ℕ),
      {n : ℕ | u n = 0} = (s : Set ℕ) ∪ ⋃ p ∈ (t : Set (ℕ × ℕ)), arithProg p.1 p.2 := by
  obtain ⟨N, d, hd, hper⟩ := zeroSet_eventuallyPeriodic K E u hu
  exact eventuallyPeriodic_decomp _ N d hd hper

end SkolemMahlerLechTheorem
