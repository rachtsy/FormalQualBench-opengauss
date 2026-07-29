import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.Filter.Ultrafilter.Basic

namespace ParisHarringtonPrinciple

open Finset Set

def RelativelyLarge (m N : ℕ) (H : Finset ℕ) : Prop :=
  H ⊆ Finset.Ico 1 (N + 1) ∧
  m ≤ H.card ∧
  ∃ hne : H.Nonempty, H.min' hne ≤ H.card

def IsHomogeneous {α β : Type*} [DecidableEq α] (k : ℕ) (H : Finset α)
    (c : Finset α → β) : Prop :=
  ∀ s ∈ H.powersetCard k, ∀ t ∈ H.powersetCard k, c s = c t

private theorem infiniteRamsey (k : ℕ) :
    ∀ (r : ℕ) (_ : 0 < r) (c : Finset ℕ → Fin r) (S : Set ℕ) (_ : S.Infinite),
    ∃ (T : Set ℕ) (d : Fin r), T ⊆ S ∧ T.Infinite ∧
      ∀ A : Finset ℕ, A.card = k → (↑A : Set ℕ) ⊆ T → c A = d := by
  induction k with
  | zero =>
    intro r _ c S hS
    exact ⟨S, c ∅, Subset.refl _, hS, fun A hA _ => by rw [Finset.card_eq_zero.mp hA]⟩
  | succ k ih =>
    intro r hr c S hS
    have step : ∀ (T : Set ℕ), T.Infinite →
        ∃ (d : Fin r) (V : Set ℕ),
          V ⊆ T \ {sInf T} ∧ V.Infinite ∧
          ∀ B : Finset ℕ, B.card = k → (↑B : Set ℕ) ⊆ V →
            c (insert (sInf T) B) = d := by
      intro T hT
      obtain ⟨V, d, hVsub, hVinf, hVmono⟩ :=
        ih r hr (fun B => c (insert (sInf T) B)) (T \ {sInf T})
          (hT.diff (Set.finite_singleton _))
      exact ⟨d, V, hVsub, hVinf, hVmono⟩
    choose d_fn V_fn hV_sub hV_inf hV_mono using step
    let seq : ℕ → {T : Set ℕ // T.Infinite} :=
      Nat.rec ⟨S, hS⟩ fun _ prev => ⟨V_fn prev.1 prev.2, hV_inf prev.1 prev.2⟩
    let elem (n : ℕ) : ℕ := sInf (seq n).1
    let color (n : ℕ) : Fin r := d_fn (seq n).1 (seq n).2
    have seq_sub : ∀ n, (seq (n + 1)).1 ⊆ (seq n).1 :=
      fun n => (hV_sub (seq n).1 (seq n).2).trans Set.diff_subset
    have seq_sub_trans : ∀ {m n}, n ≤ m → (seq m).1 ⊆ (seq n).1 := by
      intro m n h; induction h with
      | refl => exact Subset.refl _
      | step _ ih => exact (seq_sub _).trans ih
    have elem_mem : ∀ n, elem n ∈ (seq n).1 :=
      fun n => Nat.sInf_mem (seq n).2.nonempty
    have elem_lt_succ : ∀ n, elem n < elem (n + 1) := by
      intro n
      have h_in_diff := hV_sub (seq n).1 (seq n).2 (elem_mem (n + 1))
      exact lt_of_le_of_ne
        (Nat.sInf_le ((Set.mem_diff _).mp h_in_diff).1)
        (Ne.symm ((Set.mem_diff _).mp h_in_diff).2)
    have elem_strictMono : StrictMono elem := strictMono_nat_of_lt_succ elem_lt_succ
    have elem_in_future : ∀ {n m}, n < m → elem m ∈ (seq (n + 1)).1 :=
      fun hnm => seq_sub_trans (by omega : _ + 1 ≤ _) (elem_mem _)
    obtain ⟨d_star, hd_star⟩ := Finite.exists_infinite_fiber color
    have hd_inf : (color ⁻¹' {d_star}).Infinite := Set.infinite_coe_iff.mp hd_star
    let T_mono : Set ℕ := elem '' (color ⁻¹' {d_star})
    refine ⟨T_mono, d_star, ?_, ?_, ?_⟩
    · rintro x ⟨n, -, rfl⟩
      exact seq_sub_trans (Nat.zero_le n) (elem_mem n)
    · exact Set.Infinite.image (elem_strictMono.injective.injOn) hd_inf
    · intro A hAcard hAsub
      have hAne : A.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; intro h; simp [h] at hAcard
      obtain ⟨n₁, hn₁, hn₁_eq⟩ := hAsub (Finset.mem_coe.mpr (Finset.min'_mem A hAne))
      have h_elem_mem : elem n₁ ∈ A := hn₁_eq ▸ Finset.min'_mem A hAne
      set B := A.erase (elem n₁) with hB_def
      have hBcard : B.card = k := by
        rw [Finset.card_erase_of_mem h_elem_mem, hAcard]; omega
      have hBsub : (↑B : Set ℕ) ⊆ V_fn (seq n₁).1 (seq n₁).2 := by
        intro b hb
        have hb_A : b ∈ A := Finset.erase_subset _ _ hb
        have hb_ne : b ≠ elem n₁ := (Finset.mem_erase.mp hb).1
        have hb_gt : elem n₁ < b := by
          have := hn₁_eq ▸ Finset.min'_le A b hb_A
          exact lt_of_le_of_ne this (Ne.symm hb_ne)
        obtain ⟨n_b, -, rfl⟩ := hAsub (Finset.mem_coe.mpr hb_A)
        have : n₁ < n_b := by
          by_contra hle; push_neg at hle
          exact absurd (elem_strictMono.monotone hle) (not_le.mpr hb_gt)
        have : elem n_b ∈ (seq (n₁ + 1)).1 := elem_in_future this
        rwa [show (seq (n₁ + 1)).1 = V_fn (seq n₁).1 (seq n₁).2 from rfl] at this
      have h_color := hV_mono (seq n₁).1 (seq n₁).2 B hBcard hBsub
      rw [show sInf (seq n₁).1 = elem n₁ from rfl] at h_color
      rw [show A = insert (elem n₁) B from (Finset.insert_erase h_elem_mem).symm]
      rwa [show d_fn (seq n₁).1 (seq n₁).2 = color n₁ from rfl,
           show color n₁ = d_star from hn₁] at h_color

private lemma ultrafilter_fiber {r : ℕ} (U : Ultrafilter ℕ) (f : ℕ → Fin r) :
    ∃ d : Fin r, f ⁻¹' {d} ∈ U.1 := by
  by_contra h; push_neg at h
  have hmem : (⋂ d : Fin r, (f ⁻¹' {d})ᶜ) ∈ U.1 :=
    Filter.iInter_mem.mpr fun d => (U.em (f ⁻¹' {d})).resolve_left (h d)
  have hempty : (⋂ d : Fin r, (f ⁻¹' {d})ᶜ) = ∅ := by
    ext x; simp [Set.mem_iInter, Set.mem_compl_iff]
  rw [hempty] at hmem
  exact U.neBot.ne (Filter.empty_mem_iff_bot.mp hmem)

private lemma exists_finset_card_eq (S : Set ℕ) (hS : S.Infinite) (n : ℕ) :
    ∃ H : Finset ℕ, (↑H : Set ℕ) ⊆ S ∧ H.card = n := by
  induction n with
  | zero => exact ⟨∅, by simp, by simp⟩
  | succ n ihn =>
    obtain ⟨H, hHsub, hHcard⟩ := ihn
    have ⟨y, hy⟩ := (hS.diff H.finite_toSet).nonempty
    exact ⟨insert y H,
      fun z hz => by rcases Finset.mem_insert.mp hz with rfl | h
                     · exact hy.1
                     · exact hHsub (Finset.mem_coe.mpr h),
      by rw [Finset.card_insert_of_notMem (fun h => hy.2 (Finset.mem_coe.mpr h))]; omega⟩

theorem MainTheorem (k r m : ℕ) (hr : 0 < r) (hm : k ≤ m) :
    ∃ N : ℕ, ∀ (c : Finset ℕ → Fin r),
      ∃ H : Finset ℕ, RelativelyLarge m N H ∧ IsHomogeneous k H c := by
  by_contra h; push_neg at h
  choose c_bad hc_bad using h
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.cofinite
  have hU_le : (U : Filter ℕ) ≤ Filter.cofinite := Ultrafilter.of_le _
  have mem_U_inf : ∀ {S : Set ℕ}, S ∈ U.1 → S.Infinite := by
    intro S hS hfin
    have : Sᶜ ∈ U.1 := hU_le (Filter.mem_cofinite.mpr (by rwa [compl_compl]))
    have := Filter.inter_mem hS this
    rw [Set.inter_compl_self] at this
    exact U.neBot.ne (Filter.empty_mem_iff_bot.mp this)
  choose c_star hc_star using fun S => ultrafilter_fiber U (fun n => c_bad n S)
  obtain ⟨Traw, d_star, -, hTraw_inf, hTraw_mono⟩ :=
    infiniteRamsey k r hr c_star Set.univ Set.infinite_univ
  let T := Traw \ ({0} : Set ℕ)
  have hT_inf : T.Infinite := hTraw_inf.diff (Set.finite_singleton 0)
  have hT_pos : ∀ t ∈ T, 1 ≤ t := by
    intro t ht; have := ht.2; simp at this; omega
  have hT_mono : ∀ A : Finset ℕ, A.card = k → (↑A : Set ℕ) ⊆ T → c_star A = d_star :=
    fun A hA hAsub => hTraw_mono A hA (fun x hx => ((Set.mem_diff _).mp (hAsub hx)).1)
  let a := sInf T
  have ha_mem : a ∈ T := Nat.sInf_mem hT_inf.nonempty
  have ha_pos : 1 ≤ a := hT_pos a ha_mem
  let p := max m a
  obtain ⟨H₀, hH₀sub, hH₀card⟩ :=
    exists_finset_card_eq (T \ {a}) (hT_inf.diff (Set.finite_singleton a)) (p - 1)
  have ha_not : a ∉ H₀ := by
    intro h; exact ((Set.mem_diff _).mp (hH₀sub (Finset.mem_coe.mpr h))).2 rfl
  let H := insert a H₀
  have ha_in : a ∈ H := Finset.mem_insert_self a H₀
  have hH_sub : (↑H : Set ℕ) ⊆ T := by
    intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact ha_mem
    · exact Set.diff_subset (hH₀sub (Finset.mem_coe.mpr hx'))
  have hH_card : H.card = p := by
    change (insert a H₀).card = p
    rw [Finset.card_insert_of_notMem ha_not, hH₀card]
    have : 1 ≤ p := le_trans ha_pos (le_max_right m a)
    omega
  have hH_ne : H.Nonempty := ⟨a, ha_in⟩
  have hH_min : H.min' hH_ne = a :=
    le_antisymm (Finset.min'_le H a ha_in)
      (Nat.sInf_le (hH_sub (Finset.mem_coe.mpr (Finset.min'_mem H hH_ne))))
  have hH_m : m ≤ H.card := by rw [hH_card]; exact le_max_left m a
  have hH_min_le : H.min' hH_ne ≤ H.card := by
    rw [hH_min, hH_card]; exact le_max_right m a
  have hH_homo : IsHomogeneous k H c_star := by
    intro s hs t ht
    rw [hT_mono s (Finset.mem_powersetCard.mp hs).2
          (fun x hx => hH_sub ((Finset.mem_powersetCard.mp hs).1 (Finset.mem_coe.mp hx))),
        hT_mono t (Finset.mem_powersetCard.mp ht).2
          (fun x hx => hH_sub ((Finset.mem_powersetCard.mp ht).1 (Finset.mem_coe.mp hx)))]
  let good := ⋂ s ∈ H.powersetCard k, (fun n => c_bad n s) ⁻¹' {c_star s}
  have hgood_U : good ∈ U.1 :=
    (Filter.biInter_finset_mem (H.powersetCard k)).mpr fun s _ => hc_star s
  obtain ⟨N, hN_good, hN_ge⟩ : ∃ N ∈ good, H.max' hH_ne ≤ N := by
    by_contra hall; push_neg at hall
    exact (mem_U_inf hgood_U) (Set.Finite.subset (Finset.range (H.max' hH_ne)).finite_toSet
      (fun x hx => Finset.mem_coe.mpr (Finset.mem_range.mpr (hall x hx))))
  have hH_sub_Ico : H ⊆ Finset.Ico 1 (N + 1) := by
    intro x hx; rw [Finset.mem_Ico]
    exact ⟨hT_pos x (hH_sub (Finset.mem_coe.mpr hx)),
           Nat.lt_succ_of_le (le_trans (Finset.le_max' H x hx) hN_ge)⟩
  have hH_homo_bad : IsHomogeneous k H (c_bad N) := by
    intro s hs t ht
    have hs_eq : c_bad N s = c_star s :=
      (Set.mem_preimage.mp ((Set.mem_iInter₂.mp hN_good) s hs) : c_bad N s ∈ ({c_star s} : Set _))
    have ht_eq : c_bad N t = c_star t :=
      (Set.mem_preimage.mp ((Set.mem_iInter₂.mp hN_good) t ht) : c_bad N t ∈ ({c_star t} : Set _))
    rw [hs_eq, ht_eq]; exact hH_homo s hs t ht
  exact hc_bad N H ⟨hH_sub_Ico, hH_m, ⟨hH_ne, hH_min_le⟩⟩ hH_homo_bad

end ParisHarringtonPrinciple
