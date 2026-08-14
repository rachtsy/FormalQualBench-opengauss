import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Order
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Fraisse
import Mathlib.ModelTheory.PartialEquiv
import Mathlib.ModelTheory.Satisfiability

namespace DLOQuantifierElimination

open FirstOrder Language

/-- A theory T eliminates quantifiers if every formula is semantically equivalent
to a quantifier-free formula in all models of T. -/
def EliminatesQuantifiers {L : Language} (T : L.Theory) : Prop :=
  ∀ {α : Type*} {n : ℕ} (φ : L.BoundedFormula α n),
    ∃ ψ : L.BoundedFormula α n,
      ψ.IsQF ∧
      ∀ (M : Type*) [L.Structure M] [M ⊨ T],
        ∀ (v : α → M) (xs : Fin n → M),
          φ.Realize v xs ↔ ψ.Realize v xs

abbrev T_dlo := Language.order.dlo ∪ Language.order.nonemptyTheory

theorem nonempty_of_model (M : Type*) [Language.order.Structure M]
    [hM : M ⊨ T_dlo] : Nonempty M := by
  have := Theory.Model.mono hM (Set.subset_union_right : Language.order.nonemptyTheory ⊆ T_dlo)
  rwa [Language.model_nonemptyTheory_iff] at this

theorem model_dlo_of_T_dlo (M : Type*) [Language.order.Structure M]
    [hM : M ⊨ T_dlo] : M ⊨ Language.order.dlo :=
  Theory.Model.mono hM (Set.subset_union_left : Language.order.dlo ⊆ T_dlo)

theorem model_linearOrder_of_T_dlo (M : Type*) [Language.order.Structure M]
    [hM : M ⊨ T_dlo] : M ⊨ Language.order.linearOrderTheory := by
  haveI := model_dlo_of_T_dlo M; infer_instance

section Helpers

open BoundedFormula

/-- Finite conjunction of bounded formulas. -/
def bigConj {L : Language} {α : Type*} {n : ℕ}
    (l : List (L.BoundedFormula α n)) : L.BoundedFormula α n :=
  l.foldr (· ⊓ ·) ⊤

/-- Finite disjunction of bounded formulas. -/
def bigDisj {L : Language} {α : Type*} {n : ℕ}
    (l : List (L.BoundedFormula α n)) : L.BoundedFormula α n :=
  l.foldr (· ⊔ ·) ⊥

theorem isQF_bigConj {L : Language} {α : Type*} {n : ℕ}
    {l : List (L.BoundedFormula α n)} (h : ∀ φ ∈ l, IsQF φ) : (bigConj l).IsQF := by
  induction l with
  | nil => exact IsQF.top
  | cons φ l ih =>
    exact (h φ List.mem_cons_self).inf (ih (fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)))

theorem isQF_bigDisj {L : Language} {α : Type*} {n : ℕ}
    {l : List (L.BoundedFormula α n)} (h : ∀ φ ∈ l, IsQF φ) : (bigDisj l).IsQF := by
  induction l with
  | nil => exact isQF_bot
  | cons φ l ih =>
    exact (h φ List.mem_cons_self).sup (ih (fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)))

theorem realize_bigConj {L : Language} {α : Type*} {n : ℕ}
    {M : Type*} [L.Structure M] {l : List (L.BoundedFormula α n)}
    {v : α → M} {xs : Fin n → M} :
    (bigConj l).Realize v xs ↔ ∀ φ ∈ l, φ.Realize v xs := by
  induction l with
  | nil => simp [bigConj, realize_top]
  | cons φ l ih =>
    simp only [bigConj, List.foldr_cons, realize_inf]
    exact ⟨fun ⟨hφ, hl⟩ ψ hψ => by
        rcases List.mem_cons.mp hψ with rfl | hψ'; exact hφ; exact ih.mp hl ψ hψ',
      fun hh => ⟨hh φ List.mem_cons_self,
        ih.mpr (fun ψ hψ => hh ψ (List.mem_cons_of_mem _ hψ))⟩⟩

theorem realize_bigDisj {L : Language} {α : Type*} {n : ℕ}
    {M : Type*} [L.Structure M] {l : List (L.BoundedFormula α n)}
    {v : α → M} {xs : Fin n → M} :
    (bigDisj l).Realize v xs ↔ ∃ φ ∈ l, φ.Realize v xs := by
  induction l with
  | nil => simp [bigDisj, realize_bot]
  | cons φ l ih =>
    simp only [bigDisj, List.foldr_cons, realize_sup]
    exact ⟨fun h => by
        rcases h with hφ | hl
        · exact ⟨φ, List.mem_cons_self, hφ⟩
        · obtain ⟨ψ, hψ, hψr⟩ := ih.mp hl
          exact ⟨ψ, List.mem_cons_of_mem _ hψ, hψr⟩,
      fun ⟨ψ, hψ, hψr⟩ => by
        rcases List.mem_cons.mp hψ with rfl | hψ'
        · exact Or.inl hψr
        · exact Or.inr (ih.mpr ⟨ψ, hψ', hψr⟩)⟩

/-- In Language.order, every term is a variable. -/
theorem order_term_val {γ : Type*} (t : Language.order.Term γ) :
    ∃ i, t = Term.var i := by
  cases t with
  | var i => exact ⟨i, rfl⟩
  | func f => exact f.elim

/-- Realization of an atomic order relation `rel orderRel.le ![var a, var b]`
is equivalent to `≤` on the evaluations. -/
theorem realize_order_le {α : Type*} {n : ℕ} {M : Type*}
    [Language.order.Structure M] [Preorder M] [OrderedStructure Language.order M]
    {v : α → M} {xs : Fin n → M} (a b : α ⊕ Fin n)
    {ts : Fin 2 → Language.order.Term (α ⊕ Fin n)}
    (ha : ts 0 = Term.var a) (hb : ts 1 = Term.var b) :
    (rel (orderRel.le) ts).Realize v xs ↔
    Sum.elim v xs a ≤ Sum.elim v xs b := by
  simp only [Realize]
  have hf : (fun k : Fin 2 => (ts k).realize (Sum.elim v xs : α ⊕ Fin n → M)) =
      ![Sum.elim v xs a, Sum.elim v xs b] := by
    funext k; refine Fin.cases ?_ (fun k => ?_) k
    · simp [ha]
    · refine Fin.cases ?_ (fun k => k.elim0) k; simp [hb, Matrix.cons_val_one]
  rw [show orderRel.le = (leSymb : Language.order.Relations 2) from rfl, hf]
  exact Language.order.relMap_leSymb _

/-- QF formulas in Language.order are invariant under evaluations with the same
comparison type. This is the key model-theoretic invariance lemma. -/
theorem qf_order_invariant {α : Type*} {n : ℕ}
    {M : Type*} [Language.order.Structure M]
    {N : Type*} [Language.order.Structure N]
    (hM : M ⊨ Language.order.linearOrderTheory)
    (hN : N ⊨ Language.order.linearOrderTheory)
    {φ : Language.order.BoundedFormula α n} (hφ : φ.IsQF)
    {vM : α → M} {xsM : Fin n → M} {vN : α → N} {xsN : Fin n → N}
    (h_le : ∀ i j : α ⊕ Fin n,
      Structure.RelMap (leSymb : Language.order.Relations 2)
        ![Sum.elim vM xsM i, Sum.elim vM xsM j] ↔
      Structure.RelMap (leSymb : Language.order.Relations 2)
        ![Sum.elim vN xsN i, Sum.elim vN xsN j]) :
    φ.Realize vM xsM ↔ φ.Realize vN xsN := by
  classical
  haveI : DecidableRel (fun (a b : M) =>
    Structure.RelMap (leSymb : Language.order.Relations 2) ![a, b]) :=
    Classical.decRel _
  haveI : DecidableRel (fun (a b : N) =>
    Structure.RelMap (leSymb : Language.order.Relations 2) ![a, b]) :=
    Classical.decRel _
  letI linM := Language.order.linearOrderOfModels M
  letI linN := Language.order.linearOrderOfModels N
  have h_le' : ∀ i j : α ⊕ Fin n,
      (Sum.elim vM xsM i ≤ Sum.elim vM xsM j) ↔
      (Sum.elim vN xsN i ≤ Sum.elim vN xsN j) :=
    fun i j => h_le i j
  have h_eq : ∀ i j : α ⊕ Fin n,
      Sum.elim vM xsM i = Sum.elim vM xsM j ↔
      Sum.elim vN xsN i = Sum.elim vN xsN j := by
    intro i j
    exact ⟨fun h => le_antisymm ((h_le' i j).mp (le_of_eq h))
        ((h_le' j i).mp (le_of_eq h.symm)),
      fun h => le_antisymm ((h_le' i j).mpr (le_of_eq h))
        ((h_le' j i).mpr (le_of_eq h.symm))⟩
  induction hφ with
  | falsum => rfl
  | of_isAtomic hA =>
    induction hA with
    | equal t₁ t₂ =>
      obtain ⟨i, rfl⟩ := order_term_val t₁
      obtain ⟨j, rfl⟩ := order_term_val t₂
      simp only [realize_bdEqual, Term.realize_var]
      exact h_eq i j
    | rel R ts =>
      cases R with
      | le =>
        obtain ⟨i, hi⟩ := order_term_val (ts 0)
        obtain ⟨j, hj⟩ := order_term_val (ts 1)
        simp only [Relations.boundedFormula, Realize]
        have hM' : (fun k : Fin 2 => (ts k).realize (Sum.elim vM xsM)) =
            ![Sum.elim vM xsM i, Sum.elim vM xsM j] := by
          funext k; refine Fin.cases ?_ (fun k => ?_) k
          · simp [hi]
          · refine Fin.cases ?_ (fun k => k.elim0) k
            · simp [hj, Matrix.cons_val_one]
        have hN' : (fun k : Fin 2 => (ts k).realize (Sum.elim vN xsN)) =
            ![Sum.elim vN xsN i, Sum.elim vN xsN j] := by
          funext k; refine Fin.cases ?_ (fun k => ?_) k
          · simp [hi]
          · refine Fin.cases ?_ (fun k => k.elim0) k
            · simp [hj, Matrix.cons_val_one]
        rw [hM', hN']
        exact h_le i j
  | imp _ _ ih₁ ih₂ =>
    exact ⟨fun h hr => ih₂.mp (h (ih₁.mpr hr)),
      fun h hr => ih₂.mpr (h (ih₁.mp hr))⟩

end Helpers

open BoundedFormula in
theorem qf_exists_elim {α : Type*} {m : ℕ}
    (χ : Language.order.BoundedFormula α (m + 1)) (hχ : χ.IsQF) :
    ∃ δ : Language.order.BoundedFormula α m,
      δ.IsQF ∧ ∀ (M : Type*) [Language.order.Structure M] [M ⊨ T_dlo],
        ∀ (v : α → M) (xs : Fin m → M),
          (∃ a, χ.Realize v (Fin.snoc xs a)) ↔ δ.Realize v xs := by
  classical
  -- The proof uses the model-theoretic comparison type approach:
  -- 1. The truth of ∃y.χ depends only on the comparison type of (v, xs)
  -- 2. There are finitely many comparison types (for the relevant variables)
  -- 3. So ∃y.χ is equivalent to a finite disjunction of comparison type descriptions
  let S := χ.freeVarFinset
  -- Variable positions relevant to the formula
  let ι : Type _ := { a : α // a ∈ (S : Set α) } ⊕ Fin m
  -- Embedding of ι into the actual variable type
  let embed : ι → α ⊕ Fin m := Sum.map Subtype.val id
  -- For a pair of positions and an ordering, the comparison formula
  let cmpF : ι → ι → Ordering → Language.order.BoundedFormula α m := fun i j o =>
    match o with
    | .lt => (BoundedFormula.rel orderRel.le ![Term.var (embed j), Term.var (embed i)]).not
    | .eq => BoundedFormula.equal (Term.var (embed i)) (Term.var (embed j))
    | .gt => (BoundedFormula.rel orderRel.le ![Term.var (embed i), Term.var (embed j)]).not
  -- Description of a full comparison type
  let pairsList : List (ι × ι) := (Finset.univ : Finset (ι × ι)).toList
  let desc : (ι → ι → Ordering) → Language.order.BoundedFormula α m := fun τ =>
    bigConj (pairsList.map (fun p => cmpF p.1 p.2 (τ p.1 p.2)))
  -- A type is "good" if ∃y.χ holds for all tuples of that type in all models
  let good : (ι → ι → Ordering) → Prop := fun τ =>
    ∀ (N : Type _) [Language.order.Structure N] [N ⊨ T_dlo]
      (v' : α → N) (xs' : Fin m → N),
      (desc τ).Realize v' xs' → ∃ a, χ.Realize v' (Fin.snoc xs' a)
  -- δ = disjunction over descriptions of good types
  let goodTypes : List (ι → ι → Ordering) :=
    ((Finset.univ : Finset (ι → ι → Ordering)).filter (fun τ => good τ)).toList
  let δ := bigDisj (goodTypes.map desc)
  refine ⟨δ, ?_, fun M _ _ v xs => ⟨?_, ?_⟩⟩
  · -- δ is QF
    apply isQF_bigDisj
    intro φ hφ; simp only [List.mem_map] at hφ; obtain ⟨τ, _, rfl⟩ := hφ
    apply isQF_bigConj
    intro ψ hψ; simp only [List.mem_map] at hψ; obtain ⟨⟨i, j⟩, _, rfl⟩ := hψ
    cases τ i j <;> simp only [cmpF] <;>
      first | exact (IsAtomic.rel _ _).isQF.not | exact (IsAtomic.equal _ _).isQF
  · -- (→): ∃a. χ(v, snoc xs a) → δ(v, xs)
    intro ⟨a, ha⟩
    haveI := model_linearOrder_of_T_dlo M
    haveI := model_dlo_of_T_dlo M
    haveI := nonempty_of_model M
    -- Define the comparison type of (v, xs) on ι
    haveI : DecidableRel (fun (a b : M) =>
      Structure.RelMap (leSymb : Language.order.Relations 2) ![a, b]) := Classical.decRel _
    letI linM := Language.order.linearOrderOfModels M
    let eval : ι → M := fun i => Sum.elim v xs (embed i)
    let τ : ι → ι → Ordering := fun i j =>
      if eval i < eval j then .lt
      else if eval i = eval j then .eq
      else .gt
    -- Show desc(τ) is realized
    have hdesc : (desc τ).Realize v xs := by
      rw [realize_bigConj]
      intro ψ hψ; simp only [List.mem_map] at hψ
      obtain ⟨⟨i, j⟩, _, rfl⟩ := hψ
      change (cmpF i j (τ i j)).Realize v xs
      simp only [τ]; split_ifs with h1 h2
      · -- eval i < eval j: ¬(le(j,i))
        simp only [cmpF, realize_not]
        rw [realize_order_le (embed j) (embed i) rfl rfl]
        exact not_le.mpr h1
      · -- eval i = eval j: equal(i,j)
        simp only [cmpF]; exact h2
      · -- eval i > eval j: ¬(le(i,j))
        simp only [cmpF, realize_not]
        rw [realize_order_le (embed i) (embed j) rfl rfl]
        exact not_le.mpr (lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2))
    -- Show good(τ)
    have hgood : good τ := by
      intro N instN hN v' xs' hdesc'
      haveI := model_linearOrder_of_T_dlo N
      haveI := model_dlo_of_T_dlo N
      haveI := nonempty_of_model N
      sorry -- KEY: extension pair + QF invariance argument
    -- Conclude δ is realized
    rw [realize_bigDisj]
    exact ⟨desc τ, List.mem_map.mpr ⟨τ,
      Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood⟩), rfl⟩, hdesc⟩
  · -- (←): δ(v, xs) → ∃a. χ(v, snoc xs a)
    intro hδ
    rw [realize_bigDisj] at hδ
    obtain ⟨ψ, hψ_mem, hψ_real⟩ := hδ
    obtain ⟨τ, hτ_mem, rfl⟩ := List.mem_map.mp hψ_mem
    have hτ_good : good τ :=
      (Finset.mem_filter.mp (Finset.mem_toList.mp hτ_mem)).2
    exact hτ_good M v xs hψ_real

/-- **Quantifier Elimination for Dense Linear Orders**:
The theory of dense linear orders without endpoints (DLO)
admits quantifier elimination. -/
theorem MainTheorem :
    EliminatesQuantifiers (Language.order.dlo ∪ Language.order.nonemptyTheory) := by
  intro α n φ
  apply φ.induction_on_exists_not
  · -- QF base case: a QF formula is its own QF equivalent
    intro m ψ hqf
    exact ⟨ψ, hqf, fun M _ _ v xs => Iff.rfl⟩
  · -- Negation: if φ ≡_T χ (QF), then ¬φ ≡_T ¬χ (QF)
    intro m ψ ⟨χ, hχqf, hχ⟩
    exact ⟨∼χ, hχqf.not, fun M _ _ v xs => by
      simp only [BoundedFormula.realize_not]; exact not_congr (hχ M v xs)⟩
  · -- Existential: the core QE step
    intro m ψ ⟨χ, hχqf, hχ⟩
    obtain ⟨δ, hδqf, hδ⟩ := qf_exists_elim χ hχqf
    exact ⟨δ, hδqf, fun M inst1 inst2 v xs => by
      rw [BoundedFormula.realize_ex]
      exact (exists_congr fun a => hχ M v (Fin.snoc xs a)).trans (hδ M v xs)⟩
  · -- Semantic equivalence transfer
    intro m φ₁ φ₂ hse; constructor
    · rintro ⟨ψ, hqf, hiff⟩; refine ⟨ψ, hqf, fun M inst1 inst2 v xs => ?_⟩
      haveI := nonempty_of_model M
      exact (hse.realize_bd_iff (v := v) (xs := xs)).symm.trans (hiff M v xs)
    · rintro ⟨ψ, hqf, hiff⟩; refine ⟨ψ, hqf, fun M inst1 inst2 v xs => ?_⟩
      haveI := nonempty_of_model M
      exact (hse.realize_bd_iff (v := v) (xs := xs)).trans (hiff M v xs)

end DLOQuantifierElimination
