import Mathlib

namespace QuillenSuslinTheorem

/-! # Quillen–Suslin theorem

The Quillen–Suslin theorem states that finitely generated projective modules over a multivariate
polynomial ring over a field are free. The proof proceeds by induction on the number of variables:

1. **Base case**: Over a field, every module is free (`Module.Free.of_divisionRing`).
2. **Inductive step**: If every f.g. projective R-module is free, then every f.g. projective
   R[X]-module is free. This combines Quillen's local-global principle with Horrocks' theorem
   (neither is currently in Mathlib).
3. **Transfer**: The Quillen–Suslin property transfers through ring isomorphisms, allowing us to
   use `MvPolynomial.finSuccEquiv` and `MvPolynomial.isEmptyRingEquiv`.
-/

universe u v

section Transfer

private noncomputable def quillenSuslinProperty_transfer
    {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) {P : Type v} [AddCommGroup P] [Module S P]
    [Module.Finite S P] [Module.Projective S P]
    (hR : ∀ (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
      [Module.Projective R M], Module.Free R M) :
    Module.Free S P := by
  letI Rmod : Module R P := Module.compHom P (e : R →+* S)
  haveI : RingHomInvPair (e : R →+* S) (e.symm : S →+* R) :=
    ⟨RingHom.ext e.symm_apply_apply, RingHom.ext e.apply_symm_apply⟩
  haveI : RingHomInvPair (e.symm : S →+* R) (e : R →+* S) :=
    ⟨RingHom.ext e.apply_symm_apply, RingHom.ext e.symm_apply_apply⟩
  let f : P →ₛₗ[(e : R →+* S)] P :=
    ⟨⟨id, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  let g : P →ₛₗ[(e.symm : S →+* R)] P :=
    ⟨⟨id, fun _ _ => rfl⟩, fun r p => by
      change r • p = e (e.symm r) • p; rw [e.apply_symm_apply]⟩
  let sleq : P ≃ₛₗ[(e : R →+* S)] P :=
    LinearEquiv.ofLinear f g (by ext; rfl) (by ext; rfl)
  haveI : Module.Projective R P := Module.Projective.of_ringEquiv e.symm sleq.symm
  haveI : Module.Finite R P := by
    obtain ⟨s, hs⟩ := (Module.finite_def (R := S)).mp ‹_›
    rw [Module.finite_def]; refine ⟨s, ?_⟩; rw [eq_top_iff]; intro p _
    exact Submodule.span_induction (p := fun x _ => x ∈ Submodule.span R (↑s : Set P))
      (fun x hx => Submodule.subset_span hx)
      (Submodule.span R (↑s : Set P)).zero_mem
      (fun x y _ _ hx hy => (Submodule.span R (↑s : Set P)).add_mem hx hy)
      (fun r x _ hx => by
        change r • x ∈ Submodule.span R (↑s : Set P)
        rw [show r • x = @HSMul.hSMul R P P (@instHSMul R P Rmod.toSMul) (e.symm r) x from by
          change r • x = e (e.symm r) • x; rw [e.apply_symm_apply]]
        exact (Submodule.span R (↑s : Set P)).smul_mem _ hx)
      (hs ▸ Submodule.mem_top)
  haveI : Module.Free R P := hR P
  exact Module.Free.of_ringEquiv e sleq

end Transfer

section InductiveStep

/-- **Quillen–Horrocks inductive step**: if every finitely generated projective module over `R` is
free, then the same holds for `Polynomial R`. This combines Quillen's local-global principle for
projective modules with Horrocks' theorem (projective modules over `R[X]` with `R` local are
free). Neither result is currently available in Mathlib. -/
private theorem quillenSuslin_polynomial_step (R : Type u)
    [CommRing R] [IsNoetherianRing R]
    (hR : ∀ (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
      [Module.Projective R M], Module.Free R M)
    (P : Type v) [AddCommGroup P] [Module (Polynomial R) P]
    [Module.Finite (Polynomial R) P] [Module.Projective (Polynomial R) P] :
    Module.Free (Polynomial R) P := by
  /- **Horrocks' theorem** (not in Mathlib): over a local Noetherian ring, every finitely
     generated projective module over `R[X]` is free. The proof shows that such modules are
     "extended" from `R` (i.e., isomorphic to `R[X] ⊗_R N`), and since `R` is local, `N` is
     automatically free, giving freeness of the polynomial module. -/
  have horrocks : ∀ (S : Type u) [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
      (Q : Type v) [AddCommGroup Q] [Module (Polynomial S) Q]
      [Module.Finite (Polynomial S) Q] [Module.Projective (Polynomial S) Q],
      Module.Free (Polynomial S) Q := by
    sorry
  /- **Quillen's local-global principle** (not in Mathlib): for every maximal ideal `𝔪` of `R`,
     the localization `R_𝔪` is a local Noetherian ring, so by Horrocks the localization `P_𝔪`
     is free over `R_𝔪[X]`. Quillen's patching theorem then yields `P ≅ R[X] ⊗_R Q` for some
     finitely generated projective `R`-module `Q`. By hypothesis `hR`, `Q` is free, hence `P`
     is free over `R[X]`. -/
  sorry

end InductiveStep

section MainProof

private noncomputable def quillenSuslin_forall (k : Type u) [Field k] :
    ∀ (n : ℕ) (P : Type v) [AddCommGroup P] [Module (MvPolynomial (Fin n) k) P]
      [Module.Finite (MvPolynomial (Fin n) k) P]
      [Module.Projective (MvPolynomial (Fin n) k) P],
      Module.Free (MvPolynomial (Fin n) k) P := by
  intro n
  induction n with
  | zero =>
    intro P _ _ _ _
    exact quillenSuslinProperty_transfer
      (MvPolynomial.isEmptyRingEquiv k (Fin 0)).symm
      (fun M _ _ _ _ => Module.Free.of_divisionRing k M)
  | succ n ih =>
    intro P _ _ _ _
    exact quillenSuslinProperty_transfer
      ((MvPolynomial.finSuccEquiv k n).toRingEquiv).symm
      (fun Q _ _ _ _ => quillenSuslin_polynomial_step
        (MvPolynomial (Fin n) k) (fun M _ _ _ _ => ih M) Q)

/-- Quillen–Suslin theorem (Serre's conjecture): finitely generated projective modules over a
multivariate polynomial ring over a field are free. -/
theorem MainTheorem (k : Type*) [Field k] (n : ℕ) (P : Type*) [AddCommGroup P]
    [Module (MvPolynomial (Fin n) k) P]
    [Module.Finite (MvPolynomial (Fin n) k) P]
    [Module.Projective (MvPolynomial (Fin n) k) P] :
    Module.Free (MvPolynomial (Fin n) k) P :=
  quillenSuslin_forall k n P

end MainProof

end QuillenSuslinTheorem
