import Mathlib

namespace QuillenSuslinTheorem

/-! # Quillen–Suslin theorem

The Quillen–Suslin theorem states that finitely generated projective modules over a multivariate
polynomial ring over a field are free. The proof proceeds by induction on the number of variables:

1. **Base case (n=0)**: Over a field, every module is free (`Module.Free.of_divisionRing`).
2. **Base case (n=1)**: `k[X]` is a PID; over a PID, f.g. projective = f.g. torsion-free = free.
3. **Inductive step (n≥2)**: If every f.g. projective R-module is free, then every f.g. projective
   R[X]-module is free. This combines Quillen's local-global principle with Horrocks' theorem
   (neither is currently in Mathlib).
4. **Transfer**: The Quillen–Suslin property transfers through ring isomorphisms, allowing us to
   use `MvPolynomial.finSuccEquiv` and `MvPolynomial.isEmptyRingEquiv`.
-/

universe u v

section Transfer

noncomputable def quillenSuslinProperty_transfer
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
theorem quillenSuslin_polynomial_step (R : Type u)
    [CommRing R] [IsNoetherianRing R]
    (hR : ∀ (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
      [Module.Projective R M], Module.Free R M)
    (P : Type v) [AddCommGroup P] [Module (Polynomial R) P]
    [Module.Finite (Polynomial R) P] [Module.Projective (Polynomial R) P] :
    Module.Free (Polynomial R) P := by
  /- **Extension property** (Horrocks 1964 + Quillen 1976): P is "extended" from R, meaning
     P ≅ R[X] ⊗_R N for some f.g. projective R-module N. This combines Horrocks' theorem
     (the local case, where R is local) with Quillen's local-global patching principle.
     Neither result is available in Mathlib. Once N is obtained, the conclusion follows:
     N is free by `hR`, so R[X] ⊗_R N is free by `Algebra.TensorProduct.instFree`. -/
  obtain ⟨N, _, _, _, _, ⟨e⟩⟩ : ∃ (N : Type v) (_ : AddCommGroup N) (_ : Module R N)
      (_ : Module.Finite R N) (_ : Module.Projective R N),
      Nonempty (P ≃ₗ[Polynomial R] TensorProduct R (Polynomial R) N) := by
    sorry
  haveI : Module.Free R N := hR N
  haveI : Module.Free (Polynomial R) (TensorProduct R (Polynomial R) N) :=
    Algebra.TensorProduct.instFree R (Polynomial R) N
  exact Module.Free.of_equiv e.symm

end InductiveStep

section MainProof

noncomputable def quillenSuslin_forall (k : Type u) [Field k] :
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
    cases n with
    | zero =>
      exact quillenSuslinProperty_transfer
        (((MvPolynomial.finSuccEquiv k 0).toRingEquiv).trans
          (Polynomial.mapEquiv (MvPolynomial.isEmptyRingEquiv k (Fin 0)))).symm
        (fun Q _ _ _ _ => by
          haveI : Module.Flat (Polynomial k) Q := Module.Flat.of_projective
          exact Module.free_of_finite_type_torsion_free')
    | succ m =>
      exact quillenSuslinProperty_transfer
        ((MvPolynomial.finSuccEquiv k (m+1)).toRingEquiv).symm
        (fun Q _ _ _ _ => quillenSuslin_polynomial_step
          (MvPolynomial (Fin (m+1)) k) (fun M _ _ _ _ => ih M) Q)

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
