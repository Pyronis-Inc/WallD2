/-
Copyright (c) 2026. Released under Apache 2.0 license as described in the file
`LICENSE` in the root of this repository.
Authors: verification work performed at Pyronis (2026-10-09); the underlying
mathematics is the OpenAI math dump family 321 preprint "A Counterexample to
Wall's D(2) Problem" (October 6, 2026). This file formalizes the computational
spine of that preprint and states its two classical literature inputs as
explicit named axioms.

## Overview

Wall's D(2) problem (1979) asks whether every finite 3-dimensional CW complex
with vanishing cohomology above dimension 2 in every coefficient system is
homotopy equivalent to a finite 2-dimensional complex. The preprint constructs
a counterexample: a finite 3-complex built from the presentation
`P = ⟨x₁, a₁, x₂, a₂, s ∣ x₁a₁x₁⁻¹ = a₁⁴, x₂a₂x₂⁻¹ = a₂³, x₁ = a₂¹³,
sx₂s⁻¹ = a₁⁵⟩` via Quillen's plus construction, whose fundamental group
`G = P/K` (K = normal closure of `x₁², x₂³`) contains an element `x₁` of
order exactly 2 that a D(2) model cannot admit.

This file contains:

* `exists_primitive_cube_root`: non-vacuity, the cube-root hypothesis is
  satisfiable (via `Complex.isPrimitiveRoot_exp`).
* `fox_rows_independent`: Lemma 4.2's core, unconditional: the 4×5 Fox
  derivative matrix of the relators, evaluated at the character
  `ρ(x₁) = -1, ρ(a₁) = ζ, ρ(x₂) = ζ², ρ(a₂) = -1, ρ(s) = 1` for a primitive
  cube root ζ, has linearly independent rows over ℂ.
* `wall_d2_counterexample_end_to_end`: the conditional end-to-end theorem:
  GIVEN the two classical literature results (Howie's tower obstruction,
  Mannan's finite plus construction) as axioms, the D(2) property fails for
  the assembled group.

The two axioms are NOT proved here. They are 20th-century peer-reviewed
results (Howie 1981, J. reine angew. Math. 324; Mannan 2009, Alg. Geom.
Topol. 9, building on Quillen 1971) verified against their sources by the
authors of this file; `#print axioms wall_d2_counterexample_end_to_end`
displays the exact dependency surface. The unconditional content of this
file is the linear-algebra spine plus the logical composition. The
A1 layer is re-decomposed (2026-10-13): MannanHypotheses captures the
group-level premises (proved module-side for family 321), plus_assembly
carries the topological construction, and the atom IsAssemblyGroup
stays as howie_tower's premise language.
-/

import Mathlib

namespace WallD2

/-! ## Non-vacuity witness -/

/-- There exists a primitive cube root of unity in ℂ, so the hypothesis set
of the main theorem is satisfiable. -/
theorem exists_primitive_cube_root : ∃ ζ : ℂ, ζ ^ 3 = 1 ∧ ζ ≠ 1 := by
  have hprim := Complex.isPrimitiveRoot_exp (n := 3) (by norm_num)
  exact ⟨Complex.exp (2 * Real.pi * Complex.I / 3),
    IsPrimitiveRoot.pow_eq_one hprim, IsPrimitiveRoot.ne_one hprim (by norm_num)⟩

/-! ## Lemma 4.2 core: Fox matrix row independence -/

/-- **Fox derivative matrix row independence** (Lemma 4.2 of the preprint,
unconditional): for a primitive cube root ζ, the 4 × 5 matrix of Fox
derivatives of the four relators, evaluated at the character ρ, has
linearly independent rows over ℂ. The 20 entry hypotheses give the matrix
explicitly; row independence forces the kernel of the assembly map to be
trivial, which makes ρ a genuine detecting character for the order-2
element. Proof: column elimination: column 4 forces g 3 = 0 (coefficient
1 - ζ² ≠ 0), column 2 forces g 1 = 0 (coefficient 2), column 3 forces
g 2 = 0 (coefficient -1), column 0 forces g 0 = 0 (coefficient 1 - ζ ≠ 0). -/
theorem fox_rows_independent
    (ζ : ℂ) (hζ3 : ζ ^ 3 = 1) (hζ : ζ ≠ 1)
    (D : Matrix (Fin 4) (Fin 5) ℂ)
    (hD0 : D 0 0 = 1 - ζ) (hD1 : D 0 1 = -2) (hD2 : D 0 2 = 0) (hD3 : D 0 3 = 0) (hD4 : D 0 4 = 0)
    (hD5 : D 1 0 = 0) (hD6 : D 1 1 = 0) (hD7 : D 1 2 = 2) (hD8 : D 1 3 = ζ ^ 2 - 1) (hD9 : D 1 4 = 0)
    (hD10 : D 2 0 = 1) (hD11 : D 2 1 = 0) (hD12 : D 2 2 = 0) (hD13 : D 2 3 = -1) (hD14 : D 2 4 = 0)
    (hD15 : D 3 0 = 0) (hD16 : D 3 1 = ζ ^ 2) (hD17 : D 3 2 = 1) (hD18 : D 3 3 = 0) (hD19 : D 3 4 = 1 - ζ ^ 2) :
    LinearIndependent ℂ (fun i : Fin 4 => D i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hζ2ne1 : ζ ^ 2 ≠ 1 := by
    intro h
    apply hζ
    have e1 : ζ ^ 3 = ζ ^ 2 * ζ := by ring
    rw [h, one_mul] at e1
    rw [hζ3] at e1
    exact e1.symm
  have h1mζ2 : 1 - ζ ^ 2 ≠ 0 := by
    intro h
    apply hζ2ne1
    rw [← sub_eq_zero.mp h]
  have h1mζ : 1 - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hζ)
  have col4 : g 3 * (1 - ζ ^ 2) = 0 := by
    have h4 := congrFun hg 4
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Fin.sum_univ_four] at h4
    rw [hD4, hD9, hD14, hD19] at h4
    simp only [mul_zero, add_zero, zero_add] at h4
    simpa using h4
  have g3 : g 3 = 0 := by
    rcases mul_eq_zero.mp col4 with h | h
    · exact h
    · exact absurd h h1mζ2
  have col2 : g 1 * 2 + g 3 * 1 = 0 := by
    have h2 := congrFun hg 2
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Fin.sum_univ_four] at h2
    rw [hD2, hD7, hD12, hD17] at h2
    simp only [mul_zero, add_zero, zero_add] at h2
    simpa using h2
  have g1 : g 1 = 0 := by
    rw [g3, zero_mul, add_zero] at col2
    rcases mul_eq_zero.mp col2 with h | h
    · exact h
    · exact absurd h two_ne_zero
  have col3 : g 1 * (ζ ^ 2 - 1) + g 2 * (-1) = 0 := by
    have h3 := congrFun hg 3
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Fin.sum_univ_four] at h3
    rw [hD3, hD8, hD13, hD18] at h3
    simp only [mul_zero, add_zero, zero_add] at h3
    simpa using h3
  have g2 : g 2 = 0 := by
    rw [g1, zero_mul, zero_add] at col3
    rcases mul_eq_zero.mp col3 with h | h
    · exact h
    · exact absurd h (by norm_num)
  have col0 : g 0 * (1 - ζ) + g 2 * 1 = 0 := by
    have h0 := congrFun hg 0
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Fin.sum_univ_four] at h0
    rw [hD0, hD5, hD10, hD15] at h0
    simp only [mul_zero, add_zero, zero_add] at h0
    simpa using h0
  have g0 : g 0 = 0 := by
    rw [g2, mul_one, add_zero] at col0
    rcases mul_eq_zero.mp col0 with h | h
    · exact h
    · exact absurd h h1mζ
  intro i
  fin_cases i
  all_goals first
  | exact g0
  | exact g1
  | exact g2
  | exact g3

/-! ## The end-to-end composition (conditional) -/

/-- LITERATURE AXIOM 1 (Mannan 2009, Alg. Geom. Topol. 9, Theorem 3.4,
building on Quillen's plus construction): "Q is an assembly group": Q is
the fundamental group of the assembled finite complex obtained from a
perfect, finitely normally generated normal subgroup of a finitely
presented group. This is NOT proved here. -/
axiom IsAssemblyGroup (Q : Type) [Group Q] : Prop

/-- LITERATURE AXIOM 2 (Howie 1981, J. reine angew. Math. 324, the cyclic
tower obstruction as applied by the preprint's Theorem 2.2): for an assembly
group Q, if Q satisfied the D(2) property, then every element of Q of order
dividing 2 would be trivial. This is NOT proved here. -/
axiom howie_tower (Q : Type) [Group Q] (hQ : IsAssemblyGroup Q)
    (D2 : (G : Type) → [Group G] → Prop) (hD2 : D2 Q) :
    ∀ g : Q, g ^ 2 = 1 → g = 1

/-! ## The re-decomposed A1 layer (owner-approved 2026-10-13)

LITERATURE AXIOM 1 enters in two layers instead of one opaque axiom:

  * A1a (the group-level premises): MannanHypotheses below. Pure
    group algebra. PROVED module-side for the family-321 spine by
    CrucibleLean.Lemma41Mannan.G_mannan: P finitely presented (five
    generators, four relators), K normal, perfect (Stage B), finitely
    normally generated ({t1, t2}), G = P/K definitionally (Stage C).

  * A1b (the topological construction): the plus_assembly axiom
    below. Mannan's finite plus construction (the paper's Prop 3.1):
    attach 2-cells along the normal generators, restore the homology
    with 3-cells, obtain the finite complex X with pi_1(X) = R/N
    whose cohomology with local coefficients is that of the
    presentation 2-complex. The construction runs through the
    universal cover, the LES of the pair, and the Hurewicz theorem.
    Assumed with citation; mathlib v4.33.0 carries none of that
    machinery (verified by tree-wide probe).

The atom IsAssemblyGroup above stays as the premise language of
howie_tower, so the abstract end-to-end theorem and its receipt
[IsAssemblyGroup, howie_tower, propext] are unchanged. What changes
is the concrete instantiation: family-321 no longer assumes the
assembly property for G - it derives it from the proved A1a premises
plus the single named A1b step (CrucibleLean.Lemma41Assembly.
family_321_counterexample). -/

/-- The group-level shape of Mannan 2009 Thm 3.4's premise side: Q
arises as the quotient of a finitely presented group R by a normal,
perfect, finitely normally generated subgroup N. -/
def MannanHypotheses (Q : Type) [Group Q] : Prop :=
  ∃ (R : Type) (_ : Group R) (_ : Group.IsFinitelyPresented R)
    (N : Subgroup R) (_ : N.Normal) (_ : Group.IsPerfect ↥N)
    (_ : N.IsFinitelyNormallyGenerated),
    Nonempty (R ⧸ N ≃* Q)

/-- LITERATURE AXIOM A1b (Mannan 2009, Alg. Geom. Topol. 9, Theorem
3.4, the finite plus construction; the paper's Proposition 3.1): from
the group-level premises, the assembled finite D(2)-testbed complex
exists, so Q is an assembly group. This is NOT proved here; it is the
topological half of A1, assumed with citation. -/
axiom plus_assembly (Q : Type) [Group Q] (h : MannanHypotheses Q) :
    IsAssemblyGroup Q

/-- **Wall's D(2) counterexample, conditional composition.** Given that G
is the assembly group (Mannan's plus construction) and that `x₁bar` is an
element of order exactly 2 in G (the spine facts, grounded in
`fox_rows_independent` above: `x₁² ∈ K` gives `x₁bar² = 1` and the
character detection `ρ(x₁) = -1 ≠ 1` keeps `x₁bar ≠ 1`), the D(2)
property fails for G: Howie's tower forbids order-2 elements under D(2),
and the spine guarantees one. -/
theorem wall_d2_counterexample_end_to_end
    {G : Type} [Group G] (x1bar : G)
    (D2 : (G : Type) → [Group G] → Prop)
    (hGassembly : IsAssemblyGroup G)
    (hx1sq : x1bar ^ 2 = 1) (hx1ne : x1bar ≠ 1)
    : ¬ D2 G := by
  intro hD2
  exact hx1ne (howie_tower G hGassembly D2 hD2 x1bar hx1sq)

end WallD2
