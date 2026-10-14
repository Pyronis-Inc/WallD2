/-
  Lemma 4.1 assembly bridge: the A1 re-decomposition closed
  (2026-10-13).

  This file composes the two halves of the re-decomposed
  LITERATURE AXIOM 1 and derives the CONCRETE family-321 D(2)
  counterexample:

    * A1a (algebra, kernel-proved): WallD2.Lemma41Mannan.
      G_mannan proves WallD2.MannanHypotheses G for the spine
      group G = P/K: P finitely presented, K normal, perfect
      (Stage B), finitely normally generated, G = P/K (Stage C).
      Receipt: the pure standard triple (the Stage B
      identification pair moduleKab/action_conj was discharged
      2026-10-13 into a kernel-proved construction).

    * A1b (topology, named axiom): WallD2.plus_assembly turns the
      premises into WallD2.IsAssemblyGroup G (Mannan 2009 Thm 3.4,
      the finite plus construction).

    * A2 (Howie's tower, named axiom): WallD2.howie_tower forbids
      order-2 elements in an assembly group satisfying D(2).

    * The spine facts (kernel-proved, Stage C, standard triple
      only): x1bar has order exactly 2 in G (x1bar_sq,
      x1bar_ne_one), grounded in Fox row independence
      (WallD2.fox_rows_independent).

  The result: family_321_counterexample is the preprint's Theorem
  3 instantiated at the concrete presentation 10. Its assumed
  surface is EXACTLY the topological layer: the named axioms
  plus_assembly and howie_tower (plus the atom IsAssemblyGroup
  their types mention). Every algebraic premise of A1 is
  kernel-proved module-side; the Stage B identification pair
  was discharged 2026-10-13, so no Lemma41 axiom rides in.

  Receipt discipline (kernel-verified, live #print axioms
  checks): family_321_counterexample carries exactly
  [WallD2.IsAssemblyGroup, WallD2.howie_tower,
   WallD2.plus_assembly, propext, Classical.choice, Quot.sound]
  and no sorryAx.
-/

import WallD2.Lemma41Mannan

namespace Lemma41

/-- **The A1 bridge**: G is an assembly group. The Mannan premises
    are proved (G_mannan, kernel); the single assumed step is the
    plus-construction topology (WallD2.plus_assembly, Mannan 2009
    Thm 3.4). -/
theorem G_is_assembly : WallD2.IsAssemblyGroup G :=
  WallD2.plus_assembly G G_mannan

/-- **The concrete family-321 D(2) counterexample**: for the spine
    group G = P/K with its concrete order-2 element x1bar, any D(2)
    predicate on groups fails for G. This instantiates the
    preprint's Theorem 3: Howie's tower (A2) forbids order-2
    elements under D(2); the spine guarantees one; the assembly
    (A1a proved + A1b assumed) connects the two. -/
theorem family_321_counterexample
    (D2 : (Q : Type) → [Group Q] → Prop) : ¬ D2 G :=
  WallD2.wall_d2_counterexample_end_to_end
    x1bar D2 G_is_assembly x1bar_sq x1bar_ne_one

end Lemma41
