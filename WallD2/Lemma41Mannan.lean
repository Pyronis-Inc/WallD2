/-
  Mannan 2009 premises: the group-level dissection (2026-10-13).

  This file dissects LITERATURE AXIOM 1 (WallD2.lean IsAssemblyGroup,
  Mannan 2009 Thm 3.4) into what is algebra about OUR groups and
  what is genuinely the plus-construction topology.

  Mannan's theorem, in full: from a finitely presented group R, a
  normal perfect finitely-normally-generated subgroup N, one can
  build a finite complex X with fundamental group R/N and the same
  cohomology with local coefficients as the presentation 2-complex.
  The ASSEMBLY claim (that X exists) is the topological half; the
  PREMISES (that R is finitely presented, N normal, N perfect, N
  finitely normally generated, and R/N is our G) are pure group
  algebra about the family-321 presentation.

  This file proves the premises, kernel-level, with no new axioms:

    * rels_finite: the four relators form a finite set,
    * P_fp: P is a finitely presented group (instance-level, from
      Mathlib's PresentedGroup finite-relators instance),
    * K_fng: K = normalClosure {t1, t2} is finitely normally
      generated, by exhibiting the two-element generating set,
    * G_mannan: the discharge, EVERY premise proved for the
      family-321 spine: P fp, K normal (Stage B/C), K perfect
      (Stage B), K fng, and G = P/K definitionally (Stage C).

  Receipt discipline (kernel-verified, live #print axioms
  checks): the finiteness layer and G_mannan both carry the
  standard triple only (the Stage B
  identification pair moduleKab/action_conj was discharged
  2026-10-13 into a kernel-proved construction): everything
  group-level about the assembly is proved; the topological
  construction X is not claimed here and stays in the WallD2
  axiom layer.

  What this buys against WallD2.IsAssemblyGroup: the A1
  re-decomposition is now executed (owner-approved 2026-10-13).
  WallD2 defines MannanHypotheses (this file's A1a layer) and
  the named axiom plus_assembly (A1b, the plus construction);
  WallD2.Lemma41Assembly (module Lemma41Assembly.lean) composes plus_assembly with
  this file's G_mannan to prove WallD2.IsAssemblyGroup G and
  derive the concrete family_321_counterexample. This file
  remains the pure discharge layer: no topological content is
  claimed here.
-/

import WallD2.Lemma41StageC
import Mathlib.GroupTheory.FinitelyPresentedGroup
import WallD2.WallD2

namespace Lemma41
open Gen

/-! ## The finite-generator instance for the presentation -/

/-- The generator type Gen is finite: five named constructors,
    directly by the Fintype constructor on the enumerating
    Finset. -/
instance : Fintype Gen := ⟨{Gen.x1, Gen.a1, Gen.x2, Gen.a2, Gen.s}, by
  intro x; cases x <;> simp⟩

/-! ## The finiteness layer -/

/-- The four relators of the presentation (10) form a finite set. -/
theorem rels_finite : ({r1, r2, r3, r4} : Set (FreeGroup Gen)).Finite :=
  Set.Finite.ofFinset {r1, r2, r3, r4} (by intro x; simp)

/-- **The presentation is finite**: P is a finitely presented group.
    Mathlib's instance for `PresentedGroup s` under `s.Finite` needs
    the finiteness in the instance position, reached from
    `Set.Finite.to_subtype`. -/
theorem P_fp : Group.IsFinitelyPresented P :=
  haveI : Finite ↥({r1, r2, r3, r4} : Set (FreeGroup Gen)) := rels_finite.to_subtype
  inferInstance

/-- **K is finitely normally generated**: witnessed by the
    two-element set {t1, t2}, the defining set of the normal
    closure. The rfl closes the goal because K is *definitionally*
    normalClosure {t1, t2}. -/
theorem K_fng : K.IsFinitelyNormallyGenerated :=
  ⟨{t1, t2}, Set.Finite.insert t1 (Set.finite_singleton t2), rfl⟩

/-! ## The group-level assembly predicate and its discharge -/

/- The group-level shape `MannanHypotheses` is defined in WallD2
    (the re-decomposition's A1a layer, 2026-10-13); this file
    only discharges it for the family-321 spine. -/

/-- **Mannan premises discharged for the family-321 spine**: every
    algebraic premise of the assembly theorem is proved for our
    G. P is finitely presented (five generators, four relators);
    K is normal and finitely normally generated ({t1, t2} is the
    defining set); K is perfect (Stage B); and G is P/K
    definitionally (Stage C). The only remaining gap to
    IsAssemblyGroup G is the plus-construction topology, carried
    by WallD2.plus_assembly (Lemma41Assembly closes it). -/
theorem G_mannan : WallD2.MannanHypotheses G :=
  ⟨P, inferInstance, P_fp, K, K_normal, K_perfect, K_fng, ⟨MulEquiv.refl G⟩⟩

end Lemma41
