--
-- Family321Spine: the concrete family-321 instantiation of the WallD2
-- axiom layer - S (the order-2 spine) and A1a (the Mannan premises)
-- kernel-proved in this package, the composition carried to the concrete
-- counterexample with NO imported algebraic premises.
--
-- Source: "A Counterexample to Wall's D(2) Problem" (OpenAI math dump,
-- family 321, October 6 2026). The chain in this package:
--   Lemma41Defs/Lemma41 (Stage A word algebra) ->
--   Lemma41StageB (K perfect, the paper's Lemma 4.1, proved) ->
--   Lemma41StageC (S, the order-2 spine) ->
--   Lemma41Mannan (A1a, the Mannan premises) ->
--   Lemma41Assembly (the bridge + the concrete counterexample).
--
-- THE LAYERS:
--   S   (Stage C): the sign character detects x1, so x1bar in G = P/K
--        has order exactly 2. The spine's own certification.
--   A1a (Mannan premises): P finitely presented, K normal, K perfect
--        (Lemma 4.1, PROVED in Lemma41StageB), K finitely normally
--        generated, G = P/K definitionally.
--   A1b plus_assembly + A2 howie_tower: WallD2's named topological
--        axioms, used as-is. The only assumptions in the composition.
--
-- RECEIPTS (live-checked in this package's build):
--   Lemma41.x1bar_order: [propext, Classical.choice, Quot.sound]
--   Lemma41.G_mannan: [propext, Classical.choice, Quot.sound]
--   Lemma41.family_321_counterexample:
--    [WallD2.IsAssemblyGroup, WallD2.howie_tower,
--     WallD2.plus_assembly, propext, Classical.choice, Quot.sound]
--
-- Fox row independence (WallD2.fox_rows_independent, the preprint's
-- Lemma 4.2) is proved unconditionally in WallD2.lean. It is the
-- separate certification of the detecting character; the spine here
-- proves the order-2 fact self-contained, so this file does not
-- depend on it (the fine DAG shows I2 as a certification leaf off
-- the path to the target).
--

import WallD2.Lemma41Assembly
import WallD2.WallD2

/-! # The spine and the premises, at a glance

The theorems below are the chain's results, restated under this
module for the reader's single entry point. See the chain files for
the full proofs and their per-node receipts. -/

namespace Lemma41Spine

open Lemma41

/-- **S**: x1bar has order exactly 2 in G = P/K (Lemma41StageC's
    result; the sign character certifies it). -/
theorem x1bar_order : orderOf (Lemma41.x1bar) = 2 := Lemma41.x1bar_order

/-- **S**: the spine's two facts (square trivial, nontrivial). -/
theorem x1bar_sq : Lemma41.x1bar ^ 2 = 1 := Lemma41.x1bar_sq
theorem x1bar_ne_one : Lemma41.x1bar ≠ 1 := Lemma41.x1bar_ne_one

/-- **A1a**: every group-level premise of Mannan 2009 Thm 3.4 holds
    for the family-321 spine group (Lemma41Mannan's discharge). -/
theorem G_mannan : WallD2.MannanHypotheses Lemma41.G :=
  Lemma41.G_mannan

/-- **The A1 bridge**: G is an assembly group (Lemma41Assembly). -/
theorem G_is_assembly : WallD2.IsAssemblyGroup Lemma41.G :=
  Lemma41.G_is_assembly

/-- **The concrete family-321 D(2) counterexample** (Lemma41Assembly):
    assuming exactly the two topological axioms (plus_assembly,
    howie_tower) and nothing algebraic, no D(2) predicate holds for
    the spine group G. -/
theorem family_321_counterexample_spine
    (D2 : (Q : Type) → [Group Q] → Prop) : ¬ D2 Lemma41.G :=
  Lemma41.family_321_counterexample D2

end Lemma41Spine
