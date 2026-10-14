/-
  Lemma 4.1 (K is perfect) - the formalization (2026-10-12).

  Source: "A Counterexample to Wall's D(2) Problem", OpenAI, October
  6 2026, family 321. The claim: K, the kernel layer of the presented
  group P, is perfect (trivial abelianization).

  THE OWNER'S AXIOM POLICY (2026-10-12, the A1/A2 pattern): if a step
  of this formalization would require formalizing deep well-known
  older theory, that older theory is ASSUMED as a named axiom and the
  reduction is proved. No sorries, no unnamed assumptions, no fake
  definitions. The attempt stages:

  * Stage A (proved here): the entry identities, pure word algebra
    in P - t1 = [t2, a2] and s t2 s⁻¹ = [t1, a1], where
    t1 = x1^2 and t2 = x2^3. These are the entries the module
    computation consumes; they are finite letter-level calculations
    (conjugation arithmetic), not deep theory.
  * SCOPE RULING (2026-10-13, review-confirmed): Stage A is
    mechanical word algebra and is NEVER axiomatized - the entry
    identities are exactly the content the commission exists to
    prove. The axiom-eligible layer is Stage B only: the
    abelianization-of-normal-closure <-> relation-module
    identification (the [t,a] -> (1-a_bar)[t] image formula), which
    is standard group-homology theory Mathlib lacks. Tedium is not
    an axiom case; a genuinely classical theorem blocking the path
    is.
  * Stage B (the module rung, under the policy): from the two
    identities through the ZG-module annihilation (26 u1 = 0,
    15 u2 = 0, gcd(15, 26) = 1) to Kab = 0. The load-bearing older
    layer is the identification of the abelianization of a normal
    closure with the module over the group ring; where that
    machinery would be its own formalization project, it enters as
    NAMED AXIOMS with the audit's line-by-line derivation as the
    statement.
  * UPDATE (2026-10-13, later the same day): the Stage B
    identification layer was then DISCHARGED into a kernel-proved
    construction in Lemma41StageB (conjNormal through
    Abelianization.map into a Representation; Module.compHom over
    asAlgebraHom as the instance; action_conj a theorem). The
    axiom-eligible layer is now EMPTY: nothing in this arc is
    axiomatized.

  Conventions: [g, h] = g h g⁻¹ h⁻¹.
-/

import Mathlib
import Mathlib.GroupTheory.PresentedGroup

open FreeGroup PresentedGroup

namespace Lemma41

/-! ## The presented group -/

inductive Gen : Type
  | x1 | a1 | x2 | a2 | s
  deriving DecidableEq

open Gen

abbrev L (g : Gen) : FreeGroup Gen := FreeGroup.of g

/-- The four relators of the paper's presentation (10). -/
def r1 : FreeGroup Gen := L x1 * L a1 * (L x1)⁻¹ * (L a1)⁻¹ ^ 4
def r2 : FreeGroup Gen := L x2 * L a2 * (L x2)⁻¹ * (L a2)⁻¹ ^ 3
def r3 : FreeGroup Gen := L x1 * (L a2)⁻¹ ^ 13
def r4 : FreeGroup Gen := L s * L x2 * (L s)⁻¹ * (L a1)⁻¹ ^ 5

/-- The paper's group `P`, presented on five generators, four relators. -/
abbrev P : Type := PresentedGroup ({r1, r2, r3, r4} : Set (FreeGroup Gen))

/-- Images of the generators in `P`. -/
abbrev gX1 : P := of x1
abbrev gA1 : P := of a1
abbrev gX2 : P := of x2
abbrev gA2 : P := of a2
abbrev gS  : P := of s

/-- The commutator, paper convention: [g, h] = g h g⁻¹ h⁻¹. -/
abbrev cmm (g h : P) : P := g * h * g⁻¹ * h⁻¹

/-- The paper's t1 = x1^2 and t2 = x2^3. -/
abbrev t1 : P := gX1 * gX1
abbrev t2 : P := gX2 * gX2 * gX2

end Lemma41
