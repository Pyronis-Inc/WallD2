/-/
  Lemma 4.1 Stage A: COMPLETE (2026-10-13). Both entry identities
  are kernel-proved here, sorry-free, receipts verified (the
  standard axiom triple only: propext, Classical.choice,
  Quot.sound). The DEFINITIONS live in Lemma41Defs. The proof
  ladder: rungs 1-2 (relator-direct, x1 = a2^13 and
  x2 a2 x2^-1 = a2^3), the geometric conjugation ladders (conj by
  x2^n triples the a2-exponent; conj by x1^n quadruples the
  a1-exponent; rung2/rung6 fire INSIDE the Pm image at every step:
  the corresponding free-word identities are FALSE, the trap the
  early attempts fell into), rungs 5-6 (relator-direct,
  s x2 s^-1 = a1^5 and x1 a1 x1^-1 = a1^4), and the two
  assemblies (t1 = a2^26 = cmm t2 gA2; s t2 s^-1 = a1^15 =
  cmm t1 gA1). Session import is now SAFE: nothing here carries
  a sorry.
-/

import WallD2.Lemma41Defs
import Mathlib.GroupTheory.PresentedGroup

open FreeGroup PresentedGroup

namespace Lemma41

open Gen

/-- Local abbreviation for the presentation map, identical to the
    REPL-session form so proofs carry over verbatim. -/
abbrev Pm := mk ({r1, r2, r3, r4} : Set (FreeGroup Gen))

/-! ## Stage A: the entry identities (word algebra, proved) -/

/-- Rung 1 (kernel-proved 2026-10-12, the assault's first landing):
    x1 = a2^13 in P, straight from relator r3. -/
theorem rung1_x1_eq_a2pow13 :
    (gX1 : P) = (mk ({r1, r2, r3, r4} : Set (FreeGroup Gen))) (L a2 ^ 13) := by
  refine (mk_eq_mk_of_mul_inv_mem ?_)
  show L x1 * (L a2 ^ 13)⁻¹ ∈ ({r1, r2, r3, r4} : Set (FreeGroup Gen))
  rw [show L x1 * (L a2 ^ 13)⁻¹ = r3 from rfl]
  decide

theorem rung2 : (mk ({r1, r2, r3, r4} : Set (FreeGroup Gen))) (L x2 * L a2 * (L x2)⁻¹)
    = (mk ({r1, r2, r3, r4} : Set (FreeGroup Gen))) (L a2 ^ 3) := by
  refine (mk_eq_mk_of_mul_inv_mem ?_)
  show L x2 * L a2 * (L x2)⁻¹ * (L a2 ^ 3)⁻¹ ∈ ({r1, r2, r3, r4} : Set (FreeGroup Gen))
  rw [show L x2 * L a2 * (L x2)⁻¹ * (L a2 ^ 3)⁻¹ = r2 from rfl]
  decide

/-- Rung 3, the geometric conjugation ladder. The m-parameterized
    form is what makes the induction close: conj by x2^n sends a2^m
    to a2^(3^n * m) IN P (rung2 fires inside the Pm image at every
    step; the corresponding free-word identity is FALSE, which is
    why key2-style group normalization could never close). -/
theorem conj_pow_geometric (n : ℕ) : ∀ (m : ℕ),
    Pm (L x2 ^ n * L a2 ^ m * (L x2 ^ n)⁻¹) = Pm (L a2 ^ (3 ^ n * m)) := by
  induction n with
  | zero => intro m; simp
  | succ n ih =>
    intro m
    have peel : L x2 ^ (n + 1) * L a2 ^ m * (L x2 ^ (n + 1))⁻¹
        = L x2 ^ n * (L x2 * L a2 ^ m * (L x2)⁻¹) * (L x2 ^ n)⁻¹ := by
      rw [pow_succ]; group
    have mid : Pm (L x2 * L a2 ^ m * (L x2)⁻¹) = Pm (L a2 ^ (3 * m)) := by
      rw [← conj_pow, _root_.map_pow Pm, rung2, ← _root_.map_pow Pm, pow_mul]
    rw [peel, _root_.map_mul Pm, _root_.map_mul Pm, mid,
        ← _root_.map_mul Pm, ← _root_.map_mul Pm, ih (3 * m),
        show 3 ^ (n + 1) * m = 3 ^ n * (3 * m) from by
          rw [pow_succ]; exact Nat.mul_assoc _ _ _]

/-- Rung 3: x2^3 a2 x2^-3 = a2^27 in P (3^3 = 27, m = 1). -/
theorem rung3 : Pm (L x2 ^ 3 * L a2 * (L x2 ^ 3)⁻¹) = Pm (L a2 ^ 27) := by
  have h := conj_pow_geometric 3 1
  rw [pow_one, show 3 ^ 3 * 1 = 27 from by norm_num] at h
  exact h


theorem id1_target : t1 = cmm t2 gA2 := by
  have hga2 : (gA2 : P) = Pm (L a2) := rfl
  have ht1 : t1 = Pm (L a2 ^ 26) := by
    show gX1 * gX1 = Pm (L a2 ^ 26)
    rw [rung1_x1_eq_a2pow13, ← _root_.map_mul Pm,
        show L a2 ^ 13 * L a2 ^ 13 = L a2 ^ 26 from by rw [← pow_add]]
  have ht2 : t2 = Pm (L x2 ^ 3) := by
    show Pm (L x2) * Pm (L x2) * Pm (L x2) = Pm (L x2 ^ 3)
    rw [← _root_.map_mul Pm, ← _root_.map_mul Pm]
    congr 1
  have hc : t2 * gA2 * t2⁻¹ = Pm (L a2 ^ 27) := by
    rw [ht2, hga2, ← _root_.map_mul Pm, ← _root_.map_inv Pm,
        ← _root_.map_mul Pm, rung3]
  have hfin : cmm t2 gA2 = Pm (L a2 ^ 26) := by
    show t2 * gA2 * t2⁻¹ * gA2⁻¹ = Pm (L a2 ^ 26)
    rw [hc, hga2, ← _root_.map_inv Pm, ← _root_.map_mul Pm]
    have word : L a2 ^ 27 * (L a2)⁻¹ = L a2 ^ 26 := by
      rw [pow_succ, mul_inv_cancel_right]
    rw [word]
  calc t1 = Pm (L a2 ^ 26) := ht1
    _ = cmm t2 gA2 := hfin.symm

theorem rung5 : Pm (L s * L x2 * (L s)⁻¹) = Pm (L a1 ^ 5) := by
  refine (mk_eq_mk_of_mul_inv_mem ?_)
  show L s * L x2 * (L s)⁻¹ * (L a1 ^ 5)⁻¹ ∈ ({r1, r2, r3, r4} : Set (FreeGroup Gen))
  rw [show L s * L x2 * (L s)⁻¹ * (L a1 ^ 5)⁻¹ = r4 from rfl]
  decide

theorem rung6 : Pm (L x1 * L a1 * (L x1)⁻¹) = Pm (L a1 ^ 4) := by
  refine (mk_eq_mk_of_mul_inv_mem ?_)
  show L x1 * L a1 * (L x1)⁻¹ * (L a1 ^ 4)⁻¹ ∈ ({r1, r2, r3, r4} : Set (FreeGroup Gen))
  rw [show L x1 * L a1 * (L x1)⁻¹ * (L a1 ^ 4)⁻¹ = r1 from rfl]
  decide

theorem conj_pow_geometric_a1 (n : ℕ) : ∀ (m : ℕ),
    Pm (L x1 ^ n * L a1 ^ m * (L x1 ^ n)⁻¹) = Pm (L a1 ^ (4 ^ n * m)) := by
  induction n with
  | zero => intro m; simp
  | succ n ih =>
    intro m
    have peel : L x1 ^ (n + 1) * L a1 ^ m * (L x1 ^ (n + 1))⁻¹
        = L x1 ^ n * (L x1 * L a1 ^ m * (L x1)⁻¹) * (L x1 ^ n)⁻¹ := by
      rw [pow_succ]; group
    have mid : Pm (L x1 * L a1 ^ m * (L x1)⁻¹) = Pm (L a1 ^ (4 * m)) := by
      rw [← conj_pow, _root_.map_pow Pm, rung6, ← _root_.map_pow Pm, pow_mul]
    rw [peel, _root_.map_mul Pm, _root_.map_mul Pm, mid,
        ← _root_.map_mul Pm, ← _root_.map_mul Pm, ih (4 * m),
        show 4 ^ (n + 1) * m = 4 ^ n * (4 * m) from by
          rw [pow_succ]; exact Nat.mul_assoc _ _ _]

/-- Rung 7 (word algebra, proved): t1 commutes with a2 in P (both
    are powers of a2 in P: t1 = a2^26). This is the word fact behind
    "a2 fixes u1" in the Stage-B module rung. -/
theorem rung7_comm_t1_a2 : cmm t1 gA2 = 1 := by
  have ht1 : t1 = Pm (L a2 ^ 26) := by
    show gX1 * gX1 = Pm (L a2 ^ 26)
    rw [rung1_x1_eq_a2pow13, ← _root_.map_mul Pm,
        show L a2 ^ 13 * L a2 ^ 13 = L a2 ^ 26 from by rw [← pow_add]]
  have hga2 : (gA2 : P) = Pm (L a2) := rfl
  have w : L a2 ^ 26 * L a2 * (L a2 ^ 26)⁻¹ = L a2 := by group
  have hcon : t1 * gA2 * t1⁻¹ = gA2 := by
    rw [ht1, hga2, ← _root_.map_inv Pm, ← _root_.map_mul Pm,
        ← _root_.map_mul Pm, w]
  show t1 * gA2 * t1⁻¹ * gA2⁻¹ = 1
  rw [hcon]
  group

/-- Rung 8 (word algebra, proved): st2s^-1 commutes with a1 in P
    (both are powers of a1: st2s^-1 = a1^15). The word fact behind
    "a1 fixes s*u2" in the Stage-B module rung. -/
theorem rung8_comm_st2_a1 : cmm (gS * t2 * gS⁻¹) gA1 = 1 := by
  have ha1 : (gA1 : P) = Pm (L a1) := rfl
  have hs0 : (gS : P) = Pm (L s) := rfl
  have hst2 : gS * t2 * gS⁻¹ = Pm (L a1 ^ 15) := by
    have ht2 : t2 = Pm (L x2 ^ 3) := by
      show Pm (L x2) * Pm (L x2) * Pm (L x2) = Pm (L x2 ^ 3)
      rw [← _root_.map_mul Pm, ← _root_.map_mul Pm]
      congr 1
    rw [ht2, hs0, ← _root_.map_mul Pm, ← _root_.map_inv Pm,
        ← _root_.map_mul Pm]
    rw [show L s * L x2 ^ 3 * (L s)⁻¹ = (L s * L x2 * (L s)⁻¹) ^ 3 from conj_pow.symm,
        _root_.map_pow Pm, rung5, ← _root_.map_pow Pm]
    have cube : (L a1 ^ 5) ^ 3 = L a1 ^ 15 := by
      rw [show 15 = 5 * 3 from by norm_num, pow_mul]
    rw [cube]
  have w : L a1 ^ 15 * L a1 * (L a1 ^ 15)⁻¹ = L a1 := by group
  have hcon : (gS * t2 * gS⁻¹) * gA1 * (gS * t2 * gS⁻¹)⁻¹ = gA1 := by
    rw [hst2, ha1, ← _root_.map_inv Pm, ← _root_.map_mul Pm,
        ← _root_.map_mul Pm, w]
  show (gS * t2 * gS⁻¹) * gA1 * (gS * t2 * gS⁻¹)⁻¹ * gA1⁻¹ = 1
  rw [hcon]
  group

theorem id2_target : gS * t2 * gS⁻¹ = cmm t1 gA1 := by
  have hs0 : (gS : P) = Pm (L s) := rfl
  have ha1 : (gA1 : P) = Pm (L a1) := rfl
  have ht2 : t2 = Pm (L x2 ^ 3) := by
    show Pm (L x2) * Pm (L x2) * Pm (L x2) = Pm (L x2 ^ 3)
    rw [← _root_.map_mul Pm, ← _root_.map_mul Pm]
    congr 1
  have hs : gS * t2 * gS⁻¹ = Pm (L a1 ^ 15) := by
    rw [ht2, hs0, ← _root_.map_mul Pm, ← _root_.map_inv Pm,
        ← _root_.map_mul Pm]
    rw [show L s * L x2 ^ 3 * (L s)⁻¹ = (L s * L x2 * (L s)⁻¹) ^ 3 from conj_pow.symm,
        _root_.map_pow Pm, rung5, ← _root_.map_pow Pm]
    have cube : (L a1 ^ 5) ^ 3 = L a1 ^ 15 := by
      rw [show 15 = 5 * 3 from by norm_num, pow_mul]
    rw [cube]
  have ht1w : t1 = Pm (L x1 ^ 2) := by
    show Pm (L x1) * Pm (L x1) = Pm (L x1 ^ 2)
    rw [← _root_.map_mul Pm]
    congr 1
  have hc : t1 * gA1 * t1⁻¹ = Pm (L a1 ^ 16) := by
    rw [ht1w, ha1, ← _root_.map_mul Pm, ← _root_.map_inv Pm,
        ← _root_.map_mul Pm, ← pow_one (L a1), conj_pow_geometric_a1 2 1]
    norm_num
  have hfin : cmm t1 gA1 = Pm (L a1 ^ 15) := by
    show t1 * gA1 * t1⁻¹ * gA1⁻¹ = Pm (L a1 ^ 15)
    rw [hc, ha1, ← _root_.map_inv Pm, ← _root_.map_mul Pm]
    have word : L a1 ^ 16 * (L a1)⁻¹ = L a1 ^ 15 := by
      rw [pow_succ, mul_inv_cancel_right]
    rw [word]
  calc gS * t2 * gS⁻¹ = Pm (L a1 ^ 15) := hs
    _ = cmm t1 gA1 := hfin.symm


end Lemma41
