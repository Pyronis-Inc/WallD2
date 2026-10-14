/-
  Lemma 4.1 Stage B: K IS PERFECT (2026-10-13).

  The normal closure K of {t1, t2} in the presented group P is a
  perfect group. The proof runs the classical module-theoretic
  argument that AUDIT.md records under "Lemma 4.1 (K perfect),
  hand-verified module computation":

    * Kab, the abelianization of K, is a module over the
      integral group ring ZP (kernel-proved below: the
      conjugation representation via MulAut.conjNormal and
      Abelianization.map, transported by the mathlib
      representation-module bridge),
    * the ZP-action is conjugation (kernel-proved below:
      action_conj is a theorem, not an axiom),
    * the two entry identities of Stage A give
      u1 = (1-a2)u2 and s u2 = (1-a1)u1,
    * t1 = a2^26 and st2s^-1 = a1^15 (Stage A rungs 7-8, word
      algebra) give (1-a2^26)u2 = 0 and (1-a1^15)u1 = 0,
    * geometric-sum telescoping plus Bezout 1 = 7*15 - 4*26
      annihilates u1 and u2 (kernel-proved, no axioms),
    * closure induction puts every element of Kab in the span of
      u1, u2, so Kab = 0, so K equals its own commutator subgroup:
      K is perfect.

  AXIOM POLICY AFTER THE DISCHARGE (2026-10-13, owner-approved):
  this file is now AXIOM-FREE. The former identification pair
  (moduleKab, action_conj) is DISCHARGED by the kernel-proved
  construction below: the conjugation action of P on the
  abelianization of K, built from MulAut.conjNormal (mathlib's
  conjugation automorphism, K.Normal supplies H.Normal) through
  Abelianization.map into a Representation Z P Kab, landed as
  the Module instance by Module.compHom (the same representation
  bridge mathlib uses for its own asModule). All word algebra is
  Stage A, kernel-proved. The arithmetic core here
  (stageB_annihilation) is kernel-proved with the standard axiom
  triple only. Nothing carries sorryAx.

  Receipts (kernel-verified, live #print axioms checks): every
  theorem in this file elaborates with the standard triple only
  [propext, Classical.choice, Quot.sound]. No named axioms.
  Nothing carries sorryAx.
-/

import WallD2.Lemma41
import Mathlib

open BigOperators


universe u v
variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

/-- ℕ-smul (iterated addition) commutes with every scalar: the
    central-numeral fact at the smul level, proved by induction so
    it never touches the OfNat/Nat.cast syntactic gap. -/
lemma smul_nat_smul_comm (r : R) (n : ℕ) (x : M) :
    r • (n • x) = n • (r • x) := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, succ_nsmul, smul_add, ih]

lemma geom_sum_sub (x : R) (n : ℕ) :
    (∑ i ∈ Finset.range n, x ^ i) * (1 - x) = 1 - x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul, ih, mul_sub]
    noncomm_ring

lemma fixed_pow_smul {r : R} {y : M} (h : r • y = y) (i : ℕ) :
    r ^ i • y = y := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ, mul_smul, h, ih]

theorem stageB_annihilation (a1 a2 s sinv : R) (hss : sinv * s = 1)
    (u1 u2 : M)
    (rel1 : u1 = (1 - a2) • u2) (rel2 : s • u2 = (1 - a1) • u1)
    (fix2 : a2 • u1 = u1) (fix1 : a1 • (s • u2) = s • u2)
    (triv26 : (1 - a2 ^ 26) • u2 = 0) (triv15 : (1 - a1 ^ 15) • u1 = 0) :
    u1 = 0 ∧ u2 = 0 := by
  -- 26-rung: the geometric sum acts on u1 as 26u1 (a2 fixes u1),
  -- and on (1-a2)u2 as (1-a2^26)u2 = 0.
  have h26 : (26 : ℕ) • u1 = 0 := by
    have key : (∑ i ∈ Finset.range 26, a2 ^ i) • u1 = (1 - a2 ^ 26) • u2 := by
      rw [rel1, ← mul_smul, geom_sum_sub]
    have lhs : (∑ i ∈ Finset.range 26, a2 ^ i) • u1
        = ∑ i ∈ Finset.range 26, u1 := by
      rw [Finset.sum_smul]
      exact Finset.sum_congr rfl (fun i _ => fixed_pow_smul fix2 i)
    calc (26 : ℕ) • u1 = ∑ i ∈ Finset.range 26, u1 := by
          rw [Finset.sum_const, Finset.card_range]
      _ = (∑ i ∈ Finset.range 26, a2 ^ i) • u1 := lhs.symm
      _ = (1 - a2 ^ 26) • u2 := key
      _ = 0 := triv26
  -- 15-rung: the geometric sum acts on s•u2 as 15(s•u2) (a1 fixes
  -- s•u2); the s then commutes past the numeral (central).
  have h15sw : (15 : ℕ) • (s • u2) = 0 := by
    have key : (∑ i ∈ Finset.range 15, a1 ^ i) • (s • u2)
        = (1 - a1 ^ 15) • u1 := by
      rw [rel2, ← mul_smul, geom_sum_sub]
    have lhs : (∑ i ∈ Finset.range 15, a1 ^ i) • (s • u2)
        = ∑ i ∈ Finset.range 15, (s • u2) := by
      rw [Finset.sum_smul]
      exact Finset.sum_congr rfl (fun i _ => fixed_pow_smul fix1 i)
    calc (15 : ℕ) • (s • u2) = ∑ i ∈ Finset.range 15, (s • u2) := by
          rw [Finset.sum_const, Finset.card_range]
      _ = (∑ i ∈ Finset.range 15, a1 ^ i) • (s • u2) := lhs.symm
      _ = (1 - a1 ^ 15) • u1 := key
      _ = 0 := triv15
  have h15u2 : (15 : ℕ) • u2 = 0 := by
    have s15 : s • ((15 : ℕ) • u2) = 0 := by
      rw [smul_nat_smul_comm s 15 u2]
      exact h15sw
    have back : sinv • (s • ((15 : ℕ) • u2)) = (15 : ℕ) • u2 := by
      rw [← mul_smul, hss, one_smul]
    rw [← back, s15, smul_zero]
  have h15u1 : (15 : ℕ) • u1 = 0 := by
    rw [rel1, ← smul_nat_smul_comm, h15u2, smul_zero]
  -- Bezout over ℤ: 1 = 7*15 - 4*26 (105 - 104).
  have h26z : (26 : ℤ) • u1 = 0 := (natCast_zsmul u1 26).trans h26
  have h15z : (15 : ℤ) • u1 = 0 := (natCast_zsmul u1 15).trans h15u1
  have hu1 : u1 = 0 := by
    have bez : ((7 : ℤ) * (15 : ℤ) - (4 : ℤ) * (26 : ℤ)) = 1 := by norm_num
    calc u1 = (1 : ℤ) • u1 := (one_smul ℤ u1).symm
      _ = ((7 : ℤ) * (15 : ℤ) - (4 : ℤ) * (26 : ℤ)) • u1 := by rw [bez]
      _ = (7 : ℤ) • ((15 : ℤ) • u1) - (4 : ℤ) • ((26 : ℤ) • u1) := by
          rw [sub_smul, mul_smul (7 : ℤ) (15 : ℤ) u1, mul_smul (4 : ℤ) (26 : ℤ) u1]
      _ = 0 := by
          rw [h15z, smul_zero, h26z, smul_zero, sub_zero]
  have hu2 : u2 = 0 := by
    have hs2 : s • u2 = 0 := by rw [rel2, hu1, smul_zero]
    have back2 : sinv • (s • u2) = u2 := by rw [← mul_smul, hss, one_smul]
    rw [← back2, hs2, smul_zero]
  exact ⟨hu1, hu2⟩



namespace Lemma41

open Gen

/-! ## Stage B: K, Kab, the identification axioms, image formula,
    K-triviality -/

abbrev K : Subgroup P := Subgroup.normalClosure {t1, t2}

theorem t1_mem_K : t1 ∈ K := Subgroup.subset_normalClosure (Or.inl rfl)
theorem t2_mem_K : t2 ∈ K := Subgroup.subset_normalClosure (Or.inr rfl)
theorem K_normal : K.Normal := Subgroup.normalClosure_normal

abbrev Kab : Type := Additive (Abelianization ↥K)

def phi : Additive ↥K →+ Kab := MonoidHom.toAdditive (Abelianization.of (G := ↥K))

theorem phi_one : phi (Additive.ofMul 1) = 0 := map_zero phi
theorem phi_mul (x y : ↥K) :
    phi (Additive.ofMul (x * y)) = phi (Additive.ofMul x) + phi (Additive.ofMul y) :=
  map_add phi (Additive.ofMul x) (Additive.ofMul y)
theorem phi_inv (k : ↥K) :
    phi (Additive.ofMul k⁻¹) = -phi (Additive.ofMul k) :=
  map_neg phi (Additive.ofMul k)

/-- The conjugation action of P on the abelianization of K, per
    group element, as a homomorphism into conjugation
    automorphisms of K. mathlib's MulAut.conjNormal with K.Normal
    (H.Normal) supplies the automorphism; this lifts it through
    Abelianization.map (forward-only: no inv/trans needed). -/
def conjOnAbel (g : P) : Abelianization ↥K →* Abelianization ↥K :=
  Abelianization.map ((MulAut.conjNormal (H := K) g : ↥K ≃* ↥K).toMonoidHom)

theorem conjOnAbel_of (g : P) (k : ↥K) :
    conjOnAbel g (Abelianization.of k)
      = Abelianization.of (MulAut.conjNormal (H := K) g k) := by
  simp [conjOnAbel]

theorem conjOnAbel_one : conjOnAbel 1 = MonoidHom.id _ := by
  have h : MulAut.conjNormal (H := K) (1:P) = 1 := by
    simpa using (MulAut.conjNormal (H := K)).map_one
  rw [conjOnAbel, h]
  have h2 : ((1 : ↥K ≃* ↥K).toMonoidHom) = MonoidHom.id ↥K := rfl
  rw [h2]
  simp

theorem conjOnAbel_mul (g h : P) :
    conjOnAbel (g * h) = (conjOnAbel g).comp (conjOnAbel h) := by
  have hc : MulAut.conjNormal (H := K) (g * h)
      = MulAut.conjNormal (H := K) g * MulAut.conjNormal (H := K) h :=
    (MulAut.conjNormal (H := K)).map_mul g h
  show Abelianization.map ((MulAut.conjNormal (H := K) (g * h) : ↥K ≃* ↥K).toMonoidHom)
      = (conjOnAbel g).comp (conjOnAbel h)
  rw [hc]
  show Abelianization.map (((MulAut.conjNormal (H := K) g : ↥K ≃* ↥K)
      * (MulAut.conjNormal (H := K) h : ↥K ≃* ↥K)).toMonoidHom)
      = (conjOnAbel g).comp (conjOnAbel h)
  have hcomp : (((MulAut.conjNormal (H := K) g : ↥K ≃* ↥K)
      * (MulAut.conjNormal (H := K) h : ↥K ≃* ↥K)).toMonoidHom)
      = ((MulAut.conjNormal (H := K) g : ↥K ≃* ↥K).toMonoidHom).comp
        ((MulAut.conjNormal (H := K) h : ↥K ≃* ↥K).toMonoidHom) := rfl
  rw [hcomp]
  exact (Abelianization.map_comp _ _).symm

/-- **The conjugation representation**: P on Kab, built from the
    per-element conjugation homomorphisms. The Z-linear maps are
    the additive transports (MonoidHom.toAdditive) of the
    abelianization conjugation homs, made Z-linear by
    AddMonoidHom.toIntLinearMap (Kab is an AddCommGroup, hence
    uniquely a Z-module). -/
def conjRep : Representation ℤ P Kab where
  toFun g := AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (conjOnAbel g))
  map_one' := by
    have h3 : conjOnAbel 1 = MonoidHom.id _ := conjOnAbel_one
    show AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (conjOnAbel 1)) = 1
    rw [h3]
    rfl
  map_mul' := by
    intro g h
    have hc : conjOnAbel (g * h) = (conjOnAbel g).comp (conjOnAbel h) := conjOnAbel_mul g h
    have htc : MonoidHom.toAdditive ((conjOnAbel g).comp (conjOnAbel h))
        = (MonoidHom.toAdditive (conjOnAbel g)).comp (MonoidHom.toAdditive (conjOnAbel h)) := rfl
    show AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (conjOnAbel (g * h)))
        = AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (conjOnAbel g))
          * AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (conjOnAbel h))
    rw [hc, htc]
    rfl

/-- **The Module instance (B1, discharged)**: Kab is a ZP-module
    by the representation bridge: the same
    Module.compHom/asAlgebraHom route mathlib uses for
    Representation.asModule, applied directly to Kab. -/
noncomputable instance : Module (MonoidAlgebra ℤ P) Kab :=
  Module.compHom Kab (Representation.asAlgebraHom conjRep).toRingHom

noncomputable def ofZP (g : P) : MonoidAlgebra ℤ P := MonoidAlgebra.of ℤ P g
theorem ofZP_mul (a b : P) : ofZP (a * b) = ofZP a * ofZP b := map_mul _ _ _
theorem ofZP_one : ofZP 1 = 1 := map_one _
theorem ofZP_pow (g : P) (n : ℕ) : ofZP (g ^ n) = (ofZP g) ^ n := map_pow _ _ _

def conjK (g : P) (k : ↥K) : ↥K := ⟨g * ↑k * g⁻¹, K_normal.conj_mem ↑k k.2 g⟩

@[simp] theorem conjK_coe (g : P) (k : ↥K) :
    (conjK g k : P) = g * ↑k * g⁻¹ := rfl

/-- **The action identification (B2, discharged)**: the ZP-action of
    a group element on Kab is conjugation. Formerly IDENTIFICATION
    AXIOM B2; now kernel-proved from the construction above. The
    smul travels through Module.compHom + asAlgebraHom to function
    application (rfl), ofZP g is single g 1 (rfl), and the
    representation applied to phi is the abelianization of
    conjNormal, which is conjK (Subtype.ext + conjNormal_apply +
    conjK_coe). -/
theorem action_conj (g : P) (k : ↥K) :
    ofZP g • phi (Additive.ofMul k) = phi (Additive.ofMul (conjK g k)) := by
  -- Step 1: the compHom smul is application of the algebra hom
  have hsmul : ofZP g • phi (Additive.ofMul k)
      = (Representation.asAlgebraHom conjRep) (ofZP g) (phi (Additive.ofMul k)) := rfl
  -- Step 2: asAlgebraHom on a single group element is the representation
  have hsingle : (Representation.asAlgebraHom conjRep) (ofZP g) = conjRep g := by
    have hof : ofZP g = MonoidAlgebra.single g 1 := rfl
    rw [hof, Representation.asAlgebraHom_single_one]
  -- Step 3: the representation applied to phi is conjugation on the abelianization
  have happ : conjRep g (phi (Additive.ofMul k))
      = Additive.ofMul (conjOnAbel g (Abelianization.of k)) := rfl
  -- Step 4: conjOnAbel acts by conjNormal
  have hiden : MulAut.conjNormal (H := K) g k = conjK g k := by
    apply Subtype.ext
    rw [conjK_coe, MulAut.conjNormal_apply]
  rw [hsmul, hsingle, happ, conjOnAbel_of, hiden]
  rfl

def cmmK (t : ↥K) (g : P) : ↥K :=
  ⟨↑t * (g * (↑t)⁻¹ * g⁻¹),
    Subgroup.mul_mem K t.2 (K_normal.conj_mem _ (Subgroup.inv_mem K t.2) g)⟩

theorem image_formula (t : ↥K) (g : P) :
    phi (Additive.ofMul (cmmK t g)) = (1 - ofZP g) • phi (Additive.ofMul t) := by
  have hval : (cmmK t g : P) = (t : P) * (g * (t : P)⁻¹ * g⁻¹) := rfl
  have hconj : (conjK g (t⁻¹ : ↥K) : P) = g * (t : P)⁻¹ * g⁻¹ := by
    have hc := conjK_coe g (t⁻¹ : ↥K)
    rwa [Subgroup.coe_inv] at hc
  have hmulP : (cmmK t g : P) = (t : P) * (conjK g (t⁻¹ : ↥K) : P) := by
    rw [hval, hconj]
  have hmul : cmmK t g = t * conjK g (t⁻¹ : ↥K) := by
    apply Subtype.ext
    exact hmulP
  have hw : phi (Additive.ofMul (conjK g (t⁻¹ : ↥K)))
      = -(ofZP g • phi (Additive.ofMul t)) := by
    rw [← action_conj g (t⁻¹ : ↥K), phi_inv, smul_neg]
  calc phi (Additive.ofMul (cmmK t g))
      = phi (Additive.ofMul t) + phi (Additive.ofMul (conjK g (t⁻¹ : ↥K))) := by
        rw [hmul, phi_mul]
    _ = phi (Additive.ofMul t) + -(ofZP g • phi (Additive.ofMul t)) := by rw [hw]
    _ = (1 - ofZP g) • phi (Additive.ofMul t) := by
        rw [sub_smul, one_smul, sub_eq_add_neg]

/-- K acts trivially on Kab. -/
theorem trivial_action (k x : ↥K) :
    ofZP (↑k : P) • phi (Additive.ofMul x) = phi (Additive.ofMul x) := by
  rw [action_conj (↑k : P) x]
  have hval : (conjK (↑k : P) x : P) = ((k : P) * ↑x) * (↑k : P)⁻¹ := rfl
  have hprod : (conjK (↑k : P) x : P) = (k : P) * (↑x * (k : P)⁻¹) := by
    rw [hval]; group
  have hmul : conjK (↑k : P) x = k * (x * k⁻¹) := by
    apply Subtype.ext
    exact hprod
  rw [hmul, phi_mul, phi_mul, phi_inv]
  abel


/-! ### The word facts behind the six module hypotheses -/

/-- A vanishing commutator word gives the commute form. -/
lemma comm_from_cmm (w h : P) (hcmm : cmm w h = 1) : h * w * h⁻¹ = w := by
  have h2 : w * h * w⁻¹ = h := by
    calc w * h * w⁻¹ = (w * h * w⁻¹ * h⁻¹) * h := by group
      _ = cmm w h * h := by
          rw [show w * h * w⁻¹ * h⁻¹ = cmm w h from rfl]
      _ = 1 * h := by rw [hcmm]
      _ = h := by group
  have h3 : w * h = h * w := by
    calc w * h = (w * h * w⁻¹) * w := by group
      _ = h * w := by rw [h2]
  calc h * w * h⁻¹ = (w * h) * h⁻¹ := by rw [h3]
    _ = w := by group

def u1 : Kab := phi (Additive.ofMul ⟨t1, t1_mem_K⟩)
def u2 : Kab := phi (Additive.ofMul ⟨t2, t2_mem_K⟩)

/-- Relation 1: t1 = [t2, a2] in K dies as u1 = (1 - a2) u2. -/
theorem rel1 : u1 = (1 - ofZP gA2) • u2 := by
  have heq : cmmK ⟨t2, t2_mem_K⟩ gA2 = ⟨t1, t1_mem_K⟩ := by
    apply Subtype.ext
    rw [show (cmmK ⟨t2, t2_mem_K⟩ gA2 : P) = cmm t2 gA2 from by
          show t2 * (gA2 * t2⁻¹ * gA2⁻¹) = t2 * gA2 * t2⁻¹ * gA2⁻¹
          group]
    exact id1_target.symm
  have h := image_formula (⟨t2, t2_mem_K⟩ : ↥K) gA2
  rw [heq] at h
  show phi (Additive.ofMul ⟨t1, t1_mem_K⟩)
      = (1 - ofZP gA2) • phi (Additive.ofMul ⟨t2, t2_mem_K⟩)
  exact h

/-- Relation 2: s u2 = (1 - a1) u1, from st2s^-1 = [t1, a1]. -/
theorem rel2 : ofZP gS • u2 = (1 - ofZP gA1) • u1 := by
  have hcm : conjK gS ⟨t2, t2_mem_K⟩ = cmmK ⟨t1, t1_mem_K⟩ gA1 := by
    apply Subtype.ext
    rw [show (cmmK ⟨t1, t1_mem_K⟩ gA1 : P) = cmm t1 gA1 from by
          show t1 * (gA1 * t1⁻¹ * gA1⁻¹) = t1 * gA1 * t1⁻¹ * gA1⁻¹
          group]
    exact id2_target
  show ofZP gS • phi (Additive.ofMul ⟨t2, t2_mem_K⟩)
      = (1 - ofZP gA1) • phi (Additive.ofMul ⟨t1, t1_mem_K⟩)
  rw [action_conj gS ⟨t2, t2_mem_K⟩, hcm,
      image_formula (⟨t1, t1_mem_K⟩ : ↥K) gA1]

/-- a2 fixes u1 (t1 commutes with a2). -/
theorem fix2 : ofZP gA2 • u1 = u1 := by
  have hc : conjK gA2 ⟨t1, t1_mem_K⟩ = ⟨t1, t1_mem_K⟩ := by
    apply Subtype.ext
    exact comm_from_cmm t1 gA2 rung7_comm_t1_a2
  show ofZP gA2 • phi (Additive.ofMul ⟨t1, t1_mem_K⟩)
      = phi (Additive.ofMul ⟨t1, t1_mem_K⟩)
  rw [action_conj gA2 ⟨t1, t1_mem_K⟩, hc]

/-- a1 fixes s u2 (st2s^-1 commutes with a1). -/
theorem fix1 : ofZP gA1 • (ofZP gS • u2) = ofZP gS • u2 := by
  have hc : conjK (gA1 * gS) ⟨t2, t2_mem_K⟩ = conjK gS ⟨t2, t2_mem_K⟩ := by
    apply Subtype.ext
    have hw := comm_from_cmm (gS * t2 * gS⁻¹) gA1 rung8_comm_st2_a1
    show gA1 * gS * t2 * (gA1 * gS)⁻¹ = gS * t2 * gS⁻¹
    rw [show gA1 * gS * t2 * (gA1 * gS)⁻¹
          = gA1 * (gS * t2 * gS⁻¹) * gA1⁻¹ from by group]
    exact hw
  show ofZP gA1 • (ofZP gS • phi (Additive.ofMul ⟨t2, t2_mem_K⟩))
      = ofZP gS • phi (Additive.ofMul ⟨t2, t2_mem_K⟩)
  rw [smul_smul, ← ofZP_mul, action_conj (gA1 * gS) ⟨t2, t2_mem_K⟩,
      hc, action_conj gS ⟨t2, t2_mem_K⟩]

/-- t1 = a2^26 in P, so (1 - a2^26) u2 = 0 because K acts trivially. -/
theorem triv26 : (1 - (ofZP gA2) ^ 26) • u2 = 0 := by
  rw [← ofZP_pow]
  have ht1 : t1 = Pm (L a2 ^ 26) := by
    show gX1 * gX1 = Pm (L a2 ^ 26)
    rw [rung1_x1_eq_a2pow13, ← _root_.map_mul Pm,
        show L a2 ^ 13 * L a2 ^ 13 = L a2 ^ 26 from by rw [← pow_add]]
  have hp : gA2 ^ 26 = Pm (L a2 ^ 26) := by
    rw [show (gA2 : P) = Pm (L a2) from rfl, map_pow Pm]
  have hcoe : gA2 ^ 26 = t1 := by rw [hp, ht1]
  have hc1 : ((⟨t1, t1_mem_K⟩ : ↥K) : P) = t1 := rfl
  show (1 - ofZP (gA2 ^ 26)) • phi (Additive.ofMul ⟨t2, t2_mem_K⟩) = 0
  rw [hcoe, ← hc1, sub_smul, one_smul,
      trivial_action (⟨t1, t1_mem_K⟩ : ↥K) ⟨t2, t2_mem_K⟩, sub_self]

/-- st2s^-1 = a1^15 in P, so (1 - a1^15) u1 = 0 because K acts trivially. -/
theorem triv15 : (1 - (ofZP gA1) ^ 15) • u1 = 0 := by
  rw [← ofZP_pow]
  have ht2 : t2 = Pm (L x2 ^ 3) := by
    show Pm (L x2) * Pm (L x2) * Pm (L x2) = Pm (L x2 ^ 3)
    rw [← _root_.map_mul Pm, ← _root_.map_mul Pm]
    congr 1
  have hst2 : gS * t2 * gS⁻¹ = Pm (L a1 ^ 15) := by
    rw [ht2, show (gS : P) = Pm (L s) from rfl, ← _root_.map_mul Pm,
        ← _root_.map_inv Pm, ← _root_.map_mul Pm]
    rw [show L s * L x2 ^ 3 * (L s)⁻¹ = (L s * L x2 * (L s)⁻¹) ^ 3 from conj_pow.symm,
        _root_.map_pow Pm, rung5, ← _root_.map_pow Pm]
    have cube : (L a1 ^ 5) ^ 3 = L a1 ^ 15 := by
      rw [show 15 = 5 * 3 from by norm_num, pow_mul]
    rw [cube]
  have hp15 : gA1 ^ 15 = gS * t2 * gS⁻¹ := by
    rw [show (gA1 : P) = Pm (L a1) from rfl, ← map_pow Pm, ← hst2]
  have hc2 : (conjK gS ⟨t2, t2_mem_K⟩ : P) = gS * t2 * gS⁻¹ := rfl
  show (1 - ofZP (gA1 ^ 15)) • phi (Additive.ofMul ⟨t1, t1_mem_K⟩) = 0
  rw [hp15, ← hc2, sub_smul, one_smul,
      trivial_action (conjK gS ⟨t2, t2_mem_K⟩) ⟨t1, t1_mem_K⟩, sub_self]

/-- The s-eliminator is a unit in ZP. -/
theorem hss_unit : ofZP (gS⁻¹) * ofZP gS = 1 := by
  have e : ofZP (gS⁻¹) * ofZP gS = ofZP (gS⁻¹ * gS) :=
    (ofZP_mul gS⁻¹ gS).symm
  have hinv : gS⁻¹ * gS = 1 := by group
  rw [e, hinv, ofZP_one]

/-- Stage B arithmetic, instantiated: the module annihilation. -/
theorem stageB_applied : u1 = 0 ∧ u2 = 0 :=
  stageB_annihilation (ofZP gA1) (ofZP gA2) (ofZP gS) (ofZP (gS⁻¹)) hss_unit
    u1 u2 rel1 rel2 fix2 fix1 triv26 triv15


/-! ### Generation: closure induction puts every phi k in the span -/

theorem phi_mem_span (k : ↥K) :
    phi (Additive.ofMul k) ∈ Submodule.span (MonoidAlgebra ℤ P) {u1, u2} := by
  have key : ∀ (x : P) (hx : x ∈ Subgroup.closure (Group.conjugatesOfSet {t1, t2})),
      ∃ hk : x ∈ K, phi (Additive.ofMul ⟨x, hk⟩)
        ∈ Submodule.span (MonoidAlgebra ℤ P) {u1, u2} := by
    intro x hx
    refine Subgroup.closure_induction
      (p := fun x hx => ∃ hk : x ∈ K, phi (Additive.ofMul ⟨x, hk⟩)
        ∈ Submodule.span (MonoidAlgebra ℤ P) {u1, u2}) ?_ ?_ ?_ ?_ hx
    · intro x hx
      rw [Group.mem_conjugatesOfSet_iff] at hx
      obtain ⟨a, ha, c, hconj⟩ := hx
      have hsc : (↑c : P) * a = x * (↑c : P) := hconj
      have hxc : x = (↑c : P) * a * (↑c : P)⁻¹ := by
        calc x = x * (↑c : P) * (↑c : P)⁻¹ := by group
          _ = (↑c : P) * a * (↑c : P)⁻¹ := by rw [← hsc]
      have hor : a = t1 ∨ a = t2 := by simpa using ha
      rcases hor with rfl | rfl
      · have hxK : x ∈ K := by
          rw [hxc]; exact K_normal.conj_mem t1 t1_mem_K (↑c : P)
        refine ⟨hxK, ?_⟩
        have heq : (⟨x, hxK⟩ : ↥K)
            = conjK (↑c : P) (⟨t1, t1_mem_K⟩ : ↥K) := Subtype.ext hxc
        rw [heq, ← action_conj (↑c : P) (⟨t1, t1_mem_K⟩ : ↥K)]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl rfl))
      · have hxK : x ∈ K := by
          rw [hxc]; exact K_normal.conj_mem t2 t2_mem_K (↑c : P)
        refine ⟨hxK, ?_⟩
        have heq : (⟨x, hxK⟩ : ↥K)
            = conjK (↑c : P) (⟨t2, t2_mem_K⟩ : ↥K) := Subtype.ext hxc
        rw [heq, ← action_conj (↑c : P) (⟨t2, t2_mem_K⟩ : ↥K)]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr rfl))
    · refine ⟨Subgroup.one_mem K, ?_⟩
      show phi (Additive.ofMul (1 : ↥K))
          ∈ Submodule.span (MonoidAlgebra ℤ P) {u1, u2}
      rw [phi_one]
      exact Submodule.zero_mem _
    · intro x y hx hy hpx hpy
      obtain ⟨hxK, hpx'⟩ := hpx
      obtain ⟨hyK, hpy'⟩ := hpy
      refine ⟨Subgroup.mul_mem K hxK hyK, ?_⟩
      show phi (Additive.ofMul ((⟨x, hxK⟩ : ↥K) * (⟨y, hyK⟩ : ↥K)))
          ∈ Submodule.span (MonoidAlgebra ℤ P) {u1, u2}
      rw [phi_mul]
      exact Submodule.add_mem _ hpx' hpy'
    · intro x hx hpx
      obtain ⟨hxK, hpx'⟩ := hpx
      refine ⟨Subgroup.inv_mem K hxK, ?_⟩
      show phi (Additive.ofMul ((⟨x, hxK⟩ : ↥K)⁻¹))
          ∈ Submodule.span (MonoidAlgebra ℤ P) {u1, u2}
      rw [phi_inv]
      exact Submodule.neg_mem _ hpx'
  exact (key ↑k k.2).2

/-- With u1 = u2 = 0 the span collapses, so phi kills every element. -/
theorem phi_zero (k : ↥K) : phi (Additive.ofMul k) = 0 := by
  obtain ⟨hu1, hu2⟩ := stageB_applied
  have hle : Submodule.span (MonoidAlgebra ℤ P) {u1, u2}
      ≤ (⊥ : Submodule (MonoidAlgebra ℤ P) Kab) := by
    rw [Submodule.span_le]
    intro z hz
    have hz' : z = u1 ∨ z = u2 := by simpa using hz
    rcases hz' with rfl | rfl
    · rw [hu1]; exact Submodule.zero_mem _
    · rw [hu2]; exact Submodule.zero_mem _
  have hmem : phi (Additive.ofMul k)
      ∈ (⊥ : Submodule (MonoidAlgebra ℤ P) Kab) :=
    hle (phi_mem_span k)
  rwa [Submodule.mem_bot] at hmem

/-- **Lemma 4.1, Stage B (K is perfect)**: the normal closure of the
    two commutator words is a perfect group. -/
theorem K_perfect : Group.IsPerfect ↥K := by
  rw [Group.isPerfect_def, Subgroup.eq_top_iff']
  intro k
  have hphi := phi_zero k
  have hcoe : phi (Additive.ofMul k) = Additive.ofMul (Abelianization.of k) := rfl
  have hz : Additive.ofMul (Abelianization.of k) = 0 := by rw [← hcoe]; exact hphi
  have h1 : Abelianization.of k = 1 := by
    have hz0 : (0 : Additive (Abelianization ↥K)) = Additive.ofMul 1 := rfl
    rw [hz0] at hz
    exact hz
  have hk : k ∈ Abelianization.of.ker := MonoidHom.mem_ker.mpr h1
  rwa [Abelianization.ker_of ↥K] at hk


end Lemma41
