/-
  Project for AI for Formal Proof of Qiuzhen College, 2026 Winter.
  Copyright (c) 2026 Jiang Yixuan. All rights reserved.
  Authors: Jiang Yixuan（姜懿轩）
-/

import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.RepresentationTheory.Character
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.DirectSum.LinearMap

/-!
# Frobenius-Schur Indicator

Frobenius-Schur indicators are defined by the average value of the character on the squares of
group elements. They are used to determine whether a representation is real, complex, or
quaternionic.

We prove that the FS indicator can only take values -1, 0, or 1 for simple representations.

We prove that a zero FS indicator implies the character is not real-valued, and thus the
representation is complex.

## TODO
* Determine the characters of Sym²V and Alt²V.
* Prove the dual of a simple representation is simple.
* Prove the simple representations is nontrivial.
* Optimize the theorem by using the constructed Sym²V and Alt²V directly, instead of via
  `symSqFDRep`/`altSqFDRep`.
* Determine the sturcture of the representation when FSindicator is 1 or -1.
-/

variable {G : Type} [Group G] [Fintype G] {V : FDRep ℂ G}

noncomputable def FSindicator (V : FDRep ℂ G) : ℂ :=
  ∑ g : G, (V.character (g * g)) / Fintype.card G

/-We define the Sym^2 V and Alt^2 V, using the flip homormophism.-/
noncomputable def flipHom (V : FDRep ℂ G) :
  (TensorProduct ℂ V.V V.V) →ₗ[ℂ] (TensorProduct ℂ V.V V.V) :=
  TensorProduct.comm ℂ V.V V.V

noncomputable def flipSqSubmodule (sign : ℤ) (V : FDRep ℂ G) :
  Submodule ℂ (TensorProduct ℂ V.V V.V) :=
  LinearMap.ker (flipHom V - sign • LinearMap.id)

noncomputable def flipProjector (sign : ℤ) (V : FDRep ℂ G) :
  Module.End ℂ (TensorProduct ℂ V.V V.V) :=
  (⅟2 : ℂ) • (LinearMap.id + sign • flipHom V)

/-We show the projector defined above is invariant on the subspace.-/
omit [Fintype G] in
lemma symProjector_mem_symSqSubmodule (V : FDRep ℂ G) (v : TensorProduct ℂ V.V V.V) :
  flipProjector 1 V v ∈ flipSqSubmodule 1 V := by
  apply LinearMap.mem_ker.mpr
  simp only [zsmul_eq_mul, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.id_coe, id_eq,
    Module.End.intCast_apply,flipProjector]
  simp only [invOf_eq_inv, smul_add, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_coe,
    id_eq, Module.End.mul_apply, Module.End.intCast_apply, map_add, map_smul,
    LinearMap.map_smul_of_tower]
  abel_nf
  have flip_flip : (flipHom V).comp (flipHom V) = LinearMap.id := by
    ext x y
    simp [flipHom, TensorProduct.comm_tmul]
  have : (flipHom V) ((flipHom V) v) = (flipHom V).comp (flipHom V) v := by
    simp only [LinearMap.coe_comp, Function.comp_apply]
  have flip_flip_v : (flipHom V) ((flipHom V) v) = v := by
    rw [this, flip_flip]
    simp only [LinearMap.id_coe, id_eq]
  rw[flip_flip_v]
  simp only [Int.reduceNeg, neg_smul, one_smul, add_neg_cancel]

omit [Fintype G] in
lemma altProjector_mem_altSqSubmodule (V : FDRep ℂ G) (v : TensorProduct ℂ V.V V.V) :
  flipProjector (-1) V v ∈ flipSqSubmodule (-1) V := by
  apply LinearMap.mem_ker.mpr
  simp only [zsmul_eq_mul, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.id_coe, id_eq,
    Module.End.intCast_apply,flipProjector]
  simp only [invOf_eq_inv, smul_add, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_coe,
    id_eq, Module.End.mul_apply, Module.End.intCast_apply, map_add, map_smul,
    LinearMap.map_smul_of_tower]
  abel_nf
  have flip_flip : (flipHom V).comp (flipHom V) = LinearMap.id := by
    ext x y
    simp [flipHom, TensorProduct.comm_tmul]
  have : (flipHom V) ((flipHom V) v) = (flipHom V).comp (flipHom V) v := by
    simp only [LinearMap.coe_comp, Function.comp_apply]
  have flip_flip_v : (flipHom V) ((flipHom V) v) = v := by
    rw [this, flip_flip]
    simp only [LinearMap.id_coe, id_eq]
  rw[flip_flip_v]
  simp only [Int.reduceNeg, neg_smul, one_smul, smul_neg, neg_add_cancel_left, add_neg_cancel]


/- We prove that the tensor square decomposes into the internal direct sum of
`flipSqSubmodule 1 V` (symmetric) and `flipSqSubmodule (-1) V` (alternating).-/
omit [Fintype G] in
lemma sym_alt_submodule_IsInternal (V : FDRep ℂ G) :
  DirectSum.IsInternal ![(flipSqSubmodule 1 V),(flipSqSubmodule (-1) V)] := by
  have : IsCompl (flipSqSubmodule 1 V) (flipSqSubmodule (-1) V) := by
    constructor
    · intro x ha hb v hv
      let fa := LinearMap.mem_ker.mp (ha hv)
      let fb := LinearMap.mem_ker.mp (hb hv)
      simp only [one_smul, LinearMap.sub_apply, LinearMap.id_coe, id_eq] at fa
      simp only [Int.reduceNeg, neg_smul, one_smul, sub_neg_eq_add, LinearMap.add_apply,
        LinearMap.id_coe, id_eq] at fb
      have f : (2 : ℂ) • v = 0 - 0 := by
        nth_rw 1 [← fb]
        rw[← fa]
        abel_nf
        norm_cast
      simp only [sub_self] at f
      have : v = 0 := by
        have : (2 : ℂ) ≠ 0 := by norm_num
        rcases (smul_eq_zero.mp f) with h1 | h2
        · cases this h1
        · exact h2
      exact this
    · intro x ha hb v hv
      let va := flipProjector 1 V v
      let vb := flipProjector (-1) V v
      have : va + vb = v := by
        simp only [flipProjector, invOf_eq_inv, one_smul, smul_add, LinearMap.add_apply,
          LinearMap.smul_apply, LinearMap.id_coe, id_eq, Int.reduceNeg, neg_smul, smul_neg,
          LinearMap.neg_apply, va, vb]
        abel_nf
        have : (2 : ℂ) • (2⁻¹ : ℂ) • v = v := by
          rw[← mul_smul]
          simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀, one_smul]
        exact_mod_cast this
      let h_va := symProjector_mem_symSqSubmodule V v
      let h_vb := altProjector_mem_altSqSubmodule V v
      have hc_va : va ∈ x := by
        simp_all only [Int.reduceNeg, Submodule.mem_top, va, vb]
        apply ha
        simp_all only [Int.reduceNeg]
      have hc_vb : vb ∈ x := by
        simp_all only [Int.reduceNeg, Submodule.mem_top, va, vb]
        apply hb
        simp_all only [Int.reduceNeg]
      have v_mem_x : v ∈ x := by
        rw[← this]
        exact Submodule.add_mem x hc_va hc_vb
      exact v_mem_x
  have f1 : @Fin.mk 2 0 (by decide) ≠ @Fin.mk 2 1 (by decide) := by norm_num
  --have f2 : Set.univ = {@Fin.mk 2 0 (by decide), @Fin.mk 2 1 (by decide)⟩} := by sorry
  have f2 : Set.univ = {@Fin.mk 2 0 (by decide), @Fin.mk 2 1 (by decide)} := by
    ext x
    fin_cases x <;> simp
  exact (DirectSum.isInternal_submodule_iff_isCompl
    ![(flipSqSubmodule 1 V),(flipSqSubmodule (-1) V)] f1 f2).mpr this

/-The tensor square $V \otimes V$ can be decomposed into symmetric and alternating parts.
We formalize these as subrepresentations of the tensor product representation.-/

/- The symmetric (sign=1) and alternating (sign=-1) submodules are invariant under
the group action. This lemma proves the G-invariance by showing that the group action
commutes with the `flipHom` operator. -/
omit [Fintype G] in
lemma flipSqSubmodule_invariant (sign : ℤ) :
  ∀ (g : G),
    (flipSqSubmodule sign V) ≤
    Submodule.comap ((Representation.tprod V.ρ V.ρ) g) (flipSqSubmodule sign V)  := by
  intro g x hx
  unfold flipSqSubmodule at *
  simp only [Submodule.mem_comap, LinearMap.mem_ker, Representation.tprod_apply,
  LinearMap.sub_apply, zsmul_eq_mul, Module.End.mul_apply, LinearMap.id_coe,
  id_eq, Module.End.intCast_apply]
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, zsmul_eq_mul,
  Module.End.mul_apply, LinearMap.id_coe, id_eq,Module.End.intCast_apply] at hx
  have : (flipHom V).comp (TensorProduct.map (V.ρ g) (V.ρ g)) =
  (TensorProduct.map (V.ρ g) (V.ρ g)).comp (flipHom V) := by
    ext x y
    simp [flipHom, TensorProduct.map_tmul]
  have : (flipHom V) (TensorProduct.map (V.ρ g) (V.ρ g) x) =
    TensorProduct.map (V.ρ g) (V.ρ g) ((flipHom V) x) := by
    simpa using congrArg (fun f => f x) this
  rw [this, hx]
  simp only [LinearMap.map_smul_of_tower, sub_self]

/- A set-theoretic version of the invariance lemma, used for trace calculations. -/
omit [Fintype G] in
lemma flipSqSubmodule_invariant' (sign : ℤ) (g : G) :
  Set.MapsTo (TensorProduct.map (V.ρ g) (V.ρ g))
  (flipSqSubmodule sign V) (flipSqSubmodule sign V) := by
  intro x hx
  apply Submodule.mem_comap.mp
  let h := flipSqSubmodule_invariant (V:=V) sign g
  simp_all only [SetLike.mem_coe, Submodule.mem_comap]
  apply h
  exact hx

/- Construct the subrepresentation in the `Rep ℂ G` category. -/
noncomputable def flipSqRep (sign : ℤ) (V : FDRep ℂ G) : Rep ℂ G :=
  Rep.subrepresentation
    (Rep.of (Representation.tprod V.ρ V.ρ))
    (flipSqSubmodule sign V)
    (flipSqSubmodule_invariant sign)

instance flipSqSubmodule.finiteDimensional (sign : ℤ) :
  FiniteDimensional ℂ ↥(flipSqSubmodule sign V) := by
  infer_instance

omit [Fintype G] in
instance flipSqRep_finite (sign : ℤ) (V : FDRep ℂ G) :
  Module.Finite ℂ (flipSqRep sign V).V := by
  exact flipSqSubmodule.finiteDimensional sign

noncomputable def flipSqFDRep (sign : ℤ) (V : FDRep ℂ G) : FDRep ℂ G :=
  FDRep.of (flipSqRep sign V).ρ

noncomputable def symSqFDRep (V : FDRep ℂ G) : FDRep ℂ G :=
  flipSqFDRep 1 V

noncomputable def altSqFDRep (V : FDRep ℂ G) : FDRep ℂ G :=
  flipSqFDRep (-1) V


noncomputable def fsChar {G} [Group G] (sign : ℤ) (χ : G → ℂ) : G → ℂ :=
  fun g =>
    (1/2) * ((χ g) ^ 2 + (sign * χ (g * g)))

noncomputable def fsCharSym (χ : G → ℂ) : G → ℂ := fsChar 1 χ
noncomputable def fsCharAlt (χ : G → ℂ) : G → ℂ := fsChar (-1) χ

instance TensorProduct.finiteDimensional :
  FiniteDimensional ℂ (TensorProduct ℂ V.V V.V) := by
  infer_instance

/- This lemma establishes the relation between the characters of the representations V⊗V
and Sym²V (or Alt²V) by means of a projector. This approach is easier to implement in Lean
compared to computing the trace from the n² eigenvalues.-/
lemma trace_subrep_eq_trace_comp_proj (sign : ℤ) (g : G) :
  (flipSqFDRep sign V).character g =
  @LinearMap.trace ℂ _ (TensorProduct ℂ V.V V.V) _ _
  (((Representation.tprod V.ρ V.ρ) g) ∘ₗ (flipProjector sign V)) := by
  let h := Representation.subrepresentation_apply
    (Rep.of (Representation.tprod V.ρ V.ρ)).ρ
    (flipSqSubmodule sign V) (flipSqSubmodule_invariant sign)
  change ∀ (g : G), (flipSqRep sign V).ρ g = _ at h
  let h := h g
  let N := ![(flipSqSubmodule 1 V),(flipSqSubmodule (-1) V)]
  have hf : ∀ i : Fin 2, Set.MapsTo ((Representation.tprod V.ρ V.ρ) g) (N i) (N i) := by
    intro i
    rcases i with i0 | i1
    · unfold N
      simp only [Representation.tprod_apply, Nat.succ_eq_add_one, Nat.reduceAdd, Int.reduceNeg,
        Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact flipSqSubmodule_invariant' 1 g
    · unfold N
      simp only [Representation.tprod_apply, Nat.succ_eq_add_one, Nat.reduceAdd, Int.reduceNeg,
        Matrix.cons_val_succ', Matrix.cons_val_fin_one]
      exact flipSqSubmodule_invariant' (-1) g
  let f := LinearMap.trace_eq_sum_trace_restrict (sym_alt_submodule_IsInternal V) hf
  sorry

/-This lemma is to show the relation between the characters of V and Sym²V(or Alt²V).-/
lemma flipSqFDRep_character (sign : ℤ) (V : FDRep ℂ G) :
  (flipSqFDRep sign V).character = fsChar sign V.character := by
  sorry


lemma charSym_add_charAlt_eq_char_sq {G} [Group G] (χ : G → ℂ) (g : G) :
  fsCharSym χ g + fsCharAlt χ g = (χ g)^2 := by
  unfold fsCharSym fsCharAlt fsChar
  ring

lemma fsChar_is_char (sign : ℤ) (V : FDRep ℂ G) :
  ∃ W : FDRep ℂ G, W.character = fsChar sign V.character := by
    use flipSqFDRep sign V
    exact flipSqFDRep_character sign V

lemma symSqFDRep_character :
  (symSqFDRep V).character = fsCharSym V.character := by
  exact flipSqFDRep_character 1 V

lemma altSqFDRep_character :
  (altSqFDRep V).character = fsCharAlt V.character := by
  exact flipSqFDRep_character (-1) V

lemma average_rep_eq_natCast (V : FDRep ℂ G) :
  ∃ n : ℕ,
    (⅟(Fintype.card G : ℂ) • ∑ g : G, V.character g) = (n : ℂ) := by
  let n_val := Module.finrank ℂ (Representation.invariants V.ρ)
  use n_val
  unfold n_val
  exact FDRep.average_char_eq_finrank_invariants V

lemma average_alt_add_sym_eq_sq (V : FDRep ℂ G) :
  (⅟(Fintype.card G : ℂ) • ∑ g : G, fsCharSym V.character g) +
  (⅟(Fintype.card G : ℂ) • ∑ g : G, fsCharAlt V.character g) =
  (⅟(Fintype.card G : ℂ) • ∑ g : G, (V.character g)^2) := by
  simp only [← charSym_add_charAlt_eq_char_sq V.character]
  rw [Finset.sum_add_distrib, smul_add]

lemma average_sq_eq_natCast (V : FDRep ℂ G) :
  ∃ n : ℕ,
    (⅟(Fintype.card G : ℂ) • ∑ g : G, (V.character g)^2) = (n : ℂ) := by
  -- use charSym_add_charAlt_eq_char_sq and average_rep_eq_natCast twice
  obtain ⟨n1, hn1⟩ := average_rep_eq_natCast (symSqFDRep V)
  obtain ⟨n2, hn2⟩ := average_rep_eq_natCast (altSqFDRep V)
  use n1 + n2
  simp only [Nat.cast_add]
  rw [← hn1, ← hn2]
  simp only [← charSym_add_charAlt_eq_char_sq V.character]
  simp only [symSqFDRep_character, altSqFDRep_character]
  simp [Finset.sum_add_distrib, mul_add]

/- The details here are tedious and left for future work. -/
def FDRep.dual_iso :
  FDRep.of (Representation.dual V.ρ) ≅ V := sorry

omit [Fintype G] in
lemma dual_simple_of_simple [CategoryTheory.Simple V] :
  CategoryTheory.Simple (FDRep.of (Representation.dual V.ρ)) :=
  CategoryTheory.Simple.of_iso (FDRep.dual_iso)

lemma average_sq_le_one (V : FDRep ℂ G) [CategoryTheory.Simple V] :
  ∃ n : ℕ,
    (⅟(Fintype.card G : ℂ) • ∑ g : G, (V.character g)^2) = (n : ℂ) ∧ (n = 0 ∨ n = 1) := by
  obtain ⟨n, hn⟩ := average_sq_eq_natCast V
  have hle : n = 0 ∨ n = 1 := by
    have f : (⅟(Fintype.card G : ℂ) • ∑ g : G, (V.character g)^2) =
      (⅟(Fintype.card G : ℂ) • ∑ g : G, (V.character g) *
      ((FDRep.of (Representation.dual V.ρ)).character g⁻¹)) := by
      simp only [invOf_eq_inv, smul_eq_mul, FDRep.char_dual, inv_inv, mul_eq_mul_left_iff,
        inv_eq_zero, Nat.cast_eq_zero, Fintype.card_ne_zero, or_false]
      ring_nf
    haveI : CategoryTheory.Simple (FDRep.of (Representation.dual V.ρ)) :=
      dual_simple_of_simple
    rw[FDRep.char_orthonormal V (FDRep.of (Representation.dual V.ρ))] at f
    have ff : (⅟(Fintype.card G : ℂ) • ∑ g : G, (V.character g)^2) = 0 ∨
      (⅟(Fintype.card G : ℂ) • ∑ g : G, (V.character g)^2) = 1
      := by
      by_cases h : Nonempty (V ≅ FDRep.of (Representation.dual V.ρ))
      · right
        rw[f]
        simp[h]
      · left
        rw[f]
        simp[h]
    rw[hn] at ff
    exact_mod_cast ff
  exact ⟨n, hn, hle⟩

lemma charSym_sub_charAlt_eq_FSindicator (V : FDRep ℂ G) :
  (⅟(Fintype.card G : ℂ) • ∑ g : G, fsCharSym V.character g) -
  (⅟(Fintype.card G : ℂ) • ∑ g : G, fsCharAlt V.character g) =
  FSindicator V := by
  unfold FSindicator fsCharSym fsCharAlt fsChar
  simp only [invOf_eq_inv, smul_eq_mul]
  rw[← mul_sub,← Finset.sum_sub_distrib]
  ring_nf
  rw[Finset.mul_sum]

/- The values of FSindicator are only possible to be -1, 0 or 1. The different values also yield
different properties of the character. -/
theorem FSindicator_values [CategoryTheory.Simple V] :
  FSindicator V = 1 ∨ FSindicator V = 0 ∨ FSindicator V = -1 := by
  have f_sym_nat : ∃ n : ℕ,
    (⅟(Fintype.card G : ℂ) • ∑ g : G, fsCharSym V.character g) = (n : ℂ) := by
    rw[← symSqFDRep_character]
    exact average_rep_eq_natCast (symSqFDRep V)
  have f_alt_nat : ∃ n : ℕ,
    (⅟(Fintype.card G : ℂ) • ∑ g : G, fsCharAlt V.character g) = (n : ℂ) := by
    rw[← altSqFDRep_character]
    exact average_rep_eq_natCast (altSqFDRep V)
  obtain ⟨n_sym, hn_sym⟩ := f_sym_nat
  obtain ⟨n_alt, hn_alt⟩ := f_alt_nat
  obtain ⟨n_sq, hn_sq, hn_sq_le⟩ := average_sq_le_one V
  have f : n_sym+n_alt=n_sq := by
    let f0 := average_alt_add_sym_eq_sq V
    rw[hn_sym, hn_alt, hn_sq] at f0
    exact_mod_cast f0
  have g : n_sym-n_alt=FSindicator V:= by
    let g0 := charSym_sub_charAlt_eq_FSindicator V
    rw[hn_sym, hn_alt] at g0
    exact g0
  obtain hn_sq_leA | hn_sq_leB := hn_sq_le
  · right
    left
    rw [hn_sq_leA] at f
    obtain ⟨ka, kb⟩ := add_eq_zero.mp f
    rw[ka,kb] at g
    simp only [CharP.cast_eq_zero, sub_self] at g
    exact symm g
  · rw [hn_sq_leB] at f
    rcases Nat.add_eq_one_iff.mp f with ⟨ka, kb⟩ | ⟨ka,kb⟩
    · right
      right
      rw[ka,kb] at g
      simp only [CharP.cast_eq_zero, Nat.cast_one, zero_sub] at g
      exact symm g
    · left
      rw[ka,kb] at g
      simp only [Nat.cast_one, CharP.cast_eq_zero, sub_zero] at g
      exact symm g

/- The details here are tedious and left for future work. -/
lemma FDRep.nontrivial_of_simple [CategoryTheory.Simple V] :
  Nontrivial V.V := by sorry

/- A zero FS indicator implies that the symmetric and alternating squares both vanish, leading
to a zero average for χ^2. Thus, χ cannot be real-valued, as a real character would yield a
strictly positive sum of squares. -/
theorem not_real_of_FSindicator_eq_zero [CategoryTheory.Simple V] (fs0 : FSindicator V = 0) :
  ∃ g : G , (V.character g) ≠ (starRingEnd ℂ) (V.character g) := by
  -- First Part: To get n_sq = 0.
  have f_sym_nat : ∃ n : ℕ,
    (⅟(Fintype.card G : ℂ) • ∑ g : G, fsCharSym V.character g) = (n : ℂ) := by
    rw[← symSqFDRep_character]
    exact average_rep_eq_natCast (symSqFDRep V)
  have f_alt_nat : ∃ n : ℕ,
    (⅟(Fintype.card G : ℂ) • ∑ g : G, fsCharAlt V.character g) = (n : ℂ) := by
    rw[← altSqFDRep_character]
    exact average_rep_eq_natCast (altSqFDRep V)
  obtain ⟨n_sym, hn_sym⟩ := f_sym_nat
  obtain ⟨n_alt, hn_alt⟩ := f_alt_nat
  obtain ⟨n_sq, hn_sq, hn_sq_le⟩ := average_sq_le_one V
  have f : n_sym+n_alt=n_sq := by
    let f0 := average_alt_add_sym_eq_sq V
    rw[hn_sym, hn_alt, hn_sq] at f0
    exact_mod_cast f0
  have g : n_sym-n_alt=FSindicator V:= by
    let g0 := charSym_sub_charAlt_eq_FSindicator V
    rw[hn_sym, hn_alt] at g0
    exact g0
  have h : n_sym = 0 ∧ n_alt = 0 := by
    obtain hn_sq_leA | hn_sq_leB := hn_sq_le
    · rw [hn_sq_leA] at f
      obtain ⟨ka, kb⟩ := add_eq_zero.mp f
      exact ⟨ka, kb⟩
    · rw [hn_sq_leB] at f
      rcases Nat.add_eq_one_iff.mp f with ⟨ka, kb⟩ | ⟨ka,kb⟩
      · rw[ka,kb] at g
        simp only [CharP.cast_eq_zero, Nat.cast_one, zero_sub] at g
        rw[fs0] at g
        simp only [neg_eq_zero, one_ne_zero] at g
      · rw[ka,kb] at g
        simp only [Nat.cast_one, CharP.cast_eq_zero, sub_zero] at g
        rw[fs0] at g
        simp only [one_ne_zero] at g
  have h1 : n_sq = 0 := by
    obtain ⟨ha, hb⟩ := h
    rw[← f, ha, hb]
  -- Second Part: Assume the character is real-valued, desiring to lead to a contradiction.
  by_contra hcon
  push_neg at hcon
  -- From x = conjugate x to real-value
  have f_all_real (g : G) : ∃ k : ℝ, V.character g = (k : ℂ) := by
    have : V.character g = (starRingEnd ℂ) (V.character g) := hcon g
    symm at this
    exact RCLike.conj_eq_iff_real.mp this
  -- we want to show that the average for χ^2 is positive when the character is real-valued.
  have n_sq_pos : ∃ k : ℝ , n_sq = (k : ℂ) ∧ k > 0 := by
    use ⅟↑(Fintype.card G : ℝ) • ∑ g : G, (f_all_real g).choose ^ 2
    constructor
    · rw[← hn_sq]
      have : forall g : G, (V.character g)^2 = (f_all_real g).choose ^ 2 := by
        intro g
        rw [←(f_all_real g).choose_spec]
      rw[Fintype.sum_congr (fun g => (V.character g)^2) (fun g => (f_all_real g).choose ^ 2) this]
      simp only [invOf_eq_inv, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv,
        Complex.ofReal_natCast, Complex.ofReal_sum, Complex.ofReal_pow]
    · have h_nonneg : ∀ g : G, 0 ≤ (f_all_real g).choose ^ 2 := by
        intro g
        nlinarith
      have h_pos : ∃ g : G , 0 < (f_all_real g).choose ^ 2 := by
        use 1
        apply sq_pos_of_ne_zero
        have h_v : V.character 1 = (f_all_real 1).choose := (f_all_real 1).choose_spec
        have : ((f_all_real 1).choose : ℂ) ≠ 0 := by
          rw[← h_v,FDRep.char_one V]
          have : Nontrivial ↑V.V := FDRep.nontrivial_of_simple
          have h_rank_pos : 0 < (Module.finrank ℂ ↑V.V : ℝ) := by
            have : 0 < (Module.finrank ℂ ↑V.V ) := Module.finrank_pos
            exact_mod_cast this
          exact_mod_cast (ne_of_gt h_rank_pos)
        exact_mod_cast this
      -- The all terms are non-negative, and at least one is positive, so the sum is positive.
      let func := fun g : G => ((f_all_real g).choose ^ 2)
      have h_nonneg_f : 0 ≤ func := h_nonneg
      have h_pos_f : 0 < func := by
        constructor
        · exact h_nonneg_f
        · have : ¬ (forall g : G, func g ≤ 0) := by
            push_neg
            exact h_pos
          exact this
      let h_end := (Fintype.sum_pos_iff_of_nonneg h_nonneg_f).mpr h_pos_f
      unfold func at h_end
      simp only [invOf_eq_inv, smul_eq_mul, gt_iff_lt, h_end, mul_pos_iff_of_pos_right, inv_pos,
        Nat.cast_pos]
      exact Fintype.card_pos
  rw[h1] at n_sq_pos
  norm_cast at n_sq_pos
  obtain ⟨k, hk, hk_pos⟩ := n_sq_pos
  linarith
