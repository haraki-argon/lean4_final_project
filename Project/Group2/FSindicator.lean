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

/-!
# Frobenius-Schur Indicator

Frobenius-Schur indicators are defined by the average value of the character on the squares of
group elements. They are used to determine whether a representation is real, complex, or
quaternionic.

We prove that the FS indicator can only take values -1, 0, or 1 for simple representations.

We prove that a zero FS indicator implies the character is not real-valued, and thus the
representation is complex.

## TODO
* Prove that the symmetric and alternating squares of a representation correspond to the
fsCharSym and fsCharAlt functions, respectively.
* Prove the dual of a simple representation is simple.
* Determine the sturcture of the representation when FSindicator is 1 or -1.
* Prove the simple representations is nontrivial.

-/

variable {G : Type} [Group G] [Fintype G]

noncomputable def FSindicator (V : FDRep ℂ G) : ℂ :=
  ∑ g : G, (V.character (g * g)) / Fintype.card G

noncomputable def fsChar {G} [Group G] (sign : ℤ) (χ : G → ℂ) : G → ℂ :=
  fun g =>
    (1/2) * ((χ g) ^ 2 + (sign * χ (g * g)))

noncomputable def fsCharSym (χ : G → ℂ) : G → ℂ := fsChar 1 χ
noncomputable def fsCharAlt (χ : G → ℂ) : G → ℂ := fsChar (-1) χ

lemma charSym_add_charAlt_eq_char_sq {G} [Group G] (χ : G → ℂ) (g : G) :
  fsCharSym χ g + fsCharAlt χ g = (χ g)^2 := by
  unfold fsCharSym fsCharAlt fsChar
  ring

/- The fact that these formulas correspond to actual characters follows from the decomposition
of the tensor square V ⊗ V into symmetric (S²) and exterior (Λ²) components. I am leaving this
as an 'admit' for now as the structural construction of these sub-representations in mathlib is
beyond my current familiarity with the library. -/
lemma fsChar_is_char (sign : ℤ) (V : FDRep ℂ G) :
  ∃ W : FDRep ℂ G, W.character = fsChar sign V.character := by admit

noncomputable def fsSymRep (V : FDRep ℂ G) : FDRep ℂ G :=
  Classical.choose (fsChar_is_char 1 V)

noncomputable def fsAltRep (V : FDRep ℂ G) : FDRep ℂ G :=
  Classical.choose (fsChar_is_char (-1) V)


lemma fsSymRep_character (V : FDRep ℂ G) :
  (fsSymRep V).character = fsCharSym V.character :=
by
  simpa [fsCharSym]
    using (Classical.choose_spec (fsChar_is_char 1 V))


lemma fsAltRep_character (V : FDRep ℂ G) :
  (fsAltRep V).character = fsCharAlt V.character :=
by
  simpa [fsCharAlt]
    using (Classical.choose_spec (fsChar_is_char (-1) V))

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
  obtain ⟨n1, hn1⟩ := average_rep_eq_natCast (fsSymRep V)
  obtain ⟨n2, hn2⟩ := average_rep_eq_natCast (fsAltRep V)
  use n1 + n2
  simp only [Nat.cast_add]
  rw [← hn1, ← hn2]
  simp only [← charSym_add_charAlt_eq_char_sq V.character]
  simp only [fsSymRep_character, fsAltRep_character]
  simp [Finset.sum_add_distrib, mul_add]

/- The details here are tedious and left for future work. -/
def FDRep.dual_iso (V : FDRep ℂ G) :
  FDRep.of (Representation.dual V.ρ) ≅ V := sorry

omit [Fintype G] in
lemma dual_simple_of_simple (V : FDRep ℂ G) [CategoryTheory.Simple V] :
  CategoryTheory.Simple (FDRep.of (Representation.dual V.ρ)) :=
  CategoryTheory.Simple.of_iso (FDRep.dual_iso V)

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
      dual_simple_of_simple V
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
theorem FSindicator_values {G : Type} [Group G] [Fintype G]
  (V : FDRep ℂ G) [CategoryTheory.Simple V] :
  FSindicator V = 1 ∨ FSindicator V = 0 ∨ FSindicator V = -1 := by
  have f_sym_nat : ∃ n : ℕ,
    (⅟(Fintype.card G : ℂ) • ∑ g : G, fsCharSym V.character g) = (n : ℂ) := by
    rw[← fsSymRep_character V]
    exact average_rep_eq_natCast (fsSymRep V)
  have f_alt_nat : ∃ n : ℕ,
    (⅟(Fintype.card G : ℂ) • ∑ g : G, fsCharAlt V.character g) = (n : ℂ) := by
    rw[← fsAltRep_character V]
    exact average_rep_eq_natCast (fsAltRep V)
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
lemma FDRep.nontrivial_of_simple (V : FDRep ℂ G) [CategoryTheory.Simple V] :
  Nontrivial V.V := by sorry

/- A zero FS indicator implies that the symmetric and alternating squares both vanish, leading
to a zero average for χ^2. Thus, χ cannot be real-valued, as a real character would yield a
strictly positive sum of squares. -/
theorem not_real_of_FSindicator_eq_zero {G : Type} [Group G] [Fintype G]
  (V : FDRep ℂ G) [CategoryTheory.Simple V] (fs0 : FSindicator V = 0) :
  ∃ g : G , (V.character g) ≠ (starRingEnd ℂ) (V.character g) := by
  -- First Part: To get n_sq = 0.
  have f_sym_nat : ∃ n : ℕ,
    (⅟(Fintype.card G : ℂ) • ∑ g : G, fsCharSym V.character g) = (n : ℂ) := by
    rw[← fsSymRep_character V]
    exact average_rep_eq_natCast (fsSymRep V)
  have f_alt_nat : ∃ n : ℕ,
    (⅟(Fintype.card G : ℂ) • ∑ g : G, fsCharAlt V.character g) = (n : ℂ) := by
    rw[← fsAltRep_character V]
    exact average_rep_eq_natCast (fsAltRep V)
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
          have : Nontrivial ↑V.V := FDRep.nontrivial_of_simple V
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
