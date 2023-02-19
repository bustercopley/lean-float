import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Algebra.Order.Monoid.WithTop

import Fl.Lemmas
import Fl.Trunc

namespace Fl.Round

namespace Defs
axiom round : ℕ → ℕ
end Defs

open Defs
open Fl.Trunc.Defs

axiom a1 (x : ℕ) : round x = trunc x ∨ round x = next (trunc x)
axiom a2 {x : ℕ} : round x = trunc x → x - trunc x ≤ next (trunc x) - x
axiom a3 {x : ℕ} : round x = next (trunc x) → next (trunc x) - x ≤ x - trunc x

theorem a2' {x : ℕ} (h : x - trunc x < next (trunc x) - x) :
  round x = trunc x :=
    Or.elim (a1 x) (fun l => l) (fun r => False.elim ((not_lt_of_ge (a3 r)) h))

theorem a3' {x : ℕ} (h : next (trunc x) - x < x - trunc x) :
  round x = next (trunc x) :=
    Or.elim (a1 x) (fun l => False.elim ((not_lt_of_ge (a2 l)) h)) (fun r => r)

theorem a0 (x : ℕ) : trunc x = x ↔ round x = x := by
  constructor
  -- ⊢ trunc x = x → round x = x
  . intro h
    apply h ▸ a2'
    rw [Nat.sub_self]
    exact Nat.sub_pos_of_lt (Trunc.lt_next x)
  -- ⊢ round x = x → trunc x = x
  . intro h
    cases a1 x with
    | inl k => exact k ▸ h
    | inr k =>
      rw [h] at k
      apply absurd
      . exact Trunc.lt_next_trunc x
      . exact not_lt_iff_eq_or_lt.mpr (Or.inl k)

theorem a0' {x : ℕ} (h : trunc x = x) : round x = trunc x := by rwa [h, ← a0]

theorem a2'' {x : ℕ} (h : x < trunc x + ulp x / 2) :
  round x = trunc x := by
  cases lt_or_ge n x.size with
  | inr size_le => -- size_le : x.size ≤ n
    apply a0'
    unfold trunc sig ulp expt
    rw [Nat.sub_eq_zero_of_le size_le]
    rw [Nat.pow_zero, Nat.mul_one, Nat.div_one]
  | inl lt_size => -- lt_size : n < x.size
    have expt_pos : 0 < x.size - n := lt_tsub_of_add_lt_left lt_size
    have ulp_even : 2 ∣ ulp x := dvd_pow_self _ (ne_zero_of_lt expt_pos)
    apply a2'
    rw [tsub_lt_iff_left (Trunc.trunc_le x)]
    rw [← Nat.add_sub_assoc (le_of_lt (Trunc.lt_next_trunc x))]
    -- ⊢ x < trunc x + next (trunc x) - x
    unfold next
    rw [Trunc.ulp_trunc_eq_ulp]
    rw [lt_tsub_iff_left]
    rw [← Nat.add_assoc]
    rw [← Nat.div_mul_cancel ulp_even]
    rw [← mul_two, ← mul_two, ← add_mul]
    exact Nat.mul_lt_mul_of_pos_right h two_pos

theorem a3'' {x : ℕ} (h : trunc x + ulp x / 2 < x) :
  round x = next (trunc x) := by
  cases lt_or_ge n x.size with
  | inr size_le => -- size_le : n ≥ x.size
    rw [ge_iff_le, Nat.size_le] at size_le
    rw [Trunc.trunc_eq_self_of_lt size_le] at h
    exact absurd (Nat.le_add_right _ _) (not_le_of_gt h)
  | inl lt_size => -- lt_size : n < Nat.size x
    have expt_pos : 0 < x.size - n := lt_tsub_of_add_lt_left lt_size
    have ulp_even : 2 ∣ ulp x := dvd_pow_self _ (ne_zero_of_lt expt_pos)
    apply a3'
    rw [tsub_lt_iff_left (le_of_lt (Trunc.lt_next_trunc x))]
    rw [←Nat.add_sub_assoc (Trunc.trunc_le x)]
    unfold next
    rw [Trunc.ulp_trunc_eq_ulp]
    rw [lt_tsub_iff_left]
    rw [← Nat.add_assoc]
    rw [← Nat.div_mul_cancel ulp_even]
    rw [← mul_two, ← mul_two, ← add_mul]
    exact Nat.mul_lt_mul_of_pos_right h two_pos

theorem trunc_add_half_ulp_eq_of_size_le {x : ℕ} (size_le : x < 2 ^ n)
  : trunc x + ulp x / 2 = x := by
  unfold trunc sig
  rw [Trunc.ulp_eq_one_of_lt size_le]
  rw [Nat.mul_one, Nat.div_one, Nat.div_eq_zero one_lt_two, Nat.add_zero]

theorem trunc_add_half_ulp_eq_of_lt_size {x : ℕ} (lt_size : 2 ^ n ≤ x) :
  2 * (trunc x + ulp x / 2) = trunc x + next (trunc x) := by
  have ulp_even := Trunc.two_dvd_ulp_of_ge lt_size
  rw [Nat.left_distrib, Nat.two_mul, Nat.add_assoc, Nat.mul_comm,
      Nat.div_mul_cancel ulp_even, ← Trunc.ulp_trunc_eq_ulp, next]

theorem round_eq_trunc_add_half {x : ℕ} :
  x = trunc x + ulp x / 2 ∨ round x = trunc (x + ulp x / 2) := by
  cases lt_or_ge n x.size with
  | inr size_le => -- size_le : n ≥ x.size
    apply Or.inl
    unfold trunc sig ulp expt
    rw [Nat.sub_eq_zero_of_le size_le, Nat.pow_zero, Nat.div_one, Nat.mul_one]
    rw [Nat.div_eq_of_lt one_lt_two, Nat.add_zero]
  | inl lt_size => -- lt_size : n < x.size
    cases eq_or_ne x (trunc x + ulp x / 2) with
    | inl eq => exact Or.inl eq
    | inr ne => -- ne : x ≠ trunc x + ulp x / 2
      apply Or.inr
      have expt_pos : 0 < expt x := Nat.zero_lt_sub_of_lt lt_size
      have ulp_even : 2 ∣ ulp x := dvd_pow_self 2 (ne_zero_of_lt expt_pos)
      cases le_or_gt x (trunc x + ulp x / 2) with
      | inl le => -- le : x ≤ trunc x + ulp x / 2
        have lt := Nat.lt_of_le_of_ne le ne
        rw [a2'' lt]
        apply Trunc.trunc_eq_trunc_of_trunc_le_of_lt_next_trunc
        .  exact Nat.le_trans (Trunc.trunc_le x) (Nat.le_add_right _ _)
        .  rw [next, Trunc.ulp_trunc_eq_ulp]
           rw [← lt_tsub_iff_right]
           rw [add_tsub_assoc_of_le (Nat.div_le_self _ _)]
           rw [Fl.Lemmas.sub_half_of_even ulp_even]
           exact lt
      | inr gt => -- gt : x > trunc x + ulp x / 2
        rw [a3'' gt]
        rw [← Trunc.trunc_next_comm]
        apply Trunc.trunc_eq_trunc_of_trunc_le_of_lt_next_trunc
        . rw [Trunc.trunc_next_comm, next, Trunc.ulp_trunc_eq_ulp]
          rw [← tsub_le_iff_right]
          rw [add_tsub_assoc_of_le (Nat.div_le_self _ _)]
          rw [Fl.Lemmas.sub_half_of_even ulp_even]
          exact le_of_lt gt
        . rw [next, Trunc.ulp_trunc_eq_ulp]
          apply add_lt_add_of_lt_of_le (Trunc.lt_trunc_next x)
          transitivity ulp x
          . exact Nat.div_le_self _ _
          . apply Trunc.ulp_le_ulp
            exact Nat.le_add_right _ _

theorem nearest {x : ℕ} :
  (round x = trunc x ∧ x - trunc x ≤ next (trunc x) - x) ∨
  (round x = next (trunc x) ∧ next (trunc x) - x ≤ x - trunc x) :=
  Or.elim (a1 x) (fun lo => Or.inl ⟨lo, a2 lo⟩) (fun hi => Or.inr ⟨hi, a3 hi⟩)

theorem trunc_le_round (x : ℕ) : trunc x ≤ round x :=
  Or.elim (a1 x) ge_of_eq (fun hi => hi.symm ▸ Nat.le_add_right _ _)

theorem round_le_next_trunc (x : ℕ) : round x ≤ next (trunc x) :=
  Or.elim (a1 x) (fun lo => lo.symm ▸ Nat.le_add_right _ _) le_of_eq

end Fl.Round
