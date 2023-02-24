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

namespace Faithful

-- Faithful axioms
axiom a0 {x : ℕ} : trunc x = x → round x = x
axiom a1 (x : ℕ) : round x = trunc x ∨ round x = next (trunc x)

theorem trunc_eq_iff_round_eq (x : ℕ) : trunc x = x ↔ round x = x := by
  constructor
  . intro l
    exact a0 l
  . intro r
    cases a1 x with
    | inl lo => exact lo ▸ r
    | inr hi =>
      rw [r] at hi
      apply absurd
      . exact Trunc.lt_next_trunc x
      . exact Eq.not_lt hi

theorem round_eq_trunc_of_trunc_eq {x : ℕ} (h : trunc x = x) :
  round x = trunc x :=
  by rwa [h, ← trunc_eq_iff_round_eq]

theorem trunc_le_round (x : ℕ) : trunc x ≤ round x :=
  Or.elim (a1 x) ge_of_eq (fun hi => hi.symm ▸ Nat.le_add_right _ _)

theorem round_le_next_trunc (x : ℕ) : round x ≤ next (trunc x) :=
  Or.elim (a1 x) (fun lo => lo.symm ▸ Nat.le_add_right _ _) le_of_eq

theorem round_idempotent (x : ℕ) : round (round x) = round x := by
  cases a1 x with
  | inl lo => rw [← trunc_eq_iff_round_eq, lo, Trunc.trunc_idempotent]
  | inr hi => rw [← trunc_eq_iff_round_eq, hi, Trunc.trunc_next_comm,
                  Trunc.trunc_idempotent]

theorem trunc_round_eq_round (x : ℕ) : trunc (round x) = round (x) := by
  rw [trunc_eq_iff_round_eq]
  exact round_idempotent x

theorem round_trunc_eq_trunc (x : ℕ) : round (trunc x) = trunc (x) := by
  rw [← trunc_eq_iff_round_eq]
  exact Trunc.trunc_idempotent x

theorem round_eq_trunc_of_le {a : ℕ} (h : round a ≤ a) : round a = trunc a := by
  cases a1 a with
  | inl hlo => exact hlo
  | inr hhi =>
    exfalso
    apply Nat.lt_le_antisymm (Trunc.lt_next_trunc a)
    apply Nat.le_trans (m := round a)
    . exact ge_of_eq hhi
    . exact h

theorem round_le_trunc_of_le_trunc {x y : ℕ} (h : y ≤ trunc x) :
  round y ≤ trunc x := by
  cases Nat.lt_or_eq_of_le h with
  | inl lt => -- lt : y < trunc x
    have pos := Nat.zero_lt_of_lt lt
    rw [← Trunc.next_trunc_pred_eq_self' pos]
    apply Nat.le_trans (round_le_next_trunc y)
    apply Trunc.next_le_next
    apply Trunc.trunc_le_trunc
    rw [← Nat.lt_iff_le_pred pos]
    exact lt
  | inr eq => -- eq : y = trunc x
    rw [eq, round_trunc_eq_trunc]

end Faithful

namespace Correct

open Faithful

-- Correctly rounding axioms
axiom a2 {x : ℕ} : round x = trunc x → x - trunc x ≤ next (trunc x) - x
axiom a3 {x : ℕ} : round x = next (trunc x) → next (trunc x) - x ≤ x - trunc x

theorem a2' {x : ℕ} (h : x - trunc x < next (trunc x) - x) :
  round x = trunc x :=
    Or.elim (a1 x) (fun l => l) (fun r => False.elim ((not_lt_of_ge (a3 r)) h))

theorem a3' {x : ℕ} (h : next (trunc x) - x < x - trunc x) :
  round x = next (trunc x) :=
    Or.elim (a1 x) (fun l => False.elim ((not_lt_of_ge (a2 l)) h)) (fun r => r)

theorem a2'' {x : ℕ} (h : x < trunc x + ulp x / 2) :
  round x = trunc x := by
  cases lt_or_ge n x.size with
  | inr size_le => -- size_le : x.size ≤ n
    apply Faithful.round_eq_trunc_of_trunc_eq
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

theorem a2''' {x : ℕ} (hf : round x = trunc x) :
  x ≤ trunc x + ulp x / 2 := by
  cases Nat.lt_or_ge x (2 ^ n) with
  | inl size_le =>
    exact ge_of_eq (Trunc.trunc_add_half_ulp_eq_of_size_le size_le)
  | inr lt_size =>
    refine Nat.le_of_mul_le_mul_left ?_ two_pos
    rw [Trunc.trunc_add_half_ulp_eq_of_lt_size lt_size]
    have h1 : x ≤ next (trunc x) := Nat.le_of_lt (Trunc.lt_next_trunc x)
    have h2 : trunc x ≤ x := Trunc.trunc_le _
    rw [Nat.two_mul, ← tsub_le_iff_left, Nat.add_sub_assoc h2, Nat.add_comm,
        ← Nat.le_sub_iff_add_le h1]
    exact a2 hf

theorem a3''' {x : ℕ} (hf : round x = next (trunc x)) :
  trunc x + ulp x / 2 ≤ x := by
  cases Nat.lt_or_ge x (2 ^ n) with
  | inl size_le =>
    exact le_of_eq (Trunc.trunc_add_half_ulp_eq_of_size_le size_le)
  | inr lt_size =>
    refine Nat.le_of_mul_le_mul_left ?_ two_pos
    rw [Trunc.trunc_add_half_ulp_eq_of_lt_size lt_size]
    have h1 : x ≤ next (trunc x) := Nat.le_of_lt (Trunc.lt_next_trunc x)
    have h2 : trunc x ≤ x := Trunc.trunc_le _
    rw [Nat.two_mul, ← tsub_le_iff_left, Nat.add_sub_assoc h1, Nat.add_comm,
        ← Nat.le_sub_iff_add_le h2]
    exact a3 hf

theorem round_eq_trunc_add_half {x : ℕ} :
  x = trunc x + ulp x / 2 ∨ round x = trunc (x + ulp x / 2) := by
  cases Nat.lt_or_ge x (2 ^ n) with
  | inl size_le => -- size_le : x < 2 ^ n
    apply Or.inl
    rw [Trunc.trunc_add_half_ulp_eq_of_size_le size_le]
  | inr lt_size => -- lt_size : n < x.size
    cases eq_or_ne x (trunc x + ulp x / 2) with
    | inl eq => exact Or.inl eq
    | inr ne => -- ne : x ≠ trunc x + ulp x / 2
      apply Or.inr
      rw [ge_iff_le, ← Nat.lt_size] at lt_size
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

theorem round_le_round {a b : ℕ}  (hle : a ≤ b) : round a ≤ round b := by
  have lolo : trunc a ≤ trunc b := Trunc.trunc_le_trunc hle
  have lohi : trunc a ≤ next (trunc b) :=
    Nat.le_trans lolo (Nat.le_add_right _ _)
  have hihi : next (trunc a) ≤ next (trunc b) :=
    Nat.add_le_add lolo (Trunc.ulp_le_ulp lolo)
  rcases a1 a, (a1 b).symm with ⟨alo | ahi, bhi | blo⟩
  . rwa [alo, bhi]
  . rwa [alo, blo]
  . rwa [ahi, bhi]
  . cases eq_or_ne a b with
    | inl eq => exact eq ▸ le_rfl
    | inr ne =>
      rw [ahi, blo]
      apply Nat.le_of_not_lt
      intro (lt_next_trunc : trunc b < next (trunc a))
      have trunc_eq : trunc b = trunc a := by
        apply Nat.le_antisymm
        . rw [← Trunc.trunc_idempotent b]
          exact Trunc.trunc_le_trunc_of_lt_next_trunc lt_next_trunc
        . exact lolo
      have ulp_eq : ulp b = ulp a := by
        rw [← Trunc.ulp_trunc_eq_ulp a, ← Trunc.ulp_trunc_eq_ulp b, trunc_eq]
      apply Nat.lt_le_antisymm (lt_of_le_of_ne hle ne)
      apply Nat.le_trans (m := trunc b + ulp b / 2)
      . exact a2''' blo
      . rw [trunc_eq, ulp_eq]
        exact a3''' ahi

end Correct

end Fl.Round
