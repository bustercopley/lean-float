import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Algebra.Order.Monoid.WithTop

import Fl.Lemmas
import Fl.Trunc
import Fl.Round

namespace Fl

open Trunc.Defs
open Round.Defs

-- On Properties of Floating Point Arithmetics: Numerical Stability
-- and the Cost of Accurate Computations
-- Douglas M. Priest (1992) (Ph. D. Thesis)

-- For all x ∈ ℕ we say is a *floating point number* if trunc x = x.

-- A *floating point arithmetic* is a mapping which assigns to each
-- triple (a, b, ∘) where a and b are floating point numbers and ∘ is one of
-- the operations + - × / another floating point number fl (a ∘ b), provided
-- b ≠ 0 when ∘ is /.

-- The arithmetic is *faithful* if:
-- (i)  Whenever a ∘ b is a floating point number, fl (a ∘ b) = a ∘ b
-- (ii) Otherwise, fl (a ∘ b) is either ⌈a ∘ b⌉ or ⌊a ∘ b⌋

-- Sterbenz' Lemma (Priest, p. 12):
--    If a and b are floating point numbers such that 1 / 2 ≤ a / b ≤ 2
--    then a - b is also a floating point number.

-- We prove the statement in the case 0 ≤ b ≤ a ≤ 2 * b. (Then 1 ≤ a / b ≤ 2.)
-- When 0 ≤ a < b ≤ 2 * a, the same argument with a and b exchanged shows that
-- the nonnegative b - a is a floating point number.

theorem sterbenz {a b : ℕ}
  (hl : b ≤ a) (hr : a ≤ 2 * b) (hfa : trunc a = a) (hfb : trunc b = b) :
  trunc (a - b) = a - b := by
  rw [Nat.two_mul] at hr
  apply Trunc.trunc_eq_of_le_of_ulp_dvd
  . exact Nat.sub_le_of_le_add hr
  . apply Nat.dvd_sub'
    . exact dvd_trans (Trunc.ulp_dvd_ulp hl) (Trunc.ulp_dvd_of_trunc_eq hfa)
    . exact Trunc.ulp_dvd_of_trunc_eq hfb

-- Conditions for exact subtraction: properties S1 - S3 (Priest, p. 9)

-- If a, b, c are floating point numbers, define

-- S1 : If 0 ≤ a ≤ c ≤ b and fl (b - a) = b - a exactly
--      then fl (c - a) = c - a  exactly (and similarly if 0 ≥ a ≥ b)
-- S2 : If 0 ≤ a ≤ b and c = fl (b - a) then fl (b - c) = b - c exactly
--      (and similarly if 0 ≥ a ≥ b)
-- S3 : If 0 ≤ ulp (b) / 2 ≤ a ≤ b and c = fl (b - fl (b - a) satisfies c > a
--      then fl (c - d) = c - d exactly for all d ∈ [a, c] (and similarly if
--      0 ≥ -ulp (b) / 2 ≥ a ≥ b).

-- Subtraction is *antisymmetric* if fl (a - b) = -fl (b - a) for all a and b.
-- It is *monotonic* if a ≤ b implies fl (a - c) ≤ fl (b - c) for all c.

-- We prove that all faithful arithmetics have properties S1 - S3.
-- Note that S1 does not involve rounding.

-- Part of the inductive step of the proof for property S1:
-- Let a and b be floating point numbers such that 2 * a < b.
-- Suppose that b - a is a floating point number.
-- Let c denote the largest floating point number smaller than b.
-- Then c - a is a floating point number.
theorem s1' {a b : ℕ}
  (hf₁ : trunc b = b)
  (hf₂ : trunc (b - a) = b - a)
  (hba : 2 * a < b) :
  trunc (trunc (b - 1) - a) = trunc (b - 1) - a := by
  have hb_pos : 0 < b := Nat.zero_lt_of_lt hba
  have h₁ : trunc (b - 1) = b - ulp (b - 1) := by
    rw [← Nat.add_sub_cancel (trunc (b - 1)) (ulp (b - 1))]
    apply congr_arg (fun w => w - ulp (b -1))
    rw [← Trunc.ulp_trunc_eq_ulp, ← next]
    exact Trunc.next_trunc_pred_eq_self hb_pos hf₁
  rw [h₁]
  rw [Nat.sub.right_comm]
  rw [Trunc.trunc_eq_iff_ulp_dvd]
  apply Nat.dvd_sub'
  . apply dvd_trans (b := ulp (b - a))
    . apply Trunc.ulp_dvd_ulp
      exact Nat.sub_le _ _
    . rw [← Trunc.trunc_eq_iff_ulp_dvd]
      exact hf₂
  . apply Trunc.ulp_dvd_ulp
    rw [Nat.sub.right_comm]
    apply Nat.le_trans (m := b - ulp (b - 1))
    . exact Nat.sub_le _ _
    . apply Nat.sub_le_sub_left
      exact Trunc.ulp_pos _

-- S1 : If 0 ≤ a ≤ c ≤ b and fl (b - a) = b - a exactly
--      then fl (c - a) = c - a  exactly (and similarly if 0 ≥ a ≥ b)
theorem s1 {a b c : ℕ} (hac : a ≤ c) (hcb : c ≤ b)
  (hfa : trunc a = a) (hfb : trunc b = b) (hfc : trunc c = c)
  (hf : trunc (b - a) = b - a) :
  trunc (c - a) = c - a :=
by
  have h : ∀ k : ℕ,
           2 * a < b - k →
           trunc (trunc (b - k) - a) = trunc (b - k) - a := by
    intro k
    induction k with
    | zero =>
      rw [Nat.sub_zero, hfb]
      exact fun _ => hf
    | succ k ih =>
      rw [Nat.sub_succ']
      intro (hb₂a : 2 * a < b - k - 1)
      have hb₁a : 2 * a < b - k := by
        apply Nat.lt_of_lt_of_le (m := b - k - 1)
        . exact hb₂a
        . exact Nat.sub_le _ _
      replace ih := ih hb₁a
      cases eq_or_ne (trunc (b - k)) (b - k) with
      | inr ne =>
        have eq : trunc (b - k - 1) = trunc (b - k) :=
          Trunc.trunc_pred_eq_trunc_of_trunc_ne_self ne
        exact eq ▸ ih
      | inl hfb₁ =>
        rw [hfb₁] at ih
        exact s1' hfb₁ ih hb₁a
  cases le_or_gt c (2 * a) with
  | inl hle => exact sterbenz hac hle hfc hfa
  | inr hgt =>
    replace h := h (b - c)
    rw [Nat.sub_sub_self hcb, hfc] at h
    exact h hgt

-- S2 : If 0 ≤ a ≤ b and c = fl (b - a) then fl (b - c) = b - c exactly
--      (and similarly if 0 ≥ a ≥ b)
theorem s2 {a b : ℕ} (hab : a ≤ b)
  (hfa : trunc a = a) (hfb : trunc b = b) :
  trunc (b - round (b - a)) = b - round (b - a) := by
  cases Nat.lt_or_ge (2 * a) b with
  | inr hba => -- ge : 2 * a ≥ b
    have hf : round (b - a) = b - a := by
      rw [← Round.a0]
      exact sterbenz hab hba hfb hfa
    rw [hf, Nat.sub_sub_self hab]
    exact hfa
  | inl hab' => -- lt : 2 * a < b
    apply sterbenz
    . rw [Round.a0] at hfb
      apply Nat.le_trans (m := round b)
      . apply Round.round_le_round
        exact Nat.sub_le _ _
      . exact Nat.le_of_eq hfb
    . apply Nat.le_trans (m := 2 * trunc (b - a))
      . rw [← pow_one 2, ← Trunc.trunc_pow_mul, pow_one]
        apply Nat.le_trans (m := trunc b)
        . rw [hfb]
        . apply Trunc.trunc_le_trunc
          rw [Nat.mul_sub_left_distrib, Nat.two_mul,
              Nat.add_sub_assoc (le_of_lt hab')]
          exact Nat.le_add_right _ _
      . apply Nat.mul_le_mul_left
        exact Round.trunc_le_round _
    . exact hfb
    . exact Round.a0'' _

-- Inner part of the proof for property S3.
-- Let b be a floating point number such that 0 ≤ a ≤ b and ulp b ≤ 2 * a.
-- Let b' be the greatest floating point number not greater than b - a.
-- Then b - b' ≤ 2 * a.
theorem s3' {a b : ℕ} (hfb : trunc b = b) (h : ulp b ≤ 2 * a) :
  b - trunc (b - a) ≤ 2 * a := by
  cases Nat.lt_or_ge a (ulp b) with
  | inl lt_ulp =>
    apply Nat.le_trans (m := ulp b)
    . rw [tsub_le_iff_tsub_le]
      rw [← Trunc.trunc_sub_ulp_eq_of_trunc_eq hfb]
      apply Trunc.trunc_le_trunc
      exact Nat.sub_le_sub_left _ (Nat.le_of_lt lt_ulp)
    . exact h
  | inr ulp_le =>
    apply Nat.le_trans (m := a + ulp b)
    . apply Nat.le_add_of_sub_le
      rw [Nat.sub_sub]
      rw [tsub_le_iff_tsub_le]
      apply Nat.le_trans (m := trunc (b - a) + ulp (b - a))
      . rw [← Trunc.ulp_trunc_eq_ulp]
        exact Nat.le_of_lt (Trunc.lt_next_trunc _)
      . apply Nat.add_le_add_left
        apply Trunc.ulp_le_ulp
        exact Nat.sub_le _ _
    . rw [Nat.two_mul]
      apply Nat.add_le_add_left
      exact ulp_le

-- S3 : If 0 ≤ ulp (b) / 2 ≤ a ≤ b and c = fl (b - fl (b - a) satisfies c > a
--      then fl (c - d) = c - d exactly for all d ∈ [a, c] (and similarly if
--      0 ≥ -ulp (b) / 2 ≥ a ≥ b).
theorem s3 {a b d : ℕ}
  (hfa : trunc a = a) (hfb : trunc b = b) (hfd : trunc d = d)
  (hba : ulp (b) ≤ 2 * a) (hab: a ≤ b)
  (hac : a < round (b - round (b - a)))
  (had : a ≤ d) (hdc : d ≤ round (b - round (b - a))) :
  round (round (b - round (b - a)) - d) = round (b - round (b - a)) - d := by
  have hfc : round (b - round (b - a)) = b - round (b - a) := by
    rw [← Round.a0]
    exact s2 hab hfa hfb
  have helo : round (b - a) < b - a := by
    rw [lt_tsub_comm, ← hfc]
    exact hac
  have hcd : round (b - round (b - a)) ≤ 2 * d := by
    have hfe : round (b - a) = trunc (b - a) :=
      Round.round_eq_trunc_of_le (Nat.le_of_lt helo)
    apply Nat.le_trans (m := 2 * a)
    . rw [hfc, hfe]
      exact s3' hfb hba
    . exact Nat.mul_le_mul_left 2 had
  rw [← Round.a0]
  apply sterbenz
  . exact hdc
  . exact hcd
  . exact Round.a0'' (b - round (b - a))
  . exact hfd