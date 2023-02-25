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

-- The arithmetic is *correctly rounding* if it is faithful and:
-- (i)  fl (a ∘ b) = ⌊a ∘ b⌋ if a ∘ b - ⌊a ∘ b⌋ < ⌈a ∘ b⌉ - a ∘ b
-- (ii) fl (a ∘ b) = ⌈a ∘ b⌉ if a ∘ b - ⌊a ∘ b⌋ > ⌈a ∘ b⌉ - a ∘ b

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
  trunc (c - a) = c - a := by
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
      apply Round.Faithful.a0
      exact sterbenz hab hba hfb hfa
    rw [hf, Nat.sub_sub_self hab]
    exact hfa
  | inl hab' => -- lt : 2 * a < b
    apply sterbenz
    . apply Nat.le_trans (m := trunc b)
      . apply Round.Faithful.round_le_trunc_of_le_trunc
        rw [hfb]
        exact Nat.sub_le _ _
      . exact Trunc.trunc_le _
    . apply Nat.le_trans (m := 2 * trunc (b - a))
      . rw [← pow_one 2, ← Trunc.trunc_pow_mul, pow_one]
        apply Nat.le_trans (m := trunc b)
        . rw [hfb]
        . apply Trunc.trunc_le_trunc
          rw [Nat.mul_sub_left_distrib, Nat.two_mul,
              Nat.add_sub_assoc (le_of_lt hab')]
          exact Nat.le_add_right _ _
      . apply Nat.mul_le_mul_left
        exact Round.Faithful.trunc_le_round _
    . exact hfb
    . exact Round.Faithful.trunc_round_eq_round _

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
  trunc (round (b - round (b - a)) - d) = round (b - round (b - a)) - d := by
  have hfc : round (b - round (b - a)) = b - round (b - a) := by
    rw [← Round.Faithful.trunc_eq_iff_round_eq]
    exact s2 hab hfa hfb
  have helo : round (b - a) < b - a := by
    rw [lt_tsub_comm, ← hfc]
    exact hac
  have hcd : round (b - round (b - a)) ≤ 2 * d := by
    have hfe : round (b - a) = trunc (b - a) :=
      Round.Faithful.round_eq_trunc_of_le (Nat.le_of_lt helo)
    apply Nat.le_trans (m := 2 * a)
    . rw [hfc, hfe]
      exact s3' hfb hba
    . exact Nat.mul_le_mul_left 2 had
  apply sterbenz
  . exact hdc
  . exact hcd
  . exact Round.Faithful.trunc_round_eq_round (b - round (b - a))
  . exact hfd

-- Interval shift

-- Given floating point numbers x, y, z such that x > z, y > z, x ≥ ulp y
-- and y ≥ ulp x, if the floating point subtraction is monotonic and faithful
-- then the following algorithm computes a number s such that
-- round (w - s) = w - s exactly for all w between x and y inclusive.

-- Note the result in Priest (Proposition, p. 10) is much stronger,
-- assuming only monotonicity, antisymmetry and properties S1 to S3

-- float shift (float x, float y, float z) {
--   float t = y - (y - z);
--   float s = x - (x - t);
--   return s;
-- }
theorem interval_shift {x y z w s t : ℕ}
  (h₂ : monotonic₂)
  (hfx : trunc x = x) (hfy : trunc y = y)
  (hfz : trunc z = z) (hfw : trunc w = w)
  (hzx : z < x) (hzy : z < y) (hyx : ulp y ≤ x) (hxy : ulp x ≤ y)
  (ht : t = round (y - round (y - z)))
  (hs₁ : x < t → s = round (x + round (t - x)))
  (hs₂ : t ≤ x → s = round (x - round (x - t)))
  (hxwy : (x ≤ w ∧ w ≤ y) ∨ (y ≤ w ∧ w ≤ x)) :
  trunc (w - s) = w - s ∧ trunc (s - w) = s - w := by
  have hft : trunc t = t := by
    rw [ht]
    exact Round.Faithful.trunc_round_eq_round _
  rcases hxwy with ⟨hxw, hwy⟩ | ⟨hyw, hwx⟩
  . have hfty : trunc (y - t) = y - t := by
      rw [ht]
      apply s2
      . exact Round.Faithful.round_sub_le_of_trunc_eq hfy
      . exact Round.Faithful.trunc_round_eq_round _
      . exact hfy
    cases Nat.lt_or_ge x t with
    | inl hxt =>
      have hft' : t = y - round (y - z) := by
        rw [ht]
        rw [← Round.Faithful.trunc_eq_iff_round_eq]
        apply s2
        . exact hzy.le
        . exact hfz
        . exact hfy
      have hty' : t ≤ y - round (y - x) := by
        rw [hft']
        apply Nat.sub_le_sub_left
        exact h₂ hfz hfx hfy hzx.le
      have hfy' : round (y - round (y - x)) = y - round (y - x) := by
        rw [← Round.Faithful.trunc_eq_iff_round_eq]
        apply s2
        . exact Nat.le_trans hxw hwy
        . exact hfx
        . exact hfy
      have hxyx : x < round (y - round (y - x)) := by
        rw [hfy']
        exact Nat.lt_of_lt_of_le hxt hty'
      have hfxy : trunc (y - round (y - x) - x) = y - round (y - x) - x := by
        rw [← hfy']
        apply s3
        . exact hfx
        . exact hfy
        . exact hfx
        . exact Nat.le_trans hyx (Nat.le_mul_of_pos_left two_pos)
        . exact Nat.le_trans hxw hwy
        . exact hxyx
        . exact le_rfl
        . exact hxyx.le
      have hfxt : trunc (t - x) = t - x := by
        rw [ht]
        apply s1
        . exact Nat.le_of_lt (ht ▸ hxt)
        . exact ht ▸ hty'
        . exact hfx
        . rw [Round.Faithful.trunc_eq_iff_round_eq]
          exact hfy'
        . exact Round.Faithful.trunc_round_eq_round _
        . exact hfxy
      have hst : s = t := by
        rw [hs₁ hxt, Round.Faithful.round_eq_of_trunc_eq hfxt,
            add_tsub_cancel_of_le hxt.le]
        exact Round.Faithful.round_eq_of_trunc_eq hft
      rw [hst]
      cases Nat.lt_or_ge w t with
      | inr htw =>
        constructor
        . apply s1
          . exact htw
          . exact hwy
          . exact hft
          . exact hfy
          . exact hfw
          . exact hfty
        . rw [Nat.sub_eq_zero_of_le htw.le, Trunc.trunc_zero]
      | inl hwt =>
        constructor
        . rw [Nat.sub_eq_zero_of_le hwt.le, Trunc.trunc_zero]
        . rw [ht]
          apply s1
          . exact ht ▸ hwt.le
          . exact ht ▸ hty'
          . exact hfw
          . rw [Round.Faithful.trunc_eq_iff_round_eq]
            exact hfy'
          . exact Round.Faithful.trunc_round_eq_round _
          . rw [← hfy']
            apply s3
            . exact hfx
            . exact hfy
            . exact hfw
            . exact Nat.le_trans hyx (Nat.le_mul_of_pos_left two_pos)
            . exact Nat.le_trans hxw hwy
            . exact hxyx
            . exact hxw
            . apply Nat.le_trans hwt.le (hfy'.symm ▸ hty')
    | inr htx => -- htx : t ≤ x
      have hftx : round (x - t) = x - t := by
        rw [← Round.Faithful.trunc_eq_iff_round_eq]
        rw [ht]
        apply s1
        . exact ht ▸ htx
        . exact Nat.le_trans hxw hwy
        . exact Round.Faithful.trunc_round_eq_round _
        . exact hfy
        . exact hfx
        . exact ht ▸ hfty
      have hst : s = t := by
        rw [hs₂ htx, hftx, tsub_tsub_cancel_of_le htx, ht]
        exact Round.Faithful.round_idempotent _
      constructor
      . rw [hst, ht]
        apply s1
        . rw [← ht]
          exact Nat.le_trans htx hxw
        . exact hwy
        . exact Round.Faithful.trunc_round_eq_round _
        . exact hfy
        . exact hfw
        . rw [← ht]
          exact hfty
      . rw [Nat.sub_eq_zero_of_le (hst ▸ Nat.le_trans htx hxw), Trunc.trunc_zero]
  . have hty : round (y - round (y - z)) ≤ y :=
      Round.Faithful.round_sub_le_of_trunc_eq hfy
    have htx : t ≤ x := (Nat.le_trans (ht.symm ▸ hty) (Nat.le_trans hyw hwx))
    have hs : s = round (x - round (x - t)) := hs₂ htx
    have hfsx : trunc (x - s) = x - s := by
      rw [hs]
      apply s2
      . apply Nat.le_trans (m := trunc x)
        . apply Round.Faithful.round_le_trunc_of_le_trunc
          rw [hfx]
          exact Nat.sub_le _ _
        . exact Trunc.trunc_le _
      . exact Round.Faithful.trunc_round_eq_round _
      . exact hfx
    cases Nat.lt_or_ge y s with
    | inr hsy => -- hsy : s ≤ y
      constructor
      . apply s1
        . exact Nat.le_trans hsy hyw
        . exact hwx
        . rw [hs]
          exact Round.Faithful.trunc_round_eq_round _
        . exact hfx
        . exact hfw
        . exact hfsx
      . rw [Nat.sub_eq_zero_of_le (Nat.le_trans hsy hyw), Trunc.trunc_zero]
    | inl hys => -- hys : y < s
      have hfs' : s = x - round (x - t) := by
        rw [hs, ← Round.Faithful.trunc_eq_iff_round_eq]
        apply s2
        . exact Nat.le_trans (ht.symm ▸ hty) (Nat.le_trans hyw hwx)
        . exact hft
        . exact hfx
      have hfs : trunc s = s := by
        rw [hs]
        exact Round.Faithful.trunc_round_eq_round _
      have hyxtx : x - round (x - t) ≤ x - round (x - y) := by
        apply Nat.sub_le_sub_left
        exact h₂ hft hfy hfx (ht ▸ hty)
      have hys' : y < x - round (x - y) := by
        apply Nat.lt_of_lt_of_le hys
        apply Nat.le_trans hfs'.le
        exact hyxtx
      have hfyx : round (x - round (x - y)) = x - round (x - y) := by
        rw [← Round.Faithful.trunc_eq_iff_round_eq]
        apply s2
        . exact Nat.le_trans hyw hwx
        . exact hfy
        . exact hfx
      constructor
      . cases Nat.le_total w s with
        | inl hws =>
          rw [Nat.sub_eq_zero_of_le hws, Trunc.trunc_zero]
        | inr hsw =>
          apply s1
          . exact hsw
          . exact hwx
          . exact hfs
          . exact hfx
          . exact hfw
          . exact hfsx
      . cases Nat.le_total w s with
        | inr hsw =>
          rw [Nat.sub_eq_zero_of_le hsw, Trunc.trunc_zero]
        | inl hws =>
          apply s1
          . exact hws
          . exact hfs'.symm ▸ hyxtx
          . exact hfw
          . rw [Round.Faithful.trunc_eq_iff_round_eq]
            exact hfyx
          . exact hfs
          . rw [← hfyx]
            apply s3
            . exact hfy
            . exact hfx
            . exact hfw
            . exact Nat.le_trans hxy (Nat.le_mul_of_pos_left two_pos)
            . exact Nat.le_trans hyw hwx
            . exact hfyx.symm ▸ hys'
            . exact hyw
            . apply Nat.le_trans hws
              rw [hfyx]
              apply Nat.le_trans hfs'.le
              exact hyxtx

-- Still weaker version using the correct rounding axioms
theorem interval_shift' {x y z w s t : ℕ}
  (hfx : trunc x = x) (hfy : trunc y = y)
  (hfz : trunc z = z) (hfw : trunc w = w)
  (hzx : z < x) (hzy : z < y) (hyx : ulp y ≤ x) (hxy : ulp x ≤ y)
  (ht : t = round (y - round (y - z)))
  (hs₁ : x < t → s = round (x + round (t - x)))
  (hs₂ : t ≤ x → s = round (x - round (x - t)))
  (hxwy : (x ≤ w ∧ w ≤ y) ∨ (y ≤ w ∧ w ≤ x)) :
  trunc (w - s) = w - s ∧ trunc (s - w) = s - w := by
  have h₂ : monotonic₂ := Round.Correct.monotonic.right
  apply interval_shift h₂ hfx hfy hfz hfw hzx hzy hyx hxy ht hs₁ hs₂ hxwy
