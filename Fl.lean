import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Algebra.Order.Sub.Canonical
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

theorem s2' {a b : ℕ} (hab : a ≤ b)
  (hfa : trunc a = a) (hfb : trunc b = b) :
  round (b - round (b - a)) = b - round (b - a) :=
  Round.Faithful.round_eq_of_trunc_eq (s2 hab hfa hfb)

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

-- float shift (float x, float y, float z) {
--   float t = y - (y - z);
--   float s = x - (x - t);
--   return s;
-- }

-- Note the result in Priest (Proposition, p. 10) is stronger,
-- assuming only monotonicity, antisymmetry and properties S1 to S3

theorem interval_shift₁ {x y z w s t : ℕ}
  (hm₂ : monotonic₂)
  (hfx : trunc x = x) (hfy : trunc y = y)
  (hfz : trunc z = z) (hfw : trunc w = w)
  (hzx : z ≤ x) (hzy : z ≤ y) (hyxulp : ulp y ≤ 2 * x)
  (ht : t = round (y - round (y - z)))
  (hs₁ : x < t → s = round (x + round (t - x)))
  (hs₂ : t ≤ x → s = round (x - round (x - t)))
  (hxw : x ≤ w) (hwy : w ≤ y) :
  trunc (w - s) = w - s ∧ trunc (s - w) = s - w := by
  have hxy : x ≤ y := Nat.le_trans hxw hwy
  have ht' : t = y - round (y - z) := calc
    t = round (y - round (y - z)) := ht
    _ = y - round (y - z)         := s2' hzy hfz hfy
  have htx' : t ≤ y - round (y - x) := calc
    t = y - round (y - z) := ht'
    _ ≤ y - round (y - x) := Nat.sub_le_sub_left y (hm₂ hfz hfx hfy hzx)
  have hzy' : round (y - z) ≤ y := Round.Faithful.round_sub_le_of_trunc_eq _ hfy
  have hft : trunc t = t := ht ▸ Round.Faithful.trunc_round_eq_round _
  have hfx' : round (y - round (y - x)) = y - round (y - x) := s2' hxy hfx hfy
  have hfut {u : ℕ} (hxu : x ≤ u) (hut : u < t) (hfu : trunc u = u)
    (hux' : u ≤ round (y - round (y - x))) :
    trunc (t - u) = t - u := by
    have hfuxy : trunc (y - round (y - x) - u) = y - round (y - x) - u := by
      have hxyx : x < round (y - round (y - x)) := by
        rw [hfx']
        exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hxu hut) htx'
      rw [← hfx']
      exact s3 hfx hfy hfu hyxulp hxy hxyx hxu hux'
    rw [ht] at hut htx' ⊢
    rw [← Round.Faithful.trunc_eq_iff_round_eq] at hfx'
    exact s1 hut.le htx' hfu hfx' (Round.Faithful.trunc_round_eq_round _) hfuxy
  have hfty : trunc (y - t) = y - t := by
    rw [ht', Nat.sub_sub_self hzy', Round.Faithful.trunc_round_eq_round]
  have hst : s = t := by
    rw [← Round.Faithful.round_eq_of_trunc_eq hft]
    cases Nat.lt_or_ge x t with
    | inl hxt => -- hxt : x < t
      have hfxt : round (t - x) = t - x := by
        apply Round.Faithful.round_eq_of_trunc_eq
        apply hfut le_rfl hxt hfx
        rw [hfx']
        exact Nat.le_trans hxt.le htx'
      rw [hs₁ hxt, hfxt, add_tsub_cancel_of_le hxt.le]
    | inr htx => -- htx : x ≥ t
      have hftx : round (x - t) = x - t := by
        apply Round.Faithful.round_eq_of_trunc_eq
        rw [ht] at htx hfty ⊢
        exact s1 htx hxy (Round.Faithful.trunc_round_eq_round _) hfy hfx hfty
      rw [hs₂ htx, hftx, tsub_tsub_cancel_of_le htx]
  rw [hst]
  cases Nat.lt_or_ge w t with
  | inl hwt => -- hwt : w < t
    constructor
    . rw [Nat.sub_eq_zero_of_le hwt.le, Trunc.trunc_zero]
    . exact hfut hxw hwt hfw (Nat.le_trans hwt.le (hfx'.symm ▸ htx'))
  | inr htw => -- htw : w ≥ t
    constructor
    . exact s1 htw hwy hft hfy hfw hfty
    . rw [Nat.sub_eq_zero_of_le htw, Trunc.trunc_zero]

theorem interval_shift₂ {x y z w s t : ℕ}
  (hm₂ : monotonic₂)
  (hfx : trunc x = x) (hfy : trunc y = y)
  (hfw : trunc w = w)
  (hxyulp : ulp x ≤ 2 * y)
  (ht : t = round (y - round (y - z)))
  (hs₂ : t ≤ x → s = round (x - round (x - t)))
  (hyw : y ≤ w) (hwx : w ≤ x) :
  trunc (w - s) = w - s ∧ trunc (s - w) = s - w := by
  have hty : t ≤ y := ht ▸ Round.Faithful.round_sub_le_of_trunc_eq _ hfy
  have hyx := Nat.le_trans hyw hwx
  have htx : t ≤ x := Nat.le_trans hty hyx
  have hs : s = round (x - round (x - t)) := hs₂ htx
  have hfs : trunc s = s := hs.symm ▸ Round.Faithful.trunc_round_eq_round _
  have hft : trunc t = t := ht.symm ▸ Round.Faithful.trunc_round_eq_round _
  have hty' : round (x - y) ≤ round (x - t) := hm₂ hft hfy hfx hty
  have hfy' : round (x - round (x - y)) = x - round (x - y) := s2' hyx hfy hfx
  have hsy' : s ≤ round (x - round (x - y)) := calc
    s = round (x - round (x - t)) := hs
    _ = x - round (x - t)         := s2' htx hft hfx
    _ ≤ x - round (x - y)         := Nat.sub_le_sub_left _ hty'
    _ = round (x - round (x - y)) := hfy'.symm
  have hfsx : trunc (x - s) = x - s := by
    rw [hs]
    apply s2
    . exact Round.Faithful.round_sub_le_of_trunc_eq _ hfx
    . exact Round.Faithful.trunc_round_eq_round _
    . exact hfx
  obtain hsy | ⟨hys, hws | hsw⟩ : s ≤ y ∨ y < s ∧ (w ≤ s ∨ s ≤ w) :=
    Or.elim (Nat.lt_or_ge y s) (fun h => Or.inr ⟨h, Nat.le_total w s⟩) Or.inl
  . constructor
    . exact s1 (Nat.le_trans hsy hyw) hwx hfs hfx hfw hfsx
    . rw [Nat.sub_eq_zero_of_le (Nat.le_trans hsy hyw), Trunc.trunc_zero]
  . constructor
    . rw [Nat.sub_eq_zero_of_le hws, Trunc.trunc_zero]
    . have hyy' : y < round (x - round (x - y)) := Nat.lt_of_lt_of_le hys hsy'
      have hwy' : w ≤ round (x - round (x - y)) := Nat.le_trans hws hsy'
      apply s1 hws hsy' hfw (Round.Faithful.trunc_round_eq_round _) hfs
      exact s3 hfy hfx hfw hxyulp hyx hyy' hyw hwy'
  . constructor
    . exact s1 hsw hwx hfs hfx hfw hfsx
    . rw [Nat.sub_eq_zero_of_le hsw, Trunc.trunc_zero]

theorem interval_shift {x y z w s t : ℕ}
  (hm₂ : monotonic₂)
  (hfx : trunc x = x) (hfy : trunc y = y)
  (hfz : trunc z = z) (hfw : trunc w = w)
  (hzx : z ≤ x) (hzy : z ≤ y) (hyx : ulp y ≤ 2 * x) (hxy : ulp x ≤ 2 * y)
  (ht : t = round (y - round (y - z)))
  (hs₁ : x < t → s = round (x + round (t - x)))
  (hs₂ : t ≤ x → s = round (x - round (x - t)))
  (hxwy : (x ≤ w ∧ w ≤ y) ∨ (y ≤ w ∧ w ≤ x)) :
  trunc (w - s) = w - s ∧ trunc (s - w) = s - w := by
  rcases hxwy with ⟨hxw, hwy⟩ | ⟨hyw, hwx⟩
  . exact interval_shift₁ hm₂ hfx hfy hfz hfw hzx hzy hyx ht hs₁ hs₂ hxw hwy
  . exact interval_shift₂ hm₂ hfx hfy hfw hxy ht hs₂ hyw hwx

-- Still weaker version using the correct rounding axioms
theorem interval_shift' {x y z w s t : ℕ}
  (hfx : trunc x = x) (hfy : trunc y = y)
  (hfz : trunc z = z) (hfw : trunc w = w)
  (hzx : z ≤ x) (hzy : z ≤ y) (hyx : ulp y ≤ 2 * x) (hxy : ulp x ≤ 2 * y)
  (ht : t = round (y - round (y - z)))
  (hs₁ : x < t → s = round (x + round (t - x)))
  (hs₂ : t ≤ x → s = round (x - round (x - t)))
  (hxwy : (x ≤ w ∧ w ≤ y) ∨ (y ≤ w ∧ w ≤ x)) :
  trunc (w - s) = w - s ∧ trunc (s - w) = s - w := by
  have hm₂ : monotonic₂ := Round.Correct.monotonic.right
  rcases hxwy with ⟨hxw, hwy⟩ | ⟨hyw, hwx⟩
  . exact interval_shift₁ hm₂ hfx hfy hfz hfw hzx hzy hyx ht hs₁ hs₂ hxw hwy
  . exact interval_shift₂ hm₂ hfx hfy hfw hxy ht hs₂ hyw hwx

-- Sum and error

-- Theorem a1, far below, states that if a and b are floating point numbers
-- and 0 ≤ a and 0 ≤ b, then a + b - fl (a + b) is also a floating point number.

theorem a1_of_uflow {a b : ℕ} (uflow : a + b < 2 ^ n) :
  trunc (a + b - round (a + b)) = a + b - round (a + b) ∧
  trunc (round (a + b) - (a + b)) = round (a + b) - (a + b) := by
  have k : trunc (a + b) = a + b := Trunc.trunc_eq_self_of_lt uflow
  have l : round (a + b) = a + b := Round.Faithful.round_eq_of_trunc_eq k
  rw [l, Nat.sub_self]
  exact ⟨Trunc.trunc_zero, Trunc.trunc_zero⟩

theorem a1_lo_of_lt_round {a b : ℕ} (lt_round : a + b < round (a + b)) :
  trunc (a + b - round (a + b)) = a + b - round (a + b) := by
  rw [Round.Faithful.round_eq_next_trunc_of_gt lt_round,
      Nat.sub_eq_zero_of_le (Nat.le_of_lt (Trunc.lt_next_trunc _)),
      Trunc.trunc_zero]

theorem a1_hi_of_round_le {a b : ℕ} (round_le : round (a + b) ≤ a + b) :
  trunc (round (a + b) - (a + b)) = round (a + b) - (a + b) := by
  rw [Round.Faithful.round_eq_trunc_of_le round_le,
      Nat.sub_eq_zero_of_le (Trunc.trunc_le _),
     Trunc.trunc_zero]

theorem a1_hi_of_lt_round_of_ulp_sub_le {a b : ℕ}
  (hfa : trunc a = a) (hfb : trunc b = b) (hba : b ≤ a)
  (lt_round : a + b < round (a + b))
  (ulp_sub_le : ulp (a + b) - (a + b) % ulp (a + b) ≤ b) :
  trunc (round (a + b) - (a + b)) = round (a + b) - (a + b) := by
  rw [Round.Faithful.round_eq_next_trunc_of_gt lt_round]
  apply Trunc.trunc_eq_of_le_of_ulp_dvd (a := b)
  . rw [next, Trunc.ulp_trunc_eq_ulp _, Trunc.trunc_eq_sub_mod,
        tsub_add_eq_add_tsub (Nat.mod_le _ _),
        Nat.add_sub_assoc (Nat.mod_lt _ (Trunc.ulp_pos _)).le,
        Nat.add_comm, Nat.add_sub_cancel]
    exact ulp_sub_le
  . apply Nat.dvd_sub'
    . rw [next, Trunc.ulp_trunc_eq_ulp _]
      apply Nat.dvd_add
      . apply Nat.dvd_trans (b := ulp (a + b))
        . exact Trunc.ulp_dvd_ulp (Nat.le_add_left _ _)
        . exact Trunc.ulp_dvd_trunc _
      . exact Trunc.ulp_dvd_ulp (Nat.le_add_left _ _)
    . apply Nat.dvd_add
      . apply Nat.dvd_trans (b := ulp a)
        . exact Trunc.ulp_dvd_ulp hba
        . exact Trunc.ulp_dvd_of_trunc_eq hfa
      . exact Trunc.ulp_dvd_of_trunc_eq hfb

theorem a1_hi_of_no_uflow_of_no_carry_of_lt_round {a b : ℕ}
  (hfa : trunc a = a) (hfb : trunc b = b) (hba : b ≤ a)
  (no_uflow : 2 ^ n ≤ a + b) (no_carry : a + b < 2 ^ Nat.size a)
  (lt_round : a + b < round (a + b)) :
  trunc (round (a + b) - (a + b)) = round (a + b) - (a + b) := by
  have size_eq : (a + b).size = a.size := by
    apply Nat.le_antisymm
    . exact Nat.size_le.mpr no_carry
    . exact Nat.size_le_size (Nat.le_add_right _ _)
  have ulp_eq : ulp (a + b) = ulp a := by
    unfold ulp expt
    rw [size_eq]
  have ulp_le : ulp a ≤ 2 * b := by
    have ⟨d, hd⟩ := Trunc.two_dvd_ulp_of_ge no_uflow
    rw [← ulp_eq, hd]
    apply Nat.mul_le_mul_left
    apply Nat.le_of_add_le_add_left (a := a)
    apply Nat.le_trans (m := trunc (a + b) + ulp (a + b) / 2)
    . rw [hd, Nat.mul_comm, Nat.mul_div_cancel _ two_pos]
      apply Nat.add_le_add_right
      apply Nat.le_trans hfa.ge
      apply Trunc.trunc_le_trunc
      exact Nat.le_add_right _ _
    . apply Round.Correct.a3'''
      exact Round.Faithful.round_eq_next_trunc_of_gt lt_round
  apply a1_hi_of_lt_round_of_ulp_sub_le hfa hfb hba lt_round
  rw [ulp_eq, ← Nat.mod_add_mod,
      Nat.mod_eq_zero_of_dvd (Trunc.ulp_dvd_of_trunc_eq hfa), Nat.zero_add]
  . cases Nat.lt_or_ge b (ulp a) with
    | inl lt_ulp' =>
      rw [tsub_le_iff_right, Nat.mod_eq_of_lt lt_ulp', ← Nat.two_mul]
      exact ulp_le
    | inr ulp_le' => exact Nat.le_trans (Nat.sub_le _ _) ulp_le'

theorem a1_hi_of_ulp_le_of_lt_round {a b : ℕ}
  (hfa : trunc a = a) (hfb : trunc b = b) (hba : b ≤ a)
  (ulp_le : ulp (a + b) ≤ b) (lt_round : a + b < round (a + b)) :
  trunc (round (a + b) - (a + b)) = round (a + b) - (a + b) := by
  apply a1_hi_of_lt_round_of_ulp_sub_le hfa hfb hba lt_round
  exact Nat.le_trans (Nat.sub_le _ _) ulp_le

theorem a1_lo_of_no_carry_of_round_le {a b : ℕ}
  (hfa : trunc a = a) (hfb : trunc b = b) (hba : b ≤ a)
  (no_carry : a + b < 2 ^ Nat.size a)
  (round_le : round (a + b) ≤ a + b) :
  trunc (a + b - round (a + b)) = a + b - round (a + b) := by
  have size_eq : (a + b).size = a.size := by
    apply Nat.le_antisymm
    . exact Nat.size_le.mpr no_carry
    . exact Nat.size_le_size (Nat.le_add_right _ _)
  have ulp_eq : ulp (a + b) = ulp a := by
    unfold ulp expt
    rw [size_eq]
  have mod_ulp₁ : a % ulp a = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact Trunc.ulp_dvd_of_trunc_eq hfa
  have mod_ulp₂ : (a + b) % ulp a = b % ulp a := by
    rw [Nat.add_mod, mod_ulp₁, Nat.zero_add, Nat.mod_mod]
  have error_eq : a + b - trunc (a + b) = b % ulp a := by
    rw [tsub_eq_iff_eq_add_of_le (Trunc.trunc_le _), Nat.add_comm (b % ulp a)]
    rw [← mod_ulp₂, ← ulp_eq]
    unfold trunc sig
    rw [Nat.div_add_mod']
  rw [Round.Faithful.round_eq_trunc_of_le round_le, error_eq]
  apply Trunc.trunc_eq_of_le_of_ulp_dvd
  . exact Nat.mod_le _ _
  . rw [Nat.dvd_mod_iff (Trunc.ulp_dvd_ulp hba)]
    exact Trunc.ulp_dvd_of_trunc_eq hfb

theorem a1_lo_of_no_uflow_of_carry_of_round_le {a b : ℕ}
  (hfa : trunc a = a) (hfb : trunc b = b) (hba : b ≤ a)
  (no_uflow : 2 ^ n ≤ a + b) (carry : 2 ^ Nat.size a ≤ a + b)
  (round_le : round (a + b) ≤ a + b) :
  trunc (a + b - round (a + b)) = a + b - round (a + b) := by
  have size_eq : (a + b).size = a.size + 1 := by
    apply Nat.le_antisymm
    . rw [Nat.size_le, pow_succ, Nat.two_mul]
      apply Nat.add_lt_add
      . exact Nat.lt_size_self _
      . exact Nat.lt_of_le_of_lt hba (Nat.lt_size_self _)
    . rw [Nat.succ_le, Nat.lt_size]
      exact carry
  have le_size : n ≤ a.size := by
    rw [← Nat.lt_succ, Nat.succ_eq_add_one, ← size_eq]
    rw [Nat.lt_size]
    exact no_uflow
  have ulp_eq : ulp (a + b) = 2 * ulp a := by
    unfold ulp expt
    rw [← pow_succ, size_eq, Nat.sub_add_comm le_size]
  have lt_trunc : a < (a + b) / ulp a * ulp a := by
    apply Nat.lt_of_lt_of_le (m := trunc (a + b))
    . apply Lemmas.lt_of_size_lt_size
      rw [Trunc.size_trunc_eq_size]
      exact size_eq.ge
    . unfold trunc sig
      rw [ulp_eq, ← Nat.mul_assoc]
      apply Nat.mul_le_mul_right _
      rw [Nat.mul_comm 2, ← Nat.div_div_eq_div_mul]
      exact Nat.div_mul_le_self _ _
  have ulp_le : ulp a ≤ b := by
    have ulp_pos : 0 < ulp a := Trunc.ulp_pos _
    have ulp_dvd : ulp a ∣ a := Trunc.ulp_dvd_of_trunc_eq hfa
    rw [← Nat.one_le_div_iff ulp_pos]
    apply Lemmas.lt_of_mul_lt_mul_right (ulp a)
    apply Nat.lt_of_add_lt_add_left (k := a / ulp a * ulp a)
    rw [Nat.zero_mul, Nat.add_zero, ← Nat.add_mul,
        ← Lemmas.add_div_of_pos_of_dvd ulp_pos ulp_dvd,
        ← sig, ← trunc, hfa]
    exact lt_trunc
  have ⟨d, hd⟩ : ulp a ∣ (a + b) / ulp a * ulp a % (2 * ulp a) := by
    have h₁ : ulp a ∣ ulp a * 2 := ⟨2, rfl⟩
    rw [Nat.mul_comm, Nat.mul_comm 2, Nat.dvd_mod_iff h₁]
    exact ⟨_, rfl⟩
  have hdle : d ≤ 1 := by
    apply Nat.le_of_lt_succ
    apply Lemmas.lt_of_mul_lt_mul_right (ulp a)
    rw [Nat.mul_comm, ← hd]
    apply Nat.mod_lt
    exact Nat.mul_pos two_pos (Trunc.ulp_pos _)
  have h₁ : (a + b) % ulp a = b % ulp a := by
    rw [← Nat.mod_add_mod,
        Nat.mod_eq_zero_of_dvd (Trunc.ulp_dvd_of_trunc_eq hfa),
        Nat.zero_add]
  have h₂ : trunc (a + b) = (a + b) / ulp a * ulp a / (2 * ulp a) * (2 * ulp a) := by
    rw [Nat.mul_comm 2, ← Nat.div_div_eq_div_mul,
        Nat.mul_div_cancel _ (Trunc.ulp_pos _), Nat.div_div_eq_div_mul,
        Nat.mul_comm (ulp a), ← ulp_eq, ← sig, ← trunc]
  have h₃ : a + b - trunc (a + b) = d * ulp a + b % ulp a := by
    rw [tsub_eq_iff_eq_add_of_le (Trunc.trunc_le _), ← add_rotate,
        Nat.mul_comm, h₂, ← hd, ← h₁, Nat.div_add_mod', Nat.div_add_mod']
  have h₄ : d * ulp a ≤ b / ulp a * ulp a := by
    apply Nat.mul_le_mul_right
    apply Nat.le_trans hdle
    rw [Nat.one_le_div_iff (Trunc.ulp_pos _)]
    exact ulp_le
  rw [Round.Faithful.round_eq_trunc_of_le round_le, h₃]
  apply Trunc.trunc_eq_of_le_of_ulp_dvd (a := b)
  . apply Nat.le_trans
    . exact Nat.add_le_add_right h₄ _
    . exact Nat.le_of_eq (Nat.div_add_mod' _ _)
  . apply Nat.dvd_add
    . apply Nat.dvd_trans (b := ulp a)
      . exact Trunc.ulp_dvd_ulp hba
      . exact Nat.dvd_mul_left _ _
    . rw [Nat.dvd_mod_iff (Trunc.ulp_dvd_ulp hba)]
      exact Trunc.ulp_dvd_of_trunc_eq hfb

theorem round_eq_trunc_of_no_uflow_of_carry_of_lt_ulp {a b : ℕ}
  (hfa : trunc a = a) (hba : b ≤ a)
  (no_uflow : 2 ^ n ≤ a + b) (carry : 2 ^ a.size ≤ a + b)
  (lt_ulp : b < ulp (a + b)) :
  round (a + b) = trunc (a + b) := by
  have size_eq : (a + b).size = a.size + 1 := by
    apply Nat.le_antisymm
    . rw [Nat.size_le, pow_succ, Nat.two_mul]
      apply Nat.add_lt_add
      . exact Nat.lt_size_self _
      . exact Nat.lt_of_le_of_lt hba (Nat.lt_size_self _)
    . rw [Nat.succ_le, Nat.lt_size]
      exact carry
  have le_size : n ≤ a.size := by
    rw [← Nat.lt_succ, Nat.succ_eq_add_one, ← size_eq, Nat.lt_size]
    exact no_uflow
  have size_ulp : 2 ^ a.size = 2 ^ n * ulp a := by
    unfold ulp expt
    rw [← pow_add, Nat.add_sub_cancel' le_size]
  have ulp_eq : ulp (a + b) = 2 * ulp a := by
    unfold ulp expt
    rw [← pow_succ, size_eq, Nat.sub_add_comm le_size]
  have h₂ : a + b < 2 ^ a.size + ulp a := by
    have le_ulp : a ≤ 2 ^ a.size - ulp a := by
      apply Lemmas.le_sub_of_dvd_of_dvd_of_lt
      . exact Trunc.ulp_dvd_of_trunc_eq hfa
      . rw [size_ulp]
        exact Nat.dvd_mul_left _ _
      . exact Nat.lt_size_self _
    have hle₁ : ulp a ≤ 2 ^ a.size := by
      rw [size_ulp]
      exact Nat.le_mul_of_pos_left Lemmas.two_pow_pos
    rw [← Nat.sub_add_cancel hle₁, Nat.add_assoc, ← Nat.two_mul, ← ulp_eq]
    exact add_lt_add_of_le_of_lt le_ulp lt_ulp
  have h₃ : (a + b) / ulp a * ulp a = 2 ^ a.size := by
    rw [size_ulp]
    apply congr_arg (fun w => w * ulp a)
    apply Nat.le_antisymm
    . rw [Nat.div_le_iff_le_mul_add_pred (Trunc.ulp_pos a), Nat.mul_comm,
          ← size_ulp, ← Nat.add_sub_assoc (Nat.one_le_of_lt (Trunc.ulp_pos a))]
      exact Nat.le_pred_of_lt h₂
    . rw [← Nat.mul_div_cancel (2 ^ n) (Trunc.ulp_pos a), ← size_ulp]
      exact Nat.div_le_div_right carry
  have h₄ : 2 ∣ (a + b) / ulp a := by
    rw [← Nat.mul_div_cancel ((a + b) / ulp a) (Trunc.ulp_pos a), h₃, size_ulp,
        Nat.mul_div_cancel _ (Trunc.ulp_pos a)]
    exact Nat.dvd_of_pow_dvd (Nat.one_le_of_lt n_pos) dvd_rfl
  have h₅ : trunc (a + b) = 2 ^ a.size := by
    unfold trunc sig
    rw [ulp_eq, Nat.mul_comm 2, ← Nat.div_div_eq_div_mul, ← Nat.mul_comm 2,
        ← Nat.mul_assoc, Nat.div_mul_cancel h₄]
    exact h₃
  have h₆ : a + b < trunc (a + b) + ulp (a + b) / 2 := by
    rw [h₅, ulp_eq, Nat.mul_comm, Nat.mul_div_cancel _ two_pos]
    exact h₂
  exact Round.Correct.a2'' h₆

theorem round_le_of_no_uflow_of_carry_of_lt_ulp {a b : ℕ}
  (hfa : trunc a = a) (hba : b ≤ a)
  (no_uflow : a + b ≥ 2 ^ n) (carry : a + b ≥ 2 ^ Nat.size a)
  (lt_ulp : b < ulp (a + b)) :
  round (a + b) ≤ a + b := by
  have round_eq_trunc : round (a + b) = trunc (a + b) :=
    round_eq_trunc_of_no_uflow_of_carry_of_lt_ulp hfa hba no_uflow carry lt_ulp
  exact round_eq_trunc ▸ (Trunc.trunc_le _)

theorem a1' {a b : ℕ}
  (hfa : trunc a = a) (hfb : trunc b = b) (hba : b ≤ a) :
  trunc (a + b - round (a + b)) = a + b - round (a + b) ∧
  trunc (round (a + b) - (a + b)) = round (a + b) - (a + b) := by
  cases Nat.lt_or_ge (a + b) (2 ^ n) with
  | inl uflow => exact a1_of_uflow uflow
  | inr no_uflow =>
    cases Nat.lt_or_ge (a + b) (round (a + b)) with
    | inl lt_round =>
      constructor
      . exact a1_lo_of_lt_round lt_round
      . cases Nat.lt_or_ge b (ulp (a + b)) with
        | inl lt_ulp =>
          cases Nat.lt_or_ge (a + b) (2 ^ a.size) with
          | inl no_carry => exact a1_hi_of_no_uflow_of_no_carry_of_lt_round hfa hfb hba no_uflow no_carry lt_round
          | inr carry =>
            exfalso
            apply Nat.lt_le_antisymm
            . exact lt_round
            . exact round_le_of_no_uflow_of_carry_of_lt_ulp hfa hba no_uflow carry lt_ulp
        | inr ulp_le => exact a1_hi_of_ulp_le_of_lt_round hfa hfb hba ulp_le lt_round
    | inr round_le =>
      constructor
      . cases Nat.lt_or_ge (a + b) (2 ^ a.size) with
        | inl no_carry => exact a1_lo_of_no_carry_of_round_le hfa hfb hba no_carry round_le
        | inr carry => exact a1_lo_of_no_uflow_of_carry_of_round_le hfa hfb hba no_uflow carry round_le
      . exact a1_hi_of_round_le round_le

theorem a1 {a b : ℕ}
  (hfa : trunc a = a) (hfb : trunc b = b) :
  trunc (a + b - round (a + b)) = a + b - round (a + b) ∧
  trunc (round (a + b) - (a + b)) = round (a + b) - (a + b) := by
  cases lt_or_ge a b with
  | inl hab =>
    rw [Nat.add_comm]
    exact a1' hfb hfa (Nat.le_of_lt hab)
  | inr hba => exact a1' hfa hfb hba
