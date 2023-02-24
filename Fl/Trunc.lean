import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Algebra.Order.Monoid.WithTop

import Mathlib.Tactic.LibrarySearch

import Fl.Lemmas

namespace Fl.Trunc

namespace Defs

axiom n : ℕ
axiom n_pos : 0 < n

noncomputable def expt (x : ℕ) : ℕ := x.size - n
noncomputable def ulp (x : ℕ) : ℕ := 2 ^ expt x
noncomputable def sig (x : ℕ) : ℕ := x / ulp x
noncomputable def trunc (x : ℕ) : ℕ := sig x * ulp x
noncomputable def next (x : ℕ) : ℕ := x + ulp x

end Defs

open Defs

theorem expt_le_expt {x y : ℕ} (h : x ≤ y) : expt x ≤ expt y :=
  Nat.sub_le_sub_right (Nat.size_le_size h) _

theorem ulp_le_ulp {x y : ℕ} (h : x ≤ y) : ulp x ≤ ulp y :=
  Nat.pow_le_pow_of_le_right two_pos (expt_le_expt h)

theorem next_le_next {x y : ℕ} (h : x ≤ y) : next x ≤ next y :=
  Nat.add_le_add h (ulp_le_ulp h)

theorem next_lt_next {x y : ℕ} (h : x < y) : next x < next y :=
  Nat.lt_of_lt_of_le
    (Nat.add_lt_add_right h (ulp x))
    (Nat.add_le_add_left (ulp_le_ulp (le_of_lt h)) y)

theorem expt_eq_zero_of_lt {x : ℕ} (h : x < 2 ^ n) : expt x = 0 :=
  Nat.sub_eq_zero_of_le (Nat.size_le.mpr h)

theorem ulp_eq_one_of_lt {x : ℕ} (h : x < 2 ^ n) : ulp x = 1 := by
  unfold ulp
  rw [expt_eq_zero_of_lt h, Nat.pow_zero]

theorem sig_eq_self_of_lt {x : ℕ} (h : x < 2 ^ n) : sig x = x := by
  unfold sig
  rw [ulp_eq_one_of_lt h, Nat.div_one]

theorem ulp_pos (x : ℕ) : 0 < ulp x := Fl.Lemmas.two_pow_pos

theorem ulp_le {a : ℕ} (h : 0 < a) : ulp a ≤ a := by
  unfold ulp expt
  transitivity 2 ^ (a.size - 1)
  . exact pow_le_pow one_le_two (Nat.sub_le_sub_left a.size n_pos)
  . exact Fl.Lemmas.le_size_of_pos h

theorem ulp_le_trunc {a : ℕ} (h : 0 < a) : ulp a ≤ trunc a := by
  unfold trunc sig ulp expt
  apply Nat.le_mul_of_pos_left
  rw [← Nat.succ_le, ← Nat.one_eq_succ_zero]
  rw [Nat.one_le_div_iff Lemmas.two_pow_pos]
  exact ulp_le h

theorem sig_pos {a : ℕ} (h : 0 < a) : 0 < sig a := by
  change 1 ≤ sig a
  unfold sig
  rw [Nat.le_div_iff_mul_le (ulp_pos _), one_mul]
  exact ulp_le h

theorem size_trunc_eq_size (x : ℕ) : (trunc x).size = x.size := by
  unfold trunc sig ulp expt
  cases x with
  | zero => rw [Nat.zero_div _, Nat.zero_mul]
  | succ x =>
    apply Fl.Lemmas.size_div_mul
    -- ⊢ 2 ^ (x.succ.size - n) ≤ x.succ
    rw [← Nat.lt_size]
    exact Nat.sub_lt (Nat.size_pos.mpr (Nat.succ_pos x)) n_pos

theorem ulp_trunc_eq_ulp (x : ℕ) : ulp (trunc x) = ulp x :=
  congr_arg (fun w ↦ 2 ^ (w - n)) (size_trunc_eq_size x)

theorem trunc_idempotent (x : ℕ) : trunc (trunc x) = trunc x := by
  rw [trunc, sig]
  rw [ulp_trunc_eq_ulp]
  rw [trunc, sig]
  rw [Nat.mul_div_cancel _ (ulp_pos x)]

theorem trunc_eq_self_of_lt {x : ℕ} (h : x < 2 ^ n) : trunc x = x := by
  unfold trunc
  rw [sig_eq_self_of_lt h, ulp_eq_one_of_lt h, Nat.mul_one]

theorem size_next_le_succ_size (x : ℕ) : (next x).size ≤ x.size + 1 := by
  rw [Nat.size_le, Nat.pow_succ, Nat.mul_two]
  unfold next ulp expt
  rw [Nat.add_comm, ← Nat.add_one_le_iff, add_rotate]
  apply Nat.add_le_add
  . exact Nat.lt_size_self x
  . exact Nat.pow_le_pow_of_le_right two_pos (Nat.sub_le _ _)

theorem size_next_eq_size_of_lt {x : ℕ} (h : next x < 2 ^ x.size) :
  (next x).size = x.size :=
  Nat.le_antisymm (Nat.size_le.mpr h) (Nat.size_le_size (Nat.le_add_right _ _))

theorem size_next_eq_succ_size_of_ge {x : ℕ} (h : 2 ^ x.size ≤ next x) :
  (next x).size = x.size + 1 :=
  Nat.le_antisymm (size_next_le_succ_size x) (Nat.lt_size.mpr h)

theorem ulp_next_of_lt {x : ℕ} (h : next x < 2 ^ x.size) :
  ulp (next x) = ulp x := by
  unfold ulp expt
  rw [size_next_eq_size_of_lt h]

theorem ulp_next_of_ge_of_ge {x : ℕ} (h : 2 ^ x.size ≤ next x) (k : n ≤ x.size) :
  ulp (next x) = ulp x * 2 := by
  unfold ulp expt
  rw [size_next_eq_succ_size_of_ge h]
  rw [Nat.sub_add_comm k]
  exact Nat.pow_succ _ _

theorem ulp_next_of_ge_of_lt {x : ℕ} (h : 2 ^ x.size ≤ next x) (k : x.size < n) :
  ulp (next x) = 1 := by
  unfold ulp expt
  rw [size_next_eq_succ_size_of_ge h]
  rw [Nat.sub_eq_zero_of_le k]
  exact Nat.pow_zero _

theorem next_lt_size_add_ulp (x : ℕ) : next x < 2 ^ x.size + ulp x :=
  Nat.add_lt_add_right (Nat.lt_size_self _) _

theorem next_lt_of_size_lt {x : ℕ} (hlt : x.size < n) :
  next x < 2 ^ n :=
  Nat.size_le.mp (Nat.le_trans (size_next_le_succ_size x) hlt)

theorem sig_next_of_lt {x : ℕ} (h : next x < 2 ^ x.size) :
  sig (next x) = sig x + 1 := by
  unfold sig
  rw [ulp_next_of_lt h]
  exact Nat.add_div_right _ (ulp_pos x)

theorem trunc_eq_sub_mod (x : ℕ) : trunc x = x - x % (ulp x) := by
  apply Eq.symm
  rw [Nat.sub_eq_iff_eq_add (Nat.mod_le x (ulp x))]
  apply Eq.symm
  exact Nat.div_add_mod' x (ulp x)

theorem trunc_next_comm_of_lt_size {x : ℕ} (h : next x < 2 ^ x.size) :
  trunc (next x) = next (trunc x) := by
  unfold trunc
  rw [sig_next_of_lt h]
  rw [ulp_next_of_lt h]
  rw [Nat.succ_mul]
  apply congr_arg (fun w ↦ x / ulp x * ulp x + w)
  exact (ulp_trunc_eq_ulp x).symm

theorem trunc_next_of_ge_size {x : ℕ} (h : 2 ^ x.size ≤ next x) :
  trunc (next x) = 2 ^ x.size := by
  have h₁ : expt (next x) ≤ x.size := by
    unfold expt
    rw [size_next_eq_succ_size_of_ge h]
    transitivity x.size + 1 - 1
    . exact Nat.sub_le_sub_left (x.size + 1) n_pos
    . rw [Nat.add_sub_cancel]
  have h₃ : next x < 2 ^ x.size + 2 ^ expt (next x) := by
    apply add_lt_add_of_lt_of_le
    . exact Nat.lt_size_self x
    . apply ulp_le_ulp
      exact Nat.le_add_right x (2 ^ expt x)
  exact Fl.Lemmas.div_mul_eq_of_le_of_lt' h₁ h h₃

theorem next_trunc_of_ge_size {x : ℕ} (h : 2 ^ x.size ≤ next x) :
  next (trunc x) = 2 ^ x.size := by
  unfold next
  rw [ulp_trunc_eq_ulp]
  unfold trunc sig ulp
  rw [← Nat.succ_mul]
  rw [← Nat.add_div_right x Fl.Lemmas.two_pow_pos]
  have h₁ : expt x ≤ x.size := Nat.sub_le x.size n
  have h₃ : next x < 2 ^ x.size + 2 ^ expt x :=
    Nat.add_lt_add_right (Nat.lt_size_self x) _
  exact Fl.Lemmas.div_mul_eq_of_le_of_lt' h₁ h h₃

theorem trunc_next_comm (x : ℕ) : trunc (next x) = next (trunc x) := by
  cases Nat.lt_or_ge (next x) (2 ^ x.size) with
  | inl next_lt => -- next_lt : next x < 2 ^ x.size
    exact trunc_next_comm_of_lt_size next_lt
  | inr next_ge => -- next_ge : next x ≥ 2 ^ x.size
    exact (next_trunc_of_ge_size next_ge) ▸ (trunc_next_of_ge_size next_ge)

theorem lt_next (x : ℕ) : x < next x :=
  Nat.lt_add_of_pos_right (ulp_pos x)

theorem lt_next_trunc (x : ℕ) : x < next (trunc x) := by
  unfold next
  rw [ulp_trunc_eq_ulp]
  unfold trunc sig
  rw [← Nat.succ_mul, mul_comm]
  exact Nat.lt_mul_div_succ x (ulp_pos x)

theorem lt_trunc_next (x : ℕ) : x < trunc (next x) :=
  trunc_next_comm x ▸ lt_next_trunc x

theorem lt_next_trunc_of_trunc_le_trunc {x y : ℕ} (h : trunc y ≤ trunc x) :
  y < next (trunc x) :=
  Nat.lt_of_lt_of_le (lt_next_trunc y) (Nat.add_le_add h (ulp_le_ulp h))

theorem trunc_le_trunc {x y : ℕ} (h : x ≤ y) : trunc x ≤ trunc y := by
  cases Nat.lt_or_ge x.size y.size with
  | inl size_lt_size => -- size_lt_size : x.size < y.size
    rw [← size_trunc_eq_size x] at size_lt_size
    rw [← size_trunc_eq_size y] at size_lt_size
    exact le_of_lt (Fl.Lemmas.lt_of_size_lt_size size_lt_size)
  | inr size_ge_size => -- size_ge_size : y.size ≤ x.size
    have ulp_eq_ulp : ulp x = ulp y := by
      apply congr_arg (fun w => 2 ^ (w - n))
      exact Nat.le_antisymm (Nat.size_le_size h) size_ge_size
    unfold trunc sig
    rw [ulp_eq_ulp]
    exact Nat.mul_le_mul_right _ (Nat.div_le_div_right h)

theorem trunc_le (x : ℕ) : trunc x ≤ x := Nat.div_mul_le_self _ _

theorem trunc_next_le (x : ℕ) : trunc (next x) ≤ 2 ^ x.size := by
  cases Nat.le_total (next x) (2 ^ x.size) with
  | inl le => exact Nat.le_trans (trunc_le (next x)) le
  | inr ge => exact Nat.le_of_eq (trunc_next_of_ge_size ge)

theorem next_trunc_le (x : ℕ) : next (trunc x) ≤ 2 ^ x.size := by
  rw [← trunc_next_comm]
  exact trunc_next_le x

theorem trunc_eq_trunc_of_trunc_le_of_lt_next_trunc {x y : ℕ}
  (h : trunc x ≤ y) (k : y < next (trunc x)) :
  trunc x = trunc y := by
  have ulp_eq : ulp x = ulp y := by
    rw [← ulp_trunc_eq_ulp]
    apply le_antisymm
    . apply ulp_le_ulp
      exact h
    . rw [ulp_trunc_eq_ulp x]
      unfold ulp expt
      apply pow_le_pow one_le_two
      apply Nat.sub_le_sub_right
      rw [Nat.size_le]
      apply Nat.lt_of_lt_of_le k
      exact next_trunc_le x
  unfold trunc sig
  rw [← ulp_eq]
  apply Eq.symm
  apply congr_arg (fun w => w * ulp x)
  refine Nat.eq_of_le_of_lt_succ ?_ ?_
  . rw [← Nat.mul_div_cancel (x / ulp x) (ulp_pos x)]
    exact Nat.div_le_div_right h
  . rw [Nat.div_lt_iff_lt_mul (ulp_pos x)]
    rw [Nat.mul_comm, Nat.mul_succ, Nat.mul_comm]
    rw [← sig, ← trunc, ← ulp_trunc_eq_ulp, ← next]
    exact k

theorem next_pos (x : ℕ) : 0 < next x :=
  lt_add_of_le_of_pos (Nat.zero_le x) (ulp_pos x)

theorem trunc_zero : trunc 0 = 0 := by simp [trunc, sig]

theorem trunc_eq_zero_iff_eq_zero (x : ℕ) : trunc x = 0 ↔ x = 0 := by
  constructor
  . unfold trunc sig
    rw [Nat.mul_eq_zero]
    apply Or.rec
    . rw [Nat.div_eq_zero_iff (ulp_pos _)]
      unfold ulp expt
      rw [← Nat.size_le]
      rw [← Nat.size_eq_zero]
      exact Lemmas.eq_zero_of_le_sub n_pos
    . exact Not.elim (ne_zero_of_lt (ulp_pos x))
  . intro h
    rw [← trunc_zero]
    exact congr_arg trunc h

theorem trunc_pos_iff_pos {x : ℕ} : 0 < trunc x ↔ 0 < x := by
  rw [zero_lt_iff, zero_lt_iff, not_iff_not]
  exact trunc_eq_zero_iff_eq_zero x

theorem lt_trunc_next_of_trunc_le_trunc {x y : ℕ} (h : trunc y ≤ trunc x) :
  y < trunc (next x) := by
  apply Nat.lt_of_lt_of_le (m := trunc (next y))
  . exact lt_trunc_next y
  . rw [trunc_next_comm, trunc_next_comm]
    unfold next
    exact add_le_add h (ulp_le_ulp h)

theorem trunc_le_trunc_of_lt_next_trunc {x y : ℕ}
  (h : x < next (trunc y)) :
  trunc x ≤ trunc y :=
  Or.elim (le_or_gt (trunc y) x)
    (fun le => ge_of_eq (trunc_eq_trunc_of_trunc_le_of_lt_next_trunc le h))
    (fun gt => trunc_le_trunc (Nat.le_trans (le_of_lt gt) (trunc_le y)))

theorem trunc_le_trunc_iff (x y : ℕ) :
  trunc x ≤ trunc y ↔ x < next (trunc y) :=
  ⟨lt_next_trunc_of_trunc_le_trunc, trunc_le_trunc_of_lt_next_trunc⟩

theorem next_div_ulp_le (x : ℕ) :
  next x / ulp x ≤ 2 ^ (min n x.size) := by
  cases Nat.le_total x.size n with
  | inr le_size => -- le_size : n ≤ x.size
    rw [min_eq_left_iff.mpr le_size]
    rw [Nat.div_le_iff_le_mul_add_pred (ulp_pos x)]
    rw [← Nat.add_sub_assoc (ulp_pos x)]
    apply Nat.le_pred_of_lt
    change next x < 2 ^ (x.size - n) * 2 ^ n + ulp x
    rw [← pow_add]
    rw [Nat.sub_add_cancel le_size]
    exact next_lt_size_add_ulp x
  | inl size_le => -- size_lt : x.size < n
    rw [min_eq_right_iff.mpr size_le]
    unfold next ulp expt
    rw [Nat.sub_eq_zero_of_le size_le]
    rw [pow_zero, Nat.div_one]
    exact Nat.lt_size_self x

theorem next_div_ulp_ge_of_ge {x : ℕ} (h : 2 ^ x.size ≤ next x) :
  next x / ulp x ≥ 2 ^ (min n x.size) := by
  rw [ge_iff_le]
  rw [Nat.le_div_iff_mul_le (ulp_pos x)]
  unfold ulp expt
  rw [← pow_add]
  rw [min_comm, Nat.add_comm]
  rw [Nat.sub_add_min_cancel]
  exact h

theorem next_div_ulp_eq_of_ge {x : ℕ} (h : 2 ^ x.size ≤ next x) :
  next x / ulp x = 2 ^ (min n x.size) :=
  Nat.le_antisymm (next_div_ulp_le x) (next_div_ulp_ge_of_ge h)

theorem sig_next_of_ge {x : ℕ} (h : 2 ^ x.size ≤ next x) :
  sig (next x) = 2 ^ min (n - 1) x.size := by
  cases Nat.lt_or_ge x.size n with
  | inl size_lt => -- size_lt : x.size < n
    have le : x.size ≤ n - 1 := Nat.le_pred_of_lt size_lt
    have size_le : x < 2 ^ n := Nat.size_le.mp (Nat.le_of_lt size_lt)
    rw [min_eq_right_iff.mpr le]
    rw [sig_eq_self_of_lt (next_lt_of_size_lt size_lt)]
    apply le_antisymm
    . unfold next
      rw [ulp_eq_one_of_lt size_le]
      exact Nat.lt_size_self x
    . exact h
  | inr le_size => -- le_size : n ≤ x.size
    have pred_le : n - 1 ≤ x.size := Nat.le_trans (Nat.pred_le n) le_size
    rw [min_eq_left_iff.mpr pred_le]
    unfold sig
    rw [ulp_next_of_ge_of_ge h le_size]
    rw [← Nat.div_div_eq_div_mul]
    rw [next_div_ulp_eq_of_ge h]
    rw [min_eq_left_iff.mpr le_size]
    rw [← Nat.pow_div n_pos two_pos]
    rw [pow_one]

theorem ulp_dvd_ulp {a b : ℕ} (h : a ≤ b) : ulp a ∣ ulp b :=
  pow_dvd_pow 2 (expt_le_expt h)

theorem ulp_dvd_trunc (a : ℕ) : ulp a ∣ trunc a := Nat.dvd_mul_left _ _

theorem ulp_dvd_of_trunc_eq {a : ℕ} (h : trunc a = a) : ulp a ∣ a := by
  rw [← h, ulp_trunc_eq_ulp]
  exact ulp_dvd_trunc a

theorem trunc_eq_of_le_of_ulp_dvd {a b : ℕ} (k : b ≤ a) (h : ulp a ∣ b) :
  trunc b = b :=
  Nat.div_mul_cancel (dvd_trans (ulp_dvd_ulp k) h)

theorem trunc_eq_iff_ulp_dvd {a : ℕ} : trunc a = a ↔ ulp a ∣ a :=
  ⟨ulp_dvd_of_trunc_eq, trunc_eq_of_le_of_ulp_dvd le_rfl⟩

theorem next_trunc_pred_eq_self' {a : ℕ} (hpos : 0 < trunc a)
  : next (trunc (trunc a - 1)) = trunc a := by
  apply Eq.symm
  rw [← trunc_next_comm (trunc a - 1)]
  apply trunc_eq_trunc_of_trunc_le_of_lt_next_trunc
  . unfold next
    transitivity trunc a - 1 + 1
    . rw [Nat.sub_add_cancel hpos]
    . exact Nat.add_le_add_left (ulp_pos _) _
  . apply add_lt_add_of_lt_of_le
    . exact Nat.pred_lt (ne_zero_of_lt hpos)
    . exact ulp_le_ulp (Nat.sub_le _ _)

theorem next_trunc_pred_eq_self {a : ℕ} (hpos : 0 < a) (h : trunc a = a) :
  next (trunc (a - 1)) = a := by
  revert hpos
  exact h ▸ next_trunc_pred_eq_self'

theorem trunc_pred_eq_trunc_of_trunc_ne_self {a : ℕ}
  (h : trunc a ≠ a) :
  trunc (a - 1) = trunc a := by
  apply Eq.symm
  apply trunc_eq_trunc_of_trunc_le_of_lt_next_trunc
  . apply Nat.le_pred_of_lt
    exact Nat.lt_of_le_of_ne (trunc_le a) h
  . exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (lt_next_trunc a)

theorem trunc_trunc_sub_ulp_eq {a : ℕ} :
  trunc (trunc a - ulp a) = trunc a - ulp a := by
  apply trunc_eq_of_le_of_ulp_dvd
  . exact Nat.sub_le _ _
  . rw [ulp_trunc_eq_ulp]
    apply Nat.dvd_sub'
    . exact ulp_dvd_trunc _
    . exact Nat.dvd_refl _

theorem trunc_sub_ulp_eq_of_trunc_eq {a : ℕ} (h : trunc a = a) :
  trunc (a - ulp a) = a - ulp a := by
  rw [← h, ulp_trunc_eq_ulp]
  exact trunc_trunc_sub_ulp_eq

theorem one_le_expt_of_ge {a : ℕ} (hle : 2 ^ n ≤ a) : 1 ≤ expt a := by
  rw [← Nat.add_sub_cancel 1 n]
  apply Nat.sub_le_sub_right
  rw [Nat.one_add, Nat.succ_le, Nat.lt_size]
  exact hle

theorem two_le_ulp_of_ge {a : ℕ} (hle : 2 ^ n ≤ a) : 2 ≤ ulp a := by
  rw [← pow_one 2]
  unfold ulp expt
  apply pow_le_pow one_le_two
  exact one_le_expt_of_ge hle

theorem two_dvd_ulp_of_ge {a : ℕ} (hle : 2 ^ n ≤ a) : 2 ∣ ulp a := by
  rw [← pow_one 2]
  unfold ulp
  rw [Nat.pow_dvd_pow_iff_pow_le_pow two_pos]
  rw [pow_one 2]
  exact two_le_ulp_of_ge hle

theorem two_dvd_trunc_of_ge {a : ℕ} (hle : 2 ^ n ≤ a) : 2 ∣ trunc a := by
  rw [← pow_one 2]
  unfold trunc ulp
  apply dvd_mul_of_dvd_right
  apply pow_dvd_pow
  exact one_le_expt_of_ge hle

theorem ulp_mul_pow {x k : ℕ} (h : n ≤ x.size) :
  ulp (x * 2 ^ k) = ulp x * 2 ^ k := by
  unfold ulp expt
  have pos : 0 < x := by
    rw [← Nat.size_pos]
    exact Nat.lt_of_lt_of_le n_pos h
  rw [← pow_add, Lemmas.size_mul_pow pos, Nat.sub_add_comm h]

theorem trunc_mul_pow {x k : ℕ} :
  trunc (x * 2 ^ k) = trunc x * 2 ^ k := by
  cases eq_or_ne x 0 with
  | inl eq_zero =>
    unfold trunc sig ulp expt
    rw [eq_zero, Nat.zero_mul, Nat.zero_div, Nat.zero_mul, Nat.zero_mul]
  | inr ne_zero =>
    cases Nat.lt_or_ge n x.size with
    | inr size_le =>
      have lt : x < 2 ^ n := by
        rw [← Nat.size_le]
        exact size_le.le
      have d : ulp (x * 2 ^ k) ∣ x * 2 ^ k := by
        unfold ulp expt
        apply dvd_mul_of_dvd_right
        rw [Nat.pow_dvd_pow_iff_le_right one_lt_two]
        rw [Lemmas.size_mul_pow (Nat.zero_lt_of_ne_zero ne_zero)]
        rw [tsub_le_iff_left]
        apply Nat.add_le_add_right
        exact size_le
      rw [Trunc.trunc_eq_self_of_lt lt]
      exact trunc_eq_of_le_of_ulp_dvd le_rfl d
    | inl lt_size =>
      unfold trunc sig
      rw [ulp_mul_pow (le_of_lt lt_size)]
      rw [Nat.mul_div_mul_right _ _ Lemmas.two_pow_pos]
      rw [Nat.mul_assoc]

theorem trunc_pow_mul {x k : ℕ} :
  trunc (2 ^ k * x) = 2 ^ k * trunc x := by
  rw [mul_comm, trunc_mul_pow, mul_comm]

end Fl.Trunc
