import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Sub.Basic

theorem sub_div_of_pos_of_dvd {x d : ℕ} (hpos : 0 < d) (hdvd : d ∣ x) :
    x - x / d = (d - 1) * x / d := by
  have hdvd' : d ∣ (d - 1) * x := Nat.dvd_trans hdvd (Nat.dvd_mul_left _ _)
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [Nat.mul_sub_right_distrib, Nat.div_mul_cancel hdvd,
    Nat.div_mul_cancel hdvd', Nat.sub_one, Nat.pred_mul, Nat.mul_comm]

theorem sub_half_of_even {x : ℕ} (hdvd : 2 ∣ x) : x - x / 2 = x / 2 := by
  suffices x - x / 2 = (2 - 1) * x / 2 by
    rwa [show 2 - 1 = 1 from rfl, one_mul] at this
  exact sub_div_of_pos_of_dvd two_pos hdvd

theorem add_le_of_dvd_of_dvd_of_lt {n m k : ℕ} (h₁ : k ∣ n) (h₂ : k ∣ m)
    (h₃ : m < n) : m + k ≤ n := by
  apply Nat.le_of_lt_add_of_dvd
  . exact Nat.add_lt_add_right h₃ k
  . exact Nat.dvd_add h₂ (Nat.dvd_refl _)
  . exact h₁

theorem le_sub_of_dvd_of_dvd_of_lt {n m k : ℕ} (h₁ : k ∣ n) (h₂ : k ∣ m)
    (h₃ : n < m) : n ≤ m - k := by
  apply le_tsub_of_add_le_right
  exact add_le_of_dvd_of_dvd_of_lt h₂ h₁ h₃

theorem div_mul_eq_of_dvd_of_le_of_lt {m k x : ℕ} (h₁ : k ∣ m) (h₂ : m ≤ x)
    (h₃ : x < m + k) : x / k * k = m := by
  obtain ⟨d, rfl⟩ := h₁
  rewrite [mul_comm] at h₂
  rewrite [← Nat.mul_succ, mul_comm] at h₃
  rw [mul_comm, Nat.div_eq_of_lt_le h₂ h₃]

theorem div_mul_eq_of_le_of_lt {m k x : ℕ} (h₀ : k ≤ m) (h₁ : 2 ^ m ≤ x)
    (h₂ : x < 2 ^ m + 2 ^ k) : x / 2 ^ k * 2 ^ k = 2 ^ m :=
  div_mul_eq_of_dvd_of_le_of_lt (pow_dvd_pow 2 h₀) h₁ h₂

theorem div_mul_div_cancel_of_dvd {n m k : ℕ} (h₂ : k ∣ m) :
    n / k * k / m = n / m := by
  obtain ⟨d, rfl⟩ := h₂
  match k with
  | 0 => rw [Nat.mul_zero, Nat.zero_mul, Nat.zero_div, Nat.div_zero]
  | x + 1 =>
    rewrite [← Nat.div_div_eq_div_mul,
      Nat.mul_div_cancel _ (Nat.add_pos_right _ zero_lt_one)]
    exact Nat.div_div_eq_div_mul _ _ _

theorem pred_div_mul_eq_sub_of_pos_of_dvd {a b : ℕ} (h₁ : 0 < a) (h₂ : 0 < b)
    (h₃ : a ∣ b) : (b - 1) / a * a = b - a := by
  apply Nat.le_antisymm
  . apply le_sub_of_dvd_of_dvd_of_lt
    . exact Nat.dvd_mul_left _ _
    . exact h₃
    . apply Nat.lt_of_le_of_lt (m := b - 1)
      . exact Nat.div_mul_le_self _ _
      . exact tsub_lt_self h₂ zero_lt_one
  . rewrite [tsub_le_iff_right, ← Nat.add_one_mul, ← Nat.add_div_right _ h₁,
       tsub_add_eq_add_tsub (Nat.one_le_of_lt h₂),
       add_tsub_assoc_of_le (Nat.one_le_of_lt h₁)]
    trans b / a * a
    . rw [Nat.div_mul_cancel h₃]
    . apply Nat.mul_le_mul_right
      apply Nat.div_le_div_right
      exact Nat.le_add_right _ _

theorem mod_sub_mod (m n k : ℕ) (h : k ≤ m) :
    (m - k) % n = (m - k % n) % n := by
  trans (m - k % n - n * (k / n)) % n
  . rw [tsub_tsub, Nat.mod_add_div k n]
  . apply Nat.sub_mul_mod
    apply le_tsub_of_add_le_left
    rewrite [Nat.mod_add_div]
    exact h

theorem size_of_le_of_lt {x n : ℕ} (hl : 2 ^ (n - 1) ≤ x) (hr : x < 2 ^ n) :
    Nat.size x = n := by
  apply Nat.le_antisymm
  . rewrite [Nat.size_le]
    exact hr
  . apply Nat.le_of_pred_lt
    rewrite [← Nat.sub_one, Nat.lt_size]
    exact hl

theorem le_size_of_pos {x : ℕ} (pos : 0 < x) : 2 ^ (Nat.size x - 1) ≤ x := by
  rewrite [← Nat.lt_size]
  exact tsub_lt_self (Nat.size_pos.mpr pos) one_pos

theorem lt_of_size_lt_size {x y : ℕ} (h : Nat.size x < Nat.size y) : x < y :=
  Decidable.not_imp_not.mp
    (fun h => Nat.not_lt_of_le (Nat.size_le_size (Nat.le_of_not_lt h))) h

theorem size_mul_pow {x : ℕ} (h : 0 < x) (k : ℕ) :
    Nat.size (x * 2 ^ k) = Nat.size x + k := by
  have nz : x ≠ 0 := by rwa [← Nat.pos_iff_ne_zero]
  rewrite [← Nat.shiftLeft_eq_mul_pow x k]
  rw [Nat.size_shiftLeft nz]

theorem size_pow_mul {x : ℕ} (h : 0 < x) (k : ℕ) :
    Nat.size (2 ^ k * x) = Nat.size x + k := by
  rw [Nat.mul_comm, size_mul_pow h k]

theorem size_div_pow {x m : ℕ} (h : 2 ^ m ≤ x) :
    Nat.size (x / 2 ^ m) = Nat.size x - m := by
  have pos : 0 < x := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) h
  have lt_size : m < Nat.size x := by rwa [Nat.lt_size]
  apply size_of_le_of_lt
    -- ⊢ 2 ^ (Nat.size x - m - 1) ≤ x / 2 ^ m
  . have le_size_pred : m ≤ Nat.size x - 1 := Nat.le_pred_of_lt lt_size
    rewrite [tsub_right_comm, ← Nat.pow_div le_size_pred two_pos]
    apply Nat.div_le_div_right
    exact le_size_of_pos pos
  -- ⊢ x / 2 ^ m < 2 ^ (Nat.size x - m)
  . have pow_dvd : 2 ^ m ∣ 2 ^ Nat.size x := pow_dvd_pow 2 lt_size.le
    rewrite [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _),
      ← Nat.pow_div lt_size.le two_pos,
      Nat.div_mul_cancel pow_dvd]
    exact Nat.lt_size_self x

theorem size_div_mul {x m : ℕ} (h : 2 ^ m ≤ x) :
    Nat.size (x / 2 ^ m * 2 ^ m) = Nat.size x := by
  have div_pow_pos : 0 < x / 2 ^ m := Nat.div_pos h (Nat.two_pow_pos _)
  rewrite [size_mul_pow div_pow_pos m, size_div_pow h]
  apply tsub_add_cancel_of_le
  apply Nat.le_of_pred_lt
  rewrite [Nat.lt_size]
  calc 2 ^ Nat.pred m
    _ ≤ 2 ^ m := Nat.pow_le_pow_right two_pos (Nat.pred_le m)
    _ ≤ x     := h

theorem mod_eq_sub_div_mul {m k : ℕ} : m % k = m - m / k * k :=
  eq_tsub_of_add_eq <| Nat.mod_add_div' m k
