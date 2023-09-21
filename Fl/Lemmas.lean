import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Order.Lemmas

theorem two_pow_pos {m : ℕ} : 0 < 2 ^ m := Nat.pos_pow_of_pos m two_pos

theorem add_tsub_assoc' {a b c : ℕ} (h₁ : b ≤ c + a) (h₂ : c ≤ b)
: a + c - b = a - (b - c) := by
  apply eq_tsub_of_add_eq
  rewrite [← add_tsub_assoc_of_le h₂]
  rewrite [Nat.add_comm a c]
  rewrite [tsub_add_cancel_of_le h₁]
  rewrite [Nat.add_comm c a]
  exact add_tsub_cancel_right a c

theorem sub_div_of_pos_of_dvd {x d : ℕ} (hpos : 0 < d) (hdvd : d ∣ x)
: x - x / d = (d - 1) * x / d := by
  apply Nat.eq_of_mul_eq_mul_left hpos
  rewrite [mul_comm d, mul_comm d, Nat.mul_sub_right_distrib]
  have hdvd' : d ∣ (d - 1) * x := Nat.dvd_trans hdvd (Nat.dvd_mul_left _ _)
  rewrite [Nat.div_mul_cancel hdvd, Nat.div_mul_cancel hdvd']
  rewrite [Nat.sub_one, Nat.mul_pred_left]
  rw [Nat.mul_comm]

theorem sub_half_of_even {x : ℕ} (d : 2 ∣ x) : x - x / 2 = x / 2 := by
  have h₀ : 2 - 1 = 1 := by rw [← one_add_one_eq_two, add_tsub_cancel_right]
  have h₁ := sub_div_of_pos_of_dvd two_pos d
  rewrite [h₀, one_mul] at h₁
  exact h₁

theorem add_le_of_dvd_of_dvd_of_lt {n m k : ℕ}
  (h₁ : k ∣ n) (h₂ : k ∣ m) (h₃ : m < n)
: m + k ≤ n := by
  apply Nat.le_of_lt_add_of_dvd
  . exact Nat.add_lt_add_right h₃ k
  . exact Nat.dvd_add h₂ (Nat.dvd_refl _)
  . exact h₁

theorem le_sub_of_dvd_of_dvd_of_lt {n m k : ℕ}
  (h₁ : k ∣ n) (h₂ : k ∣ m) (h₃ : n < m)
: n ≤ m - k := by
  rewrite [le_tsub_iff_right]
  apply add_le_of_dvd_of_dvd_of_lt h₂ h₁ h₃
  exact Nat.le_of_dvd (Nat.zero_lt_of_lt h₃) h₂

theorem div_mul_eq_of_dvd_of_le_of_lt {m k x : ℕ}
  (h₁ : k ∣ m) (h₂ : m ≤ x) (h₃ : x < m + k)
: x / k * k = m := by
  have ⟨d, hd⟩ := h₁
  rewrite [hd, mul_comm k] at h₂ h₃ ⊢
  rewrite [← Nat.succ_mul] at h₃
  rw [Nat.div_eq_of_lt_le h₂ h₃]

theorem div_mul_eq_of_le_of_lt {m k x : ℕ} (h : k ≤ m)
: 2 ^ m ≤ x → x < 2 ^ m + 2 ^ k → x / 2 ^ k * 2 ^ k = 2 ^ m := by
  apply div_mul_eq_of_dvd_of_le_of_lt
  exact pow_dvd_pow 2 h

theorem div_mul_div_cancel_of_dvd {n m k : ℕ} (h₂ : k ∣ m)
: n / k * k / m = n / m := by
  have ⟨d, hd⟩ := h₂
  rewrite [hd]
  match k with
  | 0 => rw [Nat.mul_zero, Nat.zero_mul, Nat.zero_div, Nat.div_zero]
  | x + 1 =>
    rewrite [← Nat.div_div_eq_div_mul]
    rewrite [Nat.mul_div_cancel _ (Nat.add_pos_right _ zero_lt_one)]
    exact Nat.div_div_eq_div_mul _ _ _

theorem div_mul_pred_eq_sub_of_pos_of_dvd {a b : ℕ}
  (h₀ : 0 < a) (h₂ : 0 < b) (h₁ : a ∣ b)
: (b - 1) / a * a = b - a := by
  apply Nat.le_antisymm
  . apply le_sub_of_dvd_of_dvd_of_lt
    . exact Nat.dvd_mul_left _ _
    . exact h₁
    . apply Nat.lt_of_le_of_lt (m := b - 1)
      . exact Nat.div_mul_le_self _ _
      . apply tsub_lt_self h₂ zero_lt_one
  . rewrite [tsub_le_iff_right]
    rewrite [← Nat.succ_mul]
    rewrite [← Nat.add_div_right _ h₀]
    rewrite [tsub_add_eq_add_tsub (Nat.one_le_of_lt h₂)]
    rewrite [add_tsub_assoc_of_le (Nat.one_le_of_lt h₀)]
    trans b / a * a
    . rw [Nat.div_mul_cancel h₁]
    . apply Nat.mul_le_mul_right
      apply Nat.div_le_div_right
      exact Nat.le_add_right _ _

theorem sub_mul_mod_self_left (x y z : ℕ) (h : y * z ≤ x)
: (x - y * z) % y = x % y := by
  match z with
  | 0 => rw [Nat.mul_zero, tsub_zero]
  | Nat.succ z =>
    rewrite [Nat.mul_succ] at h
    have k : y * z ≤ x := Nat.le_trans (Nat.le_add_right _ _) h
    have l : y ≤ x - y * z := by
      rewrite [le_tsub_iff_right k]
      rewrite [Nat.add_comm]
      exact h
    rewrite [Nat.mul_succ]
    rewrite [← tsub_tsub]
    rewrite [← Nat.mod_eq_sub_mod l]
    exact sub_mul_mod_self_left x y z k

theorem mod_sub_mod (m n k : ℕ) (h : k ≤ m)
: (m - k) % n = (m - k % n) % n:= by
  conv => lhs ; rewrite [← Nat.mod_add_div k n, ← tsub_tsub]
  apply sub_mul_mod_self_left
  apply le_tsub_of_add_le_left
  rewrite [Nat.mod_add_div]
  exact h

theorem size_of_le_of_lt {x n : ℕ} (hl : 2 ^ (n - 1) ≤ x) (hr : x < 2 ^ n)
: Nat.size x = n := by
  apply Nat.le_antisymm
  . rewrite [Nat.size_le]
    exact hr
  . apply Nat.le_of_pred_lt
    rewrite [← Nat.sub_one, Nat.lt_size]
    exact hl

theorem le_size_of_pos {x : ℕ} (pos : 0 < x) : 2 ^ (Nat.size x - 1) ≤ x := by
  rewrite [← Nat.lt_size]
  exact tsub_lt_self (Nat.size_pos.mpr pos) one_pos

theorem lt_of_size_lt_size {x y : ℕ} (h : Nat.size x < Nat.size y)
: x < y := by
  apply Nat.lt_of_not_le
  intro (hle : y ≤ x)
  -- ⊢ False
  apply Nat.lt_le_antisymm h
  apply Nat.size_le_size
  exact hle

theorem size_mul_pow {x : ℕ} (h : 0 < x) (k : ℕ)
: Nat.size (x * 2 ^ k) = Nat.size x + k := by
  have nz : x ≠ 0 := by rwa [← Nat.pos_iff_ne_zero]
  rewrite [← Nat.shiftLeft_eq_mul_pow x k]
  rw [Nat.size_shiftLeft nz]

theorem size_pow_mul {x : ℕ} (h : 0 < x) (k : ℕ)
: Nat.size (2 ^ k * x) = Nat.size x + k := by
  rw [Nat.mul_comm, size_mul_pow h k]

theorem size_div_pow {x m : ℕ} (h : 2 ^ m ≤ x)
: Nat.size (x / 2 ^ m) = Nat.size x - m := by
  have pos : 0 < x := Nat.lt_of_lt_of_le two_pow_pos h
  have lt_size : m < Nat.size x := by rwa [Nat.lt_size]
  apply size_of_le_of_lt
    -- ⊢ 2 ^ (Nat.size x - m - 1) ≤ x / 2 ^ m
  . have le_size_pred : m ≤ Nat.size x - 1 := Nat.le_pred_of_lt lt_size
    rewrite [tsub_right_comm]
    rewrite [← Nat.pow_div le_size_pred two_pos]
    apply Nat.div_le_div_right
    exact le_size_of_pos pos
  -- ⊢ x / 2 ^ m < 2 ^ (Nat.size x - m)
  . have pow_dvd : 2 ^ m ∣ 2 ^ Nat.size x := pow_dvd_pow 2 lt_size.le
    rewrite [Nat.div_lt_iff_lt_mul two_pow_pos]
    rewrite [← Nat.pow_div lt_size.le two_pos]
    rewrite [Nat.div_mul_cancel pow_dvd]
    exact Nat.lt_size_self x

theorem size_div_mul {x m : ℕ} (h : 2 ^ m ≤ x)
: Nat.size (x / 2 ^ m * 2 ^ m) = Nat.size x := by
  have div_pow_pos : 0 < x / 2 ^ m := Nat.div_pos h two_pow_pos
  rewrite [size_mul_pow div_pow_pos m]
  rewrite [size_div_pow h]
  apply tsub_add_cancel_of_le
  apply Nat.le_of_pred_lt
  rewrite [Nat.lt_size]
  calc 2 ^ Nat.pred m
    ≤ 2 ^ m := Nat.pow_le_pow_of_le_right two_pos (Nat.pred_le m)
    _ ≤ x := h

theorem mod_eq_sub_div_mul {m k : ℕ} : m % k = m - m / k * k := by
  rewrite [eq_tsub_iff_add_eq_of_le (Nat.div_mul_le_self _ _)]
  rewrite [Nat.add_comm]
  exact Nat.div_add_mod' m k
