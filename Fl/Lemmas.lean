import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Order.Lemmas

namespace Fl.Lemmas

theorem two_pow_pos {m : ℕ} : 0 < 2 ^ m := Nat.pos_pow_of_pos m two_pos

theorem two_pow_pos' (m : ℕ) : 0 < 2 ^ m := Nat.pos_pow_of_pos m two_pos

theorem lt_of_pos_of_le_sub_one {m n : ℕ} (k : 0 < n) (h : m ≤ n - 1) : m < n :=
  Nat.sub_add_cancel k ▸ (Nat.add_le_add_right h 1)

theorem le_sub_one_iff_lt_of_pos {m n : ℕ} (k : 0 < n) : m ≤ n - 1 ↔ m < n :=
  ⟨lt_of_pos_of_le_sub_one k, Nat.le_pred_of_lt⟩

theorem sub_one_lt_of_pos_of_le {m n : ℕ} (h : 0 < m) : m ≤ n → m - 1 < n := by
  rw [← Nat.sub_add_cancel h]
  exact id

theorem le_iff_sub_one_lt_of_pos {m n : ℕ} (h : 0 < m) : m ≤ n ↔ m - 1 < n := by
  exact ⟨sub_one_lt_of_pos_of_le h, Nat.le_of_pred_lt⟩

theorem eq_zero_of_le_sub {n m : ℕ} (k : 0 < m) (h : n ≤ n - m) : n = 0 := by
  revert h
  rw [← not_imp_not, not_le]
  intro h
  exact Nat.sub_lt (Nat.zero_lt_of_ne_zero h) k

theorem le_of_le_of_sub_le_sub_left {m n k : Nat}
  (h₁ : n ≤ k) (h₂ : k - m ≤ k - n) : n ≤ m := by
  rw [← Nat.sub_sub_self h₁, tsub_le_iff_left, ← tsub_le_iff_right]
  exact h₂

theorem le_of_lt_of_sub_le_sub_left {m n k : Nat}
  (h₁ : m < k) (h₂ : k - m ≤ k - n) : n ≤ m := by
  cases lt_or_ge k n with
  | inl hkn =>
    exfalso
    apply Nat.lt_le_antisymm h₁
    apply Nat.le_of_sub_eq_zero
    apply Nat.eq_zero_of_le_zero
    trans k - n
    . exact h₂
    . apply Nat.le_of_eq
      apply Nat.sub_eq_zero_of_le
      apply Nat.le_of_lt
      exact hkn
  | inr hnk => exact le_of_le_of_sub_le_sub_left hnk h₂

theorem div_mul_div_cancel {n m k : ℕ} (h₁ : 0 < k) (h₂ : k ∣ m) :
  n / k * k / m = n / m := by
  have ⟨d, hd⟩ := h₂
  rw [hd,
      ← Nat.div_div_eq_div_mul,
      Nat.mul_div_cancel _ h₁,
      Nat.div_div_eq_div_mul]

theorem div_mul_eq_of_dvd_of_le_of_lt {m k x : ℕ}
  (h₁ : k ∣ m) (h₂ : m ≤ x) (h₃ : x < m + k) :
  x / k * k = m := by
  have ⟨d, hd⟩ := h₁
  rw [hd, mul_comm k] at h₂ h₃ ⊢
  apply congr_arg (fun w ↦ w * k)
  rw [← Nat.succ_mul] at h₃
  exact Nat.div_eq_of_lt_le h₂ h₃

theorem div_mul_eq_of_le_of_lt' {m k x : ℕ} (h : k ≤ m) :
  2 ^ m ≤ x → x < 2 ^ m + 2 ^ k → x / 2 ^ k * 2 ^ k = 2 ^ m := by
  apply div_mul_eq_of_dvd_of_le_of_lt
  exact pow_dvd_pow 2 h

theorem div_eq_sub_div_mul_pred {x a : ℕ} (d : a ∣ x) (pos : 0 < a) :
  x / a = x - x / a * (a - 1) := by
  apply Nat.eq_of_mul_eq_mul_left pos
  rw [Nat.mul_sub_left_distrib]
  rw [← Nat.mul_assoc, mul_comm a (x / a), Nat.div_mul_cancel d, mul_comm a x]
  rw [← Nat.mul_sub_left_distrib]
  rw [Nat.pos_iff_ne_zero, ← Nat.one_le_iff_ne_zero] at pos
  rw [Nat.sub_sub_self pos]
  rw [mul_one]

theorem mod_eq_sub_div_mul {n m : ℕ} : n % m = n - n / m * m := by
  rw [eq_tsub_iff_add_eq_of_le (Nat.div_mul_le_self _ _)]
  exact Nat.mod_add_div' _ _

theorem mul_pos_iff {n m : ℕ} : 0 < n * m ↔ 0 < n ∧ 0 < m := by
  rw [pos_iff_ne_zero, pos_iff_ne_zero, pos_iff_ne_zero]
  exact mul_ne_zero_iff

theorem sub_half_of_even {x : ℕ} (d : 2 ∣ x) : x - x / 2 = x / 2 := by
  apply Nat.eq_of_mul_eq_mul_left two_pos
  rw [mul_comm 2, mul_comm 2, Nat.mul_sub_right_distrib]
  rw [Nat.div_mul_cancel d, ← Nat.mul_pred_right]
  rw [(rfl : 2 = 2)]
  rw [Nat.pred_succ, mul_one]

theorem lt_of_size_lt_size {x y : ℕ} (h : x.size < y.size) : x < y := by
  cases Nat.lt_or_ge x y with
  | inl hxy => exact hxy
  | inr hyx =>
    exfalso
    apply Nat.lt_le_antisymm h (Nat.size_le_size hyx)

theorem le_sub_of_dvd_of_dvd_of_lt {n m k : ℕ}
  (h₁ : k ∣ n) (h₂ : k ∣ m) (h₃ : n < m) : n ≤ m - k := by
  have ⟨d, hd⟩ := h₁
  have ⟨e, he⟩ := h₂
  have h₀ : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) h₃
  rw [he, pos_iff_ne_zero, mul_ne_zero_iff,
      ← pos_iff_ne_zero, ← pos_iff_ne_zero] at h₀
  rw [hd, he, ← Nat.mul_pred_right, ← Nat.sub_one]
  apply Nat.mul_le_mul_left
  rw [← Nat.lt_iff_le_pred h₀.right]
  refine lt_of_mul_lt_mul_left ?_ (Nat.zero_le k)
  rw [← hd, ← he]
  exact h₃

theorem add_div_of_pos_of_dvd {x y k : ℕ} (hpos : 0 < k) (hdvd : k ∣ x) :
  (x + y) / k = x / k + y / k := by
  have ⟨d, hd⟩ := hdvd
  rw [Nat.add_comm x, hd, Nat.add_mul_div_left _ _ hpos,
      Nat.mul_div_cancel_left _ hpos, Nat.add_comm]

theorem div_mul_pred_eq_sub_of_pos_of_dvd {a b : ℕ}
  (h₀ : 0 < a) (h₂ : 0 < b) (h₁ : a ∣ b) :
  (b - 1) / a * a = b - a := by
  apply Nat.le_antisymm
  . apply Lemmas.le_sub_of_dvd_of_dvd_of_lt
    . exact Nat.dvd_mul_left _ _
    . exact h₁
    . apply Nat.lt_of_le_of_lt (m := b - 1)
      . exact Nat.div_mul_le_self _ _
      . apply Nat.sub_lt h₂ zero_lt_one
  . rw [tsub_le_iff_right,
        ← Nat.succ_mul,
        ← Nat.add_div_right _ h₀,
        ← Nat.sub_add_comm (Nat.one_le_of_lt h₂),
        Nat.add_sub_assoc (Nat.one_le_of_lt h₀)]
    trans b / a * a
    . rw [Nat.div_mul_cancel h₁]
    . apply Nat.mul_le_mul_right
      apply Nat.div_le_div_right
      exact Nat.le_add_right _ _

theorem size_mul_pow {x : ℕ} (h : 0 < x) (m : ℕ) :
  Nat.size (x * 2 ^ m) = x.size + m := by
  rw [← Nat.shiftl_eq_mul_pow x m]
  rw [Nat.size_shiftl (ne_zero_of_lt h) m]

theorem size_pow_mul {x : ℕ} (h : 0 < x) (m : ℕ) :
  Nat.size (2 ^ m * x) = x.size + m :=
  Nat.mul_comm x (2 ^ m) ▸ (size_mul_pow h m)

theorem le_size_of_pos {x : ℕ} (h : 0 < x) : 2 ^ (x.size - 1) ≤ x := by
  rw [← Nat.lt_size]
  apply Nat.pred_lt (n := x.size)
  apply ne_zero_of_lt
  rw [Nat.size_pos]
  exact h

theorem size_pred_lt_size_iff_pow {a : ℕ} (h : 0 < a) :
  a = 2 ^ (a.size - 1) ↔ (a - 1).size < a.size := by
  have size_pos : 0 < a.size := by
    rw [Nat.size_pos]
    exact h
  apply Iff.intro
  . intro hl
    rw [← le_sub_one_iff_lt_of_pos size_pos]
    rw [Nat.size_le]
    rw [← le_iff_sub_one_lt_of_pos h]
    exact le_of_eq hl
  . intro hr
    apply le_antisymm
    . apply Nat.le_of_pred_lt
      rw [← Nat.size_le]
      rw [← Nat.lt_iff_le_pred size_pos]
      exact hr
    . exact le_size_of_pos h

theorem pred_size_le_size_pred {a : ℕ} (h : 0 < a) :
  a.size - 1 ≤ (a - 1).size := by
  cases le_or_gt 2 a with
  | inl two_le =>
  . have h' : 2 ^ (a.size - 1 - 1) ≤ a := by
      trans 2 ^ (a.size - 1)
      . apply Nat.pow_le_pow_of_le_right two_pos
        exact Nat.sub_le _ _
      . exact le_size_of_pos h
    have one_lt_size : 1 < a.size := Nat.lt_size.mpr two_le
    have one_le_size_sub_one : 1 ≤ a.size - 1 := Nat.le_pred_of_lt one_lt_size
    apply Nat.le_of_pred_lt
    rw [Nat.pred_eq_sub_one]
    rw [Nat.lt_size]
    trans a - 2 ^ (Nat.size a - 1 - 1)
    . rw [Nat.le_sub_iff_add_le h']
      rw [← two_mul, ← pow_succ]
      rw [← Nat.lt_size]
      rw [← Nat.add_one_le_iff]
      rw [Nat.sub_add_cancel one_le_size_sub_one]
      rw [Nat.sub_add_cancel (le_of_lt one_lt_size)]
    . exact tsub_le_tsub_left (Nat.succ_le_of_lt two_pow_pos) a
  | inr lt_two =>
    have eq_one : a = 1 := Nat.eq_of_le_of_lt_succ h lt_two
    rw [eq_one, Nat.sub_self, Nat.size_zero, Nat.size_one, Nat.sub_self]
    exact le_rfl

theorem size_pred_eq_pred_size_iff_pow {a : ℕ} (h : 0 < a) :
  a = 2 ^ (a.size - 1) ↔ (a - 1).size = a.size - 1 := by
  have size_pos : 0 < a.size := by
    rw [Nat.size_pos]
    exact h
  apply Iff.intro
  . intro hl
    apply le_antisymm
    . rw [← Nat.lt_iff_le_pred size_pos]
      rw [← size_pred_lt_size_iff_pow h]
      exact hl
    . exact pred_size_le_size_pred h
  . intro hr
    rw [size_pred_lt_size_iff_pow h]
    rw [Nat.lt_iff_le_pred size_pos]
    exact le_of_eq hr

theorem size_pred_eq_pred_size_of_eq_pow {a : ℕ} (h : 0 < a) :
  a = 2 ^ (a.size - 1) → (a - 1).size = a.size - 1 := by
  have size_pos : 0 < a.size := by
    rw [Nat.size_pos]
    exact h
  intro hl
  apply le_antisymm
  . rw [← Nat.lt_iff_le_pred size_pos]
    rw [← size_pred_lt_size_iff_pow h]
    exact hl
  . exact pred_size_le_size_pred h

theorem size_pred_eq_size_self_of_ne_pow {a : ℕ} (h : 0 < a) :
  a ≠ 2 ^ (a.size - 1) → (a - 1).size = a.size := by
  rw [Ne, not_iff_not.mpr (size_pred_eq_pred_size_iff_pow h), ← Ne]
  intro h'
  apply le_antisymm
  . exact Nat.size_le_size (Nat.sub_le _ _)
  . rw [le_iff_sub_one_lt_of_pos (Nat.size_pos.mpr h)]
    exact lt_of_le_of_ne (pred_size_le_size_pred h) h'.symm

theorem size_range_of_pos {x : ℕ} (pos : 0 < x) :
  2 ^ (x.size - 1) ≤ x ∧ x < 2 ^ x.size :=
  ⟨le_size_of_pos pos, Nat.lt_size_self x⟩

theorem size_of_le_of_lt {x n : ℕ} (hl : 2 ^ (n - 1) ≤ x) (hr : x < 2 ^ n) :
  x.size = n :=
  Nat.le_antisymm (Nat.size_le.mpr hr) (Nat.le_of_pred_lt (Nat.lt_size.mpr hl))

theorem size_range_iff_of_pos {x n : ℕ} (pos : 0 < x) :
  x.size = n ↔ 2 ^ (n - 1) ≤ x ∧ x < 2 ^ n :=
  ⟨fun hl ↦ hl ▸ (size_range_of_pos pos), And.elim size_of_le_of_lt⟩

theorem size_div_pow {x m : ℕ} (h : 2 ^ m ≤ x) :
  Nat.size (x / 2 ^ m) = Nat.size x - m := by
  have div_pow_pos : 0 < x / 2 ^ m := Nat.div_pos h two_pow_pos
  have pos : 0 < x := lt_of_lt_of_le two_pow_pos h
  have range := size_range_of_pos pos
  have lt_size : m < x.size := Nat.lt_size.mpr h
  rw [size_range_iff_of_pos div_pow_pos]
  apply And.intro
    -- ⊢ 2 ^ (x.size - 1 - m) ≤ x / 2 ^ m
  . have le_size_pred : m ≤ x.size - 1 := Nat.le_pred_of_lt lt_size
    rw [Nat.sub.right_comm]
    rw [← Nat.pow_div le_size_pred two_pos]
    apply Nat.div_le_div_right
    exact range.left
  -- ⊢ x / 2 ^ m < 2 ^ (x.size - m)
  . have le_size : m ≤ x.size := le_of_lt lt_size
    have pow_dvd : 2 ^ m ∣ 2 ^ x.size := pow_dvd_pow 2 le_size
    rw [Nat.div_lt_iff_lt_mul two_pow_pos]
    rw [← Nat.pow_div le_size two_pos]
    rw [Nat.div_mul_cancel pow_dvd]
    exact range.right

theorem size_div_mul {x m : ℕ} (h : 2 ^ m ≤ x) :
  (x / 2 ^ m * 2 ^ m).size = x.size := by
  have div_pow_pos : 0 < x / 2 ^ m := Nat.div_pos h two_pow_pos
  rewrite [size_mul_pow div_pow_pos m]
  rewrite [size_div_pow h]
  -- ⊢ x.size - m + m = x.size
  apply Nat.sub_add_cancel
  -- ⊢ m ≤ x.size
  apply Nat.le_of_pred_lt
  rewrite [Nat.lt_size]
  -- ⊢ 2 ^ m.pred ≤ x
  trans 2 ^ m
  . apply Nat.pow_le_pow_of_le_right two_pos
    exact Nat.pred_le m
  . exact h

theorem tsub_tsub_assoc' {a b c : ℕ} (h₁ : b ≤ c + a) (h₂ : c ≤ b)
: a - (b - c) = a + c - b := by
  apply tsub_eq_of_eq_add
  rewrite [← add_tsub_assoc_of_le h₂]
  rewrite [Nat.add_comm a c]
  rewrite [tsub_add_cancel_of_le h₁]
  rewrite [Nat.add_comm c a]
  rw [add_tsub_cancel_right]

end Fl.Lemmas
