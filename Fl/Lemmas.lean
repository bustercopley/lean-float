import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Order.Lemmas

theorem two_pow_pos {m : ℕ} : 0 < 2 ^ m := Nat.pos_pow_of_pos m two_pos

theorem lt_of_pos_of_le_sub_one {m n : ℕ} (k : 0 < n) (h : m ≤ n - 1) : m < n :=
  Nat.sub_add_cancel k ▸ (Nat.add_le_add_right h 1)

theorem le_sub_one_iff_lt_of_pos {m n : ℕ} (k : 0 < n) : m ≤ n - 1 ↔ m < n :=
  ⟨lt_of_pos_of_le_sub_one k, Nat.le_pred_of_lt⟩

theorem sub_one_lt_of_pos_of_le {m n : ℕ} (h : 0 < m) : m ≤ n → m - 1 < n := by
  rewrite [← Nat.sub_add_cancel h]
  exact id

theorem le_iff_sub_one_lt_of_pos {m n : ℕ} (h : 0 < m) : m ≤ n ↔ m - 1 < n := by
  exact ⟨sub_one_lt_of_pos_of_le h, Nat.le_of_pred_lt⟩

theorem tsub_tsub_assoc' {a b c : ℕ} (h₁ : b ≤ c + a) (h₂ : c ≤ b)
: a - (b - c) = a + c - b := by
  apply tsub_eq_of_eq_add
  rewrite [← add_tsub_assoc_of_le h₂]
  rewrite [Nat.add_comm a c]
  rewrite [tsub_add_cancel_of_le h₁]
  rewrite [Nat.add_comm c a]
  rw [add_tsub_cancel_right]

theorem sub_div_of_pos_of_dvd {x d : ℕ} (hpos : 0 < d) (hdvd : d ∣ x) : x - x / d = (d - 1) * x / d := by
  apply Nat.eq_of_mul_eq_mul_left hpos
  rewrite [mul_comm d, mul_comm d, Nat.mul_sub_right_distrib]
  have : d ∣ (d - 1) * x := by
    conv => lhs ; rewrite [← Nat.one_mul d]
    exact Nat.mul_dvd_mul ⟨d - 1, Eq.symm $ Nat.one_mul _⟩ hdvd
  rewrite [Nat.div_mul_cancel hdvd, Nat.div_mul_cancel this]
  rw [← Nat.mul_pred_right, ← Nat.sub_one, Nat.mul_comm]

theorem sub_half_of_even {x : ℕ} (d : 2 ∣ x) : x - x / 2 = x / 2 := by
  have h₀ : 2 - 1 = 1 := by rw [← one_add_one_eq_two, add_tsub_cancel_right]
  have h₁ := sub_div_of_pos_of_dvd two_pos d
  rewrite [h₀, one_mul] at h₁
  exact h₁

theorem le_sub_of_dvd_of_dvd_of_lt {n m k : ℕ}
  (h₁ : k ∣ n) (h₂ : k ∣ m) (h₃ : n < m)
: n ≤ m - k := by
  have ⟨d, hd⟩ := h₁
  have ⟨e, he⟩ := h₂
  have h₀ : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) h₃
  rewrite [he, pos_iff_ne_zero, mul_ne_zero_iff,
      ← pos_iff_ne_zero, ← pos_iff_ne_zero] at h₀
  rewrite [hd, he, ← Nat.mul_pred_right, ← Nat.sub_one]
  apply Nat.mul_le_mul_left
  rewrite [← Nat.lt_iff_le_pred h₀.right]
  refine lt_of_mul_lt_mul_left ?_ (Nat.zero_le k)
  rewrite [← hd, ← he]
  exact h₃

theorem add_le_of_dvd_of_dvd_of_lt {n m k : ℕ}
  (h₁ : k ∣ n) (h₂ : k ∣ m) (h₃ : m < n)
: m + k ≤ n := by
  have ⟨d, hd⟩ := h₁
  have ⟨e, he⟩ := h₂
  have h₀ : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) h₃
  rewrite [hd, pos_iff_ne_zero, mul_ne_zero_iff,
      ← pos_iff_ne_zero, ← pos_iff_ne_zero] at h₀
  rewrite [hd, he, ← Nat.mul_succ, ← Nat.add_one]
  apply Nat.mul_le_mul_left
  rewrite [Nat.succ_le]
  refine lt_of_mul_lt_mul_left ?_ (Nat.zero_le k)
  rewrite [← hd, ← he]
  exact h₃

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

theorem div_mul_div_cancel_of_pos_of_dvd {n m k : ℕ} (h₁ : 0 < k) (h₂ : k ∣ m)
: n / k * k / m = n / m := by
  have ⟨d, hd⟩ := h₂
  rw [hd,
      ← Nat.div_div_eq_div_mul,
      Nat.mul_div_cancel _ h₁,
      Nat.div_div_eq_div_mul]

theorem div_mul_pred_eq_sub_of_pos_of_dvd {a b : ℕ}
  (h₀ : 0 < a) (h₂ : 0 < b) (h₁ : a ∣ b)
: (b - 1) / a * a = b - a := by
  apply Nat.le_antisymm
  . apply le_sub_of_dvd_of_dvd_of_lt
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

theorem sub_mul_mod_self_left (x y z : ℕ) (h : y * z ≤ x)
: (x - y * z) % y = x % y := by
  match z with
  | 0 => rw [Nat.mul_zero, Nat.sub_zero]
  | Nat.succ z =>
    rewrite [Nat.mul_succ] at h
    have k : y * z ≤ x := Nat.le_trans (Nat.le_add_right _ _) h
    have l : y ≤ x - y * z := by rwa [le_tsub_iff_right k, Nat.add_comm]
    rw [Nat.mul_succ, ← tsub_tsub, ← Nat.mod_eq_sub_mod l, sub_mul_mod_self_left _ _ z k]

theorem mod_sub_mod (m n k : ℕ) (h : k ≤ m)
: (m - k) % n = (m - k % n) % n:= by
  have h₀ : (m - k) % n = (m - k % n - n * (k / n)) % n := by rw [tsub_tsub, Nat.mod_add_div]
  rewrite [h₀]
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
    rewrite [Nat.pred_eq_sub_one, Nat.lt_size]
    exact hl

theorem le_size_of_pos {x : ℕ} (pos : 0 < x) : 2 ^ (Nat.size x - 1) ≤ x := by
  rewrite [← Nat.lt_size]
  exact Nat.sub_lt (Nat.size_pos.mpr pos) one_pos

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
  rewrite [← Nat.shiftl_eq_mul_pow x k]
  rw [Nat.size_shiftl nz]

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
    rewrite [Nat.sub.right_comm]
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
  apply Nat.sub_add_cancel
  apply Nat.le_of_pred_lt
  rewrite [Nat.lt_size]
  calc 2 ^ Nat.pred m
    ≤ 2 ^ m := Nat.pow_le_pow_of_le_right two_pos (Nat.pred_le m)
    _ ≤ x := h

theorem size_pred_lt_size_iff_pow {a : ℕ} (h : 0 < a) :
  a = 2 ^ (Nat.size a - 1) ↔ Nat.size (a - 1) < Nat.size a := by
  have size_pos : 0 < Nat.size a := by
    rewrite [Nat.size_pos]
    exact h
  apply Iff.intro
  . intro hl
    rewrite [← le_sub_one_iff_lt_of_pos size_pos]
    rewrite [Nat.size_le]
    rewrite [← le_iff_sub_one_lt_of_pos h]
    exact le_of_eq hl
  . intro hr
    apply le_antisymm
    . apply Nat.le_of_pred_lt
      rewrite [← Nat.size_le]
      rewrite [← Nat.lt_iff_le_pred size_pos]
      exact hr
    . exact le_size_of_pos h

theorem pred_size_le_size_pred {a : ℕ} (h : 0 < a) :
  Nat.size a - 1 ≤ Nat.size (a - 1) := by
  cases le_or_gt 2 a with
  | inl two_le =>
  . have h' : 2 ^ (Nat.size a - 1 - 1) ≤ a := by
      trans 2 ^ (Nat.size a - 1)
      . apply Nat.pow_le_pow_of_le_right two_pos
        exact tsub_le_self
      . exact le_size_of_pos h
    have one_lt_size : 1 < Nat.size a := Nat.lt_size.mpr two_le
    have one_le_size_sub_one : 1 ≤ Nat.size a - 1 := Nat.le_pred_of_lt one_lt_size
    apply Nat.le_of_pred_lt
    rewrite [Nat.pred_eq_sub_one]
    rewrite [Nat.lt_size]
    trans a - 2 ^ (Nat.size a - 1 - 1)
    . rewrite [Nat.le_sub_iff_add_le h']
      rewrite [← two_mul, ← pow_succ]
      rewrite [← Nat.lt_size]
      rewrite [← Nat.add_one_le_iff]
      rewrite [Nat.sub_add_cancel one_le_size_sub_one]
      rw [Nat.sub_add_cancel (le_of_lt one_lt_size)]
    . exact tsub_le_tsub_left (Nat.succ_le_of_lt two_pow_pos) a
  | inr lt_two =>
    have eq_one : a = 1 := Nat.eq_of_le_of_lt_succ h lt_two
    rewrite [eq_one, Nat.sub_self, Nat.size_zero, Nat.size_one, Nat.sub_self]
    exact le_rfl

theorem size_pred_eq_pred_size_of_eq_pow {a : ℕ} (h : 0 < a) :
  a = 2 ^ (Nat.size a - 1) → Nat.size (a - 1) = Nat.size a - 1 := by
  have size_pos : 0 < Nat.size a := by
    rewrite [Nat.size_pos]
    exact h
  intro hl
  apply le_antisymm
  . rewrite [← Nat.lt_iff_le_pred size_pos]
    rewrite [← size_pred_lt_size_iff_pow h]
    exact hl
  . exact pred_size_le_size_pred h
