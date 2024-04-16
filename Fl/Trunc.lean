import Fl.Lemmas

def expt (n x : ℕ) : ℕ := Nat.size x - n
def ulp (n x : ℕ) : ℕ := 2 ^ expt n x
def trunc (n x : ℕ) : ℕ := x / ulp n x * ulp n x

theorem expt_le_expt (n : ℕ) {x y : ℕ} (h : x ≤ y) : expt n x ≤ expt n y := by
  unfold expt
  exact tsub_le_tsub_right (Nat.size_le_size h) n

theorem ulp_pos (n x : ℕ) : 0 < ulp n x :=
  Nat.two_pow_pos _

theorem ulp_le_ulp (n : ℕ) {x y : ℕ} (h : x ≤ y) : ulp n x ≤ ulp n y :=
  Nat.pow_le_pow_of_le_right two_pos (expt_le_expt n h)

theorem trunc_le (n x : ℕ) : trunc n x ≤ x :=
  Nat.div_mul_le_self _ _

theorem trunc_zero (n : ℕ) : trunc n 0 = 0 := by
  unfold trunc
  rw [Nat.zero_div, Nat.zero_mul]

theorem one_le_expt_of_no_uflow {n x : ℕ} (no_uflow : 2 ^ n ≤ x) :
    1 ≤ expt n x := by
  unfold expt
  apply le_tsub_of_add_le_left
  rewrite [Nat.add_one, Nat.succ_le, Nat.lt_size]
  exact no_uflow

theorem two_dvd_ulp_of_no_uflow {n x : ℕ} (no_uflow : 2 ^ n ≤ x) :
    2 ∣ ulp n x :=
  calc
    2 = 2 ^ 1 := (Nat.pow_one ..).symm
    _ ∣ 2 ^ expt n x := pow_dvd_pow 2 (one_le_expt_of_no_uflow no_uflow)

theorem expt_eq_zero_of_uflow {n x : ℕ} (uflow: x < 2 ^ n) : expt n x = 0 :=
  tsub_eq_zero_of_le (Nat.size_le.mpr uflow)

theorem ulp_eq_one_of_uflow {n x : ℕ} (uflow : x < 2 ^ n) : ulp n x = 1 := by
  unfold ulp
  rw [expt_eq_zero_of_uflow uflow, Nat.pow_zero]

theorem trunc_add_half_ulp_eq_of_uflow {n x : ℕ} (uflow : x < 2 ^ n) :
    trunc n x + ulp n x / 2 = x := by
  unfold trunc
  rw [ulp_eq_one_of_uflow uflow, Nat.mul_one, Nat.div_one,
    Nat.div_eq_of_lt one_lt_two, Nat.add_zero]

theorem trunc_eq_self_of_uflow {n x : ℕ} (uflow : x < 2 ^ n) :
    trunc n x = x := by
  unfold trunc
  rw [ulp_eq_one_of_uflow uflow, Nat.mul_one, Nat.div_one]

theorem ulp_dvd_ulp (n : ℕ) {x y : ℕ} (h : x ≤ y) : ulp n x ∣ ulp n y :=
  pow_dvd_pow 2 (expt_le_expt n h)

theorem ulp_dvd_trunc (n a : ℕ) : ulp n a ∣ trunc n a :=
  Nat.dvd_mul_left _ _

theorem ulp_dvd_of_trunc_eq {n a : ℕ} (h : trunc n a = a) :
    ulp n a ∣ a :=
  Eq.subst h (ulp_dvd_trunc n a)

theorem trunc_eq_of_le_of_ulp_dvd {n y : ℕ} (x : ℕ) (hle : y ≤ x)
    (hdvd : ulp n x ∣ y) : trunc n y = y :=
  Nat.div_mul_cancel (Nat.dvd_trans (ulp_dvd_ulp n hle) hdvd)

theorem trunc_pred_eq_sub_ulp_of_pos_of_trunc_eq {x n : ℕ} (xpos : 0 < x)
    (hfx : trunc n x = x) : trunc n (x - 1) = x - ulp n (x - 1) := by
  unfold trunc
  apply pred_div_mul_eq_sub_of_pos_of_dvd
  . exact ulp_pos n _
  . exact xpos
  . trans ulp n x
    . exact ulp_dvd_ulp n tsub_le_self
    . exact ulp_dvd_of_trunc_eq hfx

theorem trunc_eq_iff_ulp_dvd {a n : ℕ} :
    trunc n a = a ↔ ulp n a ∣ a :=
  ⟨ulp_dvd_of_trunc_eq, trunc_eq_of_le_of_ulp_dvd a le_rfl⟩

theorem trunc_eq_sub_mod (n x : ℕ) : trunc n x = x - x % (ulp n x) := by
  apply eq_tsub_of_add_eq
  exact Nat.div_add_mod' x (ulp n x)

theorem ulp_le_self {n x : ℕ} (npos : 0 < n) (xpos : 0 < x) : ulp n x ≤ x := by
  unfold ulp expt
  trans 2 ^ (Nat.size x - 1)
  . apply Nat.pow_le_pow_of_le_right two_pos
    exact tsub_le_tsub_left (Nat.one_le_of_lt npos) _
  . exact le_size_of_pos xpos

theorem size_trunc_eq_size {n : ℕ} (npos : 0 < n) (x : ℕ) :
    Nat.size (trunc n x) = Nat.size x := by
  unfold trunc ulp expt
  cases Nat.eq_zero_or_pos x with
  | inl zero => rw [zero, Nat.zero_div, Nat.zero_mul]
  | inr pos =>
    apply size_div_mul
    rewrite [← Nat.lt_size]
    exact tsub_lt_self (Nat.size_pos.mpr pos) npos

theorem ulp_trunc {n : ℕ} (npos : 0 < n) (x : ℕ) :
    ulp n (trunc n x) = ulp n x := by
  unfold ulp expt
  rw [size_trunc_eq_size npos x]

theorem trunc_idempotent {n : ℕ} (npos : 0 < n) (x : ℕ) :
    trunc n (trunc n x) = trunc n x := by
  rw [trunc, ulp_trunc npos, trunc, Nat.mul_div_cancel _ (ulp_pos _ _)]

theorem trunc_le_trunc {n x y : ℕ} (npos : 0 < n) (h : x ≤ y) :
    trunc n x ≤ trunc n y := by
  cases Nat.lt_or_ge (Nat.size x) (Nat.size y) with
  | inl size_lt_size =>
    rewrite [← size_trunc_eq_size npos x] at size_lt_size
    rewrite [← size_trunc_eq_size npos y] at size_lt_size
    exact le_of_lt (lt_of_size_lt_size size_lt_size)
  | inr size_ge_size =>
    have ulp_eq_ulp : ulp n x = ulp n y := by
      apply congr_arg (fun w => 2 ^ (w - n))
      exact Nat.le_antisymm (Nat.size_le_size h) size_ge_size
    unfold trunc
    rewrite [ulp_eq_ulp]
    exact Nat.mul_le_mul_right _ (Nat.div_le_div_right h)

theorem trunc_trunc_sub_ulp_eq {n x : ℕ} (npos : 0 < n) :
    trunc n (trunc n x - ulp n x) = trunc n x - ulp n x := by
  apply trunc_eq_of_le_of_ulp_dvd
  . exact tsub_le_self
  . rewrite [ulp_trunc npos]
    apply Nat.dvd_sub'
    . exact ulp_dvd_trunc n _
    . exact Nat.dvd_refl _

theorem trunc_sub_ulp_eq_of_trunc_eq {n x : ℕ} (npos : 0 < n)
    (h : trunc n x = x) : trunc n (x - ulp n x) = x - ulp n x := by
  rewrite [← h, ulp_trunc npos]
  exact trunc_trunc_sub_ulp_eq npos

theorem ulp_pow_mul {n x : ℕ} (npos : 0 < n) (h : n ≤ Nat.size x) (k : ℕ) :
    ulp n (2 ^ k * x) = 2 ^ k * ulp n x := by
  unfold ulp expt
  have pos : 0 < x := by
    rewrite [← Nat.size_pos]
    exact Nat.lt_of_lt_of_le npos h
  rw [← pow_add, size_pow_mul pos, ← tsub_add_eq_add_tsub h, Nat.add_comm]

theorem trunc_pow_mul {n : ℕ} (npos : 0 < n) (x k : ℕ) :
    trunc n ((2 ^ k) * x) = 2 ^ k * trunc n x := by
  cases Decidable.eq_or_ne x 0 with
  | inl eq_zero =>
    unfold trunc ulp expt
    rw [eq_zero, Nat.mul_zero, Nat.zero_div, Nat.zero_mul, Nat.mul_zero]
  | inr ne_zero =>
    cases Nat.lt_or_ge n (Nat.size x) with
    | inr size_le =>
      have uflow : x < 2 ^ n := by
        rewrite [← Nat.size_le]
        exact size_le.le
      have d : ulp n (2 ^ k * x) ∣ 2 ^ k * x := by
        unfold ulp expt
        apply dvd_mul_of_dvd_left
        rw [Nat.pow_dvd_pow_iff_le_right one_lt_two,
          size_pow_mul (Nat.zero_lt_of_ne_zero ne_zero), tsub_le_iff_left]
        apply Nat.add_le_add_right
        exact size_le
      rewrite [trunc_eq_self_of_uflow uflow]
      exact trunc_eq_of_le_of_ulp_dvd (2 ^ k * x) le_rfl d
    | inl lt_size =>
      unfold trunc
      rw [ulp_pow_mul npos (le_of_lt lt_size),
        Nat.mul_div_mul_left _ _ (Nat.two_pow_pos _),
        mul_rotate', Nat.mul_comm (ulp n x)]

theorem trunc_two_mul {n : ℕ} (npos : 0 < n) (x : ℕ) :
    trunc n (2 * x) = 2 * trunc n x := by
  rw [← pow_one 2, trunc_pow_mul npos x 1]

theorem trunc_le_size_sub_ulp {n : ℕ} (npos : 0 < n) (a : ℕ) :
    trunc n a ≤ 2 ^ Nat.size a - ulp n a := by
  rw [← size_trunc_eq_size npos, ← ulp_trunc npos]
  apply le_sub_of_dvd_of_dvd_of_lt
  . exact ulp_dvd_of_trunc_eq (trunc_idempotent npos _)
  . rewrite [ulp, expt, Nat.pow_dvd_pow_iff_le_right one_lt_two]
    exact tsub_le_self
  . exact Nat.lt_size_self _

theorem le_size_sub_ulp_of_trunc_eq {n : ℕ} (npos : 0 < n)
    (hfa : trunc n a = a) : a ≤ 2 ^ Nat.size a - ulp n a :=
  hfa.ge.trans (trunc_le_size_sub_ulp npos a)

theorem le_size_and_ulp_eq_of_no_uflow_of_carry {n a b : ℕ} (hba : b ≤ a)
    (no_uflow : 2 ^ n ≤ a + b) (carry : 2 ^ Nat.size a ≤ a + b) :
    n ≤ Nat.size a ∧ ulp n (a + b) = 2 * ulp n a := by
  have size_eq : Nat.size (a + b) = Nat.size a + 1 := by
    apply Nat.le_antisymm
    . rewrite [Nat.size_le, pow_succ, Nat.mul_two]
      apply Nat.add_lt_add
      . exact Nat.lt_size_self _
      . exact Nat.lt_of_le_of_lt hba (Nat.lt_size_self _)
    . rewrite [Nat.succ_le, Nat.lt_size]
      exact carry
  have le_size : n ≤ Nat.size a := by
    rewrite [← Nat.lt_succ, Nat.succ_eq_add_one]
    calc
      n < Nat.size (a + b) := by rwa [Nat.lt_size]
      _ = Nat.size a + 1   := size_eq
  have ulp_eq : ulp n (a + b) = 2 * ulp n a :=
    calc
      _ = 2 ^ (Nat.size (a + b) - n) := rfl
      _ = 2 ^ (Nat.size a + 1 - n)   := by rw [size_eq]
      _ = 2 ^ (Nat.size a - n + 1)   := by rw [← tsub_add_eq_add_tsub le_size]
      _ = 2 * 2 ^ (Nat.size a - n)   := by rw [pow_succ, mul_comm]
      _ = 2 * ulp n a                := rfl
  exact ⟨le_size, ulp_eq⟩

def next (n x : ℕ) : ℕ := x + ulp n x

theorem next_le_next (n : ℕ) {x y : ℕ} (h : x ≤ y) : next n x ≤ next n y :=
  Nat.add_le_add h (ulp_le_ulp n h)

theorem size_next_le_succ_size (n x : ℕ) :
    Nat.size (next n x) ≤ Nat.size x + 1 := by
  rewrite [Nat.size_le, Nat.pow_succ, Nat.mul_two]
  unfold next ulp
  rewrite [Nat.add_comm, ← Nat.add_one_le_iff, add_rotate]
  apply Nat.add_le_add
  . exact Nat.lt_size_self x
  . exact Nat.pow_le_pow_of_le_right two_pos tsub_le_self

theorem size_next_eq_size_of_no_carry {n x : ℕ}
    (no_carry : next n x < 2 ^ Nat.size x) :
    Nat.size (next n x) = Nat.size x := by
  apply Nat.le_antisymm
  . rwa [Nat.size_le]
  . exact Nat.size_le_size (Nat.le_add_right _ _)

theorem size_next_eq_succ_size_of_carry {x : ℕ}
    (carry : 2 ^ Nat.size x ≤ next n x) :
    Nat.size (next n x) = Nat.size x + 1 := by
  apply Nat.le_antisymm
  . exact size_next_le_succ_size n x
  . rwa [Nat.add_one, Nat.succ_le, Nat.lt_size]

theorem ulp_next_of_no_carry {n x : ℕ} (no_carry : next n x < 2 ^ Nat.size x) :
    ulp n (next n x) = ulp n x := by
  unfold ulp expt
  rw [size_next_eq_size_of_no_carry no_carry]

theorem trunc_next_of_no_carry {n x : ℕ}
    (no_carry : next n x < 2 ^ Nat.size x) :
    trunc n (next n x) = trunc n x + ulp n x := by
  rw [trunc, ulp_next_of_no_carry no_carry, next, trunc, ← Nat.succ_mul,
      Nat.add_div_right _ (ulp_pos n x)]

theorem trunc_next_comm_of_no_carry {n x : ℕ} (npos : 0 < n)
    (no_carry : next n x < 2 ^ Nat.size x) :
    trunc n (next n x) = next n (trunc n x) := by
  rw [trunc_next_of_no_carry no_carry, next, ulp_trunc npos x]

theorem trunc_next_of_carry {n x : ℕ} (npos : 0 < n)
    (carry : 2 ^ Nat.size x ≤ next n x) :
    trunc n (next n x) = 2 ^ Nat.size x := by
  apply div_mul_eq_of_le_of_lt
  . unfold expt
    rewrite [size_next_eq_succ_size_of_carry carry, tsub_le_iff_tsub_le,
      add_tsub_cancel_left]
    exact Nat.one_le_of_lt npos
  . exact carry
  . apply add_lt_add_of_lt_of_le
    . exact Nat.lt_size_self x
    . apply ulp_le_ulp
      exact Nat.le_add_right x (2 ^ expt n x)

theorem next_trunc_of_carry {n x : ℕ} (npos : 0 < n)
    (carry : 2 ^ Nat.size x ≤ next n x) :
    next n (trunc n x) = 2 ^ Nat.size x := by
  unfold next
  rewrite [ulp_trunc npos]
  unfold trunc ulp
  rewrite [← Nat.succ_mul, ← Nat.add_div_right x (Nat.two_pow_pos _)]
  have h₁ : expt n x ≤ Nat.size x := tsub_le_self
  have h₃ : next n x < 2 ^ Nat.size x + 2 ^ expt n x :=
    Nat.add_lt_add_right (Nat.lt_size_self x) _
  exact div_mul_eq_of_le_of_lt h₁ carry h₃

theorem trunc_next_comm {n : ℕ} (npos : 0 < n) (x : ℕ) :
    trunc n (next n x) = next n (trunc n x) := by
  cases Nat.lt_or_ge (next n x) (2 ^ Nat.size x) with
  | inl next_lt => -- next_lt : next n x < 2 ^ Nat.size x
    exact trunc_next_comm_of_no_carry npos next_lt
  | inr next_ge => -- next_ge : next n x ≥ 2 ^ Nat.size x
    rw [next_trunc_of_carry npos next_ge, trunc_next_of_carry npos next_ge]

theorem lt_next_trunc {n : ℕ} (npos : 0 < n) (x : ℕ) :
    x < next n (trunc n x) := by
  unfold next
  rewrite [ulp_trunc npos]
  unfold trunc
  rewrite [← Nat.succ_mul, mul_comm]
  exact Nat.lt_mul_div_succ x (ulp_pos n x)

theorem trunc_next_le {n : ℕ} (npos: 0 < n) (x : ℕ) :
    trunc n (next n x) ≤ 2 ^ Nat.size x := by
  cases Nat.le_total (next n x) (2 ^ Nat.size x) with
  | inl le => exact Nat.le_trans (trunc_le n (next n x)) le
  | inr ge => exact Nat.le_of_eq (trunc_next_of_carry npos ge)

theorem next_trunc_le {n : ℕ} (npos: 0 < n) (x : ℕ) :
    next n (trunc n x) ≤ 2 ^ Nat.size x := by
  rewrite [← trunc_next_comm npos]
  exact trunc_next_le npos x

theorem trunc_eq_trunc_of_le_of_lt {x y n : ℕ} (npos : 0 < n)
    (h : trunc n x ≤ y) (k : y < next n (trunc n x)) :
    trunc n x = trunc n y := by
  have ulp_eq : ulp n x = ulp n y := by
    rewrite [← ulp_trunc npos]
    apply le_antisymm
    . apply ulp_le_ulp
      exact h
    . rewrite [ulp_trunc npos]
      unfold ulp expt
      apply Nat.pow_le_pow_of_le_right two_pos
      apply tsub_le_tsub_right
      rewrite [Nat.size_le]
      apply Nat.lt_of_lt_of_le k
      exact next_trunc_le npos x
  unfold trunc
  rewrite [← ulp_eq]
  apply Eq.symm
  apply congr_arg (fun w => w * ulp n x)
  apply Nat.eq_of_le_of_lt_succ
  . rewrite [← Nat.mul_div_cancel (x / ulp n x) (ulp_pos n x)]
    exact Nat.div_le_div_right h
  . rewrite [Nat.div_lt_iff_lt_mul (ulp_pos n x),
      Nat.mul_comm, Nat.mul_succ, Nat.mul_comm, ← trunc, ← ulp_trunc npos,
      ← next]
    exact k

theorem trunc_pred_eq_trunc_of_trunc_ne_self {n a : ℕ} (npos : 0 < n)
    (h : trunc n a ≠ a) : trunc n (a - 1) = trunc n a := by
  symm
  apply trunc_eq_trunc_of_le_of_lt npos
  . apply Nat.le_pred_of_lt
    exact Nat.lt_of_le_of_ne (trunc_le n a) h
  . exact Nat.lt_of_le_of_lt tsub_le_self (lt_next_trunc npos a)

theorem trunc_add_half_ulp_eq_of_no_uflow
    {n x : ℕ} (npos : 0 < n) (no_uflow : 2 ^ n ≤ x) :
    2 * (trunc n x + ulp n x / 2) = trunc n x + next n (trunc n x) := by
  have ulp_even := two_dvd_ulp_of_no_uflow no_uflow
  rw [Nat.left_distrib, Nat.two_mul, Nat.add_assoc,
    Nat.mul_div_cancel' ulp_even, ← ulp_trunc npos, next]

theorem trunc_le_trunc_of_lt_next_trunc {n x y : ℕ} (npos : 0 < n)
    (h : x < next n (trunc n y)) : trunc n x ≤ trunc n y := by
  cases Nat.le_total x (trunc n y) with
  | inl hxy => exact trunc_le_trunc npos (Nat.le_trans hxy (trunc_le n y))
  | inr hyx => exact ge_of_eq (trunc_eq_trunc_of_le_of_lt npos hyx h)

theorem next_trunc_sub_eq_ulp_sub_mod {n : ℕ} (npos : 0 < n) (c : ℕ) :
    next n (trunc n c) - c = ulp n c - c % ulp n c := by
  unfold next
  rw [ulp_trunc npos, trunc_eq_sub_mod, tsub_add_eq_add_tsub (Nat.mod_le _ _),
    tsub_right_comm, add_tsub_cancel_left]

theorem next_trunc_pred_trunc_eq_self {n x : ℕ} (npos : 0 < n)
    (xpos : 0 < trunc n x) :
    next n (trunc n (trunc n x - 1)) = trunc n x := by
  symm
  rewrite [← trunc_next_comm npos (trunc n x - 1)]
  unfold next
  apply trunc_eq_trunc_of_le_of_lt npos
  . rewrite [← tsub_le_iff_right]
    apply tsub_le_tsub_left
    exact Nat.one_le_of_lt (ulp_pos _ _)
  . apply add_lt_add_of_lt_of_le
    . exact tsub_lt_self xpos zero_lt_one
    . exact ulp_le_ulp n tsub_le_self
