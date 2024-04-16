import Fl.Lemmas
import Fl.Trunc

def faithful₀ (n : ℕ) (round : ℕ → ℕ) :=
  ∀ x : ℕ, trunc n x = x → round x = x

def faithful₁ (n : ℕ) (round : ℕ → ℕ) :=
  ∀ x : ℕ, round x = trunc n x ∨ round x = next n (trunc n x)

def correct₀ (n : ℕ) (round : ℕ → ℕ) :=
  ∀ x : ℕ, round x = trunc n x → x - trunc n x ≤ next n (trunc n x) - x

def correct₁ (n : ℕ) (round : ℕ → ℕ) :=
  ∀ x : ℕ, round x = next n (trunc n x) → next n (trunc n x) - x ≤ x - trunc n x

theorem round_eq_next_trunc_of_gt {n x : ℕ} {round : ℕ → ℕ}
    (hfaithful₁ : faithful₁ n round) (h : x < round x) :
    round x = next n (trunc n x) := by
  cases hfaithful₁ x with
  | inl hlo =>
    exfalso
    apply Nat.lt_le_asymm h
    exact hlo ▸ (trunc_le n x)
  | inr hhi => exact hhi

theorem round_le_next_trunc {n : ℕ} {round : ℕ → ℕ}
    (hfaithful₁ : faithful₁ n round) (x : ℕ) : round x ≤ next n (trunc n x) :=
  Or.elim (hfaithful₁ x) (fun lo => lo.symm ▸ Nat.le_add_right _ _) le_of_eq

theorem trunc_le_round (n x : ℕ) {round : ℕ → ℕ}
    (hfaithful₁ : faithful₁ n round) : trunc n x ≤ round x :=
  Or.elim (hfaithful₁ x) ge_of_eq (fun hi => hi.symm ▸ Nat.le_add_right _ _)

theorem round_trunc {n : ℕ} (npos : 0 < n) (x : ℕ) {round : ℕ → ℕ}
    (hfaithful₀ : faithful₀ n round) : round (trunc n x) = trunc n x :=
  hfaithful₀ (trunc n x) (trunc_idempotent npos x)

theorem trunc_round {n : ℕ} (npos : 0 < n) {round : ℕ → ℕ}
    (hfaithful₁: faithful₁ n round) (x : ℕ) : trunc n (round x) = round x := by
  cases hfaithful₁ x with
  | inl lo => rw [lo, trunc_idempotent npos]
  | inr hi => rw [hi, trunc_next_comm npos, trunc_idempotent npos]

theorem trunc_eq_of_round_eq {n x : ℕ} (npos : 0 < n) {round : ℕ → ℕ}
    (hfaithful₁: faithful₁ n round) (round_eq : round x = x) :
    trunc n x = x := by
  rw [← round_eq, trunc_round npos hfaithful₁ x]

theorem round_eq_of_trunc_eq {n x : ℕ} (npos : 0 < n) {round : ℕ → ℕ}
    (hfaithful₀: faithful₀ n round) (trunc_eq : trunc n x = x) :
    round x = x := by
  rw [← trunc_eq, round_trunc npos x hfaithful₀]

theorem round_eq_trunc_of_le {n x : ℕ} (npos : 0 < n) {round : ℕ → ℕ}
    (hfaithful₁ : faithful₁ n round) (h : round x ≤ x) :
    round x = trunc n x := by
  cases hfaithful₁ x with
  | inl hlo => exact hlo
  | inr hhi =>
    exfalso
    apply Nat.lt_le_asymm (lt_next_trunc npos x)
    exact hhi ▸ h

theorem le_midpoint_of_round_eq_trunc {n x : ℕ} {round : ℕ → ℕ} (npos : 0 < n)
    (hcorrect₀ : correct₀ n round) (hlo : round x = trunc n x) :
    x ≤ trunc n x + ulp n x / 2 := by
  cases Nat.lt_or_ge x (2 ^ n) with
  | inl uflow =>
    exact ge_of_eq (trunc_add_half_ulp_eq_of_uflow uflow)
  | inr no_uflow =>
    refine Nat.le_of_mul_le_mul_left ?_ two_pos
    have h1 : x ≤ next n (trunc n x) := Nat.le_of_lt (lt_next_trunc npos x)
    have h2 : trunc n x ≤ x := trunc_le n x
    rewrite [trunc_add_half_ulp_eq_of_no_uflow npos no_uflow, Nat.two_mul,
      ← tsub_le_iff_left, add_tsub_assoc_of_le h2,
      Nat.add_comm, ← le_tsub_iff_right h1]
    exact hcorrect₀ x hlo

theorem round_eq_trunc_of_lt_midpoint {n x : ℕ} (npos : 0 < n) {round : ℕ → ℕ}
    (hfaithful₀ : faithful₀ n round) (hfaithful₁ : faithful₁ n round)
    (hcorrect₁ : correct₁ n round) (h : x < trunc n x + ulp n x / 2) :
    round x = trunc n x := by
  cases Nat.lt_or_ge n (Nat.size x) with
  | inr uflow =>
    have trunc_eq : trunc n x = x := by
      unfold trunc ulp expt
      rewrite [tsub_eq_zero_of_le uflow]
      rw [Nat.pow_zero, Nat.mul_one, Nat.div_one]
    rw [round_eq_of_trunc_eq npos hfaithful₀ trunc_eq, trunc_eq]
  | inl no_uflow =>
    have expt_pos : 0 < (Nat.size x) - n := lt_tsub_of_add_lt_left no_uflow
    have ulp_even : 2 ∣ ulp n x := dvd_pow_self _ (ne_zero_of_lt expt_pos)
    have h : x - trunc n x < next n (trunc n x) - x := by
      rewrite [tsub_lt_iff_left (trunc_le n x)]
      rewrite [← add_tsub_assoc_of_le (le_of_lt (lt_next_trunc npos x))]
      -- ⊢ x < trunc n x + next (trunc n x) - x
      unfold next
      rewrite [ulp_trunc npos, lt_tsub_iff_left, ← Nat.add_assoc,
        ← Nat.div_mul_cancel ulp_even, ← mul_two, ← mul_two, ← add_mul]
      exact Nat.mul_lt_mul_of_pos_right h two_pos
    cases hfaithful₁ x with
    | inl lo => exact lo
    | inr hi => exfalso ; exact Nat.lt_le_asymm h $ hcorrect₁ x hi

theorem midpoint_le_of_round_eq_next_trunc {n x : ℕ} {round : ℕ → ℕ}
    (npos : 0 < n) (hcorrect₁ : correct₁ n round)
    (hhi : round x = next n (trunc n x)) : trunc n x + ulp n x / 2 ≤ x := by
  cases Nat.lt_or_ge x (2 ^ n) with
  | inl uflow =>
    exact le_of_eq (trunc_add_half_ulp_eq_of_uflow uflow)
  | inr no_uflow =>
    refine Nat.le_of_mul_le_mul_left ?_ two_pos
    have h1 : x ≤ next n (trunc n x) := Nat.le_of_lt (lt_next_trunc npos x)
    have h2 : trunc n x ≤ x := trunc_le n x
    rewrite [trunc_add_half_ulp_eq_of_no_uflow npos no_uflow, Nat.two_mul,
      ← tsub_le_iff_left, add_tsub_assoc_of_le h1, Nat.add_comm,
      ← le_tsub_iff_right h2]
    exact hcorrect₁ x hhi

theorem round_le_trunc_of_le_trunc {n x y : ℕ} {round : ℕ → ℕ} (npos : 0 < n)
    (hfaithful₀ : faithful₀ n round) (hfaithful₁ : faithful₁ n round)
    (h : y ≤ trunc n x) : round y ≤ trunc n x := by
  cases Nat.lt_or_eq_of_le h with
  | inl lt => -- lt : y < trunc x
    have pos := Nat.zero_lt_of_lt lt
    rewrite [← next_trunc_pred_trunc_eq_self npos pos]
    apply Nat.le_trans
    . exact round_le_next_trunc hfaithful₁ y
    . apply next_le_next
      apply trunc_le_trunc npos
      apply Nat.le_pred_of_lt
      exact lt
  | inr eq => -- eq : y = trunc x
    rw [eq, round_trunc npos x hfaithful₀]

theorem round_sub_le {a n : ℕ} {round : ℕ → ℕ} (npos : 0 < n)
    (hfaithful₀ : faithful₀ n round) (hfaithful₁ : faithful₁ n round) (b : ℕ)
    (hfa : trunc n a = a) : round (a - b) ≤ a := by
  trans trunc n a
  . apply round_le_trunc_of_le_trunc npos hfaithful₀ hfaithful₁
    exact Nat.le_trans tsub_le_self hfa.ge
  . exact trunc_le _ _

theorem round_add_le {n a b : ℕ} {round : ℕ → ℕ} (npos : 0 < n)
    (hfaithful₀ : faithful₀ n round) (hfaithful₁ : faithful₁ n round)
    (hfa : trunc n a = a) (hba : b ≤ a) : round (a + b) ≤ 2 * a := by
  rewrite [← add_tsub_tsub_cancel hba, ← two_mul, ← pow_one 2]
  apply round_sub_le npos hfaithful₀ hfaithful₁
  rw [trunc_pow_mul npos, hfa]

-- Correct rounding implies monotonicity
theorem round_le_round {n a b : ℕ} {round : ℕ → ℕ} (npos : 0 < n)
    (hfaithful₁ : faithful₁ n round) (hcorrect₀ : correct₀ n round)
    (hcorrect₁ : correct₁ n round) (hba : b ≤ a) : round b ≤ round a := by
  have lolo : trunc n b ≤ trunc n a := trunc_le_trunc npos hba
  have lohi : trunc n b ≤ next n (trunc n a) :=
    Nat.le_trans lolo (Nat.le_add_right _ _)
  have hihi : next n (trunc n b) ≤ next n (trunc n a) :=
    Nat.add_le_add lolo (ulp_le_ulp n lolo)
  rcases hfaithful₁ b, (hfaithful₁ a).symm with ⟨blo | bhi, ahi | alo⟩
  . rwa [blo, ahi]
  . rwa [blo, alo]
  . rwa [bhi, ahi]
  . cases Decidable.eq_or_ne b a with
    | inl eq => exact eq ▸ le_rfl
    | inr ne =>
      rewrite [bhi, alo]
      apply Nat.le_of_not_lt
      intro (lt_next_trunc : trunc n a < next n (trunc n b))
      have trunc_eq : trunc n a = trunc n b := by
        apply Nat.le_antisymm
        . rewrite [← trunc_idempotent npos a]
          exact trunc_le_trunc_of_lt_next_trunc npos lt_next_trunc
        . exact lolo
      have ulp_eq : ulp n a = ulp n b := by
        rw [← ulp_trunc npos b, ← ulp_trunc npos a, trunc_eq]
      apply Nat.lt_le_asymm (lt_of_le_of_ne hba ne)
      trans trunc n a + ulp n a / 2
      . exact le_midpoint_of_round_eq_trunc npos hcorrect₀ alo
      . rewrite [trunc_eq, ulp_eq]
        exact midpoint_le_of_round_eq_next_trunc npos hcorrect₁ bhi

def sub_right_monotonic (n : ℕ) (round : ℕ → ℕ) :=
  ∀ {a b c : ℕ}, trunc n a = a → trunc n b = b → trunc n c = c →
    a ≤ b → round (a - c) ≤ round (b - c)

def sub_left_monotonic (n : ℕ) (round : ℕ → ℕ) :=
  ∀ {a b c : ℕ}, trunc n a = a → trunc n b = b → trunc n c = c →
    a ≤ b → round (c - b) ≤ round (c - a)

theorem monotonic {n : ℕ} {round : ℕ → ℕ} (npos : 0 < n)
    (hfaithful₁ : faithful₁ n round) (hcorrect₀ : correct₀ n round)
    (hcorrect₁ : correct₁ n round) :
    sub_left_monotonic n round ∧ sub_right_monotonic n round := by
  unfold sub_left_monotonic
  unfold sub_right_monotonic
  constructor
  . intro a b c _ _ _ hab
    apply round_le_round npos hfaithful₁ hcorrect₀ hcorrect₁
    exact tsub_le_tsub_left hab _
  . intro a b c _ _ _ hba
    apply round_le_round npos hfaithful₁ hcorrect₀ hcorrect₁
    exact tsub_le_tsub_right hba _
