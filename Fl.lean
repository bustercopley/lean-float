import Fl.Lemmas
import Fl.Trunc
import Fl.Round

-- On Properties of Floating Point Arithmetics: Numerical Stability
-- and the Cost of Accurate Computations
-- Douglas M. Priest (1992) (Ph. D. Thesis)

-- Given a natural number n (the size in bits of the significand),
-- for all x ∈ ℕ we say x is a "floating point number" if trunc n x = x.

-- In Priest, a "floating point arithmetic" is a mapping which assigns to each
-- triple (a, b, ∘) where a and b are floating point numbers and ∘ is one of
-- the operations + - × / another floating point number fl (a ∘ b), provided
-- b ≠ 0 when ∘ is /.

-- Other authors, e.g., Knuth, use the notation "a ⊕ b" for "fl (a + b)", etc..
-- Note that "fl" does not denote a function.

-- For any real x, denote by ⌈x⌉ the smallest floating point number not greater
-- than x, and by ⌊x⌋ the largest floating point number not smaller than x.

-- The arithmetic is "faithful" if:
-- (i)  Whenever a ∘ b is a floating point number, fl (a ∘ b) = a ∘ b
-- (ii) Otherwise, fl (a ∘ b) is either ⌈a ∘ b⌉ or ⌊a ∘ b⌋

-- The arithmetic is "correctly rounding" if it is faithful and:
-- (i)  fl (a ∘ b) = ⌊a ∘ b⌋ if a ∘ b - ⌊a ∘ b⌋ < ⌈a ∘ b⌉ - a ∘ b
-- (ii) fl (a ∘ b) = ⌈a ∘ b⌉ if a ∘ b - ⌊a ∘ b⌋ > ⌈a ∘ b⌉ - a ∘ b

--   Here, though, the floating point result of subtracting b from a is
--   expressed as "round (a - b)", where "round" is some unspecified function.
--   This is a strictly less general formulation.

--   Also note that our underlying representation of a floating point number
--   is simply a natural number, and that "-" denotes cut subtraction.
--   As a consequence, all floating point numbers considered here are integers;
--   since we are concerned only with addition and subtraction, this is no loss.
--   Furthermore, we often require several versions of each statement, to handle
--   the signs of the arguments and results.

-- Sterbenz' Lemma (Priest, p. 12):
--    If a and b are floating point numbers such that 1 / 2 ≤ a / b ≤ 2
--    then a - b is also a floating point number.
--
-- We prove the statement in the case 0 ≤ b ≤ a ≤ 2 * b. (Then 1 ≤ a / b ≤ 2.)
-- When 0 ≤ a < b ≤ 2 * a, the same argument with a and b exchanged shows that
-- the nonnegative b - a is a floating point number.
theorem sterbenz
  {n a b : ℕ}
  (hfa : trunc n a = a) (hfb : trunc n b = b) (hba : b ≤ a) (hab : a ≤ 2 * b)
: trunc n (a - b) = a - b := by
  rewrite [Nat.two_mul] at hab
  apply trunc_eq_of_le_of_ulp_dvd b
  . exact tsub_le_iff_right.mpr hab
  . apply Nat.dvd_sub'
    . trans ulp n a
      . exact ulp_dvd_ulp n hba
      . exact ulp_dvd_of_trunc_eq hfa
    . exact ulp_dvd_of_trunc_eq hfb

-- Conditions for exact subtraction: properties S1 - S3 (Priest, p. 9)
--
-- If a, b, c are floating point numbers, define
--
-- S₁ : If 0 ≤ a ≤ c ≤ b and round (b - a) = b - a exactly
--      then round (c - a) = c - a  exactly (and similarly if 0 ≥ a ≥ b)
--
-- S₂ : If 0 ≤ a ≤ b and c = round (b - a) then round (b - c) = b - c exactly
--      (and similarly if 0 ≥ a ≥ b)
--
-- S₃ : If 0 ≤ ulp n (b) / 2 ≤ a ≤ b and c = round (b - round (b - a)
--      satisfies c > a then round (c - d) = c - d exactly for all d ∈ [a, c]
--      (and similarly if 0 ≥ -ulp n (b) / 2 ≥ a ≥ b).
--
-- Inductive step of the proof for property S₁.
-- Let a and b be floating point numbers such that 2 * a < b.
-- Suppose that b and b - a are floating point numbers.
-- Let c be a floating point number such that 2 * a < c <= b.
-- Then c - a is a floating point number.
theorem s₁'
  {n a b x : ℕ} (npos : 0 < n)
  (hfb : trunc n b = b)
  (hf : trunc n (b - a) = b - a)
  (h : 2 * a < b - x)
: trunc n (trunc n (b - x) - a) = trunc n (b - x) - a := by
  match x with
  | 0 =>
    rewrite [tsub_zero]
    rewrite [hfb]
    exact hf
  | w + 1 =>
    have h' : 2 * a < b - w := by
      apply Nat.lt_of_lt_of_le h
      apply tsub_le_tsub_left
      exact Nat.le_add_right _ _
    have ih : trunc n (trunc n (b - w) - a) = trunc n (b - w) - a :=
      s₁' npos hfb hf h'
    cases eq_or_ne (trunc n (b - w)) (b - w) with
    | inr ne =>
      rewrite [← tsub_tsub]
      rewrite [trunc_pred_eq_trunc_of_trunc_ne_self npos ne]
      exact ih
    | inl hfb₁ =>
      have bpos : 0 < b - w := Nat.zero_lt_of_lt h'
      rewrite [← tsub_tsub]
      rewrite [trunc_pred_eq_sub_ulp_of_pos_of_trunc_eq bpos hfb₁]
      rewrite [tsub_right_comm]
      rewrite [trunc_eq_iff_ulp_dvd]
      apply Nat.dvd_sub'
      . calc ulp n (b - w - a - ulp n (b - w - 1))
          _ ∣ ulp n (b - w - a) := ulp_dvd_ulp n tsub_le_self
          _ ∣ b - w - a         := ulp_dvd_of_trunc_eq $ hfb₁ ▸ ih
      . apply ulp_dvd_ulp
        calc b - w - a - ulp n (b - w - 1)
          _ ≤ b - w - a - 1 := tsub_le_tsub_left (Nat.one_le_of_lt $ ulp_pos n _) _
          _ ≤ b - w - 1     := tsub_le_tsub_right tsub_le_self _

theorem s₁
  {n a b c : ℕ} (npos : 0 < n)
  (hac : a ≤ c) (hcb : c ≤ b)
  (hfa : trunc n a = a) (hfb : trunc n b = b) (hfc : trunc n c = c)
  (hf : trunc n (b - a) = b - a)
: trunc n (c - a) = c - a := by
  cases le_or_gt c (2 * a) with
  | inl hle => exact sterbenz hfc hfa hac hle
  | inr hgt =>
    rewrite [← hfc]
    rewrite [← tsub_tsub_cancel_of_le hcb]
    apply s₁' npos hfb hf
    rewrite [tsub_tsub_cancel_of_le hcb]
    exact hgt

theorem s₂
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₀ : faithful₀ n round)
  (hfaithful₁ : faithful₁ n round)
  (hfa : trunc n a = a)
  (hfb : trunc n b = b)
  (hba : b ≤ a)
: trunc n (a - round (a - b)) = a - round (a - b) := by
  cases Nat.le_total (2 * b) a with
  | inr hba' => -- hba' : 2 * b ≥ a
    have hf : round (a - b) = a - b := by
      apply hfaithful₀
      exact sterbenz hfa hfb hba hba'
    rewrite [hf, tsub_tsub_cancel_of_le hba]
    exact hfb
  | inl hab' => -- hab' : 2 * b < a
    apply sterbenz
    . exact hfa
    . exact trunc_round npos hfaithful₁ (a - b)
    . exact round_sub_le npos hfaithful₀ hfaithful₁ b hfa
    . have h : a ≤ 2 * (a - b) := by
        rewrite [Nat.mul_sub_left_distrib]
        rewrite [Nat.two_mul]
        rewrite [add_tsub_assoc_of_le hab']
        exact Nat.le_add_right _ _
      calc
        a = trunc n a             := by rw [hfa]
        _ ≤ trunc n (2 * (a - b)) := trunc_le_trunc npos h
        _ = 2 * trunc n (a - b)   := by rw [← pow_one 2, ← trunc_pow_mul npos, pow_one]
        _ ≤ 2 * round (a - b)     := Nat.mul_le_mul_left _ (trunc_le_round n _ hfaithful₁)

-- Inner part of the proof for property S₃.
-- Let b be a floating point number such that 0 ≤ a ≤ b and ulp n b ≤ 2 * a.
-- Let b' be the greatest floating point number not greater than b - a.
-- Then b - b' ≤ 2 * a.
theorem s₃'
  {n a b : ℕ} (npos : 0 < n)
  (hfb : trunc n b = b) (h : ulp n b ≤ 2 * a)
: b - trunc n (b - a) ≤ 2 * a := by
  cases Nat.le_total a (ulp n b) with
  | inl le_ulp => -- a ≤ ulp n b
    trans ulp n b
    . rewrite [tsub_le_iff_tsub_le]
      calc
        b - ulp n b
        _ = trunc n (b - ulp n b) := Eq.symm $ trunc_sub_ulp_eq_of_trunc_eq npos hfb
        _ ≤ trunc n (b - a)       := trunc_le_trunc npos $ tsub_le_tsub_left le_ulp _
    . exact h
  | inr ulp_le => -- ulp n b ≤ a
    rewrite [Nat.two_mul, ← tsub_le_iff_right, tsub_right_comm, tsub_le_iff_left]
    calc
      b - a ≤ next n (trunc n (b - a))    := Nat.le_of_lt $ lt_next_trunc npos _
      _ = trunc n (b - a) + ulp n (b - a) := by unfold next ; rw [ulp_trunc npos _]
      _ ≤ trunc n (b - a) + ulp n b       := Nat.add_le_add_left (ulp_le_ulp n tsub_le_self) _
      _ ≤ trunc n (b - a) + a             := Nat.add_le_add_left ulp_le _

theorem s₃
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₀ : faithful₀ n round)
  (hfaithful₁ : faithful₁ n round)
  (hfa : trunc n a = a)
  (hfb : trunc n b = b)
  (hfd : trunc n d = d)
  (hba : b ≤ a)
  (hbd : b ≤ d)
  (hab : ulp n a ≤ 2 * b)
  (hbc : b < round (a - round (a - b)))
  (hdc : d ≤ round (a - round (a - b)))
: trunc n (round (a - round (a - b)) - d) = round (a - round (a - b)) - d := by
  have hfc : round (a - round (a - b)) = a - round (a - b) := by
    apply round_eq_of_trunc_eq npos hfaithful₀
    exact s₂ npos hfaithful₀ hfaithful₁ hfa hfb hba
  have helo : round (a - b) = trunc n (a - b) := by
    apply round_eq_trunc_of_le npos hfaithful₁
    apply Nat.le_of_lt
    rewrite [lt_tsub_comm, ← hfc]
    exact hbc
  have hcd : round (a - round (a - b)) ≤ 2 * d := by
    trans 2 * b
    . rewrite [hfc, helo]
      exact s₃' npos hfa hab
    . exact Nat.mul_le_mul_left 2 hbd
  have hfe : trunc n (round (a - round (a - b))) = round (a - round (a - b)) :=
    trunc_round npos hfaithful₁ (a - round (a - b))
  exact sterbenz hfe hfd hdc hcd

theorem interval_shift₁
  {round : ℕ → ℕ} {x y z w s t n : ℕ} (npos : 0 < n)
  (hfaithful₀ : faithful₀ n round)
  (hfaithful₁ : faithful₁ n round)
  (hml : sub_left_monotonic n round)
  (hfx : trunc n x = x) (hfy : trunc n y = y)
  (hfz : trunc n z = z) (hfw : trunc n w = w)
  (hzx : z ≤ x) (hzy : z ≤ y) (hyxulp : ulp n y ≤ 2 * x)
  (ht : t = round (y - round (y - z)))
  (hs₁ : x < t → s = round (x + round (t - x)))
  (hs₂ : t ≤ x → s = round (x - round (x - t)))
  (hxw : x ≤ w) (hwy : w ≤ y) :
  trunc n (w - s) = w - s ∧ trunc n (s - w) = s - w := by
  have hxy : x ≤ y := Nat.le_trans hxw hwy
  have ht' : t = y - round (y - z) := by
    rewrite [ht]
    apply round_eq_of_trunc_eq npos hfaithful₀
    exact s₂ npos hfaithful₀ hfaithful₁ hfy hfz hzy
  have htx' : t ≤ y - round (y - x) := calc
    t = y - round (y - z) := ht'
    _ ≤ y - round (y - x) := tsub_le_tsub_left (hml hfz hfx hfy hzx) _
  have hzy' : round (y - z) ≤ y := by
    trans round (y - 0)
    . exact hml (trunc_zero n) hfz hfy (Nat.zero_le _)
    . rw [tsub_zero, round_eq_of_trunc_eq npos hfaithful₀ hfy]
  have hft : trunc n t = t := ht ▸ trunc_round npos hfaithful₁ _
  have hfx' : round (y - round (y - x)) = y - round (y - x) := by
    apply round_eq_of_trunc_eq npos hfaithful₀
    exact s₂ npos hfaithful₀ hfaithful₁ hfy hfx hxy
  have hfut {u : ℕ} (hxu : x ≤ u) (hut : u < t) (hfu : trunc n u = u)
    (hux' : u ≤ round (y - round (y - x)))
  : trunc n (t - u) = t - u := by
    have hfuxy : trunc n (y - round (y - x) - u) = y - round (y - x) - u := by
      have hxyx : x < round (y - round (y - x)) := calc
        x ≤ u                         := hxu
        _ < t                         := hut
        _ ≤ y - round (y - x)         := htx'
        _ = round (y - round (y - x)) := hfx'.symm
      rewrite [← hfx']
      exact s₃ npos hfaithful₀ hfaithful₁ hfy hfx hfu hxy hxu hyxulp hxyx hux'
    rewrite [ht] at hut htx' ⊢
    replace hfx' := trunc_eq_of_round_eq npos hfaithful₁ hfx'
    exact s₁ npos hut.le htx' hfu hfx' (trunc_round npos hfaithful₁ _) hfuxy
  have hfty : trunc n (y - t) = y - t := by
    rw [ht', tsub_tsub_cancel_of_le hzy', trunc_round npos hfaithful₁]
  have hst : s = t := by
    rewrite [← round_eq_of_trunc_eq npos hfaithful₀ hft]
    cases Nat.lt_or_ge x t with
    | inl hxt => -- hxt : x < t
      have hfxt : round (t - x) = t - x := by
        apply round_eq_of_trunc_eq npos hfaithful₀
        apply hfut le_rfl hxt hfx
        rewrite [hfx']
        exact Nat.le_trans hxt.le htx'
      rw [hs₁ hxt, hfxt, add_tsub_cancel_of_le hxt.le]
    | inr htx => -- htx : x ≥ t
      have hftx : round (x - t) = x - t := by
        apply round_eq_of_trunc_eq npos hfaithful₀
        rewrite [ht] at htx hfty ⊢
        exact s₁ npos htx hxy (trunc_round npos hfaithful₁ _) hfy hfx hfty
      rw [hs₂ htx, hftx, tsub_tsub_cancel_of_le htx]
  rewrite [hst]
  cases Nat.lt_or_ge w t with
  | inl hwt => -- hwt : w < t
    constructor
    . rw [tsub_eq_zero_of_le hwt.le, trunc_zero]
    . apply hfut hxw hwt hfw
      rewrite [hfx']
      trans t
      . exact hwt.le
      . exact htx'
  | inr htw => -- htw : w ≥ t
    constructor
    . exact s₁ npos htw hwy hft hfy hfw hfty
    . rw [tsub_eq_zero_of_le htw, trunc_zero]

theorem interval_shift₂
  {round : ℕ → ℕ} {x y z w s t n : ℕ} (npos : 0 < n)
  (hfaithful₀ : faithful₀ n round)
  (hfaithful₁ : faithful₁ n round)
  (hml : sub_left_monotonic n round)
  (hfx : trunc n x = x) (hfy : trunc n y = y)
  (hfw : trunc n w = w)
  (hxyulp : ulp n x ≤ 2 * y)
  (ht : t = round (y - round (y - z)))
  (hs₂ : t ≤ x → s = round (x - round (x - t)))
  (hyw : y ≤ w) (hwx : w ≤ x) :
  trunc n (w - s) = w - s ∧ trunc n (s - w) = s - w := by
  have hty : t ≤ y := ht ▸ round_sub_le npos hfaithful₀ hfaithful₁ _ hfy
  have hyx : y ≤ x := Nat.le_trans hyw hwx
  have htx : t ≤ x := Nat.le_trans hty hyx
  have hs : s = round (x - round (x - t)) := hs₂ htx
  have hfs : trunc n s = s := hs.symm ▸ trunc_round npos hfaithful₁ _
  have hft : trunc n t = t := ht.symm ▸ trunc_round npos hfaithful₁ _
  have hsy' : s ≤ round (x - round (x - y)) := by
    have hfy' : round (x - round (x - y)) = x - round (x - y) := by
      apply round_eq_of_trunc_eq npos hfaithful₀
      exact s₂ npos hfaithful₀ hfaithful₁ hfx hfy hyx
    have hft' : round (x - round (x - t)) = x - round (x - t) := by
      apply round_eq_of_trunc_eq npos hfaithful₀
      exact s₂ npos hfaithful₀ hfaithful₁ hfx hft htx
    rewrite [hs, hft', hfy']
    apply tsub_le_tsub_left
    exact hml hft hfy hfx hty
  obtain hsw | ⟨hws, hys⟩ : s ≤ w ∨ (w ≤ s ∧ y < s) := by
    cases Nat.le_total s w with
    | inl hsw => exact Or.inl hsw
    | inr hws =>
      cases Nat.lt_or_ge y s with
      | inl hys => exact Or.inr ⟨hws, hys⟩
      | inr hsy => exact Or.inl (Nat.le_trans hsy hyw)
  . constructor
    . have hfr : trunc n (round (x - t)) = round (x - t) := trunc_round npos hfaithful₁ (x - t)
      have hrx : round (x - t) ≤ x := round_sub_le npos hfaithful₀ hfaithful₁ t hfx
      apply s₁ npos hsw hwx hfs hfx hfw
      rewrite [hs]
      exact s₂ npos hfaithful₀ hfaithful₁ hfx hfr hrx
    . rw [tsub_eq_zero_of_le hsw, trunc_zero]
  . constructor
    . rw [tsub_eq_zero_of_le hws, trunc_zero]
    . have hyy' : y < round (x - round (x - y)) := Nat.lt_of_lt_of_le hys hsy'
      have hwy' : w ≤ round (x - round (x - y)) := Nat.le_trans hws hsy'
      apply s₁ npos hws hsy' hfw (trunc_round npos hfaithful₁ _) hfs
      exact s₃ npos hfaithful₀ hfaithful₁ hfx hfy hfw hyx hyw hxyulp hyy' hwy'

theorem interval_shift
  {round : ℕ → ℕ} {x y z w s t : ℕ} (npos : 0 < n)
  (hfaithful₀ : faithful₀ n round)
  (hfaithful₁ : faithful₁ n round)
  (hml : sub_left_monotonic n round)
  (hfx : trunc n x = x) (hfy : trunc n y = y)
  (hfz : trunc n z = z) (hfw : trunc n w = w)
  (hzx : z ≤ x) (hzy : z ≤ y) (hyx : ulp n y ≤ 2 * x) (hxy : ulp n x ≤ 2 * y)
  (ht : t = round (y - round (y - z)))
  (hs₁ : x < t → s = round (x + round (t - x)))
  (hs₂ : t ≤ x → s = round (x - round (x - t)))
  (hxwy : (x ≤ w ∧ w ≤ y) ∨ (y ≤ w ∧ w ≤ x)) :
  trunc n (w - s) = w - s ∧ trunc n (s - w) = s - w := by
  rcases hxwy with ⟨hxw, hwy⟩ | ⟨hyw, hwx⟩
  . exact interval_shift₁ npos hfaithful₀ hfaithful₁ hml hfx hfy hfz hfw hzx hzy hyx ht hs₁ hs₂ hxw hwy
  . exact interval_shift₂ npos hfaithful₀ hfaithful₁ hml hfx hfy hfw hxy ht hs₂ hyw hwx

-- Still weaker version using the correct rounding axioms
theorem interval_shift'
  {round : ℕ → ℕ} {x y z w s t : ℕ} (npos : 0 < n)
  (hfaithful₀ : faithful₀ n round)
  (hfaithful₁ : faithful₁ n round)
  (hcorrect₀ : correct₀ n round)
  (hcorrect₁ : correct₁ n round)
  (hfx : trunc n x = x) (hfy : trunc n y = y)
  (hfz : trunc n z = z) (hfw : trunc n w = w)
  (hzx : z ≤ x) (hzy : z ≤ y) (hyx : ulp n y ≤ 2 * x) (hxy : ulp n x ≤ 2 * y)
  (ht : t = round (y - round (y - z)))
  (hs₁ : x < t → s = round (x + round (t - x)))
  (hs₂ : t ≤ x → s = round (x - round (x - t)))
  (hxwy : (x ≤ w ∧ w ≤ y) ∨ (y ≤ w ∧ w ≤ x)) :
  trunc n (w - s) = w - s ∧ trunc n (s - w) = s - w := by
  have hml : sub_left_monotonic n round := (monotonic npos hfaithful₁ hcorrect₀ hcorrect₁).left
  exact interval_shift npos hfaithful₀ hfaithful₁ hml hfx hfy hfz hfw hzx hzy hyx hxy ht hs₁ hs₂ hxwy

-- Sum and error
--
-- Theorem a₁, far below, states that if a and b are floating point numbers
-- and 0 ≤ a and 0 ≤ b, then a + b - fl (a + b) is also a floating point number.
theorem a₁_of_uflow
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₀: faithful₀ n round) (uflow : a + b < 2 ^ n)
: trunc n (a + b - round (a + b)) = a + b - round (a + b) ∧
  trunc n (round (a + b) - (a + b)) = round (a + b) - (a + b) := by
  have k : trunc n (a + b) = a + b := trunc_eq_self_of_uflow uflow
  have l : round (a + b) = a + b := round_eq_of_trunc_eq npos hfaithful₀ k
  rewrite [l, tsub_self]
  exact ⟨trunc_zero n, trunc_zero n⟩

theorem a₁_lo_of_lt_round
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₁ : faithful₁ n round) (lt_round : a + b < round (a + b))
: trunc n (a + b - round (a + b)) = a + b - round (a + b) := by
  rewrite [round_eq_next_trunc_of_gt hfaithful₁ lt_round]
  rewrite [tsub_eq_zero_of_le (Nat.le_of_lt (lt_next_trunc npos _))]
  exact trunc_zero n

theorem a₁_hi_of_round_le
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₁ : faithful₁ n round) (round_le : round (a + b) ≤ a + b)
: trunc n (round (a + b) - (a + b)) = round (a + b) - (a + b) := by
  rewrite [round_eq_trunc_of_le npos hfaithful₁ round_le,
      tsub_eq_zero_of_le (trunc_le n (a + b))]
  exact trunc_zero n

theorem a₁_hi_of_lt_round_of_ulp_sub_le
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₁ : faithful₁ n round)
  (hfa : trunc n a = a) (hfb : trunc n b = b) (hba : b ≤ a)
  (lt_round : a + b < round (a + b))
  (ulp_sub_le : ulp n (a + b) - (a + b) % ulp n (a + b) ≤ b)
: trunc n (round (a + b) - (a + b)) = round (a + b) - (a + b) := by
  rewrite [round_eq_next_trunc_of_gt hfaithful₁ lt_round]
  apply trunc_eq_of_le_of_ulp_dvd b
  . rewrite [next_trunc_sub_eq_ulp_sub_mod npos]
    exact ulp_sub_le
  . apply Nat.dvd_sub'
    . rewrite [next, ulp_trunc npos]
      apply Nat.dvd_add
      . trans ulp n (a + b)
        . exact ulp_dvd_ulp n (Nat.le_add_left _ _)
        . exact ulp_dvd_trunc n _
      . exact ulp_dvd_ulp n (Nat.le_add_left _ _)
    . apply Nat.dvd_add
      . trans ulp n a
        . exact ulp_dvd_ulp n hba
        . exact ulp_dvd_of_trunc_eq hfa
      . exact ulp_dvd_of_trunc_eq hfb

theorem ulp_sub_le_of_no_uflow_of_no_carry_of_lt_round
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₁ : faithful₁ n round)
  (hcorrect₁ : correct₁ n round)
  (hfa : trunc n a = a)
  (no_uflow : 2 ^ n ≤ a + b) (no_carry : a + b < 2 ^ Nat.size a)
  (lt_round : a + b < round (a + b))
: ulp n (a + b) - (a + b) % ulp n (a + b) ≤ b := by
  have size_eq : Nat.size (a + b) = Nat.size a := by
    apply Nat.le_antisymm
    . exact Nat.size_le.mpr no_carry
    . exact Nat.size_le_size (Nat.le_add_right _ _)
  have ulp_eq : ulp n (a + b) = ulp n a := by
    unfold ulp expt
    rw [size_eq]
  have ulp_le : ulp n a ≤ 2 * b := by
    have ⟨d, hd⟩ := two_dvd_ulp_of_no_uflow no_uflow
    rewrite [← ulp_eq, hd]
    apply Nat.mul_le_mul_left
    apply Nat.le_of_add_le_add_left (a := a)
    trans trunc n (a + b) + ulp n (a + b) / 2
    . rewrite [hd, Nat.mul_div_cancel_left _ two_pos]
      apply Nat.add_le_add_right
      trans trunc n a
      . exact hfa.ge
      . apply trunc_le_trunc npos
        exact Nat.le_add_right _ _
    . apply midpoint_le_of_round_eq_next_trunc npos hcorrect₁
      exact round_eq_next_trunc_of_gt hfaithful₁ lt_round
  rewrite [ulp_eq, ← Nat.mod_add_mod,
      Nat.mod_eq_zero_of_dvd (ulp_dvd_of_trunc_eq hfa), Nat.zero_add]
  cases Nat.lt_or_ge b (ulp n a) with
  | inl lt_ulp' =>
    rewrite [tsub_le_iff_right, Nat.mod_eq_of_lt lt_ulp', ← Nat.two_mul]
    exact ulp_le
  | inr ulp_le' => exact Nat.le_trans tsub_le_self ulp_le'

theorem a₁_hi_of_no_uflow_of_no_carry_of_lt_round {n a b : ℕ}
  (npos : 0 < n)
  {round : ℕ → ℕ}
  (hfaithful₁ : faithful₁ n round)
  (hcorrect₁ : correct₁ n round)
  (hfa : trunc n a = a) (hfb : trunc n b = b) (hba : b ≤ a)
  (no_uflow : 2 ^ n ≤ a + b) (no_carry : a + b < 2 ^ Nat.size a)
  (lt_round : a + b < round (a + b))
: trunc n (round (a + b) - (a + b)) = round (a + b) - (a + b) := by
  apply a₁_hi_of_lt_round_of_ulp_sub_le npos hfaithful₁ hfa hfb hba lt_round
  exact ulp_sub_le_of_no_uflow_of_no_carry_of_lt_round npos hfaithful₁ hcorrect₁
    hfa no_uflow no_carry lt_round

theorem a₁_hi_of_ulp_le_of_lt_round
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₁ : faithful₁ n round)
  (hfa : trunc n a = a) (hfb : trunc n b = b) (hba : b ≤ a)
  (ulp_le : ulp n (a + b) ≤ b) (lt_round : a + b < round (a + b))
: trunc n (round (a + b) - (a + b)) = round (a + b) - (a + b) := by
  apply a₁_hi_of_lt_round_of_ulp_sub_le npos hfaithful₁ hfa hfb hba lt_round
  exact Nat.le_trans tsub_le_self ulp_le

theorem a₁_lo_of_no_carry_of_round_le
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₁ : faithful₁ n round)
  (hfa : trunc n a = a) (hfb : trunc n b = b) (hba : b ≤ a)
  (no_carry : a + b < 2 ^ Nat.size a)
  (round_le : round (a + b) ≤ a + b)
: trunc n (a + b - round (a + b)) = a + b - round (a + b) := by
  have size_eq : Nat.size (a + b) = Nat.size a := by
    apply Nat.le_antisymm
    . exact Nat.size_le.mpr no_carry
    . exact Nat.size_le_size (Nat.le_add_right _ _)
  have ulp_eq : ulp n (a + b) = ulp n a := by
    unfold ulp expt
    rw [size_eq]
  have mod_ulp₁ : a % ulp n a = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    exact ulp_dvd_of_trunc_eq hfa
  have mod_ulp₂ : (a + b) % ulp n a = b % ulp n a := by
    rw [Nat.add_mod, mod_ulp₁, Nat.zero_add, Nat.mod_mod]
  have error_eq : a + b - trunc n (a + b) = b % ulp n a := by
    rewrite [tsub_eq_iff_eq_add_of_le (trunc_le _ _), Nat.add_comm (b % ulp n a)]
    rewrite [← mod_ulp₂, ← ulp_eq]
    unfold trunc
    rw [Nat.div_add_mod']
  rewrite [round_eq_trunc_of_le npos hfaithful₁ round_le, error_eq]
  apply trunc_eq_of_le_of_ulp_dvd b
  . exact Nat.mod_le _ _
  . rewrite [Nat.dvd_mod_iff (ulp_dvd_ulp n hba)]
    exact ulp_dvd_of_trunc_eq hfb

theorem a₁_lo_of_no_uflow_of_carry_of_round_le
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₁ : faithful₁ n round)
  (hfa : trunc n a = a) (hfb : trunc n b = b) (hba : b ≤ a)
  (no_uflow : 2 ^ n ≤ a + b) (carry : 2 ^ Nat.size a ≤ a + b)
  (round_le : round (a + b) ≤ a + b)
: trunc n (a + b - round (a + b)) = a + b - round (a + b) := by
  have ulp_add_eq_two_mul_ulp : ulp n (a + b) = 2 * ulp n a :=
    (le_size_and_ulp_eq_of_no_uflow_of_carry hba no_uflow carry).right
  have ulp_le : ulp n a ≤ b := by
    apply Nat.le_of_add_le_add_left (a := a)
    have ulp_le_pow : ulp n a ≤ 2 ^ Nat.size a := by
      unfold ulp expt
      exact Nat.pow_le_pow_of_le_right two_pos tsub_le_self
    trans 2 ^ Nat.size a
    . apply add_le_of_le_tsub_right_of_le ulp_le_pow
      exact le_size_sub_ulp_of_trunc_eq npos hfa
    . exact carry
  have h₀ : b % ulp n a = (a + b) % ulp n a := by
    rewrite [← Nat.mod_add_mod]
    rewrite [Nat.mod_eq_zero_of_dvd (ulp_dvd_of_trunc_eq hfa)]
    rw [Nat.zero_add]
  have h₁ : ulp n a ∣ ulp n (a + b) := ulp_dvd_ulp n $ Nat.le_add_right _ _
  have h₂ : a + b - trunc n (a + b) =
              (a + b) / ulp n a * ulp n a % ulp n (a + b) + b % ulp n a := by
    unfold trunc
    rewrite [h₀]
    rewrite [mod_eq_sub_div_mul]
    rewrite [tsub_add_eq_add_tsub (Nat.div_mul_le_self _ _)]
    rewrite [div_mul_div_cancel_of_dvd h₁]
    rw [Nat.div_add_mod' _ _]
  have h₃ : (a + b) / ulp n a * ulp n a % ulp n (a + b) ≤
              b / ulp n a * ulp n a := by
    trans ulp n (a + b) - ulp n a
    . apply le_sub_of_dvd_of_dvd_of_lt
      . rewrite [Nat.dvd_mod_iff h₁]
        exact Nat.dvd_mul_left _ _
      . exact h₁
      . exact Nat.mod_lt _ (ulp_pos n _)
    . rewrite [ulp_add_eq_two_mul_ulp]
      rewrite [← Nat.mul_pred_left]
      rewrite [← one_add_one_eq_two, Nat.add_one, Nat.pred_succ]
      apply Nat.mul_le_mul_right
      rewrite [Nat.one_le_div_iff (ulp_pos n _)]
      exact ulp_le
  rewrite [round_eq_trunc_of_le npos hfaithful₁ round_le]
  rewrite [h₂]
  apply trunc_eq_of_le_of_ulp_dvd b
  . conv => rhs; rewrite [← Nat.div_add_mod' b (ulp n a)]
    exact Nat.add_le_add_right h₃ (b % ulp n a)
  . apply Nat.dvd_add
    . trans ulp n a
      . exact ulp_dvd_ulp n hba
      . rewrite [Nat.dvd_mod_iff h₁]
        exact Nat.dvd_mul_left _ _
    . rewrite [Nat.dvd_mod_iff (ulp_dvd_ulp n hba)]
      exact ulp_dvd_of_trunc_eq hfb

theorem round_le_of_no_uflow_of_carry_of_lt_ulp
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₀ : faithful₀ n round)
  (hfaithful₁ : faithful₁ n round)
  (hcorrect₁ : correct₁ n round)
  (hfa : trunc n a = a)
  (hba : b ≤ a)
  (no_uflow : 2 ^ n ≤ a + b)
  (carry : 2 ^ Nat.size a ≤ a + b)
  (lt_ulp : b < ulp n (a + b))
: round (a + b) ≤ a + b := by
  have ⟨le_size, ulp_eq⟩ :=
    le_size_and_ulp_eq_of_no_uflow_of_carry hba no_uflow carry
  have add_lt_pow_add_ulp : a + b < 2 ^ Nat.size a + ulp n a := by
    have ulp_le : ulp n a ≤ 2 ^ Nat.size a := by
      unfold ulp expt
      exact Nat.pow_le_pow_of_le_right two_pos tsub_le_self
    rewrite [← tsub_add_cancel_of_le ulp_le]
    rewrite [Nat.add_assoc]
    rewrite [← Nat.two_mul]
    rewrite [← ulp_eq]
    apply add_lt_add_of_le_of_lt
    . exact le_size_sub_ulp_of_trunc_eq npos hfa
    . exact lt_ulp
  have eq_pow : trunc n (a + b) = 2 ^ Nat.size a := by
    have pow_size_eq_pow_mul_ulp : 2 ^ Nat.size a = 2 ^ n * ulp n a := by
      unfold ulp expt
      rewrite [← pow_add]
      rw [add_tsub_cancel_of_le le_size]
    have div_ulp_eq_pow : (a + b) / ulp n a = 2 ^ n := by
      apply Nat.eq_of_mul_eq_mul_right (ulp_pos n a)
      apply div_mul_eq_of_dvd_of_le_of_lt
      . exact Nat.dvd_mul_left _ _
      . exact pow_size_eq_pow_mul_ulp.ge.trans carry
      . apply Nat.lt_of_lt_of_le add_lt_pow_add_ulp
        rw [pow_size_eq_pow_mul_ulp]
    unfold trunc
    rewrite [ulp_eq]
    rewrite [← Nat.mul_assoc]
    rewrite [Nat.mul_comm 2]
    rewrite [← Nat.div_div_eq_div_mul]
    rewrite [div_ulp_eq_pow]
    rewrite [Nat.div_mul_cancel $ dvd_pow_self _ (Nat.not_eq_zero_of_lt npos)]
    exact pow_size_eq_pow_mul_ulp.symm
  have lt_midpoint : a + b < trunc n (a + b) + ulp n (a + b) / 2 := by
    rewrite [eq_pow]
    apply Nat.lt_of_lt_of_le add_lt_pow_add_ulp
    apply Nat.add_le_add_left
    rewrite [ulp_eq]
    rw [Nat.mul_div_cancel_left _ two_pos]
  rewrite [round_eq_trunc_of_lt_midpoint npos hfaithful₀ hfaithful₁ hcorrect₁ lt_midpoint]
  exact trunc_le _ _

theorem a₁'
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₀ : faithful₀ n round)
  (hfaithful₁ : faithful₁ n round)
  (hcorrect₁ : correct₁ n round)
  (hfa : trunc n a = a) (hfb : trunc n b = b) (hba : b ≤ a)
: trunc n (a + b - round (a + b)) = a + b - round (a + b) ∧
  trunc n (round (a + b) - (a + b)) = round (a + b) - (a + b) := by
  cases Nat.lt_or_ge (a + b) (2 ^ n) with
  | inl uflow => exact a₁_of_uflow npos hfaithful₀ uflow
  | inr no_uflow =>
    cases Nat.lt_or_ge (a + b) (round (a + b)) with
    | inl lt_round =>
      constructor
      . exact a₁_lo_of_lt_round npos hfaithful₁ lt_round
      . cases Nat.lt_or_ge (a + b) (2 ^ Nat.size a) with
        | inl no_carry =>
          exact a₁_hi_of_no_uflow_of_no_carry_of_lt_round
            npos hfaithful₁ hcorrect₁ hfa hfb hba no_uflow no_carry lt_round
        | inr carry =>
          have ulp_le : ulp n (a + b) ≤ b := by
            rewrite [← Nat.not_lt]
            intro lt_ulp
            apply Nat.lt_le_antisymm lt_round
            exact round_le_of_no_uflow_of_carry_of_lt_ulp
              npos hfaithful₀ hfaithful₁ hcorrect₁ hfa hba no_uflow carry lt_ulp
          exact a₁_hi_of_ulp_le_of_lt_round npos hfaithful₁ hfa hfb hba ulp_le lt_round
    | inr round_le =>
      constructor
      . cases Nat.lt_or_ge (a + b) (2 ^ Nat.size a) with
        | inl no_carry =>
          exact a₁_lo_of_no_carry_of_round_le
            npos hfaithful₁ hfa hfb hba no_carry round_le
        | inr carry =>
          exact a₁_lo_of_no_uflow_of_carry_of_round_le
            npos hfaithful₁ hfa hfb hba no_uflow carry round_le
      . exact a₁_hi_of_round_le npos hfaithful₁ round_le

-- Property A₁: The roundoff error of a floating point sum is itself a floating
-- point number.
theorem a₁
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₀ : faithful₀ n round)
  (hfaithful₁ : faithful₁ n round)
  (hcorrect₁ : correct₁ n round)
  (hfa : trunc n a = a) (hfb : trunc n b = b)
: trunc n (a + b - round (a + b)) = a + b - round (a + b) ∧
  trunc n (round (a + b) - (a + b)) = round (a + b) - (a + b) := by
  cases Nat.le_total a b with
  | inl hab =>
    rewrite [Nat.add_comm]
    exact a₁' npos hfaithful₀ hfaithful₁ hcorrect₁ hfb hfa hab
  | inr hba => exact a₁' npos hfaithful₀ hfaithful₁ hcorrect₁ hfa hfb hba

theorem sum_and_error₁_lo
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₀ : faithful₀ n round)
  (hfaithful₁ : faithful₁ n round)
  (hcorrect₁ : correct₁ n round)
  (hfa : trunc n a = a) (hfb : trunc n b = b) (hba : b ≤ a)
  (lo : round (a + b) ≤ a + b)
: round (a + b) + round (b - round (round (a + b) - a)) = a + b := by
  have hac : a ≤ round (a + b) := calc
    a = trunc n a       := hfa.symm
    _ ≤ trunc n (a + b) := trunc_le_trunc npos (Nat.le_add_right _ _)
    _ ≤ round (a + b)   := trunc_le_round _ _ hfaithful₁
  have hca : round (a + b) ≤ 2 * a := round_add_le npos hfaithful₀ hfaithful₁ hfa hba
  have hfc : trunc n (round (a + b)) = round (a + b) := trunc_round npos hfaithful₁ _
  have hfe : round (round (a + b) - a) = round (a + b) - a := by
    apply round_eq_of_trunc_eq npos hfaithful₀
    exact sterbenz hfc hfa hac hca
  have ⟨hfr₁, _⟩ := a₁ npos hfaithful₀ hfaithful₁ hcorrect₁ hfa hfb
  rewrite [hfe]
  rewrite [← add_tsub_assoc' lo hac]
  rewrite [Nat.add_comm b a]
  rewrite [round_eq_of_trunc_eq npos hfaithful₀ hfr₁]
  exact add_tsub_cancel_of_le lo

theorem sum_and_error₁_hi
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₀ : faithful₀ n round)
  (hfaithful₁ : faithful₁ n round)
  (hcorrect₁ : correct₁ n round)
  (hfa : trunc n a = a) (hfb : trunc n b = b) (hba : b ≤ a)
  (hi : a + b ≤ round (a + b))
: round (a + b) - round (round (round (a + b) - a) - b) = a + b := by
  have hac : a ≤ round (a + b) := Nat.le_trans (Nat.le_add_right _ _) hi
  have hca : round (a + b) ≤ 2 * a := round_add_le npos hfaithful₀ hfaithful₁ hfa hba
  have hfc : trunc n (round (a + b)) = round (a + b) := trunc_round npos hfaithful₁ _
  have hfe : round (round (a + b) - a) = round (a + b) - a := by
    apply round_eq_of_trunc_eq npos hfaithful₀
    exact sterbenz hfc hfa hac hca
  have ⟨_, hfr₂⟩ := a₁ npos hfaithful₀ hfaithful₁ hcorrect₁ hfa hfb
  rewrite [hfe]
  rewrite [tsub_tsub]
  rewrite [round_eq_of_trunc_eq npos hfaithful₀ hfr₂]
  exact tsub_tsub_cancel_of_le hi

theorem b₁_of_round_eq
  {round : ℕ → ℕ} {n a b : ℕ}
  (round_eq : round (a - b) = a - b)
: trunc n (a - b - round (a - b)) = a - b - round (a - b) ∧
  trunc n (round (a - b) - (a - b)) = round (a - b) - (a - b) := by
  rewrite [round_eq, tsub_self, trunc_zero]
  exact ⟨rfl, rfl⟩

theorem b₁_lo_of_lt_round
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₁ : faithful₁ n round) (lt_round : a - b < round (a - b))
: trunc n (a - b - round (a - b)) = a - b - round (a - b) := by
  rewrite [round_eq_next_trunc_of_gt hfaithful₁ lt_round]
  rewrite [tsub_eq_zero_of_le $ Nat.le_of_lt $ lt_next_trunc npos _]
  exact trunc_zero n

theorem b₁_hi_of_round_le
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₁ : faithful₁ n round)
  (round_le : round (a - b) ≤ a - b)
: trunc n (round (a - b) - (a - b)) = round (a - b) - (a - b) := by
  rewrite [round_eq_trunc_of_le npos hfaithful₁ round_le]
  rewrite [tsub_eq_zero_of_le (trunc_le n (a - b))]
  exact trunc_zero n

theorem ulp_sub_le_of_two_mul_le_of_lt_round
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₀ : faithful₀ n round)
  (hfaithful₁ : faithful₁ n round)
  (hfa : trunc n a = a) (hba : 2 * b ≤ a)
  (lt_round : a - b < round (a - b))
: ulp n (a - b) - (a - b) % ulp n (a - b) ≤ b := by
  have hba' : b ≤ a := Nat.le_trans (Nat.le_mul_of_pos_left two_pos) hba
  have h₁ : a ≤ b + round (a - b) := by
    trans b + (a - b)
    . rewrite [← add_tsub_assoc_of_le hba']
      exact Nat.le_of_eq $ Eq.symm $ add_tsub_cancel_left _ _
    . apply Nat.add_le_add_left
      exact lt_round.le
  have h₂ : a ≤ round (a - b) + b := by rwa [Nat.add_comm]
  have h₃ : round (a - b) ≤ a := round_sub_le npos hfaithful₀ hfaithful₁ b hfa
  rewrite [← next_trunc_sub_eq_ulp_sub_mod npos]
  rewrite [← round_eq_next_trunc_of_gt hfaithful₁ lt_round]
  rewrite [← add_tsub_assoc' h₁ hba']
  rewrite [Nat.add_comm]
  rewrite [add_tsub_assoc' h₂ h₃]
  exact tsub_le_self

theorem b₁_hi_of_two_mul_le_of_lt_round
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₀ : faithful₀ n round)
  (hfaithful₁ : faithful₁ n round)
  (hfa : trunc n a = a) (hfb : trunc n b = b) (hba : 2 * b ≤ a)
  (lt_round : a - b < round (a - b))
: trunc n (round (a - b) - (a - b)) = round (a - b) - (a - b) := by
  rewrite [round_eq_next_trunc_of_gt hfaithful₁ lt_round]
  have ulp_dvd : ulp n b ∣ ulp n (a - b) := by
    apply ulp_dvd_ulp
    apply le_tsub_of_add_le_left
    rewrite [← Nat.two_mul]
    exact hba
  have hba' : b ≤ a := Nat.le_trans (Nat.le_mul_of_pos_left two_pos) hba
  have ulp_sub_le : ulp n (a - b) - (a - b) % ulp n (a - b) ≤ b :=
    ulp_sub_le_of_two_mul_le_of_lt_round npos hfaithful₀ hfaithful₁ hfa hba lt_round
  apply trunc_eq_of_le_of_ulp_dvd b
  . rewrite [next_trunc_sub_eq_ulp_sub_mod npos]
    exact ulp_sub_le
  . apply Nat.dvd_sub'
    . rewrite [next, ulp_trunc npos]
      apply Nat.dvd_add
      . trans ulp n (a - b)
        . exact ulp_dvd
        . exact ulp_dvd_trunc n _
      . exact ulp_dvd
    . apply Nat.dvd_sub hba'
      . trans ulp n a
        . exact ulp_dvd_ulp n hba'
        . exact ulp_dvd_of_trunc_eq hfa
      . exact ulp_dvd_of_trunc_eq hfb

theorem b₁_lo_of_round_le_of_two_mul_le_of_ulp_le
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₁ : faithful₁ n round)
  (hfa : trunc n a = a)
  (hfb : trunc n b = b)
  (round_le : round (a - b) ≤ a - b)
  (two_mul_le : 2 * b ≤ a)
  (ulp_le : ulp n (a - b) ≤ b)
: trunc n (a - b - round (a - b)) = a - b - round (a - b) := by
  have hba : b ≤ a := by
    trans 2 * b
    . exact Nat.le_mul_of_pos_left two_pos
    . exact two_mul_le
  have hab : b ≤ a - b := by
    rewrite [le_tsub_iff_right hba]
    rewrite [← Nat.two_mul]
    exact two_mul_le
  rewrite [round_eq_trunc_of_le npos hfaithful₁ round_le]
  rewrite [trunc_eq_sub_mod n (a - b)]
  rewrite [tsub_tsub_cancel_of_le (Nat.mod_le _ _)]
  apply trunc_eq_of_le_of_ulp_dvd b
  . trans ulp n (a - b)
    . exact Nat.le_of_lt $ Nat.mod_lt _ (ulp_pos _ _)
    . exact ulp_le
  . rewrite [Nat.dvd_mod_iff (ulp_dvd_ulp n hab)]
    apply Nat.dvd_sub hba
    . trans ulp n a
      . exact ulp_dvd_ulp n hba
      . exact ulp_dvd_of_trunc_eq hfa
    . exact ulp_dvd_of_trunc_eq hfb

theorem b₁_lo_of_round_lt_of_ulp_le
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₀ : faithful₀ n round)
  (hfaithful₁ : faithful₁ n round)
  (hfa : trunc n a = a)
  (hfb : trunc n b = b)
  (hba : b ≤ a)
  (round_lt : round (a - b) < a - b)
  (ulp_le : ulp n a ≤ 2 * b)
: trunc n (a - b - round (a - b)) = a - b - round (a - b) := by
  have hfe : round (a - round (a - b)) = a - round (a - b) := by
    apply round_eq_of_trunc_eq npos hfaithful₀
    apply s₂ npos hfaithful₀ hfaithful₁ hfa hfb hba
  have h₀ : b < round (a - round (a - b)) := by
    rewrite [hfe]
    rewrite [lt_tsub_comm]
    exact round_lt
  apply trunc_eq_of_round_eq npos hfaithful₁
  rewrite [tsub_right_comm, ← hfe]
  apply round_eq_of_trunc_eq npos hfaithful₀
  apply s₃ npos hfaithful₀ hfaithful₁ hfa hfb hfb hba le_rfl ulp_le h₀ h₀.le

theorem b₁_lo_of_of_round_le_of_no_uflow_of_of_ulp_le
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₀ : faithful₀ n round)
  (hfaithful₁ : faithful₁ n round)
  (hcorrect₀ : correct₀ n round)
  (hfa : trunc n a = a)
  (hfb : trunc n b = b)
  (hba : b ≤ a)
  (round_le : round (a - b) ≤ a - b)
  (no_uflow : a - b ≥ 2 ^ n)
  (ulp_le' : ulp n (a - b) ≤ 2 * b)
: trunc n (a - b - round (a - b)) = a - b - round (a - b) := by
  have hca : round (a - b) ≤ a := round_sub_le npos hfaithful₀ hfaithful₁ b hfa
  have ulp_even : 2 ∣ ulp n (a - b) := two_dvd_ulp_of_no_uflow no_uflow
  have hfd : trunc n (a - round (a - b) - b) = a - round (a - b) - b := by
    apply sterbenz
    . exact s₂ npos hfaithful₀ hfaithful₁ hfa hfb hba
    . exact hfb
    . rewrite [le_tsub_iff_left hca, ← le_tsub_iff_right hba]
      exact round_le
    . rewrite [round_eq_trunc_of_le npos hfaithful₁ round_le]
      rewrite [Nat.two_mul]
      rewrite [← tsub_le_iff_left]
      rewrite [tsub_right_comm]
      trans ulp n (a - b) / 2
      . rewrite [tsub_le_iff_left]
        apply le_midpoint_of_round_eq_trunc npos hcorrect₀
        exact round_eq_trunc_of_le npos hfaithful₁ round_le
      . refine Nat.le_of_mul_le_mul_left ?_ two_pos
        rewrite [Nat.mul_comm, Nat.div_mul_cancel ulp_even]
        exact ulp_le'
  rewrite [eq_tsub_iff_add_eq_of_le round_le]
  rewrite [add_comm]
  rewrite [tsub_right_comm]
  rewrite [hfd]
  rewrite [tsub_right_comm]
  exact add_tsub_cancel_of_le round_le

theorem b₁_lo_of_round_lt_of_no_uflow_of_ulp_eq_ulp_of_two_mul_lt_of_pos_of_le_ulp
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₀ : faithful₀ n round)
  (hfaithful₁ : faithful₁ n round)
  (hcorrect₀ : correct₀ n round)
  (hfa : trunc n a = a)
  (hfb : trunc n b = b)
  (hba : b ≤ a)
  (round_lt : round (a - b) < a - b)
  (no_uflow : 2 ^ n ≤ a - b)
  (ulp_eq_ulp : ulp n (a - b) = ulp n a)
  (bpos : b > 0)
  (le_ulp : b ≤ ulp n a)
: trunc n (a - b - round (a - b)) = a - b - round (a - b) := by
  apply b₁_lo_of_round_lt_of_ulp_le npos hfaithful₀ hfaithful₁ hfa hfb hba round_lt
  have apos : 0 < a := Nat.lt_of_lt_of_le two_pow_pos $ Nat.le_trans no_uflow tsub_le_self
  have ulp_even : 2 ∣ ulp n a :=
    two_dvd_ulp_of_no_uflow $ Nat.le_trans no_uflow tsub_le_self
  have h₁ : round (a - b) = trunc n (a - b) := round_eq_trunc_of_le npos hfaithful₁ round_lt.le
  have h₂ : (a - b) % ulp n (a - b) ≤ ulp n (a - b) / 2 := by
    rewrite [← tsub_le_tsub_iff_left (Nat.mod_le _ _)]
    rewrite [← trunc_eq_sub_mod]
    rewrite [tsub_le_iff_right]
    exact le_midpoint_of_round_eq_trunc npos hcorrect₀ h₁
  have h₃ : a - b = a - ulp n a + (ulp n a - b) := by
     rewrite [← add_tsub_assoc_of_le le_ulp]
     rw [tsub_add_cancel_of_le $ ulp_le_self npos apos]
  have h₄ : (a - b) % ulp n (a - b) = ulp n a - b := by
    rewrite [ulp_eq_ulp]
    rewrite [h₃]
    rewrite [← Nat.mod_add_mod]
    rewrite [mod_sub_mod _ _ _ (ulp_le_self npos apos)]
    rewrite [Nat.mod_self, tsub_zero]
    rewrite [Nat.mod_eq_zero_of_dvd (ulp_dvd_of_trunc_eq hfa), Nat.zero_add]
    exact Nat.mod_eq_of_lt (tsub_lt_self (ulp_pos _ _) bpos)
  have h₅ : ulp n a - b ≤ ulp n a / 2 := by
    rewrite [← h₄]
    rewrite [← ulp_eq_ulp]
    exact h₂
  have h₆ : ulp n a / 2 ≤ b := by
    rewrite [← tsub_tsub_cancel_of_le le_ulp]
    rewrite [← sub_half_of_even ulp_even]
    apply tsub_le_tsub_left
    exact h₅
  rewrite [Nat.two_mul]
  rewrite [← tsub_le_iff_left]
  trans ulp n a / 2
  . exact h₅
  . exact h₆

theorem ulp_le_ulp_of_le_ulp_of_size_lt
  {n a b : ℕ} (npos : 0 < n)
  (hfa : trunc n a = a)
  (le_ulp : b ≤ ulp n a)
  (size_lt : 2 ^ (Nat.size a - 1) < a)
: ulp n a ≤ ulp n (a - b) := by
  unfold ulp expt
  apply Nat.pow_le_pow_of_le_right two_pos
  apply tsub_le_tsub_right
  apply Nat.le_of_pred_lt
  rewrite [← Nat.sub_one]
  rewrite [Nat.lt_size]
  trans 2 ^ (Nat.size a - 1) + (ulp n a - b)
  . exact Nat.le_add_right _ _
  . rewrite [← add_tsub_assoc_of_le le_ulp]
    apply tsub_le_tsub_right
    apply add_le_of_dvd_of_dvd_of_lt
    . exact ulp_dvd_of_trunc_eq hfa
    . unfold ulp expt
      rewrite [Nat.pow_dvd_pow_iff_le_right one_lt_two]
      apply tsub_le_tsub_left
      exact Nat.one_le_of_lt npos
    . exact size_lt

theorem b₁_lo_of_round_lt_of_no_uflow_of_ulp_lt_ulp_of_two_mul_lt_of_pos_of_le_ulp
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₀ : faithful₀ n round)
  (hfaithful₁ : faithful₁ n round)
  (hcorrect₀ : correct₀ n round)
  (hfa : trunc n a = a)
  (hfb : trunc n b = b)
  (hba : b ≤ a)
  (round_lt : round (a - b) < a - b)
  (no_uflow : a - b ≥ 2 ^ n)
  (ulp_lt_ulp : ulp n (a - b) < ulp n a)
  (two_mul_lt : 2 * b < a)
  (bpos : b > 0)
  (le_ulp : b ≤ ulp n (a - b))
: trunc n (a - b - round (a - b)) = a - b - round (a - b) := by
  apply b₁_lo_of_of_round_le_of_no_uflow_of_of_ulp_le
    npos hfaithful₀ hfaithful₁ hcorrect₀ hfa hfb hba
    round_lt.le no_uflow
  have ulp_even : 2 ∣ ulp n (a - b) := two_dvd_ulp_of_no_uflow no_uflow
  have lt_ulp : b < ulp n a := Nat.lt_of_le_of_lt le_ulp ulp_lt_ulp
  have lt_size : n < Nat.size a := by
    rewrite [Nat.lt_size]
    trans a - b
    . exact no_uflow
    . exact tsub_le_self
  have size_sub_one_pos : 0 < Nat.size a - 1 :=
    Nat.lt_of_lt_of_le npos $ Nat.le_pred_of_lt lt_size
  have size_pos : 0 < Nat.size a := Nat.lt_of_lt_of_le size_sub_one_pos tsub_le_self
  have apos : 0 < a := Nat.size_pos.mp size_pos
  have eq_pow : a = 2 ^ (Nat.size a - 1) := by
    apply Nat.le_antisymm
    . rewrite [← Nat.not_lt]
      intro (size_lt : 2 ^ (Nat.size a - 1) < a)
      apply Nat.lt_le_antisymm ulp_lt_ulp
      apply ulp_le_ulp_of_le_ulp_of_size_lt npos hfa lt_ulp.le size_lt
    . apply le_size_of_pos
      apply Nat.zero_lt_of_lt
      apply Nat.lt_of_le_of_lt
      . exact no_uflow.le
      . exact tsub_lt_self apos bpos
  have even : 2 ∣ 2 ^ (Nat.size a - 1) := by
    apply dvd_pow_self 2
    apply Nat.not_eq_zero_of_lt
    exact size_sub_one_pos
  have ulp_eq_half_ulp : ulp n (a - b) = ulp n a / 2 := by
    have size_lt_size : Nat.size (a - b) < Nat.size a := by
      rewrite [← Nat.succ_pred (Nat.not_eq_zero_of_lt lt_size)]
      rewrite [Nat.lt_succ, ← Nat.sub_one]
      rewrite [Nat.size_le, ← eq_pow]
      exact tsub_lt_self apos bpos
    have pow_lt : 2 ^ (Nat.size a - 1) / 2 < a - b := by
      rewrite [lt_tsub_comm]
      conv => rhs ; left ; rewrite [eq_pow]
      rewrite [sub_half_of_even even]
      apply lt_of_mul_lt_mul_left' (a := 2)
      rewrite [Nat.mul_div_cancel_left' even]
      rewrite [← eq_pow]
      exact two_mul_lt
    have size_eq_size_sub_one : Nat.size (a - b) = Nat.size a - 1 := by
      apply Nat.le_antisymm
      . rewrite [← Nat.lt_iff_le_pred size_pos]
        exact size_lt_size
      . apply Nat.le_of_pred_lt
        rewrite [← Nat.sub_one]
        rewrite [Nat.lt_size]
        rewrite [← Nat.pow_div (Nat.one_le_of_lt size_sub_one_pos) two_pos]
        rewrite [pow_one]
        exact pow_lt.le
    have size_add_one_eq_size : Nat.size (a - b) + 1 = Nat.size a := by
      rewrite [← Nat.succ_pred (Nat.not_eq_zero_of_lt size_pos)]
      rewrite [← Nat.sub_one, ← Nat.add_one]
      apply congr_arg (fun w => w + 1)
      exact size_eq_size_sub_one
    have le_size : n ≤ Nat.size (a - b) := by
      apply Nat.le_of_lt
      rewrite [Nat.lt_size]
      exact no_uflow
    have two_ulp_eq_ulp : 2 * ulp n (a - b) = ulp n a := by
      rewrite [← pow_one 2]
      unfold ulp expt
      rewrite [← pow_add]
      rewrite [Nat.add_comm]
      rewrite [tsub_add_eq_add_tsub le_size]
      apply congr_arg (fun w => 2 ^ (w - n))
      exact size_add_one_eq_size
    have ulp_even' : 2 ∣ ulp n a :=
      Nat.dvd_trans ulp_even $ ulp_dvd_ulp n tsub_le_self
    apply mul_left_cancel₀ two_ne_zero
    rewrite [Nat.mul_div_cancel_left' ulp_even']
    exact two_ulp_eq_ulp
  have one_le_size_sub : 1 ≤ Nat.size a - n := by
    apply Nat.one_le_of_lt
    rewrite [tsub_pos_iff_lt]
    exact lt_size
  have le_size_sub_one : n ≤ Nat.size a - 1 := Nat.le_pred_of_lt lt_size
  have h₂ : a - b - trunc n (a - b) = ulp n (a - b) - b := by
    have k₁ : a = 2 ^ n * ulp n (a - b) := by
      rewrite [ulp_eq_half_ulp]
      unfold ulp expt
      conv => rhs ; right ; right ; rewrite [← pow_one 2]
      rewrite [Nat.pow_div one_le_size_sub two_pos, ← pow_add]
      rewrite [tsub_right_comm]
      rewrite [add_tsub_cancel_of_le le_size_sub_one]
      exact eq_pow
    have k₂ : a - b = (2 ^ n - 1) * ulp n (a - b) + (ulp n (a - b) - b) := by
      rewrite [Nat.sub_one, Nat.mul_pred_left]
      rewrite [← add_tsub_assoc_of_le le_ulp]
      rewrite [tsub_add_cancel_of_le (Nat.le_mul_of_pos_left two_pow_pos)]
      rw [← k₁]
    have k₃ : trunc n (a - b) = (2 ^ n - 1) * ulp n (a - b) := by
      unfold trunc
      conv => lhs ; left ; left ; rewrite [k₂]
      rewrite [Nat.add_comm]
      rewrite [Nat.add_mul_div_right _ _ (ulp_pos _ _)]
      rewrite [Nat.div_eq_zero (tsub_lt_self (ulp_pos _ _) bpos)]
      rw [Nat.zero_add]
    conv => lhs ; left ; rewrite [k₂]
    rewrite [k₃]
    exact add_tsub_cancel_left _ _
  have h₃ : ulp n (a - b) / 2 ≤ b := by
    rewrite [← Nat.not_lt]
    intro (lt : b < ulp n (a - b) / 2)
    have k₁ : ulp n (a - b) / 2 < ulp n (a - b) - b := by
      rewrite [lt_tsub_comm]
      rewrite [sub_half_of_even ulp_even]
      exact lt
    have k₂ : ulp n (a - b) / 2 < a - b - trunc n (a - b) := by
      rewrite [h₂]
      exact k₁
    have k₃ : a - b - trunc n (a - b) ≤ ulp n (a - b) / 2 := by
      rewrite [tsub_le_iff_left]
      apply le_midpoint_of_round_eq_trunc npos hcorrect₀
      exact round_eq_trunc_of_le npos hfaithful₁ round_lt.le
    exact Nat.lt_le_antisymm k₂ k₃
  rewrite [← Nat.mul_div_cancel_left' ulp_even]
  apply Nat.mul_le_mul_left
  exact h₃

theorem b₁
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₀ : faithful₀ n round)
  (hfaithful₁ : faithful₁ n round)
  (hcorrect₀ : correct₀ n round)
  (hfa : trunc n a = a) (hfb : trunc n b = b) (hba : b ≤ a)
: trunc n (a - b - round (a - b)) = a - b - round (a - b) ∧
  trunc n (round (a - b) - (a - b)) = round (a - b) - (a - b) := by
  cases Nat.lt_or_ge (a - b) (2 ^ n) with
  | inl uflow =>
    apply b₁_of_round_eq
    apply round_eq_of_trunc_eq npos hfaithful₀
    exact trunc_eq_self_of_uflow uflow
  | inr no_uflow =>
    cases Nat.eq_zero_or_pos b with
    | inl bzero =>
      apply b₁_of_round_eq
      rewrite [bzero, tsub_zero]
      exact round_eq_of_trunc_eq npos hfaithful₀ hfa
    | inr bpos =>
      cases Nat.lt_or_ge (2 * b) a with
      | inr le_two_mul =>
        apply b₁_of_round_eq
        apply round_eq_of_trunc_eq npos hfaithful₀
        exact sterbenz hfa hfb hba le_two_mul
      | inl two_mul_lt =>
        rcases Nat.lt_trichotomy (a - b) (round (a - b)) with (lt_round | eq_round | round_lt)
        . -- lt_round : a - b < round (a - b)
          constructor
          . exact b₁_lo_of_lt_round npos hfaithful₁ lt_round
          . exact b₁_hi_of_two_mul_le_of_lt_round npos hfaithful₀ hfaithful₁
              hfa hfb two_mul_lt.le lt_round
        . -- eq_round : a - b = round (a - b)
          exact b₁_of_round_eq eq_round.symm
        . -- round_lt : round (a - b) < a - b
          constructor
          . cases Nat.lt_or_ge b (ulp n (a - b)) with
            | inl lt_ulp =>
              cases Nat.eq_or_lt_of_le (ulp_le_ulp n tsub_le_self) with
              | inl ulp_eq_ulp =>
                exact b₁_lo_of_round_lt_of_no_uflow_of_ulp_eq_ulp_of_two_mul_lt_of_pos_of_le_ulp
                  npos hfaithful₀ hfaithful₁ hcorrect₀ hfa hfb hba
                  round_lt no_uflow ulp_eq_ulp bpos (ulp_eq_ulp ▸ lt_ulp.le)
              | inr ulp_lt_ulp =>
                exact b₁_lo_of_round_lt_of_no_uflow_of_ulp_lt_ulp_of_two_mul_lt_of_pos_of_le_ulp
                  npos hfaithful₀ hfaithful₁ hcorrect₀ hfa hfb hba
                  round_lt no_uflow ulp_lt_ulp two_mul_lt bpos lt_ulp.le
            | inr ulp_le =>
              exact b₁_lo_of_round_le_of_two_mul_le_of_ulp_le npos hfaithful₁
                hfa hfb round_lt.le two_mul_lt.le ulp_le
          . exact b₁_hi_of_round_le npos hfaithful₁ round_lt.le

theorem sum_and_error₂_lo
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₀ : faithful₀ n round)
  (hfaithful₁ : faithful₁ n round)
  (hcorrect₀ : correct₀ n round)
  (hfa : trunc n a = a) (hfb : trunc n b = b) (hba : b ≤ a)
  (round_le : round (a - b) ≤ a - b)
: round (a - b) + round (round (a - round (a - b)) - b) = a - b := by
  have ⟨hfr₁, _⟩ := b₁ npos hfaithful₀ hfaithful₁ hcorrect₀ hfa hfb hba
  have hfe : round (a - round (a - b)) = a - round (a - b) := by
    apply round_eq_of_trunc_eq npos hfaithful₀
    exact s₂ npos hfaithful₀ hfaithful₁ hfa hfb hba
  have hfr : round (a - b - round (a - b)) = a - b - round (a - b) :=
    round_eq_of_trunc_eq npos hfaithful₀ $ hfr₁
  rewrite [hfe]
  rewrite [tsub_right_comm]
  rewrite [hfr]
  rewrite [Nat.add_comm]
  exact tsub_add_cancel_of_le round_le

theorem sum_and_error₂_hi
  {round : ℕ → ℕ} {n a b : ℕ} (npos : 0 < n)
  (hfaithful₀ : faithful₀ n round)
  (hfaithful₁ : faithful₁ n round)
  (hcorrect₀ : correct₀ n round)
  (hfa : trunc n a = a) (hfb : trunc n b = b) (hba : b ≤ a)
  (le_round : a - b ≤ round (a - b))
: round (a - b) - round (b - round (a - round (a - b))) = a - b := by
  have ⟨_, hfr₂⟩ := b₁ npos hfaithful₀ hfaithful₁ hcorrect₀ hfa hfb hba
  have hfe : round (a - round (a - b)) = a - round (a - b) := by
    apply round_eq_of_trunc_eq npos hfaithful₀
    exact s₂ npos hfaithful₀ hfaithful₁ hfa hfb hba
  have hca : round (a - b) ≤ a := round_sub_le npos hfaithful₀ hfaithful₁ b hfa
  have h : b - (a - round (a - b)) = round (a - b) - (a - b) := by
    apply tsub_eq_of_eq_add
    rewrite [tsub_add_eq_add_tsub le_round]
    rewrite [add_tsub_cancel_of_le hca]
    exact Eq.symm $ tsub_tsub_cancel_of_le hba
  rewrite [hfe]
  rewrite [h]
  rewrite [round_eq_of_trunc_eq npos hfaithful₀ hfr₂]
  exact tsub_tsub_cancel_of_le le_round
