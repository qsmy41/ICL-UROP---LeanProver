import topology.algebra.infinite_sum
import data.real.basic

open_locale big_operators
open_locale classical
open finset

-- #check has_sum (λ n, (a n)^n)

notation `|`x`|` := abs x

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

def non_decreasing (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

def is_seq_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

/- The following is a lemma proven from exercises -/

lemma bounded_above_and_increasing_func_converges_to_sup 
(M : ℝ) (u : ℕ → ℝ) (h : is_seq_sup M u) (h' : non_decreasing u) :
seq_limit u M :=
begin
  -- get rid off most of the ∀, ∃ statements
  intros ε ε_pos,
  cases h with ha hb,
  cases hb ε ε_pos with n₀ un₀,
  use n₀,
  intros n,
  specialize h' n₀ n,
  intros h'l,
  -- gather hypothesis to prove the desired result
  have inter₁ : u n₀ ≤ u n,
  {
    apply h',
    exact h'l,
  },
  have inter₂ : u n ≥ M - ε,
    { linarith, },
  have inter₃ : M + ε ≥ u n,
  {
    specialize ha n,
    linarith,
  },
  have inter₂' : M - u n ≤ ε,
    { linarith, },
  have inter₃' : u n - M ≤ ε,
    { linarith, },
  rw abs_le,
  split,
  repeat { linarith, },
end

lemma bounded_above_and_increasing_func_converges
(u : ℕ → ℝ) (bounded_above : ∃ x : ℝ, ∀ n : ℕ, u n ≤ x) (increasing : non_decreasing u) :
∃ l : ℝ, seq_limit u l :=
begin
  have non_empty : (∃ (x : ℝ), x ∈ set.range u),
  {
    use u 1,
    use 1,
  },
  -- prove that ∃ supremum
  have inter : (∃ (x : ℝ), ∀ (y : ℝ), x ≤ y ↔ ∀ (z : ℝ), z ∈ set.range u → z ≤ y),
  {
    refine real.exists_sup (set.range u) non_empty _,
    cases bounded_above with x hx,
    use x,
    intros y hy, 
    cases hy with n hn,
    specialize hx n,
    linarith,
  },
  -- in inter, x is sup, y is upper bounds, z is (u n)
  cases inter with M hM,
  cases bounded_above with x hx,
  -- simplify the expression
  /- Note: inter' should not prematurely specify y,
   - e.g. have inter₁ : M ≤ x ↔ ∀ (n : ℕ), u n ≤ x,
   - otherwise cannot be used as the Prop to be contraposed
   -/
  have inter' : ∀ y : ℝ, M ≤ y ↔ ∀ n : ℕ, u n ≤ y, 
  {
    intros y,
    rw hM,
    exact set.forall_range_iff,
  },
  -- necessary lemma to be proved so as to prove the current lemma
  have is_sup : ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε,
  {
    contrapose! inter',
    rcases inter' with ⟨ε, ε_pos, hε⟩,
    use (M - ε / 2),
    rw not_iff,
    rw not_le,
    split,
    {
      intros h1 n,
      specialize hε n,
      linarith,
    },
    {
      intro h,
      linarith,
    },
  },
  -- use everything proved previously to prove the proposition!
  use M,
  refine bounded_above_and_increasing_func_converges_to_sup M u _ increasing,
  split,
  {
    specialize inter' M,
    apply inter'.1,
    linarith,
  },
  {
    exact is_sup,
  },
end

-- The following two lemmas thanks to Jason KY

def partial_sum_to (a : ℕ → ℝ) (n : ℕ) := finset.sum (finset.range n) a
notation `∑` a := partial_sum_to a

lemma sum_diff {a : ℕ → ℝ} {n m : ℕ} (h₁ : n < m) : (∑ a) m - (∑ a) n = finset.sum (finset.Ico n m) a :=
begin
  unfold partial_sum_to, 
  induction m with k hk,
  {
    exfalso, 
    from nat.not_succ_le_zero n h₁,
  },
  {
    rw [finset.sum_range_succ, finset.sum_Ico_succ_top],
    swap, 
    from nat.lt_succ_iff.mp h₁,
    simp,
    cases nat.lt_succ_iff_lt_or_eq.mp h₁,
    {
      specialize hk h,
      linarith,
    },
    -- the line below somehow doesn't work for proving the first case
    -- {rw [←sub_eq_add_neg, hk h]},
    {
      rw h, 
      simp,
    },
  }
end

lemma sum_pos {a : ℕ → ℝ} {n m : ℕ} (h₁ : ∀ k : ℕ, 0 ≤ a k) : 0 ≤ finset.sum (finset.Ico n m) a :=
begin
  induction m with k hk,
  {
    rw finset.Ico.eq_empty_iff.mpr (zero_le n), 
    simp,
  },
  {
    cases le_or_lt n k,
    {
      rw finset.sum_Ico_succ_top h,
      from add_nonneg hk (h₁ k),
    },
    {
      rw finset.Ico.eq_empty_iff.mpr (nat.succ_le_iff.mpr h),
      simp,
    },
  },
end

lemma series_of_root_numbers_converges 
(a : ℕ → ℝ) (l : ℝ) (h_seq : seq_limit a l) (hu : ∀ n : ℕ, a n ≥ 0) 
(l_pos : l ≥ 0) (l_lt_one: l < 1) :
∃ x : ℝ, seq_limit (λ N : ℕ , (∑ (λ n : ℕ, a n ^ n)) N) x :=
-- ∃ x : ℝ, seq_limit (λ N, ∑ n in range N, (a n) ^ n) x :=
begin
  have hann : ∀ n : ℕ, a n ^ n ≥ 0,
  {
    intros n,
    specialize hu n,
    exact pow_nonneg hu n,
  },
  apply bounded_above_and_increasing_func_converges,
  {
    -- prove that the series is bounded above
    unfold seq_limit at h_seq,
    specialize h_seq ((1 - l) / 2) (by linarith),
    cases h_seq with N hN,
    let A : ℝ := (1 + l) / 2,
    have A_pos : A > 0,
    {
      have inter : (1 + l) / 2 > 0, { linarith, },
      exact inter,
    },
    -- Below is the upper bound of the series
    use (((∑ (λ n : ℕ, a n ^ n)) N) + A ^ N / (1 - A)),
    intro n,
    let hN' := hN n,
    by_cases n ≤ N,
    {
      -- trivial but unfortunately long proof...
      have hAN : A ^ N / (1 - A) > 0,
      {
        have temp₁ : A ^ N > 0,
        { exact pow_pos A_pos N, },
        have temp₂ : 1 - A > 0,
        {
          have inter : (1 - (1 + l) / 2 > 0), { linarith, },
          exact inter,
        },
        exact div_pos temp₁ temp₂,
      },
      by_cases h' : n = N,
      {
        rw h',
        linarith,
      },
      {
        refine sub_nonneg.mp _,
        have temp_add_sub_comm: ∀ x y z : ℝ, x + y - z = x - z + y,
        {
          intros x y z,
          ring,
        },
        rw temp_add_sub_comm,
        have hnN : n < N, 
        { exact lt_of_le_of_ne h h', },
        rw sum_diff hnN,
        have nonneg_sum_diff : 0 ≤ finset.sum (finset.Ico n N) (λ n : ℕ, a n ^ n),
        { exact sum_pos hann, },
        linarith,
      },
    },
    {
      push_neg at h,
      have h' : N ≤ n, { linarith, },
      specialize hN' h',
      -- The following cᵢ's are for deducing the calc block later
      have c₁ : (∑λ (n : ℕ), a n ^ n) n - (∑λ (n : ℕ), a n ^ n) N 
        = finset.sum (finset.Ico N n) (λ (n : ℕ), a n ^ n),
      { exact sum_diff h, },
      have c₂ : finset.sum (finset.Ico N n) (λ (n : ℕ), a n ^ n) 
        ≤ finset.sum (finset.Ico N n) (λ (n : ℕ), A ^ n),
      {
        have temp : ∀ x ∈ Ico N n, a x ^ x ≤ A ^ x,
        {
          intros n' hn'Nn,
          have haA : a n' ≤ (1 + l) / 2,
          {
            specialize hN n' _,
            {
              rw abs_le at hN,
              cases hN,
              linarith,
            },
            {
              rwa Ico.mem at hn'Nn,
              linarith,
            },
          },
          exact pow_le_pow_of_le_left (hu n') haA n',
        },
        exact sum_le_sum temp,
      },
      calc (∑λ (n : ℕ), a n ^ n) n 
      = (∑λ (n : ℕ), a n ^ n) N + finset.sum (finset.Ico N n) (λ (n : ℕ), a n ^ n) : by linarith
      ... ≤ (∑λ (n : ℕ), a n ^ n) N + finset.sum (finset.Ico N n) (λ (n : ℕ), A ^ n) : by linarith
      ... = (∑λ (n : ℕ), a n ^ n) N + (A ^ N - A ^ n) / (1 - A) : by sorry
      ... ≤ (∑λ (n : ℕ), a n ^ n) N + A ^ N / (1 - A) : by sorry,
    },
  },
  {
    -- prove that the series is monotonically increasing
    unfold non_decreasing,
    intros n m hnm,
    rw le_iff_lt_or_eq at hnm,
    cases hnm with hl he,
    {
      refine sub_nonneg.mp _,
      rw sum_diff hl,
      exact sum_pos hann,
    },
    {
      rw le_iff_lt_or_eq,
      right,
      rwa he,
    },
  },
end

/- potentially more general version:
lemma series_of_root_numbers_converges 
(a : ℕ → ℝ) (l : ℝ) (h_seq : seq_limit a l) (hu : ∀ n : ℕ, a n ≥ 0) 
(l_pos : l ≥ 0) (l_lt_one: l < 1) :
∃ x : ℝ, has_sum (λ n, (a n) ^ n) x :=
begin
  sorry
end
 -/