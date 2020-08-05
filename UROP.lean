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
    linarith,
  have inter₃ : M + ε ≥ u n,
  {
    specialize ha n,
    linarith,
  },
  have inter₂' : M - u n ≤ ε,
    linarith,
  have inter₃' : u n - M ≤ ε,
    linarith,
  rw abs_le,
  split,
  repeat {linarith,},
end

#check real.exists_sup
variable u : ℕ → ℝ
#check u

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

lemma series_of_root_numbers_converges 
(a : ℕ → ℝ) (l : ℝ) (h_seq : seq_limit a l) (hu : ∀ n : ℕ, a n ≥ 0) 
(l_pos : l ≥ 0) (l_lt_one: l < 1) :
∃ x : ℝ, seq_limit (λ N, ∑ n in range N, (a n) ^ n) x :=
begin
  apply bounded_above_and_increasing_func_converges,
  {
    sorry
  },
  {
    sorry
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