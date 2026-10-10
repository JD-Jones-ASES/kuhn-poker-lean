module

public import KuhnPoker.Defs

/-!
# The payoff as a sum over the six deals

The shared lemma every module unfolds through: `payoff a b σ τ` is the sum of the six `dealPayoff`s over the
deals of distinct cards, divided by six. After `simp only [dealPayoff, toHigher]` with the `Fin` comparisons
decided, the payoff is an explicit polynomial in the twelve probabilities, `a` and `b`.
-/

@[expose] public section

namespace KuhnPoker

theorem payoff_eq_sum (a b : ℝ) (σ : Strategy₁) (τ : Strategy₂) :
    payoff a b σ τ = (dealPayoff a b σ τ 0 1 + dealPayoff a b σ τ 0 2 + dealPayoff a b σ τ 1 0
      + dealPayoff a b σ τ 1 2 + dealPayoff a b σ τ 2 0 + dealPayoff a b σ τ 2 1) / 6 := by
  sorry

end KuhnPoker
