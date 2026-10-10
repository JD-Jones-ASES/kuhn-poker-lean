module

public import KuhnPoker.Boundary

/-!
# The equilibria at every ante and bet

The witnesses of `hasValue_general_internal` sandwich the payoff of every equilibrium, so every equilibrium pays
`kuhnValue a b` and a pair is an equilibrium iff each strategy guarantees the value (no minimax theorem is
needed); with the optimal sets this makes the equilibria explicit in every region, on the line `b = 2a` as I's
single strategy with II's polytope.
-/

@[expose] public section

namespace KuhnPoker

/-- At every ante `a > 0` and bet `b > 0`, every equilibrium pays I exactly `kuhnValue a b`. -/
theorem payoff_of_isEquilibrium_general_internal (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (σ : Strategy₁) (τ : Strategy₂) (h : IsEquilibrium a b σ τ) :
    payoff a b σ τ = kuhnValue a b := by
  obtain ⟨⟨σ₀, hσ₀⟩, ⟨τ₀, hτ₀⟩⟩ := hasValue_general_internal a b ha hb
  obtain ⟨hσ, hτ, h1, h2⟩ := h
  exact le_antisymm ((h2 τ₀ hτ₀.1).trans (hτ₀.2 σ hσ))
    ((hσ₀.2 τ hτ).trans (h1 σ₀ hσ₀.1))

/-- At every ante `a > 0` and bet `b > 0`, a pair is an equilibrium iff each strategy guarantees `kuhnValue a b` (the
exchangeability of optimal strategies in a zero-sum game); with the optimal sets this makes the equilibria explicit
in every region. -/
theorem isEquilibrium_general_iff_internal (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (σ : Strategy₁) (τ : Strategy₂) :
    IsEquilibrium a b σ τ ↔
      Guarantees₁ a b σ (kuhnValue a b) ∧ Guarantees₂ a b τ (kuhnValue a b) := by
  constructor
  · intro h
    have hv := payoff_of_isEquilibrium_general_internal a b ha hb σ τ h
    obtain ⟨hσ, hτ, h1, h2⟩ := h
    exact ⟨⟨hσ, fun τ' hτ' => hv ▸ h2 τ' hτ'⟩, ⟨hτ, fun σ' hσ' => hv ▸ h1 σ' hσ'⟩⟩
  · rintro ⟨h1, h2⟩
    exact co_isEquilibrium_of h1 h2

/-- The equilibria on the line `b = 2a`, explicitly: I never bets first, folds the `1` and the `2` to a bet and calls
with the `3`, and II is any strategy of the polytope of `boundary_II_iff`. -/
theorem boundary_isEquilibrium_iff_internal (a : ℝ) (ha : 0 < a) (σ : Strategy₁) (τ : Strategy₂) :
    IsEquilibrium a (2 * a) σ τ ↔
      σ = (![0, 0, 0], ![0, 0, 1]) ∧ τ.IsValid ∧ τ.1 1 = 0 ∧
      2 * τ.1 0 ≤ τ.1 2 ∧ τ.2 0 + τ.2 1 ≤ τ.1 0 ∧
      1 ≤ τ.2 1 + τ.2 2 ∧ 1 + τ.1 0 + τ.2 0 ≤ 2 * τ.2 2 := by
  have hb : 0 < 2 * a := by positivity
  rw [isEquilibrium_general_iff_internal a (2 * a) ha hb σ τ,
    case_three_I_unique_internal a (2 * a) ha hb (by linarith) le_rfl σ]
  simp only [sub_self, zero_div, gn_value_case_four ha le_rfl, boundary_II_iff_internal a ha τ]

end KuhnPoker
