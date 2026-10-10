module

public import KuhnPoker

/-!
# Solution

Each statement of `Challenge.lean`, restated verbatim and closed by the internal theorem of the same
name with the suffix `_internal` (the modules of `KuhnPoker/`; VERIFICATION.md names the module of
each theorem). This module does not import `Challenge.lean`; the definitions come from
`KuhnPoker/Defs.lean`, which restates those of the Challenge character for character.
-/

@[expose] public section

namespace KuhnPoker

theorem hasValue_one_one : HasValue 1 1 (-1 / 18) :=
  hasValue_one_one_internal

theorem hasValue_unique (a b v w : ℝ) (hv : HasValue a b v) (hw : HasValue a b w) : v = w :=
  hasValue_unique_internal a b v w hv hw

theorem exists_isEquilibrium : ∃ σ τ, IsEquilibrium 1 1 σ τ :=
  exists_isEquilibrium_internal

theorem payoff_of_isEquilibrium (σ : Strategy₁) (τ : Strategy₂) (h : IsEquilibrium 1 1 σ τ) :
    payoff 1 1 σ τ = -1 / 18 :=
  payoff_of_isEquilibrium_internal σ τ h

theorem isEquilibrium_iff (σ : Strategy₁) (τ : Strategy₂) :
    IsEquilibrium 1 1 σ τ ↔ Guarantees₁ 1 1 σ (-1 / 18) ∧ Guarantees₂ 1 1 τ (-1 / 18) :=
  isEquilibrium_iff_internal σ τ

theorem guarantees₂_iff (τ : Strategy₂) : Guarantees₂ 1 1 τ (-1 / 18) ↔ τ = kuhnII :=
  guarantees₂_iff_internal τ

theorem guarantees₁_iff (σ : Strategy₁) : Guarantees₁ 1 1 σ (-1 / 18) ↔
    ∃ α ∈ Set.Icc (0 : ℝ) (1 / 3), ∃ k ∈ Set.Icc (0 : ℝ) 1, (3 * α = 1 ∨ k = 1) ∧ σ = kuhnI α k :=
  guarantees₁_iff_internal σ

theorem essentialMatrix_eq (i : Fin 8) (j : Fin 4) :
    6 * payoff 1 1 (pure₁ (essentialRow i)) (pure₂ (essentialCol j)) = essentialMatrix i j :=
  essentialMatrix_eq_internal i j

theorem basic₁_guarantees (i : Fin 12) : GuaranteesMixed₁ (basic₁ i) (-1 / 18) :=
  basic₁_guarantees_internal i

theorem basic₂_guarantees (i : Fin 2) : GuaranteesMixed₂ (basic₂ i) (-1 / 18) :=
  basic₂_guarantees_internal i

theorem hasMixedValue : HasMixedValue (-1 / 18) :=
  hasMixedValue_internal

theorem guaranteesMixed₁_iff (p : (Fin 3 → Fin 3) → ℝ) : GuaranteesMixed₁ p (-1 / 18) ↔
    IsProb p ∧ ∃ α ∈ Set.Icc (0 : ℝ) (1 / 3),
      realBet p = ![α, 0, 3 * α] ∧ realCall p = ![0, α + 1 / 3, 1 - 3 * α] :=
  guaranteesMixed₁_iff_internal p

theorem guaranteesMixed₂_iff (q : (Fin 3 → Fin 4) → ℝ) : GuaranteesMixed₂ q (-1 / 18) ↔
    IsProb q ∧ margBet q = ![1 / 3, 0, 1] ∧ margCall q = ![0, 1 / 3, 1] :=
  guaranteesMixed₂_iff_internal q

theorem hasValue_general (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : HasValue a b (kuhnValue a b) :=
  hasValue_general_internal a b ha hb

theorem kuhnValue_one_one : kuhnValue 1 1 = -1 / 18 :=
  kuhnValue_one_one_internal

theorem guarantees_case_one (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) :
    Guarantees₁ a b (![b / (2 * a + b), 0, 1], ![0, 2 * a / (2 * a + b), 1]) (kuhnValue a b) ∧
    Guarantees₂ a b (![b / (2 * a + b), 0, 1], ![0, (2 * a - b) / (2 * a + b), 1]) (kuhnValue a b) :=
  guarantees_case_one_internal a b ha hb hab

theorem guarantees_case_three (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (hb2 : b ≤ 2 * a)
    (η : ℝ) (hη : η ∈ Set.Icc ((2 * a - b) / (2 * a + b)) (b / (2 * a + b))) :
    Guarantees₁ a b (![0, 0, 0], ![0, (2 * a - b) / (2 * a + b), 1]) (kuhnValue a b) ∧
    Guarantees₂ a b (![b / (2 * a + b), 0, 1], ![0, η, 1]) (kuhnValue a b) :=
  guarantees_case_three_internal a b ha hb hab hb2 η hη

theorem guarantees_case_four (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 2 * a ≤ b) :
    Guarantees₁ a b (![0, 0, 0], ![0, 0, 1]) 0 ∧ Guarantees₂ a b (![0, 0, 1], ![0, 0, 1]) 0 :=
  guarantees_case_four_internal a b ha hb hab

end KuhnPoker
