module

public import KuhnPoker.General

/-!
# The line `b = 2a`: II's optimal set

At `b = 2a` I's strategy that never bets first, folds the `1` and the `2` and calls with the `3` earns `a·u₁/3`
against II's `(u, v)`, so every optimal strategy of II has `u₁ = 0`; four more pure strategies of I, one card
changed at a time, give four inequalities, and `boundary_II_certificate_internal` shows they suffice: under them
`−3` times the payoff is `a` times six nonnegative products. The polytope's nine vertices and its dimension are
replayed by `scripts/check_boundary.py`, not stated.
-/

@[expose] public section

namespace KuhnPoker

/-- The identity behind II's optimal set on the line `b = 2a`, for every `a` and every pair of strategies (valid or
not) in which II never bets the `2` after a pass: `−3` times the payoff is `a` times six products, each nonnegative
when I's strategy is valid and II's lies in the polytope of `boundary_II_iff`. -/
theorem boundary_II_certificate_internal (a : ℝ) (σ : Strategy₁) (τ : Strategy₂)
    (hmid : τ.1 1 = 0) :
    -3 * payoff a (2 * a) σ τ = a *
      (2 * σ.1 0 * (τ.2 1 + τ.2 2 - 1)
        + (1 - σ.1 0) * σ.2 0 * τ.1 2
        + σ.1 1 * (2 * τ.2 2 - 1 - τ.1 0 - τ.2 0)
        + (1 - σ.1 1) * σ.2 1 * (τ.1 2 - 2 * τ.1 0)
        + σ.1 2 * (τ.1 0 - τ.2 0 - τ.2 1)
        + 2 * (1 - σ.1 2) * (1 - σ.2 2) * τ.1 0) := by
  rw [payoff_eq_sum]
  simp only [dealPayoff, toHigher, Fin.reduceLT, ↓reduceIte, hmid]
  ring

/-- The line `b = 2a`: II's optimal strategies exactly — valid, never betting the `2` after a pass, and with the bets
`u` after a pass and the calls `v` satisfying `2u₀ ≤ u₂`, `v₀ + v₁ ≤ u₀`, `1 ≤ v₁ + v₂` and `1 + u₀ + v₀ ≤ 2v₂` (a
polytope whose nine vertices `scripts/check_boundary.py` replays); Kuhn's p. 103 remark that at `b = 2a` II "can
vary his strategy considerably", made exact. -/
theorem boundary_II_iff_internal (a : ℝ) (ha : 0 < a) (τ : Strategy₂) :
    Guarantees₂ a (2 * a) τ 0 ↔ τ.IsValid ∧ τ.1 1 = 0 ∧
      2 * τ.1 0 ≤ τ.1 2 ∧ τ.2 0 + τ.2 1 ≤ τ.1 0 ∧
      1 ≤ τ.2 1 + τ.2 2 ∧ 1 + τ.1 0 + τ.2 0 ≤ 2 * τ.2 2 := by
  obtain ⟨u, v⟩ := τ
  constructor
  · rintro ⟨hτ, h⟩
    have hτ' := hτ
    simp only [Strategy₂.IsValid, Set.mem_Icc] at hτ'
    obtain ⟨⟨hu1, -⟩, -, -⟩ := hτ' 1
    -- I's pure strategies in Kuhn's coding (0 = pass then fold, 1 = pass then call, 2 = bet):
    -- (0, 0, 1), then (0, 1, 1), (0, 0, 2), (2, 0, 1), (0, 2, 1), one card changed at a time.
    have FA := h (![0, 0, 0], ![0, 0, 1])
      (gn_isValid₁ gn_zero_mem gn_zero_mem gn_zero_mem gn_zero_mem gn_zero_mem gn_one_mem)
    have FB := h (![0, 0, 0], ![0, 1, 1])
      (gn_isValid₁ gn_zero_mem gn_zero_mem gn_zero_mem gn_zero_mem gn_one_mem gn_one_mem)
    have FC := h (![0, 0, 1], ![0, 0, 0])
      (gn_isValid₁ gn_zero_mem gn_zero_mem gn_one_mem gn_zero_mem gn_zero_mem gn_zero_mem)
    have FD := h (![1, 0, 0], ![0, 0, 1])
      (gn_isValid₁ gn_one_mem gn_zero_mem gn_zero_mem gn_zero_mem gn_zero_mem gn_one_mem)
    have FE := h (![0, 1, 0], ![0, 0, 1])
      (gn_isValid₁ gn_zero_mem gn_one_mem gn_zero_mem gn_zero_mem gn_zero_mem gn_one_mem)
    rw [payoff_eq_sum] at FA FB FC FD FE
    simp only [dealPayoff, toHigher, Matrix.cons_val, Fin.reduceLT, ↓reduceIte] at FA FB FC FD FE
    have zu1 : u 1 = 0 := by
      have k : a * u 1 ≤ 0 := by linarith only [FA]
      exact le_antisymm (nonpos_of_mul_nonpos_right k ha) hu1
    simp only [zu1] at FB FC FD FE
    refine ⟨hτ, zu1, ?_, ?_, ?_, ?_⟩
    · have k : a * (2 * u 0 - u 2) ≤ 0 := by linarith only [FB]
      linarith only [nonpos_of_mul_nonpos_right k ha]
    · have k : a * (v 0 + v 1 - u 0) ≤ 0 := by linarith only [FC]
      linarith only [nonpos_of_mul_nonpos_right k ha]
    · have k : a * (1 - v 1 - v 2) ≤ 0 := by linarith only [FD]
      linarith only [nonpos_of_mul_nonpos_right k ha]
    · have k : a * (1 + u 0 + v 0 - 2 * v 2) ≤ 0 := by linarith only [FE]
      linarith only [nonpos_of_mul_nonpos_right k ha]
  · rintro ⟨hτ, hmid, c₁, c₂, c₃, c₄⟩
    refine ⟨hτ, ?_⟩
    rintro ⟨x, y⟩ hσ
    have hc := boundary_II_certificate_internal a (x, y) (u, v) hmid
    dsimp only at hmid c₁ c₂ c₃ c₄ hc
    simp only [Strategy₁.IsValid, Set.mem_Icc] at hσ
    obtain ⟨⟨hx0, hx0'⟩, hy0, -⟩ := hσ 0
    obtain ⟨⟨hx1, hx1'⟩, hy1, -⟩ := hσ 1
    obtain ⟨⟨hx2, hx2'⟩, -, hy2'⟩ := hσ 2
    have hτ' := hτ
    simp only [Strategy₂.IsValid, Set.mem_Icc] at hτ'
    obtain ⟨⟨hu0, -⟩, -, -⟩ := hτ' 0
    obtain ⟨⟨hu2, -⟩, -, -⟩ := hτ' 2
    have p₁ : 0 ≤ 2 * x 0 * (v 1 + v 2 - 1) :=
      mul_nonneg (mul_nonneg zero_le_two hx0) (sub_nonneg.mpr c₃)
    have p₂ : 0 ≤ (1 - x 0) * y 0 * u 2 :=
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hx0') hy0) hu2
    have p₃ : 0 ≤ x 1 * (2 * v 2 - 1 - u 0 - v 0) :=
      mul_nonneg hx1 (by linarith only [c₄])
    have p₄ : 0 ≤ (1 - x 1) * y 1 * (u 2 - 2 * u 0) :=
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hx1') hy1) (sub_nonneg.mpr c₁)
    have p₅ : 0 ≤ x 2 * (u 0 - v 0 - v 1) :=
      mul_nonneg hx2 (by linarith only [c₂])
    have p₆ : 0 ≤ 2 * (1 - x 2) * (1 - y 2) * u 0 :=
      mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (sub_nonneg.mpr hx2'))
        (sub_nonneg.mpr hy2')) hu0
    have hp : 0 ≤ a *
        (2 * x 0 * (v 1 + v 2 - 1) + (1 - x 0) * y 0 * u 2
          + x 1 * (2 * v 2 - 1 - u 0 - v 0)
          + (1 - x 1) * y 1 * (u 2 - 2 * u 0)
          + x 2 * (u 0 - v 0 - v 1) + 2 * (1 - x 2) * (1 - y 2) * u 0) :=
      mul_nonneg ha.le (by linarith only [p₁, p₂, p₃, p₄, p₅, p₆])
    linarith only [hc, hp]

end KuhnPoker
