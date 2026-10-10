module

public import KuhnPoker.Defs
public import KuhnPoker.Payoff

/-!
# Kuhn's game: the value −1/18, the equilibria, and the two optimal sets

The payoff of Kuhn's game (`a = b = 1`) is an explicit polynomial in the twelve probabilities
(`co_payoff_poly`). Against II's strategy `kuhnII`, I's deficit `−1/18 − payoff` is
`(1 − σ.1 0)·σ.2 0/6 + σ.1 1/18 + (1 − σ.1 2)(1 − σ.2 2)/6` (`upper_certificate_internal`, `co_upper`).
Against any valid `τ`, Kuhn's family `kuhnI α k` earns `−1/18` plus
`(α/2)·τ.2 0 + (α/2)(1 − τ.2 2) + ((1/3 − α)/2)·τ.1 1 + (1/18 + α/6)(1 − τ.1 2)`
`− (1 − 3α)(1 − k)(τ.1 0 + τ.1 1)/2`, whose last term vanishes when `3α = 1` or `k = 1`
(`lower_certificate_internal`, `co_lower`). Three pure strategies of I force every coordinate of an optimal `τ`
(`co_II_unique`); three pure strategies of II force an optimal `σ` onto the family (`co_I_family`).
The equilibria are exactly the pairs (a family member, `kuhnII`) (`isEquilibrium_iff_explicit_internal`).
-/

@[expose] public section

namespace KuhnPoker

/-- The payoff of Kuhn's game as a polynomial in the twelve probabilities. -/
theorem co_payoff_poly (σ : Strategy₁) (τ : Strategy₂) :
    payoff 1 1 σ τ =
      σ.1 0 * σ.2 0 * τ.1 1 / 6 + σ.1 0 * σ.2 0 * τ.1 2 / 6 - σ.1 0 * τ.2 1 / 2 - σ.1 0 * τ.2 2 / 2
      + 2 * σ.1 0 / 3 - σ.2 0 * τ.1 1 / 6 - σ.2 0 * τ.1 2 / 6
      - σ.1 1 * σ.2 1 * τ.1 0 / 2 + σ.1 1 * σ.2 1 * τ.1 2 / 6 + σ.1 1 * τ.1 0 / 3 + σ.1 1 * τ.2 0 / 6
      - σ.1 1 * τ.2 2 / 2 + σ.1 1 / 3 + σ.2 1 * τ.1 0 / 2 - σ.2 1 * τ.1 2 / 6
      - σ.1 2 * σ.2 2 * τ.1 0 / 2 - σ.1 2 * σ.2 2 * τ.1 1 / 2 + σ.1 2 * τ.1 0 / 3 + σ.1 2 * τ.1 1 / 3
      + σ.1 2 * τ.2 0 / 6 + σ.1 2 * τ.2 1 / 6 + σ.2 2 * τ.1 0 / 2 + σ.2 2 * τ.1 1 / 2
      - 2 * τ.1 0 / 3 - τ.1 1 / 3 := by
  rw [payoff_eq_sum]
  simp only [dealPayoff, toHigher, Fin.isValue, Fin.reduceLT, ↓reduceIte]
  ring

/-- The box constraints of a valid strategy of I at one card. -/
theorem co_box₁ {σ : Strategy₁} (hσ : σ.IsValid) (c : Fin 3) :
    0 ≤ σ.1 c ∧ σ.1 c ≤ 1 ∧ 0 ≤ σ.2 c ∧ σ.2 c ≤ 1 :=
  ⟨(hσ c).1.1, (hσ c).1.2, (hσ c).2.1, (hσ c).2.2⟩

/-- The box constraints of a valid strategy of II at one card. -/
theorem co_box₂ {τ : Strategy₂} (hτ : τ.IsValid) (c : Fin 3) :
    0 ≤ τ.1 c ∧ τ.1 c ≤ 1 ∧ 0 ≤ τ.2 c ∧ τ.2 c ≤ 1 :=
  ⟨(hτ c).1.1, (hτ c).1.2, (hτ c).2.1, (hτ c).2.2⟩

/-- Kuhn's strategy for II is valid. -/
theorem co_valid_kuhnII : kuhnII.IsValid := by
  intro c
  fin_cases c <;>
    simp only [kuhnII, Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val,
      Set.mem_Icc] <;> norm_num

/-- Kuhn's strategies for I are valid for `α ∈ [0, 1/3]`, `k ∈ [0, 1]`. -/
theorem co_valid_kuhnI (α k : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 3) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) :
    (kuhnI α k).IsValid := by
  intro c
  fin_cases c <;>
    simp only [kuhnI, Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val,
      Set.mem_Icc] <;>
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- The certificate for II: against `kuhnII`, I's deficit from `−1/18` is a sum of three products of
probabilities and complements (an identity, for every `σ`). -/
theorem upper_certificate_internal (σ : Strategy₁) :
    -1 / 18 - payoff 1 1 σ kuhnII =
      (1 - σ.1 0) * σ.2 0 / 6 + σ.1 1 / 18 + (1 - σ.1 2) * (1 - σ.2 2) / 6 := by
  rw [co_payoff_poly]
  simp only [kuhnII, Matrix.cons_val]
  ring

/-- II's strategy `kuhnII` holds every valid strategy of I to at most `−1/18`. -/
theorem co_upper (σ : Strategy₁) (hσ : σ.IsValid) : payoff 1 1 σ kuhnII ≤ -1 / 18 := by
  obtain ⟨-, b0', k0, -⟩ := co_box₁ hσ 0
  obtain ⟨b1, -, -, -⟩ := co_box₁ hσ 1
  obtain ⟨-, b2', -, k2'⟩ := co_box₁ hσ 2
  linarith [upper_certificate_internal σ, mul_nonneg (sub_nonneg.2 b0') k0,
    mul_nonneg (sub_nonneg.2 b2') (sub_nonneg.2 k2')]

/-- The certificate for I: against any `τ`, Kuhn's `kuhnI α k` earns `−1/18` plus four products of
probabilities and complements, less a term carrying the factor `(1 − 3α)(1 − k)` (an identity). -/
theorem lower_certificate_internal (α k : ℝ) (τ : Strategy₂) :
    payoff 1 1 (kuhnI α k) τ + 1 / 18 =
      α / 2 * τ.2 0 + α / 2 * (1 - τ.2 2) + (1 / 3 - α) / 2 * τ.1 1 + (1 / 18 + α / 6) * (1 - τ.1 2)
      - (1 - 3 * α) * (1 - k) * (τ.1 0 + τ.1 1) / 2 := by
  rw [co_payoff_poly]
  simp only [kuhnI, Matrix.cons_val]
  ring

/-- Kuhn's family earns at least `−1/18` against every valid strategy of II. -/
theorem co_lower (α k : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 3) (hor : 3 * α = 1 ∨ k = 1)
    (τ : Strategy₂) (hτ : τ.IsValid) : -1 / 18 ≤ payoff 1 1 (kuhnI α k) τ := by
  obtain ⟨-, -, u0, -⟩ := co_box₂ hτ 0
  obtain ⟨t1, -, -, -⟩ := co_box₂ hτ 1
  obtain ⟨-, t2', -, u2'⟩ := co_box₂ hτ 2
  have hz : (1 - 3 * α) * (1 - k) = 0 := by
    rcases hor with h | h
    · rw [show 1 - 3 * α = 0 by linarith, zero_mul]
    · rw [h, sub_self, mul_zero]
  have hid := lower_certificate_internal α k τ
  rw [hz, zero_mul, zero_div, sub_zero] at hid
  linarith [mul_nonneg hα0 u0, mul_nonneg hα0 (sub_nonneg.2 u2'), mul_nonneg (sub_nonneg.2 hα1) t1,
    mul_nonneg (show (0 : ℝ) ≤ 1 / 18 + α / 6 by linarith) (sub_nonneg.2 t2')]

/-- An optimal strategy of II is `kuhnII`: three pure strategies of I force all six coordinates. -/
theorem co_II_unique (τ : Strategy₂) (h : Guarantees₂ 1 1 τ (-1 / 18)) : τ = kuhnII := by
  obtain ⟨hτ, hg⟩ := h
  have hA := hg (![1, 0, 0], ![0, 0, 1]) (by
    intro c
    fin_cases c <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val, Set.mem_Icc] <;>
      norm_num)
  have hB := hg (![0, 0, 0], ![0, 1, 1]) (by
    intro c
    fin_cases c <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val, Set.mem_Icc] <;>
      norm_num)
  have hC := hg (![0, 0, 1], ![0, 0, 0]) (by
    intro c
    fin_cases c <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val, Set.mem_Icc] <;>
      norm_num)
  rw [co_payoff_poly] at hA hB hC
  simp only [Matrix.cons_val] at hA hB hC
  obtain ⟨t0, t0', u0, u0'⟩ := co_box₂ hτ 0
  obtain ⟨t1, t1', u1, u1'⟩ := co_box₂ hτ 1
  obtain ⟨t2, t2', u2, u2'⟩ := co_box₂ hτ 2
  have e0 : τ.1 0 = 1 / 3 := by linarith
  have e1 : τ.1 1 = 0 := by linarith
  have e2 : τ.1 2 = 1 := by linarith
  have f0 : τ.2 0 = 0 := by linarith
  have f1 : τ.2 1 = 1 / 3 := by linarith
  have f2 : τ.2 2 = 1 := by linarith
  refine Prod.ext (funext fun c => ?_) (funext fun c => ?_) <;> fin_cases c <;>
    simp only [kuhnII, Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val] <;>
    assumption

/-- An optimal strategy of I lies in Kuhn's family: three pure strategies of II force it. -/
theorem co_I_family (σ : Strategy₁) (h : Guarantees₁ 1 1 σ (-1 / 18)) :
    ∃ α ∈ Set.Icc (0 : ℝ) (1 / 3), ∃ k ∈ Set.Icc (0 : ℝ) 1, (3 * α = 1 ∨ k = 1) ∧ σ = kuhnI α k := by
  obtain ⟨hσ, hg⟩ := h
  have h1 := hg (![0, 0, 1], ![0, 0, 1]) (by
    intro c
    fin_cases c <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val, Set.mem_Icc] <;>
      norm_num)
  have h2 := hg (![1, 0, 1], ![0, 0, 1]) (by
    intro c
    fin_cases c <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val, Set.mem_Icc] <;>
      norm_num)
  have h3 := hg (![0, 0, 1], ![0, 1, 1]) (by
    intro c
    fin_cases c <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val, Set.mem_Icc] <;>
      norm_num)
  rw [co_payoff_poly] at h1 h2 h3
  simp only [Matrix.cons_val] at h1 h2 h3
  obtain ⟨b0, b0', k0, k0'⟩ := co_box₁ hσ 0
  obtain ⟨b1, b1', k1, k1'⟩ := co_box₁ hσ 1
  obtain ⟨b2, b2', k2, k2'⟩ := co_box₁ hσ 2
  have m0 := mul_nonneg (sub_nonneg.2 b0') k0
  have m1 := mul_nonneg (sub_nonneg.2 b1') k1
  have m2 := mul_nonneg (sub_nonneg.2 b2') k2
  have n0 := mul_nonneg (sub_nonneg.2 b0') (sub_nonneg.2 k0')
  have n1 := mul_nonneg (sub_nonneg.2 b1') (sub_nonneg.2 k1')
  have n2 := mul_nonneg (sub_nonneg.2 b2') (sub_nonneg.2 k2')
  have e1 : σ.1 1 = 0 := by linarith
  have e2 : σ.1 2 = 3 * σ.1 0 := by linarith
  have e3 : σ.1 0 ≤ 1 / 3 := by linarith
  have e4 : (1 - σ.1 0) * σ.2 0 = 0 := by linarith
  have e5 : (1 - σ.1 1) * σ.2 1 = σ.1 0 + 1 / 3 := by linarith
  have e6 : (1 - σ.1 2) * (1 - σ.2 2) = 0 := by linarith
  have f0 : σ.2 0 = 0 := by
    rcases mul_eq_zero.1 e4 with h | h
    · linarith
    · exact h
  have f1 : σ.2 1 = σ.1 0 + 1 / 3 := by
    rw [e1] at e5
    linarith
  have hor : 3 * σ.1 0 = 1 ∨ σ.2 2 = 1 := by
    rcases mul_eq_zero.1 e6 with h | h
    · left
      linarith
    · right
      linarith
  refine ⟨σ.1 0, ⟨b0, e3⟩, σ.2 2, ⟨k2, k2'⟩, hor, ?_⟩
  refine Prod.ext (funext fun c => ?_) (funext fun c => ?_) <;> fin_cases c <;>
    simp only [kuhnI, Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Matrix.cons_val] <;>
    assumption

/-- Both players guaranteeing the same `v` makes an equilibrium (any ante and bet). -/
theorem co_isEquilibrium_of {a b v : ℝ} {σ : Strategy₁} {τ : Strategy₂} (h1 : Guarantees₁ a b σ v)
    (h2 : Guarantees₂ a b τ v) : IsEquilibrium a b σ τ := by
  have hv : payoff a b σ τ = v := le_antisymm (h2.2 σ h1.1) (h1.2 τ h2.1)
  refine ⟨h1.1, h2.1, fun σ' hσ' => ?_, fun τ' hτ' => ?_⟩
  · rw [hv]
    exact h2.2 σ' hσ'
  · rw [hv]
    exact h1.2 τ' hτ'

/-- `kuhnI 0 1` guarantees `−1/18`. -/
theorem co_guarantees_kuhnI_zero_one : Guarantees₁ 1 1 (kuhnI 0 1) (-1 / 18) :=
  ⟨co_valid_kuhnI 0 1 le_rfl (by norm_num) zero_le_one le_rfl,
    fun τ hτ => co_lower 0 1 le_rfl (by norm_num) (Or.inr rfl) τ hτ⟩

/-- `kuhnII` guarantees `−1/18`. -/
theorem co_guarantees_kuhnII : Guarantees₂ 1 1 kuhnII (-1 / 18) :=
  ⟨co_valid_kuhnII, co_upper⟩

/-- Kuhn's game has value `−1/18`. -/
theorem hasValue_one_one_internal : HasValue 1 1 (-1 / 18) :=
  ⟨⟨kuhnI 0 1, co_guarantees_kuhnI_zero_one⟩, ⟨kuhnII, co_guarantees_kuhnII⟩⟩

/-- A game has at most one value. -/
theorem hasValue_unique_internal (a b v w : ℝ) (hv : HasValue a b v) (hw : HasValue a b w) : v = w := by
  obtain ⟨⟨σ, hσ⟩, ⟨τ, hτ⟩⟩ := hv
  obtain ⟨⟨σ', hσ'⟩, ⟨τ', hτ'⟩⟩ := hw
  exact le_antisymm ((hσ.2 τ' hτ'.1).trans (hτ'.2 σ hσ.1)) ((hσ'.2 τ hτ.1).trans (hτ.2 σ' hσ'.1))

/-- An equilibrium exists. -/
theorem exists_isEquilibrium_internal : ∃ σ τ, IsEquilibrium 1 1 σ τ :=
  ⟨kuhnI 0 1, kuhnII, co_isEquilibrium_of co_guarantees_kuhnI_zero_one co_guarantees_kuhnII⟩

/-- Every equilibrium pays I exactly `−1/18`. -/
theorem payoff_of_isEquilibrium_internal (σ : Strategy₁) (τ : Strategy₂) (h : IsEquilibrium 1 1 σ τ) :
    payoff 1 1 σ τ = -1 / 18 := by
  obtain ⟨hσ, hτ, h1, h2⟩ := h
  exact le_antisymm ((h2 kuhnII co_valid_kuhnII).trans (co_upper σ hσ))
    ((co_guarantees_kuhnI_zero_one.2 τ hτ).trans (h1 _ co_guarantees_kuhnI_zero_one.1))

/-- A pair is an equilibrium iff each strategy guarantees the value. -/
theorem isEquilibrium_iff_internal (σ : Strategy₁) (τ : Strategy₂) :
    IsEquilibrium 1 1 σ τ ↔ Guarantees₁ 1 1 σ (-1 / 18) ∧ Guarantees₂ 1 1 τ (-1 / 18) := by
  constructor
  · intro h
    have hv := payoff_of_isEquilibrium_internal σ τ h
    obtain ⟨hσ, hτ, h1, h2⟩ := h
    exact ⟨⟨hσ, fun τ' hτ' => hv ▸ h2 τ' hτ'⟩, ⟨hτ, fun σ' hσ' => hv ▸ h1 σ' hσ'⟩⟩
  · rintro ⟨h1, h2⟩
    exact co_isEquilibrium_of h1 h2

/-- Player II's optimal strategy is unique. -/
theorem guarantees₂_iff_internal (τ : Strategy₂) : Guarantees₂ 1 1 τ (-1 / 18) ↔ τ = kuhnII := by
  constructor
  · exact co_II_unique τ
  · rintro rfl
    exact co_guarantees_kuhnII

/-- Player I's optimal strategies are exactly Kuhn's family. -/
theorem guarantees₁_iff_internal (σ : Strategy₁) : Guarantees₁ 1 1 σ (-1 / 18) ↔
    ∃ α ∈ Set.Icc (0 : ℝ) (1 / 3), ∃ k ∈ Set.Icc (0 : ℝ) 1, (3 * α = 1 ∨ k = 1) ∧ σ = kuhnI α k := by
  constructor
  · exact co_I_family σ
  · rintro ⟨α, ⟨hα0, hα1⟩, k, ⟨hk0, hk1⟩, hor, rfl⟩
    exact ⟨co_valid_kuhnI α k hα0 hα1 hk0 hk1, fun τ hτ => co_lower α k hα0 hα1 hor τ hτ⟩

/-- The equilibria of Kuhn's game, explicitly: II plays `kuhnII` and I plays a member of Kuhn's family. -/
theorem isEquilibrium_iff_explicit_internal (σ : Strategy₁) (τ : Strategy₂) :
    IsEquilibrium 1 1 σ τ ↔
      (∃ α ∈ Set.Icc (0 : ℝ) (1 / 3), ∃ k ∈ Set.Icc (0 : ℝ) 1, (3 * α = 1 ∨ k = 1) ∧ σ = kuhnI α k) ∧
        τ = kuhnII := by
  rw [isEquilibrium_iff_internal, guarantees₁_iff_internal, guarantees₂_iff_internal]

end KuhnPoker
