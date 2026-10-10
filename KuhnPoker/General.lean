module

public import KuhnPoker.Defs
public import KuhnPoker.Payoff

/-!
# The value at every ante and bet

For an ante `a > 0` and a bet `b > 0`, with `d = 2a + b`, the strategies of Kuhn's pp. 102–103 guarantee
`kuhnValue a b` in each of the three regions `b ≤ a`, `a ≤ b ≤ 2a`, `2a ≤ b`. Each guarantee is a finite
nonnegative-product identity: after unfolding the payoff through `payoff_eq_sum` and multiplying by `6d`, the
difference between the payoff and the value is a sum of products of the case factors (`a`, `b`, `d`, `a − b`,
`4a − b`, `b − 2a`, and in Case 3 `dη − (2a − b)` and `b − dη`) with the opponent's probabilities and their
complements; the witness's coordinates `n/d` are eliminated by the relations `d · (n/d) = n`, each multiplied by
an explicit polynomial.
-/

@[expose] public section

namespace KuhnPoker

/-! ### The value in each region -/

theorem gn_value_case_one {a b : ℝ} (hab : b ≤ a) :
    kuhnValue a b = -(b ^ 2) / (6 * (2 * a + b)) := by
  simp only [kuhnValue, hab, ↓reduceIte]

theorem gn_value_case_three {a b : ℝ} (hab : a ≤ b) (hb2 : b ≤ 2 * a) :
    kuhnValue a b = -(b * (2 * a - b)) / (6 * (2 * a + b)) := by
  unfold kuhnValue
  split_ifs with h1
  · have h : b = a := le_antisymm h1 hab
    subst h
    ring
  · rfl

theorem gn_value_case_four {a b : ℝ} (ha : 0 < a) (hab : 2 * a ≤ b) : kuhnValue a b = 0 := by
  unfold kuhnValue
  split_ifs with h1 h2
  · exfalso
    linarith
  · have h : b = 2 * a := le_antisymm h2 hab
    rw [h]
    ring
  · rfl

/-! ### Validity of the witnesses -/

theorem gn_frac_mem {n d : ℝ} (hn : 0 ≤ n) (hnd : n ≤ d) (hd : 0 < d) : n / d ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨div_nonneg hn hd.le, (div_le_one hd).mpr hnd⟩

theorem gn_zero_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩

theorem gn_one_mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩

theorem gn_isValid₁ {p₀ p₁ p₂ q₀ q₁ q₂ : ℝ} (h₀ : p₀ ∈ Set.Icc (0 : ℝ) 1) (h₁ : p₁ ∈ Set.Icc (0 : ℝ) 1)
    (h₂ : p₂ ∈ Set.Icc (0 : ℝ) 1) (k₀ : q₀ ∈ Set.Icc (0 : ℝ) 1) (k₁ : q₁ ∈ Set.Icc (0 : ℝ) 1)
    (k₂ : q₂ ∈ Set.Icc (0 : ℝ) 1) : Strategy₁.IsValid (![p₀, p₁, p₂], ![q₀, q₁, q₂]) := by
  intro c
  fin_cases c
  · exact ⟨h₀, k₀⟩
  · exact ⟨h₁, k₁⟩
  · exact ⟨h₂, k₂⟩

theorem gn_isValid₂ {p₀ p₁ p₂ q₀ q₁ q₂ : ℝ} (h₀ : p₀ ∈ Set.Icc (0 : ℝ) 1) (h₁ : p₁ ∈ Set.Icc (0 : ℝ) 1)
    (h₂ : p₂ ∈ Set.Icc (0 : ℝ) 1) (k₀ : q₀ ∈ Set.Icc (0 : ℝ) 1) (k₁ : q₁ ∈ Set.Icc (0 : ℝ) 1)
    (k₂ : q₂ ∈ Set.Icc (0 : ℝ) 1) : Strategy₂.IsValid (![p₀, p₁, p₂], ![q₀, q₁, q₂]) := by
  intro c
  fin_cases c
  · exact ⟨h₀, k₀⟩
  · exact ⟨h₁, k₁⟩
  · exact ⟨h₂, k₂⟩

/-! ### Case 4, `2a ≤ b`: the value `0` -/

theorem gn_case_four_I (a b : ℝ) (hb : 0 < b) (hab : 2 * a ≤ b) (u v : Fin 3 → ℝ)
    (hu : ∀ c, u c ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ payoff a b (![0, 0, 0], ![0, 0, 1]) (u, v) := by
  obtain ⟨hu0, hu0'⟩ := hu 0
  obtain ⟨hu1, hu1'⟩ := hu 1
  rw [payoff_eq_sum]
  simp only [dealPayoff, toHigher, Matrix.cons_val, Fin.reduceLT, ↓reduceIte]
  linarith [mul_nonneg (sub_nonneg.mpr hab) hu0, mul_nonneg hb.le hu1]

theorem gn_case_four_II (a b : ℝ) (hb : 0 < b) (hab : 2 * a ≤ b) (x y : Fin 3 → ℝ)
    (hx : ∀ c, x c ∈ Set.Icc (0 : ℝ) 1) (hy : ∀ c, y c ∈ Set.Icc (0 : ℝ) 1) :
    payoff a b (x, y) (![0, 0, 1], ![0, 0, 1]) ≤ 0 := by
  obtain ⟨hx0, hx0'⟩ := hx 0
  obtain ⟨hx1, hx1'⟩ := hx 1
  obtain ⟨hy0, hy0'⟩ := hy 0
  obtain ⟨hy1, hy1'⟩ := hy 1
  rw [payoff_eq_sum]
  simp only [dealPayoff, toHigher, Matrix.cons_val, Fin.reduceLT, ↓reduceIte]
  linarith [mul_nonneg hx0 (sub_nonneg.mpr hab), mul_nonneg (mul_nonneg (sub_nonneg.mpr hx0') hy0) hb.le,
    mul_nonneg hx1 hb.le, mul_nonneg (mul_nonneg (sub_nonneg.mpr hx1') hy1) hb.le]

/-! ### Case 1, `b ≤ a`: the value `−b²/(6d)` -/

theorem gn_case_one_I (a b k : ℝ) (ha : 0 < a) (hb : 0 < b) (u v : Fin 3 → ℝ)
    (hu : ∀ c, u c ∈ Set.Icc (0 : ℝ) 1) (hv : ∀ c, v c ∈ Set.Icc (0 : ℝ) 1) :
    -(b ^ 2) / (6 * (2 * a + b)) ≤
      payoff a b (![b / (2 * a + b), 0, 1], ![0, 2 * a / (2 * a + b), k]) (u, v) := by
  have hd : 0 < 2 * a + b := by positivity
  obtain ⟨hu2, hu2'⟩ := hu 2
  obtain ⟨hv0, hv0'⟩ := hv 0
  obtain ⟨hv2, hv2'⟩ := hv 2
  have hp : (2 * a + b) * (b / (2 * a + b)) = b := mul_div_cancel₀ b hd.ne'
  have hr : (2 * a + b) * (2 * a / (2 * a + b)) = 2 * a := mul_div_cancel₀ (2 * a) hd.ne'
  generalize b / (2 * a + b) = p at hp ⊢
  generalize 2 * a / (2 * a + b) = r at hr ⊢
  rw [div_le_iff₀ (by positivity), payoff_eq_sum]
  simp only [dealPayoff, toHigher, Matrix.cons_val, Fin.reduceLT, ↓reduceIte]
  have e₁ : (-2 * (v 1) * a - (v 1) * b - 2 * (v 2) * a - (v 2) * b + 4 * a) *
      ((2 * a + b) * p - b) = 0 := by rw [hp, sub_self, mul_zero]
  have e₂ : (2 * (u 0) * a + (u 0) * b - (u 2) * b) * ((2 * a + b) * r - 2 * a) = 0 := by
    rw [hr, sub_self, mul_zero]
  linarith [mul_nonneg (mul_nonneg hb.le hd.le) hv0,
    mul_nonneg (mul_nonneg (mul_nonneg ha.le hb.le) (sub_nonneg.mpr hu2')) zero_le_two,
    mul_nonneg (mul_nonneg hb.le hd.le) (sub_nonneg.mpr hv2')]

theorem gn_case_one_II (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (x y : Fin 3 → ℝ)
    (hx : ∀ c, x c ∈ Set.Icc (0 : ℝ) 1) (hy : ∀ c, y c ∈ Set.Icc (0 : ℝ) 1) :
    payoff a b (x, y) (![b / (2 * a + b), 0, 1], ![0, (2 * a - b) / (2 * a + b), 1]) ≤
      -(b ^ 2) / (6 * (2 * a + b)) := by
  have hd : 0 < 2 * a + b := by positivity
  obtain ⟨hx0, hx0'⟩ := hx 0
  obtain ⟨hx1, hx1'⟩ := hx 1
  obtain ⟨hx2, hx2'⟩ := hx 2
  obtain ⟨hy0, hy0'⟩ := hy 0
  obtain ⟨hy2, hy2'⟩ := hy 2
  have hp : (2 * a + b) * (b / (2 * a + b)) = b := mul_div_cancel₀ b hd.ne'
  have hq : (2 * a + b) * ((2 * a - b) / (2 * a + b)) = 2 * a - b := mul_div_cancel₀ (2 * a - b) hd.ne'
  generalize b / (2 * a + b) = p at hp ⊢
  generalize (2 * a - b) / (2 * a + b) = q at hq ⊢
  rw [le_div_iff₀ (by positivity), payoff_eq_sum]
  simp only [dealPayoff, toHigher, Matrix.cons_val, Fin.reduceLT, ↓reduceIte]
  have e₁ : (2 * (x 1) * (y 1) * a + (x 1) * (y 1) * b - 2 * (x 1) * a + 2 * (x 2) * (y 2) * a
      + (x 2) * (y 2) * b - 2 * (x 2) * a - 2 * (y 1) * a - (y 1) * b - 2 * (y 2) * a - (y 2) * b + 4 * a) *
      ((2 * a + b) * p - b) = 0 := by rw [hp, sub_self, mul_zero]
  have e₂ : (2 * (x 0) * a + (x 0) * b - (x 2) * b) * ((2 * a + b) * q - (2 * a - b)) = 0 := by
    rw [hq, sub_self, mul_zero]
  linarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hx0') hy0) (mul_nonneg hb.le hd.le),
    mul_nonneg hx1 (mul_nonneg hb.le hb.le),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hx2') (sub_nonneg.mpr hy2'))
      (mul_nonneg hb.le (by linarith : (0 : ℝ) ≤ 4 * a - b)),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hx2') hy2) (mul_nonneg hb.le (sub_nonneg.mpr hab))]

/-! ### Case 3, `a ≤ b ≤ 2a`: the value `−b(2a − b)/(6d)` -/

theorem gn_case_three_I (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hb2 : b ≤ 2 * a)
    (u v : Fin 3 → ℝ) (hu : ∀ c, u c ∈ Set.Icc (0 : ℝ) 1) :
    -(b * (2 * a - b)) / (6 * (2 * a + b)) ≤
      payoff a b (![0, 0, 0], ![0, (2 * a - b) / (2 * a + b), 1]) (u, v) := by
  have hd : 0 < 2 * a + b := by positivity
  obtain ⟨hu1, hu1'⟩ := hu 1
  obtain ⟨hu2, hu2'⟩ := hu 2
  have hq : (2 * a + b) * ((2 * a - b) / (2 * a + b)) = 2 * a - b := mul_div_cancel₀ (2 * a - b) hd.ne'
  generalize (2 * a - b) / (2 * a + b) = q at hq ⊢
  rw [div_le_iff₀ (by positivity), payoff_eq_sum]
  simp only [dealPayoff, toHigher, Matrix.cons_val, Fin.reduceLT, ↓reduceIte]
  have e₁ : (2 * (u 0) * a + (u 0) * b - (u 2) * b) * ((2 * a + b) * q - (2 * a - b)) = 0 := by
    rw [hq, sub_self, mul_zero]
  linarith [mul_nonneg (mul_nonneg hb.le hd.le) hu1,
    mul_nonneg (mul_nonneg hb.le (sub_nonneg.mpr hb2)) (sub_nonneg.mpr hu2')]

theorem gn_case_three_II (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (η : ℝ) (hη : η ∈ Set.Icc ((2 * a - b) / (2 * a + b)) (b / (2 * a + b))) (x y : Fin 3 → ℝ)
    (hx : ∀ c, x c ∈ Set.Icc (0 : ℝ) 1) (hy : ∀ c, y c ∈ Set.Icc (0 : ℝ) 1) :
    payoff a b (x, y) (![b / (2 * a + b), 0, 1], ![0, η, 1]) ≤
      -(b * (2 * a - b)) / (6 * (2 * a + b)) := by
  have hd : 0 < 2 * a + b := by positivity
  obtain ⟨hη₁, hη₂⟩ := hη
  rw [div_le_iff₀ hd] at hη₁
  rw [le_div_iff₀ hd] at hη₂
  obtain ⟨hx0, hx0'⟩ := hx 0
  obtain ⟨hx1, hx1'⟩ := hx 1
  obtain ⟨hx2, hx2'⟩ := hx 2
  obtain ⟨hy0, hy0'⟩ := hy 0
  obtain ⟨hy2, hy2'⟩ := hy 2
  have hp : (2 * a + b) * (b / (2 * a + b)) = b := mul_div_cancel₀ b hd.ne'
  generalize b / (2 * a + b) = p at hp ⊢
  rw [le_div_iff₀ (by positivity), payoff_eq_sum]
  simp only [dealPayoff, toHigher, Matrix.cons_val, Fin.reduceLT, ↓reduceIte]
  have e₁ : (2 * (x 1) * (y 1) * a + (x 1) * (y 1) * b - 2 * (x 1) * a + 2 * (x 2) * (y 2) * a
      + (x 2) * (y 2) * b - 2 * (x 2) * a - 2 * (y 1) * a - (y 1) * b - 2 * (y 2) * a - (y 2) * b + 4 * a) *
      ((2 * a + b) * p - b) = 0 := by rw [hp, sub_self, mul_zero]
  linarith [mul_nonneg (mul_nonneg hx0 hd.le) (sub_nonneg.mpr hη₁),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hx0') hy0) (mul_nonneg hb.le hd.le),
    mul_nonneg hx1 (mul_nonneg hb.le hb.le),
    mul_nonneg (mul_nonneg hx2 hb.le) (sub_nonneg.mpr hη₂),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hx2') (sub_nonneg.mpr hy2')) (mul_nonneg hb.le hd.le)]

/-! ### The pinned statements -/

theorem kuhnValue_one_one_internal : kuhnValue 1 1 = -1 / 18 := by
  norm_num [kuhnValue]

theorem guarantees_case_one_internal (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) :
    Guarantees₁ a b (![b / (2 * a + b), 0, 1], ![0, 2 * a / (2 * a + b), 1]) (kuhnValue a b) ∧
    Guarantees₂ a b (![b / (2 * a + b), 0, 1], ![0, (2 * a - b) / (2 * a + b), 1]) (kuhnValue a b) := by
  have hd : 0 < 2 * a + b := by positivity
  rw [gn_value_case_one hab]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact gn_isValid₁ (gn_frac_mem hb.le (by linarith) hd) gn_zero_mem gn_one_mem gn_zero_mem
      (gn_frac_mem (by positivity) (by linarith) hd) gn_one_mem
  · rintro ⟨u, v⟩ hτ
    exact gn_case_one_I a b 1 ha hb u v (fun c => (hτ c).1) (fun c => (hτ c).2)
  · exact gn_isValid₂ (gn_frac_mem hb.le (by linarith) hd) gn_zero_mem gn_one_mem gn_zero_mem
      (gn_frac_mem (by linarith) (by linarith) hd) gn_one_mem
  · rintro ⟨x, y⟩ hσ
    exact gn_case_one_II a b ha hb hab x y (fun c => (hσ c).1) (fun c => (hσ c).2)

theorem guarantees_case_three_internal (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (hb2 : b ≤ 2 * a)
    (η : ℝ) (hη : η ∈ Set.Icc ((2 * a - b) / (2 * a + b)) (b / (2 * a + b))) :
    Guarantees₁ a b (![0, 0, 0], ![0, (2 * a - b) / (2 * a + b), 1]) (kuhnValue a b) ∧
    Guarantees₂ a b (![b / (2 * a + b), 0, 1], ![0, η, 1]) (kuhnValue a b) := by
  have hd : 0 < 2 * a + b := by positivity
  rw [gn_value_case_three hab hb2]
  have hη' : η ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨le_trans (div_nonneg (by linarith) hd.le) hη.1, le_trans hη.2 ((div_le_one hd).mpr (by linarith))⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact gn_isValid₁ gn_zero_mem gn_zero_mem gn_zero_mem gn_zero_mem
      (gn_frac_mem (by linarith) (by linarith) hd) gn_one_mem
  · rintro ⟨u, v⟩ hτ
    exact gn_case_three_I a b ha hb hb2 u v (fun c => (hτ c).1)
  · exact gn_isValid₂ (gn_frac_mem hb.le (by linarith) hd) gn_zero_mem gn_one_mem gn_zero_mem hη' gn_one_mem
  · rintro ⟨x, y⟩ hσ
    exact gn_case_three_II a b ha hb η hη x y (fun c => (hσ c).1) (fun c => (hσ c).2)

theorem guarantees_case_four_internal (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 2 * a ≤ b) :
    Guarantees₁ a b (![0, 0, 0], ![0, 0, 1]) 0 ∧ Guarantees₂ a b (![0, 0, 1], ![0, 0, 1]) 0 := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact gn_isValid₁ gn_zero_mem gn_zero_mem gn_zero_mem gn_zero_mem gn_zero_mem gn_one_mem
  · rintro ⟨u, v⟩ hτ
    exact gn_case_four_I a b hb hab u v (fun c => (hτ c).1)
  · exact gn_isValid₂ gn_zero_mem gn_zero_mem gn_one_mem gn_zero_mem gn_zero_mem gn_one_mem
  · rintro ⟨x, y⟩ hσ
    exact gn_case_four_II a b hb hab x y (fun c => (hσ c).1) (fun c => (hσ c).2)

theorem hasValue_general_internal (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : HasValue a b (kuhnValue a b) := by
  have hd : 0 < 2 * a + b := by positivity
  rcases le_or_gt b a with h1 | h1
  · obtain ⟨hI, hII⟩ := guarantees_case_one_internal a b ha hb h1
    exact ⟨⟨_, hI⟩, ⟨_, hII⟩⟩
  rcases le_or_gt b (2 * a) with h2 | h2
  · obtain ⟨hI, hII⟩ := guarantees_case_three_internal a b ha hb h1.le h2 (b / (2 * a + b))
      ⟨div_le_div_of_nonneg_right (by linarith) hd.le, le_rfl⟩
    exact ⟨⟨_, hI⟩, ⟨_, hII⟩⟩
  · rw [gn_value_case_four ha h2.le]
    obtain ⟨hI, hII⟩ := guarantees_case_four_internal a b ha hb h2.le
    exact ⟨⟨_, hI⟩, ⟨_, hII⟩⟩

/-! ### Extensions: the Case 3 interval is sharp -/

/-- The Case 3 certificate as an identity: for every strategy `(x, y)` of I (valid or not), `6d` times the payoff
against II's Case 3 strategy is `−b(2a − b)` minus five products, each nonnegative exactly when `(x, y)` is
valid and `η` lies in the corrected interval. -/
theorem gn_case_three_II_identity (a b η : ℝ) (ha : 0 < a) (hb : 0 < b) (x y : Fin 3 → ℝ) :
    (2 * a + b) * (6 * payoff a b (x, y) (![b / (2 * a + b), 0, 1], ![0, η, 1])) =
      -(b * (2 * a - b)) - (x 0 * (2 * a + b) * ((2 * a + b) * η - (2 * a - b))
        + (1 - x 0) * y 0 * (b * (2 * a + b)) + x 1 * (b * b) + x 2 * b * (b - (2 * a + b) * η)
        + (1 - x 2) * (1 - y 2) * (b * (2 * a + b))) := by
  have hd : 0 < 2 * a + b := by positivity
  have hp : (2 * a + b) * (b / (2 * a + b)) = b := mul_div_cancel₀ b hd.ne'
  generalize b / (2 * a + b) = p at hp ⊢
  rw [payoff_eq_sum]
  simp only [dealPayoff, toHigher, Matrix.cons_val, Fin.reduceLT, ↓reduceIte]
  linear_combination (-(2 * (x 1) * (y 1) * a + (x 1) * (y 1) * b - 2 * (x 1) * a + 2 * (x 2) * (y 2) * a
      + (x 2) * (y 2) * b - 2 * (x 2) * a - 2 * (y 1) * a - (y 1) * b - 2 * (y 2) * a - (y 2) * b + 4 * a)) * hp

/-- The corrected Case 3 interval is sharp: with the other five coordinates of II's strategy as pinned, the
calling probability `η` with the `2` guarantees the value exactly when `(2a − b)/d ≤ η ≤ b/d`. Below the
interval I gains by betting the `1` (bluffing); above it, by betting the `3` first. -/
theorem gn_case_three_II_iff (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (hb2 : b ≤ 2 * a) (η : ℝ) :
    Guarantees₂ a b (![b / (2 * a + b), 0, 1], ![0, η, 1]) (kuhnValue a b) ↔
      η ∈ Set.Icc ((2 * a - b) / (2 * a + b)) (b / (2 * a + b)) := by
  refine ⟨fun h => ?_, fun hη => (guarantees_case_three_internal a b ha hb hab hb2 η hη).2⟩
  have hd : 0 < 2 * a + b := by positivity
  have key : ∀ x y : Fin 3 → ℝ, Strategy₁.IsValid (x, y) →
      (2 * a + b) * (6 * payoff a b (x, y) (![b / (2 * a + b), 0, 1], ![0, η, 1])) ≤ -(b * (2 * a - b)) := by
    intro x y hv
    have h1 := h.2 (x, y) hv
    rw [gn_value_case_three hab hb2, le_div_iff₀ (by positivity)] at h1
    linarith
  have h1 := key ![1, 0, 0] ![0, 0, 1]
    (gn_isValid₁ gn_one_mem gn_zero_mem gn_zero_mem gn_zero_mem gn_zero_mem gn_one_mem)
  have h2 := key ![0, 0, 1] ![0, 0, 0]
    (gn_isValid₁ gn_zero_mem gn_zero_mem gn_one_mem gn_zero_mem gn_zero_mem gn_zero_mem)
  rw [gn_case_three_II_identity a b η ha hb] at h1 h2
  simp only [Matrix.cons_val] at h1 h2
  have k1 : 0 ≤ (2 * a + b) * ((2 * a + b) * η - (2 * a - b)) := by linarith
  have k2 : 0 ≤ b * (b - (2 * a + b) * η) := by linarith
  have k1' := nonneg_of_mul_nonneg_right k1 hd
  have k2' := nonneg_of_mul_nonneg_right k2 hb
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ hd]
    linarith
  · rw [le_div_iff₀ hd]
    linarith

/-- Kuhn's printed Case 3 interval `b/d ≤ η ≤ (a + b)/d` (p. 102) holds only at its lower end: there, and only
there, II's strategy guarantees the value. -/
theorem gn_case_three_printed_interval (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (hb2 : b ≤ 2 * a)
    (η : ℝ) (hη : η ∈ Set.Icc (b / (2 * a + b)) ((a + b) / (2 * a + b))) :
    Guarantees₂ a b (![b / (2 * a + b), 0, 1], ![0, η, 1]) (kuhnValue a b) ↔ η = b / (2 * a + b) := by
  have hd : 0 < 2 * a + b := by positivity
  rw [gn_case_three_II_iff a b ha hb hab hb2 η]
  constructor
  · rintro ⟨-, h2⟩
    exact le_antisymm h2 hη.1
  · rintro rfl
    exact ⟨div_le_div_of_nonneg_right (by linarith) hd.le, le_rfl⟩

/-- At `a = 2`, `b = 3`, Kuhn's printed upper end `η = (a + b)/d = 5/7` does not guarantee the value. -/
theorem gn_case_three_printed_upper_end_fails :
    ¬ Guarantees₂ 2 3 (![3 / (2 * 2 + 3), 0, 1], ![0, 5 / 7, 1]) (kuhnValue 2 3) := by
  rw [gn_case_three_II_iff 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  rintro ⟨-, h⟩
  norm_num at h

/-! ### Extensions: I's optimal strategy off the diagonal `a = b`

At `a = b` (Kuhn's game, scaled) player I has a one-parameter family of optimal strategies. Off the diagonal it
is unique: for `b < a` up to the call with the `3`, an information set I never reaches (Case 1); for
`a < b ≤ 2a` outright (Case 3). Each "only if" uses three or four pure strategies of II and a linear
certificate in the sequence-form atoms `x c`, `(1 − x c) y c`, `(1 − x c)(1 − y c)` with coefficients
polynomial in `a` and `b`. -/

/-- Case 3 off the diagonal, `a < b ≤ 2a`: I's optimal strategy is unique. -/
theorem gn_case_three_I_unique (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hb2 : b ≤ 2 * a)
    (σ : Strategy₁) :
    Guarantees₁ a b σ (kuhnValue a b) ↔ σ = (![0, 0, 0], ![0, (2 * a - b) / (2 * a + b), 1]) := by
  have hd : 0 < 2 * a + b := by positivity
  constructor
  swap
  · rintro rfl
    exact (guarantees_case_three_internal a b ha hb hab.le hb2 (b / (2 * a + b))
      ⟨div_le_div_of_nonneg_right (by linarith) hd.le, le_rfl⟩).1
  rintro ⟨hσ, h⟩
  obtain ⟨x, y⟩ := σ
  simp only [Strategy₁.IsValid, Set.mem_Icc] at hσ
  obtain ⟨⟨hx0, hx0'⟩, hy0, hy0'⟩ := hσ 0
  obtain ⟨⟨hx1, hx1'⟩, hy1, hy1'⟩ := hσ 1
  obtain ⟨⟨hx2, hx2'⟩, hy2, hy2'⟩ := hσ 2
  rw [gn_value_case_three hab.le hb2] at h
  have key : ∀ u v : Fin 3 → ℝ, Strategy₂.IsValid (u, v) →
      0 ≤ (2 * a + b) * (6 * payoff a b (x, y) (u, v)) + b * (2 * a - b) := by
    intro u v hv
    have h1 := h (u, v) hv
    rw [div_le_iff₀ (by positivity)] at h1
    linarith
  have E1 := key ![0, 0, 1] ![0, 0, 1]
    (gn_isValid₂ gn_zero_mem gn_zero_mem gn_one_mem gn_zero_mem gn_zero_mem gn_one_mem)
  have E2 := key ![1, 0, 1] ![0, 0, 1]
    (gn_isValid₂ gn_one_mem gn_zero_mem gn_one_mem gn_zero_mem gn_zero_mem gn_one_mem)
  have E3 := key ![0, 0, 1] ![0, 1, 1]
    (gn_isValid₂ gn_zero_mem gn_zero_mem gn_one_mem gn_zero_mem gn_one_mem gn_one_mem)
  rw [payoff_eq_sum] at E1 E2 E3
  simp only [dealPayoff, toHigher, Matrix.cons_val, Fin.reduceLT, ↓reduceIte] at E1 E2 E3
  have hs0 : 0 ≤ (1 - x 0) * y 0 := mul_nonneg (sub_nonneg.mpr hx0') hy0
  have hf2 : 0 ≤ (1 - x 2) * (1 - y 2) := mul_nonneg (sub_nonneg.mpr hx2') (sub_nonneg.mpr hy2')
  have H3 : 0 ≤ (2 * a - b) + (2 * a + b) * (x 2 - 2 * x 0 - x 1 - (1 - x 0) * y 0 - (1 - x 1) * y 1) := by
    have h' : 0 ≤ b * ((2 * a - b) + (2 * a + b) * (x 2 - 2 * x 0 - x 1 - (1 - x 0) * y 0
        - (1 - x 1) * y 1)) := by linarith
    exact nonneg_of_mul_nonneg_right h' hb
  have HI : 0 ≤ -((2 * a + b) * x 0 + b * x 1 + (2 * a + b) * ((1 - x 0) * y 0) - (2 * a - b) * x 2
      + (2 * a + b) * ((1 - x 2) * (1 - y 2))) := by
    have h' : 0 ≤ (2 * a + b) * -((2 * a + b) * x 0 + b * x 1 + (2 * a + b) * ((1 - x 0) * y 0)
        - (2 * a - b) * x 2 + (2 * a + b) * ((1 - x 2) * (1 - y 2))) := by
      linarith [mul_nonneg ha.le H3]
    exact nonneg_of_mul_nonneg_right h' hd
  have HII : 0 ≤ -(-(2 * a - b) * (2 * a + b) * x 0 + b * b * x 1 + b * (2 * a + b) * ((1 - x 0) * y 0)
      + b * b * x 2 + b * (2 * a + b) * ((1 - x 2) * (1 - y 2))) := by
    have h' : 0 ≤ (2 * a + b) * -(-(2 * a - b) * (2 * a + b) * x 0 + b * b * x 1
        + b * (2 * a + b) * ((1 - x 0) * y 0) + b * b * x 2 + b * (2 * a + b) * ((1 - x 2) * (1 - y 2))) := by
      linarith [mul_nonneg ha.le E1, mul_nonneg hb.le E2]
    exact nonneg_of_mul_nonneg_right h' hd
  have hT := mul_nonneg (sub_nonneg.mpr hb2) HI
  have p1 : 0 ≤ a * b * x 1 := mul_nonneg (mul_nonneg ha.le hb.le) hx1
  have p2 : 0 ≤ a * (2 * a + b) * ((1 - x 0) * y 0) := mul_nonneg (mul_nonneg ha.le hd.le) hs0
  have p3 : 0 ≤ a * (b - a) * x 2 := mul_nonneg (mul_nonneg ha.le (sub_nonneg.mpr hab.le)) hx2
  have p4 : 0 ≤ a * (2 * a + b) * ((1 - x 2) * (1 - y 2)) := mul_nonneg (mul_nonneg ha.le hd.le) hf2
  have z1 : x 1 = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right (by linarith) (mul_pos ha hb)) hx1
  have zs0 : (1 - x 0) * y 0 = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right (by linarith) (mul_pos ha hd)) hs0
  have z2 : x 2 = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right (by linarith) (mul_pos ha (sub_pos.mpr hab))) hx2
  have zf2 : (1 - x 2) * (1 - y 2) = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right (by linarith) (mul_pos ha hd)) hf2
  have z0 : x 0 = 0 := by
    have e0 : b * x 1 = 0 := by rw [z1, mul_zero]
    have e1 : (2 * a + b) * ((1 - x 0) * y 0) = 0 := by rw [zs0, mul_zero]
    have e2 : (2 * a - b) * x 2 = 0 := by rw [z2, mul_zero]
    have e3 : (2 * a + b) * ((1 - x 2) * (1 - y 2)) = 0 := by rw [zf2, mul_zero]
    have h' : (2 * a + b) * x 0 ≤ 0 := by linarith
    exact le_antisymm (nonpos_of_mul_nonpos_right h' hd) hx0
  have zy0 : y 0 = 0 := by
    rw [z0, sub_zero, one_mul] at zs0
    exact zs0
  have zy2 : y 2 = 1 := by
    rw [z2, sub_zero, one_mul, sub_eq_zero] at zf2
    exact zf2.symm
  have zy1 : y 1 = (2 * a - b) / (2 * a + b) := by
    rw [eq_div_iff hd.ne']
    simp only [z0, z1, z2, zy0, zy2] at E2
    simp only [z0, z1, z2, zy0] at H3
    have h' : 0 ≤ a * (y 1 * (2 * a + b) - (2 * a - b)) := by linarith
    have h'' := nonneg_of_mul_nonneg_right h' ha
    linarith
  refine Prod.ext (funext fun c => ?_) (funext fun c => ?_) <;> fin_cases c <;>
    simp [z0, z1, z2, zy0, zy1, zy2]

/-- Case 1 off the diagonal, `b < a`: I's optimal strategy is unique up to the call with the `3`, which is
never reached (I always bets the `3`). -/
theorem gn_case_one_I_unique (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b < a) (σ : Strategy₁) :
    Guarantees₁ a b σ (kuhnValue a b) ↔
      ∃ k ∈ Set.Icc (0 : ℝ) 1, σ = (![b / (2 * a + b), 0, 1], ![0, 2 * a / (2 * a + b), k]) := by
  have hd : 0 < 2 * a + b := by positivity
  constructor
  swap
  · rintro ⟨k, hk, rfl⟩
    rw [gn_value_case_one hab.le]
    refine ⟨gn_isValid₁ (gn_frac_mem hb.le (by linarith) hd) gn_zero_mem gn_one_mem gn_zero_mem
      (gn_frac_mem (by positivity) (by linarith) hd) hk, ?_⟩
    rintro ⟨u, v⟩ hτ
    exact gn_case_one_I a b k ha hb u v (fun c => (hτ c).1) (fun c => (hτ c).2)
  rintro ⟨hσ, h⟩
  obtain ⟨x, y⟩ := σ
  simp only [Strategy₁.IsValid, Set.mem_Icc] at hσ
  obtain ⟨⟨hx0, hx0'⟩, hy0, hy0'⟩ := hσ 0
  obtain ⟨⟨hx1, hx1'⟩, hy1, hy1'⟩ := hσ 1
  obtain ⟨⟨hx2, hx2'⟩, hy2, hy2'⟩ := hσ 2
  rw [gn_value_case_one hab.le] at h
  have key : ∀ u v : Fin 3 → ℝ, Strategy₂.IsValid (u, v) →
      0 ≤ (2 * a + b) * (6 * payoff a b (x, y) (u, v)) + b * b := by
    intro u v hv
    have h1 := h (u, v) hv
    rw [div_le_iff₀ (by positivity)] at h1
    linarith
  have E000 := key ![0, 0, 1] ![0, 0, 1]
    (gn_isValid₂ gn_zero_mem gn_zero_mem gn_one_mem gn_zero_mem gn_zero_mem gn_one_mem)
  have E001 := key ![0, 0, 1] ![0, 1, 1]
    (gn_isValid₂ gn_zero_mem gn_zero_mem gn_one_mem gn_zero_mem gn_one_mem gn_one_mem)
  have E100 := key ![1, 0, 1] ![0, 0, 1]
    (gn_isValid₂ gn_one_mem gn_zero_mem gn_one_mem gn_zero_mem gn_zero_mem gn_one_mem)
  have E101 := key ![1, 0, 1] ![0, 1, 1]
    (gn_isValid₂ gn_one_mem gn_zero_mem gn_one_mem gn_zero_mem gn_one_mem gn_one_mem)
  rw [payoff_eq_sum] at E000 E001 E100 E101
  simp only [dealPayoff, toHigher, Matrix.cons_val, Fin.reduceLT, ↓reduceIte] at E000 E001 E100 E101
  have hs0 : 0 ≤ (1 - x 0) * y 0 := mul_nonneg (sub_nonneg.mpr hx0') hy0
  have hs2 : 0 ≤ (1 - x 2) * y 2 := mul_nonneg (sub_nonneg.mpr hx2') hy2
  have hf2 : 0 ≤ (1 - x 2) * (1 - y 2) := mul_nonneg (sub_nonneg.mpr hx2') (sub_nonneg.mpr hy2')
  -- H1 ≥ 0 (from II's pure strategy 001), A ≤ 0 (from 101 and H1), B ≥ 0 (from 000 and 100)
  have H1 : 0 ≤ -(2 * ((2 * a + b) * x 0 - b) + (2 * a + b) * x 1 + (2 * a + b) * ((1 - x 0) * y 0)
      + ((2 * a + b) * ((1 - x 1) * y 1) - 2 * a) + (2 * a + b) * (1 - x 2)) := by
    have h' : 0 ≤ b * -(2 * ((2 * a + b) * x 0 - b) + (2 * a + b) * x 1 + (2 * a + b) * ((1 - x 0) * y 0)
        + ((2 * a + b) * ((1 - x 1) * y 1) - 2 * a) + (2 * a + b) * (1 - x 2)) := by linarith only [E001]
    exact nonneg_of_mul_nonneg_right h' hb
  have HA : 0 ≤ -(2 * ((2 * a + b) * x 0 - b) + b * x 1 + (2 * a + b) * ((1 - x 0) * y 0)
      + 2 * a * (1 - x 2) + (2 * a + b) * ((1 - x 2) * (1 - y 2))) := by
    have h' : 0 ≤ (2 * a + b) * -(2 * ((2 * a + b) * x 0 - b) + b * x 1 + (2 * a + b) * ((1 - x 0) * y 0)
        + 2 * a * (1 - x 2) + (2 * a + b) * ((1 - x 2) * (1 - y 2))) := by
      linarith only [E101, mul_nonneg ha.le H1]
    exact nonneg_of_mul_nonneg_right h' hd
  have HB : 0 ≤ (2 * a - b) * ((2 * a + b) * x 0 - b) - b * b * x 1 - b * (2 * a + b) * ((1 - x 0) * y 0)
      - 2 * a * b * (1 - x 2) + b * (2 * a + b) * ((1 - x 2) * y 2) := by
    have h' : 0 ≤ (2 * a + b) * ((2 * a - b) * ((2 * a + b) * x 0 - b) - b * b * x 1
        - b * (2 * a + b) * ((1 - x 0) * y 0) - 2 * a * b * (1 - x 2)
        + b * (2 * a + b) * ((1 - x 2) * y 2)) := by
      linarith only [mul_nonneg ha.le E000, mul_nonneg hb.le E100]
    exact nonneg_of_mul_nonneg_right h' hd
  clear E000 E001 E101
  have h2ab : 0 < 2 * a - b := by linarith
  have hT := mul_nonneg h2ab.le HA
  have p1 : 0 ≤ b * (2 * a + b) * x 1 := mul_nonneg (mul_nonneg hb.le hd.le) hx1
  have p2 : 0 ≤ (2 * a + b) * (2 * a + b) * ((1 - x 0) * y 0) := mul_nonneg (mul_nonneg hd.le hd.le) hs0
  have p3 : 0 ≤ (2 * a + b) * (a - b) * ((1 - x 2) * y 2) :=
    mul_nonneg (mul_nonneg hd.le (sub_nonneg.mpr hab.le)) hs2
  have p4 : 0 ≤ (4 * a - b) * (2 * a + b) * ((1 - x 2) * (1 - y 2)) :=
    mul_nonneg (mul_nonneg (by linarith) hd.le) hf2
  have z1 : x 1 = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right (by linarith only [hT, HB, p1, p2, p3, p4]) (mul_pos hb hd)) hx1
  have zs0 : (1 - x 0) * y 0 = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right (by linarith only [hT, HB, p1, p2, p3, p4]) (mul_pos hd hd)) hs0
  have zs2 : (1 - x 2) * y 2 = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right (by linarith only [hT, HB, p1, p2, p3, p4])
      (mul_pos hd (sub_pos.mpr hab))) hs2
  have zf2 : (1 - x 2) * (1 - y 2) = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right (by linarith only [hT, HB, p1, p2, p3, p4])
      (mul_pos (by linarith : (0 : ℝ) < 4 * a - b) hd)) hf2
  have z2 : x 2 = 1 := by linarith only [zs2, zf2]
  have e0 : b * x 1 = 0 := by rw [z1, mul_zero]
  have e0' : (2 * a + b) * x 1 = 0 := by rw [z1, mul_zero]
  have e1 : (2 * a + b) * ((1 - x 0) * y 0) = 0 := by rw [zs0, mul_zero]
  have e2 : a * (1 - x 2) = 0 := by rw [z2, sub_self, mul_zero]
  have e2' : b * (1 - x 2) = 0 := by rw [z2, sub_self, mul_zero]
  have e3 : (2 * a + b) * ((1 - x 2) * (1 - y 2)) = 0 := by rw [zf2, mul_zero]
  have e4 : (2 * a + b) * ((1 - x 2) * y 2) = 0 := by rw [zs2, mul_zero]
  have hD0 : (2 * a + b) * x 0 - b = 0 := by
    have h' : 0 ≤ (2 * a - b) * ((2 * a + b) * x 0 - b) := by
      have e1b : b * ((2 * a + b) * ((1 - x 0) * y 0)) = 0 := by rw [e1, mul_zero]
      have e4b : b * ((2 * a + b) * ((1 - x 2) * y 2)) = 0 := by rw [e4, mul_zero]
      have e0b : b * (b * x 1) = 0 := by rw [e0, mul_zero]
      have e2b : b * (a * (1 - x 2)) = 0 := by rw [e2, mul_zero]
      linarith only [HB, e0b, e1b, e2b, e4b]
    have h'' := nonneg_of_mul_nonneg_right h' h2ab
    linarith only [h'', HA, e0, e1, e2, e3]
  have z0 : x 0 = b / (2 * a + b) := by
    rw [eq_div_iff hd.ne']
    linarith only [hD0]
  have hx0lt : 0 < 1 - x 0 := by
    have h2a : (2 * a + b) * (1 - x 0) = 2 * a := by linarith only [hD0]
    have h2a' : 0 < (2 * a + b) * (1 - x 0) := by rw [h2a]; positivity
    exact pos_of_mul_pos_right h2a' hd.le
  have zy0 : y 0 = 0 := (mul_eq_zero.mp zs0).resolve_left hx0lt.ne'
  have zy1 : y 1 = 2 * a / (2 * a + b) := by
    rw [eq_div_iff hd.ne']
    have hD0' : (2 * a - b) * ((2 * a + b) * x 0 - b) = 0 := by rw [hD0, mul_zero]
    simp only [z1, z2, zy0] at E100 H1
    have h' : 0 ≤ a * ((2 * a + b) * y 1 - 2 * a) := by linarith only [E100, hD0']
    have h'' := nonneg_of_mul_nonneg_right h' ha
    linarith only [H1, h'', hD0]
  refine ⟨y 2, ⟨hy2, hy2'⟩, ?_⟩
  refine Prod.ext (funext fun c => ?_) (funext fun c => ?_) <;> fin_cases c <;>
    simp [z0, z1, z2, zy0, zy1]

end KuhnPoker
