module

public import KuhnPoker.Defs
public import KuhnPoker.Payoff

/-!
# The normal form

Kuhn's normal form (p. 98–100) reduced to the sequence form. For `a = b = 1` the payoff is an explicit
polynomial `nf_F B C u v` in I's sequence-form atoms (`B c` the probability of betting first with card `c`,
`C c` the probability of passing and then calling with `c`) and II's behaviour coordinates (`u c` betting after a
pass, `v c` calling a bet); it is affine in `(B, C)` for fixed `(u, v)` and affine in `(u, v)` for fixed `(B, C)`.
Hence the mixed payoff of `p` against `q` is `nf_F` at the realization plan of `p` and the marginals of `q`
(`nf_bridge`), and every normal-form statement reduces to a linear or bilinear certificate:

* `nf_lower_seq`: on Kuhn's segment, `nf_F + 1/18` is a sum of four nonnegative products;
* `nf_upper_seq`: against Kuhn's strategy for II, `−1/18 − nf_F` is linear and nonnegative on the plans;
* the "only if" directions: three pure strategies of the opponent (as point masses) and the box constraints
  pin the plan (I) or the marginals (II), by `linarith`.
-/

@[expose] public section

namespace KuhnPoker

/-! ### The sequence-form payoff -/

/-- The payoff of Kuhn's game (`a = b = 1`) in sequence form: `B c` is the probability that I bets first with
card `c`, `C c` the probability that I passes and then calls with `c`; `u c`, `v c` are II's probabilities of
betting after a pass and of calling a bet with `c`. -/
noncomputable def nf_F (B C u v : Fin 3 → ℝ) : ℝ :=
  -(2 / 3) * u 0 - 1 / 3 * u 1
    + B 0 * (2 / 3 - v 1 / 2 - v 2 / 2)
    + B 1 * (1 / 3 + u 0 / 3 + v 0 / 6 - v 2 / 2)
    + B 2 * (u 0 / 3 + u 1 / 3 + v 0 / 6 + v 1 / 6)
    + C 0 * (-(u 1 / 6) - u 2 / 6)
    + C 1 * (u 0 / 2 - u 2 / 6)
    + C 2 * (u 0 / 2 + u 1 / 2)

/-- The behaviour payoff is the sequence-form payoff at the atoms `σ.1 c` and `(1 − σ.1 c) σ.2 c`. -/
theorem nf_payoff_eq (σ : Strategy₁) (τ : Strategy₂) :
    payoff 1 1 σ τ = nf_F σ.1 (fun c => (1 - σ.1 c) * σ.2 c) τ.1 τ.2 := by
  rw [payoff_eq_sum]
  simp only [dealPayoff, toHigher, nf_F, Fin.reduceLT, ↓reduceIte]
  ring

/-- The payoff of a pair of pure strategies. -/
theorem nf_payoff_pure (x : Fin 3 → Fin 3) (y : Fin 3 → Fin 4) :
    payoff 1 1 (pure₁ x) (pure₂ y)
      = nf_F (fun c => if x c = 2 then 1 else 0) (fun c => if x c = 1 then 1 else 0)
          (fun c => if 2 ≤ y c then 1 else 0) (fun c => if y c = 1 ∨ y c = 3 then 1 else 0) := by
  have h : (fun c => (1 - (pure₁ x).1 c) * (pure₁ x).2 c) = fun c => if x c = 1 then 1 else 0 := by
    funext c
    simp only [pure₁]
    split_ifs with h1 h2 <;> first | (exfalso; rw [h1] at h2; exact absurd h2 (by decide)) | norm_num
  rw [nf_payoff_eq, h]
  rfl

/-! ### Affine sums -/

/-- `nf_F` is affine in `(B, C)`: averaging commutes with it. -/
theorem nf_sum_left {X : Type} [Fintype X] (p : X → ℝ) (hp : ∑ x, p x = 1) (B C : X → Fin 3 → ℝ)
    (u v : Fin 3 → ℝ) :
    ∑ x, p x * nf_F (B x) (C x) u v
      = nf_F (fun c => ∑ x, p x * B x c) (fun c => ∑ x, p x * C x c) u v := by
  have h : ∀ x, p x * nf_F (B x) (C x) u v =
      p x * (-(2 / 3) * u 0 - 1 / 3 * u 1)
      + p x * B x 0 * (2 / 3 - v 1 / 2 - v 2 / 2)
      + p x * B x 1 * (1 / 3 + u 0 / 3 + v 0 / 6 - v 2 / 2)
      + p x * B x 2 * (u 0 / 3 + u 1 / 3 + v 0 / 6 + v 1 / 6)
      + p x * C x 0 * (-(u 1 / 6) - u 2 / 6)
      + p x * C x 1 * (u 0 / 2 - u 2 / 6)
      + p x * C x 2 * (u 0 / 2 + u 1 / 2) := fun x => by simp only [nf_F]; ring
  simp only [h, Finset.sum_add_distrib, ← Finset.sum_mul, hp]
  simp only [nf_F]
  ring

/-- `nf_F` is affine in `(u, v)`: averaging commutes with it. -/
theorem nf_sum_right {Y : Type} [Fintype Y] (q : Y → ℝ) (hq : ∑ y, q y = 1) (B C : Fin 3 → ℝ)
    (u v : Y → Fin 3 → ℝ) :
    ∑ y, q y * nf_F B C (u y) (v y)
      = nf_F B C (fun c => ∑ y, q y * u y c) (fun c => ∑ y, q y * v y c) := by
  have h : ∀ y, q y * nf_F B C (u y) (v y) =
      q y * (2 / 3 * B 0 + 1 / 3 * B 1)
      + q y * u y 0 * (B 1 / 3 + B 2 / 3 + C 1 / 2 + C 2 / 2 - 2 / 3)
      + q y * u y 1 * (B 2 / 3 - C 0 / 6 + C 2 / 2 - 1 / 3)
      + q y * u y 2 * (-(C 0 / 6) - C 1 / 6)
      + q y * v y 0 * (B 1 / 6 + B 2 / 6)
      + q y * v y 1 * (-(B 0 / 2) + B 2 / 6)
      + q y * v y 2 * (-(B 0 / 2) - B 1 / 2) := fun y => by simp only [nf_F]; ring
  simp only [h, Finset.sum_add_distrib, ← Finset.sum_mul, hq]
  simp only [nf_F]
  ring

/-! ### Realization plans and marginals as averages -/

theorem nf_realBet_eq (p : (Fin 3 → Fin 3) → ℝ) :
    realBet p = fun c => ∑ x, p x * (if x c = 2 then 1 else 0) := by
  funext c
  unfold realBet
  refine Finset.sum_congr rfl (fun x _ => ?_)
  split_ifs <;> ring

theorem nf_realCall_eq (p : (Fin 3 → Fin 3) → ℝ) :
    realCall p = fun c => ∑ x, p x * (if x c = 1 then 1 else 0) := by
  funext c
  unfold realCall
  refine Finset.sum_congr rfl (fun x _ => ?_)
  split_ifs <;> ring

theorem nf_margBet_eq (q : (Fin 3 → Fin 4) → ℝ) :
    margBet q = fun c => ∑ y, q y * (if 2 ≤ y c then 1 else 0) := by
  funext c
  unfold margBet
  refine Finset.sum_congr rfl (fun y _ => ?_)
  split_ifs <;> ring

theorem nf_margCall_eq (q : (Fin 3 → Fin 4) → ℝ) :
    margCall q = fun c => ∑ y, q y * (if y c = 1 ∨ y c = 3 then 1 else 0) := by
  funext c
  unfold margCall
  refine Finset.sum_congr rfl (fun y _ => ?_)
  split_ifs <;> ring

/-- The affine bridge: the normal-form payoff is the sequence-form payoff at the realization plan of `p`
and the marginals of `q`. -/
theorem nf_bridge (p : (Fin 3 → Fin 3) → ℝ) (q : (Fin 3 → Fin 4) → ℝ)
    (hp : ∑ x, p x = 1) (hq : ∑ y, q y = 1) :
    mixedPayoff p q = nf_F (realBet p) (realCall p) (margBet q) (margCall q) := by
  have h1 : ∀ x : Fin 3 → Fin 3, ∑ y, p x * q y * payoff 1 1 (pure₁ x) (pure₂ y)
      = p x * nf_F (fun c => if x c = 2 then 1 else 0) (fun c => if x c = 1 then 1 else 0)
          (margBet q) (margCall q) := by
    intro x
    rw [nf_margBet_eq, nf_margCall_eq, ← nf_sum_right q hq, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [nf_payoff_pure, mul_assoc]
  unfold mixedPayoff
  simp only [h1]
  rw [nf_sum_left p hp, nf_realBet_eq, nf_realCall_eq]

/-! ### Point masses and mixtures -/

theorem nf_isProb_δ {ι : Type} [Fintype ι] [DecidableEq ι] (x₀ : ι) : IsProb (δ x₀) := by
  refine ⟨fun x => ?_, ?_⟩
  · unfold δ
    split_ifs <;> norm_num
  · simp only [δ]
    rw [Fintype.sum_ite_eq']

theorem nf_ind_δ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] (x₀ : ι) :
    ∑ x, (if P x then δ x₀ x else 0) = if P x₀ then 1 else 0 := by
  rw [Fintype.sum_eq_single x₀]
  · simp [δ]
  · intro x hx
    simp [δ, hx]

theorem nf_realBet_δ (x₀ : Fin 3 → Fin 3) : realBet (δ x₀) = fun c => if x₀ c = 2 then 1 else 0 := by
  funext c
  exact nf_ind_δ (fun x => x c = 2) x₀

theorem nf_realCall_δ (x₀ : Fin 3 → Fin 3) : realCall (δ x₀) = fun c => if x₀ c = 1 then 1 else 0 := by
  funext c
  exact nf_ind_δ (fun x => x c = 1) x₀

theorem nf_margBet_δ (y₀ : Fin 3 → Fin 4) : margBet (δ y₀) = fun c => if 2 ≤ y₀ c then 1 else 0 := by
  funext c
  exact nf_ind_δ (fun y => 2 ≤ y c) y₀

theorem nf_margCall_δ (y₀ : Fin 3 → Fin 4) :
    margCall (δ y₀) = fun c => if y₀ c = 1 ∨ y₀ c = 3 then 1 else 0 := by
  funext c
  exact nf_ind_δ (fun y => y c = 1 ∨ y c = 3) y₀

theorem nf_ind_mix2 {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P]
    (a b : ℝ) (x₁ x₂ : ι) :
    ∑ x, (if P x then a * δ x₁ x + b * δ x₂ x else 0)
      = a * (if P x₁ then 1 else 0) + b * (if P x₂ then 1 else 0) := by
  rw [← nf_ind_δ P x₁, ← nf_ind_δ P x₂, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  split_ifs <;> ring

theorem nf_ind_mix3 {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P]
    (a b d : ℝ) (x₁ x₂ x₃ : ι) :
    ∑ x, (if P x then a * δ x₁ x + b * δ x₂ x + d * δ x₃ x else 0)
      = a * (if P x₁ then 1 else 0) + b * (if P x₂ then 1 else 0) + d * (if P x₃ then 1 else 0) := by
  rw [← nf_ind_δ P x₁, ← nf_ind_δ P x₂, ← nf_ind_δ P x₃, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  split_ifs <;> ring

theorem nf_isProb_mix2 {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ℝ) (x₁ x₂ : ι)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : a + b = 1) :
    IsProb (fun x => a * δ x₁ x + b * δ x₂ x) := by
  refine ⟨fun x => ?_, ?_⟩
  · exact add_nonneg (mul_nonneg ha ((nf_isProb_δ x₁).1 x)) (mul_nonneg hb ((nf_isProb_δ x₂).1 x))
  · dsimp only
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, (nf_isProb_δ x₁).2, (nf_isProb_δ x₂).2]
    linarith

theorem nf_isProb_mix3 {ι : Type} [Fintype ι] [DecidableEq ι] (a b d : ℝ) (x₁ x₂ x₃ : ι)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (hs : a + b + d = 1) :
    IsProb (fun x => a * δ x₁ x + b * δ x₂ x + d * δ x₃ x) := by
  refine ⟨fun x => ?_, ?_⟩
  · exact add_nonneg (add_nonneg (mul_nonneg ha ((nf_isProb_δ x₁).1 x))
      (mul_nonneg hb ((nf_isProb_δ x₂).1 x))) (mul_nonneg hd ((nf_isProb_δ x₃).1 x))
  · dsimp only
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      (nf_isProb_δ x₁).2, (nf_isProb_δ x₂).2, (nf_isProb_δ x₃).2]
    linarith

/-! ### Boxes -/

/-- A realization plan of a mixed strategy of I: nonnegative, with `bet + call ≤ 1` at each card. -/
theorem nf_real_mem (p : (Fin 3 → Fin 3) → ℝ) (hp : IsProb p) (c : Fin 3) :
    0 ≤ realBet p c ∧ 0 ≤ realCall p c ∧ realBet p c + realCall p c ≤ 1 := by
  obtain ⟨h0, h1⟩ := hp
  refine ⟨Finset.sum_nonneg (fun x _ => ?_), Finset.sum_nonneg (fun x _ => ?_), ?_⟩
  · split_ifs <;> first | exact h0 x | exact le_rfl
  · split_ifs <;> first | exact h0 x | exact le_rfl
  · unfold realBet realCall
    rw [← Finset.sum_add_distrib, ← h1]
    refine Finset.sum_le_sum (fun x _ => ?_)
    split_ifs with ha hb
    · rw [ha] at hb
      exact absurd hb (by decide)
    · linarith [h0 x]
    · linarith [h0 x]
    · linarith [h0 x]

/-- The marginals of a mixed strategy of II lie in `[0, 1]`. -/
theorem nf_marg_mem (q : (Fin 3 → Fin 4) → ℝ) (hq : IsProb q) (c : Fin 3) :
    (0 ≤ margBet q c ∧ margBet q c ≤ 1) ∧ (0 ≤ margCall q c ∧ margCall q c ≤ 1) := by
  obtain ⟨h0, h1⟩ := hq
  refine ⟨⟨Finset.sum_nonneg (fun y _ => ?_), ?_⟩, ⟨Finset.sum_nonneg (fun y _ => ?_), ?_⟩⟩
  · split_ifs <;> first | exact h0 y | exact le_rfl
  · unfold margBet
    rw [← h1]
    exact Finset.sum_le_sum (fun y _ => by split_ifs <;> first | exact le_rfl | exact h0 y)
  · split_ifs <;> first | exact h0 y | exact le_rfl
  · unfold margCall
    rw [← h1]
    exact Finset.sum_le_sum (fun y _ => by split_ifs <;> first | exact le_rfl | exact h0 y)

/-! ### The two certificates in sequence form -/

/-- Kuhn's segment guarantees `−1/18`: `nf_F + 1/18 = (α/2) v₀ + (α/2)(1 − v₂) + ((1/3 − α)/2) u₁
+ (1/18 + α/6)(1 − u₂)`. -/
theorem nf_lower_seq (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) (1 / 3)) (u v : Fin 3 → ℝ)
    (hu : ∀ c, 0 ≤ u c ∧ u c ≤ 1) (hv : ∀ c, 0 ≤ v c ∧ v c ≤ 1) :
    -1 / 18 ≤ nf_F ![α, 0, 3 * α] ![0, α + 1 / 3, 1 - 3 * α] u v := by
  obtain ⟨ha0, ha1⟩ := hα
  obtain ⟨hv0, -⟩ := hv 0
  obtain ⟨-, hv2⟩ := hv 2
  obtain ⟨hu1, -⟩ := hu 1
  obtain ⟨-, hu2⟩ := hu 2
  simp only [nf_F, Matrix.cons_val]
  linarith [mul_nonneg ha0 hv0, mul_nonneg ha0 (sub_nonneg.2 hv2), mul_nonneg (sub_nonneg.2 ha1) hu1,
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 18 + α / 6) (sub_nonneg.2 hu2)]

/-- Kuhn's strategy for II holds every plan to `−1/18`: `−1/18 − nf_F = B₁/18 + C₀/6 + (1 − B₂ − C₂)/6`. -/
theorem nf_upper_seq (B C : Fin 3 → ℝ) (h : ∀ c, 0 ≤ B c ∧ 0 ≤ C c ∧ B c + C c ≤ 1) :
    nf_F B C ![1 / 3, 0, 1] ![0, 1 / 3, 1] ≤ -1 / 18 := by
  obtain ⟨hb0, hc0, hs0⟩ := h 0
  obtain ⟨hb1, hc1, hs1⟩ := h 1
  obtain ⟨hb2, hc2, hs2⟩ := h 2
  simp only [nf_F, Matrix.cons_val]
  linarith

/-! ### The optimal mixed strategies -/

theorem guaranteesMixed₁_iff_internal (p : (Fin 3 → Fin 3) → ℝ) : GuaranteesMixed₁ p (-1 / 18) ↔
    IsProb p ∧ ∃ α ∈ Set.Icc (0 : ℝ) (1 / 3),
      realBet p = ![α, 0, 3 * α] ∧ realCall p = ![0, α + 1 / 3, 1 - 3 * α] := by
  constructor
  · rintro ⟨hp, hg⟩
    refine ⟨hp, ?_⟩
    have key : ∀ y₀ : Fin 3 → Fin 4, -1 / 18 ≤ nf_F (realBet p) (realCall p)
        (fun c => if 2 ≤ y₀ c then 1 else 0) (fun c => if y₀ c = 1 ∨ y₀ c = 3 then 1 else 0) := by
      intro y₀
      have h := hg (δ y₀) (nf_isProb_δ y₀)
      rwa [nf_bridge p _ hp.2 (nf_isProb_δ y₀).2, nf_margBet_δ, nf_margCall_δ] at h
    have hA := key ![0, 0, 3]
    have hB := key ![2, 0, 3]
    have hC := key ![0, 1, 3]
    norm_num [nf_F] at hA hB hC
    obtain ⟨b0, k0, s0⟩ := nf_real_mem p hp 0
    obtain ⟨b1, k1, s1⟩ := nf_real_mem p hp 1
    obtain ⟨b2, k2, s2⟩ := nf_real_mem p hp 2
    have e1 : realBet p 1 = 0 := by linarith
    have e2 : realBet p 2 = 3 * realBet p 0 := by linarith
    have e3 : realCall p 0 = 0 := by linarith
    have e4 : realCall p 1 = realBet p 0 + 1 / 3 := by linarith
    have e5 : realCall p 2 = 1 - 3 * realBet p 0 := by linarith
    have e6 : realBet p 0 ≤ 1 / 3 := by linarith
    refine ⟨realBet p 0, ⟨b0, e6⟩, ?_, ?_⟩
    · funext c
      fin_cases c <;> simp [e1, e2]
    · funext c
      fin_cases c <;> simp [e3, e4, e5]
  · rintro ⟨hp, α, hα, hb, hc⟩
    refine ⟨hp, fun q hq => ?_⟩
    rw [nf_bridge p q hp.2 hq.2, hb, hc]
    exact nf_lower_seq α hα _ _ (fun c => (nf_marg_mem q hq c).1) (fun c => (nf_marg_mem q hq c).2)

theorem guaranteesMixed₂_iff_internal (q : (Fin 3 → Fin 4) → ℝ) : GuaranteesMixed₂ q (-1 / 18) ↔
    IsProb q ∧ margBet q = ![1 / 3, 0, 1] ∧ margCall q = ![0, 1 / 3, 1] := by
  constructor
  · rintro ⟨hq, hg⟩
    refine ⟨hq, ?_⟩
    have key : ∀ x₀ : Fin 3 → Fin 3, nf_F (fun c => if x₀ c = 2 then 1 else 0)
        (fun c => if x₀ c = 1 then 1 else 0) (margBet q) (margCall q) ≤ -1 / 18 := by
      intro x₀
      have h := hg (δ x₀) (nf_isProb_δ x₀)
      rwa [nf_bridge _ q (nf_isProb_δ x₀).2 hq.2, nf_realBet_δ, nf_realCall_δ] at h
    have h1 := key ![2, 0, 1]
    have h2 := key ![0, 1, 1]
    have h3 := key ![0, 0, 2]
    norm_num [nf_F] at h1 h2 h3
    obtain ⟨⟨u0, u0'⟩, ⟨v0, v0'⟩⟩ := nf_marg_mem q hq 0
    obtain ⟨⟨u1, u1'⟩, ⟨v1, v1'⟩⟩ := nf_marg_mem q hq 1
    obtain ⟨⟨u2, u2'⟩, ⟨v2, v2'⟩⟩ := nf_marg_mem q hq 2
    have e0 : margBet q 0 = 1 / 3 := by linarith
    have e1 : margBet q 1 = 0 := by linarith
    have e2 : margBet q 2 = 1 := by linarith
    have f0 : margCall q 0 = 0 := by linarith
    have f1 : margCall q 1 = 1 / 3 := by linarith
    have f2 : margCall q 2 = 1 := by linarith
    refine ⟨?_, ?_⟩
    · funext c
      fin_cases c <;> simp [e0, e1, e2]
    · funext c
      fin_cases c <;> simp [f0, f1, f2]
  · rintro ⟨hq, hb, hc⟩
    refine ⟨hq, fun p hp => ?_⟩
    rw [nf_bridge p q hp.2 hq.2, hb, hc]
    exact nf_upper_seq _ _ (nf_real_mem p hp)

/-! ### Kuhn's basic strategies -/

theorem nf_guar₁_mix2 (a b : ℝ) (x₁ x₂ : Fin 3 → Fin 3) (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : a + b = 1)
    (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) (1 / 3))
    (hB : ∀ c, a * (if x₁ c = 2 then 1 else 0) + b * (if x₂ c = 2 then 1 else 0) = ![α, 0, 3 * α] c)
    (hC : ∀ c, a * (if x₁ c = 1 then 1 else 0) + b * (if x₂ c = 1 then 1 else 0)
      = ![0, α + 1 / 3, 1 - 3 * α] c) :
    GuaranteesMixed₁ (fun x => a * δ x₁ x + b * δ x₂ x) (-1 / 18) := by
  refine (guaranteesMixed₁_iff_internal _).2 ⟨nf_isProb_mix2 a b x₁ x₂ ha hb hs, α, hα, ?_, ?_⟩
  · funext c
    rw [← hB c]
    exact nf_ind_mix2 (fun x => x c = 2) a b x₁ x₂
  · funext c
    rw [← hC c]
    exact nf_ind_mix2 (fun x => x c = 1) a b x₁ x₂

theorem nf_guar₁_mix3 (a b d : ℝ) (x₁ x₂ x₃ : Fin 3 → Fin 3) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hs : a + b + d = 1) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) (1 / 3))
    (hB : ∀ c, a * (if x₁ c = 2 then 1 else 0) + b * (if x₂ c = 2 then 1 else 0)
      + d * (if x₃ c = 2 then 1 else 0) = ![α, 0, 3 * α] c)
    (hC : ∀ c, a * (if x₁ c = 1 then 1 else 0) + b * (if x₂ c = 1 then 1 else 0)
      + d * (if x₃ c = 1 then 1 else 0) = ![0, α + 1 / 3, 1 - 3 * α] c) :
    GuaranteesMixed₁ (fun x => a * δ x₁ x + b * δ x₂ x + d * δ x₃ x) (-1 / 18) := by
  refine (guaranteesMixed₁_iff_internal _).2 ⟨nf_isProb_mix3 a b d x₁ x₂ x₃ ha hb hd hs, α, hα, ?_, ?_⟩
  · funext c
    rw [← hB c]
    exact nf_ind_mix3 (fun x => x c = 2) a b d x₁ x₂ x₃
  · funext c
    rw [← hC c]
    exact nf_ind_mix3 (fun x => x c = 1) a b d x₁ x₂ x₃

theorem nf_guar₂_mix2 (a b : ℝ) (y₁ y₂ : Fin 3 → Fin 4) (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : a + b = 1)
    (hB : ∀ c, a * (if 2 ≤ y₁ c then 1 else 0) + b * (if 2 ≤ y₂ c then 1 else 0) = ![1 / 3, 0, 1] c)
    (hC : ∀ c, a * (if y₁ c = 1 ∨ y₁ c = 3 then 1 else 0) + b * (if y₂ c = 1 ∨ y₂ c = 3 then 1 else 0)
      = ![0, 1 / 3, 1] c) :
    GuaranteesMixed₂ (fun y => a * δ y₁ y + b * δ y₂ y) (-1 / 18) := by
  refine (guaranteesMixed₂_iff_internal _).2 ⟨nf_isProb_mix2 a b y₁ y₂ ha hb hs, ?_, ?_⟩
  · funext c
    rw [← hB c]
    exact nf_ind_mix2 (fun y => 2 ≤ y c) a b y₁ y₂
  · funext c
    rw [← hC c]
    exact nf_ind_mix2 (fun y => y c = 1 ∨ y c = 3) a b y₁ y₂

theorem nf_guar₂_mix3 (a b d : ℝ) (y₁ y₂ y₃ : Fin 3 → Fin 4) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hs : a + b + d = 1)
    (hB : ∀ c, a * (if 2 ≤ y₁ c then 1 else 0) + b * (if 2 ≤ y₂ c then 1 else 0)
      + d * (if 2 ≤ y₃ c then 1 else 0) = ![1 / 3, 0, 1] c)
    (hC : ∀ c, a * (if y₁ c = 1 ∨ y₁ c = 3 then 1 else 0) + b * (if y₂ c = 1 ∨ y₂ c = 3 then 1 else 0)
      + d * (if y₃ c = 1 ∨ y₃ c = 3 then 1 else 0) = ![0, 1 / 3, 1] c) :
    GuaranteesMixed₂ (fun y => a * δ y₁ y + b * δ y₂ y + d * δ y₃ y) (-1 / 18) := by
  refine (guaranteesMixed₂_iff_internal _).2 ⟨nf_isProb_mix3 a b d y₁ y₂ y₃ ha hb hd hs, ?_, ?_⟩
  · funext c
    rw [← hB c]
    exact nf_ind_mix3 (fun y => 2 ≤ y c) a b d y₁ y₂ y₃
  · funext c
    rw [← hC c]
    exact nf_ind_mix3 (fun y => y c = 1 ∨ y c = 3) a b d y₁ y₂ y₃

theorem basic₁_guarantees_internal (i : Fin 12) : GuaranteesMixed₁ (basic₁ i) (-1 / 18) := by
  fin_cases i
  · exact nf_guar₁_mix2 (2 / 3) (1 / 3) ![0, 0, 1] ![0, 1, 1] (by norm_num) (by norm_num) (by norm_num)
      0 (by norm_num) (by intro c; fin_cases c <;> norm_num) (by intro c; fin_cases c <;> norm_num)
  · exact nf_guar₁_mix3 (1 / 3) (1 / 2) (1 / 6) ![0, 0, 1] ![0, 1, 2] ![2, 0, 1] (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (1 / 6) (by norm_num) (by intro c; fin_cases c <;> norm_num)
      (by intro c; fin_cases c <;> norm_num)
  · exact nf_guar₁_mix3 (5 / 9) (1 / 3) (1 / 9) ![0, 0, 1] ![0, 1, 2] ![2, 1, 1] (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (1 / 9) (by norm_num) (by intro c; fin_cases c <;> norm_num)
      (by intro c; fin_cases c <;> norm_num)
  · exact nf_guar₁_mix3 (1 / 2) (1 / 3) (1 / 6) ![0, 0, 1] ![0, 1, 2] ![2, 1, 2] (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (1 / 6) (by norm_num) (by intro c; fin_cases c <;> norm_num)
      (by intro c; fin_cases c <;> norm_num)
  · exact nf_guar₁_mix3 (2 / 5) (7 / 15) (2 / 15) ![0, 0, 2] ![0, 1, 1] ![2, 0, 1] (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (2 / 15) (by norm_num) (by intro c; fin_cases c <;> norm_num)
      (by intro c; fin_cases c <;> norm_num)
  · exact nf_guar₁_mix3 (1 / 3) (1 / 2) (1 / 6) ![0, 0, 2] ![0, 1, 1] ![2, 0, 2] (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (1 / 6) (by norm_num) (by intro c; fin_cases c <;> norm_num)
      (by intro c; fin_cases c <;> norm_num)
  · exact nf_guar₁_mix3 (1 / 2) (1 / 3) (1 / 6) ![0, 0, 2] ![0, 1, 1] ![2, 1, 1] (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (1 / 6) (by norm_num) (by intro c; fin_cases c <;> norm_num)
      (by intro c; fin_cases c <;> norm_num)
  · exact nf_guar₁_mix3 (4 / 9) (1 / 3) (2 / 9) ![0, 0, 2] ![0, 1, 1] ![2, 1, 2] (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (2 / 9) (by norm_num) (by intro c; fin_cases c <;> norm_num)
      (by intro c; fin_cases c <;> norm_num)
  · exact nf_guar₁_mix3 (1 / 6) (7 / 12) (1 / 4) ![0, 0, 2] ![0, 1, 2] ![2, 0, 1] (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (1 / 4) (by norm_num) (by intro c; fin_cases c <;> norm_num)
      (by intro c; fin_cases c <;> norm_num)
  · exact nf_guar₁_mix3 (5 / 12) (1 / 3) (1 / 4) ![0, 0, 2] ![0, 1, 2] ![2, 1, 1] (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (1 / 4) (by norm_num) (by intro c; fin_cases c <;> norm_num)
      (by intro c; fin_cases c <;> norm_num)
  · exact nf_guar₁_mix3 (1 / 3) (1 / 3) (1 / 3) ![0, 0, 2] ![0, 1, 2] ![2, 1, 2] (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (1 / 3) (by norm_num) (by intro c; fin_cases c <;> norm_num)
      (by intro c; fin_cases c <;> norm_num)
  · exact nf_guar₁_mix2 (2 / 3) (1 / 3) ![0, 1, 2] ![2, 0, 2] (by norm_num) (by norm_num) (by norm_num)
      (1 / 3) (by norm_num) (by intro c; fin_cases c <;> norm_num) (by intro c; fin_cases c <;> norm_num)

theorem basic₂_guarantees_internal (i : Fin 2) : GuaranteesMixed₂ (basic₂ i) (-1 / 18) := by
  fin_cases i
  · exact nf_guar₂_mix3 (1 / 3) (1 / 3) (1 / 3) ![0, 0, 3] ![0, 1, 3] ![2, 0, 3] (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by intro c; fin_cases c <;> norm_num) (by intro c; fin_cases c <;> norm_num)
  · exact nf_guar₂_mix2 (2 / 3) (1 / 3) ![0, 0, 3] ![2, 1, 3] (by norm_num) (by norm_num) (by norm_num)
      (by intro c; fin_cases c <;> norm_num) (by intro c; fin_cases c <;> norm_num)

theorem hasMixedValue_internal : HasMixedValue (-1 / 18) :=
  ⟨⟨basic₁ 0, basic₁_guarantees_internal 0⟩, ⟨basic₂ 0, basic₂_guarantees_internal 0⟩⟩

/-! ### Kuhn's essential matrix -/

theorem essentialMatrix_eq_internal (i : Fin 8) (j : Fin 4) :
    6 * payoff 1 1 (pure₁ (essentialRow i)) (pure₂ (essentialCol j)) = essentialMatrix i j := by
  rw [nf_payoff_pure]
  fin_cases i <;> fin_cases j <;> norm_num [nf_F, essentialRow, essentialCol, essentialMatrix]

end KuhnPoker
