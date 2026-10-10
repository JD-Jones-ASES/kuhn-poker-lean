module

public import Mathlib

/-!
# Definitions

The definitions of `Challenge.lean`, restated character for character (the registry's comparator judges the
elaborated constants; `scripts/check_definitions.py` compares the text and `scripts/verify.py` the `pp.all`
output). The development's modules import this file; `Solution.lean` restates the Challenge's theorems over it
and never imports `Challenge.lean`.
-/

@[expose] public section

namespace KuhnPoker

/-- A behaviour strategy of player I: `σ.1 c` is the probability of betting in the first round with card `c`,
`σ.2 c` the probability of calling (betting) in the second round, after passing and facing a bet, with card `c`. -/
abbrev Strategy₁ := (Fin 3 → ℝ) × (Fin 3 → ℝ)

/-- A behaviour strategy of player II: `τ.1 c` is the probability of betting when confronted by a pass with
card `c`, `τ.2 c` the probability of calling when confronted by a bet with card `c`. -/
abbrev Strategy₂ := (Fin 3 → ℝ) × (Fin 3 → ℝ)

/-- Every coordinate of a behaviour strategy is a probability. -/
def Strategy₁.IsValid (σ : Strategy₁) : Prop :=
  ∀ c, σ.1 c ∈ Set.Icc (0 : ℝ) 1 ∧ σ.2 c ∈ Set.Icc (0 : ℝ) 1

/-- Every coordinate of a behaviour strategy is a probability. -/
def Strategy₂.IsValid (τ : Strategy₂) : Prop :=
  ∀ c, τ.1 c ∈ Set.Icc (0 : ℝ) 1 ∧ τ.2 c ∈ Set.Icc (0 : ℝ) 1

/-- The amount `k` paid to the holder of the higher card, as a payoff to player I, who holds `c₁` against `c₂`. -/
def toHigher (c₁ c₂ : Fin 3) (k : ℝ) : ℝ := if c₂ < c₁ then k else -k

/-- The expected payoff to player I on the deal `(c₁, c₂)` (I holds `c₁`, II holds `c₂`), with ante `a` and bet
`b`, as the sum over Kuhn's five courses of play (p. 98): pass–pass, pass–bet–pass, pass–bet–bet, bet–pass,
bet–bet. -/
def dealPayoff (a b : ℝ) (σ : Strategy₁) (τ : Strategy₂) (c₁ c₂ : Fin 3) : ℝ :=
    (1 - σ.1 c₁) * (1 - τ.1 c₂) * toHigher c₁ c₂ a
  + (1 - σ.1 c₁) * τ.1 c₂ * (1 - σ.2 c₁) * (-a)
  + (1 - σ.1 c₁) * τ.1 c₂ * σ.2 c₁ * toHigher c₁ c₂ (a + b)
  + σ.1 c₁ * (1 - τ.2 c₂) * a
  + σ.1 c₁ * τ.2 c₂ * toHigher c₁ c₂ (a + b)

/-- The expected payoff to player I: the average over the six deals of distinct cards. -/
noncomputable def payoff (a b : ℝ) (σ : Strategy₁) (τ : Strategy₂) : ℝ :=
  (∑ c₁ : Fin 3, ∑ c₂ : Fin 3, if c₁ = c₂ then 0 else dealPayoff a b σ τ c₁ c₂) / 6

/-- Player I's strategy `σ` guarantees `v`: it is valid and earns at least `v` against every valid strategy
of II. -/
def Guarantees₁ (a b : ℝ) (σ : Strategy₁) (v : ℝ) : Prop :=
  σ.IsValid ∧ ∀ τ : Strategy₂, τ.IsValid → v ≤ payoff a b σ τ

/-- Player II's strategy `τ` guarantees `v`: it is valid and holds every valid strategy of I to at most `v`. -/
def Guarantees₂ (a b : ℝ) (τ : Strategy₂) (v : ℝ) : Prop :=
  τ.IsValid ∧ ∀ σ : Strategy₁, σ.IsValid → payoff a b σ τ ≤ v

/-- The game with ante `a` and bet `b` has value `v`: each player has a strategy guaranteeing `v`. -/
def HasValue (a b v : ℝ) : Prop := (∃ σ, Guarantees₁ a b σ v) ∧ (∃ τ, Guarantees₂ a b τ v)

/-- An equilibrium (saddle point): both strategies are valid, and neither player gains by deviating. -/
def IsEquilibrium (a b : ℝ) (σ : Strategy₁) (τ : Strategy₂) : Prop :=
  σ.IsValid ∧ τ.IsValid ∧
  (∀ σ' : Strategy₁, σ'.IsValid → payoff a b σ' τ ≤ payoff a b σ τ) ∧
  (∀ τ' : Strategy₂, τ'.IsValid → payoff a b σ τ ≤ payoff a b σ τ')

/-- Kuhn's optimal strategy for II (p. 102): bet after a pass with the `1`, `2`, `3` with probabilities
`1/3, 0, 1`; call a bet with probabilities `0, 1/3, 1`. -/
noncomputable def kuhnII : Strategy₂ := (![1 / 3, 0, 1], ![0, 1 / 3, 1])

/-- Kuhn's family for I (p. 101, `γ = 3α`): bet first with the `1`, `2`, `3` with probabilities `α, 0, 3α`;
call a bet with probabilities `0, α + 1/3, k`. -/
noncomputable def kuhnI (α k : ℝ) : Strategy₁ := (![α, 0, 3 * α], ![0, α + 1 / 3, k])

/-- Kuhn's coding of I's pure strategies (p. 98): `x c = 0` — pass, then pass (fold) if II bets; `x c = 1` — pass,
then bet (call); `x c = 2` — bet in the first round. -/
def pure₁ (x : Fin 3 → Fin 3) : Strategy₁ :=
  (fun c => if x c = 2 then 1 else 0, fun c => if x c = 1 then 1 else 0)

/-- Kuhn's coding of II's pure strategies (p. 98): `y c` in binary, the first figure the action when confronted
by a pass (`1` = bet), the second when confronted by a bet (`1` = call): `0 = 00`, `1 = 01`, `2 = 10`, `3 = 11`. -/
def pure₂ (y : Fin 3 → Fin 4) : Strategy₂ :=
  (fun c => if 2 ≤ y c then 1 else 0, fun c => if y c = 1 ∨ y c = 3 then 1 else 0)

/-- The rows of Kuhn's essential matrix (p. 99): I's pure strategies `(x₁, x₂, x₃)` with `x₁ ∈ {0, 2}`,
`x₂ ∈ {0, 1}`, `x₃ ∈ {1, 2}`, in his order. -/
def essentialRow : Fin 8 → (Fin 3 → Fin 3) :=
  ![![0, 0, 1], ![0, 0, 2], ![0, 1, 1], ![0, 1, 2], ![2, 0, 1], ![2, 0, 2], ![2, 1, 1], ![2, 1, 2]]

/-- The columns of Kuhn's essential matrix (p. 99): II's pure strategies `(y₁, y₂, y₃)` with `y₁ ∈ {0, 2}`,
`y₂ ∈ {0, 1}`, `y₃ = 3`, in his order. -/
def essentialCol : Fin 4 → (Fin 3 → Fin 4) := ![![0, 0, 3], ![0, 1, 3], ![2, 0, 3], ![2, 1, 3]]

/-- Kuhn's essential matrix (p. 99), "six times the actual game matrix". -/
def essentialMatrix : Matrix (Fin 8) (Fin 4) ℝ :=
  !![0, 0, -1, -1; 0, 1, -2, -1; -1, -1, 1, 1; -1, 0, 0, 1; 1, -2, 0, -3; 1, -1, -1, -3; 0, -3, 2, -1; 0, -2, 1, -1]

/-- A probability vector on a finite type. -/
def IsProb {ι : Type} [Fintype ι] (p : ι → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- The expected payoff to I in Kuhn's normal form, for mixed strategies `p` over the `27` pure strategies of I
and `q` over the `64` of II. -/
noncomputable def mixedPayoff (p : (Fin 3 → Fin 3) → ℝ) (q : (Fin 3 → Fin 4) → ℝ) : ℝ :=
  ∑ x, ∑ y, p x * q y * payoff 1 1 (pure₁ x) (pure₂ y)

/-- A mixed strategy of I guarantees `v` in the normal form. -/
def GuaranteesMixed₁ (p : (Fin 3 → Fin 3) → ℝ) (v : ℝ) : Prop :=
  IsProb p ∧ ∀ q : (Fin 3 → Fin 4) → ℝ, IsProb q → v ≤ mixedPayoff p q

/-- A mixed strategy of II guarantees `v` in the normal form. -/
def GuaranteesMixed₂ (q : (Fin 3 → Fin 4) → ℝ) (v : ℝ) : Prop :=
  IsProb q ∧ ∀ p : (Fin 3 → Fin 3) → ℝ, IsProb p → mixedPayoff p q ≤ v

/-- The normal form has value `v`. -/
def HasMixedValue (v : ℝ) : Prop := (∃ p, GuaranteesMixed₁ p v) ∧ (∃ q, GuaranteesMixed₂ q v)

/-- The realization plan of a mixed strategy of I: the probability of betting first with card `c`. -/
def realBet (p : (Fin 3 → Fin 3) → ℝ) (c : Fin 3) : ℝ := ∑ x, if x c = 2 then p x else 0

/-- The realization plan of a mixed strategy of I: the probability of passing and then calling with card `c`. -/
def realCall (p : (Fin 3 → Fin 3) → ℝ) (c : Fin 3) : ℝ := ∑ x, if x c = 1 then p x else 0

/-- The marginal of a mixed strategy of II: the probability of betting after a pass with card `c`. -/
def margBet (q : (Fin 3 → Fin 4) → ℝ) (c : Fin 3) : ℝ := ∑ y, if 2 ≤ y c then q y else 0

/-- The marginal of a mixed strategy of II: the probability of calling a bet with card `c`. -/
def margCall (q : (Fin 3 → Fin 4) → ℝ) (c : Fin 3) : ℝ := ∑ y, if y c = 1 ∨ y c = 3 then q y else 0

/-- The point mass at a pure strategy. -/
def δ {ι : Type} [DecidableEq ι] (x₀ x : ι) : ℝ := if x = x₀ then 1 else 0

/-- Kuhn's twelve basic optimal mixed strategies (A)–(L) for player I (p. 100). -/
noncomputable def basic₁ : Fin 12 → (Fin 3 → Fin 3) → ℝ :=
  ![fun x => 2 / 3 * δ ![0, 0, 1] x + 1 / 3 * δ ![0, 1, 1] x,
    fun x => 1 / 3 * δ ![0, 0, 1] x + 1 / 2 * δ ![0, 1, 2] x + 1 / 6 * δ ![2, 0, 1] x,
    fun x => 5 / 9 * δ ![0, 0, 1] x + 1 / 3 * δ ![0, 1, 2] x + 1 / 9 * δ ![2, 1, 1] x,
    fun x => 1 / 2 * δ ![0, 0, 1] x + 1 / 3 * δ ![0, 1, 2] x + 1 / 6 * δ ![2, 1, 2] x,
    fun x => 2 / 5 * δ ![0, 0, 2] x + 7 / 15 * δ ![0, 1, 1] x + 2 / 15 * δ ![2, 0, 1] x,
    fun x => 1 / 3 * δ ![0, 0, 2] x + 1 / 2 * δ ![0, 1, 1] x + 1 / 6 * δ ![2, 0, 2] x,
    fun x => 1 / 2 * δ ![0, 0, 2] x + 1 / 3 * δ ![0, 1, 1] x + 1 / 6 * δ ![2, 1, 1] x,
    fun x => 4 / 9 * δ ![0, 0, 2] x + 1 / 3 * δ ![0, 1, 1] x + 2 / 9 * δ ![2, 1, 2] x,
    fun x => 1 / 6 * δ ![0, 0, 2] x + 7 / 12 * δ ![0, 1, 2] x + 1 / 4 * δ ![2, 0, 1] x,
    fun x => 5 / 12 * δ ![0, 0, 2] x + 1 / 3 * δ ![0, 1, 2] x + 1 / 4 * δ ![2, 1, 1] x,
    fun x => 1 / 3 * δ ![0, 0, 2] x + 1 / 3 * δ ![0, 1, 2] x + 1 / 3 * δ ![2, 1, 2] x,
    fun x => 2 / 3 * δ ![0, 1, 2] x + 1 / 3 * δ ![2, 0, 2] x]

/-- Kuhn's two basic optimal mixed strategies for player II (p. 100). -/
noncomputable def basic₂ : Fin 2 → (Fin 3 → Fin 4) → ℝ :=
  ![fun y => 1 / 3 * δ ![0, 0, 3] y + 1 / 3 * δ ![0, 1, 3] y + 1 / 3 * δ ![2, 0, 3] y,
    fun y => 2 / 3 * δ ![0, 0, 3] y + 1 / 3 * δ ![2, 1, 3] y]

/-- The value of the game with ante `a` and bet `b` (Kuhn, pp. 102–103: Cases 1–3 as printed, Case 4 at
`b = 2a`; and `0` throughout `b ≥ 2a`). -/
noncomputable def kuhnValue (a b : ℝ) : ℝ :=
  if b ≤ a then -(b ^ 2) / (6 * (2 * a + b))
  else if b ≤ 2 * a then -(b * (2 * a - b)) / (6 * (2 * a + b))
  else 0

end KuhnPoker
