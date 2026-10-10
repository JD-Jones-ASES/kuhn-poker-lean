module

public import Mathlib

/-!
# Kuhn poker (Kuhn 1950): the value −1/18, the second player's unique optimal strategy, the first player's
optimal set, the normal form, and the value at every ante and bet

H. W. Kuhn, *A simplified two-person poker*, Contributions to the Theory of Games I, Annals of Mathematics
Studies 24 (1950), 97–103. Three cards `1 < 2 < 3` (here `0 < 1 < 2 : Fin 3`), one dealt to each player, the six
deals equiprobable; an ante of `a` from each player and a single bet of `b` (Kuhn's game has `a = b = 1`). Player I
acts first: bet or pass. After a pass, II bets or passes; after II's bet, I calls (bets) or passes (folds).
After I's bet, II calls or folds. The five courses of play (p. 98) and their payoffs to I: (1) pass, pass — `a`
to the holder of the higher card; (2) pass, bet, pass — `a` to II; (3) pass, bet, bet — `a + b` to the holder of
the higher card; (4) bet, pass — `a` to I; (5) bet, bet — `a + b` to the holder of the higher card.

A *behaviour strategy* of I assigns to each card the probability of betting in the first round and the
probability of calling in the second round (after passing and facing a bet); one of II assigns to each card the
probability of betting when confronted by a pass and the probability of calling when confronted by a bet. This
file states, and `Solution.lean` proves (kernel-only), for Kuhn's game `a = b = 1`:

* the value is `−1/18`: both players can guarantee it (`hasValue_one_one`; a game has at most one value,
  `hasValue_unique`), an equilibrium (saddle point) exists, every equilibrium pays I exactly `−1/18`, and a
  pair is an equilibrium iff each strategy guarantees the value (`exists_isEquilibrium`,
  `payoff_of_isEquilibrium`, `isEquilibrium_iff`);
* II's optimal behaviour strategy is unique at all six information sets: bet after a pass with the `1`, `2`, `3`
  with probabilities `1/3, 0, 1`; call a bet with probabilities `0, 1/3, 1` (`guarantees₂_iff`; Kuhn's
  `(ξ, η) = (1/3, 1/3)` on p. 102, with the four coordinates he removed as superfluous now proved forced);
* I's optimal behaviour strategies are exactly, for some `α ∈ [0, 1/3]`: bet the `1` with probability `α` and
  fold it to a bet; never bet the `2` first and call with it with probability `α + 1/3`; bet the `3` with
  probability `3α` and call with it — the call with the `3` being unconstrained exactly when `3α = 1`, where that
  information set is never reached (`guarantees₁_iff`; Kuhn's one-parameter family `α = γ/3, β = γ/3 + 1/3`,
  `0 ≤ γ ≤ 1` on p. 101, with `γ = 3α`);
* the normal form: with Kuhn's coding of the `27` pure strategies of I and `64` of II (p. 98), the entries of his
  "essential" `8 × 4` matrix (p. 99) are six times the payoffs (`essentialMatrix_eq`); his twelve basic optimal
  mixed strategies (A)–(L) for I and two for II (p. 100) guarantee `−1/18` (`basic₁_guarantees`,
  `basic₂_guarantees`, `hasMixedValue`); and a mixed strategy is optimal iff its realization plan lies on the
  segment above (I) or its marginals are II's unique strategy (II) (`guaranteesMixed₁_iff`,
  `guaranteesMixed₂_iff`); Kuhn's form of these sets, the convex hulls of his twelve and two strategies, is
  replayed in `scripts/check_kuhn.py` and is not a theorem here;

and for every ante `a > 0` and bet `b > 0` (Kuhn's pp. 102–103, stated there "without proof", and the region
`b > 2a` he does not state):

* the value is `−b²/(6(2a + b))` for `b ≤ a`, `−b(2a − b)/(6(2a + b))` for `a ≤ b ≤ 2a`, and `0` for `b ≥ 2a`
  (`hasValue_general`, `kuhnValue_one_one`), with explicit guaranteeing strategies in each case
  (`guarantees_case_one`, `guarantees_case_three`, `guarantees_case_four`). In Case 3 the calling probability
  `η` with the `2` ranges over `[(2a − b)/(2a + b), b/(2a + b)]`; the interval printed on p. 102,
  `b/(2a + b) ≤ η ≤ (a + b)/(2a + b)`, holds only at its lower end (at `a = 2, b = 3`, `η = 5/7` lets I gain);
* beyond Kuhn: the two certificate identities (`upper_certificate`, `lower_certificate`); the equilibria explicitly
  (`isEquilibrium_iff_explicit`); the exact optimal sets at every ante and bet — I's in every region (`case_one_I_unique`,
  `diagonal_I_iff`, `case_three_I_unique`, `case_four_I_iff`) and II's off the line `b = 2a` (`case_one_II_iff`,
  `diagonal_II_unique`, `case_three_II_set`, `case_four_II_iff`); the corrected Case 3 interval is sharp and the printed
  one holds only at its lower end (`case_three_II_iff`, `case_three_printed_interval`,
  `case_three_printed_upper_end_fails`).

The definitions are built from the game tree; no imported library holds the game. All proofs are over `ℝ` with the
probabilities as real variables; every guarantee is a finite nonnegative-product identity (the gap between the
value and the payoff is a sum of products of probabilities, their complements and case factors, with coefficients
nonnegative on the case's region: rational constants at `a = b = 1`, polynomials in `a`, `b` and the free parameter
at general stakes), and the "only if" directions are linear certificates from finitely many pure strategies.
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

/-! ### Kuhn's game: the value −1/18 -/

/-- Kuhn's game has value `−1/18`. -/
theorem hasValue_one_one : HasValue 1 1 (-1 / 18) := sorry

/-- A game has at most one value. -/
theorem hasValue_unique (a b v w : ℝ) (hv : HasValue a b v) (hw : HasValue a b w) : v = w := sorry

/-- An equilibrium exists. -/
theorem exists_isEquilibrium : ∃ σ τ, IsEquilibrium 1 1 σ τ := sorry

/-- Every equilibrium pays I exactly `−1/18`. -/
theorem payoff_of_isEquilibrium (σ : Strategy₁) (τ : Strategy₂) (h : IsEquilibrium 1 1 σ τ) :
    payoff 1 1 σ τ = -1 / 18 := sorry

/-- A pair is an equilibrium iff each strategy guarantees the value (the exchangeability of optimal
strategies in a zero-sum game). -/
theorem isEquilibrium_iff (σ : Strategy₁) (τ : Strategy₂) :
    IsEquilibrium 1 1 σ τ ↔ Guarantees₁ 1 1 σ (-1 / 18) ∧ Guarantees₂ 1 1 τ (-1 / 18) := sorry

/-! ### The optimal sets -/

/-- Player II's optimal strategy is unique: Kuhn's `(ξ, η) = (1/3, 1/3)` with the forced coordinates. -/
theorem guarantees₂_iff (τ : Strategy₂) : Guarantees₂ 1 1 τ (-1 / 18) ↔ τ = kuhnII := sorry

/-- Player I's optimal strategies are exactly Kuhn's family: `kuhnI α k` with `α ∈ [0, 1/3]`, where the call
with the `3` is forced (`k = 1`) unless `3α = 1`, in which case it is unconstrained. -/
theorem guarantees₁_iff (σ : Strategy₁) : Guarantees₁ 1 1 σ (-1 / 18) ↔
    ∃ α ∈ Set.Icc (0 : ℝ) (1 / 3), ∃ k ∈ Set.Icc (0 : ℝ) 1, (3 * α = 1 ∨ k = 1) ∧ σ = kuhnI α k := sorry

/-! ### The normal form -/

/-- Kuhn's essential matrix is six times the game matrix on his rows and columns. -/
theorem essentialMatrix_eq (i : Fin 8) (j : Fin 4) :
    6 * payoff 1 1 (pure₁ (essentialRow i)) (pure₂ (essentialCol j)) = essentialMatrix i j := sorry

/-- Each of Kuhn's twelve basic strategies (A)–(L) guarantees `−1/18`. -/
theorem basic₁_guarantees (i : Fin 12) : GuaranteesMixed₁ (basic₁ i) (-1 / 18) := sorry

/-- Each of Kuhn's two basic strategies for II guarantees `−1/18`. -/
theorem basic₂_guarantees (i : Fin 2) : GuaranteesMixed₂ (basic₂ i) (-1 / 18) := sorry

/-- The normal form has value `−1/18`. -/
theorem hasMixedValue : HasMixedValue (-1 / 18) := sorry

/-- A mixed strategy of I is optimal iff it is a probability vector whose realization plan lies on Kuhn's
segment: bet first with probabilities `(α, 0, 3α)` and pass-then-call with probabilities
`(0, α + 1/3, 1 − 3α)`, for some `α ∈ [0, 1/3]`. -/
theorem guaranteesMixed₁_iff (p : (Fin 3 → Fin 3) → ℝ) : GuaranteesMixed₁ p (-1 / 18) ↔
    IsProb p ∧ ∃ α ∈ Set.Icc (0 : ℝ) (1 / 3),
      realBet p = ![α, 0, 3 * α] ∧ realCall p = ![0, α + 1 / 3, 1 - 3 * α] := sorry

/-- A mixed strategy of II is optimal iff it is a probability vector whose marginals are Kuhn's unique
strategy. -/
theorem guaranteesMixed₂_iff (q : (Fin 3 → Fin 4) → ℝ) : GuaranteesMixed₂ q (-1 / 18) ↔
    IsProb q ∧ margBet q = ![1 / 3, 0, 1] ∧ margCall q = ![0, 1 / 3, 1] := sorry

/-! ### Every ante and bet -/

/-- The value at every ante `a > 0` and bet `b > 0`. -/
theorem hasValue_general (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : HasValue a b (kuhnValue a b) := sorry

/-- Kuhn's game is the case `a = b = 1`. -/
theorem kuhnValue_one_one : kuhnValue 1 1 = -1 / 18 := sorry

/-- Case 1, `b ≤ a` (p. 102): I bets the `1` with probability `b/(2a + b)`, never bets the `2` first, always
bets the `3`, and calls with the `2` with probability `2a/(2a + b)`; II bets the `1` after a pass with
probability `b/(2a + b)` and calls with the `2` with probability `(2a − b)/(2a + b)`. -/
theorem guarantees_case_one (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) :
    Guarantees₁ a b (![b / (2 * a + b), 0, 1], ![0, 2 * a / (2 * a + b), 1]) (kuhnValue a b) ∧
    Guarantees₂ a b (![b / (2 * a + b), 0, 1], ![0, (2 * a - b) / (2 * a + b), 1]) (kuhnValue a b) := sorry

/-- Case 3, `a ≤ b ≤ 2a` (p. 102, the interval for `η` corrected): I never bets first and calls with the `2`
with probability `(2a − b)/(2a + b)`; II bets the `1` after a pass with probability `b/(2a + b)` and calls
with the `2` with any probability `η ∈ [(2a − b)/(2a + b), b/(2a + b)]`. -/
theorem guarantees_case_three (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (hb2 : b ≤ 2 * a)
    (η : ℝ) (hη : η ∈ Set.Icc ((2 * a - b) / (2 * a + b)) (b / (2 * a + b))) :
    Guarantees₁ a b (![0, 0, 0], ![0, (2 * a - b) / (2 * a + b), 1]) (kuhnValue a b) ∧
    Guarantees₂ a b (![b / (2 * a + b), 0, 1], ![0, η, 1]) (kuhnValue a b) := sorry

/-- Case 4, `b ≥ 2a` (p. 103 at `b = 2a`, and beyond): I never bets first and calls only with the `3`; II bets
after a pass only with the `3` and calls only with the `3`; the value is `0`. -/
theorem guarantees_case_four (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 2 * a ≤ b) :
    Guarantees₁ a b (![0, 0, 0], ![0, 0, 1]) 0 ∧ Guarantees₂ a b (![0, 0, 1], ![0, 0, 1]) 0 := sorry

/-! ### The certificates, the equilibrium set, and the optimal sets at every ante and bet -/

/-- The upper-bound certificate, as an identity for every strategy of I (valid or not): `−1/18` minus the payoff against `kuhnII` is a sum of three products, nonnegative whenever `σ` is valid, so `kuhnII` holds every valid strategy to at most `−1/18`. -/
theorem upper_certificate (σ : Strategy₁) :
    -1 / 18 - payoff 1 1 σ kuhnII =
      (1 - σ.1 0) * σ.2 0 / 6 + σ.1 1 / 18 + (1 - σ.1 2) * (1 - σ.2 2) / 6 := sorry

/-- The lower-bound certificate, as an identity for every `α`, `k` and every strategy of II (valid or not): the payoff of `kuhnI α k` plus `1/18` is four products, nonnegative for `α ∈ [0, 1/3]` and valid `τ`, minus a tail carrying the factor `(1 − 3α)(1 − k)`; the tail vanishes exactly under the clause of `guarantees₁_iff`. -/
theorem lower_certificate (α k : ℝ) (τ : Strategy₂) :
    payoff 1 1 (kuhnI α k) τ + 1 / 18 =
      α / 2 * τ.2 0 + α / 2 * (1 - τ.2 2) + (1 / 3 - α) / 2 * τ.1 1 + (1 / 18 + α / 6) * (1 - τ.1 2)
      - (1 - 3 * α) * (1 - k) * (τ.1 0 + τ.1 1) / 2 := sorry

/-- The equilibria of Kuhn's game, explicitly: the pairs `(kuhnI α k, kuhnII)` with `α ∈ [0, 1/3]`, `k ∈ [0, 1]` and `3α = 1 ∨ k = 1`. -/
theorem isEquilibrium_iff_explicit (σ : Strategy₁) (τ : Strategy₂) :
    IsEquilibrium 1 1 σ τ ↔
      (∃ α ∈ Set.Icc (0 : ℝ) (1 / 3), ∃ k ∈ Set.Icc (0 : ℝ) 1, (3 * α = 1 ∨ k = 1) ∧ σ = kuhnI α k) ∧
        τ = kuhnII := sorry

/-- Case 1 off the diagonal, `b < a`: I's optimal strategy is unique up to the call with the `3`, which is never reached (I always bets the `3`); Kuhn's one-parameter family exists only at `b = a`. -/
theorem case_one_I_unique (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b < a) (σ : Strategy₁) :
    Guarantees₁ a b σ (kuhnValue a b) ↔
      ∃ k ∈ Set.Icc (0 : ℝ) 1, σ = (![b / (2 * a + b), 0, 1], ![0, 2 * a / (2 * a + b), k]) := sorry

/-- Case 1, `b ≤ a`: II's optimal strategies are exactly Kuhn's, with the bet with the `2` after a pass free in `[0, 2(a − b)/(2a + b)]` — so Kuhn's "both players have a unique optimal mode of behavior" (p. 102) holds for his reduced parameters only. -/
theorem case_one_II_iff (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (τ : Strategy₂) :
    Guarantees₂ a b τ (kuhnValue a b) ↔
      ∃ ξ ∈ Set.Icc (0 : ℝ) (2 * (a - b) / (2 * a + b)),
        τ = (![b / (2 * a + b), ξ, 1], ![0, (2 * a - b) / (2 * a + b), 1]) := sorry

/-- On the diagonal `a = b` (Kuhn's game at every scale), II's optimal strategy is unique. -/
theorem diagonal_II_unique (a : ℝ) (ha : 0 < a) (τ : Strategy₂) :
    Guarantees₂ a a τ (kuhnValue a a) ↔ τ = (![1 / 3, 0, 1], ![0, 1 / 3, 1]) := sorry

/-- On the diagonal `a = b` (Kuhn's game at every scale), I's optimal strategies are Kuhn's family, with the
unreached-set clause of `guarantees₁_iff`. -/
theorem diagonal_I_iff (a : ℝ) (ha : 0 < a) (σ : Strategy₁) :
    Guarantees₁ a a σ (kuhnValue a a) ↔
      ∃ α ∈ Set.Icc (0 : ℝ) (1 / 3), ∃ k ∈ Set.Icc (0 : ℝ) 1, (3 * α = 1 ∨ k = 1) ∧ σ = kuhnI α k := sorry

/-- Case 3 off the diagonal, `a < b ≤ 2a`: I's optimal strategy is unique. -/
theorem case_three_I_unique (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hb2 : b ≤ 2 * a)
    (σ : Strategy₁) :
    Guarantees₁ a b σ (kuhnValue a b) ↔ σ = (![0, 0, 0], ![0, (2 * a - b) / (2 * a + b), 1]) := sorry

/-- The corrected Case 3 interval is sharp: with the other five coordinates of II's strategy as pinned, the calling probability `η` with the `2` guarantees the value exactly when `(2a − b)/(2a + b) ≤ η ≤ b/(2a + b)`. Below the interval I gains by betting the `1` (bluffing); above it, by betting the `3` first. -/
theorem case_three_II_iff (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (hb2 : b ≤ 2 * a) (η : ℝ) :
    Guarantees₂ a b (![b / (2 * a + b), 0, 1], ![0, η, 1]) (kuhnValue a b) ↔
      η ∈ Set.Icc ((2 * a - b) / (2 * a + b)) (b / (2 * a + b)) := sorry

/-- Case 3 below its upper boundary, `a ≤ b < 2a`: II's optimal strategies exactly — the bets after a pass are forced, and the calls form the polytope of three inequalities stated. -/
theorem case_three_II_set (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (hb2 : b < 2 * a)
    (τ : Strategy₂) :
    Guarantees₂ a b τ (kuhnValue a b) ↔ τ.IsValid ∧ τ.1 = ![b / (2 * a + b), 0, 1] ∧
      (2 * a + b) * (τ.2 0 + τ.2 1) ≤ b ∧ 4 * a ≤ (2 * a + b) * (τ.2 1 + τ.2 2) ∧
      2 * a * (2 * a + b) + 2 * a * b + b * (2 * a + b) * τ.2 0 ≤ (2 * a + b) * (2 * a + b) * τ.2 2 := sorry

/-- Kuhn's printed Case 3 interval `b/(2a + b) ≤ η ≤ (a + b)/(2a + b)` (p. 102) holds only at its lower end: there, and only there, II's strategy guarantees the value. -/
theorem case_three_printed_interval (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (hb2 : b ≤ 2 * a)
    (η : ℝ) (hη : η ∈ Set.Icc (b / (2 * a + b)) ((a + b) / (2 * a + b))) :
    Guarantees₂ a b (![b / (2 * a + b), 0, 1], ![0, η, 1]) (kuhnValue a b) ↔ η = b / (2 * a + b) := sorry

/-- At `a = 2`, `b = 3`, Kuhn's printed upper end `η = (a + b)/(2a + b) = 5/7` does not guarantee the value. -/
theorem case_three_printed_upper_end_fails :
    ¬ Guarantees₂ 2 3 (![3 / (2 * 2 + 3), 0, 1], ![0, 5 / 7, 1]) (kuhnValue 2 3) := sorry

/-- Case 4, `2a ≤ b`: I's optimal strategies exactly — never bet the `1` or the `2` first, fold them, and with the `3` bet first or pass and call with enough weight that `4a ≤ 2a·σ.1 2 + (2a + b)(1 − σ.1 2)σ.2 2` (at `b = 2a` this forces `σ.1 2 = 0`; for `b > 2a` the `3` may be bet first with probability up to `1 − 2a/b`). -/
theorem case_four_I_iff (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 2 * a ≤ b) (σ : Strategy₁) :
    Guarantees₁ a b σ 0 ↔ σ.IsValid ∧ σ.1 0 = 0 ∧ σ.1 1 = 0 ∧ σ.2 0 = 0 ∧ σ.2 1 = 0 ∧
      4 * a ≤ 2 * a * σ.1 2 + (2 * a + b) * ((1 - σ.1 2) * σ.2 2) := sorry

/-- Case 4 beyond its boundary, `2a < b`: II's optimal strategies exactly — never bet the `1` or `2` after a pass, never call with them, and call with the `3` with probability at least `4a/(2a + b)`; the bet with the `3` after a pass is free. -/
theorem case_four_II_iff (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 2 * a < b) (τ : Strategy₂) :
    Guarantees₂ a b τ 0 ↔ τ.IsValid ∧ τ.1 0 = 0 ∧ τ.1 1 = 0 ∧ τ.2 0 = 0 ∧ τ.2 1 = 0 ∧
      4 * a ≤ (2 * a + b) * τ.2 2 := sorry

end KuhnPoker
