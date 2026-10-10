# The proofs, with the Lean names

The definitions are in `KuhnPoker/Defs.lean`, identical to those of `Challenge.lean`. Each Challenge theorem is the
`_internal` theorem of the same name in the module named in VERIFICATION.md, restated in `Solution.lean`. Cards
`0 < 1 < 2` are Kuhn's `1, 2, 3`; a strategy of I is `σ = (bet, call)` with `σ.1 c` the probability of betting
first and `σ.2 c` of calling after passing; a strategy of II is `τ = (betAfterPass, call)`. Write `d = 2a + b`.

## 1. The payoff as a polynomial (`KuhnPoker/Payoff.lean`, `Value.lean`)

`payoff_eq_sum`: `payoff a b σ τ` is the sum of the six `dealPayoff`s over the deals of distinct cards, divided
by six (`simp only [payoff, Fin.sum_univ_three]` with the `Fin` equalities reduced, then `ring`). After
`simp only [dealPayoff, toHigher]` with the `Fin 3` comparisons decided (`Fin.reduceLT`, `↓reduceIte`), the payoff
is an explicit polynomial in the twelve probabilities, `a` and `b`; `co_payoff_poly` states it at `a = b = 1`.
Every inequality below is proved by `linarith` after this unfolding, with the products named as `mul_nonneg`
hints — `linarith` multiplies them out, so it checks the certificate exactly; no `nlinarith` is used.

## 2. Kuhn's game (`KuhnPoker/Value.lean`)

- **The upper bound** (`upper_certificate`, `co_upper`): for every `σ`,
  `−1/18 − payoff σ kuhnII = (1 − σ.1 0)σ.2 0/6 + σ.1 1/18 + (1 − σ.1 2)(1 − σ.2 2)/6` (`ring` after unfolding);
  three nonnegative products, so `kuhnII` holds every valid `σ` to at most `−1/18`.
- **The lower bound** (`lower_certificate`, `co_lower`): for every `α, k, τ`,
  `payoff (kuhnI α k) τ + 1/18 = α/2·τ.2 0 + α/2·(1 − τ.2 2) + (1/3 − α)/2·τ.1 1 + (1/18 + α/6)(1 − τ.1 2)
  − (1 − 3α)(1 − k)(τ.1 0 + τ.1 1)/2`; under `3α = 1 ∨ k = 1` the tail vanishes and the four products are
  nonnegative for `α ∈ [0, 1/3]` and valid `τ`. At `τ = kuhnII` both identities give the family's shortfall
  `(1 − 3α)(1 − k)/6`, which is why the clause is needed.
- **II unique** (`co_II_unique`): the guarantee at I's pure strategies (bet 1, fold 2, call 3),
  (fold, call, call) and (fold, fold, bet 3) gives three linear inequalities in `τ`'s six coordinates; with the
  box, six `linarith` calls pin all six; `Prod.ext`, `funext`, `fin_cases` close `τ = kuhnII`.
- **I's family** (`co_I_family`): the guarantee at II's pure strategies `(![0,0,1], ![0,0,1])`,
  `(![1,0,1], ![0,0,1])`, `(![0,0,1], ![0,1,1])` (bets after a pass; calls), with the six products
  `(1 − σ.1 c)σ.2 c ≥ 0` and `(1 − σ.1 c)(1 − σ.2 c) ≥ 0`, gives by `linarith` `σ.1 1 = 0`, `σ.1 2 = 3σ.1 0`,
  `σ.1 0 ≤ 1/3`, `(1 − σ.1 0)σ.2 0 = 0`, `(1 − σ.1 1)σ.2 1 = σ.1 0 + 1/3`, `(1 − σ.1 2)(1 − σ.2 2) = 0`;
  `mul_eq_zero` twice (the first factor of the first product is positive since `σ.1 0 ≤ 1/3`), with
  `α := σ.1 0`, `k := σ.2 2`.
- **Assembly.** `hasValue_one_one` from the two bounds with `kuhnI 0 1`; `hasValue_unique` (every `a, b`) by
  `le_antisymm` of the sandwiches `v ≤ payoff σ τ' ≤ w`; `exists_isEquilibrium` with `(kuhnI 0 1, kuhnII)`;
  `payoff_of_isEquilibrium` by `payoff σ τ ≤ payoff σ kuhnII ≤ −1/18` and `−1/18 ≤ payoff (kuhnI 0 1) τ ≤
  payoff σ τ`; `isEquilibrium_iff` from it (`co_isEquilibrium_of` for the converse); `guarantees₂_iff`,
  `guarantees₁_iff` and `isEquilibrium_iff_explicit` by rewriting with the pieces above.

## 3. The normal form (`KuhnPoker/NormalForm.lean`)

`nf_F B C u v` is the payoff in sequence form — `B c` the probability of betting first, `C c` of passing then
calling, `u`, `v` II's bets and calls — an explicit polynomial; `nf_payoff_eq`:
`payoff 1 1 σ τ = nf_F σ.1 ((1 − σ.1)σ.2) τ.1 τ.2`, and `nf_payoff_pure` the same on pure strategies with the
indicator atoms `[x c = 2]`, `[x c = 1]`, `[2 ≤ y c]`, `[y c = 1 ∨ y c = 3]`. **The affine bridge**
(`nf_sum_left`, `nf_sum_right`, `nf_bridge`): `nf_F` is affine in each player's atoms, so for probability vectors
`Σ_x p x · nf_F (B x) (C x) u v = nf_F (Σ p B) (Σ p C) u v` (expand the summand as a constant plus atom-times-
coefficient terms, `Finset.sum_add_distrib`, `← Finset.sum_mul`, `Σ p = 1`), hence
`mixedPayoff p q = nf_F (realBet p) (realCall p) (margBet q) (margCall q)`. **The sequence-form certificates:**
on the segment, `nf_F + 1/18 = (α/2)v₀ + (α/2)(1 − v₂) + ((1/3 − α)/2)u₁ + (1/18 + α/6)(1 − u₂)`
(`nf_lower_seq`; the `(1 − 3α)(1 − k)` tail of §2 vanishes identically because the fold atom with the `3` is
`1 − B₂ − C₂ = 0`), and against `kuhnII`, `−1/18 − nf_F = B₁/18 + C₀/6 + (1 − B₂ − C₂)/6` (`nf_upper_seq`).

- `essentialMatrix_eq`: `rw [nf_payoff_pure]`, `fin_cases i <;> fin_cases j <;> norm_num [...]`, 32 entries.
- `basic₁_guarantees`, `basic₂_guarantees`, `hasMixedValue`: each basic strategy is a two- or three-point
  mixture (`nf_isProb_mix2/3`); its plan is the segment point at Kuhn's `α` (A 0, B 1/6, C 1/9, D 1/6, E 2/15,
  F 1/6, G 1/6, H 2/9, I 1/4, J 1/4, K 1/3, L 1/3) or II's marginals are `kuhnII`'s; the bridge and the
  sequence-form certificates finish.
- `guaranteesMixed₁_iff`: (→) the guarantee at the point masses `δ ![0,0,3]`, `δ ![2,0,3]`, `δ ![0,1,3]`,
  the bridge, the plan box (`0 ≤ realBet, realCall`, sum `≤ 1`), six `linarith` calls, `α := realBet p 0`;
  (←) the bridge and `nf_lower_seq` with the marginal box. `guaranteesMixed₂_iff`: likewise with `δ ![2,0,1]`,
  `δ ![0,1,1]`, `δ ![0,0,2]` and `nf_upper_seq`.

## 4. Every ante and bet (`KuhnPoker/General.lean`)

`kuhnValue a b` unfolds by the case hypotheses (`gn_value_case_one/three/four`; at `b = a` and `b = 2a` the two
adjacent formulas agree, by `split_ifs`, `subst`, `ring`). Validity of each witness from `gn_frac_mem`
(`n/d ∈ [0, 1]` for `0 ≤ n ≤ d`). The witness coordinates `b/d`, `2a/d`, `(2a − b)/d` are generalized to
variables with the facts `d·p = b` etc. (`mul_div_cancel₀`), denominators cleared by `div_le_iff₀` /
`le_div_iff₀`, the payoff unfolded, and `linarith` closes with two to five product hints. The certificates
(with `s_c = (1 − x_c)y_c`, `f_c = (1 − x_c)(1 − y_c)` for I's strategy `(x, y)` and `(u, v)` for II's):

| Case, side | Identity (every term on the right a product of nonnegative factors) |
| --- | --- |
| 4, I | `6·payoff = (b − 2a)u₀ + b·u₁` |
| 4, II | `−6·payoff = (b − 2a)x₀ + b·s₀ + b·x₁ + b·s₁` |
| 1, I | `6d·payoff + b² = bd·v₀ + 2ab(1 − u₂) + bd(1 − v₂)` (every `a, b > 0`, every call `k` with the `3`) |
| 1, II | `−b² − 6d·payoff = bd(1 + ξ)s₀ + b²x₁ + (b(4a − b) + 2adξ)f₂ + b(2(a − b) − dξ)s₂` (`ξ` the bet with the `2` after a pass) |
| 3, I | `6d·payoff + b(2a − b) = bd·u₁ + b(2a − b)(1 − u₂)` (needs only `b ≤ 2a`) |
| 3, II | `−b(2a − b) − 6d·payoff = d(dη − (2a − b))x₀ + bd·s₀ + b²x₁ + b(b − dη)x₂ + bd·f₂` (`gn_case_three_II_identity`) |

`hasValue_general` splits on `b ≤ a`, then `b ≤ 2a`, with the Case 3 witness at `η = b/d`. **The diagonal**
(`diagonal_I_iff`): `payoff a a σ τ = a · payoff 1 1 σ τ` (`gn_payoff_scale`, by unfolding and `ring`) and
`kuhnValue a a = a · (−1/18)`, so for `a > 0` the guarantee at scale `a` is the guarantee of Kuhn's game, and
`guarantees₁_iff` finishes. **The optimal sets** (`case_one_I_unique`, `case_three_I_unique`, `case_one_II_iff`,
`diagonal_II_unique`, `case_four_I_iff`, `case_four_II_iff`, `case_three_II_set`, `case_three_II_iff`,
`case_three_printed_interval`, `case_three_printed_upper_end_fails`): each "only if" instantiates the guarantee
at two to five pure strategies of the opponent, combines the resulting linear inequalities with coefficients polynomial in `a`, `b` (supplied
as `mul_nonneg` products to `linarith only`), and divides out the positive factors
(`nonneg_of_mul_nonneg_right`, `nonpos_of_mul_nonpos_right`); for instance, with `I` and `II` the two derived
quantities `HI` and `HII` of `case_three_I_unique` (each `≥ 0`), `(2a − b)·I + II = −2[ab·x₁ + ad·s₀ + 2a(b − a)x₂ +
ad·f₂]` forces I's Case 3 strategy. The sharpness of the
corrected interval: below `(2a − b)/d` I gains by betting the `1`, above `b/d` by betting the `3` first; on
Kuhn's printed interval only its lower end `b/d` survives, and `η = 5/7` at `a = 2, b = 3` is the concrete failure.
II's optimal set on the line `b = 2a` is §5.

## 5. The line `b = 2a`, and the equilibria at every ante and bet (`KuhnPoker/Boundary.lean`, `Equilibrium.lean`)

II's strategy is `(u, v)` as in §4 (bets after a pass, calls), I's `(x, y)` (bets first, calls). **The identity**
(`boundary_II_certificate`), for every `a` and every pair with `u₁ = 0`:
`−3·payoff a (2a) (x, y) (u, v) = a·[2x₀(v₁ + v₂ − 1) + (1 − x₀)y₀u₂ + x₁(2v₂ − 1 − u₀ − v₀) + (1 − x₁)y₁(u₂ − 2u₀)
+ x₂(u₀ − v₀ − v₁) + 2(1 − x₂)(1 − y₂)u₀]` (`payoff_eq_sum`, the unfolding, `ring`). **The set** (`boundary_II_iff`): II
guarantees `0` iff valid, `u₁ = 0`, `2u₀ ≤ u₂`, `v₀ + v₁ ≤ u₀`, `1 ≤ v₁ + v₂`, `1 + u₀ + v₀ ≤ 2v₂`. "Only if": I's pure
strategy fold–fold–call (Kuhn's `(0, 0, 1)`) earns `a·u₁/3`, so `u₁ = 0`; then `(0, 1, 1)`, `(0, 0, 2)`, `(2, 0, 1)`
and `(0, 2, 1)` earn `a(2u₀ − u₂)/3`, `a(v₀ + v₁ − u₀)/3`, `2a(1 − v₁ − v₂)/3`, `a(1 + u₀ + v₀ − 2v₂)/3`, one
inequality each (`linarith only`; `a` divided out by `nonpos_of_mul_nonpos_right`). "If": under the four inequalities
and validity each of the six products is nonnegative, so the identity gives `payoff ≤ 0` (`linarith only` over six
`mul_nonneg` facts). The polytope has dimension five (interior point `(u₀, u₂, v₀, v₁, v₂) = (3/10, 4/5, 3/100, 3/20, 9/10)`)
and nine vertices — `(0,0,0,0,1)`, `(0,1,0,0,1)`, `(1/3,2/3,0,1/3,2/3)`, `(1/3,1,0,1/3,2/3)`, `(1/2,1,0,0,1)`,
`(1/2,1,0,1/4,3/4)`, `(1/2,1,0,1/2,3/4)`, `(1/2,1,0,1/2,1)`, `(1/2,1,1/2,0,1)` — replayed by `scripts/check_boundary.py`,
not stated. The neighbouring theorems' limits are faces of it: `case_three_II_set` as `b → 2a⁻` gives the face
`u₀ = 1/2` (on it `u₂ = 1`, and the three inequalities become `v₀ + v₁ ≤ 1/2`, `1 ≤ v₁ + v₂`, `3 + 2v₀ ≤ 4v₂`),
`case_four_II_iff` as `b → 2a⁺` the edge `u₀ = 0` (on it `v₀ = v₁ = 0`, `v₂ = 1`, `u₂` free) between the first two
vertices; two vertices lie in neither.

**The equilibria at every ante and bet.** `payoff_of_isEquilibrium_general`: for an equilibrium `(σ, τ)` and the
witnesses `(σ₀, τ₀)` of `hasValue_general`, `payoff σ τ ≤ payoff σ τ₀ ≤ v ≤ payoff σ₀ τ ≤ payoff σ τ`
(`le_antisymm`). `isEquilibrium_general_iff`: from it each strategy guarantees the value; the converse is
`co_isEquilibrium_of`. `boundary_isEquilibrium_iff`: `isEquilibrium_general_iff` at `b = 2a`, I's side by
`case_three_I_unique` (whose strategy is `(0, 0, 0; 0, 0, 1)` there — `sub_self`, `zero_div`), II's by
`boundary_II_iff`, the value `0` by `gn_value_case_four`. With §4's optimal sets this makes the equilibria explicit
in every region: the pairs of optimal strategies.
