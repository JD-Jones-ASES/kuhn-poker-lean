module

import Solution
import Lean.Util.CollectAxioms

/-!
# Axiom audit

A module file importing `Solution` (not `Challenge.lean`). Walks every constant of the environment
whose name begins with `KuhnPoker.`, `_private.KuhnPoker.` or `_private.Solution.` (the public declarations of
this development; the private auxiliaries that Lean generates are not enumerated under the module
system, but `collectAxioms` reaches every private constant a public proof refers to, including a
private `axiom`), and collects the axioms each depends on. Anything outside `propext`,
`Classical.choice`, `Quot.sound` is reported with `logError`, which fails `lake build`. The audit
also fails if it matched fewer constants than the floor below (so a renamed namespace cannot make it
pass vacuously) or if any of the compared theorems is missing from the environment.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in env.constants.toList do
    let label := name.toString
    if label.startsWith "KuhnPoker." || label.startsWith "_private.KuhnPoker." ||
        label.startsWith "_private.Solution." then
      checked := checked + 1
      let axs ← collectAxioms name
      for ax in axs do
        unless allowed.contains ax do
          rejected := rejected + 1
          logError m!"Unexpected axiom dependency: {name} -> {ax}"
  unless checked ≥ 190 do
    logError m!"Axiom audit matched only {checked} project constants; expected at least 190"
  for n in [`KuhnPoker.hasValue_one_one, `KuhnPoker.hasValue_unique,
      `KuhnPoker.exists_isEquilibrium, `KuhnPoker.payoff_of_isEquilibrium,
      `KuhnPoker.isEquilibrium_iff, `KuhnPoker.guarantees₂_iff, `KuhnPoker.guarantees₁_iff,
      `KuhnPoker.essentialMatrix_eq, `KuhnPoker.basic₁_guarantees,
      `KuhnPoker.basic₂_guarantees, `KuhnPoker.hasMixedValue, `KuhnPoker.guaranteesMixed₁_iff,
      `KuhnPoker.guaranteesMixed₂_iff, `KuhnPoker.hasValue_general,
      `KuhnPoker.kuhnValue_one_one, `KuhnPoker.guarantees_case_one,
      `KuhnPoker.guarantees_case_three, `KuhnPoker.guarantees_case_four,
      `KuhnPoker.upper_certificate, `KuhnPoker.lower_certificate,
      `KuhnPoker.isEquilibrium_iff_explicit, `KuhnPoker.case_one_I_unique,
      `KuhnPoker.case_one_II_iff, `KuhnPoker.diagonal_II_unique, `KuhnPoker.diagonal_I_iff,
      `KuhnPoker.case_three_I_unique, `KuhnPoker.case_three_II_iff,
      `KuhnPoker.case_three_II_set, `KuhnPoker.case_three_printed_interval,
      `KuhnPoker.case_three_printed_upper_end_fails, `KuhnPoker.case_four_I_iff,
      `KuhnPoker.case_four_II_iff, `KuhnPoker.boundary_II_certificate,
      `KuhnPoker.boundary_II_iff, `KuhnPoker.payoff_of_isEquilibrium_general,
      `KuhnPoker.isEquilibrium_general_iff, `KuhnPoker.boundary_isEquilibrium_iff] do
    unless env.contains n do
      logError m!"Compared theorem is missing from the environment: {n}"
  logInfo m!"Audited {checked} project constants; unexpected axiom dependencies: {rejected}."
