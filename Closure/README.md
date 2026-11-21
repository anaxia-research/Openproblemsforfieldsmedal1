# Closure files for version 7

These Lean files go with Sections 18 and 19 of "The Riemann and Generalized Riemann Hypotheses from One Energy Bound" (version 7).

| File | What it proves | Builds against |
|---|---|---|
| `FunctionalEquationStep.lean` | Hypothesis H (no zeros of any Dirichlet L-function in Re s > 1/2) implies Mathlib's `RiemannHypothesis`, and GRH on the line for primitive characters | Mathlib alone |
| `MasulloRoute.lean` | Holomorphy of L′/L on Re s > 1/2 (A. M. Masullo's announced theorem) implies Hypothesis H, RH and GRH | Mathlib alone |
| `EnergyFamily.lean` | The family energy principle and Hypothesis W implies RH | L. Alpöge's project (its `Landau.lean` and `RhOfRight.lean`) |

All three use Lean 4.33.1 and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`, the pins of L. Alpöge's project. That is a different toolchain from the `LiouvilleEnergy` library in this repository, so these files are kept outside its build. For every theorem, `#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound`.

Every file is conditional. Hypotheses H and W are assumed here, not proved. Code taken from L. Alpöge's project is marked in each file header, and its authorship is his.
