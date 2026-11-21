# Pólya–Vinogradov Lean sources

This folder is copied from creelie/breakthrough-problems-3, directory `lean/`, Apache License 2.0. `NOTICE` lists the third-party parts and their sources:
- OpenAI's library `OAI/`, which contains the zero-free half-plane Re s > 7/8
- PrimeNumberTheoremAnd
- rellich-kondrachov

The Lean toolchain is v4.34.1 (`lean/lean-toolchain`). Build with `cd lean && lake exe cache get && lake build`. Then `lake env lean Axioms.lean` prints the axioms of every main theorem, among them `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` and `Vinogradov.PV.polya_vinogradov_loglog`.

These files back the result in Section 20 of preprint v7 that does not assume the Riemann hypothesis.
