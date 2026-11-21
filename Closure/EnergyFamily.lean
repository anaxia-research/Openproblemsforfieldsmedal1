/-
  The family energy principle (Section 19 of "The Riemann Hypothesis Is the
  Exponent of One Positive Energy", v7, D. Bhattacharjee and U. Bhattacharya).

  The one-sided Landau step `Formalism.HC.Landau.landau_family` and the
  definitions `Formalism.Gz`, `Formalism.Gchi`, `Formalism.HC.PChar` are taken
  from L. Alpöge's Lean project (alpo.ge/lean.tar.gz, November 2026), whose
  authorship is his. This file restates them in the paper's notation and
  derives Hypothesis W ⇒ RH and GRH.
-/
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Landau
import Formalism.GammaFactorNonvanishing.RhOfRight

open Complex DirichletCharacter

noncomputable section

namespace LiouvilleEnergy.Family

open Formalism Formalism.HC

/-- A family: a finite multiset of non-trivial primitive characters, closed under
conjugation, together with `R ≥ 1` copies of the trivial character. -/
structure EnergyFamily where
  ι : Type
  c : ι → PChar
  τ : ι → ι
  τ_invol : ∀ i, τ (τ i) = i
  τ_inv : ∀ i, c (τ i) = (c i).inv
  S : Finset ι
  nontriv : ∀ ξ ∈ S, (c ξ).χ ≠ 1
  closed : ∀ ξ ∈ S, τ ξ ∈ S
  R : ℕ
  R_ne : R ≠ 0

/-- The family energy `E_F(y) = R G₁(y) + Σ_{χ ∈ F} G_χ(y)`. -/
def E (F : EnergyFamily) (y : ℝ) : ℝ := F.R * Gz y + ∑ ξ ∈ F.S, Gchi (F.c ξ).χ y

/-- Theorem 19.2(i): a one-sided growth bound for the family energy gives a
zero-free half-plane for ζ and every L-function of the family. -/
theorem family_energy_principle (F : EnergyFamily) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1)
    {C y0 : ℝ} (hb : ∀ y ≥ y0, E F y ≤ C * y ^ θ) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 ∧ ∀ ξ ∈ F.S, LFunction (F.c ξ).χ s ≠ 0 :=
  Landau.landau_family F.c F.τ F.τ_invol F.τ_inv F.S F.nontriv F.closed F.R F.R_ne θ h0 h1 C y0 hb

/-- Hypothesis W (Definition 19.4): every primitive character lies in a family whose
energy is at most `y^{1/2+ε}` for every `ε`. -/
def HypothesisW : Prop :=
  ∀ ψ : PChar, ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
    ∃ F : EnergyFamily, (ψ.χ = 1 ∨ ∃ ξ ∈ F.S, F.c ξ = ψ) ∧
      ∃ C y0 : ℝ, ∀ y ≥ y0, E F y ≤ C * y ^ ((1 : ℝ) / 2 + ε)

/-- Under Hypothesis W, every primitive L-function (and ζ) is zero-free in `Re s > 1/2`. -/
theorem primitive_zero_free (hW : HypothesisW) (ψ : PChar) (s : ℂ) (hs : 1 / 2 < s.re) :
    riemannZeta s ≠ 0 ∧ (ψ.χ ≠ 1 → LFunction ψ.χ s ≠ 0) := by
  set ε : ℝ := min ((s.re - 1 / 2) / 2) (1 / 4) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε1 : ε < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hεs : 1 / 2 + ε < s.re := by
    have : ε ≤ (s.re - 1 / 2) / 2 := min_le_left _ _
    linarith
  obtain ⟨F, hψ, C, y0, hb⟩ := hW ψ ε hε0 hε1
  have key := family_energy_principle F (θ := 1 / 2 + ε) (by linarith) (by linarith) hb s hεs
  refine ⟨key.1, fun hne => ?_⟩
  rcases hψ with h | ⟨ξ, hξ, rfl⟩
  · exact absurd h hne
  · exact key.2 ξ hξ

/-- Hypothesis W implies Mathlib's Riemann hypothesis. -/
theorem riemannHypothesis_of_W (hW : HypothesisW) : RiemannHypothesis :=
  Formalism.VW.rh_of_right fun s hs _ => (primitive_zero_free hW PChar.one s hs).1

end LiouvilleEnergy.Family

