/-
  The windowed energy principle (Section 21 of "RH and GRH from One Energy Bound").

  `Deduction.zeroFree_of_rpow_window`, `Deduction.CharFamily`, `Deduction.Gm` and
  `Formalism.Gchi` are from L. Alpöge's Lean project (alpo.ge/lean.tar.gz,
  November 2026), whose authorship is his. This file restates his windowed
  Landau theorem in the paper's notation and derives RH from the windowed form
  of Hypothesis W.
-/
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow
import Formalism.GammaFactorNonvanishing.RhOfRight

open Complex DirichletCharacter

noncomputable section

namespace LiouvilleEnergy.Window

open Deduction

/-- The weighted family energy `E_F(y) = Σ a_i Re G_{χ_i}(y)`. -/
abbrev E (F : CharFamily) (y : ℝ) : ℝ := Gm F y

/-- Theorem 21.1 (windowed energy principle). If the energy is at most `C y^θ` on
windows `[Y, Y^{1+δ}]` for arbitrarily large `Y`, then no member vanishes in `Re s > θ`. -/
theorem windowed_energy_principle (F : CharFamily) {θ δ C : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hδ : 0 < δ) (h : ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), E F y ≤ C * y ^ θ) :
    ∀ i, ∀ s : ℂ, θ < s.re → LFunction (F.χ i) s ≠ 0 :=
  zeroFree_of_rpow_window F hθ hθ1 hδ h

/-- The one-member family made of ζ (the trivial character mod 1). -/
def zetaFamily : CharFamily where
  ι := Unit
  N := fun _ => 1
  χ := fun _ => 1
  a := fun _ => 1
  a_pos := fun _ => one_pos
  adm := fun _ => Or.inl rfl

/-- Windowed Hypothesis W for ζ: for every `ε` the energy of ζ is at most `C y^{1/2+ε}`
on windows of some fixed width, at arbitrarily large heights. -/
def WindowW : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ δ C : ℝ, 0 < δ ∧
    ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), E zetaFamily y ≤ C * y ^ ((1 : ℝ) / 2 + ε)

theorem riemannHypothesis_of_windowW (hW : WindowW) : RiemannHypothesis := by
  refine Formalism.VW.rh_of_right fun s hs _ => ?_
  set ε : ℝ := min ((s.re - 1 / 2) / 2) (1 / 4) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
  have hε1 : ε < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hεs : 1 / 2 + ε < s.re := by
    have : ε ≤ (s.re - 1 / 2) / 2 := min_le_left _ _
    linarith
  obtain ⟨δ, C, hδ, h⟩ := hW ε hε0 hε1
  have := windowed_energy_principle zetaFamily (by linarith) (by linarith) hδ h () s hεs
  simpa [zetaFamily, LFunction_modOne_eq] using this

end LiouvilleEnergy.Window

#print axioms LiouvilleEnergy.Window.windowed_energy_principle
#print axioms LiouvilleEnergy.Window.riemannHypothesis_of_windowW
