/-
  Masulloʼs route (Section 18 of the v7 preprint): holomorphy of L′/L on Re s > 1/2
  implies RH and GRH. The functional-equation proofs and the order-of-vanishing
  argument follow L. Alpöge's Lean project (alpo.ge/lean.tar.gz); the region
  argument and the statement of Masulloʼs hypothesis are ours. A. M. Masulloʼs
  theorem itself is assumed, not proved.
-/
import Mathlib

open Complex DirichletCharacter

def EveryCharacter : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0



theorem Formalism.VW.rh_of_right (hz : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) : RiemannHypothesis := by
  unfold RiemannHypothesis
  intro s hs htriv hs1
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [riemannZeta_zero] at hs
      norm_num at hs
    have ht : 1 / 2 < (1 - s).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith
    have h1 : (1 - s) ≠ 1 := by
      intro h
      apply hs0
      linear_combination -h
    have hnat : ∀ n : ℕ, (1 - s) ≠ -(n : ℂ) := by
      intro n h
      have hr := congrArg Complex.re h
      rw [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at hr
      have : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith
    have key := riemannZeta_one_sub hnat h1
    rw [sub_sub_cancel, hs] at key
    have hz' := hz (1 - s) ht h1
    have h2pi : (2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-(1 - s)) ≠ 0 :=
      mul_ne_zero two_ne_zero (Complex.cpow_ne_zero_iff.2 (Or.inl (mul_ne_zero two_ne_zero hpi)))
    have hG : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hcos : Complex.cos ((Real.pi : ℂ) * (1 - s) / 2) ≠ 0 := by
      rw [Ne, Complex.cos_eq_zero_iff]
      rintro ⟨k, hk⟩
      have h3 : ((1 - s) - (2 * (k : ℂ) + 1)) * (Real.pi : ℂ) = 0 := by
        linear_combination 2 * hk
      rcases mul_eq_zero.1 h3 with h | h
      · have hsk : s = -2 * (k : ℂ) := by linear_combination -h
        have hre : s.re = -2 * (k : ℝ) := by
          rw [hsk, Complex.mul_re]
          simp
        rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
        · have : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
          linarith
        · apply hs0
          rw [hsk, hk0]
          simp
        · apply htriv
          refine ⟨(k - 1).toNat, ?_⟩
          have hnk : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
          have h' : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by
            have := congrArg (fun m : ℤ => (m : ℂ)) hnk
            push_cast at this
            exact this
          rw [hsk, h']
          ring
      · exact hpi h
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero h2pi hG) hcos) hz') key.symm
  · exact heq
  · exact absurd hs (hz s hgt hs1)
theorem Formalism.VW.gammaFactor_ne_zero {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) : gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by rw [add_re, one_re]; linarith)

theorem Formalism.VW.critLine (h : EveryCharacter) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ)
    (h0 : 0 < s.re) (h1 : s.re < 1) (hz : LFunction χ s = 0) : s.re = 1 / 2 := by
  have hs0 : s ≠ 0 := fun e => by simp [e] at h0
  have hs1 : s ≠ 1 := fun e => by simp [e] at h1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hinv : χ⁻¹.IsPrimitive := by
      rw [isPrimitive_def, conductor_inv]; exact hχ
    have hc : completedLFunction χ s = 0 := by
      rw [LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)] at hz
      exact (div_eq_zero_iff.1 hz).resolve_right (Formalism.VW.gammaFactor_ne_zero χ h0)
    have hfe := hinv.completedLFunction_one_sub s
    rw [inv_inv, hc, mul_zero] at hfe
    have h2 : (1 - s) ≠ 0 := sub_ne_zero.2 hs1.symm
    refine h N χ⁻¹ (1 - s) (by rw [sub_re, one_re]; linarith) (Or.inr fun e => hs0 (by linear_combination -e)) ?_
    rw [LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s) (Or.inl h2), hfe, zero_div]
  · exact h N χ s hgt (Or.inr hs1) hz

theorem Formalism.VW.rh_of_every (h : EveryCharacter) : RiemannHypothesis :=
  Formalism.VW.rh_of_right fun s hs hs1 => by
    have := h 1 (1 : DirichletCharacter ℂ 1) s hs (Or.inr hs1)
    rwa [LFunction_modOne_eq] at this



open Complex Filter Topology DirichletCharacter

noncomputable section

namespace MasulloRoute

/-- Masullo's main theorem, specialised to F = ℚ: for every Dirichlet character χ, the
logarithmic derivative L'/L(χ,s) extends holomorphically to Re s > 1/2 (away from s = 1). -/
def MasulloLogDeriv : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), ∃ q : ℂ → ℂ,
    DifferentiableOn ℂ q {s | 1 / 2 < s.re ∧ s ≠ 1} ∧
    ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → deriv (LFunction χ) s = q s * LFunction χ s

/-- A holomorphic function on a connected open set, not identically zero there, whose
logarithmic derivative is holomorphic, has no zeros. (After the archive's `logDerivZeroFree`.) -/
theorem zero_free_of_logDeriv (P q : ℂ → ℂ) (V : Set ℂ) (hV : IsOpen V) (hc : IsPreconnected V)
    (hP : DifferentiableOn ℂ P V) {w : ℂ} (hwV : w ∈ V) (hw : P w ≠ 0)
    (hq : DifferentiableOn ℂ q V) (hPq : ∀ s ∈ V, deriv P s = q s * P s) :
    ∀ s ∈ V, P s ≠ 0 := by
  intro s hs hPs
  have hPa : AnalyticOnNhd ℂ P V := hP.analyticOnNhd hV
  have hqa : AnalyticAt ℂ q s := hq.analyticAt (hV.mem_nhds hs)
  have hne : analyticOrderAt P s ≠ ⊤ := by
    intro h
    have hev : P =ᶠ[𝓝 s] 0 := analyticOrderAt_eq_top.mp h
    exact hw (hPa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hs hev hwV)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : analyticOrderAt P s = 0 := by rw [← hn]; rfl
    rcases analyticOrderAt_eq_zero.mp this with h | h
    · exact h (hPa s hs)
    · exact h hPs
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hord : analyticOrderAt P s = (m : ℕ∞) + 1 := by rw [← hn]; push_cast; rfl
  have hd : analyticOrderAt (deriv P) s = m := analyticOrderAt_deriv_of_pos (hPa s hs) hord
  have hev : deriv P =ᶠ[𝓝 s] q * P :=
    Filter.eventually_of_mem (hV.mem_nhds hs) (fun w hw => by simpa using hPq w hw)
  have hmul : analyticOrderAt (deriv P) s = analyticOrderAt q s + ((m : ℕ∞) + 1) := by
    rw [analyticOrderAt_congr hev, analyticOrderAt_mul hqa (hPa s hs), hord]
  rw [hd] at hmul
  have hle : (m : ℕ∞) + 1 ≤ (m : ℕ∞) := by
    calc (m : ℕ∞) + 1 ≤ analyticOrderAt q s + ((m : ℕ∞) + 1) := le_add_self
      _ = m := hmul.symm
  exact absurd hle (by
    rw [not_le]
    exact ENat.lt_add_one_iff (ENat.natCast_ne_top m) |>.mpr le_rfl)

/-- The convex region used around a zero `s₀` with Re s₀ < 1: it avoids s = 1 and
reaches Re s ≥ 1, where L(χ,s) ≠ 0 is known (Mathlib). -/
def region (t : ℝ) : Set ℂ := {s | 1 / 2 < s.re ∧ s.re - t * s.im < 1}

theorem region_open (t : ℝ) : IsOpen (region t) := by
  apply IsOpen.inter
  · exact isOpen_lt continuous_const Complex.continuous_re
  · exact isOpen_lt (Complex.continuous_re.sub (continuous_const.mul Complex.continuous_im))
      continuous_const

theorem region_convex (t : ℝ) : Convex ℝ (region t) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hre : (a • x + b • y).re = a * x.re + b * y.re := by simp
  have him : (a • x + b • y).im = a * x.im + b * y.im := by simp
  have key : ∀ u v : ℝ, ∀ c : ℝ, u < c → v < c → a * u + b * v < c := by
    intro u v c hu hv
    rcases ha.eq_or_lt with h0 | h0
    · subst h0; have : b = 1 := by linarith
      subst this; simpa using hv
    · have hc : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
      linarith [mul_lt_mul_of_pos_left hu h0, mul_le_mul_of_nonneg_left hv.le hb]
  refine ⟨?_, ?_⟩
  · rw [hre]; have := key (-x.re) (-y.re) (-(1/2)) (by linarith) (by linarith); linarith
  · rw [hre, him]
    have := key (x.re - t * x.im) (y.re - t * y.im) 1 hx2 hy2
    linarith

theorem one_not_mem_region (t : ℝ) : (1 : ℂ) ∉ region t := by
  simp [region]

/-- Masullo's theorem gives the zero-free half-plane `Re s > 1/2` for every Dirichlet L-function. -/
theorem everyCharacter_of_masullo (hM : MasulloLogDeriv) :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re →
      (χ ≠ 1 ∨ s ≠ 1) → LFunction χ s ≠ 0 := by
  intro N _ χ s hs hχs
  rcases le_or_gt 1 s.re with h1 | h1
  · exact LFunction_ne_zero_of_one_le_re χ hχs h1
  obtain ⟨q, hq, hPq⟩ := hM N χ
  -- choose the slope so that s lies in the region
  set t : ℝ := if 0 ≤ s.im then 1 else -1 with ht
  have hsV : s ∈ region t := by
    refine ⟨hs, ?_⟩
    by_cases h : 0 ≤ s.im
    · simp only [ht, if_pos h]; linarith
    · simp only [ht, if_neg h]; push Not at h; linarith
  have hsub : region t ⊆ {s | 1 / 2 < s.re ∧ s ≠ 1} := fun z hz =>
    ⟨hz.1, fun e => one_not_mem_region t (e ▸ hz)⟩
  -- a point with Re ≥ 1 in the region
  set w : ℂ := ⟨2, 2 * t⟩ with hw
  have htt : t * t = 1 := by by_cases h : 0 ≤ s.im <;> simp [ht, h]
  have hwV : w ∈ region t := by
    refine ⟨by simp [hw]; norm_num, ?_⟩
    simp only [hw]
    nlinarith [htt]
  have hLw : LFunction χ w ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ (Or.inr (fun e => by
      have := congrArg Complex.re e; simp [hw] at this)) (by simp [hw])
  have hdiff : DifferentiableOn ℂ (LFunction χ) (region t) := fun z hz =>
    (differentiableAt_LFunction χ z (Or.inl (fun e => one_not_mem_region t (e ▸ hz)))).differentiableWithinAt
  exact zero_free_of_logDeriv (LFunction χ) q (region t) (region_open t)
    (region_convex t).isPreconnected hdiff hwV hLw (hq.mono hsub)
    (fun z hz => hPq z (hsub hz).1 (hsub hz).2) s hsV

end MasulloRoute


/-- Masullo's theorem (as stated above) implies Mathlib's Riemann hypothesis. -/
theorem MasulloRoute.riemannHypothesis_of_masullo (hM : MasulloRoute.MasulloLogDeriv) :
    RiemannHypothesis :=
  Formalism.VW.rh_of_every (fun N _ χ s hs h => MasulloRoute.everyCharacter_of_masullo hM N χ s hs h)

/-- Masullo's theorem implies GRH for primitive Dirichlet L-functions. -/
theorem MasulloRoute.grh_of_masullo (hM : MasulloRoute.MasulloLogDeriv) (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : DirichletCharacter.LFunction χ s = 0) : s.re = 1 / 2 :=
  Formalism.VW.critLine (fun N _ χ s hs h => MasulloRoute.everyCharacter_of_masullo hM N χ s hs h)
    N χ hχ s h0 h1 hz

#print axioms MasulloRoute.riemannHypothesis_of_masullo
#print axioms MasulloRoute.grh_of_masullo
