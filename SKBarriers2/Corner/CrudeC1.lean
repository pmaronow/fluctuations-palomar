module

public import SKBarriers2.Corner.CoreValue
public import SKBarriers2.Corner.Evenness
public import SKBarriers2.Analysis.QSmooth

@[expose] public section

noncomputable section
open Set Filter OAI.SK.Analytic
open scoped Topology

namespace SKBarriers2.Corner

theorem deriv_zero_of_even {f : ℝ → ℝ} (heven : ∀ t, f (-t) = f t)
    (hf : DifferentiableAt ℝ f 0) : deriv f 0 = 0 := by
  have hid : HasDerivAt (fun t : ℝ => -t) (-1) (0 : ℝ) := (hasDerivAt_id (0 : ℝ)).neg
  have hfneg : HasDerivAt f (deriv f 0) (-(0 : ℝ)) := by simpa only [neg_zero] using hf.hasDerivAt
  have hneg := hfneg.comp (0 : ℝ) hid
  have hEq : (fun t => f (-t)) = f := funext heven
  have H : HasDerivAt f (-deriv f 0) 0 := by
    convert! hneg using 1
    · exact hEq.symm
    · simp
  have h := hf.hasDerivAt.unique H
  linarith

theorem even_quadratic_le {f : ℝ → ℝ} {a M : ℝ} (ha : 0 ≤ a) (_hM : 0 ≤ M)
    (heven : ∀ t, f (-t) = f t)
    (hf : ∀ t ∈ Icc (-a) a, ContDiffAt ℝ 2 f t)
    (hbound : ∀ t ∈ Icc (-a) a, |deriv (deriv f) t| ≤ M)
    {k : ℝ} (hk : |k| ≤ a) : |f k - f 0| ≤ M * k ^ 2 / 2 := by
  have h0 : (0 : ℝ) ∈ Icc (-a) a := ⟨by linarith, ha⟩
  have hd0 : deriv f 0 = 0 := deriv_zero_of_even heven ((hf 0 h0).differentiableAt (by norm_num))
  have hder (t : ℝ) (ht : t ∈ Icc (-a) a) : DifferentiableAt ℝ (deriv f) t :=
    ((hf t ht).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hpos {u : ℝ} (hu : u ∈ Icc (0 : ℝ) a) : |f u - f 0| ≤ M * u ^ 2 / 2 := by
    have hsub : Icc (0 : ℝ) u ⊆ Icc (-a) a := fun t ht => ⟨by linarith [ht.1], ht.2.trans hu.2⟩
    have hdfCont : ContinuousOn (deriv f) (Icc (0 : ℝ) u) :=
      fun t ht => (hder t (hsub ht)).continuousAt.continuousWithinAt
    have hInt : IntervalIntegrable (deriv f) MeasureTheory.volume 0 u :=
      hdfCont.intervalIntegrable_of_Icc hu.1
    have hFTC : (∫ t in (0 : ℝ)..u, deriv f t) = f u - f 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => ((hf t (hsub (by simpa only [uIcc_of_le hu.1] using ht))).differentiableAt
          (by norm_num)).hasDerivAt) hInt
    have hSlope (t : ℝ) (ht : t ∈ Icc (0 : ℝ) u) : |deriv f t| ≤ M * t := by
      have H := (convex_Icc (0 : ℝ) u).norm_image_sub_le_of_norm_deriv_le
        (fun y hy => hder y (hsub hy))
        (fun y hy => by simpa only [Real.norm_eq_abs] using hbound y (hsub hy))
        (show (0 : ℝ) ∈ Icc (0 : ℝ) u from ⟨le_rfl, hu.1⟩) ht
      simpa only [hd0, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht.1] using H
    have H := intervalIntegral.norm_integral_le_of_norm_le (f := deriv f) hu.1
      (MeasureTheory.ae_of_all MeasureTheory.volume (fun t ht =>
        by simpa only [Real.norm_eq_abs] using hSlope t ⟨ht.1.le, ht.2⟩))
      (show IntervalIntegrable (fun t : ℝ => M * t) MeasureTheory.volume 0 u from
        (continuous_const.mul continuous_id).intervalIntegrable _ _)
    rw [hFTC, Real.norm_eq_abs, intervalIntegral.integral_const_mul, integral_id] at H
    simpa only [zero_pow (by norm_num : 2 ≠ 0), sub_zero, mul_div_assoc] using H
  have H := hpos (u := |k|) ⟨abs_nonneg k, hk⟩
  have hval : f |k| = f k := by
    rcases le_total 0 k with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, heven]
  simpa only [hval, sq_abs] using H

def cornerTerminal (β : ℝ) (α : ℝ → ℝ) (r h : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, Phi β α (r - h + 4 * h) (x i)

def BoundaryKSecondBound (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) (C h₀ : ℝ) : Prop :=
  ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ N : ℕ, 1 ≤ N →
    (∀ k : ℝ, |k| ≤ 1 / 2 → ∀ z : ℝ,
      DifferentiableAt ℝ (OW.boundary β α (1 / 2) (r - h) h k N) z) ∧
    ∀ z : ℝ, ∀ k : ℝ, |k| ≤ 1 / 2 →
      ContDiffAt ℝ 2 (fun t => OW.boundary β α (1 / 2) (r - h) h t N z) k ∧
      ContDiffAt ℝ 2 (fun t => deriv (OW.boundary β α (1 / 2) (r - h) h t N) z) k ∧
      |deriv (deriv (fun t => OW.boundary β α (1 / 2) (r - h) h t N z)) k| ≤ C * h ∧
      |deriv (deriv (fun t => deriv (OW.boundary β α (1 / 2) (r - h) h t N) z)) k| ≤ C * h

theorem crudeC1_of_second_parameter_bound {β : ℝ} {α : ℝ → ℝ} {I : Set ℝ}
    {B C h₀ : ℝ} (hC : 0 ≤ C) (hh₀ : 0 < h₀)
    (hterminal : ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ →
      QPotential 2 B (cornerTerminal β α r h))
    (hsecond : BoundaryKSecondBound β α I C h₀) : CrudeC1 β α I := by
  refine ⟨C + 1, h₀, by linarith, hh₀, ?_⟩
  intro r hr h hh hh0 k hk N hN z
  obtain ⟨hz, hj⟩ := hsecond r hr h hh hh0 N hN
  let F : ℝ → ℝ → ℝ := fun t z => OW.boundary β α (1 / 2) (r - h) h t N z
  have heven (t : ℝ) : F (-t) = F t := by
    funext y
    have hs : cornerTerminal β α r h ∘ OW.swap23 = cornerTerminal β α r h := by
      funext x
      simp [cornerTerminal, OW.swap23_apply, Fin.sum_univ_succ]
      ring
    have H := OW.window_chain_even β α (1 / 2) (r - h) h t N
      ((hterminal r hr h hh hh0).boundedDerivs le_rfl) hs y
    convert! H using 1
  have hv := even_quadratic_le (by norm_num : (0 : ℝ) ≤ 1 / 2) (mul_nonneg hC hh.le)
    (fun t => congrFun (heven t) z)
    (fun t ht => (hj z t (abs_le.mpr ht)).1)
    (fun t ht => (hj z t (abs_le.mpr ht)).2.2.1) hk
  have hd := even_quadratic_le (by norm_num : (0 : ℝ) ≤ 1 / 2) (mul_nonneg hC hh.le)
    (fun t => congrArg (fun g : ℝ → ℝ => deriv g z) (heven t))
    (fun t ht => (hj z t (abs_le.mpr ht)).2.1)
    (fun t ht => (hj z t (abs_le.mpr ht)).2.2.2) hk
  have hV : cornerV β α r h k N = fun y => F k y - F 0 y := rfl
  have hDz : deriv (fun y => F k y - F 0 y) z = deriv (F k) z - deriv (F 0) z := by
    change deriv (F k - F 0) z = _
    exact deriv_sub (hz k hk z) (hz 0 (by norm_num) z)
  rw [hV, hDz]
  constructor
  · exact hv.trans (by nlinarith [mul_nonneg (mul_nonneg hC hh.le) (sq_nonneg k), mul_nonneg hh.le (sq_nonneg k)])
  · exact hd.trans (by nlinarith [mul_nonneg (mul_nonneg hC hh.le) (sq_nonneg k), mul_nonneg hh.le (sq_nonneg k)])

end SKBarriers2.Corner
