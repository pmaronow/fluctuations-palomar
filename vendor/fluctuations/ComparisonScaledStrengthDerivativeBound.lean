module

public import ComparisonStrengthProfileCompactness
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
set_option maxHeartbeats 6000000

theorem comparison_strength_scaled_derivative_parameter_identity
    {d x : ℝ} (hd : d≠0) (hx : x≠0) (lam t : ℝ) :
    deriv (laplaceComparisonStrength d lam) (x*t)/x=
      (lam/x^2)*(lam*x/d^3)*laplaceComparisonShapeDeriv ((lam*x/d^3)*t) := by
  change deriv (comparisonStrength laplaceComparisonShape d lam) (x*t)/x=_
  rw [(hasDerivAt_comparisonStrength
    (laplaceComparisonShape_hasDerivAt (lam*(x*t)/d^3)).differentiableAt).deriv,
    (laplaceComparisonShape_hasDerivAt (lam*(x*t)/d^3)).deriv]
  have harg:lam*(x*t)/d^3=(lam*x/d^3)*t:=by ring
  rw [harg]
  field_simp [hd,hx]

theorem exists_comparison_strength_scaled_derivative_bound
    (Ccal B K : ℝ) (hCcal : 0 ≤ Ccal) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃Dder : ℝ,0 ≤ Dder ∧
      ∀(d lam x t : ℝ),0 < d  →  0 ≤ lam  →  0 < x  →  lam ≤ d^2  →  x ≤ Ccal*d  → 
        lam/x^2 ≤ K+1  →  t∈Icc (0:ℝ) B  → 
        |deriv (laplaceComparisonStrength d lam) (x*t)| ≤ Dder*x := by
  obtain ⟨M,hM⟩:=isCompact_Icc.exists_bound_of_continuousOn
    (laplaceComparisonShapeDeriv_continuous.continuousOn (s:=Icc (0:ℝ) (Ccal*B)))
  have hM0:0 ≤ M:=(norm_nonneg _).trans (hM 0 ⟨le_rfl,mul_nonneg hCcal hB⟩)
  let Dder:=(K+1)*Ccal*M
  have hK1:0 ≤ K+1:=by linarith
  refine ⟨Dder,mul_nonneg (mul_nonneg hK1 hCcal) hM0,?_⟩
  intro d lam x t hd hlam hx hld hxd hamp ht
  have hp:=comparison_strength_shape_parameter_bounds hd hlam hx.le hld hxd
  have harg:(lam*x/d^3)*t∈Icc (0:ℝ) (Ccal*B):=
    ⟨mul_nonneg hp.1 ht.1,mul_le_mul hp.2 ht.2 ht.1 hCcal⟩
  have hshape:|laplaceComparisonShapeDeriv ((lam*x/d^3)*t)| ≤ M := by
    simpa only [Real.norm_eq_abs] using hM _ harg
  have hl0:0 ≤ lam/x^2:=div_nonneg hlam (sq_nonneg _)
  have hp0:0 ≤ lam*x/d^3:=hp.1
  have hprod:=mul_le_mul hamp hp.2 hp.1 hK1
  have Hnorm:|deriv (laplaceComparisonStrength d lam) (x*t)/x| ≤ Dder := by
    rw [comparison_strength_scaled_derivative_parameter_identity hd.ne' hx.ne',
      abs_mul,abs_mul,abs_of_nonneg hl0,abs_of_nonneg hp0]
    exact mul_le_mul hprod hshape (abs_nonneg _) (mul_nonneg hK1 hCcal)
  exact (div_le_iff₀ hx).mp (by simpa only [abs_div,abs_of_pos hx] using Hnorm)

theorem exists_comparison_strength_working_radius_derivative_bound
    (Ccal B K : ℝ) (hCcal : 0 ≤ Ccal) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃Dder : ℝ,0 ≤ Dder ∧
      ∀(d lam x r : ℝ),0 < d  →  0 ≤ lam  →  0 < x  →  lam ≤ d^2  →  x ≤ Ccal*d  → 
        lam/x^2 ≤ K+1  →  r∈Icc (0:ℝ) (B*x)  → 
        |deriv (laplaceComparisonStrength d lam) r| ≤ Dder*x := by
  obtain ⟨Dder,hDder,H⟩:=exists_comparison_strength_scaled_derivative_bound Ccal B K hCcal hB hK
  refine ⟨Dder,hDder,?_⟩
  intro d lam x r hd hlam hx hld hxd hamp hr
  have ht:r/x∈Icc (0:ℝ) B:=
    ⟨div_nonneg hr.1 hx.le,(div_le_iff₀ hx).mpr hr.2⟩
  have HH:=H d lam x (r/x) hd hlam hx hld hxd hamp ht
  simpa only [mul_div_cancel₀ _ hx.ne'] using HH

end OAI.SKFluctuations.LaplaceWindowFormalization
