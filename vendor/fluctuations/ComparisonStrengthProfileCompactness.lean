module

public import ComparisonStrengthRescaling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
set_option maxHeartbeats 2200000

theorem comparison_shape_slope_continuous : Continuous laplaceComparisonSlope := by
  have heq : laplaceComparisonSlope=(fun t=>-t*laplaceComparisonShapeDeriv t/laplaceComparisonShape t) := by
    funext t
    rw [←laplaceComparisonShape_logSlope]
    unfold comparisonLogSlope
    rw [(laplaceComparisonShape_hasDerivAt t).deriv]
  rw [heq]
  exact (continuous_id.neg.mul laplaceComparisonShapeDeriv_continuous).div
    laplaceComparisonShape_contDiff.continuous (fun t=>(laplaceComparisonShape_pos t).ne')

theorem comparison_strength_scaled_parameter_identity (d lam x t : ℝ) :
    laplaceComparisonStrength d lam (x*t)/x^2 =
      (lam/x^2)*laplaceComparisonShape ((lam*x/d^3)*t) := by
  unfold laplaceComparisonStrength comparisonStrength
  have he : lam*(x*t)/d^3=(lam*x/d^3)*t := by ring
  rw [he]
  ring

theorem comparison_slope_scaled_parameter_identity {d lam : ℝ}
    (hd : d≠0) (hlam : lam≠0) (x t : ℝ) :
    comparisonLogSlope (laplaceComparisonStrength d lam) (x*t) =
      laplaceComparisonSlope ((lam*x/d^3)*t) := by
  rw [laplaceComparisonStrength_logSlope hd hlam]
  congr 1
  ring

theorem comparison_strength_shape_parameter_bounds {d lam x C : ℝ}
    (hd : 0<d) (hlam : 0≤lam) (hx : 0≤x) (hld : lam≤d^2) (hxd : x≤C*d) :
    lam*x/d^3∈Icc (0:ℝ) C := by
  refine ⟨div_nonneg (mul_nonneg hlam hx) (pow_nonneg hd.le _),?_⟩
  apply (div_le_iff₀ (pow_pos hd 3)).mpr
  calc
    lam*x ≤ d^2*x := mul_le_mul_of_nonneg_right hld hx
    _ ≤ d^2*(C*d) := mul_le_mul_of_nonneg_left hxd (sq_nonneg d)
    _ = C*d^3 := by ring

theorem comparison_strength_amplitude_bounds {d lam x c K : ℝ}
    (hd : 0<d) (hlam : 0≤lam) (hx : 0<x) (hld : lam≤d^2)
    (hK : 0≤K) (hwork : laplaceComparisonStrength d lam x/x^2∈Icc c K) :
    lam/x^2∈Icc c (K+1) := by
  exact ⟨hwork.1.trans (div_le_div_of_nonneg_right
    (laplaceComparisonStrength_le d hlam x) (sq_nonneg x)),
    comparison_zero_strength_bound_of_working hd hlam hx hld hK hwork.2⟩

theorem comparison_actual_strength_profiles_compact
    (d lam x : ℕ→ℝ) {c K C : ℝ} (hc : 0<c) (hK : 0≤K)
    (hd : ∀n,0<d n) (hlam : ∀n,0<lam n) (hx : ∀n,0<x n)
    (hld : ∀n,lam n≤(d n)^2) (hxd : ∀n,x n≤C*d n)
    (hwork : ∀n,laplaceComparisonStrength (d n) (lam n) (x n)/(x n)^2∈Icc c K) :
    ∃L A : ℝ,∃phi : ℕ→ℕ,StrictMono phi ∧L∈Icc c (K+1) ∧A∈Icc (0:ℝ) C ∧
      (∀t:ℝ,Tendsto (fun n=>laplaceComparisonStrength (d (phi n)) (lam (phi n))
          (x (phi n)*t)/(x (phi n))^2) atTop (𝓝 (L*laplaceComparisonShape (A*t)))) ∧
      (∀t:ℝ,Tendsto (fun n=>comparisonLogSlope
          (laplaceComparisonStrength (d (phi n)) (lam (phi n))) (x (phi n)*t))
          atTop (𝓝 (laplaceComparisonSlope (A*t)))) ∧
      (∀t:ℝ,0<L*laplaceComparisonShape (A*t) ∧laplaceComparisonSlope (A*t)∈Ico (0:ℝ) 1) := by
  have hLb n : lam n/(x n)^2∈Icc c (K+1) :=
    comparison_strength_amplitude_bounds (hd n) (hlam n).le (hx n) (hld n) hK (hwork n)
  have hAb n : lam n*x n/(d n)^3∈Icc (0:ℝ) C :=
    comparison_strength_shape_parameter_bounds (hd n) (hlam n).le (hx n).le (hld n) (hxd n)
  obtain ⟨L,hL,phi,hphi,hLlim⟩ := isCompact_Icc.tendsto_subseq hLb
  obtain ⟨A,hA,psi,hpsi,hAlim⟩ := isCompact_Icc.tendsto_subseq (fun n=>hAb (phi n))
  refine ⟨L,A,phi ∘ psi,hphi.comp hpsi,hL,hA,?_,?_,?_⟩
  · intro t
    have hshape := (laplaceComparisonShape_contDiff.continuous.tendsto (A*t)).comp
      (hAlim.mul_const t)
    have hlimit := (hLlim.comp hpsi.tendsto_atTop).mul hshape
    simpa only [Function.comp_apply,comparison_strength_scaled_parameter_identity] using hlimit
  · intro t
    have hlimit := (comparison_shape_slope_continuous.tendsto (A*t)).comp (hAlim.mul_const t)
    convert hlimit using 1
    ext n
    exact comparison_slope_scaled_parameter_identity (hd (phi (psi n))).ne'
      (hlam (phi (psi n))).ne' _ _
  · intro t
    exact ⟨mul_pos (hc.trans_le hL.1) (laplaceComparisonShape_pos _),laplaceComparisonSlope_mem_Ico _⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
