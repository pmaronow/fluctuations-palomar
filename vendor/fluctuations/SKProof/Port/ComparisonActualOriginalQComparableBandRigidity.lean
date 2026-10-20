module

public import SKProof.Port.ComparisonActualOriginalQComparableBandScalarCuts
public import SKProof.Port.ComparisonActualOriginalQLimitRigidity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy GaussianCalculus Scalar
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false
namespace ActualOriginalQLocalScalarLimitData
theorem scalar_radius_laws_ae_eq_of_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ} {hT : 0 < T}
    {dim : ℕ → ℕ}
    {M : (n:ℕ) → ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u  ≤  T}
    (d : ActualOriginalQLocalScalarLimitData hT T M htotal)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta) (hdim : Tendsto dim atTop atTop)
    
    (G : OriginalQComparableBandContext M T)
    :
    d.U.mass=ᵐ[volume] d.V.mass := by
  have hlocal : 0 < T := G.hT
  let gamma:=T/T
  let x:=fun n=>(M n).xs
  let q:=fun n=>actualScalarClockQuantile T (dim n+1) (M n).sweepBf (M n).sweepHf
  have hgamma:0 < gamma:=div_pos hlocal hT
  have hx:∀n,0 < x n:=fun n=>(M n).hxs
  have hxlim:Tendsto x atTop (𝓝 0):=
    G.xs_zero
  have hq:∀n,MonotoneOn (q n) (Icc (0:ℝ) 1):=fun n=>
    actualScalarClockQuantile_monotone hT (dim n+1) (by omega) (M n).sweepBf (M n).sweepHf
      (M n).inherited_bf_monotone (M n).inherited_hf_monotone
  have hqb:∀n u,u∈Icc (0:ℝ) 1 → q n u∈Icc (0:ℝ) 1:=fun n=>
    actualScalarClockQuantile_bounds hT (dim n+1) (by omega) (M n).sweepBf (M n).sweepHf
      (M n).inherited_bf_monotone (M n).inherited_hf_monotone
      ((M n).inherited_total_clock_le (htotal n))
  have hU:∀t : ℝ,Tendsto (fun n=>(quantileMassProfile (q n) (hqb n)).val
      (gamma*(x n*t))/x n) atTop (𝓝 (d.U.mass t)):=d.scalar_cdf_limit
  have hlocalLaw:∀R : ℝ,0 < R → ∃v : ℕ → ℝ,
      (∀n,v n∈Icc (0:ℝ) 1) ∧
      (∀ᶠn in atTop,gamma*(x n*R) < q n (v n) ∧ x n*R < (M n).sweepRadius (v n)) ∧
      Tendsto (fun n=>(∫w : ParisiFinite.OrderPoint in {w | (w:ℝ) ≤ v n},
        |q n (w:ℝ)/gamma-(M n).sweepRadius w|∂(uniformOrderMass : Measure ParisiFinite.OrderPoint))/(x n)^2)
        atTop (𝓝 0) := by
    intro R hR
    obtain ⟨C,hC,Hcut,Hcouple⟩:=
      actual_comparable_context_compact_original_scalar_cuts_original_q
        hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
        dim hdim M G htotal R hR
    let v:=fun n=>min (C*x n) 1
    have hv:∀n,v n∈Icc (0:ℝ) 1:=fun n=>
      ⟨le_min (mul_nonneg hC.le (hx n).le) zero_le_one,min_le_right _ _⟩
    refine ⟨v,hv,?_,?_⟩
    · filter_upwards [Hcut] with n hn
      refine ⟨?_,hn.2⟩
      have hv0:0 < v n:=lt_min (mul_pos hC (hx n)) zero_lt_one
      have H:=mul_lt_mul_of_pos_left hn.1 hgamma
      dsimp only [q]
      rw [actualScalarClockQuantile_on (dim n+1) (M n).sweepBf (M n).sweepHf hv0]
      convert H using 1; dsimp only [gamma,v,x];field_simp [hT.ne',hlocal.ne']
    · have Hroot:=G.total_root_bare_original_q
      apply Hcouple.congr'
      filter_upwards [Hroot] with n hn
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun w=>by
        dsimp only [q,gamma]
        rw [div_self hT.ne',div_one,
          (M n).inherited_local_temperature_scalar_quantile_eq_mixed_of_root T hn.2 w.property.1]
  exact comparison_shifted_local_temperature_scalar_radius_laws_ae_identified
    (ActualThetaZeroOverlapMinimum.originalQShiftedInverseSequence M) q gamma x d.U.mass d.V.mass hgamma
    (fun n=>(M n).data.hrbounds.1.le) hq hqb hx d.V.monotone
    d.omitted_small hU d.radius_inverse_cdf_limit hlocalLaw

theorem global_profile_rigidity_of_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ} {hT : 0 < T}
    {dim : ℕ → ℕ}
    {M : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {htotal : ∀n,∀u∈Icc (0 : ℝ) 1,(M n).h u+(M n).b u ≤ T}
    (d : ActualOriginalQLocalScalarLimitData hT T M htotal)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1 : ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta) (hdim : Tendsto dim atTop atTop)
    
    (G : OriginalQComparableBandContext M T)
    (hvirtual : ∀a b,0 ≤ a → a < b →
      a∈comparisonIncrementSupport d.V.mass → b∈comparisonIncrementSupport d.V.mass →
      (∀r∈Ioo a b,r∉comparisonIncrementSupport d.V.mass) →
      Nonempty (ComparisonVirtualGapData
        (comparisonLocalScalarLimitResponse hT T d.beta d.U d.sigma) a b)) :
    (∀t > 0,d.U.mass t=((T/T)*scalarInitialDensityConstant hT d.beta)*t) ∧
    (∀t > 0,d.V.mass t=((T/T)*scalarInitialDensityConstant hT d.beta)*t) := by
  have hlocal : 0 < T := G.hT
  have hUV := d.scalar_radius_laws_ae_eq_of_comparable_context
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin hdim
    G
  have hxs : Tendsto (fun n => (M n).xs) atTop (𝓝 0) :=
    G.xs_zero
  exact d.global_profile_rigidity_of_coupled_laws hUV hcl hAz hxs hvirtual

end ActualOriginalQLocalScalarLimitData
end OAI.SKFluctuations.LaplaceWindowFormalization
