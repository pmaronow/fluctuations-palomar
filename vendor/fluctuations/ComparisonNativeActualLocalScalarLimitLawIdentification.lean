module

public import ComparisonLocalTemperatureClockLawIdentification
public import ComparisonNativeActualLocalScalarLimitRadiusReadout
public import ComparisonNativeActualHistoryLocalTemperatureScalarCutsAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy GaussianCalculus Scalar
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000

theorem actual_ambient_scalar_quantile_div_local_ratio
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock T S : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : 0 < T) (hS : 0 < S) (u : ℝ) :
    actualScalarClockQuantile T (n+1) M.bf M.hf u/(S/T)=
      actualScalarClockQuantile S (n+1) M.bf M.hf u := by
  unfold actualScalarClockQuantile
  split_ifs with hu
  · simp only [zero_div]
  · field_simp [hT.ne',hS.ne']

namespace ActualInheritedLocalScalarLimitData

theorem scalar_radius_laws_ae_eq_of_actual_history
    {m delta cl cu Az C0 Ct D Bclock T c0 epsilon : ℝ} {hT : 0 < T}
    {dim : ℕ → ℕ}
    {M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u  ≤  T}
    (d : ActualInheritedLocalScalarLimitData hT (T-epsilon) M htotal)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta) (hdim : Tendsto dim atTop atTop)
    (root : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcanonical : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (shell : ℝ) (hepsilon : 0 ≤ epsilon) (hshell : 0 < shell) (hlocal : 0 < T-epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M) :
    d.U.mass=ᵐ[volume] d.V.mass := by
  let gamma:=(T-epsilon)/T
  let x:=fun n=>(M n).xs
  let q:=fun n=>actualScalarClockQuantile T (dim n+1) (M n).bf (M n).hf
  have hgamma:0 < gamma:=div_pos hlocal hT
  have hx:∀n,0 < x n:=fun n=>(M n).hxs
  have hxlim:Tendsto x atTop (𝓝 0):=
    squeeze_zero (fun n=>(M n).hxs.le)
      (fun n=>(M n).canonical_direct_test_band_ge_scale) hcanonical
  have hq:∀n,MonotoneOn (q n) (Icc (0:ℝ) 1):=fun n=>
    actualScalarClockQuantile_monotone hT (dim n+1) (by omega) (M n).bf (M n).hf
      (M n).inherited_bf_monotone (M n).inherited_hf_monotone
  have hqb:∀n u,u∈Icc (0:ℝ) 1 → q n u∈Icc (0:ℝ) 1:=fun n=>
    actualScalarClockQuantile_bounds hT (dim n+1) (by omega) (M n).bf (M n).hf
      (M n).inherited_bf_monotone (M n).inherited_hf_monotone
      ((M n).inherited_total_clock_le (htotal n))
  have hU:∀t : ℝ,Tendsto (fun n=>(quantileMassProfile (q n) (hqb n)).val
      (gamma*(x n*t))/x n) atTop (𝓝 (d.U.mass t)):=d.scalar_cdf_limit
  have hlocalLaw:∀R : ℝ,0 < R → ∃v : ℕ → ℝ,
      (∀n,v n∈Icc (0:ℝ) 1) ∧
      (∀ᶠn in atTop,gamma*(x n*R) < q n (v n) ∧ x n*R < (M n).R (v n)) ∧
      Tendsto (fun n=>(∫w : ParisiFinite.OrderPoint in {w | (w:ℝ) ≤ v n},
        |q n (w:ℝ)/gamma-(M n).R w|∂(uniformOrderMass : Measure ParisiFinite.OrderPoint))/(x n)^2)
        atTop (𝓝 0) := by
    intro R hR
    obtain ⟨C,hC,Hcut,Hcouple⟩:=
      actual_selected_bad_history_local_temperature_compact_original_scalar_cuts_along
        hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
        dim hdim root M x (fun _=>le_rfl) hxlim epsilon shell hepsilon hshell hlocal hb hh Hhistory R hR
    let v:=fun n=>min (C*x n) 1
    have hv:∀n,v n∈Icc (0:ℝ) 1:=fun n=>
      ⟨le_min (mul_nonneg hC.le (hx n).le) zero_le_one,min_le_right _ _⟩
    refine ⟨v,hv,?_,?_⟩
    · filter_upwards [Hcut] with n hn
      refine ⟨?_,hn.2⟩
      have hv0:0 < v n:=lt_min (mul_pos hC (hx n)) zero_lt_one
      have H:=mul_lt_mul_of_pos_left hn.1 hgamma
      dsimp only [q]
      rw [actualScalarClockQuantile_on (dim n+1) (M n).bf (M n).hf hv0]
      convert H using 1; dsimp only [gamma,v];field_simp [hT.ne',hlocal.ne']
    · have Hroot:=actual_selected_bad_history_total_clock_and_root
        dim root M epsilon shell hepsilon hb hh Hhistory
      apply Hcouple.congr'
      filter_upwards [Hroot] with n hn
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun w=>by
        dsimp only [q,gamma]
        rw [actual_ambient_scalar_quantile_div_local_ratio (M n) hT hlocal,
          (M n).inherited_local_temperature_scalar_quantile_eq_mixed_of_root (T-epsilon) hn.2 w.property.1]
  exact comparison_shifted_local_temperature_scalar_radius_laws_ae_identified
    (actualInverseSequence M) q gamma x d.U.mass d.V.mass hgamma
    (fun _=>le_rfl) hq hqb hx d.V.monotone
    (actualInverseSequence_omitted_small M x) hU d.radius_inverse_cdf_limit hlocalLaw

end ActualInheritedLocalScalarLimitData
end OAI.SKFluctuations.LaplaceWindowFormalization
