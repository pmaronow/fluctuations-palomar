module

public import ComparisonActualHighOnlyMacroscopicTrialCDF
public import ComparisonMacroscopicScalarAttainment

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 10000000
namespace ActualHighOnlyComparisonData
variable {n : ℕ} {delta : ℝ} (a : ActualHighOnlyComparisonData n delta)

theorem original_objective_le_scalar {T lam : ℝ} (hT : 0<T)
    (hlam : lam∈ Icc (0:ℝ) (a.d^2)) (hlT : lam ≤ T)
    (alpha : a.Profile) (hscalar : alpha.val∈scalarProfiles) :
    a.objective lam alpha ≤ scalarParisiValue hT alpha.val+
      comparisonEndpointL1Cost T a.b a.h+a.s*lam/4 := by
  let R:=a.R alpha
  let e:=fun u=>laplaceComparisonStrength a.d lam (R u)
  have HR:MonotoneOn R (Icc (0:ℝ) 1):=(a.radiusProfile alpha).property.2.monotoneOn _
  have HRb:∀u∈ Icc (0:ℝ) 1,R u∈ Icc (0:ℝ) 1:=fun u _=>(a.radiusProfile alpha).property.1 u
  have HG:=laplaceComparisonStrength_monotonicities_nonneg a.hd.ne' hlam.1
  have He:AntitoneOn e (Icc (0:ℝ) 1):=fun u hu v hv huv=>HG.1 (HRb u hu) (HRb v hv) (HR hu hv huv)
  have Heb:∀u∈ Icc (0:ℝ) 1,e u∈ Icc (0:ℝ) T:=fun u _=>
    ⟨laplaceComparisonStrength_nonneg a.d _ hlam.1,
      (laplaceComparisonStrength_le a.d hlam.1 _).trans hlT⟩
  have Her:MonotoneOn (fun u=>e u*R u) (Icc (0:ℝ) 1):=
    fun u hu v hv huv=>HG.2 (HRb u hu) (HRb v hv) (HR hu hv huv)
  have Hupper:=actualComparisonPressure_le_scalar n a.hn hT.le e R He Heb Her HR
    (fun u hu=>(HRb u hu).1)
  rw [a.physicalScalarQuantileValue_of_scalar hT alpha hscalar] at Hupper
  have Herror:=a.original_endpoint_cost alpha hlam hlT
  have Hsign:=le_abs_self (a.objective lam alpha-
    pathCompensatedPressure n (fun _=>T) (fun _=>0) e R 0)
  dsimp only [e,R] at Hupper Hsign
  linarith

end ActualHighOnlyComparisonData

theorem eventually_actual_high_only_minimum_upper_scalar_reference
    {beta : ℝ≥0} (hbeta : 0<beta) {delta epsilon : ℝ}
    (hdelta : 0<delta) (hepsilon : 0<epsilon)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (a : (n:ℕ)→ActualHighOnlyComparisonData (dim n) delta)
    (lam : ℕ→ℝ) (hlam : ∀n,lam n∈ Icc (0:ℝ) ((a n).d^2))
    (hlT : ∀n,lam n ≤ (beta:ℝ)^2)
    (M : (n:ℕ)→ActualHighOnlyComparisonMinimum (a n) (lam n))
    (hs : Tendsto (fun n=>(a n).s) atTop (𝓝 0)) :
    ∀ᶠn in atTop,(a n).objective (lam n) (M n).alpha ≤ 
      normalizedScalarParisiReference beta+epsilon+
        comparisonEndpointL1Cost ((beta:ℝ)^2) (a n).b (a n).h+(a n).s*lam n/4 := by
  have hT:0<(beta:ℝ)^2:=sq_pos_of_pos (NNReal.coe_pos.mpr hbeta)
  obtain ⟨j,hj,hj1⟩ := (eventually_macro_scalar_reference_competitor hbeta (half_pos hepsilon)).and
    (eventually_gt_atTop (1:ℕ)) |>.exists
  let eta:=macroDensityFloor j
  let Q:=macroDensityCap j
  have heta:0<eta:=macroDensityFloor_pos (by omega)
  have hQ:1<Q:=macroDensityCap_gt_one hj1
  obtain ⟨gamma,hgamma⟩:=hj heta hQ
  rw [macroInverseQuantile_massProfile_eq heta hQ gamma] at hgamma
  have Hpow:Tendsto (fun n=>(dim n:ℝ)^delta) atTop atTop:=
    (tendsto_rpow_atTop hdelta).comp (tendsto_natCast_atTop_atTop.comp hdim)
  have Hinv:Tendsto (fun n=>1/(dim n:ℝ)^delta) atTop (𝓝 0):=by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp Hpow
  have Hfloor:Tendsto (fun n=>1/((dim n:ℝ)^delta)^3) atTop (𝓝 0):=by
    simpa only [div_pow,one_pow,zero_pow (by norm_num : (3:ℕ)≠0)] using Hinv.pow 3
  have HS:Tendsto (fun n=>(beta:ℝ)^2*(a n).s) atTop (𝓝 0):=by
    simpa only [mul_zero] using hs.const_mul ((beta:ℝ)^2)
  filter_upwards [Hfloor.eventually (eventually_le_nhds (half_pos heta)),
    Hpow.eventually (eventually_ge_atTop Q),
    HS.eventually (eventually_le_nhds (half_pos hepsilon))] with n hnFloor hnCap hnSmall
  have Hk:∀r∈ Icc (0:ℝ) 1,(a n).k r ≤ eta/2:=fun r hr=>
    (comparisonFloor_le_inv_cube (a n).hN (a n).hU hr.1).trans hnFloor
  have HM:∀u∈ Icc (0:ℝ) 1,Q ≤ (a n).M u:=fun u hu=>
    hnCap.trans (comparisonCap_ge (a n).hN (a n).hU (a n).hL
      (min_le_left _ _) (a n).hE (a n).hd.le hu.1)
  let trial:=(a n).macroScalarTrial gamma heta Hk HM
  have Htrial:scalarParisiValue hT trial.val ≤ normalizedScalarParisiReference beta+epsilon:=by
    have Herr:=macroInitialMassProfile_scalar_error hT gamma ⟨(a n).hs.1,(a n).hs1⟩
    have Hsign:=le_abs_self (scalarParisiValue hT trial.val-scalarParisiValue hT gamma.val)
    change |scalarParisiValue hT trial.val-scalarParisiValue hT gamma.val| ≤ (beta:ℝ)^2*(a n).s at Herr
    linarith
  have Hobjective:=(a n).original_objective_le_scalar hT (hlam n) (hlT n) trial
    ((a n).macroScalarTrial_scalarProfile gamma heta Hk HM)
  exact ((M n).minimum trial).trans (Hobjective.trans (by linarith))

end OAI.SKFluctuations.LaplaceWindowFormalization
