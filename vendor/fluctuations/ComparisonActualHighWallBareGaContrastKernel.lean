module

public import ComparisonActualGeneralFourGaSource
public import ComparisonActualHighWallActualScalarHessianBounds

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem actual_high_wall_bare_Ga_contrast_bound
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as) (hU : U ≤ as.length)
    (W A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (Hc0 : |(W⁻¹)^st.generation*actualGeneralResourceGaCurrent M.bf M.hf U st.term| ≤ A)
    (Hc1 : |(W⁻¹)^st.generation*actualGeneralResourceGaCurrent M.bf M.hf U (st.term.retarget 0)| ≤ A)
    (Hr0 : |(W⁻¹)^st.generation*actualGeneralResourceGaRestoration M.bf M.hf U st.term| ≤ B)
    (Hr1 : |(W⁻¹)^st.generation*actualGeneralResourceGaRestoration M.bf M.hf U (st.term.retarget 0)| ≤ B) :
    |(W⁻¹)^st.generation*actualGeneralFourGaContrast M.bf M.hf U st| ≤ max Bclock 0*(A+2*B) := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have hchi : |chi| ≤ 1:=OAI.SKFluctuations.Cavity.ActualHighWallData.actual_scalar_boundary_chi_abs_le_one M.data M.alpha as ho U (by omega) hU
  have hb0 : 0 ≤ (M.bf (partitionPoint 0 as star):ℝ):=NNReal.coe_nonneg _
  have hb : (M.bf (partitionPoint 0 as star):ℝ) ≤ max Bclock 0:=
    (le_add_of_nonneg_left (NNReal.coe_nonneg _)).trans
      ((M.data.total_clock_le M.alpha _ (partitionPoint_mem as ho star)).trans
        (M.hT.trans (le_max_left Bclock 0)))
  have Hfull0 : |(W⁻¹)^st.generation*actualGeneralResourceGa M.bf M.hf U st.term| ≤ A+2*B:=by
    rw [actual_general_resource_Ga_eq_current_add_restoration M.bf M.hf
      (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) hP hi hs ho,mul_add]
    have H:=abs_add_le ((W⁻¹)^st.generation*actualGeneralResourceGaCurrent M.bf M.hf U st.term)
      ((W⁻¹)^st.generation*(2*actualGeneralResourceGaRestoration M.bf M.hf U st.term))
    have Htwo : |(W⁻¹)^st.generation*(2*actualGeneralResourceGaRestoration M.bf M.hf U st.term)|=
        2*|(W⁻¹)^st.generation*actualGeneralResourceGaRestoration M.bf M.hf U st.term|:=by
      rw [show (W⁻¹)^st.generation*(2*actualGeneralResourceGaRestoration M.bf M.hf U st.term)=
        2*((W⁻¹)^st.generation*actualGeneralResourceGaRestoration M.bf M.hf U st.term) by ring,abs_mul]
      norm_num
    rw [Htwo] at H
    linarith only [H,Hc0,Hr0]
  have Hfull1 : |(W⁻¹)^st.generation*actualGeneralResourceGa M.bf M.hf U (st.term.retarget 0)| ≤ A+2*B:=by
    rw [actual_general_resource_Ga_eq_current_add_restoration M.bf M.hf
      (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) hP.retarget hi hs ho,mul_add]
    have H:=abs_add_le ((W⁻¹)^st.generation*actualGeneralResourceGaCurrent M.bf M.hf U (st.term.retarget 0))
      ((W⁻¹)^st.generation*(2*actualGeneralResourceGaRestoration M.bf M.hf U (st.term.retarget 0)))
    have Htwo : |(W⁻¹)^st.generation*(2*actualGeneralResourceGaRestoration M.bf M.hf U (st.term.retarget 0))|=
        2*|(W⁻¹)^st.generation*actualGeneralResourceGaRestoration M.bf M.hf U (st.term.retarget 0)|:=by
      rw [show (W⁻¹)^st.generation*(2*actualGeneralResourceGaRestoration M.bf M.hf U (st.term.retarget 0))=
        2*((W⁻¹)^st.generation*actualGeneralResourceGaRestoration M.bf M.hf U (st.term.retarget 0)) by ring,abs_mul]
      norm_num
    rw [Htwo] at H
    linarith only [H,Hc1,Hr1]
  have Hdiff : |(W⁻¹)^st.generation*actualGeneralResourceGa M.bf M.hf U st.term-
      (1/2:ℝ)*((W⁻¹)^st.generation*actualGeneralResourceGa M.bf M.hf U (st.term.retarget 0))| ≤ 2*(A+2*B):=by
    have H:=abs_sub ((W⁻¹)^st.generation*actualGeneralResourceGa M.bf M.hf U st.term)
      ((1/2:ℝ)*((W⁻¹)^st.generation*actualGeneralResourceGa M.bf M.hf U (st.term.retarget 0)))
    rw [abs_mul (1/2:ℝ),abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at H
    linarith only [H,Hfull0,Hfull1,hA,hB]
  rw [actual_general_four_Ga_contrast_eq_resources M.bf M.hf st hP hi hs ho]
  have Heq : (W⁻¹)^st.generation*((chi/2)*(M.bf (partitionPoint 0 as star):ℝ)*
      (actualGeneralResourceGa M.bf M.hf U st.term-(1/2:ℝ)*actualGeneralResourceGa M.bf M.hf U (st.term.retarget 0)))=
      ((chi/2)*(M.bf (partitionPoint 0 as star):ℝ))*
        ((W⁻¹)^st.generation*actualGeneralResourceGa M.bf M.hf U st.term-
          (1/2:ℝ)*((W⁻¹)^st.generation*actualGeneralResourceGa M.bf M.hf U (st.term.retarget 0))):=by ring
  rw [Heq,abs_mul]
  have Hpre : |(chi/2)*(M.bf (partitionPoint 0 as star):ℝ)| ≤ max Bclock 0/2:=by
    rw [abs_mul,abs_div,abs_of_nonneg hb0]
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have H:=mul_le_mul (div_le_div_of_nonneg_right hchi (by norm_num : (0:ℝ) ≤ 2)) hb hb0 (by norm_num : (0:ℝ) ≤ 1/2)
    simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using H
  exact (mul_le_mul Hpre Hdiff (abs_nonneg _) (by positivity)).trans_eq (by ring)

end OAI.SKFluctuations.Cavity
