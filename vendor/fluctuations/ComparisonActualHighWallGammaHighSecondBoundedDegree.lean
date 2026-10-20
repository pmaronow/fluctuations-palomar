module

public import ComparisonActualHighWallGeneratedGammaHighSecondProfile
public import ComparisonActualGeneralGeneratedHighSecond

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_high_wall_generated_high_second_bounded_degree
    (degree rBound : ℕ) (Bclock Cmass Rmacro F : ℝ) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let W:=M.data.d
        ∀(T : ClockTree (Spin n×Bool) as) (i star U kGen : ℕ)
          (seed : List NativeResourceMark) (P₀ : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed kGen T P₀ → P₀.live.test.edges.length ≤ degree →
          i ≤ star → star < U → U ≤ as.length → T.leaves ≤ rBound →
          W ≤ Rmacro/2 → (Az+1/cl)*(1+Cmass)*W ≤ Rmacro/4 →
          partitionPoint 0 as i ≤ Cmass*M.xs → partitionPoint 0 as star ≤ Cmass*W →
        let R:=M.data.highErrorEnvelope M.alpha as U
        |actualGeneralGeneratedHighSecond M.bf M.hf T star U P₀.live.test| ≤
          C*M.data.d^P₀.live.test.edges.length*W^2*
            (T.forkCost R+edgeBudget 0 as R) := by
  classical
  have Hchoose (j : Fin degree):=eventually_actual_high_wall_generated_Gamma_high_second_profile
    (D:=D) (j.val+1) rBound (by omega) Bclock Cmass Rmacro F hCm hm hdelta hroom
    hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius
  choose Cs hCs H using Hchoose
  let C:=1+∑j : Fin degree,Cs j
  have hsum : 0 ≤ ∑j : Fin degree,Cs j:=Finset.sum_nonneg (fun j _=>(hCs j).le)
  have hC : 0 < C:=by dsimp only [C];linarith
  have hCj j : Cs j ≤ C := by
    have Hj:=Finset.single_le_sum (s:=Finset.univ) (f:=Cs) (fun k _=>(hCs k).le) (Finset.mem_univ j)
    dsimp only [C]
    linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [Filter.eventually_all.mpr H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [Filter.eventually_all.mpr (fun j : Fin degree=>hn j M hwork L us hus hret hmesh)] with k hk
  dsimp only at hk ⊢
  intro T i star U kGen seed P₀ hP hdegree hi hs hlen hT hmacroW hsmall hmi hms
  let W:=M.data.d
  let R:=M.data.highErrorEnvelope M.alpha (finiteCutMasses us k) U
  have ho:=finiteCutMasses_ordered us hus k
  have hx:=M.hxs
  have hW:=M.data.hd
  have hscale : 0 ≤ M.data.d^P₀.live.test.edges.length:=pow_nonneg M.data.hd.le _
  have hR j : 0 ≤ R j:=by
    dsimp only [R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ M.data.hTpos.le)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hcost:=add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  by_cases hzero : P₀.live.test.edges.length=0
  · rw [actual_general_generated_high_second_empty_live M.bf M.hf (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) hP hi hs ho (List.length_eq_zero_iff.mp hzero),abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC.le hscale) (sq_nonneg W)) hcost
  · let j : Fin degree:=⟨P₀.live.test.edges.length-1,by omega⟩
    have Hrow:=hk j T i star U kGen seed P₀ hP (by dsimp only [j];omega)
      hi hs hlen hT hmacroW hsmall hmi hms
    have Hlen : j.val+1=P₀.live.test.edges.length:=by dsimp only [j];omega
    rw [Hlen] at Hrow
    have HC:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCj j) hscale) (sq_nonneg W)) hcost
    apply le_trans _ HC
    convert Hrow using 1
    all_goals dsimp only [actualGeneralGeneratedHighSecond,nativePhysicalResourceCenter,W,R]
    all_goals rfl

end OAI.SKFluctuations.Cavity
