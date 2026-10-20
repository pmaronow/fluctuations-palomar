module

public import ComparisonSignedCavityActualGammaFirstHighBoundedDegree
public import ComparisonSignedCavityInheritedGeneratedGammaFirstHighProfile

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_generated_first_high_bounded_degree
    (degree : ℕ) (Bclock Temp Cf Cmass Ccal Rmacro F : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let W:=M.canonicalDirectTestBandScale
        ∀(T : ClockTree (Spin n×Bool) as) (i star U kGen rBound : ℕ)
          (seed : List NativeResourceMark) (P₀ : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed kGen T P₀ → P₀.live.test.edges.length ≤ degree →
          i ≤ star → star < U → U ≤ as.length → T.leaves ≤ rBound →
          W ≤ Rmacro/2 → (Az+1/cl)*(1+Cmass)*W ≤ Rmacro/4 →
          partitionPoint 0 as i ≤ Cmass*M.xs → partitionPoint 0 as star ≤ Cmass*W →
        let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as
          (4*Cf+2*Temp) Temp
        |nativeActualGeneratedFirstHigh M T star U P₀.live.test| ≤
          C*sourceMonomialScale M.xs W (nativeGeneratedCompleteInitial P₀.live.test i)*W^2*
            nativeGammaFirstHighVariation rBound*(T.forkCost R+edgeBudget 0 as R) := by
  classical
  have Hchoose (j : Fin degree):=eventually_actual_minimum_inherited_generated_Gamma_first_high_profile
    (D:=D) (j.val+1) (by omega) Bclock Temp Cf Cmass Ccal Rmacro F hTemp hCf hCm hm hdelta hroom
    hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
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
  intro M hsource hxs hcompare L us hus hret hmesh
  filter_upwards [Filter.eventually_all.mpr (fun j : Fin degree=>hn j M hsource hxs hcompare L us hus hret hmesh)] with k hk
  dsimp only at hk ⊢
  intro T i star U kGen rBound seed P₀ hP hdegree hi hs hlen hT hmacroW hsmall hmi hms
  let W:=M.canonicalDirectTestBandScale
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf (finiteCutMasses us k)
    (4*Cf+2*Temp) Temp
  have ho:=finiteCutMasses_ordered us hus k
  have hx:=M.hxs
  have hW:=M.canonical_direct_test_band_pos
  have hscale : 0 ≤ sourceMonomialScale M.xs W (nativeGeneratedCompleteInitial P₀.live.test i) := by
    unfold sourceMonomialScale
    positivity
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hcost:=add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  by_cases hzero : P₀.live.test.edges.length=0
  · rw [actual_minimum_generated_first_high_empty_live M hP hi hs ho (List.length_eq_zero_iff.mp hzero),abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le hscale) (sq_nonneg W))
      (nativeGammaFirstHighVariation_nonneg rBound)) hcost
  · let j : Fin degree:=⟨P₀.live.test.edges.length-1,by omega⟩
    have Hrow:=hk j T i star U kGen rBound seed P₀ hP (by dsimp only [j];omega)
      hi hs hlen hT hmacroW hsmall hmi hms
    have HC:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCj j) hscale) (sq_nonneg W))
      (nativeGammaFirstHighVariation_nonneg rBound)) hcost
    apply le_trans _ HC
    convert Hrow using 1 <;>
      dsimp only [nativeActualGeneratedFirstHigh,nativePhysicalResourceCenter,nativeGammaFirstHighVariation,W,R]
    all_goals first
      | rfl
      | ring

end OAI.SKFluctuations.Cavity
