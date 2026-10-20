module

public import ComparisonActualHighWallFourFirstHighProfile
public import ComparisonActualGeneralFirstHighProfileSum
public import ComparisonActualHighWallConstantChildrenHighRContractionAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_constant_children_first_HIGH_quadratic_along
    {m delta cl cu Az C0 Ct D Bclock c cK : ℝ}
    (depth : ℕ) (Cmass Rmacro F : ℝ) (hCm : 0 ≤ Cmass)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (hc : 0 < c) (hcout : cu*Az < c) (hcK : 0 < cK)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0)) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses Lnet,u∈us) →
      ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      ∀(star U : ℕ) (hs : star < U) (hU : U ≤ as.length),
        partitionPoint 0 as star ≤ Cmass*(M n).data.d →
        (M n).data.d ≤ Rmacro/2 → (Az+1/cl)*(1+Cmass)*(M n).data.d ≤ Rmacro/4 →
        2*c*(M n).data.d ≤ partitionPoint 0 as U →
        cK*(M n).data.d ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        |actualGeneralFourFirstHighErrorSum (M n).bf (M n).hf U (M n).data.d
          (actualGeneralFourCenteredForest (n:=dim n) (M n).bf (M n).hf hs hU (M n).data.d depth
            (actualGeneralConstantSourceChildren (n:=dim n) (M n).bf (M n).hf as star U hs hU))| ≤
          C*(M n).data.d^2 := by
  obtain ⟨C0p,hC0p,H0p⟩:=eventually_actual_high_wall_four_first_high_profile
    (D:=D) (1+depth) Bclock Cmass Rmacro F cK hCm hcK hm hdelta hroom
    hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius
  have HP:=eventually_actual_high_wall_constant_children_forest_HIGH_R_contraction
    hm hdelta hroom hcl hcu hAz hC0 hCt hc hcout hcK dim hdim M
    (fun n=>(hfixed n).le) hdlim hsRatio depth
  let CW:=Bclock/(Real.exp (-4*Bclock)*cK)
  let VP:=nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches CW 3 3 depth
  let variation:=nativeGammaFirstHighVariation (4+6*depth)
  have hBc : 0 ≤ Bclock:=(M 0).data.hTpos.le.trans (M 0).hT
  have hCW : 0 ≤ CW:=by dsimp only [CW];positivity
  have hVP : 0 ≤ VP:=nativeActualWeightedProfileFrontierCost_nonneg _ hCW _ _ _
  have hv : 0 ≤ variation:=nativeGammaFirstHighVariation_nonneg _
  let C:=12*C0p*variation*VP+1
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  filter_upwards [hdim.eventually H0p,HP] with n hn0 hnP
  intro Lnet us hus hret hmesh
  filter_upwards [hn0 (M n) (hfixed n) Lnet us hus hret hmesh,hnP] with jGrid hj0 hjP
  dsimp only at hj0 hjP ⊢
  intro star U hs hU hmass hsmall hsmall2 hcutlo hK
  let a:=M n
  let as:=finiteCutMasses us jGrid
  let K:=nativeContinuumMixedClock (dim n) a.bf a.hf as
  let b:=fun l=>(a.bf (partitionPoint 0 as l):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as 0 star) tag=>
    nativeOriginalClockParentWeight a.data.d U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let children:=actualGeneralConstantSourceChildren (n:=dim n) a.bf a.hf as star U hs hU
  let rows:=actualGeneralFourCenteredForest (n:=dim n) a.bf a.hf hs hU a.data.d depth children
  let R:=a.data.highErrorEnvelope a.alpha as U
  have Hchildren : ∀Q∈children,NativeActualResourceGenerated 0 star U [] Q.generation Q.tree Q.term:=
    fun Q hQ=>actualGeneralConstantSourceChildren_valid a.bf a.hf hs hU Q hQ
  have Hrow Q (hQ : Q∈rows) : |actualGeneralFourFirstHighError a.bf a.hf U a.data.d Q| ≤
      (C0p*a.data.d*variation)*(|Q.term.coefficient| *(Q.tree.forkCost R+edgeBudget 0 as R)):=by
    have HV:=nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth children Hchildren Q hQ
    have HG:=nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth children 1
      (fun P hP=>actualGeneralConstantSourceChildren_generation a.bf a.hf hs hU P hP) Q hQ
    have HL:=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth children 3
      (fun P hP=>actualGeneralConstantSourceChildren_leaves a.bf a.hf hs hU P hP) Q hQ
    have Hdegree : Q.term.resources.length ≤ 1+depth:=by
      rw [HV.total_factor_depth]
      simpa only [List.length_nil,zero_add] using HG.le
    have Hmi : partitionPoint 0 as 0 ≤ Cmass*a.xs:=by
      simp only [partitionPoint,partitionValues_zero,id_eq]
      exact mul_nonneg hCm a.hxs.le
    have HH:=hj0 0 star U (3+6*depth) [] Q HV Hdegree (Nat.zero_le _) hs hU HL
      hsmall hsmall2 Hmi hmass hK
    have HE : 3+6*depth+1=4+6*depth:=by omega
    rw [HE] at HH
    simpa only [nativeResourceScale,List.map_nil,List.prod_nil,mul_one,variation,mul_assoc,mul_left_comm,mul_comm] using HH
  have HS:=actual_general_first_high_error_sum_abs_le_of_profile a.bf a.hf a.data.d
    (C0p*a.data.d*variation) rows R Hrow
  have Hprof:=hjP us hus star U hs hU hcutlo hK
  change (rows.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost R+edgeBudget 0 as R))).sum ≤
    12*VP*a.data.N^(-(actualMassSavingExponent m delta/256))*a.data.d at Hprof
  have hdpos:=a.data.hd
  have H1:=mul_le_mul_of_nonneg_left Hprof (show 0 ≤ C0p*a.data.d*variation by positivity)
  have hN1 : 1 ≤ a.data.N:=by dsimp only [a,ActualHighWallData.N];exact_mod_cast (by omega : 1 ≤ dim n+1)
  have Hpow : a.data.N^(-(actualMassSavingExponent m delta/256)) ≤ 1:=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by have H:=actualMassSavingExponent_pos hm hdelta;linarith)
  apply (HS.trans H1).trans
  have H2:=mul_le_mul_of_nonneg_right Hpow (show 0 ≤ 12*C0p*variation*VP*a.data.d^2 by positivity)
  have H3 : 0 ≤ a.data.d^2:=sq_nonneg _
  change C0p*a.data.d*variation*(12*VP*a.data.N^(-(actualMassSavingExponent m delta/256))*a.data.d) ≤ C*a.data.d^2
  dsimp only [C]
  nlinarith only [H2,H3]

end OAI.SKFluctuations.Cavity
