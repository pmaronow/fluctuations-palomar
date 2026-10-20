module

public import ComparisonActualHighWallOtherSourceOriginalProfileAlong
public import ComparisonActualGeneralOtherSourceProfileSum
public import ComparisonActualHighWallFreshPairForestOnGrid
public import ComparisonActualHighWallConstantChildrenHighContractionAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 36000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_constant_children_other_source_cubic_along
    {m delta cl cu Az C0 Ct D Bclock L eta c cK : ℝ}
    (depth dOrder : ℕ) (hd : 0< dOrder)
    (p : ℝ) (hp : 2< p) (hOrder : p/(p-2)≤ (dOrder:ℝ))
    (htheta1 : 1≤ 4/p) (htheta2 : 4/p≤ 2)
    (hdeficit : 2-4/p≤ actualMassSavingExponent m delta/128)
    (Cmass Ccut Rmacro F Cx : ℝ) (hCm : 1≤ Cmass) (hCcut : 0≤ Ccut)
    (hCx : 0< Cx) (heta : 0< eta)
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta< 3*m) (hgap : 2*eta< 6*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct)
    (hmacro : 0< Rmacro) (hRhalf : Rmacro≤ 1/2)
    (hFmass : 1+2*cu≤ F) (hFradius : 1+1/Rmacro≤ F) (hL : 0< L)
    (hc : 0< c) (hcout : cu*Az< c) (hcK : 0< cK)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n=> (M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=> (M n).data.s/(M n).data.d) atTop (𝓝 0))
    (Cs : ℝ) (hCs : 0< Cs) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,ActualHighWallOverlapMinimum.IsActualHighWallCalibratedSlowWindow
      (M n) ((M n).data.d) L Cs (w n)) :
    ∃C : ℝ,0< C ∧ ∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val≤ 1)→(∀u∈uniformMasses Lnet,u∈us)→
      ((Lnet+1:ℕ):ℝ)⁻¹≤ (M n).xs→(w n).star∈us→∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      ∀(mid tail : List PositiveMass),as=mid++tail→
      mid.length=retainedMassPrefixIndex (w n).star.val as→0< mid.length→
      ∀(U : ℕ) (hs : mid.length< U) (hU : U≤ (mid++tail).length),
        partitionPoint 0 as mid.length≤ Cmass*(M n).data.d→
        partitionPoint 0 as U≤ Ccut*(M n).data.d→
        (M n).data.d≤ Rmacro/2→(Az+1/cl)*(1+Cmass)*(M n).data.d≤ Rmacro/4→
        4*(M n).data.d≤ (M n).data.wallRadius (M n).alpha (partitionPoint 0 as U)→
        (M n).z≤ min ((M n).data.wallRadius (M n).alpha (partitionPoint 0 as U)/8) (Rmacro/4)→
        (M n).data.wallRadius (M n).alpha (partitionPoint 0 as 0)≤
          min ((M n).data.wallRadius (M n).alpha (partitionPoint 0 as U)/8) (Rmacro/4)→
        (M n).data.wallRadius (M n).alpha (partitionPoint 0 as mid.length)≤
          min ((M n).data.wallRadius (M n).alpha (partitionPoint 0 as U)/8) (Rmacro/4)→
        ∀sourceMass : ℝ,∀hsourceMass : 0< sourceMass,
        Cx*(M n).xs≤ sourceMass→partitionPoint 0 as U=sourceMass→
        (∀j≤ nativeDyadicCutDepth sourceMass,nativeDyadicMassCut sourceMass hsourceMass j∈us)→
        2*c*(M n).data.d≤ partitionPoint 0 as U→
        cK*(M n).data.d≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as mid.length→
        |actualGeneralFourOtherSourceErrorSum (M n).bf (M n).hf U (M n).data.d
          (actualGeneralFourCenteredForest (n:=dim n) (M n).bf (M n).hf hs hU (M n).data.d depth
            (actualGeneralConstantSourceChildren (n:=dim n) (M n).bf (M n).hf (mid++tail)
              mid.length U hs hU))|≤ C*(M n).data.d^3 := by
  obtain ⟨Csource,hCsource,Hsource⟩:=eventually_actual_high_wall_four_other_source_original_profile_along
    (1+depth) dOrder (3+6*depth) hd p hp hOrder Cmass Ccut Rmacro F Cx hCm hCcut hCx heta
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius hL
    dim hdim M hfixed hdlim Cs hCs w hw
  have Hprofile:=eventually_actual_high_wall_constant_children_forest_HIGH_profile_contraction
    hm hdelta hroom hcl hcu hAz hC0 hCt hc hcout hcK dim hdim M
    (fun n=> by rw [hfixed n]) hdlim hsRatio depth
  let CW:=Bclock/(Real.exp (-4*Bclock)*cK)
  let V:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches CW 3 3 depth
  let VP:=nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches CW 3 3 depth
  let C:=1+Csource*(12*V+24*VP)
  have hBc : 0≤ Bclock:=(M 0).data.hTpos.le.trans (M 0).hT
  have hCW : 0≤ CW:=by dsimp only [CW];positivity
  have hV : 0≤ V:=nativeActualWeightedFrontierCost_nonneg _ hCW _ _ _
  have hVP : 0≤ VP:=nativeActualWeightedProfileFrontierCost_nonneg _ hCW _ _ _
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  filter_upwards [Hsource,Hprofile] with n hnsource hnprofile
  intro Lnet us hus hret hmesh hstar
  filter_upwards [hnsource Lnet us hus hret hmesh hstar,hnprofile] with jGrid hjsource hjprofile
  dsimp only at hjsource hjprofile ⊢
  intro mid tail hparts hindex hmid U hs hU hms hcut hsmall hsmall2 hhigh hz hri hrs
    sourceMass hsourceMass hsource hsourceeq hnodes hcutlower hK
  let a:=M n
  let as:=mid++tail
  let K:=nativeContinuumMixedClock (dim n) a.bf a.hf as
  let b:=fun l=> (a.bf (partitionPoint 0 as l):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as 0 mid.length) tag=>
    nativeOriginalClockParentWeight a.data.d U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let roots:=actualGeneralConstantSourceChildren (n:=dim n) a.bf a.hf as mid.length U hs hU
  let rows:=actualGeneralFourCenteredForest (n:=dim n) a.bf a.hf hs hU a.data.d depth roots
  let R:=a.data.highErrorEnvelope a.alpha as U
  let f:=fun l=> (R l)^(4/p)
  have ho : MassOrdered 0 as:=by dsimp only [as];rw [←hparts];exact finiteCutMasses_ordered us hus jGrid
  have hdpos : 0< a.data.d:=a.data.hd
  have hK' : cK*a.data.d≤ K mid.length:=by simpa only [K,as,hparts,a] using hK
  let PI (ss : ℕ) : Prop :=
    ∀Q : NativeActualResourceState (Spin (dim n)×Bool) as 0 ss,
      NativeActualResourceGenerated 0 ss U [] Q.generation Q.tree Q.term→
      Q.term.resources.length≤ 1+depth→Q.tree.leaves≤ 3+6*depth→
      |(a.data.d⁻¹)^Q.generation*actualGeneralFourOtherSourceErrorContrast a.bf a.hf U Q|≤
        |Q.term.coefficient| *1*Csource*(a.data.d^3+
          a.data.d*(Q.tree.forkCost (fun l=> f l+a.data.d*R l)+edgeBudget 0 as (fun l=> f l+a.data.d*R l))+
            a.data.d^2*(Q.tree.forkCost R+edgeBudget 0 as R))
  have HP0 : PI (0+mid.length):=by
    intro Q HV Hdepth HL
    have HH:=hjsource [] mid tail hparts
      (by simpa only [List.length_nil,Nat.zero_add] using hindex) U hU [] Q HV Hdepth hmid
      (by simpa only [List.length_nil,Nat.zero_add] using hs) HL
      (by simpa only [List.length_nil,partitionPoint,partitionValues_zero,id_eq] using
        mul_nonneg (zero_le_one.trans hCm) hdpos.le)
      (by simpa only [List.length_nil,Nat.zero_add] using hms) hcut hsmall hsmall2 hhigh hz hri
      (by simpa only [List.length_nil,Nat.zero_add] using hrs)
      sourceMass hsourceMass hsource hsourceeq hnodes
    rw [actual_general_high_whole_profile_linear]
    simpa only [nativeResourceScale,List.map_nil,List.prod_nil,List.nil_append,mul_one,f,R,as,a] using HH
  have HPI : PI mid.length:=Nat.zero_add mid.length ▸ HP0
  have Hlocal Q (hQ : Q∈rows) :
      |(a.data.d⁻¹)^Q.generation*actualGeneralFourOtherSourceErrorContrast a.bf a.hf U Q|≤
        |Q.term.coefficient| *1*Csource*(a.data.d^3+
          a.data.d*(Q.tree.forkCost (fun l=> f l+a.data.d*R l)+edgeBudget 0 as (fun l=> f l+a.data.d*R l))+
            a.data.d^2*(Q.tree.forkCost R+edgeBudget 0 as R)):=by
    have HV:=nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth roots
      (fun P hP=> actualGeneralConstantSourceChildren_valid a.bf a.hf hs hU P hP) Q hQ
    have HG:=nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth roots 1
      (fun P hP=> actualGeneralConstantSourceChildren_generation a.bf a.hf hs hU P hP) Q hQ
    have HL:=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth roots 3
      (fun P hP=> actualGeneralConstantSourceChildren_leaves a.bf a.hf hs hU P hP) Q hQ
    have Hdepth : Q.term.resources.length≤ 1+depth:=by rw [HV.total_factor_depth,HG];simp
    exact HPI Q HV Hdepth HL
  have HC0:=actual_high_wall_four_forest_coefficient_variation_le a ho hs hU hdpos hcK hK'
    depth 3 roots (fun Q hQ=> actualGeneralConstantSourceChildren_leaves a.bf a.hf hs hU Q hQ)
  have Hroots:=actualGeneralConstantSourceChildren_coefficient_variation (n:=dim n) a.bf a.hf
    (a.data.bf_monotone a.alpha) (a.data.hf_monotone a.alpha) ho hs hU
  have Hcoef : (rows.map (fun Q=>|Q.term.coefficient|)).sum≤ 12*V:=by
    have HH:=HC0.trans (mul_le_mul_of_nonneg_left Hroots (mul_nonneg (by norm_num : (0:ℝ)≤ 2) hV))
    convert HH using 1;dsimp only [V,CW,rows];ring
  have HP:=hjprofile us hus
  rw [hparts] at HP
  have HP0:=HP mid.length U hs hU (by simpa only [hparts] using hcutlower) hK' (4/p) htheta1 htheta2 hdeficit
  have hrate : a.data.N^(-(actualMassSavingExponent m delta/256))≤ 1:=
    Real.rpow_le_one_of_one_le_of_nonpos (by dsimp only [ActualHighWallData.N];exact_mod_cast (show 1≤ dim n+1 by omega))
      (neg_nonpos.mpr (div_nonneg (actualMassSavingExponent_pos hm hdelta).le (by norm_num)))
  have Hprof : (rows.map (fun Q=>|Q.term.coefficient| *
      (Q.tree.forkCost (fun l=> f l+a.data.d*R l)+edgeBudget 0 as (fun l=> f l+a.data.d*R l)))).sum≤ 12*VP*a.data.d^2:=by
    apply HP0.trans
    have HH:=mul_le_mul_of_nonneg_left hrate (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤ 12) hVP) (sq_nonneg a.data.d))
    convert HH using 1 <;> dsimp only [VP,CW,a] <;> ring
  have Hfinal:=actual_general_four_other_source_sum_abs_le_of_profile_and_variation a.bf a.hf ho hdpos
    (by norm_num : (0:ℝ)≤ 1) hCsource.le f R (fun l=> Real.rpow_nonneg (a.data.highErrorEnvelope_nonneg a.alpha as U l) _)
    (fun l=> a.data.highErrorEnvelope_nonneg a.alpha as U l) rows Hlocal Hcoef Hprof
  apply Hfinal.trans
  change 1*Csource*(a.data.d^3*(12*V)+2*a.data.d*(12*VP*a.data.d^2))≤ C*a.data.d^3
  dsimp only [C]
  nlinarith only [pow_nonneg hdpos.le 3]

end OAI.SKFluctuations.Cavity
