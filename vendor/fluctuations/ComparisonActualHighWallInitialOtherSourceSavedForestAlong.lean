module

public import ComparisonActualHighWallInitialOtherSourceSavedAlong
public import ComparisonActualHighWallInitialFourForestEnvelopeAlong
public import ComparisonActualHighWallForestHighContraction
public import ComparisonActualHighWallFreshPairForestOnGrid

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_initial_other_source_saved_forest_along
    {m delta cl cu Az C0 Ct D Bclock L eta c cK : ℝ}
    (depth dOrder : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (htheta1 : 1 ≤ 4/p) (htheta2 : 4/p ≤ 2)
    (hdeficit : 2-4/p ≤ actualMassSavingExponent m delta/128)
    (Cmass Ccut Rmacro F Cx : ℝ) (hCm : 1 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    (hCx : 0 < Cx) (heta : 0 < eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) (hL : 0 < L)
    (hc : 0 < c) (hcout : cu*Az < c) (hcK : 0 < cK)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0))
    (Cs : ℝ) (hCs : 0 < Cs) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,ActualHighWallOverlapMinimum.IsActualHighWallCalibratedSlowWindow
      (M n) ((M n).data.d) L Cs (w n)) :
    ∃Ca Cg Cl Cj C4 CY Ch Cgl Cjl Cd : ℝ,
      0 < Ca ∧ 0 < Cg ∧ 0 < Cl ∧ 0 < Cj ∧ 0 < C4 ∧ 0 < CY ∧ 0 < Ch ∧
      0 < Cgl ∧ 0 < Cjl ∧ 0 < Cd ∧
      ∃C CiU CiB CiM : Fin (1+depth)→ℝ, ∃Cf Cr : ℝ,
      (∀a,0 < C a ∧ 0 < CiU a ∧ 0 < CiB a ∧ 0 < CiM a) ∧ 0 < Cf ∧ 0 < Cr ∧
      ∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses Lnet,u∈us)→
      ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs→(w n).star∈us→∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      ∀(pre mid tail : List PositiveMass),as=pre++(mid++tail)→
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as→0 < mid.length→
      ∀(U : ℕ) (hs : pre.length+mid.length < U) (hU : U ≤ (pre++(mid++tail)).length),
        partitionPoint 0 as pre.length ≤ Cmass*(M n).data.d→
        partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*(M n).data.d→
        partitionPoint 0 as U ≤ Ccut*(M n).data.d→
        (M n).data.d ≤ Rmacro/2→(Az+1/cl)*(1+Cmass)*(M n).data.d ≤ Rmacro/4→
        4*(M n).data.d ≤ (M n).data.wallRadius (M n).alpha (partitionPoint 0 as U)→
        (M n).z ≤ min ((M n).data.wallRadius (M n).alpha (partitionPoint 0 as U)/8) (Rmacro/4)→
        (M n).data.wallRadius (M n).alpha (partitionPoint 0 as pre.length) ≤
          min ((M n).data.wallRadius (M n).alpha (partitionPoint 0 as U)/8) (Rmacro/4)→
        (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length)) ≤
          min ((M n).data.wallRadius (M n).alpha (partitionPoint 0 as U)/8) (Rmacro/4)→
        ∀sourceMass : ℝ,∀hsourceMass : 0 < sourceMass,
        Cx*(M n).xs ≤ sourceMass→partitionPoint 0 as U=sourceMass→
        (∀j ≤ nativeDyadicCutDepth sourceMass,nativeDyadicMassCut sourceMass hsourceMass j∈us)→
        2*c*(M n).data.d ≤ partitionPoint 0 as U→
        cK*(M n).data.d ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as (pre.length+mid.length)→
        let d:=(M n).data.d
        let Di:=nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length+1/(dim n+1:ℕ)
        let CB:=actualLowErrorComparisonConstant (2*max Bclock 0) (max Bclock 0)
        let Dstar:=(1+CB)*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as (pre.length+mid.length)+1/(dim n+1:ℕ))
        let I:=∫u in 0..Ccut*d,Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
          (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)
        let qsecond:=actualHighWallInitialFullB0Envelope (1+depth) C CiU CiB CiM Cf Cr
          (originalHighWallInitialPairErrorScale (M n) as pre.length) d (dim n:ℝ) eta
        let V:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches
          (Bclock/(Real.exp (-4*Bclock)*cK)) 3 2 depth
        let VP:=nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches
          (Bclock/(Real.exp (-4*Bclock)*cK)) 3 2 depth
        let rho:=((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/256))
        |actualGeneralFourOtherSourceErrorSum (M n).bf (M n).hf U d
          (actualGeneralFourCenteredForest (n:=dim n) (M n).bf (M n).hf hs hU d depth
            [nativeActualInitialState (S:=Spin (dim n)×Bool) (pre++(mid++tail)) pre.length
              (pre.length+mid.length) 0 (by omega)])| ≤
          d^4*(Ca*((dim n:ℝ)^(-eta))+Cg*((dim n:ℝ)^(-eta))+
            Cd*((dim n+1:ℕ):ℝ)^(-m)+2*qsecond)*(2*V)+
          d^3*(CY*Di+(CY+Cgl+Cjl)*Dstar+CY*I)*(2*V)+
          d^2*(Ca+2*Cl+Cj+C4+CY)*(2*VP*rho*d^2)+
          d^3*(Ca+2*Cl+Cj+C4+CY+Ch)*(2*VP*rho*d) := by
  obtain ⟨Ca,Cg,Cl,Cj,C4,CY,Ch,Cgl,Cjl,Cd,hCa,hCg,hCl,hCj,hC4,hCY,hCh,hCgl,hCjl,hCd,
    C,CiU,CiB,CiM,Cf,Cr,hpositive,hCf,hCr,Hsource⟩:=
    eventually_actual_high_wall_initial_four_other_source_saved_along (D:=D)
      (1+depth) dOrder (3+6*depth) hd p hp hOrder Cmass Ccut Rmacro F Cx hCm hCcut
      hCx heta hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius
      hL dim hdim M hfixed hdlim Cs hCs w hw
  have Hprofile:=eventually_actual_high_wall_full_forest_HIGH_profile_contraction
    hm hdelta hroom hcl hcu hAz hC0 hCt hc hcout hcK dim hdim M
    (fun n=> by rw [hfixed n]) hdlim hsRatio depth
  have Hcut1 : ∀ᶠn in atTop,Ccut*(M n).data.d ≤ 1 := by
    have HH:=(hdlim.const_mul Ccut).eventually
      (eventually_le_nhds (show Ccut*(0:ℝ) < 1 by simp))
    simpa only [mul_zero] using HH
  let CW:=Bclock/(Real.exp (-4*Bclock)*cK)
  let V:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches CW 3 2 depth
  let VP:=nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches CW 3 2 depth
  have hBc : 0 ≤ Bclock:=(M 0).data.hTpos.le.trans (M 0).hT
  have hCW : 0 ≤ CW:=by dsimp only [CW];positivity
  have hV : 0 ≤ V:=nativeActualWeightedFrontierCost_nonneg _ hCW _ _ _
  have hVP : 0 ≤ VP:=nativeActualWeightedProfileFrontierCost_nonneg _ hCW _ _ _
  refine ⟨Ca,Cg,Cl,Cj,C4,CY,Ch,Cgl,Cjl,Cd,hCa,hCg,hCl,hCj,hC4,hCY,hCh,hCgl,hCjl,hCd,
    C,CiU,CiB,CiM,Cf,Cr,hpositive,hCf,hCr,?_⟩
  filter_upwards [Hsource,Hprofile,Hcut1] with n hnsource hnprofile hncut1
  intro Lnet us hus hret hmesh hstar
  filter_upwards [hnsource Lnet us hus hret hmesh hstar,hnprofile] with jGrid hjsource hjprofile
  dsimp only at hjsource hjprofile ⊢
  intro pre mid tail hparts hindex hmid U hs hU hmi hms hcut hsmall hsmall2 hhigh hz hri hrs
    sourceMass hsourceMass hsource hsourceeq hnodes hcutlower hK
  let a:=M n
  let as:=pre++(mid++tail)
  let K:=nativeContinuumMixedClock (dim n) a.bf a.hf as
  let b:=fun l=>(a.bf (partitionPoint 0 as l):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as pre.length (pre.length+mid.length)) tag=>
    nativeOriginalClockParentWeight a.data.d U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  have hi : pre.length ≤ pre.length+mid.length:=by omega
  let root:=nativeActualInitialState (S:=Spin (dim n)×Bool) as pre.length (pre.length+mid.length)
    0 (hi.trans (hs.le.trans hU))
  let roots:=[root]
  have Hroot : NativeActualResourceGenerated pre.length (pre.length+mid.length) U [.initial]
      root.generation root.tree root.term:=
    .physical (.seed as hU 0 .initial (Or.inl rfl) (hi.trans (hs.le.trans hU)))
  have HLroot:=nativeActualInitialState_leaves_le (S:=Spin (dim n)×Bool) as pre.length
    (pre.length+mid.length) 0 (hi.trans (hs.le.trans hU))
  let rows:=actualGeneralFourCenteredForest (n:=dim n) a.bf a.hf hs hU a.data.d depth roots
  let R:=a.data.highErrorEnvelope a.alpha as U
  let f:=fun l=>(R l)^(4/p)
  have ho : MassOrdered 0 as:=by dsimp only [as];rw [←hparts];exact finiteCutMasses_ordered us hus jGrid
  have hdpos : 0 < a.data.d:=a.data.hd
  have hK' : cK*a.data.d ≤ K (pre.length+mid.length):=by simpa only [K,as,hparts,a] using hK
  have Hsrc:=hjsource pre mid tail
  have Hlocal Q (hQ : Q∈rows) :
      |(a.data.d⁻¹)^Q.generation*actualGeneralFourOtherSourceErrorContrast a.bf a.hf U Q| ≤
        |Q.term.coefficient| *nativeResourceScale a.data.d a.data.d 1 [.initial]*
          (a.data.d^3*(Ca*((dim n:ℝ)^(-eta))+Cg*((dim n:ℝ)^(-eta))+
              Cd*((dim n+1:ℕ):ℝ)^(-m)+2*actualHighWallInitialFullB0Envelope (1+depth)
                C CiU CiB CiM Cf Cr (originalHighWallInitialPairErrorScale a as pre.length)
                a.data.d (dim n:ℝ) eta)+
            a.data.d^2*(CY*(nativeOriginalCutLowErrorRadius (dim n) a.bf a.hf as pre.length+1/(dim n+1:ℕ))+
              (CY+Cgl+Cjl)*(1+actualLowErrorComparisonConstant (2*max Bclock 0) (max Bclock 0))*
                (nativeOriginalCutLowErrorRadius (dim n) a.bf a.hf as (pre.length+mid.length)+1/(dim n+1:ℕ))+
              CY*(∫u in 0..Ccut*a.data.d,Real.sqrt (orderedPathB (dim n+1) a.bf a.hf u-
                (orderedPathS (dim n+1) a.bf a.hf u)^2)))+
            a.data.d*(Ca+2*Cl+Cj+C4+CY)*
              ((Q.tree.forkCost f+edgeBudget 0 as f)+
                a.data.d*(Q.tree.forkCost R+edgeBudget 0 as R))+
            a.data.d^2*Ch*(Q.tree.forkCost R+edgeBudget 0 as R)) := by
    have HV:=nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth roots
      (by intro P hP;obtain rfl:=List.mem_singleton.mp hP;exact Hroot) Q hQ
    have HG:=nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth roots 0
      (by intro P hP;obtain rfl:=List.mem_singleton.mp hP;rfl) Q hQ
    have HL:=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth roots 2
      (by intro P hP;obtain rfl:=List.mem_singleton.mp hP;exact HLroot) Q hQ
    have Hdepth : Q.term.resources.length ≤ 1+depth:=by rw [HV.total_factor_depth,HG];simp
    have HH:=Hsrc hparts hindex U hU Q HV Hdepth hmid hs (HL.trans (by omega))
      hmi hms hcut hncut1 hsmall hsmall2 hhigh hz hri hrs sourceMass hsourceMass
      hsource hsourceeq hnodes
    rw [hparts] at HH
    convert HH using 1
    dsimp only [f,R,as,a]
    ring
  have HC0:=actual_high_wall_four_forest_coefficient_variation_le a ho hs hU hdpos hcK hK'
    depth 2 roots (by intro Q hQ;obtain rfl:=List.mem_singleton.mp hQ;exact HLroot)
  have Hcoef : (rows.map (fun Q=>|Q.term.coefficient|)).sum ≤ 2*V:=by
    simpa only [V,CW,rows,roots,root,nativeActualInitialState,NativeResourceTerm.ofLive,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,abs_one,mul_one] using HC0
  have HP:=hjprofile us hus
  rw [hparts] at HP
  have HP0:=HP pre.length (pre.length+mid.length) U hi hs hU
    (by simpa only [hparts] using hcutlower) hK' (4/p) htheta1 htheta2 hdeficit 0
  have hrate : a.data.N^(-(actualMassSavingExponent m delta/256)) ≤ 1:=
    Real.rpow_le_one_of_one_le_of_nonpos
      (by dsimp only [ActualHighWallData.N];exact_mod_cast (show 1 ≤ dim n+1 by omega))
      (neg_nonpos.mpr (div_nonneg (actualMassSavingExponent_pos hm hdelta).le (by norm_num)))
  have Hprof : (rows.map (fun Q=>|Q.term.coefficient| *
      (Q.tree.forkCost (fun l=>f l+a.data.d*R l)+
        edgeBudget 0 as (fun l=>f l+a.data.d*R l)))).sum ≤
      2*VP*a.data.N^(-(actualMassSavingExponent m delta/256))*a.data.d^2:=by
    simpa only [VP,CW,rows,roots,root,as,a,f,R] using HP0
  have hR l : 0 ≤ R l:=a.data.highErrorEnvelope_nonneg a.alpha as U l
  have hF l : 0 ≤ f l:=Real.rpow_nonneg (hR l) _
  have Hpower:=actual_general_four_initial_forest_power_sum_le_combined_profile ho
    a.data.d hdpos.le f R hR rows
  have Hradius:=actual_general_four_initial_forest_radius_sum_le_combined_profile ho
    a.data.d f R hF rows
  have HpowBound : (rows.map (fun Q=>|Q.term.coefficient| *
      (Q.tree.forkCost f+edgeBudget 0 as f))).sum ≤
      2*VP*a.data.N^(-(actualMassSavingExponent m delta/256))*a.data.d^2:=
    Hpower.trans Hprof
  have HradBound : (rows.map (fun Q=>|Q.term.coefficient| *
      (Q.tree.forkCost R+edgeBudget 0 as R))).sum ≤
      2*VP*a.data.N^(-(actualMassSavingExponent m delta/256))*a.data.d:=by
    apply (mul_le_mul_iff_right₀ hdpos).mp
    calc
      a.data.d*(rows.map (fun Q=>|Q.term.coefficient| *
          (Q.tree.forkCost R+edgeBudget 0 as R))).sum ≤
          2*VP*a.data.N^(-(actualMassSavingExponent m delta/256))*a.data.d^2:=
        Hradius.trans Hprof
      _=a.data.d*(2*VP*a.data.N^(-(actualMassSavingExponent m delta/256))*a.data.d):=by ring
  let Di:=nativeOriginalCutLowErrorRadius (dim n) a.bf a.hf as pre.length+1/(dim n+1:ℕ)
  let CB:=actualLowErrorComparisonConstant (2*max Bclock 0) (max Bclock 0)
  let Dstar:=(1+CB)*(nativeOriginalCutLowErrorRadius (dim n) a.bf a.hf as (pre.length+mid.length)+1/(dim n+1:ℕ))
  let I:=∫u in 0..Ccut*a.data.d,Real.sqrt (orderedPathB (dim n+1) a.bf a.hf u-
    (orderedPathS (dim n+1) a.bf a.hf u)^2)
  let qsecond:=actualHighWallInitialFullB0Envelope (1+depth) C CiU CiB CiM Cf Cr
    (originalHighWallInitialPairErrorScale a as pre.length) a.data.d (dim n:ℝ) eta
  have hDi : 0 ≤ Di:=by dsimp only [Di];exact add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hCB : 0 ≤ CB:=actualLowErrorComparisonConstant_nonneg _ (le_max_right _ _)
  have hDstar : 0 ≤ Dstar:=by
    dsimp only [Dstar]
    exact mul_nonneg (by linarith only [hCB]) (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hI : 0 ≤ I:=intervalIntegral.integral_nonneg (mul_nonneg hCcut hdpos.le)
    (fun _ _=>Real.sqrt_nonneg _)
  have hqsecond : 0 ≤ qsecond:=actual_high_wall_initial_full_B0_envelope_nonneg
    (1+depth) C CiU CiB CiM Cf Cr _ a.data.d (dim n:ℝ) eta
    (fun z=>(hpositive z).1.le) (fun z=>(hpositive z).2.1.le)
    (fun z=>(hpositive z).2.2.1.le) (fun z=>(hpositive z).2.2.2.le)
    hCf.le hCr.le (original_high_wall_initial_pair_error_scale_nonneg a as pre.length)
    hdpos.le (Nat.cast_nonneg _)
  have hA : 0 ≤ Ca*((dim n:ℝ)^(-eta))+Cg*((dim n:ℝ)^(-eta))+
      Cd*((dim n+1:ℕ):ℝ)^(-m)+2*qsecond:=by
    have hN : 0 ≤ (dim n:ℝ)^(-eta):=Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hN1 : 0 ≤ ((dim n+1:ℕ):ℝ)^(-m):=Real.rpow_nonneg (Nat.cast_nonneg _) _
    positivity
  have hB : 0 ≤ CY*Di+(CY+Cgl+Cjl)*Dstar+CY*I:=by positivity
  have hCP : 0 ≤ Ca+2*Cl+Cj+C4+CY:=by positivity
  have Hforest:=actual_high_wall_initial_four_centered_forest_modulus_price
    a as pre.length (pre.length+mid.length) U depth (1+depth) hi hs hU
    C CiU CiB CiM Cf Cr eta
    ((dim n:ℝ)^(-eta)) ((dim n:ℝ)^(-eta)) (((dim n+1:ℕ):ℝ)^(-m)) Di Dstar I
    Ca Cg Cl Cj C4 CY Ch Cgl Cjl Cd f R
    (2*V) (2*VP*a.data.N^(-(actualMassSavingExponent m delta/256))*a.data.d^2)
    (2*VP*a.data.N^(-(actualMassSavingExponent m delta/256))*a.data.d)
    hA hB hCP hCh.le
    (fun Q hQ => by simpa only [Di,Dstar,CB,I,mul_assoc] using Hlocal Q hQ)
    Hcoef HpowBound HradBound
  rw [hparts]
  simpa only [a,as,Di,Dstar,CB,I,qsecond,V,VP,CW,ActualHighWallData.N] using Hforest

end OAI.SKFluctuations.Cavity
