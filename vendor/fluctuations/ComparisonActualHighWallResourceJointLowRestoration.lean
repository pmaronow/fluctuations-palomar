module

public import ComparisonActualHighWallJointLowRestorationPrice
public import ComparisonActualHighWallRawResourcePairBudget
public import ComparisonActualGeneralResourceJointLowRestorationReadout
public import ComparisonSignedCavityActualResourceJointLowRestorationFromMinimum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_resource_joint_LOW_restoration_from_minimum
    (degree rBound : ℕ) (Bclock Cmass Ccut : ℝ) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound → seed.length+k ≤ degree →
        partitionPoint 0 as i ≤ Cmass*M.data.d → partitionPoint 0 as star ≤ Cmass*M.data.d →
        partitionPoint 0 as U ≤ Ccut*M.data.d →
        ∀a z : T.Slot,T.splitIndex a z<U →
        let R:=actualLowErrorComparisonConstant (2*M.data.T) M.data.T*
          (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex a z)+1/(n+1:ℕ))
        |(M.data.d⁻¹)^k*actualGeneralResourceJointLowRestoration M.bf M.hf U P a z| ≤
          |P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*(C*R*M.data.d^2) := by
  classical
  have HP (a : Fin (degree+1)):=eventually_actual_high_wall_canonical_joint_LOW_restoration_price
    (D:=D) a.val rBound Bclock Cmass Ccut hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  choose C hC HC using HP
  let Cmax:=1+∑a : Fin (degree+1),C a
  have hsum : 0 ≤ ∑a : Fin (degree+1),C a:=Finset.sum_nonneg (fun a _=>(hC a).le)
  have hCmax : 0 < Cmax:=by dsimp only [Cmax];linarith
  have hdom a : C a ≤ Cmax:=by
    have H:=Finset.single_le_sum (fun a _=>(hC a).le) (Finset.mem_univ a)
    dsimp only [Cmax]
    linarith
  obtain ⟨A,hA,HA⟩:=eventually_actual_high_wall_raw_resource_pair_budget
    (D:=D) (degree+1) (by omega) Bclock Cmass hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  refine ⟨Cmax*A^degree,by positivity,?_⟩
  filter_upwards [Filter.eventually_all.mpr HC,HA] with n hn hnA
  intro M hwork L us hus hret hmesh
  have Hgrids a:=hn a M hwork L us hus hret hmesh
  filter_upwards [Filter.eventually_all.mpr Hgrids,hnA M hwork L us hus hret hmesh] with jGrid hj hjA
  dsimp only at hj hjA ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth hmi hms hcut aSlot z haz
  let W:=M.data.d
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=actualLowErrorComparisonConstant (2*M.data.T) M.data.T*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex aSlot z)+1/(n+1:ℕ))
  let G:=nativeActualResourceCanonicalShape P.live hi (hs.trans_le hU)
  let I:=nativeActualResourceInitialFactors P.live
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hR : 0 ≤ R:=mul_nonneg (actualLowErrorComparisonConstant_nonneg _
    (M.data.hepsilon.1.le.trans M.data.hepsilon.2.le)) (by
    dsimp only [nativeOriginalCutLowErrorRadius]
    positivity)
  have hprice : 0 ≤ Cmax*R*W^2:=by positivity
  have Hdegree : P.resources.length ≤ degree+1:=by rw [hP.total_factor_depth];omega
  have Hpair:=hjA U i star T P Hdegree (hi.trans (hs.le.trans hU)) (hs.le.trans hU)
    hmi hms 1 1 (by norm_num) (by norm_num)
  have Hlive : P.live.factors.length ≤ degree:=by
    have Hlen:=hP.total_factor_depth
    simp only [NativeResourceTerm.resources,List.length_append,NativeResourceMonomial.tags,List.length_map] at Hlen
    omega
  let a : Fin (degree+1):=⟨P.live.factors.length,by omega⟩
  have Hmass : ∀e,G.sourceLowMass e ≤ Cmass*M.data.d:=by
    intro e
    have H:=native_actual_resource_canonical_source_mass P.live hi (hs.trans_le hU)
      Cmass M.data.d M.data.d hmi hms e
    simpa only [sourceFactorScale,ite_self] using H
  have HL:=hj a U T hU hT G (fun _=>.centered) hcut Hmass aSlot z haz
  have Hscale : nativeResourceScale M.data.d M.data.d 1 P.live.tags=M.data.d^P.live.factors.length:=by
    rw [←native_actual_resource_live_scale_eq_annotations,←source_factor_scale_product]
    simp [sourceFactorScale]
  dsimp only [a] at HL
  rw [←Hscale] at HL
  have Hcenter : nativePhysicalResourceCenter n M.bf M.hf as=
      (fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)):=by
    funext j
    exact (native_ordered_source_center_eq_completed n M.bf M.hf
      (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) (partitionPoint_mem as ho j)).symm
  rw [←Hcenter] at HL
  have HL' : |nativeCenteredLowGammaLowRestoration n q U b h K (nativePhysicalResourceCenter n M.bf M.hf as) T
      (G.canonicalPhysicalSource M.bf M.hf (fun _=>NativeSourceFactorForm.centered)).restProduct aSlot z| ≤
      nativeResourceScale M.data.d M.data.d 1 P.live.tags*(Cmax*R*W^2):=by
    apply HL.trans
    have Hdom:=mul_le_mul_of_nonneg_left (hdom a)
      (show 0 ≤ nativeResourceScale M.data.d M.data.d 1 P.live.tags*R*W^2 by
        exact mul_nonneg (mul_nonneg (actual_resource_raw_scale_pos _ M.data.hd M.data.hd).le hR) (sq_nonneg W))
    convert Hdom using 1 <;> dsimp only [W,R,as] <;> ring
  have H:=actual_general_resource_joint_LOW_normalized_price_le M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) hP hdepth ho hi (hs.trans_le hU) hU
    aSlot z hA M.data.hd le_rfl hprice Hpair HL'
  apply H.trans_eq
  ring

end OAI.SKFluctuations.Cavity
