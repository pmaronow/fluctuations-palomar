module

public import ComparisonSignedCavityInheritedCanonicalJointLowRestorationPrice
public import ComparisonSignedCavityActualResourceJointLowRestorationReadout
public import ComparisonSignedCavityInheritedRawResourcePairBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_minimum_inherited_resource_joint_LOW_restoration_from_minimum
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound → seed.length+k ≤ degree →
        ∀W : ℝ,M.xs ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*M.xs → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        ∀a z : T.Slot,T.splitIndex a z<U →
        let R:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
          (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex a z)+1/(n+1:ℕ))
        |(W⁻¹)^k*nativeActualResourceJointLowRestoration M U P a z| ≤
          |P.coefficient| *nativeResourceScale M.xs W 1 seed*(C*R*W^2) := by
  classical
  have HP (a : Fin (degree+1)):=eventually_actual_minimum_inherited_canonical_joint_LOW_restoration_price
    (D:=D) a.val rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  choose C hC HC using HP
  let Cmax:=1+∑a : Fin (degree+1),C a
  have hsum : 0 ≤ ∑a : Fin (degree+1),C a:=Finset.sum_nonneg (fun a _=>(hC a).le)
  have hCmax : 0 < Cmax:=by dsimp only [Cmax];linarith
  have hdom a : C a ≤ Cmax:=by
    have H:=Finset.single_le_sum (fun a _=>(hC a).le) (Finset.mem_univ a)
    dsimp only [Cmax]
    linarith
  obtain ⟨A,hA,HA⟩:=eventually_actual_minimum_inherited_raw_resource_pair_budget
    (D:=D) (degree+1) (by omega) Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  refine ⟨Cmax*A^degree,by positivity,?_⟩
  filter_upwards [Filter.eventually_all.mpr HC,HA] with n hn hnA
  intro M hsource hxs L us hus hret hmesh
  have Hgrids a:=hn a M hsource hxs L us hus hret hmesh
  filter_upwards [Filter.eventually_all.mpr Hgrids,hnA M hsource hxs L us hus hret hmesh] with jGrid hj hjA
  dsimp only at hj hjA ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth W hxW hW1 hmi hms hcut aSlot z haz
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as (T.splitIndex aSlot z)+1/(n+1:ℕ))
  let G:=nativeActualResourceCanonicalShape P.live hi (hs.trans_le hU)
  let I:=nativeActualResourceInitialFactors P.live
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hR : 0 ≤ R:=mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp) (by
    dsimp only [nativeOriginalCutLowErrorRadius]
    positivity)
  have hprice : 0 ≤ Cmax*R*W^2:=by positivity
  have Hdegree : P.resources.length ≤ degree+1:=by rw [hP.total_factor_depth];omega
  have Hpair:=hjA U i star T P Hdegree (hi.trans (hs.le.trans hU)) (hs.le.trans hU)
    M.xs W le_rfl hxW hmi hms 1 1 (by norm_num) (by norm_num)
  have Hlive : P.live.factors.length ≤ degree:=by
    have Hlen:=hP.total_factor_depth
    simp only [NativeResourceTerm.resources,List.length_append,NativeResourceMonomial.tags,List.length_map] at Hlen
    omega
  let a : Fin (degree+1):=⟨P.live.factors.length,by omega⟩
  have HL:=hj a U T hU hT G (fun _=>.centered) I W hxW hcut
    (native_actual_resource_canonical_source_mass P.live hi (hs.trans_le hU) Cmass M.xs W hmi hms) aSlot z haz
  rw [native_actual_resource_live_scale_eq_annotations] at HL
  have Hcenter : nativePhysicalResourceCenter n M.bf M.hf as=
      (fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)):=by
    funext j
    exact (native_ordered_source_center_eq_completed n M.bf M.hf
      M.inherited_bf_monotone M.inherited_hf_monotone (partitionPoint_mem as ho j)).symm
  rw [←Hcenter] at HL
  have HL' : |nativeCenteredLowGammaLowRestoration n q U b h K (nativePhysicalResourceCenter n M.bf M.hf as) T
      (G.canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)).restProduct aSlot z| ≤
      nativeResourceScale M.xs W 1 P.live.tags*(Cmax*R*W^2):=by
    apply HL.trans
    have Hdom:=mul_le_mul_of_nonneg_left (hdom a)
      (show 0 ≤ nativeResourceScale M.xs W 1 P.live.tags*R*W^2 by
        exact mul_nonneg (mul_nonneg (actual_resource_raw_scale_pos _ M.hxs (M.hxs.trans_le hxW)).le hR) (sq_nonneg W))
    convert Hdom using 1 <;> ring
  have H:=actual_resource_joint_LOW_normalized_price_le M hP hdepth ho hi (hs.trans_le hU) hU
    aSlot z hA le_rfl hxW hprice Hpair HL'
  apply H.trans_eq
  ring

end OAI.SKFluctuations.Cavity
