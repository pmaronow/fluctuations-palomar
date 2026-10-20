module

public import ComparisonActualHighWallCenteredTransientLowPart
public import ComparisonActualHighWallRawResourcePairBudget
public import ComparisonActualGeneralResourceTransientLowReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_resource_transient_LOW_from_minimum
    (degree rBound : ℕ) (Bclock Cmass Ccut : ℝ) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d → M.data.d ≤ 1 →
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
        ∀(a z : T.Slot) (part : NativeTransientLowErrorPart) (l t : ℝ),
        l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K)
          (nativeTransientLowErrorPartDirection n U i star b h K part)
        |(M.data.d⁻¹)^k*actualGeneralResourceTransientLowPart M.bf M.hf U P a z part l t| ≤
          |P.coefficient| *nativeResourceScale M.data.d M.data.d 1 seed*
            (C*M.data.d^2*(T.forkCost R+edgeBudget 0 as R)) := by
  classical
  have HP (a : Fin (degree+1)):=eventually_actual_high_wall_canonical_centered_transient_LOW_part_budget
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
  intro M hwork hW1 L us hus hret hmesh
  have Hgrids a:=hn a M hwork hW1 L us hus hret hmesh
  filter_upwards [Filter.eventually_all.mpr Hgrids,hnA M hwork L us hus hret hmesh] with jGrid hj hjA
  dsimp only at hj hjA ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth hmi hms hcut aSlot z part l t hl ht
  let W:=M.data.d
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K)
    (nativeTransientLowErrorPartDirection n U i star b h K part)
  let Cost:=T.forkCost R+edgeBudget 0 as R
  let G:=nativeActualResourceCanonicalShape P.live hi (hs.trans_le hU)
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hCost : 0 ≤ Cost:=add_nonneg
    (T.forkCost_nonneg (fun j=>nativeWholeLawErrorRadius_nonneg _ _ _ _ j))
    (edgeBudget_nonneg ho (fun j=>nativeWholeLawErrorRadius_nonneg _ _ _ _ j))
  have hprice : 0 ≤ Cmax*W^2*Cost:=by positivity
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
  have HL:=hj a i star U part T l t hU hl ht hT G (fun _=>.centered) hcut Hmass aSlot z
  have Hscale : nativeResourceScale M.data.d M.data.d 1 P.live.tags=M.data.d^P.live.factors.length:=by
    rw [←native_actual_resource_live_scale_eq_annotations,←source_factor_scale_product]
    simp [sourceFactorScale]
  dsimp only [a] at HL
  rw [←Hscale] at HL
  have HL' : |nativeTransientCenteredLowErrorPart n q i star U b h K T
      (G.canonicalPhysicalSource M.bf M.hf (fun _=>NativeSourceFactorForm.centered)).restProduct
      (sitePair T aSlot z) 0 part l t| ≤
      nativeResourceScale M.data.d M.data.d 1 P.live.tags*(Cmax*W^2*Cost):=by
    apply HL.trans
    have Hdom:=mul_le_mul_of_nonneg_left (hdom a)
      (show 0 ≤ nativeResourceScale M.data.d M.data.d 1 P.live.tags*W^2*Cost by
        exact mul_nonneg (mul_nonneg (actual_resource_raw_scale_pos _ M.data.hd M.data.hd).le
          (sq_nonneg W)) hCost)
    change C a*W^2*nativeResourceScale M.data.d M.data.d 1 P.live.tags*Cost ≤
      nativeResourceScale M.data.d M.data.d 1 P.live.tags*(Cmax*W^2*Cost)
    nlinarith only [Hdom]
  have H:=actual_general_resource_transient_LOW_normalized_price_le M.bf M.hf
    hP hdepth ho hi (hs.trans_le hU) aSlot z part l t hA M.data.hd le_rfl hprice Hpair HL'
  apply H.trans_eq
  ring

end OAI.SKFluctuations.Cavity
