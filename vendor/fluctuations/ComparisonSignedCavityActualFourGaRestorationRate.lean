module

public import ComparisonSignedCavityActualResourceGRestorationFromMinimum
public import ComparisonSignedCavityActualFourGaRestorationProfile
public import ComparisonNativeActualInheritedHighTailPowers

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 28000000

theorem eventually_actual_shell_history_resource_G_restoration_forest_rate
    (seedBound k₀ r₀ depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (Tbase epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
        NativeActualSmallSourceClocks M Temp Cf →
        (∀u,M.b u=historyMatrixClock Tbase epsilon shell ts u) →
        (∀u,M.h u=historyFieldClock ts u) →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀(i star U : ℕ) (seed : List NativeResourceMark)
          (st : NativeActualResourceState (Spin n×Bool) as i star),
        seed.length ≤ seedBound → st.generation=k₀ → st.tree.leaves ≤ r₀ →
        NativeActualResourceGenerated i star U seed st.generation st.tree st.term →
        i ≤ star → ∀(hs : star < U) (hU : U ≤ as.length),
        2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        partitionPoint 0 as star ≤ Cmass*W →
        cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star →
        (∀f : ℕ→ℝ,(∀j,j < U → f j=0) → st.tree.forkCost f=0) →
        ∀x : ℝ,M.xs ≤ x → x ≤ W → partitionPoint 0 as i ≤ Cmass*x →
        ((nativeActualMinimumFourCenteredForest M hs hU W depth [st]).map
          (fun Q=>|nativeActualOriginalFourGaRestorationError M U W Q|)).sum ≤
          |st.term.coefficient| *C*M.context.N^(-(actualMassSavingExponent m delta/256))*
            M.xs^2*nativeResourceScale x W 1 seed := by
  let eta:=actualMassSavingExponent m delta
  have heta : 0 < eta:=actualMassSavingExponent_pos hm hdelta
  obtain ⟨p,dOrder,hp,hdOrder,hOrder,htheta1,htheta2,hdeficit⟩:=exists_native_high_profile_holder_orders heta
  let degree:=seedBound+k₀+depth
  obtain ⟨Csrc,hCsrc,Hsource⟩:=eventually_actual_minimum_inherited_resource_G_restoration_from_minimum
    (D:=D) degree dOrder (r₀+6*depth+1) hdOrder p hp hOrder Bclock Temp Cf Cmass Ccut
    hTemp hCf hCmass hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers
    (D:=D) (Cs:=Cs) Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  let Cw:=(Temp+2*Cf)/(Real.exp (-4*(Temp+2*Cf))*cK)
  have hCw : 0 ≤ Cw:=by dsimp only [Cw];positivity
  let Vcost:=nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches Cw 3 r₀ depth
  have hVcost : 0 ≤ Vcost:=nativeActualWeightedProfileFrontierCost_nonneg _ hCw _ _ _
  let C:=2*(2*Temp/cK)*Csrc*Vcost+1
  have hC : 0 < C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [Hsource,Htail] with n hnSource hnTail
  intro M Tbase epsilon shell ts hsource hb hh hsmall hW1 L us hus hret hmesh
  have hxs1 : M.xs ≤ 1:=M.canonical_direct_test_band_ge_scale.trans hW1
  filter_upwards [hnSource M hsource hxs1 L us hus hret hmesh,
    hnTail M Tbase epsilon shell ts hb hh hsmall hW1 us hus] with jGrid hgridSource hgridTail
  dsimp only at hgridSource hgridTail ⊢
  intro i star U seed st hseed hgen hleaf hP hi hs hU hcutlo hcutup hmassstar hstarK hseedFork x hx hxW hmi
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin n×Bool) as i star) tag=>
    nativeOriginalClockParentWeight W U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let rows:=nativeActualMinimumFourCenteredForest M hs hU W depth [st]
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  let f2:=fun j=>((R j)^(2/p))^2
  let seedScale:=nativeResourceScale x W 1 seed
  let B:=(2*Temp/cK)*Csrc*seedScale
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0 < W:=M.canonical_direct_test_band_pos
  have hx0 : 0 < x:=M.hxs.trans_le hx
  have hscale : 0 ≤ seedScale:=(actual_resource_raw_scale_pos seed hx0 hW).le
  have hB : 0 ≤ B:=by dsimp only [B];positivity
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hf2 j : 0 ≤ f2 j:=sq_nonneg _
  have hRlo j (hj : j < U) : R j=0:=by simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hf2lo j (hj : j < U) : f2 j=0:=by
    dsimp only [f2]
    rw [hRlo j hj,Real.zero_rpow (by positivity : 2/p ≠ 0)]
    ring
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourGaRestorationError M U W Q| ≤
      |Q.term.coefficient| *B*(Q.tree.forkCost f2+edgeBudget 0 as f2+
        W*(Q.tree.forkCost R+edgeBudget 0 as R)) := by
    have Hvalid:=nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth [st]
      (by intro P hP';obtain rfl:=List.mem_singleton.mp hP';exact hP) Q hQ
    have Hgen:=nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth [st]
      k₀ (by intro P hP';obtain rfl:=List.mem_singleton.mp hP';exact hgen) Q hQ
    have Hleaves:=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth [st]
      r₀ (by intro P hP';obtain rfl:=List.mem_singleton.mp hP';exact hleaf) Q hQ
    have Hdegree : seed.length+Q.generation ≤ degree:=by dsimp only [degree];omega
    let g:=nativeFreshAtSlot Q.tree 0 Q.term.live.test.target star
    have hg : g.tree.leaves ≤ r₀+6*depth+1:=by
      have HH:=Q.tree.markedAttach_leaves 0 g (nativeFreshAtSlot_mem Q.tree 0 Q.term.live.test.target star)
      omega
    let cost:=Q.tree.forkCost f2+edgeBudget 0 as f2+W*(Q.tree.forkCost R+edgeBudget 0 as R)
    have hcost : 0 ≤ cost:=by
      have H2:=add_nonneg (Q.tree.forkCost_nonneg hf2) (edgeBudget_nonneg ho hf2)
      have H1:=add_nonneg (Q.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
      dsimp only [cost]
      positivity
    have H0:=hgridSource i star U Q.generation seed Q.tree Q.term Hvalid hi hs hU (by omega)
      Hdegree x W hx hxW hmi hmassstar hcutup
    have H1:=hgridSource i star U Q.generation seed g.tree (Q.term.retarget 0) Hvalid.retarget hi hs hU hg
      Hdegree x W hx hxW hmi hmassstar hcutup
    have Hf:=nativeFreshAtSlot_high_forkCost Q.tree 0 Q.term.live.test.target hs f2 hf2lo
    have HR:=nativeFreshAtSlot_high_forkCost Q.tree 0 Q.term.live.test.target hs R hRlo
    change |(W⁻¹)^Q.generation*nativeActualResourceGaRestoration M U Q.term| ≤
      |Q.term.coefficient| *seedScale*(Csrc*W*cost) at H0
    change |(W⁻¹)^Q.generation*nativeActualResourceGaRestoration M U (Q.term.retarget 0)| ≤
      |Q.term.coefficient| *seedScale*(Csrc*W*(g.tree.forkCost f2+edgeBudget 0 as f2+
        W*(g.tree.forkCost R+edgeBudget 0 as R))) at H1
    rw [show g.tree.forkCost f2=Q.tree.forkCost f2 from Hf,
      show g.tree.forkCost R=Q.tree.forkCost R from HR] at H1
    change |(W⁻¹)^Q.generation*nativeActualResourceGaRestoration M U (Q.term.retarget 0)| ≤
      |Q.term.coefficient| *seedScale*(Csrc*W*cost) at H1
    have Hbound:=actual_minimum_four_Ga_restoration_error_abs_le M Q hW hcK
      (B:=Csrc*seedScale*cost) (by positivity) hTemp
      (hsource _ (partitionPoint_mem as ho star)).1 hstarK
      (by apply H0.trans_eq;ring)
      (by apply H1.trans_eq;ring)
    apply Hbound.trans_eq
    dsimp only [B,cost]
    ring
  have Hsum:=actual_minimum_four_Ga_restoration_forest_profile_le M ho hs hU hTemp hCf hsource hxs1
    hW hcK hB hstarK depth st hleaf f2 R hf2 hR hf2lo hRlo Hrow
  rw [hseedFork f2 hf2lo,hseedFork R hRlo,zero_add,zero_add] at Hsum
  have Hpow : f2=(fun j=>(R j)^(4/p)):=by
    funext j
    dsimp only [f2]
    rw [wholeLaw_rpow_square_eq (hR j) (2/p)]
    congr 1
    ring
  have Hrate : edgeBudget 0 as f2+W*edgeBudget 0 as R ≤ M.context.N^(-eta/256)*M.xs^2:=by
    have HReq : R=nativeOriginalHighTailEnvelope n U M.bf M.hf as
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp):=by funext j;rfl
    rw [Hpow,HReq]
    simpa only [W,as,eta,neg_div] using hgridTail U hU hcutlo (4/p) htheta1 htheta2.le hdeficit
  have HtailBound:=mul_le_mul_of_nonneg_left Hrate
    (show 0 ≤ 2*|st.term.coefficient| *B*Vcost by positivity)
  have Hmajor:=mul_le_mul_of_nonneg_left
    (show 2*(2*Temp/cK)*Csrc*Vcost ≤ C by dsimp only [C];linarith)
    (show 0 ≤ |st.term.coefficient| *M.context.N^(-eta/256)*M.xs^2*seedScale by positivity)
  have Hfinal : 2*|st.term.coefficient| *B*Vcost*(M.context.N^(-eta/256)*M.xs^2) ≤
      |st.term.coefficient| *C*M.context.N^(-eta/256)*M.xs^2*seedScale := by
    convert Hmajor using 1 <;> (try dsimp only [B]) <;> ring
  apply Hsum.trans
  simpa only [eta,seedScale,W,neg_div] using HtailBound.trans Hfinal

end OAI.SKFluctuations.Cavity
