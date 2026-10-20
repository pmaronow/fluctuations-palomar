module

public import ComparisonActualHighOnlySquareInitialFrozenResponse
public import ComparisonActualHighOnlyPullbackFourProducers
public import ComparisonActualHighOnlyCavityConsumerPrimitives
public import ComparisonActualHighOnlyComparableBandStarBond
public import ComparisonActualHighOnlySquareConsumerActualSharpFourTerminalAlong
public import ComparisonActualHighOnlyTargetRefinement

@[expose] public section
noncomputable section
set_option autoImplicit false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set Filter LaplaceWindowFormalization ActualHighOnlyOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

private theorem target_gap_residual_triangle
    {S G a L R T C D x e t r A : ℝ} (_hx : 0 ≤ x) (_hr : 0 ≤ r)
    (Hm : |S-G-a*L-T| ≤ e*x^3) (HT : |T| ≤ C*x^2*D+t*x^3)
    (HR : |L-R| ≤ r*x^3) (Ha : |a| ≤ A) :
    |S-G-a*R| ≤ C*x^2*D+(e+t+A*r)*x^3 := by
  have Hprod : |a*(L-R)| ≤ A*(r*x^3) := by
    rw [abs_mul]
    exact mul_le_mul Ha HR (abs_nonneg _) (le_trans (abs_nonneg _) Ha)
  rw [show S-G-a*R=(S-G-a*L-T)+T+a*(L-R) by ring]
  have H:=((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    (add_le_add (add_le_add Hm HT) Hprod)
  exact H.trans_eq (by ring)

def ActualContinuumTargetResidualModulusAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock Temp : ℝ} {dim : ℕ→ℕ}
    (hTemp : 0 < Temp) (depth : ℕ) (Ccut Couter c C : ℝ) (eta : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W x : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn in atTop,∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ Temp,
    ∀(Lnet : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (w n).star∈us → (∀u∈uniformMasses Lnet,u∈us) →
      ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      ∀u∈us,let i:=retainedMassPrefixIndex u.val as
      ∀(U V : ℕ) (hi : i ≤ star) (_hiU : i < U) (_hUV : U ≤ V)
        (hs : star < V) (hV : V ≤ as.length),
      2*c*x n ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*x n →
      partitionPoint 0 as V ≤ Couter*W n →
      let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
      let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0 (hi.trans (hs.le.trans hV))
      |orderedPathS (dim n+1) (M n).bf (M n).hf u.val-
        scalarCovarianceResponse hTemp ((M n).inheritedScalarMassProfile hTemp htotal)
          (actualMixedClock (dim n+1) (M n).bf (M n).hf u.val)-
        2*((M n).bf u.val:ℝ)*chi*
          nativeActualMinimumFourResidualSum_high_only (M n) hs hV (W n) depth [st]| ≤
        C*(x n)^2*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+
          1/(dim n+1:ℕ))+eta n*(x n)^3

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization ActualHighOnlyOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false

def ActualInitialFullResidualOnRetainedTargetsAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} {dim : ℕ→ℕ}
    (depth : ℕ) (Atarget Cr : ℝ) (er : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop:=
  ∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
    (∀v∈us,v.val ≤ 1) → (∀v∈uniformMasses Lnet,v∈us) → ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us →
    (∀j ≤ nativeDyadicCutDepth (high n).val,nativeDyadicMassCut (high n).val (high n).property j∈us) →
  ∀ᶠjGrid in atTop,
    let as:=finiteCutMasses us jGrid
    let star:=retainedMassPrefixIndex (w n).star.val as
    let V:=retainedMassPrefixIndex (high n).val as
    ∀(i : ℕ) (hi : i < star) (hs : star<V) (hV : V ≤ as.length),
      partitionPoint 0 as i ≤ Atarget*(M n).xs →
    let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0 (hi.le.trans (hs.le.trans hV))
    |nativeActualMinimumFourResidualSum_high_only (M n) hs hV (W n) depth [st]| ≤
      Cr*(M n).xs^2*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))+
        er n*(M n).xs^3

def ActualOriginalTargetScalarGapModulusAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock Temp : ℝ} {dim : ℕ→ℕ}
    (hTemp : 0 < Temp) (Atarget C : ℝ) (rate : ℕ→ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (w : ℕ→ActualSlowWindowChoice) : Prop:=
  ∀ᶠn in atTop,∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ Temp,
    ∀u : PositiveMass,u.val ≤ Atarget*(M n).xs → u.val < (w n).star.val →
    |orderedPathS (dim n+1) (M n).bf (M n).hf u.val-
      scalarCovarianceResponse hTemp ((M n).inheritedScalarMassProfile hTemp htotal)
        (actualMixedClock (dim n+1) (M n).bf (M n).hf u.val)| ≤
      C*(M n).xs^2*(Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u.val-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u.val)^2)+1/(dim n+1:ℕ))+
        rate n*(M n).xs^3

theorem actual_original_target_gap_from_full_residual_along_high_only
    {m delta cl cu Az C0 Ct D Bclock Temp Cf cFirst cK A Rmacro Cx c Atarget Ctgt Cr : ℝ}
    {dim : ℕ→ℕ} (hTemp : 0 < Temp) (depth : ℕ) (Cinner : ℝ)
    (hc : 0 < c) (hCx : 2*c ≤ Cx) (hAtarget : Atarget < 2*c) (hCinner : 2*c ≤ Cinner)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry_high_only (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A Rmacro Cx)
    (Hsource : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (et er : ℕ→ℝ) (Ht : Tendsto et atTop (𝓝 0)) (Hr : Tendsto er atTop (𝓝 0))
    (Htarget : ActualContinuumTargetResidualModulusAlong_high_only hTemp depth Cinner A c Ctgt et M W
      (fun n=>(M n).xs) w)
    (Hfull : ActualInitialFullResidualOnRetainedTargetsAlong_high_only depth Atarget Cr er M W w high outer) :
    ∃rate : ℕ→ℝ,(∀n,0 ≤ rate n) ∧ Tendsto rate atTop (𝓝 0) ∧
      ActualOriginalTargetScalarGapModulusAlong_high_only hTemp Atarget (Ctgt+2*Temp*Cr) rate M w := by
  let rawRate:=fun n=>et n+2*Temp*er n
  let rate:=fun n=>|rawRate n|
  have Hrate : Tendsto rate atTop (𝓝 0):=by
    simpa only [rate,rawRate,mul_zero,add_zero,abs_zero] using (Ht.add (Hr.const_mul (2*Temp))).abs
  refine ⟨rate,fun n=>abs_nonneg _,Hrate,?_⟩
  filter_upwards [Hcuts,Hsource,Htarget,Hfull] with n hcuts hsource htarget hfull
  obtain ⟨htotal,htarget⟩:=htarget
  refine ⟨htotal,?_⟩
  intro u hu hustar
  obtain ⟨Lnet,hLnet⟩:=exists_nat_one_div_lt (M n).hxs
  have hmesh : ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs:=by
    simpa only [Nat.cast_add,Nat.cast_one,one_div] using hLnet.le
  obtain ⟨us,hus,huRet,hiRet,hstar,hhigh,houter,hnodes,hnet,_,Hread⟩:=
    hcuts.exists_original_target_common_net hc hCx hAtarget hu hustar Lnet [] (by simp)
  have Hfixed : ∀ᶠjGrid in atTop,
      |orderedPathS (dim n+1) (M n).bf (M n).hf u.val-
        scalarCovarianceResponse hTemp ((M n).inheritedScalarMassProfile hTemp htotal)
          (actualMixedClock (dim n+1) (M n).bf (M n).hf u.val)| ≤
      (Ctgt+2*Temp*Cr)*(M n).xs^2*
        (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf (finiteCutMasses us jGrid)
          (retainedMassPrefixIndex u.val (finiteCutMasses us jGrid))+1/(dim n+1:ℕ))+
          rate n*(M n).xs^3:=by
    filter_upwards [htarget Lnet us hus hstar hnet hmesh,
      hfull Lnet us hus hnet hmesh hstar hhigh houter hnodes] with jGrid htgrid hrgrid
    dsimp only at htgrid hrgrid ⊢
    let as:=finiteCutMasses us jGrid
    let i:=retainedMassPrefixIndex u.val as
    let star:=retainedMassPrefixIndex (w n).star.val as
    let U:=retainedMassPrefixIndex (2*c*(M n).xs) as
    let V:=retainedMassPrefixIndex (high n).val as
    have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
    have hread:=Hread jGrid
    have hU : U ≤ as.length:=hread.inner_le_coarse.trans hread.coarse_le_length
    have htgt:=htgrid u huRet U V hread.target_lt_star.le hread.target_lt_inner
      hread.inner_le_coarse hread.star_lt_coarse hread.coarse_le_length
      (by rw [hread.inner_mass])
      (by rw [hread.inner_mass];exact mul_le_mul_of_nonneg_right hCinner (M n).hxs.le)
      hread.coarse_scale
    have hr:=hrgrid i hread.target_lt_star hread.star_lt_coarse hread.coarse_le_length
      (by rw [hread.target_mass];exact hu)
    let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0
      (hread.target_lt_star.le.trans (hread.star_lt_coarse.le.trans hread.coarse_le_length))
    let residual:=nativeActualMinimumFourResidualSum_high_only (M n) hread.star_lt_coarse hread.coarse_le_length (W n) depth [st]
    have hchi:=actual_minimum_continuum_chi_mem_unit_on_any_grid_high_only (M n) as ho U
      ((Nat.zero_le i).trans_lt hread.target_lt_inner) hU
    have hb:((M n).bf u.val:ℝ) ≤ Temp:=(hsource u.val ⟨u.property.le,hus u huRet⟩).1
    have ha : |2*((M n).bf u.val:ℝ)*chi| ≤ 2*Temp:=by
      have HM:=mul_le_mul hb hchi.2 hchi.1 hTemp.le
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) (NNReal.coe_nonneg _)) hchi.1)]
      nlinarith only [HM]
    have Hprod : |2*((M n).bf u.val:ℝ)*chi*residual| ≤
        2*Temp*(Cr*(M n).xs^2*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+
          1/(dim n+1:ℕ))+er n*(M n).xs^3):=by
      rw [abs_mul]
      exact mul_le_mul ha hr (abs_nonneg _) (show 0 ≤ 2*Temp by positivity)
    have HH:=(abs_add_le
      (orderedPathS (dim n+1) (M n).bf (M n).hf u.val-
        scalarCovarianceResponse hTemp ((M n).inheritedScalarMassProfile hTemp htotal)
          (actualMixedClock (dim n+1) (M n).bf (M n).hf u.val)-2*((M n).bf u.val:ℝ)*chi*residual)
      (2*((M n).bf u.val:ℝ)*chi*residual)).trans
      (add_le_add htgt Hprod)
    have Hraw : |orderedPathS (dim n+1) (M n).bf (M n).hf u.val-
        scalarCovarianceResponse hTemp ((M n).inheritedScalarMassProfile hTemp htotal)
          (actualMixedClock (dim n+1) (M n).bf (M n).hf u.val)| ≤
      (Ctgt+2*Temp*Cr)*(M n).xs^2*
        (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))+
          rawRate n*(M n).xs^3:=by
      have HH' : |orderedPathS (dim n+1) (M n).bf (M n).hf u.val-
          scalarCovarianceResponse hTemp ((M n).inheritedScalarMassProfile hTemp htotal)
            (actualMixedClock (dim n+1) (M n).bf (M n).hf u.val)| ≤
          Ctgt*(M n).xs^2*
            (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))+
            et n*(M n).xs^3+2*Temp*
              (Cr*(M n).xs^2*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+
                1/(dim n+1:ℕ))+er n*(M n).xs^3) := by
        simpa only [sub_add_cancel] using HH
      dsimp only [rawRate]
      nlinarith only [HH']
    apply Hraw.trans
    dsimp only [rate,as,i]
    exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right (le_abs_self (rawRate n))
      (pow_nonneg (M n).hxs.le 3))
  have Hrad:=actual_original_retained_target_low_radius_with_site_tendsto_high_only (M n) us hus u huRet
  have Hright:=((Hrad.const_mul ((Ctgt+2*Temp*Cr)*(M n).xs^2)).add_const (rate n*(M n).xs^3))
  exact le_of_tendsto_of_tendsto tendsto_const_nhds Hright Hfixed

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set LaplaceWindowFormalization
open scoped NNReal
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_target_response_eq_initial_four_state_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (i star U : ℕ) (hi : i≤as.length) (W : ℝ) :
    nativeActualTargetLongitudinalResponse_high_only M as i U=
      nativeActualMinimumFourStateResponse_high_only M U W (nativeActualInitialState as i star 0 hi) := by
  rw [native_actual_target_response_original_readout_high_only M as ho i U]
  unfold nativeActualMinimumFourStateResponse_high_only nativeOriginalClockStateResponse nativeOriginalClockResourceResponse
  dsimp only [nativeActualInitialState,NativeResourceTerm.ofLive,nativeResourceSeed]
  simp only [pow_zero,one_mul]
  congr 1
  funext σ
  simp only [NativeResourceTerm.value,NativeResourceTerm.scalar,
    List.map_nil,List.prod_nil,one_mul,NativeResourceMark.cut,nativeGeneratedSeed,
    NativeGeneratedTest.value,NativeGeneratedTest.edges,nativeGeneratedEdgeProduct,
    List.map_nil,List.nil_append,List.map_singleton,List.prod_singleton]
  rw [splitIndex_symm,nativeFreshAtSlot_split,splitIndex_self,Nat.min_eq_left hi]
  rw [(nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i).restrict_at]
  rw [(nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i).spin_at]

theorem actual_target_response_eq_four_iteration_high_only
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (W : ℝ) (i star U : ℕ)
    (hi : i ≤ star) (hs : star<U) (hU : U≤as.length) (ho : MassOrdered 0 as)
    (hW : W≠0) (hstarK : 0<nativeContinuumMixedClock n M.bf M.hf as star) (depth : ℕ) :
    let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
    nativeActualTargetLongitudinalResponse_high_only M as i U=
      nativeActualMinimumFourResidualSum_high_only M hs hU W depth [st]+
      nativeActualOriginalContinuumCenteredFourGFrontier_high_only M as W i star U hi hs hU depth-
      nativeActualMinimumFourStateResponse_high_only M U W st.freeze := by
  dsimp only
  have H:=actual_minimum_initial_four_resource_finite_iteration_high_only M as W i star U hi hs hU ho hW hstarK depth
  dsimp only at H
  rw [←actual_target_response_eq_initial_four_state_high_only M as ho i star U (hi.trans (hs.le.trans hU)) W] at H
  linarith only [H]

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set Filter LaplaceWindowFormalization ActualHighOnlyOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false

def ActualTargetInitialResidualApproxAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} {dim : ℕ→ℕ}
    (depth : ℕ) (saving Cmass : ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val≤1) → (w n).star∈us → (∀u∈uniformMasses Lnet,u∈us) →
    ((Lnet+1:ℕ):ℝ)⁻¹≤(M n).xs →∀ᶠjGrid : ℕ in atTop,
    let as:=finiteCutMasses us jGrid
    let star:=retainedMassPrefixIndex (w n).star.val as
    ∀(U i : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U≤as.length),
    ∀x : ℝ,(M n).xs≤x → x≤W n → partitionPoint 0 as i≤Cmass*x →
      let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      |nativeActualTargetLongitudinalResponse_high_only (M n) as i U-
        nativeActualMinimumFourResidualSum_high_only (M n) hs hU (W n) depth [st]|≤
        3*((dim n+1:ℕ):ℝ)^(-saving)*x^3

theorem exists_actual_same_star_initial_residual_approx_along_high_only
    {m delta cl cu Az C0 Ct D Bclock Temp Tstar L Cs gamma : ℝ}
    (hm : 0 < m) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0)
    (hTemp : 0≤Temp) (hTstar : 0 < Tstar) (hgamma : 0 < gamma) (Cmass : ℝ)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) (hWlim : Tendsto W atTop (𝓝 0))
    (htotal : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤Temp)
    (hroot : ∀ᶠn in atTop,(M n).h 0=0)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) Tstar L Cs (w n))
    (Hp : ∀degree : ℕ,0<degree →∃A : ℝ,1≤A ∧
      ActualSquareResourcePairBudgetOnEveryFinalNetAlong_high_only degree A gamma Cmass M W w) :
    ∃threshold : ℕ,0<threshold ∧∃saving : ℝ,0<saving ∧∀depth : ℕ,threshold≤depth →
      ActualTargetInitialResidualApproxAlong_high_only depth saving Cmass M W w := by
  let c:=starMassBandConstant cu Az/cu
  let cK:=3*Tstar*c/8
  have hc : 0<c:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
  have hcK : 0<cK:=by dsimp only [cK];positivity
  have Hclock : ∀ᶠn in atTop,cK*W n≤actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val := by
    filter_upwards [hw] with n hn
    obtain ⟨p,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hlo,_,_⟩:=hn.1
    exact hlo
  obtain ⟨threshold,hthreshold,saving,hsaving,Hterminal⟩:=
    exists_actual_original_continuum_natural_centered_four_G_terminal_decay_of_pair_budgets_of_eventual_total_clock_along_high_only
      hm hC0 hTemp hgamma hcK Cmass dim hdim M W hxs hWlim htotal w Hclock Hp
  have Hfrozen:=hdim.eventually (eventually_actual_inherited_initial_frozen_response_cubic_high_only
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D)
    Bclock Temp hTemp hm hC0)
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨threshold,hthreshold,min m saving,lt_min hm hsaving,?_⟩
  intro depth hdepth
  filter_upwards [Hterminal depth hdepth,Hfrozen,htotal,hroot,HW,Hclock] with n hnT hnF ht hr hw1 hnK
  intro Lnet us hus hstar hret hmesh
  filter_upwards [hnT Lnet us hus hstar hret hmesh,
    hnF (M n) ht hr ((hxs n).trans hw1) us hus] with jGrid hjT hjF
  dsimp only at hjT hjF ⊢
  intro U i hi hs hU x hxsx hxW hmass
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0 (hi.trans (hs.le.trans hU))
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hW:=(M n).hxs.trans_le (hxs n)
  have hx:=(M n).hxs.trans_le hxsx
  have hK : 0<nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star := by
    rw [native_continuum_mixed_clock_retained_eq (dim n) (M n).bf (M n).hf as ho
      (w n).star (finiteCutMasses_nodes us jGrid hstar)]
    exact (mul_pos hcK hW).trans_le hnK
  have HE:=actual_target_response_eq_four_iteration_high_only (M n) as (W n) i star U hi hs hU ho hW.ne' hK depth
  dsimp only at HE
  have HF:=hjF i star U (hi.trans (hs.le.trans hU)) (W n) x hxsx
  have HT:=hjT U i hi hs hU x hxsx hxW hmass
  have hN : (1:ℝ)≤(dim n+1:ℕ):=by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (dim n))
  have H1:=Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg (min_le_left m saving))
  have H2:=Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg (min_le_right m saving))
  have Hscale : (M n).xs^2*x≤x^3 := by
    nlinarith only [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (M n).hxs.le hxsx 2) hx.le]
  have HF' := HF.trans (mul_le_mul_of_nonneg_right H1 (pow_nonneg hx.le 3))
  have HT' : |nativeActualOriginalContinuumCenteredFourGFrontier_high_only (M n) as (W n) i star U hi hs hU depth|≤
      2*((dim n+1:ℕ):ℝ)^(-min m saving)*x^3 := by
    apply HT.trans
    have H:=mul_le_mul H2 Hscale (by positivity : (0:ℝ)≤(M n).xs^2*x)
      (Real.rpow_nonneg (by positivity) (-min m saving))
    have H':=mul_le_mul_of_nonneg_left H (by norm_num : (0:ℝ)≤2)
    convert H' using 1 <;> ring
  rw [HE]
  rw [show nativeActualMinimumFourResidualSum_high_only (M n) hs hU (W n) depth [st]+
      nativeActualOriginalContinuumCenteredFourGFrontier_high_only (M n) as (W n) i star U hi hs hU depth-
      nativeActualMinimumFourStateResponse_high_only (M n) U (W n) st.freeze-
      nativeActualMinimumFourResidualSum_high_only (M n) hs hU (W n) depth [st]=
      nativeActualOriginalContinuumCenteredFourGFrontier_high_only (M n) as (W n) i star U hi hs hU depth-
      nativeActualMinimumFourStateResponse_high_only (M n) U (W n) st.freeze by ring]
  have H:=(abs_sub _ _).trans (add_le_add HT' HF')
  exact H.trans_eq (by ring)

end OAI.SKFluctuations.Cavity
