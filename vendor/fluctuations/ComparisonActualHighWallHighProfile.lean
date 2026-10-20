module

public import ComparisonActualHighWallFourSource
public import ComparisonSignedCavityActualHighErrorProfile
public import ComparisonSignedCavityActualFourForestHighProfile
public import ComparisonNativeHighTailL1Transfer
public import ComparisonNativeHighTailComparisonEnvelope

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization.ActualHighWallData
open Set MeasureTheory ProbabilityTheory Filter Hierarchy Hierarchy.ClockTree Cavity
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 32000000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {delta : ℝ} (a : ActualHighWallData (n+1) delta)

def highComparisonConstant : ℝ := actualLowErrorComparisonConstant (2*a.T) a.T

def highErrorEnvelope (alpha : a.Profile) (as : List PositiveMass) (U : ℕ) : ℕ→ℝ :=
  nativeOriginalHighErrorEnvelope n U (a.bf alpha) (a.hf alpha) as (2*a.T) a.T

def thermal (alpha : a.Profile) (u : ℝ) : ℝ :=
  orderedPathB (n+1) (a.bf alpha) (a.hf alpha) u-
    (orderedPathS (n+1) (a.bf alpha) (a.hf alpha) u)^2

theorem highComparisonConstant_nonneg : 0≤a.highComparisonConstant :=
  actualLowErrorComparisonConstant_nonneg _ a.hTpos.le

theorem thermal_nonneg (alpha : a.Profile) {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    0≤a.thermal alpha u := by
  by_cases hu0 : u=0
  · subst u
    simp [thermal,orderedPathB,orderedPathS,orderedPathPair_zero]
  · exact sub_nonneg.mpr (orderedPath_SK_bounds (n+1) (by omega) (a.bf alpha) (a.hf alpha)
      (a.bf_monotone alpha) (a.hf_monotone alpha)
      ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),hu.2⟩).2.2.1

theorem current_high_error_radius_le_original
    (alpha : a.Profile) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (U : ℕ) {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (j : ℕ) (hj : j≤as.length) :
    let b:=fun k=>(a.bf alpha (partitionPoint 0 as k):ℝ)
    let h:=fun k=>(a.hf alpha (partitionPoint 0 as k):ℝ)
    let K:=nativeContinuumMixedClock n (a.bf alpha) (a.hf alpha) as
    nativeWholeLawErrorRadius n as
      (cutFullVariance n (fun k=>Sum.elim (fun _=>b k) (fun _=>h k)) U l t b h K)
      (cutTSlope n U 0 b h K) j≤a.highErrorEnvelope alpha as U j := by
  have hbond (k : ℕ) (_hk : k≤as.length) : (a.bf alpha (partitionPoint 0 as k):ℝ)≤a.T := by
    have HH:=a.total_clock_le alpha _ (partitionPoint_mem as ho k)
    linarith [(a.hf alpha (partitionPoint 0 as k)).coe_nonneg]
  have hclock : (a.hf alpha (partitionPoint 0 as as.length):ℝ)+
      (a.bf alpha (partitionPoint 0 as as.length):ℝ)*
        orderedPathS (n+1) (a.bf alpha) (a.hf alpha) (partitionPoint 0 as as.length)+
      (a.bf alpha (partitionPoint 0 as as.length):ℝ)+
      (a.hf alpha (partitionPoint 0 as as.length):ℝ)≤2*a.T := by
    have HT:=a.total_clock_le alpha _ (partitionPoint_mem as ho as.length)
    have HS:=(physicalOrderedPathS_mem_unit n (a.bf alpha) (a.hf alpha)
      (a.bf_monotone alpha) (a.hf_monotone alpha) (partitionPoint_mem as ho as.length)).2
    have HM:=mul_le_mul_of_nonneg_left HS (a.bf alpha (partitionPoint 0 as as.length)).coe_nonneg
    linarith
  exact native_actual_high_error_radius_le_original n U (a.bf alpha) (a.hf alpha)
    (a.bf_monotone alpha) (a.hf_monotone alpha) ho hl ht a.hTpos.le hbond hclock j hj

theorem current_high_profile_le_original
    (alpha : a.Profile) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (U : ℕ) {l t exponent : ℝ}
    (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) (he : 0≤exponent) :
    let b:=fun k=>(a.bf alpha (partitionPoint 0 as k):ℝ)
    let h:=fun k=>(a.hf alpha (partitionPoint 0 as k):ℝ)
    let K:=nativeContinuumMixedClock n (a.bf alpha) (a.hf alpha) as
    let R:=a.highErrorEnvelope alpha as U
    nativeWholeLawProfileCost n
      (cutFullVariance n (fun k=>Sum.elim (fun _=>b k) (fun _=>h k)) U l t b h K)
      (cutTSlope n U 0 b h K) T exponent≤
        T.forkCost (fun j=>(R j)^exponent)+edgeBudget 0 as (fun j=>(R j)^exponent) := by
  dsimp only
  rw [nativeWholeLawProfileCost_eq_budget n ho]
  have H (j : ℕ) (hj : j≤as.length):=Real.rpow_le_rpow
    (nativeWholeLawErrorRadius_nonneg n as _ _ j)
    (a.current_high_error_radius_le_original alpha ho U hl ht j hj) he
  exact add_le_add (native_forkCost_mono_on_clock T H) (actual_low_edgeBudget_mono ho H)

theorem four_G_weight_bound
    (alpha : a.Profile) {as : List PositiveMass} {i star U : ℕ}
    (ho : MassOrdered 0 as) (hs : star<U) (hU : U≤as.length)
    {W cK : ℝ} (hW : 0<W) (hcK : 0<cK)
    (hstarK : cK*W≤nativeContinuumMixedClock n (a.bf alpha) (a.hf alpha) as star)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (tag : ℕ) :
    let K:=nativeContinuumMixedClock n (a.bf alpha) (a.hf alpha) as
    let b:=fun j=>(a.bf alpha (partitionPoint 0 as j):ℝ)
    |nativeOriginalClockParentWeight W U K st (nativeOriginalClockFourGBranchBeta U K b st tag)|≤
      a.T/(Real.exp (-4*a.T)*cK) := by
  let K:=nativeContinuumMixedClock n (a.bf alpha) (a.hf alpha) as
  let b:=fun j=>(a.bf alpha (partitionPoint 0 as j):ℝ)
  have hK:=native_continuum_mixed_clock_nonneg n (a.bf alpha) (a.hf alpha)
    (a.bf_monotone alpha) (a.hf_monotone alpha) as ho
  have hKm:=native_continuum_mixed_clock_monotone n (a.bf alpha) (a.hf alpha)
    (a.bf_monotone alpha) (a.hf_monotone alpha) as ho
  have hterminal : K as.length≤a.T:=
    (native_continuum_mixed_clock_terminal_le n (a.bf alpha) (a.hf alpha)
      (a.bf_monotone alpha) (a.hf_monotone alpha) as ho).trans (a.total_clock_le alpha 1 (by norm_num))
  have hb : b star≤a.T := by
    have HH:=a.total_clock_le alpha _ (partitionPoint_mem as ho star)
    linarith [(a.hf alpha (partitionPoint 0 as star)).coe_nonneg]
  apply nativeOriginalClockParentWeight_four_beta_abs_le
  intro j
  let chi:=((st.tree.markedAttach 0).map (fun p=>p.coeff*
    fullScalarCutGamma p.tree U K (p.embed st.term.live.test.target) p.mark)).sum
  obtain ⟨hlo,hhi⟩:=native_full_gamma_row_uniform_bounds n st.tree ho 0 ho U (by omega)
    hU K hKm hK (B:=K as.length) le_rfl st.term.live.test.target
  have hchi : 0≤chi:=(Real.exp_pos _).le.trans hlo
  have hbeta : |nativeOriginalClockGBranchBeta U K b st j|≤a.T := by
    unfold nativeOriginalClockGBranchBeta
    change |(if j=0 then chi else 1)*b star|≤a.T
    split_ifs with hj
    · rw [abs_of_nonneg (mul_nonneg hchi (a.bf alpha (partitionPoint 0 as star)).coe_nonneg)]
      exact (mul_le_mul_of_nonneg_right hhi (a.bf alpha (partitionPoint 0 as star)).coe_nonneg).trans
        (by simpa only [one_mul] using hb)
    · rw [one_mul, abs_of_nonneg (show 0≤b star from (a.bf alpha (partitionPoint 0 as star)).coe_nonneg)]
      exact hb
  have H:=native_full_gamma_recursion_coefficient_bound n st.tree ho 0 ho U (by omega)
    hU K hKm hK hterminal st.term.live.test.target hW hcK hstarK hbeta
  dsimp only at H ⊢
  unfold nativeOriginalClockParentWeight
  dsimp only
  rw [abs_mul,abs_of_pos hW]
  apply (mul_le_mul_of_nonneg_left H hW.le).trans
  apply le_of_eq
  field_simp

theorem four_forest_high_profile_le_edges
    (alpha : a.Profile) {as : List PositiveMass} {i star U : ℕ}
    (ho : MassOrdered 0 as) (hist : i ≤ star) (hs : star<U) (hU : U≤as.length)
    {W cK : ℝ} (hW : 0<W) (hcK : 0<cK)
    (hstarK : cK*W≤nativeContinuumMixedClock n (a.bf alpha) (a.hf alpha) as star)
    (depth : ℕ) (seedMass : ℝ) (f : ℕ→ℝ) (hf : ∀j,0≤f j) (hlo : ∀j,j<U→f j=0) :
    let rows:=actualGeneralFourCenteredForest (n:=n) (a.bf alpha) (a.hf alpha) hs hU W depth
      [nativeActualInitialState as i star seedMass (hist.trans (hs.le.trans hU))]
    (rows.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum≤
      2*nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches
        (a.T/(Real.exp (-4*a.T)*cK)) 3 2 depth*edgeBudget 0 as f := by
  let K:=nativeContinuumMixedClock n (a.bf alpha) (a.hf alpha) as
  let b:=fun j=>(a.bf alpha (partitionPoint 0 as j):ℝ)
  let root:=nativeActualInitialState (S:=Spin n×Bool) as i star seedMass (hist.trans (hs.le.trans hU))
  have H:=nativeActualFourCenteredForest_wholeProfile_le ho (nativeOriginalHighRowGamma U K)
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU)
    (fun Q tag=>nativeOriginalClockParentWeight W U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag))
    (show 0≤a.T/(Real.exp (-4*a.T)*cK) from div_nonneg a.hTpos.le (mul_pos (Real.exp_pos _) hcK).le)
    (fun Q tag=>a.four_G_weight_bound alpha ho hs hU hW hcK hstarK Q tag) depth [root] 2
    (by intro Q hQ;have Hq : Q=root:=List.mem_singleton.mp hQ;subst Q;
        exact nativeActualInitialState_leaves_le as i star seedMass (hist.trans (hs.le.trans hU))) f hf hlo
  have Hfork:=nativeActualInitialState_high_forkCost_zero (S:=Spin n×Bool) as i star U hist hs
    (hist.trans (hs.le.trans hU)) seedMass f hlo
  have Hforkroot : root.tree.forkCost f=0:=Hfork
  have Hcoeff : root.term.coefficient=1:=rfl
  simpa only [actualGeneralFourCenteredForest,K,b,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,Hcoeff,abs_one,one_mul,Hforkroot,zero_add] using H

def highThermalMeshBudget (alpha : a.Profile) (as : List PositiveMass)
    (q mesh : ℝ) : ℝ :=
  (∫u in q..1,a.thermal alpha u)+
    mesh*(3*physicalBApproximationConstant n (a.bf alpha) (a.hf alpha)+1)

def highThermalPrice (alpha : a.Profile) (as : List PositiveMass)
    (q mesh : ℝ) : ℝ :=
  2*a.highComparisonConstant*(Real.sqrt (a.highThermalMeshBudget alpha as q mesh)+1/(n+1:ℕ))

theorem original_high_second_edge_le_thermal
    (alpha : a.Profile) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (he : partitionEnd 0 as=1) {mesh q : ℝ} (hm : PartitionMesh mesh 0 as)
    (hq : q∈Icc (0:ℝ) 1) (U : ℕ) (hU : U≤as.length) (hqU : q≤partitionPoint 0 as U) :
    edgeBudget 0 as (fun j=>if j<U then 0 else
      (nativeOriginalCutLowErrorRadius n (a.bf alpha) (a.hf alpha) as j)^2)≤
        a.highThermalMeshBudget alpha as q mesh := by
  exact native_original_high_second_edgeBudget_le_thermal_add_mesh n
    (a.bf alpha) (a.hf alpha) (a.bf_monotone alpha) (a.hf_monotone alpha)
    ho he hm hq U hU hqU

theorem highThermalMeshBudget_nonneg
    (alpha : a.Profile) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (he : partitionEnd 0 as=1) {mesh q : ℝ} (hm : PartitionMesh mesh 0 as)
    (hq : q∈Icc (0:ℝ) 1) (U : ℕ) (hU : U≤as.length) (hqU : q≤partitionPoint 0 as U) :
    0≤a.highThermalMeshBudget alpha as q mesh := by
  exact (edgeBudget_nonneg ho (fun j=>by split_ifs <;> positivity)).trans
    (a.original_high_second_edge_le_thermal alpha ho he hm hq U hU hqU)

theorem highThermalPrice_nonneg (alpha : a.Profile) (as : List PositiveMass)
    (q mesh : ℝ) : 0≤a.highThermalPrice alpha as q mesh := by
  exact mul_nonneg (mul_nonneg (by norm_num) a.highComparisonConstant_nonneg)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))

theorem highErrorEnvelope_nonneg (alpha : a.Profile) (as : List PositiveMass)
    (U j : ℕ) : 0≤a.highErrorEnvelope alpha as U j := by
  unfold highErrorEnvelope nativeOriginalHighErrorEnvelope
  split_ifs
  · exact le_rfl
  · exact mul_nonneg a.highComparisonConstant_nonneg
      (add_nonneg (Real.sqrt_nonneg _) (by positivity))

theorem high_edge_real_moment_le_thermal
    (alpha : a.Profile) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (he : partitionEnd 0 as=1) {mesh q : ℝ} (hm : PartitionMesh mesh 0 as)
    (hq : q∈Icc (0:ℝ) 1) (U : ℕ) (hU : U≤as.length) (hqU : q≤partitionPoint 0 as U)
    {p : ℝ} (hp : 0<p) (hp2 : p≤2) :
    edgeBudget 0 as (fun j=>(a.highErrorEnvelope alpha as U j)^p)≤
      (a.highThermalPrice alpha as q mesh)^p := by
  let A:=a.highThermalMeshBudget alpha as q mesh
  let B:=Real.sqrt A+1/(n+1:ℕ)
  have hA : 0≤A:=a.highThermalMeshBudget_nonneg alpha ho he hm hq U hU hqU
  have hsite : (0:ℝ)≤1/(n+1:ℕ):=by positivity
  have hB : 0≤B:=add_nonneg (Real.sqrt_nonneg _) hsite
  have hsecond : edgeBudget 0 as (fun j=>if j<U then 0 else
      (nativeOriginalCutLowErrorRadius n (a.bf alpha) (a.hf alpha) as j)^2)≤B^2 := by
    apply (a.original_high_second_edge_le_thermal alpha ho he hm hq U hU hqU).trans
    change A≤(Real.sqrt A+1/(n+1:ℕ))^2
    nlinarith [Real.sq_sqrt hA,Real.sqrt_nonneg A]
  have H:=native_high_tail_envelope_second_le ho he U
    (nativeOriginalCutLowErrorRadius n (a.bf alpha) (a.hf alpha) as)
    (fun _=>Real.sqrt_nonneg _) a.highComparisonConstant_nonneg hsite hB
    (show 1/(n+1:ℕ)≤B from le_add_of_nonneg_left (Real.sqrt_nonneg _)) hsecond
  exact native_edgeBudget_real_moment_le ho he (a.highErrorEnvelope alpha as U)
    (a.highErrorEnvelope_nonneg alpha as U) hp hp2 (a.highThermalPrice_nonneg alpha as q mesh) H

theorem high_edge_source_profile_le_thermal
    (alpha : a.Profile) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (he : partitionEnd 0 as=1) {mesh q : ℝ} (hm : PartitionMesh mesh 0 as)
    (hq : q∈Icc (0:ℝ) 1) (U : ℕ) (hU : U≤as.length) (hqU : q≤partitionPoint 0 as U)
    {p W : ℝ} (hp : 0<p) (hp2 : p≤2) (hW : 0≤W) :
    edgeBudget 0 as (fun j=>(a.highErrorEnvelope alpha as U j)^p+
      W*a.highErrorEnvelope alpha as U j)≤
        (a.highThermalPrice alpha as q mesh)^p+W*a.highThermalPrice alpha as q mesh := by
  have HE : (fun j=>(a.highErrorEnvelope alpha as U j)^p+W*a.highErrorEnvelope alpha as U j)=
      (fun j=>1*(a.highErrorEnvelope alpha as U j)^p+W*a.highErrorEnvelope alpha as U j):=by
    funext j;ring
  rw [HE,actual_low_edgeBudget_linear,one_mul]
  have Hfirst:=a.high_edge_real_moment_le_thermal alpha ho he hm hq U hU hqU
    (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)≤2)
  simpa only [Real.rpow_one] using add_le_add
    (a.high_edge_real_moment_le_thermal alpha ho he hm hq U hU hqU hp hp2)
    (mul_le_mul_of_nonneg_left Hfirst hW)

theorem four_forest_high_source_profile_le_thermal
    (alpha : a.Profile) {as : List PositiveMass} {i star U : ℕ}
    (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1) (hist : i ≤ star)
    (hs : star<U) (hU : U≤as.length) {mesh q : ℝ}
    (hm : PartitionMesh mesh 0 as) (hq : q∈Icc (0:ℝ) 1) (hqU : q≤partitionPoint 0 as U)
    {W cK p : ℝ} (hW : 0<W) (hcK : 0<cK) (hp : 0<p) (hp2 : p≤2)
    (hstarK : cK*W≤nativeContinuumMixedClock n (a.bf alpha) (a.hf alpha) as star)
    (depth : ℕ) (seedMass : ℝ) :
    let R:=a.highErrorEnvelope alpha as U
    let f:=fun j=>(R j)^p+W*R j
    let rows:=actualGeneralFourCenteredForest (n:=n) (a.bf alpha) (a.hf alpha) hs hU W depth
      [nativeActualInitialState as i star seedMass (hist.trans (hs.le.trans hU))]
    (rows.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum≤
      2*nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches
        (a.T/(Real.exp (-4*a.T)*cK)) 3 2 depth*
          ((a.highThermalPrice alpha as q mesh)^p+W*a.highThermalPrice alpha as q mesh) := by
  dsimp only
  have hf (j : ℕ):0≤(a.highErrorEnvelope alpha as U j)^p+W*a.highErrorEnvelope alpha as U j:=
    add_nonneg (Real.rpow_nonneg (a.highErrorEnvelope_nonneg alpha as U j) _)
      (mul_nonneg hW.le (a.highErrorEnvelope_nonneg alpha as U j))
  have hlo (j : ℕ) (hj : j<U):
      (a.highErrorEnvelope alpha as U j)^p+W*a.highErrorEnvelope alpha as U j=0:=by
    simp only [highErrorEnvelope,nativeOriginalHighErrorEnvelope,hj,ite_true,
      Real.zero_rpow hp.ne',mul_zero,add_zero]
  apply (a.four_forest_high_profile_le_edges alpha ho hist hs hU hW hcK hstarK depth seedMass _ hf hlo).trans
  have hC : 0≤a.T/(Real.exp (-4*a.T)*cK):=
    div_nonneg a.hTpos.le (mul_pos (Real.exp_pos _) hcK).le
  exact mul_le_mul_of_nonneg_left
    (a.high_edge_source_profile_le_thermal alpha ho he hm hq U hU hqU hp hp2 hW.le)
    (mul_nonneg (by norm_num) (nativeActualWeightedProfileFrontierCost_nonneg
      nativeActualOriginalFourGCenteredBranches hC 3 2 depth))

def highContinuumPrice (alpha : a.Profile) (q : ℝ) : ℝ :=
  2*a.highComparisonConstant*(Real.sqrt (∫u in q..1,a.thermal alpha u)+1/(n+1:ℕ))

theorem eventually_high_edge_real_moment_le_actual_continuum
    (alpha : a.Profile) :
    ∀ᶠjGrid : ℕ in atTop,∀us : List PositiveMass,(∀u∈us,u.val≤1)→
      let as:=finiteCutMasses us jGrid
      ∀q∈Icc (0:ℝ) 1,∀U : ℕ,U≤as.length→q≤partitionPoint 0 as U→
        ∀p : ℝ,0<p→p≤2→
          edgeBudget 0 as (fun j=>(a.highErrorEnvelope alpha as U j)^p)≤
            (a.highContinuumPrice alpha q)^p := by
  let A:=3*physicalBApproximationConstant n (a.bf alpha) (a.hf alpha)+1
  let site:ℝ:=1/(n+1:ℕ)
  have hs : 0<site:=by dsimp [site];positivity
  have Hlim : Tendsto (fun j=>((j+1:ℕ):ℝ)⁻¹*A) atTop (𝓝 0):=by
    simpa only [zero_mul] using uniformMasses_mesh_tendsto.mul_const A
  have HE:=Hlim.eventually (eventually_le_nhds (sq_pos_of_pos hs))
  filter_upwards [HE] with jGrid hj
  intro us hus
  dsimp only
  intro q hq U hU hqU p hp hp2
  let as:=finiteCutMasses us jGrid
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have he : partitionEnd 0 as=1:=finiteCutMasses_end us hus jGrid
  let I:=∫u in q..1,a.thermal alpha u
  have hI : 0≤I:=by
    apply intervalIntegral.integral_nonneg hq.2
    intro u hu
    exact a.thermal_nonneg alpha ⟨hq.1.trans hu.1,hu.2⟩
  let B:=Real.sqrt I+site
  have hB : 0≤B:=add_nonneg (Real.sqrt_nonneg _) hs.le
  have Hraw:=a.original_high_second_edge_le_thermal alpha ho he
    (finiteCutMasses_mesh us hus jGrid) hq U hU hqU
  have Hsecond : edgeBudget 0 as (fun j=>if j<U then 0 else
      (nativeOriginalCutLowErrorRadius n (a.bf alpha) (a.hf alpha) as j)^2)≤B^2:=by
    apply Hraw.trans
    change I+((jGrid+1:ℕ):ℝ)⁻¹*A≤(Real.sqrt I+site)^2
    have Hmul:=mul_nonneg (Real.sqrt_nonneg I) hs.le
    nlinarith [Real.sq_sqrt hI]
  have Henv:=native_high_tail_envelope_second_le ho he U
    (nativeOriginalCutLowErrorRadius n (a.bf alpha) (a.hf alpha) as)
    (fun _=>Real.sqrt_nonneg _) a.highComparisonConstant_nonneg hs.le hB
    (show site≤B from le_add_of_nonneg_left (Real.sqrt_nonneg _)) Hsecond
  exact native_edgeBudget_real_moment_le ho he (a.highErrorEnvelope alpha as U)
    (a.highErrorEnvelope_nonneg alpha as U) hp hp2
    (mul_nonneg (mul_nonneg (by norm_num) a.highComparisonConstant_nonneg) hB) Henv

end OAI.SKFluctuations.LaplaceWindowFormalization.ActualHighWallData
