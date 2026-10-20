module

public import ComparisonActualHighWallMixedStarAtWindowAlong
public import ComparisonActualHighWallFourRetainedGammaRawAlong
public import ComparisonActualHighWallBareGaAlong
public import ComparisonActualHighWallBareLongitudinalProfile
public import ComparisonActualHighWallBareJointHighProfile
public import ComparisonActualHighWallBareTaylorLocalThermal
public import ComparisonActualHighWallBareGammaHighProfile
public import ComparisonActualHighWallGammaLowCategoryOriginalRadius
public import ComparisonActualHighWallJointLowCategoryOriginalRadius
public import ComparisonActualHighWallDeletedSiteCategorySaved
public import ComparisonActualHighWallInitialFourSecondLowModulusAlong
public import ComparisonActualGeneralFourOtherSourceSavedLocalLedger
public import ComparisonActualHighWallJointLowCubicPrice

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 36000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_initial_four_other_source_saved_along
    {m delta cl cu Az C0 Ct D Bclock L eta : ℝ}
    (degree dOrder rBound : ℕ) (hd : 0< dOrder)
    (p : ℝ) (hp : 2< p) (hOrder : p/(p-2)≤ (dOrder:ℝ))
    (Cmass Ccut Rmacro F Cx : ℝ) (hCm : 1≤ Cmass) (hCcut : 0≤ Ccut)
    (hCx : 0< Cx) (heta : 0< eta)
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta< 3*m) (hgap : 2*eta< 6*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct)
    (hmacro : 0< Rmacro) (hRhalf : Rmacro≤ 1/2)
    (hFmass : 1+2*cu≤ F) (hFradius : 1+1/Rmacro≤ F) (hL : 0< L)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n=> (M n).data.d) atTop (𝓝 0))
    (Cs : ℝ) (hCs : 0< Cs) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,ActualHighWallOverlapMinimum.IsActualHighWallCalibratedSlowWindow
      (M n) ((M n).data.d) L Cs (w n)) :
    ∃Ca Cg Cl Cj C4 CY Ch Cgl Cjl Cd : ℝ,
      0<Ca ∧ 0<Cg ∧ 0<Cl ∧ 0<Cj ∧ 0<C4 ∧ 0<CY ∧ 0<Ch ∧
      0<Cgl ∧ 0<Cjl ∧ 0<Cd ∧
      ∃C CiU CiB CiM : Fin degree→ℝ, ∃Cf Cr : ℝ,
      (∀a,0<C a ∧ 0<CiU a ∧ 0<CiB a ∧ 0<CiM a) ∧ 0<Cf ∧ 0<Cr ∧
      ∀ᶠn in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val≤ 1)→(∀u∈uniformMasses Lnet,u∈us)→
      ((Lnet+1:ℕ):ℝ)⁻¹≤ (M n).xs→(w n).star∈us→∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      ∀(pre mid tail : List PositiveMass),as=pre++(mid++tail)→
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as→
      ∀(U : ℕ) (_hU : U≤ (pre++(mid++tail)).length)
        (st : NativeActualResourceState (Spin (dim n)×Bool) (pre++(mid++tail)) pre.length (pre.length+mid.length)),
        NativeActualResourceGenerated pre.length (pre.length+mid.length) U [.initial] st.generation st.tree st.term→
        st.term.resources.length≤ degree→0< mid.length→pre.length+mid.length< U→st.tree.leaves≤ rBound→
        partitionPoint 0 as pre.length≤ Cmass*(M n).data.d→
        partitionPoint 0 as (pre.length+mid.length)≤ Cmass*(M n).data.d→
        partitionPoint 0 as U≤ Ccut*(M n).data.d→Ccut*(M n).data.d≤1→
        (M n).data.d≤ Rmacro/2→(Az+1/cl)*(1+Cmass)*(M n).data.d≤ Rmacro/4→
        4*(M n).data.d≤ (M n).data.wallRadius (M n).alpha (partitionPoint 0 as U)→
        (M n).z≤ min ((M n).data.wallRadius (M n).alpha (partitionPoint 0 as U)/8) (Rmacro/4)→
        (M n).data.wallRadius (M n).alpha (partitionPoint 0 as pre.length)≤
          min ((M n).data.wallRadius (M n).alpha (partitionPoint 0 as U)/8) (Rmacro/4)→
        (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length))≤
          min ((M n).data.wallRadius (M n).alpha (partitionPoint 0 as U)/8) (Rmacro/4)→
        ∀sourceMass : ℝ,∀hsourceMass : 0< sourceMass,
        Cx*(M n).xs≤ sourceMass→partitionPoint 0 as U=sourceMass→
        (∀j≤ nativeDyadicCutDepth sourceMass,nativeDyadicMassCut sourceMass hsourceMass j∈us)→
        let R:=(M n).data.highErrorEnvelope (M n).alpha (pre++(mid++tail)) U
        let P:=st.tree.forkCost (fun l=> (R l)^(4/p))+edgeBudget 0 (pre++(mid++tail)) (fun l=> (R l)^(4/p))+
          (M n).data.d*(st.tree.forkCost R+edgeBudget 0 (pre++(mid++tail)) R)
        let rprofile:=st.tree.forkCost R+edgeBudget 0 (pre++(mid++tail)) R
        let Di:=nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length+1/(dim n+1:ℕ)
        let CB:=actualLowErrorComparisonConstant (2*max Bclock 0) (max Bclock 0)
        let Dstar:=(1+CB)*(nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as (pre.length+mid.length)+1/(dim n+1:ℕ))
        let I:=∫u in 0..Ccut*(M n).data.d,Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
          (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)
        let qsecond:=actualHighWallInitialFullB0Envelope degree C CiU CiB CiM Cf Cr
          (originalHighWallInitialPairErrorScale (M n) as pre.length) (M n).data.d (dim n:ℝ) eta
        |((M n).data.d⁻¹)^st.generation*actualGeneralFourOtherSourceErrorContrast (M n).bf (M n).hf U st|≤
          |st.term.coefficient| *nativeResourceScale (M n).data.d (M n).data.d 1 [.initial]*
            ((M n).data.d^3*(Ca*((dim n:ℝ)^(-eta))+Cg*((dim n:ℝ)^(-eta))+
                Cd*((dim n+1:ℕ):ℝ)^(-m)+2*qsecond)+
              (M n).data.d^2*(CY*Di+(CY+Cgl+Cjl)*Dstar+CY*I)+
              (M n).data.d*P*(Ca+2*Cl+Cj+C4+CY)+
              (M n).data.d^2*rprofile*Ch) := by
  let W:=fun n=> (M n).data.d
  have Hmixed:= (actual_high_wall_mixed_projection_at_calibrated_star_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hL dim hdim M hfixed hdlim Cs hCs w hw).2
  have hsaving : 0≤ actualHighWallProjectedStarSaving m delta:=
    (actualHighWallProjectedStarSaving_pos hm hdelta hroom).le
  obtain ⟨Cgr,hCgr,Hgr⟩:=actual_high_wall_same_star_resource_retained_Gamma_along hdim degree (rBound+1)
    Cmass hCm heta hm hdelta hroom hgap hcl hcu hAz hC0 hCt M W (fun _=> rfl) hdlim hfixed hsaving w Hmixed
  obtain ⟨Cg,hCg,Hg⟩:=actual_high_wall_four_retained_Gamma_raw_from_resource_rows_along degree rBound
    hCgr M W w (fun n=> by rw [hfixed n]) Hgr
  obtain ⟨Ca,hCa,Ha⟩:=actual_high_wall_same_star_bare_Ga_along hdim degree dOrder rBound hd p hp hOrder
    Cmass Ccut hCm hCcut heta hm hdelta hroom hgap hcl hcu hAz hC0 hCt M W
    (fun _=> rfl) hdlim hfixed hsaving w Hmixed
  have hCm0 : 0≤ Cmass:=zero_le_one.trans hCm
  obtain ⟨Cl,hCl,HCl⟩:=eventually_actual_high_wall_bare_longitudinal_original_profile (D:=D) degree dOrder rBound hd p hp hOrder Bclock Cmass Ccut hCm0 hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cj,hCj,HCj⟩:=eventually_actual_high_wall_bare_joint_HIGH_original_profile (D:=D) .lowTwoHigh degree dOrder rBound hd p hp hOrder Bclock Cmass Ccut hCm0 hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨C4,hC4,HC4⟩:=eventually_actual_high_wall_bare_joint_HIGH_original_profile (D:=D) .fourGLow degree dOrder rBound hd p hp hOrder Bclock Cmass Ccut hCm0 hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨CY,hCY,HCY⟩:=eventually_actual_high_wall_bare_Taylor_local_thermal_profile (D:=D) degree dOrder rBound hd p hp hOrder Bclock Cmass Ccut hCm0 hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Ch,hCh,HCh⟩:=eventually_actual_high_wall_bare_gamma_HIGH_original_profile (D:=D) degree rBound Bclock Cmass Rmacro F hCm0 hm hdelta hroom hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius
  obtain ⟨Cgl,hCgl,HCgl⟩:=eventually_actual_high_wall_gamma_LOW_category_original_radius_price (D:=D) degree rBound Bclock Cmass Ccut hCm0 hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cjl,hCjl,HCjl⟩:=eventually_actual_high_wall_joint_LOW_category_original_radius_price (D:=D) degree rBound Bclock Cmass Ccut hCm0 hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cd,hCd,HCd⟩:=eventually_actual_high_wall_deleted_site_category_saved_price (D:=D) degree Bclock Cmass hCm0 hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨C,CiU,CiB,CiM,Cf,Cr,hpositive,hCf,hCr,HC2⟩:=
    eventually_actual_high_wall_initial_four_second_low_modulus_price_along (D:=D)
      degree rBound Bclock Cmass Ccut Rmacro F Cx hCx heta hCm0 hCcut
      hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius dim hdim
  refine ⟨Ca,Cg,Cl,Cj,C4,CY,Ch,Cgl,Cjl,Cd,
    hCa,hCg,hCl,hCj,hC4,hCY,hCh,hCgl,hCjl,hCd,
    C,CiU,CiB,CiM,Cf,Cr,hpositive,hCf,hCr,?_⟩
  filter_upwards [Ha,Hg,hdim.eventually HCl,hdim.eventually HCj,hdim.eventually HC4,
    hdim.eventually HCY,hdim.eventually HCh,hdim.eventually HCgl,hdim.eventually HCjl,
    hdim.eventually HCd,HC2,hdim.eventually (eventually_ge_atTop 1)] with
      n hna hng hnl hnj hn4 hnt hnh hngl hnjl hnd hn2 hdim1
  intro Lnet us hus hret hmesh hstar
  filter_upwards [hna Lnet us hus hret hmesh hstar,hng Lnet us hus hret hmesh hstar,
    hnl (M n) (hfixed n) Lnet us hus hret hmesh,
    hnj (M n) (hfixed n) Lnet us hus hret hmesh,
    hn4 (M n) (hfixed n) Lnet us hus hret hmesh,
    hnt (M n) (hfixed n) Lnet us hus hret hmesh,
    hnh (M n) (hfixed n) Lnet us hus hret hmesh,
    hngl (M n) (hfixed n) Lnet us hus hret hmesh,
    hnjl (M n) (hfixed n) Lnet us hus hret hmesh,
    hnd (M n) (hfixed n) Lnet us hus hret hmesh,
    hn2 (M n) (hfixed n) Lnet us hus hret hmesh] with
      jGrid hja hjg hjl hjj hj4 hjt hjh hjgl hjjl hjd hj2
  dsimp only at hja hjg hjl hjj hj4 hjt hjh hjgl hjjl hjd hj2 ⊢
  intro pre mid tail hparts hindex U hU st hP hdegree hmid hs hT hmi hms hcut hcut1
    hsmall hsmall2 hhigh hz hri hrs sourceMass hsourceMass hsource hsourceeq hnodes
  let seed : List NativeResourceMark := [.initial]
  let as:=pre++(mid++tail)
  let a:=M n
  let R:=a.data.highErrorEnvelope a.alpha as U
  let profile:=st.tree.forkCost (fun l=> (R l)^(4/p))+edgeBudget 0 as (fun l=> (R l)^(4/p))+
    a.data.d*(st.tree.forkCost R+edgeBudget 0 as R)
  let rprofile:=st.tree.forkCost R+edgeBudget 0 as R
  let Di:=nativeOriginalCutLowErrorRadius (dim n) a.bf a.hf as pre.length+1/(dim n+1:ℕ)
  let ds:=nativeOriginalCutLowErrorRadius (dim n) a.bf a.hf as (pre.length+mid.length)+1/(dim n+1:ℕ)
  let CB:=actualLowErrorComparisonConstant (2*max Bclock 0) (max Bclock 0)
  let Dstar:=(1+CB)*ds
  let I:=∫u in 0..Ccut*a.data.d,Real.sqrt (orderedPathB (dim n+1) a.bf a.hf u-
    (orderedPathS (dim n+1) a.bf a.hf u)^2)
  let qsecond:=actualHighWallInitialFullB0Envelope degree C CiU CiB CiM Cf Cr
    (originalHighWallInitialPairErrorScale a as pre.length) a.data.d (dim n:ℝ) eta
  let scale:=|st.term.coefficient| *nativeResourceScale a.data.d a.data.d 1 seed
  have hdpos : 0< a.data.d:=a.data.hd
  have hscale : 0≤ scale:=mul_nonneg (abs_nonneg _) (actual_resource_raw_scale_pos seed hdpos hdpos).le
  have ho : MassOrdered 0 as:=by
    dsimp only [as];rw [←hparts];exact finiteCutMasses_ordered us hus jGrid
  have hR l : 0≤ R l:=a.data.highErrorEnvelope_nonneg a.alpha as U l
  have hrprofile : 0≤ rprofile:=add_nonneg (st.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have hprofile : 0≤ profile:=add_nonneg (add_nonneg
    (st.tree.forkCost_nonneg (fun l=> Real.rpow_nonneg (hR l) _))
    (edgeBudget_nonneg ho (fun l=> Real.rpow_nonneg (hR l) _))) (mul_nonneg hdpos.le hrprofile)
  have hdepth : seed.length+st.generation≤ degree:=by rw [←hP.total_factor_depth];exact hdegree
  have hi : pre.length≤ pre.length+mid.length:=by omega
  have hV1 : a.data.wallRadius a.alpha (partitionPoint 0 (finiteCutMasses us jGrid) U)/2≤ 1:=by
    have HH:=(a.data.wallRadius_bounds a.alpha (partitionPoint 0 (finiteCutMasses us jGrid) U)).2
    linarith
  have hVU : a.data.wallRadius a.alpha (partitionPoint 0 (finiteCutMasses us jGrid) U)/2≤
      a.data.wallRadius a.alpha (partitionPoint 0 (finiteCutMasses us jGrid) U):=by linarith only [hhigh,hdpos]
  have hWV : a.data.d≤ a.data.wallRadius a.alpha (partitionPoint 0 (finiteCutMasses us jGrid) U)/2:=by
    linarith only [hhigh,hdpos]
  have hlow : a.data.wallRadius a.alpha (partitionPoint 0 (finiteCutMasses us jGrid) (pre.length+mid.length))≤
      (a.data.wallRadius a.alpha (partitionPoint 0 (finiteCutMasses us jGrid) U)/2)/2:=by
    have HH:=hrs.trans (min_le_left _ _);dsimp only [a] at *;linarith only [HH,hhigh,hdpos]
  have hzV : a.z≤ (a.data.wallRadius a.alpha (partitionPoint 0 (finiteCutMasses us jGrid) U)/2)/2:=by
    have HH:=hz.trans (min_le_left _ _);dsimp only [a] at *;linarith only [HH,hhigh,hdpos]
  have Hga:=hja pre mid tail hparts.symm hindex hms U seed st hP hdegree hmid hs hU hT
    a.data.d (a.data.wallRadius a.alpha (partitionPoint 0 (finiteCutMasses us jGrid) U)/2)
    (by rw [hfixed n]) le_rfl hmi hWV hV1 hVU hlow hzV hcut
  have Hgamma:=hjg pre mid tail hparts.symm hindex hms U seed st hP hdegree hmid hs hU hT
    a.data.d (a.data.wallRadius a.alpha (partitionPoint 0 (finiteCutMasses us jGrid) U)/2)
    (by rw [hfixed n]) le_rfl hmi hWV hV1 hVU hlow hzV
  have H2:=hj2 pre mid tail hparts U hU st hP hdegree hmid hs hT hcut
    a.data.d sourceMass hsourceMass (by rw [hfixed n]) le_rfl hsmall hmi hms hhigh hz hri hrs
    hsource hsourceeq hnodes
  rw [hparts] at H2
  rw [hparts] at hjl hjj hj4 hjt hjh hjgl hjjl hjd
  have hmi' : partitionPoint 0 as pre.length≤ Cmass*a.data.d:=by simpa only [as,hparts,a] using hmi
  have hms' : partitionPoint 0 as (pre.length+mid.length)≤ Cmass*a.data.d:=by simpa only [as,hparts,a] using hms
  have hcut' : partitionPoint 0 as U≤ Ccut*a.data.d:=by simpa only [as,hparts,a] using hcut
  have Hl0:=hjl pre.length (pre.length+mid.length) U seed st hP hi hs hU hT hdepth hmi' hms' hcut' false
  have Hl1:=hjl pre.length (pre.length+mid.length) U seed st hP hi hs hU hT hdepth hmi' hms' hcut' true
  have Hj:=hjj pre.length (pre.length+mid.length) U seed st hP hi hs hU hT hdepth hmi' hms' hcut'
  have H4:=hj4 pre.length (pre.length+mid.length) U seed st hP hi hs hU hT hdepth hmi' hms' hcut'
  have Ht:=hjt pre.length (pre.length+mid.length) U seed st hP hi hs hU hT hdepth hmi' hms' hcut1 hcut'
  have Hh:=hjh pre.length (pre.length+mid.length) U seed st hP hi hs hU hT hdepth hmi' hms' hsmall hsmall2
  have Hgl:=hjgl pre.length (pre.length+mid.length) U seed st hP hi hs hU hT hdepth hmi' hms' hcut'
  have Hjl:=hjjl pre.length (pre.length+mid.length) U seed st hP hi hs hU hT hdepth hmi' hms' hcut'
  have Hd:=hjd pre.length (pre.length+mid.length) U seed st hP hi (hs.trans_le hU) hdepth hmi' hms'
  have Hga' : |(a.data.d⁻¹)^st.generation*actualGeneralFourGaContrast a.bf a.hf U st|≤
      scale*(Ca*((dim n:ℝ)^(-eta))*a.data.d^3+Ca*a.data.d*profile):=by
    change _≤ scale*Ca*(((dim n):ℝ)^(-eta)*(a.data.d*a.xs^2)+a.data.d*profile) at Hga
    rw [hfixed n] at Hga
    convert Hga using 1; ring
  have Hg' : |(a.data.d⁻¹)^st.generation*actualGeneralFourCategoryContrast a.bf a.hf U st .gammaRetained|≤
      scale*(Cg*((dim n:ℝ)^(-eta))*a.data.d^3):=by
    change _≤|st.term.coefficient| *Cg*((dim n):ℝ)^(-eta)*(a.data.d*a.xs^2)*nativeResourceScale a.data.d a.data.d 1 seed at Hgamma
    rw [hfixed n] at Hgamma
    convert Hgamma using 1; dsimp only [scale]; ring
  have hSeedScale : nativeResourceScale a.data.d a.data.d 1 seed=a.data.d:=by
    dsimp only [seed]
    simp [nativeResourceScale,NativeResourceMark.savedScale]
  have H2' : |(a.data.d⁻¹)^st.generation*actualGeneralFourCategoryContrast a.bf a.hf U st .secondLow|≤
      scale*(1*(2*qsecond)*a.data.d^3):=by
    convert H2 using 1
    dsimp only [scale,qsecond,a]
    rw [hSeedScale]
    ring
  let factor:=actualLowErrorComparisonConstant (2*a.data.T) a.data.T
  have hCB : 0≤CB:=actualLowErrorComparisonConstant_nonneg _ (le_max_right _ _)
  have hFactor : factor≤CB:=
    actual_wall_low_error_comparison_constant_le
      (a.data.hepsilon.1.trans a.data.hepsilon.2).le
      (a.hT.trans (le_max_left Bclock 0))
  have hds : 0≤ds:=add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hPlainStar : ds≤Dstar:=by
    dsimp only [Dstar]
    nlinarith only [mul_nonneg hCB hds]
  have hFactorStar : factor*ds≤Dstar:=by
    have H:=mul_le_mul_of_nonneg_right hFactor hds
    dsimp only [Dstar]
    nlinarith only [H,hds]
  change _≤ scale*(Cl*a.data.d*profile) at Hl0 Hl1
  change _≤ scale*(Cj*a.data.d*profile) at Hj
  change _≤ scale*(C4*a.data.d*profile) at H4
  change _≤ scale*(CY*(a.data.d*profile+a.data.d^2*(Di+ds+I))) at Ht
  have Ht' : |(a.data.d⁻¹)^st.generation*actualGeneralFourCategoryContrast a.bf a.hf U st .higherTaylor|≤
      scale*(CY*(a.data.d*profile+a.data.d^2*(Di+Dstar+I))):=by
    apply Ht.trans
    have Hinside : a.data.d*profile+a.data.d^2*(Di+ds+I)≤
        a.data.d*profile+a.data.d^2*(Di+Dstar+I):=by
      nlinarith only [mul_le_mul_of_nonneg_left hPlainStar (sq_nonneg a.data.d)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left Hinside hCY.le) hscale
  change _≤ scale*(Ch*a.data.d^2*rprofile) at Hh
  change _≤ scale*(Cgl*(factor*ds)*a.data.d^2) at Hgl
  have Hgl' : |(a.data.d⁻¹)^st.generation*actualGeneralFourCategoryContrast a.bf a.hf U st .gammaLowRestoration|≤
      scale*(Cgl*a.data.d^2*Dstar):=by
    apply Hgl.trans
    have H:=mul_le_mul_of_nonneg_left hFactorStar (mul_nonneg hCgl.le (sq_nonneg a.data.d))
    convert mul_le_mul_of_nonneg_left H hscale using 1; ring
  change _≤ scale*(Cjl*(factor*ds)*a.data.d^2) at Hjl
  have Hjl' : |(a.data.d⁻¹)^st.generation*actualGeneralFourCategoryContrast a.bf a.hf U st .jointLowRestoration|≤
      scale*(Cjl*a.data.d^2*Dstar):=by
    apply Hjl.trans
    have H:=mul_le_mul_of_nonneg_left hFactorStar (mul_nonneg hCjl.le (sq_nonneg a.data.d))
    convert mul_le_mul_of_nonneg_left H hscale using 1; ring
  change _≤ scale*(Cd*((dim n+1:ℕ):ℝ)^(-m)*a.data.d^3) at Hd
  simp only [NativeJointHighRestorationKind.category] at Hj H4
  have Hledger:=actual_general_four_other_source_saved_local_ledger (U:=U) a.bf a.hf st
    a.data.d scale ((dim n:ℝ)^(-eta)) ((dim n:ℝ)^(-eta))
    (((dim n+1:ℕ):ℝ)^(-m)) (2*qsecond) Di Dstar I profile rprofile
    Ca Cg Cl Cj C4 CY Ch Cgl Cjl Cd 1
    Hga' Hg' Hl0 Hl1 Hj H4 Ht' Hh Hgl' Hjl' Hd H2'
  rw [hparts]
  simpa only [one_mul] using Hledger

end OAI.SKFluctuations.Cavity
