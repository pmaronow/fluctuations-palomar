module

public import ComparisonSignedCavitySecondLowInheritedOldCBaselineAtomBudget
public import ComparisonSignedCavitySecondLowActualStarAtomSavingAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped BigOperators Topology NNReal ENNReal
set_option maxHeartbeats 35000000

theorem actual_second_low_old_c_baseline_point_budget_along
    {m delta cl cu Az C0 Ct D Bclock Temp Cf Tstar Lwin Cs : ℝ}
    (degree rBound : ℕ) (Cmass Ccut Couter : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCm : 0≤Cmass) (hCcut : 0≤Ccut) (hCouter : 0≤Couter)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (HS : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃C : ℝ,0<C ∧ ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val≤1)→(w n).star∈us→
      (∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹≤(M n).xs→
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i V U : ℕ) (T : ClockTree (Spin (dim n)×Bool) as),
          U≤as.length→i<V→V ≤ star→star<U→T.leaves≤rBound→
          partitionPoint 0 as V≤Ccut*(M n).xs→partitionPoint 0 as U≤Couter*W n→
        ∀(G : ActualNaturalBoundaryShape (dim n) degree T) (forms : Fin degree→NativeSourceFactorForm)
          (initial : Finset (Fin degree)) (x : ℝ),(M n).xs≤x→x≤W n→
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x (W n) initial e)→
        ∀(f c z : T.Slot),f≠z→
          ((T.splitIndex f c=i ∧ T.splitIndex c z=i) ∨
            (T.splitIndex f c=star ∧ T.splitIndex c z=star))→
          let p0:=sourceMonomialScale x (W n) initial
          let d:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
            (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))
          |T.cavityLeft.disorderExpect (restWeight (dim n)) (restFeature (dim n)) 0 q
            (nativeSecondLowUnweightedCOldPayload (dim n) U b h K T f c z
              (G.canonicalMinimumSource (M n) forms).restProduct) 0|≤
            C*(M n).xs*d*p0+
            2*((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*(M n).xs^2*p0 := by
  obtain ⟨Craw,hCraw,Hraw⟩:=eventually_actual_minimum_inherited_second_low_old_c_error_atom_budget
    (D:=D) degree rBound Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  have Hstar:=actual_second_low_star_error_atom_saving_along degree rBound Cmass Couter 1
    hTemp hCf hCm hCouter zero_le_one hm hdelta hroom hcl hcu hAz hC0 hCt
    dim hdim M W hcanonical hWlim w HS hw
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨2*Craw*(1+Ccut),by positivity,?_⟩
  filter_upwards [hdim.eventually Hraw,Hstar,HS,HW1] with n hnRaw hnStar hnHS hnW
  have hxsW:(M n).xs≤W n:=(M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm
  intro L us hus hstar hret hmesh
  filter_upwards [hnRaw (M n) hnHS (hxsW.trans hnW) L us hus hret hmesh,
    hnStar L us hus hstar hret hmesh] with jGrid hgridRaw hgridStar
  dsimp only at hgridRaw hgridStar ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (dim n+1) (M n).bf (M n).hf (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  intro i V U T hU hiV hVstar hstarU hT hcut houter G forms initial x hxsx hxW hmass f c z Hfz Hcuts
  let p0:=sourceMonomialScale x (W n) initial
  let d:=actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
    (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))
  let rate:=((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/32))*(M n).xs^2*p0
  have hp0:0≤p0:=by
    dsimp [p0]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos ((M n).hxs.trans_le hxsx) ((M n).hxs.trans_le hxsW) initial e).le
  have hd:0≤d:=mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hrate:0≤rate:=by dsimp [rate];positivity
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  rw [native_second_low_old_c_baseline_expect_eq_error_atoms (dim n) q U b h K T ho]
  apply (abs_add_le _ _).trans
  rcases Hcuts with ⟨Hfc,Hcz⟩|⟨Hfc,Hcz⟩
  · have Hfi:T.splitIndex f c<U:=Hfc ▸ lt_of_lt_of_le hiV (hVstar.trans hstarU.le)
    have Hci:T.splitIndex c z<U:=Hcz ▸ lt_of_lt_of_le hiV (hVstar.trans hstarU.le)
    have B1:=hgridRaw U T hU hT G forms initial x (W n) hxsx hxW hmass f c z Hfi Hci Hfz true
    have B2:=hgridRaw U T hU hT G forms initial x (W n) hxsx hxW hmass f c z Hfi Hci Hfz false
    simp only [ite_true,Bool.false_eq_true,ite_false,Hfc,Hcz] at B1 B2
    have Hmass:partitionPoint 0 as i≤Ccut*(M n).xs:=
      (partitionPoint_mono as ho hiV.le).trans hcut
    have Hsum:2*(Craw*d*((M n).xs+partitionPoint 0 as i)*p0)≤2*Craw*(1+Ccut)*(M n).xs*d*p0:=by
      have H:=mul_le_mul_of_nonneg_left (add_le_add_left Hmass (M n).xs)
        (mul_nonneg (mul_nonneg hCraw.le hd) hp0)
      convert mul_le_mul_of_nonneg_left H (by norm_num : (0:ℝ)≤2) using 1 <;> ring
    apply (add_le_add B1 B2).trans
    change Craw*d*((M n).xs+partitionPoint 0 as i)*p0+Craw*d*((M n).xs+partitionPoint 0 as i)*p0≤_
    linarith only [Hsum,hrate]
  · have Hfs:T.splitIndex f c<U:=Hfc ▸ hstarU
    have Hcs:T.splitIndex c z<U:=Hcz ▸ hstarU
    have Hfn:f≠c:=native_second_low_low_slots_ne T U hU f c Hfs
    have Hcn:c≠z:=native_second_low_low_slots_ne T U hU c z Hcs
    have hzero:(0:ℝ)∈Icc (0:ℝ) 1:=⟨le_rfl,zero_le_one⟩
    have hone:(1:ℝ)∈Icc (0:ℝ) 1:=⟨zero_le_one,le_rfl⟩
    have B1:=hgridStar U T 0 0 hU hstarU houter hzero hzero hT G forms initial x hxsx hxW hmass
      f c c z f z 1 Hfc Hcs Hcn Hfz hone
    have B2:=hgridStar U T 0 0 hU hstarU houter hzero hzero hT G forms initial x hxsx hxW hmass
      c z f c f z 0 Hcz Hfs Hfn Hfz hzero
    simp only [one_mul] at B1 B2
    have hx:0 < (M n).xs:=(M n).hxs
    have Hinitial:0≤2*Craw*(1+Ccut)*(M n).xs*d*p0:=by positivity
    apply (add_le_add B1 B2).trans
    change rate+rate≤_
    linarith only [Hinitial]

end OAI.SKFluctuations.Cavity
