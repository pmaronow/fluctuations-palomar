module

public import ComparisonActualHighOnlyBroadOuterAtDiameterThermalBudget
public import ComparisonActualHighOnlyLocalDiameterBudgetDefinitions
public import ComparisonActualHighOnlyBroadMassBudget
public import ComparisonActualHighOnlyOrdinaryGroupData
public import ComparisonActualHighOnlyRetainedRaw

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 38000000
set_option linter.unnecessarySeqFocus false
attribute [local instance] Classical.propDecidable
open ActualHighOnlyOverlapMinimum

theorem eventually_actual_high_only_outer_comparable_broad_mass_budget
    (ell : ℕ) (hell : 2< ell) (Bclock : ℝ) {margin delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta<3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤ Az) (hC0 : 0 < C0) (hCt : 0≤ Ct) :
    ∃Q : ℝ,1≤ Q ∧ ∀ᶠn in atTop,
      ∀a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock,
      a.data.s≤1/4 → a.data.s≤ a.xs → ∀P : a.Potential,
      ∀cap : ShiftedCapInterval a P,∀l z v Lside cut : ℝ,
      (P.H cap.left=0 ∨ cap.left=0) ∧ (P.H cap.right=0 ∨ cap.right=1) →
      a.cavityCapTravel≤a.xs → 2*cu*(Az+1)*a.xs≤a.alpha.val.val cap.right →
      0< l → l< z → cap.left≤ l → z≤ cap.right →
      0< v → v≤1 → a.data.s< v/2 → a.data.U≤ v →
      v/2≤ a.alpha.val.val l → a.alpha.val.val z≤ min (4*v) 1 →
      v≤∫r in Ioo l z,deriv a.alpha.val.val r →
      0≤ Lside → 0 < cut → 2*cut< a.data.U → Real.log (1/cut)≤ Lside →
      (∫r in Ioo l z,deriv a.alpha.val.val r*a.shiftedNativeModel.thermal (a.alpha.val.val r))≤
        a.canonicalComparableBroadMassBudgetAtDiameter ell Q Lside cut v
          (∫r in Ioo l z,deriv a.alpha.val.val r) (a.canonicalOuterBroadMassDiameter v) := by
  have horder : ell-1+1=ell:=by omega
  obtain ⟨Craw,hCraw,Hraw⟩:=eventually_actual_high_only_original_boundary_raw (ell-1) Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  let Q:=max 1 (Real.sqrt (2*Craw))
  have hQ : 1≤ Q:=le_max_left _ _
  have Hdepth:=(tendsto_add_atTop_nat 1).eventually (eventually_comparisonLowerScale_depth hC0 hm)
  have Hlog:=(tendsto_add_atTop_nat 1).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1:ℝ))
  refine ⟨Q,hQ,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually Hraw,Hdepth,Hlog] with n hnRaw hnDepth hnLog
  intro a hs hsxs P cap l z v Lside cut hcontacts htravel houter hl0 hlz hclL hzcap hv hv1 hsV hUv hlmass hzmass
    hwidth hLside hcut hcutU hlogcut
  have hz1:=hzcap.trans cap.hright
  have hN : 1≤ a.data.N:=by dsimp only [ActualHighOnlyComparisonData.N];exact_mod_cast Nat.succ_pos n
  have hlog : 1≤ Real.log a.data.N:=hnLog
  have hnd : 1/a.data.N≤ a.data.d:=by
    have HH:=hnDepth a.data.E a.data.d a.data.hE a.data.hd a.hlower
    have HS : comparisonLowerScale (n+1:ℕ) a.data.E a.data.d≤ a.data.d:=by
      unfold comparisonLowerScale
      exact (div_le_iff₀ a.data.hd).mpr (by simpa only [pow_two] using a.hupper)
    exact HH.trans HS
  let m:=a.shiftedNativeModel
  let zg:=m.R (min (16*v) 1)
  have hzg : zg≤1:=(m.R_bounds _).2
  have hzG : z≤ zg:=by
    calc
      z=m.R (a.alpha.val.val z):=(m.R_inverse ⟨hl0.le.trans hlz.le,hz1⟩).symm
      _≤ m.R (min (16*v) 1):=m.R_monotone (hzmass.trans (min_le_min_right 1 (by nlinarith)))
  have hV : min (4*v) 1∈Icc (0:ℝ) 1:=⟨le_min (by positivity) zero_le_one,min_le_right _ _⟩
  have hAV r (hr:r∈Ioo l z) : a.alpha.val.val r≤ min (4*v) 1:=
    (a.alpha.val.property.2 hr.2.le).trans hzmass
  have hY : a.xs+a.alpha.val.val z≤ a.canonicalMassHeight v:=by
    have HH:=hzmass.trans (min_le_min_right 1 (by nlinarith : (4:ℝ)*v≤16*v))
    dsimp only [canonicalMassHeight]
    linarith only [HH]
  obtain ⟨us,hus,_,_,hraw⟩:=hnRaw a hs hsxs (⟨1,by norm_num⟩:PositiveMass) le_rfl [] (by simp)
  let grid:=fun j=> finiteCutMasses us j
  let mesh:=fun j : ℕ=>((j+1:ℕ):ℝ)⁻¹
  have ho j : MassOrdered 0 (grid j):=finiteCutMasses_ordered us hus j
  have he j : partitionEnd 0 (grid j)=1:=finiteCutMasses_end us hus j
  have hmesh j : PartitionMesh (mesh j) 0 (grid j):=finiteCutMasses_mesh us hus j
  have hm0 j : 0 ≤ mesh j:=by positivity
  have hlim : Tendsto mesh atTop (𝓝 0):=uniformMasses_mesh_tendsto
  have Hwidth:=cap.croppedRows_mass_tendsto hl0 hz1 hclL hzcap grid mesh ho he hmesh hm0 hlim
  have HwidthCut : ∀ᶠj in atTop,2*cut≤ physicalWindowMass (sampleClockSteps m.q 0 (grid j)) 0
      (cap.croppedRows l z (grid j)):=Hwidth.eventually
    (eventually_ge_nhds (hcutU.trans_le (hUv.trans hwidth)))
  have HrawQ : ∀ᶠj in atTop,physicalRawRatio (n+1) ell (sampleClockSteps m.q 0 (grid j)) 0 a.xs
      (Measure.pi fun k=> gaussianReal 0 (m.q 0 k)) id measurable_id≤ Q:=by
    filter_upwards [hraw] with j hj
    dsimp only at hj
    rw [horder] at hj
    have Hsqrt:=Real.sq_sqrt (show 0≤2*Craw by positivity)
    have Hpos:=Real.sqrt_nonneg (2*Craw)
    apply le_trans _ (le_max_right 1 (Real.sqrt (2*Craw)))
    nlinarith only [hj.1,Hsqrt,Hpos]
  obtain ⟨J0,hJ0⟩:=eventually_atTop.mp (HwidthCut.and HrawQ)
  have hshift : StrictMono (fun j : ℕ=> j+J0):=fun i j hij=> Nat.add_lt_add_right hij J0
  have hDouter : 0<a.canonicalOuterBroadMassDiameter v:=by
    have HU:=a.data.hU
    have HL:=a.data.hL
    have HE:=a.data.hE
    have HN:=a.data.hN
    have HD:=a.data.hd
    have HT : 0<a.cavityCapTravel:=by
      unfold cavityCapTravel
      exact mul_pos (div_pos HL (Real.rpow_pos_of_pos HN _))
        (Real.log_pos ((one_lt_div HU).mpr (by linarith)))
    unfold canonicalOuterBroadMassDiameter
    exact mul_pos (by linarith) (lt_min HT (by positivity))
  have Hmass:=a.inverse_slice_mass hl0.le hlz.le hz1
  have hvB : v≤a.alpha.val.val cap.right:=by
    have HH:=a.alpha.val.property.2 hzcap
    have H0:=(a.alpha.val.property.1 l).1
    rw [Hmass] at hwidth
    linarith
  have hAmax : a.alpha.val.val cap.left≤4*v:=
    ((a.alpha.val.property.2 hclL).trans (a.alpha.val.property.2 hlz.le)).trans
      (hzmass.trans (min_le_left _ _))
  have Hcap : ∀s∈Ioo cap.left cap.right,∀t∈Ioo cap.left cap.right,s≤t→
      a.radiusS t-a.radiusS s≤a.canonicalOuterBroadMassDiameter v:=by
    intro s hs t ht hst
    exact cap.radiusS_increment_outer_chosen hN hlog hnd hcontacts.1 hcontacts.2
      hcl hcu hAz htravel houter hv hvB hAmax hs ht hst
  have HH:=cap.outer_cropped_thermal_le_budget_at_diameter hDouter Hcap hN hlog hnd
    (Fintype.card (FeatureIndex (n+1))-1) (cavityCanonicalFeatureEquiv n)
    hl0 hzg hclL hzcap hlz le_rfl hzG hcontacts hcl hcu hAz htravel houter (by norm_num : (1:ℝ)≤4) hUv hV
    (min_le_left _ _) a.constraint_length_calibration hAV hzmass (min_le_left _ _) hwidth ell hell hQ hY hLside hcut hlogcut
    (fun j=> grid (j+J0)) (fun j=> mesh (j+J0)) (fun j=> ho (j+J0)) (fun j=> he (j+J0))
    (fun j=> hmesh (j+J0)) (fun j=> hm0 (j+J0)) (hlim.comp hshift.tendsto_atTop)
    (hcutU.le.trans (hUv.trans hwidth)) (fun j=>(hJ0 (j+J0) (by omega)).1)
    (fun j=>(hJ0 (j+J0) (by omega)).2)
  let width:=∫r in Ioo l z,deriv a.alpha.val.val r
  let power:=a.canonicalMassPower v
  let F:=nativeOuterComparableTraceConstant cl cu
  let loss:=F
  have hP : 0< power:=by
    dsimp only [power,canonicalMassPower]
    exact mul_pos a.data.hN (laplaceComparisonStrength_pos a.data.d a.hlam _)
  have hrho : 0< a.alpha.val.val l:=m.profile_pos hl0 (hlz.le.trans hz1)
  have hV4 : 0< v/4:=by positivity
  have hRho : v/4≤ a.alpha.val.val l:=by linarith
  have hF : 0≤F:=native_outer_comparable_trace_constant_nonneg hcl hcu
  have hloss : 0≤ loss:=by dsimp only [loss];positivity
  have hwidth0 : 0≤ width:=hv.le.trans hwidth
  have hlog0 : 0≤ Real.log (width/cut):=Real.log_nonneg
    ((one_le_div hcut).mpr (by have HH:=hcutU.le.trans (hUv.trans hwidth);linarith))
  have HVS : 108*F*(Real.log a.data.N)^2/(power*a.alpha.val.val l)*Real.log (width/cut)≤
      108*loss*(Real.log a.data.N)^2/(power*(v/4))*Real.log (width/cut):=by
    apply mul_le_mul_of_nonneg_right _ hlog0
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (show F≤ loss by dsimp only [loss];linarith) (by norm_num : (0:ℝ)≤108)) (sq_nonneg _))
      (mul_nonneg hP.le hrho.le)).trans
    exact div_le_div_of_nonneg_left (by positivity) (mul_pos hP hV4)
      (mul_le_mul_of_nonneg_left hRho hP.le)
  have HTC : 54*F*(Real.log a.data.N)^2*width/(power*(a.alpha.val.val l)^2)≤
      54*loss*(Real.log a.data.N)^2*width/(power*(v/4)^2):=by
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (show F≤ loss by dsimp only [loss];linarith)
        (by norm_num : (0:ℝ)≤54)) (sq_nonneg _)) hwidth0) (mul_nonneg hP.le (sq_nonneg _))).trans
    exact div_le_div_of_nonneg_left (by positivity) (mul_pos hP (sq_pos_of_pos hV4))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hV4.le hRho 2) hP.le)
  have Hbcoeff : 0≤66+64*Lside+65536*(1+Lside)^2:=by positivity
  have HV:=mul_le_mul_of_nonneg_left HVS (by norm_num : (0:ℝ)≤48)
  have HT:=mul_le_mul_of_nonneg_left HTC Hbcoeff
  apply HH.trans
  have HVeq : 4*(27*(Real.log a.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength a.data.d a.lam zg))*
      (nativeOuterComparableTraceConstant cl cu)/a.alpha.val.val l*Real.log (width/cut)=
      108*F*(Real.log a.data.N)^2/(power*a.alpha.val.val l)*Real.log (width/cut) := by
    dsimp only [F,power,canonicalMassPower,zg,m,ActualHighOnlyComparisonData.N]
    rw [show a.shiftedNativeModel.R=a.R from rfl]
    push_cast
    field_simp
    <;> ring
  have HTeq : 2*(27*(Real.log a.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength a.data.d a.lam zg))*
      (nativeOuterComparableTraceConstant cl cu)/(a.alpha.val.val l)^2*width=
      54*F*(Real.log a.data.N)^2*width/(power*(a.alpha.val.val l)^2) := by
    dsimp only [F,power,canonicalMassPower,zg,m,ActualHighOnlyComparisonData.N]
    rw [show a.shiftedNativeModel.R=a.R from rfl]
    push_cast
    field_simp
    <;> ring
  rw [HVeq,HTeq]
  unfold canonicalComparableBroadMassBudgetAtDiameter nativeConditionalLedgerBudget
  dsimp only [F,loss,power,width,canonicalMassPower,canonicalMassReverseAtDiameter,canonicalMassHeight] at HV HT ⊢
  nlinarith only [HV,HT]

end OAI.SKFluctuations.LaplaceWindowFormalization
