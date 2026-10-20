module

public import ComparisonActualHighOnlyConditionalCapThermalBudget
public import ComparisonActualHighOnlyRetainedRaw

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 40000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
attribute [local instance] Classical.propDecidable
open ActualHighOnlyOverlapMinimum

theorem eventually_actual_high_only_arbitrary_width_cap_source_budget
    (ell:ℕ) (hell:2 < ell) (Bclock:ℝ) {m delta cl cu Az C0 Ct D:ℝ}
    (hm:0 < m) (hdelta:0 < delta) (hroom:delta < 3*m)
    (hcl:0 < cl) (hcu:0 < cu) (hAz:0 ≤ Az) (hC0:0 < C0) (hCt:0 ≤ Ct) :
    ∃Q:ℝ,1 ≤ Q ∧ ∀ᶠn:ℕ in atTop,
      ∀(a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (hs:a.data.s ≤ 1/4) (hsxs:a.data.s ≤ a.xs) (P:a.Potential) (cap:ShiftedCapInterval a P)
        (l z zg V loss y Lside cut:ℝ),
      (P.H cap.left=0 ∨ cap.left=0) ∧ (P.H cap.right=0 ∨ cap.right=1) →
      0 < l → l < z → cap.left ≤ l → z ≤ cap.right → z ≤ zg → zg ≤ 1 →
      V∈Icc (0:ℝ) 1 → (∀r∈Ioo l z,a.alpha.val.val r ≤ V) →
      0 ≤ loss → a.data.M V*(cap.right-cap.left) ≤ loss*(∫r in Ioo l z,deriv a.alpha.val.val r) →
      a.xs+a.alpha.val.val z ≤ y → 0 ≤ Lside → 0 < cut →
      2*cut < (∫r in Ioo l z,deriv a.alpha.val.val r) → Real.log (1/cut) ≤ Lside →
      let width:=∫r in Ioo l z,deriv a.alpha.val.val r
      let power:=a.data.N*laplaceComparisonStrength a.data.d a.lam zg
      let reverse:=a.canonicalMassDiameter^(((ell:ℝ)-2)/((ell:ℝ)-1))*
        ((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
      (∫r in Ioo l z,deriv a.alpha.val.val r*a.shiftedNativeModel.thermal (a.alpha.val.val r)) ≤
        nativeConditionalLedgerBudget 1 width cut a.canonicalMassDiameter
          (108*loss*(Real.log a.data.N)^2/(power*a.alpha.val.val l)*Real.log (width/cut))
          (54*loss*(Real.log a.data.N)^2*width/(power*(a.alpha.val.val l)^2)) reverse Lside := by
  have horder:ell-1+1=ell:=by omega
  obtain ⟨Craw,hCraw,Hraw⟩:=eventually_actual_high_only_original_boundary_raw (ell-1) Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  let Q:=max 1 (Real.sqrt (2*Craw))
  have hQ:1 ≤ Q:=le_max_left _ _
  have Hdepth:=(tendsto_add_atTop_nat 1).eventually (eventually_comparisonLowerScale_depth hC0 hm)
  have Hlog:=(tendsto_add_atTop_nat 1).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1:ℝ))
  refine ⟨Q,hQ,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually Hraw,Hdepth,Hlog] with n hnRaw hnDepth hnLog
  intro a hs hsxs P cap l z zg V loss y Lside cut hcontacts hl hlz hcapL hcapZ hzG hzg
    hV hAV hloss hDensity hY hLside hcut hwidthCut hlogcut
  dsimp only
  have hN:1 ≤ a.data.N:=by exact_mod_cast Nat.succ_pos n
  have hlog:1 ≤ Real.log a.data.N:=hnLog
  have hnd:1/a.data.N ≤ a.data.d:=by
    have HH:=hnDepth a.data.E a.data.d a.data.hE a.data.hd a.hlower
    have HS:comparisonLowerScale (n+1:ℕ) a.data.E a.data.d ≤ a.data.d:=by
      unfold comparisonLowerScale
      exact (div_le_iff₀ a.data.hd).mpr (by simpa only [pow_two] using a.hupper)
    exact HH.trans HS
  let m:=a.shiftedNativeModel
  obtain ⟨us,hus,_,_,hraw⟩:=hnRaw a hs hsxs (⟨1,by norm_num⟩:PositiveMass) le_rfl [] (by simp)
  let grid:=fun j=>finiteCutMasses us j
  let mesh:=fun j:ℕ=>((j+1:ℕ):ℝ)⁻¹
  have ho j:MassOrdered 0 (grid j):=finiteCutMasses_ordered us hus j
  have he j:partitionEnd 0 (grid j)=1:=finiteCutMasses_end us hus j
  have hmesh j:PartitionMesh (mesh j) 0 (grid j):=finiteCutMasses_mesh us hus j
  have hm0 j:0 ≤ mesh j:=by positivity
  have hlim:Tendsto mesh atTop (𝓝 0):=uniformMasses_mesh_tendsto
  have Hwidth:=cap.croppedRows_mass_tendsto hl (hzG.trans hzg) hcapL hcapZ grid mesh ho he hmesh hm0 hlim
  have HwidthCut:∀ᶠj in atTop,2*cut ≤ physicalWindowMass (sampleClockSteps m.q 0 (grid j)) 0
      (cap.croppedRows l z (grid j)):=Hwidth.eventually (eventually_ge_nhds hwidthCut)
  have HrawQ:∀ᶠj in atTop,physicalRawRatio (n+1) ell (sampleClockSteps m.q 0 (grid j)) 0 a.xs
      (Measure.pi fun k=>gaussianReal 0 (m.q 0 k)) id measurable_id ≤ Q:=by
    filter_upwards [hraw] with j hj
    dsimp only at hj
    rw [horder] at hj
    have Hsqrt:=Real.sq_sqrt (show 0 ≤ 2*Craw by positivity)
    have Hpos:=Real.sqrt_nonneg (2*Craw)
    apply le_trans _ (le_max_right 1 (Real.sqrt (2*Craw)))
    nlinarith only [hj.1,Hsqrt,Hpos]
  obtain ⟨J0,hJ0⟩:=eventually_atTop.mp (HwidthCut.and HrawQ)
  have hshift:StrictMono (fun j:ℕ=>j+J0):=fun i j hij=>Nat.add_lt_add_right hij J0
  have HH:=cap.cropped_thermal_le_budget_from_density_length_high_only hN hlog hnd
    (Fintype.card (FeatureIndex (n+1))-1) (cavityCanonicalFeatureEquiv n) hl hzg hcapL hcapZ hlz le_rfl hzG
    hcontacts hV hAV hloss hDensity ell hell hQ hY hLside hcut hlogcut
    (fun j=>grid (j+J0)) (fun j=>mesh (j+J0)) (fun j=>ho (j+J0)) (fun j=>he (j+J0))
    (fun j=>hmesh (j+J0)) (fun j=>hm0 (j+J0)) (hlim.comp hshift.tendsto_atTop)
    hwidthCut.le (fun j=>(hJ0 (j+J0) (by omega)).1) (fun j=>(hJ0 (j+J0) (by omega)).2)
  have hαl:0 < a.alpha.val.val l:=a.shiftedNativeModel.profile_pos hl ((hlz.le.trans hzG).trans hzg)
  have hg:0 < laplaceComparisonStrength a.data.d a.lam zg:=laplaceComparisonStrength_pos _ a.hlam _
  have hn1:0 < (n:ℝ)+1:=by positivity
  convert HH using 1 <;> simp only [ActualHighOnlyComparisonData.N,Nat.cast_add,Nat.cast_one] <;>
    unfold nativeConditionalLedgerBudget <;> field_simp [hαl.ne',hg.ne',hn1.ne'] <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization
