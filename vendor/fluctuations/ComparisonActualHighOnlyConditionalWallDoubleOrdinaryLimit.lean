module

public import ComparisonActualHighOnlyConditionalWallDoubleOrdinarySource
public import ComparisonShiftedNativeThermalGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem Potential.retained_thermal_tendsto_double_wall_high_only
    (P : a.Potential) (ι:Type*) [Fintype ι] (c:ι→ShiftedCapInterval a P)
    (ag:ℕ→ℝ) (hag:∀j,0 ≤ ag j) (hlim:Tendsto ag atTop (𝓝 0))
    {zg:ℝ} (hzg:zg ≤ 1) :
    Tendsto (fun j=>∫u in 0..1,(P.retainedSupport c (ag j) zg).indicator (fun _=>1)
      (a.R u)*a.shiftedNativeModel.thermal u) atTop
      (𝓝 (∫u in 0..1,(P.retainedSupport c 0 zg).indicator (fun _=>1)
        (a.R u)*a.shiftedNativeModel.thermal u)) := by
  let T:=a.shiftedNativeModel.thermal
  have hT:IntegrableOn T (Icc (0:ℝ) 1):=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      (physicalOrderedThermal_intervalIntegrable n a.bf a.hf a.bf_monotone a.hf_monotone)
  have hmasks j:MeasurableSet (P.retainedSupport c (ag j) zg):=P.retainedSupport_measurable c (hag j) hzg
  have hR:Measurable a.R:=a.shiftedNativeModel.R_continuous.measurable
  have Hset:Tendsto (fun j=>∫u in Icc (0:ℝ) 1,(P.retainedSupport c (ag j) zg).indicator
      (fun _=>(1:ℝ)) (a.R u)*T u) atTop
      (𝓝 (∫u in Icc (0:ℝ) 1,(P.retainedSupport c 0 zg).indicator (fun _=>(1:ℝ)) (a.R u)*T u)):=by
    apply tendsto_integral_of_dominated_convergence (fun u=>‖T u‖)
    · intro j
      exact (((measurable_const.indicator (hmasks j)).comp hR).aestronglyMeasurable.restrict).mul
        hT.aestronglyMeasurable
    · exact hT.norm
    · intro j
      filter_upwards [] with u
      by_cases hu:a.R u∈P.retainedSupport c (ag j) zg
      · simp only [indicator_of_mem hu,one_mul,le_refl]
      · simp only [indicator_of_notMem hu,zero_mul,norm_zero]
        exact norm_nonneg _
    · filter_upwards [] with u
      apply tendsto_const_nhds.congr'
      by_cases hr:0 < a.R u
      · filter_upwards [hlim.eventually (gt_mem_nhds hr)] with j hj
        have he:(a.R u∈P.retainedSupport c 0 zg)↔(a.R u∈P.retainedSupport c (ag j) zg):=by
          change (a.R u∈Ioo (0:ℝ) zg ∩ _)↔(a.R u∈Ioo (ag j) zg ∩ _)
          simp only [mem_inter_iff,mem_Ioo,hr,hj,true_and]
        by_cases h:a.R u∈P.retainedSupport c 0 zg
        · rw [indicator_of_mem h,indicator_of_mem (he.mp h)]
        · rw [indicator_of_notMem h,indicator_of_notMem (fun HH=>h (he.mpr HH))]
      · have hnot0:a.R u∉Ioo (0:ℝ) zg:=fun h=>hr h.1
        have hnot j:a.R u∉Ioo (ag j) zg:=fun h=>hr ((hag j).trans_lt h.1)
        filter_upwards [] with j
        have h0:a.R u∉P.retainedSupport c 0 zg:=fun HH=>hnot0 HH.1
        have hj:a.R u∉P.retainedSupport c (ag j) zg:=fun HH=>hnot j HH.1
        rw [indicator_of_notMem h0,indicator_of_notMem hj]
  simpa only [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc,T] using Hset

end ActualHighOnlyOverlapMinimum
open ActualHighOnlyOverlapMinimum

theorem eventually_actual_high_only_wall_double_ordinary_complete_budget
    (ell:ℕ) (hell:2 < ell) (Bclock:ℝ) {m delta cl cu Az C0 Ct D:ℝ}
    (hm:0 < m) (hdelta:0 < delta) (hroom:delta < 3*m)
    (hcl:0 < cl) (hcu:0 < cu) (hAz:0 ≤ Az) (hC0:0 < C0) (hCt:0 ≤ Ct) :
    ∃Q:ℝ,1 ≤ Q ∧ ∀ᶠn:ℕ in atTop,
      ∀(a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (hs:a.data.s ≤ 1/4) (hsxs:a.data.s ≤ a.xs) (hspos:0 < a.data.s) (P:a.Potential)
        (ι:Type*) [Fintype ι] (c:ι→ShiftedCapInterval a P),
      (∀t,∀r∈Ioo (c t).left (c t).right,wholeUnit P.negativeSet r=Ioo (c t).left (c t).right) →
      (∀t,P.H (c t).left=0 ∧ (P.H (c t).right=0 ∨ (c t).right=1)) →
      Pairwise (fun t u=>Disjoint (Ioo (c t).left (c t).right) (Ioo (c u).left (c u).right)) →
      NativePullbackClockRegularity a.alpha.val.val a.b a.h 0 1 →
      (∀t,0 < (c t).left) → (∀t,a.alpha.val.val (c t).right ≤ min (32*a.data.s) 1) →
      ∀Lside cut:ℝ,0 ≤ Lside → 0 < cut → Real.log (1/cut) ≤ Lside →
      (∫u in 0..1,(P.retainedSupport c 0 (a.R (min (32*a.data.s) 1))).indicator (fun _=>1)
        (a.R u)*a.shiftedNativeModel.thermal u) ≤ a.canonicalOrdinaryMassBudget ell Q Lside cut (2*a.data.s) := by
  obtain ⟨Q,hQ,Hphysical⟩:=eventually_actual_high_only_wall_double_ordinary_source_budget ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Q,hQ,?_⟩
  filter_upwards [Hphysical] with n hn
  intro a hs hsxs hspos P ι inst c hwhole hcontacts hdisjoint hclock hleftpos hright Lside cut hLside hcut hlogcut
  let zg:=a.R (min (32*a.data.s) 1)
  have hmass:min (32*a.data.s) 1∈Icc a.data.s 1:=
    ⟨le_min (by linarith) a.data.hs1,min_le_right _ _⟩
  have hmassgt:a.data.s < min (32*a.data.s) 1:=lt_min (by linarith) (by linarith)
  have hzg:0 < zg:=by
    dsimp only [zg]
    by_contra H
    have Hz:a.R (min (32*a.data.s) 1)=0:=le_antisymm (le_of_not_gt H)
      (a.shiftedNativeModel.R_bounds _).1
    have HH:=a.shiftedNativeModel.R_spec hmass
    change a.alpha.val.val (a.R (min (32*a.data.s) 1))=min (32*a.data.s) 1 at HH
    rw [Hz,a.alpha.property.1] at HH
    have Hgt:a.data.s < min (32*a.data.s) 1:=lt_min (by linarith) (by linarith)
    exact Hgt.ne HH
  have hzg1:zg ≤ 1:=(a.shiftedNativeModel.R_bounds _).2
  let ag:=fun j:ℕ=>zg/((j+1:ℕ):ℝ)
  have hag j:0 < ag j:=by dsimp [ag];positivity
  have hagz j:ag j ≤ zg:=by
    apply div_le_self hzg.le
    exact_mod_cast (show 1 ≤ j+1 by omega)
  have hlim:Tendsto ag atTop (𝓝 0):=by
    simpa only [ag,div_eq_mul_inv,mul_zero] using uniformMasses_mesh_tendsto.const_mul zg
  have Hleft:∀ᶠj:ℕ in atTop,∀t,ag j ≤ (c t).left:=eventually_all.2
    (fun t=>hlim.eventually (eventually_le_nhds (hleftpos t)))
  apply le_of_tendsto (P.retained_thermal_tendsto_double_wall_high_only ι c ag (fun j=>(hag j).le) hlim hzg1)
  filter_upwards [Hleft] with j hj
  exact hn a hs hsxs hspos P ι c (ag j) hwhole hcontacts hdisjoint (hag j) (hagz j)
    (hclock.restrict (hag j).le hzg1) hj hright Lside cut hLside hcut hlogcut

end OAI.SKFluctuations.LaplaceWindowFormalization
