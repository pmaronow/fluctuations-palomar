module

public import PhysicalFiniteContactTrace

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 1000000
section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparisonPhysicalRadiusTrace_boundedWeight_eventually
    {N d lam a z : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N)
    (hd : 0 < d) (hnd : 1/N ≤ d) (hlam : 0 < lam) (hld : lam ≤ d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ→ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hlb : lam ≤ b 0)
    (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    (ha : 0 < a) (haz : a ≤ z) (hz : z ≤ 1)
    (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>b (α.val.val r)) (Icc a z))
    (hfield : LipschitzOnWith Kh (fun r=>h (α.val.val r)) (Icc a z))
    {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Ioo a z)
    (weight : ℝ→ℝ) (hwm : AEStronglyMeasurable weight volume) (K : ℝ)
    (hwb : ∀r∈A,‖weight r‖ ≤ K) (hw0 : ∀r∈A,0 ≤ weight r)
    {ε : ℝ} (hε : 0 < ε) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let S := fun r=>orderedPathS (n+1) bf hf (α.val.val r)
    let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
    ∀ᶠ j in atTop,
      (∫r in A,weight r∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
        n dphys e d lam b h α (as j) (ho j)) ≤
      (∫r in A,weight r*deriv S r)/F+ε := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let clock := completedPathClock (n+1) bf hf
  let S := fun r=>orderedPathS (n+1) bf hf (α.val.val r)
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
  let Cnode := 2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) clock
  let μs := fun j=>comparisonPhysicalRadiusFiniteMeasure hc hk hkc hm hM n dphys e
    d lam b h α (as j) (ho j)
  let ρ := volume.restrict (Icc (0:ℝ) 1)
  let ν := contactDerivativeMeasure S a z F
  have hF : 0 < F := mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith)) (laplaceComparisonStrength_pos d hlam z))
  have hsub : Icc a z⊆Icc (0:ℝ) 1 := Icc_subset_Icc ha.le hz
  have hA01 : A⊆Icc (0:ℝ) 1 := hAD.trans (Ioo_subset_Icc_self.trans hsub)
  have hSm : MonotoneOn S (Icc a z) :=
    ((comparisonVariableEndpoint_radius_moments hc hk hkc hm hM (n+1) (by omega)
      b h hd.ne' hlam.le hlb hb hh hh0 α).1).mono hsub
  have hAC := actual_variableEndpoint_radius_overlap_absolutelyContinuous hc hk hkc hm hM
    n dphys e b h hb hh hh0 hd.ne' hlam.le hlb α ha haz hz Kb hparent Kh hfield
  letI : IsFiniteMeasure ν := contactDerivativeMeasure_isFinite haz hSm hAC hF
  letI : ν.OuterRegular := inferInstance
  have hiS : IntegrableOn (deriv S) A :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le haz).mp hAC.intervalIntegrable_deriv).mono_set
      (hAD.trans Ioo_subset_Icc_self)
  have hweightBound : ∀ᵐ r∂volume.restrict A,‖weight r‖ ≤ K := by
    filter_upwards [ae_restrict_mem hA] with r hr
    exact hwb r hr
  have hAfinite : volume A≠⊤ := ne_top_of_le_ne_top
    (by simp : volume (Icc (0:ℝ) 1)≠⊤) (measure_mono hA01)
  have hiOne : IntegrableOn (fun _ : ℝ=>(1:ℝ)) A := integrableOn_const hAfinite
  have hiWeight : IntegrableOn weight A := by
    simpa only [IntegrableOn,mul_one] using hiOne.bdd_mul hwm.restrict hweightBound
  have hiProd : IntegrableOn (fun r=>weight r*deriv S r) A :=
    hiS.bdd_mul hwm.restrict hweightBound
  have hiρ : IntegrableOn weight A ρ := by
    change Integrable _ ((volume.restrict (Icc (0:ℝ) 1)).restrict A)
    rw [Measure.restrict_restrict_of_subset hA01]
    exact hiWeight
  have hiν : IntegrableOn weight A ν :=
    contactDerivativeMeasure_weight_integrable hSm hF hA
      (hAD.trans Ioo_subset_Icc_self) hiProd
  let error := fun (_ _ : ℝ) (j : ℕ)=>ENNReal.ofReal
    (2*(mesh j*Cnode)/F+2*(mesh j/c))
  have herror : Tendsto (fun j=>2*(mesh j*Cnode)/F+2*(mesh j/c)) atTop (𝓝 0) := by
    convert (((hlim.mul_const Cnode).const_mul 2).div_const F).add
      ((hlim.div_const c).const_mul 2) using 1 <;> simp
  have herr (p q : ℝ) (_ : a ≤ p) (_ : p < q) (_ : q ≤ z) :
      Tendsto (error p q) atTop (𝓝 0) := by
    simpa only [error,Function.comp_def,ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp herror
  have hbound (p q : ℝ) (hap : a ≤ p) (hpq : p < q) (hqz : q ≤ z) :
      ∀ᶠ j in atTop,(μs j:Measure ℝ) (Ioo p q) ≤ ν (Ioo p q)+error p q j := by
    apply Eventually.of_forall
    intro j
    rw [contactDerivativeMeasure_interval haz hSm hAC hF hap hpq.le hqz]
    exact comparisonPhysicalRadiusMeasure_interval_le_fixedStrength hc hk hkc hm hM
      hN hlog hd hnd hlam hld n dphys e b h hb hh hh0 hlb α (as j) (ho j) (hend j)
      (hmesh j) (hmesh0 j) (ha.trans_le hap) hpq.le hqz hz
  have ht := finite_contact_trace_budget_eventually μs ρ (K:=Icc (0:ℝ) 1) isCompact_Icc (by simp [ρ])
    (fun j=>comparisonPhysicalRadiusMeasure_le_compact_volume hc hk hkc hm hM
      n dphys e d lam b h α (as j) (ho j)) ν error herr hbound weight hA hAD
    hiρ hiν hw0 hε
  rw [contactDerivativeMeasure_weight_integral hSm hF hA
    (hAD.trans Ioo_subset_Icc_self)] at ht
  exact ht
end
end OAI.SKFluctuations.LaplaceWindowFormalization
