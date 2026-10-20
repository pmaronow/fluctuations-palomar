module

public import ComparisonActualHighWallStarBandParameters

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem Potential.mass_thermal_slab_decomposition (P : M.Potential)
    {lo hi : ℝ} (hlo : M.data.s≤ lo) (_hlohi : lo≤ hi) (hhi : hi≤1) :
    let model:=M.shiftedNativeModel
    (∫u in Ioo lo hi,model.thermal u)=
      (∫u in Ioo lo hi,P.positiveMassMask u*model.thermal u)+
      (∫u in Ioo lo hi,(P.negativeSet∪P.contactSet).indicator
        (fun _=>1) (model.R u)*model.thermal u) := by
  dsimp only
  let model:=M.shiftedNativeModel
  let F:=model.thermal
  let capmask:=(P.negativeSet∪P.contactSet).indicator (fun _ : ℝ=>(1:ℝ))
  have hsub : Ioo lo hi⊆Icc (0:ℝ) 1:=fun u hu=>
    ⟨M.data.hs.1.le.trans (hlo.trans hu.1.le),hu.2.le.trans hhi⟩
  have hF : IntegrableOn F (Ioo lo hi):=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      (physicalOrderedThermal_intervalIntegrable n M.bf M.hf
        (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha))).mono_set hsub
  have hposmeas : Measurable P.positiveMassMask:=by
    rw [P.positiveMassMask_extended]
    exact measurable_const.indicator (measurableSet_lt measurable_const
      (P.starExtendedH_continuous.comp (M.data.wallRadius_lipschitz M.alpha).continuous).measurable)
  have hcapmeas : Measurable (fun u=>capmask (model.R u)):=
    (measurable_const.indicator (P.negativeSet_open.measurableSet.union P.contactSet_measurable)).comp
      model.R_continuous.measurable
  have hposBound u : ‖P.positiveMassMask u‖≤(1:ℝ):=by
    change ‖(comparisonCalibrationFloor P.H (M.data.wallRadius M.alpha)).indicator (fun _=>(1:ℝ)) u‖≤1
    by_cases hu:u∈comparisonCalibrationFloor P.H (M.data.wallRadius M.alpha)
    · rw [indicator_of_mem hu];norm_num
    · rw [indicator_of_notMem hu];norm_num
  have hcapBound u : ‖capmask (model.R u)‖≤(1:ℝ):=by
    change ‖(P.negativeSet∪P.contactSet).indicator (fun _=>(1:ℝ)) (model.R u)‖≤1
    by_cases hu:model.R u∈P.negativeSet∪P.contactSet
    · rw [indicator_of_mem hu];norm_num
    · rw [indicator_of_notMem hu];norm_num
  have hposI : IntegrableOn (fun u=>P.positiveMassMask u*F u) (Ioo lo hi):=
    hF.bdd_mul hposmeas.aestronglyMeasurable.restrict (ae_of_all _ hposBound)
  have hcapI : IntegrableOn (fun u=>capmask (model.R u)*F u) (Ioo lo hi):=
    hF.bdd_mul hcapmeas.aestronglyMeasurable.restrict (ae_of_all _ hcapBound)
  have hpoint u (hu:u∈Ioo lo hi) : F u=P.positiveMassMask u*F u+capmask (model.R u)*F u:=by
    have hui : u∈Icc M.data.s 1:=⟨hlo.trans hu.1.le,hu.2.le.trans hhi⟩
    have hr:=model.R_bounds u
    have hspec:=model.R_spec hui
    have hrLow : M.data.rmin< model.R u:=by
      apply lt_of_le_of_ne hr.1
      intro HE
      rw [←HE,M.alpha.property.1] at hspec
      linarith [hu.1]
    have hrHigh : model.R u<1:=by
      apply lt_of_le_of_ne hr.2
      intro HE
      rw [HE,M.alpha.property.2.1] at hspec
      linarith [hu.2]
    have hrI : model.R u∈Icc M.data.rmin 1:=hr
    have hrO : model.R u∈Ioo M.data.rmin 1:=⟨hrLow,hrHigh⟩
    by_cases hp : 0< P.H (model.R u)
    · have hc : model.R u∉P.negativeSet∪P.contactSet:=by
        rintro (hn|he)
        · exact not_lt_of_ge hp.le hn.2
        · rw [he.2] at hp;exact lt_irrefl _ hp
      rw [show P.positiveMassMask u=1 from indicator_of_mem hp (fun _=>1),
        show capmask (model.R u)=0 from indicator_of_notMem hc (fun _=>1)]
      ring
    · have hc : model.R u∈P.negativeSet∪P.contactSet:=by
        rcases lt_or_eq_of_le (le_of_not_gt hp) with hh|hh
        · exact Or.inl ⟨hrO,hh⟩
        · exact Or.inr ⟨hrI,hh⟩
      have hm : P.positiveMassMask u=0:=(P.positiveMassMask_zero_iff u).mpr (le_of_not_gt hp)
      rw [hm,show capmask (model.R u)=1 from indicator_of_mem hc (fun _=>1)]
      ring
  have Hsplit : (∫u in Ioo lo hi,F u)=
      (∫u in Ioo lo hi,P.positiveMassMask u*F u)+(∫u in Ioo lo hi,capmask (model.R u)*F u):=by
    rw [←integral_add hposI hcapI]
    exact setIntegral_congr_fun measurableSet_Ioo hpoint
  exact Hsplit

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
