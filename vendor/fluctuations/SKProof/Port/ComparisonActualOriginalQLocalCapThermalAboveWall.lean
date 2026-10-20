module

public import SKProof.Port.OriginalQWholeCapAPI

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
variable {P : a.Potential}
theorem local_finite_cap_thermal_cover_above_wall {ι : Type*} [Fintype ι]
    (c : ι → ShiftedCapInterval a P)
    (A : Set ℝ) (hA : MeasurableSet A) (hAD : A⊆Ioo (0:ℝ) 1)
    (lo : ℝ) (hscale : ∀r∈A,lo≤a.alpha.val.val r)
    (hwall : 8*a.massCoverBase<lo) :
    (∫u in 0..1,(A∩((⋃i,Ioo (c i).left (c i).right)∪P.contactSet)).indicator
      (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u) ≤
      (∫u in 0..1,(A∩P.contactSet).indicator (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)+
      (∫u in 0..1,(relevantComparableCapUnion c A).indicator
        (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)+
      (∑p : RelevantBroadSlice c A,
        ∫u in 0..1,(actualBroadSlice c p.val).indicator (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u) := by
  let full := A ∩ ((⋃i,Ioo (c i).left (c i).right) ∪ P.contactSet)
  let contact := A ∩ P.contactSet
  let comp := relevantComparableCapUnion c A
  let b := fun p : RelevantBroadSlice c A => fun u =>
    (actualBroadSlice c p.val).indicator (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u
  have hfull : MeasurableSet full := hA.inter
    ((MeasurableSet.iUnion (fun _=>measurableSet_Ioo)).union (P.contactSet_measurable))
  have hcontact : MeasurableSet contact := hA.inter (P.contactSet_measurable)
  have hcomp : MeasurableSet comp := MeasurableSet.iUnion (fun _=>measurableSet_Ioo)
  have hiF := a.shiftedNativeModel.thermal_mask_integrable full hfull
  have hiC := a.shiftedNativeModel.thermal_mask_integrable contact hcontact
  have hiComp := a.shiftedNativeModel.thermal_mask_integrable comp hcomp
  have hiB p : IntervalIntegrable (b p) volume 0 1 :=
    a.shiftedNativeModel.thermal_mask_integrable _ measurableSet_Ioo
  have hiSum : IntervalIntegrable (fun u=>∑p,b p u) volume 0 1 := by
    have heq : (fun u=>∑p,b p u)=∑p,b p := by funext u; simp only [Finset.sum_apply]
    rw [heq]
    exact IntervalIntegrable.sum Finset.univ (fun p _=>hiB p)
  have hpoint : ∀ᵐu ∂volume.restrict (Ioc (0:ℝ) 1),
      full.indicator (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u ≤
        contact.indicator (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u+
        comp.indicator (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u+
        (∑p,b p u) := by
    have hc := local_finite_cap_cover_ae c A
    rw [←restrict_Ioc_eq_restrict_Icc] at hc
    filter_upwards [ae_restrict_mem measurableSet_Ioc,hc] with u hu hc
    have hT := a.shiftedNativeModel.thermal_nonneg hu
    have hn (S : Set ℝ) : 0 ≤ S.indicator (fun _=>(1:ℝ)) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u :=
      mul_nonneg (indicator_nonneg (fun _ _=>zero_le_one) _) hT
    have hbn p : 0 ≤ b p u := hn _
    have hsum : 0 ≤ ∑p,b p u := Finset.sum_nonneg (fun p _=>hbn p)
    by_cases hf : a.shiftedNativeModel.R u ∈ full
    · simp only [indicator_of_mem hf,one_mul]
      rcases hc hf with hcontact | hcomp | ⟨p,hp⟩ | hlow
      · have hh : contact.indicator (fun _=>(1:ℝ)) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u=a.shiftedNativeModel.thermal u := by
          rw [indicator_of_mem hcontact,one_mul]
        rw [hh]
        linarith [hn comp]
      · have hh : comp.indicator (fun _=>(1:ℝ)) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u=a.shiftedNativeModel.thermal u := by
          rw [indicator_of_mem hcomp,one_mul]
        rw [hh]
        linarith [hn contact]
      · have hh : b p u=a.shiftedNativeModel.thermal u := by dsimp [b]; simp only [indicator_of_mem hp,one_mul]
        have hs := Finset.single_le_sum (s:=Finset.univ) (f:=fun p=>b p u)
          (fun p _=>hbn p) (Finset.mem_univ p)
        rw [hh] at hs
        linarith [hn contact,hn comp]
      · have hrI : a.shiftedNativeModel.R u∈Ioo a.data.rmin 1 := by
          refine ⟨lt_of_le_of_ne (a.shiftedNativeModel.R_bounds u).1 ?_,(hAD hf.1).2⟩
          intro heq
          have HH:=hscale (a.shiftedNativeModel.R u) hf.1
          rw [←heq,a.alpha.property.1] at HH
          have hbase : a.data.s ≤ a.massCoverBase := le_max_right _ _
          have hs0 : 0 ≤ a.data.s := a.data.hs.1.le
          linarith
        have huHigh : u∈Icc a.data.s 1 :=
          ⟨(a.shiftedNativeModel.R_high_mass hrI.1).le,hu.2⟩
        have HH:=hscale (a.shiftedNativeModel.R u) hf.1
        rw [a.shiftedNativeModel.R_spec huHigh] at HH
        have HL:=min_le_left (8*a.massCoverBase) 1
        exact False.elim (by linarith)
    · simp only [indicator_of_notMem hf,zero_mul]
      linarith [hn contact,hn comp]
  have hb : (∫u in 0..1,full.indicator (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u) ≤
      ∫u in 0..1,contact.indicator (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u+
        comp.indicator (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u+(∑p,b p u) := by
    simp only [intervalIntegral.integral_of_le zero_le_one]
    exact integral_mono_ae ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hiF)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        ((hiC.add hiComp).add hiSum)) hpoint
  rw [intervalIntegral.integral_add (hiC.add hiComp) hiSum,
    intervalIntegral.integral_add hiC hiComp,
    intervalIntegral.integral_finsetSum (fun p _=>hiB p)] at hb
  exact hb

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
