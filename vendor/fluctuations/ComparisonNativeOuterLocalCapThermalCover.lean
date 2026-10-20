module

public import ComparisonNativeLocalMassBandAssembly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable

theorem actual_native_outer_local_finite_cap_thermal_cover {ι : Type*} [Fintype ι]
    (m : NativeBandModel) (c : ι → NativeActualCapInterval m)
    (A : Set ℝ) (hA : MeasurableSet A) {lo : ℝ} (h8 : 8*m.U ≤ lo)
    (hscale : ∀r∈A,lo ≤ m.alpha.val.val r) :
    (∫u in 0..1,(A∩((⋃i,Ioo (c i).a (c i).z)∪nativeActualContactSet m)).indicator
      (fun _=>1) (m.R u)*m.thermal u) ≤
      (∫u in 0..1,(A∩nativeActualContactSet m).indicator (fun _=>1) (m.R u)*m.thermal u)+
      (∫u in 0..1,(nativeRelevantComparableCapUnion m c A).indicator
        (fun _=>1) (m.R u)*m.thermal u)+
      (∑p : NativeRelevantBroadSlice m c A,
        ∫u in 0..1,(nativeActualBroadSlice m c p.val).indicator (fun _=>1) (m.R u)*m.thermal u) := by
  let full := A ∩ ((⋃i,Ioo (c i).a (c i).z) ∪ nativeActualContactSet m)
  let contact := A ∩ nativeActualContactSet m
  let comp := nativeRelevantComparableCapUnion m c A
  let b := fun p : NativeRelevantBroadSlice m c A => fun u =>
    (nativeActualBroadSlice m c p.val).indicator (fun _=>1) (m.R u)*m.thermal u
  have hU := m.hU
  have hfull : MeasurableSet full := hA.inter
    ((MeasurableSet.iUnion (fun _=>measurableSet_Ioo)).union (nativeActualContactSet_measurable m))
  have hcontact : MeasurableSet contact := hA.inter (nativeActualContactSet_measurable m)
  have hcomp : MeasurableSet comp := MeasurableSet.iUnion (fun _=>measurableSet_Ioo)
  have hiF := nativeActualThermal_mask_integrable m full hfull
  have hiC := nativeActualThermal_mask_integrable m contact hcontact
  have hiComp := nativeActualThermal_mask_integrable m comp hcomp
  have hiB p : IntervalIntegrable (b p) volume 0 1 :=
    nativeActualThermal_mask_integrable m _ measurableSet_Ioo
  have hiSum : IntervalIntegrable (fun u=>∑p,b p u) volume 0 1 := by
    have heq : (fun u=>∑p,b p u)=∑p,b p := by funext u; simp only [Finset.sum_apply]
    rw [heq]
    exact IntervalIntegrable.sum Finset.univ (fun p _=>hiB p)
  have hpoint : ∀ᵐu ∂volume.restrict (Ioc (0:ℝ) 1),
      full.indicator (fun _=>1) (m.R u)*m.thermal u ≤
        contact.indicator (fun _=>1) (m.R u)*m.thermal u+
        comp.indicator (fun _=>1) (m.R u)*m.thermal u+
        (∑p,b p u) := by
    have hc := native_local_finite_cap_cover_ae m c A
    rw [←restrict_Ioc_eq_restrict_Icc] at hc
    filter_upwards [ae_restrict_mem measurableSet_Ioc,hc] with u hu hc
    have hT := nativeActualThermal_nonneg m hu
    have hn (S : Set ℝ) : 0 ≤ S.indicator (fun _=>(1:ℝ)) (m.R u)*m.thermal u :=
      mul_nonneg (indicator_nonneg (fun _ _=>zero_le_one) _) hT
    have hbn p : 0 ≤ b p u := hn _
    have hsum : 0 ≤ ∑p,b p u := Finset.sum_nonneg (fun p _=>hbn p)
    by_cases hf : m.R u ∈ full
    · simp only [indicator_of_mem hf,one_mul]
      rcases hc hf with hcontact | hcomp | ⟨p,hp⟩ | hlow
      · have hh : contact.indicator (fun _=>(1:ℝ)) (m.R u)*m.thermal u=m.thermal u := by
          rw [indicator_of_mem hcontact,one_mul]
        rw [hh]
        linarith [hn comp]
      · have hh : comp.indicator (fun _=>(1:ℝ)) (m.R u)*m.thermal u=m.thermal u := by
          rw [indicator_of_mem hcomp,one_mul]
        rw [hh]
        linarith [hn contact]
      · have hh : b p u=m.thermal u := by dsimp [b]; simp only [indicator_of_mem hp,one_mul]
        have hs := Finset.single_le_sum (s:=Finset.univ) (f:=fun p=>b p u)
          (fun p _=>hbn p) (Finset.mem_univ p)
        rw [hh] at hs
        linarith [hn contact,hn comp]
      · have hs := native_mass_slice_profile_mem m
          (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num)
          (show min (8*m.U) 1∈Icc (0:ℝ) 1 from
            ⟨le_min (by positivity) zero_le_one,min_le_right _ _⟩) hlow
        have hl := hscale (m.R u) hf.1
        exfalso
        linarith [hs.2,min_le_left (8*m.U) 1]
    · simp only [indicator_of_notMem hf,zero_mul]
      linarith [hn contact,hn comp]
  have hb : (∫u in 0..1,full.indicator (fun _=>1) (m.R u)*m.thermal u) ≤
      ∫u in 0..1,contact.indicator (fun _=>1) (m.R u)*m.thermal u+
        comp.indicator (fun _=>1) (m.R u)*m.thermal u+(∑p,b p u) := by
    simp only [intervalIntegral.integral_of_le zero_le_one]
    exact integral_mono_ae ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hiF)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        ((hiC.add hiComp).add hiSum)) hpoint
  rw [intervalIntegral.integral_add (hiC.add hiComp) hiSum,
    intervalIntegral.integral_add hiC hiComp,
    intervalIntegral.integral_finsetSum (fun p _=>hiB p)] at hb
  exact hb

end OAI.SKFluctuations.LaplaceWindowFormalization
