module

public import ComparisonNativeOuterLocalCapThermalCover

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 7000000
attribute [local instance] Classical.propDecidable

theorem actual_native_outer_local_finite_cap_thermal_le_dyadic_sum {ι : Type*} [Fintype ι]
    {m : NativeBandModel} (g : NativeContactDyadicBandFamily m)
    (c : ι→NativeActualCapInterval m) (A : Set ℝ) (hA : MeasurableSet A)
    (hcase : ∀i,(m.H (c i).a=0 ∧ m.H (c i).z=0) ∨
      ((c i).a=0 ∧ m.H (c i).z=0) ∨ (m.H (c i).a=0 ∧ (c i).z=1))
    {lo hi : ℝ} (h8 : 8*m.U ≤ lo)
    (hscale : ∀r∈A,lo ≤ m.alpha.val.val r ∧ m.alpha.val.val r ≤ hi) :
    (∫u in 0..1,(A∩((⋃i,Ioo (c i).a (c i).z)∪nativeActualContactSet m)).indicator
      (fun _=>1) (m.R u)*m.thermal u) ≤
      2*(∑j : NativeLocalMassDyad m lo hi,
        ∫u in 0..1,(g.model j.val).ordinaryMask ((g.model j.val).R u)*(g.model j.val).thermal u)+
      (∑p : NativeRelevantBroadSlice m c A,
        ∫u in 0..1,(nativeActualBroadSlice m c p.val).indicator (fun _=>1) (m.R u)*m.thermal u) := by
  have hU : m.U ≤ lo := by linarith [m.hU]
  have hf := actual_native_outer_local_finite_cap_thermal_cover m c A hA h8 (fun r hr=>(hscale r hr).1)
  have hc := g.contact_thermal_le_local_sum A hA hU hscale
  have ho := g.relevant_comparable_thermal_le_local_sum c A hcase hscale
  linarith

theorem actual_native_outer_local_cap_contact_thermal_bound
    {m : NativeBandModel} (g : NativeContactDyadicBandFamily m)
    (A : Set ℝ) (hA : MeasurableSet A) {lo hi O B : ℝ}
    (h8 : 8*m.U ≤ lo) (hshort : nativeCapTravel m < 1) (hO : 0 ≤ O) (hB : 0 ≤ B)
    (hscale : ∀r∈A,lo ≤ m.alpha.val.val r ∧ m.alpha.val.val r ≤ hi)
    (hOrd : ∀j : NativeLocalMassDyad m lo hi,
      (∫u in 0..1,(g.model j.val).ordinaryMask ((g.model j.val).R u)*(g.model j.val).thermal u) ≤ O)
    (hBroad : ∀(F : Finset (ordConnectedSection (nativeNegativeSet m)))
      (c : F→NativeActualCapInterval m),
      (∀i,(m.H (c i).a=0 ∧ m.H (c i).z=0) ∨
        ((c i).a=0 ∧ m.H (c i).z=0) ∨ (m.H (c i).a=0 ∧ (c i).z=1)) →
      (⋃i,Ioo (c i).a (c i).z)=wholeCapFiniteUnion (nativeNegativeSet m) F →
      Pairwise (fun i j=>Disjoint (Ioo (c i).a (c i).z) (Ioo (c j).a (c j).z)) →
      ∀p : NativeRelevantBroadSlice m c A,
        (∫u in 0..1,(nativeActualBroadSlice m c p.val).indicator
          (fun _=>1) (m.R u)*m.thermal u) ≤ B) :
    (∫u in 0..1,(A∩(nativeNegativeSet m∪nativeActualContactSet m)).indicator
      (fun _=>1) (m.R u)*m.thermal u) ≤
      (2*O+4*B)*(Nat.ceil (Real.log (1/m.U)/Real.log 2)+1) := by
  have hU : m.U ≤ lo := by linarith [m.hU]
  have hfinite (F : Finset (ordConnectedSection (nativeNegativeSet m))) :
      (∫u in 0..1,(A∩(wholeCapFiniteUnion (nativeNegativeSet m) F∪nativeActualContactSet m)).indicator
        (fun _=>1) (m.R u)*m.thermal u) ≤
        (2*O+4*B)*(Nat.ceil (Real.log (1/m.U)/Real.log 2)+1) := by
    obtain ⟨c,hcase,hunion,hd⟩ := exists_actual_native_negative_cap_family m F hshort
    have hc := actual_native_outer_local_finite_cap_thermal_le_dyadic_sum g c A hA hcase h8 hscale
    have hsO := Finset.sum_le_sum (s:=Finset.univ) (fun j _=>hOrd j)
    have hsB := Finset.sum_le_sum (s:=Finset.univ) (fun p _=>hBroad F c hcase hunion hd p)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsO hsB
    have hcountO : (Fintype.card (NativeLocalMassDyad m lo hi):ℝ) ≤
        Nat.ceil (Real.log (1/m.U)/Real.log 2)+1 := by
      exact_mod_cast native_local_mass_dyad_card_le_log (m:=m) (lo:=lo) (hi:=hi)
    have hcountB : (Fintype.card (NativeRelevantBroadSlice m c A):ℝ) ≤
        4*(Nat.ceil (Real.log (1/m.U)/Real.log 2)+1) := by
      exact_mod_cast native_relevant_broad_slice_card_le_log_count m c A hd
    have hmulO := mul_le_mul_of_nonneg_right hcountO hO
    have hmulB := mul_le_mul_of_nonneg_right hcountB hB
    rw [hunion] at hc
    nlinarith
  have hH : ContinuousOn m.H (Icc (0:ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using m.hH.continuousOn
  have hT : IntervalIntegrable m.thermal volume 0 1 := by
    simpa only [indicator_univ,one_mul] using nativeActualThermal_mask_integrable m univ MeasurableSet.univ
  have hb := NativeCapExhaustion.actual_local_full_thermal_le_of_finite_caps
    m.hc m.hk m.hkc m.hm m.hM m.alpha (nativeNegativeSet_open m) (nativeNegativeSet_subset m)
    m.H hH A hA m.thermal ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hT)
    (B:=(2*O+4*B)*(Nat.ceil (Real.log (1/m.U)/Real.log 2)+1)) (by
      intro F
      have he (u : ℝ) :
          (A∩NativeSelectedMask.fixedSupport (NativeCapExhaustion.left (nativeNegativeSet m) F)
            (NativeCapExhaustion.right (nativeNegativeSet m) F) m.H).indicator (fun _=>(1:ℝ)) (m.R u)=
          (A∩(wholeCapFiniteUnion (nativeNegativeSet m) F∪nativeActualContactSet m)).indicator
            (fun _=>1) (m.R u) := by
        rw [NativeCapExhaustion.fixedSupport_eq (nativeNegativeSet_open m) (nativeNegativeSet_subset m)]
        have hr := comparisonSweepQuantile_bounds m.hc m.hk m.hkc m.hm m.hM m.alpha u
        simp only [indicator_apply,mem_inter_iff,mem_union,mem_ofPred_eq,nativeActualContactSet,
          mem_preimage,mem_singleton_iff,hr,true_and]
      simp_rw [he]
      rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le zero_le_one]
      exact hfinite F)
  have he (u : ℝ) :
      (A∩(nativeNegativeSet m∪{r | m.H r=0})).indicator (fun _=>(1:ℝ)) (m.R u)=
      (A∩(nativeNegativeSet m∪nativeActualContactSet m)).indicator (fun _=>1) (m.R u) := by
    have hr := comparisonSweepQuantile_bounds m.hc m.hk m.hkc m.hm m.hM m.alpha u
    simp only [indicator_apply,mem_inter_iff,mem_union,mem_ofPred_eq,nativeActualContactSet,
      mem_preimage,mem_singleton_iff,hr,true_and]
  simp_rw [he] at hb
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le zero_le_one] at hb
  exact hb

end OAI.SKFluctuations.LaplaceWindowFormalization
