module

public import ComparisonNativeWholeCapDyadicCover

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3600000
attribute [local instance] Classical.propDecidable

abbrev nativeActualBroadSliceScale {ι:Type*} (m : NativeBandModel) (c:ι→NativeActualCapInterval m)
    (p:nativeActualBroadSliceIndex m c) : ℝ := (nativeActualBroadCapSampler m c p.1).scale p.2

theorem nativeActualBroadSlice_common_scale_card_le_four {ι:Type*} [Fintype ι]
    (m:NativeBandModel) (c:ι→NativeActualCapInterval m)
    (hd:Pairwise (fun i j=>Disjoint (Ioo (c i).a (c i).z) (Ioo (c j).a (c j).z)))
    {v:ℝ} (hv:0< v) :
    (Finset.univ.filter (fun p:nativeActualBroadSliceIndex m c=>nativeActualBroadSliceScale m c p=v)).card≤4 := by
  let F := Finset.univ.filter (fun p:nativeActualBroadSliceIndex m c=>nativeActualBroadSliceScale m c p=v)
  let ceil := min (4*v) 1
  have hceil : ceil∈Icc (0:ℝ) 1 :=
    ⟨(lt_min (by linarith) zero_lt_one).le,min_le_right _ _⟩
  have hRceil := comparisonSweepQuantile_bounds m.hc m.hk m.hkc m.hm m.hM m.alpha ceil
  have hscale (p:F) : nativeActualBroadSliceScale m c p.val=v := (Finset.mem_filter.mp p.property).2
  let A := fun p:F=>nativeActualBroadSlice m c p.val
  have hsub (p:F) : A p⊆Icc (0:ℝ) (m.R ceil) := by
    intro r hr
    have hcontracts := (nativeActualBroadCapSampler m c p.val.1).contracts p.val.2
    have hcap := hcontracts.2.2.2.1 hr
    have hr01 : r∈Icc (0:ℝ) 1 :=
      ⟨(c p.val.1.val).ha.trans hcap.1.le,hcap.2.le.trans (c p.val.1.val).hz⟩
    have hmass := hcontracts.2.2.2.2.1 r hr
    have hceiling := hcontracts.2.2.1
    have hmass4 : m.alpha.val.val r≤4*v := by
      rw [←hscale p]
      exact hmass.trans hceiling
    have hmassceil : m.alpha.val.val r≤ ceil := le_min hmass4 (m.alpha.val.property.1 r).2
    have hradius := comparisonSweepQuantile_monotone m.hc m.hk m.hkc m.hm m.hM m.alpha hmassceil
    rw [comparisonSweepQuantile_at_profile m.hc m.hk m.hkc m.hm m.hM m.alpha hr01] at hradius
    exact ⟨hr01.1,hradius⟩
  have hi := (native_inverse_derivative_unit_mass m).1.mono_set
    (Icc_subset_Icc le_rfl hRceil.2)
  have hmassceil : (∫r in Icc (0:ℝ) (m.R ceil),deriv m.alpha.val.val r)=ceil := by
    rw [integral_Icc_eq_integral_Ioc,integral_Ioc_eq_integral_Ioo,
      native_actual_inverse_slice_mass m (by norm_num) hRceil.1 hRceil.2,
      comparisonSweepQuantile_spec m.hc m.hk m.hkc m.hm m.hM m.alpha hceil,m.alpha.property.1,sub_zero]
  have hdisjoint : Pairwise (fun p q:F=>Disjoint (A p) (A q)) := by
    intro p q hpq
    exact nativeActualBroadSlice_disjoint m c hd (fun he=>hpq (Subtype.ext he))
  have hsum : (∑p:F,∫r in A p,deriv m.alpha.val.val r)≤4*v := by
    have heq : (∫r in ⋃p:F,A p,deriv m.alpha.val.val r)=
        ∑p:F,∫r in A p,deriv m.alpha.val.val r :=
      integral_iUnion_fintype (s:=A) (fun _=>measurableSet_Ioo) hdisjoint (fun p=>hi.mono_set (hsub p))
    rw [←heq]
    have hb := setIntegral_mono_set hi (ae_of_all _ (fun r=>m.alpha.val.property.2.deriv_nonneg))
      (ae_of_all _ (fun r hr=>by obtain ⟨p,hp⟩:=mem_iUnion.mp hr;exact hsub p hp))
    exact (hb.trans_eq hmassceil).trans (min_le_left (4*v) 1)
  have hlower (p:F) : v≤∫r in A p,deriv m.alpha.val.val r := by
    rw [←hscale p]
    exact (nativeActualBroadCapSampler m c p.val.1).contracts p.val.2 |>.2.2.2.2.2
  have hs := (Finset.sum_le_sum (s:=Finset.univ) (fun p _=>hlower p)).trans hsum
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  have hc : (F.card:ℝ)≤4 := by
    simpa only [Fintype.card_coe] using (show (Fintype.card F:ℝ)≤(4:ℝ) by nlinarith [hs])
  exact_mod_cast hc

end OAI.SKFluctuations.LaplaceWindowFormalization
