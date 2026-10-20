module

public import ComparisonActualHighOnlyBroadSliceIndex

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
variable {P : a.Potential}
theorem actualBroadSlice_common_scale_card_le_four {ι:Type*} [Fintype ι]
    (c:ι→ShiftedCapInterval a P)
    (hd:Pairwise (fun i j=>Disjoint (Ioo (c i).left (c i).right) (Ioo (c j).left (c j).right)))
    {v:ℝ} (hv:0< v) (hs : a.data.s≤v) :
    (Finset.univ.filter (fun p:ActualBroadSliceIndex c=>actualBroadSliceScale c p=v)).card≤4 := by
  let F := Finset.univ.filter (fun p:ActualBroadSliceIndex c=>actualBroadSliceScale c p=v)
  let ceil := min (4*v) 1
  have hceil : ceil∈Icc a.data.s 1 :=
    ⟨le_min (by linarith) a.data.hs1,min_le_right _ _⟩
  have hRceil := a.shiftedNativeModel.R_bounds ceil
  have hscale (p:F) : actualBroadSliceScale c p.val=v := (Finset.mem_filter.mp p.property).2
  let A := fun p:F=>actualBroadSlice c p.val
  have hsub (p:F) : A p⊆Icc (0:ℝ) (a.shiftedNativeModel.R ceil) := by
    intro r hr
    have hcontracts := (actualBroadCapSampler c p.val.1).contracts p.val.2
    have hcap := hcontracts.2.2.2.1 hr
    have hr01 : r∈Icc (0:ℝ) 1 :=
      ⟨(c p.val.1.val).hleft.trans hcap.1.le,hcap.2.le.trans (c p.val.1.val).hright⟩
    have hmass := hcontracts.2.2.2.2.1 r hr
    have hceiling := hcontracts.2.2.1
    have hmass4 : a.alpha.val.val r≤4*v := by
      rw [←hscale p]
      exact hmass.trans hceiling
    have hmassceil : a.alpha.val.val r≤ ceil := le_min hmass4 (a.alpha.val.property.1 r).2
    have hradius := a.shiftedNativeModel.R_monotone hmassceil
    rw [a.shiftedNativeModel.R_inverse hr01] at hradius
    exact ⟨hr01.1,hradius⟩
  have hi := a.shiftedNativeModel.inverse_derivative_unit_mass.1.mono_set
    (Icc_subset_Icc le_rfl hRceil.2)
  have hmassceil : (∫r in Icc (0:ℝ) (a.shiftedNativeModel.R ceil),deriv a.alpha.val.val r)=ceil-a.data.s := by
    rw [integral_Icc_eq_integral_Ioc,integral_Ioc_eq_integral_Ioo,
      a.shiftedNativeModel.inverse_slice_mass (show (0:ℝ)∈Icc a.shiftedNativeModel.rmin 1 by norm_num) hRceil hRceil.1,
      a.shiftedNativeModel.R_spec hceil,a.alpha.property.1]
  have hdisjoint : Pairwise (fun p q:F=>Disjoint (A p) (A q)) := by
    intro p q hpq
    exact actualBroadSlice_disjoint c hd (fun he=>hpq (Subtype.ext he))
  have hsum : (∑p:F,∫r in A p,deriv a.alpha.val.val r)≤4*v := by
    have heq : (∫r in ⋃p:F,A p,deriv a.alpha.val.val r)=
        ∑p:F,∫r in A p,deriv a.alpha.val.val r :=
      integral_iUnion_fintype (s:=A) (fun _=>measurableSet_Ioo) hdisjoint (fun p=>hi.mono_set (hsub p))
    rw [←heq]
    have hb := setIntegral_mono_set hi (ae_of_all _ (fun r=>a.alpha.val.property.2.deriv_nonneg))
      (ae_of_all _ (fun r hr=>by obtain ⟨p,hp⟩:=mem_iUnion.mp hr;exact hsub p hp))
    exact (hb.trans_eq hmassceil).trans (by
      have HH:=min_le_left (4*v) 1
      dsimp only [ceil]
      linarith [a.data.hs.1])
  have hlower (p:F) : v≤∫r in A p,deriv a.alpha.val.val r := by
    rw [←hscale p]
    exact (actualBroadCapSampler c p.val.1).contracts p.val.2 |>.2.2.2.2.2
  have hs := (Finset.sum_le_sum (s:=Finset.univ) (fun p _=>hlower p)).trans hsum
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  have hc : (F.card:ℝ)≤4 := by
    simpa only [Fintype.card_coe] using (show (Fintype.card F:ℝ)≤(4:ℝ) by nlinarith [hs])
  exact_mod_cast hc

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
