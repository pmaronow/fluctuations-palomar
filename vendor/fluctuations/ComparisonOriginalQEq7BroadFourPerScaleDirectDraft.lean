module

public import ComparisonOriginalQEq7BroadFourPerScaleBoundaryDraft
public import ComparisonShiftedNativeMassSliceGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum
  (n+1) m delta cl cu Az C0 Ct D Bclock}
variable {P : Q.Potential}

theorem eq7_inner_broad_slice_pairwise_disjoint_direct_draft
    {ι : Type*} [Fintype ι]
    (c : ι → ShiftedCapInterval Q P)
    (hd : Pairwise (fun i j => Disjoint
      (Ioo (c i).left (c i).right)
      (Ioo (c j).left (c j).right))) :
    Pairwise (fun p q : Eq7InnerBroadSliceIndex c =>
      Disjoint (eq7InnerBroadSlice c p) (eq7InnerBroadSlice c q)) := by
  rintro ⟨i,p⟩ ⟨j,q⟩ hpq
  by_cases hij : i=j
  · subst j
    apply (eq7InnerBroadSampler c i).disjoint
    intro he
    apply hpq
    cases he
    rfl
  · have hval : i.val ≠ j.val := fun he => hij (Subtype.ext he)
    exact (hd hval).mono
      ((eq7InnerBroadSampler c i).contracts p).2.2.2.1
      ((eq7InnerBroadSampler c j).contracts q).2.2.2.1

theorem eq7_inner_broad_common_scale_card_le_four_direct_draft
    {ι : Type*} [Fintype ι]
    (c : ι → ShiftedCapInterval Q P)
    (hd : Pairwise (fun i j => Disjoint
      (Ioo (c i).left (c i).right)
      (Ioo (c j).left (c j).right)))
    {v : ℝ} (hv : 0 < v) (hs : Q.data.s ≤ v) :
    (Finset.univ.filter (fun p : Eq7InnerBroadSliceIndex c =>
      (eq7InnerBroadSampler c p.1).scale p.2 = v)).card ≤ 4 := by
  let F := Finset.univ.filter (fun p : Eq7InnerBroadSliceIndex c =>
    (eq7InnerBroadSampler c p.1).scale p.2 = v)
  let ceil := min (4*v) 1
  have hceil : ceil ∈ Icc Q.data.s 1 :=
    ⟨le_min (by linarith) Q.data.hs1,min_le_right _ _⟩
  have hRceil := Q.shiftedNativeModel.R_bounds ceil
  have hscale (p : F) : (eq7InnerBroadSampler c p.val.1).scale p.val.2 = v :=
    (Finset.mem_filter.mp p.property).2
  let A := fun p : F => eq7InnerBroadSlice c p.val
  have hsub (p : F) :
      A p ⊆ Icc Q.data.rmin (Q.shiftedNativeModel.R ceil) := by
    intro r hr
    have hcontracts := (eq7InnerBroadSampler c p.val.1).contracts p.val.2
    have hcap := hcontracts.2.2.2.1 hr
    have hr01 : r ∈ Icc Q.data.rmin 1 :=
      ⟨(c p.val.1.val).hleft.trans hcap.1.le,
        hcap.2.le.trans (c p.val.1.val).hright⟩
    have hmass := hcontracts.2.2.2.2.1 r hr
    have hceiling := hcontracts.2.2.1
    have hmass4 : Q.alpha.val.val r ≤ 4*v := by
      rw [←hscale p]
      exact hmass.trans hceiling
    have hmassceil : Q.alpha.val.val r ≤ ceil :=
      le_min hmass4 (Q.alpha.val.property.1 r).2
    have hradius := Q.shiftedNativeModel.R_monotone hmassceil
    rw [Q.shiftedNativeModel.R_inverse hr01] at hradius
    exact ⟨hr01.1,hradius⟩
  have hi := Q.shiftedNativeModel.inverse_derivative_unit_mass.1.mono_set
    (Icc_subset_Icc le_rfl hRceil.2)
  have hmassceil :
      (∫r in Icc Q.data.rmin (Q.shiftedNativeModel.R ceil),
        deriv Q.alpha.val.val r) = ceil-Q.data.s := by
    rw [integral_Icc_eq_integral_Ioc,integral_Ioc_eq_integral_Ioo,
      Q.shiftedNativeModel.inverse_slice_mass
        (show Q.data.rmin ∈ Icc Q.shiftedNativeModel.rmin 1 from
          ⟨le_rfl,Q.data.hr⟩) hRceil hRceil.1,
      Q.shiftedNativeModel.R_spec hceil,Q.alpha.property.1]
  have hdisjoint : Pairwise (fun p q : F => Disjoint (A p) (A q)) := by
    intro p q hpq
    exact eq7_inner_broad_slice_pairwise_disjoint_direct_draft c hd
      (fun he => hpq (Subtype.ext he))
  have hsum : (∑p : F,∫r in A p,deriv Q.alpha.val.val r) ≤ 4*v := by
    have heq :
        (∫r in ⋃p : F,A p,deriv Q.alpha.val.val r) =
          ∑p : F,∫r in A p,deriv Q.alpha.val.val r :=
      integral_iUnion_fintype (s:=A) (fun _ => measurableSet_Ioo)
        hdisjoint (fun p => hi.mono_set (hsub p))
    rw [←heq]
    have hb := setIntegral_mono_set hi
      (ae_of_all _ (fun r => Q.alpha.val.property.2.deriv_nonneg))
      (ae_of_all _ (fun r hr => by
        obtain ⟨p,hp⟩ := mem_iUnion.mp hr
        exact hsub p hp))
    exact (hb.trans_eq hmassceil).trans (by
      have HH := min_le_left (4*v) 1
      dsimp only [ceil]
      linarith [Q.data.hs.1])
  have hlower (p : F) :
      v ≤ ∫r in A p,deriv Q.alpha.val.val r := by
    rw [←hscale p]
    exact (eq7InnerBroadSampler c p.val.1).contracts p.val.2 |>.2.2.2.2.2
  have hs' := (Finset.sum_le_sum (s:=Finset.univ)
    (fun p _ => hlower p)).trans hsum
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs'
  have hc : (F.card:ℝ) ≤ 4 := by
    simpa only [Fintype.card_coe] using
      (show (Fintype.card F:ℝ) ≤ (4:ℝ) by nlinarith [hs'])
  exact_mod_cast hc

theorem eq7_inner_broad_four_per_scale_direct_draft
    {ι : Type*} [Fintype ι]
    (c : ι → ShiftedCapInterval Q P)
    (hd : Pairwise (fun i j => Disjoint
      (Ioo (c i).left (c i).right)
      (Ioo (c j).left (c j).right))) :
    Eq7InnerBroadFourPerScale c := by
  intro v hv hs
  exact eq7_inner_broad_common_scale_card_le_four_direct_draft
    c hd hv hs

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
