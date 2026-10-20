module

public import ComparisonActualHighWallOuterFloorThermal
public import ComparisonActualHighWallCapThermalAssembly
public import ComparisonActualHighWallStarPreparatory

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000
attribute [local instance] Classical.propDecidable
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
namespace ShiftedCapInterval
variable {a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : a.Potential} (c : ShiftedCapInterval a P)

theorem regular_slab_left_floor (hcl : 0< cl) (hcu : 0< cu) {lo hi : ℝ}
    (hgap : cu*Az*a.xs< lo)
    (htravelLow : a.cavityCapTravel≤ lo/(2*cu))
    (htravelGap : a.cavityCapTravel≤(lo/cu-Az*a.xs)/2)
    (hpoint : ∃r∈Ioo c.left c.right,lo≤ a.alpha.val.val r ∧ a.alpha.val.val r≤ hi) :
    a.z≤ c.left ∧ lo/(2*cu)≤ c.left ∧ (cl/(2*cu))*lo≤ a.alpha.val.val c.left := by
  obtain ⟨r,hr,hrlo,_⟩:=hpoint
  have hrI : r∈Icc a.data.rmin 1:=⟨c.hleft.trans hr.1.le,hr.2.le.trans c.hright⟩
  have HR:=a.actual_mass_slab_radius_lower hcu hgap hrI hrlo
  have HD:=c.travel
  have HG : Az*a.xs< lo/cu:=(lt_div_iff₀ hcu).mpr (by nlinarith only [hgap])
  have hleftz : a.z≤ c.left:=by linarith [a.hzxs,hr.2]
  have hleftlo : lo/(2*cu)≤ c.left:=by
    have HE : lo/(2*cu)=(lo/cu)/2:=by field_simp
    rw [HE] at htravelLow ⊢
    linarith [hr.2]
  refine ⟨hleftz,hleftlo,?_⟩
  have Hreg:=(a.regular c.left ⟨hleftz,c.hlt.le.trans c.hright⟩).1
  have HM:=mul_le_mul_of_nonneg_left hleftlo hcl.le
  have HE : cl*(lo/(2*cu))=(cl/(2*cu))*lo:=by ring
  exact (HE ▸ HM).trans Hreg

theorem regular_slab_right_ratio (hcl : 0< cl) (hcu : 0< cu) {lo hi : ℝ}
    (hgap : cu*Az*a.xs< lo)
    (htravelLow : a.cavityCapTravel≤ lo/(2*cu))
    (htravelGap : a.cavityCapTravel≤(lo/cu-Az*a.xs)/2)
    (hpoint : ∃r∈Ioo c.left c.right,lo≤ a.alpha.val.val r ∧ a.alpha.val.val r≤ hi) :
    a.alpha.val.val c.right≤(2*cu/cl)*a.alpha.val.val c.left := by
  have hf:=c.regular_slab_left_floor hcl hcu hgap htravelLow htravelGap hpoint
  have hlen:=c.travel.trans (htravelLow.trans hf.2.1)
  have HregL:=(a.regular c.left ⟨hf.1,c.hlt.le.trans c.hright⟩).1
  have HregR:=(a.regular c.right ⟨hf.1.trans c.hlt.le,c.hright⟩).2
  have Hrad : c.right≤2*c.left:=by linarith
  have Hradmass : a.alpha.val.val c.right≤(2*cu)*c.left:=by nlinarith
  have HM:=mul_le_mul_of_nonneg_left HregL (show 0≤2*cu/cl by positivity)
  have HE : (2*cu/cl)*(cl*c.left)=2*cu*c.left:=by field_simp
  rw [HE] at HM
  exact Hradmass.trans HM

theorem regular_slab_dyadic_group (hcl : 0< cl) (hcu : 0< cu) {lo hi : ℝ}
    (hgap : cu*Az*a.xs< lo)
    (htravelLow : a.cavityCapTravel≤ lo/(2*cu))
    (htravelGap : a.cavityCapTravel≤(lo/cu-Az*a.xs)/2)
    (hU : comparisonSmallMass a.data.N a.data.E≤(cl/(2*cu))*lo)
    (hpoint : ∃r∈Ioo c.left c.right,lo≤ a.alpha.val.val r ∧ a.alpha.val.val r≤ hi) :
    ∃j : comparisonMassDyadicIndices (comparisonSmallMass a.data.N a.data.E),
      (cl/(4*cu))*lo≤ comparisonSmallMass a.data.N a.data.E*(2:ℝ)^(j:ℕ) ∧
      comparisonSmallMass a.data.N a.data.E*(2:ℝ)^(j:ℕ)≤ hi ∧
      comparisonSmallMass a.data.N a.data.E*(2:ℝ)^(j:ℕ)≤ a.alpha.val.val c.left ∧
      a.alpha.val.val c.right≤ min
        ((4*cu/cl)*(comparisonSmallMass a.data.N a.data.E*(2:ℝ)^(j:ℕ))) 1 := by
  have hf:=(c.regular_slab_left_floor hcl hcu hgap htravelLow htravelGap hpoint).2.2
  have hratio:=c.regular_slab_right_ratio hcl hcu hgap htravelLow htravelGap hpoint
  obtain ⟨r,hr,_,hrhi⟩:=hpoint
  obtain ⟨j,hj,hjNext⟩:=comparison_mass_dyadic_cover a.data.hU (hU.trans hf)
    (a.alpha.val.property.1 c.left).2
  refine ⟨j,?_,hj.trans ((a.alpha.val.property.2 hr.1.le).trans hrhi),hj,?_⟩
  · have H:=hf.trans hjNext.le
    have HE : cl/(4*cu)=cl/(2*cu)/2:=by field_simp;ring
    rw [HE];linarith
  · apply le_min _ (a.alpha.val.property.1 c.right).2
    have HH:=mul_le_mul_of_nonneg_left hjNext.le (show 0≤2*cu/cl by positivity)
    have HE : (2*cu/cl)*(2*(comparisonSmallMass a.data.N a.data.E*(2:ℝ)^(j:ℕ)))=
        (4*cu/cl)*(comparisonSmallMass a.data.N a.data.E*(2:ℝ)^(j:ℕ)):=by ring
    exact hratio.trans (HH.trans_eq HE)

end ShiftedCapInterval

theorem Potential.regular_finite_cap_ordinary_cover
    {a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) {ι : Type*} [Fintype ι] (c : ι→ShiftedCapInterval a P)
    (A : Set ℝ) (hAD : A⊆Ioo a.data.rmin 1)
    {lo hi K : ℝ} (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az)
    (hgap : cu*Az*a.xs< lo)
    (htravelLow : a.cavityCapTravel≤ lo/(2*cu))
    (htravelGap : a.cavityCapTravel≤(lo/cu-Az*a.xs)/2)
    (hU : comparisonSmallMass a.data.N a.data.E≤(cl/(2*cu))*lo)
    (hstart : 2*a.data.s≤(cl/(4*cu))*lo) (hK : 4≤ K) (hKcap : 4*cu/cl≤ K)
    (hscale : ∀r∈A,lo≤ a.alpha.val.val r ∧ a.alpha.val.val r≤ hi) :
    A∩((⋃i,Ioo (c i).left (c i).right)∪P.contactSet)⊆
      ⋃j : LocalShiftedMassDyad a lo hi,P.ordinaryGroup c A K j.val := by
  intro r hr
  rcases hr.2 with hrCap|hrContact
  · obtain ⟨i,hi⟩:=mem_iUnion.mp hrCap
    obtain ⟨j,hjlo,hjhi,hjl,hjr⟩:=(c i).regular_slab_dyadic_group hcl hcu hgap htravelLow htravelGap hU
      ⟨r,hi,(hscale r hr.1).1,(hscale r hr.1).2⟩
    apply mem_iUnion.mpr
    refine ⟨⟨j,hjlo,hjhi⟩,Or.inr (mem_iUnion.mpr ?_)⟩
    refine ⟨⟨i,⟨r,hr.1,hi⟩,hjl,?_⟩,hi⟩
    exact hjr.trans (min_le_min
      (mul_le_mul_of_nonneg_right hKcap (comparison_mass_dyadic_scale a.data.hU j).1.le) le_rfl)
  · have hm:=hscale r hr.1
    have hrI:=hAD hr.1
    have hclcu : cl≤ cu:=by
      have HH:=a.regular 1 ⟨a.hz.2,le_rfl⟩
      simpa only [a.alpha.property.2.1,mul_one] using HH.1.trans HH.2
    have hlo0 : 0< lo:=by
      have H : 0≤ cu*Az*a.xs:=mul_nonneg (mul_nonneg hcu.le hAz) a.hxs.le
      exact H.trans_lt hgap
    have hratio : (cl/(2*cu))*lo≤ lo:=by
      have H : cl/(2*cu)≤1:=(div_le_one (by positivity)).mpr (by linarith)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right H hlo0.le
    obtain ⟨j,hj,hjNext⟩:=comparison_mass_dyadic_cover a.data.hU ((hU.trans hratio).trans hm.1)
      (a.alpha.val.property.1 r).2
    have hjlo : (cl/(4*cu))*lo≤ comparisonSmallMass a.data.N a.data.E*(2:ℝ)^(j:ℕ):=by
      have H : cl/(4*cu)≤(1:ℝ)/2:=(div_le_iff₀ (by positivity)).mpr (by nlinarith)
      have HH:=mul_le_mul_of_nonneg_right H hlo0.le
      linarith
    let v:=comparisonSmallMass a.data.N a.data.E*(2:ℝ)^(j:ℕ)
    have hv:=(comparison_mass_dyadic_scale a.data.hU j).1
    have hvHigh : a.data.s≤ v/2:=by dsimp only [v];linarith [hstart,hjlo]
    have hmHigh : a.alpha.val.val r∈Icc a.data.s 1:=
      (inverseConstraintMap a.alpha ⟨r,Ioo_subset_Icc_self hrI⟩).property
    have hm1 : a.alpha.val.val r<1:=by
      have H:=inverseConstraint_strictMonoOn a.data.hc a.data.hk a.data.hkc a.alpha.property
        (Ioo_subset_Icc_self hrI) ⟨a.data.hr,le_rfl⟩ hrI.2
      simpa only [a.alpha.property.2.1] using H
    have hmin : a.alpha.val.val r< min (K*v) 1:=lt_min (by dsimp only [v] at *;nlinarith) hm1
    have hiHigh : min (K*v) 1∈Icc a.data.s 1:=⟨hmHigh.1.trans hmin.le,min_le_right _ _⟩
    have hloHigh : v/2∈Icc a.data.s 1:=⟨hvHigh,by
      have HH:=(comparison_mass_dyadic_scale a.data.hU j).2.2
      dsimp only [v];linarith⟩
    apply mem_iUnion.mpr
    refine ⟨⟨j,hjlo,hj.trans hm.2⟩,Or.inl ⟨hrContact,?_⟩⟩
    have hInv:=a.shiftedNativeModel.R_inverse (Ioo_subset_Icc_self hrI)
    have hLow:=a.shiftedNativeModel.R_strictMonoOn hloHigh hmHigh
      (show v/2< a.alpha.val.val r by dsimp only [v] at *;linarith)
    have hHigh:=a.shiftedNativeModel.R_strictMonoOn hmHigh hiHigh hmin
    rw [hInv] at hLow hHigh
    exact ⟨hLow,hHigh⟩
theorem Potential.regular_finite_cap_thermal_le_ordinary_sum
    {a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) {ι : Type*} [Fintype ι] (c : ι→ShiftedCapInterval a P)
    (A : Set ℝ) (hA : MeasurableSet A) (hAD : A⊆Ioo a.data.rmin 1)
    {lo hi K : ℝ} (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az)
    (hgap : cu*Az*a.xs< lo)
    (htravelLow : a.cavityCapTravel≤ lo/(2*cu))
    (htravelGap : a.cavityCapTravel≤(lo/cu-Az*a.xs)/2)
    (hU : comparisonSmallMass a.data.N a.data.E≤(cl/(2*cu))*lo)
    (hstart : 2*a.data.s≤(cl/(4*cu))*lo) (hK : 4≤ K) (hKcap : 4*cu/cl≤ K)
    (hscale : ∀r∈A,lo≤ a.alpha.val.val r ∧ a.alpha.val.val r≤ hi) :
    (∫u in 0..1,(A∩((⋃i,Ioo (c i).left (c i).right)∪P.contactSet)).indicator
      (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)≤
      ∑j : LocalShiftedMassDyad a lo hi,∫u in 0..1,(P.ordinaryGroup c A K j.val).indicator
        (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u :=
  a.shiftedNativeModel.thermal_mask_le_finite_cover _
    (hA.inter ((MeasurableSet.iUnion (fun _=>measurableSet_Ioo)).union P.contactSet_measurable)) _
    (fun j=>P.ordinaryGroup_measurable c A K j.val)
    (P.regular_finite_cap_ordinary_cover c A hAD hcl hcu hAz hgap htravelLow htravelGap hU hstart hK hKcap hscale)

theorem Potential.regular_cap_contact_thermal_of_finite_group_budgets
    {a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) (A : Set ℝ) (hA : MeasurableSet A) (hAD : A⊆Ioo a.data.rmin 1)
    {lo hi K O : ℝ} (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az)
    (hgap : cu*Az*a.xs< lo)
    (htravelLow : a.cavityCapTravel≤ lo/(2*cu))
    (htravelGap : a.cavityCapTravel≤(lo/cu-Az*a.xs)/2)
    (hU : comparisonSmallMass a.data.N a.data.E≤(cl/(2*cu))*lo)
    (hstart : 2*a.data.s≤(cl/(4*cu))*lo) (hK : 4≤ K) (hKcap : 4*cu/cl≤ K)
    (hscale : ∀r∈A,lo≤ a.alpha.val.val r ∧ a.alpha.val.val r≤ hi) (hO : 0≤ O)
    (hOrd : ∀F : Finset (ordConnectedSection P.negativeSet),∀j : LocalShiftedMassDyad a lo hi,
      (∫u in 0..1,(P.ordinaryGroup (P.capFamily F) A K j.val).indicator
        (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)≤ O) :
    (∫u in 0..1,(A∩(P.negativeSet∪P.contactSet)).indicator
      (fun _=>1) (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)≤
      O*(Nat.ceil (Real.log (1/comparisonSmallMass a.data.N a.data.E)/Real.log 2)+1) := by
  obtain ⟨F,_,_,hlim⟩:=P.cap_contact_thermal_exhaustion A hA
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro j
  have H:=P.regular_finite_cap_thermal_le_ordinary_sum (P.capFamily (F j)) A hA hAD
    hcl hcu hAz hgap htravelLow htravelGap hU hstart hK hKcap hscale
  have HS:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>hOrd (F j) i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at HS
  have HC : (Fintype.card (LocalShiftedMassDyad a lo hi):ℝ)≤
      Nat.ceil (Real.log (1/comparisonSmallMass a.data.N a.data.E)/Real.log 2)+1:=by
    exact_mod_cast local_mass_dyad_card_le_log a lo hi
  exact H.trans (HS.trans (by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right HC hO))

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
