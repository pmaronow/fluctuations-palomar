module

public import ComparisonShiftedNativeThermalGeometry
public import ComparisonNativeWholeCapDyadicCover
public import ComparisonNativeDyadicContactCover
public import ComparisonActualHighWallContactGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

def Potential.negativeSet
    {a : ActualHighWallOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) : Set ℝ:=Ioo a.data.rmin 1∩P.H ⁻¹' Iio 0

def Potential.contactSet
    {a : ActualHighWallOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) : Set ℝ:=Icc a.data.rmin 1∩P.H ⁻¹' {0}

theorem Potential.negativeSet_open
    {a : ActualHighWallOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) : IsOpen P.negativeSet := by
  have hc : ContinuousOn P.H (Icc a.data.rmin 1):=by
    simpa only [uIcc_of_le a.data.hr] using P.hH.continuousOn
  exact (hc.mono Ioo_subset_Icc_self).isOpen_inter_preimage isOpen_Ioo isOpen_Iio

theorem Potential.negativeSet_subset
    {a : ActualHighWallOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) : P.negativeSet⊆Icc a.data.rmin 1 :=
  inter_subset_left.trans Ioo_subset_Icc_self

theorem Potential.contactSet_measurable
    {a : ActualHighWallOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) : MeasurableSet P.contactSet := by
  have hc : ContinuousOn P.H (Icc a.data.rmin 1):=by
    simpa only [uIcc_of_le a.data.hr] using P.hH.continuousOn
  exact (hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton).measurableSet

structure ShiftedCapInterval
    (a : ActualHighWallOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock)
    (P : a.Potential) where
  left : ℝ
  right : ℝ
  hleft : a.data.rmin≤ left
  hlt : left< right
  hright : right≤1
  negative : ∀r∈Ioo left right,P.H r<0

theorem Potential.negative_component_endpoints
    {a : ActualHighWallOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) {r : ℝ} (hr : r∈P.negativeSet) :
    let C:=ordConnectedComponent P.negativeSet r
    ∃c : ShiftedCapInterval a P,c.left=sInf C ∧ c.right=sSup C ∧ Ioo c.left c.right=C ∧
      (P.H c.left=0 ∨ c.left=a.data.rmin) ∧ (P.H c.right=0 ∨ c.right=1) := by
  dsimp only
  let C:=ordConnectedComponent P.negativeSet r
  have hp:=wholeCap_component_endpoints P.negativeSet_open P.negativeSet_subset hr
  have hC : C=Ioo (sInf C) (sSup C):=hp.2.2.2.2.1
  have hnon : C.Nonempty:=nonempty_ordConnectedComponent.mpr hr
  have hsub : C⊆Icc a.data.rmin 1:=ordConnectedComponent_subset.trans P.negativeSet_subset
  have hc : ContinuousOn P.H (Icc a.data.rmin 1):=by
    simpa only [uIcc_of_le a.data.hr] using P.hH.continuousOn
  have hclosed : IsClosed (Icc a.data.rmin 1∩P.H ⁻¹' Iic 0):=
    hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hCsub : C⊆Icc a.data.rmin 1∩P.H ⁻¹' Iic 0:=by
    intro t ht
    have H : P.H t<0:=(ordConnectedComponent_subset ht).2
    exact ⟨hsub ht,H.le⟩
  have hlo : BddBelow C:=⟨a.data.rmin,fun t ht=>(hsub ht).1⟩
  have hhi : BddAbove C:=⟨1,fun t ht=>(hsub ht).2⟩
  have hleft0 : P.H (sInf C)≤0:=
    (hclosed.closure_subset_iff.mpr hCsub (csInf_mem_closure hnon hlo)).2
  have hright0 : P.H (sSup C)≤0:=
    (hclosed.closure_subset_iff.mpr hCsub (csSup_mem_closure hnon hhi)).2
  have hleft : P.H (sInf C)=0 ∨ sInf C=a.data.rmin:=by
    by_cases hl:sInf C=a.data.rmin
    · exact Or.inr hl
    · apply Or.inl
      apply le_antisymm hleft0
      by_contra hbad
      have ht : sInf C∈P.negativeSet:=
        ⟨⟨lt_of_le_of_ne hp.1 (fun he=>hl he.symm),
          (hp.2.1.trans hp.2.2.1).trans_le hp.2.2.2.1⟩,lt_of_not_ge hbad⟩
      exact hp.2.2.2.2.2.1 ht
  have hright : P.H (sSup C)=0 ∨ sSup C=1:=by
    by_cases hz:sSup C=1
    · exact Or.inr hz
    · apply Or.inl
      apply le_antisymm hright0
      by_contra hbad
      have ht : sSup C∈P.negativeSet:=
        ⟨⟨hp.1.trans_lt (hp.2.1.trans hp.2.2.1),lt_of_le_of_ne hp.2.2.2.1 hz⟩,lt_of_not_ge hbad⟩
      exact hp.2.2.2.2.2.2 ht
  let c : ShiftedCapInterval a P:={
    left:=sInf C
    right:=sSup C
    hleft:=hp.1
    hlt:=hp.2.1.trans hp.2.2.1
    hright:=hp.2.2.2.1
    negative:=fun t ht=>(ordConnectedComponent_subset (hC.symm ▸ ht)).2 }
  exact ⟨c,rfl,rfl,hC.symm,hleft,hright⟩

namespace ShiftedCapInterval
variable {a : ActualHighWallOverlapMinimum n margin delta cl cu Az C0 Ct D Bclock}
    {P : a.Potential} (c : ShiftedCapInterval a P)

theorem travel : c.right-c.left≤ a.cavityCapTravel :=
  (P.cap_interval_travel c.hleft c.hlt.le c.hright c.negative).2.1

theorem endpoint_mass_envelope (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az)
    (htravel : a.cavityCapTravel≤ a.xs) :
    a.alpha.val.val c.right≤ cu*(a.alpha.val.val c.left/cl+(Az+1)*a.xs) := by
  have hlen:=c.travel.trans htravel
  have ha0:= (a.alpha.val.property.1 c.left).1
  have hmax : a.alpha.val.val c.right≤ cu*(max c.left a.z+a.xs):=by
    by_cases hz:a.z≤ c.right
    · have hr:=(a.regular c.right ⟨hz,c.hright⟩).2
      exact hr.trans (mul_le_mul_of_nonneg_left
        (show c.right≤ max c.left a.z+a.xs by linarith [le_max_left c.left a.z]) hcu.le)
    · have hr:=a.alpha.val.property.2 (le_of_not_ge hz)
      have hp:=(a.regular a.z ⟨le_rfl,a.hz.2⟩).2
      exact (hr.trans hp).trans (mul_le_mul_of_nonneg_left
        (show a.z≤ max c.left a.z+a.xs by linarith [le_max_right c.left a.z,a.hxs]) hcu.le)
  have hrad : max c.left a.z≤ a.alpha.val.val c.left/cl+Az*a.xs:=by
    by_cases hz:a.z≤ c.left
    · rw [max_eq_left hz]
      have hp:=(a.regular c.left ⟨hz,c.hlt.le.trans c.hright⟩).1
      have HH : c.left≤ a.alpha.val.val c.left/cl:=(le_div_iff₀ hcl).mpr
        (by simpa only [mul_comm] using hp)
      exact HH.trans (le_add_of_nonneg_right (mul_nonneg hAz a.hxs.le))
    · rw [max_eq_right (le_of_not_ge hz)]
      exact a.hzxs.trans (le_add_of_nonneg_left (div_nonneg ha0 hcl.le))
  exact hmax.trans (mul_le_mul_of_nonneg_left
    (by linarith : max c.left a.z+a.xs≤ a.alpha.val.val c.left/cl+(Az+1)*a.xs) hcu.le)

theorem outer_mass_floor (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az)
    (htravel : a.cavityCapTravel≤ a.xs)
    (houter : 2*cu*(Az+1)*a.xs≤ a.alpha.val.val c.right) :
    (cl/(2*cu))*a.alpha.val.val c.right≤ a.alpha.val.val c.left := by
  have H:=c.endpoint_mass_envelope hcl hcu hAz htravel
  have HH : a.alpha.val.val c.right≤2*cu*(a.alpha.val.val c.left/cl):=by nlinarith
  have hp:=mul_le_mul_of_nonneg_right HH hcl.le
  rw [mul_assoc,div_mul_cancel₀ _ hcl.ne'] at hp
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ (mul_pos (by norm_num) hcu)).mpr (by nlinarith)

theorem outer_dyadic_group (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az)
    (htravel : a.cavityCapTravel≤ a.xs) {lo hi : ℝ}
    (houter : 2*cu*(Az+1)*a.xs≤ lo)
    (hU : comparisonSmallMass a.data.N a.data.E≤(cl/(2*cu))*lo)
    (hpoint : ∃r∈Ioo c.left c.right,lo≤ a.alpha.val.val r ∧ a.alpha.val.val r≤ hi) :
    ∃j : comparisonMassDyadicIndices (comparisonSmallMass a.data.N a.data.E),
      (cl/(4*cu))*lo≤ comparisonSmallMass a.data.N a.data.E*(2:ℝ)^(j:ℕ) ∧
      comparisonSmallMass a.data.N a.data.E*(2:ℝ)^(j:ℕ)≤ hi ∧
      comparisonSmallMass a.data.N a.data.E*(2:ℝ)^(j:ℕ)≤ a.alpha.val.val c.left ∧
      a.alpha.val.val c.right≤ min
        ((4*cu/cl)*(comparisonSmallMass a.data.N a.data.E*(2:ℝ)^(j:ℕ))) 1 := by
  obtain ⟨r,hr,hrlo,hrhi⟩:=hpoint
  have hright : lo≤ a.alpha.val.val c.right:=hrlo.trans (a.alpha.val.property.2 hr.2.le)
  have hfloor:=c.outer_mass_floor hcl hcu hAz htravel (houter.trans hright)
  have hUA : comparisonSmallMass a.data.N a.data.E≤ a.alpha.val.val c.left:=
    hU.trans ((mul_le_mul_of_nonneg_left hright (by positivity : 0≤ cl/(2*cu))).trans hfloor)
  obtain ⟨j,hj,hjNext⟩:=comparison_mass_dyadic_cover a.data.hU hUA (a.alpha.val.property.1 c.left).2
  refine ⟨j,?_,hj.trans ((a.alpha.val.property.2 hr.1.le).trans hrhi),hj,?_⟩
  · have H:=(mul_le_mul_of_nonneg_left hright (show 0≤ cl/(2*cu) from by positivity)).trans hfloor
    have H2:=H.trans hjNext.le
    have hcoef : cl/(4*cu)=cl/(2*cu)/2:=by field_simp;ring
    rw [hcoef]
    nlinarith
  · apply le_min _ (a.alpha.val.property.1 c.right).2
    have H : a.alpha.val.val c.right≤ a.alpha.val.val c.left/(cl/(2*cu)):=
      (le_div_iff₀ (by positivity : 0< cl/(2*cu))).mpr (by simpa only [mul_comm] using hfloor)
    have H2:=div_le_div_of_nonneg_right hjNext.le (show 0≤ cl/(2*cu) from by positivity)
    apply H.trans
    convert H2 using 1
    field_simp [hcl.ne',hcu.ne']
    ring

end ShiftedCapInterval
end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
