module

public import ComparisonActualHighWallThetaZeroCapTravelCore
public import ComparisonActualHighWallThetaZeroCapComponents
public import ComparisonNativeWholeCapDyadicCover

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

namespace ShiftedCapInterval
variable {Q : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock}
    {P : Q.Potential} (c : ShiftedCapInterval Q P)

theorem travel : c.right-c.left≤ Q.cavityCapTravel :=
  (P.cap_interval_travel Q c.hleft c.hlt.le c.hright c.negative).2.1

theorem endpoint_mass_envelope (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az)
    (htravel : Q.cavityCapTravel≤ Q.xs) :
    Q.alpha.val.val c.right≤ cu*(Q.alpha.val.val c.left/cl+(Az+1)*Q.xs) := by
  have hlen:=c.travel.trans htravel
  have ha0:= (Q.alpha.val.property.1 c.left).1
  have hmax : Q.alpha.val.val c.right≤ cu*(max c.left Q.z+Q.xs):=by
    by_cases hz:Q.z≤ c.right
    · have hr:=(Q.regular c.right ⟨hz,c.hright⟩).2
      exact hr.trans (mul_le_mul_of_nonneg_left
        (show c.right≤ max c.left Q.z+Q.xs by linarith [le_max_left c.left Q.z]) hcu.le)
    · have hr:=Q.alpha.val.property.2 (le_of_not_ge hz)
      have hp:=(Q.regular Q.z ⟨le_rfl,Q.hz.2⟩).2
      exact (hr.trans hp).trans (mul_le_mul_of_nonneg_left
        (show Q.z≤ max c.left Q.z+Q.xs by linarith [le_max_right c.left Q.z,Q.hxs]) hcu.le)
  have hrad : max c.left Q.z≤ Q.alpha.val.val c.left/cl+Az*Q.xs:=by
    by_cases hz:Q.z≤ c.left
    · rw [max_eq_left hz]
      have hp:=(Q.regular c.left ⟨hz,c.hlt.le.trans c.hright⟩).1
      have HH : c.left≤ Q.alpha.val.val c.left/cl:=(le_div_iff₀ hcl).mpr
        (by simpa only [mul_comm] using hp)
      exact HH.trans (le_add_of_nonneg_right (mul_nonneg hAz Q.hxs.le))
    · rw [max_eq_right (le_of_not_ge hz)]
      exact Q.hzxs.trans (le_add_of_nonneg_left (div_nonneg ha0 hcl.le))
  exact hmax.trans (mul_le_mul_of_nonneg_left
    (by linarith : max c.left Q.z+Q.xs≤ Q.alpha.val.val c.left/cl+(Az+1)*Q.xs) hcu.le)

theorem outer_mass_floor (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az)
    (htravel : Q.cavityCapTravel≤ Q.xs)
    (houter : 2*cu*(Az+1)*Q.xs≤ Q.alpha.val.val c.right) :
    (cl/(2*cu))*Q.alpha.val.val c.right≤ Q.alpha.val.val c.left := by
  have H:=c.endpoint_mass_envelope hcl hcu hAz htravel
  have HH : Q.alpha.val.val c.right≤2*cu*(Q.alpha.val.val c.left/cl):=by nlinarith
  have hp:=mul_le_mul_of_nonneg_right HH hcl.le
  rw [mul_assoc,div_mul_cancel₀ _ hcl.ne'] at hp
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ (mul_pos (by norm_num) hcu)).mpr (by nlinarith)

theorem outer_dyadic_group (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az)
    (htravel : Q.cavityCapTravel≤ Q.xs) {lo hi : ℝ}
    (houter : 2*cu*(Az+1)*Q.xs≤ lo)
    (hU : comparisonSmallMass Q.data.N Q.data.E≤(cl/(2*cu))*lo)
    (hpoint : ∃r∈Ioo c.left c.right,lo≤ Q.alpha.val.val r ∧ Q.alpha.val.val r≤ hi) :
    ∃j : comparisonMassDyadicIndices (comparisonSmallMass Q.data.N Q.data.E),
      (cl/(4*cu))*lo≤ comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j:ℕ) ∧
      comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j:ℕ)≤ hi ∧
      comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j:ℕ)≤ Q.alpha.val.val c.left ∧
      Q.alpha.val.val c.right≤ min
        ((4*cu/cl)*(comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j:ℕ))) 1 := by
  obtain ⟨r,hr,hrlo,hrhi⟩:=hpoint
  have hright : lo≤ Q.alpha.val.val c.right:=hrlo.trans (Q.alpha.val.property.2 hr.2.le)
  have hfloor:=c.outer_mass_floor hcl hcu hAz htravel (houter.trans hright)
  have hUA : comparisonSmallMass Q.data.N Q.data.E≤ Q.alpha.val.val c.left:=
    hU.trans ((mul_le_mul_of_nonneg_left hright (by positivity : 0≤ cl/(2*cu))).trans hfloor)
  obtain ⟨j,hj,hjNext⟩:=comparison_mass_dyadic_cover Q.data.hU hUA (Q.alpha.val.property.1 c.left).2
  refine ⟨j,?_,hj.trans ((Q.alpha.val.property.2 hr.1.le).trans hrhi),hj,?_⟩
  · have H:=(mul_le_mul_of_nonneg_left hright (show 0≤ cl/(2*cu) from by positivity)).trans hfloor
    have H2:=H.trans hjNext.le
    have hcoef : cl/(4*cu)=cl/(2*cu)/2:=by field_simp;ring
    rw [hcoef]
    nlinarith
  · apply le_min _ (Q.alpha.val.property.1 c.right).2
    have H : Q.alpha.val.val c.right≤ Q.alpha.val.val c.left/(cl/(2*cu)):=
      (le_div_iff₀ (by positivity : 0< cl/(2*cu))).mpr (by simpa only [mul_comm] using hfloor)
    have H2:=div_le_div_of_nonneg_right hjNext.le (show 0≤ cl/(2*cu) from by positivity)
    apply H.trans
    convert H2 using 1
    field_simp [hcl.ne',hcu.ne']
    ring

end ShiftedCapInterval

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
