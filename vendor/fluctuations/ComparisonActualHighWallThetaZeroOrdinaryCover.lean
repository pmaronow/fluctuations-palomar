module

public import ComparisonActualHighWallThetaZeroCapCoverGeometry
public import ComparisonActualHighWallOrdinaryCover

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

abbrev LocalShiftedMassDyad
    (Q : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) (lo hi : ℝ):=
  {j : comparisonMassDyadicIndices (comparisonSmallMass Q.data.N Q.data.E) //
    (cl/(4*cu))*lo≤ comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j.val:ℕ) ∧
      comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j.val:ℕ)≤ hi}

def Potential.ordinaryGroup
    {Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (P : Q.Potential) {ι : Type*} (c : ι→ShiftedCapInterval Q P) (A : Set ℝ)
    (K : ℝ) (j : comparisonMassDyadicIndices (comparisonSmallMass Q.data.N Q.data.E)) : Set ℝ:=
  let v:=comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j:ℕ)
  (P.contactSet∩Q.shiftedNativeModel.massSlice (v/2) (min (K*v) 1)) ∪
    ⋃i : {i : ι // (A∩Ioo (c i).left (c i).right).Nonempty ∧
      v≤ Q.alpha.val.val (c i).left ∧ Q.alpha.val.val (c i).right≤ min (K*v) 1},
      Ioo (c i.val).left (c i.val).right

theorem Potential.ordinaryGroup_measurable
    {Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (P : Q.Potential) {ι : Type*} [Fintype ι] (c : ι→ShiftedCapInterval Q P) (A : Set ℝ)
    (K : ℝ) (j : comparisonMassDyadicIndices (comparisonSmallMass Q.data.N Q.data.E)) :
    MeasurableSet (P.ordinaryGroup c A K j) :=
  (P.contactSet_measurable.inter measurableSet_Ioo).union
    (MeasurableSet.iUnion (fun _=>measurableSet_Ioo))

theorem Potential.outer_finite_cap_ordinary_cover
    {Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (P : Q.Potential) {ι : Type*} [Fintype ι] (c : ι→ShiftedCapInterval Q P)
    (A : Set ℝ) (hAD : A⊆Ioo Q.data.rmin 1)
    {lo hi K : ℝ} (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az)
    (htravel : Q.cavityCapTravel≤ Q.xs) (houter : 2*cu*(Az+1)*Q.xs≤ lo)
    (hU : comparisonSmallMass Q.data.N Q.data.E≤(cl/(2*cu))*lo)
    (hstart : 2*Q.data.s≤(cl/(4*cu))*lo) (hK : 4≤ K) (hKcap : 4*cu/cl≤ K)
    (hscale : ∀r∈A,lo≤ Q.alpha.val.val r ∧ Q.alpha.val.val r≤ hi) :
    A∩((⋃i,Ioo (c i).left (c i).right)∪P.contactSet)⊆
      ⋃j : LocalShiftedMassDyad Q lo hi,P.ordinaryGroup c A K j.val := by
  intro r hr
  rcases hr.2 with hrCap|hrContact
  · obtain ⟨i,hi⟩:=mem_iUnion.mp hrCap
    obtain ⟨j,hjlo,hjhi,hjl,hjr⟩:=(c i).outer_dyadic_group hcl hcu hAz htravel houter hU
      ⟨r,hi,(hscale r hr.1).1,(hscale r hr.1).2⟩
    apply mem_iUnion.mpr
    refine ⟨⟨j,hjlo,hjhi⟩,Or.inr (mem_iUnion.mpr ?_)⟩
    refine ⟨⟨i,⟨r,hr.1,hi⟩,hjl,?_⟩,hi⟩
    exact hjr.trans (min_le_min
      (mul_le_mul_of_nonneg_right hKcap (comparison_mass_dyadic_scale Q.data.hU j).1.le) le_rfl)
  · have hm:=hscale r hr.1
    have hrI:=hAD hr.1
    have hclcu : cl≤ cu:=by
      have HH:=Q.regular 1 ⟨Q.hz.2,le_rfl⟩
      simpa only [Q.alpha.property.2.1,mul_one] using HH.1.trans HH.2
    have hlo0 : 0< lo:=by
      have H : 0<2*cu*(Az+1)*Q.xs:=
        mul_pos (mul_pos (mul_pos (by norm_num) hcu) (by linarith)) Q.hxs
      exact H.trans_le houter
    have hratio : (cl/(2*cu))*lo≤ lo:=by
      have H : cl/(2*cu)≤1:=(div_le_one (by positivity)).mpr (by linarith)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right H hlo0.le
    obtain ⟨j,hj,hjNext⟩:=comparison_mass_dyadic_cover Q.data.hU ((hU.trans hratio).trans hm.1)
      (Q.alpha.val.property.1 r).2
    have hjlo : (cl/(4*cu))*lo≤ comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j:ℕ):=by
      have H : cl/(4*cu)≤(1:ℝ)/2:=(div_le_iff₀ (by positivity)).mpr (by nlinarith)
      have HH:=mul_le_mul_of_nonneg_right H hlo0.le
      linarith
    let v:=comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j:ℕ)
    have hv:=(comparison_mass_dyadic_scale Q.data.hU j).1
    have hvHigh : Q.data.s≤ v/2:=by dsimp only [v];linarith [hstart,hjlo]
    have hmHigh : Q.alpha.val.val r∈Icc Q.data.s 1:=
      (inverseConstraintMap Q.alpha ⟨r,Ioo_subset_Icc_self hrI⟩).property
    have hm1 : Q.alpha.val.val r<1:=by
      have H:=inverseConstraint_strictMonoOn Q.data.hc Q.data.hk Q.data.hkc Q.alpha.property
        (Ioo_subset_Icc_self hrI) ⟨Q.data.hr,le_rfl⟩ hrI.2
      simpa only [Q.alpha.property.2.1] using H
    have hmin : Q.alpha.val.val r< min (K*v) 1:=lt_min (by dsimp only [v] at *;nlinarith) hm1
    have hiHigh : min (K*v) 1∈Icc Q.data.s 1:=⟨hmHigh.1.trans hmin.le,min_le_right _ _⟩
    have hloHigh : v/2∈Icc Q.data.s 1:=⟨hvHigh,by
      have HH:=(comparison_mass_dyadic_scale Q.data.hU j).2.2
      dsimp only [v];linarith⟩
    apply mem_iUnion.mpr
    refine ⟨⟨j,hjlo,hj.trans hm.2⟩,Or.inl ⟨hrContact,?_⟩⟩
    have hInv:=Q.shiftedNativeModel.R_inverse (Ioo_subset_Icc_self hrI)
    have hLow:=Q.shiftedNativeModel.R_strictMonoOn hloHigh hmHigh
      (show v/2< Q.alpha.val.val r by dsimp only [v] at *;linarith)
    have hHigh:=Q.shiftedNativeModel.R_strictMonoOn hmHigh hiHigh hmin
    rw [hInv] at hLow hHigh
    exact ⟨hLow,hHigh⟩

theorem Potential.outer_finite_cap_thermal_le_ordinary_sum
    {Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (P : Q.Potential) {ι : Type*} [Fintype ι] (c : ι→ShiftedCapInterval Q P)
    (A : Set ℝ) (hA : MeasurableSet A) (hAD : A⊆Ioo Q.data.rmin 1)
    {lo hi K : ℝ} (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az)
    (htravel : Q.cavityCapTravel≤ Q.xs) (houter : 2*cu*(Az+1)*Q.xs≤ lo)
    (hU : comparisonSmallMass Q.data.N Q.data.E≤(cl/(2*cu))*lo)
    (hstart : 2*Q.data.s≤(cl/(4*cu))*lo) (hK : 4≤ K) (hKcap : 4*cu/cl≤ K)
    (hscale : ∀r∈A,lo≤ Q.alpha.val.val r ∧ Q.alpha.val.val r≤ hi) :
    (∫u in 0..1,(A∩((⋃i,Ioo (c i).left (c i).right)∪P.contactSet)).indicator
      (fun _=>1) (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u)≤
      ∑j : LocalShiftedMassDyad Q lo hi,∫u in 0..1,(P.ordinaryGroup c A K j.val).indicator
        (fun _=>1) (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u :=
  Q.shiftedNativeModel.thermal_mask_le_finite_cover _
    (hA.inter ((MeasurableSet.iUnion (fun _=>measurableSet_Ioo)).union P.contactSet_measurable)) _
    (fun j=>P.ordinaryGroup_measurable c A K j.val)
    (P.outer_finite_cap_ordinary_cover c A hAD hcl hcu hAz htravel houter hU hstart hK hKcap hscale)

end ActualThetaZeroOverlapMinimum

end OAI.SKFluctuations.LaplaceWindowFormalization
