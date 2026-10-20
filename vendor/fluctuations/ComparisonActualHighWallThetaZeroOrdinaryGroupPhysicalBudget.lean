module

public import ComparisonActualHighWallThetaZeroOrdinaryPhysicalBudget
public import ComparisonActualHighWallThetaZeroOrdinaryCover
public import ComparisonActualHighWallThetaZeroRetainedRowsBasics
public import ComparisonActualHighWallThetaZeroCapExhaustion

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 32000000
attribute [local instance] Classical.propDecidable

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

abbrev Potential.ordinaryCapIndex (P : Q.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval Q P) (A : Set ℝ) (K : ℝ)
    (j : comparisonMassDyadicIndices (comparisonSmallMass Q.data.N Q.data.E)) :=
  let v:=comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j:ℕ)
  {i : ι // (A∩Ioo (c i).left (c i).right).Nonempty ∧
    v ≤ Q.alpha.val.val (c i).left ∧ Q.alpha.val.val (c i).right ≤ min (K*v) 1}

abbrev Potential.ordinaryCapSubfamily (P : Q.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval Q P) (A : Set ℝ) (K : ℝ)
    (j : comparisonMassDyadicIndices (comparisonSmallMass Q.data.N Q.data.E))
    (i : P.ordinaryCapIndex c A K j) : ShiftedCapInterval Q P := c i.val

theorem Potential.ordinaryGroup_eq_retainedSupport (P : Q.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval Q P) (A : Set ℝ) (K : ℝ)
    (j : comparisonMassDyadicIndices (comparisonSmallMass Q.data.N Q.data.E)) :
    P.ordinaryGroup c A K j=
      P.retainedSupport (P.ordinaryCapSubfamily c A K j)
        (Q.shiftedNativeModel.R ((comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j:ℕ))/2))
        (Q.shiftedNativeModel.R (min (K*(comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j:ℕ))) 1)) := by
  let v:=comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j:ℕ)
  let ag:=Q.shiftedNativeModel.R (v/2)
  let zg:=Q.shiftedNativeModel.R (min (K*v) 1)
  have hv : 0 < v:=(comparison_mass_dyadic_scale Q.data.hU j).1
  have Hleft (i : P.ordinaryCapIndex c A K j) : ag ≤ (c i.val).left := by
    have Hmass : v/2 ≤ Q.alpha.val.val (c i.val).left:=by
      have H:=i.property.2.1
      change v ≤ _ at H
      linarith
    have H:=Q.shiftedNativeModel.R_monotone Hmass
    rw [Q.shiftedNativeModel.R_inverse ⟨(c i.val).hleft,(c i.val).hlt.le.trans (c i.val).hright⟩] at H
    exact H
  have Hright (i : P.ordinaryCapIndex c A K j) : (c i.val).right ≤ zg := by
    have H:=Q.shiftedNativeModel.R_monotone i.property.2.2
    rw [Q.shiftedNativeModel.R_inverse ⟨(c i.val).hleft.trans (c i.val).hlt.le,(c i.val).hright⟩] at H
    exact H
  ext r
  change ((r∈P.contactSet∧r∈Ioo ag zg) ∨
    r∈⋃i : P.ordinaryCapIndex c A K j,Ioo (c i.val).left (c i.val).right) ↔
      r∈Ioo ag zg ∧ ((∃i : P.ordinaryCapIndex c A K j,
        r∈Ioo (c i.val).left (c i.val).right) ∨ P.H r=0)
  constructor
  · intro hr
    rcases hr with hr|hr
    · exact ⟨hr.2,Or.inr hr.1.2⟩
    · obtain ⟨i,hi⟩:=mem_iUnion.mp hr
      exact ⟨⟨(Hleft i).trans_lt hi.1,hi.2.trans_le (Hright i)⟩,Or.inl ⟨i,hi⟩⟩
  · rintro ⟨hr,hrCap|hrContact⟩
    · exact Or.inr (mem_iUnion.mpr hrCap)
    · have hrI : r∈Icc Q.data.rmin 1:=⟨
        (Q.shiftedNativeModel.R_bounds (v/2)).1.trans hr.1.le,
        hr.2.le.trans (Q.shiftedNativeModel.R_bounds (min (K*v) 1)).2⟩
      exact Or.inl ⟨⟨hrI,hrContact⟩,hr⟩

end ActualThetaZeroOverlapMinimum

 theorem eventually_actual_theta_zero_ordinary_group_optimized_budget
    (ell : ℕ) (hell : 2 < ell) (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Qraw : ℝ,1 ≤ Qraw ∧ ∀ᶠn : ℕ in atTop,
      ∀(Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (P : Q.Potential) (F : Finset (ordConnectedSection P.negativeSet))
        (A : Set ℝ) (K : ℝ)
        (j : comparisonMassDyadicIndices (comparisonSmallMass Q.data.N Q.data.E))
        (Lside cut : ℝ),
        4 ≤ K → Q.data.s < (comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j:ℕ))/2 →
        K*(comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j:ℕ)) ≤ 1 →
        0 ≤ Lside → 0 < cut → Real.log (1/cut) ≤ Lside →
        let v:=comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j:ℕ)
        let zg:=Q.shiftedNativeModel.R (K*v)
        (∫u in 0..1,(P.ordinaryGroup (P.capFamily F) A K j).indicator
          (fun _=>1) (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u) ≤ 
          Q.ordinaryOptimizedBudget ell Qraw K Lside cut (K*v) (v/2)
            (Q.xs+K*v) v K zg := by
  obtain ⟨Qraw,hQraw,Hphysical⟩:=eventually_actual_theta_zero_ordinary_optimized_budget ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Qraw,hQraw,?_⟩
  filter_upwards [Hphysical] with n hn
  intro Q P F A K j Lside cut hK hstart hKv hLside hcut hlogcut
  let v:=comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j:ℕ)
  let ag:=Q.shiftedNativeModel.R (v/2)
  let zg:=Q.shiftedNativeModel.R (K*v)
  let c:=P.ordinaryCapSubfamily (P.capFamily F) A K j
  have hv : 0 < v:=(comparison_mass_dyadic_scale Q.data.hU j).1
  have hKpos : 0 < K:=by linarith
  have hK1 : 1 ≤ K:=by linarith
  have hvKv : v ≤ K*v:=by nlinarith
  have hlow : v/2∈Icc Q.data.s 1:=⟨hstart.le,by linarith⟩
  have hhigh : K*v∈Icc Q.data.s 1:=⟨by linarith [Q.data.hs.1],hKv⟩
  have Hlow:=Q.shiftedNativeModel.R_spec hlow
  have Hhigh:=Q.shiftedNativeModel.R_spec hhigh
  have hag : Q.data.rmin < ag:=by
    have H:=Q.shiftedNativeModel.R_strictMonoOn ⟨le_rfl,Q.data.hs1⟩ hlow hstart
    rw [Q.shiftedNativeModel.R_left] at H
    exact H
  have hagz : ag ≤ zg:=Q.shiftedNativeModel.R_monotone (by linarith : v/2 ≤ K*v)
  have hzg : zg ≤ 1:=(Q.shiftedNativeModel.R_bounds (K*v)).2
  have Hleft (t : P.ordinaryCapIndex (P.capFamily F) A K j) : ag ≤ (c t).left:=by
    have Hmass : v/2 ≤ Q.alpha.val.val (c t).left:=by
      have H:=t.property.2.1
      change v ≤ Q.alpha.val.val (c t).left at H
      linarith
    have H:=Q.shiftedNativeModel.R_monotone Hmass
    rw [Q.shiftedNativeModel.R_inverse ⟨(c t).hleft,(c t).hlt.le.trans (c t).hright⟩] at H
    exact H
  have Hright (t : P.ordinaryCapIndex (P.capFamily F) A K j) : (c t).right ≤ zg:=by
    have Hmass : Q.alpha.val.val (c t).right ≤ K*v:=t.property.2.2.trans (min_le_left _ _)
    have H:=Q.shiftedNativeModel.R_monotone Hmass
    rw [Q.shiftedNativeModel.R_inverse ⟨(c t).hleft.trans (c t).hlt.le,(c t).hright⟩] at H
    exact H
  have Hcontacts : ∀t : P.ordinaryCapIndex (P.capFamily F) A K j,
      P.H (c t).left=0 ∧ (P.H (c t).right=0 ∨ (c t).right=1):=by
    intro t
    have H:=P.capFamily_contacts F t.val
    refine ⟨?_,H.2⟩
    rcases H.1 with H|H
    · exact H
    · have Hmass:=t.property.2.1
      change v ≤ Q.alpha.val.val (P.capFamily F t.val).left at Hmass
      rw [H,Q.alpha.property.1] at Hmass
      linarith
  have Hdisjoint : Pairwise (fun s t : P.ordinaryCapIndex (P.capFamily F) A K j=>
      Disjoint (Ioo (c s).left (c s).right) (Ioo (c t).left (c t).right)):=by
    intro s t hst
    exact P.capFamily_disjoint F (fun H=>hst (Subtype.ext H))
  have Hbudget:=hn Q P _ c ag zg v (K*v) K (K*v) (v/2) (Q.xs+K*v) v K Lside cut
    (fun t r hr=>P.capFamily_wholeUnit F t.val hr) Hcontacts Hdisjoint hag hagz hzg
    Hleft Hright hv.le hK1
    (by nlinarith [Q.data.hU] : K*v+comparisonSmallMass Q.data.N Q.data.E ≤ 
      K*(v+comparisonSmallMass Q.data.N Q.data.E))
    (fun t=>t.property.2.1) (fun t=>t.property.2.2.trans (min_le_left _ _))
    (mul_pos hKpos hv)
    (by dsimp only [ag,zg];rw [Hlow,Hhigh];linarith)
    (by positivity : 0 < v/2) Hlow.ge
    (by positivity [Q.hxs] : 0 < Q.xs+K*v)
    (by dsimp only [zg];rw [Hhigh]) hv hKpos
    (fun t=>by have H:=t.property.2.1;change v ≤ Q.alpha.val.val (c t).left at H;linarith [Q.data.hU])
    (fun t=>by
      have Hl:=t.property.2.1
      have Hr:=t.property.2.2.trans (min_le_left _ _)
      change v ≤ Q.alpha.val.val (c t).left at Hl
      change Q.alpha.val.val (c t).right ≤ K*v at Hr
      linarith)
    hLside hcut hlogcut
  have HE:=P.ordinaryGroup_eq_retainedSupport (P.capFamily F) A K j
  rw [min_eq_left hKv] at HE
  rw [HE]
  exact Hbudget

theorem eventually_actual_theta_zero_outer_cap_contact_optimized_sum
    (ell : ℕ) (hell : 2 < ell) (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Qraw : ℝ,1 ≤ Qraw ∧ ∀ᶠn : ℕ in atTop,
      ∀(Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (P : Q.Potential) (A : Set ℝ) (lo hi K Lside cut : ℝ),
        MeasurableSet A → A⊆Ioo Q.data.rmin 1 →
        Q.cavityCapTravel ≤ Q.xs → 2*cu*(Az+1)*Q.xs ≤ lo →
        comparisonSmallMass Q.data.N Q.data.E ≤ (cl/(2*cu))*lo →
        2*Q.data.s < (cl/(4*cu))*lo → 4 ≤ K → 4*cu/cl ≤ K → K*hi ≤ 1 →
        (∀r∈A,lo ≤ Q.alpha.val.val r ∧ Q.alpha.val.val r ≤ hi) →
        0 ≤ Lside → 0 < cut → Real.log (1/cut) ≤ Lside →
        (∫u in 0..1,(A∩(P.negativeSet∪P.contactSet)).indicator
          (fun _=>1) (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u) ≤ 
          ∑j : ActualThetaZeroOverlapMinimum.LocalShiftedMassDyad Q lo hi,
            let v:=comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j.val:ℕ)
            Q.ordinaryOptimizedBudget ell Qraw K Lside cut (K*v) (v/2)
              (Q.xs+K*v) v K (Q.shiftedNativeModel.R (K*v)) := by
  obtain ⟨Qraw,hQraw,Hgroups⟩:=eventually_actual_theta_zero_ordinary_group_optimized_budget
    ell hell Bclock (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Qraw,hQraw,?_⟩
  filter_upwards [Hgroups] with n hn
  intro Q P A lo hi K Lside cut hA hAD htravel houter hU hstart hK hKcap hhi
    hscale hLside hcut hlogcut
  obtain ⟨F,_,_,hlim⟩:=P.cap_contact_thermal_exhaustion A hA
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro t
  have Hcover:=P.outer_finite_cap_thermal_le_ordinary_sum (P.capFamily (F t)) A hA hAD
    hcl hcu hAz htravel houter hU hstart.le hK hKcap hscale
  apply Hcover.trans
  apply Finset.sum_le_sum
  intro j _
  have hstrict : Q.data.s < 
      (comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j.val:ℕ))/2:=by
    have H:=j.property.1
    linarith
  have hKv : K*(comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j.val:ℕ)) ≤ 1:=
    (mul_le_mul_of_nonneg_left j.property.2 (show 0 ≤ K by linarith)).trans hhi
  exact hn Q P (F t) A K j.val Lside cut hK hstrict hKv hLside hcut hlogcut

end OAI.SKFluctuations.LaplaceWindowFormalization
