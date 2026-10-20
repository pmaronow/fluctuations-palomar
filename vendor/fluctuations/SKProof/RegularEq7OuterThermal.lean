module

public import ComparisonOriginalQTerminalGroupImportFirstPositivityRepair
public import ComparisonActualHighWallThetaZeroOrdinaryCover
public import ComparisonActualHighWallThetaZeroCapExhaustion
public import ComparisonActualHighWallThetaZeroEq7FiniteThermalAssembly
public import ComparisonOriginalQOuterLocalErrorImportFirstDraft
public import SKProof.RegularEq7OuterGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization.RegularEq7
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem eventually_actual_theta_zero_outer_truncated_optimized_sum_draft
    (ell : ℕ) (hell : 2 < ell) (Bclock : ℝ)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Qraw : ℝ, 1 ≤ Qraw ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (Q : ActualThetaZeroOverlapMinimum
          (n+1) m delta cl cu Az C0 Ct D Bclock)
        (P : Q.Potential) (A : Set ℝ)
        (lo hi K Lside cut : ℝ),
      MeasurableSet A → A ⊆ Ioo Q.data.rmin 1 →
      Q.cavityCapTravel ≤ Q.xs →
      2*cu*(Az+1)*Q.xs ≤ lo →
      comparisonSmallMass Q.data.N Q.data.E ≤ (cl/(2*cu))*lo →
      2*Q.data.s < (cl/(4*cu))*lo →
      4 ≤ K → 4*cu/cl ≤ K →
      (∀r∈A,lo ≤ Q.alpha.val.val r ∧ Q.alpha.val.val r ≤ hi) →
      0 ≤ Lside → 0 < cut → Real.log (1/cut) ≤ Lside →
      (∫u in 0..1,
        (A∩(P.negativeSet∪P.contactSet)).indicator (fun _ => (1:ℝ))
          (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u) ≤
      ∑j : LocalShiftedMassDyad Q lo hi,
        let v := comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j.val:ℕ)
        let z := min (K*v) 1
        Q.ordinaryOptimizedBudget ell Qraw K Lside cut (K*v) (v/2)
          (Q.xs+z) v K (Q.shiftedNativeModel.R z) := by
  obtain ⟨Qraw,hQraw,Hgroups⟩ :=
    eventually_original_q_terminal_arbitrary_group_import_first_draft
      ell hell Bclock (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Qraw,hQraw,?_⟩
  filter_upwards [Hgroups] with n hn
  intro Q P A lo hi K Lside cut hA hAD htravel houter hU hstart
    hK hKcap hscale hLside hcut hlogcut
  obtain ⟨F,_,_,hlim⟩ := P.cap_contact_thermal_exhaustion A hA
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro t
  have Hcover := P.outer_finite_cap_thermal_le_ordinary_sum
    (P.capFamily (F t)) A hA hAD hcl hcu hAz htravel houter
    hU hstart.le hK hKcap hscale
  apply Hcover.trans
  apply Finset.sum_le_sum
  intro j _
  have hstrict : Q.data.s <
      (comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j.val:ℕ))/2 := by
    linarith [j.property.1]
  exact hn Q P (F t) A K j.val Lside cut hK hstrict
    hLside hcut hlogcut

variable {Q : ActualThetaZeroOverlapMinimum
  (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem ShiftedCapInterval.eq7_crossing_cap_confined_to_enlargement_draft
    {P : Q.Potential} (c : ShiftedCapInterval Q P)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (htravel : Q.cavityCapTravel ≤ Q.xs)
    {b lo : ℝ} (hinner : (Az+1)*Q.xs ≤ b)
    (hleft : Q.alpha.val.val c.left ≤ b)
    (houter : cu*(1/cl+1)*b < lo) :
    ∀ r ∈ Ioo c.left c.right, Q.alpha.val.val r < lo := by
  have Hcap := c.endpoint_mass_envelope hcl hcu hAz htravel
  have Hleft : Q.alpha.val.val c.left/cl ≤ b/cl :=
    div_le_div_of_nonneg_right hleft hcl.le
  have Hinside :
      Q.alpha.val.val c.left/cl+(Az+1)*Q.xs ≤ b/cl+b :=
    add_le_add Hleft hinner
  have Hright : Q.alpha.val.val c.right ≤ cu*(1/cl+1)*b := by
    calc
      Q.alpha.val.val c.right ≤
          cu*(Q.alpha.val.val c.left/cl+(Az+1)*Q.xs) := Hcap
      _ ≤ cu*(b/cl+b) := mul_le_mul_of_nonneg_left Hinside hcu.le
      _ = cu*(1/cl+1)*b := by ring
  intro r hr
  exact (Q.alpha.val.property.2 hr.2.le).trans_lt
    (Hright.trans_lt houter)

theorem Potential.eq7_outer_band_error_of_thermal_draft
    (P : Q.Potential)
    (hC0 : 0 < C0) (hN : 2 ≤ Q.data.N)
    (hnd : 1/Q.data.N ≤ Q.data.d)
    (hlog : 1 ≤ Real.log Q.data.N)
    (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (htravel : Q.cavityCapTravel ≤ Q.xs)
    {lo hi C T : ℝ} (hC : 0 ≤ C)
    (hlo : lo ∈ Icc Q.data.s 1) (hhi : hi ∈ Icc Q.data.s 1)
    (hlohi : lo ≤ hi) (hwidth : hi-lo ≤ C*lo)
    (houter : 2*cu*(Az+1)*Q.xs ≤ lo)
    (hthermal :
      (∫u in lo..hi,
        (P.negativeSet∪P.contactSet).indicator (fun _ => (1:ℝ))
          (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u) ≤ T) :
    (∫u in lo..hi,
      (P.negativeSet∪P.contactSet).indicator (fun _ => (1:ℝ))
        (Q.shiftedNativeModel.R u)*
          Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
      3*(max 1 cu*laplaceComparisonStrength Q.data.d Q.lam lo)*T+
      128*(max 1 cu)*C*(Real.log Q.data.N)^3*
        (C0^3*Q.data.N^(-3*m)*Q.data.E)/(Q.data.N^delta)^2 := by
  have hv : lo ∈ Ioc (0:ℝ) 1 :=
    ⟨Q.data.hs.1.trans_le hlo.1,hlo.2⟩
  have Herror := P.outer_import_first_local_error_le_thermal_draft
    hcu hAz htravel hlo hhi hlohi houter
  have Hwidth := eq7_outer_cap_width_energy_rate Q
    hC0 hN hnd hlog (a:=1) (by norm_num) hC hv hwidth
  have hG : 0 ≤ 3*(max 1 cu*laplaceComparisonStrength Q.data.d Q.lam lo) := by
    positivity [laplaceComparisonStrength_pos Q.data.d Q.hlam lo]
  have Hthermal := mul_le_mul_of_nonneg_left hthermal hG
  simp only [div_one] at Hwidth
  simp only [Q.shiftedNativeModel_radius] at hthermal ⊢
  dsimp only at Herror
  simp only [Q.shiftedNativeModel_radius] at Hthermal
  linarith only [Herror,Hwidth,Hthermal]

theorem eventually_original_q_outer_localized_nonpositive_budget_draft
    (ell : ℕ) (hell : 2 < ell) (Bclock : ℝ)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Qraw : ℝ, 1 ≤ Qraw ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (Q : ActualThetaZeroOverlapMinimum
          (n+1) m delta cl cu Az C0 Ct D Bclock)
        (P : Q.Potential) (lo hi K C Lside cut : ℝ),
      2 ≤ Q.data.N → 1/Q.data.N ≤ Q.data.d →
      1 ≤ Real.log Q.data.N →
      lo ∈ Icc Q.data.s 1 → hi ∈ Icc Q.data.s 1 → lo ≤ hi →
      0 ≤ C → hi-lo ≤ C*lo →
      Q.cavityCapTravel ≤ Q.xs →
      2*cu*(Az+1)*Q.xs ≤ lo →
      comparisonSmallMass Q.data.N Q.data.E ≤ (cl/(2*cu))*lo →
      2*Q.data.s < (cl/(4*cu))*lo →
      4 ≤ K → 4*cu/cl ≤ K →
      0 ≤ Lside → 0 < cut → Real.log (1/cut) ≤ Lside →
      (∫u in lo..hi,
        (P.negativeSet∪P.contactSet).indicator (fun _ => (1:ℝ))
          (Q.shiftedNativeModel.R u)*
            Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
        3*(max 1 cu*laplaceComparisonStrength Q.data.d Q.lam lo)*
          (∑j : LocalShiftedMassDyad Q lo hi,
            let v := comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j.val:ℕ)
            let z := min (K*v) 1
            Q.ordinaryOptimizedBudget ell Qraw K Lside cut (K*v) (v/2)
              (Q.xs+z) v K (Q.shiftedNativeModel.R z))+
        128*(max 1 cu)*C*(Real.log Q.data.N)^3*
          (C0^3*Q.data.N^(-3*m)*Q.data.E)/(Q.data.N^delta)^2 := by
  obtain ⟨Qraw,hQraw,Hsource⟩ :=
    eventually_actual_theta_zero_outer_truncated_optimized_sum_draft
      ell hell Bclock (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Qraw,hQraw,?_⟩
  filter_upwards [Hsource] with n hn
  intro Q P lo hi K C Lside cut hN hnd hlog hlo hhi hlohi hC hwidth
    htravel houter hU hstart hK hKcap hLside hcut hlogcut
  let A := Q.shiftedNativeModel.massSlice lo hi
  let F := P.negativeSet∪P.contactSet
  let T := ∑j : LocalShiftedMassDyad Q lo hi,
    let v := comparisonSmallMass Q.data.N Q.data.E*(2:ℝ)^(j.val:ℕ)
    let z := min (K*v) 1
    Q.ordinaryOptimizedBudget ell Qraw K Lside cut (K*v) (v/2)
      (Q.xs+z) v K (Q.shiftedNativeModel.R z)
  have hA : MeasurableSet A := measurableSet_Ioo
  have hAD : A ⊆ Ioo Q.data.rmin 1 := by
    intro r hr
    exact ⟨(Q.shiftedNativeModel.R_bounds lo).1.trans_lt hr.1,
      hr.2.trans_le (Q.shiftedNativeModel.R_bounds hi).2⟩
  have hscale : ∀r∈A,
      lo ≤ Q.alpha.val.val r ∧ Q.alpha.val.val r ≤ hi := by
    intro r hr
    have H := Q.shiftedNativeModel.massSlice_profile_mem hlo hhi hr
    exact ⟨H.1.le,H.2.le⟩
  have Hsource := hn Q P A lo hi K Lside cut hA hAD htravel
    houter hU hstart hK hKcap hscale hLside hcut hlogcut
  have hF : MeasurableSet F :=
    P.negativeSet_open.measurableSet.union P.contactSet_measurable
  have hmass := Q.shiftedNativeModel.massSlice_thermal_mask_integral
    hlo hhi hlohi F hF
  have hthermal :
      (∫u in lo..hi,F.indicator (fun _ => (1:ℝ))
        (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u) ≤ T := by
    rw [←hmass]
    exact Hsource
  have H := Potential.eq7_outer_band_error_of_thermal_draft P
    hC0 hN hnd hlog hcu hAz htravel hC hlo hhi hlohi hwidth
    houter hthermal
  simpa only [F,T] using H

end OAI.SKFluctuations.LaplaceWindowFormalization.RegularEq7
