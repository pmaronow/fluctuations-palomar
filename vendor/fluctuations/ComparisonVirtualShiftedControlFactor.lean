module

public import ComparisonVirtualPotentialCompactness

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 3000000

theorem inverseControlFactor_from_origin_ratio_eq
    {A : ℝ→ℝ} {origin s r : ℝ} (hir : IntervalIntegrable A volume origin r)
    (his : IntervalIntegrable A volume origin s) :
    inverseControlFactor origin A r/inverseControlFactor origin A s=Real.exp (∫t in s..r,A t) := by
  rw [inverseControlFactor,inverseControlFactor,←Real.exp_sub,
    intervalIntegral.integral_interval_sub_left hir his]

theorem inverseControlFactor_from_origin_monotoneOn
    {A : ℝ→ℝ} {origin : ℝ} (hwork : origin ≤ 1) (hi : IntervalIntegrable A volume origin 1)
    (hA : ∀ᵐ r,r∈Icc origin 1→0 ≤ A r) :
    MonotoneOn (inverseControlFactor origin A) (Icc origin 1) := by
  intro s hs r hr hsr
  apply Real.exp_le_exp.mpr
  have hir := hi.mono_set (by rw [uIcc_of_le hr.1,uIcc_of_le hwork];exact Icc_subset_Icc le_rfl hr.2)
  have his := hi.mono_set (by rw [uIcc_of_le hs.1,uIcc_of_le hwork];exact Icc_subset_Icc le_rfl hs.2)
  have hh : 0 ≤ ∫t in s..r,A t := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hsr
    filter_upwards [ae_restrict_of_ae hA,ae_restrict_mem measurableSet_Icc] with t ht htri
    exact ht ⟨hs.1.trans htri.1,htri.2.trans hr.2⟩
  change (∫t in origin..s,A t) ≤ ∫t in origin..r,A t
  rw [←sub_nonneg,intervalIntegral.integral_interval_sub_left hir his]
  exact hh

theorem inverseControlFactor_from_origin_distortion_on_band
    {A : ℝ→ℝ} {origin a b K ref : ℝ} (ha : origin ≤ a) (hb : b ≤ 1) (hab : a ≤ b)
    (hK : 1 ≤ K) (href : ref∈Icc a b)
    (hi : IntervalIntegrable A volume origin 1)
    (hA : ∀ᵐ r,r∈Icc origin 1→0 ≤ A r)
    (hIntegral : (∫r in a..b,A r) ≤ 2*Real.log K) :
    ∀r∈Icc a b,inverseControlFactor origin A r/inverseControlFactor origin A ref∈
      Icc (1/K^2) (K^2) := by
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hsub : Icc a b⊆Icc origin 1 := Icc_subset_Icc ha hb
  have hwork : origin ≤ 1 := ha.trans (hab.trans hb)
  have hm := inverseControlFactor_from_origin_monotoneOn hwork hi hA
  have hir q (hq : q∈Icc a b) : IntervalIntegrable A volume origin q :=
    hi.mono_set (by
      rw [uIcc_of_le (hsub hq).1,uIcc_of_le hwork]
      exact Icc_subset_Icc le_rfl (hsub hq).2)
  have he : Real.exp (2*Real.log K)=K^2 := by
    rw [show (2:ℝ)=((2:ℕ):ℝ) by norm_num,Real.exp_nat_mul,Real.exp_log hKp]
  have hspread : inverseControlFactor origin A b ≤ K^2*inverseControlFactor origin A a := by
    apply (div_le_iff₀ (inverseControlFactor_pos origin A a)).mp
    rw [inverseControlFactor_from_origin_ratio_eq (hir b ⟨hab,le_rfl⟩) (hir a ⟨le_rfl,hab⟩)]
    exact (Real.exp_le_exp.mpr hIntegral).trans_eq he
  intro r hr
  have hRefp := inverseControlFactor_pos origin A ref
  have hRp := inverseControlFactor_pos origin A r
  have hAr := hm (hsub ⟨le_rfl,hab⟩) (hsub hr) hr.1
  have hRb := hm (hsub hr) (hsub ⟨hab,le_rfl⟩) hr.2
  have hAref := hm (hsub ⟨le_rfl,hab⟩) (hsub href) href.1
  have hRefb := hm (hsub href) (hsub ⟨hab,le_rfl⟩) href.2
  constructor
  · apply (le_div_iff₀ hRefp).mpr
    rw [div_mul_eq_mul_div,one_mul]
    apply (div_le_iff₀ (sq_pos_of_pos hKp)).mpr
    have hh := hRefb.trans hspread
    have hh2 := mul_le_mul_of_nonneg_left hAr (sq_nonneg K)
    nlinarith [hh,hh2]
  · apply (div_le_iff₀ hRefp).mpr
    exact hRb.trans (hspread.trans (mul_le_mul_of_nonneg_left hAref (sq_nonneg K)))

theorem comparison_virtual_control_integral_bound_on_working
    {N delta U L E d origin a b : ℝ} (hN : 0 < N) (hU : 0 < U) (hL : 0 < L)
    (hE : 0 < E) (hd : 0 ≤ d) (ha : origin ≤ a) (hb : b ≤ 1) (hab : a ≤ b)
    {alpha k : ℝ→ℝ} {C : ℝ≥0}
    (hAlpha : LipschitzOnWith C alpha (Icc origin 1))
    (hMono : StrictMonoOn alpha (Icc origin 1))
    (hRange : ∀r∈Icc origin 1,alpha r∈Icc (0:ℝ) 1)
    (hAi : IntervalIntegrable (comparisonVirtualControlDensity N delta U L E d alpha k) volume a b)
    (hDeriv : ∀ᵐ r,r∈Icc origin 1→
      0 ≤ k r ∧ k r ≤ deriv alpha r ∧ deriv alpha r ≤ comparisonCap N delta U L E d (alpha r)) :
    (∫r in a..b,comparisonVirtualControlDensity N delta U L E d alpha k r) ≤
      2*Real.log ((alpha b+U)/(alpha a+U)) := by
  have hsub : Icc a b⊆Icc origin 1 := Icc_subset_Icc ha hb
  have hLip := hAlpha.mono hsub
  have hAC : AbsolutelyContinuousOnInterval alpha a b := by
    have hLipU : LipschitzOnWith C alpha (uIcc a b) := by simpa only [uIcc_of_le hab] using hLip
    exact hLipU.absolutelyContinuousOnInterval
  have hPos r (hr : r∈Icc a b) : 0 < alpha r+U := by linarith [(hRange r (hsub hr)).1]
  have hInv : ContinuousOn (fun r=>1/(alpha r+U)) (Icc a b) :=
    continuousOn_const.div (hLip.continuousOn.add continuousOn_const)
      (fun r hr=>(hPos r hr).ne')
  have hJi : IntervalIntegrable (fun r=>2*deriv alpha r/(alpha r+U)) volume a b := by
    have hInvU : ContinuousOn (fun r=>1/(alpha r+U)) (uIcc a b) := by simpa only [uIcc_of_le hab] using hInv
    have hi := hAC.intervalIntegrable_deriv.continuousOn_mul hInvU
    convert hi.const_mul 2 using 1
    funext r
    ring
  have hdom : ∀ᵐ r∂volume.restrict (Icc a b),
      comparisonVirtualControlDensity N delta U L E d alpha k r ≤ 2*deriv alpha r/(alpha r+U) := by
    filter_upwards [ae_restrict_of_ae hDeriv,ae_restrict_mem measurableSet_Icc] with r hr hri
    exact (comparison_virtual_control_density_bound hN hU hL hE hd
      (hRange r (hsub hri)).1 (hr (hsub hri)).1 (hr (hsub hri)).2.1 (hr (hsub hri)).2.2).2
  have hbound := intervalIntegral.integral_mono_ae_restrict hab hAi hJi hdom
  have habMass : alpha a ≤ alpha b := hMono.monotoneOn (hsub ⟨le_rfl,hab⟩)
    (hsub ⟨hab,le_rfl⟩) hab
  have hchange := lipschitz_interval_integral_image hab hLip (hMono.mono hsub).injOn
    (fun u=>1/(u+U))
  rw [hLip.continuousOn.image_Icc_of_monotoneOn hab (hMono.mono hsub).monotoneOn] at hchange
  have he : (∫r in a..b,deriv alpha r/(alpha r+U))=
      Real.log ((alpha b+U)/(alpha a+U)) := by
    have hlogInt : (∫u in alpha a..alpha b,1/(u+U))=Real.log ((alpha b+U)/(alpha a+U)) := by
      rw [intervalIntegral.integral_comp_add_right (f:=fun u : ℝ=>1/u),
        integral_one_div_of_pos (hPos a ⟨le_rfl,hab⟩) (hPos b ⟨hab,le_rfl⟩)]
    rw [←hlogInt]
    rw [intervalIntegral.integral_of_le hab,←integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le habMass,←integral_Icc_eq_integral_Ioc,hchange]
    apply setIntegral_congr_ae measurableSet_Icc
    filter_upwards [hDeriv] with r hr hri
    rw [abs_of_nonneg ((hr (hsub hri)).1.trans (hr (hsub hri)).2.1)]
    ring
  have he2 : (∫r in a..b,2*deriv alpha r/(alpha r+U))=
      2*(∫r in a..b,deriv alpha r/(alpha r+U)) := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r _
    ring
  exact hbound.trans_eq (by rw [he2,he])

def comparisonVirtualShiftedControlFactor (origin N delta U L E d : ℝ)
    (alpha k : ℝ→ℝ) : ℝ→ℝ :=
  inverseControlFactor origin (comparisonVirtualControlDensity N delta U L E d alpha k)

theorem comparison_virtual_shifted_native_factor_data
    {N delta U L E d c origin u0 : ℝ} {k : ℝ→ℝ}
    (hN : 0 < N) (hU : 0 < U) (hL : 0 < L) (hE : 0 < E) (hd : 0 ≤ d)
    (hwork : origin ≤ 1) (hc : 0 < c) (hk : ContinuousOn k (Icc origin 1))
    (hkc : ∀r∈Icc origin 1,c ≤ k r) (hkm : Measurable k)
    (alpha : inverseIntegralConstraints origin u0 k (comparisonCap N delta U L E d))
    {a b ref K : ℝ} (ha : origin ≤ a) (hb : b ≤ 1) (hab : a ≤ b)
    (href : ref∈Icc a b) (hK : 1 ≤ K)
    (hband : alpha.val.val b+U ≤ K*(alpha.val.val a+U)) :
    IntervalIntegrable (comparisonVirtualControlDensity N delta U L E d alpha.val.val k) volume origin 1 ∧
    MonotoneOn (comparisonVirtualShiftedControlFactor origin N delta U L E d alpha.val.val k) (Icc origin 1) ∧
    ∀r∈Icc a b,comparisonVirtualShiftedControlFactor origin N delta U L E d alpha.val.val k r/
      comparisonVirtualShiftedControlFactor origin N delta U L E d alpha.val.val k ref∈Icc (1/K^2) (K^2) := by
  let M := comparisonCap N delta U L E d
  let A := comparisonVirtualControlDensity N delta U L E d alpha.val.val k
  have hm := comparisonCap_monotoneOn (δ:=delta) hN hU.le hL hE hd
  have hM : 0 ≤ M 1 := comparisonCap_nonneg (δ:=delta) hN hU.le hL hE hd zero_le_one
  have hMc : Continuous M := comparisonCap_continuous N delta U L E d
  have hLip : LipschitzOnWith ⟨M 1,hM⟩ alpha.val.val (Icc origin 1) :=
    inverseIntegralConstraints_lipschitz hm hM alpha.property
  have hStrict := inverseConstraint_strictMonoOn hc hk hkc alpha.property
  have hSource : sourceInverseConstraints origin u0 k M alpha.val.val := by
    have he : alpha.val∈inverseDifferentialConstraints origin u0 k M := by
      rw [inverseDifferentialConstraints_eq origin u0 hwork k M hk hMc hm hM]
      exact alpha.property
    exact he
  obtain ⟨C,hC,hAe⟩ := hSource.2.2
  have hDeriv : ∀ᵐ r,r∈Icc origin 1→
      0 ≤ k r ∧ k r ≤ deriv alpha.val.val r ∧ deriv alpha.val.val r ≤ M (alpha.val.val r) := by
    filter_upwards [hAe] with r hr hri
    exact ⟨hc.le.trans (hkc r hri),(hr hri).1,(hr hri).2⟩
  have hRange r (_hr : r∈Icc origin 1) : alpha.val.val r∈Icc (0:ℝ) 1 :=
    alpha.val.property.1 r
  have hAm : Measurable A :=
    (inverseControlWeight_measurable alpha.val.property.2.measurable hkm hMc.measurable).mul
      ((comparisonCapSlope_continuous N delta U L E d).measurable.comp alpha.val.property.2.measurable)
  have hApoint r (hr : r∈Icc origin 1) : A r∈Icc (0:ℝ) (comparisonCapSlope N delta U L E d 1) := by
    have hw := inverseControlWeight_mem alpha.val.val k M r
    have hs := comparisonCapSlope_nonneg (δ:=delta) hN hU.le hL hE hd (hRange r hr).1
    have hbnd := comparisonCapSlope_bound (δ:=delta) hN hU.le hL hE hd (hRange r hr)
    rw [abs_of_nonneg hs] at hbnd
    dsimp only [A,comparisonVirtualControlDensity]
    exact ⟨mul_nonneg hw.1 hs,(mul_le_mul_of_nonneg_right hw.2 hs).trans (by simpa using hbnd)⟩
  have hi : IntervalIntegrable A volume origin 1 :=
    bounded_measurable_intervalIntegrable hwork hAm (Eventually.of_forall fun r hr=>by
      rw [abs_of_nonneg (hApoint r hr).1];exact (hApoint r hr).2)
  have hA : ∀ᵐ r,r∈Icc origin 1→0 ≤ A r := Eventually.of_forall fun r hr=>(hApoint r hr).1
  have hiab : IntervalIntegrable A volume a b :=
    hi.mono_set (by rw [uIcc_of_le hab,uIcc_of_le hwork];exact Icc_subset_Icc ha hb)
  have hIntegral := comparison_virtual_control_integral_bound_on_working hN hU hL hE hd ha hb hab
    hLip hStrict hRange hiab hDeriv
  have hleft : 0 < alpha.val.val a+U := by linarith [(hRange a ⟨ha,hab.trans hb⟩).1]
  have hright : 0 < (alpha.val.val b+U)/(alpha.val.val a+U) := by
    apply div_pos _ hleft
    linarith [(hRange b ⟨ha.trans hab,hb⟩).1]
  have hratio : (alpha.val.val b+U)/(alpha.val.val a+U) ≤ K := (div_le_iff₀ hleft).mpr hband
  have hlog := Real.log_le_log hright hratio
  have hIntegralK : (∫r in a..b,A r) ≤ 2*Real.log K := hIntegral.trans (by linarith)
  exact ⟨hi,inverseControlFactor_from_origin_monotoneOn hwork hi hA,
    inverseControlFactor_from_origin_distortion_on_band ha hb hab hK href hi hA hIntegralK⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
