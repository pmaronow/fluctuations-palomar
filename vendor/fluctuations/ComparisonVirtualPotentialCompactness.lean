module

public import ComparisonCapDensity
public import BoundedMassProfileHelly
public import ComparisonSelectedCumulativeCompactness
public import ComparisonStationarityDensityScaling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 3000000

theorem inverseControlWeight_mul_cap_le_deriv
    {alpha k M : ℝ→ℝ} {r : ℝ} (hk0 : 0 ≤ k r)
    (hk : k r ≤ deriv alpha r) (hM : deriv alpha r ≤ M (alpha r)) :
    inverseControlWeight alpha k M r*M (alpha r) ≤ deriv alpha r := by
  have hw := inverseControlWeight_mem alpha k M r
  by_cases he : k r=M (alpha r)
  · have hd : deriv alpha r=k r := le_antisymm (hM.trans_eq he.symm) hk
    unfold inverseControlWeight
    rw [hd,sub_self,he,sub_self,div_zero]
    norm_num
    nlinarith [he,hk0]
  · have hstrict : k r < M (alpha r) := lt_of_le_of_ne (hk.trans hM) he
    have hd := inverseControlWeight_equation hk hM hstrict
    nlinarith [mul_nonneg hk0 (sub_nonneg.mpr hw.2)]

def comparisonVirtualControlDensity (N delta U L E d : ℝ) (alpha k : ℝ→ℝ) : ℝ→ℝ :=
  fun r=>inverseControlWeight alpha k (comparisonCap N delta U L E d) r*
    comparisonCapSlope N delta U L E d (alpha r)

def comparisonVirtualControlFactor (N delta U L E d : ℝ) (alpha k : ℝ→ℝ) : ℝ→ℝ :=
  inverseControlFactor 0 (comparisonVirtualControlDensity N delta U L E d alpha k)

theorem comparison_virtual_control_density_bound
    {N delta U L E d : ℝ} (hN : 0 < N) (hU : 0 < U) (hL : 0 < L)
    (hE : 0 < E) (hd : 0 ≤ d) {alpha k : ℝ→ℝ} {r : ℝ}
    (ha : 0 ≤ alpha r) (hk0 : 0 ≤ k r)
    (hk : k r ≤ deriv alpha r)
    (hM : deriv alpha r ≤ comparisonCap N delta U L E d (alpha r)) :
    comparisonVirtualControlDensity N delta U L E d alpha k r∈
      Icc (0:ℝ) (2*deriv alpha r/(alpha r+U)) := by
  have hw := inverseControlWeight_mem alpha k (comparisonCap N delta U L E d) r
  have hs := comparisonCapSlope_nonneg (δ:=delta) hN hU.le hL hE hd ha
  have htimes := comparisonCapSlope_times_le (δ:=delta) (E:=E) (d:=d) hN hU.le hL ha
  have hm := inverseControlWeight_mul_cap_le_deriv hk0 hk hM
  have hh := mul_le_mul_of_nonneg_left htimes hw.1
  constructor
  · exact mul_nonneg hw.1 hs
  · apply (le_div_iff₀ (by linarith : 0 < alpha r+U)).mpr
    dsimp only [comparisonVirtualControlDensity]
    nlinarith

theorem comparison_virtual_control_integral_bound
    {N delta U L E d a b : ℝ} (hN : 0 < N) (hU : 0 < U) (hL : 0 < L)
    (hE : 0 < E) (hd : 0 ≤ d) (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b)
    {alpha k : ℝ→ℝ} {C : ℝ≥0}
    (hAlpha : LipschitzOnWith C alpha (Icc (0:ℝ) 1))
    (hMono : StrictMonoOn alpha (Icc (0:ℝ) 1))
    (hRange : ∀r∈Icc (0:ℝ) 1,alpha r∈Icc (0:ℝ) 1)
    (hAi : IntervalIntegrable (comparisonVirtualControlDensity N delta U L E d alpha k) volume a b)
    (hDeriv : ∀ᵐ r,r∈Icc (0:ℝ) 1→
      0 ≤ k r ∧ k r ≤ deriv alpha r ∧ deriv alpha r ≤ comparisonCap N delta U L E d (alpha r)) :
    (∫r in a..b,comparisonVirtualControlDensity N delta U L E d alpha k r) ≤
      2*Real.log ((alpha b+U)/(alpha a+U)) := by
  have hsub : Icc a b⊆Icc (0:ℝ) 1 := Icc_subset_Icc ha hb
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

theorem inverseControlFactor_ratio_eq
    {A : ℝ→ℝ} {s r : ℝ} (hir : IntervalIntegrable A volume 0 r)
    (his : IntervalIntegrable A volume 0 s) :
    inverseControlFactor 0 A r/inverseControlFactor 0 A s=Real.exp (∫t in s..r,A t) := by
  rw [inverseControlFactor,inverseControlFactor,←Real.exp_sub,
    intervalIntegral.integral_interval_sub_left hir his]

theorem inverseControlFactor_monotoneOn
    {A : ℝ→ℝ} (hi : IntervalIntegrable A volume (0:ℝ) 1)
    (hA : ∀ᵐ r,r∈Icc (0:ℝ) 1→0 ≤ A r) :
    MonotoneOn (inverseControlFactor 0 A) (Icc (0:ℝ) 1) := by
  intro s hs r hr hsr
  apply Real.exp_le_exp.mpr
  have hir := hi.mono_set (by rw [uIcc_of_le hr.1,uIcc_of_le zero_le_one];exact Icc_subset_Icc le_rfl hr.2)
  have his := hi.mono_set (by rw [uIcc_of_le hs.1,uIcc_of_le zero_le_one];exact Icc_subset_Icc le_rfl hs.2)
  have hh : 0 ≤ ∫t in s..r,A t := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hsr
    filter_upwards [ae_restrict_of_ae hA,ae_restrict_mem measurableSet_Icc] with t ht htri
    exact ht ⟨hs.1.trans htri.1,htri.2.trans hr.2⟩
  change (∫t in 0..s,A t) ≤ ∫t in 0..r,A t
  rw [←sub_nonneg,intervalIntegral.integral_interval_sub_left hir his]
  exact hh

theorem inverseControlFactor_distortion_on_band
    {A : ℝ→ℝ} {a b K ref : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b)
    (hK : 1 ≤ K) (href : ref∈Icc a b)
    (hi : IntervalIntegrable A volume (0:ℝ) 1)
    (hA : ∀ᵐ r,r∈Icc (0:ℝ) 1→0 ≤ A r)
    (hIntegral : (∫r in a..b,A r) ≤ 2*Real.log K) :
    ∀r∈Icc a b,inverseControlFactor 0 A r/inverseControlFactor 0 A ref∈
      Icc (1/K^2) (K^2) := by
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hsub : Icc a b⊆Icc (0:ℝ) 1 := Icc_subset_Icc ha hb
  have hm := inverseControlFactor_monotoneOn hi hA
  have hir q (hq : q∈Icc a b) : IntervalIntegrable A volume 0 q :=
    hi.mono_set (by
      rw [uIcc_of_le (hsub hq).1,uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl (hsub hq).2)
  have he : Real.exp (2*Real.log K)=K^2 := by
    rw [show (2:ℝ)=((2:ℕ):ℝ) by norm_num,Real.exp_nat_mul,Real.exp_log hKp]
  have hspread : inverseControlFactor 0 A b ≤ K^2*inverseControlFactor 0 A a := by
    apply (div_le_iff₀ (inverseControlFactor_pos 0 A a)).mp
    rw [inverseControlFactor_ratio_eq (hir b ⟨hab,le_rfl⟩) (hir a ⟨le_rfl,hab⟩)]
    exact (Real.exp_le_exp.mpr hIntegral).trans_eq he
  intro r hr
  have hRefp := inverseControlFactor_pos 0 A ref
  have hRp := inverseControlFactor_pos 0 A r
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

theorem comparison_virtual_native_factor_data
    {N delta U L E d c : ℝ} {k : ℝ→ℝ}
    (hN : 0 < N) (hU : 0 < U) (hL : 0 < L) (hE : 0 < E) (hd : 0 ≤ d)
    (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
    (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r) (hkm : Measurable k)
    (alpha : inverseIntegralConstraints 0 0 k (comparisonCap N delta U L E d))
    {a b ref K : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b)
    (href : ref∈Icc a b) (hK : 1 ≤ K)
    (hband : alpha.val.val b+U ≤ K*(alpha.val.val a+U)) :
    IntervalIntegrable (comparisonVirtualControlDensity N delta U L E d alpha.val.val k) volume (0:ℝ) 1 ∧
    MonotoneOn (comparisonVirtualControlFactor N delta U L E d alpha.val.val k) (Icc (0:ℝ) 1) ∧
    ∀r∈Icc a b,comparisonVirtualControlFactor N delta U L E d alpha.val.val k r/
      comparisonVirtualControlFactor N delta U L E d alpha.val.val k ref∈Icc (1/K^2) (K^2) := by
  let M := comparisonCap N delta U L E d
  let A := comparisonVirtualControlDensity N delta U L E d alpha.val.val k
  have hm := comparisonCap_monotoneOn (δ:=delta) hN hU.le hL hE hd
  have hM : 0 ≤ M 1 := comparisonCap_nonneg (δ:=delta) hN hU.le hL hE hd zero_le_one
  have hMc : Continuous M := comparisonCap_continuous N delta U L E d
  have hLip : LipschitzOnWith ⟨M 1,hM⟩ alpha.val.val (Icc (0:ℝ) 1) :=
    inverseIntegralConstraints_lipschitz hm hM alpha.property
  have hStrict := inverseConstraint_strictMonoOn hc hk hkc alpha.property
  have hSource : sourceInverseConstraints 0 0 k M alpha.val.val := by
    have he : alpha.val∈inverseDifferentialConstraints 0 0 k M := by
      rw [inverseDifferentialConstraints_eq 0 0 zero_le_one k M hk hMc hm hM]
      exact alpha.property
    exact he
  obtain ⟨C,hC,hAe⟩ := hSource.2.2
  have hDeriv : ∀ᵐ r,r∈Icc (0:ℝ) 1→
      0 ≤ k r ∧ k r ≤ deriv alpha.val.val r ∧ deriv alpha.val.val r ≤ M (alpha.val.val r) := by
    filter_upwards [hAe] with r hr hri
    exact ⟨hc.le.trans (hkc r hri),(hr hri).1,(hr hri).2⟩
  have hRange r (_hr : r∈Icc (0:ℝ) 1) : alpha.val.val r∈Icc (0:ℝ) 1 :=
    alpha.val.property.1 r
  have hAm : Measurable A :=
    (inverseControlWeight_measurable alpha.val.property.2.measurable hkm hMc.measurable).mul
      ((comparisonCapSlope_continuous N delta U L E d).measurable.comp alpha.val.property.2.measurable)
  have hApoint r (hr : r∈Icc (0:ℝ) 1) : A r∈Icc (0:ℝ) (comparisonCapSlope N delta U L E d 1) := by
    have hw := inverseControlWeight_mem alpha.val.val k M r
    have hs := comparisonCapSlope_nonneg (δ:=delta) hN hU.le hL hE hd (hRange r hr).1
    have hbnd := comparisonCapSlope_bound (δ:=delta) hN hU.le hL hE hd (hRange r hr)
    rw [abs_of_nonneg hs] at hbnd
    dsimp only [A,comparisonVirtualControlDensity]
    exact ⟨mul_nonneg hw.1 hs,(mul_le_mul_of_nonneg_right hw.2 hs).trans (by simpa using hbnd)⟩
  have hi : IntervalIntegrable A volume (0:ℝ) 1 :=
    bounded_measurable_intervalIntegrable zero_le_one hAm (Eventually.of_forall fun r hr=>by
      rw [abs_of_nonneg (hApoint r hr).1];exact (hApoint r hr).2)
  have hA : ∀ᵐ r,r∈Icc (0:ℝ) 1→0 ≤ A r := Eventually.of_forall fun r hr=>(hApoint r hr).1
  have hiab : IntervalIntegrable A volume a b :=
    hi.mono_set (by rw [uIcc_of_le hab,uIcc_of_le zero_le_one];exact Icc_subset_Icc ha hb)
  have hIntegral := comparison_virtual_control_integral_bound hN hU hL hE hd ha hb hab
    hLip hStrict hRange hiab hDeriv
  have hleft : 0 < alpha.val.val a+U := by linarith [(hRange a ⟨ha,hab.trans hb⟩).1]
  have hright : 0 < (alpha.val.val b+U)/(alpha.val.val a+U) := by
    apply div_pos _ hleft
    linarith [(hRange b ⟨ha.trans hab,hb⟩).1]
  have hratio : (alpha.val.val b+U)/(alpha.val.val a+U) ≤ K := (div_le_iff₀ hleft).mpr hband
  have hlog := Real.log_le_log hright hratio
  have hIntegralK : (∫r in a..b,A r) ≤ 2*Real.log K := hIntegral.trans (by linarith)
  exact ⟨hi,inverseControlFactor_monotoneOn hi hA,
    inverseControlFactor_distortion_on_band ha hb hab hK href hi hA hIntegralK⟩

theorem virtual_negative_point_near_zero
    {H : ℝ→ℝ} {r T : ℝ} (hT : 0 < T) (hr : 0 ≤ r) (hend : r+2*T ≤ 1)
    (hH : ContinuousOn H (Icc (0:ℝ) 1)) (hneg : H r < 0)
    (htravel : ∀a b : ℝ,0 ≤ a→b ≤ 1→a ≤ b→
      (∀t∈Ioo a b,H t < 0)→b-a ≤ T) :
    ∃z∈Icc r (r+2*T),H z=0 := by
  by_contra hn
  have hzero : ∀z∈Icc r (r+2*T),H z≠0 := by simpa only [not_exists,not_and] using hn
  have hnegative : ∀t∈Ioo r (r+2*T),H t < 0 := by
    intro t ht
    by_contra hnt
    have hHt : 0 ≤ H t := not_lt.mp hnt
    have hsub : Icc r t⊆Icc (0:ℝ) 1 := Icc_subset_Icc hr (ht.2.le.trans hend)
    have hex := intermediate_value_Icc ht.1.le (hH.mono hsub) ⟨hneg.le,hHt⟩
    obtain ⟨z,hz,hHz⟩ := hex
    exact hzero z ⟨hz.1,hz.2.trans ht.2.le⟩ hHz
  have hh := htravel r (r+2*T) hr hend (by linarith) hnegative
  linarith

theorem virtual_positive_mass_has_nonpositive_anchor
    {alpha H k : ℝ→ℝ} {a b : ℝ} {C : ℝ≥0} (hab : a < b)
    (hAlpha : LipschitzOnWith C alpha (Icc a b))
    (hfloor : ∀ᵐ r,r∈Icc a b→0 < H r→deriv alpha r=k r)
    (hmass : (∫r in a..b,k r) < alpha b-alpha a) :
    ∃r∈Ioo a b,H r ≤ 0 := by
  by_contra hn
  have hpositive : ∀r∈Ioo a b,0 < H r := by simpa only [not_exists,not_and,not_le] using hn
  have hAC : AbsolutelyContinuousOnInterval alpha a b := by
    have hAlphaU : LipschitzOnWith C alpha (uIcc a b) := by simpa only [uIcc_of_le hab.le] using hAlpha
    exact hAlphaU.absolutelyContinuousOnInterval
  have he : (∫r in a..b,deriv alpha r)=∫r in a..b,k r := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hfloor,volume.ae_ne a,volume.ae_ne b] with r hr hra hrb hri
    rw [uIoc_of_le hab.le] at hri
    have hrcc : r∈Icc a b := ⟨hri.1.le,hri.2⟩
    exact hr hrcc (hpositive r ⟨hri.1,lt_of_le_of_ne hri.2 hrb⟩)
  rw [hAC.integral_deriv_eq_sub] at he
  linarith

theorem virtual_potential_lipschitz_of_ae_density_bound
    {H density : ℝ→ℝ} {a b B : ℝ} (hab : a ≤ b) (hB : 0 ≤ B)
    (hH : AbsolutelyContinuousOnInterval H a b)
    (hDeriv : ∀ᵐ r,r∈Icc a b→HasDerivAt H (density r) r)
    (hBound : ∀ᵐ r,r∈Icc a b→‖density r‖ ≤ B) :
    LipschitzOnWith B.toNNReal H (Icc a b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs r hr
  have hsub : uIcc r s⊆uIcc a b := by
    rw [uIcc_of_le hab]
    intro t ht
    exact ⟨(le_min hr.1 hs.1).trans ht.1,ht.2.trans (max_le hr.2 hs.2)⟩
  have hAC := hH.mono hsub
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const_ae (a:=r) (b:=s)
    (f:=deriv H) (C:=B) (by
      filter_upwards [hDeriv,hBound] with t hdt hbt ht
      have htcc : t∈Icc a b := by rw [←uIcc_of_le hab];exact hsub (uIoc_subset_uIcc ht)
      rw [(hdt htcc).deriv]
      exact hbt htcc)
  rw [hAC.integral_deriv_eq_sub] at hnorm
  simpa only [Real.dist_eq,Real.norm_eq_abs,Real.coe_toNNReal _ hB] using hnorm

theorem virtual_band_factor_exists_pointwise_subseq
    {a b K : ℝ} (hab : a ≤ b) (hK : 1 ≤ K) (J : ℕ→ℝ→ℝ)
    (hMono : ∀n,MonotoneOn (J n) (Icc a b))
    (hBound : ∀n r,r∈Icc a b→J n r∈Icc (1/K^2) (K^2)) :
    ∃j : ℝ→ℝ,∃phi : ℕ→ℕ,StrictMono phi ∧ Monotone j ∧
      (∀r∈Icc a b,j r∈Icc (1/K^2) (K^2)) ∧
      ∀r∈Icc a b,Tendsto (fun n=>J (phi n) r) atTop (𝓝 (j r)) := by
  have hKp : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hK2 : 0 < K^2 := sq_pos_of_pos hKp
  let clamp := fun r : ℝ=>max a (min b r)
  have hclamp r : clamp r∈Icc a b := by
    exact ⟨le_max_left _ _,max_le hab (min_le_left _ _)⟩
  have hclampMono : Monotone clamp := (monotone_const.max (monotone_const.min monotone_id))
  let P : ℕ→boundedMassProfiles := fun n=>⟨fun r=>J n (clamp r)/K^2,by
    constructor
    · intro r
      have hh := hBound n (clamp r) (hclamp r)
      exact ⟨div_nonneg ((by positivity : 0 ≤ 1/K^2).trans hh.1) hK2.le,
        (div_le_one hK2).mpr hh.2⟩
    · intro r s hrs
      exact div_le_div_of_nonneg_right (hMono n (hclamp r) (hclamp s) (hclampMono hrs)) hK2.le⟩
  obtain ⟨limit,phi,hphi,hlim⟩ := boundedMassProfiles_tendsto_subseq P
  let j := fun r=>K^2*limit.val r
  have hconv r (hr : r∈Icc a b) : Tendsto (fun n=>J (phi n) r) atTop (𝓝 (j r)) := by
    have hh := ((continuous_apply r).comp continuous_subtype_val).tendsto limit |>.comp hlim
    have hClamp : clamp r=r := by dsimp only [clamp];rw [min_eq_right hr.2,max_eq_right hr.1]
    have hc := hh.const_mul (K^2)
    convert hc using 1
    · funext n
      dsimp only [Function.comp_def,P]
      rw [hClamp]
      field_simp
    · rfl
  refine ⟨j,phi,hphi,?_,?_,hconv⟩
  · exact limit.property.2.const_mul hK2.le
  · intro r hr
    exact ⟨ge_of_tendsto (hconv r hr) (Eventually.of_forall fun n=>(hBound (phi n) r hr).1),
      le_of_tendsto (hconv r hr) (Eventually.of_forall fun n=>(hBound (phi n) r hr).2)⟩

theorem virtual_potentials_exists_uniform_subseq
    {a b B R : ℝ} (hB : 0 ≤ B)
    (P : ℕ→(BoundedContinuousFunction (Icc a b) ℝ))
    (hLip : ∀n,LipschitzWith B.toNNReal (P n))
    (hBound : ∀n r,P n r∈Icc (-R) R) :
    ∃p : BoundedContinuousFunction (Icc a b) ℝ,∃phi : ℕ→ℕ,StrictMono phi ∧
      Tendsto (P∘phi) atTop (𝓝 p) := by
  let A := Set.range P
  have hEqui : Equicontinuous (fun f : A=>fun r=>f.val r) := by
    apply (Metric.uniformEquicontinuous_of_continuity_modulus
      (fun t=>B*t) (by simpa using
        ((tendsto_id : Tendsto (fun t : ℝ=>t) (𝓝 0) (𝓝 0)).const_mul B)) _ _).equicontinuous
    intro r s f
    obtain ⟨n,hn⟩ := f.property
    simpa only [←hn,Real.coe_toNNReal _ hB] using (hLip n).dist_le_mul r s
  have hCompact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (Icc (-R) R) isCompact_Icc A
      (fun f r hf=>by obtain ⟨n,rfl⟩:=hf;exact hBound n r) hEqui
  obtain ⟨p,_,phi,hphi,hlim⟩ := hCompact.tendsto_subseq
    (fun n=>subset_closure (show P n∈A from ⟨n,rfl⟩))
  exact ⟨p,phi,hphi,hlim⟩

section Product
variable {Omega : Type*} [MeasurableSpace Omega]

theorem virtual_factor_gradient_product_L1
    (mu : Measure Omega) (J G : ℕ→Omega→ℝ) (j F : Omega→ℝ) {K : ℝ}
    (hK : 0 ≤ K) (hJm : ∀n,AEStronglyMeasurable (J n) mu)
    (hjm : AEStronglyMeasurable j mu) (hGi : ∀n,Integrable (G n) mu)
    (hFi : Integrable F mu)
    (hJb : ∀n,∀ᵐ t∂mu,|J n t| ≤ K) (hjb : ∀ᵐ t∂mu,|j t| ≤ K)
    (hJlim : ∀ᵐ t∂mu,Tendsto (fun n=>J n t) atTop (𝓝 (j t)))
    (hGlim : Tendsto (fun n=>∫t,|G n t-F t|∂mu) atTop (𝓝 0)) :
    Tendsto (fun n=>∫t,|J n t*G n t-j t*F t|∂mu) atTop (𝓝 0) := by
  have hPi n : Integrable (fun t=>J n t*F t) mu := by
    have hh := hFi.bdd_mul (hJm n) (by simpa only [Real.norm_eq_abs] using hJb n)
    simpa only [mul_comm] using hh
  have hLi : Integrable (fun t=>j t*F t) mu := by
    have hh := hFi.bdd_mul hjm (by simpa only [Real.norm_eq_abs] using hjb)
    simpa only [mul_comm] using hh
  have hP : Tendsto (fun n=>∫t,|J n t*F t-j t*F t|∂mu) atTop (𝓝 0) := by
    apply comparison_density_dominated_L1 mu (fun n t=>J n t*F t) (fun t=>j t*F t)
      (fun t=>K*|F t|) (fun n=>(hJm n).mul hFi.aestronglyMeasurable)
      (hjm.mul hFi.aestronglyMeasurable) (hFi.abs.const_mul K)
    · intro n
      filter_upwards [hJb n] with t ht
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)
    · filter_upwards [hjb] with t ht
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)
    · filter_upwards [hJlim] with t ht
      exact ht.mul_const (F t)
  apply comparison_density_L1_transfer mu
    (fun n t=>J n t*G n t) (fun n t=>J n t*F t) (fun _ t=>j t*F t)
    (fun n t=>|G n t-F t|) hK (fun n=>(hJm n).mul (hGi n).aestronglyMeasurable)
    hPi (fun _=>hLi) (fun n=>((hGi n).sub hFi).abs)
    (fun n=>Eventually.of_forall fun _=>abs_nonneg _) _ hP hGlim
  intro n
  filter_upwards [hJb n] with t ht
  rw [←mul_sub,abs_mul]
  exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)

end Product

theorem virtual_potential_moving_anchor_eq_zero
    {a b : ℝ} (P : ℕ→BoundedContinuousFunction (Icc a b) ℝ)
    (p : BoundedContinuousFunction (Icc a b) ℝ) (refs : ℕ→Icc a b)
    (ref : Icc a b) (hP : Tendsto P atTop (𝓝 p)) (hrefs : Tendsto refs atTop (𝓝 ref))
    (hzero : Tendsto (fun n=>P n (refs n)) atTop (𝓝 0)) : p ref=0 := by
  have hh := (continuous_eval.tendsto (p,ref)).comp (hP.prodMk_nhds hrefs)
  exact tendsto_nhds_unique hh hzero

theorem virtual_potential_uniform_limit_nonnegative
    {a b : ℝ} (P : ℕ→BoundedContinuousFunction (Icc a b) ℝ)
    (p : BoundedContinuousFunction (Icc a b) ℝ) (errors : ℕ→ℝ)
    (hP : Tendsto P atTop (𝓝 p)) (herr : Tendsto errors atTop (𝓝 0))
    (hLower : ∀n r,-errors n ≤ P n r) : ∀r,0 ≤ p r := by
  intro r
  have hp := (BoundedContinuousFunction.lipschitz_eval_const r).continuous.tendsto p |>.comp hP
  have he := herr.neg
  simpa only [neg_zero] using le_of_tendsto_of_tendsto he hp (Eventually.of_forall fun n=>hLower n r)

def comparisonVirtualScaledPotential (x Jref : ℝ) (H : ℝ→ℝ) : ℝ→ℝ :=
  fun t=>H (x*t)/(x^4*Jref)

theorem comparison_virtual_scaled_potential_derivative
    {x Jref a b : ℝ} (hx : 0 < x) (hJref : 0 < Jref) (H J G : ℝ→ℝ)
    (hDeriv : ∀ᵐ r,r∈Icc (x*a) (x*b)→HasDerivAt H (J r*G r) r) :
    ∀ᵐ t,t∈Icc a b→HasDerivAt (comparisonVirtualScaledPotential x Jref H)
      ((J (x*t)/Jref)*(G (x*t)/x^3)) t := by
  have hPull := (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) hx.ne').ae hDeriv
  filter_upwards [hPull] with t ht hti
  have htiX : x*t∈Icc (x*a) (x*b) := ⟨mul_le_mul_of_nonneg_left hti.1 hx.le,
    mul_le_mul_of_nonneg_left hti.2 hx.le⟩
  have hd := (ht (by simpa only [smul_eq_mul] using htiX)).comp t ((hasDerivAt_id t).const_mul x)
  have hh := hd.div_const (x^4*Jref)
  simp only [smul_eq_mul] at hh
  convert hh using 1
  · rfl
  · field_simp

theorem comparison_virtual_scaled_potential_lipschitz
    {x Jref a b KJ KG : ℝ} (hx : 0 < x) (hJref : 0 < Jref) (hab : a ≤ b)
    (hKJ : 0 ≤ KJ) (hKG : 0 ≤ KG) (H J G : ℝ→ℝ)
    (hH : AbsolutelyContinuousOnInterval H (x*a) (x*b))
    (hDeriv : ∀ᵐ r,r∈Icc (x*a) (x*b)→HasDerivAt H (J r*G r) r)
    (hJB : ∀r∈Icc (x*a) (x*b),|J r/Jref| ≤ KJ)
    (hGB : ∀r∈Icc (x*a) (x*b),|G r/x^3| ≤ KG) :
    LipschitzOnWith (KJ*KG).toNNReal (comparisonVirtualScaledPotential x Jref H) (Icc a b) := by
  let B := Jref*KJ*KG*x^3
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hbound : ∀ᵐ r,r∈Icc (x*a) (x*b)→‖J r*G r‖ ≤ B := by
    exact Eventually.of_forall fun r hr=>by
      have he : J r*G r=(J r/Jref)*(G r/x^3)*(Jref*x^3) := by field_simp
      rw [he,Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (mul_pos hJref (pow_pos hx 3))]
      have hh := mul_le_mul (hJB r hr) (hGB r hr) (abs_nonneg _) hKJ
      have hh2 := mul_le_mul_of_nonneg_right hh (mul_pos hJref (pow_pos hx 3)).le
      convert hh2 using 1
      dsimp only [B]
      ring
  have hLip := virtual_potential_lipschitz_of_ae_density_bound
    (mul_le_mul_of_nonneg_left hab hx.le) hB hH hDeriv hbound
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  have hsX : x*s∈Icc (x*a) (x*b) := ⟨mul_le_mul_of_nonneg_left hs.1 hx.le,mul_le_mul_of_nonneg_left hs.2 hx.le⟩
  have htX : x*t∈Icc (x*a) (x*b) := ⟨mul_le_mul_of_nonneg_left ht.1 hx.le,mul_le_mul_of_nonneg_left ht.2 hx.le⟩
  have hh := hLip.dist_le_mul (x*s) hsX (x*t) htX
  rw [Real.dist_eq,Real.dist_eq,←mul_sub,abs_mul,abs_of_pos hx,Real.coe_toNNReal _ hB] at hh
  rw [Real.dist_eq,comparisonVirtualScaledPotential,comparisonVirtualScaledPotential,
    ←sub_div,abs_div,abs_of_pos (mul_pos (pow_pos hx 4) hJref),Real.dist_eq,
    Real.coe_toNNReal _ (mul_nonneg hKJ hKG)]
  apply (div_le_iff₀ (mul_pos (pow_pos hx 4) hJref)).mpr
  have he : B*(x*|s-t|)=((KJ*KG)*|s-t|)*(x^4*Jref) := by dsimp only [B];ring
  exact hh.trans_eq he

theorem virtual_integrals_tendsto_of_L1
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (F : ℕ→Omega→ℝ) (f : Omega→ℝ) (hFi : ∀n,Integrable (F n) mu)
    (hfi : Integrable f mu)
    (hL1 : Tendsto (fun n=>∫t,|F n t-f t|∂mu) atTop (𝓝 0)) :
    Tendsto (fun n=>∫t,F n t∂mu) atTop (𝓝 (∫t,f t∂mu)) := by
  have hdiff : Tendsto (fun n=>(∫t,F n t∂mu)-(∫t,f t∂mu)) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ hL1
    intro n
    rw [←integral_sub (hFi n) hfi]
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun t=>F n t-f t)
  convert hdiff.add_const (∫t,f t∂mu) using 1
  · funext n
    ring
  · simp

theorem virtual_positive_mass_has_nearby_contact
    {alpha H k : ℝ→ℝ} {a b T : ℝ} {C : ℝ≥0} (hab : a < b)
    (ha : 0 ≤ a) (hT : 0 < T) (hend : b+2*T ≤ 1)
    (hAlpha : LipschitzOnWith C alpha (Icc a b))
    (hH : ContinuousOn H (Icc (0:ℝ) 1))
    (hfloor : ∀ᵐ r,r∈Icc a b→0 < H r→deriv alpha r=k r)
    (hmass : (∫r in a..b,k r) < alpha b-alpha a)
    (htravel : ∀l z : ℝ,0 ≤ l→z ≤ 1→l ≤ z→
      (∀t∈Ioo l z,H t < 0)→z-l ≤ T) :
    ∃z∈Ioc a (b+2*T),H z=0 := by
  obtain ⟨r,hr,hHr⟩ := virtual_positive_mass_has_nonpositive_anchor hab hAlpha hfloor hmass
  by_cases he : H r=0
  · exact ⟨r,⟨hr.1,by linarith [hr.2]⟩,he⟩
  have hneg : H r < 0 := lt_of_le_of_ne hHr he
  obtain ⟨z,hz,hHz⟩ := virtual_negative_point_near_zero hT (ha.trans hr.1.le)
    (by linarith [hr.2]) hH hneg htravel
  exact ⟨z,⟨hr.1.trans_le hz.1,by linarith [hz.2,hr.2]⟩,hHz⟩

theorem comparison_virtual_native_contact_in_mass_slab
    {N delta U L E d a b : ℝ} (hN : 0 < N) (hU : 0 < U) (hL : 0 < L)
    (hE : 0 < E) (hd : 0 < d) {alpha H k : ℝ→ℝ} {C : ℝ≥0}
    (hAlpha : LipschitzOnWith C alpha (Icc (0:ℝ) 1))
    (hMono : StrictMonoOn alpha (Icc (0:ℝ) 1))
    (hRange : ∀r∈Icc (0:ℝ) 1,alpha r∈Icc (0:ℝ) 1)
    (hH : ContinuousOn H (Icc (0:ℝ) 1))
    (hfloor : ∀ᵐ r,r∈Icc (0:ℝ) 1→0 < H r→deriv alpha r=k r)
    (hcap : ∀ᵐ r,r∈Icc (0:ℝ) 1→H r < 0→
      deriv alpha r=comparisonCap N delta U L E d (alpha r))
    (ha : 0 ≤ a) (hab : a < b)
    (hend : b+2*((L/N^delta)*Real.log ((1+U)/U)) ≤ 1)
    (hmass : (∫r in a..b,k r) < alpha b-alpha a) :
    ∃z∈Ioc a (b+2*((L/N^delta)*Real.log ((1+U)/U))),H z=0 := by
  let T := (L/N^delta)*Real.log ((1+U)/U)
  have hT : 0 < T := by
    apply mul_pos (div_pos hL (Real.rpow_pos_of_pos hN _))
    apply Real.log_pos
    exact (one_lt_div hU).mpr (by linarith)
  have hb : b ≤ 1 := by linarith
  have hfloorLocal : ∀ᵐ r,r∈Icc a b→0 < H r→deriv alpha r=k r := by
    filter_upwards [hfloor] with r hr hri
    exact hr ⟨ha.trans hri.1,hri.2.trans hb⟩
  have htravel : ∀l z : ℝ,0 ≤ l→z ≤ 1→l ≤ z→
      (∀t∈Ioo l z,H t < 0)→z-l ≤ T := by
    intro l z hl hz hlz hneg
    exact (potential_comparison_cap_interval_travel hN hU hL hE hd hAlpha hMono hRange hcap
      hl hz hlz hneg).2.1
  exact virtual_positive_mass_has_nearby_contact hab ha hT hend
    (hAlpha.mono (Icc_subset_Icc ha hb)) hH hfloorLocal hmass htravel

theorem virtual_uniform_potential_primitive_identified
    {a b : ℝ} (P : ℕ→BoundedContinuousFunction (Icc a b) ℝ)
    (p : BoundedContinuousFunction (Icc a b) ℝ) (F : ℕ→ℝ→ℝ) (f : ℝ→ℝ)
    (hP : Tendsto P atTop (𝓝 p))
    (hFi : ∀n,IntegrableOn (F n) (Icc a b)) (hfi : IntegrableOn f (Icc a b))
    (hL1 : Tendsto (fun n=>∫t in Icc a b,|F n t-f t|) atTop (𝓝 0))
    (hPrimitive : ∀(n : ℕ) (s t : Icc a b),s.val ≤ t.val→
      P n t-P n s=∫r in s.val..t.val,F n r) :
    ∀s t : Icc a b,s.val ≤ t.val→p t-p s=∫r in s.val..t.val,f r := by
  intro s t hst
  have hsub : Ioc s.val t.val⊆Icc a b := by
    intro r hr
    exact ⟨s.property.1.trans hr.1.le,hr.2.trans t.property.2⟩
  have hsubL1 : Tendsto (fun n=>∫r in Ioc s.val t.val,|F n r-f r|) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>integral_nonneg fun _=>abs_nonneg _) _ hL1
    intro n
    exact setIntegral_mono_set ((hFi n).sub hfi).abs
      (Eventually.of_forall fun _=>abs_nonneg _) (Eventually.of_forall fun r hr=>hsub hr)
  have hIlim := virtual_integrals_tendsto_of_L1 (volume.restrict (Ioc s.val t.val)) F f
    (fun n=>(hFi n).mono_set hsub) (hfi.mono_set hsub) hsubL1
  have hDiff := ((BoundedContinuousFunction.lipschitz_eval_const t).continuous.tendsto p |>.comp hP).sub
    ((BoundedContinuousFunction.lipschitz_eval_const s).continuous.tendsto p |>.comp hP)
  have hDiffI : Tendsto (fun n=>P n t-P n s) atTop (𝓝 (∫r in s.val..t.val,f r)) := by
    rw [intervalIntegral.integral_of_le hst]
    have he : (fun n=>P n t-P n s)=(fun n=>∫r in Ioc s.val t.val,F n r) := by
      funext n
      rw [hPrimitive n s t hst,intervalIntegral.integral_of_le hst]
    rw [he]
    exact hIlim
  exact tendsto_nhds_unique hDiff hDiffI

theorem comparison_virtual_scaled_potential_primitive
    {x Jref a b KJ KG : ℝ} (hx : 0 < x) (hJref : 0 < Jref) (hab : a ≤ b)
    (hKJ : 0 ≤ KJ) (hKG : 0 ≤ KG) (H J G : ℝ→ℝ)
    (hH : AbsolutelyContinuousOnInterval H (x*a) (x*b))
    (hDeriv : ∀ᵐ r,r∈Icc (x*a) (x*b)→HasDerivAt H (J r*G r) r)
    (hJB : ∀r∈Icc (x*a) (x*b),|J r/Jref| ≤ KJ)
    (hGB : ∀r∈Icc (x*a) (x*b),|G r/x^3| ≤ KG) :
    ∀s∈Icc a b,∀t∈Icc a b,s ≤ t→
      comparisonVirtualScaledPotential x Jref H t-comparisonVirtualScaledPotential x Jref H s=
        ∫r in s..t,(J (x*r)/Jref)*(G (x*r)/x^3) := by
  have hLip := comparison_virtual_scaled_potential_lipschitz hx hJref hab hKJ hKG H J G hH hDeriv hJB hGB
  have hD := comparison_virtual_scaled_potential_derivative hx hJref H J G hDeriv
  intro s hs t ht hst
  have hLipST : LipschitzOnWith (KJ*KG).toNNReal (comparisonVirtualScaledPotential x Jref H) (uIcc s t) := by
    rw [uIcc_of_le hst]
    exact hLip.mono (Icc_subset_Icc hs.1 ht.2)
  have hAC := hLipST.absolutelyContinuousOnInterval
  have hDST : ∀ᵐ r,r∈Icc s t→HasDerivAt (comparisonVirtualScaledPotential x Jref H)
      ((J (x*r)/Jref)*(G (x*r)/x^3)) r := by
    filter_upwards [hD] with r hr hri
    exact hr ⟨hs.1.trans hri.1,hri.2.trans ht.2⟩
  exact (potential_integral_eq_sub hst hAC hDST).symm

end OAI.SKFluctuations.LaplaceWindowFormalization
