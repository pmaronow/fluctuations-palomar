module

public import ComparisonActualHighWallOriginalTaylorSavedLocalThermalAlong
public import ComparisonActualHighWallCriticalThermalRadiusAlong
public import ComparisonActualHighWallCategoryOrders
public import ComparisonActualHighWallTargetRadiusFractionalPrices

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 30000000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def actualHighWallOriginalTaylorThermalRate
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (dim : ℕ→ℕ)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (Csource : ℝ) (n : ℕ) : ℝ :=
  (∫u in 0..Csource*(M n).data.d,
    Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
      (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2))/(M n).data.d^2+
  (M n).data.N^(-(actualMassSavingExponent m delta/256))+(M n).data.d^2

theorem actual_high_wall_original_taylor_thermal_rate_nonneg
    {m delta cl cu Az C0 Ct D Bclock Csource : ℝ}
    (dim : ℕ→ℕ)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCsource : 0 ≤ Csource) (n : ℕ) :
    0 ≤ actualHighWallOriginalTaylorThermalRate dim M Csource n := by
  have HJ : 0 ≤ (∫u in 0..Csource*(M n).data.d,
      Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)) :=
    intervalIntegral.integral_nonneg (mul_nonneg hCsource (M n).data.hd.le)
      (fun _ _=>Real.sqrt_nonneg _)
  unfold actualHighWallOriginalTaylorThermalRate
  exact add_nonneg (add_nonneg (div_nonneg HJ (sq_nonneg _))
    (Real.rpow_nonneg (M n).data.hN.le _)) (sq_nonneg _)

theorem actual_high_wall_original_taylor_thermal_rate_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock Csource : ℝ}
    (hCsource : 0 < Csource)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0)) :
    Tendsto (actualHighWallOriginalTaylorThermalRate dim M Csource) atTop (𝓝 0) := by
  have HJ:=ActualHighWallOverlapMinimum.actual_high_wall_critical_thermal_radius_tendsto_zero_along
    hCsource hm hdelta hroom hcl hcu hAz hC0 hCt hD dim hdim M hfixed hdlim hsRatio
  have hsave : 0 < actualMassSavingExponent m delta/256 :=
    div_pos (actualMassSavingExponent_pos hm hdelta) (by norm_num)
  have HN : Tendsto (fun n=>(M n).data.N^(-(actualMassSavingExponent m delta/256)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def,ActualHighWallData.N] using
      (tendsto_rpow_neg_atTop hsave).comp
        (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  change Tendsto (fun n=>actualHighWallOriginalTaylorThermalRate dim M Csource n) atTop (𝓝 0)
  simpa only [actualHighWallOriginalTaylorThermalRate,zero_add,zero_pow (by decide : 2 ≠ 0)]
    using (HJ.add HN).add (hdlim.pow 2)

theorem original_taylor_raw_local_thermal_le_fractional_reader_modulus
    (p : ℕ) {d Di I rho eta : ℝ} (hd : 0 < d) (hDi : 0 ≤ Di)
    (hrate : I/d^2+rho ≤ eta) :
    d^2*Di+d*I+rho*d^3 ≤ actualHighWallFractionalReaderModulus p d eta Di := by
  have hdiv : 0 ≤ Di/d := div_nonneg hDi hd.le
  have H8 := Real.rpow_nonneg hdiv ((8:ℝ)⁻¹)
  have H4 := Real.rpow_nonneg hdiv ((4:ℝ)⁻¹)
  have Hp := Real.rpow_nonneg hdiv ((p:ℝ)⁻¹)
  have Hinside : Di/d+I/d^2+rho ≤
      (Di/d)^((8:ℝ)⁻¹)+(Di/d)^((4:ℝ)⁻¹)+(Di/d)^((p:ℝ)⁻¹)+Di/d+eta := by
    linarith only [hrate,H8,H4,Hp]
  have Hscaled:=mul_le_mul_of_nonneg_left Hinside (pow_nonneg hd.le 3)
  have Heq : d^2*Di+d*I+rho*d^3=d^3*(Di/d+I/d^2+rho) := by
    field_simp [hd.ne']
  rw [Heq]
  exact Hscaled

theorem eventually_actual_high_wall_original_Taylor_fractional_reader_price_along
    (p : ℕ) (Bclock Ctarget Csource c : ℝ)
    (hCtarget : 0 < Ctarget) (hgap : Ctarget < Csource)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc : 0 < c) (hcout : cu*Az < c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0)) :
    ∃Ctaylor : ℝ,0 < Ctaylor ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀v∈us,v.val ≤ 1) → (∀v∈uniformMasses L,v∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠk in atTop,
        let as:=finiteCutMasses us k
        ∀i U : ℕ,i < U → U ≤ as.length →
          partitionPoint 0 as i ≤ Ctarget*(M n).data.d →
          partitionPoint 0 as U ≤ Csource*(M n).data.d →
          2*c*(M n).data.d ≤ partitionPoint 0 as U →
          |actualGeneralTargetOriginalTaylorPart (n:=dim n) (M n).bf (M n).hf as i U| ≤
            Ctaylor*actualHighWallFractionalReaderModulus p (M n).data.d
              (actualHighWallOriginalTaylorThermalRate dim M Csource n)
              (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ)) := by
  have hCsource : 0 < Csource := hCtarget.trans hgap
  obtain ⟨q,dOrder,_etaOrder,hq,hdOrder,hOrder,htheta1,htheta2,hdeficit,_hetaOrder,_hetaOrderm⟩:=
    actual_high_wall_category_orders hm hdelta
  obtain ⟨Ctaylor,hCtaylor,HT⟩:=eventually_actual_high_wall_original_target_Taylor_saved_local_thermal_profile_along
    dOrder hdOrder q hq htheta1 htheta2 hOrder Bclock Csource c hCsource.le
    hdeficit hm hdelta hroom hcl hcu hAz hC0 hCt hc hcout dim hdim M hfixed hdlim hsRatio
  have Hunit : ∀ᶠn in atTop,Csource*(M n).data.d ≤ 1 :=
    (hdlim.const_mul Csource).eventually (eventually_le_nhds (by simp))
  refine ⟨Ctaylor,hCtaylor,?_⟩
  filter_upwards [HT,Hunit] with n hn hunit
  intro L us hus hret hmesh
  filter_upwards [hn L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro i U hi hU _htarget hsource hsourceLow
  have Hraw:=hk i U hi hU hunit hsource hsourceLow
  have hDi : 0 ≤ nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf
      (finiteCutMasses us k) i+1/(dim n+1:ℕ) :=
    add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have Hmodulus:=original_taylor_raw_local_thermal_le_fractional_reader_modulus p (M n).data.hd hDi
    (show (∫u in 0..Csource*(M n).data.d,
        Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
          (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2))/(M n).data.d^2+
      (M n).data.N^(-(actualMassSavingExponent m delta/256)) ≤
        actualHighWallOriginalTaylorThermalRate dim M Csource n from
      le_add_of_nonneg_right (sq_nonneg (M n).data.d))
  exact Hraw.trans (mul_le_mul_of_nonneg_left Hmodulus hCtaylor.le)

theorem actual_high_wall_fractional_reader_modulus_mono_rate
    (p : ℕ) {d Di eta eta' : ℝ} (hd : 0 ≤ d) (heta : eta ≤ eta') :
    actualHighWallFractionalReaderModulus p d eta Di ≤
      actualHighWallFractionalReaderModulus p d eta' Di := by
  unfold actualHighWallFractionalReaderModulus
  exact mul_le_mul_of_nonneg_left (add_le_add_right heta _) (pow_nonneg hd 3)

end OAI.SKFluctuations.LaplaceWindowFormalization
