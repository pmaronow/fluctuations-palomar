module

public import ComparisonActualHighWallTargetRadiusContinuousModulus
public import ComparisonRadiusFractionalRootDomination
public import ComparisonActualHighWallRadiusFractionalScalarClosureEventualBandDimAlong
public import ComparisonActualHighWallOriginalLowRadius
public import ComparisonActualHighWallOmittedSiteCubic

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

theorem retained_low_with_site_price_of_low_cut_bound
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Ccut Clow : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (us : List PositiveMass) (hus : ∀v∈us,v.val ≤ 1)
    (hsite : (1:ℝ)/(n+1:ℕ) ≤ M.data.d)
    (Hlow : ∀ᶠk : ℕ in atTop,
      let as:=finiteCutMasses us k
      ∀j,j ≤ as.length → partitionPoint 0 as j ≤ Ccut*M.data.d →
        nativeOriginalCutLowErrorRadius n M.bf M.hf as j ≤ Clow*M.data.d) :
    ∀ᶠk : ℕ in atTop,∀u∈us,u.val ≤ Ccut*M.data.d →
      nativeOriginalCutLowErrorRadius n M.bf M.hf (finiteCutMasses us k)
        (retainedMassPrefixIndex u.val (finiteCutMasses us k))+1/(n+1:ℕ) ≤ 
          (Clow+1)*M.data.d := by
  filter_upwards [Hlow] with k hk
  intro u hu humass
  let as:=finiteCutMasses us k
  have ho:=finiteCutMasses_ordered us hus k
  have hmass : partitionPoint 0 as (retainedMassPrefixIndex u.val as) ≤ Ccut*M.data.d := by
    rw [nativeRetainedCut_partitionPoint as ho u (finiteCutMasses_nodes us k hu)]
    exact humass
  have H:=hk _ (retainedMassPrefixIndex_le_length u.val as) hmass
  nlinarith only [H,hsite]

theorem eventually_actual_high_wall_retained_low_with_site_price_along
    (Bclock Ccut : ℝ) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃Clinear : ℝ,1 ≤ Clinear ∧ ∀ᶠn in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀v∈us,v.val ≤ 1) → (∀v∈uniformMasses L,v∈us) →
        ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk in atTop,∀u∈us,u.val ≤ Ccut*M.data.d →
        nativeOriginalCutLowErrorRadius (dim n) M.bf M.hf (finiteCutMasses us k)
          (retainedMassPrefixIndex u.val (finiteCutMasses us k))+1/(dim n+1:ℕ) ≤ 
            Clinear*M.data.d := by
  obtain ⟨Clow,hClow,HLow⟩:=eventually_actual_high_wall_original_low_error_radius_bigO
    (D:=D) Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Clow+1,by linarith only [hClow],?_⟩
  filter_upwards [hdim.eventually HLow,
    hdim.eventually (eventually_actual_high_wall_omitted_product_cubic_cost
      (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
      hm hC0)] with n hnlow hnsite
  intro M hfixed L us hus hret hmesh
  have hsite4 : (1:ℝ)/(dim n+1:ℕ) ≤ M.data.d^4 := by
    have H:=mul_le_mul_of_nonneg_right (hnsite M hfixed) M.data.hd.le
    convert H using 1 <;> field_simp [M.data.hd.ne']
  have hd3 : M.data.d^3 ≤ 1 := pow_le_one₀ M.data.hd.le M.data.hd1
  have hd4 : M.data.d^4 ≤ M.data.d := by
    nlinarith only [mul_le_mul_of_nonneg_right hd3 M.data.hd.le]
  exact retained_low_with_site_price_of_low_cut_bound M us hus (hsite4.trans hd4)
    (hnlow M hfixed L us hus hret hmesh)

def actualHighWallFractionalReaderModulus (p : ℕ) (d eta x : ℝ) : ℝ :=
  d^3*((x/d)^((8:ℝ)⁻¹)+(x/d)^((4:ℝ)⁻¹)+
    (x/d)^((p:ℝ)⁻¹)+x/d+eta)

theorem actual_high_wall_fractional_reader_modulus_continuous
    (p : ℕ) (d eta : ℝ) :
    Continuous (actualHighWallFractionalReaderModulus p d eta) := by
  have H8 : Continuous (fun x : ℝ => (x/d)^((8:ℝ)⁻¹)) :=
    (Real.continuous_rpow_const (by positivity)).comp (continuous_id.div_const d)
  have H4 : Continuous (fun x : ℝ => (x/d)^((4:ℝ)⁻¹)) :=
    (Real.continuous_rpow_const (by positivity)).comp (continuous_id.div_const d)
  have Hp : Continuous (fun x : ℝ => (x/d)^((p:ℝ)⁻¹)) :=
    (Real.continuous_rpow_const (by positivity)).comp (continuous_id.div_const d)
  exact ((((H8.add H4).add Hp).add (continuous_id.div_const d)).add
    continuous_const).const_mul (d^3)

theorem actual_high_wall_fractional_reader_modulus_nonneg
    (p : ℕ) {d eta x : ℝ} (hd : 0 ≤ d) (heta : 0 ≤ eta) (hx : 0 ≤ x) :
    0 ≤ actualHighWallFractionalReaderModulus p d eta x := by
  unfold actualHighWallFractionalReaderModulus
  have hxd := div_nonneg hx hd
  positivity

theorem radius_fractional_reader_linear_absorption
    {f C eta : ℝ} (hf : 0 ≤ f) (hC : 1 ≤ C) (hfC : f ≤ C)
    (p : ℕ) (hp : 0 < p) :
    f^((8:ℝ)⁻¹)+f^((4:ℝ)⁻¹)+f^((p:ℝ)⁻¹)+f+eta  ≤ 
      (1+C)*(f^((8:ℝ)⁻¹)+f^((4:ℝ)⁻¹)+f^((p:ℝ)⁻¹))+eta := by
  have hpp : (0:ℝ) < p := by exact_mod_cast hp
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp
  have H := radius_bounded_linear_defect_le_fractional_envelope hf hC hfC
    (inv_pos.mpr hpp) (by simpa only [one_div] using
      (div_le_one₀ hpp).mpr hp1)
  have H8 : 0 ≤ f^((8:ℝ)⁻¹) := Real.rpow_nonneg hf _
  have HC : 0 ≤ C := zero_le_one.trans hC
  nlinarith only [H,mul_nonneg HC H8]

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem literal_radius_band_mass_le
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : M.xs=M.data.d) (hcu : 0 ≤ cu)
    {r b : ℝ} (hr1 : r ≤ 1) (hrb : r ≤ M.xs*b) :
    M.alpha.val.val r ≤ (cu*max b Az)*M.data.d := by
  let t:=max r M.z
  have ht : t∈Icc M.z 1 :=
    ⟨le_max_right r M.z,max_le hr1 M.hz.2⟩
  have htbound : t ≤ max b Az*M.xs := by
    apply max_le
    · have H:=mul_le_mul_of_nonneg_right (le_max_left b Az) M.hxs.le
      nlinarith only [hrb,H]
    · exact M.hzxs.trans
        (mul_le_mul_of_nonneg_right (le_max_right b Az) M.hxs.le)
  have Hmass:=(M.alpha.val.property.2 (le_max_left r M.z)).trans (M.regular t ht).2
  have H:=Hmass.trans (mul_le_mul_of_nonneg_left htbound hcu)
  simpa only [hfixed,mul_assoc] using H

theorem literal_radius_low_with_site_le_of_retained_prices
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (r C : ℝ) (u : PositiveMass) (huval : u.val=M.alpha.val.val r)
    (us : List PositiveMass) (hus : ∀v∈us,v.val ≤ 1) (hu : u∈us)
    (Hlow : ∀ᶠk : ℕ in atTop,
      nativeOriginalCutLowErrorRadius n M.bf M.hf (finiteCutMasses us k)
        (retainedMassPrefixIndex u.val (finiteCutMasses us k))+1/(n+1:ℕ) ≤ C*M.data.d) :
    (Real.sqrt (M.wallRadiusPointDefect r)+1/M.data.N)/M.data.d ≤ C := by
  have Hrad := (native_original_retained_target_low_radius_tendsto n M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) us hus u hu).add_const
      (1/(n+1:ℕ):ℝ)
  have H := le_of_tendsto Hrad Hlow
  rw [huval] at H
  apply (div_le_iff₀ M.data.hd).mpr
  simpa only [ActualHighWallOverlapMinimum.wallRadiusPointDefect,
    ActualHighWallOverlapMinimum.radiusB,ActualHighWallOverlapMinimum.radiusS,
    ActualHighWallData.N] using H

theorem actual_original_target_radius_fractional_modulus_of_retained_prices
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (p : ℕ) (hp : 0 < p) (r : ℝ) (hr : r∈Icc M.data.rmin 1)
    (Cm Cr Ctaylor Clinear eta : ℝ)
    (hCr : 0 ≤ Cr) (hCtaylor : 0 ≤ Ctaylor) (hClinear : 1 ≤ Clinear) (heta : 0 ≤ eta)
    (u : PositiveMass) (huval : u.val=M.alpha.val.val r)
    (us : List PositiveMass) (hus : ∀v∈us,v.val ≤ 1) (hu : u∈us)
    (U : ℕ→ℕ)
    (Hprice : ∀ᶠk : ℕ in atTop,
      let as:=finiteCutMasses us k
      let i:=retainedMassPrefixIndex u.val as
      i < U k ∧ U k ≤ as.length ∧
      |actualGeneralTargetOriginalMeanCorrection (n:=n) M.bf M.hf as i (U k)| ≤ 
        Cm*M.data.d^4 ∧
      |actualGeneralTargetLongitudinalResponse (n:=n) M.bf M.hf as i (U k)| ≤ 
        Cr*actualHighWallFractionalReaderModulus p M.data.d eta
          (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)) ∧
      |actualGeneralTargetOriginalTaylorPart (n:=n) M.bf M.hf as i (U k)| ≤ 
        Ctaylor*actualHighWallFractionalReaderModulus p M.data.d eta
          (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)))
    (Hlow : ∀ᶠk : ℕ in atTop,
      nativeOriginalCutLowErrorRadius n M.bf M.hf (finiteCutMasses us k)
        (retainedMassPrefixIndex u.val (finiteCutMasses us k))+1/(n+1:ℕ) ≤ Clinear*M.data.d) :
    |M.radiusS r-
      scalarCovarianceResponse M.data.hTpos (M.data.scalarMassProfile M.alpha)
        (actualMixedClock (n+1) M.bf M.hf (M.alpha.val.val r))| ≤ 
      (2*max Bclock 0*Cr+Ctaylor)*(1+Clinear)*M.data.d^3*(
        (((Real.sqrt (M.wallRadiusPointDefect r)+1/M.data.N)/M.data.d)^((8:ℝ)⁻¹))+
        (((Real.sqrt (M.wallRadiusPointDefect r)+1/M.data.N)/M.data.d)^((4:ℝ)⁻¹))+
        (((Real.sqrt (M.wallRadiusPointDefect r)+1/M.data.N)/M.data.d)^((p:ℝ)⁻¹)))+
      (Cm*M.data.d+(2*max Bclock 0*Cr+Ctaylor)*eta)*M.data.d^3 := by
  let f := (Real.sqrt (M.wallRadiusPointDefect r)+1/M.data.N)/M.data.d
  let roots := f^((8:ℝ)⁻¹)+f^((4:ℝ)⁻¹)+f^((p:ℝ)⁻¹)
  let A := 2*max Bclock 0*Cr+Ctaylor
  have hf : 0 ≤ f := div_nonneg
    (add_nonneg (Real.sqrt_nonneg _) (one_div_nonneg.mpr M.data.hN.le)) M.data.hd.le
  have hfC : f ≤ Clinear := literal_radius_low_with_site_le_of_retained_prices
    M r Clinear u huval us hus hu Hlow
  have Hlinear := radius_fractional_reader_linear_absorption (eta:=eta) hf hClinear hfC p hp
  have Hreader := M.actual_original_target_radius_continuous_modulus r hr
    (actualHighWallFractionalReaderModulus p M.data.d eta)
    (actual_high_wall_fractional_reader_modulus_continuous _ _ _)
    (fun x hx => actual_high_wall_fractional_reader_modulus_nonneg p M.data.hd.le heta hx)
    hCr u huval us hus hu U Hprice
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hcoef : 2*M.data.T*Cr+Ctaylor ≤ A := by
    have H := M.hT.trans (le_max_left Bclock 0)
    dsimp only [A]
    nlinarith only [mul_le_mul_of_nonneg_right H hCr]
  have hP := actual_high_wall_fractional_reader_modulus_nonneg p M.data.hd.le heta
    (add_nonneg (Real.sqrt_nonneg (M.wallRadiusPointDefect r)) (one_div_nonneg.mpr M.data.hN.le))
  have Hcoef := mul_le_mul_of_nonneg_right hcoef hP
  have Hscaled := mul_le_mul_of_nonneg_left Hlinear (mul_nonneg hA (pow_nonneg M.data.hd.le 3))
  dsimp only [actualHighWallFractionalReaderModulus] at Hreader Hcoef
  change |M.radiusS r-
    scalarCovarianceResponse M.data.hTpos (M.data.scalarMassProfile M.alpha)
      (actualMixedClock (n+1) M.bf M.hf (M.alpha.val.val r))| ≤ 
    Cm*M.data.d^4+(2*M.data.T*Cr+Ctaylor)*(M.data.d^3*(roots+f+eta)) at Hreader
  change (2*M.data.T*Cr+Ctaylor)*(M.data.d^3*(roots+f+eta)) ≤ 
    A*(M.data.d^3*(roots+f+eta)) at Hcoef
  change f^((8:ℝ)⁻¹)+f^((4:ℝ)⁻¹)+f^((p:ℝ)⁻¹)+f+eta ≤ 
    (1+Clinear)*roots+eta at Hlinear
  change A*M.data.d^3*(roots+f+eta) ≤ 
    A*M.data.d^3*((1+Clinear)*roots+eta) at Hscaled
  have Hraw :
      |M.radiusS r-
        scalarCovarianceResponse M.data.hTpos (M.data.scalarMassProfile M.alpha)
          (actualMixedClock (n+1) M.bf M.hf (M.alpha.val.val r))| ≤ 
        Cm*M.data.d^4+A*M.data.d^3*((1+Clinear)*roots+eta) := by
    exact Hreader.trans (by nlinarith only [Hcoef,Hscaled])
  calc
    _  ≤  Cm*M.data.d^4+A*M.data.d^3*((1+Clinear)*roots+eta) := Hraw
    _ = _ := by dsimp only [A,roots,f]; ring

end ActualHighWallOverlapMinimum

def ActualHighWallLiteralRadiusFractionalReaderPrices
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (p : ℕ) (Cm Cr Ctaylor Clinear eta r : ℝ) : Prop :=
  ∃u : PositiveMass, u.val=M.alpha.val.val r ∧
  ∃us : List PositiveMass, (∀v∈us,v.val ≤ 1) ∧ u∈us ∧
  ∃U : ℕ→ℕ,
    (∀ᶠk : ℕ in atTop,
      let as:=finiteCutMasses us k
      let i:=retainedMassPrefixIndex u.val as
      i < U k ∧ U k ≤ as.length ∧
      |actualGeneralTargetOriginalMeanCorrection (n:=n) M.bf M.hf as i (U k)| ≤ 
        Cm*M.data.d^4 ∧
      |actualGeneralTargetLongitudinalResponse (n:=n) M.bf M.hf as i (U k)| ≤ 
        Cr*actualHighWallFractionalReaderModulus p M.data.d eta
          (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)) ∧
      |actualGeneralTargetOriginalTaylorPart (n:=n) M.bf M.hf as i (U k)| ≤ 
        Ctaylor*actualHighWallFractionalReaderModulus p M.data.d eta
          (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))) ∧
    (∀ᶠk : ℕ in atTop,
      nativeOriginalCutLowErrorRadius n M.bf M.hf (finiteCutMasses us k)
        (retainedMassPrefixIndex u.val (finiteCutMasses us k))+1/(n+1:ℕ) ≤ Clinear*M.data.d)

def ActualHighWallLiteralRadiusCalibratedFractionalReaderPrices
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (p : ℕ) (Cm Cr Ctaylor eta r : ℝ) : Prop :=
  ∃u : PositiveMass, u.val=M.alpha.val.val r ∧
  ∃us : List PositiveMass, (∀v∈us,v.val ≤ 1) ∧ u∈us ∧
  ∃L : ℕ, (∀v∈uniformMasses L,v∈us) ∧ ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs ∧
  ∃U : ℕ→ℕ,
    ∀ᶠk : ℕ in atTop,
      let as:=finiteCutMasses us k
      let i:=retainedMassPrefixIndex u.val as
      i < U k ∧ U k ≤ as.length ∧
      |actualGeneralTargetOriginalMeanCorrection (n:=n) M.bf M.hf as i (U k)| ≤ 
        Cm*M.data.d^4 ∧
      |actualGeneralTargetLongitudinalResponse (n:=n) M.bf M.hf as i (U k)| ≤ 
        Cr*actualHighWallFractionalReaderModulus p M.data.d eta
          (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)) ∧
      |actualGeneralTargetOriginalTaylorPart (n:=n) M.bf M.hf as i (U k)| ≤ 
        Ctaylor*actualHighWallFractionalReaderModulus p M.data.d eta
          (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))

theorem actual_high_wall_literal_radius_fractional_pointwise_of_reader_prices
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (p : ℕ) (hp : 0 < p) (r : ℝ) (hr : r∈Icc M.data.rmin 1)
    (Cm Cr Ctaylor Clinear eta : ℝ)
    (hCr : 0 ≤ Cr) (hCtaylor : 0 ≤ Ctaylor) (hClinear : 1 ≤ Clinear) (heta : 0 ≤ eta)
    (Hprice : ActualHighWallLiteralRadiusFractionalReaderPrices M p Cm Cr Ctaylor Clinear eta r) :
    |M.radiusS r-
      scalarCovarianceResponse M.data.hTpos (M.data.scalarMassProfile M.alpha)
        (actualMixedClock (n+1) M.bf M.hf (M.alpha.val.val r))| ≤ 
      (2*max Bclock 0*Cr+Ctaylor)*(1+Clinear)*M.data.d^3*(
        (((Real.sqrt (M.wallRadiusPointDefect r)+1/M.data.N)/M.data.d)^((8:ℝ)⁻¹))+
        (((Real.sqrt (M.wallRadiusPointDefect r)+1/M.data.N)/M.data.d)^((4:ℝ)⁻¹))+
        (((Real.sqrt (M.wallRadiusPointDefect r)+1/M.data.N)/M.data.d)^((p:ℝ)⁻¹)))+
      (Cm*M.data.d+(2*max Bclock 0*Cr+Ctaylor)*eta)*M.data.d^3 := by
  obtain ⟨u,huval,us,hus,hu,U,Hprices,Hlow⟩:=Hprice
  exact M.actual_original_target_radius_fractional_modulus_of_retained_prices
    p hp r hr Cm Cr Ctaylor Clinear eta hCr hCtaylor hClinear heta
    u huval us hus hu U Hprices Hlow

theorem actual_high_wall_fractional_radius_scalar_gap_of_retained_reader_prices_along
    (p : ℕ) (hp : 0 < p) (Bclock : ℝ)
    {m delta cl cu Az C0 Ct D a b ca T Cm Cr Ctaylor Clinear : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hab : a ≤ b) (hca : 0 < ca) (hT : 0 < T)
    (hCm : 0 ≤ Cm) (hCr : 0 ≤ Cr) (hCtaylor : 0 ≤ Ctaylor) (hClinear : 1 ≤ Clinear)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hTeq : ∀n,(M n).data.T=T)
    (hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hband : ∀ᶠn in atTop,(M n).data.rmin < (M n).xs*a ∧
      (M n).xs*b ≤ 1 ∧ ca*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*a))
    (eta : ℕ→ℝ) (heta0 : ∀ᶠn in atTop,0 ≤ eta n) (heta : Tendsto eta atTop (𝓝 0))
    (Hprice : ∀ᶠn in atTop,∀r∈Ioo ((M n).xs*a) ((M n).xs*b),
      ActualHighWallLiteralRadiusFractionalReaderPrices (M n) p Cm Cr Ctaylor Clinear (eta n) r)
    (dphys : ℕ→ℕ) (e : ∀n,Fin (dphys n+1)≃FeatureIndex (dim n+1)) :
    Tendsto (fun n=>(∫r in Ioo ((M n).xs*a) ((M n).xs*b),
      |(M n).radiusS r-
        scalarCovarianceResponse hT ((M n).data.scalarMassProfile (M n).alpha)
          (actualMixedClock (dim n+1) (M n).bf (M n).hf ((M n).alpha.val.val r))|)/
        (M n).xs^4) atTop (𝓝 0) := by
  let A:=2*max Bclock 0*Cr+Ctaylor
  let etaOut:=fun n=>Cm*(M n).xs+A*eta n
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hpointConstant : 0 ≤ A*(1+Clinear) :=
    mul_nonneg hA (by linarith only [hClinear])
  have herror : Tendsto etaOut atTop (𝓝 0) := by
    simpa only [etaOut,mul_zero,zero_add] using
      (hxlim.const_mul Cm).add (heta.const_mul A)
  have herror0 : ∀ᶠn in atTop,0 ≤ etaOut n := by
    filter_upwards [heta0] with n hn
    exact add_nonneg (mul_nonneg hCm (M n).hxs.le) (mul_nonneg hA hn)
  have hpoint : ∀ᶠn in atTop,∀r∈Ioo ((M n).xs*a) ((M n).xs*b),
      |(M n).radiusS r-
        scalarCovarianceResponse hT ((M n).data.scalarMassProfile (M n).alpha)
          (actualMixedClock (dim n+1) (M n).bf (M n).hf ((M n).alpha.val.val r))| ≤ 
      A*(1+Clinear)*(M n).xs^3*(
        (((Real.sqrt ((M n).wallRadiusPointDefect r)+1/(M n).data.N)/(M n).xs)^((8:ℝ)⁻¹))+
        (((Real.sqrt ((M n).wallRadiusPointDefect r)+1/(M n).data.N)/(M n).xs)^((4:ℝ)⁻¹))+
        (((Real.sqrt ((M n).wallRadiusPointDefect r)+1/(M n).data.N)/(M n).xs)^((p:ℝ)⁻¹)))+
        etaOut n*(M n).xs^3 := by
    filter_upwards [Hprice,hband,heta0] with n hn hbn hen
    intro r hr
    have hrwall : r∈Icc (M n).data.rmin 1 :=
      ⟨hbn.1.le.trans hr.1.le,hr.2.le.trans hbn.2.1⟩
    have H:=actual_high_wall_literal_radius_fractional_pointwise_of_reader_prices
      (M n) p hp r hrwall Cm Cr Ctaylor Clinear (eta n)
      hCr hCtaylor hClinear hen (hn r hr)
    simpa only [←hfixed n,hTeq n,A,etaOut] using H
  exact actual_high_wall_fractional_radius_eventual_mass_band_scalar_gap_dim_tendsto_zero
    p hp Bclock hm hdelta hmargin hcl hcu hAz hC0 hCt hab hca hpointConstant hT
    dim hdim M hfixed hband (fun n=>(M n).data.scalarMassProfile (M n).alpha)
    etaOut herror0 herror hpoint dphys e

theorem actual_high_wall_fractional_radius_scalar_gap_of_calibrated_reader_prices_along
    (p : ℕ) (hp : 0 < p) (Bclock : ℝ)
    {m delta cl cu Az C0 Ct D a b ca T Cm Cr Ctaylor : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hab : a ≤ b) (hca : 0 < ca) (hT : 0 < T)
    (hCm : 0 ≤ Cm) (hCr : 0 ≤ Cr) (hCtaylor : 0 ≤ Ctaylor)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hTeq : ∀n,(M n).data.T=T)
    (hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hband : ∀ᶠn in atTop,(M n).data.rmin < (M n).xs*a ∧
      (M n).xs*b ≤ 1 ∧ ca*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*a))
    (eta : ℕ→ℝ) (heta0 : ∀ᶠn in atTop,0 ≤ eta n) (heta : Tendsto eta atTop (𝓝 0))
    (Hprice : ∀ᶠn in atTop,∀r∈Ioo ((M n).xs*a) ((M n).xs*b),
      ActualHighWallLiteralRadiusCalibratedFractionalReaderPrices (M n) p Cm Cr Ctaylor (eta n) r)
    (dphys : ℕ→ℕ) (e : ∀n,Fin (dphys n+1)≃FeatureIndex (dim n+1)) :
    Tendsto (fun n=>(∫r in Ioo ((M n).xs*a) ((M n).xs*b),
      |(M n).radiusS r-
        scalarCovarianceResponse hT ((M n).data.scalarMassProfile (M n).alpha)
          (actualMixedClock (dim n+1) (M n).bf (M n).hf ((M n).alpha.val.val r))|)/
        (M n).xs^4) atTop (𝓝 0) := by
  let Ccut:=cu*max b Az
  have hCcut : 0 ≤ Ccut := mul_nonneg hcu.le (hAz.trans (le_max_right b Az))
  obtain ⟨Clinear,hClinear,HLow⟩:=eventually_actual_high_wall_retained_low_with_site_price_along
    (D:=D) Bclock Ccut hCcut hm hdelta (by linarith only [hmargin,hdelta])
    hcl hcu hAz hC0 hCt dim hdim
  have Hprices : ∀ᶠn in atTop,∀r∈Ioo ((M n).xs*a) ((M n).xs*b),
      ActualHighWallLiteralRadiusFractionalReaderPrices (M n) p Cm Cr Ctaylor Clinear (eta n) r := by
    filter_upwards [Hprice,HLow,hband] with n hn hnlow hbn
    intro r hr
    obtain ⟨u,huval,us,hus,hu,L,hret,hmesh,U,Hfinite⟩:=hn r hr
    have humass : u.val ≤ Ccut*(M n).data.d := by
      rw [huval]
      exact (M n).literal_radius_band_mass_le (hfixed n) hcu.le
        (hr.2.le.trans hbn.2.1) hr.2.le
    have Hlow : ∀ᶠk : ℕ in atTop,
        nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf (finiteCutMasses us k)
          (retainedMassPrefixIndex u.val (finiteCutMasses us k))+1/(dim n+1:ℕ) ≤ 
            Clinear*(M n).data.d := by
      filter_upwards [hnlow (M n) (hfixed n) L us hus hret hmesh] with k hk
      exact hk u hu humass
    exact ⟨u,huval,us,hus,hu,U,Hfinite,Hlow⟩
  exact actual_high_wall_fractional_radius_scalar_gap_of_retained_reader_prices_along
    p hp Bclock hm hdelta hmargin hcl hcu hAz hC0 hCt hab hca hT
    hCm hCr hCtaylor hClinear dim hdim M hfixed hTeq hxlim hband
    eta heta0 heta Hprices dphys e

end OAI.SKFluctuations.LaplaceWindowFormalization
