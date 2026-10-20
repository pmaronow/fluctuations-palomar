module

public import ComparisonActualHighWallTargetMassContinuousModulus
public import ComparisonActualHighWallOriginalMassFractionalFactor

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory
open scoped Topology BigOperators
set_option autoImplicit false

def finitePowerMassTargetModulus
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p : ι → ℕ) (c : ι → ℝ) (d a J : ℝ) (x : ℝ) : ℝ :=
  d^3*(a+∑j∈s,c j*(x/d)^((p j:ℝ)⁻¹))+d^2*x+d*J

theorem finitePowerMassTargetModulus_continuous
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p : ι → ℕ) (c : ι → ℝ) (d a J : ℝ)
    (_hp : ∀j∈s,0<p j) :
    Continuous (finitePowerMassTargetModulus s p c d a J) := by
  have hsum : Continuous
      (fun x : ℝ => ∑j∈s,c j*(x/d)^((p j:ℝ)⁻¹)) := by
    apply continuous_finsetSum
    intro j hj
    have hExp : 0≤((p j:ℝ)⁻¹) := by positivity
    exact continuous_const.mul
      ((Real.continuous_rpow_const hExp).comp (continuous_id.div_const d))
  unfold finitePowerMassTargetModulus
  exact (((continuous_const.add hsum).const_mul (d^3)).add
    (continuous_id.const_mul (d^2))).add continuous_const

theorem finitePowerMassTargetModulus_nonneg
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p : ι → ℕ) (c : ι → ℝ) {d a J x : ℝ}
    (hd : 0 < d) (ha : 0≤a) (hJ : 0≤J)
    (hc : ∀j∈s,0≤c j) (hx : 0≤x) :
    0≤finitePowerMassTargetModulus s p c d a J x := by
  have hsum : 0≤∑j∈s,c j*(x/d)^((p j:ℝ)⁻¹) := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (hc j hj)
      (Real.rpow_nonneg (div_nonneg hx hd.le) _)
  unfold finitePowerMassTargetModulus
  exact add_nonneg
    (add_nonneg (mul_nonneg (pow_nonneg hd.le 3) (add_nonneg ha hsum))
      (mul_nonneg (pow_nonneg hd.le 2) hx))
    (mul_nonneg hd.le hJ)

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal BigOperators
set_option autoImplicit false

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def originalMassThermalRadius
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (u : ℝ) : ℝ :=
  Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
    (orderedPathS (n+1) M.bf M.hf u)^2)

def originalMassScalarResidual
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (u : ℝ) : ℝ :=
  orderedPathS (n+1) M.bf M.hf u-
    scalarCovarianceResponse M.data.hTpos (M.data.scalarMassProfile M.alpha)
      (actualMixedClock (n+1) M.bf M.hf u)

end ActualHighWallOverlapMinimum

theorem actual_high_wall_critical_mass_pointwise_of_uniform_finite_FOUR_prices
    {m delta cl cu Az C0 Ct D Bclock Ccut Cm Cr Ctaylor Cbudget : ℝ}
    (hCcut : 0 < Ccut) (hCr : 0≤Cr) (hCbudget : 0<Cbudget)
    (hCm : Cm≤Cbudget)
    (dim : ℕ → ℕ)
    (M : (n : ℕ) → ActualHighWallOverlapMinimum
      (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p : ι → ℕ) (hp : ∀j∈s,0<p j)
    (c : ι → ℝ) (hc : ∀j∈s,0≤c j)
    (a : ℕ → ℝ) (ha : ∀ᶠn in atTop,0≤a n)
    (hcoeff : ∀ᶠn in atTop,
      2*(M n).data.T*Cr+Ctaylor≤Cbudget)
    (Hprice : ∀ᶠn in atTop,
      ∀u : PositiveMass,u.val<Ccut*(M n).data.d →
        let d := (M n).data.d
        let J := ∫v in 0..Ccut*d,(M n).originalMassThermalRadius v
        let P := finitePowerMassTargetModulus s p c d (a n) J
        ∃us : List PositiveMass,∃_hus : ∀v∈us,v.val≤1,
        ∃_hu : u∈us,∃U : ℕ→ℕ,
        ∀ᶠk : ℕ in atTop,
          let as:=finiteCutMasses us k
          let i:=retainedMassPrefixIndex u.val as
          i<U k ∧ U k≤as.length ∧
          |actualGeneralTargetOriginalMeanCorrection (n:=dim n)
            (M n).bf (M n).hf as i (U k)|≤Cm*d^4 ∧
          |actualGeneralTargetLongitudinalResponse (n:=dim n)
            (M n).bf (M n).hf as i (U k)|≤
            Cr*P (nativeOriginalCutLowErrorRadius (dim n)
              (M n).bf (M n).hf as i+1/(dim n+1:ℕ)) ∧
          |actualGeneralTargetOriginalTaylorPart (n:=dim n)
            (M n).bf (M n).hf as i (U k)|≤
            Ctaylor*P (nativeOriginalCutLowErrorRadius (dim n)
              (M n).bf (M n).hf as i+1/(dim n+1:ℕ))) :
    ∀ᶠn in atTop,∀u∈Ioo (0:ℝ) (Ccut*(M n).data.d),
      let d := (M n).data.d
      let site := 1/((dim n+1:ℕ):ℝ)
      let Dmass := (M n).originalMassThermalRadius
      let J := ∫v in 0..Ccut*d,Dmass v
      |(M n).originalMassScalarResidual u| ≤
        Cbudget*(d^4+d^2*Dmass u+d*J)+
        d^3*(Cbudget*(a n+site/d)+
          ∑j∈s,(Cbudget*c j)*
            ((Dmass u+site)/d)^((p j:ℝ)⁻¹)) := by
  filter_upwards [Hprice,ha,hcoeff] with n hnprice hna hncoeff
  intro u hu
  let m0 := M n
  let d := m0.data.d
  let site := 1/((dim n+1:ℕ):ℝ)
  let Dmass := m0.originalMassThermalRadius
  let J := ∫v in 0..Ccut*d,Dmass v
  let P := finitePowerMassTargetModulus s p c d (a n) J
  let u0 : PositiveMass := ⟨u,hu.1⟩
  obtain ⟨us,hus,hu0,U,Hfinite⟩ := hnprice u0 hu.2
  have hJ : 0≤J := intervalIntegral.integral_nonneg
    (mul_nonneg hCcut.le m0.data.hd.le)
    (fun v hv => Real.sqrt_nonneg _)
  have hPcont : Continuous P :=
    finitePowerMassTargetModulus_continuous s p c d (a n) J hp
  have hP0 : ∀x,0≤x→0≤P x := by
    intro x hx
    exact finitePowerMassTargetModulus_nonneg s p c m0.data.hd hna hJ hc hx
  have Hreader := m0.actual_original_target_mass_continuous_modulus
    P hPcont hP0 hCr u0 us hus hu0 U Hfinite
  have harg0 : 0≤Dmass u+site := add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have Hlambda : (2*m0.data.T*Cr+Ctaylor)*P (Dmass u+site)≤
      Cbudget*P (Dmass u+site) :=
    mul_le_mul_of_nonneg_right hncoeff (hP0 _ harg0)
  have Hmean : Cm*d^4≤Cbudget*d^4 :=
    mul_le_mul_of_nonneg_right hCm (pow_nonneg m0.data.hd.le 4)
  have Hprice' : |m0.originalMassScalarResidual u|≤
      Cbudget*d^4+Cbudget*P (Dmass u+site) := by
    have HH : |m0.originalMassScalarResidual u|≤
        Cm*d^4+(2*m0.data.T*Cr+Ctaylor)*P (Dmass u+site) := by
      simpa only [ActualHighWallOverlapMinimum.originalMassScalarResidual,
        ActualHighWallOverlapMinimum.originalMassThermalRadius,
        ActualHighWallData.N,m0,d,Dmass,site,P] using Hreader
    exact HH.trans (add_le_add Hmean Hlambda)
  dsimp only
  change |m0.originalMassScalarResidual u| ≤
    Cbudget*(d^4+d^2*Dmass u+d*J)+
      d^3*(Cbudget*(a n+site/d)+
        ∑j∈s,(Cbudget*c j)*
          ((Dmass u+site)/d)^((p j:ℝ)⁻¹))
  apply Hprice'.trans_eq
  have hsumEq :
      (∑j∈s,(Cbudget*c j)*((Dmass u+site)/d)^((p j:ℝ)⁻¹)) =
        Cbudget*(∑j∈s,c j*((Dmass u+site)/d)^((p j:ℝ)⁻¹)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsumEq]
  dsimp only [P,finitePowerMassTargetModulus]
  have hd0 : d≠0 := m0.data.hd.ne'
  field_simp [hd0]
  ring

end OAI.SKFluctuations.LaplaceWindowFormalization
