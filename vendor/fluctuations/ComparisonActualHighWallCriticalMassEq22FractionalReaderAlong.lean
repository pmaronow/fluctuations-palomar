module

public import ComparisonActualHighWallCriticalMassEq22FromFiniteReader
public import ComparisonActualHighWallTargetRadiusFractionalPrices
public import ComparisonActualGeneralCriticalFinitePowerOrders

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 24000000

def criticalMassReaderOrder (p : ℕ) (j : Fin 3) : ℕ :=
  if j.val=0 then 8 else if j.val=1 then 4 else p

theorem criticalMassReaderOrder_pos (p : ℕ) (hp : 0 < p) (j : Fin 3) :
    0 < criticalMassReaderOrder p j := by
  unfold criticalMassReaderOrder
  split_ifs
  · norm_num
  · norm_num
  · exact hp

theorem critical_mass_reader_modulus_eq_finite_power_modulus
    (p : ℕ) {d eta J x : ℝ} (hd : 0 < d) :
    finitePowerMassTargetModulus Finset.univ (criticalMassReaderOrder p)
      (fun _=>1) d eta J x =
      actualHighWallFractionalReaderModulus p d eta x+d*J := by
  simp [finitePowerMassTargetModulus,criticalMassReaderOrder,Fin.sum_univ_succ]
  unfold actualHighWallFractionalReaderModulus
  field_simp [hd.ne']
  ring

theorem critical_mass_fractional_reader_le_finite_power_modulus
    (p : ℕ) {d eta J x : ℝ} (hd : 0 < d) (hJ : 0 ≤ J) :
    actualHighWallFractionalReaderModulus p d eta x ≤
      finitePowerMassTargetModulus Finset.univ (criticalMassReaderOrder p)
        (fun _=>1) d eta J x := by
  rw [critical_mass_reader_modulus_eq_finite_power_modulus p hd]
  exact le_add_of_nonneg_right (mul_nonneg hd.le hJ)

def ActualHighWallMassFractionalReaderPrices
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (p : ℕ) (Cm Cr Ctaylor eta : ℝ) (u : PositiveMass) : Prop :=
  ∃us : List PositiveMass, (∀v∈us,v.val≤1) ∧ u∈us ∧
  ∃U : ℕ→ℕ,∀ᶠk : ℕ in atTop,
    let as:=finiteCutMasses us k
    let i:=retainedMassPrefixIndex u.val as
    i<U k ∧ U k≤as.length ∧
    |actualGeneralTargetOriginalMeanCorrection (n:=n) M.bf M.hf as i (U k)|≤
      Cm*M.data.d^4 ∧
    |actualGeneralTargetLongitudinalResponse (n:=n) M.bf M.hf as i (U k)|≤
      Cr*actualHighWallFractionalReaderModulus p M.data.d eta
        (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)) ∧
    |actualGeneralTargetOriginalTaylorPart (n:=n) M.bf M.hf as i (U k)|≤
      Ctaylor*actualHighWallFractionalReaderModulus p M.data.d eta
        (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))

theorem actual_high_wall_critical_mass_Eq22_of_uniform_fractional_reader_prices_along
    (p : ℕ) (hp : 0 < p)
    {m delta cl cu Az C0 Ct D Bclock Ctarget Cm Cr Ctaylor : ℝ}
    (hCtarget : 0 < Ctarget) (hCm : 0 ≤ Cm)
    (hCr : 0 ≤ Cr) (hCtaylor : 0 ≤ Ctaylor)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum
      (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0))
    (eta : ℕ→ℝ) (heta : Tendsto eta atTop (𝓝 0))
    (heta0 : ∀ᶠn in atTop,0 ≤ eta n)
    (Hprice : ∀ᶠn in atTop,∀u : PositiveMass,u.val<Ctarget*(M n).data.d →
      ActualHighWallMassFractionalReaderPrices (M n) p Cm Cr Ctaylor (eta n) u) :
    Tendsto (fun n=>
      (∫u in 0..Ctarget*(M n).data.d,
        |(M n).originalMassScalarResidual u|)/(M n).data.d^4)
      atTop (𝓝 0) := by
  let A:=2*max Bclock 0*Cr+Ctaylor
  let Cbudget:=Cm+A+1
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hCbudget : 0 < Cbudget := by dsimp only [Cbudget]; linarith
  have hCmBudget : Cm ≤ Cbudget := by dsimp only [Cbudget]; linarith
  have hcoeff : ∀ᶠn in atTop,2*(M n).data.T*Cr+Ctaylor≤Cbudget := by
    filter_upwards [] with n
    have HT:=(M n).hT.trans (le_max_left Bclock 0)
    have HC:=mul_le_mul_of_nonneg_right HT hCr
    dsimp only [A,Cbudget] at *
    linarith
  apply actual_high_wall_critical_mass_Eq22_of_uniform_finite_FOUR_prices
    hCtarget hCr hCbudget hCmBudget hm hdelta hroom hcl hcu hAz hC0 hCt hD
    dim hdim M hfixed hdlim hsRatio Finset.univ (criticalMassReaderOrder p)
    (fun j _=>criticalMassReaderOrder_pos p hp j) (fun _=>1)
    (fun _ _=>zero_le_one) eta heta heta0 hcoeff
  filter_upwards [Hprice] with n hn
  intro u huTarget
  dsimp only
  obtain ⟨us,hus,hu,U,hprices⟩:=hn u huTarget
  refine ⟨us,hus,hu,U,?_⟩
  have hJ : 0 ≤ ∫v in 0..Ctarget*(M n).data.d,
      (M n).originalMassThermalRadius v :=
    intervalIntegral.integral_nonneg (mul_nonneg hCtarget.le (M n).data.hd.le)
      (fun _ _=>Real.sqrt_nonneg _)
  filter_upwards [hprices] with k hk
  dsimp only at hk ⊢
  let as:=finiteCutMasses us k
  let i:=retainedMassPrefixIndex u.val as
  have Hmod:=critical_mass_fractional_reader_le_finite_power_modulus
    (x:=nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+
      1/(dim n+1:ℕ)) (eta:=eta n) p (M n).data.hd hJ
  exact ⟨hk.1,hk.2.1,hk.2.2.1,
    hk.2.2.2.1.trans (mul_le_mul_of_nonneg_left Hmod hCr),
    hk.2.2.2.2.trans (mul_le_mul_of_nonneg_left Hmod hCtaylor)⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
