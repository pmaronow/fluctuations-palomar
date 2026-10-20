module

public import ComparisonActualHighWallCriticalMassEq22FromPointwise

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal BigOperators
set_option autoImplicit false

theorem actual_high_wall_critical_mass_Eq22_of_uniform_finite_FOUR_prices
    {m delta cl cu Az C0 Ct D Bclock Ccut Cm Cr Ctaylor Cbudget : ℝ}
    (hCcut : 0 < Ccut) (hCr : 0≤Cr) (hCbudget : 0<Cbudget)
    (hCm : Cm≤Cbudget)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighWallOverlapMinimum
      (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n => (M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto
      (fun n => (M n).data.s/(M n).data.d) atTop (𝓝 0))
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p : ι → ℕ) (hp : ∀j∈s,0<p j)
    (c : ι → ℝ) (hc : ∀j∈s,0≤c j)
    (a : ℕ → ℝ) (halim : Tendsto a atTop (𝓝 0))
    (ha : ∀ᶠn in atTop,0≤a n)
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
    Tendsto (fun n =>
      (∫u in 0..Ccut*(M n).data.d,
        |(M n).originalMassScalarResidual u|)/(M n).data.d^4)
      atTop (𝓝 0) := by
  have Hpoint := actual_high_wall_critical_mass_pointwise_of_uniform_finite_FOUR_prices
    hCcut hCr hCbudget hCm dim M s p hp c hc a ha hcoeff Hprice
  exact actual_high_wall_critical_mass_Eq22_of_fractional_pointwise_price
    hCcut hCbudget hm hdelta hroom hcl hcu hAz hC0 hCt hD
    dim hdim M hfixed hdlim hsRatio s p hp c a halim Hpoint

end OAI.SKFluctuations.LaplaceWindowFormalization
