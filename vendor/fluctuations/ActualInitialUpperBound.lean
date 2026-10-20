module

public import UpperInitialChord
public import ComparisonPerturbedEndpointBand
public import ConcreteWallCostPowers
public import LowerLedger

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy PositiveLaplaceAssembly
open scoped Topology NNReal

def wallInitialD (m : ℝ) (n : ℕ) : ℝ := (n:ℝ)^(-(1:ℝ)/6+25*m)
def wallInitialError (m : ℝ) (n : ℕ) : ℝ :=
  (n:ℝ)^(-(2:ℝ)/3+2*m)*wallInitialD m n
def wallInitialComparisonError (m : ℝ) (n : ℕ) : ℝ :=
  (n:ℝ)^(20*(m/10000))*wallInitialError m n

def actualInitialUpperComparison (T C m : ℝ) (n : ℕ) : Prop :=
  ∃ r : boundedMassProfiles,
    (∀ u ∈ Icc (0:ℝ) 1, u < wallHighMass m n → r.val u ≤ C*wallInitialD m n) ∧
    pathCompensatedPressure n (fun _ => T) (fun _ => 0)
      (fun u => laplaceComparisonStrength (wallInitialD m n) ((wallInitialD m n)^2) (r.val u))
      r.val 0 ≤ realOrderedSKPathPressure n (fun _ => T) (fun _ => 0) 0+
        wallInitialComparisonError m n

theorem laplaceFinalStrength_shell_lower_nonneg {d C r : ℝ}
    (hd : 0 < d) (hC : 0 < C) (hr : 0 ≤ r) (hrC : r ≤ C*d) :
    min 1 (1/C)*d^2 ≤ laplaceComparisonStrength d (d^2) r := by
  rcases eq_or_lt_of_le hr with hr|hr
  · rw [← hr,laplaceFinalStrength_eq hd.ne']
    simp only [zero_div,laplaceComparisonShape,zero_le_one,ite_true,mul_one]
    exact (mul_le_mul_of_nonneg_right (min_le_left (1:ℝ) (1/C)) (sq_nonneg d)).trans_eq
      (one_mul _)
  · exact laplaceFinalStrength_shell_lower hd hC hr hrC

theorem wallInitialD_sq (m : ℝ) {n : ℕ} (hn : 0 < n) :
    (wallInitialD m n)^2=(n:ℝ)^(-(1:ℝ)/3+50*m) := by
  unfold wallInitialD
  rw [← Real.rpow_natCast,← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 1
  norm_num
  ring

theorem wallInitialComparisonError_eq (m : ℝ) {n : ℕ} (hn : 0 < n) :
    wallInitialComparisonError m n=(n:ℝ)^(-(5:ℝ)/6+27*m+20*(m/10000)) := by
  unfold wallInitialComparisonError wallInitialError wallInitialD
  rw [← Real.rpow_add (Nat.cast_pos.mpr hn),← Real.rpow_add (Nat.cast_pos.mpr hn)]
  congr 1
  ring

theorem wallInitialChord_power (m : ℝ) {n : ℕ} (hn : 0 < n) :
    wallHighMass m n*upperInitialEpsilon m n*(wallInitialD m n)^2=
      (n:ℝ)^(-(5:ℝ)/6+95*m) := by
  rw [wallInitialD_sq m hn]
  unfold wallHighMass upperInitialEpsilon
  rw [← Real.rpow_add (Nat.cast_pos.mpr hn),← Real.rpow_add (Nat.cast_pos.mpr hn)]
  congr 1
  ring

theorem actual_initial_upper_bound {T C m : ℝ}
    (hT : 1 < T) (hC : 0 < C) (hm : 0 < m) (hmmax : m < 1/300)
    (hinput : ∀ᶠ n : ℕ in atTop, actualInitialUpperComparison T C m n) :
    ∀ᶠ n : ℕ in atTop,
      physicalShellPressure n T (wallHighMass m n) (upperInitialEpsilon m n)-
        physicalShellPressure n T (wallHighMass m n) 0 ≤
      (C^2/2+1)*((n:ℝ)^(-(5:ℝ)/6+95*m)+
        (n:ℝ)^(-(5:ℝ)/6+27*m+20*(m/10000))) := by
  have hmargin := eventually_coefficient_rpow_le
    (c := (2:ℝ)) (d := min 1 (1/C))
    (lt_min zero_lt_one (one_div_pos.mpr hC))
    (show -(1:ℝ)/3+40*m < -(1:ℝ)/3+50*m by linarith)
  filter_upwards [hinput,hmargin,eventually_ge_atTop (1:ℕ)] with n hninput hnmargin hn1
  have hn : 0 < n := by omega
  have hnR : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hd : 0 < wallInitialD m n := Real.rpow_pos_of_pos hnR _
  have hd1 : wallInitialD m n ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast hn1) (by linarith)
  have hdT : (wallInitialD m n)^2 ≤ T := by nlinarith
  have hε := upperInitialEpsilon_mem hT hmmax hn1
  have hs : 0 < wallHighMass m n := wallHighMass_pos m hn
  have hs1 : wallHighMass m n ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast hn1) (by linarith)
  obtain ⟨r,hr,hcomp⟩ := hninput
  let e := fun u => laplaceComparisonStrength (wallInitialD m n) ((wallInitialD m n)^2) (r.val u)
  have hclocks := constantStrength_comparisonClockAdmissible hd.ne'
    (sq_nonneg (wallInitialD m n)) hdT r
  have he : ∀ u ∈ Icc (0:ℝ) 1, 0 < e u := fun u _ =>
    laplaceComparisonStrength_pos (wallInitialD m n) (sq_pos_of_pos hd) _
  have hp : MonotoneOn (fun u => e u*(r.val u)^2) (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    have hfield := hclocks.2.1 hu hv huv
    simp only [zero_add] at hfield
    have hrval := r.property.2 huv
    have hfieldpos : 0 ≤ e u*r.val u := mul_nonneg (he u hu).le (r.property.1 u).1
    have hp := mul_le_mul hfield hrval (r.property.1 u).1
      (mul_nonneg (he v hv).le (r.property.1 v).1)
    convert hp using 1 <;> ring
  have hres : ∀ u ∈ Icc (0:ℝ) 1, u < wallHighMass m n →
      2*upperInitialEpsilon m n ≤ e u := by
    intro u hu hus
    have hlo := laplaceFinalStrength_shell_lower_nonneg hd hC (r.property.1 u).1 (hr u hu hus)
    have hmargin' : 2*upperInitialEpsilon m n ≤ min 1 (1/C)*(wallInitialD m n)^2 := by
      simpa only [upperInitialEpsilon,wallInitialD_sq m hn] using hnmargin
    exact hmargin'.trans hlo
  have hradius : ∀ u ∈ Icc (0:ℝ) 1, u < wallHighMass m n →
      (r.val u)^2 ≤ (C*wallInitialD m n)^2 := by
    intro u hu hus
    exact pow_le_pow_left₀ (r.property.1 u).1 (hr u hu hus) 2
  have hchord := path_pressure_initial_chord_bound n hn (by linarith : 0 < T)
    hε.1.le hε.2.le hs hs1 e r.val he hclocks.1
    (by simpa only [zero_add] using hclocks.2.1) hclocks.2.2.1
    (by simpa only [zero_add] using hclocks.2.2.2) hp hres hradius 0 hcomp
  have hzero : physicalShellPressure n T (wallHighMass m n) 0=
      realOrderedSKPathPressure n (fun _ => T) (fun _ => 0) 0 := by
    unfold physicalShellPressure
    congr 1
    funext u
    unfold OAI.SKFluctuations.initialShellMatrixClock
    simp
  have hclock : initialShellMatrixClock T (upperInitialEpsilon m n) (wallHighMass m n)=
      fun u => if u < wallHighMass m n then T-upperInitialEpsilon m n else T := by
    funext u
    unfold OAI.SKFluctuations.initialShellMatrixClock
    split_ifs <;> simp
  have hmain : physicalShellPressure n T (wallHighMass m n) (upperInitialEpsilon m n)-
      physicalShellPressure n T (wallHighMass m n) 0 ≤
        C^2/2*(n:ℝ)^(-(5:ℝ)/6+95*m)+(n:ℝ)^(-(5:ℝ)/6+27*m+20*(m/10000)) := by
    have heq : upperInitialEpsilon m n*(C*wallInitialD m n)^2*wallHighMass m n/2=
        C^2/2*(n:ℝ)^(-(5:ℝ)/6+95*m) := by
      rw [← wallInitialChord_power m hn]
      ring
    rw [heq,wallInitialComparisonError_eq m hn] at hchord
    rw [hzero]
    change realOrderedSKPathPressure n
      (initialShellMatrixClock T (upperInitialEpsilon m n) (wallHighMass m n))
      (fun _ => 0) 0-realOrderedSKPathPressure n (fun _ => T) (fun _ => 0) 0 ≤ _
    rw [hclock]
    exact hchord
  have hA : 0 ≤ (n:ℝ)^(-(5:ℝ)/6+95*m) := Real.rpow_nonneg hnR.le _
  have hB : 0 ≤ (n:ℝ)^(-(5:ℝ)/6+27*m+20*(m/10000)) := Real.rpow_nonneg hnR.le _
  nlinarith [mul_nonneg (sq_nonneg C) hB]

end OAI.SKFluctuations.LaplaceWindowFormalization
