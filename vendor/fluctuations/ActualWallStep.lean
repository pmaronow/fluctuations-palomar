module

public import WallEndpointChord
public import PhysicalEndpointBridge

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem wallBareMatrix_eq_initialShellMatrixClock (T ε θ s : ℝ) :
    wallBareMatrix T ε θ s = initialShellMatrixClock T (ε+θ*wallLowStrength T ε) s := by
  funext u
  by_cases hu : u < s
  · simp only [wallBareMatrix, initialShellMatrixClock, ite_eq_left hu]
    ring
  · simp [wallBareMatrix, initialShellMatrixClock, hu]

theorem wallStep_eq_epsilon_add_half_strength (T ε : ℝ) :
    PositiveLaplaceAssembly.wallStep T ε = ε+wallLowStrength T ε/2 := by
  unfold PositiveLaplaceAssembly.wallStep wallLowStrength
  ring

theorem physicalShellPressure_lipschitz_low_mass (n : ℕ) (hn : 0 < n)
    {T s ε ε' : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hε : ε ∈ Icc (0 : ℝ) T) (hε' : ε' ∈ Icc (0 : ℝ) T) :
    |physicalShellPressure n T s ε-physicalShellPressure n T s ε'| ≤
      s/4*|ε-ε'| := by
  have hb := (initialShellMatrixClock_monotone T s hε.1).monotoneOn (Icc (0 : ℝ) 1)
  have hb' := (initialShellMatrixClock_monotone T s hε'.1).monotoneOn (Icc (0 : ℝ) 1)
  have hp := realOrderedSKPathPressure_l1_comparison n hn
    (initialShellMatrixClock T ε s) (fun _ => 0)
    (initialShellMatrixClock T ε' s) (fun _ => 0)
    hb (fun _ _ _ _ _ => le_rfl) hb' (fun _ _ _ _ _ => le_rfl)
    (by rw [initialShellMatrixClock_zero T ε hs]; linarith [hε.2]) (by norm_num)
    (by rw [initialShellMatrixClock_zero T ε' hs]; linarith [hε'.2]) (by norm_num) 0
  have heq : (fun u => |initialShellMatrixClock T ε s u-initialShellMatrixClock T ε' s u|) =
      fun u => if u < s then |ε-ε'| else 0 := by
    funext u
    by_cases hu : u < s
    · simp only [initialShellMatrixClock, ite_eq_left hu]
      have hh : T-ε-(T-ε') = -(ε-ε') := by ring
      rw [hh, abs_neg]
    · simp [initialShellMatrixClock, hu]
  rw [heq, integral_below_wall hs hs1 intervalIntegrable_const] at hp
  simp only [sub_self, abs_zero, intervalIntegral.integral_zero, mul_zero, add_zero,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hp
  unfold physicalShellPressure
  convert hp using 1
  ring

theorem physicalShellPressure_terminal_slope (n : ℕ) (hn : 0 < n)
    {T s ε : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hε : ε ∈ Icc (0 : ℝ) T) :
    physicalShellPressure n T s T-physicalShellPressure n T s ε ≤ s/4*(T-ε) := by
  have hT : T ∈ Icc (0 : ℝ) T := ⟨hε.1.trans hε.2, le_rfl⟩
  have hp := physicalShellPressure_lipschitz_low_mass n hn hs hs1 hT hε
  rw [abs_of_nonneg (sub_nonneg.mpr hε.2)] at hp
  exact (le_abs_self _).trans hp

section
variable {rmin s c : ℝ} {k M : ℝ → ℝ}
variable (hr : rmin ≤ 1) (hs1 : s ≤ 1) (hc : 0 < c)
variable (hk : ContinuousOn k (Icc rmin 1))
variable (hkc : ∀ t ∈ Icc rmin 1, c ≤ k t)
variable (hm : MonotoneOn M (Icc (0 : ℝ) 1)) (hM : 0 ≤ M 1)
variable (g : ℝ → ℝ) (hg : Continuous g)

theorem physicalShellPressure_wall_step_le {T ε τ d cutoff U V highError : ℝ}
    (hs : 0 < s) (hτ : 0 < τ) (hrmin : 0 ≤ rmin)
    (hε : ε ∈ Ioo 0 T) (hdepsilon : d^2 ≤ ε) (hginitial : g rmin = d^2)
    (hganti : AntitoneOn g (Icc rmin 1))
    (hgrmono : MonotoneOn (fun r => g r*r) (Icc rmin 1))
    (hg0 : ∀ r ∈ Icc rmin 1, 0 ≤ g r)
    (hgbound : ∀ r ∈ Icc rmin 1, g r ≤ d^2)
    (hMc : Continuous M) (hne : (inverseIntegralConstraints rmin s k M).Nonempty)
    (n : ℕ) (hn : 0 < n) (hcutoff : 0 < cutoff) (hcutoff1 : cutoff ≤ 1) (hU : 0 ≤ U)
    (hcomparison : wallMinimumValue hr hs1 hc hk hkc hm hM g hg T ε τ d n 0 0 ≤
      physicalShellPressure n T s ε+highError)
    (hband : ∀ θ ∈ Ioo cutoff 1, ∀ α : inverseIntegralConstraints rmin s k M,
      wallObjective hr hs1 hc hk hkc hm hM g hg T ε θ τ d n 0 α =
        wallMinimumValue hr hs1 hc hk hkc hm hM g hg T ε τ d n 0 θ →
      (∫ u in (0 : ℝ)..s, orderedPathB n
        (fun v => (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α v).toNNReal)
        (fun v => (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ τ d α v).toNNReal) u) ≤
        U+V*θ⁻¹) :
    physicalShellPressure n T s (PositiveLaplaceAssembly.wallStep T ε)-
      physicalShellPressure n T s ε ≤
      highError+wallLowStrength T ε/4*(U+2*s*(wallLowRadius d rmin ε)^2)+
        (wallLowStrength T ε*V/4)*(-Real.log cutoff)+
        wallLipschitzConstant T ε d rmin*cutoff := by
  have hc0 := (wallLowStrength_bounds hε).1
  have hsweep := wallMinimumValue_sweep_logarithmic_bound hr hs1 hc hk hkc hm hM g hg
    hs hτ hrmin hε hdepsilon hginitial hganti hgrmono hgbound hMc hne n hn
    hcutoff hcutoff1
    (A := wallLowStrength T ε/4*(U+s*(wallLowRadius d rmin ε)^2))
    (B := wallLowStrength T ε*V/4) (by positivity) (by
      intro θ hθ α hα
      have hθ0 : θ ∈ Icc (0 : ℝ) 1 := ⟨(hcutoff.trans hθ.1).le, hθ.2.le⟩
      have hh := wallObjectiveDerivative_le_low_cost hr hs1 hc hk hkc hm hM g hg
        hs hτ hrmin hε hθ0 hdepsilon hginitial hganti hgrmono hgbound n hn α
        (hband θ hθ α hα)
      convert hh using 1
      ring)
  obtain ⟨α, hα, _⟩ := wallMinimumValue_minimum hr hs1 hc hk hkc hm hM g hg
    hs hτ hrmin hε (show (1 : ℝ) ∈ Icc 0 1 by norm_num) hdepsilon hginitial
    hganti hgrmono hgbound hMc hne n hn 0
  have hchord := wall_endpoint_chord hr hs1 hc hk hkc hm hM g hg
    hs hτ hrmin hε hdepsilon hginitial hganti hgrmono hg0 hgbound n hn 0 α
  rw [hα, wallBareMatrix_eq_initialShellMatrixClock] at hchord
  have hp : realOrderedSKPathPressure n
      (initialShellMatrixClock T (ε+(1/2)*wallLowStrength T ε) s) (fun _ => 0) 0 =
      physicalShellPressure n T s (PositiveLaplaceAssembly.wallStep T ε) := by
    unfold physicalShellPressure
    rw [wallStep_eq_epsilon_add_half_strength]
    congr 1
    congr 1
    ring
  rw [hp] at hchord
  have hpen := wallLowPenalty_le_mass (d := d) (rmin := rmin) (ε := ε) hs hτ
  have hpen' := mul_le_mul_of_nonneg_left hpen (by positivity : 0 ≤ wallLowStrength T ε/4)
  linarith

end
end OAI.SKFluctuations.LaplaceWindowFormalization
