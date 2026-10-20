module

public import WallPhysicalBPathBand
public import ActualWallBandCover
public import ActualWallStep

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def wallPhysicalCostU (s A : ℝ) (n : ℕ) : ℝ :=
  6*s*A^2+(6*(10/Real.log 2+2)*Real.log (n:ℝ)+1)*(n:ℝ)^(-(10:ℝ))

def wallPhysicalCostV (T ε d rmin s A : ℝ) (n : ℕ) : ℝ :=
  85800*(10/Real.log 2+2)*A*(Real.log (n:ℝ))^2/
    ((n:ℝ)*wallLowStrength T ε*wallLowRadius d rmin ε*s)

theorem wallPhysicalCostU_nonneg {s A : ℝ} {n:ℕ} (hs:0  ≤  s) (hlog:0  ≤  Real.log (n:ℝ)) :
    0  ≤  wallPhysicalCostU s A n := by
  have hlog2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  unfold wallPhysicalCostU
  positivity

section
variable {rmin s c : ℝ} {k M : ℝ → ℝ}
variable (hr : rmin   ≤   1) (hs1 : s   ≤   1) (hc : 0 < c)
variable (hk : ContinuousOn k (Icc rmin 1))
variable (hkc : ∀ t ∈ Icc rmin 1, c   ≤   k t)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0   ≤   M 1)
variable (g : ℝ → ℝ) (hg : Continuous g)

theorem wallOrderedPathB_integrated_le {T ε θ d A : ℝ} (n dim : ℕ)
    (e : Fin (dim+1) ≃ FeatureIndex (n+1))
    (hs : 0 < s) (hn1 : 1<((n+1:ℕ):ℝ)) (hlogn : 1   ≤   Real.log ((n+1:ℕ):ℝ))
    (hε : ε ∈ Ioo 0 T) (hθ : θ ∈ Ioc (0:ℝ) 1)
    (hd : d ≠ 0) (hrmin : 0 < rmin)
    (hdepsilon : d^2   ≤   ε) (hginitial : g rmin=d^2)
    (hganti : AntitoneOn g (Icc rmin 1))
    (hgrmono : MonotoneOn (fun r => g r*r) (Icc rmin 1))
    (hgbound : ∀ r∈Icc rmin 1, g r  ≤  d^2)
    (α : inverseIntegralConstraints rmin s k M) (hA : 0   ≤   A) :
    let B := fun u => (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α u).toNNReal
    let F := fun u => (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ
      (((n+1:ℕ):ℝ)^(-(10:ℝ))) d α u).toNNReal
    (∀ u∈Ioo (0:ℝ) s, orderedPathS (n+1) B F u<A) →
    (∫ u in (0:ℝ)..s, orderedPathB (n+1) B F u)   ≤  
      wallPhysicalCostU s A (n+1)+wallPhysicalCostV T ε d rmin s A (n+1)*θ⁻¹ := by
  dsimp only
  intro hmean
  let B := fun u => (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α u).toNNReal
  let F := fun u => (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ
    (((n+1:ℕ):ℝ)^(-(10:ℝ))) d α u).toNNReal
  let τ := ((n+1:ℕ):ℝ)^(-(10:ℝ))
  let D := 28600*A*Real.log ((n+1:ℕ):ℝ)/
    (((n+1:ℕ):ℝ)*θ*wallLowStrength T ε*wallLowRadius d rmin ε*s)
  have hn : 0<((n+1:ℕ):ℝ) := by positivity
  have hτ : 0<τ := Real.rpow_pos_of_pos hn _
  have hcL : 0<wallLowStrength T ε := by
    unfold wallLowStrength
    exact div_pos (lt_min hε.1 (sub_pos.mpr hε.2)) (by norm_num)
  have hr0 : 0<wallLowRadius d rmin ε := by
    unfold wallLowRadius
    exact div_pos (mul_pos (sq_pos_of_ne_zero hd) hrmin) (by linarith [hε.1])
  have hlog0 : 0  ≤  Real.log ((n+1:ℕ):ℝ) := by linarith
  have hθpos : 0 < θ := hθ.1
  have hD : 0  ≤  D := by dsimp [D]; positivity
  have hadm := wall_changed_clocks_admissible hr hs1 hc hk hkc hm hM g hg hs hτ hrmin.le
    hε ⟨hθ.1.le,hθ.2⟩ hdepsilon hginitial hganti hgrmono hgbound α
  have hB : MonotoneOn B (Icc (0:ℝ) 1) :=
    fun u hu z hz huz => Real.toNNReal_mono (hadm.1 hu hz huz)
  have hF : MonotoneOn F (Icc (0:ℝ) 1) :=
    fun u hu z hz huz => Real.toNNReal_mono (hadm.2.1 hu hz huz)
  have hband (j:ℕ) (_hj:j<WallSweep.wallDyadicCount s τ) :
      (∫ u in WallSweep.wallDyadicCut s j..WallSweep.wallDyadicCut s (j+1), orderedPathB (n+1) B F u)   ≤  
        (4*A^2)*(WallSweep.wallDyadicCut s (j+1)-WallSweep.wallDyadicCut s j)+(D+2*τ) := by
    let v := s/(2:ℝ)^(j+1)
    have hv : 0<v := by dsimp [v]; positivity
    have hvs : v  ≤  s/2 := by
      apply div_le_div_of_nonneg_left hs.le (by norm_num : (0:ℝ)<2)
      simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ)  ≤  2) (by omega : 1  ≤  j+1)
    have he0 : WallSweep.wallDyadicCut s j=s-v := rfl
    have he1 : WallSweep.wallDyadicCut s (j+1)=s-v/2 := by
      change s-s/(2:ℝ)^(j+1+1)=s-(s/(2:ℝ)^(j+1))/2
      rw [pow_succ,div_mul_eq_div_div]
    rw [he0,he1]
    by_cases hlarge : 4*τ  ≤  v
    · have hh := wallOrderedPathB_dyadic_band_le hr hs1 hc hk hkc hm hM g hg n dim e
        hs hlogn hε hθ hd hrmin hlarge hvs hdepsilon hginitial hganti hgrmono hgbound α hA
        (hmean (s-v/4) (by constructor <;> linarith))
      dsimp only [D] at ⊢
      linarith
    · have hsmall : v<4*τ := lt_of_not_ge hlarge
      have horder : s-v  ≤  s-v/2 := by linarith
      have hi : IntervalIntegrable (orderedPathB (n+1) B F) volume (s-v) (s-v/2) :=
        (physicalOrderedPathB_intervalIntegrable n B F hB hF).mono_set (by
          rw [uIcc_of_le horder,uIcc_of_le (by norm_num : (0:ℝ)  ≤  1)]
          exact Icc_subset_Icc (by linarith) (by linarith))
      have hb1 := intervalIntegral.integral_mono_on horder hi
        (intervalIntegrable_const (μ:=volume) (c:=(1:ℝ))) (fun u hu =>
          orderedPathB_le_one_Icc (n+1) (by omega) B F hB hF ⟨by linarith [hu.1],by linarith [hu.2]⟩)
      simp only [intervalIntegral.integral_const,smul_eq_mul,mul_one] at hb1
      have hwidth : 0  ≤  (s-v/2)-(s-v) := sub_nonneg.mpr horder
      have hc : 0  ≤  4*A^2*((s-v/2)-(s-v)) := mul_nonneg (by positivity) hwidth
      linarith
  have hh := orderedPathB_full_low_mass_cost hs hs1 (n+1) hn1 hlogn B F hB hF
    (by positivity : 0  ≤  4*A^2) (by positivity : 0  ≤  D+2*τ) hband
  have heq : 3*(4*A^2)*(s/2)+3*(10/Real.log 2+2)*Real.log ((n+1:ℕ):ℝ)*(D+2*τ)+τ =
      wallPhysicalCostU s A (n+1)+wallPhysicalCostV T ε d rmin s A (n+1)*θ⁻¹ := by
    unfold wallPhysicalCostU wallPhysicalCostV
    dsimp [D,τ]
    field_simp
    ring
  exact hh.trans_eq heq

theorem wallObjectiveDerivative_le_of_actual_mean {T ε θ d A : ℝ} (n dim : ℕ)
    (e : Fin (dim+1) ≃ FeatureIndex (n+1))
    (hs : 0 < s) (hn1 : 1<((n+1:ℕ):ℝ)) (hlogn : 1  ≤  Real.log ((n+1:ℕ):ℝ))
    (hε : ε ∈ Ioo 0 T) (hθ : θ ∈ Ioc (0:ℝ) 1)
    (hd : d ≠ 0) (hrmin : 0 < rmin)
    (hdepsilon : d^2  ≤  ε) (hginitial : g rmin=d^2)
    (hganti : AntitoneOn g (Icc rmin 1))
    (hgrmono : MonotoneOn (fun r => g r*r) (Icc rmin 1))
    (hgbound : ∀ r∈Icc rmin 1, g r ≤ d^2)
    (α : inverseIntegralConstraints rmin s k M) (hA : 0  ≤  A)
    (hmean : ∀ u∈Ioo (0:ℝ) s, orderedPathS (n+1)
      (fun v => (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α v).toNNReal)
      (fun v => (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ
        (((n+1:ℕ):ℝ)^(-(10:ℝ))) d α v).toNNReal) u<A) :
    wallObjectiveDerivative hr hs1 hc hk hkc hm hM g hg T ε θ
      (((n+1:ℕ):ℝ)^(-(10:ℝ))) d (n+1) α  ≤ 
      wallLowStrength T ε/4*(wallPhysicalCostU s A (n+1)+
        wallPhysicalCostV T ε d rmin s A (n+1)*θ⁻¹+s*(wallLowRadius d rmin ε)^2) := by
  have hcost := wallOrderedPathB_integrated_le hr hs1 hc hk hkc hm hM g hg n dim e
    hs hn1 hlogn hε hθ hd hrmin hdepsilon hginitial hganti hgrmono hgbound α hA hmean
  exact wallObjectiveDerivative_le_low_cost hr hs1 hc hk hkc hm hM g hg hs
    (Real.rpow_pos_of_pos (by positivity) _) hrmin.le hε ⟨hθ.1.le,hθ.2⟩
    hdepsilon hginitial hganti hgrmono hgbound (n+1) (by omega) α hcost

theorem physicalShellPressure_wall_step_of_actual_mean {T ε d A cutoff highError : ℝ}
    (n dim : ℕ) (e : Fin (dim+1) ≃ FeatureIndex (n+1))
    (hs : 0 < s) (hn1 : 1<((n+1:ℕ):ℝ)) (hlogn : 1  ≤  Real.log ((n+1:ℕ):ℝ))
    (hε : ε ∈ Ioo 0 T) (hd : d ≠ 0) (hrmin : 0 < rmin)
    (hdepsilon : d^2  ≤  ε) (hginitial : g rmin=d^2)
    (hganti : AntitoneOn g (Icc rmin 1))
    (hgrmono : MonotoneOn (fun r => g r*r) (Icc rmin 1))
    (hg0 : ∀ r∈Icc rmin 1, 0 ≤ g r) (hgbound : ∀ r∈Icc rmin 1, g r ≤ d^2)
    (hMc : Continuous M) (hne : (inverseIntegralConstraints rmin s k M).Nonempty)
    (hcutoff : 0<cutoff) (hcutoff1 : cutoff ≤ 1) (hA : 0 ≤ A)
    (hcomparison : wallMinimumValue hr hs1 hc hk hkc hm hM g hg T ε
      (((n+1:ℕ):ℝ)^(-(10:ℝ))) d (n+1) 0 0  ≤ 
        physicalShellPressure (n+1) T s ε+highError)
    (hmean : ∀ θ∈Ioo cutoff 1, ∀ α : inverseIntegralConstraints rmin s k M,
      wallObjective hr hs1 hc hk hkc hm hM g hg T ε θ
        (((n+1:ℕ):ℝ)^(-(10:ℝ))) d (n+1) 0 α =
        wallMinimumValue hr hs1 hc hk hkc hm hM g hg T ε
          (((n+1:ℕ):ℝ)^(-(10:ℝ))) d (n+1) 0 θ →
      ∀ u∈Ioo (0:ℝ) s, orderedPathS (n+1)
        (fun v => (wallChangedMatrix hr hs1 hc hk hkc hm hM g hg T ε θ α v).toNNReal)
        (fun v => (wallChangedField hr hs1 hc hk hkc hm hM g hg T ε θ
          (((n+1:ℕ):ℝ)^(-(10:ℝ))) d α v).toNNReal) u<A) :
    physicalShellPressure (n+1) T s (PositiveLaplaceAssembly.wallStep T ε)-
      physicalShellPressure (n+1) T s ε  ≤ 
      highError+wallLowStrength T ε/4*(wallPhysicalCostU s A (n+1)+
        2*s*(wallLowRadius d rmin ε)^2)+
        (wallLowStrength T ε*wallPhysicalCostV T ε d rmin s A (n+1)/4)*(-Real.log cutoff)+
        wallLipschitzConstant T ε d rmin*cutoff := by
  apply physicalShellPressure_wall_step_le hr hs1 hc hk hkc hm hM g hg hs
    (Real.rpow_pos_of_pos (by positivity) _) hrmin.le hε hdepsilon hginitial
    hganti hgrmono hg0 hgbound hMc hne (n+1) (by omega) hcutoff hcutoff1
    (wallPhysicalCostU_nonneg hs.le (by linarith)) hcomparison
  intro θ hθ α hα
  exact wallOrderedPathB_integrated_le hr hs1 hc hk hkc hm hM g hg n dim e
    hs hn1 hlogn hε ⟨hcutoff.trans hθ.1,hθ.2.le⟩ hd hrmin hdepsilon hginitial
    hganti hgrmono hgbound α hA (hmean θ hθ α hα)

end
end OAI.SKFluctuations.LaplaceWindowFormalization
