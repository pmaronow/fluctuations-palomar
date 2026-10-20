module

public import CavityForkMoments

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations
open Hierarchy

def physicalCentralPairError (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {P : Type}
    (x : P → FeatureIndex n → ℝ) (fork t : ℕ)
    (z : PhysicalPathState P n steps × PhysicalPathState P n steps) : ℝ :=
  inner ℝ (actualSpinPath n steps x t z.1) (actualSpinPath n steps x t z.2) -
    ‖actualSpinPath n steps x fork z.1‖^2

theorem physicalCentralPairError_moment_le (n l : ℕ) (hl : 0 < l)
    (steps : List (GaussianStep (FeatureIndex n))) {c : ℝ}
    (hc : OrderedSteps c steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (fork t : ℕ) {tau : ℝ} (htau : 0 < tau) :
    (∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) steps x fork
      (fun z => |physicalCentralPairError n steps x fork t z|^(2*l)) p
        ∂physicalPathLaw μ n steps x hx) ≤
      (2:ℝ)^(4*l-2) *
        ((∫ p, ‖actualSpinPath n steps x t p-actualSpinPath n steps x fork p‖^(4*l)
            ∂physicalPathLaw μ n steps x hx)/tau +
          (tau/2)*((∫ p, ‖actualSpinPath n steps x t p‖^(4*l)
              ∂physicalPathLaw μ n steps x hx)+
            (∫ p, ‖actualSpinPath n steps x fork p‖^(4*l)
              ∂physicalPathLaw μ n steps x hx))) := by
  let Ω := PhysicalPathState P n steps
  let X := actualSpinPath n steps x
  let D := fun p : Ω => X t p-X fork p
  let F : Ω × Ω → ℝ := fun z => inner ℝ (D z.1) (X t z.2)
  let G : Ω × Ω → ℝ := fun z => inner ℝ (X fork z.1) (D z.2)
  let H : Ω × Ω → ℝ := fun z => inner ℝ (X fork z.1) (X fork z.2)-‖X fork z.1‖^2
  have hXt : Measurable (X t) := actualSpinPath_measurable n steps hc x hx t
  have hXf : Measurable (X fork) := actualSpinPath_measurable n steps hc x hx fork
  have hD : Measurable D := hXt.sub hXf
  have hD2 p : ‖D p‖ ≤ 2 := (norm_sub_le _ _).trans (by
    linarith [actualSpinPath_norm_le n steps hc x t p,actualSpinPath_norm_le n steps hc x fork p])
  have hF : Measurable F := (hD.comp measurable_fst).inner (hXt.comp measurable_snd)
  have hG : Measurable G := (hXf.comp measurable_fst).inner (hD.comp measurable_snd)
  have hH : Measurable H := ((hXf.comp measurable_fst).inner (hXf.comp measurable_snd)).sub
    ((hXf.comp measurable_fst).norm.pow_const 2)
  have hFR z : |F z| ≤ 2 := by
    have hi : |F z| ≤ ‖D z.1‖*‖X t z.2‖ := by
      simpa only [F,Real.norm_eq_abs] using norm_inner_le_norm (𝕜:=ℝ) (D z.1) (X t z.2)
    exact hi.trans (by
      nlinarith [hD2 z.1,actualSpinPath_norm_le n steps hc x t z.2,
        norm_nonneg (D z.1),norm_nonneg (X t z.2)])
  have hGR z : |G z| ≤ 2 := by
    have hi : |G z| ≤ ‖X fork z.1‖*‖D z.2‖ := by
      simpa only [G,Real.norm_eq_abs] using norm_inner_le_norm (𝕜:=ℝ) (X fork z.1) (D z.2)
    exact hi.trans (by
      nlinarith [hD2 z.2,actualSpinPath_norm_le n steps hc x fork z.1,
        norm_nonneg (D z.2),norm_nonneg (X fork z.1)])
  have hHR z : |H z| ≤ 2 := by
    apply (abs_sub _ _).trans
    have hi := norm_inner_le_norm (𝕜:=ℝ) (X fork z.1) (X fork z.2)
    rw [Real.norm_eq_abs] at hi
    have h1 := actualSpinPath_norm_le n steps hc x fork z.1
    have h2 := actualSpinPath_norm_le n steps hc x fork z.2
    rw [abs_of_nonneg (sq_nonneg ‖X fork z.1‖)]
    nlinarith [hi,norm_nonneg (X fork z.1),norm_nonneg (X fork z.2)]
  have hFG : Measurable (fun z => F z+G z) := hF.add hG
  have hFGR z : |F z+G z| ≤ 4 := (abs_add_le _ _).trans (by linarith [hFR z,hGR z])
  have hsum z : physicalCentralPairError n steps x fork t z = (F z+G z)+H z := by
    dsimp only [physicalCentralPairError,F,G,H,D,X]
    simp only [inner_sub_left,inner_sub_right]
    ring
  have hzero p : conditionalForkTest (uniformWeight n) (finiteFeature n) steps x fork
      (fun z => |H z|^(2*l)) p = 0 := by
    have hh := conditionalForkTest_spinPath_at_fork n steps hc x fork
      (fun A B => |inner ℝ A B-‖A‖^2|^(2*l)) p
    simpa only [H,X,real_inner_self_eq_norm_sq,sub_self,abs_zero,
      zero_pow (by omega : 2*l≠0)] using hh
  have hadd := fork_add_power_le (uniformWeight_pos n) (finiteFeature n) steps hc μ x hx fork
    hFG hH (fun z => (hFGR z).trans (le_max_left 4 2))
    (fun z => (hHR z).trans (le_max_right 4 2)) (2*l) (by omega)
  have hadd₂ := fork_add_power_le (uniformWeight_pos n) (finiteFeature n) steps hc μ x hx fork
    hF hG hFR hGR (2*l) (by omega)
  let M := ∫ p, ‖D p‖^(4*l) ∂physicalPathLaw μ n steps x hx
  let A := ∫ p, ‖X t p‖^(4*l) ∂physicalPathLaw μ n steps x hx
  let B := ∫ p, ‖X fork p‖^(4*l) ∂physicalPathLaw μ n steps x hx
  have hfirst := fork_inner_power_le_young n l steps hc μ x hx fork D (X t) hD hXt
    hD2 (actualSpinPath_norm_le n steps hc x t) htau
  have hsecond := fork_inner_power_le_young n l steps hc μ x hx fork D (X fork) hD hXf
    hD2 (actualSpinPath_norm_le n steps hc x fork) htau
  have hswap := integral_conditionalForkTest_swap (uniformWeight_pos n) (finiteFeature n)
    steps hc μ x hx fork (hG.abs.pow_const (2*l))
    (fun z => by
      rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hGR z) (2*l))
  have hg : (∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) steps x fork
      (fun z => |G z|^(2*l)) p ∂physicalPathLaw μ n steps x hx) ≤ M/(2*tau)+(tau/2)*B := by
    have hh := hswap.trans_le (by
      simpa only [G,D,X,Function.comp_def,Prod.swap,real_inner_comm,physicalPathLaw] using hsecond)
    exact hh
  have hf : (∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) steps x fork
      (fun z => |F z|^(2*l)) p ∂physicalPathLaw μ n steps x hx) ≤ M/(2*tau)+(tau/2)*A := hfirst
  simp only [hzero,integral_zero,add_zero] at hadd
  simp only [physicalPathLaw] at hf hg ⊢
  simp_rw [hsum]
  have hpow : (2:ℝ)^(2*l-1)*(2:ℝ)^(2*l-1) = (2:ℝ)^(4*l-2) := by
    rw [← pow_add]
    congr 1
    omega
  have hbound := hadd.trans (mul_le_mul_of_nonneg_left hadd₂ (pow_nonneg (by norm_num) _))
  rw [← mul_assoc,hpow] at hbound
  apply (hbound.trans (mul_le_mul_of_nonneg_left (add_le_add hf hg)
    (pow_nonneg (by norm_num : (0:ℝ)≤2) _))).trans_eq
  dsimp only [M,A,B,D,X,physicalPathLaw]
  ring

end OAI.SKFluctuations
