module

public import CavityStarPairProjection

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations
open Hierarchy

theorem conditionalForkTest_spinPath_at_fork (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c : ℝ}
    (hc : OrderedSteps c steps) {P : Type}
    (x : P → FeatureIndex n → ℝ) (fork : ℕ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (p : PhysicalPathState P n steps) :
    conditionalForkTest (uniformWeight n) (finiteFeature n) steps x fork
      (fun z => G (actualSpinPath n steps x fork z.1)
        (actualSpinPath n steps x fork z.2)) p =
      G (actualSpinPath n steps x fork p) (actualSpinPath n steps x fork p) := by
  induction steps generalizing P c fork with
  | nil =>
    cases fork with
    | zero =>
      have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) [] hc
      change (∫ q, G (actualSpinPath n [] x 0 p) (actualSpinPath n [] x 0 p)
        ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) [] (x p.1)) = _
      simp
    | succ fork => rfl
  | cons st tail ih =>
    cases fork with
    | zero =>
      have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) (st::tail) hc
      change (∫ q, G (actualSpinPath n (st::tail) x 0 p) (actualSpinPath n (st::tail) x 0 p)
        ∂hierarchyPathKernel (uniformWeight n) (finiteFeature n) (st::tail) (x p.1)) = _
      simp
    | succ fork =>
      exact ih hc.2.2.2 (fun q : P × (FeatureIndex n → ℝ) => x q.1+q.2) fork
        ((p.1,p.2.1),p.2.2)

theorem fork_inner_power_le_young (n l : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c : ℝ}
    (hc : OrderedSteps c steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (fork : ℕ) (A B : PhysicalPathState P n steps → EuclideanSpace ℝ (Fin n))
    (hA : Measurable A) (hB : Measurable B) {RA RB tau : ℝ}
    (hRA : ∀ p, ‖A p‖ ≤ RA) (hRB : ∀ p, ‖B p‖ ≤ RB) (htau : 0 < tau) :
    (∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) steps x fork
      (fun z => |inner ℝ (A z.1) (B z.2)|^(2*l)) p ∂physicalPathLaw μ n steps x hx) ≤
      (∫ p, ‖A p‖^(4*l) ∂physicalPathLaw μ n steps x hx)/(2*tau) +
        (tau/2)*(∫ p, ‖B p‖^(4*l) ∂physicalPathLaw μ n steps x hx) := by
  let F := fun z : PhysicalPathState P n steps × PhysicalPathState P n steps =>
    |inner ℝ (A z.1) (B z.2)|^(2*l)
  let Y := fun p : PhysicalPathState P n steps => ‖A p‖^(4*l)
  let Z := fun p : PhysicalPathState P n steps => ‖B p‖^(4*l)
  let H := fun z : PhysicalPathState P n steps × PhysicalPathState P n steps =>
    Y z.1/(2*tau)+(tau/2)*Z z.2
  have hF : Measurable F := ((hA.comp measurable_fst).inner (hB.comp measurable_snd)).abs.pow_const _
  have hY : Measurable Y := hA.norm.pow_const _
  have hZ : Measurable Z := hB.norm.pow_const _
  have hH : Measurable H := ((hY.comp measurable_fst).div_const _).add
    ((hZ.comp measurable_snd).const_mul _)
  have hY0 p : 0 ≤ Y p := pow_nonneg (norm_nonneg _) _
  have hZ0 p : 0 ≤ Z p := pow_nonneg (norm_nonneg _) _
  have hYR p : |Y p| ≤ RA^(4*l) := by
    rw [abs_of_nonneg (hY0 p)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hRA p) _
  have hZR p : |Z p| ≤ RB^(4*l) := by
    rw [abs_of_nonneg (hZ0 p)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hRB p) _
  have hHR z : |H z| ≤ |1/(2*tau)| *RA^(4*l)+|tau/2| *RB^(4*l) := by
    apply (abs_add_le _ _).trans
    rw [abs_div,abs_mul]
    apply add_le_add
    · simpa [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left (hYR z.1) (abs_nonneg (1/(2*tau)))
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hZR z.2) (abs_nonneg _)
  have hFG z : F z ≤ H z := by
    have hi := norm_inner_le_norm (𝕜:=ℝ) (A z.1) (B z.2)
    rw [Real.norm_eq_abs] at hi
    have hp := pow_le_pow_left₀ (abs_nonneg _) hi (2*l)
    rw [mul_pow] at hp
    have hy := sq_nonneg (‖A z.1‖^(2*l)-tau*‖B z.2‖^(2*l))
    have he (u : EuclideanSpace ℝ (Fin n)) : (‖u‖^(2*l))^2=‖u‖^(4*l) := by
      rw [← pow_mul]
      congr 1
      omega
    rw [sub_sq,mul_pow,he,he] at hy
    apply hp.trans
    dsimp only [H,Y,Z]
    apply (mul_le_mul_iff_right₀ (by positivity : (0:ℝ)<2*tau)).mp
    field_simp
    nlinarith [hy]
  have hle : (∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) steps x fork F p
      ∂physicalPathLaw μ n steps x hx) ≤
      ∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) steps x fork H p
        ∂physicalPathLaw μ n steps x hx := by
    apply integral_mono_of_nonneg
      (Eventually.of_forall fun p => conditionalPathAverage_nonneg _ _ _ _ _
        (fun q => pow_nonneg (abs_nonneg _) _) p)
      (conditionalForkTest_integrable (uniformWeight_pos n) (finiteFeature n) steps hc μ x hx fork hH hHR)
    exact Eventually.of_forall fun p => conditionalPathAverage_mono_bounded (uniformWeight_pos n)
      (finiteFeature n) steps hc x fork (hF.comp measurable_prodMk_left)
      (hH.comp measurable_prodMk_left)
      (fun q => by
        rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
        exact (hFG (p,q)).trans (le_abs_self _ |>.trans (hHR (p,q))))
      (fun q => hHR (p,q)) (fun q => hFG (p,q)) p
  have he := integral_conditionalForkTest_add (uniformWeight_pos n) (finiteFeature n)
    steps hc μ x hx fork
    ((hY.comp measurable_fst).div_const (2*tau))
    ((hZ.comp measurable_snd).const_mul (tau/2))
    (fun z => by rw [abs_div]; exact div_le_div_of_nonneg_right (hYR z.1) (abs_nonneg _))
    (fun z => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hZR z.2) (abs_nonneg _))
  change (∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) steps x fork H p
    ∂physicalPathLaw μ n steps x hx) = _ at he
  have hef := integral_conditionalForkTest_fst (uniformWeight_pos n) (finiteFeature n)
    steps hc μ x hx fork (fun p => Y p/(2*tau))
  have hes := integral_conditionalForkTest_snd (uniformWeight_pos n) (finiteFeature n)
    steps hc μ x hx fork (hZ.const_mul (tau/2))
    (fun p => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hZR p) (abs_nonneg _))
  have he' := he.trans (congrArg₂ (fun a b : ℝ => a+b) hef hes)
  rw [integral_div,integral_const_mul] at he'
  exact hle.trans_eq he'

end OAI.SKFluctuations
