module

public import CavityExteriorResampling

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace

namespace OAI.SKFluctuations.Hierarchy
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

def retainedPathEq : (steps : List (GaussianStep ι)) → {P : Type} → ℕ →
    (P × ForwardPath (ι → ℝ) S steps.length) →
    (P × ForwardPath (ι → ℝ) S steps.length) → Prop
  | _, _, 0, p, q => p.1 = q.1
  | [], _, _+1, p, q => p = q
  | _st::tail, _, k+1, p, q =>
      retainedPathEq tail k ((p.1,p.2.1),p.2.2) ((q.1,q.2.1),q.2.2)

omit [Fintype ι] [Fintype S] [Nonempty S] [MeasurableSpace S] [StandardBorelSpace S] in
theorem retainedPathEq_root (steps : List (GaussianStep ι)) {P : Type}
    (k : ℕ) (p q : P × ForwardPath (ι → ℝ) S steps.length)
    (h : retainedPathEq steps k p q) : p.1 = q.1 := by
  induction steps generalizing P k with
  | nil => cases k with
    | zero => exact h
    | succ k => exact congrArg Prod.fst h
  | cons st tail ih => cases k with
    | zero => exact h
    | succ k => exact congrArg (fun z : P × (ι → ℝ) => z.1) (ih k _ _ h)

omit [Nonempty S] [StandardBorelSpace S] in
theorem conditionalForkTest_congr_retained (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {P : Type} (x : P → ι → ℝ) (k : ℕ)
    (F G : (P × ForwardPath (ι → ℝ) S steps.length) ×
      (P × ForwardPath (ι → ℝ) S steps.length) → ℝ)
    (h : ∀ p q, retainedPathEq steps k p q → F (p,q) = G (p,q))
    (p : P × ForwardPath (ι → ℝ) S steps.length) :
    conditionalForkTest w φ steps x k F p =
      conditionalForkTest w φ steps x k G p := by
  induction steps generalizing P k with
  | nil => cases k with
    | zero =>
        simp only [conditionalForkTest, conditionalPathAverage]
        apply integral_congr_ae
        exact Eventually.of_forall fun q => h p (p.1,q) rfl
    | succ k => exact h p p rfl
  | cons st tail ih => cases k with
    | zero =>
        simp only [conditionalForkTest, conditionalPathAverage]
        apply integral_congr_ae
        exact Eventually.of_forall fun q => h p (p.1,q) rfl
    | succ k =>
        exact ih (fun q : P × (ι → ℝ) => x q.1+q.2) k
          (fun z => F ((z.1.1.1,(z.1.1.2,z.1.2)),(z.2.1.1,(z.2.1.2,z.2.2))))
          (fun z => G ((z.1.1.1,(z.1.1.2,z.1.2)),(z.2.1.1,(z.2.1.2,z.2.2))))
          (fun q r hr => h _ _ hr) ((p.1,p.2.1),p.2.2)

end OAI.SKFluctuations.Hierarchy

namespace OAI.SKFluctuations
open Hierarchy

theorem actualSpinPath_eq_of_retained (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {P : Type}
    (x : P → FeatureIndex n → ℝ) {t k : ℕ} (ht : t ≤ k)
    (p q : PhysicalPathState P n steps) (h : retainedPathEq steps k p q) :
    actualSpinPath n steps x t p = actualSpinPath n steps x t q := by
  induction steps generalizing P t k with
  | nil => cases k with
    | zero =>
        have he : t = 0 := Nat.eq_zero_of_le_zero ht
        subst t
        simp only [actualSpinPath, hierarchyMeanPath, retainedPathEq] at h ⊢
        rw [h]
    | succ k => rw [h]
  | cons st tail ih => cases t with
    | zero =>
        have hr := retainedPathEq_root (st::tail) k p q h
        simp only [actualSpinPath, hierarchyMeanPath]
        rw [hr]
    | succ t =>
        cases k with
        | zero => omega
        | succ k =>
            exact ih (fun r : P × (FeatureIndex n → ℝ) => x r.1+r.2)
              (Nat.le_of_succ_le_succ ht) ((p.1,p.2.1),p.2.2) ((q.1,q.2.1),q.2.2) h

theorem physical_exterior_resampling_eq_earlier_projection_errors (n l : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {P : Type}
    (x : P → FeatureIndex n → ℝ) {t k : ℕ} (ht : t ≤ k)
    (p : PhysicalPathState (PhysicalPathState P n steps) n steps) :
    let xc : PhysicalPathState P n steps → FeatureIndex n → ℝ := fun d => x d.1
    conditionalForkTest (uniformWeight n) (finiteFeature n) steps xc k
      (fun z => |orderedOverlap n (ForwardPath.spin steps.length z.1.1.2)
          (ForwardPath.spin steps.length z.1.2)-
        orderedOverlap n (ForwardPath.spin steps.length z.2.1.2)
          (ForwardPath.spin steps.length z.2.2)|^(2*l)) p =
    conditionalForkTest (uniformWeight n) (finiteFeature n) steps xc k
      (fun z => |physicalOverlapProjectionError n steps x t
          (z.1.1,(z.1.1.1,z.1.2))-
        physicalOverlapProjectionError n steps x t
          (z.2.1,(z.2.1.1,z.2.2))|^(2*l)) p := by
  dsimp only
  apply conditionalForkTest_congr_retained
  intro q r h
  have hr := retainedPathEq_root steps k q r h
  have hm := actualSpinPath_eq_of_retained n steps (fun d : PhysicalPathState P n steps => x d.1)
    ht q r h
  have hc (z : PhysicalPathState (PhysicalPathState P n steps) n steps) :
      actualSpinPath n steps (fun d : PhysicalPathState P n steps => x d.1) t z =
        actualSpinPath n steps x t (z.1.1,z.2) := by
    exact actualSpinPath_comp n steps x Prod.fst t z
  rw [hc q,hc r] at hm
  dsimp only [physicalOverlapProjectionError]
  rw [hr] at hm ⊢
  rw [hm]
  congr 2
  ring

theorem physical_exterior_resampling_moment_le_earlier_center (n l : ℕ) (hl : 0 < l)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (hs : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    {t k : ℕ} (ht : t ≤ k) :
    physicalExteriorResamplingMoment n l steps μ x hx k ≤
      (2:ℝ)^(2*l)*physicalOverlapProjectionErrorMoment n l steps μ x hx 0 t := by
  let ν := physicalPathLaw μ n steps x hx
  let xc : PhysicalPathState P n steps → FeatureIndex n → ℝ := fun d => x d.1
  have := physicalPathLaw_finite μ n steps hs x hx
  have : IsFiniteMeasure ν := physicalPathLaw_finite μ n steps hs x hx
  let E : PhysicalPathState (PhysicalPathState P n steps) n steps → ℝ :=
    fun p => physicalOverlapProjectionError n steps x t (p.1,(p.1.1,p.2))
  have hE : Measurable E :=
    (physicalOverlapProjectionError_measurable n steps hs x hx t).comp
      (measurable_fst.prodMk ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hER : ∀ p, |E p| ≤ 2 := fun p => physicalOverlapProjectionError_abs_le n steps hs x t _
  have hreplace : physicalExteriorResamplingMoment n l steps μ x hx k =
      ∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) steps xc k
        (fun z => |E z.1-E z.2|^(2*l)) p
        ∂physicalPathLaw ν n steps xc (hx.comp measurable_fst) := by
    apply integral_congr_ae
    exact Eventually.of_forall (physical_exterior_resampling_eq_earlier_projection_errors n l steps x ht)
  rw [hreplace]
  have H := fork_add_power_le (uniformWeight_pos n) (finiteFeature n) steps hs
    ν xc (hx.comp measurable_fst) k (hE.comp measurable_fst)
    ((hE.comp measurable_snd).neg) (fun z => hER z.1)
    (fun z => by simpa only [Function.comp_apply,Pi.neg_apply,abs_neg] using hER z.2)
    (2*l) (by omega)
  have hfst := integral_conditionalForkTest_fst (uniformWeight_pos n) (finiteFeature n)
    steps hs ν xc (hx.comp measurable_fst) k (fun p => |E p|^(2*l))
  have hsnd := integral_conditionalForkTest_snd (uniformWeight_pos n) (finiteFeature n)
    steps hs ν xc (hx.comp measurable_fst) k
    (F := fun p => |E p|^(2*l)) (R := (2:ℝ)^(2*l)) (hE.abs.pow_const (2*l))
    (fun p => by
      rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hER p) (2*l))
  simp only [Function.comp_apply,Pi.neg_apply,abs_neg,← sub_eq_add_neg] at H
  rw [hfst,hsnd] at H
  apply H.trans_eq
  have hEI := physical_exterior_projection_error_integral n l steps hs μ x hx t
  change (∫ p, |E p|^(2*l) ∂ν ⊗ₘ
    (hierarchyPathKernel (uniformWeight n) (finiteFeature n) steps).comap xc
      (hx.comp measurable_fst)) = _ at hEI
  rw [hEI]
  have hpow : (2:ℝ)^(2*l) = (2:ℝ)^(2*l-1)*2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpow]
  ring

end OAI.SKFluctuations
