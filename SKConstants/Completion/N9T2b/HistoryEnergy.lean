module

public import SKConstants.Completion.N9T2b.FreshProduct

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators Matrix

namespace SKConstants.Completion.N9T2b
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation M1 LFine N9 N9c
variable {Ω : Type*} [MeasurableSpace Ω]

def historyQueryRows (a h f H : ℝ≥0) (heq : a+(h+f) = H) (n : ℕ)
    (i : Fin n) (v : Fin n → ScalarDriverHistory H) : ℝ × ℝ :=
  (scalarHiddenSign (v i).1,
    historyCellEndpoint a h f (castDriverHistory heq.symm (v i)))

theorem measurable_historyQueryRows (a h f H : ℝ≥0) (heq : a+(h+f) = H)
    (n : ℕ) (i : Fin n) : Measurable (historyQueryRows a h f H heq n i) :=
  (((measurable_of_finite scalarHiddenSign).comp measurable_fst).comp
      (measurable_pi_apply i)).prodMk
    ((measurable_historyCellEndpoint a h f).comp
      ((measurable_castDriverHistory heq.symm).comp (measurable_pi_apply i)))

theorem historyQueryRows_fresh (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f H : ℝ≥0) (hh : 0 < h) (heq : a+(h+f) = H) (n : ℕ)
    (u : DriverPastRows a n × (Fin n → ℝ × FreshRowSeed h f)) (i : Fin n) :
    historyQueryRows a h f H heq n i (freshHistoryRows W β hβ a h f H heq n u) =
      gaussianSignRows (fun j => freshRowSign W β hβ a h f (u.1 j).1 (u.1 j).2) i u.2 := by
  subst H
  apply Prod.ext
  · rfl
  · exact freshRowHistory_cellEndpoint W β hβ a h f hh (u.1 i,u.2 i)

def historyFrozenQueryEnergy (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f H : ℝ≥0) (heq : a+(h+f) = H) (ha : a ≤ H) (n m : ℕ) (s : ℝ)
    (E : DriverPastRows a n → Matrix (Fin (m+1)) (Fin n) ℝ)
    (m₀ : DriverPastRows a n → Fin n → ℝ)
    (v : Fin n → ScalarDriverHistory H) : ℝ :=
  let p := driverPastRows a H ha n v
  let t := frozenQueryTarget W β hβ a s (m₀ p) (fun i => (p i).1) (fun i => (p i).2)
  oneQueryEnergy (historyQueryRows a h f H heq n) n
    (normalizedQuery n (paperFrame (E p) t 0)) (remainingProjection (paperFrame (E p) t)) v

theorem measurable_historyFrozenQueryEnergy (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f H : ℝ≥0) (heq : a+(h+f) = H) (ha : a ≤ H) (n m : ℕ) (s : ℝ)
    (E : DriverPastRows a n → Matrix (Fin (m+1)) (Fin n) ℝ)
    (m₀ : DriverPastRows a n → Fin n → ℝ) (hE : Measurable E) (hm₀ : Measurable m₀) :
    Measurable (historyFrozenQueryEnergy W β hβ a h f H heq ha n m s E m₀) := by
  let p := driverPastRows a H ha n
  let T := fun v => frozenQueryTarget W β hβ a s (m₀ (p v))
    (fun i => (p v i).1) (fun i => (p v i).2)
  have hp : Measurable p := measurable_driverPastRows a H ha n
  have hT (i : Fin n) : Measurable (fun v => T v i) :=
    ((N9b.measurable_fixedPastPosterior_param W β hβ a
      (fun v => (p v i).1) (fun v => (p v i).2)
      (((measurable_pi_apply i).comp hp).fst)
      (((measurable_pi_apply i).comp hp).snd)).sub
        ((measurable_pi_apply i).comp (hm₀.comp hp))).div_const s
  have hF (i j) : Measurable (fun v => paperFrame (E (p v)) (T v) i j) :=
    paperFrame_measurable (fun v => E (p v)) T
      (fun i j => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (hE.comp hp))) hT i j
  have hR := measurable_historyQueryRows a h f H heq n
  change Measurable (fun v =>
    oneQueryEnergy (historyQueryRows a h f H heq n) n
      (normalizedQuery n (paperFrame (E (p v)) (T v) 0))
      (remainingProjection (paperFrame (E (p v)) (T v))) v)
  dsimp only [oneQueryEnergy, normalizedQuery, remainingProjection, Matrix.mul_apply,
    Matrix.transpose_apply, tailRows, spin, gaussian, Pi.smul_apply, smul_eq_mul]
  exact (Finset.measurable_sum _ (fun i _ =>
    Finset.measurable_sum _ (fun j _ => Finset.measurable_sum _ (fun k _ =>
      (((hF 0 i).const_mul _).mul (Finset.measurable_sum _ (fun q _ =>
        (hF q.succ j).mul (hF q.succ k)))).mul
          (((hR i).fst.mul (hR j).fst).mul (hR k).snd))))).const_mul _

theorem historyFrozenQueryEnergy_fresh (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f H : ℝ≥0) (hh : 0 < h) (heq : a+(h+f) = H) (ha : a ≤ H) (n m : ℕ) (s : ℝ)
    (E : DriverPastRows a n → Matrix (Fin (m+1)) (Fin n) ℝ)
    (m₀ : DriverPastRows a n → Fin n → ℝ)
    (u : DriverPastRows a n × (Fin n → ℝ × FreshRowSeed h f)) :
    historyFrozenQueryEnergy W β hβ a h f H heq ha n m s E m₀
        (freshHistoryRows W β hβ a h f H heq n u) =
      let t := frozenQueryTarget W β hβ a s (m₀ u.1)
        (fun i => (u.1 i).1) (fun i => (u.1 i).2)
      let row := gaussianSignRows
        (fun i => freshRowSign W β hβ a h f (u.1 i).1 (u.1 i).2)
      oneQueryEnergy row n (normalizedQuery n (paperFrame (E u.1) t 0))
        (remainingProjection (paperFrame (E u.1) t)) u.2 := by
  unfold historyFrozenQueryEnergy
  rw [freshHistoryRows_past]
  simp only [oneQueryEnergy, spin, gaussian, historyQueryRows_fresh W β hβ a h f H hh heq n u]

theorem sourceHistory_frozenQuery_integral (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (a h f : ℝ≥0)
    (hh : 0 < h) (heq : a+(h+f) = Horizon δ K) (ha : a ≤ Horizon δ K)
    (m : ℕ) (s : ℝ)
    (E : DriverPastRows a (r+K) → Matrix (Fin (m+1)) (Fin (r+K)) ℝ)
    (m₀ : DriverPastRows a (r+K) → Fin (r+K) → ℝ)
    (hEm : Measurable E) (hm₀ : Measurable m₀)
    (hE : ∀ p i j, dot (E p i) (E p j) = if i=j then 1 else 0) :
    (∫ z, historyFrozenQueryEnergy W β hβ a h f (Horizon δ K) heq ha (r+K) m s E m₀
        (SourceHistories W β hβ δ r K z) ∂SourceLinkedLaw W β hβ δ r K) =
      ∫ z, frozenQueryExpectation W β hβ a h f s
        (E (driverPastRows a (Horizon δ K) ha (r+K) (SourceHistories W β hβ δ r K z)))
        (m₀ (driverPastRows a (Horizon δ K) ha (r+K) (SourceHistories W β hβ δ r K z)))
        (fun i => (driverPastRows a (Horizon δ K) ha (r+K)
          (SourceHistories W β hβ δ r K z) i).1)
        (fun i => (driverPastRows a (Horizon δ K) ha (r+K)
          (SourceHistories W β hβ δ r K z) i).2)
        ∂SourceLinkedLaw W β hβ δ r K := by
  let : IsProbabilityMeasure (freshRowsLaw W h f (r+K)) := freshRowsLaw_probability W h f (r+K)
  let B : DriverPastRows a (r+K) → Fin (r+K) → ScalarContinuousPath a := fun p i => (p i).1
  let D : DriverPastRows a (r+K) → Fin (r+K) → ScalarContinuousPath a := fun p i => (p i).2
  have hB : Measurable B := Measurable.of_eval fun i => (measurable_pi_apply i).fst
  have hD : Measurable D := Measurable.of_eval fun i => (measurable_pi_apply i).snd
  let G := historyFrozenQueryEnergy W β hβ a h f (Horizon δ K) heq ha (r+K) m s E m₀
  have hG : Measurable G := measurable_historyFrozenQueryEnergy W β hβ a h f _ heq ha
    (r+K) m s E m₀ hEm hm₀
  have hI : Integrable (G ∘ freshHistoryRows W β hβ a h f _ heq (r+K))
      ((driverPastRowsLaw W a (r+K)).prod (freshRowsLaw W h f (r+K))) := by
    have hi := N9b.frozenQuery_integrable_prod W β hβ (driverPastRowsLaw W a (r+K))
      a h f (r+K) m s E m₀ B D hE hEm hm₀ hB hD
    convert hi using 1
    funext u
    exact historyFrozenQueryEnergy_fresh W β hβ a h f _ hh heq ha (r+K) m s E m₀ u
  rw [sourceHistory_integral_eq_fresh W β hβ δ hδ r K a h f hh heq G hG hI]
  have he : (∫ p, frozenQueryExpectation W β hβ a h f s (E p) (m₀ p) (B p) (D p)
        ∂driverPastRowsLaw W a (r+K)) =
      ∫ z, frozenQueryExpectation W β hβ a h f s
        (E (driverPastRows a (Horizon δ K) ha (r+K) (SourceHistories W β hβ δ r K z)))
        (m₀ (driverPastRows a (Horizon δ K) ha (r+K) (SourceHistories W β hβ δ r K z)))
        (B (driverPastRows a (Horizon δ K) ha (r+K) (SourceHistories W β hβ δ r K z)))
        (D (driverPastRows a (Horizon δ K) ha (r+K) (SourceHistories W β hβ δ r K z)))
        ∂SourceLinkedLaw W β hβ δ r K := by
    exact ((sourceDriverPastRows_hasLaw W β hβ δ hδ r K a h f hh heq ha).integral_comp
      (N9b.frozenQueryExpectation_integrable W β hβ (driverPastRowsLaw W a (r+K))
        a h f (r+K) m s E m₀ B D hE hEm hm₀ hB hD).aestronglyMeasurable).symm
  rw [← he]
  apply integral_congr_ae
  apply ae_of_all
  intro p
  apply integral_congr_ae
  apply ae_of_all
  intro u
  exact historyFrozenQueryEnergy_fresh W β hβ a h f _ hh heq ha (r+K) m s E m₀ (p,u)

end SKConstants.Completion.N9T2b
