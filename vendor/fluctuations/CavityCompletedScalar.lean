module

public import CavityEndpointCoordinates

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

 def completedAmplitude (n : ℕ) : FeatureIndex n → ℝ
   | .inl _ => 1
   | .inr none => 1/Real.sqrt 2
   | .inr (some _) => 1/Real.sqrt (n:ℝ)

 theorem completedAmplitude_nonneg (n : ℕ) (i : FeatureIndex n) :
    0 ≤ completedAmplitude n i := by rcases i with i|(_|e) <;> simp [completedAmplitude,Real.sqrt_nonneg]

 theorem finiteFeature_single_coefficient (n : ℕ) (σ : Spin n) (i : FeatureIndex n) :
    finiteFeature n σ (Pi.single i 1)=featureCoefficient n σ i := by
  classical
  simp [finiteFeature_apply,Pi.single_apply]

 theorem finiteFeature_abs_amplitude (n : ℕ) (σ : Spin n) (i : FeatureIndex n) :
    |finiteFeature n σ (Pi.single i 1)| = completedAmplitude n i := by
  rw [finiteFeature_single_coefficient]
  rcases i with i|(_|e) <;>
    simp [featureCoefficient,liftedCoefficients,completedAmplitude,abs_spinValue,abs_mul,abs_div,
      abs_of_nonneg (Real.sqrt_nonneg _)]

 theorem finiteFeature_square_amplitude (n : ℕ) (σ : Spin n) (i : FeatureIndex n) :
    (finiteFeature n σ (Pi.single i 1))^2=(completedAmplitude n i)^2 := by
  rw [← finiteFeature_abs_amplitude n σ i,sq_abs]

 def completedScalarBound (n : ℕ) (B : ℝ) : FeatureIndex n → ℝ :=
    fun i => if i=Sum.inr none then B else 0

 theorem completed_scalar_cost (n : ℕ) (B : ℝ) :
    (∑ i : FeatureIndex n, completedScalarBound n B i*(completedAmplitude n i)^2) = B/2 := by
  classical
  simp only [completedScalarBound,ite_mul,zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ,ite_true,completedAmplitude,div_pow,one_pow,
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  ring

 theorem completed_scalar_expect_close (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n) as) (ho : MassOrdered 0 as)
    {b h : ℕ → ℝ} (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀ j, 0 ≤ b j) (hh0 : ∀ j, 0 ≤ h j)
    (P : T.Assignment → ℝ) (hP : ∀ σ, 0 ≤ P σ) :
    ExpClose (2*(7*(T.leaves:ℝ)+8*(T.leaves:ℝ)^2*(T.leaves+1:ℝ))*(b as.length/2))
      (T.disorderExpect (uniformWeight n) (finiteFeature n) 0 (nullCompletedClock n b h) P 0)
      (T.disorderExpect (uniformWeight n) (finiteFeature n) 0 (physicalCompletedClock n b h) P 0) := by
  classical
  have hq : ∀ i, Monotone (fun j => nullCompletedClock n b h j i) := by
    intro i; rcases i with i|(_|e) <;> first | exact hh | exact hb | exact monotone_const
  have hr : ∀ i, Monotone (fun j => physicalCompletedClock n b h j i) := by
    intro i; rcases i with i|i <;> first | exact hh | exact hb
  have hq0 : ∀ i, (0:FeatureIndex n → ℝ) i ≤ nullCompletedClock n b h 0 i := by
    intro i; rcases i with i|(_|e) <;> first | exact hh0 0 | exact hb0 0 | exact le_rfl
  have hr0 : ∀ i, (0:FeatureIndex n → ℝ) i ≤ physicalCompletedClock n b h 0 i := by
    intro i; rcases i with i|i <;> first | exact hh0 0 | exact hb0 0
  have hM (i : FeatureIndex n) : 0 ≤ completedScalarBound n (b as.length) i := by
    simp only [completedScalarBound]; split_ifs <;> first | exact hb0 _ | exact le_rfl
  have hm (i : FeatureIndex n) (j : ℕ) (hj : j ≤ as.length) :
      |nullCompletedClock n b h j i-physicalCompletedClock n b h j i| ≤
        completedScalarBound n (b as.length) i := by
    rcases i with i|(_|e)
    · simp [nullCompletedClock,physicalCompletedClock,completedScalarBound]
    · simpa [nullCompletedClock,physicalCompletedClock,completedScalarBound,abs_of_nonneg (hb0 j)] using hb hj
    · simp [nullCompletedClock,physicalCompletedClock,completedScalarBound]
  have hw (σ : T.Assignment) := T.disorderWeight_cumulative_close (uniformWeight_pos n)
    (finiteFeature n) (fun i => (completedAmplitude n i)^2) (finiteFeature_square_amplitude n) ho
    (completedAmplitude n) (completedScalarBound n (b as.length)) (completedAmplitude_nonneg n)
    (fun i σ => (finiteFeature_abs_amplitude n σ i).le) 0
    (nullCompletedClock n b h) (physicalCompletedClock n b h) hq hr hq0 hr0 hM hm σ 0
  simp only [completed_scalar_cost] at hw
  exact T.disorderExpect_close (uniformWeight n) (finiteFeature n) 0
    (nullCompletedClock n b h) (physicalCompletedClock n b h) P hP 0 hw

end OAI.SKFluctuations.Cavity
