module

public import PhysicalFilledSourceDerivative

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

theorem clockGradient_split {ι : Type*} [Fintype ι]
    {F G A H : (ι → ℝ) → ℝ}
    (hF₀ : PotentialRegularity 0 F) (hG : BddSmooth 0 G)
    (hA : BddSmooth 0 A) (hH : BddSmooth 0 H) {m s t : ℝ}
    (hm : 0 < m) (hs : 0 ≤ s) (ht : 0 ≤ t) (x : ι → ℝ) :
    clockGradient m F G A H (s+t) x =
      clockTest m (clockContinuation m F t) (clockGradient m F G A H t) s x +
      m * (clockTest m (clockContinuation m F t)
        (fun y => clockTest m F A t y * clockTest m F G t y) s x -
        clockTest m F A (s+t) x * clockTest m F G (s+t) x) := by
  obtain ⟨C,hF⟩ := hF₀.1
  have hi (y) := (exponentialIncrement_gaussian (fun _ : ι => Real.toNNReal t)).integrable_shift hF m y
  have hFc : LipschitzWith C (clockContinuation m F t) :=
    lipschitzWith_shiftedContinuation hF hm hi
  have hAt : BddSmooth 0 (clockTest m F A t) := hA.shiftedMean hF₀ hi
  have hGt : BddSmooth 0 (clockTest m F G t) := hG.shiftedMean hF₀ hi
  have hHt : BddSmooth 0 (clockTest m F H t) := hH.shiftedMean hF₀ hi
  have hAGt : BddSmooth 0 (clockTest m F (fun y => A y * G y) t) :=
    (hA.mul hG).shiftedMean hF₀ hi
  unfold clockGradient
  rw [clockTest_add_test hFc hHt ((hAGt.sub (hAt.mul hGt)).const_mul m),
    clockTest_const_mul, clockTest_sub_test hFc hAGt (hAt.mul hGt),
    clockTest_add hF hH hm.ne' hs ht,
    clockTest_add hF (hA.mul hG) hm.ne' hs ht]
  ring

end OAI.SKFluctuations.Hierarchy
