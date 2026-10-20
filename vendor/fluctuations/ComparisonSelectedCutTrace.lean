module

public import ComparisonBoundaryTraceTransport
public import ComparisonActualCutLedger
public import ComparisonSelectedFineCoupling
public import PhysicalFilledCapCellLaw

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy LaplaceWindowFormalization
open scoped BigOperators NNReal ENNReal Topology

def physicalSelectedSquareEnergy (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (q0 : FeatureIndex n → ℝ≥0)
    (J : Finset (Fin (steps.length+1))) : ℝ :=
  ∑i,WholeUnitSideKernel.physicalSelectedCellMass steps J i*
    (∫p,physicalCutSourceSquareTrace n steps id i.val p
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps)

def physicalSelectedCutDurations {ι : Type} (steps : List (GaussianStep ι))
    (J : Finset (Fin (steps.length+1))) : List ℝ≥0 :=
  List.ofFn (fun i:Fin steps.length=>Real.toNNReal (WholeUnitSideKernel.physicalSelectedCellMass steps J i.castSucc))

theorem physicalWeightedCutSum_ofFn {N : ℕ} (w : Fin N → ℝ≥0) (C : ℕ → ℝ) :
    physicalWeightedCutSum (List.ofFn w) C=∑i:Fin N,(w i:ℝ)*C i.val := by
  induction N generalizing C with
  | zero=>simp [physicalWeightedCutSum]
  | succ N ih=>
    rw [List.ofFn_succ,physicalWeightedCutSum,ih,Fin.sum_univ_succ]
    rfl

theorem physicalSelectedSquareEnergy_eq_weightedCuts (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (hlast : WholeUnitSideKernel.physicalSelectedCellMass steps J (Fin.last steps.length)=0) :
    physicalSelectedSquareEnergy n steps q0 J=
      physicalWeightedCutSum (physicalSelectedCutDurations steps J) (fun k=>
        ∫p,physicalCutSourceSquareTrace n steps id k p
          ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps) := by
  unfold physicalSelectedSquareEnergy physicalSelectedCutDurations
  rw [Fin.sum_univ_castSucc,hlast,zero_mul,add_zero,physicalWeightedCutSum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.coe_toNNReal _ (WholeUnitSideKernel.physicalSelectedCellMass_nonneg steps ha J i.castSucc)]
  rfl

theorem physicalSelectedSquareEnergy_le_filled_and_mesh (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1))
    (steps : List (GaussianStep (FeatureIndex (n+1)))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex (n+1) → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    {mesh : ℝ} (hm : 0 ≤ mesh)
    (hmesh : ∀i:Fin (steps.length+1),WholeUnitSideKernel.physicalSelectedCellMass steps J i ≤ mesh)
    (hlast : WholeUnitSideKernel.physicalSelectedCellMass steps J (Fin.last steps.length)=0) :
    physicalSelectedSquareEnergy (n+1) steps q0 J ≤
      2*zeroContinuation (Measure.pi fun k=>gaussianReal 0 (q0 k))
        (physicalFiniteCapIndexedTrace n d e (physicalSelectedCutDurations steps J) steps [] (a := 0)
          (by simpa using ha)) 0+2*mesh := by
  rw [physicalSelectedSquareEnergy_eq_weightedCuts (n+1) steps ha q0 J hlast]
  have hlen : (physicalSelectedCutDurations steps J).length ≤ steps.length := by simp [physicalSelectedCutDurations]
  have hdur : ∀w∈physicalSelectedCutDurations steps J,(w:ℝ) ≤ mesh := by
    intro w hw
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hw
    rw [← hi,Real.coe_toNNReal _ (WholeUnitSideKernel.physicalSelectedCellMass_nonneg steps ha J i.castSucc)]
    exact hmesh i.castSucc
  let F := fun ss:List (GaussianStep (FeatureIndex (n+1)))=>
    physicalWeightedCutSum (physicalSelectedCutDurations steps J) (fun k=>
      ∫p,physicalCutSourceSquareTrace (n+1) ss id k p
        ∂rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) q0 ss)
  have h := physicalWeightedCutSquareTrace_le_filled_and_mesh n d e q0
    (physicalSelectedCutDurations steps J) steps [] (by simpa using ha) hlen hm hdur
  change F (steps++[]) ≤ _ at h
  have he : F (steps++[])=F steps := congrArg F (List.append_nil steps)
  exact (le_of_eq he.symm).trans h

theorem physical_selected_filled_trace_eq_cell_energy (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1))
    (steps : List (GaussianStep (FeatureIndex (n+1)))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex (n+1) → ℝ≥0) (J : Finset (Fin (steps.length+1))) :
    zeroContinuation (Measure.pi fun k=>gaussianReal 0 (q0 k))
      (physicalFiniteCapIndexedTrace n d e (physicalSelectedCutDurations steps J) steps [] (a := 0)
        (by simpa using ha)) 0=
      ∑i:Fin steps.length,WholeUnitSideKernel.physicalSelectedCellMass steps J i.castSucc*
        physicalRootedCapCellTrace n d e q0 steps [] (a := 0) (by simpa using ha) i.val := by
  have hlen : (physicalSelectedCutDurations steps J).length ≤ steps.length := by simp [physicalSelectedCutDurations]
  rw [physicalRootedCapIndexedTrace_eq_weightedCellSum n d e q0 _ steps [] _ hlen]
  unfold physicalSelectedCutDurations
  rw [physicalWeightedCutSum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.coe_toNNReal _ (WholeUnitSideKernel.physicalSelectedCellMass_nonneg steps ha J i.castSucc)]

theorem physicalSelectedCovarianceEnergy_le_square (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    {a : ℝ} (ha0 : 0 < a) (hcut : ∀i∈J,a ≤ physicalCutMass 0 steps i.val) :
    (∑i,WholeUnitSideKernel.physicalSelectedCellMass steps J i*actualCutCovarianceEnergy n steps q0 i.val) ≤
      physicalSelectedSquareEnergy n steps q0 J/a^2 := by
  unfold physicalSelectedSquareEnergy
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi:i∈J
  · have h := physicalCutSpinTraceCovSq_integral_le_square_of_cutMass n steps ha ha0
      (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id i.val (hcut i hi)
    try simp only [← rootedHierarchyPathLaw_eq_physical] at h
    have hm := WholeUnitSideKernel.physicalSelectedCellMass_nonneg steps ha J i
    simpa only [actualCutCovarianceEnergy,mul_div_assoc,rootedHierarchyPathLaw,Kernel.comap_id] using mul_le_mul_of_nonneg_left h hm
  · simp [WholeUnitSideKernel.physicalSelectedCellMass,hi]

theorem physicalSelectedUnitEnergy_le_square (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    {U : Type} [Fintype U] [DecidableEq U] (unit : Fin (steps.length+1) → U) (u : U)
    {a : ℝ} (ha0 : 0 < a) (hcut : ∀i∈J,unit i=u → a ≤ physicalCutMass 0 steps i.val) :
    physicalSelectedUnitEnergy n steps q0 J unit u ≤
      physicalSelectedSquareEnergy n steps q0 (J.filter (fun i=>unit i=u))/a := by
  unfold physicalSelectedUnitEnergy physicalSelectedSquareEnergy
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi:i∈J ∧ unit i=u
  · simp only [hi,ite_true,WholeUnitSideKernel.physicalSelectedCellMass,Finset.mem_filter,hi,true_and,ite_true]
    have h := physicalCutSusceptibility_integral_le_square_of_cutMass n steps ha ha0
      (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id i.val (hcut i hi.1 hi.2)
    try simp only [← rootedHierarchyPathLaw_eq_physical] at h
    simpa only [mul_div_assoc,rootedHierarchyPathLaw,Kernel.comap_id] using mul_le_mul_of_nonneg_left h (pathMassDifferences_nonneg steps ha i)
  · simp [hi,WholeUnitSideKernel.physicalSelectedCellMass]

end OAI.SKFluctuations
