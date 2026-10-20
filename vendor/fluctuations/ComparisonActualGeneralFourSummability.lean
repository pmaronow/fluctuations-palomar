module

public import ComparisonActualGeneralFourSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree
open LaplaceWindowFormalization
open scoped BigOperators NNReal Topology
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false

theorem actual_general_four_residual_sum_bound
    {n : ℕ} {as : List PositiveMass} {i star U : ℕ}
    (bf hf : ℝ→ℝ≥0) (hs : star<U) (hU : U≤as.length) (W : ℝ) (depth : ℕ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) (budget : ℕ→ℝ)
    (Hprice : ∀j∈List.range depth,
      |((actualGeneralFourCenteredForest bf hf hs hU W j xs).map
        (actualGeneralFourRecursionError bf hf hs hU W)).sum|≤budget j) :
    |actualGeneralFourResidualSum bf hf hs hU W depth xs|≤
      ((List.range depth).map budget).sum := by
  let values j:=((actualGeneralFourCenteredForest bf hf hs hU W j xs).map
    (actualGeneralFourRecursionError bf hf hs hU W)).sum
  have Hsum : ∀ls : List ℕ,(∀j∈ls,|values j|≤budget j) →
      |(ls.map values).sum|≤(ls.map budget).sum := by
    intro ls
    induction ls with
    | nil => simp
    | cons j js ih =>
      intro H
      have Hj:=H j (by simp)
      have Hjs:=ih (fun k hk=>H k (List.mem_cons_of_mem _ hk))
      simp only [List.map_cons,List.sum_cons]
      exact (abs_add_le _ _).trans (add_le_add Hj Hjs)
  exact Hsum _ Hprice

theorem actual_general_four_source_bound_of_level_prices
    {n : ℕ} {as : List PositiveMass} {i star U : ℕ}
    (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hxs : ∀Q∈xs,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term)
    (hi : i ≤ star) (hs : star<U) (hU : U≤as.length) (ho : MassOrdered 0 as)
    (W : ℝ) (hW : W≠0) (hstarK : 0<nativeContinuumMixedClock n bf hf as star)
    (depth : ℕ) (budget : ℕ→ℝ) (terminalBudget : ℝ)
    (Hprice : ∀j∈List.range depth,
      |((actualGeneralFourCenteredForest bf hf hs hU W j xs).map
        (actualGeneralFourRecursionError bf hf hs hU W)).sum|≤budget j)
    (Hterminal : |((actualGeneralFourCenteredForest bf hf hs hU W depth xs).map
      (actualGeneralFourStateResponse bf hf U W)).sum|≤terminalBudget) :
    |((xs.flatMap (fun Q=>[Q,Q.freeze])).map
      (actualGeneralFourStateResponse bf hf U W)).sum|≤
      ((List.range depth).map budget).sum+terminalBudget := by
  rw [actual_general_four_resource_finite_iteration bf hf hbf hhf xs hxs hi hs hU ho W hW hstarK depth]
  exact (abs_add_le _ _).trans (add_le_add
    (actual_general_four_residual_sum_bound bf hf hs hU W depth xs budget Hprice) Hterminal)

theorem actual_general_finite_level_modulus_sum
    (depth : ℕ) (C err : ℕ→ℝ) (x Di : ℝ) (values : ℕ→ℝ)
    (Hprice : ∀j∈List.range depth,|values j|≤C j*x^2*Di+err j*x^3) :
    |((List.range depth).map values).sum|≤
      ((List.range depth).map C).sum*x^2*Di+((List.range depth).map err).sum*x^3 := by
  have Hsum : ∀ls : List ℕ,(∀j∈ls,|values j|≤C j*x^2*Di+err j*x^3) →
      |(ls.map values).sum|≤(ls.map C).sum*x^2*Di+(ls.map err).sum*x^3 := by
    intro ls
    induction ls with
    | nil => simp
    | cons j js ih =>
      intro H
      have Hj:=H j (by simp)
      have Hjs:=ih (fun k hk=>H k (List.mem_cons_of_mem _ hk))
      simp only [List.map_cons,List.sum_cons]
      exact ((abs_add_le _ _).trans (add_le_add Hj Hjs)).trans_eq (by ring)
  exact Hsum _ Hprice

theorem actual_general_finite_level_rate_tendsto_zero
    (depth : ℕ) (err : ℕ→ℕ→ℝ)
    (Hrate : ∀j∈List.range depth,Tendsto (err j) atTop (𝓝 0)) :
    Tendsto (fun n=>((List.range depth).map (fun j=>err j n)).sum) atTop (𝓝 0) := by
  have Hsum : ∀ls : List ℕ,(∀j∈ls,Tendsto (err j) atTop (𝓝 0)) →
      Tendsto (fun n=>(ls.map (fun j=>err j n)).sum) atTop (𝓝 0) := by
    intro ls
    induction ls with
    | nil => intro H; simp only [List.map_nil,List.sum_nil];exact tendsto_const_nhds
    | cons j js ih =>
      intro H
      simpa only [List.map_cons,List.sum_cons,zero_add] using
        (H j (by simp)).add (ih (fun k hk=>H k (List.mem_cons_of_mem _ hk)))
  exact Hsum _ Hrate

end OAI.SKFluctuations.Cavity
