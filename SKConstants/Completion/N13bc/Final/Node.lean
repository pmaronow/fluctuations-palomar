module

public import SKConstants.Completion.N13bc.Node
public import SKConstants.Completion.N13A.Statements

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace SKConstants.Completion.N13bc
open SKConstantsOAI.ZeroTemperatureSK Blueprint Blueprint4 LGram N13A

theorem sharpGramStatement_holds : N13A.SharpGramStatement := by
  intro Ω _ W β hβ p hf hb M hM
  filter_upwards [coarseFixedGram_budget_eventually W β hβ p hf hb M hM,
    eventually_ge_atTop (1 : ℕ)] with n hbudget hn
  have hδ : 0 < coarseMesh p n := paperGrowingQueryMeshSize_pos p.a n (by omega)
  have H := growingMixedRows_wholeGram_compl_le W W β hβ (coarseMesh p n) hδ
    (coarseCount p n) (show 0 < n by omega)
    (fixedGramTolerance (paddingDepth (coarseCount p n)))
    (fixedGramTolerance_pos _)
  convert H.trans hbudget using 1 <;>
    simp only [canonicalArrayLaw, gramGood, rowPopulation, coarseTime, readoutTime,
      fixedGramTolerance, Nat.cast_add, Nat.cast_one, one_div, paddingDepth]

end SKConstants.Completion.N13bc
