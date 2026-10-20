module

public import SKConstants.Completion.N13a.BlueprintPrefix
public import SKConstants.Completion.N13a.Positions

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open SKConstantsOAI.ZeroTemperatureSK
namespace SKConstants.N13a
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem coarsePrefix_holds : CoarsePrefixStatement := by
  intro Ω _ W β hβ δ rf qf rb qb hdim hq
  exact ⟨coarsePrefix_replayInput_measurable δ rf qf rb qb hdim hq,
    coarsePrefix_replayInput_law W δ rf qf rb qb hdim hq,
    fun v t ht => coarsePrefix_replayField W β hβ δ rf qf rb qb hdim hq v t ht⟩

end SKConstants.N13a
