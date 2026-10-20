module

public import SKConstants.Completion.N19B.Bridge

@[expose] public section
noncomputable section
open Filter
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.N19B
open Blueprint Blueprint4 N19 N19n
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem coarseBridgeBoundsStatement_holds : Blueprint5.CoarseBridgeBoundsStatement := by
  intro p hf hb _hD CB CD _hCB hCD
  refine ⟨3, by norm_num, ?_⟩
  have ha : p.b / 4 ≤ p.a := by linarith [hf.1, hb.2.1]
  simpa only [Real.rpow_ofNat] using
    coarse_bridge_bounds_eventually p hb.2.1.le hb.1.le ha CB CD hCD.le

end SKConstants.Completion.N19B
