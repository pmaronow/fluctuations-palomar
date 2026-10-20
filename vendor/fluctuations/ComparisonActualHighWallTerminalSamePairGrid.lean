module

public import ComparisonActualHighWallTerminalRetainedAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

 theorem exists_actual_high_wall_cubic_terminal_on_same_square_pair_grid_along
    {m delta cl cu Az C0 Ct D Bclock gamma cK Cmass : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hgamma : 0 < gamma) (hcK : 0 < cK)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃threshold : ℕ,0 < threshold ∧ ∃saving : ℝ,0 < saving ∧
      ∀depth : ℕ,threshold ≤ depth → ∀A : ℝ,1 ≤ A → ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(u : PositiveMass) (as : List PositiveMass),MassOrdered 0 as →
        cK*M.data.d ≤ nativeContinuumMixedClock (dim n) M.bf M.hf as
          (retainedMassPrefixIndex u.val as) →
        ActualHighWallSquareResourcePairBudgetsOnGrid (1+depth) A gamma Cmass M u as →
        ActualHighWallFourTerminalBudgetsOnGrid depth saving Cmass M u as := by
  obtain ⟨threshold,hth,saving,hsaving,Hrate⟩:=exists_actual_high_wall_cubic_terminal_depth
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
    hm hC0 hgamma
  refine ⟨threshold,hth,saving,hsaving,?_⟩
  intro depth hdepth A hA
  let Cweight:=Bclock/(Real.exp (-4*Bclock)*cK)
  let Cenv:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches
    Cweight 3 3 depth*A^(1+depth)*(2*Bclock)*nativeActualGInsertionCost (3+6*depth)
  filter_upwards [hdim.eventually (Hrate |Cenv| (abs_nonneg _))] with n hnrate
  intro M hfixed u as ho hK Hpair
  dsimp only [ActualHighWallFourTerminalBudgetsOnGrid]
  intro U i hi hs hU st seed hst hseed hmass hr
  have Hraw:=actual_high_wall_weighted_terminal_abs_le_on_grid M u ho hi hs hU hcK hK hA hgamma
    M.data.hd1 depth Hpair st hst hseed hmass hr
  have Hfrozen:=actual_high_wall_weighted_terminal_abs_le_on_grid M u ho hi hs hU hcK hK hA hgamma
    M.data.hd1 depth Hpair st.freeze hst.freeze hseed hmass hr
  simp only [NativeActualResourceState.freeze,NativeResourceTerm.freeze,abs_neg] at Hfrozen
  have HR:=hnrate M depth hdepth
  rw [hfixed] at HR
  have Habsenv : Cenv*(((dim n+1:ℕ):ℝ)^(-gamma))^depth ≤
      ((dim n+1:ℕ):ℝ)^(-saving)*M.data.d^3:=by
    apply le_trans _ HR
    exact mul_le_mul_of_nonneg_right (le_abs_self Cenv) (by positivity)
  have Hraw' : _ ≤ |st.term.coefficient| *(((dim n+1:ℕ):ℝ)^(-saving)*M.data.d^3):=
    Hraw.trans (by
      change |st.term.coefficient| *Cenv*(((dim n+1:ℕ):ℝ)^(-gamma))^depth ≤ _
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left Habsenv (abs_nonneg st.term.coefficient))
  have Hfrozen' : _ ≤ |st.term.coefficient| *(((dim n+1:ℕ):ℝ)^(-saving)*M.data.d^3):=
    Hfrozen.trans (by
      change |st.term.coefficient| *Cenv*(((dim n+1:ℕ):ℝ)^(-gamma))^depth ≤ _
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left Habsenv (abs_nonneg st.term.coefficient))
  unfold actualGeneralFourCenteredForest
  rw [nativeActualFourCenteredForest_singleton_response]
  exact (abs_add_le _ _).trans ((add_le_add Hraw' Hfrozen').trans_eq (by ring))

end OAI.SKFluctuations.Cavity
