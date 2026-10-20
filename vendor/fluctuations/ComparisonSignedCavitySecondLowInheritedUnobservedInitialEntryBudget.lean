module

public import ComparisonSignedCavitySecondLowInitialEntrySource
public import ComparisonSignedCavitySecondLowInheritedInitialWordBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 30000000

theorem eventually_actual_minimum_inherited_second_low_unobserved_initial_entry_budget
    (aDegree rBound : ℕ) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U V : ℕ) (T : ClockTree (Spin n×Bool) as) (hU : U≤as.length),
           0<V → V≤U → partitionPoint 0 as V≤Ccut*M.xs → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x → x≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀(a z : T.Slot),T.splitIndex a z<U →
        ∀(i : ℕ),i<V → ∀(j : Fin 8),
          let p0:=sourceMonomialScale x W initial
          let di:=actualLowErrorComparisonConstant Mclock Temp*
            (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))
          |nativeSecondLowInitialUnobservedClassLedger n q i U b h K T
            hU (G.canonicalMinimumSource M forms).restProduct a z j/2|≤
            C*partitionPoint 0 as U*M.xs*di*p0 := by
  obtain ⟨Cword,hCword,HW⟩:=eventually_actual_minimum_inherited_second_low_actual_initial_word_budget
    (D:=D) aDegree rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Prow:ℝ:=4*(rBound+1)*(rBound+2)*(rBound+3)*(rBound+4)
  have hProw:0<Prow:=by dsimp [Prow];positivity
  refine ⟨Prow*Cword,mul_pos hProw hCword,?_⟩
  filter_upwards [HW] with n hn
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn M hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U V T hU hV0 hVU hcut hT G forms initial x W hxsx hxW hmass a z haz i hi j
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let p0:=sourceMonomialScale x W initial
  let di:=actualLowErrorComparisonConstant Mclock Temp*
    (nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ))
  let F:=nativeSecondLowInitialUnobservedWord n q i U b h K hU
    (G.canonicalMinimumSource M forms).restProduct a z j
  let Bd:=2*Cword*M.xs*di*p0
  have hp0:0≤p0:=by
    dsimp [p0]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos (M.hxs.trans_le hxsx) (M.hxs.trans_le (hxsx.trans hxW)) initial e).le
  have hdi:0≤di:=mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
    (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hxspos:0<M.xs:=M.hxs
  have hBd:0≤Bd:=by dsimp [Bd];positivity
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HF:∀p∈T.markedAttach 0,∀r∈p.tree.markedAttach 0,
      ∀s∈r.tree.markedAttach 0,∀t∈s.tree.markedAttach 0,|F p r s t|≤Bd:=by
    intro p hp r hr s hs t ht
    dsimp only [F,nativeSecondLowInitialUnobservedWord,nativeSecondLowUnobservedWord]
    split_ifs with Hindices _Hsource
    · have H:=hgrid U V T hU hV0 hVU hcut hT G forms initial x W hxsx hxW hmass a z haz
        p hp r hr s hs t ht (Hindices.1 ▸ hi) (Hindices.2 ▸ hi)
      rw [Hindices.1,Hindices.2] at H
      convert H using 1
      dsimp [Bd,di,p0]
      ring
    · simpa only [abs_zero] using hBd
    · simpa only [abs_zero] using hBd
  have Hentry:=native_second_low_entry_four_average_abs_le T U hU ho hT
    (nativeSecondLowFirstMiddleIsFirst j) F hBd HF
  rw [←native_second_low_initial_unobserved_class_eq_entry n q i U b h K T hU
    (G.canonicalMinimumSource M forms).restProduct a z j] at Hentry
  have Hmass:0≤partitionPoint 0 as U:=(partitionPoint_mem as ho U).1
  have Hpoly:(4*(rBound:ℝ)*(rBound+1)*(rBound+2)*(rBound+3))≤Prow:=by
    dsimp [Prow]
    gcongr <;> linarith
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  calc
    _≤((4*(rBound:ℝ)*(rBound+1)*(rBound+2)*(rBound+3))*partitionPoint 0 as U*Bd)/2:=
      div_le_div_of_nonneg_right Hentry (by norm_num)
    _=(4*(rBound:ℝ)*(rBound+1)*(rBound+2)*(rBound+3))*Cword*
        partitionPoint 0 as U*M.xs*di*p0:=by dsimp [Bd];ring
    _≤Prow*Cword*partitionPoint 0 as U*M.xs*di*p0:=by
      gcongr
    _= _:=rfl

end OAI.SKFluctuations.Cavity
