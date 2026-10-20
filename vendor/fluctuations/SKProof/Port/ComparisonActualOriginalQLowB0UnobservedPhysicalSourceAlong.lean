module

public import ComparisonSignedCavitySecondLowActualUnobservedVaryingEntryDensity
public import ComparisonSignedCavitySecondLowInheritedUnobservedMovingEntryBudget
public import ComparisonSignedCavitySecondLowInheritedOriginalMeanBudget
public import SKProof.Port.ComparisonActualOriginalQOriginalTargetB0
public import SKProof.Port.ComparisonActualOriginalQLowDensitySourceAlong

@[expose] public section
noncomputable section
set_option maxHeartbeats 70000000
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualThetaZeroOverlapMinimum
open NativeOverlapMinimum (ActualSlowWindowChoice)

theorem actual_second_low_unobserved_varying_entry_density_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (C : ℝ) (hC : 0<C) (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) :
    ∀ᶠjGrid : ℕ in atTop,
      let as:=finiteCutMasses us jGrid
      ∀(i star U : ℕ) (T : ClockTree (Spin n×Bool) as),
        U ≤ as.length → NativePersistentLowForks i star U T →
        partitionPoint 0 as U ≤ min (C*M.directTestWorkingScale) 1 →
      ∀s : T.Slot,
        ((nativeSecondLowUnobservedEntryRows T U 0).map (fun p=>|p.coeff| *
          nativeSecondLowMovingOriginalEntryRadius n M.sweepBf M.sweepHf as i star U
            (p.tree.splitIndex (p.embed s) p.mark))).sum ≤
          M.actualOriginalLowErrorDensitySaving C*M.xs^2+
            partitionPoint 0 as U/(n+1:ℕ) := by
  filter_upwards [M.actual_cut_low_error_edgeBudget_on_every_final_net C hC us hus] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro i star U T hU hpersistent hmass s
  let as:=finiteCutMasses us jGrid
  let f:=nativeSecondLowMovingOriginalEntryRadius n M.sweepBf M.sweepHf as i star U
  let R:=nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as
  let site:=(1/(n+1:ℕ):ℝ)
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hf:∀j,0 ≤ f j:=by
    intro j
    dsimp only [f,nativeSecondLowMovingOriginalEntryRadius]
    split_ifs
    · exact add_nonneg (Real.sqrt_nonneg _) (by positivity)
    · exact le_rfl
  have hfi:f i=0:=by simp [f,nativeSecondLowMovingOriginalEntryRadius]
  have hfstar:f star=0:=by simp [f,nativeSecondLowMovingOriginalEntryRadius]
  have hfhigh:∀j,U ≤ j → f j=0:=by
    intro j hj
    simp [f,nativeSecondLowMovingOriginalEntryRadius,not_lt.mpr hj]
  have Hentry:=hpersistent.unobserved_moving_entry_split_profile_le_edgeBudget s hU ho f hf hfi hfstar hfhigh
  have Hmono:=actual_low_edgeBudget_mono ho (show ∀j,j ≤ as.length →
      f j ≤ if j<U then R j+site else 0 by
    intro j _hj
    dsimp only [f,nativeSecondLowMovingOriginalEntryRadius,R,site]
    by_cases Hj : j<U
    · simp only [Hj,true_and,ite_true]
      split_ifs
      · exact le_rfl
      · exact add_nonneg (Real.sqrt_nonneg _) (by positivity)
    · simp only [Hj,false_and,ite_false,le_refl])
  have Heq:(fun j=>if j<U then R j+site else 0)=
      (fun j=>(1:ℝ)*(if j<U then R j else 0)+site*(if j<U then (1:ℝ) else 0)):=by
    funext j
    split_ifs <;> ring
  rw [Heq,actual_low_edgeBudget_linear,one_mul] at Hmono
  have Hones:edgeBudget 0 as (fun j=>if j<U then (1:ℝ) else 0)=partitionPoint 0 as U:=by
    rw [native_low_edgeBudget_eq_prefix_cells as 0 U hU,massCellSum_const,massPartition_take_end]
    simp
  rw [Hones] at Hmono
  apply Hentry.trans (Hmono.trans _)
  have HD:=hgrid U hU hmass
  have HH:=add_le_add_right HD (site*partitionPoint 0 as U)
  convert HH using 1 <;> dsimp [site] <;> ring

theorem eventually_actual_minimum_inherited_second_low_unobserved_moving_entry_budget_original_q
    (aDegree rBound : ℕ) (Bclock Temp Cf Cmass Couter Cdensity : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCouter : 0 ≤ Couter) (hCdensity : 0<Cdensity)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(i star U : ℕ) (T : ClockTree (Spin n×Bool) as) (hU : U ≤ as.length),
          i ≤ star → star<U → NativePersistentLowForks i star U T →
          T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x → x ≤ W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          partitionPoint 0 as U ≤ Couter*W →
          partitionPoint 0 as U ≤ min (Cdensity*M.directTestWorkingScale) 1 →
        ∀(a z : T.Slot),T.splitIndex a z<U →
        ∀(j : Fin 8) (firstError : Bool),
          let p0:=sourceMonomialScale x W initial
          let density:=M.actualOriginalLowErrorDensitySaving Cdensity*M.xs^2+
            partitionPoint 0 as U/(n+1:ℕ)
          |nativeSecondLowMovingErrorUnobservedClassLedger n q i star U b h K T
            hU (G.canonicalOriginalQSource M forms).restProduct a z j firstError/2| ≤ C*W*actualLowErrorComparisonConstant Mclock Temp*density*p0 := by
  obtain ⟨Cword,hCword,HW⟩:=eventually_actual_minimum_inherited_second_low_error_word_budgets_original_q
    (D:=D) aDegree rBound Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Poly:ℝ:=(rBound+1)*(rBound+2)*(rBound+3)
  let C:=Poly*Cword*(1+Couter)
  have hPoly:0<Poly:=by dsimp [Poly];positivity
  have hC:0<C:=mul_pos (mul_pos hPoly hCword) (by linarith)
  refine ⟨C,hC,?_⟩
  filter_upwards [HW] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh,
    actual_second_low_unobserved_varying_entry_density_original_q M Cdensity hCdensity us hus] with jGrid hgrid hDensity
  dsimp only at hgrid hDensity ⊢
  intro i star U T hU hi hstar hpersistent hT G forms initial x W hxsx hxW hmass houter
    hdensitycut a z haz j firstError
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let p0:=sourceMonomialScale x W initial
  let rho:=M.actualOriginalLowErrorDensitySaving Cdensity*M.xs^2+partitionPoint 0 as U/(n+1:ℕ)
  let f:=nativeSecondLowMovingOriginalEntryRadius n M.sweepBf M.sweepHf as i star U
  let anchor:=nativeSecondLowErrorEntryAnchor a z j firstError
  let F:=nativeSecondLowMovingErrorUnobservedWord n q i star U b h K hU
    (G.canonicalOriginalQSource M forms).restProduct a z j firstError
  let Drow:=Cword*(1+Couter)*W*actualLowErrorComparisonConstant Mclock Temp*p0
  have hp0:0 ≤ p0:=by
    dsimp [p0]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>
      (source_factor_scale_pos (M.hxs.trans_le hxsx) (M.hxs.trans_le (hxsx.trans hxW)) initial e).le
  have HCerr:0 ≤ actualLowErrorComparisonConstant Mclock Temp:=actualLowErrorComparisonConstant_nonneg Mclock hTemp
  have hW:0<W:=M.hxs.trans_le (hxsx.trans hxW)
  have hDrow:0 ≤ Drow:=by dsimp [Drow];positivity
  have ho:MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hf:∀k,0 ≤ f k:=by
    intro k
    dsimp [f,nativeSecondLowMovingOriginalEntryRadius]
    split_ifs
    · exact add_nonneg (Real.sqrt_nonneg _) (by positivity)
    · exact le_rfl
  have HDensity:=hDensity i star U T hU hpersistent hdensitycut anchor
  have hrho:0 ≤ rho:=by
    have Hsum:0 ≤ ((nativeSecondLowUnobservedEntryRows T U 0).map (fun p=>|p.coeff| *
        f (p.tree.splitIndex (p.embed anchor) p.mark))).sum:=by
      apply List.sum_nonneg
      intro x hx
      obtain ⟨p,_hp,rfl⟩:=List.mem_map.mp hx
      exact mul_nonneg (abs_nonneg _) (hf _)
    exact Hsum.trans HDensity
  have Hother (k : ℕ) (hk : k<U):M.xs+partitionPoint 0 as k ≤ (1+Couter)*W:=by
    have Hmass:partitionPoint 0 as k ≤ Couter*W:=(partitionPoint_mono as ho hk.le).trans houter
    nlinarith only [Hmass,hxsx,hxW]
  have HF:∀p∈T.markedAttach 0,∀r∈p.tree.markedAttach 0,
      ∀s∈r.tree.markedAttach 0,∀t∈s.tree.markedAttach 0,
        |F p r s t| ≤ Drow*f (nativeSecondLowEntryDepartureCut anchor j p r):=by
    intro p hp r hr s hs t ht
    dsimp only [F,nativeSecondLowMovingErrorUnobservedWord,nativeSecondLowUnobservedErrorWord]
    split_ifs with Hmoving Hpath
    · by_cases Hfirst:r.tree.splitIndex (r.embed p.mark) r.mark<U
      · by_cases Hsecond:t.tree.splitIndex (t.embed s.mark) t.mark<U
        · let k:=nativeSecondLowErrorCut firstError p r s t
          have hk:k<U:=by
            cases firstError
            · exact Hsecond
            · exact Hfirst
          have HE:=native_second_low_original_error_cut_eq_entry_departure T U hU a z j firstError
            p r hr s hs t ht Hpath.1 Hfirst Hsecond
          have Hf:f (nativeSecondLowEntryDepartureCut anchor j p r)=
              nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as k+1/(n+1:ℕ):=by
            rw [←HE]
            change (if k<U ∧ k≠i ∧ k≠star then
              nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as k+1/(n+1:ℕ) else 0)=_
            rw [ite_eq_left ⟨hk,Hmoving⟩]
          have HB:=hgrid U T hU hT G forms initial x W hxsx hxW hmass a z haz
            p hp r hr s hs t ht Hfirst Hsecond
          have hd:0 ≤ actualLowErrorComparisonConstant Mclock Temp*
              (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as k+1/(n+1:ℕ)):=
            mul_nonneg HCerr (add_nonneg (Real.sqrt_nonneg _) (by positivity))
          have Hbound:|nativeSecondLowErrorWord n q U b h K
              (G.canonicalOriginalQSource M forms).restProduct a z firstError p r s t| ≤ Cword*(actualLowErrorComparisonConstant Mclock Temp*
                (nativeOriginalCutLowErrorRadius n M.sweepBf M.sweepHf as k+1/(n+1:ℕ)))*((1+Couter)*W)*p0:=by
            cases firstError
            · exact HB.2.trans (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (Hother _ Hfirst) (mul_nonneg hCword.le hd)) hp0)
            · exact HB.1.trans (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (Hother _ Hsecond) (mul_nonneg hCword.le hd)) hp0)
          rw [Hf]
          apply Hbound.trans_eq
          dsimp [Drow]
          ring
        · rw [native_second_low_error_word_zero_second_high n q U b h K
            (G.canonicalOriginalQSource M forms).restProduct a z firstError p r s t (not_lt.mp Hsecond)]
          simpa only [abs_zero] using mul_nonneg hDrow (hf _)
      · rw [native_second_low_error_word_zero_first_high n q U b h K
          (G.canonicalOriginalQSource M forms).restProduct a z firstError p r s hs t ht (not_lt.mp Hfirst)]
        simpa only [abs_zero] using mul_nonneg hDrow (hf _)
    · simpa only [abs_zero] using mul_nonneg hDrow (hf _)
    · simpa only [abs_zero] using mul_nonneg hDrow (hf _)
  have Hclass:|nativeSecondLowMovingErrorUnobservedClassLedger n q i star U b h K T hU
      (G.canonicalOriginalQSource M forms).restProduct a z j firstError| ≤ 2*Poly*Drow*rho:=by
    rw [native_second_low_moving_error_unobserved_class_eq_entry]
    cases HM:nativeSecondLowFirstMiddleIsFirst j
    · let R:=fun (p : MarkedPlacement T) (r : MarkedPlacement p.tree)=>
        f (r.tree.splitIndex (r.embed (p.embed anchor)) r.mark)
      let allowed:=fun p : MarkedPlacement T=>U ≤ p.tree.splitIndex
        (p.embed (if j.val<4 then a else z)) p.mark
      have HF2:∀p∈T.markedAttach 0,allowed p → ∀r∈p.tree.markedAttach 0,
          ∀s∈r.tree.markedAttach 0,∀t∈s.tree.markedAttach 0,|F p r s t| ≤ Drow*R p r:=by
        intro p hp _HA r hr s hs t ht
        simpa only [nativeSecondLowEntryDepartureCut,HM,Bool.false_eq_true,ite_false,R] using HF p hp r hr s hs t ht
      have Hzero:∀p∈T.markedAttach 0,¬allowed p → ∀r∈p.tree.markedAttach 0,
          ∀s∈r.tree.markedAttach 0,∀t∈s.tree.markedAttach 0,F p r s t=0:=by
        intro p _hp HA r hr s hs t ht
        dsimp only [F,nativeSecondLowMovingErrorUnobservedWord,nativeSecondLowUnobservedErrorWord]
        split_ifs with _Hmoving Hpath
        · exact (HA (native_second_low_word_path_second_entry_first_mark_HIGH T U hU a z p r hr s hs t ht
            j Hpath.1 HM)).elim
        · rfl
        · rfl
      have Hcost:∀p∈T.markedAttach 0,allowed p →
          ((nativeSecondLowUnobservedEntryRows p.tree U 0).map (fun r=>|r.coeff| * R p r)).sum ≤ rho:=by
        intro p hp HA
        have Hnew:=hpersistent.observedHigh hi hstar 0 p hp (if j.val<4 then a else z)
          (by rwa [p.tree.splitIndex_symm])
        exact hDensity i star U p.tree hU Hnew hdensitycut (p.embed anchor)
      have HH:=native_second_low_second_entry_four_average_profile_abs_le T U ho hT F R allowed
        (fun p _hp r _hr=>hf _) hDrow hrho HF2 Hzero Hcost
      apply HH.trans
      have Hcoef:2*(rBound:ℝ)*(rBound+2)*(rBound+3) ≤ 2*Poly:=by
        have Hnat:(rBound:ℝ) ≤ rBound+1:=by linarith
        have HC:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hnat (by norm_num : (0:ℝ) ≤ 2))
          (show 0 ≤ (rBound+2:ℝ)*(rBound+3) by positivity)
        convert HC using 1 <;> (try dsimp [Poly]) <;> ring
      have HC:=mul_le_mul_of_nonneg_right Hcoef (mul_nonneg hDrow hrho)
      convert HC using 1 <;> ring
    · let R:=fun p : MarkedPlacement T=>f (p.tree.splitIndex (p.embed anchor) p.mark)
      have HF1:∀p∈T.markedAttach 0,∀r∈p.tree.markedAttach 0,
          ∀s∈r.tree.markedAttach 0,∀t∈s.tree.markedAttach 0,|F p r s t| ≤ Drow*R p:=by
        intro p hp r hr s hs t ht
        simpa only [nativeSecondLowEntryDepartureCut,HM,ite_true,R] using HF p hp r hr s hs t ht
      have HH:=native_second_low_first_entry_four_average_profile_abs_le T U ho hT F R
        (fun p _hp=>hf _) hDrow HF1
      exact HH.trans (by
        calc
          _ ≤ (2*(rBound+1:ℝ)*(rBound+2)*(rBound+3)*Drow)*rho:=
            mul_le_mul_of_nonneg_left HDensity (by positivity)
          _=2*Poly*Drow*rho:=by dsimp [Poly];ring)
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply (div_le_div_of_nonneg_right Hclass (by norm_num)).trans_eq
  dsimp [C,Drow,Poly,rho,p0,Mclock]
  ring

theorem eventually_actual_minimum_inherited_second_low_original_mean_budget_original_q
    (degree rBound : ℕ) (Bclock Temp Cf Cmass : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0 < Cp ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n degree T) (forms : Fin degree→NativeSourceFactorForm)
          (initial : Finset (Fin degree)) (x W : ℝ),M.xs ≤ x → x ≤ W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          |nativeOriginalRestTestExpectation n q U b h K T
            (G.canonicalOriginalQSource M forms).restProduct| ≤
            Real.exp (wholeLawRowComparisonConstant rBound*(4*Cf+2*Temp))*
              Cp^degree*sourceMonomialScale x W initial := by
  by_cases ha : 0 < degree
  · obtain ⟨Cp,hCp,H⟩:=eventually_actual_minimum_inherited_canonical_continuum_square_even_moment_original_q
      (D:=D) degree 1 rBound ha (by norm_num) Bclock Temp Cf Cmass hTemp hCf hCm
      hm hdelta hroom hcl hcu hAz hC0 hCt
    refine ⟨Cp,hCp,?_⟩
    filter_upwards [H] with n hn
    intro M hs0 hsxs HS hxs L us hus hret hmesh
    filter_upwards [hn M hs0 hsxs HS hxs L us hus hret hmesh] with k hk
    dsimp only at hk ⊢
    intro U T hT G forms initial x W hxsx hxW hmass
    have hscale : 0 ≤ Real.exp (wholeLawRowComparisonConstant rBound*(4*Cf+2*Temp))*
        Cp^degree*sourceMonomialScale x W initial:=by
      have hx : 0 < x:=M.hxs.trans_le hxsx
      have hW : 0 < W:=hx.trans_le hxW
      unfold sourceMonomialScale
      positivity
    apply native_original_rest_mean_abs_le_square n _ U _ _ _ T (finiteCutMasses_ordered us hus k)
      _ hscale
    simpa only [ActualNaturalBoundaryShape.product_eq_restProduct,mul_one] using
      hk U T 1 1 (by norm_num) (by norm_num) hT G forms initial x W hxsx hxW hmass
  · have hz : degree=0:=by omega
    subst degree
    refine ⟨1,by norm_num,Eventually.of_forall fun n=>?_⟩
    intro M hs0 hsxs HS hxs L us hus hret hmesh
    refine Eventually.of_forall fun k=>?_
    dsimp only
    intro U T hT G forms initial x W hxsx hxW hmass
    have HP:(G.canonicalOriginalQSource M forms).restProduct=(fun _=>1):=by
      funext σ
      simp only [ActualNaturalBoundaryShape.restProduct,Finset.univ_eq_empty,Finset.prod_empty]
    have Hp0:sourceMonomialScale x W initial=1:=by
      rw [←source_factor_scale_product]
      exact Fin.prod_univ_zero _
    rw [HP,native_original_rest_test_one n _ U _ _ _ T (finiteCutMasses_ordered us hus k)]
    simp only [abs_one,pow_zero,mul_one,Hp0]
    apply Real.one_le_exp
    exact mul_nonneg (wholeLawRowComparisonConstant_nonneg _) (by positivity)

end OAI.SKFluctuations.Cavity
