module

public import ComparisonSignedCavitySecondLowObservedFreshOccupiedSum
public import ComparisonSignedCavitySecondLowInheritedActualResidualSavedRate
public import SKFluctuationsOAI.Probability.SKFluctuations.ScalarFiniteInvariant

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 45000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem native_second_low_original_chi_abs_le_one {as : List PositiveMass}
    (ho : MassOrdered 0 as) (U : ℕ) (K : ℕ→ℝ) :
    |(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0|≤1 := by
  let cs:=scalarBoundaryClocks as (relocatedClock U 0 K)
  have hc:=scalarBoundaryClocks_ordered ho (relocatedClock U 0 K)
  have HP:=scalarSourceJet_schedule_curvature_pos cs hc 0
  have HU:=scalarSourceJet_schedule_curvature_le_one cs hc 0
  rw [scalarSourceJet_two_schedule cs hc] at HP HU
  change |(scalarTerminal.schedule cs).H 0 (fun _=>0)|≤1
  rw [abs_of_pos HP]
  exact HU

theorem eventually_actual_minimum_inherited_second_low_whole_observed_saved_rate
    (degree rBound : ℕ) (Bclock Temp Cf Cmass Ccal : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcal : 1≤Ccal)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs≤1 →
        M.xs^2≤Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeSecondLowInheritedSavedMixedClock n M.bf M.hf as
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
          partitionPoint 0 as (pre.length+mid.length)≤Cmass*W →
        ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (s : T.Slot) (U : ℕ)
          (hU : U≤(pre++(mid++tail)).length),0 < mid.length → pre.length+mid.length<U →
          T.leaves≤rBound → NativePersistentLowForks pre.length (pre.length+mid.length) U T →
          W≤M.R (partitionPoint 0 as U) →
          M.R (partitionPoint 0 as (pre.length+mid.length))≤M.R (partitionPoint 0 as U)/2 →
          M.z≤M.R (partitionPoint 0 as U)/2 →
        ∀(G : ActualNaturalBoundaryShape n degree T) (forms : Fin degree→NativeSourceFactorForm)
          (initial : Finset (Fin degree)) (x : ℝ),M.xs≤x → x≤W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
          let g:=nativeFreshAtSlot T 0 s (pre.length+mid.length)
          let P:=(G.canonicalMinimumSource M forms).restProduct
          let Pg:=fun old=>P (g.restRestrict old)
          let χ:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          |(∑j : Fin 8,nativeSecondLowClassLedger n q U b h K g.tree hU Pg (g.embed s) g.mark j true/2)-
            χ^2*nativeSecondLowFreshOccupiedUnweightedCSource n q U b h K T s (pre.length+mid.length) hU P|≤
            C*(n:ℝ)^(-eta)*(W*M.xs^2*sourceMonomialScale x W initial) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_second_low_actual_fresh_residual_saved_rate
    (D:=D) degree rBound Bclock Temp Cf Cmass Ccal hTemp hCf hCmass hCcal
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  refine ⟨((rBound+1:ℕ):ℝ)*C,mul_pos (by positivity) hC,?_⟩
  filter_upwards [H] with n hn
  intro M HS hxs hcompare L us hus hret hmesh
  filter_upwards [hn M HS hxs hcompare L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut hmass T s U hU hmid hstar hleaves hT hWU hRstar hz
    G forms initial x hxsx hxW hmassG
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus k
  have hlen : U≤(finiteCutMasses us k).length:=by simpa only [hcut] using hU
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
    (fun _=>(M.bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
    (fun _=>(M.hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
  let b:=fun j=>(M.bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)
  let K:=nativeSecondLowInheritedSavedMixedClock n M.bf M.hf (finiteCutMasses us k)
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
  let P:=(G.canonicalMinimumSource M forms).restProduct
  let χ:=(scalarTerminal.schedule (scalarBoundaryClocks (finiteCutMasses us k) (relocatedClock U 0 K))).H 0 0
  let A:=C*(n:ℝ)^(-eta)*(W*M.xs^2*sourceMonomialScale x W initial)
  have hA : 0≤A:=by
    have hxpos : 0<x:=M.hxs.trans_le hxsx
    have hWpos : 0<W:=M.hxs.trans_le (le_max_left _ _)
    unfold A sourceMonomialScale
    positivity
  have Hpoint (B : NativeSecondLowFreshOccupiedMiddleBlock T s (pre.length+mid.length) U hU) :
      |nativeSecondLowCanonicalObservedResidualSource n q U b h K
        (nativeFreshAtSlot T 0 s (pre.length+mid.length)).tree
        (fun old=>P ((nativeFreshAtSlot T 0 s (pre.length+mid.length)).restRestrict old))
        ((nativeFreshAtSlot T 0 s (pre.length+mid.length)).embed s)
        (nativeSecondLowOccupiedBlockRepresentative (nativeFreshAtSlot T 0 s (pre.length+mid.length)).tree U hU B.val)
        (nativeFreshAtSlot T 0 s (pre.length+mid.length)).mark|≤A := by
    have Hfork:=native_second_low_fresh_occupied_old_slot_low_forks T s pre.length (pre.length+mid.length) U hU
      (by omega) hT B
    dsimp only at Hfork
    have Hrate:=hk pre mid tail hcut hmass T s
      (nativeSecondLowFreshOccupiedOldSlot T s (pre.length+mid.length) U hU B) s U hmid hstar hlen
      hleaves hT Hfork.1 Hfork.2 hWU hRstar hz G forms initial x hxsx hxW hmassG
    rw [←native_second_low_fresh_occupied_old_slot_exact T s (pre.length+mid.length) U hU B] at Hrate
    exact Hrate
  have Hgroup : |nativeSecondLowFreshOccupiedResidualSource n q U b h K T s (pre.length+mid.length) hU P|≤
      ((rBound+1:ℕ):ℝ)*A := by
    unfold nativeSecondLowFreshOccupiedResidualSource
    dsimp only
    calc
      _≤∑B : NativeSecondLowFreshOccupiedMiddleBlock T s (pre.length+mid.length) U hU,
        |nativeSecondLowCanonicalObservedResidualSource n q U b h K
          (nativeFreshAtSlot T 0 s (pre.length+mid.length)).tree
          (fun old=>P ((nativeFreshAtSlot T 0 s (pre.length+mid.length)).restRestrict old))
          ((nativeFreshAtSlot T 0 s (pre.length+mid.length)).embed s)
          (nativeSecondLowOccupiedBlockRepresentative (nativeFreshAtSlot T 0 s (pre.length+mid.length)).tree U hU B.val)
          (nativeFreshAtSlot T 0 s (pre.length+mid.length)).mark|:=Finset.abs_sum_le_sum_abs _ _
      _≤∑_B : NativeSecondLowFreshOccupiedMiddleBlock T s (pre.length+mid.length) U hU,A:=
        Finset.sum_le_sum (fun B _=>Hpoint B)
      _=(Fintype.card (NativeSecondLowFreshOccupiedMiddleBlock T s (pre.length+mid.length) U hU):ℝ)*A:=by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _≤((rBound+1:ℕ):ℝ)*A:=by
        apply mul_le_mul_of_nonneg_right _ hA
        exact Nat.cast_le.mpr ((native_second_low_fresh_occupied_middle_block_count T s (pre.length+mid.length) U hU).trans
          (hleaves.trans (Nat.le_succ rBound)))
  have Hchi : |χ|≤1:=native_second_low_original_chi_abs_le_one (finiteCutMasses_ordered us hus k) U K
  have Hsaved : |χ*nativeSecondLowFreshOccupiedResidualSource n q U b h K T s (pre.length+mid.length) hU P|≤
      ((rBound+1:ℕ):ℝ)*A := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right Hchi (abs_nonneg _)).trans (by simpa only [one_mul] using Hgroup)
  have Hwhole:=native_second_low_actual_fresh_observed_half_eq_grouped_unweighted_add_residual n q U
    (pre.length+mid.length) b h K T ho s hstar hU P
  dsimp only at Hwhole
  simp only [hcut] at Hwhole
  rw [Hwhole]
  change |χ^2*nativeSecondLowFreshOccupiedUnweightedCSource n q U b h K T s (pre.length+mid.length) hU P+
    χ*nativeSecondLowFreshOccupiedResidualSource n q U b h K T s (pre.length+mid.length) hU P-
    χ^2*nativeSecondLowFreshOccupiedUnweightedCSource n q U b h K T s (pre.length+mid.length) hU P|≤_
  rw [add_sub_cancel_left]
  simpa only [A,W,mul_assoc] using Hsaved

end OAI.SKFluctuations.Cavity
