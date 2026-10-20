module

public import ComparisonSignedCavityActualGammaCanonicalSavedCubic

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def nativeObservedRemainingTarget {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (c : T.Slot) (p : MarkedPlacement T)
    (useNew : Bool) : p.tree.Slot := if useNew then p.mark else p.embed c

def nativeCanonicalObservedFreshHighRow (n a : ℕ) {as : List PositiveMass}
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (star U : ℕ) (c b fslot : T.Slot) (useNew : Bool)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) : ℝ :=
  ((T.markedAttach 0).map fun p=>p.coeff*
    (if U≤p.tree.splitIndex (p.embed c) p.mark then
      fullScalarCutGamma p.tree U K (p.embed c) p.mark*
        nativeOriginalFreshResidual n p.tree (p.embed c) p.mark (p.embed b) 0 star 0 q 0
          (fun σ=>ActualNaturalBoundaryShape.canonicalLowRestFactor M
            (nativeObservedRemainingTarget c p useNew) (p.embed fslot) σ*
            (G.canonicalMinimumSource M forms).restProduct (p.restRestrict σ)) else 0)).sum

theorem eventually_actual_signed_fresh_high_row_saved_cubic
    (a : ℕ) (Bclock Temp Cmass Ccal : ℝ)
    (hTemp : 0≤Temp) (hCmass : 0≤Cmass) (hCcal : 1≤Ccal)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃Cp C : ℝ,0 < Cp ∧ 0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs≤1 →
        M.xs^2≤Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
          partitionPoint 0 as (pre.length+mid.length)≤Cmass*W →
        ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (c b fslot : T.Slot)
          (useNew : Bool) (U : ℕ),0 < mid.length → pre.length+mid.length < U →
          NativePersistentLowForks pre.length (pre.length+mid.length) U T →
          (T.splitIndex c b=pre.length ∨ T.splitIndex c b=pre.length+mid.length) →
          T.splitIndex c fslot≤pre.length+mid.length →
          W≤M.R (partitionPoint 0 as U) →
          M.R (partitionPoint 0 as (pre.length+mid.length))≤M.R (partitionPoint 0 as U)/2 →
          M.z≤M.R (partitionPoint 0 as U)/2 →
        ∀(G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
          (initial : Finset (Fin a)),
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale M.xs W initial e) →
          |nativeCanonicalObservedFreshHighRow n a M T (pre.length+mid.length) U c b fslot useNew
            G forms q (retainedStarMixedClock n M.bf M.hf as)|≤
            (2*(T.leaves:ℝ))*C*(n:ℝ)^(-eta)*(W*M.xs^2*(Cp^a*sourceMonomialScale M.xs W initial)) := by
  obtain ⟨Cp,C,hCp,hC,H⟩:=eventually_actual_gamma_canonical_saved_cubic
    a Bclock Temp Cmass Ccal hTemp hCmass hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  refine ⟨Cp,C,hCp,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hb hh hxs hcompare L us hus hret hmesh
  filter_upwards [hn M hb hh hxs hcompare L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut hmass T c b fslot useNew U hmid hU hT hcb hcf hWU hstar hz G forms initial hmassG
  let as:=finiteCutMasses us k
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
    (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
  let K:=retainedStarMixedClock n M.bf M.hf as
  let B:=C*(n:ℝ)^(-eta)*(W*M.xs^2*(Cp^a*sourceMonomialScale M.xs W initial))
  have hW : 0 < W:=M.hxs.trans_le (le_max_left _ _)
  have hB : 0≤B:=mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (mul_nonneg (mul_nonneg hW.le (sq_nonneg M.xs))
      (mul_nonneg (pow_nonneg hCp.le _) (mul_nonneg (pow_nonneg M.hxs.le _) (pow_nonneg hW.le _))))
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus k
  have hrow (p : MarkedPlacement T) (hp : p∈T.markedAttach 0) :
      |(if U≤p.tree.splitIndex (p.embed c) p.mark then
        fullScalarCutGamma p.tree U K (p.embed c) p.mark*
          nativeOriginalFreshResidual n p.tree (p.embed c) p.mark (p.embed b) 0 (pre.length+mid.length) 0 q 0
            (fun σ=>ActualNaturalBoundaryShape.canonicalLowRestFactor M
              (nativeObservedRemainingTarget c p useNew) (p.embed fslot) σ*
              (G.canonicalMinimumSource M forms).restProduct (p.restRestrict σ)) else 0)|≤B := by
    split_ifs with hhigh
    · have hhc : U≤p.tree.splitIndex p.mark (p.embed c):=by rwa [p.tree.splitIndex_symm]
      have hSource:=hT.observedHigh (by omega) hU 0 p hp c hhc
      have hsplitb : p.tree.splitIndex (p.embed c) (p.embed b)=pre.length ∨
          p.tree.splitIndex (p.embed c) (p.embed b)=pre.length+mid.length := by
        rw [(T.markedAttach_embed_preserves 0 p hp).2]
        exact hcb
      have hsplitf : p.tree.splitIndex (nativeObservedRemainingTarget c p useNew) (p.embed fslot)=
          T.splitIndex c fslot := by
        cases useNew
        · exact (T.markedAttach_embed_preserves 0 p hp).2 _ _
        · change p.tree.splitIndex p.mark (p.embed fslot)=_
          rw [p.tree.splitIndex_low_eq_of_high p.mark (p.embed c) (p.embed fslot) hhc (by
            rw [(T.markedAttach_embed_preserves 0 p hp).2];omega)]
          exact (T.markedAttach_embed_preserves 0 p hp).2 _ _
      have hneq : nativeObservedRemainingTarget c p useNew≠p.embed fslot := by
        intro heq
        rw [heq,p.tree.splitIndex_self] at hsplitf
        have hlen:=p.tree.splitIndex_le_clockLength (p.embed c) p.mark
        omega
      have hlowmass : partitionPoint 0 (pre++(mid++tail))
          (p.tree.splitIndex (nativeObservedRemainingTarget c p useNew) (p.embed fslot))≤Cmass*W := by
        rw [hsplitf]
        exact (partitionPoint_mono _ ho hcf).trans (by simpa only [hcut] using hmass)
      have hrad : M.R (partitionPoint 0 as U)≤
          M.R (partitionPoint 0 as (p.tree.splitIndex (p.embed c) p.mark)) :=
        comparisonSweepQuantile_monotone M.context.hc M.context.hk M.context.hkc M.context.hm M.context.hM
          M.alpha (partitionPoint_mono as (finiteCutMasses_ordered us hus k) hhigh)
      have Hrow:=hk pre mid tail hcut hmass p.tree (p.embed c) p.mark (p.embed b) U hmid hU
        hSource hhigh hsplitb _ (hWU.trans hrad) rfl (by linarith) (by linarith)
        (G.retainOnMarked 0 p hp) forms initial (fun e=>by
          simpa only [G.retained_source_mass] using hmassG e)
        (nativeObservedRemainingTarget c p useNew) (p.embed fslot) hneq hlowmass
      simpa only [ActualNaturalBoundaryShape.retained_canonical_restProduct] using Hrow
    · simpa only [abs_zero] using hB
  have Hsum:=marked_list_weight_abs_le (T.markedAttach 0) _ hrow
  rw [T.markedAttach_variation ho,sub_zero] at Hsum
  dsimp only [B,K,q,as,W] at Hsum
  simpa only [nativeCanonicalObservedFreshHighRow,mul_assoc] using Hsum

end OAI.SKFluctuations.Cavity
