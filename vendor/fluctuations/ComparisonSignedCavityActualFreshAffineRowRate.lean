module

public import ComparisonSignedCavityActualFreshAffineRow

@[expose] public section

noncomputable section
set_option maxHeartbeats 11000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_signed_fresh_affine_high_row_saved_cubic
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
          |nativeCanonicalObservedFreshAffineHighRow n a M T (pre.length+mid.length) U c b fslot useNew
            G forms q (retainedStarMixedClock n M.bf M.hf as)|≤
            (2*(T.leaves:ℝ))*C*(n:ℝ)^(-eta)*(W*M.xs^2*(Cp^a*sourceMonomialScale M.xs W initial)) := by
  obtain ⟨Cp,C,hCp,hC,H⟩:=eventually_actual_signed_fresh_high_row_saved_cubic
    a Bclock Temp Cmass Ccal hTemp hCmass hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  refine ⟨Cp,(1+Temp)*C,hCp,mul_pos (by linarith) hC,?_⟩
  filter_upwards [H] with n hn
  intro M hb hh hxs hcompare L us hus hret hmesh
  filter_upwards [hn M hb hh hxs hcompare L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut hmass T c b fslot useNew U hmid hU hT hcb hcf hWU hstar hz G forms initial hmassG
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus k
  have hcb' : T.splitIndex c b≤pre.length+mid.length:=by rcases hcb with H|H <;> omega
  rw [native_canonical_observed_fresh_affine_row_eq_bond_mul n a M T ho
    (pre.length+mid.length) U hU c b fslot useNew hcb' G forms]
  rw [abs_mul]
  have hBeta : |(M.bf (partitionPoint 0 (pre++(mid++tail)) (T.splitIndex c b)):ℝ)|≤1+Temp := by
    rw [abs_of_nonneg (NNReal.coe_nonneg _)]
    have H:=(M.bare_source_clock_bounds hcl hAz Temp hb hh
      (partitionPoint_mem (pre++(mid++tail)) ho (T.splitIndex c b))).2.1
    exact H.trans (by linarith)
  have Hrow:=hk pre mid tail hcut hmass T c b fslot useNew U hmid hU hT hcb hcf hWU hstar hz
    G forms initial hmassG
  have Hmul:=mul_le_mul hBeta Hrow (abs_nonneg _) (by linarith : 0≤1+Temp)
  convert Hmul using 1 <;> ring

end OAI.SKFluctuations.Cavity
