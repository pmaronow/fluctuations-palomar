module

public import ComparisonSignedCavityActualSpineGStarIncomingRate
public import ComparisonSignedCavityInheritedTripleGScalarRate

@[expose] public section

noncomputable section
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

theorem eventually_inherited_generated_spine_G_star_incoming_from_triple
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Temp Cp Ch : ℝ}
    {a b d rBound : ℕ} {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (Cf : ℝ) (hCf : 0 ≤ Cf)
    (hsource : ∀ᶠn : ℕ in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hxs : ∀ᶠn : ℕ in atTop,(M n).xs ≤ 1) (hxsW : ∀n,(M n).xs ≤ W n)
    (hCp : 0 ≤ Cp) (hCh : 0 ≤ Ch) (hC : ∀j,0 ≤ Cpower j ∧ 0 ≤ Cbase j)
    (H : ActualGeneratedTripleStarIncomingErrorOnEveryFinalNet a b d eta saving Cmass Cp Ch Cpower Cbase M W w) :
    ∃Cg : ℝ,0 < Cg ∧ ActualGeneratedSpineGStarIncomingOnEveryFinalNet a b d rBound
      eta saving Cmass Temp Cg Cp Ch Cpower Cbase M W w := by
  obtain ⟨Cg,hCg,HG⟩:=eventually_actual_minimum_inherited_triple_G_scalar_raw_bound
    (D₀:=D) rBound Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cg,hCg,?_⟩
  filter_upwards [H,HG,hxs,hsource] with n hn hnG hnxs hnSource
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hbDegree e₀ hIn hi x hxsx hxW hmi
    V Q spine hcount p hp rr hrr zz hzz hpH hrH hzH hef hac hleaves v hWv hvr hlow hz
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let κ:=nativeObservedGScalar
    (spine.graftDiagram ((((NativeObservedDiagram.identity T).observe p).observe rr).observe zz))
    P.live.test.target U (fun j=>
      ((M n).hf (partitionPoint 0 (finiteCutMasses us r) j):ℝ)+
      ((M n).bf (partitionPoint 0 (finiteCutMasses us r) j):ℝ)*
        orderedPathS (n+1) (M n).bf (M n).hf (partitionPoint 0 (finiteCutMasses us r) j))
  let raw:=(M n).xs+partitionPoint 0 (finiteCutMasses us r) (zz.tree.splitIndex (zz.embed rr.mark) zz.mark)
  let budget:=nativeResetPairedBudget n a b d eta saving Cp Ch Cpower Cbase (M n).xs (W n) v
    ((M n).xs+partitionPoint 0 (finiteCutMasses us r) (pre.length+mid.length))
    (sourceMonomialScale x (W n) (nativeGeneratedExteriorInitial P.live.test pre.length))
    (sourceMonomialScale x (W n) (nativeGeneratedCompleteInitial P.live.test pre.length))
  have hv:0 ≤ v:=((M n).hxs.le.trans (hxsW n)).trans hWv
  have Hκ : |κ| * raw ≤ Cg*v := by
    have HH:=hnG (M n) hnSource hnxs (pre++(mid++tail)) ho T V P.live.test Q
      (pre.length+mid.length) U spine p hp rr hrr zz hzz (by omega) hleaves hac hpH
      (by simpa only [hcut,hvr] using (hxsW n).trans hWv)
      (by have Hz : (M n).z ≤ v:=by linarith only [hz,hv]
          simpa only [hcut,hvr] using Hz)
    simpa only [κ,raw,hcut,hvr] using HH
  have HP:=hr pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hbDegree e₀ hIn hi
    x hxsx hxW hmi p hp rr hrr zz hzz hpH hrH hzH hef v hWv hvr hlow hz
  have Hbudget : 0 ≤ budget := by
    have hx0:0 ≤ x:=(M n).hxs.le.trans hxsx
    have hW0:0 ≤ W n:=hx0.trans hxW
    apply native_reset_paired_budget_nonneg n a b d eta saving hCp hCh hC (M n).hxs.le
      ((M n).hxs.le.trans (hxsW n)) hv
      (add_nonneg (M n).hxs.le (partitionPoint_mem _ (finiteCutMasses_ordered us hus r) _).1)
      <;> unfold sourceMonomialScale <;> positivity
  have hEF : U ≤ zz.tree.splitIndex (zz.embed rr.mark) zz.mark := by
    apply zz.tree.splitIndex_cut_trans U (zz.embed rr.mark)
      (zz.embed (rr.embed (p.embed P.live.test.target))) zz.mark _ hzH
    rw [ClockTree.splitIndex_symm,(rr.tree.markedAttach_embed_preserves 0 zz hzz).2]
    exact hrH
  have hpoint : partitionPoint 0 (finiteCutMasses us r) (pre.length+mid.length)=(w n).star.val := by
    rw [hindex]
    exact nativeRetainedCut_partitionPoint _ (finiteCutMasses_ordered us hus r) (w n).star
      (finiteCutMasses_nodes us r hstar)
  have HE:=native_actual_triple_spine_G_value_eq spine (M n) ho U p rr zz hEF q
  simp only [hcut,hpoint,hcount] at HE
  change nativeActualTripleSpineGValue spine (M n) U p rr zz q=
    κ*(-((M n).bf (partitionPoint 0 (finiteCutMasses us r)
      (zz.tree.splitIndex (zz.embed rr.mark) zz.mark)):ℝ)*
      nativeTripleResetPairedErrorValue n T P.live.test (M n) p rr zz q d
        (orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val)) at HE
  have HBond : 0 ≤ ((M n).bf (partitionPoint 0 (finiteCutMasses us r)
      (zz.tree.splitIndex (zz.embed rr.mark) zz.mark)):ℝ) ∧
      ((M n).bf (partitionPoint 0 (finiteCutMasses us r)
        (zz.tree.splitIndex (zz.embed rr.mark) zz.mark)):ℝ) ≤ Temp :=
    ⟨NNReal.coe_nonneg _,(hnSource _
      (partitionPoint_mem _ (finiteCutMasses_ordered us hus r) _)).1⟩
  rw [HE,abs_mul,abs_mul,abs_neg,abs_of_nonneg HBond.1]
  change |κ| * (_*_) ≤ Temp*Cg*v*budget
  calc
    _ ≤ |κ| * (Temp*(budget*raw)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul HBond.2 HP (abs_nonneg _) hTemp) (abs_nonneg κ)
    _ = Temp*budget*(|κ| * raw) := by ring
    _ ≤ Temp*budget*(Cg*v) := mul_le_mul_of_nonneg_left Hκ (mul_nonneg hTemp Hbudget)
    _ = Temp*Cg*v*budget := by ring

end OAI.SKFluctuations.LaplaceWindowFormalization
