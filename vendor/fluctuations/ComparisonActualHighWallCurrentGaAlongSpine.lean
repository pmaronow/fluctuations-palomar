module

public import ComparisonActualHighWallTripleGScalarRaw
public import ComparisonActualHighWallCurrentGaContractsAlong
public import ComparisonActualGeneralTripleIncomingSource
public import ComparisonActualGeneralTripleStarIncomingSource
public import ComparisonActualGeneralTriplePowerSource
public import ComparisonActualGeneralGProjectedRowLaw
public import ComparisonSignedCavityEventuallyInheritedSpineGAllRates
public import ComparisonSignedCavityEventuallyInheritedSpineGIncomingRate
public import ComparisonSignedCavityEventuallyInheritedSpineGPowerRate
public import ComparisonSignedCavityEventuallyInheritedSpineGStarIncomingRate
public import ComparisonActualHighWallCurrentGaAlongTriple

@[expose] public section

noncomputable section
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity LaplaceWindowFormalization NativeOverlapMinimum
variable {dim : ℕ→ℕ}

theorem actual_high_wall_bf_le_clock_bound
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) : (M.bf u:ℝ) ≤ max Bclock 0 := by
  have H:=M.data.total_clock_le M.alpha u hu
  have Hh:=(M.hf u).coe_nonneg
  exact (show (M.bf u:ℝ) ≤ M.data.T by linarith).trans (M.hT.trans (le_max_left _ _))

theorem eventually_actual_high_wall_generated_spine_G_incoming_from_triple_along (hdim : Tendsto dim atTop atTop)
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Cp Ch : ℝ}
    {a b d rBound : ℕ} {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0) (hCt : 0  ≤  Ct)
    (hfixed : ∀n,(M n).xs=(M n).data.d) (hxsW : ∀n,(M n).xs  ≤  W n)
    (hCp : 0  ≤  Cp) (hCh : 0  ≤  Ch) (hC : ∀j,0  ≤  Cpower j ∧ 0  ≤  Cbase j)
    (H : ActualHighWallGeneratedTripleIncomingErrorOnEveryFinalNetAlong a b d eta saving Cmass Cp Ch Cpower Cbase M W w) :
    ∃Cg : ℝ,0 < Cg ∧ ActualHighWallGeneratedSpineGIncomingOnEveryFinalNetAlong a b d rBound
      eta saving Cmass (max Bclock 0) Cg Cp Ch Cpower Cbase M W w := by
  have hTemp : 0 ≤ max Bclock 0:=le_max_right _ _
  obtain ⟨Cg,hCg,HG⟩:=eventually_actual_high_wall_triple_G_scalar_raw_bound
    (D₀:=D) rBound Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cg,hCg,?_⟩
  filter_upwards [H,hdim.eventually HG] with n hn hnG
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hbDegree e₀ hIn hi x hxsx hxW hmi
    V Q spine hcount p hp rr hrr zz hzz hpH hrH hzH hef hac hleaves v hWv hvr hlow hz
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let κ:=nativeObservedGScalar
    (spine.graftDiagram ((((NativeObservedDiagram.identity T).observe p).observe rr).observe zz))
    P.live.test.target U (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (finiteCutMasses us r))
  let raw:=(M n).xs+partitionPoint 0 (finiteCutMasses us r) (zz.tree.splitIndex (zz.embed rr.mark) zz.mark)
  let budget:=nativeResetPairedBudget (dim n) a b d eta saving Cp Ch Cpower Cbase (M n).xs (W n) v
    ((M n).xs+partitionPoint 0 (finiteCutMasses us r) pre.length)
    (sourceMonomialScale x (W n) (nativeGeneratedExteriorInitial P.live.test pre.length))
    (sourceMonomialScale x (W n) (nativeGeneratedCompleteInitial P.live.test pre.length))
  have hv:0  ≤  v:=((M n).hxs.le.trans (hxsW n)).trans hWv
  have Hκ : |κ| * raw  ≤  Cg*v := by
    have HH:=hnG (M n) (hfixed n) (pre++(mid++tail)) ho T V P.live.test Q
      (pre.length+mid.length) U spine p hp rr hrr zz hzz (by omega) hleaves hac hpH
      (by simpa only [hcut,hvr] using (hxsW n).trans hWv)
      (by have Hz : (M n).z  ≤  v:=by linarith only [hz,hv]
          simpa only [hcut,hvr] using Hz)
    simpa only [κ,raw,hcut,hvr] using HH
  have HP:=hr pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hbDegree e₀ hIn hi
    x hxsx hxW hmi p hp rr hrr zz hzz hpH hrH hzH hef v hWv hvr hlow hz
  have Hbudget : 0  ≤  budget := by
    have hx0:0  ≤  x:=(M n).hxs.le.trans hxsx
    have hW0:0  ≤  W n:=hx0.trans hxW
    apply native_reset_paired_budget_nonneg (dim n) a b d eta saving hCp hCh hC (M n).hxs.le
      ((M n).hxs.le.trans (hxsW n)) hv
      (add_nonneg (M n).hxs.le (partitionPoint_mem _ (finiteCutMasses_ordered us hus r) _).1)
      <;> unfold sourceMonomialScale <;> positivity
  have hEF : U  ≤  zz.tree.splitIndex (zz.embed rr.mark) zz.mark := by
    apply zz.tree.splitIndex_cut_trans U (zz.embed rr.mark)
      (zz.embed (rr.embed (p.embed P.live.test.target))) zz.mark _ hzH
    rw [ClockTree.splitIndex_symm,(rr.tree.markedAttach_embed_preserves 0 zz hzz).2]
    exact hrH
  have hpoint : partitionPoint 0 (finiteCutMasses us r) (pre.length+mid.length)=(w n).star.val := by
    rw [hindex]
    exact nativeRetainedCut_partitionPoint _ (finiteCutMasses_ordered us hus r) (w n).star
      (finiteCutMasses_nodes us r hstar)
  have HE:=actual_general_triple_spine_G_value_eq spine (M n).bf (M n).hf
    ((M n).data.bf_monotone (M n).alpha) ((M n).data.hf_monotone (M n).alpha) ho U p rr zz hEF q
  simp only [hcut,hpoint,hcount] at HE
  change actualGeneralTripleSpineGValue spine (M n).bf (M n).hf U p rr zz q=
    κ*(-((M n).bf (partitionPoint 0 (finiteCutMasses us r)
      (zz.tree.splitIndex (zz.embed rr.mark) zz.mark)):ℝ)*
      actualGeneralTripleResetPairedErrorValue (dim n) T P.live.test (M n).bf (M n).hf p rr zz q d
        (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)) at HE
  have HBond : 0  ≤  ((M n).bf (partitionPoint 0 (finiteCutMasses us r)
      (zz.tree.splitIndex (zz.embed rr.mark) zz.mark)):ℝ) ∧
      ((M n).bf (partitionPoint 0 (finiteCutMasses us r)
        (zz.tree.splitIndex (zz.embed rr.mark) zz.mark)):ℝ)  ≤  (max Bclock 0) :=
    ⟨NNReal.coe_nonneg _,(actual_high_wall_bf_le_clock_bound (M n) _
      (partitionPoint_mem _ (finiteCutMasses_ordered us hus r) _))⟩
  rw [HE,abs_mul,abs_mul,abs_neg,abs_of_nonneg HBond.1]
  change |κ| * (_*_)  ≤  (max Bclock 0)*Cg*v*budget
  calc
    _  ≤  |κ| * ((max Bclock 0)*(budget*raw)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul HBond.2 HP (abs_nonneg _) hTemp) (abs_nonneg κ)
    _ = (max Bclock 0)*budget*(|κ| * raw) := by ring
    _  ≤  (max Bclock 0)*budget*(Cg*v) := mul_le_mul_of_nonneg_left Hκ (mul_nonneg hTemp Hbudget)
    _ = (max Bclock 0)*Cg*v*budget := by ring

theorem eventually_actual_high_wall_generated_spine_G_star_incoming_from_triple_along (hdim : Tendsto dim atTop atTop)
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Cp Ch : ℝ}
    {a b d rBound : ℕ} {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0) (hCt : 0  ≤  Ct)
    (hfixed : ∀n,(M n).xs=(M n).data.d) (hxsW : ∀n,(M n).xs  ≤  W n)
    (hCp : 0  ≤  Cp) (hCh : 0  ≤  Ch) (hC : ∀j,0  ≤  Cpower j ∧ 0  ≤  Cbase j)
    (H : ActualHighWallGeneratedTripleStarIncomingErrorOnEveryFinalNetAlong a b d eta saving Cmass Cp Ch Cpower Cbase M W w) :
    ∃Cg : ℝ,0 < Cg ∧ ActualHighWallGeneratedSpineGStarIncomingOnEveryFinalNetAlong a b d rBound
      eta saving Cmass (max Bclock 0) Cg Cp Ch Cpower Cbase M W w := by
  have hTemp : 0 ≤ max Bclock 0:=le_max_right _ _
  obtain ⟨Cg,hCg,HG⟩:=eventually_actual_high_wall_triple_G_scalar_raw_bound
    (D₀:=D) rBound Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cg,hCg,?_⟩
  filter_upwards [H,hdim.eventually HG] with n hn hnG
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hbDegree e₀ hIn hi x hxsx hxW hmi
    V Q spine hcount p hp rr hrr zz hzz hpH hrH hzH hef hac hleaves v hWv hvr hlow hz
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let κ:=nativeObservedGScalar
    (spine.graftDiagram ((((NativeObservedDiagram.identity T).observe p).observe rr).observe zz))
    P.live.test.target U (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (finiteCutMasses us r))
  let raw:=(M n).xs+partitionPoint 0 (finiteCutMasses us r) (zz.tree.splitIndex (zz.embed rr.mark) zz.mark)
  let budget:=nativeResetPairedBudget (dim n) a b d eta saving Cp Ch Cpower Cbase (M n).xs (W n) v
    ((M n).xs+partitionPoint 0 (finiteCutMasses us r) (pre.length+mid.length))
    (sourceMonomialScale x (W n) (nativeGeneratedExteriorInitial P.live.test pre.length))
    (sourceMonomialScale x (W n) (nativeGeneratedCompleteInitial P.live.test pre.length))
  have hv:0  ≤  v:=((M n).hxs.le.trans (hxsW n)).trans hWv
  have Hκ : |κ| * raw  ≤  Cg*v := by
    have HH:=hnG (M n) (hfixed n) (pre++(mid++tail)) ho T V P.live.test Q
      (pre.length+mid.length) U spine p hp rr hrr zz hzz (by omega) hleaves hac hpH
      (by simpa only [hcut,hvr] using (hxsW n).trans hWv)
      (by have Hz : (M n).z  ≤  v:=by linarith only [hz,hv]
          simpa only [hcut,hvr] using Hz)
    simpa only [κ,raw,hcut,hvr] using HH
  have HP:=hr pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hbDegree e₀ hIn hi
    x hxsx hxW hmi p hp rr hrr zz hzz hpH hrH hzH hef v hWv hvr hlow hz
  have Hbudget : 0  ≤  budget := by
    have hx0:0  ≤  x:=(M n).hxs.le.trans hxsx
    have hW0:0  ≤  W n:=hx0.trans hxW
    apply native_reset_paired_budget_nonneg (dim n) a b d eta saving hCp hCh hC (M n).hxs.le
      ((M n).hxs.le.trans (hxsW n)) hv
      (add_nonneg (M n).hxs.le (partitionPoint_mem _ (finiteCutMasses_ordered us hus r) _).1)
      <;> unfold sourceMonomialScale <;> positivity
  have hEF : U  ≤  zz.tree.splitIndex (zz.embed rr.mark) zz.mark := by
    apply zz.tree.splitIndex_cut_trans U (zz.embed rr.mark)
      (zz.embed (rr.embed (p.embed P.live.test.target))) zz.mark _ hzH
    rw [ClockTree.splitIndex_symm,(rr.tree.markedAttach_embed_preserves 0 zz hzz).2]
    exact hrH
  have hpoint : partitionPoint 0 (finiteCutMasses us r) (pre.length+mid.length)=(w n).star.val := by
    rw [hindex]
    exact nativeRetainedCut_partitionPoint _ (finiteCutMasses_ordered us hus r) (w n).star
      (finiteCutMasses_nodes us r hstar)
  have HE:=actual_general_triple_spine_G_value_eq spine (M n).bf (M n).hf
    ((M n).data.bf_monotone (M n).alpha) ((M n).data.hf_monotone (M n).alpha) ho U p rr zz hEF q
  simp only [hcut,hpoint,hcount] at HE
  change actualGeneralTripleSpineGValue spine (M n).bf (M n).hf U p rr zz q=
    κ*(-((M n).bf (partitionPoint 0 (finiteCutMasses us r)
      (zz.tree.splitIndex (zz.embed rr.mark) zz.mark)):ℝ)*
      actualGeneralTripleResetPairedErrorValue (dim n) T P.live.test (M n).bf (M n).hf p rr zz q d
        (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)) at HE
  have HBond : 0  ≤  ((M n).bf (partitionPoint 0 (finiteCutMasses us r)
      (zz.tree.splitIndex (zz.embed rr.mark) zz.mark)):ℝ) ∧
      ((M n).bf (partitionPoint 0 (finiteCutMasses us r)
        (zz.tree.splitIndex (zz.embed rr.mark) zz.mark)):ℝ)  ≤  (max Bclock 0) :=
    ⟨NNReal.coe_nonneg _,(actual_high_wall_bf_le_clock_bound (M n) _
      (partitionPoint_mem _ (finiteCutMasses_ordered us hus r) _))⟩
  rw [HE,abs_mul,abs_mul,abs_neg,abs_of_nonneg HBond.1]
  change |κ| * (_*_)  ≤  (max Bclock 0)*Cg*v*budget
  calc
    _  ≤  |κ| * ((max Bclock 0)*(budget*raw)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul HBond.2 HP (abs_nonneg _) hTemp) (abs_nonneg κ)
    _ = (max Bclock 0)*budget*(|κ| * raw) := by ring
    _  ≤  (max Bclock 0)*budget*(Cg*v) := mul_le_mul_of_nonneg_left Hκ (mul_nonneg hTemp Hbudget)
    _ = (max Bclock 0)*Cg*v*budget := by ring

theorem eventually_actual_high_wall_generated_spine_G_power_from_triple_along (hdim : Tendsto dim atTop atTop)
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass : ℝ}
    {b d rBound : ℕ} {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0) (hCt : 0  ≤  Ct)
    (hfixed : ∀n,(M n).xs=(M n).data.d) (hxsW : ∀n,(M n).xs  ≤  W n)
    (hC : ∀j,0  ≤  Cpower j ∧ 0  ≤  Cbase j)
    (H : ActualHighWallGeneratedTriplePowerErrorOnEveryFinalNetAlong b d eta saving Cmass Cpower Cbase M W w) :
    ∃Cg : ℝ,0 < Cg ∧ ActualHighWallGeneratedSpineGPowerOnEveryFinalNetAlong b d rBound
      eta saving Cmass (max Bclock 0) Cg Cpower Cbase M W w := by
  have hTemp : 0 ≤ max Bclock 0:=le_max_right _ _
  obtain ⟨Cg,hCg,HG⟩:=eventually_actual_high_wall_triple_G_scalar_raw_bound
    (D₀:=D) rBound Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cg,hCg,?_⟩
  filter_upwards [H,hdim.eventually HG] with n hn hnG
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht hbDegree hIn x hxsx hxW hmi
    V Q spine hcount p hp rr hrr zz hzz hpH hrH hzH hef hac hleaves v hWv hvr hlow hz
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let κ:=nativeObservedGScalar
    (spine.graftDiagram ((((NativeObservedDiagram.identity T).observe p).observe rr).observe zz))
    P.live.test.target U (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (finiteCutMasses us r))
  let raw:=(M n).xs+partitionPoint 0 (finiteCutMasses us r) (zz.tree.splitIndex (zz.embed rr.mark) zz.mark)
  let budget:=∑j∈Finset.range d,Cpower j*(((dim n):ℝ)^(-eta))^2*(savedProjectedScale (M n).xs (W n) v)^2*
    ((Cbase j)^b*sourceMonomialScale x (W n) (nativeGeneratedCompleteInitial P.live.test pre.length))*
    ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(d-1)
  have hv:0  ≤  v:=((M n).hxs.le.trans (hxsW n)).trans hWv
  have Hκ : |κ| * raw  ≤  Cg*v := by
    have HH:=hnG (M n) (hfixed n) (pre++(mid++tail)) ho T V P.live.test Q
      (pre.length+mid.length) U spine p hp rr hrr zz hzz (by omega) hleaves hac hpH
      (by simpa only [hcut,hvr] using (hxsW n).trans hWv)
      (by have Hz : (M n).z  ≤  v:=by linarith only [hz,hv]
          simpa only [hcut,hvr] using Hz)
    simpa only [κ,raw,hcut,hvr] using HH
  have HP:=hr pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht hbDegree hIn
    x hxsx hxW hmi p hp rr hrr zz hzz hpH hrH hzH hef v hWv hvr hlow hz
  have Hbudget : 0  ≤  budget := by
    have hx0:0  ≤  x:=(M n).hxs.le.trans hxsx
    have hW0:0  ≤  W n:=hx0.trans hxW
    apply Finset.sum_nonneg
    intro j _
    have h1:0  ≤  Cpower j:=(hC j).1
    have h2:0  ≤  Cbase j:=(hC j).2
    unfold sourceMonomialScale
    positivity
  have hEF : U  ≤  zz.tree.splitIndex (zz.embed rr.mark) zz.mark := by
    apply zz.tree.splitIndex_cut_trans U (zz.embed rr.mark)
      (zz.embed (rr.embed (p.embed P.live.test.target))) zz.mark _ hzH
    rw [ClockTree.splitIndex_symm,(rr.tree.markedAttach_embed_preserves 0 zz hzz).2]
    exact hrH
  have hpoint : partitionPoint 0 (finiteCutMasses us r) (pre.length+mid.length)=(w n).star.val := by
    rw [hindex]
    exact nativeRetainedCut_partitionPoint _ (finiteCutMasses_ordered us hus r) (w n).star
      (finiteCutMasses_nodes us r hstar)
  have HE:=actual_general_triple_spine_G_value_eq spine (M n).bf (M n).hf
    ((M n).data.bf_monotone (M n).alpha) ((M n).data.hf_monotone (M n).alpha) ho U p rr zz hEF q
  simp only [hcut,hpoint,hcount] at HE
  change actualGeneralTripleSpineGValue spine (M n).bf (M n).hf U p rr zz q=
    κ*(-((M n).bf (partitionPoint 0 (finiteCutMasses us r)
      (zz.tree.splitIndex (zz.embed rr.mark) zz.mark)):ℝ)*
      actualGeneralTripleResetPairedErrorValue (dim n) T P.live.test (M n).bf (M n).hf p rr zz q d
        (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)) at HE
  have HBond : 0  ≤  ((M n).bf (partitionPoint 0 (finiteCutMasses us r)
      (zz.tree.splitIndex (zz.embed rr.mark) zz.mark)):ℝ) ∧
      ((M n).bf (partitionPoint 0 (finiteCutMasses us r)
        (zz.tree.splitIndex (zz.embed rr.mark) zz.mark)):ℝ)  ≤  (max Bclock 0) :=
    ⟨NNReal.coe_nonneg _,(actual_high_wall_bf_le_clock_bound (M n) _
      (partitionPoint_mem _ (finiteCutMasses_ordered us hus r) _))⟩
  rw [HE,abs_mul,abs_mul,abs_neg,abs_of_nonneg HBond.1]
  change |κ| * (_*_)  ≤  (max Bclock 0)*Cg*v*budget
  calc
    _  ≤  |κ| * ((max Bclock 0)*(budget*raw)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul HBond.2 HP (abs_nonneg _) hTemp) (abs_nonneg κ)
    _ = (max Bclock 0)*budget*(|κ| * raw) := by ring
    _  ≤  (max Bclock 0)*budget*(Cg*v) := mul_le_mul_of_nonneg_left Hκ (mul_nonneg hTemp Hbudget)
    _ = (max Bclock 0)*Cg*v*budget := by ring

theorem eventually_actual_high_wall_same_star_spine_G_word_bounds_along (hdim : Tendsto dim atTop atTop)
    {m delta eta cl cu Az C0 Ct D Bclock : ℝ}
    (Cmass : ℝ) (hCm : 0  ≤  Cmass)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0) (hCt : 0  ≤  Ct)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).data.d)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (saving : ℝ) (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k : ℕ,ActualHighWallMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) :
      (∀a b d rBound : ℕ,∃Cg : ℝ,0 < Cg ∧ ∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
        ∃Cpower Cbase : ℕ→ℝ,(∀j,0 < Cpower j ∧ 0 < Cbase j) ∧
        ActualHighWallGeneratedSpineGIncomingOnEveryFinalNetAlong a b d rBound eta saving Cmass (max Bclock 0) Cg Cp Ch Cpower Cbase M W w) ∧
      (∀a b d rBound : ℕ,∃Cg : ℝ,0 < Cg ∧ ∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
        ∃Cpower Cbase : ℕ→ℝ,(∀j,0 < Cpower j ∧ 0 < Cbase j) ∧
        ActualHighWallGeneratedSpineGStarIncomingOnEveryFinalNetAlong a b d rBound eta saving Cmass (max Bclock 0) Cg Cp Ch Cpower Cbase M W w) ∧
      ∀b d rBound : ℕ,∃Cg : ℝ,0 < Cg ∧ ∃Cpower Cbase : ℕ→ℝ,(∀j,0 < Cpower j ∧ 0 < Cbase j) ∧
        ActualHighWallGeneratedSpineGPowerOnEveryFinalNetAlong b d rBound eta saving Cmass (max Bclock 0) Cg Cpower Cbase M W w := by
  obtain ⟨HI,HS,HP⟩:=
    eventually_actual_high_wall_same_star_triple_error_bounds_along hdim Cmass hCm hm hdelta hroom hgap
      hcl hcu hAz hC0 hCt M W hcanonical hWlim hfixed saving w Hmixed
  have hxW (n) : (M n).xs  ≤  W n := by
    rw [hcanonical n,hfixed n]
  have hxs : ∀ᶠn : ℕ in atTop,(M n).xs  ≤  1 := by
    filter_upwards [hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))] with n hn
    exact (hxW n).trans hn
  refine ⟨?_,?_,?_⟩
  · intro a b d rBound
    obtain ⟨Cp,hCp,Ch,hCh,Cpower,Cbase,hC,H⟩:=HI a b d
    obtain ⟨Cg,hCg,HG⟩:=eventually_actual_high_wall_generated_spine_G_incoming_from_triple_along hdim (rBound:=rBound)
      hm hdelta hroom hcl hcu hAz hC0 hCt hfixed hxW hCp.le hCh.le
      (fun j=>⟨(hC j).1.le,(hC j).2.le⟩) H
    exact ⟨Cg,hCg,Cp,hCp,Ch,hCh,Cpower,Cbase,hC,HG⟩
  · intro a b d rBound
    obtain ⟨Cp,hCp,Ch,hCh,Cpower,Cbase,hC,H⟩:=HS a b d
    obtain ⟨Cg,hCg,HG⟩:=eventually_actual_high_wall_generated_spine_G_star_incoming_from_triple_along hdim (rBound:=rBound)
      hm hdelta hroom hcl hcu hAz hC0 hCt hfixed hxW hCp.le hCh.le
      (fun j=>⟨(hC j).1.le,(hC j).2.le⟩) H
    exact ⟨Cg,hCg,Cp,hCp,Ch,hCh,Cpower,Cbase,hC,HG⟩
  · intro b d rBound
    obtain ⟨Cpower,Cbase,hC,H⟩:=HP b d
    obtain ⟨Cg,hCg,HG⟩:=eventually_actual_high_wall_generated_spine_G_power_from_triple_along hdim (rBound:=rBound)
      hm hdelta hroom hcl hcu hAz hC0 hCt hfixed hxW
      (fun j=>⟨(hC j).1.le,(hC j).2.le⟩) H
    exact ⟨Cg,hCg,Cpower,Cbase,hC,HG⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
