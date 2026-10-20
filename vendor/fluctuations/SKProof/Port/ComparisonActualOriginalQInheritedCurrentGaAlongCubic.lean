module

public import SKProof.Port.ComparisonActualOriginalQActualCurrentGaAlongContracts
public import SKProof.Port.ComparisonActualOriginalQActualGProjectedRowLaw
public import SKProof.Port.ComparisonActualOriginalQGTripleRowAlgebra
public import SKProof.Port.ComparisonActualOriginalQScalarRadiusSavedRow
public import ComparisonSignedCavityInheritedCurrentGaAlongCubic
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import SKProof.Port.ComparisonActualOriginalQResourcePhysicalFactories
public import SKProof.Port.ComparisonActualOriginalQPullbackFourInterfaces
public import SKProof.Port.ComparisonActualOriginalQSourceProjectionAlong
public import SKProof.Port.ComparisonActualOriginalQGaCurrentPrerequisites
public import SKProof.Port.ComparisonActualOriginalQInheritedCurrentGaAlongNormalized

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity LaplaceWindowFormalization NativeOverlapMinimum ActualThetaZeroOverlapMinimum
variable {dim : ℕ→ℕ}

theorem actual_spine_G_incoming_cubic_from_normalized_along_original_q (hdim : Tendsto dim atTop atTop)
    {m delta cl cu Az C0 Ct D Bclock eta Cmass Ai Ap Temp Cg : ℝ} {a b d rBound : ℕ}
    (heta : 0 < eta) (hAi : 0 ≤ Ai) (hAp : 0 ≤ Ap) (hTemp : 0 ≤ Temp) (hCg : 0 ≤ Cg)
    (hm : 0 < m) (hcu : 0 ≤ cu) (hC0 : 0 < C0)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxsW : ∀n,(M n).xs ≤ W n) {w : ℕ→ActualSlowWindowChoice}
    (H : ActualNormalizedSpineGIncomingOnEveryFinalNetAlong_original_q a b d (rBound+3+d) eta Cmass Temp Cg Ai Ap M W w) :
    ActualSpineGIncomingCubicOnEveryFinalNetAlong_original_q a b d rBound eta Cmass M W w := by
  let Cv:=4*((rBound:ℝ)+1)*(rBound+2)
  have HrowI:=eventually_actual_minimum_scalar_radius_saved_row_decay_original_q heta (Cv*(Temp*Cg*Ai))
    (by dsimp only [Cv];positivity) (delta:=delta) (cl:=cl) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hcu hC0
  have HrowP:=eventually_actual_minimum_scalar_radius_saved_row_decay_original_q heta (Cv*(Temp*Cg*Ap))
    (by dsimp only [Cv];positivity) (delta:=delta) (cl:=cl) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hcu hC0
  filter_upwards [H,hdim.eventually HrowI,hdim.eventually HrowP] with n hn hnI hnP
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar,hnI (M n) us hus,hnP (M n) us hus] with r hr hrI hrP
  dsimp only at hr hrI hrP ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hdeg e₀ hIn hi hleaves
    Tcur Q spine hcount V hWV hV1 hlow hz
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).sweepBf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).sweepHf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let s:=(M n).xs+partitionPoint 0 (finiteCutMasses us r) pre.length
  let p0:=sourceMonomialScale s (W n) (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d
  let R:=fun j=>(M n).sweepRadius (partitionPoint 0 (pre++(mid++tail)) j)
  have hR (j) : 0 ≤ R j:=
    ((M n).R_bounds _).1
  have hxs0 : 0 ≤ (M n).xs:=(M n).hxs.le
  have hW : 0 < W n:=(M n).hxs.trans_le (hxsW n)
  have hs : 0 < s:=add_pos_of_pos_of_nonneg (M n).hxs
    (partitionPoint_mem _ (finiteCutMasses_ordered us hus r) _).1
  have hp0 : 0 ≤ p0:=by dsimp only [p0];unfold sourceMonomialScale;positivity
  have Hmain:=native_actual_triple_spine_G_row_abs_le_original_q spine (M n) U V q ho hleaves
    ((((dim n):ℝ)^(-eta))^2) (Temp*Cg*Ai) (Temp*Cg*Ap) p0
    (fun j=>nativeSavedIncomingScale (M n).xs (W n) s (R j))
    (fun j=>nativeSavedIncomingScale (M n).xs (W n) (W n) (R j))
    (sq_nonneg _) (by positivity) (by positivity) hp0
    (by intro j;have:=hR j;unfold nativeSavedIncomingScale savedProjectedScale savedWeightedExteriorScale;positivity)
    (by intro j;have:=hR j;unfold nativeSavedIncomingScale savedProjectedScale savedWeightedExteriorScale;positivity)
    (by
      intro p hp rr hrr zz hzz hpH hrH hzH hef hac hVR
      have hFull : (spine.graftDiagram ((((NativeObservedDiagram.identity T).observe p).observe rr).observe zz)).tree.leaves ≤ rBound+3+d := by
        have H1:=spine.graft_leaves_le ((((NativeObservedDiagram.identity T).observe p).observe rr).observe zz)
        have H2:=native_three_mark_leaves_le p hp rr hrr zz hzz
        change (spine.graftDiagram ((((NativeObservedDiagram.identity T).observe p).observe rr).observe zz)).tree.leaves ≤
          zz.tree.leaves+spine.toothCount at H1
        rw [hcount] at H1
        omega
      have hVR' : V ≤ (M n).sweepRadius (partitionPoint 0 (finiteCutMasses us r)
          (p.tree.splitIndex (p.embed P.live.test.target) p.mark)):=by simpa only [hcut] using hVR
      have Hpt:=hr pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hdeg e₀ hIn hi
        Tcur Q spine hcount p hp rr hrr zz hzz hpH hrH hzH hef hac hFull
        _ (hWV.trans hVR') rfl (by linarith) (by linarith)
      convert Hpt using 1 ; dsimp only [q,p0,s,R] ; (try simp only [hcut]) ; ring)
  rw [←hcut] at hrI hrP
  have HI:=hrI pre.length (pre.length+mid.length) U T seed depth P hP (by omega)
    (W n) V s (hxsW n) ((hxsW n).trans hWV) hV1 (by linarith) (by simpa only [hcut] using hlow)
    (by dsimp only [s];have:=(partitionPoint_mem _ (finiteCutMasses_ordered us hus r) pre.length).1;linarith)
  have HP:=hrP pre.length (pre.length+mid.length) U T seed depth P hP (by omega)
    (W n) V (W n) (hxsW n) ((hxsW n).trans hWV) hV1 (by linarith) (by simpa only [hcut] using hlow) (hxsW n)
  have Hsum:=mul_le_mul_of_nonneg_right (add_le_add HI HP) hp0
  apply Hmain.trans
  convert Hsum using 1 <;> dsimp only [Cv,R,p0,s] <;> (try simp only [hcut]) <;> ring

theorem actual_spine_G_star_incoming_cubic_from_normalized_along_original_q (hdim : Tendsto dim atTop atTop)
    {m delta cl cu Az C0 Ct D Bclock eta Cmass Ai Ap Temp Cg : ℝ} {a b d rBound : ℕ}
    (heta : 0 < eta) (hAi : 0 ≤ Ai) (hAp : 0 ≤ Ap) (hTemp : 0 ≤ Temp) (hCg : 0 ≤ Cg)
    (hm : 0 < m) (hcu : 0 ≤ cu) (hC0 : 0 < C0)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxsW : ∀n,(M n).xs ≤ W n) {w : ℕ→ActualSlowWindowChoice}
    (H : ActualNormalizedSpineGStarIncomingOnEveryFinalNetAlong_original_q a b d (rBound+3+d) eta Cmass Temp Cg Ai Ap M W w) :
    ActualSpineGStarIncomingCubicOnEveryFinalNetAlong_original_q a b d rBound eta Cmass M W w := by
  let Cv:=4*((rBound:ℝ)+1)*(rBound+2)
  have HrowI:=eventually_actual_minimum_scalar_radius_saved_row_decay_original_q heta (Cv*(Temp*Cg*Ai))
    (by dsimp only [Cv];positivity) (delta:=delta) (cl:=cl) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hcu hC0
  have HrowP:=eventually_actual_minimum_scalar_radius_saved_row_decay_original_q heta (Cv*(Temp*Cg*Ap))
    (by dsimp only [Cv];positivity) (delta:=delta) (cl:=cl) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hcu hC0
  filter_upwards [H,hdim.eventually HrowI,hdim.eventually HrowP] with n hn hnI hnP
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar,hnI (M n) us hus,hnP (M n) us hus] with r hr hrI hrP
  dsimp only at hr hrI hrP ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hdeg e₀ hIn hi hleaves
    Tcur Q spine hcount V hWV hV1 hlow hz
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).sweepBf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).sweepHf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let s:=(M n).xs+partitionPoint 0 (finiteCutMasses us r) pre.length
  let p0:=sourceMonomialScale s (W n) (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d
  let R:=fun j=>(M n).sweepRadius (partitionPoint 0 (pre++(mid++tail)) j)
  have hR (j) : 0 ≤ R j:=
    ((M n).R_bounds _).1
  have hxs0 : 0 ≤ (M n).xs:=(M n).hxs.le
  have hW : 0 < W n:=(M n).hxs.trans_le (hxsW n)
  have hs : 0 < s:=add_pos_of_pos_of_nonneg (M n).hxs
    (partitionPoint_mem _ (finiteCutMasses_ordered us hus r) _).1
  have hp0 : 0 ≤ p0:=by dsimp only [p0];unfold sourceMonomialScale;positivity
  have Hmain:=native_actual_triple_spine_G_row_abs_le_original_q spine (M n) U V q ho hleaves
    ((((dim n):ℝ)^(-eta))^2) (Temp*Cg*Ai) (Temp*Cg*Ap) p0
    (fun j=>nativeSavedIncomingScale (M n).xs (W n) (W n) (R j))
    (fun j=>nativeSavedIncomingScale (M n).xs (W n) (W n) (R j))
    (sq_nonneg _) (by positivity) (by positivity) hp0
    (by intro j;have:=hR j;unfold nativeSavedIncomingScale savedProjectedScale savedWeightedExteriorScale;positivity)
    (by intro j;have:=hR j;unfold nativeSavedIncomingScale savedProjectedScale savedWeightedExteriorScale;positivity)
    (by
      intro p hp rr hrr zz hzz hpH hrH hzH hef hac hVR
      have hFull : (spine.graftDiagram ((((NativeObservedDiagram.identity T).observe p).observe rr).observe zz)).tree.leaves ≤ rBound+3+d := by
        have H1:=spine.graft_leaves_le ((((NativeObservedDiagram.identity T).observe p).observe rr).observe zz)
        have H2:=native_three_mark_leaves_le p hp rr hrr zz hzz
        change (spine.graftDiagram ((((NativeObservedDiagram.identity T).observe p).observe rr).observe zz)).tree.leaves ≤
          zz.tree.leaves+spine.toothCount at H1
        rw [hcount] at H1
        omega
      have hVR' : V ≤ (M n).sweepRadius (partitionPoint 0 (finiteCutMasses us r)
          (p.tree.splitIndex (p.embed P.live.test.target) p.mark)):=by simpa only [hcut] using hVR
      have Hpt:=hr pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hdeg e₀ hIn hi
        Tcur Q spine hcount p hp rr hrr zz hzz hpH hrH hzH hef hac hFull
        _ (hWV.trans hVR') rfl (by linarith) (by linarith)
      convert Hpt using 1 ; dsimp only [q,p0,s,R] ; (try simp only [hcut]) ; ring)
  rw [←hcut] at hrI hrP
  have HI:=hrI pre.length (pre.length+mid.length) U T seed depth P hP (by omega)
    (W n) V (W n) (hxsW n) ((hxsW n).trans hWV) hV1 (by linarith) (by simpa only [hcut] using hlow)
    (hxsW n)
  have HP:=hrP pre.length (pre.length+mid.length) U T seed depth P hP (by omega)
    (W n) V (W n) (hxsW n) ((hxsW n).trans hWV) hV1 (by linarith) (by simpa only [hcut] using hlow) (hxsW n)
  have Hsum:=mul_le_mul_of_nonneg_right (add_le_add HI HP) hp0
  apply Hmain.trans
  convert Hsum using 1 <;> dsimp only [Cv,R,p0,s] <;> (try simp only [hcut]) <;> ring

theorem actual_spine_G_power_cubic_from_normalized_along_original_q (hdim : Tendsto dim atTop atTop)
    {m delta cl cu Az C0 Ct D Bclock eta Cmass Ap Temp Cg : ℝ} {b d rBound : ℕ}
    (heta : 0 < eta) (hAp : 0 ≤ Ap) (hTemp : 0 ≤ Temp) (hCg : 0 ≤ Cg)
    (hm : 0 < m) (hcu : 0 ≤ cu) (hC0 : 0 < C0)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxsW : ∀n,(M n).xs ≤ W n) {w : ℕ→ActualSlowWindowChoice}
    (H : ActualNormalizedSpineGPowerOnEveryFinalNetAlong_original_q b d (rBound+3+d) eta Cmass Temp Cg Ap M W w) :
    ActualSpineGPowerCubicOnEveryFinalNetAlong_original_q b d rBound eta Cmass M W w := by
  let Ai : ℝ:=0
  have hAi : 0 ≤ Ai:=le_refl 0
  let Cv:=4*((rBound:ℝ)+1)*(rBound+2)
  have HrowI:=eventually_actual_minimum_scalar_radius_saved_row_decay_original_q heta (Cv*(Temp*Cg*Ai))
    (by dsimp only [Cv];positivity) (delta:=delta) (cl:=cl) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hcu hC0
  have HrowP:=eventually_actual_minimum_scalar_radius_saved_row_decay_original_q heta (Cv*(Temp*Cg*Ap))
    (by dsimp only [Cv];positivity) (delta:=delta) (cl:=cl) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hcu hC0
  filter_upwards [H,hdim.eventually HrowI,hdim.eventually HrowP] with n hn hnI hnP
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar,hnI (M n) us hus,hnP (M n) us hus] with r hr hrI hrP
  dsimp only at hr hrI hrP ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht hdeg hIn hleaves
    Tcur Q spine hcount V hWV hV1 hlow hz
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).sweepBf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).sweepHf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let s:=(M n).xs+partitionPoint 0 (finiteCutMasses us r) pre.length
  let p0:=sourceMonomialScale s (W n) (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d
  let R:=fun j=>(M n).sweepRadius (partitionPoint 0 (pre++(mid++tail)) j)
  have hR (j) : 0 ≤ R j:=
    ((M n).R_bounds _).1
  have hxs0 : 0 ≤ (M n).xs:=(M n).hxs.le
  have hW : 0 < W n:=(M n).hxs.trans_le (hxsW n)
  have hs : 0 < s:=add_pos_of_pos_of_nonneg (M n).hxs
    (partitionPoint_mem _ (finiteCutMasses_ordered us hus r) _).1
  have hp0 : 0 ≤ p0:=by dsimp only [p0];unfold sourceMonomialScale;positivity
  have Hmain:=native_actual_triple_spine_G_row_abs_le_original_q spine (M n) U V q ho hleaves
    ((((dim n):ℝ)^(-eta))^2) (Temp*Cg*Ai) (Temp*Cg*Ap) p0
    (fun j=>nativeSavedIncomingScale (M n).xs (W n) (W n) (R j))
    (fun j=>nativeSavedIncomingScale (M n).xs (W n) (W n) (R j))
    (sq_nonneg _) (by positivity) (by positivity) hp0
    (by intro j;have:=hR j;unfold nativeSavedIncomingScale savedProjectedScale savedWeightedExteriorScale;positivity)
    (by intro j;have:=hR j;unfold nativeSavedIncomingScale savedProjectedScale savedWeightedExteriorScale;positivity)
    (by
      intro p hp rr hrr zz hzz hpH hrH hzH hef hac hVR
      have hFull : (spine.graftDiagram ((((NativeObservedDiagram.identity T).observe p).observe rr).observe zz)).tree.leaves ≤ rBound+3+d := by
        have H1:=spine.graft_leaves_le ((((NativeObservedDiagram.identity T).observe p).observe rr).observe zz)
        have H2:=native_three_mark_leaves_le p hp rr hrr zz hzz
        change (spine.graftDiagram ((((NativeObservedDiagram.identity T).observe p).observe rr).observe zz)).tree.leaves ≤
          zz.tree.leaves+spine.toothCount at H1
        rw [hcount] at H1
        omega
      have hVR' : V ≤ (M n).sweepRadius (partitionPoint 0 (finiteCutMasses us r)
          (p.tree.splitIndex (p.embed P.live.test.target) p.mark)):=by simpa only [hcut] using hVR
      have Hpt:=hr pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht hdeg hIn
        Tcur Q spine hcount p hp rr hrr zz hzz hpH hrH hzH hef hac hFull
        _ (hWV.trans hVR') rfl (by linarith) (by linarith)
      convert Hpt using 1 ; dsimp only [q,p0,s,R,Ai] ; (try simp only [hcut]) ; ring)
  rw [←hcut] at hrI hrP
  have HI:=hrI pre.length (pre.length+mid.length) U T seed depth P hP (by omega)
    (W n) V (W n) (hxsW n) ((hxsW n).trans hWV) hV1 (by linarith) (by simpa only [hcut] using hlow)
    (hxsW n)
  have HP:=hrP pre.length (pre.length+mid.length) U T seed depth P hP (by omega)
    (W n) V (W n) (hxsW n) ((hxsW n).trans hWV) hV1 (by linarith) (by simpa only [hcut] using hlow) (hxsW n)
  have Hsum:=mul_le_mul_of_nonneg_right (add_le_add HI HP) hp0
  apply Hmain.trans
  convert Hsum using 1 <;> dsimp only [Cv,R,p0,s] <;> (try simp only [hcut]) <;> ring

theorem eventually_inherited_same_star_spine_G_cubic_rows_along_original_q (hdim : Tendsto dim atTop atTop)
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Ccal : ℝ}
    (Cmass : ℝ) (hCm : 1 ≤ Cmass) (heta : 0 < eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn : ℕ in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (hcutoff : ∀ᶠn : ℕ in atTop,(M n).data.s ≤ 1/4 ∧ (M n).data.s ≤ (M n).xs)
    (saving : ℝ) (hsaving : 0 ≤ saving) (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong_original_q j k saving M W w) :
      ∀a b d rBound : ℕ,
        ActualSpineGIncomingCubicOnEveryFinalNetAlong_original_q a b d rBound eta Cmass M W w ∧
        ActualSpineGStarIncomingCubicOnEveryFinalNetAlong_original_q a b d rBound eta Cmass M W w ∧
        ActualSpineGPowerCubicOnEveryFinalNetAlong_original_q b d rBound eta Cmass M W w := by
  obtain ⟨HI,HS,HP⟩:=
    eventually_inherited_same_star_spine_G_normalized_bounds_along_original_q hdim Cmass hCm hm hdelta hroom hgap
      hcl hcu hAz hC0 hCt hTemp hCf hCcal M W hcanonical hWlim hcompare hsource hcutoff saving hsaving w Hmixed
  have hxW (n) : (M n).xs ≤ W n := by
    rw [hcanonical n]
    exact le_max_left _ _

  intro a b d rBound
  obtain ⟨Cgi,Ai,Api,hCgi,hAi,hApi,Hi⟩:=HI a b d (rBound+3+d)
  obtain ⟨Cgs,As,Aps,hCgs,hAs,hAps,Hs⟩:=HS a b d (rBound+3+d)
  obtain ⟨Cgp,Ap,hCgp,hAp,Hp⟩:=HP b d (rBound+3+d)
  exact ⟨actual_spine_G_incoming_cubic_from_normalized_along_original_q hdim heta hAi hApi hTemp hCgi.le
      hm hcu.le hC0 M W hxW Hi,
    actual_spine_G_star_incoming_cubic_from_normalized_along_original_q hdim heta hAs hAps hTemp hCgs.le
      hm hcu.le hC0 M W hxW Hs,
    actual_spine_G_power_cubic_from_normalized_along_original_q hdim heta hAp hTemp hCgp.le
      hm hcu.le hC0 M W hxW Hp⟩

theorem actual_current_G_projected_cubic_from_spine_along_original_q
    {m delta cl cu Az C0 Ct D Bclock eta Cmass : ℝ} {a b d rBound : ℕ}
    {M : (n:ℕ)→ActualThetaZeroOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (HI : ActualSpineGIncomingCubicOnEveryFinalNetAlong_original_q a b d rBound eta Cmass M W w)
    (HS : ActualSpineGStarIncomingCubicOnEveryFinalNetAlong_original_q a b d rBound eta Cmass M W w)
    (HP : ActualSpineGPowerCubicOnEveryFinalNetAlong_original_q b d rBound eta Cmass M W w) :
    ActualCurrentGProjectedCubicOnEveryFinalNetAlong_original_q a b d rBound eta Cmass M W w := by
  filter_upwards [HI,HS,HP] with n hnI hnS hnP
  intro L us hus hret hmesh hstar
  filter_upwards [hnI L us hus hret hmesh hstar,hnS L us hus hret hmesh hstar,
    hnP L us hus hret hmesh hstar] with r hrI hrS hrP
  dsimp only at hrI hrS hrP ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU hUlen ht ha hb hleaf V hWV hV1 hVU hlow hz
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  have hi : pre.length < pre.length+mid.length:=by omega
  obtain ⟨A,base,seed₀,k₀,hBase,hBaseTeeth,⟨spine⟩⟩:=hP.projectionDecomposition
  have hd : spine.toothCount=d:=by
    have H:=spine.teeth_length
    simp only [hBaseTeeth,List.length_nil,Nat.zero_add,ht] at H
    exact H.symm
  have haBase : base.live.test.exterior.length=a:=spine.exterior_length.symm.trans ha
  have hbBase : base.live.test.edges.length=b:=by
    have H:=spine.edges_length
    rw [hb,hd] at H
    omega
  have hleafBase : A.leaves≤rBound:=by have H:=spine.leaves_eq;omega
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).sweepBf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).sweepHf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  change |nativeActualDecoupledGProjectedResampling_original_q T P.live.test (pre.length+mid.length) U (M n) q|≤_
  rw [native_actual_decoupled_G_projected_resampling_eq_spine_row_original_q spine (M n) ho U hU hUlen
      V (by simpa only [hcut] using hVU),native_projection_spine_source_scale spine hi,hd]
  have hInDegree:=base.live.ancestry.incoming_degree
  cases hIn : base.live.test.incoming with
  | nil=>
    exact hrP pre mid tail hcut hindex hmass A U k₀ seed₀ base hBase hmid hU hBaseTeeth
      hbBase hIn hleafBase T P.live.test spine hd V hWV hV1 hlow hz
  | cons e es=>
    cases es with
    | nil=>
      rcases base.live.ancestry.incoming_cuts e (by simp [hIn]) with he|he
      · exact hrI pre mid tail hcut hindex hmass A U k₀ seed₀ base hBase hmid hU hBaseTeeth
          haBase hbBase e hIn he hleafBase T P.live.test spine hd V hWV hV1 hlow hz
      · exact hrS pre mid tail hcut hindex hmass A U k₀ seed₀ base hBase hmid hU hBaseTeeth
          haBase hbBase e hIn he hleafBase T P.live.test spine hd V hWV hV1 hlow hz
    | cons e' es=>simp [hIn] at hInDegree

theorem eventually_inherited_same_star_current_G_cubic_rows_along_original_q (hdim : Tendsto dim atTop atTop)
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Ccal : ℝ}
    (Cmass : ℝ) (hCm : 1 ≤ Cmass) (heta : 0 < eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn : ℕ in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (hcutoff : ∀ᶠn : ℕ in atTop,(M n).data.s ≤ 1/4 ∧ (M n).data.s ≤ (M n).xs)
    (saving : ℝ) (hsaving : 0 ≤ saving) (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong_original_q j k saving M W w) :
      ∀a b d rBound : ℕ,
        ActualCurrentGProjectedCubicOnEveryFinalNetAlong_original_q a b d rBound eta Cmass M W w := by
  have H:=eventually_inherited_same_star_spine_G_cubic_rows_along_original_q hdim Cmass hCm heta hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hTemp hCf hCcal M W hcanonical hWlim hcompare hsource hcutoff saving hsaving w Hmixed
  intro a b d rBound
  exact actual_current_G_projected_cubic_from_spine_along_original_q (H a b d rBound).1
    (H a b d rBound).2.1 (H a b d rBound).2.2

end OAI.SKFluctuations.LaplaceWindowFormalization
