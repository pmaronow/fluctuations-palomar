module

public import ComparisonSignedCavityActualSpineGPowerNormalized
public import ComparisonSignedCavityGTripleRowAlgebra
public import ComparisonSignedCavityScalarRadiusSavedRow

@[expose] public section

noncomputable section
set_option maxHeartbeats 30000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

def ActualSpineGPowerCubicOnEveryFinalNet
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (b d rBound : ℕ) (eta Cmass : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val  ≤  1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹  ≤  (M n).xs → (w n).star∈us →
  ∀ᶠr : ℕ in atTop,
    let as:=finiteCutMasses us r
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
      (fun _=>((M n).bf (partitionPoint 0 as j):ℝ)) (fun _=>((M n).hf (partitionPoint 0 as j):ℝ))
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as (pre.length+mid.length)  ≤  Cmass*W n →
    ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (U depth : ℕ) (seed : List NativeResourceMark)
      (P : NativeResourceTerm pre.length (pre.length+mid.length) T),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed depth T P →
      0 < mid.length → pre.length+mid.length < U → P.live.test.teeth=[] →
      P.live.test.edges.length=b → P.live.test.incoming=[] →
    T.leaves ≤ rBound →
    ∀(Tcur : ClockTree (Spin n×Bool) (pre++(mid++tail))) (Q : NativeGeneratedTest Tcur)
      (spine : NativeProjectionSpine P.live.test (pre.length+mid.length) Q),spine.toothCount=d →
    ∀V : ℝ,W n  ≤  V → V  ≤  1 →
      (M n).R (partitionPoint 0 as (pre.length+mid.length))  ≤  V/2 → (M n).z  ≤  V/2 →
    |nativeActualTripleSpineGRow spine (M n) U V q|  ≤
      2*(n:ℝ)^(-eta)*(W n*(M n).xs^2)*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d)

theorem actual_spine_G_power_cubic_from_normalized
    {m delta cl cu Az C0 Ct D Bclock eta Cmass Ap Temp Cg : ℝ} {b d rBound : ℕ}
    (heta : 0 < eta) (hAp : 0 ≤ Ap) (hTemp : 0 ≤ Temp) (hCg : 0 ≤ Cg)
    (hm : 0 < m) (hcu : 0 ≤ cu) (hC0 : 0 < C0)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxsW : ∀n,(M n).xs ≤ W n) {w : ℕ→ActualSlowWindowChoice}
    (H : ActualNormalizedSpineGPowerOnEveryFinalNet b d (rBound+3+d) eta Cmass Temp Cg Ap M W w) :
    ActualSpineGPowerCubicOnEveryFinalNet b d rBound eta Cmass M W w := by
  let Ai : ℝ:=0
  have hAi : 0 ≤ Ai:=le_refl 0
  let Cv:=4*((rBound:ℝ)+1)*(rBound+2)
  have HrowI:=eventually_actual_minimum_scalar_radius_saved_row_decay heta (Cv*(Temp*Cg*Ai))
    (by dsimp only [Cv];positivity) (delta:=delta) (cl:=cl) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hcu hC0
  have HrowP:=eventually_actual_minimum_scalar_radius_saved_row_decay heta (Cv*(Temp*Cg*Ap))
    (by dsimp only [Cv];positivity) (delta:=delta) (cl:=cl) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hcu hC0
  filter_upwards [H,HrowI,HrowP] with n hn hnI hnP
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar,hnI (M n) us hus,hnP (M n) us hus] with r hr hrI hrP
  dsimp only at hr hrI hrP ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht hdeg hIn hleaves
    Tcur Q spine hcount V hWV hV1 hlow hz
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let s:=(M n).xs+partitionPoint 0 (finiteCutMasses us r) pre.length
  let p0:=sourceMonomialScale s (W n) (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d
  let R:=fun j=>(M n).R (partitionPoint 0 (pre++(mid++tail)) j)
  have hR (j) : 0 ≤ R j:=
    (comparisonSweepQuantile_bounds (M n).context.hc (M n).context.hk (M n).context.hkc
      (M n).context.hm (M n).context.hM (M n).alpha _).1
  have hxs0 : 0 ≤ (M n).xs:=(M n).hxs.le
  have hW : 0 < W n:=(M n).hxs.trans_le (hxsW n)
  have hs : 0 < s:=add_pos_of_pos_of_nonneg (M n).hxs
    (partitionPoint_mem _ (finiteCutMasses_ordered us hus r) _).1
  have hp0 : 0 ≤ p0:=by dsimp only [p0];unfold sourceMonomialScale;positivity
  have Hmain:=native_actual_triple_spine_G_row_abs_le spine (M n) U V q ho hleaves
    (((n:ℝ)^(-eta))^2) (Temp*Cg*Ai) (Temp*Cg*Ap) p0
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
      have hVR' : V ≤ (M n).R (partitionPoint 0 (finiteCutMasses us r)
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

end OAI.SKFluctuations.LaplaceWindowFormalization
