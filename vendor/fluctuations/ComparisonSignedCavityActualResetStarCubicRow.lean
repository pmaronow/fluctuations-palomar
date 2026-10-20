module

public import ComparisonSignedCavityActualResetIncomingCubicRow

@[expose] public section

noncomputable section
set_option maxHeartbeats 28000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

def ActualResetStarIncomingCubicRowOnEveryFinalNet
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d : ℕ) (eta Cmass : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
  ∀ᶠr : ℕ in atTop,
    let as:=finiteCutMasses us r
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
      (fun _=>((M n).bf (partitionPoint 0 as j):ℝ)) (fun _=>((M n).hf (partitionPoint 0 as j):ℝ))
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
    ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (U depth : ℕ) (seed : List NativeResourceMark)
      (P : NativeResourceTerm pre.length (pre.length+mid.length) T),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed depth T P →
      0 < mid.length → pre.length+mid.length < U → P.live.test.teeth=[] →
      P.live.test.exterior.length=a → P.live.test.edges.length=b →
    ∀e₀ : T.Slot,P.live.test.incoming=[e₀] → T.splitIndex P.live.test.target e₀=pre.length+mid.length →
    ∀V : ℝ,W n ≤ V → V ≤ 1 →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ V/2 → (M n).z ≤ V/2 →
    |nativeResetProjectedGammaRow n T P.live.test (M n) U V q
      (retainedStarMixedClock n (M n).bf (M n).hf as) d
      (orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val)| ≤
      2*(n:ℝ)^(-eta)*(W n*(M n).xs^2)*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d)

theorem actual_reset_star_incoming_cubic_row_from_normalized
    {m delta cl cu Az C0 Ct D Bclock eta Cmass Ai Ap Temp : ℝ} {a b d : ℕ}
    (heta : 0 < eta) (hAi : 0 ≤ Ai) (hAp : 0 ≤ Ap)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxsW : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hb : ∀n u,(M n).b u=Temp) (hh : ∀n u,(M n).h u=0)
    {w : ℕ→ActualSlowWindowChoice}
    (H : ActualNormalizedResetStarIncomingOnEveryFinalNet a b d eta Cmass Ai Ap M W w) :
    ActualResetStarIncomingCubicRowOnEveryFinalNet a b d eta Cmass M W w := by
  have HrowI:=eventually_actual_minimum_bare_saved_polarized_row_decay heta Ai hAi
    (D:=D) Bclock Temp hTemp hm hdelta hroom hcl hcu hAz hC0 hCt
  have HrowP:=eventually_actual_minimum_bare_saved_polarized_row_decay heta Ap hAp
    (D:=D) Bclock Temp hTemp hm hdelta hroom hcl hcu hAz hC0 hCt
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,HrowI,HrowP,HW] with n hn hnI hnP hnW
  have hxs1: (M n).xs ≤ 1:=(hxsW n).trans hnW
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar,
    hnI (M n) (hb n) (hh n) hxs1 L us hus hret hmesh,
    hnP (M n) (hb n) (hh n) hxs1 L us hus hret hmesh] with r hr hrI hrP
  dsimp only at hr hrI hrP ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hdeg e₀ hIn hi V hWV hV1 hlow hz
  have ho:MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let K:=retainedStarMixedClock n (M n).bf (M n).hf (finiteCutMasses us r)
  let center:=orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val
  let s:=(M n).xs+partitionPoint 0 (finiteCutMasses us r) pre.length
  let p0:=sourceMonomialScale s (W n) (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d
  let R:=fun j=>(M n).R (partitionPoint 0 (pre++(mid++tail)) j)
  have hR (j) : 0 ≤ R j:=
    (comparisonSweepQuantile_bounds (M n).context.hc (M n).context.hk (M n).context.hkc
      (M n).context.hm (M n).context.hM (M n).alpha _).1
  have hxs0:0 ≤ (M n).xs:=(M n).hxs.le
  have hW:0<W n:=(M n).hxs.trans_le (hxsW n)
  have hs:0<s:=add_pos_of_pos_of_nonneg (M n).hxs
    (partitionPoint_mem _ (finiteCutMasses_ordered us hus r) _).1
  have hp0:0 ≤ p0:=by dsimp only [p0];unfold sourceMonomialScale;positivity
  have Hmain:=native_reset_projected_gamma_row_abs_le n T P.live.test (M n) U V q K d center ho
    (((n:ℝ)^(-eta))^2) Ai Ap p0
    (fun j=>nativeSavedIncomingScale (M n).xs (W n) (W n) (R j))
    (fun j=>nativeSavedIncomingScale (M n).xs (W n) (W n) (R j))
    (sq_nonneg _) hAi hAp hp0
    (by intro j;have:=hR j;unfold nativeSavedIncomingScale savedProjectedScale savedWeightedExteriorScale;positivity)
    (by intro j;have:=hR j;unfold nativeSavedIncomingScale savedProjectedScale savedWeightedExteriorScale;positivity)
    (by
      intro p hp hhigh hVR
      have hhigh':U ≤ p.tree.splitIndex p.mark (p.embed P.live.test.target):=by
        rwa [p.tree.splitIndex_symm]
      have hVR':V ≤ (M n).R (partitionPoint 0 (finiteCutMasses us r)
          (p.tree.splitIndex (p.embed P.live.test.target) p.mark)):=by simpa only [hcut] using hVR
      have Hpt:=hr pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hdeg e₀ hIn hi
        0 p hp hhigh' _ (hWV.trans hVR') rfl (by linarith) (by linarith)
      simpa only [q,K,center,p0,s,R,hcut] using Hpt)
  rw [←hcut] at hrI hrP
  have HI:=hrI pre.length (pre.length+mid.length) U T seed depth P hP (by omega) (by omega)
    (W n) V (hxsW n) ((hxsW n).trans hWV) hV1 (by linarith) (by simpa only [hcut] using hlow)
    (W n) (Or.inr rfl)
  have HP:=hrP pre.length (pre.length+mid.length) U T seed depth P hP (by omega) (by omega)
    (W n) V (hxsW n) ((hxsW n).trans hWV) hV1 (by linarith) (by simpa only [hcut] using hlow)
    (W n) (Or.inr rfl)
  have Hsum:=mul_le_mul_of_nonneg_right (add_le_add HI HP) hp0
  apply Hmain.trans
  convert Hsum using 1 <;> dsimp only [K,R,p0,s] <;> (try simp only [hcut]) <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization
