module

public import ComparisonSignedCavityScalarNativeRemainder
public import ComparisonSignedCavityScalarClockCutDifference

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity GaussianCalculus Scalar
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false

theorem original_scalar_disorder_tendsto_of_uniform_clock_bound
    {as : List PositiveMass} (tree : ClockTree Bool as) (ho : MassOrdered 0 as)
    (q : ℕ→ℝ) (qk : ℕ→ℕ→ℝ) (hq : Monotone q) (hqk : ∀k,Monotone (qk k))
    (hz : q 0=0) (hzk : ∀k,qk k 0=0)
    (P : tree.Assignment→ℝ) (hP : ∀sigma,|P sigma|≤1)
    (eps : ℕ→ℝ) (heps : ∀k,0≤eps k) (heps0 : Tendsto eps atTop (𝓝 0))
    (hdir : ∀k j,|qk k j-q j|≤eps k) :
    Tendsto (fun k=>tree.disorderExpect (fun _=>(1/2:ℝ)) scalarFeature 0
      (fun j _=>qk k j) P 0) atTop
      (𝓝 (tree.disorderExpect (fun _=>(1/2:ℝ)) scalarFeature 0 (fun j _=>q j) P 0)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  apply squeeze_zero (fun _=>abs_nonneg _) _
    (by simpa only [mul_zero] using (heps0.const_mul
      (ClockTree.errorJetVariation tree.leaves 0 0*((tree.leaves:ℝ)+1))))
  intro k
  exact native_scalar_disorder_clock_difference tree ho tree.leaves le_rfl q (qk k)
    hq (hqk k) hz (hzk k) P hP (eps k) (heps k) (hdir k)

theorem original_scalar_list_sum_tendsto {beta : Type*} (ps : List beta)
    (f : ℕ→beta→ℝ) (g : beta→ℝ)
    (h : ∀p∈ps,Tendsto (fun k=>f k p) atTop (𝓝 (g p))) :
    Tendsto (fun k=>(ps.map (f k)).sum) atTop (𝓝 ((ps.map g).sum)) := by
  induction ps with
  | nil => simpa only [List.map_nil,List.sum_nil] using tendsto_const_nhds
  | cons p ps ih =>
    simpa only [List.map_cons,List.sum_cons] using
      (h p (by simp)).add (ih (by intro r hr;exact h r (by simp [hr])))

theorem native_gamma_row_scalar_low_remainder_of_nonstrict_buffer
    (n : ℕ) {W A R Ru : ℝ}
    (before after : List PositiveMass) (a : PositiveMass)
    (ho : MassOrdered 0 (before++a::after)) (q : ℕ→ℝ) (hq : Monotone q)
    (hq0 : q 0=0) (hW : 0≤W) (hA : 0≤A) (hR : 0≤R) (hRu : 0≤Ru)
    (j V : ℕ) (hj : j<before.length+1) (hUV : before.length+1≤V)
    (hV : V≤(before++a::after).length)
    (hbuffer : a.val<partitionPoint 0 (before++a::after) V)
    (hsize : partitionPoint 0 (before++a::after) V≤A*W)
    (hjclock : q j≤R*W) (hUclock : q (before.length+1)≤Ru*W) (hsmall : q j≤1)
    (tree : ClockTree (Spin n×Bool) (before++a::after))
    (start : ℝ) (hoa : MassOrdered start (before++a::after)) (s : tree.Slot) :
    let chi:=((tree.markedAttach start).map (fun p=>p.coeff*
      fullScalarCutGamma p.tree (before.length+1) q (p.embed s) p.mark)).sum
    |nativeOriginalScalarPairMean (before++a::after) q j-chi^2*q j|≤
      nativeScalarLowRemainderConstant A R Ru*W^3 := by
  let as:=before++a::after
  let U:=before.length+1
  let eps:=fun k:ℕ=>((k+1:ℕ):ℝ)⁻¹
  have heps k : 0<eps k:=by dsimp only [eps];positivity
  have heps0 : Tendsto eps atTop (𝓝 0):=uniformMasses_mesh_tendsto
  let qk:=fun k l=>q l+if U<l then eps k else 0
  have hqk k : Monotone (qk k):=by
    intro l r hlr
    dsimp only [qk]
    have H:=hq hlr
    split_ifs with hl hr <;> try omega
    all_goals linarith only [H,(heps k).le]
  have hzk k : qk k 0=0:=by simp only [qk,show ¬U<0 by omega,ite_false,add_zero,hq0]
  have hdir k l : |qk k l-q l|≤eps k:=by
    dsimp only [qk]
    split_ifs <;> simp only [add_sub_cancel_left,abs_of_pos (heps k),le_refl,add_zero,sub_self,abs_zero]
    exact (heps k).le
  have hqkj k : qk k j=q j:=by simp only [qk,show ¬U<j by dsimp only [U];omega,ite_false,add_zero]
  have hqkU k : qk k U=q U:=by simp only [qk,lt_irrefl,ite_false,add_zero]
  have hUVlt : U<V:=by
    by_contra H
    have HE : V=U:=by dsimp only [U] at *;omega
    subst V
    rw [partitionPoint_after_before_one] at hbuffer
    exact (lt_irrefl _ hbuffer)
  have hgap k : qk k U<qk k V:=by
    rw [hqkU]
    have H:=hq hUVlt.le
    simp only [qk,hUVlt,ite_true]
    linarith only [H,heps k]
  have hq0nonneg l : 0≤q l:=by rw [←hq0];exact hq (Nat.zero_le l)
  have htotal k : 0<qk k as.length:=by
    have H : 0≤qk k U:=by rw [hqkU];exact hq0nonneg U
    exact (H.trans_lt (hgap k)).trans_le (hqk k hV)
  let chik:=fun k=>((tree.markedAttach start).map (fun p=>p.coeff*
    fullScalarCutGamma p.tree U (qk k) (p.embed s) p.mark)).sum
  let chi:=((tree.markedAttach start).map (fun p=>p.coeff*
    fullScalarCutGamma p.tree U q (p.embed s) p.mark)).sum
  have hpair : Tendsto (fun k=>nativeOriginalScalarPairMean as (qk k) j) atTop
      (𝓝 (nativeOriginalScalarPairMean as q j)):=by
    apply original_scalar_disorder_tendsto_of_uniform_clock_bound
      (ClockTree.pairClock as j) ho q qk hq hqk hq0 hzk _ _ eps
      (fun k=>(heps k).le) heps0 hdir
    intro sigma
    simp only [scalarFeature_apply_spin,abs_mul,abs_spinValue,abs_one,one_mul,le_refl]
  have hchi : Tendsto chik atTop (𝓝 chi):=by
    apply original_scalar_list_sum_tendsto
    intro p hp
    apply Tendsto.const_mul
    apply original_scalar_disorder_tendsto_of_uniform_clock_bound p.tree.cavityRight ho
      (relocatedClock U 0 q) (fun k=>relocatedClock U 0 (qk k))
      (relocatedClock_monotone U (by norm_num) hq hq0nonneg)
      (fun k=>relocatedClock_monotone U (by norm_num) (hqk k) (fun l=>by
        rw [←hzk k];exact hqk k (Nat.zero_le l)))
      (by simp only [relocatedClock,show 0<U by dsimp only [U];omega,ite_true,zero_mul])
      (by intro k;simp only [relocatedClock,show 0<U by dsimp only [U];omega,ite_true,zero_mul])
      _ (fun sigma=>(native_scalar_slot_product_abs_one _ sigma _).le)
      eps (fun k=>(heps k).le) heps0
    intro k l
    dsimp only [relocatedClock]
    split_ifs
    · simp only [zero_mul,sub_self,abs_zero];exact (heps k).le
    · exact hdir k l
  have H k : |nativeOriginalScalarPairMean as (qk k) j-(chik k)^2*q j|≤
      nativeScalarLowRemainderConstant A R Ru*W^3:=by
    have HH:=native_gamma_row_scalar_low_remainder_of_buffer n (htotal k)
      before after a ho (qk k) (hqk k) (hzk k) rfl hW hA hR hRu j V hj hUV hV
      (hgap k) hsize (by rw [hqkj];exact hjclock) (by rw [hqkU];exact hUclock)
      (by rw [hqkj];exact hsmall) tree start hoa s
    simpa only [hqkj] using HH
  exact le_of_tendsto' ((hpair.sub ((hchi.pow 2).mul_const (q j))).abs) H

end OAI.SKFluctuations.LaplaceWindowFormalization
