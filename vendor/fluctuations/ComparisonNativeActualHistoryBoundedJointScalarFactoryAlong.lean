module

public import ComparisonNativeActualHistoryBoundedJointScalarLimitAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

theorem exists_actual_selected_bad_history_bounded_joint_scalar_limit_along
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (K : ℝ) (hK : 0 ≤ K)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hshell : 0 < shell) (hTemp : 0 < T-epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hwork : ∀ᶠn in atTop,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2 ≤ K)
 :
    ∃phi : ℕ→ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
        Nonempty (ActualInheritedLocalScalarLimitData
          (hTemp.trans_le (sub_le_self T hepsilon)) (T-epsilon)
          (fun n=>M (phi n)) htotal) := by
  let hT : 0<T := hTemp.trans_le (sub_le_self T hepsilon)
  obtain ⟨n0,Cf,_hCf,Hhistory0,hdim0,Hclocks,_⟩ :=
    actual_selected_bad_history_all_index_clock_tail hm hdelta hcl hAz hC0 hc0
      hmargin hcapmargin dim hdim root M epsilon shell hepsilon hT.le hb hh Hhistory
  let shift := fun n : ℕ=>n+n0
  have hshift : Tendsto shift atTop atTop := tendsto_add_atTop_nat n0
  have ht0 : ∀n,∀u∈Icc (0:ℝ) 1,(M (shift n)).h u+(M (shift n)).b u ≤ T :=
    fun n=>(Hclocks n).2.2.1
  obtain ⟨psi,hpsi,Hlimit⟩ :=
    exists_actual_selected_bad_history_bounded_joint_scalar_limit_of_total_along K hK
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      (fun n=>dim (shift n)) hdim0 (fun n=>root (shift n)) (fun n=>M (shift n))
      epsilon shell hepsilon hshell hTemp
      (Eventually.of_forall fun n=>(Hclocks n).1)
      (Eventually.of_forall fun n=>(Hclocks n).2.1)
      Hhistory0 (fun n=>W (shift n)) (fun n=>hcanonical (shift n)) (hWlim.comp hshift)
      (fun n=>hcompare (shift n)) (hshift.eventually hwork) ht0
  exact ⟨fun n=>psi n+n0,fun i j hij=>Nat.add_lt_add_right (hpsi hij) n0,
    fun n=>ht0 (psi n),Hlimit⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
