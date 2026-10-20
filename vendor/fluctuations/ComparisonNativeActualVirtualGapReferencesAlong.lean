module

public import ComparisonNativeActualVirtualContactsAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 8000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_virtual_gap_references_subsequence_along
    (hC0 : 0 < C0) (hroom : 0 < 3*m+delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (p : (n:ℕ)→(M n).Potential)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (V : ℝ→ℝ) (hV : Monotone V)
    (hCDF : ∀s,Tendsto (fun n=>(M n).alpha.val.val ((M n).xs*s)/(M n).xs) atTop (𝓝 (V s)))
    {a b B : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbB : b < B)
    (hasupport : a∈comparisonIncrementSupport V) (hbsupport : b∈comparisonIncrementSupport V)
    (hgap : ∀r∈Ioo a b,r∉comparisonIncrementSupport V)
    (hmass : 0 < V ((a+b)/2)) :
    let c := V ((a+b)/2)/2
    ∃φ : ℕ→ℕ,StrictMono φ ∧ ∃left right : ℕ→ℝ,
      Tendsto left atTop (𝓝 a) ∧ Tendsto right atTop (𝓝 b) ∧
      ∀n,a-1 ≤ left n ∧ left n ≤ right n ∧ right n∈Icc a B ∧
        0 < left n ∧ (M (φ n)).xs*right n ≤ 1 ∧
        (p (φ n)).H ((M (φ n)).xs*left n)=0 ∧
        (p (φ n)).H ((M (φ n)).xs*right n)=0 ∧
        c*(M (φ n)).xs ≤ (M (φ n)).alpha.val.val ((M (φ n)).xs*left n) ∧
        c*(M (φ n)).xs ≤ (M (φ n)).alpha.val.val ((M (φ n)).xs*right n) := by
  classical
  dsimp only
  obtain ⟨_hc,Hcontacts⟩ := actual_virtual_gap_endpoint_contacts_eventually_along
    hC0 hroom dim hdim M p hxs V hV hCDF ha hab hasupport hbsupport hgap hmass
  let eps := fun k:ℕ=>min ((b-a)/4) (min ((B-b)/2) (1/(k+1:ℝ)))
  have heps k : 0 < eps k := by dsimp only [eps];positivity
  obtain ⟨φ,hφ,Hφ⟩ := extraction_forall_of_eventually (fun k=>Hcontacts (eps k) (heps k))
  choose l hlmem hlclose hlzero hlmass using (fun n=>(Hφ n).1)
  choose r hrmem hrclose hrzero hrmass using (fun n=>(Hφ n).2)
  let left := fun n=>l n/(M (φ n)).xs
  let right := fun n=>r n/(M (φ n)).xs
  have hleftclose n : |left n-a| < eps n := hlclose n
  have hrightclose n : |right n-b| < eps n := hrclose n
  have hepsrate n : eps n ≤ 1/(n+1:ℝ) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hleftlim : Tendsto left atTop (𝓝 a) := by
    have H : Tendsto (fun n=>left n-a) atTop (𝓝 0) := squeeze_zero_norm
      (fun n=>by
        simpa only [Real.norm_eq_abs] using (hleftclose n).le.trans (hepsrate n))
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [sub_add_cancel,zero_add] using H.add_const a
  have hrightlim : Tendsto right atTop (𝓝 b) := by
    have H : Tendsto (fun n=>right n-b) atTop (𝓝 0) := squeeze_zero_norm
      (fun n=>by
        simpa only [Real.norm_eq_abs] using (hrightclose n).le.trans (hepsrate n))
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [sub_add_cancel,zero_add] using H.add_const b
  refine ⟨φ,hφ,left,right,hleftlim,hrightlim,?_⟩
  intro n
  have hgapbound : eps n ≤ (b-a)/4 := min_le_left _ _
  have houterbound : eps n ≤ (B-b)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hepsone : eps n ≤ 1 := (hepsrate n).trans (by
    apply (div_le_one (by positivity : 0 < (n+1:ℝ))).mpr
    linarith [Nat.cast_nonneg (α:=ℝ) n])
  have hlc := abs_lt.mp (hleftclose n)
  have hrc := abs_lt.mp (hrightclose n)
  have hlcancel : (M (φ n)).xs*left n=l n := by dsimp only [left];field_simp [(M (φ n)).hxs.ne']
  have hrcancel : (M (φ n)).xs*right n=r n := by dsimp only [right];field_simp [(M (φ n)).hxs.ne']
  refine ⟨by linarith,by linarith,⟨by linarith,by linarith⟩,
    div_pos (hlmem n).1 (M (φ n)).hxs,?_,?_,?_,?_,?_⟩
  · rw [hrcancel];exact (hrmem n).2
  · rw [hlcancel];exact hlzero n
  · rw [hrcancel];exact hrzero n
  · rw [hlcancel];exact hlmass n
  · rw [hrcancel];exact hrmass n

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
