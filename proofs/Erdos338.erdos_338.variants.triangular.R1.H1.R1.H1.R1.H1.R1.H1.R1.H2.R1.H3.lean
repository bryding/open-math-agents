import OMAReductions.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1

/-! Dirichlet hyperbola method: for s ≡ 3 (mod 8) the Jacobi character a ↦ (a|s) is odd, so its partial
sums are bounded by s, and the average of the divisor sums differs from the √n-truncated L-series by
O(s/√n). -/

open Finset Filter Topology

namespace H3Work

noncomputable def χ (s a : ℕ) : ℝ := (jacobiSym (a : ℤ) s : ℝ)

variable {s : ℕ}

theorem jac_abs_le (a : ℤ) (s : ℕ) : |(jacobiSym a s : ℝ)| ≤ 1 := by
  rcases jacobiSym.trichotomy a s with h | h | h <;> simp [h]

theorem chi_abs_le (a : ℕ) : |χ s a| ≤ 1 := jac_abs_le _ _

theorem jac_neg_one (hs : s % 8 = 3) : jacobiSym (-1) s = -1 := by
  have hodd : Odd s := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.at_neg_one hodd]
  exact ZMod.χ₄_nat_three_mod_four (by omega)

theorem chi_zero (hs : s % 8 = 3) : χ s 0 = 0 := by
  simp [χ, jacobiSym.zero_left (show 1 < s by omega)]

theorem chi_period (a : ℕ) : χ s (a + s) = χ s a := by
  unfold χ
  rw [jacobiSym.mod_left, jacobiSym.mod_left (a : ℤ)]
  push_cast
  rw [Int.add_emod_right]

theorem chi_self (hs : s % 8 = 3) : χ s s = 0 := by
  have h := chi_period (s := s) 0
  rw [zero_add] at h
  rw [h, chi_zero hs]

theorem chi_reflect (hs : s % 8 = 3) (j : ℕ) (hj : j ≤ s) : χ s (s - j) = - χ s j := by
  unfold χ
  have : jacobiSym ((s - j : ℕ) : ℤ) s = jacobiSym (-1 * (j : ℤ)) s := by
    rw [jacobiSym.mod_left, jacobiSym.mod_left (-1 * (j : ℤ))]
    rw [Nat.cast_sub hj, neg_one_mul, sub_eq_neg_add, Int.add_emod_right]
  rw [this, jacobiSym.mul_left, jac_neg_one hs]
  push_cast; ring

theorem period_sum (hs : s % 8 = 3) : ∑ a ∈ range s, χ s a = 0 := by
  have h1 : ∑ j ∈ range s, χ s (j + 1) = ∑ a ∈ range s, χ s a := by
    have e1 := Finset.sum_range_succ' (fun a => χ s a) s
    have e2 := Finset.sum_range_succ (fun a => χ s a) s
    rw [chi_zero hs] at e1
    rw [chi_self hs] at e2
    linarith
  have h2 : ∑ j ∈ range s, χ s (j + 1) = - ∑ a ∈ range s, χ s a := by
    rw [← Finset.sum_range_reflect, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have e : s - 1 - j + 1 = s - j := by omega
    rw [e, chi_reflect hs j (by omega)]
  linarith

theorem window (hs : s % 8 = 3) (m : ℕ) : ∑ j ∈ range s, χ s (m + j) = 0 := by
  induction m with
  | zero => simpa using period_sum hs
  | succ m ih =>
    have e1 := Finset.sum_range_succ' (fun j => χ s (m + j)) s
    have e2 := Finset.sum_range_succ (fun j => χ s (m + j)) s
    have hp : χ s (m + s) = χ s m := chi_period m
    have e3 : ∑ j ∈ range s, χ s (m + (j + 1)) = ∑ j ∈ range s, χ s (m + 1 + j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show m + (j + 1) = m + 1 + j by omega]
    simp only [add_zero] at e1
    linarith

theorem partial_bound (hs : s % 8 = 3) (n : ℕ) : |∑ a ∈ range n, χ s a| ≤ s := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < s
    · calc |∑ a ∈ range n, χ s a| ≤ ∑ a ∈ range n, |χ s a| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ a ∈ range n, (1 : ℝ) := Finset.sum_le_sum (fun a _ => chi_abs_le a)
        _ = n := by simp
        _ ≤ s := by exact_mod_cast h.le
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + s := ⟨n - s, by omega⟩
      rw [Finset.sum_range_add, window hs m, add_zero]
      exact ih m (by omega)

theorem Ioc_bound (hs : s % 8 = 3) (u v : ℕ) : |∑ a ∈ Ioc u v, χ s a| ≤ 2 * s := by
  rcases le_or_gt u v with h | h
  · rw [show Ioc u v = Ico (u + 1) (v + 1) by ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega,
      Finset.sum_Ico_eq_sub _ (by omega)]
    calc _ ≤ |∑ a ∈ range (v + 1), χ s a| + |∑ a ∈ range (u + 1), χ s a| := abs_sub _ _
      _ ≤ s + s := add_le_add (partial_bound hs _) (partial_bound hs _)
      _ = 2 * s := by ring
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp

theorem divisor_swap (f : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Icc 1 n, ∑ a ∈ k.divisors, f a = ∑ a ∈ Icc 1 n, f a * ((n / a : ℕ) : ℝ) := by
  have h1 : ∀ k ∈ Icc 1 n, ∑ a ∈ k.divisors, f a = ∑ a ∈ Icc 1 n, if a ∣ k then f a else 0 := by
    intro k hk
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext a
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    constructor
    · rintro ⟨had, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos had (by omega), (Nat.le_of_dvd (by omega) had).trans hk.2⟩, had⟩
    · rintro ⟨_, had⟩
      exact ⟨had, by omega⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hc : ((Icc 1 n).filter (fun k => a ∣ k)).card = n / a := by
    rw [show Icc 1 n = Ioc 0 n by ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega]
    exact Nat.Ioc_filter_dvd_card_eq_div n a
  rw [hc]

theorem partA (n m : ℕ) :
    |∑ a ∈ Icc 1 m, χ s a * ((n / a : ℕ) : ℝ) - n * ∑ a ∈ Icc 1 m, χ s a / a| ≤ m := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ a ∈ Icc 1 m, |χ s a * ((n / a : ℕ) : ℝ) - n * (χ s a / a)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Icc 1 m, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
        have hpos : (0 : ℝ) < a := by exact_mod_cast ha1
        have e : χ s a * ((n / a : ℕ) : ℝ) - n * (χ s a / a) =
            χ s a * (((n / a : ℕ) : ℝ) - n / a) := by ring
        rw [e, abs_mul]
        have h2 : |((n / a : ℕ) : ℝ) - n / a| ≤ 1 := by
          rw [abs_le]
          have hle : ((n / a : ℕ) : ℝ) ≤ n / a := Nat.cast_div_le
          have hq : (a : ℝ) * ((n / a : ℕ) : ℝ) + ((n % a : ℕ) : ℝ) = n := by
            exact_mod_cast Nat.div_add_mod n a
          have hr : ((n % a : ℕ) : ℝ) < a := by exact_mod_cast Nat.mod_lt n (by omega)
          have hgt : (n : ℝ) / a < ((n / a : ℕ) : ℝ) + 1 := by
            rw [div_lt_iff₀ hpos]
            nlinarith
          constructor <;> linarith
        calc _ ≤ 1 * 1 := mul_le_mul (chi_abs_le a) h2 (abs_nonneg _) zero_le_one
          _ = 1 := by ring
    _ = m := by simp

theorem partB (hs : s % 8 = 3) (n m : ℕ) (hm : n < (m + 1) * (m + 1)) :
    |∑ a ∈ Ioc m n, χ s a * ((n / a : ℕ) : ℝ)| ≤ 2 * s * m := by
  have key : ∑ a ∈ Ioc m n, χ s a * ((n / a : ℕ) : ℝ) =
      ∑ b ∈ Icc 1 m, ∑ a ∈ Ioc m (n / b), χ s a := by
    have h1 : ∀ a ∈ Ioc m n, χ s a * ((n / a : ℕ) : ℝ) =
        ∑ b ∈ Icc 1 m, if a * b ≤ n then χ s a else 0 := by
      intro a ha
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      have ha' := Finset.mem_Ioc.mp ha
      have hdiv : n / a < m + 1 :=
        lt_of_le_of_lt (Nat.div_le_div_left (by omega) (by omega))
          ((Nat.div_lt_iff_lt_mul (by omega)).mpr hm)
      have hf : (Icc 1 m).filter (fun b => a * b ≤ n) = Icc 1 (n / a) := by
        ext b
        have hab : a * b ≤ n ↔ b ≤ n / a := by
          rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]
        simp only [Finset.mem_filter, Finset.mem_Icc]
        rw [hab]
        generalize n / a = q at *
        omega
      rw [hf]
      simp
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    ext a
    have hab : a * b ≤ n ↔ a ≤ n / b := (Nat.le_div_iff_mul_le (by omega)).symm
    have hnb : n / b ≤ n := Nat.div_le_self n b
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    rw [hab]
    generalize n / b = q at *
    omega
  rw [key]
  calc _ ≤ ∑ b ∈ Icc 1 m, |∑ a ∈ Ioc m (n / b), χ s a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ Icc 1 m, (2 * s : ℝ) := Finset.sum_le_sum (fun b _ => Ioc_bound hs _ _)
    _ = 2 * s * m := by simp; ring

theorem tendsto_sqrt : Tendsto Nat.sqrt atTop atTop :=
  tendsto_atTop_atTop.mpr fun b => ⟨b * b, fun _ hn => Nat.le_sqrt.mpr hn⟩

theorem main_bound (hs : s % 8 = 3) (n m : ℕ) (hn : 1 ≤ n) (hm1 : 1 ≤ m) (hmm : m * m ≤ n)
    (hlt : n < (m + 1) * (m + 1)) (hmn : m ≤ n) :
    |(∑ k ∈ Icc 1 n, ∑ a ∈ k.divisors, χ s a) / n - ∑ a ∈ Icc 1 m, χ s a / a| ≤
      (2 * s + 1 : ℝ) / m := by
  have hD := divisor_swap (χ s) n
  have hsplit : ∑ a ∈ Icc 1 n, χ s a * ((n / a : ℕ) : ℝ) =
      ∑ a ∈ Icc 1 m, χ s a * ((n / a : ℕ) : ℝ) + ∑ a ∈ Ioc m n, χ s a * ((n / a : ℕ) : ℝ) := by
    rw [← Finset.sum_union]
    · congr 1
      ext x
      simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]
      omega
    · exact Finset.disjoint_left.mpr fun a h1 h2 => by
        simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2; omega
  have hA := partA (s := s) n m
  have hB := partB hs n m hlt
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmmR : (m : ℝ) * m ≤ n := by exact_mod_cast hmm
  have heq : (∑ k ∈ Icc 1 n, ∑ a ∈ k.divisors, χ s a) / n - ∑ a ∈ Icc 1 m, χ s a / a =
      ((∑ a ∈ Icc 1 m, χ s a * ((n / a : ℕ) : ℝ) - n * ∑ a ∈ Icc 1 m, χ s a / a) +
        ∑ a ∈ Ioc m n, χ s a * ((n / a : ℕ) : ℝ)) / n := by
    rw [hD, hsplit]
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hnpos, div_le_div_iff₀ hnpos hmpos]
  calc _ ≤ ((m : ℝ) + 2 * s * m) * m :=
        mul_le_mul_of_nonneg_right ((abs_add_le _ _).trans (add_le_add hA hB)) hmpos.le
    _ = (2 * s + 1) * (m * m) := by ring
    _ ≤ (2 * s + 1) * n := mul_le_mul_of_nonneg_left hmmR (by positivity)

theorem H3_proof : ∀ s:ℕ, 0<s → s%8=3 → ∀ L:ℝ,
  Tendsto (fun n:ℕ => ∑ a∈Icc 1 n,(jacobiSym a s:ℝ)/(a:ℝ)) atTop (𝓝 L) →
  Tendsto (fun n:ℕ => (∑ k∈Icc 1 n,∑ a∈k.divisors,(jacobiSym a s:ℝ))/(n:ℝ)) atTop (𝓝 L) := by
  intro s _ hs L hL
  have hg : Tendsto (fun n : ℕ => ∑ a ∈ Icc 1 (Nat.sqrt n), χ s a / a) atTop (𝓝 L) :=
    hL.comp tendsto_sqrt
  have hC : Tendsto (fun n : ℕ => (2 * s + 1 : ℝ) / (Nat.sqrt n : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (2 * s + 1 : ℝ)).comp tendsto_sqrt
  let E : ℕ → ℝ := fun n => (∑ k ∈ Icc 1 n, ∑ a ∈ k.divisors, χ s a) / n -
    ∑ a ∈ Icc 1 (Nat.sqrt n), χ s a / a
  have hEb : ∀ n, 1 ≤ n → ‖E n‖ ≤ (2 * s + 1 : ℝ) / (Nat.sqrt n : ℝ) := by
    intro n hn
    rw [Real.norm_eq_abs]
    exact main_bound hs n (Nat.sqrt n) hn (Nat.le_sqrt.mpr (by omega)) (Nat.sqrt_le n)
      (Nat.lt_succ_sqrt n) (Nat.sqrt_le_self n)
  have hE0 : Tendsto E atTop (𝓝 0) := squeeze_zero_norm' (eventually_atTop.mpr ⟨1, hEb⟩) hC
  have h := hg.add hE0
  rw [add_zero] at h
  refine h.congr' (eventually_atTop.mpr ⟨1, fun n _ => ?_⟩)
  simp only [E, χ]
  ring

end H3Work

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1.H3 :=
  H3Work.H3_proof
