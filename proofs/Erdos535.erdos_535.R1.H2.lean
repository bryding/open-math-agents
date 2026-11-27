import OMAReductions.R_Erdos535_erdos_535_R1

-- Step Erdos535.erdos_535.R1.H2: hypothesis H2 of reduction Erdos535.erdos_535.R1
-- Credit: @bryding

namespace OMA.Erdos535H2

open Erdos535 ArithmeticFunction
open scoped ArithmeticFunction.Omega

/-- The part of `a` made of the primes below `y`. -/
noncomputable def sm (y a : ℕ) : ℕ := (a.factorization.filter (· < y)).prod (· ^ ·)

lemma sm_factorization (y a : ℕ) :
    (sm y a).factorization = a.factorization.filter (· < y) := by
  unfold sm
  apply Nat.prod_pow_factorization_eq_self
  intro p hp
  rw [Finsupp.support_filter, Finset.mem_filter] at hp
  exact Nat.prime_of_mem_primeFactors hp.1

lemma sm_ne_zero (y a : ℕ) : sm y a ≠ 0 := by
  unfold sm Finsupp.prod
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  rw [Finsupp.support_filter, Finset.mem_filter] at hp
  exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp.1).ne_zero

lemma sm_dvd (y : ℕ) {a : ℕ} (ha : a ≠ 0) : sm y a ∣ a := by
  rw [← Nat.factorization_le_iff_dvd (sm_ne_zero y a) ha, sm_factorization]
  intro p
  rw [Finsupp.filter_apply]
  split_ifs <;> simp

lemma sm_eq_of_key {y a a' : ℕ}
    (h : ∀ i : Fin y, a.factorization i = a'.factorization i) : sm y a = sm y a' := by
  unfold sm
  congr 1
  ext p
  rw [Finsupp.filter_apply, Finsupp.filter_apply]
  split_ifs with hp
  · exact h ⟨p, hp⟩
  · rfl

lemma factorization_le {a L : ℕ} (ha : a ≠ 0) (hL : a < 2 ^ L) (p : ℕ) :
    a.factorization p ≤ L := by
  by_cases hp : p.Prime
  · have h1 : p ^ a.factorization p ≤ a := Nat.le_of_dvd (Nat.pos_of_ne_zero ha)
      (Nat.ordProj_dvd a p)
    have h2 : 2 ^ a.factorization p ≤ p ^ a.factorization p :=
      Nat.pow_le_pow_left hp.two_le _
    have h3 : 2 ^ a.factorization p < 2 ^ L := by omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h3
    omega
  · rw [Nat.factorization_eq_zero_of_not_prime a hp]
    omega

lemma omega_le {y a N K : ℕ} (hy : 2 ≤ y) (ha : a ≠ 0) (haN : a ≤ N)
    (hK : N < y ^ (K + 1)) : Ω (a / sm y a) ≤ K := by
  have hd := sm_dvd y ha
  have hb : a / sm y a ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha) hd)
      (Nat.pos_of_ne_zero (sm_ne_zero y a))).ne'
  have hfac : (a / sm y a).factorization = a.factorization - (sm y a).factorization :=
    Nat.factorization_div hd
  have hge : ∀ p ∈ (a / sm y a).primeFactorsList, y ≤ p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactorsList hp
    have hpos : 0 < (a / sm y a).factorization p :=
      hpp.factorization_pos_of_dvd hb (Nat.dvd_of_mem_primeFactorsList hp)
    by_contra hlt
    push Not at hlt
    rw [hfac, Finsupp.tsub_apply, sm_factorization, Finsupp.filter_apply,
      if_pos hlt] at hpos
    omega
  have hpow : y ^ (a / sm y a).primeFactorsList.length ≤ a / sm y a := by
    calc y ^ (a / sm y a).primeFactorsList.length
        ≤ (a / sm y a).primeFactorsList.prod := List.pow_card_le_prod _ _ hge
      _ = a / sm y a := Nat.prod_primeFactorsList hb
  have hle : a / sm y a ≤ a := Nat.div_le_self _ _
  rw [cardFactors_apply]
  have h3 : y ^ (a / sm y a).primeFactorsList.length < y ^ (K + 1) := by omega
  have := (Nat.pow_lt_pow_iff_right (by omega : 1 < y)).mp h3
  omega

end OMA.Erdos535H2

open OMA.Erdos535H2 Erdos535 ArithmeticFunction ArithmeticFunction.Omega in
theorem OMA.solution : OMA.R_Erdos535_erdos_535_R1.H2 := by
  classical
  intro N y L K hy hL hK A hA
  have hmem : ∀ a ∈ A, a ≠ 0 ∧ a ≤ N := by
    intro a ha
    have := Finset.mem_Icc.mp (hA ha)
    omega
  let g : ℕ → (Fin y → ℕ) × ℕ := fun a => (fun i => a.factorization i, Ω (a / sm y a))
  let T : Finset ((Fin y → ℕ) × ℕ) :=
    Fintype.piFinset (fun _ => Finset.range (L + 1)) ×ˢ Finset.range (K + 1)
  have hmaps : ∀ a ∈ A, g a ∈ T := by
    intro a ha
    obtain ⟨ha0, haN⟩ := hmem a ha
    simp only [T, g, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨fun i => ?_, ?_⟩
    · have := factorization_le ha0 (by omega : a < 2 ^ L) i
      omega
    · have := omega_le hy ha0 haN hK
      omega
  have hTcard : T.card = (L + 1) ^ y * (K + 1) := by
    simp [T, Finset.card_product, Fintype.card_piFinset]
  have hTne : T.Nonempty := by
    refine ⟨(fun _ => 0, 0), ?_⟩
    simp [T, Fintype.mem_piFinset]
  obtain ⟨t, htT, htmax⟩ := Finset.exists_max_image T (fun t => (A.filter (g · = t)).card) hTne
  have hsum : A.card = ∑ u ∈ T, (A.filter (g · = u)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hAle : A.card ≤ T.card * (A.filter (g · = t)).card := by
    rw [hsum]
    calc ∑ u ∈ T, (A.filter (g · = u)).card
        ≤ ∑ _u ∈ T, (A.filter (g · = t)).card := Finset.sum_le_sum htmax
      _ = T.card * (A.filter (g · = t)).card := by rw [Finset.sum_const, smul_eq_mul]
  set F := A.filter (g · = t) with hF
  rcases F.eq_empty_or_nonempty with hFe | ⟨a0, ha0F⟩
  · refine ⟨1, 0, ∅, one_pos, Nat.zero_le _, ?_, ?_, ?_⟩
    · intro a ha
      simp at ha
    · rw [hFe, Finset.card_empty, mul_zero] at hAle
      omega
    · intro b hb
      simp at hb
  · have ha0 : a0 ∈ A ∧ g a0 = t := Finset.mem_filter.mp ha0F
    let s := sm y a0
    have hsF : ∀ a ∈ F, sm y a = s := by
      intro a haF
      have ha := Finset.mem_filter.mp haF
      apply sm_eq_of_key
      intro i
      have := congrArg (fun u => u.1 i) (ha.2.trans ha0.2.symm)
      simpa [g] using this
    have hdvd : ∀ a ∈ F, s ∣ a := by
      intro a haF
      rw [← hsF a haF]
      exact sm_dvd y (hmem a (Finset.mem_filter.mp haF).1).1
    refine ⟨s, t.2, F.image (· / s), Nat.pos_of_ne_zero (sm_ne_zero y a0), ?_, ?_, ?_, ?_⟩
    · have := (Finset.mem_product.mp htT).2
      rw [Finset.mem_range] at this
      omega
    · intro b hb
      obtain ⟨a, haF, rfl⟩ := Finset.mem_image.mp hb
      have ha := Finset.mem_filter.mp haF
      have ha0' := hmem a ha.1
      refine ⟨?_, ?_⟩
      · exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0'.1) (hdvd a haF))
          (Nat.pos_of_ne_zero (sm_ne_zero y a0))
      · have h2 := congrArg Prod.snd ha.2
        simp only [g] at h2
        rw [hsF a haF] at h2
        exact h2
    · rw [Finset.card_image_of_injOn, ← hTcard]
      · exact hAle
      · intro a haF a' haF' h
        exact (Nat.div_left_inj (hdvd a haF) (hdvd a' haF')).mp h
    · intro b hb
      obtain ⟨a, haF, rfl⟩ := Finset.mem_image.mp hb
      rw [Nat.mul_div_cancel' (hdvd a haF)]
      exact (Finset.mem_filter.mp haF).1
