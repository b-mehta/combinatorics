import data.finset
import algebra.big_operators
import tactic

open finset

lemma sdiff_union_inter {α : Type*} [decidable_eq α] (A B : finset α) : (A \ B) ∪ (A ∩ B) = A :=
by simp only [ext, mem_union, mem_sdiff, mem_inter]; tauto

lemma sdiff_inter_inter {α : Type*} [decidable_eq α] (A B : finset α) : disjoint (A \ B) (A ∩ B) := 
disjoint_of_subset_right (inter_subset_right _ _) sdiff_disjoint

@[simp] lemma sdiff_empty {α : Type*} [decidable_eq α] (s : finset α) : s \ ∅ = s := empty_union s
@[simp] lemma sdiff_idem {α : Type*} [decidable_eq α] (s t : finset α) : s \ t \ t = s \ t := by simp only [ext, mem_sdiff]; tauto
@[simp] lemma sdiff_self {α : Type*} [decidable_eq α] (s : finset α) : s \ s = ∅ := by simp only [ext, not_mem_empty, iff_self, mem_sdiff, and_not_self, forall_true_iff]
lemma inter_union_self {α : Type*} [decidable_eq α] (s t : finset α) : s ∩ (t ∪ s) = s := by simp only [ext, mem_inter, mem_union]; tauto
lemma union_sdiff_self {α : Type*} [decidable_eq α] (s t : finset α) : (s ∪ t) \ t = s \ t := by simp only [ext, mem_union, mem_sdiff]; tauto
lemma union_singleton_eq_insert {α : Type*} [decidable_eq α] (a : α) (s : finset α) : finset.singleton a ∪ s = insert a s := rfl
lemma sdiff_singleton_eq_erase {α : Type*} [decidable_eq α] (a : α) (s : finset α) : s \ finset.singleton a = erase s a := begin ext, rw [mem_erase, mem_sdiff, mem_singleton], tauto end
lemma union_sdiff_distrib_right {α : Type*} [decidable_eq α] (s₁ s₂ t : finset α) : (s₁ ∪ s₂) \ t = s₁ \ t ∪ s₂ \ t := by simp only [ext, mem_sdiff, mem_union]; tauto
lemma sdiff_union_distrib_left {α : Type*} [decidable_eq α] (s t₁ t₂ : finset α) : s \ (t₁ ∪ t₂) = (s \ t₁) ∩ (s \ t₂) := by simp only [ext, mem_union, mem_sdiff, mem_inter]; tauto
lemma union_eq_left_of_subset {α : Type*} [decidable_eq α] {s t : finset α} (h : t ⊆ s) : s ∪ t = s := by simp only [ext, mem_union]; tauto

lemma sdiff_eq_self_of_disjoint {α : Type*} [decidable_eq α] {s t : finset α} : disjoint s t → s \ t = s :=
by simp [ext, disjoint_left]; tauto

lemma sdiff_eq_self_iff_disjoint {α : Type*} [decidable_eq α] {s t : finset α} : s \ t = s ↔ disjoint s t :=
⟨λ p, p ▸ sdiff_disjoint, sdiff_eq_self_of_disjoint⟩

lemma disjoint_self_iff_empty {α : Type*} [decidable_eq α] (s : finset α) : disjoint s s ↔ s = ∅ :=
disjoint_self

lemma sdiff_subset_left {α : Type*} [decidable_eq α] (s t : finset α) : s \ t ⊆ s := 
by simp [subset_iff]; tauto

lemma sdiff_partially_injective {α : Type*} [decidable_eq α] {s t₁ t₂ : finset α} : s \ t₁ = s \ t₂ → s ∩ t₁ = s ∩ t₂ :=
by simp [ext]; intros b c; replace b := b c; split; tauto

instance decidable_disjoint {α : Type*} [decidable_eq α] (U V : finset α) : decidable (disjoint U V) := 
decidable_of_decidable_of_iff (by apply_instance) disjoint_iff_inter_eq_empty.symm

lemma sum_lt_sum {α β : Type*} {s : finset α} {f g : α → β} [decidable_eq α] [ordered_cancel_comm_monoid β] : s ≠ ∅ → (∀ x ∈ s, f x < g x) → s.sum f < s.sum g := 
begin
  apply finset.induction_on s, tauto, 
  intros x s not_mem ih _ assump, simp only [sum_insert not_mem],
  apply lt_of_lt_of_le,
    rw add_lt_add_iff_right (s.sum f),
    exact assump x (mem_insert_self _ _),
  rw add_le_add_iff_left,
  by_cases (s = ∅), simp only [h, sum_empty], 
  exact (le_of_lt $ ih h $ λ t, assump t ∘ mem_insert_of_mem),
end

lemma sum_flip {α : Type*} [add_comm_monoid α] {n : ℕ} (f : ℕ → α) : sum (range (n+1)) (λ r, f (n - r)) = sum (range (n+1)) (λ r, f r) :=
begin
  induction n with n ih,
    rw [sum_range_one, sum_range_one],
  rw sum_range_succ',
  rw sum_range_succ _ (nat.succ n),
  simp [ih],
end

lemma exists_intermediate_set {α : Type*} [decidable_eq α] (A B : finset α) (i : ℕ) (h₁ : card A ≥ i + card B) (h₂ : B ⊆ A) : 
  ∃ (C : finset α), B ⊆ C ∧ C ⊆ A ∧ card C = i + card B :=
begin
  rcases nat.le.dest h₁ with ⟨k, _⟩, clear h₁, revert A,
  induction k with k ih,
    intros A BsubA cards, exact ⟨A, BsubA, subset.refl _, cards.symm⟩,
  intros A BsubA cards, 
  have: ∃ i, i ∈ A \ B, rw [exists_mem_iff_ne_empty, ← ne, ← card_pos, card_sdiff BsubA, ← cards, nat.add_right_comm, nat.add_sub_cancel, nat.add_succ], apply nat.succ_pos,
  rcases this with ⟨a, ha⟩,
  set A' := erase A a,
  have z: i + card B + k = card A',
    rw card_erase_of_mem, rw ← cards, rw nat.add_succ, rw nat.pred_succ, rw mem_sdiff at ha, exact ha.1,
  rcases ih A' _ z with ⟨B', hB', B'subA', cards⟩,
  refine ⟨B', hB', trans B'subA' (erase_subset _ _), cards⟩, 
  rintros t th, apply mem_erase_of_ne_of_mem _ (BsubA th), rintro rfl, rw mem_sdiff at ha, tauto
end

lemma exists_smaller_set {α : Type*} [decidable_eq α] (A : finset α) (i : ℕ) (h₁ : card A ≥ i) : 
  ∃ (B : finset α), B ⊆ A ∧ card B = i :=
begin
  rcases exists_intermediate_set A ∅ i _ (empty_subset _) with ⟨B, _, x₁, x₂⟩, 
  simp at x₂, exact ⟨B, x₁, x₂⟩, simpa,
end

lemma bind_sub_bind_of_sub_left {α β : Type*} [decidable_eq β] {s₁ s₂ : finset α} (t : α → finset β) (h : s₁ ⊆ s₂) : s₁.bind t ⊆ s₂.bind t :=
by intro x; simp; intros y hy hty; refine ⟨y, h hy, hty⟩

section big_operators
  lemma sum_div {α β : Type*} [division_ring β] {s : finset α} {f : α → β} {b : β} : s.sum f / b = s.sum (λx, f x / b) :=
  calc s.sum f / b = s.sum (λ x, f x * (1 / b)) : by rw [div_eq_mul_one_div, sum_mul]
       ...         = s.sum (λ x, f x / b) : by congr; ext; rw ← div_eq_mul_one_div (f x) b

  lemma sum_const_nat {α : Type*} {m : ℕ} {f : α → ℕ} {s : finset α} (h₁ : ∀x ∈ s, f x = m) : s.sum f = card s * m :=
  begin
    rw [← nat.smul_eq_mul, ← sum_const], 
    apply sum_congr rfl h₁
  end
end big_operators

section nat
  lemma choose_symm' {n a b : ℕ} (h : n = a + b) : nat.choose n a = nat.choose n b :=
  begin
    have: a = n - b, rw h, rw nat.add_sub_cancel, 
    rw [this, nat.choose_symm], apply nat.le.intro, symmetry, rwa add_comm
  end
end nat

section natchoose
  lemma dominate_choose_lt {r n : ℕ} (h : r < n/2) : nat.choose n r ≤ nat.choose n (r+1) :=
  begin
    refine le_of_mul_le_mul_right _ (nat.lt_sub_left_of_add_lt (lt_of_lt_of_le h (nat.div_le_self n 2))),
    rw ← nat.choose_succ_right_eq,
    apply nat.mul_le_mul_left,
    rw [← nat.lt_iff_add_one_le, nat.lt_sub_left_iff_add_lt, ← mul_two],
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_right h zero_lt_two) (nat.div_mul_le_self n 2),
  end

  lemma dominate_choose_lt' {n r : ℕ} (hr : r ≤ n/2) : nat.choose n r ≤ nat.choose n (n/2) :=
  begin
    refine @nat.decreasing_induction (λ k, k ≤ n/2 → nat.choose n k ≤ nat.choose n (n/2)) (λ m k a, _) r (n/2) hr (λ _, by refl) hr,
    rcases eq_or_lt_of_le a with rfl | h, refl,
    exact trans (dominate_choose_lt h) (k h)
  end 

  lemma dominate_choose {r n : ℕ} : nat.choose n r ≤ nat.choose n (n/2) :=
  begin
    cases le_or_gt r n with b b,
      cases le_or_lt r (n/2) with a h,
        apply dominate_choose_lt' a,
      rw ← nat.choose_symm b,
      apply dominate_choose_lt',
      rw [nat.div_lt_iff_lt_mul' zero_lt_two] at h,
      rw [nat.le_div_iff_mul_le' zero_lt_two, nat.mul_sub_right_distrib, nat.sub_le_iff, mul_two, nat.add_sub_cancel],
      exact le_of_lt h,
    rw nat.choose_eq_zero_of_lt b,
    apply zero_le
  end
end natchoose

lemma div_nonneg_of_nonneg_of_nonneg {α : Type*} [discrete_linear_ordered_field α] {a b : α} : 0 ≤ a → 0 ≤ b → 0 ≤ a / b :=
begin
  intros ah bh,
  cases eq_or_lt_of_le bh,
    rw [← h, div_zero], 
  apply div_nonneg_of_nonneg_of_pos ah h
end