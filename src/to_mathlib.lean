import data.finset
import algebra.big_operators
import tactic

namespace finset

lemma sdiff_union_inter {α : Type*} [decidable_eq α] (A B : finset α) : (A \ B) ∪ (A ∩ B) = A :=
by simp only [ext, mem_union, mem_sdiff, mem_inter]; tauto

lemma sdiff_inter_inter {α : Type*} [decidable_eq α] (A B : finset α) : disjoint (A \ B) (A ∩ B) := disjoint_of_subset_right (inter_subset_right _ _) sdiff_disjoint

@[simp] lemma sdiff_empty {α : Type*} [decidable_eq α] (s : finset α) : s \ ∅ = s := empty_union s
@[simp] lemma sdiff_idem {α : Type*} [decidable_eq α] (s t : finset α) : s \ t \ t = s \ t := by simp only [ext, mem_sdiff]; tauto
@[simp] lemma sdiff_self {α : Type*} [decidable_eq α] (s : finset α) : s \ s = ∅ := by simp only [ext, not_mem_empty, iff_self, mem_sdiff, and_not_self, forall_true_iff]
lemma inter_union_self {α : Type*} [decidable_eq α] (s t : finset α) : s ∩ (t ∪ s) = s := by simp only [ext, mem_inter, mem_union]; tauto
lemma union_sdiff_self {α : Type*} [decidable_eq α] (s t : finset α) : (s ∪ t) \ t = s \ t := by simp only [ext, mem_union, mem_sdiff]; tauto
lemma union_singleton_eq_insert {α : Type*} [decidable_eq α] (a : α) (s : finset α) : finset.singleton a ∪ s = insert a s := begin ext, rw [mem_insert, mem_union, mem_singleton] end
lemma sdiff_singleton_eq_erase {α : Type*} [decidable_eq α] (a : α) (s : finset α) : s \ finset.singleton a = erase s a := begin ext, rw [mem_erase, mem_sdiff, mem_singleton], tauto end
lemma union_sdiff_distrib_right {α : Type*} [decidable_eq α] (s₁ s₂ t : finset α) : (s₁ ∪ s₂) \ t = s₁ \ t ∪ s₂ \ t := by simp only [ext, mem_sdiff, mem_union]; tauto
lemma sdiff_union_distrib_left {α : Type*} [decidable_eq α] (s t₁ t₂ : finset α) : s \ (t₁ ∪ t₂) = (s \ t₁) ∩ (s \ t₂) := by simp only [ext, mem_union, mem_sdiff, mem_inter]; tauto
lemma union_eq_left_of_subset {α : Type*} [decidable_eq α] {s t : finset α} (h : t ⊆ s) : s ∪ t = s := by simp only [ext, mem_union]; tauto
lemma new_thing {α : Type*} [decidable_eq α] {s t : finset α} : disjoint s t ↔ s \ t = s := -- split
begin
  split; intro p,
    rw disjoint_iff_inter_eq_empty at p,
    exact union_empty (s \ t) ▸ (p ▸ sdiff_union_inter s t), 
  rw ← p, apply sdiff_disjoint
end
lemma disjoint_self_iff_empty {α : Type*} [decidable_eq α] (s : finset α) : disjoint s s ↔ s = ∅ :=
disjoint_self

lemma sdiff_subset_left {α : Type*} [decidable_eq α] (s t : finset α) : s \ t ⊆ s := by have := sdiff_subset_sdiff (le_refl s) (empty_subset t); rwa sdiff_empty at this

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

lemma exists_intermediate_set {α : Type*} [decidable_eq α] (A B : finset α) (i : ℕ) (h₁ : card A ≥ i + card B) (h₂ : B ⊆ A) : 
  ∃ (C : finset α), B ⊆ C ∧ C ⊆ A ∧ card C = i + card B :=
begin
  rcases nat.le.dest h₁ with ⟨k, _⟩, clear h₁, revert A,
  induction k with k ih,
    simp, intros A BsubA cards, exact ⟨A, BsubA, subset.refl _, cards.symm⟩,
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

end finset