import data.finset
import algebra.big_operators
import tactic

open finset

lemma sdiff_union_inter {α : Type*} [decidable_eq α] (A B : finset α) : (A \ B) ∪ (A ∩ B) = A :=
by simp only [ext, mem_union, mem_sdiff, mem_inter]; tauto

lemma sdiff_inter_inter {α : Type*} [decidable_eq α] (A B : finset α) : disjoint (A \ B) (A ∩ B) := disjoint_of_subset_right (inter_subset_right _ _) sdiff_disjoint

lemma union_singleton_eq_insert {α : Type*} [decidable_eq α] (a : α) (s : finset α) : finset.singleton a ∪ s = insert a s := begin ext, rw [mem_insert, mem_union, mem_singleton] end
@[simp] lemma sdiff_empty {α : Type*} [decidable_eq α] (s : finset α) : s \ ∅ = s := empty_union s
@[simp] lemma sdiff_idem {α : Type*} [decidable_eq α] (s t : finset α) : s \ t \ t = s \ t := by simp only [ext, mem_sdiff]; tauto
lemma union_sdiff {α : Type*} [decidable_eq α] (s₁ s₂ t : finset α) : (s₁ ∪ s₂) \ t = s₁ \ t ∪ s₂ \ t := by simp only [ext, mem_sdiff, mem_union]; tauto
lemma inter_union_self {α : Type*} [decidable_eq α] (s t : finset α) : s ∩ (t ∪ s) = s := by simp only [ext, mem_inter, mem_union]; tauto
lemma union_sdiff_self {α : Type*} [decidable_eq α] (s t : finset α) : (s ∪ t) \ t = s \ t := by simp only [ext, mem_union, mem_sdiff]; tauto
lemma sdiff_singleton_eq_erase {α : Type*} [decidable_eq α] (a : α) (s : finset α) : s \ finset.singleton a = erase s a := begin ext, rw [mem_erase, mem_sdiff, mem_singleton], tauto end
lemma sdiff_union {α : Type*} [decidable_eq α] (s t₁ t₂ : finset α) : s \ (t₁ ∪ t₂) = (s \ t₁) ∩ (s \ t₂) := by simp only [ext, mem_union, mem_sdiff, mem_inter]; tauto
lemma union_eq_left_of_subset {α : Type*} [decidable_eq α] {s t : finset α} (h : t ⊆ s) : s ∪ t = s := by simp only [ext, mem_union]; tauto
lemma new_thing {α : Type*} [decidable_eq α] {s t : finset α} : disjoint s t ↔ s \ t = s := 
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
  intros x s not_mem ih _ assump,
  rw sum_insert not_mem, rw sum_insert not_mem,
  apply lt_of_lt_of_le,
    rw add_lt_add_iff_right (s.sum f),
    apply assump x (mem_insert_self _ _),
  rw add_le_add_iff_left,
  by_cases (s = ∅),
    rw h,
    rw sum_empty,
    rw sum_empty,
  apply le_of_lt,
  apply ih h,
  intros x hx,
  apply assump,
  apply mem_insert_of_mem hx
end