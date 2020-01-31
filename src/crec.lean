import data.pfun
import data.set.finite
import data.nat.basic
open classical

noncomputable theory

universes u v
-- entire section copied from https://github.com/rwbarton/lean-model-categories/blob/top-dev/src/logic/crec.lean
section
parameters {α : Type u} {r : α → α → Prop} (hwf : well_founded r)
local infix `<` := r
parameters {C : α → Type v} (q : Π ⦃i j⦄ (h : i < j), C i → C j → Prop)
parameters
  (H : Π (a : α)
         (f : {f : Π (i : α), i < a → C i // ∀ i j ria rja rij, q rij (f i ria) (f j rja)}),
       {x : C a // ∀ i (ria : i < a), q ria (f.val i ria) x})

def crec_core : Π (a : α), roption (C a) :=
hwf.fix $ λ a I,
  ⟨∃ (t : ∀ i (ria : i < a), (I i ria).dom),
     ∀ i j ria rja rij, q rij ((I i ria).get (t i ria)) ((I j rja).get (t j rja)),
   λ h, (H a ⟨λ i ria, (I i ria).get (h.fst i ria), h.snd⟩).val⟩

lemma crec_lemma : ∀ a,
  ∃ (pa : (crec_core a).dom)
    (p' : ∀ i (ria : i < a), (crec_core i).dom)
    (q' : ∀ {i j ria rja rij}, q rij
       ((crec_core i).get (p' i ria)) ((crec_core j).get (p' j rja))),
  (crec_core a).get pa =
    (H a ⟨λ m rma, (crec_core m).get (p' m rma), λ i j ria rja rij, q'⟩).val ∧
  ∀ i (ria : i < a),
    q ria ((crec_core i).get (p' i ria)) ((crec_core a).get pa) :=
begin
  refine (tc.wf hwf).fix _,
  intros a I,
  refine ⟨_, _, _, _, _⟩,
  { simp only [crec_core, hwf.fix_eq],
    refine ⟨λ i ria, (I i (tc.base _ _ ria)).fst, _⟩,
    intros i j ria rja rij,
    convert (H j ⟨λ k hkj, (crec_core k).get (I _ _).fst, _⟩).property i rij,
    { simp only [crec_core, hwf.fix_eq], refl },
    { exact tc.trans _ _ _ (tc.base _ _ hkj) (tc.base _ _ rja) } },
  { exact λ i ria, (I _ (tc.base _ _ ria)).fst },
  { intros, refine ((I _ _).snd.snd.snd).right _ _ },
  { conv { to_lhs, simp only [crec_core, hwf.fix_eq] }, refl },
  { intros i ria,
    conv { congr, skip, simp only [crec_core, hwf.fix_eq] },
    convert (H a _).property i ria,
    refl }
end

def crec (a : α) : C a := (crec_core a).get (crec_lemma a).fst

lemma crec_consistent (i j) (h : i < j) : q h (crec i) (crec j) :=
((crec_lemma j).snd.snd.snd).2 _ _

lemma crec_eq (a) :
  crec a = (H a ⟨λ m _, crec m, λ i j h _ _, crec_consistent i j _⟩).val :=
(crec_lemma a).snd.snd.snd.1

def crec' : {f : Π i, C i // ∀ i j h, q h (f i) (f j)} := ⟨crec, crec_consistent⟩

end

lemma infinite_above_of_infinite (s : set ℕ) (hs : set.infinite s) (i : ℕ) :
  set.infinite {j ∈ s | i < j} :=
begin
  intro, apply hs, apply @set.finite_subset _ ({j : ℕ | j ≤ i} ∪ {j ∈ s | i < j}), 
  apply set.finite_union (set.finite_le_nat _) a, 
  intros x hx, cases le_or_lt x i, left, exact h, right, exact ⟨hx, h⟩
end

lemma exists_mem_of_infinite {α : Type*} (s : set α) (hs : set.infinite s) : 
  ∃ x, x ∈ s :=
set.exists_mem_of_ne_empty (λ t, hs (t.symm ▸ set.finite_empty))

lemma has_sequence_of_infinite (s : set ℕ) (hs : set.infinite s) :
  ∃ (a : ℕ → ℕ), (∀ i, a i ∈ s) ∧ (∀ i j, i < j → a i < a j) :=
begin
  obtain ⟨a, ha⟩ : {a : ℕ → s // ∀ i j, i < j → (a i).val < (a j).val} :=
    crec' nat.lt_wf (λ _ _ _ (x y : s), x.val < y.val) _,
  swap,
  { rintros t ⟨If, IH⟩,
    change {x : s // ∀ i (h : i < t), (If i h).val < x.val},
    dsimp at IH, 
    cases t,
      use indefinite_description _ (exists_mem_of_infinite _ hs),
      intros i hi, exfalso, apply not_le_of_lt hi, apply zero_le, 
    obtain ⟨x, hx⟩ := indefinite_description _ (exists_mem_of_infinite _ (infinite_above_of_infinite s hs (If t (nat.lt_succ_self _)))),
    refine ⟨⟨x, set.sep_subset _ _ hx⟩, _⟩, intros i hi, cases eq_or_lt_of_le (nat.le_of_lt_succ hi),
      convert hx.2, 
    refine trans _ hx.2, apply IH, apply h },
  refine ⟨λ n, (a n).val, λ n, (a n).property, λ i j h, _⟩,
  apply ha _ _ h
end