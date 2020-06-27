import data.subtype

universes u v w

variables {α : Type u} {β : Type v} {ι : Sort w} {s t : set α}

/-- Coercion from a set to the corresponding subtype. -/
instance : has_coe_to_sort (set α) := ⟨_, λ s, {x // x ∈ s}⟩

@[simp] theorem set_coe.forall {s : set α} {p : s → Prop} :
  (∀ x : s, p x) ↔ (∀ x (h : x ∈ s), p ⟨x, h⟩) :=
subtype.forall

@[simp] theorem set_coe.exists {s : set α} {p : s → Prop} :
  (∃ x : s, p x) ↔ (∃ x (h : x ∈ s), p ⟨x, h⟩) :=
subtype.exists

namespace set

/-- The property `s.nonempty` expresses the fact that the set `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
protected def nonempty (s : set α) : Prop := ∃ x, x ∈ s

/-- Extract a witness from `s.nonempty`. This function might be used instead of case analysis
on the argument. Note that it makes a proof depend on the `classical.choice` axiom. -/
protected noncomputable def nonempty.some (h : s.nonempty) : α := classical.some h

/-- A set `s` is a `subsingleton`, if it has at most one element. -/
protected def subsingleton (s : set α) : Prop :=
∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), x = y

/-- `diagonal α` is the subset of `α × α` consisting of all pairs of the form `(a, a)`. -/
def diagonal (α : Type u) : set (α × α) := {p | p.1 = p.2}

/-- The preimage of `s : set β` by `f : α → β`, written `f ⁻¹' s`,
  is the set of `x : α` such that `f x ∈ s`. -/
def preimage (f : α → β) (s : set β) : set α := {x | f x ∈ s}

infix ` ⁻¹' `:80 := preimage
infix ` '' `:80 := image

theorem mem_image_of_mem (f : α → β) {x : α} {a : set α} (h : x ∈ a) : f x ∈ f '' a :=
⟨_, h, rfl⟩

/-- Restriction of `f` to `s` factors through `s.image_factorization f : s → f '' s`. -/
def image_factorization (f : α → β) (s : set α) : s → f '' s :=
λ p, ⟨f p.1, mem_image_of_mem f p.2⟩

/-- Range of a function.

This function is more flexible than `f '' univ`, as the image requires that the domain is in Type
and not an arbitrary Sort. -/
def range (f : ι → α) : set α := {x | ∃y, f y = x}

theorem mem_range_self {f : ι → α} (i : ι) : f i ∈ range f := ⟨i, rfl⟩

/-- Any map `f : ι → β` factors through a map `range_factorization f : ι → range f`. -/
def range_factorization (f : ι → β) : ι → range f :=
λ i, ⟨f i, mem_range_self i⟩

/-- The set `s` is pairwise `r` if `r x y` for all *distinct* `x y ∈ s`. -/
def pairwise_on (s : set α) (r : α → α → Prop) := ∀ (x ∈ s) (y ∈ s), x ≠ y → r x y

/-- The cartesian product `prod s t` is the set of `(a, b)`
  such that `a ∈ s` and `b ∈ t`. -/
protected def prod (s : set α) (t : set β) : set (α × β) :=
{p | p.1 ∈ s ∧ p.2 ∈ t}

/-- `inclusion` is the "identity" function between two subsets `s` and `t`, where `s ⊆ t` -/
def inclusion {s t : set α} (h : s ⊆ t) : s → t :=
λ x : s, (⟨x, h x.2⟩ : t)

/-- Given an index set `i` and a family of sets `s : Πa, set (π a)`, `pi i s`
is the set of dependent functions `f : Πa, π a` such that `f a` belongs to `π a`
whenever `a ∈ i`. -/
def pi {π : α → Type*} (i : set α) (s : Πa, set (π a)) : set (Πa, π a) := { f | ∀a∈i, f a ∈ s a }

end set
