---
title     : "Quantifiers: Universals and existentials"
permalink : /Quantifiers/
---

```agda
module plfa.part1.Quantifiers where
```

This chapter introduces universal and existential quantification.

## Imports

```agda
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-suc; +-mono-≤)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa.part1.Isomorphism using (_≃_; extensionality; ∀-extensionality)

open import Function using (_∘_; _$_)
open import Level renaming (zero to lzero; suc to lsuc)

open import plfa.part1.Induction using (Bin; ⟨⟩; _I; _O; inc; to; from)
```


## Universals

We formalise universal quantification using the dependent function
type, which has appeared throughout this book.  For instance, in
Chapter Induction we showed addition is associative:

    +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

which asserts for all natural numbers `m`, `n`, and `p`
that `(m + n) + p ≡ m + (n + p)` holds.  It is a dependent
function, which given values for `m`, `n`, and `p` returns
evidence for the corresponding equation.

In general, given a variable `x` of type `A` and a proposition `B x`
which contains `x` as a free variable, the universally quantified
proposition `∀ (x : A) → B x` holds if for every term `M` of type `A`
the proposition `B M` holds.  Here `B M` stands for the proposition
`B x` with each free occurrence of `x` replaced by `M`.  Variable `x`
appears free in `B x` but bound in `∀ (x : A) → B x`.

Evidence that `∀ (x : A) → B x` holds is of the form

    λ (x : A) → N x

where `N x` is a term of type `B x`, and `N x` and `B x` both contain
a free variable `x` of type `A`.  Given a term `L` providing evidence
that `∀ (x : A) → B x` holds, and a term `M` of type `A`, the term `L M`
provides evidence that `B M` holds.  In other words, evidence that
`∀ (x : A) → B x` holds is a function that converts a term `M` of type
`A` into evidence that `B M` holds.

Put another way, if we know that `∀ (x : A) → B x` holds and that `M`
is a term of type `A` then we may conclude that `B M` holds:
```agda
∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    -----------------
  → B M
∀-elim L M = L M
```
As with `→-elim`, the rule corresponds to function application.

Functions arise as a special case of dependent functions,
where the range does not depend on a variable drawn from the domain.
When a function is viewed as evidence of implication, both its
argument and result are viewed as evidence, whereas when a dependent
function is viewed as evidence of a universal, its argument is viewed
as an element of a data type and its result is viewed as evidence of
a proposition that depends on the argument. This difference is largely
a matter of interpretation, since in Agda a value of a type and
evidence of a proposition are indistinguishable.

Dependent function types are sometimes referred to as dependent
products, because if `A` is a finite type with values `x₁ , ⋯ , xₙ`,
and if each of the types `B x₁ , ⋯ , B xₙ` has `m₁ , ⋯ , mₙ` distinct
members, then `∀ (x : A) → B x` has `m₁ * ⋯ * mₙ` members.  Indeed,
sometimes the notation `∀ (x : A) → B x` is replaced by a notation
such as `Π[ x ∈ A ] (B x)`, where `Π` stands for product.  However, we
will stick with the name dependent function, because (as we will see)
dependent product is ambiguous.


#### Exercise `∀-distrib-×` (recommended)

Show that universals distribute over conjunction:
```agda
-- postulate
--   ∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
--     (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)

∀→× : ∀ {A : Set} {B C : A → Set} →
  ((x : A) → B x × C x) → ((x : A) → B x) × ((x : A) → C x)
∀→× k = ⟨ (λ x → proj₁ ∘ k $ x) , (λ x → proj₂ ∘ k $ x) ⟩
∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
     (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
×→∀ : ∀ {A : Set} {B C : A → Set} →
  ((x : A) → B x) × ((x : A) → C x) → (x : A) → B x × C x
×→∀ ⟨ aB , aC ⟩ x = ⟨ aB x , aC x ⟩
∀→×→∀ : ∀ {A : Set} {B C : A → Set} →
  (y : ((x : A) → B x) × ((x : A) → C x)) → ∀→× (×→∀ y) ≡ y
∀→×→∀ k = refl
∀-distrib-× = record {
  to = ∀→×  ;
  from = ×→∀ ;
  from∘to = λ x → refl ;
  to∘from = ∀→×→∀ }
```
Compare this with the result (`→-distrib-×`) in
Chapter [Connectives](/Connectives/).

Hint: you will need to use [`∀-extensionality`](/Isomorphism/#extensionality).

#### Exercise `⊎∀-implies-∀⊎` (practice)

Show that a disjunction of universals implies a universal of disjunctions:
```agda
-- postulate
--   ⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
--     (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ ba) a = inj₁ (ba a)
⊎∀-implies-∀⊎ (inj₂ ca) a = inj₂ (ca a)
```

∀⊎-implies-⊎∀ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x ⊎ C x) → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)
∀⊎-implies-⊎∀ f = {!f ?!}

Does the converse hold? If so, prove; if not, explain why.


#### Exercise `∀-×` (practice)

Consider the following type.
```agda
data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

→→× : ∀ {B : Tri → Set} →
  ((x : Tri) → B x) → B aa × B bb × B cc
→→× f = ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩
×→→ : ∀ {B : Tri → Set} →
  B aa × B bb × B cc → (x : Tri) → B x
×→→ ⟨ a , ⟨ _ , _ ⟩ ⟩ aa = a
×→→ ⟨ _ , ⟨ b , _ ⟩ ⟩ bb = b
×→→ ⟨ _ , ⟨ _ , c ⟩ ⟩ cc = c
∀-→→×→→ : ∀ {B : Tri → Set} →
  (y : (x : Tri) → B x) → (x : Tri) → ×→→ {B} (→→× {B} y) x ≡ y x
∀-→→×→→ y aa = refl
∀-→→×→→ y bb = refl
∀-→→×→→ y cc = refl
→→×→→ : ∀ {B : Tri → Set} →
  (y : (x : Tri) → B x) → ×→→ (→→× y) ≡ y
→→×→→ y = ∀-extensionality (∀-→→×→→ y)
×→→→× : ∀ {B : Tri → Set} →
  (y : B aa × B bb × B cc) → →→× {B} (×→→ {B} y) ≡ y
×→→→× ⟨ a , ⟨ b , c ⟩ ⟩ = refl
→≃× : ∀ {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ B aa × B bb × B cc
→≃× {B} = record {
  to = →→× ;
  from = ×→→ ;
  from∘to = →→×→→ ;
  to∘from = ×→→→× {B} }
```
Let `B` be a type indexed by `Tri`, that is `B : Tri → Set`.
Show that `∀ (x : Tri) → B x` is isomorphic to `B aa × B bb × B cc`.

Hint: you will need to use [`∀-extensionality`](/Isomorphism/#extensionality).


## Existentials

Given a variable `x` of type `A` and a proposition `B x` which
contains `x` as a free variable, the existentially quantified
proposition `Σ[ x ∈ A ] B x` holds if for some term `M` of type
`A` the proposition `B M` holds.  Here `B M` stands for
the proposition `B x` with each free occurrence of `x` replaced by
`M`.  Variable `x` appears free in `B x` but bound in
`Σ[ x ∈ A ] B x`.

We formalise existential quantification by declaring a suitable
inductive type:
```agda
data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B
```
We define a convenient syntax for existentials as follows:
```agda
Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → Bx) = Σ[ x ∈ A ] Bx
```
This is our first use of a syntax declaration, which specifies that
the term on the left may be written with the syntax on the right.
The special syntax is available only when the identifier
`Σ-syntax` is imported.

Evidence that `Σ[ x ∈ A ] B x` holds is of the form
`⟨ M , N ⟩` where `M` is a term of type `A`, and `N` is evidence
that `B M` holds.

Equivalently, we could also declare existentials as a record type:
```agda
record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′
```
Here record construction

    record
      { proj₁′ = M
      ; proj₂′ = N
      }

corresponds to the term

    ⟨ M , N ⟩

where `M` is a term of type `A` and `N` is a term of type `B M`.

Products arise as a special case of existentials, where the second
component does not depend on a variable drawn from the first
component.  When a product is viewed as evidence of a conjunction,
both of its components are viewed as evidence, whereas when it is
viewed as evidence of an existential, the first component is viewed as
an element of a datatype and the second component is viewed as
evidence of a proposition that depends on the first component.  This
difference is largely a matter of interpretation, since in Agda a value
of a type and evidence of a proposition are indistinguishable.

Existentials are sometimes referred to as dependent sums,
because if `A` is a finite type with values `x₁ , ⋯ , xₙ`, and if
each of the types `B x₁ , ⋯ B xₙ` has `m₁ , ⋯ , mₙ` distinct members,
then `Σ[ x ∈ A ] B x` has `m₁ + ⋯ + mₙ` members, which explains the
choice of notation for existentials, since `Σ` stands for sum.

Existentials are sometimes referred to as dependent products, since
products arise as a special case.  However, that choice of names is
doubly confusing, since universals also have a claim to the name dependent
product and since existentials also have a claim to the name dependent sum.

A common notation for existentials is `∃` (analogous to `∀` for universals).
We follow the convention of the Agda standard library, and reserve this
notation for the case where the domain of the bound variable is left implicit:
```agda
∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B
```
The special syntax is available only when the identifier `∃-syntax` is imported.
We will tend to use this syntax, since it is shorter and more familiar.

Given evidence that `∀ x → B x → C` holds, where `C` does not contain
`x` as a free variable, and given evidence that `∃[ x ] B x` holds, we
may conclude that `C` holds:
```agda
∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y
```
In other words, if we know for every `x` of type `A` that `B x`
implies `C`, and we know for some `x` of type `A` that `B x` holds,
then we may conclude that `C` holds.  This is because we may
instantiate that proof that `∀ x → B x → C` to any value `x` of type
`A` and any `y` of type `B x`, and exactly such values are provided by
the evidence for `∃[ x ] B x`.

Indeed, the converse also holds, and the two together form an isomorphism:
```agda
∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
    { to      =  λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
    ; from    =  λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
    ; from∘to =  λ{ f → refl }
    ; to∘from =  λ{ g → extensionality λ{ ⟨ x , y ⟩ → refl }}
    }
```
The result can be viewed as a generalisation of currying.  Indeed, the code to
establish the isomorphism is identical to what we wrote when discussing
[implication](/Connectives/#implication).

#### Exercise `∃-distrib-⊎` (recommended)

Show that existentials distribute over disjunction:
```agda
-- postulate
--   ∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
--     ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃→⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃-syntax (λ x → B x ⊎ C x) → ∃-syntax B ⊎ ∃-syntax C
∃→⊎ ⟨ a , inj₁ x ⟩ = inj₁ ⟨ a , x ⟩
∃→⊎ ⟨ a , inj₂ y ⟩ = inj₂ ⟨ a , y ⟩

⊎→∃ : ∀ {A : Set} {B C : A → Set} →
  ∃-syntax B ⊎ ∃-syntax C → ∃-syntax (λ x → B x ⊎ C x)
⊎→∃ (inj₁ ⟨ a , x ⟩) = ⟨ a , (inj₁ x) ⟩
⊎→∃ (inj₂ ⟨ b , x ⟩) = ⟨ b , (inj₂ x) ⟩

⊎→∃→⊎ : ∀ {A : Set} {B C : A → Set} →
  (x : ∃-syntax (λ x₁ → B x₁ ⊎ C x₁)) → ⊎→∃ (∃→⊎ x) ≡ x
⊎→∃→⊎ ⟨ a , inj₁ x ⟩ = refl
⊎→∃→⊎ ⟨ a , inj₂ y ⟩ = refl

∃→⊎→∃ : ∀ {A : Set} {B C : A → Set} →
  (y : ∃-syntax B ⊎ ∃-syntax C) → ∃→⊎ (⊎→∃ y) ≡ y
∃→⊎→∃ (inj₁ ⟨ a , x ⟩) = refl
∃→⊎→∃ (inj₂ ⟨ a , x ⟩) = refl

∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ = record {
  to = ∃→⊎ ;
  from = ⊎→∃ ;
  from∘to = ⊎→∃→⊎ ;
  to∘from = ∃→⊎→∃ }
```

#### Exercise `∃×-implies-×∃` (practice)

Show that an existential of conjunctions implies a conjunction of existentials:
```agda
-- postulate
  -- ∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
    -- ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ a , ⟨ ba , ca ⟩ ⟩ = ⟨ ⟨ a , ba ⟩ , ⟨ a , ca ⟩ ⟩
```
Does the converse hold? If so, prove; if not, explain why.

×∃-implies-∃× : ∀ {A : Set} {B C : A → Set} →
  (∃[ x ] B x) × (∃[ x ] C x) → ∃[ x ] (B x × C x)
×∃-implies-∃× ⟨ ⟨ a₁ , ba ⟩ , ⟨ a₂ , ca ⟩ ⟩ = ⟨ {!!} , ⟨ {!!} , {!!} ⟩ ⟩

Impossible. Because a₁ ≠ a₂.

#### Exercise `∃-⊎` (practice)

Let `Tri` and `B` be as in Exercise `∀-×`.
Show that `∃[ x ] B x` is isomorphic to `B aa ⊎ B bb ⊎ B cc`.

```agda
∃→⊎⊎⊎ : ∀ {B : Tri → Set} →
  ∃-syntax B → B aa ⊎ B bb ⊎ B cc
∃→⊎⊎⊎ ⟨ aa , bx ⟩ = inj₁ bx
∃→⊎⊎⊎ ⟨ bb , bx ⟩ = inj₂ (inj₁ bx)
∃→⊎⊎⊎ ⟨ cc , bx ⟩ = inj₂ (inj₂ bx)

⊎⊎⊎→∃ : ∀ {B : Tri → Set} →
  B aa ⊎ B bb ⊎ B cc → ∃-syntax B
⊎⊎⊎→∃ (inj₁ x) = ⟨ aa , x ⟩
⊎⊎⊎→∃ (inj₂ (inj₁ x)) = ⟨ bb , x ⟩
⊎⊎⊎→∃ (inj₂ (inj₂ x)) = ⟨ cc , x ⟩

⊎⊎⊎→∃→⊎⊎⊎ : ∀ {B : Tri → Set} →
 (x : ∃-syntax B) → ⊎⊎⊎→∃ (∃→⊎⊎⊎ x) ≡ x
⊎⊎⊎→∃→⊎⊎⊎ ⟨ aa , bx ⟩ = refl
⊎⊎⊎→∃→⊎⊎⊎ ⟨ bb , bx ⟩ = refl
⊎⊎⊎→∃→⊎⊎⊎ ⟨ cc , bx ⟩ = refl

∃→⊎⊎⊎→∃ : ∀ {B : Tri → Set} →
  (y : B aa ⊎ B bb ⊎ B cc) → ∃→⊎⊎⊎ {B} (⊎⊎⊎→∃ {B} y) ≡ y
∃→⊎⊎⊎→∃ (inj₁ x) = refl
∃→⊎⊎⊎→∃ (inj₂ (inj₁ x)) = refl
∃→⊎⊎⊎→∃ (inj₂ (inj₂ x)) = refl

∃≃⊎ : ∀ {B : Tri → Set} →
  ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc
∃≃⊎ = record {
  to = ∃→⊎⊎⊎ ;
  from = ⊎⊎⊎→∃ ;
  from∘to = ⊎⊎⊎→∃→⊎⊎⊎ ;
  to∘from = ∃→⊎⊎⊎→∃ }
```


## An existential example

Recall the definitions of `even` and `odd` from
Chapter [Relations](/Relations/):
```agda
data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)
```
A number is even if it is zero or the successor of an odd number, and
odd if it is the successor of an even number.

We will show that a number is even if and only if it is twice some
other number, and odd if and only if it is one more than twice
some other number.  In other words, we will show:

`even n`   iff   `∃[ m ] (    m * 2 ≡ n)`

`odd  n`   iff   `∃[ m ] (1 + m * 2 ≡ n)`

By convention, one tends to write constant factors first and to put
the constant term in a sum last. Here we've reversed each of those
conventions, because doing so eases the proof.

Here is the proof in the forward direction:
```agda
even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero                       =  ⟨ zero , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩  =  ⟨ suc m , refl ⟩

odd-∃  (odd-suc e)  with even-∃ e
...                    | ⟨ m , refl ⟩  =  ⟨ m , refl ⟩
```
We define two mutually recursive functions. Given
evidence that `n` is even or odd, we return a
number `m` and evidence that `m * 2 ≡ n` or `1 + m * 2 ≡ n`.
We induct over the evidence that `n` is even or odd:

* If the number is even because it is zero, then we return a pair
consisting of zero and the evidence that twice zero is zero.

* If the number is even because it is one more than an odd number,
then we apply the induction hypothesis to give a number `m` and
evidence that `1 + m * 2 ≡ n`. We return a pair consisting of `suc m`
and evidence that `suc m * 2 ≡ suc n`, which is immediate after
substituting for `n`.

* If the number is odd because it is the successor of an even number,
then we apply the induction hypothesis to give a number `m` and
evidence that `m * 2 ≡ n`. We return a pair consisting of `m` and
evidence that `1 + m * 2 ≡ suc n`, which is immediate after
substituting for `n`.

This completes the proof in the forward direction.

Here is the proof in the reverse direction:
```agda
∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨  zero , refl ⟩  =  even-zero
∃-even ⟨ suc m , refl ⟩  =  even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd  ⟨     m , refl ⟩  =  odd-suc (∃-even ⟨ m , refl ⟩)
```
Given a number that is twice some other number we must show it is
even, and a number that is one more than twice some other number we
must show it is odd.  We induct over the evidence of the existential,
and in the even case consider the two possibilities for the number
that is doubled:

- In the even case for `zero`, we must show `zero * 2` is even, which
follows by `even-zero`.

- In the even case for `suc n`, we must show `suc m * 2` is even.  The
inductive hypothesis tells us that `1 + m * 2` is odd, from which the
desired result follows by `even-suc`.

- In the odd case, we must show `1 + m * 2` is odd.  The inductive
hypothesis tell us that `m * 2` is even, from which the desired result
follows by `odd-suc`.

This completes the proof in the backward direction.

#### Exercise `∃-even-odd` (practice)

How do the proofs become more difficult if we replace `m * 2` and `1 + m * 2`
by `2 * m` and `2 * m + 1`?  Rewrite the proofs of `∃-even` and `∃-odd` when
restated in this way.

```agda
-- Your code goes here
suc-+-asso : ∀ {m n : ℕ} → m + suc n ≡ suc m + n
suc-+-asso {zero} {n} = refl
suc-+-asso {suc m} {n} rewrite suc-+-asso {m} {n} = refl

+-identityʳ : ∀ {m : ℕ} → m + 0 ≡ m
+-identityʳ {zero} = refl
+-identityʳ {suc m} rewrite +-identityʳ {m} = refl

even-∃′ : ∀ {n : ℕ} → even n → ∃[ m ] (    2 * m ≡ n)
odd-∃′  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + 2 * m ≡ n)

even-∃′ even-zero = ⟨ 0 , refl ⟩
even-∃′ (even-suc x) with odd-∃′ x
... | ⟨ m , refl ⟩ = ⟨ suc m ,
  begin
    suc (m + suc (m + 0))
  ≡⟨ cong (λ x → suc (m + suc x)) $ +-identityʳ {m} ⟩
    suc (m + suc m)
  ≡⟨ (cong suc $ suc-+-asso {m} {m}) ⟩
    suc (suc (m + m))
  ≡⟨ cong (λ x → suc (suc (m + x))) ∘ sym $ +-identityʳ {m} ⟩
    suc (suc (m + (m + 0)))
  ∎ ⟩
odd-∃′ (odd-suc x) with even-∃′ x
... | ⟨ m , refl ⟩ = ⟨ m , refl ⟩

∃-even′ : ∀ {n : ℕ} → ∃[ m ] (    2 * m ≡ n) → even n
∃-odd′  : ∀ {n : ℕ} → ∃[ m ] (1 + 2 * m ≡ n) →  odd n

∃-even′ ⟨ zero , refl ⟩ = even-zero
∃-even′ ⟨ suc x , refl ⟩ with ∃-odd′ ⟨ x , refl ⟩
... | odd-suc m rewrite +-identityʳ {x}
  | suc-+-asso {x} {x}
  = even-suc (odd-suc m)
∃-odd′ ⟨ x , refl ⟩ with ∃-even′ ⟨ x , refl ⟩
... | m = odd-suc m
```

#### Exercise `∃-+-≤` (practice)

Show that `y ≤ z` holds if and only if there exists a `x` such that
`x + y ≡ z`.

```agda
-- Your code goes here
≤→∃ : ∀ { y z : ℕ } →
  y ≤ z → ∃[ x ] (x + y ≡ z)
≤→∃ {z = z} z≤n = ⟨ z , +-identityʳ ⟩
≤→∃ {y = suc m} (s≤s y<z) with ≤→∃ y<z
... | ⟨ x , refl ⟩ = ⟨ x , suc-+-asso {x} {m} ⟩

≤-suc : ∀ {x : ℕ} → x ≤ suc x
≤-suc {zero} = z≤n
≤-suc {suc x} = s≤s $ ≤-suc {x}

∃→≤ : ∀ { y z : ℕ } →
  ∃[ x ] (x + y ≡ z) → y ≤ z
∃→≤ ⟨ zero , refl ⟩ = ≤-refl
∃→≤ {y} ⟨ suc x , refl ⟩ with ∃→≤ {y} ⟨ x , refl ⟩
... | m = ≤-trans (≤-suc {y}) (s≤s m)
```

∃≤∃ : ∀ {y z : ℕ} → (x : y ≤ z) → ∃→≤ (≤→∃ x) ≡ x
∃≤∃ {0} {z} z≤n = begin
    ∃→≤ ⟨ z , +-identityʳ ⟩
  ≡⟨ {!!} ⟩
    z≤n
  ∎
∃≤∃ (s≤s x) = {!!}

∃-+-≤ : ∀ { y z : ℕ } → y ≤ z ≃ ∃[ x ] (x + y ≡ z)
∃-+-≤ = record {
  to = ≤→∃ ;
  from = ∃→≤ ;
  from∘to = {!!} ;
  to∘from = {!!} }

Hard to prove isomorphism.


## Existentials, Universals, and Negation

Negation of an existential is isomorphic to the universal
of a negation.  Considering that existentials are generalised
disjunction and universals are generalised conjunction, this
result is analogous to the one which tells us that negation
of a disjunction is isomorphic to a conjunction of negations:
```agda
¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to      =  λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩ }
    ; from    =  λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
    ; from∘to =  λ{ ¬∃xy → extensionality λ{ ⟨ x , y ⟩ → refl } }
    ; to∘from =  λ{ ∀¬xy → refl }
    }
```
In the `to` direction, we are given a value `¬∃xy` of type
`¬ ∃[ x ] B x`, and need to show that given a value
`x` that `¬ B x` follows, in other words, from
a value `y` of type `B x` we can derive false.  Combining
`x` and `y` gives us a value `⟨ x , y ⟩` of type `∃[ x ] B x`,
and applying `¬∃xy` to that yields a contradiction.

In the `from` direction, we are given a value `∀¬xy` of type
`∀ x → ¬ B x`, and need to show that from a value `⟨ x , y ⟩`
of type `∃[ x ] B x` we can derive false.  Applying `∀¬xy`
to `x` gives a value of type `¬ B x`, and applying that to `y` yields
a contradiction.

The two inverse proofs are straightforward, where one direction
requires extensionality.


#### Exercise `∃¬-implies-¬∀` (recommended)

Show that existential of a negation implies negation of a universal:
```agda
-- postulate
--   ∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
--     → ∃[ x ] (¬ B x)
--       --------------
--     → ¬ (∀ x → B x)
∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ a , f ⟩ x = f $ x a
```
Does the converse hold? If so, prove; if not, explain why.

¬∀-implies-∃¬ : ∀ {A : Set} {B : A → Set}
  → ¬ (∀ x → B x)
    --------------
  → ∃[ x ] (¬ B x)
¬∀-implies-∃¬ x = ⟨ {!!} , (λ b → {!!}) ⟩

We only know that there exists, but we don't have the witness.

#### Exercise `Bin-isomorphism` (stretch) {#Bin-isomorphism}

Recall that Exercises
[Bin](/Naturals/#Bin),
[Bin-laws](/Induction/#Bin-laws), and
[Bin-predicates](/Relations/#Bin-predicates)
define a datatype `Bin` of bitstrings representing natural numbers,
and asks you to define the following functions and predicates:

    to   : ℕ → Bin
    from : Bin → ℕ
    Can  : Bin → Set

And to establish the following properties:

    from (to n) ≡ n

    ----------
    Can (to n)

    Can b
    ---------------
    to (from b) ≡ b

Using the above, establish that there is an isomorphism between `ℕ` and
`∃[ b ] Can b`.

We recommend proving the following lemmas which show that, for a given
binary number `b`, there is only one proof of `One b` and similarly
for `Can b`.

    ≡One : ∀ {b : Bin} (o o′ : One b) → o ≡ o′

    ≡Can : ∀ {b : Bin} (c c′ : Can b) → c ≡ c′

Many of the alternatives for proving `to∘from` turn out to be tricky.
However, the proof can be straightforward if you use the following lemma,
which is a corollary of `≡Can`.

    proj₁≡→Can≡ : {c c′ : ∃[ b ] Can b} → proj₁ c ≡ proj₁ c′ → c ≡ c′

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (x O) = x I
inc (x I) = (inc x) O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc x) = inc (to x)

from : Bin → ℕ
from ⟨⟩ = 0
from (x O) = 2 * from x
from (x I) = 1 + 2 * from x

```agda
-- Your code goes here
_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

f∘i : ∀ {b : Bin} → from (inc b) ≡ suc (from b)
f∘i {⟨⟩} = refl
f∘i {b O} = refl
f∘i {b I} rewrite f∘i {b} = cong suc $ +-suc (from b) (from b + 0)

f∘t : ∀ {n : ℕ} → from (to n) ≡ n
f∘t {zero} = refl
f∘t {suc n} rewrite f∘i {to n} = cong suc $ f∘t {n}

data One : Bin → Set where
  o1 : One (⟨⟩ I)
  1[_]O : ∀ {b} → One b → One (b O)
  1[_]I : ∀ {b} → One b → One (b I)

≡One : ∀ {b : Bin} (o o′ : One b) → o ≡ o′
≡One o1 o1 = refl
≡One 1[ x ]O 1[ y ]O = cong 1[_]O $ ≡One x y
≡One 1[ x ]I 1[ y ]I = cong 1[_]I $ ≡One x y

one-inc : ∀ {b} → One b → One (inc b)
one-inc o1 = 1[ o1 ]O
one-inc 1[ x ]O = 1[ x ]I
one-inc {b I} 1[ x ]I = let
    t = one-inc x
  in 1[ t ]O

one-≥1 : ∀ {b} → One b → 1 ≤ from b
one-≥1 o1 = s≤s z≤n
one-≥1 {b O} 1[ t ]O rewrite (+-identityʳ { from b })
  = +-mono-≤ z≤n (one-≥1 t)
one-≥1 {b I} 1[ t ]I rewrite (+-identityʳ { from b })
  = s≤s $ +-mono-≤ (z≤n {from b}) z≤n

n+n≡2n : ∀ {n} → n + n ≡ 2 * n
n+n≡2n {zero} = refl
n+n≡2n {suc n} rewrite (+-identityʳ {n})= refl

-- TODO
to2N≡toNO : ∀ {n : ℕ}
  → 1 ≤ n
-------------------
  → to (2 * n) ≡ (to n) O
to2N≡toNO {suc zero} x = refl
to2N≡toNO {suc (suc n)} (s≤s z≤n) = begin
    inc (inc (to (n + suc (suc (n + zero)))))
  ≡⟨ (cong (inc ∘ inc ∘ to) $ +-suc n (suc n + 0)) ⟩
    inc (inc (to (suc n + (suc (n + zero)))))
  ≡⟨ (cong (inc ∘ inc) $ to2N≡toNO {suc n} (s≤s z≤n)) ⟩
    (inc (inc (to n)) O)
  ∎
--   rewrite (+-suc n ((suc (n + 0))))
--   | n+n≡2n {suc n}
--   -- | to2N≡toNO {suc n} (s≤s z≤n)
--   = let t = to2N≡toNO {suc n} (s≤s z≤n) in begin
--     inc (inc ((to ((suc n) + suc (n + 0)))))
--   ≡⟨ cong (inc ∘ inc) $ t ⟩
--     (inc (inc (to n)) O)
--   ∎

data Can : Bin → Set where
  can0 : Can (⟨⟩ O)
  can : ∀ { b : Bin } ( t : One b ) → Can b

≡Can : ∀ {b : Bin} (c c′ : Can b) → c ≡ c′
≡Can can0 can0 = refl
≡Can can0 (can 1[ () ]O)
≡Can (can 1[ () ]O) can0
≡Can (can x) (can y) = cong can $ ≡One x y

can-inc : ∀ {b} → Can b → Can (inc b)
can-inc can0 = can o1
can-inc (can o1) = can 1[ o1 ]O
can-inc (can 1[ t ]O) = can 1[ t ]I
can-inc (can 1[ t ]I) = can 1[ one-inc t ]O

can-to : ∀ {n} → Can (to n)
can-to {zero} = can0
can-to {suc n} = let t = can-to {n}
  in can-inc t

can-t∘f : ∀ {b} → Can b → to (from b) ≡ b
can-t∘f can0 = refl
can-t∘f (can o1) = refl
can-t∘f {b O} (can 1[ t ]O) = begin
    to (from b + (from b + zero))
  ≡⟨ to2N≡toNO (one-≥1 t) ⟩
    to (from b) O
  ≡⟨ cong (_O) $ can-t∘f {b} (can t) ⟩
    b O
  ∎
can-t∘f {b I} (can 1[ t ]I) = begin
    inc (to (from b + (from b + 0)))
  ≡⟨ cong inc ∘ to2N≡toNO {from b} $ one-≥1 t ⟩
    inc (to (from b) O)
  ≡⟨ cong (_I) ∘ can-t∘f {b} $ (can t) ⟩
    b I
  ∎

f∘t-can : ∀ {n}
  → from (to n) ≡ n
  ----------
  → Can (to n)
f∘t-can {zero} x = can0
f∘t-can {suc n} x with f∘t-can {n} (f∘t {n})
... | cn = can-inc cn

∃proj₁ : ∀ {a : Set} {b : a → Set} → ∃ b → a
∃proj₁ ⟨ x , y ⟩ = x

-- ⟨≡⟩ : ∀ {x y : Set} {z : x → Set} {w : y → Set} → x ≡ y → {!extensionality!} → _≡_ ⟨ x , z ⟩ ⟨ y , w ⟩
-- ⟨≡⟩ e1 e2 = {!!}

proj₁≡→Can≡ : ∀ {b : Bin} {c c′ : ∃[ b ] (Can b)} → ∃proj₁ c ≡ ∃proj₁ c′ → c ≡ c′
proj₁≡→Can≡ {c = ⟨ ⟨⟩ , can () ⟩} {⟨ ⟨⟩ , can t ⟩} refl
proj₁≡→Can≡ {c = ⟨ x O , cx ⟩} {⟨ .x O , cy ⟩} refl = cong (⟨_,_⟩ (x O)) $ ≡Can cx cy
proj₁≡→Can≡ {c = ⟨ x I , cx ⟩} {⟨ .x I , cy ⟩} refl = cong (⟨_,_⟩ (x I)) $ ≡Can cx cy

∃Can→ℕ : ∀ {b : Bin} → ∃[ b ] Can b → ℕ
∃Can→ℕ ⟨ x , cx ⟩ = from x

∃Can→ℕ→∃Can : ∀ {b : Bin} → (y : ∃[ b ] Can b)
  → ⟨ to (∃Can→ℕ {b} y) , can-to {∃Can→ℕ {b} y} ⟩ ≡ y
∃Can→ℕ→∃Can {b} ⟨ x , cx ⟩ = proj₁≡→Can≡ {b} (can-t∘f cx)

ℕ≃∃Can : ∀ {b : Bin} → ℕ ≃ ∃[ b ] Can b
ℕ≃∃Can {b} = record {
  to = λ x → ⟨ (to x) , (can-to {x}) ⟩ ;
  from = λ x → ∃Can→ℕ {b} x ;
  from∘to = λ x → f∘t {x} ;
  to∘from = ∃Can→ℕ→∃Can {b} }
```


## Standard library

Definitions similar to those in this chapter can be found in the standard library:
```agda
import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
```


## Unicode

This chapter uses the following unicode:

    Π  U+03A0  GREEK CAPITAL LETTER PI (\Pi)
    Σ  U+03A3  GREEK CAPITAL LETTER SIGMA (\Sigma)
    ∃  U+2203  THERE EXISTS (\ex, \exists)
