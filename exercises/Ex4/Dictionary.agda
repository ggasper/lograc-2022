---------------------------------------------------------------------------
-- Week 4 exercises for the Logika v računalništvu course at UL FMF      --
-- Part 1 (Dictionaries)                                                 --
--                                                                       --
-- Lecturer: Andrej Bauer                                                --
-- Teaching Assistant: Danel Ahman                                       --
--                                                                       --
-- Course website: https://ucilnica.fmf.uni-lj.si/course/view.php?id=252 --
-- Lecture notes: http://www.andrej.com/zapiski/ISRM-LOGRAC-2022/        --
---------------------------------------------------------------------------

{-
   This week's exercises are split between multiple modules.
   Solve them in the following order:

   1. `Dictionary.agda`
   2. `Monoid.agda`
   3. `Monad.agda`

   Attempt the bonus exercises only when you have finished all the
   numbered exercises.
-}

module Ex4.Dictionary where

open import Level        renaming (zero to lzero; suc to lsuc)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.List    using (List; []; _∷_; length)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s; _<_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)
open import Data.Sum     using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit    using (⊤; tt)
open import Data.Vec     using (Vec; []; _∷_)

open import Function     using (id; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq                  using (_≡_; refl; sym; trans; cong; cong₂; subst; [_]; inspect)
open Eq.≡-Reasoning      using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Axiom.Extensionality.Propositional using (Extensionality)
postulate fun-ext : ∀ {a b} → Extensionality a b


----------------
-- Exercise 1 --
----------------

{-
   Recall the record type of dictionary keys (supporting decidable
   equality) and the record type of dictionaries from the lecture.
-}

_≢_ : {l : Level} {A : Set l} → A → A → Set l
x ≢ y = x ≡ y → ⊥

data Dec {l : Level} (A : Set l) : Set l where
  yes : A → Dec A
  no  : (A → ⊥) → Dec A

record Key {l : Level} : Set (lsuc l) where
  field
    Keys      : Set l
    test-keys : (k k' : Keys) → Dec (k ≡ k')

record Dictionary {l₁ l₂ l₃ : Level}
                  (K : Key {l₁}) (A : Set l₂) : Set (lsuc (l₁ ⊔ l₂ ⊔ l₃)) where

  open Key K -- opening the `K` record to easily access its fields below
  
  field
    -- type of dictionary data (for storing key-value pairs)
    Dict      : Set l₃
    -- empty dictionary
    emp       : Dict
    -- look up a key in the dictionary
    lkp       : Dict → Keys → Maybe A
    -- add a key-value pair to the dictionary
    add       : Dict → Keys × A → Dict
    -- behavioural properties
    lkp-emp   : (k : Keys)
              → lkp emp k ≡ nothing
    lkp-add-≡ : (k : Keys) (x : A) (d : Dict)
              → lkp (add d (k , x)) k ≡ just x
    lkp-add-≢ : (k k' : Keys) (x : A) (d : Dict)
              → k ≢ k'
              → lkp (add d (k , x)) k' ≡ lkp d k'

  -- derived dictionary operation (add key-value pair only if key not present)
  add-if-new : Dict → Keys × A → Dict
  add-if-new d (k , x) with lkp d k
  ... | just _  = d
  ... | nothing = add d (k , x)

  {-
     Prove the following two properties about this derived
     operation using the properties of `lkp` and `add`.

     Hint: Using `rewrite` could be a good idea. Why so?
     Alternatively, you could use the `inspect` gadget:

       https://agda.readthedocs.io/en/v2.5.2/language/with-abstraction.html#the-inspect-idiom
  -}

  lkp-add-if-new-nothing : (k : Keys) (x : A) (d : Dict)
                         → lkp d k ≡ nothing
                         → lkp (add-if-new d (k , x)) k ≡ just x
                         
  lkp-add-if-new-nothing k x d p with lkp d k
  ... | nothing = lkp-add-≡ k x d

  lkp-add-if-new-just : (k : Keys) (x x' : A) (d : Dict)
                      → lkp d k ≡ just x'
                      → lkp (add-if-new d (k , x)) k ≡ just x'
                      
  lkp-add-if-new-just k x x' d p with lkp d k | inspect (λ (d , k) → lkp d k) (d , k)
  ... | just y | [ eq ] rewrite eq = p


----------------
-- Exercise 2 --
----------------

{-
   Show that you can equip `List (K × A)` with a `Dictionary` structure.

   Note: We suggest you define `ListDict` using the `record { ... }`
   syntax instead of using copatterns. When writing out the sample
   solution to this exercise, we found that copatterns did not behave
   well when using `with` abstractions in the definitions. In
   addition, they also kept confusing Agda's termination checker.
-}

module _ {l₁ l₂} (K : Key {l₁}) (A : Set l₂) where

  open Key K
  open Dictionary

  ListDict : Dictionary K A
  ListDict = record {
    Dict      = List (Keys × A) ;
    emp       = [] ;
    lkp       = lkp-aux ;
    add       = add-aux ;
    lkp-emp   = λ k → refl ;
    lkp-add-≡ = lkp-add-aux ;
    lkp-add-≢ = lkp-add-neq-aux }

    where
      lkp-aux : List (Keys × A) → Keys → Maybe A
      lkp-aux [] k = nothing
      lkp-aux ((k' , y) ∷ l) k with test-keys k' k
      ... | yes x = just y
      ... | no x = lkp-aux l k

      add-aux : List (Keys × A) → Keys × A → List (Keys × A)
      add-aux [] (k , v) =  (k , v) ∷ []
      add-aux ((k' , w) ∷ l) (k , v)  with test-keys k' k
      ... | yes x = (k , v) ∷ l
      ... | no x = (k' , w) ∷ add-aux l (k , v)

      test-keys-refl : (k : Keys) → test-keys k k ≡ yes refl
      test-keys-refl k with test-keys k k
      ... | yes refl = refl
      ... | no x = ⊥-elim (x refl)

      lkp-add-aux : (k : Keys) (x : A) (d : List (Keys × A)) →
                      lkp-aux (add-aux d (k , x)) k ≡ just x
      lkp-add-aux k x [] rewrite test-keys-refl k = refl
      lkp-add-aux k x ((k' , v) ∷ d) with test-keys k' k
      ... | yes y rewrite test-keys-refl k = refl
      ... | no y with test-keys k' k
      ... | yes x₁ = ⊥-elim (y x₁)
      ... | no x₁ = lkp-add-aux k x d


      test-keys-neq : (k k' : Keys) → (p : k ≢ k') → test-keys k k' ≡ no p
      test-keys-neq k k' p with test-keys k k'
      ... | yes x = ⊥-elim (p x)
      ... | no x = cong no (fun-ext (λ r → ⊥-elim (p r)))

      lkp-add-neq-aux : (k k' : Keys) (x : A) (d : List (Keys × A)) →
                          k ≢ k' → lkp-aux (add-aux d (k , x)) k' ≡ lkp-aux d k'
      lkp-add-neq-aux k k' x [] p with test-keys k k'
      ... | yes x₁ = ⊥-elim (p x₁)
      ... | no x₁ = refl
      lkp-add-neq-aux k k' x ((k'' , v) ∷ d) p with test-keys k k'' | test-keys k'' k'
      ... | yes x₁ | yes refl = ⊥-elim (p x₁)
      ... | yes refl | no x₂ rewrite test-keys-neq k' k (p ∘ sym) rewrite test-keys-refl k rewrite test-keys-neq k k' p = refl
      ... | no x₁ | yes refl rewrite test-keys-neq k' k (p ∘ sym) rewrite test-keys-refl k' = refl
      ... | no x₁ | no x₂ rewrite test-keys-neq k'' k (x₁ ∘ sym)  rewrite test-keys-neq k'' k' x₂ = lkp-add-neq-aux k k' x d p

----------------
-- Exercise 3 --
----------------

{-
   Here is a small refinement of the `Dictionary` record type with an
   extra behavioural property about `add` overwriting previous values.   
-}

record Dictionary' {l₁ l₂ l₃ : Level}
                   (K : Key {l₁}) (A : Set l₂) : Set (lsuc (l₁ ⊔ l₂ ⊔ l₃)) where

  open Key K

  field
    -- inheriting all the fields from a `Dictionary`
    Dict' : Dictionary {l₁} {l₂} {l₃} K A
  open Dictionary Dict'
  
  field
    -- an additional behavioural property
    add-add-≡ : (k : Keys) (x x' : A) (d : Dict)
              → add (add d (k , x)) (k , x') ≡ add d (k , x')

{-
   Show that the lists-based dictionaries also form a `Dictionary'`.

   Depending on whether you took any shortcuts when defining `add`
   above, you might need to redefine it to satisfy `add-add-≡`. If
   you need to redefine `add`, then you will likely also need to
   reprove the lemmas involved in defining `ListDict K A`.
-}

module _ {l₁ l₂} (K : Key {l₁}) (A : Set l₂) where

  open Key K
  open Dictionary'

  ListDict' : Dictionary' K A
  ListDict' = record {
    Dict'     = ListDict K A ;
    add-add-≡ = add-add-aux }
    where
      test-keys-refl : (k : Keys) → test-keys k k ≡ yes refl
      test-keys-refl k with test-keys k k
      ... | yes refl = refl
      ... | no x = ⊥-elim (x refl)

      test-keys-neq : (k k' : Keys) → (p : k ≢ k') → test-keys k k' ≡ no p
      test-keys-neq k k' p with test-keys k k'
      ... | yes x = ⊥-elim (p x)
      ... | no x = cong no (fun-ext (λ r → ⊥-elim (p r)))

      add-add-aux : (k : Keys) (x x' : A) (d : Dictionary.Dict (ListDict K A)) →
                      Dictionary.add (ListDict K A)
                      (Dictionary.add (ListDict K A) d (k , x)) (k , x')
                      ≡ Dictionary.add (ListDict K A) d (k , x')
      add-add-aux k x x' [] with test-keys k k
      ... | yes x₁ = refl
      ... | no x₁ = ⊥-elim (x₁ refl)
      add-add-aux k x x' ((k' , x'') ∷ d) with test-keys k' k
      ... | yes x₁ rewrite test-keys-refl k = refl
      ... | no x₁ rewrite test-keys-neq k' k x₁ = cong ((k' , x'') ∷_) (add-add-aux k x x' d)

-------------------------------
-- Bonus Dictionary Exercise --
-------------------------------

{-
   Here is a further refinement of the `Dictionary` record type---this
   time it is refined with a further behavioural property `add-add-≢`,
   which states that `add` operations for distinct keys commute.
-}

record Dictionary'' {l₁ l₂ l₃ : Level}
                    (K : Key {l₁}) (A : Set l₂) : Set (lsuc (l₁ ⊔ l₂ ⊔ l₃)) where

  open Key K

  field
    Dict'' : Dictionary' {l₁} {l₂} {l₃} K A
  open Dictionary' Dict''
  open Dictionary  Dict'

  field
    -- a further behavioural property
    add-add-≢ : (k k' : Keys) (x x' : A) (d : Dict)
              → k ≢ k'
              → add (add d (k , x)) (k' , x') ≡ add (add d (k' , x')) (k , x)

{-
   Show that lists of key-value pairs can also be used to implement
   this dictionaries interface.

   Hint: You will likely need to refine the `Key` type with further
   order-theoretic properties to be able to define a new variant of
   the `add` operation that satisfies the `add-add-≢` property.
-}
module _ {l₁ l₂} (K : Key {l₁}) (A : Set l₂) where

  open Key K
  open Dictionary'
  open Dictionary''

  ListDict'' : Dictionary'' K A
  ListDict'' = record { Dict'' = ListDict' K A ; add-add-≢ = add-add-aux }
    where
      add-add-aux : (k k' : Keys) (x x' : A)
                      (d : Dictionary.Dict (Dict' (ListDict' K A))) →
                      k ≢ k' →
                      Dictionary.add (Dict' (ListDict' K A))
                      (Dictionary.add (Dict' (ListDict' K A)) d (k , x)) (k' , x')
                      ≡
                      Dictionary.add (Dict' (ListDict' K A))
                      (Dictionary.add (Dict' (ListDict' K A)) d (k' , x')) (k , x)
      add-add-aux k k' x x' [] p with test-keys k k' | test-keys k' k
      ... | yes x₁ | yes x₂ = ⊥-elim (p (sym x₂))
      ... | yes x₁ | no x₂ = ⊥-elim (p x₁)
      ... | no x₁ | yes x₂ = ⊥-elim (p (sym x₂))
      ... | no x₁ | no x₂ = {!!}
      add-add-aux k k' x x' (x₁ ∷ d) p = {!!}
