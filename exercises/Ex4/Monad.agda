---------------------------------------------------------------------------
-- Week 4 exercises for the Logika v računalništvu course at UL FMF      --
-- Part 3 (Monads)                                                       --
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

module Ex4.Monad where

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

{-
   Importing definitions of monoids from `Ex4.Monoid`.

   If you start working on this module before filling
   all the holes in `Ex4.Monoid`, please uncomment the
   pragma `{-# OPTIONS --allow-unsolved-metas #-}` in
   the beginning of the ``Ex4.Monoid` module.
-}

open import Ex4.Monoid


----------------
-- Exercise 5 --
----------------

{-
   Recall the record type of monads (in their Kleisli triple form).
-}

record Monad {l} : Set (lsuc l) where
  field
    -- carrier (object map) fo the Kleisli triple
    T       : Set l → Set l
    -- unit
    η       : {X : Set l} → X → T X
    -- bind
    _>>=_   : {X Y : Set l} → T X → (X → T Y) → T Y
    -- laws
    η-left  : {X Y : Set l} (x : X) (f : X → T Y) → η x >>= f ≡ f x
    η-right : {X : Set l} (c : T X) → c >>= η ≡ c
    >>=-assoc : {X Y Z : Set l} (c : T X) (f : X → T Y) (g : Y → T Z)
              → ((c >>= f) >>= g) ≡ c >>= (λ x → f x >>= g)

{-
   Show that any monoid induces a monad, namely, the writer monad.

   For background: In PL, the writer monad is used to model the
   computational effect of writing/outputting elements of a monoid.
-}
module _ {l} (Mon : Monoid {l}) where
  open Monoid Mon
  
  Writer : Monad {l}
  Writer = record {
    T         = λ X → M × X ;
    η         = λ x → (Monoid.ε Mon , x) ;
    _>>=_     = λ (m , x) f → (proj₁ (f x) · m) , proj₂ (f x) ;
    η-left    = λ {X Y} m f →
    begin
    proj₁ (f m) · ε , proj₂ (f m) ≡⟨  cong (_, proj₂ (f m)) (ε-right (proj₁ (f m))) ⟩
    proj₁ (f m) , proj₂ (f m) ≡⟨ refl ⟩
    f m
    ∎
    ; 
    η-right   = λ p →
    begin
    ε · proj₁ p , proj₂ p ≡⟨ cong (_, proj₂ p) (ε-left _) ⟩
    proj₁ p , proj₂ p ≡⟨ refl ⟩
    p
    ∎
    ;
    >>=-assoc = λ p f g → cong₂ _,_ (sym (·-assoc (proj₁ (g (proj₂ (f (proj₂ p))))) (proj₁ (f (proj₂ p))) (proj₁ p)))  refl }

----------------
-- Exercise 6 --
----------------

{-
   Define an algebraic operation `write` for the `Writer` monad.
   Intuitively, given a monoid element `m`, `write` should model
   performing the computational effect of writing/outputting `m`.
-}

{-
   Notice the deliberate extra whitespace on the left to define
   `write` in the scope of the same anonymous module as `Writer`.
-}

  open Monad Writer

  write : {X : Set l} → T X → M → T X
  write (m , x) m' = m · m' , x
-- write m m' = m >>= (η m') 

{-
   Prove that the `write` operation satisfies the equational theory
   corresponding to the writer monad.
-}

  write-ε : {X : Set l} → (k : T X) → write k ε ≡ k
        
  write-ε k =
    begin
      write k ε ≡⟨ cong (_, proj₂ k) (ε-right _) ⟩
      proj₁ k , proj₂ k ≡⟨ refl ⟩
      k
    ∎

  write-· : {X : Set l} → (k : T X) → (m m' : M)
          → write (write k m) m' ≡ write k (m · m')
 
  write-· k m' m'' = cong (_, (proj₂ k)) (·-assoc (proj₁ k) m' m'')


----------------
-- Exercise 7 --
----------------

{-
   Show that every monad gives rise to a monoid. Notice that you
   have to define the monoid carrier type in the universe `Set₀`.

   Hint: The solution to this exercise is an instance of a well-known
   fact about the close relationship between monads and monoids.
-}

ToMonoid : (Mon : Monad {lzero}) → Monoid {lzero}
ToMonoid Mon = record
                 { M = T ⊤
                 ; ε = η tt
                 ; _·_ = λ x y → x >>= (λ _ → y)
                 ; ε-left = λ m → η-left tt (λ _ → m)
                 ; ε-right = λ m → η-right m
                 ; ·-assoc = λ m₁ m₂ m₃ → >>=-assoc m₁ (λ _ → m₂) (λ _ → m₃)
                 }
         where open Monad Mon


--------------------------
-- Bonus Monad Exercise --
--------------------------

{-
   Construct a monad that combines the reader monad structure from the
   lecture and the writer monad structure we covered in these exercises.

   Given a type/set `S` and a monoid `(M,ε,·)`, the carrier of the
   respective monad is given by the functor `S → M × (-)`. Such monads
   are commonly called update monad update. For more information on them,
   see this article: https://danel.ahman.ee/papers/types13postproc.pdf.

   In order to equip the functor `S → M × (-)` with a monad structure, you
   will need additional (but standard) algebraic structure that describes
   the interaction of the type/set `S` and the monoid (`Act : ?` hole below).

   Can you reverse engineer this structure from what you need to define
   `>>=` and prove the monad laws? The name of the `Act` variable is a
   good hint, namely, you need an action of the monoid on `S`. Define
   this additional structure as a record type (data + equational laws).
-}

record Action {l} (Mon : Monoid {l})  (S : Set l) : Set (lsuc l) where
  open Monoid Mon
  field
    _·ᴬ_ : M → S → S
    ·ᴬ-unit : (s : S) → ε ·ᴬ s ≡ s
    ·ᴬ-hom : (s : S) → (m₁ m₂ : M) → m₁ ·ᴬ (m₂ ·ᴬ s) ≡ (m₁ · m₂) ·ᴬ s

module _ {l} (S : Set l) (Mon : Monoid {l}) (Act : Action Mon S ) where

  open Monoid Mon
  open Action Act
  Update : Monad {l}
  Update = record
             { T = λ X → S → M × X
             ; η = λ x s → ε , x
             ; _>>=_ = bind-aux
             ; η-left = λ x f  → fun-ext (η-left-aux x f)
             ; η-right = λ c → fun-ext (λ s → cong ( _, proj₂ (c s) ) (ε-right (proj₁ (c s))) )
             ; >>=-assoc = λ c f g → fun-ext λ s → bind-assoc c f g s
             }
               where
                 bind-aux : {X Y : Set l} → (S → M × X) → (X → S → M × Y) → S → M × Y 
                 bind-aux f g s = let (m , x) = f s in let (m' , x') = g x (m ·ᴬ s) in (m · m') , x'

                 η-left-aux : {X Y : Set l} → (x : X) → (f : X → S → M × Y) → (s : S) → bind-aux (λ z → ε , x) f s ≡ f x s
                 η-left-aux x f s rewrite (·ᴬ-unit s) = cong (_, proj₂ (f x s)) (ε-left (proj₁ (f x s)))

                 bind-assoc : {X Y Z : Set l} →
                            (c : S → M × X) →
                            (f : X → S → M × Y) →
                            (g : Y → S → M × Z) →
                            (s : S) →
                            bind-aux (bind-aux c f) g s ≡ bind-aux c (λ x → bind-aux (f x) g) s
                 bind-assoc c f g s = cong₂ _,_ {!·ᴬ-hom ? ? ?!} {!!}
