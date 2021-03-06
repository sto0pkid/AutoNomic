module double-negation where

data False : Set where

omega : {A : Set} → False → A
omega ()

data True : Set where
 unit : True

data _⊹_ (A B : Set) : Set where
 inl : A → A ⊹ B
 inr : B → A ⊹ B

data _×_ (A B : Set) : Set where
 _,_ : A → B → A × B

data ∃ (A : Set) (B : A → Set) : Set where
 _,_ : (x : A) → B x → ∃ A B

syntax ∃ A (λ x → e) = ∃ x ∈ A , e 

_↔_ : (A B : Set) → Set
A ↔ B = (A → B) × (B → A)

¬ : Set → Set
¬ A = A → False

False=~~False : False ↔ (¬ (¬ False))
False=~~False = ((λ q f → q) , (λ f → f (λ q → q)))

True=~~True : True ↔ (¬ (¬ True))
True=~~True = ((λ u f → f u) , (λ f → unit))



data Nat : Set where
 zero : Nat
 suc : Nat → Nat

data Ty : Set where
 $_ : Nat → Ty
 ⊤ : Ty
 ⊥ : Ty
 _∧_ : Ty → Ty → Ty
 _∨_ : Ty → Ty → Ty
 _⇒_ : Ty → Ty → Ty



{-
eval : Ty → Ctx → Set
eval ($ a) 
-}

lem1 : ∀ {A R : Set} → ((A ⊹ (A → R)) → R) → (A ⊹ (A → R))
lem1 {A} {R} f = (inr g)
 where
  g : A → R
  g a = r
   where
    r = f (inl a)

lem2 : ∀ {A R : Set} → ((A ⊹ (A → R)) → R) → (A → R)
lem2 {A} {R} f a = f (inl a)




¬¬LEM : ∀ {A R : Set} → (((A ⊹ (A → R)) → R) → R)
¬¬LEM {A} {R} f = f (inr g)
 where
  g : A → R
  g a = r
   where
    r = f (inl a)


{-
callcc : ∀ {A B : Set} → ((A → B) → A) → A)
callcc f = (
-}
