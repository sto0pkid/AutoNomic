module ChurchNat where

data _≡_ {A : Set} (x : A) : A → Set where
 refl : x ≡ x

Nat : Set₁
Nat = {A : Set} → (A → A) → A → A

zero : Nat
zero = λ f x → x

suc : Nat → Nat
suc n = λ f x → f (n f x)

_^_ : {A : Set} → (A → A) → Nat → A → A
f ^ n = λ x → n f x

f^zero≡zero : {A : Set} → (f : A → A) → (f ^ zero) ≡ zero f
f^zero≡zero f = refl

f^n≡n : {A : Set} → (f : A → A) → (n : Nat) → (f ^ n) ≡ n f
f^n≡n f n = refl

