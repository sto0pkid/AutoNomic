module ChurchNat where

data _≡_ {A : Set} : A → A → Set where
 refl : (x : A) → x ≡ x

data ℕ : Set where
 𝕫 : ℕ
 𝕤 : ℕ → ℕ

Nat : Set₁
Nat = (A : Set) → (A → A) → A → A

zero : Nat
zero = λ A f x → x

suc : Nat → Nat
suc n = λ A f x → f (n A f x)

^ : (A : Set) → (A → A) → ℕ → A → A
^ A f 𝕫 = λ x → x
^ A f (𝕤 n) = λ x → f ((^ A f n) x)


[a≡b]→[fa≡fb] : (A B : Set) → (f : A → B) → (a1 a2 : A) → (p : a1 ≡ a2) → (f a1) ≡ (f a2)
[a≡b]→[fa≡fb] A B f a .a (refl .a) = refl (f a)

-- base case
f^zero≡zero : (A : Set) → (f : A → A) → (zero A f) ≡ (^ A f (zero ℕ 𝕤 𝕫))
f^zero≡zero A f = refl (λ x → x)

something : (A : Set) → (f : A → A) → (A → A) → A → A
something A f q = λ x → f (q x)

-- inductive step
[f^n≡n]→[f^suc[n]≡suc[n]] : (A : Set) → (f : A → A) → (n : Nat) → ((n A f) ≡ (^ A f (n ℕ 𝕤 𝕫))) → ((suc n) A f) ≡ (^ A f ((suc n) ℕ 𝕤 𝕫))
[f^n≡n]→[f^suc[n]≡suc[n]] A f n hyp = [a≡b]→[fa≡fb] (A → A) (A → A) (something A f) (n A f) (^ A f (n ℕ 𝕤 𝕫)) hyp

-- final step?
{-
f^n≡n : (A : Set) → (f : A → A) → (n : Nat) → (n A f) ≡ (^ A f (n ℕ 𝕤 𝕫))
f^n≡n A f n = n ? ([f^n≡n]→[f^suc[n]≡suc[n]] A f) (f^zero≡zero A f)
-}
