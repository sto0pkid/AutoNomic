open import Agda.Primitive

data Exists {i} {j} (A : Set i) (P : A → Set j) : Set (i ⊔ j) where
 _blep_ : (a : A) -> P a -> Exists A P

syntax Exists A (λ x → e) = ∃ x ∈ A , e

data _==_ {i} {A : Set i} (x : A) : A → Set where
 refl : x == x

singletons : Set₁
-- singletons = ∃ A ∈ Set , (∃ x ∈ A , ((y : A) → x == y))
singletons = ∃ A ∈ Set , (∃ x ∈ A , (∀ y → x == y))

data True : Set where
 unit : True

_is-singleton : Set → Set
A is-singleton = ∃ x ∈ A , ((y : A) → x == y)

True-is-singleton' : (y : True) → unit == y
True-is-singleton' unit = refl

True-is-singleton : True is-singleton
True-is-singleton = (unit blep True-is-singleton')
