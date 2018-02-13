```
module proofs_test where

open import Agda.Primitive

data Exists {i} {j} (A : Set i) (P : A → Set j) : Set (i ⊔ j) where
 _,_ : (x : A) → P x → Exists A P

syntax Exists A (λ x → e) = ∃ x ∈ A , e

data _==_ {i} {A : Set i} (x : A) : A → Set i where
 refl : x == x

Singleton : ∀ {i} → Set (lsuc i)
Singleton {i} = ∃ A ∈ Set {i} , (∃ x ∈ A , (∀ (y : A) → x == y))

```
