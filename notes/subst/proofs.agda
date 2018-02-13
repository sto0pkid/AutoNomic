module proofs where

open import Agda.Primitive
open import Coinduction

{-
Symbol chart:
⊤    \top
⊥    \bot
¬    \not
∧    \and
∨    \or
∀    \all
∃    \ex
∄    \exn

≡    \equiv  \==
≠    \ne
≛    \*=
≔    \:=
≈    \~~
≅    \~=


⊢    \|-
⊨    \|=


×    \x
⊹    \+

∷    \::


∈    \in
∉    \inn
∋    \ni
∌    \nin
∩    \i
∪    \un
⋂    \I
⋃    \Un
⊂    \sub
⊄    \subn
⊃    \sup
⊅    \supn
⊆    \sub=
⊈    \sub=n
⊇    \sup=
⊉    \sup=n



≤    \<=
≥    \>=


∘    \o1
∙    \.
⊗    \ox
⊕    \o+
⊚    \oo
⊙    \o.

∮
∫
∬
∭
∯
∰
∱
∲
∳

∑    \sum
∏    \prod

∸
⋯    \...
⋮
⋰
⋱
⓪
⑴
⑵
⒜
⒝
✂
∞    \inf

؋

ℓ    \ell
⊓    \glb

‖    C-x 8 (ENTER) 2016 (ENTER)


⊘    \o/
ø    \o2  
Ø    \O

⋆    \*

₁
₂
₃
ₐ
ₑ
ₕ
ᵢ
ⱼ
ₖ
ₗ
ₘ
ₙ
ₒ
ₚ
ᵣ
ₛ
ₜ
ᵤ
ₓ

...

¹
²
³
...
ᵃ
ᵇ
ᶜ
..
ᴬ
ᴮ
..


𝕒    \ba
𝔸    \bA
𝕓    \bb
𝔹    \bB
ℕ
ℚ
ℝ
ℂ
𝕊
𝕋



α    \alpha
Α    \Alpha
β    \beta
Β    \Beta
γ    \gamma
Γ    \Gamma
δ    \delta
Δ    \Delta
ε    \epsilon
Ε    \Epsilon
ζ    \zeta
Ζ    \Zeta
θ    \theta
Θ    \Theta
ι    \iota
Ι    \Iota
κ    \kappa
Κ    \Kappa
λ    \lambda
Λ    \Lambda
μ    \mu
Μ    \Mu
ν    \nu
Ν    \Nu
ξ    \xi
Ξ    \Xi
ο    \omicron
Ο    Ο
π    \pi
Π    \Pi
ρ    \rho
Ρ    \Rho
σ    \sigma
Σ    \Sigma
τ    \tau
Τ    \Tau
υ    \upsilon
Υ    \Upsilon
φ    \phi
Φ    \Phi
χ    \chi
Χ    \Chi
ψ    \psi
Ψ    \Psi
ω    \omega
Ω    \Omega
...
∇    \nabla

ℵ    \aleph
ℶ    \beth
ℷ    \gimel


⟨    \<
⟩    \>
⦃    \{{
⦄    \}}
⦇    \(|
⦈    \|)



⊔

→    \r
←    \l
↑    \u
↓    \d
↔    \lr
↕    \ud

♯    \#
♭    \b

«    \"<
»    \">
⇒    \=>






-}
{-
data Lift {i} {j} (A : Set i) : Set (i ⊔ j) where
 ↑ : (x : A) → Lift A

↓ : ∀ {i j} {A : Set i} → Lift {i} {j} A → A
↓ (↑ x) = x
-}
record Lift {i} {j} (A : Set i) : Set (i ⊔ j) where
 constructor lift
 field lower : A

open Lift public

data ⊥ : Set where
⊘ : ∀ {i} {A : Set i} → ⊥ → A
⊘ ()

¬ : ∀ {i} (A : Set i) → Set i
¬ A = A → ⊥


data ⊤ : Set where
 unit : ⊤

¬¬⊤ : ¬ (¬ ⊤)
¬¬⊤ ¬⊤ = ¬⊤ unit

data 𝟚 : Set where
 𝕥 : 𝟚
 𝕗 : 𝟚

~ : 𝟚 → 𝟚
~ 𝕥 = 𝕗
~ 𝕗 = 𝕥


 

data _∧_ {i} {j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
 _,_ : A → B → A ∧ B

first : ∀ {i} {j} {A : Set i} {B : Set j} → A ∧ B → A
first (a , _) = a

second : ∀ {i} {j} {A : Set i} {B : Set j} → A ∧ B → B
second (_ , b) = b

data _∨_ {i} {j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
 inl : A → A ∨ B
 inr : B → A ∨ B

data Exists {i} {j} (A : Set i) (P : A → Set j) : Set (i ⊔ j) where
 _,_ : (x : A) → P x → Exists A P

syntax Exists A (λ x → e) = ∃ x ∈ A , e

π₁ : ∀ {i j} {A : Set i} {P : A → Set j} → ∃ x ∈ A , (P x) → A
π₁ (a , b) = a

π₂ : ∀ {i j} {A : Set i} {P : A → Set j} → (p : ∃ x ∈ A , (P x)) → P (π₁ p)
π₂ (a , b) = b


data _==_ {i} {A : Set i} (x : A) : A → Set i where
 refl : x == x

_≠_ : ∀ {i} {A : Set i} (x y : A) → Set i
x ≠ y = ¬ (x == y)

==-sym : ∀ {i} {A : Set i} {x y : A} → x == y → y == x
==-sym {i} {A} {x} {.x} refl = refl

==-trans : ∀ {i} {A : Set i} {x y z : A} → x == y → y == z → x == z
==-trans {i} {A} {x} {.x} {.x} refl refl = refl

≠-sym : ∀ {i} {A : Set i} {x y : A} → x ≠ y → y ≠ x
≠-sym [x≠y] [y≡x] = [x≠y] (==-sym [y≡x])

cong : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) (x y : A) → x == y → f x == f y
cong f x .x refl = refl

[A≡B]→[A→B] : ∀ {i} {A B : Set i} → A == B → A → B
[A≡B]→[A→B] {A = A} {B = .A} refl a = a

⊤≠⊥ : ⊤ ≠ ⊥
⊤≠⊥ [⊤≡⊥] = [A≡B]→[A→B] [⊤≡⊥] unit

𝟚→⋆ : 𝟚 → Set
𝟚→⋆ 𝕥 = ⊤
𝟚→⋆ 𝕗 = ⊥

𝕥≠𝕗 : 𝕥 ≠ 𝕗
𝕥≠𝕗 [𝕥≡𝕗] = ⊤≠⊥ (cong 𝟚→⋆ 𝕥 𝕗 [𝕥≡𝕗])



b≠~b : (b : 𝟚) → b ≠ ~ b
b≠~b 𝕥 = 𝕥≠𝕗
b≠~b 𝕗 = ≠-sym 𝕥≠𝕗

EmptySet : ∀ {i} → Set (lsuc i)
EmptySet {i} = ∃ A ∈ (Set i) , (¬ A)

_is-empty : ∀ {i} → (A : Set i) → Set i
A is-empty = ¬ A

⊥-is-empty : ⊥ is-empty
⊥-is-empty x = x

⊥ℓ-is-empty : ∀ {i} → (Lift {lzero} {i} ⊥) is-empty
⊥ℓ-is-empty ⊥' = lower ⊥'

Singleton : ∀ {i} → Set (lsuc i)
Singleton {i} = ∃ A ∈ (Set i) , (∃ x ∈ A , (∀ (y : A) → x == y))

_is-singleton : ∀ {i} → (A : Set i) → Set i
A is-singleton = ∃ x ∈ A , (∀ (y : A) → x == y)

x∈⊤→unit≡x : ∀ (x : ⊤) → unit == x
x∈⊤→unit≡x unit = refl

⊤-is-singleton : ⊤ is-singleton
⊤-is-singleton = (unit , x∈⊤→unit≡x)

⊤ℓ-is-singleton : ∀ {i} → (Lift {lzero} {i} ⊤) is-singleton
⊤ℓ-is-singleton {i} = (record{lower = unit} , proof)
 where
  x : Lift {lzero} {i} ⊤
  x = record{lower = unit}
  proof : ∀ (y : (Lift {lzero} {i} ⊤)) → x == y
  proof (record {lower = unit}) = refl

injection : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
injection A B = ∃ f ∈ (A → B) , ((x₁ x₂ : A) → f x₁ == f x₂ → x₁ == x₂)

_is-injection : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
_is-injection {A = A} {B = B} f = ∀ (x₁ x₂ : A) → f x₁ == f x₂ → x₁ == x₂

surjection : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
surjection A B = ∃ f ∈ (A → B) , ((y : B) → (∃ x ∈ A , (f x == y)))

_is-surjection : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
_is-surjection {A = A} {B = B} f = ∀ (y : B) → ∃ x ∈ A , (f x == y)

_is-bijection : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) → Set (i ⊔ j)
f is-bijection = (f is-injection) ∧ (f is-surjection)

bijection : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
bijection A B = ∃ f ∈ (A → B) , (f is-bijection) 

∣_∣≤∣_∣ : ∀ {i j} (A : Set i) (B : Set j) → Set (i ⊔ j)
∣ A ∣≤∣ B ∣ = (injection A B) ∨ (surjection A B)

-- Functions between sets (as opposed to between types):
-- Sets are unary relations on a type.
-- A function between sets can act on arbitrary members of the domain type,
-- and doesn't need to restrict to operating only on members of the domain set,
-- but it must return members of the codomain type that are actually elements
-- of the codomain set.
_to_ : ∀ {i j k l} {A : Set i} {B : Set j} (A' : A → Set k) (B' : B → Set l) → Set (l ⊔ (j ⊔ i))
_to_ {i} {j} {k} {l} {A} {B} A' B' = ∃ f ∈ (A → B) , ((x : A) → B' (f x)) 


{-
_Dedekind-infinite : ∀ {i} {j} (A : Set i) → Set i
_Dedekind-infinite {i} {j} A = ∃ P ∈ (A → Set j) , (∃ x ∈ A , (¬ (P x)))


-- want a natural correspondence between cardinality classes of finite types and Nats.


¬ (A → B) = ¬ (¬ A ∨ B) = (¬ (¬ A)) ∧ (¬ B) = A ∧ ¬ B
-}

-- how do we capture a cardinality class?
empty-bijection-lemma : ∀ {i j} {A : Set i} {B : Set j} → A is-empty → B is-empty → bijection A B
empty-bijection-lemma {A = A} {B = B} ¬A ¬B = (f , (f-inj , f-surj))
 where
  f : A → B
  f x = ⊘ (¬A x)

  f-inj : f is-injection
  f-inj x₁ = ⊘ (¬A x₁)
  
  f-surj : f is-surjection
  f-surj y = ⊘ (¬B y)

bijection-empty-lemma : ∀ {i j} {A : Set i} {B : Set j} → A is-empty → bijection A B → B is-empty
bijection-empty-lemma {A = A} {B = B} ¬A (f , (f-inj , f-surj)) b = contradiction
 where
  fa==b : ∃ a ∈ A , (f a == b)
  fa==b = f-surj b

  contradiction = ¬A (π₁ fa==b)

singleton-bijection-lemma : ∀ {i j} {A : Set i} {B : Set j} → A is-singleton → B is-singleton → bijection A B
singleton-bijection-lemma {A = A} {B = B} (a , p₁) (b , p₂) = (f , (f-inj , f-surj))
 where
  f : A → B
  f x = b

  f-inj : f is-injection
  f-inj x₁ x₂ hyp = ==-trans (==-sym (p₁ x₁)) (p₁ x₂)
  
  f-surj : f is-surjection
  f-surj y = (a , (p₂ y))

bijection-singleton-lemma : ∀ {i j} {A : Set i} {B : Set j} → A is-singleton → bijection A B → B is-singleton
bijection-singleton-lemma {A = A} {B = B} (a , p₁) (f , (f-inj , f-surj)) = (f a , p₂)
 where
  p₂ : ∀ (x : B) → (f a) == x
  p₂ x = proof
   where
    fa'==x : ∃ a' ∈ A , (f a' == x)
    fa'==x = f-surj x

    a' : A
    a' = π₁ fa'==x

    fa==fa' : f a == f a'
    fa==fa' = cong f a a' (p₁ a')

    proof = ==-trans fa==fa' (π₂ fa'==x)

-- can't use existence of a surjection A -> B as a ≥ relationship because this breaks down in the case
-- where B is empty, there is no function from a non-empty set into an empty set.
-- On the other hand, the existence of an injection A -> B serves as a ≤ relationship and doesn't break
-- down in the case where A is empty, and as such it can cover all the cardinality classes.

empty≤singleton : ∀ {i j} {A : Set i} {B : Set j} → A is-empty → B is-singleton → injection A B
empty≤singleton {A = A} {B = B} ¬A (b , p) = (f , f-inj)
 where
  f : A → B
  f x = ⊘ (¬A x)

  f-inj : f is-injection
  f-inj x₁ = ⊘ (¬A x₁)

singleton≰empty : ∀ {i j} {A : Set i} {B : Set j} → A is-singleton → B is-empty → ¬ (injection A B)
singleton≰empty (a , p) ¬B (f , f-inj) = ⊘ (¬B (f a))



singleton≱empty : ∀ {i j} {A : Set i} {B : Set j} → A is-singleton → B is-empty → ¬ (surjection A B)
singleton≱empty (a , p) ¬B (f , f-surj) = ¬B (f a)

empty≱singleton : ∀ {i j} {A : Set i} {B : Set j} → A is-empty → B is-singleton → ¬ (surjection A B)
empty≱singleton ¬A (b , p) (f , f-surj) = ¬A (π₁ (f-surj b))

⊥≤⊤ : injection ⊥ ⊤
⊥≤⊤ = empty≤singleton ⊥-is-empty ⊤-is-singleton

[⊥≤⊤]-ℓ : ∀ {i j} → injection (Lift {lzero} {i} ⊥) (Lift {lzero} {j} ⊤)
[⊥≤⊤]-ℓ {i} {j} = empty≤singleton (⊥ℓ-is-empty {i}) (⊤ℓ-is-singleton {j})

-- Not (exists injection A -> B implies exists surjection B -> A)

¬[A≤B→B≥A] : ∀ {i j} →  ¬ ((A : Set i) (B : Set j) → injection A B → surjection B A)
¬[A≤B→B≥A] {i} {j} hyp = lower ((π₁ (hyp (Lift {lzero} {i} ⊥) (Lift {lzero} {j} ⊤) [⊥≤⊤]-ℓ)) (record {lower = unit}))

id : ∀ {i} {A : Set i} → A → A
id x = x

id-inj : ∀ {i} (A : Set i) → (id {i} {A}) is-injection
id-inj A x₁ x₂ hyp = hyp

id-surj : ∀ {i} (A : Set i) → (id {i} {A}) is-surjection
id-surj A y = (y , refl)

id-bij : ∀ {i} (A : Set i) → (id {i} {A}) is-bijection
id-bij A = (id-inj A , id-surj A)


A≤A : ∀ {i} (A : Set i) → injection A A
A≤A A = (id , id-inj A)

A≥A : ∀ {i} (A : Set i) → surjection A A
A≥A A = (id , id-surj A)

A≡A : ∀ {i} (A : Set i) → bijection A A
A≡A A = (id , id-bij A)


{-
⊥→⊥-is-singleton : (⊥ → ⊥) is-singleton
⊥→⊥-is-singleton = ((λ x → x) , (λ y → refl))
-}
surj[⊥→⊥][⊤] : surjection (⊥ → ⊥) ⊤
surj[⊥→⊥][⊤] = ((λ x → unit) , (λ y → ((λ x → x) , ((π₂ ⊤-is-singleton) y))))




A→A≥⊤ : ∀ {i} {A : Set i} → A → surjection A ⊤
A→A≥⊤ x = ((λ x → unit) , (λ y → (x , ((π₂ ⊤-is-singleton) y))))


⊘-inj : ∀ {i} (A : Set i) → (⊘ {i} {A}) is-injection
⊘-inj {i} A x₁ = ⊘ x₁


⊥≤A : ∀ {i} (A : Set i) → injection ⊥ A
⊥≤A A = (⊘ , ⊘-inj A) 

A→⊤≤A : ∀ {i} {A : Set i} → A → injection ⊤ A
A→⊤≤A {i} {A} x = (f , f-inj)
 where
  f : ⊤ → A
  f unit = x

  f-inj : f is-injection
  f-inj x₁ x₂ hyp = ==-trans (==-sym ((π₂ ⊤-is-singleton) x₁)) ((π₂ ⊤-is-singleton) x₂)

{-

-}
-- Exists injection A -> B and surjection A -> B implies injection B -> A ?


{-
Does this require axiom of choice?
A≤P[A] : ∀ {i} (A : Set i) → injection A (A → 𝟚)
A≤P[A] A = (f , f-inj)
 where
  f : A → (A → 𝟚)
  f a₁ = ... hrm might not be constructively provable ...
  f-inj

-}

compare : ∀ {i} {j} {A : Set i} → A → A → Set (i ⊔ j)
compare {i} {j} {A} x y = Lift {i} {j} (x == y)

compare-inj : ∀ {i} {j} {A : Set i} → (compare {i} {j} {A}) is-injection
compare-inj {i} {j} {A} x₁ x₂ fx₁==fx₂ = proof
 where
  fx₁ : A → Set (i ⊔ j)
  fx₁ y = Lift {i} {j} (x₁ == y)

  fx₂ : A → Set (i ⊔ j)
  fx₂ y = Lift {i} {j} (x₂ == y)

  [x₁==x₁]==[x₂==x₁] : Lift {i} {j} (x₁ == x₁) == Lift {i} {j} (x₂ == x₁)
  [x₁==x₁]==[x₂==x₁] = cong (λ f → f x₁) fx₁ fx₂ fx₁==fx₂

  [x₁==x₁] : Lift {i} {j} (x₁ == x₁)
  [x₁==x₁] = record{lower = refl}

  

  proof = ==-sym (lower ([A≡B]→[A→B] [x₁==x₁]==[x₂==x₁] [x₁==x₁]))

-- Valid
_is-valid : ∀ {i} (A : Set i) → Set i
A is-valid = (¬ A → A) ∧ ¬ (A → ¬ A)

-- Contradiction
_is-a-contradiction : ∀ {i} (A : Set i) → Set i
A is-a-contradiction = ¬ (¬ A → A) ∧ (A → ¬ A)

-- Contingency
_is-a-contingency : ∀ {i} (A : Set i) → Set i
A is-a-contingency = ¬ (¬ A → A) ∧ ¬ (A → ¬ A)

-- Paradox
_is-paradoxical : ∀ {i} (A : Set i) → Set i
A is-paradoxical = (¬ A → A) ∧ (A → ¬ A)


A→A-valid : ∀ {i} (A : Set i) → A → A is-valid
A→A-valid A x = ((λ ¬A → ⊘ (¬A x)) , (λ f → f x x))

¬A→A-contradiction : ∀ {i} (A : Set i) → ¬ A → A is-a-contradiction
¬A→A-contradiction A ¬A = ((λ f → ¬A (f ¬A)) , (λ x y → ¬A x))



¬[A==¬A] : ∀ {i} (A : Set i) → ¬ (A == ¬ A)
¬[A==¬A] {i} A [A==¬A] = contradiction
 where
  [A→¬A] : A → ¬ A
  [A→¬A] = [A≡B]→[A→B] [A==¬A]

  [¬A→A] : ¬ A → A
  [¬A→A] = [A≡B]→[A→B] (==-sym [A==¬A]) 

  f : ¬ A
  f x = [A→¬A] x x

  a : A
  a = [¬A→A] f

  contradiction = f a

{-
(Nat → Bool) → ((Nat → Bool)  → Bool)
Nat == (Nat → Bool) → Bool

wtf?
math.andrej.com/2009/10/12/constructive-gem-double-exponentials/
-}

A≤P'[A] : ∀ {i} {j} (A : Set i) → injection A (A → Set (i ⊔ j))
A≤P'[A] {i} {j} A = (compare {i} {j} {A} , compare-inj)

=A-decidable→A≤P[A] : ∀ {i} (A : Set i) → (_≡_ : A → A → 𝟚) → ((x y : A) → (x == y → ((x ≡ y) == 𝕥)) ∧ (((x ≡ y) == 𝕥) → x == y)) → injection A (A → 𝟚)
=A-decidable→A≤P[A] {i} A _≡_ ≡-decides-=A = (_≡_ , ≡-inj)
 where
  ≡-inj : _≡_ is-injection
  ≡-inj x₁ x₂ [x₁≡==x₂≡] = proof
   where
    x₁≡ : A → 𝟚
    x₁≡ y = x₁ ≡ y

    x₂≡ : A → 𝟚
    x₂≡ y = x₂ ≡ y

    x₁≡x₁==x₂≡x₁ : (x₁ ≡ x₁) == (x₂ ≡ x₁)
    x₁≡x₁==x₂≡x₁ = cong (λ f → f x₁) x₁≡ x₂≡ [x₁≡==x₂≡]

    x₁≡x₁ : (x₁ ≡ x₁) == 𝕥
    x₁≡x₁ = (first (≡-decides-=A x₁ x₁)) refl

    x₂≡x₁ : (x₂ ≡ x₁) == 𝕥
    x₂≡x₁ = ==-trans (==-sym x₁≡x₁==x₂≡x₁) x₁≡x₁

    proof = ==-sym ((second (≡-decides-=A x₂ x₁)) x₂≡x₁)

{-
A≤P[A]→=A-decidable : ∀ {i} (A : Set i) → injection A (A → 𝟚) → ∃ _≡_ ∈ (A → A → 𝟚) , ((x y : A) → (x == y → ((x ≡ y) == 𝕥)) ∧ (((x ≡ y) == 𝕥) → x == y))
A≤P[A]→=A-decidable {i} A (f , f-inj) = (_≡_ , (≡→= , =→≡))
 where
  _≡_ : A → A → 𝟚
  x ≡ y = output
   where
    fx==fy→x==y : ((f x) == (f y)) → (x == y)
    fx==fy→x==y = f-inj x y

    fx==fy→fxz==fyz : ((f x) == (f y)) → (z : A) → (f x z) == (f y z)
    fx==fy→fxz==fyz [fx==fy] z = cong (λ f → f z) (f x) (f y) [fx==fy]

    =→≡ : (x y : A) → (x == y → ((f x y) == 𝕥))
    
    no
    so
    

    output
  ≡→=
  =→≡
-}

{-
[f≠g]→∃x,fx≠gx : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → (g : A → B) → f ≠ g → ∃ x ∈ A , ((f x) ≠ (g x))
[f≠g]→∃x,fx≠gx {i} {j} {A} {B} f g [f≠g] = (x , 
-}

{-
[f≠g]→[f≢g] : ∀ {i j} {A : Set i} {B : Set j} → (f : A → B) → (g : A → B) → f ≠ g → ¬ ((x : A) → (f x) == (g x))
[f≠g]→[f≢g] {i} {j} {A} {B} f g [f≠g] hyp = 
-}

A≱P'[A] : ∀ {i} (A : Set i) → ¬ (surjection A (A → Set i))
A≱P'[A] {i} A (f , f-surj) = contradiction
 where
  evil : A → Set i
  evil a = ¬ (f a a)

  fx==evil : ∃ x ∈ A , (f x == evil)
  fx==evil = f-surj evil

  x : A
  x = π₁ fx==evil

  fxx==evilx : f x x == evil x
  fxx==evilx = cong (λ f → f x) (f x) evil (π₂ fx==evil)
  
  contradiction = ¬[A==¬A] (f x x) fxx==evilx



A≱P[A] : ∀ {i} (A : Set i) → ¬ (surjection A (A → 𝟚))
A≱P[A] A (f , f-surj) = proof
 where
  evil : A → 𝟚
  evil a = ~ (f a a)

  fx==evil : ∃ x ∈ A , (f x == evil)
  fx==evil = f-surj evil

  x : A
  x = π₁ fx==evil

  fxx==evilx : f x x == evil x
  fxx==evilx = cong (λ f → f x) (f x) evil (π₂ fx==evil)



  proof = b≠~b (f x x) fxx==evilx

_∘_ : ∀ {i j k} {A : Set i} {B : Set j} {C : Set k} → (g : B → C) → (f : A → B) → A → C
(g ∘ f) x = g (f x)


[_,_]-inverses : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) (g : B → A) → Set (i ⊔ j)
[ f , g ]-inverses = ((g ∘ f) == id) ∧ ((f ∘ g) == id)

[_,_]-inversesₑₓₜ : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) (g : B → A) → Set (i ⊔ j)
[_,_]-inversesₑₓₜ {i} {j} {A} {B} f g = ((a : A) → ((g ∘ f) a) == a) ∧ ((b : B) → ((f ∘ g) b) == b)

[f,g]-inverses→[f,g]-inversesₑₓₜ : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) (g : B → A) → [ f , g ]-inverses → [ f , g ]-inversesₑₓₜ
[f,g]-inverses→[f,g]-inversesₑₓₜ {i} {j} {A} {B} f g ( [g∘f=id] , [f∘g=id] ) = ((λ a → (cong (λ f → f a) (g ∘ f) id [g∘f=id])) , (λ b → (cong (λ f → f b) (f ∘ g) id [f∘g=id])))



singleton-inversesₑₓₜ-lemma : ∀ {i j} {A : Set i} {B : Set j} → A is-singleton → B is-singleton → ∃ f ∈ (A → B) , (∃ g ∈ (B → A) , [ f , g ]-inversesₑₓₜ)
singleton-inversesₑₓₜ-lemma {i} {j} {A} {B} (a , p₁) (b , p₂) = (f , (g , ([gf=id] , [fg=id])))
 where
  f : A → B
  f x = b

  g : B → A
  g y = a

  [gf=id] : (x : A) → ((g ∘ f) x) == x
  [gf=id] = p₁

  [fg=id] : (y : B) → ((f ∘ g) y) == y
  [fg=id] = p₂

{-
singleton-inverses-lemma : ∀ {i j} {A : Set i} {B : Set j} → A is-singleton → B is-singleton → ∃ f ∈ (A → B) , (∃ g ∈ (B → A) , [ f , g ]-inverses)
singleton-inverses-lemma {i} {j} {A} {B} (a , p₁) (b , p₂) = (f , (g , ([gf=id] , [fg=id])))
 where
  f : A → B
  f x = b

  g : B → A
  g y = a

  const-a : A → A
  const-a x = a

  const-b : B → B
  const-b y = b

  f' : A → B
  f' = λ x → (f x)

  f==f' : f == f'
  f==f' = refl

  g∘f=const-a : (g ∘ f) == const-a
  g∘f=const-a = refl

  f∘g=const-b : (f ∘ g) == const-b
  f∘g=const-b = refl

  f∘g∘f=f : (f ∘ (g ∘ f)) == f
  f∘g∘f=f = refl

  g∘f∘g=g : (g ∘ (f ∘ g)) == g
  g∘f∘g=g = refl

  -- but here we get stuck because const-a != id {A}
  {-
  Two ways to go about this:
  1) (g ∘ f) == λ x . a; 
     whatever x we take as input must be equal to a, we have this
     as an assumption, so, this is equivalent to
     λ a . a == id

  2) id == λ x . x;
     whatever x we give as output must be equal to a, we have this
     as an assumption, so, this is equivalent to
     λ x . a == (g ∘ f)
  -- needs function extensionality or something
  -}
  [gf=id] = g∘f=const-a
  [fg=id] = f∘g=const-b
-}

data List {i} (A : Set i) : Set i where
 [] : List A
 _∷_ : A → List A → List A



{-
_has-finite-cardinality_ : ∀ {i} → Set i → Nat → Set i
A has-finite-cardinality k = 
-}

-- this is so weird how the proof just pulls itself up by its own bootstraps
negation-lemma : ∀ {i j} {P : Set i} {Q : Set j} → ((P ∨ (¬ P)) → (¬ Q)) → ¬ Q
negation-lemma {i} {j} {P} {Q} hyp q = contradiction
 where
  contradiction = hyp (inr ¬P) q
   where
    ¬P : ¬ P
    ¬P p = hyp [P∨¬P]' q
     where
      [P∨¬P]' : P ∨ ¬ P
      [P∨¬P]' = inl p

    [P∨¬P] : P ∨ ¬ P
    [P∨¬P] = inr ¬P

¬¬LEM : ∀ {i} {P : Set i} → ((P ∨ ¬ P) → ⊥) → ⊥
¬¬LEM {i} {P} hyp = hyp [P∨¬P]
 where
  [P∨¬P] = inr [¬P]
   where
    [¬P] : ¬ P
    [¬P] p = hyp (inl p)
    

[P∨Q→R]→P→R : ∀ {i j k} {P : Set i} {Q : Set j} {R : Set k} → ((P ∨ Q) → R) → P → R
[P∨Q→R]→P→R hyp p = hyp (inl p)

[P∨Q→⊥]→P→⊥ : ∀ {i j} {P : Set i} {Q : Set j} → ((P ∨ Q) → ⊥) → P → ⊥
[P∨Q→⊥]→P→⊥ hyp p = hyp (inl p)

¬[P∨¬P]→P→⊥ : ∀ {i} {P : Set i} → ((P ∨ ¬ P) → ⊥) → P → ⊥
¬[P∨¬P]→P→⊥ {i} {P} hyp p = hyp (inl p)

¬[P∨¬P]→¬P : ∀ {i} {P : Set i} → ((P ∨ ¬ P) → ⊥) → ¬ P
¬[P∨¬P]→¬P {i} {P} hyp p = hyp (inl p)

¬LEM→LEM : ∀ {i} {P : Set i} → ((P ∨ ¬ P) → ⊥) → P ∨ ¬ P
¬LEM→LEM {i} {P} hyp = (inr ¬P)
 where
  ¬P : ¬ P
  ¬P p = hyp (inl p)

¬[LEM→¬LEM] : ∀ {i} {P : Set i} → ¬ ((P ∨ ¬ P) → ¬ (P ∨ ¬ P))
¬[LEM→¬LEM] {i} {P} hyp = hyp (inr ¬P) (inr ¬P)
 where
  ¬P : ¬ P
  ¬P p = hyp (inl p) (inl p)

[P∨[P→Q]→Q]→P→Q : ∀ {i j} {P : Set i} {Q : Set j} → ((P ∨ (P → Q)) → Q) → P → Q
[P∨[P→Q]→Q]→P→Q hyp p = hyp (inl p)

[P∨[P→Q]→Q]→[P∨[P→Q]] : ∀ {i j} {P : Set i} {Q : Set j} → ((P ∨ (P → Q)) → Q) → P ∨ (P → Q)
[P∨[P→Q]→Q]→[P∨[P→Q]] hyp = inr [P→Q]
 where
  [P→Q] = [P∨[P→Q]→Q]→P→Q hyp

[P∨[P→Q]→Q]→Q : ∀ {i j} {P : Set i} {Q : Set j} → ((P ∨ (P → Q)) → Q) → Q
[P∨[P→Q]→Q]→Q {i} {j} {P} {Q} hyp = hyp [P∨[P→Q]]
 where
  [P∨[P→Q]] = [P∨[P→Q]→Q]→[P∨[P→Q]] hyp

process-of-elimination : ∀ {i j} {P : Set i} {Q : Set j} → P ∨ Q → ¬ P → Q
process-of-elimination (inl p) ¬P = ⊘ (¬P p)
process-of-elimination (inr q) ¬P = q

¬P∨Q→P→Q : ∀ {i j} {P : Set i} {Q : Set j} → (¬ P ∨ Q) → P → Q
¬P∨Q→P→Q hyp p = process-of-elimination hyp (λ f → f p)


_in-list_ : ∀ {i} {A : Set i} → A → List A → Set i
x in-list [] = Lift ⊥
x in-list (y ∷ ys) = (x == y) ∨ (x in-list ys)

{-
Finiteness as listability:
-}

_is-listability-finite : ∀ {i} (A : Set i) → Set i
A is-listability-finite = ∃ as ∈ (List A) , ((a : A) → a in-list as)

⊥-is-listability-finite : ⊥ is-listability-finite
⊥-is-listability-finite = ([] , (λ q → ⊘ q))

empty-sets-are-listability-finite : ∀ {i} {A : Set i} → A is-empty → A is-listability-finite
empty-sets-are-listability-finite ¬A = ([] , (λ a → ⊘ (¬A a)))

⊤-is-listability-finite : ⊤ is-listability-finite
⊤-is-listability-finite = ((unit ∷ []) , f)
 where
  f : (x : ⊤) → x in-list (unit ∷ [])
  f unit = inl refl

singletons-are-listability-finite : ∀ {i} {A : Set i} → A is-singleton → A is-listability-finite
singletons-are-listability-finite (a , p) = ((a ∷ []) , (λ x → (inl (==-sym (p x)))))

𝟚-is-listability-finite : 𝟚 is-listability-finite
𝟚-is-listability-finite = ((𝕥 ∷ (𝕗 ∷ [])) , f)
 where
  f : (x : 𝟚) → x in-list (𝕥 ∷ (𝕗 ∷ []))
  f 𝕥 = inl refl
  f 𝕗 = inr (inl refl)

data ℕ : Set where
  𝕫 : ℕ
  𝕤 : ℕ → ℕ

length : ∀ {i} {A : Set i} → List A → ℕ
length [] = 𝕫
length (a ∷ as) = 𝕤 (length as)

the-object-in-list_at-position_equals_ : ∀ {i} {A : Set i} → List A → ℕ → A → Set i
the-object-in-list [] at-position n equals x = Lift ⊥
the-object-in-list (y ∷ ys) at-position 𝕫 equals x = x == y
the-object-in-list (y ∷ ys) at-position (𝕤 n) equals x = the-object-in-list ys at-position n equals x



_is-in-the-list_at-a-certain-position : ∀ {i} {A : Set i} → A → List A → Set i
x is-in-the-list xs at-a-certain-position = ∃ n ∈ ℕ , (the-object-in-list xs at-position n equals x)




_is-uniquely-in-the-list_ : ∀ {i} {A : Set i} → A → List A → Set i
_is-uniquely-in-the-list_ {i} {A} x xs = ∃ hyp1 ∈ (x is-in-the-list xs at-a-certain-position) , ((y : A) → (hyp2 : y is-in-the-list xs at-a-certain-position) → x == y → π₁ hyp1 == π₁ hyp2)



_has-listability-finite-cardinality_ : ∀ {i} → Set i → ℕ → Set i
A has-listability-finite-cardinality n = ∃ as ∈ (List A) , (((a : A) → a is-uniquely-in-the-list as) ∧ (length as == n))

⊥-has-listability-finite-cardinality-0 : ⊥ has-listability-finite-cardinality 𝕫
⊥-has-listability-finite-cardinality-0 = ([] , ((λ q → ⊘ q), refl))

empty-sets-have-listability-finite-cardinality-0 : ∀ {i} {A : Set i} → A is-empty → A has-listability-finite-cardinality 𝕫
empty-sets-have-listability-finite-cardinality-0 ¬A = ([] , ((λ a → ⊘ (¬A a)) , refl))

is-𝕫 : ℕ → 𝟚
is-𝕫 𝕫 = 𝕥
is-𝕫 (𝕤 n) = 𝕗


𝕫≠𝕤x : ∀ {x : ℕ} → 𝕫 ≠ 𝕤 x
𝕫≠𝕤x {x} [𝕫=𝕤x] = 𝕥≠𝕗 (cong is-𝕫 𝕫 (𝕤 x) [𝕫=𝕤x])


A-has-listability-finite-cardinality-0-implies-¬A : ∀ {i} {A : Set i} → A has-listability-finite-cardinality 𝕫 → A is-empty
A-has-listability-finite-cardinality-0-implies-¬A {i} {A} ([] , (f , p)) a = ⊘ (lower (π₂ (π₁ (f a))))
A-has-listability-finite-cardinality-0-implies-¬A {i} {A} ((x ∷ xs) , (f , p)) a = ⊘ (𝕫≠𝕤x (==-sym p))


⊤-has-listability-finite-cardinality-1 : ⊤ has-listability-finite-cardinality (𝕤 𝕫)
⊤-has-listability-finite-cardinality-1 = ((unit ∷ []) , (f , refl))
 where
  f : (x : ⊤) → x is-uniquely-in-the-list (unit ∷ [])
  f unit = ((𝕫 , refl ) , g)
   where
    g : (y : ⊤) → (hyp : y is-in-the-list (unit ∷ []) at-a-certain-position) → unit == y → 𝕫 == π₁ hyp
    g y (𝕫 , p) refl = refl
    g y ((𝕤 n) , p) refl = ⊘ (lower p)

singletons-have-listability-finite-cardinality-1 : ∀ {i} {A : Set i} → A is-singleton → A has-listability-finite-cardinality (𝕤 𝕫)
singletons-have-listability-finite-cardinality-1 {i} {A} (a , p) = ((a ∷ []) , (f , refl))
 where
  f : (x : A) → x is-uniquely-in-the-list (a ∷ [])
  f x = ((𝕫 , (==-sym (p x))) , g)
   where
    g : (y : A) → (hyp : y is-in-the-list (a ∷ []) at-a-certain-position) → x == y → 𝕫 == π₁ hyp
    g y (𝕫 , p₂) [x=y] = refl
    g y ((𝕤 n) , p₂) refl = ⊘ (lower p₂)


_gt_ : ℕ → ℕ → 𝟚
𝕫 gt n = 𝕗
(𝕤 x) gt 𝕫 = 𝕥
(𝕤 x) gt (𝕤 y) = x gt y

pred : ℕ → ℕ
pred 𝕫 = 𝕫
pred (𝕤 n) = n

𝕤-inj : 𝕤 is-injection
𝕤-inj x₁ x₂ [𝕤x₁=𝕤x₂] = cong pred (𝕤 x₁) (𝕤 x₂) [𝕤x₁=𝕤x₂]



[x-gt-y]→x≠y-ind : (x y : ℕ) → ((x gt y) == 𝕥 → x ≠ y) → ((𝕤 x) gt (𝕤 y)) == 𝕥 → (𝕤 x) ≠ (𝕤 y)
[x-gt-y]→x≠y-ind x y hyp [𝕤x-gt-𝕤y] [𝕤x=𝕤y] = hyp [𝕤x-gt-𝕤y] (𝕤-inj x y [𝕤x=𝕤y])


[x-gt-y]→x≠y : (x y : ℕ) → (x gt y) == 𝕥 → x ≠ y
[x-gt-y]→x≠y 𝕫 y [𝕫-gt-y] [𝕫=y] = 𝕥≠𝕗 (==-sym [𝕫-gt-y])
[x-gt-y]→x≠y (𝕤 x) 𝕫 [𝕤x-gt-𝕫] [𝕤x=𝕫] = 𝕫≠𝕤x (==-sym [𝕤x=𝕫]) 
[x-gt-y]→x≠y (𝕤 x) (𝕤 y) = [x-gt-y]→x≠y-ind x y ([x-gt-y]→x≠y x y)


x∈[a]→x=a : ∀ {i} {A : Set i} {x a : A} → x in-list (a ∷ []) → x == a
x∈[a]→x=a (inl p) = p
x∈[a]→x=a (inr p) = ⊘ (lower p)

x∈[a]→x=a' : ∀ {i} {A : Set i} {x a : A} → x is-in-the-list (a ∷ []) at-a-certain-position → x == a
x∈[a]→x=a' (𝕫 , p) = p
x∈[a]→x=a' (𝕤 n , p) = ⊘ (lower p)


x,y∈[a]→x=y : ∀ {i} {A : Set i} {x y a : A} → x in-list (a ∷ []) → y in-list (a ∷ []) → x == y 
x,y∈[a]→x=y x∈[a] y∈[a] = ==-trans (x∈[a]→x=a x∈[a]) (==-sym (x∈[a]→x=a y∈[a]))

x,y∈[a]→x=y' :
 ∀ {i} {A : Set i} {x y a : A} →
 x is-in-the-list (a ∷ []) at-a-certain-position →
 y is-in-the-list (a ∷ []) at-a-certain-position →
 x == y
x,y∈[a]→x=y' x∈[a] y∈[a] = ==-trans (x∈[a]→x=a' x∈[a]) (==-sym (x∈[a]→x=a' y∈[a]))


A-has-listability-finite-cardinality-1-implies-A-is-singleton : ∀ {i} {A : Set i} → A has-listability-finite-cardinality (𝕤 𝕫) → A is-singleton
A-has-listability-finite-cardinality-1-implies-A-is-singleton {i} {A} ([] , (f , p)) = ⊘ (𝕫≠𝕤x p)
A-has-listability-finite-cardinality-1-implies-A-is-singleton {i} {A} ((a ∷ []) , (f , p)) = (a , g)
 where
  g : (x : A) → a == x
  g x = [a=x]
   where
    
    [a=x] : a == x
    [a=x] = x,y∈[a]→x=y' (π₁ (f a)) (π₁ (f x)) 
A-has-listability-finite-cardinality-1-implies-A-is-singleton {i} {A} ((a ∷ (b ∷ xs)) , (f , p)) = ⊘ ([x-gt-y]→x≠y (length (a ∷ (b ∷ xs))) (𝕤 𝕫) refl p)



𝟚-has-listability-finite-cardinality-2 : 𝟚 has-listability-finite-cardinality (𝕤 (𝕤 𝕫))
𝟚-has-listability-finite-cardinality-2 = ((𝕥 ∷ (𝕗 ∷ [])) , (f , refl))
 where
  xs = (𝕥 ∷ (𝕗 ∷ []))
  f : (x : 𝟚) → x is-uniquely-in-the-list xs
  f 𝕥 = ((𝕫 , refl) , g)
   where
    g : (y : 𝟚) → (hyp : y is-in-the-list xs at-a-certain-position) → 𝕥 == y → 𝕫 == π₁ hyp
    g y (𝕫 , p) refl = refl
    g y ((𝕤 𝕫), p) [𝕥=y] = ⊘ (𝕥≠𝕗 (==-trans [𝕥=y] p))
    g y ((𝕤 (𝕤 n)) , p) [𝕥=y] = ⊘ (lower p)
  f 𝕗 = (((𝕤 𝕫) , refl) , g)
   where
    g : (y : 𝟚) → (hyp : y is-in-the-list xs at-a-certain-position) → 𝕗 == y → (𝕤 𝕫) == π₁ hyp
    g y (𝕫 , p) [𝕗=y] = ⊘ (𝕥≠𝕗 (==-trans (==-sym p) (==-sym [𝕗=y])))
    g y ((𝕤 𝕫) , p) refl = refl
    g y ((𝕤 (𝕤 n)) , p) refl = ⊘ (lower p)




_+_ : ℕ → ℕ → ℕ
𝕫 + y = y
(𝕤 x) + y = 𝕤 (x + y)


_>_ : ℕ → ℕ → Set
x > y = ∃ k ∈ ℕ , (((𝕤 k) + y) == x)

_<_ : ℕ → ℕ → Set
x < y = ∃ k ∈ ℕ , (((𝕤 k) + x) == y)

x<y→y>x : {x y : ℕ} → x < y → y > x
x<y→y>x p = p

x<y→x<𝕤y : (x y : ℕ) → x < y → x < (𝕤 y)
x<y→x<𝕤y x y (k , [𝕤k+x=y]) = ((𝕤 k) , cong 𝕤 ((𝕤 k) + x) y [𝕤k+x=y])


x<𝕤x : (x : ℕ) → x < 𝕤 x
x<𝕤x x = (𝕫 , refl)

𝕫<𝕤x : (x : ℕ) → 𝕫 < 𝕤 x
𝕫<𝕤x 𝕫 = (𝕫 , refl)
𝕫<𝕤x (𝕤 n) = x<y→x<𝕤y 𝕫 (𝕤 n) (𝕫<𝕤x n)

𝕤x≠x-ind : (x : ℕ) → (𝕤 x) ≠ x → (𝕤 (𝕤 x)) ≠ (𝕤 x)
𝕤x≠x-ind x hyp [𝕤𝕤x=𝕤x] = hyp (cong pred (𝕤 (𝕤 x)) (𝕤 x) [𝕤𝕤x=𝕤x])

𝕤x≠x : {x : ℕ} → (𝕤 x) ≠ x
𝕤x≠x {𝕫} [𝕤𝕫=𝕫] = 𝕫≠𝕤x (==-sym [𝕤𝕫=𝕫])
𝕤x≠x {(𝕤 n)} = 𝕤x≠x-ind n (𝕤x≠x {n})

x+𝕤y=𝕤[x+y]-ind : (x y : ℕ) → (x + (𝕤 y)) == 𝕤 (x + y) → ((𝕤 x) + (𝕤 y)) == 𝕤 ((𝕤 x) + y)
x+𝕤y=𝕤[x+y]-ind x y hyp = cong 𝕤 (x + (𝕤 y)) (𝕤 (x + y)) hyp


x+𝕤y=𝕤[x+y] : (x y : ℕ) → (x + (𝕤 y)) == 𝕤 (x + y)
x+𝕤y=𝕤[x+y] 𝕫 y = refl
x+𝕤y=𝕤[x+y] (𝕤 n) y = x+𝕤y=𝕤[x+y]-ind n y (x+𝕤y=𝕤[x+y] n y)

¬[x>x]-ind : (x : ℕ) → ¬ (x > x) → ¬ ((𝕤 x) > (𝕤 x))
¬[x>x]-ind x hyp (k , [𝕤k+𝕤x=𝕤x]) = hyp (k , (cong pred (𝕤 ((𝕤 k) + x)) (𝕤 x) (==-trans (==-sym (x+𝕤y=𝕤[x+y] (𝕤 k) x)) [𝕤k+𝕤x=𝕤x])))



¬[x>x] : {x : ℕ} → ¬ (x > x)
¬[x>x] {𝕫} (k , [𝕤k+𝕫=𝕫]) = 𝕫≠𝕤x (==-sym [𝕤k+𝕫=𝕫])
¬[x>x] {𝕤 x} = ¬[x>x]-ind x (¬[x>x] {x})


data Fin : ℕ →  Set where
 zero : {n : ℕ} → Fin (𝕤 n)
 suc : {n : ℕ} → Fin n → Fin (𝕤 n)

Fin' : ℕ → Set
Fin' 𝕫 = ⊥
Fin' (𝕤 n) = ⊤ ∨ (Fin' n)



Vec' : ∀ {i} {A : Set i} → ℕ → Set i
Vec' 𝕫 = Lift ⊤
Vec' {i} {A} (𝕤 n) = A ∨ (Vec' {i} {A} n)

data _∨'_ (A : Set) (B : ∞ Set) : Set where
 inl' : A → A ∨' B
 inr' : ♭ B → A ∨' B



{-
Nat' : Set
Nat' = ♭ (⊤ ∨ (♯ Nat'))
-}

{-
Nat' : ∞ Set
Nat' = ⊤ ∨' (♯ Nat')
-}
{-
 zero₀ : Fin (𝕤 𝕫)
 
 zero₁ : Fin (𝕤 (𝕤 𝕫))
 suc₁ (zero₀)
-}

Fin'₀-is-empty : (Fin' 𝕫) is-empty
Fin'₀-is-empty p = ⊘ p

{-
zero₁ : Fin (𝕤 𝕫)
zero₁ = zero

Fin₁-singleton : (Fin (𝕤 𝕫)) is-singleton
Fin₁-singleton = (zero , f)
 where
  f : (x : Fin (𝕤 𝕫)) → zero == x
  f zero = refl
  f (suc n) = dummy
   where
    dummy
-}

{-
Fin'₁-is-singleton : (Fin' (𝕤 𝕫)) is-singleton
Fin'₁-is-singleton = ⊤-is-singleton
-}

{-
_has-listability-finite-cardinality_ : ∀ {i} → Set i → ℕ → Set i
A has-listability-finite-cardinality n = ∃ as ∈ (List A) , (((a : A) → a is-uniquely-in-the-list as) ∧ (length as == n))
-}


{-
Fin'ₖₙ : (k : Nat) → Fin' (𝕤 k)
Fin'ₖₙ 𝕫 = (inl ⊤)
-}

{-
all-Fin'ₖ : (k : Nat) → List (Fin' k)
all-Fin'ₖ 𝕫 = []
all-Fin'ₖ (𝕤 𝕫) = ((inl unit) ∷ []
-}

{-
Fin'ₖ-has-finite-listability-cardinality-k-ind :
 (k : ℕ) →
 (Fin' k) has-listability-finite-cardinality k →
 (Fin' (𝕤 k)) has-listability-finite-cardinality (𝕤 k)
Fin'ₖ-has-finite-listability-cardinality-k-ind k hyp = 
-}

{-
Fin'ₖ-has-finite-listability-cardinality-k : (k : ℕ) → (Fin' k) has-listability-finite-cardinality k
Fin'ₖ-has-finite-listability-cardinality-k 𝕫 = empty-sets-have-listability-finite-cardinality-0 Fin'₀-is-empty
Fin'ₖ-has-finite-listability-cardinality-k (𝕤 k) = 
-}

{-
zero₂ : Fin (𝕤 (𝕤 𝕫))
zero₂ = zero

one₂ : Fin (𝕤 (𝕤 𝕫))
one₂ = suc (zero₁)
-}

-- Prove that Fin 𝕫 is empty?
{-
_[_] :  
-}

{-
_[[_;_]] : ∀ {i} {A : Set i} → (xs : List A) → (k : ℕ) → ((length xs) > 𝕫) ∧ (k < (length xs)) → A
(a ∷ as) [[ 𝕫 ; hyp ]] = a

[] [ x ; hyp ] = omega (¬[x>x] (first hyp))
-}


fold-ℕ : {A : Set} → A → (ℕ → A → A) → ℕ → A
fold-ℕ z f 𝕫 = z
fold-ℕ z f (𝕤 n) = f n (fold-ℕ z f n)


fold-ℕ' : ∀ {i} {C : ℕ → Set i} → C 𝕫 → ((n : ℕ) → (C n) → (C (𝕤 n))) → (n : ℕ) → (C n)
fold-ℕ' z f 𝕫     = z
fold-ℕ' z f (𝕤 n) = f n (fold-ℕ' z f n)

eta? : {C : ℕ → Set} → (n : ℕ) → (C n) == (fold-ℕ' (C 𝕫) (λ m → (λ cm → C (𝕤 m))) n)
eta? 𝕫 = refl
eta? (𝕤 n) = refl

eta?' : {C : ℕ → Set} → (n : ℕ) → C (fold-ℕ' 𝕫 (λ m → (λ cm → (𝕤 m))) n) == fold-ℕ' (C 𝕫) (λ m → (λ cm → (C (𝕤 m)))) n
eta?' 𝕫 = refl
eta?' (𝕤 n) = refl

A,B-have-listability-finite-cardinality-k-implies-bijection-A-B :
 ∀ {i j} {A : Set i} {B : Set j} {k : ℕ} →
 A has-listability-finite-cardinality k →
 B has-listability-finite-cardinality k →
 bijection A B
A,B-have-listability-finite-cardinality-k-implies-bijection-A-B {i} {j} {A} {B} {k} (as , (f , p)) (bs , (g , q)) = (h , h-bij)
 where
  l[as]==l[bs] : length as == length bs
  l[as]==l[bs] = ==-trans p (==-sym q)

  h : A → B
  h x = y
   where
    x-unique : x is-uniquely-in-the-list as
    x-unique = f x

    x-pos : ℕ
    x-pos = (π₁ (π₁ x-unique))

    -- needs a list lookup function
    y
  h-bij



{-
TODO:
Structure
*identity types
*equivalence relations
*congruence: [x==y]→[fx==fy]
  * continuity
*rewrite-relations as equalities
*computations as paths (execution paths, yea?)


*[A==B]→[A→B]

*forall over the objects of a finite but arbitrarily large structure as a recursive AND
*exists over the objects of a finite but arbitrarily large structure as a recursive OR
*forall over the objects of an infinitely large structure as a corecursive AND?
*exists over the objects of an infinitely large structure as a corecrusive OR?
*relationship between stateful computation and logics above propositional logic.
 * need state in order to compute over arbitrarily large (or even potentially infinitely large) inputs
 * state is abstract "feedback"
 * with feedback comes metastability
 * with metastability comes undecidability
 * combinatorial circuits are stuck in propositional logic
 * predicates allow quantification over infinitely large spaces
  * any infinitely large space with a concrete representation contains arbitrarily large terms in that representation
 * ski from ##logic: trace is an operation in linear and multilinear algebra that seems to be
   related to loop f a = b where (
b,s) = f(a,s)'(feedback loop of 's') in some way
  * sum of elements along main diagonal of a square matrix
   * relationship to diagonalization proofs?
  * the trace of a matrix is the sum of the (complex) eigenvalues, and it is invariant wrt change in basis
  * golem.ph.utexas.edu/category/2007/05/linear_algebra_done_right.html
  * fixed-points and cycles in dynamic systems
  * a dynamic system is an endomorphism (obvious when you know what this means)
  * Julia sets, Fatou sets, Mandelbrot set
  * combinatorial dynamics: the study of iterating a function on a finite set back to itself.
  * for every endomorphism f on a finite set, the set {f, f², f³, ... } contains precisely one idempotent
  * every trajectory is attracted to a cycle
  * every linear endomorphism has an eigenvalue
  * "Representation of Partial Traces" Mark Bangol
  * monoidal categories
  * trace in a monoidal category, interpretation as feedback
  * infinite-dimensional Hilbert spaces
  * traced monoidal categories
  * knot theory
  * "Categorical Semantics of Digital Circuits" Dan R. Ghica, Achim Jung.
  * set of strings in a language as a free monoid on the alphabet
  * extend the monoid to a monoid action on a set Σ*×R → R
  * traced monoidal category Aut of finite automata
  * traced monoidal category Reg of regular languages
  * the definition of languages by automata is implemented by a traced monoidal functor Aut → Reg


* Real numbers as Cauchy sequences
* Real numbers as Dedekind cuts
* Continuum breaks down when trying to interpret it as points.
 * Interpret as just subdivisions of continuums all the way down, never reaching "points"?
 * Cell complexes
 * www.loa.istc.cnr.it/workshops/epinion2017/papers/JOWO_2017_paper_32.pdf
   * "Continuum as a primitive: towards an intuitionistic analysis." -Stanislaw Ambroszkiewicz
* Brouwer's notion of the continuum
* Brouwer's continuity theorem
* Brouwer's choice sequences
* https://arxiv.org/pdf/1510.02787.pdf

* equalities as computation rules



S4 modal logics
Kripke semantics

ℝⁿ equipped with p-norm has the property that each of the circle ratios C/D and A/r² attain
global minimum at p=2 (Euclidean norm)

circumference/diameter = π
area/radius² = π

π is the global minimum of these ratios under the p-norms?

further, p = 1,2,∞ (taxicab, Euclidean, and chessboard metrics) are the only values for 
which these two ratios are equal.

Only Euclidean metric is rotationally invariant
 * Only Euclidean metric has SO(3) lie group structure
   * more generally SO(n) ?
   * SO(n) the group of all rotations in ℝⁿ
 * only p = 2 has a continuous symmetry, which happens to be rotation
 * this means that for other p-norms, choice of basis matters when measuring length
 * only p = 2 makes an inner product? 
   * p = 2 is the only p-norm hat arises from an inner product
 * Noether's theorem; conservation of angular momentum
   * distance & speed must be rotation invariant
   * Lagrangians & action
Algebraic completeness of the complex numbers (i.e. fundamental theorem of algebra)
Euclidean metric the only inner product on ℝ² up to scaling?
Embedding of grid metric into Euclidean metric
Continuous compounding and the definition of e
Euler's identity and continuous compounding at imaginary rates
Euler's identity under different p-norms?
e^π = (e^(iπ))^(-i) = (-1)ⁱ
Since -i is algebraic but not rational, e^π is transcendental.
Gelfond-Schneider theorem:
* if a and b are algebraic numbers, with a² ≠ a, and b irrational, then
  any aᵇ is transcendental.

Infinite limits




* Ordinal numbers


* W-types
* Inductive types
* Induction-recursion
* Induction-induction
* Mutual induction
* Strong induction
* Transfinite induction



* Structure identity principle
* Principle of invariance
* Univalence axiom
* Missing computational interpretation of HoTT

* Path transport

* Information theory
* Algorithmic randomness



*diagonalization
*Godel's incompleteness
*Halting problem
*Tarski's undefinability
*Rice's theorem
*uncountability of the reals
*Lawvere's theorem


*can't prove induction rule for church/BB-encoded Nats?
*only used where it "makes sense" like in System F
*breaks down for dependent types, why?

*


*extensional equality

*continuous functions
  * congruence
  * recursion

*path spaces
*inverses
*homotopy fibers
*fiber bundles
*fibrations
*Dedekind-infinite sets
*Dedekind-finite sets
*Kuratowski finiteness
*Subfiniteness
*Listability finiteness
*Listability cardinality
*Lists with no repeats modulo permuations == sets

*bijection -> inverses
*inverses -> bijection


*parametricity
*(A : Set) -> A -> A should only have one member, at least up to extensional equality.

*Relationship between demorgan's, law of non-contradiction, and law of excluded middle:
 law of non-contradiction: ¬ (A ∧ ¬ A)
 demorgans : ¬ (A ∧ B) = (¬ A) ∧ (¬ B)
 demorgans 2 : ¬ (A ∨ B) = (¬ A) ∧ (¬ B)
 law of excluded middle : A ∨ ¬ A
 law of excluded middle revised: ¬ (¬ A ∧ ¬ (¬ A))
 
 ¬ (A ∧ ¬ A) = (¬ A ∨ ¬ (¬ A))
 
 Π(P : Prop) . ¬¬(P ∈ {⊥ , ⊤})
 Π(P : Prop) . ¬¬(P ∨ ¬P)

propositional truncation
quotient types
higher inductive types
algebra of data-types
how to get from lists to sets (i.e. removing ordering & repetition of elements)
can use postulates to specify the higher identities that form higher-inductive types
 * can use --rewriting to specify the computation rules on them



isProp A = ∀ (x y : A) → x == y
isSet A = ∀ (x y : A) → isProp (x == y)

after ¬, bishop, kuratowski, and sub-finiteness all coincide

so e.g. LEM is also equivalent to isBishopFinite(Prop)
so if we had say isKuratowskiFinite(Prop) then we would have ¬¬isKuratowskiFinite(Prop)
so ¬¬isBishopFinite(Prop), so ¬¬LEM
so, e.g., apparently if there is some Q : Prop so that Pi (P : Prop), || P ∨ ¬ P ∨ (P = Q)||, then ¬¬LEM
and this still holds if we use any finite number of Q_i



Levels
* similarities between delay/force & lift/lower
* level-polymorphic self-application
* level-polymorphic Y-combinator
* recursion and meta-levels
* set-levels and meta-levels
* constructors must be injections
  * and non-overlapping
  * because by pattern-matching on constructors we can send terms build from different constructors
    to different return values
  * but if two values built up differently from the constructors are considered to be equal, then
    congruence forces the return values to be equal, even though we assumed that we mapped them
    to different return values, a contradiction.
  * solutions:
    * a) do something besides simple case-matching on constructors
    * b) make sure constructors are non-overlapping injections
   

Brown-Palsberg self-interpretation

functors
natural transformations
adjoint functors
F-algebras
initial algebras
terminal coalebgras

heyting algebras
boolean algebras
filters
ultrafilters
maximal ideals
ultrafilter lemma
stone spaces
prime element
irreducible element

realizability
Harrop formuals
hereditary harrop formulas


principle of explosion
definition of "omega ()"

False as product (intersection) of all statements in the space
 * principle of explosion follows directly
True as sum (union) of all statements in the space


peirce's law







Visualization:
---------------------------------------
Syntax trees of terms
Syntax trees collapse to nodes in a graph
The edges in this graph are identities between nodes
Higher identities are edges between edges (maybe surfaces, etc..)
Hover over nodes to reveal their details
Propositional equality encapsulates beta/eta/cong1/cong2/xi, which
 gives the fundamental equational and computational theory of the
 lambda calc.
In HoTT, path spaces are kind of the fundamental structure.
Relate type-families to their deciders 

-}
