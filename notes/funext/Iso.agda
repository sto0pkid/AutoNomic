module Iso where

data _==_ {A : Set} (x : A) : A → Set where
 refl : x == x

data Nat : Set where
 zero : Nat
 suc : Nat → Nat

data Nat' : Set where
 zero' : Nat'
 suc' : Nat' → Nat'




_+_ : Nat → Nat → Nat
zero + y = y
(suc x) + y = suc (x + y)

_+'_ : Nat' → Nat' → Nat'
zero' +' y = y
(suc' x) +' y = suc' (x +' y)

{-
There is a trivial isomorphism between <Nat,zero,suc,+> and <Nat',zero',suc',+'>

iso Nat --> Nat'
iso zero --> zero'
iso suc --> suc'
iso _+_ --> _+'_

iso Nat == Nat', check
iso zero == zero', check
(x y : Nat) -> suc x == y -> (iso suc) (iso x) == (iso y)), check
(x y z : Nat) -> x + y == z -> (iso x) (iso +) (iso y) == (iso z), check

Structure is preserved across the mapping, and it trivially invertible


Now look what we can do based on this isomorphism:
-}



0+x==x : (x : Nat) → (zero + x) == x
0+x==x x = refl


0'+x'==x' : (x : Nat') → (zero' +' x) == x
0'+x'==x' x = refl


==-trans' : {A : Set} {x y z : A} → x == y → y == z → x == z
==-trans' refl p = p

{-
It doesn't suffice to just substitute Nat for Nat', we have to
substitute Nat for Nat', zero for zero', suc for suc', and + for +',
throughout the proposition and proof.

That was kind of trivial though so let's look at something more
complicated:
-}

Nat'' : Set → Set
Nat'' A = A → (A → A) → A

zero'' : {A : Set} → Nat'' A
zero'' {A} z f = z

suc'' : {A : Set} → Nat'' A → Nat'' A
suc'' {A} n z f = f (n z f)

one'' : {A : Set} → Nat'' A
one'' = suc'' zero''

one''-def : {A : Set} → (z : A) → (s : A → A) → one'' {A} == (λ z s → s z)
one''-def {A} z s = refl

+'' : {A : Set} → Nat'' A → Nat'' A → Nat'' A
+'' x y z f = x (y z f) f



{-
Ok, quite a bit different from Nat and Nat', on the face of it, but then:

Forall A : Set :

iso Nat --> Nat'' A
iso zero --> zero'' {A}
iso suc --> suc'' {A}
iso _+_ --> _+''_ {A}

iso Nat == Nat'' {A}, check
iso zero == zero'' {A}, check
(x y : Nat) -> suc x == y -> (iso suc) (iso x) == (iso y)), check
(x y z : Nat) -> x + y == z -> (iso x) (iso +) (iso y) == (iso z), check


-}



zero''+one''==one'' : {A : Set} → (+'' {A} zero'' one'') == one''
zero''+one''==one'' {A} = refl




{-
Sure enough, if we use the isomorphism to substitute throughout a proof that only
uses the operations & relations in the signatures that are related by the isomorphism,
we get another true statement:
-}
0''+''x==x : {A : Set} → (x : Nat'' A) → (+'' {A} zero'' x) == x
0''+''x==x x = refl


{-
This might not work in general in Agda, but the fact that it *should* work in general in logic
is the point.

Substitution of equals for equals in proofs should be restricted such that you can only do this
when that proof is restricted to just using the operations/relations in that signature (or
other operations/relations derived solely from these). 

To perform the substitution based on an equality given by an isomorphism, you substitute the entire
signatures that were related by the isomorphism, not just the carrier set.

That's more or less my informal description of how I would attempt a computational interpretation
of "signature-restricted univalence", and is also my informal description of how I would control
the "showing vs. hiding of structure". Structure of the carrier set is hidden or revealed by the
rest of the signature.

Extensional equality of functions works for proofs of implications when the signature is
<implication_proofs_carrier_set, modus_ponens>

We can have function extensionality under this signature, we can't have it under a signature
that allows you to "use"/"talk about" the intensional properties of the objects in
implication_proofs_carrier_set.

@ mietek: I was not disagreeing about the need for showing vs. hiding *proof structure* in particular, 
nor claiming that my notions here give any indication about the appropriate way to show vs. hide
the structure within proofs that would allow us to reason about their complexity, what I was rather
saying was that I see this fitting into the broader picture of signature-restricted univalence and
full-signature substitution, in the sense that once we do have the appropriate mechanism for talking
about proof-structure internally, that "should" just be able to correspond to modifying the signature on
implication_proofs_carrier_set, so that we can have both the funext stuff (under the signatures where 
it's appropriate) along with the ability to talk about the intensional properties of functions (under
the signatures where it's appropriate), without them clashing with each other (because they're restricted
to the signatures where they actually make sense).




-}



{-
This isn't a great example, for many reasons, but look how we wouldn't be able
to simply transport this proof to a proof about Nat under this signature, because
we're using "intensional" properties of our representation of the Nats that break
the signature:
-}

break-the-signature : {A : Set} → Nat'' A → A → (A → A) → (A → A → A) → A
break-the-signature x z s + = x z s

{-
It's not so straightforward (if it even makes sense) to transport this proof into one
about Nat because Nats aren't functions, we can't apply them like we can apply Nat''s

-}
