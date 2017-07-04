module basics where

{-
  To use universe-polymorphism you have to bind BUILTIN LEVEL to a postulated
  type to serve as Level:
-}

postulate
 Level : Set
 lzero : Level
 lsuc  : (l : Level) -> Level
 lmax  : (l1 l2 : Level) -> Level

-- MAlonzo compiles Level to (). This should be fine because... 
-- ... why is this fine, again?

{-# COMPILED_TYPE Level ()            #-}
{-# COMPILED      lzero ()            #-}
{-# COMPILED      lsuc  (\_ -> ())    #-}
{-# COMPILED      lmax  (\_ _ -> ())  #-}


{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC  lsuc  #-}
{-# BUILTIN LEVELMAX  lmax  #-}


id : {n : Level} -> {A : Set n} -> A -> A
id {n} {A} x = x

comp : 
 {a b c : Level} {A : Set a} {B : Set b} {C : Set c} -> 
 (B -> C) -> (A -> B) -> (A -> C)
comp {n} {A} {B} {C} g f a = g (f a)

{-
  To use Agda's sizes for sized-types you have to bind BUILTIN SIZE to a postulated
  type to serve as Size:
-}
postulate
 Size : Set
 ssuc : Size -> Size
 sinf : Size

{-# BUILTIN SIZE    Size #-}
{-# BUILTIN SIZESUC ssuc #-}
{-# BUILTIN SIZEINF sinf #-}




-- Basic propositions:

data False : Set where
False-elim : {w : Level} -> {Whatever : Set w} → False → Whatever
False-elim ()

data True : Set where
 I : True

Not : {n : Level} -> (A : Set n) -> Set n
Not A = (A -> False) 

data Or {m n : Level} (A : Set m) (B : Set n) : Set (lmax m n) where
 inl : A -> Or A B
 inr : B -> Or A B

record And {m n : Level} (A : Set m) (B : Set n) : Set (lmax m n) where
 field
  andFst : A
  andSnd : B

open And public

Pi : {a b : Level} -> (A : Set a) -> (B : A -> Set b) -> Set (lmax a b)
Pi A B = (a : A) -> B a

record Sigma {a b : Level} (A : Set a) (B : A -> Set b) : Set (lmax a b) where
 field
  proj1 : A
  proj2 : B proj1

open Sigma public

not_or_imp_not_and : {m n : Level} -> {A : Set} -> {B : Set} -> Not (Or A B) -> Not (And A B)
not_or_imp_not_and not_orAB andAB = not_orAB (inl (andFst andAB))

and-imp-or : {m n : Level} {A : Set} {B : Set} -> And A B -> Or A B
and-imp-or {m} {n} {A} {B} andAB = inl (andFst andAB)

and-imp-or2 : {m n : Level} {A : Set} {B : Set} -> And A B -> Or A B
and-imp-or2 {m} {n} {A} {B} andAB = inr (andSnd andAB) 

-- Basic implications:

t_imp_t : True -> True
t_imp_t = id

t_imp_t2 : True -> True
t_imp_t2 I = I

f_imp_f : False -> False
f_imp_f = id

f_imp_t : False -> True
f_imp_t f = False-elim f

not_t_imp_f : (True -> False) -> False
not_t_imp_f tf = tf I



-- Booleans

data Bool : Set where
 true : Bool
 false : Bool

{-# BUILTIN BOOL Bool   #-}
{-# BUILTIN TRUE true   #-}
{-# BUILTIN FALSE false #-}

IsTrue : Bool -> Set
IsTrue true = True
IsTrue false = False

b_not : Bool -> Bool
b_not true = false
b_not false = true

b_and : Bool -> Bool -> Bool
b_and true true = true
b_and true false = false
b_and false true = false
b_and false false = false

b_or : Bool -> Bool -> Bool
b_or true true = true
b_or true false = true
b_or false true = true
b_or false false = false


--Identity types


data Id {a : Level} {A : Set a} : A ->  A -> Set a where
 refl : (x : A) -> Id x x



data Id2 {a : Level} {A : Set a} (x : A) : A -> Set a where
 refl2 : Id2 x x

{-# BUILTIN EQUALITY Id2     #-}
{-# BUILTIN REFL     refl2   #-} 


Id_AB_imp_A_imp_B : {n : Level} {A B : Set n} -> Id A B -> A -> B
Id_AB_imp_A_imp_B {n} {A} {.A} (refl .A) x = x

not_True_eq_False : Not (Id True False)
not_True_eq_False p = Id_AB_imp_A_imp_B p I

Id_refl : {a : Level} {A : Set a} (x : A) -> Id x x
Id_refl {a} {A} = refl

Id_sym : {a : Level} {A : Set a} {x y : A} -> Id x y -> Id y x
Id_sym (refl a) = refl a

Id_trans : {a : Level} {A : Set a} {x y z : A} -> Id x y -> Id y z -> Id x z
Id_trans (refl a) (refl .a) = refl a

Id_trans2 : {a : Level} {A : Set a} {x y z : A} -> Id x y -> Id y z -> Id x z
Id_trans2 (refl a) e = e

transport : {m n : Level} {A : Set m} {x : A} {y : A} (p : Id x y) -> (P : A -> Set n) -> P x -> P y
transport {m} {n} {A} {a} {.a} (refl .a) P pa = pa  

functions_respect_identity : {m n : Level} {A : Set m} {B : Set n} (f : A -> B) -> (x : A) -> (y : A) -> (p : Id x y) -> Id (f x) (f y)
functions_respect_identity {m} {n} {A} {B} f a .a (refl .a) = refl (f a)

pis_respect_identity : {m n : Level} {A : Set m} {B : A -> Set n} (f : Pi A B) -> (x : A) -> (y : A) -> (p : Id x y) -> Id (transport p B (f x)) (f y)
pis_respect_identity {m} {n} {A} {B} f a .a (refl .a) = (refl (f a))

not_true_eq_false : Not (Id true false)
not_true_eq_false p = not_True_eq_False (functions_respect_identity IsTrue true false p)

{- need to figure out the pattern such that we can always use the Pi form
   instead of the function form, when applicable. this is a situation where
   it's applicable
-}


{- 
not_true_eq_false2 : Not (Id true false)
not_true_eq_false2 p = not_True_eq_False (pis_respect_identity IsTrue true false p)

-}


neq-a-nota : (a : Bool) -> (Id a (b_not a)) -> False
neq-a-nota true p = not_True_eq_False (functions_respect_identity IsTrue true false p)
neq-a-nota false p = not_True_eq_False (Id_sym (functions_respect_identity IsTrue false true p)) 

--This time without destructing in the pattern-matching. Can it be done?
{-
neq-a-nota2 : (a : Bool) -> (Id a (b_not a)) -> False
neq-a-nota2 a p = ?
-}

--This time using Pi's instead of functions
{-
neq-a-nota3 : (a : Bool) -> (Id a (b_not a)) -> False
neq-a-nota3 true p = not_True_eq_False (pis_respect_identity IsTrue true false p)
neq-a-nota3 false p = not_True_eq_False (Id_sym (pis_respect_identity IsTrue false true p))

-}


data Nat : Set where
 zero : Nat
 suc : Nat -> Nat

{-
  We already know this should work because of functions_repect_identity, but let's
  just make sure it applies to constructors:
-}

suc-respects-identity : (m n : Nat) -> Id m n -> Id (suc m) (suc n)
suc-respects-identity m n p = functions_respect_identity suc m n p


fiber : {m n : Level} {A : Set m} {B : Set n} (f : A -> B) -> (b : B) -> Set (lmax m n)
fiber {m} {n} {A} {B} f b = Sigma A \{a -> Id (f a) b} 

Fibers : {m n : Level} {A : Set m} {B : Set n} (f : A -> B) -> Set (lmax m n)
Fibers {m} {n} {A} {B} f = Sigma B \{b -> fiber f b}

NoFibers : {m n : Level} {A : Set m} {B : Set n} (f : A -> B) -> Set (lmax m n)
NoFibers {m} {n} {A} {B} f = Sigma B \{b -> (fiber f b) -> False}
 
fibrate : 
 {m n : Level} {A : Set m} {B : Set n} ->
 (f : A -> B) -> A -> Fibers f
fibrate {m} {n} {A} {B} f a = 
 record { 
  proj1 = f a ; 
  proj2 = record {
   proj1 = a ;
   proj2 = refl (f a)
  }
 }

unfibrate : 
 {m n : Level} {A : Set m} {B : Set n} ->
 (f : A -> B) -> Fibers f -> A
unfibrate {m} {n} {A} {B} f fib = proj1 (proj2 fib)
  
fib-unfib-is-id : 
 {m n : Level} {A : Set m} {B : Set n} ->
 (f : A -> B) -> (a : A) -> Id a (unfibrate f (fibrate f a))
fib-unfib-is-id {m} {n} {A} {B} f a = refl a

fib-unfib-is-id-strong : 
 {m n : Level} {A : Set m} {B : Set n} ->
 (f : A -> B) -> Id id (comp (unfibrate f) (fibrate f))
fib-unfib-is-id-strong {m} {n} {A} {B} f = refl \{a -> a}


injection : {m n : Level} {A : Set m} {B : Set n} (f : A -> B) -> Set (lmax m n)
injection {m} {n} {A} {B} f = (a1 a2 : A) -> Id (f a1) (f a2) -> Id a1 a2

surjection : {m n : Level} {A : Set m} {B : Set n} (f : A -> B) -> Set (lmax m n)
surjection {m} {n} {A} {B} f = (b : B) -> fiber f b 


bijection : {m n : Level} {A : Set m} {B : Set n} (f : A -> B) -> Set (lmax m n)
bijection {m} {n} {A} {B} f = And (injection f) (surjection f) 

id-is-injection : {n : Level} {A : Set n} -> injection (id { n } { A })
id-is-injection {n} {A} = \{a1 a2 p -> p}

id-is-surjection : {n : Level} {A : Set n} -> surjection (id { n } { A })
id-is-surjection {n} {A} = \{a -> record { proj1 = a; proj2 = (refl a)}}

id-is-bijection : {n : Level} {A : Set n} -> bijection (id { n } { A })
id-is-bijection {n} {A} = record { andFst = id-is-injection ; andSnd = id-is-surjection }


unfibrate-is-surjection :
 {m n : Level} {A : Set m} {B : Set n} ->
 (f : A -> B) -> surjection (unfibrate f)
unfibrate-is-surjection {m} {n} {A} {B} f a = 
 record {
  proj1 = record {
   proj1 = f a;
   proj2 = record {
    proj1 = a;
    proj2 = refl (f a)
   }
  };
  proj2 = refl a
 }
 
ex-surjA1-imp-A : {m : Level} {A : Set m} {f : A -> True} -> surjection f -> A
ex-surjA1-imp-A {m} {A} {f} surj = proj1 (surj I)

ex-surjA1-imp-AB-imp-B :
 {m n : Level} {A : Set m} {B : Set n} ->
 {a1 : A -> True} -> surjection a1 ->
 (ab : A -> B ) -> B
ex-surjA1-imp-AB-imp-B {m} {A} {B} {a1} surj ab = ab (proj1 (surj I))

ex-surjA1-imp-AB-imp-BA :
 {m n : Level} {A : Set m} {B : Set n} ->
 {a1 : A -> True} -> surjection a1 ->
 (ab : A -> B) -> B -> A
ex-surjA1-imp-AB-imp-BA {m} {A} {B} {a1} surj ab b = proj1 (surj I)

ex-surjA1-imp-AB-imp-FibersAB :
 {m n : Level} {A : Set m} {B : Set n} ->
 {a1 : A -> True} -> surjection a1 -> 
 (ab : A -> B) -> Fibers ab
ex-surjA1-imp-AB-imp-FibersAB {m} {n} {A} {B} {a1} surj ab =
 record {
  proj1 = ab (proj1 (surj I));
  proj2 = record {
   proj1 = proj1 (surj I);
   proj2 = refl (ab (proj1 (surj I)))
  }
 }


ex-surjA1-imp-AB-imp-B-to-FibersAB :
 {m n : Level} {A : Set m} {B : Set n} ->
 {a1 : A -> True} -> surjection a1 -> 
 (ab : A -> B) -> B -> Fibers ab
ex-surjA1-imp-AB-imp-B-to-FibersAB {m} {n} {A} {B} {a1} surj ab b =
 ex-surjA1-imp-AB-imp-FibersAB surj ab



data Maybe {n : Level} (A : Set n) : Set n where
 Just : (a : A) -> Maybe A  
 Nothing : Maybe A


 

-- Homogeneous binary relations : 
{-
  Should probably make heterogeneous n-ary relations instead and define
  homogeneous binary relations as a special case.
-}


relation : {n : Level} {A : Set n} -> Set n
relation {n} {A} = A -> A -> Bool

{-
  Two elements either are or aren't related; not both.
  For any pair of elements (a1,a2), we know that a relation will return either
  true or false; not both, and not neither. We know this because the relation is
  given as a function, and we know how functions behave, but let's go ahead and show
  how to demonstrate that relations actually are well-defined:
-}
relations-are-well-defined : 
  {n : Level} {A : Set n} -> (R : relation { n } { A }) ->
  (a1 a2 : A) -> (b : Bool) -> Id (R a1 a2) b -> (Id (R a1 a2) (b_not b) -> False)
relations-are-well-defined {n} {A} R a1 a2 b pb pnb = neq-a-nota b (Id_trans (Id_sym pb) pnb)

--Reflexivity
IsReflexive : {n : Level} {A : Set n} -> relation { n } { A } -> Set n
IsReflexive {n} {A} R = (a : A) -> Id (R a a) true

IsIrreflexive : {n : Level} {A : Set n} -> relation { n } { A } -> Set n
IsIrreflexive {n} {A} R = (a : A) -> Id (R a a) false


--Symmetry
IsSymmetric : {n : Level} {A : Set n} -> relation { n } { A } -> Set n
IsSymmetric {n} {A} R = (a b : A) -> Id (R a b) true -> Id (R b a) true

IsAntisymmetric : {n : Level} {A : Set n} -> relation { n } { A } -> Set n
IsAntisymmetric {n} {A} R = (a b : A) -> Id (R a b) true -> Id (R b a) true -> Id a b

IsAsymmetric : {n : Level} {A : Set n} -> relation { n } { A } -> Set n
IsAsymmetric {n} {A} R = (a b : A) -> Id (R a b) true -> Id (R b a) false


--Transitivity
IsTransitive : {n : Level} {A : Set n} -> relation { n } { A } -> Set n
IsTransitive {n} {A} R = (a b c : A) -> Id (R a b) true -> Id (R b c) true -> Id (R a c) true


--Specific relations
IsPreorder : {n : Level} {A : Set n} -> relation { n } { A } -> Set n
IsPreorder {n} {A} R = And (IsReflexive R) (IsTransitive R)

IsPartialOrder : {n : Level} {A : Set n} -> relation { n } { A } -> Set n
IsPartialOrder {n} {A} R = And (IsReflexive R) (And (IsAntisymmetric R) (IsTransitive R))

IsEquivalence : {n : Level} {A : Set n} -> relation { n } { A } -> Set n
IsEquivalence {n} {A} R = And (IsReflexive R) (And (IsSymmetric R) (IsTransitive R))


{- 
   obviously equivalences & partial orders are preorders, but let's demonstrate it
   anyway
-}

equivalences-are-preorders : 
  {n : Level} {A : Set n} -> (R : relation { n } { A }) -> 
  IsEquivalence R -> IsPreorder R
equivalences-are-preorders {n} {A} R eq = 
  record { 
    andFst = andFst eq; 
    andSnd = andSnd (andSnd eq)
  }

partialorders-are-preorders :
  {n : Level} {A : Set n} -> (R : relation { n } { A }) -> 
  IsPartialOrder R -> IsPreorder R
partialorders-are-preorders {n} {A} R eq = 
  record {
    andFst = andFst eq;
    andSnd = andSnd (andSnd eq)
  }

FuncId : {m n : Level} {A : Set m} {B : Set n} (f g : A -> B) -> Set (lmax m n)
FuncId {m} {n} {A} {B} f g = (a : A) -> Id (f a) (g a)


eta : {m n : Level} {A : Set m} {B : Set n} -> (f : A -> B) -> FuncId f (\{x -> f x})
eta {m} {n} {A} {B} f a = refl (f a)

eta2 : {m n : Level} {A : Set m} {B : Set n} -> (f : A -> B) -> Id2 f (\{a -> f a})
eta2 {m} {n} {A} {B} f = refl2

eta3 : {m n : Level} {A : Set m} {B : Set n} -> (f : A -> B) -> Id f (\{a -> f a})
eta3 {m} {n} {A} {B} f = refl f



function-composition-is-associative : 
  {n : Level} {A B C D : Set n} ->
  (f : A -> B) -> (g : B -> C) -> (h : C -> D) ->
  FuncId (comp h (comp g f)) (comp (comp h g) f)
function-composition-is-associative {n} {A} {B} {C} {D} f g h a = refl (h (g (f a)))

function-composition-is-associative2 : 
  {n : Level} {A B C D : Set n} -> 
  (f : A -> B) -> (g : B -> C) -> (h : C -> D) ->
  Id2 (comp h (comp g f)) (comp (comp h g) f)
function-composition-is-associative2 {n} {A} {B} {C} {D} f g h = refl2
  
function-composition-is-associative3 :
  {n : Level} {A B C D : Set n} ->
  (f : A -> B) -> (g : B -> C) -> (h : C -> D) ->
  Id (comp h (comp g f)) (comp (comp h g) f)
function-composition-is-associative3 {n} {A} {B} {C} {D} f g h = refl (\{a -> h (g (f a))})

{-
Interactive theorem proving version:

function-composition-is-associative4 :
  {n : Level} {A B C D : Set n} ->
  (f : A -> B) -> (g : B -> C) -> (h : C -> D) ->
  Id (comp h (comp g f)) (comp (comp h g) f)
function-composition-is-associative4 {n} {A} {B} {C} {D} f g h = refl ?

Then type C-c C-l to load the "?" as a goal
Then type C-c C-s to solve the goal, and we get:

-}


function-composition-is-associative4 :
  {n : Level} {A B C D : Set n} ->
  (f : A -> B) -> (g : B -> C) -> (h : C -> D) ->
  Id (comp h (comp g f)) (comp (comp h g) f)
function-composition-is-associative4 {n} {A} {B} {C} {D} f g h = refl (comp h (comp g f))

{-
  I could have sworn that when I tried to type in this proof manually that it
  didn't pass type-check, but I haven't been able to reproduce this behavior
  since then. Maybe somebody else can reproduce it?
-}

weak-f-is-g-imp-weak-fib-unfib-f-is-fib-unfib-g :
 {m n : Level} {A : Set m} {B : Set n} ->
 (f g : A -> B) -> Id (comp (unfibrate f) (fibrate f)) (comp (unfibrate g) (fibrate g))
weak-f-is-g-imp-weak-fib-unfib-f-is-fib-unfib-g {m} {n} {A} {B} f g = 
 Id_trans (Id_sym (fib-unfib-is-id-strong f)) (fib-unfib-is-id-strong g)   

f1-is-f2-imp-gf1-is-gf2 :
 {a b c : Level} {A : Set a} {B : Set b} {C : Set c} ->
 (f1 f2 : A -> B) -> Id f1 f2 -> (g : B -> C) ->
 Id (comp g f1) (comp g f2)
f1-is-f2-imp-gf1-is-gf2 {a} {b} {c} {A} {B} {C} f .f (refl .f) g =
 refl (comp g f)

f1-is-f2-imp-f1g-is-f2g :
 {a b c : Level} {A : Set a} {B : Set b} {C : Set c} ->
 (f1 f2 : B -> C) -> Id f1 f2 -> (g : A -> B) ->
 Id (comp f1 g) (comp f2 g)
f1-is-f2-imp-f1g-is-f2g {a} {b} {c} {A} {B} {C} f .f (refl .f) g =
 refl (comp f g)





{-
 
only-False-is-not-implied : 
  {n : Level} {A : Set n} {B : Set} -> 
  Not (A -> B) -> And (Not (Id A False)) (Id B False)
only-False-is-not-implied {n} {A} {B} notAB = 
  record { 
    andFst = ; 
    andSnd = 
  } 

-}

bool-LEM : (b : Bool) -> Or (Id b true) (Id b false)
bool-LEM true = inl (refl true)
bool-LEM false = inr (refl false)

{- 
  Is there anyway to do this without pattern-matching?
-}

bool-consistency : (b : Bool) -> And (Id b true) (Id b false) -> False
bool-consistency b inc = 
  not_true_eq_false (
   Id_trans (Id_sym (andFst inc)) (andSnd inc)
  )


eq-funcs-same-arg-same-result : 
  {m n : Level} {A : Set m} {B : Set n} ->
  (f g : A -> B) -> (h : Id f g) -> (a : A) -> 
  Id (f a) (g a)
eq-funcs-same-arg-same-result {m} {n} {A} {B} f .f (refl .f) a = refl (f a)

eq-funcs-same-arg-same-result2 : 
 {m n : Level} {A : Set m} {B : Set n} ->
 (f g : A -> B) -> (hom : Id f g) -> (a1 a2 : A) -> Id a1 a2 -> Id (f a1) (g a2)
eq-funcs-same-arg-same-result2 {m} {n} {A} {B} f .f (refl .f) a .a (refl .a) = refl (f a)

eq-pis-same-arg-same-result :
  {m n : Level} {A : Set m} {B : A -> Set n} ->
  (f g : Pi A B) -> (h : Id f g) -> (a : A) ->
  Id (f a) (g a)
eq-pis-same-arg-same-result {m} {n} {A} {B} f .f (refl .f) a = refl (f a)


id-is-comp-g-f-imp-surj-g :
 {m n : Level} {A : Set m} {B : Set n} ->
 (f : A -> B) -> (g : B -> A) ->
 Id id (comp g f) -> surjection g
id-is-comp-g-f-imp-surj-g {m} {n} {A} {B} f g p a = 
 record {
  proj1 = f a;
  proj2 = Id_sym (eq-funcs-same-arg-same-result id (comp g f) p a)
 }


id-is-comp-g-f-imp-inj-f :
 {m n : Level} {A : Set m} {B : Set n} ->
 (f : A -> B) -> (g : B -> A) ->
 Id id (comp g f) -> injection f

id-is-comp-g-f-imp-inj-f {m} {n} {A} {B} f g hom a1 a2 p = 
 Id_trans
  (Id_trans 
   (eq-funcs-same-arg-same-result id (comp g f) hom a1)
   (functions_respect_identity g (f a1) (f a2) p)
  )
  (Id_sym (eq-funcs-same-arg-same-result id (comp g f) hom a2))


fibrate-is-injection :
 {m n : Level} {A : Set m} {B : Set n} ->
 (f : A -> B) -> injection (fibrate f)
fibrate-is-injection {m} {n} {A} {B} f = 
 id-is-comp-g-f-imp-inj-f (fibrate f) (unfibrate f) (fib-unfib-is-id-strong f)


 
unfibrate-is-surjection2 :
 {m n : Level} {A : Set m} {B : Set n} ->
 (f : A -> B) -> surjection (unfibrate f)
unfibrate-is-surjection2 {m} {n} {A} {B} f =
 id-is-comp-g-f-imp-surj-g (fibrate f) (unfibrate f) (fib-unfib-is-id-strong f)


inj-trans :
 {a b c : Level} {A : Set a} {B : Set b} {C : Set c} ->
 (f : A -> B) -> injection f ->
 (g : B -> C) -> injection g ->
 injection (comp g f)
inj-trans {a} {b} {c} {A} {B} {C} f inj_f g inj_g a1 a2 p = 
 inj_f a1 a2 (inj_g (f a1) (f a2) p)

inj-refl :
 {a : Level} {A : Set a} -> Sigma (A -> A) \{f -> injection f}
inj-refl {a} {A} = 
 record {
  proj1 = id;
  proj2 = id-is-injection
 }

surj-refl :
 {a : Level} {A : Set a} -> Sigma (A -> A) \{f -> surjection f}
surj-refl {a} {A} =
 record {
  proj1 = id;
  proj2 = id-is-surjection
 }

bij-refl :
 {a : Level} {A : Set a} -> Sigma (A -> A) \{f -> bijection f}
bij-refl {a} {A} =
 record {
  proj1 = id;
  proj2 = id-is-bijection
 }
 
f-of-fiber-f-b-is-b : 
  {m n : Level} {A : Set m} {B : Set n} ->
  (f : A -> B) -> (b : B) -> (fib : fiber f b) ->
  Id (f (proj1 fib)) b
f-of-fiber-f-b-is-b {m} {n} {A} {B} f b fib = proj2 fib

surj-trans :
 {a b c : Level} {A : Set a} {B : Set b} {C : Set c} ->
 (f : A -> B) -> surjection f ->
 (g : B -> C) -> surjection g ->
 surjection (comp g f)
surj-trans {a} {b} {c} {A} {B} {C} f surj-f g surj-g c' =
 record {
  proj1 = proj1 (surj-f (proj1 (surj-g c')));
  proj2 = 
   Id_trans 
    (functions_respect_identity
     g
     (f (proj1 (surj-f (proj1 (surj-g c')))))
     (proj1 (surj-g c'))
     (proj2 (surj-f (proj1 (surj-g c'))))
    )
    (f-of-fiber-f-b-is-b g c' (surj-g c'))
 }


bij-trans :
 {a b c : Level} {A : Set a} {B : Set b} {C : Set c} ->
 (f : A -> B) -> bijection f ->
 (g : B -> C) -> bijection g -> 
 bijection (comp g f)
bij-trans {a} {b} {c} {A} {B} {C} f bij-f g bij-g = 
 record {
  andFst = inj-trans f (andFst bij-f) g (andFst bij-g);
  andSnd = surj-trans f (andSnd bij-f) g (andSnd bij-g)
 }



-- g is the left-inverse of f 
left-inv : {m n : Level} {A : Set m} {B : Set n} (g : B -> A) (f : A -> B) -> Set m
left-inv {m} {n} {A} {B} g f = (a : A) -> Id a ((comp g f) a)

left-inv-strong : {m n : Level} {A : Set m} {B : Set n} (g : B -> A) (f : A -> B) -> Set m
left-inv-strong {m} {n} {A} {B} g f = Id id (comp g f)

right-inv : {m n : Level} {A : Set m} {B : Set n} (g : B -> A) (f : A -> B) -> Set n
right-inv {m} {n} {A} {B} g f = (b : B) -> Id b ((comp f g) b)

right-inv-strong : {m n : Level} {A : Set m} {B : Set n} (g : B -> A) (f : A -> B) -> Set n
right-inv-strong {m} {n} {A} {B} g f = Id id (comp f g)

record iso {m n : Level} (A : Set m) (B : Set n) : Set (lmax m n) where
 field
  isoA : A -> B
  isoB : B -> A
  left : left-inv isoB isoA
  right : right-inv isoB isoA

record iso-strong {m n : Level} (A : Set m) (B : Set n) : Set (lmax m n) where
 field
  isoA : A -> B
  isoB : B -> A
  left : left-inv-strong isoB isoA
  right : right-inv-strong isoB isoA
 

left-inv-strong-imp-left-inv-weak : (m n : Level) -> Set (lsuc (lmax m n))
left-inv-strong-imp-left-inv-weak m n = 
 {A : Set m} {B : Set n} -> 
 (g : B -> A) -> (f : A -> B) ->
 left-inv-strong g f ->
 left-inv g f
prf-left-inv-strong-imp-left-inv-weak : (m n : Level) -> left-inv-strong-imp-left-inv-weak m n
prf-left-inv-strong-imp-left-inv-weak m n {A} {B} g f p a = eq-funcs-same-arg-same-result id (comp g f) p a

right-inv-strong-imp-right-inv-weak : (m n : Level) -> Set (lsuc (lmax m n))
right-inv-strong-imp-right-inv-weak m n  = 
 {A : Set m} {B : Set n} -> 
 (g : B -> A ) -> (f : A -> B) ->
 right-inv-strong g f ->
 right-inv g f
prf-right-inv-strong-imp-right-inv-weak : (m n : Level) ->  right-inv-strong-imp-right-inv-weak m n
prf-right-inv-strong-imp-right-inv-weak m n {A} {B} g f p b = eq-funcs-same-arg-same-result id (comp f g) p b


inv-strong-imp-inv-weak : (m n : Level) ->  And (left-inv-strong-imp-left-inv-weak m n) (right-inv-strong-imp-right-inv-weak m n)
inv-strong-imp-inv-weak m n = 
 record {
  andFst = prf-left-inv-strong-imp-left-inv-weak m n;
  andSnd = prf-right-inv-strong-imp-right-inv-weak m n
 }


different-fibers-different-objects :
  {m n : Level} {A : Set m} {B : Set n} -> 
  (f : A -> B) -> (b1 b2 : B) ->
  (nopath : (Id b1 b2) -> False) ->
  (a1 : fiber f b1) -> (a2 : fiber f b2) ->
  Id (proj1 a1) (proj1 a2) -> False
different-fibers-different-objects {m} {n} {A} {B} f b1 b2 nopath a1 a2 p =
  nopath 
    (Id_trans
      (Id_trans
        (Id_sym (proj2 a1))
        (functions_respect_identity f(proj1 a1) (proj1 a2) p)
      )
      (proj2 a2)
    )

--functions from False to True are injections 
F-T-is-injection : (f : False -> True) -> injection f
F-T-is-injection f a1 a2 p = False-elim a1

--functions from False to True are not surjections
F-T-not-surjection : (f : False -> True) -> surjection f -> False
F-T-not-surjection f surj = proj1 (surj I)


--These definitions have to return universe-polymorphic function types
--which means their return type is actually not Set (lmax m n), but SetOmega
--which is not allowed in Agda.
--Why?
{-
epimorphic : {m n : Level} {A : Set m} {B : Set n} -> (f : A -> B) -> Set (lmax m n)
epimorphic {m} {n} {A} {B} f = 
 {q : Level} {C : Set q} (g1 g2 : B -> C) -> FuncId (comp g1 f) (comp g2 f) -> FuncId g1 g2

epimorphic-strong : {m n : Level} {A : Set m} {B : Set n} -> (f : A -> B) -> Set (lmax m n)
epimorphic-strong {m} {n} {A} {B} f = 
 {q : Level} {C : Set q} (g1 g2 : B -> C) -> Id (comp g1 f) (comp g2 f) -> Id g1 g2

monomorphic : {m n : Level} {A : Set m} {B : Set n} -> (f : A -> B) -> Set (lmax m n)
monomorphic {m} {n} {A} {B} f =
 {q : Level} {C : Set q} (g1 g2 : C -> A) -> FuncId (comp f g1) (comp f g2) -> FuncId g1 g2

monomorphic-strong : {m n : Level} {A : Set m} {B : Set n} -> (f : A -> B) -> Set (lmax m n)
monomorphic-strong {m} {n} {A} {B} f = 
 {q : Level} {C : Set q} (g1 g2 : C -> A) -> Id (comp f g1) (comp f g2) -> Id g1 g2

-}  



--surjection from A to B implies injection from B to A
ex-surj-AB-imp-ex-inj-BA :
  {m n : Level} {A : Set m} {B : Set n} -> 
  (f : A -> B) -> surjection f ->
  Sigma (B -> A) injection
ex-surj-AB-imp-ex-inj-BA {m} {n} {A} {B} f surj = 
  record {
    proj1 = \{b -> proj1 (surj b)};
    proj2 = \{b1 b2 p ->
      Id_trans
        (Id_trans 
          (Id_sym (proj2 (surj b1))) 
          (functions_respect_identity f (proj1 (surj b1)) (proj1 (surj b2)) p)
        )
        (proj2 (surj b2))
    }  
  }

 
--injection from A to B doesn't imply surjection from B to A
ex-inj-AB-nimp-ex-surj-BA :
  ({m n : Level} {A : Set m} {B : Set n} ->
  (f : A -> B) -> injection f ->
  Sigma (B -> A) surjection) -> False
ex-inj-AB-nimp-ex-surj-BA hyp = proj1 (hyp f_imp_t (F-T-is-injection f_imp_t)) I

--not exists surjection A to B doesn't imply exists injection A to B
nex-surj-AB-nimp-ex-inj-AB : 
  ({m n : Level} {A : Set m} {B : Set n} ->
  ((f : A -> B) -> surjection f -> False) -> 
  Sigma (A -> B) injection) -> False
nex-surj-AB-nimp-ex-inj-AB hyp = proj1 (hyp { lzero } { lzero } {True } { False } \{f surj -> f I}) I 

--not exists injection A to B doesn't imply exists surjection A to B
nex-inj-AB-nimp-ex-surj-AB :
  ({m n : Level} {A : Set m} {B : Set n} ->
   ((f : A -> B) -> injection f -> False) ->
   Sigma (A -> B) surjection) -> False
nex-inj-AB-nimp-ex-surj-AB hyp = proj1 (hyp { lzero } { lzero } { True } { False } \{f inj -> f I}) I

{-

--exists surjection B to 1 and not-exists injection A to B implies exists surjection A to B
--intuitively: if B is not empty, and A doesn't fit in B, then A covers B with a surjection
ex-surj-B1-nex-inj-AB-imp-ex-surj-AB :
  {m n : Level} {A : Set m} {B : Set n} ->
  (f : B -> True) -> surjection f ->
  ((g : A -> B) -> injection g -> False) ->
  Sigma (A -> B) surjection
ex-surj-B1-nex-inj-AB-imp-ex-surj-AB {m} {n} {A} {B} f surj_f noinjAB =

-}


surjection-fiber-reverse :
 {m n : Level} {A : Set m} {B : Set n} ->
 (f : A -> B) -> surjection f -> 
 (b : B) -> Fibers f
surjection-fiber-reverse {m} {n} {A} {B} f surj-f b = record {proj1 = b; proj2 = surj-f b}
 

{-
--exists surjection A to 1 and exists injection A to B implies exists surjection B to A
--intuitively: if A is not empty, and A fits in B, then B covers A with a surjection

ex-surj-A1-ex-inj-AB-imp-ex-surj-BA :
  {m n : Level} {A : Set m} {B : Set n} ->
  (f : A -> True) -> surjection f ->
  (g : A -> B) -> injection g ->
  Sigma (B -> A) surjection
ex-surj-A1-ex-inj-AB-imp-ex-surj-BA {m} {n} {A} {B} f surj_f g inj_g = 
-}

-- reverse the fibers of the injection
-- map every other point in B to an arbitrary object in A
-- but how to tell Agda to do this?



{-
--exists surjection B to 1 and not-exists surjection A to B implies exists injection A to B
--intuitively: if B is not empty, and A doesn't cover B, then A fits in B
ex-surj-B1-nex-surj-AB-imp-ex-inj-AB :
  {m n : Level} {A : Set m} {B : Set n} ->
  (f : B -> True) -> surjection f ->
  ((g : A -> B) -> surjection g -> False) ->
  Sigma (A -> B) injection
ex-surj-B1-nex-surj-AB-imp-ex-inj-AB {m} {n} {A} {B} f surj_f nosurjAB =

-}



{-
--injection A to B, injection B to A implies bijection A to B
inj-antisym :
  {m n : Level} {A : Set m} {B : Set n} ->
  (f : A -> B) -> injection f ->
  (g : B -> A) -> injection g ->
  bijection f
inj-antisym {m} {n} {A} {B} f inj-f g inj-g =
-}

{-
inj-antisym2 :
 {m n : Level} {A : Set m} {B : Set n} ->
 (f : A -> B) -> injection f ->
 (g : B -> A) -> injection g -> 
 bijective A B
inj-antisym2 {m} {n} {A} {B} f inj-f g inj-g =
 record {
  proj1 = 
 }
-}



injective : {m n : Level} (A : Set m) (B : Set n) -> Set (lmax m n)
injective {m} {n} A B = Sigma (A -> B) \{f -> injection f}

surjective : {m n : Level} (A : Set m) (B : Set n) -> Set (lmax m n)
surjective {m} {n} A B = Sigma (A -> B) \{f -> surjection f}

bijective : {m n : Level} (A : Set m) (B : Set n) -> Set (lmax m n)
bijective {m} {n} A B = And (injective A B) (surjective A B)

fiber-inj-b-is-unique :
 {m n : Level} {A : Set m} {B : Set n} ->
 (f : A -> B) -> injection f -> 
 (b : B) -> (fib1 : fiber f b) -> (fib2 : fiber f b) ->
 Id (proj1 fib1) (proj1 fib2)
fiber-inj-b-is-unique {m} {n} {A} {B} f inj-f b fib1 fib2 =
 inj-f (proj1 fib1) (proj1 fib2) (Id_trans (proj2 fib1) (Id_sym (proj2 fib2)))


surj-inj-imp-ex-a1-a2-where-surj-a1-eq-inj-a2 :
 {m n : Level} {A : Set m} {B : Set n} ->
 (f : A -> B) -> surjection f ->
 (g : A -> B) -> injection g ->
 (b : B) -> Sigma A \{a1 -> Sigma A \{a2 -> Id (g a1) (f a2)}}
surj-inj-imp-ex-a1-a2-where-surj-a1-eq-inj-a2 {m} {n} {A} {B} f surj-f g inj-g b =
 record {
  proj1 = proj1 (surj-f b) ;
  proj2 = record {
   proj1 = proj1 (surj-f (g (proj1 (surj-f b))));
   proj2 = Id_sym (proj2 (surj-f (g (proj1 (surj-f b)))))
  }
 }

record transaction : Set where
 field
  sender : Nat

tx1 : transaction
tx1 = record { sender = zero}

tx2 : transaction
tx2 = record { sender = suc zero}

-- ...

-- the following won't work
{-
data acceptedTransactions : Set where
 tx1 : acceptedTransactions //error, tx1 already declared
 tx2 : acceptedTransactions
 ...
-}

--what can we do instead?
data acceptedTransactions : Set where 
 atx1 : (t : transaction) -> Id t tx1 -> acceptedTransactions
 atx2 : (t : transaction) -> Id t tx2 -> acceptedTransactions

atx1' : acceptedTransactions
atx1' = atx1 tx1 (refl tx1)
atx2' : acceptedTransactions
atx2' = atx2 tx2 (refl tx2)

func-matching-surj-is-surj :
 {m n : Level} {A : Set m} {B : Set n} ->
 (f : A -> B) -> surjection f ->
 (g : A -> B) -> ((a : A) -> Id (g a) (f a)) ->
 (b : B) -> Sigma A \{a -> Id (g a) b}
func-matching-surj-is-surj {m} {n} {A} {B} f surj-f g matching b =
 record {
  proj1 = proj1 (surj-f b);
  proj2 = Id_trans (matching (proj1 (surj-f b))) (f-of-fiber-f-b-is-b f b (surj-f b))
 }

func-matching-inj-is-inj :
 {m n : Level} {A : Set m} {B : Set n} ->
 (f : A -> B) -> injection f ->
 (g : A -> B) -> ((a : A) -> Id (g a) (f a)) ->
 (a1 a2 : A) -> Id (g a1) (g a2) -> Id a1 a2
func-matching-inj-is-inj {m} {n} {A} {B} f inj-f g matching a1 a2 p =
 inj-f a1 a2 (Id_trans (Id_sym (matching a1)) (Id_trans p (matching a2)))


{-
surjective-imp-inj-is-surj :
 ({m n : Level} {A : Set m} {B : Set n} ->
 (f : A -> B) -> surjection f -> 
 (g : A -> B) -> injection g -> 
 (b : B) -> Sigma A \{a -> Id (g a) b}) -> False
surjective-imp-inj-is-surj {m} {n} {A} {B} hyp = 
-} 

--counterexample : 
-- f(n) = 2n is a surjection Z -> 2Z
-- f(n) = 4n is an injection Z -> 2Z
-- but the injection is not a surjection
-- proof: there is no n:Z such that 4n = 2


bijection-invertible :
 {m n : Level} {A : Set m} {B : Set n} ->
 (f : A -> B) -> bijection f ->
 Sigma (B -> A) \{g -> left-inv g f}
bijection-invertible {m} {n} {A} {B} f bij-f = 
 record {
  proj1 = \{b -> proj1 (proj2 (surjection-fiber-reverse f (andSnd bij-f) b))};
  proj2 = 
   \{a -> 
     (andFst bij-f) 
      a 
      (proj1 (proj2 (surjection-fiber-reverse f (andSnd bij-f) (f a)))) 
      (Id_sym (f-of-fiber-f-b-is-b f (f a) (proj2 (surjection-fiber-reverse f (andSnd bij-f) (f a)))))
   }
 }

{-
bijectivity-symmetric :
 {m n : Level} {A : Set m} {B : Set n} ->
 bijective A B -> bijective B A
bijectivity-symmetric {m} {n} {A} {B} bijAB =
 record {
  andFst = ;
  andSnd = 
 }
-}






{-
injective-imp-surj-is-inj :
 ({m n : Level} {A : Set m} {B : Set n} ->
 (f : A -> B) -> injection f ->
 (g : A -> B) -> surjection g ->
 (a1 a2 : A) -> Id (g a1) (g a2) -> Id a1 a2) -> False
injective-imp-surj-is-inj hyp =
-} 


--counterexample :
--There are bijections between Z and 2Z:
--f(n) = 2n 
--f(n) = 2*ceiling(n/2) is a surjection Z -> 2Z, but not an injection



--surjection A to B, surjection B to A implies bijection A to B
{-
surj-antisym :
 ({m n : Level} {A : Set m} {B : Set n} ->
 (f : A -> B) -> surjection f ->
 (g : B -> A) -> surjection g ->
 bijection f) -> False
surj-antisym2 hyp =
-}




{-
surj-antisym2 :
  {m n : Level} {A : Set m} {B : Set n} ->
  (f : A -> B) -> surjection f ->
  (g : B -> A) -> surjection g ->
  Sigma (A -> B) \{bij -> bijection bij}
surj-antisym2 {m} {n} {A} {B} f surj-f g surj-g =
 record {
  proj1 = ?
  proj2 = record { 
   andFst = injection proj1
   andSnd = surjection proj1
  }
 }
-}

--Method 1:
--ex-surj-AB-imp-ex-inj-BA will tell us that an injection A -> B does exist
--surjective-imp-inj-is-surj would then tell us that this injection is also a surjection,
--completing the proof.

--Method 2:
--ex-surj-AB-imp-ex-inj-BA will tell us that an injection A -> B does exist
--injective-imp-surj-is-inj would then tell us that the surjection f is also an injection,
--completing the proof.
--This also proves "surj-antisym" and not just "surj-antisym2"





surj-antisym3 :
 {m n : Level} {A : Set m} {B : Set n} ->
 (f : A -> B) -> surjection f ->
 (g : B -> A) -> surjection g ->
 bijective A B
surj-antisym3 {m} {n} {A} {B} f surj-f g surj-g =
 record {
  andFst = record {
   proj1 = proj1 (ex-surj-AB-imp-ex-inj-BA g surj-g);
   proj2 = proj2 (ex-surj-AB-imp-ex-inj-BA g surj-g)
  } ;
  andSnd = record {
   proj1 = f ;
   proj2 = surj-f
  }
 }

{-
unique
 if you have a type A : Set m,
 and an object a : A
 and a proposition P : A -> Set n
 and a proof prf-a : P a
 then is unique if forall a' : A, P a' -> Id a a'
-}

unique : {m n : Level} -> {A : Set m} -> (P : A -> Set n) -> (a : A) -> Set (lmax m n)
unique {m} {n} {A} P a = (a' : A) -> P a' -> Id a a'
  



record Functor {m n : Level} {A : Set m} {B : Set n} : Set (lmax m n) where
 field
  omap : A -> B
  fmap : (A -> A) -> (B -> B)
  
  

data List (A : Set) : Set where
 [] : List A
 _::_ : A -> List A -> List A




curry : {a b c : Level} {A : Set a} {B : A -> Set b} {C : Sigma A B -> Set c} -> 
        ((p : Sigma A B) -> C p) ->
        ((x : A) -> (y : B x) -> C (record {proj1 = x ; proj2 = y } ))
curry f x y = f (record {proj1 = x ; proj2 = y })



uncurry : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} -> (A -> B -> C) -> (Sigma A (\{a -> B}) -> C)
uncurry f xy = f (proj1 xy) (proj2 xy)



