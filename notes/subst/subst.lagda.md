```
module subst where
open import lc-essentials
open import Agda.Primitive
```

version 1 - we keep the freshest var id globally for the whole tree
```
{-# TERMINATING #-}
-- yea i think thats what it is. I mean, was there ever any discussion wether this algo is terminating?
-- i certainly trust it, let's see if it works

subst-helper1 : LambdaTerm -> LambdaVar -> LambdaTerm -> Nat -> Pair LambdaTerm Nat
-- it returns a pair of (new term, freshest var id)

subst-helper1 (Var x) v r n = (x' , n)
 where
  x' = if (LambdaVar-eq x v) then r else (Var x)

subst-helper1 (App f x) v r n = ((App f' x'), n') -- # <-- and then package them up to return
 where
  f'' = subst-helper1 f v r n
  f' = first f''
  -- so here substitute in the function part of the App, get a pair
  -- extract the term with first
  -- extract the freshest var with second
  -- use that freshest var when substituting into the arg part of the App
  x'' = subst-helper1 x v r (second f'')
  x' = first x''
  -- extract the term
  n' = second x''
  -- and extract the freshest var

subst-helper1 (Abs x e) v r n = case-Abs
 where
  case-Abs =
   if (LambdaVar-eq x v) then 
    ((Abs x e) , n)
   else (
    if (list-in (FV r) x) then -- if the var is in the replacer
     ((Abs (V (suc n)) capture-avoidingly-substituted-body) , second (subst-helper1 body-with-captured-var-substituted-for-fresh v r (suc n))) -- subst it for a fresh var in the replacer, then do the replacement
    else 
     ((Abs x (first (subst-helper1 e v r n))) , (second (subst-helper1 e v r n))) -- just do the replacement in the lambda body
   )
   where
    -- yea just this right here
    -- this recursive call uses e which is a substructure of (Abs x e),
    -- everything's good with this one, we know it's theoretically heading towards termination
    body-with-captured-var-substituted-for-fresh = first (subst-helper1 e x (Var (V (suc n))) (suc n))
    -- on the other hand, Agda doesn't know what "body-with..." is really, in terms of
    -- whether it's a bigger or smaller (or same-sized) arg as (Abs x e)
    -- 
    -- usually to make the recursive function work out as a proper function though it would need to
    -- recurse over something that can at least cover every case, and then you can potentially switch
    -- over to a different structure that fits your cases better (like switching over to Nat if we're
    -- gonna recurse over depths of trees instead of subterms of trees, etc..)

    -- but ok, so, i'm wondering if we could fix this having the function run a subst-list instead of
    -- just a single subst, then we'd only be making the recursive call onto the substructure e, but
    -- passing two substitutions in the list
    -- well, that's sort of what i'm thinking except the other function would just be subst-list and
    -- they'd mutually recurse on each other, but, in a way that Agda can check
 
    -- the way i'm looking at this is, we *almost* have the substructural recursion required, minus
    -- this slight one-step detour, which only occurs in this particular case, doesn't change the
    -- size of the term, and doesn't change the overall substitution process beyond that one step

    -- all we need is some argument that will necessarily decrease as we make recursive calls, and
    -- i think we could potentially use depth for that.makes sense

    -- so, agda wouldn't care that we're using this body-with-... if some other argument were decreasing
    -- but, this is what Agda sees for the purposes of termination check:
    -- (Abs x e)   v r n
    -- {something} v r (suc n)

    -- but if we had a depth arg, that should decrease on every recursive call
    -- almost, Agda's termination check doesn't know what our depth() function means so
    -- we'd call depth in the subst function and pass the value to subst-helper to initialize it
    -- then in subst-helper we'd have to define things manually so that Agda can just see
    -- (suc n) decreasing to n
    -- Now, there's a slight caveat to this approach: depending how we do it we might have to
    -- prove in various cases that depths of terms actually align with what we've manually defined
    -- I'll have to think about that, we're not having to prove anything for the "freshest var id"
    -- param because we've basically opted to "not care about its correctness yet", but, we
    -- also aren't depending on that parameter to be the decreasing one
    -- so, if we pass this depth arg, there will be some impossible cases that we have to figure
    -- out what to do with, example: (App a b) with depth parameter 0, or depth parameter 1000000
    -- yea, shouldnt be a proble right? brb coffee
    --
    -- so, what we do is pass the depth parameter along with a proof that the depth parameter
    -- actually matches the depth of the term
    -- then in any special cases like (App a b) with depth parameter 0, we can use this
    -- assumed proof of the equality between the depth parameter and the result of running depth()
    -- on the term, and derive a contradiction, allowing us to "formally skip those cases"
    -- but when we recurse, we have to actually provide those proofs that the depth parameters
    -- we're passing to the recursive call match the terms we're passing to the recursive call,
    -- under the assumption that our original depth parameter matches our original term

    -- so like this Abs case would have two more parameters, depth & proof-that-depth-matches-for-Abs-x-e,
    -- and then we have that proof-that-depth-matches available as an assumption to use to prove
    -- proof-that-depth-matches-for-e

    -- we'd case split on depth, there would be the case for 0 that's impossible and we'd derive a
    -- contradiction and skip that case, and then we'd have the case of
    -- (suc n) proof-that-depth-matches-for-Abs-x-e
    -- then we know that if (Abs x e) has depth (suc n), then e should have depth n, so that's what
    -- we'll pass as the depth parameter in the recursive call, now Agda will catch the decrease
    -- and we'll pass termination check, so long as we can provide a proof that e has depth n under
    -- assumption that (Abs x e) has depth (suc n), which should likely be trivial since
    -- depth(Abs x e) will probably be literally just defined as suc (depth e)

    -- so then it would all work out nice for Agda, even if it's kinda jumping through some hoops for us,
    -- but, as a bonus this builds a decent amount of verification of some things right into the
    -- structure of the function

    -- so, *that* would work. but, is it the best option? idk. there's probably some simpler & easier
    -- solution that i'm not thinking of because i tend to just roll with the math when i'm in agda

    -- before we dive into that, let's mull over: what if don't pass the proof of depth-matching
    -- we'd basically have to change the output to a Maybe LambdaTerm because, not every input would
    -- correspond to a LambdaTerm output, like where do we send (App a b) when passed with depth param = 0?

    -- if we were cool with Maybe LambdaTerms, then we could do dynamic-checking to make sure the
    -- args match up and if they don't then fail into a Nothing
    
    -- btw this is why i don't think of agda as a "programming" lang
    -- it's great to have this environment for proofs, not so great to have to do a workaround every step
    -- of the way to write programs in functional-style and then further ensure that they fit some exact
    -- mold that agda will tolerate in order to pass the termination-checker
    -- so generally i think in terms of eventually having a modeled programming language that's more "loose"
    -- and then just doing verification or generic correct-by-construction translation/compilation things
    -- from this level, with even that probably making heavy use of the algorithms described in the
    -- modeled languages rather than having to write algorithms where you're supposed to be writing your proofs


    -- here i just kinda made the mistake of assuming that all the basic lambda calc operations were
    -- straightforward enough for agda without too many workarounds, but, even this is an example of something
    -- where i'd be extracting the algorithm from a simulated programming lang (ideally)
    
    capture-avoidingly-substituted-body = first (subst-helper1 body-with-captured-var-substituted-for-fresh v r (suc n))
    -- capture-avoidingly-substituted-body = subst-list
-- yea i'm totally fine with an on-paper proof of correctness and maybe coming back to formalize that later and
-- fix this up accordingly if we ever feel the need

-- do you understand why it fails termination check here?
-- so we're recursing on subst-helper1
-- Agda only allows what i call "substructural recursion"
-- meaning one of the arguments to the recursive call needs to be
-- a substructure of one of the arguments to the original call.
-- so, x and e are substructures of (Abs x e)
-- 

subst1 : LambdaTerm -> LambdaVar -> LambdaTerm -> LambdaTerm
subst1 t v r = first (subst-helper1 t v r (max (maxVar t) (maxVar r)))
-- instead of passing it the term i pass it the max var id
-- and then by passing around that id i can generate the fresh
-- var as needed







-- --------------------------- version 2 - dunno



{-# TERMINATING #-}
-- yea i think thats what it is. I mean, was there ever any discussion wether this algo is terminating?
-- i certainly trust it, let's see if it works


subst-helper2 : LambdaTerm -> LambdaVar -> LambdaTerm -> Nat -> LambdaTerm
-- it returns a pair of (new term, freshest var id)

subst-helper2 (Var x) v r n = x'
 where
  x' = if (LambdaVar-eq x v) then r else (Var x)

subst-helper2 (App f x) v r n = App f' x'
 where
  f' = subst-helper2 f v r n
  -- so here substitute in the function part of the App, get a pair
  -- extract the term with first

  -- version 2 doesn't keep track of globally freshest var
  x' = subst-helper2 x v r n
subst-helper2 (Abs x e) v r n = case-Abs
 where
   case-Abs =
    if (LambdaVar-eq x v) then 
     (Abs x e)
    else (
     if (list-in (FV r) x) then -- if the var is in the replacer
      (Abs (V (suc n)) capture-avoidingly-substituted-body) -- subst it for a fresh var in the replacer, then do the replacement
     else 
      (Abs x (subst-helper2 e v r n)) -- just do the replacement in the lambda body
    )
     where
    -- this recursive call uses e which is a substructure of (Abs x e),
    -- everything's good with this one, we know it's theoretically heading towards termination
      body-with-captured-var-substituted-for-fresh = subst-helper2 e x (Var (V (suc n))) (suc n)
      capture-avoidingly-substituted-body = subst-helper2 body-with-captured-var-substituted-for-fresh v r (suc n)


subst2 : LambdaTerm -> LambdaVar -> LambdaTerm -> LambdaTerm
subst2 t v r = subst-helper2 t v r (max (maxVar t) (maxVar r))








-- ----------------------- version 3 - subst list
-- like version 1, but this tries to make that recursion that it doesn't like happen
-- inside of subst-list which is already decreasing on the list
-- actually i think the mutual recursion with the subst-list would work after all:
-- inside subst-helper it would always be decreasing on the structure of the term
-- inside subst-list it would always be decreasing on the length of the list

-- btw just C-c C-l instead of compile
-- :). Alright, what if we turn all subst-helper cases into subst-lists
-- i think we'd run into the same problem because the basic backbone of the
-- subst algo is recursing over the term structure rather than over subst-lists
-- at least under this formulation of the subst algo anyway
-- for agda to see it as decreasing under the subst-lists, we'd have to make a way
-- that it actually was, which would mean we'd need to start out with basically
-- a list of all the potential substitutions and loop through that and either
-- perform them or cross them off the list, but, i don't think that would really
-- work out because we'd have to predict the appropriate list for any given
-- term and also have the algo that recurses over it the right way

-- ultimately something more along the lines of depth is the thing to be
-- recursing over, like, consider this in terms of a proof by induction
-- this is pretty much what i was mentioning the other day about how this
-- capture-avoiding subst changes the term, makes us not be able to recurse
-- directly over the structure, and, as far as math goes at least, makes
-- us induct over some other way to chop up the cases

-- alright one last idea, can we thread an 'orig' term along with the changed one?
-- sure that's what i was doing originally to keep track of fresh vars
-- whatever we want to thread along with it can just be added as an extra
-- parameter, and when we start having too many parameters then we can stick
-- them into a record type and just use that record as a single parameter for
-- convenience (maybe not in this particular case, but, in general when you
-- start threading around lots of different objects you just stuff them into
-- a record)

-- or, err, 


-- ok so it won't work to make the substitution in the replacer, because these substitutions
-- fit into a larger context of evaluation

-- agda should be figuring this out for us
-- arguably it partially is
-- it's forcing us to examine the algos & models in way more detail than we probably would
-- have otherwise, and, except in a couple cases i'd say this is mostly not a bad thing
-- i don't really think of it as a great programming framework, and don't really use much of
-- the automated proving, but, the automated verification + correct-by-construction gives it
-- it's "place" in the toolkit, i don't necessarily think it needs to go beyond that "place",
-- and imo one of the big problems getting it widely adopted is the academic community really
-- pushes it as the be-all-end-all for everything, despite decades of evidence that it consistently demonstrates
-- it doesn't measure up in terms of quickly pushing out a manually constructed algorithm, and
-- despite those same decades they've theoretically had to fix the problem.

-- as a proof-checking & logical modeling framework, so far i'd say it's doing it's
-- job well for our task. agda takes a bunch of useful proof methods (not all proof methods
-- but a bunch of useful ones) and packages it up into a nice box so when i'm
-- confronted with like, a random structural induction problem, vaguely defined in
-- literature, i can think "what would i do in agda", and then, even if i'm having to
-- jump through some hoops in some places, at least i'm basically just following a
-- cookie-cutter formula rather than trying to build up the conceptual framework to
-- tackle these problems from scratch.

-- now, more concretely, i noticed the whole thing about how capture-avoiding substitution
-- would force us to use something besides for just standard direct structural induction/recursion
-- on the terms, way before we jumped into agda, of course i had some intuition & experience
-- with agda to predict we would've run into the issue, but, this particular issue is not
-- one with agda at all, it's just a matter of the non-trivial structure we want to induct over
-- and if we were just going about informally on paper, we might not catch that, but


-- agda not only catches that, it forces us into thinking of more appropriate models/structures/algos
-- (more appropriate for math & reasoning), and these turn out to be more appropriate on paper
-- because if we can figure out what kind of structure to induct over *in Agda*, well, relative to
-- "on paper" math this is just following a well-defined cookie cutter proof-structuring process


-- i take all the crutches i can get, personally.

-- my one major gripe about what we're doing (or i should say, what we have the capacity to be
-- doing, at this stage of our developments with MLTT), is that we don't already have flexible
-- programming models to write the algorithms in so that we don't waste time doing that at
-- agda's tfpl level, and can just push out algorithms in the model & then jump straight to
-- the proofs we actually want to be doing at this level.

-- but unfortunately that's just exactly what those "cumulative developments" would be

-- long story short, this isn't "how i intend MLTT-TFPL to be used", it's just "as good a
-- problem as any"
-- in "real world" i would build up lots more foundational logic/math libs, lots of libs
-- with proofs about basic data structures & functions & algorithms, build up basic framework
-- for abstraction & "math-interfaces" (i'll stop saying isomorphism i promise XD)
-- and then before i would set out to tackle proofs about something more sophisticated like
-- lambda calc evaluation semantics, i would try to first build up my model of it in
-- terms of whats provided in those basic libs, so that i'd already have lots of reusable
-- results ready to go

-- but that's not what we're doing now, we'll save that for after we've built our own MLTT-TFPL
-- i must say that now that you're diving into the concrete details you're picking up on
-- it quite fast, i was doing stuff like A -> A, A -> (A -> B) -> A, not (True -> False) for
-- like weeks before i was getting into the nitty-gritty 


-- what agda *really* should probably have is some more human-friendly error reporting so that
-- you actually know why it has a problem with something without just already knowing why
-- beforehand, like, why in particular does it have a termination-checking problem on the subst
-- even with us knowing beforehand that we would be running into this issue, we still tried
-- all kinds of other workarounds because the exact details of why they couldn't work weren't
-- entirely obvious

-- here's how i would instead imagine agda being used in "real world":
-- take x86 and, idk, subleq
-- you make a datatype of x86 programs, along with a specification of their semantics
-- same with subleq
-- now you have a database of x86 code snippets
-- all typed with various constraints they satisfy, with a basic framework that
-- would allow you to make sure you only produced correct-by-construction x86, relative
-- to some higher-level human specifications

-- the "basic" framework centers around making liberal use of those "math-interface"
-- concepts to... basically ensure that some definition of "coherence" is satisfied,
-- along with formalization of various different comp sci results that enable different
-- kinds of automated translations, or, well, most things center around some kind of
-- translation. translation from format A to format B, translation from source to
-- compiled code, translation from human-level semantics to machine-level semantics
-- translation from regex to automaton,

-- idk maybe i abuse the word "translation"

-- transformation**. there we go. most everything useful will come down to a transformation
-- or be centered around transformations of different kinds, because, ultimately we don't
-- really care all that much about just having some static knowledge sitting there letting
-- us sleep a bit better at night because we think we proved something, we want transformations
-- that do things for us and such that we can be assured that *in the future* when we come back
-- and pick up these programs, we'll be able to easily compose them without having things
-- being broken all over the place

-- i wanna get to the point where we can just do shit like say "web app" and a blank web app
-- just appears, and we don't have to worry about any of the details, it's just correct by
-- construction already based on all kinds of proven transformations & relations
--

-- at some point now that you've played around in Agda a bit take a look at
-- github.com/sto0pkid/CategoryTheory/blob/master/Agatha2.agda
-- and you'll see a sort of first approximation of what i'm aiming for (on the human side of the spectrum)


{-
People, other animals, sensors
------------- 
Natural lang / plain-txt / raw input/output                <-------- haven't worked on these yet
 ^                           ^                                  |
 |                           |                                  |
 v                           v                                  |
Manual translation      CNL, NLP, AI <--> control, training <---
 ^  ^                       /      
 |  |______________________/_______________________________________________________________________
 v                        /                                                                        |
Formalized human-level semantics (specific models) <--> customization/personalization ### <---------
 ^                                                                                                 |
 |                                                                                                 |
 v                                                                                                 |  
Mathematical modeling libs     ### sto0pkid/CategoryTheory/Agatha2.agda ---------------------------
 ^
 |
 |
 |-----------> Core math/logic/reasoning <---> everything  ### most of the content of sto0pkid/CategoryTheory
 | 
 |
 v
Comp sci theory       ### what we're working on now
 ^
 |
 v
Real-world machine models  ### haven't worked on this yet.
 ^
 |
 v
---------- Real/virtual boundary
Machines
-}



-- ideally :) but, this is like the machine code of math, you don't get much magic aside from
-- verification & correct-by-construction until more cumulative developments
-- agda has hole-filling though (term inferencing / interactive theorem proving) that i don't
-- mess with enough because i'm usually focused on learning the basic concepts of the proof
-- theory & how to construct a proof in the first place rather than get ahead of myself by
-- just automating, but, we probably should start messing with that sooner rather than later
-- sounds good
-- i need to nap for a bit. 
 -- agda doesn't recognize it as terminating
{-# TERMINATING #-}
subst-helper3 : LambdaTerm -> LambdaVar -> LambdaTerm -> Nat -> Pair LambdaTerm Nat

subst-list : LambdaTerm -> List (Pair LambdaVar LambdaTerm) -> Nat -> Pair LambdaTerm Nat
subst-list t [] n = (t , n)
subst-list t ((v , r) :: subss) n = subst-list (first (subst-helper3 t v r n)) subss (second (subst-helper3 t v r n))  

-- so, we're decreasing on the list, but apparently Agda's smart enough to see that we might
-- be recursing back into subst-helper3 with something other than a subterm of what it
-- was originally called with.
-- i thought that yea the problem is that we are recursing into it with not-a-subterm,
-- but the solution here was supposed to be that we only do it in a function where we are also recursing
-- on a decreasing list, that was the theory, but, didn't work :)
-- because we're still recursing back into subst-helper3 it's just the same as whether
-- we had been doing it from within subst-helper3 or from within this function, like, if
-- we recurse back into subst-helper3 with a bigger term than we originally called with
-- then it didn't matter that we were decreasing on this list, but, i didn't quite
-- see that all the way through until i wrote out the function


-- subst-helper3 : LambdaTerm -> LambdaVar -> LambdaTerm -> Nat -> Pair LambdaTerm Nat
-- it returns a pair of (new term, freshest var id)

subst-helper3 (Var x) v r n = (x' , n)
 where
  x' = if (LambdaVar-eq x v) then r else (Var x)

subst-helper3 (App f x) v r n = ((App f' x'), n') -- # <-- and then package them up to return
 where
  f'' = subst-helper3 f v r n
  f' = first f''
  -- so here substitute in the function part of the App, get a pair
  -- extract the term with first
  -- extract the freshest var with second
  -- use that freshest var when substituting into the arg part of the App
  x'' = subst-helper3 x v r n
  x' = first x''
  -- extract the term
  -- and extract the freshest var

  n' = max (second f'') (second x'')
subst-helper3 (Abs x e) v r n = case-Abs
 where
  case-Abs =
   if (LambdaVar-eq x v) then 
    ((Abs x e) , n)
   else (
    if (list-in (FV r) x) then -- if the var is in the replacer
     ((Abs (V (suc n)) capture-avoidingly-substituted-body), second tmp) -- subst it for a fresh var in the replacer, then do the replacement
    else 
     ((Abs x (first (subst-helper3 e v r n))), n) -- just do the replacement in the lambda body
   )
   where
    tmp = subst-list e ((x , (Var (V (suc n)))) :: ((v , r) :: [])) (suc n)
    capture-avoidingly-substituted-body = first tmp

-- first (subst-helper2 body-with-captured-var-substituted-for-fresh v r (suc n))


subst3 : LambdaTerm -> LambdaVar -> LambdaTerm -> LambdaTerm
subst3 t v r = first (subst-helper3 t v r (max (maxVar t) (maxVar r)))





-- ok so there is a pretty non-hackish approach to this actually i think but we'd
-- have to rework the basic mechanism of the substitution algo, basically build up
-- a substitution list as we recurse down the term structure, just like we would in
-- euler, so, basically a unification algorithm
-- alright, thats gonna be an altogether another version of subst
-- ah hrm, nvm, that would work for alphaEq because it's just comparing the terms
-- this would work for subst too but the main point of subst is to actually
-- apply the substitution list rather than build it up
-- yea but you can first build it up provably terminatingly and then apply it --maybe
-- sounds better than the provable depth-recursion if we could make it work
-- yeah
-- so if it wasn't for this capture-avoidance, we wouldn't have any problems here,
-- we could just recurse directly over the structure and agda would see termination
-- so maybe if we can build up a substitution-list thats already... "capture-avoided"
-- and then make a second algo that recurses again and is more of a text-replace
-- rather than a substitution algo
-- so the big q there is whether we can build up that list, with a recursion that
-- Agda can easily check
-- doesnt this simply come down to the other version of the subst algo, which is to check for free vars
-- in the replacer that would conflict with vars in the term, and just replace them, in the replacer, with non-conflicting ones?
-- "substitution-list thats already capture-avoided"
-- ah i see what you're saying, no that's not quite what i meant there, but, that's
-- another possibility we haven't tried yet
-- ah, hrm, lemme think about that












{-
alphaEq only checks if the *bound* vars can be renamed to yield syntactically
equal terms. if two terms have different free vars then they are not alphaEq.
-}
alphaEq : (LambdaTerm -> LambdaVar -> LambdaTerm -> LambdaTerm) -> LambdaTerm -> LambdaTerm -> Bool
alphaEq subst (Var (V x)) (Var (V y)) = Nat-eq x y 
alphaEq subst (App t s) (App t' s') = (alphaEq subst t t') and (alphaEq subst s s')
alphaEq subst (Abs x e) (Abs x' e') = alphaEq subst e (subst e' x' (Var x))
alphaEq subst _ _ = false


suc-inj : (n m : Nat) -> (suc n) == (suc m) -> n == m
suc-inj n m [suc-n==suc-m] = cong pred (suc n) (suc m) [suc-n==suc-m]


P[x]+P[y]-implies-P[if-Q-then-x-else-y] : ∀ {i j} {A : Set i} (P : A -> Set j) -> {x y : A} -> P x -> P y -> (b : Bool) -> P (if b then x else y)
P[x]+P[y]-implies-P[if-Q-then-x-else-y] P Px Py true = Px
P[x]+P[y]-implies-P[if-Q-then-x-else-y] P Px Py false = Py


data _∨_ {i} {j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
 inl : A -> A ∨ B
 inr : B -> A ∨ B

∨-is-commutative :  ∀ {i j} {A : Set i} {B : Set j} -> A ∨ B -> B ∨ A
∨-is-commutative (inl a) = inr a
∨-is-commutative (inr a) = inl a

[if-b-A-B]==[if-b-A'-B']-implies-[A=A'∨B=B'] : ∀ {i} {A : Set i} {x x' y y' : A} -> (b : Bool) -> (if b then x else y) == (if b then x' else y') -> (x == x') ∨ (y == y')
[if-b-A-B]==[if-b-A'-B']-implies-[A=A'∨B=B'] true hyp = (inl hyp)
[if-b-A-B]==[if-b-A'-B']-implies-[A=A'∨B=B'] false hyp = (inr hyp)

[A=A'&B=B']-implies-[if-b-A-B]==[if-b-A'-B'] : ∀ {i} {A : Set i} {x x' y y' : A} -> (x == x') -> (y == y') -> (b : Bool) -> (if b then x else y) == (if b then x' else y')
[A=A'&B=B']-implies-[if-b-A-B]==[if-b-A'-B'] hyp1 hyp2 true = hyp1
[A=A'&B=B']-implies-[if-b-A-B]==[if-b-A'-B'] hyp1 hyp2 false = hyp2


process-of-elimination : ∀ {i j} {A : Set i} {B : Set j} -> A ∨ B -> ¬ A -> B
process-of-elimination (inl a) ¬A = omega (¬A a)
process-of-elimination (inr b) ¬A = b

f[if-b-x-y]==[if-b-fx-fy] : ∀ {i j} {A : Set i} {B : Set j} {x y : A} (f : A -> B) -> (b : Bool) -> f (if b then x else y) == (if b then (f x) else (f y))
f[if-b-x-y]==[if-b-fx-fy] f true = refl
f[if-b-x-y]==[if-b-fx-fy] f false = refl

[if-b-x-x]==x : ∀ {i} {A : Set i} {x : A} (b : Bool) -> (if b then x else x) == x
[if-b-x-x]==x true = refl
[if-b-x-x]==x false = refl

x->x',y->y'-implies-[if-b-x-y]->[if-b-x'-y'] : ∀ {i} {x x' y y' : Set i} -> (x -> x') -> (y -> y') -> (b : Bool) -> (if b then x else y) -> (if b then x' else y')
x->x',y->y'-implies-[if-b-x-y]->[if-b-x'-y'] hyp1 hyp2 true x = hyp1 x
x->x',y->y'-implies-[if-b-x-y]->[if-b-x'-y'] hyp1 hyp2 false y = hyp2 y

pair-extensionality : ∀ {A : Set } {B : Set} {a a' : A} {b b' : B} -> (a == a') -> b == b' -> (a , b) == (a' , b')
pair-extensionality {A} {B} {a} {.a} {b} {.b} refl refl = refl

pair-decomp : ∀ {A B : Set} (p : Pair A B) -> p == ((first p) , (second p))
pair-decomp (a , b) = refl



pair-extensionality' : ∀ {A B : Set} {p1 p2 : Pair A B} -> (first p1) == (first p2) -> (second p1) == (second p2) -> p1 == p2
pair-extensionality' {A} {B} {p1} {p2} hyp1 hyp2 = proof
 where
  p1-lem : p1 == ((first p1) , (second p1))
  p1-lem = pair-decomp p1
  
  p2-lem : p2 == ((first p2) , (second p2))
  p2-lem = pair-decomp p2

  f : A -> Pair A B
  f q = (q , (second p1))

  g : B -> Pair A B
  g q = ((first p2) , q)

  lem-1 : ((first p1) , (second p1)) == ((first p2) , (second p1))
  lem-1 = cong f (first p1) (first p2) hyp1

  lem-2 : ((first p2) , (second p1)) == ((first p2) , (second p2))
  lem-2 = cong g (second p1) (second p2) hyp2

  proof = ==-trans p1-lem (==-trans lem-1 (==-trans lem-2 (==-sym p2-lem)))



data Exists {i} {j} (A : Set i) (P : A -> Set j) : Set (i ⊔ j) where
 _,_ : (a : A) -> P a -> Exists A P

-- syntax Exists A (λ x → e) = Exists x ∈ A , e
syntax Exists A (λ x → e) = ∃ x ∈ A , e





π₁ : ∀ {i j} {A : Set i} {P : A -> Set j} -> Exists A P -> A
π₁ (a , _) = a

π₂ : ∀ {i j} {A : Set i} {P : A -> Set j} -> (p : Exists A P) -> P (π₁ p)
π₂ (_ , b) = b

_+_ : Nat → Nat → Nat
z       + y = y
(suc n) + y = suc (n + y)


_≤_ : (x y : Nat) → Set
x ≤ y = ∃ k ∈ Nat , ((k + x) == y)

_<_ : (x y : Nat) → Set
x < y = ∃ k ∈ Nat , (((suc k) + x) == y)

sx≠sy-implies-x≠y : (x y : Nat) -> (suc x) ≠ (suc y) -> x ≠ y
sx≠sy-implies-x≠y x y [sx≠sy] [x=y] = contradiction
 where
  lem1 : (suc x) == (suc y)
  lem1 = cong suc x y [x=y]
  
  contradiction = [sx≠sy] lem1

Nat-eq-refl-ind : (n : Nat) -> (Nat-eq n n == true) -> Nat-eq (suc n) (suc n) == true
Nat-eq-refl-ind n hyp = proof
 where
  lem1 : Nat-eq (suc n) (suc n) == Nat-eq n n
  lem1 = refl
  
  proof = ==-trans lem1 hyp

Nat-eq-refl : (n : Nat) -> (Nat-eq n n == true)
Nat-eq-refl z = refl
Nat-eq-refl (suc n) = Nat-eq-refl-ind n (Nat-eq-refl n)

Nat-Eq-implies-eq : (x y : Nat) -> x == y -> Nat-eq x y == true
Nat-Eq-implies-eq x .x refl = Nat-eq-refl x


Nat-NEq-implies-neq : (x y : Nat) -> x ≠ y -> Nat-eq x y == false
Nat-NEq-implies-neq z z [z≠z] = omega ([z≠z] refl)
Nat-NEq-implies-neq z (suc y) [z≠sy] = refl
Nat-NEq-implies-neq (suc x) z [sx≠z] = refl
Nat-NEq-implies-neq (suc x) (suc y) [sx≠sy] = Nat-NEq-implies-neq x y (sx≠sy-implies-x≠y x y [sx≠sy])


Nat-eq-implies-Eq-ind : (x y : Nat) -> (Nat-eq x y == true -> x == y) -> Nat-eq (suc x) (suc y) == true -> (suc x) == (suc y)
Nat-eq-implies-Eq-ind x y hyp1 hyp2 = proof
 where
  lem1 : Nat-eq (suc x) (suc y) == Nat-eq x y
  lem1 = refl

  lem2 : Nat-eq x y == true
  lem2 = ==-trans (==-sym lem1) hyp2

  lem3 : x == y
  lem3 = hyp1 lem2

  proof = cong suc x y lem3

Nat-eq-implies-Eq : (x y : Nat) -> Nat-eq x y == true -> x == y
Nat-eq-implies-Eq z z hyp = refl
Nat-eq-implies-Eq z (suc y) hyp = omega (true≠false (==-sym hyp))
Nat-eq-implies-Eq (suc x) z hyp = omega (true≠false (==-sym hyp))
Nat-eq-implies-Eq (suc x) (suc y) = Nat-eq-implies-Eq-ind x y (Nat-eq-implies-Eq x y)


LambdaVar-eq-refl : (v : LambdaVar) -> (LambdaVar-eq v v == true)
LambdaVar-eq-refl (V n) = Nat-eq-refl n

LambdaVar-Eq-implies-eq : (x y : LambdaVar) -> x == y -> LambdaVar-eq x y == true
LambdaVar-Eq-implies-eq x .x refl = LambdaVar-eq-refl x

LambdaVar-eq-implies-Eq : (x y : LambdaVar) -> LambdaVar-eq x y == true -> x == y
LambdaVar-eq-implies-Eq (V x) (V y) hyp = proof
 where
  lem1 : LambdaVar-eq (V x) (V y) == Nat-eq x y
  lem1 = refl 

  lem2 : Nat-eq x y == true
  lem2 = ==-trans (==-sym lem1) hyp

  lem3 : x == y
  lem3 = Nat-eq-implies-Eq x y lem2

  proof = cong V x y lem3

gte-refl-ind : (x : Nat) -> (x gte x) == true -> (((suc x) gte (suc x)) == true)
gte-refl-ind x hyp = hyp

gte-refl : (x : Nat) -> (x gte x) == true
gte-refl z = refl
gte-refl (suc n) = gte-refl-ind n (gte-refl n)

gte-lemma-ind : (x : Nat) -> (x gte (suc x)) == false -> ((suc x) gte (suc (suc x))) == false
gte-lemma-ind x hyp = hyp

gte-lemma : (x : Nat) -> (x gte (suc x)) == false
gte-lemma z = refl
gte-lemma (suc n) = gte-lemma-ind n (gte-lemma n)

x≠sucx : (x : Nat) -> x ≠ suc x
x≠sucx x [x=sx] = omega contradiction
 where
  f : Nat -> Bool
  f n = x gte n

  lem1 : (x gte x) == true
  lem1 = gte-refl x

  lem2 : (x gte (suc x)) == false
  lem2 = gte-lemma x

  lem3 : (x gte x) == (x gte (suc x))
  lem3 = cong f x (suc x) [x=sx]

  contradiction = true≠false (==-trans (==-sym lem1) (==-trans lem3 lem2))


x+suc-y==suc[x+y]-ind : (x y : Nat) -> (x + (suc y)) == suc (x + y) -> ((suc x) + (suc y)) == suc ((suc x) + y)
x+suc-y==suc[x+y]-ind x y hyp = proof
 where
  lem1 : ((suc x) + (suc y)) == suc (x + (suc y))
  lem1 = refl

  lem2 : suc (x + (suc y)) == suc (suc (x + y))
  lem2 = cong suc (x + (suc y)) (suc (x + y)) hyp

  lem3 : suc (suc (x + y)) == suc ((suc x) + y)
  lem3 = refl

  proof = ==-trans lem1 (==-trans lem2 lem3)

x+suc-y==suc[x+y] : (x y : Nat) -> (x + (suc y)) == suc (x + y)
x+suc-y==suc[x+y] z y = refl
x+suc-y==suc[x+y] (suc x) y = x+suc-y==suc[x+y]-ind x y (x+suc-y==suc[x+y] x y)


x+0==x : (x : Nat) -> (x + z) == x
x+0==x z = refl
x+0==x (suc n) = cong suc (n + z) n (x+0==x n)

[x+a]+y==a+[x+y] : (x y a : Nat) -> ((x + a) + y) == (a + (x + y))
[x+a]+y==a+[x+y] x y z = proof-z
 where
  lem1 : ((x + z) + y) == (x + y)
  lem1 = cong (λ q → q + y) (x + z) x (x+0==x x)

  lem2 : (z + (x + y)) == (x + y)
  lem2 = refl
 
  proof-z = ==-trans lem1 (==-sym lem2)
[x+a]+y==a+[x+y] x y (suc n) = proof-suc-n
 where
  lem1 : ((x + (suc n)) + y) == ((suc (x + n)) + y)
  lem1 = cong (λ q → q + y) (x + (suc n)) (suc (x + n)) (x+suc-y==suc[x+y] x n)

  lem2 : ((suc (x + n)) + y) == suc ((x + n) + y)
  lem2 = refl

  lem3 : ((suc n) + (x + y)) == suc (n + (x + y))
  lem3 = refl

  lem4 : ((x + n) + y) == (n + (x + y))
  lem4 = [x+a]+y==a+[x+y] x y n

  lem5 : suc ((x + n) + y) == suc (n + (x + y))
  lem5 = cong suc ((x + n) + y) (n + (x + y)) lem4

  proof-suc-n = ==-trans lem1 (==-trans lem2 (==-trans lem5 (==-sym lem3)))


a+[b+c]==[a+b]+c : (a b c : Nat) -> (a + (b + c)) == ((a + b) + c)
a+[b+c]==[a+b]+c z b c = refl
a+[b+c]==[a+b]+c (suc n) b c = proof
 where
  lem1 : ((suc n) + (b + c)) == suc (n + (b + c))
  lem1 = refl

  lem2 : ((suc n) + b) == suc (n + b)
  lem2 = refl

  lem3 : (((suc n) + b) + c) == ((suc (n + b)) + c)
  lem3 = refl

  lem4 : ((suc (n + b)) + c) == suc ((n + b) + c)
  lem4 = refl

  lem5 : (n + (b + c)) == ((n + b) + c)
  lem5 = a+[b+c]==[a+b]+c n b c

  lem6 : (suc (n + (b + c))) == (suc ((n + b) + c))
  lem6 = cong suc (n + (b + c)) ((n + b) + c) lem5

  proof : ((suc n) + (b + c)) == (((suc n) + b) + c)
  proof = ==-trans lem1 (==-trans lem6 (==-sym (==-trans lem3 lem4)))





¬[x<x] : (x : Nat) -> x < x -> False
¬[x<x] z (k , [sk+z=z]) = contradiction
 where
  lem1 : ((suc k) + z) == suc (k + z)
  lem1 = refl

  lem2 : isZero z == true
  lem2 = refl

  lem3 : isZero (suc (k + z)) == false
  lem3 = refl

  lem4 : isZero ((suc k) + z) == isZero (suc (k + z))
  lem4 = cong isZero (suc (k) + z) (suc (k + z)) lem1

  lem5 : isZero z == isZero ((suc k) + z)
  lem5 = cong isZero z ((suc k) + z) (==-sym [sk+z=z])

  lem6 : true == false
  lem6 = ==-trans (==-sym lem2) (==-trans lem5 (==-trans lem4 lem3))

  contradiction = true≠false lem6
¬[x<x] (suc n) (k , [sk+sn=sn]) = contradiction
 where
  lem1 : ((suc k) + (suc n)) == suc (k + (suc n)) 
  lem1 = refl

  lem2 : (k + (suc n)) == suc (k + n)
  lem2 = x+suc-y==suc[x+y] k n

  lem3 : suc (k + (suc n)) == suc (suc (k + n))
  lem3 = cong suc (k + suc n) (suc (k + n)) lem2

  lem4 : ((suc (suc k)) + n) == ((suc (suc k)) + n)
  lem4 = refl

  lem5 : ((suc k) + n) == suc (k + n)
  lem5 = refl

  lem6 : (suc n) == suc (suc (k + n))
  lem6 = ==-trans (==-sym [sk+sn=sn]) (==-trans lem1 lem3)
  
  lem7 : n == suc (k + n)
  lem7 = suc-inj n (suc (k + n)) lem6

  lem8 : ((suc k) + n) == n
  lem8 = ==-trans lem5 (==-sym lem7)

  lem9 : n < n
  lem9 = (k , lem8)

  contradiction = ¬[x<x] n lem9




x+y==y-implies-x==0 : (x y : Nat) -> (x + y) == y -> x == z
x+y==y-implies-x==0 z y hyp = refl
x+y==y-implies-x==0 (suc n) y hyp = omega (¬[x<x] y (n , hyp))

x+y==0-implies-x==0&y==0 : (x y : Nat) -> (x + y) == z -> Pair (x == z) (y == z)
x+y==0-implies-x==0&y==0 z z hyp = ( refl , refl )
x+y==0-implies-x==0&y==0 z (suc y) hyp = omega (zero≠sucn y (==-sym hyp)) 
x+y==0-implies-x==0&y==0 (suc x) z hyp = omega (zero≠sucn (x + z) (==-sym hyp))
x+y==0-implies-x==0&y==0 (suc x) (suc y) hyp = omega (zero≠sucn (x + (suc y)) (==-sym hyp))


≤-refl : (x : Nat) -> x ≤ x
≤-refl x = (z , refl)

≤-antisym : (x y : Nat) -> (x ≤ y) -> (y ≤ x) -> x == y
≤-antisym x y (k1 , [k1+x==y]) (k2 , [k2+y==x]) = proof
 where
  lem1 : (k2 + (k1 + x)) == (k2 + y)
  lem1 = cong (_+_ k2) (k1 + x) y [k1+x==y]

  lem2 : (k2 + (k1 + x)) == x
  lem2 = ==-trans lem1 [k2+y==x]

  lem3 : (k2 + (k1 + x)) == ((k2 + k1) + x)
  lem3 = a+[b+c]==[a+b]+c k2 k1 x

  lem4 : ((k2 + k1) + x) == x
  lem4 = ==-trans (==-sym lem3) lem2

  lem5 : (k2 + k1) == z
  lem5 = x+y==y-implies-x==0 (k2 + k1) x lem4

  lem6 : k1 == z
  lem6 = second (x+y==0-implies-x==0&y==0 k2 k1 lem5)

  proof : (z + x) == y
  proof = ==-trans (cong (λ q → q + x) z k1 (==-sym lem6)) [k1+x==y]







≤-trans : {a b c : Nat} -> (a ≤ b) -> (b ≤ c) -> (a ≤ c)
≤-trans {a} {b} {c} (k1 , [k1+a==b]) (k2 , [k2+b==c]) = proof
 where
  lem1 : (k2 + b) == (k2 + (k1 + a))
  lem1 = cong (λ q → k2 + q) b (k1 + a) (==-sym [k1+a==b])
 
  lem2 : (k2 + (k1 + a)) == ((k2 + k1) + a)
  lem2 = a+[b+c]==[a+b]+c k2 k1 a

  lem3 : ((k2 + k1) + a) == c
  lem3 = ==-trans (==-sym (==-trans lem1 lem2)) [k2+b==c]

  proof = ((k2 + k1) , lem3)


<-antirefl : (x : Nat) → ¬ ( x < x)
<-antirefl x [x<x] = ¬[x<x] x [x<x]

<-trans : (a b c : Nat) → (a < b) → (b < c) → (a < c)
<-trans a b c (k1 , [sk1+a==b]) (k2 , [sk2+b==c]) = ((k2 + (suc k1)) , proof)
 where
  lem1 : ((suc k2) + ((suc k1) + a)) == ((suc k2) + b)
  lem1 = cong (λ q → ((suc k2) + q)) ((suc k1) + a) b [sk1+a==b]

  lem2 : ((suc k2) + ((suc k1) + a)) == (((suc k2) + (suc k1)) + a)
  lem2 = a+[b+c]==[a+b]+c (suc k2) (suc k1) a

  proof = ==-trans (==-sym lem2) (==-trans lem1 [sk2+b==c])



x<y-implies-x≠y : (x y : Nat) -> x < y -> x ≠ y
x<y-implies-x≠y x y (k , [sk+x=y]) [x=y] = contradiction
 where
  f : Nat -> Nat
  f n = ((suc k) + n)

  lem1 : ((suc k) + x) == ((suc k) + y)
  lem1 = cong f x y [x=y]

  lem2 : ((suc k) + y) == y
  lem2 = ==-trans (==-sym lem1) [sk+x=y]

  lem3 : y < y
  lem3 = (k , lem2)

  contradiction = ¬[x<x] y lem3

x≤[if-x-gte-y-x-y]-ind : (x y : Nat) -> (x ≤ (if (x gte y) then x else y)) -> ((suc x) ≤ (if ((suc x) gte (suc y)) then (suc x) else (suc y)))
x≤[if-x-gte-y-x-y]-ind x y hyp = proof
 where
  lem1 : ((suc x) gte (suc y)) == (x gte y)
  lem1 = refl

  f : Bool -> Nat
  f b = if b then (suc x) else (suc y)

  lem2 : (if ((suc x) gte (suc y)) then (suc x) else (suc y)) == (if (x gte y) then (suc x) else (suc y))
  lem2 = cong f ((suc x) gte (suc y)) (x gte y) refl

  P : Nat -> Set
  P n = x ≤ n

  P-suc : Nat -> Set
  P-suc n = (suc x) ≤ n

  lem3 : ((suc x) ≤ (if ((suc x) gte (suc y)) then (suc x) else (suc y))) == ((suc x) ≤ (if (x gte y) then (suc x) else (suc y)))
  lem3 = cong P-suc (if ((suc x) gte (suc y)) then (suc x) else (suc y)) (if (x gte y) then (suc x) else (suc y)) lem2

  lem4 : ((suc x) ≤ (if (x gte y) then (suc x) else (suc y))) == (if (x gte y) then ((suc x) ≤ (suc x)) else ((suc x) ≤ (suc y)))
  lem4 = f[if-b-x-y]==[if-b-fx-fy] P-suc (x gte y)

  lem5 : (x ≤ (if (x gte y) then x else y)) == (if (x gte y) then (x ≤ x) else (x ≤ y))
  lem5 = f[if-b-x-y]==[if-b-fx-fy] P (x gte y)

  lem6 : (x ≤ x) -> (suc x) ≤ (suc x)
  lem6 hyp = (z , refl)

  lem7 : (x ≤ y) -> (suc x) ≤ (suc y)
  lem7 hyp = ((π₁ hyp) , [k+sx=sy])
   where
    sublem7,1 : ((π₁ hyp) + (suc x)) == suc ((π₁ hyp) + x)
    sublem7,1 = x+suc-y==suc[x+y] (π₁ hyp) x

    sublem7,2 : suc ((π₁ hyp) + x) == suc y
    sublem7,2 = cong suc ((π₁ hyp) + x) y (π₂ hyp)

    [k+sx=sy] = ==-trans sublem7,1 sublem7,2

  lem8 : (if (x gte y) then (x ≤ x) else (x ≤ y)) -> (if (x gte y) then ((suc x) ≤ (suc x)) else ((suc x) ≤ (suc y)))
  lem8 = x->x',y->y'-implies-[if-b-x-y]->[if-b-x'-y'] lem6 lem7 (x gte y)

  lem9 : (x ≤ (if (x gte y) then x else y)) -> (if (x gte y) then (x ≤ x) else (x ≤ y))
  lem9 = A==B-implies-A-implies-B  {-(x ≤ (if (x gte y) then x else y)) (if (x gte y) then (x ≤ x) else (x ≤ y)) -}lem5

  lem10 : (if (x gte y) then ((suc x) ≤ (suc x)) else ((suc x) ≤ (suc y))) -> ((suc x) ≤ (if (x gte y) then (suc x) else (suc y)))
  lem10 = A==B-implies-A-implies-B {-(if (x gte y) then ((suc x) ≤ (suc x)) else ((suc x) ≤ (suc y))) ((suc x) ≤ (if (x gte y) then (suc x) else (suc y)))-} (==-sym lem4)

  lem11 : ((suc x) ≤ (if (x gte y) then (suc x) else (suc y))) -> ((suc x) ≤ (if ((suc x) gte (suc y)) then (suc x) else (suc y)))
  lem11 = A==B-implies-A-implies-B refl

  proof = lem11 (lem10 (lem8 (lem9 hyp)))


x≤[if-x-gte-y-x-y] : (x y : Nat) -> (x ≤ (if (x gte y) then x else y))
x≤[if-x-gte-y-x-y] z z = (z , refl)
x≤[if-x-gte-y-x-y] z (suc y) = (suc y , x+0==x (suc y))
x≤[if-x-gte-y-x-y] (suc x) z = (z , refl)
x≤[if-x-gte-y-x-y] (suc x) (suc y) = x≤[if-x-gte-y-x-y]-ind x y (x≤[if-x-gte-y-x-y] x y)


x≤y->sx≤sy : (x y : Nat) -> x ≤ y -> (suc x) ≤ (suc y)
x≤y->sx≤sy x y hyp = proof
 where
  lem1 : ((π₁ hyp) + (suc x)) == suc ((π₁ hyp) + x)
  lem1 = x+suc-y==suc[x+y] (π₁ hyp) x

  lem2 : suc ((π₁ hyp) + x) == suc y
  lem2 = cong suc ((π₁ hyp) + x) y (π₂ hyp)

  proof = ((π₁ hyp) , ==-trans lem1 lem2)

y≤[if-x-gte-y-x-y]-ind : (x y : Nat) -> (y ≤ (if (x gte y) then x else y)) -> ((suc y) ≤ (if ((suc x) gte (suc y)) then (suc x) else (suc y)))
y≤[if-x-gte-y-x-y]-ind x y hyp = proof
 where
  P : Nat -> Set
  P q = y ≤ q

  P-suc : Nat -> Set
  P-suc q = (suc y) ≤ q

  lem1 : ((suc y) ≤ (if ((suc x) gte (suc y)) then (suc x) else (suc y))) == (if ((suc x) gte (suc y)) then ((suc y) ≤ (suc x)) else ((suc y) ≤ (suc y)))
  lem1 = f[if-b-x-y]==[if-b-fx-fy] P-suc ((suc x) gte (suc y))

  lem2 : (if ((suc x) gte (suc y)) then ((suc y) ≤ (suc x)) else ((suc y) ≤ (suc y))) == (if (x gte y) then ((suc y) ≤ (suc x)) else ((suc y) ≤ (suc y)))
  lem2 = refl

  lem3 : (y ≤ (if (x gte y) then x else y)) == (if (x gte y) then (y ≤ x) else (y ≤ y))
  lem3 = f[if-b-x-y]==[if-b-fx-fy] P (x gte y)

  
  lem4 : (y ≤ x) -> (suc y) ≤ (suc x)
  lem4 = x≤y->sx≤sy y x

  lem5 : (y ≤ y) -> (suc y) ≤ (suc y)
  lem5 = x≤y->sx≤sy y y

  lem6 : (if (x gte y) then (y ≤ x) else (y ≤ y)) -> (if (x gte y) then ((suc y) ≤ (suc x)) else ((suc y) ≤ (suc y)))
  lem6 = x->x',y->y'-implies-[if-b-x-y]->[if-b-x'-y'] lem4 lem5 (x gte y)

  lem7 : (y ≤ (if (x gte y) then x else y)) -> (if (x gte y) then (y ≤ x) else (y ≤ y))
  lem7 = A==B-implies-A-implies-B lem3

  lem8 : (if (x gte y) then ((suc y) ≤ (suc x)) else ((suc y) ≤ (suc y))) == ((suc y) ≤ (if ((suc x) gte (suc y)) then (suc x) else (suc y)))
  lem8 = ==-sym (==-trans lem1 lem2)

  lem9 : (if (x gte y) then ((suc y) ≤ (suc x)) else ((suc y) ≤ (suc y))) -> ((suc y) ≤ (if ((suc x) gte (suc y)) then (suc x) else (suc y)))
  lem9 = A==B-implies-A-implies-B lem8

  proof = lem9 (lem6 (lem7 hyp))

y≤[if-x-gte-y-x-y] : (x y : Nat) -> (y ≤ (if (x gte y) then x else y))
y≤[if-x-gte-y-x-y] z z = (z , refl)
y≤[if-x-gte-y-x-y] z (suc y) = (z , refl)
y≤[if-x-gte-y-x-y] (suc x) z = (suc x , x+0==x (suc x))
y≤[if-x-gte-y-x-y] (suc x) (suc y) = y≤[if-x-gte-y-x-y]-ind x y (y≤[if-x-gte-y-x-y] x y)


n≤sucn : (x : Nat) → x ≤ (suc x)
n≤sucn x = ((suc z) , refl)

n<sucn : (x : Nat) → x < (suc x)
n<sucn x = (z , refl)

[x<sucy]→[x≤y] : (x y : Nat) → x < (suc y) → x ≤ y
[x<sucy]→[x≤y] x y (k , [sk+x==sy]) = (k , suc-inj (k + x) y [sk+x==sy])



renaming-vars-doesnt-change-height-1 : (t : LambdaTerm) -> (x y : LambdaVar) -> height t == height (subst1 t x (Var y))



renaming-vars-doesnt-change-height-1b-ind-Abs : (k : Nat) -> ((e : LambdaTerm) -> height e == k -> (x y : LambdaVar) -> (n : Nat) -> height e == height (first (subst-helper1 e x (Var y) n))) -> (v : LambdaVar) (e : LambdaTerm) -> height e == k -> (x y : LambdaVar) -> (n : Nat) -> height (Abs v e) == height (first (subst-helper1 (Abs v e) x (Var y) n))
renaming-vars-doesnt-change-height-1b-ind-Abs k hyp1 v e hyp2 x y n = proof
 where
  b = LambdaVar-eq v x
  v∈[y] = list-in (FV (Var y)) v
  e[v=n+1] = subst-helper1 e v (Var (V (suc n))) (suc n)
  e[v=n+1][x=y] = subst-helper1 (first e[v=n+1]) x (Var y) (suc n)
  e[x=y] = subst-helper1 e x (Var y) n

  h₀ = height (Abs v e)

  h = h₀ == height (first (subst-helper1 (Abs v e) x (Var y) n))

  h₁ = h₀ == h₀

  hₑ = height e
  

  h₂,₃ =
   h₀ == 
   height( first (
    if v∈[y] then
     ((Abs (V (suc n)) (first e[v=n+1][x=y])) , (second e[v=n+1][x=y]))
    else 
     ((Abs v (first e[x=y])) , (second e[x=y])) -- just do the replacement in the lambda body
   ))

  h₂-a = height e == height (first e[v=n+1])
  h₂-b = height (first e[v=n+1]) == height (first e[v=n+1][x=y])

  h₂ = h₀ == (height (Abs (V (suc n)) (first e[v=n+1][x=y])))
  h₂' = suc (height e) == suc (height (first e[v=n+1][x=y]))
  
  h₃ = h₀ == (height (Abs v (first e[x=y])))
  h₃' = suc (height e) == suc (height (first e[x=y]))
  

  h₂,₃' = (if v∈[y] then h₂' else h₃')

  h' = if b then h₁ else h₂,₃
  h'' = if b then h₁ else h₂,₃'

  P : Pair LambdaTerm Nat → Set
  P q = height (Abs v e) == height (first q)

  lem1 : h₂,₃ == h₂,₃'
  lem1 = f[if-b-x-y]==[if-b-fx-fy] P v∈[y]


  lem2 : h == h'
  lem2 = f[if-b-x-y]==[if-b-fx-fy] P b

  lem3 : h' == h''
  lem3 = cong (λ q → (if b then h₁ else q)) h₂,₃ h₂,₃' lem1
  
  lem-h₁ : h₁
  lem-h₁ = refl

  lem-h₂-a : h₂-a
  lem-h₂-a = hyp1 e hyp2 v (V (suc n)) (suc n)

  lem-h₂-b : h₂-b
  lem-h₂-b = hyp1 (first e[v=n+1]) (==-trans (==-sym lem-h₂-a) hyp2) x y (suc n)

-- h₂' = suc (height e) == suc (height (first e[v=n+1][x=y]))
  lem-h₂ : h₂
  lem-h₂ = cong suc (height e) (height (first e[v=n+1][x=y])) (==-trans lem-h₂-a lem-h₂-b)

  lem-h₃ : h₃
  lem-h₃ = cong suc (height e) (height (first e[x=y])) (hyp1 e hyp2 x y n)

  lem-h₂,₃ : h₂,₃
  lem-h₂,₃ = P[x]+P[y]-implies-P[if-Q-then-x-else-y] P lem-h₂ lem-h₃ v∈[y]

 
  proof = P[x]+P[y]-implies-P[if-Q-then-x-else-y] P lem-h₁ lem-h₂,₃ b
{-
  lem1 :

   height (first (subst-helper1 (Abs v e) x (Var y) n)) ==
   if b then 
    (height (Abs v e))
   else (
    if (list-in (FV (Var y)) v) then
     (height (Abs (V (suc n)) (first e[v=n+1][x=y])))
    else 
     (height (Abs v (first (subst-helper1 e x (Var y) n)))) -- just do the replacement in the lambda body
   )
-}
  
--  proof


renaming-vars-doesnt-change-height-1b : (k : Nat) -> (t : LambdaTerm) -> height t == k -> (x y : LambdaVar) -> (n : Nat) -> height t == height (first (subst-helper1 t x (Var y) n))
renaming-vars-doesnt-change-height-1b k (Var v) hyp x y n = proof-Var
 where
  v==x = LambdaVar-eq v x
  
  lem1 :
   height (first (subst-helper1 (Var v) x (Var y) n))
    ==
   (if v==x then z else z)
   
  lem1 = f[if-b-x-y]==[if-b-fx-fy] height v==x

  lem2 : (if v==x then z else z) == z
  lem2 = [if-b-x-x]==x v==x

  proof-Var = ==-sym (==-trans lem1 lem2)
renaming-vars-doesnt-change-height-1b k (App t s) hyp x y n = proof-App
 where
  t[x=y] = subst-helper1 t x (Var y) n
  s[x=y] = subst-helper1 s x (Var y) (second t[x=y])

  lem1 : height (App (first t[x=y]) (first s[x=y])) == suc (max (height (first t[x=y])) (height (first s[x=y])))
  lem1 = refl

  lem2 : height t == height (first t[x=y])
  lem2 = renaming-vars-doesnt-change-height-1b (height t) t refl x y n

  lem3 : height s == height (first s[x=y])
  lem3 = renaming-vars-doesnt-change-height-1b (height s) s refl x y (second t[x=y])
  
  lem4 : height (App t s) == suc (max (height t) (height s))
  lem4 = refl

  lem5 : suc (max (height t) (height s)) == suc (max (height (first t[x=y])) (height s))
  lem5 = cong (λ q → suc (max q (height s))) (height t) (height (first t[x=y])) lem2

  lem6 : suc (max (height (first t[x=y])) (height s)) == suc (max (height (first t[x=y])) (height (first s[x=y])))
  lem6 = cong (λ q → suc (max (height (first t[x=y])) q)) (height s) (height (first s[x=y])) lem3

  proof-App = ==-trans lem4 (==-trans lem5 (==-trans lem6 (==-sym lem1)))
renaming-vars-doesnt-change-height-1b k (Abs v e) hyp x y n = renaming-vars-doesnt-change-height-1b-ind-Abs (height e) (renaming-vars-doesnt-change-height-1b (height e)) v e refl x y n

renaming-vars-doesnt-change-height-1c : (t : LambdaTerm) -> (x y : LambdaVar) -> (n : Nat) -> height t == height (first (subst-helper1 t x (Var y) n))
renaming-vars-doesnt-change-height-1c t x y n = renaming-vars-doesnt-change-height-1b (height t) t refl x y n





-- substituting-other-vars-first-is-same-as-substituting-last-var : 
subst1-lemma : (e' : LambdaTerm) -> (v' : LambdaVar) -> (n' k' : Nat) -> (maxVar e') ≤ n' -> (maxVar e') ≤ k' -> subst-helper1 e' v' (Var (V (suc k'))) (suc k') == subst-helper1 (first (subst-helper1 e' v' (Var (V (suc n'))) (suc k'))) (V (suc n')) (Var (V (suc k'))) (suc k')


FVin≤FVout1-ind-Abs : (k : Nat) -> ((e : LambdaTerm) (x : LambdaVar) (r : LambdaTerm) (n : Nat) -> height e == k -> n ≤ (second (subst-helper1 e x r n))) -> (e : LambdaTerm) (v : LambdaVar) (x : LambdaVar) (r : LambdaTerm) (n : Nat) -> height e == k -> n ≤ (second (subst-helper1 (Abs v e) x r n))
FVin≤FVout1-ind-Abs k hyp1 e v x r n hyp2 = proof
 where
  inner-nocap = ((Abs v (first (subst-helper1 e x r n))) , (second (subst-helper1 e x r n)))

  inner-cap = ((Abs (V (suc n)) (first (subst-helper1 (first (subst-helper1 e v (Var (V (suc n))) (suc n))) x r (suc n)))) , second (subst-helper1 (first (subst-helper1 e v (Var (V (suc n))) (suc n))) x r (suc n))) -- subst it for a fresh var in the replacer, then do the replacement

  inner =
    if (list-in (FV r) v) then inner-cap else inner-nocap -- just do the replacement in the lambda body



  lem1 : subst-helper1 (Abs v e) x r n == ( if (LambdaVar-eq v x) then ((Abs v e) , n) else inner )
  lem1 = refl

  lem2 : second (subst-helper1 (Abs v e) x r n) == second ( if (LambdaVar-eq v x) then ((Abs v e) , n) else inner )
  lem2 = refl

  lem3 : second ( if (LambdaVar-eq v x) then ((Abs v e) , n) else inner ) == (if (LambdaVar-eq v x) then (second ((Abs v e) , n)) else (second inner))
  lem3 = f[if-b-x-y]==[if-b-fx-fy] second (LambdaVar-eq v x)

  lem4 : second inner == (if (list-in (FV r) v) then (second inner-cap) else (second inner-nocap))
  lem4 = f[if-b-x-y]==[if-b-fx-fy] second (list-in (FV r) v)

  lem5 : second inner-nocap == (second (subst-helper1 e x r n))
  lem5 = refl

  lem6 : second inner-cap == (second (subst-helper1 (first (subst-helper1 e v (Var (V (suc n))) (suc n))) x r (suc n)))
  lem6 = refl

  lem7 :
   (if (LambdaVar-eq v x) then (second ((Abs v e) , n)) else (second inner)) ==
   (if (LambdaVar-eq v x) then
     (second ((Abs v e) , n))
    else
     (if (list-in (FV r) v) then
       (second (subst-helper1 (first (subst-helper1 e v (Var (V (suc n))) (suc n))) x r (suc n)))
      else
       (second (subst-helper1 e x r n))
     )
   )
   
  lem7 =
   cong
    (λ q → (if (LambdaVar-eq v x) then (second ((Abs v e) , n)) else q))
    (second inner)
    (if (list-in (FV r) v) then
       (second (subst-helper1 (first (subst-helper1 e v (Var (V (suc n))) (suc n))) x r (suc n)))
      else
       (second (subst-helper1 e x r n))
    )
    lem4

  lem8 :
   second (subst-helper1 (Abs v e) x r n) == 
   (if (LambdaVar-eq v x) then
     n
    else
     (if (list-in (FV r) v) then
       (second (subst-helper1 (first (subst-helper1 e v (Var (V (suc n))) (suc n))) x r (suc n)))
      else
       (second (subst-helper1 e x r n))
     )
   )
  lem8 = ==-trans lem2 (==-trans lem3 lem7)
  
  P : Nat -> Set
  P q = n ≤ q

  lem9 :
   (n ≤ (if (LambdaVar-eq v x) then
     n
    else
     (if (list-in (FV r) v) then
       (second (subst-helper1 (first (subst-helper1 e v (Var (V (suc n))) (suc n))) x r (suc n)))
      else
       (second (subst-helper1 e x r n))
     )
   ))
   ==
   (if (LambdaVar-eq v x) then
     (n ≤ n)
    else
     (n ≤ (if (list-in (FV r) v) then
       (second (subst-helper1 (first (subst-helper1 e v (Var (V (suc n))) (suc n))) x r (suc n)))
      else
       (second (subst-helper1 e x r n))
     ))
   )
  lem9 =  f[if-b-x-y]==[if-b-fx-fy] P (LambdaVar-eq v x)

  lem10 :
     (n ≤ (if (list-in (FV r) v) then
       (second (subst-helper1 (first (subst-helper1 e v (Var (V (suc n))) (suc n))) x r (suc n)))
      else
       (second (subst-helper1 e x r n))
     )) ==
     (if (list-in (FV r) v) then
       (n ≤ (second (subst-helper1 (first (subst-helper1 e v (Var (V (suc n))) (suc n))) x r (suc n))))
      else
       (n ≤ (second (subst-helper1 e x r n)))
     )
  lem10 = f[if-b-x-y]==[if-b-fx-fy] P (list-in (FV r) v)


  -- two of the three cases down but once again we might have to do
  -- induction over height rather than subterms.
  lem11 : (n ≤ (second (subst-helper1 e x r n)))
  lem11 = hyp1 e x r n hyp2

  lem12 : (suc n) ≤ (second (subst-helper1 e v (Var (V (suc n))) (suc n)))
  lem12 = hyp1 e v (Var (V (suc n))) (suc n) hyp2

  lem13 : (n ≤ n)
  lem13 = ≤-refl n




  proof

FVin≤FVout1 : (t : LambdaTerm) (x : LambdaVar) (r : LambdaTerm) (n : Nat) -> n ≤ (second (subst-helper1 t x r n))
FVin≤FVout1 (Var (V v)) x r n = ≤-refl n
FVin≤FVout1 (App s t) x r n = proof-App
 where
  s[x=r] = subst-helper1 s x r n
  t[x=r] = subst-helper1 t x r (second s[x=r])

  lem1 : (subst-helper1 (App s t) x r n) == ((App (first s[x=r]) (first t[x=r])) , second t[x=r] )
  lem1 = refl

  lem2 : n ≤ (second s[x=r])
  lem2 = FVin≤FVout1 s x r n

  lem3 : (second s[x=r]) ≤ (second t[x=r])
  lem3 = FVin≤FVout1 t x r (second s[x=r])

  proof-App : n ≤ (second t[x=r])
  proof-App = ≤-trans lem2 lem3


FVin≤FVout1 (Abs v e) x r n = proof-Abs
 where
  inner-nocap = ((Abs v (first (subst-helper1 e x r n))) , (second (subst-helper1 e x r n)))

  inner-cap = ((Abs (V (suc n)) (first (subst-helper1 (first (subst-helper1 e v (Var (V (suc n))) (suc n))) x r (suc n)))) , second (subst-helper1 (first (subst-helper1 e v (Var (V (suc n))) (suc n))) x r (suc n))) -- subst it for a fresh var in the replacer, then do the replacement

  inner =
    if (list-in (FV r) v) then inner-cap else inner-nocap -- just do the replacement in the lambda body



  lem1 : subst-helper1 (Abs v e) x r n == ( if (LambdaVar-eq v x) then ((Abs v e) , n) else inner )
  lem1 = refl

  lem2 : second (subst-helper1 (Abs v e) x r n) == second ( if (LambdaVar-eq v x) then ((Abs v e) , n) else inner )
  lem2 = refl

  lem3 : second ( if (LambdaVar-eq v x) then ((Abs v e) , n) else inner ) == (if (LambdaVar-eq v x) then (second ((Abs v e) , n)) else (second inner))
  lem3 = f[if-b-x-y]==[if-b-fx-fy] second (LambdaVar-eq v x)

  lem4 : second inner == (if (list-in (FV r) v) then (second inner-cap) else (second inner-nocap))
  lem4 = f[if-b-x-y]==[if-b-fx-fy] second (list-in (FV r) v)

  lem5 : second inner-nocap == (second (subst-helper1 e x r n))
  lem5 = refl

  lem6 : second inner-cap == (second (subst-helper1 (first (subst-helper1 e v (Var (V (suc n))) (suc n))) x r (suc n)))
  lem6 = refl

  lem7 :
   (if (LambdaVar-eq v x) then (second ((Abs v e) , n)) else (second inner)) ==
   (if (LambdaVar-eq v x) then
     (second ((Abs v e) , n))
    else
     (if (list-in (FV r) v) then
       (second (subst-helper1 (first (subst-helper1 e v (Var (V (suc n))) (suc n))) x r (suc n)))
      else
       (second (subst-helper1 e x r n))
     )
   )
   
  lem7 =
   cong
    (λ q → (if (LambdaVar-eq v x) then (second ((Abs v e) , n)) else q))
    (second inner)
    (if (list-in (FV r) v) then
       (second (subst-helper1 (first (subst-helper1 e v (Var (V (suc n))) (suc n))) x r (suc n)))
      else
       (second (subst-helper1 e x r n))
    )
    lem4

  lem8 :
   second (subst-helper1 (Abs v e) x r n) == 
   (if (LambdaVar-eq v x) then
     n
    else
     (if (list-in (FV r) v) then
       (second (subst-helper1 (first (subst-helper1 e v (Var (V (suc n))) (suc n))) x r (suc n)))
      else
       (second (subst-helper1 e x r n))
     )
   )
  lem8 = ==-trans lem2 (==-trans lem3 lem7)
  
  P : Nat -> Set
  P q = n ≤ q

  lem9 :
   (n ≤ (if (LambdaVar-eq v x) then
     n
    else
     (if (list-in (FV r) v) then
       (second (subst-helper1 (first (subst-helper1 e v (Var (V (suc n))) (suc n))) x r (suc n)))
      else
       (second (subst-helper1 e x r n))
     )
   ))
   ==
   (if (LambdaVar-eq v x) then
     (n ≤ n)
    else
     (n ≤ (if (list-in (FV r) v) then
       (second (subst-helper1 (first (subst-helper1 e v (Var (V (suc n))) (suc n))) x r (suc n)))
      else
       (second (subst-helper1 e x r n))
     ))
   )
  lem9 =  f[if-b-x-y]==[if-b-fx-fy] P (LambdaVar-eq v x)

  lem10 :
     (n ≤ (if (list-in (FV r) v) then
       (second (subst-helper1 (first (subst-helper1 e v (Var (V (suc n))) (suc n))) x r (suc n)))
      else
       (second (subst-helper1 e x r n))
     )) ==
     (if (list-in (FV r) v) then
       (n ≤ (second (subst-helper1 (first (subst-helper1 e v (Var (V (suc n))) (suc n))) x r (suc n))))
      else
       (n ≤ (second (subst-helper1 e x r n)))
     )
  lem10 = f[if-b-x-y]==[if-b-fx-fy] P (list-in (FV r) v)


  -- two of the three cases down but once again we might have to do
  -- induction over height rather than subterms.
  lem11 : (n ≤ (second (subst-helper1 e x r n)))
  lem11 = FVin≤FVout1 e x r n

  lem12 : (suc n) ≤ (second (subst-helper1 e v (Var (V (suc n))) (suc n)))
  lem12 = FVin≤FVout1 e v (Var (V (suc n))) (suc n)

  lem13 : (n ≤ n)
  lem13 = ≤-refl n

  
-- (second (subst-helper1 (first (subst-helper1 e v (Var (V (suc n))) (suc n))) x r (suc n))))
--  lem14 : (suc n) ≤ 


-- dae mark  

  proof-Abs




subst1-lemma (Var (V x')) v' n' k' hyp1' hyp2' = proof-Var
   where
    --x'[v':=k'+1]
    sublem1 : subst-helper1 (Var (V x')) v' (Var (V (suc k'))) (suc k') == ((if (LambdaVar-eq (V x') v') then (Var (V (suc k'))) else (Var (V x'))) , (suc k'))
    sublem1 = refl

    first-sublem1 : first (subst-helper1 (Var (V x')) v' (Var (V (suc k'))) (suc k')) == (if (LambdaVar-eq (V x') v') then (Var (V (suc k'))) else (Var (V x')))
    first-sublem1 = refl



    --(x'[v':=n'+1],k'+1)
    sublem2 : subst-helper1 (Var (V x')) v' (Var (V (suc n'))) (suc k') == ((if (LambdaVar-eq (V x') v') then (Var (V (suc n'))) else (Var (V x'))) , (suc k'))
    sublem2 = refl

    --x'[v':=n'+1]
    sublem3 : first (subst-helper1 (Var (V x')) v' (Var (V (suc n'))) (suc k')) == (if (LambdaVar-eq (V x') v') then (Var (V (suc n'))) else (Var (V x')))
    sublem3 = refl

    subst-rest : LambdaTerm -> LambdaTerm
    subst-rest q = first (subst-helper1 q (V (suc n')) (Var (V (suc k'))) (suc k'))

    subst-rest2 : LambdaTerm -> Nat
    subst-rest2 q = second (subst-helper1 q (V (suc n')) (Var (V (suc k'))) (suc k'))


    subst-decomp : first (subst-helper1 (first (subst-helper1 (Var (V x')) v' (Var (V (suc n'))) (suc k'))) (V (suc n')) (Var (V (suc k'))) (suc k')) == (if (LambdaVar-eq (V x') v') then (first (subst-helper1 (Var (V (suc n'))) (V (suc n')) (Var (V (suc k'))) (suc k'))) else (first (subst-helper1 (Var (V x')) (V (suc n')) (Var (V (suc k'))) (suc k'))))
    subst-decomp = f[if-b-x-y]==[if-b-fx-fy] subst-rest (LambdaVar-eq (V x') v')

    subst-decomp2 : second (subst-helper1 (first (subst-helper1 (Var (V x')) v' (Var (V (suc n'))) (suc k'))) (V (suc n')) (Var (V (suc k'))) (suc k')) == (if (LambdaVar-eq (V x') v') then (second (subst-helper1 (Var (V (suc n'))) (V (suc n')) (Var (V (suc k'))) (suc k'))) else (second (subst-helper1 (Var (V x')) (V (suc n')) (Var (V (suc k'))) (suc k'))))
    subst-decomp2 = f[if-b-x-y]==[if-b-fx-fy] subst-rest2 (LambdaVar-eq (V x') v')

    seconds-equal-part-1 : (second (subst-helper1 (Var (V (suc n'))) (V (suc n')) (Var (V (suc k'))) (suc k'))) == (suc k')
    seconds-equal-part-1 = refl

    seconds-equal-part-2 : (second (subst-helper1 (Var (V x')) (V (suc n')) (Var (V (suc k'))) (suc k'))) == (suc k')
    seconds-equal-part-2 = refl

    seconds-equal-part-3 : (if (LambdaVar-eq (V x') v') then (second (subst-helper1 (Var (V (suc n'))) (V (suc n')) (Var (V (suc k'))) (suc k'))) else (second (subst-helper1 (Var (V x')) (V (suc n')) (Var (V (suc k'))) (suc k')))) == (suc k')
    seconds-equal-part-3 = [if-b-x-x]==x (LambdaVar-eq (V x') v')

    seconds-equal-part-4 : second (subst-helper1 (first (subst-helper1 (Var (V x')) v' (Var (V (suc n'))) (suc k'))) (V (suc n')) (Var (V (suc k'))) (suc k')) == (suc k')
    seconds-equal-part-4 = ==-trans subst-decomp2 seconds-equal-part-3

    {-
     so prove:
     a) first (subst-helper1 (Var (V (suc n'))) (V (suc n')) (Var (V (suc k'))) (suc k')) == Var (V (suc k'))

     sublem10 : subst-helper1 (Var (V (suc n'))) (V (suc n')) (Var (V (suc k'))) (suc k') == ((Var (V (suc k'))) , (suc k'))

     first-sublem10 : first (subst-helper1 (Var (V (suc n'))) (V (suc n')) (Var (V (suc k'))) (suc k')) == (Var (V (suc k')))

 
     b) first (subst-helper1 (Var (V x'))) (V (suc n')) (Var (V (suc k'))) (suc k') == (Var (V x'))

    sublem24 : first (subst-helper1 (Var (V x')) (V (suc n')) (Var (V (suc k'))) (suc k')) == (Var (V x'))
    sublem24 = ==-trans refl (==-trans sublem22 sublem23)

    -}



    -- for the (Var (V (suc n'))) case:
    sublem4 : subst-helper1 (Var (V (suc n'))) (V (suc n')) (Var (V (suc k'))) (suc k') == ((if (LambdaVar-eq (V (suc n')) (V (suc n'))) then (Var (V (suc k'))) else (Var (V (suc n')))) , (suc k'))
    sublem4 = refl

    sublem5 : LambdaVar-eq (V (suc n')) (V (suc n')) == true
    sublem5 = LambdaVar-eq-refl (V (suc n'))

    f1 : Bool -> LambdaTerm
    f1 b = if b then (Var (V (suc k'))) else (Var (V (suc n')))

    sublem6 : (if (LambdaVar-eq (V (suc n')) (V (suc n'))) then (Var (V (suc k'))) else (Var (V (suc n')))) == (if true then (Var (V (suc k'))) else (Var (V (suc n'))))
    sublem6 = cong f1 (LambdaVar-eq (V (suc n')) (V (suc n'))) true sublem5

    sublem7 : (if true then (Var (V (suc k'))) else (Var (V (suc n')))) == (Var (V (suc k')))
    sublem7 = refl

    sublem8 : (if (LambdaVar-eq (V (suc n')) (V (suc n'))) then (Var (V (suc k'))) else (Var (V (suc n')))) == (Var (V (suc k')))
    sublem8 = ==-trans sublem6 sublem7

    f2 : LambdaTerm -> Pair LambdaTerm Nat
    f2 t = (t , (suc k'))

    sublem9 : ((if (LambdaVar-eq (V (suc n')) (V (suc n'))) then (Var (V (suc k'))) else (Var (V (suc n')))) , (suc k')) == ((Var (V (suc k'))) , (suc k'))
    sublem9 = cong f2 (if (LambdaVar-eq (V (suc n')) (V (suc n'))) then (Var (V (suc k'))) else (Var (V (suc n')))) (Var (V (suc k'))) sublem8 

    sublem10 : subst-helper1 (Var (V (suc n'))) (V (suc n')) (Var (V (suc k'))) (suc k') == ((Var (V (suc k'))) , (suc k'))
    sublem10 = ==-trans sublem4 sublem9

    first-sublem10 : first (subst-helper1 (Var (V (suc n'))) (V (suc n')) (Var (V (suc k'))) (suc k')) == (Var (V (suc k')))
    first-sublem10 = cong first (subst-helper1 (Var (V (suc n'))) (V (suc n')) (Var (V (suc k'))) (suc k')) ((Var (V (suc k'))) , (suc k')) sublem10



    -- for the (Var (V x')) case:
    sublem11 : subst-helper1 (Var (V x')) (V (suc n')) (Var (V (suc k'))) (suc k') == ((if (LambdaVar-eq (V x') (V (suc n'))) then (Var (V (suc k'))) else (Var (V x'))) , (suc k'))
    sublem11 = refl

    sublem12 : maxVar (Var (V x')) == x'
    sublem12 = refl

    sublem13 : LambdaVar-eq (V x') (V (suc n')) == Nat-eq x' (suc n')
    sublem13 = refl

    sublem14 : ((π₁ hyp1') + x') == n'
    sublem14 = π₂ hyp1'

    sublem15 : suc ((π₁ hyp1') + x') == suc n'
    sublem15 = cong suc ((π₁ hyp1') + x') n' sublem14

    sublem16 : suc ((π₁ hyp1') + x') == (suc (π₁ hyp1') + x')
    sublem16 = refl

    sublem17 : (suc (π₁ hyp1') + x') == suc n'
    sublem17 = ==-trans (==-sym sublem16) sublem15

    sublem18 : x' < (suc n')
    sublem18 = ((π₁ hyp1') , sublem17)

    sublem19 : x' ≠ (suc n')
    sublem19 = x<y-implies-x≠y x' (suc n') sublem18

    sublem20 : Nat-eq x' (suc n') == false
    sublem20 = Nat-NEq-implies-neq x' (suc n') sublem19

    sublem21 : LambdaVar-eq (V x') (V (suc n')) == false
    sublem21 = ==-trans sublem13 sublem20

    f3 : Bool -> LambdaTerm
    f3 b = (if b then (Var (V (suc k'))) else (Var (V x')))


    sublem22 : (if (LambdaVar-eq (V x') (V (suc n'))) then (Var (V (suc k'))) else (Var (V x'))) == (if false then (Var (V (suc k'))) else (Var (V x')))
    sublem22 = cong f3 (LambdaVar-eq (V x') (V (suc n'))) false sublem21

    sublem23 : (if false then (Var (V (suc k'))) else (Var (V x'))) == (Var (V x'))
    sublem23 = refl


    sublem24 : first (subst-helper1 (Var (V x')) (V (suc n')) (Var (V (suc k'))) (suc k')) == (Var (V x'))
    sublem24 = ==-trans refl (==-trans sublem22 sublem23)


{-
     so prove:
     a) first (subst-helper1 (Var (V (suc n'))) (V (suc n')) (Var (V (suc k'))) (suc k')) == Var (V (suc k'))

     sublem10 : subst-helper1 (Var (V (suc n'))) (V (suc n')) (Var (V (suc k'))) (suc k') == ((Var (V (suc k'))) , (suc k'))

     first-sublem10 : first (subst-helper1 (Var (V (suc n'))) (V (suc n')) (Var (V (suc k'))) (suc k')) == (Var (V (suc k')))

 
     b) first (subst-helper1 (Var (V x'))) (V (suc n')) (Var (V (suc k'))) (suc k') == (Var (V x'))

    sublem24 : first (subst-helper1 (Var (V x')) (V (suc n')) (Var (V (suc k'))) (suc k')) == (Var (V x'))
    sublem24 = ==-trans refl (==-trans sublem22 sublem23)

    -}

    sublem25 : (if (LambdaVar-eq (V x') v') then (Var (V (suc k'))) else (Var (V x'))) == (if (LambdaVar-eq (V x') v') then (first (subst-helper1 (Var (V (suc n'))) (V (suc n')) (Var (V (suc k'))) (suc k'))) else (first (subst-helper1 (Var (V x')) (V (suc n')) (Var (V (suc k'))) (suc k'))))
    sublem25 = [A=A'&B=B']-implies-[if-b-A-B]==[if-b-A'-B'] (==-sym first-sublem10) (==-sym sublem24) (LambdaVar-eq (V x') v')

    -- oy... getting closer

    sublem26 : (first (subst-helper1 (Var (V x')) v' (Var (V (suc k'))) (suc k'))) == (first (subst-helper1 (first (subst-helper1 (Var (V x')) v' (Var (V (suc n'))) (suc k'))) (V (suc n')) (Var (V (suc k'))) (suc k')))
    sublem26 = ==-trans first-sublem1 (==-trans sublem25 (==-sym subst-decomp))

    {-
    now just prove that the seconds are the same
    and then prove that pairs with equals firsts and equal seconds are equal
    -}

    LHS-seconds-are-equal : (second (subst-helper1 (Var (V x')) v' (Var (V (suc k'))) (suc k'))) == (suc k')
    LHS-seconds-are-equal = refl

    seconds-are-equal : (second (subst-helper1 (Var (V x')) v' (Var (V (suc k'))) (suc k'))) == (second (subst-helper1 (first (subst-helper1 (Var (V x')) v' (Var (V (suc n'))) (suc k'))) (V (suc n')) (Var (V (suc k'))) (suc k')))
    seconds-are-equal = ==-trans LHS-seconds-are-equal (==-sym seconds-equal-part-4)

    proof-Var = pair-extensionality' sublem26 seconds-are-equal
subst1-lemma (App t' s') v' n' k' hyp1' hyp2' = proof-App
   where
    {-
    subst-helper1 e' v' (Var (V (suc k'))) (suc k') == subst-helper1 (first (subst-helper1 e' v' (Var (V (suc n'))) (suc k'))) (V (suc n')) (Var (V (suc k'))) (suc k')
    -}

    vars' = maxVar (App t' s')

    vars-lem1 : vars' == (if ((maxVar t') gte (maxVar s')) then (maxVar t') else (maxVar s'))
    vars-lem1 = refl

    tVars' = maxVar t'
    sVars' = maxVar s'

    tVars'≤vars' : tVars' ≤ (if ((maxVar t') gte (maxVar s')) then (maxVar t') else (maxVar s'))
    tVars'≤vars' = x≤[if-x-gte-y-x-y] tVars' sVars'

    sVars'≤vars' : sVars' ≤ (if ((maxVar t') gte (maxVar s')) then (maxVar t') else (maxVar s'))
    sVars'≤vars' = y≤[if-x-gte-y-x-y] tVars' sVars'

    tVars'≤n' : tVars' ≤ n'
    tVars'≤n' = ≤-trans tVars'≤vars' hyp1'

    tVars'≤k' : tVars' ≤ k'
    tVars'≤k' = ≤-trans tVars'≤vars' hyp2'

    sVars'≤n' : sVars' ≤ n'
    sVars'≤n' = ≤-trans sVars'≤vars' hyp1'
    
    sVars'≤k' : sVars' ≤ k'
    sVars'≤k' = ≤-trans sVars'≤vars' hyp2'
    
    t'[v'=k'+1] = subst-helper1 t' v' (Var (V (suc k'))) (suc k')
    s'[v'=k'+1] = subst-helper1 s' v' (Var (V (suc k'))) (second t'[v'=k'+1])

    

    sublem1 : subst-helper1 (App t' s') v' (Var (V (suc k'))) (suc k') == ((App (first t'[v'=k'+1]) (first s'[v'=k'+1])) , (second s'[v'=k'+1]))
    sublem1 = refl

    sublem2 : t'[v'=k'+1] == (subst-helper1 (first (subst-helper1 t' v' (Var (V (suc n'))) (suc k'))) (V (suc n')) (Var (V (suc k'))) (suc k'))
    sublem2 = subst1-lemma t' v' n' k' tVars'≤n' tVars'≤k'

    -- ok so for this we need a subproof that the freshest var that comes out is always bigger
    -- than the freshest var we put in.
    {-
    sublem3 : s'[v'=k'+1] == (subst-helper1 (first (subst-helper1 s' v' (Var (V (suc n'))) (suc k'))) (V (suc n')) (Var (V (suc k'))) (suc k'))
    sublem3 = sublemma s' v' n' k' sVars'≤n' sVars'≤k'
    -}
   

    proof-App
subst1-lemma (Abs x' e') v' n' k' hyp1' hyp2' = proof-Abs
   where
    proof-Abs








{-
subst-helper1 (Abs x e) v r n = case-Abs
 where
  case-Abs =
   if (LambdaVar-eq x v) then 
    ((Abs x e) , n)
   else (
    if (list-in (FV r) x) then -- if the var is in the replacer
     ((Abs (V (suc n)) capture-avoidingly-substituted-body) , second (subst-helper1 body-with-captured-var-substituted-for-fresh v r (suc n))) -- subst it for a fresh var in the replacer, then do the replacement
    else 
     ((Abs x (first (subst-helper1 e v r n))) , (second (subst-helper1 e v r n))) -- just do the replacement in the lambda body
   )
   where
    -- yea just this right here
    -- this recursive call uses e which is a substructure of (Abs x e),
    -- everything's good with this one, we know it's theoretically heading towards termination
    body-with-captured-var-substituted-for-fresh = first (subst-helper1 e x (Var (V (suc n))) (suc n))

  proof-Abs
-}
{-
using-0-for-freshest-var-doesnt-change-height-1-ind-App : (x : LambdaVar) -> (r : LambdaTerm) -> (t s : LambdaTerm) -> height (subst1 t x r) == height (first (subst-helper1 t x r z)) -> height (subst1 s x r) == height (first (subst-helper1 s x r z)) -> height (subst1 (App t s) x r) == height (first (subst-helper1 (App t s) x r z))
using-0-for-freshest-var-doesnt-change-height-1-ind-App x r t s hyp1 hyp2 = proof
 where
  lem1 : subst1 (App t s) x r == 
  proof




using-0-for-freshest-var-doesnt-change-height-1 : (t : LambdaTerm) -> (x : LambdaVar) -> (r : LambdaTerm) -> height (subst1 t x r) == height (first (subst-helper1 t x r z))
using-0-for-freshest-var-doesnt-change-height-1 (Var v) x r = proof-Var
 where
  lem1 : subst1 (Var v) x r == first (subst-helper1 (Var v) x r z)
  lem1 = refl
  
  proof-Var = cong height (subst1 (Var v) x r) (first (subst-helper1 (Var v) x r z)) lem1
using-0-for-freshest-var-doesnt-change-height-1 (App s t) x r = proof-App
 where
  proof-App
using-0-for-freshest-var-doesnt-change-height-1 (Abs v e) x r = proof-Abs
 where
  proof-Abs
-}

using-different-id-for-freshest-var-doesnt-change-height-1-ind-App : (x : LambdaVar) -> (r : LambdaTerm) -> (m n : Nat) -> ((s : LambdaTerm) -> height s == m -> (k : Nat) -> height (subst1 s x r) == height (first (subst-helper1 s x r k))) -> ((t : LambdaTerm) -> height t == n -> (k : Nat) -> height (subst1 t x r) == height (first (subst-helper1 t x r k))) -> (s t : LambdaTerm) -> height s == m -> height t == n -> (k : Nat) -> height (subst1 (App s t) x r) == height (first (subst-helper1 (App s t) x r k))
using-different-id-for-freshest-var-doesnt-change-height-1-ind-App x r m n hyp1 hyp2 s t hyp3 hyp4 k = proof
 where
  vars = max (maxVar (App s t)) (maxVar r)
  sVars = maxVar s
  tVars = maxVar t
  
  s[x=y] = subst-helper1 s x r vars
  t[x=y] = subst-helper1 t x r (second s[x=y])

  s[x=y]' = subst-helper1 s x r sVars
  t[x=y]' = subst-helper1 t x r tVars

  lem1 : subst1 (App s t) x r == App (first s[x=y]) (first t[x=y])
  lem1 = refl

  lem2 : height (subst1 s x r) == height (first s[x=y])
  lem2 = hyp1 s hyp3 vars

  lem3 : height (subst1 t x r) == height (first t[x=y])
  lem3 = hyp2 t hyp4 (second s[x=y])
  
  lem4 : height (App (first s[x=y]) (first t[x=y])) == suc (max (height (first s[x=y])) (height (first t[x=y])))
  lem4 = refl

  s[x=y]'' = subst-helper1 s x r k
  t[x=y]'' = subst-helper1 t x r (second s[x=y]'')

  lem5 : height (subst1 s x r) == height (first s[x=y]'')
  lem5 = hyp1 s hyp3 k

  lem6 : height (subst1 t x r) == height (first t[x=y]'')
  lem6 = hyp2 t hyp4 (second s[x=y]'')

  lem7 : height (first s[x=y]) == height (first s[x=y]'')
  lem7 = ==-trans (==-sym lem2) lem5

  lem8 : height (first t[x=y]) == height (first t[x=y]'')
  lem8 = ==-trans (==-sym lem3) lem6
  

  lem9 : first (subst-helper1 (App s t) x r k) == App (first s[x=y]'') (first t[x=y]'')
  lem9 = refl

  lem10 : height (App (first s[x=y]'') (first t[x=y]'')) == suc (max (height (first s[x=y]'')) (height (first t[x=y]'')))
  lem10 = refl

  f1 : Nat -> Nat
  f1 q = suc (max q (height (first t[x=y])))

  f2 : Nat -> Nat
  f2 q = suc (max (height (first s[x=y]'')) q)

  lem11 : suc (max (height (first s[x=y])) (height (first t[x=y]))) == suc (max (height (first s[x=y]'')) (height (first t[x=y])))
  lem11 = cong f1 (height (first s[x=y])) (height (first s[x=y]'')) lem7



  lem12 : suc (max (height (first s[x=y]'')) (height (first t[x=y]))) == suc (max (height (first s[x=y]'')) (height (first t[x=y]'')))
  lem12 = cong f2 (height (first t[x=y])) (height (first t[x=y]'')) lem8

  lem13 : height (App (first s[x=y]) (first t[x=y])) == suc (max (height (first s[x=y])) (height (first t[x=y])))
  lem13 = refl

  lem14 : height (subst1 (App s t) x r) == height (App (first s[x=y]) (first t[x=y]))
  lem14 = cong height (subst1 (App s t) x r) (App (first s[x=y]) (first t[x=y])) lem1

  lem15 : height (first (subst-helper1 (App s t) x r k)) == height (App (first s[x=y]'') (first t[x=y]''))
  lem15 = cong height (first (subst-helper1 (App s t) x r k)) (App (first s[x=y]'') (first t[x=y]'')) lem9

  proof = ==-trans lem14 (==-trans lem13 (==-trans lem11 (==-sym (==-trans lem15 (==-trans lem10 (==-sym lem12)))))) 





using-different-id-for-freshest-var-doesnt-change-height-1-ind-Abs : (n : Nat) -> ((e : LambdaTerm) -> height e == n -> (x : LambdaVar) -> (r : LambdaTerm) -> (k : Nat) -> height (subst1 e x r) == height (first (subst-helper1 e x r k))) -> (v : LambdaVar) -> (e : LambdaTerm) -> height e == n -> (x : LambdaVar) -> (r : LambdaTerm) -> (k : Nat) -> ((maxVar (Abs v e)) ≤ k) -> height (subst1 (Abs v e) x r) == height (first (subst-helper1 (Abs v e) x r k))
using-different-id-for-freshest-var-doesnt-change-height-1-ind-Abs n hyp1 v e hyp2 x r k hyp3 = proof
 where

  vars = max (maxVar (Abs v e)) (maxVar r)
  eVars = maxVar e

  lem1 : subst1 (Abs v e) x r == first (subst-helper1 (Abs v e) x r vars)
  lem1 = refl

  val = subst-helper1 (first (subst-helper1 e v (Var (V (suc vars))) (suc vars))) x r (suc vars)
  val' = subst-helper1 (first (subst-helper1 e v (Var (V (suc k))) (suc k))) x r (suc k)

  -- oy... foiled again...
  -- our inductive hypothesis doesn't cover the case that r might be different
  -- works under the assumption that neither substituting a Var nor choosing arbitrary freshest var id
  -- will change the height. but the notion that substituting a Var doesn't change the height is what
  -- we were originally trying to prove! will mutual induction work here? i guess that will depend on
  -- whether every call from replacing-vars-... into using-different-id-... that leads to a call back
  -- into replacing-vars-... is decreasing in some arg.

  lem4 : height e == height (subst1 e v (Var (V (suc vars))))
  lem4 = renaming-vars-doesnt-change-height-1 e v (V (suc vars))

  lem5 : height e == height (subst1 e v (Var (V (suc k))))
  lem5 = renaming-vars-doesnt-change-height-1 e v (V (suc k))

  lem6 : height (subst1 e v (Var (V (suc vars)))) == n
  lem6 = ==-trans (==-sym lem4) hyp2

  lem7 : height (subst1 e v (Var (V (suc k)))) == n
  lem7 = ==-trans (==-sym lem5) hyp2

  lem8 : height (subst1 e v (Var (V (suc vars)))) == height (first (subst-helper1 e v (Var (V (suc vars))) (suc vars)))
  lem8 = hyp1 e hyp2 v (Var (V (suc vars))) (suc vars) 

  lem9 : height (subst1 e v (Var (V (suc k)))) == height (first (subst-helper1 e v (Var (V (suc k))) (suc k)))
  lem9 = hyp1 e hyp2 v (Var (V (suc k))) (suc k)

  lem10 : height (first (subst-helper1 e v (Var (V (suc vars))) (suc vars))) == n
  lem10 = ==-trans (==-sym lem8) lem6

  lem11 : height (first (subst-helper1 e v (Var (V (suc k))) (suc k))) == n
  lem11 = ==-trans (==-sym lem9) lem7

  lem12 : height (subst1 (first (subst-helper1 e v (Var (V (suc vars))) (suc vars))) x r) == height (first (subst-helper1 (first (subst-helper1 e v (Var (V (suc vars))) (suc vars))) x r (suc vars)))
  lem12 = hyp1 (first (subst-helper1 e v (Var (V (suc vars))) (suc vars))) lem10 x r (suc vars)

  lem13 : height (subst1 (first (subst-helper1 e v (Var (V (suc k))) (suc k))) x r) == height (first (subst-helper1 (first (subst-helper1 e v (Var (V (suc k))) (suc k))) x r (suc k)))
  lem13 = hyp1 (first (subst-helper1 e v (Var (V (suc k))) (suc k))) lem11 x r (suc k)

  -- want to prove that LHS of lem12 equals the LHS of lem13
  -- very close

{-
  lem14 : subst-helper1 e v (Var (V (suc vars))) (suc k) == subst-helper1 e (V (suc vars)) (Var (V (suc k))) (suc k)
  lem14 = ...
-}





  lem2 : subst-helper1 (Abs v e) x r vars == 
   (if (LambdaVar-eq v x) then 
    ((Abs v e), vars)
   else (
    if (list-in (FV r) v) then -- if the var is in the replacer
     ((Abs (V (suc vars)) (first val)) , (second val)) -- subst it for a fresh var in the replacer, then do the replacement
    else 
     ((Abs v (first (subst-helper1 e x r vars))), (second (subst-helper1 e x r vars))) -- just do the replacement in the lambda body
   ))
  lem2 = refl

  lem3 : subst-helper1 (Abs v e) x r k ==
   (if (LambdaVar-eq v x) then 
    ((Abs v e), k)
   else (
    if (list-in (FV r) v) then -- if the var is in the replacer
     ((Abs (V (suc k)) (first val')) , (second val')) -- subst it for a fresh var in the replacer, then do the replacement
    else 
     ((Abs v (first (subst-helper1 e x r k))), (second (subst-helper1 e x r k))) -- just do the replacement in the lambda body
   ))
  lem3 = refl

  lem-case1 : height (first ((Abs v e) , vars)) == height (first ((Abs v e), k))
  lem-case1 = refl



  lem-case2-a : height (first ((Abs (V (suc vars)) (first val)) , (second val))) == height (Abs (V (suc vars)) (first val))
  lem-case2-a = refl

  lem-case2-b : height (Abs (V (suc vars)) (first val)) == suc (height (first val))
  lem-case2-b = refl

  lem-case2-c : suc (height (first val')) == height (Abs (V (suc k)) (first val'))
  lem-case2-c = refl

  lem-case2-d : height (Abs (V (suc k)) (first val')) == height (first ((Abs (V (suc k)) (first val')) , (second val')))
  lem-case2-d = refl

  {-
   if we can show that height (first val) == height (first val'), then we'll have proven this case
   and proven the whole theorem.
  -}



  lem-case3-a : height (first ((Abs v (first (subst-helper1 e x r vars))), (second (subst-helper1 e x r vars)))) == height (Abs v (first (subst-helper1 e x r vars)))
  lem-case3-a = refl

  lem-case3-b : height (Abs v (first (subst-helper1 e x r vars))) == suc (height (first (subst-helper1 e x r vars)))
  lem-case3-b = refl

  lem-case3-c : suc (height (first (subst-helper1 e x r k))) == height (Abs v (first (subst-helper1 e x r k)))
  lem-case3-c = refl

  lem-case3-d : height (Abs v (first (subst-helper1 e x r k))) == height (first ((Abs v (first (subst-helper1 e x r k))) , (second (subst-helper1 e x r k))))
  lem-case3-d = refl

  lem-case3-e : height (subst1 e x r) == height (first (subst-helper1 e x r vars))
  lem-case3-e = hyp1 e hyp2 x r vars
  
  lem-case3-f : height (first (subst-helper1 e x r k)) == height (subst1 e x r)
  lem-case3-f = ==-sym (hyp1 e hyp2 x r k)

  lem-case3-g : height (first (subst-helper1 e x r vars)) == height (first (subst-helper1 e x r k))
  lem-case3-g = ==-sym (==-trans lem-case3-f lem-case3-e)

  lem-case3-h : suc (height (first (subst-helper1 e x r vars))) == suc (height (first (subst-helper1 e x r k)))
  lem-case3-h = cong suc (height (first (subst-helper1 e x r vars))) (height (first (subst-helper1 e x r k))) lem-case3-g

  lem-case3 : height (first ((Abs v (first (subst-helper1 e x r vars))), (second (subst-helper1 e x r vars)))) == height (first ((Abs v (first (subst-helper1 e x r k))), (second (subst-helper1 e x r k))))
  lem-case3 = ==-trans lem-case3-a (==-trans lem-case3-b (==-trans lem-case3-h (==-trans lem-case3-c lem-case3-d)))

  {-
   if we can show that height (first (subst-helper1 e x r vars)) == height (first (subst-helper e x r k)), we'll
   have proven this case.
   
  -}


  proof




{-
Note that the Var case holds for arbitrary Nats and the App case holds for arbitrary Nats if the statement holds
for arbitrary Nats for its subterms. This does not work out in Abs case, or in the case of terms that contain
Abs's. By selecting the right Nat to serve as the freshest var id, you can force variable-capturing to happen.
By capturing variables, the results of substitutions are changed, potentially resulting in terms with different
heights. On the other hand, if we constrain the arbitrary Nat to at least be larger than maxVar t, then this should ensure that there's never any interference causing variable-captures that would cause the results of these substitutions to differ in height. It also works for arbitrary Nats for some of the sub-cases of Abs, just not the one subcase where we actually do the capture-avoidance.
-}
using-different-id-for-freshest-var-doesnt-change-height-1 : (t : LambdaTerm) -> (x : LambdaVar) -> (r : LambdaTerm) -> (n : Nat) -> ((maxVar t) ≤ n) -> height (subst1 t x r) == height (first (subst-helper1 t x r n))
using-different-id-for-freshest-var-doesnt-change-height-1 (Var v) x r n hyp = proof-Var
 where
  lem1 : subst1 (Var v) x r == first (subst-helper1 (Var v) x r n)
  lem1 = refl

  proof-Var = cong height (subst1 (Var v) x r) (first (subst-helper1 (Var v) x r n)) lem1
using-different-id-for-freshest-var-doesnt-change-height-1 (App t s) x r n = proof-App
 where
  proof-App = using-different-id-for-freshest-var-doesnt-change-height-1-ind-App x r (height t) (height s) (λ a → (λ p → (λ k → using-different-id-for-freshest-var-doesnt-change-height-1 a x r k))) (λ a → (λ p → (λ k → using-different-id-for-freshest-var-doesnt-change-height-1 a x r k))) t s refl refl n
using-different-id-for-freshest-var-doesnt-change-height-1 (Abs v e) x r n = proof-Abs
 where
  proof-Abs


-- variable-height induction:
renaming-vars-doesnt-change-height-1-ind-App : (x y : LambdaVar) -> (m n : Nat) -> ((s : LambdaTerm) -> (height s) == m -> height s == height (subst1 s x (Var y))) -> ((t : LambdaTerm) -> (height t) == n -> height t == height (subst1 t x (Var y))) -> (s t : LambdaTerm) -> height s == m -> height t == n -> height (App t s) == height (subst1 (App t s) x (Var y))
renaming-vars-doesnt-change-height-1-ind-App x y m n hyp1 hyp2 s t hyp3 hyp4 = proof
 where
  lem1 : height (App s t) == suc (max (height s) (height t))
  lem1 = refl

  vars = maxVar (App s t)

  sVars = maxVar s
  tVars = maxVar t

  s[x=y] = subst-helper1 s x (Var y) vars
  t[x=y] = subst-helper1 t x (Var y) (second s[x=y])
  


  lem2 : subst1 (App s t) x (Var y) == App (first s[x=y]) (first t[x=y])
  lem2 = refl

  s[x=y]' = subst-helper1 s x (Var y) sVars
  t[x=y]' = subst-helper1 t x (Var y) tVars

  {-
  so what's the relationship between s[x=y] and s[x=y]'
  vars >= sVars and vars >= tVars 
  and (vars == sVars) OR (vars == tVars)
  and (second s[x=y]) >= sVars and (second s[x=y]) >= tVars

  -}

  proof


{-
-- strong induction on height
-- how to do strong induction in Agda?? :O
renaming-vars-doesnt-change-height-1-ind-App : (x y : LambdaVar) → (n : Nat) → ((s : LambdaTerm) → (height s) ≤ n → height s == height (subst1 s x (Var y))) → (s t : LambdaTerm) → height s ≤ n → height t ≤ n → height (App s t) == height (subst1 (App s t) x (Var y))
renaming-vars-doesnt-change-height-1-ind-App x y n hyp s t [s≤n] [t≤n] = proof
 where
  m = maxVar (App s t)
  
  lem1 : subst1 (App s t) x (Var y) == first (subst-helper1 (App s t) x (Var y) m)
  lem1 = refl


  s[x=y] = subst-helper1 s x (Var y) m 
  t[x=y] = subst-helper1 t x (Var y) (second s[x=y])

  lem2 : subst-helper1 (App s t) x (Var y) m == (App (first s[x=y]) (first t[x=y]) , second t[x=y])
  lem2 = refl


  lem3 : subst1 (App s t) x (Var y) == App (first s[x=y]) (first t[x=y])
  lem3 = refl

  ns = maxVar s
  nt = maxVar t

  s[x=y]' = subst-helper1 s x (Var y) ns
  t[x=y]' = subst-helper1 t x (Var y) nt

  lem4 : subst1 s x (Var y) == first s[x=y]'
  lem4 = refl

  lem5 : subst1 t x (Var y) == first t[x=y]'
  lem5 = refl

  

  -- lem2 : subst-helper1 (App s t) x (Var y) (maxVar (App s t)) == (

  proof

-}


{-
-- standard subterm induction
renaming-vars-doesnt-change-height-1-ind-App : (x y : LambdaVar) -> (s t : LambdaTerm) -> height s == height (subst1 s x (Var y)) -> height t == height (subst1 t x (Var y)) -> height (App s t) == height (subst1 (App s t) x (Var y))
renaming-vars-doesnt-change-height-1-ind-App x y s t hyp1 hyp2 = proof
 where
  lem1 : height (App s t) == suc (max (height s) (height t))
  lem1 = refl

  n : Nat
  n = maxVar (App s t)

  lem2 : subst1 (App s t) x (Var y) == first (subst-helper1 (App s t) x (Var y) n)
  lem2 = refl

  s[x=y] = subst-helper1 s x (Var y) n 
  t[x=y] = subst-helper1 t x (Var y) (second s[x=y])

  lem3 : subst-helper1 (App s t) x (Var y) n == (App (first s[x=y]) (first t[x=y]) , second t[x=y])
  lem3 = refl

  lem4 : first (App (first s[x=y]) (first t[x=y]) , second t[x=y]) == App (first s[x=y]) (first t[x=y])
  lem4 = refl

  lem5 : subst1 (App s t) x (Var y) == App (first s[x=y]) (first t[x=y])
  lem5 = refl

  ns = maxVar s
  nt = maxVar t

  lem6 : subst1 s x (Var y) == first (subst-helper1 s x (Var y) ns)
  lem6 = refl

  lem7 : subst1 t x (Var y) == first (subst-helper1 t x (Var y) nt)
  lem7 = refl

  s[x=y]' = subst-helper1 s x (Var y) ns
  t[x=y]' = subst-helper1 t x (Var y) nt

  lem8 : height (subst1 s x (Var y)) == height (first s[x=y]')
  lem8 = cong height (subst1 s x (Var y)) (first s[x=y]') lem6
  
  lem9 : height (subst1 t x (Var y)) == height (first t[x=y]')
  lem9 = cong height (subst1 t x (Var y)) (first t[x=y]') lem7

  lem10 : height s == height (first s[x=y]')
  lem10 = ==-trans hyp1 lem8

  lem11 : height t == height (first t[x=y]')
  lem11 = ==-trans hyp2 lem9

  f1 : Nat -> Nat
  f1 q = suc (max q (height t))

  f2 : Nat -> Nat
  f2 q = suc (max (height (first s[x=y]')) q)

  lem12 : suc (max (height s) (height t)) == suc (max (height (first s[x=y]')) (height t))
  lem12 = cong f1 (height s) (height (first s[x=y]')) lem10

  lem13 : suc (max (height (first s[x=y]')) (height t)) == suc (max (height (first s[x=y]')) (height (first t[x=y]')))
  lem13 = cong f2 (height t) (height (first t[x=y]')) lem11

  lem14 : height (App s t) == suc (max (height (first s[x=y]')) (height (first t[x=y]')))
  lem14 = ==-trans lem1 (==-trans lem12 lem13)

  

  proof
-}



renaming-vars-doesnt-change-height-1 (Var v) x y = proof-Var
 where
  w = subst1 (Var v) x (Var y)

  h[Var-v]==0 : height (Var v) == z
  h[Var-v]==0 = refl

  lem1 : w == (if (LambdaVar-eq v x) then (Var y) else (Var v))
  lem1 = refl

  P : LambdaTerm -> Set
  P t' = height (Var v) == height t'

  P-v : P (Var v)
  P-v = refl

  P-y : P (Var y)
  P-y = refl

  proof-Var : P w
  proof-Var = P[x]+P[y]-implies-P[if-Q-then-x-else-y] P P-y P-v (LambdaVar-eq v x)

renaming-vars-doesnt-change-height-1 (App s t) x y = proof-App
 where
  proof-App
renaming-vars-doesnt-change-height-1 (Abs v e) x y = proof-Abs
 where
  proof-Abs




renaming-vars-doesnt-change-height-2 : (t : LambdaTerm) -> (x y : LambdaVar) -> height t == height (subst2 t x (Var y))
renaming-vars-doesnt-change-height-2 (Var v) x y = proof-Var
 where
  proof-Var
renaming-vars-doesnt-change-height-2 (App s t) x y = proof-App
 where
  proof-App
renaming-vars-doesnt-change-height-2 (Abs v e) x y = proof-Abs
 where
  proof-Abs

substEquiv-height-ind : (n : Nat) -> ((s t : LambdaTerm) -> height s == n -> height t == n -> alphaEq subst1 s t == alphaEq subst2 s t) -> ((s t : LambdaTerm) -> height s == (suc n) -> height t == (suc n) -> alphaEq subst1 s t == alphaEq subst2 s t)
substEquiv-height-ind n hyp (Var (V x)) (Var (V y)) [ds==n+1] [dt==n+1] = skip-it
 where
  -- use 0 ≠ suc n to derive a contradiction from the assumptions
  contradiction : False
  contradiction = zero≠sucn n [dt==n+1]

  -- use the contradiction in the assumptions to generate a term of the required type
  -- essentially a formalization of "we get to skip this case because it doesn't apply"
  skip-it = omega contradiction
substEquiv-height-ind n hyp (Abs x e) (Abs x' e') [ds==n+1] [dt==n+1] = proof-Abs
 where
  h[Abs-x-e]==suc[h[e]] : height (Abs x e) == suc (height e)
  h[Abs-x-e]==suc[h[e]] = refl

  suc[h[e]]==suc-n : suc (height e) == suc n
  suc[h[e]]==suc-n = ==-sym (==-trans (==-sym [ds==n+1]) h[Abs-x-e]==suc[h[e]])

  h[e]==n : height e == n
  h[e]==n = suc-inj (height e) n suc[h[e]]==suc-n

  lem1 : alphaEq subst1 (Abs x e) (Abs x' e') == alphaEq subst1 e (subst1 e' x' (Var x))
  lem1 = refl

  -- need to prove that subst'ing a var for a var yields a term of the same height.

  proof-Abs  
substEquiv-height-ind n hyp (App s t) (App s' t') [dt==n+1] [ds==n+1] = proof-App
 where
  proof-App
  -- bleh 
substEquiv-height-ind n hyp _ _ _ _ = refl


substEquiv-1,2 : (a b : LambdaTerm) -> alphaEq subst1 a b == alphaEq subst2 a b
substEquiv-1,2 (Var (V x)) (Var (V y)) = refl
substEquiv-1,2 (App t s) (App t' s') = proof-App
 where
  
  proof-App
substEquiv-1,2 (Abs x e) (Abs x' e') = proof-Abs
 where
  proof-Abs
substEquiv-1,2 _ _ = refl



```








#do we need to worry about that subtree having the "same" var, again?
#well, that's the q now :)
#if we do, then this is safe and reasonably efficient
#if we don't, then we can make it a bit more efficient by dropping this extra stuff
#i haven't been able to find a counterexample but i also don't have a proof that
#none exists.
#alright, so we just make two versions and let math sort it out. we have to tell Agda what
#we mean by "it's correct vs. non-correct" before it can help us decide, and then we still
#have to do most of the work in actually demonstrating which one is the correct one, Agda
#will just check our work when we finish.
idk, you always made it sound like its almost magic:)
the magic comes later after we've already built up lots of proof stuff &
descriptive framework

but, i think we just care that the "probably correct" version has the same results
as the "maybe correct" version, i imagine you could somehow magically prove that
one version is morphable to the other, eliminate the checks

hrm, there's a bit further we could go beyond that in terms of qualitative descriptions
of the tree structures generated, but, ultimately that's still more or less the same
idea, proving that one "version" is the same thing as another version in some kind of way.
so, we'd prove that 

forall x : LambdaTerm, v : LambdaVar, r : LambdaTerm, alphaEq(subst1 x v r, subst2 x v r)

The only problem with this is that alphaEq is defined in terms of subst, which wouldn't
be a problem except in the context of this situation where we have two different versions
of subst are trying to figure out which one to use in the first place
its alright as long as an alphaEqWithSubst1 agrees with alphaEqWithSubst2, how do we define
that agreement though. hrm







forall x y : LambdaTerm, alphaEqSubst1(x, y) <-> alphaEqSubst2(x, y)






alphaEqSubst1: LambdaTerm -> LambdaTerm -> Set
alphaEqSubst1 a b = exists s : List (Pair Nat Nat) , 

#so, later we'll write an alphEq algorithm that will actually check using one of
#these versions of substitution, but here we're just trying to compare teh
#versions of subst, so what this is doing is taking two lambda terms and returning
#a type/proposition that's going to express what it means for the two terms to
#be alphaEq, independently of these particular algorithms. (at least, that's the thought, anyway)
seems
 like trying to define the correct version

#hrm, these subst algos won't change bound vars
#so, we're gonna state some (random) known invariants that any version should satisfy?
#that's generally the ideal but we might not achieve that in every case, and here it looks
#like i'm taking the wrong approach with that because if these are the invariants that
#any version should satisfy then how would i end up with two different versions to compare
#in the first place, ah nvm, it would just change the proposition from

forall x y : LambdaTerm, alphaEqReference(x,y) <-> alphaEqImpl(x,y) == true, or some such.

and then we'd have our Impl1, Impl2, ...

#but i'm having trouble formulating what those invariants would be

#so, here's the first issue in any of these approaches, if we look at subst like a relation
between pairs (Term,Var,Term) and Term, then the two different versions will relate different
terms together, according to the basic notion of equality available from Agda

so this wouldn't work, for example:
forall t: LambdaTerm, x : LambdaVar, r : LambdaTerm, subst1(t,x,r) == subst2(t,x,r)

because subst1 and subst2 might introduce different fresh vars, and so these aren't actually
equal terms according to Agda.

#hence why we have to look at alphaEq, because that captures the proper notion of equality
#(independent of differences in the particular var names that the resulting term has)
#but if we define any kind of alphaEq algorithm in term of these substs, they don't change
#the bound vars in a way that we can really control

my idea was, checking that two versions of alphaEq get the same true or false for any given set of inputs,
so, like:

forall x y, alphaEqSubst1(x,y) == alphaEqSubst2(x,y)

so let's write a generic alphaEq that takes an impl of subst and uses that, then if we have more
implementations later we'll have less work
its pretty obvious that we can write that parametric alphaEq,
sure:


except it doesn't make sense to recurse over terms to subst into them and miss all the bound vars and
then recurse into them again to get those bound vars.
miss all the bound vars?

alphaEqGeneric : (subst : LambdaTerm -> LambdaVar -> LambdaTerm -> LambdaTerm) -> LambdaTerm -> LambdaTerm -> Bool

i dont even get whats the matter with bound vars here, presumably some result of some feature of the
subst functions that you are specifically concerned with? well the substs themselves are presumably fine
but using them directly to build the alphaEq algo doesn't seem efficient, even though it would be simple-ish
and would work
you mean it would run weeks or something? 
ah you mean in actual runtime of the actual lc-interpreter?
right it doesn't make sense to me to do these substs that recurse the whole structure but don't do anything
with bound vars, and then have to recurse the whole structure again to check that the bound vars line up
alright, i dont actually know how alphaeq is supposed to work
well, it's not a specific algo but there is a logical characterization of what the result is supposed to be
alphaEq(x,y) == true if there is a non-capturing replacement of vars in x for vars in y that makes x and y
syntactically indentical (*replacement*, rather than subst, because this would have to replace bound vars as well
if the two terms are actually going to be made syntactically equal)
there are potentially other ways to implement that though then doing like a two-phase:
1) replace vars in x to yield x'
2) check x' and y for syntactic equality
yea i can imagine one or two ways
You could do these checks as you recurse, and rather than making replacements directly in x, we could keep
a list of what vars are supposed to get replaced by what vars (like unification/union-find)

there is an impl in simpler-easier we can always check
all in all though, it seems the more the merrier, we can go proving that all our ideas of how these
two (alphaeq and subst) can work are equal or not, ah sure, definitely, this is something i ramble about
periodically, Agda kinda changes the game from trying to miminimiize your code to having more like a
database of all yoru code and everything you know about it

so, let's just start with the alphaEq algos. we can make the generic version that takes the versions of
substs, i checked out the alphaEq algo in simpler easier and it just calls subst during alpha-Eq even
though this just adding full recursions of the tree that are probably unnecessary, the goal here is
to prove equality of the two subst algos not necessarily optimize the alphaEq algo yet (and, we're in
the wrong kinda setting for optimization of these algos anyway)
yea



alright, i hope youll show me that it really holds
thats where the magic would come in, once you have these things built up then you can generically compose
things in a correct-by-construction fashion, like
(Exists L : Lang, such that L is regular) -> (Exists M : FSA, such that M recognizes L), etc..
and this is a *concrete* datatype, this isn't even where abstraction & generalization come into play
you would generalize/abstract from a starting point like this, and then with these building blocks
you would just be able to toss things together without having to worry about any of the coding details,
since it's already been checked and Agda won't let you put together things that don't fit
yea i get it
brb
unfortunately the way i also describe the situation is that it's like the state of computers in general in 1950,
except nobody's excited about the prospect of the new computers. :)
think how impossible this conversation we're having right now would've looked in 1950, prior to decades of
society's cumulative efforts. Agda's like machine-code of math, and so we're almost nearly as far separated
from the actual applications we want to be building as we would be if we were trying to write directly in
machine code, but, we have much more capacity for abstraction & generic programming & making sure everything
fits together coherently so in theory we should be able to make much more rapid pace towards those applications
than if we had actually been starting from machine code.

there's only one major place still where the magic really starts to break down, and that's when you try 
to turn the math around on itself and have Agda try to describe and optimize its own implementation.
all that shit like Godel and undecidability and undefinability starts popping out
hrm

yea this is actually a pretty major issue that we have to think about for AutoNomic.
like, we can use Agda to model a computation environment, we're already in the middle of doing that
and then based on the rules of that modeled environment, we can talk about computational complexity
we can impose constraints on the model so that Agda would only accept programs for that model if they're
proven to satisfy the complexity constraints

but Agda can only do this for its *models*, it' can't do it for itself, exactly
Agda doesn't have any capacity to differentiate its functions based on their internal/intensional properties,
only based on whether they map the same input to different outputs.
most dependent type theory and type theory in general is this way.


so
if
i
have


simple : Nat -> Nat
simple x = x


vs.

complex : Nat -> Nat
complex x = find256BitsOfSHA256HashCollsion x

like, you'd have to hand-define the complexity of the collision function, sure, but once you have that,
you can just add a complexity parameter to all your functions, and agda will check if you'd end up calling
a function with a bigger complexity from a function supposed to have lower complexity

ah sure, you could always do something like that, but, well, just so long as you can trust your
hand-defined complexity values. this is potentially workable, but, basically just trying to hack our
way around Agda's inherent flaw. ideally we'll eventually* have a proof system where can actually v erifiably bound
the complexity rather than verifiably bound what we say the complexity is. block-chain might make this
even somewhat more realistic (the workaround that is) because you can at least trust that everybody's
agreed on the same values for a while and they're not just arbitrarily changing, especially if they provide
write-ups of their informal proofs along with, or Agda proofs in a modeled environment.

your only issue is that you dont happen to have a model/ast of a function available from within an agda code
that also uses/contains the function? yes but like, more extreme than that

assume we have two functions f : A -> B and g : A -> B
and assume that forall x, f x == g x
then for any proposition P : (A -> B) -> Set, we can't have (P f) & ~(P g)

i.e. no proposition about functions can answer differently about f and g if they agree on every input.
I think it might actually be even a slightly stronger version of this:

forall P : (A -> B), (P f) <-> (P g)

No intensional properties about functions can affect the result of any statement in Agda.
yea alright, you could only stick stuff into monads
i imagine some kind of tag system for lemon
type signature is just one kind of tag

one idea i've been sort of playing with is to separate functions from their implementations
so we'd have some class representing syntax trees of lambdas along with their one-step
evaluation semantics, and then actual "functions" would be like an equivalence class of
implementations based on whether they agree on outputs. so MLTT could then talk about the
implementations as though they were any other objects in any other inductive type, i.e.
reference their intensional properties, and "functions", by the given definition, would
still retain their property of extensional equality (which does become important in later
stuff in the math)

another which is more along the lines your tag system, is, constructive logic only says that
proofs of implications have to be usable as functions, but, it's not quite so strict about
saying that they have to be *only* functions. In a lot of more advanced type theory work like
HoTT stuff, they restrict themselves to talking about *continuous* functions, for some pretty
abstract definition of "continuous", and making that kind of restriction opens up the door
for a lot of the homotopy/topology math they do there, but, that's going exactly the opposite
direction, and they're trying to make it even *harder* to differentiate functions based on
their intensional properties, and failing to provide an alternative mechanism for dealing with
complexity.

so if you take regular MLTT functions, and extend them with some sort of tag system, you'd
wind up with something like that, except going the opposite direction from the HoTT people
(ideally)

this would probably be the easiest effective solution prior to getting more info from research:
1. construct a data type that models the structure of Agda functions along with their one-step
   evaluation semantics
2. prove things about complexity of "programs" in this model, from outside the model
3. make a generic higher-level function that would translate these models into actual Agda
   functions that Agda can run, a semi-self-interpreter, it doesn't need to interpret
   all possible Agda functions, just enough to provide a useful environment for programming
 
This doesn't solve the underlying issue but basically would let you sandbox a subset of
Agda so that you could at least be sure that if you restrict yourself to that subset you'll
be constrained to the specified complexities, and would only have to deal with the
uncertainty when you step outside that model, which, at that point you might only be
doing in order to prove computational complexity results about it and just doing most of
the rest of your work entirely in the sandbox.

Example: if i write an Agda function, Agda can't tell me anything about it's complexity.
If we finish describing this lambda calc model and it's one-step evaluation semantics, then
we can do either a) define an arity-2 proposition (binary relation) that characterizes the
n-step evaluation semantics based on the one-step evaluation function/relation, or b) make
a coinductive type that serves as an infinite list/stream that plays out the evaluation, i.e.
myStream[0] = computation at state 0, myStream[i] = computation at state i, ....

Since it would be an infinite stream, we can model Turing-complete computation this way, even
though we don't actually have it available in our functions.

So if i want to say, for example, that some computation will be in state x within n steps, i
can make a proposition:

exists i : Nat , (i <= n) && myComputation[i] == x

Or I could make a check on states that sees whether they are halting states or not, and then
check whether the computation halts within n steps:

exists i : Nat, (i <= n) && isHaltingState(myComputation[i])

One question you might have is: even though we can't write an algorithm that solves the
halting problem, can we in theory *prove* every halting computation to be halting, with
manual proofs & creativity?
i just wanted to say that "with matual proofs and creativity" kinda precludes that we
even could try to prove something about every halting function, ah, the question here would
be more like, given some halting function, does Agda even contain a proof that it halts.
if we set a program to just loop through all possible Agda proofs, maybe it would eventually
find the proof, but as long as it keeps running we don't know whether it will actually stop.
On the other hand, we could apply our creativity and manually search through. If we did that,
would we necessarily find a proof that our program halts? No.
ah alright, thats the intuitive "the prover pretty much has to run it" idea. more or less yea,
in some informal terms Agda could be said to contain some amount of complexity, and can't prove
anything about complexity beyond that, kind of like a machine with n bits of memory is somewhat
limited in what it could prove about a machine with (n+1) bits of memory, and just like
we can keep adding another bit of memory, we can keep adding more complexity to our proof
system, but, unless we can add a full infinite amount of complexity, some things will be
beyond its "reach". Chaitin talks a lot about this and all his work is very very readable
i definitely recommend checking some of that out
alright remind me sometime in future
will do



Answer: no. Any consistent proof framework will be limited and there will be programs
that halt but such that you can't prove it just using the axioms in that framework. You
would need infinitely many *independent* axioms in order to consistently assign a halting/looping
value to every program in a Turing-complete programming lang.
whatever, doesnt matter lol, might matter, if you were to start on a wild-goose chase for
trying to see whether you could do this in theory, i've been down that road XD
me i pretty much only turn to math when i need to prove that something cant be done
as in yeeea im pretty sure theres some law about that

So: one take-away from this is that pretty much any solution to the complexity thing that
we could come with which is entirely relative to a single consistent proof framework, must in
some sense be a kind of hack/workaround. Or so it appears at this stage anyway. perhaps there
are general methods that can reapply to any proof framework in an appropriate way.

But, this is all pretty heavy shit when we get down into the details of it, you're jumping
from just starting with proofs to going all the way to the deep-end with this analysis
of proof complexity XD i was mostly just a) giving you a heads up that we'll eventually have
to figure out *some* strategy for dealing with this, and b) i have to add this as the one
caveat when describing all the "magic" (really there aren't any other *major* caveats)

well i still have no idea where it exactly caveats the magic, but ill find that in time




so, at this point you've seen nearly everything that i've been rambling about with Agda,
modulo details, and not including homomorphism/isomorphism/functor stuff (which doesn't
come back up until we're trying to generically program in Agda, right now we're still
working our way up to mastering the *concrete* data)
What the idea with the h omomorphism/isomorphism/functor stuff is, it gives you a way
to describe what it means for two different concrete structures to actually just be
different instances of the same abstract structure, and further what a proper translation
between the two instances could then consist of.
So after making some proofs & functions about Nat, you might move over to Ints, and then you
say "ah crap i have to write all my proofs & functions again". using isomorphism, you can
save yourself the trouble and just do this once, so, instead of writing your proofs like:

(forall x : Nat) -> {some properties about x}

You make them generic over the entire isomorphism class:

(forall A : Type) -> (A isomorphic_to Nat) -> (forall a : A) -> {those same properties about a}

Example of two concrete structures that are isomorphic:
a) a wall-clock with an hour-hand and a "tick operation"
b) the set {0,...,11} with a "successor mod 12 operation"

yea well we call these interfaces
sure, so, the only difference between interfaces here and interfaces in other langs is that
here you can precisely characterize the logical structure/behavior the interface must
provide, whereas in other langs you make an abstract type and its like "give me a Nat -> Nat, any
Nat -> Nat, i'll run it, even if it infloops or does w/e other wrong things"
i was just commenting on ^, ah
well, that was maybe a bad example
lemme try and think of some other wrong behaviors
well, np
let's imagine you have a program that's supposed to take a description of a language, and an
implementation of a parser for that language, and then do something with them (likely involving parsing)
theoretically the parser provided should actually parse the lang
and if that's not what it does, then almost assuredly you will end up with some brokenness in
your larger program.
but a programming lang without this kind of ability to constrain things based on their
logical properties won't be able to catch that, it'll just say "sure give me a function String -> Tree, i'll
try to run it" they don't have the ability to say "give me a function String -> Tree such that this is actually
a valid parser for the language you provided"
this also isn't a great example, but, mainly because it's sort of contrived.
these issues pop up all over the place in traditional programming langs, you have to
manually make sure that you're arranging everything in a coherent fashion, you have to
make sure that you're not passing null-terminated strings to a function that finds the
end of a string by checking for a null-terminator, and you can't reliably make a
NullTerminatedStrings type. you could make a class whose constructor takes a string as input 
and then null-terminates it if necessary and then try to make sure that functions that require
null-terminated strings only ever get them from this class, and make sure we don't ever go in
and overwrite the member value of the class holding this null-terminated string, without
going through the private functions of the class that will ensure our update is still 
null-terminated, and if god forbid we mess up something in the NullTerminatedString class, C++
won't check it, and i'm just talking about the existence of a null-terminator on the end of
a string here, what if we actually have a non-trivial logical property to enforce? :)

its not so black and white
well it's not a "this is black vs. that i s white" thing it's just that MLTT's abstract types
come built-in with a convenient way to enforce their own coherence when composed into larger
applications, and this *capacity* is generally lacking in anything without dependent types or
something equivalent that allows it to use logical universal/existential quantification in
its types/constraints, which forces the programmer to have to verify all the coherence manually
in most cases

this becomes a way more major issue if we consider crowd-sourcing code (into an application, rather
than just a database of text snippets that supposedly represent code and informal proofs about them). 
i can't see how it could even be made possible without this extreme capacity for constraining
logical properties in the abstract data types. this is currently my only viable strategy for how
to do atlas project without sacrificing on 99% of what i wanted to actually do with it

but, that could also just be my lack of imagination. now that you've got a more concrete idea
of what the strategy is there, you might be able to find some more-reasonable less-overkill
approaches that i'm just not thinking of yet

the other application/utility that i could see this being a major factor in is "semantic routing".
i explained that somewhat recently and you seemed to get the idea of it but i'll recap for
good measure: 
node A has a database in format A'
node B has a database in format B'
node B wants node A's data to go into their database.

node C knows a (proven correct) translation function from A' -> C'
node D knows a (also proven correct) translation function from C' -> B'

the composition of a proven correct translation function from A' -> C' with
a proven correct translation function from C' -> B' yields a correct-by-construction
translation function from A' -> B'.

Proven correct relative to what? Idk, probably some human-level logical model of
the real-world situation that both formats are hypothetically supposed to be
representations of.

So, the idea that everybody on the internet might have access to different
databases, in different formats, and have different translation functions available
to them, at different times, but, functions A -> B, B -> C, C -> D..
they can be seen as links in a virtual semantic overlay network, and paths could
be routed through this semantic network to get automated translations from
database A to database B, even if in diverse formats.

yea id been coding something like this about 12 years ago so i guess i get the idea
probably 15
or more
sigh

so, if you get the basic idea of what function the isomorphism/interface stuff serves,
that's pretty much the "magic" that all the rest leads up to, and i'll have to find
something new to ramble about that you have no idea what i'm talking about :D
lol

so i figure these 2 things (crowd-sourcing code + semantic routing) + decentralization = atlas project
or, would provide the basic framework to then fill the encycopledia
i guess i'd have to say a couple more things there to differentiate it from autonomic, but
that's the idea i'm working with anyway

in theory, this basic stuff that MLTT provides would allow users to crowd-source their UI
into the encyclopedia, without too much fear of making it all fall apart on itself due to
incoherence or insecurity or w/e. the one critical thing to address would be that same
complexity thing from before, but, atlas project would have way more options for how to
address that than autonomic does. for example: general users might not be given a "full"
MLTT to use directly, they might do everything in a modeled environment where complexity
can be constrained, and then more advanced/involved users could work in the full MLTT in
order to develop the sandbox further for the rest of the users. i mean, wikipedia can handle it
without *any* verification whatsoever, so... 

well, this has been a pretty good intro to the concepts if you've followed
everything more or less so far, i wasn't expecting we'd be able to successfully
cover these topics until getting down to the details with Agda, but i guess
maybe it all fits into context a bit better now that you've gone over proof-structuring
and all that

dunno, some things have felt rather patchy
ah, well, if you feel something's rather patchy at this point, there's a decent chance it
actually is
hehe alright
also, i havent really yet seen anything in agda that i wouldnt more or less imagine i'd see
guess im not easily amused, but ill be when we write all the versions of subst and alphaeq *and*
succesfully debug it all, well, i guess you'll be in for a treat then :)
its late-ish over there, are you still up to go into the proof details with that or should we
save for tomorrow (or, whenever, i think you said tuesday?)
well, mmm, dunno, i am a bit tired
lets leave it for tomorrow i guess, any easier stuff we have on our todo list? for discussing, or something,
not agda
do we have agda-mode on here?  i cant figure out how to load it in my emacs
i haven't set up agda on here yet
wrt our todo list, we still haven't even really started our actual todo list because everything
on it is too hard :D
its the warmup, no? well, that was supposed to go until about today but i'm still several steps
away from where i wanna be with proofs about lambda calc & type theory before i start killing
myself with the lambda-auth paper
ive been distracted with all sorts of stuff, yeah
so let's call it another week for warmup and reassess next friday or so
i personally wasn't expecting this warmup phase to be nearly so fruitful as it has been,
wasn't originally planning to go incrementally through a series of proofs that start with
untyped lambda calc and stuff and lead up to proofs about lambda-auth, was just planning
on refreshing my memory about a couple things and then trying to dive into lambda-auth, but
after getting the hang of the stuff i've been working with over the last week or so, i
could hardly imagine trying to dive into the lambda-auth paper without these tools at my
disposal, so, i don't figure that a bit more time developing those tools a bit further is gonna
hurt anything
..and i just gotta start with the basics
right. so i figure, as long as we're making progress in developing our tools for proving
things in comp sci in general (while keeping in mind how it applies to the eventual goal of
proving correctness/security of lambda-auth/MLTT-auth/etc), then i'd say that's forward progress for the
project as a whole.
so, along those lines, there's plenty of easier things we could work on (in Agda or otherwise).
especially in Agda though, we could start with just basic proofs about simple structures like Nat
and simple algorithms like _+_, and it might be easier to get a hang of proofs without having to
worry about details of lambda calc evaluation
outside of Agda, the only things on our to-do list on the math side of things would be way
harder proofs, but, there's lots of things we could code in something like C++
SK combinator evaluator, lambda calc evaluator, lambas <-> SK's translator, that kinda thing
(there's plenty more besides that, i've just been on a lambdas & SK's kick lately and that's
all that's popping to mind at the moment)
but i figure those implementations would not be particularly educational for you since you
already know how to code & are just trying to learn how to Agda now
me on the other hand, i do need lots of coding practice & things to force me to practice,
outside of Agda

yea, if we were already onto the point of actually coding up AutoNomic or parts of it then
there would be plenty of other things to do besides for this study, but, at the moment this
is pretty much the most relevant work we could be doing

if you want to do some c++ or something, anytime, i guess it will be easier for me to find 
the situation to be able to focus on that
hopefully

cool, i've started a bit on an SK combinator evaluator but only made it through the
well-formedness checker and then got sidetracked trying to give proofs of correctness
and never finished because i have to build up some conceptual framework to do
proofs in an imperative context. 

well, if you want to do proofs about it, then youd better just stay in agda?
long-story short: yes, but my more critical issue is getting trapped into one
way of doing things, like "the Agda way of doing things", and then i go look at
some C++ code and think "ahhh run away". this is less to do with "i should be
using C++" and more to do with "i should be able to approach comp sci problems
that are presented to me, regardless of where they're coming up or what the
problem is". like, this is pretty much math practice for me, but the math i'm
struggling the most with right now is "code that is not Agda". i wanna snap
myself out of that and be able to just go code things like i used to would've done
before i got sucked into all this math & verification stuff, and I kinda have
to step outside of Agda for that so that none of that is even there for me to 
think about working with in the first place
hmmm

here's a more concrete example of how this is really really bad for me as a coder:
Agda is a pure functional language, it doesn't have state, it doesn't have
variable assignment, it doesn't have non-termination, and it doesn't "really" have
sequencing of operations (it can only simulate it, with monads or some such)

as a coder/computer-scientist, i should not be afraid of these things, but, 
when i get into C++ and have to start allocating memory on the heap, and am too used
to the crutches agda provides with its verification, well...

i stop coding after i finish my well-formedness checker because the next meaningful
things for me to write would require all kinds of memory allocation stuff that,
while it's not complex in theory, i never spend the time to really get the hang of it
in C++ (or anything else), etc....

so, i wasn't even gonna *touch* agda until you got interested in it, i was gonna
do everything the traditional ways and anywhere i did proofs it was gonna be
alll on paper

like, here's my experience of my ~2 years immersed into agda:
i pretty much just formalized my analysis paralysis

so, somebody who's less distracted by every mathematical notion and less prone
to analysis paralysis might have better luck with it than me (and might be able
to keep me from bouncing all over the place haha)

ultimately we want me to stop with the mathematical masturbations and just code
the damn thing already, so, i'm going C++ hehe

lol

im dreaming away about lemon here
are you finding that any of this stuff would have utility for that?

i worry agda would be too strict to try coding up the whole thing in it,
but i wonder if ive finally gotten to where there are some individual peices,
separable, definabe declaratively, possible to keep them small and understandable
like, we could code up the algo for transforming cfgs with operator precedence/associativity
in agda or python with rdf, doesnt matter, shouldnt matter
then i wire it up into my magic reparsing algo
then wire that up into the libmarpa essentially-microservice
then i'd redo the language builtins nice and declarative

yea i'd imagine agda's strictness would be overkill to try to write the whole thing
in, but yea could be useful for individual (functional) pieces. i rarely think of
using Agda/MLTT to actually write an application in, all my ideas that use MLTT instead
have MLTT built-in to the app for the users

i feel kinda uncertain about the plan to dissect lambda auth and maybe go thru all 
the proof traces theory and whatnot, it sounds good, that when we finally grok everything,
autonomic will be obvious, but the part of me that screams that we should deliver something
meaningful within a year (yea i set that totally arbitrarily based on my money management),
that part says that we should maybe look at the mltt implementation we did back then,
or a comparable one, and try to identify the missing pieces from there

like i always thought id approach it, at least mentally, not necessarily in code, but
take the central part that we know, which is a mltt interpreter, add functionality, which is 
the dht api, marvel at how its insecure etc, then proceed to add restrictions

its like, take all the pieces, throw them onto a pile, because this gives you an idea about 
all of them

sure, only two things:
a) for dissecting lambda auth we actually only need to look at STLC
b) for mltt-in-dht, mltt should already be "the restrictions"

but other than that, yes 100%`
now, my only "problem" with that is that i'm not... "very good at it"
i'm more mathematician than coder so it's way easier for me to just do the next
incremental proof than it is to get all the pieces into the pile, so i nearly
always just default to the proofs

you're definitely right though, especially since we don't have indefinite time
to devote to it (though i do think we're making fine pace with the proof-based approach,
especially considering where we're starting there, and also the proof-based approach
is also gonna lead through a series of steps that incrementally add in the functionality)

i figure we gotta somehow time-manage between both approaches, cause we don't want
to get to the end of the code and have no verification of it and be starting from
square 1, and we don't want to get to the end of the math and have no code to show
for it and again be starting from square 1

so i've been hoping to try to adhere to the ideal of verifying the individual pieces
as we add them in so that they're both done at the same time and we don't have to
backtrack on either side of it when we get to the end

i'm thinking the approach will look a bit more reasonable once we get past the basics
of just proving stuff and into the actual pieces that will go into the construction

i gotta for a bit though so let's pick back up on the lambda calc & basic proof practice tomorrow
(or so). i'm thinking you might a bit more confidence in the approach once you 
go through some of the results fully and see how we can apply them. a week or so
ago i was thinking pretty much the same thing you are here but like i said, after
what i've been researching lately i would totally apply all of this to the dissection
of lambda-auth and i'm not sure how i would've approached it without these results
yo
alright




well, that's not a bad way to look at it, but, i can do proofs on paper faster than i
can in agda, especially without having the programming environment modeled already, or
just coding them functional-style using agda functions

i originally was trying to get away from Agda because it's like a black-hole for me,
until you got interested in diving into it

if all the comp sci theory is correct, we shouldn't be able to verify our MLTT from
within MLTT, so, ultimately some amount of the verification will have to be done
manually (and even if we could verify it from within MLTT, we'd still have to verify
MLTT from outside MLTT in order to verify that that internal verification was even
meaningful in the first place)

the other issue is, unless we model the lower-level programming structures, like,
for example, model C++ in Agda, or model x86 in Agda, then there's a good chance
we're only proving things about things that are pretty far separated from what the
computer is actually going to be doing (and if we don't do that modeling, then
Agda couldn't tell us anything about the complexity of our code)

so, as much as i like to think that the answer to all questions in life is "better
just stay in agda", building an MLTT implementation is one of the couple things
where this might not be the case, and, i haven't had much success with that route
personally...

*but* i also can't say i gave it a full try because i kept getting side-tracked
by intermediate things along the way to the goal, and had slightly different
goals in mind







well, now youre making it sound like, that interfaces are the right thing to use to define all these
complexity things with. hrm. maybe. *if* you had the ability in the lang to talk about the
complexity of functions, then you could constrain the allowed complexity in your abstract type, and
any concrete impl. would have to come along with a demonstration that it is actually constrained
to that complexity, but, not sure if that's what you meant




Agda has no idea of the differences in complexity between these two functions, all it can see is "Nat -> Nat"
and there's no way to have the type system talk about these differences.

It is *the* critical flaw, currently.

But, as long as you're restricting yourself to talking about things inside a *modeled* environment, all
of Agda's magic will totally apply to anything you want to talk about in there.

The weird question is: since Agda can model a turing-complete programming environment, Agda can model Agda
this isn't particularly surprising, since the whole basis of Godel's proof is to use a proof framework to
encode a representation of itself.

What we'll find is that there will be plenty of things about this implementation that Agda can't provide an
answer to: is it consistent? if Agda says one way or the other, then Agda would be inconsistent. does the
implementation actually capture Agda's intended semantics? Agda can't define its own semantics (Tarki's
undefinability theorem). 

That being said, just because it can't answer those kinds of questions, doesn't mean it wouldn't be able to
answer *any* questions about itself. It could hypothetically prove things about complexity of some of its
mechanics, and prove that there are more optimal implementations.

So then you get to the question of: ok well how would we get from there to actually switching out Agda's
internals with these more optimal implementations, and what kinds of limitations will Agda run into
in proving things about computational complexity of its own implementation?

And then: if this isn't the appropriate way to bound complexity, then what is?


no need to worry about that much yet, just wanted to give you heads up on that aspect since it's
really *the* major thing to address besides for MLTT-auth, but we'll get back to that

well, i dont follow all the associations
but, you can make anything a part of a functions' type, by, like, passing it around like a monad, no?
hrm, can you elaborate on that? not sure if i know exactly what you're referring to there












like subst [x:=v] into (\x.x), doesn't result in (\v.v)
so we can't compare (\x.x) to (\v.v) by trying (\x.x)[x:=v] == (\v.v)
on the other hand, we could compare (\x.x) to (\v.v) by trying:
(\v.x[x:=v]) = (\v.v)

i.e. since we know that our subst algos won't handle the bound vars for us, handle
that specially in the alphaEq algo. 

i dont follow, but what i gathered is that we should be comparing the results of alphaEqs after multiple substs'
sort of, to compare x and y for alphaEq, there should be a list of var replacements you can make in x in order to
make x and y syntactically identical, so that's what the multiple substs' thing is (supposed to be, but, doesn't
quite work by itself because of the above example).


This is the "coherentism" interpretation of logic. Nothing is "absolutely correct" we just
check what's the same things as each other, and hope we're talking about the correct things :)
works for me:)we'll tell the public we ascribe to "verificationism" though, they'll find that
less discomforting.

so have you started pulling any of this into Agda yet?
no, i only succesfully compiled stuff up until this subst thing, ah sure, i just meant
any of my pastebin. cool, were you able to get agda-mode working on terminal?
on terminal? the agda mode in atom seems to be broken, and i didnt have agda-mode for emacs, 
but im still making attempts to cabal install agda
so i was just tweaking the source in atom, at least i got sytax highlighting, 
and i was running it on the command line
*running agda on it




     -- (\x.vx)[v := r], where x in FV(r)
     -- This is the wrong way to do it:
     -- (\x.rx)
     -- This is the right way to do it:
     -- (\y.My), where y is a fresh var.
     -- And that's how we evade capture



{-
Example:
(\y.xy)[x:=y]

If this equals (\y.yy), then we've changed the meaning
But, (\z.yz), that's correct substitution.
what happens if there are free variables in the replacer?
So lets say we have
(\y.xy)[x:=(\y.y)]
(\y.(\y.y)y) is fine because of variable shadowing
so, here we see that y occurs bound in x, i.e. it's under the \y.
so those are always gonna get shadowed in this case
so we're only worried about capturing free occurrences in the replacer
-}

