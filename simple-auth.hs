-- Syntax of the language:
type Sym = String

data Expr
 = Var Sym
 | App Expr Expr
 | Lam Sym Type Expr
 | Pi Sym Type Type
 | Kind Kinds
 | Auth Type
 | Unauth Type
 deriving (Eq, Read, Show)
type Type = Expr
data Kinds = Star | Box deriving (Eq, Read, Show)

-- An "Env" is a list of type-assumptions, which are pairs
-- where the first element is a variable, and the second element is
-- the type assumed for that variable in the current context
newtype Env = Env [(Sym, Type)] deriving (Show)


allowedKinds :: [(Type, Type)]
allowedKinds = [
 (Kind Star, Kind Star),
 (Kind Star, Kind Box),
 (Kind Box, Kind Star),
 (Kind Box, Kind Box)
]




-- auth modes:
data Modes = Ideal | Verifier | Prover

-- The initial context is an empty list of type-assumptions
initialEnv :: Env
initialEnv = Env []

-- This adds a new type-assumption into the context
extend :: Sym -> Type -> Env -> Env
extend s t (Env r) = Env ((s, t) : r)

nub :: (Eq a) => [a] -> [a]
nub = nubBy (==)

nubBy :: (a -> a -> Bool) -> [a] -> [a]
nubBy eq l = nubBy' l []
 where
  nubBy' [] _ = []
  nubBy' (y:ys) xs
   | elem_by eq y xs = nubBy' ys xs
   | otherwise = y : nubBy' ys (y:xs)

elem_by :: (a -> a -> Bool) -> a -> [a] -> Bool
elem_by _ _ [] = False
elem_by eq y (x:xs) = x `eq` y || elem_by eq y xs

delete :: (Eq a) => a -> [a] -> [a]
delete = deleteBy (==)

deleteBy :: (a -> a -> Bool) -> a -> [a] -> [a]
deleteBy _ _ [] = []
deleteBy eq x (y:ys) = if x `eq` y then ys else (y : deleteBy eq x ys)

(\\) :: (Eq a) => [a] -> [a] -> [a]
(\\) = foldl (flip delete)

union :: (Eq a) => [a] -> [a] -> [a]
union = unionBy (==)

unionBy :: (a -> a -> Bool) -> [a] -> [a] -> [a]
unionBy eq xs ys = xs ++ foldl (flip (deleteBy eq)) (nubBy eq ys) xs

liftM :: (Monad m) => (a1 -> r) -> m a1 -> m r
liftM f m1 = do {x1 <- m1; return (f x1)}



type ErrorMsg = String

--type-checking can fail, so we need exceptions, so we'll use
--an Either, so our type-checking return either the type or an
--error message if it can't compute a type:
type TC a = Either ErrorMsg a


-- use this to return an error-message of type TC Type
throwError :: ErrorMsg -> TC Type
throwError msg = Left msg




-- Check the Env to see if a type-assumption for the var "s" is
-- present; if so, return the type, and if not then throw an error
findVar :: Env -> Sym -> TC Type
findVar (Env r) s =
 case lookup s r of
 Just t -> return t
 Nothing -> throwError $ "Cannot find variable " ++ s



-- Find the unbound variables in an expression
freeVars :: Expr -> [Sym]
-- (Var s) is unbound in (Var s)
freeVars (Var s) = [s]

-- the free vars in an application are the free vars in the function
-- union with the free vars in the argument
freeVars (App f a) = freeVars f `union` freeVars a

-- the free vars in a lambda are the free vars in the domain union with
-- (free vars in the body with the variable of quantification removed
-- from the list)
freeVars (Lam i t e) = freeVars t `union` (freeVars e \\ [i])

-- the free vars in a pi-type are the free vars in the domain union with
-- (free vars in the codomain with the variable of quantification removed
-- from the list)
freeVars (Pi i k t) = freeVars k `union` (freeVars t \\ [i])

--Kind expressions don't contain Vars, return an empty list.
freeVars (Kind _) = []



-- helper function for subst; 
substVar :: Sym -> Sym -> Expr -> Expr
substVar s s' e = subst s (Var s') e


--       what   with     in      
subst :: Sym -> Expr -> Expr -> Expr
subst v x = sub
 where 	
-- if "in" == (Var "what"), then return "for", else return "in"
  sub e@(Var i) = if i == v then x else e

-- applications: substitute "what" by "with" in both f and a
  sub (App f a) = App (sub f) (sub a)

-- handle Lam's and Pi's the same way
  sub (Lam i t e) = abstr Lam i t e
  sub (Pi i t e) = abstr Pi i t e

-- don't substitute into Kinds; no vars, nothing to substitute
  sub (Kind k) = Kind k

-- list of free variables in the value being substituted
  fvx = freeVars x

-- generate a fresh variable for i which isn't a free variable
-- in e
  cloneSym e i = loop i
   where 
    -- keep adding "'"s to the var name until you have a var name
    -- which isn't the name of any var in the free vars of e
    loop i' = if i' `elem` vars then loop (i' ++ "'") else i'
    --get the free vars for e
    vars = fvx ++ freeVars e


  abstr con i t e =

-- if the variable being substituted is the variable of quantification, 
-- then only make the substitution in the type, not in the body
   if v == i then
    con i (sub t) e

-- if the variable of quantification is in the free variables of the
-- value being substituted, then replace the variable of quantification
-- with a fresh variable before making the substitution, in order to
-- prevent variable-capture.
   else if i `elem` fvx then
    let 
     -- generate the fresh variable
     i' = cloneSym e i
     -- substitute the fresh variable for the original into the body
     -- of the abstraction
     e' = substVar i i' e
    -- now that we've replaced the variable of quantification with
    -- a fresh variable, we're free to make the original substitution
    -- into both the type and the body.
    in con i' (sub t) (sub e')

-- if the variable of quantification isn't the variable being substituted,
-- and it's also not in the free-vars of the value being substituted, then
-- we can freely substitute into both the type and the body of the
-- abstraction without worrying about variable-capture.
   else
    con i (sub t) (sub e)







-- Compute the "weak head normal form" of the expression
whnf :: Expr -> Expr
whnf ee = spine ee []
 where
  -- the WHNF of a Var is itself 
  spine (Var x) as = app (Var x) as

  -- the WHNF of an Application of f to an arg takes the arg
  -- and prepends it to the list or args and returns the WHNF of f with
  -- this list of args
  spine (App f a) as = spine f (a:as)

  -- the WHNF of a lambda with no args is itself
  spine (Lam s t e) [] = Lam s t e

  -- the WHNF of a lambda with args is the body of the lambda but
  -- with the first arg substituted for the variable of quantification
  spine (Lam s t e) (a:as) = spine (subst s a e) as

  -- the WHNF of a Pi is itself
  spine (Pi s k t) as = app (Pi s k t) as

  -- the WHNF of a Kind is itself
  spind (Kind k) as = app (Kind k) as

  -- why is this a conflicting definition?
  -- we do this when we get to a stuck term, i.e. something in function position
  -- and something in argument position, but no reduction. in this case we
  -- package everything back up into an Application.
  app f as = foldl App f as






-- Compute the "normal form" of the expression
nf :: Expr -> Expr
nf ee = spine ee []
 where 
  -- the NF of a Var is itself
  spine (Var x) as = app (Var x) as

  -- if the expression is an application, prepend the arg to the list
  -- of args and then normalize the function with this list
  spine (App f a) as = spine f (a : as)

  -- a lambda with no args normalizes to a lambda with the same variable of 
  -- quantification but a normalized type and normalized body:
  spine (Lam s t e) [] = Lam s (nf t) (nf e)

  -- a lambda with an arg normalizes to its body but with the arg subsituted
  -- for the variable of quantification; i.e. it's the lambda applied to the arg
  spine (Lam s _ e) (a:as) = spine (subst s a e) as

  -- the NF of a Pi type is a Pi-type with the same variable of quantification
  -- but with normalized domain and codomain:
  -- why would a Pi-type have arguments? why would a Pi-type be *applied* to anything?
  -- so why are we calling "app"? seems like it's "just in case" we have arguments
  spine (Pi s k t) as = app (Pi s (nf k) (nf t)) as

  -- a Kind normalizes to itself
  spine (Kind k) as = app (Kind k) as

  -- this takes an expression with arguments, puts the arguments into normal form, and
  -- then repackages the whole thing into a nested application on these arguments:
  app f as = foldl App f (map nf as)
 





--Alpha equivalence:
alphaEq :: Expr -> Expr -> Bool
-- two Vars are alphaEq if their symbols are equal
alphaEq (Var v) 	(Var v') 	= v == v'

--two applications are alphaEq if the functions are alphaEq and the arguments are alphaEq
alphaEq (App f a)	(App f' a') 	= alphaEq f f' && alphaEq a a'

-- two Lams are alphaEq if their types are equal after substituting the variable of quantification
-- from the first lambda for the variable of quantification in the second lambda, and likewise with
-- their bodies
alphaEq (Lam s t e)	(Lam s' t' e')	= alphaEq t (substVar s' s t') && alphaEq e (substVar s' s e')

-- two Pis are alphaEq under the same conditions as when two Lams are alphaEq
alphaEq (Pi s t e)	(Pi s' t' e')   = alphaEq t (substVar s' s t') && alphaEq e (substVar s' s e')

-- two Kinds are alphaEq if they're exactly the same Kind:
alphaEq (Kind Star) 	(Kind Star) 	= True
alphaEq (Kind Box)	(Kind Box)	= True

-- no other expressions are alphaEq
alphaEq _		_		= False






-- two expressions are beta-equivalent if their normal-forms are alpha-equivalent
betaEq :: Expr -> Expr -> Bool
betaEq e1 e2 = alphaEq (nf e1) (nf e2)





-- "type-check-reduce"
tCheckRed :: Env -> Expr -> TC Type
tCheckRed r e = liftM whnf (tCheck r e)

tCheck :: Env -> Expr -> TC Type
-- to type-check a Var, find the symbol for that Var in the env, and return the corresponding Type, if found
tCheck r (Var s) = findVar r s

-- to type-check an Application:
tCheck r (App f a) = do
 -- first type-check-reduce the function
 tf <- tCheckRed r f
 case tf of
  -- make sure the type of the function is a Pi-type
  Pi x at rt -> do
   -- alright so it is actually a function, now type-check the argument
   ta <- tCheck r a
   -- make sure that the type of the argument is beta-equivalent to the type of the domain, otherwise you
   -- cannot apply this function to this argument; if they are beta-equivalent, then substitute the variable
   -- of quantification with the argument in the return-type, and this is the type of the whole application:
   if (not (betaEq ta at)) then throwError $ "Bad function argument type" else return $ subst x a rt
  -- the type of the function was not a Pi-type, therefore it wasn't a function after all; error!
  _ -> throwError $ "Non-function in application"

-- to type-check a Lambda:
tCheck r (Lam s t e) = do
 -- type-check the domain; we don't care what it type-checks to, we just care that it actually type-checks
 -- to *something* and doesn't fail with an error.
 -- we actually do care what it type-checks to; it must type-check to a Kind.
 tCheck r t
 -- then extend the Env with the type-assumption (<variable-of-quantification> : <domain-type)
 let r' = extend s t r
 -- type-check the body of the lambda under the extended Env
 te <- tCheck r' e
 -- the type of the whole lambda-expression is then a Pi-type with the same variable of quantification and
 -- domain, but as it's body has the *type* of the body of the lambda
 let lt = Pi s t te
 -- why do we have this? under what conditions can it fail?
 -- for example: "Lam x 5 e". 
 -- Why don't we just make sure that the "tCheck r t" above type-checks to a Kind?
 tCheck r lt
 --return the type of the lambda
 return lt

-- Star : Box
tCheck _ (Kind Star) = return $ Kind Box

-- Box has no type; like SetOmega
tCheck _ (Kind Box) = throwError "Found a Box"

-- r is the context
-- s is the kind of the type, under the assumptions r
-- t is the kind of the body, under the assumptions r,(x:a)
-- make sure this a valid kind for a Pi, and if so return the kind of the body
-- (are we sure it should be "return t" and not "return max(s,t)"?)
tCheck r (Pi x a b) = do
 s <- tCheckRed r a
 let r' = extend x a r
 t <- tCheckRed r' b
 if ((s, t) `notElem` allowedKinds) then throwError "Bad abstraction" else return t






-- type-check the given expression, starting with the empty Env
typeCheck :: Expr -> TC Type
typeCheck e =
 case tCheck initialEnv e of
 -- if there's any kind of error, the result will be a Left
 Left msg -> error ("Type error:\n" ++ msg)
 -- if it's a Right, then there was no error, so return the type t
 Right t -> return t


main :: IO ()
main = return ()
