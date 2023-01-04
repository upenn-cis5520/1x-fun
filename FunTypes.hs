{-
This file demonstrates type inference for FUN!

FUN types
=========
-}

module FunTypes where

import Control.Monad.Except (MonadError (throwError))
import Control.Monad.State (StateT (..))
import qualified Control.Monad.State as State
import Control.Monad.Writer
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
{-
In this lecture, we will explore type *inference* for functional
programming languages.  In particular, we will implement the
Hindley-Milner type inference algorithm, a function of whose type is:

      typeInference :: Expression -> Either String Type

That is, the function takes an expression in a simple purely functional
programming language, and returns either an error string, if the expression
has a type error, or the type inferred for the expression.

This algorithm is the basis for Haskell type inference. It was
originally developed by Robert Hindley (1969) in his study of
combinatory logic and was later rediscovered by Robin Milner (1978)
for use in ML.  Milner's student Luis Damas analyzed the properties of
this system in his Ph.D. dissertation (1985).

There are many presentations of the type system, and its type
inference algorithm, called *Algorithm W*. We'll follow the structure
that is most similar to the algorithm that GHC uses, though
GHC optimizes this algorithm to make it more efficient.

For more information about type inference in Haskell:

* Simon Peyton Jones's third lecture from OPLSS, slides and video from the
[website](http://www.cs.uoregon.edu/research/summerschool/summer13/curriculum.html).

* Dimitrios Vytiniotis, Simon Peyton Jones, Tom Schrijvers, and Martin
Sulzmann, OutsideIn(X): Modular type inference with local assumptions,
in Journal of Functional Programming, Cambridge University Press,
September 2011.

The FUN language
----------------

We'll work with the syntax and semantics of the simple, functional language
called FUN.

We already have the abstract syntax, parser and pretty printer available for
this language:
-}

{-
We also defined an environment-based evaluator:
-}

import FunEnv
import FunSyntax
  ( Bop (Minus, Plus, Times),
    Expression (..),
    PP (..),
    Variable,
    parse,
  )
import Text.PrettyPrint (Doc, ($$), (<+>), (<>))
import qualified Text.PrettyPrint as PP

{-
Recall that the evaluator is a function

    eval :: Expression -> Environment -> Value

that takes an environment and calculates the value of that expression, where
we had three sorts of values and where the Environment keeps track of the
values of variables (i.e. it was a `Map Variable Value`).

Type checking as abstract interpretation
----------------------------------------

We can view type checking as an *abstraction* of the evaluator. In other
words, instead of calculating a precise value for expressions, we'll
approximate those values with types.

Therefore, we need three type forms: `IntTy`, `BoolTy` and `FunTy`, one for
each value form.
-}

data Type
  = IntTy -- i.e. 'Int'
  | BoolTy -- i.e. 'Bool'
  | FunTy Type Type -- i.e. t1 -> t2
  | VarTy TypeVariable -- we'll get to this later
  deriving (Eq, Show)

instance PP Type where
  pp (VarTy i) = PP.text [i]
  pp (FunTy t1@(FunTy _ _) t2) = PP.parens (pp t1) <+> PP.text "->" <+> pp t2
  pp (FunTy t1 t2) = pp t1 <+> PP.text "->" <+> pp t2
  pp IntTy = PP.text "Int"
  pp BoolTy = PP.text "Bool"

{-
For type *inference*, we actually need one more form for type variables, which
we will get back to.
-}

type TypeVariable = Char

{-
Let's practice first with a type checker for *part* of our functional
language. We'll type check everything except for first-class functions (Fun)
and recursive bindings (Let). (We will see why those are tricky shortly.)

Just like the interpreter, we need a *type environment* to keep track of the
*types* of free variables.
-}

type TypeEnv = Map Variable Type

{-
Also like the interpreter, there is a case that we may not know anything about
the variable; for example if it is unbound. If that is so, we should produce a
type error. We'll use the following lookup function, that can report errors.
-}

tLookup :: MonadError String m => Variable -> Map Variable a -> m a
tLookup x env = do
  case Map.lookup x env of
    Just ty -> return ty
    Nothing -> throwError $ "Unbound variable " ++ x

{-
So, our simple type inferencer expects that the type environment will contain
bindings for all free variables of the expressions.
-}

inferTySimple :: Expression -> Map Variable Type -> Either String Type
{-
That means that for variables, we simply look up in the type environment the
type for the variable.
-}

inferTySimple (Var x) env = tLookup x env
{-
The cases for literals are also straightforward.
-}

inferTySimple (IntExp _) env = return IntTy
inferTySimple (BoolExp _) env = return BoolTy
{-
For `if` expressions, we first determine the types of the three
subexpressions. Then we record two constraints: the condition must
have boolean type, and the two branches of the `if` must have the same
type (which is also the type of the entire expression).
-}

inferTySimple (If e1 e2 e3) env = do
  ty1 <- inferTySimple e1 env
  ty2 <- inferTySimple e2 env
  ty3 <- inferTySimple e3 env
  unless (ty2 == ty3) $
    throwError "Different types in if expression"
  unless (ty1 == BoolTy) $
    throwError "Condition of an if must be a boolean"
  return ty2

{-
Likewise, inference for binary operators constrains the argument types to be
integers and returns the appropriate result type depending on the particular
operator.
-}

inferTySimple (Op b e1 e2) env = do
  ty1 <- inferTySimple e1 env
  ty2 <- inferTySimple e2 env
  when (ty1 /= IntTy || ty2 /= IntTy) $
    throwError "Operator arguments must be int"
  if b == Plus || b == Times || b == Minus
    then return IntTy
    else return BoolTy

{-
In the `App e1 e2` case, we know that the first subexpression must have a
function type, where the type of the argument is the same as the type of `e2`.
-}

inferTySimple (App e1 e2) env = do
  ty1 <- inferTySimple e1 env
  ty2 <- inferTySimple e2 env
  case ty1 of
    FunTy tyA tyB -> do
      unless (ty2 == tyA) $ throwError "Incorrect argument in application"
      return tyB
    _ -> throwError "Application of non-function"
inferTySimple (Let x e1 e2) env = error "Let unimplemented"
inferTySimple (Fun x e1) env = error "Fun unimplemented"

{-
Here are some test cases to give it a spin. Even though we can't define our own
functions yet, we can assume that there are already some defined for us by
putting their types in an initial type environment:
-}

prelude :: Map String Type
prelude =
  Map.fromList
    [ ("NOT", FunTy BoolTy BoolTy),
      ("AND", FunTy BoolTy (FunTy BoolTy BoolTy)),
      ("OR", FunTy BoolTy (FunTy BoolTy BoolTy))
    ]

{-
Think about which of these test cases should pass and which should fail:
-}

simpleTop :: String -> String
simpleTop s = case parseExp s >>= \e -> inferTySimple e prelude of
  Left err -> err
  Right t -> s ++ " : " ++ show (pp t)

-- >>> simpleTop "1 + 3"
-- "1 + 3 : Int"

-- >>> simpleTop "if 1 < 3 then 1 + 3 else 4 * 5"
-- "if 1 < 3 then 1 + 3 else 4 * 5 : Int"

-- >>> simpleTop "if 1 < 3 then true else 4 * 5"
-- "Different types in if expression"

-- >>> simpleTop "if (NOT true) then AND else OR"
-- "if (NOT true) then AND else OR : Bool -> Bool -> Bool"

{-
Guessing Types and Polymorphism
-------------------------------

What is the difficulty with `Fun` and `Let`?

Well, what should the type of this function be?
-}

example0 :: String
example0 = "fun X -> X + 1"

{-
It is not too hard for *us* to figure out, but our simple type checker cannot do it.
We'd like to write something like this...

      inferTySimple (Fun x e) env = do
           let argTy = ...
           resTy <- inferTySimple e (Map.insert x argTy env)
           return (FunTy argTy resTy)

but what is `argTy`, the argument type of the function? How can the type checker guess
it?

Here is another problem.  What should be the type of a function like this?
-}

example1 :: String
example1 = "fun X -> X"

{-
This function should work for any type of input, and it will obviously return
something of the same type.  By analogy with Haskell, a good type for it would
be `a -> a`. In fact, this is the reason that we include type variables in
types above---so that we have a type for this expression.

However, we will see that type variables also solve the more general problem
of type checking functions. The basic idea is that when we typecheck a
function, we can create a "fresh" type variable for the argument type and then
later figure out what that type actually should be.

      inferTy (Fun x e) env =
         do  tv <- fresh
             let argTy = VarTy tv
             resTy <- inferTy e (Map.insert x argTy env)
             return (FunTy argTy resTy)

Ok, let's do it.

We will rewrite our type inferencer, this time in a monad called `TcMonad`.

      inferTy :: Expression -> TypeEnv -> TcMonad Type

What should this monad contain?

* When we typecheck a function expression, like `fun X -> X`, we'll
introduce a type variable for the type of `X`, and that type variable
needs to be different from any other type variable that has been
introduced so far, to avoid confusion.  For example, consider:
-}

example2 :: String
example2 = "fun X -> fun Y -> X"

{-
This expression should have type `a -> b -> a`, so we need to make sure that
the type variable that we introduce for `Y` is different from the one that we
introduce for `X`.  Therefore, our monad also needs the ability to generate
*fresh* type variables.
-}

fresh :: TcMonad TypeVariable
fresh = do
  State.modify succ
  State.get

{-
* Now consider this function
-}

example3 :: String
example3 = "fun X -> X + 1"

{-
In this example, the type of the argument to the function should be `Int`
instead of `a`. But we won't know that until we see that `X` is used as the
argument to addition. To accommodate this sort of reasoning, we'll break type
inference into two steps:

   * First, we will traverse the syntax of the expression, using type
     variables for unknown types and gathering constraints about types. This part
     only fails for unbound (term) variables.

   * Then we solve those constraints, potentially resolving some type
     variables to concrete types like Int. It may be that the constraints are
     impossible to solve, in which case there is a type error in the
     program.

For example, type inference for `example3` above will determine that
it has type `a -> Int` under the constraint that `a = Int`. From this,
we can work out that the actual type of the expression is `Int ->
Int`.

Thus, we need a data structure for representing type equality
constraints and a way to tell the type inference monad to record these
constraints.
-}

data Constraint = Equal Type Type

equate :: Type -> Type -> TcMonad ()
equate t1 t2
  | t1 == t2 = return ()
  | otherwise = tell [Equal t1 t2]

{-
In summary, we put this all together in the monad:
-}

type TcMonad a =
  WriterT
    [Constraint] -- gathered constraints
    ( StateT
        TypeVariable -- generator for new type variables
        (Either String) -- error messages (for unbound variables)
    )
    a

{-
Running the first part of the type checker either produces an error
(for an unbound variable) or succeeds with a type and a list of
constraints.
-}

runTc :: TcMonad a -> Either String (a, [Constraint])
runTc m = State.evalStateT (runWriterT m) 'a'

{-
Constraint Generation
=====================

So let's write the first part of type inference, which
works with the above monad to infer the type (and constraints) of an
expression.
-}

inferTy :: Expression -> TypeEnv -> TcMonad Type
{-
Some of this version looks the same as above:
-}

inferTy (Var x) env = tLookup x env
inferTy (IntExp _) env = return IntTy
inferTy (BoolExp _) env = return BoolTy
{-
For `if` expressions, instead of checking type right away, we record two
constraints: the condition must have boolean type, and the two branches of the
`if` must have the same type (which is also the type of the entire
expression).
-}

inferTy (If e1 e2 e3) env = do
  t1 <- inferTy e1 env
  t2 <- inferTy e2 env
  t3 <- inferTy e3 env
  equate t2 t3
  equate t1 BoolTy
  return t2

{-
Likewise, inference for boolean operators constrains the argument types to be
integers and returns the appropriate result type depending on the particular
operator.
-}

inferTy (Op b e1 e2) env = do
  t1 <- inferTy e1 env
  t2 <- inferTy e2 env
  equate t1 IntTy
  equate t2 IntTy
  if b == Plus || b == Times || b == Minus
    then return IntTy
    else return BoolTy

{-
For function definitions (the `Fun` case) we assign the formal
parameter `x` a fresh type variable and then analyze the body `e`
using that type variable. The type of the function is a function type
from that type variable to the type of the body.  (Of course, we
expect that checking the body of the function may also place
constraints on the type variable.)
-}

inferTy (Fun x e) env = do
  a <- fresh
  ty <- inferTy e (Map.insert x (VarTy a) env)
  return $ FunTy (VarTy a) ty

{-
In the `App e1 e2` case, we know that the first subexpression must have
a function type, where the type of the argument is the same as the type
of `e2`. However, we don't know what the result type should be, so we
generate a fresh type variable.
-}

inferTy (App e1 e2) env = do
  t1 <- inferTy e1 env
  t2 <- inferTy e2 env
  a <- fresh
  equate t1 (FunTy t2 (VarTy a))
  return (VarTy a)

{-
Finally, for the case of a (recursive) let-binding we create a fresh type
variable for the type of `e1` and then add it to the environment before type
checking the right-hand-side and the body of the expression.  (Note: This is
not what Haskell does, when we get to polymorphism we'll need to tweak this
part.)
-}

inferTy (Let x e1 e2) env = do
  a <- fresh
  let xTy = VarTy a
  t1 <- inferTy e1 (Map.insert x xTy env)
  equate t1 (VarTy a)
  inferTy e2 (Map.insert x xTy env)

{-
Seeing the generated constraints
--------------------------------

With a little code for pretty printing types and constraints, we can
take a look at what constraints are generated for the various
examples.
-}

instance PP Constraint where
  pp (Equal t1 t2) = pp t1 <+> PP.text "=" <+> pp t2

genConstraints :: Expression -> Either String (Type, [Constraint])
genConstraints = runTc . (`inferTy` Map.empty)

parseExp :: String -> Either String Expression
parseExp s = case parse s of
  Just e -> Right e
  Nothing -> Left "parse error"

putConstraints :: String -> PP.Doc
putConstraints s = case parseExp s >>= runTc . (`inferTy` Map.empty) of
  Left err -> PP.text err
  Right (t, c) ->
    (PP.text s <+> PP.text ":" <+> pp t $$ PP.text "where")
      <+> PP.vcat (map pp c)

example4 :: String
example4 = "let F = fun X -> if X <= 1 then 1 else F (X - 1) in F"

-- >>> putConstraints example4
-- let F = fun X -> if X <= 1 then 1 else F (X - 1) in F : b

{-
where c = Int
      c = Int
      b = Int -> d
      Int = d
      b = c -> Int

Here are some trickier ones:
-}

-- >>> putConstraints "(fun X -> let Y = X in Y) 3"

{-
(fun X -> let Y = X in Y) 3 : d
where
 c = b
 b -> c = Int -> d
-}

-- >>> putConstraints "(fun F -> fun X -> F X + 1) (fun Y -> Y)"

{-
(fun F -> fun X -> F X + 1) (fun Y -> Y) : f
where b = c -> d
      d = Int
      b -> c -> Int = (e -> e) -> f
-}

-- >>> putConstraints "(fun F -> fun X -> F (F X)) (fun Y -> if Y then 1 else 0)"

{-
(fun F -> fun X -> F (F X)) (fun Y -> if Y then 1 else 0) : g
where b = c -> d
      b = d -> e
      f = Bool
      b -> c -> e = (f -> Int) -> g

Activity: solve the constraints to determine the types generated by these examples.
(Or figure out the terms don't type check!)

1.

         (fun X -> let Y = X in Y) 3 : c
         where b = a
               a -> b = Int -> c

Is this solvable (i.e. satisfiable)?  What substitution satisfies these constraints?

What is the type? Int

2.
            (fun F -> fun X -> F X + 1) (fun Y -> Y) : e
            where a = b -> c
                  c = Int
                  a -> (b -> Int) = (d -> d) -> e

Is this satisfiable? What is the solution?

3.

            (fun F -> fun X -> F (F X)) (fun Y -> if Y then 1 else 0) : f
            where a = b -> c
                  a = c -> d
                  e = Bool
                  a -> (b -> d) = (e -> Int) -> f

Is this satisfiable? What is the solution?

Unification
===========

As we saw in our informal overview, the inference algorithm proceeds
by traversing the expression, generating fresh type variables for
unknown types and generating constraints about the types of
sub-expressions based on how they are used.

These constraints are then solved by a process called *unification*,
which produces a mapping from type variables to types. We can use this
mapping, called a *substitution*, to replace all occurrences of type
variables with their definitions.

We now formalize the notion of substitution and use this to define the
unification procedure.
-}

newtype Substitution = Subst (Map TypeVariable Type) deriving (Show, Eq)

{-
The function `subst` takes a substitution and applies it to a type by
replacing variables in the type with the corresponding mapping in the
substitution (if any).
-}

subst :: Substitution -> Type -> Type
subst (Subst s) (VarTy a) = fromMaybe (VarTy a) (Map.lookup a s)
subst s (FunTy t1 t2) = FunTy (subst s t1) (subst s t2)
subst s IntTy = IntTy
subst s BoolTy = BoolTy

{-
The empty substitution leaves any type unchanged ...
-}

empSubst :: Substitution
empSubst = Subst Map.empty

{-
and we can *compose* two substitutions as `s1 after s2` ...
-}

after :: Substitution -> Substitution -> Substitution
Subst s1 `after` Subst s2 = Subst $ Map.map (subst (Subst s1)) s2 `Map.union` s1

{-
to form a single substitution that applies the substitutions in `s1` *after*
it applies those in `s2`. (This means we need to propagate s1 through the
range of s2).  This composition is only valid when the domains of `s1` and
`s2` are disjoint, which the unification algorithm will have to ensure.

For example, if s2 is { a := Int } and  s1 is { b := (a -> Bool) }, then for
`s2 after s1` we should get the combined substitution

        { a := Int, b := (Int -> Bool) }
-}

s2 :: Substitution
s2 = Subst (Map.fromList [('a', IntTy)])

s1 :: Substitution
s1 = Subst (Map.fromList [('b', FunTy (VarTy 'a') BoolTy)])

-- >>> s2 `after` s1
-- Subst (fromList [('a',IntTy),('b',FunTy IntTy BoolTy)])

{-
Most General Unifiers
---------------------

Armed with the above, we can formally define the notion of *type
unification*.  We want unification to have the following informal
behavior:

**T1**     **T2**        **Unified**     **Substitution**
-------	   ------        -----------     ----------------
`a`	   `Int`            Int              a :-> Int
`a`        `b`               a               b :-> a
`a->b`     `a->d`          a -> b            d :-> b
`a->Int`   `Bool->b`      Bool -> Int        a :-> Bool, b :-> Int
`Int`      `Int`             Int               empty
`Int`      `Bool`            none              none
`Int`      `a->b`            none              none
`a`        `a->Int`          none              none

The first few cases are where unification is indeed possible, and the
last few cases are where it fails corresponding to a *type error* in
the source program. The very last case is an interesting one: the
failure is because the type variable `a` in the first type occurs
inside the second type. Thus, if we try substituting `a` with `a->Int`
we will just keep spinning forever! Hence, this also throws a
unification failure.

**Exercise:** Write a Haskell program that is rejected by the
typechecker because it fails the above *occurs check*.  Chances are
you've done it any number of times already!

Here is the unification function `mgu`, which takes two types as input
and either returns a successful unified output along with the
substitution (as shown in the table above) or an error string
explaining the failure (hence, our use of an error monad to describe
output.)
-}

mgu :: Type -> Type -> Either String Substitution
mgu IntTy IntTy = return empSubst
mgu BoolTy BoolTy = return empSubst
mgu (FunTy l r) (FunTy l' r') = do
  s1 <- mgu l l'
  s2 <- mgu (subst s1 r) (subst s1 r')
  return $ s2 `after` s1
mgu (VarTy a) t = varAsgn a t
mgu t (VarTy a) = varAsgn a t
mgu _ _ = throwError "types don't unify"

{-
The function `varAsgn` attempts to assign a type variable to a type
and return that assignment as a substitution, but throws an error if
the variable occurs within the assigned type.
-}

varAsgn :: TypeVariable -> Type -> Either String Substitution
varAsgn a (VarTy b) | a == b = return empSubst
varAsgn a t =
  if a `Set.member` fv t
    then throwError "occurs check fails"
    else return $ Subst (Map.insert a t Map.empty)

fv :: Type -> Set TypeVariable
fv (VarTy v) = Set.singleton v
fv (FunTy t1 t2) = fv t1 `Set.union` fv t2
fv IntTy = Set.empty
fv BoolTy = Set.empty

{-
The name `mgu` stands for *Most-General Unifier* ; the function is
guaranteed to find the most general unification possible (for example,
it will _not_ unify `a` and `b` via the substitution `a :=
Int, b := Int`, but will rather unify them to `a` by the substitution
`b := a`.)  This property is crucial for showing that type inference
returns the most general type possible for any term (that is, `a -> a`
and not `Int -> Int` for the identity function).

Test cases for mgu:
-}

-- >>> mgu (VarTy 'a') IntTy
-- Right (Subst (fromList [('a',IntTy)]))

-- >>> mgu (VarTy 'a') (VarTy 'b')
-- Right (Subst (fromList [('a',VarTy 'b')]))

-- >>> mgu (FunTy (VarTy 'a') (VarTy 'b')) (FunTy (VarTy 'a') (VarTy 'd'))
-- Right (Subst (fromList [('b',VarTy 'd')]))

-- >>> mgu (FunTy (VarTy 'a') IntTy)       (FunTy BoolTy      (VarTy 'b'))
-- Right (Subst (fromList [('a',BoolTy),('b',IntTy)]))

-- >>> mgu IntTy IntTy
-- Right (Subst (fromList []))

-- >>> mgu IntTy BoolTy
-- Left "types don't unify"

-- >>> mgu IntTy (FunTy (VarTy 'a') (VarTy 'b'))
-- Left "types don't unify"

-- >>> mgu (VarTy 'a') (FunTy (VarTy 'a') (VarTy 'b'))
-- Left "occurs check fails"

{-
We can solve an entire list of constraints by running the `mgu`
function on each one and combining the resulting substitutions with
`after`.
-}

solve :: [Constraint] -> Either String Substitution
solve = foldM process empSubst
  where
    process s1 (Equal t1 t2) = do
      s2 <- mgu (subst s1 t1) (subst s1 t2)
      return (s2 `after` s1)

{-
Putting it all together
=======================

Finally, we have all the pieces necessary to define the `typeInference`
function promised at the beginning.
-}

typeInference :: Expression -> Either String Type
typeInference e = do
  (ty, constraints) <- genConstraints e
  s <- solve constraints
  return (subst s ty)

top :: String -> PP.Doc
top s = case parseExp s >>= typeInference of
  Left err -> PP.text err
  Right t -> PP.text s <+> PP.colon <+> pp t

{-
We can now try it out on our running examples:
-}

-- >>> top example1
-- fun X -> X : b -> b

-- >>> top example2
-- fun X -> fun Y -> X : b -> c -> b

-- >>> top example3
-- fun X -> X + 1 : Int -> Int

-- >>> top example4
-- let F = fun X -> if X <= 1 then 1 else F (X - 1) in F : Int -> Int

{-
As well as a few that don't type check:
-}

-- >>> top "X + 1"
-- Unbound variable X

-- >>> top "1 + true"
-- types don't unify

-- >>> top "(fun X -> X + 1) true"
-- types don't unify

-- >>> top "fun X -> X X"
-- occurs check fails

{-
Polymorphism
============

What about polymorphic functions?

We've seen in Haskell that some functions have polymorphic types, but
(perhaps surprisingly) we don't have that here (yet).  The type
inference algorithm that we've developed so far looks like it is
almost there. The type of `fun X -> X` is `a -> a`, meaning that this
function should be applicable at any type.
-}

example5 = "let Y = (fun X -> X) true in (fun X -> X) 3"

{-
This looks good so far.  But unfortunately, if we give the identity
function a _name_, the example no longer works.
-}

example6 = "let I = fun X -> X in let Y = I true in I 3"

{-
The variable `I` has type `a -> a` in the typing environment, but each
use of `I` adds constraints to `a` and we end up trying to unify
`IntTy` with `BoolTy`, which fails.

The key change that we need is to store 'type schemes' instead of
types in the typing environment. Type schemes represent polymorphic
types -- they indicate that the corresponding expression variable is
polymorphic.  For example, in Haskell, the identity function has type
`forall a. a -> a`.  The "forall" part is often omitted when we write
types -- i.e., we often elide the difference between types and type
schemes -- but for type inference it is a crucial distinction.

To see how polymorphic type inference works, let's see how we infer a
type for `example6`, step by step:

1) Typecheck the right-hand side (`fun X -> X`) of the `let`.  The
result is `a -> a`, for a fresh type variable `a`.

2) *Generalize* `a -> a` to the type scheme `forall a. a -> a`, extend
the environment with the binding `I |-> forall a. a -> a`, and
recursively infer a type for the body (`let Y = I true in I 3`) in
this context.

3) When we get to the first use of `I` in the application `I true`, we
*instantiate* its type by making up a fresh type variable `b` and
substituting it for the universally quantified variable `a` to get the
type `b -> b` for this occurrence of `I`.  This gives us the type
`Bool` for the application `I true`.  (Strictly speaking, it gives us
the type `b` for the application, plus the constraint `b = Bool`.)

4) Extend the environment with a binding of `Y` to the type `Bool`
(or, if you like, `b`, remembering that `b = Bool`) and recursively
infer a type for the body of the `let`, i.e., `I 3`.

5) When we get to the use of `I` in the application `I 3`, we again
instantiate its type using a new fresh type variable `c` to get the
type `c -> c` for this occurrence of `I`.  This gives us the type
`Int` for the application `I 3` (i.e., it gives us the type `c` for
the application, plus the constraint `c = Int`.)

6) The type of the whole `example6` is now `Int` (i.e., `c`, with the
constraints `b = Bool` and `c = Int`).

One point that must be understood clearly is that the generalization
step happens *only* at `let` bindings.  To see this distinction
more clearly, consider the following examples:
-}

example7a = "let I = fun X -> X in I I"

example7b = "let J = fun X -> X X in J"

{-
In `example7a`, the function `I` is `let`-bound, so its type will be
generalized to `forall a. a -> a`.  This means that each occurrence of
`I` in `I I` will be instantiated with a different fresh type
variable, i.e., the first `I` will have type `b -> b` and the second
will have type `c -> c`.  The application `I I` (and hence the whole
example) will thus have type `b`, with the constraint `b = c -> c`.

In `example7b`, on the other hand, the type of the formal parameter
`X` is just `a -> a`, so both uses of `X` in the application `X X` are
given this type; this generates the constraint `a = a -> a` for the
application, which fails the occur check, and so the whole expression
is not typeable.

Implementing Polymorphic Type Inference
---------------------------------------

With these intuitions in mind, here are the extensions we need.
First, a representation for type schemes:
-}

data Scheme = Forall (Set TypeVariable) Type

{-
We will need to change the definition of type environment from types to type
schemes.

Next, instantiation: we need to create a version of the type where
all generalized type variables have been replaced by fresh variables.
-}

instantiate :: Scheme -> TcMonad Type
instantiate (Forall vs ty) = do
  let combine s v = do
        x <- fresh
        return $ Subst (Map.singleton v (VarTy x)) `after` s
  s <- foldM combine empSubst (Set.toList vs)
  return (subst s ty)

{-
Finally, generalization.  Here, though, we need to be careful about
one more thing.  If the right-hand side of the `let` _shares_ any
type variables with the current typing environment, then it is _not_
correct to generalize these variables (as this would break the
connection between different occurrences of the same variable).  For
example, when typechecking
-}

example8 = "fun X -> let Y = X in Y + 1"

{-
if we choose `a` as the type of `X`, then we would _not_ want to
generalize the type of `Y` from `a` to `forall a. a`, as this would
give us the (unsound) type `a -> Int` for the whole expression.

For this reason, during generalization, we need to calculate the "free
variables" of both the inferred type of right-hand side and the
current type environment and generalize only the ones that appear in
the type but not also in the environment.
-}

generalize :: TypeEnv -> TcMonad Type -> TcMonad Scheme
generalize env m = do
  (ty, constraints) <- listen m
  case solve constraints of
    Left err -> throwError err
    Right s -> do
      let sty = subst s ty
      let fvs = fv sty `minus` fvEnv (substEnv s env)
      return (Forall fvs sty)

substEnv :: Substitution -> TypeEnv -> TypeEnv
substEnv s = Map.map (subst s)
  where
    substs :: Substitution -> Scheme -> Scheme
    substs s (Forall vs ty) = Forall vs (subst s ty)

{-
The function `fv` here calculates the set of variables that appear in
a type (after constraint solving).
-}

fvEnv :: TypeEnv -> Set TypeVariable
fvEnv = Map.foldr gather Set.empty
  where
    gather ty s = undefined

minus :: Ord a => Set a -> Set a -> Set a
minus = Set.foldr Set.delete

{-
To integrate this extension with our existing type inference code in
the earlier part of this file, we just need to change a few places:

1) Change the definition of type environment from types to type schemes.

2) Change the places where variables are added to the type environment
to either generalize (if we are adding a `let`-bound variable) or add
a trivial empty quantifier (for a `fun`-bound variable).

3) Use `instantiate` to change a type scheme back to a type when we
look up a variable in the environment.

A few more examples...
-}

-- >>> top "let I = fun X -> let Y = X in Y in I I"

-- >>> top "let I = fun X -> X in let F = fun X -> I X in F"

-- >>> top "let I = fun X -> X in let F = fun X -> let Y = I X in Y + 1 in F"
