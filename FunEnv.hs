{-
Interpreters for functional programming languages
=================================================>

Interpreters
------------
-}

module FunEnv where

import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
{-
So far, we have seen how to write an interpreter for a simple
imperative language with While loops. But what about something closer
to home?  What if you wanted to write an interpreter for Haskell?  Or
for Ocaml?  Or Scheme? Or Clojure?

Today we'll implement an interpreter (or two) for small purely functional
language that captures the essence of these languages. This language is called
FUN.

The abstract syntax for this language is in the module
[FunSyntax](FunSyntax.lhs), together with a parser and pretty-printer
for its concrete syntax.
-}

import FunSyntax
  ( Bop (..),
    Expression (..),
    Variable,
    factExp,
    parse,
  )

{-
An Interpreter for FUN
----------------------

In some sense, writing an interpreter for FUN is *easy* because it is
so similar to Haskell. In the interpreter below, we will lean on
Haskell's features to implement similar structures for FUN.
For example, we can use Haskell integer and boolean
values to represent FUN's integer and boolean values; and use
Haskell's plus operator to implement addition in FUN.

We'll use also this trick to implement higher-order functions.  To
extend the datatype of values with function values, we'll just use
Haskell functions!
-}

data Value
  = IntVal Int
  | BoolVal Bool
  | -- new! function values
    FunVal (Value -> Value)

instance Show Value where
  show (IntVal i) = show i
  show (BoolVal b) = show b
  show (FunVal _) = "<function>" -- can't show functions

{-
Now, on to the interpreter itself.  The interpreter for boolean operators
is straightforward...
-}

evalB :: Bop -> Value -> Value -> Value
evalB Plus (IntVal i1) (IntVal i2) = IntVal (i1 + i2)
evalB Minus (IntVal i1) (IntVal i2) = IntVal (i1 - i2)
evalB Times (IntVal i1) (IntVal i2) = IntVal (i1 * i2)
evalB Gt (IntVal i1) (IntVal i2) = BoolVal (i1 > i2)
evalB Ge (IntVal i1) (IntVal i2) = BoolVal (i1 >= i2)
evalB Lt (IntVal i1) (IntVal i2) = BoolVal (i1 < i2)
evalB Le (IntVal i1) (IntVal i2) = BoolVal (i1 <= i2)
evalB _ _ _ = IntVal 0

{-
... and we can use a finite map to keep track of the values of
variables.
-}

type Environment = Map Variable Value

{-
If a variable is not found in the environment, we'll return "0".
For simplicity, we won't trigger runtime errors in the interpreter now.
That will come later.)
-}

slookup :: Variable -> Environment -> Value
slookup x m = fromMaybe (IntVal 0) (Map.lookup x m)

{-
So our interpreter using the following type:

     eval :: Expression -> Environment -> Value

We'll pass the current value of the store as an additional argument to
the evaluator. When we extend the store, the extension is only
temporary -- and it follows the recursive structure of the evaluator
itself... which just so happens to match the lexical structure of the
term. Nifty!

[Aside: we could also use the state monad for the interpreter, but this
would not work as nicely. In that case our evaluator would have type

    eval :: Expression -> State Environment Value

which is essentially equivalent to:

    eval :: Expression -> Environment -> (Value, Environment)

That is, every call to `eval` returns a *new* Environment.  However, the
language we are interpreting is _pure_ -- there is no way to change
the value of a FUN variable -- so the fact that we get access to the
resulting `Environment` is of no use to us.]

Here is the implementation of the environment-based evaluator for FUN. Again,
in the case of a "runtime type error" the evaluator just returns "0".
-}

eval :: Expression -> Environment -> Value
eval (Var x) s = slookup x s
eval (IntExp i) s = IntVal i
eval (BoolExp i) s = BoolVal i
eval (Op o e1 e2) s = evalB o (eval e1 s) (eval e2 s)
eval (If e1 e2 e3) s = case eval e1 s of
  BoolVal b -> if b then eval e2 s else eval e3 s
  _ -> IntVal 0
{-
We need to update the variable mapping when we evaluate functions.
The value of a function expression is a Haskell function (whose
argument will be used to provide the value of the bound variable when
evaluating the body of the function).
-}

eval (Fun x e) s = FunVal g
  where
    g :: Value -> Value
    g v = eval e (Map.insert x v s)

{-
(Make sure you understand this bit -- it's the crux of the evaluator!)

We can then evaluate a function application by applying the function
value to its argument.
-}

eval (App fun arg) s = case eval fun s of
  FunVal g -> g (eval arg s)
  _ -> IntVal 0
{-
Finally, in the case of a recursive definition for x, we need to
evaluate the right-hand-side using a store that maps x to the value
that we are currently computing?!  Whoa!  We're using a Haskell
recursive definition to define recursive definitions in FUN.
-}

eval (Let x e1 e2) s =
  let v = eval e1 s'
      s' = Map.insert x v s
   in eval e2 s'

{-
Let's give it a try!

Our first test cases are for simple expressions
-}

parseAndEval :: String -> Maybe Value
parseAndEval s = fmap (`eval` Map.empty) (parse s)

-- >>> parseAndEval "1 + 3"
-- Just 4

-- >>> parseAndEval "(fun X -> fun Y -> X) 1 2"
-- Just 1

-- >>> parseAndEval "(fun X -> fun Y -> Y) 1 2"
-- Just 2

{-
Once we finish recursive definitions, we can do factorial...
-}

-- >>> eval factExp Map.empty
-- 120

{-
Now let's do fibonacci.
-}

fibString :: String
fibString = "let F = fun X -> if X <= 1 then 1 else F (X - 1) + F (X - 2) in F"

-- >>> parseAndEval ("(" ++ fibString ++ ") " ++ "5")
-- Just 8

{-
Here's another way to write factorial of 5, based on the [Y combinator](https://en.wikipedia.org/wiki/Y_Combinator):
-}

yExp :: String
yExp = "(fun F -> (fun X -> F (X X)) (fun X -> F (X X)))"

fExp :: String
fExp = "(fun FACT -> fun X -> if X <= 0 then 1 else X * FACT (X - 1)))"

-- >>> parseAndEval ("(" ++ yExp ++ " " ++ fExp ++ " 5)")
-- Just 120

{-
Here are tests that involve defining infinite loops.
-}

-- >>> parseAndEval "let LOOP = fun Y -> LOOP Y in LOOP"
-- Just <function>

-- THIS IS AN INFINITE LOOP!!
-- >>> parseAndEval "let LOOP = fun Y -> LOOP Y in LOOP 1"
-- ProgressCancelledException

{-
This test demonstrates that our language uses call-by-need evaluation. Even though
the argument is an infinite loop, it is never evaluated.
-}

-- >>> parseAndEval "let LOOP = fun Y -> LOOP Y in (fun Z -> 2) (LOOP 3)"
-- Just 2

{-
In fact, we can even create a simple REPL (read-eval-print loop) for
evaluating expressions and showing their results.
-}

replE :: IO ()
replE = do
  putStr "%> "
  line <- getLine
  case parse line of
    Just exp -> do
      print (eval exp Map.empty)
      replE
    Nothing -> putStrLn "what?!?" >> replE
