{-
A Continuation-Passing Interpreter
==================================
-}

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import FunSyntax (Bop (..), Expression (..), Variable, parse)
import Prelude hiding (map)

{-
The environment-passing interpreter establishes the *data context* in
which a FUN program is executed.

Next, we will do the same for the *control context*, a reification of
the call stack of the interpreter. This control context determines how
evaluation happens in the interpreter, what gets evaluated when, and
what will happen to the result. In the environment-passing
interpreter, this control context was the same as the control context
of Haskell. However, once we make the control context explicit, we'll
be able to change it---including making the evaluation of function
arguments eager instead of lazy.

Programs with explicit control contexts are said to be written in
*continuation-passing* style.

Continuation-Passing Style
--------------------------

When are control contexts implicitly created? Consider this evaluation
of an expression involving the factorial function:
-}

fact :: Int -> Int
fact x =
  if x <= 1 then 1 else x * fact (x - 1)

{-
     fact 4
     ==
     4 * fact 3
     ==
     4 * (3 * fact 2)
     ==
     4 * (3 * (2 * fact 1))
     ==
     4 * (3 * (2 * 1))
     ==
     4 * (3 * 2)
     ==
     4 * 6
     ==
     24

Each call of `fact` is made with the promise that the value returned
will be multiplied by the value of the parameter at the time of the
call. Thus, `fact` is invoked with larger and larger control contexts
as the calculation proceeds.

Compare this version to this version of factorial, written in
continuation-passing style.
-}

fact_cps :: Int -> (Int -> Int) -> Int
fact_cps x k =
  if x <= 1 then k 1 else fact_cps (x -1) (\v -> k (x * v))

{-
The extra argument `k` represents the _continuation_ of a call to
`fact_cps` -- a function that takes the result of `fact_cps` and
"finishes the rest of the computation" (i.e., conceptually, the whole
rest of the program).

Let's see what happens when we call `fact_cps` using `id` as the first
continuation.

~~~~{.haskell}
     fact_cps 4 id
     ==
     fact_cps 3 (\v -> id (4 * v))
     ==
     fact_cps 2 (\v' -> (\v -> id (4 * v)) (3 * v'))
     ==
     fact_cps 1 (\v'' -> (\v' -> (\v -> id (4 * v)) (3 * v')) (2 * v''))
     ==
     (\v'' -> (\v' -> (\v -> id (4 * v)) (3 * v')) (2 * v'')) 1
     ==
     (\v' -> (\v -> id (4 * v)) (3 * v')) (2 * 1)
     ==
     (\v -> id (4 * v)) (3 * (2 * 1))
     ==
     id (4 * (3 * (2 * 1)))
     ==
     (4 * (3 * (2 * 1)))
     ==
     24
~~~~

Note how the control context is made explicit in the continuation
argument to `fact_cps`. In other words, we never have a call to
`fact_cps` that is the argument to some other computation. Instead,
each step remembers what to do with the result by building a
first-class function to receive it. When we get to the bottom of the
recursion, we begin evaluating these continuations.

Intuitively, when we write in continuation-passing style (CPS), a
function never returns a result to its caller.  Instead, when it
finishes computing its result, it _calls_ a continuation (a function
of one argument) that has been provided by its caller.

CPS makes several things explicit that are left implicit in the usual
"direct" style, including:

    - return points (which which become explicit
      as calls to the continuation);

    - intermediate values in compound expressions (which become
      bound variables in continuation functions);

    - order of argument evaluation; and

    - tail calls, which are simply places where a call to a
      sub-function is given exactly the same continuation that was
      passed to the caller.

We can also mix code written in CPS and in direct style.

Examples
--------

Let's practice transforming some simple functions into CPS...
-}

plus1 :: Int -> Int
plus1 = \x -> x + 1

plus1_cps :: Int -> (Int -> t) -> t
plus1_cps x k = k (x + 1)

plus2 :: Int -> Int
plus2 = \x -> plus1 (plus1 x)

plus2_cps :: Int -> (Int -> t) -> t
plus2_cps x k = undefined

plus :: Int -> Int -> Int
plus = \x y -> x + y

plus_cps :: Int -> Int -> (Int -> t) -> t
plus_cps = undefined

times_cps :: Int -> Int -> (Int -> t) -> t
times_cps = undefined

f :: Int -> Int
f = \x -> x + (x * 3)

f_cps :: Int -> (Int -> t) -> t
f_cps x k = undefined

fib :: Int -> Int
fib n = if n < 2 then 1 else fib (n -2) + fib (n -1)

fib_cps :: Int -> (Int -> t) -> t
fib_cps = undefined

-- >>> fib_cps 10 id
-- 89

map :: (a -> b) -> [a] -> [b]
map f [] = []
map f (x : xs) = f x : map f xs

map_cps :: (a -> (b -> t) -> t) -> [a] -> ([b] -> t) -> t
map_cps = undefined

-- >>> map_cps (\x k -> k (x + 1)) [1,2,3] id
-- [2,3,4]

{-
A CPS Interpreter for FUN
-------------------------

The CPS version of our FUN evaluator will take a new third
parameter. This parameter, the *continuation*, is an abstraction of
the control context in which a FUN expression is evaluated.  The goal
is to rewrite the interpreter in CPS -- i.e., to write it so that no
call to `eval` builds control context: all of the control context will
be contained in the continuation parameter.

     eval :: Expression -> Environment -> Cont -> Value

What is the type of the continuation here?  It is a first-class
function that takes the result of the expression and completes the
computation. In other words, it needs to take a `Value` and returns a
`Value`.
-}

type Cont = Value -> Value

{-
Another change that we need to make is to the definition of the
`Value` type itself.  We'll still represent the result of evaluating a
FUN function as a Haskell function, but now that function will also
take a continuation argument.
-}

data Value
  = IntVal Int
  | BoolVal Bool
  | -- NOTE: all functions take a continuation as an extra argument,
    -- including function values!
    FunVal (Value -> Cont -> Value)

{-
Some parts of the evaluator can remain exactly the same as before,
such as looking things up in the environment and evaluating boolean
operators.  (We won't bother to CPS these parts, though we could.)
-}

instance Show Value where
  show (IntVal i) = show i
  show (BoolVal b) = show b
  show (FunVal f) = "<function>"

type Environment = Map Variable Value

slookup :: Variable -> Environment -> Value
slookup x m = fromMaybe (IntVal 0) (Map.lookup x m)

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
Now the rest of the evaluator needs to be rewritten to use the
continuation argument explicitly.
-}

eval :: Expression -> Environment -> Cont -> Value
{-
For expressions that are already values, the change is simple.  We
just create the corresponding value and pass it directly to the
continuation argument.
-}

eval (Var x) s k = k (slookup x s)
eval (IntExp i) s k = k (IntVal i)
eval (BoolExp i) s k = k (BoolVal i)
eval (Fun x e) s k = k (FunVal (\v -> eval e (Map.insert x v s)))
{-
In an if-expression, we need to first evaluate the condition.  We do
so by creating a continuation that receives the result of evaluating
the guard and then evaluates the appropriate branch (or returns 0 if
the guard did not yield a boolean value).
-}

eval (If e1 e2 e3) s k =
  eval
    e1
    s
    ( \v1 ->
        case v1 of
          BoolVal b -> if b then eval e2 s k else eval e3 s k
          _ -> k (IntVal 0)
    )
{-
For binary operators, we need to evaluate each of the arguments
sequentially, using a continuation that (eventually) evaluates the
operator on the two results of the computation. Note that this
translation fixes a left-to-right order of evaluation for binary
operators (instead of inheriting from Haskell's implicit control
structure.)  We could force operators to evaluate right-to-left by
changing how the evaluation works here.
-}

eval (Op o e1 e2) s k =
  eval e1 s $ \v1 ->
    eval e2 s $ \v2 ->
      k (evalB o v1 v2)
{-
Finally for function applications, we need to evaluate the `fun` and
`arg` components sequentially. Then, if the first argument is indeed a
function, we should apply it to the second using the current
continuation.  Remember that we want a call-by-value evaluation order
here, so we should evaluate the argument before passing it to the function.
-}

eval (App fun arg) s k =
  eval fun s $ \fv -> eval arg s $ \av ->
    case fv of
      FunVal f -> f av k
      _ -> k (IntVal 0)
{-
For `Let`, we'll restrict the right-hand side of a recursive
definitions to be functions. (This is actually the only thing that
makes sense in a call-by-value language.) If we do so, then the only
real change is to pass the continuation through to the evaluation of
the body of the `Let` expression.
-}

eval (Let x (Fun y e1body) e2) s k =
  let v = eval (Fun y e1body) s' id
      -- i.e., FunVal (\v' -> eval e1body (Map.insert y v' s'))
      s' = Map.insert x v s
   in eval e2 s' k
{-
If the RHS is not a function, we assume that this is not a recursive
definition. So we evaluate the RHS and then evaluate the body of the let
expression with the extended environment.
-}

eval (Let x e1 e2) s k =
  eval e1 s $ \v1 ->
    eval e2 (Map.insert x v1 s) k

{-
The only change that we need to give to the `repl` is to provide a
top-level continuation to get things started.  As usual, we use the
identity function for this.
-}

repl :: IO ()
repl = do
  putStr "%> "
  line <- getLine
  case parse line of
    Just exp -> do
      print (eval exp Map.empty id)
      repl
    Nothing -> putStrLn "what?!?" >> repl

parseAndEval :: String -> Maybe Value
parseAndEval s = fmap (\v -> eval v Map.empty id) (parse s)

{-
Here are some test cases from `FunEnv`:

We can define functions that are infinite loops when you call them.
Defining the function terminates.
-}

-- >>> parseAndEval "let LOOP = fun Y -> LOOP Y in LOOP"
-- Just <function>

{-
As in `FunEnv`, calling the function produces an infinite loop.
-}

-- >>> parseAndEval "let LOOP = fun Y -> LOOP Y in LOOP 1"
-- ProgressCancelledException

{-
However, this language has a call-by-value semantics. In FunEnv, we got the
result 2, because the `(fun Z -> 2)` doesn't need its argument. Here though,
that argument is an infinite loop.
-}

-- >>> parseAndEval "let LOOP = fun Y -> LOOP Y in (fun Z -> 2) (LOOP 3)"
-- ProgressCancelledException
{-

Why is CPS important?
---------------------

CPS can be used to give control to the writers of interpreters about
evaluation order. This is actually why CPS was invented by Plotkin
(1975) in the first-place: to allow the comparison of call-by-name
vs. call-by-value in the lambda-calculus. A function written in CPS
produces the same answer no matter whether it is evaluated using
call-by-name or call-by-value reduction.

Because it makes control explicit, CPS is a good intermediate
representation for compilers. CPS desugars function return, exceptions
and first-class continuations; function call turns into a single jump
instruction.

In other words, CPS does a lot of the heavy lifting in
compilation. For more information, see Andrew Appel's classic
textbook, "Compiling with Continuations".

More recently, CPS is the basis for the implementation of non-blocking
IO in single threaded languages and as the basis for distributing
programming.

* Simon Marlow's talk on the
      [The Haxl Project at Facebook](http://skillsmatter.com/podcast/home/simon-marlow)
      discusses its use for distributed computation.

* The [Async library](https://realworldocaml.org/beta3/en/html/concurrent-programming-with-async.html)
      developed by Jane Street, adds non-blocking IO to OCaml.

* The Python [Twisted](http://twistedmatrix.com/trac/) library

* [Node.js](http://nodejs.org) is an event-driven, non-blocking
       I/O model for JavaScript programming.

Acknowledgements
----------------

Parts of this lecture were inspired by Ch 7 of the excellent textbook,
"Essentials of Programming Languages", by Friedman, Wand, and Haynes.
-}
