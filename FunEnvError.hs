{-
FunEnvError
===========

Let's revise the environment based interpreter
`FunEnv` so that it
can return error messages when things go wrong instead of producing junk
values.

-}

module FunEnvError where

import Control.Monad.Except (MonadError (throwError))
import Data.Map (Map)
import qualified Data.Map as Map
import FunSyntax
  ( Bop (..),
    Expression (..),
    Variable,
    factExp,
    parse,
  )
import Test.HUnit

{-
The big change is that our evaluation function may sometimes fail, for example
if we try to evaluate "2 + true" or "X + 1".

So we will give the evaluator this type, where if there is a runtime error, we can return
a string describing that error.

     eval :: Expression -> Environment -> Either String Value

We'll give a name to the type that is returned by the evaluator:
-}

type EvalResult = Either String Value

{-
And use this type in the definition of the environment
-}

type Environment = Map Variable EvalResult

{-
And in the type of function values. Below, we need the arguments to
functions to be lazily evaluated, so we use the evaluator type. We also
need to let function values also produce errors when they are evaluated.
-}

data Value
  = IntVal Int
  | BoolVal Bool
  | -- note! functions can trigger errors when they are applied
    FunVal (EvalResult -> EvalResult)

instance Show Value where
  show (IntVal i) = show i
  show (BoolVal b) = show b
  show (FunVal _) = "<function>" -- can't show functions

{-
Now let's look at the function for evaluating binary operators.  Most of the
cases just return the appropriate value. However, the last case uses the
`throwError` function to report the problem.
-}

evalB :: Bop -> Value -> Value -> EvalResult
evalB Plus (IntVal i1) (IntVal i2) = return $ IntVal (i1 + i2)
evalB Minus (IntVal i1) (IntVal i2) = return $ IntVal (i1 - i2)
evalB Times (IntVal i1) (IntVal i2) = return $ IntVal (i1 * i2)
evalB Gt (IntVal i1) (IntVal i2) = return $ BoolVal (i1 > i2)
evalB Ge (IntVal i1) (IntVal i2) = return $ BoolVal (i1 >= i2)
evalB Lt (IntVal i1) (IntVal i2) = return $ BoolVal (i1 < i2)
evalB Le (IntVal i1) (IntVal i2) = return $ BoolVal (i1 <= i2)
evalB _ _ _ = throwError "Invalid argument to binary operator"

{-
We can use `throwError` because `Either String` is an instance of the class
`MonadError String`, i.e. the class of monads that can report errors using
strings.

Furthermore, we can throw an error if there is no value for a variable
available in the environment.
-}

tLookup :: Variable -> Environment -> EvalResult
tLookup x env =
  case Map.lookup x env of
    Just ty -> ty
    Nothing -> throwError $ "Unbound variable " ++ x

{-
Now it is your turn: complete the following cases of the environment based
interpreter.  You can use the repl or the test cases below for testing.
-}

eval :: Expression -> Environment -> EvalResult
eval (Var x) s = tLookup x s
eval (IntExp i) s = return $ IntVal i
eval (BoolExp i) s = return $ BoolVal i
eval (Op o e1 e2) s = do
  v1 <- eval e1 s
  v2 <- eval e2 s
  evalB o v1 v2
eval (If e1 e2 e3) s = do
  v1 <- eval e1 s
  case v1 of
    BoolVal b -> if b then eval e2 s else eval e3 s
    _ -> throwError "if requires a boolean"
eval (Fun x e) s = return $ FunVal (\v -> eval e (Map.insert x v s))
eval (App fun arg) s = do
  v1 <- eval fun s
  case v1 of
    FunVal g -> g (eval arg s)
    _ -> throwError "app requires a function"
eval (Let x e1 e2) s =
  let s' = Map.insert x (eval e1 s') s
   in eval e2 s'

-- Testing code

isErr :: EvalResult -> Test
isErr (Left _) = TestCase $ assert True
isErr (Right _) = TestCase $ assert False

isIntVal :: Int -> EvalResult -> Test
isIntVal y (Right (IntVal x)) = TestCase $ assert (x == y)
isIntVal y _ = TestCase $ assert False

tests :: Test
tests =
  TestList
    [ "1 + true" ~: isErr $ eval (Op Plus (IntExp 1) (BoolExp True)) Map.empty,
      "1 1" ~: isErr $ eval (App (IntExp 1) (IntExp 1)) Map.empty,
      "if 1 .." ~: isErr $ eval (If (IntExp 1) (IntExp 2) (IntExp 3)) Map.empty,
      "X" ~: isErr $ eval (Var "X") Map.empty,
      "FACT 6" ~: isIntVal 120 $ eval factExp Map.empty
    ]

-- >>> runTestTT tests
-- Counts {cases = 5, tried = 5, errors = 0, failures = 0}

{-
This test demonstrates that our language uses call-by-need evaluation. Even though
the argument is an infinite loop, it is never evaluated.
-}

parseAndEval :: String -> Maybe EvalResult
parseAndEval s = fmap (`eval` Map.empty) (parse s)

-- >>> parseAndEval "let LOOP = fun Y -> LOOP Y in (fun Z -> 2) (LOOP 3)"
-- Just (Right 2)

replE :: IO ()
replE = do
  putStr "%> "
  line <- getLine
  case parse line of
    Just exp ->
      case eval exp Map.empty of
        Left str -> putStrLn str >> replE
        Right val -> print val >> replE
    Nothing -> putStrLn "what?!?" >> replE
