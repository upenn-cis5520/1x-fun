{-
The abstract and concrete syntax of FUN, a small functional
programming language.

-}

module FunSyntax where

import Control.Applicative (Alternative (..))
import qualified Data.Char as Char
import ParserCombinators (Parser)
import qualified ParserCombinators as Parser
import Test.QuickCheck hiding (Fun)
import Text.PrettyPrint (Doc, ($$), (<+>), (<>))
import qualified Text.PrettyPrint as PP

{-
The syntax of the language is a little like that of the Lu programming
language from your homework assignment.
-}

type Variable = String

data Bop
  = -- | +  :: Int  -> Int  -> Int
    Plus
  | -- | -  :: Int  -> Int  -> Int
    Minus
  | -- | *  :: Int  -> Int  -> Int
    Times
  | -- | >  :: Int -> Int -> Bool
    Gt
  | -- | >= :: Int -> Int -> Bool
    Ge
  | -- | <  :: Int -> Int -> Bool
    Lt
  | -- | <= :: Int -> Int -> Bool
    Le
  deriving (Eq, Show, Enum)

{-
Like Haskell (and OCaml), this language does not
distinguish between expressions and statements: everything is an
expression. For that reason, we add 'If' as a new expression form to
the expressions that we already had in Lu (variables, constants and
binary operators).
-}

data Expression
  = -- familiar core expression language
    Var Variable -- uppercase strings 'X'
  | IntExp Int -- natural numbers   '0' ..
  | BoolExp Bool -- 'true' or 'false'
  | Op Bop Expression Expression -- infix binary operators 'e1 + e2'
  -- new stuff...
  | If Expression Expression Expression -- if expressions, 'if X then Y else Z'
  -- interesting new stuff...
  | Fun Variable Expression -- anonymous function,   'fun X -> e'
  | App Expression Expression -- function application, 'e1 e2'
  | Let Variable Expression Expression -- (recursive) binding,  'let F = e in e'
  deriving (Show, Eq)

{-
The "fun" stuff is in the last three lines. We want to be able to
create (anonymous) first-class functions, apply them to arguments, and
use them in recursive definitions. For example, our good friend the
factorial function might be written in the concrete syntax of FUN as:

      let FACT = fun X ->
                  if X <= 1 then 1 else X * FACT (X - 1)
      in FACT 5

and represented in the abstract syntax as:
-}

factExp :: Expression
factExp =
  Let
    "FACT"
    ( Fun
        "X"
        ( If
            (Op Le (Var "X") (IntExp 1))
            (IntExp 1)
            (Op Times (Var "X") (App (Var "FACT") (Op Minus (Var "X") (IntExp 1))))
        )
    )
    (App (Var "FACT") (IntExp 5))

{-
FUN Parser
----------

The rest of this file is a parser and pretty printer for the FUN
language. This code depends on the parsing library that we developed in class.
-}

-- parse something then consume all following whitespace
wsP :: Parser a -> Parser a
wsP p = p <* many (Parser.satisfy Char.isSpace)

-- a parser that looks for a particular string, then consumes all
-- whitespace afterwards.
kwP :: String -> Parser String
kwP s = wsP $ Parser.string s

varP :: Parser Variable
varP = wsP (some (Parser.satisfy Char.isUpper))

boolP :: Parser Bool
boolP =
  kwP "true" *> pure True
    <|> kwP "false" *> pure False

intP :: Parser Int
intP = Parser.int

opP :: Parser Bop
opP =
  kwP "+" *> pure Plus
    <|> kwP "-" *> pure Minus
    <|> kwP "*" *> pure Times
    <|> kwP ">=" *> pure Ge
    <|> kwP "<=" *> pure Le
    <|> kwP ">" *> pure Gt
    <|> kwP "<" *> pure Lt

varExprP = Var <$> wsP varP

boolExprP = BoolExp <$> wsP boolP

intExprP = IntExp <$> wsP intP

ifP =
  If
    <$> (kwP "if" *> exprP)
    <*> (kwP "then" *> exprP)
    <*> (kwP "else" *> exprP)

funP =
  Fun
    <$> (kwP "fun" *> varP)
    <*> (kwP "->" *> exprP)

letrecP =
  Let
    <$> (kwP "let" *> varP)
    <*> (kwP "=" *> exprP)
    <*> (kwP "in" *> exprP)

-- we use chainl1 for associativity and precedence
exprP :: Parser Expression
exprP = sumP
  where
    sumP = prodP `Parser.chainl1` (Op <$> addOp)
    prodP = compP `Parser.chainl1` (Op <$> mulOp)
    compP = appP `Parser.chainl1` (Op <$> cmpOp)
    appP = factorP `Parser.chainl1` wsP (pure App)
    factorP = wsP (Parser.between (Parser.char '(') exprP (Parser.char ')')) <|> baseP
    baseP =
      boolExprP <|> intExprP <|> ifP <|> funP <|> letrecP
        <|> varExprP

addOp :: Parser Bop
addOp =
  kwP "+" *> pure Plus
    <|> kwP "-" *> pure Minus

mulOp :: Parser Bop
mulOp = kwP "*" *> pure Times

cmpOp :: Parser Bop
cmpOp =
  kwP "<=" *> pure Le
    <|> kwP ">=" *> pure Ge
    <|> kwP "<" *> pure Lt
    <|> kwP ">" *> pure Gt

parse :: String -> Maybe Expression
parse s = case Parser.doParse exprP s of
  Just (exp, _) -> Just exp
  _ -> Nothing

{-
FUN Printer
------------
-}

instance PP Bop where
  pp Plus = PP.text "+"
  pp Minus = PP.text "-"
  pp Times = PP.text "*"
  pp Gt = PP.text ">"
  pp Ge = PP.text ">="
  pp Lt = PP.text "<"
  pp Le = PP.text "<="

class PP a where
  pp :: a -> Doc

display :: PP a => a -> String
display = show . pp

instance PP Variable where
  pp = PP.text

instance PP Expression where
  pp (Var x) = PP.text x
  pp (IntExp x) = PP.text (show x)
  pp (BoolExp x) = if x then PP.text "true" else PP.text "false"
  pp e@(Op _ _ _) = ppPrec 0 e
  pp (If e s1 s2) =
    PP.vcat
      [ PP.text "if" <+> pp e <+> PP.text "then",
        PP.nest 2 (pp s1),
        PP.text "else",
        PP.nest 2 (pp s2)
      ]
  pp e@(App _ _) = ppPrec 0 e
  pp (Fun x e) =
    PP.hang (PP.text "fun" <+> pp x <+> PP.text "->") 2 (pp e)
  pp (Let x e1 e2) =
    PP.vcat
      [ PP.text "let" <+> pp x <+> PP.text "=",
        PP.nest 2 (pp e1),
        PP.text "in",
        PP.nest 2 (pp e2)
      ]

ppPrec n (Op bop e1 e2) =
  parens (level bop < n) $
    ppPrec (level bop) e1 <+> pp bop <+> ppPrec (level bop + 1) e2
ppPrec n (App e1 e2) =
  parens (levelApp < n) $
    ppPrec levelApp e1 <+> ppPrec (levelApp + 1) e2
ppPrec n e@(Fun _ _) =
  parens (levelFun < n) $ pp e
ppPrec n e@(If {}) =
  parens (levelIf < n) $ pp e
ppPrec n e@(Let {}) =
  parens (levelLet < n) $ pp e
ppPrec _ e' = pp e'

parens b = if b then PP.parens else id

-- emulate the C++ precendence-level table
level :: Bop -> Int
level Plus = 3
level Minus = 3
level Times = 5
level _ = 8

levelApp :: Int
levelApp = 10

levelIf :: Int
levelIf = 2

levelLet :: Int
levelLet = 1

levelFun :: Int
levelFun = 1 -- (= almost always needs parens)

{-
Roundtrip Property
------------------

In the terminal, you can test the correctness of the parser/pretty printer
using the following rountrip property.

    ghci> quickCheckN 1000 prop_roundtrip
-}

indented :: PP a => a -> String
indented = PP.render . pp

prop_roundtrip :: Expression -> Bool
prop_roundtrip s = parse (indented s) == Just s

quickCheckN :: Test.QuickCheck.Testable prop => Int -> prop -> IO ()
quickCheckN n = quickCheckWith $ stdArgs {maxSuccess = n, maxSize = 500}

instance Arbitrary Expression where
  arbitrary = sized genExp

  shrink (Op o e1 e2) = [Op o e1' e2' | e1' <- shrink e1, e2' <- shrink e2]
  shrink (If e1 e2 e3) = [If e1' e2' e3' | e1' <- shrink e1, e2' <- shrink e2, e3' <- shrink e3]
  shrink (Fun v e1) = [Fun v e1' | e1' <- shrink e1]
  shrink (App e1 e2) = [App e1' e2' | e1' <- shrink e1, e2' <- shrink e2]
  shrink (Let v e1 e2) = [Let v e1' e2' | e1' <- shrink e1, e2' <- shrink e2]
  shrink _ = []

genExp :: Int -> Gen Expression
genExp 0 =
  oneof
    [ Var <$> arbVar,
      IntExp <$> arbitrary,
      BoolExp <$> arbitrary
    ]
genExp n =
  frequency
    [ (1, Var <$> arbVar),
      (1, IntExp <$> arbNat),
      (1, BoolExp <$> arbitrary),
      (7, Op <$> arbitrary <*> genExp n' <*> genExp n'),
      (7, If <$> genExp n' <*> genExp n' <*> genExp n'),
      (7, Fun <$> arbVar <*> genExp n'),
      (7, App <$> genExp n' <*> genExp n'),
      (7, Let <$> arbVar <*> genExp n' <*> genExp n')
    ]
  where
    n' = n `div` 2

instance Arbitrary Bop where
  arbitrary = elements [Plus ..]

arbNat :: Gen Int
arbNat = abs <$> arbitrary

arbVar :: Gen Variable
arbVar = elements $ map pure ['A' .. 'Z']
