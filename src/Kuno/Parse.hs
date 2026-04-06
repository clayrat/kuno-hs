module Kuno.Parse
  ( parseTPTP
  , parseTPTPFile
  ) where

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Void (Void)
import Data.Char (isAlphaNum, isUpper, isLower)
import Control.Monad (void)

import Kuno.Expression
import Kuno.TPTP

type Parser = Parsec Void String

-- Lexer helpers

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "%") empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

comma :: Parser String
comma = symbol ","

dot :: Parser String
dot = symbol "."

-- Careful operator parsers that don't match prefixes of longer operators
opEq :: Parser ()
opEq = lexeme $ try (char '=' >> notFollowedBy (char '>')) >> return ()

opNeq :: Parser ()
opNeq = void $ symbol "!="

opImplies :: Parser ()
opImplies = void $ symbol "=>"

opRevImplies :: Parser ()
opRevImplies = void $ try (string "<=" >> notFollowedBy (char '>'))  >> sc

opIff :: Parser ()
opIff = void $ symbol "<=>"

opXor :: Parser ()
opXor = void $ symbol "<~>"

opNand :: Parser ()
opNand = void $ symbol "~&"

opOr :: Parser ()
opOr = void $ symbol "|"

opAnd :: Parser ()
opAnd = void $ symbol "&"

opNot :: Parser ()
opNot = void $ symbol "~"

-- Word parsers

lowerWord :: Parser String
lowerWord = lexeme $ do
  c <- satisfy isLower
  rest <- many (satisfy (\x -> isAlphaNum x || x == '_'))
  return (c : rest)

upperWord :: Parser String
upperWord = lexeme $ do
  c <- satisfy isUpper
  rest <- many (satisfy (\x -> isAlphaNum x || x == '_'))
  return (c : rest)

singleQuoted :: Parser String
singleQuoted = lexeme $ do
  _ <- char '\''
  content <- many (satisfy (/= '\''))
  _ <- char '\''
  return content

integer :: Parser Int
integer = lexeme L.decimal

atomicWord :: Parser String
atomicWord = lowerWord <|> singleQuoted

-- TPTP file structure

tptpFile :: Parser TPTPDb
tptpFile = do
  sc
  formulas <- many tptpInput
  eof
  return $ TPTPDb formulas Nothing

tptpInput :: Parser TPTPFormula
tptpInput = try fofAnnotated <|> cnfAnnotated

fofAnnotated :: Parser TPTPFormula
fofAnnotated = do
  _ <- symbol "fof"
  _ <- symbol "("
  n <- name_
  _ <- comma
  r <- formulaRole
  _ <- comma
  f <- fofFormula
  _ <- optional (try (comma >> skipGeneralTerm >> optional (try (comma >> skipGeneralTerm))))
  _ <- symbol ")"
  _ <- dot
  return $ TPTPFormula n r f

cnfAnnotated :: Parser TPTPFormula
cnfAnnotated = do
  _ <- symbol "cnf"
  _ <- symbol "("
  n <- name_
  _ <- comma
  r <- formulaRole
  _ <- comma
  f <- cnfFormula
  _ <- optional (try (comma >> skipGeneralTerm >> optional (try (comma >> skipGeneralTerm))))
  _ <- symbol ")"
  _ <- dot
  return $ TPTPFormula n r f

name_ :: Parser String
name_ = atomicWord <|> (show <$> integer)

formulaRole :: Parser String
formulaRole = choice $ map (\r -> try (symbol r)) roles
  where
    roles = [ "axiom", "hypothesis", "definition", "assumption"
            , "lemma", "theorem", "conjecture", "negated_conjecture"
            , "plain", "fi_domain", "fi_functors", "fi_predicates"
            , "type", "unknown" ]

-- FOF formula parsing

fofFormula :: Parser Formula
fofFormula = fofLogicFormula

fofLogicFormula :: Parser Formula
fofLogicFormula = do
  left <- fofUnitaryFormula
  option left (fofBinaryRest left)

fofBinaryRest :: Formula -> Parser Formula
fofBinaryRest left =
      try (fofBinaryNonassoc left)
  <|> try (fofOrRest left)
  <|> fofAndRest left

fofBinaryNonassoc :: Formula -> Parser Formula
fofBinaryNonassoc left = do
  conn <- fofBinaryConnective
  right <- fofUnitaryFormula
  return $ conn left right

fofBinaryConnective :: Parser (Formula -> Formula -> Formula)
fofBinaryConnective =
      (try opIff >> return (Binary Equiv))
  <|> (try opXor >> return (Binary Nonequiv))
  <|> (try opImplies >> return (Binary Impl))
  <|> (try opRevImplies >> return (Binary RevImpl))
  <|> (try opNand >> return (\a b -> Negation (Binary And a b)))

fofOrRest :: Formula -> Parser Formula
fofOrRest left = do
  opOr
  right <- fofUnitaryFormula
  let disj = Binary Or left right
  option disj (fofOrRest disj)

fofAndRest :: Formula -> Parser Formula
fofAndRest left = do
  opAnd
  right <- fofUnitaryFormula
  let conj = Binary And left right
  option conj (fofAndRest conj)

fofUnitaryFormula :: Parser Formula
fofUnitaryFormula =
      parens fofLogicFormula
  <|> try fofQuantifiedFormula
  <|> fofUnaryFormula
  <|> try definedProp
  <|> try fofAtomicWithInfix
  <|> plainAtomicFormula

-- Parse atomic formula, then optionally check for infix = or !=
fofAtomicWithInfix :: Parser Formula
fofAtomicWithInfix = do
  left <- term_
  -- Check for = or !=
  (do opEq
      right <- term_
      return $ Equation left right)
    <|>
    (do opNeq
        right <- term_
        return $ Disequation left right)

fofQuantifiedFormula :: Parser Formula
fofQuantifiedFormula = do
  q <- folQuantifier
  vars <- brackets fofVariableList
  _ <- symbol ":"
  matrix <- fofUnitaryFormula
  return $ q vars matrix

folQuantifier :: Parser ([Term] -> Formula -> Formula)
folQuantifier =
      (try (symbol "!" >> notFollowedBy (char '=')) >> return UniversalQ)
  <|> (symbol "?" >> return ExistentialQ)

fofVariableList :: Parser [Term]
fofVariableList = variable `sepBy1` comma

variable :: Parser Term
variable = Variable <$> upperWord

fofUnaryFormula :: Parser Formula
fofUnaryFormula = do
  opNot
  f <- fofUnitaryFormula
  case f of
    Equation l r -> return (Disequation l r)
    _            -> return (Negation f)

-- Atomic formulas (plain: predicate with optional args)
plainAtomicFormula :: Parser Formula
plainAtomicFormula = do
  p <- atomicWord
  args <- option [] (parens (term_ `sepBy1` comma))
  return $ Atomic p args

definedProp :: Parser Formula
definedProp = do
  _ <- symbol "$"
  w <- lowerWord
  case w of
    "true"  -> return Verum
    "false" -> return Falsum
    _       -> fail $ "Unknown defined prop: $" ++ w

-- CNF formula

cnfFormula :: Parser Formula
cnfFormula = try (parens disjunction) <|> disjunction

disjunction :: Parser Formula
disjunction = do
  first <- literal
  rest <- many (opOr >> literal)
  return $ foldl (Binary Or) first rest

literal :: Parser Formula
literal =
      try (do opNot
              f <- cnfAtomicFormula
              case f of
                Equation l r -> return (Disequation l r)
                _            -> return (Negation f))
  <|> try cnfInfix
  <|> cnfAtomicFormula

cnfAtomicFormula :: Parser Formula
cnfAtomicFormula = plainAtomicFormula

cnfInfix :: Parser Formula
cnfInfix = do
  left <- term_
  (do opEq;  right <- term_; return $ Equation left right)
    <|>
    (do opNeq; right <- term_; return $ Disequation left right)

-- Terms

term_ :: Parser Term
term_ = try functionTerm <|> variable

functionTerm :: Parser Term
functionTerm = do
  f <- atomicWord
  args <- option [] (parens (term_ `sepBy1` comma))
  return $ FunTerm f args

-- General terms (for source/optional-info fields; skip them)
skipGeneralTerm :: Parser ()
skipGeneralTerm = skipGeneralData <|> skipGeneralList

skipGeneralData :: Parser ()
skipGeneralData =
      try (atomicWord >> optional (parens skipGeneralTermList) >> return ())
  <|> try (void variable)
  <|> try (void integer)
  <|> skipGeneralList

skipGeneralList :: Parser ()
skipGeneralList = void $ brackets (optional skipGeneralTermList)

skipGeneralTermList :: Parser ()
skipGeneralTermList = void $ skipGeneralTerm' `sepBy1` comma

skipGeneralTerm' :: Parser ()
skipGeneralTerm' = try skipGeneralData <|> skipGeneralList

-- Top-level parse functions

parseTPTP :: String -> Either String TPTPDb
parseTPTP input =
  case parse tptpFile "<input>" input of
    Left err -> Left (errorBundlePretty err)
    Right db -> Right db

parseTPTPFile :: FilePath -> IO (Either String TPTPDb)
parseTPTPFile path = do
  contents <- readFile path
  case parse tptpFile path contents of
    Left err -> return $ Left (errorBundlePretty err)
    Right db -> return $ Right (db { tptpPath = Just path })
