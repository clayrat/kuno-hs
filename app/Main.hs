module Main (main) where

import System.Exit (exitWith, ExitCode(..), exitSuccess)
import Control.Monad (when, unless)
import System.Directory (doesFileExist, doesDirectoryExist)
import System.Timeout (timeout)
import Options.Applicative

import Kuno.TPTP
import Kuno.Parse
import Kuno.DialogueSearch

data Options = Options
  { optTimeout :: Int
  , optDepth   :: Int
  , optFile    :: FilePath
  }

optionsParser :: Parser Options
optionsParser = Options
  <$> option auto
        ( long "timeout"
       <> short 't'
       <> metavar "TIME"
       <> value 30
       <> help "Spend at most TIME seconds solving the problem (default: 30)" )
  <*> option auto
        ( long "depth"
       <> short 'd'
       <> metavar "DEPTH"
       <> value 30
       <> help "Consider winning strategies having depth at most DEPTH (default: 30)" )
  <*> argument str
        ( metavar "TPTP-FILE"
       <> help "Path to the TPTP problem file" )

optsInfo :: ParserInfo Options
optsInfo = info (optionsParser <**> helper)
  ( fullDesc
 <> progDesc "Kuno -- A theorem prover for intuitionistic logic based on dialogue games"
 <> header "kuno - intuitionistic theorem prover" )

resultToSZS :: SearchResult -> String
resultToSZS (Proved _) = "Theorem"
resultToSZS Refuted    = "CounterSatisfiable"
resultToSZS Cutoff     = "ResourceOut"

main :: IO ()
main = do
  opts <- execParser optsInfo
  let file = optFile opts
      timeoutSecs = optTimeout opts
      depth = optDepth opts

  -- Check file exists
  isDir <- doesDirectoryExist file
  when isDir $ do
    putStrLn $ "% SZS status InputError for " ++ file ++ " : Argument is a directory rather than a file."
    exitWith (ExitFailure 1)

  exists <- doesFileExist file
  unless exists $ do
    putStrLn $ "% SZS status InputError for " ++ file ++ " : File does not exist or is unreadable."
    exitWith (ExitFailure 1)

  -- Parse
  parseResult <- parseTPTPFile file
  case parseResult of
    Left _err -> do
      putStrLn $ "% SZS status SyntaxError for " ++ file ++ " : Unparsable TPTP file."
      exitWith (ExitFailure 1)

    Right db -> do
      -- Pre-checks: reject problems outside the prover's scope.
      -- Section 5 of Alama 2014 explains these limitations:
      -- - ⊥ (falsum) and ⊤ (verum) have no particle rules in the dialogue framework
      -- - Equality requires specialized rules not implemented here
      -- - A conjecture is required to serve as P's initial thesis
      if not (hasConjecture db) then do
        putStrLn $ "% SZS status Inappropriate for " ++ file ++ " : No conjecture formula."
        exitSuccess
      else if dbContainsContradiction db then do
        putStrLn $ "% SZS status Inappropriate for " ++ file ++ " : At least one occurrence of falsum was found."
        exitSuccess
      else if dbContainsVerum db then do
        putStrLn $ "% SZS status Inappropriate for " ++ file ++ " : At least one occurrence of verum was found."
        exitSuccess
      else if dbContainsEquation db then do
        putStrLn $ "% SZS status Inappropriate for " ++ file ++ " : At least one equation was found."
        exitSuccess
      else do
        -- Solve with timeout
        result <- timeout (timeoutSecs * 1000000) $
                    return $! intuitionisticallyValid (Right db) depth
        case result of
          Nothing -> do
            putStrLn $ "% SZS status Timeout for " ++ file
            exitSuccess
          Just searchResult -> do
            putStrLn $ "% SZS status " ++ resultToSZS searchResult ++ " for " ++ file
            exitSuccess

