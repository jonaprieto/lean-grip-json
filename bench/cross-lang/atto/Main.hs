-- Attoparsec JSON leaf-scalar counter benchmark (STRICT RFC-8259)
-- Counts: numbers, strings, true/false/null each = 1 leaf
-- Object keys are NOT counted (only values)
-- No DOM/tree built; count is accumulated directly as Int

{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified Data.Attoparsec.ByteString as A
import qualified Data.ByteString            as BS
import           System.Clock               (Clock(Monotonic), getTime, toNanoSecs)
import           Control.Exception          (evaluate)
import           Data.IORef
import           Data.List                  (sort)
import           System.Environment         (getArgs)
import           System.FilePath            (takeFileName)

-- | Skip ASCII whitespace: space, tab, newline, carriage-return
skipWS :: A.Parser ()
skipWS = A.skipWhile isWS
  where
    isWS w = w == 0x20 || w == 0x09 || w == 0x0A || w == 0x0D

-- | Parse a JSON value and return its leaf count
-- Numbers, strings, true/false/null = 1
-- Arrays/objects = sum of children (container adds 0)
jsonValue :: A.Parser Int
jsonValue = do
  skipWS
  w <- A.peekWord8'
  case w of
    0x22 -> jsonString   -- '"'
    0x7B -> jsonObject   -- '{'
    0x5B -> jsonArray    -- '['
    0x74 -> jsonTrue     -- 't'
    0x66 -> jsonFalse    -- 'f'
    0x6E -> jsonNull     -- 'n'
    _    -> jsonNumber   -- digit or '-'

-- | Strict string parser: bulk-scan safe runs, branch on '"' or '\', reject < 0x20
jsonString :: A.Parser Int
jsonString = do
  _ <- A.word8 0x22   -- opening '"'
  go
  where
    -- Bulk-skip bytes that are safe: >= 0x20, not '"' (0x22), not '\' (0x5C)
    go = do
      A.skipWhile isSafe          -- consume a run of safe bytes (may be empty)
      w <- A.anyWord8             -- must be '"', '\', or a control byte
      case w of
        0x22 -> return 1          -- closing '"', done
        0x5C -> do                -- backslash: validate escape
          esc <- A.anyWord8
          case esc of
            0x22 -> go            -- \"
            0x5C -> go            -- \\
            0x2F -> go            -- \/
            0x62 -> go            -- \b
            0x66 -> go            -- \f
            0x6E -> go            -- \n
            0x72 -> go            -- \r
            0x74 -> go            -- \t
            0x75 -> do            -- \uXXXX: exactly 4 hex digits
              _ <- A.satisfy isHex
              _ <- A.satisfy isHex
              _ <- A.satisfy isHex
              _ <- A.satisfy isHex
              go
            _    -> fail "invalid escape"
        _ -> fail "unescaped control character"  -- w < 0x20 (only remaining case)
    isSafe w = w >= 0x20 && w /= 0x22 && w /= 0x5C
    isHex b  = (b >= 0x30 && b <= 0x39)  -- 0-9
            || (b >= 0x41 && b <= 0x46)  -- A-F
            || (b >= 0x61 && b <= 0x66)  -- a-f

-- | Strict number parser per RFC 8259
-- -? (0 | [1-9][0-9]*) (.[0-9]+)? ([eE][+-]?[0-9]+)?
-- Rejects: 00, 1., 1e, +1, lone -
jsonNumber :: A.Parser Int
jsonNumber = do
  _ <- A.option 0x30 (A.word8 0x2D)  -- optional '-'
  -- integer part
  first <- A.anyWord8
  if first == 0x30
    then do
      -- leading zero: next char must NOT be a digit
      next <- A.peekWord8
      case next of
        Just d | d >= 0x30 && d <= 0x39 -> fail "leading zero in number"
        _ -> return ()
    else do
      if first >= 0x31 && first <= 0x39
        then A.skipWhile isDigit   -- [1-9][0-9]*
        else fail "expected digit in number"
  -- optional fractional part: '.' followed by at least one digit
  _ <- A.option () $ do
    _ <- A.word8 0x2E
    _ <- A.takeWhile1 isDigit
    return ()
  -- optional exponent: [eE][+-]?[0-9]+
  _ <- A.option () $ do
    _ <- A.satisfy (\x -> x == 0x65 || x == 0x45)
    _ <- A.option () (A.satisfy (\x -> x == 0x2B || x == 0x2D) >> return ())
    _ <- A.takeWhile1 isDigit
    return ()
  return 1
  where
    isDigit w = w >= 0x30 && w <= 0x39

-- | Parse "true" keyword
jsonTrue :: A.Parser Int
jsonTrue = A.string "true" >> return 1

-- | Parse "false" keyword
jsonFalse :: A.Parser Int
jsonFalse = A.string "false" >> return 1

-- | Parse "null" keyword
jsonNull :: A.Parser Int
jsonNull = A.string "null" >> return 1

-- | Parse a JSON array; return sum of element leaf counts
jsonArray :: A.Parser Int
jsonArray = do
  _ <- A.word8 0x5B       -- '['
  skipWS
  w <- A.peekWord8'
  if w == 0x5D
    then A.anyWord8 >> return 0   -- empty array ']'
    else do
      !first <- jsonValue
      !rest  <- accumulateCommaList 0
      skipWS
      _ <- A.word8 0x5D   -- ']'
      return (first + rest)

-- | Parse a JSON object; return sum of leaf counts of VALUES only
-- (object keys are strings but NOT counted)
jsonObject :: A.Parser Int
jsonObject = do
  _ <- A.word8 0x7B       -- '{'
  skipWS
  w <- A.peekWord8'
  if w == 0x7D
    then A.anyWord8 >> return 0   -- empty object '}'
    else do
      !first <- keyValue
      !rest  <- accumulateCommaKV 0
      skipWS
      _ <- A.word8 0x7D   -- '}'
      return (first + rest)

-- | Parse "key" : value and return the VALUE leaf count only
keyValue :: A.Parser Int
keyValue = do
  skipWS
  _ <- jsonString         -- consume key (count discarded)
  skipWS
  _ <- A.word8 0x3A       -- ':'
  !v <- jsonValue         -- parse value
  return v                -- do NOT add key's count

-- | After parsing first element of array, accumulate the rest
accumulateCommaList :: Int -> A.Parser Int
accumulateCommaList !acc = do
  skipWS
  w <- A.peekWord8'
  if w == 0x2C
    then do
      _ <- A.anyWord8     -- consume ','
      !v <- jsonValue
      accumulateCommaList (acc + v)
    else return acc

-- | After parsing first key-value of object, accumulate the rest
accumulateCommaKV :: Int -> A.Parser Int
accumulateCommaKV !acc = do
  skipWS
  w <- A.peekWord8'
  if w == 0x2C
    then do
      _ <- A.anyWord8     -- consume ','
      !v <- keyValue
      accumulateCommaKV (acc + v)
    else return acc

-- | Top-level: parse a complete JSON document
parseJSON :: BS.ByteString -> Either String Int
parseJSON bs =
  A.parseOnly (jsonValue <* skipWS <* A.endOfInput) bs

-- | Get monotonic time in nanoseconds
nowNS :: IO Integer
nowNS = toNanoSecs <$> getTime Monotonic

main :: IO ()
main = do
  args <- getArgs
  path <- case args of
    (p:_) -> return p
    []    -> error "Usage: atto-bench <path-to-json>"

  let basename = takeFileName path
  bs <- BS.readFile path  -- preload entire file into memory

  -- warm-up / correctness check
  n0 <- case parseJSON bs of
    Left err -> error $ "Parse error (warmup): " ++ err
    Right n  -> return n

  -- best-of-20 timing
  bsRef <- newIORef bs

  let doRun :: IO Integer
      doRun = do
        input <- readIORef bsRef
        t0 <- nowNS
        !n <- case A.parseOnly (jsonValue <* skipWS <* A.endOfInput) input of
                Left  err -> error $ "Parse error in run: " ++ err
                Right x   -> evaluate x
        _ <- evaluate n
        t1 <- nowNS
        return (t1 - t0)

  times <- mapM (\_ -> doRun) [1..20 :: Int]
  let sorted = sort times
  let bestMS = fromIntegral (head sorted) / 1.0e6 :: Double
  let medMS  = fromIntegral (sorted !! (length sorted `div` 2)) / 1.0e6 :: Double

  putStrLn $ "attoparsec " ++ basename
          ++ " count=" ++ show n0
          ++ " best_ms=" ++ show bestMS
          ++ " med_ms=" ++ show medMS
