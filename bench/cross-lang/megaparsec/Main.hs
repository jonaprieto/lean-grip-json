-- Megaparsec JSON leaf-scalar counter benchmark (STRICT RFC-8259)
-- Counts: numbers, strings, true/false/null each = 1 leaf
-- Object keys are NOT counted (only values)
-- No DOM/tree built; count is accumulated directly as Int

{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Main where

import           Control.Exception          (evaluate)
import           Data.ByteString            (ByteString)
import qualified Data.ByteString            as BS
import           Data.IORef
import           Data.List                  (sort)
import           Data.Void                  (Void)
import           Data.Word                  (Word8)
import           System.Clock               (Clock (Monotonic), getTime, toNanoSecs)
import           System.Environment         (getArgs)
import           System.FilePath            (takeFileName)
import           Text.Megaparsec
import           Text.Megaparsec.Byte

-- Parser type: Megaparsec over strict ByteString, no custom error component
type Parser = Parsec Void ByteString

-- | Skip JSON whitespace: space, tab, CR, LF
skipWS :: Parser ()
skipWS = skipMany (satisfy isWS)
  where
    isWS w = w == 0x20 || w == 0x09 || w == 0x0A || w == 0x0D

-- | Parse a JSON value and return its leaf count
jsonValue :: Parser Int
jsonValue = do
  skipWS
  w <- lookAhead anySingle
  case w of
    0x22 -> jsonString   -- '"'
    0x7B -> jsonObject   -- '{'
    0x5B -> jsonArray    -- '['
    0x74 -> jsonTrue     -- 't'
    0x66 -> jsonFalse    -- 'f'
    0x6E -> jsonNull     -- 'n'
    _    -> jsonNumber   -- digit or '-'

-- | Strict string parser: bulk-scan safe runs, branch on '"' or '\', reject < 0x20
jsonString :: Parser Int
jsonString = do
  _ <- single 0x22   -- opening '"'
  go
  where
    go :: Parser Int
    go = do
      -- Bulk-skip bytes that are safe: >= 0x20, not '"' (0x22), not '\' (0x5C)
      _ <- takeWhileP (Just "safe string byte") isSafe
      w <- anySingle    -- must be '"', '\', or a control byte
      case w of
        0x22 -> return 1       -- closing '"'
        0x5C -> do             -- backslash: validate escape
          esc <- anySingle
          case esc of
            0x22 -> go   -- \"
            0x5C -> go   -- \\
            0x2F -> go   -- \/
            0x62 -> go   -- \b
            0x66 -> go   -- \f
            0x6E -> go   -- \n
            0x72 -> go   -- \r
            0x74 -> go   -- \t
            0x75 -> do   -- \uXXXX: exactly 4 hex digits
              _ <- satisfy isHex
              _ <- satisfy isHex
              _ <- satisfy isHex
              _ <- satisfy isHex
              go
            _    -> fail "invalid escape sequence"
        _ -> fail "unescaped control character"  -- w < 0x20 (only remaining case)
    isSafe :: Word8 -> Bool
    isSafe w = w >= 0x20 && w /= 0x22 && w /= 0x5C
    isHex :: Word8 -> Bool
    isHex b = (b >= 0x30 && b <= 0x39)
           || (b >= 0x41 && b <= 0x46)
           || (b >= 0x61 && b <= 0x66)

-- | Strict number parser per RFC 8259
-- -? (0 | [1-9][0-9]*) (.[0-9]+)? ([eE][+-]?[0-9]+)?
jsonNumber :: Parser Int
jsonNumber = do
  _ <- optional (single 0x2D)  -- optional '-'
  first <- anySingle
  if first == 0x30
    then do
      -- leading zero: next char must NOT be a digit
      mnext <- optional (lookAhead anySingle)
      case mnext of
        Just d | d >= 0x30 && d <= 0x39 -> fail "leading zero in number"
        _ -> return ()
    else do
      if first >= 0x31 && first <= 0x39
        then skipMany (satisfy isDigit)
        else fail "expected digit in number"
  -- optional fractional part
  _ <- optional $ do
    _ <- single 0x2E   -- '.'
    _ <- takeWhile1P (Just "digit") isDigit
    return ()
  -- optional exponent
  _ <- optional $ do
    _ <- satisfy (\x -> x == 0x65 || x == 0x45)   -- 'e' or 'E'
    _ <- optional (satisfy (\x -> x == 0x2B || x == 0x2D))
    _ <- takeWhile1P (Just "digit") isDigit
    return ()
  return 1
  where
    isDigit w = w >= 0x30 && w <= 0x39

-- | Parse "true"
jsonTrue :: Parser Int
jsonTrue = string "true" >> return 1

-- | Parse "false"
jsonFalse :: Parser Int
jsonFalse = string "false" >> return 1

-- | Parse "null"
jsonNull :: Parser Int
jsonNull = string "null" >> return 1

-- | Parse a JSON array; return sum of element leaf counts
jsonArray :: Parser Int
jsonArray = do
  _ <- single 0x5B       -- '['
  skipWS
  w <- lookAhead anySingle
  if w == 0x5D
    then anySingle >> return 0   -- empty array
    else do
      !first <- jsonValue
      !rest  <- accumulateCommaList 0
      skipWS
      _ <- single 0x5D   -- ']'
      return (first + rest)

-- | Parse a JSON object; return sum of leaf counts of VALUES only
jsonObject :: Parser Int
jsonObject = do
  _ <- single 0x7B       -- '{'
  skipWS
  w <- lookAhead anySingle
  if w == 0x7D
    then anySingle >> return 0   -- empty object
    else do
      !first <- keyValue
      !rest  <- accumulateCommaKV 0
      skipWS
      _ <- single 0x7D   -- '}'
      return (first + rest)

-- | Parse "key" : value; return VALUE leaf count only (key not counted)
keyValue :: Parser Int
keyValue = do
  skipWS
  _ <- jsonString      -- consume key, discard count
  skipWS
  _ <- single 0x3A    -- ':'
  jsonValue

-- | After first array element, accumulate remaining comma-separated elements
accumulateCommaList :: Int -> Parser Int
accumulateCommaList !acc = do
  skipWS
  w <- lookAhead anySingle
  if w == 0x2C
    then do
      _ <- anySingle   -- consume ','
      !v <- jsonValue
      accumulateCommaList (acc + v)
    else return acc

-- | After first object member, accumulate remaining comma-separated members
accumulateCommaKV :: Int -> Parser Int
accumulateCommaKV !acc = do
  skipWS
  w <- lookAhead anySingle
  if w == 0x2C
    then do
      _ <- anySingle   -- consume ','
      !v <- keyValue
      accumulateCommaKV (acc + v)
    else return acc

-- | Top-level: parse a complete JSON document
parseJSON :: ByteString -> Either String Int
parseJSON bs =
  case runParser (jsonValue <* skipWS <* eof) "" bs of
    Left  err -> Left (errorBundlePretty err)
    Right n   -> Right n

-- | Get monotonic time in nanoseconds
nowNS :: IO Integer
nowNS = toNanoSecs <$> getTime Monotonic

main :: IO ()
main = do
  args <- getArgs
  path <- case args of
    (p:_) -> return p
    []    -> error "Usage: megaparsec-bench <path-to-json>"

  let basename = takeFileName path
  bs <- BS.readFile path  -- preload entire file

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
        !n <- case parseJSON input of
                Left  err -> error $ "Parse error in run: " ++ err
                Right x   -> evaluate x
        _ <- evaluate n
        t1 <- nowNS
        return (t1 - t0)

  times <- mapM (\_ -> doRun) [1..20 :: Int]
  let sorted = sort times
  let bestMS = fromIntegral (head sorted) / 1.0e6 :: Double
  let medMS  = fromIntegral (sorted !! (length sorted `div` 2)) / 1.0e6 :: Double

  putStrLn $ "megaparsec " ++ basename
          ++ " count=" ++ show n0
          ++ " best_ms=" ++ show bestMS
          ++ " med_ms=" ++ show medMS
