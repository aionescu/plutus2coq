{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections, LambdaCase, FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}

module HsToCoq.Edits.Lexer (
  -- * Lexer
  Lexer, runLexer, requestTactics, prettyParseError,
  -- ** Lexer state
  NewlineStatus(..),
  -- * Tokens
  Token(..), tokenDescription,
  token, token', proofBody,
  -- * Character categories
  isHSpace, isVSpace, isDigit, isWordInit, isWord, isOperator, isOpen, isClose,
  -- * Proofs
  ProofEnder(..), proof, proofEnderName,
  -- * Component parsers
  -- ** Types
  NameCategory(..),
  -- ** Identifiers
  qualid, qualified, unqualified,
  -- ** Whitespace and comments
  comment, space, newline,
  -- ** Atomic components
  nat, uword, word, op, unit, nil,
  -- ** Parse until a given string
  parseUntilAny,
) where

import Prelude hiding (Num())

import Data.Foldable
import Data.Function ((&))
import Data.Bifunctor (first, second, bimap)
import HsToCoq.Util.Foldable
import HsToCoq.Util.Functor
import Control.Applicative
import Control.Monad
import HsToCoq.Util.Monad
import Control.Monad.State
import Control.Monad.Parse
import Control.Monad.Activatable

import Data.Char
import HsToCoq.Util.Char
import HsToCoq.Util.Has

import Data.Text (Text)
import qualified Data.Text as T

import HsToCoq.Coq.Gallina

--------------------------------------------------------------------------------
-- Lexing-specific character categories
--------------------------------------------------------------------------------

isWordInit :: Char -> Bool
isWordInit c = isAlpha c || c == '_'

isWord :: Char -> Bool
isWord c = isAlphaNum c || c == '_' || c == '\'' || c == '#'
-- Note: a `'` can appear IN a word, but not at the beginning

isOperator :: Char -> Bool
isOperator c =
  c /= '_' && c /= '\'' &&
  generalCategory c `elem` [ ConnectorPunctuation, DashPunctuation, OtherPunctuation
                           , MathSymbol, CurrencySymbol, ModifierSymbol, OtherSymbol ]

isTick :: Char -> Bool
isTick c = c == '\''

--------------------------------------------------------------------------------
-- Tokens
--------------------------------------------------------------------------------
data ProofEnder = PEQed | PEDefined | PEAdmitted
                deriving (Eq, Ord, Enum, Bounded, Show, Read)

proofEnderName :: ProofEnder -> String
proofEnderName PEQed      = "Qed"
proofEnderName PEDefined  = "Defined"
proofEnderName PEAdmitted = "Admitted"

proof :: Tactics -> ProofEnder -> Proof
proof tactics PEQed      = ProofQed      tactics
proof tactics PEDefined  = ProofDefined  tactics
proof tactics PEAdmitted = ProofAdmitted tactics

data Token = TokWord    Ident
           | TokNat     Num
           | TokOp      Ident
           | TokTick
           | TokOpen    Char
           | TokClose   Char
           | TokString  Text
           | TokTactics Tactics
           | TokPfEnd   ProofEnder
           | TokNewline
           | TokEOF
           deriving (Eq, Ord, Show, Read)

tokenDescription :: Token -> String
tokenDescription (TokWord    w) = "word `"              ++ T.unpack       w ++ "'"
tokenDescription (TokNat     n) = "number `"            ++ show           n ++ "'"
tokenDescription (TokOp      o) = "operator `"          ++ T.unpack       o ++ "'"
tokenDescription TokTick        = "tick"
tokenDescription (TokOpen    o) = "opening delimeter `" ++ pure           o ++ "'"
tokenDescription (TokClose   c) = "closing delimeter `" ++ pure           c ++ "'"
tokenDescription (TokString  s) = "string literal `"    ++ T.unpack       s ++ "'"
tokenDescription (TokTactics t) = "tactics `"           ++ T.unpack       t ++ "'"
tokenDescription (TokPfEnd   e) = "proof ender `"       ++ proofEnderName e ++ "'"
tokenDescription TokNewline     = "newline"
tokenDescription TokEOF         = "end of file"

--------------------------------------------------------------------------------
-- Lexing
--------------------------------------------------------------------------------

-- Module-local
empty_brackets :: MonadParse m => Char -> Char -> m Text
empty_brackets open close = T.pack [open,close] <$ parseChar (== open)
                                                <* many (parseChar isSpace)
                                                <* parseChar (== close)

tuple_operator :: MonadParse m => m Text
tuple_operator = (\x y z -> T.pack $ [x] ++ y ++ [z]) <$>
                 parseChar (== '(') <*> many (parseChar (== ',')) <*> parseChar (== ')')


infix_datacon :: MonadParse m => m Text
infix_datacon = (\x y -> T.pack (x:y)) <$> parseChar (== ':') <*> some (parseChar isOperator)

-- Module-local
none :: Char -> Bool
none = const False

-- Module-local
is :: Eq a => a -> a -> Bool
is = (==)

data NameCategory = CatWord | CatSym
                  deriving (Eq, Ord, Enum, Bounded, Show, Read)

uword, word, op, tick, unit, nil :: MonadParse m => m Ident
uword = parseToken id isUpper    isWord
word  = parseToken id isWordInit isWord
op    = parseToken id isOperator isOperator
tick  = parseToken id isTick isTick
unit  = empty_brackets '(' ')'
nil   = empty_brackets '[' ']'

unqualified :: MonadParse m => m (NameCategory, Ident)
unqualified = asumFmap (CatWord,) [word] <|> asumFmap (CatSym,) [op,unit,nil,tuple_operator,infix_datacon]

qualified :: MonadParse m => m (NameCategory, Ident)
qualified = do
  root  <- uword
  _ <- parseChar (is '.')
  second ((root <> ".") <>) <$> qualid

qualid :: MonadParse m => m (NameCategory, Ident)
qualid = qualified <|> unqualified

comment, space, newline :: MonadParse m => m ()
comment = parseToken (const ()) (is '#') (not . isVSpace)
space   = parseToken (const ()) isHSpace isHSpace
newline = parseToken (const ()) isVSpace none

nat :: MonadParse m => m Num
nat = parseToken (read . T.unpack) isDigit isDigit

-- No escape sequences for now
stringLit :: MonadParse m => m Text
stringLit = parseChar (is '"') *> parseChars (not . is '"') <* parseChar (is '"')

parseUntilAny :: MonadParse m => [(Text, a)] -> m (Text, a)
parseUntilAny stops = do
  stopInit <- case T.transpose $ map fst stops of
                []      -> empty
                heads:_ -> pure $ \c -> T.any (is c) heads
  
  let parseCommand = T.foldr (\c -> (parseChar (is c) *>)) (pure ())
      
      terminator = asum [Left res <$ parseCommand stop | (stop, res) <- stops]
      char       = Right <$> parseChar stopInit

  fix $ \loop -> do
    text <- parseChars $ not . stopInit
    (terminator <|> char) >>= \case
      Left  res -> pure (text, res)
      Right c'  -> first ((text <> T.singleton c') <>) <$> loop

-- arguments from parseToken (from Control.Monad.Trans.Parse)
-- parseToken :: MonadParse m => (Text -> a)  -> (Char -> Bool) -> (Char -> Bool) -> m a
-- parseToken build isFirst isRest = ...

data NewlineStatus = NewlineSeparators | NewlineWhitespace
                   deriving (Eq, Ord, Enum, Bounded, Show, Read)

type MonadNewlineStatus s m = (MonadParse m, MonadState s m, Has s NewlineStatus)

token' :: MonadNewlineStatus s m => m (Maybe Token)
token' = asum $
  [ Nothing          <$  comment
  , Nothing          <$  space
  , newlineToken     <*  newline
  , Just TokTick     <$  tick
  , Just . TokString <$> stringLit
  , Just . TokNat    <$> nat
  , Just . TokOpen   <$> parseChar isOpen
  , Just . TokClose  <$> parseChar isClose
  , Just . nameToken <$> qualid
  , Just TokEOF      <$  (guard =<< atEOF) ]
  where
    newlineToken = getPart <&> \case
                     NewlineSeparators -> Just TokNewline
                     NewlineWhitespace -> Nothing
    nameToken    = uncurry $ \case
                     CatWord -> TokWord
                     CatSym  -> TokOp

token :: (MonadActivatable Token m, MonadNewlineStatus s m) => m Token
token = switching' (untilJustM token') (bimap TokTactics TokPfEnd <$> proofBody)

proofBody :: MonadParse m => m (Tactics, ProofEnder)
proofBody = do
  parseUntilAny [ ("Qed",      PEQed)
                , ("Defined",  PEDefined)
                , ("Admitted", PEAdmitted) ]

requestTactics :: (MonadActivatable Token m, MonadParse m) => m ()
requestTactics = activateWith $ \case
  DoubleActivation -> parseError "already about to parse tactics"
  EarlyActivation  -> parseError "can't parse tactics again immediately after parsing tactics"

type Lexer s = ActivatableT Token (StateT (NewlineStatus :* s) Parse)

evalParserState :: Monad m => StateT (NewlineStatus :* s) m a -> s -> m a
evalParserState u s = evalStateT u (NewlineSeparators :* s)

runLexer :: Lexer s a -> s -> Text -> Either [ParseError] a
runLexer act s t = act
  & finalizeActivatableT (\_ -> parseError "trailing post-tactics keyword not parsed")
  & (`evalParserState` s)
  & (`evalParse` t)
