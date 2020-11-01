module AMR2FOL where

import Data.List
import Text.Regex.PCRE

-- constants and variables are strings
type Constant = String
type Variable = String
-- properties are functions from constants/variables to formulas
type Property = String -> Formula Variable
-- roles are strings
type Role     = String
-- continuation (phi, lambda-expression for role)
type Cont     = String -> Formula Variable
-- list of (text, type) tokens
type Tokens   = [(String, String)]
-- list of out-going (role, UMR) edges
type Edges    = [(Role, UMR)]

        -- constants are UMRs
data UMR = C Constant
        -- variables are UMRs
         | X Variable
        -- instance assignments (possibly with out-going roles) are UMRs
         | A Variable Property Edges
        -- projection phenomena are UMRs
         | P Variable Property Edges

instance Show UMR where
    show (C c)         = intercalate " " ["C", show c]
    show (X x)         = intercalate " " ["X", show x]
    show (A x p edges) = intercalate " " ["A", show x, (\ (Atom q y) -> show q)
                                          (p x), show edges]
    show (P x p edges) = intercalate " " ["P", show x, (\ (Atom q y) -> show q)
                                          (p x), show edges]

-- see van Eijck and Unger, FSynF.hs
data Formula a = Atom  String [a]
               | Neg  (Formula a)
               | Conj [Formula a]
               | Exists Variable (Formula a)
               | Top
               deriving (Eq)

instance (Show a, Eq a) => Show (Formula a) where
    show (Atom p xs)    =  show p ++ " " ++ show xs
    show (Neg  phi)     =  "Not (" ++ show phi ++ ")"
    show (Conj phis) = intercalate " And " [show phi | phi <- phis, phi /= Top]
    show (Exists x phi) =  "Exists " ++ show x ++ " (" ++ show phi ++ ")"
    show (Top)          =  "Top"

-- main function
process :: String -> Formula Variable
process s = umr2fol (str2umr s) (\ _ -> Top)

-- turn string into structured UMR
str2umr :: String -> UMR
str2umr s = snd . tok2nod $ str2tok s

-- regular expressions for parsing UMRs
-- based on https://github.com/goodmami/penman
string = "\\\"[^\\\"]*(?:\\\\.[^\\\"]*)*\\\""
role   = ":[^\\s()\\/:~]*"
symbol =  "[^\\s()\\/:~]+"
lparen = "\\("
rparen = "\\)"
slash  = "\\/"
-- bslash for projection phenomena
bslash = "\\\\"

penman_re = ("(" ++ intercalate ")|(" [string, lparen,
             rparen, slash, bslash, role, symbol] ++ ")")

-- turn string into list of (text, type) tokens
-- roughly corresponds to penman._lexer._lex
str2tok :: String -> Tokens
str2tok s | not $ null text = (text, typ) : str2tok t
          | otherwise       = []
          where (_, text, t, patterns)
                    = s =~ penman_re :: (String, String, String, [String])
                typ | not . null $ patterns !! 0 = "string"
                    | not . null $ patterns !! 1 = "lparen"
                    | not . null $ patterns !! 2 = "rparen"
                    | not . null $ patterns !! 3 = "slash"
                    | not . null $ patterns !! 4 = "bslash"
                    | not . null $ patterns !! 5 = "role"
                    | not . null $ patterns !! 6 = "symbol"
                    | otherwise = error "Tokenization error: str2tok" -- fail

-- parse a penman node from tokens
-- roughly corresponds to penman._parse._parse_node
-- tok2nod :: starting tokens -> (remaining tokens, node)
tok2nod :: Tokens -> (Tokens, UMR)
tok2nod ((_, "lparen") : (v, "symbol") : (_, "slash" ) : (p, "symbol") : t)
          = (tokens, A v (\ x -> Atom p [x]) edges)
          where (tokens, edges) = tok2edg (t, [])
tok2nod ((_, "lparen") : (v, "symbol") : (_, "slash" ) : (p, "string") : t)
          = (tokens, A v (\ x -> Atom p [x]) edges)
          where (tokens, edges) = tok2edg (t, [])
-- for robustness, don't assume next token is the concept
tok2nod ((_, "lparen") : (v, "symbol") : (_, "slash" ) : t)
          = (tokens, A v (\ x -> Atom "none" [x]) edges)
          where (tokens, edges) = tok2edg (t, [])
-- bslash for projection phenomena
tok2nod ((_, "lparen") : (v, "symbol") : (_, "bslash") : (p, "symbol") : t)
          = (tokens, P v (\ x -> Atom p [x]) edges)
          where (tokens, edges) = tok2edg (t, [])
tok2nod ((_, "lparen") : (v, "symbol") : (_, "bslash") : (p, "string") : t)
          = (tokens, P v (\ x -> Atom p [x]) edges)
          where (tokens, edges) = tok2edg (t, [])
-- for robustness, don't assume next token is the concept
tok2nod ((_, "lparen") : (v, "symbol") : (_, "bslash") : t)
          = (tokens, P v (\ x -> Atom "none" [x]) edges)
          where (tokens, edges) = tok2edg (t, [])
tok2nod ((_, "lparen") : (v, "symbol") : t)
          = (tokens, A v (\ x -> Atom "none" [x]) edges)
          where (tokens, edges) = tok2edg (t, [])
tok2nod _ = error "Parsing error: tok2nod" -- fail

-- parse a penman edge from tokens
-- roughly corresponds to penman._parse._parse_edge
-- tok2edg :: (starting  tokens, initial edges) ->
--            (remaining tokens, updated edges)
tok2edg :: (Tokens, Edges) -> (Tokens, Edges)
tok2edg ((r, "role") : (c, "string") : t, edges)
          = tok2edg (t, edges ++ [(tail r, C c)])
tok2edg ((r, "role") : (v, "symbol") : t, edges)
          = tok2edg (t, edges ++ [(tail r, X v)])
tok2edg ((r, "role") : (l, "lparen") : t, edges)
          = tok2edg (tokens, edges ++ [(tail r, node)])
          where (tokens, node) = tok2nod ((l, "lparen") : t)
-- for robustness in parsing, allow edges with no target
tok2edg ((r, "role") : (p, "rparen") : t, edges)
          = tok2edg ((p, "rparen") : t, edges ++ [(tail r, C "none")])
tok2edg ((r, "role") : (o,  "role" ) : t, edges)
          = tok2edg ((o,  "role" ) : t, edges ++ [(tail r, C "none")])
tok2edg ((_, "rparen") : t, edges)
          = (t, edges) -- base case
tok2edg _ = error "Parsing error: tok2edg" -- fail

-- turn structured UMR into formula using continuations
umr2fol :: UMR -> Cont -> Formula Variable
umr2fol (C c)         = \ k -> k c
umr2fol (X x)         = \ k -> k x
umr2fol (P x p edges) = \ k -> umr2fol (A x p edges) k
-- wide-scope negation
umr2fol (A x p (("polarity", umr@(P _ _ _)) : edges))
                      = \ k -> Neg (umr2fol (A x p edges) k)
-- narrow-scope negation
umr2fol (A x p (("polarity", umr) : edges))
                      = \ k -> umr2fol (A x (\ m -> Neg (p m)) edges) k
-- universal quantification
umr2fol (A x p (("quant", umr) : edges))
                      = \ k -> Neg (umr2fol (A x p edges) (\ m -> Neg (k m)))
-- projection phenomena
umr2fol (A x p ((r, umr@(P _ _ _)) : edges))
                      = \ k -> umr2fol umr
                       (\ n -> umr2fol (A x p edges)
                       (\ m -> Conj [Atom r [m, n], k m]))
-- instance assignments
umr2fol (A x p ((r, umr) : edges))
                      = \ k -> umr2fol (A x p edges)
                       (\ m -> Conj [umr2fol umr
                       (\ n -> Atom r [m, n]), k m])
-- base case
umr2fol (A x p [])    = \ k -> Exists x (Conj [p x, k x])
