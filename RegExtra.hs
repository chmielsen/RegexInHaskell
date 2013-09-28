-- Wojciech Chmiel
-- regex in haskell
module RegExtra where
import Mon
import Reg
import Data.List
import Debug.Trace

data AB = A | B deriving(Eq,Ord,Show)

infix 4 ===
class Equiv a where
  (===) :: a -> a -> Bool

instance (Eq c) => Equiv (Reg c) where
   r1 === r2 = (simpl r1) == (simpl r2)

instance Mon (Reg c) where
  m1 = Eps
  x <> y = x :> y
 

-- simplify the regular expression 
simpl :: Eq c => Reg c -> Reg c
simpl x = simplified
    where 
        simplified = if simplify x == x
                    then x
                    else simpl $ simplify x

-- with Empty
simplify :: Eq c => Reg c -> Reg c
simplify (Empty :> r) = Empty
simplify (r :> Empty) = Empty
simplify (Empty :| r) = simplify r
simplify (r :| Empty) = simplify r
simplify (Many Empty) = Eps
-- with Eps
simplify (Eps :> Eps) = Eps
simplify (Eps :> r)   = simplify r
simplify (r :> Eps)   = simplify r
simplify (Eps :| Eps) = Eps
simplify (r :| Eps)   = Eps :| simplify r
simplify (Many Eps)   = Eps
-- with union
simplify (a :| b) 
    | a `contains` b = simplify a
    | b `contains` a = simplify b
simplify (a :| b :| c) 
    | a `contains` b = simplify (a :| c)
    | a `contains` c = simplify (a :| b)
    | b `contains` c = simplify (a :| b)
    | b `contains` a = simplify (b :| c)
    | c `contains` a = simplify (b :| c)
    | c `contains` b = simplify (a :| c)
simplify (a :| b) 
    | a == b    = simplify a
    | otherwise = (simplify a) :| (simplify b)
-- with Many
simplify (Many (Many r)) = simplify (Many r)
simplify (Many r)        = Many (simplify r)
-- with concat
simplify (a :> (b :> c)) = simplify (a :> b :> c)
simplify (a :> b)        = (simplify a) :> (simplify b)
-- otherwise
simplify r = r


nullable :: Reg c -> Bool
nullable Eps      = True
nullable (Many x) = True
nullable (Lit c)  = False
nullable Empty    = False
nullable (a :| b) = (nullable a) || nullable b
nullable (a :> b) = (nullable a) && nullable b


empty :: Reg c -> Bool 
empty Empty = True
empty (a :| b) = empty a && empty b
empty (a :> b) = empty a || empty b
empty r = False


--based on http://matt.might.net/articles/implementation-of-regular-expression-matching-in-scheme-with-derivatives/
der :: Eq c => c -> Reg c -> Reg c
der c Empty = Empty
der c Eps = Empty
der c (Lit b)
    | c == b = Eps
    | otherwise = Empty
der c (a :| b) = (der c a) :| (der c b)
der c (a :> b) 
    | nullable a = (der c b) :| ((der c a) :> b)
    | otherwise  = ((der c a) :> b)
der c (Many a) = (der c a) :> Many a

ders :: Eq c => [c] -> Reg c -> Reg c
ders [] r = r
ders c r 
    | empty r = r
    | otherwise = ders (tail c) dr
        where dr = der (head c) (simpl r)


accepts :: Eq c => Reg c -> [c] -> Bool
accepts r w = nullable $ ders w (simpl r)


mayStart :: Eq c => c -> Reg c -> Bool
mayStart c r = simpl (der c (simpl r)) /= Empty


match :: Eq c => Reg c -> [c] -> Maybe [c]
match r w = match' (simpl r) w [] Nothing

match' :: Eq a => Reg a -> [a] -> [a] -> Maybe [a] -> Maybe [a]
match' r w curWord longestWord
    | null w     = if nullable r then Just (reverse curWord) else longestWord
    | empty r    = longestWord
    | nullable r = match' dr (tail w) (hw:curWord) (Just $ reverse curWord)
    | otherwise  = match' dr (tail w) (hw:curWord) longestWord
    where
        hw = head w
        dr = der hw r


search :: Eq c => Reg c -> [c] -> Maybe [c]
search r w
    | curSubword /= Nothing = curSubword
    | w == []               = Nothing
    | otherwise             = search sim $ tail w
    where
        sim        = simpl r
        curSubword = match sim w


findall :: Eq c => Reg c -> [c] -> [[c]]
findall r w = reverse $ findall' (simpl r) w []

findall' r w words
    | w == []               = if nullable r then []:words else words
    | curSubword == Nothing = findall' r (tail w) words
    | curSubword == Just [] = findall' r (tail w) [[]]++words
    | otherwise             = findall' r (drop len w) (newWord:words)
    where
        curSubword = match r w
        newWord    = eliminate curSubword
        len        = length newWord


eliminate :: Maybe a -> a
eliminate (Just a) = a


char :: Char -> Reg Char
char = Lit


string :: [Char] -> Reg Char
string = foldr1 (:>) . map Lit


alts :: [Char] -> Reg Char
alts = foldr1 (:|) . map Lit


letter = alts ['a'..'z'] :| alts ['A'..'Z']
digit  = alts ['0'..'9']
number = digit :> Many digit
ident  = letter :> Many (letter :| digit)


many1 r = r :> Many r

contains :: Eq c => Reg c -> Reg c -> Bool
contains r Empty    = True
contains r Eps      = nullable r
contains r (Lit c)  = nullable $ der c r
contains (Many r) (Many s) = r `contains` s
contains r (s :| t) = (r `contains` s) && (r `contains` t)
contains (r :| s) t = (r `contains` t) || (s `contains` t)
contains r s        = r == s
