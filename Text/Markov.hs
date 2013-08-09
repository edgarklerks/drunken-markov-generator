{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}
module Text.Markov where 

import qualified Data.HashMap.Strict as S 
import qualified Data.List as L 
import Control.Monad 
import Data.Monoid
import Data.Hashable 
import Data.Maybe 
import Control.Arrow 
import System.Random 
import System.IO 
import Network.HTTP

-- | The nth order markov model is a mapping:
--   n x Char -> [(Char, Freq)] 

type One = Char 
type Two = (Char, Char)
type Three = (Char, Char, Char)
type Four = (Char, Char, Char, Char)
type Five = (Char, Char, Char, Char, Char)
type Six = (Char, Char, Char, Char, Char,Char)
type Seven = (Char,Char,Char,Char,Char,Char,Char)
type Freq = Integer

type TwoWord = (String,String)

newtype MarkovModel order out = MM { 
	unMM :: S.HashMap order [(out, Freq)]
	} deriving Show 

class (Hashable order, Eq order) => Order order out where 
	takeOrder :: [out] -> [(order, out)] 
	shiftOrder :: out -> order -> order 
	

instance Order One Char where 
	takeOrder (x:y:_) = return (x,y)
	takeOrder _ = mzero 
	shiftOrder c _ = c 

instance Order Two Char where 
	takeOrder (x:y:z:_) = return ((x,y),z)
	takeOrder _ = mzero 
	shiftOrder c (a,b) = (b,c)

instance Order Three Char where 
	takeOrder (x:y:z:p:_) = return ((x,y,z),p)
	takeOrder _ = mzero 
	shiftOrder c (a,b,d) = (b,d,c)

instance Order Four Char where 
	takeOrder (x:y:z:p:q:_) = return ((x,y,z,p),q)
	takeOrder _ = mzero 
	shiftOrder q (a,b,c,d) = (b,c,d,q)

instance Order Five Char where 
	takeOrder (x:y:z:p:q:r:_) = return ((x,y,z,p,q),r)
	takeOrder _ = mzero 
	shiftOrder q (a,b,c,d,e) = (b,c,d,e,q)
instance Order Six Char where 
	takeOrder (x:y:z:p:q:r:s:_) = return ((x,y,z,p,q,r),s)
	takeOrder _ = mzero 
	shiftOrder q (a,b,c,d,e,f) = (b,c,d,e,f,q)
instance Order Seven Char where 
	takeOrder (x:y:z:p:q:r:s:t:_) = return ((x,y,z,p,q,r,s),t)
	takeOrder _ = mzero 
	shiftOrder q (a,b,c,d,e,f,g) = (b,c,d,e,f,g,q)

one :: One 
one = undefined 
two :: Two 
two = undefined 
three :: Three 
three = undefined 
four :: Four 
four = undefined 
five :: Five 
five = undefined  
six :: Six 
six = undefined 
seven :: Seven 
seven = undefined 


testntOrder :: Order o Char => o -> IO ()
testntOrder o = do 
	xs <- analyzeFromUrls o [
		"http://www.textfiles.com/sex/808-lust.txt",
		"http://www.ewtn.com/library/liturgy/womord.txt",
		"http://www.textfiles.com/sex/808-next.txt",
		"http://www.textfiles.com/sex/a_friend.txt",
		"http://www.textfiles.com/sex/camptrip.txt",
		"http://www.textfiles.com/sex/clothes.pin",
		"http://www.brothermike.com/Outlines/2002text/s120802.txt",
		"http://www.rfc-editor.org/rfc/rfc1127.txt",
		"http://www.rfc-editor.org/rfc/rfc1141.txt" 
		]
	c <- newStdGen 
	writeFile "generated" $  take 5000 $  generateString c xs 

analyzeFromUrls :: Order order Char => order -> [String] -> IO (MarkovModel order Char) 
analyzeFromUrls o xs = do 
			reqs <- forM xs $ \s -> simpleHTTP (getRequest s)
			body <- forM reqs $ getResponseBody
			return $ analyzeOrder o (concat body)

analyzeOrder :: Order o Char => o -> String -> MarkovModel o Char 
analyzeOrder _ xs = createPairs (collapseSpaces $ filterShit xs) takeOrder 

	where filterShit (x:xs) = case x of
					'\n' -> ' ' : filterShit xs
					'\r' -> filterShit xs 
					'"' -> filterShit xs 
					'\'' -> filterShit xs 
					'-' -> filterShit xs 
					c -> c : filterShit xs  
	      filterShit [] = [] 

collapseSpaces :: String -> String 
collapseSpaces (' ': ' ': xs) = collapseSpaces (' ':xs)
collapseSpaces (x:xs) = x : collapseSpaces xs
collapseSpaces [] = [] 
generateString :: (Order order a) => StdGen -> MarkovModel order a -> [a]
generateString stdg m = let (k,g) = choose stdg (S.keys $ unMM m)
			in chainString k m g
chainString :: (Order a b) => a -> MarkovModel a b -> StdGen -> [b]
chainString a m g = case S.lookup a (unMM m) of 
				Nothing -> [] 
				Just str -> let (n, g') = freq str g 
					    in n : chainString (shiftOrder n a) m g'


freq :: [(a, Freq)] -> StdGen -> (a, StdGen)
freq xs g = let (p,g') = randomR (1, tot) g
	        tot = sum (fmap snd xs)
	  in (pick p xs,g') 

pick :: Freq -> [(a,Freq)] -> a 
pick n ((a,k):xs) | n <= k = a
	 	  | otherwise = pick (n - k) xs 
  
	
choose :: StdGen -> [a] -> (a, StdGen)
choose std xs = let (a, g) = randomR (0, length xs - 1) std in (xs !! a, g)
 

-- | This looks supiciously comonadic to me 
createPairs :: (Eq a, Hashable a, Eq b) => [b] -> ([b] -> [(a,b)]) -> MarkovModel a b
createPairs [] _ = MM mempty  
createPairs xs f =  f xs `squashProb` (createPairs (tail xs) f)
	where squashProb xs m = MM $ foldr step (unMM m) xs 
			where step x z = updateProb (fst x) (snd x) z  

updateProb :: (Eq a, Hashable a, Eq b) => a -> b -> S.HashMap a [(b,Freq)] -> S.HashMap a [(b, Freq)]
updateProb a c m = case (S.lookup a m) of 
			Nothing -> S.insert a [(c,1)] m
			Just ts -> S.insert a (intoList c ts) m  
		where intoList c (x:xs) | c == fst x = second (+1) x : xs  
					| otherwise = x : intoList c xs 
		      intoList c [] = [(c,1)]


