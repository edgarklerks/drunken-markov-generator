{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}
module Text.Markov(
 	One,
	Two,
	Three,
	Four,
	Five,
	Six,
	Seven,
	OneWord,
	TwoWord,
	ThreeWord,
	FourWord,
	one,
	two,
	three,
	four,
	five,
	six,
	seven,
	oneWord,
	twoWord,
	threeWord,
	fourWord,
	MarkovModel,
	MarkovArrow,
	Freq,
	Order(..),
	analyzeOrder,
	gAnalyzeOrder,
	analyzeFromUrls,
	generateString,
	chainString,
	generateMarkovArrow,
	runMarkovArrow,
	liftMarkovModel	
) where 

import qualified Data.HashMap.Strict as S 
import qualified Data.List as L 
import Control.Monad 
import Data.Monoid
import Data.Hashable 
import Data.Maybe 
import Control.Applicative 
import Control.Category 
import Control.Arrow 
import System.Random 
import System.IO 
import Network.HTTP
import Prelude hiding ((.), id)


type One = Char 
type Two = (Char, Char)
type Three = (Char, Char, Char)
type Four = (Char, Char, Char, Char)
type Five = (Char, Char, Char, Char, Char)
type Six = (Char, Char, Char, Char, Char,Char)
type Seven = (Char,Char,Char,Char,Char,Char,Char)
type Freq = Integer

type OneWord = String 
type TwoWord = (String,String)
type ThreeWord = (String,String, String)
type FourWord = (String,String, String, String)

-- | This is the model of the markov chain  
--  The nth order markov model is a mapping:
--   n x a -> [(b, Freq)] 
--
--   It makes one wonder of this could be cast into an arrow. The arrow would
--   than build a more complicated model from other models. It would not be an easy one. Especially because I use frequencies instead of probabilities.  
--  
newtype MarkovModel order out = MM { 
	unMM :: S.HashMap order [(out, Freq)]
	} deriving Show 

-- | It would look like this 
newtype MarkovArrow order out = MA {
		unMA :: order -> [(out, Freq)]
	}

-- | Run a markov arrow as a mapping from order to [(out, freq)]
runMarkovArrow :: MarkovArrow order out -> order -> [(out, Freq)]
runMarkovArrow m o = unMA m o

-- | Generate a string of out from a markov arrow 
generateMarkovArrow :: (Order order out, RandomGen g) => MarkovArrow order out ->  g -> order -> [out]
generateMarkovArrow m seed o = let xs = unMA m o
				   (p,g) = freq xs seed	
			       in generateMarkovArrow m seed (shiftOrder p o)

-- | And I can lift an MarkovModel into the MarkovArrow category 
liftMarkovModel :: Order order out => MarkovModel order out -> MarkovArrow order out 
liftMarkovModel (MM s) = MA (\order -> case S.lookup order s of 
						Nothing -> [] 
						Just ts -> ts )


-- | The identity function is rather trivial
idMA :: MarkovArrow a a  
idMA = MA $ \i -> [(i, 1)]

-- | But composition is a problem 
-- I would have to convert the frequency into probabilities and the compose them 
compMA :: MarkovArrow b c -> MarkovArrow a b -> MarkovArrow a c 
compMA (MA f) (MA g) = MA $ compRaw f g 

-- | Which of course is entirely possible 
compRaw :: (b -> [(c, Freq)]) ->  (a -> [(b, Freq)]) -> a -> [(c, Freq)]
compRaw f g a = let xs = toProb $ g a  
		in fromProb $ foldr step [] xs 
	where step (x,p) z = let xs = toProb (f x)
			     in fmap (second (*p)) xs ++ z 

toProb :: [(a, Freq)] -> [(a, Double)] 
toProb xs =  let tot = fromInteger $ sum (snd <$> xs) 
	     in fmap (second (\x -> fromInteger x / tot)) xs 

fromProb :: [(a, Double)] -> [(a, Freq)]
fromProb xs = let min = minimum (fmap snd xs) 
		  reversed = 1 / min 
	      in fmap (second (round.(*reversed))) xs  

-- | The category is quite neat, but the arrow is probably not an arrow 
instance Category MarkovArrow where 
	id = idMA 
	(.) = compMA  

-- | Now lets instantiate a functor 
instance Functor (MarkovArrow a) where 
	fmap f (MA g) = MA $ \i -> fmap (first f) $ g i

-- | And a applicative instance, which has a lot in common with the arrow interface.
--   We would want to take the cross product instead of the zipping functor  
--   This looks rather sane, we take both probabilities and multiply them 
instance Applicative (MarkovArrow a) where 
	pure f = MA $ \i -> [(f, 1)] 
	(<*>) (MA f) (MA g) = MA $ \i -> let xs = toProb $ f i 
					     ns = toProb $ g i 
					 in fromProb $  [ (h a, p * p') | (h,p) <- xs, (a,p') <- ns]  

-- | Create the arrow interface, this doesn't look to good unfortunetaly, I bet this thing isn't an arrow   
--  but the arrow is probably sane
instance Arrow MarkovArrow where 
	arr f= MA $ \i -> [(f i, 1)]
	first (MA f) = MA $ \(i,s) -> let xs = f i
				      in fmap (first (\x -> (x,s))) xs  


-- | This is a class which specify the relation between out and order,
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

instance Order OneWord String where 
	takeOrder (x:y:_) = return (x,y)
	takeOrder _ = mzero 
	shiftOrder q a = q

instance Order TwoWord String where 
	takeOrder (x:y:z:_) = return ((x,y),z)
	takeOrder _ = mzero
	shiftOrder q (a,b) = (b,q)

instance Order ThreeWord String where 
	takeOrder (x:y:z:p:_) = return ((x,y,z),p)
	takeOrder _ = mzero 
	shiftOrder q (a,b,c) = (b,c,q)

instance Order FourWord String where
	takeOrder (x:y:z:p:q:_) = return ((x,y,z,p),q)
	takeOrder _ = mzero 
	shiftOrder q (a,b,c,d) = (b,c,d,q)

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
oneWord :: OneWord 
oneWord = undefined 
twoWord :: TwoWord 
twoWord = undefined 
threeWord :: ThreeWord 
threeWord = undefined 
fourWord :: FourWord 
fourWord = undefined 


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

-- | Analyze and build a markov model from specified urls
-- o is the order of the markov model 
analyzeFromUrls :: Order order Char => order -> [String] -> IO (MarkovModel order Char) 
analyzeFromUrls o xs = do 
			reqs <- forM xs $ \s -> simpleHTTP (getRequest s)
			body <- forM reqs $ getResponseBody
			return $ analyzeOrder o (concat body)

-- | Analyze a markov model from a given string 
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
-- | Analyze an markov model for more general types 
gAnalyzeOrder :: Eq out => Order order out => order -> [out] -> MarkovModel order out 
gAnalyzeOrder _ xs = createPairs xs takeOrder 

testGAnalyze o  = do 
		let urls = [	"http://www.textfiles.com/sex/808-lust.txt",
			"http://www.ewtn.com/library/liturgy/womord.txt",
			"http://www.textfiles.com/sex/808-next.txt",
			"http://www.textfiles.com/sex/a_friend.txt",
			"http://www.textfiles.com/sex/camptrip.txt",
			"http://www.textfiles.com/sex/clothes.pin",
			"http://www.brothermike.com/Outlines/2002text/s120802.txt",
			"http://www.rfc-editor.org/rfc/rfc1127.txt",
			"http://www.rfc-editor.org/rfc/rfc1141.txt"  ]

		xs <- forM urls $ \s -> simpleHTTP (getRequest s) 
		body <- forM xs $ \p -> getResponseBody p  
		let mos = gAnalyzeOrder o (words $ collapseSpaces $ concat body)
		n <- newStdGen 
		let bs =  generateString n mos 
		writeFile "generated-words" $ unwords (take 400 bs) 

collapseSpaces :: String -> String 
collapseSpaces (' ': ' ': xs) = collapseSpaces (' ':xs)
collapseSpaces (x:xs) = x : collapseSpaces xs
collapseSpaces [] = [] 

-- | Generate a string from a markov model with a given seed 
generateString :: (Order order a, RandomGen g) => g -> MarkovModel order a -> [a]
generateString stdg m = let (k,g) = choose stdg (S.keys $ unMM m)
			in chainString k m g

-- | Generate a string from a starting seed and a markov model 
chainString :: (Order a b, RandomGen g) => a -> MarkovModel a b -> g -> [b]
chainString a m g = case S.lookup a (unMM m) of 
				Nothing -> [] 
				Just str -> let (n, g') = freq str g 
					    in n : chainString (shiftOrder n a) m g'


freq :: RandomGen g => [(a, Freq)] -> g -> (a, g)
freq xs g = let (p,g') = randomR (1, tot) g
	        tot = sum (fmap snd xs)
	  in (pick p xs,g') 

pick :: Freq -> [(a,Freq)] -> a 
pick n ((a,k):xs) | n <= k = a
	 	  | otherwise = pick (n - k) xs 
  
	
choose :: RandomGen g => g -> [a] -> (a, g)
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


