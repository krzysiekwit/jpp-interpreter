s1 = Ass "x" ELitInt 100
	While (ERel (ELitInt 99) GT (ELitInt 99))
		Ass "x" (Minus (EVar "x") (ELitInt 1))
	(Print (EVar "x"))
		

type Location = Int
type Index = [Ident]
type Stack = [Int]
type Val = Int --zmienić też na inne niż int

position :: Ident -> Index -> Location
position name index = let pos n (nm:nms) = if name == nm
					                       then n
					                       else pos (n+1) nms
		              in pos 1 index

fetch :: Location -> Stack -> Int
fetch n (v:vs) = if n == 1 then v else fetch (n-1) vs

put :: Location -> Int -> Stack -> Stack
put n x (v:vs) = if n == 1
                 then x:vs
                 else v:(put (n-1) x vs)

newtype M a = StOut (Stack -> (a, Stack, String))

instance Monad M where
	return x = StOut (\n -> (x,n,""))
	e >>= f = StOut (\n -> let (a,n1,s1) = (unStOut e) n; (b,n2,s2) = unStOut (f a) n1
                           in (b,n2,s1++s2))

instance Functor M where
    fmap = liftM

instance Applicative M where
    pure = return
    (<*>) = ap

unStOut (StOut f) = f			        

getfrom :: Location -> M Int
getfrom i = StOut (\ns -> (fetch i ns,ns,""))

write :: Location -> Int -> M ()
write i v = StOut (\ns -> ((),put i v ns,""))

push :: Int -> M ()
push x = StOut(\ns -> ((), x:ns, "") ) 

pop :: M ()
pop = StOut (\m -> let  (n:ns) = m in ((),ns,""))

eval :: Expr -> Index -> M Val
eval expr index = case expr of
			        EVar x -> let loc = position x index in getfrom loc
			        EAdd x Plus y -> do {	a <- eval x index ;
						                    b <- eval y index ;
						                    return (a + b) }
			        EAdd x Minus y -> do {	a <- eval x index ;
						                    b <- eval y index ;
						                    return (a - b) }
			        EMul x Times y -> do {	a <- eval x index ;
						                    b <- eval y index ;
						                    return (a * b) }
			        --EMul x Div y -> do {	a <- eval x index ;
					--	                    b <- eval y index ;
					--	                    return (a / b) }
			        --EMul x Mod y -> do {	a <- eval x index ;
					--	                    b <- eval y index ;
					--	                    return (a mod b) }
			        ELitInt x -> return x -- ??
			        --EString x -> return x --Tu źle - mamy zwrócić int
			        --ELitTrue -> return true --źle
			        --ELitFalse -> return false -- źle
			        --ERel x LTH y -> do {a <- eval x index ;
					--	                b <- eval y index ;
					--	                return (a < b) }
			        --ERel x LE y -> do {	a <- eval x index ;
					--	                b <- eval y index ;
					--	                return (a <= b) }
			        --ERel x GTH y -> do {a <- eval x index ;
					--	                b <- eval y index ;
					--	                return (a > b) }
			        --ERel x GE y -> do {	a <- eval x index ;
					--	                b <- eval y index ;
					--	                return (a >= b) }
			        --ERel x EQU y -> do {a <- eval x index ;
					--	                b <- eval y index ;
					--	                return (a == b) }
			        --ERel x NE y -> do {	a <- eval x index ;
					--	                b <- eval y index ;
					--	                return (a != b) }
			        --EAnd x y -> do {    a <- eval x index ;
					--	                b <- eval y index ;
					--	                return (a && b) }
			        --EOr x y -> do {		a <- eval x index ;
					--	                b <- eval y index ;
					--	                return (a || b) }
			        
			--pozostałe operatory i pozostałe Exp
			-- index, position, getfrom

interpret :: Stmt -> Index -> M ()
interpret stmt index = case stmt of
                    While e b -> let loop () = do {v <- eval e index ;
                                                if v == 0 
                                                then return ()
                                                else do {interpret b index ;
                                                loop ()}}
                                 in loop ()
                    Ass name e -> let loc = position name index
                                  in do {   v <- eval e index ;
                                            write loc v }
                    Print e -> do {v <- eval e index ;
                                   output v}
                    Decl (ArgTypeP (PType Int)) [(Init name e)] -> do { v <- eval e index ;
                                                                        push v ;
                                                                        --do index dołożyć na początek name - jak ???
                                                                        pop ; }

output :: Show a => a -> M ()
output v = StOut (\n -> ((),n,show v))
