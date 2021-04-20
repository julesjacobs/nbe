class ty
case class Arr(a:ty, b:ty) extends ty {
  override def toString() = s"($a -> $b)"
}
case class And(a:ty, b:ty) extends ty {
  override def toString() = s"($a ∧ $b)"
}
case class All(f:ty => ty) extends ty{
  override def toString() =
    val x = fresh(); s"(∀$x, ${f(SVar(x))})"
}
case class SVar(x:String) extends ty {
  override def toString() = x
}

def fail(msg:String) = assert(false, msg)

var k = 0
def fresh() = { k += 1; (k+'a'-1).toChar.toString() }

def eq(a:ty, b:ty) : Boolean =
  (a,b) match {
    case (Arr(a1,a2),Arr(b1,b2)) => eq(a1,b1) && eq(a2,b2)
    case (And(a1,a2),And(b1,b2)) => eq(a1,b1) && eq(a2,b2)
    case (All(f), All(g)) => val x = SVar(fresh()); eq(f(x), g(x))
    case (SVar(x),SVar(y)) => x==y
    case _ => false
  }

def app(a:ty, b:ty) =
  a match {
    case Arr(c,d) => assert(eq(c,b), s"The types $c and $b don't match."); d
    case _ => fail(s"Can't app $a.")
  }

def lam(a:ty, f:ty => ty) = Arr(a,f(a))

def pair(a:ty, b:ty) = And(a,b)

def fst(a:ty) =
  a match {
    case And(c,d) => c
    case _ => fail(s"Can't take fst of $a.")
  }

def snd(a:ty) =
  a match {
    case And(c,d) => d
    case _ => fail(s"Can't take snd of $a.")
  }

def tlam(f:ty => ty) = All(f)

def tapp(a:ty, b:ty) =
  a match {
    case All(f) => f(b)
    case _ => fail(s"Can't tapp $a.")
  }

val A = SVar("A")
val B = SVar("B")

val flip = tlam(X => tlam(Y => lam(And(X,Y), x => pair(snd(x),fst(x)))))
val foo = lam(And(A,B), x => app(tapp(tapp(flip, A), B), x))

class typ
case class TyVar(x:String) extends typ
case class TyArr(a:typ, b:typ) extends typ
case class TyAll(x:String, a:typ) extends typ

class tm
case class TmVar(x:String) extends tm
case class TmApp(a:tm, b:tm) extends tm
case class TmLam(x:String, t:typ, e:tm) extends tm
case class TmTApp(a:tm, t:typ) extends tm
case class TmTLam(x:String, e:tm) extends tm

def checkty(tctx:Map[String,ty], t:typ):ty =
  t match {
    case TyVar(x) => tctx(x)
    case TyArr(a,b) => Arr(checkty(tctx,a), checkty(tctx,b))
    case TyAll(x,a) => All(X => checkty(tctx + (x -> X), a))
  }

def check(tctx:Map[String,ty],ctx:Map[String,ty], a:tm):ty =
  a match {
    case TmVar(x) => ctx(x)
    case TmApp(a,b) => app(check(tctx,ctx,a), check(tctx,ctx,b))
    case TmLam(x,t,e) => lam(checkty(tctx,t), X => check(tctx,ctx + (x -> X), e))
    case TmTApp(a,t) => tapp(check(tctx,ctx,a), checkty(tctx,t))
    case TmTLam(x, e) => tlam(X => check(tctx + (x -> X),ctx, e))
  }

val term = TmTLam("A", TmLam("x", TyVar("A"), TmVar("x")))
val t = check(Map.empty, Map.empty, term)