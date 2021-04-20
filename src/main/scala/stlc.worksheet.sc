class ty
case class Base(x:String) extends ty {
  override def toString() = x
}
case class Arr(a:ty, b:ty) extends ty {
  override def toString() = s"($a -> $b)"
}

def fail(msg:String) = assert(false, msg)

def app(a:ty, b:ty) =
  a match {
    case Arr(c,d) => assert(b == c, s"The types ${b} and ${c} don't match."); d
    case _ => fail(s"Can't apply $a.")
  }

def lam(a:ty, f:ty => ty) = Arr(a,f(a))

val A = Base("A")
val B = Base("B")

val modusponens = lam(A, x => lam(Arr(A,B), f => app(f,x)))

case class And(a:ty, b:ty) extends ty {
  override def toString() = s"($a & $b)"
}

def pair(a:ty, b:ty) = And(a,b)

def fst(a:ty) =
  a match {
    case And(a,b) => a
    case _ => fail(s"Can't do fst$a.")
  }

def snd(a:ty) =
  a match {
    case And(a,b) => b
    case _ => fail(s"Can't do snd$a.")
  }

val flip = lam(And(A,B), x => pair(snd(x),fst(x)))

def destr(a:ty, f : (ty,ty) => ty) =
  a match {
    case And(a,b) => f(a,b)
    case _ => fail(s"Cant destr$a.")
  }

val flip2 = lam(And(A,B), x => destr(x, (a,b) => pair(b,a)))