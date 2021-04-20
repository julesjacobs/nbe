class ty
case class Base(x:String) extends ty
case class Arr(a:ty, b:ty) extends ty

case class tm(t:ty)

def fail(msg:String) = assert(false, msg)

def app(a:tm, b:tm):tm =
  a.t match {
    case Arr(c,d) => assert(b.t == c, s"The types ${b.t} and ${c} don't match."); tm(d)
    case _ => fail(s"Can't apply $a.")
  }

def lam(a:ty, f:tm => tm):tm = tm(Arr(a,f(tm(a)).t))

val A = Base("A")
val B = Base("B")

val modusponens = lam(A, x => lam(Arr(A,B), f => app(f,x)))

case class And(a:ty, b:ty) extends ty

def pair(a:tm, b:tm):tm = tm(And(a.t,b.t))

def fst(a:tm):tm=
  a.t match {
    case And(a,b) => tm(a)
    case _ => fail(s"Can't do fst(${a.t}).")
  }

def snd(a:tm) =
  a.t match {
    case And(a,b) => tm(b)
    case _ => fail(s"Can't do snd(${a.t}).")
  }

val flip = lam(And(A,B), x => pair(snd(x),fst(x)))

case class Or(a:ty, b:ty) extends ty

def inl(a:tm, b:ty):tm = tm(Or(a.t,b))
def inr(a:ty, b:tm):tm = tm(Or(a,b.t))

def destr(a:tm, f:tm => tm, g:tm => tm):tm =
  a.t match {
    case Or(a,b) =>
      val p = f(tm(a)); val q = g(tm(b));
      if(p == q) then p else fail(s"The types ${p.t} and ${q.t} are not equal.")
    case _ => fail(s"Can't do destr(${a.t}).")
  }

val flop = lam(Or(A,B), x => destr(x, p => inr(B,p), q => inl(q,A)))

def ascribe(t:ty, f:ty => Unit):tm = { f(t); tm(t) }

def check(x:tm) = (y:ty) => assert(x.t == y, s"The types ${x.t} and $y are not equal.")

def ilam(f : tm => (ty => Unit)) = (x:ty) =>
  x match {
    case Arr(a,b) => f(tm(a))(b)
    case _ => fail(s"The type $x is not an arrow.")
  }

val id = ascribe(Arr(A,Arr(Arr(A,B),B)),
  ilam(a => ilam(f => check(app(f,a)))))