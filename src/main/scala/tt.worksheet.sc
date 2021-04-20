class tm
case class Lam(f:tm => tm) extends tm
case class Pi(t:tm, f:tm => tm) extends tm
case class Univ() extends tm

case class Var(x:String) extends tm
case class App(left:tm, right:tm) extends tm


def fail(msg:String) = assert(false, msg)

var k = 0
def fresh() = { k += 1; s"x$k" }


case class ty(t:tm)               // judgement A type
case class thm(w:tm, t:ty)        // judgement w : t


val U = thm(Univ(), ty(Univ()))

def pi(t:ty, f:thm => ty):ty =
  ty(Pi(t.t, x => f(thm(x,t)).t))

def lam(t:ty, f:thm => thm):thm =
  thm(Lam(x => f(thm(x,t)).w), pi(t, x => f(x).t))

def conv(p:tm, q:tm):Boolean =
  (p,q) match {
    case (Lam(f),Lam(g)) => val x = Var(fresh()); conv(f(x),g(x))
    case (Pi(a,f),Pi(b,g)) => val x = Var(fresh()); conv(a,b) && conv(f(x),g(x))
    case (Var(x),Var(y)) => x == y
    case (Univ(),Univ()) => true
    case (App(a1,b1),App(a2,b2)) => conv(a1,a2) && conv(b1,b2)
    case _ => false
  }

def apptm(a:tm, b:tm):tm =
  a match {
    case Lam(f) => f(b)
    case _ => App(a,b)
  }

def app(a:thm, b:thm):thm =
  a.t.t match {
    case Pi(t, f) =>
      assert(conv(t, b.t.t), s"Trying to apply ${pp(a)} to ${pp(b)}.")
      thm(apptm(a.w, b.w), ty(f(b.w)))
    case _ => fail(s"Trying to apply non-function ${a.t}.")
  }

def typ(a:thm):ty =
  assert(conv(a.t.t, Univ()), "The term ${a} is not a type.")
  ty(a.w)

def emb(a:ty):thm = thm(a.t, ty(Univ()))

def pptm(a:tm):String =
  a match {
    case Lam(f) => val x = fresh(); s"(fun $x => ${pptm(f(Var(x)))})"
    case Pi(a,f) => val x = fresh(); s"(pi $x:${pptm(a)}, ${pptm(f(Var(x)))})"
    case Univ() => "U"
    case App(a,b) => s"app(${pptm(a)},${pptm(b)})"
    case Var(x) => x
  }

def pp(a:thm):String =
  s"${pptm(a.w)}  :  ${pptm(a.t.t)}"

val id = lam(typ(U), x => lam(typ(x), y => y))
pp(id)
val idU = app(id,U)
pp(idU)
val Up = app(idU,U)

val idtyp = pi(typ(U), x => pi(typ(x), a => typ(app(app(id,U),x))))
pptm(idtyp.t)

val idid = app(id, emb(idtyp))
pp(idid)
val id2 = app(idid,id)
pp(id2)