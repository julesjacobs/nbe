class tm
case class Lam(f:tm => tm) extends tm
case class Pi(t:tm, f:tm => tm) extends tm
case class Univ() extends tm

case class Var(x:String) extends tm
case class App(left:tm, right:tm) extends tm


def fail(msg:String) = assert(false, msg)

var k = 0
def fresh() = { k += 1; (k+'a'-1).toChar.toString() }

def pptm(a:tm):String =
  a match {
    case Lam(f) => val x = fresh(); s"($x => ${pptm(f(Var(x)))})"
    case Pi(a,f) => val x = fresh(); s"($x:${pptm(a)} -> ${pptm(f(Var(x)))})"
    case Univ() => "U"
    case App(a,b) => s"app(${pptm(a)},${pptm(b)})"
    case Var(x) => x
  }

case class thm(w:tm, t:tm) {        // judgement w : t, invariant that t is a type
  override def toString() =
    k = 0
    s"${pptm(w)}  :  ${pptm(t)}"
}

val U = thm(Univ(), Univ())

def pi(t:thm, f:thm => thm):thm =
  assert(conv(t.t, Univ()), s"The first argument of pi must be a type, not $t.")
  thm(Pi(t.w, x => f(thm(x,t.t)).w), Univ())

def lam(t:thm, f:thm => thm):thm =
  assert(conv(t.t, Univ()), s"The first argument of lam must be a type, not $t.")
  thm(Lam(x => f(thm(x,t.w)).w), Pi(t.w, x => f(thm(x,t.w)).t))

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
  a.t match {
    case Pi(t, f) =>
      assert(conv(t, b.t), s"Trying to apply ${a} to ${b}.")
      thm(apptm(a.w, b.w), f(b.w))
    case _ => fail(s"Trying to apply non-function ${a}.")
  }


val idt = pi(U, x => pi(x, y => x))
val id = lam(U, x => lam(x, y => y))
val idU = app(id,U)
val Up = app(idU,U)
val foo = app(id,idt)
val idtyp = pi(U, x => pi(x, a => app(app(id,U),x)))

val idid = app(id, idtyp)
val id2 = app(idid,id)

def arr(a:thm,b:thm) = pi(a, x => b)

val nat = pi(U, t => arr(arr(t,t), arr(t,t)))
val zero = lam(U, t => lam(arr(t,t), f => lam(t, z => z)))
val succ = lam(nat, n => lam(U, t =>
  lam(arr(t,t), f => lam(t, z => app(app(app(n,t),f), app(f,z))))
))
val one = app(succ, zero)
val two = app(succ, one)
val three = app(succ, two)
val add = lam(nat, n => lam(nat, m =>
  lam(U, t => lam(arr(t,t), f => lam(t, z =>
    val nf = app(app(app(n,t),f),z)
    app(app(app(m,t),f),nf)
  )))
))

val two2 = app(app(add,one),one)
val six = app(app(add,three),three)

// val lots = app(app(two,nat),app(two,nat))

val fls = pi(U, x => x)