class sem
case class Lam(f : sem => sem) extends sem
case class App(a:sem, b:sem) extends sem
case class Var(x:String) extends sem

def app(a:sem, b:sem):sem =
  a match {
    case Lam(f) => f(b)
    case _ => App(a,b)
  }

class tm
case class tLam(x:String, e:tm) extends tm
case class tApp(a:tm, b:tm) extends tm
case class tVar(x:String) extends tm

def eval(ctx : Map[String, sem], t : tm) : sem =
  t match {
    case tVar(x) => ctx(x)
    case tLam(x, e) => Lam(v => eval(ctx + (x -> v), e))
    case tApp(e1, e2) => app(eval(ctx, e1), eval(ctx,e2))
  }

var k = 0
def fresh() = { k += 1; s"x$k" }

def uneval(s : sem) : tm =
  s match {
    case Lam(f) => val x = fresh(); tLam(x, uneval(f(Var(x))))
    case App(a,b) => tApp(uneval(a), uneval(b))
    case Var(x) => tVar(x)
  }

def norm(t : tm) = uneval(eval(Map.empty, t))

val t1 = tLam("x", tVar("x"))
val t2 = tApp(t1, t1)
val t3 = tApp(t2, t2)
val res1 = norm(t3)

val t4 = tLam("x", tLam("y", tApp(tVar("x"), tVar("y"))))
val t5 = tApp(t4,t4)
val res2 = norm(t5)

val zero = tLam("f", tLam("z", tVar("z")))
def succ(t:tm) = tLam("f", tLam("z", tApp(tApp(t, tVar("f")), tApp(tVar("f"), tVar("z")))))
val one = succ(zero)
val two = succ(one)
val four = tApp(two, two)
val twohundredfiftysix = tApp(four, four)
val res4 = norm(twohundredfiftysix)