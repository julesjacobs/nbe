class tm
case class Var(x : String) extends tm
case class Lam(x : String, t : tm) extends tm
case class App(t1 : tm, t2 : tm) extends tm

class sem
case class Tm(t : tm) extends sem
case class Fun(f : sem => sem) extends sem

def eval(ctx : Map[String, sem], t : tm) : sem =
  t match {
    case Var(x) => ctx(x)
    case Lam(x, e) => Fun(v => eval(ctx + (x -> v), e))
    case App(e1, e2) => (eval(ctx, e1), eval(ctx,e2)) match {
      case (Fun(f),v) => f(v)
      case (Tm(t),v) => Tm(App(t,uneval(v)))
    }
  }

var k = 0
def fresh() = { k += 1; s"x$k" }

def uneval(s : sem) : tm =
  s match {
    case Tm(t) => t
    case Fun(f) => val x = fresh(); Lam(x, uneval(f(Tm(Var(x)))))
  }

def norm(t : tm) = uneval(eval(Map.empty, t))

val t1 = Lam("x", Var("x"))
val t2 = App(t1, t1)
val t3 = App(t2, t2)
val res1 = norm(t3)

val t4 = Lam("x", Lam("y", App(Var("x"), Var("y"))))
val t5 = App(t4,t4)
val res2 = norm(t5)

val zero = Lam("f", Lam("z", Var("z")))
def succ(t:tm) = Lam("f", Lam("z", App(App(t, Var("f")), App(Var("f"), Var("z")))))
val one = succ(zero)
val two = succ(one)
val four = App(two, two)
val twohundredfiftysix = App(four, four)
val res4 = norm(twohundredfiftysix)